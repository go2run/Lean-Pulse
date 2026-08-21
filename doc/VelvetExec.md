# Velvet 怎麼跑：從 `method` 到原生執行檔

> **關於這份教材**
> 回答兩個問題：**(1) Velvet 在 Lean 4 裡到底是怎麼執行的**、**(2) 怎麼把驗證過的
> 程式抽出來、編譯成可以獨立跑的執行檔**。
>
> 全部內容都在本專案（Lean 4.24.0 + Velvet master）實測過。可執行的對照檔是
> [VelvetExec.lean](../VelvetExec.lean)（Velvet 端）與 [Main.lean](../Main.lean)（`IO` 端）：
>
> ```sh
> lake build VelvetExec     # 驗證 + 抽取 + tester + 隨機測試
> lake build velvet_demo    # 編譯成原生執行檔
> ./.lake/build/bin/velvet_demo 3 1 4 1 5
> ```

---

## 目錄

| 節 | 主題 |
|---|---|
| 1 | Velvet 在 Lean 4 中的執行模型（`method` 展開成什麼） |
| 2 | 三種「跑起來」的方式：`#eval` / `#guard_msgs` / 執行檔 |
| 3 | `extract_program_for`：抽取可執行程式 |
| 4 | `lean_exe`：編譯成原生執行檔 |
| 5 | tester 與隨機測試：把規格當 runtime check |
| 6 | 陷阱：驗證過 ≠ 跑得完 |
| 7 | 抽取到其他程式語言？（FFI / 手寫 / 證等價） |
| 8 | 速查表 |

---

## 1. Velvet 在 Lean 4 中的執行模型

### 1.1 `method` 不是新語言，是 Lean 的 `def`

這是理解一切的起點。`method` 是一個 **command elaborator**，它做兩件事：

1. 產生一個**普通的 Lean `def`**，名字和參數跟你寫的一樣，回傳型別是 `VelvetM ...`。
2. 把 `require` / `ensures` 記在一張表裡，等 `prove_correct` 來取用。

驗證一下。寫：

```lean
method Maximum (a : Int) (b : Int) return (m : Int)
    ensures m ≥ a
    ensures m ≥ b
    ensures m = a ∨ m = b
    do
    if a ≥ b then
      return a
    else
      return b
```

然後 `#print Maximum`，實際輸出是：

```lean
def Maximum : ℤ → ℤ → VelvetM ℤ :=
fun a b => if a ≥ b then pure a else pure b
```

規格完全不見了——它們不在程式裡，而是在 `prove_correct` 生成的**另一個定理**裡：

```lean
prove_correct Maximum by
  loom_solve
-- 生成 @[loomSpec] lemma Maximum_correct : triple ⟨require⟩ (Maximum a b) (fun m => ⟨ensures⟩)
```

`#print Maximum_correct` 可以看到它。**程式與證明是分離的兩個 Lean 宣告**，這是後面能安全抽取的根本原因：抽取只碰程式那半邊。

### 1.2 `VelvetM` 是什麼

```lean
abbrev VelvetM α := NonDetT DivM α          -- Velvet/VelvetTheory.lean

inductive DivM (α : Type u) where           -- Loom/MonadAlgebras/Instances/Basic.lean
  | res (x : α)                             -- 正常結束，帶回傳值
  | div                                     -- 發散（語意上的 ⊥）
```

拆兩層看：

- **`DivM`** = 「可能不終止」。`.res x` 是有結果，`.div` 是沒有。
  部分正確性（partial correctness）語意就是靠這個型別表達的：規格只約束 `.res` 的情形。
- **`NonDetT`** = 非確定性 transformer。它是一棵**語法樹**（`pure` / `vis` / `pickCont` /
  `repeatCont` 四個構造子），不是可以直接跑的東西。

所以 `method` 產生的 `Maximum a b` 只是**一棵程式樹**。要跑它，得先把樹「解釋」掉——這就是下一節的 `.run`。

### 1.3 `.run` = 把語法樹變成可執行的計算

`NonDetT.run` 定義在 `Loom/MonadAlgebras/NonDetT/Extract.lean`：

```lean
def NonDetT.run {α : Type u} : NonDetT m α -> m α
  | .pure x => Pure.pure x
  | .vis x f => liftM x >>= (fun x => (f x).run)
  | .pickCont p f =>
    match Findable.find (p := p) () with
    | none => CCPOBot.compBot          -- 找不到見證 → DivM.div
    | some x => (f x).run
  | .repeatCont init f cont =>
    forIn Lean.Loop.mk init (fun _ x => (f x).run) >>= (fun x => (cont x).run)
```

三個重點：

| 構造子 | 跑起來變成什麼 |
|---|---|
| `.pickCont` | 用 `Findable` 實例**實際去搜**一個滿足謂詞的值；搜不到就回 `DivM.div` |
| `.repeatCont` | 變成 Lean 的 `forIn Lean.Loop.mk`，也就是**真的 while 迴圈** |
| `.vis` | 一般的 monadic bind |

「`while` 變成真的 while 迴圈」這句話有個後果：**驗證時被 `invariant` 抽象掉的迴圈，執行時是真的一圈一圈跑**。如果它不終止，執行檔就會卡住——不會回傳 `.div`。§6.1 有實測。

### 1.4 為什麼可以信任 `.run`

抽取如果不保證正確，前面的驗證就白做了。Loom 證了這件事：

```lean
-- Loom/MonadAlgebras/NonDetT/Extract.lean
lemma ExtractNonDet.extract_refines (pre : l) (s : NonDetT m α) :
  triple pre s post -> triple pre s.run post
```

（`PartialCorrectness.DemonicChoice` 與 `TotalCorrectness.DemonicChoice` 兩個
namespace 各有一份。）

白話：**你對程式樹 `s` 證出來的 triple，`s.run` 一樣成立**。所以
`Maximum_correct` 講的 `ensures`，抽取後的 `MaximumExec` 照樣滿足。

這是一條**已經證好的 Lean 定理**，不是文件上的口頭承諾——這正是 Velvet 抽取和「把
Dafny 程式手動翻譯成 C#」的本質差別。

---

## 2. 三種「跑起來」的方式

### 2.1 `#eval`——最快的回饋迴圈

```lean
#eval (Maximum 3 7).run
-- DivM.res 7
```

注意 `.run` 不能省。`Maximum 3 7` 是語法樹，`#eval` 它不會給你 7。

有 `mut` 參數時，回傳值會和被改動的參數打包成 tuple：

```lean
method DoubleAll (mut arr : Array Int) return (u : Unit) ...

#eval (DoubleAll #[1, 2, 3]).run
-- DivM.res ((), #[2, 4, 6])
--          ↑    ↑
--          |    mut 參數的最終值
--          return 的值（Unit）
```

順序是 `(回傳值, mut₁, mut₂, ...)`，`mut` 依宣告順序排。

### 2.2 `#guard_msgs`——把 `#eval` 變成會擋 build 的測試

```lean
/-- info: DivM.res ((), #[2, 4, 6]) -/
#guard_msgs in
#eval (DoubleAll #[1, 2, 3]).run
```

輸出不符就 build 失敗。註解必須是 `/-- ... -/`（三個 `-` 開頭），寫成 `/- ... -/` 不會生效。

這是**寫規格之前**最划算的一步：先用幾個具體輸入確認實作方向對，再去跟 solver 搏鬥。

### 2.3 原生執行檔

前兩種都跑在 Lean 的直譯器裡，離不開 `lake env`。要獨立的執行檔就是 §3–§4 的主題。

---

## 3. `extract_program_for`：抽取可執行程式

### 3.1 它做什麼

```lean
extract_program_for Maximum
```

生成一個 `⟨方法名⟩Exec` 定義。`#print MaximumExec` 的實際輸出：

```lean
def MaximumExec : ℤ → ℤ → DivM ℤ :=
fun a b => NonDetT.run (Maximum a b)
```

就這樣——**它就是幫你把 `.run` 包成具名定義**，沒有別的魔法。功能上
`MaximumExec 3 7` 和 `(Maximum 3 7).run` 完全等價。

那為什麼要用它？三個理由：

1. **型別變乾淨了**：`VelvetM ℤ`（樹）變成 `DivM ℤ`（結果）。這是你要交給 `IO` 那層的東西。
2. **參數自動補齊**：方法有 10 個參數時不用手抄。
3. **`derive_tester_for` 依賴它**：沒先 `extract_program_for` 會直接報
   `no executable found for X, please extract the program first`。

### 3.2 型別對照

| `method` 寫法 | `⟨name⟩Exec` 的型別 |
|---|---|
| `(a : Int) (b : Int) return (m : Int)` | `Int → Int → DivM Int` |
| `(mut arr : Array Int) return (u : Unit)` | `Array Int → DivM (Unit × Array Int)` |
| `(x : Int) (mut y : Int) return (r : Bool)` | `Int → Int → DivM (Bool × Int)` |

規則：**`mut` 參數同時是輸入也是輸出**。輸入位置照原樣，輸出位置接在回傳值後面。

### 3.3 抽取的邊界

抽取要求程式是**可計算的**（computable）。Velvet 的表層語法基本都可計算，但規格裡的東西不一定：

- `ensures` 裡寫 `∃ k, ...`、`Multiset`、`Classical.choice` —— 完全沒問題，
  **規格不會被抽取**，它只活在 `_correct` 定理裡。
- 程式（`do` 區塊）裡呼叫 `noncomputable` 的定義 —— 不行，抽取會失敗。

實務上：規格隨便用數學，程式碼保持可計算，兩邊井水不犯河水。

---

## 4. 編譯成原生執行檔

### 4.1 lakefile：加一個 `lean_exe`

```lean
-- lakefile.lean
@[default_target]
lean_lib VelvetExec        -- Velvet 端：method / prove_correct / extract_program_for

lean_exe velvet_demo where
  root := `Main            -- IO 端：Main.lean 裡的 def main
```

`lean_exe` 的 `root` 指向含 `def main` 的模組。刻意分成兩個檔：
`VelvetExec.lean` 是被驗證的部分，`Main.lean` 是沒被驗證的膠水，界線一眼可見。

### 4.2 `Main.lean`：處理 `DivM`

型別逼你面對「可能不終止」這件事——`DivM α` 不是 `α`：

```lean
import VelvetExec

/-- 把 `DivM` 的結果攤平成 `IO`。 -/
def runDiv [Inhabited α] (name : String) : DivM α → IO α
  | .res x => pure x
  | .div   => throw <| IO.userError s!"{name}: diverged"

def main (args : List String) : IO Unit := do
  let nums := args.filterMap (·.toInt?)
  let arr := if nums.isEmpty then #[1, 2, 3, 4] else nums.toArray

  -- 無 mut：MaximumExec : Int → Int → DivM Int
  let m ← runDiv "Maximum" (MaximumExec 3 7)
  IO.println s!"Maximum 3 7 = {m}"

  -- 有 mut：DoubleAllExec : Array Int → DivM (Unit × Array Int)
  let (_, doubled) ← runDiv "DoubleAll" (DoubleAllExec arr)
  IO.println s!"DoubleAll {arr} = {doubled}"
```

想偷懶的話 Loom 附了 `DivM.run`（注意和 `NonDetT.run` 同名不同物）：

```lean
def DivM.run {α} [Inhabited α] : DivM α -> α
  | DivM.res x => x
  | DivM.div => default        -- 發散時吐 default 值，錯誤被吃掉
```

`.div` 直接變成 `default` —— 快，但把失敗吞了。要區分「結果是 0」和「跑不出來」就得自己 pattern match。

### 4.3 建置與執行

```sh
lake build velvet_demo
./.lake/build/bin/velvet_demo 3 1 4 1 5
```

實際輸出：

```
Maximum 3 7 = 7
DoubleAll #[3, 1, 4, 1, 5] = #[6, 2, 8, 2, 10]
DoubleAllTester #[3, 1, 4, 1, 5] = true
```

也可以 `lake exe velvet_demo 3 1 4 1 5`（順便確保是最新的）。

這是**真的原生執行檔**：Lean 把程式編成 C、再交給 clang 編成機器碼，執行時不需要
Lean 工具鏈、不需要 `.lake/`、不需要 z3。

### 4.4 產物很大——為什麼，以及能不能小

本專案實測（Linux x64）：

| 產物 | 大小 |
|---|---|
| `velvet_demo` | 212 MB |
| `velvet_demo`（`strip -s` 之後） | 165 MB |
| 同一 toolchain 的 `def main := IO.println "hi"` | 9.3 MB |

原因：Lean 的 `lean_exe` 會把**所有 transitively import 的模組的編譯產物靜態連結進來**，
而且不做跨模組的死碼消除。`VelvetExec` import 了 `Velvet.Std`，它拉進 Loom、Auto、
**整個 mathlib**——即使執行期一行都用不到。

可行的對策，由便宜到貴：

1. **`strip -s`**：212 MB → 165 MB。零成本，先做。
2. **接受它**。如果目標是「有個能跑的驗證過程式」，200 MB 的內部工具沒什麼問題。
3. **手寫一份無相依的版本，再證等價**。把演算法用純 Lean（不 import Velvet）重寫成
   `def foo' `，證 `foo' = fun args => (foo args).run`，然後 `Main.lean` 只 import 那份。
   這樣二進位回到 10 MB 等級，代價是多一個等價證明——而且要小心別在證明時把原本
   驗證的性質弄丟。

---

## 5. tester：把規格變成 runtime check

抽取還有第二種用途：讓 `require` / `ensures` **在執行期真的去檢查**。

### 5.1 三道命令

```lean
extract_program_for DoubleAll            -- 先抽（必要前置）
prove_precondition_decidable_for DoubleAll
prove_postcondition_decidable_for DoubleAll
derive_tester_for DoubleAll
```

`prove_*_decidable_for` 幫規格合成 `Decidable` 實例——把 `Prop` 變成能 `decide` 的東西。
它會自動處理常見情形（連 `∀ i, i < arr.size → ...` 這種有界全稱都行，實測可過）；
合成不掉的部分會留成 proof goal，用 `by` 接手：

```lean
prove_postcondition_decidable_for Method by (
  simp_all
  exact instDecidableIff
)
```

> 提示：規格裡用到的自訂 `def`，標上 `@[loomAbstractionSimp]` 可以大幅提高自動合成的成功率。

`derive_tester_for` 把三塊組起來，產生 `⟨name⟩Tester : ⟨參數⟩ → Bool`：

```lean
-- 展開後的形狀
if decide ⟨require⟩ then
  match ⟨name⟩Exec args with
  | DivM.res ret => decide ⟨ensures⟩
  | _            => false            -- 發散算失敗
else true                            -- 前置條件不成立 → 不算數，回 true
```

讀 tester 結果時記住兩件事：**`true` 可能只是因為前置條件不成立**（vacuous pass），
而**發散算 `false`**。

### 5.2 它真的抓得到 bug

`DoubleAllBuggy` 少跑最後一格（`while i < arr.size - 1`）：

```lean
/-- info: DivM.res ((), #[2, 4, 3]) -/   -- 最後的 3 沒被加倍
#guard_msgs in
#eval DoubleAllBuggyExec #[1, 2, 3]

/-- info: false -/
#guard_msgs in
#eval DoubleAllBuggyTester #[1, 2, 3]
```

關鍵：**tester 不需要 `prove_correct`**。`DoubleAllBuggy` 根本證不出來，但 tester 照跑不誤。

### 5.3 配 Plausible 做隨機測試

```lean
run_elab do
  let g : Plausible.Gen (Array Int × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    pure (arr, DoubleAllBuggyTester arr)
  for _ in [0:200] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break
```

實測輸出（每次跑到的反例不同）：

```
info: VelvetExec.lean:117:0: postcondition violated for input #[8]
```

`run_elab` 在**編譯期**跑，反例直接出現在建置輸出裡。

這件事的價值在於順序：**先隨機測、再驗證**。`loom_solve` 失敗時，你分不清是「規格錯了」、
「實作錯了」還是「solver 不夠力」——這三種的處理方式完全不同。隨機測試幾秒鐘就能把前兩種篩掉。

---

## 6. 陷阱：驗證過 ≠ 跑得完

### 6.1 partial correctness 下，不終止的程式也能通過驗證

實測。這個方法有 `prove_correct` 而且**過了**：

```lean
set_option loom.semantics.termination "partial"

method Spin (n : Int) return (r : Int)
    ensures r = 0
    do
    let mut i := 0
    while i ≥ 0
      invariant i ≥ 0
    do
      i := i + 1
    return 0

prove_correct Spin by
  loom_solve          -- ✓ 通過
```

抽取出來執行：

```lean
extract_program_for Spin
#eval SpinExec 1      -- 掛住，永遠不會結束
```

**不會回傳 `DivM.div`，是真的當掉。** 因為 §1.3 說過，`.repeatCont` 跑起來就是
`forIn Lean.Loop.mk`——一個真正的無窮迴圈。`.div` 只在 `.pickCont` 找不到見證時才出現。

這不是 bug，是 partial correctness 的定義：「**如果**終止，結果滿足 `ensures`」。
把它抽取成執行檔，就等於把這個「如果」交給了執行期。

### 6.2 要終止保證就切 `total`

```lean
set_option loom.semantics.termination "total"
```

同一個 `Spin`，實際錯誤訊息：

```
error: Decreasing annotations are required in total correctness semantics
error: Failed to prove assertion without names: WPGen (forIn Lean.Loop.mk 0 fun x r => ...)
```

total 語意強制每個 `while` 都要有 `decreasing ⟨遞減量⟩`，而且要證得出來。

反過來，在 `partial` 底下寫 `decreasing` 會拿到警告：

```
warning: Decreasing annotations are not checked in partial correctness semantics
```

—— 白寫的。**要打算抽取成執行檔的程式，認真考慮用 `total`。**

### 6.3 規格太弱

抽取只保證「程式滿足規格」，不保證「規格滿足意圖」。這是驗證的原罪，抽取幫不上忙。
[VelvetTutorial.md](VelvetTutorial.md) 有一整組「驗證會過但方法根本不對」的範例。

實務對策：對每個規格問一次「什麼都不做 / 回傳常數，會不會也通過？」，然後用 §5 的
tester 拿真實輸入戳它。

---

## 7. 抽取到其他程式語言？

**Velvet 沒有多語言後端。** `extract_program_for` 唯一做的事就是包 `NonDetT.run`
（§3.1），產物是 Lean 的值。這一點和 Coq（extraction 到 OCaml/Haskell）、
F\*（到 OCaml/C/Wasm）、Dafny（到 C#/Java/Go/Python/Rust）不同——Velvet 的
「multi-modal」指的是 SMT／互動式證明／隨機測試三種**驗證模式**，不是多個編譯目標。

### 7.0 「先展開成 Lean 4，再萃取出其他語言」行不行？

這是最自然的想法，值得認真拆開看。分成三個問題：

**問題一：Velvet 展開得成 Lean 4 嗎？——已經是了。**

§1.1 就講過，`method` 產生的是一個普通的 Lean `def`。`#print Maximum` 給你
`fun a b => if a ≥ b then pure a else pure b`。**沒有「展開」這一步要做**，
Velvet 從來就沒有自己的中間語言。

**問題二：那 Lean 4 有沒有萃取到其他語言？——沒有。**

Lean 4 只有兩個後端，而且都不是 Coq 意義下的 extraction：

| 後端 | 狀態（本專案 Lean 4.24.0 實測） |
|---|---|
| C（`--c`，預設） | 可用，但產物是 `lean_object*` + refcount 的 runtime 呼叫，不是可讀的 C |
| LLVM bitcode（`--bc`） | **官方 release 沒編進去**。`lean --features` 回 `[]`；`lean -b out.bc f.lean` 直接 assertion violation：`Please build a version of Lean4 with -DLLVM=ON` |

兩個後端共用同一套執行模型（GC / refcount / boxed `lean_object`），所以**不管走哪個，
你都得帶著 Lean runtime**。這正是 §7.1 FFI 那條路的由來——不是繞路，那就是唯一的原生路。

**問題三：那把它「攤平」成乾淨的 Lean 再翻譯呢？——方向對，但抽取版沒有你想的乾淨。**

看實際的編譯器 IR（`set_option trace.compiler.ir.result true`）。`Maximum` 只是一個
if-then-else，但 `MaximumExec` 編出來是這樣：

```
def Loop.forIn.loop._at_.NonDetT.run._at_.MaximumExec.spec_0.spec_0._redArg (x_1 : obj) (x_2 : tobj) : tobj :=
  inc x_1;
  let x_3 : obj := app x_1 x_2;
  let x_4 : tobj := NonDetT.run._at_.MaximumExec.spec_0._redArg x_3;
  case x_4 : tobj of
  DivM.res → ...
  DivM.div → ...
```

一個取最大值的函數，IR 裡有**整個 `NonDetT.run` 直譯器**（連 `repeatCont` 的迴圈分支都被
specialize 進來了，即使 `Maximum` 沒有迴圈）、`DivM` 的建構子、還有 `inc`/`dec`/`isShared`
這些 refcount 操作。

原因是 §1.2–1.3 的架構：`Maximum a b` 是一棵**語法樹**，`run` 是**直譯器**。
`extract_program_for` 不做 partial evaluation——執行期真的會配置一個 `NonDetT.pure`
節點，再 pattern match 把它拆掉。

量化一下依賴閉包（遞迴收集定義用到的常數個數）：

| 定義 | 常數個數 |
|---|---|
| `maximumPure`（手寫純 Lean） | 96 |
| `MaximumExec`（Velvet 抽取） | 349 |
| `doubleAllPure := arr.map (2 * ·)` | 302 |
| `DoubleAllExec`（Velvet 抽取） | **2464** |

**要翻譯到其他語言，你要翻的是這個閉包。** 2464 個常數（`NonDetT`、`DivM`、CCPO、
`MProdWithNames`……）是不可能人工翻的；302 個（大多是 `Array`/`Int` 的標準庫）才有機會。

**結論**：「展開成乾淨的 Lean 4」確實是正確的第一步，但那不是 `extract_program_for`
幫你做的事，得自己做——也就是 §7.3 的路線 C。做完之後，那份純 Lean 函數只用
`Int`／`Array`／`if`／遞迴，才真的能 1:1 對到 Rust/Go/C。

好消息是這一步在**無迴圈**的情況下便宜到不可思議（實測兩行就過）：

```lean
def maximumPure (a b : Int) : Int := if a ≥ b then a else b

example (a b : Int) : MaximumExec a b = .res (maximumPure a b) := by
  unfold MaximumExec Maximum maximumPure
  split <;> rfl
```

壞消息是**有迴圈就不能只靠 `unfold`**。`unfold` 之後 goal 裡還躺著
`forIn Lean.Loop.mk ...`，要往下走得用 `Loop.forIn.loop.fixpoint_induct`
並自己滿足 `Lean.Order.admissible motive`——對「等式」型的 motive 這不是 free。

（順帶一提，這裡有個 Loom 設計得很漂亮的地方：Lean core 的 `Loop.forIn` 是
`partial def`，對邏輯完全不透明，證不了任何事。Loom 用 `@[instance high]` 蓋掉它，
換成自己用 **`partial_fixpoint`** 定義的版本——CCPO 上的單調不動點，
**既可執行又有 `fixpoint_induct`**。迴圈能同時被跑和被證，靠的就是這個。）

> 順手可以檢查信任基礎：`#print axioms DoubleAll_correct` 在本專案回
> `[propext, Classical.choice, Quot.sound]`——標準三條，沒有 `sorryAx`。
> 注意 Loom 有 `axiom trust_smt : ∀ (p : Prop), p`（`Loom/SMT.lean`），
> 走 z3/cvc5 的證明會多出這一條；上面這些例子是 `grind` 解掉的，所以沒有。

以下三條路的成本與可信度差很多。

### 7.1 路線 A：Lean 的 C 後端 + FFI（可行，已實測）

Lean 4 本來就會把程式編成 C（`.lake/build/ir/*.c`），再交給 clang。所以
**其他語言可以用 FFI 呼叫抽取出來的程式**，不需要任何翻譯。

Lean 端加一層 `@[export]`（[VelvetFFI.lean](../VelvetFFI.lean)）：

```lean
import VelvetExec

@[export velvet_maximum]
def velvetMaximum (a b : UInt64) : UInt64 :=
  match MaximumExec (a.toNat : Int) (b.toNat : Int) with
  | .res r => r.toNat.toUInt64
  | .div   => 0
```

Lean 產生的 C 標頭就是一個乾淨的 C 簽名（`.lake/build/ir/VelvetFFI.c` 裡實際長這樣）：

```c
LEAN_EXPORT uint64_t velvet_maximum(uint64_t, uint64_t);
```

C 端呼叫它（[ffi/main.c](../ffi/main.c)），只需要先起 Lean runtime：

```c
lean_initialize_runtime_module();
lean_object* res = initialize_VelvetFFI(1, lean_io_mk_world());
lean_dec_ref(res);
lean_io_mark_end_initialization();
printf("%lu\n", (unsigned long)velvet_maximum(3, 7));   // 7
```

Python 端用 ctypes 打 `.so`（[ffi/demo.py](../ffi/demo.py)）也一樣，
只是 `lean_io_mk_world()` 在 C 裡是 inline、`.so` 沒有這個符號，要自己傳
`lean_box(0)`（就是指標值 `1`）：

```python
lib = ctypes.CDLL("libvelvet.so", mode=ctypes.RTLD_GLOBAL)
lib.lean_initialize_runtime_module()
lib.initialize_VelvetFFI(1, ctypes.c_void_p(1))    # lean_box(0)
lib.lean_io_mark_end_initialization()
lib.velvet_maximum.restype = ctypes.c_uint64
lib.velvet_maximum(3, 7)                            # 7
```

一鍵重現（實測輸出如下）：

```sh
./ffi/build.sh
# ==> 產物
#   ffi/out/c_demo         可執行檔，直接跑：./ffi/out/c_demo
#   ffi/out/libvelvet.so   共享函式庫，不能直接執行，給 ctypes/FFI 載入：...
#   ffi/out/build/         中間檔（main.o、link_cmd.txt），不能執行，可安全刪除
#
# ==> C:
# velvet_maximum(3, 7)   = 7
# velvet_maximum(42, 17) = 42
# ==> Python:
# velvet_maximum(3, 7) = 7
# ...
```

三個產物的差別（以及為什麼 `build/main.o` 是 `chmod +x` 也跑不起來的目的檔）
另見 [ffi/README.md](../ffi/README.md)。

**代價與限制**（都是實測踩到的）：

- **要帶著 Lean runtime**。`c_demo` 212 MB、`libvelvet.so` 55 MB，而且執行前一定要
  呼叫 `lean_initialize_runtime_module()` 和模組的 `initialize_*`。
  靜態連結的 `c_demo` 之後就自給自足了（`ldd` 只剩 libc/pthread/m/dl/rt），
  但 `.so` 版本是動態連 `libleanshared.so`，跑的時候要 `LD_LIBRARY_PATH=$(lean --print-prefix)/lib/lean`。
- **型別要在邊界上翻譯**。只有 `UInt8/16/32/64`、`USize`、`Bool`、`Float` 這些
  scalar 會變成原生 C 型別；`Int`（GMP 大整數）、`Array`、`String` 過去都是
  `lean_object*`，要照 Lean 的物件表示法和 refcount 規則操作。上面的例子刻意用
  `UInt64` 包一層就是為了避開這件事。**這一層 wrapper 沒有被驗證**——`Int` 轉
  `UInt64` 溢位了誰也不負責。
- **Lake 沒有一級的 shared library target**。`lake build VelvetFFI:shared` 在本專案
  會撞 `ld.lld: error: duplicate symbol`；直接對靜態 runtime 下 `-shared` 則會撞
  `relocation R_X86_64_TPOFF32 against lean::g_heartbeat cannot be used with -shared`
  （`libleanrt.a` 不是 PIC，要換成 `-lleanshared`）。`ffi/build.sh` 的做法是撈
  `lake build -v` 印出來的連結指令再改寫——能用，但 Lake 改輸出格式就會壞。

適用情境：**你的主程式是別的語言，想把某個關鍵演算法換成驗證過的版本**。

### 7.2 路線 B：手寫目標語言版本 + 差分測試

Velvet 抽取的東西沒辦法變成漂亮的 Rust/Go 原始碼（Lean 產生的 C 全是
`lean_object*` 和 refcount，見 `.lake/build/ir/VelvetExec.c`），所以要「乾淨的目標語言程式碼」
只能自己寫。

但 §5 的 tester 讓這件事沒那麼糟：`FooTester` 是**可執行的規格**，可以拿它當
oracle 對你手寫的版本做差分測試——同一組隨機輸入餵兩邊，比對結果。

這**不是證明**，只是測試。但比起「照著文件重寫一遍然後祈禱」，已經好很多。

### 7.3 路線 C：在 Lean 裡重寫成無相依版本 + 證等價

§7.0 說的「先展開成乾淨的 Lean 4」，具體就是這條：用純 Lean（不 import Velvet）
寫一份 `foo'`，證 `foo' args = (foo args).run`，然後 `Main.lean`／翻譯工作只針對那一份。

兩種收穫：

- **想要小執行檔**：依賴閉包從 2464 掉到 302，二進位回到 10 MB 等級，等價性有證明背書。
- **想翻譯到其他語言**：`foo'` 只用 `Int`／`Array`／`if`／遞迴，人工或工具翻譯到
  Rust/Go/C 都是 1:1 的對應，review 得動。

成本就是那個等價證明：**無迴圈兩行，有迴圈要動 `fixpoint_induct`**（§7.0）。
迴圈多的程式，這條路可能比重新在目標語言裡驗證還貴——先估算再投入。

本專案的 [LeanLC917.lean](../LeanLC917.lean) 就是這種「零相依純 Lean + 完整證明」的樣子。

### 7.4 選哪條

| 你要的 | 路線 | 可信度 |
|---|---|---|
| 從 C/Python/Rust 呼叫驗證過的演算法 | A（FFI） | 高（wrapper 那層除外） |
| 乾淨的 Rust/Go/TypeScript 原始碼 | C 之後再手動翻譯，或 B | C 高、B 低 |
| 小的獨立執行檔，不換語言 | C（無相依重寫 + 證等價） | 高 |
| 只是要跑起來 | §4 的 `lean_exe` | 高 |

至於「自己寫一個 Lean → X 的後端」：技術上不是死路，Lean 的 IR 讀得到
（`set_option trace.compiler.ir.result true`，或直接用 `Lean.IR` 的 API），
針對一個受限子集發射 Rust/Go 是可以想像的。但那是**寫編譯器後端**的工程量，
而且信任基礎要重建一次——Lean 的 refcount 記憶體模型對應到目標語言的語意，
本身就是一個需要證明的命題。沒有現成的東西可以用。

---

## 8. 速查表

### 命令

| 命令 | 生成 | 型別 |
|---|---|---|
| `method Foo ...` | `Foo` | `... → VelvetM α` |
| `prove_correct Foo by ...` | `Foo_correct` | `triple pre (Foo args) post` |
| `extract_program_for Foo` | `FooExec` | `... → DivM (α × muts)` |
| `prove_precondition_decidable_for Foo` | `FooPreDecidable` | `Decidable pre` |
| `prove_postcondition_decidable_for Foo` | `FooPostDecidable` | `Decidable post` |
| `derive_tester_for Foo` | `FooTester` | `... → Bool` |

### 執行方式

| 需求 | 做法 |
|---|---|
| 互動時看一眼結果 | `#eval (Foo args).run` |
| 把結果釘成會擋 build 的測試 | `/-- info: ... -/` + `#guard_msgs in` + `#eval` |
| 具名的可執行版本 | `extract_program_for Foo` → `FooExec args` |
| 獨立執行檔 | `lean_exe` + `Main.lean` + `lake build ⟨exe⟩` |
| 執行期檢查規格 | `derive_tester_for Foo` → `FooTester args` |
| 驗證前的隨機測試 | `run_elab` + `Plausible.Gen` + `FooTester` |

### 型別

| 名字 | 定義 | 意義 |
|---|---|---|
| `VelvetM α` | `NonDetT DivM α` | 程式**樹**，還不能跑 |
| `NonDetT.run` | `NonDetT m α → m α` | 把樹解釋成計算 |
| `DivM α` | `.res x \| .div` | 跑完的結果，`.div` = 發散 |
| `DivM.run` | `DivM α → α`（需 `Inhabited`） | 攤平，`.div` 變 `default` |

### 完整流程

```
method + require/ensures          寫規格與實作
        ↓
#eval / #guard_msgs               先確認方向對（秒級）
        ↓
extract_program_for               抽出 FooExec : ... → DivM _
        ↓
derive_tester_for + Plausible     隨機測試，篩掉規格/實作的錯（秒級）
        ↓
prove_correct + loom_solve        正式驗證（分鐘級）
        ↓
lean_exe + Main.lean              編譯成原生執行檔
```

抽取的正確性由 `ExtractNonDet.extract_refines` 保證；剩下的風險全在**規格本身**和
**`Main.lean` 那層沒被驗證的膠水**。

---

## 延伸閱讀

- [VelvetTutorial.md](VelvetTutorial.md) — Velvet 語法入門六例
- [INSTALL.md](INSTALL.md) — 環境安裝與建置
- [Velvet 官方文件](https://github.com/verse-lab/velvet/blob/master/velvet_documentation.md) — §6 Testing
- `.lake/packages/Loom/Loom/MonadAlgebras/NonDetT/Extract.lean` — `NonDetT.run` 與 refinement 定理
- `.lake/packages/Velvet/Velvet/Syntax.lean` — 上面每個命令的 elaborator
