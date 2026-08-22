# 第 00 次優化 — 環境勘查報告

**日期**：2026-08-21
**狀態**：✅ 完成
**範圍**：只勘查，不寫任何規格。所有結論皆由**實際編譯**取得，非閱讀推測。

---

## 0. 三十秒摘要

指引 §9 的設計稿**大體可行**，但有 **7 項實測發現**會改寫後續步驟，其中 3 項是決定性的：

| # | 發現 | 影響 |
|---|---|---|
| **F1** | `method` 巨集把回傳型別**寫死成 `VelvetM τ`**（`Velvet/Syntax.lean:343`） | **第 09 次的 `SortM` 不可能用 `method` 語法**。§6.9 的 Q1 已提前有答案：否。 |
| **F2** | **分身計數器作弊實測「通過」**——完整插入排序、做滿所有比較、全部記到 `fake`、`ticks` 一動不動，`prove_correct` 綠燈 | §2.4 的 open problem **經驗證屬實**。第 09 次是必要的，不是假設性的。 |
| **F3** | `[part\|` 記號**有歧義**（Loom 與 Velvet 各定義一個同名記號） | 第 03 次起每個 `structure` 都要改用 `open ... in` 寫法 |
| F4 | `Array.toMultiset` **不需要任何 typeclass** | 第 08 次的關鍵前提成立 |
| F5 | `private mk` 三種偽造路徑**全部**被跨模組擋下 | 第 06 次的機制如設計運作 |
| F6 | Velvet 把 `ensures` 子句**反序**合取 | 第 03 次的 `SortSpec` 要配合，否則要寫橋接證明 |
| **F7** | **基準 `lake build` 是紅的**（既有失敗，非本次造成） | **R4 需要一個決定**，見 §6 |

---

## 1. 基本環境

```
lean-toolchain : leanprover/lean4:v4.24.0
lakefile       : lakefile.lean（Lake DSL，非 toml）
Velvet         : git dependency @ master，位於 .lake/packages/Velvet/
Loom           : git dependency，位於 .lake/packages/Loom/
```

### 1.1 ⚠ 與指引 R1 的出入：`Velvet/` 不在專案內

指引 R1 說「放在專案 Lean source root 底下（**與 `Velvet/` 同層**）」。

本專案的 `Velvet/` 是 **git 外部依賴**（`.lake/packages/Velvet/Velvet/`），不是專案內的資料夾。
因此「與 Velvet 同層」在此無法字面套用。採用的解讀是「**專案的 Lean source root**」，即專案根目錄——與 `LeanPulse/`、`VelvetTutorial.lean` 同層：

```
/home/claw/Repo/Lean-Pulse/
├─ LeanPulse/  LeanPulse.lean  VelvetTutorial.lean  …   ← 既有
└─ SortRubric/                                           ← ★ 本次新建
```

R1「不得修改 Velvet 本體」自動滿足——它在 `.lake/packages/` 底下，不會被碰到。

### 1.2 ⚠ 與指引 R1 的第二處出入：必須改 `lakefile.lean`

Lake 不會自動收錄新資料夾。已在 `lakefile.lean` **末尾附加**（未改動任何既有行）：

```lean
-- 排序 rubric 分階段強化：十次優化（Opt01–Opt10 + 選配 Opt11）
@[default_target]
lean_lib SortRubric where
  globs := #[Glob.submodules `SortRubric]
```

**已實測確認**：
- `lake build SortRubric` 綠燈（用一個 `Smoke.lean` 驗證後刪除）
- **不需要**根檔 `SortRubric.lean`——`Glob.submodules` 自己處理。R1「只新建一個資料夾」得以完整遵守。
- 空資料夾也能 build（`Build completed successfully (1 job)`）

---

## 2. 真實 API 逐字摘錄

### 2.1 `method` 的語法（`Velvet/Syntax.lean:51-77`）

```lean
declare_syntax_cat leafny_binder

syntax "(" ident ":" term ")" : leafny_binder
syntax "(mut" ident ":" term ")" : leafny_binder
syntax "require" termBeforeReqEnsDo : require_caluse
syntax "ensures" termBeforeReqEnsDo : ensures_caluse

syntax "method" ident leafny_binder* "return" "(" ident ":" term ")"
  (require_caluse )*
  (ensures_caluse)* "do" doSeq
  Termination.suffix : command

declare_syntax_cat prove_correct_command
syntax "prove_correct" : prove_correct_command
syntax "prove_correct?" : prove_correct_command
syntax prove_correct_command ident Termination.suffix "by" tacticSeq : command
```

**關鍵限制**：`leafny_binder` 只有兩種形式。**沒有 `{implicit}`、沒有 `[instance]`**。
→ typeclass 只能靠 section 層級的 `variable [C α]` 帶進來（`Velvet/Demo/Demo.lean:42` 即如此）。

注意拼字：是 `require`（單數，無 s），不是 `requires`。指引 §2.4 寫的 `requires` 是 F\*/Pulse 的拼法。

### 2.2 `mut` = tuple threading（`Velvet/Syntax.lean:96-98, 215, 330-337, 343`）

```lean
| `(leafny_binder| (mut $id:ident : $tp:term)) => do
  let idOld := mkIdent <| id.getId.appendAfter "Old"          -- ← xOld 的來源
```

```lean
  if argName ∈ modArgs then throwErrorAt arg s!"mutable arguments cannot alias"
```

```lean
    let mutTypes ← getMutTypes binders
    let mut retType : Term <- `($type)
    if mutTypes.size != 0 then
      ...
      retType <- `($retType × $mutTypeProd)                    -- ← mut 併進回傳 tuple
```

```lean
      def $name $bindersIdents* : VelvetM $retType:term := do $mods* $doSeq*
```

**這四段合起來，字面證實了指引 §2.4 的三點主張**：
`mut` 是 tuple 語法糖；唯一的額外檢查是「同一次呼叫的兩個 mut 參數不能 alias」；沒有所有權、沒有分離邏輯。

### 2.3 `VelvetM` 與 `triple`

`Velvet/VelvetTheory.lean:1-8`：
```lean
import Loom.MonadAlgebras.NonDetT.Extract

abbrev VelvetM α := NonDetT DivM α

set_option quotPrecheck false in
notation "[totl|" t "]" => open TotalCorrectness TotalCorrectness.DemonicChoice in t
set_option quotPrecheck false in
notation "[part|" t "]" => open PartialCorrectness PartialCorrectness.DemonicChoice in t
```

`Loom/MonadAlgebras/WP/Basic.lean:19-23`：
```lean
def wp (c : m α) (post : α -> l) : l := liftM (n := Cont l) c post
def triple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ≤ wp c post
```

> **⚠ 指引筆誤**：指引通篇寫 `[total| ...]`，真實記號是 **`[totl|`**（四個字母）。

### 2.4 `Array.toMultiset`（`Velvet/Std.lean:103`）★ 第 08 次的關鍵

```lean
def Array.toMultiset (arr : Array α) := Multiset.ofList arr.toList
```

**逐字確認：完全沒有 typeclass 約束。** 對任意 `α : Type` 可用，不需 `DecidableEq`。
指引 §6.8「要確認的事」得到**正面**答案——第 08 次不會因此 BLOCKED。

實測（`probe/P1.lean`）：
```lean
example (α : Type) (a : Array α) : Multiset α := a.toMultiset   -- ✅ 編譯通過
```

搬移保存引理則**需要** `[Inhabited α]`（`Velvet/Std.lean:105`）：
```lean
theorem Array.multiset_swap [Inhabited α]
  (arr: Array α) (idx₁ idx₂: Nat) (h_idx₁: idx₁ < arr.size) (h_idx₂: idx₂ < arr.size) :
  ((arr.set! idx₂ arr[idx₁]!).set! idx₁ arr[idx₂]!).toMultiset = arr.toMultiset
```

### 2.5 官方 `insertionSort`（`Velvet/Examples/Examples.lean:50-77`）★ 主要範本

```lean
attribute [grind] Array.multiset_swap

method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arrOld.size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant arr.toMultiset = arrOld.toMultiset
    done_with n = arr.size
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arrOld.size
      invariant mind ≤ n
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arrOld.toMultiset
      done_with mind = 0
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1
    return
```

**印證了指引 §6.2 的三分類與三個陷阱**：
- Structural（`arr.size = arrOld.size`）／Ordering（區域有序）／Preservation（`toMultiset`）三類俱全
- 陷阱 2 得到證實：`arr.size = arrOld.size` 確實是可由 multiset 推出的**冗餘**，官方仍然留著
- 外部 spec 用**全域** `i ≤ j` 版本，未弱化

`swap!` 是 Velvet 的 doElem（`Velvet/Std.lean:70`），語法為 `swap! id1[idx1]! id2[idx2]!`。

### 2.6 `chain_le`（`Velvet/Examples/IsSorted.lean`）

```lean
def chain_le (a : Array Int) (h_adjacent : ∀ k, 0 ≤ k ∧ k < a.size - 1 → a[k]! ≤ a[k+1]!)
    (i j : Nat) (h_i_ge : 0 ≤ i) (h_i_lt_j : i < j) (h_j_lt_size : j < a.size) : a[i]! ≤ a[j]! :=
  if h : j = i + 1 then by
    rw [h]; exact h_adjacent i ⟨h_i_ge, by omega⟩
  else by
    have h_next : i + 1 < j := by omega
    have h_step1 := h_adjacent i ⟨h_i_ge, by omega⟩
    have h_step2 := chain_le a h_adjacent (i + 1) j (by omega) h_next (by omega)
    exact le_trans h_step1 h_step2
termination_by j - i

lemma adjacent_to_global_sorted (a : Array Int) : … 
attribute [grind] adjacent_to_global_sorted
```

**注意**：`chain_le` 寫死 `Array Int` 與 `≤`。第 08 次抽象化 α 之後，若需要相鄰→全域的手法，**必須自己改寫成 `SpecOrder.trans` 版本**（`le_trans` → `ord.trans`）。這是一筆已知的移植成本。

### 2.7 total/partial 切換（`Velvet/Examples/Total_Partial_example.lean`）

檔案結構逐字確認為 **section 層級**：

```lean
section
set_option loom.semantics.termination "partial"
…
method insertionSort_part …            -- 完整 invariant，真正的 postcondition
prove_correct insertionSort_part by loom_solve!
end

section
set_option loom.semantics.termination "total"
…
method insertionSort_termination …     -- decreasing，ensures True
prove_correct insertionSort_termination by loom_solve!
end

set_option loom.semantics.termination "total"
method insertionSort_result …          -- 無標註，真正的 postcondition
prove_correct insertionSort_result by
  exact VelvetM.total_decompose_triple
    (insertionSort_termination arrOld) (insertionSort_part arrOld) (insertionSort_result arrOld)
    (eqx := by rfl) (eqy := by rfl) triple_termination triple_res
```

`Velvet/VelvetTheory.lean:183-185`：
```lean
lemma VelvetM.total_decompose_triple {α : Type} {pre : Prop} {post : α -> Prop}
  (x y z: VelvetM α) (termination: [totl| triple pre x fun _ => True])
  (postcondition: [part| triple pre y post]) {eqx: x = z} {eqy: y = z}:
  [totl| triple pre z post]
```

**指引 §6.11 的代價評估完全正確**：三份 body、`by rfl` 要求定義相等、section 層級的 set_option。

---

## 3. §4.3 四個問題的答案（全部**實測**）

### Q1. `method` 能不能吃 `structure` 型別的參數？ → ✅ **能**

`probe/P1.lean`，實際編譯通過：

```lean
structure Ticks where
  val : Nat

method P1_bumpTicks (mut t : Ticks) return (u : Unit)
  ensures t.val = tOld.val + 1
  do
    t := { val := t.val + 1 }
    return

prove_correct P1_bumpTicks by loom_solve      -- ✅ 綠
```

`structure` 型別連 `mut` 都能用。第 03、07、08 步的基礎成立。

`#print P1_bumpTicks_correct` 的輸出（★ 這是 `_correct` 定理的真實形狀）：
```
theorem P1_bumpTicks_correct : ∀ (tOld : Ticks),
  {have t := tOld;
    True}P1_bumpTicks tOld{x,match x with
    | (u, t) => t.val = tOld.val + 1}
```

三點值得記下：
1. 定理名是 `<method>_correct`，參數是各 `mut` 參數的 **`Old` 版**
2. 前條件是 `have t := tOld; True`（不是裸的 `True`）——但**與 `True` 定義相等**（實測 §3.Q1-補 確認）
3. 後條件是 `match x with | (u, t) => …`——但**與 `… x.2` 定義相等**（結構 eta）

### Q2. `method` 的參數能不能是多型的 `(α : Type)`？ → ✅ **能**，兩種寫法

`probe/P2.lean` / `probe/P3.lean`：

```lean
-- (a) 顯式 (α : Type) leafny binder：✅ 通過
method P2_idArray (α : Type) (mut a : Array α) return (u : Unit)
  ensures a.toMultiset = aOld.toMultiset
  do return
prove_correct P2_idArray by loom_solve

-- (b) auto-bound implicit α + variable [Inhabited α]：✅ 通過
variable [Inhabited α]
method P3_withOrd (ord : SpecOrder α) (mut a : Array α) return (u : Unit)
  ensures a.toMultiset = aOld.toMultiset
  ensures ∀ i j, i ≤ j ∧ j < a.size → (ord.le a[i]! a[j]! ∨ True)
  do return
prove_correct P3_withOrd by loom_solve
```

#### ⚠⚠ 但發現一個指引沒提到的硬約束：`a[i]!` 需要 `[Inhabited α]`

不加 `variable [Inhabited α]` 時的**逐字錯誤訊息**：
```
probe/P2.lean:21:46: error: failed to synthesize
  Inhabited α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
probe/P2.lean:21:52: error: failed to synthesize
  Inhabited α
```

**這對第 08 次是好消息，不是壞消息，但必須寫進 Notes：**

`Inhabited α` **不違反** M2 面 3。理由：

| typeclass | 給實作什麼能力 | 面 3 是否失效 |
|---|---|---|
| `DecidableRel (·≤·)` | 算出 `x ≤ y` | ✗ **當場失效**（指引 §6.8 已警告） |
| `DecidableEq α` | 算出 `x = y` | ✗ 失效 |
| `FinEnum α` | 列舉所有 α | ✗ 失效 |
| **`Inhabited α`** | 生出一個 `default : α` | ✅ **不失效**——能「生」不能「觀察」 |

`Inhabited` 只提供 `default`，沒有任何比較兩個 α 的途徑。作弊者可以用 `default` 填滿陣列，但那會**當場違反 `SameElements`**。
且 `Array.multiset_swap` 本身就要求 `[Inhabited α]`，官方範例通篇使用 `[i]!`——這是 Velvet 的既定寫法，不是本專案的妥協。

#### ⚠ 更正一處：`Inhabited` 的安全性是**有條件的**，不是無條件的

上表「只能生，不能觀察」的敘述不完整。精確的敘述是：

> `Inhabited α` 安全，**條件是 `SameElements` 留在後條件裡。**

`default` 讓實作能生出**輸入裡沒有的元素**（例如把整個陣列填成 `default`）。
擋住它的是 multiset 相等，**不是 `Inhabited` 本身無害**。
這個依賴關係已寫進 [`README.md`](README.md) 的 typeclass 預算表。

#### 能不能連 `Inhabited` 都不要？——實測結果：代價高，保留

| 層 | 能否避開 `Inhabited` | 證據 |
|---|---|---|
| **規格層** | ✅ **能** | `probe/I1.lean`：`a[i]'(by omega)`（dependent indexing）與 `a[i]?` 兩種寫法都對抽象 α 編譯通過 |
| **實作層** | ❌ 實務上不能 | `swap!` 展開成 `getElem!`（`Velvet/Std.lean:70`）→ `failed to synthesize Inhabited α`；改用非 bang 的 `swap` 雖能避開，但 polymorphic 下的界內證明無法自動導出 |
| **證明層** | ❌ **決定性** | `Array.multiset_swap [Inhabited α]`（`Velvet/Std.lean:105`）是每一條 preservation invariant 都要用的 `[grind]` 引理，**它自己就要求 `Inhabited`**；`Array.get_set_c [Inhabited α]`（`:77`，帶 `[grind =]`）同理 |

**判準**（「代價低就換掉；不需要論證的約束勝過需要論證的約束」）**的適用結果**：
代價是「在 Velvet 之外重證核心陣列引理 + 與所有官方範例分岔」，屬於高成本，
因此**保留 `Inhabited`**，並把上面那條**條件式**論證寫進 Notes 與預算表。

#### 順帶記下的兩個 API 事實（已進 ERRATA）

- 非 bang 的 `swap $a[$i] $b[$j]` 存在（`Velvet/Std.lean:64`），展開成 `getElem` + `Array.set!`，**不需要 `Inhabited`**
- dependent if（`if h : cond then …`）在 `method` body 內**是支援的**（`probe/I4.lean` 通過）；
  I2/I3 看到的 `PUnit.{...}` universe mismatch 來自 polymorphic α 下 `getElem` 的界內證明無法導出，不是 dependent if 的問題

### Q3. `set_option loom.semantics.termination` 是 section 層級還是 per-method？ → **section 層級**

由 `Total_Partial_example.lean` 的檔案結構直接確認（見 §2.7）：三個 `section … end` 包住三種模式。
**沒有** per-method 的寫法。指引 §6.11 的判斷正確，第 11 次的代價評估不需修正。

### Q4. `loom_solve` 在什麼情況下會失手？ → 實測到 **4 種**

| # | 失手情境 | 症狀 | 解法 |
|---|---|---|---|
| 1 | `grind.splits` 不足 | 巢狀迴圈的 ordering invariant `Failed to prove assertion` | `set_option loom.solver.grind.splits 40` |
| 2 | 缺支撐 `done_with` 的 invariant | `unsolved goals` / `case «done_1: …»` | 補 `invariant i ≤ arr.size` |
| 3 | 缺 `[grind]` 引理 | multiset 保存跨 swap 證不出 | `attribute [grind] Array.multiset_swap` |
| 4 | `loom_solve` 力道不足 | 巢狀迴圈殘留目標 | 改用 `loom_solve!` |

#### 情境 1 的逐字錯誤訊息（`probe/P4.lean`，未設 splits 時）
```
probe/P4.lean:36:18: error: Failed to prove assertion
case a.right.left.left.left.left.left.right.right.left
⊢ ∀ (i j : ℕ),
    0 ≤ i → i < j → j ≤ n → j ≠ mind - 1 →
            ((arr_1.set! mind arr_1[mind - 1]!).set! (mind - 1) arr_1[mind]!)[i]! ≤
              ((arr_1.set! mind arr_1[mind - 1]!).set! (mind - 1) arr_1[mind]!)[j]!
probe/P4.lean:49:30: error: unsolved goals
```

#### 情境 2 的逐字錯誤訊息（`probe/P5.lean`，未補 `i ≤ arr.size` 時）
```
probe/P5.lean:27:30: error: unsolved goals
case «done_1: i = arr.size»
arrOld : Array ℤ
ticksOld fake i : ℕ
if_neg : ¬i < arrOld.size
⊢ i = arrOld.size
```

**已驗證的可用配方**（第 02 次起直接沿用）：
```lean
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40
attribute [grind] Array.multiset_swap
…
set_option maxHeartbeats 1000000 in
prove_correct <name> by loom_solve!
```

---

## 4. ★ 提前執行的實驗：第 09 次「實驗 2」

指引 §6.9 說實驗 2「便宜、必做」，且其結果會決定實驗 1 要不要做。**成本極低，因此在勘查階段先做掉。**

### 4.1 結論：**分身計數器作弊通過。指引 §2.4 的 open problem 由「推測的表達力缺口」升格為「已實測確認」。**

> 這一項的成果已升格並固定下來，見 [`Cheats/Unresolved_FakeCounter.lean`](Cheats/Unresolved_FakeCounter.lean)
> （含 `#guard_msgs` 釘住的比較次數 witness）與
> [`Cheats/Unresolved_FakeCounterPadded.lean`](Cheats/Unresolved_FakeCounterPadded.lean)
> （「加一條下界」為什麼救不了）。第 09 次的風險等級因此從「實驗性，可能失敗」改為 **「必要」**。

### 4.2 最小反例（`probe/P5.lean`）— ✅ `prove_correct` 通過

```lean
method FakeCounterLoop
  (mut arr : Array Int) (mut ticks : Nat) return (u : Unit)
  ensures ticks ≤ ticksOld + arrOld.size
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let mut fake := ticks     -- 分身：一行，複製一份計數器
    let mut i := 0
    while i < arr.size
    invariant arr = arrOld
    invariant ticks = ticksOld
    invariant i ≤ arr.size
    done_with i = arr.size
    do
      let _b := arr[i]! ≤ arr[0]!   -- 真的做了比較
      fake := fake + 1              -- 記到分身，不記到 ticks
      i := i + 1
    return

prove_correct FakeCounterLoop by loom_solve
```
```
P5 EXIT: 0        ← 無任何錯誤訊息，完全通過
```

### 4.3 完整反例（`probe/P4.lean`）— ✅ `prove_correct` 通過

一支**貨真價實的插入排序**：做滿所有 O(n²) 次比較、每次都 `fake := fake + 1`、`ticks` 從頭到尾不動，
同時滿足 `Sorted ∧ SameElements ∧ ticks ≤ ticksOld + n²`：

```lean
method FakeCounterSort
  (mut arr : Array Int) (mut ticks : Nat) return (u : Unit)
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  ensures ticks ≤ ticksOld + arrOld.size * arrOld.size
  do
    …
    let mut fake := ticks
    …
        invariant ticks = ticksOld      -- ← 計數器全程不動，還能寫成 invariant
        do
          fake := fake + 1              -- ← 所有計費都流向分身
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
    …

set_option maxHeartbeats 1000000 in
prove_correct FakeCounterSort by loom_solve!
```
```
P4b EXIT: 0       ← 綠燈
```

### 4.4 為什麼 M1／面 1／面 3 都擋不住（指引 §6.9 的分析獲得證實）

- `private mk` 擋的是「**造**一個更小的 `Ticks`」，`let mut fake := ticks` 是「**複製**」——不經過建構子
- 每一次 `cmp` 的 spec 都沒有被違反（它確實對 `fake` 計了費）
- 最終 `ticks ≤ ticksOld + f n` 因為 `ticks = ticksOld` 而**平凡成立**
- `mutable arguments cannot alias` 只檢查**同一次呼叫的兩個 mut 參數**，管不到 `let mut` 區域變數

### 4.5 對第 09 次的直接影響（★ 決定性）

**F1：`method` 的回傳型別被寫死成 `VelvetM`**（`Velvet/Syntax.lean:343`）：
```lean
      def $name $bindersIdents* : VelvetM $retType:term := do $mods* $doSeq*
```

指引 §6.9 的 Q1（「Velvet 的 method 語法能不能在 `SortM` 上用？」）**在勘查階段就有了答案：不能。**
`SortM α β := SortState α → VelvetM (β × SortState α)` 不是 `VelvetM τ`，`method` 無法產生它。

因此第 09 次目前預期落在指引所列的**「部分成功」或「失敗」**區間：
若走 `SortM` 路線，必須手寫 Lean monadic code，**失去 `invariant` / `decreasing` / `done_with` 語法與 `loom_solve` 自動化**。
Q2（「`loom_solve` 能不能穿過一層 opaque monad」）仍為 **UNKNOWN**，要到第 09 次才能實測。

---

## 5. 指引草稿碼 vs 真實 API：差異清單

> 這份清單會被後面每一步引用。

| # | 指引寫的 | 真實 API | 影響的步驟 |
|---|---|---|---|
| D1 | `[total\| …]` | **`[totl\| …]`** | 11 |
| D2 | `requires` | **`require`**（method 內；`requires` 是 F\*/Pulse 拼法） | 全部 |
| D3 | `structure SortImpl` 內直接寫 `[part\| triple …]` | **歧義，編譯失敗**。改用 `open PartialCorrectness PartialCorrectness.DemonicChoice in` | 03–09 |
| D4 | `sort : Array Int → VelvetM (Array Int)` | **`VelvetM (Unit × Array Int)`**——`mut` 併進回傳 tuple | 03–09 |
| D5 | `SortSpec = Sorted ∧ SameElements` | Velvet **反序**合取 `ensures`；要順接則需寫成 `SameElements ∧ Sorted`，否則得寫橋接證明 | 02–09 |
| D6 | `Sorted a := ∀ i j, i ≤ j ∧ j < a.size → …` | 若要與 `ensures` 定義相等，需**逐字**含冗餘的 `0 ≤ i` | 01–09 |
| D7 | 未提及 | **`a[i]!` 需要 `[Inhabited α]`**，且只能由 `variable` 帶入（`leafny_binder` 不收 `[…]`） | 08 |
| D8 | 未提及 | `method` 回傳型別**寫死 `VelvetM`** | **09** |
| D9 | `Cheats/` 反證用 `example : ¬ SortSpec …` | 可行，但 `Sorted`/`SameElements` 對 `Int` 需 `decide`/`simp` 輔助（尚未實測） | 02, 10 |
| D10 | `Velvet/` 與 `SortRubric/` 同層 | Velvet 是外部依賴；`SortRubric/` 放專案根目錄 | 全部 |
| D11 | 未提及 | 需在 `lakefile.lean` 追加 `lean_lib SortRubric` | 全部 |
| D12 | `chain_le` 可用 | 寫死 `Array Int` + `le_trans`；第 08 次需自行改寫成 `ord.trans` 版 | 08 |

---

## 6. 已知環境債（決定 (一)：已定案）

### 6.1 決定

**R4 修訂為**：`bash SortRubric/check_build.sh` 全過。該腳本查三件事：

1. **import 隔離**（條件 2）— `SortRubric` 的閉包不含任何專案根目錄模組
2. `lake build SortRubric` 全綠
3. **完整 `lake build` 的失敗集合與 §6.2 釘住的 baseline 逐字相同**（條件 1）
   —— 多出任何一個新錯誤 = 該步未完成

> 條件 1 的理由：`lake build SortRubric` 只證明我們自己的東西是綠的，
> **不證明我們沒有弄壞別的東西**。每一步結束時仍要跑完整 build 並比對。

### 6.2 ★ 釘住的基準紅燈（逐字）

- **HEAD**：`2ab50076dfa57e7ed6ad3719d9f88cf35289d19b`
- **引入 commit**：`69e292a61d7345c24fdfd307767db94993b6c778`
  （`69e292a 新增安裝與建置說明文件，並撰寫 Velvet 入門教材…`）
- **工作區狀態**：`git status --porcelain` 乾淨（勘查開始時）
- **機械化的簽名檔**：[`baseline_errors.txt`](baseline_errors.txt)

```
error: VelvetLC917.lean:44:16: Failed to prove assertion
error: VelvetLC917.lean:34:12: Failed to prove assertion
error: VelvetLC917.lean:92:33: unsolved goals
error: Lean exited with code 1
error: build failed
- VelvetLC917
```

三個錯誤的完整內容（`lake build` 逐字輸出）：

<details>
<summary><code>VelvetLC917.lean:44:16: Failed to prove assertion</code></summary>

```
error: VelvetLC917.lean:44:16: Failed to prove assertion
case a.left.left.right.right.right.right.right.right.right
aOld : Array Char
require_1 : aOld.size > 0
a : Array Char
i : ℕ
j : ℕ
invariant_1 : a.size = aOld.size
invariant_2 : j < a.size
invariant_3 : i ≤ j + 1
invariant_4 : ∀ k < a.size, isLetter a[k]! = isLetter aOld[k]!
invariant_5 : ∀ k < a.size, isLetter aOld[k]! = false → a[k]! = aOld[k]!
invariant_6 : a.toMultiset = aOld.toMultiset
if_pos : i < j
if_neg : ¬(!isLetter a[i]!) = true
if_neg_1 : ¬(!isLetter a[j]!) = true
⊢ ((a.set! i a[j]!).set! j a[i]!).toMultiset = aOld.toMultiset
```
</details>

<details>
<summary><code>VelvetLC917.lean:34:12: Failed to prove assertion</code></summary>

```
error: VelvetLC917.lean:34:12: Failed to prove assertion
case a.right.right
aOld : Array Char
require_1 : aOld.size > 0
a : Array Char
i : ℕ
j : ℕ
invariant_1 : a.size = aOld.size
invariant_2 : j < a.size
invariant_3 : i ≤ j + 1
invariant_4 : ∀ k < a.size, isLetter a[k]! = isLetter aOld[k]!
invariant_5 : ∀ k < a.size, isLetter aOld[k]! = false → a[k]! = aOld[k]!
invariant_6 : a.toMultiset = aOld.toMultiset
done_1 : i ≥ j
i_1 : Array Char
i_2 : ℕ
j_1 : ℕ
i_3 : { fst := a, snd := { fst := i, snd := j } } = { fst := i_1, snd := { fst := i_2, snd := j_1 } }
⊢ i_1.toList = revOnly aOld.toList
```
</details>

<details>
<summary><code>VelvetLC917.lean:92:33: unsolved goals</code></summary>

```
error: VelvetLC917.lean:92:33: unsolved goals
case «invariant_6: a.toMultiset = aOld.toMultiset»
（context 同上）
⊢ ((a.set! i a[j]!).set! j a[i]!).toMultiset = aOld.toMultiset

case «ensures_1: a.toList = revOnly aOld.toList»
（context 同上）
⊢ i_1.toList = revOnly aOld.toList
```
</details>

**內容**：`ReverseOnlyLetters` 的 multiset 保存 invariant 與最終 `ensures` 證不出來。
與 `SortRubric` 無關；本專案不修它（那是與本任務無關的既有債）。

**`VelvetLC917` 是 leaf module**：專案內**沒有任何檔案** import 它，
它只被 `lakefile.lean` 當成 `@[default_target]` 直接建置（`check_isolation.sh` 每次複驗）。
因此「這筆債與我們無關」不是論證，是**事實**——它不在任何東西的 import 閉包裡，
包括 `SortRubric` 的。

### 6.3 條件 2：import 隔離的機械證明

腳本：[`check_isolation.sh`](check_isolation.sh)。實際輸出：

```
=== [基底] SortRubric 各檔的直接 import ===
  SortRubric/Cheats/Unresolved_FakeCounter.lean
      [toolchain] /home/claw/.elan/toolchains/leanprover--lean4---v4.24.0/bin/../src/lean/Init.lean
      [package  ] .lake/packages/Velvet/Velvet/Std.lean
  SortRubric/Cheats/Unresolved_FakeCounterPadded.lean
      [toolchain] /home/claw/.elan/toolchains/leanprover--lean4---v4.24.0/bin/../src/lean/Init.lean
      [package  ] .lake/packages/Velvet/Velvet/Std.lean

=== [歸納] .lake/packages/ 是否有檔案 import 專案根目錄模組？ ===
  ✓ 無。所有 7 個根目錄模組都沒有被任何套件 import

=== [對照] 專案內誰 import 了 VelvetLC917？ ===
  ✓ 沒有任何檔案 import VelvetLC917（它是 leaf module，只被 lakefile 當 default_target）

✓ 隔離成立：SortRubric 的 import 閉包不含專案根目錄模組。
```

**證明結構**（歸納，避免展開數千個 mathlib 檔案）：

- **基底**：`SortRubric/*.lean` 的直接 import 全部落在 toolchain 或 `.lake/packages/` 之下
  （用 `lean --src-deps` 查，是 Lean 自己的解析，不是我的字串比對）
- **歸納**：`.lake/packages/` 底下沒有任何檔案 import 專案根目錄模組
  （Lake 依賴套件看不到依賴它的套件的模組）
- **⇒** 閉包封閉在 toolchain ∪ packages ∪ `SortRubric/` 之內，`VelvetLC917` 進不來

### 6.4 對外說明

[`README.md`](README.md) 頂部已放告示，說明基準紅燈早於本資料夾存在，避免後來的人誤以為是我們弄的。

## 7. 第 03 次與第 08 次的方案預覽（§7.4 要求先交出）

### 7.1 第 03 次：interface 形狀——**已實測可行，且橋接成本為零**

`probe/P10.lean` 完整通過：

```lean
def Sorted (a : Array Int) : Prop := ∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!
def SameElements (before after : Array Int) : Prop := after.toMultiset = before.toMultiset
def SortSpec (before after : Array Int) : Prop := SameElements before after ∧ Sorted after

open PartialCorrectness PartialCorrectness.DemonicChoice in
structure SortImpl where
  sort : Array Int → VelvetM (Unit × Array Int)
  spec : ∀ a, triple True (sort a) (fun r => SortSpec a r.2)

def bubbleImpl : SortImpl where
  sort := bubble
  spec := bubble_correct        -- ★ 逐字直接用，不需要任何橋接證明
```
```
'bubbleImpl' depends on axioms: [propext, Classical.choice, Quot.sound]
P10 EXIT: 0
```

**三個必須遵守的對齊條件**（否則就要付橋接證明的成本）：
1. `SortSpec` 依 `ensures` 的**反序**合取
2. `Sorted` 逐字照抄 `ensures` 子句（含冗餘 `0 ≤ i`）
3. `SameElements before after := after.toMultiset = before.toMultiset`（方向照 `ensures` 寫）

順帶確認：前條件 `have arr := a; True` **與 `True` 定義相等**；後條件 `match x with | (u, arr) => …` **與 `… x.2` 定義相等**（結構 eta）。指引 §6.3 預期的「薄包裝」在對齊得好的情況下**不需要**。

> **待你確認**：指引 §6.2 把 `SortSpec` 寫成 `Sorted ∧ SameElements`（自然的閱讀順序），
> 但那樣就要付一個小橋接證明。**建議照 Velvet 的反序寫並在 Notes 說明原因**——讓 `spec := bubble_correct` 保持一行，
> 對教材而言「規格與證明零距離」本身就是一個賣點。

**`#print axioms` 已可用**：`bubbleImpl` 乾淨（只有 `propext, Classical.choice, Quot.sound`）；
稍早有 `sorry` 的版本則如實顯示 `sorryAx`。第 10 次的 D3 稽核機制確認可行。

### 7.2 第 08 次：α 的抽象方式——**方案已定，前提全部驗證通過**

```lean
variable {α : Type} [Inhabited α]        -- Inhabited 是必要且安全的（見 §3.Q2）

structure SpecOrder (α : Type) where
  le       : α → α → Prop                -- Prop-valued ⇒ 無 Decidable ⇒ 實作算不出
  total    : ∀ x y, le x y ∨ le y x
  trans    : ∀ x y z, le x y → le y z → le x z
  antisymm : ∀ x y, le x y → le y x → x = y
```

**已驗證的三個前提**：
- `Array.toMultiset` 對抽象 α 可用，無 typeclass（§2.4）→ **不會 BLOCKED**
- `SpecOrder` 這個 `structure` 可以當 `method` 參數（§3.Q1、§3.Q2(b)）
- `ord.le a[i]! a[j]!` 能寫進 `ensures`（`probe/P3.lean` 通過）

**明確禁止清單**（指引 §6.8 的陷阱，已納入第 10 次稽核項）：
`[DecidableRel]`、`[DecidableEq]`、`[FinEnum]`、`[LE α]`、`Classical.dec`／`classical`（後者會讓定義變 `noncomputable`，由 `#print axioms` 抓）。

---

## 8. 交付物與現況

```
SortRubric/
└─ Opt00_Recon.md        ← 本檔
lakefile.lean            ← 末尾追加 lean_lib SortRubric（未動既有行）
```

勘查用的 probe 檔在 scratchpad（不進 repo）：`P1`–`P10.lean`。

| 驗收 | 狀態 |
|---|---|
| `lake build SortRubric` | ✅ 綠（`Build completed successfully`） |
| `lake build`（全域） | ⚠ 紅——**既有失敗** `VelvetLC917`，非本次造成，見 §6 |
| 是否修改 Velvet 本體 | ✅ 否 |
| 是否有 `sorry` 進入 repo | ✅ 否（probe 檔留在 scratchpad） |

---

## 9. UNKNOWN 清單

| # | 問題 | 為什麼還不知道 | 打算怎麼實測 |
|---|---|---|---|
| U1 | `loom_solve` 能不能穿過一層 opaque monad？（§6.9 Q2） | 需要先有 `SortM` | 第 09 次；但 **F1 已使此路線先天受限**——`method` 產不出 `SortM` |
| U2 | `Cheats/` 的 `¬ SortSpec #[8,2,5,3] #[0,0,0,0]` 用什麼戰術？ | 未實測 | 第 02 次；`Multiset` 相等對 `Int` 應可 `decide` 或 `simp [Array.toMultiset]` |
| U3 | 第 08 次抽象化後，`loom_solve` 還能證出 bubble sort 嗎？ | `grind` 對 `Prop`-valued `ord.le` 沒有 `Int` 的算術支援，**風險高**（指引亦標為「高」） | 第 08 次；預期要手動餵 `ord.total`/`ord.trans` 當 `[grind]` 引理 |
| U4 | 第 07 次的 `InstrOrder.cmp` 回傳 `VelvetM (Bool × Ticks)`，能不能在 `method` 的 `do` 區塊裡 `←` 呼叫？ | 未實測 | 第 07 次 |

---

## 10. 下一步（決定已定案）

### 已完成的後續動作

| # | 事項 | 狀態 |
|---|---|---|
| 1 | 決定 (一) 條件 1：釘住基準紅燈 | ✅ §6.2 + `baseline_errors.txt` + `check_build.sh` |
| 2 | 決定 (一) 條件 2：證明 import 隔離 | ✅ §6.3 + `check_isolation.sh` |
| 3 | `README.md` 頂部的基準紅燈告示 | ✅ |
| 4 | 指引勘誤表 | ✅ [`Opt00_GUIDE_ERRATA.md`](Opt00_GUIDE_ERRATA.md) |
| 5 | 發現 1 升格：穩定命名 + 機械 witness + 「下界」否決 | ✅ `Cheats/Unresolved_FakeCounter{,Padded}.lean` |
| 6 | `α` 的 typeclass 預算表 | ✅ [`README.md`](README.md) |
| 7 | `Inhabited` 能否拿掉的實測 | ✅ §3.Q2（結論：代價高，保留） |

### 決定 (二) 的現況：待實測數字

`SortSpec` 採**人類順序**（`Sorted after ∧ SameElements before after`），橋接由 method 端付。
`Sorted` **不含**裝飾用的 `0 ≤ i`（此條不論 (二) 如何決定都成立）。

判準（第 03 次動手前要交出的數字）：

| 量到的結果 | 決定 |
|---|---|
| 橋接 ≤ 3 行，且不依賴脆弱的 `simp` lemma set | 採乾淨版 |
| 橋接 > 3 行，或需要脆弱自動化 | 採對齊版，並在 Notes 與附錄 A 標明這是**工具強加的約束**而非設計選擇 |

> 註：`SortSpec` 在**第 02 次**就要定義，所以橋接成本在第 02 次即可量到，
> 屆時一併交出，不必等到第 03 次動手前。

**目前沒有 BLOCKED 項目。**
