# 失敗路徑注入 `sorry`，而不是報錯

**給 verse-lab/velvet 的回報**
驗證環境：`leanprover/lean4:v4.24.0`、Velvet@master、Loom@master

---

## 摘要

> `prove_correct UseDoubler by loom_solve` 綠燈，**一句訊息都沒有**。
> `#eval` 顯示它算出 4，而 spec 說是 6。

重點不是「錯誤訊息不好」，是**根本沒有訊息**。
任何監看錯誤的工具都攔不到；CI 攔不到；`#guard_msgs` 也攔不到（它不產生訊息，包不住）。
**唯一的信號是 `#print axioms`，而那是一個要主動去跑的指令。**

我們在兩條不同的路徑上撞到同一個模式：

| | 路徑 | 注入點 |
|---|---|---|
| **Instance 1** | `prove_correct` 失敗 | 註冊一個帶 `sorryAx` 的 **`@[loomSpec]`** lemma，之後被 `loom_solve` 取用 |
| **Instance 2** | 呼叫 `mut` 參數的 method | 呼叫端的證明目標直接變成 `⊢ sorry = yOld + 1` |

兩者都是：**失敗路徑注入 `sorry`，而不是報錯。**

**因此這份報告不是兩張票。** 建議的問題是：
*Velvet/Loom 裡還有第三個這樣的地方嗎？*
把「失敗時注入 sorry」當成一個要系統性排查的模式，比修這兩個點有用。

---

## Instance 1：未證的 spec 會**靜默**污染下游驗證

**最小重現**：`SortRubric/Cheats/Upstream_ContaminationA.lean` + `Upstream_ContaminationB.lean`

### 觸發路徑是**被鼓勵的工作流程**，不是壞習慣

```
1. 使用者寫 method A，prove_correct 失敗，先擱著往下做   ← 「先寫 spec、proof 之後再補」
2. A_correct 帶著 sorryAx 進了 loom_solve 的取用集合
3. 使用者寫 method B，B 呼叫 A
4. loom_solve 用那條【未證的】A_correct 補完了 B 的證明
5. B 綠燈，而且【不產生任何訊息】
```

### 檔 1（A）——`ensures` 是假的

```lean
method Doubler (mut x : Nat) return (u : Unit)
  ensures x = xOld * 2
  do
    x := x + 1        -- xOld = 3 時 body 給 4，spec 要 6
    return

prove_correct Doubler by loom_solve
-- error: unsolved goals ⊢ xOld + 1 = xOld * 2
-- 'Doubler_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### 檔 2（B）——呼叫 A，宣稱同樣假的性質

```lean
method UseDoubler (mut y : Nat) return (u : Unit)
  ensures y = yOld * 2
  do
    let ⟨_, y'⟩ ← Doubler y
    y := y'
    return

prove_correct UseDoubler by loom_solve
-- ★ 完全沒有錯誤訊息。綠燈。
-- 'UseDoubler_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

#eval (UseDoubler 3).run   -- DivM.res ((), 4)，而 spec 說 3 * 2 = 6
```

### ★ 控制組：連「真話」都會被污染

**檔 A／B 用的是一個假的 spec，那容易讓人以為「只要別寫錯 spec 就沒事」。不是。**

`SortRubric/Cheats/Upstream_ContaminationControl.lean`：

```lean
-- A' 的 spec 是【真的】：迴圈確實跑兩次、每次加一
method AddTwo (mut x : Nat) return (u : Unit)
  ensures x = xOld + 2
  do
    let mut i := 0
    while i < 2
    invariant i ≤ 2          -- 只是少了 `invariant x = xOld + i`
    done_with i = 2
    do
      x := x + 1
      i := i + 1
    return

prove_correct AddTwo by loom_solve
-- error: unsolved goals ⊢ x_1 = xOld + 2
#eval (AddTwo 5).run          -- DivM.res ((), 7) ← spec 是對的

-- B' 宣稱的也是【真的】
method AddFour (mut y : Nat) return (u : Unit)
  ensures y = yOld + 4
  do
    let ⟨_, y1⟩ ← AddTwo y
    y := y1
    let ⟨_, y2⟩ ← AddTwo y
    y := y2
    return

prove_correct AddFour by loom_solve   -- ★ 綠燈，零訊息
#eval (AddFour 5).run                 -- DivM.res ((), 9) ← spec 也是對的
-- 'AddFour_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

| | 檔 A／B（假 spec） | **控制組（真 spec）** |
|---|---|---|
| A 的 spec | 假的 | **真的** |
| B 的 spec | 假的 | **真的** |
| A 的證明 | 失敗 | 失敗（只是少一條 invariant） |
| B 的證明 | 綠燈、零訊息 | **綠燈、零訊息** |
| B 帶 `sorryAx` | ✅ | ✅ |

⇒ **這個 bug 與 spec 的真假完全無關。**
`loom_solve` 會取用任何掛著 `@[loomSpec]` 的定理，**不管它證明了沒有**。

**沒有人寫錯任何東西**——使用者只是還沒把一個證明做完，
而工具靜默地宣告了第二個證明成立。

### 根因

`Velvet/Syntax.lean:411` 產生的是

```lean
@[loomSpec] lemma <name>_correct … := by <proof>
```

證明失敗時 Lean 仍把宣告加進環境（依賴 `sorryAx`），**而 `@[loomSpec]` 屬性照樣生效**，
於是它進入 `loom_solve` 的取用集合。B 的 `_correct` 也帶 `sorryAx` 與 `@[loomSpec]`，**繼續污染 C**。

### 建議

擇一或並行：
1. `prove_correct` 失敗時**不要**加上 `@[loomSpec]`（或根本不註冊該宣告）
2. `loom_solve` 取用 `loomSpec` 集合時過濾掉依賴 `sorryAx` 的條目
3. 至少在使用被污染的 spec 時發出 warning

---

## Instance 2：`mut` 參數的 method 幾乎無法被呼叫

被呼叫端（**本身完全證明成功，與 Instance 1 無關**）：

```lean
method Incr (mut x : Nat) return (u : Unit)
  ensures x = xOld + 1
  do
    x := x + 1
    return
prove_correct Incr by loom_solve     -- ✅ 綠燈，axioms 乾淨
```

| # | 呼叫寫法 | 結果 |
|---|---|---|
| 1 | `Incr y`（bare，`Syntax.lean:219-236` 的 macro 宣稱支援） | ❌ 注入 `sorry` |
| 2 | `let r ← Incr y`（`velvet_documentation.md:552` 記載的寫法） | ❌ 注入 `sorry` |
| 3 | `let ⟨_, y'⟩ ← Incr y` 然後 `y := y'` | ✅ 可行 |

寫法 1 的逐字錯誤：

```
error: Unknown identifier `x`
error: unsolved goals
case «ensures_1: z = zOld + 1»
zOld : ℕ
x : Unit × ℕ
ensures_1 : x.2 = zOld + 1        ← spec 有正確傳進來
⊢ sorry = zOld + 1                ← ★ body 的展開注入了 sorry
```

注意 `ensures_1` **是對的**——spec 傳遞沒問題。壞掉的是 body 的展開。
錯誤位置指向**被呼叫端**的 `(mut x : Nat)` binder，
推測是 macro 展開時 mut 參數名在呼叫端的 context 裡解析不到。

### 為什麼這個 bug 能活到現在

**`Examples/` 與 `Demo/` 裡沒有任何一個呼叫 `mut` 參數 method 的例子。**
一個 macro 宣稱支援、文件記載、但**沒有任何測試覆蓋**的語法路徑。

### 影響

任何要做模組化／遞迴分解的程式都會撞到。
（我們的專案要示範「遞迴呼叫的成本界限疊不起來」，正好需要它。）

---

## 附帶回報 A：`method` 把回傳型別寫死成 `VelvetM`

**位置**：`Velvet/Syntax.lean:343`

```lean
      def $name $bindersIdents* : VelvetM $retType:term := do $mods* $doSeq*
```

**後果**：任何想把 `method` 用在 `VelvetM` 以外的 monad（例如把計數器藏進 state 的
`SortM α β := SortState α → VelvetM (β × SortState α)`）都不可能。
只能退回手寫 monadic code，**失去 `invariant` / `decreasing` / `done_with` 語法與 `loom_solve` 自動化**。

**這是本專案第 09 次受限的直接成因。**

**問題**：`method` 有沒有可能參數化它的目標 monad（例如接受一個 `MonadLift` 或
`MAlgOrdered` 實例），還是這是刻意的設計邊界？

---

## 附帶回報 B：`VelvetM` 沒有所有權，計數器可被複製

**最小重現**：`SortRubric/Cheats/Unresolved_FakeCounter.lean`

一支**貨真價實的插入排序**，做滿 O(n²) 次比較，全部記到區域變數 `fake`，
真計數器 `ticks` 從頭到尾不動，通過：

```
Sorted ∧ SameElements ∧ ticks ≤ ticksOld + n²
```

作弊的全部內容是一行 `let mut fake := ticks`。

`#guard_msgs` 釘住的行為（`(observed, arr, ticks)`）：

| 輸入 | 輸出 |
|---|---|
| n=8 逆序, ticksOld=0 | `(28, sorted, 0)` |
| n=8 逆序, ticksOld=**100** | `(128, sorted, **100**)` |

**對照 F\***：`MR.pts_to ctr #1.0R i` 是**資源**不是值，`1.0R` 分不出第二份 `1.0R`。
Velvet 的 `VelvetM = NonDetT DivM` 是純值上的不確定性 + 發散，沒有 heap／分離邏輯／所有權。
`Velvet/Syntax.lean:215` 的 `mutable arguments cannot alias` 只管**同一次呼叫的兩個 mut 參數**，
管不到 `let mut` 區域變數。

**附帶結果**：`SortRubric/Cheats/Unresolved_FakeCounterPadded.lean` 顯示，
試圖用**下界**（`ensures ticks ≥ ticksOld + (n−1)`）補救會讓事情**更糟**——
湊數即可通過，而計數器從「沉默地報 0」變成「報一個 Θ(n) 的假數字」，
也就是認證了一個資訊論上不存在的比較排序複雜度等級。

**問題**：Loom/Velvet 有沒有規劃引入分離邏輯或線性資源？
若沒有，有沒有推薦的替代慣用法來表達「這個值只有一份」？

---

## 附帶回報 C（可用性 bug）：`[part|` 記號歧義，錯誤訊息無法自我診斷

**重現**：在 `structure` 欄位裡使用 `[part| triple … ]`

```lean
open PartialCorrectness PartialCorrectness.DemonicChoice in  -- 不加這行就會出錯
structure SortImpl where
  sort : Array Int → VelvetM (Unit × Array Int)
  spec : ∀ a, [part| triple True (sort a) (fun r => SortSpec a r.2)]
```

**錯誤訊息**：

```
error: Ambiguous term
  [part|triple True (sort a) (fun r => SortSpec a r.2)]
Possible interpretations:
  {True}sort a{r,SortSpec a r.2} : Prop

  {True}sort a{r,SortSpec a r.2} : Prop
```

**問題所在**：兩個 interpretation **印出來一模一樣**，使用者無從判斷差在哪。

**根因**：有兩個同名記號同時在 scope 內——

- `Loom/MonadAlgebras/WP/Liberal.lean:143`：`notation "[part|" t "]" => open ExceptionAsSuccess in t`
- `Velvet/VelvetTheory.lean:8`：`notation "[part|" t "]" => open PartialCorrectness PartialCorrectness.DemonicChoice in t`

**建議**：兩者擇一改名（例如 Liberal 的改成 `[part_exn|`），
或讓歧義訊息把來源 `notation` 的定義位置印出來。

**繞法**（已驗證可行）：不要用 `[part|`，改成顯式 `open PartialCorrectness PartialCorrectness.DemonicChoice in`。

---

## 附帶回報 D：待補 —— 第 09 次 spike 的 Q2 答案

**Q2**：`loom_solve`（或等價自動化）能不能穿過一層 opaque monad？

⏳ 第 09 次做完後填入。
