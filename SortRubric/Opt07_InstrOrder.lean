/-
================================================================
  第 07 次優化 — M2 面 1：比較器本身必須誠實
  檔案      : SortRubric/Opt07_InstrOrder.lean
  依賴      : Opt06_MonotonicTicks.lean
----------------------------------------------------------------
  這一步淘汰的作弊:
      「提供一個不計費／亂回答的比較器」
      （`Cheats/Opt07_Cheat_LyingComparator.lean`）

  ⚠ 證據等級：**證明失敗，不是型別錯誤。**
     `cmp` 欄位的型別對誰都一樣，作弊者寫得出那個函式；
     他寫不出來的是 `correct` 與 `charged` 這兩個**欄位的證明**。
     kill 表要誠實標成「證明失敗」。
----------------------------------------------------------------
  ★ 這一步**買不到**的兩件事，都要講清楚:

  (1) 「強迫實作去用 `iord`」——買不到。
      只要 `α = Int`，實作大可收下 `iord` 完全不用，直接 `x ≤ y`。
      **那是面 3 的工作**（第 08 次）。
      見 `Cheats/Unresolved_BypassWithInt.lean`（它**通過**，這是 08 存在的理由）。

  (2) 「呼叫 `cmp` 必定讓**實作的**計數器 +1」——買不到。
      `charged` 講的是「`cmp` 回傳的那個計數器 = 傳進去的 +1」。
      實作可以傳一份**複製品**進去，再把回傳的計數器丟掉。
      見 `Cheats/Unresolved_DiscardCmpTicks.lean`（它也**通過**）。
      這是第 06 次那個發現的延續：**問題是複製，不是建構。**
----------------------------------------------------------------
  仍然活著的洞:
    - 收下 `iord` 但不用，直接 `x ≤ y`   → 第 08 次
    - `ResetToOld` / `FakeCounter` / 丟掉 `cmp` 的計數器 → ★ **無解**（同源）
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt06_MonotonicTicks

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Opt07

open SortRubric.Opt02 SortRubric.Opt06

/-! ## 1. 帶計費的比較器

★ **設計定案（D-3）：`cmp` 是純函式，不是 monadic 的。**

F\* 用 Pulse `fn` 是因為那邊的計數器是**資源**（`MR.pts_to ctr #1.0R i`）；
Lean 的 `Ticks` 是**值**，所以 monad 在這裡沒有承載任何東西。

兩個具體的好處：

| | 純函式 | monadic |
|---|---|---|
| 迴圈本體 | **一行 `let r := iord.cmp a b ticks`，形狀不變** | 每次比較一個 bind |
| 規格形式 | **等式／iff** → grind 可直接當 rewrite | `triple` → 要穿過 WP |

第二列在第 08 次特別關鍵：那一步的風險正是 grind 失去對序的推理能力，
而等式是唯一 grind 能直接吃的形式。

（本檔實測：`correct` / `charged` 掛 `local grind` 之後，排序的證明
**第一次就過，17 秒**。） -/

structure InstrOrder where
  /-- 比較兩個元素，並把計數器往前推。**吃一個 `Ticks`** ——
  堵住「不帶計數器就比較」。 -/
  cmp     : Int → Int → Ticks → Bool × Ticks
  /-- 回答的是真的序。堵住「呼叫了但不用結果，自己瞎猜」。 -/
  correct : ∀ x y t, ((cmp x y t).1 = true ↔ x ≤ y)
  /-- 呼叫必定計費。堵住「呼叫了但不計費」——
  **沒有『不 tick 的版本』可選**，因為 `cmp` 只有這一個欄位。 -/
  charged : ∀ x y t, (cmp x y t).2.val = t.val + 1

namespace InstrOrder

/-- `correct` 的 `false` 側。grind 在 `if` 的 else 分支拿到的是
`(cmp x y t).1 = false`，需要這條才接得回 `¬ (x ≤ y)`。

沒有它，序的 invariant 證不出來——這是第 07 次唯一一條需要手寫的引理。 -/
theorem correct_false (o : InstrOrder) (x y : Int) (t : Ticks) :
    (o.cmp x y t).1 = false ↔ ¬ (x ≤ y) := by
  rw [← o.correct x y t]
  cases h : (o.cmp x y t).1 <;> simp

end InstrOrder

/-! ## 2. 一個誠實的實例

面 1 的三條全部證得出來——這一步不是不可能滿足的，它只是**要求誠實**。
（R12 的正向控制組：沒有這個實例，「作弊者證不出 `correct`／`charged`」
就可能只是「這兩條根本沒人證得出來」。） -/

def honestInt : InstrOrder where
  cmp x y t := (decide (x ≤ y), t.bump)
  correct := by intro x y t; simp
  charged := by intro x y t; exact Ticks.val_bump t

/-- info: 'SortRubric.Opt07.honestInt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms honestInt

/-! ## 3. 遷移後的插入排序

與第 06 次逐字比較，只有兩處不同：多一個 `iord` 參數，
迴圈本體的 `if` 條件換成 `cmp` 的回傳值。

```lean
-- 第 06 次
ticks := ticks.bump
if arr[mind]! < arr[mind - 1]! then …

-- 第 07 次
let r := iord.cmp arr[mind]! arr[mind - 1]! ticks
ticks := r.2
if r.1 then …
```

★ 計費從**手寫**變成**比較器的副產品**：本檔沒有任何一行 `ticks.bump`。
這就是面 1 買到的東西——計費不再是實作的自律。

（`cmp x y` 為真代表 `x ≤ y`，所以相等時也會交換。對有序性與 multiset
都無害，只是比第 06 次多做幾次無謂的搬移。） -/

attribute [grind] Array.multiset_swap
attribute [local grind] Ticks.val_bump
  InstrOrder.correct InstrOrder.charged InstrOrder.correct_false

method insertionSortInstr
  (iord : InstrOrder) (mut arr : Array Int) (mut ticks : Ticks) return (u : Unit)
  ensures arr.size = arrOld.size
  ensures Sorted arr
  ensures SameElements arrOld arr
  ensures ticks.val ≤ ticksOld.val + arrOld.size * arrOld.size
  do
    let arr₀ := arr
    let arr_size := arr.size
    let t_in := ticks.val
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ arr.size
      invariant arr.size = arr_size
      invariant 1 ≤ n ∧ n ≤ arr.size
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arr₀.toMultiset
      invariant ticks.val ≤ t_in + n * n
      do
        let t0 := ticks.val
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
        invariant arr.toMultiset = arr₀.toMultiset
        invariant ticks.val = t0 + (n - mind)
        invariant t0 ≤ t_in + n * n
        do
          let r := iord.cmp arr[mind]! arr[mind - 1]! ticks
          ticks := r.2
          if r.1 then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 4000000 in
prove_correct insertionSortInstr by
  loom_solve!

/-! ## 4. 遷移後的 rubric（R13）

`sort` 多收一個 `InstrOrder`，`spec` 多量化一個 `iord`。

★ **注意 `spec` 對 `iord` 是全稱量化的**：實作必須對**任何**誠實的比較器
都給出排好的結果與界限，不能只對某一個特定的比較器有效。 -/

open PartialCorrectness PartialCorrectness.DemonicChoice in
structure ArraySort (f : Nat → Nat) where
  sort : InstrOrder → Array Int → Ticks → VelvetM (Unit × Array Int × Ticks)
  spec : ∀ iord a t, triple True (sort iord a t)
                      (fun r => SortSpec a r.2.1 ∧ r.2.2.val ≤ t.val + f a.size)

/-- 橋接仍然是那一行 `triple_cons`，第五次只換投影。 -/
def insertionSortInstrImpl : ArraySort (fun n => n * n) where
  sort := insertionSortInstr
  spec := fun iord a t =>
    triple_cons _ (fun _ => trivial) (fun _ h => ⟨⟨h.2.2.1, h.2.1⟩, h.1⟩)
      (insertionSortInstr_correct iord a t)

/-- info: 'SortRubric.Opt07.insertionSortInstrImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insertionSortInstrImpl

/-! ## 5. R13：組合性再遷移一次

證明本體**又是一字未改**——只有多帶一個 `iord`。
第 05.5 次那條 `SameElements.size_eq` 到現在完全沒動過。 -/

open PartialCorrectness PartialCorrectness.DemonicChoice in
theorem ArraySort.compose_two (f : Nat → Nat) (S : ArraySort f)
    (iord : InstrOrder) (a : Array Int) (t : Ticks) :
    triple True (S.sort iord a t >>= fun r => S.sort iord r.2.1 r.2.2)
      (fun r => SortSpec a r.2.1 ∧ r.2.2.val ≤ t.val + f a.size + f a.size) := by
  apply triple_bind (cut := fun y => SortSpec a y.2.1 ∧ y.2.2.val ≤ t.val + f a.size)
  · exact S.spec iord a t
  · intro y hcut
    obtain ⟨⟨hsy, hmy⟩, hty⟩ := hcut
    have hsz : a.size = y.2.1.size := Opt05b.SameElements.size_eq hmy
    refine (triple_cons _ (fun _ => trivial) ?_ (S.spec iord y.2.1 y.2.2)) trivial
    rintro r ⟨⟨hs, hm⟩, ht⟩
    refine ⟨⟨hs, hmy.trans hm⟩, ?_⟩
    rw [← hsz] at ht
    omega

/-! ## 6. 這一步買到什麼、買不到什麼

### 買到

| 子句 | 堵住的作弊 | 證據等級 |
|---|---|---|
| `cmp` 吃一個 `Ticks` | 不帶計數器就比較 | 型別 |
| `charged` | 呼叫了但不計費 | 證明失敗 |
| `correct` | 呼叫了但不用結果，自己瞎猜 | 證明失敗 |

另外一件實質的事：**計費從「實作的自律」變成「比較器的副產品」**。
第 06 次的排序自己寫 `ticks.bump`；第 07 次的排序一行都沒有。

### 買不到（兩件，都有活著的作弊當證據）

**(1) 強迫實作去用 `iord`。** 只要 `α = Int`，實作大可收下不用。
→ `Cheats/Unresolved_BypassWithInt.lean`（通過）。**那是面 3 的工作。**

**(2) 「呼叫 `cmp` 必定讓實作的計數器 +1」。**
`charged` 說的是「`cmp` **回傳**的計數器 = **傳進去**的 +1」。
實作可以傳複製品進去、把回傳值丟掉：

```lean
let fake := ticks                     -- 複製
let r := iord.cmp x y fake            -- 誠實的比較器，誠實地計費
-- 用 r.1，丟掉 r.2；ticks 一動不動
```

→ `Cheats/Unresolved_DiscardCmpTicks.lean`（通過）。

這是第 06 次那個發現的第三種穿法。三支作弊、同一個根因：

| 作弊 | 做的事 | 死於 |
|---|---|---|
| `ResetToOld` | 複製 → 計費 → 放回複製品 | 無 |
| `FakeCounter` | 複製 → 對複製品計費 | 無 |
| `DiscardCmpTicks` | 複製 → 餵給 `cmp` → 丟掉回傳 | 無 |

**複製一個值不需要任何建構子，也不需要任何權限。**

### 與 F\* 的形狀差異（誠實記錄）

F\* 的 `instrumented_total_order a ord ctr` 把**計數器烤進比較器的型別**；
我們只是讓 `cmp` **收一個 `Ticks` 參數**。

對照表那一列要標「**弱：`ctr` 沒烤進型別**」。
上面的 (2) 正是這個差異的可觀察後果——F\* 那邊 `ctr` 是型別的一部分，
比較器只能對**那一個**計數器計費；我們這邊 `cmp` 對**你遞給它的任何一個**計費。
-/

end SortRubric.Opt07
