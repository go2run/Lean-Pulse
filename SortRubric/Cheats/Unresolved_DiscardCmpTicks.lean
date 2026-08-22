/-
================================================================
  作弊 — 呼叫誠實的比較器，但餵它一份**複製品**，丟掉回傳的計數器
  檔案      : SortRubric/Cheats/Unresolved_DiscardCmpTicks.lean
  死於      : ★ **沒有任何一步淘汰得了它**
  證據等級  : 完整插入排序 + `prove_correct` 綠燈 + 乾淨的 `#print axioms`
----------------------------------------------------------------
  ★ 這一支界定了第 07 次面 1 的**上界**。

     `charged : ∀ x y t, (cmp x y t).2.val = t.val + 1`
     講的是「`cmp` **回傳**的計數器 = **傳進去**的 +1」。

     它**沒有**講「實作的計數器 +1」。實作可以：

         let fake := ticks                    -- 複製
         let r := iord.cmp x y fake           -- 誠實的比較器，誠實地計費
         if r.1 then …                        -- 用 r.1
         -- 丟掉 r.2；ticks 一動不動

     比較器從頭到尾都是誠實的。**不誠實的是「哪一個計數器被計」。**
----------------------------------------------------------------
  它與第 08 次的關係:
      `Unresolved_BypassWithInt` 根本不呼叫 `cmp` ⇒ 第 08 次的抽象 α 殺得掉。
      **這一支真的呼叫 `cmp`，而且用了它的答案** ⇒ 第 08 次殺不掉。

      換句話說：第 08 次強迫實作「經過比較器」，
      但強迫不了它「把帳算在自己頭上」。
----------------------------------------------------------------
  與另外兩支同源:
      ResetToOld       複製 → 對本尊計費   → 放回複製品
      FakeCounter      複製 → 對複製品計費
      DiscardCmpTicks  複製 → 餵給 `cmp`   → 丟掉回傳   ← 本檔

      三支都只做一件事：**複製一個 `Ticks` 值**。
      要擋住的是**線性性**，不是模組抽象、也不是比較器的誠實性。
----------------------------------------------------------------
  狀態: [ ] 未解 —— 與 ResetToOld / FakeCounter 同一個根因
================================================================
-/
import SortRubric.Opt07_InstrOrder

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Cheats.DiscardCmpTicks

open SortRubric.Opt02 SortRubric.Opt06 SortRubric.Opt07

attribute [grind] Array.multiset_swap
attribute [local grind] InstrOrder.correct InstrOrder.correct_false

/-! ## 1. 一支真的插入排序，真的經過比較器，帳單丟進垃圾桶

和 `Opt07_InstrOrder.lean` 的 `insertionSortInstr` 逐字比較，只差兩行：

```lean
-- 誠實版
let r := iord.cmp arr[mind]! arr[mind - 1]! ticks
ticks := r.2                                        -- ← 收下帳單

-- 本檔
let fake := ticks                                   -- ← 複製
let r := iord.cmp arr[mind]! arr[mind - 1]! fake
                                                    -- ← 沒有 ticks := r.2
```

比較的答案照用（`r.1`），所以排序是真的。
計數器沒有收下任何一張帳單，所以 `ticks = ticksOld`。 -/

method discardSort
  (iord : InstrOrder) (mut arr : Array Int) (mut ticks : Ticks) return (u : Unit)
  ensures Sorted arr
  ensures SameElements arrOld arr
  ensures ticks = ticksOld
  do
    let arr₀ := arr
    let arr_size := arr.size
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
      do
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
        invariant arr.toMultiset = arr₀.toMultiset
        do
          let fake := ticks                                     -- ★ 複製
          let r := iord.cmp arr[mind]! arr[mind - 1]! fake      -- ★ 誠實地計費 fake
          if r.1 then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1                                       -- ★ 沒有 ticks := r.2
        n := n + 1
      return

set_option maxHeartbeats 4000000 in
prove_correct discardSort by
  loom_solve!

/-- info: 'SortRubric.Cheats.DiscardCmpTicks.discardSort_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms discardSort_correct

/-! ## 2. 它住得進 `ArraySort (fun _ => 0)`

**第 07 次的 rubric 承認一支「零次比較的比較排序」，
而且這一支真的做滿了 n(n−1)/2 次比較，每一次都經過誠實的比較器。** -/

def zeroCompareSort : Opt07.ArraySort (fun _ => 0) where
  sort := discardSort
  spec := fun iord a t =>
    triple_cons _ (fun _ => trivial)
      (fun _ h => ⟨⟨h.2.2, h.2.1⟩, by simp [h.1]⟩)
      (discardSort_correct iord a t)

/-- info: 'SortRubric.Cheats.DiscardCmpTicks.zeroCompareSort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeroCompareSort

/-! ## 3. 與 F\* 的差異就落在這裡

F\* 的 `instrumented_total_order a ord ctr` 把**計數器烤進比較器的型別**——
比較器只能對 `ctr` **那一個**計數器計費。

我們的 `cmp : Int → Int → Ticks → Bool × Ticks` 對**你遞給它的任何一個**計費。
`Ticks` 是值，值可以複製，所以「遞給它哪一個」是實作說了算。

要把 `ctr` 烤進型別，需要的是資源語意（`MR.pts_to ctr #1.0R i`），
而 `VelvetM = NonDetT DivM` 上沒有地方掛得住它。
詳見第 09 次的 `Opt09_Notes.md`。
-/

end SortRubric.Cheats.DiscardCmpTicks
