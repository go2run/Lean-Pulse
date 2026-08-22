/-
================================================================
  作弊 — 收下 `iord`，完全不用，直接 `x < y`
  檔案      : SortRubric/Cheats/Unresolved_BypassWithInt.lean
  死於      : 預定第 08 次（面 3：抽象 α）—— **尚未驗證**
  證據等級  : 完整插入排序 + `prove_correct` 綠燈
----------------------------------------------------------------
  ⚠ 檔名用 `Unresolved_` 前綴，不是 `Opt08_Cheat_`。

     指引把它寫成 `Opt08_Cheat_BypassWithInt`，但依 `Cheats/` 命名規則
     第 1 條，`OptNN_Cheat_` 是一句**已驗證**的宣稱，而第 08 次還沒做。
     第 08 次真的殺掉它的那一刻，當場改名（規則第 2 條）。

     第 06 次剛好示範了為什麼這條規則重要：指引預期
     `ResetToOld` 死於第 06 次，實測沒死。
----------------------------------------------------------------
  ★ 這一支是第 08 次存在的理由。

     它**必須通過**。如果它在第 07 次就死了，那代表面 1 做了面 3 的工作，
     兩步的分工就講錯了（指引 v1 附錄 A 曾經把它列成 07 淘汰，
     v2 §5.2.4 已修正）。

     面 1 買到的是「比較器值得信任」，買不到「強迫實作去用它」。
     只要 `α = Int`，`x < y` 是語言原生能力，收不回來。
----------------------------------------------------------------
  狀態: [ ] 未解（等第 08 次）
================================================================
-/
import SortRubric.Opt07_InstrOrder

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Cheats.BypassWithInt

open SortRubric.Opt02 SortRubric.Opt06 SortRubric.Opt07

attribute [grind] Array.multiset_swap

/-! ## 1. 一支真的插入排序，收下 `iord` 之後完全不看它

`iord` 在整個 method body 裡出現 **0 次**。
排序是對的、元素是對的、界限是對的——**因為它一次都沒計費**。

後條件寫 `ticks = ticksOld`，讓「它報了什麼」是一條全稱定理。 -/

method bypassSort
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
          if arr[mind]! < arr[mind - 1]! then    -- ★ 語言原生的序，沒經過 iord
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 2000000 in
prove_correct bypassSort by
  loom_solve!

/-- info: 'SortRubric.Cheats.BypassWithInt.bypassSort_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bypassSort_correct

/-! ## 2. 它住得進第 07 次的 rubric，而且是 `f _ = 0` 那一格 -/

def zeroCompareSort : Opt07.ArraySort (fun _ => 0) where
  sort := bypassSort
  spec := fun iord a t =>
    triple_cons _ (fun _ => trivial)
      (fun _ h => ⟨⟨h.2.2, h.2.1⟩, by simp [h.1]⟩)
      (bypassSort_correct iord a t)

/-- info: 'SortRubric.Cheats.BypassWithInt.zeroCompareSort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeroCompareSort

/-! ## 3. 第 08 次要怎麼殺它

把 `Int` 換成抽象的 `(α : Type)` + `SpecOrder α`：

- `ord.le x y : Prop`，**沒有 `Decidable` 實例**，`if` 用不了
- `SpecOrder` 結構裡就沒有可計算的欄位，**取不到**一個 `Decidable`
- ⇒ `if arr[mind]! < arr[mind - 1]! then` 連型別檢查都過不了

那會是本專案第二列「型別錯誤」的 kill（第一列是第 06 次的 `ForgeZero`）。

⚠ 第 08 次要小心的反面：只要不小心寫上
`[LE α] [DecidableRel (· ≤ ·)]` / `[DecidableEq α]` / `[FinEnum α]`
其中任何一個，這一支就**當場復活，而且不會有任何錯誤訊息**。
-/

end SortRubric.Cheats.BypassWithInt
