/-
================================================================
  作弊：刪掉元素 — **在第 02 次優化被淘汰**
  檔案      : SortRubric/Cheats/Opt02_Cheat_DropElements.lean
  依賴      : Opt02_SameElements.lean
----------------------------------------------------------------
  第 01 次  : ✅ 通過（空陣列沒有任何一對索引，`Sorted` 平凡成立）
  第 02 次  : ❌ 死於 `ensures SameElements arrOld arr`
----------------------------------------------------------------
  為什麼取極端版（全刪）而不是指引 §6.2 的「刪一個」:
    `Sorted` 對空陣列**平凡成立**，讓這支作弊的重點乾淨地落在
    「規格沒說輸出要跟輸入有關」上，不必先證一個排序的正確性。
    指引舉的 `#[8,2,5,3] ↦ #[2,3,5]`（只刪一個）同樣被殺，見 §2.5。
----------------------------------------------------------------
  ⚠ 本檔含一個被 `#guard_msgs` 釘住的失敗證明，`DropAll_correct` 帶 `sorryAx`。
    R5 的受控例外，三重圍堵說明見 Opt02_Cheat_AllZeros.lean 檔頭。
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt02_SameElements

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.DropElements

open SortRubric.Opt02

/-! ## 1. 作弊本體 -/

method DropAll (mut arr : Array Int) return (u : Unit)
  ensures Sorted arr
  ensures SameElements arrOld arr
  do
    arr := #[]
    return

/-! ## 2. 第 02 次為什麼殺得掉它

### 2.1 失敗被釘進 build -/

/--
error: unsolved goals
case «ensures_1: SameElements arrOld arr»
arrOld : Array ℤ
⊢ SameElements arrOld #[]
-/
#guard_msgs in
prove_correct DropAll by
  loom_solve

/-! 目標 `SameElements arrOld #[]` 對任何非空的 `arrOld` 都是**假的**。 -/

/-! ### 2.2 程式照樣跑得動 -/

/-- info: DivM.res ((), #[]) -/
#guard_msgs in
#eval (DropAll #[8,2,5,3]).run

/-! ### 2.3 受控的 `sorryAx`，明文釘住 -/

/-- info: 'SortRubric.Cheats.DropElements.DropAll_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DropAll_correct

/-! ### 2.4 機械可檢的反證 -/

theorem dropAll_violates_sortSpec : ¬ SortSpec #[8,2,5,3] #[] := by
  rintro ⟨-, h⟩
  revert h
  unfold SameElements Array.toMultiset
  decide

/-! ### 2.5 只刪一個也一樣被殺（指引 §6.2 舉的例子） -/

theorem drop_one_violates_sortSpec : ¬ SortSpec #[8,2,5,3] #[2,3,5] := by
  rintro ⟨-, h⟩
  revert h
  unfold SameElements Array.toMultiset
  decide

end SortRubric.Cheats.DropElements
