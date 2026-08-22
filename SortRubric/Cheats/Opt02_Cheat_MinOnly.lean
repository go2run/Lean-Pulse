/-
================================================================
  作弊：只留最小值 — **在第 02 次優化被淘汰**
  檔案      : SortRubric/Cheats/Opt02_Cheat_MinOnly.lean
  依賴      : Opt02_SameElements.lean
----------------------------------------------------------------
  第 01 次  : ✅ 通過（長度 1 的陣列必定有序）
  第 02 次  : ❌ 死於 `ensures SameElements arrOld arr`

  這一支比前兩支「更像在做事」——它真的掃過整個陣列找最小值。
  第 01 次的規格擋不住它，正因為那份規格**從未提到輸入**。
----------------------------------------------------------------
  ⚠ 本檔含一個被 `#guard_msgs` 釘住的失敗證明，`MinOnly_correct` 帶 `sorryAx`。
    R5 的受控例外，三重圍堵說明見 Opt02_Cheat_AllZeros.lean 檔頭。
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt02_SameElements

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.MinOnly

open SortRubric.Opt02

/-! ## 1. 作弊本體：真的找最小值，然後只留它 -/

method MinOnly (mut arr : Array Int) return (u : Unit)
  ensures Sorted arr
  ensures SameElements arrOld arr
  do
    let mut m := arr[0]!
    let mut i := 0
    while i < arr.size
    invariant i ≤ arr.size
    done_with i = arr.size
    do
      if arr[i]! < m then
        m := arr[i]!
      i := i + 1
    arr := #[m]
    return

/-! ## 2. 第 02 次為什麼殺得掉它

### 2.1 失敗被釘進 build

★ **這一則錯誤訊息是 invariant 三分類最好的實例。**

底下的 context 裡，Structural 那一類齊全（`invariant_1 : i ≤ arrOld.size`），
迴圈也確實跑完了（`done_1 : i = arrOld.size`），`m_1` 真的是最小值。
**唯獨沒有任何一條談到元素去哪了**——因為程式根本沒保留它們。

錯誤訊息自己指出了缺的是三分類裡的哪一類：**Preservation**。 -/

/--
error: unsolved goals
case «ensures_1: SameElements arrOld arr»
arrOld : Array ℤ
i : ℕ
m : ℤ
invariant_1 : i ≤ arrOld.size
done_1 : i = arrOld.size
i_1 : ℕ
m_1 : ℤ
i_2 : { fst := i, snd := m } = { fst := i_1, snd := m_1 }
⊢ SameElements arrOld #[m_1]
-/
#guard_msgs in
prove_correct MinOnly by
  loom_solve

/-! `m_1` 確實是最小值，可是**一個元素換不回四個**。 -/

/-! ### 2.2 程式照樣跑得動 -/

/-- info: DivM.res ((), #[2]) -/
#guard_msgs in
#eval (MinOnly #[8,2,5,3]).run

/-! ### 2.3 受控的 `sorryAx`，明文釘住 -/

/-- info: 'SortRubric.Cheats.MinOnly.MinOnly_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MinOnly_correct

/-! ### 2.4 機械可檢的反證 -/

theorem minOnly_violates_sortSpec : ¬ SortSpec #[8,2,5,3] #[2] := by
  rintro ⟨-, h⟩
  revert h
  unfold SameElements Array.toMultiset
  decide

end SortRubric.Cheats.MinOnly
