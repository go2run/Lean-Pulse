/-
================================================================
  作弊：恆等函數 — **在第 02 次優化被淘汰**（由 `Sorted` 那一條殺）
  檔案      : SortRubric/Cheats/Opt02_Cheat_Identity.lean
  依賴      : Opt02_SameElements.lean
----------------------------------------------------------------
  ★ 這支作弊是「被規格的哪一條殺」那一欄**主動指出來的**，不是想出來的。

  第 02 次原本的三支作弊（AllZeros / DropElements / MinOnly）
  **全部**是被 `SameElements` 殺的，`Sorted` 零紀錄。
  那一欄的第一次使用就暴露了：不是 `Sorted` 可疑，是**我們的作弊集合有偏**——
  三支全是「有序但元素錯」，沒有一支是「**元素對但沒排序**」。

  那一支就是恆等函數。補上之後那張表才成立：
      `SameElements` 3 殺、`Sorted` 1 殺，兩條都是承重的，機械證明。

  → 這讓「被哪一條殺」從**紀錄**升級成**診斷工具**：
    它會主動指出你漏測了什麼。
----------------------------------------------------------------
  第 01 次  : ✅ 通過？**不**——第 01 次只有 `ensures Sorted arr`，它就死了。
              恆等函數是唯一一支**第 01 次就死、但第 02 次的另一條擋不住**的作弊。
  第 02 次  : ❌ 死於 `ensures Sorted arr`
----------------------------------------------------------------
  ⚠ 本檔含被 `#guard_msgs` 釘住的失敗證明，`Identity_correct` 帶 `sorryAx`（R5′）。
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt02_SameElements

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.Identity

open SortRubric.Opt02

/-! ## 1. 作弊本體：什麼都不做 -/

method Identity (mut arr : Array Int) return (u : Unit)
  ensures Sorted arr
  ensures SameElements arrOld arr
  do
    return

/-! ## 2. 為什麼死

`SameElements` 它**完美滿足**——一個元素都沒動，multiset 當然相等。
死的是 `Sorted`。 -/

/--
error: unsolved goals
case «ensures_2: Sorted arr»
arrOld : Array ℤ
⊢ Sorted arrOld
-/
#guard_msgs in
prove_correct Identity by
  loom_solve

/-! 目標 `⊢ Sorted arrOld` 讀起來就是「**請證明輸入本來就已經排好序了**」——
對任意輸入當然是假的。

這是四支作弊裡唯一一支目標**只跟輸入有關、跟輸出無關**的：
其他三支的目標形如 `SameElements arrOld <某個新東西>`，
這一支是 `Sorted arrOld`。因為它根本沒產生新東西。 -/

/-! ## 3. 程式照樣跑得動 -/

/-- info: DivM.res ((), #[8, 2, 5, 3]) -/
#guard_msgs in
#eval (Identity #[8,2,5,3]).run

/-! ## 4. 受控的 `sorryAx`，明文釘住 -/

/-- info: 'SortRubric.Cheats.Identity.Identity_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Identity_correct

/-! ## 5. 機械可檢的反證 —— ★ 用 `Sorted` 那一半

前三支作弊的反證都是 `rintro ⟨-, h⟩`（丟掉 `Sorted`，用 `SameElements`）。
這一支**反過來**：`rintro ⟨h, -⟩`。

證明的形狀本身就是「被哪一條殺」那一欄的機械證據。 -/

theorem identity_violates_sortSpec : ¬ SortSpec #[8,2,5,3] #[8,2,5,3] := by
  rintro ⟨h, -⟩                       -- 取 Sorted 那一半
  have h01 := h 0 1 ⟨by omega, by simp⟩ -- a[0]! ≤ a[1]! 即 8 ≤ 2
  simp at h01

/-- info: 'SortRubric.Cheats.Identity.identity_violates_sortSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_violates_sortSpec

end SortRubric.Cheats.Identity
