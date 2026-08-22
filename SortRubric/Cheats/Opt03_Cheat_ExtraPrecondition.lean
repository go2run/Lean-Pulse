/-
================================================================
  作弊：多一條前條件 — **在第 03 次優化被淘汰**
  檔案      : SortRubric/Cheats/Opt03_Cheat_ExtraPrecondition.lean
  依賴      : Opt03_Interface.lean
----------------------------------------------------------------
  第 02 次  : ✅ 通過。它**真的排序**，`Sorted` 與 `SameElements` 都成立，
              `prove_correct` 完全綠燈——第 02 次的 Level A（共用 predicate）
              管不到「每支 method 的前條件可以各寫各的」。
  第 03 次  : ❌ 死於 Level B——它塞不進 `SortImpl`。
----------------------------------------------------------------
  這正是 F\* 原文抱怨的情況:
    AutoCLRS 的四個演算法已經共用 sorted/permutation，
    但 heapsort 多一條 `SZ.fits` 前條件、只證 `sorted_upto s n`、
    還多一句「後半段不變」——**每一份都得從頭讀**。

  多一條前條件不會讓實作變錯，它讓 **rubric 失去意義**：
    審查者不能再「只讀規格」，因為每一份的規格都不一樣。
----------------------------------------------------------------
  ⚠ 本檔含一個被 `#guard_msgs` 釘住的失敗（型別錯誤，非 sorry）。
    `RestrictedSort_correct` 本身是**真定理**，不帶 sorryAx——
    失敗發生在「把它裝進 `SortImpl`」的那一步。
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt03_Interface

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Cheats.ExtraPrecondition

open SortRubric.Opt02 SortRubric.Opt03

attribute [grind] Array.multiset_swap

/-! ## 1. 作弊本體：一支**貨真價實的排序**，只是多要求了 `1 ≤ arr.size`

注意它跟 `Opt02_SameElements.lean` 的 `insertionSort` **只差一行 `require`**。
（官方 `Velvet/Examples/Examples.lean:52` 的 `insertionSort` 就是這樣寫的，
所以這不是杜撰的作弊，是很自然會出現的寫法。） -/

method RestrictedSort (mut arr : Array Int) return (u : Unit)
  require 1 ≤ arr.size            -- ★ 全部的差別就是這一行
  ensures Sorted arr
  ensures SameElements arrOld arr
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
      invariant n ≤ arr.size
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
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 1000000 in
prove_correct RestrictedSort by
  loom_solve!

/-! ## 2. 它在第 02 次是**完全合格**的

`prove_correct` 綠燈，而且是真定理——不帶 `sorryAx`： -/

/-- info: 'SortRubric.Cheats.ExtraPrecondition.RestrictedSort_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RestrictedSort_correct

/-- info: DivM.res ((), #[2, 3, 5, 8]) -/
#guard_msgs in
#eval (RestrictedSort #[8,2,5,3]).run

/-! ## 3. 第 03 次為什麼殺得掉它

`SortImpl.spec` 要求的前條件是 `True`（對**所有**輸入都要成立）。
`RestrictedSort_correct` 的前條件是 `1 ≤ arrOld.size`。
兩者對不上——而且**這是型別錯誤，不是證明失敗**：連寫都寫不出來。 -/

/--
error: Type mismatch
  RestrictedSort_correct
has type
  ∀ (arrOld : Array ℤ),
    {have arr := arrOld;
      1 ≤ arr.size}RestrictedSort arrOld{x,match x with
      | (u, arr) => SameElements arrOld arr ∧ Sorted arr}
but is expected to have type
  ∀ (a : Array ℤ), {True}RestrictedSort a{r,SortSpec a r.2}
-/
#guard_msgs in
def restrictedImpl : SortImpl where
  sort := RestrictedSort
  spec := RestrictedSort_correct

/-! ## 4. ★ R11 控制組：確認它是被**前條件**殺的，不是被別的東西殺的

型別錯誤特別容易跟「我們自己寫錯了」混淆。控制組把變因隔離到只剩那一行 `require`：

下面的 `UnrestrictedSort` 與上面的 `RestrictedSort` **body 一字不差**，
唯一的差別是**沒有** `require 1 ≤ arr.size`。它裝得進 `SortImpl`。

⇒ 失敗的成因是那一行 `require`，不是 body、不是橋接、不是環境。 -/

method UnrestrictedSort (mut arr : Array Int) return (u : Unit)
  -- 與 RestrictedSort 唯一的差別：這裡沒有 `require 1 ≤ arr.size`
  ensures Sorted arr
  ensures SameElements arrOld arr
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
      invariant n ≤ arr.size
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
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 1000000 in
prove_correct UnrestrictedSort by
  loom_solve!

/-- ★ 控制組通過：同樣的 body，拿掉 `require` 就裝得進去。 -/
def unrestrictedImpl : SortImpl where
  sort := UnrestrictedSort
  spec := fun a =>
    triple_cons _ le_rfl (fun _ h => ⟨h.2, h.1⟩) (UnrestrictedSort_correct a)

/-- info: 'SortRubric.Cheats.ExtraPrecondition.unrestrictedImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unrestrictedImpl

/-! **R11 判定**：`RestrictedSort` 的淘汰**成立**——
失敗目標指向 `SortImpl.spec` 的前條件形狀，且控制組確認 body 與橋接都沒問題。 -/

/-! **強度差別**：第 02 次擋作弊靠的是「證不出來」（`prove_correct` 失敗，留下 `sorryAx`）；
第 03 次擋的是「**寫不出來**」——型別檢查器在證明開始之前就拒絕了。

這跟第 06 次 `private mk` 的手法是同一類（見 README 的十步總表）。 -/

end SortRubric.Cheats.ExtraPrecondition
