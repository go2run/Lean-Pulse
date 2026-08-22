/-
================================================================
  上游 bug 最小重現（檔 1／2）— 未證的 spec 會污染下游驗證
  檔案      : SortRubric/Cheats/Upstream_ContaminationA.lean
----------------------------------------------------------------
  命名慣例第三類：`Upstream_*` = 給上游的最小重現，不是本 rubric 的作弊。
  （另兩類：`OptNN_Cheat_*` 已被第 NN 次淘汰；`Unresolved_*` 無解。）
----------------------------------------------------------------
  本檔的角色：一支 `prove_correct` **失敗**的 method。
  它的 `ensures` 是**假的**：body 做 `x := x + 1`，卻宣稱 `x = xOld * 2`
  （xOld = 3 時 body 給 4，spec 要 6）。

  失敗後 Lean 仍會註冊 `Doubler_correct`，帶 `sorryAx`，
  **而且帶 `@[loomSpec]`**（`Velvet/Syntax.lean:411`），
  也就是進入 `loom_solve` 的取用集合。

  後果見檔 2。
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.Upstream

/-! 這是使用者完全正常的流程：先寫 method、證明還沒過、先擱著往下做。 -/

method Doubler (mut x : Nat) return (u : Unit)
  ensures x = xOld * 2
  do
    x := x + 1
    return

/-! 失敗訊息被釘住：目標 `xOld + 1 = xOld * 2` 是假的。 -/

/--
error: unsolved goals
case «ensures_1: x = xOld * 2»
xOld : ℕ
⊢ xOld + 1 = xOld * 2
-/
#guard_msgs in
prove_correct Doubler by
  loom_solve

/-- info: 'SortRubric.Cheats.Upstream.Doubler_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Doubler_correct

end SortRubric.Cheats.Upstream
