/-
================================================================
  上游 bug 最小重現（檔 2／2）— 未證的 spec 會污染下游驗證
  檔案      : SortRubric/Cheats/Upstream_ContaminationB.lean
  依賴      : Upstream_ContaminationA.lean
----------------------------------------------------------------
  ★ 本檔是整個重現的重點：

    下面的 `UseDoubler` 宣稱 `y = yOld * 2`，而它做的事只是呼叫 `Doubler`
    （body 實際上是 `y := y + 1`）。這個宣稱**是假的**——見 §3 的 `#eval`。

    但 `prove_correct UseDoubler by loom_solve` **完全沒有報錯**。

    `loom_solve` 用檔 1 那條**未證的** `Doubler_correct` 補完了它的證明。

  唯一的信號是 `#print axioms`，而多數人不會跑。
----------------------------------------------------------------
  使用者流程（完全正常，沒有人在作弊）:
    1. 寫 method A，prove_correct 失敗，先擱著往下做
    2. A_correct 帶著 sorryAx 進了 loom_solve 的取用集合
    3. 寫 method B，B 呼叫 A
    4. loom_solve 用那條未證的 A_correct 補完了 B 的證明
    5. B 綠燈，且**不產生任何訊息**
----------------------------------------------------------------
  狀態: [x] 完成（bug 重現成功）
================================================================
-/
import SortRubric.Cheats.Upstream_ContaminationA

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.Upstream

/-! ## 1. B 呼叫 A

呼叫語法用**明確解構 tuple**——`mut` 參數的 method 只有這個形式能用，
見 `Opt00_GUIDE_ERRATA.md`（bare `Doubler y` 與 `let r ← Doubler y` 都會壞）。 -/

method UseDoubler (mut y : Nat) return (u : Unit)
  ensures y = yOld * 2
  do
    let ⟨_, y'⟩ ← Doubler y
    y := y'
    return

/-! ## 2. ★ 它綠燈了，而且一句訊息都沒有

下面這行**沒有**被 `#guard_msgs` 包住——因為它根本不產生訊息。
`prove_correct` 直接成功。 -/

prove_correct UseDoubler by
  loom_solve

/-! ## 3. 但它宣稱的東西是假的

`yOld = 3` 時，`UseDoubler` 實際回傳 4；而它的 `ensures` 說 `3 * 2 = 6`。 -/

/-- info: DivM.res ((), 4) -/
#guard_msgs in
#eval (UseDoubler 3).run

/-! ## 4. 唯一的信號

`sorryAx` 從檔 1 一路傳染過來。這是使用者唯一能察覺的線索。 -/

/-- info: 'SortRubric.Cheats.Upstream.UseDoubler_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UseDoubler_correct

end SortRubric.Cheats.Upstream
