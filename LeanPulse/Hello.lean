/-
  LeanPulse.Hello — 對應 pulse-sandbox 的 `Hello.fst`

  Pulse 原文：
    fn test (x:unit)
      requires emp
      ensures emp
    { () }

  觀念對應：
  - Pulse 的 `fn` ↦ Velvet 的 `method`。
  - Pulse 的 `requires emp / ensures emp`（不擁有、也不歸還任何堆積資源）
    ↦ Velvet 中「沒有 mut 參數、沒有 require/ensures」的方法：
    Velvet 的規格只談值，不談資源，所以「空資源」就是「什麼都不用寫」。
  - Pulse 用 `fstar.exe` 檢查；Velvet 用 `prove_correct ... by loom_solve`，
    背後是 Lean 的 grind（或 SMT）自動證明。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method hello (x : Unit) return (u : Unit)
    do
    return

prove_correct hello by
  loom_solve

-- Velvet 程式是可執行的 Lean 定義——這是 Pulse 沒有的「多模態」能力之一：
-- 同一份程式可以直接跑、可以測試、也可以證明。
#eval (hello ()).run
