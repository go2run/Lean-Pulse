import Velvet.Std

/-!
# Velvet → 可執行程式：抽取與編譯的示範

對應 `doc/VelvetExec.md`。這個檔案示範完整流程：

1. `method` + `prove_correct` —— 寫規格、寫實作、驗證。
2. `extract_program_for` —— 從 `VelvetM` 抽出純 `DivM` 的可執行版本 `⟨name⟩Exec`。
3. `prove_pre/postcondition_decidable_for` + `derive_tester_for` —— 產生
   把規格當 runtime check 的 `⟨name⟩Tester`。
4. `Main.lean`（`lean_exe velvet_demo`）把 `⟨name⟩Exec` 包進 `IO`，
   `lake build velvet_demo` 產生原生執行檔。
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-! ## 例一：無迴圈（`.run` 直接可用） -/

method Maximum (a : Int) (b : Int) return (m : Int)
    ensures m ≥ a
    ensures m ≥ b
    ensures m = a ∨ m = b
    do
    if a ≥ b then
      return a
    else
      return b

prove_correct Maximum by
  loom_solve

/-- info: DivM.res 7 -/
#guard_msgs in
#eval (Maximum 3 7).run

-- 抽取：產生 `MaximumExec (a b : Int) : DivM Int`
extract_program_for Maximum

/-- info: DivM.res 7 -/
#guard_msgs in
#eval MaximumExec 3 7

/-! ## 例二：有 `mut` 參數與 `while` 迴圈 -/

method DoubleAll (mut arr : Array Int) return (u : Unit)
    ensures arr.size = arrOld.size
    ensures ∀ i, i < arr.size → arr[i]! = 2 * arrOld[i]!
    do
    let mut i := 0
    while i < arr.size
      invariant arr.size = arrOld.size
      invariant i ≤ arr.size
      invariant ∀ k, k < i → arr[k]! = 2 * arrOld[k]!
      invariant ∀ k, i ≤ k ∧ k < arr.size → arr[k]! = arrOld[k]!
      done_with i = arr.size
    do
      arr := arr.set! i (2 * arr[i]!)
      i := i + 1
    return

prove_correct DoubleAll by
  loom_solve

-- 抽取有 `mut` 參數的方法：回傳型別是 `DivM (Unit × Array Int)`
extract_program_for DoubleAll

/-- info: DivM.res ((), #[2, 4, 6]) -/
#guard_msgs in
#eval DoubleAllExec #[1, 2, 3]

/-! ## 例三：規格轉成 runtime check（tester） -/

-- 把 require/ensures 轉成可判定的 `Decidable` 實例，再組成 `DoubleAllTester`
prove_precondition_decidable_for DoubleAll
prove_postcondition_decidable_for DoubleAll
derive_tester_for DoubleAll

/-- info: true -/
#guard_msgs in
#eval DoubleAllTester #[1, 2, 3]

/-
tester 抓得到 bug：下面這版少跑最後一格（`arr.size - 1`）。
它沒有 `prove_correct`（證不出來），但 tester 不需要證明就能跑。
-/
method DoubleAllBuggy (mut arr : Array Int) return (u : Unit)
    ensures arr.size = arrOld.size
    ensures ∀ i, i < arr.size → arr[i]! = 2 * arrOld[i]!
    do
    let mut i := 0
    while i < arr.size - 1
      invariant arr.size = arrOld.size
      invariant i ≤ arr.size
      done_with i = arr.size - 1
    do
      arr := arr.set! i (2 * arr[i]!)
      i := i + 1
    return

extract_program_for DoubleAllBuggy
prove_precondition_decidable_for DoubleAllBuggy
prove_postcondition_decidable_for DoubleAllBuggy
derive_tester_for DoubleAllBuggy

/-- info: DivM.res ((), #[2, 4, 3]) -/
#guard_msgs in
#eval DoubleAllBuggyExec #[1, 2, 3]

/-- info: false -/
#guard_msgs in
#eval DoubleAllBuggyTester #[1, 2, 3]

/-! ## 例四：用 Plausible 做隨機測試（驗證前的第一道防線） -/

run_elab do
  let g : Plausible.Gen (Array Int × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    pure (arr, DoubleAllBuggyTester arr)
  for _ in [0:200] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break
