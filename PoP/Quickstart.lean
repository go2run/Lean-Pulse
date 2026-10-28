/-
  PoP.Quickstart — Velvet V2 最小範例：把 V1 的 `VelvetExec.lean`（v1/tutorial 分支）
  與 `LeanPulse/Ref.lean`（v1/LeanPulse 分支）的幾個方法移植到 V2。

  V1 → V2 對照表：
  │ V1（Loom，Lean v4.24.0）                  │ V2（v2.0，Lean v4.34.0）                          │
  │ import Velvet.Std                         │ import Velvet                                      │
  │ method f (x : τ) return (r : ρ)           │ method f (x : τ) returns (r : ρ) [in M]            │
  │ require P                                 │ requires [名稱 :] P                                │
  │ (mut a : τ) + 規格裡的 aOld               │ 無 mut 參數：回傳新值（規格裡的 a 就是舊值），     │
  │                                           │   或改用 StateM τ + given (a₀ : τ) 捕捉初值       │
  │ prove_correct f by loom_solve             │ prove_correct f by velvet_vcgen [f] with finish    │
  │ set_option loom.semantics.termination …   │ set_option velvet.semantics.termination …          │
  │ 預設 partial（while 不需 decreasing）     │ 預設 total：while 必須寫 decreasing                │
  │ set_option loom.semantics.choice …        │ 改成選 monad：DemonicT / AngelicT                  │
  │ DivM、extract_program_for f → fExec       │ 方法本身就能執行（預設 monad 是 Option）           │
  │ prove_*_decidable_for + derive_tester_for │ #derive_tester_for f → f.check（回傳 TestVerdict） │
  │   → fTester : … → Bool                    │   decidable 多半自動推得，不行才手動補             │
  │ swap! a[i]! a[j]!                         │ 手寫兩次 set!（見 InsertionSort.lean）             │
-/
import Velvet
import Plausible

open Velvet.Testing

namespace PoP.Quickstart

/-! ## 例一：無迴圈

每個方法都跑在某個 monad 裡，用 `in M` 指定。`in M` 和 `signals` 都沒寫時，Velvet 用
`Option`：`maximum : Int → Int → Option Int`，正常結束得到 `some 值`，`failure` 得到 `none`。
證明的合約（預設 total）也保證：滿足 `requires` 時一定不會是 `none`。 -/

method maximum (a b : Int) returns (m : Int)
  ensures ge_a: m ≥ a
  ensures ge_b: m ≥ b
  ensures is_arg: m = a ∨ m = b
do
  if a ≥ b then
    return a
  else
    return b

prove_correct maximum by
  velvet_vcgen [maximum] with finish

/-- info: some 7 -/
#guard_msgs in
#eval maximum 3 7

/-! ## 例二：V1 的 `(mut arr)` 改成「回傳新陣列」，`arrOld` 就是參數 `arr` 本身

V2 預設 total correctness，所以 `while` 一定要給 `decreasing`。 -/

method doubleAll (arr : Array Int) returns (res : Array Int)
  requires True   -- 給 tester 用，見例三
  ensures same_size: res.size = arr.size
  ensures doubled: ∀ i, i < res.size → res[i]! = 2 * arr[i]!
do
  let mut res := arr
  let mut i := 0
  while loop_cond: i < res.size
    invariant sz: res.size = arr.size
    invariant i_le: i ≤ res.size
    invariant done_prefix: ∀ k, k < i → res[k]! = 2 * arr[k]!
    invariant rest_same: ∀ k, i ≤ k → k < res.size → res[k]! = arr[k]!
    decreasing remaining: res.size - i
    done_with at_end: i = res.size
  do
    res := res.set! i (2 * res[i]!)
    i := i + 1
  return res

prove_correct doubleAll by
  velvet_vcgen [doubleAll] with finish

/-- info: some #[2, 4, 6] -/
#guard_msgs in
#eval doubleAll #[1, 2, 3]

/-! ## 例三：規格當 runtime check。`#derive_tester_for f` 產生 `f.check`

`.pass` / `.fail` / `.discard`（前置條件不成立，不執行）。不需要先證明。

v2.0 的 tester 有兩個坑（上游 Testing.lean 的例子剛好都沒踩到）：
1. 沒寫 `requires` 時，前置條件是裸的 `True`，tester 內部的 `simp only` 沒進展就報錯
   → 補一行 `requires True`。
2. 多條 `ensures` 會被 `Lean.Order.meet` 合起來；tester 先把 `meet` 展開成 `inf`，
   核心的 `meet_prop_eq_and` 就套不上，Decidable 推不出來。兩種解法：
   (A) 合成一條 `ensures … ∧ …`（見 `doubleAllBuggy`）；
   (B) 保留具名的多條 `ensures`，自己用 `inf_pair_prop` 補 postcondition（見下）。 -/

theorem inf_pair_prop (a b : Prop) : Lean.Order.inf (fun z => z = a ∨ z = b) = (a ∧ b) :=
  Lean.Order.meet_prop_eq_and a b

-- 要證的目標：Decidable (inf {z | z = (res.size = arr.size) ∨ z = (∀ i, …)})
prove_postcondition_decidable_for doubleAll by
  simp only [inf_pair_prop]   -- 目標變成 Decidable (res.size = arr.size ∧ ∀ i, i < res.size → …)
  infer_instance              -- `=` 可判定、`∀ i < n` 可判定、`∧` 可判定 → 交給 Lean 自動找

#derive_tester_for doubleAll                 -- 產生 doubleAll.check : Array Int → TestVerdict
#guard doubleAll.check #[1, 2, 3] == .pass   -- 編譯時就執行；不成立的話建置失敗

/-- 少跑最後一格的錯誤版本：證不出來，但 tester 照樣能跑、能抓到。 -/
method doubleAllBuggy (arr : Array Int) returns (res : Array Int)
  requires True
  ensures post: res.size = arr.size ∧ ∀ i, i < res.size → res[i]! = 2 * arr[i]!
do
  let mut res := arr
  let mut i := 0
  while loop_cond: i < res.size - 1
    invariant sz: res.size = arr.size
    decreasing remaining: res.size - i
  do
    res := res.set! i (2 * res[i]!)
    i := i + 1
  return res

#derive_tester_for doubleAllBuggy
#guard doubleAllBuggy.check #[1, 2, 3] == .fail
#guard doubleAllBuggy.check #[1, 2, 0] == .pass   -- 最後一格是 0 時剛好躲過

/-! ## 例四：用 Plausible 隨機產生輸入，餵給 `.check`（驗證前的第一道防線） -/

run_elab do
  let mut fails := 0
  let mut firstBad : Option (Array Int) := none
  for _ in [0:100] do
    let arr ← Plausible.Gen.run (Plausible.SampleableExt.interpSample (Array Int)) 10
    if doubleAllBuggy.check arr == .fail then
      fails := fails + 1
      if firstBad.isNone then firstBad := some arr
  IO.println s!"doubleAllBuggy: {fails}/100 次違反後條件，第一個反例 {firstBad}"

/-! ## 例五：Pulse 的 `ref` —— V1 用 `(mut r)` + `rOld`，V2 用 `StateM Int` + `given`

Pulse：`fn incr (r:ref int) requires pts_to r 'v ensures pts_to r ('v + 1)`
狀態就是 `r` 指向的值，`given (v₀ : Int)` 就是 ghost 的 `'v`。 -/

method add (n : Int) returns (u : PUnit) in StateM Int
  given (v₀ : Int)
  requires (r : Int) => r = v₀
  ensures (r : Int) => r = v₀ + n
do
  let v ← get
  set (v + n)

prove_correct add by
  velvet_vcgen [add] with finish

/-- Pulse 的 `quadruple`：呼叫兩次 `add`，驗證時自動套用 `add.spec`。 -/
method quadruple returns (u : PUnit) in StateM Int
  given (v₀ : Int)
  requires (r : Int) => r = v₀
  ensures (r : Int) => r = 4 * v₀
do
  let v1 ← get
  add v1
  let v2 ← get
  add v2

prove_correct quadruple by
  velvet_vcgen [quadruple] with finish

/-- info: ((), 20) -/
#guard_msgs in
#eval (quadruple).run 5

end PoP.Quickstart
