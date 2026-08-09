/-
  LeanPulse.Existentials — 對應
  `src/tutorial/PulseTutorial.Existentials.fst`

  Pulse 的 `exists*` 是 separation-logic assertion 裡的存在量詞：
  它不只隱藏一個值，也把該值和一塊 heap 資源綁在一起。Velvet 的
  mutable argument 已直接帶著目前值，因此「存在某個舊值」通常不再
  是前置條件；需要隱藏輸出 witness 時，則使用普通 Lean `∃`。

  對照：
  * `exists* w. pts_to x w`  ↦ `mut x` 已經提供一個具體值
  * `introduce exists* ... with e` ↦ 由 `loom_solve` 建立 Lean 的 `∃ e`
  * Pulse 中離開量詞作用域的 witness 不可使用；Lean 的 binder
    同樣以詞法作用域防止這件事。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method assignExisting (mut x : α) (v : α) return (u : Unit)
    ensures x = v
    do
    x := v
    return

prove_correct assignExisting by
  loom_solve

/- 對應 make_even_explicit：程式相同，但這裡把 witness 的選擇寫成
   普通 Lean lemma，顯示它並不是另一種執行行為。 -/
theorem doubled_is_even (v : Int) :
    ∃ w, v + v = w ∧ w % 2 = 0 := by
  refine ⟨v + v, rfl, ?_⟩
  omega

method makeEven (mut x : Int) return (u : Unit)
    ensures ∃ w, x = w ∧ w % 2 = 0
    do
    x := x + x
    return

prove_correct makeEven by
  loom_solve
  exact doubled_is_even _

/- Pulse 的 explicit 版本把 existential witness 的引入寫在程式裡；
   Velvet 對應是把相同 witness lemma 寫在 `prove_correct` 區塊。 -/
method makeEvenExplicit (mut x : Int) return (u : Unit)
    ensures ∃ w, x = w ∧ w % 2 = 0
    do
    x := x + x
    return

prove_correct makeEvenExplicit by
  loom_solve
  exact doubled_is_even _

theorem add_even_of_same_remainder (x y : Int)
    (h : x % 2 = y % 2) :
    (x + y) % 2 = 0 := by
  omega

attribute [grind] add_even_of_same_remainder

method makeEvenExplicitAlt
    (mut x : Int) (y : Int) return (u : Unit)
    require x % 2 = y % 2
    ensures ∃ x', x = x' ∧ x' % 2 = 0
    do
    x := x + y
    return

prove_correct makeEvenExplicitAlt by
  loom_solve

/- 對應 call_make_even 的「呼叫後只知道存在某個偶數」。
   在 Velvet 值模型中，最終值就是可用 witness。 -/
method callMakeEven (mut x : Int) return (u : Unit)
    ensures ∃ w, x = w ∧ w % 2 = 0
    do
    x := x + x
    return

prove_correct callMakeEven by
  loom_solve
  exact doubled_is_even _
