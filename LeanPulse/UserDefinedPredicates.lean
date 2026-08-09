/-
  LeanPulse.UserDefinedPredicates — 對應
  `src/tutorial/PulseTutorial.UserDefinedPredicates.fst`

  Pulse 的自訂 predicate 封裝 heap ownership；`fold`/`unfold` 會在
  抽象 predicate 與底層 `pts_to` 資源之間切換。Velvet 規格可以
  直接使用 Lean `def ... : Prop`，但它封裝的是值關係，不是資源。
  因此 fold/unfold 變成普通定義展開，通常由 `loom_solve` 完成。

  `double`/`double_alt`、`move`/`move_alt` 與
  `create_and_move`/`create_and_move_alt` 的差別只在 Pulse 的
  fold/unfold helper；值投影後各對合併成一個 Velvet method。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

@[reducible]
def ptsToDiag (p : Int × Int) (v : Int) : Prop :=
  p = (v, v)

method doubleDiag
    (mut p : Int × Int) (v : Int) return (u : Unit)
    require ptsToDiag p v
    ensures ptsToDiag p (2 * v)
    do
    let doubled := p.1 + p.2
    p := (doubled, doubled)
    return

prove_correct doubleDiag by
  loom_solve

structure Point where
  x : Int
  y : Int
deriving Repr, DecidableEq

@[reducible]
def isPoint (p : Point) (xy : Int × Int) : Prop :=
  p.x = xy.1 ∧ p.y = xy.2

theorem foldIsPoint (p : Point) :
    isPoint p (p.x, p.y) := by
  simp [isPoint]

method movePoint
    (mut p : Point) (dx : Int) (dy : Int) return (u : Unit)
    ensures p.x = pOld.x + dx
    ensures p.y = pOld.y + dy
    ensures isPoint p (pOld.x + dx, pOld.y + dy)
    do
    p := { x := p.x + dx, y := p.y + dy }
    return

prove_correct movePoint by
  loom_solve

method createAndMove (u : Unit) return (p : Point)
    ensures isPoint p (1, 1)
    do
    let mut p : Point := { x := 0, y := 0 }
    p := { x := p.x + 1, y := p.y + 1 }
    return p

prove_correct createAndMove by
  loom_solve

@[reducible]
def isPointCurry (p : Point) (x y : Int) : Prop :=
  p.x = x ∧ p.y = y

method movePointCurry
    (mut p : Point) (dx : Int) (dy : Int) return (u : Unit)
    ensures isPointCurry p (pOld.x + dx) (pOld.y + dy)
    do
    p := { x := p.x + dx, y := p.y + dy }
    return

prove_correct movePointCurry by
  loom_solve
