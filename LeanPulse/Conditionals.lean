/-
  LeanPulse.Conditionals — 對應
  `src/tutorial/PulseTutorial.Conditionals.fst`

  Pulse 本課同時示範一般分支，以及「nullable ref + 自訂 slprop」。
  Velvet 沒有可別名的 heap reference，因此分成兩種翻譯：

  * 唯讀 `ref int` 直接成為 `Int` 值；分支的驗證條件由 Loom 產生。
  * `option (ref α)` 降成 `Option α`。這保留「空／有值」的功能行為，
    但不聲稱保留 Pulse 的所有權、分數權限或 aliasing 語意。

  Pulse 的 `max_alt2` 必須替 if 寫分支後置條件，才能重新取得區域
  reference 的精確內容。Velvet 會把 `let mut` 轉成單子中的值傳遞，
  所以 `maxValueAlt` 不需要額外 annotation；這正是兩種驗證模型的差異。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

@[reducible]
def maxSpec (x y : Int) : Int :=
  if x < y then y else x

method maxValue (x : Int) (y : Int) return (n : Int)
    ensures n = maxSpec x y
    do
    if x > y then
      return x
    else
      return y

prove_correct maxValue by
  loom_solve

method maxValueAlt (x : Int) (y : Int) return (n : Int)
    ensures n = maxSpec x y
    do
    let mut result := 0
    if x > y then
      result := x
    else
      result := y
    return result

prove_correct maxValueAlt by
  loom_solve

/- `pts_to_or_null r v` 在 Pulse 是 heap predicate；值模型中只剩
   「目前觀察值等於 v」這個純命題。 -/
@[reducible]
def ptsToOrNull (cell view : Option α) : Prop :=
  cell = view

theorem ptsToOrNull_none :
    ptsToOrNull (none : Option α) view ↔ view = none := by
  unfold ptsToOrNull
  constructor <;> intro h <;> exact h.symm

theorem ptsToOrNull_some (x : α) :
    ptsToOrNull (some x) view ↔ view = some x := by
  unfold ptsToOrNull
  constructor <;> intro h <;> exact h.symm

method readNullable (r : Option α) return (o : Option α)
    ensures ptsToOrNull r o
    do
    match r with
    | none => pure none
    | some x => pure (some x)

prove_correct readNullable by
  loom_solve

/- Pulse 的 `read_nullable_alt` 透過四個 ghost helper
   顯式折疊／展開 `pts_to_or_null`。在值投影中，那四步就是上面的
   `ptsToOrNull_none` / `ptsToOrNull_some` 等價，所以執行內容退化為
   identity；保留另一個 method 名稱，讓原教材的對照仍可追蹤。 -/
method readNullableAlt (r : Option α) return (o : Option α)
    ensures ptsToOrNull r o
    do
    return r

prove_correct readNullableAlt by
  loom_solve

@[reducible]
def writeNullableSpec (cell : Option α) (v : α) : Option α :=
  cell.map (fun _ => v)

/- Pulse 的 write_nullable 只在 r = Some ref 時寫入；None 保持 None。
   `mut cell` 讓 Velvet 同時產生 cellOld 與最終 cell。 -/
method writeNullable (mut cell : Option α) (v : α) return (u : Unit)
    ensures cell = writeNullableSpec cellOld v
    ensures cellOld = none → cell = none
    ensures (∃ old, cellOld = some old) → cell = some v
    do
    cell := writeNullableSpec cell v
    return

prove_correct writeNullable by
  loom_solve
