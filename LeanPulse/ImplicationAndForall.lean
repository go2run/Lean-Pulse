/-
  LeanPulse.ImplicationAndForall — 對應
  `src/tutorial/PulseTutorial.ImplicationAndForall.fst`

  本檔刻意主要使用「普通 Lean theorem」，而非假裝 Velvet 已具備
  Pulse 的 ghost heap。Pulse 的 `@==>` 是 separating implication
  (magic wand)：它本身是可消耗的資源；`forall*` 也是 spatial
  quantifier。翻成 Lean 的 `→` / `∀` 後，只保留邏輯形狀，不保留
  線性、所有權或可消耗性。Lean 的 proof term 可重複使用，這一點
  與 Pulse 不等價。

  對 Velvet 而言，這些 theorem 可以直接成為 VC 的 helper lemma；
  這正是論文所稱「自動 + 互動」多模態證明的互補位置。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Pulse:
     pts_to x #0.5R v @==> pts_to x v
   純命題投影只保留「若 Half v 成立，就能得到 Full v」。 -/
@[reducible]
def RegainHalf (Half Full : α → Prop) (v : α) : Prop :=
  Half v → Full v

theorem useRegainHalf
    (Half Full : α → Prop) (v : α)
    (half : Half v) (cap : RegainHalf Half Full v) :
    Full v :=
  cap half

@[reducible]
def RegainHalfQ (Half Full : α → Prop) : Prop :=
  ∀ v, Half v → Full v

theorem specializeRegainHalf
    (Half Full : α → Prop)
    (cap : RegainHalfQ Half Full) (v : α) :
    RegainHalf Half Full v :=
  cap v

theorem useRegainHalfQ
    (Half Full : α → Prop)
    (cap : RegainHalfQ Half Full) (v : α) (half : Half v) :
    Full v :=
  cap v half

/- Pulse 的 can_update:
     forall* old new. Half old @==> Full new
   這裡只保留量詞與 implication 的外形。 -/
@[reducible]
def CanUpdate (Half Full : Int → Prop) : Prop :=
  ∀ old new, Half old → Full new

theorem useCanUpdate
    (Half Full : Int → Prop)
    (cap : CanUpdate Half Full)
    (old new : Int) (half : Half old) :
    Full new :=
  cap old new half

/- 執行層的更新仍由 Velvet 規格約束。allowed 是純 policy，
   不是 Pulse 中可分割、可回收的 permission token。 -/
method updateAllowed
    (mut x : Int) (next : Int) (allowed : Int → Int → Prop)
    return (u : Unit)
    require allowed x next
    ensures x = next
    ensures allowed xOld x
    do
    x := next
    return

prove_correct updateAllowed by
  loom_solve

