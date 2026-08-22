/-
================================================================
  作弊：用 `triple_cons` 把前條件「洗掉」— **擋得住**
  檔案      : SortRubric/Cheats/Opt03_Cheat_LaunderPrecondition.lean
  依賴      : Opt03_Cheat_ExtraPrecondition.lean
----------------------------------------------------------------
  這個檔案不是在示範一支「曾經通得過」的作弊，
  而是在**測試我們自己剛引進的規則**。

  第 02 次的橋接改用了 Loom 的 consequence rule `triple_cons`
  （`Loom/MonadAlgebras/WP/Basic.lean:54`）：

      triple_cons : pre' ≤ pre → (∀ y, post y ≤ post' y)
                  → triple pre x post → triple pre' x post'

  它同時做兩件事：**弱化後條件**、**強化前條件**。
  而第二件事正好卡在第 03 次唯一的保證上——
  `RestrictedSort` 進不了 `SortImpl` 的門，就是因為它的前條件是
  `1 ≤ arr.size` 而不是 `True`。

  **問題**：`triple_cons` 會不會讓人把 `1 ≤ arr.size` 洗成 `True`，
           從而讓第 03 次整步作廢？

  **答案**：不會。但這是實測出來的，不是推論出來的——
           「一條沒有被試圖繞過的規則，不知道它擋不擋得住。」
----------------------------------------------------------------
  狀態: [x] 完成（規則守住了，且已釘進 build）
================================================================
-/
import SortRubric.Cheats.Opt03_Cheat_ExtraPrecondition

namespace SortRubric.Cheats.LaunderPrecondition

open SortRubric.Opt02 SortRubric.Opt03 SortRubric.Cheats.ExtraPrecondition
open PartialCorrectness PartialCorrectness.DemonicChoice

/-! ## 1. 洗前條件：失敗（已釘住）

`pre' ≤ pre` 在 `l = Prop` 時就是「`pre'` 蘊涵 `pre`」。
要把 `triple (1 ≤ size) …` 洗成 `triple True …`，需要的是 `True → 1 ≤ size`——**假的**。 -/

/--
error: Tactic `assumption` failed

a : Array ℤ
⊢ True ≤
    have arr := a;
    1 ≤ arr.size
-/
#guard_msgs in
def laundered : SortImpl where
  sort := RestrictedSort
  spec := fun a =>
    triple_cons _ (by trivial) (fun _ h => ⟨h.2, h.1⟩) (RestrictedSort_correct a)

/-! 目標 `True ≤ (1 ≤ arr.size)` 對空陣列是假的，所以不是「證不出來」，是**不成立**。

`triple_cons` 的方向性是**安全**的：它只讓你把前條件變得**更嚴**，
不讓你變鬆。第 03 次的保證守住了。 -/

/-! ## 2. 對照：安全的方向確實可行（而且沒用）

反過來——從 `triple True …` 得到 `triple (1 ≤ size) …`——是成立的，
因為 `(1 ≤ size) → True`。

這正好說明為什麼方向性是對的：**強化前條件只會讓 contract 更難用，不會讓它更好過。**
一個只在 `1 ≤ size` 時成立的保證，本來就比「對所有輸入成立」弱。 -/

example : ∀ a, triple (1 ≤ (a : Array Int).size)
                      (insertionSort a) (fun r => SortSpec a r.2) :=
  fun a => triple_cons _ (fun _ => trivial) (fun _ h => h) (insertionSort_sortSpec a)

/-! ## 3. `laundered` 帶 `sorryAx`，明文釘住（R5′）

`by trivial` 失敗後 Lean 仍會把 `laundered` 加進環境並讓它依賴 `sorryAx`。
與 `Cheats/` 其他檔案同一個處理：釘成明文，且本檔不被任何模組 import。 -/

/-- info: 'SortRubric.Cheats.LaunderPrecondition.laundered' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms laundered

end SortRubric.Cheats.LaunderPrecondition
