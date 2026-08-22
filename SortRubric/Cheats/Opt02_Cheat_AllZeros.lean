/-
================================================================
  作弊：全部填 0 — **在第 02 次優化被淘汰**
  檔案      : SortRubric/Cheats/Opt02_Cheat_AllZeros.lean
  依賴      : Opt02_SameElements.lean
----------------------------------------------------------------
  命名慣例  : `OptNN_Cheat_*` = 在第 NN 次優化被淘汰的作弊。
              也就是說它在第 NN−1 次是**通得過的**。
              （相對地，`Unresolved_*` = 目前沒有任何一步淘汰得了。）

  第 01 次  : ✅ 通過（`ensures Sorted arr` 擋不住它）
  第 02 次  : ❌ 死於 `ensures SameElements arrOld arr`
----------------------------------------------------------------
  ⚠ 本檔含一個**被 `#guard_msgs` 釘住的失敗證明**，
    因此 `ZeroFill_correct` 帶 `sorryAx`（見 §2.3，已明文釘住）。
    這是 R5 的**受控例外**，三重圍堵：
      1. 失敗訊息由 `#guard_msgs` 釘住 —— 作弊哪天通過了，build 會紅
      2. `sorryAx` 由第二個 `#guard_msgs` 釘住 —— 它是明文，不是暗樁
      3. **沒有任何模組 import 本檔**（`check_isolation.sh` 每次複驗）
         —— 這點是必要的：`prove_correct` 產生的 lemma 帶 `@[loomSpec]`，
         一個 sorry 過的 spec 若被下游看見，可能污染 `loom_solve`
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt02_SameElements

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.AllZeros

open SortRubric.Opt02

/-! ## 1. 作弊本體（真的程式，不是只有 `example`）

R10：每一步「應該通得過／應該通不過」的宣稱，都必須有一支真的跑過 `prove_correct` 的程式。
`example : ¬ SortSpec …` 講的是命題，rubric 擋的是**程式**。

這裡直接掛上**第 02 次的完整規格**，讓失敗成為 build 的一部分。 -/

method ZeroFill (mut arr : Array Int) return (u : Unit)
  ensures Sorted arr                    -- 第 01 次的規格：它**滿足**
  ensures SameElements arrOld arr       -- 第 02 次補上的：它**做不到**
  do
    arr := Array.replicate arr.size 0
    return

/-! ## 2. 第 02 次為什麼殺得掉它

### 2.1 ★ 失敗被釘進 build（R6 的強化版）

`#guard_msgs` 在訊息相符時**吃掉**該則訊息，build 保持綠；
訊息不符、或**根本沒有訊息（= 作弊居然通過了）**時，它自己報錯。

於是「這支作弊證不出來」不再是一次性的觀察，而是一個
**會隨規格演進自動失效的迴歸測試**——`SortSpec` 之後還要改三次（第 04、08、09），
改完之後若這段沒跟著更新，build 立刻會告訴你。 -/

/--
error: unsolved goals
case «ensures_1: SameElements arrOld arr»
arrOld : Array ℤ
⊢ SameElements arrOld (Array.replicate arrOld.size 0)
-/
#guard_msgs in
prove_correct ZeroFill by
  loom_solve

/-! 那個目標 `SameElements arrOld (Array.replicate arrOld.size 0)` **是假的**
（只要 `arrOld` 有任何一個非 0 元素），所以不是「證不出來」，是「不成立」。 -/

/-! ### 2.2 程式本身照樣跑得動——失敗的是**證明**，不是程式 -/

/-- info: DivM.res ((), #[0, 0, 0, 0]) -/
#guard_msgs in
#eval (ZeroFill #[8,2,5,3]).run

/-! ### 2.3 受控的 `sorryAx`，明文釘住

證明失敗後 Lean 仍會把 `ZeroFill_correct` 加進環境，並讓它依賴 `sorryAx`。
**把它釘出來**，而不是讓它變成暗樁： -/

/-- info: 'SortRubric.Cheats.AllZeros.ZeroFill_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZeroFill_correct

/-! ### 2.4 機械可檢的反證（不依賴上面任何 sorry） -/

theorem zeroFill_violates_sortSpec : ¬ SortSpec #[8,2,5,3] #[0,0,0,0] := by
  rintro ⟨-, h⟩
  revert h
  unfold SameElements Array.toMultiset
  decide

/-- info: 'SortRubric.Cheats.AllZeros.zeroFill_violates_sortSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeroFill_violates_sortSpec

end SortRubric.Cheats.AllZeros
