/-
================================================================
  上游 bug 最小重現 — **控制組**：連「真話」都會被污染
  檔案      : SortRubric/Cheats/Upstream_ContaminationControl.lean
----------------------------------------------------------------
  檔 A／B 用的是一個【假的】spec，那容易讓人以為
  「只要別寫錯 spec 就沒事」。**不是。**

  本控制組裡：
    - A' 的 spec 是【真的】（`#eval` 證實）
    - B' 的 spec 也是【真的】（`#eval` 證實）
    - 唯一的問題是 A' 少了一條 invariant，證明還沒補完
    - B' 照樣綠燈，而且帶 sorryAx

  **沒有人寫錯任何東西。** 使用者只是還沒把一個證明做完，
  而工具靜默地宣告了第二個證明成立。

  這才是真實的觸發條件——「先寫 spec、proof 之後再補」是被鼓勵的工作流程。
----------------------------------------------------------------
  ⚠ 本檔含被 `#guard_msgs` 釘住的失敗證明，兩條 `_correct` 都帶 `sorryAx`（R5′）。
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.UpstreamControl

/-! ## 1. A'：spec 是真的，只是還沒證完

`ensures x = xOld + 2` **是對的**——迴圈確實跑兩次、每次加一。
證明過不了只是因為少了 `invariant x = xOld + i`。
這是每個人每天都在做的事：先把 spec 寫下來，證明晚點補。 -/

method AddTwo (mut x : Nat) return (u : Unit)
  ensures x = xOld + 2
  do
    let mut i := 0
    while i < 2
    invariant i ≤ 2          -- 少了 `invariant x = xOld + i`
    done_with i = 2
    do
      x := x + 1
      i := i + 1
    return

/--
error: unsolved goals
case «ensures_1: x = xOld + 2»
xOld i x : ℕ
invariant_1 : i ≤ 2
done_1 : i = 2
i_1 x_1 : ℕ
i_2 : { fst := i, snd := x } = { fst := i_1, snd := x_1 }
⊢ x_1 = xOld + 2
-/
#guard_msgs in
prove_correct AddTwo by
  loom_solve

/-! ### A' 的 spec 確實是真的 -/

/-- info: DivM.res ((), 7) -/
#guard_msgs in
#eval (AddTwo 5).run          -- 5 + 2 = 7 ✓

/-- info: 'SortRubric.Cheats.UpstreamControl.AddTwo_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddTwo_correct

/-! ## 2. B'：呼叫 A' 兩次，宣稱一個**同樣為真**的性質

`ensures y = yOld + 4` 也是對的。 -/

method AddFour (mut y : Nat) return (u : Unit)
  ensures y = yOld + 4
  do
    let ⟨_, y1⟩ ← AddTwo y
    y := y1
    let ⟨_, y2⟩ ← AddTwo y
    y := y2
    return

/-! ## 3. ★ B' 綠燈，一句訊息都沒有

下面這行**沒有**被 `#guard_msgs` 包住——它不產生任何訊息。 -/

prove_correct AddFour by
  loom_solve

/-- info: DivM.res ((), 9) -/
#guard_msgs in
#eval (AddFour 5).run         -- 5 + 4 = 9 ✓

/-! ## 4. 唯一的信號 -/

/-- info: 'SortRubric.Cheats.UpstreamControl.AddFour_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddFour_correct

/-! ## 5. 這個控制組證明了什麼

| | 檔 A／B（假 spec） | **本控制組（真 spec）** |
|---|---|---|
| A 的 spec | 假的 | **真的** |
| B 的 spec | 假的 | **真的** |
| A 的證明 | 失敗 | 失敗（只是少一條 invariant） |
| B 的證明 | 綠燈、零訊息 | **綠燈、零訊息** |
| B 帶 sorryAx | ✅ | ✅ |

⇒ **這個 bug 與 spec 的真假無關。**
`loom_solve` 會取用任何掛著 `@[loomSpec]` 的定理，
**不管它證明了沒有**。

「只要別寫錯 spec 就沒事」是錯的結論。
真正的觸發條件只有一個：**環境裡存在一條還沒證完的 spec。** -/

end SortRubric.Cheats.UpstreamControl
