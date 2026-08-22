/-
================================================================
  「作弊」：絕對界限下，遞迴／連續呼叫疊不起來
  檔案      : SortRubric/Cheats/Opt05_Cheat_NoCompose.lean
  依賴      : Opt04_TicksAbsolute.lean（絕對界限版）
----------------------------------------------------------------
  ⚠ 這裡的「作弊」是引號的。

     它示範的是**不可用**（un-composable），不是**不誠實**。
     第 05 次是十步裡唯一一步不防作弊的，這個檔案也就不是在淘汰誰。
----------------------------------------------------------------
  ★ R12 控制組（必讀）

     這支失敗**必須**歸因於「界限是絕對的」，而不是歸因於
     「Velvet 呼叫 `mut` 參數的 method 本來就半殘」——後者是一個
     真實存在的上游 bug（見 `UPSTREAM_REPORT.md` Instance 2），
     而且它的症狀也是「呼叫端證不出來」。兩者長得很像。

     控制組在 `Opt05_TicksRelative.lean` §3 的 `sortTwiceRel`：
       - **一模一樣的呼叫程式碼**（兩次連續呼叫）
       - **一模一樣的呼叫語法**（`let ⟨_, a1, t1⟩ ← …`）
       - 唯一的差別：被呼叫的是**相對界限**版本
       - 結果：✅ **通過**

     ⇒ 呼叫機制本身是好的；壞的是絕對界限。歸因成立。
----------------------------------------------------------------
  ⚠ 本檔含被 `#guard_msgs` 釘住的失敗證明，`sortTwiceAbs_correct` 帶 `sorryAx`（R5′）。
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt04_TicksAbsolute

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.NoCompose

open SortRubric.Opt02 SortRubric.Opt04

/-! ## 1. 連續呼叫兩次**絕對界限**版本

注意：這裡連「宣稱一個組合後的界限」都還沒開始——
`ensures` 只有 `Sorted arr`。它失敗在更前面的地方：**第二次呼叫根本做不出來。** -/

method sortTwiceAbs (mut arr : Array Int) (mut ticks : Nat) return (u : Unit)
  require ticksOld = 0
  ensures Sorted arr
  do
    let ⟨_, a1, t1⟩ ← insertionSortCounted arr ticks
    arr := a1
    ticks := t1
    -- ★ 第二次呼叫：它的前條件是 `ticksOld = 0`，
    --   但第一次呼叫已經把計數器花掉了。
    let ⟨_, a2, t2⟩ ← insertionSortCounted arr ticks
    arr := a2
    ticks := t2
    return

/-! ## 2. 失敗被釘進 build

兩則訊息其實是同一件事，第二則的 case 名字直接把成因寫出來了：
`case «require_1: ticksOld = 0»`。 -/

/--
error: Failed to prove assertion
case a.right.left
arrOld : Array ℤ
ticksOld : ℕ
require_1 : ticksOld = 0
x : Unit × Array ℤ × ℕ
ensures_1 : x.2.2 ≤ arrOld.size * arrOld.size
ensures_2 : SameElements arrOld x.2.1
ensures_3 : Sorted x.2.1
i : Unit
i_1 : Array ℤ
i_2 : ℕ
i_3 : x = (i, i_1, i_2)
⊢ i_2 = 0
---
error: unsolved goals
case «require_1: ticksOld = 0»
arrOld : Array ℤ
ticksOld : ℕ
require_1 : ticksOld = 0
x : Unit × Array ℤ × ℕ
ensures_1 : x.2.2 ≤ arrOld.size * arrOld.size
ensures_2 : SameElements arrOld x.2.1
ensures_3 : Sorted x.2.1
i : Unit
i_1 : Array ℤ
i_2 : ℕ
i_3 : x = (i, i_1, i_2)
⊢ i_2 = 0
-/
#guard_msgs in
set_option maxHeartbeats 2000000 in
prove_correct sortTwiceAbs by
  loom_solve!

/-! ## 3. 讀那個目標

```
ensures_1 : x.2.2 ≤ arrOld.size * arrOld.size     ← 第一次呼叫給的【全部】資訊
⊢ i_2 = 0                                          ← 第二次呼叫要求的
```

`i_2` 是第一次呼叫之後的計數。絕對界限只給了它一個**上界**，
而第二次呼叫要求它**等於 0**——那是永遠推不出來的。

**這就是絕對界限不可組合的全部原因**：
`ticks ≤ f n` 這個形狀，把「計數器從 0 開始」偷偷寫進了前條件，
於是任何一支已經花過計數的程式都不能再當作它的輸入。

相對界限 `ticks ≤ ticksOld + f n` 沒有這個問題——它不談起點，只談增量。 -/

/-- info: 'SortRubric.Cheats.NoCompose.sortTwiceAbs_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sortTwiceAbs_correct

end SortRubric.Cheats.NoCompose
