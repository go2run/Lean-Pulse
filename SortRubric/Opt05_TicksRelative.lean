/-
================================================================
  第 05 次優化 — 改成相對界限（★ 本步**不防作弊**）
  檔案      : SortRubric/Opt05_TicksRelative.lean
  依賴      : Opt04_TicksAbsolute.lean
----------------------------------------------------------------
  ⚠ 這是十步裡**唯一一步不防作弊的**。

     它防的是「**不可用**」（遞迴／連續呼叫的界限疊不起來），
     不是「**不誠實**」。混在裡面不標會誤導讀者。

     第 04 次能通過的所有作弊，第 05 次**一個都沒淘汰**。
----------------------------------------------------------------
  改了什麼:
      ✗ 絕對   ensures ticks ≤ f arrOld.size          （＋ require ticksOld = 0）
      ✓ 相對   ensures ticks ≤ ticksOld + f arrOld.size（無 require）

  對照 F* 的形狀：`ticks <= i + f (Seq.length s)`
----------------------------------------------------------------
  副作用（重要，這一步同時定案）:
      `ticksOld` 只有在計數器是 `mut` 參數時才存在。
      ⇒ **計數器用 `mut` 參數傳，不是 tuple 回傳。**
----------------------------------------------------------------
  仍然活著的洞（與第 04 次完全相同，一個都沒少）:
    - 老實計費，最後 `ticks := ticksOld`   → 第 06 次
    - 做滿比較但比較器不計費               → 第 07 次
    - 實作繞過比較器直接 `x < y`           → 第 08 次
    - 計數器分身                           → 第 09 次（已知無解）
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt04_TicksAbsolute

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Opt05

open SortRubric.Opt02 SortRubric.Opt04

attribute [grind] Array.multiset_swap

/-! ## 1. 相對界限版

與第 04 次的 `insertionSortCounted` 只差兩處：
拿掉 `require ticksOld = 0`，後條件改成 `ticks ≤ ticksOld + …`。

內層仍然用**線性內層／非線性外層**的技術（見 `Opt04_Notes.md` §6.2）：
`let t0 := ticks` 之後 `invariant ticks = t0 + (n - mind)` 完全沒有乘法。
這裡多綁一個 `t_in := ticks` 當作整支方法的起點。 -/

method insertionSortRel
  (mut arr : Array Int) (mut ticks : Nat) return (u : Unit)
  ensures arr.size = arrOld.size        -- proof-friendly redundancy，給呼叫端用
  ensures Sorted arr
  ensures SameElements arrOld arr
  ensures ticks ≤ ticksOld + arrOld.size * arrOld.size
  do
    let arr₀ := arr
    let arr_size := arr.size
    let t_in := ticks
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ arr.size
      invariant arr.size = arr_size
      invariant 1 ≤ n ∧ n ≤ arr.size
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arr₀.toMultiset
      invariant ticks ≤ t_in + n * n
      do
        let t0 := ticks
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
        invariant arr.toMultiset = arr₀.toMultiset
        invariant ticks = t0 + (n - mind)
        invariant t0 ≤ t_in + n * n
        do
          ticks := ticks + 1
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 2000000 in
prove_correct insertionSortRel by
  loom_solve!

/-! ## 2. rubric：起點不再被釘死

與第 04 次的 `ArraySort` 唯一的差別——`spec` 多量化一個起始計數 `t`，
界限寫成 `t + f a.size`。 -/

open PartialCorrectness PartialCorrectness.DemonicChoice in
structure ArraySort (f : Nat → Nat) where
  sort : Array Int → Nat → VelvetM (Unit × Array Int × Nat)
  spec : ∀ a t, triple True (sort a t)
                 (fun r => SortSpec a r.2.1 ∧ r.2.2 ≤ t + f a.size)

/-- 橋接仍然是那一行 `triple_cons`，第三次只換投影。 -/
def insertionSortRelImpl : ArraySort (fun n => n * n) where
  sort := insertionSortRel
  spec := fun a t =>
    triple_cons _ (fun _ => trivial) (fun _ h => ⟨⟨h.2.2.1, h.2.1⟩, h.1⟩)
      (insertionSortRel_correct a t)

/-- info: 'SortRubric.Opt05.insertionSortRelImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insertionSortRelImpl

/-! ## 3. ★ 這一步買到的東西：界限疊得起來

連續呼叫兩次，成本界限**加得起來**。

**這同時是 R12 的控制組**——`Cheats/Opt05_Cheat_NoCompose.lean` 裡有
**一模一樣的呼叫程式碼、一模一樣的呼叫語法**，只是被呼叫的是絕對界限版本，
那一支證不出來。兩者並排，失敗才能歸因於「界限的形式」，
而不是歸因於「Velvet 的 `mut` method 呼叫本來就半殘」（那是另一個真實存在的 bug，
見 `UPSTREAM_REPORT.md` Instance 2）。 -/

method sortTwiceRel (mut arr : Array Int) (mut ticks : Nat) return (u : Unit)
  ensures Sorted arr
  ensures ticks ≤ ticksOld + 2 * (arrOld.size * arrOld.size)
  do
    let ⟨_, a1, t1⟩ ← insertionSortRel arr ticks
    arr := a1
    ticks := t1
    let ⟨_, a2, t2⟩ ← insertionSortRel arr ticks
    arr := a2
    ticks := t2
    return

set_option maxHeartbeats 2000000 in
prove_correct sortTwiceRel by
  loom_solve!

/-- info: 'SortRubric.Opt05.sortTwiceRel_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sortTwiceRel_correct

/-! 排兩次的比較次數是 **28 + 28 = 56**——第二次雖然輸入已經排好，
內層迴圈仍然固定跑滿 `n` 次（沒有提早跳出），所以資料的有序性一點都沒省到。
界限是 2 × 64 = 128。

（`(實際, 宣稱)` 的落差在這裡是 56 vs 128，比單次的 28 vs 64 更鬆——
**組合會讓鬆度累積**。這是第 04 次 §5 那一課的延伸。） -/

/-- info: (56, 128) -/
#guard_msgs in
#eval ((sortTwiceRel #[8,7,6,5,4,3,2,1] 0).extract.2.2, 2 * (8 * 8))

end SortRubric.Opt05
