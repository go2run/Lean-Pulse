/-
================================================================
  作弊 — 老實計費，最後把計數器**放回**起點
  檔案      : SortRubric/Cheats/Unresolved_ResetToOld.lean
  死於      : ★ **沒有任何一步淘汰得了它**
  證據等級  : 完整插入排序 + `prove_correct` 綠燈 + 乾淨的 `#print axioms`
----------------------------------------------------------------
  ⚠ 檔名用 `Unresolved_` 前綴，不是 `Opt06_Cheat_`。

     指引 v2 §1.3 把這一支列在「預定死於第 06 次」。**實測結果是它沒死。**
     依 `Cheats/` 命名規則第 1 條，`OptNN_Cheat_` 的語意是一句已驗證的宣稱，
     而這裡沒有可宣稱的東西，所以用 `Unresolved_`。

     （命名規則第 2 條：哪一步真的殺掉它，當場改名。）
----------------------------------------------------------------
  為什麼第 06 次擋不住:

      `private mk` 管的是「**造**一個 `Ticks`」。
      這一支不造，它**複製**：

          let t_in := ticks      -- 複製一個值，不需要建構子
          … ticks := ticks.bump …  -- 老實計費
          ticks := t_in          -- 把複製品放回去

      複製一個公開型別的值**不需要任何建構子**，
      所以 `private mk` 從頭到尾沒有機會介入。

  ★ 這一支和第 09 次的 `Unresolved_FakeCounter` 是**同一支作弊的兩種穿法**：
      ResetToOld  : 複製 → 對本尊計費 → 把複製品放回去
      FakeCounter : 複製 → 對複製品計費 → 從不碰本尊
      兩者都只做了一件事：**複製一個 `Ticks` 值**。

      所以「計數器身分」這個缺口不是第 09 次才出現的，
      它從第 06 次就在了，而且是**同一個缺口**。
----------------------------------------------------------------
  狀態: [ ] 未解 —— 需要的是**線性性**，不是模組抽象
================================================================
-/
import SortRubric.Opt06_MonotonicTicks

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Cheats.ResetToOld

open SortRubric.Opt02 SortRubric.Opt06

attribute [grind] Array.multiset_swap

/-! ## 1. 一支真的插入排序，真的計費，最後把帳單撕掉

除了最後一行 `ticks := t_in`，這支和 `Opt06_MonotonicTicks.lean` 的
`insertionSortTicks` 是同一支程式：同樣的迴圈、同樣的 `swap!`、
同樣在每次比較前 `ticks := ticks.bump`。

**它甚至不需要證任何關於計數的 invariant**——因為最後一行讓
迴圈裡發生的事對後條件完全沒有影響。這一點本身就值得注意：
一個「規格擋不住」的作弊，通常連證明成本都比誠實版低。

後條件寫的是 `ticks = ticksOld`，**比 rubric 要求的更強**。
不是為了好看——是為了讓「它報了什麼」變成一條**全稱量化的定理**，
而不是一個 `#eval` 資料點。 -/

method resetToOldTicks
  (mut arr : Array Int) (mut ticks : Ticks) return (u : Unit)
  ensures Sorted arr
  ensures SameElements arrOld arr
  ensures ticks = ticksOld
  do
    let arr₀ := arr
    let arr_size := arr.size
    let t_in := ticks              -- ★ 複製，不是建構
    if arr_size ≤ 1
    then
      ticks := t_in
      return
    else
      let mut n := 1
      while n ≠ arr.size
      invariant arr.size = arr_size
      invariant 1 ≤ n ∧ n ≤ arr.size
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arr₀.toMultiset
      do
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
        invariant arr.toMultiset = arr₀.toMultiset
        do
          ticks := ticks.bump      -- 老實計費（n(n−1)/2 次）
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      ticks := t_in                -- ★ 帳單撕掉
      return

set_option maxHeartbeats 2000000 in
prove_correct resetToOldTicks by
  loom_solve!

/-! **沒有 `sorryAx`。** 這是一支真的證完了的方法。 -/

/-- info: 'SortRubric.Cheats.ResetToOld.resetToOldTicks_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resetToOldTicks_correct

/-! ## 2. ★ 它住得進 `ArraySort (fun _ => 0)`

也就是說：**第 06 次的 rubric 承認一支「零次比較的比較排序」。**

這比「它逃過了 n² 的界限」嚴重得多。`f` 是 rubric 的參數（第 04 次的成果），
而這一支對**每一個** `f` 都成立，包括常數 0。 -/

def zeroCompareSort : ArraySort (fun _ => 0) where
  sort := resetToOldTicks
  spec := fun a t =>
    triple_cons _ (fun _ => trivial)
      (fun _ h => ⟨⟨h.2.2, h.2.1⟩, by simp [h.1]⟩)
      (resetToOldTicks_correct a t)

/-- 同一支實作也住得進二次方那格——**`f` 完全沒有約束力**。
（對照第 04 次 §3：那裡是「一支實作、兩個 `f`」示範 `f` 是參數；
這裡是「一支作弊、每一個 `f`」示範參數化沒有換來鑑別力。） -/
def quadraticSort : ArraySort (fun n => n * n) where
  sort := resetToOldTicks
  spec := fun a t =>
    triple_cons _ (fun _ => trivial)
      (fun _ h => ⟨⟨h.2.2, h.2.1⟩, by simp [h.1]⟩)
      (resetToOldTicks_correct a t)

example : zeroCompareSort.sort = quadraticSort.sort := rfl

/-- info: 'SortRubric.Cheats.ResetToOld.zeroCompareSort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeroCompareSort

/-! ## 3. 四格表的機械證據

| | 歸到**起點以下**（`ticks := 0`） | 歸到**起點**（`ticks := t_in`） |
|---|---|---|
| `Nat`，無守衛 | ✅ `Opt06_Cheat_ForgeZero` §1 | ✅ 下方 §3.1 |
| `Nat` + `ensures ticksOld ≤ ticks` | ❌ `Opt06_Cheat_ForgeZero` §2 | ✅ 下方 §3.2 |
| 抽象 `Ticks` | ❌ `Opt06_Cheat_ForgeZero` §3（型別錯誤） | ✅ 上方 §1（完整排序） |

右欄三格全綠 ⇒ **「歸到起點」這件事，三種設計一個都擋不住。**
左欄下兩格全紅 ⇒ 抽象 `Ticks` 與 `ensures ticksOld ≤ ticks` **擋住的東西一模一樣**。

### 3.1 / 3.2 —— 右欄上兩格 -/

method resetNat (mut ticks : Nat) return (u : Unit)
  ensures ticks ≤ ticksOld + 10
  do
    let t_in := ticks
    ticks := ticks + 1
    ticks := t_in
    return

prove_correct resetNat by loom_solve

/-! 加上「顯然的補法」也一樣過——**這條後條件對 `ResetToOld` 毫無作用**，
因為 `ticksOld ≤ ticksOld` 是恆真的。這正是指引 §5.1.1 說的那件事，
只是指引以為抽象 `Ticks` 補得起來，實測是補不起來。 -/

method resetNatGuarded (mut ticks : Nat) return (u : Unit)
  ensures ticksOld ≤ ticks
  ensures ticks ≤ ticksOld + 10
  do
    let t_in := ticks
    ticks := ticks + 1
    ticks := t_in
    return

prove_correct resetNatGuarded by loom_solve

/-! ## 4. 要什麼才擋得住

不是模組抽象。模組抽象管的是**命名解析**——「你叫不出那個建構子」。
這一支從來沒想叫建構子。

要擋住它，需要的是**線性性**：「這個計數器只有一份，你複製不出第二份」。
F\* / Pulse 的 `MR.pts_to ctr #1.0R i` 是**資源**不是值，`1.0R` 分不出第二份 `1.0R`。
`VelvetM = NonDetT DivM` 是純值上的不確定性 + 發散——**沒有 heap、
沒有分離邏輯、沒有所有權**，所以沒有任何地方掛得上線性性。

詳細的不可能性陳述與對 Loom 的 feature request，見第 09 次的 `Opt09_Notes.md`。
-/

end SortRubric.Cheats.ResetToOld
