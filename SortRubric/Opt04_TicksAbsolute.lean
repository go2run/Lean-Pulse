/-
================================================================
  第 04 次優化 — 加計數器 + 絕對界限；`f` 升格成 rubric 參數
  檔案      : SortRubric/Opt04_TicksAbsolute.lean
  依賴      : Opt03_Interface.lean
----------------------------------------------------------------
  本次做兩件事:
    (a) 引入計數器 `ticks`，後條件加上 `ticks ≤ f n`
    (b) ★ 把界限 `f : Nat → Nat` **升格成 rubric 的參數**
        （對應 F* 的 `class array_sort (f: nat -> nat)`）

  為什麼 (b) 一定要在這一步做、不能延後:
    `f` 一旦寫死在後條件裡，第 05 次的相對界限、以及之後每一次優化
    都要重改這個 structure 的形狀，而每改一次就要付
    「所有既有 instance 重新適配」的成本。
    F* 那邊的 git 歷史顯示 `array_sort` 被 retrofit 三次，
    每次都連帶三個 instance 的適配 commit。
----------------------------------------------------------------
  本次堵的洞:
    - bogosort（隨機打亂到排好為止）—— 證不出任何界限
    - 「換一個複雜度等級就得換一份規格」—— 由 (b) 解決
  淘汰不了（要明寫，因為它們是後面幾步存在的理由）:
    - 做滿比較但一次都不 tick → `ticks = 0 ≤ f n` ✓ 通過  → 第 07 次
    - 老實計費，最後 `ticks := 0`                        → 第 06 次
    - 分身計數器                                          → 第 09 次（已知無解）
----------------------------------------------------------------
  ⚠ 本次只承諾目標 (i)：`f` 是活的參數。(ii)(iii) 見 Opt04_Notes.md §5
----------------------------------------------------------------
  狀態: [x] 完成（目標 (i)）
================================================================
-/
import SortRubric.Opt03_Interface

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Opt04

open SortRubric.Opt02 SortRubric.Opt03

attribute [grind] Array.multiset_swap

/-! ## 1. 會計費的插入排序

`ticks` 是第二個 `mut` 參數，所以回傳型別變成 `Unit × Array Int × Nat`。

`require ticksOld = 0` 是**絕對界限**的必然結果：後條件寫的是 `ticks ≤ f n`，
沒有提到起點，所以起點必須被釘死。
**第 05 次會拿掉這一行**——它正是「遞迴呼叫的界限疊不起來」的成因。 -/

method insertionSortCounted
  (mut arr : Array Int) (mut ticks : Nat) return (u : Unit)
  require ticksOld = 0
  ensures Sorted arr
  ensures SameElements arrOld arr
  ensures ticks ≤ arrOld.size * arrOld.size
  do
    let arr₀ := arr
    let arr_size := arr.size
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
      invariant ticks ≤ n * n
      do
        -- ★ 把內層的計數做成【線性】：只跟 t0 與 mind 有關，沒有乘法。
        --   直接寫 `2 * ticks = n * (n-1)` 會讓 grind 的預算爆掉，
        --   連早期 return 分支那種平凡目標都證不出來。見 Opt04_Notes.md §6.1
        let t0 := ticks
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
        invariant arr.toMultiset = arr₀.toMultiset
        invariant ticks = t0 + (n - mind)
        invariant t0 ≤ n * n
        do
          ticks := ticks + 1              -- ★ 每一次比較計一次費
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 2000000 in
prove_correct insertionSortCounted by
  loom_solve!

/-! ## 2. ★ rubric：`f` 是參數，不是寫死的常數

對照第 03 次的 `SortImpl`——形狀一樣，只是多了一個索引 `f` 與一條成本後條件。

命名的演進路徑（第 03 次已預告）：
`SortImpl` → **`ArraySort (f : Nat → Nat)`** → 之後每一步都在這個 structure 上
加參數與收緊 spec，不再改名。 -/

open PartialCorrectness PartialCorrectness.DemonicChoice in
/-- 排序 rubric，**依複雜度界限 `f` 索引**。

審查者要讀的仍然只有這幾行；`f` 換掉，型別就換掉，但**規格的形狀不變**。 -/
structure ArraySort (f : Nat → Nat) where
  sort : Array Int → Nat → VelvetM (Unit × Array Int × Nat)
  spec : ∀ a, triple True (sort a 0)
                (fun r => SortSpec a r.2.1 ∧ r.2.2 ≤ f a.size)

/-! ## 3. 目標 (i)：同一支實作，兩個不同的 `f`

橋接還是那一行 `triple_cons`——**形狀不變、位置不變，只換投影**。
第 02 次是 `⟨h.2, h.1⟩`（兩項），這裡變成三項： -/

/-- 緊一點的界限。 -/
def insertionSortQuadratic : ArraySort (fun n => n * n) where
  sort := insertionSortCounted
  spec := fun a =>
    triple_cons _ (fun _ => rfl) (fun _ h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩)
      (insertionSortCounted_correct a 0)

/-- 鬆一點的界限。**同一支實作**，只是換一個 `f`。 -/
def insertionSortLoose : ArraySort (fun n => n * n + n) where
  sort := insertionSortCounted
  spec := fun a =>
    triple_cons _ (fun _ => rfl) (fun _ h => ⟨⟨h.2.2, h.2.1⟩, le_trans h.1 (Nat.le_add_right _ _)⟩)
      (insertionSortCounted_correct a 0)

/-! ## 4. 兩個 instance 的型別**確實不同**，而實作**確實相同**

這就是「`f` 是活的參數」的機械證據。 -/

example : ArraySort (fun n => n * n)     := insertionSortQuadratic
example : ArraySort (fun n => n * n + n) := insertionSortLoose
example : insertionSortQuadratic.sort = insertionSortLoose.sort := rfl

/-- info: 'SortRubric.Opt04.insertionSortQuadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insertionSortQuadratic

/-- info: 'SortRubric.Opt04.insertionSortLoose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insertionSortLoose

/-! ## 5. ★ 界限有多鬆：`(實際, 宣稱)` 並排

`(u, arr, ticks)`——n=8 逆序真的做了 28 次比較（= 8·7/2）。 -/

/-- info: DivM.res ((), #[1, 2, 3, 4, 5, 6, 7, 8], 28) -/
#guard_msgs in
#eval (insertionSortCounted #[8,7,6,5,4,3,2,1] 0).run

/-! 而我們宣稱的界限是 `f(8) = 8 * 8 = 64`。並排看： -/

/-- info: (28, 64) -/
#guard_msgs in
#eval ((insertionSortCounted #[8,7,6,5,4,3,2,1] 0).extract.2.2, (fun n => n * n) 8)

/-! **rubric 接受了一個 2.3 倍鬆的界限，而且什麼都沒察覺。**

這不是缺陷報告，是**保證強度分級表的實物**——
那張表裡「`f` 真的是那個複雜度等級嗎 → **人**」那一列，證據就是這兩個數字。

成本軸的完整一課（另一半在第 06 次）：

| 方向 | 規格能做什麼 | 誰負責 |
|---|---|---|
| **上界太鬆** | **照收，毫無反應（64 vs 28）** | **人** |
| 下界 | 加了**更糟**——把沉默換成假數字（見 `Cheats/Unresolved_FakeCounterPadded.lean`） | 不能加 |
| 「等於真實比較次數」 | **寫不出來**——那個量不在 Lean 的語意裡 | — |

三個方向都堵死，正是為什麼後面幾步不再補後條件，改用型別封路。 -/

end SortRubric.Opt04
