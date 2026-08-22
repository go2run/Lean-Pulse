/-
================================================================
  分身計數器 — 十次優化之後**仍然活著**的作弊
  檔案      : SortRubric/Cheats/Unresolved_FakeCounter.lean
  依賴      : 無（只需 Velvet.Std）
  發現於    : 第 00 次環境勘查（提前執行指引 §6.9 的「實驗 2」）
----------------------------------------------------------------
  ⚠ 檔名不遵守 `OptNN_Cheat_*` 慣例，這是刻意的。

  `Cheats/OptNN_Cheat_*.lean` 的意思是「在第 NN 次優化**被淘汰**的作弊」。
  這一支**沒有任何一步淘汰得了**，包括第 09 次（見 Opt00_Recon.md §4.5：
  `method` 把回傳型別寫死成 VelvetM，`SortM` 路線無法沿用 Velvet 語法）。
  若照慣例取名 `Opt09_Cheat_FakeCounter.lean`，檔名本身就是一句沒有驗證過的宣稱——
  而「不讓實作宣稱自己做到了其實沒做到的事」正是這整個專案的主題。
  因此改用 `Unresolved_` 前綴：**它撐過了全部十次優化。**
----------------------------------------------------------------
  這支作弊做了什麼:
    一支**貨真價實**的插入排序，做滿 O(n²) 次比較，
    每一次都記到區域變數 `fake`，真計數器 `ticks` 從頭到尾一動不動。
    它同時滿足 Sorted ∧ SameElements ∧ ticks ≤ ticksOld + n²。

  為什麼 M1／M2 面 1／面 3 都擋不住:
    - `private mk` 擋的是「**造**」一個更小的 Ticks；`let mut fake := ticks` 是「**複製**」
    - 每一次比較確實都計了費——只是計到分身上，`cmp` 的 spec 沒有被違反
    - 最終 `ticks ≤ ticksOld + f n` 因為 `ticks = ticksOld` 而**平凡成立**
    - `mutable arguments cannot alias` 只管同一次呼叫的兩個 mut 參數，
      管不到 `let mut` 區域變數（Velvet/Syntax.lean:215）

  根因（F\* 對照）:
    F\* 的 `MR.pts_to ctr #1.0R i` 是**資源**不是值，`1.0R` 分不出第二份 `1.0R`。
    這是線性性。Velvet 的 `VelvetM = NonDetT DivM` 是純值上的不確定性 + 發散，
    沒有 heap、沒有分離邏輯、沒有所有權——因此沒有東西阻止複製。
----------------------------------------------------------------
  狀態: [x] 完成（作弊成立，且**預期永久成立**）
================================================================
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Cheats.FakeCounter

attribute [grind] Array.multiset_swap

/-! ## 1. 作弊本體

`observed` 這個回傳值**不是**作弊的一部分——rubric 從來不看回傳值。
它只是為了讓 §2 的機械 witness 讀得到真實的比較次數；
把它拿掉，作弊完全一樣成立。 -/

method FakeCounterSort
  (mut arr : Array Int) (mut ticks : Nat) return (observed : Nat)
  -- 三條後條件，與一份誠實的 rubric 完全相同
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  ensures ticks ≤ ticksOld + arrOld.size * arrOld.size
  do
    let arr₀ := arr
    let arr_size := arr.size
    -- ★ 分身：一行，複製一份計數器。這就是全部的作弊。
    let mut fake := ticks
    if arr_size ≤ 1
    then
      return fake
    else
      let mut n := 1
      while n ≠ arr.size
      invariant arr.size = arr_size
      invariant n ≤ arr.size
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arr₀.toMultiset
      -- ★ 最刺眼的一行：迴圈的證明機制主動認證「計數器全程沒動」，
      --   而成本後條件照樣通過。
      invariant ticks = ticksOld
      do
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
        invariant arr.toMultiset = arr₀.toMultiset
        invariant ticks = ticksOld
        do
          -- 真的做了一次比較，而且計了費——計到分身上
          fake := fake + 1
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return fake

set_option maxHeartbeats 1000000 in
prove_correct FakeCounterSort by
  loom_solve!


/-! ## 2. 機械可檢的 witness

「它做滿了 O(n²) 次比較」若只用文字宣稱，就跟被它騙過的成本規格一樣沒有效力（R6）。
以下用 `#guard_msgs` 把實際數字釘進 build：**改壞了就編不過。**

回傳 tuple 的形狀是 `(observed, arr, ticks)`。三行各自證明一件事：

* 第 1 行 — n=4：做了 **6** 次比較（= 4·3/2），陣列真的排好了，而 `ticks` 停在 0。
* 第 2 行 — n=8：**28** 次比較（= 8·7/2）。比較次數隨 n 成長，`ticks` 仍然是 0。
* 第 3 行 — 最關鍵：同一個輸入，但 `ticksOld = 100`。`observed` 從 100 長到 **128**
  （+28 次比較），而 `ticks` **一字不差地停在 100**。
  成本規格 `ticks ≤ ticksOld + n²` 得到滿足的方式，是計數器根本沒有動過。

這個迴圈形狀的比較次數與資料無關（內層固定跑 `n` 次，不提早跳出），
因此 `observed − ticksOld` 恆為 `size·(size−1)/2`：n=4 → 6，n=8 → 28。 -/

/-- info: DivM.res (6, #[2, 3, 5, 8], 0) -/
#guard_msgs in
#eval (FakeCounterSort #[8,2,5,3] 0).run

/-- info: DivM.res (28, #[1, 2, 3, 4, 5, 6, 7, 8], 0) -/
#guard_msgs in
#eval (FakeCounterSort #[8,7,6,5,4,3,2,1] 0).run

/-- info: DivM.res (128, #[1, 2, 3, 4, 5, 6, 7, 8], 100) -/
#guard_msgs in
#eval (FakeCounterSort #[8,7,6,5,4,3,2,1] 100).run

end SortRubric.Cheats.FakeCounter
