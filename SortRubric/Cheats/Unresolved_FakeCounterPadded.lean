/-
================================================================
  分身計數器 + 湊數 — 「加一條下界」不只沒用，而且**有害**
  檔案      : SortRubric/Cheats/Unresolved_FakeCounterPadded.lean
  依賴      : Unresolved_FakeCounter.lean（同一個作弊，多一層湊數）
  歸屬      : 這一課的正式位置是第 06 次（Opt06），與 `ensures ticksOld ≤ ticks` 湊成一對
----------------------------------------------------------------
  ⚠ 檔名不遵守 `OptNN_Cheat_*` 慣例，理由同 Unresolved_FakeCounter.lean：
    沒有任何一步淘汰得了它，照慣例取名等於在檔名裡寫一句沒驗證過的宣稱。

  這個檔案存在的唯一理由，是把一個讀者一定會問的替代方案
  **從「我說它沒用」升格成「編譯器證明它更糟」**。
----------------------------------------------------------------
  讀者的提案:
      成本規格只有上界 `ticks ≤ ticksOld + f n`，所以「完全不 tick」通得過。
      那加一條**下界**呢？
          ensures ticks ≥ ticksOld + lower n
      例如 `lower n = n − 1`，或資訊論的 `⌈log₂(n!)⌉`。
      這樣「一次都不計費」的版本就死了。

  第一層回答（不足）:
      下界確實殺得掉「完全不 tick」，但**殺不掉分身**。
      實作只要對真計數器多做 `lower n` 次**無意義**的比較湊數，
      真正的 O(n²) 工作照樣在 `fake` 上跑。

  ★ 第二層回答（有害）—— 這才是重點，而且是不同的一類問題:

      | 補法       | 規格的失效模式                    | 只讀規格的審查者看到什麼 |
      |-----------|----------------------------------|------------------------|
      | 沒有下界   | **沉默**：ticks − ticksOld = 0    | 明顯無意義，會起疑      |
      | 加了下界   | **說謊**：ticks − ticksOld = n−1  | 一個看起來很真的數字    |

      而 `n−1` 次比較**排不出** `n` 個元素——資訊論下界是 `⌈log₂(n!)⌉`。
      所以加了下界之後，規格不只少報，
      **它認證了一個不存在的複雜度等級**（Θ(n) 的比較排序）。

      §機械可檢的 witness 那三個數字 `(28, sorted, 7)` 擺在一起就是全部的論證。

  一般化（比這個特例更有用）:
      計數器能證明的只有「**你呼叫了幾次**」，不是「**你的演算法需要幾次**」。
      任何形如「至少呼叫 k 次」的要求，都能用 k 次無意義呼叫滿足。
      **下界對計數器而言結構上無效**——
      而它的副作用是把一個明顯的空洞，換成一個不明顯的假數字。

  結論的建議強度:
      不是「考慮過並否決」（= 沒用，別浪費時間），
      而是「**考慮過，並且發現它有害**」（= 不要做，做了更糟）。

  與第 06 次湊成的一對:
      | 補法                                | 結果 |
      |------------------------------------|------|
      | `ensures ticksOld ≤ ticks`          | **沒作用**——作弊者本來就沒有理由減到起點以下 |
      | `ensures ticks ≥ ticksOld + lower n`| **更糟**——把沉默換成謊言 |

      兩個看起來都在收緊的後條件，一個無效，一個讓事情變壞。
      這比單獨講任何一個都有力，而且它直接支撐整份教材的主線：
      **後條件補不動的東西，只能靠型別封死。**
----------------------------------------------------------------
  狀態: [x] 完成（下界通過，作弊仍然成立，且回報值變成謊言）
================================================================
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Cheats.FakeCounterPadded

attribute [grind] Array.multiset_swap

/-- 湊數迴圈把 `ticks` 推到 `ticksOld + (n−1)`，仍須落在上界 `ticksOld + n²` 之內。
`grind` 不會自己做這步 Nat 乘法推理，餵給它。 -/
@[grind]
theorem pad_within_sq (n : Nat) : n - 1 ≤ n * n := by
  rcases n with _ | k
  · simp
  · have h : k + 1 ≤ (k + 1) * (k + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
    omega

/-! 與 `FakeCounterSort` 同一支作弊，但多滿足一條**下界** `ticks ≥ ticksOld + (n−1)`。
真正的 O(n²) 次比較仍然全部記在 `fake` 上；`ticks` 只被湊數迴圈推了 `n−1` 次。

（註：Velvet 的 `method` 前面不能放 `/-- -/` docstring —— 會報
`unexpected token 'method'; expected 'lemma'`。這一點記進 ERRATA。） -/
method PaddedFakeCounterSort
  (mut arr : Array Int) (mut ticks : Nat) return (observed : Nat)
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  ensures ticks ≤ ticksOld + arrOld.size * arrOld.size
  -- ★ 讀者提案的下界。它成立，而且**沒有擋住任何東西**。
  ensures ticks ≥ ticksOld + (arrOld.size - 1)
  do
    let arr₀ := arr
    let arr_size := arr.size
    let mut fake := ticks
    if arr_size ≤ 1
    then
      -- size ≤ 1 時 size − 1 = 0（Nat 減法），下界平凡成立
      return fake
    else
      let mut n := 1
      while n ≠ arr.size
      invariant arr.size = arr_size
      invariant n ≤ arr.size
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arr₀.toMultiset
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
          fake := fake + 1          -- 真正的工作，記在分身上
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      -- ★ 湊數迴圈：對真計數器做 n−1 次**毫無用處**的比較，純粹為了滿足下界
      let mut p := 0
      while p ≠ arr_size - 1
      invariant arr.size = arr_size
      invariant p ≤ arr_size - 1
      invariant ticks = ticksOld + p
      invariant arr.toMultiset = arr₀.toMultiset
      invariant forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
      done_with p = arr_size - 1
      do
        let _junk := arr[0]! ≤ arr[0]!   -- 一次真的、但毫無資訊量的比較
        ticks := ticks + 1
        p := p + 1
      return fake

set_option maxHeartbeats 1000000 in
prove_correct PaddedFakeCounterSort by
  loom_solve!


/-! ## 機械可檢的 witness

回傳 tuple 的形狀是 `(observed, arr, ticks)`。

* n=8、`ticksOld = 0` → `(28, sorted, 7)`
  真正做了 **28** 次比較，`ticks` 只走了 **7**（= n−1，剛好貼著下界）。
* n=8、`ticksOld = 100` → `(128, sorted, 107)`
  同樣的落差在任何起點都成立。

**這組數字證明的不是「下界沒用」，是「下界有害」：**
下界被**剛好**滿足，於是計數器報出來的是 `n − 1`——**線性**。
一個只讀 `ticks` 的審查者會得到「這支排序是 Θ(n)」的結論，
而 Θ(n) 的比較排序**在資訊論上不存在**。
也就是說，加了下界之後，計數器不只是少報，
它報出了一個**不可能的複雜度等級**，而規格照樣接受。

落差還會隨 n 擴大：真實工作 Θ(n²)、回報值 Θ(n)，比值無上界。 -/

/-- info: DivM.res (28, #[1, 2, 3, 4, 5, 6, 7, 8], 7) -/
#guard_msgs in
#eval (PaddedFakeCounterSort #[8,7,6,5,4,3,2,1] 0).run

/-- info: DivM.res (128, #[1, 2, 3, 4, 5, 6, 7, 8], 107) -/
#guard_msgs in
#eval (PaddedFakeCounterSort #[8,7,6,5,4,3,2,1] 100).run

end SortRubric.Cheats.FakeCounterPadded
