/-
  LeanPulse.BubbleSort — 對應 Pulse
  `share/pulse/examples/PulseExample.BubbleSort.fst`

  原檔是「完全驗證」的泛型 bubble sort，同時證明兩件事：
    1. sorted        —— 輸出已排序
    2. permutation   —— 輸出是輸入的排列（元素不增不減）

  Pulse 的 permutation 那半靠一整套手寫 lemma（swap_is_permutation、
  compose_permutations、lemma_swap_is_two_upds…）與 reveal_opaque 完成——
  那是分離邏輯 + 手動證明的地盤，SMT 無法自動想出。

  本翻譯（第一版）**只證 sorted**，把 permutation 留待後續：
    Pulse:  A.pts_to a s   ↦  Velvet: (mut a : Array Int) + aOld
    sorted s               ↦  ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!

  演算法（與原檔同構）：
    外圈 i 從 size-1 遞減——把當前未排序區間 [0, i] 的最大值冒泡到位置 i，
    使後綴 [i+1, size) 逐步變成「已排序且不小於前面所有元素」。
    內圈 j 從 0 掃到 i——相鄰比較，較大者往右換，最終最大值落在位置 i。

  兩條核心不變量（對照 Pulse 的 suffix_sorted / prefix_le_suffix）：
    * 後綴已排序：i < p ≤ q < size → a[p] ≤ a[q]
    * 前綴 ≤ 後綴：p ≤ i < q < size → a[p] ≤ a[q]
  內圈額外維持「a[j] 是 [0, j] 的最大值」（對照 is_max_up_to）。

  註：Velvet 自帶的 InsertionSort 用 `a.toMultiset = aOld.toMultiset`
  + `attribute [grind] Array.multiset_swap` 就能讓 grind 自動證出
  permutation——所以補上 permutation 其實成本不高（見檔尾）。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-
  `swap! a[j]! a[j+1]!` 展開成兩層 `Array.set!`，於是每條牽涉 `a[_]!` 的
  不變量在 swap 分支都變成「雙層 set! 的讀取」。Velvet 內建的
  `Array.get_set_c` 只剝一層，grind 無法自己把兩層疊起來推理（把
  `loom.solver.grind.splits` 開到 60 也一樣失敗），所以這裡直接給它
  一條 swap 的讀取規則：三個分支——被換到的兩格與其餘不動的格子。
-/
@[grind =]
theorem Array.getElem!_swap! [Inhabited α] (a : Array α) (j k p : Nat)
    (hp : p < a.size) :
    ((a.set! j a[k]!).set! k a[j]!)[p]! =
      if p = k then a[j]! else if p = j then a[k]! else a[p]! := by
  have hsize : (a.set! j a[k]!).size = a.size := by simp
  rw [Array.get_set_c p k a[j]! (a.set! j a[k]!) (by omega)]
  by_cases h : p = k
  · simp [h]
  · simp only [h, if_false]
    rw [Array.get_set_c p j a[k]! a hp]

method bubbleSort (mut a : Array Int) return (u : Unit)
    require 1 ≤ a.size
    ensures a.size = aOld.size
    ensures ∀ i j, i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!
    do
    let mut i := a.size - 1
    while 0 < i
      invariant a.size = aOld.size -- [ * * * * * * * * ]
      invariant i < a.size         -- [       i|  ∀p≤∀q ]
      invariant ∀ p q, i < p ∧ p ≤ q ∧ q < a.size → a[p]! ≤ a[q]!   -- 後綴已排序
                                   -- [ * * * * * * * * ]
                                   -- [   ∀p  i|  ∀q    ]
      invariant ∀ p q, p ≤ i ∧ i < q ∧ q < a.size → a[p]! ≤ a[q]!   -- 前綴 ≤ 後綴
      done_with i = 0
      do
      let mut j := 0
      while j < i
        invariant a.size = aOld.size
        invariant i < a.size
        invariant j ≤ i
        invariant ∀ p q, i < p ∧ p ≤ q ∧ q < a.size → a[p]! ≤ a[q]!
        invariant ∀ p q, p ≤ i ∧ i < q ∧ q < a.size → a[p]! ≤ a[q]!
                                   -- [ * * * * * * * * ]
                                   -- [   p      |j     ]
                                   -- [|p=j             ]
        invariant ∀ p, p ≤ j → a[p]! ≤ a[j]!                         -- a[j] 是 [0,j] 的最大值
        done_with j = i
        do
        if a[j]! > a[j + 1]! then 
          swap! a[j]! a[j + 1]!
        j := j + 1
      i := i - 1
    return

set_option maxHeartbeats 4000000 in
prove_correct bubbleSort by
  loom_solve
