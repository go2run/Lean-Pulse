/-
================================================================
  第 02 次優化 — `+ SameElements`
  檔案      : SortRubric/Opt02_SameElements.lean
  依賴      : Opt01_Sorted.lean
----------------------------------------------------------------
  本次堵的洞: 「最後給我一個有序陣列」→「而且它是原元素的重排」
  對照作弊  : Cheats/Opt02_Cheat_AllZeros.lean
              Cheats/Opt02_Cheat_DropElements.lean
              Cheats/Opt02_Cheat_MinOnly.lean
  驗證結果  : 見 SortRubric/Opt02_Notes.md（含逐字錯誤訊息）
----------------------------------------------------------------
  仍然活著的洞:
    - 每支 method 的簽章、前條件各寫各的        → 第 03 次處理
    - 完全不談成本（比較次數）                  → 第 04 次起處理
    - 計數器歸零                                → 第 06 次處理
    - 比較器不誠實 / 實作繞過比較器             → 第 07、08 次處理
    - 計數器分身                                → 第 09 次（已知受限，見 README）
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import Velvet.Std
import Mathlib.Tactic.IntervalCases

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Opt02

attribute [grind] Array.multiset_swap

/-! ## 1. 規格

`Sorted` 沿用第 01 次（不含裝飾用的 `0 ≤ i`）。 -/

@[grind] def Sorted (a : Array Int) : Prop :=
  ∀ i j, i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!

/-- 「是原元素的重排」。用 multiset 相等表達，
不需要 `DecidableEq`（`Array.toMultiset` 零 typeclass 需求，`Velvet/Std.lean:103`）。 -/
@[grind] def SameElements (before after : Array Int) : Prop :=
  before.toMultiset = after.toMultiset

/-- ★ 本次的規格。**採人類閱讀順序**：先講結果有序，再講元素沒變。
（Velvet 的 `ensures` 是反序合取，因此這裡與 `_correct` 定理之間有一個形狀落差；
落差的實測成本見 §4 與 `Opt02_Notes.md` §3。） -/
def SortSpec (before after : Array Int) : Prop :=
  Sorted after ∧ SameElements before after

/-! ## 2. 一支真的排序

**命名**：這是**插入排序**，不是 bubble sort。指引 §6.2 寫的是「一支 bubbleSort」，
但把插入排序叫成別的名字，正是第 10 次 D1 軸要抓的那種事
（F\* 原文：*"producing an implementation of insertion sort and claiming that it is quicksort"*）。
在一份以「不讓實作宣稱自己做到了其實沒做到的事」為主題的專案裡，
連函式名字都不該說謊。 -/

method insertionSort (mut arr : Array Int) return (u : Unit)
  ensures Sorted arr
  ensures SameElements arrOld arr
  do
    let arr₀ := arr
    let arr_size := arr.size
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ arr.size
      -- Structural：index 還合法嗎？size 變了嗎？
      invariant arr.size = arr_size
      invariant n ≤ arr.size
      -- Ordering：哪一區已經排好？
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
      -- Preservation：元素還在嗎？
      invariant arr.toMultiset = arr₀.toMultiset
      do
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
        invariant arr.toMultiset = arr₀.toMultiset
        do
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 1000000 in
prove_correct insertionSort by
  loom_solve!

/-! ## 3. 驗收：規格擋得住三支作弊，也放得過正確答案

三支作弊各自在 `Cheats/Opt02_Cheat_*.lean`（含逐字錯誤訊息 + 機械反證）。
這裡放對照組。 -/

theorem correct_answer_passes : SortSpec #[8,2,5,3] #[2,3,5,8] := by
  constructor
  · intro i j ⟨hij, hj⟩
    simp at hj
    interval_cases j <;> interval_cases i <;> simp
  · unfold SameElements Array.toMultiset; decide

/-! ## 4. ★ 決定 (二)：橋接

`SortSpec` 採**人類順序**（`Sorted ∧ SameElements`），而 Velvet 把 `ensures` **反序**合取，
所以 `insertionSort_correct` 的後條件是 `SameElements ∧ Sorted`。

落差**只有合取順序**——兩邊的 `Sorted`、`SameElements` 完全一致，
連 `x.2` 的結構 eta 都自動對上（實測見 `Opt02_Notes.md` §3）。

橋接用 Loom 的 **consequence rule**（`Loom/MonadAlgebras/WP/Basic.lean:54`）：

```lean
lemma triple_cons (x : m α) {pre pre' : l} {post post' : α -> l} :
  pre' ≤ pre -> (∀ y, post y ≤ post' y) -> triple pre x post -> triple pre' x post'
```

`l = Prop` 時 `≤` 就是蘊涵，所以後條件的重排寫成一個 `fun _ h => ⟨…⟩` 即可。

**為什麼選它而不是 `funext`/`propext`/`▸`**：兩者在兩項時都是 1 行，
但第 04 次加上 `ticks ≤ ticksOld + f n` 之後落差會變成**三項的重排**，
`funext` 版當場失效（`and_comm` 不夠，還要 `and_assoc`，且 `▸` 的 motive 推導會斷）。
`triple_cons` 版**形狀不變、位置不變，只換投影**。實測對照見 `Opt02_Notes.md` §3.3。 -/

open PartialCorrectness PartialCorrectness.DemonicChoice in
/-- 人類順序的 `SortSpec` 與 Velvet 產生的 `_correct` 之間的橋。
這就是第 03 次 `SortImpl.spec` 欄位要放的東西。 -/
theorem insertionSort_sortSpec :
    ∀ a, triple True (insertionSort a) (fun r => SortSpec a r.2) :=
  fun a => triple_cons _ le_rfl (fun _ h => ⟨h.2, h.1⟩) (insertionSort_correct a)

/-- info: 'SortRubric.Opt02.insertionSort_sortSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insertionSort_sortSpec

end SortRubric.Opt02
