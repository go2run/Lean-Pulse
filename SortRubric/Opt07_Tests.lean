/-
================================================================
  第 07 次 — SPOTs 與數字見證
  檔案      : SortRubric/Opt07_Tests.lean
  依賴      : Opt07_InstrOrder.lean
  R16       : 本檔屬 `*_Tests.lean`，允許使用 `Ticks.mkForTesting`
================================================================
-/
import SortRubric.Opt07_InstrOrder

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Opt07.Tests

open SortRubric.Opt02 SortRubric.Opt06 SortRubric.Opt07

/-! ## 1. 計費現在是比較器的副產品

`insertionSortInstr` 的 body 裡**一行 `ticks.bump` 都沒有**。
28 這個數字完全來自 `honestInt.cmp` 的 `charged` 那一項。

與第 06 次同樣是 28——形狀換了，行為沒換。 -/

/-- info: (28, 64) -/
#guard_msgs in
#eval ((do let r ← insertionSortInstr honestInt #[8,7,6,5,4,3,2,1] (Ticks.mkForTesting 0)
           pure r.2.2.val : VelvetM Nat).extract, 8 * 8)

/-- info: #[Int.ofNat 1, Int.ofNat 2, Int.ofNat 3, Int.ofNat 4, Int.ofNat 5, Int.ofNat 6, Int.ofNat 7, Int.ofNat 8] -/
#guard_msgs in
#eval (do let r ← insertionSortInstr honestInt #[8,7,6,5,4,3,2,1] (Ticks.mkForTesting 0)
          pure r.2.1 : VelvetM (Array Int)).extract

/-! ## 2. 相對界限在新形狀下仍然對得起來 -/

/-- info: (128, 164) -/
#guard_msgs in
#eval ((do let r ← insertionSortInstr honestInt #[8,7,6,5,4,3,2,1] (Ticks.mkForTesting 100)
           pure r.2.2.val : VelvetM Nat).extract, 100 + 8 * 8)

/-! ## 3. 有重複元素也對

`cmp x y` 為真代表 `x ≤ y`，所以相等時也會交換。
對有序性與 multiset 都無害，只是多做幾次無謂的搬移——
**比較次數不受影響**（內層迴圈固定跑滿）。 -/

/-- info: (6, #[Int.ofNat 2, Int.ofNat 2, Int.ofNat 5, Int.ofNat 5]) -/
#guard_msgs in
#eval (do let r ← insertionSortInstr honestInt #[5,2,5,2] (Ticks.mkForTesting 0)
          pure (r.2.2.val, r.2.1) : VelvetM (Nat × Array Int)).extract

/-! ## 4. ★ 對照表：三支實作，同一個 rubric

不能在這裡 `#eval` 那兩支作弊——`Cheats/` 是 import 圖的葉節點。
但它們的後條件都寫 `ensures ticks = ticksOld`，那是**全稱量化的定理**，
比 `#eval` 強。

| 實作 | 真的比較幾次 | 經過 `iord` 嗎 | 報幾次 | 住得進哪些 `ArraySort f` |
|---|---|---|---|---|
| `insertionSortInstr`（誠實） | 28 | ✅ | **28** | `f n = n²` ✅／`f _ = 0` ❌ |
| `Unresolved_BypassWithInt` | 28 | ❌ 直接 `x < y` | **0** | **每一個 `f`** |
| `Unresolved_DiscardCmpTicks` | 28 | ✅ **而且用了答案** | **0** | **每一個 `f`** |

第三列是第 07 次最誠實的一行：**比較器完全誠實，帳還是可以不算在自己頭上。**
-/

end SortRubric.Opt07.Tests
