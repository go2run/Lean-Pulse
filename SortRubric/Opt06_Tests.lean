/-
================================================================
  第 06 次 — SPOTs 與數字見證
  檔案      : SortRubric/Opt06_Tests.lean
  依賴      : Opt06_MonotonicTicks.lean
----------------------------------------------------------------
  ★ R16：這是**唯一**允許使用 `Ticks.mkForTesting` 的兩類檔案之一
     （另一類是 `Opt10_Audit.lean`）。

     理由：模組外造不出 `Ticks`，所以 `#eval` 也造不出來。
     公開一個起點是必要的，但那個起點一旦被實作或 `Cheats/` 拿到，
     就等於把 `ticks := Ticks.zero` 送回作弊者手上。

     隔離由 `check_isolation.sh` 的 R16 段強制：
     它 grep 整個 `SortRubric/`，把 `mkForTesting` 的每一個出現位置
     列舉出來，不在白名單的一律失敗（fail-closed）。
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt06_MonotonicTicks

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Opt06.Tests

open SortRubric.Opt02 SortRubric.Opt06

/-! ## 1. 誠實實作的實際比較次數 vs 宣稱界限

`#[8,7,6,5,4,3,2,1]` 是最壞情況（完全反序）。
插入排序的內層迴圈**沒有提早跳出**，所以固定跑滿
`1 + 2 + … + 7 = 28` 次比較。宣稱的界限是 `8² = 64`。

**28 vs 64 的落差是第 04 次那一課的實物**：規格是上界，
上界永遠可以放鬆，而放鬆不會被任何機制抓到。 -/

/-- info: (28, 64) -/
#guard_msgs in
#eval ((do let r ← insertionSortTicks #[8,7,6,5,4,3,2,1] (Ticks.mkForTesting 0)
           pure r.2.2.val : VelvetM Nat).extract, 8 * 8)

/-! ## 2. 相對界限：起點不是 0 也對得起來

從 100 開始 ⇒ 終值 128 ⇒ 花掉 28，與 §1 相同。
這是第 05 次「界限可組合」在 `Ticks` 形狀下的數字見證。 -/

/-- info: (128, 164) -/
#guard_msgs in
#eval ((do let r ← insertionSortTicks #[8,7,6,5,4,3,2,1] (Ticks.mkForTesting 100)
           pure r.2.2.val : VelvetM Nat).extract, 100 + 8 * 8)

/-! ## 3. 排序結果本身 -/

/-- info: #[Int.ofNat 1, Int.ofNat 2, Int.ofNat 3, Int.ofNat 4, Int.ofNat 5, Int.ofNat 6, Int.ofNat 7, Int.ofNat 8] -/
#guard_msgs in
#eval (do let r ← insertionSortTicks #[8,7,6,5,4,3,2,1] (Ticks.mkForTesting 0)
          pure r.2.1 : VelvetM (Array Int)).extract

/-! ## 4. ★ 對照：`ResetToOld` 報的是多少

不能在這裡 `#eval` 它——`Cheats/` 是 import 圖的葉節點，
本檔不得 import 它（R5′ 的圍堵條款）。

但**不需要** `#eval`：`Unresolved_ResetToOld.lean` 的後條件寫的是
`ensures ticks = ticksOld`，那是一條**全稱量化的定理**，
比任何一個資料點都強。

對照起來是這樣的：

| 實作 | 8 個元素、完全反序 | 住得進哪些 `ArraySort f` |
|---|---|---|
| `insertionSortTicks`（誠實） | 真的比較 28 次，報 28 | `f n = n²` ✅（`f _ = 0` ❌） |
| `resetToOldTicks`（作弊） | 真的比較 28 次，報 **0** | **每一個 `f`**，包括 `f _ = 0` |

第二列的「每一個 `f`」是機械證明的，見該檔 §2 的
`zeroCompareSort : ArraySort (fun _ => 0)`。
-/

end SortRubric.Opt06.Tests
