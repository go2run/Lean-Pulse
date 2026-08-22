/-
================================================================
  第 03 次優化 — 統一成 interface
  檔案      : SortRubric/Opt03_Interface.lean
  依賴      : Opt02_SameElements.lean
----------------------------------------------------------------
  本次堵的洞: 各支排序各寫各的簽章與前條件——審查者每一份都得從頭讀
  對照作弊  : Cheats/Opt03_Cheat_ExtraPrecondition.lean
  驗證結果  : 見 SortRubric/Opt03_Notes.md
----------------------------------------------------------------
  仍然活著的洞:
    - 完全不談成本（比較次數）        → 第 04 次處理
    - 遞迴呼叫的界限疊不起來          → 第 05 次處理
    - 計數器歸零                      → 第 06 次處理
    - 比較器不誠實 / 實作繞過比較器   → 第 07、08 次處理
    - 計數器分身                      → 第 09 次（已知受限）
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt02_SameElements

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Opt03

open SortRubric.Opt02

/-! ## 1. 兩個層次的差別

```
Level A：共用 predicate          ← 第 02 次已經做到
   插入排序 ─┐
   氣泡排序 ─┼── 都 ensures Sorted / SameElements
   合併排序 ─┘
   但每支 method 的簽章、前條件仍可各寫各的

Level B：共用完整 contract       ← 第 03 次要做到
   同樣的參數、同樣的 requires、同樣的 ensures
```

F\* 原文抱怨的正是 Level A 不夠：AutoCLRS 的四個演算法已經共用
`sorted`/`permutation`，但 heapsort 多一條 `SZ.fits` 前條件、只證 `sorted_upto s n`、
還多一句「後半段不變」——**每一份都得從頭讀**。

## 2. Velvet 的困難，與這裡採用的解法

Velvet 的規格**不在** method 的 Lean function type 裡：`method` 展開成
`def … : VelvetM τ`（`Velvet/Syntax.lean:343`），規格另外存成 `<name>_correct` 定理。
所以要得到 F\* 式的 first-class rubric，**必須把 implementation 與它的 `triple` evidence
額外綁在一起**。

至少四種等價寫法：`structure` / `class` / 函式 + proof 參數 / Σ-bundle。
本檔選 **`structure`**，因為教學最直觀——**但這不是型別論上唯一的路**。
（`class` 的差別只在能不能靠 instance resolution 自動找到實作；
對「審查者只讀規格」這個目的沒有影響。）

兩個 API 細節（都來自第 00 次勘查，見 `Opt00_GUIDE_ERRATA.md`）：

1. `mut` 參數會併進回傳 tuple，所以 `sort` 的型別是 `Array Int → VelvetM (Unit × Array Int)`，
   不是指引草稿寫的 `VelvetM (Array Int)`
2. `[part| …]` 記號**有歧義**（Loom 與 Velvet 各定義一個同名記號），
   在 `structure` 欄位裡必須改用顯式 `open … in`
-/

open PartialCorrectness PartialCorrectness.DemonicChoice in
/-- ★ 第 03 次的 rubric：實作 + 證據，綁成一個值。

**審查者只需要讀這 3 行。** 交件者必須交出能塞進這個型別的東西；
型別檢查器接受它，就等於通過驗收。

命名的演進路徑（先記著，免得後面混淆）：
`SortImpl`（第 03 次）→ `ArraySort (f : Nat → Nat)`（第 04 次加上界限索引）
→ 之後每一步都是在這同一個 structure 上加參數與收緊 spec，不再改名。 -/
structure SortImpl where
  sort : Array Int → VelvetM (Unit × Array Int)
  spec : ∀ a, triple True (sort a) (fun r => SortSpec a r.2)

/-! ## 3. 把第 02 次的實作裝進去

橋接就是第 02 次量出來的那一行（`triple_cons`）。 -/

def insertionSortImpl : SortImpl where
  sort := insertionSort
  spec := insertionSort_sortSpec

/-- info: 'SortRubric.Opt03.insertionSortImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insertionSortImpl

/-! ## 4. `sort` 欄位的型別**不具鑑別力**——鑑別力全在 `spec`

一個把陣列輾平成 0 的程式，型別與 `SortImpl.sort` **一字不差**： -/

/-- 一個顯然不是排序的程式。 -/
def notASort : Array Int → VelvetM (Unit × Array Int) :=
  fun a => pure ((), Array.replicate a.size 0)

/-- 它的型別與 `SortImpl.sort` 完全相同——`SortImpl.mk` 的第一個欄位收得下它。 -/
example : ∀ (f : Array Int → VelvetM (Unit × Array Int)), f = f := fun _ => rfl
example : Array Int → VelvetM (Unit × Array Int) := notASort
example : Array Int → VelvetM (Unit × Array Int) := insertionSort

/-! 所以第 03 次買到的東西**不是**「型別擋掉了作弊」——
`sort` 欄位對 `notASort` 跟對 `insertionSort` 一視同仁。

買到的是：**`spec` 欄位與 `sort` 欄位被綁在同一個值裡，交件者不能只交前者。**
`notASort` 進不來，不是因為它的型別不對，是因為**沒有人能造出它的 `spec`**
（第 02 次的 `Cheats/Opt02_Cheat_AllZeros.lean` 已經把那個失敗釘進 build 了）。

而 `Cheats/Opt03_Cheat_ExtraPrecondition.lean` 展示了另一半：
一支**真的會排序、`prove_correct` 完全綠燈**的實作，只因為多寫了一行 `require`，
就連 `SortImpl` 的門都進不去——**那是型別錯誤，不是證明失敗**。

兩者合起來才是 Level B：
**不只共用 predicate（Level A），而是共用整份 contract。** -/

end SortRubric.Opt03
