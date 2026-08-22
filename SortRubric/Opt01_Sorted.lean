/-
================================================================
  第 01 次優化 — 只有 `Sorted`
  檔案      : SortRubric/Opt01_Sorted.lean
  依賴      : 無（只需 Velvet.Std）
----------------------------------------------------------------
  本次堵的洞: 無。這一步**故意留洞**，建立最直覺的起點。
  對照作弊  : 本檔 §3 的 `ZeroFill`——它通過，而且應該通過
  驗證結果  : 見 SortRubric/Opt01_Notes.md
----------------------------------------------------------------
  仍然活著的洞:
    - 全部填 0                              → 第 02 次處理
    - 刪掉元素                              → 第 02 次處理
    - 只留最小值                            → 第 02 次處理
    - 不談成本（比較次數）                  → 第 04 次起處理
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import Velvet.Std
import Mathlib.Tactic.IntervalCases

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Opt01

/-! ## 1. 規格

全域版的有序性：任兩個索引 `i ≤ j` 都滿足 `a[i]! ≤ a[j]!`。

**這裡刻意不寫成 `0 ≤ i ∧ i ≤ j ∧ j < a.size`。**
`0 ≤ i` 對 `Nat` 恆真，是純裝飾。`Sorted` 是整個專案最常被讀的定義，
它應該讀起來就是那句數學敘述。proof-friendly 的冗餘屬於 invariant，不屬於 top-level spec
（見 Opt02 的 invariant 三分類）。 -/
def Sorted (a : Array Int) : Prop :=
  ∀ i j, i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!

/-! ## 2. 驗收：兩個都要通得過

第二個通得過，**正是這一步的重點**。 -/

/-- 真的排好序的陣列滿足 `Sorted`。 -/
example : Sorted #[2,3,5,8] := by
  intro i j ⟨hij, hj⟩
  simp at hj
  interval_cases j <;> interval_cases i <;> simp

/-- ★ 全部是 0 的陣列**也**滿足 `Sorted`——而它跟輸入毫無關係。 -/
example : Sorted #[0,0,0,0] := by
  intro i j ⟨hij, hj⟩
  simp at hj
  interval_cases j <;> interval_cases i <;> simp

/-! ## 3. 把洞變成一支真的程式

`example` 只說明「這個 `Prop` 證得出來」。
下面這支 Velvet method 更難看：它**通過了 `ensures Sorted a`**，
而它做的事是把整個陣列輾平成 0。 -/

/-- `Array.replicate n 0` 的每一格都是 0——界外也是，因為 `default : Int` 就是 0。 -/
theorem replicate_zero_get (n i : Nat) : (Array.replicate n (0:Int))[i]! = 0 := by
  by_cases h : i < n
  · rw [getElem!_pos (h := by simpa using h)]; simp
  · rw [getElem!_neg (h := by simpa using h)]; rfl

@[grind]
theorem sorted_replicate_zero (n : Nat) : Sorted (Array.replicate n (0:Int)) := by
  intro i j _
  simp [replicate_zero_get]

method ZeroFill (mut a : Array Int) return (u : Unit)
  ensures Sorted a
  do
    a := Array.replicate a.size 0
    return

prove_correct ZeroFill by
  loom_solve

/-! ### 這一步的重點，用一行輸出說完

`#[8,2,5,3]` 進去，`#[0,0,0,0]` 出來——輸入的四個元素一個都不剩，
而 `ZeroFill_correct` 是一條**真的定理**，沒有 `sorry`。 -/

/-- info: DivM.res ((), #[0, 0, 0, 0]) -/
#guard_msgs in
#eval (ZeroFill #[8,2,5,3]).run

/-- info: 'SortRubric.Opt01.ZeroFill_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZeroFill_correct

/-! `ensures Sorted a` 不代表「把原陣列排序」，
只代表「最後給我一個有序陣列」。**規格從來沒有提到輸入。**
→ 第 02 次補上 `SameElements`。 -/

end SortRubric.Opt01
