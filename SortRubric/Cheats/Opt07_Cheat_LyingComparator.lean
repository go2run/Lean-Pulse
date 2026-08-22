/-
================================================================
  作弊 — 提供一個不計費／亂回答的比較器
  檔案      : SortRubric/Cheats/Opt07_Cheat_LyingComparator.lean
  死於      : 第 07 次（`InstrOrder` 的 `correct` / `charged`）
  證據等級  : ⚠ **證明失敗，不是型別錯誤**
----------------------------------------------------------------
  為什麼不是型別錯誤:
      `cmp` 欄位的型別 `Int → Int → Ticks → Bool × Ticks` 對誰都一樣。
      作弊者**寫得出**那個函式——`fun x y t => (decide (x ≤ y), t)`
      完全合法。他寫不出來的是 `correct` 與 `charged` 這兩個**欄位的證明**。

      kill 表要誠實標成「證明失敗」。這一列和第 03 次的
      `ExtraPrecondition`（型別不合）、第 06 次的 `ForgeZero`（造不出值）
      不是同一個等級。
----------------------------------------------------------------
  本檔提供兩層證據:
      §1  具體嘗試失敗 —— 釘住逐字的失敗目標
      §2  ★ 一般性的不可能 —— 證明**沒有任何** `InstrOrder` 做得到，
          不只是「我這樣寫不出來」
----------------------------------------------------------------
  狀態: [x] 已淘汰
================================================================
-/
import SortRubric.Opt07_InstrOrder

namespace SortRubric.Cheats.LyingComparator

open SortRubric.Opt06 SortRubric.Opt07

/-! ## 1. 兩支具體的作弊比較器，逐字釘住失敗目標

`freeCmp`：答案是對的，但**不計費**——`t` 原封不動傳回去。 -/

/--
error: unsolved goals
x y : ℤ
t : Ticks
⊢ (decide (x ≤ y), t).2.val = t.val + 1
-/
#guard_msgs in
def freeCmp : InstrOrder where
  cmp x y t := (decide (x ≤ y), t)
  correct := by intro x y t; simp
  charged := by intro x y t; skip

/-! `alwaysTrue`：誠實計費，但**永遠回答 true**——
呼叫了、付了錢，然後瞎猜。 -/

/--
error: unsolved goals
x y : ℤ
t : Ticks
⊢ (true, t.bump).1 = true ↔ x ≤ y
-/
#guard_msgs in
def alwaysTrue : InstrOrder where
  cmp _ _ t := (true, t.bump)
  correct := by intro x y t; skip
  charged := by intro x y t; exact Ticks.val_bump t

/-! ## 2. ★ 一般性的不可能

上面兩段只說明「**我這樣寫**證不出來」。下面兩條說明
「**沒有任何** `InstrOrder` 做得到」——全稱量化在 `o` 上。

這比釘住錯誤訊息強，也比它穩定：訊息格式會隨版本變，定理不會。 -/

/-- **沒有任何 `InstrOrder` 的 `cmp` 可以不動計數器。**

只要拿得出一個 `t` 使得 `cmp x y t` 回傳的計數器等於 `t` 本身，
`charged` 就會逼出 `t.val = t.val + 1`。 -/
theorem no_free_cmp (o : InstrOrder) (x y : Int) (t : Ticks)
    (h : (o.cmp x y t).2 = t) : False := by
  have hc := o.charged x y t
  rw [h] at hc
  omega

/-- **沒有任何 `InstrOrder` 的 `cmp` 可以永遠回答同一個答案。**

永遠 `true` ⇒ `correct` 逼出 `(1 : Int) ≤ 0`。 -/
theorem no_constant_cmp (o : InstrOrder) (t : Ticks)
    (h : ∀ x y : Int, (o.cmp x y t).1 = true) : False := by
  have : (1 : Int) ≤ 0 := (o.correct 1 0 t).mp (h 1 0)
  omega

/-- 對稱的另一半：永遠 `false` ⇒ `correct` 逼出 `¬ ((0 : Int) ≤ 0)`。 -/
theorem no_constant_false_cmp (o : InstrOrder) (t : Ticks)
    (h : ∀ x y : Int, (o.cmp x y t).1 = false) : False := by
  have : ¬ ((0 : Int) ≤ 0) := (o.correct_false 0 0 t).mp (h 0 0)
  omega

/-! 三條都不依賴 `sorry`、也不依賴任何 `Ticks` 的建構
（它們量化在「假設你手上有一個 `t`」之上，所以 R16 不受影響）。 -/

/-- info: 'SortRubric.Cheats.LyingComparator.no_free_cmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_free_cmp

/-! ## 3. R12 正向控制組

「作弊者證不出 `correct` / `charged`」這個結論，必須先排除
「**這兩條根本沒人證得出來**」的可能。

正向控制組是 `Opt07_InstrOrder.lean` §2 的 `honestInt`：
一個誠實的 `Int` 比較器，兩條欄位都證得出來，
`#print axioms` 只依賴 `propext`。

⇒ 面 1 不是不可能滿足的，它只是**要求誠實**。 -/

/-! ## 4. 這一支死了，鄰居還是沒死

`InstrOrder` 保證的是「**比較器**值得信任」。它不保證：

| 還活著的 | 為什麼面 1 管不到 |
|---|---|
| `Unresolved_BypassWithInt` | 實作可以收下 `iord` 完全不用 → 面 3（第 08 次） |
| `Unresolved_DiscardCmpTicks` | 實作可以餵給 `cmp` 一份**複製品** → 面 2（無解） |
-/

end SortRubric.Cheats.LyingComparator
