/-
================================================================
  作弊 — 無視呼叫端的起點，直接把計數器設成 0
  檔案      : SortRubric/Cheats/Opt06_Cheat_ForgeZero.lean
  死於      : 第 06 次（抽象 `Ticks`）
  證據等級  : ★ **型別錯誤**（kill 表的第一列「寫不出來」）
----------------------------------------------------------------
  作弊的內容:
      呼叫端從 `ticksOld` 開始算帳，作弊者在最後一行寫 `ticks := 0`。
      相對界限 `ticks ≤ ticksOld + f n` 對 `ticks = 0` 恆成立
      （Nat 減不到負數），所以第 05 次擋不住。

  死法:
      第 06 次之後 `ticks : Ticks`，而 `Ticks` 的建構子是 `private`。
      模組外**造不出**任何 `Ticks` 值——四條路徑全部是型別錯誤。

  ⚠ 這一支不是 `ResetToOld`。`ResetToOld` **還活著**，
     見 `Unresolved_ResetToOld.lean`。兩者的差別只有一個字：
     這一支要「造」一個計數器，那一支只要「複製」一個。
----------------------------------------------------------------
  狀態: [x] 已淘汰
================================================================
-/
import SortRubric.Opt06_MonotonicTicks

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.ForgeZero

open SortRubric.Opt06

/-! ## 1. 第 05 次的形狀下：**通過**（這是它作為作弊的資格）

計數器是裸 `Nat`，最後一行歸零。相對界限恆成立。
`prove_correct` 綠燈，`#print axioms` 乾淨。 -/

method forgeZeroNat (mut ticks : Nat) return (u : Unit)
  ensures ticks ≤ ticksOld + 10
  do
    ticks := ticks + 1
    ticks := 0            -- ★ 無視呼叫端已經花掉的帳
    return

prove_correct forgeZeroNat by
  loom_solve

/-- info: 'SortRubric.Cheats.ForgeZero.forgeZeroNat_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forgeZeroNat_correct

/-! ## 2. 「顯然的補法」：加一條 `ensures ticksOld ≤ ticks`

**這條擋得住這一支。** 但它擋不住 `ResetToOld`——見另一檔。
指引 §5.1.1 說這條後條件「從來不是在擋歸零」，這裡的實測結果是：
**它確實擋得住歸零（歸到起點以下），只是擋不住歸到起點。** -/

method forgeZeroNatGuarded (mut ticks : Nat) return (u : Unit)
  ensures ticksOld ≤ ticks
  ensures ticks ≤ ticksOld + 10
  do
    ticks := ticks + 1
    ticks := 0
    return

/--
error: unsolved goals
case «ensures_2: ticksOld ≤ ticks»
ticksOld : ℕ
⊢ ticksOld ≤ 0
-/
#guard_msgs in
prove_correct forgeZeroNatGuarded by loom_solve

/-! ## 3. ★ 第 06 次的形狀下：**四條偽造路徑全部是型別錯誤**

這是本專案最高的證據等級——不是「證不出來」，是「寫不出來」。
編譯器在 elaboration 階段就拒絕，連 `prove_correct` 都跑不到。

四條路徑對應 `Opt06_Ticks.lean` 檔頭禁止清單的前三條，加上直呼建構子。 -/

/--
error: Invalid `⟨...⟩` notation: Constructor for `SortRubric.Opt06.Ticks` is marked as private
-/
#guard_msgs in
example : Ticks := ⟨0⟩

/--
error: invalid {...} notation, constructor for `Ticks` is marked as private
-/
#guard_msgs in
example : Ticks := { val := 0 }

/--
error: invalid {...} notation, constructor for `Ticks` is marked as private
-/
#guard_msgs in
example (t : Ticks) : Ticks := { t with val := 0 }

/--
error: Unknown constant `SortRubric.Opt06.Ticks.mk`
-/
#guard_msgs in
example : Ticks := Ticks.mk 0

/-! ## 4. 第四條偽造路徑：typeclass 洩漏

`Opt06_Ticks.lean` 一個 `deriving` 都沒有。這裡把三個危險的
typeclass 逐一試出來——**每一個都會造出 `Ticks` 值，
而且都不會有任何「你破壞了 M1」的警告**。 -/

/-- error: failed to synthesize
  Inhabited Ticks

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
example : Ticks := default

/-- error: failed to synthesize
  OfNat Ticks 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Ticks
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
example : Ticks := 0

/-! ## 5. 這一支死了，但它的鄰居沒死

| 作弊 | 要做的動作 | 第 06 次 |
|---|---|---|
| `ForgeZero`（本檔） | **造**一個 `Ticks` | ❌ 型別錯誤 |
| `ResetToOld` | **複製**一個 `Ticks` | ✅ 還活著 |
| `FakeCounter` | **複製**一個 `Ticks` | ✅ 還活著 |

`private mk` 管「造」，管不到「複製」。
-/

end SortRubric.Cheats.ForgeZero
