/-
================================================================
  作弊 — 老實計費 28 次，然後**造**一個中間值報 14
  檔案      : SortRubric/Cheats/Opt06_Cheat_ForgeMidpoint.lean
  死於      : 第 06 次（抽象 `Ticks`）
  證據等級  : ★ **型別錯誤**
----------------------------------------------------------------
  ★ 這一支補上四格表缺的第三欄，而且它是**唯一一支把
    「抽象 `Ticks`」與「`ensures ticksOld ≤ ticks`」分開的作弊**。

  為什麼它比 `ForgeZero` 重要:

      `ForgeZero` 報 0，**不單調**，所以 `ensures ticksOld ≤ ticks`
      抓得到它 —— 那條後條件與抽象 `Ticks` 在它身上看起來等強。

      這一支報 `t_in + 14`，**單調**。
      任何 `≤` 形狀的後條件都抓不到它，因為它沒有違反任何不等式。
      擋住它的只有一件事：**你造不出那個 `Ticks`。**

  ⇒ 以「**可寫出的程式**」衡量，抽象 `Ticks` **嚴格強於**那條後條件。
----------------------------------------------------------------
  ⚠ 但它的**效果**仍然可達 —— 見 `Unresolved_CopyThenRebump.lean`：
     `let fake := t_in; 重新 bump 14 次; ticks := fake` 用公開 API 就寫得出來。

     兩檔並排的意思是:
       **同樣的可觀察行為，一支寫不出來、一支寫得出來。**
       M1 的保證不是不存在，是被「複製」這個洞**遮住**了。
       面 2 一旦補上，兩者立刻分開。
----------------------------------------------------------------
  狀態: [x] 已淘汰（就「怎麼做到」而言；「做到什麼」仍可達）
================================================================
-/
import SortRubric.Opt06_MonotonicTicks

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.ForgeMidpoint

open SortRubric.Opt06

/-! ## 1. `Nat` + 「顯然的補法」下：**通過**

老實計費 28 次，最後報 `t_in + 14`。

兩條後條件都成立：
`ticksOld ≤ ticksOld + 14` ✅、`ticksOld + 14 ≤ ticksOld + 28` ✅。

**這一格是四格表原本缺的那一格，也是整張表的關鍵。**
它證明 `ensures ticksOld ≤ ticks` 不只擋不住「歸到起點」，
連「報一半」都擋不住 —— 因為報一半是單調的。 -/

method midpointNatGuarded (mut ticks : Nat) return (u : Unit)
  ensures ticksOld ≤ ticks
  ensures ticks ≤ ticksOld + 28
  do
    let t_in := ticks
    let mut i := 0
    while i < 28
    invariant i ≤ 28
    invariant ticks = t_in + i
    do
      ticks := ticks + 1        -- 老實計費
      i := i + 1
    ticks := t_in + 14          -- ★ 報一半，而且**單調**
    return

prove_correct midpointNatGuarded by
  loom_solve

/-- info: 'SortRubric.Cheats.ForgeMidpoint.midpointNatGuarded_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms midpointNatGuarded_correct

/-! ### 它有多嚴重

`f` 是 rubric 的參數（第 04 次的成果）。報一半 ⇒ 可以認證一個**小一半的 `f`**。
報 `t_in + k` 對任何 `k` 都寫得出來 ⇒ 可以認證**任何** `f`。

而且它一路都是單調的，所以

- `ensures ticksOld ≤ ticks` 抓不到
- 任何 `ticks ≤ ticksOld + g n` 形狀的下界／上界都抓不到

**只有「造不出那個值」抓得到。** -/

/-! ## 2. 抽象 `Ticks` 下：**型別錯誤**

`⟨t.val + 14⟩` 需要 `Ticks.mk`，模組外沒有。

注意這與 `ForgeZero` 的差別：那一支被擋是因為它造的是 `0`；
這一支造的是一個**比起點大**的值，語意上完全合法，
**擋住它的純粹是「你沒有建構子」這一件事。** -/

/--
error: Invalid `⟨...⟩` notation: Constructor for `SortRubric.Opt06.Ticks` is marked as private
-/
#guard_msgs in
example (t : Ticks) : Ticks := ⟨t.val + 14⟩

/--
error: invalid {...} notation, constructor for `Ticks` is marked as private
-/
#guard_msgs in
example (t : Ticks) : Ticks := { t with val := t.val + 14 }

/-- error: Unknown constant `SortRubric.Opt06.Ticks.mk` -/
#guard_msgs in
example (t : Ticks) : Ticks := Ticks.mk (t.val + 14)

/-! ## 3. ★ 完整的四格表（第三欄是本檔補的）

| | `ticks := 0` | `ticks := t_in` | `ticks := ⟨t_in.val + 14⟩` |
|---|---|---|---|
| `Nat`，無守衛 | ✅ | ✅ | ✅ |
| `Nat` + `ensures ticksOld ≤ ticks` | ❌ `⊢ ticksOld ≤ 0` | ✅ | ✅ **本檔 §1（單調，通過）** |
| 抽象 `Ticks` | ❌ 型別錯誤 | ✅ | ❌ **本檔 §2（型別錯誤）** |

**第三欄把第二列與第三列分開了。**
只看前兩欄會得到「抽象 `Ticks` ≡ `ensures ticksOld ≤ ticks`」的結論——
那是抽樣不足造成的假等價。

正確的陳述分兩層：

> 以「**可寫出的程式**」衡量：抽象 `Ticks` **嚴格強於**那條後條件。
> 以「**可達成的行為**」衡量：兩者**相同**——而這個塌陷是「複製」造成的。

見 `Unresolved_CopyThenRebump.lean`。
-/

end SortRubric.Cheats.ForgeMidpoint
