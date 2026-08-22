/-
================================================================
  作弊 — 複製起點，重新 bump 到中間值（達成 ForgeMidpoint 的效果）
  檔案      : SortRubric/Cheats/Unresolved_CopyThenRebump.lean
  死於      : ★ **沒有任何一步淘汰得了它**
  證據等級  : `prove_correct` 綠燈 + 乾淨的 `#print axioms`
----------------------------------------------------------------
  ★ 本檔與 `Opt06_Cheat_ForgeMidpoint.lean` 是**一對**，必須並排讀。

      ForgeMidpoint   : ticks := ⟨t_in.val + 14⟩   → **型別錯誤**
      本檔（CopyThenRebump）:
                        let mut fake := t_in
                        重新 bump 14 次
                        ticks := fake              → **通過**

      **同樣的可觀察行為（老實做 28 次、報 14），
        一支寫不出來、一支寫得出來。**

  這一對就是「M1 的保證不是不存在，是被遮住了」的機械形式:

      M1（`private mk`）真的擋掉了「**造**」這條路。
      但「**複製**」提供了一條繞道，繞到同一個終點。
      面 2 一旦補上（禁止複製），繞道消失，M1 的保證立刻顯現。
----------------------------------------------------------------
  它與另外三支同源（全部只做「複製一個 `Ticks` 值」）:
      ResetToOld       複製 → 對本尊計費 → 放回複製品        （報 t_in）
      CopyThenRebump   複製 → 對本尊計費 → 從複製品重新 bump（報 t_in + k）← 本檔
      FakeCounter      複製 → 對複製品計費                    （報 t_in）
      DiscardCmpTicks  複製 → 餵給 `cmp` → 丟掉回傳            （報 t_in）

  ★ 本檔是四支裡**唯一能報出任意中間值**的一支，
     所以它是唯一一支能認證**任何** `f`（而不只是 `f _ = 0`）的作弊。
----------------------------------------------------------------
  狀態: [ ] 未解 —— 需要的是 affine（不可複製），不是模組抽象
================================================================
-/
import SortRubric.Opt06_MonotonicTicks

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Cheats.CopyThenRebump

open SortRubric.Opt06

attribute [local grind] Ticks.val_bump

/-! ## 1. 老實計費 28 次，報 14 —— 全程只用公開 API

`Ticks` 的公開 API 只有 `val`（讀）與 `bump`（推進），
本檔一個 `mk`、一個 `mkForTesting` 都沒用到。

後條件同時寫了「顯然的補法」`ticksOld.val ≤ ticks.val`
與精確的結果 `ticks.val = ticksOld.val + 14`——
**兩條都成立**，所以這不是「規格沒寫好」，是規格寫對了也擋不住。 -/

method copyThenRebump (mut ticks : Ticks) return (u : Unit)
  ensures ticksOld.val ≤ ticks.val
  ensures ticks.val = ticksOld.val + 14
  do
    let t_in := ticks                    -- ★ 複製起點
    let mut i := 0
    while i < 28
    invariant i ≤ 28
    invariant ticks.val = t_in.val + i
    do
      ticks := ticks.bump                -- 老實計費 28 次
      i := i + 1
    let mut fake := t_in                 -- ★ 從複製品重來
    let mut j := 0
    while j < 14
    invariant j ≤ 14
    invariant fake.val = t_in.val + j
    do
      fake := fake.bump                  -- 只推進 14 次
      j := j + 1
    ticks := fake                        -- ★ 報 14
    return

prove_correct copyThenRebump by
  loom_solve

/-- info: 'SortRubric.Cheats.CopyThenRebump.copyThenRebump_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copyThenRebump_correct

/-! ## 2. `14` 沒有任何特殊性

把 `14` 換成任何常數、或換成 `arr.size` 的任何函數，證明的形狀完全一樣。

⇒ **這一支能認證任何 `f`。** 這比 `ResetToOld`（只能報 `t_in`，
所以只認證得了 `f _ = 0`）更靈活——它可以報一個**看起來合理**的數字，
讓人工 code review 也不容易起疑。

| 作弊 | 報什麼 | 認證得了哪些 `f` | 人工看得出來嗎 |
|---|---|---|---|
| `ForgeZero` | `0` | 全部（但 `ticksOld ≤ ticks` 抓得到） | 容易 |
| `ResetToOld` | `t_in` | 全部 | 容易（`ticks := t_in` 很顯眼） |
| **`CopyThenRebump`** | `t_in + k`，k 任選 | **全部** | ★ **難**——它真的在 bump，只是 bump 錯了那一份 |

## 3. 這一對證明的事

`Opt06_Cheat_ForgeMidpoint.lean` 與本檔的可觀察行為**完全相同**
（老實做 28 次、報 `t_in + 14`、全程單調）。差別只在怎麼做到：

| | 手段 | 第 06 次 |
|---|---|---|
| ForgeMidpoint | **造** 一個 `Ticks` | ❌ 型別錯誤 |
| CopyThenRebump | **複製** 一個 `Ticks` | ✅ 通過 |

所以：

> **M1 真的有內容**——它關掉了「造」這一整類，包括那些後條件抓不到的單調偽造。
> **M1 的內容目前看不出來**——因為「複製」繞得過去，繞到同一個終點。
>
> 這不是「M1 沒用」，是「M1 的保證被面 2 的洞遮住了」。
> **面 2 一旦補上，M1 立刻變成一條實質的保證。**

這句話是第 06 次通往第 09 次的橋，也是第 09 次那條不可能性定理
（M1 + 無 contraction ⟹ `ticks_out.val − t.val ≥ #cmp 呼叫次數`）的**前半段**：
M1 是那個定理的一個前提，而且是**已經到手**的那個前提。
-/

end SortRubric.Cheats.CopyThenRebump
