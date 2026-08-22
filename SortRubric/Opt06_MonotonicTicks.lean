/-
================================================================
  第 06 次優化 — M1：計數器換成抽象型別 `Ticks`
  檔案      : SortRubric/Opt06_MonotonicTicks.lean
  依賴      : Opt05b_Composition.lean, Opt06_Ticks.lean
----------------------------------------------------------------
  這一步淘汰的作弊:
      「無視呼叫端的起點，直接把計數器設成 0」
      （`Cheats/Opt06_Cheat_ForgeZero.lean` —— ★ **型別錯誤**，
        kill 表的第一列「寫不出來」而不是「證不出來」）

  ★★ 這一步**沒有**淘汰指引預期的那一支:
      「老實計費，最後 `ticks := ticksOld`」（`ResetToOld`）
      **仍然活著**，見 `Cheats/Unresolved_ResetToOld.lean`。

      原因一句話：**`ResetToOld` 不需要建構一個 `Ticks`，
      它只需要複製一個。** `let t_in := ticks; … ; ticks := t_in`
      從頭到尾沒碰過 `Ticks.mk`。

      這同時說明 `ResetToOld` 與第 09 次的 `FakeCounter` 是**同一支作弊
      的兩種穿法**——一個複製後放回去，一個複製後拿去記帳。
      所以「計數器身分」這個缺口不是第 09 次才出現的，它從第 06 次
      就在了。詳見 `Opt06_Notes.md` §3。
----------------------------------------------------------------
  仍然活著的洞:
    - 老實計費，最後 `ticks := ticksOld`   → ★ **無解**（第 09 次已知擋不住）
    - 做滿比較但比較器不計費               → 第 07 次
    - 實作繞過比較器直接 `x < y`           → 第 08 次
    - 計數器分身                           → ★ **無解**（與第一項同源）
----------------------------------------------------------------
  狀態: [x] 完成（結論與指引預期不同，已記入 Opt00_GUIDE_ERRATA §G）
================================================================
-/
import SortRubric.Opt05b_Composition
import SortRubric.Opt06_Ticks

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Opt06

open SortRubric.Opt02

attribute [grind] Array.multiset_swap

/-! `Ticks` 是 structure，`loom_solve` 對它沒有原生支援，
每一條關於 `.val` 的算術都要餵 `val_bump`。

★ 用 **`local`**：這條屬性**不會外洩給 import 這個模組的人**。
第 04 次的 `tick_step` 事故（一條*正確*的引理讓三步前的平凡目標失敗）
就是全域屬性造成的；`local` 從結構上消掉那一整類風險，
因此依 P1 不需要進 `AttributeBudget.md`。 -/
attribute [local grind] Ticks.val_bump

/-! ## 1. 遷移後的插入排序

與第 05 次的 `insertionSortRel` 逐字比較，只有四處不同：

| 第 05 次 | 第 06 次 |
|---|---|
| `(mut ticks : Nat)` | `(mut ticks : Ticks)` |
| `let t_in := ticks` | `let t_in := ticks.val` ← 存**數字**，不是存計數器 |
| `ticks := ticks + 1` | `ticks := ticks.bump` |
| invariant／ensures 裡的 `ticks` | `ticks.val` |

「線性內層／非線性外層」的技巧原封不動：`t0 := ticks.val` 之後
`invariant ticks.val = t0 + (n - mind)` 完全沒有乘法。

★ 注意 `let t_in := ticks.val` 這個寫法。**存數字是誠實的**
（`t_in : Nat` 只能用來寫規格，回填不了計數器）；
存 `ticks` 本身就變成 `ResetToOld` 了——見 `Cheats/Unresolved_ResetToOld.lean`。
**型別分不出這兩者，只有讀 code 分得出。** -/

method insertionSortTicks
  (mut arr : Array Int) (mut ticks : Ticks) return (u : Unit)
  ensures arr.size = arrOld.size
  ensures Sorted arr
  ensures SameElements arrOld arr
  ensures ticks.val ≤ ticksOld.val + arrOld.size * arrOld.size
  do
    let arr₀ := arr
    let arr_size := arr.size
    let t_in := ticks.val
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ arr.size
      invariant arr.size = arr_size
      invariant 1 ≤ n ∧ n ≤ arr.size
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arr₀.toMultiset
      invariant ticks.val ≤ t_in + n * n
      do
        let t0 := ticks.val
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
        invariant arr.toMultiset = arr₀.toMultiset
        invariant ticks.val = t0 + (n - mind)
        invariant t0 ≤ t_in + n * n
        do
          ticks := ticks.bump
          if arr[mind]! < arr[mind - 1]! then
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 2000000 in
prove_correct insertionSortTicks by
  loom_solve!

/-! ## 2. 遷移後的 rubric（R13：與 instance、cheats、SPOTs 同一個 commit） -/

open PartialCorrectness PartialCorrectness.DemonicChoice in
structure ArraySort (f : Nat → Nat) where
  sort : Array Int → Ticks → VelvetM (Unit × Array Int × Ticks)
  spec : ∀ a t, triple True (sort a t)
                 (fun r => SortSpec a r.2.1 ∧ r.2.2.val ≤ t.val + f a.size)

/-- 橋接仍然是那一行 `triple_cons`，第四次只換投影。 -/
def insertionSortTicksImpl : ArraySort (fun n => n * n) where
  sort := insertionSortTicks
  spec := fun a t =>
    triple_cons _ (fun _ => trivial) (fun _ h => ⟨⟨h.2.2.1, h.2.1⟩, h.1⟩)
      (insertionSortTicks_correct a t)

/-- info: 'SortRubric.Opt06.insertionSortTicksImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms insertionSortTicksImpl

/-! ## 3. R13：第 05.5 次的組合性也要跟著遷移

證明本體**一字未改**——只有算術那幾行多了 `.val`。
`SameElements.size_eq` 完全沒動（它談的是陣列，不是計數器）。 -/

open PartialCorrectness PartialCorrectness.DemonicChoice in
theorem ArraySort.compose_two (f : Nat → Nat) (S : ArraySort f)
    (a : Array Int) (t : Ticks) :
    triple True (S.sort a t >>= fun r => S.sort r.2.1 r.2.2)
      (fun r => SortSpec a r.2.1 ∧ r.2.2.val ≤ t.val + f a.size + f a.size) := by
  apply triple_bind (cut := fun y => SortSpec a y.2.1 ∧ y.2.2.val ≤ t.val + f a.size)
  · exact S.spec a t
  · intro y hcut
    obtain ⟨⟨hsy, hmy⟩, hty⟩ := hcut
    have hsz : a.size = y.2.1.size := Opt05b.SameElements.size_eq hmy
    refine (triple_cons _ (fun _ => trivial) ?_ (S.spec y.2.1 y.2.2)) trivial
    rintro r ⟨⟨hs, hm⟩, ht⟩
    refine ⟨⟨hs, hmy.trans hm⟩, ?_⟩
    rw [← hsz] at ht
    omega

/-! ## 4. ★ 這一步真正買到什麼——四格表

指引 §5.1.1 要求先示範「顯然的補法」`ensures ticksOld ≤ ticks` 為什麼無效，
再示範抽象 `Ticks` 有效。**實測的答案是：兩者一樣有效，也一樣無效。**

| | 歸到**起點以下**（`ticks := 0`） | 歸到**起點**（`ticks := t_in`） |
|---|---|---|
| `Nat`，無守衛 | ✅ 通過 | ✅ 通過 |
| `Nat` + `ensures ticksOld ≤ ticks` | ❌ 證不出來（`⊢ ticksOld ≤ 0`） | ✅ 通過 |
| 抽象 `Ticks` | ❌ **型別錯誤**（造不出 `Ticks`） | ✅ 通過 |

四格全部有機械證據，見 `Cheats/Opt06_Cheat_ForgeZero.lean`（上兩列）
與 `Cheats/Unresolved_ResetToOld.lean`（下一列與整張表）。

所以精確的陳述是：

> **抽象 `Ticks` ≡ `ensures ticksOld.val ≤ ticks.val`。**
> 兩者擋住的集合**一模一樣**：都只保證終值不低於起點。
> 都不保證中間過程單調（複製一份、bump 五次、放回去，中間就不單調），
> 也都不保證終值反映真正的比較次數。

### 那型別版還有沒有比後條件版強的地方？

有一項，而且對 rubric 而言是實質的：

**它是結構性的，不是證明義務。** `ensures ticksOld ≤ ticks` 要有人寫下來、
有人證出來；漏寫就沒有。抽象 `Ticks` 對**任何**拿到 `Ticks` 參數的方法都成立，
包括我們沒看過的那些——**沒有「忘記加一條 `ensures`」這個失效模式**。

不比後條件版強的地方也要講清楚：
**擋不住 `ResetToOld`，也擋不住分身。** 兩者同源，見 §5。

## 5. ★ `ResetToOld` 與 `FakeCounter` 是同一支作弊

```lean
-- ResetToOld：複製 → 老實計費 → 把複製品放回去
let t_in := ticks;  … ticks := ticks.bump …;  ticks := t_in

-- FakeCounter：複製 → 對複製品計費 → 從不碰本尊
let mut fake := ticks;  … fake := fake.bump …
```

兩者都只做了一件事：**複製一個 `Ticks` 值**。
`private mk` 管的是「造」，管不到「複製」——而複製一個公開型別的值
**不需要任何建構子**。

這一句就是第 06 次通往第 09 次的橋，而且它把第 09 次的結論提前了三步：
**M1 與 M2 面 2 不是兩個問題，是同一個問題。**
Velvet 缺的不是 ghost state，是**線性性**。

## 6. 一個代價：`Ticks` 讓 `#eval` 與 SPOTs 需要一個公開起點

模組外造不出 `Ticks` ⇒ `#eval` 也造不出來。
解法是 `Ticks.mkForTesting`，並由 **R16** 把它隔離在
`Opt06_Tests.lean` 與 `Opt10_Audit.lean` 之內
（`check_isolation.sh` 會 grep 整個 `SortRubric/` 列舉所有建構點）。

本檔一次都沒有用到它——**實作不需要造計數器，只需要接一個進來**。
這正是為什麼相對界限（第 05 次）與計數器身分（第 09 次）互相拉扯：
相對界限**要求**實作收下一個計數器，而收下的那一刻，
它就有一個可以複製的值了。
-/

end SortRubric.Opt06
