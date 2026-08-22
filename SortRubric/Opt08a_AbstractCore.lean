/-
================================================================
  第 08a 次優化 — M2 面 3：抽象元素型別 α
  檔案      : SortRubric/Opt08a_AbstractCore.lean
  依賴      : Opt07_InstrOrder.lean
----------------------------------------------------------------
  ★ 這一步淘汰的作弊:
      「收下 `iord` 但完全不用，直接 `x < y`」
      （`Cheats/Opt08_Cheat_BypassWithInt.lean`）

  ★ 證據等級：**型別錯誤**。這是本專案第三列「寫不出來」
     （前兩列是第 06 次的 `ForgeZero` 與 `ForgeMidpoint`）。

     機制：`SpecOrder.le : α → α → Prop`，而 `if c then _ else _`
     需要 `[Decidable c]`。`SpecOrder` 結構裡**沒有那個欄位**，
     所以沒有任何辦法從 `ord` 取得一個 `Decidable`。
     ⇒ 實作**算不出** `ord.le x y`，只能問 `iord.cmp`。
----------------------------------------------------------------
  ★ 為什麼拆成 08a / 08b（D-08）:

      面 3 的鑑別內容是**型別錯誤**，不需要一支完整的排序。
      08a 交的是定義 + rubric 形狀 + 一支只用 `cmp` 的方法，
      這樣就足以證明「除了 `iord` 沒有別的觀察 α 的途徑」。

      08b（完整的抽象插入排序）是加分項，**目前 BLOCKED**
      （R8，兩次未過；診斷見 `Opt08_Notes.md` §5）。
      它卡在證明工程，與面 3 的論點無關。
----------------------------------------------------------------
  ⚠ 已知的弱點，必須誠實記錄:
      本檔的 `ArraySort`（抽象版）**目前沒有 instance**——
      唯一能住進去的東西是一支多型排序，而那正是 BLOCKED 的 08b。
      一個沒有住戶的 rubric 鑑別不了任何東西。
      **面 3 的結論由型別錯誤承擔，不由 rubric 的住戶承擔。**
      詳見 `Opt08_Notes.md` §6。
----------------------------------------------------------------
  仍然活著的洞:
    - `ResetToOld` / `FakeCounter` / `CopyThenRebump` / `DiscardCmpTicks`
      → ★ **無解**（同源：複製一個 `Ticks` 值）
----------------------------------------------------------------
  狀態: [x] 完成（08b 另計）
================================================================
-/
import SortRubric.Opt07_InstrOrder

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Opt08

open SortRubric.Opt06

/-! ## 1. `SpecOrder` —— Lean 版的 `erased`

★ **`le` 是 `Prop`-valued，這是整個面 3 的支點。**

規格講得出 `ord.le x y`（它是個命題），實作**算不出**它
（`if` 需要 `Decidable`，而這個結構裡沒有那個欄位，
也沒有任何辦法從別處生一個出來）。

對照 F\*：那邊用 `erased` 標記「只能在規格裡出現」；
Lean 這邊不需要特別的標記——**`Prop` 本身就是那個標記**。 -/

structure SpecOrder (α : Type) where
  le       : α → α → Prop
  total    : ∀ x y, le x y ∨ le y x
  trans    : ∀ x y z, le x y → le y z → le x z
  antisymm : ∀ x y, le x y → le y x → x = y

namespace SpecOrder
variable {α : Type} (ord : SpecOrder α)

/-! 依 §5.3.4 的建議，把抽象版需要的引理**一次備齊**，不要邊證邊補——
否則會在「`grind` 失敗」與「引理缺失」之間分不清因果。

`SpecOrder` 只有四個欄位，全序的其他性質都要從它們導出。 -/

/-- 自反。由 `total` 導出（`le x x ∨ le x x`）。 -/
theorem le_refl (x : α) : ord.le x x := by
  rcases ord.total x x with h | h <;> exact h

/-- ★ **`SpecOrder` 沒有 `lt`。** 所有嚴格不等式都要走這一條：
「不是 `le x y`」就等於「`le y x`」。

第 08 次的排序在 `if` 的 else 分支拿到的正是這個形狀。 -/
theorem not_le (x y : α) (h : ¬ ord.le x y) : ord.le y x := by
  rcases ord.total x y with h' | h'
  · exact absurd h' h
  · exact h'

end SpecOrder

/-! ## 2. 帶計費的比較器（抽象版）

與第 07 次逐字比較，只有 `correct` 的右邊從 `x ≤ y` 換成 `ord.le x y`。

★ 注意 `InstrOrder` **以 `ord` 為索引**：一個比較器只對**一個**序誠實。
拿 `InstrOrder α ord₁` 去證關於 `ord₂` 的規格是型別錯誤。 -/

structure InstrOrder (α : Type) (ord : SpecOrder α) where
  cmp     : α → α → Ticks → Bool × Ticks
  correct : ∀ x y t, ((cmp x y t).1 = true ↔ ord.le x y)
  charged : ∀ x y t, (cmp x y t).2.val = t.val + 1

/-- `correct` 的 `false` 側，與第 07 次同形。 -/
theorem InstrOrder.correct_false {α : Type} {ord : SpecOrder α}
    (o : InstrOrder α ord) (x y : α) (t : Ticks) :
    (o.cmp x y t).1 = false ↔ ¬ ord.le x y := by
  rw [← o.correct x y t]
  cases h : (o.cmp x y t).1 <;> simp

/-! ## 3. 規格（抽象版）

`SameElements` **完全沒有 typeclass 需求**——
`Array.toMultiset a = Multiset.ofList a.toList`（`Velvet/Std.lean:102`）。
指引 §5.3.5 把「`toMultiset` 對抽象 α 需要 `DecidableEq`」列為高衝擊風險，
實測**不需要**，這一格是綠的。

`Sorted` 需要 `[Inhabited α]`，因為它用 `a[i]!`。R11 的論證見 `AttributeBudget.md`：
`Inhabited` 讓實作造得出一個 α 的值（等於抽象版的 `ZeroFill`），
但那支作弊在第 02 次已被 `SameElements` 殺掉，
而且 **`Inhabited` 不提供任何比較能力**，面 3 不受影響。 -/

def Sorted {α : Type} [Inhabited α] (ord : SpecOrder α) (a : Array α) : Prop :=
  ∀ i j, i ≤ j ∧ j < a.size → ord.le a[i]! a[j]!

def SameElements {α : Type} (before after : Array α) : Prop :=
  before.toMultiset = after.toMultiset

def SortSpec {α : Type} [Inhabited α] (ord : SpecOrder α) (before after : Array α) : Prop :=
  Sorted ord after ∧ SameElements before after

/-! ★ 這三個 `def` 在第 02 次是全域 `@[grind]`（「前提性」，見 `AttributeBudget.md`）。
這裡改成 **local**：本檔內生效，不外洩給 importer。

代價：下游模組（`Cheats/`、將來的 08b）要自己寫一次
`attribute [local grind] Sorted SameElements`。
換來的是第 04 次 `tick_step` 那一類跨模組事故從結構上不可能發生。 -/

attribute [local grind] Ticks.val_bump
  InstrOrder.correct InstrOrder.charged InstrOrder.correct_false
  SpecOrder.le_refl SpecOrder.not_le SpecOrder.trans
  Sorted SameElements

/-! ## 4. rubric 的新形狀

`sort` 對 α、`ord`、`iord` 全稱量化。

⚠ **本 structure 目前沒有 instance。** 唯一住得進去的是一支多型排序，
那是 BLOCKED 的 08b。這一點在 `Opt08_Notes.md` §6 誠實記錄——
**面 3 的結論由 §6 的型別錯誤承擔，不由 rubric 的住戶承擔。** -/

open PartialCorrectness PartialCorrectness.DemonicChoice in
structure ArraySort (f : Nat → Nat) where
  sort : (α : Type) → [Inhabited α] → (ord : SpecOrder α) → InstrOrder α ord →
         Array α → Ticks → VelvetM (Unit × Array α × Ticks)
  spec : ∀ (α : Type) [Inhabited α] (ord : SpecOrder α) (iord : InstrOrder α ord) a t,
           triple True (sort α ord iord a t)
             (fun r => SortSpec ord a r.2.1 ∧ r.2.2.val ≤ t.val + f a.size)

/-! ## 5. ★ 一支只用 `cmp` 的方法

`minIndex`：找出區間最小值的索引。

它為什麼夠格當面 3 的正面證據：

- **它做的是真正的序推理**（「這個位置的元素小於等於區間裡每一個」），
  不是形式上呼叫一下 `cmp` 就算了
- **它一次都沒有辦法看到 α 的內容**——`α` 是一個沒有任何結構的型別變數，
  手上只有 `ord`（算不出來）與 `iord.cmp`（要付錢）
- 它的計費是線性的，界限 `ticks.val ≤ ticksOld.val + arr.size`

證明成本：`loom_solve!` **2.8 秒**，一次就過。
序的推理全部由 `ord.trans` / `ord.le_refl` / `ord.not_le` 三條 local grind 提示承擔。

（`require 0 < arr.size` 是誠實的——空陣列沒有最小值。
這與第 03 次殺掉的 `ExtraPrecondition` 不同：那一支是在
**rubric 的共用 contract** 上偷加前條件，這裡是一支 helper 自己的規格。） -/

variable {α : Type} [Inhabited α]

method minIndex (ord : SpecOrder α) (iord : InstrOrder α ord)
  (arr : Array α) (mut ticks : Ticks) return (best : Nat)
  require 0 < arr.size
  ensures best < arr.size
  ensures forall j, j < arr.size → ord.le arr[best]! arr[j]!
  ensures ticks.val ≤ ticksOld.val + arr.size
  do
    let t_in := ticks.val
    let mut best := 0
    let mut i := 1
    while i ≠ arr.size
    invariant 1 ≤ i ∧ i ≤ arr.size
    invariant best < i
    invariant forall j, j < i → ord.le arr[best]! arr[j]!
    invariant ticks.val = t_in + (i - 1)
    do
      let r := iord.cmp arr[i]! arr[best]! ticks
      ticks := r.2
      if r.1 then
        best := i
      i := i + 1
    return best

set_option maxHeartbeats 4000000 in
prove_correct minIndex by
  loom_solve!

/-- info: 'SortRubric.Opt08.minIndex_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minIndex_correct

/-! ## 6. R12 正向控制組：抽象的東西真的住得進去

沒有這一節，「作弊者寫不出來」就可能只是「這些定義根本沒人滿足得了」。 -/

/-- `Int` 的自然序當 `SpecOrder`。 -/
def intOrder : SpecOrder Int where
  le := (· ≤ ·)
  total := fun x y => le_total x y
  trans := fun _ _ _ h₁ h₂ => le_trans h₁ h₂
  antisymm := fun _ _ h₁ h₂ => le_antisymm h₁ h₂

/-- 誠實的 `Int` 比較器，索引在 `intOrder` 上。 -/
def honestInt : InstrOrder Int intOrder where
  cmp x y t := (decide (x ≤ y), t.bump)
  correct := by intro x y t; simp [intOrder]
  charged := by intro x y t; exact Ticks.val_bump t

/-- info: 'SortRubric.Opt08.honestInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms honestInt

/-! ★ **`intOrder` 用得到 `Int` 的可判定性，`honestInt` 也是——
那完全正當**，因為那是**比較器的實作者**在做的事，不是**排序的實作者**。

面 3 要擋的是後者：排序只拿得到 `ord : SpecOrder α` 與 `iord`，
拿不到任何 `Decidable`。比較器的作者知道 α 是什麼，當然可以用它的結構。

**這條分工就是 `InstrOrder` 這個 structure 的全部意義。**

## 7. 這一步買到什麼

| | |
|---|---|
| **買到** | ★ 「除了 `iord` 沒有別的觀察 α 的途徑」——由**型別**強制，見 `Cheats/Opt08_Cheat_BypassWithInt.lean` |
| **買到** | 演算法課本的「**比較排序模型**」被寫進型別：`sort` 能做的只剩比較與搬移。**counting sort / radix sort 在這個 rubric 下寫不出來**（它們要看 α 的內容） |
| **買不到** | 計數器身分。四支同源作弊全部不受影響 |
| **未完成** | 抽象版的完整排序（08b），BLOCKED。⇒ 本檔的 `ArraySort` 目前沒有住戶 |

### F\* 那邊的旁證

AlgoStar 真的另立了一個
`array_counting_sort (a:eqtype) (key:a -> GTot nat) …`——
把 `Type` 放寬成 `eqtype`、把比較換成抽 key。

**型別的表達力剛好切在演算法理論的分類線上。**
-/

end SortRubric.Opt08
