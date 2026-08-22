/-
================================================================
  作弊 — 收下 `iord`，完全不用，直接 `x < y`
  檔案      : SortRubric/Cheats/Unresolved_BypassWithInt.lean
  死於      : 第 08a 次（面 3：抽象 α）—— ★ **已驗證**
  證據等級  : ★ **型別錯誤**（§4）；另附第 07 次下通過的綠燈（§1–2）
----------------------------------------------------------------
  📛 **改名紀錄**（`Cheats/` 命名規則第 2 條）:
     `Unresolved_BypassWithInt.lean` → `Opt08_Cheat_BypassWithInt.lean`
     時間：第 08a 次完成時。理由：§4 的型別錯誤已經是機械證據，
     檔名這句宣稱從「未驗證」變成「已驗證」。

     （第 06 次示範過反方向：指引預期 `ResetToOld` 死於第 06 次，
     實測沒死，所以它至今仍叫 `Unresolved_`。）
----------------------------------------------------------------
  ★ 這一支是第 08 次存在的理由。

     它**必須通過**。如果它在第 07 次就死了，那代表面 1 做了面 3 的工作，
     兩步的分工就講錯了（指引 v1 附錄 A 曾經把它列成 07 淘汰，
     v2 §5.2.4 已修正）。

     面 1 買到的是「比較器值得信任」，買不到「強迫實作去用它」。
     只要 `α = Int`，`x < y` 是語言原生能力，收不回來。
----------------------------------------------------------------
  狀態: [x] 已淘汰（第 08a 次，型別錯誤）
================================================================
-/
import SortRubric.Opt07_InstrOrder
import SortRubric.Opt08a_AbstractCore

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40

namespace SortRubric.Cheats.BypassWithInt

open SortRubric.Opt02 SortRubric.Opt06 SortRubric.Opt07

attribute [grind] Array.multiset_swap

/-! ## 1. 一支真的插入排序，收下 `iord` 之後完全不看它

`iord` 在整個 method body 裡出現 **0 次**。
排序是對的、元素是對的、界限是對的——**因為它一次都沒計費**。

後條件寫 `ticks = ticksOld`，讓「它報了什麼」是一條全稱定理。 -/

method bypassSort
  (iord : InstrOrder) (mut arr : Array Int) (mut ticks : Ticks) return (u : Unit)
  ensures Sorted arr
  ensures SameElements arrOld arr
  ensures ticks = ticksOld
  do
    let arr₀ := arr
    let arr_size := arr.size
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
      do
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
        invariant arr.toMultiset = arr₀.toMultiset
        do
          if arr[mind]! < arr[mind - 1]! then    -- ★ 語言原生的序，沒經過 iord
            swap! arr[mind]! arr[mind - 1]!
          mind := mind - 1
        n := n + 1
      return

set_option maxHeartbeats 2000000 in
prove_correct bypassSort by
  loom_solve!

/-- info: 'SortRubric.Cheats.BypassWithInt.bypassSort_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bypassSort_correct

/-! ## 2. 它住得進第 07 次的 rubric，而且是 `f _ = 0` 那一格 -/

def zeroCompareSort : Opt07.ArraySort (fun _ => 0) where
  sort := bypassSort
  spec := fun iord a t =>
    triple_cons _ (fun _ => trivial)
      (fun _ h => ⟨⟨h.2.2, h.2.1⟩, by simp [h.1]⟩)
      (bypassSort_correct iord a t)

/-- info: 'SortRubric.Cheats.BypassWithInt.zeroCompareSort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeroCompareSort

/-! ## 3. 第 08a 次怎麼殺它

把 `Int` 換成抽象的 `(α : Type)` + `SpecOrder α`：

- `ord.le x y : Prop`，**沒有 `Decidable` 實例**
- `SpecOrder` 結構裡就沒有那個欄位，**取不到**一個
- ⇒ `if …` 連型別檢查都過不了

以下四條是實作可能想走的全部路徑。 -/

section Face3
open SortRubric.Opt08
variable {α : Type} [Inhabited α]

/-! ## 4. ★ 四條繞過路徑，全部是型別錯誤

這是本專案第三列「寫不出來」（前兩列是第 06 次的
`ForgeZero` 與 `ForgeMidpoint`），而且是唯一一列**不依賴任何自動化**的——
編譯器在 elaboration 就拒絕，`loom_solve` 根本沒機會跑。 -/

/-! 路徑 1：直接把規格的序拿去 `if`。 -/
/--
error: failed to synthesize
  Decidable (ord.le a[0]! a[1]!)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example (ord : SpecOrder α) (a : Array α) : Bool :=
  if ord.le a[0]! a[1]! then true else false

/-! 路徑 2：改用 `decide`。同一個障礙。 -/
/--
error: failed to synthesize
  Decidable (ord.le a[0]! a[1]!)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example (ord : SpecOrder α) (a : Array α) : Bool :=
  decide (ord.le a[0]! a[1]!)

/-! 路徑 3：不管 `ord`，用語言原生的序（這正是 §1 那支在 `Int` 上做的事）。 -/
/--
error: failed to synthesize
  LT α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example (a : Array α) : Bool :=
  if a[0]! < a[1]! then true else false

/-! 路徑 4：退而求其次，只問「相不相等」。連這個都不行。 -/
/--
error: failed to synthesize
  Decidable (a[0]! = a[1]!)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example (a : Array α) : Bool :=
  if a[0]! = a[1]! then true else false

/-! ## 5. ★★ 讓面 3 **靜默失效**的三個 typeclass

上面四條之所以是型別錯誤，靠的是 α **沒有任何可計算的結構**。
只要多寫一個 typeclass 假設，作弊就當場復活——
**而且不會有任何錯誤訊息、任何警告**。

下面三段**全部編譯成功**。它們是這一節存在的理由：
把 §5.3.3 的散文警告變成 build 裡的機械事實。 -/

/-- ✗ `[DecidableEq α]`：路徑 4 復活。 -/
example [DecidableEq α] (a : Array α) : Bool :=
  if a[0]! = a[1]! then true else false

/-- ✗ `[LT α] [DecidableLT α]`：路徑 3 復活。 -/
example [LT α] [DecidableLT α] (a : Array α) : Bool :=
  if a[0]! < a[1]! then true else false

/-- ✗ 對 `ord.le` 的 `Decidable` 實例：路徑 1、2 同時復活，
而且這一個最危險——它看起來像是「只是讓規格好用一點」。 -/
example (ord : SpecOrder α) [∀ x y, Decidable (ord.le x y)] (a : Array α) : Bool :=
  if ord.le a[0]! a[1]! then true else false

/-! ⇒ **面 3 的保證等於「typeclass 假設清單保持乾淨」這件事。**

它由**編譯器**強制（型別錯誤），但前提是沒有人加那些假設；
而加了不會有任何訊號。所以第 10 次的稽核清單必須包含：

```
□ grep 整個 SortRubric/：α 上有沒有出現 DecidableEq / DecidableRel /
  DecidableLT / FinEnum / LT / LE / Ord 或任何 Decidable (ord.le _ _)
```

（`Velvet/Demo/Demo.lean` 的 `variable [FinEnum α]` 是「Velvet 可以多型 +
接 typeclass」的正面證據，**但不能照抄當成序的來源**。）

### 次要陷阱：`Classical.dec`

`Classical.dec` 生得出 `Decidable`，所以路徑 1、2 用 `open Classical in` 寫得出來。
**但它不會靜默**——那樣的定義會變成 `noncomputable`，
`#print axioms` 會出現 `Classical.choice`，而且 `#eval` 跑不動。
已記進第 10 次的 D3 檢查項。 -/

end Face3

end SortRubric.Cheats.BypassWithInt
