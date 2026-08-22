/-
================================================================
  第 05.5 次 — 補驗 **rubric 層**的組合性（★ 本步不防作弊）
  檔案      : SortRubric/Opt05b_Composition.lean
  依賴      : Opt05_TicksRelative.lean
----------------------------------------------------------------
  ⚠ 這一步和第 05 次一樣**不淘汰任何作弊**。
     它補的是盤點表裡唯一標「待驗」的格子。

  第 05 次證到的是「**method** 的界限疊得起來」——`sortTwiceRel`
  走的是 `insertionSortRel_correct`（四條 `ensures`，含
  `arr.size = arrOld.size`），不是 `ArraySort.spec`。

  但 rubric 賣的是 `ArraySort.spec` 那三項。**橋接把四條收成三項時，
  丟掉的正是 `arr.size = arrOld.size`，而那條又是第二次呼叫需要的。**
  所以「界限可組合」這個保證，在 rubric 層是**未驗**的。

  本檔只用 `S.spec`，不碰任何 method 的 `_correct` 定理。
----------------------------------------------------------------
  結論（實測）:
      ✅ 過，而且**不需要動 spec**。
      缺口由一條兩行的 local 引理 `SameElements.size_eq` 補上。
      指引 §4.3 的做法 (b)（把 size 塞進 `SortSpec`）與
      (c)（塞進 `ArraySort.spec`）都**不必動用**。
----------------------------------------------------------------
  仍然活著的洞（與第 05 次完全相同，一個都沒少）:
    - 老實計費，最後 `ticks := ticksOld`   → 第 06 次
    - 做滿比較但比較器不計費               → 第 07 次
    - 實作繞過比較器直接 `x < y`           → 第 08 次
    - 計數器分身                           → 第 09 次（已知無解）
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/
import SortRubric.Opt05_TicksRelative

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace SortRubric.Opt05b

open SortRubric.Opt02 SortRubric.Opt05
open PartialCorrectness PartialCorrectness.DemonicChoice

/-! ## 1. 缺口在哪

第二次呼叫的界限是 `f a₁.size`，手上只有 `f a.size`。
要接起來需要 `a₁.size = a.size`——而 rubric 沒說。

不過 rubric **說了** `SameElements a a₁`，而 multiset 相等蘊含長度相等。
所以這條資訊其實在 spec 裡，只是還沒被取出來。 -/

/-- 「是原元素的重排」蘊含「長度沒變」。

`Array.toMultiset x = Multiset.ofList x.toList`（`Velvet/Std.lean:102`），
兩邊取 `Multiset.card` 即得。**零 typeclass 需求。**

依 P1，**不掛全域 `@[grind]`**——用到的地方就地帶入。 -/
theorem SameElements.size_eq {x y : Array Int} (h : SameElements x y) :
    x.size = y.size := by
  have := congrArg Multiset.card h
  simpa [Array.toMultiset] using this

/-! ## 2. ★ 主結論：rubric 層的界限疊得起來

**只用 `S.spec`。** 不碰 `insertionSortRel_correct`，不碰任何 method。
證明用的是 Loom 的兩條結構規則：`triple_bind`（`WP/Basic.lean:63`）
接續、`triple_cons`（同檔 :54）調整前後條件。 -/

theorem ArraySort.compose_two (f : Nat → Nat) (S : ArraySort f)
    (a : Array Int) (t : Nat) :
    triple True (S.sort a t >>= fun r => S.sort r.2.1 r.2.2)
      (fun r => SortSpec a r.2.1 ∧ r.2.2 ≤ t + f a.size + f a.size) := by
  apply triple_bind (cut := fun y => SortSpec a y.2.1 ∧ y.2.2 ≤ t + f a.size)
  · exact S.spec a t
  · intro y hcut
    obtain ⟨⟨hsy, hmy⟩, hty⟩ := hcut
    -- ★ 這一行就是整個缺口
    have hsz : a.size = y.2.1.size := SameElements.size_eq hmy
    refine (triple_cons _ (fun _ => trivial) ?_ (S.spec y.2.1 y.2.2)) trivial
    rintro r ⟨⟨hs, hm⟩, ht⟩
    refine ⟨⟨hs, hmy.trans hm⟩, ?_⟩
    rw [← hsz] at ht
    omega

/-- do-notation + tuple pattern 的寫法也接得上（`triple_bind` 穿得過 destructuring）。 -/
theorem ArraySort.compose_two_do (f : Nat → Nat) (S : ArraySort f)
    (a : Array Int) (t : Nat) :
    triple True (do let ⟨_, a₁, t₁⟩ ← S.sort a t
                    S.sort a₁ t₁)
      (fun r => SortSpec a r.2.1 ∧ r.2.2 ≤ t + f a.size + f a.size) :=
  ArraySort.compose_two f S a t

/-! ## 3. R10：套到真的程式上

`insertionSortRelImpl` 是第 05 次那支真的插入排序。
定理是**通用的**——它對任何 `ArraySort f` 成立，這裡只是實例化。 -/

example (a : Array Int) (t : Nat) :
    triple True (insertionSortRelImpl.sort a t >>=
                   fun r => insertionSortRelImpl.sort r.2.1 r.2.2)
      (fun r => SortSpec a r.2.1 ∧ r.2.2 ≤ t + a.size * a.size + a.size * a.size) :=
  ArraySort.compose_two _ insertionSortRelImpl a t

/-! 實際比較次數 vs 宣稱界限。與第 05 次的 `sortTwiceRel` 一致（56 vs 128），
證明這條 rubric 層的界限講的是同一件事。 -/

/-- info: (56, 128) -/
#guard_msgs in
#eval ((insertionSortRelImpl.sort #[8,7,6,5,4,3,2,1] 0 >>=
          fun r => insertionSortRelImpl.sort r.2.1 r.2.2).extract.2.2,
       0 + 8 * 8 + 8 * 8)

/-- info: 'SortRubric.Opt05b.ArraySort.compose_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ArraySort.compose_two

/-! ## 4. 缺口是真的——機械反證

拿掉 `SameElements.size_eq` 之後剩下的算術步驟**不是「難證」，是「假的」**。
把它抽成純算術命題，給一組反例：`f = id`、`a.size = 0`、`a₁.size = 5`。

（讀法：第一次排序「聲稱」花不超過 `f 0 = 0`，第二次「聲稱」花不超過
`f 5 = 5`。如果陣列真的可以從長度 0 變成長度 5，總帳就對不起來。
擋住這件事的是 `SameElements`，不是界限本身。） -/

example : ¬ (∀ (f : Nat → Nat) (t sa sy ty r : Nat),
    ty ≤ t + f sa → r ≤ ty + f sy → r ≤ t + f sa + f sa) := by
  intro h
  exact absurd (h id 0 0 5 0 5 (by simp) (by simp)) (by simp)

/-! ## 5. R12 控制組（兩組，方向相反）

否定結論要控制組；這裡結論是肯定的，所以控制組要證的是**另一件事**：
「卡住的地方真的是 size，不是 `triple` 的接續本身」。

### 控制組 (a)：界限與 size 無關時，同一條證明路徑不需要引理就過

`f` 取常數 ⇒ `f y.2.1.size` 與 `f a.size` beta-reduce 成同一個東西 ⇒
`omega` 直接過。**證明骨架一字未改，只少了 `hsz` 那一行。**
⇒ 骨架（`triple_bind` + `triple_cons`）是好的，缺的只有 size 連結。 -/

example (S : ArraySort (fun _ => 3)) (a : Array Int) (t : Nat) :
    triple True (S.sort a t >>= fun r => S.sort r.2.1 r.2.2)
      (fun r => SortSpec a r.2.1 ∧ r.2.2 ≤ t + 3 + 3) := by
  apply triple_bind (cut := fun y => SortSpec a y.2.1 ∧ y.2.2 ≤ t + 3)
  · exact S.spec a t
  · intro y hcut
    obtain ⟨⟨hsy, hmy⟩, hty⟩ := hcut
    refine (triple_cons _ (fun _ => trivial) ?_ (S.spec y.2.1 y.2.2)) trivial
    rintro r ⟨⟨hs, hm⟩, ht⟩
    exact ⟨⟨hs, hmy.trans hm⟩, by omega⟩

/-! ### 控制組 (b)：把 `hsz` 那一行拿掉，`omega` 卡在哪

釘住逐字的失敗訊息。重點是最後兩列——`omega` 把
`f a.size` 與 `f y.2.1.size` 當成**兩個不同的原子**（`c` 與 `e`）。
那就是缺口的機械形式：**不是算術不夠強，是兩個 `f` 的引數不知道相等。** -/

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  g ≥ 0
  e ≥ 0
  d ≥ 0
  d + e - g ≥ 0
  c ≥ 0
  b ≥ 0
  b + c - d ≥ 0
  b + 2*c - g ≤ -1
where
 b := ↑t
 c := ↑(f a.size)
 d := ↑y.2.2
 e := ↑(f y.2.1.size)
 g := ↑r.2.2
-/
#guard_msgs in
example (f : Nat → Nat) (S : ArraySort f) (a : Array Int) (t : Nat) :
    triple True (S.sort a t >>= fun r => S.sort r.2.1 r.2.2)
      (fun r => SortSpec a r.2.1 ∧ r.2.2 ≤ t + f a.size + f a.size) := by
  apply triple_bind (cut := fun y => SortSpec a y.2.1 ∧ y.2.2 ≤ t + f a.size)
  · exact S.spec a t
  · intro y hcut
    obtain ⟨⟨hsy, hmy⟩, hty⟩ := hcut
    refine (triple_cons _ (fun _ => trivial) ?_ (S.spec y.2.1 y.2.2)) trivial
    rintro r ⟨⟨hs, hm⟩, ht⟩
    refine ⟨⟨hs, hmy.trans hm⟩, ?_⟩
    omega

/-! ## 6. 這一步買到什麼

| | |
|---|---|
| **買到** | 「界限可組合」從 method 層升到 **rubric 層**。第 10 次的保證強度表那一列可以只寫 `ArraySort.spec`，不必附註「只在 method 層驗過」 |
| **買到** | 一條可重用的 local 引理。第 06/07/08 次每次改 `ArraySort` 形狀，這條證明都要跟著遷移（R13），但引理本身不會變 |
| **沒買到** | 任何防作弊能力。作弊者一樣能用一支假排序滿足這個組合定理——因為它是從 `S.spec` 推出來的，`S` 是誰不影響 |
| **沒買到** | n 次組合。只做了兩次；n 次要 induction，形狀已經清楚（cut 換成 `fun y => SortSpec a y.2.1 ∧ y.2.2 ≤ t + n * f a.size`），沒做是因為 time-box |

## 7. 對「橋接丟資訊」這件事的回頭看

第 02 次決定 `SortSpec` 只講兩件事（有序 + 重排），不含 `arr.size = arrOld.size`，
理由是「不把 proof-friendly 的冗餘塞進 top-level spec」。

這一步證明那個決定**是對的**：丟掉的資訊不是真的丟掉了，
它蘊含在 `SameElements` 裡，取出來只要兩行。
**規格該講的是「什麼是對的」，不是「怎麼證比較方便」。**
-/

end SortRubric.Opt05b
