# 第 02 次優化 — Notes

## 1. 這一步做了什麼

補上 `SameElements`（multiset 相等），把規格從「給我一個有序陣列」收緊成
「給我一個**由原元素重排而成的**有序陣列」。
淘汰三支在第 01 次通得過的作弊，並交出一支真的插入排序。
同時量出**決定 (二) 的橋接成本**（見 §3）。

## 2. 與指引草稿碼的差異

| 指引寫的（§6.2） | 本檔實際 | 為什麼 |
|---|---|---|
| `SameElements before after := before.toMultiset = after.toMultiset` | 一字不差採用 | — |
| `SortSpec := Sorted after ∧ SameElements before after` | 一字不差採用（**人類順序**） | 決定 (二)；成本已量出，見 §3 |
| 「一支 `bubbleSort`」 | 命名為 **`insertionSort`** | 它就是插入排序。把插入排序叫成別的名字，正是第 10 次 D1 軸要抓的事（F\* 原文的 *"claiming that it is quicksort"*）。在一份以「不讓實作說謊」為主題的專案裡，函式名字也不該說謊 |
| （未提） | `Sorted`/`SameElements`/`SortSpec` 都要掛 `@[grind]` | 否則 `ensures Sorted arr` 會讓 `loom_solve!` 卡住，見 §6.1 |
| 三支作弊只列 `example : ¬ SortSpec …` | 每支都附**一支真的跑過 `prove_correct` 的程式** | R10。`example` 講的是命題，rubric 擋的是程式 |

### invariant 三分類（已標進 `Opt02_SameElements.lean` 的註解）

| 類型 | 回答什麼 | 本檔的例子 |
|---|---|---|
| Structural | index 還合法嗎？size 變了嗎？ | `arr.size = arr_size`、`n ≤ arr.size` |
| Ordering | 哪一區已經排好？ | `∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ n-1 → arr[i]! ≤ arr[j]!` |
| Preservation | 元素還在嗎？ | `arr.toMultiset = arr₀.toMultiset` |

三個陷阱都遇到並照指引處理：不拿 `Sorted arr` 當 invariant（用區域版）；
`arr.size = arr_size` 雖可由 multiset 推出仍保留（proof-friendly redundancy）；
外部 spec 維持全域 `i ≤ j` 版本，未弱化。

---

## 3. ★ 決定 (二)：橋接成本的實測結果

### 3.1 落差只有一個 `And.comm`

先確認落差的**唯一**成因。把 `and_comm` 拿掉、其餘不變（`probe/A2.lean`）：

```
error: Type mismatch: After simplification, term
  insertionSort_correct a
 has type
  {True}insertionSort a{x,SameElements a x.2 ∧ Sorted x.2}
but is expected to have type
  {True}insertionSort a{r,Sorted r.2 ∧ SameElements a r.2}
```

兩邊的 `Sorted` 與 `SameElements` **完全一致**，連 `x.2` 的結構 eta 都自動對上。
差的只有合取順序。

### 3.2 五種寫法的實測

| 版本 | 橋接行數 | 依賴的自動化 | 三項時還成立嗎？ |
|---|---|---|---|
| B：對齊 Velvet 反序 | 0 行 | 無 | （不適用，形狀被釘死在工具上） |
| **`triple_cons`（採用）** | **1 行** | **零**（Loom 的 consequence rule） | ✅ **成立** |
| A-term：`funext`+`propext`+`▸` | 1 行 | 零 `simp`，但依賴 `▸` 的 motive 推導 | ❌ **失效** |
| A-simpa：`simpa [SortSpec, and_comm]` | 1 行 | `and_comm` 進 simp set | 未測（simp set 本身已不採用） |
| A-explicit：`funext` + `rw` | 5 行 | 零 `simp` | 未測 |

### 3.3 ★ 為什麼最後選 `triple_cons` 而不是 A-term

Loom **有** consequence rule（`Loom/MonadAlgebras/WP/Basic.lean:54`）：

```lean
lemma triple_cons (x : m α) {pre pre' : l} {post post' : α -> l} :
  pre' ≤ pre -> (∀ y, post y ≤ post' y) -> triple pre x post -> triple pre' x post'
```

`l = Prop` 時 `≤` 就是蘊涵，所以後條件的重排寫成一個 `fun _ h => ⟨…⟩`：

```lean
theorem insertionSort_sortSpec :
    ∀ a, triple True (insertionSort a) (fun r => SortSpec a r.2) :=
  fun a => triple_cons _ le_rfl (fun _ h => ⟨h.2, h.1⟩) (insertionSort_correct a)
```

**選 A 的全部理由是「落差被吸收在單一位置，之後只改那一行」，所以要挑最穩的寫法。**
穩定性用一個模擬第 04 次的實驗驗過，不是用推論（`probe/T2.lean`）：
後條件變成**三項**、且與 Velvet 展開完全反序時——

| 版本 | 三項時 |
|---|---|
| `triple_cons` | ✅ 通過。**形狀不變、位置不變**，只把 `⟨h.2, h.1⟩` 換成 `⟨h.2.2, h.2.1, h.1⟩` |
| A-term | ❌ 失敗 |

A-term 三項時的逐字錯誤：

```
error: Type mismatch
  NoOp3_correct a
has type
  {have a := a; True}NoOp3 a{x,match x with
    | (u, a_1) => a_1 = a ∧ SameElements a a_1 ∧ a_1.size = a.size}
but is expected to have type
  {True}NoOp3 a{x,(SameElements a x.2 ∧ x.2 = a) ∧ x.2.size = a.size}
```

`and_comm` 只換掉了外層那一對（`(SameElements ∧ =) ∧ size`），
但目標是 `size ∧ SameElements ∧ =`——還需要 `and_assoc`，而 `▸` 的 motive 推導在這裡會斷。

**第 04 次會加上 `ticks ≤ ticksOld + f n`，落差正好變成三項。**
換句話說，A-term 撐不到第 04 次；`triple_cons` 撐得到，而且對任意項數與任意重排都成立。

### 3.4 對照判準

> | 量到的結果 | 決定 |
> |---|---|
> | 橋接 ≤ 3 行，且不依賴脆弱的 `simp` lemma set | 乾淨版（人類順序） |

1 行、零 `simp`、零自動化 ⇒ **落在第一列。乾淨版（人類順序）定案。**

### 3.5 一個附帶的觀察

B 的 0 行看起來更漂亮，但它的 0 是**把 rubric 的形狀釘在工具的展開順序上**換來的。
`triple_cons` 的 1 行則把落差吸收在單一位置——
第 04 次加 `ticks`、第 08 次抽象 α、第 09 次可能換 monad，要改的永遠只有那個 `fun _ h => ⟨…⟩`。

對照 F\* 側的教訓：`array_sort` 被 retrofit 三次，每次都連帶 N 個 instance 的適配 commit。

## 4. 驗證：應該死掉的作弊

三支都遵守 R10（附真的程式）。**而且失敗本身被釘進 build**，不再只是貼上的紀錄。

### 4.0 ★ 做法升級：`#guard_msgs` 也能釘失敗

原本的做法是「保留通得過的版本，把錯誤貼進 Notes」。問題是：
**那個錯誤訊息是一次性的觀察，不是持續驗證的事實。**
`SortSpec` 後面還要改三次（第 04、08、09），改完之後貼上的錯誤就過期了，而沒有東西會告訴你。

實測確認 `#guard_msgs` 可以捕捉 `prove_correct` 的失敗：

```lean
/--
error: unsolved goals
case «ensures_1: SameElements arrOld arr»
arrOld : Array ℤ
⊢ SameElements arrOld (Array.replicate arrOld.size 0)
-/
#guard_msgs in
prove_correct ZeroFill by
  loom_solve
```

訊息相符 → 吃掉訊息，build 綠。訊息不符、或**根本沒有訊息（= 作弊居然通過了）** → 它自己報錯。
負向測試（改一個字）確認它真的會失敗：

```
error: ❌️ Docstring on `#guard_msgs` does not match generated message:
  error: unsolved goals
  case «ensures_1: SameElements arrOld arr»
  arrOld : Array ℤ
- ⊢ SOMETHING ELSE ENTIRELY
+ ⊢ SameElements arrOld (Array.replicate arrOld.size 0)
```

### 4.0.1 ⚠ 代價：受控的 `sorryAx`，以及為什麼要圍堵

證明失敗後 Lean **仍會**把 `<method>_correct` 加進環境，並讓它依賴 `sorryAx`。
更麻煩的是 `prove_correct` 產生的 lemma 帶 **`@[loomSpec]`**（`Velvet/Syntax.lean:411`），
所以一個 sorry 過的 spec 若被下游看見，**可能污染 `loom_solve`**。

因此這是 R5 的**受控例外**，三重圍堵，每一層都機械化：

| # | 圍堵 | 由誰保證 |
|---|---|---|
| 1 | 失敗訊息被釘住 —— 作弊哪天通過了，build 會紅 | `#guard_msgs`（build） |
| 2 | `sorryAx` 被第二個 `#guard_msgs` 釘住 —— 明文，不是暗樁 | `#print axioms` + `#guard_msgs`（build） |
| 3 | **沒有任何模組 import `Cheats/`** | `check_isolation.sh` 的「圍堵」段，附負向測試 |

> R5 的用意是「不能用 `sorry` 假造正面結果」。
> 一支**專門用來示範失敗**的作弊帶著被釘住、且不外洩的 `sorryAx`，沒有假造任何東西。
> 但這是對 R5 的字面修改，已在 README 與本節明載。

### 4.1 `Cheats/Opt02_Cheat_AllZeros.lean`
- 真程式：`ZeroFill`，`arr := Array.replicate arr.size 0`
- 釘住的失敗：`⊢ SameElements arrOld (Array.replicate arrOld.size 0)`
  —— 這個目標**是假的**（只要 `arrOld` 有任何非 0 元素），所以不是「證不出來」，是「不成立」
- 釘住的 `sorryAx`：`ZeroFill_correct` → `[propext, sorryAx, Classical.choice, Quot.sound]`
- 程式照樣跑得動：`DivM.res ((), #[0, 0, 0, 0])`
- 機械反證（**不依賴任何 sorry**）：`¬ SortSpec #[8,2,5,3] #[0,0,0,0]`，其 `#print axioms` 乾淨

### 4.2 `Cheats/Opt02_Cheat_DropElements.lean`
- 真程式：`DropAll`，`arr := #[]`
- 釘住的失敗：`⊢ SameElements arrOld #[]`
- 程式行為：`DivM.res ((), #[])`
- 機械反證：`¬ SortSpec #[8,2,5,3] #[]`，另加指引舉的 `¬ SortSpec #[8,2,5,3] #[2,3,5]`

### 4.3 `Cheats/Opt02_Cheat_MinOnly.lean` ★ 三分類的最好實例
- 真程式：`MinOnly`，真的掃過整個陣列找最小值，然後 `arr := #[m]`
- 釘住的失敗：

  ```
  error: unsolved goals
  case «ensures_1: SameElements arrOld arr»
  arrOld : Array ℤ
  i : ℕ
  m : ℤ
  invariant_1 : i ≤ arrOld.size
  done_1 : i = arrOld.size
  i_1 : ℕ
  m_1 : ℤ
  i_2 : { fst := i, snd := m } = { fst := i_1, snd := m_1 }
  ⊢ SameElements arrOld #[m_1]
  ```

  **這則訊息自己指出了缺的是三分類裡的哪一類。**
  Structural 那一類齊全（`invariant_1 : i ≤ arrOld.size`），
  迴圈確實跑完了（`done_1 : i = arrOld.size`），`m_1` 真的是最小值。
  **唯獨沒有任何一條談到元素去哪了**——缺的是 **Preservation**。
  `m_1` 確實是最小值，可是一個元素換不回四個。
- 程式行為：`DivM.res ((), #[2])`
- 機械反證：`¬ SortSpec #[8,2,5,3] #[2]`

### 4.4 被規格的哪一條殺？

| 作弊 | 被哪一步殺 | 被規格的哪一條殺 |
|---|---|---|
| `Opt02_Cheat_AllZeros` | Opt02 | `SameElements` |
| `Opt02_Cheat_DropElements` | Opt02 | `SameElements` |
| `Opt02_Cheat_MinOnly` | Opt02 | `SameElements` |

**三支都是 `SameElements` 殺的，`Sorted` 一支都沒殺到。**
這不是巧合——三支作弊的輸出**都是有序的**，它們違反的從來不是有序性。
而這個結論是**從證明的形狀讀出來的**（反證只需要 `rintro ⟨-, h⟩` 取後半），不是從論述推出來的。

`Sorted` 單獨是空的；全部的鑑別力都在 `SameElements`。
這一欄會持續累積：**十步做完後，任何一條從來沒殺過東西的後條件，都是空洞的嫌疑犯。**

## 5. 驗證：應該活下來的正確實作

`insertionSort` 通過完整的 `Sorted ∧ SameElements`：

```
Build completed successfully (1189 jobs).
```

`bash SortRubric/check_build.sh` 三關全過（隔離 / SortRubric 綠 / 失敗集合與 baseline 逐字相同）。

對照組 `correct_answer_passes : SortSpec #[8,2,5,3] #[2,3,5,8]` ✅ 留在 build 裡。

`#print axioms insertionSort_sortSpec` = `[propext, Classical.choice, Quot.sound]`，以 `#guard_msgs` 釘住。

無 `sorry` / `admit` / `native_decide` / `@[implemented_by]` / `unsafe`。

---

## 6. 仍然活著的洞

| 洞 | 預計由第幾次處理 |
|---|---|
| 每支 method 的簽章、前條件各寫各的 | 03 |
| 完全不談成本（比較次數） | 04 |
| 遞迴呼叫的界限疊不起來 | 05 |
| 老實計費，最後 `ticks := ticksOld` | 06 |
| 比較器不計費 / 亂回答 | 07 |
| 實作繞過比較器，直接 `x < y` | 08 |
| **計數器分身** | 09（**已知受限**，見 README；目前預期無解） |

### 已知的未來衝突（延續 Opt01 §5.1）

第 01 次記下的「`default` 三次轉向」在這一步發生了第二次：
`Array.replicate arr.size 0` 在第 01 次是**合法的通過**，在這一步變成
`⊢ SameElements arrOld (Array.replicate arrOld.size 0)` 這個**證不出來的目標**。

擋住它的是 `SameElements`，不是 `Inhabited` 本身——
這正是 typeclass 預算表那條「`Inhabited` 安全，**條件是 `SameElements` 在**」的實例。

---

## 7. 遇到的問題 / 未解決

### 7.1 `ensures Sorted arr` 需要 `@[grind]`

直接寫 `ensures Sorted arr`（引用 `def` 而非展開式）會讓 `loom_solve!` 卡住：

```
error: SortRubric/Opt02_SameElements.lean:62:10: Failed to prove assertion
error: SortRubric/Opt02_SameElements.lean:61:10: Failed to prove assertion
```

解法：把 `Sorted` / `SameElements` 標成 `@[grind]`，`grind` 才會展開它們。

**這不是一條 API 差異，是一條依賴鏈——第 03 次能不能存在的前提：**

```
ensures Sorted arr 沒有 @[grind]
  → loom_solve! 卡住
  → 規格只能「就地展開」，不能引用具名 predicate
  → 沒有具名 predicate
  → 第 03 次的 interface 抽象不成立
```

所以它同時屬於指引的 §6.2「陷阱」與 §6.3「前提」兩處，不只是 ERRATA §C 的一列。
已同步記進 `README.md` 的自動化屬性預算表。

### 7.2 `decide` 看不穿 `def`

`¬ SortSpec #[8,2,5,3] #[0,0,0,0]` 不能直接 `decide`：

```
error: failed to synthesize
  Decidable ¬SortSpec #[8, 2, 5, 3] #[0, 0, 0, 0]
```

兩個原因，要分開看：
1. `Sorted` 含**無界** `∀ i j`，本來就不可判定——所以不能對整個 `SortSpec` 用 `decide`
2. `SameElements` **可判定**（`Multiset Int` 有 `DecidableEq`），但 `decide` 看不穿 `def`

可用的配方（`Opt00_GUIDE_ERRATA.md` §E 的 U2 至此有了答案）：

```lean
theorem … : ¬ SortSpec a b := by
  rintro ⟨-, h⟩                      -- 只取 SameElements 那一半
  revert h
  unfold SameElements Array.toMultiset
  decide
```

**設計上的觀察**：反證只需要 `SameElements` 那一半，因為三支作弊的輸出**都是有序的**。
它們違反的從來不是有序性，是「跟輸入有關」——這正是這一步補上的東西。

### 7.3 未解決

無。這一步沒有 BLOCKED。
