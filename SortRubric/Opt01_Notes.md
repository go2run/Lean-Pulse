# 第 01 次優化 — Notes

## 1. 這一步做了什麼

定義 `Sorted : Array Int → Prop`（全域版，任兩個索引 `i ≤ j` 都遞增）。
**故意不補任何東西**，讓「只有 `Sorted`」的洞暴露出來。
洞的具體形狀：一支 `ZeroFill` method 把整個陣列輾平成 0，通過 `ensures Sorted a`。

## 2. 與指引草稿碼的差異

| 指引寫的（§6.1） | 本檔實際 | 為什麼 |
|---|---|---|
| `def Sorted (a : Array Int) : Prop := ∀ i j, i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!` | **一字不差採用** | — |
| 驗收只列兩個 `example` | 另加一支 Velvet method `ZeroFill` | `example` 只說明「這個 `Prop` 證得出來」；一支**通過 `ensures` 的程式**才讓洞變得刺眼 |
| （未提） | `import Mathlib.Tactic.IntervalCases` | `Velvet.Std` 不含 `interval_cases`。逐字錯誤：`unknown tactic`。已進 ERRATA |
| （未提） | 需自證 `sorted_replicate_zero` | `loom_solve` 不會自己處理 `Array.replicate`；`Sorted (Array.replicate n 0)` 要手動餵。見 §6 |

### 一個刻意的決定：`Sorted` **不含** `0 ≤ i`

`0 ≤ i` 對 `Nat` 恆真，是純裝飾。理由有二：

1. `Sorted` 是整個專案最常被讀的定義，它應該讀起來就是那句數學敘述
2. §6.2 才剛教「postcondition 寫真正需求，proof-friendly redundancy 放 invariant」，
   把冗餘塞進 top-level spec 是自打嘴巴

**代價**：Velvet 的 `ensures` 產生的後條件會逐字保留你寫的形狀，
所以 `Sorted` 與 `<method>_correct` 之間會差一個形狀轉換。
這個差額就是**決定 (二) 要量的橋接成本**，第 02 次交出數字。

## 3. 驗證：應該死掉的作弊

**這一步不淘汰任何作弊**——這是設計，不是遺漏。

反過來，這一步要證明**作弊活著**：

### `ZeroFill`（本檔 §3，非 `Cheats/`）
- 機械可檢的證據：`prove_correct ZeroFill by loom_solve` ✅ 通過
- `#guard_msgs` 釘住的行為：

  ```
  info: DivM.res ((), #[0, 0, 0, 0])
  ```
  `#[8,2,5,3]` 進去，`#[0,0,0,0]` 出來——輸入的四個元素一個都不剩。

- 而它是一條**真的定理**，不是 `sorry`：

  ```
  info: 'SortRubric.Opt01.ZeroFill_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

> `ZeroFill` 放在主檔而不是 `Cheats/`，因為它在這一步**應該通過**。
> 第 02 次會有 `Cheats/Opt02_Cheat_AllZeros.lean` 拿同一支程式去撞新規格。

## 4. 驗證：應該活下來的正確實作

```
########## [1/3] import 隔離 ##########
✓ 隔離成立：SortRubric 的 import 閉包不含專案根目錄模組。

########## [2/3] lake build SortRubric ##########
✓ SortRubric 綠

########## [3/3] 完整 lake build，比對既有環境債 ##########
✓ 失敗集合與 baseline 逐字相同（既有環境債，非本次造成）

    error: VelvetLC917.lean:44:16: Failed to prove assertion
    error: VelvetLC917.lean:34:12: Failed to prove assertion
    error: VelvetLC917.lean:92:33: unsolved goals
    error: Lean exited with code 1
    error: build failed
    - VelvetLC917

========== 全部通過 ==========
```

`lake build SortRubric` 本身：`Build completed successfully (1185 jobs).`

無 `sorry` / `admit` / `native_decide` / `@[implemented_by]` / `unsafe`。

## 5. 仍然活著的洞

| 洞 | 預計由第幾次處理 |
|---|---|
| 全部填 0（`ZeroFill` 就是） | 02 |
| 刪掉元素 | 02 |
| 只留最小值 | 02 |
| 每支 method 的簽章、前條件各寫各的 | 03 |
| 完全不談成本（比較次數） | 04 起 |
| 計數器歸零 / 分身 | 06 / 09（分身**預期無解**，見 README） |

### 5.1 ★ 已知的未來衝突：`default` 的三次轉向

本檔那兩條餵給 `Array.replicate` 的引理，之所以能「對**所有** `i` 成立（含界外）」，
是因為 `default : Int = 0` 是一個**已知的具體值**。

**第 08 次 α 抽象之後，`default : α` 不可知，同形狀的引理會失效**，
界外索引必須改回**有界量化**（`i < a.size → …`）。
先記在這裡，第 08 次撞到時才不會以為是別的東西壞了。

把這條線連起來看，同一個 `default` 在三步裡翻轉了三次：

| 第幾次 | `default` 扮演什麼 | 效果 |
|---|---|---|
| **01** | 已知等於 `0`，界外索引也回傳 `0` | ✅ **幫忙**——`sorted_replicate_zero` 的證明變成一行 `simp` |
| **02 之後** | 實作可以無中生有地產生 `default` 填滿陣列 | ❌ **變成障礙**——`SameElements` 讓它證不出來 |
| **08** | α 抽象後 `default : α` 不可知 | ⚠ **變成證明負擔**——引理要改成有界量化 |

這正好是 typeclass 預算表那條「**`Inhabited` 安全，條件是 `SameElements` 在**」的具體展開：
`Inhabited` 給實作的能力（生出 `default`）在每一步的意義都不同，
而擋住它的從來不是 `Inhabited` 本身，是後條件。

## 6. 遇到的問題 / 未解決

### 6.1 `interval_cases` 不在 `Velvet.Std` 裡

```
error: SortRubric/Opt01_Sorted.lean:46:3: unknown tactic
```
補 `import Mathlib.Tactic.IntervalCases` 解決。已記進 `Opt00_GUIDE_ERRATA.md` §C。

### 6.2 `loom_solve` 不處理 `Array.replicate`

`ZeroFill` 的後條件卡住：
```
error: SortRubric/Opt01_Sorted.lean:67:23: unsolved goals
case «ensures_1: Sorted a»
aOld : Array ℤ
⊢ Sorted (Array.replicate aOld.size 0)
```

解法：手寫兩條引理並把後者掛 `@[grind]`。

```lean
theorem replicate_zero_get (n i : Nat) : (Array.replicate n (0:Int))[i]! = 0 := by
  by_cases h : i < n
  · rw [getElem!_pos (h := by simpa using h)]; simp
  · rw [getElem!_neg (h := by simpa using h)]; rfl

@[grind]
theorem sorted_replicate_zero (n : Nat) : Sorted (Array.replicate n (0:Int)) := by
  intro i j _
  simp [replicate_zero_get]
```

**一個小發現值得記**：界外索引也回傳 0，因為 `getElem!` 界外給 `default`，
而 `default : Int` 就是 `0`。所以 `replicate_zero_get` 對**所有** `i` 成立，不需要 `i < n` 的前提——
這讓 `sorted_replicate_zero` 的證明變成一行 `simp`。

這也順帶說明了為什麼 `Inhabited` 在第 08 次是安全的**但需要條件**：
`default` 是實作可以無中生有的元素。這裡它剛好幫了忙；
在第 02 次之後，`SameElements` 會讓同一個 `default` 變成一個**證不出來**的障礙。

### 6.3 未解決

無。這一步沒有 BLOCKED。
