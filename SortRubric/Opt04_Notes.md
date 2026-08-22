# 第 04 次優化 — Notes

## 1. 這一步做了什麼

(a) 引入計數器 `ticks`（第二個 `mut` 參數），後條件加上 `ticks ≤ f n`。
(b) ★ 把界限 `f : Nat → Nat` **升格成 rubric 的參數**：`SortImpl` → `ArraySort (f : Nat → Nat)`。

**只承諾目標 (i)**：`f` 是活的參數。同一支 `insertionSortCounted`，
兩個不同的 `f`（`n*n` 與 `n*n+n`），兩個 instance 型別不同、實作相同。

## 2. 與指引草稿碼的差異

| 指引寫的（§6.4） | 本檔實際 | 為什麼 |
|---|---|---|
| `structure ArraySort (f : Nat → Nat)` | 一字不差採用 | — |
| `ensures ticks ≤ f aOld.size` | 方法寫 `ticks ≤ arrOld.size * arrOld.size`，`f` 在 rubric 層 | 方法不能被 `f` 索引（`method` 沒有型別參數化機制）；`f` 的引入點在 `ArraySort`，橋接由 `triple_cons` 做 |
| （未提） | `require ticksOld = 0` | **絕對界限的必然結果**：後條件沒提起點，起點就必須釘死。第 05 次拿掉這一行，它正是「界限疊不起來」的成因 |
| （未提） | 內層計數必須寫成**線性**形式 | 見 §6.1——這是本次最花時間的一件事 |

### 橋接：形狀不變，只換投影

第 02 次（兩項）：`fun _ h => ⟨h.2, h.1⟩`
第 04 次（三項）：`fun _ h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩`

**`triple_cons` 的穩定性在這一步得到第二次印證**（第一次是 `probe/T2.lean` 的模擬）。
若當初留在 A-term（`funext`/`propext`/`▸`），這一步就要重寫橋接。

## 3. 目標 (i)：機械證據

```lean
example : ArraySort (fun n => n * n)     := insertionSortQuadratic
example : ArraySort (fun n => n * n + n) := insertionSortLoose
example : insertionSortQuadratic.sort = insertionSortLoose.sort := rfl   -- ★ 實作相同
```

兩個 instance 的**型別不同**（`f` 不同），**實作相同**（`rfl` 證明）。
這就是「`f` 是活的參數」——不需要第二支演算法。

計費是真的（`#guard_msgs` 釘住）：

```
#eval (insertionSortCounted #[8,7,6,5,4,3,2,1] 0).run
-- DivM.res ((), #[1, 2, 3, 4, 5, 6, 7, 8], 28)
```

n=8 做了 28 次比較（= 8·7/2），界限是 8·8 = 64。

## 4. 這一步淘汰了什麼、淘汰不了什麼

**淘汰**：
- bogosort——證不出任何界限
- 「換一個複雜度等級就得換一份規格」——由 (b) 解決

**淘汰不了**（必須明寫，它們是後面幾步存在的理由）：
| 洞 | 為什麼還活著 | 第幾次處理 |
|---|---|---|
| 做滿比較但一次都不 tick | `ticks = 0 ≤ f n` ✓ 通過 | 07 |
| 老實計費，最後 `ticks := 0` | 後條件只有上界 | 06 |
| 分身計數器 | 見 `Cheats/Unresolved_FakeCounter.lean` | 09（**已知無解**） |

## 5. ⚠ 三層目標：只承諾了第一層

| | 要證明什麼 | 現況 |
|---|---|---|
| **(i)** | `f` 真的是參數 | ✅ **完成**——同一支實作、兩個不同的 `f` |
| (ii) | 介面可重用（不同演算法、同一個 `f`） | ⬜ 氣泡排序仍 BLOCKED（第 03 次起） |
| (iii) | **跨複雜度等級** | ❌ **已知缺口，見下** |

### 5.1 (iii) 是 Lean 側比 F\* 側弱的地方——不含糊帶過

F\* 那邊的 `array_sort` 有**三個不同等級**的界限：

```
insertion sort : fun n => n * (n - 1) / 2
merge sort     : fun n => if n > 0 then 4 * n * log2_ceil n + 4 * n else 0
heapsort       : heapsort_sort_bound
quicksort      : fun n => n * (n - 1) / 2          ← 與 insertion sort 一字不差
```

**我們這邊目前只有一個等級**（二次）。兩個 `f` 雖然不同，但同屬 Θ(n²)。

所以 (i) 證明的是「`f` 這個參數在型別層是活的」，
**不是**「rubric 已經涵蓋了不同複雜度等級的演算法」。這兩件事不要混為一談。

已列入第 10 次稽核表。

### 5.2 補 (iii) 最便宜的路：binary insertion sort（將來的選項，本次不碰）

不是 merge sort。**binary insertion sort**——插入排序的形狀，但用二分搜尋定位插入點：

- 比較次數 `n⌈log n⌉` ← **真的換一個等級**
- 寫入次數仍是 O(n²)，但我們**只計比較**，所以不影響 `f`
- 實作結構與現有的插入排序幾乎一樣，是唯一「改動最小、`f` 卻換等級」的選項

記在這裡當作將來的選項。

### 5.3 另外修正一個先前的錯誤判斷

第 03 次的 Notes 曾主張「把氣泡排序延到第 04 次可以一次買到兩個結論（介面可重用 + 兩種複雜度）」。
**這個理由是錯的**：氣泡排序的最壞情況比較次數是 `n(n−1)/2`，**跟插入排序一模一樣**。
所有簡單的二次排序（選擇排序、雞尾酒排序）都是同一個界限；
F\* 那邊 `insertion_sort` 與 `quicksort` 的界限一字不差也是同一件事。

延後氣泡排序只買得到 (ii)，買不到 (iii)。決定不變（仍然延後），但理由更正如上。

## 6. 遇到的問題

### 6.1 ★ `@[grind]` 屬性**主動破壞了不相關的目標**

這是自動化屬性預算表存在的理由，第一次真的發生。

想證緊界限 `2 * ticks = n * (n-1)` 時，缺的是一步非線性 Nat 算術，
於是加了一條看起來完全無害的引理：

```lean
@[grind]
theorem tick_step (n : Nat) (h : 1 ≤ n) : n * (n - 1) + 2 * n = (n + 1) * n
```

**結果**：`loom_solve!` 開始在**完全不相關的平凡目標**上失敗——

```
error: Failed to prove assertion
case a.left.right.left
if_pos : arrOld.size ≤ 1
⊢ SameElements arrOld arrOld        ← 這是 rfl
```

```
error: Failed to prove assertion
if_pos : arrOld.size ≤ 1
⊢ Sorted arrOld                     ← size ≤ 1 時平凡成立
```

**只要把 `@[grind]` 拿掉**（引理本身不動），這些平凡目標**立刻恢復**，
只剩下真正困難的那一個。已用受控實驗確認：

| 版本 | 早期 return 分支的平凡目標 |
|---|---|
| 有 `@[grind] tick_step` | ❌ 失敗 |
| 無 `@[grind]`（引理仍在） | ✅ 通過 |

**教訓**：屬性是全域的，而**一條正確的引理也可能是一條壞的自動化提示**。
自動化屬性預算表不是形式主義。

延伸的隔離實驗（每次只加一個變因，全部通過）：
- 只加 `mut ticks` 參數 → ✅
- 只加 `require ticksOld = 0` → ✅
- 只加 `import Mathlib.Tactic.Ring` → ✅
- 加 `@[grind] tick_step` → ❌

### 6.2 技術：**線性內層／非線性外層**

（給它一個名字，第 07、09 次會再需要它，那時的計數推理只會更複雜。）

直接寫 `invariant 2 * ticks = n * (n - 1) + 2 * (n - mind)` 會讓 grind 的預算爆掉。

可行的寫法是在內層迴圈前綁一個 `let t0 := ticks`，然後：

```lean
invariant ticks = t0 + (n - mind)     -- ★ 完全線性，沒有乘法
invariant t0 ≤ n * n                  -- 乘法只出現在這裡，且是不變的
```

把非線性的部分留在外層，內層保持線性。

**已重複使用**：第 05 次的 `insertionSortRel` 直接沿用同一個形狀
（多綁一個 `t_in := ticks` 當整支方法的起點）。

### 6.3 緊界限 `n(n−1)/2`：兩次嘗試未過（R8）

| 嘗試 | 形式 | 結果 |
|---|---|---|
| 1 | 等式 `2 * ticks = n * (n - 1)` | 卡在外層 invariant 的非線性推進步 |
| 2 | 不等式 `2 * ticks ≤ n * (n - 1)` | 同一步，同樣卡住 |

顯然的補法（`@[grind] tick_step`）就是 §6.1 那個**反而更糟**的做法。
把引理改成局部傳入（`grind [tick_step]`）也沒能收掉。

依 R8 停手。**這不影響目標 (i)**——(i) 只需要「兩個不同的 `f`」，不需要「最緊的 `f`」。
但它確實讓我們離 (iii) 更遠：連同一等級內的緊界限都還沒證出來。

### 6.4 `omega` 不碰非線性原子

`ticks ≤ n*n → ticks ≤ n*n + n` 這種「加一個非負項」的推理，
`omega` 會拒絕（它看到 `n*n` 就放棄），要改用 `le_trans h (Nat.le_add_right _ _)`。

## 7. 仍然活著的洞

| 洞 | 第幾次處理 |
|---|---|
| 遞迴／連續呼叫的界限疊不起來（`require ticksOld = 0` 的直接後果） | 05 |
| 老實計費，最後 `ticks := ticksOld` | 06 |
| 做滿比較但不呼叫計費的比較器 | 07 |
| 實作繞過比較器直接 `x < y` | 08 |
| **計數器分身** | 09（已知無解） |
| (ii) 介面可重用 | BLOCKED（氣泡排序） |
| (iii) 跨複雜度等級 | 已知缺口，見 §5.1 |
