# 第 08 次 Notes — M2 面 3：抽象元素型別 α

**檔案**：`Opt08a_AbstractCore.lean`
**Cheats**：`Opt08_Cheat_BypassWithInt.lean`（**死**，型別錯誤）
**time-box**：08a 2 個工作段（實際約半段）／08b 2 個工作段（用完）
**結局**：**08a 綠 ⇒ 面 3 達成**。08b `BLOCKED`（R8，兩次未過）

---

## 1. 面 3 達成，證據是型別錯誤

四條繞過路徑全部在 elaboration 就被拒絕，`loom_solve` 根本沒機會跑：

| 路徑 | 錯誤 |
|---|---|
| `if ord.le a[0]! a[1]! then` | `failed to synthesize Decidable (ord.le a[0]! a[1]!)` |
| `decide (ord.le a[0]! a[1]!)` | 同上 |
| `if a[0]! < a[1]! then` | `failed to synthesize LT α` |
| `if a[0]! = a[1]! then` | `failed to synthesize Decidable (a[0]! = a[1]!)` |

機制一句話：**`SpecOrder.le : α → α → Prop`，而 `if` 需要 `Decidable`；
`SpecOrder` 結構裡沒有那個欄位，也沒有任何辦法從別處生一個出來。**

這是本專案第三列「寫不出來」（前兩列是第 06 次的 `ForgeZero` 與
`ForgeMidpoint`），而且是**唯一一列完全不依賴自動化**的。

`Cheats/Unresolved_BypassWithInt.lean` 依命名規則第 2 條當場改名為
`Opt08_Cheat_BypassWithInt.lean`。檔案裡同時保留它在第 07 次通過的綠燈——
兩段對照才是完整論證。

## 2. ★★ 面 3 的保證等於「typeclass 假設清單保持乾淨」

這是本步最重要的發現，而且我把它從散文變成了 build 的一部分。

上面四條之所以是型別錯誤，靠的是 α **沒有任何可計算的結構**。
只要多寫一個假設，作弊就當場復活——**而且沒有任何錯誤訊息、任何警告**：

```lean
example [DecidableEq α] (a : Array α) : Bool :=
  if a[0]! = a[1]! then true else false                    -- ✓ 編譯成功

example [LT α] [DecidableLT α] (a : Array α) : Bool :=
  if a[0]! < a[1]! then true else false                    -- ✓ 編譯成功

example (ord : SpecOrder α) [∀ x y, Decidable (ord.le x y)] (a : Array α) : Bool :=
  if ord.le a[0]! a[1]! then true else false               -- ✓ 編譯成功
```

三段都在 `Opt08_Cheat_BypassWithInt.lean` §5，**故意編譯成功**。

> **這是本專案唯一一個「加了東西反而變弱、而且完全靜默」的失效模式。**
> 型別錯誤會叫、證明失敗會叫、`sorry` 至少 `#print axioms` 抓得到。
> 這一個什麼都不會發生。

### 所以它由 `check_isolation.sh` 守（fail-closed）

新增「面 3」段：剝掉註解之後 grep 整個 `SortRubric/`，
找 `[…DecidableEq…]` / `DecidableRel` / `DecidableLT` / `DecidableLE` /
`FinEnum` / `Decidable (ord.` / `[LT ` / `[LE ` / `[Ord ` / `[Min ` / `[Max `。

白名單只有一個檔：`Cheats/Opt08_Cheat_BypassWithInt.lean`
（它**故意**示範這三個陷阱）。其餘一律失敗。

負向測試 6 已加進 `check_selftest.sh`：把 `[DecidableEq α]` 放到白名單外，
隔離檢查器必須拒絕。

## 3. `Inhabited α` 的 R11 論證（實測版）

| | |
|---|---|
| **為什麼需要** | `a[i]!` 需要它；真正的阻塞點是 `Array.multiset_swap [Inhabited α]`（`Velvet/Std.lean:104`） |
| **它讓實作多做什麼** | 造得出一個 α 的值 ⇒ 抽象版的 `ZeroFill` |
| **為什麼可以接受** | `ZeroFill` 在第 02 次已被 `SameElements` 殺掉（機械反證）。而且 **`Inhabited` 不提供任何比較能力**——它給不出 `Decidable`，面 3 不受影響 |
| **完全避開的代價** | 改用 `a[i]'h`（帶證明的索引）⇒ spec 形狀改變 + 所有既有引理重寫。**收尾期不做這個交換** |

已記入 `AttributeBudget.md`。

## 4. `Array.toMultiset` 對抽象 α —— 風險清單那一格是綠的

指引把「`toMultiset` 需要 `DecidableEq`」列為**低機率、高衝擊**（08 直接卡死）。

實測**完全不需要**：`Array.toMultiset a = Multiset.ofList a.toList`
（`Velvet/Std.lean:102`），零 typeclass。

連帶好處：第 05.5 次的 `SameElements.size_eq` 在抽象版**照抄即可**
（它談的是陣列不是元素）。這是三次型別遷移都沒動過的那條引理。

## 5. ★ 08b BLOCKED —— 精確診斷

**兩次未過，依 R8 停手。**

### 卡在哪

不是整支排序，是**內層迴圈 swap 分支的序 invariant**：

```
if_pos_2 : (iord.cmp arr[mind]! arr[mind-1]! ticks).1 = true
⊢ ∀ i j, 0 ≤ i → i < j → j ≤ n → j ≠ mind - 1 →
    ord.le ((arr.set! mind arr[mind-1]!).set! (mind-1) arr[mind]!)[i]!
           ((arr.set! mind arr[mind-1]!).set! (mind-1) arr[mind]!)[j]!
```

### 兩次嘗試

| # | 做法 | 結果 |
|---|---|---|
| 1 | `local grind` 給滿（`trans`/`total`/`le_refl`/`not_le`/`correct`/`correct_false`/`Sorted`/`SameElements`），splits 40，4M heartbeats | ✗ swap 分支未過（22 秒） |
| 2 | 同上但 splits 100 | ✗ 同一個目標（20 秒） |

中間還做了一次診斷性的變化（拿掉 `trans`/`total`），結果**換成 else 分支失敗**——
那證實 `trans` 是 else 分支需要的（把 invariant 從 `j ≠ mind` 延伸到 `j ≠ mind-1`
時，`i < mind-1` 那格要 `ord.le arr[i] arr[mind-1]` 接 `ord.le arr[mind-1] arr[mind]`）。
所以兩條都要，而兩條都在的時候 swap 分支過不了。

### 為什麼這是證明工程而不是設計問題

**同一支排序在第 07 次（`α = Int`）17 秒就過。** 程式碼一字未改，
只有 `≤` 換成 `ord.le`。需要的事實完全相同——

- `j = mind`、`i < mind-1` ⇒ invariant_8 於 `(i, mind-1)`
- `j = mind`、`i = mind-1` ⇒ `if_pos_2` 經 `correct`
- `j > mind` 的三種 `i` ⇒ 三個 invariant_8 實例

**全部是 invariant_8 的直接實例，一次 `trans` 都不需要。**
差別只在 `Int` 版有 grind 內建的線性序理論可以幫忙 e-matching，
抽象版只剩下假設本身。

⇒ 這是 `grind` 在不透明 predicate 上的 e-matching 能力問題，
**與面 3 的論點無關**。

### 未走的路（留給後人）

手寫一條 swap 的引理，把索引的 case analysis 一次包好：

```lean
theorem swap_preserves_order (ord : SpecOrder α) (a : Array α) (m n : Nat)
    (hm : 0 < m) (hmn : m ≤ n) (hn : n < a.size)
    (hinv : ∀ i j, i < j → j ≤ n → j ≠ m → ord.le a[i]! a[j]!)
    (hswap : ord.le a[m]! a[m-1]!) :
    ∀ i j, i < j → j ≤ n → j ≠ m - 1 →
      ord.le ((a.set! m a[m-1]!).set! (m-1) a[m]!)[i]!
             ((a.set! m a[m-1]!).set! (m-1) a[m]!)[j]!
```

上面 §5「為什麼這是證明工程」那段就是它的證明大綱（五個 case）。
成本估計是 `Array.getElem!_set!` 相關引理的一場硬仗，
**依 R8 不在本次動手**。

## 6. ⚠ 誠實記錄：抽象版的 `ArraySort` 目前沒有住戶

08b BLOCKED 的直接後果：`Opt08a_AbstractCore.lean` 的 `ArraySort` **沒有 instance**。
唯一住得進去的東西是一支多型排序。

**一個沒有住戶的 rubric 鑑別不了任何東西**，這一點不能含糊。所以：

> **面 3 的結論由型別錯誤承擔，不由 rubric 的住戶承擔。**

四條繞過路徑的型別錯誤是**獨立**的證據——它們說的是
「任何實作都不能這樣寫」，那句話不需要有人真的寫出一支實作來佐證。

非空性（non-vacuity）由兩件已完成的事提供：

| 證據 | 說明什麼 |
|---|---|
| `minIndex`（2.8 秒證完） | 抽象的 `SpecOrder` + `InstrOrder` **可以做真正的序推理**，不是形式上呼叫一下 |
| `intOrder` / `honestInt` | 比較器側住得進去，`InstrOrder` 不是不可能滿足的（R12 正向控制組） |

缺的那一塊是「排序側住得進去」，那正是 08b。

## 7. 一個分工，就是 `InstrOrder` 存在的全部意義

`intOrder` 與 `honestInt` 用得到 `Int` 的可判定性（`decide (x ≤ y)`）。
**那完全正當**——那是**比較器的實作者**在做的事。

面 3 要擋的是**排序的實作者**：它只拿得到 `ord`（算不出來）與 `iord.cmp`（要付錢）。

> 比較器的作者知道 α 是什麼，當然可以用它的結構。
> 排序的作者不知道，所以只能問。

## 8. 附帶的漂亮結果

這一步把演算法課本的「**比較排序模型**」寫進了型別——
`sort` 能做的只剩比較與搬移。

⇒ **在這個 rubric 下寫不出 counting sort 或 radix sort**，因為它們要看 α 的內容。

F\* 那邊的旁證：AlgoStar 真的另立了一個
`array_counting_sort (a:eqtype) (key:a -> GTot nat) …`——
把 `Type` 放寬成 `eqtype`、把比較換成抽 key。

**型別的表達力剛好切在演算法理論的分類線上。**

## 9. R13 / R14

**R13**：`ArraySort` 換形狀。因為 08b BLOCKED，本步沒有 instance 要遷移；
`Cheats/Opt08_Cheat_BypassWithInt.lean` 已在同一 commit 內加上抽象版的四條路徑。
第 07 次的 `ArraySort` 與其 instance 原地保留，作為「第 07 次的快照」。

**R14**：死者名單**增長 1**（`BypassWithInt`），既有九支全部維持死亡。

```
$ bash SortRubric/check_build.sh --with-selftest
[0/3] 守衛自己的負向測試   ✓（6 項，含新的面 3 測試）
[1/3] import 隔離          ✓（含 R16 與面 3 兩張白名單）
[2/3] lake build SortRubric ✓ 綠
[3/3] 完整 lake build       ✓ 失敗集合與 baseline 逐字相同
```

## 10. 對第 09、10 次的交代

- **第 09 次**：四支同源作弊（`ResetToOld` / `FakeCounter` / `CopyThenRebump` /
  `DiscardCmpTicks`）全部不受第 08 次影響。E1 的答案確定：三刀下完，洞還在
- **第 10 次**：保證強度表新增兩列——
  「實作算不出 `ord.le`」（**編譯器**，✅ 08a）與
  「α 上沒有可計算 typeclass」（**腳本檢查**，`check_isolation.sh` 面 3 段）。
  後者是新的一級，比「證明」弱、比「人」強
- **第 10 次**：D3 檢查項要加 `Classical.dec`——它生得出 `Decidable`，
  所以路徑 1、2 用 `open Classical in` 寫得出來，
  但那會讓定義變 `noncomputable`、`#print axioms` 出現 `Classical.choice`、`#eval` 跑不動。
  **不靜默，所以不是面 3 的漏洞**，但要列進清單
