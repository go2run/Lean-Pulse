# 第 07 次 Notes — M2 面 1：比較器必須誠實

**檔案**：`Opt07_InstrOrder.lean`、`Opt07_Tests.lean`
**Cheats**：`Opt07_Cheat_LyingComparator.lean`（死）、
`Unresolved_BypassWithInt.lean`（活，第 08 次的理由）、
`Unresolved_DiscardCmpTicks.lean`（**活，無解**）
**time-box**：2 個工作段（實際約半段）
**結局**：面 1 三條子句全部到位；兩個買不到的東西都有活著的作弊當證據

---

## 1. D-3 定案的實測驗證

純函式 `cmp : Int → Int → Ticks → Bool × Ticks`，不是 monadic。

指引 §5.2.1 說的兩個好處都成立：

| | 實測 |
|---|---|
| 迴圈本體形狀不變 | ✅ 只多兩行（`let r := …` / `ticks := r.2`），巢狀結構完全沒動 |
| 規格是等式／iff，grind 可直接當 rewrite | ✅ `correct` / `charged` 掛 `local grind` 之後**第一次就過，17 秒** |

D-07 當初對支撐理由的更正（monadic 版**不會**踩 mut-call bug，
因為 `iord.cmp` 是 structure 欄位不是 Velvet method）維持成立；
真正的理由就是上表第二列。第 08 次的主要風險是 grind 失去對序的推理能力，
而等式是唯一 grind 直接吃得下的形式。

### 唯一一條要手寫的引理

```lean
theorem InstrOrder.correct_false (o : InstrOrder) (x y : Int) (t : Ticks) :
    (o.cmp x y t).1 = false ↔ ¬ (x ≤ y) := by
  rw [← o.correct x y t]; cases h : (o.cmp x y t).1 <;> simp
```

`if` 的 else 分支給的是 `(cmp x y t).1 = false`，grind 不會自己把它接回
`¬ (x ≤ y)`。這是先前 probe 卡住的那一點——**與純／monadic 無關**，
monadic 版會需要同一個事實，只是包在 triple 裡更難拿。

### 自動化：`local grind` 第二次派上用場

```lean
attribute [local grind] Ticks.val_bump
  InstrOrder.correct InstrOrder.charged InstrOrder.correct_false
```

四條全部 `local`。R15 不觸發，`AttributeBudget.md` 不需要加列
（已在該檔的「明確不掛全域屬性」表記錄）。
第 06 次發現的這條路現在是 07/08 的預設做法。

## 2. 面 1 的三條子句，逐條對到堵住的洞

| 子句 | 堵住 | 證據等級 |
|---|---|---|
| `cmp` 吃一個 `Ticks` 參數 | 不帶計數器就比較 | 型別 |
| `charged : (cmp x y t).2.val = t.val + 1` | 呼叫了但不計費 | **證明失敗** |
| `correct : (cmp x y t).1 = true ↔ x ≤ y` | 呼叫了但不用結果，自己瞎猜 | **證明失敗** |

⚠ 後兩列**不是型別錯誤**。`cmp` 欄位的型別對誰都一樣，作弊者寫得出
那個函式；他寫不出來的是兩個**欄位的證明**。kill 表已誠實標註。

### 證據做了兩層

1. **具體嘗試失敗**：`freeCmp`（不計費）、`alwaysTrue`（永遠回 true）
   各釘住逐字失敗目標
2. ★ **一般性的不可能**：三條全稱量化在 `o : InstrOrder` 上的定理——
   `no_free_cmp`、`no_constant_cmp`、`no_constant_false_cmp`。
   它們說的是「**沒有任何** `InstrOrder` 做得到」，不只是「我這樣寫不出來」

第二層比第一層強，也比它穩定：訊息格式會隨版本變，定理不會。
而且它們不需要建構任何 `Ticks`（量化在「假設你手上有一個 `t`」之上），
所以 R16 不受影響。

**R12 正向控制組**：`honestInt` 兩條欄位都證得出來，`#print axioms` 只有
`propext`。⇒ 面 1 不是不可能滿足的，它只是要求誠實。

## 3. ★ 這一步實質改變的一件事

第 06 次的排序自己寫 `ticks.bump`；第 07 次的排序 body 裡**一行都沒有**。

> **計費從「實作的自律」變成「比較器的副產品」。**

`Opt07_Tests.lean` §1 的 28 這個數字，完全來自 `honestInt.cmp` 的 `charged`。

## 4. 買不到的兩件事（都有活著的作弊）

### (1) 強迫實作去用 `iord` —— 面 3 的工作

`Unresolved_BypassWithInt.lean`：收下 `iord`，body 裡出現 **0 次**，
直接 `arr[mind]! < arr[mind - 1]!`。綠燈。

**它必須通過。** 如果它在第 07 次就死了，代表面 1 做了面 3 的工作，
兩步的分工就講錯了（指引 v1 附錄 A 曾經把它列成 07 淘汰，v2 §5.2.4 已修正——
這裡是那條修正的實測確認）。

### (2) 「呼叫 `cmp` 必定讓**實作的**計數器 +1」

`charged` 講的是「`cmp` **回傳**的計數器 = **傳進去**的 +1」。
沒有講「實作的計數器 +1」。

`Unresolved_DiscardCmpTicks.lean`：

```lean
let fake := ticks                                 -- 複製
let r := iord.cmp arr[mind]! arr[mind - 1]! fake  -- 誠實的比較器，誠實地計費
if r.1 then swap! …                               -- 用了答案
mind := mind - 1                                  -- 沒有 ticks := r.2
```

比較器從頭到尾都是誠實的。**不誠實的是「哪一個計數器被計」。**
它做滿 28 次比較、每次都經過 `honestInt`、報 0，
而且住得進 `ArraySort (fun _ => 0)`。

## 5. ★★ 三支作弊、一個根因（第 06 次那個發現的第三種穿法）

| 作弊 | 做的事 | 第 06 次 | 第 07 次 | 第 08 次（預期） |
|---|---|---|---|---|
| `ResetToOld` | 複製 → 對本尊計費 → 放回複製品 | 活 | 活 | 活 |
| `FakeCounter` | 複製 → 對複製品計費 | 活 | 活 | 活 |
| `DiscardCmpTicks` | 複製 → 餵給 `cmp` → 丟掉回傳 | — | **活** | **活** |
| `BypassWithInt` | 根本不呼叫 `cmp` | — | 活 | **預期死** |

前三列都只做一件事：**複製一個 `Ticks` 值**。

第四列與前三列的差別值得記下來：
**第 08 次強迫實作「經過比較器」，但強迫不了它「把帳算在自己頭上」。**

## 6. 與 F\* 的形狀差異（誠實記錄）

F\* 的 `instrumented_total_order a ord ctr` 把**計數器烤進比較器的型別**——
比較器只能對 `ctr` **那一個**計數器計費。

我們的 `cmp` 對**你遞給它的任何一個** `Ticks` 計費。

對照表那一列標「**弱：`ctr` 沒烤進型別**」。
§4(2) 正是這個差異的可觀察後果，不是理論上的顧慮。

## 7. R13 遷移成本

| 對象 | 成本 |
|---|---|
| 排序 method | 多一個參數；`ticks.bump` → `let r := iord.cmp …` + `ticks := r.2`。17 秒證完 |
| `ArraySort` + 橋接 | 多量化一個 `iord`；橋接仍是那一行 `triple_cons`（第五次） |
| `compose_two` | 證明本體**一字未改**，只多帶一個 `iord` |
| SPOTs | `Opt07_Tests.lean`，四組全部第一次就對 |

`Opt05b` 的 `SameElements.size_eq` 從第 05.5 次到現在**完全沒動過**——
三次型別遷移都不影響它，因為它談的是陣列不是計數器。

## 8. R14 —— kill 表單調性證據

```
$ bash SortRubric/check_build.sh --with-selftest
[0/3] 守衛自己的負向測試   ✓（5 項）
[1/3] import 隔離          ✓（含 R16 白名單列舉）
[2/3] lake build SortRubric ✓ 綠
[3/3] 完整 lake build       ✓ 失敗集合與 baseline 逐字相同
```

死者名單**增長 1**：新增 `LyingComparator`（證明失敗）。
既有八支全部維持死亡。

## 9. 對第 08 次的交代

- `Unresolved_BypassWithInt.lean` §3 已經寫好第 08 次要怎麼殺它，
  以及**會讓它靜默復活**的三個 typeclass（`DecidableRel` / `DecidableEq` / `FinEnum`）
- `InstrOrder` 要多兩個參數變成 `InstrOrder (α) (ord : SpecOrder α)`；
  `correct` 的右邊從 `x ≤ y` 換成 `ord.le x y`
- `correct_false` 要跟著改，而且**會變難**：現在 `¬ (x ≤ y)` 靠 `Int` 的
  可判定性，抽象版要走 `ord.total`
- 依 D-08 的階梯，08a（面 3 的鑑別內容）不需要完整排序，
  `BypassWithInt` 的型別錯誤就是面 3 達成的證據
