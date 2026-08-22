# 第 03 次優化 — Notes

## 1. 這一步做了什麼

把「共用 predicate」（Level A，第 02 次已達成）升級成「共用完整 contract」（Level B）：
定義 `structure SortImpl`，把 **implementation 與它的 `triple` evidence 綁成一個值**。
淘汰「多一條前條件」這類作弊——它們不會讓實作變錯，但會讓 rubric 失去意義。

## 2. 與指引草稿碼的差異

| 指引寫的（§6.3） | 本檔實際 | 為什麼 |
|---|---|---|
| `sort : Array Int → VelvetM (Array Int)` | `Array Int → VelvetM (Unit × Array Int)` | `mut` 併進回傳 tuple（`Velvet/Syntax.lean:330-337`） |
| `spec : ∀ a, [part\| triple True (sort a) …]` | 改用顯式 `open PartialCorrectness PartialCorrectness.DemonicChoice in` | `[part\|` **有歧義**（Loom 與 Velvet 各定義一個同名記號），在 `structure` 欄位裡編不過 |
| （未提） | 橋接用 `triple_cons` | Loom **有** consequence rule，指引沒提到。見 `Opt02_Notes.md` §3.3 |
| 「再寫第二支…確認兩支的型別一字不差」 | ⚠ **只交出一支正確實作**，見 §5 | 氣泡排序的證明兩次都沒過，依 R8 停手回報 |

`structure` vs `class` vs 函式+proof 參數 vs Σ-bundle：本檔選 `structure`，教學最直觀。
**這不是型別論上唯一的路**——`class` 的差別只在能不能靠 instance resolution 自動找到實作，
對「審查者只讀規格」這個目的沒有影響。已在檔內註明。

## 3. 驗證：應該死掉的作弊

### `Cheats/Opt03_Cheat_ExtraPrecondition.lean` — `RestrictedSort`

**這一支跟第 02 次的 `insertionSort` 只差一行 `require 1 ≤ arr.size`。**
（官方 `Velvet/Examples/Examples.lean:52` 就是這樣寫的，所以不是杜撰的作弊。）

它在第 02 次是**完全合格**的：

- `prove_correct` 綠燈
- `#print axioms RestrictedSort_correct` = `[propext, Classical.choice, Quot.sound]`——**真定理，不帶 sorryAx**
- `#eval` → `DivM.res ((), #[2, 3, 5, 8])`——它真的會排序

第 03 次殺掉它的方式，**是型別錯誤，不是證明失敗**（已用 `#guard_msgs` 釘進 build）：

```
error: Type mismatch
  RestrictedSort_correct
has type
  ∀ (arrOld : Array ℤ),
    {have arr := arrOld;
      1 ≤ arr.size}RestrictedSort arrOld{x,match x with
      | (u, arr) => SameElements arrOld arr ∧ Sorted arr}
but is expected to have type
  ∀ (a : Array ℤ), {True}RestrictedSort a{r,SortSpec a r.2}
```

**強度差別**（延續第 06 次會再用到的分類）：

| | 第 02 次擋作弊 | 第 03 次擋作弊 |
|---|---|---|
| 手段 | 證不出來（`prove_correct` 失敗） | **寫不出來**（型別檢查器拒絕） |
| 留下什麼 | `sorryAx`（受控） | 什麼都沒有——連宣告都不成立 |

## 4. 驗證：應該活下來的正確實作

`insertionSortImpl : SortImpl`，橋接就是第 02 次量出的那一行 `triple_cons`。

```
'SortRubric.Opt03.insertionSortImpl' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`bash SortRubric/check_build.sh --with-selftest` 四關全過。

### 4.1 一個值得單獨講的觀察：`sort` 欄位不具鑑別力

```lean
def notASort : Array Int → VelvetM (Unit × Array Int) :=
  fun a => pure ((), Array.replicate a.size 0)
```

它的型別與 `SortImpl.sort` **一字不差**。所以第 03 次買到的**不是**「型別擋掉了作弊」——
`sort` 欄位對 `notASort` 跟對 `insertionSort` 一視同仁。

買到的是：**`spec` 與 `sort` 被綁在同一個值裡，交件者不能只交前者。**

兩支作弊合起來才說完 Level B 的內容：

| 作弊 | 型別對嗎 | 擋在哪 |
|---|---|---|
| `notASort` / `ZeroFill` | ✅ `sort` 欄位收得下 | `spec` 造不出來（第 02 次已釘） |
| `RestrictedSort` | ❌ | `spec` 的**前條件形狀**不符 |

## 5. ⚠ 未完成的部分：第二支正確實作（R8）

指引 §6.3 的驗收要求「再寫第二支…確認兩支的型別一字不差」。**這一項沒有完成。**

### 做了什麼

目標選了**氣泡排序**（真正不同的演算法，而非變體）。兩次嘗試都沒過：

| 嘗試 | 設定 | 結果 |
|---|---|---|
| 1 | `splits 40`, `maxHeartbeats 2000000` | `(deterministic) timeout at whnf` + `not a triple: _inhabitedExprDummy` |
| 2 | 同上 invariants，`maxHeartbeats 10000000`（2 分 01 秒跑完，非資源問題） | 三條內層 invariant `Failed to prove assertion`（第 31–33 行） |

用的 invariant 組合（外層尾段已排好 + 尾段 ≥ 前段；內層 running max + 前兩者 + multiset）
對 `loom_solve!` 不足。第二次不是超時，是**invariant 真的不夠**——需要更精細的
「內層掃描把最大值冒到 `i-1`」的敘述。

### 依 R8 停手

同一個障礙兩次未解，**不繞過、不自己改小目標**，在此回報。

### 這一項對第 03 次的核心結論**沒有影響**

Level B 的內容是「contract 被釘成一個型別，形狀不符的交不進來」，
而這一點由 `RestrictedSort`（型別錯誤）與 `notASort`（型別對但 spec 造不出來）
兩面**已經完整展示**。第二支正確實作證明的是「介面可重用」，是加分項，不是核心。

### 需要決定

| 選項 | 說明 |
|---|---|
| A | 花額外預算把氣泡排序或選擇排序證出來（指引 §6.3 也允許「直接複用一個變體」，但變體證明不了「介面可重用於不同演算法」） |
| B | 接受目前狀態，把第二支實作延到第 04 次（那時 `ArraySort (f)` 會有兩個不同的 `f`，正好需要兩支不同複雜度的演算法） |
| C | 記為永久已知限制 |

**建議 B**：第 04 次要把 `f : Nat → Nat` 升格成 rubric 參數，
「一種複雜度一份規格」這個洞本來就需要至少兩支**不同複雜度**的演算法才展示得出來。
在那裡付這筆成本，一次買到兩個結論。

## 6. 仍然活著的洞

| 洞 | 預計由第幾次處理 |
|---|---|
| 完全不談成本（比較次數） | 04 |
| 一種複雜度一份規格（`f` 寫死在後條件裡） | 04 |
| 遞迴呼叫的界限疊不起來 | 05 |
| 老實計費，最後 `ticks := ticksOld` | 06 |
| 比較器不計費 / 亂回答 | 07 |
| 實作繞過比較器 | 08 |
| **計數器分身** | 09（已知受限） |

## 7. 遇到的問題 / 未解決

### 7.1 氣泡排序（見 §5）— 依 R8 回報，待決定

### 7.2 `@[grind]` 依賴鏈在這一步得到印證

第 02 次記下的那條鏈：

```
ensures Sorted arr 沒有 @[grind] → loom_solve! 卡住 → 規格只能就地展開
  → 沒有具名 predicate → 第 03 次的 interface 抽象不成立
```

第 03 次的 `SortImpl.spec` 欄位型別是 `∀ a, triple True (sort a) (fun r => SortSpec a r.2)`，
**直接引用具名的 `SortSpec`**。若第 02 次沒有把 `Sorted`/`SameElements` 標成 `@[grind]`，
這個欄位就只能寫成一大串就地展開的式子，而「審查者只讀 3 行」的賣點也就沒了。

**這條鏈現在是被驗證過的，不是預測。**
