# 第 06 次 Notes — M1 抽象 `Ticks`

**檔案**：`Opt06_Ticks.lean`、`Opt06_MonotonicTicks.lean`、`Opt06_Tests.lean`
**Cheats**：`Opt06_Cheat_ForgeZero.lean`（死）、`Unresolved_ResetToOld.lean`（**活**）
**time-box**：2 個工作段（實際約 1 段）
**結局**：機制做出來了，但**它殺的不是指引預期的那一支**

---

## 1. 一句話結論

> **`private mk` 管「造」，管不到「複製」。
> 而 `ResetToOld` 從頭到尾只需要複製。**

指引 v2 §1.3 把 `ResetToOld` 列在「預定死於第 06 次」。實測它沒死，
而且證明只花 12 秒。它現在叫 `Unresolved_ResetToOld.lean`。

## 2. ★ 四格表（全部有機械證據）

| | 歸到**起點以下**（`ticks := 0`） | 歸到**起點**（`ticks := t_in`） |
|---|---|---|
| `Nat`，無守衛 | ✅ 通過 | ✅ 通過 |
| `Nat` + `ensures ticksOld ≤ ticks` | ❌ `⊢ ticksOld ≤ 0` | ✅ 通過 |
| 抽象 `Ticks` | ❌ **型別錯誤** ×4 | ✅ 通過（完整插入排序） |

證據位置：上兩列在 `Cheats/Opt06_Cheat_ForgeZero.lean`，
下一列與整張表在 `Cheats/Unresolved_ResetToOld.lean` §1、§3。

由這張表得到的精確陳述：

> **抽象 `Ticks` ≡ `ensures ticksOld.val ≤ ticks.val`。**
> 兩者擋住的集合一模一樣：都只保證終值不低於起點。

### 指引 §5.1.1 的說法要修正

指引說 `ensures ticksOld ≤ ticks`「**從來不是在擋歸零**，它擋的是
『減到起點以下』」。前半句不精確：**「歸零」和「減到起點以下」在
`ticksOld = 0` 以外的所有情況下是同一件事**，而那條後條件確實擋得住它
（第二列左格是紅的）。

真正該說的是：**它擋不住的是「歸到起點」，而抽象 `Ticks` 也擋不住。**

## 3. ★★ `ResetToOld` 與 `FakeCounter` 是同一支作弊

```lean
-- ResetToOld ：複製 → 對本尊計費 → 把複製品放回去
let t_in := ticks;      … ticks := ticks.bump …;  ticks := t_in

-- FakeCounter：複製 → 對複製品計費 → 從不碰本尊
let mut fake := ticks;  … fake  := fake.bump  …
```

兩者都只做一件事：**複製一個 `Ticks` 值**。

**所以「計數器身分」這個缺口不是第 09 次才出現，它從第 06 次就在了，
而且是同一個缺口。** 這把第 09 次的結論提前了三步，也把它的份量放大了：
面 2 不是一個「最後一步做不到的加分項」，它是**從計數器一出現就在的洞**。

對第 09 次的影響：E1（在新型別下重跑 `FakeCounter`）的答案已經知道了——
還活著，而且 `Unresolved_ResetToOld` 就是它的另一半證據。
第 09 次的重心（精確的不可能性陳述 + feature request）不變，但它現在
有兩支活著的作弊當佐證，不是一支。

## 4. 這一步實際買到什麼

**買到（真的）**

1. **kill 表的第一列「型別錯誤」**：`ForgeZero`——「無視呼叫端的起點，
   直接報 0」。它在第 05 次是綠的（相對界限對 `ticks = 0` 恆成立），
   在第 06 次連 elaboration 都過不了。四條偽造路徑全部釘住逐字錯誤。
2. **`ticksOld ≤ ticks` 變成結構性質**：不需要有人寫下來、不需要有人證。
   「忘記加一條 `ensures`」這個失效模式消失了。這一點後條件版做不到——
   不是強度差別，是**失效模式**差別。

**買不到**

1. `ResetToOld`（§2、§3）
2. 分身 / `FakeCounter`（同上，同源）
3. 「終值反映真正的比較次數」——這從來就不是上界規格講得出來的事

## 5. 遷移成本（R13）

`ArraySort` 換形狀，同一個 commit 內遷移完的東西：

| 對象 | 成本 |
|---|---|
| `insertionSortRel` → `insertionSortTicks` | **4 處**：參數型別、`t_in := ticks.val`、`ticks.bump`、invariant/ensures 加 `.val`。16 秒證完 |
| `ArraySort` + 橋接 instance | 橋接仍是那一行 `triple_cons`，第四次只換投影 |
| `Opt05b` 的 `compose_two` | 證明本體**一字未改**，只有算術多 `.val`。`SameElements.size_eq` 完全沒動 |
| SPOTs | 移進 `Opt06_Tests.lean`（R16），`#eval` 改成先 map 到 `Nat` 再 `.extract` |

### 一個沒踩到的坑

`VelvetM.extract` 需要 `[Inhabited α]`，而 α 是整個回傳 tuple。
直接 `#eval (insertionSortTicks …).extract` 會要求 `Inhabited Ticks`——
**那正是禁止清單的第一條**。

解法是先在 `VelvetM` 裡 map 成 `Nat` 再 `.extract`：

```lean
#eval (do let r ← insertionSortTicks … ; pure r.2.2.val : VelvetM Nat).extract
```

如果沒注意到，很可能會為了讓 `#eval` 跑起來而 `deriving Inhabited`，
**M1 就在那一行靜默失效了**。這是禁止清單第四條（typeclass 洩漏）
最可能的真實觸發路徑，值得寫進指引。

## 6. 自動化：`attribute [local grind]` —— 一個比預算表更好的答案

`Ticks` 是 structure，`loom_solve` 對它沒有原生支援；每條關於 `.val` 的
算術都要餵 `val_bump`。而 `loom_solve` **不吃引理參數**
（`Loom/CaseStudies/Tactic.lean:65`：`syntax "loom_solve" : loom_solve_tactic`，
沒有 `(term,*)`），所以 `grind [Ticks.val_bump]` 這條路走不通。

指引 §5.1.5 預期會被迫上全域屬性（R15 預算表 + 全量 rebuild）。實測有第三條路：

```lean
attribute [local grind] Ticks.val_bump
```

`local` 屬性**不會外洩給 import 這個模組的人**。第 04 次的 `tick_step` 事故
（一條*正確*的引理讓三步前的平凡目標失敗）整個是「全域」造成的；
`local` 從結構上消掉那一類風險。

⇒ 依 P1 這算 local，**`AttributeBudget.md` 不需要為第 06 次加列**，
R15 不觸發，P2 的全量 rebuild 也不必要（但還是跑了，見 §8）。

已把這條寫進 `AttributeBudget.md` 的「明確不掛全域屬性」表——
它應該是後續 07/08 的預設做法。

## 7. R16 的實作：一個「完整列舉」的檢查

`Ticks` 的公開起點 `mkForTesting` 由 `check_isolation.sh` 隔離。
這個檢查之所以**完整**（不是抽樣），理由是可以講清楚的：

> `Ticks.mk` 是 private，作用域 = `Opt06_Ticks.lean` 這個模組。
> 所以模組外每一個造出 `Ticks` 的地方都必須寫出 `mkForTesting` 這個字。
> ⇒ 列舉這個字串 = 列舉模組外的全部建構點。

實作細節：

- **fail-closed**：白名單是 `Opt06_Ticks.lean`（定義處）／`Opt10_Audit.lean`／`*_Tests.lean`，其餘一律失敗
- **剝註解**：`strip_comments.py` 先把 Lean 的巢狀 `/- -/`、`--`、字串常值處理掉，只看程式碼。否則檔頭沒辦法解釋 R16（第一版就被自己的檔頭擋下來了）
- **`_private` 逃生門**：Lean 的 private 名稱在 olean 裡是 `_private.<module>.<n>.<name>`，理論上打得出來。一併堵上
- **兩支負向測試**（`check_selftest.sh` 4 與 5）：白名單外用它 → 必須拒絕；只在註解提到 → 必須放行

順手把指引 §5.5.1 的稽核漏洞 1 也修了：`check_isolation.sh` 的 catch-all
從 fail-open（未知位置 = 當成 toolchain = 通過）改成 fail-closed。

## 8. R14 —— kill 表單調性證據

```
$ bash SortRubric/check_build.sh --with-selftest
[0/3] 守衛自己的負向測試   ✓（5 項，含 2 項新的 R16 測試）
[1/3] import 隔離          ✓（含 R16 白名單列舉）
[2/3] lake build SortRubric ✓ 綠
[3/3] 完整 lake build       ✓ 失敗集合與 baseline 逐字相同
```

死者名單**增長 1**：新增 `ForgeZero`（型別錯誤）。
既有的七支（`ZeroFill`、刪元素、只留最小值、恆等、`ExtraPrecondition`、
bogosort、`LaunderPrecondition`）全部維持死亡——它們的失敗訊息都是
`#guard_msgs` 釘住的，任何一支復活都會讓 build 紅燈。

## 9. 對後續步驟的影響

| 步驟 | 影響 |
|---|---|
| **07** | `cmp : α → α → Ticks → Bool × Ticks`。實作可以複製 `ticks` 去餵 `cmp`，把結果的計數器丟掉——**這就是 `FakeCounter`**。所以面 1 的 `charged` 子句買到的是「呼叫 `cmp` 必定讓*它回傳的那個*計數器 +1」，不是「必定讓*實作的*計數器 +1」。這一點要在第 07 次的檔頭誠實標出來 |
| **08** | 無影響。面 3 談的是 α 的觀察途徑，與計數器無關 |
| **09** | E1 的答案已知（洞還在）。重心不變，但佐證從一支變兩支，而且可以把「面 2 從第 06 次就破了」寫成主線結論 |
| **10** | 保證強度表的「計數器造不出更小的」那一列要改寫：買到的是**造不出**，不是**降不下來** |

## 10. 一個值得記下來的張力

相對界限（第 05 次）與計數器身分（第 09 次）**互相拉扯**：

- 相對界限 `ticks ≤ ticksOld + f n` **要求**實作收下一個計數器（否則 `ticksOld` 無從談起）
- 而收下的那一刻，實作就有一個**可以複製**的值

換句話說，第 05 次為了換到「界限可組合」，付出的代價正好是第 06/09 次
想擋的那個洞。指引 §5.4.2 的 E3（「不吃 `Ticks` 的 `sort` 是否可行」）
答案因此可以現在就寫下來：**不可行，而且理由不只是「呼叫不了 `cmp`」——
是相對界限本身需要它。**
