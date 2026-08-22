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

**但這不代表 M1 沒有內容**——見 §2 的第三欄。

## 2. ★ 三分法與完整的四格表

所有針對計數器的攻擊，取得「一個比較小的 `Ticks`」只有三種手段：

| 手段 | 例子 | 被什麼擋 |
|---|---|---|
| **造** | `ForgeZero`、`ForgeMidpoint` | ✅ **M1（`private mk`）** |
| **複製** | `ResetToOld`、`CopyThenRebump`、`FakeCounter` | ❌ 開著 |
| **丟棄** | `DiscardCmpTicks`（第 07 次新增） | ❌ 開著 |

**M1 恰好覆蓋三分之一。**

### 四格表（第三欄是後補的，而且它是關鍵）

| | `ticks := 0` | `ticks := t_in` | `ticks := ⟨t_in.val + 14⟩` |
|---|---|---|---|
| `Nat`，無守衛 | ✅ | ✅ | ✅ |
| `Nat` + `ensures ticksOld ≤ ticks` | ❌ `⊢ ticksOld ≤ 0` | ✅ | ✅ **通過（單調！）** |
| 抽象 `Ticks` | ❌ 型別錯誤 ×4 | ✅（完整插入排序） | ❌ **型別錯誤 ×3** |

證據：`Cheats/Opt06_Cheat_ForgeZero.lean`（第一欄）、
`Cheats/Unresolved_ResetToOld.lean`（第二欄）、
`Cheats/Opt06_Cheat_ForgeMidpoint.lean`（★ 第三欄）。

### ⚠ 我第一版的結論抽樣不足

第一版只測了前兩欄，得到「抽象 `Ticks` ≡ `ensures ticksOld ≤ ticks`」。
**那是假等價。** 第三欄把兩列分開了：

「老實計費 28 次、報 `t_in + 14`」是**單調**的，所以

- `ensures ticksOld ≤ ticks` 抓不到（`ticksOld ≤ ticksOld + 14` 成立）
- 任何 `≤` 形狀的上界／下界都抓不到
- **只有「你造不出那個值」抓得到**

而且它比 `ResetToOld` 危險：`ResetToOld` 只能報 `t_in`，所以只認證得了
`f _ = 0`（一眼就看得出荒謬）；`ForgeMidpoint` 報 `t_in + k`，k 任選，
**可以報一個看起來合理的數字**，人工 code review 也不容易起疑。

### 正確的陳述要分兩層

> 以「**可寫出的程式**」衡量：抽象 `Ticks` **嚴格強於**那條後條件。
> 以「**可達成的行為**」衡量：兩者**相同**——而這個塌陷是「複製」造成的。

第二層的機械證據是 `Cheats/Unresolved_CopyThenRebump.lean`：

```lean
let mut fake := t_in     -- 從複製品重來
… 只 bump 14 次 …
ticks := fake            -- 報 14
```

全程只用公開 API（`val` 讀、`bump` 推進），達成與 `ForgeMidpoint`
**完全相同**的可觀察行為。

**同樣的行為，一支寫不出來、一支寫得出來。**

⇒ **M1 的保證不是不存在，是被面 2 的洞遮住了。
面 2 一旦補上，M1 立刻變成一條實質的保證。**

這也是第 09 次那條不可能性定理的前半段——M1 是它的一個前提，
而且是**已經到手**的那個前提。

### 指引 §5.1.1 的說法要修正

指引說 `ensures ticksOld ≤ ticks`「**從來不是在擋歸零**，它擋的是
『減到起點以下』」。在 rubric 層（spec 對 `∀ t` 量化）**說反了**：
`ticks := 0` 的目標是 `⊢ ticksOld ≤ 0`，證不出來——**它擋得住歸零**。

它擋不住的是「歸到**起點**」與「報一個**單調的中間值**」。

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
1a. ★ **`ForgeMidpoint`**——老實計費 28 次、造一個中間值報 14。
   它是**單調的**，所以沒有任何 `≤` 形狀的後條件抓得到它。
   **這一支才是 M1 不可取代的證據**：它證明「造不出來」關掉了一整類
   後條件關不掉的作弊。
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
