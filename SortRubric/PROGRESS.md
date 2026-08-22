# SortRubric 進度

驗收指令：`lake build SortRubric`
（全域 `lake build` 有**既有**失敗 `VelvetLC917`，非本專案造成，詳見 `Opt00_Recon.md` §6）

| 第 N 次 | 名稱 | 狀態 | lake build | 淘汰的作弊 | 備註 |
|---|---|---|---|---|---|
| 00 | 環境勘查 | ✅ 完成 | ✓ 全過 | — | 4 問全部有答案；另產出 ERRATA、隔離證明、baseline 釘樁 |
| 01 | Sorted | ✅ 完成 | ✓ 全過 | （故意不淘汰） | `ZeroFill` 通過 `ensures Sorted a`，witness 已釘進 build |
| 02 | +SameElements | ✅ 完成 | ✓ 全過 | 3 個 | 橋接成本已量出：**1 行、零 simp** |
| 03 | Interface | ⚠ 大致完成 | ✓ 全過 | 1 個（多一條前條件） | **第二支正確實作未完成**（氣泡排序 2 次未過，R8），見 Opt03_Notes §5 |
| 04 | TicksAbsolute | ✅ 完成（目標 (i)） | ✓ 全過 | bogosort；一種複雜度一份規格 | (ii) 仍 BLOCKED；(iii) 記為已知缺口 |
| 05 | TicksRelative | ✅ 完成 | ✓ 全過 | （不防作弊） | ★ 帶 R12 控制組：同程式碼同語法、只換相對界限 → 通過 |
| 05.5 | Composition | ✅ 完成 | ✓ 全過 | （不防作弊） | ★ rubric 層界限可組合。做法 (a)：2 行 local 引理，**未動 spec**。兩組反向控制組 + 機械反證 |
| 06 | MonotonicTicks | ✅ 完成 | ✓ 全過 | 2 個（`ForgeZero`、`ForgeMidpoint`，皆**型別錯誤**） | ★ **結論與指引不同**：`ResetToOld` 沒死（複製≠建構）。三分法：M1 覆蓋「造」，「複製／丟棄」開著。`ForgeMidpoint`/`CopyThenRebump` 這一對證明 M1 的保證是**被遮住**不是不存在。見 ERRATA §G |
| 07 | InstrOrder | ✅ 完成 | ✓ 全過 | 1 個（`LyingComparator`，證明失敗） | 純函式 `cmp` 定案正確：**第一次就過，17 秒**。買不到的兩件事都有活著的作弊 |
| 08a | AbstractCore | ✅ 完成 | ✓ 全過 | 1 個（`BypassWithInt`，**型別錯誤**） | 面 3 達成。★ 面 3 的保證＝「typeclass 清單乾淨」，已由 `check_isolation.sh` fail-closed 強制 |
| 08b | AbstractSort | 🚫 BLOCKED | — | — | R8 兩次未過。卡在 swap 分支的序 invariant（`grind` 在不透明 predicate 上的 e-matching）。**與面 3 論點無關**，診斷見 Opt08_Notes §5 |
| 09 | SortM | ⬜ 未開始 | | | ★ 實驗性。**實驗 2 已提前完成：作弊通過** |
| 10 | Audit | ⬜ 未開始 | | | `#print axioms` 已確認可用 |
| 11 | Termination（選配） | ⬜ 未開始 | | | 代價已核實：三份 body |

## 第 00 次的重點結論

1. **分身計數器作弊實測通過**（最小版與完整插入排序版皆然）→ 第 09 次的 open problem 屬實
2. **`method` 回傳型別寫死 `VelvetM`**（`Velvet/Syntax.lean:343`）→ 第 09 次的 `SortM` 無法沿用 `method` 語法
3. `Array.toMultiset` 無 typeclass 需求 → 第 08 次不會 BLOCKED
4. `private mk` 三種偽造路徑全被跨模組擋下 → 第 06 次機制有效
5. 第 03 次的 bundle 可做到**零橋接證明**（需三個對齊條件，見 Recon §7.1）

## 動手前的決定（第 07、08 次）

### D-07：`InstrOrder.cmp` 用**純函式**，不是 monadic — ✅ 定案

```lean
-- 指引 §6.7 草稿（從 F* 抄來的形狀）
cmp : Int → Int → Ticks → VelvetM (Bool × Ticks)   ＋ triple 規格

-- 採用
cmp    : α → α → Ticks → Bool × Ticks
bills  : ∀ x y t, (cmp x y t).2 = t.bump
honest : ∀ x y t, (cmp x y t).1 = true ↔ ord.le x y
```

**面 1 的三條一條不少**：吃 `Ticks` 參數（不帶計數器就比不了）、
`.2 = t.bump`（沒有不計費的版本）、`.1 = true ↔ ord.le x y`（不能瞎猜）。

理由（`probe/PURE1.lean` 實測）：

| | 純函式 | monadic |
|---|---|---|
| 迴圈本體 | **一行 `let c := iord.cmp a b ticks`，形狀不變** | 每次比較變成一個 bind |
| 規格形式 | **等式** → grind 可直接當 rewrite | `triple` → 要穿過 WP |
| F\* 為什麼要 monadic | 它的計數器是**資源**，非得在 Pulse 裡動 | — |
| 我們的 `Ticks` | 是一個**值**，那層 `VelvetM` 是 cargo-cult | — |

**第 08 次的風險是 grind 失去對序的推理能力**，所以「規格是等式而非 triple」
這一點特別重要——它是唯一能讓 grind 直接用的形式。

> ⚠ 一處更正：原本的支撐理由說 monadic 版會踩到 mut-call bug。**不會。**
> 那個 bug 在 `method` 呼叫的 macro（`Syntax.lean:203-236` 查 `globalMutVarsCtx`），
> 而 `iord.cmp` 是 **structure 欄位**，不是 Velvet method，macro 不會改寫它。
> 真正的理由是上表的第二列。

**已驗證**：純版本 typecheck、誠實的 `Int` instance 造得出來、
塞進現有迴圈只多一行、`bills` + `val_bump` 掛 grind 後**計數 invariant 已通過**。
剩下的是 `honest` 與序推理的接線——那是第 07 次的證明工程。

### D-08：面 3 的 fallback 階梯 — ✅ 先講定

**關鍵認識：面 3 的鑑別內容是型別錯誤，根本不需要一支排序。**

面 3 要證的是「除了 `iord` 沒有別的觀察 α 的途徑」。它的機械證據是
**一支試圖繞過比較器的實作連型別檢查都過不了**——那不需要任何正確性證明。

| 層 | 內容 | 需要完整排序嗎 | 承諾 |
|---|---|---|---|
| **(a)** | 面 3 的鑑別內容：`Cheats/Opt08_Cheat_BypassWithInt` 直接寫 `x ≤ y` → 型別錯誤；`decide (ord.le x y)` → 無 `Decidable` 實例 | **否** | **必做** |
| (b) | rubric 可被實作（全多型插入排序住得進去） | 是 | 盡力；卡住就退到 (c) |
| (c) | 最小可住者（三元素／只有比較器接線的例子） | 否 | (b) 失敗時的合格交付 |

**(b) 失敗退到 (c) 不算妥協**——面 3 的論點由 (a) 完整承擔，
(b) 證的是另一件事（rubric 不是空的）。

風險來源已知：`Sorted` 換成 `ord.le` 之後，grind 對 `Int` 的原生序推理全部失效，
`trans` / `total` / `antisymm` 都要手動餵（U3，PROGRESS 已標高風險）。

**先講定，就不會在那裡卡兩輪才回報。**

## R11 追溯複查：現有「已淘汰」紀錄

判準：① 失敗目標指向規格中的某一條 ② 不是語法錯誤／unknown identifier／timeout
③ 有控制組（把作弊換成正確版本，確認它通過）。

| 作弊 | 失敗目標 | 指向規格哪一條 | 控制組 | 機械反證 | 判定 |
|---|---|---|---|---|---|
| `Opt02_Cheat_AllZeros` | `⊢ SameElements arrOld (Array.replicate arrOld.size 0)` | `SameElements` | 同檔 `correct_answer_passes`（Opt02） | ✅ `¬ SortSpec #[8,2,5,3] #[0,0,0,0]` | ✅ 成立 |
| `Opt02_Cheat_DropElements` | `⊢ SameElements arrOld #[]` | `SameElements` | 同上 | ✅ ×2 | ✅ 成立 |
| `Opt02_Cheat_MinOnly` | `⊢ SameElements arrOld #[m_1]` | `SameElements` | 同上 | ✅ | ✅ 成立 |
| `Opt02_Cheat_Identity` | `⊢ Sorted arrOld` | **`Sorted`** | 同上 | ✅ `rintro ⟨h, -⟩` | ✅ 成立 |
| `Opt03_Cheat_ExtraPrecondition` | `Type mismatch`：`{1 ≤ arr.size}` vs `{True}` | `ArraySort`/`SortImpl` 的**前條件形狀** | ✅ **新增** `UnrestrictedSort`＋`unrestrictedImpl`：同 body、拿掉 `require` 就裝得進去 | —（型別層，無 Prop 可反證） | ✅ 成立 |
| `Opt03_Cheat_LaunderPrecondition` | `⊢ True ≤ (have arr := a; 1 ≤ arr.size)` | `triple_cons` 的方向性 | ✅ 同檔「安全方向」對照可行 | — | ✅ 成立（規則守住） |
| `Opt05_Cheat_NoCompose` | `⊢ i_2 = 0`（case «require_1: ticksOld = 0»） | 絕對界限的隱含前條件 | ✅ **`sortTwiceRel`：同程式碼、同呼叫語法、只換相對界限 → 通過** | — | ✅ 成立（歸因於界限，非上游 mut-call bug） |

**四支 Opt02 的機械反證（`¬ SortSpec …`）是最高標準**——那個證明完全獨立於 elaboration 行為。
後續每一步能做機械反證就不要只靠錯誤訊息。

## 累積給第 10 次的稽核項

隨每一步累積，第 10 次一次做完。

| # | 項目 | 來源 | 軸 |
|---|---|---|---|
| A1 | `#print axioms` 對每一個交付的定義與定理 | 指引 §6.10 | D3 |
| A2 | 人工 grep `@[implemented_by]` / `unsafe` | 指引 §6.10 | D3 |
| A3 | `Classical.dec` / `classical` 會讓定義變 `noncomputable` | Recon §7.2 | D3 |
| A4 | **逐一核對每個實作的名字與它實際做的事** | 第 02 次（`insertionSort` 更名） | **D1** |
| A5 | 核對 `Cheats/` 狀態表第三欄：有沒有哪一條後條件從來沒殺過東西 | 第 02 次 | D4 |
| A6 | 核對兩張預算表（typeclass / 自動化屬性）每一列的理由是否仍成立 | 第 00、02 次 | D3 |
| A7 | 確認 `Cheats/` 的 `sorryAx` 都被 `#guard_msgs` 釘住且未外洩 | 第 02 次 | D3 |
| A8 | **記錄 (iii) 缺口**：F\* 有三個複雜度等級的界限，我們只有一個（二次）。兩個 `f` 不同但同屬 Θ(n²) | 第 04 次 | **D2** |
| A9 | 記錄「`f` 真的是那個複雜度等級嗎」——我們連緊界限 `n(n−1)/2` 都還沒證出來 | 第 04 次 | D2 |

> A4 不會讓 rubric 變強——原文說 D1 只能靠 plain old code review。
> **那就至少對自己做一次 code review，並把結果記下來。**

## BLOCKED

> **兩個 BLOCKED 都是「證明工程」，不是「rubric 設計」。**
> rubric 的主線（規格如何被收緊、作弊如何被淘汰）**一步都沒卡**。
> 這個區分很重要——兩個 BLOCKED 掛著容易讓人以為方法論出了問題。

| # | 項目 | 類別 | 影響 rubric 主線？ |
|---|---|---|---|
| B1 | 氣泡排序的 invariant | 證明工程 | ❌ 否（只影響目標 (ii)「介面可重用」的展示） |
| B2 | 緊界限 `n(n−1)/2` | 證明工程 | ❌ 否（**已定案永久接受鬆界限**，見 Opt04_Notes §5.4） |

**第 03 次 §5：第二支正確實作**（非阻擋核心結論）

- 卡在哪：氣泡排序的 `prove_correct`，兩次嘗試皆未過
- 試了什麼：① `splits 40` / `maxHeartbeats 2M` → whnf timeout；② 同 invariants / `maxHeartbeats 10M`（2 分 01 秒，非資源問題）→ 三條內層 invariant `Failed to prove assertion`
- 需要什麼決定：見 `Opt03_Notes.md` §5 的 A/B/C 三選項（**建議 B**：延到第 04 次，那時本來就需要兩支不同複雜度的演算法）
- 影響範圍：**不影響第 03 次的核心結論**（Level B 已由 `RestrictedSort` 與 `notASort` 兩面完整展示）

## 待你決定

| # | 事項 | 現況 |
|---|---|---|
| 1 | R4 的修訂 | ✅ **已定案**：`bash SortRubric/check_build.sh`（隔離 + SortRubric 綠 + 失敗集合逐字比對） |
| 2 | `SortSpec` 的合取順序 | ✅ **已定案**：人類順序。橋接 = 1 行 term-level、零 simp，落在判準第一列（Opt02_Notes §3） |
