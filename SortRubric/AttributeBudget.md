# 全域自動化屬性預算表

> **R15**：新增任何全域 `@[grind]` / `@[simp]` 之前，先在這張表加一列
> （屬性名、宣告於哪個檔、加它是為了讓**哪個目標**過、風險評估）。
> 動屬性之後**全量 rebuild**（P2）並重跑全部 `Cheats/`（R14）。
>
> 預設仍是 **local**（P1）：`grind [lemma]` / `simp only [lemma]` 就地帶入。
> 同一條引理被局部使用 ≥3 處，才考慮升級成全域。

## 為什麼需要這張表

第 04 次加了一條**正確無誤**的引理 `tick_step` 並標上 `@[grind]`，結果
`loom_solve!` 開始在完全不相關的平凡目標上失敗——連 `⊢ SameElements arrOld arrOld`
（那是 `rfl`）都證不出來。拿掉屬性、引理本身不動，立刻恢復。

> **一條正確的引理也可能是一條壞的自動化提示。**

型別錯誤是局部的、當場的；自動化干擾是全域的、延遲的、而且**不指向兇手**。
所以屬性要有預算，型別不用。

## 目前生效的全域屬性

| 屬性 | 宣告於 | 為什麼需要 | 風險 |
|---|---|---|---|
| `attribute [grind] Array.multiset_swap` | Opt02、兩支 `Unresolved_*` | 跨 `swap!` 的 multiset 保存 invariant；官方 `Examples.lean:47` 亦如此 | 低（Velvet 自己的引理） |
| `@[grind] def Sorted` | Opt02 | **前提性**：不加則 `ensures Sorted arr` 會讓 `loom_solve!` 卡住，規格就只能就地展開 —— 見下方依賴鏈 | 低 |
| `@[grind] def SameElements` | Opt02 | 同上 | 低 |
| `@[grind] sorted_replicate_zero` | Opt01 | `loom_solve` 不處理 `Array.replicate` | 低（只在 Opt01 用到） |
| `@[grind] pad_within_sq` | `Unresolved_FakeCounterPadded` | `n - 1 ≤ n * n` 的 Nat 乘法推理 | 低（葉節點模組，不外洩） |
| ~~`@[grind] tick_step`~~ | **試過，已移除** | 想補第 04 次緊界限的非線性步 | 🚫 **它主動破壞了不相關的平凡目標**——加上之後連 `⊢ SameElements arrOld arrOld`（rfl）都證不出來，拿掉立刻恢復。詳見 `Opt04_Notes.md` §6.1 |


## 目前生效的全域 `@[simp]`

**0 個。**

決定 (二) 的教訓：`and_comm` 之類的 permutative lemma 一旦進 simp set，
就會跟後續宣告互相干擾；term-level 直接套用則沒有這個問題。
**能用 term-level 就不要進 simp set。**

## 明確不掛全域屬性的引理（P1 的正面紀錄）

| 引理 | 宣告於 | 為什麼保持 local |
|---|---|---|
| `Ticks.val_bump` | `Opt06_MonotonicTicks` | ★ 用 `attribute [local grind]`。`loom_solve` **不吃引理參數**（`Loom/CaseStudies/Tactic.lean:65`），所以 `grind [Ticks.val_bump]` 這條路走不通；`local` 屬性有全域屬性的效力，但**不外洩給 importer**，從結構上消掉第 04 次 `tick_step` 那一類事故。**這應該是 07/08 的預設做法。** |
| `InstrOrder.correct` / `.charged` / `.correct_false` | `Opt07_InstrOrder`、`Opt08a_AbstractCore` | 純函式版的 `cmp` 規格是**等式／iff**，grind 可直接當 rewrite。`local` ⇒ 不外洩 |
| `SpecOrder.trans` / `.le_refl` / `.not_le` | `Opt08a_AbstractCore` | 抽象序沒有內建推理，全部要手餵。⚠ `trans` 是傳遞律，全域掛上去容易爆搜尋空間——**這正是為什麼用 `local`** |
| `Sorted` / `SameElements`（抽象版 `def`） | `Opt08a_AbstractCore` | 與第 02 次同樣是「前提性」；改用 `local`，代價是下游模組要自己寫一次 |
| `SameElements.size_eq` | `Opt05b_Composition` | 只在組合定理裡用到 1 處，遠低於 P1 的 ≥3 門檻。它是 `Multiset.card` 的 congruence，掛上去會讓 grind 對每個 `SameElements` 假設都多生一條 size 等式 |

## 預留：後續步驟預期會來申請的

| 步驟 | 預期屬性 | 為什麼 | 決定 |
|---|---|---|---|
| ~~06~~ | ~~`Ticks.val_bump`~~ | — | ✅ **已解決，未動用全域**：`attribute [local grind]`，見上表 |
| 07 | `InstrOrder.correct` / `InstrOrder.charged` | 純函式版的 `cmp` 規格是**等式**，grind 可直接當 rewrite | 用 `attribute [local grind]`（第 06 次已驗證這條路可行） |
| 08 | `SpecOrder.trans` / `.total` | `grind` 對抽象序沒有內建推理，全部要手餵 | ⚠ 高風險：`trans` 是**傳遞律**，掛全域 grind 容易爆搜尋空間。預設 local，且優先寫成手動 `apply ord.trans` 鏈 |
| ~~08~~ | ~~`SpecOrder.trans` / `.total`~~ | — | ✅ **已解決，未動用全域**：`attribute [local grind]` |


## α 的 typeclass 預算（R11）—— 實測版

| typeclass | 出現在 | 為什麼需要 | 面 3 受影響嗎 |
|---|---|---|---|
| `[Inhabited α]` | `Opt08a_AbstractCore` 的 `Sorted`、`minIndex`、（將來的）08b | `a[i]!` 需要它；**真正的阻塞點是 `Array.multiset_swap [Inhabited α]`**（`Velvet/Std.lean:104`），那條是 multiset 保存 invariant 的唯一來源 | ❌ **不受影響**。它讓實作造得出一個 α 的值（＝抽象版的 `ZeroFill`），但那支作弊在第 02 次已被 `SameElements` 機械反證殺掉；而且 `Inhabited` **給不出 `Decidable`**，四條繞過路徑一條都沒開 |

**完全避開的代價**：改用 `a[i]'h`（帶證明的索引）⇒ spec 形狀改變 + 所有既有引理重寫。
收尾期不做這個交換。

### ✗ 永遠不得加入的（加了面 3 靜默失效）

```
[DecidableEq α]   [DecidableRel …]   [DecidableLT α]   [DecidableLE α]
[FinEnum α]       [LT α]  [LE α]  [Ord α]  [Min α]  [Max α]
[∀ x y, Decidable (ord.le x y)]
```

**由 `check_isolation.sh` 的「面 3」段 fail-closed 強制**，
白名單只有 `Cheats/Opt08_Cheat_BypassWithInt.lean`（它故意示範這些陷阱）。
負向測試見 `check_selftest.sh` 第 6 項。

理由見 `Opt08_Notes.md` §2：**這是本專案唯一一個「加了東西反而變弱、
而且完全靜默」的失效模式。**
