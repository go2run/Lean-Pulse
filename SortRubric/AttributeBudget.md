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
| `SameElements.size_eq` | `Opt05b_Composition` | 只在組合定理裡用到 1 處，遠低於 P1 的 ≥3 門檻。它是 `Multiset.card` 的 congruence，掛上去會讓 grind 對每個 `SameElements` 假設都多生一條 size 等式 |

## 預留：後續步驟預期會來申請的

| 步驟 | 預期屬性 | 為什麼 | 決定 |
|---|---|---|---|
| ~~06~~ | ~~`Ticks.val_bump`~~ | — | ✅ **已解決，未動用全域**：`attribute [local grind]`，見上表 |
| 07 | `InstrOrder.correct` / `InstrOrder.charged` | 純函式版的 `cmp` 規格是**等式**，grind 可直接當 rewrite | 用 `attribute [local grind]`（第 06 次已驗證這條路可行） |
| 08 | `SpecOrder.trans` / `.total` | `grind` 對抽象序沒有內建推理，全部要手餵 | ⚠ 高風險：`trans` 是**傳遞律**，掛全域 grind 容易爆搜尋空間。預設 local，且優先寫成手動 `apply ord.trans` 鏈 |
| 08 | `[Inhabited α]`（typeclass，非屬性） | `a[i]!` 需要它；真正的阻塞點是 `Array.multiset_swap [Inhabited α]` | 已在 README 的 typeclass 預算表論證：`Inhabited` **不提供任何比較能力**，面 3 不受影響 |
