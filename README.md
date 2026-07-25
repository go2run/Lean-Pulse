# Lean-Pulse

用 [Velvet](https://github.com/verse-lab/velvet)（Lean 4 內嵌的基礎式多模態驗證器，
[CAV'26 論文](https://ilyasergey.net/assets/pdf/papers/velvet-cav26.pdf)）改寫
[pulse-sandbox](https://github.com/FStarLang/pulse-sandbox) 教程的練習專案。

## 第一階段：入門（separation logic 直覺 → Velvet 值語意）

| Pulse 原檔 | 本專案 | 主題 |
|---|---|---|
| `Hello.fst` | `LeanPulse/Hello.lean` | 最小驗證程式、`method`/`prove_correct` |
| `src/PulseByExample.fst` | `LeanPulse/PulseByExample.lean` | 規格、swap、陣列、迴圈不變式 |
| `PulseTutorial.Intro.fst` | `LeanPulse/Intro.lean` | incr、ghost 參數、frame rule |
| `PulseTutorial.Ref.fst` | `LeanPulse/Ref.lean` | 讀寫、權限模型的對應、失敗案例 |
| `PulseTutorial.Box.fst` | `LeanPulse/Box.lean` | 堆積配置/釋放的顯式建模 |
| `PulseTutorial.Conditionals.fst` | `LeanPulse/Conditionals.lean` | 分支匯合點、nullable pointer、自動化的邊界 |

核心翻譯原則（詳見各檔案開頭的對照表）：

- `pts_to r 'v`（擁有 + ghost 初值）↦ `mut` 參數 + `rOld`
- 分數權限（唯讀共享）↦ 非 `mut` 參數
- `p ** q`（分離）↦ 值語意下不同參數天生不 alias
- frame rule ↦ 沒宣告 `mut` 的東西不可能被改（免費）
- `Box.alloc`/`free` ↦ 顯式 store 建模（`Array (Option Int)`），frame 條款手寫
- Pulse 的並行（`par`）：Velvet 無對應——這是分離邏輯不可替代的地盤

## 建置

需要 [elan](https://github.com/leanprover/elan)（Lean 工具鏈管理器）與網路：

```sh
lake build          # 會抓取 Velvet/Loom 相依並驗證所有檔案
```

`prove_correct` 預設用 Lean 的 `grind`；SMT 後端（z3/cvc5）由 Velvet
的建置流程自動下載。

> 完整的安裝需求、步驟與常見問題見 [INSTALL.md](INSTALL.md)。
> 第一次建置需下載約 7 GB 相依（含 mathlib）並耗時 10 分鐘以上。

> 注意：本專案在無法連外的環境中撰寫，尚未實際以 `lake build` 驗證過；
> `attribute [grind]` 提示與個別 `prove_correct` 可能需要按照
> [Velvet 文件](https://github.com/verse-lab/velvet/blob/master/velvet_documentation.md)
> 的除錯流程（`loom_solve!`、補 lemma hint、調 `splits`/`maxHeartbeats`）微調。
