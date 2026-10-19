# Lean-Pulse：Pulse 教程的 Velvet 改寫

> **Velvet 版本：V1**（Loom 架構，固定在 commit
> [`d254391`](https://github.com/verse-lab/velvet/tree/d254391d5e84546f96576e5b67dfb6bafe9fc301)，Lean `v4.24.0`）。
> 上游 Velvet 已改寫成 V2（tag `v2.0`，Lean `v4.34.0`），語法不相容，兩者也沒有共同歷史。
> 本分支保留 V1 時期的成果，不跟著升級；V2 的新工作在 [`main`](https://github.com/go2run/Lean-Pulse/tree/main)。

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

核心翻譯原則（詳見各檔案開頭的對照表）：

- `pts_to r 'v`（擁有 + ghost 初值）↦ `mut` 參數 + `rOld`
- 分數權限（唯讀共享）↦ 非 `mut` 參數
- `p ** q`（分離）↦ 值語意下不同參數天生不 alias
- frame rule ↦ 沒宣告 `mut` 的東西不可能被改（免費）
- `Box.alloc`/`free` ↦ 顯式 store 建模（`Array (Option Int)`），frame 條款手寫
- Pulse 的並行（`par`）：Velvet 無對應——這是分離邏輯不可替代的地盤

## 其他課程

| Pulse 原檔 | 本專案 |
|---|---|
| `src/tutorial/PulseTutorial.Conditionals.fst` | `LeanPulse/Conditionals.lean` |
| `src/tutorial/PulseTutorial.Existentials.fst` | `LeanPulse/Existentials.lean` |
| `src/tutorial/PulseTutorial.ImplicationAndForall.fst` | `LeanPulse/ImplicationAndForall.lean` |
| `src/tutorial/PulseTutorial.UserDefinedPredicates.fst` | `LeanPulse/UserDefinedPredicates.lean` |
| `share/pulse/examples/PulseExample.BubbleSort.fst` | `LeanPulse/BubbleSort.lean` |
| `lib/pulse/lib/Pulse.Lib.RingBuffer.fst`（分支 `_nik_ring_buffer`） | `LeanPulse/RingBuffer.lean` |

## 建置

需要 [elan](https://github.com/leanprover/elan) 與網路；Lean 版本由 `lean-toolchain` 固定為 `v4.24.0`。

```sh
lake build                  # 驗證 LeanPulse/ 底下全部模組
lake build LeanPulse.Ref    # 只驗證單一模組
```

第一次建置需下載約 7 GB 相依（含 mathlib），耗時 10 分鐘以上。`prove_correct` 預設用 Lean 的
`grind`；SMT 後端（z3/cvc5）由 Velvet 的建置流程自動下載。完整需求、步驟與常見問題見
[doc/INSTALL.md](doc/INSTALL.md)。

## 分支一覽

| 分支 | 內容 | Velvet |
|---|---|---|
| [`main`](https://github.com/go2run/Lean-Pulse/tree/main) | PoP | **V2**（`v2.0`，Lean `v4.34.0`） |
| [`v1/LeanPulse`](https://github.com/go2run/Lean-Pulse/tree/v1/LeanPulse) | 用 Velvet 改寫 pulse-sandbox 教程（`LeanPulse/`） | V1 |
| [`v1/SortRubric`](https://github.com/go2run/Lean-Pulse/tree/v1/SortRubric) | 排序 rubric 分階段強化（`SortRubric/`） | V1 |
| [`v1/tutorial`](https://github.com/go2run/Lean-Pulse/tree/v1/tutorial) | V1 教學：VelvetTutorial、VelvetExec、VelvetFFI + `ffi/`、`doc/` | V1 |
| [`v1/LC917`](https://github.com/go2run/Lean-Pulse/tree/v1/LC917) | LeetCode 917：`LeanLC917` + `VelvetLC917` | V1 |

`v1/*` 分支與 `main` 都從同一個 commit `5e1075a`（V1 固定版本）分出，各自保有完整歷史。
