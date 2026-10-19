# Lean-Pulse：PoP

> **Velvet 版本：V2**（tag [`v2.0`](https://github.com/verse-lab/velvet/tree/v2.0)，commit `8b7dc75`，
> Lean `v4.34.0`）。V1（Loom 架構，Lean `v4.24.0`）時期的成果保留在 `v1/*` 分支，兩者語法不相容。

`PoP/` 是本分支的主要內容，以 Velvet V2 撰寫，目前只有骨架。

## 建置

需要 [elan](https://github.com/leanprover/elan) 與網路；Lean 版本由 `lean-toolchain` 固定為 `v4.34.0`。

```sh
lake build
```

V2 不依賴 mathlib，從原始碼建置只要幾分鐘。語法參考 Velvet 的
[docs/doc.md](https://github.com/verse-lab/velvet/blob/v2.0/docs/doc.md)，入門範例在
[Velvet/Examples/](https://github.com/verse-lab/velvet/tree/v2.0/Velvet/Examples)。

> **不要和 V1 分支共用同一個工作目錄。** V1 與 V2 的 Lean 版本和相依都不同（例如 `plausible`
> 的版本），在同一個目錄切換分支會讓 Lake 重新 checkout `.lake/packages/`，切回 V1 時 mathlib
> 可能要整個重建。請用 `git worktree add ../Lean-Pulse-main main` 把 `main` 放在另一個目錄。

## 分支一覽

| 分支 | 內容 | Velvet |
|---|---|---|
| [`main`](https://github.com/go2run/Lean-Pulse/tree/main) | PoP | **V2**（`v2.0`，Lean `v4.34.0`） |
| [`v1/LeanPulse`](https://github.com/go2run/Lean-Pulse/tree/v1/LeanPulse) | 用 Velvet 改寫 pulse-sandbox 教程（`LeanPulse/`） | V1 |
| [`v1/SortRubric`](https://github.com/go2run/Lean-Pulse/tree/v1/SortRubric) | 排序 rubric 分階段強化（`SortRubric/`） | V1 |
| [`v1/tutorial`](https://github.com/go2run/Lean-Pulse/tree/v1/tutorial) | V1 教學：VelvetTutorial、VelvetExec、VelvetFFI + `ffi/`、`doc/` | V1 |
| [`v1/LC917`](https://github.com/go2run/Lean-Pulse/tree/v1/LC917) | LeetCode 917：`LeanLC917` + `VelvetLC917` | V1 |

`v1/*` 分支與 `main` 都從同一個 commit `5e1075a`（V1 固定版本）分出，各自保有完整歷史。
