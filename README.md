# Lean-Pulse：SortRubric

> **Velvet 版本：V1**（Loom 架構，固定在 commit
> [`d254391`](https://github.com/verse-lab/velvet/tree/d254391d5e84546f96576e5b67dfb6bafe9fc301)，Lean `v4.24.0`）。
> 上游 Velvet 已改寫成 V2（tag `v2.0`，Lean `v4.34.0`），語法不相容，兩者也沒有共同歷史。
> 本分支保留 V1 時期的成果，不跟著升級；V2 的新工作在 [`main`](https://github.com/go2run/Lean-Pulse/tree/main)。

用十次優化把「看起來像排序」逼成「只有真排序才滿足」：排序 rubric 的分階段強化。
完整說明、進度與每一步的筆記見 [SortRubric/README.md](SortRubric/README.md) 與
[SortRubric/PROGRESS.md](SortRubric/PROGRESS.md)。

## 建置

需要 [elan](https://github.com/leanprover/elan) 與網路；Lean 版本由 `lean-toolchain` 固定為 `v4.24.0`。

```sh
lake build SortRubric
bash SortRubric/check_build.sh --with-selftest   # 隔離 + SortRubric 全綠 + 全域失敗集合比對
```

第一次建置需下載約 7 GB 相依（含 mathlib），耗時 10 分鐘以上。`prove_correct` 預設用 Lean 的
`grind`；SMT 後端（z3/cvc5）由 Velvet 的建置流程自動下載。完整需求、步驟與常見問題見
[doc/INSTALL.md](doc/INSTALL.md)。

拆分前 `SortRubric/baseline_errors.txt` 記錄的是 `VelvetLC917` 的 3 個既有錯誤。`VelvetLC917`
已移到 [`v1/LC917`](https://github.com/go2run/Lean-Pulse/tree/v1/LC917)，本分支的完整 `lake build` 為全綠，所以 baseline 改成空檔。

## 分支一覽

| 分支 | 內容 | Velvet |
|---|---|---|
| [`main`](https://github.com/go2run/Lean-Pulse/tree/main) | PoP | **V2**（`v2.0`，Lean `v4.34.0`） |
| [`v1/LeanPulse`](https://github.com/go2run/Lean-Pulse/tree/v1/LeanPulse) | 用 Velvet 改寫 pulse-sandbox 教程（`LeanPulse/`） | V1 |
| [`v1/SortRubric`](https://github.com/go2run/Lean-Pulse/tree/v1/SortRubric) | 排序 rubric 分階段強化（`SortRubric/`） | V1 |
| [`v1/tutorial`](https://github.com/go2run/Lean-Pulse/tree/v1/tutorial) | V1 教學：VelvetTutorial、VelvetExec、VelvetFFI + `ffi/`、`doc/` | V1 |
| [`v1/LC917`](https://github.com/go2run/Lean-Pulse/tree/v1/LC917) | LeetCode 917：`LeanLC917` + `VelvetLC917` | V1 |

`v1/*` 分支與 `main` 都從同一個 commit `5e1075a`（V1 固定版本）分出，各自保有完整歷史。
