# Lean-Pulse：LeetCode 917

> **Velvet 版本：V1**（Loom 架構，固定在 commit
> [`d254391`](https://github.com/verse-lab/velvet/tree/d254391d5e84546f96576e5b67dfb6bafe9fc301)，Lean `v4.24.0`）。
> 上游 Velvet 已改寫成 V2（tag `v2.0`，Lean `v4.34.0`），語法不相容，兩者也沒有共同歷史。
> 本分支保留 V1 時期的成果，不跟著升級；V2 的新工作在 [`main`](https://github.com/go2run/Lean-Pulse/tree/main)。

## Velvet 自動化的邊界：LeetCode 917

拿 [Reverse Only Letters](https://leetcode.com/problems/reverse-only-letters/) 當實例，
兩個獨立 `lean_lib`：

- [LeanLC917.lean](LeanLC917.lean) — 純 Lean 4 前向掃描解法 + 完整正確性證明。
  **零相依**（連 Velvet 和 mathlib 都不用），可以單獨拿走。
- [VelvetLC917.lean](VelvetLC917.lean) — 同一題的 Velvet 雙指標版，規格引用
  `LeanLC917.revOnly` 當參考實作。完整規格 `loom_solve` 證不出來（附實際錯誤訊息與診斷）；
  換成弱規格會自動過，但「什麼都不做」也一樣過。

> **已知狀態：** `VelvetLC917` 目前有 3 個錯誤（`:34`、`:44` Failed to prove assertion；`:92`
> unsolved goals），自 commit `69e292a` 起即如此；`LeanLC917` 全綠。
> `VelvetLC917.lean` 註解提到的 `doc/VelvetTutorial.md` 在 [`v1/tutorial`](https://github.com/go2run/Lean-Pulse/tree/v1/tutorial) 分支。

## 建置

需要 [elan](https://github.com/leanprover/elan) 與網路；Lean 版本由 `lean-toolchain` 固定為 `v4.24.0`。

```sh
lake build LeanLC917 VelvetLC917
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
