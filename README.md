# Lean-Pulse：Velvet V1 教學

> **Velvet 版本：V1**（Loom 架構，固定在 commit
> [`d254391`](https://github.com/verse-lab/velvet/tree/d254391d5e84546f96576e5b67dfb6bafe9fc301)，Lean `v4.24.0`）。
> 上游 Velvet 已改寫成 V2（tag `v2.0`，Lean `v4.34.0`），語法不相容，兩者也沒有共同歷史。
> 本分支保留 V1 時期的成果，不跟著升級；V2 的新工作在 [`main`](https://github.com/go2run/Lean-Pulse/tree/main)。
>
> **這是 V1 教學。** 這裡用到的 `loom_solve`、`DivM`、`extract_program_for`、`(mut …)` 參數等
> 在 V2 都已不存在，內容不適用於 V2。

## Velvet 入門教材

[doc/VelvetTutorial.md](doc/VelvetTutorial.md) 是六節的 Velvet 語法入門；
[VelvetTutorial.lean](VelvetTutorial.lean) 是它全部範例的可執行實作（單檔、獨立的
`lean_lib`），含正確版與兩類錯誤版：**驗證會過但規格太弱**的（活的程式碼，
`prove_correct` 就在下面）與**證不出來**的（只留 `method`，`prove_correct` 註解掉）。

```sh
lake build VelvetTutorial
```

## 從驗證到執行檔

[doc/VelvetExec.md](doc/VelvetExec.md) 解釋 Velvet 在 Lean 4 中的執行模型
（`method` 展開成什麼、`VelvetM` / `NonDetT` / `DivM` 各是什麼），以及如何用
`extract_program_for` 抽取可執行程式、用 `lean_exe` 編譯成原生執行檔。
可執行對照檔是 [VelvetExec.lean](VelvetExec.lean)（Velvet 端）與
[Main.lean](Main.lean)（`IO` 端）。

```sh
lake build VelvetExec              # 驗證 + 抽取 + tester + 隨機測試
lake build velvet_demo             # 編譯成原生執行檔
./.lake/build/bin/velvet_demo 3 1 4 1 5
```

同一份文件的 §7 回答「能不能抽取成其他程式語言」：Velvet 沒有多語言後端，但可以用
`@[export]` 走 Lean 的 C 後端讓 C／Python 直接呼叫驗證過的程式
（[VelvetFFI.lean](VelvetFFI.lean) + [ffi/](ffi/)）：

```sh
./ffi/build.sh                     # 產生 C 執行檔與 libvelvet.so 並各跑一次
```

產物說明（哪個能直接執行、哪個是中間檔）見 [ffi/README.md](ffi/README.md)。

## 建置

需要 [elan](https://github.com/leanprover/elan) 與網路；Lean 版本由 `lean-toolchain` 固定為 `v4.24.0`。

```sh
lake build                  # VelvetTutorial + VelvetExec
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
