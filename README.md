# Lean-Pulse：PoP

> **Velvet 版本：V2**（上游 `lean-4.35` 分支的固定 commit
> [`10744dc`](https://github.com/verse-lab/velvet/tree/10744dcf1902aa29000ed4ae2b7a938376a9485b)，
> Lean `v4.35.0`）。V1（Loom 架構，Lean `v4.24.0`）時期的成果保留在 `v1/*` 分支，兩者語法不相容。

`PoP/` 是本分支的主要內容，以 Velvet V2 撰寫。目前只有 [`PoP/Quickstart.lean`](PoP/Quickstart.lean)：
把 V1 的 `VelvetExec` / `Ref` 範例移植到 V2 的最小範例，檔頭附 V1 → V2 語法對照表。

## 建置

需要 [elan](https://github.com/leanprover/elan) 與網路；Lean 版本由 [lean-toolchain](lean-toolchain) 固定為 `v4.35.0`。

```sh
lake build
```

V2 不依賴 mathlib，從原始碼建置只要幾分鐘。語法參考 Velvet 的
[docs/doc.md](https://github.com/verse-lab/velvet/blob/10744dcf1902aa29000ed4ae2b7a938376a9485b/docs/doc.md)，入門範例在
[Velvet/Examples/](https://github.com/verse-lab/velvet/tree/10744dcf1902aa29000ed4ae2b7a938376a9485b/Velvet/Examples)。

### 共用編譯快取與版本

[lakefile.lean](lakefile.lean) 已啟用 Lake 的 `enableArtifactCache`。同一使用者、同一 Lean
toolchain 的專案可共用編譯產物；使用 elan 時，預設儲存在
`~/.elan/toolchains/leanprover--lean4---v4.35.0/lake/cache/`。其他專案也啟用此選項後，
相同輸入的建置可以重用快取。不同 Lean 版本的編譯產物不能混用。

這是 Lake 官方提供、仍標示為實驗性的功能。依賴原始碼仍下載到各專案的
`.lake/packages/`，版本由 [lake-manifest.json](lake-manifest.json) 鎖定，避免共用可變的
checkout 而互相覆蓋版本。支援快取的編譯產物不一定放在原本的 build 目錄，請透過
`lake build`、`lake lean` 或 Lean 編輯器擴充套件使用。單獨檢查範例：

```sh
lake lean PoP/Quickstart.lean
```

請勿改成 `lake env lean PoP/Quickstart.lean`：它不會準備模組的快取路徑，可能找不到
已移入共用快取的 `.olean`。詳見
[Lake artifact cache 文件](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)。

升級 Lean 時，需要同時確認 Velvet 和 Plausible 的相容版本。原始 Velvet `v2.0` 使用
Lean 4.34 的 `Std.Internal.Do`，不能直接用 Lean 4.35 編譯；目前固定的 Velvet commit
已完成上游相容性移植，並依賴 Plausible `v4.35.0`。更新依賴時保留專案指定的 toolchain：

```sh
lake --keep-toolchain update
lake build
```

啟用共用快取不會自動清除之前的 `.lake/` 編譯產物或已不使用的依賴，也不會自動移除
elan 中的舊 toolchain。

> **不要和 V1 分支共用同一個工作目錄。** V1 與 V2 的 Lean 版本和相依都不同（例如 `plausible`
> 的版本），在同一個目錄切換分支會讓 Lake 重新 checkout `.lake/packages/`，切回 V1 時 mathlib
> 可能要整個重建。請用 `git worktree add ../Lean-Pulse-main main` 把 `main` 放在另一個目錄。

## 分支一覽

| 分支 | 內容 | Velvet |
|---|---|---|
| [`main`](https://github.com/go2run/Lean-Pulse/tree/main) | PoP | **V2**（`10744dc`，Lean `v4.35.0`） |
| [`v1/LeanPulse`](https://github.com/go2run/Lean-Pulse/tree/v1/LeanPulse) | 用 Velvet 改寫 pulse-sandbox 教程（`LeanPulse/`） | V1 |
| [`v1/SortRubric`](https://github.com/go2run/Lean-Pulse/tree/v1/SortRubric) | 排序 rubric 分階段強化（`SortRubric/`） | V1 |
| [`v1/tutorial`](https://github.com/go2run/Lean-Pulse/tree/v1/tutorial) | V1 教學：VelvetTutorial、VelvetExec、VelvetFFI + `ffi/`、`doc/` | V1 |
| [`v1/LC917`](https://github.com/go2run/Lean-Pulse/tree/v1/LC917) | LeetCode 917：`LeanLC917` + `VelvetLC917` | V1 |

`v1/*` 分支與 `main` 都從同一個 commit `5e1075a`（V1 固定版本）分出，各自保有完整歷史。
