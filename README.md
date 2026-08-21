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

核心翻譯原則（詳見各檔案開頭的對照表）：

- `pts_to r 'v`（擁有 + ghost 初值）↦ `mut` 參數 + `rOld`
- 分數權限（唯讀共享）↦ 非 `mut` 參數
- `p ** q`（分離）↦ 值語意下不同參數天生不 alias
- frame rule ↦ 沒宣告 `mut` 的東西不可能被改（免費）
- `Box.alloc`/`free` ↦ 顯式 store 建模（`Array (Option Int)`），frame 條款手寫
- Pulse 的並行（`par`）：Velvet 無對應——這是分離邏輯不可替代的地盤

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

## Velvet 自動化的邊界：LeetCode 917

拿 [Reverse Only Letters](https://leetcode.com/problems/reverse-only-letters/) 當實例，
兩個獨立 `lean_lib`：

- [LeanLC917.lean](LeanLC917.lean) — 純 Lean 4 前向掃描解法 + 完整正確性證明。
  **零相依**（連 Velvet 和 mathlib 都不用），可以單獨拿走。
- [VelvetLC917.lean](VelvetLC917.lean) — 同一題的 Velvet 雙指標版，規格引用
  `LeanLC917.revOnly` 當參考實作。完整規格 `loom_solve` 證不出來（附實際錯誤訊息與診斷）；
  換成弱規格會自動過，但「什麼都不做」也一樣過。

```sh
lake build LeanLC917 VelvetLC917
```

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
