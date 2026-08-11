# 安裝與建置說明

本專案是 Lean 4 專案，用 [Velvet](https://github.com/verse-lab/velvet) 驗證器改寫
Pulse 教程。以下說明如何從零把環境裝好並成功 `lake build`。

## 需求總覽

| 項目 | 版本／需求 | 說明 |
|---|---|---|
| 作業系統 | Linux (x64) 或 macOS | z3/cvc5 預編譯檔依此下載 |
| [elan](https://github.com/leanprover/elan) | ≥ 4.x | Lean 工具鏈管理器，會自動裝對的 Lean 版本 |
| Lean | `leanprover/lean4:v4.24.0` | 由 `lean-toolchain` 指定，elan 自動處理 |
| 網路 | 必要 | 抓取 Velvet 相依 + 下載 z3/cvc5 |
| 磁碟 | 約 7 GB 空間 | `.lake/` 完整相依樹（mathlib 佔大宗） |
| 時間 | 第一次 10 分鐘以上 | 需編譯 mathlib/Loom/Auto 共約 1000+ 個目標 |

> SMT 後端（z3、cvc5）**不需要手動安裝** —— Velvet 的建置流程會自動下載到
> `.lake/` 內（本專案實測抓的是 z3 4.15.4）。

## 步驟

### 1. 安裝 elan（Lean 工具鏈管理器）

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

裝完把 `~/.elan/bin` 加進 `PATH`（安裝程式通常會提示或自動改 shell profile）：

```sh
export PATH="$HOME/.elan/bin:$PATH"
```

macOS 也可用 `brew install elan-init`。

### 2. 確認 elan 可用

```sh
elan --version
```

不需要手動 `elan toolchain install`：進到專案目錄後，elan 會讀 `lean-toolchain`
自動下載並固定 `leanprover/lean4:v4.24.0`。

### 3. 建置

```sh
cd Lean-Pulse
lake build
```

第一次會依序做這些事（都自動、不用介入）：

1. 讀 `lakefile.lean`，從 GitHub 抓 `Velvet`，並遞迴拉入相依：
   `Loom`、`auto`、`mathlib`、`aesop`、`batteries`、`Qq`、`proofwidgets`、
   `plausible`、`Cli`、`importGraph`、`LeanSearchClient`。
2. 編譯全部相依（約 1000+ 個目標，mathlib 最耗時）。
3. 執行 Velvet 的 `downloadDependencies`，自動下載 **z3** 與 **cvc5** 到
   `.lake/packages/Velvet/.lake/packages/Loom/.lake/build/`。
4. 最後才驗證本專案 5 個檔案（`Hello`／`PulseByExample`／`Intro`／`Ref`／`Box`）。

`prove_correct` 預設用 Lean 的 `grind`；需要 SMT 時會呼叫上面下載好的 z3/cvc5。

### 4. 驗證單一檔案（可選）

想只重建某個檔案：

```sh
lake build LeanPulse.Ref
```

## 常見問題

- **第一次 `lake build` 好像卡住？**
  它在編譯 mathlib 或下載 z3/cvc5（`downloadDependencies` 這步實測約 2 分鐘）。
  可另開終端 `du -sh .lake` 觀察磁碟成長確認仍在進行。若怕前景逾時被砍，可用
  `nohup lake build > build.log 2>&1 &` 背景執行後 `tail -f build.log` 追進度。

- **磁碟不足**：`.lake/` 完整約 7 GB，先確認有足夠空間。

- **改了 `lakefile.lean` 或相依後編譯行為怪異**：
  ```sh
  lake update    # 重算相依版本、更新 lake-manifest.json
  ```
  最後手段可刪掉 `.lake/` 重建（會重新下載一切，較久）。

- **`prove_correct` 驗證失敗**：這是證明層問題，非安裝問題。依
  [Velvet 文件](https://github.com/verse-lab/velvet/blob/master/velvet_documentation.md)
  的除錯流程處理（`loom_solve!`、補 lemma hint、調 `splits`／`maxHeartbeats`）。

## 環境檢查小抄

```sh
elan --version     # elan 4.x
lake --version     # Lake 5.x (Lean 4.24.0)
lean --version     # Lean 4.24.0
```
