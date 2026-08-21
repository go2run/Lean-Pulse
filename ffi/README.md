# ffi/ — 從 C / Python 呼叫 Velvet 驗證過的程式

把 [VelvetFFI.lean](../VelvetFFI.lean) 用 `@[export]` 暴露出來的 C 符號，連結成
C 執行檔與共享函式庫。原理與限制見 [doc/VelvetExec.md](../doc/VelvetExec.md) §7.1。

```sh
./ffi/build.sh      # 建置 + 各跑一次
```

## 原始檔

| 檔案 | 用途 |
|---|---|
| `main.c` | C 端的 `main`，起 Lean runtime 後直接呼叫 `velvet_maximum` |
| `demo.py` | Python 端，用 `ctypes` 載入 `.so` 後呼叫同一個函數 |
| `build.sh` | 撈 `lake build -v` 的連結指令改寫後重跑，產生下面兩個成品 |

## 產物（`ffi/out/`，已在 `.gitignore` 裡）

| 產物 | 能直接執行？ | 怎麼用 |
|---|---|---|
| `c_demo` | **可以** | `./ffi/out/c_demo` |
| `libvelvet.so` | **不行** | `LD_LIBRARY_PATH=$(lean --print-prefix)/lib/lean python3 ffi/demo.py ffi/out/libvelvet.so` |
| `build/` | **不行** | 中間檔（`main.o`、`link_cmd.txt`），可安全刪除 |

## 為什麼 `build/main.o` 不能執行

```console
$ file ffi/out/build/main.o
ELF 64-bit LSB relocatable, x86-64          ← 目的檔
$ file ffi/out/c_demo
ELF 64-bit LSB pie executable, x86-64       ← 執行檔
```

`relocatable` 表示它只是 `main.c` 編譯後的**半成品**：符號位址還沒填、也沒有進入點
（`_start`），核心無從執行起。所以會拿到：

```
bash: ./main.o: cannot execute binary file: 可執行檔格式錯誤
```

**`chmod +x` 沒有用**——問題不在權限，在檔案格式。`main.o` 要再跟 Lean 那 1800 多個
`.o` 連結之後，才變成 `c_demo`。

同理 `libvelvet.so` 是 `shared object`，設計上就是給別的程式載入的，不是拿來直接跑的。

## 已知限制

- **`.so` 需要 `LD_LIBRARY_PATH`**：它動態連到 `libleanshared.so`。靜態連結的 `c_demo`
  則自給自足（`ldd` 只剩 libc/pthread/m/dl/rt）。
- **`build.sh` 靠撈 Lake 的輸出**：Lake 沒有「把 `lean_lib` 做成 C 可呼叫的 `.so`」這種
  一級 target（`lake build VelvetFFI:shared` 在本專案會撞 duplicate symbol），所以腳本
  解析 `lake build -v` 印出的連結指令再改寫。Lake 改輸出格式就會壞。
