#!/usr/bin/env bash
# 把 Velvet 抽取出來的程式包成 C 可呼叫的產物：
#   ffi/out/c_demo       —— C 寫的 main，直接呼叫 velvet_maximum（可執行）
#   ffi/out/libvelvet.so —— 共享函式庫，給 Python ctypes / 其他語言 FFI 用（不可執行）
#   ffi/out/build/       —— 中間檔（main.o、link_cmd.txt），可安全刪除
#
# 原理：Lake 沒有「把 lean_lib 做成 C 可呼叫的 .so」這種一級 target
# （`lake build VelvetFFI:shared` 在本專案會撞到 duplicate symbol），
# 所以這裡撈 `lake build ... -v` 印出的連結指令，改掉輸入輸出後重跑。
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="$ROOT/ffi/out"
BUILD="$OUT/build"          # 中間檔跟成品分開放，免得誤把 .o 當執行檔
TOOLCHAIN="$(lean --print-prefix)"
mkdir -p "$BUILD"

cd "$ROOT"
lake build VelvetFFI velvet_demo

echo "==> 取得 Lake 的連結指令"
rm -f "$ROOT/.lake/build/bin/velvet_demo"
lake build velvet_demo -v \
  | grep -o '^trace: \.> .*clang -o .*' \
  | sed 's/^trace: \.> //' > "$BUILD/link_cmd.txt"
test -s "$BUILD/link_cmd.txt" || { echo "抓不到連結指令，Lake 輸出格式可能變了"; exit 1; }

echo "==> 編譯 C 端 main"
cc -c -O2 -I"$TOOLCHAIN/include" -o "$BUILD/main.o" "$ROOT/ffi/main.c"

python3 - "$OUT" "$BUILD" "$ROOT" <<'PY'
import subprocess, sys
out, build, root = sys.argv[1], sys.argv[2], sys.argv[3]
base = open(f"{build}/link_cmd.txt").read().strip()

def link(what, cmd):
    r = subprocess.run(cmd.split(' '), capture_output=True, text=True)
    if r.returncode != 0:
        print(f"{what}: 連結失敗\n{r.stderr[-800:]}")
        sys.exit(1)          # 沒有這行的話 set -e 攔不到，會繼續去跑不存在的檔案
    print(f"{what}: ok")

# 1. C main 取代 Lean 的 Main.c.o.export，並補上 VelvetFFI 的目的檔
link("c_demo", base
    .replace(f"-o {root}/.lake/build/bin/velvet_demo", f"-o {out}/c_demo")
    .replace(f"{root}/.lake/build/ir/Main.c.o.export",
             f"{build}/main.o {root}/.lake/build/ir/VelvetFFI.c.o.export"))

# 2. 共享函式庫：拿掉 main，靜態 runtime 換成 libleanshared（靜態的 libleanrt.a 不是 PIC）
link("libvelvet.so", base
    .replace(f"-o {root}/.lake/build/bin/velvet_demo", f"-shared -o {out}/libvelvet.so")
    .replace(f"{root}/.lake/build/ir/Main.c.o.export",
             f"{root}/.lake/build/ir/VelvetFFI.c.o.export")
    .replace("-Wl,--start-group -lleancpp -lLean -Wl,--end-group -lStd "
             "-Wl,--start-group -lInit -lleanrt -Wl,--end-group", "-lleanshared")
    .replace("-Wl,-Bstatic -lc++ -lc++abi -Wl,-Bdynamic", ""))
PY

cat <<EOF

==> 產物
  ffi/out/c_demo         可執行檔，直接跑：./ffi/out/c_demo
  ffi/out/libvelvet.so   共享函式庫，不能直接執行，給 ctypes/FFI 載入：
                         LD_LIBRARY_PATH=\$(lean --print-prefix)/lib/lean \\
                           python3 ffi/demo.py ffi/out/libvelvet.so
  ffi/out/build/         中間檔（main.o、link_cmd.txt），不能執行，可安全刪除

  說明見 ffi/README.md
EOF

echo
echo "==> C:"
"$OUT/c_demo"
echo "==> Python:"
LD_LIBRARY_PATH="$TOOLCHAIN/lib/lean" python3 "$ROOT/ffi/demo.py" "$OUT/libvelvet.so"
