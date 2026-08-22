#!/usr/bin/env bash
# ============================================================================
#  SortRubric import 隔離證明  (決定 (一) 條件 2 的機械化)
#
#  要證明的命題:
#      SortRubric 的 import 遞移閉包**不含**任何專案根目錄模組
#      （尤其是既有紅燈的 VelvetLC917）。
#
#  證明策略（歸納，避免展開數千個 mathlib 檔案）:
#      基底: SortRubric/*.lean 的**直接** import 全部落在
#            toolchain 或 .lake/packages/ 之下（用 `lean --src-deps` 查，Lean 自己的解析）
#      歸納: .lake/packages/ 底下**沒有任何檔案** import 專案根目錄模組
#            （Lake 依賴套件看不到依賴它的套件的模組）
#      ⇒ 閉包封閉在 toolchain ∪ packages ∪ SortRubric/ 之內，
#        專案根目錄模組（含 VelvetLC917）進不來。
#
#  用法:  bash SortRubric/check_isolation.sh
# ============================================================================
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"

# 專案根目錄的頂層模組 —— **動態推導，不寫死**。
# 理由：寫死的話，將來專案多一個根模組，歸納步就有一個沒被檢查到的出口。
#   來源 (1) 專案根目錄的 *.lean 檔
#   來源 (2) 專案根目錄下含有 *.lean 的子目錄（排除 SortRubric 自己與隱藏目錄）
ROOT_MODULES=$(
  {
    # 排除 lakefile.lean：它是建置腳本，不是可被 import 的函式庫模組
    find . -maxdepth 1 -name '*.lean' -not -name 'lakefile.lean' -printf '%f\n' 2>/dev/null | sed 's/\.lean$//'
    find . -maxdepth 1 -mindepth 1 -type d -not -name '.*' -not -name 'SortRubric' -printf '%f\n' 2>/dev/null |
      while read -r d; do
        [ -n "$(find "$d" -name '*.lean' -print -quit 2>/dev/null)" ] && echo "$d"
      done
  } | sort -u
)
FAIL=0

echo "=== 動態推導出的專案根目錄模組 ==="
echo "$ROOT_MODULES" | sed 's/^/  /'
echo

echo "=== [基底] SortRubric 各檔的直接 import（每次重新 glob，非固定清單）==="
while IFS= read -r f; do
  echo "  $f"
  deps=$(lake env lean --src-deps "$f" 2>/dev/null)
  while IFS= read -r d; do
    [ -z "$d" ] && continue
    case "$d" in
      *"/.lake/packages/"*)      tag="package  " ;;
      "$ROOT"/SortRubric/*)      tag="SortRubric" ;;
      *"/toolchains/"*|*"/src/lean/"*) tag="toolchain" ;;
      "$ROOT"/*)                 tag="✗ 專案根目錄"; FAIL=1 ;;
      *)                         tag="toolchain" ;;
    esac
    echo "      [$tag] ${d#"$ROOT"/}"
  done <<< "$deps"
done < <(find SortRubric -name '*.lean' | sort)

echo
echo "=== [歸納] .lake/packages/ 是否有檔案 import 專案根目錄模組？ ==="
hits=0
for m in $ROOT_MODULES; do
  if grep -rlE "^import[[:space:]]+$m([[:space:]]|\.|$)" .lake/packages/ --include='*.lean' 2>/dev/null | head -1 | grep -q .; then
    echo "  ✗ 有檔案 import $m"
    grep -rlE "^import[[:space:]]+$m([[:space:]]|\.|$)" .lake/packages/ --include='*.lean' 2>/dev/null | head -5 | sed 's/^/      /'
    hits=1; FAIL=1
  fi
done
[ "$hits" = 0 ] && echo "  ✓ 無。所有 $(echo "$ROOT_MODULES" | wc -w) 個根目錄模組都沒有被任何套件 import"

echo
echo "=== [對照] 專案內誰 import 了 VelvetLC917？ ==="
if grep -rnE "^import[[:space:]]+VelvetLC917" --include='*.lean' . 2>/dev/null | grep -v '^\./\.lake/' | grep -q .; then
  grep -rnE "^import[[:space:]]+VelvetLC917" --include='*.lean' . | grep -v '^\./\.lake/' | sed 's/^/  /'
  FAIL=1
else
  echo "  ✓ 沒有任何檔案 import VelvetLC917（它是 leaf module，只被 lakefile 當 default_target）"
fi

echo
echo "=== [圍堵] 有沒有模組 import 了 Cheats/？ ==="
# 理由：Cheats/ 裡的檔案含被 #guard_msgs 釘住的失敗證明，
# 其 `<method>_correct` 帶 sorryAx **且帶 @[loomSpec] 屬性**。
# 一個 sorry 過的 spec 若被下游看見，可能污染 loom_solve。
# 因此 Cheats/ 必須是 import 圖的葉節點。
cheat_importers=$(grep -rlnE "^import[[:space:]]+SortRubric\.Cheats\." --include='*.lean' . 2>/dev/null \
                  | grep -v '^\./\.lake/' | grep -v '^\./SortRubric/Cheats/' || true)
if [ -n "$cheat_importers" ]; then
  echo "  ✗ 有模組 import 了 Cheats/（sorryAx 可能外洩）："
  echo "$cheat_importers" | sed 's/^/      /'
  FAIL=1
else
  n_cheats=$(find SortRubric/Cheats -name '*.lean' 2>/dev/null | wc -l)
  echo "  ✓ 無。Cheats/ 的 $n_cheats 個模組都是 import 圖的葉節點，sorryAx 不會外洩"
fi

echo
if [ "$FAIL" = 0 ]; then
  echo "✓ 隔離成立：SortRubric 的 import 閉包不含專案根目錄模組，且 Cheats/ 未被任何模組 import。"
  exit 0
else
  echo "✗ 隔離不成立，見上方 ✗ 標記。"
  exit 1
fi
