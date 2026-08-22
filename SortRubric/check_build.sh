#!/usr/bin/env bash
# ============================================================================
#  SortRubric 每步驗收腳本  (決定 (一) 的機械化)
#
#  R4（修訂版）要求三件事，本腳本三件都查：
#    1. import 隔離：SortRubric 的閉包不含專案根目錄模組（條件 2）
#       ＋ Cheats/ 是葉節點（sorryAx 圍堵）
#    2. `lake build SortRubric` 全綠
#    3. 完整 `lake build` 的失敗集合與 baseline_errors.txt **逐字相同**（條件 1）
#       —— 多出任何一個新錯誤 = 該步未完成
#
#  用 --with-selftest 另外跑守衛自己的負向測試（每一步都該跑；守衛腳本本身也會被改）
#
#  用法:  bash SortRubric/check_build.sh
#  離開碼: 0 = 通過; 1 = 隔離失敗; 2 = SortRubric 紅; 3 = 全域出現新錯誤
# ============================================================================
set -uo pipefail
cd "$(dirname "$0")/.."

BASE="SortRubric/baseline_errors.txt"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

if [ "${1:-}" = "--with-selftest" ]; then
  echo "########## [0/3] 守衛自己的負向測試 ##########"
  if ! bash SortRubric/check_selftest.sh > "$TMP/self.txt" 2>&1; then
    echo "✗ FAIL: 守衛沒有通過負向測試"; cat "$TMP/self.txt"; exit 4
  fi
  tail -1 "$TMP/self.txt"
  echo
fi

echo "########## [1/3] import 隔離 ##########"
if ! bash SortRubric/check_isolation.sh > "$TMP/iso.txt" 2>&1; then
  echo "✗ FAIL: 隔離不成立"; cat "$TMP/iso.txt"; exit 1
fi
tail -1 "$TMP/iso.txt"
echo "   （完整清單: bash SortRubric/check_isolation.sh）"

echo
echo "########## [2/3] lake build SortRubric ##########"
if ! lake build SortRubric > "$TMP/sr.txt" 2>&1; then
  echo "✗ FAIL: SortRubric 未通過"
  grep -E '^error: ' "$TMP/sr.txt" | head -40
  exit 2
fi
echo "✓ SortRubric 綠"

echo
echo "########## [3/3] 完整 lake build，比對既有環境債 ##########"
lake build > "$TMP/full.txt" 2>&1
{ grep -E '^error: ' "$TMP/full.txt"; grep -E '^- ' "$TMP/full.txt"; } > "$TMP/now.txt"

if diff -u "$BASE" "$TMP/now.txt" > "$TMP/diff.txt"; then
  echo "✓ 失敗集合與 baseline 逐字相同（既有環境債，非本次造成）"
  echo
  sed 's/^/    /' "$BASE"
  echo
  echo "========== 全部通過 =========="
  exit 0
else
  echo "✗ FAIL: 全域 build 的失敗集合與 baseline 不同"
  echo "  （'-' = baseline 有而現在沒有；'+' = 新出現的錯誤）"
  echo
  sed 's/^/    /' "$TMP/diff.txt"
  exit 3
fi
