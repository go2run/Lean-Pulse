#!/usr/bin/env bash
# ============================================================================
#  檢查器的負向測試  (決定 (一) 加固建議 (c))
#
#  理由與 R6 相同：**一個從來沒失敗過的檢查器，不知道它會不會失敗。**
#  本腳本故意製造兩種違規，確認 check_isolation.sh / check_build.sh
#  真的會以非零離開碼拒絕它們，然後把現場還原。
#
#  用法:  bash SortRubric/check_selftest.sh
# ============================================================================
set -uo pipefail
cd "$(dirname "$0")/.."

PROBE="SortRubric/__selftest_probe.lean"
BASE="SortRubric/baseline_errors.txt"
BAK="$(mktemp)"
cp "$BASE" "$BAK"

cleanup() {
  rm -f "$PROBE"
  cp "$BAK" "$BASE"; rm -f "$BAK"
}
trap cleanup EXIT

FAIL=0
pass() { echo "  ✓ $1"; }
fail() { echo "  ✗ $1"; FAIL=1; }

echo "########## 負向測試 1：隔離檢查器抓不抓得到違規 import ##########"
cat > "$PROBE" <<'EOF'
import VelvetLC917
EOF
if bash SortRubric/check_isolation.sh > /dev/null 2>&1; then
  fail "check_isolation.sh 對 'import VelvetLC917' 竟然回傳 0 —— 檢查器失效"
else
  pass "check_isolation.sh 正確拒絕（非零離開碼）"
  echo "      證據："
  bash SortRubric/check_isolation.sh 2>&1 | grep -E '✗|專案根目錄' | head -3 | sed 's/^/        /'
fi
rm -f "$PROBE"

echo
echo "########## 負向測試 2：Cheats/ 圍堵抓不抓得到外洩 ##########"
cat > "$PROBE" <<'EOF'
import SortRubric.Cheats.Opt02_Cheat_AllZeros
EOF
if bash SortRubric/check_isolation.sh > /dev/null 2>&1; then
  fail "check_isolation.sh 對 'import SortRubric.Cheats.*' 竟然回傳 0 —— sorryAx 圍堵失效"
else
  pass "check_isolation.sh 正確拒絕 Cheats/ 被 import（非零離開碼）"
  echo "      證據："
  bash SortRubric/check_isolation.sh 2>&1 | grep -E '✗' | head -2 | sed 's/^/        /'
fi
rm -f "$PROBE"

echo
echo "########## 負向測試 4：R16 抓不抓得到 mkForTesting 外洩 ##########"
# 模擬一支實作檔（不在白名單）拿公開起點造 Ticks —— 等於把 ResetToOld 送回來
cat > "$PROBE" <<'EOF'
import SortRubric.Opt06_Ticks
open SortRubric.Opt06 in
example : Ticks := Ticks.mkForTesting 0
EOF
if bash SortRubric/check_isolation.sh > /dev/null 2>&1; then
  fail "check_isolation.sh 對白名單外的 mkForTesting 竟然回傳 0 —— R16 失效"
else
  pass "check_isolation.sh 正確拒絕白名單外的 mkForTesting（非零離開碼）"
  echo "      證據："
  bash SortRubric/check_isolation.sh 2>&1 | grep -E '違反 R16' | head -2 | sed 's/^/        /'
fi
rm -f "$PROBE"

echo
echo "########## 負向測試 5：R16 的註解剝除會不會誤判 ##########"
# 反向：只在**註解**裡提到 mkForTesting，不該被判違規（否則檔頭沒辦法解釋 R16）
cat > "$PROBE" <<'EOF'
/-! 這個檔頭提到 Ticks.mkForTesting 與 _private，但程式碼裡沒有用。 -/
-- 行註解裡的 mkForTesting 也一樣
example : Nat := 0
EOF
if bash SortRubric/check_isolation.sh > /dev/null 2>&1; then
  pass "check_isolation.sh 正確忽略註解裡的 mkForTesting（不誤判）"
else
  fail "check_isolation.sh 把註解裡的 mkForTesting 當成違規 —— 剝除註解失效"
  bash SortRubric/check_isolation.sh 2>&1 | grep -E '違反 R16' | head -2 | sed 's/^/        /'
fi
rm -f "$PROBE"

echo
echo "########## 負向測試 6：面 3 抓不抓得到 typeclass 洩漏 ##########"
# 模擬有人「只是讓規格好用一點」而加上 α 的可判定性 —— 面 3 會靜默失效
cat > "$PROBE" <<'EOF'
import SortRubric.Opt08a_AbstractCore
open SortRubric.Opt08 in
example {α : Type} [Inhabited α] [DecidableEq α] (a : Array α) : Bool :=
  if a[0]! = a[1]! then true else false
EOF
if bash SortRubric/check_isolation.sh > /dev/null 2>&1; then
  fail "check_isolation.sh 對白名單外的 [DecidableEq α] 竟然回傳 0 —— 面 3 的守衛失效"
else
  pass "check_isolation.sh 正確拒絕白名單外的可計算 typeclass（非零離開碼）"
  echo "      證據："
  bash SortRubric/check_isolation.sh 2>&1 | grep -E '面 3 失效' | head -2 | sed 's/^/        /'
fi
rm -f "$PROBE"

echo
echo "########## 負向測試 3：baseline 比對抓不抓得到新錯誤 ##########"
echo "error: FakeModule.lean:1:1: 這是一個不存在的錯誤" >> "$BASE"
bash SortRubric/check_build.sh > /dev/null 2>&1
rc=$?
if [ "$rc" = 3 ]; then
  pass "check_build.sh 正確偵測到失敗集合不符（exit 3）"
else
  fail "check_build.sh 對被竄改的 baseline 回傳 $rc（預期 3）—— 比對邏輯失效"
fi
cp "$BAK" "$BASE"

echo
echo "########## 還原後複驗 ##########"
if bash SortRubric/check_build.sh > /dev/null 2>&1; then
  pass "現場已還原，check_build.sh 回到綠燈"
else
  fail "還原後仍是紅的 —— 自我測試把現場弄髒了"
fi

echo
if [ "$FAIL" = 0 ]; then
  echo "========== 檢查器本身通過負向測試 =========="
  exit 0
else
  echo "========== ✗ 檢查器有問題，見上 =========="
  exit 1
fi
