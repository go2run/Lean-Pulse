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
      # ★ fail-closed（R16）：認不出來的位置一律當失敗。
      # 舊版這裡是 `tag="toolchain"`，也就是把未知一律當成安全——
      # 那讓整個歸納法有一個沒人看守的出口。
      *)                         tag="✗ 未知位置"; FAIL=1 ;;
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
echo "=== [R16] Ticks 的公開起點 mkForTesting 出現在哪些檔？（fail-closed 白名單）==="
# 為什麼這個檢查是**完整**的列舉：
#   Ticks 的建構子是 private（作用域 = Opt06_Ticks.lean 這個模組），
#   所以模組外每一個造出 Ticks 的地方都必須寫出 `mkForTesting` 這個字。
#   ⇒ 列舉這個字串等於列舉模組外的全部建構點。
#
# 用 strip_comments.py 先剝掉註解再找，因為註解裡提到這個名字是正常的
# （檔頭要解釋 R16），只有**程式碼**裡的出現才算建構點。
#   同一支腳本也會找 `_private`：Lean 的 private 名稱在 olean 裡是
#   `_private.<module>.<n>.<name>`，理論上打得出來，那是繞過模組抽象的逃生門。
#
# 白名單:
#   SortRubric/Opt06_Ticks.lean   定義處
#   SortRubric/Opt10_Audit.lean   稽核
#   SortRubric/**/*_Tests.lean    SPOTs
r16_hits=$(python3 SortRubric/strip_comments.py 'mkForTesting|_private' $(find SortRubric -name '*.lean' | sort) 2>/dev/null)
if [ -z "$r16_hits" ]; then
  echo "  ✓ 程式碼裡沒有任何 mkForTesting / _private"
else
  r16_bad=0
  while IFS= read -r hit; do
    [ -z "$hit" ] && continue
    f="${hit%%:*}"
    case "$f" in
      SortRubric/Opt06_Ticks.lean) echo "      [定義處    ] $hit" ;;
      SortRubric/Opt10_Audit.lean) echo "      [稽核      ] $hit" ;;
      *_Tests.lean)                echo "      [SPOTs     ] $hit" ;;
      *) echo "      [✗ 違反 R16] $hit"; FAIL=1; r16_bad=1 ;;
    esac
  done <<< "$r16_hits"
  [ "$r16_bad" = 0 ] && echo "  ✓ 全部落在白名單內（定義處 / Opt10_Audit / *_Tests）"
fi

echo
echo "=== [面 3] α 上有沒有可計算的 typeclass 假設？（fail-closed 白名單）==="
# 為什麼這一段是面 3 的**強制機制**而不是文件:
#   面 3（「除了 iord 沒有別的觀察 α 的途徑」）由型別錯誤保證，
#   但那個保證的前提是「α 上沒有任何可計算的結構」。
#   只要有人加一個 [DecidableEq α] / [DecidableRel] / [FinEnum α] /
#   [∀ x y, Decidable (ord.le x y)]，作弊就當場復活，
#   **而且不會有任何錯誤訊息、任何警告**。
#   ⇒ 這是本專案唯一一個「加了東西反而變弱、且完全靜默」的失效模式，
#     必須用 grep 守。
# 白名單:
#   Cheats/Opt08_Cheat_BypassWithInt.lean  ——它**故意**示範這三個陷阱，
#                                            那幾行編譯成功正是它要證明的事
face3_pat='\[[^]]*(DecidableEq|DecidableRel|DecidableLT|DecidableLE|FinEnum)|Decidable \(ord\.|\[(LT|LE|Ord|Min|Max) '
face3_hits=$(python3 SortRubric/strip_comments.py "$face3_pat" $(find SortRubric -name '*.lean' | sort) 2>/dev/null)
if [ -z "$face3_hits" ]; then
  echo "  ✓ 程式碼裡沒有任何 α 上的可計算 typeclass 假設"
else
  face3_bad=0
  while IFS= read -r hit; do
    [ -z "$hit" ] && continue
    f="${hit%%:*}"
    case "$f" in
      SortRubric/Cheats/Opt08_Cheat_BypassWithInt.lean)
        echo "      [示範陷阱  ] $hit" ;;
      *) echo "      [✗ 面 3 失效] $hit"; FAIL=1; face3_bad=1 ;;
    esac
  done <<< "$face3_hits"
  [ "$face3_bad" = 0 ] && echo "  ✓ 只出現在故意示範陷阱的那一支 cheat 裡"
fi

echo
if [ "$FAIL" = 0 ]; then
  echo "✓ 隔離成立：SortRubric 的 import 閉包不含專案根目錄模組，且 Cheats/ 未被任何模組 import。"
  exit 0
else
  echo "✗ 隔離不成立，見上方 ✗ 標記。"
  exit 1
fi
