#!/usr/bin/env python3
"""在 Lean 原始碼裡搜尋 pattern，但**先剝掉註解**。

用法:
    strip_comments.py <regex> <file>...

供 check_isolation.sh 使用。理由：檔頭必須能解釋自己在防什麼
（例如 R16 要提到 `mkForTesting`、面 3 要提到 `DecidableEq`），
所以純文字 grep 會被自己的文件擋下來。只有**程式碼**裡的出現才算數。

Lean 的區塊註解 /- ... -/ 可以巢狀；行註解是 --；字串常值裡的
-- 與 /- 不算註解。三者都處理。
"""
import re
import sys


def strip(src: str) -> str:
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        if depth > 0:
            if src.startswith('/-', i):
                depth += 1; i += 2
            elif src.startswith('-/', i):
                depth -= 1; i += 2
            else:
                if src[i] == '\n':
                    out.append('\n')
                i += 1
        elif src.startswith('/-', i):
            depth = 1; i += 2
        elif src.startswith('--', i):
            while i < n and src[i] != '\n':
                i += 1
        elif src[i] == '"':
            out.append('"'); i += 1
            while i < n:
                if src[i] == '\\':
                    out.append(src[i:i + 2]); i += 2
                elif src[i] == '"':
                    out.append('"'); i += 1; break
                else:
                    out.append(src[i]); i += 1
        else:
            out.append(src[i]); i += 1
    return ''.join(out)


def main() -> int:
    if len(sys.argv) < 3:
        print("usage: strip_comments.py <regex> <file>...", file=sys.stderr)
        return 2
    pat = re.compile(sys.argv[1])
    for path in sys.argv[2:]:
        try:
            with open(path, encoding='utf-8') as f:
                src = f.read()
        except OSError as e:
            print(f"{path}:0:<讀取失敗: {e}>")
            continue
        for lineno, line in enumerate(strip(src).split('\n'), 1):
            if pat.search(line):
                print(f"{path}:{lineno}:{line.strip()}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
