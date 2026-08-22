#!/usr/bin/env python3
"""把 Lean 原始碼的註解剝掉，其餘原樣輸出（供 check_isolation.sh 的 R16 段使用）。

Lean 的區塊註解 /- ... -/ 可以巢狀，行註解是 --。
字串常值裡的 -- 與 /- 不算註解，所以也要處理 " ... "。
"""
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
                    out.append(src[i:i+2]); i += 2
                elif src[i] == '"':
                    out.append('"'); i += 1; break
                else:
                    out.append(src[i]); i += 1
        else:
            out.append(src[i]); i += 1
    return ''.join(out)

for path in sys.argv[1:]:
    with open(path, encoding='utf-8') as f:
        for lineno, line in enumerate(strip(f.read()).split('\n'), 1):
            if 'mkForTesting' in line or '_private' in line:
                print(f"{path}:{lineno}:{line.strip()}")
