#!/usr/bin/env python3
"""Proof-text size of named theorems: lines and non-blank characters after the statement's `:=`.

usage: proofsize.py FILE [FILE ...] --names a,b,c   (prints name, file, lines, chars; then totals)
A declaration runs from `theorem NAME` to the next line that starts a top-level command. The proof
starts at the first `:=` at bracket depth 0 (so `(Fact := Fact)` in a statement is skipped).
"""
import re, sys

STARTERS = re.compile(r'^(theorem|def|abbrev|instance|structure|inductive|class|#|/--|/-|--|end\b|section|namespace|variable|open|omit|@\[|private|public|noncomputable|example)')

def decls(path):
    lines = open(path).read().split('\n')
    out = {}
    i = 0
    while i < len(lines):
        m = re.match(r'^theorem\s+(\S+)', lines[i])
        if not m:
            i += 1; continue
        name = m.group(1); j = i + 1
        while j < len(lines) and not STARTERS.match(lines[j]) and not (lines[j] == '' and j + 1 < len(lines) and STARTERS.match(lines[j+1] or '#')):
            j += 1
        text = '\n'.join(lines[i:j]).rstrip()
        depth = 0; k = None
        for idx, ch in enumerate(text):
            if ch in '([{⟨': depth += 1
            elif ch in ')]}⟩': depth -= 1
            elif ch == ':' and depth == 0 and text[idx:idx+2] == ':=':
                k = idx; break
        proof = text[k+2:] if k is not None else ''
        plines = [l for l in proof.split('\n') if l.strip()]
        out[name] = (len(plines), sum(len(l.strip()) for l in plines))
        i = j
    return out

def main():
    args = sys.argv[1:]
    names = args[args.index('--names') + 1].split(',')
    files = args[:args.index('--names')]
    found = {}
    for f in files:
        for n, v in decls(f).items():
            found.setdefault(n, (f, v))
    tl = tc = 0
    for n in names:
        if n not in found:
            print(f'{n}\tMISSING'); continue
        f, (l, c) = found[n]; tl += l; tc += c
        print(f'{n}\t{l}\t{c}')
    print(f'TOTAL\t{tl}\t{tc}')

main()
