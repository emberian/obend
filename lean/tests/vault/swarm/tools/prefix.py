#!/usr/bin/env python3
"""Print a Unicode character prefix of each line (GNU cut -c splits UTF-8 bytes)."""
import sys

width = int(sys.argv[1])
source = open(sys.argv[2], encoding="utf-8") if len(sys.argv) > 2 else sys.stdin
for line in source:
    print(line.rstrip("\n")[:width])
