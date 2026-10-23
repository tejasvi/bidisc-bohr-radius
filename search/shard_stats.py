#!/usr/bin/env python3
"""Leaf/split/half-width statistics over shard files (reads only the "cells" part, which precedes "verts").
usage: shard_stats.py N0 HALF(0|1) SHARD.json ..."""
import sys, json
from fractions import Fraction
from collections import Counter
n0, half = int(sys.argv[1]), sys.argv[2] == '1'
hist, hmin, hmax, nleaf, nsplit, ncells = Counter(), None, None, 0, 0, 0
for fn in sys.argv[3:]:
    with open(fn, 'rb') as f:
        buf = b''
        while b'"verts"' not in buf:
            blk = f.read(1 << 22)
            if not blk: break
            buf += blk
    pre = buf[:buf.index(b'"verts"')].decode().rstrip().rstrip(',') + '}'
    d = json.loads(pre); D = d['k'] - 1
    w = Fraction(2, n0)
    def walk(node, hs, depth):
        global hmin, hmax, nleaf, nsplit
        if node == 'L':
            nleaf += 1; hist[depth] += 1
            lo, hi = min(hs), max(hs)
            hmin = lo if hmin is None or lo < hmin else hmin
            hmax = hi if hmax is None or hi > hmax else hmax
            return
        nsplit += 1; dd = node[1]; h2 = list(hs); h2[dd] /= 2
        walk(node[2], h2, depth + 1); walk(node[3], h2, depth + 1)
    sys.setrecursionlimit(10000)
    for c, t in d['cells'].items():
        ncells += 1; walk(t, [w / 2] * D, 0)
print(f'cells={ncells} leaves={nleaf} splits={nsplit} leaf half-width (units of pi) min={hmin} max={hmax} max depth={max(hist)}')
