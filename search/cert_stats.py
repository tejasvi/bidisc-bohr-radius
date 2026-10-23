#!/usr/bin/env python3
"""Statistics of a sidon_bb2.py certificate: leaves, distinct vertices, leaf half-widths (units of pi), depth histogram.
usage: cert_stats.py CERT.json"""
import json, sys, itertools
from fractions import Fraction
from collections import Counter
d = json.load(open(sys.argv[1])); k, n0, tree = d['k'], d['n0'], d['tree']; D = k - 1
half = d.get('domain') == 'half'
hist, hmin, hmax, nleaf, nsplit = Counter(), None, None, 0, 0
def walk(node, hs, depth):
    global hmin, hmax, nleaf, nsplit
    if node == 'L':
        nleaf += 1; hist[depth] += 1
        lo, hi = min(hs), max(hs)
        hmin = lo if hmin is None or lo < hmin else hmin
        hmax = hi if hmax is None or hi > hmax else hmax
        return
    nsplit += 1
    dd = node[1]; h2 = list(hs); h2[dd] = hs[dd] / 2
    walk(node[2], h2, depth + 1); walk(node[3], h2, depth + 1)
w = Fraction(2, n0)
for cell in tree:
    walk(cell, [w / 2] * D, 0)
print(f'k={k} target={d["target"]} domain={"half (conjugation)" if half else "full [-pi,pi]^" + str(D)} n0={n0} root cells={len(tree)}')
print(f'leaves={nleaf} splits={nsplit} distinct vertex certificates={len(d["verts"])}')
print(f'leaf half-width (units of pi): smallest coordinate {hmin} = {float(hmin):.6f}, largest coordinate {hmax} = {float(hmax):.6f}')
print('leaves by depth (number of bisections below the root cell):', dict(sorted(hist.items())))
