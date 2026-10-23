#!/usr/bin/env python3
"""Which K7 root cells take the direct path and which are split (kernel-only S({0..7}) <= 2.552, half domain).

A root cell whose recorded tree has at most LCAP leaves gets one walk theorem (tools/gen_k7.py cells: Bohr59aK7C/Cnnnn).
A larger cell is cut into sub-boxes of at most LCAP leaves by tools/gen_k7split.py, run once per shard s on all the split
cells of s (cell i lies in shard i mod 576) with tag H<sss>; its cell theorem is cellH7_<i> in module Bohr59aK7HG.H<sss>C<i>.
LCAP = 64: a walk declaration needs ~50 KB per key reference, and a leaf has 729 keys.

usage: k7_split_plan.py INDEX_DIR OUT_JSON   (INDEX_DIR: the trees.json written by tools/gen_k7.py index)
"""
import json, os, sys

NSH, NCELL, LCAP = 576, 2048, 64


def leaves(t):
    n, stack = 0, [t]
    while stack:
        x = stack.pop()
        if x == 'L':
            n += 1
        else:
            if not (isinstance(x, list) and len(x) == 4 and x[0] == 'S'):
                sys.exit('PLAN FAILED: bad tree node')
            stack.extend((x[2], x[3]))
    return n


def main():
    idir, out = sys.argv[1], sys.argv[2]
    trees = json.load(open(os.path.join(idir, 'trees.json')))
    if sorted(int(i) for i in trees) != list(range(NCELL)):
        sys.exit('PLAN FAILED: trees.json does not hold the root cells 0..%d' % (NCELL - 1))
    nl = {int(i): leaves(t) for i, t in trees.items()}
    direct = [i for i in range(NCELL) if nl[i] <= LCAP]
    split = {}
    for i in range(NCELL):
        if nl[i] > LCAP:
            split.setdefault(i % NSH, []).append(i)
    heavy = {str(i): ['Bohr59aK7HG.H%03dC%d' % (s, i), 'cellH7_%d' % i] for s, cs in split.items() for i in cs}
    plan = dict(lcap=LCAP, cells=NCELL, leaves=sum(nl.values()), direct=direct,
                direct_leaves=sum(nl[i] for i in direct),
                split={'%d' % s: cs for s, cs in sorted(split.items())}, split_cells=len(heavy),
                split_leaves=sum(nl[int(i)] for i in heavy), heavy=heavy)
    json.dump(plan, open(out, 'w'), indent=0)
    print('direct cells', len(direct), 'leaves', plan['direct_leaves'], '| split cells', len(heavy), 'leaves',
          plan['split_leaves'], 'in', len(split), 'shards')


if __name__ == '__main__':
    main()
