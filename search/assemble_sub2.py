#!/usr/bin/env python3
"""Assemble sub-box results of MIXED depths (sidon_sub.py outputs with fields cell, L, j) into a shard file: for each root
cell, tree(level, j) = the computed sub-box tree if (level, j) was computed, else the forced split along dim level mod D
into (level+1, 2j) and (level+1, 2j+1).  If several computed results nest, the shallowest one is used.
usage: assemble_sub2.py OUT_SHARD.json SHARD NSHARDS SUB.json ..."""
import json, sys
out, shard, nsh = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
res, meta, verts, seen = {}, None, [], set()
for f in sys.argv[4:]:
    d = json.load(open(f))
    key = (d['k'], d['target'], d['n0'], d['domain'])
    if meta is None: meta = key
    if key != meta: sys.exit('inconsistent sub-box metadata')
    if d['cell'] % nsh != shard: continue
    res[(d['cell'], d['L'], d['j'])] = (d['tree'], d['verts'])
k, tgt, n0, dom = meta; D = k - 1
ncell = (n0 // 2) * n0 ** (D - 1)
maxL = max(L for (_, L, _) in res)
used = set()
def rec(cell, level, j):
    if (cell, level, j) in res:
        used.add((cell, level, j)); return res[(cell, level, j)][0]
    if level >= maxL:
        sys.exit(f'cell {cell}: sub-box (L={level}, j={j}) missing')
    return ['S', level % D, rec(cell, level + 1, 2 * j), rec(cell, level + 1, 2 * j + 1)]
cells = {}
for cell in sorted({c for (c, _, _) in res}):
    cells[str(cell)] = rec(cell, 0, 0)
for key in sorted(used):
    for kk, y in res[key][1]:
        ks = json.dumps(kk)
        if ks not in seen:
            seen.add(ks); verts.append([kk, y])
want = [n for n in range(ncell) if n % nsh == shard]
missing = [n for n in want if str(n) not in cells]
if missing: sys.exit(f'shard {shard}: cells missing {missing}')
json.dump({'k': k, 'target': tgt, 'n0': n0, 'domain': dom, 'cells': cells, 'verts': verts, 'shard': shard, 'nshards': nsh}, open(out, 'w'))
print(f'assembled shard {shard}: {len(cells)} cells, {len(used)} sub-boxes used, {len(verts)} vertices')
