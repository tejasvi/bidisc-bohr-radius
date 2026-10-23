#!/usr/bin/env python3
"""Merge sharded sidon_bb2.py outputs into one certificate.  usage: merge_bb.py OUT.json SHARD1.json ...
Vertex keys certified in several shards keep the first y seen (each is checked independently by check/check_sidon.py)."""
import json, sys
parts = [json.load(open(f)) for f in sys.argv[2:]]
k, n0, tgt = parts[0]['k'], parts[0]['n0'], parts[0]['target']
D = k - 1
cells, verts, seen = {}, [], set()
for p in parts:
    if (p['k'], p['n0'], p['target']) != (k, n0, tgt):
        sys.exit('inconsistent shards')
    for n, t in p['cells'].items():
        if n in cells: sys.exit(f'cell {n} in two shards')
        cells[n] = t
    for key, y in p['verts']:
        ks = json.dumps(key)
        if ks not in seen:
            seen.add(ks); verts.append([key, y])
missing = [n for n in range(n0 ** D) if str(n) not in cells]
if missing: sys.exit(f'missing cells {missing[:10]} ({len(missing)})')
bad = sum(1 for n in range(n0 ** D) if 'F' in json.dumps(cells[str(n)]))
json.dump({'k': k, 'target': tgt, 'n0': n0, 'tree': [cells[str(n)] for n in range(n0 ** D)], 'verts': verts}, open(sys.argv[1], 'w'))
print(f'merged {len(parts)} shards: {n0 ** D} cells, {len(verts)} vertices, cells with failures: {bad}')
