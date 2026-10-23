#!/usr/bin/env python3
"""Coverage check for a sharded certificate of Proposition 4.2 of the paper "A lower bound for the Bohr radius of the bidisc".

usage: python3 -I check_cover.py SHARD_DIR LOG...      (exit status 0 only on COVERED; refuses to run under python -O)

It reads the lines "VERIFIED SHARD: ..." that check_shard.py prints, recomputes the SHA-256 checksum of every shard file
they name in SHARD_DIR and compares it with the logged one, rejects a file named twice, checks that all shards have the
same k, n0, domain and bound, and checks that every cell of the initial grid occurs in exactly one shard. It trusts that
the lines come from runs of check_shard.py."""
import sys, re, os, hashlib
if sys.flags.optimize:
    sys.exit('refusing to run with python -O')
sd = sys.argv[1]
seen, meta, leaves, verts, files = {}, None, 0, 0, set()
for fn in sys.argv[2:]:
    for line in open(fn):
        if not line.startswith('VERIFIED SHARD:'): continue
        m = dict(re.findall(r'(\w+)=(\S+)', line))
        if 'file' not in m or 'sha256' not in m: sys.exit(f'NOT COVERED: log {fn} lacks file/sha256')
        if m['file'] in files: sys.exit(f'NOT COVERED: shard file {m["file"]} listed twice')
        files.add(m['file'])
        h = hashlib.sha256()
        with open(os.path.join(sd, m['file']), 'rb') as fh:
            for blk in iter(lambda: fh.read(1 << 24), b''):
                h.update(blk)
        if h.hexdigest() != m['sha256']: sys.exit(f'NOT COVERED: sha256 mismatch for {m["file"]} (log {fn})')
        key = (m['k'], m['n0'], m['domain'], m['target'])
        if meta is None: meta = key
        if key != meta: sys.exit('NOT COVERED: inconsistent shard metadata')
        for i in m['cells'].split(','):
            i = int(i)
            if i in seen: sys.exit(f'NOT COVERED: cell {i} in two shards')
            seen[i] = fn
        leaves += int(m['leaves']); verts += int(m['vertices'])
if meta is None: sys.exit('NOT COVERED: no shard lines')
k, n0, dom, tgt = int(meta[0]), int(meta[1]), meta[2], meta[3]
ncell = (n0 // 2) * n0 ** (k - 2) if dom == 'half' else n0 ** (k - 1)
missing = [i for i in range(ncell) if i not in seen]
if missing: sys.exit(f'NOT COVERED: {len(missing)} root cells missing, e.g. {missing[:5]}')
print(f'COVERED: S({{0..{k}}}) <= {tgt}: {ncell} root cells, {len(files)} shard files (sha256 recomputed and matched), '
      f'{leaves} leaves, {verts} vertex checks (shared vertices counted per shard)')
