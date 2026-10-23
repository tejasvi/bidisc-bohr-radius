#!/usr/bin/env python3
"""Rigorous checker for one file of a sharded certificate of Proposition 4.2 of the paper "A lower bound for the Bohr
radius of the bidisc" (the certificate for S({0, ..., 6}) <= 2.363 consists of 48 such files, the certificate for
S({0, ..., 7}) <= 2.552 of 576).

usage: python3 -I check_shard.py SHARD.json BOUND      (exit status 0 only on VERIFIED; refuses to run under python -O)

A shard file lists some cells of the initial grid ("cells": {index: tree}) and the vertex certificates they need
("verts"). For each listed cell the program makes the checks of check_sidon.py: it rebuilds the boxes from the grid and
the recorded bisections, forms the 3^(k-1) vertices of each box (Lemma 4.1(d)), and checks for each vertex v that the
Hermitian Toeplitz matrix T(y) is positive definite (all leading principal minors > 0) and v^* T(y)^{-1} v < BOUND^2
(Lemma 4.1(c)), in Arb balls at 128 bits. With "domain": "half" (the certificate for S({0, ..., 7})) the grid covers
phi_2 in [0, pi] only, which suffices by Lemma 4.1(e). It ends with a line "VERIFIED SHARD: ..." that names the file,
gives its SHA-256 checksum and lists the cells it covered; check_cover.py checks these lines. The program also accepts a
single-file certificate like check_sidon.py. certificate/FORMAT.md describes the file formats."""
import itertools, json, sys
from fractions import Fraction
if sys.flags.optimize:
    sys.exit('refusing to run with python -O')
from flint import arb, acb, acb_mat, fmpq, ctx

ctx.prec = 128

def fail(msg):
    print('NOT VERIFIED:', msg); sys.exit(1)

def parse_key(raw, D):
    if not (isinstance(raw, list) and len(raw) == D):
        fail('bad vertex key')
    out = []
    for kk in raw:
        if isinstance(kk, list) and len(kk) == 2 and kk[0] == 'c':
            out.append(('c', Fraction(kk[1])))
        elif isinstance(kk, list) and len(kk) == 3 and kk[0] == 't':
            q, h = Fraction(kk[1]), Fraction(kk[2])
            if not (0 < h <= Fraction(1, 4)):
                fail('tangent half-width out of range')
            out.append(('t', q, h))
        else:
            fail('bad vertex key component')
    return tuple(out)

def main():
    cert = json.load(open(sys.argv[1]))
    sharded = isinstance(cert, dict) and 'cells' in cert and 'tree' not in cert
    if not isinstance(cert, dict) or not ({'k', 'n0', 'verts'} <= set(cert)) or not (sharded or 'tree' in cert):
        fail('malformed certificate')
    tgt = Fraction(sys.argv[2])
    k, n0, verts = cert['k'], cert['n0'], cert['verts']
    if sharded:
        if not isinstance(cert['cells'], dict): fail('bad cells')
        cellmap = {}
        for key_, t in cert['cells'].items():
            if not (isinstance(key_, str) and key_.isdigit()): fail('bad cell index')
            cellmap[int(key_)] = t
        tree = None
    else:
        tree = cert['tree']
    if not (isinstance(k, int) and 2 <= k <= 12 and isinstance(n0, int) and n0 >= 4 and (sharded or isinstance(tree, list))
            and isinstance(verts, list)):
        fail('bad k / n0 / tree / verts')
    D = k - 1
    half = cert.get('domain') == 'half'
    if half and n0 % 2:
        fail('half domain needs even n0')
    ncell = (n0 // 2) * n0 ** (D - 1) if half else n0 ** D
    if not sharded and len(tree) != ncell:
        fail(f'root grid has {len(tree)} cells, expected {ncell}')
    if sharded and not all(0 <= i < ncell for i in cellmap):
        fail('cell index out of range')
    table = {}
    for ent in verts:
        if not (isinstance(ent, list) and len(ent) == 2 and isinstance(ent[1], list) and len(ent[1]) == 2 * k
                and all(isinstance(x, float) for x in ent[1])):
            fail('bad vertex entry')
        key = parse_key(ent[0], D)
        if key in table:
            fail('duplicate vertex key')
        table[key] = ent[1]
    B2 = arb(fmpq(tgt.numerator, tgt.denominator)) ** 2
    done = {}
    stats = {'leaves': 0, 'vchecks': 0, 'min_slack': None}

    def unit(q):
        s, c = arb.sin_cos_pi_fmpq(fmpq(q.numerator, q.denominator))
        return acb(c, s)

    def coord(kk):
        if kk[0] == 'c':
            return unit(kk[1])
        _, ch = arb.sin_cos_pi_fmpq(fmpq(kk[2].numerator, kk[2].denominator))
        return unit(kk[1]) / ch

    def check_vertex(key):
        if key in done:
            return
        if key not in table:
            fail(f'missing vertex certificate {key}')
        y = table[key]
        yc = [acb(arb(y[2 * j]), arb(y[2 * j + 1])) for j in range(k)]
        T = acb_mat(k + 1, k + 1)
        for j in range(k + 1):
            T[j, j] = acb(1)
            for l in range(j + 1, k + 1):
                T[j, l] = yc[l - j - 1]; T[l, j] = yc[l - j - 1].conjugate()
        for m in range(1, k + 2):
            Mm = acb_mat(m, m)
            for a in range(m):
                for b in range(m):
                    Mm[a, b] = T[a, b]
            if not (Mm.det().real > 0):
                fail(f'T not certified positive definite at vertex {key}')
        v = acb_mat(k + 1, 1)
        v[0, 0] = acb(1); v[1, 0] = acb(1)
        for d in range(D):
            v[d + 2, 0] = coord(key[d])
        x = T.solve(v)
        val = acb(0)
        for j in range(k + 1):
            val += v[j, 0].conjugate() * x[j, 0]
        slack = B2 - val.real
        if not (slack > 0):
            fail(f'vertex value not below B^2 at {key}: {val}')
        lo = slack.lower()
        if stats['min_slack'] is None or lo < stats['min_slack']:
            stats['min_slack'] = lo
        done[key] = True
        stats['vchecks'] += 1

    def leaf(cs, hs):
        for d in range(D):
            if not (0 < hs[d] <= Fraction(1, 4)):
                fail('leaf half-width out of range')
        opts = [[('c', cs[d] - hs[d]), ('c', cs[d] + hs[d]), ('t', cs[d], hs[d])] for d in range(D)]
        for cb in itertools.product(range(3), repeat=D):
            check_vertex(tuple(opts[d][cb[d]] for d in range(D)))
        stats['leaves'] += 1

    def walk(node, cs, hs, depth):
        if depth > 400:
            fail('tree too deep')
        if node == 'L':
            leaf(cs, hs)
        elif isinstance(node, list) and len(node) == 4 and node[0] == 'S' and isinstance(node[1], int) and 0 <= node[1] < D:
            d = node[1]
            h2 = list(hs); h2[d] = hs[d] / 2
            c0 = list(cs); c0[d] = cs[d] - h2[d]
            c1 = list(cs); c1[d] = cs[d] + h2[d]
            walk(node[2], c0, h2, depth + 1); walk(node[3], c1, h2, depth + 1)
        else:
            fail(f'bad node {str(node)[:40]}')

    sys.setrecursionlimit(10000)
    w = Fraction(2, n0)
    ranges = ([range(n0 // 2)] + [range(n0)] * (D - 1)) if half else [range(n0)] * D
    for n, idx in enumerate(itertools.product(*ranges)):
        if sharded:
            if n not in cellmap: continue
            cell = cellmap[n]
        else:
            cell = tree[n]
        cs = [((i + Fraction(1, 2)) * w if (half and d == 0) else Fraction(-1) + (i + Fraction(1, 2)) * w) for d, i in enumerate(idx)]
        walk(cell, cs, [w / 2] * D, 0)
    if sharded:
        import hashlib, os
        hf = hashlib.sha256()
        with open(sys.argv[1], 'rb') as fh:
            for blk in iter(lambda: fh.read(1 << 24), b''):
                hf.update(blk)
        idxs = sorted(cellmap)
        dg = hashlib.sha256(','.join(map(str, idxs)).encode()).hexdigest()[:16]
        print(f'VERIFIED SHARD: k={k} n0={n0} domain={"half" if half else "full"} target={sys.argv[2]} cells={len(idxs)} '
              f'leaves={stats["leaves"]} vertices={stats["vchecks"]} file={os.path.basename(sys.argv[1])} sha256={hf.hexdigest()} '
              f'min_slack={stats["min_slack"]} cells_digest={dg} '
              f'cells={",".join(map(str, idxs))}')
        return
    print(f'VERIFIED: S({{0..{k}}}) <= {sys.argv[2]}  (domain {"half (conjugation)" if half else "full"}, {stats["leaves"]} leaves, {stats["vchecks"]} vertex certificates, '
          f'min slack in B^2 {stats["min_slack"]})')

main()
