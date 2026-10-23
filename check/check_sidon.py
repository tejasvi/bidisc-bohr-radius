#!/usr/bin/env python3
"""Rigorous checker for the certificates of Proposition 4.2 of the paper "A lower bound for the Bohr radius of the bidisc".

usage: python3 -I check_sidon.py CERTIFICATE.json BOUND      (exit status 0 only on VERIFIED; refuses to run under python -O)

It checks that N(w) <= BOUND for every w = (1, 1, w_2, ..., w_k) with |w_j| = 1, where N is the dual norm of Lemma 4.1;
by Lemma 4.1(a) this gives S({0, 1, ..., k}) <= BOUND. The certificate tiles the phases, in units of pi, [-1, 1]^(k-1) by
boxes: a uniform grid of n0^(k-1) boxes, refined by bisection at exact midpoints. For a box with centre c and
half-widths h (each at most 1/4), the unimodular points lie in the product of the triangles with vertices
exp(i pi (c - h)), exp(i pi (c + h)) and exp(i pi c)/cos(pi h) (Lemma 4.1(d)). N is convex (Lemma 4.1(b)), so it suffices
that N(v) < BOUND at the 3^(k-1) vertices v of this product. For each vertex the certificate supplies y such that
  (i)  the Hermitian Toeplitz matrix T(y) with unit diagonal is positive definite (all leading principal minors > 0), and
  (ii) v^* T(y)^{-1} v < BOUND^2,
which gives N(v)^2 <= v^* T(y)^{-1} v < BOUND^2 (Lemma 4.1(c)). All checks use Arb balls at 128 bits, and the binary64
entries of y are read exactly. certificate/FORMAT.md describes the file format."""
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
    if not isinstance(cert, dict) or not {'k', 'n0', 'tree', 'verts'} <= set(cert):
        fail('malformed certificate')
    tgt = Fraction(sys.argv[2])
    k, n0, tree, verts = cert['k'], cert['n0'], cert['tree'], cert['verts']
    if not (isinstance(k, int) and 2 <= k <= 12 and isinstance(n0, int) and n0 >= 4 and isinstance(tree, list)
            and isinstance(verts, list)):
        fail('bad k / n0 / tree / verts')
    D = k - 1
    if len(tree) != n0 ** D:
        fail(f'root grid has {len(tree)} cells, expected {n0 ** D}')
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
    for idx, cell in zip(itertools.product(range(n0), repeat=D), tree):
        walk(cell, [Fraction(-1) + (i + Fraction(1, 2)) * w for i in idx], [w / 2] * D, 0)
    print(f'VERIFIED: S({{0..{k}}}) <= {sys.argv[2]}  ({stats["leaves"]} leaves, {stats["vchecks"]} vertex certificates, '
          f'min slack in B^2 {stats["min_slack"]})')

main()
