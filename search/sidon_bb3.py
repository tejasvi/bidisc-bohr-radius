#!/usr/bin/env python3
"""Branch-and-bound search for S({0..k}) <= B with PER-VERTEX certificates (search side; checker check/check_shard.py).

N(w) := max{Re sum_j conj(w_j) c_j : |sum_j c_j z^j| <= 1 on T} is convex in w in C^(k+1); S({0..k}) = max N over
w_0 = w_1 = 1, w_j = e^{i phi_j} (j = 2..k).  A phase box (centre pi*c, half-width pi*h per coordinate, units of pi)
lies in the product of triangles {e^{i pi (c-h)}, e^{i pi (c+h)}, e^{i pi c}/cos(pi h)}; by convexity
max_box N <= max over the 3^(k-1) vertices.  Each vertex v gets its own certificate y (Lemma 4.1(c) of the paper):
T(y) Hermitian Toeplitz, unit diagonal, positive definite, and v^* T(y)^{-1} v < B^2  =>  N(v) < B.
Vertex keys are exact (units of pi): per coordinate ('c', q) = e^{i pi q} or ('t', q, h) = e^{i pi q}/cos(pi h).

Output JSON: {"k", "target" (decimal string), "n0", "tree", "verts": [[key, [y re/im ...]], ...]}
tree node = "L" | ["S", dim, lo, hi]; root = uniform n0^(k-1) grid on [-1, 1]^(k-1) (units of pi), row-major.
usage: sidon_bb3.py K TARGET_DECIMAL OUT.json [n0] [hmin] [shard nshards]
HALF DOMAIN (v3): phi_2 in [0, pi] only (conjugation symmetry N(conj w) = N(w)); root grid n0/2 cells in phi_2, n0 in the others.   (sharded runs write {'cells': {idx: tree}}; merge_bb.py)
"""
import itertools, json, math, sys, time, warnings
from fractions import Fraction
import numpy as np
import cvxpy as cp
warnings.filterwarnings('ignore')

K = int(sys.argv[1]); TSTR = sys.argv[2]; TARGET = float(Fraction(TSTR)); OUT = sys.argv[3]
N0 = int(sys.argv[4]) if len(sys.argv) > 4 else 16
HMIN = Fraction(sys.argv[5]) if len(sys.argv) > 5 else Fraction(1, 2 ** 16)
SHARD = int(sys.argv[6]) if len(sys.argv) > 7 else 0
NSH = int(sys.argv[7]) if len(sys.argv) > 7 else 1
D = K - 1
B2 = TARGET * TARGET
MARGIN = 1e-10

# point SDP: min t s.t. [[T(y), v], [v^*, t]] >= 0
Vr = cp.Parameter(K + 1); Vi = cp.Parameter(K + 1)
y = cp.Variable(K, complex=True); tt = cp.Variable()
Tv = cp.Variable((K + 1, K + 1), hermitian=True)
cons = [Tv[j, j] == 1 for j in range(K + 1)]
for d in range(1, K + 1):
    for j in range(K + 1 - d):
        cons.append(Tv[j, j + d] == y[d - 1])
vv = Vr + 1j * Vi
M = cp.bmat([[Tv, cp.reshape(vv, (K + 1, 1), order='C')],
             [cp.reshape(cp.conj(vv), (1, K + 1), order='C'), cp.reshape(tt, (1, 1), order='C')]])
cons.append(M >> 0)
prob = cp.Problem(cp.Minimize(tt), cons)

def Tmat(yv):
    T = np.eye(K + 1, dtype=complex)
    for j in range(K + 1):
        for l in range(j + 1, K + 1):
            T[j, l] = yv[l - j - 1]; T[l, j] = np.conj(yv[l - j - 1])
    return T

def coord(key):
    if key[0] == 'c':
        return complex(np.exp(1j * math.pi * float(key[1])))
    return complex(np.exp(1j * math.pi * float(key[1])) / math.cos(math.pi * float(key[2])))

cache = {}
stats = {'sdp': 0, 'leaves': 0, 'fails': 0, 'maxval': 0.0}
def vertex_val(vkey):
    if vkey in cache:
        return cache[vkey][0]
    v = np.array([1, 1] + [coord(kk) for kk in vkey])
    Vr.value = v.real; Vi.value = v.imag
    best = (math.inf, None)
    try:
        prob.solve(solver=cp.CLARABEL); stats['sdp'] += 1
        y0 = y.value
    except Exception:
        y0 = None
    if y0 is not None:
        for eps in (1e-9, 1e-8, 1e-7, 1e-6, 1e-5, 1e-4):
            yv = (1 - eps) * y0
            T = Tmat(yv)
            try:
                np.linalg.cholesky(T)
            except np.linalg.LinAlgError:
                continue
            val = float(np.real(np.conj(v) @ np.linalg.solve(T, v)))
            if val < best[0]:
                best = (val, yv)
    cache[vkey] = best
    return best[0]

def box_keys(cs, hs):
    opts = [[('c', cs[d] - hs[d]), ('c', cs[d] + hs[d]), ('t', cs[d], hs[d])] for d in range(D)]
    return [tuple(opts[d][cb[d]] for d in range(D)) for cb in itertools.product(range(3), repeat=D)]

used = set()
fails = []
def solve_box(cs, hs):
    keys = box_keys(cs, hs)
    vals = [vertex_val(kk) for kk in keys]
    if max(vals) <= B2 - MARGIN:
        stats['leaves'] += 1; stats['maxval'] = max(stats['maxval'], max(vals))
        used.update(keys)
        return "L"
    d = max(range(D), key=lambda i: hs[i])
    if hs[d] <= HMIN:
        stats['fails'] += 1; fails.append(([float(c) for c in cs], [float(h) for h in hs], max(vals)))
        return ["F"]
    h2 = list(hs); h2[d] = hs[d] / 2
    c0 = list(cs); c0[d] = cs[d] - h2[d]
    c1 = list(cs); c1[d] = cs[d] + h2[d]
    return ["S", d, solve_box(c0, h2), solve_box(c1, h2)]

sys.setrecursionlimit(100000)
t0 = time.time()
w = Fraction(2, N0)
cells = {}
ranges = [range(N0 // 2)] + [range(N0)] * (D - 1)
NCELL = (N0 // 2) * N0 ** (D - 1)
for n, idx in enumerate(itertools.product(*ranges)):
    if n % NSH != SHARD:
        continue
    cs = [(i + Fraction(1, 2)) * w if d == 0 else Fraction(-1) + (i + Fraction(1, 2)) * w for d, i in enumerate(idx)]
    cells[n] = solve_box(cs, [w / 2] * D)
    if (n + 1) % max(1, NCELL // 20) == 0:
        print(f'  cells {n + 1}/{N0 ** D}  leaves {stats["leaves"]}  fails {stats["fails"]}  sdp {stats["sdp"]}  '
              f'{time.time() - t0:.0f} s', flush=True)

def kstr(key):
    return [[kk[0]] + [str(x) for x in kk[1:]] for kk in key]
verts = [[kstr(kk), [float(z) for c in cache[kk][1] for z in (c.real, c.imag)]] for kk in sorted(used, key=str)]
if NSH == 1:
    json.dump({'k': K, 'target': TSTR, 'n0': N0, 'domain': 'half', 'tree': [cells[n] for n in range(NCELL)], 'verts': verts}, open(OUT, 'w'))
else:
    json.dump({'k': K, 'target': TSTR, 'n0': N0, 'domain': 'half', 'cells': {str(n): t for n, t in cells.items()}, 'verts': verts,
               'shard': SHARD, 'nshards': NSH}, open(OUT, 'w'))
print(f'k={K} target={TSTR}: leaves {stats["leaves"]}, fails {stats["fails"]}, sdp {stats["sdp"]}, verts {len(verts)}, '
      f'max vertex val {stats["maxval"]:.12f} (B^2 = {B2:.12f}), {time.time() - t0:.0f} s')
for f in fails[:10]:
    print('  FAIL c=', np.round(f[0], 6), 'h=', f[1], 'val', f[2])
