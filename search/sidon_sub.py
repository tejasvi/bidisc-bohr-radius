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
usage: sidon_sub.py K TARGET_DECIMAL OUT.json CELL L J   (n0 = 4, hmin = 1/4096 fixed; see SUB-BOX MODE)
HALF DOMAIN (v3): phi_2 in [0, pi] only (conjugation symmetry N(conj w) = N(w)); root grid n0/2 cells in phi_2, n0 in the others.   (sharded runs write {'cells': {idx: tree}}; merge_bb.py)
"""
import itertools, json, math, sys, time, warnings
from fractions import Fraction
import numpy as np
import cvxpy as cp
warnings.filterwarnings('ignore')

K = int(sys.argv[1]); TSTR = sys.argv[2]; TARGET = float(Fraction(TSTR)); OUT = sys.argv[3]
N0 = 4
HMIN = Fraction(1, 4096)
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
# SUB-BOX MODE (sidon_sub.py): args after the usual ones are replaced by: CELL L J
#   root cell index CELL (half-domain enumeration as in sidon_bb3.py), forced split depth L (dims cycling 0..D-1),
#   sub-box J in [0, 2^L): bit b of J (from the top level down) picks lo (0) or hi (1) at forced level b.
CELL, LV, JB = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
t0 = time.time()
w = Fraction(2, N0)
ranges = [range(N0 // 2)] + [range(N0)] * (D - 1)
idx = list(itertools.product(*ranges))[CELL]
cs = [(i + Fraction(1, 2)) * w if d == 0 else Fraction(-1) + (i + Fraction(1, 2)) * w for d, i in enumerate(idx)]
hs = [w / 2] * D
for b in range(LV):
    d = b % D
    hs[d] = hs[d] / 2
    bit = (JB >> (LV - 1 - b)) & 1
    cs[d] = cs[d] + hs[d] if bit else cs[d] - hs[d]
tree = solve_box(cs, hs)
def kstr(key):
    return [[kk[0]] + [str(x) for x in kk[1:]] for kk in key]
verts = [[kstr(kk), [float(z) for c in cache[kk][1] for z in (c.real, c.imag)]] for kk in sorted(used, key=str)]
json.dump({'k': K, 'target': TSTR, 'n0': N0, 'domain': 'half', 'cell': CELL, 'L': LV, 'j': JB, 'tree': tree, 'verts': verts}, open(OUT, 'w'))
print(f'SUB k={K} cell={CELL} L={LV} j={JB}: leaves {stats["leaves"]}, fails {stats["fails"]}, sdp {stats["sdp"]}, verts {len(verts)}, '
      f'max vertex val {stats["maxval"]:.12f} (B^2 = {B2:.12f}), {time.time() - t0:.0f} s')
