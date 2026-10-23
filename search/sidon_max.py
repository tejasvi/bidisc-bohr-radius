# Numerical max of N(w) over normalized phases (w_0 = w_1 = 1) via the point SDP (the dual of Lemma 4.1(c) is exact at the optimum).
import sys, math, numpy as np, cvxpy as cp, warnings
from scipy.optimize import minimize
warnings.filterwarnings('ignore')
K = int(sys.argv[1]); NS = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
Vr = cp.Parameter(K + 1); Vi = cp.Parameter(K + 1)
y = cp.Variable(K, complex=True); tt = cp.Variable()
Tv = cp.Variable((K + 1, K + 1), hermitian=True)
cons = [Tv[j, j] == 1 for j in range(K + 1)]
for d in range(1, K + 1):
    for j in range(K + 1 - d): cons.append(Tv[j, j + d] == y[d - 1])
vv = Vr + 1j * Vi
cons.append(cp.bmat([[Tv, cp.reshape(vv, (K + 1, 1), order='C')], [cp.reshape(cp.conj(vv), (1, K + 1), order='C'), cp.reshape(tt, (1, 1), order='C')]]) >> 0)
prob = cp.Problem(cp.Minimize(tt), cons)
def N(ph):
    v = np.concatenate([[1, 1], np.exp(1j * np.asarray(ph))])
    Vr.value = v.real; Vi.value = v.imag
    try:
        prob.solve(solver=cp.CLARABEL); return math.sqrt(max(prob.value, 0))
    except Exception:
        return 0.0
rng = np.random.default_rng(seed)
res = []
for s in range(NS):
    r = minimize(lambda p: -N(p), rng.uniform(-np.pi, np.pi, K - 1), method='Nelder-Mead',
                 options={'maxiter': 3000, 'xatol': 1e-8, 'fatol': 1e-11})
    res.append((-r.fun, r.x))
res.sort(key=lambda z: -z[0])
print(f'k={K}: best N = {res[0][0]:.9f}  (sqrt(k) = {math.sqrt(K):.6f}); top values:', [round(z[0], 7) for z in res[:8]])
print('best phases', np.round(np.mod(res[0][1] + np.pi, 2 * np.pi) - np.pi, 6).tolist())
