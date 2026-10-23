/-!
# Data format of the Sidon certificates (core Lean only)

Certificates for `S({0..k}) ≤ B` (`k = 5`: `B = 2187/1000`, one shard; `k = 6`: `B = 2363/1000`, 48 shards), exported from the
frozen v3 files `bb5_t2187.json` and `bb6/sh*.json`.

* Phases are in units of `π`.  `D = k - 1` coordinates (the phases of `w_2, …, w_k`; `w_0 = w_1 = 1`).
* Root grid: `n0^D` cells of half-width `1/n0`; root cell `i` has the mixed-radix digits `idx_0 … idx_{D-1}` of `i` in base `n0`
  with `idx_{D-1}` least significant (Python's `itertools.product(range(n0), repeat=D)` order), centre
  `-1 + (2 idx_d + 1)/n0` in coordinate `d`.
* `Tree.split d lo hi` halves coordinate `d`; `lo` is the lower half (Python: `node[2]`), `hi` the upper half (`node[3]`).
* A leaf with centres `c_d` and half-widths `h_d` has the `3^D` vertices with coordinate `d` one of
  `e^{iπ(c_d - h_d)}`, `e^{iπ(c_d + h_d)}` (corners) and `e^{iπ c_d}/cos(π h_d)` (tangent point).
* Vertex keys: `Comp.mk false m 0` is the corner `e^{iπ m/512}`; `Comp.mk true m j` is the tangent point
  `e^{iπ m/512}/cos(π/2^j)`.  (Python key `['c', q]` ↦ `⟨false, 512 q, 0⟩`; `['t', q, h]` ↦ `⟨true, 512 q, log₂(1/h)⟩`.)
* `VCert.y` lists `re y_1, im y_1, …, re y_k, im y_k` (`2k` rationals: the float64 values of the frozen file, exactly).

Decoding is not trusted.  The checker accepts a `Shard` only if its cells are exactly the root cells `i < n0^D` with
`i % nsh = s`, in increasing order, and every vertex of every leaf has a certificate (looked up by key, the key compared after
lookup) that passes the exact checks; the soundness proof does not depend on how the `Shard` value was produced.
-/

namespace Bohr59aCore

/-- One coordinate of a vertex: `tan = false`: the corner `e^{iπ m/512}`; `tan = true`: the tangent point
`e^{iπ m/512}/cos(π/2^j)`. -/
structure Comp where
  tan : Bool
  m : Int
  j : Nat
deriving DecidableEq, Hashable, Repr, Inhabited

/-- A vertex certificate: the key (coordinates `2, …, k` of the vertex) and `re y_1, im y_1, …, re y_k, im y_k`. -/
structure VCert where
  key : Array Comp
  y : Array Rat
deriving Inhabited

/-- The split tree of a root cell. -/
inductive Tree where
  | leaf
  | split (d : Nat) (lo hi : Tree)
deriving Inhabited

/-- One shard: the root cells `i` (with their trees) and the vertex certificates their leaves use. -/
structure Shard where
  k : Nat
  n0 : Nat
  nsh : Nat
  s : Nat
  bnum : Nat
  bden : Nat
  cells : Array (Nat × Tree)
  verts : Array VCert
deriving Inhabited

end Bohr59aCore
