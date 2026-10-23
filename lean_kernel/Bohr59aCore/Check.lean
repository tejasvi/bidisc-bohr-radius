import Bohr59aCore.Format
import C64Core.Ival
import Std.Data.HashMap

/-!
# The shard checker (core Lean only)

For each vertex certificate (key, `y`) with `n = k + 1`:
* `T = T(y)` is the Hermitian Toeplitz matrix with unit diagonal (`tmat`);
* an `LDL*` factorization is computed in exact rational arithmetic (`ldl`, not trusted) and re-checked:
  `T = L D L*` entrywise and `D ≥ 0` (`ldlOK`), so `T` is positive semidefinite;
* a hint `x ≈ T⁻¹ v` (exact solve, rounded to `2^-64`; not trusted), `w = T x` and `q = x* w` exactly;
* `ρ ≥ Σ_j |v_j - w_j|` from ball enclosures of the vertex coordinates (`cos`/`sin` of `π m/512` and `cos(π/2^j)` by the
  ball arithmetic of `C64Core.Ival`);
* accepted iff `ρ ≤ B` and `q ≤ (B - ρ)²`.

Then `Re Σ_j conj(v_j) c_j ≤ (√q + ρ) max_T |Σ c_j z^j| ≤ B max_T |Σ c_j z^j|` (soundness in `Bohr59a/CertSound.lean`).
The leaves of every root cell `i < 8^D` with `i % nsh = s` are walked; each of their `3^D` vertex keys must be found
(hash lookup, key compared after lookup) with a passing certificate.
-/

namespace Bohr59aCore

open Ival

/-! ## Complex rationals -/

/-- `re + i im` -/
structure CQ where
  re : Rat
  im : Rat
deriving DecidableEq, Inhabited

namespace CQ

@[inline] def add (a b : CQ) : CQ := ⟨a.re + b.re, a.im + b.im⟩
@[inline] def sub (a b : CQ) : CQ := ⟨a.re - b.re, a.im - b.im⟩
@[inline] def mul (a b : CQ) : CQ := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
@[inline] def conj (a : CQ) : CQ := ⟨a.re, -a.im⟩
@[inline] def smul (r : Rat) (a : CQ) : CQ := ⟨r * a.re, r * a.im⟩
def zero : CQ := ⟨0, 0⟩
def one : CQ := ⟨1, 0⟩

end CQ

/-- `Σ_{p < n} f p` -/
def sumN (n : Nat) (f : Nat → CQ) : CQ := (List.range n).foldl (fun acc p => acc.add (f p)) CQ.zero

/-- the Hermitian Toeplitz matrix `T(y)`: `T_jj = 1`, `T_jl = y_{l-j}`, `T_lj = conj y_{l-j}` (`l > j`), where `y`
holds `y_1, …, y_k` at the indices `0, …, k - 1` -/
def tmat (y : Array CQ) (j l : Nat) : CQ :=
  if j = l then CQ.one else if j < l then y[l - j - 1]! else (y[j - l - 1]!).conj

/-! ## `LDL*` (computed, then re-checked) -/

/-- `LDL*` of the `n × n` Hermitian matrix `t` (row-major `L`); `none` if a pivot is not positive.  Not trusted. -/
def ldl (n : Nat) (t : Nat → Nat → CQ) : Option (Array CQ × Array Rat) := Id.run do
  let mut L : Array CQ := Array.replicate (n * n) CQ.zero
  let mut D : Array Rat := Array.replicate n 0
  for i in [0:n] do
    let mut di : Rat := (t i i).re
    for p in [0:i] do
      let lip := L[i * n + p]!
      di := di - (lip.re * lip.re + lip.im * lip.im) * D[p]!
    if di ≤ 0 then return none
    D := D.set! i di
    L := L.set! (i * n + i) CQ.one
    for j in [i+1:n] do
      let mut s := t j i
      for p in [0:i] do
        s := s.sub ((L[j * n + p]!.mul (L[i * n + p]!.conj)).smul D[p]!)
      L := L.set! (j * n + i) (s.smul (1 / di))
  return some (L, D)

/-- `D ≥ 0` and `t = L D L*` on and below the diagonal (both sides are Hermitian) -/
def ldlOK (n : Nat) (t : Nat → Nat → CQ) (L : Array CQ) (D : Array Rat) : Bool :=
  (List.range n).all (fun i => decide (0 ≤ D[i]!)) &&
  (List.range n).all fun j => (List.range (j + 1)).all fun l =>
    decide (sumN n (fun p => (L[j * n + p]!.mul (L[l * n + p]!.conj)).smul D[p]!) = t j l)

/-- `x = (L D L*)⁻¹ v` by substitution (exact).  Not trusted. -/
def solve (n : Nat) (L : Array CQ) (D : Array Rat) (v : Array CQ) : Array CQ := Id.run do
  let mut z : Array CQ := Array.replicate n CQ.zero
  for j in [0:n] do
    let mut s := v[j]!
    for p in [0:j] do
      s := s.sub (L[j * n + p]!.mul z[p]!)
    z := z.set! j s
  let mut x : Array CQ := Array.replicate n CQ.zero
  for jj in [0:n] do
    let j := n - 1 - jj
    let mut s := z[j]!.smul (1 / D[j]!)
    for p in [j+1:n] do
      s := s.sub ((L[p * n + j]!.conj).mul x[p]!)
    x := x.set! j s
  return x

/-- rounding to `2^-64` (any value would do) -/
def rnd (r : Rat) : Rat := mkRat (r * (2 ^ 64 : Rat)).floor (2 ^ 64)

/-! ## Ball enclosures of the vertex coordinates -/

/-- precision and Taylor/doubling parameters of the trigonometric balls -/
def P : Nat := 128
def nT : Nat := 24
def kT : Nat := 6

/-- `(cos π m/512, sin π m/512)` for `m = i - 512`, `i ≤ 1024` -/
def trigTab : Array (Option (Ball × Ball)) :=
  Array.ofFn (n := 1025) fun i => Ball.cosSinTurn P nT kT (Ball.ofRat P ((i.val : Int) - 512) 1024)

/-- `(cos π/2^j, sin π/2^j)` for `j < 16` -/
def cosTab : Array (Option (Ball × Ball)) :=
  Array.ofFn (n := 16) fun j => Ball.cosSinTurn P nT kT (Ball.ofRat P 1 (2 ^ (j.val + 1)))

/-- `|r|` -/
@[inline] def rabs (r : Rat) : Rat := if r < 0 then -r else r

/-- centre and radius of a ball as rationals -/
def ballC (b : Ball) : Rat := mkRat b.m (2 ^ P)
def ballR (b : Ball) : Rat := mkRat (b.r : Int) (2 ^ P)

/-- an upper bound of `|v - w|` for the vertex coordinate `v` with key component `c` -/
def coordErr (c : Comp) (w : CQ) : Option Rat :=
  if c.m < -512 || 512 < c.m then none else
  match trigTab[(c.m + 512).toNat]! with
  | none => none
  | some (C, S) =>
    let cc := ballC C
    let cr := ballR C
    let sc := ballC S
    let sr := ballR S
    if !c.tan then some (rabs (cc - w.re) + cr + (rabs (sc - w.im) + sr))
    else if 16 ≤ c.j then none else
      match cosTab[c.j]! with
      | none => none
      | some (H, _) =>
        let hc := ballC H
        let hr := ballR H
        if hc - hr ≤ 0 then none
        else some ((rabs (cc - w.re * hc) + cr + rabs w.re * hr + (rabs (sc - w.im * hc) + sr + rabs w.im * hr)) / (hc - hr))

/-- the centres of the vertex coordinates (only used for the hint `x`) -/
def coordCentre (c : Comp) : CQ :=
  match trigTab[(c.m + 512).toNat]! with
  | none => CQ.zero
  | some (C, S) =>
    let v : CQ := ⟨ballC C, ballC S⟩
    if !c.tan then v else
      match cosTab[c.j]! with
      | none => CQ.zero
      | some (H, _) => v.smul (1 / ballC H)

/-- `Σ_i coordErr cs_i w_{j+i}` -/
def errTail (w : Array CQ) : List Comp → Nat → Option Rat
  | [], _ => some 0
  | c :: cs, j =>
    match coordErr c w[j]!, errTail w cs (j + 1) with
    | some e, some r => some (e + r)
    | _, _ => none

/-- `Σ_j` of the error bounds: `|1 - w_0| + |1 - w_1| + Σ_d coordErr key_d w_{d+2}` -/
def errSum (key : List Comp) (w : Array CQ) : Option Rat :=
  (errTail w key 2).map fun r => rabs (1 - w[0]!.re) + rabs w[0]!.im + (rabs (1 - w[1]!.re) + rabs w[1]!.im) + r

/-! ## The vertex check -/

/-- the hint `x ≈ T⁻¹ v` (rounded) -/
def hint (n : Nat) (L : Array CQ) (D : Array Rat) (key : List Comp) : Array CQ :=
  let vc : Array CQ := #[CQ.one, CQ.one] ++ (key.map coordCentre).toArray
  (solve n L D vc).map fun z => ⟨rnd z.re, rnd z.im⟩

/-- the values `w = T x` and `q = Re x* w` -/
def wvec (n : Nat) (t : Nat → Nat → CQ) (x : Array CQ) : Array CQ :=
  Array.ofFn (n := n) fun j => sumN n fun l => (t j l).mul x[l]!

def qval (n : Nat) (x w : Array CQ) : Rat := (sumN n fun j => (x[j]!.conj).mul w[j]!).re

/-- the final comparison: `ρ ≤ B` and `q ≤ (B - ρ)²` -/
def finalOK (B q : Rat) (ρ : Option Rat) : Bool :=
  match ρ with
  | none => false
  | some r => decide (r ≤ B) && decide (q ≤ (B - r) * (B - r))

/-- the vertex certificate passes (for `S({0..k}) ≤ B`) -/
def vertexOK (k : Nat) (B : Rat) (key : List Comp) (yv : Array Rat) : Bool :=
  let n := k + 1
  if key.length + 2 ≠ n then false else
  let y : Array CQ := Array.ofFn (n := k) fun i => ⟨yv[2 * i.val]!, yv[2 * i.val + 1]!⟩
  let t := tmat y
  match ldl n t with
  | none => false
  | some (L, D) =>
    ldlOK n t L D &&
      (let x := hint n L D key
       let w := wvec n t x
       finalOK B (qval n x w) (errSum key w))

/-! ## Leaves, trees, root cells -/

/-- the three vertex options of a coordinate with centre `m/512` and half-width `2^-j` -/
def opts (m : Int) (j : Nat) : List Comp :=
  [⟨false, m - 2 ^ (9 - j), 0⟩, ⟨false, m + 2 ^ (9 - j), 0⟩, ⟨true, m, j⟩]

/-- `f` holds at every choice of one option per coordinate (prefixed by `acc`, reversed) -/
def allVerts (f : List Comp → Bool) : List (List Comp) → List Comp → Bool
  | [], acc => f acc.reverse
  | o :: os, acc => o.all fun c => allVerts f os (c :: acc)

/-- a leaf box: all half-width exponents in `[2, 9]` and all vertices found -/
def leafOK (f : List Comp → Bool) (ms : List Int) (js : List Nat) : Bool :=
  ms.length == js.length && js.all (fun j => 2 ≤ j && j ≤ 9) && allVerts f (List.zipWith opts ms js) []

/-- walk a split tree from the box with centres `ms/512` and half-widths `2^-js` -/
def walk (f : List Comp → Bool) : Tree → List Int → List Nat → Bool
  | .leaf, ms, js => leafOK f ms js
  | .split d lo hi, ms, js =>
    decide (d < ms.length) && decide (d < js.length) && decide (js[d]! ≤ 8) &&
      walk f lo (ms.set d (ms[d]! - 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1)) &&
      walk f hi (ms.set d (ms[d]! + 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1))

/-- the `D` digits of `i` in base `8`, most significant first -/
def digits8 : Nat → Nat → List Nat
  | 0, _ => []
  | D + 1, i => digits8 D (i / 8) ++ [i % 8]

/-- the centres of root cell `i` (`n0 = 8`: half-width `1/8 = 2^-3`, centres `-1 + (2 idx + 1)/8`) -/
def rootMs (D i : Nat) : List Int := (digits8 D i).map fun (a : Nat) => -512 + (2 * (a : Int) + 1) * 64

/-- the shard check -/
def checkShard (sh : Shard) : Bool :=
  if sh.n0 ≠ 8 || sh.k < 2 || sh.nsh = 0 || sh.bden = 0 then false else
  let D := sh.k - 1
  let B : Rat := mkRat sh.bnum sh.bden
  let ok : Array Bool := sh.verts.map fun vc => vertexOK sh.k B vc.key.toList vc.y
  let idx : Std.HashMap (List Comp) Nat :=
    sh.verts.foldl (init := (∅, 0)) (fun (acc : Std.HashMap (List Comp) Nat × Nat) vc =>
      (acc.1.insert vc.key.toList acc.2, acc.2 + 1)) |>.1
  let lookup (key : List Comp) : Bool :=
    match idx.get? key with
    | some i => decide (i < sh.verts.size) && decide (sh.verts[i]!.key.toList = key) && ok[i]!
    | none => false
  let cellMap : Std.HashMap Nat Tree := sh.cells.foldl (init := ∅) fun acc c => acc.insert c.1 c.2
  (List.range (8 ^ D)).all fun i =>
    i % sh.nsh != sh.s ||
      match cellMap.get? i with
      | some t => walk lookup t (rootMs D i) (List.replicate D 3)
      | none => false

end Bohr59aCore
