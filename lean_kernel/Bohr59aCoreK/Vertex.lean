import C64Core.Ival
import Bohr59aCore.Format

/-!
# Kernel-friendly vertex check (integers only, structural recursion, no `Rat`, no arrays)

All quantities are integers at explicit binary scales.  `T = T(y)` at scale `2^E` (`E = 128`: the certificate values `y` are
dyadic with denominators dividing `2^128`, given as the integers `Y = 2^128 y`); hints `W ≈ L⁻¹` (unit lower triangular) and
`x ≈ T⁻¹ v` at scale `2^P` are computed in fixed point at scale `2^Q` (not trusted); the checks are exact:
* `M = W T W*` (scale `2^{2P+E}`) is strictly diagonally dominant with positive diagonal, so `T ⪰ 0` (`W` unit lower
  triangular);
* `w = T x` (scale `2^{E+P}`), `q = Re x* w` (scale `2^{E+2P}`), `ρ ≥ Σ_j |v_j - w_j|` from ball enclosures of the vertex
  coordinates (scale `2^{E+P}`, rounded up);
* `ρ ≤ B` and `q ≤ (B - ρ)²`, cleared of denominators.
-/

namespace Bohr59aK

/-- Gaussian integers -/
structure GI where
  re : Int
  im : Int
deriving Inhabited, DecidableEq

namespace GI
@[inline] def add (a b : GI) : GI := ⟨a.re + b.re, a.im + b.im⟩
@[inline] def sub (a b : GI) : GI := ⟨a.re - b.re, a.im - b.im⟩
@[inline] def neg (a : GI) : GI := ⟨-a.re, -a.im⟩
@[inline] def mul (a b : GI) : GI := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
@[inline] def conj (a : GI) : GI := ⟨a.re, -a.im⟩
def zero : GI := ⟨0, 0⟩
/-- `|re| + |im|` -/
def abs1 (a : GI) : Int := a.re.natAbs + a.im.natAbs
end GI

/-- `l[i]` with default -/
def nth {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: as, i + 1 => nth d as i

/-- `Σ_{p < n} f p` -/
def sumGI (f : Nat → GI) : Nat → GI
  | 0 => GI.zero
  | n + 1 => (sumGI f n).add (f n)

/-- `Σ_{p < n} f p` -/
def sumInt (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumInt f n + f n

/-- `T(y)` at scale `2^E`: `T_jj = 2^E`, `T_jl = Y_{l-j}`, `T_lj = conj Y_{l-j}` (`l > j`); `Y` lists `Y_1, …, Y_k` -/
def tK (E : Nat) (Y : List GI) (j l : Nat) : GI :=
  if j = l then ⟨2 ^ E, 0⟩ else if j < l then nth GI.zero Y (l - j - 1) else (nth GI.zero Y (j - l - 1)).conj

/-! ## Fixed-point hints (not trusted) -/

/-- `a / 2^s`, rounded -/
def rsh (a : Int) (s : Nat) : Int := (a + (2 ^ s / 2 : Nat)) / (2 ^ s : Nat)

/-- `a / b`, rounded (`0` if `b ≤ 0`) -/
def rdiv (a b : Int) : Int := if b ≤ 0 then 0 else (2 * a + b) / (2 * b)

/-- fixed-point product at scale `2^Q` -/
def fmul (Q : Nat) (a b : GI) : GI := ⟨rsh (a.re * b.re - a.im * b.im) Q, rsh (a.re * b.im + a.im * b.re) Q⟩

/-- fixed-point real scaling at scale `2^Q` -/
def fscale (Q : Nat) (r : Int) (a : GI) : GI := ⟨rsh (r * a.re) Q, rsh (r * a.im) Q⟩

/-- fixed-point division by a positive real at scale `2^Q` -/
def fdiv (Q : Nat) (a : GI) (d : Int) : GI := ⟨rdiv (a.re * 2 ^ Q) d, rdiv (a.im * 2 ^ Q) d⟩

/-- row `i` of `L` (entries `p < i`): `L_ip = (t_ip - Σ_{r<p} L_ir conj(L_pr) D_r) / D_p` -/
def lRow (Q : Nat) (t : Nat → Nat → GI) (Ls : List (List GI)) (Ds : List Int) (i : Nat) : Nat → List GI
  | 0 => []
  | p + 1 =>
    let acc := lRow Q t Ls Ds i p
    let s := (t i p).sub (sumGI (fun r => fscale Q (nth 0 Ds r) (fmul Q (nth GI.zero acc r)
      (nth GI.zero (nth [] Ls p) r).conj)) p)
    acc ++ [fdiv Q s (nth 0 Ds p)]

/-- the pivot `D_i = t_ii - Σ_{p<i} |L_ip|² D_p` -/
def dPiv (Q : Nat) (t : Nat → Nat → GI) (Ds : List Int) (row : List GI) (i : Nat) : Int :=
  (t i i).re - sumInt (fun p => let l := nth GI.zero row p
    rsh (rsh (l.re * l.re + l.im * l.im) Q * nth 0 Ds p) Q) i

/-- fixed-point `LDL*` (rows of `L`, pivots) -/
def ldlK (Q : Nat) (t : Nat → Nat → GI) : Nat → List (List GI) × List Int
  | 0 => ([], [])
  | i + 1 =>
    let LD := ldlK Q t i
    let row := lRow Q t LD.1 LD.2 i i
    (LD.1 ++ [row], LD.2 ++ [dPiv Q t LD.2 row i])

/-- row `i` of `W = L⁻¹` (entries `j ≤ i`, `W_ii = 1`): `W_ij = -Σ_{j ≤ p < i} L_ip W_pj` -/
def wRow (Q : Nat) (Ls Ws : List (List GI)) (i : Nat) : List GI :=
  (List.range i).map (fun j => (sumGI (fun r => fmul Q (nth GI.zero (nth [] Ls i) (j + r))
    (nth GI.zero (nth [] Ws (j + r)) j)) (i - j)).neg) ++ [⟨2 ^ Q, 0⟩]

def wAll (Q : Nat) (Ls : List (List GI)) : Nat → List (List GI)
  | 0 => []
  | i + 1 => let Ws := wAll Q Ls i
    Ws ++ [wRow Q Ls Ws i]

/-- `x = W* D⁻¹ W v` in fixed point -/
def xHint (Q n : Nat) (Ws : List (List GI)) (Ds : List Int) (v : List GI) : List GI :=
  let u : List GI := (List.range n).map fun i =>
    fdiv Q (sumGI (fun j => fmul Q (nth GI.zero (nth [] Ws i) j) (nth GI.zero v j)) (i + 1)) (nth 0 Ds i)
  (List.range n).map fun j =>
    sumGI (fun r => fmul Q (nth GI.zero (nth [] Ws (j + r)) j).conj (nth GI.zero u (j + r))) (n - j)

/-! ## Exact checks -/

/-- the rounded hint rows `W` at scale `2^P` -/
def roundRows (s : Nat) (Ws : List (List GI)) : List (List GI) := Ws.map fun row => row.map fun a => ⟨rsh a.re s, rsh a.im s⟩

/-- `M_ij = Σ_{b ≤ j} V_ib conj(W_jb)` with `V_ib = Σ_{a ≤ i} W_ia T_ab` (lower triangle `j ≤ i`) -/
def mEntry (E : Nat) (Y : List GI) (Wr : List (List GI)) (n i j : Nat) : GI :=
  sumGI (fun b => (sumGI (fun a => (nth GI.zero (nth [] Wr i) a).mul (tK E Y a b)) (i + 1)).mul
    (nth GI.zero (nth [] Wr j) b).conj) (j + 1)

/-- strict diagonal dominance of `M` from its lower triangle, and `W_ii = 2^96` (so `W / 2^96` is unit lower triangular; only
the entries `j ≤ i` of row `i` are ever used) -/
def domOK (E : Nat) (Y : List GI) (Wr : List (List GI)) (n : Nat) : Bool :=
  let low : List (List GI) := (List.range n).map fun i => (List.range (i + 1)).map fun j => mEntry E Y Wr n i j
  (List.range n).all fun i =>
    let off := sumInt (fun j => if j < i then (nth GI.zero (nth [] low i) j).abs1
      else if i < j then (nth GI.zero (nth [] low j) i).abs1 else 0) n
    decide (off < (nth GI.zero (nth [] low i) i).re) && decide ((nth GI.zero (nth [] low i) i).im = 0) &&
      decide (nth GI.zero (nth [] Wr i) i = ⟨2 ^ 96, 0⟩)

/-- `w = T x` -/
def wVec (E : Nat) (Y : List GI) (x : List GI) (n : Nat) : List GI :=
  (List.range n).map fun j => sumGI (fun l => (tK E Y j l).mul (nth GI.zero x l)) n

/-- `q = Re x* w` -/
def qVal (x w : List GI) (n : Nat) : Int := sumInt (fun j => ((nth GI.zero x j).conj.mul (nth GI.zero w j)).re) n


/-! ## The trigonometric table -/

/-- the balls `(cos, sin)` of an angle at precision `128`: centres `cm`, `sm` and radii `cr`, `sr` (units `2^-128`) -/
structure TE where
  cm : Int
  cr : Nat
  sm : Int
  sr : Nat
deriving Inhabited, DecidableEq

/-- a binary tree indexed by the bits of the index, least significant first -/
inductive TT where
  | none
  | leaf (e : TE)
  | node (l r : TT)
deriving Inhabited

/-- the entry at index `i` of a tree of depth `d` -/
def ttGet : TT → Nat → Nat → Option TE
  | .leaf e, 0, _ => some e
  | .node l r, d + 1, i => if i % 2 = 0 then ttGet l d (i / 2) else ttGet r d (i / 2)
  | _, _, _ => Option.none

/-- the ball pair of `Ival.Ball.cosSinTurn` as a table entry -/
def teOf (cs : Ival.Ball × Ival.Ball) : TE := ⟨cs.1.m, cs.1.r, cs.2.m, cs.2.r⟩

/-- the specification of the table: entry `i ≤ 1024` holds `(cos, sin)(π (i - 512)/512)` -/
def ttSpec (i : Nat) : Option TE :=
  (Ival.Ball.cosSinTurn 128 24 6 (Ival.Ball.ofRat 128 ((i : Int) - 512) 1024)).map teOf

/-! ## Errors and the vertex check -/

/-- `⌈a / b⌉` for `b > 0` -/
def cdivI (a : Int) (b : Int) : Int := if b ≤ 0 then 0 else -((-a) / b)

/-- an upper bound of `|v - w|` at scale `2^224` (`w` at scale `2^224`, `E + P = 224`) for the vertex coordinate of `c` -/
def coordErrK (tt : TT) (c : Bohr59aCore.Comp) (w : GI) : Option Int :=
  if c.m < -512 || 512 < c.m then Option.none else
  match ttGet tt 11 (c.m + 512).toNat with
  | Option.none => Option.none
  | some e =>
    if !c.tan then
      some ((e.cm * 2 ^ 96 - w.re).natAbs + e.cr * 2 ^ 96 + ((e.sm * 2 ^ 96 - w.im).natAbs + e.sr * 2 ^ 96))
    else if c.j < 2 || 9 < c.j then Option.none else
      match ttGet tt 11 (512 + 2 ^ (9 - c.j)) with
      | Option.none => Option.none
      | some h =>
        let den : Int := h.cm - h.cr
        if den ≤ 0 then Option.none
        else some (cdivI ((e.cm * 2 ^ 224 - w.re * h.cm).natAbs + e.cr * 2 ^ 224 + w.re.natAbs * h.cr +
          ((e.sm * 2 ^ 224 - w.im * h.cm).natAbs + e.sr * 2 ^ 224 + w.im.natAbs * h.cr)) den)

/-- `Σ_i coordErrK cs_i w_{j+i}` -/
def errTailK (tt : TT) (w : List GI) : List Bohr59aCore.Comp → Nat → Option Int
  | [], _ => some 0
  | c :: cs, j =>
    match coordErrK tt c (nth GI.zero w j), errTailK tt w cs (j + 1) with
    | some e, some r => some (e + r)
    | _, _ => Option.none

/-- `ρ` at scale `2^224`: `|1 - w_0| + |1 - w_1| + Σ_d coordErrK key_d w_{d+2}` -/
def errSumK (tt : TT) (key : List Bohr59aCore.Comp) (w : List GI) : Option Int :=
  (errTailK tt w key 2).map fun r =>
    ((2 ^ 224 : Int) - (nth GI.zero w 0).re).natAbs + (nth GI.zero w 0).im.natAbs +
      (((2 ^ 224 : Int) - (nth GI.zero w 1).re).natAbs + (nth GI.zero w 1).im.natAbs) + r

/-- the hint vertex at scale `2^Q` (`Q = 160`) from the table centres -/
def vHint (tt : TT) (key : List Bohr59aCore.Comp) : List GI :=
  [⟨2 ^ 160, 0⟩, ⟨2 ^ 160, 0⟩] ++ key.map fun c =>
    match ttGet tt 11 (c.m + 512).toNat with
    | Option.none => GI.zero
    | some e =>
      let z : GI := ⟨e.cm * 2 ^ 32, e.sm * 2 ^ 32⟩
      if !c.tan then z else
        match ttGet tt 11 (512 + 2 ^ (9 - c.j)) with
        | Option.none => GI.zero
        | some h => fdiv 128 z h.cm

/-- the final comparison: `ρ ≤ B` and `q ≤ (B - ρ)²` with `B = bnum/bden`, `ρ = R/2^224`, `q = q₀/2^320` -/
def finalK (bnum bden : Nat) (q : Int) (ρ : Option Int) : Bool :=
  match ρ with
  | Option.none => false
  | some R => decide (R * bden ≤ bnum * 2 ^ 224) && decide (q * bden ^ 2 * 2 ^ 128 ≤ (bnum * 2 ^ 224 - R * bden) ^ 2)

/-- `T(y)` at scale `2^160` -/
def tQ (Y : List GI) (j l : Nat) : GI := let a := tK 128 Y j l
  ⟨a.re * 2 ^ 32, a.im * 2 ^ 32⟩

/-- **The kernel vertex check** for `S({0..k}) ≤ bnum/bden` (`E = 128`, `P = 96`, `Q = 160`). -/
def vertexOKK (tt : TT) (k bnum bden : Nat) (key : List Bohr59aCore.Comp) (Y : List GI) : Bool :=
  let n := k + 1
  if key.length + 2 ≠ n then false else
  let LD := ldlK 160 (tQ Y) n
  let Ws := wAll 160 LD.1 n
  let Wr := roundRows 64 Ws
  domOK 128 Y Wr n &&
    (let x := (xHint 160 n Ws LD.2 (vHint tt key)).map fun a => (⟨rsh a.re 64, rsh a.im 64⟩ : GI)
     let w := wVec 128 Y x n
     finalK bnum bden (qVal x w n) (errSumK tt key w))

end Bohr59aK
