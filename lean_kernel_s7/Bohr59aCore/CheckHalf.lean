import Bohr59aCore.Check

/-!
# The shard check on the half phase domain (the k = 7 certificate)

The root cells tile `[0, 1] × [-1, 1]^D` (phases in units of `π`, `D + 1 = k - 1` coordinates): `n0 = 4`, half-width
`1/4`. Root cell `i < 2 · 4^D` has the base-4 digits `a, b₁, …, b_D` (most significant first, `a < 2`), centre
`1/4 + a/2` in the first coordinate and `-3/4 + b/2` in the others, the order of the certificate's
`itertools.product(range(2), range(4), …)`. Conjugation covers the other half (`Bohr59a/CertHalf.lean`).
-/

namespace Bohr59aCore

/-- the base-4 digits of `i` (`D` of them, most significant first) -/
def digits4 : Nat → Nat → List Nat
  | 0, _ => []
  | D + 1, i => digits4 D (i / 4) ++ [i % 4]

/-- the centres (units of `π/512`) of root cell `i` of the half domain with `D + 1` coordinates -/
def rootMsH (D i : Nat) : List Int :=
  match digits4 (D + 1) i with
  | [] => []
  | a :: rest => (128 + 256 * (a : Int)) :: rest.map fun (b : Nat) => -384 + 256 * (b : Int)

/-- the shard check on the half domain -/
def checkShardH (sh : Shard) : Bool :=
  if sh.n0 ≠ 4 || sh.k < 2 || sh.nsh = 0 || sh.bden = 0 then false else
  let D := sh.k - 2
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
  (List.range (2 * 4 ^ D)).all fun i =>
    i % sh.nsh != sh.s ||
      match cellMap.get? i with
      | some t => walk lookup t (rootMsH D i) (List.replicate (D + 1) 2)
      | none => false

end Bohr59aCore
