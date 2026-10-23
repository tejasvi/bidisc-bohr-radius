import Bohr59aCoreK.VertexH

/-!
# Packed vertex hints

All integers of one vertex certificate (the `k` entries of `y`, the rows of `W`, the `k + 1` entries of `x`, as
Gaussian integers) in one natural number, decoded by the kernel: the low 10 bits give the width `w`, then come
`2 k + (k + 1) (k + 2) + 2 (k + 1)` fields of `w` bits each (zigzag signs), least significant first. Untrusted data:
`exists_of_vertexOKKp` only uses that SOME lists make `vertexOKKh` true.
-/

namespace Bohr59aK

open Bohr59aCore

/-- `c` integers of `w` bits each (zigzag: `2 v` for `v ≥ 0`, `2 (-v) - 1` for `v < 0`), least significant first -/
def unpackZ (w : Nat) : Nat → Nat → List Int
  | 0, _ => []
  | c + 1, n =>
    (if n % 2 = 0 then Int.ofNat (n % 2 ^ w / 2) else Int.negSucc (n % 2 ^ w / 2)) :: unpackZ w c (n / 2 ^ w)

/-- consecutive pairs as Gaussian integers -/
def pairGI : List Int → List GI
  | a :: b :: r => ⟨a, b⟩ :: pairGI r
  | _ => []

/-- `r` rows of lengths `i + 1, i + 2, …` -/
def rowsGI : Nat → Nat → List GI → List (List GI)
  | 0, _, _ => []
  | r + 1, i, l => l.take (i + 1) :: rowsGI r (i + 1) (l.drop (i + 1))

/-- the decoded Gaussian integers of a packed certificate -/
def unpackGI (k n : Nat) : List GI :=
  pairGI (unpackZ (n % 1024) (2 * k + (k + 1) * (k + 2) + 2 * (k + 1)) (n / 1024))

/-- the kernel vertex check with packed hints -/
def vertexOKKp (tt : TT) (k bnum bden : Nat) (key : List Comp) (n : Nat) : Bool :=
  vertexOKKh tt k bnum bden key ((unpackGI k n).take k) (rowsGI (k + 1) 0 ((unpackGI k n).drop k))
    (((unpackGI k n).drop (k + (k + 1) * (k + 2) / 2)).take (k + 1))

theorem exists_of_vertexOKKp {tt : TT} {k bnum bden : Nat} {key : List Comp} {n : Nat}
    (h : vertexOKKp tt k bnum bden key n = true) : ∃ Y Wr x, vertexOKKh tt k bnum bden key Y Wr x = true :=
  ⟨_, _, _, h⟩

end Bohr59aK
