/-
The vertex check with the straight-line parts (`Bohr59aCoreK/FastArith3.lean`) agrees with the original one:
`domOKFast = domOKF`, `wVecFast = wVecF`, `qValFast = qValF` (by `rfl` on the packed shapes) and
`vertexOKKhF2 = vertexOKKh` (`Bohr59a/CertFast2.lean`).
-/
import Bohr59a.CertFast2
import Bohr59aCoreK.FastArith3

namespace Bohr59aK

open Bohr59aCore

theorem vertexOKKhF3_eq (tt : TT) (k bnum bden : Nat) (key : List Comp) (Y : List GI) (Wr : List (List GI))
    (x : List GI) : vertexOKKhF3 tt k bnum bden key Y Wr x = vertexOKKh tt k bnum bden key Y Wr x := by
  rw [← vertexOKKhF2_eq]
  simp only [vertexOKKhF3, vertexOKKhF2, domOKFast_eq, wVecFast_eq, qValFast_eq]

theorem vertexOKKpF3_eq (tt : TT) (k bnum bden : Nat) (key : List Comp) (n : Nat) :
    vertexOKKpF3 tt k bnum bden key n = vertexOKKp tt k bnum bden key n := by
  simp only [vertexOKKpF3, vertexOKKp, vertexOKKhF3_eq]

theorem exists_of_vertexOKKpF3 {tt : TT} {k bnum bden : Nat} {key : List Comp} {n : Nat}
    (h : vertexOKKpF3 tt k bnum bden key n = true) : ∃ Y Wr x, vertexOKKh tt k bnum bden key Y Wr x = true :=
  exists_of_vertexOKKp (by rwa [vertexOKKpF3_eq] at h)

end Bohr59aK
