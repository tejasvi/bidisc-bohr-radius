/-
The fast final test `finalKF` (`Bohr59aCoreK/FastArith2.lean`) computes `finalK`, so `vertexOKKpF2 = vertexOKKp` and the
fast vertex check inherits the soundness of the original one (as `Bohr59a/CertFast.lean` for `vertexOKKpF`).
-/
import Bohr59a.CertFast
import Bohr59aCoreK.FastArith2

namespace Bohr59aK

open Bohr59aCore

theorem ile_eq (a b : Int) : ile a b = decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr
  cases a <;> cases b <;> simp only [ile, Nat.ble_eq, decide_eq_true_eq, Int.negSucc_eq, Int.ofNat_eq_natCast,
    Bool.false_eq_true, false_iff, true_iff] <;> omega

theorem finalKF_eq (bnum bden : Nat) (q : Int) (ρ : Option Int) : finalKF bnum bden q ρ = finalK bnum bden q ρ := by
  cases ρ with
  | none => rfl
  | some R =>
    simp only [finalKF, finalK, imul_eq, isub_eq, ile_eq, Nat.mul_eq, Nat.pow_eq, Int.ofNat_eq_natCast]
    push_cast
    ring_nf

theorem vertexOKKhF2_eq (tt : TT) (k bnum bden : Nat) (key : List Comp) (Y : List GI) (Wr : List (List GI))
    (x : List GI) : vertexOKKhF2 tt k bnum bden key Y Wr x = vertexOKKh tt k bnum bden key Y Wr x := by
  rw [← vertexOKKhF_eq]
  simp only [vertexOKKhF2, vertexOKKhF, finalKF_eq]

theorem vertexOKKpF2_eq (tt : TT) (k bnum bden : Nat) (key : List Comp) (n : Nat) :
    vertexOKKpF2 tt k bnum bden key n = vertexOKKp tt k bnum bden key n := by
  simp only [vertexOKKpF2, vertexOKKp, vertexOKKhF2_eq]

theorem exists_of_vertexOKKpF2 {tt : TT} {k bnum bden : Nat} {key : List Comp} {n : Nat}
    (h : vertexOKKpF2 tt k bnum bden key n = true) : ∃ Y Wr x, vertexOKKh tt k bnum bden key Y Wr x = true :=
  exists_of_vertexOKKp (by rwa [vertexOKKpF2_eq] at h)

end Bohr59aK
