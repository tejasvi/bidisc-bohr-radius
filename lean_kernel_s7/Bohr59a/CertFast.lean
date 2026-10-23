/-
The fast kernel primitives (`Bohr59aCoreK/FastArith.lean`) compute the standard operations, so the fast vertex check
`vertexOKKpF` equals `vertexOKKp` and inherits its soundness. The primitive lemmas follow the worm K proofs
(`WormKProof/Prims.lean`).
-/
import Mathlib.Tactic
import Bohr59aCoreK.FastArith

namespace Bohr59aK

open Bohr59aCore

/-! ### The primitives -/

theorem isnn_eq (m n : Nat) : isnn m n = Int.subNatNat m n := by
  show Nat.rec (motive := fun _ => Int) (Int.ofNat (m - n)) (fun k _ => Int.negSucc k) (n - m) = Int.subNatNat m n
  unfold Int.subNatNat
  cases h : n - m with
  | zero => rfl
  | succ k => rfl

theorem iadd_eq (a b : Int) : iadd a b = a + b := by
  cases a <;> cases b <;> simp only [iadd, isnn_eq] <;> rfl

theorem nneg_eq (n : Nat) : nneg n = -(n : Int) := by
  cases n <;> rfl

theorem ineg_eq (a : Int) : ineg a = -a := by
  cases a with
  | ofNat n => simp only [ineg, nneg_eq]; rfl
  | negSucc n => rfl

theorem isub_eq (a b : Int) : isub a b = a - b := by
  simp only [isub, iadd_eq, ineg_eq, Int.sub_eq_add_neg]

theorem imul_eq (a b : Int) : imul a b = a * b := by
  cases a <;> cases b <;> simp only [imul, nneg_eq] <;> rfl

theorem iabs_eq (a : Int) : iabs a = a.natAbs := by
  cases a <;> rfl

theorem ilt_eq (a b : Int) : ilt a b = decide (a < b) := by
  apply Bool.eq_iff_iff.mpr
  cases a <;> cases b <;> simp only [ilt, Nat.blt_eq, decide_eq_true_eq, Int.negSucc_eq, Int.ofNat_eq_natCast,
    Bool.false_eq_true, false_iff, true_iff] <;> omega

theorem ieq_eq (a b : Int) : ieq a b = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  cases a <;> cases b <;> simp only [ieq, Nat.beq_eq, decide_eq_true_eq, Int.negSucc_eq, Int.ofNat_eq_natCast,
    Bool.false_eq_true, false_iff] <;> omega

/-! ### Gaussian integers -/

theorem GI.addF_eq (a b : GI) : a.addF b = a.add b := by
  simp only [GI.addF, GI.add, iadd_eq]

theorem GI.mulF_eq (a b : GI) : a.mulF b = a.mul b := by
  simp only [GI.mulF, GI.mul, iadd_eq, isub_eq, imul_eq]

theorem GI.conjF_eq (a : GI) : a.conjF = a.conj := by
  simp only [GI.conjF, GI.conj, ineg_eq]

theorem GI.abs1F_eq (a : GI) : a.abs1F = a.abs1 := by
  unfold GI.abs1F GI.abs1
  rw [iabs_eq, iabs_eq, Nat.add_eq, Int.ofNat_eq_natCast, Nat.cast_add]

theorem sumGIF_eq (f : Nat → GI) : ∀ n, sumGIF f n = sumGI f n
  | 0 => rfl
  | n + 1 => by simp only [sumGIF, sumGI, sumGIF_eq f n, GI.addF_eq]

theorem sumIntF_eq (f : Nat → Int) : ∀ n, sumIntF f n = sumInt f n
  | 0 => rfl
  | n + 1 => by simp only [sumIntF, sumInt, sumIntF_eq f n, iadd_eq]

theorem tKF_eq (E : Nat) (Y : List GI) (j l : Nat) : tKF E Y j l = tK E Y j l := by
  simp only [tKF, tK, GI.conjF_eq]

theorem mEntryF_eq (E : Nat) (Y : List GI) (Wr : List (List GI)) (n i j : Nat) :
    mEntryF E Y Wr n i j = mEntry E Y Wr n i j := by
  simp only [mEntryF, mEntry, sumGIF_eq, GI.mulF_eq, GI.conjF_eq, tKF_eq]

lemma decide_GI_eq (g : GI) (a b : Int) : decide (g = ⟨a, b⟩) = (decide (g.re = a) && decide (g.im = b)) := by
  cases g
  simp only [GI.mk.injEq, Bool.decide_and]

theorem domOKF_eq (E : Nat) (Y : List GI) (Wr : List (List GI)) (n : Nat) : domOKF E Y Wr n = domOK E Y Wr n := by
  simp only [domOKF, domOK, mEntryF_eq, sumIntF_eq, GI.abs1F_eq, ilt_eq, ieq_eq, decide_GI_eq]
  congr 1

theorem wVecF_eq (E : Nat) (Y : List GI) (x : List GI) (n : Nat) : wVecF E Y x n = wVec E Y x n := by
  simp only [wVecF, wVec, sumGIF_eq, GI.mulF_eq, tKF_eq]

theorem qValF_eq (x w : List GI) (n : Nat) : qValF x w n = qVal x w n := by
  simp only [qValF, qVal, sumIntF_eq, GI.mulF_eq, GI.conjF_eq]

theorem vertexOKKhF_eq (tt : TT) (k bnum bden : Nat) (key : List Comp) (Y : List GI) (Wr : List (List GI))
    (x : List GI) : vertexOKKhF tt k bnum bden key Y Wr x = vertexOKKh tt k bnum bden key Y Wr x := by
  simp only [vertexOKKhF, vertexOKKh, domOKF_eq, wVecF_eq, qValF_eq]

theorem vertexOKKpF_eq (tt : TT) (k bnum bden : Nat) (key : List Comp) (n : Nat) :
    vertexOKKpF tt k bnum bden key n = vertexOKKp tt k bnum bden key n := by
  simp only [vertexOKKpF, vertexOKKp, vertexOKKhF_eq]

theorem exists_of_vertexOKKpF {tt : TT} {k bnum bden : Nat} {key : List Comp} {n : Nat}
    (h : vertexOKKpF tt k bnum bden key n = true) : ∃ Y Wr x, vertexOKKh tt k bnum bden key Y Wr x = true :=
  exists_of_vertexOKKp (by rwa [vertexOKKpF_eq] at h)

end Bohr59aK
