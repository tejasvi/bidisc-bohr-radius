/-
The Toeplitz bound: for a positive definite Hermitian Toeplitz matrix `T` of size `k + 1` and every polynomial
`q(z) = Σ_{j ≤ k} c_j z^j` with `|q| ≤ M` on the unit circle, `c* T c ≤ T₀₀ M²`.
Proof (Patel's Gram argument): in `ℂ^{k+1}` with the inner product `⟪x, y⟫ = x* T y` the shift `δ_j ↦ δ_{j+1}` (`j < k`) is an
isometry between spans (Toeplitz), it extends to a unitary `U`, `q(U) δ₀ = c`, and `‖q(U)‖ ≤ M` by the continuous functional
calculus (the spectrum of a unitary lies on the circle).
-/
import Mathlib

open Matrix Polynomial
open scoped ComplexOrder

namespace Bohr59a

/-- a positive definite matrix of size `k + 1` -/
structure PDMat (k : ℕ) where
  T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ
  pd : T.PosDef

/-- `ℂ^{k+1}` with the inner product `⟪x, y⟫ = x* T y` -/
def TSpace {k : ℕ} (_P : PDMat k) : Type := Fin (k + 1) → ℂ

namespace TSpace

variable {k : ℕ} (P : PDMat k)

instance : AddCommGroup (TSpace P) := inferInstanceAs (AddCommGroup (Fin (k + 1) → ℂ))
instance : Module ℂ (TSpace P) := inferInstanceAs (Module ℂ (Fin (k + 1) → ℂ))
instance : FiniteDimensional ℂ (TSpace P) := inferInstanceAs (FiniteDimensional ℂ (Fin (k + 1) → ℂ))

/-- the coordinates -/
def toFun : TSpace P ≃ₗ[ℂ] (Fin (k + 1) → ℂ) := LinearEquiv.refl ℂ _

lemma hermitian_entry (i j : Fin (k + 1)) : star (P.T i j) = P.T j i := P.pd.isHermitian.apply j i

noncomputable instance core : InnerProductSpace.Core ℂ (TSpace P) where
  inner x y := star (toFun P x) ⬝ᵥ (P.T *ᵥ toFun P y)
  conj_inner_symm x y := by
    change star (star (toFun P y) ⬝ᵥ (P.T *ᵥ toFun P x)) = star (toFun P x) ⬝ᵥ (P.T *ᵥ toFun P y)
    rw [← star_dotProduct, star_mulVec, P.pd.isHermitian.eq, dotProduct_mulVec]
  re_inner_nonneg x := by
    have h := P.pd.posSemidef.dotProduct_mulVec_nonneg (toFun P x)
    rw [RCLike.re_to_complex]
    exact (Complex.nonneg_iff.1 h).1
  add_left x y z := by simp [add_dotProduct]
  smul_left x y r := by simp [smul_dotProduct]
  definite x hx := by
    by_contra hne
    have hne' : toFun P x ≠ 0 := hne
    have h := P.pd.dotProduct_mulVec_pos hne'
    change star (toFun P x) ⬝ᵥ (P.T *ᵥ toFun P x) = 0 at hx
    rw [hx] at h
    exact lt_irrefl _ h

noncomputable instance : NormedAddCommGroup (TSpace P) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
noncomputable instance : InnerProductSpace ℂ (TSpace P) := InnerProductSpace.ofCore (𝕜 := ℂ) _

lemma inner_def (x y : TSpace P) : inner ℂ x y = star (toFun P x) ⬝ᵥ (P.T *ᵥ toFun P y) := rfl

lemma norm_sq_def (x : TSpace P) : ‖x‖ ^ 2 = (star (toFun P x) ⬝ᵥ (P.T *ᵥ toFun P x)).re := by
  rw [@norm_sq_eq_re_inner ℂ, inner_def]; rfl

/-- the shift on coordinates -/
def shiftFun : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun x := Fin.cons 0 fun j : Fin k => x j.castSucc
  map_add' x y := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' r x := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- the shift `x ↦ (0, x₀, ..., x_{k-1})` -/
def shift : TSpace P →ₗ[ℂ] TSpace P :=
  (toFun P).symm.toLinearMap ∘ₗ shiftFun ∘ₗ (toFun P).toLinearMap

lemma toFun_shift (x : TSpace P) : toFun P (shift P x) = Fin.cons 0 fun j : Fin k => toFun P x j.castSucc := rfl

/-- the subspace `x_k = 0` -/
def sub : Submodule ℂ (TSpace P) := LinearMap.ker ((LinearMap.proj (Fin.last k)).comp (toFun P).toLinearMap)

lemma mem_sub {x : TSpace P} : x ∈ sub P ↔ toFun P x (Fin.last k) = 0 := Iff.rfl

end TSpace

/-- Toeplitz along the diagonal: `T (j+1) (l+1) = T j l` for `j, l < k` -/
def IsToeplitz {k : ℕ} (T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  ∀ j l : Fin k, T j.succ l.succ = T j.castSucc l.castSucc

namespace TSpace

variable {k : ℕ} (P : PDMat k)

lemma inner_eq_sum (x y : TSpace P) :
    inner ℂ x y = ∑ i, ∑ l, star (toFun P x i) * (P.T i l * toFun P y l) := by
  rw [inner_def]; simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]

lemma inner_shift (x y : TSpace P) : inner ℂ (shift P x) (shift P y) =
    ∑ j : Fin k, ∑ m : Fin k, star (toFun P x j.castSucc) * (P.T j.succ m.succ * toFun P y m.castSucc) := by
  rw [inner_eq_sum]
  simp only [toFun_shift, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, star_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, zero_add]

lemma inner_sub (x y : TSpace P) (hx : toFun P x (Fin.last k) = 0) (hy : toFun P y (Fin.last k) = 0) :
    inner ℂ x y =
    ∑ j : Fin k, ∑ m : Fin k, star (toFun P x j.castSucc) * (P.T j.castSucc m.castSucc * toFun P y m.castSucc) := by
  rw [inner_eq_sum]
  simp only [Fin.sum_univ_castSucc, hx, hy, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

lemma shift_isometry (hTo : IsToeplitz P.T) (x y : sub P) :
    inner ℂ (shift P x) (shift P y) = inner ℂ (x : TSpace P) (y : TSpace P) := by
  rw [inner_shift, inner_sub P _ _ ((mem_sub P).1 x.2) ((mem_sub P).1 y.2)]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by rw [hTo j m]

/-- the shift on `sub P` as a linear isometry into `TSpace P` -/
noncomputable def shiftIso (hTo : IsToeplitz P.T) : sub P →ₗᵢ[ℂ] TSpace P :=
  ((shift P).domRestrict (sub P)).isometryOfInner fun x y => shift_isometry P hTo x y

/-- the unitary extension -/
noncomputable def U (hTo : IsToeplitz P.T) : TSpace P →ₗᵢ[ℂ] TSpace P := (shiftIso P hTo).extend

lemma U_apply_sub (hTo : IsToeplitz P.T) {x : TSpace P} (hx : x ∈ sub P) : U P hTo x = shift P x :=
  LinearIsometry.extend_apply (shiftIso P hTo) ⟨x, hx⟩

/-- the basis vectors -/
def ev (j : Fin (k + 1)) : TSpace P := (toFun P).symm (Pi.single j 1)

lemma toFun_ev (j : Fin (k + 1)) : toFun P (ev P j) = Pi.single j 1 := rfl

lemma ev_mem_sub (j : Fin k) : ev P j.castSucc ∈ sub P := by
  rw [mem_sub, toFun_ev, Pi.single_apply]
  simp [(Fin.castSucc_ne_last j).symm]

lemma shift_ev (j : Fin k) : shift P (ev P j.castSucc) = ev P j.succ := by
  apply (toFun P).injective
  rw [toFun_shift, toFun_ev, toFun_ev]
  funext i
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [Pi.single_apply, Fin.succ_ne_zero]
  · simp only [Fin.cons_succ, Pi.single_apply, Fin.castSucc_inj, Fin.succ_inj]

lemma U_ev (hTo : IsToeplitz P.T) (j : Fin k) : U P hTo (ev P j.castSucc) = ev P j.succ := by
  rw [U_apply_sub P hTo (ev_mem_sub P j), shift_ev]

lemma U_iterate_ev (hTo : IsToeplitz P.T) : ∀ i (hi : i < k + 1), (U P hTo)^[i] (ev P 0) = ev P ⟨i, hi⟩
  | 0, _ => rfl
  | i + 1, hi => by
    rw [Function.iterate_succ_apply', U_iterate_ev hTo i (by omega)]
    have := U_ev P hTo ⟨i, by omega⟩
    simpa using this

end TSpace

/-- `‖q(u)‖ ≤ max_{|z|=1} |q(z)|` for a unitary `u` -/
lemma norm_aeval_unitary_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : unitary (E →L[ℂ] E)) (q : ℂ[X]) {M : ℝ} (hM0 : 0 ≤ M)
    (hq : ∀ z : ℂ, ‖z‖ = 1 → ‖q.eval z‖ ≤ M) : ‖aeval (u : E →L[ℂ] E) q‖ ≤ M := by
  rw [← cfc_polynomial q (u : E →L[ℂ] E)]
  refine norm_cfc_le hM0 fun z hz => hq z ?_
  have := spectrum.subset_circle_of_unitary (𝕜 := ℂ) u.2 hz
  simpa using this

/-- **The Toeplitz bound.** -/
theorem toeplitz_bound {k : ℕ} (T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hT : T.PosDef) (hTo : IsToeplitz T)
    (c : Fin (k + 1) → ℂ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ j, c j * z ^ (j : ℕ)‖ ≤ M) :
    (star c ⬝ᵥ (T *ᵥ c)).re ≤ (T 0 0).re * M ^ 2 := by
  let P : PDMat k := ⟨T, hT⟩
  let u : unitary (TSpace P →L[ℂ] TSpace P) :=
    Unitary.linearIsometryEquiv.symm ((TSpace.U P hTo).toLinearIsometryEquiv rfl)
  have hu : ∀ x, (u : TSpace P →L[ℂ] TSpace P) x = TSpace.U P hTo x := fun x => rfl
  let q : ℂ[X] := ∑ j : Fin (k + 1), C (c j) * X ^ (j : ℕ)
  have hq : ∀ z : ℂ, ‖z‖ = 1 → ‖q.eval z‖ ≤ M := by
    intro z hz
    simpa [q, eval_finsetSum] using hM z hz
  have hnorm := norm_aeval_unitary_le u q hM0 hq
  -- `q(u) e₀ = c`
  have hpow : ∀ n (hn : n < k + 1),
      ((u : TSpace P →L[ℂ] TSpace P) ^ n) (TSpace.ev P 0) = TSpace.ev P ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih (by omega), hu]
      have := TSpace.U_ev P hTo ⟨n, by omega⟩
      simpa using this
  have hpow' : ∀ j : Fin (k + 1), ((u : TSpace P →L[ℂ] TSpace P) ^ (j : ℕ)) (TSpace.ev P 0) = TSpace.ev P j :=
    fun j => hpow j j.2
  have hqe : aeval (u : TSpace P →L[ℂ] TSpace P) q (TSpace.ev P 0) = (TSpace.toFun P).symm c := by
    simp only [q, map_sum, map_mul, aeval_C, aeval_X_pow, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ContinuousLinearMap.coe_smul', Pi.smul_apply, hpow']
    apply (TSpace.toFun P).injective
    rw [map_sum, LinearEquiv.apply_symm_apply]
    funext i
    simp only [map_smul, TSpace.toFun_ev, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hx : ‖(TSpace.toFun P).symm c‖ ≤ M * ‖TSpace.ev P 0‖ := by
    rw [← hqe]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  have h1 : ‖(TSpace.toFun P).symm c‖ ^ 2 = (star c ⬝ᵥ (T *ᵥ c)).re := by
    rw [TSpace.norm_sq_def, LinearEquiv.apply_symm_apply]
  have h2 : ‖TSpace.ev P 0‖ ^ 2 = (T 0 0).re := by
    rw [TSpace.norm_sq_def, TSpace.toFun_ev, Pi.star_single, star_one, single_one_dotProduct,
      Matrix.mulVec_single_one]
    rfl
  rw [← h1, ← h2]
  have h0 : 0 ≤ ‖(TSpace.toFun P).symm c‖ := norm_nonneg _
  nlinarith [mul_le_mul hx hx h0 (mul_nonneg hM0 (norm_nonneg _))]

/-- **The Toeplitz bound**, positive semidefinite version (apply the definite one to `T + ε 1`, `ε → 0`). -/
theorem toeplitz_bound_psd {k : ℕ} (T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hT : T.PosSemidef)
    (hTo : IsToeplitz T) (c : Fin (k + 1) → ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ j, c j * z ^ (j : ℕ)‖ ≤ M) :
    (star c ⬝ᵥ (T *ᵥ c)).re ≤ (T 0 0).re * M ^ 2 := by
  have key : ∀ ε : ℝ, 0 < ε → (star c ⬝ᵥ (T *ᵥ c)).re ≤ (T 0 0).re * M ^ 2 + ε * M ^ 2 := by
    intro ε hε
    set Tε : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := T + (ε : ℂ) • 1 with hTε
    have hquad : ∀ x : Fin (k + 1) → ℂ, star x ⬝ᵥ (Tε *ᵥ x) = star x ⬝ᵥ (T *ᵥ x) + (ε : ℂ) * (star x ⬝ᵥ x) := by
      intro x
      rw [hTε, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
        smul_eq_mul]
    have hpd : Tε.PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
      · rw [hTε, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          hT.isHermitian.eq, Complex.star_def, Complex.conj_ofReal]
      · rw [hquad]
        have h1 := hT.dotProduct_mulVec_nonneg x
        have h2 : 0 < star x ⬝ᵥ x := dotProduct_star_self_pos_iff.2 hx
        have h3 : (0 : ℂ) < (ε : ℂ) := by exact_mod_cast hε
        exact add_pos_of_nonneg_of_pos h1 (mul_pos h3 h2)
    have hTo' : IsToeplitz Tε := by
      intro j l
      simp only [hTε, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hTo j l, Fin.succ_inj,
        Fin.castSucc_inj]
    have hb := toeplitz_bound Tε hpd hTo' c hM0 hM
    rw [hquad] at hb
    have hc : 0 ≤ (star c ⬝ᵥ c).re := (Complex.nonneg_iff.1 (dotProduct_star_self_nonneg c)).1
    have hT00 : (Tε 0 0).re = (T 0 0).re + ε := by
      simp [hTε, Matrix.one_apply]
    rw [hT00, Complex.add_re, Complex.re_ofReal_mul] at hb
    nlinarith [mul_nonneg hε.le hc]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hε : 0 < δ / (M ^ 2 + 1) := div_pos hδ (by positivity)
  have h := key _ hε
  have : δ / (M ^ 2 + 1) * M ^ 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg M]
  linarith

end Bohr59a
