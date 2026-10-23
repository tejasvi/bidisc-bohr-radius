/-
Newman's bound `S_n ≤ √n` (D. J. Newman; H. S. Shapiro's thesis, 1951), from the Toeplitz bound applied to the corner matrix
`T = I + ξ E_{0n} + ξ̄ E_{n0}` (`|ξ| = 1`), which gives `Σ|c_j|² + 2|c_0||c_n| ≤ max_T |q|²`, and Cauchy–Schwarz over the
`n` numbers `|c_0| + |c_n|, |c_1|, …, |c_{n-1}|`.
-/
import Bohr59a.Toeplitz
import Bohr59a.Slice

open Complex Finset Matrix
open scoped ComplexOrder

namespace Bohr59a

/-- the corner Toeplitz matrix `I + ξ E_{0,n} + ξ̄ E_{n,0}` of size `n + 1 = m + 2` -/
noncomputable def cornerMat (m : ℕ) (ξ : ℂ) : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ :=
  1 + Matrix.single 0 (Fin.last (m + 1)) ξ + Matrix.single (Fin.last (m + 1)) 0 (star ξ)

lemma star_dot_self {k : ℕ} (x : Fin k → ℂ) : star x ⬝ᵥ x = ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]

/-- a sum over `Fin (m + 2)` with the two ends split off -/
lemma sum_fin_ends {M : Type*} [AddCommMonoid M] (m : ℕ) (f : Fin (m + 1 + 1) → M) :
    ∑ j, f j = f 0 + (∑ i : Fin m, f i.castSucc.succ + f (Fin.last (m + 1))) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  rfl

lemma cornerMat_quad (m : ℕ) (ξ : ℂ) (x : Fin (m + 1 + 1) → ℂ) :
    star x ⬝ᵥ (cornerMat m ξ *ᵥ x) = star x ⬝ᵥ x + star (x 0) * (ξ * x (Fin.last (m + 1)))
      + star (x (Fin.last (m + 1))) * (star ξ * x 0) := by
  rw [cornerMat, add_mulVec, add_mulVec, one_mulVec, single_mulVec_eq, single_mulVec_eq, dotProduct_add, dotProduct_add,
    dotProduct_smul, dotProduct_smul, dotProduct_single, dotProduct_single]
  simp only [Pi.star_apply, smul_eq_mul, mul_one]
  ring

lemma cornerMat_herm (m : ℕ) (ξ : ℂ) : (cornerMat m ξ).IsHermitian := by
  unfold IsHermitian cornerMat
  rw [conjTranspose_add, conjTranspose_add, conjTranspose_one, conjTranspose_single, conjTranspose_single, star_star]
  abel

lemma cornerMat_psd (m : ℕ) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) : (cornerMat m ξ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (cornerMat_herm m ξ) fun x => ?_
  set l := Fin.last (m + 1)
  set w := star (x 0) * (ξ * x l) with hw
  have hw' : star (x l) * (star ξ * x 0) = (starRingEnd ℂ) w := by
    rw [hw, ← Complex.star_def, star_mul', star_mul', star_star]; ring
  rw [cornerMat_quad, star_dot_self, hw', add_assoc, Complex.add_conj, ← Complex.ofReal_add, Complex.zero_le_real]
  have hsum : ‖x 0‖ ^ 2 + ‖x l‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 := by
    rw [sum_fin_ends m (fun j => ‖x j‖ ^ 2)]
    have : 0 ≤ ∑ i : Fin m, ‖x i.castSucc.succ‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    linarith
  have hwn : ‖w‖ ≤ ‖x 0‖ * ‖x l‖ := by
    rw [hw, norm_mul, norm_mul, norm_star]
    calc ‖x 0‖ * (‖ξ‖ * ‖x l‖) ≤ ‖x 0‖ * (1 * ‖x l‖) := by gcongr
      _ = ‖x 0‖ * ‖x l‖ := by ring
  have hre : -‖w‖ ≤ w.re := by
    have := Complex.abs_re_le_norm w
    have := neg_abs_le w.re
    linarith
  nlinarith [sq_nonneg (‖x 0‖ - ‖x l‖)]

lemma cornerMat_toeplitz (m : ℕ) (ξ : ℂ) : IsToeplitz (cornerMat m ξ) := by
  intro j l
  have h1 : (0 : Fin (m + 1 + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  have h2 : Fin.last (m + 1) ≠ l.castSucc := (Fin.castSucc_lt_last l).ne'
  have h3 : (0 : Fin (m + 1 + 1)) ≠ l.succ := (Fin.succ_ne_zero l).symm
  have h4 : Fin.last (m + 1) ≠ j.castSucc := (Fin.castSucc_lt_last j).ne'
  simp [cornerMat, Matrix.one_apply, h1, h2, h3, h4, Fin.succ_inj, Fin.castSucc_inj]

lemma cornerMat_00 (m : ℕ) (ξ : ℂ) : cornerMat m ξ 0 0 = 1 := by
  have h : (0 : Fin (m + 1 + 1)) ≠ Fin.last (m + 1) := (Fin.last_pos' (n := m + 1)).ne
  simp [cornerMat, h.symm]

/-- **Newman's bound** `S_n ≤ √n` for `n ≥ 1`. -/
theorem sidon_newman {n : ℕ} (hn : 1 ≤ n) : SidonBound n (Real.sqrt n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro c M hM
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 1 (by simp))
  set l := Fin.last (m + 1)
  -- the phase `ξ` aligning `c_0` and `c_n`
  obtain ⟨ξ, hξ1, hξ⟩ := Complex.exists_norm_eq_mul_self (star (c 0) * c l)
  have hT := toeplitz_bound_psd (cornerMat m ξ) (cornerMat_psd m hξ1.le) (cornerMat_toeplitz m ξ) c hM0 hM
  rw [cornerMat_00, cornerMat_quad, star_dot_self] at hT
  have e1 : star (c 0) * (ξ * c l) = ((‖star (c 0) * c l‖ : ℝ) : ℂ) := by rw [hξ]; ring
  have e2 : star (c l) * (star ξ * c 0) = ((‖star (c 0) * c l‖ : ℝ) : ℂ) := by
    rw [← Complex.conj_ofReal, hξ, ← Complex.star_def, star_mul', star_mul', star_star]; ring
  rw [e1, e2, norm_mul, norm_star] at hT
  simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re, one_mul] at hT
  -- `Σ|c_j|² + 2|c_0||c_n| ≤ M²`
  set u := ‖c 0‖ + ‖c l‖
  set d : Fin (m + 1) → ℝ := Fin.cons u (fun i : Fin m => ‖c i.castSucc.succ‖)
  have hd1 : ∑ i, d i = ∑ j, ‖c j‖ := by
    rw [Fin.sum_univ_succ, sum_fin_ends m (fun j => ‖c j‖)]
    simp only [d, Fin.cons_zero, Fin.cons_succ, u]; ring
  have hd2 : ∑ i, d i ^ 2 = ∑ j, ‖c j‖ ^ 2 + 2 * (‖c 0‖ * ‖c l‖) := by
    rw [Fin.sum_univ_succ, sum_fin_ends m (fun j => ‖c j‖ ^ 2)]
    simp only [d, Fin.cons_zero, Fin.cons_succ, u]; ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin (m + 1)))) (f := d)
  rw [card_univ, Fintype.card_fin, hd1, hd2] at hcs
  have hS : (∑ j, ‖c j‖) ^ 2 ≤ (Real.sqrt ((m + 1 : ℕ) : ℝ) * M) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc (∑ j, ‖c j‖) ^ 2 ≤ ((m + 1 : ℕ) : ℝ) * (∑ j, ‖c j‖ ^ 2 + 2 * (‖c 0‖ * ‖c l‖)) := by exact_mod_cast hcs
      _ ≤ ((m + 1 : ℕ) : ℝ) * M ^ 2 := by gcongr; linarith
  have h0 : 0 ≤ ∑ j, ‖c j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 hS

end Bohr59a
