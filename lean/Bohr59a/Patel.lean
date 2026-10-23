/-
Patel's Lemma 1 (MathDB problem 392062, Section 1) for `h` in `PosReClass`, with `A₂ = |h₂₀| + |h₀₂|`, `B₂ = |h₁₁|`,
`A₃ = |h₃₀| + |h₀₃|`, `B₃ = |h₂₁| + |h₁₂|`:
(a) `A₂² + B₂² ≤ 4` (the slice `q₂(ζ)` at `±ζ₀` and the parallelogram law);
(b) `35 A₃² + 28 B₃² ≤ 176` (the Toeplitz bound for `R = uu* + 28vv* + 35ww*`);
(c) `A₃ + B₂²/2 ≤ 2` is the named hypothesis `PatelColligation`;
(d) `S₂(H) + r S₃(H) ≤ B(r)` from (a)–(c) by completing four squares.
-/
import Bohr59a.Newman

open Complex Finset Matrix
open scoped ComplexOrder

namespace Bohr59a

lemma slice2 (h : ℕ × ℕ → ℂ) (ζ : ℂ) : sliceCoeff h ζ 2 = h (0, 2) + h (1, 1) * ζ + h (2, 0) * ζ ^ 2 := by
  rw [sliceCoeff, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma Sn2 (h : ℕ × ℕ → ℂ) : Sn h 2 = ‖h (0, 2)‖ + ‖h (1, 1)‖ + ‖h (2, 0)‖ := by
  rw [Sn, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma Sn3 (h : ℕ × ℕ → ℂ) : Sn h 3 = ‖h (0, 3)‖ + ‖h (1, 2)‖ + ‖h (2, 1)‖ + ‖h (3, 0)‖ := by
  rw [Sn, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma conj_mul_unimod {σ : ℂ} (hσ : ‖σ‖ = 1) : (starRingEnd ℂ) σ * σ = 1 := by
  rw [Complex.conj_mul', hσ]; simp

lemma unimod_sq_root {ρ : ℂ} (hρ : ‖ρ‖ = 1) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ ^ 2 = ρ := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq ρ (n := 2) two_pos
  refine ⟨ζ, ?_, hζ⟩
  have : ‖ζ‖ ^ 2 = 1 := by rw [← norm_pow, hζ, hρ]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this

lemma norm_unimod_mul_add {σ : ℂ} (hσ : ‖σ‖ = 1) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖σ * ((a : ℂ) + (b : ℂ))‖ = a + b := by
  rw [norm_mul, hσ, one_mul, ← Complex.ofReal_add, Complex.norm_of_nonneg (add_nonneg ha hb)]

/-- **Lemma 1 (a)**: `A₂² + B₂² ≤ 4`. -/
theorem patel_quad {h : ℕ × ℕ → ℂ} (hP : PosReClass h) :
    (‖h (2, 0)‖ + ‖h (0, 2)‖) ^ 2 + ‖h (1, 1)‖ ^ 2 ≤ 4 := by
  obtain ⟨σ1, hσ1, h1⟩ := Complex.exists_norm_eq_mul_self (h (0, 2))
  obtain ⟨σ2, hσ2, h2⟩ := Complex.exists_norm_eq_mul_self (h (2, 0))
  have hρ : ‖σ2 * (starRingEnd ℂ) σ1‖ = 1 := by rw [norm_mul, Complex.norm_conj, hσ1, hσ2, one_mul]
  obtain ⟨ζ, hζ1, hζ2⟩ := unimod_sq_root hρ
  set a := h (0, 2) + h (2, 0) * ζ ^ 2 with ha_def
  set b := h (1, 1) * ζ with hb_def
  have ha : ‖a‖ = ‖h (2, 0)‖ + ‖h (0, 2)‖ := by
    have e : a = (starRingEnd ℂ) σ1 * ((‖h (0, 2)‖ : ℂ) + (‖h (2, 0)‖ : ℂ)) := by
      rw [h1, h2, ha_def, hζ2]
      linear_combination (-h (0, 2)) * conj_mul_unimod hσ1
    rw [e, norm_unimod_mul_add (by rw [Complex.norm_conj, hσ1]) _ _ (norm_nonneg _) (norm_nonneg _), add_comm]
  have hb : ‖b‖ = ‖h (1, 1)‖ := by rw [hb_def, norm_mul, hζ1, mul_one]
  have hp : ‖a + b‖ ≤ 2 := by
    have := norm_sliceCoeff_le hP hζ1.le (n := 2) (by norm_num)
    rwa [slice2, show h (0, 2) + h (1, 1) * ζ + h (2, 0) * ζ ^ 2 = a + b by rw [ha_def, hb_def]; ring] at this
  have hm : ‖a - b‖ ≤ 2 := by
    have := norm_sliceCoeff_le hP (ζ := -ζ) (by rw [norm_neg, hζ1]) (n := 2) (by norm_num)
    rwa [slice2, show h (0, 2) + h (1, 1) * -ζ + h (2, 0) * (-ζ) ^ 2 = a - b by rw [ha_def, hb_def]; ring] at this
  have hpar := parallelogram_law_with_norm ℂ a b
  rw [← ha, ← hb]
  nlinarith [norm_nonneg (a + b), norm_nonneg (a - b)]

/-! ### The cubic estimate -/

/-- `u = (3, 4, -4, -3)` -/
def uVec : Fin 4 → ℂ := ![3, 4, -4, -3]
/-- `v = (0, 1, 1, 0)` -/
def vVec : Fin 4 → ℂ := ![0, 1, 1, 0]
/-- `w = (ξ, 0, 0, 1)` -/
def wVec (ξ : ℂ) : Fin 4 → ℂ := ![ξ, 0, 0, 1]

/-- `R = uu* + 28 vv* + 35 ww*` -/
noncomputable def RMat (ξ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vecMulVec uVec (star uVec) + (28 : ℂ) • vecMulVec vVec (star vVec) + (35 : ℂ) • vecMulVec (wVec ξ) (star (wVec ξ))

lemma quad_rank1 {n : ℕ} (a x : Fin n → ℂ) :
    star x ⬝ᵥ (vecMulVec a (star a) *ᵥ x) = ((‖star a ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
  rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, star_dotProduct (v := x) (w := a),
    Complex.star_def, Complex.mul_conj']
  push_cast; ring

lemma RMat_quad (ξ : ℂ) (x : Fin 4 → ℂ) :
    star x ⬝ᵥ (RMat ξ *ᵥ x) = ((‖star uVec ⬝ᵥ x‖ ^ 2 + 28 * ‖star vVec ⬝ᵥ x‖ ^ 2
      + 35 * ‖star (wVec ξ) ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
  rw [RMat, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_add, dotProduct_smul,
    dotProduct_smul, quad_rank1, quad_rank1, quad_rank1]
  push_cast
  simp only [smul_eq_mul]

lemma RMat_psd (ξ : ℂ) : (RMat ξ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simp only [IsHermitian, RMat, conjTranspose_add, conjTranspose_smul, conjTranspose_vecMulVec, star_star]
    congr 2 <;> simp [Complex.star_def]
  · rw [RMat_quad, Complex.zero_le_real]
    positivity

lemma RMat_apply (ξ : ℂ) (i j : Fin 4) :
    RMat ξ i j = uVec i * star (uVec j) + 28 * (vVec i * star (vVec j)) + 35 * (wVec ξ i * star (wVec ξ j)) := by
  simp [RMat, vecMulVec_apply]

lemma RMat_00 {ξ : ℂ} (hξ : ‖ξ‖ = 1) : RMat ξ 0 0 = 44 := by
  rw [RMat_apply]
  have : wVec ξ 0 * star (wVec ξ 0) = 1 := by
    simp only [wVec, Matrix.cons_val_zero, Complex.star_def]
    rw [mul_comm]; exact conj_mul_unimod hξ
  rw [this]
  simp [uVec, vVec]
  norm_num

lemma RMat_toeplitz {ξ : ℂ} (hξ : ‖ξ‖ = 1) : IsToeplitz (RMat ξ) := by
  have hξξ : ξ * (starRingEnd ℂ) ξ = 1 := by rw [mul_comm]; exact conj_mul_unimod hξ
  intro j l
  rw [RMat_apply, RMat_apply]
  fin_cases j <;> fin_cases l <;> simp [uVec, vVec, wVec, Complex.star_def, hξξ] <;> norm_num

/-- **The cubic estimate**: if `|Σ_{j ≤ 3} c_j z^j| ≤ M` on the circle, then
`35 (|c₀| + |c₃|)² + 28 (|c₁| + |c₂|)² ≤ 44 M²`. -/
theorem cubic_est (c : Fin 4 → ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ j, c j * z ^ (j : ℕ)‖ ≤ M) :
    35 * (‖c 0‖ + ‖c 3‖) ^ 2 + 28 * (‖c 1‖ + ‖c 2‖) ^ 2 ≤ 44 * M ^ 2 := by
  -- rotate `z` so that `c₁ τ` and `c₂ τ²` have the same argument
  obtain ⟨σ1, hσ1, h1⟩ := Complex.exists_norm_eq_mul_self (c 1)
  obtain ⟨σ2, hσ2, h2⟩ := Complex.exists_norm_eq_mul_self (c 2)
  set τ := (starRingEnd ℂ) σ1 * σ2 with hτ_def
  have hτ : ‖τ‖ = 1 := by rw [hτ_def, norm_mul, Complex.norm_conj, hσ1, hσ2, one_mul]
  set c' : Fin 4 → ℂ := fun j => c j * τ ^ (j : ℕ) with hc'_def
  have hnc' : ∀ j, ‖c' j‖ = ‖c j‖ := fun j => by rw [hc'_def, norm_mul, norm_pow, hτ, one_pow, mul_one]
  have hM' : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ j, c' j * z ^ (j : ℕ)‖ ≤ M := by
    intro z hz
    have e : ∑ j, c' j * z ^ (j : ℕ) = ∑ j, c j * (τ * z) ^ (j : ℕ) :=
      Finset.sum_congr rfl fun j _ => by rw [hc'_def, mul_pow]; ring
    rw [e]
    exact hM _ (by rw [norm_mul, hτ, hz, one_mul])
  have hB : ‖c' 1 + c' 2‖ = ‖c 1‖ + ‖c 2‖ := by
    have e : c' 1 + c' 2 = ((starRingEnd ℂ) σ1 ^ 2 * σ2) * ((‖c 1‖ : ℂ) + (‖c 2‖ : ℂ)) := by
      rw [h1, h2, hc'_def]
      simp only [Fin.val_one, Fin.val_two, pow_one, hτ_def]
      linear_combination (-((starRingEnd ℂ) σ1 * σ2 * c 1)) * conj_mul_unimod hσ1
    rw [e, norm_unimod_mul_add (by rw [norm_mul, norm_pow, Complex.norm_conj, hσ1, hσ2]; norm_num) _ _
      (norm_nonneg _) (norm_nonneg _)]
  -- the phase `ξ` with `|ξ̄ c'₀ + c'₃| = |c'₀| + |c'₃|`
  obtain ⟨σ0, hσ0, h0⟩ := Complex.exists_norm_eq_mul_self (c' 0)
  obtain ⟨σ3, hσ3, h3⟩ := Complex.exists_norm_eq_mul_self (c' 3)
  set ξ := (starRingEnd ℂ) σ0 * σ3 with hξ_def
  have hξ : ‖ξ‖ = 1 := by rw [hξ_def, norm_mul, Complex.norm_conj, hσ0, hσ3, one_mul]
  have hA : ‖(starRingEnd ℂ) ξ * c' 0 + c' 3‖ = ‖c 0‖ + ‖c 3‖ := by
    have e : (starRingEnd ℂ) ξ * c' 0 + c' 3 = (starRingEnd ℂ) σ3 * ((‖c' 0‖ : ℂ) + (‖c' 3‖ : ℂ)) := by
      rw [h0, h3, hξ_def, map_mul, Complex.conj_conj]
      linear_combination (-c' 3) * conj_mul_unimod hσ3
    rw [e, norm_unimod_mul_add (by rw [Complex.norm_conj, hσ3]) _ _ (norm_nonneg _) (norm_nonneg _), hnc', hnc']
  -- the Toeplitz bound for `R`
  have hT := toeplitz_bound_psd (RMat ξ) (RMat_psd ξ) (RMat_toeplitz hξ) c' hM0 hM'
  rw [RMat_quad, RMat_00 hξ, Complex.ofReal_re] at hT
  have hv : star vVec ⬝ᵥ c' = c' 1 + c' 2 := by
    simp [dotProduct, Fin.sum_univ_four, vVec]
  have hw : star (wVec ξ) ⬝ᵥ c' = (starRingEnd ℂ) ξ * c' 0 + c' 3 := by
    simp [dotProduct, Fin.sum_univ_four, wVec, Complex.star_def]
  rw [hv, hw, hB, hA] at hT
  norm_num at hT
  nlinarith [sq_nonneg ‖star uVec ⬝ᵥ c'‖]

/-- **Lemma 1 (b)**: `35 A₃² + 28 B₃² ≤ 176`. -/
theorem patel_cubic {h : ℕ × ℕ → ℂ} (hP : PosReClass h) :
    35 * (‖h (3, 0)‖ + ‖h (0, 3)‖) ^ 2 + 28 * (‖h (2, 1)‖ + ‖h (1, 2)‖) ^ 2 ≤ 176 := by
  have := cubic_est (fun j : Fin 4 => h ((j : ℕ), 3 - j)) (M := 2) (by norm_num) fun z hz => by
    rw [← sliceCoeff_eq_fin]; exact norm_sliceCoeff_le hP hz.le (by norm_num)
  norm_num at this
  nlinarith [this]

/-! ### Completing the squares -/

/-- Patel's majorant `B(r)` of `S₂(H) + r S₃(H)` -/
noncomputable def BFun (α β γ r : ℝ) : ℝ :=
  4 * α + 176 * β + 2 * γ + 1 / (4 * α) + 1 / (4 * (α + γ / 2)) + (r - γ) ^ 2 / (140 * β) + r ^ 2 / (112 * β)

/-- **Lemma 1 (d)**, the algebra: (a), (b), (c) imply `A₂ + B₂ + r (A₃ + B₃) ≤ B(r)`. -/
theorem patel_combine {A2 B2 A3 B3 α β γ r : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ha : A2 ^ 2 + B2 ^ 2 ≤ 4) (hb : 35 * A3 ^ 2 + 28 * B3 ^ 2 ≤ 176) (hc : A3 + B2 ^ 2 / 2 ≤ 2) :
    A2 + B2 + r * (A3 + B3) ≤ BFun α β γ r := by
  have hαγ : 0 < α + γ / 2 := by linarith
  have key : BFun α β γ r - (A2 + B2 + r * (A3 + B3)) =
      α * (4 - A2 ^ 2 - B2 ^ 2) + β * (176 - 35 * A3 ^ 2 - 28 * B3 ^ 2) + γ * (2 - A3 - B2 ^ 2 / 2)
      + α * (A2 - 1 / (2 * α)) ^ 2 + (α + γ / 2) * (B2 - 1 / (2 * (α + γ / 2))) ^ 2
      + 35 * β * (A3 - (r - γ) / (70 * β)) ^ 2 + 28 * β * (B3 - r / (56 * β)) ^ 2 := by
    unfold BFun
    field_simp
    ring
  have t1 : 0 ≤ α * (4 - A2 ^ 2 - B2 ^ 2) := mul_nonneg hα.le (by linarith)
  have t2 : 0 ≤ β * (176 - 35 * A3 ^ 2 - 28 * B3 ^ 2) := mul_nonneg hβ.le (by linarith)
  have t3 : 0 ≤ γ * (2 - A3 - B2 ^ 2 / 2) := mul_nonneg hγ.le (by linarith)
  have t4 : 0 ≤ α * (A2 - 1 / (2 * α)) ^ 2 := by positivity
  have t5 : 0 ≤ (α + γ / 2) * (B2 - 1 / (2 * (α + γ / 2))) ^ 2 := by positivity
  have t6 : 0 ≤ 35 * β * (A3 - (r - γ) / (70 * β)) ^ 2 := by positivity
  have t7 : 0 ≤ 28 * β * (B3 - r / (56 * β)) ^ 2 := by positivity
  linarith

/-- **Lemma 1 (d)**: `S₂(H) + r S₃(H) ≤ B(r)`, given Patel's colligation estimate (c). -/
theorem patel_S23 (hPC : PatelColligation) {h : ℕ × ℕ → ℂ} (hP : PosReClass h) {α β γ : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 < γ) (r : ℝ) : Sn h 2 + r * Sn h 3 ≤ BFun α β γ r := by
  have ha := patel_quad hP
  have hb := patel_cubic hP
  have hc := hPC h hP
  have := patel_combine (A2 := ‖h (2, 0)‖ + ‖h (0, 2)‖) (B2 := ‖h (1, 1)‖) (A3 := ‖h (3, 0)‖ + ‖h (0, 3)‖)
    (B3 := ‖h (2, 1)‖ + ‖h (1, 2)‖) (r := r) hα hβ hγ ha hb (by linarith)
  rw [Sn2, Sn3]
  linarith

end Bohr59a
