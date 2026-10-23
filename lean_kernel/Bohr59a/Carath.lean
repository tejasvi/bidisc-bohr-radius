/-
Carathéodory's coefficient lemma: if `g(λ) = Σ gₙ λⁿ` converges on the unit disc with `Re g > 0` and `g₀ = 1`, then `|gₙ| ≤ 2`
for `n ≥ 1`.  Proof: on the circle of radius `ρ < 1`, `2π gₙ ρⁿ = ∫ g e^{-inθ} = ∫ (g + conj g) e^{-inθ}` (the second integral
`∫ conj(g) e^{-inθ} = conj ∫ g e^{inθ}` vanishes), so `2π |gₙ| ρⁿ ≤ ∫ 2 Re g = 4π`; then `ρ → 1`.
-/
import Mathlib

open Complex MeasureTheory intervalIntegral

namespace Bohr59a

/-- `∫₀^{2π} e^{i p θ} dθ = 2π [p = 0]` -/
lemma integral_exp_int_mul (p : ℤ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp ((p : ℂ) * I * θ) = if p = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hp : p = 0
  · subst hp; simp
  · simp only [hp, ↓reduceIte]
    have hc : (p : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hp) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((p : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have : (p : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ) = (p : ℂ) * (2 * Real.pi * I) := by push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [h1]
    simp

section carath

variable {g : ℕ → ℂ} (hg : ∀ z : ℂ, ‖z‖ < 1 → ∃ v, HasSum (fun n => g n * z ^ n) v ∧ 0 < v.re)
include hg

lemma summable_norm_coeff {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) : Summable fun n => ‖g n‖ * ρ ^ n := by
  obtain ⟨v, hv, -⟩ := hg ρ (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have hs := (summable_norm_iff (E := ℂ)).2 hv.summable
  simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] using hs

/-- the values on the circle of radius `ρ` -/
noncomputable def circF (g : ℕ → ℂ) (ρ θ : ℝ) : ℂ := ∑' n, g n * ((ρ : ℂ) * Complex.exp (θ * I)) ^ n

lemma hasSum_circF {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (θ : ℝ) :
    HasSum (fun n => g n * ((ρ : ℂ) * Complex.exp (θ * I)) ^ n) (circF g ρ θ) := by
  have hn : ‖(ρ : ℂ) * Complex.exp (θ * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  obtain ⟨v, hv, -⟩ := hg _ hn
  exact hv.summable.hasSum

lemma re_circF_pos {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (θ : ℝ) : 0 < (circF g ρ θ).re := by
  have hn : ‖(ρ : ℂ) * Complex.exp (θ * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  obtain ⟨v, hv, hre⟩ := hg _ hn
  rw [(hasSum_circF hg h0 h1 θ).unique hv]
  exact hre

omit hg in
lemma term_eq (m : ℕ) (k : ℤ) (ρ θ : ℝ) :
    g m * ((ρ : ℂ) * Complex.exp (θ * I)) ^ m * Complex.exp (-(k : ℂ) * I * θ) =
      g m * (ρ : ℂ) ^ m * Complex.exp ((((m : ℤ) - k : ℤ) : ℂ) * I * θ) := by
  have h1 : ((ρ : ℂ) * Complex.exp (θ * I)) ^ m = (ρ : ℂ) ^ m * Complex.exp (m * (θ * I)) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
  have h2 : Complex.exp (m * (θ * I)) * Complex.exp (-(k : ℂ) * I * θ) =
      Complex.exp ((((m : ℤ) - k : ℤ) : ℂ) * I * θ) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h1, ← h2]
  ring

/-- the Fourier coefficients of the boundary values on the circle of radius `ρ` -/
lemma hasSum_integral_circF (k : ℤ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    HasSum (fun m : ℕ => g m * (ρ : ℂ) ^ m * (if (m : ℤ) - k = 0 then (2 * Real.pi : ℂ) else 0))
      (∫ θ in (0 : ℝ)..2 * Real.pi, circF g ρ θ * Complex.exp (-(k : ℂ) * I * θ)) := by
  have hcont : ∀ m : ℕ, Continuous fun θ : ℝ =>
      g m * ((ρ : ℂ) * Complex.exp (θ * I)) ^ m * Complex.exp (-(k : ℂ) * I * θ) := fun m => by fun_prop
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 2 * Real.pi)
    (F := fun (m : ℕ) (θ : ℝ) => g m * ((ρ : ℂ) * Complex.exp (θ * I)) ^ m * Complex.exp (-(k : ℂ) * I * θ))
    (f := fun θ => circF g ρ θ * Complex.exp (-(k : ℂ) * I * θ))
    (fun m _ => ‖g m‖ * ρ ^ m) (fun m => (hcont m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall fun θ _ => by
      rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg h0]
      have : ‖Complex.exp (-(k : ℂ) * I * θ)‖ = 1 := by
        rw [show -(k : ℂ) * I * θ = ((-(k : ℝ) * θ : ℝ) : ℂ) * I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [this, mul_one])
    (Filter.Eventually.of_forall fun θ _ => summable_norm_coeff hg h0 h1)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => (hasSum_circF hg h0 h1 θ).mul_right _)
  have hfun : (fun m : ℕ => ∫ θ in (0 : ℝ)..2 * Real.pi,
      g m * ((ρ : ℂ) * Complex.exp (θ * I)) ^ m * Complex.exp (-(k : ℂ) * I * θ)) =
      fun m : ℕ => g m * (ρ : ℂ) ^ m * (if (m : ℤ) - k = 0 then (2 * Real.pi : ℂ) else 0) := by
    funext m
    simp only [term_eq m k ρ]
    rw [intervalIntegral.integral_const_mul, integral_exp_int_mul]
  rw [← hfun]
  exact h

lemma continuous_circF {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) : Continuous (circF g ρ) := by
  refine continuous_tsum (fun m => by fun_prop) (summable_norm_coeff hg h0 h1) fun m θ => ?_
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg h0]

omit hg in
lemma intervalIntegral_conj (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ∫ θ in a..b, (starRingEnd ℂ) (f θ) = (starRingEnd ℂ) (∫ θ in a..b, f θ) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, integral_conj]

/-- Carathéodory's coefficient lemma. -/
theorem carath_coeff (h0 : g 0 = 1) {n : ℕ} (hn : 1 ≤ n) : ‖g n‖ ≤ 2 := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have key : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ‖g n‖ * ρ ^ n ≤ 2 := by
    intro ρ hρ0 hρ1
    have hF := continuous_circF hg hρ0.le hρ1
    -- the three Fourier coefficients
    have hI1 : ∫ θ in (0 : ℝ)..2 * Real.pi, circF g ρ θ * Complex.exp (-((n : ℤ) : ℂ) * I * θ) =
        g n * (ρ : ℂ) ^ n * (2 * Real.pi : ℂ) := by
      refine (hasSum_integral_circF hg (n : ℤ) hρ0.le hρ1).unique ?_
      have : (fun m : ℕ => g m * (ρ : ℂ) ^ m * (if (m : ℤ) - (n : ℤ) = 0 then (2 * Real.pi : ℂ) else 0)) =
          fun m => if m = n then g n * (ρ : ℂ) ^ n * (2 * Real.pi : ℂ) else 0 := by
        funext m
        by_cases hm : m = n
        · subst hm; simp
        · have : (m : ℤ) - (n : ℤ) ≠ 0 := by omega
          simp [hm, this]
      rw [this]
      exact hasSum_ite_eq n _
    have hI2 : ∫ θ in (0 : ℝ)..2 * Real.pi, circF g ρ θ * Complex.exp (-((-(n : ℤ) : ℤ) : ℂ) * I * θ) = 0 := by
      refine (hasSum_integral_circF hg (-(n : ℤ)) hρ0.le hρ1).unique ?_
      have : (fun m : ℕ => g m * (ρ : ℂ) ^ m * (if (m : ℤ) - (-(n : ℤ)) = 0 then (2 * Real.pi : ℂ) else 0)) =
          fun _ => 0 := by
        funext m
        have : ¬ ((m : ℤ) - (-(n : ℤ)) = 0) := by omega
        simp only [this, ↓reduceIte, mul_zero]
      rw [this]
      exact hasSum_zero
    have hI0 : ∫ θ in (0 : ℝ)..2 * Real.pi, circF g ρ θ * Complex.exp (-((0 : ℤ) : ℂ) * I * θ) =
        (2 * Real.pi : ℂ) := by
      refine (hasSum_integral_circF hg 0 hρ0.le hρ1).unique ?_
      have : (fun m : ℕ => g m * (ρ : ℂ) ^ m * (if (m : ℤ) - (0 : ℤ) = 0 then (2 * Real.pi : ℂ) else 0)) =
          fun m => if m = 0 then (2 * Real.pi : ℂ) else 0 := by
        funext m
        by_cases hm : m = 0
        · subst hm; simp [h0]
        · have : (m : ℤ) - 0 ≠ 0 := by omega
          simp [hm, this]
      rw [this]
      exact hasSum_ite_eq 0 _
    simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one] at hI0
    -- `I1 = ∫ (F + conj F) e^{-inθ} = ∫ 2 Re F e^{-inθ}`
    set E : ℝ → ℂ := fun θ => Complex.exp (-((n : ℤ) : ℂ) * I * θ) with hE
    have hEconj : ∀ θ : ℝ, (starRingEnd ℂ) (Complex.exp (-((-(n : ℤ) : ℤ) : ℂ) * I * θ)) = E θ := by
      intro θ
      rw [← Complex.exp_conj, hE]
      congr 1
      simp [Complex.conj_ofReal]
    have hconj : (starRingEnd ℂ) (∫ θ in (0 : ℝ)..2 * Real.pi,
        circF g ρ θ * Complex.exp (-((-(n : ℤ) : ℤ) : ℂ) * I * θ)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, (starRingEnd ℂ) (circF g ρ θ) * E θ := by
      rw [← intervalIntegral_conj _ hpi]
      congr 1
      funext θ
      rw [map_mul, hEconj]
    rw [hI2, map_zero] at hconj
    have hsum : g n * (ρ : ℂ) ^ n * (2 * Real.pi : ℂ) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, (((2 * (circF g ρ θ).re : ℝ) : ℂ) * E θ) := by
      have hint1 : IntervalIntegrable (fun θ => circF g ρ θ * E θ) MeasureTheory.volume 0 (2 * Real.pi) :=
        (hF.mul (by fun_prop)).intervalIntegrable _ _
      have hint2 : IntervalIntegrable (fun θ => (starRingEnd ℂ) (circF g ρ θ) * E θ) MeasureTheory.volume 0
          (2 * Real.pi) :=
        ((Complex.continuous_conj.comp hF).mul (by fun_prop)).intervalIntegrable _ _
      rw [← hI1, ← add_zero (∫ θ in (0 : ℝ)..2 * Real.pi, circF g ρ θ * E θ), hconj,
        ← intervalIntegral.integral_add hint1 hint2]
      congr 1
      funext θ
      rw [← add_mul, Complex.add_conj]
    -- norm bound
    have hnormE : ∀ θ : ℝ, ‖E θ‖ = 1 := by
      intro θ
      show ‖Complex.exp (-((n : ℤ) : ℂ) * I * θ)‖ = 1
      rw [show -((n : ℤ) : ℂ) * I * θ = ((-(n : ℝ) * θ : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hbound : ‖g n * (ρ : ℂ) ^ n * (2 * Real.pi : ℂ)‖ ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, 2 * (circF g ρ θ).re := by
      rw [hsum]
      refine (intervalIntegral.norm_integral_le_integral_norm hpi).trans (le_of_eq ?_)
      refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [norm_mul, hnormE, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by have := re_circF_pos hg hρ0.le hρ1 θ; linarith)]
    have hre : ∫ θ in (0 : ℝ)..2 * Real.pi, 2 * (circF g ρ θ).re = 2 * (2 * Real.pi) := by
      have : ∫ θ in (0 : ℝ)..2 * Real.pi, (circF g ρ θ).re = (∫ θ in (0 : ℝ)..2 * Real.pi, circF g ρ θ).re := by
        rw [intervalIntegral.integral_of_le hpi, intervalIntegral.integral_of_le hpi]
        exact integral_re ((hF.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
      rw [intervalIntegral.integral_const_mul, this, hI0]
      simp
    rw [hre, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0] at hbound
    have h2pi : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    rw [h2pi] at hbound
    have hpos : 0 < 2 * Real.pi := by positivity
    nlinarith
  -- let `ρ → 1`
  by_contra hcon
  have hcon : 2 < ‖g n‖ := lt_of_not_ge hcon
  set a := ‖g n‖ with ha
  -- choose `ρ = 1 - ε` with `a (1 - n ε) > 2`
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set ε := (a - 2) / (2 * a * n) with hε
  have ha0 : 0 < a := by linarith
  have hε0 : 0 < ε := by rw [hε]; apply div_pos (by linarith) (by positivity)
  have hε1 : ε < 1 := by
    rw [hε, div_lt_one (by positivity)]
    have h1n : a * 1 ≤ a * n := mul_le_mul_of_nonneg_left (by exact_mod_cast hn) ha0.le
    linarith
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -ε by linarith) n
  have hk := key (1 - ε) (by linarith) (by linarith)
  have hρn : 1 - n * ε ≤ (1 - ε) ^ n := by
    have := hb; rw [show (1 : ℝ) + -ε = 1 - ε by ring] at this; linarith
  have : a * (1 - n * ε) ≤ 2 := le_trans (mul_le_mul_of_nonneg_left hρn ha0.le) hk
  have hcalc : a * (1 - n * ε) = a - (a - 2) / 2 := by
    rw [hε]; field_simp
  rw [hcalc] at this
  linarith

end carath

end Bohr59a
