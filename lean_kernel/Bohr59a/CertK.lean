/-
Soundness of the kernel checker `Bohr59aCoreK` (integers, fixed-point hints, exact checks).
-/
import Bohr59aCoreK.TrigOK
import Bohr59aCoreK.Walk
import Bohr59aCoreK.VertexH
import Bohr59aCoreK.Walk2
import Bohr59a.CertShard

open Complex Matrix Finset Real
open scoped ComplexOrder

namespace Bohr59a.CertK

open Bohr59aK Bohr59aCore Bohr59a.Cert

/-! ### Gaussian integers -/

/-- the complex number of a Gaussian integer -/
def giC (a : GI) : ℂ := ⟨(a.re : ℝ), (a.im : ℝ)⟩

@[simp] lemma giC_re (a : GI) : (giC a).re = a.re := rfl
@[simp] lemma giC_im (a : GI) : (giC a).im = a.im := rfl

lemma giC_add (a b : GI) : giC (a.add b) = giC a + giC b := by apply Complex.ext <;> simp [GI.add]
lemma giC_sub (a b : GI) : giC (a.sub b) = giC a - giC b := by apply Complex.ext <;> simp [GI.sub]
lemma giC_mul (a b : GI) : giC (a.mul b) = giC a * giC b := by
  apply Complex.ext <;> simp [GI.mul, Complex.mul_re, Complex.mul_im]
lemma giC_conj (a : GI) : giC a.conj = star (giC a) := by apply Complex.ext <;> simp [GI.conj]
@[simp] lemma giC_zero : giC GI.zero = 0 := by apply Complex.ext <;> simp [GI.zero]

lemma norm_giC_le (a : GI) : ‖giC a‖ ≤ (a.abs1 : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  simp [GI.abs1, Int.natCast_natAbs, Int.cast_abs]

lemma giC_sumGI (f : ℕ → GI) (n : ℕ) : giC (sumGI f n) = ∑ p : Fin n, giC (f p) := by
  rw [← Finset.sum_range (fun p => giC (f p))]
  induction n with
  | zero => simp [sumGI]
  | succ n ih => rw [sumGI, giC_add, ih, Finset.sum_range_succ]

lemma cast_sumInt (f : ℕ → ℤ) (n : ℕ) : ((sumInt f n : ℤ) : ℝ) = ∑ p : Fin n, (f p : ℝ) := by
  rw [← Finset.sum_range (fun p => (f p : ℝ))]
  induction n with
  | zero => simp [sumInt]
  | succ n ih => rw [sumInt, Int.cast_add, ih, Finset.sum_range_succ]

/-! ### Positive semidefiniteness from diagonal dominance -/

/-- A Hermitian matrix whose diagonal dominates the off-diagonal row sums is positive semidefinite. -/
lemma psd_of_dom {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hH : M.IsHermitian)
    (hd : ∀ i, ∑ j, (if j = i then 0 else ‖M i j‖) ≤ (M i i).re) : M.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
  have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := by
    have h := hH.star_dotProduct_mulVec_comm x x
    have := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [Complex.nonneg_iff]
  refine ⟨?_, him.symm⟩
  have hdiag : ∀ i, (M i i).im = 0 := fun i => by
    have := congrArg Complex.im (hH.apply i i)
    rw [Complex.star_def, Complex.conj_im] at this
    linarith
  have hsym : ∀ i j, ‖M i j‖ = ‖M j i‖ := fun i j => by rw [← hH.apply j i, norm_star]
  set a : Fin n → ℝ := fun i => ‖x i‖
  -- termwise lower bound
  have hterm : ∀ i j, (if j = i then (M i i).re * a i ^ 2 else -(‖M i j‖ * (a i ^ 2 + a j ^ 2) / 2)) ≤
      (star (x i) * (M i j * x j)).re := by
    intro i j
    split_ifs with hji
    · subst hji
      rw [show star (x j) * (M j j * x j) = M j j * (star (x j) * x j) by ring, Complex.star_def,
        Complex.conj_mul', ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hdiag,
        zero_mul, sub_zero]
    · have h1 := Complex.abs_re_le_norm (star (x i) * (M i j * x j))
      have h2 : ‖star (x i) * (M i j * x j)‖ = ‖M i j‖ * (a i * a j) := by
        simp only [norm_mul, norm_star, a]; ring
      have h3 : a i * a j ≤ (a i ^ 2 + a j ^ 2) / 2 := by nlinarith [sq_nonneg (a i - a j)]
      have h4 := neg_abs_le (star (x i) * (M i j * x j)).re
      have h5 : ‖M i j‖ * (a i * a j) ≤ ‖M i j‖ * ((a i ^ 2 + a j ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      linarith
  have hsum : (star x ⬝ᵥ (M *ᵥ x)).re = ∑ i, ∑ j, (star (x i) * (M i j * x j)).re := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum]
  rw [hsum]
  refine le_trans ?_ (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j)
  -- the lower bound is `Σ_i a_i² (M_ii - R_i) ≥ 0`
  set m : Fin n → Fin n → ℝ := fun i j => if j = i then 0 else ‖M i j‖ with hm
  set R : Fin n → ℝ := fun i => ∑ j, m i j with hR
  have hmsym : ∀ i j, m i j = m j i := fun i j => by
    simp only [hm]
    by_cases hij : j = i
    · subst hij; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij), hsym]
  have e1 : ∀ i j, (if j = i then (M i i).re * a i ^ 2 else -(‖M i j‖ * (a i ^ 2 + a j ^ 2) / 2)) =
      (if j = i then (M i i).re * a i ^ 2 else 0) - m i j * a i ^ 2 / 2 - m i j * a j ^ 2 / 2 := by
    intro i j
    simp only [hm]
    split_ifs <;> ring
  simp only [e1, Finset.sum_sub_distrib]
  have s1 : ∀ i, ∑ j, (if j = i then (M i i).re * a i ^ 2 else 0) = (M i i).re * a i ^ 2 := fun i => by
    rw [Finset.sum_ite_eq']; simp
  have s2 : ∀ i, ∑ j, m i j * a i ^ 2 / 2 = R i * a i ^ 2 / 2 := fun i => by
    simp only [hR]; rw [Finset.sum_mul, Finset.sum_div]
  have s3 : ∑ i, ∑ j, m i j * a j ^ 2 / 2 = ∑ i, R i * a i ^ 2 / 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hR]; rw [Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [hmsym]
  simp only [s1, s2, s3]
  have : ∀ i, 0 ≤ ((M i i).re - R i) * a i ^ 2 := fun i => mul_nonneg (sub_nonneg.2 (hd i)) (sq_nonneg _)
  have h0 := Finset.sum_nonneg fun i (_ : i ∈ univ) => this i
  have e2 : ∑ i, ((M i i).re - R i) * a i ^ 2 = ∑ i, (M i i).re * a i ^ 2 - ∑ i, R i * a i ^ 2 / 2 -
      ∑ i, R i * a i ^ 2 / 2 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- Congruence by a unit lower triangular matrix preserves positive semidefiniteness. -/
lemma psd_of_congr {n : ℕ} {T W : Matrix (Fin n) (Fin n) ℂ} (hlow : ∀ i j, i < j → W i j = 0)
    (hdiag : ∀ i, W i i = 1) (hM : (W * T * Wᴴ).PosSemidef) : T.PosSemidef := by
  have hdet : W.det = 1 := by
    rw [Matrix.det_of_lowerTriangular W (fun i j hij => hlow i j hij)]
    simp [hdiag]
  have hu : IsUnit W.det := by rw [hdet]; exact isUnit_one
  have e : T = W⁻¹ * (W * T * Wᴴ) * (W⁻¹)ᴴ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    rw [show W⁻¹ * (W * T * Wᴴ) * (Wᴴ)⁻¹ = (W⁻¹ * W) * T * (Wᴴ * (Wᴴ)⁻¹) by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.nonsing_inv_mul W hu, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_conjTranspose, hdet]; simp),
      Matrix.one_mul, Matrix.mul_one]
  rw [e]
  exact hM.mul_mul_conjTranspose_same W⁻¹


/-! ### The trigonometric table -/

/-- the table agrees with its specification (from the 65 kernel-checked chunks) -/
theorem trigTT_spec (i : ℕ) (hi : i ≤ 1024) : ttGet trigTT 11 i = ttSpec i := by
  obtain ⟨c, r, hr, rfl⟩ : ∃ c r, r < 16 ∧ i = 16 * c + r :=
    ⟨i / 16, i % 16, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 16).symm⟩
  have hc : c ≤ 64 := by omega
  interval_cases c
  · exact trig_chunk_0 r hr (by omega)
  · exact trig_chunk_1 r hr (by omega)
  · exact trig_chunk_2 r hr (by omega)
  · exact trig_chunk_3 r hr (by omega)
  · exact trig_chunk_4 r hr (by omega)
  · exact trig_chunk_5 r hr (by omega)
  · exact trig_chunk_6 r hr (by omega)
  · exact trig_chunk_7 r hr (by omega)
  · exact trig_chunk_8 r hr (by omega)
  · exact trig_chunk_9 r hr (by omega)
  · exact trig_chunk_10 r hr (by omega)
  · exact trig_chunk_11 r hr (by omega)
  · exact trig_chunk_12 r hr (by omega)
  · exact trig_chunk_13 r hr (by omega)
  · exact trig_chunk_14 r hr (by omega)
  · exact trig_chunk_15 r hr (by omega)
  · exact trig_chunk_16 r hr (by omega)
  · exact trig_chunk_17 r hr (by omega)
  · exact trig_chunk_18 r hr (by omega)
  · exact trig_chunk_19 r hr (by omega)
  · exact trig_chunk_20 r hr (by omega)
  · exact trig_chunk_21 r hr (by omega)
  · exact trig_chunk_22 r hr (by omega)
  · exact trig_chunk_23 r hr (by omega)
  · exact trig_chunk_24 r hr (by omega)
  · exact trig_chunk_25 r hr (by omega)
  · exact trig_chunk_26 r hr (by omega)
  · exact trig_chunk_27 r hr (by omega)
  · exact trig_chunk_28 r hr (by omega)
  · exact trig_chunk_29 r hr (by omega)
  · exact trig_chunk_30 r hr (by omega)
  · exact trig_chunk_31 r hr (by omega)
  · exact trig_chunk_32 r hr (by omega)
  · exact trig_chunk_33 r hr (by omega)
  · exact trig_chunk_34 r hr (by omega)
  · exact trig_chunk_35 r hr (by omega)
  · exact trig_chunk_36 r hr (by omega)
  · exact trig_chunk_37 r hr (by omega)
  · exact trig_chunk_38 r hr (by omega)
  · exact trig_chunk_39 r hr (by omega)
  · exact trig_chunk_40 r hr (by omega)
  · exact trig_chunk_41 r hr (by omega)
  · exact trig_chunk_42 r hr (by omega)
  · exact trig_chunk_43 r hr (by omega)
  · exact trig_chunk_44 r hr (by omega)
  · exact trig_chunk_45 r hr (by omega)
  · exact trig_chunk_46 r hr (by omega)
  · exact trig_chunk_47 r hr (by omega)
  · exact trig_chunk_48 r hr (by omega)
  · exact trig_chunk_49 r hr (by omega)
  · exact trig_chunk_50 r hr (by omega)
  · exact trig_chunk_51 r hr (by omega)
  · exact trig_chunk_52 r hr (by omega)
  · exact trig_chunk_53 r hr (by omega)
  · exact trig_chunk_54 r hr (by omega)
  · exact trig_chunk_55 r hr (by omega)
  · exact trig_chunk_56 r hr (by omega)
  · exact trig_chunk_57 r hr (by omega)
  · exact trig_chunk_58 r hr (by omega)
  · exact trig_chunk_59 r hr (by omega)
  · exact trig_chunk_60 r hr (by omega)
  · exact trig_chunk_61 r hr (by omega)
  · exact trig_chunk_62 r hr (by omega)
  · exact trig_chunk_63 r hr (by omega)
  · exact trig_chunk_64 r hr (by omega)

/-- the table entries are balls around `cos`, `sin` of `π m/512` -/
lemma table_mem {m : ℤ} (hm1 : -512 ≤ m) (hm2 : m ≤ 512) {e : TE}
    (h : ttGet trigTT 11 (m + 512).toNat = some e) :
    Ival.Ball.mem 128 (Real.cos (π * m / 512)) ⟨e.cm, e.cr⟩ ∧ Ival.Ball.mem 128 (Real.sin (π * m / 512)) ⟨e.sm, e.sr⟩ := by
  rw [trigTT_spec _ (by omega)] at h
  unfold ttSpec at h
  obtain ⟨cs, hcs, he⟩ := Option.map_eq_some_iff.1 h
  subst he
  have hU := Ival.Ball.mem_ofRat 128 (((m + 512).toNat : ℤ) - 512) 1024 (by norm_num)
  have h2 := Ival.Ball.mem_cosSinTurn hU hcs
  have e : 2 * π * ((((((m + 512).toNat : ℤ) - 512 : ℤ)) : ℝ) / ((1024 : ℕ) : ℝ)) = π * m / 512 := by
    have : (((m + 512).toNat : ℤ) - 512 : ℤ) = m := by omega
    rw [this]; push_cast; ring
  rw [e] at h2
  exact h2


/-! ### Errors of the vertex coordinates -/

/-- the complex number of a Gaussian integer at scale `2^s` -/
noncomputable def gS (s : ℕ) (a : GI) : ℂ := ⟨(a.re : ℝ) / 2 ^ s, (a.im : ℝ) / 2 ^ s⟩

@[simp] lemma gS_re (s : ℕ) (a : GI) : (gS s a).re = (a.re : ℝ) / 2 ^ s := rfl
@[simp] lemma gS_im (s : ℕ) (a : GI) : (gS s a).im = (a.im : ℝ) / 2 ^ s := rfl

lemma ball_abs {x : ℝ} {m : ℤ} {r : ℕ} (h : Ival.Ball.mem 128 x ⟨m, r⟩) : |x - (m : ℝ) / 2 ^ 128| ≤ (r : ℝ) / 2 ^ 128 := h

lemma cdivI_ge (a b : ℤ) (hb : 0 < b) : (a : ℝ) / b ≤ (cdivI a b : ℝ) := by
  unfold cdivI
  rw [if_neg (not_le.2 hb)]
  have hq := Int.ediv_mul_le (-a) hb.ne'
  have hq' : (((-a) / b : ℤ) : ℝ) * (b : ℝ) ≤ ((-a : ℤ) : ℝ) := by exact_mod_cast hq
  rw [div_le_iff₀ (by exact_mod_cast hb), Int.cast_neg]
  rw [Int.cast_neg] at hq'
  linarith

/-- `coordErrK` bounds the distance of the vertex coordinate from `w / 2^224` (times `2^224`) -/
lemma coordErrK_sound {c : Comp} {w : GI} {e : ℤ} (h : coordErrK trigTT c w = some e) :
    ‖coordC c - gS 224 w‖ ≤ (e : ℝ) / 2 ^ 224 := by
  unfold coordErrK at h
  set θ : ℝ := π * c.m / 512 with hθ
  have hexp : cexp ((θ : ℂ) * I) = ⟨Real.cos θ, Real.sin θ⟩ := by
    apply Complex.ext
    · simp only [Complex.exp_ofReal_mul_I_re]
    · simp only [Complex.exp_ofReal_mul_I_im]
  by_cases hm : (decide (c.m < -512) || decide (512 < c.m)) = true
  · rw [if_pos hm] at h; exact absurd h (by simp)
  rw [if_neg hm] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hm
  obtain ⟨hm1, hm2⟩ := hm
  split at h
  · exact absurd h (by simp)
  rename_i E hE
  obtain ⟨hC, hS⟩ := table_mem hm1 hm2 hE
  have hC' := ball_abs hC
  have hS' := ball_abs hS
  have p128 : (0 : ℝ) < 2 ^ 128 := by positivity
  have p224 : (0 : ℝ) < 2 ^ 224 := by positivity
  have p96 : ((2 : ℝ) ^ 224) = 2 ^ 128 * 2 ^ 96 := by rw [← pow_add]
  by_cases htan : c.tan = true
  · -- tangent
    rw [htan] at h
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hj : (decide (c.j < 2) || decide (9 < c.j)) = true
    · rw [if_pos hj] at h; exact absurd h (by simp)
    rw [if_neg hj] at h
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hj
    obtain ⟨hj1, hj2⟩ := hj
    split at h
    · exact absurd h (by simp)
    rename_i H hH
    -- the ball of `cos(π/2^j)` is the table entry at `m = 2^{9-j}`
    have hm' : ((512 + 2 ^ (9 - c.j) : ℕ) : ℤ) = (2 ^ (9 - c.j) : ℤ) + 512 := by push_cast; ring
    have hidx : (512 + 2 ^ (9 - c.j) : ℕ) = (((2 ^ (9 - c.j) : ℕ) : ℤ) + 512).toNat := by
      rw [show (((2 ^ (9 - c.j) : ℕ) : ℤ) + 512) = ((2 ^ (9 - c.j) + 512 : ℕ) : ℤ) by push_cast; ring,
        Int.toNat_natCast]
      ring
    have h29 : (2 : ℤ) ^ (9 - c.j) ≤ 512 := by
      calc (2 : ℤ) ^ (9 - c.j) ≤ 2 ^ 9 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 512 := by norm_num
    rw [hidx] at hH
    have h0 : (0 : ℤ) ≤ ((2 ^ (9 - c.j) : ℕ) : ℤ) := by positivity
    obtain ⟨hHc, _⟩ := table_mem (m := ((2 ^ (9 - c.j) : ℕ) : ℤ)) (by omega) (by exact_mod_cast h29) hH
    have hHc' := ball_abs hHc
    have hcosarg : π * (((2 ^ (9 - c.j) : ℕ) : ℤ) : ℝ) / 512 = π / 2 ^ c.j := by
      push_cast
      rw [show (512 : ℝ) = 2 ^ (9 - c.j) * 2 ^ c.j by rw [← pow_add, Nat.sub_add_cancel hj2]; norm_num]
      field_simp
    rw [hcosarg] at hHc'
    try dsimp only at h
    by_cases hden : H.cm - (H.cr : ℤ) ≤ 0
    · rw [if_pos hden] at h; exact absurd h (by simp)
    rw [if_neg hden] at h
    simp only [Option.some.injEq] at h
    subst h
    set ch := Real.cos (π / 2 ^ c.j) with hch_def
    set hc : ℝ := (H.cm : ℝ) / 2 ^ 128
    set hr : ℝ := (H.cr : ℝ) / 2 ^ 128
    have hden' : (0 : ℝ) < H.cm - H.cr := by exact_mod_cast (not_le.1 hden)
    have hch : hc - hr ≤ ch := by have := (abs_le.1 hHc').1; linarith
    have hpos : 0 < hc - hr := by
      simp only [hc, hr]; rw [← sub_div]; exact div_pos hden' p128
    have hch0 : 0 < ch := lt_of_lt_of_le hpos hch
    have hcoord : coordC c = cexp ((θ : ℂ) * I) / (ch : ℂ) := by
      unfold coordC; rw [if_pos htan]
    rw [hcoord, hexp]
    have hch0' : (ch : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hch0.ne'
    have hsplit : (⟨Real.cos θ, Real.sin θ⟩ : ℂ) / (ch : ℂ) - gS 224 w =
        ((⟨Real.cos θ, Real.sin θ⟩ : ℂ) - gS 224 w * (ch : ℂ)) / (ch : ℂ) := by field_simp
    rw [hsplit, norm_div, Complex.norm_real, Real.norm_of_nonneg hch0.le, div_le_iff₀ hch0]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, gS_re, gS_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero, zero_add]
    -- the integer numerator, as a real number
    set Nn : ℝ := |(E.cm : ℝ) * 2 ^ 224 - w.re * H.cm| + E.cr * 2 ^ 224 + |(w.re : ℝ)| * H.cr +
      (|(E.sm : ℝ) * 2 ^ 224 - w.im * H.cm| + E.sr * 2 ^ 224 + |(w.im : ℝ)| * H.cr) with hNn
    have hNn0 : 0 ≤ Nn := by positivity
    have hb : (0 : ℤ) < H.cm - H.cr := not_le.1 hden
    have hcdiv : ∀ X : ℤ, (X : ℝ) = Nn → Nn / ((H.cm : ℝ) - H.cr) ≤ (cdivI X (H.cm - H.cr) : ℝ) := fun X hX => by
      have := cdivI_ge X (H.cm - H.cr) hb
      rw [hX] at this
      push_cast at this
      exact this
    -- the two coordinate estimates (scaled by `2^352 = 2^128 · 2^224`)
    have h1 : |Real.cos θ - w.re / 2 ^ 224 * ch| ≤ (|(E.cm : ℝ) * 2 ^ 224 - w.re * H.cm| + E.cr * 2 ^ 224 +
        |(w.re : ℝ)| * H.cr) / (2 ^ 128 * 2 ^ 224) := by
      have e : Real.cos θ - w.re / 2 ^ 224 * ch = (Real.cos θ - E.cm / 2 ^ 128) +
          ((E.cm : ℝ) * 2 ^ 224 - w.re * H.cm) / (2 ^ 128 * 2 ^ 224) + w.re / 2 ^ 224 * (hc - ch) := by
        simp only [hc]; field_simp; ring
      rw [e]
      have t1 := abs_add_le (Real.cos θ - E.cm / 2 ^ 128 + ((E.cm : ℝ) * 2 ^ 224 - w.re * H.cm) / (2 ^ 128 * 2 ^ 224))
        (w.re / 2 ^ 224 * (hc - ch))
      have t2 := abs_add_le (Real.cos θ - E.cm / 2 ^ 128) (((E.cm : ℝ) * 2 ^ 224 - w.re * H.cm) / (2 ^ 128 * 2 ^ 224))
      have t3 : |w.re / 2 ^ 224 * (hc - ch)| ≤ |(w.re : ℝ)| * H.cr / (2 ^ 128 * 2 ^ 224) := by
        rw [abs_mul, abs_div, abs_of_pos p224]
        have : |hc - ch| ≤ hr := by rw [abs_sub_comm]; exact hHc'
        calc |(w.re : ℝ)| / 2 ^ 224 * |hc - ch| ≤ |(w.re : ℝ)| / 2 ^ 224 * hr :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by simp only [hr]; field_simp
      have t4 : |((E.cm : ℝ) * 2 ^ 224 - w.re * H.cm) / (2 ^ 128 * 2 ^ 224)| =
          |(E.cm : ℝ) * 2 ^ 224 - w.re * H.cm| / (2 ^ 128 * 2 ^ 224) := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128 * 2 ^ 224)]
      have t5 : (E.cr : ℝ) / 2 ^ 128 = E.cr * 2 ^ 224 / (2 ^ 128 * 2 ^ 224) := by field_simp
      rw [t4] at t2
      have := hC'
      rw [t5] at this
      have e6 : (|(E.cm : ℝ) * 2 ^ 224 - w.re * H.cm| + E.cr * 2 ^ 224 + |(w.re : ℝ)| * H.cr) / (2 ^ 128 * 2 ^ 224) =
          E.cr * 2 ^ 224 / (2 ^ 128 * 2 ^ 224) + |(E.cm : ℝ) * 2 ^ 224 - w.re * H.cm| / (2 ^ 128 * 2 ^ 224) +
            |(w.re : ℝ)| * H.cr / (2 ^ 128 * 2 ^ 224) := by ring
      rw [e6]
      linarith
    have h2 : |Real.sin θ - w.im / 2 ^ 224 * ch| ≤ (|(E.sm : ℝ) * 2 ^ 224 - w.im * H.cm| + E.sr * 2 ^ 224 +
        |(w.im : ℝ)| * H.cr) / (2 ^ 128 * 2 ^ 224) := by
      have e : Real.sin θ - w.im / 2 ^ 224 * ch = (Real.sin θ - E.sm / 2 ^ 128) +
          ((E.sm : ℝ) * 2 ^ 224 - w.im * H.cm) / (2 ^ 128 * 2 ^ 224) + w.im / 2 ^ 224 * (hc - ch) := by
        simp only [hc]; field_simp; ring
      rw [e]
      have t1 := abs_add_le (Real.sin θ - E.sm / 2 ^ 128 + ((E.sm : ℝ) * 2 ^ 224 - w.im * H.cm) / (2 ^ 128 * 2 ^ 224))
        (w.im / 2 ^ 224 * (hc - ch))
      have t2 := abs_add_le (Real.sin θ - E.sm / 2 ^ 128) (((E.sm : ℝ) * 2 ^ 224 - w.im * H.cm) / (2 ^ 128 * 2 ^ 224))
      have t3 : |w.im / 2 ^ 224 * (hc - ch)| ≤ |(w.im : ℝ)| * H.cr / (2 ^ 128 * 2 ^ 224) := by
        rw [abs_mul, abs_div, abs_of_pos p224]
        have : |hc - ch| ≤ hr := by rw [abs_sub_comm]; exact hHc'
        calc |(w.im : ℝ)| / 2 ^ 224 * |hc - ch| ≤ |(w.im : ℝ)| / 2 ^ 224 * hr :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by simp only [hr]; field_simp
      have t4 : |((E.sm : ℝ) * 2 ^ 224 - w.im * H.cm) / (2 ^ 128 * 2 ^ 224)| =
          |(E.sm : ℝ) * 2 ^ 224 - w.im * H.cm| / (2 ^ 128 * 2 ^ 224) := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128 * 2 ^ 224)]
      have t5 : (E.sr : ℝ) / 2 ^ 128 = E.sr * 2 ^ 224 / (2 ^ 128 * 2 ^ 224) := by field_simp
      rw [t4] at t2
      have := hS'
      rw [t5] at this
      have e6 : (|(E.sm : ℝ) * 2 ^ 224 - w.im * H.cm| + E.sr * 2 ^ 224 + |(w.im : ℝ)| * H.cr) / (2 ^ 128 * 2 ^ 224) =
          E.sr * 2 ^ 224 / (2 ^ 128 * 2 ^ 224) + |(E.sm : ℝ) * 2 ^ 224 - w.im * H.cm| / (2 ^ 128 * 2 ^ 224) +
            |(w.im : ℝ)| * H.cr / (2 ^ 128 * 2 ^ 224) := by ring
      rw [e6]
      linarith
    -- combine: `(N_re + N_im)/2^352 ≤ (cdiv / 2^224) · ch`
    have hsum : |Real.cos θ - w.re / 2 ^ 224 * ch| + |Real.sin θ - w.im / 2 ^ 224 * ch| ≤
        Nn / (2 ^ 128 * 2 ^ 224) := by
      have : Nn / (2 ^ 128 * 2 ^ 224) = (|(E.cm : ℝ) * 2 ^ 224 - w.re * H.cm| + E.cr * 2 ^ 224 +
          |(w.re : ℝ)| * H.cr) / (2 ^ 128 * 2 ^ 224) + (|(E.sm : ℝ) * 2 ^ 224 - w.im * H.cm| + E.sr * 2 ^ 224 +
          |(w.im : ℝ)| * H.cr) / (2 ^ 128 * 2 ^ 224) := by simp only [hNn]; ring
      linarith
    refine hsum.trans ?_
    have key : Nn / (2 ^ 128 * 2 ^ 224) = Nn / (H.cm - H.cr) / 2 ^ 224 * (hc - hr) := by
      simp only [hc, hr]; field_simp
    rw [key]
    calc Nn / (H.cm - H.cr) / 2 ^ 224 * (hc - hr) ≤ Nn / (H.cm - H.cr) / 2 ^ 224 * ch :=
          mul_le_mul_of_nonneg_left hch (by positivity)
      _ ≤ _ := by
          gcongr
          exact hcdiv _ (by simp only [hNn]; push_cast; ring)
  · -- corner
    have htan' : c.tan = false := by simpa using htan
    rw [htan'] at h
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at h
    subst h
    have hcoord : coordC c = cexp ((θ : ℂ) * I) := by
      unfold coordC; rw [if_neg htan]
    rw [hcoord, hexp]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, gS_re, gS_im]
    push_cast
    have h1 : |Real.cos θ - (w.re : ℝ) / 2 ^ 224| ≤ ((|(E.cm : ℝ) * 2 ^ 96 - w.re| + (E.cr : ℝ) * 2 ^ 96) / 2 ^ 224 : ℝ) := by
      have e : Real.cos θ - (w.re : ℝ) / 2 ^ 224 = (Real.cos θ - E.cm / 2 ^ 128) + ((E.cm : ℝ) * 2 ^ 96 - w.re) / 2 ^ 224 := by
        rw [p96]; field_simp; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos p224]
      have : (E.cr : ℝ) / 2 ^ 128 = E.cr * 2 ^ 96 / 2 ^ 224 := by rw [p96]; field_simp
      rw [this] at hC'
      have e2 : ((|(E.cm : ℝ) * 2 ^ 96 - w.re| + (E.cr : ℝ) * 2 ^ 96) / 2 ^ 224 : ℝ) =
          (E.cr : ℝ) * 2 ^ 96 / 2 ^ 224 + |(E.cm : ℝ) * 2 ^ 96 - w.re| / 2 ^ 224 := by ring
      rw [e2]; linarith
    have h2 : |Real.sin θ - (w.im : ℝ) / 2 ^ 224| ≤ ((|(E.sm : ℝ) * 2 ^ 96 - w.im| + (E.sr : ℝ) * 2 ^ 96) / 2 ^ 224 : ℝ) := by
      have e : Real.sin θ - (w.im : ℝ) / 2 ^ 224 = (Real.sin θ - E.sm / 2 ^ 128) + ((E.sm : ℝ) * 2 ^ 96 - w.im) / 2 ^ 224 := by
        rw [p96]; field_simp; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos p224]
      have : (E.sr : ℝ) / 2 ^ 128 = E.sr * 2 ^ 96 / 2 ^ 224 := by rw [p96]; field_simp
      rw [this] at hS'
      have e2 : ((|(E.sm : ℝ) * 2 ^ 96 - w.im| + (E.sr : ℝ) * 2 ^ 96) / 2 ^ 224 : ℝ) =
          (E.sr : ℝ) * 2 ^ 96 / 2 ^ 224 + |(E.sm : ℝ) * 2 ^ 96 - w.im| / 2 ^ 224 := by ring
      rw [e2]; linarith
    have e3 : ((|(E.cm : ℝ) * 2 ^ 96 - w.re| + (E.cr : ℝ) * 2 ^ 96 + (|(E.sm : ℝ) * 2 ^ 96 - w.im| +
        (E.sr : ℝ) * 2 ^ 96)) / 2 ^ 224 : ℝ) = (|(E.cm : ℝ) * 2 ^ 96 - w.re| + (E.cr : ℝ) * 2 ^ 96) / 2 ^ 224 +
          (|(E.sm : ℝ) * 2 ^ 96 - w.im| + (E.sr : ℝ) * 2 ^ 96) / 2 ^ 224 := by ring
    linarith


/-! ### Lists -/

lemma nth_eq_getD {α : Type} (d : α) : ∀ (l : List α) (i : ℕ), nth d l i = l.getD i d
  | [], _ => by simp [nth]
  | a :: as, 0 => by simp [nth]
  | a :: as, i + 1 => by simp [nth, nth_eq_getD d as i]

lemma nth_range_map {α : Type} (d : α) (f : ℕ → α) {i n : ℕ} (h : i < n) :
    nth d ((List.range n).map f) i = f i := by
  rw [nth_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-! ### The error sum -/

lemma errTailK_sound (w : List GI) : ∀ (l : List Comp) (j : ℕ) (r : ℤ), errTailK trigTT w l j = some r →
    ∑ i ∈ Finset.range l.length, ‖coordC (l.getD i default) - gS 224 (nth GI.zero w (j + i))‖ ≤ (r : ℝ) / 2 ^ 224
  | [], j, r, h => by
    simp only [errTailK, Option.some.injEq] at h
    subst h; simp
  | c :: cs, j, r, h => by
    unfold errTailK at h
    split at h
    · rename_i e r' he hr
      simp only [Option.some.injEq] at h
      subst h
      have h1 := coordErrK_sound he
      have h2 := errTailK_sound w cs (j + 1) r' hr
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      have e : ∑ i ∈ Finset.range cs.length, ‖coordC (cs.getD i default) - gS 224 (nth GI.zero w (j + (i + 1)))‖ =
          ∑ i ∈ Finset.range cs.length, ‖coordC (cs.getD i default) - gS 224 (nth GI.zero w (j + 1 + i))‖ :=
        Finset.sum_congr rfl fun i _ => by rw [show j + (i + 1) = j + 1 + i by ring]
      rw [e]
      push_cast
      rw [add_div]
      linarith
    · exact absurd h (by simp)

lemma norm_one_sub_gS (a : GI) : ‖1 - gS 224 a‖ ≤ (|(2 : ℝ) ^ 224 - a.re| + |(a.im : ℝ)|) / 2 ^ 224 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  simp only [Complex.sub_re, Complex.one_re, gS_re, Complex.sub_im, Complex.one_im, gS_im, zero_sub, abs_neg]
  have p : (0 : ℝ) < 2 ^ 224 := by positivity
  rw [show (1 : ℝ) - a.re / 2 ^ 224 = (2 ^ 224 - a.re) / 2 ^ 224 by field_simp, abs_div, abs_div, abs_of_pos p,
    add_div]

/-- the total error bound -/
lemma errSumK_sound {D : ℕ} {key : List Comp} (hkey : key.length = D) {w : List GI} {ρ : ℤ}
    (h : errSumK trigTT key w = some ρ) :
    ∑ j : Fin (D + 1 + 1), ‖vtx D key j - gS 224 (nth GI.zero w j)‖ ≤ (ρ : ℝ) / 2 ^ 224 := by
  unfold errSumK at h
  obtain ⟨r, hr, hρ⟩ := Option.map_eq_some_iff.1 h
  subst hρ
  have ht := errTailK_sound w key 2 r hr
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have e0 : vtx D key 0 = 1 := rfl
  have e1 : vtx D key (Fin.succ 0) = 1 := rfl
  have e2 : ∀ d : Fin D, vtx D key d.succ.succ = coordC (key.getD d.val default) := fun d => rfl
  have f2 : ∀ d : Fin D, ((d.succ.succ : Fin (D + 1 + 1)) : ℕ) = 2 + d.val := fun d => by
    simp only [Fin.val_succ]; ring
  simp only [e0, e1, e2, f2, Fin.val_zero, Fin.val_succ, zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun d => ‖coordC (key.getD d default) - gS 224 (nth GI.zero w (2 + d))‖) D, ← hkey]
  have h0 := norm_one_sub_gS (nth GI.zero w 0)
  have h1 := norm_one_sub_gS (nth GI.zero w 1)
  push_cast
  rw [add_div, add_div, add_div, add_div]
  have q0 : (|(2 : ℝ) ^ 224 - (nth GI.zero w 0).re| + |((nth GI.zero w 0).im : ℝ)|) / 2 ^ 224 =
      |(2 : ℝ) ^ 224 - (nth GI.zero w 0).re| / 2 ^ 224 + |((nth GI.zero w 0).im : ℝ)| / 2 ^ 224 := by ring
  have q1 : (|(2 : ℝ) ^ 224 - (nth GI.zero w 1).re| + |((nth GI.zero w 1).im : ℝ)|) / 2 ^ 224 =
      |(2 : ℝ) ^ 224 - (nth GI.zero w 1).re| / 2 ^ 224 + |((nth GI.zero w 1).im : ℝ)| / 2 ^ 224 := by ring
  rw [q0] at h0
  rw [q1] at h1
  linarith


/-! ### The matrices of the vertex check -/

lemma gS_eq (s : ℕ) (a : GI) : gS s a = ((((2 : ℝ) ^ s)⁻¹ : ℝ) : ℂ) * giC a := by
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, gS_re, giC_re, div_eq_inv_mul]
  · rw [Complex.im_ofReal_mul, gS_im, giC_im, div_eq_inv_mul]

lemma tK_herm (E : ℕ) (Y : List GI) (j l : ℕ) : tK E Y j l = (tK E Y l j).conj := by
  unfold tK
  rcases lt_trichotomy j l with h | h | h
  · rw [if_neg h.ne, if_pos h, if_neg h.ne', if_neg (not_lt.2 h.le)]
    cases nth GI.zero Y (l - j - 1)
    simp [GI.conj]
  · subst h; simp [GI.conj]
  · rw [if_neg h.ne', if_neg (not_lt.2 h.le), if_neg h.ne, if_pos h]

lemma tK_succ (E : ℕ) (Y : List GI) (j l : ℕ) : tK E Y (j + 1) (l + 1) = tK E Y j l := by
  unfold tK
  simp only [Nat.add_right_cancel_iff, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]

/-- `T(y)` as a complex matrix (scale `2^128` removed) -/
noncomputable def TcK (n : ℕ) (Y : List GI) : Matrix (Fin n) (Fin n) ℂ := fun j l => gS 128 (tK 128 Y j l)

/-- the hint `W` as a complex matrix (lower triangular part, scale `2^96` removed) -/
noncomputable def WcK (n : ℕ) (Wr : List (List GI)) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if (j : ℕ) ≤ i then gS 96 (nth GI.zero (nth [] Wr i) j) else 0

lemma TcK_herm (n : ℕ) (Y : List GI) : (TcK n Y).IsHermitian := by
  ext j l
  simp only [conjTranspose_apply, TcK]
  rw [tK_herm 128 Y l j]
  apply Complex.ext <;> simp [gS, GI.conj] <;> ring

lemma TcK_toeplitz (k : ℕ) (Y : List GI) : IsToeplitz (TcK (k + 1) Y) := by
  intro j l
  simp only [TcK, Fin.val_succ, Fin.coe_castSucc, tK_succ]

lemma TcK_00 (k : ℕ) (Y : List GI) : TcK (k + 1) Y 0 0 = 1 := by
  apply Complex.ext <;> simp [TcK, tK, gS] <;> norm_num

lemma sum_fin_ite_le {n i : ℕ} (hi : i < n) (g : ℕ → ℂ) :
    ∑ a : Fin n, (if (a : ℕ) ≤ i then g a else 0) = ∑ a : Fin (i + 1), g a := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if a ≤ i then g a else 0) n, Fin.sum_univ_eq_sum_range g (i + 1),
    ← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- the computed lower triangle of `M = W T W*` is the matrix product -/
lemma mEntry_eq {n : ℕ} (Y : List GI) (Wr : List (List GI)) {i j : Fin n} (hji : (j : ℕ) ≤ i) :
    (WcK n Wr * TcK n Y * (WcK n Wr)ᴴ) i j = gS 320 (mEntry 128 Y Wr n i j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, conjTranspose_apply, WcK, TcK]
  have h1 : ∀ b : Fin n, (∑ a : Fin n, (if (a : ℕ) ≤ i then gS 96 (nth GI.zero (nth [] Wr i) a) else 0) *
      gS 128 (tK 128 Y a b)) = ∑ a : Fin (i + 1), gS 96 (nth GI.zero (nth [] Wr i) a) * gS 128 (tK 128 Y a b) := by
    intro b
    refine Eq.trans ?_ (sum_fin_ite_le i.isLt (fun a => gS 96 (nth GI.zero (nth [] Wr i) a) * gS 128 (tK 128 Y a b)))
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
  simp only [h1]
  have h2 : (∑ b : Fin n, (∑ a : Fin (i + 1), gS 96 (nth GI.zero (nth [] Wr i) a) * gS 128 (tK 128 Y a b)) *
      star (if (b : ℕ) ≤ j then gS 96 (nth GI.zero (nth [] Wr j) b) else 0)) =
      ∑ b : Fin (j + 1), (∑ a : Fin (i + 1), gS 96 (nth GI.zero (nth [] Wr i) a) * gS 128 (tK 128 Y a b)) *
        star (gS 96 (nth GI.zero (nth [] Wr j) b)) := by
    refine Eq.trans ?_ (sum_fin_ite_le j.isLt (fun b => (∑ a : Fin (i + 1), gS 96 (nth GI.zero (nth [] Wr i) a) *
      gS 128 (tK 128 Y a b)) * star (gS 96 (nth GI.zero (nth [] Wr j) b))))
    exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp
  rw [h2]
  unfold mEntry
  rw [gS_eq, giC_sumGI]
  simp only [giC_mul, giC_sumGI, giC_conj, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [gS_eq, gS_eq, gS_eq]
  have h320 : ((((2 : ℝ) ^ 320)⁻¹ : ℝ) : ℂ) = ((((2 : ℝ) ^ 96)⁻¹ : ℝ) : ℂ) * ((((2 : ℝ) ^ 128)⁻¹ : ℝ) : ℂ) *
      ((((2 : ℝ) ^ 96)⁻¹ : ℝ) : ℂ) := by
    push_cast; rw [← mul_inv, ← mul_inv, ← pow_add, ← pow_add]
  simp only [h320, star_mul', Complex.star_def, Complex.conj_ofReal, map_mul]
  ring

/-- `domOK` makes `T` positive semidefinite -/
lemma domOK_psd {n : ℕ} {Y : List GI} {Wr : List (List GI)} (h : domOK 128 Y Wr n = true) : (TcK n Y).PosSemidef := by
  unfold domOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  have hMH : (WcK n Wr * TcK n Y * (WcK n Wr)ᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, (TcK_herm n Y).eq,
      Matrix.mul_assoc]
  have hlow : ∀ i j : Fin n, (j : ℕ) ≤ i →
      nth GI.zero (nth [] ((List.range n).map fun i => (List.range (i + 1)).map fun j => mEntry 128 Y Wr n i j) i) j =
        mEntry 128 Y Wr n i j := fun i j hji => by
    rw [nth_range_map _ _ i.isLt, nth_range_map _ _ (Nat.lt_succ_of_le hji)]
  have hnorm : ∀ a : GI, ‖gS 320 a‖ ≤ (a.abs1 : ℝ) / 2 ^ 320 := fun a => by
    rw [gS_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (norm_giC_le a) (by positivity)
  have hdom : ∀ i, ∑ j, (if j = i then 0 else ‖(WcK n Wr * TcK n Y * (WcK n Wr)ᴴ) i j‖) ≤
      ((WcK n Wr * TcK n Y * (WcK n Wr)ᴴ) i i).re := by
    intro i
    obtain ⟨⟨hoff, him⟩, hW⟩ := h i i.isLt
    rw [hlow i i le_rfl] at hoff him
    rw [mEntry_eq Y Wr le_rfl, gS_re]
    have hoff' := (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 320)).2
      (by exact_mod_cast hoff : ((sumInt _ n : ℤ) : ℝ) < ((mEntry 128 Y Wr n i i).re : ℝ))
    refine le_trans ?_ hoff'.le
    rw [cast_sumInt, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hji : j = i
    · subst hji; simp
    · rw [if_neg hji]
      rcases lt_or_gt_of_ne (fun e : (j : ℕ) = i => hji (Fin.ext e)) with hlt | hgt
      · rw [if_pos hlt, hlow i j hlt.le, mEntry_eq Y Wr hlt.le]
        exact hnorm _
      · rw [if_neg (not_lt.2 hgt.le), if_pos hgt, hlow j i hgt.le]
        rw [show (WcK n Wr * TcK n Y * (WcK n Wr)ᴴ) i j = star ((WcK n Wr * TcK n Y * (WcK n Wr)ᴴ) j i) from
          (hMH.apply i j).symm, norm_star, mEntry_eq Y Wr hgt.le]
        exact hnorm _
  have hMpsd := psd_of_dom hMH hdom
  refine psd_of_congr (W := WcK n Wr) (fun i j hij => ?_) (fun i => ?_) hMpsd
  · simp only [WcK]; rw [if_neg (not_le.2 (Fin.lt_def.1 hij))]
  · obtain ⟨_, hW⟩ := h i i.isLt
    simp only [WcK, le_refl, if_true, hW]
    apply Complex.ext <;> simp [gS] <;> norm_num


/-! ### Soundness of the kernel vertex check -/

lemma wVec_get {n : ℕ} (Y x : List GI) {j : ℕ} (hj : j < n) :
    nth GI.zero (wVec 128 Y x n) j = sumGI (fun l => (tK 128 Y j l).mul (nth GI.zero x l)) n := by
  unfold wVec; exact nth_range_map _ _ hj

/-- **Soundness of the exact checks** (any hints `Wr`, `x`). -/
theorem vertex_core_sound {D bnum bden : ℕ} (hbden : 0 < bden) {key : List Comp} (hkey : key.length = D)
    {Y : List GI} {Wr : List (List GI)} {x : List GI} (hdom : domOK 128 Y Wr (D + 1 + 1) = true)
    (hfin : finalK bnum bden (qVal x (wVec 128 Y x (D + 1 + 1)) (D + 1 + 1))
      (errSumK trigTT key (wVec 128 Y x (D + 1 + 1))) = true) :
    VProp (D + 1) ((bnum : ℝ) / bden) (vtx D key) := by
  set n := D + 1 + 1 with hn
  set w := wVec 128 Y x n with hw
  unfold finalK at hfin
  split at hfin
  · exact absurd hfin (by simp)
  rename_i R hR
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfin
  obtain ⟨hRB, hq⟩ := hfin
  -- the matrix and the hint vectors
  set Tc := TcK n Y with hTc
  have hpsd : Tc.PosSemidef := domOK_psd hdom
  have hto : IsToeplitz Tc := TcK_toeplitz (D + 1) Y
  have h00 : Tc 0 0 = 1 := TcK_00 (D + 1) Y
  set xc : Fin n → ℂ := fun l => gS 96 (nth GI.zero x l) with hxc
  set wc : Fin n → ℂ := fun j => gS 224 (nth GI.zero w j) with hwc
  have hwT : wc = Tc *ᵥ xc := by
    funext j
    simp only [hwc, hw, wVec_get Y x j.isLt, mulVec, dotProduct, hTc, TcK, hxc]
    rw [gS_eq, giC_sumGI, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [giC_mul, gS_eq, gS_eq]
    have : ((((2 : ℝ) ^ 224)⁻¹ : ℝ) : ℂ) = ((((2 : ℝ) ^ 128)⁻¹ : ℝ) : ℂ) * ((((2 : ℝ) ^ 96)⁻¹ : ℝ) : ℂ) := by
      push_cast; rw [← mul_inv, ← pow_add]
    rw [this]; ring
  have hqv : ((qVal x w n : ℤ) : ℝ) / 2 ^ 320 = (star xc ⬝ᵥ wc).re := by
    unfold qVal
    rw [cast_sumInt, Finset.sum_div]
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, hxc, hwc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gS_eq, gS_eq, star_mul', Complex.star_def, Complex.conj_ofReal]
    have e : ((((2 : ℝ) ^ 96)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (giC (nth GI.zero x j)) *
        (((((2 : ℝ) ^ 224)⁻¹ : ℝ) : ℂ) * giC (nth GI.zero w j)) =
        ((((2 : ℝ) ^ 320)⁻¹ : ℝ) : ℂ) * giC ((nth GI.zero x j).conj.mul (nth GI.zero w j)) := by
      rw [giC_mul, giC_conj, Complex.star_def]
      have : ((((2 : ℝ) ^ 320)⁻¹ : ℝ) : ℂ) = ((((2 : ℝ) ^ 96)⁻¹ : ℝ) : ℂ) * ((((2 : ℝ) ^ 224)⁻¹ : ℝ) : ℂ) := by
        push_cast; rw [← mul_inv, ← pow_add]
      rw [this]; ring
    rw [e, Complex.re_ofReal_mul, giC_re, inv_mul_eq_div]
  have herr := errSumK_sound hkey hR
  -- the real parameters
  set B : ℝ := (bnum : ℝ) / bden with hB
  set ρ : ℝ := (R : ℝ) / 2 ^ 224 with hρ
  have hb : (0 : ℝ) < bden := by exact_mod_cast hbden
  have p224 : (0 : ℝ) < 2 ^ 224 := by positivity
  have hρB : ρ ≤ B := by
    rw [hρ, hB, div_le_div_iff₀ p224 hb]
    have : ((R * bden : ℤ) : ℝ) ≤ ((bnum * 2 ^ 224 : ℤ) : ℝ) := by exact_mod_cast hRB
    push_cast at this; linarith
  have hqB : (star xc ⬝ᵥ (Tc *ᵥ xc)).re ≤ (B - ρ) ^ 2 := by
    rw [← hwT, ← hqv]
    have h1 : ((qVal x w n * bden ^ 2 * 2 ^ 128 : ℤ) : ℝ) ≤ (((bnum * 2 ^ 224 - R * bden) ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast hq
    push_cast at h1
    have e : (B - ρ) ^ 2 = ((bnum : ℝ) * 2 ^ 224 - R * bden) ^ 2 / ((bden : ℝ) ^ 2 * 2 ^ 448) := by
      rw [hB, hρ]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 : ℝ) ^ 448 = 2 ^ 320 * 2 ^ 128 := by rw [← pow_add]
    rw [this]
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ 320)
    rw [show (2 : ℝ) ^ 224 = 26959946667150639794667015087019630673637144422540572481103610249216 by norm_num,
      show (2 : ℝ) ^ 128 = 340282366920938463463374607431768211456 by norm_num]
    calc ((qVal x w n : ℤ) : ℝ) * ((bden : ℝ) ^ 2 * (2 ^ 320 * 340282366920938463463374607431768211456))
        = ((qVal x w n : ℤ) : ℝ) * (bden : ℝ) ^ 2 * 340282366920938463463374607431768211456 * 2 ^ 320 := by ring
      _ ≤ _ := h2
  -- the bound
  intro c M hM
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 1 (by simp))
  have hcj := norm_coeff_le c hM0 hM
  have hTb := toeplitz_bound_psd Tc hpsd hto c hM0 hM
  rw [h00, Complex.one_re, one_mul] at hTb
  have hcs := psd_cauchy_schwarz hpsd xc c
  have hBρ : 0 ≤ B - ρ := by linarith
  have hcc0 : 0 ≤ (star c ⬝ᵥ (Tc *ᵥ c)).re := (Complex.nonneg_iff.1 (hpsd.dotProduct_mulVec_nonneg c)).1
  have hmain : ‖star xc ⬝ᵥ (Tc *ᵥ c)‖ ≤ (B - ρ) * M := by
    have h2 : ‖star xc ⬝ᵥ (Tc *ᵥ c)‖ ^ 2 ≤ ((B - ρ) * M) ^ 2 := by
      calc ‖star xc ⬝ᵥ (Tc *ᵥ c)‖ ^ 2 ≤ (star xc ⬝ᵥ (Tc *ᵥ xc)).re * (star c ⬝ᵥ (Tc *ᵥ c)).re := hcs
        _ ≤ (B - ρ) ^ 2 * M ^ 2 := mul_le_mul hqB hTb hcc0 (sq_nonneg _)
        _ = ((B - ρ) * M) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hBρ hM0) two_ne_zero).1 h2
  have hswap : star wc ⬝ᵥ c = star xc ⬝ᵥ (Tc *ᵥ c) := by
    rw [hwT, star_mulVec, hpsd.isHermitian.eq, ← dotProduct_mulVec]
  have hsplit : (∑ j, star (vtx D key j) * c j) = star wc ⬝ᵥ c + star (vtx D key - wc) ⬝ᵥ c := by
    rw [← add_dotProduct, ← star_add, add_sub_cancel]
    rfl
  have herr2 : ‖star (vtx D key - wc) ⬝ᵥ c‖ ≤ ρ * M := by
    calc ‖star (vtx D key - wc) ⬝ᵥ c‖ ≤ ∑ j, ‖star (vtx D key - wc) j * c j‖ := norm_sum_le _ _
      _ = ∑ j, ‖vtx D key j - wc j‖ * ‖c j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Pi.star_apply, norm_star, Pi.sub_apply]
      _ ≤ ∑ j, ‖vtx D key j - wc j‖ * M :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcj j) (norm_nonneg _)
      _ = (∑ j, ‖vtx D key j - wc j‖) * M := by rw [Finset.sum_mul]
      _ ≤ ρ * M := mul_le_mul_of_nonneg_right herr hM0
  rw [hsplit, Complex.add_re, hswap]
  have r1 := Complex.re_le_norm (star xc ⬝ᵥ (Tc *ᵥ c))
  have r2 := Complex.re_le_norm (star (vtx D key - wc) ⬝ᵥ c)
  nlinarith



/-- **Soundness of the kernel vertex check** (in-kernel hints). -/
theorem vertexOKK_sound {D bnum bden : ℕ} (hbden : 0 < bden) {key : List Comp} {Y : List GI}
    (h : vertexOKK trigTT (D + 1) bnum bden key Y = true) : VProp (D + 1) ((bnum : ℝ) / bden) (vtx D key) := by
  unfold vertexOKK at h
  dsimp only at h
  split_ifs at h with hlen
  simp only [Bool.and_eq_true] at h
  exact vertex_core_sound hbden (by omega) h.1 h.2

/-- **Soundness of the kernel vertex check** (hints given as data). -/
theorem vertexOKKh_sound {D bnum bden : ℕ} (hbden : 0 < bden) {key : List Comp} {Y : List GI}
    {Wr : List (List GI)} {x : List GI} (h : vertexOKKh trigTT (D + 1) bnum bden key Y Wr x = true) :
    VProp (D + 1) ((bnum : ℝ) / bden) (vtx D key) := by
  unfold vertexOKKh at h
  dsimp only at h
  split_ifs at h with hlen
  simp only [Bool.and_eq_true] at h
  exact vertex_core_sound hbden (by omega) h.1 h.2

/-! ### The kernel walk -/

lemma allP_iff {α : Type} {P : α → Prop} : ∀ (l : List α), allP P l ↔ ∀ x ∈ l, P x
  | [] => by simp [allP]
  | a :: l => by simp [allP, allP_iff l]

lemma product_mem : ∀ (os : List (List Comp)) (cs : List Comp), List.Forall₂ (fun c o => c ∈ o) cs os →
    cs ∈ product os
  | [], cs, h => by rw [List.forall₂_nil_right_iff] at h; subst h; simp [product]
  | o :: os, cs, h => by
    cases h with
    | cons hc hcs =>
      rename_i c cs'
      simp only [product, List.mem_flatMap, List.mem_map]
      exact ⟨c, hc, cs', product_mem os cs' hcs, rfl⟩

lemma allVerts_of_forall (f : List Comp → Bool) : ∀ (os : List (List Comp)) (acc : List Comp),
    (∀ cs, List.Forall₂ (fun c o => c ∈ o) cs os → f (acc.reverse ++ cs) = true) → allVerts f os acc = true
  | [], acc, h => by simpa [allVerts] using h [] List.Forall₂.nil
  | o :: os, acc, h => by
    unfold allVerts
    rw [List.all_eq_true]
    intro c hc
    refine allVerts_of_forall f os (c :: acc) fun cs hcs => ?_
    have := h (c :: cs) (List.Forall₂.cons hc hcs)
    simpa [List.reverse_cons, List.append_assoc] using this

lemma leafK_suffix {ms : List ℤ} {js : List ℕ} {kl rest : List (List Comp)} (h : leafK ms js kl = some rest) :
    ∃ pre, kl = pre ++ rest := by
  unfold leafK at h
  split_ifs at h with h1
  try dsimp only at h
  split_ifs at h with h2
  simp only [Option.some.injEq] at h
  exact ⟨_, by rw [← h, List.take_append_drop]⟩

lemma walkK_suffix : ∀ (t : Tree) (ms : List ℤ) (js : List ℕ) (kl rest : List (List Comp)),
    walkK t ms js kl = some rest → ∃ pre, kl = pre ++ rest
  | .leaf, ms, js, kl, rest, h => leafK_suffix h
  | .split d lo hi, ms, js, kl, rest, h => by
    unfold walkK at h
    split_ifs at h with hc
    split at h
    · exact absurd h (by simp)
    rename_i kl' hlo
    obtain ⟨p1, e1⟩ := walkK_suffix lo _ _ kl kl' hlo
    obtain ⟨p2, e2⟩ := walkK_suffix hi _ _ kl' rest h
    exact ⟨p1 ++ p2, by rw [e1, e2, List.append_assoc]⟩

/-- the two children of a split cover the box -/
lemma split_child {D : ℕ} {ms : List ℤ} {js : List ℕ} {d : ℕ} (hdD : d < D) (hd1 : d < ms.length)
    (hd2 : d < js.length) (hj8 : js.getD d default ≤ 8) {φ : Fin D → ℝ} (hφ : InBox D ms js φ) :
    InBox D (ms.set d (ms.getD d default - 2 ^ (8 - js.getD d default))) (js.set d (js.getD d default + 1)) φ ∨
    InBox D (ms.set d (ms.getD d default + 2 ^ (8 - js.getD d default))) (js.set d (js.getD d default + 1)) φ := by
  set j := js.getD d default with hjdef
  set m := ms.getD d default with hmdef
  have hφd := hφ ⟨d, hdD⟩
  simp only [] at hφd
  have hdef : (default : ℤ) = 0 := rfl
  have hdefn : (default : ℕ) = 0 := rfl
  rw [← hdef, ← hdefn] at hφd
  have h2 : ((2 : ℝ) ^ (8 - j)) / 512 = 1 / 2 ^ (j + 1) := by
    rw [show (512 : ℝ) = 2 ^ (8 - j) * 2 ^ (j + 1) by
      rw [← pow_add, show 8 - j + (j + 1) = 9 by omega]; norm_num]
    field_simp
  have hhalf : (1 : ℝ) / 2 ^ j = 2 * (1 / 2 ^ (j + 1)) := by rw [pow_succ]; field_simp
  have child : ∀ (σ : ℤ), (σ = -1 ∨ σ = 1) → (σ * (φ ⟨d, hdD⟩ - m / 512) ≥ 0) →
      InBox D (ms.set d (m + σ * 2 ^ (8 - j))) (js.set d (j + 1)) φ := by
    intro σ hσ hside e
    by_cases hed : e.val = d
    · have he : e = ⟨d, hdD⟩ := Fin.ext hed
      subst he
      simp only []
      rw [getD_set_eq _ _ _ _ hd1, getD_set_eq _ _ _ _ hd2]
      push_cast
      rw [show ((m : ℝ) + σ * 2 ^ (8 - j)) / 512 = m / 512 + σ * (2 ^ (8 - j) / 512) by ring, h2]
      rw [hhalf] at hφd
      rcases hσ with rfl | rfl
      · push_cast at hside ⊢
        rw [abs_le] at hφd ⊢
        constructor <;> nlinarith
      · push_cast at hside ⊢
        rw [abs_le] at hφd ⊢
        constructor <;> nlinarith
    · rw [getD_set_ne _ _ _ (Ne.symm hed), getD_set_ne _ _ _ (Ne.symm hed)]
      exact hφ e
  by_cases hs : φ ⟨d, hdD⟩ ≤ m / 512
  · left
    have hb := child (-1) (Or.inl rfl) (by push_cast; linarith)
    have e : m + (-1 : ℤ) * 2 ^ (8 - j) = m - 2 ^ (8 - j) := by ring
    rwa [e] at hb
  · right
    have hb := child 1 (Or.inr rfl) (by push_cast; linarith)
    have e : m + (1 : ℤ) * 2 ^ (8 - j) = m + 2 ^ (8 - j) := by ring
    rwa [e] at hb

/-- **Soundness of the kernel walk**: if every key of the stream has the vertex property, so does every phase vector in
the box. -/
theorem walkK_sound {D : ℕ} {B : ℝ} {P : List Comp → Prop} (hP : ∀ key, P key → VProp (D + 1) B (vtx D key)) :
    ∀ (t : Tree) (ms : List ℤ) (js : List ℕ) (kl rest : List (List Comp)), ms.length = D → js.length = D →
      walkK t ms js kl = some rest → allP P kl → ∀ φ, InBox D ms js φ → VProp (D + 1) B (wPhase D φ)
  | .leaf, ms, js, kl, rest, hms, hjs, h, hkl, φ, hφ => by
    unfold walkK at h
    unfold leafK at h
    split_ifs at h with hc
    try dsimp only at h
    split_ifs at h with ht
    simp only [Option.some.injEq] at h
    obtain ⟨hlen, hjall⟩ := hc
    set keys := product (List.zipWith opts ms js) with hkeys
    refine leaf_sound (f := fun key => decide (key ∈ keys)) (fun key hk => ?_) hms ?_ hφ
    · have hmem : key ∈ keys := by simpa using hk
      rw [← ht] at hmem
      exact hP key ((allP_iff kl).1 hkl key (List.mem_of_mem_take hmem))
    · unfold leafOK
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨hlen, hjall⟩, allVerts_of_forall _ _ [] fun cs hcs => ?_⟩
      simp only [List.reverse_nil, List.nil_append, decide_eq_true_eq, hkeys]
      exact product_mem _ cs hcs
  | .split d lo hi, ms, js, kl, rest, hms, hjs, h, hkl, φ, hφ => by
    unfold walkK at h
    split_ifs at h with hc
    obtain ⟨hd1, hd2, hj8⟩ := hc
    split at h
    · exact absurd h (by simp)
    rename_i kl' hlo
    rw [getElem!_eq_getD', getElem!_eq_getD'] at hlo h
    rw [getElem!_eq_getD'] at hj8
    have hdD : d < D := by omega
    obtain ⟨p1, e1⟩ := walkK_suffix lo _ _ kl kl' hlo
    have hkl' : allP P kl' := by
      rw [allP_iff] at hkl ⊢
      exact fun x hx => hkl x (by rw [e1]; exact List.mem_append_right _ hx)
    rcases split_child hdD hd1 hd2 hj8 hφ with hb | hb
    · exact walkK_sound hP lo _ _ kl kl' (by simp [hms]) (by simp [hjs]) hlo hkl φ hb
    · exact walkK_sound hP hi _ _ kl' rest (by simp [hms]) (by simp [hjs]) h hkl' φ hb


/-- **A root cell from its kernel checks**: the walk theorem and the linked vertex theorems give the cell property. -/
theorem cellOK_of_K {D k bnum bden : ℕ} (hk : k = D + 1) (hbden : 0 < bden) {i : ℕ} {t : Tree}
    {kl : List (List Comp)} (hw : walkK t (rootMs D i) (List.replicate D 3) kl = some [])
    (hv : allP (fun key => ∃ Y, vertexOKK trigTT k bnum bden key Y = true) kl) :
    CellOK D ((bnum : ℝ) / bden) i := by
  subst hk
  intro φ hφ
  exact walkK_sound (fun key ⟨_, hY⟩ => vertexOKK_sound hbden hY) t _ _ kl [] (by simp [rootMs, length_digits8])
    (by simp) hw hv φ hφ


/-- **A root cell from its kernel checks**, hints given as data. -/
theorem cellOK_of_Kh {D k bnum bden : ℕ} (hk : k = D + 1) (hbden : 0 < bden) {i : ℕ} {t : Tree}
    {kl : List (List Comp)} (hw : walkK t (rootMs D i) (List.replicate D 3) kl = some [])
    (hv : allP (fun key => ∃ Y Wr x, vertexOKKh trigTT k bnum bden key Y Wr x = true) kl) :
    CellOK D ((bnum : ℝ) / bden) i := by
  subst hk
  intro φ hφ
  exact walkK_sound (fun key ⟨_, _, _, hY⟩ => vertexOKKh_sound hbden hY) t _ _ kl [] (by simp [rootMs, length_digits8])
    (by simp) hw hv φ hφ


/-- `allP` of a concatenation (for chunked key lists) -/
lemma allP_append {α : Type} {P : α → Prop} : ∀ {l₁ l₂ : List α}, allP P l₁ → allP P l₂ → allP P (l₁ ++ l₂)
  | [], _, _, h₂ => h₂
  | _ :: l, _, h₁, h₂ => ⟨h₁.1, allP_append (l₁ := l) h₁.2 h₂⟩


/-! ### The kernel walk with per-leaf key lists -/

lemma walkK2_suffix : ∀ (t : Tree) (ms : List ℤ) (js : List ℕ) (kls rest : List (List (List Comp))),
    walkK2 t ms js kls = some rest → ∃ pre, kls = pre ++ rest
  | .leaf, ms, js, kls, rest, h => by
    unfold walkK2 at h
    cases kls with
    | nil => exact absurd h (by simp [leafK2])
    | cons kl rest' =>
      dsimp only [leafK2] at h
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      exact ⟨[kl], by rw [← h]; rfl⟩
  | .split d lo hi, ms, js, kls, rest, h => by
    unfold walkK2 at h
    split_ifs at h with hc
    split at h
    · exact absurd h (by simp)
    rename_i kls' hlo
    obtain ⟨p1, e1⟩ := walkK2_suffix lo _ _ kls kls' hlo
    obtain ⟨p2, e2⟩ := walkK2_suffix hi _ _ kls' rest h
    exact ⟨p1 ++ p2, by rw [e1, e2, List.append_assoc]⟩

/-- **Soundness of the per-leaf kernel walk.** -/
theorem walkK2_sound {D : ℕ} {B : ℝ} {P : List Comp → Prop} (hP : ∀ key, P key → VProp (D + 1) B (vtx D key)) :
    ∀ (t : Tree) (ms : List ℤ) (js : List ℕ) (kls rest : List (List (List Comp))), ms.length = D → js.length = D →
      walkK2 t ms js kls = some rest → allP (allP P) kls → ∀ φ, InBox D ms js φ → VProp (D + 1) B (wPhase D φ)
  | .leaf, ms, js, kls, rest, hms, hjs, h, hkl, φ, hφ => by
    unfold walkK2 at h
    cases kls with
    | nil => exact absurd h (by simp [leafK2])
    | cons kl rest' =>
      dsimp only [leafK2] at h
      split_ifs at h with hc
      obtain ⟨hlen, hjall, hkeq⟩ := hc
      have hkl1 : allP P kl := hkl.1
      set keys := product (List.zipWith opts ms js) with hkeys
      refine leaf_sound (f := fun key => decide (key ∈ keys)) (fun key hk => ?_) hms ?_ hφ
      · have hmem : key ∈ keys := by simpa using hk
        rw [← hkeq] at hmem
        exact hP key ((allP_iff kl).1 hkl1 key hmem)
      · unfold leafOK
        simp only [Bool.and_eq_true, beq_iff_eq]
        refine ⟨⟨hlen, hjall⟩, allVerts_of_forall _ _ [] fun cs hcs => ?_⟩
        simp only [List.reverse_nil, List.nil_append, decide_eq_true_eq, hkeys]
        exact product_mem _ cs hcs
  | .split d lo hi, ms, js, kls, rest, hms, hjs, h, hkl, φ, hφ => by
    unfold walkK2 at h
    split_ifs at h with hc
    obtain ⟨hd1, hd2, hj8⟩ := hc
    split at h
    · exact absurd h (by simp)
    rename_i kls' hlo
    rw [getElem!_eq_getD', getElem!_eq_getD'] at hlo h
    rw [getElem!_eq_getD'] at hj8
    have hdD : d < D := by omega
    obtain ⟨p1, e1⟩ := walkK2_suffix lo _ _ kls kls' hlo
    have hkl' : allP (allP P) kls' := by
      rw [allP_iff] at hkl ⊢
      exact fun x hx => hkl x (by rw [e1]; exact List.mem_append_right _ hx)
    rcases split_child hdD hd1 hd2 hj8 hφ with hb | hb
    · exact walkK2_sound hP lo _ _ kls kls' (by simp [hms]) (by simp [hjs]) hlo hkl φ hb
    · exact walkK2_sound hP hi _ _ kls' rest (by simp [hms]) (by simp [hjs]) h hkl' φ hb

/-- **A root cell from its kernel checks** (per-leaf key lists, kernel-computed hints). -/
theorem cellOK_of_K2 {D k bnum bden : ℕ} (hk : k = D + 1) (hbden : 0 < bden) {i : ℕ} {t : Tree}
    {kls : List (List (List Comp))} (hw : walkK2 t (rootMs D i) (List.replicate D 3) kls = some [])
    (hv : allP (allP (fun key => ∃ Y, vertexOKK trigTT k bnum bden key Y = true)) kls) :
    CellOK D ((bnum : ℝ) / bden) i := by
  subst hk
  intro φ hφ
  exact walkK2_sound (fun key ⟨_, hY⟩ => vertexOKK_sound hbden hY) t _ _ kls [] (by simp [rootMs, length_digits8])
    (by simp) hw hv φ hφ

/-- **A root cell from its kernel checks** (per-leaf key lists, hints given as data). -/
theorem cellOK_of_K2h {D k bnum bden : ℕ} (hk : k = D + 1) (hbden : 0 < bden) {i : ℕ} {t : Tree}
    {kls : List (List (List Comp))} (hw : walkK2 t (rootMs D i) (List.replicate D 3) kls = some [])
    (hv : allP (allP (fun key => ∃ Y Wr x, vertexOKKh trigTT k bnum bden key Y Wr x = true)) kls) :
    CellOK D ((bnum : ℝ) / bden) i := by
  subst hk
  intro φ hφ
  exact walkK2_sound (fun key ⟨_, _, _, hY⟩ => vertexOKKh_sound hbden hY) t _ _ kls []
    (by simp [rootMs, length_digits8]) (by simp) hw hv φ hφ

end Bohr59a.CertK
