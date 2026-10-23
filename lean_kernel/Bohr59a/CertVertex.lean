/-
Soundness of the vertex check of `Bohr59aCore/Check.lean`: if `vertexOK k B key y` then
`Re Σ_j conj(v_j) c_j ≤ B · max_T |Σ_j c_j z^j|` for the vertex `v = (1, 1, coord key_0, …, coord key_{D-1})`.
-/
import Bohr59aCore.Check
import C64.Ival.SoundTrig
import Bohr59a.Toeplitz
import Bohr59a.Newman

open Complex Matrix Finset Real
open scoped ComplexOrder

namespace Bohr59a.Cert

open Bohr59aCore

/-! ### Complex rationals -/

/-- the complex number of a complex rational -/
def toC (a : CQ) : ℂ := ⟨(a.re : ℝ), (a.im : ℝ)⟩

@[simp] lemma toC_re (a : CQ) : (toC a).re = a.re := rfl
@[simp] lemma toC_im (a : CQ) : (toC a).im = a.im := rfl

lemma toC_add (a b : CQ) : toC (a.add b) = toC a + toC b := by
  apply Complex.ext <;> simp [CQ.add]

lemma toC_sub (a b : CQ) : toC (a.sub b) = toC a - toC b := by
  apply Complex.ext <;> simp [CQ.sub]

lemma toC_mul (a b : CQ) : toC (a.mul b) = toC a * toC b := by
  apply Complex.ext <;> simp [CQ.mul, Complex.mul_re, Complex.mul_im]

lemma toC_conj (a : CQ) : toC a.conj = star (toC a) := by
  apply Complex.ext <;> simp [CQ.conj]

lemma toC_smul (r : ℚ) (a : CQ) : toC (a.smul r) = ((r : ℝ) : ℂ) * toC a := by
  apply Complex.ext <;> simp [CQ.smul, Complex.mul_re, Complex.mul_im]

@[simp] lemma toC_zero : toC CQ.zero = 0 := by apply Complex.ext <;> simp [CQ.zero]

@[simp] lemma toC_one : toC CQ.one = 1 := by apply Complex.ext <;> simp [CQ.one]

lemma sumN_succ (n : ℕ) (f : ℕ → CQ) : sumN (n + 1) f = (sumN n f).add (f n) := by
  simp [sumN, List.range_succ, List.foldl_append]

lemma toC_sumN (n : ℕ) (f : ℕ → CQ) : toC (sumN n f) = ∑ p : Fin n, toC (f p) := by
  rw [← Finset.sum_range (fun p => toC (f p))]
  induction n with
  | zero => simp [sumN]
  | succ n ih => rw [sumN_succ, toC_add, ih, Finset.sum_range_succ]

lemma rabs_eq (r : ℚ) : rabs r = |r| := by
  unfold rabs
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.1 h)).symm

/-! ### The Toeplitz matrix of a certificate -/

/-- the complex matrix of `t` -/
def matC (n : ℕ) (t : ℕ → ℕ → CQ) : Matrix (Fin n) (Fin n) ℂ := fun j l => toC (t j l)

/-- the complex vector of an array -/
def vecC (n : ℕ) (x : Array CQ) : Fin n → ℂ := fun j => toC x[j.val]!

lemma tmat_herm (y : Array CQ) (j l : ℕ) : tmat y j l = (tmat y l j).conj := by
  unfold tmat
  rcases lt_trichotomy j l with h | h | h
  · rw [if_neg h.ne, if_pos h, if_neg h.ne', if_neg (not_lt.2 h.le)]
    cases y[l - j - 1]!
    simp [CQ.conj]
  · subst h
    simp [CQ.one, CQ.conj]
  · rw [if_neg h.ne', if_neg (not_lt.2 h.le), if_neg h.ne, if_pos h]

lemma tmat_succ (y : Array CQ) (j l : ℕ) : tmat y (j + 1) (l + 1) = tmat y j l := by
  unfold tmat
  simp only [Nat.add_right_cancel_iff, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]

lemma matC_toeplitz (k : ℕ) (y : Array CQ) : IsToeplitz (matC (k + 1) (tmat y)) := by
  intro j l
  simp only [matC, Fin.val_succ, Fin.coe_castSucc, tmat_succ]

lemma matC_00 (k : ℕ) (y : Array CQ) : matC (k + 1) (tmat y) 0 0 = 1 := by
  simp [matC, tmat]

/-- `ldlOK` gives a positive semidefinite matrix -/
lemma ldlOK_psd {n : ℕ} {t : ℕ → ℕ → CQ} (hH : ∀ j l, t j l = (t l j).conj) {L : Array CQ} {D : Array ℚ}
    (h : ldlOK n t L D = true) : (matC n t).PosSemidef := by
  unfold ldlOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hD, hT⟩ := h
  set Lc : Matrix (Fin n) (Fin n) ℂ := fun j p => toC L[j.val * n + p.val]! with hLc
  set Dc : Fin n → ℂ := fun p => ((D[p.val]! : ℝ) : ℂ) with hDc
  have hDpsd : (diagonal Dc).PosSemidef :=
    PosSemidef.diagonal fun p => Complex.zero_le_real.2 (by exact_mod_cast hD p.val p.isLt)
  have hprod : ∀ j l : Fin n, (Lc * diagonal Dc * Lcᴴ) j l =
      toC (sumN n (fun p => (L[j.val * n + p]!.mul (L[l.val * n + p]!.conj)).smul D[p]!)) := by
    intro j l
    rw [toC_sumN, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_diagonal, conjTranspose_apply, toC_smul, toC_mul, toC_conj]
    simp only [hLc, hDc]
    ring
  have heq : matC n t = Lc * diagonal Dc * Lcᴴ := by
    ext j l
    rcases le_or_gt l.val j.val with hlj | hjl
    · rw [hprod, hT j.val j.isLt l.val (Nat.lt_succ_of_le hlj)]
      rfl
    · have h1 : (Lc * diagonal Dc * Lcᴴ) j l = star ((Lc * diagonal Dc * Lcᴴ) l j) := by
        have hh : (Lc * diagonal Dc * Lcᴴ).IsHermitian := (hDpsd.mul_mul_conjTranspose_same Lc).isHermitian
        exact (hh.apply j l).symm
      rw [h1, hprod, hT l.val l.isLt j.val (Nat.lt_succ_of_le hjl.le)]
      simp only [matC]
      rw [hH, toC_conj]
  rw [heq]
  exact hDpsd.mul_mul_conjTranspose_same Lc

/-! ### Cauchy–Schwarz for positive semidefinite matrices -/

lemma psd_cauchy_schwarz {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (x y : Fin n → ℂ) :
    ‖star x ⬝ᵥ (A *ᵥ y)‖ ^ 2 ≤ (star x ⬝ᵥ (A *ᵥ x)).re * (star y ⬝ᵥ (A *ᵥ y)).re := by
  set z := star x ⬝ᵥ (A *ᵥ y) with hz
  set Qx := star x ⬝ᵥ (A *ᵥ x) with hQx
  set Qy := star y ⬝ᵥ (A *ᵥ y) with hQy
  have hyx : star y ⬝ᵥ (A *ᵥ x) = star z := (hA.isHermitian.star_dotProduct_mulVec_comm x y).symm
  have hb0 : 0 ≤ Qy.re := (Complex.nonneg_iff.1 (hA.dotProduct_mulVec_nonneg y)).1
  have hzz : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; ring
  have hzz' : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [mul_comm]; exact hzz
  -- `0 ≤ (x - t z̄ y)* A (x - t z̄ y) = Qx - 2 t |z|² + t² |z|² Qy`
  have key : ∀ t : ℝ, 0 ≤ Qx.re - 2 * t * ‖z‖ ^ 2 + t ^ 2 * ‖z‖ ^ 2 * Qy.re := by
    intro t
    set s : ℂ := (t : ℂ) * star z with hs
    have hst : star s = (t : ℂ) * z := by
      rw [hs, star_mul', star_star, Complex.star_def, Complex.conj_ofReal]
    have h := (Complex.nonneg_iff.1 (hA.dotProduct_mulVec_nonneg (x - s • y))).1
    have e : star (x - s • y) ⬝ᵥ (A *ᵥ (x - s • y)) = Qx - s * z - star s * star y ⬝ᵥ (A *ᵥ x)
        + star s * (s * Qy) := by
      simp only [star_sub, star_smul, mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      rw [← hz, ← hQx, ← hQy]
      ring
    have e1 : s * z = ((t * ‖z‖ ^ 2 : ℝ) : ℂ) := by rw [hs, mul_assoc, hzz']; push_cast; ring
    have e2 : star s * star y ⬝ᵥ (A *ᵥ x) = ((t * ‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [hyx, hst, mul_assoc, hzz]; push_cast; ring
    have e3 : star s * (s * Qy) = ((t ^ 2 * ‖z‖ ^ 2 : ℝ) : ℂ) * Qy := by
      rw [hst, hs, show (t : ℂ) * z * ((t : ℂ) * star z * Qy) = (t : ℂ) ^ 2 * (z * star z) * Qy by ring, hzz]
      push_cast; ring
    rw [e, e1, e2, e3] at h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul] at h
    linarith
  rcases hb0.lt_or_eq with hb | hb
  · have := key (1 / Qy.re)
    have e : Qx.re - 2 * (1 / Qy.re) * ‖z‖ ^ 2 + (1 / Qy.re) ^ 2 * ‖z‖ ^ 2 * Qy.re = Qx.re - ‖z‖ ^ 2 / Qy.re := by
      field_simp; ring
    rw [e] at this
    have : ‖z‖ ^ 2 / Qy.re ≤ Qx.re := by linarith
    rw [div_le_iff₀ hb] at this
    linarith
  · rw [← hb, mul_zero]
    by_contra hcon
    have hz2 : 0 < ‖z‖ ^ 2 := lt_of_not_ge hcon
    have := key ((Qx.re + 1) / (2 * ‖z‖ ^ 2))
    rw [← hb] at this
    have hz0 : ‖z‖ ^ 2 ≠ 0 := hz2.ne'
    have hz0' : ‖z‖ ≠ 0 := fun h0 => hz0 (by rw [h0]; ring)
    have e : Qx.re - 2 * ((Qx.re + 1) / (2 * ‖z‖ ^ 2)) * ‖z‖ ^ 2 + ((Qx.re + 1) / (2 * ‖z‖ ^ 2)) ^ 2 * ‖z‖ ^ 2 * 0
        = -1 := by
      rw [mul_zero, add_zero]
      field_simp
      ring
    linarith

/-! ### The vertex vector and the ball enclosures -/

/-- the vertex coordinate of a key component -/
noncomputable def coordC (c : Comp) : ℂ :=
  if c.tan then cexp (((π * c.m / 512 : ℝ) : ℂ) * I) / ((Real.cos (π / 2 ^ c.j) : ℝ) : ℂ)
  else cexp (((π * c.m / 512 : ℝ) : ℂ) * I)

/-- the vertex `(1, 1, coord key_0, …, coord key_{D-1})` -/
noncomputable def vtx (D : ℕ) (key : List Comp) : Fin (D + 1 + 1) → ℂ :=
  Fin.cons 1 (Fin.cons 1 fun d : Fin D => coordC (key.getD d.val default))

lemma ballC_cast (b : Ival.Ball) : ((ballC b : ℚ) : ℝ) = (b.m : ℝ) / 2 ^ P := by
  unfold ballC
  rw [Rat.cast_mkRat_of_ne_zero _ (by positivity)]
  push_cast; ring

lemma ballR_cast (b : Ival.Ball) : ((ballR b : ℚ) : ℝ) = (b.r : ℝ) / 2 ^ P := by
  unfold ballR
  rw [Rat.cast_mkRat_of_ne_zero _ (by positivity)]
  push_cast; ring

lemma mem_ball_abs {x : ℝ} {b : Ival.Ball} (h : Ival.Ball.mem P x b) :
    |x - ((ballC b : ℚ) : ℝ)| ≤ ((ballR b : ℚ) : ℝ) := by
  rw [ballC_cast, ballR_cast]; exact h

lemma trigTab_get {i : ℕ} (hi : i < 1025) :
    trigTab[i]! = Ival.Ball.cosSinTurn P nT kT (Ival.Ball.ofRat P ((i : ℤ) - 512) 1024) := by
  unfold trigTab
  rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

lemma cosTab_get {j : ℕ} (hj : j < 16) :
    cosTab[j]! = Ival.Ball.cosSinTurn P nT kT (Ival.Ball.ofRat P 1 (2 ^ (j + 1))) := by
  unfold cosTab
  rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_ofFn]

/-- the trigonometric balls of `π m/512` -/
lemma trig_mem {m : ℤ} (hm1 : -512 ≤ m) (hm2 : m ≤ 512) {C S : Ival.Ball}
    (h : trigTab[(m + 512).toNat]! = some (C, S)) :
    Ival.Ball.mem P (Real.cos (π * m / 512)) C ∧ Ival.Ball.mem P (Real.sin (π * m / 512)) S := by
  have hi : (m + 512).toNat < 1025 := by omega
  rw [trigTab_get hi] at h
  have hU := Ival.Ball.mem_ofRat P (((m + 512).toNat : ℤ) - 512) 1024 (by norm_num)
  have h2 := Ival.Ball.mem_cosSinTurn hU h
  have e : 2 * π * ((((((m + 512).toNat : ℤ) - 512 : ℤ)) : ℝ) / ((1024 : ℕ) : ℝ)) = π * m / 512 := by
    have : (((m + 512).toNat : ℤ) - 512 : ℤ) = m := by omega
    rw [this]; push_cast; ring
  rwa [e] at h2

/-- the ball of `cos(π/2^j)` -/
lemma cos_mem {j : ℕ} (hj : j < 16) {H S : Ival.Ball} (h : cosTab[j]! = some (H, S)) :
    Ival.Ball.mem P (Real.cos (π / 2 ^ j)) H := by
  rw [cosTab_get hj] at h
  have hU := Ival.Ball.mem_ofRat P 1 (2 ^ (j + 1)) (by positivity)
  have h2 := (Ival.Ball.mem_cosSinTurn hU h).1
  have e : 2 * π * (((1 : ℤ) : ℝ) / (((2 ^ (j + 1) : ℕ)) : ℝ)) = π / 2 ^ j := by
    push_cast; rw [pow_succ]; field_simp
  rwa [e] at h2

/-- `coordErr` bounds the distance from the vertex coordinate -/
lemma coordErr_sound {c : Comp} {w : CQ} {e : ℚ} (h : coordErr c w = some e) :
    ‖coordC c - toC w‖ ≤ (e : ℝ) := by
  unfold coordErr at h
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
  rename_i C S hCS
  obtain ⟨hC, hS⟩ := trig_mem hm1 hm2 hCS
  have hC' := mem_ball_abs hC
  have hS' := mem_ball_abs hS
  dsimp only at h
  by_cases htan : c.tan = true
  · -- tangent
    rw [htan] at h
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hj : 16 ≤ c.j
    · rw [if_pos hj] at h; exact absurd h (by simp)
    rw [if_neg hj] at h
    split at h
    · exact absurd h (by simp)
    rename_i H S2 hHS
    try dsimp only at h
    by_cases hpos' : ballC H - ballR H ≤ 0
    · rw [if_pos hpos'] at h; exact absurd h (by simp)
    rw [if_neg hpos'] at h
    simp only [Option.some.injEq] at h
    subst h
    have htan' : c.tan = true := htan
    have hj16 : c.j < 16 := by omega
    have hH := mem_ball_abs (cos_mem hj16 hHS)
    set hc := ((ballC H : ℚ) : ℝ) with hhc
    set hr := ((ballR H : ℚ) : ℝ) with hhr
    have hpos2 : 0 < hc - hr := by
      have h0 : (0 : ℚ) < ballC H - ballR H := by
        simp only [not_le] at hpos'; linarith
      have := (Rat.cast_pos (K := ℝ)).2 h0
      push_cast at this; exact this
    set ch := Real.cos (π / 2 ^ c.j) with hch_def
    have hch : hc - hr ≤ ch := by
      have := (abs_le.1 hH).1; linarith
    have hch0 : 0 < ch := lt_of_lt_of_le hpos2 hch
    have hc' : coordC c = cexp ((θ : ℂ) * I) / (ch : ℂ) := by
      unfold coordC; rw [if_pos htan']
    rw [hc', hexp]
    have hch0' : (ch : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hch0.ne'
    have hsplit : (⟨Real.cos θ, Real.sin θ⟩ : ℂ) / (ch : ℂ) - toC w =
        ((⟨Real.cos θ, Real.sin θ⟩ : ℂ) - toC w * (ch : ℂ)) / (ch : ℂ) := by
      field_simp
    rw [hsplit, norm_div, Complex.norm_real, Real.norm_of_nonneg hch0.le, div_le_iff₀ hch0]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, toC_re, toC_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero, zero_add]
    push_cast [rabs_eq]
    set X := |((ballC C : ℚ) : ℝ) - w.re * hc| + ((ballR C : ℚ) : ℝ) + |(w.re : ℝ)| * hr +
      (|((ballC S : ℚ) : ℝ) - w.im * hc| + ((ballR S : ℚ) : ℝ) + |(w.im : ℝ)| * hr) with hX_def
    have hhr : |hc - ch| ≤ hr := by rw [abs_sub_comm]; exact hH
    have hr0 : 0 ≤ hr := le_trans (abs_nonneg _) hhr
    have hX : 0 ≤ X := by
      have : 0 ≤ ((ballR C : ℚ) : ℝ) := le_trans (abs_nonneg _) hC'
      have : 0 ≤ ((ballR S : ℚ) : ℝ) := le_trans (abs_nonneg _) hS'
      positivity
    have h1 : |Real.cos θ - w.re * ch| ≤ |((ballC C : ℚ) : ℝ) - w.re * hc| + ((ballR C : ℚ) : ℝ) +
        |(w.re : ℝ)| * hr := by
      have e : Real.cos θ - w.re * ch = (Real.cos θ - ((ballC C : ℚ) : ℝ)) + (((ballC C : ℚ) : ℝ) - w.re * hc)
          + w.re * (hc - ch) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have := abs_add_le (Real.cos θ - ((ballC C : ℚ) : ℝ)) (((ballC C : ℚ) : ℝ) - w.re * hc)
      nlinarith [abs_nonneg (w.re : ℝ), hC', mul_le_mul_of_nonneg_left hhr (abs_nonneg (w.re : ℝ))]
    have h2 : |Real.sin θ - w.im * ch| ≤ |((ballC S : ℚ) : ℝ) - w.im * hc| + ((ballR S : ℚ) : ℝ) +
        |(w.im : ℝ)| * hr := by
      have e : Real.sin θ - w.im * ch = (Real.sin θ - ((ballC S : ℚ) : ℝ)) + (((ballC S : ℚ) : ℝ) - w.im * hc)
          + w.im * (hc - ch) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have := abs_add_le (Real.sin θ - ((ballC S : ℚ) : ℝ)) (((ballC S : ℚ) : ℝ) - w.im * hc)
      nlinarith [abs_nonneg (w.im : ℝ), hS', mul_le_mul_of_nonneg_left hhr (abs_nonneg (w.im : ℝ))]
    calc |Real.cos θ - w.re * ch| + |Real.sin θ - w.im * ch| ≤ X := by linarith
      _ = X / (hc - hr) * (hc - hr) := by field_simp
      _ ≤ X / (hc - hr) * ch := by gcongr
  · -- corner
    have htan' : c.tan = false := by simpa using htan
    rw [htan'] at h
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at h
    subst h
    have hc : coordC c = cexp ((θ : ℂ) * I) := by
      unfold coordC; rw [if_neg htan]
    rw [hc, hexp]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, toC_re, toC_im]
    push_cast [rabs_eq]
    have h1 : |Real.cos θ - (w.re : ℝ)| ≤ |((ballC C : ℚ) : ℝ) - w.re| + ((ballR C : ℚ) : ℝ) := by
      have e : Real.cos θ - (w.re : ℝ) = (Real.cos θ - ((ballC C : ℚ) : ℝ)) + (((ballC C : ℚ) : ℝ) - w.re) := by ring
      rw [e]; exact (abs_add_le _ _).trans (by linarith [hC'])
    have h2 : |Real.sin θ - (w.im : ℝ)| ≤ |((ballC S : ℚ) : ℝ) - w.im| + ((ballR S : ℚ) : ℝ) := by
      have e : Real.sin θ - (w.im : ℝ) = (Real.sin θ - ((ballC S : ℚ) : ℝ)) + (((ballC S : ℚ) : ℝ) - w.im) := by ring
      rw [e]; exact (abs_add_le _ _).trans (by linarith [hS'])
    linarith


/-! ### The error sum -/

lemma errTail_sound (w : Array CQ) : ∀ (l : List Comp) (j : ℕ) (r : ℚ), errTail w l j = some r →
    ∑ i ∈ Finset.range l.length, ‖coordC (l.getD i default) - toC w[j + i]!‖ ≤ (r : ℝ)
  | [], j, r, h => by
    simp only [errTail, Option.some.injEq] at h
    subst h; simp
  | c :: cs, j, r, h => by
    unfold errTail at h
    split at h
    · rename_i e r' he hr
      simp only [Option.some.injEq] at h
      subst h
      have h1 := coordErr_sound he
      have h2 := errTail_sound w cs (j + 1) r' hr
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      have e : ∑ i ∈ Finset.range cs.length, ‖coordC (cs.getD i default) - toC w[j + (i + 1)]!‖ =
          ∑ i ∈ Finset.range cs.length, ‖coordC (cs.getD i default) - toC w[j + 1 + i]!‖ :=
        Finset.sum_congr rfl fun i _ => by rw [show j + (i + 1) = j + 1 + i by ring]
      rw [e]
      push_cast
      linarith
    · exact absurd h (by simp)

lemma norm_one_sub_le (a : CQ) : ‖1 - toC a‖ ≤ |1 - (a.re : ℝ)| + |(a.im : ℝ)| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp [Complex.sub_re, Complex.sub_im, abs_neg]

/-- the total error bound -/
lemma errSum_sound {D : ℕ} {key : List Comp} (hkey : key.length = D) {w : Array CQ} {ρ : ℚ}
    (h : errSum key w = some ρ) :
    ∑ j : Fin (D + 1 + 1), ‖vtx D key j - vecC (D + 1 + 1) w j‖ ≤ (ρ : ℝ) := by
  unfold errSum at h
  obtain ⟨r, hr, hρ⟩ := Option.map_eq_some_iff.1 h
  subst hρ
  have ht := errTail_sound w key 2 r hr
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have e0 : vtx D key 0 = 1 := rfl
  have e1 : vtx D key (Fin.succ 0) = 1 := rfl
  have e2 : ∀ d : Fin D, vtx D key d.succ.succ = coordC (key.getD d.val default) := fun d => rfl
  have f0 : vecC (D + 1 + 1) w 0 = toC w[0]! := rfl
  have f1 : vecC (D + 1 + 1) w (Fin.succ 0) = toC w[1]! := rfl
  have f2 : ∀ d : Fin D, vecC (D + 1 + 1) w d.succ.succ = toC w[2 + d.val]! := fun d => by
    simp only [vecC, Fin.val_succ]; rw [show d.val + 1 + 1 = 2 + d.val by ring]
  simp only [e0, e1, e2, f0, f1, f2]
  rw [Fin.sum_univ_eq_sum_range (fun d => ‖coordC (key.getD d default) - toC w[2 + d]!‖) D, ← hkey]
  have h0 := norm_one_sub_le w[0]!
  have h1 := norm_one_sub_le w[1]!
  push_cast [rabs_eq]
  linarith

/-! ### Soundness of the vertex check -/

/-- The vertex property: `Re Σ_j conj(v_j) c_j ≤ B max_T |Σ_j c_j z^j|`. -/
def VProp (k : ℕ) (B : ℝ) (v : Fin (k + 1) → ℂ) : Prop :=
  ∀ (c : Fin (k + 1) → ℂ) (M : ℝ), (∀ z : ℂ, ‖z‖ = 1 → ‖∑ j, c j * z ^ (j : ℕ)‖ ≤ M) →
    (∑ j, star (v j) * c j).re ≤ B * M

lemma isToeplitz_one (k : ℕ) : IsToeplitz (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := by
  intro j l
  simp [Matrix.one_apply, Fin.succ_inj, Fin.castSucc_inj]

/-- `|c_j| ≤ max_T |Σ c_j z^j|` (Parseval, via the Toeplitz bound for the identity) -/
lemma norm_coeff_le {k : ℕ} (c : Fin (k + 1) → ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ j, c j * z ^ (j : ℕ)‖ ≤ M) (j : Fin (k + 1)) : ‖c j‖ ≤ M := by
  have h := toeplitz_bound_psd 1 PosSemidef.one (isToeplitz_one k) c hM0 hM
  rw [Matrix.one_mulVec, star_dot_self, Complex.ofReal_re, Matrix.one_apply_eq, Complex.one_re, one_mul] at h
  have : ‖c j‖ ^ 2 ≤ ∑ i, ‖c i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖c i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hM0 two_ne_zero).1 (this.trans h)

lemma wvec_get {n : ℕ} (t : ℕ → ℕ → CQ) (x : Array CQ) (j : Fin n) :
    (wvec n t x)[j.val]! = sumN n fun l => (t j l).mul x[l]! := by
  unfold wvec
  rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn]

/-- **Soundness of the vertex check.** -/
theorem vertexOK_sound {D : ℕ} {B : ℚ} {key : List Comp} {yv : Array ℚ}
    (h : vertexOK (D + 1) B key yv = true) : VProp (D + 1) B (vtx D key) := by
  unfold vertexOK at h
  dsimp only at h
  split_ifs at h with hlen
  have hkey : key.length = D := by omega
  set y : Array CQ := Array.ofFn (n := D + 1) fun i => ⟨yv[2 * i.val]!, yv[2 * i.val + 1]!⟩ with hy
  try simp only at h
  split at h
  · exact absurd h (by simp)
  rename_i L Dg hldl
  simp only [Bool.and_eq_true] at h
  obtain ⟨hok, hfin⟩ := h
  set n := D + 1 + 1 with hn
  set t := tmat y with ht
  set x := hint n L Dg key with hx
  set w := wvec n t x with hw
  unfold finalOK at hfin
  split at hfin
  · exact absurd hfin (by simp)
  rename_i ρ hρ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfin
  obtain ⟨hρB, hq⟩ := hfin
  -- the matrix, its properties, and the hint vectors
  set Tc := matC n t with hTc
  have hpsd : Tc.PosSemidef := ldlOK_psd (tmat_herm y) hok
  have hto : IsToeplitz Tc := matC_toeplitz (D + 1) y
  have h00 : Tc 0 0 = 1 := matC_00 (D + 1) y
  set xc := vecC n x with hxc
  set wc := vecC n w with hwc
  have hwT : wc = Tc *ᵥ xc := by
    funext j
    simp only [hwc, vecC, hw, wvec_get, toC_sumN, toC_mul, mulVec, dotProduct, hTc, matC, hxc]
  have hqv : ((qval n x w : ℚ) : ℝ) = (star xc ⬝ᵥ wc).re := by
    unfold qval
    rw [show ((sumN n fun j => (x[j]!.conj).mul w[j]!).re : ℝ) = (toC (sumN n fun j => (x[j]!.conj).mul w[j]!)).re
      from rfl, toC_sumN]
    simp only [toC_mul, toC_conj, dotProduct, Pi.star_apply, hxc, hwc, vecC]
  have herr := errSum_sound hkey hρ
  -- the bound
  intro c M hM
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 1 (by simp))
  have hcj := norm_coeff_le c hM0 hM
  have hTb := toeplitz_bound_psd Tc hpsd hto c hM0 hM
  rw [h00, Complex.one_re, one_mul] at hTb
  have hcs := psd_cauchy_schwarz hpsd xc c
  have hBρ : (0 : ℝ) ≤ B - ρ := by have : (ρ : ℝ) ≤ B := by exact_mod_cast hρB
                                   linarith
  have hq' : (star xc ⬝ᵥ (Tc *ᵥ xc)).re ≤ ((B : ℝ) - ρ) ^ 2 := by
    rw [← hwT, ← hqv]
    have : ((qval n x w : ℚ) : ℝ) ≤ ((B - ρ) * (B - ρ) : ℚ) := by exact_mod_cast hq
    push_cast at this; nlinarith
  have hxx0 : 0 ≤ (star xc ⬝ᵥ (Tc *ᵥ xc)).re := (Complex.nonneg_iff.1 (hpsd.dotProduct_mulVec_nonneg xc)).1
  have hcc0 : 0 ≤ (star c ⬝ᵥ (Tc *ᵥ c)).re := (Complex.nonneg_iff.1 (hpsd.dotProduct_mulVec_nonneg c)).1
  have hmain : ‖star xc ⬝ᵥ (Tc *ᵥ c)‖ ≤ ((B : ℝ) - ρ) * M := by
    have h2 : ‖star xc ⬝ᵥ (Tc *ᵥ c)‖ ^ 2 ≤ (((B : ℝ) - ρ) * M) ^ 2 := by
      calc ‖star xc ⬝ᵥ (Tc *ᵥ c)‖ ^ 2 ≤ (star xc ⬝ᵥ (Tc *ᵥ xc)).re * (star c ⬝ᵥ (Tc *ᵥ c)).re := hcs
        _ ≤ ((B : ℝ) - ρ) ^ 2 * M ^ 2 := mul_le_mul hq' hTb hcc0 (sq_nonneg _)
        _ = (((B : ℝ) - ρ) * M) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hBρ hM0) two_ne_zero).1 h2
  have hswap : star wc ⬝ᵥ c = star xc ⬝ᵥ (Tc *ᵥ c) := by
    rw [hwT, star_mulVec, hpsd.isHermitian.eq, ← dotProduct_mulVec]
  have hsplit : (∑ j, star (vtx D key j) * c j) = star wc ⬝ᵥ c + star (vtx D key - wc) ⬝ᵥ c := by
    rw [← add_dotProduct, ← star_add, add_sub_cancel]
    rfl
  have herr2 : ‖star (vtx D key - wc) ⬝ᵥ c‖ ≤ (ρ : ℝ) * M := by
    calc ‖star (vtx D key - wc) ⬝ᵥ c‖ ≤ ∑ j, ‖star (vtx D key - wc) j * c j‖ := norm_sum_le _ _
      _ = ∑ j, ‖vtx D key j - wc j‖ * ‖c j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Pi.star_apply, norm_star, Pi.sub_apply]
      _ ≤ ∑ j, ‖vtx D key j - wc j‖ * M :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcj j) (norm_nonneg _)
      _ = (∑ j, ‖vtx D key j - wc j‖) * M := by rw [Finset.sum_mul]
      _ ≤ (ρ : ℝ) * M := mul_le_mul_of_nonneg_right herr hM0
  rw [hsplit, Complex.add_re, hswap]
  have r1 := Complex.re_le_norm (star xc ⬝ᵥ (Tc *ᵥ c))
  have r2 := Complex.re_le_norm (star (vtx D key - wc) ⬝ᵥ c)
  nlinarith

end Bohr59a.Cert
