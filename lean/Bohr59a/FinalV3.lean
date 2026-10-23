/-
Version 3: `K₂ ≥ 0.301657` from Patel's Lemma 1, Lemma 2, `S_4 ≤ 2` (Newman), the Sidon bounds `S_5 ≤ 2.187`, `S_6 ≤ 2.363`
(Lemma 4, hypotheses here; discharged by the certificate checks), Newman's `S_n ≤ √n ≤ q_n/10⁸` for `7 ≤ n ≤ 40`
(`q_n = ⌈10⁸ √n⌉`) and `√n ≤ n` beyond:
`E(r) = 2r + r² B(r) + 2 [2 r⁴ + 2.187 r⁵ + 2.363 r⁶ + Σ_{n=7}^{40} (q_n/10⁸) rⁿ] + 2 r⁴¹ (41 - 40 r)/(1 - r)²`, `E(r*) < 1`.
-/
import Bohr59a.FinalPatel

open Finset

namespace Bohr59a

/-- `M_r(H) ≤ 2r + r² B(r) + 2 Σ_{n=4}^{n₀} s_n rⁿ + 2 Σ_{n > n₀} n rⁿ` whenever `S_n(H) ≤ 2 s_n` for `4 ≤ n ≤ n₀`. -/
theorem majorant_le_of_bounds (hPC : PatelColligation) {h : ℕ × ℕ → ℂ} (hP : PosReClass h) {α β γ r : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n₀ : ℕ) (hn₀ : 3 ≤ n₀) (s : ℕ → ℝ)
    (hs : ∀ n, 4 ≤ n → n ≤ n₀ → Sn h n ≤ 2 * s n) (N : ℕ) :
    ∑ n ∈ range N, Sn h (n + 1) * r ^ (n + 1) ≤
      2 * r + r ^ 2 * BFun α β γ r + ∑ n ∈ Ico 3 n₀, 2 * s (n + 1) * r ^ (n + 1) + 2 * tailT (n₀ + 1) r := by
  set a : ℕ → ℝ := fun n => Sn h (n + 1) * r ^ (n + 1) with ha_def
  have ha0 : ∀ n, 0 ≤ a n := fun n => mul_nonneg (Sn_nonneg h _) (pow_nonneg hr0 _)
  have h1 : ∑ n ∈ range N, a n ≤ ∑ n ∈ range (max N n₀), a n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (le_max_left _ _)) fun n _ _ => ha0 n
  refine h1.trans ?_
  rw [← Finset.sum_range_add_sum_Ico _ (le_max_right N n₀), ← Finset.sum_range_add_sum_Ico _ hn₀]
  have h012 : ∑ n ∈ range 3, a n ≤ 2 * r + r ^ 2 * BFun α β γ r := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ha_def]
    have hS1 : Sn h 1 ≤ 2 := by
      have := Sn_le_two_sqrt hP (n := 1) le_rfl
      simpa using this
    have hS23 := patel_S23 hPC hP hα hβ hγ r
    have e : Sn h (1 + 1) * r ^ (1 + 1) + Sn h (2 + 1) * r ^ (2 + 1) = r ^ 2 * (Sn h 2 + r * Sn h 3) := by ring
    nlinarith [mul_le_mul_of_nonneg_right hS1 hr0, mul_le_mul_of_nonneg_left hS23 (sq_nonneg r)]
  have hmid : ∑ n ∈ Ico 3 n₀, a n ≤ ∑ n ∈ Ico 3 n₀, 2 * s (n + 1) * r ^ (n + 1) := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Ico] at hn
    exact mul_le_mul_of_nonneg_right (hs (n + 1) (by omega) (by omega)) (pow_nonneg hr0 _)
  have htail : ∑ n ∈ Ico n₀ (max N n₀), a n ≤ 2 * tailT (n₀ + 1) r := by
    have hb : ∀ n ∈ Ico n₀ (max N n₀), a n ≤ 2 * (((n + 1 : ℕ) : ℝ) * r ^ (n + 1)) := by
      intro n _
      have hS := Sn_le_two_sqrt hP (n := n + 1) (by omega)
      have hsq : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_self_iff.2 (Or.inr (by exact_mod_cast Nat.succ_pos n))
      have : Sn h (n + 1) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by linarith
      calc a n = Sn h (n + 1) * r ^ (n + 1) := rfl
        _ ≤ 2 * ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) := mul_le_mul_of_nonneg_right this (pow_nonneg hr0 _)
        _ = _ := by ring
    calc ∑ n ∈ Ico n₀ (max N n₀), a n ≤ ∑ n ∈ Ico n₀ (max N n₀), 2 * (((n + 1 : ℕ) : ℝ) * r ^ (n + 1)) :=
          Finset.sum_le_sum hb
      _ = 2 * ∑ n ∈ Ico n₀ (max N n₀), ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) := by rw [Finset.mul_sum]
      _ ≤ 2 * tailT (n₀ + 1) r := by gcongr; exact sum_Ico_le_tailT n₀ hr0 hr1 _
  linarith

/-- `q_n = ⌈10⁸ √n⌉`, `n = 7, …, 40` -/
def qV3 : List ℕ := [264575132, 282842713, 300000000, 316227767, 331662480, 346410162, 360555128, 374165739, 387298335,
  400000000, 412310563, 424264069, 435889895, 447213596, 458257570, 469041576, 479583153, 489897949, 500000000, 509901952,
  519615243, 529150263, 538516481, 547722558, 556776437, 565685425, 574456265, 583095190, 591607979, 600000000, 608276254,
  616441401, 624499800, 632455533]

/-- `q_n` (`7 ≤ n ≤ 40`) -/
def q3 (n : ℕ) : ℕ := qV3.getD (n - 7) 0

lemma q3_sq : ∀ n ∈ Finset.Icc 7 40, 10 ^ 16 * n ≤ q3 n ^ 2 := by decide

lemma sqrt_le_q3 {n : ℕ} (hn : n ∈ Finset.Icc 7 40) : Real.sqrt n ≤ (q3 n : ℝ) / 10 ^ 8 := by
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast (by have := q3_sq n hn; linarith : n * (10 ^ 8) ^ 2 ≤ q3 n ^ 2)

/-- the degree bounds of version 3 -/
noncomputable def sV3 (n : ℕ) : ℝ :=
  if n = 4 then 2 else if n = 5 then 2187 / 1000 else if n = 6 then 2363 / 1000 else (q3 n : ℝ) / 10 ^ 8

lemma Sn_le_sV3 {h : ℕ × ℕ → ℂ} (hP : PosReClass h) (h5 : SidonBound 5 (2187 / 1000))
    (h6 : SidonBound 6 (2363 / 1000)) {n : ℕ} (hn4 : 4 ≤ n) (hn40 : n ≤ 40) : Sn h n ≤ 2 * sV3 n := by
  unfold sV3
  by_cases e4 : n = 4
  · subst e4
    have := Sn_le_two_sqrt hP (n := 4) (by norm_num)
    have hs : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
      rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hs] at this
    simpa using this
  by_cases e5 : n = 5
  · subst e5; simpa using Sn_le_of_sidon hP (by norm_num) h5
  by_cases e6 : n = 6
  · subst e6; simpa using Sn_le_of_sidon hP (by norm_num) h6
  rw [if_neg e4, if_neg e5, if_neg e6]
  have hS := Sn_le_two_sqrt hP (n := n) (by omega)
  have hq := sqrt_le_q3 (n := n) (Finset.mem_Icc.2 ⟨by omega, hn40⟩)
  linarith

/-- the majorant of version 3 -/
noncomputable def EV3 (α β γ r : ℝ) : ℝ :=
  2 * r + r ^ 2 * BFun α β γ r + ∑ n ∈ Ico 3 40, 2 * sV3 (n + 1) * r ^ (n + 1) + 2 * tailT 41 r

/-- The radius of version 3 -/
noncomputable def r3 : ℝ := 301657 / 1000000

/-- `E(r*) < 1`, exactly. -/
theorem EV3_lt_one : EV3 (165392627 / 500000000) (62421603 / 25000000000) (25496997 / 250000000) r3 < 1 := by
  unfold EV3 BFun tailT r3
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sV3, q3, qV3]
  norm_num

/-- The majorant bound at `r* = 0.301657`, given the two Sidon bounds. -/
theorem majorantBound_v3 (hPC : PatelColligation) (h5 : SidonBound 5 (2187 / 1000))
    (h6 : SidonBound 6 (2363 / 1000)) : MajorantBound r3 := fun h hP N =>
  (majorant_le_of_bounds hPC hP (by norm_num) (by norm_num) (by norm_num) (by norm_num [r3]) (by norm_num [r3]) 40
    (by norm_num) sV3 (fun n h4 h40 => Sn_le_sV3 hP h5 h6 h4 h40) N).trans EV3_lt_one.le

/-- **`K₂ ≥ 0.301657`**, given `PatelColligation` and the Sidon bounds `S_5 ≤ 2.187`, `S_6 ≤ 2.363`. -/
theorem K2_ge_of_sidon (hPC : PatelColligation) (h5 : SidonBound 5 (2187 / 1000))
    (h6 : SidonBound 6 (2363 / 1000)) : K2Claim :=
  le_K2 (by norm_num) (bohrIneq_of_majorant (by norm_num [r3]) (majorantBound_v3 hPC h5 h6))

end Bohr59a
