/-
Patel's own lower bound `K₂ ≥ r* = 15079379/50000000 = 0.30158758`, conditional on `PatelColligation` only:
`M_r(H) ≤ E(r) = 2r + r² B(r) + 2 Σ_{n=4}^{20} (q_n/10⁸) rⁿ + 2 r²¹ (21 - 20 r)/(1 - r)²` (Lemma 1, Lemma 2 with Newman's
`S_n ≤ √n`, `√n ≤ q_n/10⁸` for `4 ≤ n ≤ 20`, `√n ≤ n` beyond), and `E(r*) < 1` in exact rational arithmetic.
-/
import Bohr59a.Patel
import Bohr59a.Passage

open Finset

namespace Bohr59a

/-- `S_n(H) ≤ 2 √n` for `n ≥ 1` (Lemma 2 with Newman's bound). -/
lemma Sn_le_two_sqrt {h : ℕ × ℕ → ℂ} (hP : PosReClass h) {n : ℕ} (hn : 1 ≤ n) : Sn h n ≤ 2 * Real.sqrt n :=
  Sn_le_of_sidon hP hn (sidon_newman hn)

lemma Sn_nonneg (h : ℕ × ℕ → ℂ) (n : ℕ) : 0 ≤ Sn h n := Finset.sum_nonneg fun _ _ => norm_nonneg _

/-! ### The tail `Σ_{m ≥ a} m rᵐ` -/

/-- `Σ_{m ≥ a} m rᵐ = rᵃ (a - (a - 1) r)/(1 - r)²` -/
noncomputable def tailT (a : ℕ) (r : ℝ) : ℝ := r ^ a * (a - (a - 1) * r) / (1 - r) ^ 2

lemma tailT_succ (a : ℕ) {r : ℝ} (hr : r ≠ 1) : tailT a r = a * r ^ a + tailT (a + 1) r := by
  have h : (1 - r) ≠ 0 := sub_ne_zero.2 (Ne.symm hr)
  unfold tailT
  push_cast
  field_simp
  ring

lemma tailT_nonneg (a : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 ≤ tailT a r := by
  unfold tailT
  have : 0 ≤ (a : ℝ) - (a - 1) * r := by nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  positivity

/-- the partial sums of the tail lie below `tailT` -/
lemma sum_Ico_le_tailT (a : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∑ n ∈ Ico a K, ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) ≤ tailT (a + 1) r := by
  rcases le_or_gt K a with hK | hK
  · rw [Finset.Ico_eq_empty_of_le hK, Finset.sum_empty]; exact tailT_nonneg _ hr0 hr1
  · have key : ∀ K, a ≤ K → ∑ n ∈ Ico a K, ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) + tailT (K + 1) r = tailT (a + 1) r := by
      intro K hK
      induction K, hK using Nat.le_induction with
      | base => simp
      | succ K hK ih =>
        rw [Finset.sum_Ico_succ_top hK, ← ih, tailT_succ (K + 1) hr1.ne]
        ring
    have := key K hK.le
    linarith [tailT_nonneg (K + 1) hr0 hr1]

/-! ### Patel's table and the majorant -/

/-- Patel's integers `q_n ≥ 10⁸ √n`, `n = 4, …, 20` -/
def qPatel : List ℕ := [200000000, 223606798, 244948975, 264575132, 282842713, 300000000, 316227767, 331662480,
  346410162, 360555128, 374165739, 387298335, 400000000, 412310563, 424264069, 435889895, 447213596]

/-- `q_n` (`4 ≤ n ≤ 20`) -/
def qP (n : ℕ) : ℕ := qPatel.getD (n - 4) 0

lemma qP_sq : ∀ n ∈ Finset.Icc 4 20, 10 ^ 16 * n ≤ qP n ^ 2 := by decide

lemma sqrt_le_qP {n : ℕ} (hn : n ∈ Finset.Icc 4 20) : Real.sqrt n ≤ (qP n : ℝ) / 10 ^ 8 := by
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast (by have := qP_sq n hn; linarith : n * (10 ^ 8) ^ 2 ≤ qP n ^ 2)

/-- Patel's majorant `E(r)` -/
noncomputable def EPatel (α β γ r : ℝ) : ℝ :=
  2 * r + r ^ 2 * BFun α β γ r + ∑ n ∈ Ico 3 20, 2 * ((qP (n + 1) : ℝ) / 10 ^ 8) * r ^ (n + 1) + 2 * tailT 21 r

/-- `M_r(H) ≤ E(r)` for every partial sum. -/
theorem majorant_le_EPatel (hPC : PatelColligation) {h : ℕ × ℕ → ℂ} (hP : PosReClass h) {α β γ r : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ n ∈ range N, Sn h (n + 1) * r ^ (n + 1) ≤ EPatel α β γ r := by
  set a : ℕ → ℝ := fun n => Sn h (n + 1) * r ^ (n + 1) with ha_def
  have ha0 : ∀ n, 0 ≤ a n := fun n => mul_nonneg (Sn_nonneg h _) (pow_nonneg hr0 _)
  -- enlarge to `N' = max N 20 ≥ 20`
  have h1 : ∑ n ∈ range N, a n ≤ ∑ n ∈ range (max N 20), a n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (le_max_left _ _)) fun n _ _ => ha0 n
  refine h1.trans ?_
  rw [← Finset.sum_range_add_sum_Ico _ (le_max_right N 20), ← Finset.sum_range_add_sum_Ico _ (by norm_num : 3 ≤ 20)]
  have h012 : ∑ n ∈ range 3, a n ≤ 2 * r + r ^ 2 * BFun α β γ r := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ha_def]
    have hS1 : Sn h 1 ≤ 2 := by
      have := Sn_le_two_sqrt hP (n := 1) le_rfl
      simpa using this
    have hS23 := patel_S23 hPC hP hα hβ hγ r
    have e : Sn h (1 + 1) * r ^ (1 + 1) + Sn h (2 + 1) * r ^ (2 + 1) = r ^ 2 * (Sn h 2 + r * Sn h 3) := by ring
    nlinarith [mul_le_mul_of_nonneg_right hS1 hr0, mul_le_mul_of_nonneg_left hS23 (sq_nonneg r)]
  have hmid : ∑ n ∈ Ico 3 20, a n ≤ ∑ n ∈ Ico 3 20, 2 * ((qP (n + 1) : ℝ) / 10 ^ 8) * r ^ (n + 1) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' : n + 1 ∈ Finset.Icc 4 20 := by
      rw [Finset.mem_Ico] at hn; rw [Finset.mem_Icc]; omega
    have hS := Sn_le_two_sqrt hP (n := n + 1) (by omega)
    have hq := sqrt_le_qP hn'
    have : Sn h (n + 1) ≤ 2 * ((qP (n + 1) : ℝ) / 10 ^ 8) := by linarith
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hr0 _)
  have htail : ∑ n ∈ Ico 20 (max N 20), a n ≤ 2 * tailT 21 r := by
    have hb : ∀ n ∈ Ico 20 (max N 20), a n ≤ 2 * (((n + 1 : ℕ) : ℝ) * r ^ (n + 1)) := by
      intro n _
      have hS := Sn_le_two_sqrt hP (n := n + 1) (by omega)
      have hsq : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_self_iff.2 (Or.inr (by exact_mod_cast Nat.succ_pos n))
      have : Sn h (n + 1) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by linarith
      calc a n = Sn h (n + 1) * r ^ (n + 1) := rfl
        _ ≤ 2 * ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) := mul_le_mul_of_nonneg_right this (pow_nonneg hr0 _)
        _ = _ := by ring
    calc ∑ n ∈ Ico 20 (max N 20), a n ≤ ∑ n ∈ Ico 20 (max N 20), 2 * (((n + 1 : ℕ) : ℝ) * r ^ (n + 1)) :=
          Finset.sum_le_sum hb
      _ = 2 * ∑ n ∈ Ico 20 (max N 20), ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) := by rw [Finset.mul_sum]
      _ ≤ 2 * tailT 21 r := by gcongr; exact sum_Ico_le_tailT 20 hr0 hr1 _
  unfold EPatel
  linarith

/-- Patel's parameters -/
noncomputable def rP : ℝ := 15079379 / 50000000

/-- `E(r*) < 1`, exactly. -/
theorem EPatel_lt_one : EPatel (264631 / 800000) (249627 / 100000000) (10197021 / 100000000) rP < 1 := by
  unfold EPatel BFun tailT rP
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, qP, qPatel]
  norm_num

/-- The majorant bound at Patel's radius. -/
theorem majorantBound_patel (hPC : PatelColligation) : MajorantBound rP := fun h hP N =>
  (majorant_le_EPatel hPC hP (by norm_num) (by norm_num) (by norm_num) (by norm_num [rP]) (by norm_num [rP]) N).trans
    EPatel_lt_one.le

/-- **Patel's theorem** `K₂ ≥ 0.30158758`, conditional on `PatelColligation` (Lemma 1 (c)). -/
theorem K2_ge_patel (hPC : PatelColligation) : (15079379 / 50000000 : ℝ) ≤ K2 :=
  le_K2 (by norm_num) (bohrIneq_of_majorant (by norm_num [rP]) (majorantBound_patel hPC))

end Bohr59a
