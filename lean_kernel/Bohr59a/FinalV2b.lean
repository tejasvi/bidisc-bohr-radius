/-
Version 2b: `K₂ ≥ 0.301633` from the Sidon bound `S_5 ≤ 2.187` alone (Newman's `S_n ≤ √n ≤ q_n/10⁸` for `n = 6, …, 40`,
`q_n = ⌈10⁸ √n⌉`): THEOREM_59_v3 consistency row (ii), parameters `a = 165393231/500000000`, `b = 249665903/100000000000`,
`g = 25495461/250000000`.
-/
import Bohr59a.FinalV3

open Finset

namespace Bohr59a

/-- `q_n = ⌈10⁸ √n⌉`, `n = 6, …, 40` -/
def q2b (n : ℕ) : ℕ := (244948975 :: qV3).getD (n - 6) 0

lemma q2b_sq : ∀ n ∈ Finset.Icc 6 40, 10 ^ 16 * n ≤ q2b n ^ 2 := by decide

lemma sqrt_le_q2b {n : ℕ} (hn : n ∈ Finset.Icc 6 40) : Real.sqrt n ≤ (q2b n : ℝ) / 10 ^ 8 := by
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast (by have := q2b_sq n hn; linarith : n * (10 ^ 8) ^ 2 ≤ q2b n ^ 2)

/-- the degree bounds of version 2b -/
noncomputable def sV2b (n : ℕ) : ℝ := if n = 4 then 2 else if n = 5 then 2187 / 1000 else (q2b n : ℝ) / 10 ^ 8

lemma Sn_le_sV2b {h : ℕ × ℕ → ℂ} (hP : PosReClass h) (h5 : SidonBound 5 (2187 / 1000)) {n : ℕ} (hn4 : 4 ≤ n)
    (hn40 : n ≤ 40) : Sn h n ≤ 2 * sV2b n := by
  unfold sV2b
  by_cases e4 : n = 4
  · subst e4
    have := Sn_le_two_sqrt hP (n := 4) (by norm_num)
    have hs : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
      rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hs] at this
    simpa using this
  by_cases e5 : n = 5
  · subst e5; simpa using Sn_le_of_sidon hP (by norm_num) h5
  rw [if_neg e4, if_neg e5]
  have hS := Sn_le_two_sqrt hP (n := n) (by omega)
  have hq := sqrt_le_q2b (n := n) (Finset.mem_Icc.2 ⟨by omega, hn40⟩)
  linarith

/-- the majorant of version 2b -/
noncomputable def EV2b (α β γ r : ℝ) : ℝ :=
  2 * r + r ^ 2 * BFun α β γ r + ∑ n ∈ Ico 3 40, 2 * sV2b (n + 1) * r ^ (n + 1) + 2 * tailT 41 r

/-- The radius of version 2b -/
noncomputable def r2b : ℝ := 301633 / 1000000

/-- `E(r*) < 1`, exactly. -/
theorem EV2b_lt_one : EV2b (165393231 / 500000000) (249665903 / 100000000000) (25495461 / 250000000) r2b < 1 := by
  unfold EV2b BFun tailT r2b
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sV2b, q2b, qV3]
  norm_num

/-- The majorant bound at `r* = 0.301633`, given `S_5 ≤ 2.187`. -/
theorem majorantBound_v2b (hPC : PatelColligation) (h5 : SidonBound 5 (2187 / 1000)) : MajorantBound r2b :=
  fun h hP N =>
  (majorant_le_of_bounds hPC hP (by norm_num) (by norm_num) (by norm_num) (by norm_num [r2b]) (by norm_num [r2b]) 40
    (by norm_num) sV2b (fun n h4 h40 => Sn_le_sV2b hP h5 h4 h40) N).trans EV2b_lt_one.le

/-- **`K₂ ≥ 0.301633`**, given `PatelColligation` and the Sidon bound `S_5 ≤ 2.187`. -/
theorem K2_ge_of_sidon5 (hPC : PatelColligation) (h5 : SidonBound 5 (2187 / 1000)) :
    (301633 / 1000000 : ℝ) ≤ K2 :=
  le_K2 (by norm_num) (bohrIneq_of_majorant (by norm_num [r2b]) (majorantBound_v2b hPC h5))

end Bohr59a
