/-
Version 3b: `K₂ ≥ 0.301665`, version 3 plus the Sidon bound `S_7 ≤ 2.552` (Lemma 4, k = 7; a hypothesis here, to be
discharged by the certificate checks):
`E(r) = 2r + r² B(r) + 2 [2 r⁴ + 2.187 r⁵ + 2.363 r⁶ + 2.552 r⁷ + Σ_{n=8}^{40} (q_n/10⁸) rⁿ] + 2 r⁴¹ (41 - 40 r)/(1 - r)²`,
`E(r*) < 1` at `r* = 60333/200000`.
-/
import Bohr59a.FinalV3

open Finset

namespace Bohr59a

/-- the degree bounds of version 3b -/
noncomputable def sV3b (n : ℕ) : ℝ :=
  if n = 4 then 2 else if n = 5 then 2187 / 1000 else if n = 6 then 2363 / 1000 else if n = 7 then 2552 / 1000
  else (q3 n : ℝ) / 10 ^ 8

lemma Sn_le_sV3b {h : ℕ × ℕ → ℂ} (hP : PosReClass h) (h5 : SidonBound 5 (2187 / 1000))
    (h6 : SidonBound 6 (2363 / 1000)) (h7 : SidonBound 7 (2552 / 1000)) {n : ℕ} (hn4 : 4 ≤ n) (hn40 : n ≤ 40) :
    Sn h n ≤ 2 * sV3b n := by
  unfold sV3b
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
  by_cases e7 : n = 7
  · subst e7; simpa using Sn_le_of_sidon hP (by norm_num) h7
  rw [if_neg e4, if_neg e5, if_neg e6, if_neg e7]
  have hS := Sn_le_two_sqrt hP (n := n) (by omega)
  have hq := sqrt_le_q3 (n := n) (Finset.mem_Icc.2 ⟨by omega, hn40⟩)
  linarith

/-- the majorant of version 3b -/
noncomputable def EV3b (α β γ r : ℝ) : ℝ :=
  2 * r + r ^ 2 * BFun α β γ r + ∑ n ∈ Ico 3 40, 2 * sV3b (n + 1) * r ^ (n + 1) + 2 * tailT 41 r

/-- The radius of version 3b -/
noncomputable def r3b : ℝ := 60333 / 200000

/-- `E(r*) < 1`, exactly. -/
theorem EV3b_lt_one : EV3b (20674053 / 62500000) (3901457 / 1562500000) (101990031 / 1000000000) r3b < 1 := by
  unfold EV3b BFun tailT r3b
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sV3b, q3, qV3]
  norm_num

/-- The majorant bound at `r* = 0.301665`, given the three Sidon bounds. -/
theorem majorantBound_v3b (hPC : PatelColligation) (h5 : SidonBound 5 (2187 / 1000))
    (h6 : SidonBound 6 (2363 / 1000)) (h7 : SidonBound 7 (2552 / 1000)) : MajorantBound r3b := fun h hP N =>
  (majorant_le_of_bounds hPC hP (by norm_num) (by norm_num) (by norm_num) (by norm_num [r3b]) (by norm_num [r3b]) 40
    (by norm_num) sV3b (fun n h4 h40 => Sn_le_sV3b hP h5 h6 h7 h4 h40) N).trans EV3b_lt_one.le

/-- **`K₂ ≥ 0.301665`**, given `PatelColligation` and the Sidon bounds `S_5 ≤ 2.187`, `S_6 ≤ 2.363`, `S_7 ≤ 2.552`. -/
theorem K2_ge_of_sidon7 (hPC : PatelColligation) (h5 : SidonBound 5 (2187 / 1000))
    (h6 : SidonBound 6 (2363 / 1000)) (h7 : SidonBound 7 (2552 / 1000)) : (60333 / 200000 : ℝ) ≤ K2 :=
  le_K2 (by norm_num) (bohrIneq_of_majorant (by norm_num [r3b]) (majorantBound_v3b hPC h5 h6 h7))

end Bohr59a
