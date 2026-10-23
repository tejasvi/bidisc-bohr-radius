/-
Passage from `PosReClass` to the Bohr radius (Patel): for `f` with `|f| < 1`, rotated so that `σ f(0) = t ∈ [0, 1)`,
`H = (1 - σ f)/(1 - t)` is in `PosReClass` and `|f_α| = (1 - t)|h_α|` for `α ≠ 0`, so every finite partial sum of
`Σ_α |f_α| r^{|α|}` is at most `t + (1 - t) Σ_{n ≥ 1} S_n(H) r^n`.  Also `K₂ ≥ r` as soon as Bohr's inequality holds at `r > 0`
(the set is bounded by `1`, test function `f = z₁`).
-/
import Bohr59a.Slice

open Complex Finset

namespace Bohr59a

/-- The majorant bound at radius `r`: every partial sum of `Σ_{n ≥ 1} S_n(H) rⁿ` is at most `1`, for every `H`. -/
def MajorantBound (r : ℝ) : Prop :=
  ∀ h : ℕ × ℕ → ℂ, PosReClass h → ∀ N : ℕ, ∑ n ∈ range N, Sn h (n + 1) * r ^ (n + 1) ≤ 1

lemma bohrClass_zero {c : ℕ × ℕ → ℂ} (hc : BohrClass c) : ‖c (0, 0)‖ < 1 := by
  obtain ⟨w, hw, hw1⟩ := hc 0 0 (by simp) (by simp)
  have : HasSum (fun α : ℕ × ℕ => c α * (0 : ℂ) ^ α.1 * (0 : ℂ) ^ α.2) (c (0, 0)) := by
    have e : (fun α : ℕ × ℕ => c α * (0 : ℂ) ^ α.1 * (0 : ℂ) ^ α.2) =
        fun α => if α = (0, 0) then c (0, 0) else 0 := by
      funext α
      obtain ⟨j, k⟩ := α
      by_cases hj : j = 0 <;> by_cases hk : k = 0 <;> simp [hj, hk]
    rw [e]
    exact hasSum_ite_eq (0, 0) (c (0, 0))
  rwa [this.unique hw]

/-- **Patel's passage**: the majorant bound at `r ≥ 0` implies Bohr's inequality at `r`. -/
theorem bohrIneq_of_majorant {r : ℝ} (hr : 0 ≤ r) (hM : MajorantBound r) : BohrIneq r := by
  intro c hc s
  set t := ‖c (0, 0)‖ with ht_def
  have ht1 : t < 1 := bohrClass_zero hc
  have ht0 : 0 ≤ t := norm_nonneg _
  obtain ⟨σ, hσ1, hσ⟩ := Complex.exists_norm_eq_mul_self (c (0, 0))
  have h1t : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
  have h1t0 : ((1 - t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
  -- `H = (1 - σ f)/(1 - t)`
  set h : ℕ × ℕ → ℂ := fun α => ((if α = (0, 0) then 1 else 0) - σ * c α) / ((1 - t : ℝ) : ℂ) with h_def
  have hP : PosReClass h := by
    refine ⟨?_, fun z w hz hw => ?_⟩
    · show ((if ((0 : ℕ), (0 : ℕ)) = (0, 0) then (1 : ℂ) else 0) - σ * c (0, 0)) / ((1 - t : ℝ) : ℂ) = 1
      rw [if_pos rfl, ← hσ, ← ht_def, h1t]
      exact div_self h1t0
    · obtain ⟨F, hF, hF1⟩ := hc z w hz hw
      refine ⟨(1 - σ * F) / ((1 - t : ℝ) : ℂ), ?_, ?_⟩
      · have h1 : HasSum (fun α : ℕ × ℕ => (if α = (0, 0) then (1 : ℂ) else 0) * z ^ α.1 * w ^ α.2) 1 := by
          have e : (fun α : ℕ × ℕ => (if α = (0, 0) then (1 : ℂ) else 0) * z ^ α.1 * w ^ α.2) =
              fun α => if α = (0, 0) then 1 else 0 := by
            funext α
            by_cases hα : α = (0, 0)
            · subst hα; simp
            · simp [hα]
          rw [e]
          exact hasSum_ite_eq _ _
        have h2 := (h1.sub (hF.mul_left σ)).div_const ((1 - t : ℝ) : ℂ)
        convert h2 using 1
        funext α
        simp only [h_def]
        ring
      · have hσF : ‖σ * F‖ < 1 := by rw [norm_mul, hσ1, one_mul]; exact hF1
        have hre : (σ * F).re < 1 := lt_of_le_of_lt (Complex.re_le_norm _) hσF
        rw [Complex.div_ofReal_re]
        apply div_pos _ (by linarith)
        rw [Complex.sub_re, Complex.one_re]
        linarith
  -- `|f_α| = (1 - t) |h_α|` for `α ≠ 0`
  have hcoef : ∀ α : ℕ × ℕ, α ≠ (0, 0) → ‖c α‖ = (1 - t) * ‖h α‖ := by
    intro α hα
    simp only [h_def, if_neg hα, zero_sub, norm_div, norm_neg, norm_mul, hσ1, one_mul]
    rw [Complex.norm_of_nonneg (by linarith)]
    have : (1 - t) ≠ 0 := (sub_pos.2 ht1).ne'
    field_simp
  -- the partial sum over `s` lies below the partial sum over the antidiagonals `n ≤ N`
  obtain ⟨N, hN⟩ : ∃ N, ∀ α ∈ s, α.1 + α.2 < N + 1 :=
    ⟨∑ α ∈ s, (α.1 + α.2), fun α hα => by
      have := Finset.single_le_sum (f := fun α : ℕ × ℕ => α.1 + α.2) (fun _ _ => Nat.zero_le _) hα
      omega⟩
  have step1 : ∑ α ∈ s, ‖c α‖ * r ^ (α.1 + α.2) ≤
      ∑ n ∈ range (N + 1), ∑ α ∈ antidiagonal n, ‖c α‖ * r ^ (α.1 + α.2) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun α : ℕ × ℕ => α.1 + α.2) (t := range (N + 1))
      (fun α hα => mem_range.2 (hN α hα))]
    refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum_of_subset_of_nonneg ?_ fun α _ _ => by positivity
    intro α hα
    simp only [Finset.mem_filter] at hα
    exact Finset.HasAntidiagonal.mem_antidiagonal.2 hα.2
  have step2 : ∀ n, ∑ α ∈ antidiagonal n, ‖c α‖ * r ^ (α.1 + α.2) = (∑ α ∈ antidiagonal n, ‖c α‖) * r ^ n := by
    intro n
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun α hα => by rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hα]
  have step3 : ∀ n, ∑ α ∈ antidiagonal (n + 1), ‖c α‖ = (1 - t) * Sn h (n + 1) := by
    intro n
    rw [Sn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => hcoef α ?_
    rintro rfl
    simp at hα
  have hsum := hM h hP N
  calc ∑ α ∈ s, ‖c α‖ * r ^ (α.1 + α.2) ≤ _ := step1
    _ = t + (1 - t) * ∑ n ∈ range N, Sn h (n + 1) * r ^ (n + 1) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      congr 1
      · simp [ht_def]
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [step2, step3]
        ring
    _ ≤ t + (1 - t) * 1 := by gcongr
    _ = 1 := by ring

/-- Bohr's inequality fails beyond `1` (test function `f = z₁`). -/
lemma bohrIneq_le_one {r : ℝ} (h : BohrIneq r) : r ≤ 1 := by
  set c : ℕ × ℕ → ℂ := fun α => if α = (1, 0) then 1 else 0 with hc_def
  have hc : BohrClass c := by
    intro z₁ z₂ hz₁ _
    refine ⟨z₁, ?_, hz₁⟩
    have e : (fun α : ℕ × ℕ => c α * z₁ ^ α.1 * z₂ ^ α.2) = fun α => if α = (1, 0) then z₁ else 0 := by
      funext α
      by_cases hα : α = (1, 0)
      · subst hα; simp [hc_def]
      · simp [hc_def, hα]
    rw [e]
    exact hasSum_ite_eq _ _
  have := h c hc {(1, 0)}
  simpa [hc_def] using this

/-- `r ≤ K₂` whenever Bohr's inequality holds at `r > 0`. -/
theorem le_K2 {r : ℝ} (hr : 0 < r) (h : BohrIneq r) : r ≤ K2 :=
  le_csSup ⟨1, fun _ hx => bohrIneq_le_one hx.2⟩ ⟨hr, h⟩

end Bohr59a
