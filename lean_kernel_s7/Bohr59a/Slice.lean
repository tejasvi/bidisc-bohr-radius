/-
Slices of the class `PosReClass`: for `|ζ| ≤ 1` the function `λ ↦ H(λζ, λ)` has the Taylor coefficients
`qₙ(ζ) = Σ_{j+k=n} h_{jk} ζ^j` (regrouping the double series by antidiagonals), positive real part and `q₀ = 1`; hence
`|qₙ(ζ)| ≤ 2` for `n ≥ 1` (Carathéodory), and `Sₙ(H) ≤ 2 s` whenever `s` is a Sidon bound for degree `n` (Lemma 2).
-/
import Bohr59a.Hypotheses
import Bohr59a.Carath

open Complex Finset

namespace Bohr59a

/-- regrouping a double series by antidiagonals -/
lemma hasSum_antidiag {F : ℕ × ℕ → ℂ} {v : ℂ} (h : HasSum F v) :
    HasSum (fun n => ∑ kl ∈ antidiagonal n, F kl) v := by
  have h' := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.2 h
  refine h'.sigma fun n => ?_
  have := hasSum_fintype (fun c : antidiagonal n => F c)
  simpa [Function.comp_def, Finset.sum_coe_sort, Finset.sum_attach] using this

/-- the slice coefficients `qₙ(ζ) = Σ_{j+k=n} h_{jk} ζ^j` -/
def sliceCoeff (h : ℕ × ℕ → ℂ) (ζ : ℂ) (n : ℕ) : ℂ := ∑ kl ∈ antidiagonal n, h kl * ζ ^ kl.1

lemma slice_carath_hyp {h : ℕ × ℕ → ℂ} (hP : PosReClass h) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) :
    ∀ z : ℂ, ‖z‖ < 1 → ∃ v, HasSum (fun n => sliceCoeff h ζ n * z ^ n) v ∧ 0 < v.re := by
  intro z hz
  have hzζ : ‖z * ζ‖ < 1 := by
    rw [norm_mul]; calc ‖z‖ * ‖ζ‖ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hz
  obtain ⟨v, hv, hre⟩ := hP.2 (z * ζ) z hzζ hz
  refine ⟨v, ?_, hre⟩
  have h2 := hasSum_antidiag hv
  convert h2 using 1
  funext n
  rw [sliceCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, mul_pow, pow_add]
  ring

lemma sliceCoeff_zero {h : ℕ × ℕ → ℂ} (hP : PosReClass h) (ζ : ℂ) : sliceCoeff h ζ 0 = 1 := by
  simp [sliceCoeff, hP.1]

/-- `|qₙ(ζ)| ≤ 2` for `n ≥ 1` and `|ζ| ≤ 1` -/
lemma norm_sliceCoeff_le {h : ℕ × ℕ → ℂ} (hP : PosReClass h) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖sliceCoeff h ζ n‖ ≤ 2 :=
  carath_coeff (slice_carath_hyp hP hζ) (sliceCoeff_zero hP ζ) hn

/-- `Sₙ(H) = Σ_{j+k=n} |h_{jk}|` -/
noncomputable def Sn (h : ℕ × ℕ → ℂ) (n : ℕ) : ℝ := ∑ kl ∈ antidiagonal n, ‖h kl‖

/-- Sidon bound: `Σ_{j ≤ n} |c_j| ≤ s · max_T |Σ c_j z^j|` -/
def SidonBound (n : ℕ) (s : ℝ) : Prop :=
  ∀ (c : Fin (n + 1) → ℂ) (M : ℝ), (∀ z : ℂ, ‖z‖ = 1 → ‖∑ j, c j * z ^ (j : ℕ)‖ ≤ M) → ∑ j, ‖c j‖ ≤ s * M

lemma sliceCoeff_eq_fin (h : ℕ × ℕ → ℂ) (ζ : ℂ) (n : ℕ) :
    sliceCoeff h ζ n = ∑ j : Fin (n + 1), h ((j : ℕ), n - j) * ζ ^ (j : ℕ) := by
  rw [sliceCoeff, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]

lemma Sn_eq_fin (h : ℕ × ℕ → ℂ) (n : ℕ) : Sn h n = ∑ j : Fin (n + 1), ‖h ((j : ℕ), n - j)‖ := by
  rw [Sn, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]

/-- Lemma 2: `Sₙ(H) ≤ 2 s` -/
lemma Sn_le_of_sidon {h : ℕ × ℕ → ℂ} (hP : PosReClass h) {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : SidonBound n s) :
    Sn h n ≤ 2 * s := by
  rw [Sn_eq_fin]
  have := hs (fun j => h ((j : ℕ), n - j)) 2 fun z hz => by
    rw [← sliceCoeff_eq_fin]; exact norm_sliceCoeff_le hP hz.le hn
  linarith

end Bohr59a
