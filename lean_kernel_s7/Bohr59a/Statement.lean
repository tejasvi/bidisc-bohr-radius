/-
Statement of the lower bound `K₂ ≥ 0.301657` for the Bohr radius of the bidisc (constant 59a of the
optimization-constants repository). Mathlib definitions only.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Bohr59a

/-- The coefficient families `c : ℕ × ℕ → ℂ` of the holomorphic functions `f : 𝔻² → 𝔻`:
`f(z₁, z₂) = Σ_α c_α z₁^{α₁} z₂^{α₂}` converges (unconditionally, i.e. absolutely) at every point of the open
bidisc and its value has modulus `< 1`. -/
def BohrClass (c : ℕ × ℕ → ℂ) : Prop :=
  ∀ z₁ z₂ : ℂ, ‖z₁‖ < 1 → ‖z₂‖ < 1 →
    ∃ w : ℂ, HasSum (fun α : ℕ × ℕ => c α * z₁ ^ α.1 * z₂ ^ α.2) w ∧ ‖w‖ < 1

/-- Bohr's inequality at radius `r`: `‖f_r‖₁ = Σ_α |c_α| r^{|α|} ≤ 1` for every `f` in the class
(stated for all finite partial sums of the non-negative series). -/
def BohrIneq (r : ℝ) : Prop :=
  ∀ c : ℕ × ℕ → ℂ, BohrClass c → ∀ s : Finset (ℕ × ℕ), ∑ α ∈ s, ‖c α‖ * r ^ (α.1 + α.2) ≤ 1

/-- The Bohr radius of the bidisc, `K₂ = sup {r > 0 : Bohr's inequality holds at r}`. -/
noncomputable def K2 : ℝ := sSup {r : ℝ | 0 < r ∧ BohrIneq r}

/-- The claim: `K₂ ≥ 0.301657`. -/
def K2Claim : Prop := (301657 / 1000000 : ℝ) ≤ K2

end Bohr59a
