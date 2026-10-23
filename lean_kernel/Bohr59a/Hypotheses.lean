/-
Named hypotheses of the `K₂ ≥ 0.301657` proof (Mathlib definitions only).  Only `PatelColligation` is meant to remain in the final
theorem; it is Patel's colligation estimate (MathDB problem 392062, Section 1, the third boxed estimate), whose proof uses Andô's
theorem (Schur class = Schur–Agler class on the bidisc) and Agler's unitary-colligation realization, neither in Mathlib.
-/
import Bohr59a.Statement

namespace Bohr59a

/-- The coefficient families `h : ℕ × ℕ → ℂ` of the holomorphic functions `H` on the open bidisc with `H(0,0) = 1` and
`Re H > 0`: `H(z,w) = Σ_α h_α z^{α₁} w^{α₂}` converges (unconditionally, i.e. absolutely) at every point of the open bidisc,
its value has positive real part, and the constant coefficient is `1`. -/
def PosReClass (h : ℕ × ℕ → ℂ) : Prop :=
  h (0, 0) = 1 ∧ ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 →
    ∃ v : ℂ, HasSum (fun α : ℕ × ℕ => h α * z ^ α.1 * w ^ α.2) v ∧ 0 < v.re

/-- Patel's colligation estimate: `A₃ + B₂²/2 ≤ 2`, where `A₃ = |h₃₀| + |h₀₃|` and `B₂ = |h₁₁|`. -/
def PatelColligation : Prop :=
  ∀ h : ℕ × ℕ → ℂ, PosReClass h → ‖h (3, 0)‖ + ‖h (0, 3)‖ + ‖h (1, 1)‖ ^ 2 / 2 ≤ 2

end Bohr59a
