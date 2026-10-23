import Bohr59aCoreK.Walk

/-! `allP` of a concatenation, core Lean only (for chunked linking theorems in the generated cell modules). -/

namespace Bohr59aK

theorem allP_app {α : Type} {P : α → Prop} : ∀ {l₁ l₂ : List α}, allP P l₁ → allP P l₂ → allP P (l₁ ++ l₂)
  | [], _, _, h₂ => h₂
  | _ :: l, _, h₁, h₂ => ⟨h₁.1, allP_app (l₁ := l) h₁.2 h₂⟩

end Bohr59aK
