import Bohr59a.CertSplit
import Bohr59a.CertFast3
import Bohr59aSplitK.Pred

/-!
# Glue for the split k = 7 cells

`boxOK7`: one sub-box of a heavy cell has the box property, from its kernel walk (`walkK2 … = some []`) and its
per-leaf links in the fast form (`allP (allP PF7)`), via `Bohr59a.CertK.boxOK_of_K2h` and
`Bohr59aK.exists_of_vertexOKKpF3`. The generated cell modules then apply `Bohr59a.CertK.cellOKH_of_boxesOf`.
-/

namespace Bohr59aSplitK

open Bohr59a.CertK Bohr59aK Bohr59aCore

theorem allP_mono {α : Type} {P Q : α → Prop} (h : ∀ a, P a → Q a) : ∀ {l : List α}, allP P l → allP Q l
  | [], _ => trivial
  | _ :: _, hl => ⟨h _ hl.1, allP_mono h hl.2⟩

/-- a sub-box of a k = 7 cell from its kernel walk and the links of its leaves -/
theorem boxOK7 {ms : List ℤ} {js : List ℕ} {t : Tree} {kls : List (List (List Comp))}
    (hw : walkK2 t ms js kls = some []) (hv : allP (allP PF7) kls)
    (hms : ms.length = 6 := by rfl) (hjs : js.length = 6 := by rfl) :
    BoxOK 6 (((2552 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)) ms js :=
  boxOK_of_K2h (k := 7) rfl (by norm_num) hms hjs hw
    (allP_mono (fun _ => allP_mono fun _ h => h.elim fun _ h' => exists_of_vertexOKKpF3 h') hv)

end Bohr59aSplitK
