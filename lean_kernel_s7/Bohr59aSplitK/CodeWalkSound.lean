import Bohr59aSplitK.CodeWalk
import Bohr59aSplitK.Glue7
import Bohr59a.CertHalfK

/-!
# Boxes and cells from code walks (k = 7)

A sub-box of a heavy cell (`boxOK7C`, via `boxOK7`) and a whole half-domain cell (`cellOK_of_KC7`, via
`Bohr59a.CertK.cellOK_of_K2hH`) follow from a code walk (`walkKC`) and the links of its codes in the fast form
(`allP (allP PF7C)`), through `walkKC_walkK2` and `allP_mapC2` (`Bohr59aSplitK/CodeWalk.lean`).
-/

namespace Bohr59aSplitK

open Bohr59a.Cert Bohr59a.CertK Bohr59aK Bohr59aCore

/-- a sub-box of a k = 7 cell from its code walk and the links of its codes -/
theorem boxOK7C {ms : List ℤ} {js : List ℕ} {t : Tree} {cls : List (List ℕ)}
    (hw : walkKC t ms js cls = some []) (hv : allP (allP PF7C) cls)
    (hms : ms.length = 6 := by rfl) (hjs : js.length = 6 := by rfl) :
    BoxOK 6 (((2552 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)) ms js :=
  boxOK7 (by simpa using walkKC_walkK2 t ms js cls [] hw) (allP_mapC2 hv) hms hjs

/-- a half-domain k = 7 cell (no split) from its code walk and the links of its codes -/
theorem cellOK_of_KC7 {i : ℕ} {t : Tree} {cls : List (List ℕ)}
    (hw : walkKC t (rootMsH 5 i) (List.replicate 6 2) cls = some []) (hv : allP (allP PF7C) cls) :
    CellOKH 5 (((2552 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)) i :=
  cellOK_of_K2hH (k := 7) rfl (by norm_num) (by simpa using walkKC_walkK2 _ _ _ cls [] hw)
    (allP_mono (fun _ => allP_mono fun _ h => h.elim fun _ h' => exists_of_vertexOKKpF3 h') (allP_mapC2 hv))

end Bohr59aSplitK
