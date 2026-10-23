/-
The kernel cell property on the half domain (for a kernel-only k = 7 proof): the half-grid analogue of
`Bohr59a.CertK.cellOK_of_K2h`, from a `walkK2` theorem over `rootMsH` and the per-leaf links.
-/
import Bohr59a.CertK
import Bohr59a.CertHalf

namespace Bohr59a.CertK

open Bohr59a.Cert Bohr59aCore Bohr59aK

/-- The half-domain cell property from the kernel walk of the cell's tree and the vertex links (per-leaf key lists). -/
theorem cellOK_of_K2hH {D k bnum bden : ℕ} (hk : k = D + 1 + 1) (hbden : 0 < bden) {i : ℕ} {t : Tree}
    {kls : List (List (List Comp))} (hw : walkK2 t (rootMsH D i) (List.replicate (D + 1) 2) kls = some [])
    (hv : allP (allP (fun key => ∃ Y Wr x, vertexOKKh trigTT k bnum bden key Y Wr x = true)) kls) :
    CellOKH D ((bnum : ℝ) / bden) i := by
  subst hk
  intro φ hφ
  exact walkK2_sound (fun key ⟨_, _, _, hY⟩ => vertexOKKh_sound hbden hY) t _ _ kls []
    (length_rootMsH D i) (by simp) hw hv φ hφ

end Bohr59a.CertK
