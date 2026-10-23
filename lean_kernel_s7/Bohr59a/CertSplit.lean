/-
Sub-box splits for the kernel-only proofs (heavy cells): the box property `BoxOK`, its assembly from the leaf boxes of a
top tree (`boxOK_of_boxesOf`, the split case of `walkK2_sound` as a lemma), a box from its own kernel walk
(`boxOK_of_K2h`), and the half-domain cell property from a split of the root box (`cellOKH_of_boxesOf`).
-/
import Bohr59a.CertK
import Bohr59a.CertHalf
import Bohr59aCoreK.Split

namespace Bohr59a.CertK

open Bohr59a.Cert Bohr59aCore Bohr59aK

/-- every phase point of the box (centres `ms/512`, half-widths `2^-js`) satisfies `VProp` -/
def BoxOK (D : ℕ) (B : ℝ) (ms : List ℤ) (js : List ℕ) : Prop :=
  ∀ φ, InBox D ms js φ → VProp (D + 1) B (wPhase D φ)

/-- **Assembly of a split box**: if every leaf box of the top tree has the box property, so does the box. -/
theorem boxOK_of_boxesOf {D : ℕ} {B : ℝ} : ∀ (t : Tree) (ms : List ℤ) (js : List ℕ) (bs : List (List ℤ × List ℕ)),
    ms.length = D → js.length = D → boxesOf t ms js = some bs → (∀ b ∈ bs, BoxOK D B b.1 b.2) → BoxOK D B ms js
  | .leaf, ms, js, bs, _, _, h, hb => by
    unfold boxesOf at h
    simp only [Option.some.injEq] at h
    subst h
    exact hb (ms, js) (by simp)
  | .split d lo hi, ms, js, bs, hms, hjs, h, hb => by
    unfold boxesOf at h
    split_ifs at h with hc
    obtain ⟨hd1, hd2, hj8⟩ := hc
    split at h
    · rename_i a b hlo hhi
      simp only [Option.some.injEq] at h
      subst h
      rw [getElem!_eq_getD', getElem!_eq_getD'] at hlo hhi
      rw [getElem!_eq_getD'] at hj8
      have hdD : d < D := by omega
      intro φ hφ
      rcases split_child hdD hd1 hd2 hj8 hφ with hφ' | hφ'
      · exact boxOK_of_boxesOf lo _ _ a (by simp [hms]) (by simp [hjs]) hlo
          (fun x hx => hb x (List.mem_append_left _ hx)) φ hφ'
      · exact boxOK_of_boxesOf hi _ _ b (by simp [hms]) (by simp [hjs]) hhi
          (fun x hx => hb x (List.mem_append_right _ hx)) φ hφ'
    · exact absurd h (by simp)

/-- a box from its kernel walk and the vertex links (per-leaf key lists, hints given as data) -/
theorem boxOK_of_K2h {D k bnum bden : ℕ} (hk : k = D + 1) (hbden : 0 < bden) {ms : List ℤ} {js : List ℕ} {t : Tree}
    {kls : List (List (List Comp))} (hms : ms.length = D) (hjs : js.length = D) (hw : walkK2 t ms js kls = some [])
    (hv : allP (allP (fun key => ∃ Y Wr x, vertexOKKh trigTT k bnum bden key Y Wr x = true)) kls) :
    BoxOK D ((bnum : ℝ) / bden) ms js := by
  subst hk
  intro φ hφ
  exact walkK2_sound (fun key ⟨_, _, _, hY⟩ => vertexOKKh_sound hbden hY) t _ _ kls [] hms hjs hw hv φ hφ

/-- the half-domain cell property from a split of the root box and the box property of every leaf box -/
theorem cellOKH_of_boxesOf {D : ℕ} {B : ℝ} {i : ℕ} {t : Tree} {bs : List (List ℤ × List ℕ)}
    (h : boxesOf t (rootMsH D i) (List.replicate (D + 1) 2) = some bs)
    (hb : allP (fun b : List ℤ × List ℕ => BoxOK (D + 1) B b.1 b.2) bs) : CellOKH D B i :=
  boxOK_of_boxesOf t _ _ bs (length_rootMsH D i) (by simp) h ((allP_iff bs).1 hb)

end Bohr59a.CertK
