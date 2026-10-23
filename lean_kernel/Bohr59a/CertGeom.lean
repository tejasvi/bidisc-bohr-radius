/-
Geometry of the certificate: the arc in the triangle (Lemma 3 (d)), leaves (the best vertex), the split trees, root cells
and their coverage of `[-1, 1]^D`, and the normalization `w₀ = w₁ = 1` (Lemma 3 (a)).
-/
import Bohr59a.CertVertex
import Bohr59a.Slice

open Complex Real Finset

namespace Bohr59a.Cert

open Bohr59aCore

/-- `e^{iθ}` -/
noncomputable def cis (θ : ℝ) : ℂ := cexp ((θ : ℂ) * I)

lemma cis_re (θ : ℝ) : (cis θ).re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ

lemma cis_im (θ : ℝ) : (cis θ).im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ

lemma cis_add (a b : ℝ) : cis (a + b) = cis a * cis b := by
  unfold cis; rw [← Complex.exp_add]; push_cast; ring_nf

lemma norm_cis (θ : ℝ) : ‖cis θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

/-- **Lemma 3 (d)**: for `|δ| ≤ H ≤ π/4`, `e^{iδ}` is a convex combination of `e^{-iH}`, `e^{iH}` and `1/cos H`. -/
lemma arc_in_triangle {δ H : ℝ} (hH0 : 0 < H) (hH1 : H ≤ π / 4) (hδ : |δ| ≤ H) :
    ∃ l1 l2 l3 : ℝ, 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ l1 + l2 + l3 = 1 ∧
      cis δ = (l1 : ℂ) * cis (-H) + (l2 : ℂ) * cis H + (l3 : ℂ) * ((1 / Real.cos H : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos H := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : 0 < Real.sin H := Real.sin_pos_of_pos_of_lt_pi hH0 (by linarith)
  have hsc := Real.sin_sq_add_cos_sq H
  have hs2 : 0 < Real.sin H ^ 2 := by positivity
  set s := (1 - Real.cos δ * Real.cos H) / Real.sin H ^ 2 with hs
  set d := Real.sin δ / Real.sin H with hd
  have hsd1 : s - d = (1 - Real.cos (δ - H)) / Real.sin H ^ 2 := by
    rw [Real.cos_sub, hs, hd]; field_simp; ring
  have hsd2 : s + d = (1 - Real.cos (δ + H)) / Real.sin H ^ 2 := by
    rw [Real.cos_add, hs, hd]; field_simp; ring
  have hcδ : Real.cos H ≤ Real.cos δ := by
    rw [← Real.cos_abs δ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg δ) (by linarith) hδ
  refine ⟨(s - d) / 2, (s + d) / 2, 1 - s, ?_, ?_, ?_, by ring, ?_⟩
  · rw [hsd1]; have := Real.cos_le_one (δ - H); positivity
  · rw [hsd2]; have := Real.cos_le_one (δ + H); positivity
  · rw [hs, sub_nonneg, div_le_one hs2]
    nlinarith
  · have hre : (s - d) / 2 * Real.cos H + (s + d) / 2 * Real.cos H + (1 - s) * (1 / Real.cos H) = Real.cos δ := by
      have e1 : (s - d) / 2 * Real.cos H + (s + d) / 2 * Real.cos H = s * Real.cos H := by ring
      have e2 : s * Real.sin H ^ 2 = 1 - Real.cos δ * Real.cos H := by rw [hs]; field_simp
      rw [e1]
      have e3 : s * Real.cos H + (1 - s) * (1 / Real.cos H) = (s * Real.cos H ^ 2 + 1 - s) / Real.cos H := by
        field_simp; ring
      rw [e3, div_eq_iff hcos.ne']
      linear_combination -e2 + s * hsc
    have him : (s - d) / 2 * -Real.sin H + (s + d) / 2 * Real.sin H = Real.sin δ := by
      rw [hd]; field_simp; ring
    apply Complex.ext
    · simp only [cis_re, Complex.add_re, Complex.re_ofReal_mul, Real.cos_neg, Complex.ofReal_re]
      linarith [hre]
    · simp only [cis_im, Complex.add_im, Complex.im_ofReal_mul, Real.sin_neg, Complex.ofReal_im, mul_zero,
        add_zero]
      linarith [him]

/-- the best of the three triangle vertices for the linear functional `p ↦ Re(p̄ a)` -/
lemma triangle_best {δ H : ℝ} (hH0 : 0 < H) (hH1 : H ≤ π / 4) (hδ : |δ| ≤ H) (a : ℂ) :
    (star (cis δ) * a).re ≤ (star (cis (-H)) * a).re ∨ (star (cis δ) * a).re ≤ (star (cis H) * a).re ∨
      (star (cis δ) * a).re ≤ (star (((1 / Real.cos H : ℝ) : ℂ)) * a).re := by
  obtain ⟨l1, l2, l3, h1, h2, h3, hsum, he⟩ := arc_in_triangle hH0 hH1 hδ
  have key : (star (cis δ) * a).re = l1 * (star (cis (-H)) * a).re + l2 * (star (cis H) * a).re +
      l3 * (star (((1 / Real.cos H : ℝ) : ℂ)) * a).re := by
    rw [he]
    simp only [star_add, star_mul', Complex.star_def, Complex.conj_ofReal, add_mul, mul_assoc, Complex.add_re,
      Complex.re_ofReal_mul]
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  set X := (star (cis δ) * a).re
  set A := (star (cis (-H)) * a).re
  set B := (star (cis H) * a).re
  set C := (star (((1 / Real.cos H : ℝ) : ℂ)) * a).re
  set m := min (min (X - A) (X - B)) (X - C) with hm_def
  have hm : 0 < m := lt_min (lt_min (sub_pos.2 c1) (sub_pos.2 c2)) (sub_pos.2 c3)
  have t1 : l1 * m ≤ l1 * (X - A) :=
    mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (min_le_left _ _)) h1
  have t2 : l2 * m ≤ l2 * (X - B) :=
    mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (min_le_right _ _)) h2
  have t3 : l3 * m ≤ l3 * (X - C) := mul_le_mul_of_nonneg_left (min_le_right _ _) h3
  have sm : l1 * m + l2 * m + l3 * m = m := by rw [← add_mul, ← add_mul, hsum, one_mul]
  have sX : l1 * X + l2 * X + l3 * X = X := by rw [← add_mul, ← add_mul, hsum, one_mul]
  nlinarith

lemma coordC_corner (m : ℤ) : coordC ⟨false, m, 0⟩ = cis (π * m / 512) := by
  unfold coordC cis; simp

/-- the vertex options of a coordinate: corners at `π(m ∓ 2^{9-j})/512` and the tangent point -/
lemma coordC_opts {m : ℤ} {j : ℕ} (hj : j ≤ 9) :
    coordC ⟨false, m - 2 ^ (9 - j), 0⟩ = cis (π * m / 512) * cis (-(π / 2 ^ j)) ∧
    coordC ⟨false, m + 2 ^ (9 - j), 0⟩ = cis (π * m / 512) * cis (π / 2 ^ j) ∧
    coordC ⟨true, m, j⟩ = cis (π * m / 512) * ((1 / Real.cos (π / 2 ^ j) : ℝ) : ℂ) := by
  have h2 : ((2 : ℝ) ^ (9 - j)) / 512 = 1 / 2 ^ j := by
    rw [show (512 : ℝ) = 2 ^ (9 - j) * 2 ^ j by rw [← pow_add, Nat.sub_add_cancel hj]; norm_num]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [coordC_corner, ← cis_add]
    congr 1
    push_cast
    rw [show π * ((m : ℝ) - 2 ^ (9 - j)) / 512 = π * m / 512 - π * (2 ^ (9 - j) / 512) by ring, h2]
    ring
  · rw [coordC_corner, ← cis_add]
    congr 1
    push_cast
    rw [show π * ((m : ℝ) + 2 ^ (9 - j)) / 512 = π * m / 512 + π * (2 ^ (9 - j) / 512) by ring, h2]
    ring
  · unfold coordC; simp only [↓reduceIte]
    unfold cis; push_cast; ring

/-- In a leaf coordinate (`2 ≤ j ≤ 9`, `|ψ - m/512| ≤ 2^{-j}`) some option beats `e^{iπψ}`. -/
lemma opt_best {m : ℤ} {j : ℕ} (hj2 : 2 ≤ j) (hj9 : j ≤ 9) {ψ : ℝ} (hψ : |ψ - m / 512| ≤ 1 / 2 ^ j) (a : ℂ) :
    ∃ o ∈ opts m j, (star (cis (π * ψ)) * a).re ≤ (star (coordC o) * a).re := by
  obtain ⟨e1, e2, e3⟩ := coordC_opts (m := m) hj9
  have hpi := Real.pi_pos
  have hH0 : 0 < π / 2 ^ j := by positivity
  have hH1 : π / 2 ^ j ≤ π / 4 := by
    apply div_le_div_of_nonneg_left hpi.le (by norm_num)
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj2
  have hδ : |π * ψ - π * m / 512| ≤ π / 2 ^ j := by
    rw [show π * ψ - π * m / 512 = π * (ψ - m / 512) by ring, abs_mul, abs_of_pos hpi]
    calc π * |ψ - m / 512| ≤ π * (1 / 2 ^ j) := mul_le_mul_of_nonneg_left hψ hpi.le
      _ = π / 2 ^ j := by ring
  have hrot : cis (π * ψ) = cis (π * m / 512) * cis (π * ψ - π * m / 512) := by rw [← cis_add]; ring_nf
  have hb := triangle_best hH0 hH1 hδ (star (cis (π * m / 512)) * a)
  have hre : ∀ t : ℂ, (star t * (star (cis (π * m / 512)) * a)).re = (star (cis (π * m / 512) * t) * a).re := by
    intro t; rw [star_mul', mul_comm (star (cis _)) (star t), mul_assoc]
  have hl : (star (cis (π * ψ)) * a).re = (star (cis (π * ψ - π * m / 512)) * (star (cis (π * m / 512)) * a)).re := by
    rw [hre, ← hrot]
  rw [← hl, hre (cis (-(π / 2 ^ j))), hre (cis (π / 2 ^ j)), hre (((1 / Real.cos (π / 2 ^ j) : ℝ) : ℂ))] at hb
  rcases hb with hb | hb | hb
  · exact ⟨⟨false, m - 2 ^ (9 - j), 0⟩, by simp [opts], by rw [e1]; exact hb⟩
  · exact ⟨⟨false, m + 2 ^ (9 - j), 0⟩, by simp [opts], by rw [e2]; exact hb⟩
  · exact ⟨⟨true, m, j⟩, by simp [opts], by rw [e3]; exact hb⟩


/-! ### Leaves and trees -/

/-- the phase vector `(1, 1, e^{iπφ_0}, …, e^{iπφ_{D-1}})` -/
noncomputable def wPhase (D : ℕ) (φ : Fin D → ℝ) : Fin (D + 1 + 1) → ℂ :=
  Fin.cons 1 (Fin.cons 1 fun d => cis (π * φ d))

/-- `φ` lies in the box with centres `ms/512` and half-widths `2^{-js}` -/
def InBox (D : ℕ) (ms : List ℤ) (js : List ℕ) (φ : Fin D → ℝ) : Prop :=
  ∀ d : Fin D, |φ d - (ms.getD d 0 : ℝ) / 512| ≤ 1 / 2 ^ (js.getD d 0)

lemma getElem!_eq_getD' {α : Type*} [Inhabited α] (l : List α) (i : ℕ) : l[i]! = l.getD i default := by
  rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

lemma getD_set_eq {α : Type*} (l : List α) (i : ℕ) (a d : α) (hi : i < l.length) : (l.set i a).getD i d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]; rfl

lemma getD_set_ne {α : Type*} (l : List α) {i j : ℕ} (a d : α) (h : i ≠ j) : (l.set i a).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

lemma allVerts_sound (f : List Comp → Bool) : ∀ (os : List (List Comp)) (acc : List Comp),
    allVerts f os acc = true → ∀ cs, List.Forall₂ (fun c o => c ∈ o) cs os → f (acc.reverse ++ cs) = true
  | [], acc, h, cs, hcs => by
    rw [List.forall₂_nil_right_iff] at hcs
    subst hcs
    simpa [allVerts] using h
  | o :: os, acc, h, cs, hcs => by
    cases hcs with
    | cons hc hcs' =>
      rename_i c cs'
      unfold allVerts at h
      have h1 := List.all_eq_true.1 h c hc
      have := allVerts_sound f os (c :: acc) h1 cs' hcs'
      simpa [List.reverse_cons, List.append_assoc] using this

/-- **Leaves**: if every vertex key of a leaf has the vertex property, so does every phase vector in the box. -/
lemma leaf_sound {D : ℕ} {B : ℝ} {f : List Comp → Bool} (hf : ∀ key, f key = true → VProp (D + 1) B (vtx D key))
    {ms : List ℤ} {js : List ℕ} (hms : ms.length = D) (h : leafOK f ms js = true) {φ : Fin D → ℝ}
    (hφ : InBox D ms js φ) : VProp (D + 1) B (wPhase D φ) := by
  unfold leafOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hjs⟩, hall⟩ := h
  have hjsD : js.length = D := by omega
  have hj : ∀ d : Fin D, 2 ≤ js.getD d 0 ∧ js.getD d 0 ≤ 9 := fun d => by
    have hd : d.val < js.length := by omega
    have := hjs (js.getD d 0) (by rw [List.getD_eq_getElem _ _ hd]; exact List.getElem_mem hd)
    exact this
  intro c M hM
  -- the best option in each coordinate
  have hbest : ∀ d : Fin D, ∃ o ∈ opts (ms.getD d 0) (js.getD d 0),
      (star (cis (π * φ d)) * c d.succ.succ).re ≤ (star (coordC o) * c d.succ.succ).re := fun d =>
    opt_best (hj d).1 (hj d).2 (hφ d) _
  choose ch hch hle using hbest
  set cs := List.ofFn ch with hcs
  have hF : List.Forall₂ (fun c o => c ∈ o) cs (List.zipWith opts ms js) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [hcs, hms, hjsD], fun i h1 h2 => ?_⟩
    have hiD : i < D := by simpa [hcs] using h1
    simp only [List.get_eq_getElem, hcs, List.getElem_ofFn, List.getElem_zipWith]
    have e1 : ms[i]'(by omega) = ms.getD i 0 := (List.getD_eq_getElem _ _ (by omega)).symm
    have e2 : js[i]'(by omega) = js.getD i 0 := (List.getD_eq_getElem _ _ (by omega)).symm
    rw [e1, e2]
    exact hch ⟨i, hiD⟩
  have hkey := allVerts_sound f _ [] hall cs hF
  simp only [List.reverse_nil, List.nil_append] at hkey
  have hV := hf cs hkey c M hM
  refine le_trans ?_ hV
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [wPhase, vtx, Fin.cons_zero, Fin.cons_succ, Complex.add_re, Complex.re_sum]
  have hd : ∀ d : Fin D, cs.getD d.val default = ch d := fun d => by
    rw [List.getD_eq_getElem?_getD]; simp [hcs]
  simp only [hd]
  have := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => hle d)
  linarith

lemma walk_sound {D : ℕ} {B : ℝ} {f : List Comp → Bool} (hf : ∀ key, f key = true → VProp (D + 1) B (vtx D key)) :
    ∀ (t : Tree) (ms : List ℤ) (js : List ℕ), ms.length = D → js.length = D → walk f t ms js = true →
      ∀ φ, InBox D ms js φ → VProp (D + 1) B (wPhase D φ)
  | .leaf, ms, js, hms, _, h, φ, hφ => leaf_sound hf hms h hφ
  | .split d lo hi, ms, js, hms, hjs, h, φ, hφ => by
    unfold walk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hd1, hd2⟩, hj8⟩, hlo⟩, hhi⟩ := h
    rw [getElem!_eq_getD', getElem!_eq_getD'] at hlo hhi
    rw [getElem!_eq_getD'] at hj8
    set j := js.getD d default with hjdef
    set m := ms.getD d default with hmdef
    have hdD : d < D := by omega
    have hφd := hφ ⟨d, hdD⟩
    simp only [] at hφd
    have hdef : (default : ℤ) = 0 := rfl
    have hdefn : (default : ℕ) = 0 := rfl
    rw [← hdef] at hφd
    rw [← hdefn] at hφd
    have h2 : ((2 : ℝ) ^ (8 - j)) / 512 = 1 / 2 ^ (j + 1) := by
      rw [show (512 : ℝ) = 2 ^ (8 - j) * 2 ^ (j + 1) by
        rw [← pow_add, show 8 - j + (j + 1) = 9 by omega]; norm_num]
      field_simp
    have hhalf : (1 : ℝ) / 2 ^ j = 2 * (1 / 2 ^ (j + 1)) := by rw [pow_succ]; field_simp
    -- the child boxes
    have child : ∀ (σ : ℤ), (σ = -1 ∨ σ = 1) → (σ * (φ ⟨d, hdD⟩ - m / 512) ≥ 0) →
        InBox D (ms.set d (m + σ * 2 ^ (8 - j))) (js.set d (j + 1)) φ := by
      intro σ hσ hside e
      by_cases hed : e.val = d
      · have he : e = ⟨d, hdD⟩ := Fin.ext hed
        subst he
        simp only []
        rw [getD_set_eq _ _ _ _ (by omega), getD_set_eq _ _ _ _ (by omega)]
        push_cast
        rw [show ((m : ℝ) + σ * 2 ^ (8 - j)) / 512 = m / 512 + σ * (2 ^ (8 - j) / 512) by ring, h2]
        rw [hhalf] at hφd
        rcases hσ with rfl | rfl
        · push_cast at hside ⊢
          rw [abs_le] at hφd ⊢
          constructor <;> nlinarith
        · push_cast at hside ⊢
          rw [abs_le] at hφd ⊢
          constructor <;> nlinarith
      · rw [getD_set_ne _ _ _ (Ne.symm hed), getD_set_ne _ _ _ (Ne.symm hed)]
        exact hφ e
    by_cases hs : φ ⟨d, hdD⟩ ≤ m / 512
    · have hb := child (-1) (Or.inl rfl) (by push_cast; linarith)
      have e : m + (-1 : ℤ) * 2 ^ (8 - j) = m - 2 ^ (8 - j) := by ring
      rw [e] at hb
      exact walk_sound hf lo _ _ (by simp [hms]) (by simp [hjs]) hlo φ hb
    · have hb := child 1 (Or.inr rfl) (by push_cast; linarith)
      have e : m + (1 : ℤ) * 2 ^ (8 - j) = m + 2 ^ (8 - j) := by ring
      rw [e] at hb
      exact walk_sound hf hi _ _ (by simp [hms]) (by simp [hjs]) hhi φ hb


/-! ### Root cells and their coverage -/

/-- Horner encoding of base-`8` digits, most significant first -/
def enc8 (L : List ℕ) : ℕ := L.foldl (fun acc a => 8 * acc + a) 0

lemma enc8_concat (L : List ℕ) (a : ℕ) : enc8 (L ++ [a]) = 8 * enc8 L + a := by
  simp [enc8, List.foldl_append]

lemma length_digits8 : ∀ (D i : ℕ), (digits8 D i).length = D
  | 0, _ => rfl
  | D + 1, i => by simp [digits8, length_digits8 D]

lemma digits8_enc8 : ∀ (L : List ℕ), (∀ a ∈ L, a < 8) → digits8 L.length (enc8 L) = L ∧ enc8 L < 8 ^ L.length := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; simp [digits8, enc8]
  | append_singleton L a ih =>
    intro hL
    have ha : a < 8 := hL a (by simp)
    obtain ⟨h1, h2⟩ := ih fun b hb => hL b (by simp [hb])
    rw [List.length_append, List.length_singleton, enc8_concat]
    refine ⟨?_, ?_⟩
    · simp only [digits8]
      have e1 : (8 * enc8 L + a) / 8 = enc8 L := by omega
      have e2 : (8 * enc8 L + a) % 8 = a := by omega
      rw [e1, e2, h1]
    · rw [pow_succ]; omega

/-- the cell property of root cell `i` -/
def CellOK (D : ℕ) (B : ℝ) (i : ℕ) : Prop :=
  ∀ φ, InBox D (rootMs D i) (List.replicate D 3) φ → VProp (D + 1) B (wPhase D φ)

/-- every point of `[-1, 1]^D` lies in a root cell -/
lemma root_cover {D : ℕ} (φ : Fin D → ℝ) (hφ : ∀ d, |φ d| ≤ 1) :
    ∃ i < 8 ^ D, InBox D (rootMs D i) (List.replicate D 3) φ := by
  set a : Fin D → ℕ := fun d => min 7 ⌊(φ d + 1) * 4⌋₊ with ha
  have ha8 : ∀ d, a d < 8 := fun d => by simp only [ha]; omega
  have hbox : ∀ d, (a d : ℝ) ≤ (φ d + 1) * 4 ∧ (φ d + 1) * 4 ≤ a d + 1 := by
    intro d
    have h1 := (abs_le.1 (hφ d)).1
    have h2 := (abs_le.1 (hφ d)).2
    have hu0 : 0 ≤ (φ d + 1) * 4 := by linarith
    have hfl := Nat.floor_le hu0
    have hfl2 := Nat.lt_floor_add_one ((φ d + 1) * 4)
    simp only [ha]
    rcases le_total ⌊(φ d + 1) * 4⌋₊ 7 with hle | hle
    · rw [min_eq_right hle]
      exact ⟨hfl, hfl2.le⟩
    · rw [min_eq_left hle]
      constructor
      · have : ((7 : ℕ) : ℝ) ≤ ⌊(φ d + 1) * 4⌋₊ := by exact_mod_cast hle
        push_cast at this ⊢; linarith
      · push_cast; linarith
  set L := List.ofFn a with hL
  have hLa : ∀ x ∈ L, x < 8 := fun x hx => by
    rw [hL, List.mem_ofFn] at hx
    obtain ⟨d, rfl⟩ := hx
    exact ha8 d
  obtain ⟨h1, h2⟩ := digits8_enc8 L hLa
  have hlen : L.length = D := by simp [hL]
  rw [hlen] at h1 h2
  refine ⟨enc8 L, h2, fun d => ?_⟩
  have hd1 : (rootMs D (enc8 L)).getD d 0 = -512 + (2 * (a d : ℤ) + 1) * 64 := by
    unfold rootMs
    rw [h1, List.getD_eq_getElem?_getD]
    simp [hL]
  have hd2 : (List.replicate D 3).getD d 0 = 3 := by
    rw [List.getD_eq_getElem?_getD]; simp
  rw [hd1, hd2]
  push_cast
  obtain ⟨b1, b2⟩ := hbox d
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Normalization (Lemma 3 (a)) -/

/-- **Lemma 3 (a)**: the vertex property at every phase vector of `[-1, 1]^D` gives the Sidon bound. -/
theorem sidon_of_phases {D : ℕ} {B : ℝ}
    (h : ∀ φ : Fin D → ℝ, (∀ d, |φ d| ≤ 1) → VProp (D + 1) B (wPhase D φ)) : SidonBound (D + 1) B := by
  intro c M hM
  have hσ : ∀ j, ∃ σ : ℂ, ‖σ‖ = 1 ∧ (‖c j‖ : ℂ) = σ * c j := fun j => Complex.exists_norm_eq_mul_self (c j)
  choose σ hσ1 hσc using hσ
  have hconj : ∀ z : ℂ, ‖z‖ = 1 → star z * z = 1 := fun z hz => by
    rw [Complex.star_def, Complex.conj_mul', hz]; simp
  set α := σ 0 with hα
  set β := σ 1 * star (σ 0) with hβ
  have hα1 : ‖α‖ = 1 := hσ1 0
  have hβ1 : ‖β‖ = 1 := by rw [hβ, norm_mul, norm_star, hσ1, hσ1, one_mul]
  set w : Fin (D + 1 + 1) → ℂ := fun j => star (σ j) * α * β ^ (j : ℕ) with hw
  set c' : Fin (D + 1 + 1) → ℂ := fun j => α * β ^ (j : ℕ) * c j with hc'
  have hw1 : ∀ j, ‖w j‖ = 1 := fun j => by
    simp only [hw, norm_mul, norm_star, norm_pow, hσ1, hα1, hβ1, one_pow, one_mul]
  have hM' : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ j, c' j * z ^ (j : ℕ)‖ ≤ M := by
    intro z hz
    have e : ∑ j, c' j * z ^ (j : ℕ) = α * ∑ j, c j * (β * z) ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [hc']; rw [mul_pow]; ring
    rw [e, norm_mul, hα1, one_mul]
    exact hM _ (by rw [norm_mul, hβ1, hz, one_mul])
  -- the phases of `w`
  set φ : Fin D → ℝ := fun d => Complex.arg (w d.succ.succ) / π with hφ
  have hφ1 : ∀ d, |φ d| ≤ 1 := fun d => by
    simp only [hφ]
    rw [abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos, abs_le]
    exact ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hwP : wPhase D φ = w := by
    funext j
    refine Fin.cases ?_ (fun j' => Fin.cases ?_ (fun d => ?_) j') j
    · simp only [wPhase, Fin.cons_zero, hw, Fin.val_zero, pow_zero, mul_one]
      rw [hα, hconj _ (hσ1 0)]
    · have e1 : wPhase D φ (Fin.succ 0) = 1 := by simp only [wPhase, Fin.cons_succ, Fin.cons_zero]
      have e2 : w (Fin.succ 0) = star (σ 1) * σ 0 * (σ 1 * star (σ 0)) := by
        simp only [hw, hα, hβ, Fin.succ_zero_eq_one, Fin.val_one, pow_one]
      rw [e1, e2]
      have h0 := hconj _ (hσ1 0)
      have h1 := hconj _ (hσ1 1)
      have e : star (σ 1) * σ 0 * (σ 1 * star (σ 0)) = (star (σ 1) * σ 1) * (star (σ 0) * σ 0) := by ring
      rw [e, h0, h1, one_mul]
    · simp only [wPhase, Fin.cons_succ, hφ]
      have hpi := Real.pi_pos.ne'
      rw [show π * (Complex.arg (w d.succ.succ) / π) = Complex.arg (w d.succ.succ) by field_simp]
      have := Complex.norm_mul_exp_arg_mul_I (w d.succ.succ)
      rw [hw1, Complex.ofReal_one, one_mul] at this
      exact this
  have hV := h φ hφ1 c' M hM'
  rw [hwP] at hV
  have e : ∑ j, star (w j) * c' j = ∑ j, ((‖c j‖ : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hw, hc', star_mul', star_star, star_pow]
    rw [hσc j]
    have hα' := hconj α hα1
    have hβ' : star β ^ (j : ℕ) * β ^ (j : ℕ) = 1 := by rw [← mul_pow, hconj β hβ1, one_pow]
    calc σ j * star α * star β ^ (j : ℕ) * (α * β ^ (j : ℕ) * c j)
        = (star α * α) * (star β ^ (j : ℕ) * β ^ (j : ℕ)) * (σ j * c j) := by ring
      _ = σ j * c j := by rw [hα', hβ', one_mul, one_mul]
  rw [e, Complex.re_sum] at hV
  simpa using hV

end Bohr59a.Cert
