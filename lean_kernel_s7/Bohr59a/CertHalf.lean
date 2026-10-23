/-
The half phase domain (the k = 7 certificate): conjugation symmetry (Lemma 3 (e)), the root cells of
`[0, 1] × [-1, 1]^D` and their coverage, the Sidon bound from the half-domain cells, and the soundness of the half-domain
shard check `Bohr59aCore.checkShardH`.
-/
import Bohr59a.CertShard
import Bohr59aCore.CheckHalf

open Complex Real Finset

namespace Bohr59a.Cert

open Bohr59aCore

/-! ### Conjugation (Lemma 3 (e)) -/

lemma cis_neg (θ : ℝ) : cis (-θ) = star (cis θ) := by
  unfold cis
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma wPhase_neg (D : ℕ) (φ : Fin D → ℝ) (j : Fin (D + 1 + 1)) :
    wPhase D (fun d => -φ d) j = star (wPhase D φ j) := by
  refine Fin.cases ?_ (fun j' => Fin.cases ?_ (fun d => ?_) j') j
  · simp [wPhase]
  · simp [wPhase]
  · simp only [wPhase, Fin.cons_succ]
    rw [show π * -φ d = -(π * φ d) by ring, cis_neg]

/-- **Lemma 3 (e)**: the vertex property at `-φ` gives it at `φ` (`c ↦ conj c` maps `q(z)` to `conj q(conj z)`). -/
theorem vprop_neg {D : ℕ} {B : ℝ} {φ : Fin D → ℝ} (h : VProp (D + 1) B (wPhase D fun d => -φ d)) :
    VProp (D + 1) B (wPhase D φ) := by
  intro c M hM
  have hM' : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ j, star (c j) * z ^ (j : ℕ)‖ ≤ M := by
    intro z hz
    have e : ∑ j, star (c j) * z ^ (j : ℕ) = star (∑ j, c j * star z ^ (j : ℕ)) := by
      rw [star_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [star_mul', star_pow, star_star]
    rw [e, norm_star]
    exact hM _ (by rw [norm_star, hz])
  have hV := h (fun j => star (c j)) M hM'
  have e : ∑ j, star (wPhase D (fun d => -φ d) j) * star (c j) = star (∑ j, star (wPhase D φ j) * c j) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [wPhase_neg, star_mul', star_star]
  rw [e, Complex.star_def, Complex.conj_re] at hV
  exact hV

/-! ### Root cells of the half domain -/

/-- Horner encoding of base-`4` digits, most significant first -/
def enc4 (L : List ℕ) : ℕ := L.foldl (fun acc a => 4 * acc + a) 0

lemma enc4_concat (L : List ℕ) (a : ℕ) : enc4 (L ++ [a]) = 4 * enc4 L + a := by
  simp [enc4, List.foldl_append]

lemma length_digits4 : ∀ (D i : ℕ), (digits4 D i).length = D
  | 0, _ => rfl
  | D + 1, i => by simp [digits4, length_digits4 D]

lemma digits4_enc4 : ∀ (L : List ℕ), (∀ a ∈ L, a < 4) → digits4 L.length (enc4 L) = L ∧ enc4 L < 4 ^ L.length := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; simp [digits4, enc4]
  | append_singleton L a ih =>
    intro hL
    have ha : a < 4 := hL a (by simp)
    obtain ⟨h1, h2⟩ := ih fun b hb => hL b (by simp [hb])
    rw [List.length_append, List.length_singleton, enc4_concat]
    refine ⟨?_, ?_⟩
    · simp only [digits4]
      have e1 : (4 * enc4 L + a) / 4 = enc4 L := by omega
      have e2 : (4 * enc4 L + a) % 4 = a := by omega
      rw [e1, e2, h1]
    · rw [pow_succ]; omega

lemma foldl_four (L : List ℕ) (x : ℕ) :
    L.foldl (fun acc a => 4 * acc + a) x = x * 4 ^ L.length + L.foldl (fun acc a => 4 * acc + a) 0 := by
  induction L generalizing x with
  | nil => simp
  | cons b L ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (4 * x + b), ih (4 * 0 + b), pow_succ]
    ring

lemma enc4_cons (a : ℕ) (L : List ℕ) : enc4 (a :: L) = a * 4 ^ L.length + enc4 L := by
  simp only [enc4, List.foldl_cons]
  rw [foldl_four L (4 * 0 + a)]
  ring

lemma length_rootMsH (D i : ℕ) : (rootMsH D i).length = D + 1 := by
  unfold rootMsH
  have h := length_digits4 (D + 1) i
  split
  · next h0 => rw [h0] at h; simp at h
  · next a rest h0 => rw [h0] at h; simpa using h

/-- the cell property of root cell `i` of the half domain (`D + 1` coordinates) -/
def CellOKH (D : ℕ) (B : ℝ) (i : ℕ) : Prop :=
  ∀ φ, InBox (D + 1) (rootMsH D i) (List.replicate (D + 1) 2) φ → VProp (D + 1 + 1) B (wPhase (D + 1) φ)

/-- every point of `[0, 1] × [-1, 1]^D` lies in a root cell of the half domain -/
lemma root_cover_half {D : ℕ} (φ : Fin (D + 1) → ℝ) (h0 : 0 ≤ φ 0) (hφ : ∀ d, |φ d| ≤ 1) :
    ∃ i < 2 * 4 ^ D, InBox (D + 1) (rootMsH D i) (List.replicate (D + 1) 2) φ := by
  -- the digits: `a` for the first coordinate (`< 2`), `b d` for the others (`< 4`)
  set a : ℕ := min 1 ⌊φ 0 * 2⌋₊ with ha
  set b : Fin D → ℕ := fun d => min 3 ⌊(φ d.succ + 1) * 2⌋₊ with hb
  have ha2 : a < 2 := by simp only [ha]; omega
  have hb4 : ∀ d, b d < 4 := fun d => by simp only [hb]; omega
  have hboxa : (a : ℝ) ≤ φ 0 * 2 ∧ φ 0 * 2 ≤ a + 1 := by
    have h2 := (abs_le.1 (hφ 0)).2
    have hu0 : 0 ≤ φ 0 * 2 := by linarith
    have hfl := Nat.floor_le hu0
    have hfl2 := Nat.lt_floor_add_one (φ 0 * 2)
    simp only [ha]
    rcases le_total ⌊φ 0 * 2⌋₊ 1 with hle | hle
    · rw [min_eq_right hle]
      exact ⟨hfl, hfl2.le⟩
    · rw [min_eq_left hle]
      constructor
      · have : ((1 : ℕ) : ℝ) ≤ ⌊φ 0 * 2⌋₊ := by exact_mod_cast hle
        push_cast at this ⊢; linarith
      · push_cast; linarith
  have hboxb : ∀ d, (b d : ℝ) ≤ (φ d.succ + 1) * 2 ∧ (φ d.succ + 1) * 2 ≤ b d + 1 := by
    intro d
    have h1 := (abs_le.1 (hφ d.succ)).1
    have h2 := (abs_le.1 (hφ d.succ)).2
    have hu0 : 0 ≤ (φ d.succ + 1) * 2 := by linarith
    have hfl := Nat.floor_le hu0
    have hfl2 := Nat.lt_floor_add_one ((φ d.succ + 1) * 2)
    simp only [hb]
    rcases le_total ⌊(φ d.succ + 1) * 2⌋₊ 3 with hle | hle
    · rw [min_eq_right hle]
      exact ⟨hfl, hfl2.le⟩
    · rw [min_eq_left hle]
      constructor
      · have : ((3 : ℕ) : ℝ) ≤ ⌊(φ d.succ + 1) * 2⌋₊ := by exact_mod_cast hle
        push_cast at this ⊢; linarith
      · push_cast; linarith
  set R := List.ofFn b with hR
  set L := a :: R with hL
  have hLa : ∀ x ∈ L, x < 4 := fun x hx => by
    rw [hL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · rw [hR, List.mem_ofFn] at hx
      obtain ⟨d, rfl⟩ := hx
      exact hb4 d
  obtain ⟨h1, _⟩ := digits4_enc4 L hLa
  obtain ⟨_, hR2⟩ := digits4_enc4 R fun x hx => hLa x (by rw [hL]; exact List.mem_cons_of_mem _ hx)
  have hRlen : R.length = D := by simp [hR]
  have hlen : L.length = D + 1 := by simp [hL, hRlen]
  rw [hlen] at h1
  rw [hRlen] at hR2
  have hi : enc4 L < 2 * 4 ^ D := by
    rw [hL, enc4_cons, hRlen]
    have : a * 4 ^ D ≤ 1 * 4 ^ D := Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨enc4 L, hi, fun d => ?_⟩
  have hms : rootMsH D (enc4 L) = (128 + 256 * (a : ℤ)) :: R.map fun (x : ℕ) => -384 + 256 * (x : ℤ) := by
    unfold rootMsH
    rw [h1]
  have hjs : (List.replicate (D + 1) 2).getD d 0 = 2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp [d.isLt]
  rw [hjs, hms]
  refine Fin.cases ?_ (fun d' => ?_) d
  · simp only [Fin.val_zero, List.getD_cons_zero]
    push_cast
    obtain ⟨b1, b2⟩ := hboxa
    rw [abs_le]
    constructor <;> nlinarith
  · simp only [Fin.val_succ, List.getD_cons_succ]
    have hg : (R.map fun (x : ℕ) => -384 + 256 * (x : ℤ)).getD d' 0 = -384 + 256 * (b d' : ℤ) := by
      rw [List.getD_eq_getElem?_getD]
      simp [hR]
    rw [hg]
    push_cast
    obtain ⟨b1, b2⟩ := hboxb d'
    rw [abs_le]
    constructor <;> nlinarith

/-- the half-domain root cells and conjugation cover `[-1, 1]^(D+1)`: the cell property everywhere gives the Sidon bound -/
theorem sidon_of_cells_half {D : ℕ} {B : ℝ} (h : ∀ i < 2 * 4 ^ D, CellOKH D B i) : SidonBound (D + 1 + 1) B :=
  sidon_of_phases fun φ hφ => by
    rcases le_total 0 (φ 0) with h0 | h0
    · obtain ⟨i, hi, hbox⟩ := root_cover_half φ h0 hφ
      exact h i hi φ hbox
    · apply vprop_neg
      have h0' : 0 ≤ (fun d => -φ d) 0 := by simp only; linarith
      have hφ' : ∀ d, |(fun d => -φ d) d| ≤ 1 := fun d => by simp only [abs_neg]; exact hφ d
      obtain ⟨i, hi, hbox⟩ := root_cover_half (fun d => -φ d) h0' hφ'
      exact h i hi _ hbox

/-! ### The half-domain shard check -/

/-- **Soundness of the half-domain shard check.** -/
theorem checkShardH_sound {sh : Shard} (h : checkShardH sh = true) :
    2 ≤ sh.k ∧ ∀ i < 2 * 4 ^ (sh.k - 2), i % sh.nsh = sh.s →
      CellOKH (sh.k - 2) ((mkRat sh.bnum sh.bden : ℚ) : ℝ) i := by
  unfold checkShardH at h
  split_ifs at h with hh
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, ne_eq, not_not] at hh
  obtain ⟨⟨⟨_, hk⟩, _⟩, _⟩ := hh
  refine ⟨hk, ?_⟩
  set D := sh.k - 2 with hD
  have hkD : sh.k = D + 1 + 1 := by omega
  set B : ℚ := mkRat sh.bnum sh.bden with hB
  dsimp only at h
  set ok : Array Bool := sh.verts.map fun vc => vertexOK sh.k B vc.key.toList vc.y with hok
  have hf : ∀ (idx : Std.HashMap (List Comp) ℕ) (key : List Comp),
      (match idx.get? key with
        | some i => decide (i < sh.verts.size) && decide (sh.verts[i]!.key.toList = key) && ok[i]!
        | none => false) = true → VProp (D + 1 + 1) B (vtx (D + 1) key) := by
    intro idx key hl
    split at hl
    · rename_i i _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨⟨hi, hkey⟩, hoki⟩ := hl
      rw [hok, map_getElem! _ _ hi] at hoki
      rw [hkD] at hoki
      have := vertexOK_sound hoki
      rwa [hkey] at this
    · exact absurd hl (by simp)
  intro i hi hs
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  rcases h i hi with h1 | h1
  · exact absurd hs h1
  split at h1
  · rename_i t _
    intro φ hφ
    exact walk_sound (hf _) t (rootMsH D i) (List.replicate (D + 1) 2) (length_rootMsH D i) (by simp) h1 φ hφ
  · exact absurd h1 (by simp)

/-- `N` half-domain shards with the residues `s = 0, …, N - 1` (same `k`, `nsh = N` and bound) give the Sidon bound. -/
theorem sidon_of_shardsH {N k bnum bden : ℕ} (shs : Fin N → Shard) (hN : 0 < N) (hk : ∀ s, (shs s).k = k)
    (hnsh : ∀ s, (shs s).nsh = N) (hs : ∀ s, (shs s).s = s) (hbn : ∀ s, (shs s).bnum = bnum)
    (hbd : ∀ s, (shs s).bden = bden) (hok : ∀ s, checkShardH (shs s) = true) :
    SidonBound k ((mkRat bnum bden : ℚ) : ℝ) := by
  have hk2 : 2 ≤ k := by rw [← hk ⟨0, hN⟩]; exact (checkShardH_sound (hok ⟨0, hN⟩)).1
  have hkD : k = k - 2 + 1 + 1 := by omega
  rw [hkD]
  refine sidon_of_cells_half fun i hi => ?_
  set s : Fin N := ⟨i % N, Nat.mod_lt _ hN⟩
  have h := (checkShardH_sound (hok s)).2
  rw [hk, hnsh, hs, hbn, hbd] at h
  exact h i hi rfl

end Bohr59a.Cert
