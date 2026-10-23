/-
Soundness of the shard check (`Bohr59aCore.checkShard`) and the Sidon bound from the shards.
-/
import Bohr59a.CertGeom

namespace Bohr59a.Cert

open Bohr59aCore

/-- the root cells cover `[-1, 1]^D`: the cell property everywhere gives the Sidon bound -/
theorem sidon_of_cells {D : ℕ} {B : ℝ} (h : ∀ i < 8 ^ D, CellOK D B i) : SidonBound (D + 1) B :=
  sidon_of_phases fun φ hφ => by
    obtain ⟨i, hi, hbox⟩ := root_cover φ hφ
    exact h i hi φ hbox

lemma map_getElem! {α β : Type*} [Inhabited α] [Inhabited β] (a : Array α) (g : α → β) {i : ℕ}
    (hi : i < a.size) : (a.map g)[i]! = g a[i]! := by
  rw [getElem!_pos (a.map g) i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

/-- **Soundness of the shard check.** -/
theorem checkShard_sound {sh : Shard} (h : checkShard sh = true) :
    2 ≤ sh.k ∧ ∀ i < 8 ^ (sh.k - 1), i % sh.nsh = sh.s →
      CellOK (sh.k - 1) ((mkRat sh.bnum sh.bden : ℚ) : ℝ) i := by
  unfold checkShard at h
  split_ifs at h with hh
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, ne_eq, not_not] at hh
  obtain ⟨⟨⟨_, hk⟩, _⟩, _⟩ := hh
  refine ⟨hk, ?_⟩
  set D := sh.k - 1 with hD
  have hkD : sh.k = D + 1 := by omega
  set B : ℚ := mkRat sh.bnum sh.bden with hB
  dsimp only at h
  set ok : Array Bool := sh.verts.map fun vc => vertexOK sh.k B vc.key.toList vc.y with hok
  -- the lookup
  have hf : ∀ (idx : Std.HashMap (List Comp) ℕ) (key : List Comp),
      (match idx.get? key with
        | some i => decide (i < sh.verts.size) && decide (sh.verts[i]!.key.toList = key) && ok[i]!
        | none => false) = true → VProp (D + 1) B (vtx D key) := by
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
    exact walk_sound (hf _) t (rootMs D i) (List.replicate D 3) (by simp [rootMs, length_digits8])
      (by simp) h1 φ hφ
  · exact absurd h1 (by simp)

/-- One shard holding all root cells (`nsh = 1`, `s = 0`) gives the Sidon bound. -/
theorem sidon_of_shard {sh : Shard} (h : checkShard sh = true) (hn : sh.nsh = 1) (hs : sh.s = 0) :
    SidonBound sh.k ((mkRat sh.bnum sh.bden : ℚ) : ℝ) := by
  obtain ⟨hk, hc⟩ := checkShard_sound h
  have hkD : sh.k = sh.k - 1 + 1 := by omega
  rw [hkD]
  exact sidon_of_cells fun i hi => hc i hi (by rw [hn, hs, Nat.mod_one])

/-- `N` shards with the residues `s = 0, …, N - 1` (same `k`, `nsh = N` and bound) give the Sidon bound. -/
theorem sidon_of_shards {N k bnum bden : ℕ} (shs : Fin N → Shard) (hN : 0 < N) (hk : ∀ s, (shs s).k = k)
    (hnsh : ∀ s, (shs s).nsh = N) (hs : ∀ s, (shs s).s = s) (hbn : ∀ s, (shs s).bnum = bnum)
    (hbd : ∀ s, (shs s).bden = bden) (hok : ∀ s, checkShard (shs s) = true) :
    SidonBound k ((mkRat bnum bden : ℚ) : ℝ) := by
  have hk2 : 2 ≤ k := by rw [← hk ⟨0, hN⟩]; exact (checkShard_sound (hok ⟨0, hN⟩)).1
  have hkD : k = k - 1 + 1 := by omega
  rw [hkD]
  refine sidon_of_cells fun i hi => ?_
  set s : Fin N := ⟨i % N, Nat.mod_lt _ hN⟩
  have h := (checkShard_sound (hok s)).2
  rw [hk, hnsh, hs, hbn, hbd] at h
  exact h i hi rfl

end Bohr59a.Cert
