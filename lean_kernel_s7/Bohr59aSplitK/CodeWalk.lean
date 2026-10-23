import Bohr59aCoreK.Walk2
import Bohr59aSplitK.Key
import Bohr59aSplitK.Pred

/-!
# Kernel walk over key codes (core Lean only)

As `Bohr59aK.walkK2`, but each leaf's list holds the codes `encK k` of the leaf's `3^D` keys (in `product` order) instead of
the keys. The kernel computes the expected codes from the 18 codes of the coordinates' vertex options (`prodN`) and
compares natural numbers, which is much cheaper than building and comparing keys, and the generated key chunks are lists
of numerals (small to elaborate and to store). Each leaf also checks that it has six coordinates whose options fit the
16-bit code, so that `decK (encK k) = k` (`decK_encK`): a code walk is then a
`walkK2` walk over the decoded lists (`walkKC_walkK2`), and vertex theorems are stated for `decK n`. The round trip and
the reduction to `walkK2` are proved here (core Lean only); the box and cell lemmas are in `Bohr59aSplitK/CodeWalkSound.lean`.
-/

namespace Bohr59aSplitK

open Bohr59aK Bohr59aCore

/-- the 16-bit code of a key component: `tan` in bit 0, `j` in bits 1-4, `m + 512` in bits 5-15 (inverse of `decC`) -/
def encC (c : Comp) : Nat := (if c.tan then 1 else 0) + 2 * c.j + 32 * (c.m + 512).toNat

/-- the code of a key, 16 bits per component, first component lowest (inverse of `decK` on six components) -/
def encK : List Comp → Nat
  | [] => 0
  | c :: r => encC c + 65536 * encK r

/-- the component fits its 16-bit code -/
def inRB (c : Comp) : Bool := decide (-512 ≤ c.m) && decide (c.m < 1536) && decide (c.j < 16)

/-- the key has six components, each fitting its code -/
def keyRB (k : List Comp) : Bool := k.length == 6 && k.all inRB

/-- the codes of all choices of one element per list, in `product` order (first list in the lowest 16 bits) -/
def prodN : List (List Nat) → List Nat
  | [] => [0]
  | o :: os => o.flatMap fun c => (prodN os).map fun r => c + 65536 * r

/-- equality of code lists as a Boolean function (`Nat.beq` on literals is a kernel primitive; no `Decidable` terms) -/
def eqN : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && eqN as bs
  | _, _ => false

/-- a leaf: the half-width exponents are in `[2, 9]`, there are six coordinates whose vertex options fit their codes, and the
next list is the codes of the leaf's keys, computed from the 18 option codes (`prodN`, no key is built) -/
def leafKC (ms : List Int) (js : List Nat) : List (List Nat) → Option (List (List Nat))
  | [] => none
  | cl :: rest =>
    if ms.length = js.length ∧ js.all (fun j => 2 ≤ j && j ≤ 9) = true ∧ ms.length = 6 ∧
        (List.zipWith opts ms js).all (·.all inRB) = true ∧ eqN cl (prodN ((List.zipWith opts ms js).map (·.map encC))) = true then
      some rest
    else none

/-- walk a split tree, consuming one code list per leaf (the split rule of `walkK2`) -/
def walkKC : Tree → List Int → List Nat → List (List Nat) → Option (List (List Nat))
  | .leaf, ms, js, cls => leafKC ms js cls
  | .split d lo hi, ms, js, cls =>
    if d < ms.length ∧ d < js.length ∧ js[d]! ≤ 8 then
      match walkKC lo (ms.set d (ms[d]! - 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1)) cls with
      | none => none
      | some cls' => walkKC hi (ms.set d (ms[d]! + 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1)) cls'
    else none

/-- the link predicate on codes: the fast vertex check accepts the decoded key with some packed hint -/
def PF7C (n : Nat) : Prop := PF7 (decK n)

/-- a link from a vertex theorem (keeps the generated link terms small: no motive per key) -/
theorem pf7c_of {n m : Nat} (h : vertexOKKpF3 trigTT 7 2552 1000 (decK n) m = true) : PF7C n := ⟨m, h⟩

theorem encC_lt (c : Comp) (h : inRB c = true) : encC c < 65536 := by
  obtain ⟨t, m, j⟩ := c
  simp only [inRB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hm : (((m + 512).toNat : Nat) : Int) = m + 512 := Int.toNat_of_nonneg (by omega)
  simp only [encC]
  split <;> omega

theorem decC_encC (c : Comp) (h : inRB c = true) : decC (encC c) = c := by
  obtain ⟨t, m, j⟩ := c
  simp only [inRB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hm : (((m + 512).toNat : Nat) : Int) = m + 512 := Int.toNat_of_nonneg (by omega)
  generalize hu : (m + 512).toNat = u at hm
  have hu2 : u < 2048 := by omega
  simp only [decC, encC, hu]
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Comp.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · have e : (2 * j + 32 * u) % 2 = 0 := by omega
      simp [e]
    · have e : (2 * j + 32 * u) / 32 % 2048 = u := by omega
      rw [e, Int.subNatNat_eq_coe]
      omega
    · omega
  · simp only [↓reduceIte, Comp.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · have e : (1 + 2 * j + 32 * u) % 2 = 1 := by omega
      simp [e]
    · have e : (1 + 2 * j + 32 * u) / 32 % 2048 = u := by omega
      rw [e, Int.subNatNat_eq_coe]
      omega
    · omega

theorem dec6 {a0 a1 a2 a3 a4 a5 : Nat} (h0 : a0 < 65536) (h1 : a1 < 65536) (h2 : a2 < 65536) (h3 : a3 < 65536)
    (h4 : a4 < 65536) (h5 : a5 < 65536) :
    decK (a0 + 65536 * (a1 + 65536 * (a2 + 65536 * (a3 + 65536 * (a4 + 65536 * (a5 + 65536 * 0)))))) =
      [decC a0, decC a1, decC a2, decC a3, decC a4, decC a5] := by
  simp only [decK, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;> omega

theorem decK_encK (k : List Comp) (h : keyRB k = true) : decK (encK k) = k := by
  simp only [keyRB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hl, ha⟩ := h
  match k, hl with
  | [c0, c1, c2, c3, c4, c5], _ =>
    have r0 := ha c0 (by simp)
    have r1 := ha c1 (by simp)
    have r2 := ha c2 (by simp)
    have r3 := ha c3 (by simp)
    have r4 := ha c4 (by simp)
    have r5 := ha c5 (by simp)
    simp only [encK]
    rw [dec6 (encC_lt c0 r0) (encC_lt c1 r1) (encC_lt c2 r2) (encC_lt c3 r3) (encC_lt c4 r4) (encC_lt c5 r5),
      decC_encC c0 r0, decC_encC c1 r1, decC_encC c2 r2, decC_encC c3 r3, decC_encC c4 r4, decC_encC c5 r5]

theorem eq_of_eqN : ∀ {l1 l2 : List Nat}, eqN l1 l2 = true → l1 = l2
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [eqN, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eq_of_eqN h.2]
  | [], _ :: _, h => by simp [eqN] at h
  | _ :: _, [], h => by simp [eqN] at h

theorem prodN_map : ∀ os : List (List Comp), prodN (os.map (·.map encC)) = (product os).map encK
  | [] => rfl
  | o :: os => by
    simp only [List.map_cons, prodN, product, prodN_map os, List.map_flatMap, List.flatMap_map, List.map_map]
    rfl

theorem mem_product : ∀ (os : List (List Comp)) (k : List Comp), k ∈ product os →
    k.length = os.length ∧ ∀ c ∈ k, ∃ o ∈ os, c ∈ o
  | [], k, h => by
    simp only [product, List.mem_singleton] at h
    subst h
    simp
  | o :: os, k, h => by
    simp only [product, List.mem_flatMap, List.mem_map] at h
    obtain ⟨c, hc, r, hr, rfl⟩ := h
    obtain ⟨hl, hm⟩ := mem_product os r hr
    refine ⟨by simp [hl], fun c' hc' => ?_⟩
    simp only [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ⟨o, by simp, hc⟩
    · obtain ⟨o', ho', hc''⟩ := hm c' hc'
      exact ⟨o', by simp [ho'], hc''⟩

theorem keyRB_of_mem {ms : List Int} {js : List Nat} {k : List Comp} (h1 : ms.length = js.length) (h6 : ms.length = 6)
    (h3 : (List.zipWith opts ms js).all (·.all inRB) = true) (hk : k ∈ product (List.zipWith opts ms js)) :
    keyRB k = true := by
  obtain ⟨hl, hm⟩ := mem_product _ k hk
  simp only [keyRB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨by rw [hl, List.length_zipWith]; omega, fun c hc => ?_⟩
  obtain ⟨o, ho, hco⟩ := hm c hc
  exact List.all_eq_true.1 (List.all_eq_true.1 h3 o ho) c hco

theorem leafKC_leafK2 (ms : List Int) (js : List Nat) (cls r : List (List Nat)) (h : leafKC ms js cls = some r) :
    leafK2 ms js (cls.map (·.map decK)) = some (r.map (·.map decK)) := by
  match cls with
  | [] => simp [leafKC] at h
  | cl :: rest =>
    simp only [leafKC] at h
    split at h
    · rename_i hc
      obtain ⟨h1, h2, h6, h3, h4⟩ := hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.map_cons, leafK2]
      rw [ite_eq_left]
      refine ⟨h1, h2, ?_⟩
      rw [eq_of_eqN h4, prodN_map, List.map_map]
      exact (List.map_congr_left fun k hk => decK_encK k (keyRB_of_mem h1 h6 h3 hk)).trans (List.map_id _)
    · exact absurd h (by simp)

theorem walkKC_walkK2 : ∀ (t : Tree) (ms : List Int) (js : List Nat) (cls r : List (List Nat)), walkKC t ms js cls = some r →
    walkK2 t ms js (cls.map (·.map decK)) = some (r.map (·.map decK))
  | .leaf, ms, js, cls, r, h => leafKC_leafK2 ms js cls r h
  | .split d lo hi, ms, js, cls, r, h => by
    simp only [walkKC] at h
    split at h
    · rename_i hc
      split at h
      · exact absurd h (by simp)
      · rename_i cls' hlo
        simp only [walkK2, ite_eq_left hc, walkKC_walkK2 lo _ _ cls cls' hlo]
        exact walkKC_walkK2 hi _ _ cls' r h
    · exact absurd h (by simp)

theorem allP_mapC {P : List Comp → Prop} : ∀ {l : List Nat}, allP (fun n => P (decK n)) l → allP P (l.map decK)
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, allP_mapC h.2⟩

theorem allP_mapC2 : ∀ {l : List (List Nat)}, allP (allP PF7C) l → allP (allP PF7) (l.map (·.map decK))
  | [], _ => trivial
  | _ :: _, h => ⟨allP_mapC h.1, allP_mapC2 h.2⟩

end Bohr59aSplitK
