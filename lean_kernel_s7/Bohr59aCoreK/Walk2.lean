import Bohr59aCoreK.Walk

/-!
# Kernel walk with per-leaf key lists (core Lean only)

As `walkK`, but the key stream is a list of per-leaf lists: at each leaf the next inner list must be exactly the leaf's
`3^D` vertex keys (in `product` order).  The linking proof `allP (allP P) kls` then nests only as deep as the number of
leaves (plus `3^D`), instead of the number of keys.
-/

namespace Bohr59aK

open Bohr59aCore

/-- a leaf: the half-width exponents are in `[2, 9]` and the next list is the leaf's keys; returns the rest -/
def leafK2 (ms : List Int) (js : List Nat) : List (List (List Comp)) → Option (List (List (List Comp)))
  | [] => none
  | kl :: rest =>
    if ms.length = js.length ∧ js.all (fun j => 2 ≤ j && j ≤ 9) = true ∧ kl = product (List.zipWith opts ms js) then
      some rest
    else none

/-- walk a split tree, consuming one key list per leaf -/
def walkK2 : Tree → List Int → List Nat → List (List (List Comp)) → Option (List (List (List Comp)))
  | .leaf, ms, js, kls => leafK2 ms js kls
  | .split d lo hi, ms, js, kls =>
    if d < ms.length ∧ d < js.length ∧ js[d]! ≤ 8 then
      match walkK2 lo (ms.set d (ms[d]! - 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1)) kls with
      | none => none
      | some kls' => walkK2 hi (ms.set d (ms[d]! + 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1)) kls'
    else none

end Bohr59aK
