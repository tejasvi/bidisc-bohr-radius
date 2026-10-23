import Bohr59aCore.Check

/-!
# Kernel walk over a root cell (core Lean only)

`walkK t ms js kl` walks the split tree `t` of a box (centres `ms/512`, half-widths `2^-js`, as in `Bohr59aCore.walk`) and
consumes, at each leaf, the next `3^D` keys of the stream `kl`, which must be exactly the leaf's vertex keys in the order of
`product` (one option of `opts` per coordinate, first coordinate outermost).  The certificates of those keys are separate
theorems (`vertexOKK … key Y = true`), linked by `List.Forall`.
-/

namespace Bohr59aK

open Bohr59aCore

/-- `P` holds at every element of a list -/
def allP {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: l => P a ∧ allP P l

/-- all choices of one element per list -/
def product : List (List Comp) → List (List Comp)
  | [] => [[]]
  | o :: os => o.flatMap fun c => (product os).map (c :: ·)

/-- a leaf: the half-width exponents are in `[2, 9]` and the stream starts with the leaf's keys; returns the rest -/
def leafK (ms : List Int) (js : List Nat) (kl : List (List Comp)) : Option (List (List Comp)) :=
  if ms.length = js.length ∧ js.all (fun j => 2 ≤ j && j ≤ 9) = true then
    let keys := product (List.zipWith opts ms js)
    if kl.take keys.length = keys then some (kl.drop keys.length) else none
  else none

/-- walk a split tree, consuming the key stream -/
def walkK : Tree → List Int → List Nat → List (List Comp) → Option (List (List Comp))
  | .leaf, ms, js, kl => leafK ms js kl
  | .split d lo hi, ms, js, kl =>
    if d < ms.length ∧ d < js.length ∧ js[d]! ≤ 8 then
      match walkK lo (ms.set d (ms[d]! - 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1)) kl with
      | none => none
      | some kl' => walkK hi (ms.set d (ms[d]! + 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1)) kl'
    else none

end Bohr59aK
