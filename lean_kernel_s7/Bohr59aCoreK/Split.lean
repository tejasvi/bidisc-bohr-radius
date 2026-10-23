import Bohr59aCoreK.Walk2

/-!
# Sub-box split of a heavy cell (core Lean only)

`boxesOf t ms js` lists, in order, the leaves of a top tree `t` over a box (centres `ms/512`, half-widths `2^-js`; the split
rule of `walkK2`) as boxes `(ms', js')`. Each listed box is then certified on its own (a `walkK2` over its subtree with its
key lists, in a separate module), and `Bohr59a.CertK.boxOK_of_boxesOf` (`Bohr59a/CertSplit.lean`) assembles them into the
box of `t`.
-/

namespace Bohr59aK

open Bohr59aCore

/-- the leaf boxes of a split tree, in order (`none` if a split is invalid) -/
def boxesOf : Tree → List Int → List Nat → Option (List (List Int × List Nat))
  | .leaf, ms, js => some [(ms, js)]
  | .split d lo hi, ms, js =>
    if d < ms.length ∧ d < js.length ∧ js[d]! ≤ 8 then
      match boxesOf lo (ms.set d (ms[d]! - 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1)),
          boxesOf hi (ms.set d (ms[d]! + 2 ^ (8 - js[d]!))) (js.set d (js[d]! + 1)) with
      | some a, some b => some (a ++ b)
      | _, _ => none
    else none

end Bohr59aK
