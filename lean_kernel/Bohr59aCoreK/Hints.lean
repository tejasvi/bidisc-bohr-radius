import Bohr59aCoreK.TrigTab

/-!
# The fixed-point hints of the kernel vertex check, as a standalone function

`hintsK k key Y` returns exactly the hints `(W rows at scale 2^96, x at scale 2^96)` that `vertexOKK` computes in the
kernel; `vertexOKKh trigTT k bnum bden key Y W x` with these hints performs the same exact checks.  Untrusted.
-/

namespace Bohr59aK

open Bohr59aCore

/-- the hints of `vertexOKK` -/
def hintsK (k : Nat) (key : List Comp) (Y : List GI) : List (List GI) × List GI :=
  let n := k + 1
  let LD := ldlK 160 (tQ Y) n
  let Ws := wAll 160 LD.1 n
  (roundRows 64 Ws, (xHint 160 n Ws LD.2 (vHint trigTT key)).map fun a => (⟨rsh a.re 64, rsh a.im 64⟩ : GI))

end Bohr59aK
