import Bohr59aCoreK.Vertex

/-!
# The kernel vertex check with the hints given as data

Same exact checks as `vertexOKK`, but the hints `W` (unit lower triangular rows, scale `2^96`) and `x` (scale `2^96`)
are supplied by the certificate instead of computed in fixed point by the kernel (any values are sound).
-/

namespace Bohr59aK

open Bohr59aCore

/-- the kernel vertex check with given hints -/
def vertexOKKh (tt : TT) (k bnum bden : Nat) (key : List Comp) (Y : List GI) (Wr : List (List GI)) (x : List GI) :
    Bool :=
  let n := k + 1
  if key.length + 2 ≠ n then false else
  domOK 128 Y Wr n &&
    (let w := wVec 128 Y x n
     finalK bnum bden (qVal x w n) (errSumK tt key w))

end Bohr59aK
