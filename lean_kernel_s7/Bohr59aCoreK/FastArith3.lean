import Bohr59aCoreK.FastDom8
import Bohr59aCoreK.FastWQ8

/-!
# The vertex check with the straight-line parts

`vertexOKKhF3` / `vertexOKKpF3` are `vertexOKKhF2` / `vertexOKKpF2` with the straight-line versions for `n = 8` of the
dominance test and of `w = T x`, `q = x* w`: `domOKFast` (`FastDom8.lean`), `wVecFast`, `qValFast` (`FastWQ8.lean`).
`Bohr59a/CertFast3.lean` proves that they agree with the original checks.
-/

namespace Bohr59aK

open Bohr59aCore

/-- `vertexOKKhF2` with `domOKFast`, `wVecFast`, `qValFast` -/
noncomputable def vertexOKKhF3 (tt : TT) (k bnum bden : Nat) (key : List Comp) (Y : List GI) (Wr : List (List GI))
    (x : List GI) : Bool :=
  let n := k + 1
  if key.length + 2 ≠ n then false else
  domOKFast 128 Y Wr n &&
    (let w := wVecFast 128 Y x n
     finalKF bnum bden (qValFast x w n) (errSumK tt key w))

/-- `vertexOKKpF2` with `domOKFast`, `wVecFast`, `qValFast` -/
noncomputable def vertexOKKpF3 (tt : TT) (k bnum bden : Nat) (key : List Comp) (n : Nat) : Bool :=
  vertexOKKhF3 tt k bnum bden key ((unpackGI k n).take k) (rowsGI (k + 1) 0 ((unpackGI k n).drop k))
    (((unpackGI k n).drop (k + (k + 1) * (k + 2) / 2)).take (k + 1))

end Bohr59aK
