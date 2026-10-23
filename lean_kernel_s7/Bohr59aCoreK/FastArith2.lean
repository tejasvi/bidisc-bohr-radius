import Bohr59aCoreK.FastArith

/-!
# The final test on the fast primitives

`finalKF` is `finalK` (the comparisons `ρ ≤ B` and `q ≤ (B - ρ)²`, cleared of denominators) with the products, the
difference and the comparisons on the direct-recursor primitives of `FastArith.lean` and the constants as `Nat` powers,
which the kernel evaluates with GMP. `vertexOKKhF2` / `vertexOKKpF2` are `vertexOKKhF` / `vertexOKKpF` with `finalKF`.
`Bohr59a/CertFast2.lean` proves that they agree with the original checks.
-/

namespace Bohr59aK

open Bohr59aCore

/-- `a ≤ b` -/
noncomputable def ile (a b : Int) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun m => Int.rec (motive := fun _ => Bool) (fun n => Nat.ble m n) (fun _ => false) b)
    (fun m => Int.rec (motive := fun _ => Bool) (fun _ => true) (fun n => Nat.ble n m) b) a

/-- `finalK` on the fast primitives -/
noncomputable def finalKF (bnum bden : Nat) (q : Int) (ρ : Option Int) : Bool :=
  match ρ with
  | Option.none => false
  | some R =>
    let rb := imul R (Int.ofNat bden)
    let bb := Int.ofNat (Nat.mul bnum (Nat.pow 2 224))
    let d := isub bb rb
    ile rb bb && ile (imul (imul q (Int.ofNat (Nat.mul bden bden))) (Int.ofNat (Nat.pow 2 128))) (imul d d)

/-- `vertexOKKhF` with `finalKF` -/
noncomputable def vertexOKKhF2 (tt : TT) (k bnum bden : Nat) (key : List Comp) (Y : List GI) (Wr : List (List GI))
    (x : List GI) : Bool :=
  let n := k + 1
  if key.length + 2 ≠ n then false else
  domOKF 128 Y Wr n &&
    (let w := wVecF 128 Y x n
     finalKF bnum bden (qValF x w n) (errSumK tt key w))

/-- `vertexOKKpF` with `finalKF` -/
noncomputable def vertexOKKpF2 (tt : TT) (k bnum bden : Nat) (key : List Comp) (n : Nat) : Bool :=
  vertexOKKhF2 tt k bnum bden key ((unpackGI k n).take k) (rowsGI (k + 1) 0 ((unpackGI k n).drop k))
    (((unpackGI k n).drop (k + (k + 1) * (k + 2) / 2)).take (k + 1))

end Bohr59aK
