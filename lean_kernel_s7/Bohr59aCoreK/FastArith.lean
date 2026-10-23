import Bohr59aCoreK.Packed

/-!
# Direct-recursor integer primitives for kernel evaluation

`iadd`, `isub`, `imul`, `ilt`, `ieq` work on `Int.rec` / `Nat.rec` directly, with the core `Nat` operations (which the
kernel evaluates on literals with GMP) inside: about a third of the kernel unfoldings of `+`, `*`, `-`, `<` through their
instances and matchers (the pattern of the worm K pilot's `WormK/Fast3.lean`). They are `noncomputable` (the code generator
has no `Int.rec`); they are only evaluated by the kernel. `Bohr59a/CertFast.lean` proves that they agree with the standard
operations, and that the checks built from them (`domOKF`, …) agree with the original ones.
-/

namespace Bohr59aK

open Bohr59aCore

/-- `m - n` as an integer -/
noncomputable def isnn (m n : Nat) : Int :=
  Nat.rec (motive := fun _ => Int) (Int.ofNat (Nat.sub m n)) (fun k _ => Int.negSucc k) (Nat.sub n m)

/-- `a + b` -/
noncomputable def iadd (a b : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => Int.ofNat (Nat.add m n)) (fun n => isnn m (Nat.succ n)) b)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => isnn n (Nat.succ m))
      (fun n => Int.negSucc (Nat.succ (Nat.add m n))) b) a

/-- `-(n : Int)` -/
noncomputable def nneg (n : Nat) : Int := Nat.rec (motive := fun _ => Int) (Int.ofNat 0) (fun k _ => Int.negSucc k) n

/-- `-a` -/
noncomputable def ineg (a : Int) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => nneg m) (fun m => Int.ofNat (Nat.succ m)) a

/-- `a - b` -/
noncomputable def isub (a b : Int) : Int := iadd a (ineg b)

/-- `a * b` -/
noncomputable def imul (a b : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => Int.ofNat (Nat.mul m n)) (fun n => nneg (Nat.mul m (Nat.succ n))) b)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => nneg (Nat.mul (Nat.succ m) n))
      (fun n => Int.ofNat (Nat.mul (Nat.succ m) (Nat.succ n))) b) a

/-- `|a|` as a natural number -/
noncomputable def iabs (a : Int) : Nat := Int.rec (motive := fun _ => Nat) (fun m => m) (fun m => Nat.succ m) a

/-- `a < b` -/
noncomputable def ilt (a b : Int) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun m => Int.rec (motive := fun _ => Bool) (fun n => Nat.blt m n) (fun _ => false) b)
    (fun m => Int.rec (motive := fun _ => Bool) (fun _ => true) (fun n => Nat.blt n m) b) a

/-- `a = b` -/
noncomputable def ieq (a b : Int) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun m => Int.rec (motive := fun _ => Bool) (fun n => Nat.beq m n) (fun _ => false) b)
    (fun m => Int.rec (motive := fun _ => Bool) (fun _ => false) (fun n => Nat.beq m n) b) a

/-! ## Gaussian integers on the fast primitives -/

namespace GI
noncomputable def addF (a b : GI) : GI := ⟨iadd a.re b.re, iadd a.im b.im⟩
noncomputable def mulF (a b : GI) : GI := ⟨isub (imul a.re b.re) (imul a.im b.im), iadd (imul a.re b.im) (imul a.im b.re)⟩
noncomputable def conjF (a : GI) : GI := ⟨a.re, ineg a.im⟩
noncomputable def abs1F (a : GI) : Int := Int.ofNat (Nat.add (iabs a.re) (iabs a.im))
end GI

/-- `Σ_{p < n} f p` -/
noncomputable def sumGIF (f : Nat → GI) : Nat → GI
  | 0 => GI.zero
  | n + 1 => (sumGIF f n).addF (f n)

/-- `Σ_{p < n} f p` -/
noncomputable def sumIntF (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => iadd (sumIntF f n) (f n)

/-- `T(y)` at scale `2^E` -/
noncomputable def tKF (E : Nat) (Y : List GI) (j l : Nat) : GI :=
  if j = l then ⟨2 ^ E, 0⟩ else if j < l then nth GI.zero Y (l - j - 1) else (nth GI.zero Y (j - l - 1)).conjF

/-- entry `(i, j)` of `M = W T W*` -/
noncomputable def mEntryF (E : Nat) (Y : List GI) (Wr : List (List GI)) (n i j : Nat) : GI :=
  sumGIF (fun b => (sumGIF (fun a => (nth GI.zero (nth [] Wr i) a).mulF (tKF E Y a b)) (i + 1)).mulF
    (nth GI.zero (nth [] Wr j) b).conjF) (j + 1)

/-- `domOK` on the fast primitives -/
noncomputable def domOKF (E : Nat) (Y : List GI) (Wr : List (List GI)) (n : Nat) : Bool :=
  let low : List (List GI) := (List.range n).map fun i => (List.range (i + 1)).map fun j => mEntryF E Y Wr n i j
  (List.range n).all fun i =>
    let off := sumIntF (fun j => if j < i then (nth GI.zero (nth [] low i) j).abs1F
      else if i < j then (nth GI.zero (nth [] low j) i).abs1F else 0) n
    ilt off (nth GI.zero (nth [] low i) i).re && ieq (nth GI.zero (nth [] low i) i).im 0 &&
      (ieq (nth GI.zero (nth [] Wr i) i).re (Int.ofNat (2 ^ 96)) && ieq (nth GI.zero (nth [] Wr i) i).im 0)

/-- `w = T x` on the fast primitives -/
noncomputable def wVecF (E : Nat) (Y : List GI) (x : List GI) (n : Nat) : List GI :=
  (List.range n).map fun j => sumGIF (fun l => (tKF E Y j l).mulF (nth GI.zero x l)) n

/-- `q = Re x* w` on the fast primitives -/
noncomputable def qValF (x w : List GI) (n : Nat) : Int :=
  sumIntF (fun j => ((nth GI.zero x j).conjF.mulF (nth GI.zero w j)).re) n

/-- `vertexOKKh` with `domOK`, `wVec`, `qVal` on the fast primitives (the error sum and the final test unchanged) -/
noncomputable def vertexOKKhF (tt : TT) (k bnum bden : Nat) (key : List Comp) (Y : List GI) (Wr : List (List GI))
    (x : List GI) : Bool :=
  let n := k + 1
  if key.length + 2 ≠ n then false else
  domOKF 128 Y Wr n &&
    (let w := wVecF 128 Y x n
     finalK bnum bden (qValF x w n) (errSumK tt key w))

/-- `vertexOKKp` on the fast primitives -/
noncomputable def vertexOKKpF (tt : TT) (k bnum bden : Nat) (key : List Comp) (n : Nat) : Bool :=
  vertexOKKhF tt k bnum bden key ((unpackGI k n).take k) (rowsGI (k + 1) 0 ((unpackGI k n).drop k))
    (((unpackGI k n).drop (k + (k + 1) * (k + 2) / 2)).take (k + 1))

end Bohr59aK
