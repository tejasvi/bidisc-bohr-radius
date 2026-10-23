import Bohr59aCore.Format

/-!
# Decoding the exported certificate streams (core Lean only; NOT trusted)

`tools/export59.py` writes one base64 string per shard (`Bohr59aData/*.lean`).  Binary layout (little-endian):
`"B59A"`, `u8 version = 1`, `u8 k`, `u8 n0`, `u8 D`, `u32 ncells`, `u32 nverts`; then the trees of the `ncells` root cells
(increasing root index; preorder bytes `0` = leaf, `d + 1` = split coordinate `d`, lower half first); then `nverts` records of
`D` key components (`u16 m + 32768`, `u8 tan * 128 + j`) followed by `2k` IEEE-754 binary64 bit patterns (`re y_1, im y_1,
…`), decoded to rationals exactly.

The checker (`Bohr59aCore.checkShard`) validates whatever this produces; a malformed stream decodes to a shard without cells,
which the checker rejects.  The header fields of the `Shard` (`k`, `n0`, `nsh`, `s`, `bnum`, `bden`) are the arguments of
`decodeShard`, never read from the stream.
-/

namespace Bohr59aCore

/-- the value of a base64 character (`64` for the padding `=`, `255` otherwise) -/
def b64v (c : UInt8) : UInt8 :=
  if 65 ≤ c && c ≤ 90 then c - 65
  else if 97 ≤ c && c ≤ 122 then c - 71
  else if 48 ≤ c && c ≤ 57 then c + 4
  else if c == 43 then 62
  else if c == 47 then 63
  else if c == 61 then 64
  else 255

/-- base64 decoding (no line breaks); `none` on a malformed string -/
def b64decode (s : String) : Option ByteArray := Id.run do
  let src := s.toUTF8
  let n := src.size
  if n % 4 != 0 then return none
  let mut out : ByteArray := ByteArray.emptyWithCapacity (n / 4 * 3)
  for g in [0:n / 4] do
    let i := 4 * g
    let a := b64v src[i]!
    let b := b64v src[i + 1]!
    let c := b64v src[i + 2]!
    let d := b64v src[i + 3]!
    if a ≥ 64 || b ≥ 64 || c == 255 || d == 255 then return none
    out := out.push ((a <<< 2) ||| (b >>> 4))
    if c == 64 then
      if d != 64 || g + 1 != n / 4 then return none
    else
      out := out.push ((b <<< 4) ||| (c >>> 2))
      if d == 64 then
        if g + 1 != n / 4 then return none
      else
        out := out.push ((c <<< 6) ||| d)
  return some out

/-- little-endian unsigned integer of `len` bytes at `p` -/
def rdLE (b : ByteArray) (p len : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:len] do
    v := v + b[p + i]!.toNat * 256 ^ i
  return v

/-- the exact rational value of an IEEE-754 binary64 bit pattern (`none` for infinities and NaNs) -/
def ratOfF64 (bits : Nat) : Option Rat :=
  let sign : Nat := bits / 2 ^ 63 % 2
  let ex : Nat := bits / 2 ^ 52 % 2048
  let mant : Nat := bits % 2 ^ 52
  if ex == 2047 then none
  else
    let m : Nat := if ex == 0 then mant else mant + 2 ^ 52
    let e : Int := if ex == 0 then -1074 else (ex : Int) - 1075
    let v : Rat := if 0 ≤ e then ((m * 2 ^ e.toNat : Nat) : Rat) else mkRat (m : Int) (2 ^ (-e).toNat)
    some (if sign == 1 then -v else v)

/-- the preorder tree at byte `p` (fuel bounds the depth): the tree and the next position -/
def decTree (b : ByteArray) (D : Nat) : Nat → Nat → Option (Tree × Nat)
  | 0, _ => none
  | f + 1, p =>
    if p ≥ b.size then none
    else
      let c := b[p]!.toNat
      if c == 0 then some (.leaf, p + 1)
      else if c ≤ D then
        match decTree b D f (p + 1) with
        | none => none
        | some (lo, p1) =>
          match decTree b D f p1 with
          | none => none
          | some (hi, p2) => some (.split (c - 1) lo hi, p2)
      else none

/-- the root cells `s, s + nsh, …` with their trees, from byte `p`; the cells and the next position -/
def decCells (b : ByteArray) (D nsh s ncells : Nat) (p : Nat) : Option (Array (Nat × Tree) × Nat) := Id.run do
  let mut out : Array (Nat × Tree) := Array.mkEmpty ncells
  let mut q := p
  for t in [0:ncells] do
    match decTree b D 500 q with
    | none => return none
    | some (tr, q') =>
      out := out.push (s + t * nsh, tr)
      q := q'
  return some (out, q)

/-- the vertex records from byte `p` -/
def decVerts (b : ByteArray) (k D nverts p : Nat) : Option (Array VCert) := Id.run do
  let rec_ := 3 * D + 16 * k
  if p + nverts * rec_ != b.size then return none
  let mut out : Array VCert := Array.mkEmpty nverts
  for v in [0:nverts] do
    let base := p + v * rec_
    let mut key : Array Comp := Array.mkEmpty D
    for d in [0:D] do
      let m : Int := (rdLE b (base + 3 * d) 2 : Int) - 32768
      let fl := b[base + 3 * d + 2]!.toNat
      key := key.push ⟨fl ≥ 128, m, fl % 128⟩
    let mut y : Array Rat := Array.mkEmpty (2 * k)
    for i in [0:2 * k] do
      match ratOfF64 (rdLE b (base + 3 * D + 8 * i) 8) with
      | none => return none
      | some r => y := y.push r
    out := out.push ⟨key, y⟩
  return some out

/-- cells and vertex certificates of a stream, checked against the expected `k`, `n0` -/
def decodeBody (k n0 nsh s : Nat) (data : String) : Option (Array (Nat × Tree) × Array VCert) := do
  let b ← b64decode data
  if b.size < 16 then none
  if !(b[0]! == 66 && b[1]! == 53 && b[2]! == 57 && b[3]! == 65 && b[4]! == 1) then none
  if !(b[5]!.toNat == k && b[6]!.toNat == n0 && b[7]!.toNat + 1 == k) then none
  let D := k - 1
  let ncells := rdLE b 8 4
  let nverts := rdLE b 12 4
  let (cells, p) ← decCells b D nsh s ncells 16
  let verts ← decVerts b k D nverts p
  some (cells, verts)

/-- The shard of a stream; the header fields are the arguments (a malformed stream gives a shard without cells). -/
def decodeShard (k n0 nsh s bnum bden : Nat) (data : String) : Shard :=
  let body := (decodeBody k n0 nsh s data).getD (#[], #[])
  { k := k, n0 := n0, nsh := nsh, s := s, bnum := bnum, bden := bden, cells := body.1, verts := body.2 }

/-- Counts for the export cross-checks: cells, vertices, leaves, and the first vertex (`m`, `j` of its key components and
the numerators and denominators of its `y`). -/
def shardStats (sh : Shard) : Nat × Nat × Nat × List (Int × Nat) × List (Int × Nat) :=
  let rec leaves : Tree → Nat
    | .leaf => 1
    | .split _ lo hi => leaves lo + leaves hi
  let v0 := sh.verts[0]!
  (sh.cells.size, sh.verts.size, sh.cells.foldl (fun acc c => acc + leaves c.2) 0,
   v0.key.toList.map (fun c => (c.m, c.j)), v0.y.toList.map (fun r => (r.num, r.den)))

end Bohr59aCore
