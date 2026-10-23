import Bohr59aCoreK.Hints

/-!
`k6hints K`: reads one vertex per line from stdin, `tan,m,j tan,m,j …|re,im re,im …` (key components, then `Y` at scale
`2^128`), and prints `re,im re,im …;re,im …|re,im …` (the rows of `W`, separated by `;`, then `x`), from `Bohr59aK.hintsK`.
Untrusted helper for the data generator.
-/

open Bohr59aK Bohr59aCore

def parseComp (s : String) : Option Comp :=
  match s.splitOn "," with
  | [t, m, j] => do
    let m ← m.toInt?
    let j ← j.toNat?
    some ⟨t == "1", m, j⟩
  | _ => none

def parseGI (s : String) : Option GI :=
  match s.splitOn "," with
  | [a, b] => do
    let a ← a.toInt?
    let b ← b.toInt?
    some ⟨a, b⟩
  | _ => none

def showGI (g : GI) : String := s!"{g.re},{g.im}"

partial def loop (k : Nat) (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let line : String := String.ofList (line.toList.filter (fun c => c != (Char.ofNat 10) && c != (Char.ofNat 13)))
  match line.splitOn "|" with
  | [ks, ys] =>
    let key := (ks.splitOn " ").filterMap parseComp
    let Y := (ys.splitOn " ").filterMap parseGI
    let (W, x) := hintsK k key Y
    o.putStrLn (";".intercalate (W.map fun row => " ".intercalate (row.map showGI)) ++ "|" ++
      " ".intercalate (x.map showGI))
  | _ => o.putStrLn "ERR"
  loop k h o

def main (args : List String) : IO Unit := do
  let k := (args.headD "6").toNat!
  loop k (← IO.getStdin) (← IO.getStdout)
