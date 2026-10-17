import Std.Tactic.BVDecide.LRAT
open Std.Sat Std.Tactic.BVDecide

namespace LratCheck

/-- Parse a DIMACS CNF text. DIMACS variable `v ≥ 1` becomes atom `v - 1 : Nat` (the convention of `CNF.dimacs` and `LRAT.check`);
literal `+v` is `(v-1, true)`, `-v` is `(v-1, false)`. Comment lines (`c`) and the header (`p`) are skipped.
A clause is terminated by `0`. Returns the clauses in file order. -/
def parseDimacs (s : String) : CNF Nat := Id.run do
  let b := s.toUTF8
  let n := b.size
  let mut i := 0
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut cur : CNF.Clause Nat := CNF.Clause.empty
  let mut lineStart := true
  while i < n do
    let c := b.get! i
    if lineStart && (c == 'c'.toUInt8 || c == 'p'.toUInt8) then
      -- skip the line
      while i < n && b.get! i != 10 do i := i + 1
      i := i + 1
      lineStart := true
    else if c == 10 then
      i := i + 1; lineStart := true
    else if c == 32 || c == 9 || c == 13 then
      i := i + 1
    else
      lineStart := false
      let mut neg := false
      if c == '-'.toUInt8 then neg := true; i := i + 1
      let mut v : Nat := 0
      while i < n && b.get! i ≥ 48 && b.get! i ≤ 57 do
        v := v * 10 + (b.get! i - 48).toNat
        i := i + 1
      if v == 0 then
        clauses := clauses.push cur
        cur := CNF.Clause.empty
      else
        cur := cur.add (v - 1) (!neg)
  return ⟨clauses⟩

def lratOf (s : String) : Array LRAT.IntAction :=
  match LRAT.parseLRATProof s.toUTF8 with
  | .ok p => p
  | .error _ => #[]

end LratCheck
