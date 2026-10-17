import Std.Tactic.BVDecide.LRAT
/-!
# TrCheck: executable re-implementation of the W11-referee trace relaxation Φ_{a,c}
(sat/w11ref/tr/tr_core.py), core Lean only (no Mathlib), so it can be compiled to a shared
library and evaluated natively by `native_decide`.

Everything here is *computation*; the meaning of each test is proved in `BridgeNoK4.lean`.
Masks are `Nat` bitmasks over the core points `0..n-1`; `nd a m = a ∧ ¬m` (within `full`).
-/
open Std.Sat

namespace TrCheck

/-- population count of the low `k` bits. -/
def pcK : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, m => m % 2 + pcK k (m / 2)

/-- class data: core size `n`, base-edge core masks `P0..P3`, private sizes `O0..O3`, rule flags
(bit 8 W7 off, 4 NK off, 2 N24 off, 1 N34 on; the controls are never used here). -/
structure Cls where
  n : Nat
  P0 : Nat
  P1 : Nat
  P2 : Nat
  P3 : Nat
  O0 : Nat
  O1 : Nat
  O2 : Nat
  O3 : Nat
  flags : Nat

/-- a 4-vector of naturals (state `o`, overlaps `z`). -/
structure V4 where
  a0 : Nat
  a1 : Nat
  a2 : Nat
  a3 : Nat
deriving Repr, DecidableEq, BEq

def V4.get (v : V4) : Nat → Nat
  | 0 => v.a0
  | 1 => v.a1
  | 2 => v.a2
  | 3 => v.a3
  | _ => 0

def V4.sum (v : V4) : Nat := v.a0 + v.a1 + v.a2 + v.a3

namespace Cls
variable (C : Cls)

def P : Nat → Nat
  | 0 => C.P0
  | 1 => C.P1
  | 2 => C.P2
  | 3 => C.P3
  | _ => 0

def OS : Nat → Nat
  | 0 => C.O0
  | 1 => C.O1
  | 2 => C.O2
  | 3 => C.O3
  | _ => 0

def full : Nat := 2 ^ C.n - 1
def pc (m : Nat) : Nat := pcK C.n m
def nd (a m : Nat) : Nat := a &&& (m ^^^ C.full)

/-- `cls_ok` of tr_core.py. -/
def clsOk (a c : Nat) : Bool :=
  (C.flags &&& 8 != 0 || (2 ≤ a && 2 ≤ c)) &&
  (C.flags &&& 4 != 0 || 6 ≤ a + c) &&
  (1 ≤ a && 1 ≤ c && 5 ≤ a + c) &&
  (C.flags &&& 2 != 0 || !((a == 2 && c == 4) || (a == 4 && c == 2))) &&
  (C.flags &&& 1 == 0 || !((a == 3 && c == 4) || (a == 4 && c == 3)))

def q4 : List Nat := [0, 1, 2, 3]
def pairs4 : List (Nat × Nat) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
/-- the 11 subfamilies `S ⊆ {0,1,2,3}` with `|S| ≥ 2`, as bitmasks. -/
def subs : List Nat := [3,5,6,7,9,10,11,12,13,14,15]

def mem (S q : Nat) : Bool := S.testBit q
def capS (S : Nat) : Nat := q4.foldl (fun acc q => if mem S q then acc &&& C.P q else acc) C.full
def cupS (S : Nat) : Nat := q4.foldl (fun acc q => if mem S q then acc ||| C.P q else acc) 0
def osS (S : Nat) : Nat := q4.foldl (fun acc q => if mem S q then acc + C.OS q else acc) 0
/-- `Σ_{q ∉ S} v_q` -/
def outS (S : Nat) (v : V4) : Nat := q4.foldl (fun acc q => if mem S q then acc else acc + v.get q) 0

def xq (b : Nat) (o : V4) (q : Nat) : Nat := C.pc (b &&& C.P q) + o.get q

/-! ### per-edge rules (`edge_ok`) -/

def eBox (b : Nat) (o : V4) : Bool :=
  q4.all (fun q => o.get q ≤ C.OS q) && C.pc b + o.sum ≤ 21

def eA (b : Nat) (o : V4) : Bool := q4.all (fun q => 5 ≤ C.xq b o q)

def eF1 (b : Nat) : Bool := pairs4.all (fun (i, j) => b &&& C.P i &&& C.P j != 0)

def eL (b : Nat) (o : V4) : Bool :=
  let u := 21 - (C.pc b + o.sum)
  subs.all fun S =>
    b &&& C.capS S != 0 ||
    61 ≤ C.osS S + C.pc (C.cupS S) + (C.pc (C.nd b (C.cupS S)) + u + outS S o)

/-- rules at the base 5-pair `(P_i, P_j)`. -/
def eBasePair (b : Nat) (o : V4) (i j : Nat) : Bool :=
  let N := C.P i &&& C.P j
  if C.pc N != 5 then true else
  let bn := b &&& N
  (bn == N || C.xq b o i + C.xq b o j ≤ 9 + C.pc bn) &&
  (C.pc bn != 1 ||
    (C.xq b o i == 5 && C.xq b o j == 5 &&
     q4.all fun k =>
       k == i || k == j ||
       (let y := C.P k &&& N
        C.pc y != 1 || y == bn ||
        (C.nd (b &&& C.P k) (C.P i ||| C.P j) == 0 && o.get k == 0 &&
         C.clsOk (C.pc (C.nd (b &&& C.P k &&& C.P i) (C.P j)))
                 (C.pc (C.nd (b &&& C.P k &&& C.P j) (C.P i)))))))

/-- rules at a derived 5-pair `(P_i, X)` (only when `|X ∩ P_i| = 5`). -/
def eDerived (b : Nat) (o : V4) (i : Nat) : Bool :=
  C.xq b o i != 5 ||
  (let Nc := b &&& C.P i
   (q4.all fun j => j == i ||
      ((o.get i == 0 && C.nd Nc (C.P j) == 0) ||
          C.pc (C.P j &&& C.P i) + C.pc (C.nd (b &&& C.P j) (C.P i)) + o.get j ≤ 9) &&
      (C.pc (C.P j &&& Nc) != 1 || C.xq b o j == 5)) &&
   (pairs4.all fun (j, k) =>
      j == i || k == i || C.pc (C.P j &&& Nc) != 1 || C.pc (C.P k &&& Nc) != 1 ||
      C.P j &&& C.P k &&& Nc != 0 ||
      (C.nd (C.nd (C.P j &&& C.P k) (C.P i)) b == 0 &&
       C.clsOk (C.pc (C.nd (C.P j &&& C.P k &&& C.P i) b))
               (C.pc (C.nd (C.P j &&& C.P k &&& b) (C.P i))))))

def edgeOk (b : Nat) (o : V4) : Bool :=
  C.eBox b o && C.eA b o && C.eF1 b && C.eL b o &&
  pairs4.all (fun (i, j) => C.eBasePair b o i j) &&
  q4.all (fun i => C.eDerived b o i)

/-- lower bound `L_q = max(0, 5 - |b ∩ P_q|)` (from rule A). -/
def lo (b q : Nat) : Nat := 5 - C.pc (b &&& C.P q)

/-- all admissible states of trace `b` (nested box with running-sum pruning). -/
def states (b : Nat) : List V4 :=
  let s := C.pc b
  let L0 := C.lo b 0; let L1 := C.lo b 1; let L2 := C.lo b 2; let L3 := C.lo b 3
  (List.range' L0 (C.OS 0 + 1 - L0)).flatMap fun o0 =>
  (List.range' L1 (C.OS 1 + 1 - L1)).flatMap fun o1 =>
    if s + o0 + o1 + L2 + L3 > 21 then [] else
  (List.range' L2 (C.OS 2 + 1 - L2)).flatMap fun o2 =>
    if s + o0 + o1 + o2 + L3 > 21 then [] else
  ((List.range' L3 (C.OS 3 + 1 - L3)).filterMap fun o3 =>
    let o : V4 := ⟨o0, o1, o2, o3⟩
    if C.edgeOk b o then some o else none)

/-- the universe: `(trace, states)` for every trace with at least one state, in increasing trace order
(= DIMACS variable order of the tr CNFs: atom `i` ↔ `univ[i]`). -/
def univ : List (Nat × List V4) :=
  ((List.range (2 ^ C.n)).map fun b => (b, C.states b)).filter fun p => !p.2.isEmpty

/-! ### pair rules -/

def pSAME (b1 b2 : Nat) (z : V4) (zu : Nat) : Bool :=
  let I := b1 &&& b2
  pairs4.all fun (i, j) =>
    let N := C.P i &&& C.P j
    let s1 := b1 &&& N; let s2 := b2 &&& N
    C.pc N != 5 || C.pc s1 != 1 || C.pc s2 != 1 || s1 == s2 ||
    (C.nd I (C.P i ||| C.P j) == 0 && zu == 0 &&
     q4.all (fun q => q == i || q == j || z.get q == 0) &&
     C.clsOk (C.pc (C.nd (I &&& C.P i) (C.P j)) + z.get i) (C.pc (C.nd (I &&& C.P j) (C.P i)) + z.get j))

/-- rules at the derived 5-pair `(P_k, A)` seen from the other edge `B` (`I = bA ∧ bB`). -/
def pDer1 (bA : Nat) (oA : V4) (bB : Nat) (oB : V4) (I : Nat) (z : V4) (zu : Nat) : Bool :=
  q4.all fun k =>
    C.xq bA oA k != 5 ||
    (let offk := C.pc (C.nd I (C.P k)) + zu + q4.foldl (fun acc q => if q == k then acc else acc + z.get q) 0
     let nB := C.pc (I &&& C.P k) + z.get k
     (5 ≤ nB || C.xq bB oB k + offk ≤ 9) &&
     (nB != 1 ||
       (C.xq bB oB k == 5 && nB + offk == 5 &&
        (let Nc := bA &&& C.P k
         q4.all fun j =>
           j == k ||
           (let y := Nc &&& C.P j
            C.pc y != 1 || bB &&& y != 0 ||
            (C.nd (C.nd (bB &&& C.P j) (C.P k)) bA == 0 && oB.get j == z.get j &&
             C.clsOk (C.pc (C.nd (bB &&& C.P j &&& C.P k) bA)) (C.pc (C.nd (I &&& C.P j) (C.P k)) + z.get j)))))))

/-- rules at the derived 5-pair `(F1, F2)`. -/
def pDer2 (b1 : Nat) (o1 : V4) (b2 : Nat) (o2 : V4) (I : Nat) (z : V4) : Bool :=
  let nj := fun j => C.pc (I &&& C.P j) + z.get j
  (q4.all fun j =>
     (5 ≤ nj j || C.xq b1 o1 j + C.xq b2 o2 j ≤ 9 + nj j) &&
     (nj j != 1 || (C.xq b1 o1 j == 5 && C.xq b2 o2 j == 5))) &&
  (pairs4.all fun (j, k) =>
     nj j != 1 || nj k != 1 || I &&& (C.P j &&& C.P k) != 0 ||
     (C.nd (C.P j &&& C.P k) (b1 ||| b2) == 0 &&
      C.clsOk (C.pc (C.nd (C.P j &&& C.P k &&& b1) b2)) (C.pc (C.nd (C.P j &&& C.P k &&& b2) b1))))

def pairRules (b1 : Nat) (o1 : V4) (b2 : Nat) (o2 : V4) (z : V4) (zu : Nat) : Bool :=
  let I := b1 &&& b2
  let u1 := 21 - (C.pc b1 + o1.sum)
  let u2 := 21 - (C.pc b2 + o2.sum)
  let inter := C.pc I + z.sum + zu
  5 ≤ inter &&
  q4.all (fun q => I &&& C.P q != 0 || z.get q != 0) &&
  (subs.all fun S =>
     I &&& C.capS S != 0 ||
     61 + (C.pc (C.nd I (C.cupS S)) + zu + outS S z) ≤
       C.osS S + C.pc (C.cupS S) + (C.pc (C.nd b1 (C.cupS S)) + u1 + outS S o1) +
         (C.pc (C.nd b2 (C.cupS S)) + u2 + outS S o2)) &&
  C.pSAME b1 b2 z zu &&
  C.pDer1 b1 o1 b2 o2 I z zu && C.pDer1 b2 o2 b1 o1 I z zu &&
  (inter != 5 || C.pDer2 b1 o1 b2 o2 I z)

def rng (lo hi : Nat) : List Nat := List.range' lo (hi + 1 - lo)

/-- `pair_ok`: some integer overlap vector satisfies all pair rules. -/
def pairOk (b1 : Nat) (o1 : V4) (b2 : Nat) (o2 : V4) : Bool :=
  let u1 := 21 - (C.pc b1 + o1.sum)
  let u2 := 21 - (C.pc b2 + o2.sum)
  let lo := fun q => o1.get q + o2.get q - C.OS q
  let hi := fun q => min (o1.get q) (o2.get q)
  (rng (lo 0) (hi 0)).any fun z0 => (rng (lo 1) (hi 1)).any fun z1 =>
  (rng (lo 2) (hi 2)).any fun z2 => (rng (lo 3) (hi 3)).any fun z3 =>
  (List.range (min u1 u2 + 1)).any fun zu => C.pairRules b1 o1 b2 o2 ⟨z0, z1, z2, z3⟩ zu

def compat (p1 p2 : Nat × List V4) : Bool :=
  p1.2.any fun o1 => p2.2.any fun o2 => C.pairOk p1.1 o1 p2.1 o2

/-! ### clause checker -/

/-- `B` certifies the positive clause `cl` as a COV clause: `|B| ≤ 4`, `B` meets every base edge, and every universe
trace avoiding `B` is an atom of `cl`. -/
def covOkB (U : Array (Nat × List V4)) (cl : List Nat) (B : Nat) : Bool :=
  C.pc B ≤ 4 && q4.all (fun q => B &&& C.P q != 0) &&
  ((List.range U.size).filter fun i => (U.getD i (0, [])).1 &&& B == 0).all fun i => cl.contains i

/-- COV check: candidate `B := full ∖ ⋃ traces of the clause`, else any sub-mask of it. -/
def covOk (U : Array (Nat × List V4)) (cl : List Nat) : Bool :=
  let un := cl.foldl (fun acc i => acc ||| (U.getD i (0, [])).1) 0
  let cand := C.nd C.full un
  C.covOkB U cl cand ||
  (List.range (2 ^ C.n)).any fun s => s &&& cand == s && C.pc s == 4 && C.covOkB U cl s

def clauseOk (U : Array (Nat × List V4)) (r : Nat) (cl : List (Nat × Bool)) : Bool :=
  if cl.all (·.2) then
    (cl.length == 1 && cl.all (·.1 == r)) || C.covOk U (cl.map (·.1))
  else match cl with
    | [(i, false), (j, false)] => i != j && i < U.size && j < U.size && !C.compat U[i]! U[j]!
    | _ => false

/-- permutation action on traces: bit `i` of the result is bit `g i` of `t`. -/
def permT (g : List Nat) (t : Nat) : Nat :=
  ((List.range g.length).zip g).foldl (fun acc (i, gi) => if t.testBit gi then acc ||| (1 <<< i) else acc) 0

/-- `(g, π)` is an automorphism of the labelled base: `g` permutes `0..n-1`, `π` permutes `0..3`,
bit `i` of `P_q` = bit `g i` of `P_{π q}`, and `|O_q| = |O_{π q}|`. -/
def autOk (g π : List Nat) : Bool :=
  g.length == C.n && (List.range C.n).all (fun i => g.getD i 0 < C.n) &&
  (List.range C.n).all (fun i => (List.range C.n).all fun j => i == j || g.getD i 0 != g.getD j 0) &&
  π.length == 4 && q4.all (fun q => π.getD q 0 < 4) &&
  q4.all (fun i => q4.all fun j => i == j || π.getD i 0 != π.getD j 0) &&
  q4.all (fun q => C.OS q == C.OS (π.getD q 0) &&
    (List.range C.n).all fun i => (C.P q).testBit i == (C.P (π.getD q 0)).testBit (g.getD i 0))

/-- root step: `B*` is needed, and every universe trace avoiding `B*` is mapped by a listed automorphism onto
one of the case representatives. `wit` lists `(avoider index, g, π, rep index)`. -/
def orbitOk (U : Array (Nat × List V4)) (Bs : Nat) (reps : List Nat)
    (wit : List (Nat × List Nat × List Nat × Nat)) : Bool :=
  C.pc Bs ≤ 4 && q4.all (fun q => Bs &&& C.P q != 0) &&
  (List.range U.size).all fun i =>
    (U.getD i (0, [])).1 &&& Bs != 0 ||
    wit.any fun (i', g, π, r) => i' == i && reps.any (· == r) && C.autOk g π &&
      permT g (U.getD i (0, [])).1 == (U.getD r (0, [])).1

/-- basic sanity of the class data: masks inside `full`, `|O_q| = 21 - |core ∩ P_q|`. -/
def clsSane : Bool :=
  q4.all (fun q => C.P q ≤ C.full && C.OS q + C.pc (C.P q) == 21) && C.n ≤ 20

/-- the whole check for one class: all case CNFs (each with its unit `r`), orbit cover of `B*`. -/
def checkAll (cnfs : List (CNF Nat × Nat)) (Bs : Nat) (wit : List (Nat × List Nat × List Nat × Nat)) : Bool :=
  let U := C.univ.toArray
  C.clsSane && C.orbitOk U Bs (cnfs.map (·.2)) wit &&
  cnfs.all fun (f, r) => r < U.size && f.clauses.all (fun c => C.clauseOk U r c.literals)

end Cls

def cls33 : Cls := ⟨15, 1023, 31775, 15841, 24290, 11, 11, 12, 12, 0⟩
def cls34 : Cls := ⟨14, 1023, 15391, 15841, 16098, 11, 12, 12, 12, 0⟩
/-- (2,4) without N24 (flag bit 2 = N24 off), as in tree_24x. -/
def cls24x : Cls := ⟨15, 2047, 30751, 31201, 32354, 10, 12, 12, 12, 2⟩

end TrCheck
