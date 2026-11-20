module

public import LeanQbe.T.LeanLCNF.Basic

/-!
# Idiomatic Lean 4 demo programs compiled through impure `LCNF` → `LeanQbe.T`

Four functional programs, spliced from the Lean compiler's real impure LCNF via `lcnf_of_lean!`:

1. `RBNode`: an Okasaki red-black tree map (`insert`, `find?`, `fold`, `mapValues`) with shared
   `balance` join points, `sproj`/`sset` colour fields, and FBIP in-place node reuse
   (`isShared` → `oset`/`setTag`) on linear trees vs path copying on persistent snapshots.
2. `mergeSort` with the higher-order combinators `lmap`/`lfilter`/`lfoldl`/`lzipWith`, exercising
   `pap` closures with exact, under- (`lpartial`) and over-application (`konst`).
3. `dpll`: a purely functional DPLL SAT solver (unit propagation, branching, backtracking) on
   pigeonhole `PHP(n, m)` and random 3-SAT instances.
4. `ExprVM`: an expression compiler to a stack bytecode with unboxed `UInt64` fields
   (`sproj`/`sset`) and a 6-parameter tail-recursive VM loop (`extra_args` spilling).

The text between the `BEGIN`/`END LCNF DEMO` markers is extracted verbatim by `test/lcnf/run.sh`
into the native `lean -c` reference oracle, so all backends run the *same* source.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF.Demo

-- BEGIN LCNF DEMO
/-! ### 1. Okasaki red-black tree map (`Nat ↦ Nat`) -/

inductive RBColor where
  | red | black

inductive RBNode where
  | leaf
  | node (c : RBColor) (l : RBNode) (k : Nat) (v : Nat) (r : RBNode)

namespace RBNode
open RBColor

def balance : RBColor → RBNode → Nat → Nat → RBNode → RBNode
  | black, node red (node red a xk xv b) yk yv c, zk, zv, d
  | black, node red a xk xv (node red b yk yv c), zk, zv, d
  | black, a, xk, xv, node red (node red b yk yv c) zk zv d
  | black, a, xk, xv, node red b yk yv (node red c zk zv d) =>
    node red (node black a xk xv b) yk yv (node black c zk zv d)
  | c, a, k, v, b => node c a k v b

def ins : RBNode → Nat → Nat → RBNode
  | leaf, k, v => node red leaf k v leaf
  | node c l k' v' r, k, v =>
    if k < k' then balance c (ins l k v) k' v' r
    else if k' < k then balance c l k' v' (ins r k v)
    else node c l k v r

def setBlack : RBNode → RBNode
  | node _ l k v r => node black l k v r
  | leaf => leaf

def insert (t : RBNode) (k v : Nat) : RBNode := setBlack (ins t k v)

def find? : RBNode → Nat → Option Nat
  | leaf, _ => none
  | node _ l k' v r, k =>
    if k < k' then find? l k else if k' < k then find? r k else some v

def fold (f : Nat → Nat → Nat → Nat) : Nat → RBNode → Nat
  | acc, leaf => acc
  | acc, node _ l k v r => fold f (f (fold f acc l) k v) r

def mapValues (f : Nat → Nat) : RBNode → RBNode
  | leaf => leaf
  | node c l k v r => node c (mapValues f l) k (f v) (mapValues f r)

/-- Black height if the red-black invariants hold, else `0` (`leaf` has height `1`). -/
def blackHeight : RBNode → Nat
  | leaf => 1
  | node c l _ _ r =>
    let hl := blackHeight l
    let hr := blackHeight r
    let redOk := match c, l, r with
      | red, node red .., _ => false
      | red, _, node red .. => false
      | _, _, _ => true
    if hl == 0 || hl != hr || !redOk then 0
    else match c with
      | black => hl + 1
      | red => hl

end RBNode

def modP : Nat := 1000000007

def rbBuild : Nat → Nat → RBNode → RBNode
  | 0, _, t => t
  | i + 1, n, t => rbBuild i n (t.insert ((i * 7919) % n) (i * i % 1000))

def rbHits (t : RBNode) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
    match t.find? i with
    | some v => rbHits t i ((acc + v + 1) % modP)
    | none => rbHits t i acc

def rbSum (t : RBNode) : Nat := t.fold (fun acc k v => (acc * 31 + k * 7 + v) % modP) 0

/-- Build `n` keys (linear: every insert mutates nodes in place), query, `mapValues` in place. -/
def rbBench (n : Nat) : Nat :=
  let t := rbBuild n n .leaf
  let bh := t.blackHeight
  let s1 := rbSum t
  let h := rbHits t (n + 10) 0
  let t2 := t.mapValues (fun v => v * 3 + 1)
  let s2 := rbSum t2
  ((s1 * 1009 + s2) % modP * 1013 + h) % modP * 64 + bh

/-- Persistent snapshots: `t1` stays live while `t2 := t1.insert ..` path-copies. -/
def rbPersist (n : Nat) : Nat :=
  let t1 := rbBuild n n .leaf
  let t2 := t1.insert n 4242
  let t3 := t1.mapValues (· + 5)
  let a := match t1.find? n with | some _ => 1 | none => 0
  let b := match t2.find? n with | some v => v | none => 0
  let c := match t3.find? 0 with | some v => v | none => 0
  ((rbSum t1 * 31 + rbSum t2) % modP * 31 + rbSum t3) % modP * 8 + a + 2 * b + 3 * c

/-- `reps` passes of `mapValues` over a *linear* tree: every pass updates the nodes in place
(FBIP: `isShared` is false, so `oset` reuses each cell and nothing is allocated). -/
def rbMapIter : Nat → RBNode → RBNode
  | 0, t => t
  | r + 1, t => rbMapIter r (t.mapValues (· + 1))

def rbLinear (n reps : Nat) : Nat := rbSum (rbMapIter reps (rbBuild n n .leaf))

/-- The same passes while every old version stays live: each pass path-copies all nodes. -/
def rbSharedIter : Nat → RBNode → Nat → Nat
  | 0, t, acc => (acc * 7 + rbSum t) % modP
  | r + 1, t, acc =>
    let t' := t.mapValues (· + 1)
    rbSharedIter r t' ((acc * 7 + rbSum t) % modP)

def rbShared (n reps : Nat) : Nat := rbSharedIter reps (rbBuild n n .leaf) 0

/-! ### 2. `mergeSort` and higher-order combinators -/

def msplit : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
    match msplit rest with
    | (a, b) => (x :: a, y :: b)

def mmerge : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: mmerge xs (y :: ys) else y :: mmerge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

partial def mergeSort (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | [x] => [x]
  | _ =>
    match msplit xs with
    | (a, b) => mmerge (mergeSort a) (mergeSort b)

def lmap (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => f x :: lmap f xs

def lfilter (p : Nat → Bool) : List Nat → List Nat
  | [] => []
  | x :: xs => if p x then x :: lfilter p xs else lfilter p xs

def lfoldl (f : Nat → Nat → Nat) : Nat → List Nat → Nat
  | acc, [] => acc
  | acc, x :: xs => lfoldl f (f acc x) xs

def lzipWith (f : Nat → Nat → Nat) : List Nat → List Nat → List Nat
  | x :: xs, y :: ys => f x y :: lzipWith f xs ys
  | _, _ => []

/-- `[f x | x ∈ xs]` for a binary `f`: each `f x` is an *under*-application. -/
def lpartial (f : Nat → Nat → Nat) : List Nat → List (Nat → Nat)
  | [] => []
  | x :: xs => f x :: lpartial f xs

def lapplyAll (k : Nat) : List (Nat → Nat) → Nat → Nat
  | [], acc => acc
  | g :: gs, acc => lapplyAll k gs ((acc * 7 + g k) % modP)

def lcgNext (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def lcgList : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | n + 1, s, acc => lcgList n (lcgNext s) ((s / 65536) % 10000 :: acc)

def isSorted : List Nat → Bool
  | x :: y :: rest => x ≤ y && isSorted (y :: rest)
  | _ => true

def llength : List Nat → Nat → Nat
  | [], n => n
  | _ :: xs, n => llength xs (n + 1)

@[noinline] def weight (a b c : Nat) : Nat := a + 2 * b + 3 * c

/-- Returns its first argument: `konst g` is a closure with one missing argument whose result is
again a function, so `lfoldl (konst g)` *over*-applies it. -/
@[noinline] def konst {α : Type} (a : α) (_ : Nat) : α := a

@[noinline] def stage (a : Nat) : Nat → Nat → Nat :=
  let t := weight a a 1
  fun b c => (t * b + c) % modP

def sortBench (n seed : Nat) : Nat :=
  let xs := lcgList n seed []
  let ys := mergeSort xs
  let sorted := if isSorted ys then 1 else 0
  let scale := seed % 5 + 2
  let zs := lmap (fun x => x * scale + seed % 7) ys
  let ws := lfilter (fun x => x % 3 != 0) zs
  let s := lfoldl (fun acc x => (acc * 31 + x) % modP) 0 ws
  let ps := lzipWith (weight seed) ys ws
  let p := lfoldl (fun acc x => (acc + x) % modP) 0 ps
  let gs := lpartial (weight n) (lmap (· % 100) ys)
  let g := lapplyAll 3 gs 0
  let st := lfoldl (stage scale) 1 (lmap (· % 10) ys)
  let ov := lfoldl (konst (fun y => y * 2 + scale)) 0 ys
  ((((s * 31 + p) % modP * 31 + g) % modP * 31 + st % modP) % modP * 4096
    + (llength ws 0 + ov) % 2048) * 2 + sorted

/-! ### 3. `LcnfDpll`: a purely functional DPLL SAT solver -/

def litNeg (l : Nat) : Nat := if l % 2 == 0 then l + 1 else l - 1

def clauseHas : List Nat → Nat → Bool
  | [], _ => false
  | x :: xs, l => x == l || clauseHas xs l

def clauseDrop (l : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x == l then clauseDrop l xs else x :: clauseDrop l xs

def assign (l : Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | c :: cs => if clauseHas c l then assign l cs else clauseDrop (litNeg l) c :: assign l cs

def findUnit : List (List Nat) → Option Nat
  | [] => none
  | [l] :: _ => some l
  | _ :: cs => findUnit cs

def hasEmpty : List (List Nat) → Bool
  | [] => false
  | [] :: _ => true
  | _ :: cs => hasEmpty cs

/-- Returns `2 * nodes + sat`. -/
def dpll : Nat → List (List Nat) → Nat
  | 0, _ => 0
  | fuel + 1, cnf =>
    match cnf with
    | [] => 3
    | (l :: _) :: _ =>
      if hasEmpty cnf then 2
      else match findUnit cnf with
        | some u => dpll fuel (assign u cnf) + 2
        | none =>
          let r1 := dpll fuel (assign l cnf)
          if r1 % 2 == 1 then r1 + 2 else r1 + dpll fuel (assign (litNeg l) cnf) + 2
    | [] :: _ => 2

def phpRow (i m : Nat) : Nat → List Nat → List Nat
  | 0, acc => acc
  | j + 1, acc => phpRow i m j (2 * (i * m + j) :: acc)

def phpAtLeast (m : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, acc => acc
  | i + 1, acc => phpAtLeast m i (phpRow i m m [] :: acc)

def phpPairs (m j i : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, acc => acc
  | i' + 1, acc => phpPairs m j i i' ([2 * (i * m + j) + 1, 2 * (i' * m + j) + 1] :: acc)

def phpAtMostI (m j : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, acc => acc
  | i + 1, acc => phpAtMostI m j i (phpPairs m j i i acc)

def phpAtMost (n m : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, acc => acc
  | j + 1, acc => phpAtMost n m j (phpAtMostI m j n acc)

/-- Pigeonhole `PHP(n, m)`: `n` pigeons into `m` holes (UNSAT iff `n > m`). -/
def php (n m : Nat) : List (List Nat) := phpAtLeast m n (phpAtMost n m m [])

def rand3 (nv : Nat) : Nat → Nat → List (List Nat) → List (List Nat)
  | 0, _, acc => acc
  | c + 1, s, acc =>
    let s1 := lcgNext s
    let s2 := lcgNext s1
    let s3 := lcgNext s2
    let lit (x : Nat) := 2 * ((x / 65536) % nv) + (x / 8) % 2
    rand3 nv c s3 ([lit s1, lit s2, lit s3] :: acc)

/-- `kind = 0`: `PHP(a, b)`; `kind = 1`: random 3-SAT with `a` vars, `b` clauses, `seed`. -/
def satSolve (kind a b seed : Nat) : Nat :=
  let cnf := if kind == 0 then php a b else rand3 a b seed []
  dpll 10000 cnf

/-! ### 4. `ExprVM`: expression compiler and tail-recursive `UInt64` stack VM -/

inductive VExpr where
  | lit (v : UInt64)
  | var (i : Nat)
  | add (a b : VExpr)
  | mul (a b : VExpr)
  | xor (a b : VExpr)

inductive Instr where
  | push (v : UInt64)
  | load (i : Nat)
  | add
  | mul
  | xor

inductive Stk where
  | nil
  | cons (v : UInt64) (s : Stk)

def vcompile : VExpr → List Instr → List Instr
  | .lit v, k => .push v :: k
  | .var i, k => .load i :: k
  | .add a b, k => vcompile a (vcompile b (.add :: k))
  | .mul a b, k => vcompile a (vcompile b (.mul :: k))
  | .xor a b, k => vcompile a (vcompile b (.xor :: k))

def sel (i : Nat) (a b c d : UInt64) : UInt64 :=
  if i == 0 then a else if i == 1 then b else if i == 2 then c else d

def veval (r0 r1 r2 r3 : UInt64) : VExpr → UInt64
  | .lit v => v
  | .var i => sel i r0 r1 r2 r3
  | .add a b => veval r0 r1 r2 r3 a + veval r0 r1 r2 r3 b
  | .mul a b => veval r0 r1 r2 r3 a * veval r0 r1 r2 r3 b
  | .xor a b => veval r0 r1 r2 r3 a ^^^ veval r0 r1 r2 r3 b

/-- Tail-recursive stack machine (6 parameters: exercises `extra_args` spilling). -/
def run : List Instr → Stk → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | [], .cons v _, _, _, _, _ => v
  | [], .nil, _, _, _, _ => 0
  | .push v :: rest, s, a, b, c, d => run rest (.cons v s) a b c d
  | .load i :: rest, s, a, b, c, d => run rest (.cons (sel i a b c d) s) a b c d
  | .add :: rest, .cons y (.cons x s), a, b, c, d => run rest (.cons (x + y) s) a b c d
  | .mul :: rest, .cons y (.cons x s), a, b, c, d => run rest (.cons (x * y) s) a b c d
  | .xor :: rest, .cons y (.cons x s), a, b, c, d => run rest (.cons (x ^^^ y) s) a b c d
  | _ :: _, _, _, _, _, _ => 0

def genExpr : Nat → Nat → VExpr
  | 0, s => if s % 3 == 0 then .lit (UInt64.ofNat (s % 1000)) else .var (s % 4)
  | d + 1, s =>
    let s1 := lcgNext s
    let s2 := lcgNext s1
    match (s / 65536) % 3 with
    | 0 => .add (genExpr d s1) (genExpr d s2)
    | 1 => .mul (genExpr d s1) (genExpr d s2)
    | _ => .xor (genExpr d s1) (genExpr d s2)

def vmLoop (code : List Instr) (e : VExpr) : Nat → UInt64 → Nat → UInt64 × Nat
  | 0, acc, ok => (acc, ok)
  | i + 1, acc, ok =>
    let x := UInt64.ofNat i
    let r := run code .nil x (acc >>> 7) (x * 3) (acc ^^^ x)
    let ok' := if i % 64 == 0 then
        (if r == veval x (acc >>> 7) (x * 3) (acc ^^^ x) e then ok + 1 else ok) else ok
    vmLoop code e i (acc * 1000003 + r) ok'

def vmBench (n depth seed : Nat) : UInt64 :=
  let e := genExpr depth seed
  let code := vcompile e []
  match vmLoop code e n 7 0 with
  | (acc, ok) => acc + UInt64.ofNat ok
-- END LCNF DEMO

/-! The demo program: real impure LCNF of the entry points and their transitive callees. -/
lcnf_of_lean! demoMod [rbBench, rbPersist, rbLinear, rbShared, sortBench, satSolve, vmBench]

end LeanQbe.T.LeanLCNF.Demo
