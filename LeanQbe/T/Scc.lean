module

public import LeanQbe.T.Module
public import LeanQbe.T.Trie

/-!
# Call Graph Extraction, Untrusted Tarjan SCC Condensation, and Verified Order Checker

Provides:
* `Fn.callees` & `callGraph`: syntactic callee extraction over PHOAS `Expr`/`Blocks` (including
  both arms of `.jnz`, matching `Expr.callsOk`).
* `sccOrder`: untrusted kernel-reducible Tarjan condensation in callees-first topological order
  (pure structural recursion on fuel over `Trie` state; zero `WellFounded.fix`).
* `checkSccOrder`: verified boolean checker validating non-emptiness, global name uniqueness
  disjoint from `extSigs`, and topological call/exit closure (`earlier ++ own ++ extSigs`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## 1. Syntactic Call Graph Extraction -/

/-- Insert `e` into `cs` unless a `SigEntry.beq`-equal signature is already present. -/
def addCalleeEntry (e : SigEntry) (cs : List SigEntry) : List SigEntry :=
  if cs.any (SigEntry.beq e) then cs else e :: cs

mutual
/-- Collect all syntactic call signatures `(f, as, bs)` occurring anywhere in `e`. -/
def Expr.calleesAux {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → List SigEntry → List SigEntry
  | .let_ (ts := ts) _ k, cs => Expr.calleesAux (k (Tup.units ts)) cs
  | .load _ _ k, cs => Expr.calleesAux (k ()) cs
  | .store _ _ k, cs => Expr.calleesAux k cs
  | .call f (as := as) (bs := bs) _ k, cs =>
      Expr.calleesAux (k (Tup.units bs)) (addCalleeEntry (f, as, bs) cs)
  | .jnz _ t e, cs => Expr.calleesAux e (Expr.calleesAux t cs)
  | .jump _ _, cs | .ret _, cs | .hlt, cs | .exit _ _, cs => cs
  | .group (sig := sig) bodies k, cs =>
      let ls := Tup.units sig
      Blocks.calleesAux (bodies ls) (Expr.calleesAux (k ls) cs)

/-- Mutual helper for `Expr.calleesAux` over `Blocks`. -/
def Blocks.calleesAux {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig →
    List SigEntry → List SigEntry
  | _, .nil, cs => cs
  | _, .cons (ts := ts) b bs, cs =>
      Blocks.calleesAux bs (Expr.calleesAux (b (Tup.units ts)) cs)
end

/-- Deduplicated list of callee signatures referenced in `fn.body`. -/
def Fn.callees (fn : Fn) : List SigEntry :=
  (Expr.calleesAux (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as)) []).reverse

/-- Syntactic call graph of `fns`, mapping each function name to its callee signatures. -/
def callGraph (fns : List Fn) : List (Sym × List SigEntry) :=
  fns.map fun fn => (fn.name, fn.callees)

/-! ## 2. Untrusted Tarjan SCC Condensation (Callees-First Order) -/

def enumList {α : Type 1} : List α → Nat → List (Nat × α)
  | [], _ => []
  | x :: xs, i => (i, x) :: enumList xs (i + 1)

def adjOfCallees (sigs : List (Nat × SigEntry)) (callees : List SigEntry) : List Nat :=
  sigs.filterMap fun (v, sig) =>
    if callees.any (SigEntry.beq sig) then some v else none

def buildAdjTrie (fns : List Fn) : Trie (List Nat) × Nat :=
  let indexed := enumList fns 0
  let sigs := indexed.map fun (i, fn) => (i, fn.sig)
  indexed.foldl
    (fun (t, eCount) (i, fn) =>
      let vs := adjOfCallees sigs fn.callees
      (t.insert i vs, eCount + vs.length))
    (.empty, 0)

structure TarjanState where
  nextIdx : Nat := 0
  idx : Trie Nat := .empty
  low : Trie Nat := .empty
  onStack : Trie Bool := .empty
  stack : List Nat := []
  sccs : List (List Nat) := []

inductive DfsFrame where
  | enter (u : Nat)
  | edge (u : Nat) (vs : List Nat)
  | finishEdge (u v : Nat) (vs : List Nat)
  | exit (u : Nat)

def popUntil (root : Nat) (acc : List Nat) (onSt : Trie Bool) :
    List Nat → List Nat × List Nat × Trie Bool
  | [] => (acc, [], onSt)
  | v :: vs =>
      let onSt' := onSt.insert v false
      let acc' := v :: acc
      if v == root then (acc', vs, onSt')
      else popUntil root acc' onSt' vs

def tarjanRun (adj : Trie (List Nat)) :
    Nat → List DfsFrame → TarjanState → TarjanState
  | 0, _, st => st
  | _, [], st => st
  | fuel + 1, .enter u :: frames, st =>
      match st.idx.find? u with
      | some _ => tarjanRun adj fuel frames st
      | none =>
          let uIdx := st.nextIdx
          let st' : TarjanState := {
            nextIdx := uIdx + 1
            idx := st.idx.insert u uIdx
            low := st.low.insert u uIdx
            onStack := st.onStack.insert u true
            stack := u :: st.stack
            sccs := st.sccs
          }
          let vs := adj.getD u []
          tarjanRun adj fuel (.edge u vs :: .exit u :: frames) st'
  | fuel + 1, .edge _ [] :: frames, st =>
      tarjanRun adj fuel frames st
  | fuel + 1, .edge u (v :: vs) :: frames, st =>
      match st.idx.find? v with
      | none =>
          tarjanRun adj fuel (.enter v :: .finishEdge u v vs :: frames) st
      | some vIdx =>
          let st' :=
            if st.onStack.getD v false then
              let uLow := st.low.getD u vIdx
              if vIdx < uLow then { st with low := st.low.insert u vIdx } else st
            else st
          tarjanRun adj fuel (.edge u vs :: frames) st'
  | fuel + 1, .finishEdge u v vs :: frames, st =>
      let uLow := st.low.getD u 0
      let vLow := st.low.getD v uLow
      let st' := if vLow < uLow then { st with low := st.low.insert u vLow } else st
      tarjanRun adj fuel (.edge u vs :: frames) st'
  | fuel + 1, .exit u :: frames, st =>
      let uIdx := st.idx.getD u 0
      let uLow := st.low.getD u uIdx
      if uLow == uIdx then
        let (scc, stack', onSt') := popUntil u [] st.onStack st.stack
        let st' := { st with stack := stack', onStack := onSt', sccs := scc :: st.sccs }
        tarjanRun adj fuel frames st'
      else
        tarjanRun adj fuel frames st

def tarjanOuter (adj : Trie (List Nat)) (fuel : Nat) :
    List Nat → TarjanState → TarjanState
  | [], st => st
  | u :: us, st =>
      let st' :=
        match st.idx.find? u with
        | some _ => st
        | none => tarjanRun adj fuel [.enter u] st
      tarjanOuter adj fuel us st'

def nthOpt {α : Type 1} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nthOpt xs n

/-- Untrusted Tarjan SCC condensation returning components in callees-first topological order.
Always validated downstream by `checkSccOrder`. -/
def sccOrder (fns : List Fn) : List (List Fn) :=
  let (adj, eCount) := buildAdjTrie fns
  let n := fns.length
  let fuel := 3 * n + 2 * eCount + 4
  let nodes := (enumList fns 0).map Prod.fst
  let st := tarjanOuter adj fuel nodes {}
  st.sccs.reverse.filterMap fun is =>
    let scc := is.filterMap (nthOpt fns)
    if scc.isEmpty then none else some scc

/-! ## 3. Verified Topological & Partition Checker -/

/-- Check that every SCC in `rest` is non-empty and only calls functions in `earlier`, its own
SCC `own`, or `extSigs`, and only exits to symbols in `exits`. -/
def checkSccCalls (exits : List Sym) (extSigs : List SigEntry) :
    List SigEntry → List (List Fn) → Bool
  | _, [] => true
  | earlier, scc :: rest =>
      let own := scc.map Fn.sig
      !scc.isEmpty &&
      scc.all (fun fn => fn.checkCallsOk (earlier ++ own ++ extSigs) exits) &&
      checkSccCalls exits extSigs (earlier ++ own) rest

/-- Kernel-reducible checker verifying that `sccs` has globally unique function names disjoint
from `extSigs`, has no empty SCC, and is ordered callees-first so every SCC calls only earlier
SCCs, itself, or `extSigs`. -/
def checkSccOrder (sccs : List (List Fn)) (extSigs : List SigEntry)
    (exits : List Sym := []) : Bool :=
  listNodup (sccs.flatten.map Fn.name ++ extSigs.map Prod.fst) &&
  checkSccCalls exits extSigs [] sccs

/-- Check that `sccs` is a valid callees-first SCC condensation covering `M.fns` with `M.externs`
and `M.exits`. -/
def checkModuleSccOrder (M : Module) (sccs : List (List Fn)) : Bool :=
  checkSccOrder sccs (M.externs.map Extern.sig) M.exits &&
  sccs.flatten.length == M.fns.length &&
  M.fns.all (fun fn => sccs.flatten.any (fun g => SigEntry.beq g.sig fn.sig))

end LeanQbe.T
