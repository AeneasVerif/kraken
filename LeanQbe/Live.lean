module

public import LeanQbe.WP

/-!
# Liveness (QBE `live.c`), untrusted

Nothing here is trusted: the lowering checks every hint it gets (`Rega.lean`), so this file has no
lemmas. It computes, for a term at `V := Nat, L := Nat`,

* `Tree`: a first-order view with exactly the name and label numbering `Rega.lower` uses
  (`toTree` replays `lower`'s traversal order: `jnz` lowers the else branch first, a `block`
  lowers its `rest` before its body);
* `liveLabels`: the values live into each join point, by a fixpoint over the jumps;
* `liveIn`: the values live into a subterm, given the label live sets.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Live

/-- First-order view of a term, numbered as `Rega.lower` numbers it. -/
inductive Tree
  | let_ (x : Nat) (op : Op Nat) (k : Tree)
  | load (x : Nat) (a : Arg Nat) (k : Tree)
  | store (v a : Arg Nat) (k : Tree)
  /-- `jnz c`: the then branch starts at label `l`. -/
  | jnz (c : Nat) (l : Nat) (t e : Tree)
  | jump (j : Nat) (args : List (Arg Nat))
  | ret (vs : List (Arg Nat))
  /-- `hlt`, and everything `lower` rejects. -/
  | stop
  | param (x : Nat) (k : Tree)
  | label (l : Nat) (k : Tree)
  /-- The block defining label `l`, then the rest of the group. -/
  | block (l : Nat) (b rest : Tree)
  deriving Inhabited, Repr

/-- Replay `Rega.lower`'s traversal: returns the tree, the next fresh name and label. -/
def toTree : Expr Nat Nat → Nat → Nat → List Nat → Tree × Nat × Nat
  | .param f, nv, nl, _ =>
    let (t, nv', nl') := toTree (f nv) (nv + 1) nl []
    (.param nv t, nv', nl')
  | .let_ op k, nv, nl, _ =>
    let (t, nv', nl') := toTree (k nv) (nv + 1) nl []
    (.let_ nv op t, nv', nl')
  | .load _ _ _ a k, nv, nl, _ =>
    let (t, nv', nl') := toTree (k nv) (nv + 1) nl []
    (.load nv a t, nv', nl')
  | .store _ v a k, nv, nl, _ =>
    let (t, nv', nl') := toTree k nv nl []
    (.store v a t, nv', nl')
  | .call _ _ _, nv, nl, _ => (.stop, nv, nl)
  | .jnz (.imm c) t e, nv, nl, _ =>
    if Truthy c then toTree t nv nl [] else toTree e nv nl []
  | .jnz (.var x) t e, nv, nl, _ =>
    let (te, nv1, nl1) := toTree e nv (nl + 1) []
    let (tt, nv2, nl2) := toTree t nv1 nl1 []
    (.jnz x nl tt te, nv2, nl2)
  | .jump j as, nv, nl, _ => (.jump j as, nv, nl)
  | .ret vs, nv, nl, _ => (.ret vs, nv, nl)
  | .exit _ _, nv, nl, _ => (.stop, nv, nl)
  | .hlt, nv, nl, _ => (.stop, nv, nl)
  | .label f, nv, nl, pend =>
    let (t, nv', nl') := toTree (f nl) nv (nl + 1) (pend ++ [nl])
    (.label nl t, nv', nl')
  | .block b rest, nv, nl, pend =>
    match pend with
    | [] => (.stop, nv, nl)
    | ℓ :: pend' =>
      let (tr, nv1, nl1) := toTree rest nv nl pend'
      let (tb, nv2, nl2) := toTree b nv1 nl1 []
      (.block ℓ tb tr, nv2, nl2)

def Tree.ofFn (f : Fn) : Tree := (toTree (f.body Nat Nat) 0 0 []).1

/-! ### Small set operations on lists -/

def union (a b : List Nat) : List Nat := b.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) a

def argVars (as : List (Arg Nat)) : List Nat := as.filterMap fun | .var x => some x | .imm _ => none

def opVars : Op Nat → List Nat
  | .bin _ _ a b => argVars [a, b]
  | .cmp _ _ a b => argVars [a, b]
  | .ext _ _ _ a => argVars [a]
  | .copy _ a => argVars [a]

/-! ### Join points -/

/-- Every block of the tree: label, body (starting with its parameters). -/
def Tree.blocks : Tree → List (Nat × Tree)
  | .let_ _ _ k | .load _ _ k | .store _ _ k | .param _ k | .label _ k => k.blocks
  | .jnz _ _ t e => t.blocks ++ e.blocks
  | .block l b rest => (l, b) :: b.blocks ++ rest.blocks
  | .jump _ _ | .ret _ | .stop => []

/-- The parameters at the start of a block body, and the body after them. -/
def Tree.params : Tree → List Nat × Tree
  | .param x k => let (ps, b) := k.params; (x :: ps, b)
  | t => ([], t)

abbrev LiveMap := List (Nat × List Nat)

def LiveMap.get (L : LiveMap) (l : Nat) : List Nat := ((L.find? (·.1 == l)).map (·.2)).getD []

/-- Values live into a subterm; a jump needs its arguments and the values live into its target. -/
def liveIn (L : LiveMap) : Tree → List Nat
  | .let_ x op k => union ((liveIn L k).filter (· != x)) (opVars op)
  | .load x a k => union ((liveIn L k).filter (· != x)) (argVars [a])
  | .store v a k => union (liveIn L k) (argVars [v, a])
  | .jnz c _ t e => union (union (liveIn L t) (liveIn L e)) [c]
  | .jump j as => union (argVars as) (L.get j)
  | .ret vs => argVars vs
  | .stop => []
  | .param x k => (liveIn L k).filter (· != x)
  | .label _ k => liveIn L k
  | .block _ _ rest => liveIn L rest

/-- Values live into every join point: the least fixpoint, by iteration. -/
def liveLabels (t : Tree) : LiveMap :=
  let bs := t.blocks
  let step (L : LiveMap) : LiveMap := bs.map fun (l, b) => (l, liveIn L b)
  let rec go : Nat → LiveMap → LiveMap
    | 0, L => L
    | n + 1, L => let L' := step L; if L'.map (·.2.length) == L.map (·.2.length) then L else go n L'
  go (8 * bs.length + 8) (bs.map fun (l, _) => (l, []))

end Live
end LeanQbe
