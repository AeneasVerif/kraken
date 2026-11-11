module

public import LeanQbe.WP

/-!
# Liveness (QBE `live.c`), untrusted

Nothing here is trusted: the lowering checks every hint it gets (`Rega.lean`), so this file has no
lemmas. It computes, for a term at `V := Nat, L := Nat`,

* `Tree`: a first-order view with exactly the numbering `Rega.lower` uses for names (`param`,
  `let_`, `load` bind the next name), labels (`label` takes the next label; `jnz` on a variable
  takes one for its then branch) and instructions (`let_`, `load`, `store`, `call`, `jnz`, `jump`,
  `ret`, `exit`, `hlt` each take the next instruction number). `toTree` replays `lower`'s traversal
  order: `jnz` lowers the else branch first, a `block` lowers its `rest` before its body, and a
  `jnz` on a constant lowers only the branch it takes;
* `liveLabels`: the values live into each join point, by a fixpoint over the jumps;
* `liveIn`: the values live into a subterm, given the label live sets;
* `acrossCalls`: the values live across some call (live after it, other than its results).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Live

/-- First-order view of a term, numbered as `Rega.lower` numbers it. `ip` is the instruction
number, whose pre-moves run before the instruction. -/
inductive Tree
  | let_ (ip x : Nat) (op : Op Nat) (k : Tree)
  | load (ip x : Nat) (a : Arg Nat) (k : Tree)
  | store (ip : Nat) (v a : Arg Nat) (k : Tree)
  /-- `call g args`; the leading `param`s of `k` bind the results. -/
  | call (ip : Nat) (g : Sym) (args : List (Arg Nat)) (k : Tree)
  /-- `jnz c` on a variable: the then branch starts at label `l`. -/
  | jnz (ip c l : Nat) (t e : Tree)
  /-- `jnz` on a constant: only the branch taken, `k`, is lowered. -/
  | skip (ip : Nat) (k : Tree)
  | jump (ip j : Nat) (args : List (Arg Nat))
  | ret (ip : Nat) (vs : List (Arg Nat))
  | exit (ip : Nat) (g : Sym) (args : List (Arg Nat))
  /-- `hlt`, and everything `lower` rejects. -/
  | stop
  | param (x : Nat) (k : Tree)
  | label (l : Nat) (k : Tree)
  /-- The block defining label `l`, then the rest of the group. -/
  | block (l : Nat) (b rest : Tree)
  deriving Inhabited, Repr

/-- Replay `Rega.lower`'s traversal from names `nv`, labels `nl`, instructions `ip` and pending
labels `pend`: returns the tree and the next fresh name, label and instruction number. -/
def toTree : Expr Nat Nat → Nat → Nat → Nat → List Nat → Tree × Nat × Nat × Nat
  | .param f, nv, nl, ip, _ =>
    let (t, r) := toTree (f nv) (nv + 1) nl ip []
    (.param nv t, r)
  | .let_ op k, nv, nl, ip, _ =>
    let (t, r) := toTree (k nv) (nv + 1) nl (ip + 1) []
    (.let_ ip nv op t, r)
  | .load _ _ _ a k, nv, nl, ip, _ =>
    let (t, r) := toTree (k nv) (nv + 1) nl (ip + 1) []
    (.load ip nv a t, r)
  | .store _ v a k, nv, nl, ip, _ =>
    let (t, r) := toTree k nv nl (ip + 1) []
    (.store ip v a t, r)
  | .call g as k, nv, nl, ip, _ =>
    let (t, r) := toTree k nv nl (ip + 1) []
    (.call ip g as t, r)
  | .jnz (.imm c) t e, nv, nl, ip, _ =>
    let (k, r) := if Truthy c then toTree t nv nl (ip + 1) [] else toTree e nv nl (ip + 1) []
    (.skip ip k, r)
  | .jnz (.var x) t e, nv, nl, ip, _ =>
    let (te, nv1, nl1, ip1) := toTree e nv (nl + 1) (ip + 1) []
    let (tt, r) := toTree t nv1 nl1 ip1 []
    (.jnz ip x nl tt te, r)
  | .jump j as, nv, nl, ip, _ => (.jump ip j as, nv, nl, ip + 1)
  | .ret vs, nv, nl, ip, _ => (.ret ip vs, nv, nl, ip + 1)
  | .exit g as, nv, nl, ip, _ => (.exit ip g as, nv, nl, ip + 1)
  | .hlt, nv, nl, ip, _ => (.stop, nv, nl, ip + 1)
  | .label f, nv, nl, ip, pend =>
    let (t, r) := toTree (f nl) nv (nl + 1) ip (pend ++ [nl])
    (.label nl t, r)
  | .block b rest, nv, nl, ip, pend =>
    match pend with
    | [] => (.stop, nv, nl, ip)
    | ℓ :: pend' =>
      let (tr, nv1, nl1, ip1) := toTree rest nv nl ip pend'
      let (tb, r) := toTree b nv1 nl1 ip1 []
      (.block ℓ tb tr, r)

def Tree.ofFn (f : Fn) : Tree := (toTree (f.body Nat Nat) 0 0 0 []).1

/-- Convert `f` to `Tree`, also returning the variable count `nv`. -/
def Tree.ofFnWithNv (f : Fn) : Tree × Nat :=
  let (t, nv, _, _) := toTree (f.body Nat Nat) 0 0 0 []
  (t, nv)

/-! ### Small set operations on lists -/

def union (a b : List Nat) : List Nat :=
  b.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) a

def argVars (as : List (Arg Nat)) : List Nat := as.filterMap fun | .var x => some x | .imm _ => none

def opVars : Op Nat → List Nat
  | .bin _ _ a b => argVars [a, b]
  | .cmp _ _ a b => argVars [a, b]
  | .ext _ _ _ a => argVars [a]
  | .copy _ a => argVars [a]

/-! ### Join points -/

/-- Every block of the tree: label, body (starting with its parameters). -/
def Tree.blocks : Tree → List (Nat × Tree)
  | .let_ _ _ _ k | .load _ _ _ k | .store _ _ _ k | .call _ _ _ k | .skip _ k | .param _ k
  | .label _ k => k.blocks
  | .jnz _ _ _ t e => t.blocks ++ e.blocks
  | .block l b rest => (l, b) :: b.blocks ++ rest.blocks
  | .jump _ _ _ | .ret _ _ | .exit _ _ _ | .stop => []

/-- The parameters at the start of a block body, and the body after them. -/
def Tree.params : Tree → List Nat × Tree
  | .param x k => let (ps, b) := k.params; (x :: ps, b)
  | t => ([], t)

abbrev LiveMap := List (Nat × List Nat)

def LiveMap.get (L : LiveMap) (l : Nat) : List Nat := ((L.find? (·.1 == l)).map (·.2)).getD []

/-- Values live into a subterm; a jump needs its arguments and the values live into its target. -/
def liveIn (L : LiveMap) : Tree → List Nat
  | .let_ _ x op k => union ((liveIn L k).filter (· != x)) (opVars op)
  | .load _ x a k => union ((liveIn L k).filter (· != x)) (argVars [a])
  | .store _ v a k => union (liveIn L k) (argVars [v, a])
  | .call _ _ as k => union (liveIn L k) (argVars as)
  | .jnz _ c _ t e => union (union (liveIn L t) (liveIn L e)) [c]
  | .skip _ k => liveIn L k
  | .jump _ j as => union (argVars as) (L.get j)
  | .ret _ vs => argVars vs
  | .exit _ _ as => argVars as
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

/-- Values live across some call of the tree: live after the call, other than its results (the
leading `param`s of the continuation remove those). -/
def acrossCalls (L : LiveMap) : Tree → List Nat
  | .call _ _ _ k => union (liveIn L k) (acrossCalls L k)
  | .let_ _ _ _ k | .load _ _ _ k | .store _ _ _ k | .skip _ k | .param _ k | .label _ k =>
    acrossCalls L k
  | .jnz _ _ _ t e => union (acrossCalls L t) (acrossCalls L e)
  | .block _ b rest => union (acrossCalls L b) (acrossCalls L rest)
  | .jump _ _ _ | .ret _ _ | .exit _ _ _ | .stop => []

/-- All jump targets appearing anywhere in a subtree. -/
def allJumps : Tree → List Nat
  | .jump _ j _ => [j]
  | .let_ _ _ _ k | .load _ _ _ k | .store _ _ _ k | .call _ _ _ k | .skip _ k | .param _ k
  | .label _ k => allJumps k
  | .jnz _ _ _ t e => union (allJumps t) (allJumps e)
  | .block _ b rest => union (allJumps b) (allJumps rest)
  | .ret _ _ | .exit _ _ _ | .stop => []

/-- Labels that lie on some cycle in the block jump graph (loop headers and mutual-loop blocks). -/
def loopBlocks (t : Tree) : List Nat :=
  let bs := t.blocks
  let adj : List (Nat × List Nat) := bs.map fun (l, b) => (l, allJumps b)
  let succs (l : Nat) : List Nat := ((adj.find? (·.1 == l)).map (·.2)).getD []
  let canReach (src target : Nat) : Bool :=
    let rec dfs : Nat → List Nat → List Nat → Bool
      | 0, _, _ => false
      | _, [], _ => false
      | fuel + 1, x :: xs, vis =>
        if x == target then true
        else if vis.contains x then dfs fuel xs vis
        else dfs fuel (succs x ++ xs) (x :: vis)
    dfs (bs.length * bs.length + bs.length + 1) (succs src) []
  (bs.filter fun (l, _) => canReach l l).map (·.1)

end Live
end LeanQbe
