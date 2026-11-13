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
* `liveLabelsArr`: the values live into each join point, by a fixpoint over the jumps;
* `fillLive`: populates every subterm with its live-in set in a single bottom-up pass;
* `acrossCalls`: the values live across some call (live after it, other than its results).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Live

/-- First-order view of a term, numbered as `Rega.lower` numbers it. `ip` is the instruction
number, whose pre-moves run before the instruction; `lv` holds the live-in set once populated by
`fillLive`. -/
inductive Tree
  | let_ (lv : List Nat) (ip x : Nat) (op : Op Nat) (k : Tree)
  | load (lv : List Nat) (ip x : Nat) (a : Arg Nat) (k : Tree)
  | store (lv : List Nat) (ip : Nat) (v a : Arg Nat) (k : Tree)
  /-- `call g args`; the leading `param`s of `k` bind the results. -/
  | call (lv : List Nat) (ip : Nat) (g : Sym) (args : List (Arg Nat)) (k : Tree)
  /-- `jnz c` on a variable: the then branch starts at label `l`. -/
  | jnz (lv : List Nat) (ip c l : Nat) (t e : Tree)
  /-- `jnz` on a constant: only the branch taken, `k`, is lowered. -/
  | skip (lv : List Nat) (ip : Nat) (k : Tree)
  | jump (lv : List Nat) (ip j : Nat) (args : List (Arg Nat))
  | ret (lv : List Nat) (ip : Nat) (vs : List (Arg Nat))
  | exit (lv : List Nat) (ip : Nat) (g : Sym) (args : List (Arg Nat))
  /-- `hlt`, and everything `lower` rejects. -/
  | stop
  | param (lv : List Nat) (x : Nat) (k : Tree)
  | label (lv : List Nat) (l : Nat) (k : Tree)
  /-- The block defining label `l`, then the rest of the group. -/
  | block (lv : List Nat) (l : Nat) (b rest : Tree)
  deriving Inhabited, Repr

/-- Replay `Rega.lower`'s traversal from names `nv`, labels `nl`, instructions `ip` and pending
labels `pend`: returns the tree and the next fresh name, label and instruction number. -/
def toTree : Expr Nat Nat → Nat → Nat → Nat → List Nat → Tree × Nat × Nat × Nat
  | .param f, nv, nl, ip, _ =>
    let (t, r) := toTree (f nv) (nv + 1) nl ip []
    (.param [] nv t, r)
  | .let_ op k, nv, nl, ip, _ =>
    let (t, r) := toTree (k nv) (nv + 1) nl (ip + 1) []
    (.let_ [] ip nv op t, r)
  | .load _ _ _ a k, nv, nl, ip, _ =>
    let (t, r) := toTree (k nv) (nv + 1) nl (ip + 1) []
    (.load [] ip nv a t, r)
  | .store _ v a k, nv, nl, ip, _ =>
    let (t, r) := toTree k nv nl (ip + 1) []
    (.store [] ip v a t, r)
  | .call g as k, nv, nl, ip, _ =>
    let (t, r) := toTree k nv nl (ip + 1) []
    (.call [] ip g as t, r)
  | .jnz (.imm c) t e, nv, nl, ip, _ =>
    let (k, r) := if Truthy c then toTree t nv nl (ip + 1) [] else toTree e nv nl (ip + 1) []
    (.skip [] ip k, r)
  | .jnz (.var x) t e, nv, nl, ip, _ =>
    let (te, nv1, nl1, ip1) := toTree e nv (nl + 1) (ip + 1) []
    let (tt, r) := toTree t nv1 nl1 ip1 []
    (.jnz [] ip x nl tt te, r)
  | .jump j as, nv, nl, ip, _ => (.jump [] ip j as, nv, nl, ip + 1)
  | .ret vs, nv, nl, ip, _ => (.ret [] ip vs, nv, nl, ip + 1)
  | .exit g as, nv, nl, ip, _ => (.exit [] ip g as, nv, nl, ip + 1)
  | .hlt, nv, nl, ip, _ => (.stop, nv, nl, ip + 1)
  | .label f, nv, nl, ip, pend =>
    let (t, r) := toTree (f nl) nv (nl + 1) ip (pend ++ [nl])
    (.label [] nl t, r)
  | .block b rest, nv, nl, ip, pend =>
    match pend with
    | [] => (.stop, nv, nl, ip)
    | ℓ :: pend' =>
      let (tr, nv1, nl1, ip1) := toTree rest nv nl ip pend'
      let (tb, r) := toTree b nv1 nl1 ip1 []
      (.block [] ℓ tb tr, r)

/-- Convert `f` to `Tree`, also returning `(nv, nl, ip)`. -/
def Tree.ofFnWithSizes (f : Fn) : Tree × Nat × Nat × Nat :=
  toTree (f.body Nat Nat) 0 0 0 []

/-- Precomputed live-in set stored on a tree node. -/
def Tree.lv : Tree → List Nat
  | .let_ lv .. | .load lv .. | .store lv .. | .call lv .. | .jnz lv ..
  | .skip lv .. | .jump lv .. | .ret lv .. | .exit lv .. | .param lv ..
  | .label lv .. | .block lv .. => lv
  | .stop => []

/-! ### Non-recursive 4-way array keyed by `Nat` (avoids `brecOn` in the kernel) -/

inductive Q4 (α : Type)
  | mk (m1 m2 m3 : Nat) (c0 c1 c2 c3 : α)

def Q4.build {α : Type} (sub : Nat → α × Nat) (i0 : Nat) : Q4 α × Nat :=
  let (c0, m1) := sub i0; let (c1, m2) := sub m1; let (c2, m3) := sub m2; let (c3, i4) := sub m3
  (.mk m1 m2 m3 c0 c1 c2 c3, i4)

def Q4.get {α β : Type} (x : Nat) (sub : α → β) : Q4 α → β
  | .mk m1 m2 m3 c0 c1 c2 c3 =>
    match Nat.ble (x + 1) m2 with
    | true => match Nat.ble (x + 1) m1 with | true => sub c0 | false => sub c1
    | false => match Nat.ble (x + 1) m3 with | true => sub c2 | false => sub c3

def Q4.mod {α : Type} (x : Nat) (sub : α → α) : Q4 α → Q4 α
  | .mk m1 m2 m3 c0 c1 c2 c3 =>
    match Nat.ble (x + 1) m2 with
    | true =>
      match Nat.ble (x + 1) m1 with
      | true => .mk m1 m2 m3 (sub c0) c1 c2 c3
      | false => .mk m1 m2 m3 c0 (sub c1) c2 c3
    | false =>
      match Nat.ble (x + 1) m3 with
      | true => .mk m1 m2 m3 c0 c1 (sub c2) c3
      | false => .mk m1 m2 m3 c0 c1 c2 (sub c3)

abbrev Q16 (α : Type) := Q4 (Q4 α)
def Q16.build {α : Type} (b : Nat → α × Nat) : Nat → Q16 α × Nat := Q4.build (Q4.build b)
def Q16.get {α β : Type} (x : Nat) (f : α → β) : Q16 α → β := Q4.get x (Q4.get x f)
def Q16.mod {α : Type} (x : Nat) (f : α → α) : Q16 α → Q16 α := Q4.mod x (Q4.mod x f)

/-- A table indexed by `Nat`, at one of four fixed depths, for up to 65,536 entries. Larger indices
share the last entry; the tables only feed hints, so that cannot produce wrong code. -/
inductive Arr (α : Type)
  | d2 (t : Q16 α)
  | d4 (t : Q16 (Q16 α))
  | d6 (t : Q16 (Q16 (Q16 α)))
  | d8 (t : Q16 (Q16 (Q16 (Q16 α))))

def Arr.ofSize {α : Type} (n : Nat) (d : α) : Arr α :=
  let b0 := fun (i : Nat) => (d, i + 1)
  if Nat.ble n 16 then .d2 (Q16.build b0 0).1
  else if Nat.ble n 256 then .d4 (Q16.build (Q16.build b0) 0).1
  else if Nat.ble n 4096 then .d6 (Q16.build (Q16.build (Q16.build b0)) 0).1
  else .d8 (Q16.build (Q16.build (Q16.build (Q16.build b0))) 0).1

def Arr.get {α : Type} (a : Arr α) (x : Nat) : α :=
  match a with
  | .d2 q => Q16.get x id q
  | .d4 q => Q16.get x (Q16.get x id) q
  | .d6 q => Q16.get x (Q16.get x (Q16.get x id)) q
  | .d8 q => Q16.get x (Q16.get x (Q16.get x (Q16.get x id))) q

def Arr.mod {α : Type} (a : Arr α) (x : Nat) (f : α → α) : Arr α :=
  match a with
  | .d2 q => .d2 (Q16.mod x f q)
  | .d4 q => .d4 (Q16.mod x (Q16.mod x f) q)
  | .d6 q => .d6 (Q16.mod x (Q16.mod x (Q16.mod x f)) q)
  | .d8 q => .d8 (Q16.mod x (Q16.mod x (Q16.mod x (Q16.mod x f))) q)

def Arr.set {α : Type} (a : Arr α) (x : Nat) (val : α) : Arr α := a.mod x (fun _ => val)
def Arr.push {α : Type} (a : Arr (List α)) (x : Nat) (v : α) : Arr (List α) := a.mod x (v :: ·)

/-! ### Small set operations on lists -/

def natMem (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => match Nat.beq x y with | true => true | false => natMem x ys

def eraseRev (x : Nat) : List Nat → List Nat → List Nat
  | [], acc => acc
  | y :: ys, acc =>
    match Nat.beq y x with | true => eraseRev x ys acc | false => eraseRev x ys (y :: acc)

def erase (x : Nat) (xs : List Nat) : List Nat := (eraseRev x xs []).reverse

def unionAux : List Nat → List Nat → List Nat
  | [], acc => acc.reverse
  | x :: xs, acc =>
    match natMem x acc with | true => unionAux xs acc | false => unionAux xs (x :: acc)

def union (a b : List Nat) : List Nat := unionAux b a.reverse
def dedup (xs : List Nat) : List Nat := unionAux xs []

def argVars (as : List (Arg Nat)) : List Nat :=
  as.filterMap fun | .var x => some x | .imm _ => none

def opVars : Op Nat → List Nat
  | .bin _ _ a b | .cmp _ _ a b => dedup (argVars [a, b])
  | .ext _ _ _ a | .copy _ a => argVars [a]

/-! ### Join points -/

/-- Every block of the tree: label, body (starting with its parameters). -/
def Tree.blocks : Tree → List (Nat × Tree)
  | .let_ _ _ _ _ k | .load _ _ _ _ k | .store _ _ _ _ k | .call _ _ _ _ k | .skip _ _ k
  | .param _ _ k | .label _ _ k => k.blocks
  | .jnz _ _ _ _ t e => t.blocks ++ e.blocks
  | .block _ l b rest => (l, b) :: b.blocks ++ rest.blocks
  | .jump .. | .ret .. | .exit .. | .stop => []

def Tree.paramVars : Tree → List Nat
  | .param _ x k => x :: k.paramVars
  | _ => []

/-- The node `mk lv` together with its live-in set `lv`, which `fillLive` hands to the parent. -/
def withLv (lv : List Nat) (mk : List Nat → Tree) : List Nat × Tree := (lv, mk lv)

/-- Populate every node of `t` with its live-in set under `lTree`, in a single bottom-up pass. -/
def fillLive (lTree : Arr (List Nat)) : Tree → List Nat × Tree
  | .let_ _ ip x op k =>
    let (klv, k) := fillLive lTree k
    withLv (unionAux (opVars op) (eraseRev x klv [])) fun lv => .let_ lv ip x op k
  | .load _ ip x a k =>
    let (klv, k) := fillLive lTree k
    withLv (unionAux (argVars [a]) (eraseRev x klv [])) fun lv => .load lv ip x a k
  | .store _ ip v a k =>
    let (klv, k) := fillLive lTree k
    withLv (union klv (argVars [v, a])) fun lv => .store lv ip v a k
  | .call _ ip g as k =>
    let (klv, k) := fillLive lTree k
    withLv (union klv (argVars as)) fun lv => .call lv ip g as k
  | .jnz _ ip c l t e =>
    let (tlv, t) := fillLive lTree t
    let (elv, e) := fillLive lTree e
    withLv (union (union tlv elv) [c]) fun lv => .jnz lv ip c l t e
  | .skip _ ip k => let (klv, k) := fillLive lTree k; (klv, .skip klv ip k)
  | .jump _ ip j as => withLv (union (argVars as) (lTree.get j)) fun lv => .jump lv ip j as
  | .ret _ ip vs => withLv (dedup (argVars vs)) fun lv => .ret lv ip vs
  | .exit _ ip g as => withLv (dedup (argVars as)) fun lv => .exit lv ip g as
  | .stop => ([], .stop)
  | .param _ x k => let (klv, k) := fillLive lTree k; withLv (erase x klv) fun lv => .param lv x k
  | .label _ l k => let (klv, k) := fillLive lTree k; (klv, .label klv l k)
  | .block _ l b rest =>
    let (rlv, rest) := fillLive lTree rest
    (rlv, .block rlv l (fillLive lTree b).2 rest)

/-- All jump targets appearing anywhere in a subtree. -/
def allJumps : Tree → List Nat
  | .jump _ _ j _ => [j]
  | .let_ _ _ _ _ k | .load _ _ _ _ k | .store _ _ _ _ k | .call _ _ _ _ k | .skip _ _ k
  | .param _ _ k | .label _ _ k => allJumps k
  | .jnz _ _ _ _ t e => union (allJumps t) (allJumps e)
  | .block _ _ b rest => union (allJumps b) (allJumps rest)
  | .ret .. | .exit .. | .stop => []

/-- Values live into every join point, by fixpoint iteration. -/
def liveLabelsArr (nl : Nat) (bs0 : List (Nat × Tree)) : Arr (List Nat) :=
  let bs := bs0.map fun (l, b) => (l, b, allJumps b)
  let chFalse := Arr.ofSize nl false
  let rec go : Nat → Bool → Arr (List Nat) → Arr Bool → Arr (List Nat)
    | 0, _, lTree, _ => lTree
    | n + 1, first, lTree, prevCh =>
      let (lTree', nextCh, ch) := bs.foldl (fun (lt, nch, ch) (l, b, js) =>
        if !(first || js.any prevCh.get) then (lt, nch, ch)
        else
          let lv := (fillLive lTree b).1
          if lv.length == (lt.get l).length then (lt, nch, ch)
          else (lt.set l lv, nch.set l true, true))
        (lTree, chFalse, false)
      if ch then go n false lTree' nextCh else lTree
  go (8 * bs.length + 8) true (Arr.ofSize nl []) chFalse

/-- Values live across some call of an already `fillLive`-annotated tree: live after the call,
other than its results (the leading `param`s of the continuation remove those). -/
def acrossCalls : Tree → List Nat
  | .call _ _ _ _ k => union k.lv (acrossCalls k)
  | .let_ _ _ _ _ k | .load _ _ _ _ k | .store _ _ _ _ k | .skip _ _ k | .param _ _ k
  | .label _ _ k => acrossCalls k
  | .jnz _ _ _ _ t e => union (acrossCalls t) (acrossCalls e)
  | .block _ _ b rest => union (acrossCalls b) (acrossCalls rest)
  | .jump .. | .ret .. | .exit .. | .stop => []

/-- Labels that lie on some cycle in the block jump graph (loop headers and mutual-loop blocks). -/
def loopBlocksWithSize (nl : Nat) (bs : List (Nat × Tree)) : List Nat :=
  let adj := bs.foldl (fun a (l, b) => a.set l (allJumps b)) (Arr.ofSize nl [])
  let maxFuel := bs.length * bs.length + bs.length + 1
  let canReach (src target : Nat) : Bool :=
    let rec dfs : Nat → List Nat → List Nat → Bool
      | 0, _, _ | _, [], _ => false
      | fuel + 1, x :: xs, vis =>
        if x == target then true
        else if vis.contains x then dfs fuel xs vis
        else dfs fuel (adj.get x ++ xs) (x :: vis)
    dfs maxFuel (adj.get src) []
  (bs.filter fun (l, _) => canReach l l).map (·.1)

end Live
end LeanQbe
