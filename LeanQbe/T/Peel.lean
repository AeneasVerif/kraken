module

public import LeanQbe.T.OptUtil

/-!
# Bounded 1-Iteration Loop Peeling (`O-M2`)

Pure Style-A PHOAS-to-PHOAS 1-iteration loop peeling pass for single-block join-point loops
`.group (sig := [ts]) bodies entry` (which includes `loop1`):

* Uses `V := Arg V` (avoiding redundant `.copy` bindings on immediate initial arguments) and a
  label-substitution wrapper `Peel.PeelL V L rs` with `.outer`, `.subst`, and `.probe`.
* Guards peeling with a code-growth budget (`size ≤ budget`, default `maxLoopSize := 40`) and
  single-entry / single-back-jump site checks (`entryJumps == 1`, `backJumps == 1`, no nested
  `.subst` duplication) so code growth stays strictly `≤ 1x` per loop and `≤ maxLoopSize` across
  nested loops (`remBudget := (budget - size) / 2`).
* Unrolls the first iteration at `entry`'s jump to the loop block while placing the remaining
  `.group` at the first iteration's back-jump, so pure expressions and loads in iteration 1
  lexically dominate iterations `≥ 2` for downstream `Func.gvn` / `Func.memLoad` LICM synergy.

Correctness (`LeanQbe/T/PeelLemmas.lean`): `peel_wp`, `peel_wf`, `Func.peel_wf`, `Func.peel_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace Peel

/-- Construct a tuple of default immediate operands for metrics inspection. -/
def immDefaults (V : Ty → Type) : (ts : List Ty) → Tup (Arg V) ts
  | [] => ()
  | t :: ts => (.imm (@default (Val t) (Val.inhabited t)), immDefaults V ts)

/-- Label representation used during PHOAS peeling: outer target labels, substituted continuation
labels (tagged by unique `id : Nat`), or probe labels (for structural jump/size counting). -/
inductive PeelL (V : Ty → Type) (L : List Ty → Type) (rs : List Ty) : List Ty → Type
  | outer {ts : List Ty} (j : L ts) : PeelL V L rs ts
  | subst {ts : List Ty} (id : Nat) (k : Tup (Arg V) ts → Expr V L rs) : PeelL V L rs ts
  | probe {ts : List Ty} (id : Nat) : PeelL V L rs ts

/-- Wrap a tuple of target labels `Tup L sig` into `PeelL.outer`. -/
def toOuterTup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Tup L sig → Tup (PeelL V L rs) sig
  | [], () => ()
  | _ :: _, (j, js) => (.outer j, toOuterTup js)

/-- Construct a tuple of fresh probe labels starting at `nextId`. -/
def probeTup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (sig : List (List Ty)) → Nat → Tup (PeelL V L rs) sig
  | [], _ => ()
  | _ :: sig, id => (.probe id, probeTup sig (id + 1))

/-- Structural metrics collected by `peelMetrics`: AST node count, jumps to `targetId`, and jumps
to `.subst` continuations. -/
structure Metrics where
  size : Nat
  targetJumps : Nat
  substJumps : Nat
  deriving DecidableEq, Repr

/-- Componentwise addition of `Metrics`. -/
def Metrics.add (a b : Metrics) : Metrics :=
  ⟨a.size + b.size, a.targetJumps + b.targetJumps, a.substJumps + b.substJumps⟩

mutual
/-- Compute AST node size and jump counts to `targetId` and `.subst` labels. -/
def peelMetrics {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (targetId nextId : Nat) : Expr (Arg V) (PeelL V L rs) rs → Metrics
  | .let_ (ts := ts) _ k =>
    let m := peelMetrics targetId nextId (k (immDefaults V ts))
    ⟨1 + m.size, m.targetJumps, m.substJumps⟩
  | .load t _ k =>
    let m := peelMetrics targetId nextId (k (.imm (@default (Val t) (Val.inhabited t))))
    ⟨1 + m.size, m.targetJumps, m.substJumps⟩
  | .store _ _ k =>
    let m := peelMetrics targetId nextId k
    ⟨1 + m.size, m.targetJumps, m.substJumps⟩
  | .call _ (bs := bs) _ k =>
    let m := peelMetrics targetId nextId (k (immDefaults V bs))
    ⟨1 + m.size, m.targetJumps, m.substJumps⟩
  | .jnz _ t e =>
    let mt := peelMetrics targetId nextId t
    let me := peelMetrics targetId nextId e
    ⟨1 + mt.size + me.size, mt.targetJumps + me.targetJumps, mt.substJumps + me.substJumps⟩
  | .jump j _ =>
    match j with
    | .outer _ => ⟨1, 0, 0⟩
    | .subst _ _ => ⟨1, 0, 1⟩
    | .probe id => ⟨1, if id == targetId then 1 else 0, 0⟩
  | .ret _ | .exit _ _ | .hlt => ⟨1, 0, 0⟩
  | .group (sig := sig) bodies k =>
    let ps := probeTup sig nextId
    let nextId' := nextId + sig.length
    let mb := peelMetricsB targetId nextId' (bodies ps)
    let mk := peelMetrics targetId nextId' (k ps)
    ⟨1 + mb.size + mk.size, mb.targetJumps + mk.targetJumps, mb.substJumps + mk.substJumps⟩

/-- Block-list companion of `peelMetrics`. -/
def peelMetricsB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (targetId nextId : Nat) :
    {sig : List (List Ty)} → Blocks (Arg V) (PeelL V L rs) rs sig → Metrics
  | _, .nil => ⟨0, 0, 0⟩
  | _, .cons (ts := ts) b bs =>
    let m := peelMetrics targetId nextId (b (immDefaults V ts))
    m.add (peelMetricsB targetId nextId bs)
end

/-- Compute `peelMetrics` for the single block of a `[ts]` `Blocks`. -/
def loopBlockMetrics {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty}
    (bs : Blocks (Arg V) (PeelL V L rs) rs [ts]) : Metrics :=
  match bs with
  | .cons b _ => peelMetrics 0 1 (b (immDefaults V ts))

/-- Peel decision predicate for a single-block group: checks code-growth budget (`size ≤ budget`),
single back-jump (`targetJumps == 1`), no outer `.subst` duplication (`substJumps == 0`), and
single entry jump (`entryJumps == 1`). -/
def canPeel (budget : Nat) (mb me : Metrics) : Bool :=
  Nat.ble mb.size budget && mb.targetJumps == 1 && mb.substJumps == 0 && me.targetJumps == 1

mutual
/-- Internal depth-indexed 1-iteration loop peeling worker. -/
def peelAux (budget depth : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (Arg V) (PeelL V L rs) rs → Expr V L rs
  | .let_ op k =>
    .let_ (flattenOp op) fun xs => peelAux budget depth (k (toArgTup xs))
  | .load t a k =>
    .load t (flattenArg a) fun v => peelAux budget depth (k (.var v))
  | .store v a k =>
    .store (flattenArg v) (flattenArg a) (peelAux budget depth k)
  | .call f args k =>
    .call f (flattenArgs args) fun xs => peelAux budget depth (k (toArgTup xs))
  | .jnz c t e =>
    .jnz (flattenArg c) (peelAux budget depth t) (peelAux budget depth e)
  | .jump j args =>
    match j with
    | .outer l => .jump l (flattenArgs args)
    | .subst _ k => k (flattenArgs args)
    | .probe _ => .hlt
  | .ret vs => .ret (flattenArgs vs)
  | .exit f args => .exit f (flattenArgs args)
  | .hlt => .hlt
  | .group (sig := sig) bodies entry =>
    match sig, bodies, entry with
    | [ts], bodies, entry =>
      let mb := loopBlockMetrics (bodies (.probe 0, ()))
      let me := peelMetrics 0 1 (entry (.probe 0, ()))
      if canPeel budget mb me then
        let remBudget := (budget - mb.size) / 2
        let remBodies : Tup L [ts] → Blocks V L rs [ts] :=
          fun Js => peelBAux remBudget (depth + 1) (bodies (toOuterTup Js))
        let remIter2 : Tup (Arg V) ts → Expr V L rs := fun backArgs =>
          .group (sig := [ts]) remBodies (fun Js => .jump Js.1 backArgs)
        let iter1 : Tup (Arg V) ts → Expr V L rs :=
          (peelArgBAux remBudget (depth + 1) (bodies (.subst (2 * depth) remIter2, ()))).1
        peelAux budget (depth + 1) (entry (.subst (2 * depth + 1) iter1, ()))
      else
        .group (sig := [ts])
          (fun Js => peelBAux budget depth (bodies (toOuterTup Js)))
          (fun Js => peelAux budget depth (entry (toOuterTup Js)))
    | _, bodies, entry =>
      .group
        (fun Js => peelBAux budget depth (bodies (toOuterTup Js)))
        (fun Js => peelAux budget depth (entry (toOuterTup Js)))

/-- Peel every block in `Blocks`, returning continuations taking `Tup (Arg V) ts`. -/
def peelArgBAux (budget depth : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} →
    Blocks (Arg V) (PeelL V L rs) rs sig →
    Tup (fun ts => Tup (Arg V) ts → Expr V L rs) sig
  | _, .nil => ()
  | _, .cons b bs =>
    (fun args => peelAux budget depth (b args), peelArgBAux budget depth bs)

/-- Block-list companion of `peelAux`. -/
def peelBAux (budget depth : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} →
    Blocks (Arg V) (PeelL V L rs) rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons b bs =>
    .cons (fun xs => peelAux budget depth (b (toArgTup xs))) (peelBAux budget depth bs)
end

end Peel

/-- Structural 1-iteration loop peeling over `Expr (Arg V) (Peel.PeelL V L rs) rs` with code
growth budget `budget`. -/
def peel (budget : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (Arg V) (Peel.PeelL V L rs) rs → Expr V L rs :=
  Peel.peelAux budget 0

/-- Block-list companion of `peel`. -/
def peelB (budget : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {sig : List (List Ty)} :
    Blocks (Arg V) (Peel.PeelL V L rs) rs sig → Blocks V L rs sig :=
  Peel.peelBAux budget 0

/-- Peel 1 iteration of eligible single-block loops in a closed function `Func`, bounded by
`maxLoopSize` (default `40`). -/
def Func.peel {as rs : List Ty} (f : Func as rs) (maxLoopSize : Nat := 40) : Func as rs :=
  fun V L xs => LeanQbe.T.peel maxLoopSize (f (Arg V) (Peel.PeelL V L rs) (toArgTup xs))

/-- Peel 1 iteration of eligible single-block loops in a named function `Fn`, keeping `name`,
`as`, and `rs`. -/
def Fn.peel (fn : Fn) (maxLoopSize : Nat := 40) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.peel fn.body maxLoopSize⟩

end LeanQbe.T
