module

public import LeanQbe.T.Flat
public import LeanQbe.T.OptFlatPlanKit
public import LeanQbe.T.Peel

/-!
# Native `TFlat` Bounded 1-Iteration Loop Peeling (`OptFlatPeel`)

Direct `TFlat rs → TFlat rs` implementation of `Func.peel`, eliminating PHOAS
`denoteFunc`/`reifyFunc` round-trips using level-indexed `Trie` environments and `PeelLFlat`
output-depth closures (`0` shifts, strictly structural recursion on `TFlat`/`TBlocks`):

* `OptFlatPeel.peelMetricsFlat`: AST size and target/subst jump counter matching `Peel.peelMetrics`.
* `OptFlatPeel.peelAuxFlat`: depth-indexed 1-iteration loop peeling worker matching `Peel.peelAux`.
* `OptFlatPeel.peelFlat`: closed-function entry point matching `reifyFunc (Func.peel ...)`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace OptFlatPeel

open OptFlatPlanKit
open Peel

/-- Output-level-based `TFlat` label payload mirroring `Peel.PeelL K KL rs`. -/
inductive PeelLFlat (rs : List Ty) : List Ty → Type
  | outer {ts : List Ty} (outLbl : Nat) : PeelLFlat rs ts
  | subst {ts : List Ty} (id : Nat) (k : Nat → Nat → Tup (Arg K) ts → TFlat rs) :
      PeelLFlat rs ts
  | probe {ts : List Ty} (id : Nat) : PeelLFlat rs ts

/-- Wrap output label levels `Tup KL sig` into `PeelLFlat.outer`. -/
def toOuterTupFlat {rs : List Ty} :
    {sig : List (List Ty)} → Tup KL sig → Tup (PeelLFlat rs) sig
  | [], () => ()
  | _ :: _, (j, js) => (.outer j, toOuterTupFlat js)

/-- Construct a tuple of fresh `.probe` labels starting at `nextId`. -/
def probeTupFlat {rs : List Ty} :
    (sig : List (List Ty)) → Nat → Tup (PeelLFlat rs) sig
  | [], _ => ()
  | _ :: sig, id => (.probe id, probeTupFlat sig (id + 1))

mutual
/-- Compute AST node size and jump counts to `targetId` and `.subst` labels directly on `TFlat`. -/
def peelMetricsFlat {rs : List Ty} (targetId nextId : Nat)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × PeelLFlat rs ts)) : TFlat rs → Metrics
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    let m := peelMetricsFlat targetId nextId inLD inLE k
    ⟨1 + m.size, m.targetJumps, m.substJumps⟩
  | .jnz _ t e =>
    let mt := peelMetricsFlat targetId nextId inLD inLE t
    let me := peelMetricsFlat targetId nextId inLD inLE e
    ⟨1 + mt.size + me.size, mt.targetJumps + me.targetJumps, mt.substJumps + me.substJumps⟩
  | .jump (ts := ts) j _ =>
    match resolveLabel inLD inLE ts j with
    | some (.outer _) => ⟨1, 0, 0⟩
    | some (.subst _ _) => ⟨1, 0, 1⟩
    | some (.probe id) => ⟨1, if id == targetId then 1 else 0, 0⟩
    | none => ⟨1, 0, 0⟩
  | .ret _ | .exit _ _ | .hlt => ⟨1, 0, 0⟩
  | .group (sig := sig) bodies k =>
    let ps := probeTupFlat (rs := rs) sig nextId
    let nextId' := nextId + sig.length
    let inLD' := inLD + sig.length
    let inLE' := insertTupEnv inLD inLE ps
    let mb := peelMetricsBFlat targetId nextId' inLD' inLE' bodies
    let mk := peelMetricsFlat targetId nextId' inLD' inLE' k
    ⟨1 + mb.size + mk.size, mb.targetJumps + mk.targetJumps, mb.substJumps + mk.substJumps⟩

/-- Block-list companion of `peelMetricsFlat`. -/
def peelMetricsBFlat {rs : List Ty} (targetId nextId : Nat)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × PeelLFlat rs ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Metrics
  | _, .nil => ⟨0, 0, 0⟩
  | _, .cons b bs =>
    let m := peelMetricsFlat targetId nextId inLD inLE b
    m.add (peelMetricsBFlat targetId nextId inLD inLE bs)
end

/-- Compute `peelMetricsFlat` for the single block of a `[ts]` `TBlocks`. -/
def loopBlockMetricsFlat {rs ts : List Ty} (inLD : Nat)
    (inLE : Trie ((ts : List Ty) × PeelLFlat rs ts)) (bs : TBlocks rs [ts]) : Metrics :=
  match bs with
  | .cons b _ => peelMetricsFlat 0 1 inLD inLE b

mutual
/-- Internal depth-indexed 1-iteration loop peeling worker on `TFlat`, structurally recursive on
`TFlat`. -/
def peelAuxFlat {rs : List Ty} (budget depth : Nat) :
    TFlat rs → Nat → Trie ((t : Ty) × Arg K t) →
    Nat → Trie ((ts : List Ty) × PeelLFlat rs ts) →
    Nat → Nat → TFlat rs
  | .let_ (ts := ts) op k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let args' := flattenArgs (resolveEnvArgs inVD inVE op.args)
    .let_ ⟨op.code, idxArgs outVD args'⟩
      (peelAuxFlat budget depth k (inVD + ts.length)
        (insertFreshWith (fun _ _ od => .var od) inVD outVD ts inVE)
        inLD inLE (outVD + ts.length) outLD)
  | .load t a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let a' := flattenArg (resolveEnvArg inVD inVE a)
    .load t (idxArg outVD a')
      (peelAuxFlat budget depth k (inVD + 1) (inVE.insert inVD ⟨t, .var outVD⟩)
        inLD inLE (outVD + 1) outLD)
  | .store v a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let v' := flattenArg (resolveEnvArg inVD inVE v)
    let a' := flattenArg (resolveEnvArg inVD inVE a)
    .store (idxArg outVD v') (idxArg outVD a')
      (peelAuxFlat budget depth k inVD inVE inLD inLE outVD outLD)
  | .call f bs args k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let args' := flattenArgs (resolveEnvArgs inVD inVE args)
    .call f bs (idxArgs outVD args')
      (peelAuxFlat budget depth k (inVD + bs.length)
        (insertFreshWith (fun _ _ od => .var od) inVD outVD bs inVE)
        inLD inLE (outVD + bs.length) outLD)
  | .jnz c t e, inVD, inVE, inLD, inLE, outVD, outLD =>
    let c' := flattenArg (resolveEnvArg inVD inVE c)
    .jnz (idxArg outVD c')
      (peelAuxFlat budget depth t inVD inVE inLD inLE outVD outLD)
      (peelAuxFlat budget depth e inVD inVE inLD inLE outVD outLD)
  | .jump (ts := ts) j args, inVD, inVE, inLD, inLE, outVD, outLD =>
    let args' := flattenArgs (resolveEnvArgs inVD inVE args)
    match resolveLabel inLD inLE ts j with
    | some (.outer outLbl) => .jump (idxLabel outLD outLbl) (idxArgs outVD args')
    | some (.subst _ k) => k outVD outLD args'
    | some (.probe _) => .hlt
    | none => .hlt
  | .ret vs, inVD, inVE, _, _, outVD, _ =>
    .ret (idxArgs outVD (flattenArgs (resolveEnvArgs inVD inVE vs)))
  | .exit f args, inVD, inVE, _, _, outVD, _ =>
    .exit f (idxArgs outVD (flattenArgs (resolveEnvArgs inVD inVE args)))
  | .hlt, _, _, _, _, _, _ => .hlt
  | .group (sig := sig) bodies entry, inVD, inVE, inLD, inLE, outVD, outLD =>
    match sig with
    | [ts] =>
      match bodies with
      | .cons b .nil =>
        let inLD' := inLD + 1
        let inLEProbe := inLE.insert inLD ⟨ts, .probe 0⟩
        let mb := peelMetricsFlat 0 1 inLD' inLEProbe b
        let me := peelMetricsFlat 0 1 inLD' inLEProbe entry
        if canPeel budget mb me then
          let remBudget := (budget - mb.size) / 2
          let remIter2 : Nat → Nat → Tup (Arg K) ts → TFlat rs := fun ovd2 old2 backArgs =>
            let remBodies := peelBAuxFlat remBudget (depth + 1) (TBlocks.cons (ts := ts) b .nil)
              inVD inVE inLD' (inLE.insert inLD ⟨ts, .outer old2⟩) ovd2 (old2 + 1)
            .group (sig := [ts]) remBodies (.jump 0 (idxArgs ovd2 backArgs))
          let iter1 : Nat → Nat → Tup (Arg K) ts → TFlat rs := fun ovd1 old1 args1 =>
            peelAuxFlat remBudget (depth + 1) b
              (inVD + ts.length) (insertTupEnv inVD inVE args1)
              inLD' (inLE.insert inLD ⟨ts, .subst (2 * depth) remIter2⟩) ovd1 old1
          peelAuxFlat budget (depth + 1) entry
            inVD inVE inLD' (inLE.insert inLD ⟨ts, .subst (2 * depth + 1) iter1⟩) outVD outLD
        else
          let inLE' := insertTupEnv inLD inLE (toOuterTupFlat (Tup.levels [ts] outLD))
          let outLD' := outLD + 1
          .group (sig := [ts])
            (peelBAuxFlat budget depth (TBlocks.cons (ts := ts) b .nil)
              inVD inVE inLD' inLE' outVD outLD')
            (peelAuxFlat budget depth entry inVD inVE inLD' inLE' outVD outLD')
    | _ =>
      let inLD' := inLD + sig.length
      let inLE' := insertTupEnv inLD inLE (toOuterTupFlat (Tup.levels sig outLD))
      let outLD' := outLD + sig.length
      .group
        (peelBAuxFlat budget depth bodies inVD inVE inLD' inLE' outVD outLD')
        (peelAuxFlat budget depth entry inVD inVE inLD' inLE' outVD outLD')

/-- Block-list companion of `peelAuxFlat`. -/
def peelBAuxFlat {rs : List Ty} (budget depth : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig →
    Nat → Trie ((t : Ty) × Arg K t) →
    Nat → Trie ((ts : List Ty) × PeelLFlat rs ts) →
    Nat → Nat → TBlocks rs sig
  | _, .nil, _, _, _, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inVD, inVE, inLD, inLE, outVD, outLD =>
    .cons
      (peelAuxFlat budget depth b (inVD + ts.length)
        (insertFreshWith (fun _ _ od => .var od) inVD outVD ts inVE)
        inLD inLE (outVD + ts.length) outLD)
      (peelBAuxFlat budget depth bs inVD inVE inLD inLE outVD outLD)
end

/-- Direct `TFlat` 1-iteration loop peeling matching `reifyFunc (Func.peel (denoteFunc tf) budget)`. -/
def peelFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) (budget : Nat := 40) : TFlat rs :=
  peelAuxFlat budget 0 tf as.length (initEnv (fun x _ => .var x) as) 0 .empty as.length 0

/-- `TFlatFn` wrapper for `peelFlat`. -/
def peelFlatFn (f : TFlatFn) (budget : Nat := 40) : TFlatFn :=
  ⟨f.name, f.as, f.rs, peelFlat f.as f.body budget⟩

end OptFlatPeel
end LeanQbe.T
