module

public import LeanQbe.T.FlatDirect
public import LeanQbe.T.OptFlatPlanKit
public import LeanQbe.T.CondThreadOpt

/-!
# Native `Trie`-Env Dominating Path-Condition Optimization (`OptFlatPathCond`)

Direct `TFlat rs → TFlat rs` implementation of `Func.pathCondOpt` using a de Bruijn level
`Trie ((t : Ty) × PVal K t)` environment, dominating path-fact list `facts : List BoolFact`,
and output level counter `depth` (`0` = oldest parameter, `depth - 1` = newest bound output):

* `OptFlatPathCond.pathCondOptFlat`: `TFlat` pass matching `reifyFunc (Func.pathCondOpt ...)`.
* `OptFlatPathCond.pathCondOptFlatFn`: `TFlatFn` wrapper.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace OptFlatPathCond

open OptFlatPlanKit
open CondThreadOpt

/-- `SweepKL` specification for `pathCondOptFlat`. -/
def pathCondSweep : SweepKL (PVal K) (List BoolFact) where
  argOut := pOut
  termArgs facts {_} args := tupPOut (resolveBoolArgs facts args)
  freshLoad depth t := PVal.fresh t depth depth
  freshTup ts depth := freshPVals ts (Tup.levels ts depth) depth
  onLet facts depth {ts} op :=
    match pcStep op facts depth with
    | .elim res => .elim res facts
    | .emit op' wrap => .emit1 op' (wrap (Tup.levels ts depth)) facts (depth + ts.length)
  onJnz facts c :=
    match resolveBool? facts c with
    | some true => .takeT facts
    | some false => .takeF facts
    | none =>
      let info := pInfo c
      .emit (pOut c) (pushFacts info.tf facts) (pushFacts info.ff facts)

/-- Direct `TFlat` dominating path-fact and known-condition optimization matching
`reifyFunc (Func.pathCondOpt (denoteFunc tf))`. -/
def pathCondOptFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  pathCondSweep.run tf as.length
    (initEnv (fun {t} x next => PVal.fresh t x next) as) as.length []

/-- `TFlatFn` wrapper for `pathCondOptFlat`. -/
def pathCondOptFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, pathCondOptFlat f.as f.body⟩

end OptFlatPathCond
end LeanQbe.T
