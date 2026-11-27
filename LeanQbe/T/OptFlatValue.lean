module

public import LeanQbe.T.FlatDirect
public import LeanQbe.T.OptFlatPlanKit
public import LeanQbe.T.Fold
public import LeanQbe.T.Copy
public import LeanQbe.T.Canon
public import LeanQbe.T.Gvn

/-!
# Native `Trie`-Env First-Order Mid-End Value Passes (`OptFlatValue`)

Direct `TFlat rs → TFlat rs` implementations of the core PHOAS value passes (`Func.fold`,
`Func.copy`, `Func.canon`, `Func.gvn`) using a de Bruijn level `Trie ((t : Ty) × W t)`
environment and output level counter `outDepth` (`0` = oldest parameter, `outDepth - 1` = newest
bound output):

* `OptFlatValue.foldFlat`: constant folding, algebraic rules, strength reduction, and static
  branch pruning (`Fold.lean`).
* `OptFlatValue.copyFlat`: copy, `mkpair`/`unpair` pair-projection propagation (`Copy.lean`).
* `OptFlatValue.canonFlat`: commutative canonicalization and associative constant chains
  (`Canon.lean`).
* `OptFlatValue.gvnFlat`: lexical-scope CSE / GVN over hash-bucketed `GvnTbl K` (`Gvn.lean`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace OptFlatValue

open OptFlatPlanKit

/-! ## 1. Native `TFlat` Constant Folding & Strength Reduction (`foldFlat`) -/

/-- `SweepKL` specification for `foldFlat`. -/
def foldSweep : SweepKL (FVal K) Unit where
  argOut := Arg.fout
  freshLoad outD _ := FVal.fresh outD outD
  freshTup ts outD := freshFVals ts (Tup.levels ts outD) outD
  onLet _ outD {ts} op :=
    match op.simpAct with
    | some act => .elim (act.apply op.args) ()
    | none =>
      match op.simpProv? with
      | some res => .elim res ()
      | none =>
        .emit1 op.foldRewrite (op.foldWrap outD (Tup.levels ts outD)) () (outD + ts.length)
  onJnz _ c :=
    match c.fout with
    | .imm true => .takeT ()
    | .imm false => .takeF ()
    | .var v => .emit (.var v) () ()

/-- Direct `TFlat` constant folding, algebraic simplification, strength reduction, and static
branch pruning matching `reifyFunc (Func.fold (denoteFunc tf))`. -/
def foldFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  foldSweep.run tf as.length (initEnv FVal.fresh as) as.length ()

/-- `TFlatFn` wrapper for `foldFlat`. -/
def foldFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, foldFlat f.as f.body⟩

/-! ## 2. Native `TFlat` Copy & Pair-Projection Propagation (`copyFlat`) -/

/-- `SweepKL` specification for `copyFlat`. -/
def copySweep : SweepKL (CVal K) Unit where
  argOut := Arg.cout
  freshLoad outD _ := CVal.fresh outD outD
  freshTup ts outD := freshCVals ts (Tup.levels ts outD) outD
  onLet _ outD {ts} op :=
    match op.copyLet outD with
    | .elim res => .elim res ()
    | .emit op' next' wrap => .emit1 op' (wrap (Tup.levels ts outD)) () next'
  onJnz _ c := .emit c.cout () ()

/-- Direct `TFlat` copy and pair-projection propagation matching
`reifyFunc (Func.copy (denoteFunc tf))`. -/
def copyFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  copySweep.run tf as.length (initEnv CVal.fresh as) as.length ()

/-- `TFlatFn` wrapper for `copyFlat`. -/
def copyFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, copyFlat f.as f.body⟩

/-! ## 3. Native `TFlat` Commutative Canonicalization & Constant Chains (`canonFlat`) -/

/-- `SweepKL` specification for `canonFlat`. -/
def canonSweep : SweepKL (CanonVal K) Unit where
  argOut := Arg.cnout
  freshLoad outD _ := CanonVal.fresh outD outD
  freshTup ts outD := freshCanonVals ts (Tup.levels ts outD) outD
  onLet _ outD {ts} op :=
    let step := op.canonLet outD
    .emit1 step.op (step.wrap (Tup.levels ts outD)) () (outD + ts.length)
  onJnz _ c := .emit c.cnout () ()

/-- Direct `TFlat` commutative canonicalization and associative constant-chain reassociation
matching `reifyFunc (Func.canon (denoteFunc tf))`. -/
def canonFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  canonSweep.run tf as.length (initEnv CanonVal.fresh as) as.length ()

/-- `TFlatFn` wrapper for `canonFlat`. -/
def canonFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, canonFlat f.as f.body⟩

/-! ## 4. Native `TFlat` Lexical GVN / CSE (`gvnFlat`) -/

/-- `SweepKL` specification for `gvnFlat`. -/
def gvnSweep : SweepKL (GVal K) (GvnTbl K) where
  argOut := Arg.gout
  freshLoad outD _ := (outD, outD)
  freshTup ts outD := freshGVals ts (Tup.levels ts outD) outD
  onLet tbl outD {ts} op :=
    let kArgs := tupGKey op.args
    match tbl.find op.sig ts op.code kArgs with
    | some cached => .elim cached tbl
    | none =>
      let gs := freshGVals ts (Tup.levels ts outD) outD
      .emit1 ⟨op.code, tupGOut op.args⟩ gs (tbl.insert op.sig ts op.code kArgs gs)
        (outD + ts.length)
  onJnz tbl c := .emit c.gout tbl tbl

/-- Direct `TFlat` lexical GVN/CSE matching `reifyFunc (Func.gvn (denoteFunc tf))`. -/
def gvnFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  gvnSweep.run tf as.length (initEnv (fun x next => (x, next)) as) as.length .empty

/-- `TFlatFn` wrapper for `gvnFlat`. -/
def gvnFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, gvnFlat f.as f.body⟩

end OptFlatValue
end LeanQbe.T
