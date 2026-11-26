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

mutual
/-- Recursive `TFlat` mirror of `LeanQbe.T.fold`. -/
def foldFlatAux {rs : List Ty} :
    TFlat rs → Nat → Trie ((t : Ty) × FVal K t) → Nat → TFlat rs
  | .let_ (ts := ts) op k, inDepth, inEnv, outDepth =>
    let fOp : Op (FVal K) ts := ⟨op.code, resolveEnvArgs inDepth inEnv op.args⟩
    match fOp.simpAct with
    | some act =>
      foldFlatAux k (inDepth + ts.length) (insertTupEnv inDepth inEnv (act.apply fOp.args)) outDepth
    | none =>
      match fOp.simpProv? with
      | some res =>
        foldFlatAux k (inDepth + ts.length) (insertTupEnv inDepth inEnv res) outDepth
      | none =>
        let op' := fOp.foldRewrite
        let wrapped := fOp.foldWrap outDepth (Tup.levels ts outDepth)
        .let_ ⟨op'.code, idxArgs outDepth op'.args⟩
          (foldFlatAux k (inDepth + ts.length) (insertTupEnv inDepth inEnv wrapped)
            (outDepth + ts.length))
  | .load t a k, inDepth, inEnv, outDepth =>
    let a' := (resolveEnvArg inDepth inEnv a).fout
    let inEnv' := inEnv.insert inDepth ⟨t, FVal.fresh outDepth outDepth⟩
    .load t (idxArg outDepth a') (foldFlatAux k (inDepth + 1) inEnv' (outDepth + 1))
  | .store v a k, inDepth, inEnv, outDepth =>
    let v' := (resolveEnvArg inDepth inEnv v).fout
    let a' := (resolveEnvArg inDepth inEnv a).fout
    .store (idxArg outDepth v') (idxArg outDepth a') (foldFlatAux k inDepth inEnv outDepth)
  | .call f bs args k, inDepth, inEnv, outDepth =>
    let args' := tupMapArg (fun _ => Arg.fout) (resolveEnvArgs inDepth inEnv args)
    let wrapped := freshFVals bs (Tup.levels bs outDepth) outDepth
    .call f bs (idxArgs outDepth args')
      (foldFlatAux k (inDepth + bs.length) (insertTupEnv inDepth inEnv wrapped)
        (outDepth + bs.length))
  | .jnz c t e, inDepth, inEnv, outDepth =>
    match (resolveEnvArg inDepth inEnv c).fout with
    | .imm true => foldFlatAux t inDepth inEnv outDepth
    | .imm false => foldFlatAux e inDepth inEnv outDepth
    | .var v =>
      .jnz (idxArg outDepth (.var v))
        (foldFlatAux t inDepth inEnv outDepth)
        (foldFlatAux e inDepth inEnv outDepth)
  | .jump j args, inDepth, inEnv, outDepth =>
    let args' := tupMapArg (fun _ => Arg.fout) (resolveEnvArgs inDepth inEnv args)
    .jump j (idxArgs outDepth args')
  | .ret vs, inDepth, inEnv, outDepth =>
    let vs' := tupMapArg (fun _ => Arg.fout) (resolveEnvArgs inDepth inEnv vs)
    .ret (idxArgs outDepth vs')
  | .exit f args, inDepth, inEnv, outDepth =>
    let args' := tupMapArg (fun _ => Arg.fout) (resolveEnvArgs inDepth inEnv args)
    .exit f (idxArgs outDepth args')
  | .hlt, _, _, _ => .hlt
  | .group bodies k, inDepth, inEnv, outDepth =>
    .group (foldFlatAuxB bodies inDepth inEnv outDepth) (foldFlatAux k inDepth inEnv outDepth)

/-- Block-list companion of `foldFlatAux`. -/
def foldFlatAuxB {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × FVal K t) → Nat →
    TBlocks rs sig
  | _, .nil, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inDepth, inEnv, outDepth =>
    let wrapped := freshFVals ts (Tup.levels ts outDepth) outDepth
    .cons
      (foldFlatAux b (inDepth + ts.length) (insertTupEnv inDepth inEnv wrapped)
        (outDepth + ts.length))
      (foldFlatAuxB bs inDepth inEnv outDepth)
end

/-- Direct `TFlat` constant folding, algebraic simplification, strength reduction, and static
branch pruning matching `reifyFunc (Func.fold (denoteFunc tf))`. -/
def foldFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  foldFlatAux tf as.length (initEnv FVal.fresh as) as.length

/-- `TFlatFn` wrapper for `foldFlat`. -/
def foldFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, foldFlat f.as f.body⟩

/-! ## 2. Native `TFlat` Copy & Pair-Projection Propagation (`copyFlat`) -/

mutual
/-- Recursive `TFlat` mirror of `LeanQbe.T.copy`. -/
def copyFlatAux {rs : List Ty} :
    TFlat rs → Nat → Trie ((t : Ty) × CVal K t) → Nat → TFlat rs
  | .let_ (ts := ts) op k, inDepth, inEnv, outDepth =>
    let cOp : Op (CVal K) ts := ⟨op.code, resolveEnvArgs inDepth inEnv op.args⟩
    match cOp.copyLet outDepth with
    | .elim res =>
      copyFlatAux k (inDepth + ts.length) (insertTupEnv inDepth inEnv res) outDepth
    | .emit op' next' wrap =>
      let wrapped := wrap (Tup.levels ts outDepth)
      .let_ ⟨op'.code, idxArgs outDepth op'.args⟩
        (copyFlatAux k (inDepth + ts.length) (insertTupEnv inDepth inEnv wrapped) next')
  | .load t a k, inDepth, inEnv, outDepth =>
    let a' := (resolveEnvArg inDepth inEnv a).cout
    let inEnv' := inEnv.insert inDepth ⟨t, CVal.fresh outDepth outDepth⟩
    .load t (idxArg outDepth a') (copyFlatAux k (inDepth + 1) inEnv' (outDepth + 1))
  | .store v a k, inDepth, inEnv, outDepth =>
    let v' := (resolveEnvArg inDepth inEnv v).cout
    let a' := (resolveEnvArg inDepth inEnv a).cout
    .store (idxArg outDepth v') (idxArg outDepth a') (copyFlatAux k inDepth inEnv outDepth)
  | .call f bs args k, inDepth, inEnv, outDepth =>
    let args' := tupCOut (resolveEnvArgs inDepth inEnv args)
    let wrapped := freshCVals bs (Tup.levels bs outDepth) outDepth
    .call f bs (idxArgs outDepth args')
      (copyFlatAux k (inDepth + bs.length) (insertTupEnv inDepth inEnv wrapped)
        (outDepth + bs.length))
  | .jnz c t e, inDepth, inEnv, outDepth =>
    let c' := (resolveEnvArg inDepth inEnv c).cout
    .jnz (idxArg outDepth c')
      (copyFlatAux t inDepth inEnv outDepth)
      (copyFlatAux e inDepth inEnv outDepth)
  | .jump j args, inDepth, inEnv, outDepth =>
    .jump j (idxArgs outDepth (tupCOut (resolveEnvArgs inDepth inEnv args)))
  | .ret vs, inDepth, inEnv, outDepth =>
    .ret (idxArgs outDepth (tupCOut (resolveEnvArgs inDepth inEnv vs)))
  | .exit f args, inDepth, inEnv, outDepth =>
    .exit f (idxArgs outDepth (tupCOut (resolveEnvArgs inDepth inEnv args)))
  | .hlt, _, _, _ => .hlt
  | .group bodies k, inDepth, inEnv, outDepth =>
    .group (copyFlatAuxB bodies inDepth inEnv outDepth) (copyFlatAux k inDepth inEnv outDepth)

/-- Block-list companion of `copyFlatAux`. -/
def copyFlatAuxB {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × CVal K t) → Nat →
    TBlocks rs sig
  | _, .nil, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inDepth, inEnv, outDepth =>
    let wrapped := freshCVals ts (Tup.levels ts outDepth) outDepth
    .cons
      (copyFlatAux b (inDepth + ts.length) (insertTupEnv inDepth inEnv wrapped)
        (outDepth + ts.length))
      (copyFlatAuxB bs inDepth inEnv outDepth)
end

/-- Direct `TFlat` copy and pair-projection propagation matching
`reifyFunc (Func.copy (denoteFunc tf))`. -/
def copyFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  copyFlatAux tf as.length (initEnv CVal.fresh as) as.length

/-- `TFlatFn` wrapper for `copyFlat`. -/
def copyFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, copyFlat f.as f.body⟩

/-! ## 3. Native `TFlat` Commutative Canonicalization & Constant Chains (`canonFlat`) -/

mutual
/-- Recursive `TFlat` mirror of `LeanQbe.T.canon`. -/
def canonFlatAux {rs : List Ty} :
    TFlat rs → Nat → Trie ((t : Ty) × CanonVal K t) → Nat → TFlat rs
  | .let_ (ts := ts) op k, inDepth, inEnv, outDepth =>
    let cnOp : Op (CanonVal K) ts := ⟨op.code, resolveEnvArgs inDepth inEnv op.args⟩
    let step := cnOp.canonLet outDepth
    let wrapped := step.wrap (Tup.levels ts outDepth)
    .let_ ⟨step.op.code, idxArgs outDepth step.op.args⟩
      (canonFlatAux k (inDepth + ts.length) (insertTupEnv inDepth inEnv wrapped)
        (outDepth + ts.length))
  | .load t a k, inDepth, inEnv, outDepth =>
    let a' := (resolveEnvArg inDepth inEnv a).cnout
    let inEnv' := inEnv.insert inDepth ⟨t, CanonVal.fresh outDepth outDepth⟩
    .load t (idxArg outDepth a') (canonFlatAux k (inDepth + 1) inEnv' (outDepth + 1))
  | .store v a k, inDepth, inEnv, outDepth =>
    let v' := (resolveEnvArg inDepth inEnv v).cnout
    let a' := (resolveEnvArg inDepth inEnv a).cnout
    .store (idxArg outDepth v') (idxArg outDepth a') (canonFlatAux k inDepth inEnv outDepth)
  | .call f bs args k, inDepth, inEnv, outDepth =>
    let args' := tupCnOut (resolveEnvArgs inDepth inEnv args)
    let wrapped := freshCanonVals bs (Tup.levels bs outDepth) outDepth
    .call f bs (idxArgs outDepth args')
      (canonFlatAux k (inDepth + bs.length) (insertTupEnv inDepth inEnv wrapped)
        (outDepth + bs.length))
  | .jnz c t e, inDepth, inEnv, outDepth =>
    let c' := (resolveEnvArg inDepth inEnv c).cnout
    .jnz (idxArg outDepth c')
      (canonFlatAux t inDepth inEnv outDepth)
      (canonFlatAux e inDepth inEnv outDepth)
  | .jump j args, inDepth, inEnv, outDepth =>
    .jump j (idxArgs outDepth (tupCnOut (resolveEnvArgs inDepth inEnv args)))
  | .ret vs, inDepth, inEnv, outDepth =>
    .ret (idxArgs outDepth (tupCnOut (resolveEnvArgs inDepth inEnv vs)))
  | .exit f args, inDepth, inEnv, outDepth =>
    .exit f (idxArgs outDepth (tupCnOut (resolveEnvArgs inDepth inEnv args)))
  | .hlt, _, _, _ => .hlt
  | .group bodies k, inDepth, inEnv, outDepth =>
    .group (canonFlatAuxB bodies inDepth inEnv outDepth) (canonFlatAux k inDepth inEnv outDepth)

/-- Block-list companion of `canonFlatAux`. -/
def canonFlatAuxB {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × CanonVal K t) → Nat →
    TBlocks rs sig
  | _, .nil, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inDepth, inEnv, outDepth =>
    let wrapped := freshCanonVals ts (Tup.levels ts outDepth) outDepth
    .cons
      (canonFlatAux b (inDepth + ts.length) (insertTupEnv inDepth inEnv wrapped)
        (outDepth + ts.length))
      (canonFlatAuxB bs inDepth inEnv outDepth)
end

/-- Direct `TFlat` commutative canonicalization and associative constant-chain reassociation
matching `reifyFunc (Func.canon (denoteFunc tf))`. -/
def canonFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  canonFlatAux tf as.length (initEnv CanonVal.fresh as) as.length

/-- `TFlatFn` wrapper for `canonFlat`. -/
def canonFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, canonFlat f.as f.body⟩

/-! ## 4. Native `TFlat` Lexical GVN / CSE (`gvnFlat`) -/

mutual
/-- Recursive `TFlat` mirror of `LeanQbe.T.gvn`. -/
def gvnFlatAux {rs : List Ty} :
    TFlat rs → Nat → Trie ((t : Ty) × GVal K t) → Nat → GvnTbl K → TFlat rs
  | .let_ (ts := ts) op k, inDepth, inEnv, outDepth, tbl =>
    let gArgs := resolveEnvArgs inDepth inEnv op.args
    let kArgs := tupGKey gArgs
    match tbl.find op.sig ts op.code kArgs with
    | some cached =>
      gvnFlatAux k (inDepth + ts.length) (insertTupEnv inDepth inEnv cached) outDepth tbl
    | none =>
      let outArgs := idxArgs outDepth (tupGOut gArgs)
      let gs := freshGVals ts (Tup.levels ts outDepth) outDepth
      .let_ ⟨op.code, outArgs⟩
        (gvnFlatAux k (inDepth + ts.length) (insertTupEnv inDepth inEnv gs)
          (outDepth + ts.length) (tbl.insert op.sig ts op.code kArgs gs))
  | .load t a k, inDepth, inEnv, outDepth, tbl =>
    let a' := (resolveEnvArg inDepth inEnv a).gout
    let inEnv' := inEnv.insert inDepth ⟨t, (outDepth, outDepth)⟩
    .load t (idxArg outDepth a') (gvnFlatAux k (inDepth + 1) inEnv' (outDepth + 1) tbl)
  | .store v a k, inDepth, inEnv, outDepth, tbl =>
    let v' := (resolveEnvArg inDepth inEnv v).gout
    let a' := (resolveEnvArg inDepth inEnv a).gout
    .store (idxArg outDepth v') (idxArg outDepth a') (gvnFlatAux k inDepth inEnv outDepth tbl)
  | .call f bs args k, inDepth, inEnv, outDepth, tbl =>
    let args' := tupGOut (resolveEnvArgs inDepth inEnv args)
    let gs := freshGVals bs (Tup.levels bs outDepth) outDepth
    .call f bs (idxArgs outDepth args')
      (gvnFlatAux k (inDepth + bs.length) (insertTupEnv inDepth inEnv gs)
        (outDepth + bs.length) tbl)
  | .jnz c t e, inDepth, inEnv, outDepth, tbl =>
    let c' := (resolveEnvArg inDepth inEnv c).gout
    .jnz (idxArg outDepth c')
      (gvnFlatAux t inDepth inEnv outDepth tbl)
      (gvnFlatAux e inDepth inEnv outDepth tbl)
  | .jump j args, inDepth, inEnv, outDepth, _ =>
    .jump j (idxArgs outDepth (tupGOut (resolveEnvArgs inDepth inEnv args)))
  | .ret vs, inDepth, inEnv, outDepth, _ =>
    .ret (idxArgs outDepth (tupGOut (resolveEnvArgs inDepth inEnv vs)))
  | .exit f args, inDepth, inEnv, outDepth, _ =>
    .exit f (idxArgs outDepth (tupGOut (resolveEnvArgs inDepth inEnv args)))
  | .hlt, _, _, _, _ => .hlt
  | .group bodies k, inDepth, inEnv, outDepth, tbl =>
    .group (gvnFlatAuxB bodies inDepth inEnv outDepth tbl)
      (gvnFlatAux k inDepth inEnv outDepth tbl)

/-- Block-list companion of `gvnFlatAux`. -/
def gvnFlatAuxB {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × GVal K t) → Nat →
    GvnTbl K → TBlocks rs sig
  | _, .nil, _, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inDepth, inEnv, outDepth, tbl =>
    let gs := freshGVals ts (Tup.levels ts outDepth) outDepth
    .cons
      (gvnFlatAux b (inDepth + ts.length) (insertTupEnv inDepth inEnv gs)
        (outDepth + ts.length) tbl)
      (gvnFlatAuxB bs inDepth inEnv outDepth tbl)
end

/-- Direct `TFlat` lexical GVN/CSE matching `reifyFunc (Func.gvn (denoteFunc tf))`. -/
def gvnFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  gvnFlatAux tf as.length (initEnv (fun x next => (x, next)) as) as.length .empty

/-- `TFlatFn` wrapper for `gvnFlat`. -/
def gvnFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, gvnFlat f.as f.body⟩

end OptFlatValue
end LeanQbe.T
