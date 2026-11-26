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

mutual
/-- Native `TFlat` recursive sweep matching `CondThreadOpt.pathCondOpt`. -/
def pathCondOptFlatAux {rs : List Ty} (facts : List BoolFact) :
    TFlat rs → Nat → Trie ((t : Ty) × PVal K t) → Nat → TFlat rs
  | .let_ (ts := ts) op k, inDepth, inEnv, depth =>
    let pOp : Op (PVal K) ts := ⟨op.code, resolveEnvArgs inDepth inEnv op.args⟩
    match pcStep pOp facts depth with
    | .elim res =>
      pathCondOptFlatAux facts k (inDepth + ts.length) (insertTupEnv inDepth inEnv res) depth
    | .emit op' wrap =>
      let wrapped := wrap (Tup.levels ts depth)
      .let_ ⟨op'.code, idxArgs depth op'.args⟩
        (pathCondOptFlatAux facts k
          (inDepth + ts.length) (insertTupEnv inDepth inEnv wrapped) (depth + ts.length))
  | .load t a k, inDepth, inEnv, depth =>
    let a' := pOut (resolveEnvArg inDepth inEnv a)
    let inEnv' := inEnv.insert inDepth ⟨t, PVal.fresh t depth depth⟩
    .load t (idxArg depth a') (pathCondOptFlatAux facts k (inDepth + 1) inEnv' (depth + 1))
  | .store v a k, inDepth, inEnv, depth =>
    let v' := pOut (resolveEnvArg inDepth inEnv v)
    let a' := pOut (resolveEnvArg inDepth inEnv a)
    .store (idxArg depth v') (idxArg depth a') (pathCondOptFlatAux facts k inDepth inEnv depth)
  | .call f bs args k, inDepth, inEnv, depth =>
    let args' := tupPOut (resolveEnvArgs inDepth inEnv args)
    let wrapped := freshPVals bs (Tup.levels bs depth) depth
    .call f bs (idxArgs depth args')
      (pathCondOptFlatAux facts k
        (inDepth + bs.length) (insertTupEnv inDepth inEnv wrapped) (depth + bs.length))
  | .jnz c t e, inDepth, inEnv, depth =>
    let pc := resolveEnvArg inDepth inEnv c
    match resolveBool? facts pc with
    | some true => pathCondOptFlatAux facts t inDepth inEnv depth
    | some false => pathCondOptFlatAux facts e inDepth inEnv depth
    | none =>
      let info := pInfo pc
      .jnz (idxArg depth (pOut pc))
        (pathCondOptFlatAux (pushFacts info.tf facts) t inDepth inEnv depth)
        (pathCondOptFlatAux (pushFacts info.ff facts) e inDepth inEnv depth)
  | .jump j args, inDepth, inEnv, depth =>
    .jump j (idxArgs depth (tupPOut (resolveBoolArgs facts (resolveEnvArgs inDepth inEnv args))))
  | .ret vs, inDepth, inEnv, depth =>
    .ret (idxArgs depth (tupPOut (resolveBoolArgs facts (resolveEnvArgs inDepth inEnv vs))))
  | .exit f args, inDepth, inEnv, depth =>
    .exit f (idxArgs depth (tupPOut (resolveBoolArgs facts (resolveEnvArgs inDepth inEnv args))))
  | .hlt, _, _, _ => .hlt
  | .group bodies k, inDepth, inEnv, depth =>
    .group
      (pathCondOptFlatAuxB facts bodies inDepth inEnv depth)
      (pathCondOptFlatAux facts k inDepth inEnv depth)

/-- Block-list companion of `pathCondOptFlatAux`. -/
def pathCondOptFlatAuxB {rs : List Ty} (facts : List BoolFact) :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × PVal K t) → Nat →
    TBlocks rs sig
  | _, .nil, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inDepth, inEnv, depth =>
    let wrapped := freshPVals ts (Tup.levels ts depth) depth
    .cons
      (pathCondOptFlatAux facts b
        (inDepth + ts.length) (insertTupEnv inDepth inEnv wrapped) (depth + ts.length))
      (pathCondOptFlatAuxB facts bs inDepth inEnv depth)
end

/-- Direct `TFlat` dominating path-fact and known-condition optimization matching
`reifyFunc (Func.pathCondOpt (denoteFunc tf))`. -/
def pathCondOptFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  pathCondOptFlatAux [] tf as.length
    (initEnv (fun {t} x next => PVal.fresh t x next) as) as.length

/-- `TFlatFn` wrapper for `pathCondOptFlat`. -/
def pathCondOptFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, pathCondOptFlat f.as f.body⟩

end OptFlatPathCond
end LeanQbe.T
