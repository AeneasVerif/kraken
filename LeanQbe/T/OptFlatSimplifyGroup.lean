module

public import LeanQbe.T.Flat
public import LeanQbe.T.OptFlatPlanKit
public import LeanQbe.T.SimplifyGroupPlan

/-!
# Native `TFlat` Plan-Guided Join-Group Simplification (`OptFlatSimplifyGroup`)

Direct `TFlat rs → TFlat rs` implementation of `Func.simplifyGroupWithPlan` and
`Func.simplifyGroupPlan`, eliminating PHOAS `denoteFunc`/`reifyFunc` round-trips using
level-indexed `Trie` environments and `PlanLFlat` output-depth closures (`0` shifts,
`termination_by structural`):

* `OptFlatSimplifyGroup.validatePlanFlat`: native `TFlat` mirror of `SgpImpl.validatePlan`.
* `OptFlatSimplifyGroup.rewriteExprFlat`: native `TFlat` mirror of `SgpImpl.rewriteExpr`.
* `OptFlatSimplifyGroup.simplifyGroupWithPlanFlat` / `simplifyGroupPlanFlat`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace OptFlatSimplifyGroup

open OptFlatPlanKit
open SgpImpl

/-- Fallback `.hlt` `TBlocks` for structural plan-mismatch cases. -/
def mkHltTBlocks {rs : List Ty} : (sig : List (List Ty)) → TBlocks rs sig
  | [] => .nil
  | _ :: sig => .cons .hlt (mkHltTBlocks sig)

mutual
/-- Native `TFlat` mirror of `SgpImpl.validatePlan`, structurally recursive on `plan`. -/
def validatePlanFlat {rs : List Ty} (plan : SimpPlan)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × BoolL ts)) : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    match plan with
    | .node1 pk => validatePlanFlat pk inLD inLE k
    | _ => false
  | .jnz _ t e =>
    match plan with
    | .node2 pt pe => validatePlanFlat pt inLD inLE t && validatePlanFlat pe inLD inLE e
    | _ => false
  | .jump (ts := ts) j _ =>
    match plan with
    | .leaf => (resolveLabel inLD inLE ts j).getD false
    | _ => false
  | .ret _ | .exit _ _ | .hlt =>
    match plan with
    | .leaf => true
    | _ => false
  | .group (sig := sig) bodies k =>
    match plan with
    | .group .unwrap _ pk =>
      validatePlanFlat pk (inLD + sig.length) (insertTupEnv inLD inLE (allFalse sig)) k
    | .group (.splice idx) pbs pk =>
      let inLD' := inLD + sig.length
      validateSpliceBlockFlat idx pbs inLD' (insertTupEnv inLD inLE (allFalse sig)) bodies &&
      validatePlanFlat pk inLD' (insertTupEnv inLD inLE (oneTrue idx sig)) k
    | .group (.filter keep) pbs pk =>
      let ls := boolTup keep sig
      let inLD' := inLD + sig.length
      let inLE' := insertTupEnv inLD inLE ls
      validateFilteredBlocksFlat keep pbs inLD' inLE' bodies &&
      validatePlanFlat pk inLD' inLE' k
    | _ => false
termination_by structural plan

/-- Validate the single spliced block at index `idx` under all-dead local labels. -/
def validateSpliceBlockFlat {rs : List Ty} (idx : Nat) (pbs : SimpPlanB)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × BoolL ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | [], .nil => false
  | _ :: _, .cons b bs =>
    match idx, pbs with
    | 0, .cons pb _ => validatePlanFlat pb inLD inLE b
    | idx' + 1, .cons _ pbs' => validateSpliceBlockFlat idx' pbs' inLD inLE bs
    | _, .nil => false
termination_by structural pbs

/-- Validate every kept block in a `.filter keep` group and check mask/plan/sig lengths. -/
def validateFilteredBlocksFlat {rs : List Ty} (ks : List Bool) (pbs : SimpPlanB)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × BoolL ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | [], .nil =>
    match ks, pbs with
    | [], .nil => true
    | _, _ => false
  | _ :: _, .cons b bs =>
    match ks, pbs with
    | true :: ks', .cons pb pbs' =>
      validatePlanFlat pb inLD inLE b && validateFilteredBlocksFlat ks' pbs' inLD inLE bs
    | false :: ks', .cons _ pbs' =>
      validateFilteredBlocksFlat ks' pbs' inLD inLE bs
    | _, _ => false
termination_by structural pbs
end

mutual
/-- Native `TFlat` mirror of `SgpImpl.rewriteExpr` using `PlanLFlat` output-depth closures,
structurally recursive on `plan`. -/
def rewriteExprFlat {rs : List Ty} (plan : SimpPlan)
    (inVD : Nat) (inVE : Trie ((t : Ty) × Arg K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × PlanLFlat rs ts))
    (outVD outLD : Nat) : TFlat rs → TFlat rs
  | .let_ (ts := ts) op k =>
    match plan with
    | .node1 pk =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE op.args)
      .let_ ⟨op.code, idxArgs outVD args'⟩
        (rewriteExprFlat pk (inVD + ts.length)
          (insertFreshWith (fun _ _ od => .var od) inVD outVD ts inVE)
          inLD inLE (outVD + ts.length) outLD k)
    | _ => .hlt
  | .load t a k =>
    match plan with
    | .node1 pk =>
      let a' := flattenArg (resolveEnvArg inVD inVE a)
      .load t (idxArg outVD a')
        (rewriteExprFlat pk (inVD + 1) (inVE.insert inVD ⟨t, .var outVD⟩)
          inLD inLE (outVD + 1) outLD k)
    | _ => .hlt
  | .store v a k =>
    match plan with
    | .node1 pk =>
      let v' := flattenArg (resolveEnvArg inVD inVE v)
      let a' := flattenArg (resolveEnvArg inVD inVE a)
      .store (idxArg outVD v') (idxArg outVD a')
        (rewriteExprFlat pk inVD inVE inLD inLE outVD outLD k)
    | _ => .hlt
  | .call f bs args k =>
    match plan with
    | .node1 pk =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE args)
      .call f bs (idxArgs outVD args')
        (rewriteExprFlat pk (inVD + bs.length)
          (insertFreshWith (fun _ _ od => .var od) inVD outVD bs inVE)
          inLD inLE (outVD + bs.length) outLD k)
    | _ => .hlt
  | .jnz c t e =>
    match plan with
    | .node2 pt pe =>
      let c' := flattenArg (resolveEnvArg inVD inVE c)
      .jnz (idxArg outVD c')
        (rewriteExprFlat pt inVD inVE inLD inLE outVD outLD t)
        (rewriteExprFlat pe inVD inVE inLD inLE outVD outLD e)
    | _ => .hlt
  | .jump (ts := ts) j args =>
    match plan with
    | .leaf =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE args)
      match resolveLabel inLD inLE ts j with
      | some (.keep outLbl) => .jump (idxLabel outLD outLbl) (idxArgs outVD args')
      | some .dead => .hlt
      | some (.splice body) => body outVD outLD args'
      | none => .hlt
    | _ => .hlt
  | .ret vs =>
    match plan with
    | .leaf => .ret (idxArgs outVD (flattenArgs (resolveEnvArgs inVD inVE vs)))
    | _ => .hlt
  | .exit f args =>
    match plan with
    | .leaf => .exit f (idxArgs outVD (flattenArgs (resolveEnvArgs inVD inVE args)))
    | _ => .hlt
  | .hlt => .hlt
  | .group (sig := sig) bodies k =>
    match plan with
    | .group .unwrap _ pk =>
      let inLE' := insertTupEnv inLD inLE (deadTupFlat sig)
      rewriteExprFlat pk inVD inVE (inLD + sig.length) inLE' outVD outLD k
    | .group (.splice idx) pbs pk =>
      let inLD' := inLD + sig.length
      let inLEDead := insertTupEnv inLD inLE (deadTupFlat sig)
      let ls := rewriteSpliceLabelsFlat idx pbs inVD inVE inLD' inLEDead bodies
      let inLE' := insertTupEnv inLD inLE ls
      rewriteExprFlat pk inVD inVE inLD' inLE' outVD outLD k
    | .group (.filter keep) pbs pk =>
      let keptSig := filterSig keep sig
      let inLD' := inLD + sig.length
      let ls := expandKeepFlat keep sig (Tup.levels keptSig outLD)
      let inLE' := insertTupEnv inLD inLE ls
      let outLD' := outLD + keptSig.length
      .group
        (rewriteFilteredBlocksFlat keep pbs inVD inVE inLD' inLE' outVD outLD' bodies)
        (rewriteExprFlat pk inVD inVE inLD' inLE' outVD outLD' k)
    | _ => .hlt
termination_by structural plan

/-- Native `TFlat` mirror of `SgpImpl.rewriteSpliceLabels`, structurally recursive on `pbs`. -/
def rewriteSpliceLabelsFlat {rs : List Ty} (idx : Nat) (pbs : SimpPlanB)
    (inVD : Nat) (inVE : Trie ((t : Ty) × Arg K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × PlanLFlat rs ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Tup (PlanLFlat rs) sig
  | [], .nil => ()
  | ts :: sig', .cons b bs =>
    match idx, pbs with
    | 0, .cons pb _ =>
      (.splice fun ovd old args =>
        rewriteExprFlat pb (inVD + ts.length) (insertTupEnv inVD inVE args) inLD inLE ovd old b,
       deadTupFlat sig')
    | idx' + 1, .cons _ pbs' =>
      (.dead, rewriteSpliceLabelsFlat idx' pbs' inVD inVE inLD inLE bs)
    | _, .nil => (.dead, deadTupFlat sig')
termination_by structural pbs

/-- Native `TFlat` mirror of `SgpImpl.rewriteFilteredBlocks`, handling `pbs = .nil` via
`mkHltTBlocks` so recursion is strictly structural on `pbs`. -/
def rewriteFilteredBlocksFlat {rs : List Ty} :
    (ks : List Bool) → (pbs : SimpPlanB) →
    Nat → Trie ((t : Ty) × Arg K t) →
    Nat → Trie ((ts : List Ty) × PlanLFlat rs ts) →
    Nat → Nat → {sig : List (List Ty)} → TBlocks rs sig →
    TBlocks rs (filterSig ks sig)
  | ks, _, _, _, _, _, _, _, [], .nil =>
    mkHltTBlocks (filterSig ks [])
  | [], _, _, _, _, _, _, _, ts :: sig', .cons _ _ =>
    mkHltTBlocks (filterSig [] (ts :: sig'))
  | k :: ks', .nil, _, _, _, _, _, _, ts :: sig', .cons _ _ =>
    mkHltTBlocks (filterSig (k :: ks') (ts :: sig'))
  | true :: ks', .cons pb pbs', inVD, inVE, inLD, inLE, outVD, outLD, ts :: _, .cons b bs =>
    .cons
      (rewriteExprFlat pb (inVD + ts.length)
        (insertFreshWith (fun _ _ od => .var od) inVD outVD ts inVE)
        inLD inLE (outVD + ts.length) outLD b)
      (rewriteFilteredBlocksFlat ks' pbs' inVD inVE inLD inLE outVD outLD bs)
  | false :: ks', .cons _ pbs', inVD, inVE, inLD, inLE, outVD, outLD, _ :: _, .cons _ bs =>
    rewriteFilteredBlocksFlat ks' pbs' inVD inVE inLD inLE outVD outLD bs
termination_by structural _ pbs => pbs
end

/-- Apply a precomputed `SimpPlan` directly to `tf` if `validatePlanFlat` passes. -/
def simplifyGroupWithPlanFlat (as : List Ty) {rs : List Ty} (plan : SimpPlan)
    (tf : TFlat rs) : TFlat rs :=
  if validatePlanFlat plan 0 .empty tf then
    rewriteExprFlat plan as.length (initEnv (fun x _ => .var x) as) 0 .empty as.length 0 tf
  else
    tf

/-- Direct `TFlat` `O(N)` plan-guided join-group simplification matching
`reifyFunc (Func.simplifyGroupPlan (denoteFunc tf))`. -/
def simplifyGroupPlanFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  let (plan, info) := buildPlan 0 tf
  if info.changed then simplifyGroupWithPlanFlat as plan tf
  else tf

/-- `TFlatFn` wrapper for `simplifyGroupPlanFlat`. -/
def simplifyGroupPlanFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, simplifyGroupPlanFlat f.as f.body⟩

end OptFlatSimplifyGroup
end LeanQbe.T
