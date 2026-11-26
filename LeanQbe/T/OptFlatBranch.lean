module

public import LeanQbe.T.Flat
public import LeanQbe.T.OptFlatPlanKit
public import LeanQbe.T.CondThreadOpt
public import LeanQbe.T.TailDup

/-!
# Native `TFlat` Conditional Branch Threading & Tail Duplication (`OptFlatBranch`)

Direct `TFlat rs → TFlat rs` implementations of `Func.tailDup` and `Func.condThreadPass`,
eliminating PHOAS `denoteFunc`/`reifyFunc` overhead using level-indexed `Trie` environments and
output-depth closures:

* `OptFlatBranch.tailDupFlat` / `OptFlatBranch.tailDupFlatFn`: native `TFlat` loop/once/plan
  mirror of `Func.tailDup` (`PlanLFlat` closures, `0` `shiftTFlat`, `termination_by structural`).
* `OptFlatBranch.condThreadPassFlat` / `OptFlatBranch.condThreadPassFlatFn`: native `TFlat`
  mirror of `Func.condThreadPass` (`ValidLFlat`, `CTLabelFlat`, `peelThreadHeadFlat`,
  `validateInlineFlat`, `rewriteCTInlineFlat`, `validateCTPlanFlat`, `rewriteCTFlat`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace OptFlatBranch

open OptFlatPlanKit

/-! ## Shared Helpers -/

/-- Fallback `.hlt` `TBlocks` for structural mismatch cases. -/
def mkHltTBlocks {rs : List Ty} : (sig : List (List Ty)) → TBlocks rs sig
  | [] => .nil
  | _ :: sig => .cons .hlt (mkHltTBlocks sig)

/-! ## 1. Native `TFlat` Tail Duplication (`tailDupFlat`) -/

/-- Expand kept output label levels `Tup KL (TailDup.filterActsSig acts sig)` into
`Tup (PlanLFlat rs) sig`. -/
def expandDupKeepFlat {rs : List Ty} :
    (acts : List TailDup.DupAct) → (sig : List (List Ty)) →
    Tup KL (TailDup.filterActsSig acts sig) → Tup (PlanLFlat rs) sig
  | _, [], () => ()
  | [], _ :: sig, () => (.dead, deadTupFlat sig)
  | .keep :: acts, _ :: sig, (j, js) => (.keep j, expandDupKeepFlat acts sig js)
  | .dup :: acts, _ :: sig, js
  | .drop :: acts, _ :: sig, js => (.dead, expandDupKeepFlat acts sig js)

mutual
/-- Native `TFlat` mirror of `TailDup.validatePlan`, structurally recursive on `plan`. -/
def validateDupPlanFlat {rs : List Ty} (plan : TailDup.DupPlan)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × TailDup.BoolL ts)) : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    match plan with
    | .node1 pk => validateDupPlanFlat pk inLD inLE k
    | _ => false
  | .jnz _ t e =>
    match plan with
    | .node2 pt pe => validateDupPlanFlat pt inLD inLE t && validateDupPlanFlat pe inLD inLE e
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
    | .group acts pbs pk =>
      let lsNo := TailDup.noDupBoolTup acts sig
      let lsYes := TailDup.dupBoolTup acts sig
      let inLD' := inLD + sig.length
      validateDupBlocksFlat acts pbs inLD' (insertTupEnv inLD inLE lsNo) bodies &&
      validateKeptBlocksFlat acts pbs inLD' (insertTupEnv inLD inLE lsYes) bodies &&
      validateDupPlanFlat pk inLD' (insertTupEnv inLD inLE lsYes) k
    | _ => false
termination_by structural plan

/-- Validate every `.dup` block under `lsNo` matching `TailDup.validateDupBlocks`. -/
def validateDupBlocksFlat {rs : List Ty} (acts : List TailDup.DupAct) (pbs : TailDup.DupPlanB)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × TailDup.BoolL ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | [], .nil =>
    match acts, pbs with
    | [], .nil => true
    | _, _ => false
  | _ :: _, .cons b bs =>
    match acts, pbs with
    | .dup :: acts', .cons pb pbs' =>
      validateDupPlanFlat pb inLD inLE b && validateDupBlocksFlat acts' pbs' inLD inLE bs
    | .keep :: acts', .cons _ pbs'
    | .drop :: acts', .cons _ pbs' =>
      validateDupBlocksFlat acts' pbs' inLD inLE bs
    | _, _ => false
termination_by structural pbs

/-- Validate every `.keep` block under `lsYes` matching `TailDup.validateKeptBlocks`. -/
def validateKeptBlocksFlat {rs : List Ty} (acts : List TailDup.DupAct) (pbs : TailDup.DupPlanB)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × TailDup.BoolL ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | [], .nil =>
    match acts, pbs with
    | [], .nil => true
    | _, _ => false
  | _ :: _, .cons b bs =>
    match acts, pbs with
    | .keep :: acts', .cons pb pbs' =>
      validateDupPlanFlat pb inLD inLE b && validateKeptBlocksFlat acts' pbs' inLD inLE bs
    | .dup :: acts', .cons _ pbs'
    | .drop :: acts', .cons _ pbs' =>
      validateKeptBlocksFlat acts' pbs' inLD inLE bs
    | _, _ => false
termination_by structural pbs
end

mutual
/-- Native `TFlat` mirror of `TailDup.rewriteExpr` using `PlanLFlat` output-depth closures,
structurally recursive on `plan`. -/
def rewriteDupFlat {rs : List Ty} (plan : TailDup.DupPlan)
    (inVD : Nat) (inVE : Trie ((t : Ty) × Arg K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × PlanLFlat rs ts))
    (outVD outLD : Nat) : TFlat rs → TFlat rs
  | .let_ (ts := ts) op k =>
    match plan with
    | .node1 pk =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE op.args)
      .let_ ⟨op.code, idxArgs outVD args'⟩
        (rewriteDupFlat pk (inVD + ts.length)
          (insertFreshWith (fun _ _ od => .var od) inVD outVD ts inVE)
          inLD inLE (outVD + ts.length) outLD k)
    | _ => .hlt
  | .load t a k =>
    match plan with
    | .node1 pk =>
      let a' := flattenArg (resolveEnvArg inVD inVE a)
      .load t (idxArg outVD a')
        (rewriteDupFlat pk (inVD + 1) (inVE.insert inVD ⟨t, .var outVD⟩)
          inLD inLE (outVD + 1) outLD k)
    | _ => .hlt
  | .store v a k =>
    match plan with
    | .node1 pk =>
      let v' := flattenArg (resolveEnvArg inVD inVE v)
      let a' := flattenArg (resolveEnvArg inVD inVE a)
      .store (idxArg outVD v') (idxArg outVD a')
        (rewriteDupFlat pk inVD inVE inLD inLE outVD outLD k)
    | _ => .hlt
  | .call f bs args k =>
    match plan with
    | .node1 pk =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE args)
      .call f bs (idxArgs outVD args')
        (rewriteDupFlat pk (inVD + bs.length)
          (insertFreshWith (fun _ _ od => .var od) inVD outVD bs inVE)
          inLD inLE (outVD + bs.length) outLD k)
    | _ => .hlt
  | .jnz c t e =>
    match plan with
    | .node2 pt pe =>
      let c' := flattenArg (resolveEnvArg inVD inVE c)
      .jnz (idxArg outVD c')
        (rewriteDupFlat pt inVD inVE inLD inLE outVD outLD t)
        (rewriteDupFlat pe inVD inVE inLD inLE outVD outLD e)
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
    | .group acts pbs pk =>
      let inLD' := inLD + sig.length
      if acts.any (· == .keep) then
        let keptSig := TailDup.filterActsSig acts sig
        let lsNo := expandDupKeepFlat acts sig (Tup.levels keptSig outLD)
        let inLENo := insertTupEnv inLD inLE lsNo
        let lsDup := buildDupLabelsFlat acts pbs inVD inVE inLD' inLENo bodies lsNo
        let inLEDup := insertTupEnv inLD inLE lsDup
        let outLD' := outLD + keptSig.length
        .group
          (rewriteDupKeptBlocksFlat acts pbs inVD inVE inLD' inLEDup outVD outLD' bodies)
          (rewriteDupFlat pk inVD inVE inLD' inLEDup outVD outLD' k)
      else
        let lsNo : Tup (PlanLFlat rs) sig := deadTupFlat sig
        let inLENo := insertTupEnv inLD inLE lsNo
        let lsDup := buildDupLabelsFlat acts pbs inVD inVE inLD' inLENo bodies lsNo
        let inLEDup := insertTupEnv inLD inLE lsDup
        rewriteDupFlat pk inVD inVE inLD' inLEDup outVD outLD k
    | _ => .hlt
termination_by structural plan

/-- Native `TFlat` mirror of `TailDup.buildDupLabels`, structurally recursive on `pbs`. -/
def buildDupLabelsFlat {rs : List Ty} (acts : List TailDup.DupAct) (pbs : TailDup.DupPlanB)
    (inVD : Nat) (inVE : Trie ((t : Ty) × Arg K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × PlanLFlat rs ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Tup (PlanLFlat rs) sig → Tup (PlanLFlat rs) sig
  | [], .nil, () => ()
  | ts :: sig', .cons b bs, (l, ls) =>
    match acts, pbs with
    | .dup :: acts', .cons pb pbs' =>
      (.splice fun ovd old args =>
        rewriteDupFlat pb (inVD + ts.length) (insertTupEnv inVD inVE args) inLD inLE ovd old b,
       buildDupLabelsFlat acts' pbs' inVD inVE inLD inLE bs ls)
    | .keep :: acts', .cons _ pbs' =>
      (l, buildDupLabelsFlat acts' pbs' inVD inVE inLD inLE bs ls)
    | .drop :: acts', .cons _ pbs' =>
      (.dead, buildDupLabelsFlat acts' pbs' inVD inVE inLD inLE bs ls)
    | _, _ => (.dead, deadTupFlat sig')
termination_by structural pbs

/-- Native `TFlat` mirror of `TailDup.rewriteKeptBlocks`, handling `pbs = .nil` via
`mkHltTBlocks` so recursion is strictly structural on `pbs`. -/
def rewriteDupKeptBlocksFlat {rs : List Ty} :
    (acts : List TailDup.DupAct) → (pbs : TailDup.DupPlanB) →
    Nat → Trie ((t : Ty) × Arg K t) →
    Nat → Trie ((ts : List Ty) × PlanLFlat rs ts) →
    Nat → Nat → {sig : List (List Ty)} → TBlocks rs sig →
    TBlocks rs (TailDup.filterActsSig acts sig)
  | acts, _, _, _, _, _, _, _, [], .nil =>
    mkHltTBlocks (TailDup.filterActsSig acts [])
  | [], _, _, _, _, _, _, _, ts :: sig', .cons _ _ =>
    mkHltTBlocks (TailDup.filterActsSig [] (ts :: sig'))
  | a :: acts', .nil, _, _, _, _, _, _, ts :: sig', .cons _ _ =>
    mkHltTBlocks (TailDup.filterActsSig (a :: acts') (ts :: sig'))
  | .keep :: acts', .cons pb pbs', inVD, inVE, inLD, inLE, outVD, outLD, ts :: _, .cons b bs =>
    .cons
      (rewriteDupFlat pb (inVD + ts.length)
        (insertFreshWith (fun _ _ od => .var od) inVD outVD ts inVE)
        inLD inLE (outVD + ts.length) outLD b)
      (rewriteDupKeptBlocksFlat acts' pbs' inVD inVE inLD inLE outVD outLD bs)
  | .dup :: acts', .cons _ pbs', inVD, inVE, inLD, inLE, outVD, outLD, _ :: _, .cons _ bs
  | .drop :: acts', .cons _ pbs', inVD, inVE, inLD, inLE, outVD, outLD, _ :: _, .cons _ bs =>
    rewriteDupKeptBlocksFlat acts' pbs' inVD inVE inLD inLE outVD outLD bs
termination_by structural _ pbs => pbs
end

/-- Apply a precomputed `DupPlan` directly to `tf` if `validateDupPlanFlat` passes. -/
def tailDupWithPlanFlat (as : List Ty) {rs : List Ty} (plan : TailDup.DupPlan)
    (tf : TFlat rs) : TFlat rs :=
  if validateDupPlanFlat plan 0 .empty tf then
    rewriteDupFlat plan as.length (initEnv (fun x _ => .var x) as) 0 .empty as.length 0 tf
  else
    tf

/-- Single native `TFlat` pass of `tailDupOnce`. -/
def tailDupOnceFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (cfg : TailDup.TailDupConfig := {}) : TFlat rs × Bool :=
  let (plan, info) := TailDup.buildPlan cfg 0 tf
  if info.changed then
    (tailDupWithPlanFlat as plan tf, true)
  else
    (tf, false)

/-- Bounded-iteration native `TFlat` loop matching `Func.tailDupLoop`. -/
def tailDupLoopFlat (as : List Ty) {rs : List Ty} (cfg : TailDup.TailDupConfig) :
    Nat → TFlat rs → TFlat rs
  | 0, tf => tf
  | fuel + 1, tf =>
    let (tf', ch) := tailDupOnceFlat as tf cfg
    if ch then tailDupLoopFlat as cfg fuel tf' else tf'

/-- Native `TFlat` tiny join/tail block duplication matching `reifyFunc (Func.tailDup ...)`. -/
def tailDupFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (cfg : TailDup.TailDupConfig := {}) : TFlat rs :=
  tailDupLoopFlat as cfg cfg.maxIters tf

/-- `TFlatFn` wrapper for `tailDupFlat`. -/
def tailDupFlatFn (f : TFlatFn) (cfg : TailDup.TailDupConfig := {}) : TFlatFn :=
  ⟨f.name, f.as, f.rs, tailDupFlat f.as f.body cfg⟩

/-! ## 2. Native `TFlat` Conditional Branch Threading (`condThreadPassFlat`) -/

open CondThreadOpt

/-- Default fallback operand for out-of-scope variable lookups in `CTOptV` environments. -/
def ctDflt {W : Ty → Type} : ∀ t, Arg (Arg (CTOptV W)) t := fun _ => .var (.var none)

/-- Validation-time label payload matching `CondThreadOpt.ValidL`. -/
structure ValidLFlat (rs : List Ty) (ts : List Ty) where
  target : CTTarget UnitV (fun _ => Unit) ts
  inlineOk? : Tup (Arg (CTOptV UnitV)) ts → Bool

/-- Rewriter-time label payload matching `CondThreadOpt.CTLabel K KL rs ts` using output-depth
closures for `inline?`. -/
structure CTLabelFlat (rs : List Ty) (ts : List Ty) where
  target : CTTarget K KL ts
  inline? : Nat → Nat → Tup (Arg (CTOptV K)) ts → Option (TFlat rs)

/-- Build a `CTLabelFlat` without head-inlining (`inline? := none`). -/
def CTLabelFlat.noInline {rs : List Ty} {ts : List Ty} (t : CTTarget K KL ts) :
    CTLabelFlat rs ts :=
  ⟨t, fun _ _ _ => none⟩

/-- Native `TFlat` emission for a `CTTarget K KL ts` at output depth `(outVD, outLD)`. -/
def emitCTTargetFlat {rs : List Ty} {ts : List Ty} (outVD outLD : Nat)
    (args : Tup (Arg (CTOptV K)) ts) : CTTarget K KL ts → TFlat rs
  | .keep l =>
    match toRealArgs? args with
    | some ra => .jump (idxLabel outLD l) (idxArgs outVD ra)
    | none => .hlt
  | .dead => .hlt
  | .split m lT? lF? lD? =>
    match getTupMem m args with
    | .imm true =>
      match lT?, toRealArgs? (dropTupMem m args) with
      | some lT, some ra => .jump (idxLabel outLD lT) (idxArgs outVD ra)
      | _, _ => .hlt
    | .imm false =>
      match lF?, toRealArgs? (dropTupMem m args) with
      | some lF, some ra => .jump (idxLabel outLD lF) (idxArgs outVD ra)
      | _, _ => .hlt
    | .var (some v) =>
      match lD? with
      | some lD =>
        match toRealArgs? args with
        | some ra => .jump (idxLabel outLD lD) (idxArgs outVD ra)
        | none => .hlt
      | none =>
        match lT?, lF?, toRealArgs? (dropTupMem m args) with
        | some lT, some lF, some ra =>
          .jnz (idxArg outVD (.var v))
            (.jump (idxLabel outLD lT) (idxArgs outVD ra))
            (.jump (idxLabel outLD lF) (idxArgs outVD ra))
        | _, _, _ => .hlt
    | .var none => .hlt

/-- Emit a `.jump` through a `CTLabelFlat` at output depth `(outVD, outLD)`. -/
def CTLabelFlat.emitJump {rs : List Ty} {ts : List Ty} (tryInline : Bool)
    (j : CTLabelFlat rs ts) (outVD outLD : Nat) (args : Tup (Arg (CTOptV K)) ts) : TFlat rs :=
  if tryInline then
    match j.inline? outVD outLD args with
    | some tf => tf
    | none => emitCTTargetFlat outVD outLD args j.target
  else
    emitCTTargetFlat outVD outLD args j.target

/-- Native `TFlat` head constant/copy reduction matching `CondThreadOpt.peelThreadHead`. -/
def peelThreadHeadFlat {W : Ty → Type} {rs : List Ty} :
    Nat → Bool → CTPlan → Nat → Trie ((t : Ty) × Arg (CTOptV W) t) → TFlat rs →
    Bool × CTPlan × Nat × Trie ((t : Ty) × Arg (CTOptV W) t) × TFlat rs
  | 0, res, p, inVD, inVE, tf => (res, p, inVD, inVE, tf)
  | fuel + 1, res, .node1 pk, inVD, inVE, .let_ (ts := dts) ⟨code, args⟩ k =>
    let args' := flattenArgs (resolveEnvArgs inVD inVE args ctDflt)
    match evalThreadLet? code args' with
    | some out =>
      peelThreadHeadFlat fuel res pk (inVD + dts.length) (insertTupEnv inVD inVE out) k
    | none => (res, .node1 pk, inVD, inVE, .let_ ⟨code, args⟩ k)
  | fuel + 1, res, .node2 pt pe, inVD, inVE, .jnz c t e =>
    match flattenArg (resolveEnvArg inVD inVE c ctDflt) with
    | .imm true => peelThreadHeadFlat fuel true pt inVD inVE t
    | .imm false => peelThreadHeadFlat fuel true pe inVD inVE e
    | .var _ => (res, .node2 pt pe, inVD, inVE, .jnz c t e)
  | _, res, p, inVD, inVE, tf => (res, p, inVD, inVE, tf)

/-- Native `TFlat` validator for `.group`-free inline snippets matching
`CondThreadOpt.validateInline`, parameterized over label validity check `checkJ` and
structurally recursive on `plan`. -/
def validateInlineFlat {W : Ty → Type} {LFlat : List Ty → Type} {rs : List Ty}
    (checkJ : ∀ {ts : List Ty}, LFlat ts → Tup (Arg (CTOptV W)) ts → Bool)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × LFlat ts)) :
    Nat → (plan : CTPlan) → Nat → Trie ((t : Ty) × Arg (CTOptV W) t) → TFlat rs → Option Nat
  | 0, _, _, _, _ => none
  | b + 1, .node1 pk, inVD, inVE, .let_ (ts := dts) ⟨code, args⟩ k =>
    let args' := flattenArgs (resolveEnvArgs inVD inVE args ctDflt)
    match evalThreadLet? code args' with
    | some out =>
      validateInlineFlat checkJ inLD inLE (b + 1) pk (inVD + dts.length)
        (insertTupEnv inVD inVE out) k
    | none =>
      (validateInlineFlat checkJ inLD inLE b pk (inVD + dts.length)
        (insertTupEnv inVD inVE (noneArgTup dts)) k).map (· + 1)
  | b + 1, .node1 pk, inVD, inVE, .load t _ k =>
    (validateInlineFlat checkJ inLD inLE b pk (inVD + 1)
      (inVE.insert inVD ⟨t, .var none⟩) k).map (· + 1)
  | b + 1, .node1 pk, inVD, inVE, .store _ _ k =>
    (validateInlineFlat checkJ inLD inLE b pk inVD inVE k).map (· + 1)
  | b + 1, .node1 pk, inVD, inVE, .call _ bs _ k =>
    (validateInlineFlat checkJ inLD inLE b pk (inVD + bs.length)
      (insertTupEnv inVD inVE (noneArgTup bs)) k).map (· + 1)
  | b + 1, .node2 pt pe, inVD, inVE, .jnz c t e =>
    match flattenArg (resolveEnvArg inVD inVE c ctDflt) with
    | .imm true => validateInlineFlat checkJ inLD inLE (b + 1) pt inVD inVE t
    | .imm false => validateInlineFlat checkJ inLD inLE (b + 1) pe inVD inVE e
    | .var _ => do
      let st ← validateInlineFlat checkJ inLD inLE b pt inVD inVE t
      let se ← validateInlineFlat checkJ inLD inLE (b - st) pe inVD inVE e
      pure (1 + st + se)
  | _ + 1, .jump _, inVD, inVE, .jump (ts := ts) j args =>
    let args' := flattenArgs (resolveEnvArgs inVD inVE args ctDflt)
    match resolveLabel inLD inLE ts j with
    | some jl => if checkJ jl args' then some 1 else none
    | none => none
  | _ + 1, .leaf, _, _, .ret _
  | _ + 1, .leaf, _, _, .exit _ _
  | _ + 1, .leaf, _, _, .hlt => some 1
  | _, _, _, _, _ => none
termination_by structural _ plan => plan

/-- Non-`.group` single-pass native `TFlat` rewriter for validated inline snippets matching
`CondThreadOpt.rewriteCTInline`, structurally recursive on `plan`. -/
def rewriteCTInlineFlat {rs : List Ty}
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × CTLabelFlat rs ts))
    (plan : CTPlan) (inVD : Nat) (inVE : Trie ((t : Ty) × Arg (CTOptV K) t))
    (outVD outLD : Nat) : TFlat rs → TFlat rs
  | .let_ (ts := dts) ⟨code, args⟩ k =>
    match plan with
    | .node1 pk =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE args ctDflt)
      match evalThreadLet? code args' with
      | some out =>
        rewriteCTInlineFlat inLD inLE pk (inVD + dts.length) (insertTupEnv inVD inVE out)
          outVD outLD k
      | none =>
        match toRealArgs? args' with
        | some rargs =>
          .let_ ⟨code, idxArgs outVD rargs⟩
            (rewriteCTInlineFlat inLD inLE pk (inVD + dts.length)
              (insertFreshWith (fun _ _ od => .var (some od)) inVD outVD dts inVE)
              (outVD + dts.length) outLD k)
        | none => .hlt
    | _ => .hlt
  | .load t a k =>
    match plan with
    | .node1 pk =>
      match toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt)) with
      | some ra =>
        .load t (idxArg outVD ra)
          (rewriteCTInlineFlat inLD inLE pk (inVD + 1)
            (inVE.insert inVD ⟨t, .var (some outVD)⟩) (outVD + 1) outLD k)
      | none => .hlt
    | _ => .hlt
  | .store v a k =>
    match plan with
    | .node1 pk =>
      let v' := toRealArg? (flattenArg (resolveEnvArg inVD inVE v ctDflt))
      let a' := toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt))
      match v', a' with
      | some rv, some ra =>
        .store (idxArg outVD rv) (idxArg outVD ra)
          (rewriteCTInlineFlat inLD inLE pk inVD inVE outVD outLD k)
      | _, _ => .hlt
    | _ => .hlt
  | .call f bs args k =>
    match plan with
    | .node1 pk =>
      match toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | some rargs =>
        .call f bs (idxArgs outVD rargs)
          (rewriteCTInlineFlat inLD inLE pk (inVD + bs.length)
            (insertFreshWith (fun _ _ od => .var (some od)) inVD outVD bs inVE)
            (outVD + bs.length) outLD k)
      | none => .hlt
    | _ => .hlt
  | .jnz c t e =>
    match plan with
    | .node2 pt pe =>
      match flattenArg (resolveEnvArg inVD inVE c ctDflt) with
      | .imm true => rewriteCTInlineFlat inLD inLE pt inVD inVE outVD outLD t
      | .imm false => rewriteCTInlineFlat inLD inLE pe inVD inVE outVD outLD e
      | .var (some v) =>
        .jnz (idxArg outVD (.var v))
          (rewriteCTInlineFlat inLD inLE pt inVD inVE outVD outLD t)
          (rewriteCTInlineFlat inLD inLE pe inVD inVE outVD outLD e)
      | .var none => .hlt
    | _ => .hlt
  | .jump (ts := ts) j args =>
    match plan with
    | .jump _ =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE args ctDflt)
      match resolveLabel inLD inLE ts j with
      | some jl =>
        if jl.target.canEmit args' then emitCTTargetFlat outVD outLD args' jl.target
        else (jl.inline? outVD outLD args').getD .hlt
      | none => .hlt
    | _ => .hlt
  | .ret vs =>
    match plan with
    | .leaf =>
      match toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE vs ctDflt)) with
      | some rvs => .ret (idxArgs outVD rvs)
      | none => .hlt
    | _ => .hlt
  | .exit f args =>
    match plan with
    | .leaf =>
      match toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | some rargs => .exit f (idxArgs outVD rargs)
      | none => .hlt
    | _ => .hlt
  | .hlt | .group _ _ => .hlt
termination_by structural plan

/-- Build validation-time `ValidLFlat` targets matching `CondThreadOpt.validTargets`. -/
def validTargetsFlat {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) → Tup (ValidLFlat rs) sig
  | _, [] => ()
  | [], _ :: sig => (⟨.keep (), fun _ => false⟩, validTargetsFlat [] sig)
  | a :: acts, ts :: sig =>
    let tgt : CTTarget UnitV (fun _ => Unit) ts := match a with
      | .keep true _ => .keep ()
      | .keep false _ => .dead
      | .splitBool p keepT keepF keepDisp _ _ =>
        match splitMember? p ts with
        | none => .keep ()
        | some m =>
          .split m (if keepT then some () else none) (if keepF then some () else none)
            (if keepDisp then some () else none)
    (⟨tgt, fun _ => false⟩, validTargetsFlat acts sig)

/-- Attach validation-time inline checks onto a `ValidLFlat` matching
`CondThreadOpt.tryMakeInlineLabel` (`V := UnitV`, `L := fun _ => Unit`). -/
def tryMakeValidInlineFlat {rs ts : List Ty} (inVD : Nat)
    (inVE : Trie ((t : Ty) × Arg (CTOptV UnitV) t))
    (inLD : Nat) (inLE : Trie ((ts' : List Ty) × ValidLFlat rs ts'))
    (act : BlockAct) (pb : CTPlan) (b : TFlat rs) (l : ValidLFlat rs ts) : ValidLFlat rs ts :=
  let checkJ : ∀ {ts' : List Ty}, ValidLFlat rs ts' → Tup (Arg (CTOptV UnitV)) ts' → Bool :=
    fun jl a => jl.target.canEmit a || jl.inlineOk? a
  match act with
  | .keep _ false => l
  | .keep _ true =>
    ⟨l.target, fun args =>
      let (res, p', inVD', inVE', tf') :=
        peelThreadHeadFlat 4 false pb (inVD + ts.length) (insertTupEnv inVD inVE args) b
      let budget := if res then 8 else 3
      (validateInlineFlat checkJ inLD inLE budget p' inVD' inVE' tf').isSome⟩
  | .splitBool _ _ _ _ inlT inlF =>
    if inlT || inlF then
      ⟨l.target, fun args =>
        let (res, p', inVD', inVE', tf') :=
          peelThreadHeadFlat 4 false pb (inVD + ts.length) (insertTupEnv inVD inVE args) b
        res && (validateInlineFlat checkJ inLD inLE 8 p' inVD' inVE' tf').isSome⟩
    else l

/-- Attach validation-time inline checks across a block list matching
`CondThreadOpt.attachInlines`. -/
def attachValidInlinesFlat {rs : List Ty} (inVD : Nat)
    (inVE : Trie ((t : Ty) × Arg (CTOptV UnitV) t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × ValidLFlat rs ts)) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    TBlocks rs sig → Tup (ValidLFlat rs) sig → Tup (ValidLFlat rs) sig
  | _, _, [], .nil, () => ()
  | a :: acts, .cons pb pbs, _ :: _, .cons b bs, (l, ls) =>
    (tryMakeValidInlineFlat inVD inVE inLD inLE a pb b l,
     attachValidInlinesFlat inVD inVE inLD inLE acts pbs bs ls)
  | _, _, _ :: _, .cons _ bs, (l, ls) =>
    (l, attachValidInlinesFlat inVD inVE inLD inLE [] .nil bs ls)

mutual
/-- Native `TFlat` structural validator matching `CondThreadOpt.validateCTPlan`,
structurally recursive on `plan`. -/
def validateCTPlanFlat {rs : List Ty} (plan : CTPlan)
    (inVD : Nat) (inVE : Trie ((t : Ty) × Arg (CTOptV UnitV) t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × ValidLFlat rs ts)) : TFlat rs → Bool
  | .let_ (ts := dts) ⟨code, args⟩ k =>
    match plan with
    | .node1 pk =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE args ctDflt)
      match evalThreadLet? code args' with
      | some out =>
        validateCTPlanFlat pk (inVD + dts.length) (insertTupEnv inVD inVE out) inLD inLE k
      | none =>
        validateCTPlanFlat pk (inVD + dts.length)
          (insertTupEnv inVD inVE (toOptArgTup (Tup.units dts))) inLD inLE k
    | _ => false
  | .load t _ k =>
    match plan with
    | .node1 pk =>
      validateCTPlanFlat pk (inVD + 1) (inVE.insert inVD ⟨t, .var (some ())⟩) inLD inLE k
    | _ => false
  | .store _ _ k =>
    match plan with
    | .node1 pk => validateCTPlanFlat pk inVD inVE inLD inLE k
    | _ => false
  | .call _ bs _ k =>
    match plan with
    | .node1 pk =>
      validateCTPlanFlat pk (inVD + bs.length)
        (insertTupEnv inVD inVE (toOptArgTup (Tup.units bs))) inLD inLE k
    | _ => false
  | .jnz c t e =>
    match plan with
    | .node2 pt pe =>
      match flattenArg (resolveEnvArg inVD inVE c ctDflt) with
      | .imm true => validateCTPlanFlat pt inVD inVE inLD inLE t
      | .imm false => validateCTPlanFlat pe inVD inVE inLD inLE e
      | .var _ =>
        validateCTPlanFlat pt inVD inVE inLD inLE t &&
        validateCTPlanFlat pe inVD inVE inLD inLE e
    | _ => false
  | .jump (ts := ts) j args =>
    match plan with
    | .jump tryInl =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE args ctDflt)
      match resolveLabel inLD inLE ts j with
      | some jl =>
        if tryInl then jl.inlineOk? args' || jl.target.canEmit args'
        else jl.target.canEmit args'
      | none => false
    | _ => false
  | .ret _ | .exit _ _ | .hlt =>
    match plan with
    | .leaf => true
    | _ => false
  | .group (sig := sig) bodies k =>
    match plan with
    | .group acts pbs pk =>
      let lsNoInl := validTargetsFlat acts sig
      let inLD' := inLD + sig.length
      let inLENoInl := insertTupEnv inLD inLE lsNoInl
      let lsBody := attachValidInlinesFlat inVD inVE inLD' inLENoInl acts pbs bodies lsNoInl
      let inLEBody := insertTupEnv inLD inLE lsBody
      validateCTBlocksFlat acts pbs inVD inVE inLD' inLEBody bodies &&
      validateCTPlanFlat pk inVD inVE inLD' inLEBody k
    | _ => false
termination_by structural plan

/-- Validate block branches matching `CondThreadOpt.validateCTBlocks`, structurally recursive on
`pbs`. -/
def validateCTBlocksFlat {rs : List Ty} (acts : List BlockAct) (pbs : CTPlanB)
    (inVD : Nat) (inVE : Trie ((t : Ty) × Arg (CTOptV UnitV) t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × ValidLFlat rs ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | [], .nil =>
    match acts, pbs with
    | [], .nil => true
    | _, _ => false
  | ts :: _, .cons b bs =>
    match acts, pbs with
    | a :: acts', .cons pb pbs' =>
      let bodyOk := match a with
        | .keep true _ =>
          validateCTPlanFlat pb (inVD + ts.length)
            (insertTupEnv inVD inVE (toOptArgTup (Tup.units ts))) inLD inLE b
        | .keep false _ => true
        | .splitBool p keepT keepF _ _ _ =>
          match splitMember? p ts with
          | none =>
            validateCTPlanFlat pb (inVD + ts.length)
              (insertTupEnv inVD inVE (toOptArgTup (Tup.units ts))) inLD inLE b
          | some m =>
            let argsBase := toOptArgTup (Tup.units (eraseMem m))
            (!keepT || validateCTPlanFlat pb (inVD + ts.length)
              (insertTupEnv inVD inVE (insertTupMem m (.imm true) argsBase)) inLD inLE b) &&
            (!keepF || validateCTPlanFlat pb (inVD + ts.length)
              (insertTupEnv inVD inVE (insertTupMem m (.imm false) argsBase)) inLD inLE b)
      validateAct ts a && bodyOk && validateCTBlocksFlat acts' pbs' inVD inVE inLD inLE bs
    | _, _ => false
termination_by structural pbs
end

/-- Build `Tup (CTLabelFlat rs) sig` without `inline?`, matching `CondThreadOpt.buildTargets`. -/
def buildTargetsFlat {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) → Tup KL (threadSig acts sig) →
    Tup (CTLabelFlat rs) sig
  | _, [], () => ()
  | [], _ :: sig, (j, js) => (CTLabelFlat.noInline (.keep j), buildTargetsFlat [] sig js)
  | a :: acts, ts :: sig, js =>
    let (headJs, tailJs) := splitLabelTup (actSig ts a) (threadSig acts sig) js
    (CTLabelFlat.noInline (mkActTarget ts a headJs), buildTargetsFlat acts sig tailJs)

/-- Attach depth-1 `inline?` closure onto a `CTLabelFlat` matching
`CondThreadOpt.tryMakeInlineLabel`. -/
def tryMakeInlineLabelFlat {rs ts : List Ty} (inVD : Nat)
    (inVE : Trie ((t : Ty) × Arg (CTOptV K) t))
    (inLD : Nat) (inLE : Trie ((ts' : List Ty) × CTLabelFlat rs ts'))
    (act : BlockAct) (pb : CTPlan) (b : TFlat rs) (l : CTLabelFlat rs ts) : CTLabelFlat rs ts :=
  let checkJ : ∀ {ts' : List Ty}, CTLabelFlat rs ts' → Tup (Arg (CTOptV K)) ts' → Bool :=
    fun jl a => jl.target.canEmit a || (jl.inline? 0 0 a).isSome
  match act with
  | .keep _ false => l
  | .keep _ true =>
    ⟨l.target, fun ovd old args =>
      let (res, p', inVD', inVE', tf') :=
        peelThreadHeadFlat 4 false pb (inVD + ts.length) (insertTupEnv inVD inVE args) b
      let budget := if res then 8 else 3
      if (validateInlineFlat checkJ inLD inLE budget p' inVD' inVE' tf').isSome then
        some (rewriteCTInlineFlat inLD inLE p' inVD' inVE' ovd old tf')
      else none⟩
  | .splitBool _ _ _ _ inlT inlF =>
    if inlT || inlF then
      ⟨l.target, fun ovd old args =>
        let (res, p', inVD', inVE', tf') :=
          peelThreadHeadFlat 4 false pb (inVD + ts.length) (insertTupEnv inVD inVE args) b
        if res && (validateInlineFlat checkJ inLD inLE 8 p' inVD' inVE' tf').isSome then
          some (rewriteCTInlineFlat inLD inLE p' inVD' inVE' ovd old tf')
        else none⟩
    else l

/-- Attach `inline?` closures onto `lsNoInl` matching `CondThreadOpt.attachInlines`. -/
def attachInlinesFlat {rs : List Ty} (inVD : Nat)
    (inVE : Trie ((t : Ty) × Arg (CTOptV K) t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × CTLabelFlat rs ts)) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    TBlocks rs sig → Tup (CTLabelFlat rs) sig → Tup (CTLabelFlat rs) sig
  | _, _, [], .nil, () => ()
  | a :: acts, .cons pb pbs, _ :: _, .cons b bs, (l, ls) =>
    (tryMakeInlineLabelFlat inVD inVE inLD inLE a pb b l,
     attachInlinesFlat inVD inVE inLD inLE acts pbs bs ls)
  | _, _, _ :: _, .cons _ bs, (l, ls) =>
    (l, attachInlinesFlat inVD inVE inLD inLE [] .nil bs ls)

/-- Concatenate two `TBlocks` lists matching `CondThreadOpt.blocksAppend`. -/
def tblocksAppend {rs : List Ty} :
    {s₁ s₂ : List (List Ty)} → TBlocks rs s₁ → TBlocks rs s₂ → TBlocks rs (s₁ ++ s₂)
  | [], _, .nil, bs₂ => bs₂
  | _ :: _, _, .cons b bs₁, bs₂ => .cons b (tblocksAppend bs₁ bs₂)

/-- Prepend a block conditionally matching `CondThreadOpt.condConsBlock`. -/
def condConsTBlock {rs : List Ty} {ts : List Ty} (b : Bool) (blk : Unit → TFlat rs)
    {rest : List (List Ty)} (tl : TBlocks rs rest) :
    TBlocks rs ((if b then [ts] else []) ++ rest) :=
  match b with
  | true => .cons (blk ()) tl
  | false => tl

/-- Assemble transformed `TBlocks` for a `.splitBool` block matching
`CondThreadOpt.mkSplitBlocks`. -/
def mkSplitBlocksFlat {rs ts : List Ty} (m : Member .bool ts) (keepDisp keepT keepF : Bool)
    (lbl : CTLabelFlat rs ts) (outVD outLD : Nat)
    (rwT rwF : TFlat rs) : TBlocks rs (splitSig keepDisp keepT keepF ts (eraseMem m)) :=
  condConsTBlock keepDisp (fun () =>
    match lbl.target with
    | .split m' (some lT) (some lF) _ =>
      let outVD' := outVD + ts.length
      let xs := Tup.levels ts outVD
      let args' := dropTupMem m' (toArgTup xs)
      .jnz (idxArg outVD' (.var (getTupMem m' xs)))
        (.jump (idxLabel outLD lT) (idxArgs outVD' args'))
        (.jump (idxLabel outLD lF) (idxArgs outVD' args'))
    | _ => .hlt)
    (condConsTBlock keepT (fun () => rwT)
      (condConsTBlock keepF (fun () => rwF) .nil))

/-- Helper for `rewriteCTBlocksFlat` indexed on `splitMember? p ts`. -/
def mkSplitCurBlocksFlat {rs ts : List Ty} (keepT keepF keepDisp : Bool)
    (l : CTLabelFlat rs ts) (outVD outLD : Nat) (rwId : TFlat rs)
    (rwSplit : (m : Member .bool ts) → Bool → TFlat rs) :
    (sp : Option (Member .bool ts)) → TBlocks rs (splitMemberSig ts keepT keepF keepDisp sp)
  | none => .cons rwId .nil
  | some m =>
    mkSplitBlocksFlat m keepDisp keepT keepF l outVD outLD (rwSplit m true) (rwSplit m false)

mutual
/-- Emit all transformed blocks of a `.group` matching `CondThreadOpt.rewriteCTBlocks`,
handling mismatched `.nil` lengths via `mkHltTBlocks` so recursion is strictly structural on
`pbs`. -/
def rewriteCTBlocksFlat {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) →
    Nat → Trie ((t : Ty) × Arg (CTOptV K) t) →
    Nat → Trie ((ts : List Ty) × CTLabelFlat rs ts) →
    Nat → Nat → {sig : List (List Ty)} → TBlocks rs sig → Tup (CTLabelFlat rs) sig →
    TBlocks rs (threadSig acts sig)
  | acts, _, _, _, _, _, _, _, [], .nil, () => mkHltTBlocks (threadSig acts [])
  | [], _, _, _, _, _, _, _, ts :: sig', .cons _ _, _ =>
    mkHltTBlocks (threadSig [] (ts :: sig'))
  | a :: acts', .nil, _, _, _, _, _, _, ts :: sig', .cons _ _, _ =>
    mkHltTBlocks (threadSig (a :: acts') (ts :: sig'))
  | a :: acts', .cons pb pbs', inVD, inVE, inLD, inLE, outVD, outLD, ts :: _,
      .cons b bs, (l, ls') =>
    let cur : TBlocks rs (actSig ts a) := match a with
      | .keep true _ =>
        .cons
          (rewriteCTFlat pb (inVD + ts.length)
            (insertFreshWith (fun _ _ od => .var (some od)) inVD outVD ts inVE)
            inLD inLE (outVD + ts.length) outLD b)
          .nil
      | .keep false _ => .nil
      | .splitBool p keepT keepF keepDisp _ _ =>
        mkSplitCurBlocksFlat keepT keepF keepDisp l outVD outLD
          (rewriteCTFlat pb (inVD + ts.length)
            (insertFreshWith (fun _ _ od => .var (some od)) inVD outVD ts inVE)
            inLD inLE (outVD + ts.length) outLD b)
          (fun m bVal =>
            let args := insertTupMem m (.imm bVal) (toOptArgTup (Tup.levels (eraseMem m) outVD))
            rewriteCTFlat pb (inVD + ts.length) (insertTupEnv inVD inVE args)
              inLD inLE (outVD + (eraseMem m).length) outLD b)
          (splitMember? p ts)
    tblocksAppend cur (rewriteCTBlocksFlat acts' pbs' inVD inVE inLD inLE outVD outLD bs ls')
termination_by structural _ pbs => pbs

/-- Single-pass native `TFlat` rewriter matching `CondThreadOpt.rewriteCTAux`, structurally
recursive on `plan`. -/
def rewriteCTFlat {rs : List Ty} (plan : CTPlan)
    (inVD : Nat) (inVE : Trie ((t : Ty) × Arg (CTOptV K) t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × CTLabelFlat rs ts))
    (outVD outLD : Nat) : TFlat rs → TFlat rs
  | .let_ (ts := dts) ⟨code, args⟩ k =>
    match plan with
    | .node1 pk =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE args ctDflt)
      match evalThreadLet? code args' with
      | some out =>
        rewriteCTFlat pk (inVD + dts.length) (insertTupEnv inVD inVE out) inLD inLE outVD outLD k
      | none =>
        match toRealArgs? args' with
        | some rargs =>
          .let_ ⟨code, idxArgs outVD rargs⟩
            (rewriteCTFlat pk (inVD + dts.length)
              (insertFreshWith (fun _ _ od => .var (some od)) inVD outVD dts inVE)
              inLD inLE (outVD + dts.length) outLD k)
        | none => .hlt
    | _ => .hlt
  | .load t a k =>
    match plan with
    | .node1 pk =>
      match toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt)) with
      | some ra =>
        .load t (idxArg outVD ra)
          (rewriteCTFlat pk (inVD + 1) (inVE.insert inVD ⟨t, .var (some outVD)⟩)
            inLD inLE (outVD + 1) outLD k)
      | none => .hlt
    | _ => .hlt
  | .store v a k =>
    match plan with
    | .node1 pk =>
      let v' := toRealArg? (flattenArg (resolveEnvArg inVD inVE v ctDflt))
      let a' := toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt))
      match v', a' with
      | some rv, some ra =>
        .store (idxArg outVD rv) (idxArg outVD ra)
          (rewriteCTFlat pk inVD inVE inLD inLE outVD outLD k)
      | _, _ => .hlt
    | _ => .hlt
  | .call f bs args k =>
    match plan with
    | .node1 pk =>
      match toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | some rargs =>
        .call f bs (idxArgs outVD rargs)
          (rewriteCTFlat pk (inVD + bs.length)
            (insertFreshWith (fun _ _ od => .var (some od)) inVD outVD bs inVE)
            inLD inLE (outVD + bs.length) outLD k)
      | none => .hlt
    | _ => .hlt
  | .jnz c t e =>
    match plan with
    | .node2 pt pe =>
      match flattenArg (resolveEnvArg inVD inVE c ctDflt) with
      | .imm true => rewriteCTFlat pt inVD inVE inLD inLE outVD outLD t
      | .imm false => rewriteCTFlat pe inVD inVE inLD inLE outVD outLD e
      | .var (some v) =>
        .jnz (idxArg outVD (.var v))
          (rewriteCTFlat pt inVD inVE inLD inLE outVD outLD t)
          (rewriteCTFlat pe inVD inVE inLD inLE outVD outLD e)
      | .var none => .hlt
    | _ => .hlt
  | .jump (ts := ts) j args =>
    match plan with
    | .jump tryInl =>
      let args' := flattenArgs (resolveEnvArgs inVD inVE args ctDflt)
      match resolveLabel inLD inLE ts j with
      | some jl => jl.emitJump tryInl outVD outLD args'
      | none => .hlt
    | _ => .hlt
  | .ret vs =>
    match plan with
    | .leaf =>
      match toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE vs ctDflt)) with
      | some rvs => .ret (idxArgs outVD rvs)
      | none => .hlt
    | _ => .hlt
  | .exit f args =>
    match plan with
    | .leaf =>
      match toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | some rargs => .exit f (idxArgs outVD rargs)
      | none => .hlt
    | _ => .hlt
  | .hlt => .hlt
  | .group (sig := sig) bodies k =>
    match plan with
    | .group acts pbs pk =>
      let outSig := threadSig acts sig
      let lsNoInl := buildTargetsFlat acts sig (Tup.levels outSig outLD)
      let inLD' := inLD + sig.length
      let inLENoInl := insertTupEnv inLD inLE lsNoInl
      let lsBody := attachInlinesFlat inVD inVE inLD' inLENoInl acts pbs bodies lsNoInl
      let inLEBody := insertTupEnv inLD inLE lsBody
      let outLD' := outLD + outSig.length
      .group
        (rewriteCTBlocksFlat acts pbs inVD inVE inLD' inLEBody outVD outLD' bodies lsNoInl)
        (rewriteCTFlat pk inVD inVE inLD' inLEBody outVD outLD' k)
    | _ => .hlt
termination_by structural plan
end

/-- Apply a precomputed `CTPlan` directly to `tf` if `validateCTPlanFlat` passes. -/
def condThreadWithPlanFlat (as : List Ty) {rs : List Ty} (plan : CTPlan)
    (tf : TFlat rs) : TFlat rs :=
  if validateCTPlanFlat plan as.length (initEnv (fun _ _ => .var (some ())) as) 0 .empty tf then
    rewriteCTFlat plan as.length (initEnv (fun x _ => .var (some x)) as) 0 .empty as.length 0 tf
  else
    tf

/-- Native `TFlat` constant-arg branch threading and bool-param splitting matching
`reifyFunc (Func.condThreadPass ...)`. -/
def condThreadPassFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  let (st, _) := collectStats 0 tf
  let plan := buildCTPlan [] tf st
  if plan.hasChanges then condThreadWithPlanFlat as plan tf
  else tf

/-- `TFlatFn` wrapper for `condThreadPassFlat`. -/
def condThreadPassFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, condThreadPassFlat f.as f.body⟩

end OptFlatBranch
end LeanQbe.T
