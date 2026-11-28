/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public meta import Lean
public meta import LeanQbe.T.InlinePlanSeg
public meta import LeanQbe.T.MainCertSeg
public meta import LeanQbe.T.MainCertSegStaged
public meta import LeanQbe.T.MainCertFlat
public meta import LeanQbe.T.MainCertFlatDecode
public meta import LeanQbe.T.MainFlat
public meta import LeanQbe.T.MainCertInline

/-!
# Subsystem-Aligned Plan-Inline & Oracle-Hint Cert Elaborators (`MainCertSegElab`)

Declarative command elaborators for subsystem-aligned `Build/` modules reading untrusted oracle
constants (`plan`, `hints`, `ext`) with **zero** `meta import LeanQbe.T.Spill` and **zero**
`Spill.hints` invocations:

* `inline_seg! segId srcFnsExpr (plan := ...) [(deps := ...)] [(exports := ...)]`:
  materializes per-subsystem post-inline `TFlatFn`s with independent per-function kernel `rfl`
  step proofs (no cascading reduction), exports `segId.seg : InlSeg`, and optionally proves
  `segId.exports_sub : ∀ e ∈ exportsExpr, e ∈ segId.fns`.
* `seg_cert! segCertId target layout legalTarget labelClean fnsExpr (hints := ...) (ext := ...)`:
  compiles a subsystem's materialized `TFlatFn`s via `compileModuleFlat` using precomputed oracle
  `hints` and `ext`, emitting `segCertId : SegChunks ...` (or `segCertId.part0`, `part1`, ...
  around excluded heavy functions when `(exclude := [...])` is specified).
* `fn_cert! fnCertId target layout legalTarget labelClean flatFnExpr (hints := ...) (ext := ...)`:
  compiles a single isolated heavy `TFlatFn` with its oracle `hint` and `ext`, emitting
  `fnCertId : SegChunks ...`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

meta section

open Lean Elab Command Meta
open InlineMeta

/-! ## 1. Shared Meta Helpers (Zero `Spill` Usage) -/

private def evalLoweredFlatWithHints (I : Isa) (lt : LegalTarget)
    (items : List (TFlatFn × I.Hints × Bool)) :
    Except String (List (Sym × I.Hints × List I.Directive × Rega.Ext × SigEntry × Bool)) :=
  let tasks := items.map fun (f, h, excluded) => Task.spawn fun () =>
    if !f.wfCheck then .error s!"{f.name}: flat wfCheck failed"
    else
      let ef := earlyOptFlat f
      if !ef.supportsSource lt then .error s!"{f.name}: unsupported source op for target"
      else
        let mf := midStageFlat lt ef
        let ext := TFlat.ext mf.body
        if excluded then
          .ok (f.name, h, ([] : List I.Directive), ext, mf.sig, true)
        else
          match Rega.lowerFlatFn I h ext mf with
          | .ok c => .ok (f.name, h, c, ext, mf.sig, false)
          | .error e => .error s!"{f.name}: {e}"
  let rec collect :
      List (Task (Except String (Sym × I.Hints × List I.Directive × Rega.Ext × SigEntry × Bool))) →
      Except String (List (Sym × I.Hints × List I.Directive × Rega.Ext × SigEntry × Bool))
    | [] => .ok []
    | t :: ts => do let v ← t.get; .ok (v :: (← collect ts))
  collect tasks

/-- Evaluated sub-run of non-excluded functions within a subsystem for `seg_cert!`. -/
structure EvalSegRun where
  startIdx : Nat
  fnCount : Nat
  isLastFull : Bool
  data : EvalModuleData
  deriving Inhabited

/-- Evaluate a subsystem's `TFlatFn` list with precomputed oracle `hints` and `ext0`, optionally
splitting around excluded heavy function names while threading their stack bounds accurately. -/
def evalSegCertRuns (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (chunkSize maxBound maxDirs : Nat) (pruneExt : Bool)
    (excludeNames : List Sym) (fs : List TFlatFn) (hs : List I.Hints)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String (List EvalSegRun) := do
  if fs.length != hs.length then
    throw s!"seg_cert!: fn/hints length mismatch ({fs.length} fns vs {hs.length} hints)"
  let paired := (fs.zip hs).map fun (f, h) => (f, h, excludeNames.contains f.name)
  let lowered ← evalLoweredFlatWithHints I lt paired
  let rec splitRuns (idx : Nat) (acc : List (SigEntry × Nat))
      (curStart : Nat) (curAcc : List (SigEntry × Nat))
      (curRev : List (Sym × I.Hints × List I.Directive × Rega.Ext × SigEntry))
      (outRev : List EvalSegRun) :
      List (Sym × I.Hints × List I.Directive × Rega.Ext × SigEntry × Bool) →
      Except String (List EvalSegRun)
    | [] => do
      let outRev' ←
        if curRev.isEmpty && !outRev.isEmpty then pure outRev
        else
          let md ← evalLinkedChunksCore I raBytes curAcc exits nX chunkSize maxBound maxDirs
            pruneExt curRev.reverse
          let run : EvalSegRun := {
            startIdx := curStart, fnCount := curRev.length
            isLastFull := curStart == 0 && excludeNames.isEmpty
            data := md
          }
          pure (run :: outRev)
      pure outRev'.reverse
    | (nm, h, c, ext, sig, excluded) :: rest => do
      let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext
      let acc' := (sig, b) :: acc
      if excluded then
        let outRev' ←
          if curRev.isEmpty then pure outRev
          else
            let md ← evalLinkedChunksCore I raBytes curAcc exits nX chunkSize maxBound maxDirs
              pruneExt curRev.reverse
            pure ({ startIdx := curStart, fnCount := curRev.length, isLastFull := false,
                    data := md } :: outRev)
        splitRuns (idx + 1) acc' (idx + 1) acc' [] outRev' rest
      else
        let curStart' := if curRev.isEmpty then idx else curStart
        let curAcc' := if curRev.isEmpty then acc else curAcc
        splitRuns (idx + 1) acc' curStart' curAcc' ((nm, h, c, ext, sig) :: curRev) outRev rest
  splitRuns 0 ext0 0 ext0 [] [] lowered

/-- Curried oracle-hint evaluator for `seg_cert!` over decoded `List TFlatFn`. -/
def makeSegCertEvaluator (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (chunkSize maxBound maxDirs : Nat) (pruneExt : Bool) (excludeNames : List Sym)
    (hs : List I.Hints)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    List TFlatFn → Except String (List EvalSegRun) :=
  fun fs =>
    evalSegCertRuns I lt raBytes ext0 exits nX chunkSize maxBound maxDirs pruneExt
      excludeNames fs hs

/-- Single-function oracle-hint evaluator for `fn_cert!` over a decoded `TFlatFn`. -/
def makeFnCertEvaluator (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (pruneExt : Bool) (h : I.Hints)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    List TFlatFn → Except String EvalModuleData :=
  fun fs => do
    let lowered ← evalLoweredFlatWithHints I lt (fs.map fun f => (f, h, false))
    let stripped := lowered.map fun (nm, hi, c, ext, sig, _) => (nm, hi, c, ext, sig)
    evalLinkedChunksCore I raBytes ext0 exits nX 1 maxBound 0 pruneExt stripped

/-- Peel a concrete `List` expression into element `Lean.Expr`s using `whnf` (returns `none`
if the tail is not a concrete `List.cons`/`List.nil` spine). -/
private def tryPeelListElems (listE : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let mut cur := listE
  let mut out : Array Lean.Expr := #[]
  while true do
    let w ← whnf cur
    if w.isAppOfArity ``List.nil 1 then
      return some out
    else if w.isAppOfArity ``List.cons 3 then
      let args := w.getAppArgs
      out := out.push args[1]!
      cur := args[2]!
    else
      return none
  return none

/-- Build a proof of `elem ∈ [a0, a1, ..., a_{n-1}]` at index `idx` in `O(idx)` without unfolding
elements. -/
private def mkListMemAtProof (u : Level) (elemTy : Lean.Expr)
    (elems : Array Lean.Expr) (idx : Nat) : Lean.Expr :=
  let rec go (i : Nat) : Lean.Expr :=
    let tailE := mkExprList u elemTy (elems.extract (i + 1) elems.size).toList
    if h : i < idx then
      mkApp5 (Lean.mkConst ``List.mem_cons_of_mem [u]) elemTy elems[i]! elems[idx]! tailE
        (go (i + 1))
    else
      mkApp3 (Lean.mkConst ``List.mem_cons_self [u]) elemTy elems[i]! tailE
  termination_by idx - i
  decreasing_by omega
  go 0

/-- Evaluate `inlineFnsPlan` and reify each post-inline function body to `TFlatFn`. -/
def evalInlSegData (plan : InlPlan) (deps src : List Fn) : List TFlatFn :=
  (inlineFnsPlan plan deps src).map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩

/-- Curried `inline_seg!` evaluator over decoded `TFlatFn` lists. -/
def evalInlSegFlat (plan : InlPlan) (depsFns srcFns : List TFlatFn) : List TFlatFn :=
  evalInlSegData plan (depsFns.map TFlatFn.toFn) (srcFns.map TFlatFn.toFn)

/-! ## 2. `inline_seg!` Command Elaborator -/

private structure InlSegOptions where
  planT? : Option Term := none
  depsT? : Option Term := none
  exportsT? : Option Term := none
  compileT? : Option Term := none
  deriving Inhabited

private def parseInlSegOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM InlSegOptions :=
  parseKvOptions "inline_seg!" "plan, deps, exports, compile" {}
    (fun opts k v => pure <| match k with
      | `plan => some { opts with planT? := some v }
      | `deps => some { opts with depsT? := some v }
      | `exports => some { opts with exportsT? := some v }
      | `compile => some { opts with compileT? := some v }
      | _ => none) optKeys optVals

/-- `inline_seg! segId srcFnsExpr [(plan := ...)] [(deps := ...)] [(exports := ...)]
[(compile := ...)]` materializes a subsystem's plan-inlined functions as `TFlatFn` literals,
proves per-function `rfl` step theorems (no cascading reduction), emits `segId.seg : InlSeg`,
and optionally verifies `segId.exports_sub : ∀ e ∈ exportsExpr, e ∈ segId.fns`. -/
scoped syntax "inline_seg! " ident term:arg ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(inline_seg! $segId $srcFnsT $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let segNm := ns ++ segId.getId
    let opts ← parseInlSegOptions optKeys optVals
    let tys := mkCertTypes
    let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
    let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) flatTy
    let inlPlanTy := Lean.mkConst ``LeanQbe.T.InlPlan
    let (srcFnsE, planE, depsE, exportsE?, compile, tfs) ← liftTermElabM do
      let srcFnsE ← Term.elabTerm srcFnsT (some tys.listFnTy)
      let planE ← elabOptTerm opts.planT? inlPlanTy
        (mkApp (Lean.mkConst ``List.nil [.zero])
          (mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) tys.symTy
            (mkApp (Lean.mkConst ``List [.zero]) tys.symTy)))
      let depsE ← elabOptTerm opts.depsT? tys.listFnTy
        (mkApp (Lean.mkConst ``List.nil [1]) tys.fnTy)
      let exportsE? ← match opts.exportsT? with
        | some t => some <$> Term.elabTerm t (some tys.listFnTy)
        | none => pure none
      let compile ← evalBoolOpt opts.compileT? false
      Term.synthesizeSyntheticMVarsNoPostponing
      let srcFnsE ← instantiateMVars srcFnsE
      let planE ← instantiateMVars planE
      let depsE ← instantiateMVars depsE
      let exportsE? ← exportsE?.mapM instantiateMVars
      let planVal ← unsafe evalExpr InlPlan inlPlanTy planE
      let srcDec? ← decodeFlatSliceExpr srcFnsE
      let depsDec? ← decodeFlatSliceExpr depsE
      let tfs ← match srcDec?, depsDec? with
        | some (srcFlats, _, _), some (depsFlats, _, _) =>
          pure (evalInlSegFlat planVal depsFlats srcFlats)
        | _, _ =>
          let callE := mkApp3 (Lean.mkConst ``LeanQbe.T.evalInlSegData) planE depsE srcFnsE
          unsafe evalExpr (List TFlatFn) listFlatTy callE
      return (srcFnsE, planE, depsE, exportsE?, compile, tfs)
    let (flatConsts, fnConsts) ← liftCoreM <| emitMatFnDefs segNm tfs compile
    let flatFnsNm := segNm ++ `flatFns
    let fnsNm := segNm ++ `fns
    let fnsFlatEqNm := segNm ++ `fns_flat_eq
    let inlEqNm := segNm ++ `inl_eq
    liftCoreM do
      addCertDef flatFnsNm listFlatTy (mkListLit .zero flatTy flatConsts) compile
      addCertDef fnsNm tys.listFnTy (mkListLit .one tys.fnTy fnConsts) compile
      let mapFlatE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
        flatTy tys.fnTy (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) (Lean.mkConst flatFnsNm)
      addKernelEqThm fnsFlatEqNm tys.listFnTy (Lean.mkConst fnsNm) mapFlatE .one
    let rhsFull := mkApp3 (Lean.mkConst ``LeanQbe.T.inlineFnsPlan) planE depsE srcFnsE
    let srcElems? ← liftTermElabM <| tryPeelListElems srcFnsE
    match srcElems? with
    | some srcArr =>
      if srcArr.size != fnConsts.length then
        throwError "inline_seg!: peeled srcFns length {srcArr.size} != output {fnConsts.length}"
      let fnArr := fnConsts.toArray
      let mut stepNms : Array Name := #[]
      let mut candsE := depsE
      for i in [:srcArr.size] do
        let sE := srcArr[i]!
        let fnOutE := fnArr[i]!
        let csE := mkApp3 (Lean.mkConst ``LeanQbe.T.selectPlanCands) planE candsE
          (mkApp (Lean.mkConst ``LeanQbe.T.Fn.name) sE)
        let rhsStep := mkApp (Lean.mkConst ``LeanQbe.T.Fn.renorm)
          (mkApp2 (Lean.mkConst ``LeanQbe.T.Fn.inline) csE sE)
        let stNm := segNm ++ `step ++ Name.mkSimple s!"f{i}"
        liftCoreM <| addKernelEqThm stNm tys.fnTy fnOutE rhsStep .one
        stepNms := stepNms.push stNm
        candsE := mkApp3 (Lean.mkConst ``List.cons [1]) tys.fnTy fnOutE candsE
      let mut candsPrefix : Array Lean.Expr := #[depsE]
      for i in [:srcArr.size] do
        candsPrefix := candsPrefix.push
          (mkApp3 (Lean.mkConst ``List.cons [1]) tys.fnTy fnArr[i]! candsPrefix[i]!)
      let nilFnE := mkApp (Lean.mkConst ``List.nil [1]) tys.fnTy
      let mut restProof := mkApp2 (Lean.mkConst ``Eq.refl [2]) tys.listFnTy nilFnE
      let mut restSrcE := nilFnE
      let mut restOutE := nilFnE
      for revIdx in [:srcArr.size] do
        let i := srcArr.size - 1 - revIdx
        let sE := srcArr[i]!
        let fnOutE := fnArr[i]!
        restProof := mkAppN (Lean.mkConst ``LeanQbe.T.inlineFnsPlan_cons_eq)
          #[planE, candsPrefix[i]!, sE, fnOutE, restSrcE, restOutE,
            Lean.mkConst stepNms[i]!, restProof]
        restSrcE := mkApp3 (Lean.mkConst ``List.cons [1]) tys.fnTy sE restSrcE
        restOutE := mkApp3 (Lean.mkConst ``List.cons [1]) tys.fnTy fnOutE restOutE
      let inlEqTy := mkApp3 (Lean.mkConst ``Eq [2]) tys.listFnTy (Lean.mkConst fnsNm) rhsFull
      liftCoreM <| addCertThm inlEqNm inlEqTy restProof
    | none =>
      liftCoreM <| addKernelEqThm inlEqNm tys.listFnTy (Lean.mkConst fnsNm) rhsFull .one
    let segDefNm := segNm ++ `seg
    let segVal := mkAppN (Lean.mkConst ``LeanQbe.T.InlSeg.mk)
      #[srcFnsE, planE, depsE, Lean.mkConst flatFnsNm, Lean.mkConst fnsNm,
        Lean.mkConst fnsFlatEqNm, Lean.mkConst inlEqNm]
    liftCoreM <| addCertDef segDefNm (Lean.mkConst ``LeanQbe.T.InlSeg) segVal compile
    if let some expE := exportsE? then
      let some expElems ← liftTermElabM (tryPeelListElems expE)
        | throwError "inline_seg!: exports must be a concrete list of exported Fn constants"
      let fnArr := fnConsts.toArray
      let tfArr := tfs.toArray
      let mut expProofs : Array (Lean.Expr × Lean.Expr) := #[]
      for j in [:expElems.size] do
        let eExpr := expElems[j]!
        let eNm ← liftTermElabM do
          match ← decodeFlatSliceExpr (mkExprList 1 tys.fnTy [eExpr]) with
          | some ([tf], _, _) => pure tf.name
          | _ =>
            let nmE := mkApp (Lean.mkConst ``LeanQbe.T.Fn.name) eExpr
            unsafe evalExpr Sym tys.symTy nmE
        let some idx := tfArr.findIdx? (fun tf => tf.name == eNm)
          | throwError "inline_seg!: exported fn '{eNm}' not found in segment '{segNm}'"
        let eqNm := segNm ++ `exp_eq ++ Name.mkSimple s!"e{j}"
        liftCoreM <| addKernelEqThm eqNm tys.fnTy eExpr fnArr[idx]! .one
        let memAt := mkListMemAtProof 1 tys.fnTy fnArr idx
        let memPf := mkAppN (Lean.mkConst ``LeanQbe.T.InlSeg.mem_of_eq_mem [1])
          #[tys.fnTy, eExpr, fnArr[idx]!, Lean.mkConst fnsNm, Lean.mkConst eqNm, memAt]
        expProofs := expProofs.push (eExpr, memPf)
      let (predE, subTy) ← liftTermElabM do
        let predE ← withLocalDeclD `e tys.fnTy fun e => do
          mkLambdaFVars #[e] (← mkAppM ``Membership.mem #[Lean.mkConst fnsNm, e])
        let subTy ← withLocalDeclD `e tys.fnTy fun e => do
          let hIn ← mkAppM ``Membership.mem #[expE, e]
          let hOut ← mkAppM ``Membership.mem #[Lean.mkConst fnsNm, e]
          mkForallFVars #[e] (Lean.mkForall `_ .default hIn hOut)
        return (← instantiateMVars predE, ← instantiateMVars subTy)
      let mut subPf := mkApp2 (Lean.mkConst ``LeanQbe.T.InlSeg.forall_mem_nil [1]) tys.fnTy predE
      let mut tailE := mkApp (Lean.mkConst ``List.nil [1]) tys.fnTy
      for revIdx in [:expProofs.size] do
        let j := expProofs.size - 1 - revIdx
        let (eExpr, memPf) := expProofs[j]!
        subPf := mkAppN (Lean.mkConst ``LeanQbe.T.InlSeg.forall_mem_cons [1])
          #[tys.fnTy, predE, eExpr, tailE, memPf, subPf]
        tailE := mkApp3 (Lean.mkConst ``List.cons [1]) tys.fnTy eExpr tailE
      liftCoreM <| addCertThm (segNm ++ `exports_sub) subTy subPf

/-! ## 3. `seg_cert!` & `fn_cert!` Command Elaborators (Oracle Hints, Zero `Spill`) -/

private structure SegCertOptions where
  base : CertOptions := {}
  hintsT? : Option Term := none
  chunkSizeT? : Option Term := none
  excludeT? : Option Term := none
  stagedT? : Option Term := none
  deriving Inhabited

private def parseSegCertOptions (cmd : String)
    (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM SegCertOptions :=
  parseKvOptions cmd
    "hints, ext, exits, nX, maxBound, maxDirs, chunkSize, pruneExt, exclude, compile, staged" {}
    (fun opts k v => pure <| match k with
      | `hints => some { opts with hintsT? := some v }
      | `chunkSize => some { opts with chunkSizeT? := some v }
      | `exclude => some { opts with excludeT? := some v }
      | `staged => some { opts with stagedT? := some v }
      | `maxBound => some { opts with base := { opts.base with maxBT? := some v } }
      | `ext => some { opts with base := { opts.base with extT? := some v } }
      | `exits => some { opts with base := { opts.base with exitsT? := some v } }
      | `nX => some { opts with base := { opts.base with nXT? := some v } }
      | `maxDirs => some { opts with base := { opts.base with maxDirsT? := some v } }
      | `pruneExt => some { opts with base := { opts.base with pruneExtT? := some v } }
      | `compile => some { opts with base := { opts.base with compileT? := some v } }
      | _ => none) optKeys optVals

private def evalOptBoolOpt (opt? : Option Term) : TermElabM (Option Bool) := do
  match opt? with
  | none => pure none
  | some t => some <$> evalBoolOpt (some t) false

private def runStagedFnEval (cmd : String) (b : CertBaseEnv) (pruneExt : Bool)
    (hintsE : Lean.Expr) (flatFns : List TFlatFn) : TermElabM EvalStagedFnData := do
  let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.TFlatFn)
  let pruneExtE := Lean.mkConst (if pruneExt then ``Bool.true else ``Bool.false)
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String)
    (Lean.mkConst ``LeanQbe.T.EvalStagedFnData)
  let runnerTy := Lean.mkForall `_ .default listFlatTy outTy
  let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.makeStagedFnEvaluator)
    #[b.isaE, b.ltE, b.raE, b.ext0E, b.exitsE, b.nXE, b.maxBE, pruneExtE, hintsE,
      b.toExprHintsInst, b.toExprDirInst])
  let runner ← unsafe evalExpr (List TFlatFn → Except String EvalStagedFnData) runnerTy callE
  match runner flatFns with
  | .error e => throwError "{cmd}: {e}"
  | .ok sd => return sd

private def emitSegChunksFromRun (segNm auxNs : Name) (b : CertBaseEnv)
    (runFnsE flatBaseE : Lean.Expr) (fnsFlatEqNm : Name)
    (run : EvalSegRun) : CommandElabM Unit := do
  let tys := mkCertTypes
  let flatCtx := some (runFnsE, flatBaseE, fnsFlatEqNm)
  let mut chunkNames : Array AcycChunkNames := #[]
  let mut ci : Nat := 0
  for ch in run.data.chunks do
    chunkNames := chunkNames.push
      (← emitAcycChunkDefs auxNs s!"c{ci}" b.compileCert runFnsE b.listHintsTy b.listDirTy ch
        (some flatBaseE))
    ci := ci + 1
  for ac in chunkNames do liftCoreM <| emitAcycChunkThms b ac flatCtx
  let mut chunkEntries : List Lean.Expr := []
  for ac in chunkNames do
    chunkEntries := chunkEntries ++ [← liftCoreM <| emitAcycCompiledChunk b ac]
  let chunkTy := mkAppN (Lean.mkConst ``LeanQbe.T.CompiledChunk)
    #[b.targE, b.ltE, b.exitsE, b.nXE]
  let chunksNm := auxNs ++ `chunks
  liftCoreM <| addCertDef chunksNm (mkApp (Lean.mkConst ``List [1]) chunkTy)
    (mkExprList 1 chunkTy chunkEntries) b.compileCert
  let fnsEqNm := auxNs ++ `fns_eq
  let maxBLeNm := auxNs ++ `maxBound_le
  let chunksFnsE := mkAppN (Lean.mkConst ``LeanQbe.T.chunksFns)
    #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst chunksNm]
  let mut fnsEqProof : Lean.Expr := default
  let mut restFnsE := mkApp (Lean.mkConst ``List.nil [1]) tys.fnTy
  let mut maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_nil)
    #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE]
  let mut restChunksE := mkApp (Lean.mkConst ``List.nil [1]) chunkTy
  let nChunks := chunkNames.size
  for revIdx in [:nChunks] do
    let i := nChunks - 1 - revIdx
    let ac := chunkNames[i]!
    let chunkVal := chunkEntries[i]!
    fnsEqProof := if revIdx == 0 then
      mkApp3 (Lean.mkConst ``LeanQbe.T.slice_last_eq [1]) tys.fnTy runFnsE (mkNatLit ac.startIdx)
    else mkApp6 (Lean.mkConst ``LeanQbe.T.slice_cons_eq [1])
      tys.fnTy runFnsE restFnsE (mkNatLit ac.startIdx) (mkNatLit ac.fnCount) fnsEqProof
    maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_cons)
      #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE, chunkVal, restChunksE,
        mkApp (Lean.mkConst ``Nat.le_refl) b.maxBE, maxBProof]
    restFnsE := mkApp3 (Lean.mkConst ``List.append [1]) tys.fnTy (Lean.mkConst ac.fnsNm) restFnsE
    restChunksE := mkApp3 (Lean.mkConst ``List.cons [1]) chunkTy chunkVal restChunksE
  liftCoreM <| addCertThm fnsEqNm
    (mkApp3 (Lean.mkConst ``Eq [2]) tys.listFnTy runFnsE chunksFnsE) fnsEqProof
  let maxBLeProp ← liftTermElabM do
    let lhs := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound)
      #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst chunksNm]
    instantiateMVars (← mkAppM ``LE.le #[lhs, b.maxBE])
  liftCoreM do
    addCertThm maxBLeNm maxBLeProp maxBProof
    let segTy := mkAppN (Lean.mkConst ``LeanQbe.T.SegChunks)
      #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE]
    let segVal := mkAppN (Lean.mkConst ``LeanQbe.T.SegChunks.mk)
      #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE,
        runFnsE, Lean.mkConst chunksNm, Lean.mkConst fnsEqNm, Lean.mkConst maxBLeNm]
    addCertDef segNm segTy segVal b.compileCert

/-- `seg_cert! segCertId target layout legalTarget labelClean fnsExpr (hints := ...)
[(ext := ...)] [(exits := ...)] [(nX := ...)] [(maxBound := ...)] [(maxDirs := ...)]
[(chunkSize := 1)] [(pruneExt := true)] [(exclude := [...])] [(compile := false)]` compiles
materialized `fnsExpr` with oracle `hints` and `ext` via `compileModuleFlat`, emitting
`segCertId : SegChunks ...` (or `segCertId.part0`, `part1`, ... around excluded heavy fns). -/
scoped syntax "seg_cert! " ident
    term:arg term:arg term:arg term:arg term:arg ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(seg_cert! $certId $targT $layoutT $ltT $clT $fnsT $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let certNm := ns ++ certId.getId
    let opts ← parseSegCertOptions "seg_cert!" optKeys optVals
    let some hintsT := opts.hintsT?
      | throwError "seg_cert!: required option `(hints := ...)` missing"
    let tys := mkCertTypes
    let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
    let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) flatTy
    let (b, fnsBaseE, flatListE, pf, evalRes) ← liftTermElabM do
      let b ← elabCertBase targT layoutT ltT clT opts.base
      let pruneExt ← evalBoolOpt opts.base.pruneExtT? true
      let stagedOpt ← evalOptBoolOpt opts.stagedT?
      let chunkSize ← match opts.chunkSizeT? with
        | none => pure 1
        | some t =>
          let e ← Term.elabTerm t (some tys.natTy)
          Term.synthesizeSyntheticMVarsNoPostponing
          unsafe evalExpr Nat tys.natTy (← instantiateMVars e)
      let exclE ← elabOptTerm opts.excludeT?
        (mkApp (Lean.mkConst ``List [.zero]) tys.symTy)
        (mkApp (Lean.mkConst ``List.nil [.zero]) tys.symTy)
      let exclNames ← unsafe evalExpr (List Sym)
        (mkApp (Lean.mkConst ``List [.zero]) tys.symTy) (← instantiateMVars exclE)
      let hintsE ← instantiateMVars (← Term.elabTerm hintsT (some b.listHintsTy))
      let fnsE ← instantiateMVars (← Term.elabTerm fnsT (some tys.listFnTy))
      Term.synthesizeSyntheticMVarsNoPostponing
      let some (flatFns, flatListE, pf) ← decodeFlatSliceExpr fnsE
        | throwError "seg_cert!: fnsExpr must be a materialized TFlatFn/denoteFunc list"
      if !exclNames.isEmpty && stagedOpt == some true then
        throwError "seg_cert!: (staged := true) requires an unexcluded single-function segment"
      let useStaged := match flatFns with
        | [f] => exclNames.isEmpty && stagedOpt.getD (tflatSize f.body >= 800)
        | _ => false
      if !useStaged && stagedOpt == some true then
        throwError "seg_cert!: (staged := true) requires a single-function segment"
      if useStaged then
        let sd ← runStagedFnEval "seg_cert!" b pruneExt hintsE flatFns
        return (b, fnsE, flatListE, pf, Sum.inr sd)
      let pruneExtE := Lean.mkConst (if pruneExt then ``Bool.true else ``Bool.false)
      let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String)
        (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.EvalSegRun))
      let runnerTy := Lean.mkForall `_ .default listFlatTy outTy
      let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.makeSegCertEvaluator)
        #[b.isaE, b.ltE, b.raE, b.ext0E, b.exitsE, b.nXE, mkNatLit chunkSize, b.maxBE,
          b.maxDirsE, pruneExtE, exclE, hintsE, b.toExprHintsInst, b.toExprDirInst])
      let runner ← unsafe evalExpr (List TFlatFn → Except String (List EvalSegRun)) runnerTy callE
      match runner flatFns with
      | .error e => throwError "seg_cert!: {e}"
      | .ok runs => return (b, fnsE, flatListE, pf, Sum.inl (runs, !exclNames.isEmpty))
    let auxRoot := certNm ++ `aux
    let flatFnsNm := auxRoot ++ `flatFns
    let fnsFlatEqNm := auxRoot ++ `fns_flat_eq
    let flatFnsConstE := Lean.mkConst flatFnsNm
    let rhsE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
      flatTy tys.fnTy (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) flatFnsConstE
    let eqTy := mkApp3 (Lean.mkConst ``Eq [2]) tys.listFnTy fnsBaseE rhsE
    liftCoreM do
      addCertDef flatFnsNm listFlatTy flatListE false
      addCertThm fnsFlatEqNm eqTy pf
    match evalRes with
    | .inr sd =>
      emitStagedSegChunks certNm auxRoot b fnsBaseE flatFnsConstE fnsFlatEqNm
        (flatListE.getArg! 1) sd
    | .inl (runs, hasExcl) =>
      if !hasExcl then
        let some run := runs.head?
          | throwError "seg_cert!: internal error (empty run list)"
        emitSegChunksFromRun certNm auxRoot b fnsBaseE flatFnsConstE fnsFlatEqNm run
      else
        let mut pi : Nat := 0
        for run in runs do
          let pNm := certNm ++ Name.mkSimple s!"part{pi}"
          let pAux := pNm ++ `aux
          let pFnsNm := pAux ++ `runFns
          let pFlatNm := pAux ++ `runFlat
          let pEqNm := pAux ++ `run_flat_eq
          let sliceFnsE := mkSliceExpr tys.fnTy fnsBaseE run.startIdx run.fnCount false 1
          let sliceFlatE := mkSliceExpr flatTy flatFnsConstE run.startIdx run.fnCount false .zero
          let sliceEqPf := mkAppN (Lean.mkConst ``LeanQbe.T.map_slice_eq [.zero, .one])
            #[flatTy, tys.fnTy, Lean.mkConst ``LeanQbe.T.TFlatFn.toFn, fnsBaseE, flatFnsConstE,
              Lean.mkConst fnsFlatEqNm, mkNatLit run.startIdx, mkNatLit run.fnCount]
          let pEqTy := mkApp3 (Lean.mkConst ``Eq [2]) tys.listFnTy (Lean.mkConst pFnsNm)
            (mkApp4 (Lean.mkConst ``List.map [.zero, .one]) flatTy tys.fnTy
              (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) (Lean.mkConst pFlatNm))
          liftCoreM do
            addCertDef pFnsNm tys.listFnTy sliceFnsE b.compileCert
            addCertDef pFlatNm listFlatTy sliceFlatE false
            addCertThm pEqNm pEqTy sliceEqPf
          emitSegChunksFromRun pNm pAux b (Lean.mkConst pFnsNm) (Lean.mkConst pFlatNm) pEqNm run
          pi := pi + 1

/-- `fn_cert! fnCertId target layout legalTarget labelClean flatFnExpr (hints := hintExpr)
[(ext := ...)] [(exits := ...)] [(nX := ...)] [(maxBound := ...)] [(pruneExt := true)]
[(compile := false)] [(staged := auto)]` compiles a single isolated heavy `TFlatFn` using oracle
`hintExpr` and `ext`, emitting `fnCertId : SegChunks ...` covering `[flatFnExpr.toFn]`. Uses
staged per-pass `TFlat` kernel equalities automatically when `tflatSize ≥ 800` or
`(staged := true)`. -/
scoped syntax "fn_cert! " ident
    term:arg term:arg term:arg term:arg term:arg ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(fn_cert! $certId $targT $layoutT $ltT $clT $flatFnT $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let certNm := ns ++ certId.getId
    let auxNs := certNm ++ `aux
    let opts ← parseSegCertOptions "fn_cert!" optKeys optVals
    let some hintT := opts.hintsT?
      | throwError "fn_cert!: required option `(hints := ...)` missing"
    let tys := mkCertTypes
    let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
    let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) flatTy
    let (b, flatFnE, evalRes) ← liftTermElabM do
      let b ← elabCertBase targT layoutT ltT clT opts.base
      let pruneExt ← evalBoolOpt opts.base.pruneExtT? true
      let stagedOpt ← evalOptBoolOpt opts.stagedT?
      let hintTy := mkApp (Lean.mkConst ``LeanQbe.T.Isa.Hints) b.isaE
      let hintE ← instantiateMVars (← Term.elabTerm hintT (some hintTy))
      let flatFnE ← instantiateMVars (← Term.elabTerm flatFnT (some flatTy))
      Term.synthesizeSyntheticMVarsNoPostponing
      let singleFnE := mkExprList 1 tys.fnTy
        [mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) flatFnE]
      let some (flatFns, _, _) ← decodeFlatSliceExpr singleFnE
        | throwError "fn_cert!: flatFnExpr must decode to a concrete TFlatFn literal"
      let [f] := flatFns
        | throwError "fn_cert!: expected singleton TFlatFn"
      let useStaged := stagedOpt.getD (tflatSize f.body >= 800)
      if useStaged then
        let hintsE := mkExprList .zero hintTy [hintE]
        let sd ← runStagedFnEval "fn_cert!" b pruneExt hintsE flatFns
        return (b, flatFnE, Sum.inr sd)
      let pruneExtE := Lean.mkConst (if pruneExt then ``Bool.true else ``Bool.false)
      let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String)
        (Lean.mkConst ``LeanQbe.T.EvalModuleData)
      let runnerTy := Lean.mkForall `_ .default listFlatTy outTy
      let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.makeFnCertEvaluator)
        #[b.isaE, b.ltE, b.raE, b.ext0E, b.exitsE, b.nXE, b.maxBE, pruneExtE, hintE,
          b.toExprHintsInst, b.toExprDirInst])
      let runner ← unsafe evalExpr (List TFlatFn → Except String EvalModuleData) runnerTy callE
      match runner flatFns with
      | .error e => throwError "fn_cert!: {e}"
      | .ok md => return (b, flatFnE, Sum.inl md)
    let fnSingletonE := mkExprList 1 tys.fnTy
      [mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) flatFnE]
    let flatSingletonE := mkExprList .zero flatTy [flatFnE]
    let flatFnsNm := auxNs ++ `flatFns
    let fnsFlatEqNm := auxNs ++ `fns_flat_eq
    let rhsE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
      flatTy tys.fnTy (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) (Lean.mkConst flatFnsNm)
    liftCoreM do
      addCertDef flatFnsNm listFlatTy flatSingletonE false
      addKernelEqThm fnsFlatEqNm tys.listFnTy fnSingletonE rhsE .one
    match evalRes with
    | .inr sd =>
      emitStagedSegChunks certNm auxNs b fnSingletonE (Lean.mkConst flatFnsNm) fnsFlatEqNm
        flatFnE sd
    | .inl md =>
      let run : EvalSegRun := { startIdx := 0, fnCount := 1, isLastFull := true, data := md }
      emitSegChunksFromRun certNm auxNs b fnSingletonE (Lean.mkConst flatFnsNm) fnsFlatEqNm run

end

end LeanQbe.T
