/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertFlat
public meta import Lean
public meta import LeanQbe.T.MainCertSeg
public meta import LeanQbe.T.MainCertFlat
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainFlat
public meta import LeanQbe.T.MainCertInline

/-!
# Staged Per-Pass Kernel Certificate Elaborator (`MainCertSegStaged`)

ISA-generic meta evaluator and kernel equality emitter splitting single-function
`compileModuleFlat` verification across `15` per-pass `TFlat` literal equalities (`earlyOptFlat_eq`,
`midStageFlat_eq`, `compileModuleFlat_single`) so heavy functions (`≥ 800` IR nodes) verify
within default kernel heartbeats and `< 10 GiB` RSS with zero `.olean` bloat (intermediate literals
use `mkPrivateName` + `forceExpose := false`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

meta section

open Lean Elab Command Meta
open InlineMeta

/-- Pre-evaluated per-pass literal expressions for staged single-function `SegChunks` emission. -/
structure EvalStagedFnData where
  md : EvalModuleData
  e0Lit : Lean.Expr
  e1Lit : Lean.Expr
  tflatTyE : Lean.Expr
  tflatTyMidE : Lean.Expr
  mLits : Array (String × Lean.Expr)
  extCtorLit : Lean.Expr
  bndNat : Nat
  deriving Inhabited

/-- Evaluate a single `TFlatFn` with oracle hint `h` across all `earlyOptFlat` and `midStageFlat`
pass boundaries, returning `EvalStagedFnData` for staged kernel verification. -/
def makeStagedFnEvaluator (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (pruneExt : Bool) (hs : List I.Hints)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    List TFlatFn → Except String EvalStagedFnData :=
  fun fs => do
    let [f] := fs
      | throw s!"staged fn cert: expected singleton TFlatFn list, got {fs.length}"
    let [h] := hs
      | throw s!"staged fn cert: expected singleton hints list, got {hs.length}"
    if !f.wfCheck then throw s!"{f.name}: flat wfCheck failed"
    let e0 := OptFlatValue.foldFlat f.as (OptFlatValue.copyFlat f.as
      (OptFlatValue.gvnFlat f.as (OptFlatValue.copyFlat f.as
        (OptFlatValue.canonFlat f.as (OptFlatValue.foldFlat f.as f.body)))))
    let e1 := OptFlatCfg.dcePFlat f.as (OptFlatValue.foldFlat f.as (OptFlatValue.copyFlat f.as
      (TFlat.zeroPeelWith { peelBudget := 24 }
        (peelFastFlat f.as (simplifyGroupFastFlat f.as
          (OptFlatCfg.ifOptFlat false f.as e0)) 24))))
    let ef : TFlatFn := ⟨f.name, f.as, f.rs, e1⟩
    if !ef.supportsSource lt then throw s!"{f.name}: unsupported source op for target"
    let as' := lt.legalSig ef.as
    let rs' := lt.legalSig ef.rs
    let m0 := legalFlat lt (as := ef.as) ef.body
    let m1 := OptFlatValue.copyFlat as' (OptFlatMem.divConstFlat as'
      (OptFlatValue.canonFlat as' (OptFlatValue.foldFlat as' m0)))
    let m2a := OptFlatMem.memLoadFlat as' m1
    let m2b := OptFlatValue.gvnFlat as' m2a
    let m2 := OptFlatValue.foldFlat as' (OptFlatMem.assumeBitsFlat as' m2b)
    let m3a := OptFlatValue.foldFlat as' (assumeElimFlat (OptFlatCfg.deadLoadElimFlat as'
      (simplifyGroupFastFlat as' (OptFlatCfg.ifOptFlat true as' m2))))
    let m3b := addrRangeOptFlatWith lt.foldAddrDisp as' m3a
    let m3 := OptFlatValue.gvnFlat as' m3b
    let m4a := OptFlatCfg.dcePFlat as' (licmFlat as' m3)
    let m4 := loopRotateFlat as' m4a
    let m5a := pathCondOptFlat as' m4
    let m5b := condThreadPassFlat as' m5a
    let m5 := mergeRetsFlat (tailDupFlat as' (OptFlatCfg.dcePFlat as'
      (OptFlatValue.foldFlat as' m5b)) {})
    let mf : TFlatFn := ⟨ef.name, as', rs', m5⟩
    let ext := TFlat.ext mf.body
    let code ← match Rega.lowerFlatFn I h ext mf with
      | .ok c => .ok c
      | .error e => .error s!"{f.name}: {e}"
    let bnd ← evalOneFnBoundCheck I raBytes exits nX maxBound ext0 f.name h ext
    let md ← evalLinkedChunksCore I raBytes ext0 exits nX 1 maxBound 0 pruneExt
      [(f.name, h, code, ext, mf.sig)]
    let tflatTyE := mkApp (Lean.mkConst ``LeanQbe.T.TFlat) (listTyToExpr f.rs)
    let tflatTyMidE := mkApp (Lean.mkConst ``LeanQbe.T.TFlat) (listTyToExpr rs')
    let mkM (lbl : String) (v : TFlat rs') : String × Lean.Expr :=
      (lbl, tflatToExpr rs' v)
    let mLits := #[
      mkM "m0" m0, mkM "m1" m1, mkM "m2a" m2a, mkM "m2b" m2b, mkM "m2" m2,
      mkM "m3a" m3a, mkM "m3b" m3b, mkM "m3" m3, mkM "m4a" m4a, mkM "m4" m4,
      mkM "m5a" m5a, mkM "m5b" m5b, mkM "m5" m5
    ]
    let extCtorLit := mkApp2 (Lean.mkConst ``LeanQbe.T.Rega.Ext.mk)
      (listSigToExpr ext.callees) (listSymToExpr ext.exits)
    return {
      md, e0Lit := tflatToExpr f.rs e0, e1Lit := tflatToExpr f.rs e1,
      tflatTyE, tflatTyMidE, mLits, extCtorLit, bndNat := bnd
    }

private def addPrivDef (declNm : Name) (ty val : Lean.Expr) : CoreM Name :=
  withCurrHeartbeats do
    let pnm := Lean.mkPrivateName (← getEnv) declNm
    let decl := Declaration.defnDecl {
      name := pnm, levelParams := [], type := ty, value := val,
      hints := .abbrev, safety := .safe }
    addDecl decl
    modifyEnv (Lean.addNoncomputable · pnm)
    return pnm

private def addPrivEq (declNm : Name) (eqTy lhs rhs : Lean.Expr) : CoreM Name := do
  let pnm := Lean.mkPrivateName (← getEnv) declNm
  addKernelEqThm pnm eqTy lhs rhs .zero
  return pnm

private def addPrivThm (declNm : Name) (ty val : Lean.Expr) : CoreM Name := do
  let pnm := Lean.mkPrivateName (← getEnv) declNm
  addCertThm pnm ty val
  return pnm

private def appF (fn : Name) (asArg rsArg x : Lean.Expr) : Lean.Expr :=
  mkApp3 (Lean.mkConst fn) asArg rsArg x

private def emitEarlyThms (auxNs : Name) (f0C : Lean.Expr) (sd : EvalStagedFnData) :
    CoreM (Lean.Expr × Name) := do
  let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
  let e0Nm ← addPrivDef (auxNs ++ `s_e0) sd.tflatTyE sd.e0Lit
  let e1Nm ← addPrivDef (auxNs ++ `s_e1) sd.tflatTyE sd.e1Lit
  let fAsE := mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.as) f0C
  let fRsE := mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.rs) f0C
  let fBodyE := mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.body) f0C
  let efVal := mkApp4 (Lean.mkConst ``LeanQbe.T.TFlatFn.mk)
    (mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.name) f0C) fAsE fRsE (Lean.mkConst e1Nm)
  let efNm ← addPrivDef (auxNs ++ `s_ef) flatTy efVal
  let efC := Lean.mkConst efNm
  let e0Lhs := appF ``LeanQbe.T.OptFlatValue.foldFlat fAsE fRsE
    (appF ``LeanQbe.T.OptFlatValue.copyFlat fAsE fRsE
      (appF ``LeanQbe.T.OptFlatValue.gvnFlat fAsE fRsE
        (appF ``LeanQbe.T.OptFlatValue.copyFlat fAsE fRsE
          (appF ``LeanQbe.T.OptFlatValue.canonFlat fAsE fRsE
            (appF ``LeanQbe.T.OptFlatValue.foldFlat fAsE fRsE fBodyE)))))
  let hE0 ← addPrivEq (auxNs ++ `h_e0) sd.tflatTyE e0Lhs (Lean.mkConst e0Nm)
  let e1Lhs := appF ``LeanQbe.T.OptFlatCfg.dcePFlat fAsE fRsE
    (appF ``LeanQbe.T.OptFlatValue.foldFlat fAsE fRsE
      (appF ``LeanQbe.T.OptFlatValue.copyFlat fAsE fRsE
        (mkApp3 (Lean.mkConst ``LeanQbe.T.TFlat.zeroPeelWith)
          (Lean.mkConst ``LeanQbe.T.stagedZpCfg24) fRsE
          (mkApp4 (Lean.mkConst ``LeanQbe.T.peelFastFlat) fAsE fRsE
            (appF ``LeanQbe.T.simplifyGroupFastFlat fAsE fRsE
              (mkApp4 (Lean.mkConst ``LeanQbe.T.OptFlatCfg.ifOptFlat)
                (Lean.mkConst ``Bool.false) fAsE fRsE (Lean.mkConst e0Nm)))
            (mkNatLit 24)))))
  let hE1 ← addPrivEq (auxNs ++ `h_e1) sd.tflatTyE e1Lhs (Lean.mkConst e1Nm)
  let pf := mkAppN (Lean.mkConst ``LeanQbe.T.earlyOptFlat_eq)
    #[f0C, Lean.mkConst e0Nm, Lean.mkConst e1Nm, Lean.mkConst hE0, Lean.mkConst hE1]
  let ty := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) flatTy
    (mkApp (Lean.mkConst ``LeanQbe.T.earlyOptFlat) f0C) efC
  let hEfNm ← addPrivThm (auxNs ++ `h_ef) ty pf
  return (efC, hEfNm)

private def emitMidThms (auxNs : Name) (ltE efC : Lean.Expr) (sd : EvalStagedFnData) :
    CoreM (Lean.Expr × Name) := do
  let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
  let mut mNms : Array Name := #[]
  for (lbl, lit) in sd.mLits do
    mNms := mNms.push (← addPrivDef (auxNs ++ Name.mkSimple s!"s_{lbl}") sd.tflatTyMidE lit)
  let #[m0Nm, m1Nm, m2aNm, m2bNm, m2Nm, m3aNm, m3bNm, m3Nm,
        m4aNm, m4Nm, m5aNm, m5bNm, m5Nm] := mNms
    | throwError "emitMidThms: expected 13 mid-stage pass literals"
  let efAsE := mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.as) efC
  let efRsE := mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.rs) efC
  let efBodyE := mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.body) efC
  let lAsE := mkApp2 (Lean.mkConst ``LeanQbe.T.LegalTarget.legalSig) ltE efAsE
  let lRsE := mkApp2 (Lean.mkConst ``LeanQbe.T.LegalTarget.legalSig) ltE efRsE
  let mfVal := mkApp4 (Lean.mkConst ``LeanQbe.T.TFlatFn.mk)
    (mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.name) efC) lAsE lRsE (Lean.mkConst m5Nm)
  let mfNm ← addPrivDef (auxNs ++ `s_mf) flatTy mfVal
  let mfC := Lean.mkConst mfNm
  let mkEq (s : String) (lhs : Lean.Expr) (rhsNm : Name) :=
    addPrivEq (auxNs ++ Name.mkSimple s) sd.tflatTyMidE lhs (Lean.mkConst rhsNm)
  let hM0 ← mkEq "h_m0"
    (mkApp4 (Lean.mkConst ``LeanQbe.T.legalFlat) ltE efAsE efRsE efBodyE) m0Nm
  let hM1 ← mkEq "h_m1" (appF ``LeanQbe.T.OptFlatValue.copyFlat lAsE lRsE
    (appF ``LeanQbe.T.OptFlatMem.divConstFlat lAsE lRsE
      (appF ``LeanQbe.T.OptFlatValue.canonFlat lAsE lRsE
        (appF ``LeanQbe.T.OptFlatValue.foldFlat lAsE lRsE (Lean.mkConst m0Nm))))) m1Nm
  let hM2a ← mkEq "h_m2a"
    (appF ``LeanQbe.T.OptFlatMem.memLoadFlat lAsE lRsE (Lean.mkConst m1Nm)) m2aNm
  let hM2b ← mkEq "h_m2b"
    (appF ``LeanQbe.T.OptFlatValue.gvnFlat lAsE lRsE (Lean.mkConst m2aNm)) m2bNm
  let hM2 ← mkEq "h_m2" (appF ``LeanQbe.T.OptFlatValue.foldFlat lAsE lRsE
    (appF ``LeanQbe.T.OptFlatMem.assumeBitsFlat lAsE lRsE (Lean.mkConst m2bNm))) m2Nm
  let hM3a ← mkEq "h_m3a" (appF ``LeanQbe.T.OptFlatValue.foldFlat lAsE lRsE
    (mkApp2 (Lean.mkConst ``LeanQbe.T.assumeElimFlat) lRsE
      (appF ``LeanQbe.T.OptFlatCfg.deadLoadElimFlat lAsE lRsE
        (appF ``LeanQbe.T.simplifyGroupFastFlat lAsE lRsE
          (mkApp4 (Lean.mkConst ``LeanQbe.T.OptFlatCfg.ifOptFlat)
            (Lean.mkConst ``Bool.true) lAsE lRsE (Lean.mkConst m2Nm)))))) m3aNm
  let hM3b ← mkEq "h_m3b" (mkApp4 (Lean.mkConst ``LeanQbe.T.addrRangeOptFlatWith)
    (mkApp (Lean.mkConst ``LeanQbe.T.LegalTarget.foldAddrDisp) ltE) lAsE lRsE
    (Lean.mkConst m3aNm)) m3bNm
  let hM3 ← mkEq "h_m3"
    (appF ``LeanQbe.T.OptFlatValue.gvnFlat lAsE lRsE (Lean.mkConst m3bNm)) m3Nm
  let hM4a ← mkEq "h_m4a" (appF ``LeanQbe.T.OptFlatCfg.dcePFlat lAsE lRsE
    (appF ``LeanQbe.T.licmFlat lAsE lRsE (Lean.mkConst m3Nm))) m4aNm
  let hM4 ← mkEq "h_m4" (mkApp4 (Lean.mkConst ``LeanQbe.T.loopRotateFlat) lAsE lRsE
    (Lean.mkConst m4aNm) (Lean.mkConst ``LeanQbe.T.LoopRotate.defaultRotConfig)) m4Nm
  let hM5a ← mkEq "h_m5a"
    (appF ``LeanQbe.T.pathCondOptFlat lAsE lRsE (Lean.mkConst m4Nm)) m5aNm
  let hM5b ← mkEq "h_m5b"
    (appF ``LeanQbe.T.condThreadPassFlat lAsE lRsE (Lean.mkConst m5aNm)) m5bNm
  let hM5 ← mkEq "h_m5" (mkApp2 (Lean.mkConst ``LeanQbe.T.mergeRetsFlat) lRsE
    (mkApp4 (Lean.mkConst ``LeanQbe.T.tailDupFlat) lAsE lRsE
      (appF ``LeanQbe.T.OptFlatCfg.dcePFlat lAsE lRsE
        (appF ``LeanQbe.T.OptFlatValue.foldFlat lAsE lRsE (Lean.mkConst m5bNm)))
      (Lean.mkConst ``LeanQbe.T.TailDup.defaultConfig))) m5Nm
  let pf := mkAppN (Lean.mkConst ``LeanQbe.T.midStageFlat_eq)
    #[ltE, efC, Lean.mkConst m0Nm, Lean.mkConst m1Nm, Lean.mkConst m2aNm, Lean.mkConst m2bNm,
      Lean.mkConst m2Nm, Lean.mkConst m3aNm, Lean.mkConst m3bNm, Lean.mkConst m3Nm,
      Lean.mkConst m4aNm, Lean.mkConst m4Nm, Lean.mkConst m5aNm, Lean.mkConst m5bNm,
      Lean.mkConst m5Nm, Lean.mkConst hM0, Lean.mkConst hM1, Lean.mkConst hM2a,
      Lean.mkConst hM2b, Lean.mkConst hM2, Lean.mkConst hM3a, Lean.mkConst hM3b,
      Lean.mkConst hM3, Lean.mkConst hM4a, Lean.mkConst hM4, Lean.mkConst hM5a,
      Lean.mkConst hM5b, Lean.mkConst hM5]
  let ty := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) flatTy
    (mkApp2 (Lean.mkConst ``LeanQbe.T.midStageFlat) ltE efC) mfC
  let hMfNm ← addPrivThm (auxNs ++ `h_mf) ty pf
  return (mfC, hMfNm)

private def emitStagedChunkThms (auxNs : Name) (b : CertBaseEnv) (ac : AcycChunkNames)
    (fnsBaseE flatFnsConstE : Lean.Expr) (fnsFlatEqNm : Name)
    (flatFnE hintLit : Lean.Expr) (sd : EvalStagedFnData) : CoreM Unit := do
  let tys := mkCertTypes
  let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
  let boolTy := Lean.mkConst ``Bool
  let f0Nm ← addPrivDef (auxNs ++ `s_f0) flatTy flatFnE
  let f0C := Lean.mkConst f0Nm
  let hWf ← addPrivEq (auxNs ++ `h_wf) boolTy
    (mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.wfCheck) f0C) (Lean.mkConst ``Bool.true)
  let (efC, hEfNm) ← emitEarlyThms auxNs f0C sd
  let hSupp ← addPrivEq (auxNs ++ `h_supp) boolTy
    (mkApp2 (Lean.mkConst ``LeanQbe.T.TFlatFn.supportsSource) b.ltE efC)
    (Lean.mkConst ``Bool.true)
  let (mfC, hMfNm) ← emitMidThms auxNs b.ltE efC sd
  let extTy := Lean.mkConst ``LeanQbe.T.Rega.Ext
  let extNm ← addPrivDef (auxNs ++ `s_ext) extTy sd.extCtorLit
  let extC := Lean.mkConst extNm
  let h0Nm ← addPrivDef (auxNs ++ `s_h0)
    (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Hints) b.isaE) hintLit
  let h0C := Lean.mkConst h0Nm
  let hExt ← addPrivEq (auxNs ++ `h_ext) extTy
    (mkApp2 (Lean.mkConst ``LeanQbe.T.TFlat.ext)
      (mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.rs) mfC)
      (mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.body) mfC)) extC
  let excCodeTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero])
    (Lean.mkConst ``String) b.listDirTy
  let hLow ← addPrivEq (auxNs ++ `h_low) excCodeTy
    (mkApp4 (Lean.mkConst ``LeanQbe.T.Rega.lowerFlatFn) b.isaE h0C extC mfC)
    (mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero]) (Lean.mkConst ``String) b.listDirTy
      (Lean.mkConst ac.codeNm))
  let optNatTy := mkApp (Lean.mkConst ``Option [.zero]) tys.natTy
  let hBnd ← addPrivEq (auxNs ++ `h_bnd) optNatTy
    (mkAppN (Lean.mkConst ``LeanQbe.T.checkAndBoundExt)
      #[b.isaE, b.raE, b.exitsE, b.nXE, Lean.mkConst ac.extNm, h0C, extC])
    (mkApp2 (Lean.mkConst ``Option.some [.zero]) tys.natTy (mkNatLit sd.bndNat))
  let some flatNm := ac.flatNm? | throwError "emitStagedChunkThms: missing flatNm"
  let some cmFlatNm := ac.cmFlatNm? | throwError "emitStagedChunkThms: missing cmFlatNm"
  let okPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) b.listDirTy tys.listBoundsTy
  let excTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) okPairTy
  let cmFlatLhs := mkAppN (Lean.mkConst ``LeanQbe.T.compileModuleFlat)
    #[b.isaE, b.ltE, b.raE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
      Lean.mkConst flatNm, Lean.mkConst ac.hintsNm]
  let cmRhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero]) (Lean.mkConst ``String) okPairTy
    (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) b.listDirTy tys.listBoundsTy
      (Lean.mkConst ac.codeNm) (Lean.mkConst ac.boundsNm))
  let cmFlatVal := mkAppN (Lean.mkConst ``LeanQbe.T.compileModuleFlat_single)
    #[b.isaE, b.ltE, b.raE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
      f0C, efC, mfC, h0C, extC, Lean.mkConst ac.codeNm, mkNatLit sd.bndNat,
      Lean.mkConst hWf, Lean.mkConst hEfNm, Lean.mkConst hSupp, Lean.mkConst hMfNm,
      Lean.mkConst hExt, Lean.mkConst hLow, Lean.mkConst hBnd]
  addCertThm cmFlatNm (mkApp3 (Lean.mkConst ``Eq [.succ .zero]) excTy cmFlatLhs cmRhs) cmFlatVal
  let sliceEqPf := mkAppN (Lean.mkConst ``LeanQbe.T.map_drop_eq [.zero, .one])
    #[flatTy, tys.fnTy, Lean.mkConst ``LeanQbe.T.TFlatFn.toFn, fnsBaseE, flatFnsConstE,
      Lean.mkConst fnsFlatEqNm, mkNatLit 0]
  let cmLhs := mkAppN (Lean.mkConst ``LeanQbe.T.compileModule)
    #[b.isaE, b.ltE, b.raE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
      Lean.mkConst ac.fnsNm, Lean.mkConst ac.hintsNm]
  let cmTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) excTy cmLhs cmRhs
  let cmVal := mkAppN (Lean.mkConst ``LeanQbe.T.compileModule_of_flat_eq)
    #[b.isaE, b.ltE, b.raE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
      Lean.mkConst ac.fnsNm, Lean.mkConst flatNm, Lean.mkConst ac.hintsNm,
      Lean.mkConst ac.codeNm, Lean.mkConst ac.boundsNm, sliceEqPf, Lean.mkConst cmFlatNm]
  addCertThm ac.cmNm cmTy cmVal
  let fnNamesE := mkApp4 (Lean.mkConst ``List.map [1, .zero])
    tys.fnTy tys.symTy (Lean.mkConst ``LeanQbe.T.Fn.name) (Lean.mkConst ac.fnsNm)
  let metaLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkCompileLit)
    #[b.dirTy, b.labelE, b.progSmallE, Lean.mkConst ac.codeNm, Lean.mkConst ac.boundsNm,
      fnNamesE, b.exitsE, b.maxBE]
  addKernelEqThm ac.metaNm boolTy metaLhs (Lean.mkConst ``Bool.true) .zero

/-- Emit a staged single-function `SegChunks` certificate using per-pass `TFlat` kernel
equalities (`emitStagedChunkThms`). -/
def emitStagedSegChunks (segNm auxNs : Name) (b : CertBaseEnv)
    (runFnsE flatBaseE : Lean.Expr) (fnsFlatEqNm : Name)
    (flatFnE : Lean.Expr) (sd : EvalStagedFnData) : CommandElabM Unit := do
  let some ch := sd.md.chunks.head?
    | throwError "emitStagedSegChunks: empty chunk list"
  if !ch.hintsLit.isAppOfArity ``List.cons 3 then
    throwError "emitStagedSegChunks: expected singleton hints list literal"
  let hintLit := ch.hintsLit.getArg! 1
  let tys := mkCertTypes
  let ac ← emitAcycChunkDefs auxNs "c0" b.compileCert runFnsE b.listHintsTy b.listDirTy ch
    (some flatBaseE)
  liftCoreM <| emitStagedChunkThms auxNs b ac runFnsE flatBaseE fnsFlatEqNm flatFnE hintLit sd
  let chunkEntry ← liftCoreM <| emitAcycCompiledChunk b ac
  let chunkTy := mkAppN (Lean.mkConst ``LeanQbe.T.CompiledChunk)
    #[b.targE, b.ltE, b.exitsE, b.nXE]
  let chunksNm := auxNs ++ `chunks
  liftCoreM <| addCertDef chunksNm (mkApp (Lean.mkConst ``List [1]) chunkTy)
    (mkExprList 1 chunkTy [chunkEntry]) b.compileCert
  let fnsEqNm := auxNs ++ `fns_eq
  let maxBLeNm := auxNs ++ `maxBound_le
  let chunksFnsE := mkAppN (Lean.mkConst ``LeanQbe.T.chunksFns)
    #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst chunksNm]
  let fnsEqProof := mkApp3 (Lean.mkConst ``LeanQbe.T.slice_last_eq [1])
    tys.fnTy runFnsE (mkNatLit 0)
  let maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_cons)
    #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE, chunkEntry,
      mkApp (Lean.mkConst ``List.nil [1]) chunkTy, mkApp (Lean.mkConst ``Nat.le_refl) b.maxBE,
      mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_nil)
        #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE]]
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

end

end LeanQbe.T
