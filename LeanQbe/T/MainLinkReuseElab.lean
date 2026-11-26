/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainLinkReuseCover
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainLinkReuseCover

/-!
# Meta Elaborators for Callee-Cover & Pruned-Ext Literals (`MainLinkReuseElab`)

Arch-neutral meta command elaborators (`eval_raw_callees!`, `eval_pruned_ext!`) emitting flat
literal `List SigEntry` and `List (SigEntry × Nat)` definitions for `MainLinkReuseCover` without
kernel `Fn.mid` evaluation or `pruneExt` allocation over large prefix tables.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

meta section

open Lean Elab Command Meta

/-- Deduplicate a list of `SigEntry` values preserving first occurrence via `SigEntry.beq`. -/
def dedupSigEntries (gs : List SigEntry) : List SigEntry :=
  gs.foldl (fun acc g => if acc.any (SigEntry.beq g) then acc else acc ++ [g]) []

/-- Evaluate deduplicated `(f.rawCalls.map (sigEntryLegal lt))` over `fs` in compiled meta code
and return the flat `List SigEntry` literal expression. -/
def evalRawCalleesLit (lt : LegalTarget) (fs : List Fn) : Lean.Expr :=
  Lean.toExpr <| dedupSigEntries <| fs.flatMap fun f => f.rawCalls.map (sigEntryLegal lt)

/-- Flat-list variant of `evalRawCalleesLit` over `.olean`-decoded `List TFlatFn`. -/
def evalRawCalleesFlatLit (lt : LegalTarget) (tfs : List TFlatFn) : Lean.Expr :=
  evalRawCalleesLit lt (tfs.map TFlatFn.toFn)

/-- Evaluate `pruneExt S acc` in compiled meta code and return the flat `List (SigEntry × Nat)`
literal expression. -/
def evalPrunedExtLit (S : List SigEntry) (acc : List (SigEntry × Nat)) : Lean.Expr :=
  Lean.toExpr (pruneExt S acc)

/-- `eval_raw_callees! outName legalTarget fnsExpr` computes deduplicated raw legal callees of
`fnsExpr` in compiled meta code and emits `@[expose] def outName : List SigEntry := <literal>`. -/
scoped syntax "eval_raw_callees! " ident term:arg term:arg : command

scoped elab_rules : command
  | `(eval_raw_callees! $outId $ltT $fnsT) => do
    let ns ← getCurrNamespace
    let outNm := ns ++ outId.getId
    let listSigTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.SigEntry)
    let lit ← liftTermElabM do
      let ltE ← Term.elabTerm ltT (some (Lean.mkConst ``LeanQbe.T.LegalTarget))
      let listFnTy := mkApp (Lean.mkConst ``List [1]) (Lean.mkConst ``LeanQbe.T.Fn)
      let fnsE ← Term.elabTerm fnsT (some listFnTy)
      Term.synthesizeSyntheticMVarsNoPostponing
      let ltE ← instantiateMVars ltE
      let fnsE ← instantiateMVars fnsE
      match (← decodeFlatSliceExpr fnsE) with
      | some (flatFns, _, _) =>
        let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.TFlatFn)
        let runnerTy := Lean.mkForall `_ .default listFlatTy (Lean.mkConst ``Lean.Expr)
        let callE ← instantiateMVars
          (mkApp (Lean.mkConst ``LeanQbe.T.evalRawCalleesFlatLit) ltE)
        let runner ← unsafe evalExpr (List TFlatFn → Lean.Expr) runnerTy callE
        pure (runner flatFns)
      | none =>
        let callE ← instantiateMVars
          (mkAppN (Lean.mkConst ``LeanQbe.T.evalRawCalleesLit) #[ltE, fnsE])
        unsafe evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) callE
    liftCoreM <| addCertDef outNm listSigTy lit true

/-- `eval_pruned_ext! outName calleesExpr accExpr` computes `pruneExt calleesExpr accExpr` in
compiled meta code and emits `@[expose] def outName : List (SigEntry × Nat) := <literal>`. -/
scoped syntax "eval_pruned_ext! " ident term:arg term:arg : command

scoped elab_rules : command
  | `(eval_pruned_ext! $outId $sT $accT) => do
    let ns ← getCurrNamespace
    let outNm := ns ++ outId.getId
    let sigEntryNatTy :=
      mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
        (Lean.mkConst ``LeanQbe.T.SigEntry) (Lean.mkConst ``Nat)
    let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
    let lit ← liftTermElabM do
      let listSigTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.SigEntry)
      let sE ← Term.elabTerm sT (some listSigTy)
      let accE ← Term.elabTerm accT (some listExtTy)
      Term.synthesizeSyntheticMVarsNoPostponing
      let sE ← instantiateMVars sE
      let accE ← instantiateMVars accE
      let callE ← instantiateMVars
        (mkAppN (Lean.mkConst ``LeanQbe.T.evalPrunedExtLit) #[sE, accE])
      unsafe evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) callE
    liftCoreM <| addCertDef outNm listExtTy lit true

end

end LeanQbe.T
