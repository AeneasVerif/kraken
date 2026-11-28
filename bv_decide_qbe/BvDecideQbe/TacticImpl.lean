module

public import BvDecideQbe.Syntax
public import BvDecideQbe.Prover
public import BvDecideQbe.Cegar
public import BvDecideQbe.Cut
public import Lean.Elab.Tactic.BVDecide
public import Lean.Elab.ConfigEval
public import Lean.Elab.Tactic.Grind.Basic

/-!
# Precompiled Tactic Elaborators for `bv_decide_qbe` & `bv_cut_qbe`

Compiled into `BvDecideQbeNative` and registered via `BvDecideQbePlugin` so downstream files
importing `BvDecideQbe` / `BvDecideQbe.Tactic` run native tactic elaborators directly with zero
`Lean.*` `.olean` imports and zero unconditional `Grind.mkDefaultParams` setup on plain goals.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Elab.Tactic.BVDecide
open Lean.Meta.Tactic.BVDecide
open Lean.Parser.Tactic

open scoped Lean.Elab.ConfigEval in
private local ensure_eval_expr_instance BvDecideQbe.QbeConfig

private def normalizeQbeConfigStx (item : Lean.Elab.ConfigEval.ConfigItem) : Term :=
  let val : Term := ⟨item.value⟩
  match val with
  | `({ $[$src:term with]? $[$fields:structInstField],* }) =>
    let fields' := fields.map fun (field : TSyntax `Lean.Parser.Term.structInstField) =>
      match field with
      | `(Parser.Term.structInstField| mode := .upstream) =>
        Unhygienic.run
          `(Parser.Term.structInstField| mode := some BvDecideQbe.QbeMode.upstream)
      | `(Parser.Term.structInstField| mode := .enhanced) =>
        Unhygienic.run
          `(Parser.Term.structInstField| mode := some BvDecideQbe.QbeMode.enhanced)
      | _ => field
    match src with
    | some s => Unhygienic.run `({ $s:term with $[$fields':structInstField],* })
    | none => Unhygienic.run `({ $[$fields':structInstField],* })
  | _ => val

declare_config_elab elabQbeConfig BvDecideQbe.QbeConfig where
  option config := fun _ item =>
    (Lean.Elab.ConfigEval.evalExprWithElab (normalizeQbeConfigStx item) : TermElabM QbeConfig)

@[inline] private def isEmptyOptConfig (cfg : TSyntax `Lean.Parser.Tactic.optConfig) : Bool :=
  match cfg with
  | `(Lean.Parser.Tactic.optConfig| ) => true
  | _ => false

@[inline] private def elabQbeConfigFast (cfg : TSyntax `Lean.Parser.Tactic.optConfig) :
    TacticM QbeConfig :=
  if isEmptyOptConfig cfg then pure {} else elabQbeConfig cfg

private def elabQbeConfigGrind (cfg : TSyntax `Lean.Parser.Tactic.optConfig) (goal : MVarId)
    (elaborator : Name) (recover : Bool := true) : TermElabM QbeConfig := do
  if isEmptyOptConfig cfg then
    return {}
  elabQbeConfig cfg
    |>.run { elaborator, recover }
    |>.run' { goals := [goal] }

@[builtin_tactic bvDecideQbeStx]
def evalBvDecideQbe : Tactic := fun
  | `(tactic| bv_decide_qbe $cfgStx:optConfig $[$types:bvTypes]?) => do
    let ref ← getRef
    let qcfg ← elabQbeConfigFast cfgStx
    let mode ← resolveQbeMode qcfg.mode
    let features := resolveQbeFeatures mode qcfg
    let bvCfg := qcfg.toBVDecideConfig
    let types ← elabBVDecideTypes types bvCfg
    liftMetaFinishingTactic fun g => do
      let mut goal := g
      if features.extraNormalize then
        match ← trySimpNormalizeRules goal with
        | none => return
        | some next => goal := next
      if features.ringDispatch then
        if ← tryRingDispatch goal then
          return
      let effCfg ←
        if features.autoAcNf then
          resolveAutoAcNf cfgStx bvCfg goal
        else
          pure bvCfg
      let tacticCtx := mkQbeTacticContext effCfg types
      let qbeCtx := mkQbeContext effCfg features (some ref)
      discard <| runPlainGrindM <|
        bvDecideQbe (.mvarIdTarget goal) tacticCtx qbeCtx
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic bvDecideQbeGrindStx]
def evalBvDecideQbeGrind : Grind.GrindTactic := fun
  | `(grind| bv_decide_qbe $cfgStx:optConfig $[$types:bvTypes]?) => do
    let ref ← getRef
    let g ← Grind.getMainGoal
    let recover := (← read).recover
    let qcfg ← elabQbeConfigGrind cfgStx g.mvarId `bv_decide_qbe recover
    let mode ← resolveQbeMode qcfg.mode
    let features := resolveQbeFeatures mode qcfg
    let bvCfg ←
      if features.autoAcNf then
        resolveAutoAcNfGrind cfgStx qcfg.toBVDecideConfig g
      else
        pure qcfg.toBVDecideConfig
    let types ← elabBVDecideTypes types bvCfg
    let tacticCtx := mkQbeTacticContext bvCfg types
    let qbeCtx := mkQbeContext bvCfg features (some ref)
    discard <| Grind.liftGrindM <| bvDecideQbe (.grindTarget g) tacticCtx qbeCtx
    Grind.replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic bvDecideQbePushStx]
def evalBvDecideQbePush : Grind.GrindTactic := fun
  | `(grind| bv_decide_qbe_push $cfgStx:optConfig) => do
    let g ← Grind.getMainGoal
    let recover := (← read).recover
    let qcfg ← elabQbeConfigGrind cfgStx g.mvarId `bv_decide_qbe_push recover
    let mode ← resolveQbeMode qcfg.mode
    let features := resolveQbeFeatures mode qcfg
    let bvCfg ←
      if features.autoAcNf then
        resolveAutoAcNfGrind cfgStx qcfg.toBVDecideConfig g (fixedInt := false)
      else
        pure qcfg.toBVDecideConfig
    Grind.liftGoalM <| do
      let g ← get
      let ctx := Normalize.PreProcessContext.new .push bvCfg
      let (_, state) ← Normalize.bvNormalize.run ctx (.grindTarget g)
      let .grindTarget goal := state.target | unreachable!
      set goal
  | _ => throwUnsupportedSyntax

@[builtin_tactic bvCutQbeStx]
def evalBvCutQbe : Tactic := fun
  | `(tactic| bv_cut_qbe $cfgStx:optConfig $[[$cuts,*]]? $[$types:bvTypes]?) => do
    let ref ← getRef
    let qcfg ← elabQbeConfigFast cfgStx
    let mode := qcfg.mode.getD .enhanced
    let features := resolveQbeFeatures mode qcfg (inCut := true)
    let bvCfg := qcfg.toBVDecideConfig
    let types ← elabBVDecideTypes types bvCfg
    let g ← getMainGoal
    let explicitCuts ← g.withContext do
      match cuts with
      | none => pure #[]
      | some cs =>
        cs.getElems.mapM fun stx => do
          let e ← Term.elabTermAndSynthesize stx (some (mkSort 0))
          instantiateMVars e
    liftMetaFinishingTactic fun goal => do
      let effCfg ←
        if features.autoAcNf then
          resolveAutoAcNf cfgStx bvCfg goal
        else
          pure bvCfg
      let qbeCtx := mkQbeContext effCfg features (some ref)
      bvCutQbe goal effCfg types qbeCtx explicitCuts
  | _ => throwUnsupportedSyntax

end BvDecideQbe
