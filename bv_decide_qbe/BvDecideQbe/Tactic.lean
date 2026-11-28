module

public import Std.Tactic.BVDecide
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import BvDecideQbe.NormalizeRules
public import BvDecideQbe.Prover
public import BvDecideQbe.Cegar
public import BvDecideQbe.CutCore
public import BvDecideQbe.Cut
public import Lean.Elab.Tactic.BVDecide
public import Lean.Elab.ConfigEval
public import Lean.Elab.Tactic.Grind.Basic
public import Lean.Meta.Tactic.BVDecide.Main
public import Lean.Meta.Tactic.Grind.Main
public meta import BvDecideQbe.FFI
public meta import BvDecideQbe.NormalizeRules
public meta import BvDecideQbe.Prover
public meta import BvDecideQbe.Cegar
public meta import BvDecideQbe.CutCore
public meta import BvDecideQbe.Cut
public meta import Lean.Elab.Tactic.BVDecide
public meta import Lean.Elab.ConfigEval
public meta import Lean.Elab.Tactic.Grind.Basic
public meta import Lean.Meta.Tactic.BVDecide.Main
public meta import Lean.Meta.Tactic.Grind.Main

/-!
# Trust-Pure `bv_decide_qbe` & `bv_cut_qbe` Tactics (`Step 3` + `E0 / H5a + H6a + H7`)

Public tactics and `sym =>` / `grind =>` entrypoints using `Std.Tactic.BVDecide`'s normalizer
(`Normalize.bvNormalize`), reflection (`closeWithBVReflection`), Phase-1 CEGAR wrapper
(`BvDecideQbe.cegarBlaster`), trust-pure prover (`BvDecideQbe.unsatProver`) backed by verified
in-process `KissatFidelity`, and the zero-new-trust `bv_cut_qbe` cutpoint-slicing + ring-dispatch
front end (`BvDecideQbe.Cut`).
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

/-- Trust-pure `BitVec` decision tactic backed by `BVP1` + verified `KissatFidelity`
+ kernel `rfl`. -/
syntax (name := bvDecideQbeStx) "bv_decide_qbe" optConfig (bvTypes)? : tactic

/-- Upstream-fidelity `bv_decide_qbe` alias (disables `D1–D8`, keeping only `D0`). -/
macro (name := bvDecideQbeUpstreamStx) "bv_decide_qbe_upstream"
    cfg:optConfig types:(bvTypes)? : tactic => do
  let `(Lean.Parser.Tactic.optConfig| $items:configItem*) := cfg | Macro.throwUnsupported
  `(tactic| bv_decide_qbe $items* (mode := .upstream) $[$types]?)

/-- Trust-pure `BitVec` decision tactic in `sym =>` and `grind =>` mode. -/
syntax (name := bvDecideQbeGrindStx) "bv_decide_qbe" optConfig (bvTypes)? : grind

/-- Upstream-fidelity `bv_decide_qbe` alias in `sym =>` and `grind =>` mode. -/
macro (name := bvDecideQbeUpstreamGrindStx) "bv_decide_qbe_upstream"
    cfg:optConfig types:(bvTypes)? : grind => do
  let `(Lean.Parser.Tactic.optConfig| $items:configItem*) := cfg | Macro.throwUnsupported
  `(grind| bv_decide_qbe $items* (mode := .upstream) $[$types]?)

/-- Incremental pre-processor for `bv_decide_qbe` in `sym =>` and `grind =>` mode. -/
syntax (name := bvDecideQbePushStx) "bv_decide_qbe_push" optConfig : grind

/-- Zero-new-trust cutpoint-equivalence & ring-dispatch tactic (`E0 / H5a + H6a + H7`).
Supports automatic pre-inlining cut discovery (`bv_cut_qbe`) and explicit cutpoint lists
(`bv_cut_qbe [e1 = e2, ...]`). -/
syntax (name := bvCutQbeStx) "bv_cut_qbe" optConfig ("[" term,* "]")? (bvTypes)? : tactic

meta section

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

private def elabQbeConfigGrind (cfg : TSyntax `Lean.Parser.Tactic.optConfig) (goal : MVarId)
    (elaborator : Name) (recover : Bool := true) : TermElabM QbeConfig := do
  elabQbeConfig cfg
    |>.run { elaborator, recover }
    |>.run' { goals := [goal] }

@[tactic bvDecideQbeStx]
def evalBvDecideQbe : Tactic := fun
  | `(tactic| bv_decide_qbe $cfgStx:optConfig $[$types:bvTypes]?) => do
    let ref ← getRef
    let qcfg ← elabQbeConfig cfgStx
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
      let params ← Grind.mkDefaultParams {}
      discard <| Grind.GrindM.run (params := params) <|
        bvDecideQbe (.mvarIdTarget goal) tacticCtx qbeCtx
  | _ => throwUnsupportedSyntax

@[grind_tactic bvDecideQbeGrindStx]
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

@[grind_tactic bvDecideQbePushStx]
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

@[tactic bvCutQbeStx]
def evalBvCutQbe : Tactic := fun
  | `(tactic| bv_cut_qbe $cfgStx:optConfig $[[$cuts,*]]? $[$types:bvTypes]?) => do
    let ref ← getRef
    let qcfg ← elabQbeConfig cfgStx
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

end

end BvDecideQbe
