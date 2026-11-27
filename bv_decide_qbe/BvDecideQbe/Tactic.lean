module

public import Std.Tactic.BVDecide
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import BvDecideQbe.Prover
public import BvDecideQbe.Cegar
public import Lean.Elab.Tactic.BVDecide
public import Lean.Elab.Tactic.Grind.Basic
public import Lean.Meta.Tactic.BVDecide.Main
public import Lean.Meta.Tactic.Grind.Main
public meta import BvDecideQbe.FFI
public meta import BvDecideQbe.Prover
public meta import BvDecideQbe.Cegar
public meta import Lean.Elab.Tactic.BVDecide
public meta import Lean.Elab.Tactic.Grind.Basic
public meta import Lean.Meta.Tactic.BVDecide.Main
public meta import Lean.Meta.Tactic.Grind.Main

/-!
# Trust-Pure `bv_decide_qbe` Tactic & `sym`/`grind` Elaborator (`Step 3`)

Public tactic and `sym =>` / `grind =>` entrypoints using `Std.Tactic.BVDecide`'s normalizer
(`Normalize.bvNormalize`), reflection (`closeWithBVReflection`), Phase-1 CEGAR wrapper
(`BvDecideQbe.cegarBlaster`), and trust-pure prover (`BvDecideQbe.unsatProver`) backed by
verified in-process `KissatFidelity` (`Step-12` `517` fns + `64` Bitblast fns).
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

/-- Trust-pure `BitVec` decision tactic backed by `BVP1` + verified `KissatFidelity` + kernel `rfl`. -/
syntax (name := bvDecideQbeStx) "bv_decide_qbe" optConfig (bvTypes)? : tactic

/-- Trust-pure `BitVec` decision tactic in `sym =>` and `grind =>` mode. -/
syntax (name := bvDecideQbeGrindStx) "bv_decide_qbe" optConfig (bvTypes)? : grind

/-- Incremental pre-processor for `bv_decide_qbe` in `sym =>` and `grind =>` mode. -/
syntax (name := bvDecideQbePushStx) "bv_decide_qbe_push" optConfig : grind

meta section

private def elabBVDecideConfigGrind (cfg : TSyntax `Lean.Parser.Tactic.optConfig) (goal : MVarId)
    (elaborator : Name) : TermElabM BVDecideConfig := do
  Lean.Meta.Tactic.BVDecide.elabBVDecideConfig cfg
    |>.run { elaborator }
    |>.run' { goals := [goal] }

@[tactic bvDecideQbeStx]
def evalBvDecideQbe : Tactic := fun
  | `(tactic| bv_decide_qbe $cfgStx:optConfig $[$types:bvTypes]?) => do
    let ref ← getRef
    let cfg ← elabBVDecideConfig cfgStx
    let types ← elabBVDecideTypes types cfg
    liftMetaFinishingTactic fun g => do
      let cfg ← resolveAutoAcNf cfgStx cfg g
      let tacticCtx := mkQbeTacticContext cfg types
      let qbeCtx : QbeContext := {
        fuel := fuelOfTimeout cfg.timeout
        axiomDeclRange? := some ref
        acNf := cfg.acNf
      }
      let params ← Grind.mkDefaultParams {}
      discard <| Grind.GrindM.run (params := params) <|
        bvDecideQbe (.mvarIdTarget g) tacticCtx qbeCtx
  | _ => throwUnsupportedSyntax

@[grind_tactic bvDecideQbeGrindStx]
def evalBvDecideQbeGrind : Grind.GrindTactic := fun
  | `(grind| bv_decide_qbe $cfgStx:optConfig $[$types:bvTypes]?) => do
    let ref ← getRef
    let g ← Grind.getMainGoal
    let cfg ← elabBVDecideConfigGrind cfgStx g.mvarId `bv_decide_qbe
    let cfg ← resolveAutoAcNfGrind cfgStx cfg g
    let types ← elabBVDecideTypes types cfg
    let tacticCtx := mkQbeTacticContext cfg types
    let qbeCtx : QbeContext := {
      fuel := fuelOfTimeout cfg.timeout
      axiomDeclRange? := some ref
      acNf := cfg.acNf
    }
    discard <| Grind.liftGrindM <| bvDecideQbe (.grindTarget g) tacticCtx qbeCtx
    Grind.replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[grind_tactic bvDecideQbePushStx]
def evalBvDecideQbePush : Grind.GrindTactic := fun
  | `(grind| bv_decide_qbe_push $cfgStx:optConfig) => do
    let g ← Grind.getMainGoal
    let cfg ← elabBVDecideConfigGrind cfgStx g.mvarId `bv_decide_qbe_push
    let cfg ← resolveAutoAcNfGrind cfgStx cfg g (fixedInt := false)
    Grind.liftGoalM <| do
      let g ← get
      let ctx := Normalize.PreProcessContext.new .push cfg
      let (_, state) ← Normalize.bvNormalize.run ctx (.grindTarget g)
      let .grindTarget goal := state.target | unreachable!
      set goal
  | _ => throwUnsupportedSyntax

end

end BvDecideQbe
