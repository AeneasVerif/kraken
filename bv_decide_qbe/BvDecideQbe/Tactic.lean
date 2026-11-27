module

public import Std.Tactic.BVDecide
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import BvDecideQbe.Prover
public import BvDecideQbe.Cegar
public import Lean.Elab.Tactic.BVDecide
public import Lean.Meta.Tactic.BVDecide.Main
public import Lean.Meta.Tactic.Grind.Main
public meta import BvDecideQbe.FFI
public meta import BvDecideQbe.Prover
public meta import BvDecideQbe.Cegar
public meta import Lean.Elab.Tactic.BVDecide
public meta import Lean.Meta.Tactic.BVDecide.Main
public meta import Lean.Meta.Tactic.Grind.Main

/-!
# Trust-Pure `bv_decide_qbe` Tactic Elaborator (`S3d`)

Public tactic entrypoint using `Std.Tactic.BVDecide`'s normalizer (`Normalize.bvNormalize`),
reflection (`closeWithBVReflection`), Phase-1 CEGAR wrapper (`BvDecideQbe.cegarBlaster`), and
trust-pure prover (`BvDecideQbe.unsatProver`).
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

/-- Trust-pure `BitVec` decision tactic backed by `BVP1` + verified Kissat + kernel `rfl`. -/
syntax (name := bvDecideQbeStx) "bv_decide_qbe" optConfig (bvTypes)? : tactic

meta section
@[tactic bvDecideQbeStx]
def evalBvDecideQbe : Tactic := fun
  | `(tactic| bv_decide_qbe $cfg:optConfig $[$types:bvTypes]?) => do
    let ref ← getRef
    let cfg ← elabBVDecideConfig cfg
    let types ← elabBVDecideTypes types cfg
    let tacticCtx := mkQbeTacticContext cfg types
    let qbeCtx : QbeContext := {
      fuel := defaultFuel
      axiomDeclRange? := some ref
    }
    liftMetaFinishingTactic fun g => do
      let params ← Grind.mkDefaultParams {}
      discard <| Grind.GrindM.run (params := params) <|
        bvDecideQbe (.mvarIdTarget g) tacticCtx qbeCtx
  | _ => throwUnsupportedSyntax
end

end BvDecideQbe
