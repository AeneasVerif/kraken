/-
The frame inference procedure of the separation wp. A memory spec's
precondition is `⌜new ⊑ Q () r z f⌝ ⊓ fp`: the footprint `fp` and the post
entailment that continues the run into the tail. The procedure frames `emp`,
unifies `fp` with the goal's precondition to assign the spec's logical
variables, and returns two subgoals: `pre ⊑ fp` for the discharge, and
`new ⊑ Q () r z f` for `vcgen` to continue with.

Every instruction spec is a triple of one directive, so the procedure is
keyed on `Directive`.
-/
import Kraken.SepSpecs
import Lean.Elab.Tactic.VCGen.FrameProc

open Lean Meta Sym Sym.Internal Elab Tactic VCGen
open Std.WP
open Lean.Order
open scoped SepWP

namespace SepWP

variable {pre fp new : MProp 64} {W X : Reg64s → RegZmms → StatusFlags → MProp 64}
  {r : Reg64s} {z : RegZmms} {f : StatusFlags}

/-- The split VC at the empty frame is the spec's own entailment. -/
theorem split_emp (hspec : pre ⊑ W r z f) : pre ⊑ frameOp MProp.emp W r z f := by
  rwa [frameOp_apply, MProp.emp_sep]

/-- The pre VC of a memory spec at the empty frame, from the footprint's
entailment and the post entailment into the continuation. -/
theorem le_ofProp_meet_emp (hc : pre ⊑ fp) (hφ : new ⊑ X r z f) :
    pre ⊑ ⌜new ⊑ PreservesSup.upperAdjoint (frameOp MProp.emp) X r z f⌝ ⊓ fp := by
  refine le_meet _ _ _ (le_ofProp _ _ ?_) hc
  show new ⊑ PreservesSup.upperAdjoint
    (Function.comp (Function.comp (Function.comp (MProp.sep MProp.emp)))) X r z f
  rw [PreservesSup.upperAdjoint_comp_apply, PreservesSup.upperAdjoint_comp_apply,
    PreservesSup.upperAdjoint_comp_apply]
  exact PreservesSup.le_upperAdjoint _ (by rwa [MProp.emp_sep])

/-- Phase two: frame `emp` and take the precondition as the footprint. At a
memory spec `⌜new ⊑ upperAdjoint (frameOp emp) X r z f⌝ ⊓ fp`, prove the pre
VC from the subgoals `pre ⊑ fp` and `new ⊑ X r z f`; at any other spec, the
pre VC stays a goal of `vcgen`. -/
private def frameSplit (i : FrameInferenceInfo) (goal : FrameGoal) : Grind.GrindM FrameSplit := do
  let #[r, z, f] := goal.framedApp.excessArgs
    | throwError "sep frameproc: expected three state arguments, got {goal.framedApp.excessArgs.size}"
  goal.frame.assign (← mkAppNS (← mkConstS ``MProp.emp) #[i.le.getAppArgs[0]!.appArg!])
  goal.footprint.assign i.pre
  let splitVCProof ← mkAppNS (← mkConstS ``split_emp)
    #[i.pre, goal.framedApp.wp, r, z, f, goal.specProof]
  let specPre ← instantiateMVarsS goal.specPre
  let some (_, _, pφ, fp) := specPre.app4? ``meet | return { splitVCProof, subgoals := [] }
  let some (_, _, new, wand) := pφ.appArg!.app4? ``PartialOrder.rel
    | return { splitVCProof, subgoals := [] }
  unless wand.isAppOfArity ``PreservesSup.upperAdjoint 7 do return { splitVCProof, subgoals := [] }
  -- The unifier keeps the assignments it made before a mismatch, so the spec's byte list is
  -- assigned even where the address is spelled through a register write.
  discard <| isDefEqS i.pre fp
  let fp ← instantiateMVarsS fp
  -- The continuation `X` runs at the wand's own state, the state the instruction leaves.
  let args := wand.getAppArgs
  let hc ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS i.le #[i.pre, fp])
  let hφ ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS i.le #[new, ← mkAppNS args[3]! (args.extract 4 7)])
  goal.preVC.assign (← mkAppNS (← mkConstS ``le_ofProp_meet_emp)
    (#[i.pre, fp, new] ++ args.extract 3 7 ++ #[hc, hφ]))
  return { splitVCProof, subgoals := [hc.mvarId!, hφ.mvarId!] }

@[frameproc] def sepFrameProc : FrameProc where
  prog := ``Directive
  opHead := ``SepWP.frameOp
  mkOpAppM := fun _ => pure (mkConst ``SepWP.frameOp)
  mkResourceTy := fun _ => pure (mkApp (mkConst ``MProp) (mkNatLit 64))
  proc := fun i => return .commit i.unframedApp.excessArgs (frameSplit i)

end SepWP

/-! ## The entry point

`kvcgen64 [defs] with step` is `vcgen` with the register state folded as it
goes: every write to a named register becomes a structure update, so the
state `vcgen` threads through a block stays one register literal. -/

/-- `vcgen` on the separation wp with the register state folded. -/
syntax (name := kvcgen64) "kvcgen64" (" [" ident,* "]")? (" with " vcgenDischarge)? : tactic

macro_rules
  | `(tactic| kvcgen64 $[[$ids,*]]? $[with $d]?) => do
    let lemmas ← (ids.map (·.getElems) |>.getD #[]).mapM fun i =>
      `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| vcgen [$lemmas,*] simplifying_assumptions [
        Reg64s.set64_rax,
        Reg64s.set64_rbx,
        Reg64s.set64_rcx,
        Reg64s.set64_rdx,
        Reg64s.set64_rsi,
        Reg64s.set64_rdi,
        Reg64s.set64_rsp,
        Reg64s.set64_rbp,
        Reg64s.set64_r8,
        Reg64s.set64_r9,
        Reg64s.set64_r10,
        Reg64s.set64_r11,
        Reg64s.set64_r12,
        Reg64s.set64_r13,
        Reg64s.set64_r14,
        Reg64s.set64_r15] $[with $d]?)
