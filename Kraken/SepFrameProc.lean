module

/-
The frame inference procedure of the separation wp, with `ecancel` as its
engine. At a spec application `vcgen` hands over the goal's precondition and
the spec's precondition with its logical variables live.
`Kraken.Tactic.solveSepSplit` at `MProp.sepOps` cancels the spec's footprint
out of the goal precondition, assigning the logical variables by matching,
the remainder to the frame, and proves the split by one AC equation.
`Program.FrameWP.split_of_eq` turns that equation into the split VC's proof, and
`Program.FrameWP.frames_directive` is the frame-rule side goal.

Every instruction spec is a triple of one directive, so the procedure is
keyed on `Directive`: that is where `vcgen` applies a spec with a footprint.
-/
public import Kraken.SepSpecs
public import Kraken.SepCancel
public import Kraken.KVCGen
public import Lean.Elab.Tactic.VCGen.FrameProc

public section

open Lean Meta Sym Sym.Internal Elab Tactic VCGen
open Std.WP
open Lean.Order
open scoped Program.FrameWP

namespace Program.FrameWP

/-- The split VC of a frame `R` and a footprint `fp`: the precondition is
`fp ∗ R` by AC, and the spec runs at `fp`. -/
theorem split_of_eq {pre fp R : MProp 64}
    {W : Reg64s → RegZmms → StatusFlags → MProp 64} {r : Reg64s} {z : RegZmms}
    {f : StatusFlags} (hc : pre = fp ∗ R) (hspec : fp ⊑ W r z f) :
    pre ⊑ frameOp R W r z f := by
  rw [frameOp_apply, hc, MProp.sep_comm]
  exact MProp.sep_mono_right R hspec

/-- The split VC when the spec's precondition is `⌜φ⌝ ⊓ fp`: the footprint `fp`
is matched, and `φ` is a subgoal of the frameproc. -/
theorem split_of_eq_ofProp {pre fp R : MProp 64}
    {W : Reg64s → RegZmms → StatusFlags → MProp 64} {r : Reg64s} {z : RegZmms}
    {f : StatusFlags} {φ : Prop} (hc : pre = fp ∗ R) (hφ : φ)
    (hspec : ⌜φ⌝ ⊓ fp ⊑ W r z f) : pre ⊑ frameOp R W r z f := by
  rw [frameOp_apply, hc, MProp.sep_comm]
  refine MProp.sep_mono_right R (PartialOrder.rel_trans ?_ hspec)
  exact le_meet _ _ _ (le_ofProp _ _ hφ) PartialOrder.rel_refl

/-- The wand of the frame operator at a state is the wand of `∗` at that
state: `PreservesSup.upperAdjoint_comp_apply` through the three layers. -/
theorem upperAdjoint_frameOp_pointwise (R : MProp 64)
    (X : Reg64s → RegZmms → StatusFlags → MProp 64) (r : Reg64s) (z : RegZmms)
    (f : StatusFlags) :
    PreservesSup.upperAdjoint (frameOp R) X r z f
      = PreservesSup.upperAdjoint (MProp.sep R) (X r z f) := by
  show PreservesSup.upperAdjoint
    (Function.comp (Function.comp (Function.comp (MProp.sep R)))) X r z f = _
  rw [PreservesSup.upperAdjoint_comp_apply, PreservesSup.upperAdjoint_comp_apply,
    PreservesSup.upperAdjoint_comp_apply]

/-- The wand of the empty frame is the identity. -/
theorem upperAdjoint_frameOp_emp
    (X : Reg64s → RegZmms → StatusFlags → MProp 64) (r : Reg64s) (z : RegZmms)
    (f : StatusFlags) :
    PreservesSup.upperAdjoint (frameOp MProp.emp) X r z f = X r z f := by
  rw [upperAdjoint_frameOp_pointwise]
  refine PartialOrder.rel_antisymm ?_ ?_
  · have h := PreservesSup.upperAdjoint_le (MProp.sep MProp.emp) (X r z f)
    rwa [MProp.emp_sep] at h
  · exact PreservesSup.le_upperAdjoint _ (PartialOrder.rel_of_eq (MProp.emp_sep _))

/-- The trivial split: frame `emp`, the whole precondition pays the spec. -/
theorem split_emp {pre : MProp 64}
    {W : Reg64s → RegZmms → StatusFlags → MProp 64} {r : Reg64s} {z : RegZmms}
    {f : StatusFlags} (h : pre ⊑ W r z f) : pre ⊑ frameOp MProp.emp W r z f := by
  rw [frameOp_apply, MProp.emp_sep]
  exact h

/-- Phase two. The spec's precondition is `⌜φ⌝ ⊓ fp` or a bare `fp`; `fp` is
the footprint. `solveSepSplit` splits the goal's precondition into `fp` and
the frame `R`, assigning the spec's logical variables, and proves
`pre = fp ∗ R`; `split_of_eq` turns that into the split VC. The pure
conjunct `φ` is the post entailment `new ⊑ Q () r z f`, where after the
frame rule `Q () r z f` is the wand `upperAdjoint (frameOp R) X r z f`; it is
pushed through the frame's layers by `upperAdjoint_frameOp_pointwise`, so the
lattice split of `vcgen` continues at `R ∗ new ⊑ X r z f`. -/
meta def sepFrameSplit (i : FrameInferenceInfo) (goal : FrameGoal) :
    Lean.Meta.Grind.GrindM FrameSplit := do
  let ss := goal.framedApp.excessArgs
  let W := goal.framedApp.expr.stripArgsN ss.size
  let w64 ← shareCommon (mkNatLit 64)
  let mprop ← mkAppNS (← mkConstS ``MProp) #[w64]
  let specPre ← instantiateMVarsS goal.specPre
  let (pure?, fp) :=
    if specPre.isAppOfArity ``Lean.Order.meet 4 then
      let a := specPre.appFn!.appArg!
      if a.isAppOfArity ``Lean.Order.CompleteLattice.ofProp 3 then (some a.appArg!, specPre.appArg!)
      else (none, specPre)
    else (none, specPre)
  let some (R, hc, sideGoals) ← withConfig (fun c => { c with assignSyntheticOpaque := true }) <|
      withTransparency .reducible <| Kraken.Tactic.solveSepSplit MProp.sepOps i.pre fp
    | throwError "sep frameproc: no split of{indentExpr i.pre}\nfor{indentExpr fp}"
  let R ← shareCommon R
  goal.frame.assign R
  let specPre ← shareCommon (← instantiateMVarsS specPre)
  let fp ← shareCommon (← instantiateMVarsS fp)
  goal.footprint.assign specPre
  let leArgs := i.le.getAppArgs
  goal.preVC.assign (← mkAppNS
    (← mkConstS ``Lean.Order.PartialOrder.rel_refl i.le.getAppFn.constLevels!)
    #[leArgs[0]!, leArgs[1]!, specPre])
  match pure? with
  | none =>
    let prf ← mkAppNS (← mkConstS ``Program.FrameWP.split_of_eq)
      #[i.pre, fp, R, W, ss[0]!, ss[1]!, ss[2]!, hc, goal.specProof]
    return { splitVCProof := prf, subgoals := sideGoals }
  | some φ =>
    let φ ← shareCommon (← instantiateMVarsS φ)
    let (hφ, sub) ← pushWand mprop R i.le φ
    let prf ← mkAppNS (← mkConstS ``Program.FrameWP.split_of_eq_ofProp)
      #[i.pre, fp, R, W, ss[0]!, ss[1]!, ss[2]!, φ, hc, hφ, goal.specProof]
    return { splitVCProof := prf, subgoals := sub :: sideGoals }
where
  /-- The post entailment `lhs ⊑ upperAdjoint (frameOp R) X r z f` from the
  entailment into the wand pushed through the layers, `lhs ⊑ upperAdjoint
  (MProp.sep R) (X r z f)` (or into `X r z f` at the empty frame), which is
  the subgoal. Any other shape is the subgoal itself. -/
  pushWand (mprop R le φ : Expr) : Lean.Meta.Grind.GrindM (Expr × MVarId) := do
    let some (_, _, lhs, rhs) := φ.app4? ``Lean.Order.PartialOrder.rel
      | let h ← mkFreshExprSyntheticOpaqueMVar φ; return (h, h.mvarId!)
    let args := rhs.getAppArgs
    unless rhs.isAppOfArity ``Lean.Order.PreservesSup.upperAdjoint 7
        && args[2]!.isAppOfArity ``Program.FrameWP.frameOp 1 do
      let h ← mkFreshExprSyntheticOpaqueMVar φ; return (h, h.mvarId!)
    let X := args[3]!
    let isEmp := R.isAppOf ``MProp.emp
    let heq ← if isEmp then
        mkAppNS (← mkConstS ``Program.FrameWP.upperAdjoint_frameOp_emp) #[X, args[4]!, args[5]!, args[6]!]
      else
        mkAppNS (← mkConstS ``Program.FrameWP.upperAdjoint_frameOp_pointwise) #[R, X, args[4]!, args[5]!, args[6]!]
    let some (_, _, rhs') := (← instantiateMVarsS (← Sym.inferType heq)).eq?
      | throwError "sep frameproc: not an equation{indentExpr heq}"
    let rhs' ← shareCommon rhs'
    let φ' ← mkAppNS le #[lhs, rhs']
    let hsub ← mkFreshExprSyntheticOpaqueMVar φ'
    let hcongr ← mkAppNS (← mkConstS ``congrArg [.succ .zero, .succ .zero])
      #[mprop, mkSort .zero, rhs, rhs', ← mkAppNS le #[lhs], heq]
    let hφ ← mkAppNS (← mkConstS ``Eq.mpr [.zero]) #[φ, φ', hcongr, hsub]
    return (hφ, hsub.mvarId!)

/-- Phase one: always frame, at the goal's own state. -/
meta def sepFrameProc : FrameInferenceProc := fun i =>
  return .commit i.unframedApp.excessArgs (sepFrameSplit i)

/-- Active under `open scoped Program.FrameWP`, together with the instance. -/
@[scoped frameproc] meta def sepFP : FrameProc where
  prog := ``Directive
  opHead := ``Program.FrameWP.frameOp
  mkOpAppM := fun _ => pure (mkConst ``Program.FrameWP.frameOp)
  mkResourceTy := fun _ => pure (mkApp (mkConst ``MProp) (mkNatLit 64))
  proc := sepFrameProc

end Program.FrameWP

/-! ## Smoke tests

A store and a register write with the goal owning exactly the slot; two
stores into two slots, where each store's footprint is one slot and the other
slot is the frame `solveSepEq` finds; and a store followed by an `add` from
the other slot. -/

section Smoke

open Kraken.X64.Parser

attribute [local grind .] Lean.Order.PartialOrder.rel_refl

example [Host] [FunDecls] (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f => bs.AtM (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt) ⦄
      parse("movq %rax, 136(%rdx)\nmovq $1, %rbx")
    ⦃ fun _ r z f => (Int.toBytes 8 (r.get64 .rax).toInt).AtM
        (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt) ⦄ := by
  kvcgen64 with finish

example [Host] [FunDecls] (bs cs : List UInt8) (hb : bs.length = 8) (hc : cs.length = 8) :
    ⦃ fun r z f => bs.AtM (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt)
        ∗ cs.AtM (r.get64 .rdx + BitVec.ofInt 64 (144 : Int64).toInt) ⦄
      parse("movq %rax, 136(%rdx)\nmovq %rbx, 144(%rdx)")
    ⦃ fun _ r z f => (Int.toBytes 8 (r.get64 .rax).toInt).AtM
          (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt)
        ∗ (Int.toBytes 8 (r.get64 .rbx).toInt).AtM
          (r.get64 .rdx + BitVec.ofInt 64 (144 : Int64).toInt) ⦄ := by
  kvcgen64 with finish

example [Host] [FunDecls] (bs cs : List UInt8) (hb : bs.length = 8) (hc : cs.length = 8) :
    ⦃ fun r z f => bs.AtM (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt)
        ∗ cs.AtM (r.get64 .rdx + BitVec.ofInt 64 (144 : Int64).toInt) ⦄
      parse("movq %rax, 136(%rdx)\naddq 144(%rdx), %rbx")
    ⦃ fun _ r z f => (Int.toBytes 8 (r.get64 .rax).toInt).AtM
          (r.get64 .rdx + BitVec.ofInt 64 (136 : Int64).toInt)
        ∗ cs.AtM (r.get64 .rdx + BitVec.ofInt 64 (144 : Int64).toInt) ⦄ := by
  kvcgen64 with finish

end Smoke
