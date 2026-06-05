/-
Kraken - Example Programs

This demonstrates our proof style using the `kstep` stepping tactic that
advances through ASM instructions. This is a work in progress, and is the result
of several experiments, which can be found in the Git history at revision
a556993a and earlier.

For semantics, see Kraken/Semantics.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Kraken.Tactics
import Kraken.Parser
import Kraken.Eval

open Kraken.Parser

-- TODO: a large amount of this is intended to be generic and should omve to
-- Tactics.lean

unif_hint (w : Width) where
  w =?= Width.W8 |- Width.type w =?= BitVec 8

unif_hint (w : Width) where
  w =?= Width.W16 |- Width.type w =?= BitVec 16

unif_hint (w : Width) where
  w =?= Width.W32 |- Width.type w =?= BitVec 32

unif_hint (w : Width) where
  w =?= Width.W64 |- Width.type w =?= BitVec 64

--------------------------------------------------------------------------------

open Lean Meta Sym Sym.DSimp
open Elab Tactic

partial def peelLambdaLets (f : Expr) (args : Array Expr) (fvars : Array Expr) (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  -- (fun y => let x = e1 in e2) () ~~> let x = e1 in (fun y => e2) ()
  match f with
  | .lam binderName binderType body binderInfo =>
    match body with
    | .letE letName letType letVal letBody _ =>
      if !letType.hasLooseBVar 0 && !letVal.hasLooseBVar 0 then
        withLetDecl letName letType letVal fun fvarLet => do
          -- substitute open variable x for 0 in e2, shifting all other variables by 1
          let instBody : Expr := letBody.instantiate1 fvarLet
          -- meaning we can close in DeBruijn directly
          let newLambda := .lam binderName binderType instBody binderInfo
          -- and add our open variable to the list of variables to be folded over
          peelLambdaLets newLambda args (fvars.push fvarLet) k
      else
        k (mkAppN f args) fvars
    | _ => k (mkAppN f args) fvars
  | _ => k (mkAppN f args) fvars

partial def peelLets (e : Expr) (fvars : Array Expr) (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  match e with
  | .letE name type val body _ =>
    withLetDecl name type val fun fvar =>
      peelLets (body.instantiate1 fvar) (fvars.push fvar) k
  | _ =>
    if e.isApp && e.getAppFn.isLambda then
      peelLambdaLets e.getAppFn e.getAppArgs fvars k
    else
      k e fvars

partial def peelArgsLets (args : Array Expr) (i : Nat) (peeled : Array Expr) (fvars : Array Expr) (k : Array Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  if h : i < args.size then
    let arg := args[i]
    peelLets arg fvars fun arg' fvars' =>
      peelArgsLets args (i + 1) (peeled.push arg') fvars' k
  else
    k peeled fvars

def kdeltaBetaOnly (targets: List Name) : DSimproc := fun e => do
  -- This focuses on application nodes.
  unless e.isApp && targets.any e.getAppFn'.isConstOf do return .rfl

  let f := e.getAppFn'
  let args := e.getAppArgs

  -- In order to unblock reduction, Meta.unfoldDefinition will happily inline
  -- away let-bindings to make e.g. a constructor appear as an argument to a
  -- match recursor. We intervene ahead of time, and hoist the lets that appear in
  -- argument position, which we know for a fact happens quite a bunch in our
  -- semantics. Concretely: `f (let x = ... in arg)` => `let x = ... in f arg`.
  peelArgsLets args 0 #[] #[] fun (args : Array Expr) (fvars : Array Expr) => do

    if f.isConstOf ``Effects.All && args[1]!.isApp && args[1]!.getAppFn'.isConstOf ``Directives.interp then
      -- Finding a node of the form `Effects.All ... (Directives.interp ...)`
      -- means that we are ready to step through. We manually force reduction of
      -- Directives.interp (since it is *not* is our list of targets), then let
      -- everything simplify until we're called again.
      let some arg1 ← Meta.unfoldDefinition? args[1]! true | throwError "can't unfold Directives.interp"
      let e := mkAppN f (args.set! 1 arg1)
      let e' ← shareCommon e
      let e'' ← mkLetFVars fvars e'
      return .step e''
      -- TODO: we could here have a post := in the simproc that forces the
      -- result to be .step ... (done := true) to prevent the next unrolling of
      -- Directives.interp from being applied. This would essentially allow
      -- implementing a kstep1 tactic (and leave it to done := false to keep
      -- stepping until something blocks).

      -- Essentially this behavior allows us to keep reducing and stepping,
      -- until we have no steps left to apply and YET the goal has landed us
      -- back on something that is neither Effects.All ... (Directives.interp
      -- ...), nor Effects.All ... (require_exec_access ...), handled in the
      -- case below.
    else
      -- Application, *sans* the let-bindings in the arguments.
      let e_rebuilt := mkAppN f args
      -- Remember that `Meta.unfoldDefinition` is "smart" and wants to see the whole
      -- application node `f ...` before deciding whether it's worth doing a step of
      -- delta and replacing `f` with its definition.
      if let some e' ← Meta.unfoldDefinition? e_rebuilt true then
        /- let step := (← get).numSteps -/
        /- logInfo m!"deltaBetaOnly {step}: {e_rebuilt}\nunfolds to:{e'}" -/
        let e' ← shareCommon e'
        let e'' ← betaRevS e'.getAppFn e'.getAppRevArgs
        let e'' ← mkLetFVars fvars e''
        /- logInfo m!"deltaBetaOnly {step}: {e}\nunfolds to:{e'}\nreduces to: {e''}" -/
        return .step e''
      else if fvars.size > 0 then
        -- Can't reduce application, but we should at least hoist the lets!
        let e ← mkLetFVars fvars e_rebuilt
        return .step e
      else
        -- Really nothing to do here.
        return .rfl

def gimmickId (p: Prop): Prop := p

def gimmick {p: Prop} (h: gimmickId p): p := by
  simp [gimmickId] at h
  assumption

def gimmickInv {p: Prop} (h: p): gimmickId p := by
  simp [gimmickId]
  assumption

-- Debugging the reduction steps: to easily have a marker that tells us when we've hit the top-level
-- term, we assume prior to running `kstep`, the user does `apply gimmick`. (This also avoids having
-- to reason about whether we're at the top-level term or not -- we never are.)
def klog : DSimproc := fun e => do
  -- We log every top-level term get a trace of the various states of the dsimp
  -- call.
  let s := (← get).numSteps
  /- if s = 789 then -/
  /-   return .rfl (done := true) -/
  if e.isApp && e.getAppFn'.isConstOf ``gimmickId then
    logInfo m!"klog: step {s} visiting\n{e.getAppRevArgs[0]!}"
  return .rfl


syntax (name := symKStep) "kstep " : grind

def kdsimpMatch: DSimproc := fun e => do
  let some e' ← reduceRecMatcher? e | return .rfl
  -- Iota-reduction may expose kernel `Expr.proj` terms via struct-eta,
  -- which the structural simplifier cannot consume directly.
  let e'' ← Sym.foldProjs e'
  if isSameExpr e e'' then
    return .rfl
  else
    return .step (← share e'')

def kbeta: DSimproc := fun e => do
  unless e.isApp do return .rfl
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then
    let e' ← betaRevS f e.getAppRevArgs
    /- let step := (← get).numSteps -/
    /- logInfo m!"kbeta {step}: {e}\nreduces to\n{e'}" -/
    return .step e'
  else
    return .rfl

def kdsimpProj : DSimproc := fun e => do
  let f := e.getAppFn
  let .const declName _ := f | return .rfl
  let some _projInfo ← getProjectionFnInfo? declName | return .rfl
  let reduceProjCont? (e? : Option Expr) : DSimpM Result := do
    match e? with
    | none   => return .rfl
    | some e =>
      match (← reduceProj? e.getAppFn) with
      | some f => return .step (← shareCommon (mkAppN f e.getAppArgs))
      | none   => return .rfl
  -- TODO: special support for instances?
  reduceProjCont? (← unfoldDefinition? e)

def kLiftLets : DSimproc := fun e => do
  -- We only lift lets to the top-level (which is always an application of
  -- Effects.all)
  unless e.isApp && e.getAppFn'.isConstOf ``Effects.All do return .rfl

  let (es, st) ← ExtractLets.extract #[e] |>.run {} |>.run' {} |>.run { givenNames := [] }
  unless st.decls.size > 0 do return .rfl

  let e' := Meta.ExtractLets.mkLetDecls st.decls es[0]!
  let e' ← Sym.share e'
  /- logInfo m!"liftLets produces {e'}" -/
  return .step e'

-- TODO: make our tactic take an optional config to aid debugging
@[grind_tactic symKStep]
def evalSymKStep : Grind.GrindTactic :=
  fun _stx : Syntax => do
  -- A `sym` tactic operates over a pair of the grind state and an MVarId
  let gGoal : Grind.Goal ← Grind.getMainGoal
  let mvarId := gGoal.mvarId

  -- Apply the debug gimmick. We actually *do* expect the goal to be in this form (see comment in
  -- kdeltaBetaOnly).
  let gimmickRule ← mkBackwardRuleFromDecl ``gimmick
  let mvarId ← Grind.liftGrindM (do
    let .goals [mvarId] ← gimmickRule.apply mvarId | failure
    pure mvarId
  )

  let goal ← mvarId.getType

  let decls := [
    ``Reg.interp, ``Reg64s.get, ``Reg.base, ``Reg.offset, ``MachineData.set,
    ``MachineData.setReg, ``Reg64s.set, ``Width.type, ``Width.bits,
    ``Width.bytes,
    ``Width.bytesv,
    ``Reg64s.get64, ``Reg64s.set64, ``BitVec.drop, ``BitVec.take,
    ``BitVec.extractLsb', ``BitVec.truncate, ``ConstExpr.interp,

    -- We INTENTIONALLY do not include Directives.interp -- this serves as our
    -- special marker, and one that determines whether know we can resume.
    ``Directive.interp, ``Instr.interp, ``Operation.interp,
    ``Operand.interp, ``Effects.All,
    ``ConstExpr.interp, ``RegOrMem.interp, ``Reg.interp,
    ``ShiftCountExpr.interp, ``CondCode.interp,
    ``ShiftCountExpr.interpMasked,

    -- We also do not include MachineData.store/load as we intend for those to
    -- be destructed with rw-lemmas.

    ``StatusFlags.from_result
  ]

  let goal ← Grind.liftGrindM (do
    Sym.dsimp
      (config := { maxSteps := 1000000 })
      (methods := { pre := klog >> kdeltaBetaOnly decls >> kdsimpMatch >> kdsimpProj >> kbeta})
      goal)

  -- TEMPORARY: trying to simplify binders in the goal
  /- let goal ← Meta.letToHave goal -/
  /- let goal ← Grind.liftGrindM $ shareCommon goal -/
  /- let mvarId ← mvarId.replaceTargetDefEq goal -/

  /- let simpMethods: Sym.Simp.Methods ← mkSimpMethods4 #[ ``Nat.shiftRight_zero ] -/
  /- let simpResult ← Grind.liftGrindM (Sym.simpGoal mvarId simpMethods) -/
  /- let mvarId ← Grind.liftGrindM (match simpResult with -/
  /-   | .noProgress => pure mvarId -/
  /-   | .goal mvarId => pure mvarId -/
  /-   | .closed => throwError "unexpected") -/

  let mvarId ← mvarId.replaceTargetDefEq goal

  -- Remove the gimmick debug marker.
  let gimmickRule ← mkBackwardRuleFromDecl ``gimmickInv
  let mvarId ← Grind.liftGrindM (do
    let .goals [mvarId] ← gimmickRule.apply mvarId | failure
    pure mvarId
  )

  Grind.setGoals [ { gGoal with mvarId } ]

--------------------------------------------------------------------------------

def p1 := parse("start: mov $1, %rax")

theorem Executable.directivesFromStart [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) := by
  induction prog <;> simp [Executable.directivesFromAddress,Executable.withAddresses,Layout.apply]
    
-- Super-simple example to debug tactics
example [layout : Layout] s : straightlineStep (layout p1) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  dsimp only [p1]
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  sym =>
  kstep
  tactic =>
  decide

  /- simp [Instr.interp,Operation.interp,Operand.interp,MachineData.set] -/
  /- simp [MachineData.setReg,Reg64s.set,Reg64s.set64,ConstExpr.interp] -/
  /- simp [Width.bits] -/

  /- simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,eval_imm,set_reg_or_mem,next,MachineState.setReg,Registers.set] -/

def swap : Program := parse("
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax")

theorem swap_correct [layout : Layout] (d : MachineData) :
      Eventually (straightlineStep (layout swap))
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  dsimp [swap]
  apply step_cps
  dsimp only [straightlineStep, Executable.straightline, Directives.interp]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]

  sym =>
  kstep
  tactic =>
  simp (zeta:=false) -- TODO: figure out why `simp` gives us two `Eventually`s
  lift_lets
  intros
  constructor
  <;> apply Eventually.done
  <;> bv_decide

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2 : Program := parse("
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax")

-- Example 2: stepping through both straightline and control instructions
example [layout : Layout] (s : MachineData): Eventually (straightlineStep (layout p2)) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  dsimp [p2]
  apply step_cps
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  sym =>
  kstep
  tactic =>
  lift_lets
  -- TODO: I would like `kstep` to do this automatically
  intros v1 v2 v status
  -- TODO: I would like `kstep` to try `decide`-ing conditionals that block reduction (or `grind`-ing)
  have: v1 = 0 := by decide
  simp [this]

  sym =>
  kstep
  tactic =>
  apply Eventually.done
  bv_decide

-- Example 3 commented out until we figure out how to parse concrete syntax.

-- TODO: restore p3

/- def p3: Program := parse("
init:
  mov $2 %rdx             # rdx: current result = 2
start:
  sub $0 %rbx             # TEST: zf = (rbx == 0)
  jz _end                 # end loop if rbx == 0 (a.k.a. « while rbx >= 0 »)
  .mulx %rdx %rdx %rax    # BODY: rdx := rdx * rdx
  sub 1 %rbx              # rbx -= 1
  jmp start               # go back to test & loop body
_end:
  nop
")

def p3_spec (s: MachineState): Nat := 2^(2^s.1.regs.rbx.toNat)

set_option maxHeartbeats 4000000 in
theorem p3_correct [Layout] (initial: MachineState):
    p3_spec initial < 2^64 →
    (layout ("init", 0) = initial.2) →
    eventually p3 (fun s => s.1.regs.rdx.toNat == p3_spec initial ∧ s.1.regs.rax == 0) initial :=
  by
  sorry -- simp times out due to larger Reg enum (64 constructors with aliased registers) -/
  /-
    intros h_bounds h_rip
    simp [p3]
    -- First step sets rdx = 2
    apply step_cps
    step_one
    rw [h_rip]
    clear h_rip
    simp

    -- Loop invariant introduction
    apply reg_dec_loop p3 _ _ (fun i s => s.rip = 1 ∧ s.regs.rbx.toNat = i ∧ i ≤ initial.regs.rbx.toNat ∧ s.regs.rdx.toNat = 2^(2^(initial.regs.rbx.toNat - i))) initial.regs.rbx.toNat
    constructor
    . simp
    . constructor
      -- Invariant at index 0 ==> post
      . intros state inv
        rcases inv with ⟨ h_rip, h_rbx_zero, h_rbx_le, h_inv ⟩
        -- Step through a few program steps
        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp
        apply step_cps
        step_one
        have : state.regs.rbx.toNat = 0 := by grind
        simp [this]
        apply step_cps
        step_one
        apply eventually.done
        simp
        -- Now functional correctness for initial invariant
        simp [p3_spec]
        grind

      -- Invariant preserved
      . intro state k h_k_nonzero inv
        rcases inv with ⟨ h_rip, h_rbx_is_k, h_rbx_le, h_inv ⟩

        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp

        apply step_cps
        step_one
        have h_k_ne : k ≠ 0 := by grind
        -- state.regs.rbx.toNat = k and toNat < 2^64 for UInt64
        have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (state.regs.rbx.toNat_lt)
        -- Simplify all the Int64.toUInt64 terms
        simp_all only [ne_eq, not_false_eq_true]
        -- Prove the if-condition is false: UInt64.ofInt ↑k ≠ 0 when k ≠ 0
        have h_cond : UInt64.ofInt (k : Int) ≠ 0 := UInt64_ofInt_natCast_ne_zero k h_k_lt h_k_ne
        rw [if_neg h_cond]




        apply step_cps
        step_one
        apply step_cps
        step_one
        apply step_cps
        step_one
        apply eventually.done

        -- Goals for invariant preservation
        constructor
        . simp -- back to correct address
        . match h_state:state.regs.rbx, h_init:initial.regs.rbx with
          | ⟨v_s⟩, ⟨v_i⟩ =>
            have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (by rw [h_state]; exact v_s.isLt)
            have h_init_lt : v_i.toNat < 2^64 := v_i.isLt
            simp [h_state, h_init, p3_spec, Reg.width, UInt64.ofInt, UInt64.ofNat, UInt64.toNat_ofNat] at *
            constructor
            . omega
            . constructor
              . omega
              . rw [h_inv]
                have h_vi_k : v_i.toNat - (k - 1) = (v_i.toNat - k) + 1 := by omega
                rw [h_vi_k, Nat.mod_eq_of_lt]
                . rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                . apply Nat.lt_of_le_of_lt _ h_bounds
                  rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                  apply Nat.pow_le_pow_right (by decide)
                  apply Nat.pow_le_pow_right (by decide)
                  omega
  -/

def p4 := eval% parse("start: mov $2, %rax
dec %rax")

-- Super-simple example to debug tactics
example [layout : Layout] s : straightlineStep (layout p4) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p4
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  -- TODO: this preamble above is a good form for what we need (although I'd
  -- also like registers to be exploded). Can we move it to a tactic? Like
  -- `kprologue p4` or something. I did not manage because of the =>, and I got
  -- into a rabbit hole of syntax macros and weird syntactic classes (elimExpr
  -- vs ident) and gave up.

  sym =>
  kstep
  intros
  tactic =>
  decide

/- Examples -/

def p5 := parse("start: mov $2, %rax
dec %rax
start2:
dec %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.all true -/

example [layout : Layout] s : straightlineStep (layout p5) (s, layout.start) (fun s => s.1.regs.rax = 0) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p5
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  -- TODO: same remark, lift this preamble

  sym => 
  kstep
  tactic =>
  bv_decide

def p6 := parse("push %rax
mov $0, %rax
pop %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.coercions false -/
/- set_option pp.all true -/

theorem simpleAlignedStore64 (s : MachineData) (addr : BitVec 64) (v : BitVec 64) (ret: MachineData → Effects)
  (hAligned: addr % 8 = 0)
  (hContains: UInt64.ofBitVec addr ∈ s.dmem):
  MachineData.store s addr v ret =
  require_write_access addr Width.W64 (fun _unit =>
    ret { s with dmem := s.dmem.insert (UInt64.ofBitVec addr) (UInt64.ofBitVec v) }) :=
by
  simp only [MachineData.store,Width.bytesv,Width.bytes]
  have: addr % 8#64 = 0#64 := by grind
  simp only [this]
  have: UInt64.ofBitVec (addr &&& ~~~0b111#64) = UInt64.ofBitVec addr := by
    bv_decide
  rw [this]
  have: addr &&& 7#64 = 0 := by bv_decide
  simp [this,Width.bits]
  -- TODO: lift and generalize this
  have (old v: BitVec 64): BitVec.replace old 0 v = v := by
    simp [BitVec.replace,BitVec.drop]
    bv_decide
  simp [this]
  rw [Std.ExtHashMap.getElem?_eq_some_getElem! hContains]

-- AE, JP: it would be nice to eliminate CPS from the post and say that the post
-- is just called with the value that is loaded
theorem simpleAlignedLoad64 (s : MachineData) (addr : BitVec 64) (ret: BitVec 64 → MachineData → Effects)
  (hAligned: addr % 8 = 0)
  (hContains: UInt64.ofBitVec addr ∈ s.dmem):
  MachineData.load s addr .W64 ret =
  require_read_access addr Width.W64 (fun _unit =>
    ret (s.dmem[UInt64.ofBitVec addr]!.toBitVec) s) :=
by
  simp only [MachineData.load,Width.bytesv,Width.bytes]
  -- TODO: figure out why `simp` cannot deduce the fact below; setting
  -- pp.coercions to false reveals that one version of the lemma uses
  -- `OfNat.ofNat` to produce a BitVec, while the other uses `OfNat.ofNat` to
  -- produce a Nat, followed by a call to `BitVec.ofNat`, and there appears to
  -- be no simp-rule that would show that one can be rewritten into the other.
  have: addr % 8#64 = 0#64 := by grind
  simp only [this]
  -- TODO: perhaps there should be a rule for this that can be in a simpset or a
  -- grindset to facilitate this sort of reasoning
  have: UInt64.ofBitVec (addr &&& ~~~0b111#64) = UInt64.ofBitVec addr := by
    bv_decide
  rw [this]
  have: addr &&& 7#64 = 0 := by bv_decide
  simp [this,Width.bits]
  rw [Std.ExtHashMap.getElem?_eq_some_getElem! hContains]

example [layout : Layout] (s: MachineData)
  (hAlign: s.regs.rsp % 8 = 0)
  (hContains: forall x, x ∈ s.dmem)
  : straightlineStep (layout p6) (s, layout.start) (fun s' => s'.1.regs.rax = s.regs.rax) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp_old rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  simp at hAlign
  simp at hContains
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p6
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  -- An example of how to do some memory reasoning.

  sym => 
  kstep
  tactic =>
  lift_lets
  intros rsp_store v
  -- TODO: I would like kstep to try to decide this automatically
  have: rsp_store % 8 = 0 := by bv_decide
  rw [simpleAlignedStore64]
  <;> try grind
  sym =>
  kstep
  tactic =>
  lift_lets
  intros rsp
  intros
  rw [simpleAlignedLoad64]
  <;> try grind
  sym =>
  kstep
  tactic =>
  intros
  simp [rsp]

/- def bigp := parseFile("./ecc-secp521r1-modp.S") -/

/- set_option maxRecDepth 4000 -/
/- set_option maxHeartbeats 2000000 -/

/- example [layout : Layout] s -/ 
/-   (hAlign: s.regs.rsp % 8 = 0) -/
/-   (hContains: forall x, x ∈ s.dmem) -/
/- : straightlineStep (layout bigp) (s, layout.start) (fun s => s.1.regs.rax = 0) := by -/
/-   -- Refine the state to make registers apparent -- note that `cases` consumes -/
/-   -- the hypothesis, and substitutes it, so we make a copy of it to have a -/
/-   -- refined state in the hypotheses, not the goal. -/
/-   let ss := s -/
/-   change (straightlineStep _ (ss, _) _) -/
/-   cases s with | mk regs flags mem => -/
/-   cases regs with | mk rax => -/
/-   -- Rewrite the program to make layout, addresses, etc. apparent -/
/-   delta bigp -/
/-   dsimp only [straightlineStep,Executable.straightline] -/
/-   rw [Executable.directivesFromStart] -/
/-   simp [List.mapIdx,List.mapIdx.go] -/

/-   sym => -/ 
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedLoad64] -/
/-   <;> try grind -/

/-   rotate_right 1 -/
/-   . sorry -- need additional alignment hypotheses here -/
/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro count -/
/-   have: count ≠ 0 := by bv_decide -/
/-   simp [this] -/
  
/-   sym => -/
/-   kstep -/
/-   intro -/
/-   tactic => -/
/-   have : count = 55 := by decide -/
/-   simp [this] -/
  
/-   sym => -/
/-   kstep -/
/-   intros -/
/-   kstep -/
/-   sorry -/
  /- tactic => -/
  /- lift_lets -/
  /- revert -/
  /- sorry -/

