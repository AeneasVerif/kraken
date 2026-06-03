/-
Kraken - Example Programs

Test programs demonstrating the assembly interpreter.
Compatible with Lean 4.22.0+.

For semantics, see Kraken/Semantics.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Kraken.Tactics
import Kraken.Parser
import Kraken.Eval

open Kraken.Parser

def p1 := parse("start: mov $1, %rax")

theorem Executable.directivesFromStart [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) := by
  induction prog <;> simp [Executable.directivesFromAddress,Executable.withAddresses,Layout.apply]
    

-- Super-simple example to debug tactics
example [layout : Layout] s : Step1 (layout p1) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  dsimp only [p1]
  dsimp only [Step1,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  dsimp only [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp]
  dsimp only [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp,require_exec_access]
  simp (ground:=True)
  dsimp only [Effects.All]
  rfl

  /- simp [Instr.interp,Operation.interp,Operand.interp,MachineData.set] -/
  /- simp [MachineData.setReg,Reg64s.set,Reg64s.set64,ConstExpr.interp] -/
  /- simp [Width.bits] -/

  /- simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,eval_imm,set_reg_or_mem,next,MachineState.setReg,Registers.set] -/

def swap : Program := parse("
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax")

theorem swap_correct [layout : Layout] (d : MachineData) :
      Eventually (layout swap)
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  dsimp [swap]
  apply step_cps
  dsimp only [Step1, Executable.straightline, Directives.interp]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]
  -- TODO It would be nice to progress instruction by instruction instead of all at once, like below.
  dsimp only [Directives.interp, Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp]
  dsimp [MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64, Effects.All]
  intros _af1 _af2 _af3
  apply Eventually.done
  simp (ground:=True)
  dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset]
  dsimp only [BitVec.drop, BitVec.take, Width.bits]
  dsimp only [Nat.sub_zero] -- FIXME: needed after nightly
  simp only [BitVec.extractLsb'_eq_self] -- FIXME: needed after nightly
  bv_decide

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2 : Program := eval% [
  .label "start",
  .instr ⟨ .W64, .W64, .mov Reg.rax (.imm (.int64 1)) ⟩,
  .instr ⟨ .W64, .W64, .xor Reg.rax Reg.rax ⟩,
  .instr ⟨ .W64, .W64, .jcc .nz "start" ⟩,
  .instr ⟨ .W64, .W64, .mov Reg.rax (.imm (.int64 2)) ⟩,
]
def p2' : Program := parse("
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax")

-- Example 2: stepping through both straightline and control instructions
example [layout : Layout] (s : MachineData): Eventually (layout p2) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  dsimp [p2]
  apply step_cps
  dsimp only [Step1,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  dsimp only [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp]
  dsimp only [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp,CondCode.interp,StatusFlags.from_result, Effects.All]
  simp only [Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.truncate_eq_setWidth, BitVec.xor_self, BitVec.zero_eq,
    BEq.rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, BitVec.msb_zero]
  intros _af
  apply Eventually.done
  simp (ground:=True)
  rfl -- FIXME: needed after nightly

-- Example 3 commented out until we figure out how to parse concrete syntax.
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
example [layout : Layout] s : Step1 (layout p4) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (Step1 _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p4
  dsimp only [Step1,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  -- We now have a goal of the form Directives.interp [ ..., ... ]. Time to do
  -- some stepping.
  dsimp (zeta:=false)(iota:=true) only [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,ConstExpr.interp,RegOrMem.interp,Reg.interp,Reg64s.get,Reg.base,Reg.offset,MachineData.set,MachineData.setReg,Reg64s.set,Width.type,Width.bits,Effects.All]
  lift_lets
  dsimp (zeta:=false)(beta:=true)(eta:=false)(iota:=true)(proj:=true) only [Reg64s.get64,Reg64s.set64,BitVec.drop,BitVec.take,ss,Effects.All] -- reduces UInt64.toBitVec but leaves let binders behind and gets stuck confused on it
  intros rax1
  lift_lets; intros t -- unfortunately a separte tactic rather than a simp flag
  -- simp [MachineData.regs,Reg64s.set64,Reg64s.get64,ss] at t -- made no progress for some reason
  dsimp (zeta:=false)(beta:=false)(eta:=false)(iota:=false)(proj:=true) only [Reg64s.set64,Reg64s.get64,ss,t]
  -- now just bashing because rax1 in context is already bad
  simp [rax1]
  simp (ground:=true) (decide:=true)

/- Experiments using SymM: 1/N -/

open Lean Meta Elab Tactic Sym

def silly (mvarId: MVarId): SymM Unit := do
  let rflRule ← mkBackwardRuleFromDecl ``Eq.refl
  let _ ← rflRule.apply mvarId

elab "silly " : tactic => do
  let mvarId ← getMainGoal
  SymM.run do silly mvarId

example : 2 = 2 := by
  silly

/- Experiments using SymM: 2/N -/

def f (x: Nat) (y: Nat): Prop := x = y

def f_thm x y (h: x = y): f x y := by
  simp [f]; assumption

def silly2 (mvarId: MVarId): SymM Unit := do
  let goal ← mvarId.getType
  -- match goal with f ?x ?y
  let_expr ent@f x y := goal | throwError "goal not of the form f x y"
  -- apply f_thm
  let thmRule ← mkBackwardRuleFromDecl ``f_thm
  let .goals [ mvarId ] ← thmRule.apply mvarId | throwError "f_thm did not apply"
  -- rfl
  let rflRule ← mkBackwardRuleFromDecl ``Eq.refl
  let .goals [] ← rflRule.apply mvarId | throwError "rfl did not apply"
  /- let finalSimpMethods ← mkMethods #[] -/
  /- let .closed ← Sym.simpGoal mvarId finalSimpMethods {} | throwError "simpGoal did not close" -/
  /- return -/

elab "silly2 " : tactic => do
  let mvarId ← getMainGoal
  SymM.run do silly2 mvarId

example : f 4 (2 + 2) := by
  apply f_thm
  apply Eq.refl

example : f 4 4 := by
  silly2

/- Experiments using SymM: 3/N -/

def of_bits {α} (w: UInt64) (bits: List Bool) (k: UInt64 → α): α :=
  match bits with
  | b :: bits =>
    let b: UInt64 := if b then 1 else 0
    of_bits (w <<< 1 + b) bits k
  | [] =>
    k w

/- def silly3: dead-end, deleted, see git history -/


/- Experiments using SymM: 4/N

   This time, relying on the reduction machine provided by Sebastian Graf.
   Original code below.
-/

/--
Repeatedly reduces head redexes in `e`, cycling through the following reductions until
no further progress is made:

1. **Beta**: `(fun x₁ ... xₘ => b) a₁ ... aₙ` → `b[a₁/x₁, aₘ/xₘ] aₘ₊₁ ... aₙ`
2. **Iota**: `MyType.casesOn (MyType.ctor args) alts` → `altᵢ args`
   (matcher/recursor applied to a constructor, at reducible transparency)
3. **Proj-reduction**: `⟨a, b, c⟩.1` → `a` (kernel `.proj` nodes)
4. **Projection delta**: `Struct.field x` → `x.5` (unfolds projection *functions*,
   progress only if followed by proj-reduction)

Returns `none` when no reduction was possible. Maintains maximal sharing via `shareCommonInc`.
-/
meta partial def reduceHead? (e : Expr) : SymM (Option Expr) :=
  withReducible <| go none e.getAppFn e.getAppRevArgs
  where
    go lastReduction f rargs := do
      match f with
      | .mdata _ f => go lastReduction f rargs
      | .app f a => go lastReduction f (rargs.push a)
      | .lam .. =>
        if rargs.size = 0 then return lastReduction
        let e' := f.betaRev rargs
        let e' ← Sym.shareCommonInc e'
        go (some e') e'.getAppFn e'.getAppRevArgs
      | .const name .. =>
        -- projections
        if ← isProjectionFn name then
          let some e' ← Meta.unfoldDefinition? (mkAppRev f rargs) | return lastReduction
          let e' ← Sym.shareCommonInc e'
          go lastReduction e'.getAppFn e'.getAppRevArgs  -- intentional lastReduction! see docstring
        -- iota reduction: match/recursor with concrete discriminant
        else if let some e' ← liftMetaM <| reduceRecMatcher? (mkAppRev f rargs) then
          let e' ← Sym.shareCommonInc e'
          go (some e') e'.getAppFn e'.getAppRevArgs
        else
          pure lastReduction
      | .proj .. => match ← reduceProj? f with
        | some f' =>
          let e' := mkAppRev f' rargs
          let e' ← Sym.shareCommonInc e'
          go (some e') e'.getAppFn e'.getAppRevArgs
        | none    => pure lastReduction
      | _ => pure lastReduction

def reduceApp (e: Expr) : SymM Expr :=
  withReducible <|
  let hd := e.getAppFn
  let rargs := e.getAppRevArgs
  let e := hd.betaRev rargs
  -- TODO: why is sharing not preserved here?
  shareCommonInc e

def debug: Sym.Simp.Simproc := fun e => do
  logInfo m!"simp (not dsimp!): {e}"
  return .rfl

/- simp using the provided methods *and* ground := True -/
def mkSimpMethods4 (declNames : Array Name) : MetaM Sym.Simp.Methods := do
  let rewrite ← Sym.mkSimprocFor declNames Sym.Simp.dischargeSimpSelf
  return {
    post := debug.andThen (rewrite.andThen Sym.Simp.evalGround)
  }

partial def silly4 (mvarId: MVarId): SymM MVarId := do
  let simpMethods ← mkSimpMethods4 #[``ite_cond_eq_true, ``ite_cond_eq_false]
  let goal_is_of_bits (goal: Expr): SymM Bool := do
    let_expr of_bits _ _ bits _ := goal | throwError "ERROR: goal is not of the form of_bits"
    let_expr List.cons _ _ _ := bits | return false
    pure true

  -- Assumes `goal_is_of_bits`.
  let rec go (i: Nat) (mvarId: MVarId): SymM MVarId := do
    let goal ← mvarId.getType
    let is_cons ← goal_is_of_bits goal
    -- NOTE: Symp.simpGoal does not work -- it reduces too aggressively; failed
    -- attempt, below:
    -- let .goal mvarId ← Sym.simpGoal mvarId unfoldMethods | throwError "can't unfold"
    -- WORKING:
    -- TODO: just unfold the head?
    -- TODO: have something more generic that finds *any* application whose head
    -- is a definition from our semantics -- settle on a reduction strategy
    let some goal ← Meta.unfoldDefinition? goal | throwError "can't unfold"
    let mvarId ← mvarId.replaceTargetDefEq (← reduceApp goal)

    -- DONE: we just reduced the empty list case and now the user can deal with
    -- the post-condition themselves
    if not is_cons then
      return mvarId

    -- CONS CASE: we have binders to introduce
    -- FIXME: no progress made by simp here; we want to simp in the goal since
    -- we do not have simp at value yet.
    -- TODO: try simp discharger
    -- https://leanprover.zulipchat.com/#narrow/channel/594054-SymM-users/topic/simp.20with.20discharger.3F/near/591796469
    -- to basically call simp with (ground := True)
    let mvarId ← match ← Sym.simpGoal mvarId simpMethods with
      | .noProgress => pure mvarId
      | .goal mvarId => pure mvarId
      | .closed => throwError "unexpected"
    let .goal _ mvarId ← Sym.intros mvarId #[ Name.mkSimple (s!"bit{i}") ] | throwError "nothing to intros"
    go (i + 1) mvarId
  go 0 mvarId

elab "silly4 " : tactic => do
  let mvarId ← getMainGoal
  let mvarId ← SymM.run do silly4 mvarId
  replaceMainGoal [ mvarId ]

/- set_option pp.all true -/
      
example : of_bits 0 [ true, false, true ] (fun r => r = 5) := by
  silly4
  bv_decide

/- Experiments using SymM: 5/N -/

def myUnfold (declName: Name) (lvls: List Level): SymM Expr := do
  let some cinfo := (← getEnv).find? declName | throwError "oh noes"
  -- check smart unfolding only after `getUnfoldableConstNoEx?` because smart unfoldings have a
  -- significant chance of not existing and `Environment.contains` misses are more costly
  if smartUnfolding.get (← getOptions) && (← getEnv).contains (mkSmartUnfoldingNameFor declName) then
    throwError "oh noes 2"
  else
    unless cinfo.hasValue do
      if cinfo.isAxiom then
        recordUnfoldAxiom cinfo.name
      throwError "oh noes 3"
    if cinfo.levelParams.length != lvls.length then
      throwError "oh noes 4"
    else
      let e := instantiateValueLevelParams cinfo lvls
      recordUnfold declName
      e

def reallyUnfoldAndApp (hd: Expr) (rargs: Array Expr) : SymM Expr :=
  withReducible <| do
  let some hd ← withOptions (smartUnfolding.set · false) (Meta.unfoldDefinition? hd true) | throwError s!"can't unfold definition: {hd}"
  /- let hd ← myUnfold declName us -/
  let e := hd.betaRev rargs
  shareCommonInc e

def reallyReduceApp (e: Expr) : SymM Expr :=
  withReducible <| do
  let hd := e.getAppFn
  let rargs := e.getAppRevArgs
  reallyUnfoldAndApp hd rargs

partial def reduceOne (e : Expr) (stop_: Name → Bool) : SymM Expr :=
  withReducible <| go none e.getAppFn e.getAppRevArgs
  where
    go lastReduction f rargs := do
      let fallback : SymM Expr := match lastReduction with
        | some e' => pure e'
        | none => throwError s!"reduceOne failed at: {mkAppRev f rargs}"
      match f with
      | .mdata _ f => go lastReduction f rargs
      | .app f a => go lastReduction f (rargs.push a)
      | .lam .. =>
        if rargs.size = 0 then fallback
        else
          let e' := f.betaRev rargs
          let e' ← Sym.shareCommonInc e'
          go (some e') e'.getAppFn e'.getAppRevArgs
      | .const name _lvls =>
        if stop_ name && lastReduction.isSome then
          fallback
        else if ← isProjectionFn name then
          -- projections
          let some e' ← Meta.unfoldDefinition? (mkAppRev f rargs) true | fallback
          let e' ← Sym.shareCommonInc e'
          go (some e') e'.getAppFn e'.getAppRevArgs
        else if let some e' ← liftMetaM <| reduceRecMatcher? (mkAppRev f rargs) then
          -- iota reduction: match/recursor with concrete discriminant
          let e' ← Sym.shareCommonInc e'
          go (some e') e'.getAppFn e'.getAppRevArgs
        else if let some e' ← Meta.unfoldDefinition? (mkAppRev f rargs) true then
          let e' ← Sym.shareCommonInc e'
          go (some e') e'.getAppFn e'.getAppRevArgs
        else
          fallback
      | .proj .. => match ← reduceProj? f with
        | some f' =>
          let e' := mkAppRev f' rargs
          let e' ← Sym.shareCommonInc e'
          go (some e') e'.getAppFn e'.getAppRevArgs
        | none    => fallback
      | _ => fallback

def matchApp (f: Name) (e: Expr): Option (Expr × Array Expr) :=
  let hd := e.getAppFn
  let rargs := e.getAppRevArgs
  if hd.isConstOf f then
    some (hd, rargs)
  else
    none

-- Traverses a term looking for an application whose head is in the list of
-- target names, or a beta-redex, i.e. `app (lam ...) ...`; once found,
-- repeatedly delta-beta-reduces this application, potentially discovering more
-- delta-beta-redexes, and reducing those too, until either there is nothing
-- left to reduce, or we hit an application whose head is `name` and for which
-- `stop_ name`.
--
-- The returned boolean indicates whether such an application node was found.
partial def reduceKnownHeads (targets: List Name) (e: Expr) (stop_ := fun (_: Name) => true): SymM (Expr × Bool) := do
  -- Traverse a term, remembering if we found anything to unfold anywhere
  let rec visit: Expr → StateRefT Bool SymM Expr := fun e => do
    -- we want to reduce:
    let worthReducing :=
      -- applications of known functions
      e.isApp && targets.any e.getAppFn'.isConstOf ||
      -- beta-redexes
      e.isApp && e.getAppFn'.isLambda
    if worthReducing then
      set true
      reduceOne e stop_
    else
      traverseChildren visit e
  StateRefT'.run (visit e) false

def projSimproc : Sym.Simp.Simproc := fun e => do
  -- The problem is that the right subterm is never visited; perhaps we need to
  -- take inspiration from the reduction of projectors in CBV?
  --    https://leanprover.zulipchat.com/#narrow/channel/594054-SymM-users/topic/how.20can.20I.20tell.20Sym.2EsimpGoal.20to.20reduce.20projectors/near/593610862 
  -- but if the correct subterms are not even visited, I'm not sure what to do
  -- about this.
  -- Uncomment for verbose output
  -- logInfo m!"Current state: {← ppExpr e}"
  if e.isApp then
    let hd := e.getAppFn
    let .some (name, _) := hd.const? | return .rfl
    let isProj ← isProjectionFn name
    /- logInfo m!"Current state: {isProj} {name}" -/
    if name matches .str (.str (.str _ "Syntax") /- e.g. "Instr" -/_) /- e.g. "operation_size" -/_ && isProj then
      let some e ← Meta.unfoldDefinition? (mkAppRev hd e.getAppRevArgs) | return .rfl
      let e ← Sym.shareCommonInc e
      pure (.step e (← Meta.mkEqRefl e))
    else
      pure .rfl
  else
    pure .rfl

/- simp using the provided methods *and* ground := True -/
def mkSimpMethods (declNames : Array Name) : MetaM Sym.Simp.Methods := do
  let rewrite ← Sym.mkSimprocFor declNames Sym.Simp.dischargeSimpSelf
  return {
    -- Combine ground evaluation, projectors, and reduction of terms.
    post := Sym.Simp.evalGround.andThen (projSimproc.andThen rewrite)
  }

-- kstep: kraken stepping
partial def kstep (mvarId: MVarId): SymM MVarId := do
  let decls ← #[
    ``Reg.interp, ``Reg64s.get, ``Reg.base, ``Reg.offset, ``MachineData.set,
    ``MachineData.setReg, ``Reg64s.set, ``Width.type, ``Width.bits,
    ``Reg64s.get64, ``Reg64s.set64, ``BitVec.drop, ``BitVec.take,
    ``BitVec.extractLsb', ``BitVec.truncate, ``ConstExpr.interp
  ].mapM (fun name => do
    if let some eqns ← getEqnsFor? name then
      pure eqns
    else
      pure #[name]
  )
  let simpMethods ← mkSimpMethods decls.flatten


  -- `step` takes a goal of the form (Directives.interp ...).all and reduces the
  -- `Directives.interp` application until the next occurrence of `Directives.interp`.
  let rec step (mvarId: MVarId): SymM MVarId := do
    let goal ← mvarId.getType

    -- Reduce call to Directives.interp
    let (goal, matched) ← reduceKnownHeads [ ``Directives.interp ] goal (fun name => name = ``Directives.interp)
    if !matched then
      return mvarId

    -- This may leave an effect -- reduce the handler, if any.
    let goal ←
      match matchApp ``Effects.All goal with
      | .some (_, #[ _post, e_eff ]) =>
        -- We trigger reduction of Effects.All if its first argument is the
        -- application of a constructor (which by typing ought to be an effect
        -- constructor).
        if ← Meta.isConstructorApp e_eff then
          let (goal, true) ← reduceKnownHeads [ ``Effects.All ] goal (fun name => name = ``Directives.interp) |
            throwError "could not reduce effect handling in goal"
          pure goal
        else
          pure goal
      | _ =>
        pure goal
    -- There may be beta-redexes left still -- eliminate those if any.
    let (goal, _) ← reduceKnownHeads [] goal (fun name => name = ``Directives.interp)

    -- At this stage, we have a bunch of helpers that we need to reduce away.
    -- For convenience, we use a simp-set.
    let mvarId ← mvarId.replaceTargetDefEq goal
    let mvarId ← match ← Sym.simpGoal mvarId simpMethods with
      | .noProgress => pure mvarId
      | .goal mvarId => pure mvarId
      | .closed => throwError "unexpected"

    -- For reasons that I don't fully understand (dependent arguments, maybe?)
    -- my projection simplifier does *not* do what I want. One can try running
    -- *just* the projection simplifications here, with this:
    --
    -- let mvarId ← match ← Sym.simpGoal mvarId { post := projSimproc } with ...

    -- This is the equivalent of lift_lets, for which we have to re-establish
    -- sharing.
    let goal ← mvarId.getType
    let goal ← Meta.liftLets goal
    let goal ← shareCommonInc goal
    

    let mvarId ← mvarId.replaceTargetDefEq goal
    step mvarId

  let mvarId ← step mvarId
  
  pure mvarId

elab "kstep" : tactic => do
  let mvarId ← getMainGoal
  let mvarId ← SymM.run do kstep mvarId
  replaceMainGoal [ mvarId ]

/- Experiments using SymM: 6/N -/

open Lean Meta Sym Sym.DSimp

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
  unless e.isApp && targets.any e.getAppFn'.isConstOf do return .rfl

  let f := e.getAppFn
  let args := e.getAppArgs

  -- In order to unblock reduction, Meta.unfoldDefinition will happily inline
  -- away let-bindings to make e.g. a constructor appear as an argument to a
  -- match recursor. We intervene ahead of time, and hoist the lets that appear in
  -- argument position, which we know for a fact happens quite a bunch in our
  -- semantics. Concretely: `f (let x = ... in arg)` => `let x = ... in f arg`.
  peelArgsLets args 0 #[] #[] fun (peeled : Array Expr) (fvars : Array Expr) => do
    -- Application, *sans* the let-bindings in the arguments.
    let e_rebuilt := mkAppN f peeled
    -- Remember that `Meta.unfoldDefinition` is "smart" and wants to see the whole
    -- application node `f ...` before deciding whether it's worth doing a step of
    -- delta and replacing `f` with its definition.
    if let some e' ← Meta.unfoldDefinition? e_rebuilt true then
      /- let step := (← get).numSteps -/
      /- logInfo m!"deltaBetaOnly {step}: {e_rebuilt}\nunfolds to:{e'}" -/
      let e' ← shareCommon e'
      let e'' ← betaRevS e'.getAppFn e'.getAppRevArgs
      let e'' ← mkLetFVars fvars e''
      -- Here, we want to give other simprocs a chance to run, and reduce e.g.
      -- matches or projectors rather than recursively unfold other occurrences of
      -- e.g. Directives.interp in the continuation. Because we are never at the top-level (due to
      -- the presence of the debug let-gimmick), there is no danger that returning done := true will
      -- stop the traversal.
      /- logInfo m!"deltaBetaOnly {step}: {e}\nunfolds to:{e'}\nreduces to: {e''}" -/
      return .step e'' (done := true)
    else
      /- let f := e.getAppFn -/
      /- logInfo m!"deltaBetaOnly: {f} is expected to reduce but Meta.unfoldDefinition thinks otherwise" -/
      return .rfl

def gimmickId (p: Prop): Prop := p

def gimmick {p: Prop} (h: gimmickId p): p := by
  simp [gimmickId] at h
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
    return .step e' (done := true)
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
    ``Reg64s.get64, ``Reg64s.set64, ``BitVec.drop, ``BitVec.take,
    ``BitVec.extractLsb', ``BitVec.truncate, ``ConstExpr.interp,

    ``Directives.interp, ``Directive.interp, ``Instr.interp, ``Operation.interp,
    ``Operand.interp, ``Effects.All,
    ``ConstExpr.interp, ``RegOrMem.interp, ``Reg.interp, ``MachineData.store,

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

  Grind.setGoals [ { gGoal with mvarId } ]

--------------------------------------------------------------------------------

/- Examples -/

def p5 := parse("start: mov $2, %rax
dec %rax
start2:
dec %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.all true -/

example [layout : Layout] s : Step1 (layout p5) (s, layout.start) (fun s => s.1.regs.rax = 0) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (Step1 _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p5
  dsimp only [Step1,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  sym => 
  kstep
  tactic =>
  /- simp (zeta:=false)(beta:=false)(eta:=false)(iota:=false)(proj:=false)(ground:=true) -/
  simp (zeta:=false)(beta:=false)(eta:=false)(iota:=false)(proj:=false)(ground:=false) only [Nat.shiftRight_zero]
  intros
  simp [gimmickId]

def p6 := parse("push %rax
mov $0, %rax
pop %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.all true -/

example [layout : Layout] s : Step1 (layout p6) (s, layout.start) (fun s' => s'.1.regs.rax = s.regs.rax) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (Step1 _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p6
  dsimp only [Step1,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  sym => 
  kstep
  tactic =>
  /- simp (zeta:=false)(beta:=false)(eta:=false)(iota:=false)(proj:=false)(ground:=true) -/
  simp (zeta:=false)(beta:=false)(eta:=false)(iota:=false)(proj:=false)(ground:=false) only [Nat.shiftRight_zero]
  intros
  simp [gimmickId]

/-   tactic => -/
/-   lift_lets -/
/-   dsimp (zeta:=false)(beta:=true)(eta:=false)(iota:=true)(proj:=true) only [Effects.All] -/

/- def bigp := parseFile("./ecc-secp521r1-modp.S") -/

/- set_option maxRecDepth 4000 -/
/- set_option maxHeartbeats 2000000 -/

/- example [layout : Layout] s : Step1 (layout bigp) (s, layout.start) (fun s => s.1.regs.rax = 0) := by -/
/-   -- Refine the state to make registers apparent -- note that `cases` consumes -/
/-   -- the hypothesis, and substitutes it, so we make a copy of it to have a -/
/-   -- refined state in the hypotheses, not the goal. -/
/-   let ss := s -/
/-   change (Step1 _ (ss, _) _) -/
/-   cases s with | mk regs flags mem => -/
/-   cases regs with | mk rax => -/
/-   -- Rewrite the program to make layout, addresses, etc. apparent -/
/-   delta bigp -/
/-   dsimp only [Step1,Executable.straightline] -/
/-   rw [Executable.directivesFromStart] -/
/-   simp [List.mapIdx,List.mapIdx.go] -/
/-   sym => -/ 
/-   kstep -/
/-   sorry -/
/-   /1- tactic => -1/ -/
/-   /1- lift_lets -1/ -/
/-   /1- revert -1/ -/
/-   /1- sorry -1/ -/

