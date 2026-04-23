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
import Kraken.BetaLetReduce

import Lean

open Kraken.Parser

namespace LiftArgs
open Lean Meta Elab Term

/-- Given a proof of `∀ x₁ ... xₙ, lhs = rhs`, return a proof where as many
    trailing LHS arguments as possible are moved into a `fun ... => ...` on the
    RHS via `funext`. A trailing LHS arg is liftable iff it is a forall-bound
    fvar `f` that doesn't appear elsewhere in the LHS, and no other kept
    forall-binder has a type depending on `f`. If lifting would consume the
    first explicit (default-binder) argument of the LHS — leaving the LHS as
    just `@FuncName` and producing a useless simp lemma — we instead emit a
    warning and fall back to the function's `.eq_unfold` theorem. -/
def liftArgs (proof : Expr) : MetaM Expr := do
  forallTelescope (← inferType proof) fun xs body => do
    let some (_, lhs, rhs) := body.eq?
      | throwError "lift_args%: expected equation, got{indentExpr body}"
    let lhsFn := lhs.getAppFn
    let lhsArgs := lhs.getAppArgs

    -- Index of the first default-binder arg of `lhsFn`.
    let fnType ← inferType lhsFn
    let firstExplicitIdx : Nat ←
      forallBoundedTelescope fnType (some lhsArgs.size) fun fnArgs _ => do
        let lctx ← getLCtx
        for i in [0 : fnArgs.size] do
          let bi := (lctx.find? fnArgs[i]!.fvarId!).map (·.binderInfo) |>.getD .default
          if bi == .default then return i
        return lhsArgs.size

    let mut liftedFvars : Array Expr := #[]
    let mut liftedSet : Std.HashSet FVarId := {}
    let mut hitFirstExplicit := false
    for i in [0 : lhsArgs.size] do
      let argIdx := lhsArgs.size - 1 - i
      let arg := lhsArgs[argIdx]!.consumeMData
      let .fvar fvarId := arg | break
      let some xsIdx := xs.findIdx? (·.fvarId! == fvarId) | break
      if liftedSet.contains fvarId then break
      if lhsFn.containsFVar fvarId then break
      let mut bad := false
      for j in [0 : argIdx] do
        if lhsArgs[j]!.containsFVar fvarId then bad := true; break
      if bad then break
      -- Any kept forall-binder introduced after `f` whose type mentions `f`
      -- would become ill-formed once `f` is lifted.
      for k in [xsIdx + 1 : xs.size] do
        if liftedSet.contains xs[k]!.fvarId! then continue
        if (← inferType xs[k]!).containsFVar fvarId then bad := true; break
      if bad then break
      -- All checks passed; this arg would be lifted. If it's the first
      -- explicit arg of the LHS, lifting would leave no anchor — bail out.
      if argIdx ≤ firstExplicitIdx then
        hitFirstExplicit := true
        break
      liftedFvars := liftedFvars.push arg
      liftedSet := liftedSet.insert fvarId

    if hitFirstExplicit then
      let some fnName := lhsFn.constName?
        | throwError "lift_args%: would lift all explicit args, but LHS head is not a constant"
      let unfoldName := fnName.str "eq_unfold"
      unless (← getEnv).contains unfoldName do
        throwError "lift_args%: would lift all explicit args of `{fnName}`, but `{unfoldName}` does not exist"
      logWarning m!"lift_args% would lift all explicit args of `{fnName}`; using `{unfoldName}` instead"
      return (← mkConstWithFreshMVarLevels unfoldName)

    trace[Meta.debug] "lift_args%: lifted {liftedFvars.size} of {lhsArgs.size} lhs args"
    if liftedFvars.isEmpty then return proof

    let mut p := mkAppN proof xs
    for f in liftedFvars do
      p ← mkAppM ``funext #[← mkLambdaFVars #[f] p]
    let keptXs := xs.filter (fun x => !liftedSet.contains x.fvarId!)
    -- Explicitly cast to a type that preserves the original binder names
    -- (otherwise `funext` introduces fresh `x x_1 ...`).
    let liftedInLhsOrder := liftedFvars.reverse
    let cleanLhs := mkAppN lhsFn (lhsArgs.extract 0 (lhsArgs.size - liftedFvars.size))
    let cleanRhs ← mkLambdaFVars liftedInLhsOrder rhs
    let cleanEq ← mkEq cleanLhs cleanRhs
    let expectedType ← mkForallFVars keptXs cleanEq
    mkExpectedTypeHint (← mkLambdaFVars keptXs p) expectedType

elab "lift_args% " thm:term : term => do
  let proof ← match thm with
    | `($id:ident) | `(@$id:ident) =>
      mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo id)
    | _ => elabTerm thm none
  liftArgs proof

end LiftArgs

def p1 := parse("start: mov $1, %rax")

theorem Executable.directivesFromStart [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) :=
  sorry

def Directives.interp.eq_1' := lift_args% Directives.interp.eq_1
def Directives.interp.eq_2' := lift_args% Directives.interp.eq_2
def Directive.interp.eq_1' := lift_args% Directive.interp.eq_1
def Directive.interp.eq_2' := lift_args% Directive.interp.eq_2
def Operation.interp.eq_1' := lift_args% Operation.interp.eq_1
def Operand.interp.eq_2' := lift_args% Operand.interp.eq_2
def MachineData.set.eq_1' := lift_args% MachineData.set.eq_1
def Reg64s.set.eq_1' := lift_args% Reg64s.set.eq_1
def ConstExpr.interp.eq_2' := lift_args% ConstExpr.interp.eq_2
def ConstExpr.interp.eq_6' := lift_args% ConstExpr.interp.eq_6
def Reg64s.set64.eq_1' := lift_args% Reg64s.set64.eq_1

-- Super-simple example to debug tactics
example [layout : Layout] s : step1 (layout p1) (s, layout.start) (fun s => s.1.regs.rax = 1) := by sym =>

  --dsimp only [p1]
  simp betaLetReduce [p1.eq_unfold]

  --dsimp only [step1,Executable.straightline]
  simp betaLetReduce [step1.eq_unfold,Executable.straightline.eq_unfold]
  /-
⊢ have e :=
  layout.apply
    [Directive.label "start",
      Directive.instr
        { address_size := Width.W64, operation_size := Width.W64,
          operation := Operation.mov ↑(Reg.low Reg64.rax Width.W64) ↑↑1 }];
have s := (s, Layout.start);
Directives.interp (Executable.directivesFromAddress e s.snd) s.fst s.snd fun pc s => (s, pc).fst.regs.rax = 1
  -/

  --rw [Executable.directivesFromStart]
  -- Need to unfold `e` at this point for thm to match
  tactic => intro e; dsimp only [e]; sym =>
  simp betaLetReduce [Executable.directivesFromStart]

  --simp [List.mapIdx,List.mapIdx.go]
  simp betaLetReduce [List.mapIdx_cons, List.mapIdx_nil]

  --dsimp only [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp]
  simp betaLetReduce [Directives.interp.eq_1',Directives.interp.eq_2', Directive.interp.eq_1', Directive.interp.eq_2']
  /-
⊢ have pc := Layout.start;
have ret := fun pc s => s.regs.rax = 1;
have pc := pc + Int64.ofNat (Layout.size 0);
{ address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.mov ↑(Reg.low Reg64.rax Width.W64) ↑↑1 }.interp
  s (pc...pc + Int64.ofNat (Layout.size (0 + 1))) (fun s => ret (pc + Int64.ofNat (Layout.size (0 + 1))) s) ret
  -/
  -- unfold `ret`
  tactic => intros pc ret pc2; subst ret; sym =>
  simp betaLetReduce [Instr.interp.eq_unfold]
  -- unfold `i` and iota reduce
  tactic => intro i; subst i; dsimp only; sym =>
  simp betaLetReduce [Operation.interp.eq_1']  -- makes `p` linear!
  simp betaLetReduce [MachineData.set.eq_1']
  /-
pc : Int64 := Layout.start
pc2 : Int64 := pc + Int64.ofNat (Layout.size 0)
⊢ have p := pc2...pc2 + Int64.ofNat (Layout.size (0 + 1));
(↑↑1).interp s p fun val => (s.setReg (Reg.low Reg64.rax Width.W64) val).regs.rax = 1
  -/
  -- unfold `p`
  tactic => intro p; subst p; sym =>
  simp betaLetReduce [Operand.interp.eq_2']

  --dsimp only [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp]
  simp betaLetReduce [MachineData.setReg.eq_unfold,ConstExpr.interp.eq_2']
  -- iota reduce
  tactic => dsimp -zeta only; sym =>
  -- does not match otherwise?
  tactic => rw [Reg64s.set.eq_1']; sym =>
  simp betaLetReduce [Reg64s.set64.eq_1']

  -- iota reduce + finish
  --simp (ground:=True)
  --simp
  tactic => simp [Width.bits]

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
  dsimp only [step1, Executable.straightline, Directives.interp]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]
  -- TODO It would be nice to progress instruction by instruction instead of all at once, like below.
  dsimp only [Directives.interp, Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp]
  dsimp [MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64]
  intros _af1 _af2 _af3
  apply Eventually.done
  simp (ground:=True)
  dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset]
  dsimp only [BitVec.drop, BitVec.take, Width.bits]
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
  dsimp only [step1,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  dsimp only [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp]
  dsimp only [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp,CondCode.interp,StatusFlags.from_result]
  simp only [Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.truncate_eq_setWidth, BitVec.xor_self, BitVec.zero_eq,
    BEq.rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_zero, BitVec.msb_zero]
  dsimp [undefined,Undefined.undefined]; intros _af
  apply Eventually.done
  simp (ground:=True)

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
