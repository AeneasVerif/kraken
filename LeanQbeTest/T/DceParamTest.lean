module

public import LeanQbe.T.DceParamLemmas
public import LeanQbe.T.OptLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainSplice
public import LeanQbe.T.Examples.LratTrimProg
public import LeanQbe.T.Examples.Kissat.CorePlus
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.LratTrimProg
meta import LeanQbe.T.Examples.Kissat.CorePlus

/-!
# Tests of `LeanQbe.T.DceParam` (`Func.dceP`)

Covers:
1. Dead `.group` join-parameter elimination (`Func.dceP`, `Func.opt`, `Func.earlyOpt`,
   `Func.lateOpt`), verifying signature/operand narrowing, `Wf`, and `Func.spec` refinement.
2. Multi-block asymmetric parameter masks (`multiBlockParamProg`).
3. Dead `let_` cascading into a dead block parameter (`letCascadeParamProg`).
4. Multi-round join-to-join dead-parameter chain (`rounds = 0` vs `rounds = 1`).
5. Preserving used block parameters (`usedParamProg`).
6. Corpus validation on `LratTrim` (`trimProof`) and `Kissat.CorePlus` (`kissat_propagate_lit`),
   confirming dead block-parameter removal and `x64Target` `checkCompile = true`.
7. Single-line `#print axioms` checks (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.DceParamTest

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Examples.LratTrim
open LeanQbe.T.Examples.Kissat.CorePlus

/-! ## 1. Dead join-block parameter elimination (`Func.dceP`, `Func.opt`, `earlyOpt`, `lateOpt`) -/

/-- Diamond join where parameter `dead` is mutated on arms (`x + 1` vs `x + 2`) but unused
in the join body. -/
def deadJoinParamProg : Func [.bool, i64, i64] [i64] := fun _ _ (c, live, dead, ()) =>
  .group (sig := [[i64, i64]])
    (fun _ =>
      .cons (fun (l, _d, ()) =>
        .let_ (op2 (.add i64) (.var l) (.imm 10)) fun (r, ()) =>
        .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var live) (.imm 1)) fun (l1, ()) =>
         .let_ (op2 (.add i64) (.var dead) (.imm 2)) fun (d1, ()) =>
         .jump J (.var l1, .var d1, ()))
        (.jump J (.var live, .var dead, ())))

theorem deadJoinParamProg_dceP_out :
    Func.dceP deadJoinParamProg = fun _ _ (c, live, dead, ()) =>
      .group (sig := [[i64]])
        (fun _ =>
          .cons (fun (l, ()) =>
            .let_ (op2 (.add i64) (.var l) (.imm 10)) fun (r, ()) =>
            .ret (.var r, ())) .nil)
        (fun (J, ()) =>
          .jnz (.var c)
            (.let_ (op2 (.add i64) (.var live) (.imm 1)) fun (l1, ()) =>
             .let_ (op2 (.add i64) (.var dead) (.imm 2)) fun (_d1, ()) =>
             .jump J (.var l1, ()))
            (.jump J (.var live, ()))) := by
  t_kernel_rfl

theorem deadJoinParamProg_r1_out :
    Func.dceP deadJoinParamProg 1 = fun _ _ (c, live, _dead, ()) =>
      .group (sig := [[i64]])
        (fun _ =>
          .cons (fun (l, ()) =>
            .let_ (op2 (.add i64) (.var l) (.imm 10)) fun (r, ()) =>
            .ret (.var r, ())) .nil)
        (fun (J, ()) =>
          .jnz (.var c)
            (.let_ (op2 (.add i64) (.var live) (.imm 1)) fun (l1, ()) =>
             .jump J (.var l1, ()))
            (.jump J (.var live, ()))) := by
  t_kernel_rfl

theorem deadJoinParamProg_opt_out :
    Func.opt deadJoinParamProg = fun _ _ (c, live, dead, ()) =>
      .group (sig := [[i64]])
        (fun _ =>
          .cons (fun (l, ()) =>
            .let_ (op2 (.add i64) (.var l) (.imm 10)) fun (r, ()) =>
            .ret (.var r, ())) .nil)
        (fun (J, ()) =>
          .jnz (.var c)
            (.let_ (op2 (.add i64) (.var live) (.imm 1)) fun (l1, ()) =>
             .let_ (op2 (.add i64) (.var dead) (.imm 2)) fun (_d1, ()) =>
             .jump J (.var l1, ()))
            (.jump J (.var live, ()))) := by
  t_kernel_rfl

theorem deadJoinParamProg_wf : deadJoinParamProg.Wf := by t_wf_reify

theorem deadJoinParamProg_dceP_wf : (Func.dceP deadJoinParamProg).Wf :=
  Func.dceP_wf deadJoinParamProg_wf

theorem deadJoinParamProg_dceP_spec (Γ : Env) (c : Bool) (live dead : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.dceP deadJoinParamProg) (c, live, dead, ()) m
      (fun (r, ()) m' => r = (if c then live + 11#64 else live + 10#64) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.dceP_spec deadJoinParamProg_wf
  dsimp only [Func.spec, Func.wp, deadJoinParamProg]
  simp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, i64, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, Closed]
  intro ⟨J, ⟨⟩⟩ hJ
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · exact hJ.1 (live + 1#64, dead + 2#64, ()) m ⟨by simp [hc]; bv_omega, rfl⟩
  · exact hJ.1 (live, dead, ()) m ⟨by simp [hc], rfl⟩

theorem deadJoinParamProg_earlyOpt_wf : (Func.earlyOpt deadJoinParamProg).Wf :=
  Func.earlyOpt_wf deadJoinParamProg_wf

theorem deadJoinParamProg_lateOpt_wf : (Func.lateOpt deadJoinParamProg).Wf :=
  Func.lateOpt_wf deadJoinParamProg_wf

/-! ## 2. Multi-block asymmetric parameter elimination -/

/-- Two-block `.group` where block 0 uses only param 0 and block 1 uses only param 1. -/
def multiBlockParamProg : Func [.bool, i64, i64] [i64] := fun _ _ (c, a, b, ()) =>
  .group (sig := [[i64, i64], [i64, i64]])
    (fun _ =>
      .cons (fun (x, _y, ()) => .ret (.var x, ()))
        (.cons (fun (_x, y, ()) => .ret (.var y, ())) .nil))
    (fun (J0, J1, ()) =>
      .jnz (.var c)
        (.jump J0 (.var a, .var b, ()))
        (.jump J1 (.var a, .var b, ())))

theorem multiBlockParamProg_dceP_out :
    Func.dceP multiBlockParamProg = fun _ _ (c, a, b, ()) =>
      .group (sig := [[i64], [i64]])
        (fun _ =>
          .cons (fun (x, ()) => .ret (.var x, ()))
            (.cons (fun (y, ()) => .ret (.var y, ())) .nil))
        (fun (J0, J1, ()) =>
          .jnz (.var c)
            (.jump J0 (.var a, ()))
            (.jump J1 (.var b, ()))) := by
  t_kernel_rfl

theorem multiBlockParamProg_wf : multiBlockParamProg.Wf := by t_wf_reify

theorem multiBlockParamProg_dceP_wf : (Func.dceP multiBlockParamProg).Wf :=
  Func.dceP_wf multiBlockParamProg_wf

/-! ## 3. Dead `let_` cascading into dead block parameter -/

/-- Unused `let_` inside block uses `d`, so dropping the dead `let_` makes `d` dead too. -/
def letCascadeParamProg : Func [.bool, i64, i64] [i64] := fun _ _ (c, a, b, ()) =>
  .group (sig := [[i64, i64]])
    (fun _ =>
      .cons (fun (x, d, ()) =>
        .let_ (op2 (.mul i64) (.var d) (.imm 7)) fun _unused =>
        .ret (.var x, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c) (.jump J (.var a, .var b, ())) (.jump J (.var b, .var a, ())))

theorem letCascadeParamProg_dceP_out :
    Func.dceP letCascadeParamProg = fun _ _ (c, a, b, ()) =>
      .group (sig := [[i64]])
        (fun _ => .cons (fun (x, ()) => .ret (.var x, ())) .nil)
        (fun (J, ()) => .jnz (.var c) (.jump J (.var a, ())) (.jump J (.var b, ()))) := by
  t_kernel_rfl

/-! ## 4. Multi-round join-to-join dead-parameter chain (`rounds = 0` vs `rounds = 1`) -/

/-- `J1` forwards its second parameter `d` to `J2`, where `d` is unused:
`rounds = 0` eliminates `J2`'s dead param, while `rounds = 1` eliminates both `J1` and `J2`. -/
def chainParamProg : Func [.bool, i64, i64] [i64] := fun _ _ (c, a, b, ()) =>
  .group (sig := [[i64, i64]])
    (fun _ => .cons (fun (x, _d, ()) => .ret (.var x, ())) .nil)
    (fun (J2, ()) =>
      .group (sig := [[i64, i64]])
        (fun _ => .cons (fun (x, d, ()) => .jump J2 (.var x, .var d, ())) .nil)
        (fun (J1, ()) =>
          .jnz (.var c) (.jump J1 (.var a, .var b, ())) (.jump J1 (.var b, .var a, ()))))

theorem chainParamProg_r0_out :
    Func.dceP chainParamProg 0 = fun _ _ (c, a, b, ()) =>
      .group (sig := [[i64]])
        (fun _ => .cons (fun (x, ()) => .ret (.var x, ())) .nil)
        (fun (J2, ()) =>
          .group (sig := [[i64, i64]])
            (fun _ => .cons (fun (x, _d, ()) => .jump J2 (.var x, ())) .nil)
            (fun (J1, ()) =>
              .jnz (.var c) (.jump J1 (.var a, .var b, ())) (.jump J1 (.var b, .var a, ())))) := by
  t_kernel_rfl

theorem chainParamProg_r1_out :
    Func.dceP chainParamProg 1 = fun _ _ (c, a, b, ()) =>
      .group (sig := [[i64]])
        (fun _ => .cons (fun (x, ()) => .ret (.var x, ())) .nil)
        (fun (J2, ()) =>
          .group (sig := [[i64]])
            (fun _ => .cons (fun (x, ()) => .jump J2 (.var x, ())) .nil)
            (fun (J1, ()) =>
              .jnz (.var c) (.jump J1 (.var a, ())) (.jump J1 (.var b, ())))) := by
  t_kernel_rfl

theorem chainParamProg_wf : chainParamProg.Wf := by t_wf_reify

theorem chainParamProg_r1_wf : (Func.dceP chainParamProg 1).Wf :=
  Func.dceP_wf chainParamProg_wf 1

theorem chainParamProg_r1_spec (Γ : Env) (c : Bool) (a b : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.dceP chainParamProg 1) (c, a, b, ()) m
      (fun (r, ()) m' => r = (if c then a else b) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.dceP_spec chainParamProg_wf _ 1
  dsimp only [Func.spec, Func.wp, chainParamProg]
  simp only [wp, Closed, Arg.val, vals]
  intro ⟨J2, ⟨⟩⟩ hJ2
  intro ⟨J1, ⟨⟩⟩ hJ1
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · exact hJ1.1 (a, b, ()) m (hJ2.1 (a, b, ()) m ⟨by simp [hc], rfl⟩)
  · exact hJ1.1 (b, a, ()) m (hJ2.1 (b, a, ()) m ⟨by simp [hc], rfl⟩)

/-! ## 5. Preserving used parameters & `checkTFlat` -/

/-- When every block parameter is live, `Func.dceP` preserves the function unchanged. -/
def usedParamProg : Func [.bool, i64, i64] [i64] := fun _ _ (c, a, b, ()) =>
  .group (sig := [[i64, i64]])
    (fun _ =>
      .cons (fun (x, y, ()) =>
        .let_ (op2 (.add i64) (.var x) (.var y)) fun (s, ()) =>
        .ret (.var s, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c) (.jump J (.var a, .var b, ())) (.jump J (.var b, .var a, ())))

theorem usedParamProg_dceP_out : Func.dceP usedParamProg = usedParamProg := by t_kernel_rfl

theorem deadJoinParamProg_checkTFlat :
    (Func.lateOpt (Func.legal LegalTarget.x64 (Func.earlyOpt deadJoinParamProg))).checkTFlat =
      true := by
  t_kernel_rfl

/-! ## 6. Kissat & LRAT corpus checks and x64 `checkCompile = true` -/

mutual
/-- Total number of `.group` block parameter slots across a `TFlat` AST. -/
def countGroupParams {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => countGroupParams k
  | .jnz _ t e => countGroupParams t + countGroupParams e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group (sig := sig) bodies k =>
    sig.foldl (fun acc ts => acc + ts.length) 0 +
      countGroupParamsB bodies + countGroupParams k

/-- Block-list companion of `countGroupParams`. -/
def countGroupParamsB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => countGroupParams b + countGroupParamsB bs
end

/-- `LratTrim.trimProof`: `Func.dceP` drops dead join parameters on `earlyOpt` IR (`22 → 20`). -/
theorem lratTrim_trimProof_param_count_dce :
    countGroupParams (reifyFunc (Func.dce
      (Func.peelFast (Func.simplifyGroupFast (Func.earlyCore trimProof)) 24))) = 22 := by
  t_kernel_rfl

theorem lratTrim_trimProof_param_count_dceP :
    countGroupParams (reifyFunc (Func.dceP
      (Func.peelFast (Func.simplifyGroupFast (Func.earlyCore trimProof)) 24))) = 20 := by
  t_kernel_rfl

/-- `Kissat.CorePlus.kissat_propagate_lit`: `Func.dceP` drops dead join parameters on `earlyOpt`
IR (`8 → 5` in round 0). -/
theorem kissat_propagate_lit_param_count_dce :
    countGroupParams (reifyFunc (Func.dce
      (Func.peelFast (Func.simplifyGroupFast (Func.earlyCore kissat_propagate_lit_body)) 24))) =
      8 := by
  t_kernel_rfl

theorem kissat_propagate_lit_param_count_dceP :
    countGroupParams (reifyFunc (Func.dceP
      (Func.peelFast (Func.simplifyGroupFast (Func.earlyCore kissat_propagate_lit_body)) 24))) =
      5 := by
  t_kernel_rfl

-- `LratTrim` callee-first module (`5` functions) compiles cleanly on x64 after `Func.dceP`
-- wiring (`checkCompile = true`).
splice_module_hints lratTrimHints (x64Target.toIsa) x64LegalTarget lratTrimFns

theorem lratTrim_x64_checkCompile :
    checkCompile x64Target x64Layout x64LegalTarget [] ["lrat_fail"] 0
      lratTrimFns lratTrimHints 2048 = true := by
  t_kernel_rfl

/-- `Kissat.CorePlus` propagation slice (`kissat_assign`, `kissat_find_repl`,
`kissat_propagate_lit`) in callee-first order. -/
def kissatPropSlice : List Fn :=
  coreplus_fns.filter fun f =>
    f.name == "kissat_assign" || f.name == "kissat_find_repl" || f.name == "kissat_propagate_lit"

-- Compile the Kissat propagation slice on x64 (`checkCompile = true`).
splice_module_hints kissatPropHints (x64Target.toIsa) x64LegalTarget kissatPropSlice

theorem kissatPropSlice_x64_checkCompile :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      kissatPropSlice kissatPropHints 2048 = true := by
  t_kernel_rfl

/-! ## 7. Axiom audits -/

#print axioms LeanQbe.T.Func.dcePWith_wf
#print axioms LeanQbe.T.Func.dcePWith_spec
#print axioms LeanQbe.T.Func.dceP_wf
#print axioms LeanQbe.T.Func.dceP_spec
#print axioms LeanQbe.T.Func.opt_wf
#print axioms LeanQbe.T.Func.opt_spec
#print axioms LeanQbe.T.Func.earlyOpt_wf
#print axioms LeanQbe.T.Func.earlyOpt_spec
#print axioms LeanQbe.T.Func.lateOpt_wf
#print axioms LeanQbe.T.Func.lateOpt_spec

end LeanQbeTest.T.DceParamTest
