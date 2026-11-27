module

public import LeanQbe.T.IfOptLemmas
public import LeanQbe.T.SimplifyGroupPlanLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas

/-!
# Tests of `LeanQbe.T.IfOpt` and `LeanQbe.T.SimplifyGroupPlan`

Covers:
1. `IfOpt` (diamond `jnz` → `select`) + `SimplifyGroupPlan` straight-line collapse:
   - Scalar arithmetic branch diamond,
   - Multi-arg (`≤ 4` safe ops + identical-operand passthrough),
   - Entry `.load`/`.let_` prefix + `.pair` component-wise `.select`,
   - Negative safety checks: partial op (`udiv`) NOT hoisted, `> 4` pure ops NOT hoisted,
     float signature/op NOT hoisted, existing `.select` NOT turned into `.jnz`.
2. `SimplifyGroupPlan` PHOAS join-group elimination:
   - Single-block tail join (`k = .jump J args`) spliced even over size 16,
   - Small single-use block (`size ≤ 16 && jumps == 1`) spliced,
   - Multi-use (`jumps == 2`) and self-loop (`selfRec == true`) preserved,
   - Dead single-block `.group` (`jumps == 0`) unwrapped,
   - Multi-block `.group` dead-block filtering & zero-jump unwrap,
   - Bottom-up nested `.group` elimination.
3. Relational `Wf` (`Func.ifOpt_wf`, `Func.simplifyGroupPlan_wf`), `Func.checkTFlat`,
   `wp`/`Func.spec` refinement (`Func.ifOpt_spec`, `Func.simplifyGroupPlan_spec`), and clean
   `#print axioms`.
-/

set_option autoImplicit false


namespace LeanQbeTest.T.CfgOptTest

open LeanQbe.T

/-- Combined `CfgOpt` pipeline: `IfOpt` followed by `SimplifyGroupPlan`. -/
def ifSimp {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.simplifyGroupPlan (Func.ifOpt f)

theorem ifSimp_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (ifSimp f).Wf :=
  Func.simplifyGroupPlan_wf (Func.ifOpt_wf hf)

theorem ifSimp_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (ifSimp f) xs m Q X :=
  Func.simplifyGroupPlan_spec (Func.ifOpt_wf hf) (Func.ifOpt_spec hf h)

/-! ## 1. Branch diamond `jnz` → `select` and `SimplifyGroupPlan` collapse -/

/-- Branch diamond: `if (x <s y) { a + 10 } else { a - 10 }` joining on `[i64]`. -/
def mb3Diamond : Func [i64, i64, i64] [i64] := fun _ _ (x, y, a, ()) =>
  .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
  .group (sig := [[i64]])
    (fun _ =>
      .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var a) (.imm 10)) fun (t, ()) => .jump J (.var t, ()))
        (.let_ (op2 (.sub i64) (.var a) (.imm 10)) fun (e, ()) => .jump J (.var e, ())))

theorem mb3Diamond_ifOpt_out : Func.ifOpt mb3Diamond = fun _ _ (x, y, a, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
    .group (sig := [[i64]])
      (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
      (fun (J, ()) =>
        .let_ (op2 (.add i64) (.var a) (.imm 10)) fun (t, ()) =>
        .let_ (op2 (.sub i64) (.var a) (.imm 10)) fun (e, ()) =>
        .let_ (op3 (.select i64) (.var c) (.var t) (.var e)) fun (s, ()) =>
        .jump J (.var s, ())) := by
  t_kernel_rfl

theorem mb3Diamond_ifSimp_out : ifSimp mb3Diamond = fun _ _ (x, y, a, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 10)) fun (t, ()) =>
    .let_ (op2 (.sub i64) (.var a) (.imm 10)) fun (e, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var t) (.var e)) fun (s, ()) =>
    .ret (.var s, ()) := by
  t_kernel_rfl

theorem mb3Diamond_wf : mb3Diamond.Wf := by t_wf_reify

theorem mb3Diamond_ifOpt_wf : (Func.ifOpt mb3Diamond).Wf := Func.ifOpt_wf mb3Diamond_wf

theorem mb3Diamond_ifSimp_wf : (ifSimp mb3Diamond).Wf := ifSimp_wf mb3Diamond_wf

theorem mb3Diamond_ifSimp_checkTFlat : (ifSimp mb3Diamond).checkTFlat = true := by t_kernel_rfl

theorem mb3Diamond_ifSimp_spec (Γ : Env) (x y a : BitVec 64) (m : Mem 64) :
    Func.spec Γ (ifSimp mb3Diamond) (x, y, a, ()) m
      (fun (r, ()) m' =>
        r = (if BitVec.slt x y then a + 10#64 else a - 10#64) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply ifSimp_spec mb3Diamond_wf
  dsimp only [Func.spec, Func.wp, mb3Diamond]
  simp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, liftCmp, CmpOp.evalBits, i64, Closed]
  intro ⟨J, ⟨⟩⟩ hJ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hJ.1 (a + 10#64, ()) m ⟨by simp [h], rfl⟩
  · exact hJ.1 (a - 10#64, ()) m ⟨by simp [h], rfl⟩

/-- 4-op safe arm (`add`, `xor`, `rotl`, `zext`), multi-arg `[i64, .bool]`, identical `.bool`
operand kept un-selected. -/
def diamondMax4AndId : Func [i32, i64, .bool] [i64, .bool] := fun _ _ (w, a, flag, ()) =>
  .group (sig := [[i64, .bool]])
    (fun _ => .cons (fun (r, b, ()) => .ret (.var r, .var b, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var flag)
        (.let_ (op2 (.add i32) (.var w) (.imm 1)) fun (w1, ()) =>
         .let_ (op2 (.xor i32) (.var w1) (.imm 3)) fun (w2, ()) =>
         .let_ (op2 (.rotl i32) (.var w2) (.imm 5)) fun (w3, ()) =>
         .let_ (op1 (.zext 32 64) (.var w3)) fun (x4, ()) =>
         .jump J (.var x4, .var flag, ()))
        (.let_ (op2 (.mul i64) (.var a) (.imm 3)) fun (y1, ()) =>
         .let_ (op2 (.shl i64) (.var y1) (.imm 1)) fun (y2, ()) =>
         .jump J (.var y2, .var flag, ())))

theorem diamondMax4AndId_ifSimp_out : ifSimp diamondMax4AndId = fun _ _ (w, a, flag, ()) =>
    .let_ (op2 (.add i32) (.var w) (.imm 1)) fun (w1, ()) =>
    .let_ (op2 (.xor i32) (.var w1) (.imm 3)) fun (w2, ()) =>
    .let_ (op2 (.rotl i32) (.var w2) (.imm 5)) fun (w3, ()) =>
    .let_ (op1 (.zext 32 64) (.var w3)) fun (x4, ()) =>
    .let_ (op2 (.mul i64) (.var a) (.imm 3)) fun (y1, ()) =>
    .let_ (op2 (.shl i64) (.var y1) (.imm 1)) fun (y2, ()) =>
    .let_ (op3 (.select i64) (.var flag) (.var x4) (.var y2)) fun (s, ()) =>
    .ret (.var s, .var flag, ()) := by
  t_kernel_rfl

theorem diamondMax4AndId_wf : diamondMax4AndId.Wf := by t_wf_reify

theorem diamondMax4AndId_ifSimp_checkTFlat : (ifSimp diamondMax4AndId).checkTFlat = true := by
  t_kernel_rfl

/-- Diamond with `.load` prefix inside entry and `.pair i64 .bool` join signature (converted to
leaf-wise `.select`s + `mkpair`, then collapsed out of `.group`). -/
def diamondPrefixPair : Func [.bool, i64, i64.pair .bool] [i64.pair .bool] :=
  fun _ _ (c, ptr, p, ()) =>
  .group (sig := [[i64.pair .bool]])
    (fun _ => .cons (fun (q, ()) => .ret (.var q, ())) .nil)
    (fun (J, ()) =>
      .load i64 (.var ptr) fun mv =>
      .jnz (.var c)
        (.let_ (op2 (.mkpair i64 .bool) (.var mv) (.imm true)) fun (pt, ()) =>
         .jump J (.var pt, ()))
        (.jump J (.var p, ())))

theorem diamondPrefixPair_ifSimp_out : ifSimp diamondPrefixPair = fun _ _ (c, ptr, p, ()) =>
    .load i64 (.var ptr) fun mv =>
    .let_ (op2 (.mkpair i64 .bool) (.var mv) (.imm true)) fun (pt, ()) =>
    .let_ (op1 (.unpair i64 .bool) (.var pt)) fun ut =>
    .let_ (op1 (.unpair i64 .bool) (.var p)) fun ue =>
    .let_ (op3 (.select i64) (.var c) (.var ut.1) (.var ue.1)) fun (s0, ()) =>
    .let_ (op3 (.select .bool) (.var c) (.var ut.2.1) (.var ue.2.1)) fun (s1, ()) =>
    .let_ (op2 (.mkpair i64 .bool) (.var s0) (.var s1)) fun (sp, ()) =>
    .ret (.var sp, ()) := by
  t_kernel_rfl

theorem diamondPrefixPair_wf : diamondPrefixPair.Wf := by t_wf_reify

theorem diamondPrefixPair_ifSimp_checkTFlat : (ifSimp diamondPrefixPair).checkTFlat = true := by
  t_kernel_rfl

/-! ## 2. Negative `IfOpt` guards (`udiv`, `> 4` ops, floats, `.select` preservation) -/

/-- Partial op (`udiv 64`) in an arm must not be speculatively hoisted. -/
def udivDiamond : Func [.bool, i64, i64] [i64] := fun _ _ (c, x, d, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.udiv 64) (.var x) (.var d)) fun (q, ()) => .jump J (.var q, ()))
        (.jump J (.imm 0, ())))

theorem udivDiamond_ifOpt_unchanged : Func.ifOpt udivDiamond = udivDiamond := by t_kernel_rfl

theorem udivDiamond_ifSimp_unchanged : ifSimp udivDiamond = udivDiamond := by t_kernel_rfl

theorem udivDiamond_wf : udivDiamond.Wf := by t_wf_reify

/-- More than 4 pure ops in one arm (`5` `.let_`s) must not be hoisted. -/
def over4Diamond : Func [.bool, i64] [i64] := fun _ _ (c, x, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (x1, ()) =>
         .let_ (op2 (.add i64) (.var x1) (.imm 2)) fun (x2, ()) =>
         .let_ (op2 (.add i64) (.var x2) (.imm 3)) fun (x3, ()) =>
         .let_ (op2 (.add i64) (.var x3) (.imm 4)) fun (x4, ()) =>
         .let_ (op2 (.add i64) (.var x4) (.imm 5)) fun (x5, ()) =>
         .jump J (.var x5, ()))
        (.jump J (.var x, ())))

theorem over4Diamond_ifOpt_unchanged : Func.ifOpt over4Diamond = over4Diamond := by t_kernel_rfl

/-- Float join signature / float arithmetic must not be hoisted to `.select`. -/
def floatDiamond : Func [.bool, f64] [f64] := fun _ _ (c, x, ()) =>
  .group (sig := [[f64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.fadd f64) (.var x) (.imm default)) fun (y, ()) => .jump J (.var y, ()))
        (.jump J (.var x, ())))

theorem floatDiamond_ifOpt_unchanged : Func.ifOpt floatDiamond = floatDiamond := by t_kernel_rfl

/-- Existing `.select` is never turned back into `.jnz`. -/
def selectStayProg : Func [.bool, i64, i64] [i64] := fun _ _ (c, a, b, ()) =>
  .let_ (op3 (.select i64) (.var c) (.var a) (.var b)) fun (s, ()) =>
  .ret (.var s, ())

theorem selectStay_unchanged : ifSimp selectStayProg = selectStayProg := by t_kernel_rfl

/-! ## 3. `SimplifyGroupPlan` join elimination, dead unwrapping, loops, and nested groups -/

/-- Large non-recursive join block (`> 16` nodes) is still spliced when entry is `.jump J args`. -/
def tailJoinLargeProg : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64]])
    (fun _ =>
      .cons (fun (a, ()) =>
        .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (a1, ()) =>
        .let_ (op2 (.add i64) (.var a1) (.imm 2)) fun (a2, ()) =>
        .let_ (op2 (.add i64) (.var a2) (.imm 3)) fun (a3, ()) =>
        .let_ (op2 (.add i64) (.var a3) (.imm 4)) fun (a4, ()) =>
        .let_ (op2 (.add i64) (.var a4) (.imm 5)) fun (a5, ()) =>
        .let_ (op2 (.add i64) (.var a5) (.imm 6)) fun (a6, ()) =>
        .let_ (op2 (.add i64) (.var a6) (.imm 7)) fun (a7, ()) =>
        .let_ (op2 (.add i64) (.var a7) (.imm 8)) fun (a8, ()) =>
        .let_ (op2 (.add i64) (.var a8) (.imm 9)) fun (a9, ()) =>
        .let_ (op2 (.add i64) (.var a9) (.imm 10)) fun (a10, ()) =>
        .let_ (op2 (.add i64) (.var a10) (.imm 11)) fun (a11, ()) =>
        .let_ (op2 (.add i64) (.var a11) (.imm 12)) fun (a12, ()) =>
        .let_ (op2 (.add i64) (.var a12) (.imm 13)) fun (a13, ()) =>
        .let_ (op2 (.add i64) (.var a13) (.imm 14)) fun (a14, ()) =>
        .let_ (op2 (.add i64) (.var a14) (.imm 15)) fun (a15, ()) =>
        .let_ (op2 (.add i64) (.var a15) (.imm 16)) fun (a16, ()) =>
        .ret (.var a16, ())) .nil)
    (fun (J, ()) => .jump J (.var x, ()))

theorem tailJoinLargeProg_simp_out : Func.simplifyGroupPlan tailJoinLargeProg = fun _ _ (a, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (a1, ()) =>
    .let_ (op2 (.add i64) (.var a1) (.imm 2)) fun (a2, ()) =>
    .let_ (op2 (.add i64) (.var a2) (.imm 3)) fun (a3, ()) =>
    .let_ (op2 (.add i64) (.var a3) (.imm 4)) fun (a4, ()) =>
    .let_ (op2 (.add i64) (.var a4) (.imm 5)) fun (a5, ()) =>
    .let_ (op2 (.add i64) (.var a5) (.imm 6)) fun (a6, ()) =>
    .let_ (op2 (.add i64) (.var a6) (.imm 7)) fun (a7, ()) =>
    .let_ (op2 (.add i64) (.var a7) (.imm 8)) fun (a8, ()) =>
    .let_ (op2 (.add i64) (.var a8) (.imm 9)) fun (a9, ()) =>
    .let_ (op2 (.add i64) (.var a9) (.imm 10)) fun (a10, ()) =>
    .let_ (op2 (.add i64) (.var a10) (.imm 11)) fun (a11, ()) =>
    .let_ (op2 (.add i64) (.var a11) (.imm 12)) fun (a12, ()) =>
    .let_ (op2 (.add i64) (.var a12) (.imm 13)) fun (a13, ()) =>
    .let_ (op2 (.add i64) (.var a13) (.imm 14)) fun (a14, ()) =>
    .let_ (op2 (.add i64) (.var a14) (.imm 15)) fun (a15, ()) =>
    .let_ (op2 (.add i64) (.var a15) (.imm 16)) fun (a16, ()) =>
    .ret (.var a16, ()) := by
  t_kernel_rfl

theorem tailJoinLargeProg_wf : tailJoinLargeProg.Wf := by t_wf_reify

theorem tailJoinLargeProg_checkTFlat :
    (Func.simplifyGroupPlan tailJoinLargeProg).checkTFlat = true := by
  t_kernel_rfl

/-- Dead single-block `.group` (`jumps == 0`) is unwrapped completely. -/
def deadGroupProg : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (a, ()) => .ret (.var a, ())) .nil)
    (fun _ => .let_ (op2 (.add i64) (.var x) (.imm 7)) fun (y, ()) => .ret (.var y, ()))

theorem deadGroupProg_simp_out : Func.simplifyGroupPlan deadGroupProg = fun _ _ (x, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 7)) fun (y, ()) => .ret (.var y, ()) := by
  t_kernel_rfl

theorem deadGroupProg_wf : deadGroupProg.Wf := by t_wf_reify

theorem deadGroupProg_spec (Γ : Env) (x : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.simplifyGroupPlan deadGroupProg) (x, ()) m
      (fun (r, ()) m' => r = x + 7#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.simplifyGroupPlan_spec deadGroupProg_wf
  dsimp only [Func.spec, Func.wp, deadGroupProg]
  simp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, i64]
  intro _ _; simp

/-- Small single-use join block (`size ≤ 16 && jumps == 1`) with non-jump prefix in
`k` is spliced by `SimplifyGroupPlan`, whereas two jump sites (`jumps == 2`) keep `.group`. -/
def smallSingleUseProg : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64]])
    (fun _ =>
      .cons (fun (a, ()) =>
        .let_ (op2 (.mul i64) (.var a) (.imm 5)) fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 2)) fun (y, ()) => .jump J (.var y, ()))

theorem smallSingleUseProg_simp_out : Func.simplifyGroupPlan smallSingleUseProg = fun _ _ (x, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 2)) fun (y, ()) =>
    .let_ (op2 (.mul i64) (.var y) (.imm 5)) fun (r, ()) =>
    .ret (.var r, ()) := by
  t_kernel_rfl

def twoUseNotSplicedProg : Func [.bool, i64] [i64] := fun _ _ (c, x, ()) =>
  .group (sig := [[i64]])
    (fun _ =>
      .cons (fun (a, ()) =>
        .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c) (.jump J (.var x, ())) (.jump J (.imm 42, ())))

theorem twoUseNotSpliced_simp_unchanged :
    Func.simplifyGroupPlan twoUseNotSplicedProg = twoUseNotSplicedProg := by
  t_kernel_rfl

/-- Zero local jumps in a multi-block `.group` unwraps the group completely to `k'`. -/
def multiBlockZeroJumpProg : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64], [i64]])
    (fun _ =>
      .cons (fun (a, ()) => .ret (.var a, ()))
      (.cons (fun (b, ()) => .ret (.var b, ())) .nil))
    (fun _ => .let_ (op2 (.sub i64) (.var x) (.imm 1)) fun (r, ()) => .ret (.var r, ()))

theorem multiBlockZeroJump_simp_out :
    Func.simplifyGroupPlan multiBlockZeroJumpProg = fun _ _ (x, ()) =>
    .let_ (op2 (.sub i64) (.var x) (.imm 1)) fun (r, ()) => .ret (.var r, ()) := by
  t_kernel_rfl

/-- Self-recursive single-block loop must not be spliced (`selfRec == true`), even when entry
is `.jump J args`. -/
def selfLoopProg : Func [i64] [i64] := fun _ _ (n, ()) =>
  .group (sig := [[i64]])
    (fun (loop, ()) =>
      .cons (fun (i, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var i) (.imm 0)) fun (done, ()) =>
        .jnz (.var done) (.ret (.var i, ()))
          (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) => .jump loop (.var i', ())))
        .nil)
    (fun (loop, ()) => .jump loop (.var n, ()))

theorem selfLoopProg_simp_unchanged : Func.simplifyGroupPlan selfLoopProg = selfLoopProg := by
  t_kernel_rfl

theorem selfLoopProg_wf : selfLoopProg.Wf := by t_wf_reify

theorem selfLoopProg_simp_checkTFlat :
    (Func.simplifyGroupPlan selfLoopProg).checkTFlat = true := by
  t_kernel_rfl

/-- Multi-block `.group` dead-block elimination (`sig = [i64, i64, i64]` where middle block `B1`
is unreachable from entry + `B0` + `B2`) + outer `Wf`/`spec`/`checkTFlat`. -/
def multiBlockDeadProg : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64], [i64], [i64]])
    (fun (b0, b1, b2, ()) =>
      .cons (fun (a, ()) => .jump b2 (.var a, ()))
      (.cons (fun (deadArg, ()) => .jump b1 (.var deadArg, ()))
      (.cons (fun (c, ()) => .let_ (op2 (.add i64) (.var c) (.imm 5)) fun (r, ()) =>
        .ret (.var r, ()))
      .nil)))
    (fun (b0, _, _, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0)) fun (zc, ()) =>
      .jnz (.var zc) (.jump b0 (.var x, ())) (.jump b0 (.imm 9, ())))

theorem multiBlockDeadProg_simp_out : Func.simplifyGroupPlan multiBlockDeadProg = fun _ _ (x, ()) =>
    .group (sig := [[i64], [i64]])
      (fun (_, b2, ()) =>
        .cons (fun (a, ()) => .jump b2 (.var a, ()))
        (.cons (fun (c, ()) => .let_ (op2 (.add i64) (.var c) (.imm 5)) fun (r, ()) =>
          .ret (.var r, ()))
        .nil))
      (fun (b0, _, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0)) fun (zc, ()) =>
        .jnz (.var zc) (.jump b0 (.var x, ())) (.jump b0 (.imm 9, ()))) := by
  t_kernel_rfl

theorem multiBlockDeadProg_wf : multiBlockDeadProg.Wf := by t_wf_reify

theorem multiBlockDeadProg_simp_wf : (Func.simplifyGroupPlan multiBlockDeadProg).Wf :=
  Func.simplifyGroupPlan_wf multiBlockDeadProg_wf

theorem multiBlockDeadProg_checkTFlat :
    (Func.simplifyGroupPlan multiBlockDeadProg).checkTFlat = true := by
  t_kernel_rfl

/-- Nested `.group` cleanup: dead multi-block inner group inside a small single-use outer join
group collapses completely bottom-up to straight-line code. -/
def nestedGroupProg : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64]])
    (fun _ =>
      .cons (fun (a, ()) =>
        .group (sig := [[i64], [i64]])
          (fun _ =>
            .cons (fun (u, ()) => .ret (.var u, ()))
            (.cons (fun (v, ()) => .ret (.var v, ())) .nil))
          (fun _ => .let_ (op2 (.mul i64) (.var a) (.imm 3)) fun (r, ()) => .ret (.var r, ())))
        .nil)
    (fun (J, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) =>
      .jump J (.var y, ()))

theorem nestedGroupProg_simp_out : Func.simplifyGroupPlan nestedGroupProg = fun _ _ (x, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) =>
    .let_ (op2 (.mul i64) (.var y) (.imm 3)) fun (r, ()) =>
    .ret (.var r, ()) := by
  t_kernel_rfl

theorem nestedGroupProg_wf : nestedGroupProg.Wf := by t_wf_reify

theorem nestedGroupProg_simp_spec (Γ : Env) (x : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.simplifyGroupPlan nestedGroupProg) (x, ()) m
      (fun (r, ()) m' => r = (x + 1#64) * 3#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.simplifyGroupPlan_spec nestedGroupProg_wf
  dsimp only [Func.spec, Func.wp, nestedGroupProg]
  simp only [wp, Op.wp, OpCode.wp, op2, Closed]
  intro ⟨J, ⟨⟩⟩ hJ
  exact hJ.1 (x + 1#64, ()) m (fun _ _ => ⟨rfl, rfl⟩)

/-! ## 4. Axiom audits -/

#print axioms LeanQbe.T.ifOpt_wf
#print axioms LeanQbe.T.Func.ifOpt_wf
#print axioms LeanQbe.T.ifOpt_wp
#print axioms LeanQbe.T.Func.ifOpt_spec
#print axioms LeanQbe.T.Func.simplifyGroupPlan_wf
#print axioms LeanQbe.T.Func.simplifyGroupPlan_spec
#print axioms mb3Diamond_ifSimp_spec
#print axioms deadGroupProg_spec
#print axioms nestedGroupProg_simp_spec

end LeanQbeTest.T.CfgOptTest
