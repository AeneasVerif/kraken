/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Wp0
public import LeanQbe.T.Examples.Kissat.Proof.Factor.WpFilter0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Filter-Row Cleanup Loop & Main WP (`Proof.Factor.WpFilter1`)

Zero-legacy (`0` `Full*` imports, `0` placeholders, `XPost`-polymorphic) cleanup loop and outer
loop WP proof `full_bva_filter_row_wp` establishing `fidBvaFilterRowSpec` (`12/15`).
-/

set_option autoImplicit false

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

public section

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

@[local bv_c0] private theorem flt1_bv64_one : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem flt1_bv32_one : (1 : BitVec 32).toNat = 1 := rfl

private theorem flt1_and2_of_andFE {x : BitVec 8} (h : (x &&& 0xFE#8) = 0#8) :
    (x &&& 2#8) = 0#8 := by
  have h0 : (x &&& 0xFE#8) &&& 2#8 = 0#8 &&& 2#8 := congrArg (· &&& 2#8) h
  simpa only [BitVec.and_assoc, show (0xFE#8 &&& 2#8 : BitVec 8) = 2#8 from rfl,
    BitVec.zero_and] using h0

/-! ## 1. Pure AST Bridge Lemmas -/

private theorem flt1_stepZ_zext32 {rs : List Ty} {args : Tup (Arg Val) [i32]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    fltStepZ (.let_ (Op.mk (.zext 32 64) args) k) =
      k (BitVec.setWidth 64 args.1.val, ()) := by
  rcases args with ⟨a, ⟨⟩⟩; rfl

private theorem flt1_stepZ_add64 {rs : List Ty} {args : Tup (Arg Val) [i64, i64]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    fltStepZ (.let_ (Op.mk (.add i64) args) k) = k (args.1.val + args.2.1.val, ()) := by
  rcases args with ⟨a, b, ⟨⟩⟩; rfl

private theorem flt1_stepZ_mul64 {rs : List Ty} {args : Tup (Arg Val) [i64, i64]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    fltStepZ (.let_ (Op.mk (.mul i64) args) k) = k (fltDummyTup [i64]) := rfl

private theorem flt1_stepZ_shl64 {rs : List Ty} {args : Tup (Arg Val) [i64, i64]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    fltStepZ (.let_ (Op.mk (.shl i64) args) k) = k (fltDummyTup [i64]) := rfl

private theorem flt1_stepZ_and32 {rs : List Ty} {args : Tup (Arg Val) [i32, i32]}
    {k : Tup Val [i32] → Expr Val Cont rs} :
    fltStepZ (.let_ (Op.mk (.and i32) args) k) = k (fltDummyTup [i32]) := rfl

private theorem flt1_stepZ_sext32 {rs : List Ty} {args : Tup (Arg Val) [i32]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    fltStepZ (.let_ (Op.mk (.sext 32 64) args) k) = k (fltDummyTup [i64]) := rfl

private theorem flt1_grpB4_cons {rs : List Ty} (v : Tup Val [i32, i32, i32, i32])
    (J : Cont [i32, i32, i32, i32])
    (b : Tup Val [i32, i32, i32, i32] → Expr Val Cont rs)
    (k : Tup Cont [[i32, i32, i32, i32]] → Expr Val Cont rs) :
    fltGrpB4 v J (.group (sig := [[i32, i32, i32, i32]]) (fun _ => .cons b .nil) k) = b v := rfl

private theorem flt1_grpB2_cons {rs : List Ty} (v : Tup Val [i32, i64])
    (J : Cont [i32, i64])
    (b : Tup Val [i32, i64] → Expr Val Cont rs)
    (k : Tup Cont [[i32, i64]] → Expr Val Cont rs) :
    fltGrpB2 v J (.group (sig := [[i32, i64]]) (fun _ => .cons b .nil) k) = b v := rfl

private theorem flt1_step_eq_ite
    (ro nro po cqn bl : Val i32) (h64 pWv pWs pAr pLm pSb pRp rcl : Val i64)
    (Jo : Cont [i32, i32, i64]) (nq qi : Val i32) (tk : Val i64) (Jc : Cont [])
    (qw : Val i32) (Js : Cont [i32, i64]) :
    let e := fltStepExpr ro nro po cqn bl h64 pWv pWs pAr pLm pSb pRp rcl Jo nq qi tk Jc qw Js
    e = .let_ (Op.mk (.and i32) (Arg.var qw, Arg.imm 0x80000000, ())) fun p1 =>
        .let_ (Op.mk (.cmp .ne i32) (Arg.var p1.1, Arg.imm 0, ())) fun p2 =>
        .jnz (Arg.var p2.1) (e |> fltSteps 2 |> fltThen) (e |> fltSteps 2 |> fltElse) := by
  intro e; dsimp only [e]
  simp only [fltStepExpr, fltOuterContExpr, fltHdrExpr,
    fltSteps.eq_1, fltSteps.eq_2, fltStep.eq_1, fltStep.eq_2, fltStep.eq_3, fltStep.eq_4,
    fltLd64.eq_1, fltLd32.eq_1, fltCall64.eq_1, fltThen.eq_1, fltElse.eq_1,
    fltGrpK0.eq_1, fltGrpK2.eq_1, fltGrpB3.eq_1, fltDummyVal, fltDummyTup,
    full_bva_filter_row_body]

private theorem flt1_bin_then_body_eq
    (ro nro po cqn bl : Val i32) (h64 pWv pWs pAr pLm pSb pRp rcl : Val i64)
    (Jo : Cont [i32, i32, i64]) (nq qi : Val i32) (tk : Val i64) (Jc : Cont [])
    (qw : Val i32) (Js : Cont [i32, i64]) :
    ∃ k : Tup Val [i64] → Tup Val [i64] → Tup Val [i64] → Expr Val Cont [i32],
      (fltStepExpr ro nro po cqn bl h64 pWv pWs pAr pLm pSb pRp rcl Jo nq qi tk Jc qw Js
        |> fltSteps 2 |> fltThen) =
      (.let_ (Op.mk (.and i32) (Arg.var qw, Arg.imm 0x7FFFFFFF, ())) fun q =>
       .let_ (Op.mk (.zext 32 64) (Arg.var q.1, ())) fun q64 =>
       .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun s1 =>
       .let_ (Op.mk (.shl i64) (Arg.var q64.1, Arg.var s1.1, ())) fun q2 =>
       .let_ (Op.mk (.mul i64) (Arg.var q2.1, Arg.imm 4, ())) fun q2b =>
       .let_ (Op.mk (.add i64) (Arg.var pWv, Arg.var q2b.1, ())) fun w0a =>
       .load i32 (Arg.var w0a.1) fun qoff =>
       .let_ (Op.mk (.zext 32 64) (Arg.var qoff, ())) fun qoff64 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var q.1, ())) fun q64b =>
       .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun s1b =>
       .let_ (Op.mk (.shl i64) (Arg.var q64b.1, Arg.var s1b.1, ())) fun q2c =>
       .let_ (Op.mk (.add i64) (Arg.var q2c.1, Arg.imm 1, ())) fun q2p1 =>
       .let_ (Op.mk (.mul i64) (Arg.var q2p1.1, Arg.imm 4, ())) fun q2p1b =>
       .let_ (Op.mk (.add i64) (Arg.var pWv, Arg.var q2p1b.1, ())) fun w1a =>
       .load i32 (Arg.var w1a.1) fun qsz =>
       .let_ (Op.mk (.zext 32 64) (Arg.var qsz, ())) fun qsz64 =>
       .let_ (Op.mk (.add i64) (Arg.var qoff64.1, Arg.var qsz64.1, ())) fun qend =>
       .let_ (Op.mk (.add i64) (Arg.var tk, Arg.imm 1, ())) fun tk1 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var q.1, ())) fun q64c =>
       .let_ (Op.mk (.mul i64) (Arg.var q64c.1, Arg.imm 4, ())) fun rpb =>
       .let_ (Op.mk (.add i64) (Arg.var pRp, Arg.var rpb.1, ())) fun rpa =>
       .load i32 (Arg.var rpa.1) fun deg =>
       .let_ (Op.mk (.zext 32 64) (Arg.var deg, ())) fun deg64 =>
       .call "full_bva_clines_fid" (as := [i64]) (bs := [i64]) (Arg.var deg64.1, ()) fun rcb =>
       .let_ (Op.mk (.add i64) (Arg.var tk1.1, Arg.var rcb.1, ())) fun tk2 =>
       k qoff64 qend tk2) ∧
      ∀ qoff qsz rcb,
        k (BitVec.setWidth 64 qoff, ())
          (BitVec.setWidth 64 qoff + BitVec.setWidth 64 qsz, ())
          (tk + 1#64 + rcb, ()) =
        (fltStepExpr ro nro po cqn bl h64 pWv pWs pAr pLm pSb pRp rcl Jo nq qi tk Jc qw Js
          |> fltSteps 2 |> fltThen |> fltStepsZ 6 |> fltLd32 qoff |> fltStepZ |> fltStepsZ 6
          |> fltLd32 qsz |> fltStepsZ 3 |> fltStepsZ 3 |> fltLd32 0#32 |> fltStepZ
          |> fltCall64 rcb |> fltStepZ) := by
  simp only [fltStepExpr, fltOuterContExpr, fltHdrExpr,
    fltSteps.eq_1, fltSteps.eq_2, fltStep.eq_1, fltStep.eq_2, fltStep.eq_3, fltStep.eq_4,
    fltLd64.eq_1, fltLd32.eq_1, fltCall64.eq_1, fltThen.eq_1,
    fltGrpK0.eq_1, fltGrpK2.eq_1, fltGrpB3.eq_1, fltDummyVal, fltDummyTup,
    full_bva_filter_row_body]
  simp only [fltStepsZ.eq_1, fltStepsZ.eq_2, flt1_stepZ_zext32, flt1_stepZ_add64,
    flt1_stepZ_mul64, flt1_stepZ_shl64, flt1_stepZ_and32, flt1_stepZ_sext32,
    Arg.val.eq_1, Arg.val.eq_2, fltLd32.eq_1, fltCall64.eq_1, fltDummyVal, fltDummyTup]
  exact ⟨_, rfl, fun _ _ _ => rfl⟩

private theorem flt1_bin_grp2_eq
    (ro nro po cqn bl : Val i32) (h64 pWv pWs pAr pLm pSb pRp rcl : Val i64)
    (Jo : Cont [i32, i32, i64]) (nq qi : Val i32) (tk : Val i64) (Jc : Cont [])
    (qw : Val i32) (Js : Cont [i32, i64]) (qoff qsz : Val i32) (rcb : Val i64) :
    (fltStepExpr ro nro po cqn bl h64 pWv pWs pAr pLm pSb pRp rcl Jo nq qi tk Jc qw Js
      |> fltSteps 2 |> fltThen |> fltStepsZ 6 |> fltLd32 qoff |> fltStepZ |> fltStepsZ 6
      |> fltLd32 qsz |> fltStepsZ 3 |> fltStepsZ 3 |> fltLd32 0#32 |> fltStepZ
      |> fltCall64 rcb |> fltStepZ) =
    .group (sig := [[i32, i64]])
      (fun _ => .cons (fun p => .jump Js (Arg.var p.1, Arg.var (tk + 1#64 + rcb), ())) .nil)
      (fun Jb =>
        fltStepExpr ro nro po cqn bl h64 pWv pWs pAr pLm pSb pRp rcl Jo nq qi tk Jc qw Js
          |> fltSteps 2 |> fltThen |> fltStepsZ 6 |> fltLd32 qoff |> fltStepZ |> fltStepsZ 6
          |> fltLd32 qsz |> fltStepsZ 3 |> fltStepsZ 3 |> fltLd32 0#32 |> fltStepZ
          |> fltCall64 rcb |> fltStepZ |> fltGrpK2 Jb.1) := by
  simp only [fltStepExpr, fltOuterContExpr, fltHdrExpr,
    fltSteps.eq_1, fltSteps.eq_2, fltStep.eq_1, fltStep.eq_2, fltStep.eq_3, fltStep.eq_4,
    fltLd64.eq_1, fltLd32.eq_1, fltCall64.eq_1, fltThen.eq_1,
    fltGrpK0.eq_1, fltGrpK2.eq_1, fltGrpB3.eq_1, fltDummyVal, fltDummyTup,
    full_bva_filter_row_body]
  simp only [fltStepsZ.eq_1, fltStepsZ.eq_2, flt1_stepZ_zext32, flt1_stepZ_add64,
    flt1_stepZ_mul64, flt1_stepZ_shl64, flt1_stepZ_and32, flt1_stepZ_sext32,
    Arg.val.eq_1, Arg.val.eq_2, fltLd32.eq_1, fltCall64.eq_1, fltGrpK2.eq_1,
    fltDummyVal, fltDummyTup]
  rfl

private theorem flt1_large_else_body_eq
    (ro nro po cqn bl : Val i32) (h64 pWv pWs pAr pLm pSb pRp rcl : Val i64)
    (Jo : Cont [i32, i32, i64]) (nq qi : Val i32) (tk : Val i64) (Jc : Cont [])
    (qw : Val i32) (Js : Cont [i32, i64]) :
    ∃ k : Val i32 → Tup Val [i64] → Expr Val Cont [i32],
      (fltStepExpr ro nro po cqn bl h64 pWv pWs pAr pLm pSb pRp rcl Jo nq qi tk Jc qw Js
        |> fltSteps 2 |> fltElse) =
      (.let_ (Op.mk (.zext 32 64) (Arg.var qw, ())) fun p1 =>
       .let_ (Op.mk (.add i64) (Arg.var p1.1, Arg.imm 2, ())) fun p2 =>
       .let_ (Op.mk (.mul i64) (Arg.var p2.1, Arg.imm 4, ())) fun p3 =>
       .let_ (Op.mk (.add i64) (Arg.var pAr, Arg.var p3.1, ())) fun p4 =>
       .load i32 (Arg.var p4.1) fun csz =>
       .let_ (Op.mk (.add i64) (Arg.var tk, Arg.imm 1, ())) fun p5 =>
       k csz p5) ∧
      ∀ csz, k csz (tk + 1#64, ()) =
        fltLargeHdrExpr ro nro po cqn bl h64 pWv pWs pAr pLm pSb pRp rcl Jo nq qi tk Jc qw Js
          csz := by
  simp only [fltLargeHdrExpr, fltStepExpr, fltOuterContExpr, fltHdrExpr,
    fltSteps.eq_1, fltSteps.eq_2, fltStep.eq_1, fltStep.eq_2, fltStep.eq_3, fltStep.eq_4,
    fltStepsZ.eq_1, fltStepsZ.eq_2, flt1_stepZ_zext32, flt1_stepZ_add64, flt1_stepZ_mul64,
    Arg.val.eq_1, Arg.val.eq_2,
    fltLd64.eq_1, fltLd32.eq_1, fltCall64.eq_1, fltThen.eq_1, fltElse.eq_1,
    fltGrpK0.eq_1, fltGrpK2.eq_1, fltGrpB3.eq_1, fltDummyVal, fltDummyTup,
    full_bva_filter_row_body]
  exact ⟨_, rfl, fun _ => rfl⟩

private theorem flt1_large_hdr_is_grp4
    (ro nro po cqn bl : Val i32) (h64 pWv pWs pAr pLm pSb pRp rcl : Val i64)
    (Jo : Cont [i32, i32, i64]) (nq qi : Val i32) (tk : Val i64) (Jc : Cont [])
    (qw : Val i32) (Js : Cont [i32, i64]) (csz : Val i32) :
    ∃ (b : Tup Val [i32, i32, i32, i32] → Expr Val Cont [i32])
      (k : Tup Cont [[i32, i32, i32, i32]] → Expr Val Cont [i32]),
      fltLargeHdrExpr ro nro po cqn bl h64 pWv pWs pAr pLm pSb pRp rcl Jo nq qi tk Jc qw Js csz =
        .group (sig := [[i32, i32, i32, i32]]) (fun _ => .cons b .nil) k ∧
      ∀ v, ∃ (b2 : Tup Val [i32, i64] → Expr Val Cont [i32])
             (k2 : Tup Cont [[i32, i64]] → Expr Val Cont [i32]),
        b v = .group (sig := [[i32, i64]]) (fun _ => .cons b2 .nil) k2 := by
  simp only [fltLargeHdrExpr, fltStepExpr, fltOuterContExpr, fltHdrExpr,
    fltSteps.eq_1, fltSteps.eq_2, fltStep.eq_1, fltStep.eq_2, fltStep.eq_3, fltStep.eq_4,
    fltStepsZ.eq_1, fltStepsZ.eq_2, flt1_stepZ_zext32, flt1_stepZ_add64, flt1_stepZ_mul64,
    Arg.val.eq_1, Arg.val.eq_2,
    fltLd64.eq_1, fltLd32.eq_1, fltCall64.eq_1, fltThen.eq_1, fltElse.eq_1,
    fltGrpK0.eq_1, fltGrpK2.eq_1, fltGrpB3.eq_1, fltDummyVal, fltDummyTup,
    full_bva_filter_row_body]
  exact ⟨_, _, rfl, fun _ => ⟨_, _, rfl⟩⟩

private theorem flt1_post_mark_eq_ite
    (ro nro po cqn bl : Val i32) (h64 pWv pWs pAr pLm pSb pRp rcl : Val i64)
    (Jo : Cont [i32, i32, i64]) (nq qi : Val i32) (tk : Val i64) (Jc : Cont [])
    (qw : Val i32) (Js : Cont [i32, i64]) (csz min_l min_d fc k : Val i32)
    (Jp : Cont [i32, i32, i32, i32]) (Jclr : Cont [i32, i64]) :
    ∃ t,
      (fltLargeHdrExpr ro nro po cqn bl h64 pWv pWs pAr pLm pSb pRp rcl Jo nq qi tk Jc qw Js csz
        |> fltGrpB4 (min_l, min_d, fc, k, ()) Jp
        |> fltGrpK2 Jclr) =
      .let_ (Op.mk (.cmp .eq i32) (Arg.var fc, Arg.imm 1#32, ())) fun p1 =>
      .jnz (Arg.var p1.1)
        (.let_ (Op.mk (.cmp .ne i32) (Arg.var min_l, Arg.imm 0xFFFFFFFF#32, ())) fun p2 =>
          .jnz (Arg.var p2.1) t (.jump Jclr (Arg.var nq, Arg.var (tk + 1#64), ())))
        (.jump Jclr (Arg.var nq, Arg.var (tk + 1#64), ())) := by
  simp only [fltLargeHdrExpr, fltStepExpr, fltOuterContExpr, fltHdrExpr,
    fltSteps.eq_1, fltSteps.eq_2, fltStep.eq_1, fltStep.eq_2, fltStep.eq_3, fltStep.eq_4,
    fltStepsZ.eq_1, fltStepsZ.eq_2, flt1_stepZ_zext32, flt1_stepZ_add64, flt1_stepZ_mul64,
    Arg.val.eq_1, Arg.val.eq_2,
    fltLd64.eq_1, fltLd32.eq_1, fltCall64.eq_1, fltThen.eq_1, fltElse.eq_1,
    fltGrpK0.eq_1, fltGrpK2.eq_1, fltGrpB3.eq_1, fltGrpB4.eq_1, fltDummyVal, fltDummyTup,
    full_bva_filter_row_body]
  exact ⟨_, rfl⟩

/-! ## 2. Cleanup Loop WP -/

private theorem flt_cleanup_loop_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off nrow_off par_off cur_qn best_lit new_qn qi : Val i32}
    {ticks r_cl : Val i64} {J_out : Cont [i32, i32, i64]} {J_cond : Cont []}
    {step : Nat} {ar sb : List (BitVec 32)} {ant : BitVec 64} {mc : Mem 64}
    (hslen : s.LengthsOk c)
    (hout : FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
      cur_qn.toNat best_lit.toNat new_qn.toNat sb)
    (har_inv : FidFilterArInv c s nrow_off.toNat 0 new_qn.toNat sb ar)
    (hmc : (FullMem c (fltMkSt s ant ar s.core.lit_mark sb) ⋆ R) mc)
    (hRet : ∀ (ant' : BitVec 64) (m' : Mem 64),
      let s' : FullState :=
        { s with scratch := { s.scratch with scratch_buf := sb, ant_sz := ant' } }
      (FullMem c s' ⋆ R) m' → Q (new_qn, ()) m') :
    wp Γ Q X (fltHdrExpr 0#32 row_off nrow_off par_off cur_qn best_lit c.hdr c.pWvec c.pWstk
      c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl
      |> fltGrpB3 (new_qn, qi, ticks, ()) J_out
      |> fltGrpB0 J_cond) mc := by
  have hscr := c.hscr; have har_b := c.harena; unfold dimacsBound at *
  have hcl := hslen.core_ok; have har_l := hcl.arena_len_arr; have hsb_l := hout.1
  simp only [fltHdrExpr, fltStep.eq_1, fltStep.eq_2, fltStep.eq_3, fltStep.eq_4,
    fltLd64.eq_1, fltCall64.eq_1, fltGrpB3.eq_1, fltGrpB0.eq_1, fltDummyVal, fltDummyTup,
    full_bva_filter_row_body]
  refine wp_while_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) (fun p => p.1)
    (fun (ci, _) => new_qn.toNat - ci.toNat)
    (fun (ci, arc) mp => ci.toNat ≤ new_qn.toNat ∧
      FidFilterArInv c s nrow_off.toNat ci.toNat new_qn.toNat sb arc ∧
      (FullMem c (fltMkSt s ant arc s.core.lit_mark sb) ⋆ R) mp)
    (fun Jci hJci => by c0_hfast; exact hJci (0#32, ar) mc ⟨Nat.zero_le _, har_inv, hmc⟩)
    (fun Jci (ci, arc) mp ⟨hci_le, har_c, hmp⟩ ihci => ?_)
  clear hmc
  dsimp only [fltMkSt] at hmp
  have har_c_l := har_c.1
  c0_hfast_nogrp
  rotate_left 1
  · have hdone : ci.toNat = new_qn.toNat := by
      have : ¬ (ci.toNat < new_qn.toNat) := by assumption
      omega
    rw [hdone] at har_c
    rw [fidFilterArInv_done har_l har_c] at hmp
    refine wp_join_state1 (t := i64) (α := BitVec 64) id
      (fun ant' mp' => mp' = mp ∧ ant' =
        (if ticks.toNat < ant.toNat then ant - ticks else 0#64))
      (fun _ ant' mp' ⟨hmp', _⟩ => by
        rw [hmp']; c0_hfast
        exact hRet ant' m (by simpa only [fltMkSt, id] using hm))
      (fun Jant hJant => ?_)
    c0_hfast_nogrp
    · exact hJant (ant - ticks) mp ⟨rfl, by rw [ite_eq_left (by assumption)]⟩
    · exact hJant 0#64 mp ⟨rfl, by rw [ite_eq_right (by assumption)]⟩
  have hci_lt : ci.toNat < new_qn.toNat := by assumption
  have hci_cap : nrow_off.toNat + ci.toNat < c.scratch_cap := by
    have := har_c.2.2.1; omega
  have hno_ci_sb : (BitVec.setWidth 64 (nrow_off + ci)).toNat < sb.length := by
    rw [fid_bv64_32, hsb_l]; c0_bound
  have hno_ci_eq : (nrow_off + ci).toNat = nrow_off.toNat + ci.toNat := by c0_bound
  have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
  c0_hfast_nogrp
  refine wp_join0
    (fun mp' => ∃ ar', FidFilterArInv c s nrow_off.toNat (ci.toNat + 1) new_qn.toNat sb ar' ∧
      (FullMem c (fltMkSt s ant ar' s.core.lit_mark sb) ⋆ R) mp')
    (fun _ mp' ⟨ar', har', hmp'⟩ => by
      c0_hfast; exact ihci (ci + 1#32, ar') mp' (by dsimp only; rw [hci1]; omega)
        ⟨by rw [hci1]; omega, by rwa [hci1], hmp'⟩)
    (fun Jnext hJnext => ?_)
  c0_hfast_nogrp
  · have hwb_eq : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'hno_ci_sb &&&
        0x80000000#32) = 0#32 := by assumption
    have hnb_inv : (sb[nrow_off.toNat + ci.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
      rw [List.getElem?_eq_getElem (by rw [hsb_l]; omega), Option.getD_some]
      simpa only [fid_bv64_32, hno_ci_eq] using hwb_eq
    have ⟨hidx_cap, har_step⟩ := fidFilterArInv_clear_step har_l har_c hci_lt hnb_inv
    let rw_v := sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'hno_ci_sb
    have hrw_nat : rw_v.toNat = (sb[nrow_off.toNat + ci.toNat]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem (by rw [hsb_l]; omega), Option.getD_some]
      dsimp only [rw_v]; simp only [fid_bv64_32, hno_ci_eq]
    have hrw_ar : (BitVec.setWidth 64 rw_v).toNat < arc.length := by
      rw [fid_bv64_32, har_c_l, hrw_nat]; exact hidx_cap
    c0_hfast
    dsimp only at hm
    have hidx_eq : (BitVec.setWidth 64 rw_v).toNat =
        (sb[nrow_off.toNat + ci.toNat]?.getD 0#32).toNat := by
      rw [fid_bv64_32]; exact hrw_nat
    have hidx_cap2 : (sb[nrow_off.toNat + ci.toNat]?.getD 0#32).toNat < arc.length := by
      rw [har_c_l]; exact hidx_cap
    have hv_eq : arc[(BitVec.setWidth 64 rw_v).toNat]'hrw_ar =
        arc[(sb[nrow_off.toNat + ci.toNat]?.getD 0#32).toNat]'hidx_cap2 := by
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem hrw_ar, ← List.getElem?_eq_getElem hidx_cap2, hidx_eq]
    have hm_set : arc.set (BitVec.setWidth 64 rw_v).toNat
          (arc[(BitVec.setWidth 64 rw_v).toNat]'hrw_ar &&& ~~~(0x02000000 : BitVec 32)) =
        arc.set (sb[nrow_off.toNat + ci.toNat]?.getD 0#32).toNat
          (arc[(sb[nrow_off.toNat + ci.toNat]?.getD 0#32).toNat]'hidx_cap2 &&&
            ~~~0x02000000#32) := by
      rw [hv_eq, hidx_eq]; rfl
    dsimp only [rw_v] at hm_set
    rw [hm_set] at hm
    exact hJnext m ⟨_, har_step, hm⟩
  · have hwb_ne : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'hno_ci_sb &&&
        0x80000000#32) ≠ 0#32 := by assumption
    have hbin_inv : (sb[nrow_off.toNat + ci.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
      rw [List.getElem?_eq_getElem (by rw [hsb_l]; omega), Option.getD_some]
      simpa only [fid_bv64_32, hno_ci_eq] using hwb_ne
    exact hJnext mp ⟨arc, fidFilterArInv_clear_skip har_c hci_lt hbin_inv, hmp⟩

/-! ## 3. Binary & Large Step Branches -/

private theorem flt1_bin_branch_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X →
      Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off nrow_off par_off cur_qn best_lit new_qn qi : Val i32}
    {ticks r_cl : Val i64} {J_out : Cont [i32, i32, i64]} {J_cond : Cont []}
    {qw : Val i32} {J_step : Cont [i32, i64]}
    {step bump : Nat} {ar sb : List (BitVec 32)} {mp : Mem 64}
    (hslen : s.LengthsOk c) (hdw : DenseWatchesInv F_cur s.core)
    (hstep : 1 ≤ step) (hro_n : row_off.toNat = (s.scratch.scratch_buf[fidStepsCap c.scratch_cap +
      (step - 1)]?.getD 0#32).toNat)
    (hcqn_n : cur_qn.toNat = (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
      (step - 1)]?.getD 0#32).toNat)
    (hnro_n : nrow_off.toNat = bump) (hno_le : nrow_off.toNat ≤ par_off.toNat)
    (hpo_fit : par_off.toNat + (par_off.toNat - nrow_off.toNat) ≤ c.scratch_cap)
    (hnew_lt : new_qn.toNat < par_off.toNat - nrow_off.toNat)
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hmat : FidBvaMatrixInv c F_cur s step bump)
    (hout : FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
      cur_qn.toNat best_lit.toNat new_qn.toNat sb)
    (har_inv : FidFilterArInv c s nrow_off.toNat 0 new_qn.toNat sb ar)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hrefs_ar :
      fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
      ∀ r ∈ fullArenaClauseRefsCore s.core,
        fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
        fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
        fullArenaClauseLitsCore { s.core with arena := ar } r =
          fullArenaClauseLitsCore s.core r)
    (hbin : (qw &&& 0x80000000#32) ≠ 0#32)
    (hqw_eq : qw = s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32)
    (hmp : (FullMem c (fltMkSt s s.scratch.ant_sz ar s.core.lit_mark sb) ⋆ R) mp)
    (hJstep : ∀ (nq' : BitVec 32) (tk' : BitVec 64) (ar' sb' : List (BitVec 32)) (mp' : Mem 64),
      FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
        cur_qn.toNat best_lit.toNat nq'.toNat sb' →
      FidFilterArInv c s nrow_off.toNat 0 nq'.toNat sb' ar' →
      FullWitnessInv c F0 F_cur { s.core with arena := ar' } →
      (fullArenaClauseRefsCore { s.core with arena := ar' } = fullArenaClauseRefsCore s.core ∧
        ∀ r ∈ fullArenaClauseRefsCore s.core,
          fullArenaClauseGarbCore { s.core with arena := ar' } r =
            fullArenaClauseGarbCore s.core r ∧
          fullArenaClauseSizeCore { s.core with arena := ar' } r =
            fullArenaClauseSizeCore s.core r ∧
          fullArenaClauseLitsCore { s.core with arena := ar' } r =
            fullArenaClauseLitsCore s.core r) →
      (FullMem c (fltMkSt s s.scratch.ant_sz ar' s.core.lit_mark sb') ⋆ R) mp' →
      J_step (nq', tk', ()) mp') :
    wp Γ Q X (fltStepExpr row_off nrow_off par_off cur_qn best_lit c.hdr c.pWvec c.pWstk c.pArena
      c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi ticks J_cond qw J_step
      |> fltSteps 2 |> fltThen) mp := by
  have hmx := c.hmaxv; unfold dimacsBound at *
  have hcl := hslen.core_ok; have hcv_le := hcl.cur_vars_le
  let q := (qw &&& 0x7FFFFFFF#32).toNat
  have hfr_res := hmat.2.2.2.2.2 (step - 1) (by omega)
  have ⟨_, _, _, hok_old, _, _⟩ := hfr_res.2.2.2.2.2 qi.toNat (by omega)
  rw [← hro_n, ← hqw_eq] at hok_old
  have hbin_info := hok_old
  unfold FidBvaRowEntryOk at hbin_info; rw [ite_eq_left hbin] at hbin_info
  have hq_lt : q < 2 * s.core.cur_vars := hbin_info.1
  have hq_shl1 : (BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32) <<< (1 : Nat)).toNat = 2 * q := by
    dsimp only [q]; c0_bound
  have hq_w0 : (BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32) <<< (1 : Nat)).toNat <
      s.core.wvec.length := by rw [hq_shl1, hcl.wvec_len]; omega
  have hq_w1 : ((BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32) <<< (1 : Nat)) + 1#64).toNat <
      s.core.wvec.length := by
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, hq_shl1,
      Nat.mod_eq_of_lt (by omega), hcl.wvec_len]
    omega
  have hq_rp : (BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32)).toNat < s.core.repr.length := by
    rw [fid_bv64_32, hcl.repr_len]; exact Nat.lt_of_lt_of_le hq_lt (by omega)
  have hqoff_bv : s.core.wvec[(BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32) <<<
      (1 : Nat)).toNat]'hq_w0 = BitVec.ofNat 32 (fullWatchOffCore s.core q) := by
    apply BitVec.eq_of_toNat_eq; unfold fullWatchOffCore
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
    apply congrArg BitVec.toNat; apply Option.some.inj
    rw [← List.getElem?_eq_getElem hq_w0, hq_shl1]
    rw [List.getElem?_eq_getElem (by rw [hcl.wvec_len]; omega), Option.getD_some]
  have hqsz_bv : s.core.wvec[((BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32) <<<
      (1 : Nat)) + 1#64).toNat]'hq_w1 = BitVec.ofNat 32 (fullWatchSizeCore s.core q) := by
    apply BitVec.eq_of_toNat_eq; unfold fullWatchSizeCore
    have hidx1 : ((BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32) <<<
        (1 : Nat)) + 1#64).toNat = 2 * q + 1 := by
      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, hq_shl1,
        Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
    apply congrArg BitVec.toNat; apply Option.some.inj
    rw [← List.getElem?_eq_getElem hq_w1, hidx1]
    rw [List.getElem?_eq_getElem (by rw [hcl.wvec_len]; omega), Option.getD_some]
  obtain ⟨k_bin, hthen, hk_bin⟩ := flt1_bin_then_body_eq row_off nrow_off par_off cur_qn best_lit
    c.hdr c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi ticks
    J_cond qw J_step
  rw [hthen]
  dsimp only [fltMkSt] at hmp
  c0_hfast_nogrp
  fid_call hClines; intro r_cl_bin
  c0_hfast_nogrp
  dsimp only
  change wp Γ Q X (k_bin
    (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32) <<<
      (1 : Nat)).toNat]'hq_w0), ())
    (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32) <<<
      (1 : Nat)).toNat]'hq_w0) +
     BitVec.setWidth 64 (s.core.wvec[((BitVec.setWidth 64 (qw &&& 0x7FFFFFFF#32) <<<
      (1 : Nat)) + 1#64).toNat]'hq_w1), ())
    (ticks + 1#64 + r_cl_bin, ())) mp
  rw [hqoff_bv, hqsz_bv, hk_bin]
  rw [flt1_bin_grp2_eq]
  refine wp_join_state (ts := [i32, i64]) (α := BitVec 32 × BitVec 64 × List (BitVec 32))
    (fun x => (x.1, x.2.1, ()))
    (fun (nq', qp', sb') mp' =>
      FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
        cur_qn.toNat best_lit.toNat nq'.toNat sb' ∧
      FidFilterArInv c s nrow_off.toNat 0 nq'.toNat sb' ar ∧
      (FullMem c (fltMkSt s s.scratch.ant_sz ar s.core.lit_mark sb') ⋆ R) mp')
    (fun _ (nq', qp', sb') mp' ⟨ho', ha', hm'⟩ => by
      c0_hfast
      exact hJstep nq' (ticks + 1#64 + r_cl_bin) ar sb' mp' ho' ha' hw_ar hrefs_ar hm')
    (fun Jbin hJbin =>
      flt_bin_loop_wp (J_out := J_out) (J_cond := J_cond) (J_step := J_step) (J_bin := Jbin)
        (r_cl := r_cl) (r_cl_bin := r_cl_bin) (ticks := ticks) hslen hdw hstep hro_n hcqn_n
        hnro_n hno_le hpo_fit hnew_lt hqi_lt hmat hout har_inv hbin hqw_eq hmp
        fun nq' qp' sb' mp' ho' ha' hm' => hJbin (nq', qp', sb') mp' ⟨ho', ha', hm'⟩)

private theorem flt1_large_branch_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X →
      Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    (hMatch : ∀ a m Q X, fidBvaMatchLargeBvaSpec a m Q X →
      Γ "full_bva_match_large_bva_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off nrow_off par_off cur_qn best_lit new_qn qi : Val i32}
    {ticks r_cl : Val i64} {J_out : Cont [i32, i32, i64]} {J_cond : Cont []}
    {qw : Val i32} {J_step : Cont [i32, i64]}
    {step bump : Nat} {ar sb : List (BitVec 32)} {mp : Mem 64}
    (hslen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnodup : FullArenaVarsNodup s) (hdw : DenseWatchesInv F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hdm0 : s.core.dense_mode ≠ 0#64)
    (hstep : 1 ≤ step) (hro_n : row_off.toNat = (s.scratch.scratch_buf[fidStepsCap c.scratch_cap +
      (step - 1)]?.getD 0#32).toNat)
    (hcqn_n : cur_qn.toNat = (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
      (step - 1)]?.getD 0#32).toNat)
    (hnro_n : nrow_off.toNat = bump) (hno_le : nrow_off.toNat ≤ par_off.toNat)
    (hpo_fit : par_off.toNat + (par_off.toNat - nrow_off.toNat) ≤ c.scratch_cap)
    (hnew_lt : new_qn.toNat < par_off.toNat - nrow_off.toNat)
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hmat : FidBvaMatrixInv c F_cur s step bump)
    (hout : FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
      cur_qn.toNat best_lit.toNat new_qn.toNat sb)
    (har_inv : FidFilterArInv c s nrow_off.toNat 0 new_qn.toNat sb ar)
    (hlm0_b1 : ∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hlm_b0 : ∀ r < step, (s.core.lit_mark[(s.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8
      &&& 1#8) ≠ 0#8)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hrefs_ar :
      fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
      ∀ r ∈ fullArenaClauseRefsCore s.core,
        fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
        fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
        fullArenaClauseLitsCore { s.core with arena := ar } r =
          fullArenaClauseLitsCore s.core r)
    (hnb : (qw &&& 0x80000000#32) = 0#32)
    (hqw_eq : qw = s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32)
    (hmp : (FullMem c (fltMkSt s s.scratch.ant_sz ar s.core.lit_mark sb) ⋆ R) mp)
    (hJstep : ∀ (nq' : BitVec 32) (tk' : BitVec 64) (ar' sb' : List (BitVec 32)) (mp' : Mem 64),
      FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
        cur_qn.toNat best_lit.toNat nq'.toNat sb' →
      FidFilterArInv c s nrow_off.toNat 0 nq'.toNat sb' ar' →
      FullWitnessInv c F0 F_cur { s.core with arena := ar' } →
      (fullArenaClauseRefsCore { s.core with arena := ar' } = fullArenaClauseRefsCore s.core ∧
        ∀ r ∈ fullArenaClauseRefsCore s.core,
          fullArenaClauseGarbCore { s.core with arena := ar' } r =
            fullArenaClauseGarbCore s.core r ∧
          fullArenaClauseSizeCore { s.core with arena := ar' } r =
            fullArenaClauseSizeCore s.core r ∧
          fullArenaClauseLitsCore { s.core with arena := ar' } r =
            fullArenaClauseLitsCore s.core r) →
      (FullMem c (fltMkSt s s.scratch.ant_sz ar' s.core.lit_mark sb') ⋆ R) mp' →
      J_step (nq', tk', ()) mp') :
    wp Γ Q X (fltStepExpr row_off nrow_off par_off cur_qn best_lit c.hdr c.pWvec c.pWstk c.pArena
      c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi ticks J_cond qw J_step
      |> fltSteps 2 |> fltElse) mp := by
  have har_b := c.harena; have hmx := c.hmaxv; unfold dimacsBound at *
  have hcl := hslen.core_ok; have har_l := hcl.arena_len_arr; have hlm0_l := hcl.lit_mark_len
  have har_cur_l := har_inv.1
  have hfr_res := hmat.2.2.2.2.2 (step - 1) (by omega)
  have ⟨_, _, _, hok_old, _, _⟩ := hfr_res.2.2.2.2.2 qi.toNat (by omega)
  rw [← hro_n, ← hqw_eq] at hok_old
  have hlar := hok_old
  unfold FidBvaRowEntryOk at hlar; rw [ite_eq_right (fun h => h hnb)] at hlar
  have hqw_ref := hlar.1; have hqw_garb := hlar.2.1
  have hwf := hw.arena.refs_wf qw.toNat hqw_ref
  have hqw2_ar : (BitVec.setWidth 64 qw + 2#64).toNat < ar.length := by
    rw [har_cur_l]; have := hcl.arena_len_le; c0_bound
  have har_qw : ar[qw.toNat + 2]? = s.core.arena[qw.toNat + 2]? ∧
      ∀ j < (ar[(BitVec.setWidth 64 qw + 2#64).toNat]'hqw2_ar).toNat,
        ar[qw.toNat + 3 + j]? = s.core.arena[qw.toNat + 3 + j]? := by
    have har_ext : ∀ idx < c.arena_cap,
        qw.toNat + 2 ≤ idx →
        idx < qw.toNat + 3 + fullArenaClauseSizeCore s.core qw.toNat →
        ar[idx]? = s.core.arena[idx]? := by
      intro idx hidx_cap hge hlt
      rcases har_inv.2.2.2.2.2 idx hidx_cap with heq | ⟨t_i, ht0, hti, hwb_i, hidx_eq, _, _⟩
      · exact heq
      · exfalso
        have hdisj := hw.arena.disjoint hqw_ref (har_inv.2.2.2.1 t_i ht0 hti hwb_i).1 (by omega)
        omega
    have h2e : ar[qw.toNat + 2]? = s.core.arena[qw.toNat + 2]? :=
      har_ext (qw.toNat + 2) (by have := hcl.arena_len_le; omega) (by omega) (by omega)
    have hsz_qw : (ar[(BitVec.setWidth 64 qw + 2#64).toNat]'hqw2_ar).toNat =
        fullArenaClauseSizeCore s.core qw.toNat := by
      have hidx2 : (BitVec.setWidth 64 qw + 2#64).toNat = qw.toNat + 2 := by c0_bound
      unfold fullArenaClauseSizeCore
      apply congrArg BitVec.toNat; apply Option.some.inj
      rw [← List.getElem?_eq_getElem hqw2_ar, hidx2, h2e,
        List.getElem?_eq_getElem (by rw [har_l]; have := hcl.arena_len_le; omega),
        Option.getD_some]
    exact ⟨h2e, fun j hj => har_ext (qw.toNat + 3 + j)
      (by have := hcl.arena_len_le; omega) (by omega) (by rw [← hsz_qw]; omega)⟩
  have hcsz_eq : (ar[(BitVec.setWidth 64 qw + 2#64).toNat]'hqw2_ar).toNat =
      fullArenaClauseSizeCore s.core qw.toNat := by
    have hidx2 : (BitVec.setWidth 64 qw + 2#64).toNat = qw.toNat + 2 := by c0_bound
    unfold fullArenaClauseSizeCore
    apply congrArg BitVec.toNat; apply Option.some.inj
    rw [← List.getElem?_eq_getElem hqw2_ar, hidx2, har_qw.1,
      List.getElem?_eq_getElem (by rw [har_l]; have := hcl.arena_len_le; omega),
      Option.getD_some]
  obtain ⟨k_el, helse, hk_el⟩ := flt1_large_else_body_eq row_off nrow_off par_off cur_qn best_lit
    c.hdr c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi ticks
    J_cond qw J_step
  rw [helse]
  dsimp only [fltMkSt] at hmp
  c0_hfast_nogrp
  let csz := ar[(BitVec.setWidth 64 qw + 2#64).toNat]'hqw2_ar
  have hqw_csz_le : qw.toNat + 3 + csz.toNat ≤ c.arena_cap := by
    rw [hcsz_eq]; have := hcl.arena_len_le; omega
  change wp Γ Q X (k_el csz (ticks + 1#64, ())) mp
  rw [hk_el]
  obtain ⟨b4, k4, h4, hb4⟩ := flt1_large_hdr_is_grp4 row_off nrow_off par_off cur_qn best_lit
    c.hdr c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi ticks
    J_cond qw J_step csz
  rw [h4]
  refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 8))
    (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ()))
    (fun (min_l, min_d, fc, k, lm') mp' =>
      k.toNat ≤ csz.toNat ∧
      LmBit2Inv c ar s.core.lit_mark qw.toNat 0 k.toNat lm' ∧
      (∀ l < 2 * c.max_vars, (lm'[l]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (s.core.lit_mark[l]?.getD 0#8 &&& 1#8) = 0#8) ∧
      (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars) ∧
      (FullMem c (fltMkSt s s.scratch.ant_sz ar lm' sb) ⋆ R) mp')
    (fun _ (min_l, min_d, fc, k, lm') mp' ⟨hk_le, hlm', hb1', hml', hmp'⟩ => ?_)
    (fun Jpost hJpost => by
      have hmk := flt_mark_loop_wp (Γ := Γ) (Q := Q) (X := X)
        (row_off := row_off) (nrow_off := nrow_off) (par_off := par_off) (cur_qn := cur_qn)
        (best_lit := best_lit) (new_qn := new_qn) (qi := qi)
        (J_out := J_out) (J_cond := J_cond) (J_step := J_step) (J_post := Jpost)
        (r_cl := r_cl) (ticks := ticks) (csz := csz)
        hslen hw har_cur_l hlm0_l (fun l hl => flt1_and2_of_andFE (hlm0_b1 l hl))
        hqw_ref hqw_garb hcsz_eq har_qw hmp
        fun min_l min_d fc k lm' mp' hk_le hlm' hb1' hml' hmp' =>
        hJpost (min_l, min_d, fc, k, lm') mp' ⟨hk_le, hlm', hb1', hml', hmp'⟩
      rw [h4, fltGrpK4.eq_1] at hmk
      exact hmk)
  simp only [Blocks.get]
  obtain ⟨b2, k2, h2⟩ := hb4 (min_l, min_d, fc, k, ())
  rw [h2]
  refine wp_join_state (α := BitVec 32 × BitVec 64 × List (BitVec 32) × List (BitVec 32))
    (fun x => (x.1, x.2.1, ()))
    (fun (nq_c, tk_c, ar', sb') mp'' =>
      FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
        cur_qn.toNat best_lit.toNat nq_c.toNat sb' ∧
      FidFilterArInv c s nrow_off.toNat 0 nq_c.toNat sb' ar' ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
      (fullArenaClauseRefsCore { s.core with arena := ar' } = fullArenaClauseRefsCore s.core ∧
        ∀ r ∈ fullArenaClauseRefsCore s.core,
          fullArenaClauseGarbCore { s.core with arena := ar' } r =
            fullArenaClauseGarbCore s.core r ∧
          fullArenaClauseSizeCore { s.core with arena := ar' } r =
            fullArenaClauseSizeCore s.core r ∧
          fullArenaClauseLitsCore { s.core with arena := ar' } r =
            fullArenaClauseLitsCore s.core r) ∧
      (FullMem c (fltMkSt s s.scratch.ant_sz ar' lm' sb') ⋆ R) mp'')
    (fun _ (nq_c, tk_c, ar', sb') mp'' ⟨ho', ha', hwa', hra', hm''⟩ => by
      simp only [Blocks.get]
      have har'_ext : ∀ idx < c.arena_cap,
          qw.toNat + 2 ≤ idx →
          idx < qw.toNat + 3 + fullArenaClauseSizeCore s.core qw.toNat →
          ar'[idx]? = s.core.arena[idx]? := by
        intro idx hidx_cap hge hlt
        rcases ha'.2.2.2.2.2 idx hidx_cap with heq | ⟨t_i, ht0, hti, hwb_i, hidx_eq, _, _⟩
        · exact heq
        · exfalso
          have hdisj := hw.arena.disjoint hqw_ref (ha'.2.2.2.1 t_i ht0 hti hwb_i).1 (by omega)
          omega
      have har'_qw : ar'[qw.toNat + 2]? = s.core.arena[qw.toNat + 2]? ∧
          ∀ j < csz.toNat, ar'[qw.toNat + 3 + j]? = s.core.arena[qw.toNat + 3 + j]? :=
        ⟨har'_ext (qw.toNat + 2) (by omega) (by omega) (by rw [← hcsz_eq]; omega),
         fun j hj => har'_ext (qw.toNat + 3 + j) (by omega) (by omega)
           (by rw [← hcsz_eq]; exact Nat.add_lt_add_left hj _)⟩
      have hlm'_clr : LmBit2Inv c ar' s.core.lit_mark qw.toNat 0 csz.toNat lm' := by
        refine ⟨hlm'.1, fun l hl => (hlm'.2 l hl).imp_right fun ⟨j, hj1, hj2, harj, heq⟩ =>
          ⟨j, hj1, Nat.lt_of_lt_of_le hj2 hk_le, ?_, heq⟩⟩
        have hj_csz : j < csz.toNat := Nat.lt_of_lt_of_le hj2 hk_le
        have hj_ar : j < (ar[(BitVec.setWidth 64 qw + 2#64).toNat]'hqw2_ar).toNat := hj_csz
        rw [har'_qw.2 j hj_csz, ← har_qw.2 j hj_ar]; exact harj
      have hclr := flt_clr_lm_wp (Γ := Γ) (Q := Q) (X := X)
        (row_off := row_off) (nrow_off := nrow_off) (par_off := par_off) (cur_qn := cur_qn)
        (best_lit := best_lit) (new_qn := new_qn) (qi := qi)
        (J_out := J_out) (J_cond := J_cond) (J_step := J_step)
        (J_post := fun _ _ => False) (J_clr := fun _ _ => False)
        (r_cl := r_cl) (ticks := ticks) (csz := csz)
        (min_l := min_l) (min_d := min_d) (fc := fc) (k := k)
        hslen hw ha'.1 hlm0_l (fun l hl => flt1_and2_of_andFE (hlm0_b1 l hl))
        hqw_ref hqw_garb hcsz_eq har'_qw hlm'_clr hm''
        fun mp''' hm''' => hJstep nq_c tk_c ar' sb' mp''' ho' ha' hwa' hra' hm'''
      rw [h4, flt1_grpB4_cons, h2, flt1_grpB2_cons] at hclr
      exact hclr)
    (fun Jclr hJclr => ?_)
  by_cases hfc_eq : fc = 1#32
  · by_cases hml_ne : min_l ≠ 0xFFFFFFFF#32
    · have hmw := flt_match_loop_wp (Γ := Γ) (Q := Q) (X := X) (J_out := J_out)
        (J_cond := J_cond) (J_step := J_step) (J_post := fun _ _ => False) (J_clr := Jclr)
        (r_cl := r_cl) (ticks := ticks) (csz := csz) (min_d := min_d)
        hClines hMatch hslen hw hnodup hdw hl0 hdm0 hstep hro_n hcqn_n
        hnro_n hno_le hpo_fit hnew_lt hqi_lt hmat hout har_inv hlm0_l
        (fun l hl => flt1_and2_of_andFE (hlm0_b1 l hl))
        (fun r hr => hlm_b0 r (by omega)) hnb hqw_eq hcsz_eq hk_le hfc_eq hml_ne
        (hml' hml_ne) hlm' hb1' hw_ar hrefs_ar har_qw hmp'
        fun nq' tk' ar' sb' mp'' ho' ha' hwa' hra' hm'' =>
        hJclr (nq', tk', ar', sb') mp'' ⟨ho', ha', hwa', hra', hm''⟩
      rw [h4, flt1_grpB4_cons, h2, fltGrpK2.eq_1] at hmw
      exact hmw
    · obtain ⟨_, hpm⟩ := flt1_post_mark_eq_ite row_off nrow_off par_off cur_qn best_lit
        c.hdr c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi
        ticks J_cond qw J_step csz min_l min_d fc k (fun _ _ => False) Jclr
      rw [h4, flt1_grpB4_cons, h2, fltGrpK2.eq_1] at hpm
      rw [hpm]; c0_hfast_nogrp
      · exact absurd (by assumption) hml_ne
      · c0_hfast
        exact hJclr (new_qn, ticks + 1#64, ar, sb) mp' ⟨hout, har_inv, hw_ar, hrefs_ar, hmp'⟩
      · c0_hfast
        exact hJclr (new_qn, ticks + 1#64, ar, sb) mp' ⟨hout, har_inv, hw_ar, hrefs_ar, hmp'⟩
  · obtain ⟨_, hpm⟩ := flt1_post_mark_eq_ite row_off nrow_off par_off cur_qn best_lit
      c.hdr c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi
      ticks J_cond qw J_step csz min_l min_d fc k (fun _ _ => False) Jclr
    rw [h4, flt1_grpB4_cons, h2, fltGrpK2.eq_1] at hpm
    rw [hpm]; c0_hfast_nogrp
    · exact absurd (by assumption) hfc_eq
    · exact absurd (by assumption) hfc_eq
    · c0_hfast
      exact hJclr (new_qn, ticks + 1#64, ar, sb) mp' ⟨hout, har_inv, hw_ar, hrefs_ar, hmp'⟩

/-! ## 4. Main `full_bva_filter_row_wp` Theorem -/

theorem full_bva_filter_row_wp (Γ : Env)
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X →
      Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    (hMatch : ∀ a m Q X, fidBvaMatchLargeBvaSpec a m Q X →
      Γ "full_bva_match_large_bva_fid" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Func.wp Γ full_bva_filter_row_body a m Q X := by
  rintro ⟨h_arg, row_off, nrow_off, par_off, cur_qn, best_lit, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, step, bump, rfl, hslen, hw, hnodup, _, hl0, hdm0, _,
     hstep, _, hro_n, hcqn_n, hnro_n, hno_le, hpo_fit, hbl_lt, hmat, hlm0_b1, hlm_b0, hmem, hQ⟩
  have hdw : DenseWatchesInv F_cur s.core := by
    have := hw.watches; unfold ModeWatchesInv at this; rw [ite_eq_right hdm0] at this; exact this
  have hscr := c.hscr; have har_b := c.harena; have hmx := c.hmaxv; unfold dimacsBound at *
  have hcl := hslen.core_ok; have hsb_l := hslen.scratch_ok.scratch_buf_len
  have hmax_new_eq : (par_off - nrow_off).toNat = par_off.toNat - nrow_off.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hno_le)]
  have hmat_row_bd : row_off.toNat + cur_qn.toNat ≤ nrow_off.toNat := by
    have ⟨h_a, h_b, h_c, h_d, h_e, _⟩ := hmat.2.2.2.2.2 (step - 1) (by omega)
    rw [hro_n, hcqn_n, hnro_n]; omega
  have hrefs0 :
      fullArenaClauseRefsCore { s.core with arena := s.core.arena } =
        fullArenaClauseRefsCore s.core ∧
      ∀ r ∈ fullArenaClauseRefsCore s.core,
        fullArenaClauseGarbCore { s.core with arena := s.core.arena } r =
          fullArenaClauseGarbCore s.core r ∧
        fullArenaClauseSizeCore { s.core with arena := s.core.arena } r =
          fullArenaClauseSizeCore s.core r ∧
        fullArenaClauseLitsCore { s.core with arena := s.core.arena } r =
          fullArenaClauseLitsCore s.core r :=
    ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  unfold Func.wp full_bva_filter_row_body
  c0_hfast_nogrp
  fid_call hClines; intro r_cl
  c0_hfast_nogrp
  refine wp_while_state (α := BitVec 32 × BitVec 32 × BitVec 64 × List (BitVec 32) ×
      List (BitVec 32)) (fun x => (x.1, x.2.1, x.2.2.1, ()))
    (fun x => cur_qn.toNat - x.2.1.toNat)
    (fun (new_qn, qi, ticks, ar, sb) mp =>
      qi.toNat ≤ cur_qn.toNat ∧ new_qn.toNat ≤ par_off.toNat - nrow_off.toNat ∧
      FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
        cur_qn.toNat best_lit.toNat new_qn.toNat sb ∧
      FidFilterArInv c s nrow_off.toNat 0 new_qn.toNat sb ar ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar } ∧
      (fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
        ∀ r ∈ fullArenaClauseRefsCore s.core,
          fullArenaClauseGarbCore { s.core with arena := ar } r =
            fullArenaClauseGarbCore s.core r ∧
          fullArenaClauseSizeCore { s.core with arena := ar } r =
            fullArenaClauseSizeCore s.core r ∧
          fullArenaClauseLitsCore { s.core with arena := ar } r =
            fullArenaClauseLitsCore s.core r) ∧
      (FullMem c (fltMkSt s s.scratch.ant_sz ar s.core.lit_mark sb) ⋆ R) mp)
    (fun Jout hJout => by
      c0_hfast
      exact hJout (0#32, 0#32, 1#64 + r_cl, s.core.arena, s.scratch.scratch_buf) m
        ⟨Nat.zero_le _, Nat.zero_le _, fidFilterOutInv_init hsb_l,
         fidFilterArInv_init hslen (by omega), hw, hrefs0, hmem⟩)
    (fun Jout (new_qn, qi, ticks, ar, sb) mp
        ⟨hqi_le, hnew_le, hout, har_inv, hw_ar, hrefs_ar, hmp⟩ ihout => ?_)
  clear hmem
  dsimp only [fltMkSt] at hmp
  have hsb_cur_l := hout.1
  refine wp_join0 (FullMem c (fltMkSt s s.scratch.ant_sz ar s.core.lit_mark sb) ⋆ R)
    (fun _ m0 hm0 => ?_) (fun Jcond hJcond => ?_)
  · simpa only [fltHdrExpr, fltStep.eq_1, fltStep.eq_2, fltStep.eq_3, fltStep.eq_4,
      fltLd64.eq_1, fltCall64.eq_1, fltGrpB3.eq_1, fltGrpB0.eq_1, fltDummyVal, fltDummyTup,
      full_bva_filter_row_body, Blocks.get] using
      flt_cleanup_loop_wp (J_out := Jout) (J_cond := fun _ _ => False) (r_cl := r_cl)
        (qi := qi) (ticks := ticks) hslen hout har_inv hm0 fun ant' m' hm' => by
      let s' : FullState :=
        { s with scratch := { s.scratch with scratch_buf := sb, ant_sz := ant' } }
      have hs'len : s'.LengthsOk c :=
        ⟨hslen.core_ok, { hslen.scratch_ok with scratch_buf_len := hsb_cur_l }⟩
      exact hQ new_qn sb ant' m' hs'len hnew_le hout.2.2.1 hout.2.2.2 hm'
  · c0_hfast_nogrp
    rotate_left 1
    · c0_hfast; exact hJcond mp hmp
    · c0_hfast; exact hJcond mp hmp
    have hqi_lt : qi.toNat < cur_qn.toNat := by assumption
    have hnew_lt : new_qn.toNat < par_off.toNat - nrow_off.toNat := by
      have : new_qn.toNat < (par_off - nrow_off).toNat := by assumption
      rwa [hmax_new_eq] at this
    have hro_qi_sb : (BitVec.setWidth 64 (row_off + qi)).toNat < sb.length := by
      rw [fid_bv64_32, hsb_cur_l]; c0_bound
    have hro_qi_eq : (row_off + qi).toNat = row_off.toNat + qi.toNat := by c0_bound
    have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by c0_bound
    let qw := sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'hro_qi_sb
    have hqw_eq : qw = s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 := by
      dsimp only [qw]
      rw [← Option.some_inj, ← List.getElem?_eq_getElem hro_qi_sb, fid_bv64_32, hro_qi_eq]
      have hpres := hout.2.2.1 (row_off.toNat + qi.toNat) (by omega) (by omega) (by omega)
      rw [hpres, List.getElem?_eq_getElem (by rw [hsb_l]; omega), Option.getD_some]
    c0_hfast_nogrp
    refine wp_join_state (ts := [i32, i64])
      (α := BitVec 32 × BitVec 64 × List (BitVec 32) × List (BitVec 32))
      (fun x => (x.1, x.2.1, ()))
      (fun (nq', tk', ar', sb') mp' =>
        FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
          cur_qn.toNat best_lit.toNat nq'.toNat sb' ∧
        FidFilterArInv c s nrow_off.toNat 0 nq'.toNat sb' ar' ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
        (fullArenaClauseRefsCore { s.core with arena := ar' } = fullArenaClauseRefsCore s.core ∧
          ∀ r ∈ fullArenaClauseRefsCore s.core,
            fullArenaClauseGarbCore { s.core with arena := ar' } r =
              fullArenaClauseGarbCore s.core r ∧
            fullArenaClauseSizeCore { s.core with arena := ar' } r =
              fullArenaClauseSizeCore s.core r ∧
            fullArenaClauseLitsCore { s.core with arena := ar' } r =
              fullArenaClauseLitsCore s.core r) ∧
        (FullMem c (fltMkSt s s.scratch.ant_sz ar' s.core.lit_mark sb') ⋆ R) mp')
      (fun _ (nq', tk', ar', sb') mp' ⟨ho', ha', hwa', hra', hm'⟩ => by
        c0_hfast
        exact ihout (nq', qi + 1#32, tk', ar', sb') mp' (by dsimp only; rw [hqi1]; omega)
          ⟨by rw [hqi1]; omega, ho'.2.1, ho', ha', hwa', hra', hm'⟩)
      (fun Jstep hJstep => ?_)
    have hstep_wp : wp Γ Q X (fltStepExpr row_off nrow_off par_off cur_qn best_lit c.hdr
        c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl Jout new_qn qi ticks
        Jcond qw Jstep) mp := by
      rw [flt1_step_eq_ite]
      c0_hfast_nogrp
      · exact flt1_bin_branch_wp hClines hslen hdw hstep hro_n hcqn_n hnro_n hno_le hpo_fit
          hnew_lt hqi_lt hmat hout har_inv hw_ar hrefs_ar (by assumption) hqw_eq hmp
          fun nq' tk' ar' sb' mp' ho' ha' hwa' hra' hm' =>
          hJstep (nq', tk', ar', sb') mp' ⟨ho', ha', hwa', hra', hm'⟩
      · exact flt1_large_branch_wp hClines hMatch hslen hw hnodup hdw hl0 hdm0 hstep hro_n
          hcqn_n hnro_n hno_le hpo_fit hnew_lt hqi_lt hmat hout har_inv hlm0_b1 hlm_b0 hw_ar
          hrefs_ar (by assumption) hqw_eq hmp
          fun nq' tk' ar' sb' mp' ho' ha' hwa' hra' hm' =>
          hJstep (nq', tk', ar', sb') mp' ⟨ho', ha', hwa', hra', hm'⟩
    simpa only [fltStepExpr, fltOuterContExpr, fltHdrExpr, fltSteps.eq_1, fltSteps.eq_2,
      fltStep.eq_1, fltStep.eq_2, fltStep.eq_3, fltStep.eq_4,
      fltLd64.eq_1, fltLd32.eq_1, fltCall64.eq_1, fltThen.eq_1,
      fltGrpK0.eq_1, fltGrpK2.eq_1, fltGrpB3.eq_1, fltDummyVal, fltDummyTup,
      full_bva_filter_row_body] using hstep_wp

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
