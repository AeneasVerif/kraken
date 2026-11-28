module

public import LeanQbe.T.LeanLCNF.LcnfC0Strings
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof1
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof2
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof2
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof3
import LeanQbe.T.Logic.ControlComb
import Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Strings`, Part 2b: `lcnf_string_pos_op`

Proves `Func.wp rtR2bEnv` for the exported position/slice helper `lcnf_string_pos_op`,
factored into per-opcode (`0..5`) and slice-phase (`clamp`, `count`, `alloc_copy`) helpers.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

local macro "r2b_steps" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_steps))
local elab "r2b_to_group" : tactic => do
  let _ ← Lean.Elab.Tactic.tryTactic
    (Lean.Elab.Tactic.evalTactic (← `(tactic| change LeanQbe.T.wp _ _ _ _ _)))
  for _ in [:200] do
    let st0 ← Lean.Elab.Tactic.saveState
    let isGrp ← Lean.Elab.Tactic.tryTactic <| Lean.Elab.Tactic.evalTactic
      (← `(tactic| refine LeanQbe.T.wp_unroll_group fun _ _ => ?_))
    if isGrp then
      st0.restore
      break
    let gs0 ← Lean.Elab.Tactic.getGoals
    let ok ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step)))
    if !ok then
      st0.restore
      break
    let gs1 ← Lean.Elab.Tactic.getGoals
    if gs1.length > gs0.length then
      st0.restore
      break
local macro "r2b_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_); try c0_let_simp))

/-! ## 1. Reusable Bit-Tag, Capacity, and `strPosOpVal` Lemmas -/

private theorem strMaxCap_lt_pow64 : strMaxCap < 2 ^ 64 := by
  unfold strMaxCap; decide

private theorem strMaxCap_succ_lt_pow64 : strMaxCap + 1 < 2 ^ 64 := by
  unfold strMaxCap; decide

private theorem str_one_le_max : 1 ≤ strMaxCap := by
  unfold strMaxCap; decide

private theorem str_empty_valid : 0 < strMaxCap ∧ 0 < 1 ∧ 1 ≤ strMaxCap := by
  unfold strMaxCap; decide

private theorem rc1_nonneg : 0 ≤ (1#32 : BitVec 32).toInt := by decide

private theorem bv64_sext1_toNat : (BitVec.signExtend 64 1#32).toNat = 1 := rfl

private theorem bv64_ushiftRight_sext1 (v : BitVec 64) :
    (v >>> BitVec.signExtend 64 1#32) = v >>> 1 := by
  rw [BitVec.ushiftRight_eq', bv64_sext1_toNat]

private theorem bv64_ne_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hlt : a < b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
  omega

private theorem bv64_1_ne_0 : (1#64 : BitVec 64) ≠ 0#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem bv64_2_ne_0 : (2#64 : BitVec 64) ≠ 0#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem bv64_2_ne_1 : (2#64 : BitVec 64) ≠ 1#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem bv64_4_ne_0 : (4#64 : BitVec 64) ≠ 0#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem bv64_4_ne_1 : (4#64 : BitVec 64) ≠ 1#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem bv64_4_ne_2 : (4#64 : BitVec 64) ≠ 2#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem bv64_5_ne_0 : (5#64 : BitVec 64) ≠ 0#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem bv64_5_ne_1 : (5#64 : BitVec 64) ≠ 1#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem bv64_5_ne_2 : (5#64 : BitVec 64) ≠ 2#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem bv64_5_ne_4 : (5#64 : BitVec 64) ≠ 4#64 :=
  (bv64_ne_of_lt (by omega) (by omega) (by omega)).symm

private theorem strPosOpVal_op0 (bs : List UInt8) (idxV endV : BitVec 64) :
    strPosOpVal 0#64 bs idxV endV =
      if (idxV &&& 1#64) = 0#64 then 0#64
      else if (idxV >>> 1).toNat < bs.length then utf8DecodeCpAt bs (idxV >>> 1).toNat
      else 0#64 := by
  simp [strPosOpVal]

private theorem strPosOpVal_op1 (bs : List UInt8) (idxV endV : BitVec 64) :
    strPosOpVal 1#64 bs idxV endV =
      if (idxV &&& 1#64) = 0#64 then idxV
      else if (idxV >>> 1).toNat < bs.length then
        ((BitVec.ofNat 64 ((idxV >>> 1).toNat + utf8DecodeStepAt bs (idxV >>> 1).toNat)) <<< 1) |||
          1#64
      else idxV := by
  simp [strPosOpVal]

private theorem strPosOpVal_op2 (bs : List UInt8) (idxV endV : BitVec 64) :
    strPosOpVal 2#64 bs idxV endV =
      if (idxV &&& 1#64) = 0#64 then 1#64
      else if (idxV >>> 1).toNat < bs.length then 0#64 else 1#64 := by
  simp [strPosOpVal, bv64_2_ne_0, bv64_2_ne_1]

private theorem strPosOpVal_op4 (bs : List UInt8) (idxV endV : BitVec 64) :
    strPosOpVal 4#64 bs idxV endV =
      if (idxV &&& 1#64) = 0#64 then 0#64
      else if h : (idxV >>> 1).toNat < bs.length then
        BitVec.setWidth 64 bs[(idxV >>> 1).toNat].toBitVec
      else 0#64 := by
  simp [strPosOpVal, bv64_4_ne_0, bv64_4_ne_1, bv64_4_ne_2]

private theorem strPosOpVal_op5 (bs : List UInt8) (idxV endV : BitVec 64) :
    strPosOpVal 5#64 bs idxV endV =
      if (idxV &&& 1#64) = 0#64 then 0#64
      else if bs.length < (idxV >>> 1).toNat then 0#64
      else if h : (idxV >>> 1).toNat < bs.length then
        if (bs[(idxV >>> 1).toNat].toNat &&& 0xc0) ≠ 0x80 then 1#64 else 0#64
      else 1#64 := by
  simp [strPosOpVal, bv64_5_ne_0, bv64_5_ne_1, bv64_5_ne_2, bv64_5_ne_4]

/-! ## 2. Named Sub-AST Projections for `lcnf_string_pos_op_body` -/

private def posOp0Expr (s szV idxV : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.and i64,
              args := (Arg.var idxV, Arg.imm 1, ()) } fun p_4 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
              args := (Arg.var p_4.fst, Arg.imm 0, ()) } fun p_5 =>
  Expr.jnz (Arg.var p_5.fst) (Expr.ret (Arg.imm 0, ()))
    (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_6 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                args := (Arg.var idxV, Arg.var p_6.fst, ()) } fun p_7 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64 Ty.bool,
                args := (Arg.var p_7.fst, Arg.var szV, ()) } fun p_8 =>
    Expr.jnz (Arg.var p_8.fst) (Expr.ret (Arg.imm 0, ()))
      (Expr.let_
        { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var s, Arg.imm 32, ()) }
        fun p =>
      Expr.call (as := [i64, i64, i64]) (bs := [i64]) "r2b_utf8_decode_cp"
        (Arg.var p.fst, Arg.var szV, Arg.var p_7.fst, ()) fun p =>
      Expr.ret (Arg.var p.fst, ())))

private def posOp1Expr (s szV idxV : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.and i64,
              args := (Arg.var idxV, Arg.imm 1, ()) } fun p_5 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
              args := (Arg.var p_5.fst, Arg.imm 0, ()) } fun p_6 =>
  Expr.jnz (Arg.var p_6.fst)
    (Expr.call (as := [i64]) (bs := []) "r2_inc_obj" (Arg.var idxV, ()) fun _ =>
    Expr.ret (Arg.var idxV, ()))
    (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_7 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                args := (Arg.var idxV, Arg.var p_7.fst, ()) } fun p_8 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64 Ty.bool,
                args := (Arg.var p_8.fst, Arg.var szV, ()) } fun p_9 =>
    Expr.jnz (Arg.var p_9.fst) (Expr.ret (Arg.var idxV, ()))
      (Expr.let_
        { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var s, Arg.imm 32, ()) }
        fun p =>
      Expr.call (as := [i64, i64, i64]) (bs := [i64]) "r2b_utf8_decode_step"
        (Arg.var p.fst, Arg.var szV, Arg.var p_8.fst, ()) fun p =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p_8.fst, Arg.var p.fst, ()) } fun p =>
      Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_10 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.shl i64,
                  args := (Arg.var p.fst, Arg.var p_10.fst, ()) } fun p =>
      Expr.let_ { sig := [i64, i64], code := OpCode.or i64,
                  args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
      Expr.ret (Arg.var p.fst, ())))

private def posOp2Expr (szV idxV : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.and i64,
              args := (Arg.var idxV, Arg.imm 1, ()) } fun p_6 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
              args := (Arg.var p_6.fst, Arg.imm 0, ()) } fun p_7 =>
  Expr.jnz (Arg.var p_7.fst) (Expr.ret (Arg.imm 1, ()))
    (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_8 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                args := (Arg.var idxV, Arg.var p_8.fst, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64 Ty.bool,
                args := (Arg.var p.fst, Arg.var szV, ()) } fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 1, ())) (Expr.ret (Arg.imm 0, ())))

private def posOp3ClampExpr (v szV : Val i64)
    (k : Val i64 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]])
    (fun _Js => Blocks.cons (fun p => k p.fst) Blocks.nil)
    fun Js =>
    Expr.let_ { sig := [i64, i64], code := OpCode.and i64,
                args := (Arg.var v, Arg.imm 1, ()) } fun p_8 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool,
                args := (Arg.var p_8.fst, Arg.imm 0, ()) } fun p_9 =>
    Expr.jnz (Arg.var p_9.fst)
      (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_10 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                  args := (Arg.var v, Arg.var p_10.fst, ()) } fun p =>
      Expr.group (sig := [[i64]])
        (fun _Js_1 => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
        fun Js_1 =>
        Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                    args := (Arg.var p.fst, Arg.var szV, ()) } fun p_11 =>
        Expr.jnz (Arg.var p_11.fst) (Expr.jump Js_1.fst (Arg.var szV, ()))
          (Expr.jump Js_1.fst (Arg.var p.fst, ())))
      (Expr.jump Js.fst (Arg.var szV, ()))

private def posOp3CountLoopExpr (s bV eV : Val i64)
    (k : Tup Val [i64, i64] → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64]])
    (fun Js =>
      Blocks.cons
        (fun p_11 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool,
                      args := (Arg.var p_11.snd.fst, Arg.var eV, ()) } fun p_12 =>
          Expr.jnz (Arg.var p_12.fst)
            (Expr.let_
              { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var s, Arg.imm 32, ()) }
              fun p =>
            Expr.call (as := [i64, i64, i64]) (bs := [i64]) "r2b_utf8_decode_step"
              (Arg.var p.fst, Arg.var eV, Arg.var p_11.snd.fst, ()) fun p =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var p_11.snd.fst, Arg.var p.fst, ()) } fun p =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var p_11.fst, Arg.imm 1, ()) } fun p_13 =>
            Expr.jump Js.fst (Arg.var p_13.fst, Arg.var p.fst, ()))
            (k p_11))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.var bV, ())

private def posOp3SliceExpr (rt s bV eV : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64 Ty.bool,
              args := (Arg.var bV, Arg.var eV, ()) } fun p_9 =>
  Expr.jnz (Arg.var p_9.fst)
    (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "r2b_str_alloc_cap"
      (Arg.var rt, Arg.imm 1, Arg.imm 0, Arg.imm 0, ()) fun p =>
    Expr.ret (Arg.var p.fst, ()))
    (Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var eV, Arg.var bV, ()) }
      fun p_10 =>
    posOp3CountLoopExpr s bV eV fun p_11 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p_10.fst, Arg.imm 1, ()) } fun p_13 =>
      Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "r2b_str_alloc_cap"
        (Arg.var rt, Arg.var p_13.fst, Arg.var p_10.fst, Arg.var p_11.fst, ()) fun p_14 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p_14.fst, Arg.imm 32, ()) } fun p_15 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var s, Arg.imm 32, ()) } fun p =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p.fst, Arg.var bV, ()) } fun p =>
      Expr.call (as := [i64, i64, i64]) (bs := []) "r2_mem_copy_bytes"
        (Arg.var p_15.fst, Arg.var p.fst, Arg.var p_10.fst, ()) fun _ =>
      Expr.ret (Arg.var p_14.fst, ()))

private def posOp3Expr (rt s szV idxV endV : Val i64) : Expr Val Cont [i64] :=
  posOp3ClampExpr idxV szV fun bV =>
    posOp3ClampExpr endV szV fun eV =>
      posOp3SliceExpr rt s bV eV

private def posOp4Expr (s szV idxV : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.and i64,
              args := (Arg.var idxV, Arg.imm 1, ()) } fun p_8 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
              args := (Arg.var p_8.fst, Arg.imm 0, ()) } fun p_9 =>
  Expr.jnz (Arg.var p_9.fst) (Expr.ret (Arg.imm 0, ()))
    (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_10 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                args := (Arg.var idxV, Arg.var p_10.fst, ()) } fun p_11 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64 Ty.bool,
                args := (Arg.var p_11.fst, Arg.var szV, ()) } fun p_12 =>
    Expr.jnz (Arg.var p_12.fst) (Expr.ret (Arg.imm 0, ()))
      (Expr.let_
        { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var s, Arg.imm 32, ()) }
        fun p =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p.fst, Arg.var p_11.fst, ()) } fun p =>
      Expr.load i8 (Arg.var p.fst) fun ld =>
      Expr.let_ { sig := [i8], code := OpCode.zext 8 64, args := (Arg.var ld, ()) } fun p =>
      Expr.ret (Arg.var p.fst, ())))

private def posOp5Expr (s szV idxV : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.and i64,
              args := (Arg.var idxV, Arg.imm 1, ()) } fun p_9 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
              args := (Arg.var p_9.fst, Arg.imm 0, ()) } fun p_10 =>
  Expr.jnz (Arg.var p_10.fst) (Expr.ret (Arg.imm 0, ()))
    (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_11 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                args := (Arg.var idxV, Arg.var p_11.fst, ()) } fun p_12 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                args := (Arg.var p_12.fst, Arg.var szV, ()) } fun p_13 =>
    Expr.jnz (Arg.var p_13.fst) (Expr.ret (Arg.imm 0, ()))
      (Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
          args := (Arg.var p_12.fst, Arg.var szV, ()) }
        fun p_14 =>
      Expr.jnz (Arg.var p_14.fst) (Expr.ret (Arg.imm 1, ()))
        (Expr.let_
          { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var s, Arg.imm 32, ()) }
          fun p =>
        Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var p.fst, Arg.var p_12.fst, ()) } fun p =>
        Expr.load i8 (Arg.var p.fst) fun ld =>
        Expr.let_ { sig := [i8], code := OpCode.zext 8 64, args := (Arg.var ld, ()) } fun p =>
        Expr.let_ { sig := [i64, i64], code := OpCode.and i64,
                    args := (Arg.var p.fst, Arg.imm 192, ()) } fun p =>
        Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool,
                    args := (Arg.var p.fst, Arg.imm 128, ()) } fun p =>
        Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 1, ())) (Expr.ret (Arg.imm 0, ())))))

/-! ## 3. Per-Opcode and Slice-Phase WP Helpers -/

private theorem lcnf_string_pos_op0_wp
    {rt : BitVec 64} {sObj : LcnfObj} {objs : List LcnfObj}
    {idxV endV : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcanon : StrCanon sObj)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m)
    (hPost : ∀ m', (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' →
      Q (strPosOpVal 0#64 (strPayload sObj) idxV endV, ()) m') :
    wp rtR2bEnv Q X (posOp0Expr sObj.addr (BitVec.ofNat 64 (strPayload sObj).length) idxV) m := by
  let bs := strPayload sObj
  have hszLt := str_payload_lt_max sObj hcanon
  have hsz64 : bs.length < 2 ^ 64 := Nat.lt_trans hszLt strMaxCap_lt_pow64
  have hszTo : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz64]
  have hmS : (lcnfObjMem sObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
  dsimp only [posOp0Expr]
  r2b_to_group
  c0_step
  · have ha0 : (idxV &&& 1#64) = 0#64 := hc
    r2b_steps
    have hsp := hPost m (sep_cast hm (by ac_rfl))
    rwa [strPosOpVal_op0, ite_eq_left ha0] at hsp
  · have ha1 : (idxV &&& 1#64) ≠ 0#64 := hc
    r2b_to_group
    c0_step
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      r2b_steps
      have hsp := hPost m (sep_cast hm (by ac_rfl))
      rwa [strPosOpVal_op0, ite_eq_right ha1, ite_eq_right (Nat.not_lt_of_le hc)] at hsp
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      have hlt : (idxV >>> 1).toNat < bs.length := Nat.lt_of_not_le hc
      r2b_call rtR2bEnv_r2b_utf8_decode_cp
      dsimp only [r2bUtf8DecodeCpSpec, vals, Tup.map, Arg.val]
      refine ⟨bs, Rest, hszTo.symm, hmExp, ?_⟩
      have hsp := hPost m (sep_cast hm (by ac_rfl))
      rwa [strPosOpVal_op0, ite_eq_right ha1, ite_eq_left hlt] at hsp

private theorem lcnf_string_pos_op1_wp
    {rt : BitVec 64} {sObj : LcnfObj} {objs : List LcnfObj}
    {idxV endV : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcanon : StrCanon sObj)
    (hobj1 : (idxV &&& 1#64) = 0#64 ∧ idxV ≠ 0#64 →
      ∃ iObj ∈ objs, iObj.addr = idxV ∧ iObj.Wf)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m)
    (hPost : ∀ m',
      (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap (incObjList idxV objs) ⋆ R) m' →
      Q (strPosOpVal 1#64 (strPayload sObj) idxV endV, ()) m') :
    wp rtR2bEnv Q X (posOp1Expr sObj.addr (BitVec.ofNat 64 (strPayload sObj).length) idxV) m := by
  let bs := strPayload sObj
  have hszLt := str_payload_lt_max sObj hcanon
  have hsz64 : bs.length < 2 ^ 64 := Nat.lt_trans hszLt strMaxCap_lt_pow64
  have hszTo : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz64]
  have hmS : (lcnfObjMem sObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m := sep_cast hm (by ac_rfl)
  dsimp only [posOp1Expr]
  r2b_to_group
  c0_step
  · have ha0 : (idxV &&& 1#64) = 0#64 := hc
    by_cases h0 : idxV = 0#64
    · r2b_call rtR2bEnv_r2_inc_obj
      dsimp only [r2IncObjSpec, vals, Tup.map, Arg.val]
      rw [ite_eq_left (Or.inl h0)]
      r2b_steps
      have hinc0 : incObjList idxV objs = objs := by
        unfold incObjList; rw [ite_eq_left (Or.inl h0)]
      rw [hinc0] at hPost
      have hsp := hPost m (sep_cast hm (by ac_rfl))
      rwa [strPosOpVal_op1, ite_eq_left ha0] at hsp
    · obtain ⟨iObj, hiMem, hiAddr, hiWf⟩ := hobj1 ⟨ha0, h0⟩
      obtain ⟨k, hkLen, hobjk⟩ := List.getElem_of_mem hiMem
      have hnd : (objs.map LcnfObj.addr).Nodup :=
        lcnfHeap_nodup_addrs (sep_cast hm (by ac_rfl) :
          (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ R)) m)
      have hfocus : lcnfHeap objs = lcnfObjMem iObj ⋆ lcnfHeap (objs.eraseIdx k) := by
        rw [lcnfHeap_focus objs hkLen, hobjk, ← lcnfHeap_eraseIdx objs]
      have hmI : (lcnfObjMem iObj ⋆ (lcnfHeap (objs.eraseIdx k) ⋆
          rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ R)) m := by
        rw [hfocus] at hm; exact sep_cast hm (by ac_rfl)
      r2b_call rtR2bEnv_r2_inc_obj
      dsimp only [r2IncObjSpec, vals, Tup.map, Arg.val]
      rw [ite_eq_right (by simp [h0, ha0])]
      refine ⟨iObj, _, hiAddr, hiWf, hmI, fun m1 hm1 => ?_⟩
      r2b_steps
      have hmInc : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆
          lcnfHeap (incObjList idxV objs) ⋆ R) m1 := by
        have hset : objs.set k (iObj.withRc (incRcVal iObj.rc)) =
            objs.map (fun o => if o.addr = idxV then o.withRc (incRcVal o.rc) else o) := by
          rw [list_set_eq_map_of_nodup hkLen (iObj.withRc (incRcVal iObj.rc)) hnd]
          refine List.map_congr_left fun o ho => ?_
          rw [hobjk, hiAddr]
          split
          · next heq =>
            obtain ⟨ko, hko, hkoEq⟩ := List.getElem_of_mem ho
            have hkEq : ko = k :=
              nodup_map_getElem_eq LcnfObj.addr hnd hko hkLen
                (by rw [hkoEq, hobjk, heq, hiAddr])
            subst hkEq; rw [← hobjk, hkoEq]
          · rfl
        have hinc : incObjList idxV objs = objs.set k (iObj.withRc (incRcVal iObj.rc)) := by
          unfold incObjList; rw [ite_eq_right (by simp [h0, ha0]), ← hset]
        have hfc : lcnfHeap (objs.set k (iObj.withRc (incRcVal iObj.rc))) =
            lcnfObjMem (iObj.withRc (incRcVal iObj.rc)) ⋆ lcnfHeap (objs.eraseIdx k) := by
          rw [lcnfHeap_focus (objs.set k _) (by rw [List.length_set]; exact hkLen),
            List.getElem_set_self, ← lcnfHeap_eraseIdx (objs.set k _), eraseIdx_set_eq_self]
        rw [hinc, hfc]
        exact sep_cast hm1 (by ac_rfl)
      have hsp := hPost m1 hmInc
      rwa [strPosOpVal_op1, ite_eq_left ha0] at hsp
  · have ha1 : (idxV &&& 1#64) ≠ 0#64 := hc
    have hincId : incObjList idxV objs = objs := by
      unfold incObjList; rw [ite_eq_left (Or.inr ha1)]
    rw [hincId] at hPost
    r2b_to_group
    c0_step
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      r2b_steps
      have hsp := hPost m (sep_cast hm (by ac_rfl))
      rwa [strPosOpVal_op1, ite_eq_right ha1, ite_eq_right (Nat.not_lt_of_le hc)] at hsp
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      have hlt : (idxV >>> 1).toNat < bs.length := Nat.lt_of_not_le hc
      obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
      r2b_call rtR2bEnv_r2b_utf8_decode_step
      dsimp only [r2bUtf8DecodeStepSpec, vals, Tup.map, Arg.val]
      refine ⟨bs, Rest, hszTo.symm, hmExp, ?_⟩
      r2b_steps
      have hst := (utf8DecodeStepAt_pos hlt).2
      have hstLt : utf8DecodeStepAt bs (idxV >>> 1).toNat < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hst) hsz64
      have hsumLt : (idxV >>> 1).toNat + utf8DecodeStepAt bs (idxV >>> 1).toNat < 2 ^ 64 :=
        Nat.lt_of_le_of_lt hst hsz64
      have hbox :
          ((((idxV >>> 1) + BitVec.ofNat 64 (utf8DecodeStepAt bs (idxV >>> 1).toNat)) <<<
              BitVec.signExtend 64 1#32) ||| 1#64) =
            ((BitVec.ofNat 64 ((idxV >>> 1).toNat +
              utf8DecodeStepAt bs (idxV >>> 1).toNat)) <<< 1) ||| 1#64 := by
        rw [BitVec.shiftLeft_eq', bv64_sext1_toNat]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_add,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hstLt, Nat.mod_eq_of_lt hsumLt]
      have hsp := hPost m (sep_cast hm (by ac_rfl))
      rw [strPosOpVal_op1, ite_eq_right ha1, ite_eq_left hlt] at hsp
      rw [show (BitVec.signExtend 64 1#32) = 1#64 from rfl,
        show (1 : BitVec 64) = 1#64 from rfl] at *
      rwa [← hbox] at hsp

private theorem lcnf_string_pos_op2_wp
    {rt : BitVec 64} {sObj : LcnfObj} {objs : List LcnfObj}
    {idxV endV : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcanon : StrCanon sObj)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m)
    (hPost : ∀ m', (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' →
      Q (strPosOpVal 2#64 (strPayload sObj) idxV endV, ()) m') :
    wp rtR2bEnv Q X (posOp2Expr (BitVec.ofNat 64 (strPayload sObj).length) idxV) m := by
  let bs := strPayload sObj
  have hszLt := str_payload_lt_max sObj hcanon
  have hsz64 : bs.length < 2 ^ 64 := Nat.lt_trans hszLt strMaxCap_lt_pow64
  dsimp only [posOp2Expr]
  r2b_to_group
  c0_step
  · have ha0 : (idxV &&& 1#64) = 0#64 := hc
    r2b_steps
    have hsp := hPost m (sep_cast hm (by ac_rfl))
    rwa [strPosOpVal_op2, ite_eq_left ha0] at hsp
  · have ha1 : (idxV &&& 1#64) ≠ 0#64 := hc
    r2b_to_group
    c0_step
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      r2b_steps
      have hsp := hPost m (sep_cast hm (by ac_rfl))
      rwa [strPosOpVal_op2, ite_eq_right ha1, ite_eq_right (Nat.not_lt_of_le hc)] at hsp
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      have hlt : (idxV >>> 1).toNat < bs.length := Nat.lt_of_not_le hc
      r2b_steps
      have hsp := hPost m (sep_cast hm (by ac_rfl))
      rwa [strPosOpVal_op2, ite_eq_right ha1, ite_eq_left hlt] at hsp

private theorem posOp3_clamp_wp
    {v : BitVec 64} {sz : Nat} (hsz64 : sz < 2 ^ 64) {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {k : Val i64 → Expr Val Cont [i64]}
    (hk : wp rtR2bEnv Q X (k (BitVec.ofNat 64 (strPosClamp v sz))) m) :
    wp rtR2bEnv Q X (posOp3ClampExpr v (BitVec.ofNat 64 sz) k) m := by
  let c := strPosClamp v sz
  have hcLe : c ≤ sz := by
    dsimp only [c, strPosClamp]
    split <;> first | exact Nat.min_le_right _ _ | exact Nat.le_refl _
  have hc64 : c < 2 ^ 64 := Nat.lt_of_le_of_lt hcLe hsz64
  dsimp only [posOp3ClampExpr]
  refine wp_join_group
    (P := fun (xs : Tup Val [i64]) m1 => match xs with
      | (bv, PUnit.unit) => m1 = m ∧ bv = BitVec.ofNat 64 c) ?_ ?_
  · intro _ ⟨bv, ⟨⟩⟩ m1 ⟨hm1Eq, hbv⟩
    subst hbv; cases hm1Eq
    exact hk
  · intro J_out hJ_out
    r2b_to_group
    c0_step
    · have ha1 : (v &&& 1#64) ≠ 0#64 := hc
      r2b_to_group
      c0_step
      r2b_to_group
      c0_step
      · r2b_steps
        try rw [bv64_ushiftRight_sext1] at hc
        rw [Nat.mod_eq_of_lt hsz64] at hc
        have hcEq : BitVec.ofNat 64 sz = BitVec.ofNat 64 c := by
          dsimp only [c, strPosClamp]
          rw [ite_eq_left ha1, Nat.min_eq_right (Nat.le_of_lt hc)]
        apply hJ; simp only [Blocks.get]; c0_steps
        rw [hcEq]
        exact hJ_out (BitVec.ofNat 64 c, ()) m ⟨rfl, rfl⟩
      · r2b_steps
        try rw [bv64_ushiftRight_sext1] at hc
        rw [Nat.mod_eq_of_lt hsz64] at hc
        have hle : (v >>> 1).toNat ≤ sz := Nat.not_lt.mp hc
        have hcEq : (v >>> 1) = BitVec.ofNat 64 c := by
          dsimp only [c, strPosClamp]
          rw [ite_eq_left ha1, Nat.min_eq_left hle]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hsz64)]
        apply hJ; simp only [Blocks.get]; c0_steps
        try rw [bv64_ushiftRight_sext1]
        rw [hcEq]
        exact hJ_out (BitVec.ofNat 64 c, ()) m ⟨rfl, rfl⟩
    · r2b_steps
      have hnot : (v &&& 1#64) = 0#64 := by
        first | exact hc | exact Classical.not_not.mp hc
      have hcEq : BitVec.ofNat 64 sz = BitVec.ofNat 64 c := by
        dsimp only [c, strPosClamp]; rw [ite_eq_right (by simp [hnot])]
      rw [hcEq]
      exact hJ_out (BitVec.ofNat 64 c, ()) m ⟨rfl, rfl⟩

private theorem posOp3_count_loop_wp
    {sObj : LcnfObj} {b e : Nat} {Rest : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {k : Tup Val [i64, i64] → Expr Val Cont [i64]}
    (hcanon : StrCanon sObj) (hbe : b < e) (heLe : e ≤ (strPayload sObj).length)
    (hmSubE : (bytes (sObj.addr + 32#64) ((strPayload sObj).take e) ⋆ Rest) m)
    (hk : utf8CountFrom ((strPayload sObj).take e) b < 2 ^ 64 → wp rtR2bEnv Q X
      (k (BitVec.ofNat 64 (utf8CountFrom ((strPayload sObj).take e) b), BitVec.ofNat 64 e, ()))
      m) :
    wp rtR2bEnv Q X
      (posOp3CountLoopExpr sObj.addr (BitVec.ofNat 64 b) (BitVec.ofNat 64 e) k) m := by
  let bs := strPayload sObj
  have hszLt := str_payload_lt_max sObj hcanon
  have hsz64 : bs.length < 2 ^ 64 := Nat.lt_trans hszLt strMaxCap_lt_pow64
  have he64 : e < 2 ^ 64 := Nat.lt_of_le_of_lt heLe hsz64
  have heTo : (BitVec.ofNat 64 e).toNat = e := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
  have htakeLen : (bs.take e).length = e := by rw [List.length_take, Nat.min_eq_left heLe]
  dsimp only [posOp3CountLoopExpr]
  refine wp_loop_inv
    (fun (xs : Tup Val [i64, i64]) mL =>
      mL = m ∧ ∃ posN : Nat, b ≤ posN ∧ posN ≤ e ∧
        xs.2.1 = BitVec.ofNat 64 posN ∧
        xs.1.toNat + utf8CountFrom (bs.take e) posN = utf8CountFrom (bs.take e) b ∧
        xs.1.toNat + (e - posN) ≤ e)
    (fun (xs : Tup Val [i64, i64]) _ => e - xs.2.1.toNat) ?_ ?_
  · intro Jlp hJlp
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    exact hJlp (0#64, BitVec.ofNat 64 b, ()) m
      ⟨rfl, b, Nat.le_refl _, Nat.le_of_lt hbe, rfl,
        by simp only [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.zero_add],
        by simp only [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.zero_add]
           exact Nat.sub_le _ _⟩
  · intro Jlp ⟨nlen, pos, ⟨⟩⟩ mL ⟨hmL, posN, hbp, hpe, hposEq, hcntEq, hbnd⟩ hRec
    cases hmL
    dsimp only at hposEq hcntEq hbnd
    subst hposEq
    have hpos64 : posN < 2 ^ 64 := Nat.lt_of_le_of_lt hpe he64
    have hposTo : (BitVec.ofNat 64 posN).toNat = posN := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos64]
    r2b_to_group
    c0_step
    · rw [Nat.mod_eq_of_lt hpos64, Nat.mod_eq_of_lt he64] at hc
      have hltTake : posN < (bs.take e).length := by rw [htakeLen]; exact hc
      have hstepPos := utf8DecodeStepAt_pos hltTake
      rw [htakeLen] at hstepPos
      have hnlenLt : nlen.toNat + 1 < 2 ^ 64 := by
        have : nlen.toNat + 1 ≤ e + 1 := by omega
        exact Nat.lt_of_le_of_lt this
          (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt heLe hszLt))
            strMaxCap_lt_pow64)
      have hnlen1 : (nlen + 1#64).toNat = nlen.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hnlenLt]
      r2b_call rtR2bEnv_r2b_utf8_decode_step
      dsimp only [r2bUtf8DecodeStepSpec, vals, Tup.map, Arg.val]
      refine ⟨bs.take e, Rest, by rw [htakeLen, heTo], hmSubE, ?_⟩
      r2b_steps
      have hposNext : posN + utf8DecodeStepAt (bs.take e) posN ≤ e := hstepPos.2
      have hposAdd : BitVec.ofNat 64 posN +
          BitVec.ofNat 64 (utf8DecodeStepAt (bs.take e) posN) =
          BitVec.ofNat 64 (posN + utf8DecodeStepAt (bs.take e) posN) :=
        (BitVec.ofNat_add _ _).symm
      have hposNextTo :
          (BitVec.ofNat 64 (posN + utf8DecodeStepAt (bs.take e) posN)).toNat =
            posN + utf8DecodeStepAt (bs.take e) posN := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hposNext he64)]
      have hstepCnt := utf8CountFrom_step hltTake
      apply hRec
      · dsimp only; rw [hposTo, hposAdd, hposNextTo]
        have := hstepPos.1; omega
      · refine ⟨rfl, posN + utf8DecodeStepAt (bs.take e) posN,
          Nat.le_trans hbp (Nat.le_add_right _ _), hposNext,
          by rw [hposTo]; exact hposAdd, ?_, ?_⟩
        · dsimp only; rw [hstepCnt] at hcntEq
          rw [show (1 : BitVec 64) = 1#64 from rfl, hnlen1]; omega
        · dsimp only; rw [show (1 : BitVec 64) = 1#64 from rfl, hnlen1]
          have := hstepPos.1; omega
    · rw [Nat.mod_eq_of_lt hpos64, Nat.mod_eq_of_lt he64] at hc
      have hposE : posN = e := Nat.le_antisymm hpe (Nat.not_lt.mp hc)
      rw [hposE] at hcntEq
      have hcnt0 : utf8CountFrom (bs.take e) e = 0 := by
        apply utf8CountFrom_end; rw [htakeLen]; exact Nat.lt_irrefl _
      rw [hcnt0, Nat.add_zero] at hcntEq
      have hcntLt : utf8CountFrom (bs.take e) b < 2 ^ 64 := hcntEq ▸ nlen.isLt
      have hnlenBv : nlen = BitVec.ofNat 64 (utf8CountFrom (bs.take e) b) := by
        apply BitVec.eq_of_toNat_eq
        rw [← hcntEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt nlen.isLt]
      subst hnlenBv
      rw [hposE]
      exact hk hcntLt

private theorem posOp3_empty_wp
    {rt : BitVec 64} {sObj : LcnfObj} {objs : List LcnfObj}
    {st : RtC0State} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hav : st.hasFree (strAllocBytes 1) ∨ strAllocBytes 1 ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m)
    (hpostK : ∀ r st' m',
      r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      StrCanon (mkStrObj r 1#32 1 [] 0) →
      (rtC0Inv rt st' ⋆ lcnfObjMem (mkStrObj r 1#32 1 [] 0) ⋆
        lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' →
      Q (r, ()) m') :
    wp rtR2bEnv Q X
      (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "r2b_str_alloc_cap"
        (Arg.var rt, Arg.imm 1, Arg.imm 0, Arg.imm 0, ()) fun p =>
      Expr.ret (Arg.var p.fst, ())) m := by
  r2b_call rtR2bEnv_r2b_str_alloc_cap
  dsimp only [r2bStrAllocCapSpec, vals, Tup.map, Arg.val]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, show (1 : BitVec 64).toNat = 1 from rfl,
    ite_eq_left str_empty_valid]
  refine ⟨st, lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R, hav, sep_cast hm (by ac_rfl),
    fun r st1 m1 hr0 hr8 hpr1 hrem1 _ hm1 => ?_⟩
  r2b_steps
  let rObj := mkStrObj r 1#32 1 [] 0
  have hcanR : StrCanon rObj :=
    mkStrObj_canon hr0 hr8 rc1_nonneg (Nat.le_refl _) str_one_le_max (Nat.two_pow_pos 64)
  have hmR : (rtC0Inv rt st1 ⋆ lcnfObjMem rObj ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m1 := by
    have hparts : (cell64 r strHeaderWord ⋆
        cell64 (r + 8#64) (BitVec.ofNat 64 (([] : List UInt8).length + 1)) ⋆
        cell64 (r + 16#64) (BitVec.ofNat 64 1) ⋆
        cell64 (r + 24#64) (BitVec.ofNat 64 0) ⋆
        bytes (r + 32#64) [] ⋆
        bytes (r + 32#64 + BitVec.ofNat 64 ([] : List UInt8).length) [(0 : UInt8)] ⋆
        region (r + 32#64 + BitVec.ofNat 64 ([] : List UInt8).length + 1#64)
          (strAllocBytes 1 - (32 + ([] : List UInt8).length + 1)) ⋆
        (rtC0Inv rt st1 ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R)) m1 := by
      simp only [List.length_nil, Nat.zero_add,
        show (0 : BitVec 64) = 0#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
        show r + 32#64 + 0#64 = r + 32#64 from by simp,
        bytes_nil_eq, region_zero] at hm1 ⊢
      exact sep_cast hm1 (by ac_rfl)
    exact sep_cast (mkStrObj_mem_of_parts str_one_le_max (Nat.le_refl _) hparts) (by ac_rfl)
  exact hpostK r st1 m1 hr0 hr8 hpr1 hrem1 hcanR hmR

private theorem posOp3_alloc_copy_wp
    {rt : BitVec 64} {sObj : LcnfObj} {objs : List LcnfObj}
    {b e : Nat} {st : RtC0State} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcanon : StrCanon sObj) (hbe : b < e) (heLe : e ≤ (strPayload sObj).length)
    (hcntLt : utf8CountFrom ((strPayload sObj).take e) b < 2 ^ 64)
    (hav : st.hasFree (strAllocBytes ((((strPayload sObj).take e).drop b).length + 1)) ∨
      strAllocBytes ((((strPayload sObj).take e).drop b).length + 1) ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m)
    (hpostK : ∀ r st' m',
      r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      StrCanon (mkStrObj r 1#32 (((strPayload sObj).take e).drop b).length.succ
        (((strPayload sObj).take e).drop b) (utf8CountFrom ((strPayload sObj).take e) b)) →
      (rtC0Inv rt st' ⋆
        lcnfObjMem (mkStrObj r 1#32 (((strPayload sObj).take e).drop b).length.succ
          (((strPayload sObj).take e).drop b) (utf8CountFrom ((strPayload sObj).take e) b)) ⋆
        lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' →
      Q (r, ()) m') :
    let bs := strPayload sObj
    let newSz := e - b
    let nlen := BitVec.ofNat 64 (utf8CountFrom (bs.take e) b)
    wp rtR2bEnv Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.add i64,
          args := (Arg.var (BitVec.ofNat 64 newSz), Arg.imm 1, ()) }
        fun p_13 =>
      Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "r2b_str_alloc_cap"
        (Arg.var rt, Arg.var p_13.fst, Arg.var (BitVec.ofNat 64 newSz), Arg.var nlen, ())
        fun p_14 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p_14.fst, Arg.imm 32, ()) } fun p_15 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var sObj.addr, Arg.imm 32, ()) } fun p =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p.fst, Arg.var (BitVec.ofNat 64 b), ()) } fun p =>
      Expr.call (as := [i64, i64, i64]) (bs := []) "r2_mem_copy_bytes"
        (Arg.var p_15.fst, Arg.var p.fst, Arg.var (BitVec.ofNat 64 newSz), ()) fun _ =>
      Expr.ret (Arg.var p_14.fst, ())) m := by
  intro bs newSz nlen
  have hszLt := str_payload_lt_max sObj hcanon
  have hsz64 : bs.length < 2 ^ 64 := Nat.lt_trans hszLt strMaxCap_lt_pow64
  have hbLe : b ≤ bs.length := Nat.le_trans (Nat.le_of_lt hbe) heLe
  have hnewLt : newSz < strMaxCap :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt heLe hszLt)
  have hnew64 : newSz < 2 ^ 64 := Nat.lt_trans hnewLt strMaxCap_lt_pow64
  have hnew1LeMax : newSz + 1 ≤ strMaxCap := Nat.succ_le_of_lt hnewLt
  have hnew164 : newSz + 1 < 2 ^ 64 := Nat.lt_of_le_of_lt hnew1LeMax strMaxCap_lt_pow64
  have hnewTo : (BitVec.ofNat 64 newSz).toNat = newSz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew64]
  have hnew1To : (BitVec.ofNat 64 newSz + 1#64).toNat = newSz + 1 := by
    rw [bv_ofNat_add1_mod64 newSz hnew64, BitVec.toNat_ofNat, Nat.mod_mod,
      Nat.mod_eq_of_lt hnew164]
  let sub := (bs.take e).drop b
  have hsubLen : sub.length = newSz := by
    simp [sub, bs, List.length_drop, List.length_take, Nat.min_eq_left heLe, newSz]
  r2b_call rtR2bEnv_r2b_str_alloc_cap
  dsimp only [r2bStrAllocCapSpec, vals, Tup.map, Arg.val]
  have hvalid : newSz < strMaxCap ∧ newSz < newSz + 1 ∧ newSz + 1 ≤ strMaxCap :=
    ⟨hnewLt, Nat.lt_succ_self _, hnew1LeMax⟩
  rw [show (1 : BitVec 64) = 1#64 from rfl, hnewTo, hnew1To, ite_eq_left hvalid]
  have hav' : st.hasFree (strAllocBytes (newSz + 1)) ∨ strAllocBytes (newSz + 1) ≤ st.rem := by
    rw [show ((bs.take e).drop b).length = newSz from hsubLen] at hav
    exact hav
  refine ⟨st, lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R, hav', sep_cast hm (by ac_rfl),
    fun dst st1 m1 hdst0 hdst8 hpr1 hrem1 _ hm1 => ?_⟩
  rw [bv_ofNat_add1_mod64 newSz hnew64, Nat.mod_eq_of_lt hnew164] at hm1
  r2b_steps
  have hmS1 : (lcnfObjMem sObj ⋆
      (region (dst + 32#64) newSz ⋆ rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
        cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
        cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
        cell64 (dst + 24#64) nlen ⋆
        bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
        region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
          (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
        lcnfHeap objs ⋆ R)) m1 := sep_cast hm1 (by ac_rfl)
  rw [strObj_eq_bytes_rest hcanon] at hmS1
  have hspSub : bs = bs.take b ++ sub ++ bs.drop e := by
    dsimp only [sub]
    have h1 : (bs.take e).take b = bs.take b := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hbe)]
    conv => lhs; rw [← List.take_append_drop e bs, ← List.take_append_drop b (bs.take e), h1]
  have htakeB : (bs.take b).length = b := by rw [List.length_take, Nat.min_eq_left hbLe]
  have hspSum : (bs.take b).length + (sub ++ bs.drop e).length ≤ 2 ^ 64 := by
    rw [← List.length_append, ← List.append_assoc, ← hspSub]; exact Nat.le_of_lt hsz64
  have hsubDropSum : sub.length + (bs.drop e).length ≤ 2 ^ 64 := by
    have hle := Nat.le_add_left (sub ++ bs.drop e).length (bs.take b).length
    rw [← List.length_append, ← List.append_assoc, ← hspSub] at hle
    rw [List.length_append] at hle
    exact Nat.le_trans hle (Nat.le_of_lt hsz64)
  have happ1 := bytes_append (sObj.addr + 32#64) (bs.take b) (sub ++ bs.drop e) hspSum
  have happ2 := bytes_append (sObj.addr + 32#64 + BitVec.ofNat 64 b) sub (bs.drop e) hsubDropSum
  let restOuter :=
    bytes (sObj.addr + 32#64) (bs.take b) ⋆
      bytes (sObj.addr + 32#64 + BitVec.ofNat 64 b + BitVec.ofNat 64 newSz) (bs.drop e) ⋆
      strRest sObj ⋆ rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
      cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
      cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
      cell64 (dst + 24#64) nlen ⋆
      bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
      region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
        (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
      lcnfHeap objs ⋆ R
  have hmSplit : (bytes (sObj.addr + 32#64 + BitVec.ofNat 64 b) sub ⋆
      region (dst + 32#64) newSz ⋆ restOuter) m1 := by
    dsimp only [bs] at hmS1 hspSub ⊢
    have hmA : (bytes (sObj.addr + 32#64) (bs.take b ++ (sub ++ bs.drop e)) ⋆
        (strRest sObj ⋆ region (dst + 32#64) newSz ⋆ rtC0Inv rt st1 ⋆
          cell64 dst strHeaderWord ⋆ cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
          cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆ cell64 (dst + 24#64) nlen ⋆
          bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
          region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
            (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
          lcnfHeap objs ⋆ R)) m1 := by
      rw [← List.append_assoc, ← hspSub]; exact sep_cast hmS1 (by ac_rfl)
    rw [happ1, htakeB, happ2, hsubLen] at hmA
    dsimp only [restOuter]
    exact sep_cast hmA (by ac_rfl)
  r2b_call rtR2bEnv_r2_mem_copy_bytes
  dsimp only [r2MemCopyBytesSpec, vals, Tup.map, Arg.val]
  try simp only [show (32 : BitVec 64) = 32#64 from rfl]
  refine ⟨sub, newSz, restOuter, by rw [hnewTo]; exact hsubLen, by rw [hnewTo]; exact Nat.le_refl _,
    Nat.le_of_lt hnew64, hmSplit, fun m2 hm2 => ?_⟩
  rw [hnewTo, Nat.sub_self, region_zero] at hm2
  try simp only [emp_sep] at hm2
  try simp only [sep_emp] at hm2
  dsimp only [restOuter] at hm2
  have hmClosed : (lcnfObjMem sObj ⋆ bytes (dst + 32#64) sub ⋆ rtC0Inv rt st1 ⋆
      cell64 dst strHeaderWord ⋆ cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
      cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆ cell64 (dst + 24#64) nlen ⋆
      bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
      region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
        (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
      lcnfHeap objs ⋆ R) m2 := by
    rw [strObj_eq_bytes_rest hcanon]
    dsimp only [bs] at hspSub ⊢
    have hmJ0 : (bytes (sObj.addr + 32#64) (bs.take b ++ (sub ++ bs.drop e)) ⋆
        (strRest sObj ⋆ bytes (dst + 32#64) sub ⋆ rtC0Inv rt st1 ⋆
          cell64 dst strHeaderWord ⋆ cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
          cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆ cell64 (dst + 24#64) nlen ⋆
          bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
          region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
            (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
          lcnfHeap objs ⋆ R)) m2 := by
      rw [happ1, htakeB, happ2, hsubLen]; exact sep_cast hm2 (by ac_rfl)
    rw [← List.append_assoc, ← hspSub] at hmJ0
    exact sep_cast hmJ0 (by ac_rfl)
  r2b_steps
  let rObj := mkStrObj dst 1#32 (sub.length + 1) sub (utf8CountFrom (bs.take e) b)
  have hsubMax : sub.length + 1 ≤ strMaxCap := by rw [hsubLen]; exact hnew1LeMax
  have hcanR : StrCanon rObj :=
    mkStrObj_canon hdst0 hdst8 rc1_nonneg (Nat.le_refl _) hsubMax hcntLt
  have hmR : (rtC0Inv rt st1 ⋆ lcnfObjMem rObj ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m2 := by
    have hparts : (cell64 dst strHeaderWord ⋆
        cell64 (dst + 8#64) (BitVec.ofNat 64 (sub.length + 1)) ⋆
        cell64 (dst + 16#64) (BitVec.ofNat 64 (sub.length + 1)) ⋆
        cell64 (dst + 24#64) (BitVec.ofNat 64 (utf8CountFrom (bs.take e) b)) ⋆
        bytes (dst + 32#64) sub ⋆
        bytes (dst + 32#64 + BitVec.ofNat 64 sub.length) [(0 : UInt8)] ⋆
        region (dst + 32#64 + BitVec.ofNat 64 sub.length + 1#64)
          (strAllocBytes (sub.length + 1) - (32 + sub.length + 1)) ⋆
        (rtC0Inv rt st1 ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R)) m2 := by
      rw [hsubLen]; exact sep_cast hmClosed (by ac_rfl)
    exact sep_cast (mkStrObj_mem_of_parts hsubMax (Nat.le_refl _) hparts) (by ac_rfl)
  exact hpostK dst st1 m2 hdst0 hdst8 hpr1 hrem1 hcanR hmR

private theorem lcnf_string_pos_op3_wp
    {rt : BitVec 64} {sObj : LcnfObj} {objs : List LcnfObj}
    {idxV endV : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcanon : StrCanon sObj)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m)
    (hPost :
      let bs := strPayload sObj
      let b := strPosClamp idxV bs.length
      let e := strPosClamp endV bs.length
      let sub := if b < e then (bs.take e).drop b else []
      let subLen := if b < e then utf8CountFrom (bs.take e) b else 0
      let reqBytes := strAllocBytes (sub.length + 1)
      (st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
      ∀ r st' m',
        r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        StrCanon (mkStrObj r 1#32 (sub.length + 1) sub subLen) →
        (rtC0Inv rt st' ⋆ lcnfObjMem (mkStrObj r 1#32 (sub.length + 1) sub subLen) ⋆
          lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' →
        Q (r, ()) m') :
    wp rtR2bEnv Q X
      (posOp3Expr rt sObj.addr (BitVec.ofNat 64 (strPayload sObj).length) idxV endV) m := by
  rcases hPost with ⟨hav, hpostK⟩
  let bs := strPayload sObj
  let b := strPosClamp idxV bs.length
  let e := strPosClamp endV bs.length
  have hszLt := str_payload_lt_max sObj hcanon
  have hsz64 : bs.length < 2 ^ 64 := Nat.lt_trans hszLt strMaxCap_lt_pow64
  have hbLe : b ≤ bs.length := by
    dsimp only [b, strPosClamp]
    split <;> first | exact Nat.min_le_right _ _ | exact Nat.le_refl _
  have heLe : e ≤ bs.length := by
    dsimp only [e, strPosClamp]
    split <;> first | exact Nat.min_le_right _ _ | exact Nat.le_refl _
  have hb64 : b < 2 ^ 64 := Nat.lt_of_le_of_lt hbLe hsz64
  have he64 : e < 2 ^ 64 := Nat.lt_of_le_of_lt heLe hsz64
  have hmS : (lcnfObjMem sObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m := sep_cast hm (by ac_rfl)
  dsimp only [posOp3Expr]
  refine posOp3_clamp_wp hsz64 (posOp3_clamp_wp hsz64 ?_)
  dsimp only [posOp3SliceExpr]
  c0_let_simp
  by_cases hbe : b < e
  · have hnotGe : (BitVec.ofNat 64 e).ule (BitVec.ofNat 64 b) = false := by
      rw [BitVec.ule, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt he64, Nat.mod_eq_of_lt hb64]
      exact decide_eq_false (Nat.not_le_of_lt hbe)
    let newSz := e - b
    have hnewLt : newSz < strMaxCap :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt heLe hszLt)
    have hnew64 : newSz < 2 ^ 64 := Nat.lt_trans hnewLt strMaxCap_lt_pow64
    have hnewSub : BitVec.ofNat 64 e - BitVec.ofNat 64 b = BitVec.ofNat 64 newSz := by
      apply BitVec.eq_of_toNat_eq
      rw [str_sub_mod_lt e b he64 (Nat.le_of_lt hbe), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hnew64]
    have htakeLen : (bs.take e).length = e := by rw [List.length_take, Nat.min_eq_left heLe]
    obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
    have hspE : bs = bs.take e ++ bs.drop e := (List.take_append_drop e bs).symm
    have hlenSum : (bs.take e).length + (bs.drop e).length ≤ 2 ^ 64 := by
      rw [← List.length_append, ← hspE]; exact Nat.le_of_lt hsz64
    have happE := bytes_append (sObj.addr + 32#64) (bs.take e) (bs.drop e) hlenSum
    have hmSubE : (bytes (sObj.addr + 32#64) (bs.take e) ⋆
        (bytes (sObj.addr + 32#64 + BitVec.ofNat 64 e) (bs.drop e) ⋆ Rest)) m := by
      have hmE0 : (bytes (sObj.addr + 32#64) (bs.take e ++ bs.drop e) ⋆ Rest) m := by
        dsimp only [bs] at hspE hmExp ⊢; rw [← hspE]; exact hmExp
      rw [happE, htakeLen] at hmE0
      exact sep_cast hmE0 (by ac_rfl)
    refine wp_jnz_false ?_ ?_
    · exact hnotGe
    c0_let_simp
    rw [hnewSub]
    refine posOp3_count_loop_wp hcanon hbe heLe hmSubE fun hcntLt => ?_
    have hav' : st.hasFree (strAllocBytes (((bs.take e).drop b).length + 1)) ∨
        strAllocBytes (((bs.take e).drop b).length + 1) ≤ st.rem := by
      simpa [bs, b, e, hbe] using hav
    refine posOp3_alloc_copy_wp hcanon hbe heLe hcntLt hav' hm ?_
    intro r st' m' hr0 hr8 hpr1 hrem1 hcanR hmR
    have hpostK' := hpostK r st' m' hr0 hr8 hpr1 hrem1
    simpa [bs, b, e, hbe] using hpostK' (by simpa [bs, b, e, hbe] using hcanR)
      (by simpa [bs, b, e, hbe] using hmR)
  · have hge : (BitVec.ofNat 64 e).ule (BitVec.ofNat 64 b) = true := by
      rw [BitVec.ule, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt he64, Nat.mod_eq_of_lt hb64]
      exact decide_eq_true (Nat.not_lt.mp hbe)
    refine wp_jnz_true ?_ ?_
    · exact hge
    refine posOp3_empty_wp (by simpa [bs, b, e, hbe] using hav) hm ?_
    intro r st' m' hr0 hr8 hpr1 hrem1 hcanR hmR
    have hpostK' := hpostK r st' m' hr0 hr8 hpr1 hrem1
    simpa [bs, b, e, hbe] using hpostK' (by simpa [bs, b, e, hbe] using hcanR)
      (by simpa [bs, b, e, hbe] using hmR)

private theorem lcnf_string_pos_op4_wp
    {rt : BitVec 64} {sObj : LcnfObj} {objs : List LcnfObj}
    {idxV endV : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcanon : StrCanon sObj)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m)
    (hPost : ∀ m', (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' →
      Q (strPosOpVal 4#64 (strPayload sObj) idxV endV, ()) m') :
    wp rtR2bEnv Q X (posOp4Expr sObj.addr (BitVec.ofNat 64 (strPayload sObj).length) idxV) m := by
  let bs := strPayload sObj
  have hszLt := str_payload_lt_max sObj hcanon
  have hsz64 : bs.length < 2 ^ 64 := Nat.lt_trans hszLt strMaxCap_lt_pow64
  have hmS : (lcnfObjMem sObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
  dsimp only [posOp4Expr]
  r2b_to_group
  c0_step
  · have ha0 : (idxV &&& 1#64) = 0#64 := hc
    r2b_steps
    have hsp := hPost m (sep_cast hm (by ac_rfl))
    rwa [strPosOpVal_op4, ite_eq_left ha0] at hsp
  · have ha1 : (idxV &&& 1#64) ≠ 0#64 := hc
    r2b_to_group
    c0_step
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      r2b_steps
      have hsp := hPost m (sep_cast hm (by ac_rfl))
      rwa [strPosOpVal_op4, ite_eq_right ha1, dite_eq_right (Nat.not_lt_of_le hc)] at hsp
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      have hlt : (idxV >>> 1).toNat < bs.length := Nat.lt_of_not_le hc
      apply wp_load_of (by
        first
        | exact r2b_c0_load_bytes_add32 hmExp hlt (Nat.le_of_lt hsz64)
        | exact r2b_c0_load_bytes_add32 hmExp (by rwa [bv64_ushiftRight_sext1])
            (Nat.le_of_lt hsz64))
      r2b_steps
      have hspec := hPost m (sep_cast hm (by ac_rfl))
      rw [strPosOpVal_op4, ite_eq_right ha1, dite_eq_left hlt] at hspec
      try rw [bv64_ushiftRight_sext1]
      have hbvEq : BitVec.ofNat 8 bs[(idxV >>> 1).toNat].toNat =
          bs[(idxV >>> 1).toNat].toBitVec := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
        exact Nat.mod_eq_of_lt bs[(idxV >>> 1).toNat].toBitVec.isLt
      rwa [hbvEq]

private theorem lcnf_string_pos_op5_wp
    {rt : BitVec 64} {sObj : LcnfObj} {objs : List LcnfObj}
    {idxV endV : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcanon : StrCanon sObj)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m)
    (hPost : ∀ m', (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' →
      Q (strPosOpVal 5#64 (strPayload sObj) idxV endV, ()) m') :
    wp rtR2bEnv Q X (posOp5Expr sObj.addr (BitVec.ofNat 64 (strPayload sObj).length) idxV) m := by
  let bs := strPayload sObj
  have hszLt := str_payload_lt_max sObj hcanon
  have hsz64 : bs.length < 2 ^ 64 := Nat.lt_trans hszLt strMaxCap_lt_pow64
  have hszTo : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz64]
  have hmS : (lcnfObjMem sObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
  dsimp only [posOp5Expr]
  r2b_to_group
  c0_step
  · have ha0 : (idxV &&& 1#64) = 0#64 := hc
    r2b_steps
    have hsp := hPost m (sep_cast hm (by ac_rfl))
    rwa [strPosOpVal_op5, ite_eq_left ha0] at hsp
  · have ha1 : (idxV &&& 1#64) ≠ 0#64 := hc
    r2b_to_group
    c0_step
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      r2b_steps
      have hsp := hPost m (sep_cast hm (by ac_rfl))
      rwa [strPosOpVal_op5, ite_eq_right ha1, ite_eq_left hc] at hsp
    · try rw [bv64_ushiftRight_sext1] at hc
      rw [Nat.mod_eq_of_lt hsz64] at hc
      have hng : ¬ bs.length < (idxV >>> 1).toNat := hc
      r2b_to_group
      c0_step
      · try rw [bv64_ushiftRight_sext1] at hc
        have heq : (idxV >>> 1).toNat = bs.length := by
          have := congrArg BitVec.toNat hc; rwa [hszTo] at this
        r2b_steps
        have hnl : ¬ (idxV >>> 1).toNat < bs.length := by rw [heq]; exact Nat.lt_irrefl _
        have hsp := hPost m (sep_cast hm (by ac_rfl))
        rwa [strPosOpVal_op5, ite_eq_right ha1, ite_eq_right hng, dite_eq_right hnl] at hsp
      · try rw [bv64_ushiftRight_sext1] at hc
        have hne : (idxV >>> 1).toNat ≠ bs.length := by
          intro he; apply hc; apply BitVec.eq_of_toNat_eq; rw [he, hszTo]
        have hlt : (idxV >>> 1).toNat < bs.length :=
          Nat.lt_of_le_of_ne (Nat.not_lt.mp hng) hne
        apply wp_load_of (by
          first
          | exact r2b_c0_load_bytes_add32 hmExp hlt (Nat.le_of_lt hsz64)
          | exact r2b_c0_load_bytes_add32 hmExp (by rwa [bv64_ushiftRight_sext1])
              (Nat.le_of_lt hsz64))
        r2b_to_group
        c0_step
        · have hmNe : (bs[(idxV >>> 1).toNat].toNat &&& 0xc0) ≠ 0x80 := by
            rw [show (192 : BitVec 64) = 192#64 from rfl,
              show (128 : BitVec 64) = 128#64 from rfl] at hc
            intro h0; apply hc; apply BitVec.eq_of_toNat_eq
            rw [bv8_zext_mask_eq]; exact h0
          r2b_steps
          have hsp := hPost m (sep_cast hm (by ac_rfl))
          rwa [strPosOpVal_op5, ite_eq_right ha1, ite_eq_right hng, dite_eq_left hlt,
            ite_eq_left hmNe] at hsp
        · have hmEq : (bs[(idxV >>> 1).toNat].toNat &&& 0xc0) = 0x80 := by
            rw [show (192 : BitVec 64) = 192#64 from rfl,
              show (128 : BitVec 64) = 128#64 from rfl] at hc
            have htn := congrArg BitVec.toNat hc
            rw [bv8_zext_mask_eq] at htn; exact htn
          r2b_steps
          have hsp := hPost m (sep_cast hm (by ac_rfl))
          rw [strPosOpVal_op5, ite_eq_right ha1, ite_eq_right hng, dite_eq_left hlt,
            ite_eq_right (Classical.not_not.mpr hmEq)] at hsp
          rwa [show (0#64 : BitVec 64) = 0 from rfl] at hsp

/-! ## 4. Main Router: `lcnf_string_pos_op_wp` -/

theorem lcnf_string_pos_op_wp :
    ∀ xs m Q X,
      lcnfStringPosOpSpec xs m Q X → Func.wp rtR2bEnv lcnf_string_pos_op_body xs m Q X := by
  intro ⟨rt, op, s, idxV, endV, ⟨⟩⟩ m Q X
    ⟨st, sObj, objs, R, hsAddr, hcanon, hobj1, _, hm, hPost⟩
  subst hsAddr
  dsimp only [Func.wp, lcnf_string_pos_op_body]
  change LeanQbe.T.wp _ _ _ _ _
  have hmS : (lcnfObjMem sObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m := sep_cast hm (by ac_rfl)
  apply wp_load_of (str_load_sz hcanon hmS)
  c0_let_simp
  try rw [str_sz_sub1_eq sObj hcanon] at *
  by_cases hop0 : op = 0#64
  · subst hop0
    rw [ite_eq_left (Or.inl rfl)] at hPost
    dsimp only at hPost
    simp only [bv64_1_ne_0.symm, ite_false] at hPost
    apply wp_jnz_true rfl
    exact lcnf_string_pos_op0_wp hcanon hm hPost
  · apply wp_jnz_false (by simpa using beq_false_of_ne hop0)
    c0_let_simp
    by_cases hop1 : op = 1#64
    · subst hop1
      rw [ite_eq_left (Or.inr (Or.inl rfl))] at hPost
      dsimp only at hPost
      simp only [ite_true] at hPost
      apply wp_jnz_true rfl
      exact lcnf_string_pos_op1_wp hcanon (fun h => hobj1 ⟨rfl, h.1, h.2⟩) hm hPost
    · apply wp_jnz_false (by simpa using beq_false_of_ne hop1)
      c0_let_simp
      by_cases hop2 : op = 2#64
      · subst hop2
        rw [ite_eq_left (Or.inr (Or.inr (Or.inl rfl)))] at hPost
        dsimp only at hPost
        simp only [bv64_2_ne_1, ite_false] at hPost
        apply wp_jnz_true rfl
        exact lcnf_string_pos_op2_wp hcanon hm hPost
      · apply wp_jnz_false (by simpa using beq_false_of_ne hop2)
        c0_let_simp
        by_cases hop3 : op = 3#64
        · subst hop3
          rw [ite_eq_right (by simp [hop0, hop1, hop2]), ite_eq_left rfl] at hPost
          apply wp_jnz_true rfl
          exact lcnf_string_pos_op3_wp hcanon hm hPost
        · apply wp_jnz_false (by simpa using beq_false_of_ne hop3)
          c0_let_simp
          by_cases hop4 : op = 4#64
          · subst hop4
            rw [ite_eq_left (Or.inr (Or.inr (Or.inr (Or.inl rfl))))] at hPost
            dsimp only at hPost
            simp only [bv64_4_ne_1, ite_false] at hPost
            apply wp_jnz_true rfl
            exact lcnf_string_pos_op4_wp hcanon hm hPost
          · apply wp_jnz_false (by simpa using beq_false_of_ne hop4)
            c0_let_simp
            by_cases hop5 : op = 5#64
            · subst hop5
              rw [ite_eq_left (Or.inr (Or.inr (Or.inr (Or.inr rfl))))] at hPost
              dsimp only at hPost
              simp only [bv64_5_ne_1, ite_false] at hPost
              apply wp_jnz_true rfl
              exact lcnf_string_pos_op5_wp hcanon hm hPost
            · apply wp_jnz_false (by simpa using beq_false_of_ne hop5)
              rw [ite_eq_right (by simp [hop0, hop1, hop2, hop4, hop5]),
                ite_eq_right hop3] at hPost
              r2b_steps
              exact hPost

end LeanQbe.T.LeanLCNF
