/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidCoreHelpers

/-!
# Kissat Fidelity BVE WP Proofs — `full_k6_core_fid_wp`

`CanonicalEnv`-clean `Func.wp` proof for `full_k6_core_fid` (`0` legacy `Full*` imports;
zero `@[expose]` on theorems; every decl `<= 450` LOC; `<= 100` cols).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FidK6Tactics M8K6bTactics FidK6DefTactics

public section

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide | omega | fid_omega)

/-! ## 1. Phase 3 Clause Closure & Fixpoint Loop Sub-WPs -/

/-- Extracted C0 `Expr` for one active clause's antecedent/level-0 core closure in Phase 3. -/
private def fidCorePhase3ClauseExpr (pScr : BitVec 64)
    (mv nc nv acap cid' cmeta off sz : BitVec 32) (chg_c : Bool)
    (Jc : Cont [.bool]) : Expr Val Cont [] :=
  let o_rsn : BitVec 32 := 4224 + mv
  let o_cl_meta : BitVec 32 := 4224 + 33 * mv
  let o_cl_aux : BitVec 32 := 4224 + 37 * mv
  let o_arena : BitVec 32 := 4224 + 45 * mv
  Expr.group (sig := [[.bool]]) (fun Js_m =>
    Blocks.cons (fun p_36 =>
      Expr.group (sig := [[.bool]]) (fun _ =>
        Blocks.cons (fun p => Expr.jump Jc (Arg.var p.fst, ())) Blocks.nil) fun Jw =>
      Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                  args := (Arg.var off, Arg.var sz, ()) } fun p_37 =>
      Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ule i32 Ty.bool (by decide),
                  args := (Arg.var p_37.fst, Arg.var acap, ()) } fun p_38 =>
      Expr.jnz (Arg.var p_38.fst)
        (Expr.group (sig := [[.bool, i32]]) (fun Js_3 =>
           Blocks.cons (fun p_39 =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                         args := (Arg.var p_39.snd.fst, Arg.var sz, ()) } fun p_40 =>
             Expr.jnz (Arg.var p_40.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var o_arena, Arg.var off, ()) } fun p_41 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var p_41.fst, Arg.var p_39.snd.fst, ()) } fun p_42 =>
                Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                            args := (Arg.var p_42.fst, ()) } fun p_43 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var p_43.fst, Arg.imm 4, ()) } fun p_44 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var pScr, Arg.var p_44.fst, ()) } fun p_45 =>
                Expr.load i32 (Arg.var p_45.fst) fun ld_8 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                            args := (Arg.var ld_8, Arg.imm 1, ()) } fun p_46 =>
                Expr.group (sig := [[.bool]]) (fun _ =>
                  Blocks.cons (fun p =>
                    Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                args := (Arg.var p_39.snd.fst, Arg.imm 1, ()) } fun p_47 =>
                    Expr.jump Js_3.fst (Arg.var p.fst, Arg.var p_47.fst, ())) Blocks.nil)
                    fun Jk =>
                Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool
                              (by decide),
                            args := (Arg.var p_46.fst, Arg.var nv, ()) } fun p_47 =>
                Expr.jnz (Arg.var p_47.fst)
                  (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                               args := (Arg.imm 4224, Arg.var p_46.fst, ()) } fun p_48 =>
                   Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                               args := (Arg.var p_48.fst, ()) } fun p_49 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                               args := (Arg.var p_49.fst, Arg.imm 4, ()) } fun p_50 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var pScr, Arg.var p_50.fst, ()) } fun p_51 =>
                   Expr.load i32 (Arg.var p_51.fst) fun ld_9 =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool
                                 (by decide),
                               args := (Arg.var ld_9, Arg.imm 0, ()) } fun p_52 =>
                   Expr.jnz (Arg.var p_52.fst)
                     (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                  args := (Arg.var o_rsn, Arg.var p_46.fst, ()) } fun p =>
                      Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                  args := (Arg.var p.fst, ()) } fun p =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                  args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                      Expr.load i32 (Arg.var p.fst) fun ld_10 =>
                      Expr.group (sig := [[.bool]]) (fun _ =>
                        Blocks.cons (fun p => Expr.jump Jk.fst (Arg.var p.fst, ())) Blocks.nil)
                          fun J9 =>
                      Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool
                                    (by decide),
                                  args := (Arg.var ld_10, Arg.var nc, ()) } fun p =>
                      Expr.jnz (Arg.var p.fst)
                        (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                     args := (Arg.var o_cl_meta, Arg.var ld_10, ()) } fun p =>
                         Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                     args := (Arg.var p.fst, ()) } fun p =>
                         Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                     args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                         Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                     args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                         Expr.load i32 (Arg.var p.fst) fun ld_11 =>
                         Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                                     args := (Arg.var ld_11, Arg.imm 2147483648, ()) } fun p =>
                         Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool
                                       (by decide),
                                     args := (Arg.var p.fst, Arg.imm 0, ()) } fun p =>
                         Expr.jnz (Arg.var p.fst)
                           (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                        args := (Arg.var o_cl_meta, Arg.var ld_10, ()) } fun p =>
                            Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                        args := (Arg.var p.fst, ()) } fun p =>
                            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                        args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                        args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                            Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                        args := (Arg.var o_cl_meta, Arg.var ld_10, ()) }
                              fun p_53 =>
                            Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                        args := (Arg.var p_53.fst, ()) } fun p_54 =>
                            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                        args := (Arg.var p_54.fst, Arg.imm 4, ()) } fun p_55 =>
                            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                        args := (Arg.var pScr, Arg.var p_55.fst, ()) } fun p_56 =>
                            Expr.load i32 (Arg.var p_56.fst) fun ld =>
                            Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                                        args := (Arg.var ld, Arg.imm 2147483648, ()) } fun p_57 =>
                            Expr.store (Arg.var p_57.fst) (Arg.var p.fst)
                              (Expr.jump J9.fst (Arg.imm true, ())))
                           (Expr.jump J9.fst (Arg.var p_39.fst, ())))
                        (Expr.jump J9.fst (Arg.var p_39.fst, ())))
                     (Expr.jump Jk.fst (Arg.var p_39.fst, ())))
                  (Expr.jump Jk.fst (Arg.var p_39.fst, ())))
               (Expr.jump Jw.fst (Arg.var p_39.fst, ()))) Blocks.nil) fun Js =>
         Expr.jump Js.fst (Arg.var p_36.fst, Arg.imm 0, ()))
        (Expr.jump Jw.fst (Arg.var p_36.fst, ()))) Blocks.nil) fun Jm =>
  Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
              args := (Arg.var cmeta, Arg.imm 1073741824, ()) } fun p =>
  Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool (by decide),
              args := (Arg.var p.fst, Arg.imm 0, ()) } fun p =>
  Expr.jnz (Arg.var p.fst)
    (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                 args := (Arg.var o_cl_aux, Arg.var cid', ()) } fun p =>
     Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                 args := (Arg.var p.fst, ()) } fun p =>
     Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                 args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
     Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                 args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
     Expr.load i32 (Arg.var p.fst) fun ld_8 =>
     Expr.group (sig := [[.bool]]) (fun _ =>
       Blocks.cons (fun p => Expr.jump Jm.fst (Arg.var p.fst, ())) Blocks.nil) fun Jw =>
     Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                 args := (Arg.var off, Arg.var sz, ()) } fun p =>
     Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                 args := (Arg.var p.fst, Arg.var ld_8, ()) } fun p =>
     Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ule i32 Ty.bool (by decide),
                 args := (Arg.var p.fst, Arg.var acap, ()) } fun p =>
     Expr.jnz (Arg.var p.fst)
       (Expr.group (sig := [[.bool, i32]]) (fun Js_2 =>
          Blocks.cons (fun p_loop =>
            Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                        args := (Arg.var p_loop.snd.fst, Arg.var ld_8, ()) } fun p_36 =>
            Expr.jnz (Arg.var p_36.fst)
              (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                           args := (Arg.var o_arena, Arg.var off, ()) } fun p_37 =>
               Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                           args := (Arg.var p_37.fst, Arg.var sz, ()) } fun p_38 =>
               Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                           args := (Arg.var p_38.fst, Arg.var p_loop.snd.fst, ()) } fun p_39 =>
               Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                           args := (Arg.var p_39.fst, ()) } fun p_40 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                           args := (Arg.var p_40.fst, Arg.imm 4, ()) } fun p_41 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                           args := (Arg.var pScr, Arg.var p_41.fst, ()) } fun p_42 =>
               Expr.load i32 (Arg.var p_42.fst) fun ld_9 =>
               Expr.group (sig := [[.bool]]) (fun _ =>
                 Blocks.cons (fun p_43 =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                               args := (Arg.var p_loop.snd.fst, Arg.imm 1, ()) } fun p =>
                   Expr.jump Js_2.fst (Arg.var p_43.fst, Arg.var p.fst, ())) Blocks.nil)
                   fun Js_k =>
               Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                           args := (Arg.var ld_9, Arg.var nc, ()) } fun p_43 =>
               Expr.jnz (Arg.var p_43.fst)
                 (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                              args := (Arg.var o_cl_meta, Arg.var ld_9, ()) } fun p_44 =>
                  Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                              args := (Arg.var p_44.fst, ()) } fun p_45 =>
                  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                              args := (Arg.var p_45.fst, Arg.imm 4, ()) } fun p_46 =>
                  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var pScr, Arg.var p_46.fst, ()) } fun p_47 =>
                  Expr.load i32 (Arg.var p_47.fst) fun ld_10 =>
                  Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                              args := (Arg.var ld_10, Arg.imm 2147483648, ()) } fun p_48 =>
                  Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool
                                (by decide),
                              args := (Arg.var p_48.fst, Arg.imm 0, ()) } fun p_49 =>
                  Expr.jnz (Arg.var p_49.fst)
                    (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                 args := (Arg.var o_cl_meta, Arg.var ld_9, ()) } fun pa0 =>
                     Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                 args := (Arg.var pa0.fst, ()) } fun pa1 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                 args := (Arg.var pa1.fst, Arg.imm 4, ()) } fun pa2 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var pScr, Arg.var pa2.fst, ()) } fun pa3 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                 args := (Arg.var o_cl_meta, Arg.var ld_9, ()) } fun p_50 =>
                     Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                 args := (Arg.var p_50.fst, ()) } fun p_51 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                 args := (Arg.var p_51.fst, Arg.imm 4, ()) } fun p_52 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var pScr, Arg.var p_52.fst, ()) } fun p_53 =>
                     Expr.load i32 (Arg.var p_53.fst) fun ld =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                                 args := (Arg.var ld, Arg.imm 2147483648, ()) } fun p_54 =>
                     Expr.store (Arg.var p_54.fst) (Arg.var pa3.fst)
                       (Expr.jump Js_k.fst (Arg.imm true, ())))
                    (Expr.jump Js_k.fst (Arg.var p_loop.fst, ())))
                 (Expr.jump Js_k.fst (Arg.var p_loop.fst, ())))
              (Expr.jump Jw.fst (Arg.var p_loop.fst, ()))) Blocks.nil) fun Js =>
        Expr.jump Js.fst (Arg.var chg_c, Arg.imm 0, ()))
       (Expr.jump Jw.fst (Arg.var chg_c, ())))
    (Expr.jump Jm.fst (Arg.var chg_c, ()))

/-- Extracted WP proof for one active clause in Phase 3 (`fidCorePhase3ClauseExpr`). -/
private theorem fidCore_phase3_clause_wp (Γ : Env) (c : FullCfg) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post []) (X : XPost) (scr0 scrc : List (BitVec 32))
    (cid : BitVec 32) (chg_c : Bool) (Jc : Cont [.bool]) (mc_m : Mem 64)
    (h4214 : 4214 < scr0.length) (h4192 : 4192 < scr0.length)
    (h4193 : 4193 < scr0.length) (h4207 : 4207 < scr0.length) :
    let mv := scr0[4214]'h4214
    let nc := scr0[4193]'h4193
    let nv := scr0[4192]'h4192
    let acap := scr0[4207]'h4207
    let cid' := cid - 1#32
    0 < cid.toNat → (cid - 1#32).toNat = cid.toNat - 1 → cid'.toNat < nc.toNat →
    256 ≤ mv.toNat → mv.toNat ≤ 8192 →
    nc.toNat ≤ 4 * mv.toNat → nv.toNat ≤ mv.toNat →
    4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length →
    scr0.length < 2 ^ 30 → 4224 + 45 * mv.toNat ≤ scr0.length →
    FidCoreInv scr0 mv nc scrc →
    ((4224 + 33 * mv + cid').setWidth 64).toNat = 4224 + 33 * mv.toNat + cid'.toNat →
    ((4224 + 29 * mv + cid').setWidth 64).toNat = 4224 + 29 * mv.toNat + cid'.toNat →
    ∀ (hcm_lt : ((4224 + 33 * mv + cid').setWidth 64).toNat < scrc.length)
      (hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat < scrc.length),
    let cmeta := scrc[((4224 + 33 * mv + cid').setWidth 64).toNat]'hcm_lt
    let off := scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt
    let sz := cmeta &&& 0xFFFF#32
    sz.toNat ≤ 65535 →
    off.toNat + sz.toNat ≤ acap.toNat →
    ((cmeta &&& 0x40000000#32) ≠ 0#32 →
      off.toNat + sz.toNat +
        (scrc[4224 + 37 * mv.toNat + cid'.toNat]?.getD 0#32).toNat ≤ acap.toNat) →
    (FullMem c (m8ScrSt s scrc) ⋆ R) mc_m →
    (∀ (x : Bool × List (BitVec 32)) mj, FidCoreInv scr0 mv nc x.2 →
      (FullMem c (m8ScrSt s x.2) ⋆ R) mj → Jc (x.1, ()) mj) →
    wp Γ Q X (fidCorePhase3ClauseExpr c.pScratchBuf mv nc nv acap cid' cmeta off sz chg_c Jc)
      mc_m := by
  intro mv nc nv acap cid' hcid_pos hcid1 hcid'_lt hmv_lo hmv_hi hnc_le hnv_le hlen_scr
    hcap_lt hbge hikc hcm_e hco_e hcm_lt hco_lt cmeta off sz hsz_le hos_le hcl_lrn hmc hJc
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  have hlc : scrc.length = scr0.length := hikc.2.1
  let invB : Bool × List (BitVec 32) → Mem 64 → Prop := fun x mk =>
    FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) mk
  dsimp only [fidCorePhase3ClauseExpr]
  c0_hsteps_nogrp
  refine wp_join_state (ts := [.bool])
    (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
    (fun _ ⟨chg_m, scrm⟩ m_m ⟨hikm, hmm⟩ => by
      have hlm : scrm.length = scr0.length := hikm.2.1
      c0_hsteps_nogrp
      refine wp_join_state (ts := [.bool])
        (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
        (fun _ x mj ⟨h1, h2⟩ => by c0_hsteps!; exact hJc x mj h1 h2)
        (fun Jw hJw => by
          c0_hsplit
          · c0_hsteps_nogrp
            refine wp_loop_group (ts := [.bool, i32])
              (fun rj (chgj, j, ()) mj => ∃ scrj : List (BitVec 32),
                FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ sz.toNat ∧ rj = sz.toNat - j.toNat ∧
                (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
            · rintro Lj rem_j ⟨chgj, j, ⟨⟩⟩ mj hLj ⟨scrj, hikj, hj_le, rfl, hmj⟩
              have hlj : scrj.length = scr0.length := hikj.2.1
              c0_hsplit
              · have hj_lt : j.toNat < sz.toNat := by
                  have hc' := hc; fid_norm_ofnat
                  try simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                    at hc'
                  exact hc'
                have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                  m8_bv32_add1_toNat hj_lt (by clear hmc hikc hmm hikm hmj hikj hLj hJw; omega)
                have har_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := off) (y := j) hmv_hi
                  (by decide) (by clear hmc hikc hmm hikm hmj hikj hLj hJw; omega)
                have har_lt : ((4224 + 45 * mv + off + j).setWidth 64).toNat < scrj.length := by
                  clear hmc hikc hmm hikm hmj hikj hLj hJw; rw [hlj, har_e]; omega
                let lv := (scrj[((4224 + 45 * mv + off + j).setWidth 64).toNat]'har_lt) >>>
                  (1 : Nat)
                c0_hsteps_nogrp
                refine wp_join_state (ts := [.bool])
                  (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
                  (fun _ ⟨chgk, scrk⟩ mk ⟨hikk, hmk⟩ => by
                    c0_hsteps!
                    exact hLj (sz.toNat - (j + 1#32).toNat) (chgk, j + 1#32, ()) mk (by omega)
                      ⟨scrk, hikk, by omega, rfl, hmk⟩)
                  (fun Jk hJk => by
                    c0_hsplit
                    · have hlv_lt : lv.toNat < nv.toNat := by
                        have hc' := hc; clear hc hmc hikc hmm hikm hmj hikj hLj hJw hJk
                        fid_norm_ofnat
                        simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                          at hc'
                        have har_mod : (4224 + 45 * mv.toNat + off.toNat + j.toNat) % 4294967296 =
                            ((4224 + 45 * mv + off + j).setWidth 64).toNat := by
                          rw [har_e, Nat.mod_eq_of_lt (by omega)]
                        have hlv_eq := congrArg (fun v : BitVec 32 => v.toNat / 2)
                          (m8_k6_get_congr har_mod (by rw [har_mod, hlj, har_e]; omega) har_lt)
                        have hlv_nat : lv.toNat = (scrj[((4224 + 45 * mv + off +
                            j).setWidth 64).toNat]'har_lt).toNat / 2 :=
                          m8_bv32_lshr1_toNat _
                        rw [hlv_nat, ← hlv_eq]
                        simpa [Nat.shiftRight_eq_div_pow, Nat.pow_one] using hc'
                      clear hc
                      have hlv_e := fid_k6_off_add0 (x := lv)
                        (by clear hmc hikc hmm hikm hmj hikj hLj hJw hJk; omega)
                      have hlv_b : (((4224 : BitVec 32) + lv).setWidth 64).toNat < scrj.length := by
                        rw [hlj, hlv_e]; omega
                      c0_hsplit
                      · have hrs_e := fid_k6_off_add1 (mv := mv) (x := lv) hmv_hi
                          (by clear hmc hikc hmm hikm hmj hikj hLj hJw hJk; omega)
                        have hrs_b : ((4224 + mv + lv).setWidth 64).toNat < scrj.length := by
                          rw [hlj, hrs_e]; exact fidCore_1_lt (Nat.le_trans (Nat.le_of_lt hlv_lt)
                            hnv_le) hmv_lo hbge
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [.bool])
                          (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
                          (fun _ ⟨chg9, scr9⟩ m9 ⟨hik9, hm9⟩ => by
                            c0_hsteps!; exact hJk (chg9, scr9) m9 ⟨hik9, hm9⟩)
                          (fun J9 hJ9 => by
                            let r0 := scrj[((4224 + mv + lv).setWidth 64).toNat]'hrs_b
                            c0_hsplit
                            · have hr0_lt : r0.toNat < nc.toNat := by
                                have hc' := hc; clear hc hmc hikc hmm hikm hmj hikj hLj hJw hJk
                                  hJ9
                                fid_norm_ofnat
                                simp (disch := fid_omega) only [bv_c0, Nat.reducePow,
                                  BitVec.reduceToNat] at hc'
                                have har_mod :
                                    (4224 + 45 * mv.toNat + off.toNat + j.toNat) % 4294967296 =
                                      ((4224 + 45 * mv + off + j).setWidth 64).toNat := by
                                  rw [har_e, Nat.mod_eq_of_lt (by omega)]
                                have hlv_eq : (scrj[(4224 + 45 * mv.toNat + off.toNat +
                                    j.toNat) % 4294967296]'(by
                                      rw [har_mod, hlj, har_e]; omega)).toNat / 2 = lv.toNat := by
                                  rw [m8_bv32_lshr1_toNat]
                                  exact congrArg (fun v : BitVec 32 => v.toNat / 2)
                                    (m8_k6_get_congr har_mod _ har_lt)
                                try simp only [BitVec.toNat_ushiftRight,
                                  Nat.shiftRight_eq_div_pow, Nat.pow_one] at hc'
                                have hrs_idx_eq : (4224 + mv.toNat + (scrj[(4224 + 45 * mv.toNat +
                                    off.toNat + j.toNat) % 4294967296]'(by
                                      rw [har_mod, hlj, har_e]; omega)).toNat / 2) % 4294967296 =
                                    ((4224 + mv + lv).setWidth 64).toNat := by
                                  rw [hlv_eq, hrs_e, Nat.mod_eq_of_lt (by omega)]
                                have hr0_eq := congrArg BitVec.toNat
                                  (m8_k6_get_congr hrs_idx_eq
                                    (by rw [hrs_idx_eq, hlj, hrs_e]; omega) hrs_b)
                                dsimp only [r0]
                                rw [← hr0_eq]
                                exact hc'
                              clear hc
                              have hmr_e := fid_k6_off_add (mv := mv) (k := 33) (x := r0) hmv_hi
                                (by decide) (by omega)
                              have hmr_b : ((4224 + 33 * mv + r0).setWidth 64).toNat <
                                  scrj.length := by
                                rw [hlj, hmr_e]; exact fidCore_k_lt 33
                                  (Nat.le_trans (Nat.le_of_lt hr0_lt) hnc_le) hmv_lo hbge
                              c0_hsplit
                              · c0_hsteps!
                                refine hJ9 (true, _) _ ⟨fidCoreInv_set_meta_pres h4214 hmv_eq
                                  hnc_le hikj hr0_lt hmr_e hmr_b (m8_km_core_or_pres _), hm⟩
                              · c0_hsteps!; exact hJ9 (chgj, scrj) mj ⟨hikj, hmj⟩
                            · c0_hsteps!; exact hJ9 (chgj, scrj) mj ⟨hikj, hmj⟩)
                      · c0_hsteps!; exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩
                    · c0_hsteps!; exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩)
              · c0_hsteps!; exact hJw (chgj, scrj) mj ⟨hikj, hmj⟩
            · intro Lj hLj; c0_hsteps!
              exact hLj sz.toNat (chg_m, 0#32, ()) m_m ⟨scrm, hikm, Nat.zero_le _, by simp, hmm⟩
          · c0_hsteps!; exact hJw (chg_m, scrm) m_m ⟨hikm, hmm⟩))
    (fun Jm hJm => by
      c0_hsplit
      · have hlrn : (cmeta &&& 0x40000000#32) ≠ 0#32 := by
          intro heq; apply hc; exact heq
        have hca_e := fid_k6_off_add (mv := mv) (k := 37) (x := cid') hmv_hi (by decide)
          (by omega)
        have hca_lt : ((4224 + 37 * mv + cid').setWidth 64).toNat < scrc.length := by
          rw [hlc, hca_e]
          exact fidCore_k_lt 37 (Nat.le_trans (Nat.le_of_lt hcid'_lt) hnc_le) hmv_lo hbge
        let na := scrc[((4224 + 37 * mv + cid').setWidth 64).toNat]'hca_lt
        have hna_eq : (scrc[4224 + 37 * mv.toNat + cid'.toNat]?.getD 0#32) = na := by
          rw [List.getElem?_eq_getElem (by
            rw [hlc]; exact fidCore_k_lt 37 (Nat.le_trans (Nat.le_of_lt hcid'_lt) hnc_le)
              hmv_lo hbge),
            Option.getD_some]
          exact m8_k6_get_congr hca_e.symm _ _
        have hosn_le : off.toNat + sz.toNat + na.toNat ≤ acap.toNat := by
          rw [← hna_eq]; exact hcl_lrn hlrn
        c0_hsteps_nogrp
        refine wp_join_state (ts := [.bool])
          (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
          (fun _ x mj h => by c0_hsteps!; exact hJm x mj h)
          (fun Jw hJw => by
            c0_hsplit
            · c0_hsteps_nogrp
              refine wp_loop_group (ts := [.bool, i32])
                (fun rj (chgj, j, ()) mj => ∃ scrj : List (BitVec 32),
                  FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ na.toNat ∧ rj = na.toNat - j.toNat ∧
                  (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
              · rintro Lj rem_j ⟨chgj, j, ⟨⟩⟩ mj hLj ⟨scrj, hikj, hj_le, rfl, hmj⟩
                have hlj : scrj.length = scr0.length := hikj.2.1
                c0_hsplit
                · have hj_lt : j.toNat < na.toNat := by
                    have hc' := hc; clear hc; fid_norm_ofnat
                    simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                      at hc'
                    have hna_mod : (4224 + 37 * mv.toNat + cid'.toNat) % 4294967296 =
                        ((4224 + 37 * mv + cid').setWidth 64).toNat := by
                      rw [hca_e, Nat.mod_eq_of_lt (by clear hmc hikc hmj hikj hLj hJm hJw; omega)]
                    have hna_g : (scrc[(4224 + 37 * mv.toNat + cid'.toNat) % 4294967296]'(by
                          rw [hna_mod]; exact hca_lt)).toNat = na.toNat :=
                      congrArg BitVec.toNat (m8_k6_get_congr hna_mod _ _)
                    try rw [hna_g] at hc'
                    exact hc'
                  have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                    m8_bv32_add1_toNat hj_lt (by clear hmc hikc hmj hikj hLj hJm hJw; omega)
                  have har_e := fid_k6_off_add3 (mv := mv) (k := 45)
                    (x := off) (y := sz) (z := j) hmv_hi (by decide)
                    (by clear hmc hikc hmj hikj hLj hJm hJw; omega)
                  have har_lt : ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat <
                      scrj.length := by
                    clear hmc hikc hmj hikj hLj hJm hJw; rw [hlj, har_e]; omega
                  let ant := scrj[((4224 + 45 * mv + off + sz + j).setWidth 64).toNat]'har_lt
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [.bool])
                    (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
                    (fun _ ⟨chgk, scrk⟩ mk ⟨hikk, hmk⟩ => by
                      c0_hsteps!
                      exact hLj (na.toNat - (j + 1#32).toNat) (chgk, j + 1#32, ()) mk (by omega)
                        ⟨scrk, hikk, by omega, rfl, hmk⟩)
                    (fun Jk hJk => by
                      c0_hsplit
                      · have hant_lt : ant.toNat < nc.toNat := by
                          have hc' := hc; clear hc; fid_norm_ofnat
                          simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                            at hc'
                          have har_mod : (4224 + 45 * mv.toNat + off.toNat + sz.toNat + j.toNat) %
                              4294967296 = ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat := by
                            rw [har_e, Nat.mod_eq_of_lt (by omega)]
                          have hant_eq := congrArg BitVec.toNat (m8_k6_get_congr har_mod
                            (by rw [har_mod, hlj, har_e]; omega) har_lt)
                          dsimp only [ant]; rw [← hant_eq]; exact hc'
                        clear hc
                        have hma_e := fid_k6_off_add (mv := mv) (k := 33) (x := ant) hmv_hi
                          (by decide) (by omega)
                        have hma_lt : ((4224 + 33 * mv + ant).setWidth 64).toNat < scrj.length := by
                          rw [hlj, hma_e]
                          exact fidCore_k_lt 33 (Nat.le_trans (Nat.le_of_lt hant_lt) hnc_le)
                            hmv_lo hbge
                        c0_hsplit
                        · c0_hsteps!
                          refine hJk (true, _) _ ⟨fidCoreInv_set_meta_pres h4214 hmv_eq hnc_le
                            hikj hant_lt hma_e hma_lt (m8_km_core_or_pres _), hm⟩
                        · c0_hsteps!; exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩
                      · c0_hsteps!; exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩)
                · c0_hsteps!; exact hJw (chgj, scrj) mj ⟨hikj, hmj⟩
              · intro Lj hLj; c0_hsteps!
                exact hLj na.toNat (chg_c, 0#32, ()) mc_m ⟨scrc, hikc, Nat.zero_le _, by simp, hmc⟩
            · c0_hsteps!; exact hJw (chg_c, scrc) mc_m ⟨hikc, hmc⟩)
      · c0_hsteps!; exact hJm (chg_c, scrc) mc_m ⟨hikc, hmc⟩)

/-- Extracted C0 `Expr` for Phase 3 fixpoint closure loop (`while (changed && pass < nc)`). -/
private def fidCorePhase3Expr (pScr : BitVec 64)
    (mv nc nv acap : BitVec 32) : Expr Val Cont [] :=
  let o_cl_off : BitVec 32 := 4224 + 29 * mv
  let o_cl_meta : BitVec 32 := 4224 + 33 * mv
  Expr.group (sig := [[i32, .bool]]) (fun Js_pass =>
    Blocks.cons (fun p_19 =>
      Expr.jnz (Arg.var p_19.snd.fst)
        (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                     args := (Arg.var p_19.fst, Arg.var nc, ()) } fun p_20 =>
         Expr.jnz (Arg.var p_20.fst)
           (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var p_19.fst, Arg.imm 1, ()) } fun p_21 =>
            Expr.group (sig := [[.bool, i32]]) (fun Js_1 =>
              Blocks.cons (fun p_22 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32 Ty.bool
                              (by decide),
                            args := (Arg.var p_22.snd.fst, Arg.imm 0, ()) } fun p_23 =>
                Expr.jnz (Arg.var p_23.fst)
                  (Expr.let_ { sig := [i32, i32], code := OpCode.sub i32,
                               args := (Arg.var p_22.snd.fst, Arg.imm 1, ()) } fun p_24 =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                               args := (Arg.var o_cl_meta, Arg.var p_24.fst, ()) } fun p_25 =>
                   Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                               args := (Arg.var p_25.fst, ()) } fun p_26 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                               args := (Arg.var p_26.fst, Arg.imm 4, ()) } fun p_27 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var pScr, Arg.var p_27.fst, ()) } fun p_28 =>
                   Expr.load i32 (Arg.var p_28.fst) fun ld_6 =>
                   Expr.group (sig := [[.bool]]) (fun _ =>
                     Blocks.cons (fun p =>
                       Expr.jump Js_1.fst (Arg.var p.fst, Arg.var p_24.fst, ())) Blocks.nil)
                       fun Jc =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                               args := (Arg.var ld_6, Arg.imm 2147483648, ()) } fun p_29 =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool
                                 (by decide),
                               args := (Arg.var p_29.fst, Arg.imm 0, ()) } fun p_30 =>
                   Expr.jnz (Arg.var p_30.fst)
                     (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                  args := (Arg.var o_cl_off, Arg.var p_24.fst, ()) } fun p_31 =>
                      Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                  args := (Arg.var p_31.fst, ()) } fun p_32 =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                  args := (Arg.var p_32.fst, Arg.imm 4, ()) } fun p_33 =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var pScr, Arg.var p_33.fst, ()) } fun p_34 =>
                      Expr.load i32 (Arg.var p_34.fst) fun ld_7 =>
                      Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                                  args := (Arg.var ld_6, Arg.imm 65535, ()) } fun p_35 =>
                      fidCorePhase3ClauseExpr pScr mv nc nv acap p_24.fst ld_6 ld_7 p_35.fst
                        p_22.fst Jc.fst)
                     (Expr.jump Jc.fst (Arg.var p_22.fst, ())))
                  (Expr.jump Js_pass.fst (Arg.var p_21.fst, Arg.var p_22.fst, ()))) Blocks.nil)
                fun Js =>
            Expr.jump Js.fst (Arg.imm false, Arg.var nc, ()))
           (Expr.ret (rs := []) PUnit.unit))
        (Expr.ret (rs := []) PUnit.unit)) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.imm 0, Arg.imm true, ())

/-- Extracted WP proof for the Phase 3 fixpoint closure loop (`fidCorePhase3Expr`). -/
private theorem fidCore_phase3_wp (Γ : Env) (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (Q : Post []) (X : XPost) (scr0 scr2 : List (BitVec 32)) (m2 : Mem 64)
    (_hmin : 15744 ≤ scr0.length) (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) (h4192 : 4192 < scr0.length)
    (h4193 : 4193 < scr0.length) (h4207 : 4207 < scr0.length) :
    let mv := scr0[4214]'h4214
    let nc := scr0[4193]'h4193
    let nv := scr0[4192]'h4192
    let acap := scr0[4207]'h4207
    256 ≤ mv.toNat → mv.toNat ≤ 8192 →
    nc.toNat ≤ 4 * mv.toNat → nv.toNat ≤ mv.toNat →
    4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length →
    scr0.length < 2 ^ 30 → 4224 + 45 * mv.toNat ≤ scr0.length →
    FidCoreInv scr0 mv nc scr2 → (FullMem c (m8ScrSt s scr2) ⋆ R) m2 →
    (∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        (idx < 4224 + 6 * mv.toNat ∨
          (4224 + 7 * mv.toNat ≤ idx ∧ idx < 4224 + 33 * mv.toNat) ∨
          4224 + 37 * mv.toNat ≤ idx) → scr'[idx]? = scr0[idx]?) →
      FidK6BufOk scr' →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') →
    wp Γ Q X (fidCorePhase3Expr c.pScratchBuf mv nc nv acap) m2 := by
  intro mv nc nv acap hmv_lo hmv_hi hnc_le hnv_le hlen_scr hcap_lt hbge hik2 hm2 hQ
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  have hnc_eq : scr0[4193]?.getD 0#32 = nc := m8_k6_get_eq h4193
  have hac_eq : scr0[4207]?.getD 0#32 = acap := m8_k6_get_eq h4207
  dsimp only [fidCorePhase3Expr]
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, .bool])
    (fun rem (pass, chg, ()) mp => ∃ scrp : List (BitVec 32),
      FidCoreInv scr0 mv nc scrp ∧ pass.toNat ≤ nc.toNat ∧
      rem = (if chg then nc.toNat - pass.toNat else 0) ∧ (FullMem c (m8ScrSt s scrp) ⋆ R) mp)
    ?_ ?_
  · rintro Lp rem ⟨pass, chg, ⟨⟩⟩ mp hLp ⟨scrp, hikp, hpass_le, rfl, hmp⟩
    have hlp : scrp.length = scr0.length := hikp.2.1
    have hfin_p : Q () mp :=
      hQ scrp mp (hlp.trans hscr_len) (fun idx hi hor => hikp.2.2.1 idx (by omega) hor)
        hikp.1 (m8ScrSt_eq s scrp ▸ hmp)
    c0_hsplit
    · have hchg_t : chg = true := hc
      c0_hsplit
      · have hpass_lt : pass.toNat < nc.toNat := hc
        have hp1 : (pass + 1#32).toNat = pass.toNat + 1 :=
          m8_bv32_add1_toNat hpass_lt (by clear hQ hfin_p hLp hmp hikp hm2 hik2; omega)
        c0_hsteps_nogrp
        refine wp_loop_group (ts := [.bool, i32])
          (fun rem_c (chg_c, cid, ()) mc_m => ∃ scrc : List (BitVec 32),
            FidCoreInv scr0 mv nc scrc ∧ cid.toNat ≤ nc.toNat ∧ rem_c = cid.toNat ∧
            (FullMem c (m8ScrSt s scrc) ⋆ R) mc_m) ?_ ?_
        · rintro Lc rem_c ⟨chg_c, cid, ⟨⟩⟩ mc_m hLc ⟨scrc, hikc, hcid_le, rfl, hmc⟩
          have hlc : scrc.length = scr0.length := hikc.2.1
          c0_hsplit
          · have hcid_pos : 0 < cid.toNat := hc
            clear hc
            have hcid1 : (cid - 1#32).toNat = cid.toNat - 1 := m8_bv32_sub1_toNat hcid_pos
            let cid' := cid - 1#32
            have hcid'_lt : cid'.toNat < nc.toNat := by
              clear hQ hfin_p hLp hmp hikp hLc hmc hikc hm2 hik2
              dsimp only [cid']; rw [hcid1]; omega
            have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := cid') hmv_hi (by decide)
              (by clear hQ hfin_p hLp hmp hikp hLc hmc hikc hm2 hik2; omega)
            have hcm_lt : ((4224 + 33 * mv + cid').setWidth 64).toNat < scrc.length := by
              clear hQ hfin_p hLp hmp hikp hLc hmc hikc hm2 hik2; rw [hlc, hcm_e]
              exact fidCore_k_lt 33 (Nat.le_trans (Nat.le_of_lt hcid'_lt) hnc_le) hmv_lo hbge
            let cmeta := scrc[((4224 + 33 * mv + cid').setWidth 64).toNat]'hcm_lt
            c0_hsteps_nogrp
            refine wp_join_state (ts := [.bool])
              (α := Bool × List (BitVec 32)) (fun x => (x.1, ()))
              (fun x mk => FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) mk)
              (fun _ ⟨chgj, scrj⟩ mj ⟨hikj, hmj⟩ => by
                c0_hsteps!
                exact hLc cid'.toNat (chgj, cid', ()) mj (by
                  clear hQ hfin_p hLp hmp hikp hLc hmc hikc hikj hmj hm2 hik2
                  dsimp only [cid']; rw [hcid1]; omega)
                  ⟨scrj, hikj,
                    by clear hQ hfin_p hLp hmp hikp hLc hmc hikc hikj hmj hm2 hik2; omega,
                    rfl, hmj⟩)
              (fun Jc hJc => by
                c0_hsplit
                · have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := cid') hmv_hi (by decide)
                    (by clear hQ hfin_p hLp hmp hikp hLc hmc hikc hJc hm2 hik2; omega)
                  have hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat < scrc.length := by
                    clear hQ hfin_p hLp hmp hikp hLc hmc hikc hJc hm2 hik2; rw [hlc, hco_e]
                    exact fidCore_k_lt 29 (Nat.le_trans (Nat.le_of_lt hcid'_lt) hnc_le) hmv_lo hbge
                  let off := scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt
                  let sz := cmeta &&& 0xFFFF#32
                  have hsz_le : sz.toNat ≤ 65535 := m8_and_ffff_le cmeta
                  have hmv_c := fidCoreInv_mv h4214 hmv_eq hikc
                  have hnc_c : scrc[4193]?.getD 0#32 = nc := by
                    rw [hikc.2.2.1 4193 h4193 (Or.inl (by omega)), hnc_eq]
                  have hac_c : scrc[4207]?.getD 0#32 = acap := by
                    rw [hikc.2.2.1 4207 h4207 (Or.inl (by omega)), hac_eq]
                  have hcl_c := hikc.1.clause_ok (cid := cid'.toNat) (by rw [hnc_c]; exact hcid'_lt)
                  dsimp only at hcl_c; rw [hmv_c, hac_c] at hcl_c
                  have hoff_eq : (scrc[4224 + 29 * mv.toNat + cid'.toNat]?.getD 0#32) = off := by
                    rw [List.getElem?_eq_getElem (by
                      rw [hlc]; exact fidCore_k_lt 29 (Nat.le_trans (Nat.le_of_lt hcid'_lt) hnc_le)
                        hmv_lo hbge), Option.getD_some]
                    exact m8_k6_get_congr hco_e.symm _ _
                  have hcm_eq : (scrc[4224 + 33 * mv.toNat + cid'.toNat]?.getD 0#32) = cmeta := by
                    rw [List.getElem?_eq_getElem (by
                      rw [hlc]; exact fidCore_k_lt 33 (Nat.le_trans (Nat.le_of_lt hcid'_lt) hnc_le)
                        hmv_lo hbge), Option.getD_some]
                    exact m8_k6_get_congr hcm_e.symm _ _
                  rw [hoff_eq, hcm_eq, show (cmeta &&& 0xFFFF#32) = sz from rfl] at hcl_c
                  c0_hsteps_nogrp
                  exact fidCore_phase3_clause_wp Γ c s R Q X scr0 scrc cid chg_c Jc mc_m
                    h4214 h4192 h4193 h4207 hcid_pos hcid1 hcid'_lt hmv_lo hmv_hi hnc_le hnv_le
                    hlen_scr hcap_lt hbge hikc hcm_e hco_e hcm_lt hco_lt hsz_le hcl_c.1 hcl_c.2
                    hmc (fun x mj h1 h2 => hJc x mj ⟨h1, h2⟩)
                · c0_hsteps!; exact hJc (chg_c, scrc) mc_m ⟨hikc, hmc⟩)
          · c0_hsteps!
            exact hLp (if chg_c then nc.toNat - (pass + 1#32).toNat else 0) (pass + 1#32, chg_c, ())
              mc_m (by subst hchg_t; cases chg_c <;> simp [hp1] <;> omega)
              ⟨scrc, hikc, by omega, rfl, hmc⟩
        · intro Lc hLc; c0_hsteps!
          exact hLc nc.toNat (false, nc, ()) mp ⟨scrp, hikp, Nat.le_refl _, rfl, hmp⟩
      · c0_hsteps!; exact hfin_p
    · c0_hsteps!; exact hfin_p
  · intro Lp hLp; c0_hsteps!
    exact hLp nc.toNat (0#32, true, ()) m2 ⟨scr2, hik2, Nat.zero_le _, by simp, hm2⟩

/-! ## 2. `full_k6_core_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_k6_core_fid`, certifying `fidK6CoreSpec`. -/
theorem full_k6_core_fid_wp (Γ : Env) :
    ∀ a m Q X, fidK6CoreSpec a m Q X → Func.wp Γ full_k6_core_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6CoreSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have hlen_ge := hok.length_ge; have hlen_lt := hok.length_lt
  have h4214 : 4214 < scr0.length := by omega
  have h4193 : 4193 < scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  have h4207 : 4207 < scr0.length := by omega
  let mv := scr0[4214]'h4214; let nc := scr0[4193]'h4193
  let nv := scr0[4192]'h4192; let acap := scr0[4207]'h4207
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  have hmv_d : (scr0[4214]'h4214).toNat = mv.toNat := rfl
  have hnc_o : (scr0[(@OfNat.ofNat Nat 4193 _)]'h4193).toNat = nc.toNat := rfl
  have hnv_o : (scr0[(@OfNat.ofNat Nat 4192 _)]'h4192).toNat = nv.toNat := rfl
  have hacap_o : (scr0[(@OfNat.ofNat Nat 4207 _)]'h4207).toNat = acap.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  have hnc_eq : (scr0[4193]?.getD 0#32) = nc := m8_k6_get_eq h4193
  have hac_eq : (scr0[4207]?.getD 0#32) = acap := m8_k6_get_eq h4207
  rw [hmv_eq] at hmv_lo hmv_hi hbge hlen_ge; rw [hac_eq] at hlen_ge
  have hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length := hlen_ge
  have hcap_lt : scr0.length < 2 ^ 30 := hlen_lt
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q () m0 := hQ scr0 m0 hscr_len (fun _ _ _ => rfl) hok hm0
  let invS : Mem 64 → Prop := fun mj =>
    ∃ scrj : List (BitVec 32), FidCoreInv scr0 mv nc scrj ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj
  unfold Func.wp full_k6_core_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_noop
  · c0_hsplit
    · c0_hsteps!; exact hret_noop
    · c0_hsplit
      · c0_hsteps!; exact hret_noop
      · have hnc_le : nc.toNat ≤ 4 * mv.toNat := by fid_omega
        c0_hsplit
        · c0_hsteps!; exact hret_noop
        · have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
          have hinv0 : FidCoreInv scr0 mv nc scr0 :=
            ⟨hok, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32])
            (fun rem (i, ()) ml => ∃ scrl : List (BitVec 32),
              FidCoreInv scr0 mv nc scrl ∧ i.toNat ≤ nc.toNat ∧ rem = nc.toNat - i.toNat ∧
              (FullMem c (m8ScrSt s scrl) ⋆ R) ml) ?_ ?_
          · rintro L1 rem ⟨i, ⟨⟩⟩ ml hL1 ⟨scrl, hikl, hi_le, rfl, hml⟩
            have hll : scrl.length = scr0.length := hikl.2.1
            have hmin_l : 15744 ≤ scrl.length := by rw [hll]; exact hmin
            c0_hsplit
            · have hi_lt : i.toNat < nc.toNat := hc
              have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_bv32_add1_toNat hi_lt
                (by clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hml hikl; omega)
              have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := i) hmv_hi (by decide)
                (by clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hml hikl; omega)
              have hcm_lt : (((4224 : BitVec 32) + (33 : BitVec 32) * mv + i).setWidth 64).toNat <
                  scrl.length := by
                clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hml hikl; rw [hll, hcm_e]; omega
              c0_hsteps!
              exact hL1 (nc.toNat - (i + 1#32).toNat) (i + 1#32, ()) _
                (by clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hikl hm; omega)
                ⟨_, fidCoreInv_set_meta_pres h4214 hmv_eq hnc_le hikl hi_lt hcm_e hcm_lt
                  (m8_km_core_clear_pres _),
                  by clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hikl hm; omega, rfl, hm⟩
            · c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 32))
                (fun x => (x.1, ()))
                (fun x m2 => FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) m2)
                ?_ ?_
              · rintro _ ⟨_, scr2⟩ m2 ⟨hik2, hm2⟩
                c0_hsteps_nogrp
                exact fidCore_phase3_wp Γ c s R Q X scr0 scr2 m2 hmin hscr_len h4214 h4192
                  h4193 h4207 hmv_lo hmv_hi hnc_le hnv_le hlen_scr hcap_lt hbge hik2 hm2
                  (fun scr' m' h1 h2 h3 h4 =>
                    hQ scr' m' h1 (fun idx hi hor => by rw [hmv_eq] at hor; exact h2 idx hi hor)
                      h3 h4)
              · intro J2 hJ2
                clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1
                have h4199 : 4199 < scrl.length := by omega
                let inc := scrl[4199]'h4199
                have hinc_o : (scrl[(@OfNat.ofNat Nat 4199 _)]'h4199).toNat = inc.toNat := rfl
                c0_hsplit
                · have hinc_lt : inc.toNat < nc.toNat := hc
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i32])
                    (fun rem (i, ()) ma => ∃ scra : List (BitVec 32),
                      FidCoreInv scr0 mv nc scra ∧ i.toNat ≤ nv.toNat ∧ rem = nv.toNat - i.toNat ∧
                      (FullMem c (m8ScrSt s scra) ⋆ R) ma) ?_ ?_
                  · rintro La rem ⟨i, ⟨⟩⟩ ma hLa ⟨scra, hika, hi_le, rfl, hma⟩
                    have hla : scra.length = scr0.length := hika.2.1
                    c0_hsplit
                    · have hi_lt : i.toNat < nv.toNat := hc
                      have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                        m8_bv32_add1_toNat hi_lt (by omega)
                      have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := i)
                        hmv_hi (by decide) (by omega)
                      have hfl_b : ((4224 + 6 * mv + i).setWidth 64).toNat < scra.length := by
                        rw [hla, hfl_e]; omega
                      c0_hsteps!
                      exact hLa (nv.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
                        ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hika (by omega) hfl_e _,
                          by omega, rfl, hm⟩
                    · have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := inc)
                        hmv_hi (by decide) (by omega)
                      have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := inc)
                        hmv_hi (by decide) (by omega)
                      have hcm_b : ((4224 + 33 * mv + inc).setWidth 64).toNat < scra.length := by
                        rw [hla, hcm_e]; omega
                      have hco_b : ((4224 + 29 * mv + inc).setWidth 64).toNat < scra.length := by
                        rw [hla, hco_e]; omega
                      let meta_i := scra[((4224 + 33 * mv + inc).setWidth 64).toNat]'hcm_b
                      have hmeta_get : scra[4224 + 33 * mv.toNat + inc.toNat]'(by omega) = meta_i :=
                        m8_k6_get_congr hcm_e.symm (by omega) hcm_b
                      let scrb := scra.set (4224 + 33 * mv.toNat + inc.toNat)
                        (meta_i ||| 0x80000000#32)
                      have hikb : FidCoreInv scr0 mv nc scrb := by
                        have hpres := m8_km_core_or_pres meta_i
                        refine fidCoreInv_set_meta h4214 hmv_eq hnc_le hika hinc_lt ?_ ?_
                        · rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hmeta_get]
                          exact hpres.1
                        · rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hmeta_get]
                          exact hpres.2
                      have hlb : scrb.length = scr0.length := hikb.2.1
                      have hmv_b := fidCoreInv_mv h4214 hmv_eq hikb
                      have hnc_b : scrb[4193]?.getD 0#32 = nc := by
                        rw [hikb.2.2.1 4193 h4193 (Or.inl (by omega)), hnc_eq]
                      have hac_b : scrb[4207]?.getD 0#32 = acap := by
                        rw [hikb.2.2.1 4207 h4207 (Or.inl (by omega)), hac_eq]
                      have hcl_b := hikb.1.clause_ok (cid := inc.toNat)
                        (by rw [hnc_b]; exact hinc_lt)
                      dsimp only at hcl_b; rw [hmv_b, hac_b] at hcl_b
                      c0_hsteps_nogrp
                      replace hm : (FullMem c (m8ScrSt s scrb) ⋆ R) m := by
                        dsimp only [scrb]; rw [← hcm_e]; exact hm
                      refine wp_join0 invS ?_ ?_
                      · rintro _ mb ⟨scrm, hikm, hmb⟩
                        clear hLa hika hikb hcl_b hm hml hikl hmeta_get
                          hmv_b hnc_b hac_b hco_b hcm_b hco_e hcm_e hlb scrb meta_i hla hll
                        have hlm : scrm.length = scr0.length := hikm.2.1
                        have hmin_m : 15744 ≤ scrm.length := by omega
                        c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                          (fun ti => (ti, ())) (fun ti => ti.toNat ≤ mv.toNat) ?_ ?_
                        · intro _ ti0 hti0
                          c0_hsteps_nogrp
                          exact fidCore_phase2_trace_wp Γ c s R Q X scr0 scrm ti0
                            (fun y => J2 (y.1, ())) mb hmin h4214 h4192 h4193 h4207 hmv_lo
                            hmv_hi hnc_le hnv_le hbge hti0 hikm hmb
                            (fun x scrf mf hikf hmf => hJ2 (x, scrf) mf ⟨hikf, hmf⟩)
                        · intro Jti hJti; c0_hsplit
                          · c0_hsteps!; exact hJti mv (Nat.le_refl _)
                          · c0_hsteps!; exact hJti _ (Nat.le_of_not_lt hc)
                      · intro Jm hJm
                        clear hLa hml hikl hJ2
                        have hco_b2 : ((4224 + 29 * mv + inc).setWidth 64).toNat < scrb.length := by
                          rw [hlb, hco_e]
                          exact fidCore_k_lt 29 (Nat.le_trans (Nat.le_of_lt hinc_lt) hnc_le)
                            hmv_lo hbge
                        have hcm_b2 : ((4224 + 33 * mv + inc).setWidth 64).toNat < scrb.length := by
                          rw [hlb, hcm_e]
                          exact fidCore_k_lt 33 (Nat.le_trans (Nat.le_of_lt hinc_lt) hnc_le)
                            hmv_lo hbge
                        let off_i := scrb[((4224 + 29 * mv + inc).setWidth 64).toNat]'hco_b2
                        let sz_i :=
                          (scrb[((4224 + 33 * mv + inc).setWidth 64).toNat]'hcm_b2) &&& 0xFFFF#32
                        have hszi_le : sz_i.toNat ≤ 65535 := m8_and_ffff_le _
                        have hszi_bnd : off_i.toNat + sz_i.toNat ≤ acap.toNat :=
                          (fidCore_clause_ok_bnds
                            h4214 hmv_eq h4193 hnc_eq h4207 hac_eq hmv_hi hnc_le
                            hikb hinc_lt hco_e hcm_e hco_b2 hcm_b2).1
                        c0_hsplit
                        · try clear hc
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i32])
                            (fun rem_j (j, ()) mj => ∃ scrj : List (BitVec 32),
                              FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ sz_i.toNat ∧
                              rem_j = sz_i.toNat - j.toNat ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj)
                            ?_ ?_
                          · rintro Lj rem_j ⟨j, ⟨⟩⟩ mj hLj ⟨scrj, hikj, hj_le, rfl, hmj⟩
                            clear hikb hm hmv_b hnc_b hac_b
                            have hlj : scrj.length = scr0.length := hikj.2.1
                            c0_hsplit
                            · have hj_lt : j.toNat < sz_i.toNat := by
                                have hc' := hc; fid_norm_ofnat
                                simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
                                have hcm_u4 : 4224 + 33 * mv.toNat + (scrl[4199]'h4199).toNat <
                                    4294967296 := by clear hc hc' hLj hikj hcl_b hJm; omega
                                have hcm_eq_i : (4224 + 33 * (scr0[4214]'h4214).toNat +
                                      (scrl[4199]'h4199).toNat) % 4294967296 =
                                      4224 + 33 * mv.toNat + (scrl[4199]'h4199).toNat := by
                                  rw [hmv_d, Nat.mod_eq_of_lt hcm_u4]
                                have hc1 := fidCore_p4_hc_rw hcm_eq_i
                                  (hb1' := by
                                    clear hc hc' hLj hikj hcl_b
                                    rw [show scrl[4199]'h4199 = inc from rfl, ← hcm_e]; exact hcm_b)
                                  (hb2' := by
                                    clear hc hc' hLj hikj hcl_b; rw [List.length_set]
                                    rw [show scrl[4199]'h4199 = inc from rfl, ← hcm_e]; exact hcm_b)
                                  hc'
                                have hidx_lt : 4224 + 33 * mv.toNat + inc.toNat < scra.length := by
                                  rw [hla]; clear hc hc' hLj hikj hcl_b hJm; omega
                                have hidx_lt' :
                                    4224 + 33 * mv.toNat + (scrl[4199]'h4199).toNat <
                                      scra.length :=
                                  hidx_lt
                                have hset_l : (scra.set (4224 + 33 * mv.toNat +
                                      (scrl[4199]'h4199).toNat)
                                      (scra[4224 + 33 * mv.toNat +
                                        (scrl[4199]'h4199).toNat]'hidx_lt' ||| 2147483648#32))[
                                      4224 + 33 * mv.toNat + (scrl[4199]'h4199).toNat]? =
                                    some (meta_i ||| 2147483648#32) := by
                                  rw [List.getElem?_set_self hidx_lt', Option.some_inj]
                                  exact congrArg (· ||| 2147483648#32) hmeta_get
                                have hset_r : scrb[((4224 + 33 * mv + inc).setWidth
                                    64).toNat]? = some (meta_i ||| 2147483648#32) := by
                                  dsimp only [scrb]; rw [hcm_e]
                                  exact List.getElem?_set_self hidx_lt
                                have hmeta_e :
                                    ((scra.set (4224 + 33 * mv.toNat + (scrl[4199]'h4199).toNat)
                                        (scra[4224 + 33 * mv.toNat +
                                          (scrl[4199]'h4199).toNat]'hidx_lt' ||| 2147483648#32))[
                                        4224 + 33 * mv.toNat + (scrl[4199]'h4199).toNat]'(by
                                          rw [List.length_set]; exact hidx_lt')).toNat %
                                      65536 = sz_i.toNat := by
                                  have hset_eq :
                                      (scra.set (4224 + 33 * mv.toNat +
                                          (scrl[4199]'h4199).toNat)
                                          (scra[4224 + 33 * mv.toNat +
                                            (scrl[4199]'h4199).toNat]'hidx_lt' |||
                                            2147483648#32))[
                                          4224 + 33 * mv.toNat + (scrl[4199]'h4199).toNat]'(by
                                            rw [List.length_set]; exact hidx_lt') =
                                        scrb[((4224 + 33 * mv + inc).setWidth
                                          64).toNat]'hcm_b2 := by
                                    rw [← Option.some_inj, ← List.getElem?_eq_getElem,
                                      ← List.getElem?_eq_getElem, hset_l, hset_r]
                                  dsimp only [sz_i]; rw [fid_bv32_and_ffff_toNat, hset_eq]
                                rw [hmeta_e] at hc1
                                exact hc1
                              have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                                m8_bv32_add1_toNat hj_lt (by clear hLj hikj hcl_b hJm; omega)
                              have har_e := fid_k6_off_add2 (mv := mv) (k := 45)
                                (x := off_i) (y := j) hmv_hi (by decide)
                                (by clear hLj hikj hcl_b hJm; omega)
                              have har_b : ((4224 + 45 * mv + off_i + j).setWidth 64).toNat <
                                  scrj.length := by clear hLj hikj hcl_b hJm; rw [hlj, har_e]; omega
                              let lv := (scrj[((4224 + 45 * mv + off_i + j).setWidth 64).toNat]'
                                har_b) >>> (1 : Nat)
                              have hoff_raw_g : ∀ {hb_a1 hb_a2 hb_a3 hb_b1 hb_b2 hb_b3 hb_c hb_d},
                                  (scra.set (((4224 : BitVec 32) + (33 : BitVec 32) *
                                      (scr0[4214]'hb_a1) + (scrl[4199]'hb_b1)).setWidth 64).toNat
                                      ((scra[((4224 : BitVec 32) + (33 : BitVec 32) *
                                        (scr0[4214]'hb_a2) + (scrl[4199]'hb_b2)).setWidth
                                        64 |>.toNat]'hb_c) ||| 2147483648#32))[
                                      ((4224 : BitVec 32) + (29 : BitVec 32) *
                                      (scr0[4214]'hb_a3) + (scrl[4199]'hb_b3)).setWidth
                                      64 |>.toNat]'hb_d = off_i := by
                                intro hb_a1 hb_a2 hb_a3 hb_b1 hb_b2 hb_b3 hb_c hb_d
                                rw [← Option.some_inj, ← List.getElem?_eq_getElem,
                                  ← List.getElem?_eq_getElem, List.getElem?_set_ne (by
                                    change ((4224 + 33 * mv + inc).setWidth 64).toNat ≠
                                      ((4224 + 29 * mv + inc).setWidth 64).toNat
                                    rw [hcm_e, hco_e]; clear hLj hikj hcl_b hJm; omega)]
                                dsimp only [off_i, scrb]
                                rw [List.getElem?_set_ne (by
                                  rw [hco_e]; clear hLj hikj hcl_b hJm; omega)]
                              conv =>
                                arg 4; arg 1; arg 2; arg 2; arg 1; arg 1
                                tactic => exact hoff_raw_g
                              c0_hsteps_nogrp
                              refine wp_join0 invS
                                (fun _ mj' ⟨scrj', hikj', hmj'⟩ => by
                                  c0_hsteps!
                                  exact hLj (sz_i.toNat - (j + 1#32).toNat) (j + 1#32, ()) mj'
                                    (by clear hLj hikj' hmj' hmj hikj; omega)
                                    ⟨scrj', hikj', by clear hLj hikj' hmj' hmj hikj; omega, rfl,
                                      hmj'⟩)
                                (fun Js hJs => by
                                  c0_hsplit
                                  · have hlv_lt : lv.toNat < nv.toNat := by
                                      first
                                      | exact hc
                                      | (have hc' := hc; clear hc; fid_norm_ofnat
                                         simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
                                         exact fidCore_p4_hlv_off h4214 rfl h4192 rfl har_e har_b
                                           rfl hc')
                                    have hfl_lv := fid_k6_off_add (mv := mv) (k := 6) (x := lv)
                                      hmv_hi (by decide) (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le
                                        hlv_lt hnv_le) (Nat.le_trans hmv_hi (by decide)))
                                    have hfl_lvb : ((4224 + 6 * mv + lv).setWidth 64).toNat <
                                        scrj.length := by
                                      rw [hlj, hfl_lv]
                                      exact fidCore_b6_lt (Nat.lt_of_lt_of_le hlv_lt hnv_le) hbge
                                    c0_hsteps!
                                    exact hJs _ ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hikj
                                      (Nat.lt_of_lt_of_le hlv_lt hnv_le) hfl_lv _, hm⟩
                                  · c0_hsteps!; exact hJs _ ⟨scrj, hikj, hmj⟩)
                            · c0_hsteps!; exact hJm mj ⟨scrj, hikj, hmj⟩
                          · intro Lj hLj; c0_hsteps!
                            exact hLj sz_i.toNat (0#32, ()) _
                              ⟨scrb, hikb, Nat.zero_le _, by simp, hm⟩
                        · c0_hsteps!; exact hJm _ ⟨scrb, hikb, hm⟩
                  · intro La hLa; c0_hsteps!
                    exact hLa nv.toNat (0#32, ()) ml ⟨scrl, hikl, Nat.zero_le _, by simp, hml⟩
                · c0_hsteps!; exact hJ2 (_, scrl) ml ⟨hikl, hml⟩
          · intro L1 hL1; c0_hsteps!
            exact hL1 nc.toNat (0#32, ()) m0 ⟨scr0, hinv0, Nat.zero_le _, by simp, hm0'⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
