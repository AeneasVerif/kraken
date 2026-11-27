/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof3a
public import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step 13 S5 `full_probe_m6` — `initial` Path & Top-Level Spec (`Proof3b`)

Proves `full_probe_m6_init_core` (`initial = true`) and `full_probe_m6_s5_wp` satisfying
`FullM6Orch.m6ProbeSpec` (`<= 390` lines per decl, `< 1,400` LOC, `<= 100` cols).
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open FullArenaTactics
open scoped FullArenaTactics FullM6Hdr.M6HdrTactics FullM6ProofUtil.M6ProofUtilTactics

private theorem s5_probe_init_tail_ret1 {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {saved_prob : Val i64} {ext1 : List (BitVec 64)} {s1 : FullState} {m1 : Mem 64}
    (henv : S5ProbeEnv Γ) (hinv1 : S5ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : S5ProbeQ c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_update_classify_fid"
        (Arg.var c.hdr, ()) fun _ =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
          s5RetWmExpr c saved_prob 1#64) Blocks.nil) fun Js =>
        Expr.jnz (Arg.var (true : Val .bool)) (Expr.jump Js.fst ())
          (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 984, ())) fun p =>
          Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.call (as := [i64, i64]) (bs := [i64]) "f64u_nlogpown"
            (Arg.var ld, Arg.imm 1, ()) fun p_1 =>
          Expr.call (as := [i64, i64]) (bs := [i64]) "f64u_mul"
            (Arg.imm 4636737291354636288, Arg.var p_1.fst, ()) fun p_2 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p_3 =>
          Expr.load i64 (Arg.var p_3.fst) fun ld_1 =>
          Expr.call (as := [i64]) (bs := [i64]) "f64u_to_u64" (Arg.var p_2.fst, ()) fun p_4 =>
          Expr.call (as := [i64, i64]) (bs := [i64]) "full_scale_delta_m5"
            (Arg.var c.hdr, Arg.var p_4.fst, ()) fun p_5 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var ld_1, Arg.var p_5.fst, ())) fun p_6 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 976, ())) fun p_7 =>
          Expr.store (t := i64) (Arg.var p_6.fst) (Arg.var p_7.fst) (Expr.jump Js.fst ()))) m1 := by
  obtain ⟨hinv, hcl, hfu, hm⟩ := hinv1
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.updCls _ _ _ _ h) hinv.cfgOk hinv.extOk
    hinv.sparse.lengths hm fun _ extU sU mU hcU hlU hmsU hextU _ hmU => ?_
  have hinvU := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlU hcU hmsU) hextU
  have hclU : sU.core.cur_level = 0 := by rw [hcU]; exact hcl
  have hfuU : sU.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcU]; exact hfu
  refine wp_join_group (ts := []) (fun _ mF => ∃ extF sF, S5ProbeStateInv c F0 s R extF sF mF)
    (fun _ _ mF ⟨extF, sF, hinvF, hclF, hfuF, hmF⟩ =>
      s5_probe_ret_wm henv hinvF.cfgOk hinvF.extOk hinvF.sparse.lengths hfuF
        (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinvF, hclF⟩) hmF hQ)
    (fun JF hJF => by
      c0_hfast_nogrp
      · exact hJF () mU ⟨extU, sU, hinvU, hclU, hfuU, hmU⟩
      · cases ‹true = false›)

private theorem s5_probe_init_cong {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s0 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {ext0 : List (BitVec 64)} {m0 : Mem 64} {saved_prob : Val i64}
    (henv : S5ProbeEnv Γ) (hinv0 : S5ProbeStateInv c F0 s R ext0 s0 m0) (hQ : S5ProbeQ c F0 s R Q)
    (JC : Cont [.bool])
    (hJC : ∀ subst_c mC, (∃ extC sC, S5ProbeStateInv c F0 s R extC sC mC) →
      JC (subst_c, ()) mC) :
    wp Γ Q X (Expr.call (as := [i64, i64]) (bs := [.bool]) "m6_hdr_delaying"
        (Arg.var c.hdr, Arg.imm 1, ()) fun p_8 =>
      Expr.jnz (Arg.var p_8.fst) (Expr.jump JC (Arg.imm true, ()))
        (Expr.group (sig := [[.bool]]) (fun _ => Blocks.cons (fun p =>
            Expr.jump JC (Arg.var p.fst, ())) Blocks.nil) fun JC' =>
          Expr.call (as := [i64]) (bs := [.bool]) "full_enter_dense" (Arg.var c.hdr, ()) fun p_9 =>
          Expr.jnz (Arg.var p_9.fst)
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1072, ())) fun p_10 =>
            Expr.load i64 (Arg.var p_10.fst) fun ld_1 =>
            Expr.call (as := [i64, i64]) (bs := [i64]) "full_congruence_dense"
              (Arg.var c.hdr, Arg.imm 18446744073709551615, ()) fun p_11 =>
            Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_11.fst, Arg.imm 20, ()))
              fun p_12 =>
            Expr.jnz (Arg.var p_12.fst)
              (Expr.call (as := [i64]) (bs := []) "full_dense_bin_roundtrip_fid"
                (Arg.var c.hdr, ()) fun _ =>
              Expr.call (as := [i64]) (bs := [i64]) "full_rebuild_watches_nosort_fid"
                (Arg.var c.hdr, ()) fun _ => s5RetWmExpr c saved_prob 20#64)
              (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1072, ())) fun p_13 =>
              Expr.load i64 (Arg.var p_13.fst) fun ld_2 =>
              Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                  Expr.call (as := [i64]) (bs := []) "full_dense_bin_roundtrip_fid"
                    (Arg.var c.hdr, ()) fun _ =>
                  s5Reb20Expr c saved_prob (Expr.group (sig := [[.bool]]) (fun _ =>
                      Blocks.cons (fun p => Expr.jump JC'.fst (Arg.var p.fst, ())) Blocks.nil)
                    fun Jcb =>
                    Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
                        (Arg.var ld_2, Arg.var ld_1, ())) fun p_18 =>
                    Expr.jnz (Arg.var p_18.fst)
                      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 504, ())) fun p_19 =>
                      Expr.load i64 (Arg.var p_19.fst) fun ld_3 =>
                      Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
                          (Arg.var ld_3, Arg.imm 0, ())) fun p_20 =>
                      Expr.jnz (Arg.var p_20.fst)
                        (Expr.call (as := [i64]) (bs := [i64]) "full_substitute"
                            (Arg.var c.hdr, ()) fun p_21 =>
                          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                              (Arg.var p_21.fst, Arg.imm 20, ())) fun p_22 =>
                          Expr.jnz (Arg.var p_22.fst) (s5RetWmExpr c saved_prob 20#64)
                            (Expr.jump Jcb.fst (Arg.imm false, ())))
                        (Expr.jump Jcb.fst (Arg.imm false, ())))
                      (Expr.jump Jcb.fst (Arg.imm true, ())))) Blocks.nil)
                fun JDl =>
                Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                    Expr.call (as := [i64, i64]) (bs := []) "m6_hdr_bump_delay"
                      (Arg.var c.hdr, Arg.imm 1, ()) fun _ => Expr.jump JDl.fst ()) Blocks.nil)
                  fun JDb =>
                  Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
                      (Arg.var ld_2, Arg.var ld_1, ())) fun p_14 =>
                  Expr.jnz (Arg.var p_14.fst)
                    (Expr.let_ (Op.mk (.sub i64) (Arg.var ld_2, Arg.var ld_1, ())) fun p_15 =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var p_15.fst, Arg.imm 1000, ())) fun p_16 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 792, ())) fun p_17 =>
                    Expr.load i64 (Arg.var p_17.fst) fun ld_u =>
                    Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl)
                        (Arg.var p_16.fst, Arg.var ld_u, ())) fun p_18 =>
                    Expr.jnz (Arg.var p_18.fst)
                      (Expr.call (as := [i64, i64]) (bs := []) "m6_hdr_reduce_delay"
                        (Arg.var c.hdr, Arg.imm 1, ()) fun _ => Expr.jump JDl.fst ())
                      (Expr.jump JDb.fst ()))
                    (Expr.jump JDb.fst ())))
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) fun p_10 =>
            Expr.load i64 (Arg.var p_10.fst) fun ld_1 =>
            Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var ld_1, Arg.imm 0, ())) fun p_11 =>
            Expr.jnz (Arg.var p_11.fst) (s5RetWmExpr c saved_prob 20#64)
              (Expr.jump JC'.fst (Arg.imm true, ()))))) m0 := by
  obtain ⟨hinv0', hcl0, hfu0, hm0⟩ := hinv0
  refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.delay _ _ _ _ h) hinv0'.cfgOk hinv0'.extOk
    hinv0'.sparse.lengths (fullM6HdrMem_unfocus hm0f)
    fun ⟨delC, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
  have hinvCd := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv0' hlCd hcCd hmsCd) hextCd
  have hclCd : sCd.core.cur_level = 0 := by rw [hcCd]; exact hcl0
  have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcCd]; exact hfu0
  c0_hfast_nogrp
  · exact hJC true mCd ⟨extCd, sCd, hinvCd, hclCd, hfuCd, hmCd⟩
  · refine wp_join_group (ts := [.bool])
      (fun p mC' => ∃ extC' sC', S5ProbeStateInv c F0 s R extC' sC' mC')
      (fun _ ⟨sc, ⟨⟩⟩ mC' hC' => by c0_hfast_nogrp; exact hJC sc mC' hC')
      fun JC' hJC' => ?_
    refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
    c0_call henv.enter
    refine ⟨c, F0, extCd, sCd, R, rfl, hinvCd.cfgOk, hinvCd.extOk, hinvCd.sparse.lengths,
      hinvCd.sparse.1, hinvCd.sparse.2.1, hinvCd.sparse.2.2.1, hinvCd.sparse.2.2.2.1,
      (fun hdm => absurd hinvCd.sparse.2.2.2.2 hdm), fullM6HdrMem_unfocus hmCdf,
      fun okE extE sE mE _ hextE _ hlenE hlmE hndE hesE _ hfuE hdenE hspE hmE => ?_⟩
    have hfuE' := Nat.le_trans hfuE hfuCd
    c0_hfast_nogrp
    · have hdenE' := hdenE ‹okE = true›
      refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
      c0_hfast_nogrp; c0_call henv.cong
      refine ⟨c, F0, sE, m6ExtMem (m6ExtAddr c.hdr) extE ⋆ R, rfl, hdenE', hmEf,
        fun rC sC mC hdenC _ hfuC _ huC hmC => ?_⟩
      have hfuC' := Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat hfuC)) hfuE'
      c0_hfast_nogrp
      · refine s5_probe_bin_rt henv hdenC (fullM6HdrMem_unfocus hmC)
          fun sRt mRt hdenRt hfuRt hmRt => ?_
        c0_call henv.rebNosort
        refine ⟨c, F0, extE, sRt, R, rfl, hinvCd.cfgOk, hextE, hdenRt, hmRt,
          fun _ extR sR mR hinvR _ hfuR _ _ hmR => ?_⟩
        exact s5_probe_ret_wm henv hinvR.cfgOk hinvR.extOk hinvR.sparse.lengths
          (Nat.le_trans hfuR (by rw [hfuRt]; exact hfuC')) (Or.inr rfl)
          (fun _ => huC ‹_›) (fun h => by cases h) hmR hQ
      · have hmC' := fullM6HdrMem_unfocus hmC
        refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
            M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧ sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
        · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
          try dsimp only [Blocks.get_here]
          refine s5_probe_bin_rt henv hdenDl hmDl fun sRt mRt hdenRt hfuRt hmRt => ?_
          refine s5_probe_reb20 henv hinvCd.cfgOk hextDl hdenRt (by rw [hfuRt]; exact hfuDl) hmRt
            hQ fun extR sR mR hinvR => ?_
          refine wp_join_group (ts := [.bool])
            (fun _ mcb => ∃ extcb scb, S5ProbeStateInv c F0 s R extcb scb mcb)
            (fun _ ⟨scb, ⟨⟩⟩ mcb hcb => by c0_hfast_nogrp; exact hJC' (scb, ()) mcb hcb)
            fun Jcb hJcb => ?_
          c0_hfast_nogrp
          · exact s5_probe_subst_if henv hinvR hQ fun extS sS mS hS => by
              c0_hfast_nogrp; exact hJcb (false, ()) mS ⟨extS, sS, hS⟩
          · exact hJcb (true, ()) mR ⟨extR, sR, hinvR⟩
        · intro JDl hJDl
          c0_hfast_nogrp
          refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
              M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧ sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
          · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
            try dsimp only [Blocks.get_here]
            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.bumpD _ _ _ _ h) hinvCd.cfgOk hextDl
              hdenDl.lengths hmDl fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
            exact hJDl () mDl' ⟨extDl', sDl', hextDl',
              fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres, by rw [hcDl]; exact hfuDl,
              hmDl'⟩
          · intro JDb hJDb
            refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
            c0_hfast_nogrp
            · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.redD _ _ _ _ h) hinvCd.cfgOk hextE
                hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
              exact hJDl () mDl ⟨extDl, sDl, hextDl,
                fullDenseInv_of_core_eq hdenC hlDl hcDl hmsDl.extPres, by rw [hcDl]; exact hfuC',
                hmDl⟩
            all_goals
              exact hJDb () mC ⟨extE, sC, hextE, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
    · have hinvE := FullM6HdrInv.mk_inv hinvCd.cfgOk hextE (hspE ‹okE = false›).1
      refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
      c0_hfast_nogrp
      · exact s5_probe_ret_wm henv hinvE.cfgOk hextE hinvE.sparse.lengths hfuE' (Or.inr rfl)
          (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›) (fun h => by cases h)
          (fullM6HdrMem_unfocus hmEf) hQ
      · exact hJC' (true, ()) mE ⟨extE, sE, hinvE, (hspE ‹okE = false›).2, hfuE',
          fullM6HdrMem_unfocus hmEf⟩

private theorem s5_probe_init_sweep {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s0 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {ext0 : List (BitVec 64)} {m0 : Mem 64} {saved_prob dticks : Val i64} {subst_c : Val .bool}
    (henv : S5ProbeEnv Γ) (hinv0 : S5ProbeStateInv c F0 s R ext0 s0 m0) (hQ : S5ProbeQ c F0 s R Q)
    (JSw : Cont [.bool])
    (hJSw : ∀ subst_sw mSw, (∃ extSw sSw, S5ProbeStateInv c F0 s R extSw sSw mSw) →
      JSw (subst_sw, ()) mSw) :
    wp Γ Q X (Expr.call (as := [i64, i64]) (bs := [.bool]) "m6_hdr_delaying"
        (Arg.var c.hdr, Arg.imm 2, ()) fun p_10 =>
      Expr.jnz (Arg.var p_10.fst) (Expr.jump JSw (Arg.var subst_c, ()))
        (Expr.group (sig := [[.bool]]) (fun _ => Blocks.cons (fun p =>
            Expr.jump JSw (Arg.var p.fst, ())) Blocks.nil) fun JSw' =>
          Expr.call (as := [i64]) (bs := [.bool]) "full_enter_dense" (Arg.var c.hdr, ()) fun p_11 =>
          Expr.jnz (Arg.var p_11.fst)
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 432, ())) fun p_12 =>
            Expr.load i64 (Arg.var p_12.fst) fun ld_1 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 32, ())) fun p_13 =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var p_13.fst, Arg.imm 4, ())) fun p_14 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var ld_1, Arg.var p_14.fst, ())) fun p_15 =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p_15.fst)
              (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1080, ())) fun p_16 =>
              Expr.load i64 (Arg.var p_16.fst) fun ld_2 =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p_17 =>
              Expr.load i64 (Arg.var p_17.fst) fun ld_3 =>
              Expr.let_ (Op.mk (.udiv 64) (Arg.var dticks, Arg.imm 10, ())) fun p_18 =>
              Expr.call (as := [i64, i64, i64]) (bs := [i64]) "full_sweep_dense_m6"
                (Arg.var c.hdr, Arg.var ld_3, Arg.var p_18.fst, ()) fun p_19 =>
              Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_19.fst, Arg.imm 20, ()))
                fun p_20 =>
              Expr.jnz (Arg.var p_20.fst)
                (Expr.call (as := [i64]) (bs := [i64]) "full_rebuild_watches_nosort_fid"
                  (Arg.var c.hdr, ()) fun _ => s5RetWmExpr c saved_prob 20#64)
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1080, ())) fun p_21 =>
                Expr.load i64 (Arg.var p_21.fst) fun ld_4 =>
                Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 32, ())) fun p_22 =>
                Expr.let_ (Op.mk (.mul i64) (Arg.var p_22.fst, Arg.imm 4, ())) fun p_23 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var ld_1, Arg.var p_23.fst, ())) fun p_24 =>
                Expr.load i32 (Arg.var p_24.fst) fun ld_5 =>
                Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_5, ())) fun p_25 =>
                Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                    s5Reb20Expr c saved_prob (Expr.group (sig := [[.bool]]) (fun _ =>
                        Blocks.cons (fun p => Expr.jump JSw'.fst (Arg.var p.fst, ())) Blocks.nil)
                      fun Jsb =>
                      Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
                          (Arg.var ld_4, Arg.var ld_2, ())) fun p_29 =>
                      Expr.jnz (Arg.var p_29.fst)
                        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 504, ())) fun p_30 =>
                        Expr.load i64 (Arg.var p_30.fst) fun ld_6 =>
                        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
                            (Arg.var ld_6, Arg.imm 0, ())) fun p_31 =>
                        Expr.jnz (Arg.var p_31.fst)
                          (Expr.call (as := [i64]) (bs := [i64]) "full_substitute"
                              (Arg.var c.hdr, ()) fun p_32 =>
                            Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                                (Arg.var p_32.fst, Arg.imm 20, ())) fun p_33 =>
                            Expr.jnz (Arg.var p_33.fst) (s5RetWmExpr c saved_prob 20#64)
                              (Expr.jump Jsb.fst (Arg.imm false, ())))
                          (Expr.jump Jsb.fst (Arg.imm false, ())))
                        (Expr.jump Jsb.fst (Arg.var subst_c, ())))) Blocks.nil)
                  fun JDl =>
                  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                      Expr.call (as := [i64, i64]) (bs := []) "m6_hdr_bump_delay"
                        (Arg.var c.hdr, Arg.imm 2, ()) fun _ => Expr.jump JDl.fst ()) Blocks.nil)
                    fun JDb =>
                    Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
                        (Arg.var ld_4, Arg.var ld_2, ())) fun p_26 =>
                    Expr.jnz (Arg.var p_26.fst)
                      (Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
                          (Arg.var p_25.fst, Arg.imm 0, ())) fun p_27 =>
                      Expr.jnz (Arg.var p_27.fst)
                        (Expr.let_ (Op.mk (.sub i64) (Arg.var ld_4, Arg.var ld_2, ())) fun p_28 =>
                        Expr.let_ (Op.mk (.mul i64) (Arg.var p_28.fst, Arg.imm 1000, ()))
                          fun p_29 =>
                        Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl)
                            (Arg.var p_29.fst, Arg.var p_25.fst, ())) fun p_30 =>
                        Expr.jnz (Arg.var p_30.fst)
                          (Expr.call (as := [i64, i64]) (bs := []) "m6_hdr_reduce_delay"
                            (Arg.var c.hdr, Arg.imm 2, ()) fun _ => Expr.jump JDl.fst ())
                          (Expr.jump JDb.fst ()))
                        (Expr.jump JDb.fst ()))
                      (Expr.jump JDb.fst ()))))
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) fun p_12 =>
            Expr.load i64 (Arg.var p_12.fst) fun ld_1 =>
            Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var ld_1, Arg.imm 0, ())) fun p_13 =>
            Expr.jnz (Arg.var p_13.fst) (s5RetWmExpr c saved_prob 20#64)
              (Expr.jump JSw'.fst (Arg.var subst_c, ()))))) m0 := by
  obtain ⟨hinv0', hcl0, hfu0, hm0⟩ := hinv0
  refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.delay _ _ _ _ h) hinv0'.cfgOk hinv0'.extOk
    hinv0'.sparse.lengths (fullM6HdrMem_unfocus hm0f)
    fun ⟨delSw, ⟨⟩⟩ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
  have hinvSd := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv0' hlSd hcSd hmsSd) hextSd
  have hclSd : sSd.core.cur_level = 0 := by rw [hcSd]; exact hcl0
  have hfuSd : sSd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcSd]; exact hfu0
  c0_hfast_nogrp
  · exact hJSw subst_c mSd ⟨extSd, sSd, hinvSd, hclSd, hfuSd, hmSd⟩
  · refine wp_join_group (ts := [.bool])
      (fun _ mSw' => ∃ extSw' sSw', S5ProbeStateInv c F0 s R extSw' sSw' mSw')
      (fun _ ⟨sc, ⟨⟩⟩ mSw' hSw' => by c0_hfast_nogrp; exact hJSw sc mSw' hSw')
      fun JSw' hJSw' => ?_
    refine wp_m6Hdr_focus_frame hmSd fun hmSdf => ?_
    c0_call henv.enter
    refine ⟨c, F0, extSd, sSd, R, rfl, hinvSd.cfgOk, hinvSd.extOk, hinvSd.sparse.lengths,
      hinvSd.sparse.1, hinvSd.sparse.2.1, hinvSd.sparse.2.2.1, hinvSd.sparse.2.2.2.1,
      (fun hdm => absurd hinvSd.sparse.2.2.2.2 hdm), fullM6HdrMem_unfocus hmSdf,
      fun okE extE sE mE _ hextE _ hlenE hlmE hndE hesE _ hfuE hdenE hspE hmE => ?_⟩
    have hfuE' := Nat.le_trans hfuE hfuSd
    c0_hfast_nogrp
    · have hdenE' := hdenE ‹okE = true›
      have hgu_len : 32 < sE.scratch.glue_used.length := by
        rw [hlenE.scratch_ok.glue_used_len]; decide
      refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
      c0_hfast_nogrp
      have hdenEz := s5Dense_zero_gu32 hdenE'
      c0_call henv.sweepD
      refine ⟨c, F0, _, m6ExtMem (m6ExtAddr c.hdr) extE ⋆ R, rfl, hdenEz, by assumption,
        fun rSw sSw mSw hdenSw _ hfuSw _ huSw hmSw => ?_⟩
      have hfuSw' := Nat.le_trans hfuSw hfuE'
      c0_hfast_nogrp
      · c0_call henv.rebNosort
        refine ⟨c, F0, extE, sSw, R, rfl, hinvSd.cfgOk, hextE, hdenSw,
          fullM6HdrMem_unfocus hmSw, fun _ extR sR mR hinvR _ hfuR _ _ hmR => ?_⟩
        exact s5_probe_ret_wm henv hinvR.cfgOk hinvR.extOk hinvR.sparse.lengths
          (Nat.le_trans hfuR hfuSw') (Or.inr rfl) (fun _ => huSw ‹_›)
          (fun h => by cases h) hmR hQ
      · have hgu_len' : 32 < sSw.scratch.glue_used.length := by
          rw [hdenSw.lengths.scratch_ok.glue_used_len]; decide
        c0_hfast_nogrp
        have hmSw' := fullM6HdrMem_unfocus (by assumption)
        refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
            M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧ sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
        · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
          try dsimp only [Blocks.get_here]
          refine s5_probe_reb20 henv hinvSd.cfgOk hextDl hdenDl hfuDl hmDl hQ
            fun extR sR mR hinvR => ?_
          refine wp_join_group (ts := [.bool])
            (fun _ msb => ∃ extsb ssb, S5ProbeStateInv c F0 s R extsb ssb msb)
            (fun _ ⟨scb, ⟨⟩⟩ msb hsb => by c0_hfast_nogrp; exact hJSw' (scb, ()) msb hsb)
            fun Jsb hJsb => ?_
          c0_hfast_nogrp
          · exact s5_probe_subst_if henv hinvR hQ fun extS sS mS hS => by
              c0_hfast_nogrp; exact hJsb (false, ()) mS ⟨extS, sS, hS⟩
          · exact hJsb (subst_c, ()) mR ⟨extR, sR, hinvR⟩
        · intro JDl hJDl
          c0_hfast_nogrp
          refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
              M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧ sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
          · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
            try dsimp only [Blocks.get_here]
            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.bumpD _ _ _ _ h) hinvSd.cfgOk hextDl
              hdenDl.lengths hmDl fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
            exact hJDl () mDl' ⟨extDl', sDl', hextDl',
              fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres, by rw [hcDl]; exact hfuDl,
              hmDl'⟩
          · intro JDb hJDb
            refine wp_m6Hdr_focus_frame hmSw' fun hmSwf => ?_
            c0_hfast_nogrp
            · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.redD _ _ _ _ h) hinvSd.cfgOk hextE
                hdenSw.lengths (fullM6HdrMem_unfocus hmSwf)
                fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
              exact hJDl () mDl ⟨extDl, sDl, hextDl,
                fullDenseInv_of_core_eq hdenSw hlDl hcDl hmsDl.extPres, by rw [hcDl]; exact hfuSw',
                hmDl⟩
            all_goals
              exact hJDb () _ ⟨extE, sSw, hextE, hdenSw, hfuSw', fullM6HdrMem_unfocus hmSwf⟩
    · have hinvE := FullM6HdrInv.mk_inv hinvSd.cfgOk hextE (hspE ‹okE = false›).1
      refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
      c0_hfast_nogrp
      · exact s5_probe_ret_wm henv hinvE.cfgOk hextE hinvE.sparse.lengths hfuE' (Or.inr rfl)
          (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›) (fun h => by cases h)
          (fullM6HdrMem_unfocus hmEf) hQ
      · exact hJSw' (subst_c, ()) mE ⟨extE, sE, hinvE, (hspE ‹okE = false›).2, hfuE',
          fullM6HdrMem_unfocus hmEf⟩

theorem full_probe_m6_init_core (Γ : Env) (henv : S5ProbeEnv Γ)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hQ : S5ProbeQ c F0 s R Q) :
    Func.wp Γ FullFidelityStep13S5ReduceProbe.full_probe_m6_body (c.hdr, true, ()) m Q X := by
  unfold Func.wp FullFidelityStep13S5ReduceProbe.full_probe_m6_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hfast_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.probeDt _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths (fullM6HdrMem_unfocus hmf)
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := by rw [hc0]; exact hcl0
  refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
  c0_hfast_nogrp
  let s0s : FullState :=
    { s0 with scratch := { s0.scratch with probings := s0.scratch.probings + 1#64 } }
  have hst0a := fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
    (s0.scratch.probings + 1#64)
  let s0a : FullState := { s0s with core := { s0s.core with probing := 1#64 } }
  have hinv0a := s5M6HdrInv_with_probing (fullM6HdrInv_of_probeStep hinv0 hst0a) 1#64
  have hcl0a : s0a.core.cur_level = 0 := hcl0'
  have hfu0a : s0a.core.fuel.toNat ≤ s.core.fuel.toNat := by
    dsimp only [s0a, s0s]; rw [hc0]; exact Nat.le_refl _
  have hm0a : (FullM6HdrMem c ext0 s0a ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, S5ProbeStateInv c F0 s R ext1 s1 m1)
    ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1⟩
    try dsimp only [Blocks.get_here]
    exact s5_probe_init_tail_ret1 henv hinv1 hQ
  · intro J1 hJ1
    c0_hfast_nogrp
    · refine wp_join_group (ts := [.bool])
        (fun _ mC => ∃ extC sC, S5ProbeStateInv c F0 s R extC sC mC) ?_ ?_
      · rintro _ ⟨subst_c, ⟨⟩⟩ mC ⟨extC, sC, hC⟩; try dsimp only [Blocks.get_here]
        refine wp_join_group (ts := [])
          (fun _ mB => ∃ extB sB, S5ProbeStateInv c F0 s R extB sB mB) ?_ ?_
        · rintro _ _ mB ⟨extB, sB, hB⟩; try dsimp only [Blocks.get_here]
          refine wp_join_group (ts := [.bool])
            (fun _ mSw => ∃ extSw sSw, S5ProbeStateInv c F0 s R extSw sSw mSw) ?_ ?_
          · rintro _ ⟨subst_sw, ⟨⟩⟩ mSw ⟨extSw, sSw, hSw⟩; try dsimp only [Blocks.get_here]
            refine wp_join_group (ts := [])
              (fun _ mF => ∃ extF sF, S5ProbeStateInv c F0 s R extF sF mF) ?_ ?_
            · rintro _ _ mF ⟨extF, sF, hF⟩; try dsimp only [Blocks.get_here]
              refine s5_probe_factor_block henv hF hQ ?_
              intro extD sD mD hD
              c0_hfast_nogrp
              exact hJ1 () mD ⟨extD, sD, hD⟩
            · intro JF hJF
              c0_hfast_nogrp
              · refine s5_probe_subst_if henv hSw hQ fun extF sF mF hF => by
                  c0_hfast_nogrp; exact hJF () mF ⟨extF, sF, hF⟩
              · exact hJF () mSw ⟨extSw, sSw, hSw⟩
          · intro JSw hJSw
            exact s5_probe_init_sweep henv hB hQ JSw
              (fun subst_sw mSw h => hJSw (subst_sw, ()) mSw h)
        · intro JB hJB
          exact s5_probe_bone_if henv hC hQ fun extB sB mB hB => by
            c0_hfast_nogrp; exact hJB () mB ⟨extB, sB, hB⟩
      · intro JC hJC
        exact s5_probe_init_cong henv ⟨hinv0a, hcl0a, hfu0a, hm0a⟩ hQ JC
          (fun subst_c mC h => hJC (subst_c, ()) mC h)
    · cases ‹true = false›

theorem full_probe_m6_s5_wp (Γ : Env)
    (hProbeDt : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hUpdCls : ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
      Γ "full_update_classify_fid" [i64] [] a m Q X)
    (hEnter : ∀ a m Q X, step13EnterDenseM6Spec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hEnterEx : ∀ a m Q X, step13EnterDenseExM6Spec a m Q X →
      Γ "full_enter_dense_ex_fid" [i64, .bool] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hBinRt : ∀ a m Q X, step13DenseBinRoundtripSpec a m Q X →
      Γ "full_dense_bin_roundtrip_fid" [i64] [] a m Q X)
    (hRebNosort : ∀ a m Q X, step13RebuildWatchesM6Spec a m Q X →
      Γ "full_rebuild_watches_nosort_fid" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, step13SubstituteM6Spec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, s5aBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hSweepD : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hHasFact : ∀ a m Q X, step13HasFactorCandsSpec a m Q X →
      Γ "full_has_factor_cands_fid" [i64] [.bool] a m Q X)
    (hFactor : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, s5aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, s5aTransitiveSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X)
    (hNlogpown : ∀ a m Q X, f64uPure2Spec a m Q X →
      Γ "f64u_nlogpown" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X →
      Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hToU64 : ∀ a m Q X, f64uPure1Spec a m Q X →
      Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hScaleM5 : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X →
      Func.wp Γ FullFidelityStep13S5ReduceProbe.full_probe_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  let henv : S5ProbeEnv Γ :=
    ⟨hProbeDt, hDelay, hRedD, hBumpD, hGetWm, hSetWm, hUpdCls, hEnter, hEnterEx, hCong, hBinRt,
      hRebNosort, hSubst, hBone, hSweepD, hHasFact, hFactor, hViv, hTrans, hNlogpown, hMul,
      hToU64, hScaleM5⟩
  cases initial
  · exact full_probe_m6_notinit_core Γ henv hinv hcl0 hm hQ
  · exact full_probe_m6_init_core Γ henv hinv hcl0 hm hQ

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
