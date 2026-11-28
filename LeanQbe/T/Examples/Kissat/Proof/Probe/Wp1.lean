/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Probe.Spec
public import LeanQbe.T.Examples.Kissat.Src.Probe
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Probe.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical WP Proofs for `Kissat.Src.Probe` Part 1 (`Wp1`)

Proves `full_probe_m6_init_core` (`initial = true`), `full_probe_m6_notinit_core`
(`initial = false`), and `full_probe_m6_wp` satisfying `Spec.fullProbeM6Spec` (`0`
legacy imports, `0` `@[expose]` on theorems/lemmas/sections, every decl `<= 450`
lines, every line `<= 100` cols).
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Probe

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Probe
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Probe.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6ProofUtilTactics

/-! ## 1. `initial` Path (`full_probe_m6_init_core`) -/

private theorem probe_init_tail_ret1 {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {saved_prob : Val i64} {ext1 : List (BitVec 64)} {s1 : FullState} {m1 : Mem 64}
    (henv : ProbeEnv Γ) (hinv1 : ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : ProbeQ c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_update_classify_fid"
        (Arg.var c.hdr, ()) fun _ =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
          probeRetWmExpr c saved_prob 1#64) Blocks.nil) fun Js =>
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
  refine wp_join_group (ts := []) (fun _ mF => ∃ extF sF, ProbeStateInv c F0 s R extF sF mF)
    (fun _ _ mF ⟨extF, sF, hinvF, hclF, hfuF, hmF⟩ =>
      probe_ret_wm henv hinvF.cfgOk hinvF.extOk hinvF.sparse.lengths hfuF
        (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinvF, hclF⟩) hmF hQ)
    (fun JF hJF => by
      c0_hfast_nogrp
      · exact hJF () mU ⟨extU, sU, hinvU, hclU, hfuU, hmU⟩
      · cases ‹true = false›)

private theorem probe_init_cong {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s0 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {ext0 : List (BitVec 64)} {m0 : Mem 64} {saved_prob : Val i64}
    (henv : ProbeEnv Γ) (hinv0 : ProbeStateInv c F0 s R ext0 s0 m0) (hQ : ProbeQ c F0 s R Q)
    (JC : Cont [.bool])
    (hJC : ∀ subst_c mC, (∃ extC sC, ProbeStateInv c F0 s R extC sC mC) →
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
                (Arg.var c.hdr, ()) fun _ => probeRetWmExpr c saved_prob 20#64)
              (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1072, ())) fun p_13 =>
              Expr.load i64 (Arg.var p_13.fst) fun ld_2 =>
              Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                  Expr.call (as := [i64]) (bs := []) "full_dense_bin_roundtrip_fid"
                    (Arg.var c.hdr, ()) fun _ =>
                  probeReb20Expr c saved_prob (Expr.group (sig := [[.bool]]) (fun _ =>
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
                          Expr.jnz (Arg.var p_22.fst) (probeRetWmExpr c saved_prob 20#64)
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
            Expr.jnz (Arg.var p_11.fst) (probeRetWmExpr c saved_prob 20#64)
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
      (fun _ mC' => ∃ extC' sC', ProbeStateInv c F0 s R extC' sC' mC')
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
      · refine probe_bin_rt henv hdenC (fullM6HdrMem_unfocus hmC)
          fun sRt mRt hdenRt hfuRt hmRt => ?_
        c0_call henv.rebNosort
        refine ⟨c, F0, extE, sRt, R, rfl, hinvCd.cfgOk, hextE, hdenRt, hmRt,
          fun _ extR sR mR hinvR _ hfuR _ _ hmR => ?_⟩
        exact probe_ret_wm henv hinvR.cfgOk hinvR.extOk hinvR.sparse.lengths
          (Nat.le_trans hfuR (by rw [hfuRt]; exact hfuC')) (Or.inr rfl)
          (fun _ => huC ‹_›) (fun h => by cases h) hmR hQ
      · have hmC' := fullM6HdrMem_unfocus hmC
        refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
            M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧ sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
        · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
          try dsimp only [Blocks.get_here]
          refine probe_bin_rt henv hdenDl hmDl fun sRt mRt hdenRt hfuRt hmRt => ?_
          refine probe_reb20 henv hinvCd.cfgOk hextDl hdenRt (by rw [hfuRt]; exact hfuDl) hmRt
            hQ fun extR sR mR hinvR => ?_
          refine wp_join_group (ts := [.bool])
            (fun _ mcb => ∃ extcb scb, ProbeStateInv c F0 s R extcb scb mcb)
            (fun _ ⟨scb, ⟨⟩⟩ mcb hcb => by c0_hfast_nogrp; exact hJC' (scb, ()) mcb hcb)
            fun Jcb hJcb => ?_
          c0_hfast_nogrp
          · exact probe_subst_if henv hinvR hQ fun extS sS mS hS => by
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
      · exact probe_ret_wm henv hinvE.cfgOk hextE hinvE.sparse.lengths hfuE' (Or.inr rfl)
          (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›) (fun h => by cases h)
          (fullM6HdrMem_unfocus hmEf) hQ
      · exact hJC' (true, ()) mE ⟨extE, sE, hinvE, (hspE ‹okE = false›).2, hfuE',
          fullM6HdrMem_unfocus hmEf⟩

private theorem probe_init_sweep {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s0 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {ext0 : List (BitVec 64)} {m0 : Mem 64} {saved_prob dticks : Val i64} {subst_c : Val .bool}
    (henv : ProbeEnv Γ) (hinv0 : ProbeStateInv c F0 s R ext0 s0 m0) (hQ : ProbeQ c F0 s R Q)
    (JSw : Cont [.bool])
    (hJSw : ∀ subst_sw mSw, (∃ extSw sSw, ProbeStateInv c F0 s R extSw sSw mSw) →
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
                  (Arg.var c.hdr, ()) fun _ => probeRetWmExpr c saved_prob 20#64)
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1080, ())) fun p_21 =>
                Expr.load i64 (Arg.var p_21.fst) fun ld_4 =>
                Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 32, ())) fun p_22 =>
                Expr.let_ (Op.mk (.mul i64) (Arg.var p_22.fst, Arg.imm 4, ())) fun p_23 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var ld_1, Arg.var p_23.fst, ())) fun p_24 =>
                Expr.load i32 (Arg.var p_24.fst) fun ld_5 =>
                Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_5, ())) fun p_25 =>
                Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                    probeReb20Expr c saved_prob (Expr.group (sig := [[.bool]]) (fun _ =>
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
                            Expr.jnz (Arg.var p_33.fst) (probeRetWmExpr c saved_prob 20#64)
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
            Expr.jnz (Arg.var p_13.fst) (probeRetWmExpr c saved_prob 20#64)
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
      (fun _ mSw' => ∃ extSw' sSw', ProbeStateInv c F0 s R extSw' sSw' mSw')
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
      have hdenEz := probeDense_zero_gu32 hdenE'
      c0_call henv.sweepD
      refine ⟨c, F0, _, m6ExtMem (m6ExtAddr c.hdr) extE ⋆ R, rfl, hdenEz, by assumption,
        fun rSw sSw mSw hdenSw _ hfuSw _ huSw hmSw => ?_⟩
      have hfuSw' := Nat.le_trans hfuSw hfuE'
      c0_hfast_nogrp
      · c0_call henv.rebNosort
        refine ⟨c, F0, extE, sSw, R, rfl, hinvSd.cfgOk, hextE, hdenSw,
          fullM6HdrMem_unfocus hmSw, fun _ extR sR mR hinvR _ hfuR _ _ hmR => ?_⟩
        exact probe_ret_wm henv hinvR.cfgOk hinvR.extOk hinvR.sparse.lengths
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
          refine probe_reb20 henv hinvSd.cfgOk hextDl hdenDl hfuDl hmDl hQ
            fun extR sR mR hinvR => ?_
          refine wp_join_group (ts := [.bool])
            (fun _ msb => ∃ extsb ssb, ProbeStateInv c F0 s R extsb ssb msb)
            (fun _ ⟨scb, ⟨⟩⟩ msb hsb => by c0_hfast_nogrp; exact hJSw' (scb, ()) msb hsb)
            fun Jsb hJsb => ?_
          c0_hfast_nogrp
          · exact probe_subst_if henv hinvR hQ fun extS sS mS hS => by
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
      · exact probe_ret_wm henv hinvE.cfgOk hextE hinvE.sparse.lengths hfuE' (Or.inr rfl)
          (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›) (fun h => by cases h)
          (fullM6HdrMem_unfocus hmEf) hQ
      · exact hJSw' (subst_c, ()) mE ⟨extE, sE, hinvE, (hspE ‹okE = false›).2, hfuE',
          fullM6HdrMem_unfocus hmEf⟩

private theorem full_probe_m6_init_core (Γ : Env) (henv : ProbeEnv Γ)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hQ : ProbeQ c F0 s R Q) :
    Func.wp Γ full_probe_m6_body (c.hdr, true, ()) m Q X := by
  unfold Func.wp full_probe_m6_body
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
  have hinv0a := probeM6HdrInv_with_probing (fullM6HdrInv_of_probeStep hinv0 hst0a) 1#64
  have hcl0a : s0a.core.cur_level = 0 := hcl0'
  have hfu0a : s0a.core.fuel.toNat ≤ s.core.fuel.toNat := by
    dsimp only [s0a, s0s]; rw [hc0]; exact Nat.le_refl _
  have hm0a : (FullM6HdrMem c ext0 s0a ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, ProbeStateInv c F0 s R ext1 s1 m1)
    ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1⟩
    try dsimp only [Blocks.get_here]
    exact probe_init_tail_ret1 henv hinv1 hQ
  · intro J1 hJ1
    c0_hfast_nogrp
    · refine wp_join_group (ts := [.bool])
        (fun _ mC => ∃ extC sC, ProbeStateInv c F0 s R extC sC mC) ?_ ?_
      · rintro _ ⟨subst_c, ⟨⟩⟩ mC ⟨extC, sC, hC⟩; try dsimp only [Blocks.get_here]
        refine wp_join_group (ts := [])
          (fun _ mB => ∃ extB sB, ProbeStateInv c F0 s R extB sB mB) ?_ ?_
        · rintro _ _ mB ⟨extB, sB, hB⟩; try dsimp only [Blocks.get_here]
          refine wp_join_group (ts := [.bool])
            (fun _ mSw => ∃ extSw sSw, ProbeStateInv c F0 s R extSw sSw mSw) ?_ ?_
          · rintro _ ⟨subst_sw, ⟨⟩⟩ mSw ⟨extSw, sSw, hSw⟩; try dsimp only [Blocks.get_here]
            refine wp_join_group (ts := [])
              (fun _ mF => ∃ extF sF, ProbeStateInv c F0 s R extF sF mF) ?_ ?_
            · rintro _ _ mF ⟨extF, sF, hF⟩; try dsimp only [Blocks.get_here]
              refine probe_factor_block henv hF hQ ?_
              intro extD sD mD hD
              c0_hfast_nogrp
              exact hJ1 () mD ⟨extD, sD, hD⟩
            · intro JF hJF
              c0_hfast_nogrp
              · refine probe_subst_if henv hSw hQ fun extF sF mF hF => by
                  c0_hfast_nogrp; exact hJF () mF ⟨extF, sF, hF⟩
              · exact hJF () mSw ⟨extSw, sSw, hSw⟩
          · intro JSw hJSw
            exact probe_init_sweep henv hB hQ JSw
              (fun subst_sw mSw h => hJSw (subst_sw, ()) mSw h)
        · intro JB hJB
          exact probe_bone_if henv hC hQ fun extB sB mB hB => by
            c0_hfast_nogrp; exact hJB () mB ⟨extB, sB, hB⟩
      · intro JC hJC
        exact probe_init_cong henv ⟨hinv0a, hcl0a, hfu0a, hm0a⟩ hQ JC
          (fun subst_c mC h => hJC (subst_c, ()) mC h)
    · cases ‹true = false›

/-! ## 2. `!initial` Path (`full_probe_m6_notinit_core`) & Top-Level `full_probe_m6_wp` -/

private theorem probe_tail_ret1 {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {saved_prob : Val i64} {ext1 : List (BitVec 64)} {s1 : FullState} {m1 : Mem 64}
    (henv : ProbeEnv Γ) (hinv1 : ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : ProbeQ c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_update_classify_fid"
        (Arg.var c.hdr, ()) fun _ =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
          probeRetWmExpr c saved_prob 1#64) Blocks.nil) fun Js =>
        Expr.jnz (Arg.var (false : Val .bool)) (Expr.jump Js.fst ())
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
  refine wp_join_group (ts := []) (fun _ mF => ∃ extF sF, ProbeStateInv c F0 s R extF sF mF)
    (fun _ _ mF ⟨extF, sF, hinvF, hclF, hfuF, hmF⟩ =>
      probe_ret_wm henv hinvF.cfgOk hinvF.extOk hinvF.sparse.lengths hfuF
        (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinvF, hclF⟩) hmF hQ)
    (fun JF hJF => by
      refine wp_m6Hdr_focus_frame hmU fun hmUf => ?_
      c0_hfast_nogrp
      c0_call henv.nlogpown; intro _
      c0_call henv.mul; intro _
      c0_hfast_nogrp
      c0_call henv.toU64; intro _
      c0_call henv.scaleM5
      refine ⟨c, sU, m6ExtMem (m6ExtAddr c.hdr) extU ⋆ R, rfl, hinvU.sparse.lengths,
        by assumption, fun sd => ?_⟩
      c0_hfast_nogrp
      have hstP := fullState_upd_probe_step hinvU.sparse.lengths
        (sU.scratch.conflicts + sd) sU.scratch.probings
      have hinvP := fullM6HdrInv_of_probeStep hinvU hstP
      have hlim : ({ sU with scratch := { sU.scratch with
          probe_limit := sU.scratch.conflicts + sd, probings := sU.scratch.probings } } :
          FullState) =
          { sU with scratch := { sU.scratch with probe_limit := sU.scratch.conflicts + sd } } := by
        cases sU with | mk _ sc => cases sc; rfl
      have hmP : (FullM6HdrMem c extU
          { sU with scratch := { sU.scratch with probe_limit := sU.scratch.conflicts + sd } } ⋆ R)
          _ := fullM6HdrMem_unfocus (by rw [← hlim]; exact hm)
      exact hJF () _ ⟨extU, _, hinvP, hstP.2.1 ▸ hclU, by rw [hstP.2.1]; exact hfuU, hmP⟩)

private theorem full_probe_m6_notinit_core (Γ : Env) (henv : ProbeEnv Γ)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hQ : ProbeQ c F0 s R Q) :
    Func.wp Γ full_probe_m6_body (c.hdr, false, ()) m Q X := by
  unfold Func.wp full_probe_m6_body
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
  have hinv0a := probeM6HdrInv_with_probing (fullM6HdrInv_of_probeStep hinv0 hst0a) 1#64
  have hcl0a : s0a.core.cur_level = 0 := hcl0'
  have hfu0a : s0a.core.fuel.toNat ≤ s.core.fuel.toNat := by
    dsimp only [s0a, s0s]; rw [hc0]; exact Nat.le_refl _
  have hm0a : (FullM6HdrMem c ext0 s0a ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, ProbeStateInv c F0 s R ext1 s1 m1)
    ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1⟩
    try dsimp only [Blocks.get_here]
    exact probe_tail_ret1 henv hinv1 hQ
  · intro J1 hJ1
    c0_hfast_nogrp
    refine wp_join_group (ts := [i64])
      (fun _ mB => ∃ extB sB, ProbeStateInv c F0 s R extB sB mB) ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ mB hB; try dsimp only [Blocks.get_here]; c0_hfast_nogrp; exact hJ1 () mB hB
    · intro Jbrk hJbrk
      c0_hfast_nogrp
      refine wp_loop_inv (fun (round, ()) mL => round.toNat ≤ 2 ∧
          ∃ extL sL, ProbeStateInv c F0 s R extL sL mL)
        (fun (round, ()) _ => 2 - round.toNat)
        (fun JL hJL => by
          c0_hfast_nogrp
          exact hJL (0#64, ()) _ ⟨Nat.zero_le _, ext0, s0a, hinv0a, hcl0a, hfu0a, hm0a⟩)
        (fun JL (round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ ihL => ?_)
      · c0_hfast_nogrp
        · have hnd_lt : round.toNat < 2 :=
            Nat.lt_of_lt_of_eq (BitVec.lt_def.mp ‹round < 2#64›) (by decide)
          have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
          c0_hfast_nogrp
          refine probe_var_cnt_loop rfl hinvL (fullM6HdrMem_unfocus hmLf) fun _ => ?_
          refine wp_join_group (ts := [])
            (fun _ mC => ∃ extC sC, ProbeStateInv c F0 s R extC sC mC) ?_ ?_
          · rintro _ _ mC ⟨extC, sC, hC⟩; try dsimp only [Blocks.get_here]
            refine wp_join_group (ts := [])
              (fun _ mS1 => ∃ extS1 sS1, ProbeStateInv c F0 s R extS1 sS1 mS1) ?_ ?_
            · rintro _ _ mS1 ⟨extS1, sS1, hS1⟩; try dsimp only [Blocks.get_here]
              refine wp_join_group (ts := [])
                (fun _ mB1 => ∃ extB1 sB1, ProbeStateInv c F0 s R extB1 sB1 mB1) ?_ ?_
              · rintro _ _ mB1 ⟨extB1, sB1, hinvB1, hclB1, hfuB1, hmB1⟩
                try dsimp only [Blocks.get_here]
                c0_call henv.viv
                refine ⟨c, F0, extB1, sB1, R, rfl, hinvB1.cfgOk, hinvB1.extOk, hinvB1.sparse,
                  hmB1, fun rV extV sV mV hextV hspV hclprV hfuV _ huV hmV => ?_⟩
                have hinvV := FullM6HdrInv.mk_inv hinvB1.cfgOk hextV.1 hspV
                have hfuV' := Nat.le_trans hfuV hfuB1
                c0_hfast_nogrp
                · exact probe_ret_wm henv hinvV.cfgOk hextV.1 hinvV.sparse.lengths hfuV'
                    (Or.inr rfl) (fun _ => huV ‹_›) (fun h => by cases h) hmV hQ
                · refine wp_join_group (ts := [])
                      (fun _ mSw => ∃ extSw sSw, ProbeStateInv c F0 s R extSw sSw mSw) ?_ ?_
                  · rintro _ _ mSw ⟨extSw, sSw, hSw⟩; try dsimp only [Blocks.get_here]
                    refine wp_join_group (ts := [])
                      (fun _ mS2 => ∃ extS2 sS2, ProbeStateInv c F0 s R extS2 sS2 mS2) ?_ ?_
                    · rintro _ _ mS2 ⟨extS2, sS2, hinvS2, hclS2, hfuS2, hmS2⟩
                      try dsimp only [Blocks.get_here]
                      c0_hfast_nogrp
                      refine wp_join_group (ts := [])
                          (fun _ mTr => ∃ extTr sTr, ProbeStateInv c F0 s R extTr sTr mTr) ?_ ?_
                      · rintro _ _ mTr ⟨extTr, sTr, hTr⟩; try dsimp only [Blocks.get_here]
                        refine wp_join_group (ts := [])
                          (fun _ mB2 => ∃ extB2 sB2, ProbeStateInv c F0 s R extB2 sB2 mB2) ?_ ?_
                        · rintro _ _ mB2 ⟨extB2, sB2, hB2⟩; try dsimp only [Blocks.get_here]
                          refine probe_factor_block henv hB2 hQ ?_
                          intro extF sF mF ⟨hinvF, hclF, hfuF, hmF⟩
                          refine wp_m6Hdr_focus_frame hmF fun hmFf => ?_
                          c0_hfast_nogrp
                          refine probe_var_cnt_ai_loop rfl hinvF
                            (fullM6HdrMem_unfocus hmFf) fun _ => ?_
                          c0_hfast_nogrp
                          · exact hJbrk (_, ()) _
                              ⟨extF, sF, hinvF, hclF, hfuF, fullM6HdrMem_unfocus hmFf⟩
                          · exact ihL (round + 1#64, ()) _ (by dsimp only; omega)
                              ⟨by omega, extF, sF, hinvF, hclF, hfuF,
                                fullM6HdrMem_unfocus hmFf⟩
                        · intro JB2 hJB2
                          refine probe_bone_if henv hTr hQ fun extB2 sB2 mB2 hB2 => by
                            c0_hfast_nogrp; exact hJB2 () mB2 ⟨extB2, sB2, hB2⟩
                      · intro JTr hJTr
                        refine wp_m6Hdr_focus_frame hmS2 fun hmS2f => ?_
                        c0_hfast_nogrp
                        · c0_call henv.trans
                          refine ⟨c, F0, extS2, sS2, R, rfl, hinvS2.cfgOk, hinvS2.extOk,
                            hinvS2.sparse, fullM6HdrMem_unfocus hmS2f,
                            fun rT extT sT mT hextT hspT _ _ hclprT hfuT _ huT hmT => ?_⟩
                          have hinvT := FullM6HdrInv.mk_inv hinvS2.cfgOk hextT.1 hspT
                          have hfuT' := Nat.le_trans hfuT hfuS2
                          c0_hfast_nogrp
                          · exact probe_ret_wm henv hinvT.cfgOk hextT.1 hinvT.sparse.lengths
                              hfuT' (Or.inr rfl) (fun _ => huT ‹_›) (fun h => by cases h) hmT hQ
                          · exact hJTr () mT ⟨extT, sT, hinvT, hclprT.1, hfuT', hmT⟩
                        · exact hJTr () mS2
                            ⟨extS2, sS2, hinvS2, hclS2, hfuS2, fullM6HdrMem_unfocus hmS2f⟩
                    · intro JS2 hJS2
                      refine probe_subst_if henv hSw hQ fun extS2 sS2 mS2 hS2 => by
                        c0_hfast_nogrp; exact hJS2 () mS2 ⟨extS2, sS2, hS2⟩
                  · intro JSw hJSw
                    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.delay _ _ _ _ h) hinvV.cfgOk
                      hextV.1 hinvV.sparse.lengths hmV
                      fun ⟨delSw, ⟨⟩⟩ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
                    have hinvSd := fullM6HdrInv_with_ext
                      (fullM6HdrInv_of_m6Pres hinvV hlSd hcSd hmsSd) hextSd
                    have hclSd : sSd.core.cur_level = 0 := by rw [hcSd]; exact hclprV.1
                    have hfuSd : sSd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                      rw [hcSd]; exact hfuV'
                    c0_hfast_nogrp
                    · exact hJSw () mSd ⟨extSd, sSd, hinvSd, hclSd, hfuSd, hmSd⟩
                    · refine wp_join_group (ts := [])
                        (fun _ mE => ∃ extE sE, ProbeStateInv c F0 s R extE sE mE) ?_ ?_
                      · rintro _ _ mE hE; try dsimp only [Blocks.get_here]
                        c0_hfast_nogrp; exact hJSw () mE hE
                      · intro JSw' hJSw'
                        refine wp_m6Hdr_focus_frame hmSd fun hmSdf => ?_
                        c0_call henv.enter
                        refine ⟨c, F0, extSd, sSd, R, rfl, hinvSd.cfgOk, hinvSd.extOk,
                          hinvSd.sparse.lengths, hinvSd.sparse.1, hinvSd.sparse.2.1,
                          hinvSd.sparse.2.2.1, hinvSd.sparse.2.2.2.1,
                          (fun hdm => absurd hinvSd.sparse.2.2.2.2 hdm),
                          fullM6HdrMem_unfocus hmSdf,
                          fun okE extE sE mE _ hextE _ hlenE hlmE hndE hesE _ hfuE hdenE hspE
                            hmE => ?_⟩
                        have hfuE' := Nat.le_trans hfuE hfuSd
                        c0_hfast_nogrp
                        · have hdenE' := hdenE ‹okE = true›
                          refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
                          have hgu32E : 32 < sE.scratch.glue_used.length := by
                            rw [hdenE'.lengths.scratch_ok.glue_used_len]; decide
                          c0_hfast_nogrp
                          have hdenEz := probeDense_zero_gu32 hdenE'
                          c0_call henv.sweepD
                          refine ⟨c, F0, _, m6ExtMem (m6ExtAddr c.hdr) extE ⋆ R, rfl, hdenEz,
                            by assumption, fun rSw sSw mSw hdenSw _ hfuSw _ huSw hmSw => ?_⟩
                          have hfuSw' := Nat.le_trans hfuSw hfuE'
                          have hgu32Sw : 32 < sSw.scratch.glue_used.length := by
                            rw [hdenSw.lengths.scratch_ok.glue_used_len]; decide
                          c0_hfast_nogrp
                          · c0_call henv.rebNosort
                            refine ⟨c, F0, extE, sSw, R, rfl, hinvV.cfgOk, hextE, hdenSw,
                              fullM6HdrMem_unfocus hmSw,
                              fun _ extR sR mR hinvR _ hfuR _ _ hmR => ?_⟩
                            exact probe_ret_wm henv hinvR.cfgOk hinvR.extOk
                              hinvR.sparse.lengths (Nat.le_trans hfuR hfuSw') (Or.inr rfl)
                              (fun _ => huSw ‹_›) (fun h => by cases h) hmR hQ
                          · have hmSw' := fullM6HdrMem_unfocus hmSw
                            refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                                M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                                sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                            · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                              try dsimp only [Blocks.get_here]
                              exact probe_reb20 henv hinvV.cfgOk hextDl hdenDl hfuDl hmDl hQ
                                (fun _ _ mR hR => hJSw' () mR ⟨_, _, hR⟩)
                            · intro JDl hJDl
                              c0_hfast_nogrp
                              refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                                  M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                                  sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                              · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                                try dsimp only [Blocks.get_here]
                                refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.bumpD _ _ _ _ h)
                                  hinvV.cfgOk hextDl hdenDl.lengths hmDl
                                  fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                                exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                                  fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                                  by rw [hcDl]; exact hfuDl, hmDl'⟩
                              · intro JDb hJDb
                                refine wp_m6Hdr_focus_frame hmSw' fun hmSwf => ?_
                                c0_hfast_nogrp
                                · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.redD _ _ _ _ h)
                                    hinvV.cfgOk hextE hdenSw.lengths (fullM6HdrMem_unfocus hmSwf)
                                    fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                                  exact hJDl () mDl ⟨extDl, sDl, hextDl,
                                    fullDenseInv_of_core_eq hdenSw hlDl hcDl hmsDl.extPres,
                                    by rw [hcDl]; exact hfuSw', hmDl⟩
                                all_goals exact hJDb () _ ⟨extE, sSw, hextE, hdenSw, hfuSw',
                                  fullM6HdrMem_unfocus hmSwf⟩
                        · have hinvE := FullM6HdrInv.mk_inv hinvV.cfgOk hextE (hspE ‹okE = false›).1
                          refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
                          c0_hfast_nogrp
                          · have hinvE' := probeM6HdrInv_with_probing hinvE s0.core.probing
                            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.setWm _ _ _ _ h)
                              hinvE'.cfgOk hextE hinvE'.sparse.lengths
                              (fullM6HdrMem_unfocus (by assumption))
                              fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
                            c0_hfast_nogrp
                            exact hQ 20#64 ext' s' m' hlen' hext' (by rw [hc']; exact hfuE')
                              (Or.inr rfl) (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                              (fun h => by cases h) hm'
                          · exact hJSw' () mE ⟨extE, sE, hinvE, (hspE ‹okE = false›).2, hfuE',
                              fullM6HdrMem_unfocus (by assumption)⟩
              · intro JB1 hJB1
                refine probe_bone_if henv hS1 hQ fun extB1 sB1 mB1 hB1 => by
                  c0_hfast_nogrp; exact hJB1 () mB1 ⟨extB1, sB1, hB1⟩
            · intro JS1 hJS1
              refine probe_subst_if henv hC hQ fun extS1 sS1 mS1 hS1 => by
                c0_hfast_nogrp; exact hJS1 () mS1 ⟨extS1, sS1, hS1⟩
          · intro JC hJC
            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.delay _ _ _ _ h) hinvL.cfgOk
              hinvL.extOk hinvL.sparse.lengths (fullM6HdrMem_unfocus hmLf)
              fun ⟨delC, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
            have hinvCd := fullM6HdrInv_with_ext
              (fullM6HdrInv_of_m6Pres hinvL hlCd hcCd hmsCd) hextCd
            have hclCd : sCd.core.cur_level = 0 := by rw [hcCd]; exact hclL
            have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcCd]; exact hfuL
            c0_hfast_nogrp
            · exact hJC () mCd ⟨extCd, sCd, hinvCd, hclCd, hfuCd, hmCd⟩
            · refine wp_join_group (ts := [])
                (fun _ mC' => ∃ extC' sC', ProbeStateInv c F0 s R extC' sC' mC') ?_ ?_
              · rintro _ _ mC' hC'; try dsimp only [Blocks.get_here]
                c0_hfast_nogrp; exact hJC () mC' hC'
              · intro JC' hJC'
                refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                c0_call henv.enter
                refine ⟨c, F0, extCd, sCd, R, rfl, hinvCd.cfgOk, hinvCd.extOk,
                  hinvCd.sparse.lengths, hinvCd.sparse.1, hinvCd.sparse.2.1,
                  hinvCd.sparse.2.2.1, hinvCd.sparse.2.2.2.1,
                  (fun hdm => absurd hinvCd.sparse.2.2.2.2 hdm),
                  fullM6HdrMem_unfocus hmCdf,
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
                  · refine probe_bin_rt henv hdenC (fullM6HdrMem_unfocus hmC)
                      fun sRt mRt hdenRt hfuRt hmRt => ?_
                    c0_call henv.rebNosort
                    refine ⟨c, F0, extE, sRt, R, rfl, hinvL.cfgOk, hextE, hdenRt, hmRt,
                      fun _ extR sR mR hinvR _ hfuR _ _ hmR => ?_⟩
                    exact probe_ret_wm henv hinvR.cfgOk hinvR.extOk hinvR.sparse.lengths
                      (Nat.le_trans hfuR (by rw [hfuRt]; exact hfuC')) (Or.inr rfl)
                      (fun _ => huC ‹_›) (fun h => by cases h) hmR hQ
                  · have hmC' := fullM6HdrMem_unfocus hmC
                    refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                        M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                        sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                    · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                      try dsimp only [Blocks.get_here]
                      refine probe_bin_rt henv hdenDl hmDl fun sRt mRt hdenRt hfuRt hmRt => ?_
                      exact probe_reb20 henv hinvL.cfgOk hextDl hdenRt
                        (by rw [hfuRt]; exact hfuDl) hmRt hQ
                        (fun _ _ mR hR => hJC' () mR ⟨_, _, hR⟩)
                    · intro JDl hJDl
                      c0_hfast_nogrp
                      refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                          M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                          sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                      · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                        try dsimp only [Blocks.get_here]
                        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.bumpD _ _ _ _ h)
                          hinvL.cfgOk hextDl hdenDl.lengths hmDl
                          fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                        exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                          fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                          by rw [hcDl]; exact hfuDl, hmDl'⟩
                      · intro JDb hJDb
                        refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                        c0_hfast_nogrp
                        · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.redD _ _ _ _ h)
                            hinvL.cfgOk hextE hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                            fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                          exact hJDl () mDl ⟨extDl, sDl, hextDl,
                            fullDenseInv_of_core_eq hdenC hlDl hcDl hmsDl.extPres,
                            by rw [hcDl]; exact hfuC', hmDl⟩
                        all_goals
                          exact hJDb () mC
                            ⟨extE, sC, hextE, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hextE (hspE ‹okE = false›).1
                  refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
                  c0_hfast_nogrp
                  · have hinvE' := probeM6HdrInv_with_probing hinvE s0.core.probing
                    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.setWm _ _ _ _ h)
                      hinvE'.cfgOk hextE hinvE'.sparse.lengths
                      (fullM6HdrMem_unfocus (by assumption))
                      fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
                    c0_hfast_nogrp
                    exact hQ 20#64 ext' s' m' hlen' hext' (by rw [hc']; exact hfuE')
                      (Or.inr rfl) (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                      (fun h => by cases h) hm'
                  · exact hJC' () mE ⟨extE, sE, hinvE, (hspE ‹okE = false›).2, hfuE',
                      fullM6HdrMem_unfocus (by assumption)⟩
        · exact hJbrk (_, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, hmL⟩

theorem full_probe_m6_wp (Γ : Env)
    (hProbeDt : Γ.Has "full_probe_dticks_m6_hdr" fullProbeDticksM6HdrSpec)
    (hDelay : Γ.Has "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hRedD : Γ.Has "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBumpD : Γ.Has "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hGetWm : Γ.Has "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64]))
    (hSetWm : Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hUpdCls : Γ.Has "full_update_classify_fid" Internal.Spec.fullUpdateClassifyFidSpec)
    (hEnter : Γ.Has "full_enter_dense" Dense.Spec.fullEnterDenseM6Spec)
    (hEnterEx : Γ.Has "full_enter_dense_ex_fid" Dense.Spec.fullEnterDenseExM6Spec)
    (hCong : Γ.Has "full_congruence_dense" Congruence.Spec.fullCongruenceDenseSpec)
    (hBinRt : Γ.Has "full_dense_bin_roundtrip_fid" Forward.Spec.fullDenseBinRoundtripFidSpec)
    (hRebNosort : Γ.Has "full_rebuild_watches_nosort_fid" Dense.Spec.fullRebuildWatchesM6Spec)
    (hSubst : Γ.Has "full_substitute" Substitute.Spec.fullSubstituteM6Spec)
    (hBone : Γ.Has "full_backbone_m6" Backbone.Spec.fullBackboneM6Spec)
    (hSweepD : Γ.Has "full_sweep_dense_m6" Sweep.Spec.fullSweepDenseM6Spec)
    (hHasFact : Γ.Has "full_has_factor_cands_fid" Factor.Spec.step13HasFactorCandsSpec)
    (hFactor : Γ.Has "full_factor" Factor.Spec.fullFactorHeapSpec)
    (hViv : Γ.Has "full_vivify_m6_hdr" Vivify.Spec.vivifyM6HdrSpec)
    (hTrans : Γ.Has "full_transitive_m6" Transitive.Spec.fullTransitiveM6Spec)
    (hNlogpown : Γ.Has "f64u_nlogpown" Float64.Spec.f64uPure2Spec)
    (hMul : Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec)
    (hToU64 : Γ.Has "f64u_to_u64" Float64.Spec.f64uPure1Spec)
    (hScaleM5 : Γ.Has "full_scale_delta_m5" Limits.Spec.schedScaleDeltaSpec) :
    ∀ a m Q X, fullProbeM6Spec a m Q X →
      Func.wp Γ full_probe_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases fullProbeM6Spec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  let henv : ProbeEnv Γ :=
    ⟨hProbeDt, hDelay, hRedD, hBumpD, hGetWm, hSetWm, hUpdCls, hEnter, hEnterEx, hCong, hBinRt,
      hRebNosort, hSubst, hBone, hSweepD, hHasFact, hFactor, hViv, hTrans, hNlogpown, hMul,
      hToU64, hScaleM5⟩
  cases initial
  · exact full_probe_m6_notinit_core Γ henv hinv hcl0 hm hQ
  · exact full_probe_m6_init_core Γ henv hinv hcl0 hm hQ

end LeanQbe.T.Examples.Kissat.Proof.Probe
