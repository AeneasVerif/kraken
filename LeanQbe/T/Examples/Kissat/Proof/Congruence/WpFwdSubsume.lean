/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpFwdSubsume0
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence Forward Subsumption WP Proof (`full_cong_fwd_subsume`)

Canonical `Func.wp` proof for `full_cong_fwd_subsume` (`Spec.fullCongFwdSubsumeSpec`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

/-! ## 1. Subsumption Check & Pass-2 Occurrence Loop (`fidFs_subsumption_wp`, `fidFs_pass2_wp`) -/

private def fidFs_subsumption_expr {V : Ty → Type} {L : List Ty → Type}
    (pRepr pArena pVals pLitMark pTmp pScr pW1 pW2 tl tk2p1 : V i64)
    (msz cref lr0 lcnt0 : V i32) (cRed : V .bool)
    (kExit : Tup V [i64, i32, i32, i32, .bool] → Expr V L [i64]) : Expr V L [i64] :=
  .group (sig := [[i64, i32, i32, i32, .bool]]) (fun Js5 => .cons (fun p72 =>
    .group (sig := [[]]) (fun Js6 => .cons (fun _ => kExit p72) .nil) fun Js6 =>
    .let_ ⟨.cmp .ult i32, (.var p72.2.1, (.var msz, ()))⟩ fun pc1 => .jnz (.var pc1.1)
      (.jnz (.var p72.2.2.2.2.1) (.jump Js6.1 ())
        (.let_ ⟨.cmp .ult i64, (.var p72.1, (.var tl, ()))⟩ fun pc2 => .jnz (.var pc2.1)
           (.let_ ⟨.zext 32 64, (.var p72.2.1, ())⟩ fun pa1 =>
            .let_ ⟨.mul i64, (.var pa1.1, (.imm 4, ()))⟩ fun pa2 =>
            .let_ ⟨.add i64, (.var pTmp, (.var pa2.1, ()))⟩ fun pa3 =>
            .load i32 (.var pa3.1) fun rk =>
            .let_ ⟨.zext 32 64, (.var rk, ())⟩ fun pa4 =>
            .let_ ⟨.mul i64, (.var pa4.1, (.imm 4, ()))⟩ fun pa5 =>
            .let_ ⟨.add i64, (.var pW2, (.var pa5.1, ()))⟩ fun pa6 =>
            .load i32 (.var pa6.1) fun cnt =>
            .group (sig := [[i32, i32]]) (fun Jlr => .cons (fun plr =>
               .let_ ⟨.zext 32 64, (.var rk, ())⟩ fun pb1 =>
               .let_ ⟨.mul i64, (.var pb1.1, (.imm 4, ()))⟩ fun pb2 =>
               .let_ ⟨.add i64, (.var pW1, (.var pb2.1, ()))⟩ fun pb3 =>
               .load i32 (.var pb3.1) fun nd0 =>
               .group (sig := [[i64, .bool, i32]]) (fun Jnd_ex => .cons (fun pnd_e =>
                  .let_ ⟨.add i32, (.var p72.2.1, (.imm 1, ()))⟩ fun pki1 =>
                  .jump Js5.1 (.var pnd_e.1, (.var pki1.1, (.var plr.1, (.var plr.2.1,
                    (.var pnd_e.2.1, ())))))) .nil)
               fun Jnd_ex =>
               .group (sig := [[i64, i32]]) (fun Jnd => .cons (fun pnd =>
                  .let_ ⟨.cmp .ne i32, (.var pnd.2.1, (.imm 4294967295, ()))⟩ fun pn1 =>
                  .jnz (.var pn1.1)
                    (.let_ ⟨.cmp .ult i64, (.var pnd.1, (.var tl, ()))⟩ fun pn2 =>
                     .jnz (.var pn2.1)
                       (.let_ ⟨.add i64, (.var pnd.1, (.imm 1, ()))⟩ fun ptk1 =>
                        .let_ ⟨.zext 32 64, (.var pnd.2.1, ())⟩ fun pd1 =>
                        .let_ ⟨.mul i64, (.var pd1.1, (.imm 4, ()))⟩ fun pd2 =>
                        .let_ ⟨.add i64, (.var pScr, (.var pd2.1, ()))⟩ fun pd3 =>
                        .load i32 (.var pd3.1) fun dref =>
                        .let_ ⟨.zext 32 64, (.var pnd.2.1, ())⟩ fun pd4 =>
                        .let_ ⟨.add i64, (.var pd4.1, (.imm 1, ()))⟩ fun pd5 =>
                        .let_ ⟨.mul i64, (.var pd5.1, (.imm 4, ()))⟩ fun pd6 =>
                        .let_ ⟨.add i64, (.var pScr, (.var pd6.1, ()))⟩ fun pd7 =>
                        .load i32 (.var pd7.1) fun nxt =>
                        .let_ ⟨.zext 32 64, (.var dref, ())⟩ fun pd8 =>
                        .let_ ⟨.mul i64, (.var pd8.1, (.imm 4, ()))⟩ fun pd9 =>
                        .let_ ⟨.add i64, (.var pArena, (.var pd9.1, ()))⟩ fun pd10 =>
                        .load i32 (.var pd10.1) fun dhdr =>
                        .let_ ⟨.zext 32 64, (.var dref, ())⟩ fun pd11 =>
                        .let_ ⟨.add i64, (.var pd11.1, (.imm 2, ()))⟩ fun pd12 =>
                        .let_ ⟨.mul i64, (.var pd12.1, (.imm 4, ()))⟩ fun pd13 =>
                        .let_ ⟨.add i64, (.var pArena, (.var pd13.1, ()))⟩ fun pd14 =>
                        .load i32 (.var pd14.1) fun dsz =>
                        .let_ ⟨.and i32, (.var dhdr, (.imm 4194304, ()))⟩ fun pd15 =>
                        .let_ ⟨.cmp .ne i32, (.var pd15.1, (.imm 0, ()))⟩ fun pd16 =>
                        .group (sig := [[.bool]]) (fun Jskd => .cons (fun _ =>
                           .jump Jnd.1 (.var ptk1.1, (.var nxt, ()))) .nil) fun Jskd =>
                        .let_ ⟨.and i32, (.var dhdr, (.imm 524288, ()))⟩ fun pd17 =>
                        .let_ ⟨.cmp .eq i32, (.var pd17.1, (.imm 0, ()))⟩ fun pd18 =>
                        .jnz (.var pd18.1)
                          (.let_ ⟨.cmp .ne i32, (.var dref, (.var cref, ()))⟩ fun pd19 =>
                           .jnz (.var pd19.1)
                             (.group (sig := [[]]) (fun Jent => .cons (fun _ =>
                                .group (sig := [[.bool, i32]]) (fun Jdj_ex => .cons (fun pdj =>
                                   .jnz (.var pdj.1)
                                     (.jump Jnd_ex.1 (.var ptk1.1, (.imm true, (.var pnd.2.1, ()))))
                                     (.jump Jskd.1 (.var p72.2.2.2.2.1, ()))) .nil) fun Jdj_ex =>
                                .group (sig := [[i32]]) (fun Jdj => .cons (fun dj =>
                                   .let_ ⟨.cmp .ult i32, (.var dj.1, (.var dsz, ()))⟩ fun pj1 =>
                                   .jnz (.var pj1.1)
                                     (.let_ ⟨.zext 32 64, (.var dref, ())⟩ fun pj2 =>
                                      .let_ ⟨.add i64, (.var pj2.1, (.imm 3, ()))⟩ fun pj3 =>
                                      .let_ ⟨.zext 32 64, (.var dj.1, ())⟩ fun pj4 =>
                                      .let_ ⟨.add i64, (.var pj3.1, (.var pj4.1, ()))⟩ fun pj5 =>
                                      .let_ ⟨.mul i64, (.var pj5.1, (.imm 4, ()))⟩ fun pj6 =>
                                      .let_ ⟨.add i64, (.var pArena, (.var pj6.1, ()))⟩ fun pj7 =>
                                      .load i32 (.var pj7.1) fun ol =>
                                      .let_ ⟨.zext 32 64, (.var ol, ())⟩ fun pj8 =>
                                      .let_ ⟨.add i64, (.var pVals, (.var pj8.1, ()))⟩ fun pj9 =>
                                      .load i8 (.var pj9.1) fun ov =>
                                      .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun pj10 =>
                                      .let_ ⟨.sext 8 32, (.var ov, ())⟩ fun pj11 =>
                                      .let_ ⟨.sext 8 32, (.var pj10.1, ())⟩ fun pj12 =>
                                      .let_ ⟨.cmp .sgt i32, (.var pj11.1, (.var pj12.1,
                                        ()))⟩ fun pj13 =>
                                      .jnz (.var pj13.1)
                                        (.jump Jdj_ex.1 (.imm false, (.var dj.1, ())))
                                        (.group (sig := [[.bool]]) (fun Jdo => .cons (fun _ =>
                                           .let_ ⟨.add i32, (.var dj.1, (.imm 1, ()))⟩ fun pdj1 =>
                                           .jump Jdj.1 (.var pdj1.1, ())) .nil) fun Jdo =>
                                         .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun pj14 =>
                                         .let_ ⟨.sext 8 32, (.var ov, ())⟩ fun pj15 =>
                                         .let_ ⟨.sext 8 32, (.var pj14.1, ())⟩ fun pj16 =>
                                         .let_ ⟨.cmp .eq i32, (.var pj15.1, (.var pj16.1,
                                           ()))⟩ fun pj17 =>
                                         .jnz (.var pj17.1)
                                           (.call "full_cong_find" (as := [i64, i32]) (bs := [i32])
                                              (Arg.var pRepr, (Arg.var ol, ())) fun ro =>
                                            .let_ ⟨.zext 32 64, (.var ro.1, ())⟩ fun pj18 =>
                                            .let_ ⟨.add i64, (.var pVals, (.var pj18.1,
                                              ()))⟩ fun pj19 =>
                                            .load i8 (.var pj19.1) fun rov =>
                                            .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun pj20 =>
                                            .let_ ⟨.sext 8 32, (.var rov, ())⟩ fun pj21 =>
                                            .let_ ⟨.sext 8 32, (.var pj20.1, ())⟩ fun pj22 =>
                                            .let_ ⟨.cmp .sgt i32, (.var pj21.1, (.var pj22.1,
                                              ()))⟩ fun pj23 =>
                                            .jnz (.var pj23.1)
                                              (.jump Jdj_ex.1 (.imm false, (.var dj.1, ())))
                                              (.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun pj24 =>
                                               .let_ ⟨.sext 8 32, (.var rov, ())⟩ fun pj25 =>
                                               .let_ ⟨.sext 8 32, (.var pj24.1, ())⟩ fun pj26 =>
                                               .let_ ⟨.cmp .eq i32, (.var pj25.1, (.var pj26.1,
                                                 ()))⟩ fun pj27 =>
                                               .jnz (.var pj27.1)
                                                 (.let_ ⟨.zext 32 64, (.var ro.1, ())⟩ fun pj28 =>
                                                  .let_ ⟨.add i64, (.var pLitMark, (.var pj28.1,
                                                    ()))⟩ fun pj29 =>
                                                  .load i8 (.var pj29.1) fun rlm =>
                                                  .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun pj30 =>
                                                  .let_ ⟨.zext 8 32, (.var rlm, ())⟩ fun pj31 =>
                                                  .let_ ⟨.zext 8 32, (.var pj30.1, ())⟩ fun pj32 =>
                                                  .let_ ⟨.cmp .eq i32, (.var pj31.1, (.var pj32.1,
                                                    ()))⟩ fun pj33 =>
                                                  .jnz (.var pj33.1)
                                                    (.jump Jdj_ex.1 (.imm false, (.var dj.1, ())))
                                                    (.jump Jdo.1 (.imm true, ())))
                                                 (.jump Jdo.1 (.imm true, ()))))
                                           (.jump Jdo.1 (.imm true, ()))))
                                     (.jump Jdj_ex.1 (.imm true, (.var dj.1, ())))) .nil)
                                fun Jdj => .jump Jdj.1 (.imm 0, ())) .nil)
                              fun Jent => .jnz (.var cRed) (.jump Jent.1 ())
                                (.jnz (.var pd16.1) (.jump Jskd.1 (.var p72.2.2.2.2.1,
                                  ())) (.jump Jent.1 ())))
                             (.jump Jskd.1 (.var p72.2.2.2.2.1, ())))
                          (.jump Jskd.1 (.var p72.2.2.2.2.1, ())))
                       (.jump Jnd_ex.1 (.var pnd.1, (.var p72.2.2.2.2.1, (.var pnd.2.1, ())))))
                    (.jump Jnd_ex.1 (.var pnd.1, (.var p72.2.2.2.2.1, (.var pnd.2.1, ()))))) .nil)
               fun Jnd => .jump Jnd.1 (.var p72.1, (.var nd0, ()))) .nil)
            fun Jlr => .let_ ⟨.cmp .ult i32, (.var cnt, (.var p72.2.2.2.1, ()))⟩ fun pl1 =>
              .jnz (.var pl1.1) (.jump Jlr.1 (.var rk, (.var cnt, ())))
                (.jump Jlr.1 (.var p72.2.2.1, (.var p72.2.2.2.1, ()))))
           (.jump Js6.1 ())))
      (.jump Js6.1 ())) .nil)
  (fun Js5 => .jump Js5.1 (.var tk2p1, (.imm 0, (.var lr0, (.var lcnt0, (.imm false, ()))))))

private theorem fidFs_subsumption_wp (Γ : Env)
  (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 alen0 : Nat} {fuel0 : BitVec 64}
    {refs0 : List Nat} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {s2 sk : FullState}
    {mk : Mem 64} {pRepr pArena pVals pLitMark pTmp pScr pW1 pW2 tl tk2p1 : Val i64}
    {msz cref lr0 lcnt0 : Val i32} {cRed : Val .bool} {ncand occ_pos : Nat}
    {kExit : Tup Val [i64, i32, i32, i32, .bool] → Expr Val Cont [i64]}
    (hRepr : pRepr = c.pRepr) (hAr : pArena = c.pArena) (hVals : pVals = c.pVals)
    (hLm : pLitMark = c.pLitMark) (hTmp : pTmp = c.pTmp) (hScr : pScr = c.pScratchBuf)
    (hW1 : pW1 = c.pWorkStk1) (hW2 : pW2 = c.pWorkStk2)
    (hb_k : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk)
    (hark : sk.core.arena = s2.core.arena) (hvlk : sk.core.vals = s2.core.vals)
    (hinck : sk.core.inconsistent = 0#64) (hscrk : sk.scratch = s2.scratch)
    (htkk_le : tk2p1.toNat ≤ tl.toNat) (hlr0_lt : lr0.toNat < 2 * cv0) (hmsz_cv : msz.toNat ≤ cv0)
    (htmp_lt : ∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0)
    (hlm_ok : ∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0))
    (hocc2 : FidFsOccOk refs0 (2 * cv0) (2 * ncand) occ_pos
      s2.scratch.work_stk1 s2.scratch.scratch_buf)
    (hm_k : (FullMem c sk ⋆ R) mk)
    (hk : ∀ (tk_k : Val i64) (ki lr lcnt : Val i32) (sub_k : Bool) (s_cl : FullState)
      (m_cl : Mem 64),
      tk_k.toNat ≤ tl.toNat → lr.toNat < 2 * cv0 →
      FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat s_cl →
      (FullMem c s_cl ⋆ R) m_cl → wp Γ Q X (kExit (tk_k, ki, lr, lcnt, sub_k, ())) m_cl) :
    wp Γ Q X (fidFs_subsumption_expr pRepr pArena pVals pLitMark pTmp pScr pW1 pW2
      tl tk2p1 msz cref lr0 lcnt0 cRed kExit) mk := by
  subst hRepr hAr hVals hLm hTmp hScr hW1 hW2
  have hmx := c.hmaxv; have hac := c.harena; have hsc := c.hscr; unfold dimacsBound at hmx hac hsc
  have hcv_le : cv0 ≤ c.max_vars := by rw [← hb_k.hcv]; exact hb_k.hlen.core_ok.cur_vars_le
  unfold fidFs_subsumption_expr
  refine wp_loop_inv (ts := [i64, i32, i32, i32, .bool])
    (fun (tk_k, ki, lr, _lcnt, _sub_k, ()) mk_s => ∃ sk_s : FullState,
      ki.toNat ≤ msz.toNat ∧ tk_k.toNat ≤ tl.toNat ∧ lr.toNat < 2 * cv0 ∧
      FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sk_s ∧
        (FullMem c sk_s ⋆ R) mk_s)
    (fun (_, ki, _, _, _, ()) _ => msz.toNat - ki.toNat)
    (fun Jsub hJsub => by
      c0_hsteps!; exact hJsub (tk2p1, 0#32, lr0, lcnt0, false, ()) mk
        ⟨sk, Nat.zero_le _, htkk_le, hlr0_lt,
         ⟨hb_k, hark, hvlk, rfl, rfl, hinck, hscrk, hlm_ok⟩, hm_k⟩)
    (fun Jsub (tk_k, ki, lr, lcnt, sub_k, ()) mk_s ⟨sk_s, hki_le, htkk_le, hlr_lt, hscan,
      hmks⟩ ihsub => ?_)
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () m_cl => ∃ s_cl : FullState, tk_k.toNat ≤ tl.toNat ∧
      lr.toNat < 2 * cv0 ∧ FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat s_cl ∧
      (FullMem c s_cl ⋆ R) m_cl)
    (fun _ ⟨⟩ m_cl ⟨s_cl, ht1, ht2, hsc_cl, hm_cl⟩ => by
      c0_hsteps!; exact hk tk_k ki lr lcnt sub_k s_cl m_cl ht1 ht2 hsc_cl hm_cl)
    ?_
  · intro Js6 hJs6; c0_hstep
    c0_hsplit; rotate_left 1
    · c0_hsteps!; exact hJs6 () mk_s ⟨sk_s, htkk_le, hlr_lt, hscan, hmks⟩
    have hki_lt : ki.toNat < msz.toNat := hc
    have hki1 : (ki + 1#32).toNat = ki.toNat + 1 := by bv_omega
    clear hc; c0_hsplit
    · c0_hsteps!; exact hJs6 () mk_s ⟨sk_s, htkk_le, hlr_lt, hscan, hmks⟩
    clear hc; c0_hsplit; rotate_left 1
    · c0_hsteps!; exact hJs6 () mk_s ⟨sk_s, htkk_le, hlr_lt, hscan, hmks⟩
    clear hc
    have hki_tmp : ki.toNat < sk_s.core.tmp.length := by
      have := hscan.hb.hlen.core_ok.tmp_len_arr; omega
    have hki_z : (ki.setWidth 64).toNat = ki.toNat := bv_zext32_toNat ki
    have hki_tmp_z : (ki.setWidth 64).toNat < sk_s.core.tmp.length := by rw [hki_z]; exact hki_tmp
    let rk := sk_s.core.tmp[(ki.setWidth 64).toNat]'hki_tmp_z
    have hrk_lt : rk.toNat < 2 * cv0 := by
      have h := htmp_lt ki.toNat hki_lt; dsimp only [rk]
      rwa [← hscan.htmp, List.getElem?_eq_getElem hki_tmp, Option.getD_some,
        ← list_getElem_congr hki_z hki_tmp_z hki_tmp] at h
    have hrk_z : (rk.setWidth 64).toNat = rk.toNat := bv_zext32_toNat rk
    have hrk_w1 : (rk.setWidth 64).toNat < sk_s.scratch.work_stk1.length := by
      rw [hrk_z, hscan.hb.hlen.scratch_ok.work_stk1_len]; omega
    have hrk_w2 : (rk.setWidth 64).toNat < sk_s.scratch.work_stk2.length := by
      rw [hrk_z, hscan.hb.hlen.scratch_ok.work_stk2_len]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i32, i32]) (fun (lr', _lcnt', ()) mlr =>
      mlr = mk_s ∧ lr'.toNat < 2 * cv0)
      ?_ (fun Jlr hJlr => by
        c0_hsplit
        · c0_hsteps!
          exact hJlr (rk, sk_s.scratch.work_stk2[(rk.setWidth 64).toNat]'hrk_w2, ()) mk_s ⟨rfl,
            hrk_lt⟩
        · c0_hsteps!; exact hJlr (lr, lcnt, ()) mk_s ⟨rfl, hlr_lt⟩)
    rintro _ ⟨lr', lcnt', ⟨⟩⟩ mlr ⟨hmlr, hlr'_lt⟩; subst mlr
    c0_hsteps_nogrp
    let nd0 := sk_s.scratch.work_stk1[(rk.setWidth 64).toNat]'hrk_w1
    have hnd0_ok : FidFsOccPtrOk (2 * ncand) occ_pos nd0 := by
      have h := hocc2.2.2.2.1 rk.toNat hrk_lt; dsimp only [nd0]; rw [← hscan.hscr] at h
      rwa [List.getElem?_eq_getElem (by rw [← hrk_z]; exact hrk_w1), Option.getD_some,
        ← list_getElem_congr hrk_z hrk_w1 _] at h
    refine wp_join_group (ts := [i64, .bool, i32])
      (fun (tk_n', _sub_n', _nd', ()) mnd_e => ∃ s_ne : FullState, tk_n'.toNat ≤ tl.toNat ∧
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat s_ne ∧
          (FullMem c s_ne ⋆ R) mnd_e)
      (fun _ ⟨tk_n', sub_n', _, ⟨⟩⟩ mnd_e ⟨s_ne, htkn', hsc_ne, hm_ne⟩ => by
        c0_hsteps!; exact ihsub (tk_n', ki + 1#32, lr', lcnt', sub_n', ()) mnd_e
          (by dsimp only; omega) ⟨s_ne, by omega, htkn', hlr'_lt, hsc_ne, hm_ne⟩)
      ?_
    intro Jnd_ex hJnd_ex
    refine wp_loop_inv (ts := [i64, i32])
      (fun (tk_n, nd, ()) mnd => ∃ s_nd : FullState, tk_n.toNat ≤ tl.toNat ∧
        FidFsOccPtrOk (2 * ncand) occ_pos nd ∧
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat s_nd ∧
          (FullMem c s_nd ⋆ R) mnd)
      (fun (tk_n, _, ()) _ => tl.toNat - tk_n.toNat)
      (fun Jnd hJnd => by c0_hsteps!; exact hJnd (tk_k, nd0, ()) mk_s ⟨sk_s, htkk_le, hnd0_ok,
        hscan, hmks⟩)
      (fun Jnd (tk_n, nd, ()) mnd ⟨s_nd, htkn_le, hnd_ok, hsc_nd, hm_nd⟩ ihnd => ?_)
    c0_hsplit; rotate_left 1
    · c0_hsteps!; exact hJnd_ex (tk_n, sub_k, nd, ()) mnd ⟨s_nd, htkn_le, hsc_nd, hm_nd⟩
    have hnd_ne : nd ≠ 0xFFFFFFFF#32 := hc; clear hc; c0_hsplit; rotate_left 1
    · c0_hsteps!; exact hJnd_ex (tk_n, sub_k, nd, ()) mnd ⟨s_nd, htkn_le, hsc_nd, hm_nd⟩
    have htkn_lt : tk_n.toNat < tl.toNat := hc
    have htkn1 : (tk_n + 1#64).toNat = tk_n.toNat + 1 := by bv_omega
    clear hc; obtain ⟨hnd_lo, hnd_hi, hnd_ev⟩ := hnd_ok.resolve_left hnd_ne
    have hnd_z : (nd.setWidth 64).toNat = nd.toNat := bv_zext32_toNat nd
    have hnd1_n : (nd.setWidth 64 + 1#64).toNat = nd.toNat + 1 := by bv_omega
    have hs2_len : s2.scratch.scratch_buf.length = c.scratch_cap := by
      rw [← hscrk]; exact hb_k.hlen.scratch_ok.scratch_buf_len
    have hnd_scr : (nd.setWidth 64).toNat < s_nd.scratch.scratch_buf.length := by
      rw [hnd_z, hsc_nd.hb.hlen.scratch_ok.scratch_buf_len]; have := hocc2.2.1; omega
    have hnd1_scr : (nd.setWidth 64 + 1#64).toNat < s_nd.scratch.scratch_buf.length := by
      rw [hnd1_n, hsc_nd.hb.hlen.scratch_ok.scratch_buf_len]; have := hocc2.2.1; omega
    let dref := s_nd.scratch.scratch_buf[(nd.setWidth 64).toNat]'hnd_scr
    let nxt := s_nd.scratch.scratch_buf[(nd.setWidth 64 + 1#64).toNat]'hnd1_scr
    obtain ⟨hdref_ref0, hnxt_ok⟩ : dref.toNat ∈ refs0 ∧ FidFsOccPtrOk (2 * ncand) occ_pos nxt := by
      obtain ⟨h1, h2⟩ := hocc2.2.2.2.2 nd.toNat hnd_lo hnd_hi hnd_ev; rw [← hsc_nd.hscr] at h1 h2
      dsimp only [dref, nxt]
      rw [List.getElem?_eq_getElem (by rw [← hnd_z]; exact hnd_scr), Option.getD_some,
        ← list_getElem_congr hnd_z hnd_scr _] at h1
      rw [List.getElem?_eq_getElem (by rw [← hnd1_n]; exact hnd1_scr), Option.getD_some,
        ← list_getElem_congr hnd1_n hnd1_scr _] at h2
      exact ⟨h1, h2⟩
    obtain ⟨hdr_arr0, hdr_arr2, hdr2_n, hdr_bd0⟩ := hsc_nd.hb.cr_ar hdref_ref0
    have hdr_z : (dref.setWidth 64).toNat = dref.toNat := bv_zext32_toNat dref
    have hdr_arr0_z : (dref.setWidth 64).toNat < s_nd.core.arena.length := by
      rw [hdr_z]; exact hdr_arr0
    let dhdr := s_nd.core.arena[(dref.setWidth 64).toNat]'hdr_arr0_z
    let dsz := s_nd.core.arena[(dref.setWidth 64 + 2#64).toNat]'hdr_arr2
    have hdhdr_eq : dhdr = s_nd.core.arena[dref.toNat]'hdr_arr0 := list_getElem_congr hdr_z _ _
    have hdsz_eq : fullArenaClauseSizeCore s_nd.core dref.toNat = dsz.toNat := by
      unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (list_getElem_congr hdr2_n.symm _ _)
    c0_hsteps_nogrp
    refine wp_join_group (ts := [.bool])
      (fun _ md => ∃ sd : FullState,
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sd ∧ (FullMem c sd ⋆ R) md)
      (fun _ _ md ⟨sd, hsd, hmd⟩ => by
        c0_hsteps!; exact ihnd (tk_n + 1#64, nxt, ()) md (by dsimp only; omega)
          ⟨sd, by omega, hnxt_ok, hsd, hmd⟩)
      ?_
    intro Jskip_d hJskip_d; c0_hsplit; rotate_left 1
    · c0_hsteps!; exact hJskip_d (sub_k, ()) mnd ⟨s_nd, hsc_nd, hm_nd⟩
    have hdgarb0 : (dhdr &&& 0x00080000#32) = 0#32 := by
      exact (by simpa only [dhdr, dref, list_getElem_congr hnd_z.symm (hnd_z ▸ hnd_scr) hnd_scr,
        list_getElem_congr hdr_z.symm hdr_arr0 hdr_arr0_z] using hc : (dhdr &&& 524288) = 0)
    clear hc; c0_hsplit; rotate_left 1
    · c0_hsteps!; exact hJskip_d (sub_k, ()) mnd ⟨s_nd, hsc_nd, hm_nd⟩
    clear hc; c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun () md => md = mnd) ?_
      (fun Jenter hJenter => by
        c0_hsplit
        · clear hc; c0_hsteps!; exact hJenter () mnd rfl
        · clear hc; c0_hsplit
          · clear hc; c0_hsteps!; exact hJskip_d (sub_k, ()) mnd ⟨s_nd, hsc_nd, hm_nd⟩
          · clear hc; c0_hsteps!; exact hJenter () mnd rfl)
    rintro _ ⟨⟩ md rfl
    have hng_d : fullArenaClauseGarbCore s_nd.core dref.toNat = false := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem hdr_arr0, Option.getD_some, ← hdhdr_eq]
      exact fid_garb_false_of_and hdgarb0
    have hdr_bd : dref.toNat + 3 + dsz.toNat ≤ alen0 := by rw [← hdsz_eq]; exact hdr_bd0
    c0_hsteps_nogrp
    refine wp_join_group (ts := [.bool, i32])
      (fun (dok, _dj, ()) mdj => ∃ sd : FullState,
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sd ∧ (FullMem c sd ⋆ R) mdj)
      (fun _ ⟨dok, _, ⟨⟩⟩ mdj ⟨sd, hsd, hmdj⟩ => by
        c0_hsplit
        · c0_hsteps!; exact hJnd_ex (tk_n + 1#64, true, nd, ()) mdj ⟨sd, by omega, hsd, hmdj⟩
        · c0_hsteps!; exact hJskip_d (sub_k, ()) mdj ⟨sd, hsd, hmdj⟩)
      ?_
    intro Jdj_ex hJdj_ex
    refine wp_loop_inv (ts := [i32])
      (fun (dj, ()) md => ∃ sd : FullState, dj.toNat ≤ dsz.toNat ∧
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sd ∧ (FullMem c sd ⋆ R) md)
      (fun (dj, ()) _ => dsz.toNat - dj.toNat)
      (fun Jd hJd => by c0_hsteps!; exact hJd (0#32, ()) md ⟨s_nd, Nat.zero_le _, hsc_nd, hm_nd⟩)
      (fun Jd (dj, ()) md ⟨sd, hdj_le, hsd, hmd⟩ ihd => ?_)
    c0_hsplit; rotate_left 1
    · c0_hsteps!; exact hJdj_ex (true, dj, ()) md ⟨sd, hsd, hmd⟩
    have hdj_lt : dj.toNat < dsz.toNat := hc; have hdj1 : (dj + 1#32).toNat = dj.toNat + 1 := by
      bv_omega
    have har_sd_nd : sd.core.arena = s_nd.core.arena := hsd.har.trans hsc_nd.har.symm
    obtain ⟨hol_arr, hol_lt⟩ := fidFs_k_lit_lt (p := dref.setWidth 64) hsd.hb har_sd_nd
      (by rw [hdr_z]; exact hdref_ref0) (by rw [hdr_z]; exact hng_d)
      (by rw [hdr_z]; exact hdsz_eq) (by rw [hdr_z]; exact hdr_bd) hdj_lt
    let ol := sd.core.arena[(dref.setWidth 64 + 3#64 + dj.setWidth 64).toNat]'hol_arr
    have hol_vl : ol.toNat < sd.core.vals.length := hsd.hb.vals_lt hol_lt
    have hol_z : (ol.setWidth 64).toNat = ol.toNat := bv_zext32_toNat ol
    have hol_vl_z : (ol.setWidth 64).toNat < sd.core.vals.length := by rw [hol_z]; exact hol_vl
    clear hc; c0_hsplit
    · c0_hsteps!; exact hJdj_ex (false, dj, ()) md ⟨sd, hsd, hmd⟩
    clear hc; c0_hsteps_nogrp
    refine wp_join_group (ts := [.bool])
      (fun (_dok', ()) m1 => ∃ sd1 : FullState,
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sd1 ∧ (FullMem c sd1 ⋆ R) m1)
      (fun _ _ m1 ⟨sd1, hsd1, hm1⟩ => by
        c0_hsteps!; exact ihd (dj + 1#32, ()) m1 (by dsimp only; omega) ⟨sd1, by omega, hsd1, hm1⟩)
      ?_
    intro Jdo hJdo; c0_hsplit; rotate_left 1
    · c0_hsteps!; exact hJdo (true, ()) md ⟨sd, hsd, hmd⟩
    clear hc; c0_hsteps!; c0_hcall hFind
    refine ⟨F_cur, 2 * cv0, sd.core.repr, ArrayField.repr.rest c sd ⋆ R,
      hsd.hb.hrepr, hol_lt, focus_full_repr hmd,
      fun ro repr_o mo hrl_o hrepr_o _ hro_lt _ hmo => ?_⟩
    let sd1 : FullState := { sd with core := { sd.core with repr := repr_o } }
    have hmo' : (FullMem c sd1 ⋆ R) mo := unfocus_full_repr hmo
    have hsd1 := hsd.with_repr (hrl_o.trans hsd.hb.hlen.core_ok.repr_len) hrepr_o
    have hro_vl : ro.toNat < sd1.core.vals.length := hsd1.hb.vals_lt hro_lt
    have hro_lm : ro.toNat < sd1.core.lit_mark.length := hsd1.hb.lm_lt hro_lt
    have hro_z : (ro.setWidth 64).toNat = ro.toNat := bv_zext32_toNat ro
    have hro_vl_z : (ro.setWidth 64).toNat < sd1.core.vals.length := by rw [hro_z]; exact hro_vl
    have hro_lm_z : (ro.setWidth 64).toNat < sd1.core.lit_mark.length := by rw [hro_z]; exact hro_lm
    c0_hsplit
    · c0_hsteps!; exact hJdj_ex (false, dj, ()) mo ⟨sd1, hsd1, hmo'⟩
    clear hc; c0_hsplit
    · clear hc; c0_hsplit
      · c0_hsteps!; exact hJdj_ex (false, dj, ()) mo ⟨sd1, hsd1, hmo'⟩
      · c0_hsteps!; exact hJdo (true, ()) mo ⟨sd1, hsd1, hmo'⟩
    · c0_hsteps!; exact hJdo (true, ()) mo ⟨sd1, hsd1, hmo'⟩

private def fidFs_pass2_expr {V : Ty → Type} {L : List Ty → Type}
    (h tl pRepr pArena pVals pLitMark pTmp pScr pW1 pW2 ncand ticksInit occInit cv64 : V i64)
    (reduceKLoop : V i64 → V i64 → V i64 → V i64 → V i64 → V i64 → V i32 → V i32 →
      L [.bool, .bool, .bool, i32, i32] → Expr V L [i64])
    (clearLmLoop : V i64 → V i64 → V i32 → Expr V L [i64] → Expr V L [i64])
    (subLoop : V i64 → V i64 → V i64 → V i64 → V i64 → V i64 → V i64 → V i64 → V i64 → V i64 →
      V i32 → V i32 → V i32 → V i32 → V .bool →
      (Tup V [i64, i32, i32, i32, .bool] → Expr V L [i64]) → Expr V L [i64]) :
    Expr V L [i64] :=
  .group (sig := [[i64, i64, i64]]) (fun Js => .cons (fun p40 =>
    .group (sig := [[]]) (fun Js1 => .cons (fun _ =>
       .group (sig := [[i64]]) (fun Jr => .cons (fun r => .ret (.var r.1, ())) .nil) fun Jr =>
       .let_ ⟨.add i64, (.var h, (.imm 1024, ()))⟩ fun pa => .load i64 (.var pa.1) fun ldi =>
       .let_ ⟨.cmp .ne i64, (.var ldi, (.imm 0, ()))⟩ fun pb =>
       .jnz (.var pb.1) (.jump Jr.1 (.imm 20, ())) (.jump Jr.1 (.imm 1, ()))) .nil) fun Js1 =>
    .let_ ⟨.cmp .ult i64, (.var p40.2.2.1, (.var ncand, ()))⟩ fun pc1 => .jnz (.var pc1.1)
      (.let_ ⟨.cmp .ult i64, (.var p40.1, (.var tl, ()))⟩ fun pc2 => .jnz (.var pc2.1)
         (.let_ ⟨.add i64, (.var h, (.imm 1024, ()))⟩ fun pa1 => .load i64 (.var pa1.1) fun ld13 =>
          .let_ ⟨.cmp .eq i64, (.var ld13, (.imm 0, ()))⟩ fun pc3 => .jnz (.var pc3.1)
            (.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun ps1 =>
             .let_ ⟨.shl i64, (.var p40.2.2.1, (.var ps1.1, ()))⟩ fun p46 =>
             .let_ ⟨.add i64, (.var p46.1, (.imm 1, ()))⟩ fun p47 =>
             .let_ ⟨.mul i64, (.var p47.1, (.imm 4, ()))⟩ fun p48 =>
             .let_ ⟨.add i64, (.var pScr, (.var p48.1, ()))⟩ fun p49 =>
               .load i32 (.var p49.1) fun cref =>
             .let_ ⟨.zext 32 64, (.var cref, ())⟩ fun p50 =>
             .let_ ⟨.mul i64, (.var p50.1, (.imm 4, ()))⟩ fun p51 =>
             .let_ ⟨.add i64, (.var pArena, (.var p51.1, ()))⟩ fun p52 =>
               .load i32 (.var p52.1) fun chdr =>
             .let_ ⟨.zext 32 64, (.var cref, ())⟩ fun p53 =>
             .let_ ⟨.add i64, (.var p53.1, (.imm 2, ()))⟩ fun p54 =>
             .let_ ⟨.mul i64, (.var p54.1, (.imm 4, ()))⟩ fun p55 =>
             .let_ ⟨.add i64, (.var pArena, (.var p55.1, ()))⟩ fun p56 =>
               .load i32 (.var p56.1) fun csz =>
             .let_ ⟨.add i64, (.var p40.1, (.imm 1, ()))⟩ fun p57 =>
             .group (sig := [[]]) (fun Js2 => .cons (fun _ =>
                .let_ ⟨.add i64, (.var p40.2.2.1, (.imm 1, ()))⟩ fun pci1 =>
                .jump Js.1 (.var p57.1, (.var p40.2.1, (.var pci1.1, ())))) .nil) fun Js2 =>
             .let_ ⟨.and i32, (.var chdr, (.imm 524288, ()))⟩ fun p58 =>
             .let_ ⟨.cmp .ne i32, (.var p58.1, (.imm 0, ()))⟩ fun p59 =>
             .jnz (.var p59.1) (.jump Js2.1 ())
               (.let_ ⟨.cmp .ult i32, (.var csz, (.imm 3, ()))⟩ fun p60 =>
                .jnz (.var p60.1) (.jump Js2.1 ())
                  (.let_ ⟨.and i32, (.var chdr, (.imm 4194304, ()))⟩ fun p61 =>
                   .let_ ⟨.cmp .ne i32, (.var p61.1, (.imm 0, ()))⟩ fun p62 =>
                   .group (sig := [[.bool, .bool, .bool, i32, i32]]) (fun Js3 => .cons (fun p63 =>
                      .group (sig := [[]]) (fun Js4 => .cons (fun _ =>
                         clearLmLoop pLitMark pTmp p63.2.2.2.1
                           (.let_ ⟨.zext 32 64, (.var cref, ())⟩ fun pm1 =>
                            .let_ ⟨.mul i64, (.var pm1.1, (.imm 4, ()))⟩ fun pm2 =>
                            .let_ ⟨.add i64, (.var pArena, (.var pm2.1, ()))⟩ fun pm3 =>
                            .let_ ⟨.or i32, (.var chdr, (.imm 524288, ()))⟩ fun pm4 =>
                            .store (t := i32) (.var pm4.1) (.var pm3.1)
                              (.let_ ⟨.add i64, (.var h, (.imm 472, ()))⟩ fun pg1 =>
                                .load i64 (.var pg1.1) fun ldg =>
                               .let_ ⟨.add i64, (.var ldg, (.imm 3, ()))⟩ fun pg2 =>
                               .let_ ⟨.zext 32 64, (.var csz, ())⟩ fun pg3 =>
                               .let_ ⟨.add i64, (.var pg2.1, (.var pg3.1, ()))⟩ fun pg4 =>
                               .let_ ⟨.add i64, (.var h, (.imm 472, ()))⟩ fun pg5 =>
                               .store (t := i64) (.var pg4.1) (.var pg5.1)
                                 (.let_ ⟨.add i64, (.var p40.2.2.1, (.imm 1, ()))⟩ fun pci1 =>
                                  .jump Js.1 (.var p57.1, (.var p40.2.1, (.var pci1.1,
                                    ()))))))) .nil)
                      fun Js4 =>
                      .jnz (.var p63.1) (.jump Js4.1 ()) (.jnz (.var p63.2.1) (.jump Js4.1 ())
                        (.jnz (.var p63.2.2.1)
                          (clearLmLoop pLitMark pTmp p63.2.2.2.1
                             (.let_ ⟨.add i64, (.var p40.2.2.1, (.imm 1, ()))⟩ fun pci1 =>
                              .jump Js.1 (.var p57.1, (.var p40.2.1, (.var pci1.1, ())))))
                          (.let_ ⟨.cmp .eq i32, (.var p63.2.2.2.1, (.imm 0, ()))⟩ fun p64 =>
                           .jnz (.var p64.1)
                             (.let_ ⟨.add i64, (.var h, (.imm 1024, ()))⟩ fun pi1 =>
                              .store (t := i64) (.imm 1) (.var pi1.1) (.ret (.imm 20, ())))
                             (.let_ ⟨.cmp .eq i32, (.var p63.2.2.2.1, (.imm 1, ()))⟩ fun p65 =>
                              .jnz (.var p65.1)
                                (.let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun pu1 =>
                                 .let_ ⟨.mul i64, (.var pu1.1, (.imm 4, ()))⟩ fun pu2 =>
                                 .let_ ⟨.add i64, (.var pTmp, (.var pu2.1, ()))⟩ fun pu3 =>
                                 .load i32 (.var pu3.1) fun u0 =>
                                 .let_ ⟨.zext 32 64, (.var u0, ())⟩ fun pu4 =>
                                 .let_ ⟨.add i64, (.var pLitMark, (.var pu4.1, ()))⟩ fun pu5 =>
                                 .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun pu6 =>
                                 .store (t := i8) (.var pu6.1) (.var pu5.1)
                                   (.let_ ⟨.zext 32 64, (.var cref, ())⟩ fun pm1 =>
                                    .let_ ⟨.mul i64, (.var pm1.1, (.imm 4, ()))⟩ fun pm2 =>
                                    .let_ ⟨.add i64, (.var pArena, (.var pm2.1, ()))⟩ fun pm3 =>
                                    .let_ ⟨.or i32, (.var chdr, (.imm 524288, ()))⟩ fun pm4 =>
                                    .store (t := i32) (.var pm4.1) (.var pm3.1)
                                      (.let_ ⟨.add i64, (.var h, (.imm 472, ()))⟩ fun pg1 =>
                                       .load i64 (.var pg1.1) fun ldg =>
                                       .let_ ⟨.add i64, (.var ldg, (.imm 3, ()))⟩ fun pg2 =>
                                       .let_ ⟨.zext 32 64, (.var csz, ())⟩ fun pg3 =>
                                       .let_ ⟨.add i64, (.var pg2.1, (.var pg3.1, ()))⟩ fun pg4 =>
                                       .let_ ⟨.add i64, (.var h, (.imm 472, ()))⟩ fun pg5 =>
                                       .store (t := i64) (.var pg4.1) (.var pg5.1)
                                         (.let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun pu7 =>
                                          .let_ ⟨.mul i64, (.var pu7.1, (.imm 4, ()))⟩ fun pu8 =>
                                          .let_ ⟨.add i64, (.var pTmp, (.var pu8.1, ()))⟩ fun pu9 =>
                                          .load i32 (.var pu9.1) fun u0b =>
                                          .call "full_add_unit" (as := [i64, i32]) (bs := [.bool])
                                            (Arg.var h, (Arg.var u0b, ())) fun pok =>
                                          .jnz (.var pok.1)
                                            (.let_ ⟨.add i64, (.var p40.2.2.1, (.imm 1,
                                              ()))⟩ fun pci1 =>
                                             .jump Js.1 (.var p57.1, (.var p40.2.1, (.var pci1.1,
                                               ()))))
                                            (.ret (.imm 20, ()))))))
                                (.let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun pl1 =>
                                 .let_ ⟨.mul i64, (.var pl1.1, (.imm 4, ()))⟩ fun pl2 =>
                                 .let_ ⟨.add i64, (.var pTmp, (.var pl2.1, ()))⟩ fun pl3 =>
                                 .load i32 (.var pl3.1) fun lr0 =>
                                 .let_ ⟨.zext 32 64, (.var lr0, ())⟩ fun pl4 =>
                                 .let_ ⟨.mul i64, (.var pl4.1, (.imm 4, ()))⟩ fun pl5 =>
                                 .let_ ⟨.add i64, (.var pW2, (.var pl5.1, ()))⟩ fun pl6 =>
                                 .load i32 (.var pl6.1) fun lcnt0 =>
                                 subLoop pRepr pArena pVals pLitMark pTmp pScr pW1 pW2 tl p57.1
                                   p63.2.2.2.1 cref lr0 lcnt0 p62.1 fun p72 =>
                                 clearLmLoop pLitMark pTmp p63.2.2.2.1
                                   (.group (sig := [[i64]]) (fun Jo => .cons (fun po =>
                                      .let_ ⟨.add i64, (.var p40.2.2.1, (.imm 1, ()))⟩ fun pci1 =>
                                      .jump Js.1 (.var p72.1, (.var po.1, (.var pci1.1, ())))) .nil)
                                    fun Jo =>
                                    .jnz (.var p72.2.2.2.2.1)
                                      (.let_ ⟨.zext 32 64, (.var cref, ())⟩ fun pm1 =>
                                       .let_ ⟨.mul i64, (.var pm1.1, (.imm 4, ()))⟩ fun pm2 =>
                                       .let_ ⟨.add i64, (.var pArena, (.var pm2.1, ()))⟩ fun pm3 =>
                                       .let_ ⟨.or i32, (.var chdr, (.imm 524288, ()))⟩ fun pm4 =>
                                       .store (t := i32) (.var pm4.1) (.var pm3.1)
                                         (.let_ ⟨.add i64, (.var h, (.imm 472, ()))⟩ fun pg1 =>
                                          .load i64 (.var pg1.1) fun ldg =>
                                          .let_ ⟨.add i64, (.var ldg, (.imm 3, ()))⟩ fun pg2 =>
                                          .let_ ⟨.zext 32 64, (.var csz, ())⟩ fun pg3 =>
                                          .let_ ⟨.add i64, (.var pg2.1, (.var pg3.1,
                                            ()))⟩ fun pg4 =>
                                          .let_ ⟨.add i64, (.var h, (.imm 472, ()))⟩ fun pg5 =>
                                          .store (t := i64) (.var pg4.1) (.var pg5.1)
                                            (.jump Jo.1 (.var p40.2.1, ()))))
                                      (.group (sig := [[i64]]) (fun Jo2 => .cons (fun po =>
                                         .jump Jo.1 (.var po.1, ())) .nil) fun Jo2 =>
                                       .let_ ⟨.add i64, (.var p40.2.1, (.imm 2, ()))⟩ fun po2 =>
                                       .let_ ⟨.add i64, (.var h, (.imm 928, ()))⟩ fun pc =>
                                       .load i64 (.var pc.1) fun scap =>
                                       .let_ ⟨.cmp .ule i64, (.var po2.1, (.var scap,
                                         ()))⟩ fun pcu =>
                                       .jnz (.var pcu.1)
                                         (.let_ ⟨.mul i64, (.var p40.2.1, (.imm 4, ()))⟩ fun pq1 =>
                                          .let_ ⟨.add i64, (.var pScr, (.var pq1.1, ()))⟩ fun pq2 =>
                                          .store (t := i32) (.var cref) (.var pq2.1)
                                            (.let_ ⟨.add i64, (.var p40.2.1, (.imm 1,
                                              ()))⟩ fun pq3 =>
                                             .let_ ⟨.mul i64, (.var pq3.1, (.imm 4, ()))⟩ fun pq4 =>
                                             .let_ ⟨.add i64, (.var pScr, (.var pq4.1,
                                               ()))⟩ fun pq5 =>
                                             .let_ ⟨.zext 32 64, (.var p72.2.2.1, ())⟩ fun pq6 =>
                                             .let_ ⟨.mul i64, (.var pq6.1, (.imm 4, ()))⟩ fun pq7 =>
                                             .let_ ⟨.add i64, (.var pW1, (.var pq7.1,
                                               ()))⟩ fun pq8 =>
                                             .load i32 (.var pq8.1) fun hd =>
                                             .store (t := i32) (.var hd) (.var pq5.1)
                                               (.let_ ⟨.zext 32 64, (.var p72.2.2.1, ())⟩ fun pq9 =>
                                                .let_ ⟨.mul i64, (.var pq9.1, (.imm 4,
                                                  ()))⟩ fun pq10 =>
                                                .let_ ⟨.add i64, (.var pW1, (.var pq10.1,
                                                  ()))⟩ fun pq11 =>
                                                .let_ ⟨.trunc 64 32, (.var p40.2.1, ())⟩ fun pq12 =>
                                                .store (t := i32) (.var pq12.1) (.var pq11.1)
                                                  (.let_ ⟨.zext 32 64, (.var p72.2.2.1,
                                                    ())⟩ fun pr1 =>
                                                   .let_ ⟨.mul i64, (.var pr1.1, (.imm 4,
                                                     ()))⟩ fun pr2 =>
                                                   .let_ ⟨.add i64, (.var pW2, (.var pr2.1,
                                                     ()))⟩ fun pr3 =>
                                                   .let_ ⟨.zext 32 64, (.var p72.2.2.1,
                                                     ())⟩ fun pr4 =>
                                                   .let_ ⟨.mul i64, (.var pr4.1, (.imm 4,
                                                     ()))⟩ fun pr5 =>
                                                   .let_ ⟨.add i64, (.var pW2, (.var pr5.1,
                                                     ()))⟩ fun pr6 =>
                                                   .load i32 (.var pr6.1) fun oc =>
                                                   .let_ ⟨.add i32, (.var oc, (.imm 1,
                                                     ()))⟩ fun oc1 =>
                                                   .store (t := i32) (.var oc1.1) (.var pr3.1)
                                                     (.let_ ⟨.add i64, (.var p40.2.1, (.imm 2,
                                                       ()))⟩ fun po2' =>
                                                      .jump Jo2.1 (.var po2'.1, ()))))))
                                         (.jump Jo2.1 (.var p40.2.1, ())))))))))) .nil)
                   fun Js3 => reduceKLoop pRepr pArena pVals pLitMark pTmp cv64 cref csz Js3.1)))
            (.jump Js1.1 ())) (.jump Js1.1 ())) (.jump Js1.1 ())) .nil)
  fun Js => .jump Js.1 (.var ticksInit, (.var occInit, (.imm 0, ())))

private theorem fidFs_pass2_wp (Γ : Env) (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 alen0 : Nat} {fuel0 : BitVec 64}
    {refs0 : List Nat} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {sio : FullState}
    {mio : Mem 64} {h tl pRepr pArena pVals pLitMark pTmp pScr pW1 pW2 ncand ticksInit occInit :
      Val i64}
    (hh : h = c.hdr) (hRepr : pRepr = c.pRepr) (hAr : pArena = c.pArena) (hVals : pVals = c.pVals)
    (hLm : pLitMark = c.pLitMark) (hTmp : pTmp = c.pTmp) (hScr : pScr = c.pScratchBuf)
    (hW1 : pW1 = c.pWorkStk1) (hW2 : pW2 = c.pWorkStk2)
    (hoccInit_eq : occInit.toNat = 2 * ncand.toNat) (hnc_gt1 : 1 < ncand.toNat)
    (hnc_le : ncand.toNat ≤ c.scratch_cap / 4) (htk_le : ticksInit.toNat ≤ tl.toNat)
    (htl_le : tl.toNat ≤ 0x7FFFFFFFFFFFFFFF) (hdio : FullDenseInvW c F0 F_cur sio)
    (hcvo : sio.core.cur_vars = cv0) (halo : sio.core.arena_len = alen0)
    (hflo : sio.core.fuel = fuel0) (hrefso : fullArenaClauseRefs sio = refs0)
    (hrepro : FullCongReprInv F_cur (2 * cv0) sio.core.repr)
    (hpairso : CongPairsOk (fun _ cr => cr.toNat ∈ refs0) sio.scratch.scratch_buf ncand.toNat)
    (hocco : FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) occInit.toNat
      sio.scratch.work_stk1 sio.scratch.scratch_buf)
    (hmio : (FullMem c sio ⋆ R) mio)
    (hQ : ∀ r s' m', FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = cv0 →
      s'.core.fuel = fuel0 → FullCongReprInv F_cur (2 * cv0) s'.core.repr →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (fidFs_pass2_expr h tl pRepr pArena pVals pLitMark pTmp pScr pW1 pW2
      ncand ticksInit occInit (BitVec.ofNat 64 cv0)
      (fun a b d e f g cref csz J => fidFs_reduce_k_expr a b d e f g cref csz J)
      fidFs_clearLm_expr fidFs_subsumption_expr) mio := by
  subst hh hRepr hAr hVals hLm hTmp hScr hW1 hW2
  have hmx := c.hmaxv; have hac := c.harena; have hsc := c.hscr; unfold dimacsBound at hmx hac hsc
  have hcv_le : cv0 ≤ c.max_vars := by rw [← hcvo]; exact hdio.1.core_ok.cur_vars_le
  unfold fidFs_pass2_expr
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (tk2, occ_pos, ci, ()) m2 => ∃ s2 : FullState, ci.toNat ≤ ncand.toNat ∧
      tk2.toNat ≤ tl.toNat ∧ occ_pos.toNat ≤ c.scratch_cap ∧ FullDenseInvW c F0 F_cur s2 ∧
      s2.core.cur_vars = cv0 ∧ s2.core.arena_len = alen0 ∧ s2.core.fuel = fuel0 ∧
      fullArenaClauseRefs s2 = refs0 ∧ FullCongReprInv F_cur (2 * cv0) s2.core.repr ∧
      CongPairsOk (fun _ cr => cr.toNat ∈ refs0) s2.scratch.scratch_buf ncand.toNat ∧
      FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) occ_pos.toNat
        s2.scratch.work_stk1 s2.scratch.scratch_buf ∧ (FullMem c s2 ⋆ R) m2)
    (fun (_, _, ci, ()) _ => ncand.toNat - ci.toNat)
    (fun Jc2 hJc2 => by
      c0_hsteps!; exact hJc2 (ticksInit, occInit, 0#64, ()) mio
        ⟨sio, Nat.zero_le _, htk_le, by omega, hdio, hcvo, halo, hflo, hrefso, hrepro,
         hpairso, hocco, hmio⟩)
    (fun Jc2 (tk2, occ_pos, ci, ()) m2 ⟨s2, hci_le, htk2_le, hoccp_le, hd2, hcv2, hal2, hfl2,
      hrefs2, hrepr2, hpairs2, hocc2, hm2⟩ ihc2 => ?_)
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () mf => ∃ sf : FullState,
      FullDenseInvW c F0 F_cur sf ∧ sf.core.cur_vars = cv0 ∧ sf.core.fuel = fuel0 ∧
      FullCongReprInv F_cur (2 * cv0) sf.core.repr ∧ (FullMem c sf ⋆ R) mf)
    (fun _ ⟨⟩ mf ⟨sf, hdf, hcvf, hflf, hreprf, hmf⟩ => by
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun (r, ()) mr => mr = mf ∧ (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
        (fun _ ⟨r, ⟨⟩⟩ mr ⟨hmr, hr_dom, huns⟩ => by
          c0_hsteps!; exact hQ r sf mr hdf hcvf hflf hreprf hr_dom huns (hmr ▸ hmf))
        (fun Jrf hJrf => by
          c0_hsplit
          · c0_hsteps!
            exact hJrf (20#64, ()) mf ⟨rfl, Or.inr rfl, fun _ => unsat_of_inconsistent_w hdf.2.1 hc⟩
          · c0_hsteps!; exact hJrf (1#64, ()) mf ⟨rfl, Or.inl rfl, fun h => by cases h⟩))
    ?_
  intro Jexit2 hJexit2
  have hpass2_exit : Jexit2 () m2 := hJexit2 () m2 ⟨s2, hd2, hcv2, hfl2, hrepr2, hm2⟩
  c0_hsplit; rotate_left 1; · c0_hsteps!; exact hpass2_exit
  have hci_lt : ci.toNat < ncand.toNat := hc
  have hci1_n : (ci + 1#64).toNat = ci.toNat + 1 := by bv_omega
  clear hc; c0_hsplit; rotate_left 1; · c0_hsteps!; exact hpass2_exit
  have htk2_lt : tk2.toNat < tl.toNat := hc
  have htk21_n : (tk2 + 1#64).toNat = tk2.toNat + 1 := by bv_omega
  clear hc; c0_hsplit; rotate_left 1; · c0_hsteps!; exact hpass2_exit
  have hinc2 : s2.core.inconsistent = 0#64 := hc
  clear hc Jexit2 hJexit2 hpass2_exit
  have hci21_n : ((ci <<< BitVec.signExtend 64 1#32) + 1#64).toNat = 2 * ci.toNat + 1 := by
    rw [BitVec.toNat_add, bv64_shl_s1 ci (by omega), show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hscr_len2 := hd2.1.scratch_ok.scratch_buf_len
  have hci21_arr :
    ((ci <<< BitVec.signExtend 64 1#32) + 1#64).toNat < s2.scratch.scratch_buf.length := by
    rw [hci21_n]; omega
  let cref := s2.scratch.scratch_buf[((ci <<< BitVec.signExtend 64 1#32) + 1#64).toNat]'hci21_arr
  have hci21_c0 : (ci <<< (1 : Nat) + (1 : BitVec 64)).toNat =
      ((ci <<< BitVec.signExtend 64 1#32) + 1#64).toNat := by bv_omega
  have hcref_c0 : s2.scratch.scratch_buf[(ci <<< (1 : Nat) +
    (1 : BitVec 64)).toNat]'(hci21_c0 ▸ hci21_arr) =
      cref := list_getElem_congr hci21_c0 _ _
  have hcref_ref0 : cref.toNat ∈ refs0 := by
    have h :=
      hpairs2 ci.toNat hci_lt; have h21_lt : 2 * ci.toNat + 1 < s2.scratch.scratch_buf.length := by
        omega
    rw [List.getElem?_eq_getElem h21_lt, Option.getD_some] at h
    dsimp only [cref]; rwa [list_getElem_congr hci21_n hci21_arr h21_lt]
  have hcref_ref : cref.toNat ∈ fullArenaClauseRefs s2 := hrefs2.symm ▸ hcref_ref0
  obtain ⟨hb_2, hlm_2⟩ := FidFsBaseOk.of_dense hd2 hcv2 hal2 hfl2 hrefs2 hrepr2
  obtain ⟨hcr_arr0, hcr_arr2, hcr2_n, hcr_bd0⟩ := hb_2.cr_ar hcref_ref0
  have hcr_z : (cref.setWidth 64).toNat = cref.toNat := bv_zext32_toNat cref
  have hcr_arr0_z : (cref.setWidth 64).toNat < s2.core.arena.length := by rw [hcr_z]; exact hcr_arr0
  let chdr := s2.core.arena[(cref.setWidth 64).toNat]'hcr_arr0_z
  let csz := s2.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr_arr2
  have hchdr_eq : chdr = s2.core.arena[cref.toNat]'hcr_arr0 := list_getElem_congr hcr_z _ _
  have hcsz_eq : fullArenaClauseSizeCore s2.core cref.toNat = csz.toNat := by
    unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hcr2_n.symm _ _)
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () msk => msk = m2)
    (fun _ ⟨⟩ msk hmsk => by
      c0_hsteps!; exact ihc2 (tk2 + 1#64, occ_pos, ci + 1#64, ()) msk (by dsimp only; omega)
        ⟨s2, by omega, by omega, hoccp_le, hd2, hcv2, hal2, hfl2, hrefs2, hrepr2, hpairs2, hocc2,
          hmsk ▸ hm2⟩)
    ?_
  intro Jskip2 hJskip2; c0_hsplit
  · clear hc; c0_hsteps!; exact hJskip2 () m2 rfl
  have hci_idx : (2 * ci.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
      ((ci <<< BitVec.signExtend 64 1#32) + 1#64).toNat := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    exact hci21_n.symm
  have hcgarb0 : (chdr &&& 0x00080000#32) = 0#32 := by
    exact (by simpa only [chdr, cref, list_getElem_congr hci_idx (hci_idx ▸ hci21_arr) hci21_arr,
      list_getElem_congr hcr_z.symm hcr_arr0 hcr_arr0_z] using hc : (chdr &&& 524288) = 0)
  clear hc; c0_hsplit
  · clear hc; c0_hsteps!; exact hJskip2 () m2 rfl
  clear Jskip2 hJskip2
  have hcsz3 : 3 ≤ csz.toNat := by
    have hcr_rfl : s2.scratch.scratch_buf[((ci <<< BitVec.signExtend 64 1#32) +
      1#64).toNat]'hci21_arr =
        cref := rfl
    have hcr2_hc : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
        (cref.setWidth 64 + 2#64).toNat := by
      rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; bv_omega
    simpa only [csz, hcr_rfl, list_getElem_congr hci_idx (hci_idx ▸ hci21_arr) hci21_arr,
      list_getElem_congr hcr2_hc (hcr2_hc ▸ hcr_arr2) hcr_arr2,
      show BitVec.toNat (3 : BitVec 32) = 3 from rfl, Nat.not_lt] using hc
  have hng_c2 : fullArenaClauseGarb s2 cref.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_arr0, Option.getD_some, ← hchdr_eq]
    exact fid_garb_false_of_and hcgarb0
  have hcsz_cv : csz.toNat ≤ cv0 := by
    rw [← hcv2, ← hcsz_eq]
    exact fullArenaClauseSize_le_cur_vars hd2.1 hd2.2.1 hd2.2.2.2.1 hcref_ref hng_c2
  have hcr_bd : cref.toNat + 3 + csz.toNat ≤ alen0 := by rw [← hcsz_eq]; exact hcr_bd0
  clear hc; c0_hsteps_nogrp
  refine wp_join_group (ts := [.bool, .bool, .bool, i32, i32])
    (fun (sat, taut, ovf, msz, _k, ()) mk => ∃ sk : FullState,
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk ∧ sk.core.arena = s2.core.arena ∧
      sk.core.vals = s2.core.vals ∧ sk.core.inconsistent = 0#64 ∧ sk.scratch = s2.scratch ∧
      msz.toNat ≤ cv0 ∧ (∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (sat = false → taut = false → ovf = false →
        ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → ∀ j < csz.toNat,
          evalLitVal α (sk.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat = true →
          ∃ q < msz.toNat, evalLitVal α (sk.core.tmp[q]?.getD 0#32).toNat = true) ∧
      (FullMem c sk ⋆ R) mk)
    ?_
    (fun Jk2_ex hJk2_ex => fidFs_reduce_k_wp Γ hFind rfl rfl rfl rfl rfl rfl hb_2 hinc2 hlm_2
      hcref_ref0 hng_c2 hcsz_eq hcr_bd hm2 fun sat taut ovf msz k_r mk h =>
        hJk2_ex (sat, taut, ovf, msz, k_r, ()) mk h)
  rintro _ ⟨sat, taut, ovf, msz, _k, ⟨⟩⟩ mk
    ⟨sk, hbk, hark, hvlk, hinck, hscrk, hmsz_cv, htmp_lt, hlm_ok, hsem_ok, hmk⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () mm => mm = mk ∧ (sat = true ∨ taut = true))
    (fun _ ⟨⟩ mm ⟨hmm, _⟩ => by
      refine fidFs_clearLm_wp Γ rfl rfl (hmm ▸ hmk) hbk hark rfl hscrk hmsz_cv htmp_lt
        (fidFs_lm_clear_from_zero hlm_ok)
        fun sc _ _ harc _ hscrc hdc hcvc halc hflc hrefsc hreprc hm => ?_
      have hcr_c : cref.toNat < sc.core.arena.length := by rw [harc]; exact hcr_arr0
      have hchdr_c : sc.core.arena[cref.toNat]'hcr_c = chdr := by
        rw [hchdr_eq]; exact list_eq_getElem_congr harc _ _
      c0_hsteps!
      obtain ⟨hd_mg, hmg_refs⟩ := fid_fs_markGarb_dense' hdc (hrefsc.symm ▸ hcref_ref0) hcr_c
        (sc.core.arena_garbage + 3#64 + csz.setWidth 64)
      rw [hchdr_c] at hd_mg hmg_refs
      exact ihc2 (tk2 + 1#64, occ_pos, ci + 1#64, ()) _ (by dsimp only; omega)
        ⟨_, by omega, by omega, hoccp_le, hd_mg, hcvc, halc, hflc, hmg_refs.trans hrefsc,
         hreprc, hscrc.symm ▸ hpairs2, hscrc.symm ▸ hocc2,
         by simpa only [hcref_c0, hcr_z, ← hchdr_eq, show (csz : BitVec 32) =
             s2.core.arena[(cref.setWidth 64 + (2 : BitVec 64)).toNat]'hcr_arr2 from rfl,
             show (3#64 : BitVec 64) = 3 from rfl, show (2#64 : BitVec 64) = 2 from rfl,
             show (0x00080000#32 : BitVec 32) = 524288 from rfl] using hm⟩)
    ?_
  intro Jst2 hJst2; c0_hsplit
  · c0_hsteps!; exact hJst2 () mk ⟨rfl, Or.inl hc⟩
  have hsat_f : sat = false := hc; clear hc; c0_hsplit
  · c0_hsteps!; exact hJst2 () mk ⟨rfl, Or.inr hc⟩
  have htaut_f : taut = false := hc; clear hc Jst2 hJst2; c0_hsplit
  · clear hc; refine fidFs_clearLm_wp Γ rfl rfl hmk hbk hark rfl hscrk hmsz_cv htmp_lt
      (fidFs_lm_clear_from_zero hlm_ok)
      fun sc mc _ _ _ hscrc hdc hcvc halc hflc hrefsc hreprc hmc => by
        c0_hsteps!; exact ihc2 (tk2 + 1#64, occ_pos, ci + 1#64, ()) mc (by dsimp only; omega)
          ⟨sc, by omega, by omega, hoccp_le, hdc, hcvc, halc, hflc, hrefsc, hreprc,
           hscrc.symm ▸ hpairs2, hscrc.symm ▸ hocc2, hmc⟩
  have hovf_f : ovf = false := hc; clear hc; c0_hsplit
  · have hmsz0 : msz.toNat = 0 := by have := hc; bv_omega
    obtain ⟨hdk, hcvk, _, hflk, hrefsk, hreprk⟩ := hbk.to_dense fun l hl =>
      (hlm_ok l hl).elim id fun ⟨j, hj, _⟩ => by omega
    have hcr_k : cref.toNat < sk.core.arena.length := by rw [hark]; exact hcr_arr0
    have hng_k : fullArenaClauseGarb sk cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem hcr_k, Option.getD_some,
        list_eq_getElem_congr hark hcr_k hcr_arr0, ← hchdr_eq]; exact fid_garb_false_of_and hcgarb0
    have hsz_k : fullArenaClauseSizeCore sk.core cref.toNat = csz.toNat := by
      unfold fullArenaClauseSizeCore; rw [hark, ← hcsz_eq]; rfl
    have hu_cur : (cnfOfClauses F_cur).Unsat :=
      fidFs_msz0_unsat hdk.1 hdk.2.1 (hrefsk.symm ▸ hcref_ref0) hng_k hsz_k fun α hα j hj hl => by
        obtain ⟨q, hq, _⟩ := hsem_ok hsat_f htaut_f hovf_f α hα j hj hl; omega
    clear hc; c0_hsteps!
    exact hQ 20#64 _ _ (fid_denseInvW_with_inc hdk hu_cur 1#64) hcvk hflk
      hreprk (Or.inr rfl) (fun _ => hdk.2.1.ext_sound.2 hu_cur) ‹_›
  have hmsz_ne0 : msz.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
  clear hc; c0_hsplit
  · have hmsz1 : msz.toNat = 1 := by have := hc; bv_omega
    have h0_tmp : 0 < sk.core.tmp.length := by have := hbk.hlen.core_ok.tmp_len_arr; omega
    let u0 := sk.core.tmp[0]'h0_tmp
    have hu0_lt : u0.toNat < 2 * cv0 := by
      have h := htmp_lt 0 (by omega); rwa [List.getElem?_eq_getElem h0_tmp, Option.getD_some] at h
    have hu0_lm : u0.toNat < sk.core.lit_mark.length := hbk.lm_lt hu0_lt
    have hu0_z : (u0.setWidth 64).toNat = u0.toNat := bv_zext32_toNat u0
    have hcr_k : cref.toNat < sk.core.arena.length := by rw [hark]; exact hcr_arr0
    have hchdr_k : sk.core.arena[cref.toNat]'hcr_k = chdr := by
      rw [hchdr_eq]; exact list_eq_getElem_congr hark _ _
    have hlm1 : ∀ l < 2 * c.max_vars, (sk.core.lit_mark.set u0.toNat 0#8)[l]?.getD 0#8 = 0#8 :=
      fidFs_lm_clear_done (msz := 1) (tmp := sk.core.tmp)
        (fidFs_lm_clear_step (k := 0) (by omega) h0_tmp hu0_lm
          (fidFs_lm_clear_from_zero (hmsz1 ▸ hlm_ok)))
    let sk_cl : FullState :=
      { sk with core := { sk.core with lit_mark := sk.core.lit_mark.set u0.toNat 0#8 } }
    have hbk_cl := hbk.with_lm (lm' := sk.core.lit_mark.set u0.toNat 0#8)
      (by simp [hbk.hlen.core_ok.lit_mark_len])
    obtain ⟨hd_cl, hcv_cl, hal_cl, hfl_cl, hrefs_cl, hrepr_cl⟩ := hbk_cl.to_dense hlm1
    have hng_cl : fullArenaClauseGarb sk_cl cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem hcr_k, Option.getD_some, hchdr_k]
      exact fid_garb_false_of_and hcgarb0
    have hsz_cl : fullArenaClauseSizeCore sk_cl.core cref.toNat = csz.toNat := by
      change fullArenaClauseSizeCore sk.core cref.toNat = csz.toNat
      unfold fullArenaClauseSizeCore; rw [hark, ← hcsz_eq]; rfl
    have hent_u : (cnfOfClauses F_cur).EntailsClause (cnfClause [u0.toNat]) :=
      fidFs_msz1_entails hd_cl.1 hd_cl.2.1 (hrefs_cl.symm ▸ hcref_ref0) hng_cl hsz_cl
        fun α hα j hj hl => by
          obtain ⟨q, hq, hqt⟩ := hsem_ok hsat_f htaut_f hovf_f α hα j hj hl
          obtain rfl : q = 0 := by omega
          rwa [List.getElem?_eq_getElem h0_tmp, Option.getD_some] at hqt
    have h0_bv_tmp : (BitVec.ofNat 64 0).toNat < sk.core.tmp.length := by simpa using h0_tmp
    have hu0_bv_eq : sk.core.tmp[(BitVec.ofNat 64 0).toNat]'h0_bv_tmp = u0 :=
      list_getElem_congr (by decide) _ _
    clear hc; c0_hsteps!
    obtain ⟨hd_mg, hmg_refs⟩ := fid_fs_markGarb_dense' hd_cl (hrefs_cl.symm ▸ hcref_ref0) hcr_k
      (sk_cl.core.arena_garbage + 3#64 + csz.setWidth 64)
    rw [hchdr_k] at hd_mg hmg_refs; c0_hcall hAddUnit
    refine ⟨c, F0, F_cur, _, R, rfl, hd_mg.1, hd_mg.2.1, fun _ => by rw [hu0_bv_eq]; exact hent_u,
      by simpa only [hu0_bv_eq, hu0_z, hcref_c0, hcr_z, ← hchdr_eq,
          show sk_cl.core.arena_garbage = sk.core.arena_garbage from rfl,
          show (csz : BitVec 32) = s2.core.arena[(cref.setWidth 64 +
            (2 : BitVec 64)).toNat]'hcr_arr2 from rfl,
          show (0#8 : BitVec 8) = BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 0) from rfl,
          show (3#64 : BitVec 64) = 3 from rfl, show (2#64 : BitVec 64) = 2 from rfl,
          show (0x00080000#32 : BitVec 32) = 524288 from rfl] using hm,
      fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
        phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mu hlu hwu hclu _ h_f hmu => ?_⟩
    have hdu := fid_addUnit_denseInvW hd_mg hlu hwu hclu rfl rfl rfl rfl rfl rfl rfl
    c0_hsplit
    · c0_hsteps!; exact ihc2 (tk2 + 1#64, occ_pos, ci + 1#64, ()) mu (by dsimp only; omega)
        ⟨_, by omega, by omega, hoccp_le, hdu, hcv_cl, hal_cl, hfl_cl, hmg_refs.trans hrefs_cl,
         hrepr_cl, by change CongPairsOk _ sk.scratch.scratch_buf _; rw [hscrk]; exact hpairs2,
         by change FidFsOccOk _ _ _ _ sk.scratch.work_stk1 sk.scratch.scratch_buf; rw [hscrk]
            exact hocc2, hmu⟩
    · have hu_f := h_f hc
      have hu := (hu_f.resolve_left (by rw [hu0_bv_eq, hcv_cl]; exact Nat.not_le_of_lt hu0_lt)).1
      c0_hsteps!; exact hQ 20#64 _ mu hdu hcv_cl hfl_cl hrepr_cl (Or.inr rfl) (fun _ => hu) hmu
  have hmsz_ge2 : 2 ≤ msz.toNat := by
    have : msz.toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq h); omega
  clear hc
  have h0_tmp : 0 < sk.core.tmp.length := by have := hbk.hlen.core_ok.tmp_len_arr; omega
  have h0_bv_tmp : (BitVec.ofNat 64 0).toNat < sk.core.tmp.length := by simpa using h0_tmp
  let lr0 := sk.core.tmp[(BitVec.ofNat 64 0).toNat]'h0_bv_tmp
  have hlr0_lt : lr0.toNat < 2 * cv0 := by
    have h := htmp_lt 0 (by omega); dsimp only [lr0]
    rwa [List.getElem?_eq_getElem h0_tmp, Option.getD_some,
      ← list_getElem_congr (by decide : (BitVec.ofNat 64 0).toNat = 0) h0_bv_tmp h0_tmp] at h
  have hlr0_w2 : (lr0.setWidth 64).toNat < sk.scratch.work_stk2.length := by
    rw [bv_zext32_toNat, hbk.hlen.scratch_ok.work_stk2_len]; omega
  c0_hsteps_nogrp
  refine fidFs_subsumption_wp Γ hFind rfl rfl rfl rfl rfl rfl rfl rfl hbk hark hvlk hinck hscrk
    (by change (tk2 + 1#64).toNat ≤
      tl.toNat; rw [htk21_n]; omega) hlr0_lt hmsz_cv htmp_lt hlm_ok hocc2 hmk
    fun tk_k _ lr _ sub_k s_cl m_cl htkk_le hlr_lt hsc_cl hm_cl => ?_
  refine fidFs_clearLm_wp Γ rfl rfl hm_cl hsc_cl.hb hsc_cl.har hsc_cl.htmp hsc_cl.hscr
    hmsz_cv htmp_lt (fidFs_lm_clear_from_zero hsc_cl.hlmok)
    fun sc mc _ harc _ hscrc hdc hcvc halc hflc hrefsc hreprc hmc => ?_
  have hpairs_c : CongPairsOk (fun _ cr => cr.toNat ∈ refs0) sc.scratch.scratch_buf ncand.toNat :=
    hscrc.symm ▸ hpairs2
  have hocc_c : FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) occ_pos.toNat
      sc.scratch.work_stk1 sc.scratch.scratch_buf := hscrc.symm ▸ hocc2
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (occ_pos', ()) mop => ∃ sop : FullState, occ_pos'.toNat ≤ c.scratch_cap ∧
      FullDenseInvW c F0 F_cur sop ∧ sop.core.cur_vars = cv0 ∧ sop.core.arena_len = alen0 ∧
      sop.core.fuel = fuel0 ∧ fullArenaClauseRefs sop = refs0 ∧
      FullCongReprInv F_cur (2 * cv0) sop.core.repr ∧
      CongPairsOk (fun _ cr => cr.toNat ∈ refs0) sop.scratch.scratch_buf ncand.toNat ∧
      FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) occ_pos'.toNat
        sop.scratch.work_stk1 sop.scratch.scratch_buf ∧ (FullMem c sop ⋆ R) mop)
    (fun _ ⟨occ_pos', ⟨⟩⟩ mop ⟨sop, hoccp', hdop, hcvop, halop, hflop, hrefsop, hreprop, hpop,
      hocop, hmop⟩ => by
      c0_hsteps!; exact ihc2 (tk_k, occ_pos', ci + 1#64, ()) mop (by dsimp only; omega)
        ⟨sop, by omega, htkk_le, hoccp', hdop, hcvop, halop, hflop, hrefsop, hreprop, hpop, hocop,
          hmop⟩)
    ?_
  intro Jfin hJfin; c0_hsplit
  · have hcr_c : cref.toNat < sc.core.arena.length := by rw [harc]; exact hcr_arr0
    have hchdr_c : sc.core.arena[cref.toNat]'hcr_c = chdr := by
      rw [hchdr_eq]; exact list_eq_getElem_congr harc _ _
    clear hc; c0_hsteps!
    obtain ⟨hd_mg, hmg_refs⟩ := fid_fs_markGarb_dense' hdc (hrefsc.symm ▸ hcref_ref0) hcr_c
      (sc.core.arena_garbage + 3#64 + csz.setWidth 64)
    rw [hchdr_c] at hd_mg hmg_refs
    exact hJfin (occ_pos, ()) _ ⟨_, hoccp_le, hd_mg, hcvc, halc, hflc, hmg_refs.trans hrefsc,
      hreprc, hpairs_c, hocc_c,
      by simpa only [hcref_c0, hcr_z, ← hchdr_eq,
        show (csz : BitVec 32) = s2.core.arena[(cref.setWidth 64 +
          (2 : BitVec 64)).toNat]'hcr_arr2 from rfl,
        show (3#64 : BitVec 64) = 3 from rfl, show (2#64 : BitVec 64) = 2 from rfl,
        show (0x00080000#32 : BitVec 32) = 524288 from rfl] using hm⟩
  clear hc; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (occ_pos', ()) mop => ∃ sop : FullState, occ_pos'.toNat ≤ c.scratch_cap ∧
      FullDenseInvW c F0 F_cur sop ∧ sop.core.cur_vars = cv0 ∧ sop.core.arena_len = alen0 ∧
      sop.core.fuel = fuel0 ∧ fullArenaClauseRefs sop = refs0 ∧
      FullCongReprInv F_cur (2 * cv0) sop.core.repr ∧
      CongPairsOk (fun _ cr => cr.toNat ∈ refs0) sop.scratch.scratch_buf ncand.toNat ∧
      FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) occ_pos'.toNat
        sop.scratch.work_stk1 sop.scratch.scratch_buf ∧ (FullMem c sop ⋆ R) mop)
    (fun _ ⟨occ_pos', ⟨⟩⟩ mop h => by c0_hsteps!; exact hJfin (occ_pos', ()) mop h)
    ?_
  intro Jo2 hJo2; c0_hsplit; rotate_left 1
  · c0_hsteps!; exact hJo2 (occ_pos, ()) mc
      ⟨sc, hoccp_le, hdc, hcvc, halc, hflc, hrefsc, hreprc, hpairs_c, hocc_c, hmc⟩
  have hscr_lc := hdc.1.scratch_ok.scratch_buf_len
  have hoccp2_n : (occ_pos + 2#64).toNat = occ_pos.toNat + 2 := by
    rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by have := hocc_c.2.1; omega)]
  have hoccp2_le : occ_pos.toNat + 2 ≤ c.scratch_cap := by
    have h := hc
    rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
      Nat.mod_eq_of_lt (by have := hocc_c.2.1; omega), Nat.mod_eq_of_lt (by omega)] at h
    exact h
  have hoccp_arr : occ_pos.toNat < sc.scratch.scratch_buf.length := by omega
  have hoccp1_arr : (occ_pos + 1#64).toNat < sc.scratch.scratch_buf.length := by bv_omega
  have hlr_z : (lr.setWidth 64).toNat = lr.toNat := bv_zext32_toNat lr
  have hlr_w1 : lr.toNat < sc.scratch.work_stk1.length := by
    have := hdc.1.scratch_ok.work_stk1_len; omega
  have hlr_w1_z : (lr.setWidth 64).toNat < sc.scratch.work_stk1.length := by
    rw [hlr_z]; exact hlr_w1
  have hlr_w2 : lr.toNat < sc.scratch.work_stk2.length := by
    rw [hdc.1.scratch_ok.work_stk2_len]; omega
  have hlr_w2_z : (lr.setWidth 64).toNat < sc.scratch.work_stk2.length := by
    rw [hlr_z]; exact hlr_w2
  clear hc; c0_hsteps!
  have hop_bv32 : occ_pos.setWidth 32 = BitVec.ofNat 32 occ_pos.toNat := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  have hhead_eq : sc.scratch.work_stk1[(lr.setWidth 64).toNat]'hlr_w1_z =
      sc.scratch.work_stk1[lr.toNat]'hlr_w1 := list_getElem_congr hlr_z _ _
  have hcnt_eq : sc.scratch.work_stk2[(lr.setWidth 64).toNat]'hlr_w2_z =
      sc.scratch.work_stk2[lr.toNat]'hlr_w2 := list_getElem_congr hlr_z _ _
  have hocc_push := fidFsOccOk_push hocc_c (by omega) (by omega) hcref_ref0 hlr_lt hlr_w1
  let scr_p := (sc.scratch.scratch_buf.set occ_pos.toNat cref).set (occ_pos.toNat + 1)
    (sc.scratch.work_stk1[lr.toNat]'hlr_w1)
  let w1_p := sc.scratch.work_stk1.set lr.toNat (BitVec.ofNat 32 occ_pos.toNat)
  let w2_p := sc.scratch.work_stk2.set lr.toNat (sc.scratch.work_stk2[lr.toNat]'hlr_w2 + 1#32)
  let sop : FullState :=
    { sc with scratch :=
      { sc.scratch with scratch_buf := scr_p, work_stk1 := w1_p, work_stk2 := w2_p } }
  have hpairs_push : CongPairsOk (fun _ cr => cr.toNat ∈ refs0) scr_p ncand.toNat :=
    congPairsOk_set_ge (congPairsOk_set_ge hpairs_c hocc_c.1) (by have := hocc_c.1; omega)
  have hd_push := fid_denseInvW_with_ws12 (w1' := w1_p) (w2' := w2_p)
    (fullDenseInvW_with_scr (scr' := scr_p) hdc (by simp [scr_p, hscr_lc]))
    (by simp [w1_p, hdc.1.scratch_ok.work_stk1_len]) (by simp [w2_p,
      hdc.1.scratch_ok.work_stk2_len])
  have hoccp1_n : (occ_pos + (1 : BitVec 64)).toNat = occ_pos.toNat + 1 := by bv_omega
  have hm' : (FullMem c sop ⋆ R) m := by
    dsimp only [sop, scr_p, w1_p, w2_p]
    simpa only [hcref_c0, hoccp1_n, hhead_eq, hcnt_eq, hlr_z, hop_bv32,
      show (1#32 : BitVec 32) = 1 from rfl] using hm
  exact hJo2 (occ_pos + 2#64, ()) m
    ⟨sop, by omega, hd_push, hcvc, halc, hflc, hrefsc, hreprc,
     hpairs_push, by rw [hoccp2_n]; exact hocc_push, hm'⟩

/-! ## 2. Main Entry Theorem (`full_cong_fwd_subsume_wp`) -/

public section

/-- Canonical `Func.wp` proof for `full_cong_fwd_subsume`. -/
theorem full_cong_fwd_subsume_wp (Γ : Env)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    (hSortPairs : Γ.Has "full_cong_sort_pairs_fid" Spec.fullCongSortPairsFidSpec) :
    ∀ args m Q X, Spec.fullCongFwdSubsumeSpec args m Q X →
      Func.wp Γ full_cong_fwd_subsume_body args m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hd0, hrepr0, hm0, hQ⟩
  have hmx := c.hmaxv; have hac := c.harena; have hwc := c.hwcap; have hsc := c.hscr
  unfold dimacsBound at hmx hac hwc hsc
  let cv0 := s0.core.cur_vars; let alen0 := s0.core.arena_len; let fuel0 := s0.core.fuel
  let refs0 := fullArenaClauseRefs s0
  have hcv_le : cv0 ≤ c.max_vars := hd0.1.core_ok.cur_vars_le
  unfold Func.wp full_cong_fwd_subsume_body; c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () mj => mj = m0 ∧ (s0.core.inconsistent ≠ 0#64 ∨ s0.scratch.ant_sz ≠ 0#64))
    (fun _ ⟨⟩ mj ⟨hmj, _⟩ => by
      have hmj0 : (FullMem c s0 ⋆ R) mj := hmj ▸ hm0
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun (r, ()) mr => mr = mj ∧ (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
        (fun _ ⟨r, ⟨⟩⟩ mr ⟨hmr, hr_dom, huns⟩ => by
          c0_hsteps!; exact hQ r s0 mr hd0 rfl rfl hrepr0 hr_dom huns (hmr ▸ hmj0))
        (fun Jret hJret => by
          c0_hsplit
          · c0_hsteps!
            exact hJret (20#64, ()) mj ⟨rfl, Or.inr rfl, fun _ =>
              unsat_of_inconsistent_w hd0.2.1 hc⟩
          · c0_hsteps!; exact hJret (1#64, ()) mj ⟨rfl, Or.inl rfl, fun h => by cases h⟩))
    ?_
  intro Jearly hJearly
  c0_hsplit; · c0_hsteps!; exact hJearly () m0 ⟨rfl, Or.inl hc⟩
  clear hc; c0_hsplit; · c0_hsteps!; exact hJearly () m0 ⟨rfl, Or.inr hc⟩
  clear hc Jearly hJearly; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (tl, ()) mtl =>
    mtl = m0 ∧ tl.toNat ≤ 0x7FFFFFFFFFFFFFFF) ?_
    (fun Jtl hJtl => by
      c0_hsplit
      · c0_hsteps!; exact hJtl (0x7FFFFFFFFFFFFFFF#64, ()) m0 ⟨rfl, by decide⟩
      · have hle : tick_lim.toNat ≤ 0x7FFFFFFFFFFFFFFF := by bv_omega
        c0_hsteps!; exact hJtl (tick_lim, ()) m0 ⟨rfl, hle⟩)
  rintro _ ⟨tl, ⟨⟩⟩ mtl ⟨hmtl, htl_le⟩; subst mtl
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s0 m0 hd0 rfl rfl hrepr0 (Or.inl rfl) (fun h => by cases h) hm0
  have htl_pos : 0 < tl.toNat := by bv_omega
  clear hc; c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s0 m0 hd0 rfl rfl hrepr0 (Or.inl rfl) (fun h => by cases h) hm0
  have hcap4 : 4 ≤ c.scratch_cap := by bv_omega
  clear hc; c0_hsteps_nogrp
  refine fidFs_mch_init_wp Γ hFind rfl rfl rfl rfl hd0 rfl rfl rfl rfl hrepr0 hm0
    fun _i2 hmch si2 mi2 hdi2 hcvi2 hali2 hfli2 hrefsi2 hrepri2 hmi2 => ?_
  c0_hsplit; rotate_left 1
  · c0_hsteps!
    exact hQ 1#64 si2 mi2 hdi2 hcvi2 hfli2 (hcvi2 ▸ hrepri2)
      (Or.inl rfl) (fun h => by cases h) hmi2
  clear hc; c0_hsteps_nogrp
  have hmaxc_n : ((BitVec.ofNat 64 c.scratch_cap) >>> BitVec.signExtend 64 2#32).toNat =
      c.scratch_cap / 4 := by
    rw [bv64_shr_s2, bv64_ofNat_toNat_lt (by omega)]
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (ncand, p, ticks, ()) mp => ∃ sp : FullState, ncand.toNat ≤ c.scratch_cap / 4 ∧
      p.toNat ≤ alen0 ∧ (p.toNat = alen0 ∨ p.toNat ∈ refs0) ∧ ticks.toNat ≤ tl.toNat ∧
      FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = cv0 ∧ sp.core.arena_len = alen0 ∧
      sp.core.fuel = fuel0 ∧ fullArenaClauseRefs sp = refs0 ∧
      FullCongReprInv F_cur (2 * cv0) sp.core.repr ∧
      CongPairsOk (fun _ cr => cr.toNat ∈ refs0) sp.scratch.scratch_buf ncand.toNat ∧
      (FullMem c sp ⋆ R) mp)
    (fun (_, p, _, ()) _ => alen0 - p.toNat)
    (fun Jp hJp => by
      have h0_mem : 0 = alen0 ∨ 0 ∈ refs0 := by
        rcases Nat.eq_zero_or_pos alen0 with hz | hpos
        · exact Or.inl hz.symm
        · refine Or.inr ?_; change 0 ∈ fullArenaClauseRefs s0; rw [← hrefsi2]
          exact fullArenaClauseRefs_zero_mem hdi2.2.1 (by rw [hali2]; exact hpos)
      c0_hsteps!; exact hJp (0#64, 0#64, 0#64, ()) mi2
        ⟨si2, Nat.zero_le _, Nat.zero_le _, h0_mem, Nat.zero_le _,
         hdi2, hcvi2, hali2, hfli2, hrefsi2, hrepri2, fun _ h =>
           absurd h (Nat.not_lt_zero _), hmi2⟩)
    (fun Jp (ncand, p, ticks, ()) mp ⟨sp, hnc_le, hp_le, hp_mem, htk_le, hdp, hcvp, halp, hflp,
      hrefsp, hreprp, hpairs, hmp⟩ ihp => ?_)
  · clear hdi2 hcvi2 hali2 hfli2 hrefsi2 hrepri2 hmi2; c0_hsteps_nogrp
    refine wp_join_group (ts := [])
      (fun () me => ∃ se : FullState, ncand.toNat ≤ c.scratch_cap / 4 ∧ ticks.toNat ≤ tl.toNat ∧
        FullDenseInvW c F0 F_cur se ∧ se.core.cur_vars = cv0 ∧ se.core.arena_len = alen0 ∧
        se.core.fuel = fuel0 ∧ fullArenaClauseRefs se = refs0 ∧
        FullCongReprInv F_cur (2 * cv0) se.core.repr ∧
        CongPairsOk (fun _ cr => cr.toNat ∈ refs0) se.scratch.scratch_buf ncand.toNat ∧
        (FullMem c se ⋆ R) me)
      ?_ ?_
    · rintro _ ⟨⟩ me ⟨se, hnc_le, htk_le_e, hde, hcve, hale, hfle, hrefse, hrepre, hpairs_e, hme⟩
      clear Jp hp_le hp_mem htk_le hdp hcvp halp hflp hrefsp hreprp hpairs hmp ihp
      c0_hsplit
      · c0_hsteps!; exact hQ 20#64 se me hde hcve hfle (hcve ▸ hrepre) (Or.inr rfl)
          (fun _ => unsat_of_inconsistent_w hde.2.1 hc) hme
      clear hc; c0_hsplit
      · c0_hsteps!; exact hQ 1#64 se me hde hcve hfle (hcve ▸ hrepre) (Or.inl rfl)
          (fun h => by cases h) hme
      have hnc_gt1 : 1 < ncand.toNat := by bv_omega
      clear hc; c0_hsplit
      · c0_hsteps!; exact hQ 1#64 se me hde hcve hfle (hcve ▸ hrepre) (Or.inl rfl)
          (fun h => by cases h) hme
      have htk_lt_e : ticks.toNat < tl.toNat := by bv_omega
      clear hc; have hscrl_e := hde.1.scratch_ok.scratch_buf_len
      c0_hsteps!; c0_hcall hSortPairs
      refine ⟨fun _ cr =>
        cr.toNat ∈ refs0, se.scratch.scratch_buf, ArrayField.scratch_buf.rest c se ⋆ R,
        by omega, by omega, hpairs_e, focus_full_scratch_buf hme, fun scr_s m_s hscrl_s hpairs_s _
          hm_s => ?_⟩
      let s_s : FullState := { se with scratch := { se.scratch with scratch_buf := scr_s } }
      have hm_s' : (FullMem c s_s ⋆ R) m_s := unfocus_full_scratch_buf hm_s
      have hd_s : FullDenseInvW c F0 F_cur s_s := fullDenseInvW_with_scr hde (hscrl_s.trans hscrl_e)
      have hnlits_n : ((BitVec.ofNat 64 cv0) <<< BitVec.signExtend 64 1#32).toNat = 2 * cv0 := by
        rw [bv64_shl_s1 _ (by rw [bv64_ofNat_toNat_lt (by omega)]; omega),
          bv64_ofNat_toNat_lt (by omega)]
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64])
        (fun (io, ()) mio => ∃ sio : FullState, io.toNat ≤ 2 * cv0 ∧ FullDenseInvW c F0 F_cur sio ∧
          sio.core = s_s.core ∧ sio.scratch.scratch_buf = scr_s ∧
          (∀ l < io.toNat, sio.scratch.work_stk1[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
          (FullMem c sio ⋆ R) mio)
        (fun (io, ()) _ => 2 * cv0 - io.toNat)
        (fun Jo hJo => by
          c0_hsteps!; exact hJo (0#64, ()) m_s
            ⟨s_s, Nat.zero_le _, hd_s, rfl, rfl, (fun _ h => absurd h (Nat.not_lt_zero _)), hm_s'⟩)
        (fun Jo (io, ()) mio ⟨sio, hio_le, hdio, hcor_io, hscr_io, hhead_io, hmio⟩ iho => ?_)
      c0_hsplit
      · have hio_lt : io.toNat < 2 * cv0 := by
          have := hc; dsimp only [cv0] at hcv_le ⊢
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
        have hio1_n : (io + 1#64).toNat = io.toNat + 1 := by bv_omega
        have hio_w1 : io.toNat < sio.scratch.work_stk1.length := by
          have := hdio.1.scratch_ok.work_stk1_len; omega
        have hio_w2 : io.toNat < sio.scratch.work_stk2.length := by
          have := hdio.1.scratch_ok.work_stk2_len; omega
        clear hc; c0_hsteps!
        let sio' : FullState :=
          { sio with scratch :=
            { sio.scratch with
              work_stk1 := sio.scratch.work_stk1.set io.toNat 0xFFFFFFFF#32
              work_stk2 := sio.scratch.work_stk2.set io.toNat 0#32 } }
        have hhead' : ∀ l < (io + 1#64).toNat,
            sio'.scratch.work_stk1[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
          rw [hio1_n]; intro l hl; dsimp only [sio']
          by_cases hli : l = io.toNat
          · subst hli; rw [List.getElem?_set_self hio_w1, Option.getD_some]
          · rw [List.getElem?_set_ne (Ne.symm hli)]; exact hhead_io l (by omega)
        exact iho (io + 1#64, ()) _ (by dsimp only; omega)
          ⟨sio', by omega, fid_denseInvW_with_ws12 hdio
            (by simp [hdio.1.scratch_ok.work_stk1_len]) (by simp [hdio.1.scratch_ok.work_stk2_len]),
           hcor_io, hscr_io, hhead', hm⟩
      · have hio_eq : io.toNat = 2 * cv0 := by
          have := hc; dsimp only [cv0] at hcv_le ⊢
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
        clear hc Jo hio_le iho
        have hocc_init : FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) (2 * ncand.toNat)
            sio.scratch.work_stk1 sio.scratch.scratch_buf :=
          fidFsOccOk_init (by rw [hdio.1.scratch_ok.scratch_buf_len]; omega) (hio_eq ▸ hhead_io)
        have hnc2_init : (ncand <<< (1 : Nat)).toNat = 2 * ncand.toNat := by bv_omega
        have hocc_init' : FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat)
            (ncand <<< (1 : Nat)).toNat sio.scratch.work_stk1 sio.scratch.scratch_buf := by
          rw [hnc2_init]; exact hocc_init
        c0_hsteps_nogrp
        exact fidFs_pass2_wp Γ hAddUnit hFind
          (h := c.hdr) (tl := tl) (pRepr := c.pRepr) (pArena := c.pArena) (pVals := c.pVals)
          (pLitMark := c.pLitMark) (pTmp := c.pTmp) (pScr := c.pScratchBuf)
          (pW1 := c.pWorkStk1) (pW2 := c.pWorkStk2) (ncand := ncand) (ticksInit := ticks)
          (occInit := ncand <<< (1 : Nat))
          rfl rfl rfl rfl rfl rfl rfl rfl rfl hnc2_init
          hnc_gt1 hnc_le htk_le_e htl_le hdio (hcor_io.symm ▸ hcve) (hcor_io.symm ▸ hale)
          (hcor_io.symm ▸ hfle)
          (by change fullArenaClauseRefsCore sio.core = refs0; rw [hcor_io]; exact hrefse)
          (hcor_io.symm ▸ hrepre) (hscr_io.symm ▸ hpairs_s) hocc_init' hmio
          (fun r s' m' hd hcv hfl hrep hr huns hm =>
            hQ r s' m' hd hcv hfl (hcv ▸ hrep) hr huns hm)
    · intro Jexit1 hJexit1
      have hpass1_exit : Jexit1 () mp := hJexit1 () mp
        ⟨sp, hnc_le, htk_le, hdp, hcvp, halp, hflp, hrefsp, hreprp, hpairs, hmp⟩
      c0_hsplit; rotate_left 1; · clear hc; c0_hsteps!; exact hpass1_exit
      have har_le_p := hdp.1.core_ok.arena_len_le; have har_arr_p := hdp.1.core_ok.arena_len_arr
      have hp_lt : p.toNat < alen0 := by omega
      clear hc; c0_hsplit; rotate_left 1; · clear hc; c0_hsteps!; exact hpass1_exit
      have htk_lt : ticks.toNat < tl.toNat := hc
      have htk1_n : (ticks + 1#64).toNat = ticks.toNat + 1 := by bv_omega
      clear hc; c0_hsplit; rotate_left 1; · clear hc; c0_hsteps!; exact hpass1_exit
      have hinc0 : sp.core.inconsistent = 0#64 := hc
      have hp_ref0 : p.toNat ∈ refs0 := hp_mem.resolve_left (by omega)
      have hp_ref : p.toNat ∈ fullArenaClauseRefs sp := hrefsp.symm ▸ hp_ref0
      have hp_wf := hdp.2.1.arena.refs_wf p.toNat hp_ref
      have hp_arr0 : p.toNat < sp.core.arena.length := by omega
      have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
      have hp_arr2 : (p + 2#64).toNat < sp.core.arena.length := by rw [hp2_n]; omega
      have hp_32n : (p.setWidth 32).toNat = p.toNat := by bv_omega
      clear hc Jexit1 hJexit1 hpass1_exit; c0_hsteps!; c0_hcall hNext
      refine ⟨c, sp, R, rfl, hdp.1, hmp, ?_⟩
      let np_nat := fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat
      have hnp_bds := fullArenaNextOff_bounds (ar := sp.core.arena) (alen := sp.core.arena_len)
        (cref := p.toNat) hp_wf.1
      let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena
        sp.core.arena_len (p.setWidth 32).toNat)).setWidth 64
      have hnp_n : np.toNat = np_nat := by
        dsimp only [np, np_nat]; rw [hp_32n, bv_zext32_toNat, bv32_ofNat_toNat_lt (by omega)]
      have hnp_mem : np_nat = alen0 ∨ np_nat ∈ refs0 := by
        have h := fullArenaClauseRefs_next_or_end hdp.2.1 hp_ref
        exact h.elim (fun h1 => Or.inl (h1.trans halp)) fun h2 => Or.inr (hrefsp ▸ h2)
      have hsz_eq : fullArenaClauseSizeCore sp.core p.toNat =
          (sp.core.arena[(p + 2#64).toNat]'hp_arr2).toNat := by
        unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact congrArg BitVec.toNat (list_getElem_congr hp2_n.symm _ _)
      c0_hsplit
      · clear hc
        c0_hsteps!; exact ihp (ncand, np, ticks + 1#64, ()) mp (by dsimp only; rw [hnp_n]; omega)
          ⟨sp, hnc_le, by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem, by omega,
           hdp, hcvp, halp, hflp, hrefsp, hreprp, hpairs, hmp⟩
      have hgarb0 : ((sp.core.arena[p.toNat]'hp_arr0) &&& 0x00080000#32) = 0#32 := hc
      clear hc; c0_hsplit
      · clear hc
        c0_hsteps!; exact ihp (ncand, np, ticks + 1#64, ()) mp (by dsimp only; rw [hnp_n]; omega)
          ⟨sp, hnc_le, by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem, by omega,
           hdp, hcvp, halp, hflp, hrefsp, hreprp, hpairs, hmp⟩
      let hdr := sp.core.arena[p.toNat]'hp_arr0; let sz := sp.core.arena[(p + 2#64).toNat]'hp_arr2
      have hsz3 : 3 ≤ sz.toNat := by
        have hp2_hc : (p.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = (p + 2#64).toNat := by
          bv_omega
        have hhc := hc
        rw [list_getElem_congr hp2_hc (hp2_hc ▸ hp_arr2) hp_arr2] at hhc
        simpa only [sz, show BitVec.toNat (3 : BitVec 32) = 3 from rfl, Nat.not_lt] using hhc
      have hng_p : fullArenaClauseGarb sp p.toNat = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
        rw [List.getElem?_eq_getElem hp_arr0, Option.getD_some]; exact fid_garb_false_of_and hgarb0
      have hsz_cv : sz.toNat ≤ cv0 := by
        rw [← hcvp, ← hsz_eq]
        exact fullArenaClauseSize_le_cur_vars hdp.1 hdp.2.1 hdp.2.2.2.1 hp_ref hng_p
      have hp_bd : p.toNat + 3 + sz.toNat ≤ alen0 := by
        dsimp only [sz]; have h1 := hp_wf.2.2.1; have h2 := hp_wf.2.2.2.1
        rw [hsz_eq] at h1; rw [← halp]; omega
      obtain ⟨hb_p, hlm_p⟩ := FidFsBaseOk.of_dense hdp hcvp halp hflp hrefsp hreprp
      clear hc; c0_hsteps_nogrp
      refine wp_join_group (ts := [.bool, .bool, .bool, .bool, i32, i32])
        (fun (sat, taut, _c_mch, ovf, msz, _k, ()) mk => ∃ sk : FullState,
          FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk ∧ sk.core.arena = sp.core.arena ∧
          sk.core.vals = sp.core.vals ∧ sk.core.min_clr = sp.core.min_clr ∧
          sk.core.inconsistent = 0#64 ∧ sk.scratch = sp.scratch ∧ msz.toNat ≤ cv0 ∧
          (∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
          (∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
            (∃ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
          (sat = false → taut = false → ovf = false →
            ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → ∀ j < sz.toNat,
              evalLitVal α (sk.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat = true →
              ∃ q < msz.toNat, evalLitVal α (sk.core.tmp[q]?.getD 0#32).toNat = true) ∧
          (FullMem c sk ⋆ R) mk)
        ?_
        (fun Jk1_ex hJk1_ex => fidFs_pass1_k_wp Γ hFind rfl rfl rfl rfl rfl rfl rfl hb_p hinc0
          hlm_p hp_ref0 hng_p hsz_eq hp_bd hmp fun sat taut c_mch ovf msz k_r mk h =>
            hJk1_ex (sat, taut, c_mch, ovf, msz, k_r, ()) mk h)
      rintro _ ⟨sat, taut, c_mch, ovf, msz, _k, ⟨⟩⟩ mk
        ⟨sk, hbk, hark, hvlk, hmck, hinck, hscrk, hmsz_cv, htmp_lt, hlm_ok, hsem_ok, hmk⟩
      refine fidFs_clearLm_wp Γ rfl rfl hmk hbk hark rfl hscrk hmsz_cv htmp_lt
        (fidFs_lm_clear_from_zero hlm_ok)
        fun sc mc _ harc htmpc hscrc hdc hcvc halc hflc hrefsc hreprc hmc => ?_
      have hp_ref_c : p.toNat ∈ fullArenaClauseRefs sc := hrefsc.symm ▸ hp_ref0
      have harc_p : p.toNat < sc.core.arena.length := by rw [harc]; exact hp_arr0
      have hhdr_c : sc.core.arena[p.toNat]'harc_p = hdr := list_eq_getElem_congr harc _ _
      have hpairs_c : CongPairsOk (fun _ cr =>
        cr.toNat ∈ refs0) sc.scratch.scratch_buf ncand.toNat :=
        hscrc.symm ▸ hpairs
      have har_sc_sk : sc.core.arena = sk.core.arena := harc.trans hark.symm
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun () mm => mm = mc ∧ (sat = true ∨ taut = true))
        (fun _ ⟨⟩ mm ⟨hmm, _⟩ => by
          have hmm' : (FullMem c sc ⋆ R) mm := hmm ▸ hmc; c0_hsteps!
          obtain ⟨hd_mg, hmg_refs⟩ := fid_fs_markGarb_dense' hdc hp_ref_c harc_p
            (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
          rw [hhdr_c] at hd_mg hmg_refs
          exact ihp (ncand, np, ticks + 1#64, ()) _ (by dsimp only; rw [hnp_n]; omega)
            ⟨_, hnc_le, by rw [hnp_n, ← halp]; exact hnp_bds.2, by rw [hnp_n]; exact hnp_mem,
             by omega, hd_mg, hcvc, halc, hflc, hmg_refs.trans hrefsc, hreprc, hpairs_c, hm⟩)
        ?_
      intro Jst hJst; c0_hsplit
      · c0_hsteps!; exact hJst () mc ⟨rfl, Or.inl hc⟩
      have hsat_f : sat = false := hc; clear hc; c0_hsplit
      · c0_hsteps!; exact hJst () mc ⟨rfl, Or.inr hc⟩
      have htaut_f : taut = false := hc; clear hc Jst hJst; c0_hsplit
      · c0_hsteps!; exact ihp (ncand, np, ticks + 1#64, ()) mc (by dsimp only; rw [hnp_n]; omega)
          ⟨sc, hnc_le, by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem, by omega,
           hdc, hcvc, halc, hflc, hrefsc, hreprc, hpairs_c, hmc⟩
      have hovf_f : ovf = false := hc; clear hc; c0_hsplit
      · have hmsz0 : msz.toNat = 0 := by have := hc; bv_omega
        have hng_c : fullArenaClauseGarb sc p.toNat = false := by
          unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
          rw [List.getElem?_eq_getElem harc_p, Option.getD_some, hhdr_c]
          exact fid_garb_false_of_and hgarb0
        have hsz_c : fullArenaClauseSizeCore sc.core p.toNat = sz.toNat := by
          unfold fullArenaClauseSizeCore; rw [harc, ← hsz_eq]; rfl
        have hu_cur : (cnfOfClauses F_cur).Unsat :=
          fidFs_msz0_unsat hdc.1 hdc.2.1 hp_ref_c hng_c hsz_c fun α hα j hj hl => by
            obtain ⟨q, hq, _⟩ := hsem_ok hsat_f htaut_f hovf_f α hα j hj (har_sc_sk ▸ hl); omega
        clear hc; c0_hsteps!
        exact hQ 20#64 _ _ (fid_denseInvW_with_inc hdc hu_cur 1#64) hcvc hflc
          (hcvc ▸ hreprc) (Or.inr rfl) (fun _ => hdc.2.1.ext_sound.2 hu_cur) hm
      have hmsz_ne0 : msz.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
      clear hc; c0_hsplit
      · have hmsz1 : msz.toNat = 1 := by have := hc; bv_omega
        have h0_tmp : 0 < sc.core.tmp.length := by have := hdc.1.core_ok.tmp_len_arr; omega
        have hu0_lt : (sc.core.tmp[0]'h0_tmp).toNat < 2 * cv0 := by
          have h := htmp_lt 0 (by omega)
          rwa [← htmpc, List.getElem?_eq_getElem h0_tmp, Option.getD_some] at h
        have hng_c : fullArenaClauseGarb sc p.toNat = false := by
          unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
          rw [List.getElem?_eq_getElem harc_p, Option.getD_some, hhdr_c]
          exact fid_garb_false_of_and hgarb0
        have hsz_c : fullArenaClauseSizeCore sc.core p.toNat = sz.toNat := by
          unfold fullArenaClauseSizeCore; rw [harc, ← hsz_eq]; rfl
        have hent_u : (cnfOfClauses F_cur).EntailsClause
          (cnfClause [(sc.core.tmp[0]'h0_tmp).toNat]) :=
          fidFs_msz1_entails hdc.1 hdc.2.1 hp_ref_c hng_c hsz_c fun α hα j hj hl => by
            obtain ⟨q, hq, hqt⟩ := hsem_ok hsat_f htaut_f hovf_f α hα j hj (har_sc_sk ▸ hl)
            obtain rfl : q = 0 := by omega
            rwa [← htmpc, List.getElem?_eq_getElem h0_tmp, Option.getD_some] at hqt
        have h0_bv_tmp : (BitVec.ofNat 64 0).toNat < sc.core.tmp.length := by simpa using h0_tmp
        clear hc; c0_hsteps!
        obtain ⟨hd_mg, hmg_refs⟩ := fid_fs_markGarb_dense' hdc hp_ref_c harc_p
          (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
        rw [hhdr_c] at hd_mg hmg_refs; c0_hcall hAddUnit
        refine ⟨c, F0, F_cur, _, R, rfl, hd_mg.1, hd_mg.2.1, fun _ => by
            rw [list_getElem_congr (by decide : (BitVec.ofNat 64 0).toNat = 0) h0_bv_tmp h0_tmp]
            exact hent_u,
          hm, fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
            phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mu hlu hwu hclu _ h_f hmu => ?_⟩
        have hdu := fid_addUnit_denseInvW hd_mg hlu hwu hclu rfl rfl rfl rfl rfl rfl rfl
        c0_hsplit
        · c0_hsteps!; exact ihp (ncand, np, ticks + 1#64, ()) mu (by dsimp only; rw [hnp_n]; omega)
            ⟨_, hnc_le, by rw [hnp_n, ← halp]; exact hnp_bds.2, by rw [hnp_n]; exact hnp_mem,
             by omega, hdu, hcvc, halc, hflc, hmg_refs.trans hrefsc, hreprc, hpairs_c, hmu⟩
        · have hu_f := h_f hc
          have hlt_su :
            (sc.core.tmp[(BitVec.ofNat 64 0).toNat]'h0_bv_tmp).toNat < 2 * sc.core.cur_vars := by
            rw [list_getElem_congr (by decide) h0_bv_tmp h0_tmp, hcvc]; exact hu0_lt
          have hu := (hu_f.resolve_left (Nat.not_le_of_lt hlt_su)).1
          c0_hsteps!
          exact hQ 20#64 _ mu hdu hcvc hflc (hcvc ▸ hreprc) (Or.inr rfl) (fun _ => hu) hmu
      clear hc; c0_hsplit; rotate_left 1
      · c0_hsteps!; exact ihp (ncand, np, ticks + 1#64, ()) mc (by dsimp only; rw [hnp_n]; omega)
          ⟨sc, hnc_le, by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem, by omega,
           hdc, hcvc, halc, hflc, hrefsc, hreprc, hpairs_c, hmc⟩
      clear hc; c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun (nc', ()) mnc => ∃ snc : FullState, nc'.toNat ≤ c.scratch_cap / 4 ∧
          FullDenseInvW c F0 F_cur snc ∧ snc.core.cur_vars = cv0 ∧ snc.core.arena_len = alen0 ∧
          snc.core.fuel = fuel0 ∧ fullArenaClauseRefs snc = refs0 ∧
          FullCongReprInv F_cur (2 * cv0) snc.core.repr ∧
          CongPairsOk (fun _ cr => cr.toNat ∈ refs0) snc.scratch.scratch_buf nc'.toNat ∧
          (FullMem c snc ⋆ R) mnc)
        (fun _ ⟨nc', ⟨⟩⟩ mnc ⟨snc, hnc', hdnc, hcvnc, halnc, hflnc, hrefsnc, hreprnc, hpnc,
          hmnc⟩ => by
          c0_hsteps!; exact ihp (nc', np, ticks + 1#64, ()) mnc (by dsimp only; rw [hnp_n]; omega)
            ⟨snc, hnc', by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem, by omega,
             hdnc, hcvnc, halnc, hflnc, hrefsnc, hreprnc, hpnc, hmnc⟩)
        ?_
      intro Jnc hJnc; c0_hsplit; rotate_left 1
      · c0_hsteps!
        exact hJnc (ncand, ()) mc ⟨sc, hnc_le, hdc, hcvc, halc, hflc, hrefsc, hreprc, hpairs_c, hmc⟩
      have hnc_lt : ncand.toNat < c.scratch_cap / 4 := by
        have h : ncand.toNat < (BitVec.ofNat 64 c.scratch_cap >>> (2 : Nat)).toNat := hc
        bv_omega
      have hnc1_n : (ncand + 1#64).toNat = ncand.toNat + 1 := by bv_omega
      have hnc2_n : (ncand <<< BitVec.signExtend 64 1#32).toNat = 2 * ncand.toNat :=
        bv64_shl_s1 ncand (by omega)
      have hnc21_n :
        ((ncand <<< BitVec.signExtend 64 1#32) + 1#64).toNat = 2 * ncand.toNat + 1 := by
        rw [BitVec.toNat_add, hnc2_n, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hsc_len : sc.scratch.scratch_buf.length = c.scratch_cap :=
        hdc.1.scratch_ok.scratch_buf_len
      have hnc2_arr :
        (ncand <<< BitVec.signExtend 64 1#32).toNat < sc.scratch.scratch_buf.length := by
        rw [hnc2_n]; omega
      have hnc21_arr : ((ncand <<< BitVec.signExtend 64 1#32) + 1#64).toNat <
          sc.scratch.scratch_buf.length := by rw [hnc21_n]; omega
      clear hc; c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun (_bit, ()) mb => mb = mc)
        (fun _ ⟨bit, ⟨⟩⟩ mb hmb => by
          subst mb; c0_hsteps!
          let scr_n := (sc.scratch.scratch_buf.set (2 * ncand.toNat) ((msz <<< 1#32) ||| bit)).set
            (2 * ncand.toNat + 1) (p.setWidth 32)
          let snc : FullState := { sc with scratch := { sc.scratch with scratch_buf := scr_n } }
          have hpairs' := congPairsOk_push hpairs_c (key := (msz <<< 1#32) ||| bit)
            (cr := p.setWidth 32) (by omega) (by rw [hp_32n]; exact hp_ref0)
          have hnc2_n' : (ncand <<< (1 : Nat)).toNat = 2 * ncand.toNat := by bv_omega
          have hnc21_n' : ((ncand <<< (1 : Nat)) + 1).toNat = 2 * ncand.toNat + 1 := by bv_omega
          rw [hnc2_n', hnc21_n'] at hm
          exact hJnc (ncand + 1#64, ()) _
            ⟨snc, by omega, fullDenseInvW_with_scr hdc (by simp [scr_n, hsc_len]),
             hcvc, halc, hflc, hrefsc, hreprc, by rw [hnc1_n]; exact hpairs', hm⟩)
        (fun Jbit hJbit => by
          c0_hsplit
          · c0_hsteps!; exact hJbit (1#32, ()) mc rfl
          · c0_hsteps!; exact hJbit (0#32, ()) mc rfl)

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
