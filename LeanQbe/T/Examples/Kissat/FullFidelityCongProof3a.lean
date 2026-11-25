/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof3a0
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1

/-!
# Kissat 4.0.4 Congruence Parity Proofs — Part 3a (`FullFidelityCongProof3a`)

Proves `full_cong_fwd_subsume_wp` (`m6CongFwdSubsumeSpec`, `BUG-CONG-00` fix) over
`FullFidelityCongProof3a0` (`full_cong_sift_pairs_fid_wp`, `full_cong_sort_pairs_fid_wp`,
and shared forward-subsumption invariants).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullCongTactics M6bHeadTactics

section FwdSubsumeProof

private theorem fidFs_clearLm_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {s2 sk st0 : FullState} {msz : Val i32} {m_in : Mem 64}
    {kExit : Tup Val [i32] → Expr Val Cont [i64]}
    (hm_in : (FullMem c st0 ⋆ R) m_in)
    (hb0 : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 st0)
    (har0 : st0.core.arena = s2.core.arena) (htmp0 : st0.core.tmp = sk.core.tmp)
    (hscr0 : st0.scratch = s2.scratch) (hmsz_cv : msz.toNat ≤ cv0)
    (htmp_lt : ∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0)
    (hlm0 : ∀ l < 2 * c.max_vars, st0.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
      (∃ j, 0 ≤ j ∧ j < msz.toNat ∧
        (st0.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0))
    (hk : ∀ (kc : Val i32) (sc : FullState) (mc : Mem 64),
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sc →
      sc.core.arena = s2.core.arena → sc.core.tmp = sk.core.tmp →
      sc.scratch = s2.scratch → FullDenseInvW c F0 F_cur sc →
      sc.core.cur_vars = cv0 → sc.core.arena_len = alen0 → sc.core.fuel = fuel0 →
      fullArenaClauseRefs sc = refs0 → FullCongReprInv F_cur (2 * cv0) sc.core.repr →
      (FullMem c sc ⋆ R) mc → wp Γ Q X (kExit (kc, ())) mc) :
    wp Γ Q X (.group (sig := [[i32]]) (fun Js => .cons (fun p =>
      .let_ ⟨.cmp .ult i32, (.var p.1, (.var msz, ()))⟩ fun p_cmp =>
      .jnz (.var p_cmp.1)
        (.let_ ⟨.zext 32 64, (.var p.1, ())⟩ fun p1 =>
         .let_ ⟨.mul i64, (.var p1.1, (.imm 4, ()))⟩ fun p2 =>
         .let_ ⟨.add i64, (.var c.pTmp, (.var p2.1, ()))⟩ fun p3 =>
         .load i32 (.var p3.1) fun ld =>
         .let_ ⟨.zext 32 64, (.var ld, ())⟩ fun p4 =>
         .let_ ⟨.add i64, (.var c.pLitMark, (.var p4.1, ()))⟩ fun p5 =>
         .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p6 =>
         .store (t := i8) (.var p6.1) (.var p5.1)
           (.let_ ⟨.add i32, (.var p.1, (.imm 1, ()))⟩ fun p7 =>
            .jump Js.1 (.var p7.1, ())))
        (kExit p)) .nil) (fun Js => .jump Js.1 (.imm 0, ()))) m_in := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hb0.1.core_ok.cur_vars_le
  refine wp_loop_inv (ts := [i32])
    (fun (kc, ()) mc => ∃ sc : FullState,
      kc.toNat ≤ msz.toNat ∧
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sc ∧
      sc.core.arena = s2.core.arena ∧ sc.core.tmp = sk.core.tmp ∧ sc.scratch = s2.scratch ∧
      (∀ l < 2 * c.max_vars, sc.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j, kc.toNat ≤ j ∧ j < msz.toNat ∧
          (sc.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (FullMem c sc ⋆ R) mc)
    (fun (kc, ()) _ => msz.toNat - kc.toNat)
    (fun Jc hJc => by
      m6b_steps
      exact hJc (0#32, ()) m_in ⟨st0, Nat.zero_le _, hb0, har0, htmp0, hscr0, hlm0, hm_in⟩)
    (fun Jc (kc, ()) mc ⟨sc, hkc_le, hbc, harc, htmpc, hscrc, hlmc, hmc⟩ ihc => ?_)
  m6b_split
  · have hkc_lt : kc.toNat < msz.toNat := bv32_ult_lt hc
    have hcvc := hbc.2.2.2.2.2.2.2.1
    have hkc1 : (kc + 1#32).toNat = kc.toNat + 1 := bv32_add1_lt_of (by omega)
    have hkc_arr : kc.toNat < sc.core.tmp.length := by
      have := hbc.1.core_ok.tmp_len_arr; omega
    let rk := sc.core.tmp[kc.toNat]'hkc_arr
    have hrk_lt : rk.toNat < 2 * cv0 := by
      have h := htmp_lt kc.toNat hkc_lt
      rwa [← htmpc, List.getElem?_eq_getElem hkc_arr, Option.getD_some] at h
    have hrk_arr : rk.toNat < sc.core.lit_mark.length := fidFs_base_lm_lt hbc hrk_lt
    have hkc_z : (kc.setWidth 64).toNat = kc.toNat := bv_zext32_toNat kc
    have hkc_z_arr : (kc.setWidth 64).toNat < sc.core.tmp.length := by rw [hkc_z]; exact hkc_arr
    have hlmc' : ∀ l < 2 * c.max_vars,
        (sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0))[l]?.getD 0#8 = 0#8 ∨
          (∃ j, (kc + 1#32).toNat ≤ j ∧ j < msz.toNat ∧
            (sc.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0) := by
      rw [hkc1]; exact fidFs_lm_clear_step hkc_lt hkc_arr hrk_arr hlmc
    have hrk_eq_z : sc.core.tmp[(kc.setWidth 64).toNat]'hkc_z_arr = rk :=
      list_getElem_congr hkc_z hkc_z_arr hkc_arr
    have hrk_z_lm : ((sc.core.tmp[(kc.setWidth 64).toNat]'hkc_z_arr).setWidth 64).toNat <
        sc.core.lit_mark.length := by
      rw [hrk_eq_z, bv_zext32_toNat]; exact hrk_arr
    have hlm_set_eq : sc.core.lit_mark.set
        ((sc.core.tmp[(kc.setWidth 64).toNat]'hkc_z_arr).setWidth 64).toNat
        (BitVec.ofNat 8 0) = sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0) :=
      congrArg (sc.core.lit_mark.set · _) (by rw [hrk_eq_z, bv_zext32_toNat])
    clear hc; m6b_steps
    let P_lm (lm : List (BitVec 8)) :=
      (FullMem c { sc with core := { sc.core with lit_mark := lm } } ⋆ R) m
    have hm_rk : P_lm (sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0)) :=
      (congrArg P_lm hlm_set_eq).mp hm
    exact ihc (kc + 1#32, ()) m (by dsimp only; omega)
      ⟨_, by rw [hkc1]; omega,
       fidFsBaseOk_with_lm hbc (lm' := sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0))
        (by simp [hbc.1.core_ok.lit_mark_len]),
       harc, htmpc, hscrc, hlmc', hm_rk⟩
  have hkc_eq : kc.toNat = msz.toNat := by have := bv32_ult_not_lt hc; omega
  clear hc
  obtain ⟨hdc, hcvc, halc, hflc, hrefsc, hreprc⟩ :=
    fidFsBaseOk_to_dense hbc (fidFs_lm_clear_done (hkc_eq ▸ hlmc))
  exact hk kc sc mc hbc harc htmpc hscrc hdc hcvc halc hflc hrefsc hreprc hmc

private def fidFs_reduce_k_expr {V : Ty → Type} {L : List Ty → Type}
    (pRepr pArena pVals pLitMark pTmp cv64 : V i64) (cref csz : V i32)
    (Jk2_ex : L [.bool, .bool, .bool, i32, i32]) : Expr V L [i64] :=
  .group (sig := [[i32, i32]]) (fun Jk => .cons (fun p =>
    .let_ ⟨.cmp .ult i32, (.var p.2.1, (.var csz, ()))⟩ fun p_lt =>
    .jnz (.var p_lt.1)
      (.let_ ⟨.zext 32 64, (.var cref, ())⟩ fun p2 =>
       .let_ ⟨.add i64, (.var p2.1, (.imm 3, ()))⟩ fun p3 =>
       .let_ ⟨.zext 32 64, (.var p.2.1, ())⟩ fun p4 =>
       .let_ ⟨.add i64, (.var p3.1, (.var p4.1, ()))⟩ fun p5 =>
       .let_ ⟨.mul i64, (.var p5.1, (.imm 4, ()))⟩ fun p6 =>
       .let_ ⟨.add i64, (.var pArena, (.var p6.1, ()))⟩ fun p7 =>
       .load i32 (.var p7.1) fun l =>
       .let_ ⟨.zext 32 64, (.var l, ())⟩ fun p8 =>
       .let_ ⟨.add i64, (.var pVals, (.var p8.1, ()))⟩ fun p9 =>
       .load i8 (.var p9.1) fun lv =>
       .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p10 =>
       .let_ ⟨.sext 8 32, (.var lv, ())⟩ fun p11 =>
       .let_ ⟨.sext 8 32, (.var p10.1, ())⟩ fun p12 =>
       .let_ ⟨.cmp .sgt i32, (.var p11.1, (.var p12.1, ()))⟩ fun p13 =>
       .jnz (.var p13.1)
         (.jump Jk2_ex (.imm true, (.imm false, (.imm false, (.var p.1, (.var p.2.1, ()))))))
         (.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p14 =>
          .let_ ⟨.sext 8 32, (.var lv, ())⟩ fun p15 =>
          .let_ ⟨.sext 8 32, (.var p14.1, ())⟩ fun p16 =>
          .let_ ⟨.cmp .slt i32, (.var p15.1, (.var p16.1, ()))⟩ fun p17 =>
          .jnz (.var p17.1)
            (.let_ ⟨.add i32, (.var p.2.1, (.imm 1, ()))⟩ fun p18 =>
             .jump Jk.1 (.var p.1, (.var p18.1, ())))
            (.call "full_cong_find" (as := [i64, i32]) (bs := [i32])
               (Arg.var pRepr, (Arg.var l, ())) fun rr =>
             .let_ ⟨.zext 32 64, (.var rr.1, ())⟩ fun p19 =>
             .let_ ⟨.add i64, (.var pVals, (.var p19.1, ()))⟩ fun p20 =>
             .load i8 (.var p20.1) fun rv =>
             .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p21 =>
             .let_ ⟨.sext 8 32, (.var rv, ())⟩ fun p22 =>
             .let_ ⟨.sext 8 32, (.var p21.1, ())⟩ fun p23 =>
             .let_ ⟨.cmp .sgt i32, (.var p22.1, (.var p23.1, ()))⟩ fun p24 =>
             .jnz (.var p24.1)
               (.jump Jk2_ex (.imm true, (.imm false, (.imm false, (.var p.1, (.var p.2.1, ()))))))
               (.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p25 =>
                .let_ ⟨.sext 8 32, (.var rv, ())⟩ fun p26 =>
                .let_ ⟨.sext 8 32, (.var p25.1, ())⟩ fun p27 =>
                .let_ ⟨.cmp .slt i32, (.var p26.1, (.var p27.1, ()))⟩ fun p28 =>
                .jnz (.var p28.1)
                  (.let_ ⟨.add i32, (.var p.2.1, (.imm 1, ()))⟩ fun p29 =>
                   .jump Jk.1 (.var p.1, (.var p29.1, ())))
                  (.let_ ⟨.xor i32, (.var rr.1, (.imm 1, ()))⟩ fun p29 =>
                   .let_ ⟨.zext 32 64, (.var p29.1, ())⟩ fun p30 =>
                   .let_ ⟨.add i64, (.var pLitMark, (.var p30.1, ()))⟩ fun p31 =>
                   .load i8 (.var p31.1) fun lm1 =>
                   .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p32 =>
                   .let_ ⟨.zext 8 32, (.var lm1, ())⟩ fun p33 =>
                   .let_ ⟨.zext 8 32, (.var p32.1, ())⟩ fun p34 =>
                   .let_ ⟨.cmp .ne i32, (.var p33.1, (.var p34.1, ()))⟩ fun p35 =>
                   .jnz (.var p35.1)
                     (.jump Jk2_ex
                       (.imm false, (.imm true, (.imm false, (.var p.1, (.var p.2.1, ()))))))
                     (.group (sig := [[.bool, i32]]) (fun Jov => .cons (fun p36 =>
                        .let_ ⟨.add i32, (.var p.2.1, (.imm 1, ()))⟩ fun pk1 =>
                        .jump Jk.1 (.var p36.2.1, (.var pk1.1, ()))) .nil)
                      fun Jov =>
                      .let_ ⟨.zext 32 64, (.var rr.1, ())⟩ fun p36 =>
                      .let_ ⟨.add i64, (.var pLitMark, (.var p36.1, ()))⟩ fun p37 =>
                      .load i8 (.var p37.1) fun lm0 =>
                      .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p38 =>
                      .let_ ⟨.zext 8 32, (.var lm0, ())⟩ fun p39 =>
                      .let_ ⟨.zext 8 32, (.var p38.1, ())⟩ fun p40 =>
                      .let_ ⟨.cmp .eq i32, (.var p39.1, (.var p40.1, ()))⟩ fun p41 =>
                      .jnz (.var p41.1)
                        (.let_ ⟨.zext 32 64, (.var p.1, ())⟩ fun p42 =>
                         .let_ ⟨.cmp .ult i64, (.var p42.1, (.var cv64, ()))⟩ fun p43 =>
                         .jnz (.var p43.1)
                           (.let_ ⟨.zext 32 64, (.var rr.1, ())⟩ fun p44 =>
                            .let_ ⟨.add i64, (.var pLitMark, (.var p44.1, ()))⟩ fun p45 =>
                            .let_ ⟨.trunc 32 8, (.imm 1, ())⟩ fun p46 =>
                            .store (t := i8) (.var p46.1) (.var p45.1)
                              (.let_ ⟨.zext 32 64, (.var p.1, ())⟩ fun p47 =>
                               .let_ ⟨.mul i64, (.var p47.1, (.imm 4, ()))⟩ fun p48 =>
                               .let_ ⟨.add i64, (.var pTmp, (.var p48.1, ()))⟩ fun p49 =>
                               .store (t := i32) (.var rr.1) (.var p49.1)
                                 (.let_ ⟨.add i32, (.var p.1, (.imm 1, ()))⟩ fun pm1 =>
                                  .jump Jov.1 (.imm false, (.var pm1.1, ())))))
                           (.jump Jk2_ex
                             (.imm false, (.imm false, (.imm true, (.var p.1, (.var p.2.1, ())))))))
                        (.jump Jov.1 (.imm false, (.var p.1, ())))))))))
      (.jump Jk2_ex (.imm false, (.imm false, (.imm false, (.var p.1, (.var p.2.1, ()))))))
  ) .nil) (fun Jk => .jump Jk.1 (.imm 0, (.imm 0, ())))

private theorem fidFs_reduce_k_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {s2 : FullState} {m2 : Mem 64} {pRepr pArena pVals pLitMark pTmp cv64 : Val i64}
    {cref csz : Val i32} {Jk2_ex : Cont [.bool, .bool, .bool, i32, i32]}
    (hRepr : pRepr = c.pRepr) (hAr : pArena = c.pArena) (hVals : pVals = c.pVals)
    (hLm : pLitMark = c.pLitMark) (hTmp : pTmp = c.pTmp)
    (hcv64 : cv64 = BitVec.ofNat 64 cv0)
    (hb_2 : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s2)
    (hinc2 : s2.core.inconsistent = 0#64)
    (hlm_2 : ∀ l < 2 * c.max_vars, s2.core.lit_mark[l]?.getD 0#8 = 0#8)
    (hcref_ref0 : cref.toNat ∈ refs0) (hng_c2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hcsz_eq : fullArenaClauseSizeCore s2.core cref.toNat = csz.toNat)
    (hcr_bd : cref.toNat + 3 + csz.toNat ≤ alen0)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hJk2_ex : ∀ (sat taut ovf : Bool) (msz k_r : Val i32) (mk : Mem 64),
      (∃ sk : FullState,
        FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk ∧
        sk.core.arena = s2.core.arena ∧ sk.core.vals = s2.core.vals ∧
        sk.core.inconsistent = 0#64 ∧ sk.scratch = s2.scratch ∧ msz.toNat ≤ cv0 ∧
        (∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
        (∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
          (∃ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
        (sat = false → taut = false → ovf = false →
          ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
            ∀ j < csz.toNat,
              evalLitVal α (sk.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat = true →
              ∃ q < msz.toNat, evalLitVal α (sk.core.tmp[q]?.getD 0#32).toNat = true) ∧
        (FullMem c sk ⋆ R) mk) →
      Jk2_ex (sat, taut, ovf, msz, k_r, ()) mk) :
    wp Γ Q X (fidFs_reduce_k_expr pRepr pArena pVals pLitMark pTmp cv64 cref csz Jk2_ex)
      m2 := by
  subst hRepr hAr hVals hLm hTmp hcv64
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le : cv0 ≤ c.max_vars := by
    rw [← hb_2.2.2.2.2.2.2.2.1]; exact hb_2.1.core_ok.cur_vars_le
  have hcr_z : (cref.setWidth 64).toNat = cref.toNat := bv_zext32_toNat cref
  unfold fidFs_reduce_k_expr
  m6b_steps
  refine wp_loop_inv (ts := [i32, i32])
    (fun (msz, k, ()) mk_in => ∃ sk_in : FullState,
      k.toNat ≤ csz.toNat ∧
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk_in ∧
      sk_in.core.arena = s2.core.arena ∧ sk_in.core.vals = s2.core.vals ∧
      sk_in.core.inconsistent = 0#64 ∧ sk_in.scratch = s2.scratch ∧ msz.toNat ≤ cv0 ∧
      (∀ j < msz.toNat, (sk_in.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ l < 2 * c.max_vars, sk_in.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j < msz.toNat, (sk_in.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
        ∀ j < k.toNat,
          evalLitVal α (sk_in.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat = true →
          ∃ q < msz.toNat, evalLitVal α (sk_in.core.tmp[q]?.getD 0#32).toNat = true) ∧
      (FullMem c sk_in ⋆ R) mk_in)
    (fun (_, k, ()) _ => csz.toNat - k.toNat)
    (fun Jk hJk => by
      m6b_let
      exact hJk (0#32, 0#32, ()) m2
        ⟨s2, Nat.zero_le _, hb_2, rfl, rfl, hinc2, rfl, Nat.zero_le _,
         (fun _ hj => absurd hj (Nat.not_lt_zero _)), fun l hl => Or.inl (hlm_2 l hl),
         (fun _ _ _ hj _ => absurd hj (Nat.not_lt_zero _)), hm2⟩)
    (fun Jk (msz, k, ()) mk_in
        ⟨sk_in, hk_le, hb_in, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
         htmp_lt_in, hlm_ok_in, hsem_in, hmk_in⟩ ihk => ?_)
  m6b_split; rotate_left 1
  · have hk_eq : k.toNat = csz.toNat := by
      have h := bv32_ult_not_lt hc; change ¬ k.toNat < csz.toNat at h; omega
    m6b_let
    exact hJk2_ex false false false msz k mk_in
      ⟨sk_in, hb_in, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, fun _ _ _ => hk_eq ▸ hsem_in, hmk_in⟩
  have hk_lt : k.toNat < csz.toNat := bv32_ult_lt hc
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := bv32_add1_lt_of (by omega)
  obtain ⟨hl_arr, hl_lt⟩ := fidFs_k_lit_lt (p := cref.setWidth 64) hb_in har_in
    (by rw [hcr_z]; exact hcref_ref0) (by rw [hcr_z]; exact hng_c2)
    (by rw [hcr_z]; exact hcsz_eq) (by rw [hcr_z]; exact hcr_bd) hk_lt
  let l := sk_in.core.arena[(cref.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hl_arr
  have hpk_n : (cref.setWidth 64 + 3#64 + k.setWidth 64).toNat = cref.toNat + 3 + k.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hcr_z, bv_zext32_toNat,
      show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have har_k_pk : cref.toNat + 3 + k.toNat < sk_in.core.arena.length := by
    rw [har_in, hb_2.1.core_ok.arena_len_arr]; have := hb_2.1.core_ok.arena_len_le
    have := hb_2.2.2.2.2.2.2.2.1; omega
  have hl_get : sk_in.core.arena[cref.toNat + 3 + k.toNat]'har_k_pk = l :=
    list_getElem_congr hpk_n.symm _ _
  have hl_vl : l.toNat < sk_in.core.vals.length := fidFs_base_vals_lt hb_in hl_lt
  have hl_z : (l.setWidth 64).toNat = l.toNat := bv_zext32_toNat l
  have hl_vl_z : (l.setWidth 64).toNat < sk_in.core.vals.length := by rw [hl_z]; exact hl_vl
  clear hc; m6b_steps; m6b_split
  · m6b_let
    exact hJk2_ex true false false msz k mk_in
      ⟨sk_in, hb_in, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun h => Bool.noConfusion h), hmk_in⟩
  clear hc; m6b_split
  · have hl_pk_lt : (sk_in.core.arena[cref.toNat + 3 + k.toNat]'har_k_pk).toNat < 2 * cv0 := by
      rw [hl_get]; exact hl_lt
    have hlt_v : (sk_in.core.vals[(sk_in.core.arena[cref.toNat + 3 +
        k.toNat]'har_k_pk).toNat]?.getD 0#8).slt 0#8 = true := by
      rw [hl_get, List.getElem?_eq_getElem hl_vl, Option.getD_some]
      refine bv8_sext32_slt0_true ?_
      rw [list_getElem_congr hl_z.symm hl_vl _]; exact hc
    have hsem' := fidFs_k_sem_false hb_in.2.1 hb_in.2.2.2.2.2.1 hb_in.2.2.2.2.2.2.2.1
      hsem_in har_k_pk hl_pk_lt hlt_v
    m6b_let
    exact ihk (msz, k + 1#32, ()) mk_in (by dsimp only; rw [hk1]; omega)
      ⟨sk_in, by rw [hk1]; omega, hb_in, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem', hmk_in⟩
  clear hc; m6b_steps; m6b_call hFind
  refine ⟨F_cur, 2 * cv0, sk_in.core.repr, FullReprRest c sk_in ⋆ R,
    hb_in.2.2.2.2.2.2.2.2.2.2.2, hl_lt, focus_full_repr hmk_in,
    fun r repr_r mr hrl_r hrepr_r _ hr_lt heqv_lr hmr => ?_⟩
  let sk_r : FullState := { sk_in with core := { sk_in.core with repr := repr_r } }
  have hmr' : (FullMem c sk_r ⋆ R) mr := unfocus_full_repr hmr
  have hb_r := fidFsBaseOk_with_repr hb_in (hrl_r.trans hb_in.1.core_ok.repr_len) hrepr_r
  have hr_vl : r.toNat < sk_r.core.vals.length := fidFs_base_vals_lt hb_r hr_lt
  have hr_lm : r.toNat < sk_r.core.lit_mark.length := fidFs_base_lm_lt hb_r hr_lt
  have hr1_lm : (r ^^^ 1#32).toNat < sk_r.core.lit_mark.length := by
    rw [FullCongHelpers.bv32_xor1_eq_litNeg]
    exact fidFs_base_lm_lt hb_r (bv32_xor1_lt_even hr_lt)
  have hr_z : (r.setWidth 64).toNat = r.toNat := bv_zext32_toNat r
  have hr_vl_z : (r.setWidth 64).toNat < sk_r.core.vals.length := by rw [hr_z]; exact hr_vl
  have hr_lm_z : (r.setWidth 64).toNat < sk_r.core.lit_mark.length := by rw [hr_z]; exact hr_lm
  have hr1_lm_z : ((r ^^^ 1).setWidth 64).toNat < sk_r.core.lit_mark.length := by
    rw [show (1 : BitVec 32) = 1#32 from rfl, bv_zext32_toNat]; exact hr1_lm
  have heqv_pk : LitEquiv (cnfOfClauses F_cur)
      (sk_r.core.arena[cref.toNat + 3 + k.toNat]'har_k_pk).toNat r.toNat := by
    change LitEquiv (cnfOfClauses F_cur)
      (sk_in.core.arena[cref.toNat + 3 + k.toNat]'har_k_pk).toNat r.toNat
    rw [hl_get]; exact heqv_lr
  m6b_steps; m6b_split
  · m6b_let
    exact hJk2_ex true false false msz k mr
      ⟨sk_r, hb_r, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun h => Bool.noConfusion h), hmr'⟩
  clear hc; m6b_split
  · have hr_slt : (sk_r.core.vals[r.toNat]?.getD 0#8).slt 0#8 = true := by
      rw [List.getElem?_eq_getElem hr_vl, Option.getD_some]
      refine bv8_sext32_slt0_true ?_
      rw [list_getElem_congr hr_z.symm hr_vl _]; exact hc
    have hsem' := fidFs_k_sem_equiv hb_r.2.1 hb_r.2.2.2.2.2.1 hb_r.2.2.2.2.2.2.2.1
      hsem_in har_k_pk hr_lt heqv_pk hr_slt
    m6b_let
    exact ihk (msz, k + 1#32, ()) mr (by dsimp only; rw [hk1]; omega)
      ⟨sk_r, by rw [hk1]; omega, hb_r, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem', hmr'⟩
  clear hc; m6b_split
  · m6b_let
    exact hJk2_ex false true false msz k mr
      ⟨sk_r, hb_r, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun _ h => Bool.noConfusion h), hmr'⟩
  clear hc; m6b_to_group
  refine wp_join_group (ts := [.bool, i32])
    (fun (ovf', msz', ()) m1 => ∃ sk1 : FullState,
      ovf' = false ∧ msz'.toNat ≤ cv0 ∧
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk1 ∧
      sk1.core.arena = s2.core.arena ∧ sk1.core.vals = s2.core.vals ∧
      sk1.core.inconsistent = 0#64 ∧ sk1.scratch = s2.scratch ∧
      (∀ j < msz'.toNat, (sk1.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ l < 2 * c.max_vars, sk1.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j < msz'.toNat, (sk1.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
        ∀ j < k.toNat + 1,
          evalLitVal α (sk1.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat = true →
          ∃ q < msz'.toNat, evalLitVal α (sk1.core.tmp[q]?.getD 0#32).toNat = true) ∧
      (FullMem c sk1 ⋆ R) m1)
    (fun _ ⟨_, msz', ⟨⟩⟩ m1
        ⟨sk1, _, hmsz', hb1, har1, hvl1, hinc1, hscr1, htmp1, hlm1, hsem1, hm1⟩ => by
      m6b_steps
      exact ihk (msz', k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
        ⟨sk1, by rw [hk1]; omega, hb1, har1, hvl1, hinc1, hscr1, hmsz',
         htmp1, hlm1, by rw [hk1]; exact hsem1, hm1⟩)
    ?_
  intro Jov hJov
  m6b_split; rotate_left 1
  · have hneq : sk_r.core.lit_mark[r.toNat]?.getD 0#8 ≠ 0#8 := by
      rw [List.getElem?_eq_getElem hr_lm, Option.getD_some]
      refine bv8_zext32_beq0_false ?_
      rw [list_getElem_congr hr_z.symm hr_lm _]; exact hc
    have hsem' := fidFs_k_sem_mem hsem_in har_k_pk hr_lt hcv_le hlm_ok_in hneq heqv_pk
    m6b_let
    exact hJov (false, msz, ()) mr
      ⟨sk_r, rfl, hmsz_cv, hb_r, har_in, hvl_in, hinc_in, hscr_in,
       htmp_lt_in, hlm_ok_in, hsem', hmr'⟩
  clear hc; m6b_split; rotate_left 1
  · m6b_let
    exact hJk2_ex false false true msz k mr
      ⟨sk_r, hb_r, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun _ _ h => Bool.noConfusion h), hmr'⟩
  have hmsz_lt : msz.toNat < cv0 := by
    have h := bv64_ult_lt hc; rwa [bv_zext32_toNat, bv64_ofNat_toNat_lt (by omega)] at h
  have hmsz1 : (msz + 1#32).toNat = msz.toNat + 1 := bv32_add1_lt_of (by omega)
  have hmsz_arr : msz.toNat < sk_r.core.tmp.length := by
    have := hb_r.1.core_ok.tmp_len_arr; dsimp only [sk_r] at this ⊢; omega
  have hmsz_z : (msz.setWidth 64).toNat = msz.toNat := bv_zext32_toNat msz
  have hmsz_z_arr : (msz.setWidth 64).toNat < sk_r.core.tmp.length := by rw [hmsz_z]; exact hmsz_arr
  clear hc; m6b_steps; rw [hmsz_z, hr_z] at hm
  obtain ⟨htmp', hlm'⟩ := fidFs_lm_set_mark htmp_lt_in hlm_ok_in hr_lt hmsz_arr hr_lm
  have hsem' := fidFs_k_sem_push hsem_in har_k_pk hmsz_arr heqv_pk
  exact hJov (false, msz + 1#32, ()) m
    ⟨_, rfl, by rw [hmsz1]; omega,
     fidFsBaseOk_with_tmp
       (fidFsBaseOk_with_lm hb_r (lm' := sk_r.core.lit_mark.set r.toNat 1#8)
         (by rw [List.length_set]; exact hb_r.1.core_ok.lit_mark_len))
       (tmp' := sk_r.core.tmp.set msz.toNat r)
       (by rw [List.length_set]; exact hb_r.1.core_ok.tmp_len_arr),
     har_in, hvl_in, hinc_in, hscr_in,
     by rw [hmsz1]; exact htmp', by rw [hmsz1]; exact hlm', by rw [hmsz1]; exact hsem', hm⟩

private def fidFs_mch_init_expr {V : Ty → Type} {L : List Ty → Type}
    (pMinClr pFlags pRepr cv64 : V i64)
    (kExit : Tup V [i64, .bool] → Expr V L [i64]) : Expr V L [i64] :=
  .group (sig := [[i64]]) (fun Ji => .cons (fun p =>
    .let_ ⟨.cmp .ult i64, (.var p.1, (.var cv64, ()))⟩ fun p_lt =>
    .jnz (.var p_lt.1)
      (.let_ ⟨.mul i64, (.var p.1, (.imm 4, ()))⟩ fun p2 =>
       .let_ ⟨.add i64, (.var pMinClr, (.var p2.1, ()))⟩ fun p3 =>
       .store (t := i32) (.imm 0) (.var p3.1)
         (.let_ ⟨.add i64, (.var p.1, (.imm 1, ()))⟩ fun pi1 =>
          .jump Ji.1 (.var pi1.1, ())))
      (.group (sig := [[i64, .bool]]) (fun Jm => .cons (fun pm =>
         .let_ ⟨.cmp .ult i64, (.var pm.1, (.var cv64, ()))⟩ fun pm_lt =>
         .jnz (.var pm_lt.1)
           (.group (sig := [[.bool]]) (fun Jhm => .cons (fun phm =>
              .let_ ⟨.add i64, (.var pm.1, (.imm 1, ()))⟩ fun pm1 =>
              .jump Jm.1 (.var pm1.1, (.var phm.1, ()))) .nil)
            fun Jhm =>
            .let_ ⟨.mul i64, (.var pm.1, (.imm 4, ()))⟩ fun pm_off =>
            .let_ ⟨.add i64, (.var pFlags, (.var pm_off.1, ()))⟩ fun pm_ptr =>
            .load i32 (.var pm_ptr.1) fun ldf =>
            .let_ ⟨.and i32, (.var ldf, (.imm 1, ()))⟩ fun pm_and =>
            .let_ ⟨.cmp .ne i32, (.var pm_and.1, (.imm 0, ()))⟩ fun pm_ne =>
            .jnz (.var pm_ne.1)
              (.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_s1 =>
               .let_ ⟨.shl i64, (.var pm.1, (.var p_s1.1, ()))⟩ fun p_sh =>
               .let_ ⟨.trunc 64 32, (.var p_sh.1, ())⟩ fun p_lit =>
               .call "full_cong_find" (as := [i64, i32]) (bs := [i32])
                 (Arg.var pRepr, (Arg.var p_lit.1, ())) fun p_rr =>
               .group (sig := [[.bool]]) (fun Jhm2 => .cons (fun phm2 =>
                  .jump Jhm.1 (.var phm2.1, ())) .nil)
                fun Jhm2 =>
                .let_ ⟨.cmp .ne i32, (.var p_rr.1, (.var p_lit.1, ()))⟩ fun p_neq =>
                .jnz (.var p_neq.1)
                  (.let_ ⟨.mul i64, (.var pm.1, (.imm 4, ()))⟩ fun q1 =>
                   .let_ ⟨.add i64, (.var pMinClr, (.var q1.1, ()))⟩ fun q2 =>
                   .store (t := i32) (.imm 1) (.var q2.1)
                     (.let_ ⟨.lshr i32, (.var p_rr.1, (.imm 1, ()))⟩ fun q3 =>
                      .let_ ⟨.zext 32 64, (.var q3.1, ())⟩ fun q4 =>
                      .let_ ⟨.mul i64, (.var q4.1, (.imm 4, ()))⟩ fun q5 =>
                      .let_ ⟨.add i64, (.var pMinClr, (.var q5.1, ()))⟩ fun q6 =>
                      .store (t := i32) (.imm 1) (.var q6.1)
                        (.jump Jhm2.1 (.imm true, ()))))
                  (.jump Jhm2.1 (.var pm.2.1, ())))
              (.jump Jhm.1 (.var pm.2.1, ())))
           (kExit pm)) .nil)
       fun Jm => .jump Jm.1 (.imm 0, (.imm false, ())))) .nil)
  fun Ji => .jump Ji.1 (.imm 0, ())

private theorem fidFs_mch_init_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {s0 : FullState} {m0 : Mem 64} {pMinClr pFlags pRepr cv64 : Val i64}
    {kExit : Tup Val [i64, .bool] → Expr Val Cont [i64]}
    (hMc : pMinClr = c.pMinClr) (hFl : pFlags = c.pFlags) (hRepr : pRepr = c.pRepr)
    (hcv64 : cv64 = BitVec.ofNat 64 cv0)
    (hd0 : FullDenseInvW c F0 F_cur s0)
    (hcv0 : s0.core.cur_vars = cv0) (hal0 : s0.core.arena_len = alen0)
    (hfl0 : s0.core.fuel = fuel0) (href0 : fullArenaClauseRefs s0 = refs0)
    (hrepr0 : FullCongReprInv F_cur (2 * cv0) s0.core.repr)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hk : ∀ (i2 : Val i64) (hmch : Bool) (si2 : FullState) (mi2 : Mem 64),
      FullDenseInvW c F0 F_cur si2 → si2.core.cur_vars = cv0 →
      si2.core.arena_len = alen0 → si2.core.fuel = fuel0 →
      fullArenaClauseRefs si2 = refs0 → FullCongReprInv F_cur (2 * cv0) si2.core.repr →
      (FullMem c si2 ⋆ R) mi2 → wp Γ Q X (kExit (i2, hmch, ())) mi2) :
    wp Γ Q X (fidFs_mch_init_expr pMinClr pFlags pRepr cv64 kExit) m0 := by
  subst hMc hFl hRepr hcv64
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le : cv0 ≤ c.max_vars := by rw [← hcv0]; exact hd0.1.core_ok.cur_vars_le
  unfold fidFs_mch_init_expr
  refine wp_loop_inv (ts := [i64])
    (fun (i, ()) mi => ∃ si : FullState,
      i.toNat ≤ cv0 ∧ FullDenseInvW c F0 F_cur si ∧
      si.core.cur_vars = cv0 ∧ si.core.arena_len = alen0 ∧ si.core.fuel = fuel0 ∧
      fullArenaClauseRefs si = refs0 ∧ FullCongReprInv F_cur (2 * cv0) si.core.repr ∧
      (FullMem c si ⋆ R) mi)
    (fun (i, ()) _ => cv0 - i.toNat)
    (fun J0 hJ0 => by
      m6b_let
      exact hJ0 (0#64, ()) m0 ⟨s0, Nat.zero_le _, hd0, hcv0, hal0, hfl0, href0, hrepr0, hm0⟩)
    (fun J0 (i, ()) mi ⟨si, hi_le, hdi, hcvi, hali, hfli, hrefsi, hrepri, hmi⟩ ihi => ?_)
  have hmli := hdi.1.core_ok.min_clr_len_arr
  m6b_split
  · have hi_lt : i.toNat < cv0 := by
      have h := bv64_ult_lt hc; rwa [bv64_ofNat_toNat_lt (by omega)] at h
    have hi1_n : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
    have hi_arr : i.toNat < si.core.min_clr.length := by omega
    clear hc; m6b_steps
    let si' : FullState :=
      { si with core := { si.core with min_clr := si.core.min_clr.set i.toNat 0#32 } }
    exact ihi (i + 1#64, ()) m (by dsimp only; omega)
      ⟨si', by rw [hi1_n]; omega, fid_denseInvW_with_mclr hdi (by simp [hmli]),
       hcvi, hali, hfli, hrefsi, hrepri, hm⟩
  clear hc J0 hi_le hmli ihi hd0 hrepr0 hm0
  m6b_to_group
  refine wp_loop_inv (ts := [i64, .bool])
    (fun (i2, _hmch, ()) mi2 => ∃ si2 : FullState,
      i2.toNat ≤ cv0 ∧ FullDenseInvW c F0 F_cur si2 ∧
      si2.core.cur_vars = cv0 ∧ si2.core.arena_len = alen0 ∧ si2.core.fuel = fuel0 ∧
      fullArenaClauseRefs si2 = refs0 ∧ FullCongReprInv F_cur (2 * cv0) si2.core.repr ∧
      (FullMem c si2 ⋆ R) mi2)
    (fun (i2, _, ()) _ => cv0 - i2.toNat)
    (fun Jm hJm => by
      m6b_steps
      exact hJm (0#64, false, ()) mi
        ⟨si, Nat.zero_le _, hdi, hcvi, hali, hfli, hrefsi, hrepri, hmi⟩)
    (fun Jm (i2, hmch, ()) mi2
        ⟨si2, hi2_le, hdi2, hcvi2, hali2, hfli2, hrefsi2, hrepri2, hmi2⟩ ihm => ?_)
  have hfl_len2 := hdi2.1.core_ok.flags_len
  have hmli2 := hdi2.1.core_ok.min_clr_len_arr
  m6b_split
  · have hi2_lt : i2.toNat < cv0 := by
      have h := bv64_ult_lt hc; rwa [bv64_ofNat_toNat_lt (by omega)] at h
    have hi2_1 : (i2 + 1#64).toNat = i2.toNat + 1 := bv64_add1_lt (by omega)
    have hi2_fl : i2.toNat < si2.core.flags.length := by omega
    clear hc; m6b_to_group
    refine wp_join_group (ts := [.bool])
      (fun (_hm', ()) mj => ∃ sj : FullState,
        FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = cv0 ∧
        sj.core.arena_len = alen0 ∧ sj.core.fuel = fuel0 ∧
        fullArenaClauseRefs sj = refs0 ∧ FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧
        (FullMem c sj ⋆ R) mj)
      (fun _ ⟨hm', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, halj, hflj, hrefsj, hreprj, hmj⟩ => by
        m6b_steps
        exact ihm (i2 + 1#64, hm', ()) mj (by dsimp only; omega)
          ⟨sj, by rw [hi2_1]; omega, hdj, hcvj, halj, hflj, hrefsj, hreprj, hmj⟩)
      (fun Jhm hJhm => by
        m6b_split; rotate_left 1
        · m6b_let; exact hJhm (hmch, ()) mi2
            ⟨si2, hdi2, hcvi2, hali2, hfli2, hrefsi2, hrepri2, hmi2⟩
        have hlit_n : (BitVec.setWidth 32 (i2 <<< (1 : Nat))).toNat = 2 * i2.toNat := by
          rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
            Nat.mul_comm, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        clear hc; m6b_steps; m6b_call hFind
        refine ⟨F_cur, 2 * cv0, si2.core.repr, FullReprRest c si2 ⋆ R,
          hrepri2, by rw [hlit_n]; omega, focus_full_repr hmi2,
          fun rr repr_r mr hrl_r hrepr_r _ hrr_lt _ hmr => ?_⟩
        let sr : FullState := { si2 with core := { si2.core with repr := repr_r } }
        have hmr' : (FullMem c sr ⋆ R) mr := unfocus_full_repr hmr
        have hdr := fid_denseInvW_with_repr hdi2 (hrl_r.trans hdi2.1.core_ok.repr_len)
        m6b_to_group
        refine wp_join_group (ts := [.bool])
          (fun (_hm'', ()) mj => ∃ sj : FullState,
            FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = cv0 ∧
            sj.core.arena_len = alen0 ∧ sj.core.fuel = fuel0 ∧
            fullArenaClauseRefs sj = refs0 ∧ FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧
            (FullMem c sj ⋆ R) mj)
          (fun _ ⟨hm'', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, halj, hflj, hrefsj, hreprj, hmj⟩ =>
            hJhm (hm'', ()) mj ⟨sj, hdj, hcvj, halj, hflj, hrefsj, hreprj, hmj⟩)
          (fun Jhm2 hJhm2 => by
            m6b_split; rotate_left 1
            · m6b_let; exact hJhm2 (hmch, ()) mr
                ⟨sr, hdr, hcvi2, hali2, hfli2, hrefsi2, hrepr_r, hmr'⟩
            have hri_mc : i2.toNat < sr.core.min_clr.length := by
              change i2.toNat < si2.core.min_clr.length; omega
            have hrr1_n : ((rr >>> 1#32).setWidth 64).toNat = rr.toNat / 2 := by
              rw [bv_zext32_toNat, show (rr >>> 1#32 : BitVec 32) = rr >>> (1 : Nat) from rfl,
                BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
            have hrr1_mc : ((rr >>> 1#32).setWidth 64).toNat <
                (sr.core.min_clr.set i2.toNat 1#32).length := by
              rw [List.length_set, hrr1_n]; change rr.toNat / 2 < si2.core.min_clr.length; omega
            clear hc; m6b_steps
            have hsr_mcl : sr.core.min_clr.length = c.max_vars := hmli2
            exact hJhm2 (true, ()) m ⟨_, fid_denseInvW_with_mclr
              (fid_denseInvW_with_mclr hdr (by rw [List.length_set]; exact hsr_mcl))
              (by rw [List.length_set, List.length_set]; exact hsr_mcl),
              hcvi2, hali2, hfli2, hrefsi2, hrepr_r, hm⟩))
  exact hk i2 hmch si2 mi2 hdi2 hcvi2 hali2 hfli2 hrefsi2 hrepri2 hmi2

theorem full_cong_fwd_subsume_wp (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hSortPairs : ∀ a m Q X, fidCongSortPairsSpec a m Q X →
      Γ "full_cong_sort_pairs_fid" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
      Func.wp Γ full_cong_fwd_subsume_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hd0, hrepr0, hm0, hQ⟩
  have hmx := c.hmaxv; have hac := c.harena; have hwc := c.hwcap; have hsc := c.hscr
  unfold dimacsBound at hmx hac hwc hsc
  let cv0 := s0.core.cur_vars; let alen0 := s0.core.arena_len; let fuel0 := s0.core.fuel
  let refs0 := fullArenaClauseRefs s0
  have hcv_le : cv0 ≤ c.max_vars := hd0.1.core_ok.cur_vars_le
  unfold Func.wp full_cong_fwd_subsume_body
  -- Early exit 1: inconsistent != 0 || ant_sz != 0
  m6b_to_group
  refine wp_join_group (ts := [])
    (fun () mj => mj = m0 ∧ (s0.core.inconsistent ≠ 0#64 ∨ s0.scratch.ant_sz ≠ 0#64))
    (fun _ ⟨⟩ mj ⟨hmj, _⟩ => by
      have hmj0 : (FullMem c s0 ⋆ R) mj := hmj ▸ hm0
      m6b_to_group
      refine wp_join_group (ts := [i64])
        (fun (r, ()) mr => mr = mj ∧ (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
        (fun _ ⟨r, ⟨⟩⟩ mr ⟨hmr, hr_dom, huns⟩ => by
          m6b_steps; exact hQ r s0 mr hd0 rfl rfl hrepr0 hr_dom huns (hmr ▸ hmj0))
        (fun Jret hJret => by
          m6b_split
          · m6b_let
            exact hJret (20#64, ()) mj ⟨rfl, Or.inr rfl, fun _ =>
              FullM3CongBva.unsat_of_inconsistent_w hd0.2.1 (bne_iff_ne.mp hc)⟩
          m6b_let; exact hJret (1#64, ()) mj ⟨rfl, Or.inl rfl, fun h => by cases h⟩))
    ?_
  intro Jearly hJearly
  m6b_split
  · m6b_let; exact hJearly () m0 ⟨rfl, Or.inl (bne_iff_ne.mp hc)⟩
  clear hc; m6b_split
  · m6b_let; exact hJearly () m0 ⟨rfl, Or.inr (bne_iff_ne.mp hc)⟩
  clear hc Jearly hJearly
  -- Clamp tick_lim <= 0x7FFFFFFFFFFFFFFF
  m6b_to_group
  refine wp_join_group (ts := [i64])
    (fun (tl, ()) mtl => mtl = m0 ∧ tl.toNat ≤ 0x7FFFFFFFFFFFFFFF)
    ?_
    (fun Jtl hJtl => by
      m6b_split
      · m6b_let; exact hJtl (0x7FFFFFFFFFFFFFFF#64, ()) m0 ⟨rfl, by decide⟩
      have hle : tick_lim.toNat ≤ 0x7FFFFFFFFFFFFFFF := by
        have h := bv64_ult_not_lt hc
        change ¬ 0x7FFFFFFFFFFFFFFF < tick_lim.toNat at h; omega
      m6b_let; exact hJtl (tick_lim, ()) m0 ⟨rfl, hle⟩)
  rintro _ ⟨tl, ⟨⟩⟩ mtl ⟨hmtl, htl_le⟩; subst mtl
  -- Early exit 2: tick_lim == 0 || scratch_cap < 4
  m6b_split
  · m6b_steps; exact hQ 1#64 s0 m0 hd0 rfl rfl hrepr0 (Or.inl rfl) (fun h => by cases h) hm0
  have htl_pos : 0 < tl.toNat := by
    have hne : tl ≠ 0#64 := beq_eq_false_iff_ne.mp hc
    have h0 : tl.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
    omega
  clear hc; m6b_split
  · m6b_steps; exact hQ 1#64 s0 m0 hd0 rfl rfl hrepr0 (Or.inl rfl) (fun h => by cases h) hm0
  have hcap4 : 4 ≤ c.scratch_cap := by
    have h := bv64_ult_not_lt hc
    rw [bv64_ofNat_toNat_lt (by omega)] at h; change ¬ c.scratch_cap < 4 at h; omega
  clear hc
  -- Init mch[0 ..< cv0) = 0 and mark merged vars
  m6b_steps
  refine fidFs_mch_init_wp Γ hFind rfl rfl rfl rfl hd0 rfl rfl rfl rfl hrepr0 hm0
    fun _i2 hmch si2 mi2 hdi2 hcvi2 hali2 hfli2 hrefsi2 hrepri2 hmi2 => ?_
  -- if (!has_mch) { return 1ULL; }
  m6b_split; rotate_left 1
  · m6b_steps
    exact hQ 1#64 si2 mi2 hdi2 hcvi2 hfli2 (hcvi2 ▸ hrepri2) (Or.inl rfl)
      (fun h => by cases h) hmi2
  clear hc
  -- Pass 1: collect candidate clauses into scr[0 ..< 2 * ncand)
  have hmaxc_n : ((BitVec.ofNat 64 c.scratch_cap) >>> 2#64).toNat = c.scratch_cap / 4 := by
    rw [bv64_shr2_toNat, bv64_ofNat_toNat_lt (by omega)]
  m6b_to_group
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (ncand, p, ticks, ()) mp => ∃ sp : FullState,
      ncand.toNat ≤ c.scratch_cap / 4 ∧
      p.toNat ≤ alen0 ∧ (p.toNat = alen0 ∨ p.toNat ∈ refs0) ∧
      ticks.toNat ≤ tl.toNat ∧
      FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = cv0 ∧
      sp.core.arena_len = alen0 ∧ sp.core.fuel = fuel0 ∧
      fullArenaClauseRefs sp = refs0 ∧
      FullCongReprInv F_cur (2 * cv0) sp.core.repr ∧
      FidPairsOk (fun _ cr => cr.toNat ∈ refs0) sp.scratch.scratch_buf ncand.toNat ∧
      (FullMem c sp ⋆ R) mp)
    (fun (_, p, _, ()) _ => alen0 - p.toNat)
    (fun Jp hJp => by
      have h0_mem : 0 = alen0 ∨ 0 ∈ refs0 := by
        rcases Nat.eq_zero_or_pos alen0 with hz | hpos
        · exact Or.inl hz.symm
        · refine Or.inr ?_
          change 0 ∈ fullArenaClauseRefs s0
          rw [← hrefsi2]
          exact fullArenaClauseRefs_zero_mem hdi2.2.1 (by rw [hali2]; exact hpos)
      m6b_steps
      exact hJp (0#64, 0#64, 0#64, ()) mi2
        ⟨si2, Nat.zero_le _, Nat.zero_le _, h0_mem, Nat.zero_le _,
         hdi2, hcvi2, hali2, hfli2, hrefsi2, hrepri2, fun _ h => absurd h (Nat.not_lt_zero _),
           hmi2⟩)
    (fun Jp (ncand, p, ticks, ()) mp
        ⟨sp, hnc_le, hp_le, hp_mem, htk_le, hdp, hcvp, halp, hflp, hrefsp, hreprp, hpairs, hmp⟩
        ihp => ?_)
  clear hdi2 hcvi2 hali2 hfli2 hrefsi2 hrepri2 hmi2
  m6b_to_group
  refine wp_join_group (ts := [])
    (fun () me => ∃ se : FullState,
      ncand.toNat ≤ c.scratch_cap / 4 ∧ ticks.toNat ≤ tl.toNat ∧
      FullDenseInvW c F0 F_cur se ∧ se.core.cur_vars = cv0 ∧
      se.core.arena_len = alen0 ∧ se.core.fuel = fuel0 ∧
      fullArenaClauseRefs se = refs0 ∧ FullCongReprInv F_cur (2 * cv0) se.core.repr ∧
      FidPairsOk (fun _ cr => cr.toNat ∈ refs0) se.scratch.scratch_buf ncand.toNat ∧
      (FullMem c se ⋆ R) me)
    ?_
    ?_
  rotate_left 1
  -- Pass 1 loop body
  · intro Jexit1 hJexit1
    have hpass1_exit : Jexit1 () mp := hJexit1 () mp
      ⟨sp, hnc_le, htk_le, hdp, hcvp, halp, hflp, hrefsp, hreprp, hpairs, hmp⟩
    m6b_split; rotate_left 1
    · clear hc; m6b_let; exact hpass1_exit
    have har_le_p := hdp.1.core_ok.arena_len_le
    have har_arr_p := hdp.1.core_ok.arena_len_arr
    have hp_lt : p.toNat < alen0 := by
      have h := bv64_ult_lt hc; rwa [halp, bv64_ofNat_toNat_lt (by omega)] at h
    clear hc; m6b_split; rotate_left 1
    · clear hc; m6b_let; exact hpass1_exit
    have htk_lt : ticks.toNat < tl.toNat := bv64_ult_lt hc
    have htk1_n : (ticks + 1#64).toNat = ticks.toNat + 1 := bv64_add1_lt (by omega)
    clear hc; m6b_split; rotate_left 1
    · clear hc; m6b_let; exact hpass1_exit
    have hinc0 : sp.core.inconsistent = 0#64 := by simpa using hc
    have hp_ref0 : p.toNat ∈ refs0 := hp_mem.resolve_left (by omega)
    have hp_ref : p.toNat ∈ fullArenaClauseRefs sp := hrefsp.symm ▸ hp_ref0
    have hp_wf := hdp.2.1.arena.refs_wf p.toNat hp_ref
    have hp_arr0 : p.toNat < sp.core.arena.length := by omega
    have hp2_n : (p + 2#64).toNat = p.toNat + 2 := bv64_add2_lt (by omega)
    have hp_arr2 : (p + 2#64).toNat < sp.core.arena.length := by rw [hp2_n]; omega
    have hp_32n : (p.setWidth 32).toNat = p.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    clear hc Jexit1 hJexit1 hpass1_exit; m6b_steps
    refine LeanQbe.T.wp_call_of_spec _ _ (hNext _ _ _ _ ?_)
    dsimp only [LeanQbe.T.vals_nil, LeanQbe.T.vals_cons,
      LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
    refine ⟨c, sp, R, rfl, hdp.1, hmp, ?_⟩
    let np_nat := fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat
    have hnp_bds := fullArenaNextOff_bounds (ar := sp.core.arena)
      (alen := sp.core.arena_len) (cref := p.toNat) hp_wf.1
    let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena
      sp.core.arena_len (p.setWidth 32).toNat)).setWidth 64
    have hnp_n : np.toNat = np_nat := by
      dsimp only [np, np_nat]
      rw [hp_32n, bv_zext32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hnp_mem : np_nat = alen0 ∨ np_nat ∈ refs0 := by
      have h := fullArenaClauseRefs_next_or_end hdp.2.1 hp_ref
      exact h.elim (fun h1 => Or.inl (h1.trans halp)) fun h2 => Or.inr (hrefsp ▸ h2)
    have hsz_eq : fullArenaClauseSizeCore sp.core p.toNat =
        (sp.core.arena[(p + 2#64).toNat]'hp_arr2).toNat := by
      unfold fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (list_getElem_congr hp2_n.symm _ _)
    m6b_split
    · clear hc; m6b_let
      exact ihp (ncand, np, ticks + 1#64, ()) mp (by dsimp only; rw [hnp_n]; omega)
        ⟨sp, hnc_le, by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem, by rw [htk1_n]; omega,
         hdp, hcvp, halp, hflp, hrefsp, hreprp, hpairs, hmp⟩
    have hgarb0 : ((sp.core.arena[p.toNat]'hp_arr0) &&& 0x00080000#32) = 0#32 := by simpa using hc
    clear hc; m6b_split
    · clear hc; m6b_let
      exact ihp (ncand, np, ticks + 1#64, ()) mp (by dsimp only; rw [hnp_n]; omega)
        ⟨sp, hnc_le, by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem, by rw [htk1_n]; omega,
         hdp, hcvp, halp, hflp, hrefsp, hreprp, hpairs, hmp⟩
    let hdr := sp.core.arena[p.toNat]'hp_arr0
    let sz := sp.core.arena[(p + 2#64).toNat]'hp_arr2
    have hsz3 : 3 ≤ sz.toNat := by
      have h := bv32_ult_not_lt hc
      rw [show (3 : BitVec 32).toNat = 3 from rfl] at h; change ¬ sz.toNat < 3 at h; omega
    have hng_p : fullArenaClauseGarb sp p.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem hp_arr0, Option.getD_some]
      exact fid_garb_false_of_and hgarb0
    have hsz_cv : sz.toNat ≤ cv0 := by
      rw [← hcvp, ← hsz_eq]
      exact fullArenaClauseSize_le_cur_vars hdp.1 hdp.2.1 hdp.2.2.2.1 hp_ref hng_p
    have hp_bd : p.toNat + 3 + sz.toNat ≤ alen0 := by
      dsimp only [sz]
      have h1 := hp_wf.2.2.1; have h2 := hp_wf.2.2.2.1; rw [hsz_eq] at h1; omega
    obtain ⟨hb_p, hlm_p⟩ := fidFsBaseOk_of_dense hdp hcvp halp hflp hrefsp hreprp
    clear hc; m6b_to_group
    refine wp_join_group (ts := [.bool, .bool, .bool, .bool, i32, i32])
      (fun (sat, taut, _c_mch, ovf, msz, _k, ()) mk => ∃ sk : FullState,
        FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk ∧
        sk.core.arena = sp.core.arena ∧ sk.core.vals = sp.core.vals ∧
        sk.core.min_clr = sp.core.min_clr ∧ sk.core.inconsistent = 0#64 ∧
        sk.scratch = sp.scratch ∧ msz.toNat ≤ cv0 ∧
        (∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
        (∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
          (∃ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
        (sat = false → taut = false → ovf = false →
          ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
            ∀ j < sz.toNat,
              evalLitVal α (sk.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat = true →
              ∃ q < msz.toNat, evalLitVal α (sk.core.tmp[q]?.getD 0#32).toNat = true) ∧
        (FullMem c sk ⋆ R) mk)
      ?_ ?_
    rotate_left 1
    -- Pass 1 inner clause reduction loop (k < sz)
    · intro Jk1_ex hJk1_ex
      m6b_steps
      refine wp_loop_inv (ts := [.bool, i32, i32])
        (fun (_c_mch, msz, k, ()) mk_in => ∃ sk_in : FullState,
          k.toNat ≤ sz.toNat ∧
          FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk_in ∧
          sk_in.core.arena = sp.core.arena ∧ sk_in.core.vals = sp.core.vals ∧
          sk_in.core.min_clr = sp.core.min_clr ∧ sk_in.core.inconsistent = 0#64 ∧
          sk_in.scratch = sp.scratch ∧ msz.toNat ≤ cv0 ∧
          (∀ j < msz.toNat, (sk_in.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
          (∀ l < 2 * c.max_vars, sk_in.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
            (∃ j < msz.toNat, (sk_in.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
          (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
            ∀ j < k.toNat,
              evalLitVal α (sk_in.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat = true →
              ∃ q < msz.toNat, evalLitVal α (sk_in.core.tmp[q]?.getD 0#32).toNat = true) ∧
          (FullMem c sk_in ⋆ R) mk_in)
        (fun (_, _, k, ()) _ => sz.toNat - k.toNat)
        (fun Jk hJk => by
          m6b_let
          exact hJk (false, 0#32, 0#32, ()) mp
            ⟨sp, Nat.zero_le _, hb_p, rfl, rfl, rfl, hinc0, rfl, Nat.zero_le _,
             (fun _ hj => absurd hj (Nat.not_lt_zero _)),
             fun l hl => Or.inl (hlm_p l hl),
             (fun _ _ _ hj _ => absurd hj (Nat.not_lt_zero _)), hmp⟩)
        (fun Jk (c_mch, msz, k, ()) mk_in
            ⟨sk_in, hk_le, hb_in, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
             htmp_lt_in, hlm_ok_in, hsem_in, hmk_in⟩ ihk => ?_)
      m6b_split; rotate_left 1
      · have hk_eq : k.toNat = sz.toNat := by
          have h : ¬ k.toNat < sz.toNat := bv32_ult_not_lt hc; omega
        m6b_let
        exact hJk1_ex (false, false, c_mch, false, msz, k, ()) mk_in
          ⟨sk_in, hb_in, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
           htmp_lt_in, hlm_ok_in, fun _ _ _ => hk_eq ▸ hsem_in, hmk_in⟩
      have hk_lt : k.toNat < sz.toNat := bv32_ult_lt hc
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := bv32_add1_lt_of (by omega)
      obtain ⟨hl_arr, hl_lt⟩ := fidFs_k_lit_lt hb_in har_in hp_ref0 hng_p hsz_eq hp_bd hk_lt
      let l := sk_in.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hl_arr
      have hpk_n : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
          show (3#64 : BitVec 64).toNat = 3 from rfl,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have har_k_pk : p.toNat + 3 + k.toNat < sk_in.core.arena.length := by rw [har_in]; omega
      have hl_get : sk_in.core.arena[p.toNat + 3 + k.toNat]'har_k_pk = l :=
        list_getElem_congr hpk_n.symm _ _
      have hl_vl : l.toNat < sk_in.core.vals.length := fidFs_base_vals_lt hb_in hl_lt
      have hl_z : (l.setWidth 64).toNat = l.toNat := bv_zext32_toNat l
      clear hc; m6b_split
      · m6b_let
        exact hJk1_ex (true, false, c_mch, false, msz, k, ()) mk_in
          ⟨sk_in, hb_in, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
           htmp_lt_in, hlm_ok_in, (fun h => Bool.noConfusion h), hmk_in⟩
      clear hc; m6b_split
      · have hl_pk_lt : (sk_in.core.arena[p.toNat + 3 + k.toNat]'har_k_pk).toNat < 2 * cv0 := by
          rw [hl_get]; exact hl_lt
        have hlt_v : (sk_in.core.vals[(sk_in.core.arena[p.toNat + 3 +
            k.toNat]'har_k_pk).toNat]?.getD 0#8).slt 0#8 = true := by
          rw [hl_get, List.getElem?_eq_getElem hl_vl, Option.getD_some]
          refine bv8_sext32_slt0_true ?_
          rw [list_getElem_congr hl_z.symm hl_vl _]; exact hc
        have hsem' := fidFs_k_sem_false hb_in.2.1 hb_in.2.2.2.2.2.1 hb_in.2.2.2.2.2.2.2.1
          hsem_in har_k_pk hl_pk_lt hlt_v
        m6b_let
        exact ihk (c_mch, msz, k + 1#32, ()) mk_in (by dsimp only; rw [hk1]; omega)
          ⟨sk_in, by rw [hk1]; omega, hb_in, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
           htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem', hmk_in⟩
      have hl1_mc : ((l >>> 1#32).setWidth 64).toNat < sk_in.core.min_clr.length := by
        rw [bv_zext32_toNat, show (l >>> 1#32 : BitVec 32) = l >>> (1 : Nat) from rfl,
          BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
        have hl_cv : l.toNat < 2 * cv0 := hl_lt
        have := hb_in.1.core_ok.min_clr_len_arr; omega
      clear hc; m6b_to_group
      refine wp_join_group (ts := [.bool]) (fun _ mc1 => mk_in = mc1) ?_
        (fun Jcm hJcm => by
          m6b_split
          · m6b_let; exact hJcm (true, ()) mk_in rfl
          m6b_let; exact hJcm (c_mch, ()) mk_in rfl)
      rintro _ ⟨c_mch', ⟨⟩⟩ mc1 rfl
      m6b_steps; m6b_call hFind
      refine ⟨F_cur, 2 * cv0, sk_in.core.repr, FullReprRest c sk_in ⋆ R,
        hb_in.2.2.2.2.2.2.2.2.2.2.2, hl_lt, focus_full_repr hmk_in,
        fun r repr_r mr hrl_r hrepr_r _ hr_lt heqv_lr hmr => ?_⟩
      let sk_r : FullState := { sk_in with core := { sk_in.core with repr := repr_r } }
      have hmr' : (FullMem c sk_r ⋆ R) mr := unfocus_full_repr hmr
      have hb_r := fidFsBaseOk_with_repr hb_in (hrl_r.trans hb_in.1.core_ok.repr_len) hrepr_r
      have hr_vl : r.toNat < sk_r.core.vals.length := fidFs_base_vals_lt hb_r hr_lt
      have hr_lm : r.toNat < sk_r.core.lit_mark.length := fidFs_base_lm_lt hb_r hr_lt
      have hr1_lm : (r ^^^ 1#32).toNat < sk_r.core.lit_mark.length := by
        rw [FullCongHelpers.bv32_xor1_eq_litNeg]
        exact fidFs_base_lm_lt hb_r (bv32_xor1_lt_even hr_lt)
      have hr_z : (r.setWidth 64).toNat = r.toNat := bv_zext32_toNat r
      have heqv_pk : LitEquiv (cnfOfClauses F_cur)
          (sk_r.core.arena[p.toNat + 3 + k.toNat]'har_k_pk).toNat r.toNat := by
        change LitEquiv (cnfOfClauses F_cur)
          (sk_in.core.arena[p.toNat + 3 + k.toNat]'har_k_pk).toNat r.toNat
        rw [hl_get]; exact heqv_lr
      m6b_split
      · m6b_let
        exact hJk1_ex (true, false, c_mch', false, msz, k, ()) mr
          ⟨sk_r, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
           htmp_lt_in, hlm_ok_in, (fun h => Bool.noConfusion h), hmr'⟩
      clear hc; m6b_split
      · have hr_slt : (sk_r.core.vals[r.toNat]?.getD 0#8).slt 0#8 = true := by
          rw [List.getElem?_eq_getElem hr_vl, Option.getD_some]
          refine bv8_sext32_slt0_true ?_
          rw [list_getElem_congr hr_z.symm hr_vl _]; exact hc
        have hsem' := fidFs_k_sem_equiv hb_r.2.1 hb_r.2.2.2.2.2.1 hb_r.2.2.2.2.2.2.2.1
          hsem_in har_k_pk hr_lt heqv_pk hr_slt
        m6b_let
        exact ihk (c_mch', msz, k + 1#32, ()) mr (by dsimp only; rw [hk1]; omega)
          ⟨sk_r, by rw [hk1]; omega, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
           htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem', hmr'⟩
      clear hc; m6b_split
      · m6b_let
        exact hJk1_ex (false, true, c_mch', false, msz, k, ()) mr
          ⟨sk_r, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
           htmp_lt_in, hlm_ok_in, (fun _ h => Bool.noConfusion h), hmr'⟩
      clear hc; m6b_to_group
      refine wp_join_group (ts := [.bool, i32])
        (fun (ovf', msz', ()) m1 => ∃ sk1 : FullState,
          ovf' = false ∧ msz'.toNat ≤ cv0 ∧
          FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk1 ∧
          sk1.core.arena = sp.core.arena ∧ sk1.core.vals = sp.core.vals ∧
          sk1.core.min_clr = sp.core.min_clr ∧ sk1.core.inconsistent = 0#64 ∧
          sk1.scratch = sp.scratch ∧
          (∀ j < msz'.toNat, (sk1.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
          (∀ l < 2 * c.max_vars, sk1.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
            (∃ j < msz'.toNat, (sk1.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
          (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
            ∀ j < k.toNat + 1,
              evalLitVal α (sk1.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat = true →
              ∃ q < msz'.toNat, evalLitVal α (sk1.core.tmp[q]?.getD 0#32).toNat = true) ∧
          (FullMem c sk1 ⋆ R) m1)
        (fun _ ⟨_, msz', ⟨⟩⟩ m1
            ⟨sk1, _, hmsz', hb1, har1, hvl1, hmc1, hinc1, hscr1, htmp1, hlm1, hsem1, hm1⟩ => by
          m6b_steps
          exact ihk (c_mch', msz', k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
            ⟨sk1, by rw [hk1]; omega, hb1, har1, hvl1, hmc1, hinc1, hscr1, hmsz',
             htmp1, hlm1, by rw [hk1]; exact hsem1, hm1⟩)
        ?_
      intro Jov hJov
      m6b_split; rotate_left 1
      · have hneq : sk_r.core.lit_mark[r.toNat]?.getD 0#8 ≠ 0#8 := by
          rw [List.getElem?_eq_getElem hr_lm, Option.getD_some]
          refine bv8_zext32_beq0_false ?_
          rw [list_getElem_congr hr_z.symm hr_lm _]; exact hc
        have hsem' := fidFs_k_sem_mem hsem_in har_k_pk hr_lt hcv_le hlm_ok_in hneq heqv_pk
        m6b_let
        exact hJov (false, msz, ()) mr
          ⟨sk_r, rfl, hmsz_cv, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in,
           htmp_lt_in, hlm_ok_in, hsem', hmr'⟩
      clear hc; m6b_split; rotate_left 1
      · m6b_let
        exact hJk1_ex (false, false, c_mch', true, msz, k, ()) mr
          ⟨sk_r, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
           htmp_lt_in, hlm_ok_in, (fun _ _ h => Bool.noConfusion h), hmr'⟩
      have hmsz_lt : msz.toNat < cv0 := by
        have h := bv64_ult_lt hc; rwa [bv_zext32_toNat, bv64_ofNat_toNat_lt (by omega)] at h
      have hmsz1 : (msz + 1#32).toNat = msz.toNat + 1 := bv32_add1_lt_of (by omega)
      have hmsz_arr : msz.toNat < sk_r.core.tmp.length := by
        dsimp only [sk_r]; have := hb_in.1.core_ok.tmp_len_arr; omega
      have hmsz_z : (msz.setWidth 64).toNat = msz.toNat := bv_zext32_toNat msz
      clear hc; m6b_steps; rw [hmsz_z, hr_z] at hm
      obtain ⟨htmp', hlm'⟩ := fidFs_lm_set_mark htmp_lt_in hlm_ok_in hr_lt hmsz_arr hr_lm
      have hsem' := fidFs_k_sem_push hsem_in har_k_pk hmsz_arr heqv_pk
      exact hJov (false, msz + 1#32, ()) m
        ⟨_, rfl, by rw [hmsz1]; omega,
         fidFsBaseOk_with_tmp
           (fidFsBaseOk_with_lm hb_r (lm' := sk_r.core.lit_mark.set r.toNat 1#8)
             (by rw [List.length_set]; exact hb_r.1.core_ok.lit_mark_len))
           (tmp' := sk_r.core.tmp.set msz.toNat r)
           (by rw [List.length_set]; exact hb_r.1.core_ok.tmp_len_arr),
         har_in, hvl_in, hmc_in, hinc_in, hscr_in,
         by rw [hmsz1]; exact htmp', by rw [hmsz1]; exact hlm', by rw [hmsz1]; exact hsem', hm⟩
    -- Pass 1 post-reduction: clear lm,
    -- then branch on sat||taut / ovf / msz==0 / msz==1 / !c_mch / push
    rintro _ ⟨sat, taut, c_mch, ovf, msz, _k, ⟨⟩⟩ mk
      ⟨sk, hbk, hark, hvlk, hmck, hinck, hscrk, hmsz_cv, htmp_lt, hlm_ok, hsem_ok, hmk⟩
    m6b_to_group
    refine wp_loop_inv (ts := [i32])
      (fun (kc, ()) mc => ∃ sc : FullState,
        kc.toNat ≤ msz.toNat ∧
        FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sc ∧
        sc.core.arena = sp.core.arena ∧ sc.core.tmp = sk.core.tmp ∧
        sc.core.inconsistent = 0#64 ∧ sc.scratch = sp.scratch ∧
        (∀ l < 2 * c.max_vars, sc.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
          (∃ j, kc.toNat ≤ j ∧ j < msz.toNat ∧
            (sc.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
        (FullMem c sc ⋆ R) mc)
      (fun (kc, ()) _ => msz.toNat - kc.toNat)
      (fun Jc hJc => by
        m6b_steps
        exact hJc (0#32, ()) mk
          ⟨sk, Nat.zero_le _, hbk, hark, rfl, hinck, hscrk,
           fidFs_lm_clear_from_zero hlm_ok, hmk⟩)
      (fun Jc (kc, ()) mc ⟨sc, hkc_le, hbc, harc, htmpc, hincc, hscrc, hlmc, hmc⟩ ihc => ?_)
    m6b_split
    · have hkc_lt : kc.toNat < msz.toNat := bv32_ult_lt hc
      have hkc1 : (kc + 1#32).toNat = kc.toNat + 1 := bv32_add1_lt_of (by omega)
      have hkc_arr : kc.toNat < sc.core.tmp.length := by
        have := hbc.1.core_ok.tmp_len_arr; omega
      let rk := sc.core.tmp[kc.toNat]'hkc_arr
      have hrk_lt : rk.toNat < 2 * cv0 := by
        have h := htmp_lt kc.toNat hkc_lt
        rwa [← htmpc, List.getElem?_eq_getElem hkc_arr, Option.getD_some] at h
      have hrk_arr : rk.toNat < sc.core.lit_mark.length := fidFs_base_lm_lt hbc hrk_lt
      have hkc_z : (kc.setWidth 64).toNat = kc.toNat := bv_zext32_toNat kc
      have hlmc' : ∀ l < 2 * c.max_vars,
          (sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0))[l]?.getD 0#8 = 0#8 ∨
            (∃ j, (kc + 1#32).toNat ≤ j ∧ j < msz.toNat ∧
              (sc.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0) := by
        rw [hkc1]; exact fidFs_lm_clear_step hkc_lt hkc_arr hrk_arr hlmc
      have hlm_set_eq : sc.core.lit_mark.set
          ((sc.core.tmp[(kc.setWidth 64).toNat]'(by rw [hkc_z]; exact hkc_arr)).setWidth 64).toNat
          (BitVec.ofNat 8 0) = sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0) :=
        congrArg (sc.core.lit_mark.set · _) (by
          rw [bv_zext32_toNat]; exact congrArg BitVec.toNat (list_getElem_congr hkc_z _ _))
      clear hc; m6b_steps
      let P_lm (lm : List (BitVec 8)) :=
        (FullMem c { sc with core := { sc.core with lit_mark := lm } } ⋆ R) m
      have hm_rk : P_lm (sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0)) :=
        (congrArg P_lm hlm_set_eq).mp hm
      exact ihc (kc + 1#32, ()) m (by dsimp only; omega)
        ⟨_, by rw [hkc1]; omega,
         fidFsBaseOk_with_lm hbc (lm' := sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0))
           (by simp [hbc.1.core_ok.lit_mark_len]),
         harc, htmpc, hincc, hscrc, hlmc', hm_rk⟩
    have hkc_eq : kc.toNat = msz.toNat := by have := bv32_ult_not_lt hc; omega
    clear hc Jc hkc_le ihc
    have hlm_done := fidFs_lm_clear_done (hkc_eq ▸ hlmc)
    obtain ⟨hdc, hcvc, halc, hflc, hrefsc, hreprc⟩ := fidFsBaseOk_to_dense hbc hlm_done
    have hp_ref_c : p.toNat ∈ fullArenaClauseRefs sc := hrefsc.symm ▸ hp_ref0
    have harc_p : p.toNat < sc.core.arena.length := by rw [harc]; exact hp_arr0
    have hhdr_c : sc.core.arena[p.toNat]'harc_p = hdr := list_eq_getElem_congr harc _ _
    have hpairs_c : FidPairsOk (fun _ cr => cr.toNat ∈ refs0) sc.scratch.scratch_buf ncand.toNat :=
      hscrc.symm ▸ hpairs
    have har_sc_sk : sc.core.arena = sk.core.arena := harc.trans hark.symm
    -- if (sat || taut)
    m6b_to_group
    refine wp_join_group (ts := [])
      (fun () mm => mm = mc ∧ (sat = true ∨ taut = true))
      (fun _ ⟨⟩ mm ⟨hmm, _⟩ => by
        have hmm' : (FullMem c sc ⋆ R) mm := hmm ▸ hmc
        m6b_steps
        have hd_mg := fid_fs_markGarb_dense' hdc hp_ref_c harc_p
          (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
        have hmg_refs := fid_fs_markGarb_refs hdc hp_ref_c harc_p
          (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
        rw [hhdr_c] at hd_mg hmg_refs
        exact ihp (ncand, np, ticks + 1#64, ()) m (by dsimp only; rw [hnp_n]; omega)
          ⟨_, hnc_le, by rw [hnp_n, ← halp]; exact hnp_bds.2,
           by rw [hnp_n]; exact hnp_mem, by rw [htk1_n]; omega,
           hd_mg, hcvc, halc, hflc, hmg_refs.trans hrefsc, hreprc, hpairs_c, hm⟩)
      ?_
    intro Jst hJst
    m6b_split
    · m6b_let; exact hJst () mc ⟨rfl, Or.inl hc⟩
    have hsat_f : sat = false := hc; clear hc
    m6b_split
    · m6b_let; exact hJst () mc ⟨rfl, Or.inr hc⟩
    have htaut_f : taut = false := hc; clear hc Jst hJst
    -- if (ovf)
    m6b_split
    · m6b_let
      exact ihp (ncand, np, ticks + 1#64, ()) mc (by dsimp only; rw [hnp_n]; omega)
        ⟨sc, hnc_le, by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem, by rw [htk1_n]; omega,
         hdc, hcvc, halc, hflc, hrefsc, hreprc, hpairs_c, hmc⟩
    have hovf_f : ovf = false := hc; clear hc
    -- if (msz == 0u)
    m6b_split
    · have hmsz0 : msz.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
      have hng_c : fullArenaClauseGarb sc p.toNat = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
        rw [List.getElem?_eq_getElem harc_p, Option.getD_some, hhdr_c]
        exact fid_garb_false_of_and hgarb0
      have hsz_c : fullArenaClauseSizeCore sc.core p.toNat = sz.toNat := by
        unfold fullArenaClauseSizeCore; rw [harc, ← hsz_eq]; rfl
      have hu_cur : (cnfOfClauses F_cur).Unsat :=
        fidFs_msz0_unsat hdc.1 hdc.2.1 hp_ref_c hng_c hsz_c fun α hα j hj hl => by
          obtain ⟨q, hq, _⟩ := hsem_ok hsat_f htaut_f hovf_f α hα j hj (har_sc_sk ▸ hl)
          omega
      clear hc; m6b_steps
      exact hQ 20#64 _ m (fid_denseInvW_with_inc hdc hu_cur 1#64) hcvc hflc (hcvc ▸ hreprc)
        (Or.inr rfl) (fun _ => hdc.2.1.ext_sound.2 hu_cur) hm
    have hmsz_ne0 : msz.toNat ≠ 0 := fun h => (beq_eq_false_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
    clear hc
    -- if (msz == 1u)
    m6b_split
    · have hmsz1 : msz.toNat = 1 := by rw [beq_iff_eq.mp hc]; rfl
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
      have hent_u : (cnfOfClauses F_cur).EntailsClause (cnfClause [(sc.core.tmp[0]'h0_tmp).toNat])
        :=
        fidFs_msz1_entails hdc.1 hdc.2.1 hp_ref_c hng_c hsz_c fun α hα j hj hl => by
          obtain ⟨q, hq, hqt⟩ := hsem_ok hsat_f htaut_f hovf_f α hα j hj (har_sc_sk ▸ hl)
          have hq0 : q = 0 := by omega
          subst hq0; rwa [← htmpc, List.getElem?_eq_getElem h0_tmp, Option.getD_some] at hqt
      clear hc; m6b_steps
      let sc_mg : FullState :=
        { sc with core :=
          { sc.core with
            arena := sc.core.arena.set p.toNat (hdr ||| 0x00080000#32)
            arena_garbage := sc.core.arena_garbage + 3#64 + sz.setWidth 64 } }
      have hd_mg : FullDenseInvW c F0 F_cur sc_mg := by
        simpa only [sc_mg, hhdr_c] using
          fid_fs_markGarb_dense' hdc hp_ref_c harc_p (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
      have hmg_refs : fullArenaClauseRefs sc_mg = refs0 := by
        have h := fid_fs_markGarb_refs hdc hp_ref_c harc_p
          (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
        rw [hhdr_c] at h; exact h.trans hrefsc
      m6b_call hAddUnit
      refine ⟨c, F0, F_cur, sc_mg, R, rfl, hd_mg.1, hd_mg.2.1,
        fun _ => by
          rw [list_getElem_congr (by decide : (BitVec.ofNat 64 0).toNat = 0) _ h0_tmp]
          exact hent_u,
        hm,
        fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass'
          unfl' inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss'
          mu hlu hwu hclu _h_unc h_f hmu => ?_⟩
      let su : FullState :=
        { sc_mg with
          core := { sc_mg.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
            unassigned := unass', unflushed := unfl', inconsistent := inc' }
          scratch := { sc_mg.scratch with
            phases := phases', target_assigned := ta', best_assigned := ba',
            phases_target := pt', phases_best := pb', heap := hp', pos := ps',
            heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
      have hdu := fid_addUnit_denseInvW hd_mg hlu hwu hclu rfl rfl rfl rfl rfl rfl rfl
      m6b_split
      · m6b_let
        exact ihp (ncand, np, ticks + 1#64, ()) mu (by dsimp only; rw [hnp_n]; omega)
          ⟨su, hnc_le, by rw [hnp_n, ← halp]; exact hnp_bds.2,
           by rw [hnp_n]; exact hnp_mem, by rw [htk1_n]; omega,
           hdu, hcvc, halc, hflc, hmg_refs, hreprc, hpairs_c, hmu⟩
      have hu_f := h_f hc
      have hu0_eq : (sc.core.tmp[(BitVec.ofNat 64 0).toNat]'(by
          rw [bv64_ofNat_toNat_lt (by decide)]; exact h0_tmp)).toNat =
          (sc.core.tmp[0]'h0_tmp).toNat :=
        congrArg BitVec.toNat (list_getElem_congr
          (by decide : (BitVec.ofNat 64 0).toNat = 0) _ h0_tmp)
      have hlt_su : (sc.core.tmp[(BitVec.ofNat 64 0).toNat]'(by
          rw [bv64_ofNat_toNat_lt (by decide)]; exact h0_tmp)).toNat < 2 * su.core.cur_vars := by
        rw [hu0_eq, show su.core.cur_vars = cv0 from hcvc]; exact hu0_lt
      have hu := (hu_f.resolve_left (Nat.not_le_of_lt hlt_su)).1
      m6b_steps
      exact hQ 20#64 su mu hdu hcvc hflc (hcvc ▸ hreprc) (Or.inr rfl) (fun _ => hu) hmu
    clear hc
    -- if (!c_mch) { p = np; continue; }
    m6b_split; rotate_left 1
    · m6b_let
      exact ihp (ncand, np, ticks + 1#64, ()) mc (by dsimp only; rw [hnp_n]; omega)
        ⟨sc, hnc_le, by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem, by rw [htk1_n]; omega,
         hdc, hcvc, halc, hflc, hrefsc, hreprc, hpairs_c, hmc⟩
    clear hc
    -- if (ncand < max_cand) { push (key, p) into scr }
    m6b_to_group
    refine wp_join_group (ts := [i64])
      (fun (nc', ()) mnc => ∃ snc : FullState,
        nc'.toNat ≤ c.scratch_cap / 4 ∧
        FullDenseInvW c F0 F_cur snc ∧ snc.core.cur_vars = cv0 ∧
        snc.core.arena_len = alen0 ∧ snc.core.fuel = fuel0 ∧
        fullArenaClauseRefs snc = refs0 ∧ FullCongReprInv F_cur (2 * cv0) snc.core.repr ∧
        FidPairsOk (fun _ cr => cr.toNat ∈ refs0) snc.scratch.scratch_buf nc'.toNat ∧
        (FullMem c snc ⋆ R) mnc)
      (fun _ ⟨nc', ⟨⟩⟩ mnc ⟨snc, hnc', hdnc, hcvnc, halnc, hflnc, hrefsnc, hreprnc, hpnc, hmnc⟩ =>
        by
          m6b_steps
          exact ihp (nc', np, ticks + 1#64, ()) mnc (by dsimp only; rw [hnp_n]; omega)
            ⟨snc, hnc', by rw [hnp_n]; omega, by rw [hnp_n]; exact hnp_mem,
             by rw [htk1_n]; omega, hdnc, hcvnc, halnc, hflnc, hrefsnc, hreprnc, hpnc, hmnc⟩)
      ?_
    intro Jnc hJnc
    m6b_split; rotate_left 1
    · m6b_let
      exact hJnc (ncand, ()) mc ⟨sc, hnc_le, hdc, hcvc, halc, hflc, hrefsc, hreprc, hpairs_c, hmc⟩
    have hnc_lt : ncand.toNat < c.scratch_cap / 4 := by
      have h := bv64_ult_lt hc
      change ncand.toNat < ((BitVec.ofNat 64 c.scratch_cap) >>> 2#64).toNat at h
      rwa [hmaxc_n] at h
    have hnc1_n : (ncand + 1#64).toNat = ncand.toNat + 1 := bv64_add1_lt (by omega)
    have hnc2_n : (ncand <<< 1#64).toNat = 2 * ncand.toNat := bv64_shl1_lt (by omega)
    have hnc21_n : ((ncand <<< 1#64) + 1#64).toNat = 2 * ncand.toNat + 1 :=
      bv64_shl1_add1_lt (by omega)
    have hsc_len : sc.scratch.scratch_buf.length = c.scratch_cap := hdc.1.scratch_ok.scratch_buf_len
    have hnc2_arr : (ncand <<< 1#64).toNat < sc.scratch.scratch_buf.length := by rw [hnc2_n]; omega
    have hnc21_arr : ((ncand <<< 1#64) + 1#64).toNat < sc.scratch.scratch_buf.length := by
      rw [hnc21_n]; omega
    clear hc; m6b_to_group
    refine wp_join_group (ts := [i32])
      (fun (_bit, ()) mb => mb = mc)
      (fun _ ⟨bit, ⟨⟩⟩ mb hmb => by
        subst mb; m6b_steps
        let scr_n :=
          (sc.scratch.scratch_buf.set (ncand <<< 1#64).toNat ((msz <<< 1#32) ||| bit)).set
            ((ncand <<< 1#64) + 1#64).toNat (p.setWidth 32)
        change (FullMem c { sc with scratch := { sc.scratch with scratch_buf := scr_n } } ⋆ R) m
          at hm
        dsimp only [scr_n] at hm
        rw [hnc2_n, hnc21_n] at hm
        have hscr_l' : ((sc.scratch.scratch_buf.set (2 * ncand.toNat)
            ((msz <<< 1#32) ||| bit)).set (2 * ncand.toNat + 1) (p.setWidth 32)).length =
            c.scratch_cap := by simp [hsc_len]
        have hpairs' := fidPairsOk_push hpairs_c (key := (msz <<< 1#32) ||| bit)
          (cr := p.setWidth 32) (by omega) (by rw [hp_32n]; exact hp_ref0)
        exact hJnc (ncand + 1#64, ()) m
          ⟨_, by rw [hnc1_n]; omega, fid_denseInvW_with_scr hdc hscr_l',
           hcvc, halc, hflc, hrefsc, hreprc, by rw [hnc1_n]; exact hpairs', hm⟩)
      (fun Jbit hJbit => by
        m6b_split
        · m6b_let; exact hJbit (1#32, ()) mc rfl
        m6b_let; exact hJbit (0#32, ()) mc rfl)
  -- Pass 1 exit continuation -> sort pairs -> init occ -> Pass 2!
  rintro _ ⟨⟩ me ⟨se, hnc_le, htk_le_e, hde, hcve, hale, hfle, hrefse, hrepre, hpairs_e, hme⟩
  clear Jp hp_le hp_mem htk_le hdp hcvp halp hflp hrefsp hreprp hpairs hmp ihp
  -- if (h->inconsistent != 0ULL) { return 20ULL; }
  m6b_split
  · m6b_steps
    exact hQ 20#64 se me hde hcve hfle (hcve ▸ hrepre) (Or.inr rfl)
      (fun _ => FullM3CongBva.unsat_of_inconsistent_w hde.2.1 (bne_iff_ne.mp hc)) hme
  clear hc
  -- if (ncand <= 1ULL || ticks >= tick_lim) { return 1ULL; }
  m6b_split
  · m6b_steps
    exact hQ 1#64 se me hde hcve hfle (hcve ▸ hrepre) (Or.inl rfl) (fun h => by cases h) hme
  have hnc_gt1 : 1 < ncand.toNat := bv64_ule_not_le hc
  clear hc; m6b_split
  · m6b_steps
    exact hQ 1#64 se me hde hcve hfle (hcve ▸ hrepre) (Or.inl rfl) (fun h => by cases h) hme
  have htk_lt_e : ticks.toNat < tl.toNat := bv64_ule_not_le hc
  clear hc
  -- full_cong_sort_pairs_fid(scr, ncand)
  have hfs_e := focus_full_scratch_buf hme; clear hme
  have hscrl_e := hde.1.scratch_ok.scratch_buf_len
  m6b_let
  refine LeanQbe.T.wp_call_of_spec _ _ (hSortPairs _ _ _ _ ?_)
  dsimp only [LeanQbe.T.vals_nil, LeanQbe.T.vals_cons,
    LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
  refine ⟨fun _ cr => cr.toNat ∈ refs0, se.scratch.scratch_buf, FullScrBufRest c se ⋆ R,
    by omega, by omega, hpairs_e, hfs_e, fun scr_s m_s hscrl_s hpairs_s _ hm_s => ?_⟩
  let s_s : FullState := { se with scratch := { se.scratch with scratch_buf := scr_s } }
  have hm_s' : (FullMem c s_s ⋆ R) m_s := unfocus_full_scratch_buf hm_s
  have hd_s : FullDenseInvW c F0 F_cur s_s := fid_denseInvW_with_scr hde (hscrl_s.trans hscrl_e)
  -- Init occ_head[0 ..< nlits) = 0xFFFFFFFF, occ_cnt[0 ..< nlits) = 0
  have hnlits_n : ((BitVec.ofNat 64 cv0) <<< 1#64).toNat = 2 * cv0 := by
    rw [bv64_shl1_lt (by rw [bv64_ofNat_toNat_lt (by omega)]; omega),
      bv64_ofNat_toNat_lt (by omega)]
  m6b_to_group
  refine wp_loop_inv (ts := [i64])
    (fun (io, ()) mio => ∃ sio : FullState,
      io.toNat ≤ 2 * cv0 ∧ FullDenseInvW c F0 F_cur sio ∧
      sio.core = s_s.core ∧ sio.scratch.scratch_buf = scr_s ∧
      (∀ l < io.toNat, sio.scratch.work_stk1[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
      (FullMem c sio ⋆ R) mio)
    (fun (io, ()) _ => 2 * cv0 - io.toNat)
    (fun Jo hJo => by
      m6b_steps
      exact hJo (0#64, ()) m_s
        ⟨s_s, Nat.zero_le _, hd_s, rfl, rfl, (fun _ h => absurd h (Nat.not_lt_zero _)), hm_s'⟩)
    (fun Jo (io, ()) mio ⟨sio, hio_le, hdio, hcor_io, hscr_io, hhead_io, hmio⟩ iho => ?_)
  m6b_split
  · have hio_lt : io.toNat < 2 * cv0 := by
      have h := bv64_ult_lt hc
      change io.toNat < ((BitVec.ofNat 64 cv0) <<< 1#64).toNat at h; rwa [hnlits_n] at h
    have hio1_n : (io + 1#64).toNat = io.toNat + 1 := bv64_add1_lt (by omega)
    have hio_w1 : io.toNat < sio.scratch.work_stk1.length := by
      have := hdio.1.scratch_ok.work_stk1_len; omega
    have hio_w2 : io.toNat < sio.scratch.work_stk2.length := by
      have := hdio.1.scratch_ok.work_stk2_len; omega
    clear hc; m6b_steps
    let sio' : FullState :=
      { sio with scratch :=
        { sio.scratch with
          work_stk1 := sio.scratch.work_stk1.set io.toNat 0xFFFFFFFF#32
          work_stk2 := sio.scratch.work_stk2.set io.toNat 0#32 } }
    change (FullMem c sio' ⋆ R) m at hm
    have hhead' : ∀ l < (io + 1#64).toNat,
        sio'.scratch.work_stk1[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
      rw [hio1_n]; intro l hl; dsimp only [sio']
      by_cases hli : l = io.toNat
      · subst hli; rw [List.getElem?_set_self hio_w1, Option.getD_some]
      · rw [List.getElem?_set_ne (Ne.symm hli)]; exact hhead_io l (by omega)
    exact iho (io + 1#64, ()) m (by dsimp only; omega)
      ⟨sio', by rw [hio1_n]; omega,
       fid_denseInvW_with_ws12 hdio
         (w1' := sio.scratch.work_stk1.set io.toNat 0xFFFFFFFF#32)
         (w2' := sio.scratch.work_stk2.set io.toNat 0#32)
         (by rw [List.length_set]; exact hdio.1.scratch_ok.work_stk1_len)
         (by rw [List.length_set]; exact hdio.1.scratch_ok.work_stk2_len),
       hcor_io, hscr_io, hhead', hm⟩
  have hio_eq : io.toNat = 2 * cv0 := by
    have h := bv64_ult_not_lt hc
    change ¬ io.toNat < ((BitVec.ofNat 64 cv0) <<< 1#64).toNat at h; rw [hnlits_n] at h; omega
  clear hc Jo hio_le iho
  have hocc_init : FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) (2 * ncand.toNat)
      sio.scratch.work_stk1 sio.scratch.scratch_buf :=
    fidFsOccOk_init (by rw [hdio.1.scratch_ok.scratch_buf_len]; omega) (hio_eq ▸ hhead_io)
  have hnc2_init : (ncand <<< 1#64).toNat = 2 * ncand.toNat := bv64_shl1_lt (by omega)
  -- Pass 2: sorted forward subsumption loop
  m6b_to_group
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (tk2, occ_pos, ci, ()) m2 => ∃ s2 : FullState,
      ci.toNat ≤ ncand.toNat ∧ tk2.toNat ≤ tl.toNat ∧ occ_pos.toNat ≤ c.scratch_cap ∧
      FullDenseInvW c F0 F_cur s2 ∧ s2.core.cur_vars = cv0 ∧
      s2.core.arena_len = alen0 ∧ s2.core.fuel = fuel0 ∧
      fullArenaClauseRefs s2 = refs0 ∧ FullCongReprInv F_cur (2 * cv0) s2.core.repr ∧
      FidPairsOk (fun _ cr => cr.toNat ∈ refs0) s2.scratch.scratch_buf ncand.toNat ∧
      FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) occ_pos.toNat
        s2.scratch.work_stk1 s2.scratch.scratch_buf ∧
      (FullMem c s2 ⋆ R) m2)
    (fun (_, _, ci, ()) _ => ncand.toNat - ci.toNat)
    (fun Jc2 hJc2 => by
      m6b_steps
      exact hJc2 (ticks, ncand <<< 1#64, 0#64, ()) mio
        ⟨sio, Nat.zero_le _, htk_le_e, by rw [hnc2_init]; omega, hdio,
         hcor_io.symm ▸ hcve, hcor_io.symm ▸ hale, hcor_io.symm ▸ hfle,
         (by change fullArenaClauseRefsCore sio.core = refs0; rw [hcor_io]; exact hrefse),
         hcor_io.symm ▸ hrepre, hscr_io.symm ▸ hpairs_s,
         by rw [hnc2_init]; exact hocc_init, hmio⟩)
    (fun Jc2 (tk2, occ_pos, ci, ()) m2
        ⟨s2, hci_le, htk2_le, hoccp_le, hd2, hcv2, hal2, hfl2, hrefs2, hrepr2,
         hpairs2, hocc2, hm2⟩ ihc2 => ?_)
  clear hdio hcor_io hscr_io hhead_io hmio hocc_init hd_s hm_s' hde hcve hale hfle hrefse hrepre
    hpairs_e hpairs_s hscrl_e hscrl_s
  m6b_to_group
  refine wp_join_group (ts := [])
    (fun () mf => ∃ sf : FullState,
      FullDenseInvW c F0 F_cur sf ∧ sf.core.cur_vars = cv0 ∧ sf.core.fuel = fuel0 ∧
      FullCongReprInv F_cur (2 * cv0) sf.core.repr ∧ (FullMem c sf ⋆ R) mf)
    (fun _ ⟨⟩ mf ⟨sf, hdf, hcvf, hflf, hreprf, hmf⟩ => by
      m6b_to_group
      refine wp_join_group (ts := [i64])
        (fun (r, ()) mr => mr = mf ∧ (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
        (fun _ ⟨r, ⟨⟩⟩ mr ⟨hmr, hr_dom, huns⟩ => by
          m6b_steps; exact hQ r sf mr hdf hcvf hflf (hcvf ▸ hreprf) hr_dom huns (hmr ▸ hmf))
        (fun Jrf hJrf => by
          m6b_split
          · m6b_let
            exact hJrf (20#64, ()) mf ⟨rfl, Or.inr rfl, fun _ =>
              FullM3CongBva.unsat_of_inconsistent_w hdf.2.1 (bne_iff_ne.mp hc)⟩
          m6b_let; exact hJrf (1#64, ()) mf ⟨rfl, Or.inl rfl, fun h => by cases h⟩))
    ?_
  intro Jexit2 hJexit2
  have hpass2_exit : Jexit2 () m2 := hJexit2 () m2 ⟨s2, hd2, hcv2, hfl2, hrepr2, hm2⟩
  m6b_split; rotate_left 1
  · clear hc; m6b_let; exact hpass2_exit
  have hci_lt : ci.toNat < ncand.toNat := bv64_ult_lt hc
  have hci1_n : (ci + 1#64).toNat = ci.toNat + 1 := bv64_add1_lt (by omega)
  clear hc; m6b_split; rotate_left 1
  · clear hc; m6b_let; exact hpass2_exit
  have htk2_lt : tk2.toNat < tl.toNat := bv64_ult_lt hc
  have htk21_n : (tk2 + 1#64).toNat = tk2.toNat + 1 := bv64_add1_lt (by omega)
  clear hc; m6b_split; rotate_left 1
  · clear hc; m6b_let; exact hpass2_exit
  have hinc2 : s2.core.inconsistent = 0#64 := by simpa using hc
  clear hc Jexit2 hJexit2 hpass2_exit
  have hci21_n : ((ci <<< 1#64) + 1#64).toNat = 2 * ci.toNat + 1 := bv64_shl1_add1_lt (by omega)
  have hscr_len2 := hd2.1.scratch_ok.scratch_buf_len
  have hci21_arr : ((ci <<< 1#64) + 1#64).toNat < s2.scratch.scratch_buf.length := by
    rw [hci21_n]; omega
  let cref := s2.scratch.scratch_buf[((ci <<< 1#64) + 1#64).toNat]'hci21_arr
  have hcref_ref0 : cref.toNat ∈ refs0 := by
    have h := hpairs2 ci.toNat hci_lt
    dsimp only at h
    have h21_lt : 2 * ci.toNat + 1 < s2.scratch.scratch_buf.length := by
      rw [← hci21_n]; exact hci21_arr
    rw [List.getElem?_eq_getElem h21_lt, Option.getD_some] at h
    dsimp only [cref]; rwa [list_getElem_congr hci21_n hci21_arr h21_lt]
  have hcref_ref : cref.toNat ∈ fullArenaClauseRefs s2 := hrefs2.symm ▸ hcref_ref0
  obtain ⟨hb_2, hlm_2⟩ := fidFsBaseOk_of_dense hd2 hcv2 hal2 hfl2 hrefs2 hrepr2
  obtain ⟨hcr_arr0, hcr_arr2, hcr2_n, hcr_bd0⟩ := fidFs_cr_ar hb_2 hcref_ref0
  have hcr_z : (cref.setWidth 64).toNat = cref.toNat := bv_zext32_toNat cref
  have hcr_arr0_z : (cref.setWidth 64).toNat < s2.core.arena.length := by rw [hcr_z]; exact hcr_arr0
  let chdr := s2.core.arena[(cref.setWidth 64).toNat]'hcr_arr0_z
  let csz := s2.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr_arr2
  have hchdr_eq : chdr = s2.core.arena[cref.toNat]'hcr_arr0 := list_getElem_congr hcr_z _ _
  have hcsz_eq : fullArenaClauseSizeCore s2.core cref.toNat = csz.toNat := by
    unfold fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hcr2_n.symm _ _)
  m6b_to_group
  refine wp_join_group (ts := []) (fun () msk => msk = m2)
    (fun _ ⟨⟩ msk hmsk => by
      m6b_steps
      exact ihc2 (tk2 + 1#64, occ_pos, ci + 1#64, ()) msk (by dsimp only; rw [hci1_n]; omega)
        ⟨s2, by rw [hci1_n]; omega, by rw [htk21_n]; omega, hoccp_le,
         hd2, hcv2, hal2, hfl2, hrefs2, hrepr2, hpairs2, hocc2, hmsk ▸ hm2⟩)
    ?_
  intro Jskip2 hJskip2
  m6b_split
  · clear hc; m6b_let; exact hJskip2 () m2 rfl
  have hcgarb0 : (chdr &&& 0x00080000#32) = 0#32 := by simpa [chdr, cref] using hc
  clear hc; m6b_split
  · clear hc; m6b_let; exact hJskip2 () m2 rfl
  clear Jskip2 hJskip2
  have hcsz3 : 3 ≤ csz.toNat := by
    have h := bv32_ult_not_lt hc
    rw [show (3 : BitVec 32).toNat = 3 from rfl] at h; change ¬ csz.toNat < 3 at h; omega
  have hng_c2 : fullArenaClauseGarb s2 cref.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_arr0, Option.getD_some, ← hchdr_eq]
    exact fid_garb_false_of_and hcgarb0
  have hcsz_cv : csz.toNat ≤ cv0 := by
    rw [← hcv2, ← hcsz_eq]
    exact fullArenaClauseSize_le_cur_vars hd2.1 hd2.2.1 hd2.2.2.2.1 hcref_ref hng_c2
  have hcr_bd : cref.toNat + 3 + csz.toNat ≤ alen0 := by rw [← hcsz_eq]; exact hcr_bd0
  have hlen_s2 : alen0 ≤ s2.core.arena.length := by
    rw [hd2.1.core_ok.arena_len_arr, ← hal2]; exact hd2.1.core_ok.arena_len_le
  clear hc; m6b_to_group
  -- Pass 2 clause reduction loop (k < csz)
  refine wp_join_group (ts := [.bool, .bool, .bool, i32, i32])
    (fun (sat, taut, ovf, msz, _k, ()) mk => ∃ sk : FullState,
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk ∧
      sk.core.arena = s2.core.arena ∧ sk.core.vals = s2.core.vals ∧
      sk.core.inconsistent = 0#64 ∧ sk.scratch = s2.scratch ∧ msz.toNat ≤ cv0 ∧
      (∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (sat = false → taut = false → ovf = false →
        ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
          ∀ j < csz.toNat,
            evalLitVal α (sk.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat = true →
            ∃ q < msz.toNat, evalLitVal α (sk.core.tmp[q]?.getD 0#32).toNat = true) ∧
      (FullMem c sk ⋆ R) mk)
    ?_ ?_
  rotate_left 1
  · intro Jk2_ex hJk2_ex
    exact fidFs_reduce_k_wp Γ hFind rfl rfl rfl rfl rfl rfl hb_2 hinc2 hlm_2 hcref_ref0 hng_c2
      hcsz_eq hcr_bd hm2 fun sat taut ovf msz k_r mk h =>
        hJk2_ex (sat, taut, ovf, msz, k_r, ()) mk h
  -- Pass 2 post-reduction branches
  rintro _ ⟨sat, taut, ovf, msz, _k, ⟨⟩⟩ mk
    ⟨sk, hbk, hark, hvlk, hinck, hscrk, hmsz_cv, htmp_lt, hlm_ok, hsem_ok, hmk⟩
  -- if (sat || taut) { clear lm; mark garb; continue; }
  m6b_to_group
  refine wp_join_group (ts := [])
    (fun () mm => mm = mk ∧ (sat = true ∨ taut = true))
    (fun _ ⟨⟩ mm ⟨hmm, _⟩ => by
      have hmm' : (FullMem c sk ⋆ R) mm := hmm ▸ hmk
      refine fidFs_clearLm_wp Γ hmm' hbk hark rfl hscrk hmsz_cv htmp_lt
        (fidFs_lm_clear_from_zero hlm_ok)
        fun _kc sc m _hbc harc _htmpc hscrc hdc hcvc halc hflc hrefsc hreprc hm => ?_
      have hcr_c : cref.toNat < sc.core.arena.length := by rw [harc]; exact hcr_arr0
      have hchdr_c : sc.core.arena[cref.toNat]'hcr_c = chdr := by
        rw [hchdr_eq]; exact list_eq_getElem_congr harc _ _
      m6b_steps
      let P_mg (ar' : List (BitVec 32)) (ag' : BitVec 64) :=
        (FullMem c { sc with core := { sc.core with arena := ar', arena_garbage := ag' } } ⋆ R) m
      have hm' : P_mg (sc.core.arena.set cref.toNat (chdr ||| 0x00080000#32))
          (sc.core.arena_garbage + 3#64 + csz.setWidth 64) := by
        have heq1 : sc.core.arena.set (cref.setWidth 64).toNat (chdr ||| 0x00080000#32) =
            sc.core.arena.set cref.toNat (chdr ||| 0x00080000#32) := by rw [hcr_z]
        exact heq1 ▸ hm
      have hd_mg := fid_fs_markGarb_dense' hdc (hrefsc.symm ▸ hcref_ref0) hcr_c
        (sc.core.arena_garbage + 3#64 + csz.setWidth 64)
      have hmg_refs := fid_fs_markGarb_refs hdc (hrefsc.symm ▸ hcref_ref0) hcr_c
        (sc.core.arena_garbage + 3#64 + csz.setWidth 64)
      rw [hchdr_c] at hd_mg hmg_refs
      exact ihc2 (tk2 + 1#64, occ_pos, ci + 1#64, ()) m (by dsimp only; rw [hci1_n]; omega)
        ⟨_, by rw [hci1_n]; omega, by rw [htk21_n]; omega, hoccp_le,
         hd_mg, hcvc, halc, hflc, hmg_refs.trans hrefsc, hreprc,
         hscrc.symm ▸ hpairs2, hscrc.symm ▸ hocc2, hm'⟩)
    ?_
  intro Jst2 hJst2
  m6b_split
  · m6b_let; exact hJst2 () mk ⟨rfl, Or.inl hc⟩
  have hsat_f : sat = false := hc; clear hc
  m6b_split
  · m6b_let; exact hJst2 () mk ⟨rfl, Or.inr hc⟩
  have htaut_f : taut = false := hc; clear hc Jst2 hJst2
  -- if (ovf) { clear lm; continue; }
  m6b_split
  · clear hc
    refine fidFs_clearLm_wp Γ hmk hbk hark rfl hscrk hmsz_cv htmp_lt
      (fidFs_lm_clear_from_zero hlm_ok)
      fun _kc sc mc _hbc _harc _htmpc hscrc hdc hcvc halc hflc hrefsc hreprc hmc => ?_
    m6b_let
    exact ihc2 (tk2 + 1#64, occ_pos, ci + 1#64, ()) mc (by dsimp only; rw [hci1_n]; omega)
      ⟨sc, by rw [hci1_n]; omega, by rw [htk21_n]; omega, hoccp_le,
       hdc, hcvc, halc, hflc, hrefsc, hreprc, hscrc.symm ▸ hpairs2, hscrc.symm ▸ hocc2, hmc⟩
  have hovf_f : ovf = false := hc; clear hc
  -- if (msz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
  m6b_split
  · have hmsz0 : msz.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
    have hlm0 : ∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 := fun l hl =>
      (hlm_ok l hl).elim id fun ⟨j, hj, _⟩ => by omega
    obtain ⟨hdk, hcvk, halk, hflk, hrefsk, hreprk⟩ := fidFsBaseOk_to_dense hbk hlm0
    have hcr_k : cref.toNat < sk.core.arena.length := by rw [hark]; exact hcr_arr0
    have hng_k : fullArenaClauseGarb sk cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem hcr_k, Option.getD_some,
        list_eq_getElem_congr hark hcr_k hcr_arr0, ← hchdr_eq]
      exact fid_garb_false_of_and hcgarb0
    have hsz_k : fullArenaClauseSizeCore sk.core cref.toNat = csz.toNat := by
      unfold fullArenaClauseSizeCore; rw [hark, ← hcsz_eq]; rfl
    have hu_cur : (cnfOfClauses F_cur).Unsat :=
      fidFs_msz0_unsat hdk.1 hdk.2.1 (hrefsk.symm ▸ hcref_ref0) hng_k hsz_k fun α hα j hj hl => by
        obtain ⟨q, hq, _⟩ := hsem_ok hsat_f htaut_f hovf_f α hα j hj hl
        omega
    clear hc; m6b_steps
    exact hQ 20#64 _ m (fid_denseInvW_with_inc hdk hu_cur 1#64) hcvk hflk (hcvk ▸ hreprk)
      (Or.inr rfl) (fun _ => hdk.2.1.ext_sound.2 hu_cur) hm
  have hmsz_ne0 : msz.toNat ≠ 0 := fun h => (beq_eq_false_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
  clear hc
  -- if (msz == 1u) { lm[tmp[0]] = 0; mark garb; full_add_unit(h, tmp[0]); continue; }
  m6b_split
  · have hmsz1 : msz.toNat = 1 := by rw [beq_iff_eq.mp hc]; rfl
    have h0_tmp : 0 < sk.core.tmp.length := by have := hbk.1.core_ok.tmp_len_arr; omega
    let u0 := sk.core.tmp[0]'h0_tmp
    have hu0_lt : u0.toNat < 2 * cv0 := by
      have h := htmp_lt 0 (by omega)
      rwa [List.getElem?_eq_getElem h0_tmp, Option.getD_some] at h
    have hu0_lm : u0.toNat < sk.core.lit_mark.length := fidFs_base_lm_lt hbk hu0_lt
    have hu0_z : (u0.setWidth 64).toNat = u0.toNat := bv_zext32_toNat u0
    have hcr_k : cref.toNat < sk.core.arena.length := by rw [hark]; exact hcr_arr0
    have hchdr_k : sk.core.arena[cref.toNat]'hcr_k = chdr := by
      rw [hchdr_eq]; exact list_eq_getElem_congr hark _ _
    have hlm1 : ∀ l < 2 * c.max_vars,
        (sk.core.lit_mark.set u0.toNat (BitVec.ofNat 8 0))[l]?.getD 0#8 = 0#8 :=
      fidFs_lm_clear_done (msz := 1) (tmp := sk.core.tmp)
        (fidFs_lm_clear_step (k := 0) (by omega) h0_tmp hu0_lm
          (fidFs_lm_clear_from_zero (hmsz1 ▸ hlm_ok)))
    let sk_cl : FullState :=
      { sk with core := { sk.core with lit_mark := sk.core.lit_mark.set u0.toNat 0#8 } }
    have hbk_cl := fidFsBaseOk_with_lm hbk (lm' := sk.core.lit_mark.set u0.toNat 0#8)
      (by simp [hbk.1.core_ok.lit_mark_len])
    obtain ⟨hd_cl, hcv_cl, hal_cl, hfl_cl, hrefs_cl, hrepr_cl⟩ := fidFsBaseOk_to_dense hbk_cl hlm1
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
          have hq0 : q = 0 := by omega
          subst hq0; rwa [List.getElem?_eq_getElem h0_tmp, Option.getD_some] at hqt
    have h0_bv_tmp : (BitVec.ofNat 64 0).toNat < sk.core.tmp.length := by
      rw [bv64_ofNat_toNat_lt (by decide)]; exact h0_tmp
    have hu0_bv_eq : sk.core.tmp[(BitVec.ofNat 64 0).toNat]'h0_bv_tmp = u0 :=
      list_getElem_congr (by decide) _ _
    clear hc; m6b_steps
    have hlm_set_u0 : sk.core.lit_mark.set
        ((sk.core.tmp[(BitVec.ofNat 64 0).toNat]'h0_bv_tmp).setWidth 64).toNat
        (BitVec.ofNat 8 0) = sk.core.lit_mark.set u0.toNat 0#8 := by
      rw [hu0_bv_eq, hu0_z]
    have hcr_z_d : (BitVec.setWidth 64
        s2.scratch.scratch_buf[(ci <<< OfNat.ofNat 1 + 1).toNat]).toNat = cref.toNat := hcr_z
    have hchdr_d : s2.core.arena[(BitVec.setWidth 64
        s2.scratch.scratch_buf[(ci <<< OfNat.ofNat 1 + 1).toNat]).toNat] = chdr := rfl
    have hcsz_d : s2.core.arena[(BitVec.setWidth 64
        s2.scratch.scratch_buf[(ci <<< OfNat.ofNat 1 + 1).toNat] + 2).toNat] = csz := rfl
    let sc_mg : FullState :=
      { sk_cl with core :=
        { sk_cl.core with
          arena := sk_cl.core.arena.set cref.toNat (chdr ||| 0x00080000#32)
          arena_garbage := sk_cl.core.arena_garbage + 3#64 + csz.setWidth 64 } }
    have hm_mg : (FullMem c sc_mg ⋆ R) m := by
      dsimp only [sc_mg, sk_cl]
      rw [hlm_set_u0, hchdr_d, hcsz_d, hcr_z_d,
        show (524288 : BitVec 32) = 0x00080000#32 from rfl,
        show (3 : BitVec 64) = 3#64 from rfl] at hm
      exact hm
    have hd_mg : FullDenseInvW c F0 F_cur sc_mg := by
      simpa only [sc_mg, hchdr_k] using fid_fs_markGarb_dense' hd_cl
        (hrefs_cl.symm ▸ hcref_ref0) hcr_k (sk_cl.core.arena_garbage + 3#64 + csz.setWidth 64)
    have hmg_refs : fullArenaClauseRefs sc_mg = refs0 := by
      have h := fid_fs_markGarb_refs hd_cl (hrefs_cl.symm ▸ hcref_ref0) hcr_k
        (sk_cl.core.arena_garbage + 3#64 + csz.setWidth 64)
      rw [hchdr_k] at h; exact h.trans hrefs_cl
    m6b_call hAddUnit
    refine ⟨c, F0, F_cur, sc_mg, R, rfl, hd_mg.1, hd_mg.2.1,
      fun _ => by rw [hu0_bv_eq]; exact hent_u, hm_mg,
      fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass'
        unfl' inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss'
        mu hlu hwu hclu _h_unc h_f hmu => ?_⟩
    let su : FullState :=
      { sc_mg with
        core := { sc_mg.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
          unassigned := unass', unflushed := unfl', inconsistent := inc' }
        scratch := { sc_mg.scratch with
          phases := phases', target_assigned := ta', best_assigned := ba',
          phases_target := pt', phases_best := pb', heap := hp', pos := ps',
          heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
    have hdu := fid_addUnit_denseInvW hd_mg hlu hwu hclu rfl rfl rfl rfl rfl rfl rfl
    m6b_split
    · m6b_let
      exact ihc2 (tk2 + 1#64, occ_pos, ci + 1#64, ()) mu (by dsimp only; rw [hci1_n]; omega)
        ⟨su, by rw [hci1_n]; omega, by rw [htk21_n]; omega, hoccp_le,
         hdu, hcv_cl, hal_cl, hfl_cl, hmg_refs, hrepr_cl,
         by change FidPairsOk _ sk.scratch.scratch_buf _; rw [hscrk]; exact hpairs2,
         by change FidFsOccOk _ _ _ _ sk.scratch.work_stk1 sk.scratch.scratch_buf; rw [hscrk]
            exact hocc2,
         hmu⟩
    have hu_f := h_f hc
    have hlt_su : (sk.core.tmp[(BitVec.ofNat 64 0).toNat]'h0_bv_tmp).toNat < 2 * su.core.cur_vars :=
      by rw [hu0_bv_eq, show su.core.cur_vars = cv0 from hcv_cl]; exact hu0_lt
    have hu := (hu_f.resolve_left (Nat.not_le_of_lt hlt_su)).1
    m6b_steps
    exact hQ 20#64 su mu hdu hcv_cl hfl_cl (hcv_cl ▸ hrepr_cl) (Or.inr rfl) (fun _ => hu) hmu
  have hmsz_ne1 : msz.toNat ≠ 1 := fun h => (beq_eq_false_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
  have hmsz_ge2 : 2 ≤ msz.toNat := by omega
  clear hc
  -- Subsumption search over occ_head[tmp[k]] for k < msz
  have h0_tmp : 0 < sk.core.tmp.length := by have := hbk.1.core_ok.tmp_len_arr; omega
  have h0_bv_tmp : (BitVec.ofNat 64 0).toNat < sk.core.tmp.length := by
    rw [bv64_ofNat_toNat_lt (by decide)]; exact h0_tmp
  let lr0 := sk.core.tmp[(BitVec.ofNat 64 0).toNat]'h0_bv_tmp
  have hlr0_lt : lr0.toNat < 2 * cv0 := by
    have h := htmp_lt 0 (by omega)
    dsimp only [lr0]
    rwa [List.getElem?_eq_getElem h0_tmp, Option.getD_some,
      ← list_getElem_congr (by decide : (BitVec.ofNat 64 0).toNat = 0) h0_bv_tmp h0_tmp] at h
  have hlr0_w2 : (lr0.setWidth 64).toNat < sk.scratch.work_stk2.length := by
    rw [bv_zext32_toNat, hbk.1.scratch_ok.work_stk2_len]; omega
  m6b_steps
  refine wp_loop_inv (ts := [i64, i32, i32, i32, .bool])
    (fun (tk_k, ki, lr, _lcnt, sub_k, ()) mk_s => ∃ sk_s : FullState,
      ki.toNat ≤ msz.toNat ∧ tk_k.toNat ≤ tl.toNat ∧ lr.toNat < 2 * cv0 ∧
      FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sk_s ∧
      (FullMem c sk_s ⋆ R) mk_s)
    (fun (_, ki, _, _, _, ()) _ => msz.toNat - ki.toNat)
    (fun Jsub hJsub => by
      m6b_let
      exact hJsub (tk2 + 1#64, 0#32, lr0, sk.scratch.work_stk2[(lr0.setWidth 64).toNat]'hlr0_w2,
        false, ()) mk
        ⟨sk, Nat.zero_le _, by rw [htk21_n]; omega, hlr0_lt,
         ⟨hbk, hark, hvlk, rfl, rfl, hinck, hscrk, hlm_ok⟩, hmk⟩)
    (fun Jsub (tk_k, ki, lr, lcnt, sub_k, ()) mk_s
        ⟨sk_s, hki_le, htkk_le, hlr_lt, hscan, hmks⟩ ihsub => ?_)
  m6b_to_group
  refine wp_join_group (ts := [])
    (fun () m_cl => ∃ s_cl : FullState,
      FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat s_cl ∧
      (FullMem c s_cl ⋆ R) m_cl)
    ?_ ?_
  rotate_left 1
  -- Subsumption outer k loop body
  · intro Jsub_ex hJsub_ex
    have hsub_exit : Jsub_ex () mk_s := hJsub_ex () mk_s ⟨sk_s, hscan, hmks⟩
    m6b_split; rotate_left 1
    · clear hc; m6b_let; exact hsub_exit
    have hki_lt : ki.toNat < msz.toNat := bv32_ult_lt hc
    have hki1 : (ki + 1#32).toNat = ki.toNat + 1 := bv32_add1_lt_of (by omega)
    clear hc; m6b_split
    · clear hc; m6b_let; exact hsub_exit
    clear hc; m6b_split; rotate_left 1
    · clear hc; m6b_let; exact hsub_exit
    clear hc Jsub_ex hJsub_ex hsub_exit
    have hki_tmp : ki.toNat < sk_s.core.tmp.length := by
      have := hscan.1.1.core_ok.tmp_len_arr; omega
    have hki_z : (ki.setWidth 64).toNat = ki.toNat := bv_zext32_toNat ki
    have hki_tmp_z : (ki.setWidth 64).toNat < sk_s.core.tmp.length := by rw [hki_z]; exact hki_tmp
    let rk := sk_s.core.tmp[(ki.setWidth 64).toNat]'hki_tmp_z
    have hrk_lt : rk.toNat < 2 * cv0 := by
      have h := htmp_lt ki.toNat hki_lt
      dsimp only [rk]
      rwa [← hscan.2.2.2.1, List.getElem?_eq_getElem hki_tmp, Option.getD_some,
        ← list_getElem_congr hki_z hki_tmp_z hki_tmp] at h
    have hrk_z : (rk.setWidth 64).toNat = rk.toNat := bv_zext32_toNat rk
    have hrk_w1 : (rk.setWidth 64).toNat < sk_s.scratch.work_stk1.length := by
      rw [hrk_z, hscan.1.1.scratch_ok.work_stk1_len]; omega
    have hrk_w2 : (rk.setWidth 64).toNat < sk_s.scratch.work_stk2.length := by
      rw [hrk_z, hscan.1.1.scratch_ok.work_stk2_len]; omega
    m6b_to_group
    refine wp_join_group (ts := [i32, i32])
      (fun (lr', _lcnt', ()) mlr => mlr = mk_s ∧ lr'.toNat < 2 * cv0)
      ?_
      (fun Jlr hJlr => by
        m6b_split
        · m6b_let; exact hJlr (rk, sk_s.scratch.work_stk2[(rk.setWidth 64).toNat]'hrk_w2, ())
            mk_s ⟨rfl, hrk_lt⟩
        m6b_let; exact hJlr (lr, lcnt, ()) mk_s ⟨rfl, hlr_lt⟩)
    rintro _ ⟨lr', lcnt', ⟨⟩⟩ mlr ⟨hmlr, hlr'_lt⟩; subst mlr
    let nd0 := sk_s.scratch.work_stk1[(rk.setWidth 64).toNat]'hrk_w1
    have hnd0_ok : FidFsOccPtrOk (2 * ncand.toNat) occ_pos.toNat nd0 := by
      have h := hocc2.2.2.2.1 rk.toNat hrk_lt
      dsimp only [nd0]; rw [← hscan.2.2.2.2.2.2.1] at h
      rwa [List.getElem?_eq_getElem (by rw [← hrk_z]; exact hrk_w1), Option.getD_some,
        ← list_getElem_congr hrk_z hrk_w1 _] at h
    m6b_to_group
    refine wp_join_group (ts := [i64, .bool, i32])
      (fun (tk_n', sub_n', _nd', ()) mnd_e => ∃ s_ne : FullState,
        tk_n'.toNat ≤ tl.toNat ∧
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat s_ne ∧
        (FullMem c s_ne ⋆ R) mnd_e)
      (fun _ ⟨tk_n', sub_n', _, ⟨⟩⟩ mnd_e ⟨s_ne, htkn', hsc_ne, hm_ne⟩ => by
        m6b_steps
        exact ihsub (tk_n', ki + 1#32, lr', lcnt', sub_n', ()) mnd_e (by
          dsimp only; rw [hki1]; omega)
          ⟨s_ne, by rw [hki1]; omega, htkn', hlr'_lt, hsc_ne, hm_ne⟩)
      ?_
    intro Jnd_ex hJnd_ex
    refine wp_loop_inv (ts := [i64, i32])
      (fun (tk_n, nd, ()) mnd => ∃ s_nd : FullState,
        tk_n.toNat ≤ tl.toNat ∧
        FidFsOccPtrOk (2 * ncand.toNat) occ_pos.toNat nd ∧
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat s_nd ∧
        (FullMem c s_nd ⋆ R) mnd)
      (fun (tk_n, _, ()) _ => tl.toNat - tk_n.toNat)
      (fun Jnd hJnd => by
        m6b_let; exact hJnd (tk_k, nd0, ()) mk_s ⟨sk_s, htkk_le, hnd0_ok, hscan, hmks⟩)
      (fun Jnd (tk_n, nd, ()) mnd ⟨s_nd, htkn_le, hnd_ok, hsc_nd, hm_nd⟩ ihnd => ?_)
    m6b_split; rotate_left 1
    · clear hc; m6b_let; exact hJnd_ex (tk_n, sub_k, nd, ()) mnd ⟨s_nd, htkn_le, hsc_nd, hm_nd⟩
    have hnd_ne : nd ≠ 0xFFFFFFFF#32 := bne_iff_ne.mp hc
    clear hc; m6b_split; rotate_left 1
    · clear hc; m6b_let; exact hJnd_ex (tk_n, sub_k, nd, ()) mnd ⟨s_nd, htkn_le, hsc_nd, hm_nd⟩
    have htkn_lt : tk_n.toNat < tl.toNat := bv64_ult_lt hc
    have htkn1 : (tk_n + 1#64).toNat = tk_n.toNat + 1 := bv64_add1_lt (by omega)
    clear hc
    obtain ⟨hnd_lo, hnd_hi, hnd_ev⟩ := hnd_ok.resolve_left hnd_ne
    have hnd_z : (nd.setWidth 64).toNat = nd.toNat := bv_zext32_toNat nd
    have hnd1_n : (nd.setWidth 64 + 1#64).toNat = nd.toNat + 1 := by
      rw [bv64_add1_lt (by rw [hnd_z]; omega), hnd_z]
    have hnd_scr : (nd.setWidth 64).toNat < s_nd.scratch.scratch_buf.length := by
      rw [hnd_z, hsc_nd.1.1.scratch_ok.scratch_buf_len]; omega
    have hnd1_scr : (nd.setWidth 64 + 1#64).toNat < s_nd.scratch.scratch_buf.length := by
      rw [hnd1_n, hsc_nd.1.1.scratch_ok.scratch_buf_len]; omega
    let dref := s_nd.scratch.scratch_buf[(nd.setWidth 64).toNat]'hnd_scr
    let nxt := s_nd.scratch.scratch_buf[(nd.setWidth 64 + 1#64).toNat]'hnd1_scr
    obtain ⟨hdref_ref0, hnxt_ok⟩ :
        dref.toNat ∈ refs0 ∧ FidFsOccPtrOk (2 * ncand.toNat) occ_pos.toNat nxt := by
      obtain ⟨h1, h2⟩ := hocc2.2.2.2.2 nd.toNat hnd_lo hnd_hi hnd_ev
      rw [← hsc_nd.2.2.2.2.2.2.1] at h1 h2
      dsimp only [dref, nxt]
      rw [List.getElem?_eq_getElem (by rw [← hnd_z]; exact hnd_scr), Option.getD_some,
        ← list_getElem_congr hnd_z hnd_scr _] at h1
      rw [List.getElem?_eq_getElem (by rw [← hnd1_n]; exact hnd1_scr), Option.getD_some,
        ← list_getElem_congr hnd1_n hnd1_scr _] at h2
      exact ⟨h1, h2⟩
    obtain ⟨hdr_arr0, hdr_arr2, hdr2_n, hdr_bd0⟩ := fidFs_cr_ar hsc_nd.1 hdref_ref0
    have hdr_z : (dref.setWidth 64).toNat = dref.toNat := bv_zext32_toNat dref
    have hdr_arr0_z : (dref.setWidth 64).toNat < s_nd.core.arena.length := by
      rw [hdr_z]; exact hdr_arr0
    let dhdr := s_nd.core.arena[(dref.setWidth 64).toNat]'hdr_arr0_z
    let dsz := s_nd.core.arena[(dref.setWidth 64 + 2#64).toNat]'hdr_arr2
    have hdhdr_eq : dhdr = s_nd.core.arena[dref.toNat]'hdr_arr0 := list_getElem_congr hdr_z _ _
    have hdsz_eq : fullArenaClauseSizeCore s_nd.core dref.toNat = dsz.toNat := by
      unfold fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (list_getElem_congr hdr2_n.symm _ _)
    have hnd_step : Jnd (tk_n + 1#64, nxt, ()) mnd :=
      ihnd (tk_n + 1#64, nxt, ()) mnd (by dsimp only; rw [htkn1]; omega)
        ⟨s_nd, by rw [htkn1]; omega, hnxt_ok, hsc_nd, hm_nd⟩
    m6b_to_group
    refine wp_join_group (ts := [.bool])
      (fun _ md => ∃ sd : FullState,
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sd ∧
        (FullMem c sd ⋆ R) md)
      (fun _ _ md ⟨sd, hsd, hmd⟩ => by
        m6b_steps
        exact ihnd (tk_n + 1#64, nxt, ()) md (by dsimp only; rw [htkn1]; omega)
          ⟨sd, by rw [htkn1]; omega, hnxt_ok, hsd, hmd⟩)
      ?_
    intro Jskip_d hJskip_d
    m6b_steps; m6b_split; rotate_left 1
    · clear hc; m6b_let; exact hJskip_d (sub_k, ()) mnd ⟨s_nd, hsc_nd, hm_nd⟩
    have hdgarb0 : (dhdr &&& 0x00080000#32) = 0#32 := by simpa [dhdr, dref] using hc
    clear hc; m6b_split; rotate_left 1
    · clear hc; m6b_let; exact hJskip_d (sub_k, ()) mnd ⟨s_nd, hsc_nd, hm_nd⟩
    clear hc; m6b_to_group
    refine wp_join_group (ts := []) (fun () md => md = mnd) ?_
      (fun Jenter hJenter => by
        m6b_split
        · clear hc; m6b_let; exact hJenter () mnd rfl
        clear hc; m6b_split
        · clear hc; m6b_let; exact hJskip_d (sub_k, ()) mnd ⟨s_nd, hsc_nd, hm_nd⟩
        clear hc; m6b_let; exact hJenter () mnd rfl)
    rintro _ ⟨⟩ md hmd; subst md
    have hng_d : fullArenaClauseGarbCore s_nd.core dref.toNat = false := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem hdr_arr0, Option.getD_some, ← hdhdr_eq]
      exact fid_garb_false_of_and hdgarb0
    have hdr_bd : dref.toNat + 3 + dsz.toNat ≤ alen0 := by rw [← hdsz_eq]; exact hdr_bd0
    -- Innermost dj < dsz loop
    m6b_to_group
    refine wp_join_group (ts := [.bool, i32])
      (fun (dok, _dj, ()) mdj => ∃ sd : FullState,
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sd ∧
        (FullMem c sd ⋆ R) mdj)
      (fun _ ⟨dok, _, ⟨⟩⟩ mdj ⟨sd, hsd, hmdj⟩ => by
        m6b_split
        · m6b_let; exact hJnd_ex (tk_n + 1#64, true, nd, ()) mdj
            ⟨sd, by rw [htkn1]; omega, hsd, hmdj⟩
        m6b_let; exact hJskip_d (sub_k, ()) mdj ⟨sd, hsd, hmdj⟩)
      ?_
    intro Jdj_ex hJdj_ex
    refine wp_loop_inv (ts := [i32])
      (fun (dj, ()) md => ∃ sd : FullState,
        dj.toNat ≤ dsz.toNat ∧
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sd ∧
        (FullMem c sd ⋆ R) md)
      (fun (dj, ()) _ => dsz.toNat - dj.toNat)
      (fun Jd hJd => by m6b_let; exact hJd (0#32, ()) mnd ⟨s_nd, Nat.zero_le _, hsc_nd, hm_nd⟩)
      (fun Jd (dj, ()) md ⟨sd, hdj_le, hsd, hmd⟩ ihd => ?_)
    m6b_split; rotate_left 1
    · m6b_let; exact hJdj_ex (true, dj, ()) md ⟨sd, hsd, hmd⟩
    have hdj_lt : dj.toNat < dsz.toNat := bv32_ult_lt hc
    have hdj1 : (dj + 1#32).toNat = dj.toNat + 1 := bv32_add1_lt_of (by omega)
    have har_sd_nd : sd.core.arena = s_nd.core.arena := hsd.2.1.trans hsc_nd.2.1.symm
    obtain ⟨hol_arr, hol_lt⟩ := fidFs_k_lit_lt (p := dref.setWidth 64) hsd.1 har_sd_nd
      (by rw [hdr_z]; exact hdref_ref0) (by rw [hdr_z]; exact hng_d)
      (by rw [hdr_z]; exact hdsz_eq) (by rw [hdr_z]; exact hdr_bd) hdj_lt
    let ol := sd.core.arena[(dref.setWidth 64 + 3#64 + dj.setWidth 64).toNat]'hol_arr
    have hol_vl : ol.toNat < sd.core.vals.length := fidFs_base_vals_lt hsd.1 hol_lt
    have hol_z : (ol.setWidth 64).toNat = ol.toNat := bv_zext32_toNat ol
    clear hc; m6b_split
    · m6b_let; exact hJdj_ex (false, dj, ()) md ⟨sd, hsd, hmd⟩
    clear hc; m6b_to_group
    refine wp_join_group (ts := [.bool])
      (fun (_dok', ()) m1 => ∃ sd1 : FullState,
        FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz.toNat sd1 ∧
        (FullMem c sd1 ⋆ R) m1)
      (fun _ _ m1 ⟨sd1, hsd1, hm1⟩ => by
        m6b_steps
        exact ihd (dj + 1#32, ()) m1 (by dsimp only; rw [hdj1]; omega)
          ⟨sd1, by rw [hdj1]; omega, hsd1, hm1⟩)
      ?_
    intro Jdo hJdo
    m6b_split; rotate_left 1
    · m6b_let; exact hJdo (true, ()) md ⟨sd, hsd, hmd⟩
    clear hc; m6b_steps; m6b_call hFind
    refine ⟨F_cur, 2 * cv0, sd.core.repr, FullReprRest c sd ⋆ R,
      hsd.1.2.2.2.2.2.2.2.2.2.2.2, hol_lt, focus_full_repr hmd,
      fun ro repr_o mo hrl_o hrepr_o _ hro_lt _ hmo => ?_⟩
    let sd1 : FullState := { sd with core := { sd.core with repr := repr_o } }
    have hmo' : (FullMem c sd1 ⋆ R) mo := unfocus_full_repr hmo
    have hsd1 := fidFsScanInv_with_repr hsd (hrl_o.trans hsd.1.1.core_ok.repr_len) hrepr_o
    have hro_vl : ro.toNat < sd1.core.vals.length := fidFs_base_vals_lt hsd1.1 hro_lt
    have hro_lm : ro.toNat < sd1.core.lit_mark.length := fidFs_base_lm_lt hsd1.1 hro_lt
    have hro_z : (ro.setWidth 64).toNat = ro.toNat := bv_zext32_toNat ro
    m6b_split
    · m6b_let; exact hJdj_ex (false, dj, ()) mo ⟨sd1, hsd1, hmo'⟩
    clear hc; m6b_split
    · clear hc; m6b_split
      · m6b_let; exact hJdj_ex (false, dj, ()) mo ⟨sd1, hsd1, hmo'⟩
      m6b_let; exact hJdo (true, ()) mo ⟨sd1, hsd1, hmo'⟩
    m6b_let; exact hJdo (true, ()) mo ⟨sd1, hsd1, hmo'⟩
  -- After subsumption loop: clear lm, then mark garb (if subsumed) or push occ node!
  rintro _ ⟨⟩ m_cl ⟨s_cl, hsc_cl, hm_cl⟩
  refine fidFs_clearLm_wp Γ hm_cl hsc_cl.1 hsc_cl.2.1 hsc_cl.2.2.2.1 hsc_cl.2.2.2.2.2.2.1
    hmsz_cv htmp_lt (fidFs_lm_clear_from_zero hsc_cl.2.2.2.2.2.2.2)
    fun _kc sc mc hbc harc htmpc hscrc hdc hcvc halc hflc hrefsc hreprc hmc => ?_
  have hpairs_c : FidPairsOk (fun _ cr => cr.toNat ∈ refs0) sc.scratch.scratch_buf ncand.toNat :=
    hscrc.symm ▸ hpairs2
  have hocc_c : FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) occ_pos.toNat
      sc.scratch.work_stk1 sc.scratch.scratch_buf := hscrc.symm ▸ hocc2
  -- Final if (subsumed) ... else if (occ_pos + 2 <= scratch_cap) ...
  m6b_to_group
  refine wp_join_group (ts := [i64])
    (fun (occ_pos', ()) mop => ∃ sop : FullState,
      occ_pos'.toNat ≤ c.scratch_cap ∧
      FullDenseInvW c F0 F_cur sop ∧ sop.core.cur_vars = cv0 ∧
      sop.core.arena_len = alen0 ∧ sop.core.fuel = fuel0 ∧
      fullArenaClauseRefs sop = refs0 ∧ FullCongReprInv F_cur (2 * cv0) sop.core.repr ∧
      FidPairsOk (fun _ cr => cr.toNat ∈ refs0) sop.scratch.scratch_buf ncand.toNat ∧
      FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) occ_pos'.toNat
        sop.scratch.work_stk1 sop.scratch.scratch_buf ∧
      (FullMem c sop ⋆ R) mop)
    (fun _ ⟨occ_pos', ⟨⟩⟩ mop
        ⟨sop, hoccp', hdop, hcvop, halop, hflop, hrefsop, hreprop, hpop, hocop, hmop⟩ => by
      m6b_steps
      exact ihc2 (tk_k, occ_pos', ci + 1#64, ()) mop (by dsimp only; rw [hci1_n]; omega)
        ⟨sop, by rw [hci1_n]; omega, htkk_le, hoccp',
         hdop, hcvop, halop, hflop, hrefsop, hreprop, hpop, hocop, hmop⟩)
    ?_
  intro Jfin hJfin
  m6b_split
  · have hcr_c : cref.toNat < sc.core.arena.length := by rw [harc]; exact hcr_arr0
    have hchdr_c : sc.core.arena[cref.toNat]'hcr_c = chdr := by
      rw [hchdr_eq]; exact list_eq_getElem_congr harc _ _
    clear hc; m6b_steps
    let P_mg (ar' : List (BitVec 32)) (ag' : BitVec 64) :=
      (FullMem c { sc with core := { sc.core with arena := ar', arena_garbage := ag' } } ⋆ R) m
    have hm' : P_mg (sc.core.arena.set cref.toNat (chdr ||| 0x00080000#32))
        (sc.core.arena_garbage + 3#64 + csz.setWidth 64) := by
      have heq1 : sc.core.arena.set (cref.setWidth 64).toNat (chdr ||| 0x00080000#32) =
          sc.core.arena.set cref.toNat (chdr ||| 0x00080000#32) := by rw [hcr_z]
      exact heq1 ▸ hm
    have hd_mg := fid_fs_markGarb_dense' hdc (hrefsc.symm ▸ hcref_ref0) hcr_c
      (sc.core.arena_garbage + 3#64 + csz.setWidth 64)
    have hmg_refs := fid_fs_markGarb_refs hdc (hrefsc.symm ▸ hcref_ref0) hcr_c
      (sc.core.arena_garbage + 3#64 + csz.setWidth 64)
    rw [hchdr_c] at hd_mg hmg_refs
    exact hJfin (occ_pos, ()) m
      ⟨_, hoccp_le, hd_mg, hcvc, halc, hflc, hmg_refs.trans hrefsc, hreprc,
       hpairs_c, hocc_c, hm'⟩
  clear hc; m6b_to_group
  refine wp_join_group (ts := [i64])
    (fun (occ_pos', ()) mop => ∃ sop : FullState,
      occ_pos'.toNat ≤ c.scratch_cap ∧
      FullDenseInvW c F0 F_cur sop ∧ sop.core.cur_vars = cv0 ∧
      sop.core.arena_len = alen0 ∧ sop.core.fuel = fuel0 ∧
      fullArenaClauseRefs sop = refs0 ∧ FullCongReprInv F_cur (2 * cv0) sop.core.repr ∧
      FidPairsOk (fun _ cr => cr.toNat ∈ refs0) sop.scratch.scratch_buf ncand.toNat ∧
      FidFsOccOk refs0 (2 * cv0) (2 * ncand.toNat) occ_pos'.toNat
        sop.scratch.work_stk1 sop.scratch.scratch_buf ∧
      (FullMem c sop ⋆ R) mop)
    (fun _ x mop hx => by m6b_let; exact hJfin x mop hx) ?_
  intro Jfin2 hJfin2
  m6b_split; rotate_left 1
  · m6b_let
    exact hJfin2 (occ_pos, ()) mc
      ⟨sc, hoccp_le, hdc, hcvc, halc, hflc, hrefsc, hreprc, hpairs_c, hocc_c, hmc⟩
  have hoccp2_n : (occ_pos + 2#64).toNat = occ_pos.toNat + 2 := bv64_add2_lt (by omega)
  have hoccp2_le : occ_pos.toNat + 2 ≤ c.scratch_cap := by
    have h := bv64_ule_le hc
    change (occ_pos + 2#64).toNat ≤ (BitVec.ofNat 64 c.scratch_cap).toNat at h
    rwa [hoccp2_n, bv64_ofNat_toNat_lt (by omega)] at h
  have hoccp1_n : (occ_pos + 1#64).toNat = occ_pos.toNat + 1 := bv64_add1_lt (by omega)
  have hscr_lc := hdc.1.scratch_ok.scratch_buf_len
  have hoccp_arr : occ_pos.toNat < sc.scratch.scratch_buf.length := by omega
  have hoccp1_arr : (occ_pos + 1#64).toNat < sc.scratch.scratch_buf.length := by
    rw [hoccp1_n]; omega
  have hlr_z : (lr.setWidth 64).toNat = lr.toNat := bv_zext32_toNat lr
  have hlr_w1 : lr.toNat < sc.scratch.work_stk1.length := by
    have := hdc.1.scratch_ok.work_stk1_len; omega
  have hlr_w1_z : (lr.setWidth 64).toNat < sc.scratch.work_stk1.length := by
    rw [hlr_z]; exact hlr_w1
  have hlr_w2 : lr.toNat < sc.scratch.work_stk2.length := by
    rw [hdc.1.scratch_ok.work_stk2_len]; omega
  have hlr_w2_z : (lr.setWidth 64).toNat < sc.scratch.work_stk2.length := by
    rw [hlr_z]; exact hlr_w2
  clear hc; m6b_steps
  have hop_bv32 : occ_pos.setWidth 32 = BitVec.ofNat 32 occ_pos.toNat := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  have hhead_eq : sc.scratch.work_stk1[(lr.setWidth 64).toNat]'hlr_w1_z =
      sc.scratch.work_stk1[lr.toNat]'hlr_w1 := list_getElem_congr hlr_z _ _
  have hcnt_eq : sc.scratch.work_stk2[(lr.setWidth 64).toNat]'hlr_w2_z =
      sc.scratch.work_stk2[lr.toNat]'hlr_w2 := list_getElem_congr hlr_z _ _
  try rw [show s2.scratch.scratch_buf[(ci <<< OfNat.ofNat 1 + 1).toNat] = cref from rfl] at hm
  rw [show (occ_pos + 1).toNat = (occ_pos + 1#64).toNat from rfl] at hm
  rw [hoccp1_n, hhead_eq, hcnt_eq, hlr_z, hop_bv32] at hm
  have hocc_push := fidFsOccOk_push hocc_c (by omega) (by omega) hcref_ref0 hlr_lt hlr_w1
  have hpairs_push : FidPairsOk (fun _ cr => cr.toNat ∈ refs0)
      ((sc.scratch.scratch_buf.set occ_pos.toNat cref).set (occ_pos.toNat + 1)
        (sc.scratch.work_stk1[lr.toNat]'hlr_w1)) ncand.toNat :=
    fidPairsOk_set_ge (fidPairsOk_set_ge hpairs_c hocc_c.1) (by have := hocc_c.1; omega)
  let scr_p := (sc.scratch.scratch_buf.set occ_pos.toNat cref).set (occ_pos.toNat + 1)
    (sc.scratch.work_stk1[lr.toNat]'hlr_w1)
  let w1_p := sc.scratch.work_stk1.set lr.toNat (BitVec.ofNat 32 occ_pos.toNat)
  let w2_p := sc.scratch.work_stk2.set lr.toNat (sc.scratch.work_stk2[lr.toNat]'hlr_w2 + 1#32)
  have hd_push := fid_denseInvW_with_ws12
    (w1' := w1_p) (w2' := w2_p)
    (fid_denseInvW_with_scr (scr' := scr_p) hdc (by simp [scr_p, hscr_lc]))
    (by simp [w1_p, hdc.1.scratch_ok.work_stk1_len])
    (by simp [w2_p, hdc.1.scratch_ok.work_stk2_len])
  exact hJfin2 (occ_pos + 2#64, ()) m
    ⟨_, by rw [hoccp2_n]; exact hoccp2_le, hd_push, hcvc, halc, hflc, hrefsc, hreprc,
     hpairs_push, by rw [hoccp2_n]; exact hocc_push, hm⟩

end FwdSubsumeProof

end LeanQbe.T.Examples.Kissat.FullFidelityCong

end
