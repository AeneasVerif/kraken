/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-! # Kissat Step-13 S6a Unchanged-Caller Lifts — Part 3b (Shared Subproofs)
Callee-parametric `(Γ : Env)` Step-13 helper subproofs (`deduce_1uip` helpers &
`full_elim_bve_m6_step13_wp`): `0` cross-shard `S0..S5` imports, `0` `@[expose]`, `<= 100` cols. -/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullAnalyzeHelpers FullDenseWatchHelpers FullFastBveBudgets FullM3CongBva FullM6BveFwd
open scoped FullArenaTactics FullAnalyzeTactics Deduce1UipTactics

local macro "s6a_m6_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Deduce-1UIP Clear, UIP-Exit & OTFS Branch Helpers (`step13OtfsLargeSpec`) -/

private theorem s6a_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  simpa [litVar, litNeg] using litVar_litNeg l

private theorem s6a_litMarksClear_of_mrk {c : FullCfg} {s s' : FullState}
    (h0 : Full.FullLitMarksClear c s) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hmrk : ∀ v < c.max_vars, s'.core.mrk[v]?.getD 0#8 = 0#8) :
    Full.FullLitMarksClear c s' :=
  ⟨hmrk, fun l hl => by rw [hlm]; exact h0.2 l hl⟩

private theorem s6a_otfsInvW_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut' : Nat} {s s' : FullState} (hlen : s'.LengthsOk c)
    (hw : Full.FullWitnessCutInv c F0 F_cur cut' s'.core) (hmrk : Full.FullLitMarksClear c s')
    (hnd : Full.FullArenaVarsNodup s') (hext0 : Full.FullExtScratchOk c s)
    (hext : Full.FullExtScratchPres s s')
    (hrefs : Full.fullArenaClauseRefs s' = Full.fullArenaClauseRefs s)
    (hdm : s'.core.dense_mode = 0#64) : Full.FullOtfsInvW c F0 F_cur s' :=
  ⟨hlen, hw.toFullOtfsWitnessInv, hmrk, hnd,
   ⟨fun i hi => by
      change (let cr := s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32; _); rw [hext.1]
      exact (hext0.1 i hi).imp id (fun h => hrefs ▸ h),
    by rw [hext.2]; exact hext0.2⟩, hdm⟩

private theorem s6a_lowerLits_tmp_take {tmp : List (BitVec 32)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (_htl : tl ≤ tmp.length) (h0 : tmp[0]? = some uip) :
    (tmp.take tl).map BitVec.toNat = uip.toNat :: Full.fullLowerLits tmp tl := by
  cases tmp with
  | nil => simp at h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases tl with
    | zero => omega
    | succ n => simp [Full.fullLowerLits]

theorem s6a_anaMarksCov_of_same {c : FullCfg} {s1 s2 : FullState}
    (hcov : Full.FullAnaMarksCov c s1) (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (hmcl : s2.core.min_clr_len = s1.core.min_clr_len) (hmrk : s2.core.mrk = s1.core.mrk)
    (hws1 : s2.scratch.work_stk1 = s1.scratch.work_stk1) : Full.FullAnaMarksCov c s2 :=
  ⟨by rw [hcv, hmcl]; exact hcov.1, by rw [hmcl, hws1]; exact hcov.2.1,
   fun k hk => by rw [hws1, hcv, hmrk]; exact hcov.2.2.1 k (hmcl ▸ hk),
   fun v hv hnz => by
     rw [hmrk] at hnz; obtain ⟨k, hk, hget⟩ := hcov.2.2.2 v hv hnz
     exact ⟨k, by rw [hmcl]; exact hk, by rw [hws1]; exact hget⟩⟩

private theorem s6a_cut_with_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut' : Nat} {k : FullCoreState} (hw : Full.FullWitnessCutInv c F0 F_cur cut' k)
    (ct' cr' : BitVec 64) :
    Full.FullWitnessCutInv c F0 F_cur cut' { k with confl_type := ct', confl_ref := cr' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

private theorem s6a_deduce_clear_ana_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {K : Tup Val [] → Expr Val Cont [i64]}
    {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (hlen1 : s1.LengthsOk c) (hw1 : Full.FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : Full.FullAnaMarksCov c s1) (hext0 : Full.FullExtScratchOk c s)
    (hext1 : Full.FullExtScratchPres s s1) (hnd1 : Full.FullArenaVarsNodup s1)
    (hrefs1 : Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s)
    (hlm1 : s1.core.lit_mark = s.core.lit_mark) (hdm1 : s1.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk' m_clr,
      let s_clr : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
      s_clr.LengthsOk c → Full.FullOtfsInvW c F0 F_cur s_clr →
      Full.FullWitnessCutInv c F0 F_cur cut' s_clr.core → (FullMem c s_clr ⋆ R) m_clr →
      wp Γ Q X (K ()) m_clr) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana"
      (Arg.var c.hdr, ()) K) m1 := by
  refine wp_call_of_spec _ _ (hClear (c.hdr, ()) _ _ _ ⟨c, s1, R, rfl, hlen1, hm1, ?_⟩)
  intro mrk' m_c hm'_len _ _ hm'_cov hm_c
  let s_c : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
  have hlen_c : s_c.LengthsOk c :=
    ⟨{ hlen1.core_ok with mrk_len := hm'_len, min_clr_len_le := Nat.zero_le _ }, hlen1.scratch_ok⟩
  have hw_c : Full.FullWitnessCutInv c F0 F_cur cut' s_c.core :=
    Full.deduce_same_core_cut hw1 mrk' s1.core.tmp s1.core.tmp_cnt s1.core.tmp_len 0
  have hlm_c : Full.FullLitMarksClear c s_c := s6a_litMarksClear_of_mrk hm0_lm hlm1 (hm'_cov hcov1)
  exact hK mrk' m_c hlen_c (s6a_otfsInvW_of hlen_c hw_c hlm_c hnd1 hext0 hext1 hrefs1 hdm1)
    hw_c hm_c

private theorem s6a_deduce_res_clear_ret_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (retv : BitVec 64)
    (hlen1 : s1.LengthsOk c) (hw1 : Full.FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : Full.FullAnaMarksCov c s1) (hext0 : Full.FullExtScratchOk c s)
    (hext1 : Full.FullExtScratchPres s s1) (hws2 : s1.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd1 : Full.FullArenaVarsNodup s1)
    (hrefs1 : Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s)
    (hstat1 : Full.FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk_c m_c,
      let s_c : FullState :=
        { s1 with core := { s1.core with mrk := mrk_c, min_clr_len := 0 },
                  scratch := { s1.scratch with res_sz := BitVec.ofNat 64 s1.core.min_clr_len } }
      s_c.LengthsOk c → Full.FullOtfsInvW c F0 F_cur s_c →
      Full.FullWitnessCutInv c F0 F_cur cut' s_c.core → Full.FullCutInvW c F0 F_cur cut' s_c →
      s_c.core.cur_vars = s.core.cur_vars → s_c.core.cur_level = s.core.cur_level →
      s_c.core.fuel = s.core.fuel → s_c.scratch.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s_c ⋆ R) m_c → Q (retv, ()) m_c) :
    wp Γ Q X (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272#64, ())) fun p1 =>
      .load i64 (Arg.var p1.fst) fun ld =>
        .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144#64, ())) fun p2 =>
          .store (Arg.var ld) (Arg.var p2.fst)
            (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
              (fun _ => .ret (Arg.imm retv, ())))) m1 := by
  c0_let_simp; refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm1) ?_; c0_let_simp
  refine wp_store_sep (FullArenaTactics.store_full_res_sz
    (BitVec.ofNat 64 s1.core.min_clr_len) hm1) fun m_r hm_r => ?_
  let s_r : FullState :=
    { s1 with scratch := { s1.scratch with res_sz := BitVec.ofNat 64 s1.core.min_clr_len } }
  have hlen_r : s_r.LengthsOk c := ⟨hlen1.core_ok, { hlen1.scratch_ok with }⟩
  refine s6a_deduce_clear_ana_wp hClear hlen_r hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1.lm
    (hstat1.dm.trans hdm0) hm0_lm hm_r fun mrk_c m_c hlen_c hotfs_c hw_c hm_c => ?_
  fa_fast_steps
  let s_c : FullState :=
    { s1 with core := { s1.core with mrk := mrk_c, min_clr_len := 0 },
              scratch := { s1.scratch with res_sz := BitVec.ofNat 64 s1.core.min_clr_len } }
  have hcutw : Full.FullCutInvW c F0 F_cur cut' s_c :=
    ⟨hlen_c, hw_c, hotfs_c.2.2.1, hotfs_c.2.2.2.1, hotfs_c.2.2.2.2.1, hotfs_c.2.2.2.2.2⟩
  exact hK mrk_c m_c hlen_c hotfs_c hw_c hcutw hstat1.cv hstat1.cl hstat1.fuel hws2 hm_c

theorem s6a_deduce_uip_exit_body_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut_b idx_u : Nat}
    {s sb : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mb : Mem 64}
    {p_bv : BitVec 32}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        Full.FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        Full.FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hext0 : Full.FullExtScratchOk c s) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s) (hlen_b : sb.LengthsOk c)
    (hw_b : Full.FullWitnessCutInv c F0 F_cur cut_b sb.core)
    (hcov_b : Full.FullAnaMarksCov c sb) (hext_b : Full.FullExtScratchPres s sb)
    (hws2_b : sb.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd_b : Full.FullArenaVarsNodup sb)
    (hrefs_b : Full.fullArenaClauseRefs sb = Full.fullArenaClauseRefs s)
    (hstat_b : Full.FullDeduceStaticEq s.core sb.core)
    (htl1 : 1 ≤ sb.core.tmp_len) (htl_cv : sb.core.tmp_len ≤ sb.core.cur_vars)
    (hlow_b : Full.FullLowerInv c sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len)
    (hiu_te : idx_u < sb.core.trail_end)
    (hp_get : (sb.core.trl[idx_u]?.getD 0#32).toNat = p_bv.toNat)
    (hpl_cl : (sb.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sb.core.cur_level)
    (hent_b : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((p_bv ^^^ 1#32).toNat :: Full.fullLowerLits sb.core.tmp sb.core.tmp_len)))
    (hmb : (FullMem c sb ⋆ R) mb) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i32 .bool rfl)
        (Arg.var (p_bv ^^^ 1#32), Arg.imm 0xFFFFFFFF#32, ())) fun p19 =>
      .jnz (Arg.var p19.fst)
        (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
          fun _ => .ret (Arg.imm 0#64, ()))
        (.let_ (Op.mk (.sext 32 64) (Arg.imm 0#32, ())) fun p20 =>
          .let_ (Op.mk (.mul i64) (Arg.var p20.fst, Arg.imm 4#64, ())) fun p21 =>
            .let_ (Op.mk (.add i64) (Arg.var c.pTmp, Arg.var p21.fst, ())) fun p22 =>
              .store (Arg.var (t := i32) (p_bv ^^^ 1#32)) (Arg.var p22.fst)
                (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272#64, ())) fun p23 =>
                  .load i64 (Arg.var p23.fst) fun ld =>
                    .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144#64, ())) fun p24 =>
                      .store (Arg.var ld) (Arg.var p24.fst)
                        (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana"
                          (Arg.var c.hdr, ()) fun _ => .ret (Arg.imm 1#64, ()))))) mb := by
  let uip := p_bv ^^^ 1#32
  have hmaxv := c.hmaxv; have hcv_le := hlen_b.core_ok.cur_vars_le; unfold dimacsBound at hmaxv
  have hp_lt : p_bv.toNat < 2 * sb.core.cur_vars := hp_get ▸ hw_b.trail_lits_lt idx_u hiu_te
  have huip_nat : uip.toNat = p_bv.toNat ^^^ 1 := bv32_xor_1 p_bv
  have huip_lt : uip.toNat < 2 * sb.core.cur_vars := huip_nat ▸ litNeg_lt_two_mul hp_lt
  have huip_ne : uip ≠ 0xFFFFFFFF#32 := fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  have htb_len : sb.core.tmp.length = c.max_vars := hlen_b.core_ok.tmp_len_arr
  have h0_tb : 0 < sb.core.tmp.length := by have := hw_b.cur_level_le; omega
  let tmp0 := sb.core.tmp.set 0 uip
  have htmp0_len : tmp0.length = c.max_vars := by rw [List.length_set, htb_len]
  let s0 : FullState := { sb with core := { sb.core with tmp := tmp0 } }
  have htmp0_gt0 : ∀ j, 1 ≤ j → tmp0[j]? = sb.core.tmp[j]? := fun _ _ =>
    List.getElem?_set_ne (by omega)
  have htmp0_0 : tmp0[0]? = some uip := List.getElem?_set_self h0_tb
  have hlow0 : Full.FullLowerInv c s0.core tmp0 sb.core.mrk sb.core.tmp_len :=
    ⟨fun j h1 h2 => htmp0_gt0 j h1 ▸ hlow_b.1 j h1 h2, fun j1 j2 h1 h12 h2 => by
      have := hlow_b.2 j1 j2 h1 h12 h2; rwa [htmp0_gt0 j1 h1, htmp0_gt0 j2 (by omega)]⟩
  have hlowLits0 : Full.fullLowerLits tmp0 sb.core.tmp_len =
      Full.fullLowerLits sb.core.tmp sb.core.tmp_len := by
    change Full.fullLowerLits (sb.core.tmp.set 0 uip) sb.core.tmp_len = _
    unfold Full.fullLowerLits; cases sb.core.tmp <;> rfl
  have hs0_len : s0.LengthsOk c :=
    ⟨{ hlen_b.core_ok with tmp_len_arr := by dsimp [s0, tmp0]; simp [htb_len] }, hlen_b.scratch_ok⟩
  have hw0 := Full.deduce_same_core_cut hw_b sb.core.mrk tmp0 sb.core.tmp_cnt sb.core.tmp_len
    sb.core.min_clr_len
  have huip_fals : sb.core.vals[uip.toNat]?.getD 0#8 = 0xFF#8 :=
    (hw_b.vals_false_iff uip.toNat huip_lt).mpr ⟨idx_u, hiu_te, by
      rw [hp_get, huip_nat]; exact (litNeg_litNeg _).symm⟩
  have huip_cl : (sb.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = sb.core.cur_level := by
    rwa [huip_nat, s6a_xor1_div2]
  c0_let_simp; refine wp_jnz_of (fun hc => ?_) (fun _ => ?_)
  · simp only [Arg.val_var] at hc; c0_cond hc; exact absurd hc huip_ne
  · c0_let_simp
    refine wp_store_sep (Full.Deduce1UipTactics.d1_store_full_tmp0_mul uip h0_tb hmb)
      fun m_st hm_st => ?_
    refine s6a_deduce_res_clear_ret_wp hClear 1#64 hs0_len hw0 hcov_b hext0 hext_b hws2_b
      hnd_b hrefs_b hstat_b.repack hdm0 hm0_lm hm_st
      fun mrk_c m_c hlen_c hotfs_c _ _ hcv_c hcl_c hfuel_c hws2_c hm_c => ?_
    let s_c : FullState :=
      { s0 with core := { s0.core with mrk := mrk_c, min_clr_len := 0 },
                scratch := { s0.scratch with res_sz := BitVec.ofNat 64 s0.core.min_clr_len } }
    have _hsc_tl_len : s_c.core.tmp.length = c.max_vars := htmp0_len
    have hnd_uip := Full.fullTmpTake_uip_nodup htl1 (by omega) htmp0_0 hlow0 huip_cl
    refine hQ 1#64 s_c m_c hlen_c (Or.inr (Or.inl rfl)) hcv_c hfuel_c hws2_c
      (fun h => by cases h) (fun h => by cases h) (fun _ => ?_) (fun h => by cases h) hm_c
    refine ⟨hotfs_c, hcl_c, htl1, htl_cv, hnd_uip, fun k hk => ?_, fun k hk1 hk2 => ?_, ?_, ?_⟩
    · cases k with
      | zero => rw [htmp0_0, Option.getD_some]; exact ⟨huip_lt, huip_fals⟩
      | succ k' => let hlk := hlow0.1 (k' + 1) (by omega) hk; exact ⟨hlk.1, hlk.2.1⟩
    · let hlk := hlow0.1 k hk1 hk2; exact ⟨hlk.2.2.1, hlk.2.2.2.1⟩
    · rw [htmp0_0, Option.getD_some]; exact huip_cl
    · rw [s6a_lowerLits_tmp_take htl1 (by omega) htmp0_0, hlowLits0]; exact hent_b

private theorem s6a_deduce_otfs_ret2_subsume_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut idx' resolved : Nat}
    {s s_ot : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m_ot : Mem 64}
    {init_res_sz old_ct old_cr : BitVec 64} {p rsn : BitVec 32}
    {new_confl_arg : Arg Val i32} {to_bin : Bool}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        Full.FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        Full.FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hw0 : Full.FullWitnessCutInv c F0 F_cur cut s.core)
    (hconfl0 : Full.FullConflictOkCut F_cur cut s)
    (hext0 : Full.FullExtScratchOk c s) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s)
    (hlen_ot : s_ot.LengthsOk c) (hw_ot : Full.FullWitnessCutInv c F0 F_cur idx' s_ot.core)
    (hcov_ot : Full.FullAnaMarksCov c s_ot) (hext_ot : Full.FullExtScratchPres s s_ot)
    (hws2_ot : s_ot.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd_ot : Full.FullArenaVarsNodup s_ot)
    (hrefs_ot : Full.fullArenaClauseRefs s_ot = Full.fullArenaClauseRefs s)
    (hstat_ot : Full.FullDeduceStaticEq s.core s_ot.core)
    (hconfl_ot : Full.FullConflictOkCut F_cur idx' s_ot)
    (hiu_te : idx' < s_ot.core.trail_end) (hres_lt : resolved + 1 < 2 ^ 64)
    (hbin_ct : to_bin = true → s_ot.core.confl_type = 1#64)
    (hzero_cond : resolved = 0 →
      cut = cut ∧ idx' < cut ∧ (s.core.trl[idx']?.getD 0#32).toNat = p.toNat ∧
      s.core.rsns[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn ∧
      rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) = 0#32 ∧
      old_ct = s.core.confl_type ∧ old_cr = s.core.confl_ref ∧
      (to_bin = false → new_confl_arg.val.toNat ∈ Full.fullArenaClauseRefs s_ot ∧
        new_confl_arg.val.toNat = rsn.toNat ∧ s_ot.core.confl_ref.toNat = rsn.toNat))
    (hm_ot : (FullMem c s_ot ⋆ R) m_ot) :
    wp Γ Q X (.group (sig := [[]]) (fun _Js => .cons (fun _ =>
      .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272#64, ())) fun p1 =>
        .load i64 (Arg.var p1.fst) fun ld =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144#64, ())) fun p2 =>
            .store (Arg.var ld) (Arg.var p2.fst)
              (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
                fun _ => .ret (Arg.imm 2#64, ()))) .nil)
      fun Js => .let_ (Op.mk (.cmp .eq i64 .bool rfl)
          (Arg.var (BitVec.ofNat 64 resolved + 1#64), Arg.imm 1#64, ()))
        fun p66 => .jnz (Arg.var p66.fst)
          (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p67 =>
            .load i64 (Arg.var p67.fst) fun ld23 =>
              .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                  (Arg.var ld23, Arg.var init_res_sz, ()))
                fun p68 => .jnz (Arg.var p68.fst)
                  (.call (rs := [i64]) (as := [i64, i32, i64, i64, .bool]) (bs := [])
                    "full_otfs_subsume"
                    (Arg.var c.hdr, new_confl_arg, Arg.var old_ct, Arg.var old_cr,
                      Arg.imm to_bin, ())
                    fun _ => .jump Js.fst ())
                  (.jump Js.fst ()))
          (.jump Js.fst ())) m_ot := by
  fa_fast_steps_nogrp
  refine wp_join_group (ts := []) (fun () ml => ∃ s_j : FullState,
      s_j.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur idx' s_j.core ∧
      Full.FullAnaMarksCov c s_j ∧ Full.FullExtScratchPres s s_j ∧
      s_j.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup s_j ∧
      Full.fullArenaClauseRefs s_j = Full.fullArenaClauseRefs s ∧
      Full.FullDeduceStaticEq s.core s_j.core ∧ Full.FullConflictOkCut F_cur idx' s_j ∧
      (FullMem c s_j ⋆ R) ml) ?_ ?_
  · rintro _ ⟨⟩ ml ⟨s_j, hlen_j, hw_j, hcov_j, hext_j, hws2_j, hnd_j, hrefs_j, hstat_j,
      hconfl_j, hml⟩
    fa_fast_steps_nogrp
    refine s6a_deduce_res_clear_ret_wp hClear 2#64 hlen_j hw_j hcov_j hext0 hext_j hws2_j
      hnd_j hrefs_j hstat_j hdm0 hm0_lm hml fun mrk_c m_c hlen_c _ hw_c hcut_c hcv_c
        hcl_c hfuel_c hws2_c hm_c => ?_
    let s_c : FullState :=
      { s_j with core := { s_j.core with mrk := mrk_c, min_clr_len := 0 },
                 scratch := { s_j.scratch with res_sz := BitVec.ofNat 64 s_j.core.min_clr_len } }
    have hte_eq : s_c.core.trail_end = s_j.core.trail_end := rfl
    have hte_j : s_j.core.trail_end = s_ot.core.trail_end := by rw [hstat_j.te, hstat_ot.te]
    have hconfl_c := Full.deduce_conflOk_same_of_clear hconfl_j rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl
    exact Full.deduce_otfs_ret2_post hQ hlen_c (by rw [hte_eq, hte_j]; exact Nat.le_of_lt hiu_te)
      hcut_c hconfl_c hcv_c hcl_c hfuel_c hws2_c hm_c
  · intro Jsub hJsub; fa_fast_steps
    · have hres0 : resolved = 0 := by
        have hnat := congrArg BitVec.toNat (by assumption : BitVec.ofNat 64 resolved + 1#64 = 1#64)
        simp only [bv_c0, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : resolved < 2 ^ 64), Nat.mod_eq_of_lt hres_lt] at hnat
        omega
      obtain ⟨_, hiu_cut0, hp0, hr0, hrsn_ne0, hrsn_lg0, hct0, hcr0, hnew0⟩ := hzero_cond hres0
      have hnonact := Full.deduce_otfs_old_cr_nonactive hw0 hconfl0 hiu_cut0
        (by rw [← hstat_ot.te]; exact hiu_te) hp0 hr0 hrsn_ne0 hrsn_lg0 hct0 hcr0 hstat_ot
      refine wp_call_of_spec _ _ (hOtfsSub (c.hdr, new_confl_arg.val, old_ct, old_cr, to_bin, ())
        _ _ _ ⟨c, F0, F_cur, idx', s_ot, R, rfl, hlen_ot, hw_ot, hnd_ot, fun hct2 hcr_ne => ?_,
          hm_ot, ?_⟩)
      · obtain ⟨hne_rsn, hna⟩ := hnonact hct2 hcr_ne
        refine ⟨?_, fun hf => (hnew0 hf).1, hna⟩
        rw [hrefs_ot, hcr0]; rcases hconfl0.1 with ⟨h1, _⟩ | ⟨_, href0, _⟩
        · exact absurd (hct0.symm.trans hct2) (by rw [h1]; decide)
        · exact href0
      · intro arena_s ag_s ni_s nr_s m_s _ hlen_s hw_s hnd_s hrefs_s hkeep_s hm_s
        let s_s : FullState :=
          { s_ot with core := { s_ot.core with arena := arena_s, arena_garbage := ag_s,
                                               num_irred := ni_s, num_redundant := nr_s } }
        have hconfl_s : Full.FullConflictOkCut F_cur idx' s_s := by
          refine Full.deduce_conflOk_of_subsume hconfl_ot rfl rfl rfl rfl rfl rfl rfl rfl rfl
            hrefs_s fun r hr => ⟨(hkeep_s r hr).1, fun hct2 r_eq => ?_⟩
          rcases hkeep_s r hr with ⟨_, hgr⟩
          by_cases hct_old : old_ct = 2#64 ∧ old_cr ≠ 0xFFFFFFFF#64
          · have ⟨hne_rsn, _⟩ := hnonact hct_old.1 hct_old.2; refine hgr fun _ => ?_
            cases to_bin with
            | true => exact absurd (hct2.symm.trans (hbin_ct rfl)) (by decide)
            | false => obtain ⟨_, _, hcr_sot⟩ := hnew0 rfl; rw [r_eq, hcr_sot]; exact hne_rsn
          · by_cases hct_old2 : old_ct = 2#64
            · have heqff : old_cr = 0xFFFFFFFF#64 :=
                Classical.byContradiction fun hne => hct_old ⟨hct_old2, hne⟩
              have hwf := (hw_ot.arena.refs_wf r hr).1; have har_le := hlen_ot.core_ok.arena_len_le
              have hcap31 := c.harena; unfold dimacsBound at hcap31; refine hgr fun _ => ?_
              rw [heqff]; have hff : (0xFFFFFFFF#64 : BitVec 64).toNat = 4294967295 := rfl; omega
            · exact hgr (fun h => absurd h hct_old2)
        fa_fast_steps
        exact hJsub () m_s ⟨s_s, hlen_s, hw_s, hcov_ot, hext_ot, hws2_ot, hnd_s,
          hrefs_s.trans hrefs_ot, hstat_ot.repack, hconfl_s, hm_s⟩
    · exact hJsub () m_ot ⟨s_ot, hlen_ot, hw_ot, hcov_ot, hext_ot, hws2_ot, hnd_ot, hrefs_ot,
        hstat_ot, hconfl_ot, hm_ot⟩
    · exact hJsub () m_ot ⟨s_ot, hlen_ot, hw_ot, hcov_ot, hext_ot, hws2_ot, hnd_ot, hrefs_ot,
        hstat_ot, hconfl_ot, hm_ot⟩

private theorem s6a_deduce_otfs_loop_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx' tc2 tl2 : Nat} {s s2 s3 s' : FullState} {mrk2 : List (BitVec 8)}
    {tmp2 : List (BitVec 32)}
    (hlen' : s'.LengthsOk c) (hw' : Full.FullWitnessCutInv c F0 F_cur idx' s'.core)
    (hcov' : Full.FullAnaMarksCov c s') (hext' : Full.FullExtScratchPres s s')
    (hws2' : s'.scratch.work_stk2 = s.scratch.work_stk2) (hnd' : Full.FullArenaVarsNodup s')
    (hrefs' : Full.fullArenaClauseRefs s' = Full.fullArenaClauseRefs s)
    (hstat' : Full.FullDeduceStaticEq s.core s'.core)
    (hres' : s'.scratch.res_sz = BitVec.ofNat 64 ((tl2 - 1) + tc2))
    (hs3_hw_eq : s3.core = s2.core) (hcv : s'.core.cur_vars = s3.core.cur_vars)
    (hcl : s'.core.cur_level = s3.core.cur_level) (hte : s'.core.trail_end = s3.core.trail_end)
    (hvals : s'.core.vals = s3.core.vals) (hlvl : s'.core.lvl = s3.core.lvl)
    (htrl : s'.core.trl = s3.core.trl) (hmrk : s'.core.mrk = s3.core.mrk)
    (htmp : s'.core.tmp = s3.core.tmp) (htl : s'.core.tmp_len = s3.core.tmp_len)
    (htc : s'.core.tmp_cnt = s3.core.tmp_cnt)
    (hs3_mrk : s2.core.mrk = mrk2) (hs3_tmp : s2.core.tmp = tmp2)
    (hs3_tl : s2.core.tmp_len = tl2) (hs3_tc : s2.core.tmp_cnt = tc2)
    (htc2_eq' : tc2 = (Full.fullCurTrailIdxs s2.core mrk2 idx').length)
    (htl2_1 : 1 ≤ tl2) (htl2_cv' : tl2 ≤ s2.core.cur_vars)
    (hlow2 : Full.FullLowerInv c s2.core tmp2 mrk2 tl2)
    (hmcov2 : Full.FullMarksCov s2.core tmp2 mrk2 tl2)
    (hent2 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (Full.fullActiveResolvent s2.core tmp2 mrk2 tl2 idx'))) :
    Full.FullDeduceStateInv c F0 F_cur idx' idx' s s' := by
  have hcv2 : s'.core.cur_vars = s2.core.cur_vars :=
    hcv.trans (congrArg FullCoreState.cur_vars hs3_hw_eq)
  have hcl2 : s'.core.cur_level = s2.core.cur_level :=
    hcl.trans (congrArg FullCoreState.cur_level hs3_hw_eq)
  have hte2 : s'.core.trail_end = s2.core.trail_end :=
    hte.trans (congrArg FullCoreState.trail_end hs3_hw_eq)
  have hva2 : s'.core.vals = s2.core.vals := hvals.trans (congrArg FullCoreState.vals hs3_hw_eq)
  have hlv2 : s'.core.lvl = s2.core.lvl := hlvl.trans (congrArg FullCoreState.lvl hs3_hw_eq)
  have htr2 : s'.core.trl = s2.core.trl := htrl.trans (congrArg FullCoreState.trl hs3_hw_eq)
  have hmr2 : s'.core.mrk = mrk2 :=
    hmrk.trans ((congrArg FullCoreState.mrk hs3_hw_eq).trans hs3_mrk)
  have htp2 : s'.core.tmp = tmp2 :=
    htmp.trans ((congrArg FullCoreState.tmp hs3_hw_eq).trans hs3_tmp)
  have htl2 : s'.core.tmp_len = tl2 :=
    htl.trans ((congrArg FullCoreState.tmp_len hs3_hw_eq).trans hs3_tl)
  have htc2 : s'.core.tmp_cnt = tc2 :=
    htc.trans ((congrArg FullCoreState.tmp_cnt hs3_hw_eq).trans hs3_tc)
  refine ⟨hlen', hw', hcov', hext', hws2', hnd', hrefs', hstat', htl2 ▸ htl2_1,
    by rw [htl2, hcv2]; exact htl2_cv',
    by rw [htc2, hmr2]; unfold Full.fullCurTrailIdxs; rw [htr2, hlv2, hcl2]; exact htc2_eq',
    by rw [hmr2, htp2, htl2]; unfold Full.FullLowerInv
       rw [hcv2, hva2, hlv2, hcl2]; exact hlow2,
    by rw [hmr2, htp2, htl2]; unfold Full.FullMarksCov
       rw [hcv2, hte2, htr2, hlv2, hcl2]; exact hmcov2,
    fun j hj _ _ => hj,
    by rw [hmr2, htp2, htl2]; unfold Full.fullActiveResolvent Full.fullCurLits
       unfold Full.fullCurTrailIdxs; rw [htr2, hlv2, hcl2]; exact hent2,
    by rw [htl2, htc2]; exact hres'⟩

theorem s6a_deduce_otfs_branch_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, step13OtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut cut_cur idx' resolved : Nat}
    {s sl sl2 s2 s3 : FullState} {mrk2 : List (BitVec 8)} {tmp2 : List (BitVec 32)}
    {tc2 tl2 : Nat} {sc2 : FullScratch} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {m3 : Mem 64} {init_res_sz : BitVec 64} {p_bv rsn : BitVec 32} {Js : Cont []}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        Full.FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        Full.FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hw0 : Full.FullWitnessCutInv c F0 F_cur cut s.core)
    (hconfl0 : Full.FullConflictOkCut F_cur cut s)
    (hext0 : Full.FullExtScratchOk c s) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s)
    (hJot : ∀ ml,
      (∃ (cut_n : Nat) (s_n : FullState),
        idx' + (resolved + 1) ≤ s_n.core.trail_end ∧
        Full.FullDeduceStateInv c F0 F_cur cut_n idx' s s_n ∧ 0 < s_n.core.tmp_cnt ∧
        (FullMem c s_n ⋆ R) ml) → Js () ml)
    (_hcv_le : sl.core.cur_vars ≤ c.max_vars) (hcur_pos : 0 < s.core.cur_level)
    (hres1_lt64 : resolved + 1 < 2 ^ 64) (hir3 : idx' + (resolved + 1) ≤ s3.core.trail_end)
    (htc2_pos : 0 < tc2) (htc2_eq' : tc2 = (Full.fullCurTrailIdxs s2.core mrk2 idx').length)
    (htl2_1 : 1 ≤ tl2) (htl2_cv' : tl2 ≤ s2.core.cur_vars)
    (hlow2 : Full.FullLowerInv c s2.core tmp2 mrk2 tl2)
    (hmcov2 : Full.FullMarksCov s2.core tmp2 mrk2 tl2)
    (hent2 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (Full.fullActiveResolvent s2.core tmp2 mrk2 tl2 idx')))
    (hlen2 : s2.LengthsOk c) (hw_s2 : Full.FullWitnessCutInv c F0 F_cur cut_cur s2.core)
    (hws2_s3 : s3.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd_s2 : Full.FullArenaVarsNodup s2)
    (hlen_s3 : s3.LengthsOk c) (hw_s3 : Full.FullWitnessCutInv c F0 F_cur cut_cur s3.core)
    (hcov_s3 : Full.FullAnaMarksCov c s3) (hext_s3 : Full.FullExtScratchPres s s3)
    (hnd_s3 : Full.FullArenaVarsNodup s3)
    (hrefs_s3 : Full.fullArenaClauseRefs s3 = Full.fullArenaClauseRefs s)
    (hstat_s3 : Full.FullDeduceStaticEq s.core s3.core)
    (hs3_hw_eq : s3.core = s2.core) (hs3_mrk_eq : s2.core.mrk = mrk2)
    (hs3_tmp_eq : s2.core.tmp = tmp2) (hs3_tl_eq : s2.core.tmp_len = tl2)
    (hs3_tc_eq : s2.core.tmp_cnt = tc2) (hs3_ant_eq : s3.scratch.ant_sz = sc2.ant_sz)
    (hs3_res_eq : s3.scratch.res_sz = BitVec.ofNat 64 ((tl2 - 1) + tc2))
    (hs3_res_lt_ant : s3.scratch.res_sz.ult sc2.ant_sz = true)
    (hp_get_s2 : (s2.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hr_get_s2 : s2.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hpl_s3 : (s3.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s3.core.cur_level)
    (hp_lt_s3 : p_bv.toNat < 2 * s3.core.cur_vars)
    (hiu_cut : idx' < cut_cur) (hte_s3 : idx' < s3.core.trail_end)
    (hok_ne : rsn ≠ 0xFFFFFFFF#32) (hrsn_lg : (rsn &&& 0x80000000#32) = 0#32)
    (href_s2 : rsn.toNat ∈ Full.fullArenaClauseRefs s2)
    (hng_s2 : Full.fullArenaClauseGarb s2 rsn.toNat = false)
    (hall_mrk : ∀ l ∈ Full.fullRsnLits sl2 rsn, l / 2 ≠ p_bv.toNat / 2 →
      0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat → mrk2[l / 2]?.getD 0#8 ≠ 0#8)
    (heq_s2 : Full.fullArenaClauseLits s2 rsn.toNat = Full.fullRsnLits sl2 rsn)
    (hant_s2 : sc2.ant_sz = BitVec.ofNat 64 ((Full.fullRsnLits s2 rsn).countP fun l =>
      decide (l / 2 < s2.core.cur_vars ∧ 0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s2.core.lvl[l / 2]?.getD 0#32).toNat ≤ s2.core.cur_level)))
    (hzero_b : resolved = 0 →
      cut = cut ∧ idx' < cut ∧ (s.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat ∧
      s.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn ∧
      rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) = 0#32 ∧
      sl.core.confl_type = s.core.confl_type ∧ sl.core.confl_ref = s.core.confl_ref)
    (hconfl_eq : s3.core.confl_type = sl.core.confl_type ∧ s3.core.confl_ref = sl.core.confl_ref)
    (hm3 : (FullMem c s3 ⋆ R) m3) :
    wp (rs := [i64]) Γ Q X
      (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 528, ())) fun p58 => .load i64
        (Arg.var p58.fst) fun ld20 => .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 176, ()))
        fun p59 => .load i64 (Arg.var p59.fst) fun ld21 => .group (sig := [[]])
        (fun _Js3 => .cons (fun _ => .jump Js ()) .nil) fun JsIn => .let_ (Op.mk (.add i64)
        (Arg.var c.hdr, Arg.imm 1136, ())) fun p60 => .load i64 (Arg.var p60.fst) fun ld22 =>
      .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld22, Arg.imm 3#64, ())) fun p61 =>
      .jnz (Arg.var p61.fst)
        (.call (rs := [i64]) (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_bin"
          (Arg.var c.hdr, Arg.var rsn, Arg.var p_bv, ()) fun p62 =>
        .jnz (Arg.var p62.fst)
          (.group (sig := [[]]) (fun _Js4 => .cons (fun _ =>
            .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272#64, ())) fun p1 => .load i64
              (Arg.var p1.fst) fun ld => .let_ (Op.mk (.add i64)
              (Arg.var c.hdr, Arg.imm 1144#64, ())) fun p2 => .store (Arg.var ld)
              (Arg.var p2.fst) (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana"
              (Arg.var c.hdr, ()) fun _ => .ret (Arg.imm 2#64, ()))) .nil) fun Js4 =>
          .let_ (Op.mk (.cmp .eq i64 .bool rfl)
            (Arg.var (BitVec.ofNat 64 resolved + 1#64), Arg.imm 1#64, ())) fun p66 =>
          .jnz (Arg.var p66.fst) (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ()))
            fun p67 => .load i64 (Arg.var p67.fst) fun ld23 => .let_ (Op.mk (.cmp .ult i64 .bool
            rfl) (Arg.var ld23, Arg.var init_res_sz, ())) fun p68 => .jnz (Arg.var p68.fst)
              (.call (rs := [i64]) (as := [i64, i32, i64, i64, .bool]) (bs := [])
                "full_otfs_subsume"
                (Arg.var c.hdr, Arg.imm 0#32, Arg.var ld20, Arg.var ld21, Arg.imm true, ())
                fun _ => .jump Js4.fst ()) (.jump Js4.fst ())) (.jump Js4.fst ()))
          (.jump JsIn.fst ()))
        (.call (rs := [i64]) (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_large"
          (Arg.var c.hdr, Arg.var rsn, Arg.var p_bv, ()) fun p62 =>
        .jnz (Arg.var p62.fst)
          (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 528, ())) fun p63 =>
          .store (Arg.imm (t := i64) 2#64) (Arg.var p63.fst)
          (.let_ (Op.mk (.zext 32 64) (Arg.var rsn, ())) fun p64 => .let_ (Op.mk (.add i64)
            (Arg.var c.hdr, Arg.imm 176, ())) fun p65 => .store (Arg.var p64.fst)
            (Arg.var p65.fst)
          (.group (sig := [[]]) (fun _Js4 => .cons (fun _ =>
            .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272#64, ())) fun p1 => .load i64
              (Arg.var p1.fst) fun ld => .let_ (Op.mk (.add i64)
              (Arg.var c.hdr, Arg.imm 1144#64, ())) fun p2 => .store (Arg.var ld)
              (Arg.var p2.fst) (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana"
              (Arg.var c.hdr, ()) fun _ => .ret (Arg.imm 2#64, ()))) .nil) fun Js4 =>
          .let_ (Op.mk (.cmp .eq i64 .bool rfl)
            (Arg.var (BitVec.ofNat 64 resolved + 1#64), Arg.imm 1#64, ())) fun p66 =>
          .jnz (Arg.var p66.fst) (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ()))
            fun p67 => .load i64 (Arg.var p67.fst) fun ld23 => .let_ (Op.mk (.cmp .ult i64 .bool
            rfl) (Arg.var ld23, Arg.var init_res_sz, ())) fun p68 => .jnz (Arg.var p68.fst)
              (.call (rs := [i64]) (as := [i64, i32, i64, i64, .bool]) (bs := [])
                "full_otfs_subsume"
                (Arg.var c.hdr, Arg.var rsn, Arg.var ld20, Arg.var ld21, Arg.imm false, ())
                fun _ => .jump Js4.fst ()) (.jump Js4.fst ())) (.jump Js4.fst ()))))
          (.jump JsIn.fst ()))) m3 := by
  have hcl_s3_pos : 0 < s3.core.cur_level := by rw [hstat_s3.cl]; exact hcur_pos
  have hall_s3 : ∀ l ∈ Full.fullArenaClauseLitsCore s3.core rsn.toNat,
      l / 2 ≠ p_bv.toNat / 2 → 0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat →
      mrk2[l / 2]?.getD 0#8 ≠ 0#8 := fun l hl hne hpos => by
    have hl_sl2 : l ∈ Full.fullRsnLits sl2 rsn := by
      rw [← heq_s2]; unfold Full.fullArenaClauseLits; rw [← hs3_hw_eq]; exact hl
    exact hall_mrk l hl_sl2 hne (by rw [← hs3_hw_eq]; exact hpos)
  have hlt_s2_arr : tl2 ≤ s2.core.tmp.length := by
    rw [hlen2.core_ok.tmp_len_arr]; exact Nat.le_trans htl2_cv' hlen2.core_ok.cur_vars_le
  fa_fast_steps_nogrp
  refine wp_join_group (ts := []) (fun () ml => ∃ cut_n s_n,
      idx' + (resolved + 1) ≤ s_n.core.trail_end ∧
      Full.FullDeduceStateInv c F0 F_cur cut_n idx' s s_n ∧ 0 < s_n.core.tmp_cnt ∧
      (FullMem c s_n ⋆ R) ml) (fun _ ⟨⟩ ml h => hJot ml h) ?_
  intro J_in hJin
  have htc2' : tc2 = (Full.fullCurTrailIdxs s2.core s2.core.mrk idx').length := by
    rw [hs3_mrk_eq]; exact htc2_eq'
  have hlow2'' : Full.FullLowerInv c s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len := by
    rw [hs3_tmp_eq, hs3_mrk_eq, hs3_tl_eq]; exact hlow2
  have hmcov2'' : Full.FullMarksCov s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len := by
    rw [hs3_tmp_eq, hs3_mrk_eq, hs3_tl_eq]; exact hmcov2
  have hent2'' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (Full.fullActiveResolvent s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len
        idx')) := by rw [hs3_tmp_eq, hs3_mrk_eq, hs3_tl_eq]; exact hent2
  have href_s3 : rsn.toNat ∈ Full.fullArenaClauseRefs s3 := by
    change rsn.toNat ∈ Full.fullArenaClauseRefsCore s3.core; rw [hs3_hw_eq]; exact href_s2
  have hng_s3 : Full.fullArenaClauseGarb s3 rsn.toNat = false := by
    change Full.fullArenaClauseGarbCore s3.core rsn.toNat = false; rw [hs3_hw_eq]; exact hng_s2
  have hp_get_s3 : (s3.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat := by
    rw [hs3_hw_eq]; exact hp_get_s2
  have hr_get_s3 : s3.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
    rw [hs3_hw_eq]; exact hr_get_s2
  fa_fast_steps_nogrp
  · have hant3 : s3.scratch.ant_sz = 3#64 := by assumption
    have hbin_ent := Full.otfs_entails_bin_of_res_lt_ant hw_s2 hnd_s2 hlen2 htl2_1 htl2_cv'
      hlt_s2_arr (hs3_tl_eq ▸ hlow2'') (hs3_tl_eq ▸ hmcov2'') htc2' (hs3_tl_eq ▸ hent2'')
      hiu_cut (hs3_hw_eq ▸ hte_s3) hp_get_s2 hr_get_s2 (hs3_hw_eq ▸ hpl_s3)
      (hs3_hw_eq ▸ hcl_s3_pos) hok_ne hrsn_lg (fun l hl hne hpos => by
        rw [hs3_mrk_eq]; exact hall_s3 l (hs3_hw_eq ▸ hl) hne (hs3_hw_eq ▸ hpos))
      hs3_res_eq hant_s2 hs3_res_lt_ant (hs3_ant_eq.symm.trans hant3)
    have hbin_ent3 : ∀ f0 f1 : BitVec 32,
        f0.toNat ∈ Full.fullArenaClauseLits s3 rsn.toNat →
        f1.toNat ∈ Full.fullArenaClauseLits s3 rsn.toNat →
        f0 ≠ p_bv → f1 ≠ p_bv → f0 ≠ f1 →
        0 < (s3.core.lvl[f0.toNat / 2]?.getD 0#32).toNat →
        0 < (s3.core.lvl[f1.toNat / 2]?.getD 0#32).toNat →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat]) := by
      simpa only [Full.fullArenaClauseLits, hs3_hw_eq] using hbin_ent
    refine wp_call_of_spec _ _ (hOtfsBin (c.hdr, rsn, p_bv, ()) _ _ _
      ⟨c, F0, F_cur, cut_cur, idx', s3, R, rfl, hlen_s3, hw_s3, hnd_s3,
       hstat_s3.dm.trans hdm0, href_s3, hng_s3, hp_lt_s3, hiu_cut,
       hp_get_s3, hr_get_s3, hpl_s3, hbin_ent3, hm3, ?_⟩)
    intro ok_b ar_b ag_b wv_b ws_b wl_b wu_b nb_b ct_b cr_b c0_b c1_b oom_b sc_b m_b _
      hlen_b hw_b hnd_b hext_b hws1_b hws2_b hres_b hrefs_b hok_b hm_b
    let s_b : FullState :=
      { s3 with
        core := { s3.core with
          arena := ar_b, arena_garbage := ag_b, wvec := wv_b, wstk := ws_b, wlen := wl_b,
          wusable := wu_b, num_binary := nb_b, confl_type := ct_b, confl_ref := cr_b,
          confl_lit0 := c0_b, confl_lit1 := c1_b, oom := oom_b }
        scratch := sc_b }
    have hcov_b := s6a_anaMarksCov_of_same (s2 := s_b) hcov_s3 rfl rfl rfl hws1_b
    have hext_sb := Full.fullExtScratchPres_trans hext_s3 hext_b
    have hrefs_sb : Full.fullArenaClauseRefs s_b = Full.fullArenaClauseRefs s :=
      hrefs_b.trans hrefs_s3
    cases ok_b with
    | true =>
      obtain ⟨hct_b, hconfl_b⟩ := hok_b rfl; fa_fast_steps_nogrp
      refine s6a_deduce_otfs_ret2_subsume_wp (init_res_sz := init_res_sz)
        (old_ct := s3.core.confl_type) (old_cr := s3.core.confl_ref)
        (p := p_bv) (rsn := rsn) (new_confl_arg := Arg.imm 0#32) (to_bin := true)
        hClear hOtfsSub hQ hw0 hconfl0 hext0 hdm0 hm0_lm hlen_b hw_b hcov_b hext_sb
        (hws2_b.trans hws2_s3) hnd_b hrefs_sb hstat_s3.repack hconfl_b hte_s3 hres1_lt64
        (fun _ => hct_b) (fun hr0 => by
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hzero_b hr0
          exact ⟨h1, h2, h3, h4, h5, h6, hconfl_eq.1.trans h7, hconfl_eq.2.trans h8,
            fun hc => by cases hc⟩) hm_b
    | false =>
      fa_fast_steps
      refine hJin () m_b ⟨idx', s_b, hir3,
        s6a_deduce_otfs_loop_inv hlen_b hw_b hcov_b hext_sb (hws2_b.trans hws2_s3) hnd_b hrefs_sb
          hstat_s3.repack (hres_b.trans hs3_res_eq) hs3_hw_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl hs3_mrk_eq hs3_tmp_eq hs3_tl_eq hs3_tc_eq htc2_eq' htl2_1 htl2_cv' hlow2 hmcov2 hent2,
        ((congrArg FullCoreState.tmp_cnt hs3_hw_eq).trans hs3_tc_eq) ▸ htc2_pos, hm_b⟩
  · have hlarge_ent := Full.otfs_entails_large_of_res_lt_ant hw_s2 hnd_s2 hlen2 htl2_1 hlt_s2_arr
      (hs3_tl_eq ▸ hlow2'') (hs3_tl_eq ▸ hmcov2'') htc2' (hs3_tl_eq ▸ hent2'') hiu_cut
      (hs3_hw_eq ▸ hte_s3) hp_get_s2 hr_get_s2 (hs3_hw_eq ▸ hpl_s3) (hs3_hw_eq ▸ hcl_s3_pos)
      hok_ne hrsn_lg (fun l hl hne hpos => by
        rw [hs3_mrk_eq]; exact hall_s3 l (hs3_hw_eq ▸ hl) hne (hs3_hw_eq ▸ hpos))
      hs3_res_eq hant_s2 hs3_res_lt_ant
    have hlarge_ent3 : (cnfOfClauses F_cur).EntailsClause (cnfClause (List.filter (fun l =>
        decide (l ≠ p_bv.toNat ∧ (0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s3.core.arena[rsn.toNat + 3]?.getD 0#32).toNat ∨
          l = (s3.core.arena[rsn.toNat + 4]?.getD 0#32).toNat)))
        (Full.fullArenaClauseLits s3 rsn.toNat))) := by
      simpa only [Full.fullArenaClauseLits, hs3_hw_eq] using hlarge_ent
    refine wp_call_of_spec _ _ (hOtfsLarge (c.hdr, rsn, p_bv, ()) _ _ _
      ⟨c, F0, F_cur, cut_cur, idx', s3, R, rfl, hlen_s3, hw_s3, hnd_s3,
       hstat_s3.dm.trans hdm0, href_s3, hng_s3, hp_lt_s3, hiu_cut,
       hp_get_s3, hr_get_s3, hpl_s3, hlarge_ent3, hm3, ?_⟩)
    intro ok_l fl_l ar_l wv_l ws_l wl_l wu_l oom_l sc_l m_l _ hlen_l hw_l hnd_l hext_l
      hws1_l hws2_l hres_l hrefs_l hok_l hm_l
    let s_l : FullState :=
      { s3 with
        core := { s3.core with
          flags := fl_l, arena := ar_l, wvec := wv_l, wstk := ws_l,
          wlen := wl_l, wusable := wu_l, oom := oom_l }
        scratch := sc_l }
    have hcov_l' := s6a_anaMarksCov_of_same (s2 := s_l) hcov_s3 rfl rfl rfl hws1_l
    have hext_sl := Full.fullExtScratchPres_trans hext_s3 hext_l
    have hrefs_sl : Full.fullArenaClauseRefs s_l = Full.fullArenaClauseRefs s :=
      hrefs_l.trans hrefs_s3
    cases ok_l with
    | true =>
      obtain ⟨href_l, hng_l, hlits_l⟩ := hok_l rfl; fa_fast_steps_nogrp
      let s_ot : FullState :=
        { s_l with core := { s_l.core with confl_type := 2#64, confl_ref := rsn.setWidth 64 } }
      have hlen_ot : s_ot.LengthsOk c := ⟨{ hlen_l.core_ok with }, hlen_l.scratch_ok⟩
      have hw_ot : Full.FullWitnessCutInv c F0 F_cur idx' s_ot.core :=
        s6a_cut_with_confl hw_l 2#64 (rsn.setWidth 64)
      have hconfl_ot : Full.FullConflictOkCut F_cur idx' s_ot :=
        Full.deduce_large_conflOk_of href_l hng_l hlits_l
      refine s6a_deduce_otfs_ret2_subsume_wp (init_res_sz := init_res_sz)
        (old_ct := s3.core.confl_type) (old_cr := s3.core.confl_ref)
        (p := p_bv) (rsn := rsn) (new_confl_arg := Arg.var rsn) (to_bin := false)
        hClear hOtfsSub hQ hw0 hconfl0 hext0 hdm0 hm0_lm hlen_ot hw_ot hcov_l' hext_sl
        (hws2_l.trans hws2_s3) hnd_l hrefs_sl hstat_s3.repack hconfl_ot hte_s3 hres1_lt64
        (fun h => by cases h) (fun hr0 => by
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hzero_b hr0
          have hz : (rsn.setWidth 64).toNat = rsn.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans rsn.isLt (by decide))]
          exact ⟨h1, h2, h3, h4, h5, h6, hconfl_eq.1.trans h7, hconfl_eq.2.trans h8,
            fun _ => ⟨href_l, rfl, hz⟩⟩) ?_
      simpa only [s_ot, s_l, hconfl_eq.1, hconfl_eq.2] using (by assumption : (FullMem c _ ⋆ R) _)
    | false =>
      fa_fast_steps
      refine hJin () m_l ⟨idx', s_l, hir3,
        s6a_deduce_otfs_loop_inv hlen_l hw_l hcov_l' hext_sl (hws2_l.trans hws2_s3) hnd_l hrefs_sl
          hstat_s3.repack (hres_l.trans hs3_res_eq) hs3_hw_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl hs3_mrk_eq hs3_tmp_eq hs3_tl_eq hs3_tc_eq htc2_eq' htl2_1 htl2_cv' hlow2 hmcov2 hent2,
        ((congrArg FullCoreState.tmp_cnt hs3_hw_eq).trans hs3_tc_eq) ▸ htc2_pos, hm_l⟩

/-! ## 2. `full_elim_bve_m6_step13_wp` (`step13BveHeapPushSpec`) -/

private theorem s6a_watchLayout_of_denseInv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : WatchStackLayout s.core := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  have hw := hdw.2.1.watches
  unfold ModeWatchesInv at hw
  rw [ite_eq_right hdw.2.2.2.2.2.2] at hw
  exact hw.layout

private theorem s6a_denseInv_with_ws1_ss {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {ws1' : List (BitVec 32)} {ss' : List (BitVec 64)}
    (hws1 : ws1'.length = 2 * c.max_vars) (hss : ss'.length = c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  let sc' : FullScratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' }
  exact (m6_fullDenseInvW_with_scratch hdw (sc' := sc')
    { hdw.1.scratch_ok with work_stk1_len := hws1, sim_sig_len := hss } rfl rfl).toDense

private theorem s6a_elim_bve_post_loop_wp (Γ : Env)
    {c : FullCfg} {F0 : CNF Nat} {s0 sb : FullState} {R : Mem 64 → Prop}
    {Q : Post [i64]} {X : XPost} {mb : Mem 64} {hl_b : BitVec 64} {lre_b : Bool}
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → TmkZero s' → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hdenb : FullDenseInv c F0 sb) (htmkb : TmkZero sb)
    (hfub : sb.core.fuel.toNat ≤ s0.core.fuel.toNat) (hmb : (FullMem c sb ⋆ R) mb) :
    wp (rs := [i64]) Γ Q X
      (.group (sig := [[]]) (fun _Jf => .cons (fun _ => .group (sig := [[i64]])
        (fun _Jr => .cons (fun r => .ret (Arg.var r.fst, ())) .nil)
        fun Jr => .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) fun p =>
        .load i64 (Arg.var p.fst) fun ld => .let_ (Op.mk (.cmp .ne i64 .bool rfl)
          (Arg.var ld, Arg.imm 0, ())) fun p => .jnz (Arg.var p.fst)
          (.jump Jr.fst (Arg.imm 20, ())) (.jump Jr.fst (Arg.imm 1, ()))) .nil)
      fun Jf => .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) fun p1 =>
        .load i64 (Arg.var p1.fst) fun ld => .let_ (Op.mk (.cmp .eq i64 .bool rfl)
          (Arg.var ld, Arg.imm 0, ())) fun p2 => .jnz (Arg.var p2.fst)
          (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p3 =>
            .load i64 (Arg.var p3.fst) fun ld => .group (sig := [[.bool]])
              (fun _ => .cons (fun pc =>
              .group (sig := [[]]) (fun _ => .cons (fun _ => .jump Jf.fst ()) .nil) fun Jc =>
                .jnz (Arg.var pc.fst) (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1008, ()))
                fun p => .load i64 (Arg.var p.fst) fun ld1 => .group (sig := [[]])
                (fun _ => .cons (fun _ => .jump Jc.fst ()) .nil) fun Jn => .let_ (Op.mk (.cmp .ult
                i64 .bool rfl) (Arg.var ld1, Arg.imm 16, ())) fun p => .jnz (Arg.var p.fst)
                (.group (sig := [[i64]]) (fun _ => .cons (fun pn => .group (sig := [[i64]])
                (fun _ => .cons (fun pnb => .let_ (Op.mk (.add i64)
                  (Arg.var c.hdr, Arg.imm 1008, ())) fun p4 => .store (Arg.var pnb.fst)
                  (Arg.var p4.fst) (.group (sig := [[i64]]) (fun Js4 => .cons (fun pk =>
                  .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var pk.fst, Arg.var ld, ()))
                  fun p5 => .jnz (Arg.var p5.fst) (.let_ (Op.mk (.mul i64) (Arg.var pk.fst,
                  Arg.imm 4, ())) fun p6 => .let_ (Op.mk (.add i64) (Arg.var c.pFlags,
                  Arg.var p6.fst, ())) fun p7 => .let_ (Op.mk (.mul i64) (Arg.var pk.fst,
                  Arg.imm 4, ())) fun p8 => .let_ (Op.mk (.add i64) (Arg.var c.pFlags,
                  Arg.var p8.fst, ())) fun p9 => .load i32 (Arg.var p9.fst) fun ldf =>
                  .let_ (Op.mk (.or i32) (Arg.var ldf, Arg.imm 16, ())) fun p10 =>
                  .store (Arg.var p10.fst) (Arg.var p7.fst) (.let_ (Op.mk (.add i64)
                  (Arg.var pk.fst, Arg.imm 1, ())) fun pk1 => .jump Js4.fst (Arg.var pk1.fst,
                  ()))) (.jump Jn.fst ())) .nil) fun Js4 => .jump Js4.fst (Arg.imm 0, ()))) .nil)
                fun Jb2 => .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var pn.fst, Arg.imm 16, ()))
                  fun p4 => .jnz (Arg.var p4.fst) (.jump Jb2.fst (Arg.imm 16, ()))
                  (.jump Jb2.fst (Arg.var pn.fst, ()))) .nil) fun Jb0 => .let_ (Op.mk (.cmp .eq
                  i64 .bool rfl) (Arg.var ld1, Arg.imm 0, ())) fun p => .jnz (Arg.var p.fst)
                  (.jump Jb0.fst (Arg.imm 1, ())) (.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ()))
                  fun ps => .let_ (Op.mk (.shl i64) (Arg.var ld1, Arg.var ps.fst, ())) fun psh =>
                  .jump Jb0.fst (Arg.var psh.fst, ()))) (.jump Jn.fst ())) (.group (sig := [[i64]])
                  (fun Js2 => .cons (fun pk => .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                  (Arg.var pk.fst, Arg.var ld, ())) fun p4 => .jnz (Arg.var p4.fst) (.let_ (Op.mk
                  (.mul i64) (Arg.var pk.fst, Arg.imm 4, ())) fun p5 => .let_ (Op.mk (.add i64)
                  (Arg.var c.pFlags, Arg.var p5.fst, ())) fun p6 => .let_ (Op.mk (.mul i64)
                  (Arg.var pk.fst, Arg.imm 4, ())) fun p7 => .let_ (Op.mk (.add i64)
                  (Arg.var c.pFlags, Arg.var p7.fst, ())) fun p8 => .load i32 (Arg.var p8.fst)
                  fun ldf => .let_ (Op.mk (.not i32) (Arg.imm 16, ())) fun p9 => .let_ (Op.mk
                  (.and i32) (Arg.var ldf, Arg.var p9.fst, ())) fun p10 => .store (Arg.var p10.fst)
                  (Arg.var p6.fst) (.let_ (Op.mk (.add i64) (Arg.var pk.fst, Arg.imm 1, ()))
                  fun pk1 => .jump Js2.fst (Arg.var pk1.fst, ()))) (.jump Jc.fst ())) .nil)
                  fun Js2 => .jump Js2.fst (Arg.imm 0, ()))) .nil) fun Jc => .let_ (Op.mk (.cmp .eq
                  i64 .bool rfl) (Arg.var hl_b, Arg.imm 0, ())) fun p4 => .jnz (Arg.var p4.fst)
                  (.jnz (Arg.var lre_b) (.jump Jc.fst (Arg.imm false, ())) (.let_ (Op.mk (.add i64)
                  (Arg.var c.hdr, Arg.imm 760, ())) fun p => .load i64 (Arg.var p.fst) fun ldo =>
                  .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ldo, Arg.imm 0, ())) fun p =>
                  .jnz (Arg.var p.fst) (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 168, ()))
                  fun p => .load i64 (Arg.var p.fst) fun ldf => .let_ (Op.mk (.cmp .ugt i64 .bool
                  rfl) (Arg.var ldf, Arg.imm 0, ())) fun p => .jnz (Arg.var p.fst) (.jump Jc.fst
                  (Arg.imm true, ())) (.jump Jc.fst (Arg.imm false, ()))) (.jump Jc.fst (Arg.imm
                  false, ())))) (.jump Jc.fst (Arg.imm false, ()))) (.jump Jf.fst ())) mb := by
  c0_hsteps_nogrp
  refine wp_join0 (P := fun mf => ∃ sf : FullState,
    FullDenseInv c F0 sf ∧ TmkZero sf ∧ sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
    (FullMem c sf ⋆ R) mf)
    (fun _ mf ⟨sf, hdenf, htmkf, hfuf, hmf⟩ => by
      c0_hsteps!
      · exact hQ 20#64 sf mf hdenf htmkf hfuf (Or.inr rfl)
          (fun _ => hdenf.inconsistent_unsat hc) hmf
      · exact hQ 1#64 sf mf hdenf htmkf hfuf (Or.inl rfl) (fun h => by cases h) hmf)
    (fun Jf hJf => by
      c0_hsplit
      · have hmx := c.hmaxv; unfold dimacsBound at hmx
        have hcvb := hdenb.lengths.core_ok.cur_vars_le; have hflb := hdenb.lengths.core_ok.flags_len
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
          (fun _ comp _ => by
            c0_hsteps_nogrp
            refine wp_join0 (P := fun mj => ∃ sj : FullState, FullDenseInv c F0 sj ∧
                TmkZero sj ∧ sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj)
              (fun _ mj h => by c0_hsteps!; exact hJf mj h)
              (fun _ hJc => by
                c0_hsplit
                · c0_hsteps_nogrp
                  refine wp_join0 (P := fun mj => ∃ sj : FullState, FullDenseInv c F0 sj ∧
                      TmkZero sj ∧ sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                      (FullMem c sj ⋆ R) mj)
                    (fun _ mj h => by c0_hsteps!; exact hJc mj h)
                    (fun _ hJc2 => by
                      c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                          (fun x => (x, ())) (fun _ => True) (fun _ nb0 _ => by
                            c0_hsteps_nogrp
                            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                              (fun x => (x, ())) (fun _ => True) (fun _ nb _ => by
                                c0_hsteps_nogrp
                                let sb1 : FullState :=
                                  { sb with scratch := { sb.scratch with elim_bound := nb } }
                                have hden1 : FullDenseInv c F0 sb1 :=
                                  fullDenseInv_with_scratch_keep hdenb
                                    { hdenb.lengths.scratch_ok with
                                      walk_vals_len := hdenb.lengths.scratch_ok.walk_vals_len }
                                    rfl rfl
                                refine wp_loop_group (ts := [i64]) (fun rem_k (k, ()) mk =>
                                    ∃ flk : List (BitVec 32), flk.length = c.max_vars ∧
                                      k.toNat ≤ sb.core.cur_vars ∧
                                      rem_k = sb.core.cur_vars - k.toNat ∧
                                      (FullMem c { sb1 with
                                        core := { sb1.core with flags := flk } } ⋆ R) mk) ?_ ?_
                                · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk ⟨flk, hflk, hk_le, rfl, hmk⟩
                                  c0_hsplit
                                  · have hk_lt : k.toNat < sb.core.cur_vars := by
                                      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                    have hk_b : k.toNat < flk.length := by omega
                                    have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                                    c0_hsteps!
                                    exact hLk (sb.core.cur_vars - (k + 1#64).toNat) (k + 1#64, ()) _
                                      (by omega) ⟨_, by simp [hflk], by omega, rfl, hm⟩
                                  · c0_hsteps!
                                    let sf : FullState :=
                                      { sb1 with core := { sb1.core with flags := flk } }
                                    exact hJc2 mk ⟨sf, fullDenseInv_with_flags hden1 hflk,
                                      htmkb.congr rfl rfl, hfub, hmk⟩
                                · intro Lk hLk; c0_hsteps!
                                  exact hLk sb.core.cur_vars (0#64, ()) _
                                    ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hm⟩)
                              (fun Jm hJm => by c0_hsplit <;> (c0_hsteps!; exact hJm _ trivial)))
                          (fun Jb hJb => by c0_hsplit <;> (c0_hsteps!; exact hJb _ trivial))
                      · c0_hsteps!; exact hJc2 mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)
                · c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i64]) (fun rem_k (k, ()) mk =>
                      ∃ flk : List (BitVec 32), flk.length = c.max_vars ∧
                        k.toNat ≤ sb.core.cur_vars ∧ rem_k = sb.core.cur_vars - k.toNat ∧
                        (FullMem c { sb with core := { sb.core with flags := flk } } ⋆ R) mk)
                    ?_ ?_
                  · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk ⟨flk, hflk, hk_le, rfl, hmk⟩
                    c0_hsplit
                    · have hk_lt : k.toNat < sb.core.cur_vars := by
                        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                      have hk_b : k.toNat < flk.length := by omega
                      have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                      c0_hsteps!
                      exact hLk (sb.core.cur_vars - (k + 1#64).toNat) (k + 1#64, ()) _ (by omega)
                        ⟨_, by simp [hflk], by omega, rfl, hm⟩
                    · c0_hsteps!
                      let sf : FullState := { sb with core := { sb.core with flags := flk } }
                      exact hJc mk ⟨sf, fullDenseInv_with_flags hdenb hflk, htmkb.congr rfl rfl,
                        hfub, hmk⟩
                  · intro Lk hLk; c0_hsteps!
                    exact hLk sb.core.cur_vars (0#64, ()) mb
                      ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hmb⟩))
          (fun Jc hJc => by c0_hsteps! <;> exact hJc _ trivial)
      · c0_hsteps!; exact hJf mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)

private theorem s6a_elim_bve_rearm_loop_wp (Γ : Env)
    (hPush : ∀ a m Q X, step13BveHeapPushSpec a m Q X →
      Γ "full_bve_heap_push_m6" [i64, i64, i32] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s0 s4 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]}
    {X : XPost} {m4 : Mem 64} {hl_dec1 nn : BitVec 64} {re_1 : Bool} {Jn : Cont [i64, .bool]}
    (hJn : ∀ (hl_f : BitVec 64) (re_f : Bool) (mf : Mem 64),
      (∃ sf : FullState, hl_f.toNat ≤ sf.core.cur_vars ∧ FullDenseInv c F0 sf ∧ TmkZero sf ∧
        sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf) →
      Jn (hl_f, re_f, ()) mf)
    (hhl4 : hl_dec1.toNat ≤ s4.core.cur_vars) (hnn_le : nn.toNat ≤ s4.core.cur_vars)
    (hden4 : FullDenseInv c F0 s4) (htmk4 : TmkZero s4)
    (hfu4 : s4.core.fuel.toNat ≤ s0.core.fuel.toNat) (hm4 : (FullMem c s4 ⋆ R) m4) :
    wp Γ Q X (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p4 =>
      .load i64 (Arg.var p4.fst) fun ld =>
        .group (sig := [[i64, i64]]) (fun Js3 => .cons (fun p5 =>
          .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p5.snd.fst, Arg.var nn, ())) fun p6 =>
          .jnz (Arg.var p6.fst)
            (.let_ (Op.mk (.mul i64) (Arg.var p5.snd.fst, Arg.imm 4, ())) fun p =>
            .let_ (Op.mk (.add i64) (Arg.var c.pWorkStk2, Arg.var p.fst, ())) fun p =>
            .load i32 (Arg.var p.fst) fun ld3 =>
            .group (sig := [[i64]]) (fun _ => .cons (fun p =>
              .let_ (Op.mk (.add i64) (Arg.var p5.snd.fst, Arg.imm 1, ())) fun p7 =>
              .jump Js3.fst (Arg.var p.fst, Arg.var p7.fst, ())) .nil)
            fun Js =>
              .let_ (Op.mk (.zext 32 64) (Arg.var ld3, ())) fun p =>
              .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p.fst, Arg.var ld, ())) fun p =>
              .jnz (Arg.var p.fst)
                (.let_ (Op.mk (.zext 32 64) (Arg.var ld3, ())) fun p =>
                .let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                .let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p.fst, ())) fun p =>
                .load i32 (Arg.var p.fst) fun ldf =>
                .let_ (Op.mk (.and i32) (Arg.var ldf, Arg.imm 1, ())) fun p =>
                .let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p.fst, Arg.imm 0, ())) fun p =>
                .jnz (Arg.var p.fst)
                  (.let_ (Op.mk (.zext 32 64) (Arg.var ld3, ())) fun p =>
                  .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun p7 =>
                  .let_ (Op.mk (.shl i64) (Arg.var p.fst, Arg.var p7.fst, ())) fun p =>
                  .let_ (Op.mk (.add i64) (Arg.var c.pVals, Arg.var p.fst, ())) fun p =>
                  .load i8 (Arg.var p.fst) fun ldv =>
                  .let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p =>
                  .let_ (Op.mk (.sext 8 32) (Arg.var ldv, ())) fun p8 =>
                  .let_ (Op.mk (.sext 8 32) (Arg.var p.fst, ())) fun p =>
                  .let_ (Op.mk (.cmp .eq i32 .bool rfl)
                      (Arg.var p8.fst, Arg.var p.fst, ())) fun p =>
                  .jnz (Arg.var p.fst)
                    (.let_ (Op.mk (.zext 32 64) (Arg.var ld3, ())) fun p =>
                    .let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                    .let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p.fst, ())) fun p =>
                    .let_ (Op.mk (.zext 32 64) (Arg.var ld3, ())) fun p9 =>
                    .let_ (Op.mk (.mul i64) (Arg.var p9.fst, Arg.imm 4, ())) fun p10 =>
                    .let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p10.fst, ())) fun p11 =>
                    .load i32 (Arg.var p11.fst) fun ldf2 =>
                    .let_ (Op.mk (.or i32) (Arg.var ldf2, Arg.imm 16, ())) fun p12 =>
                    .store (Arg.var p12.fst) (Arg.var p.fst)
                      (.call (rs := [i64]) (as := [i64, i64, i32]) (bs := [i64])
                        "full_bve_heap_push_m6" (Arg.var c.hdr, Arg.var p5.fst, Arg.var ld3, ())
                        fun p => .jump Js.fst (Arg.var p.fst, ())))
                    (.jump Js.fst (Arg.var p5.fst, ())))
                  (.jump Js.fst (Arg.var p5.fst, ())))
                (.jump Js.fst (Arg.var p5.fst, ())))
            (.jump Jn (Arg.var p5.fst, Arg.var re_1, ()))) .nil)
        fun Js => .jump Js.fst (Arg.var hl_dec1, Arg.imm 0, ())) m4 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64, i64])
    (fun rem_k (hl_k, k, ()) mk => ∃ sk : FullState,
      k.toNat ≤ nn.toNat ∧ rem_k = nn.toNat - k.toNat ∧ hl_k.toNat ≤ sk.core.cur_vars ∧
      sk.core.cur_vars = s4.core.cur_vars ∧ FullDenseInv c F0 sk ∧ TmkZero sk ∧
      sk.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sk ⋆ R) mk)
    ?_ ?_
  · rintro Lk rem_k ⟨hl_k, k, ⟨⟩⟩ mk hLk ⟨sk, hk_le, rfl, hhlk, hcvk, hdenk, htmkk, hfuk, hmk⟩
    have hlkl := hdenk.lengths
    have hcvk_le := hlkl.core_ok.cur_vars_le
    c0_hsplit
    · have hk_lt : k.toNat < nn.toNat := hc
      have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
      have hk_w : k.toNat < sk.scratch.work_stk2.length := by
        rw [hlkl.scratch_ok.work_stk2_len]; omega
      let uk := sk.scratch.work_stk2[k.toNat]'hk_w
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i64]) (α := BitVec 64 × FullState) (fun x => (x.1, ()))
        (fun x mj => x.1.toNat ≤ x.2.core.cur_vars ∧ x.2.core.cur_vars = s4.core.cur_vars ∧
          FullDenseInv c F0 x.2 ∧ TmkZero x.2 ∧ x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
          (FullMem c x.2 ⋆ R) mj)
        (fun _ ⟨hl_j, sj⟩ mj ⟨hhlj, hcvj, hdenj, htmkj, hfuj, hmj⟩ => by
          c0_hsteps!
          exact hLk (nn.toNat - (k + 1#64).toNat) (hl_j, k + 1#64, ()) mj (by omega)
            ⟨sj, by omega, rfl, hhlj, hcvj, hdenj, htmkj, hfuj, hmj⟩)
        (fun Jk hJk => by
          c0_hsplit
          · have huk_lt : uk.toNat < sk.core.cur_vars := by
              rw [← hcvk, Nat.mod_eq_of_lt (by omega : sk.core.cur_vars < 2 ^ 64)] at hc; exact hc
            have hflk_l := hlkl.core_ok.flags_len
            have huk_fl : (uk.setWidth 64).toNat < sk.core.flags.length := by
              rw [hflk_l, m6_zext32_toNat]; omega
            c0_hsplit
            · have huk_vl : (uk.setWidth 64 <<< (1 : Nat)).toNat < sk.core.vals.length := by
                rw [hlkl.core_ok.vals_len]; c0_bound
              c0_hsplit
              · c0_hsteps_nogrp
                let u64 := (uk.setWidth 64).toNat
                let fl_u := sk.core.flags.set u64 (sk.core.flags[u64]'huk_fl ||| 16#32)
                let su_k : FullState := { sk with core := { sk.core with flags := fl_u } }
                have hden_u := fullDenseInv_with_flags hdenk
                  (show fl_u.length = c.max_vars from (List.length_set ..).trans hflk_l)
                s6a_m6_call hPush
                refine ⟨c, su_k, R, rfl, hden_u.lengths, s6a_watchLayout_of_denseInv hden_u, hm, ?_⟩
                intro hl_p ws1p ssp mp_ hws1p hssp hhlp hmp_
                c0_hsteps!
                let s_pu : FullState :=
                  { su_k with scratch := { su_k.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                exact hJk (hl_p, s_pu) mp_
                  ⟨hhlp hhlk, hcvk, s6a_denseInv_with_ws1_ss hden_u hws1p hssp,
                    htmkk.congr rfl rfl, hfuk, hmp_⟩
              · c0_hsteps!; exact hJk (hl_k, sk) mk ⟨hhlk, hcvk, hdenk, htmkk, hfuk, hmk⟩
            · c0_hsteps!; exact hJk (hl_k, sk) mk ⟨hhlk, hcvk, hdenk, htmkk, hfuk, hmk⟩
          · c0_hsteps!; exact hJk (hl_k, sk) mk ⟨hhlk, hcvk, hdenk, htmkk, hfuk, hmk⟩)
    · c0_hsteps!; exact hJn hl_k re_1 mk ⟨sk, hhlk, hdenk, htmkk, hfuk, hmk⟩
  · intro Lk hLk; c0_hsteps!
    exact hLk nn.toNat (hl_dec1, 0#64, ()) m4
      ⟨s4, Nat.zero_le _, by simp, hhl4, rfl, hden4, htmk4, hfu4, hm4⟩

/-- Step-13 lift for `full_elim_bve_m6` over `step13BveHeapPushSpec`. -/
theorem full_elim_bve_m6_step13_wp (Γ : Env)
    (hFlush : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m6" [i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, step13BveHeapPushSpec a m Q X →
      Γ "full_bve_heap_push_m6" [i64, i64, i32] [i64] a m Q X)
    (hPop : ∀ a m Q X, fullBveHeapPopM6Spec a m Q X →
      Γ "full_bve_heap_pop_m6" [i64, i64] [i32] a m Q X)
    (hNbrs : ∀ a m Q X, m3ElimCollectNbrsSpec a m Q X →
      Γ "full_bve_collect_nbrs_m6" [i64, i32] [i64] a m Q X)
    (hBveVar : ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m6" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m3ElimBveSpec a m Q X → Func.wp Γ full_elim_bve_m6_body a m Q X := by
  rintro ⟨h, bve_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, htmk0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv0_le := hden0.lengths.core_ok.cur_vars_le
  have hmcl0 := hden0.lengths.core_ok.min_clr_len_arr
  unfold Func.wp full_elim_bve_m6_body; c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64]) (fun rem_c (ci, ()) mc => ∃ mclrc : List (BitVec 32),
      mclrc.length = c.max_vars ∧ ci.toNat ≤ s0.core.cur_vars ∧
      rem_c = s0.core.cur_vars - ci.toNat ∧
      (FullMem c { s0 with core := { s0.core with min_clr := mclrc } } ⋆ R) mc)
    ?_ (fun Lc hLc => by
      c0_hsteps!; exact hLc s0.core.cur_vars (0#64, ()) m0
        ⟨s0.core.min_clr, hmcl0, Nat.zero_le _, by simp, hm0⟩)
  rintro Lc rem_c ⟨ci, ⟨⟩⟩ mc hLc ⟨mclrc, hmclrc, hci_le, rfl, hmc⟩
  c0_hsplit
  · have hci_lt : ci.toNat < s0.core.cur_vars := by rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hmcl_b : ci.toNat < mclrc.length := by omega
    have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by c0_bound
    c0_hsteps!; exact hLc (s0.core.cur_vars - (ci + 1#64).toNat) (ci + 1#64, ()) _ (by omega)
      ⟨_, by simp [hmclrc], by omega, rfl, hm⟩
  let sz : FullState := { s0 with core := { s0.core with min_clr := mclrc } }
  have hdenz : FullDenseInv c F0 sz := by
    obtain ⟨F_cur, hw0⟩ := hden0.exists_witness
    exact FullDenseInvW.toDense ⟨⟨{ hw0.1.core_ok with min_clr_len_arr := hmclrc },
      hw0.1.scratch_ok⟩, fullWitnessInv_with_min_clr hw0.2.1 mclrc, hw0.2.2.1, hw0.2.2.2.1,
      hw0.2.2.2.2.1, hw0.2.2.2.2.2.1, hw0.2.2.2.2.2.2⟩
  have htmkz : TmkZero sz := htmk0.congr rfl rfl; c0_hsteps_nogrp
  refine wp_loop_break_group (brkTs := [i64, i64, .bool, i64]) (lpTs := [i64, i64, .bool, i64])
    (fun (_tr, _hl, _lre, _rd, ()) mb => ∃ sb : FullState, FullDenseInv c F0 sb ∧ TmkZero sb ∧
      sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sb ⋆ R) mb)
    (fun rem_r (tried, hlen, _lre, round, ()) mr => ∃ sr : FullState,
      round.toNat ≤ 16 ∧ rem_r = 16 - round.toNat ∧ tried.toNat ≤ bve_lim.toNat ∧
      hlen.toNat ≤ sr.core.cur_vars ∧ FullDenseInv c F0 sr ∧ TmkZero sr ∧
      sr.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sr ⋆ R) mr) ?_ ?_ ?_
  · rintro _ ⟨_tr, hl_b, lre_b, _rd, ⟨⟩⟩ mb ⟨sb, hdenb, htmkb, hfub, hmb⟩
    rw [Blocks.get_here]; try dsimp only
    exact s6a_elim_bve_post_loop_wp Γ hQ hdenb htmkb hfub hmb
  · rintro Br Lr rem_r ⟨tried, hlen, lre, round, ⟨⟩⟩ mr hBr hLr
      ⟨sr, hrd_le, rfl, htr_le, hhl_le, hdenr, htmkr, hfur, hmr⟩
    have hbrk_r := hBr (tried, hlen, lre, round, ()) mr ⟨sr, hdenr, htmkr, hfur, hmr⟩
    c0_hsplit
    · have hrd_lt : round.toNat < 16 := hc
      have hrd1 : (round + 1#64).toNat = round.toNat + 1 := by c0_bound
      c0_hsplit
      · have htr_lt : tried.toNat < bve_lim.toNat := hc
        c0_hsplit
        · c0_hsplit
          · c0_hsplit
            · c0_hsteps_nogrp; obtain ⟨F_cur, hdwr⟩ := hdenr.exists_witness
              s6a_m6_call hFlush; refine fullDenseFlushUnitsM6Spec_intro rfl hdwr hmr ?_
              intro ok_u su mu hdwu hcvu _ hfuu _ htmku _ _ _ _ _ hfu_uns hmu
              have hdenu : FullDenseInv c F0 su := hdwu.toDense
              have htmku' : TmkZero su := htmkr.congr hcvu htmku
              have hfuu' : su.core.fuel.toNat ≤ s0.core.fuel.toNat := by rw [hfuu]; exact hfur
              c0_hsplit
              · have hcvu_le := hdwu.1.core_ok.cur_vars_le
                have hws1u := hdwu.1.scratch_ok.work_stk1_len; c0_hsteps_nogrp
                refine wp_loop_group (ts := [i64]) (fun rem_i (i, ()) mi =>
                    ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
                      i.toNat ≤ su.core.cur_vars ∧ rem_i = su.core.cur_vars - i.toNat ∧
                      (FullMem c { su with scratch := { su.scratch with work_stk1 := ws1 } } ⋆ R)
                        mi) ?_ ?_
                · rintro Li rem_i ⟨i, ⟨⟩⟩ mi hLi ⟨ws1, hws1, hi_le, rfl, hmi⟩
                  c0_hsplit
                  · have hi_lt : i.toNat < su.core.cur_vars := by
                      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                    have hmv_i : (BitVec.ofNat 64 c.max_vars + i).toNat < ws1.length := by
                      rw [hws1]; c0_bound
                    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                    c0_hsteps!
                    exact hLi (su.core.cur_vars - (i + 1#64).toNat) (i + 1#64, ()) _ (by omega)
                      ⟨_, by simp [hws1], by omega, rfl, hm⟩
                  · let su1 : FullState :=
                      { su with scratch := { su.scratch with work_stk1 := ws1 } }
                    have hdenu1 : FullDenseInv c F0 su1 :=
                      s6a_denseInv_with_ws1_ss hdenu hws1 hdwu.1.scratch_ok.sim_sig_len
                    c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i64, i64])
                      (fun rem_p (hl_p, ip, ()) mp => ∃ ws1p ssp,
                        let sp : FullState := { su with scratch :=
                          { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                        ws1p.length = 2 * c.max_vars ∧ ssp.length = c.max_vars ∧
                        ip.toNat ≤ su.core.cur_vars ∧ rem_p = su.core.cur_vars - ip.toNat ∧
                        hl_p.toNat ≤ su.core.cur_vars ∧ (FullMem c sp ⋆ R) mp) ?_ ?_
                    · rintro Lp rem_p ⟨hl_p, ip, ⟨⟩⟩ mp hLp
                        ⟨ws1p, ssp, hws1p, hssp, hip_le, rfl, hhlp_le, hmp⟩
                      let sp : FullState := { su with scratch :=
                        { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                      c0_hsplit
                      · have hip_lt : ip.toNat < su.core.cur_vars := by
                          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                        have hip1 : (ip + 1#64).toNat = ip.toNat + 1 := by c0_bound
                        have hip_fl : ip.toNat < su.core.flags.length := by
                          rw [hdwu.1.core_ok.flags_len]; omega
                        have hip_vl : (ip <<< (1 : Nat)).toNat < su.core.vals.length := by
                          rw [hdwu.1.core_ok.vals_len]; c0_bound
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i64])
                          (α := BitVec 64 × List (BitVec 32) × List (BitVec 64))
                          (fun x => (x.1, ()))
                          (fun x mj => let sj : FullState := { su with scratch :=
                              { su.scratch with work_stk1 := x.2.1, sim_sig := x.2.2 } }
                            x.2.1.length = 2 * c.max_vars ∧ x.2.2.length = c.max_vars ∧
                            x.1.toNat ≤ su.core.cur_vars ∧ (FullMem c sj ⋆ R) mj)
                          (fun _ ⟨hl_j, ws1j, ssj⟩ mj ⟨hws1j, hssj, hhlj, hmj⟩ => by
                            c0_hsteps!
                            exact hLp (su.core.cur_vars - (ip + 1#64).toNat) (hl_j, ip + 1#64, ())
                              mj (by omega) ⟨ws1j, ssj, hws1j, hssj, by omega, rfl, hhlj, hmj⟩)
                          (fun Jp hJp => by
                            c0_hsplit
                            · c0_hsplit
                              · c0_hsteps_nogrp
                                have hden_sp := s6a_denseInv_with_ws1_ss hdenu hws1p hssp
                                s6a_m6_call hPush; refine ⟨c, sp, R, rfl, hden_sp.lengths,
                                  s6a_watchLayout_of_denseInv hden_sp, hmp, ?_⟩
                                intro hl_n ws1n ssn mn hws1n hssn hhln hmn; c0_hsteps!
                                exact hJp (hl_n, ws1n, ssn) mn ⟨hws1n, hssn, hhln hhlp_le, hmn⟩
                              · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                                  ⟨hws1p, hssp, hhlp_le, hmp⟩
                            · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                                ⟨hws1p, hssp, hhlp_le, hmp⟩)
                      · have hdensp := s6a_denseInv_with_ws1_ss hdenu hws1p hssp
                        have htmksp : TmkZero sp := htmku'.congr rfl rfl
                        c0_hsplit
                        · c0_hsteps!; exact hBr (tried, hl_p, false, round, ()) mp
                            ⟨sp, hdensp, htmksp, hfuu', hmp⟩
                        · c0_hsteps_nogrp
                          refine wp_loop_break_group (brkTs := [i64, i64, .bool])
                            (lpTs := [i64, i64, .bool])
                            (fun (tr_b, hl_b, re_b, ()) mb => ∃ sb : FullState,
                              tr_b.toNat ≤ bve_lim.toNat ∧ hl_b.toNat ≤ sb.core.cur_vars ∧
                              FullDenseInv c F0 sb ∧ TmkZero sb ∧
                              sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sb ⋆ R) mb)
                            (fun rem_h (tr_h, hl_h, re_h, ()) mh => ∃ sh : FullState,
                              tr_h.toNat ≤ bve_lim.toNat ∧ hl_h.toNat ≤ sh.core.cur_vars ∧
                              rem_h = (bve_lim.toNat - tr_h.toNat) * (c.max_vars + 1) +
                                hl_h.toNat ∧ FullDenseInv c F0 sh ∧ TmkZero sh ∧
                              sh.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sh ⋆ R) mh)
                            ?_ ?_ ?_
                          · rintro _ ⟨tr_b, hl_b, re_b, ⟨⟩⟩ mb
                              ⟨sb, htrb, hhlb, hdenb, htmkb, hfub, hmb⟩
                            c0_hsplit
                            · c0_hsteps!
                              exact hLr (16 - (round + 1#64).toNat)
                                (tr_b, hl_b, re_b, round + 1#64, ()) mb (by omega)
                                ⟨sb, by omega, rfl, htrb, hhlb, hdenb, htmkb, hfub, hmb⟩
                            · c0_hsteps!; exact hBr (tr_b, hl_b, re_b, round, ()) mb
                                ⟨sb, hdenb, htmkb, hfub, hmb⟩
                          · rintro Bh Lh rem_h ⟨tr_h, hl_h, re_h, ⟨⟩⟩ mh hBh hLh
                              ⟨sh, htrh, hhlh, rfl, hdenh, htmkh, hfuh, hmh⟩
                            have hbrk_h := hBh (tr_h, hl_h, re_h, ()) mh
                              ⟨sh, htrh, hhlh, hdenh, htmkh, hfuh, hmh⟩
                            c0_hsplit
                            · have hhl_pos : 0 < hl_h.toNat := hc
                              have hhl_dec : (hl_h - 1#64).toNat = hl_h.toNat - 1 := by c0_bound
                              c0_hsplit
                              · have htrh_lt : tr_h.toNat < bve_lim.toNat := hc
                                have htrh1 : (tr_h + 1#64).toNat = tr_h.toNat + 1 := by c0_bound
                                c0_hsplit
                                · c0_hsplit
                                  · c0_hsplit
                                    · c0_hsteps_nogrp; s6a_m6_call hPop
                                      refine fullBveHeapPopM6Spec_intro rfl hdenh.lengths hmh ?_
                                      intro v ws1_1 m1 hws1_1 hm1
                                      let s1 : FullState := { sh with scratch :=
                                        { sh.scratch with work_stk1 := ws1_1 } }
                                      have hden1 : FullDenseInv c F0 s1 :=
                                        s6a_denseInv_with_ws1_ss hdenh hws1_1
                                          hdenh.lengths.scratch_ok.sim_sig_len
                                      have htmk1 : TmkZero s1 := htmkh.congr rfl rfl
                                      have hcv1_le := hden1.lengths.core_ok.cur_vars_le
                                      have hhl_dec1 : (hl_h - 1#64).toNat ≤ s1.core.cur_vars := by
                                        dsimp only [s1]; rw [hhl_dec]; omega
                                      c0_hsplit
                                      · c0_hsteps!; exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                          (by rw [hhl_dec]; omega)
                                          ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                      · c0_hsplit
                                        · c0_hsteps!; exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                            (by rw [hhl_dec]; omega)
                                            ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                        · have hv_lt : v.toNat < s1.core.cur_vars := by
                                            rw [Nat.mod_eq_of_lt
                                              (by omega : s1.core.cur_vars < 2 ^ 64)] at hc
                                            omega
                                          have hv_fl : (v.setWidth 64).toNat <
                                              s1.core.flags.length := by
                                            rw [hden1.lengths.core_ok.flags_len, m6_zext32_toNat]
                                            omega
                                          have hv_vl : (v.setWidth 64 <<< (1 : Nat)).toNat <
                                              s1.core.vals.length := by
                                            rw [hden1.lengths.core_ok.vals_len]; c0_bound
                                          c0_hsplit
                                          · c0_hsteps!
                                            exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                              (by rw [hhl_dec]; omega)
                                              ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                          · c0_hsplit
                                            · c0_hsteps!
                                              exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                                (by rw [hhl_dec]; omega)
                                                ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                            · c0_hsteps_nogrp
                                              let fl2 := s1.core.flags.set (v.setWidth 64).toNat
                                                (s1.core.flags[(v.setWidth 64).toNat]'hv_fl &&&
                                                  ~~~16#32)
                                              let s2 : FullState :=
                                                { s1 with core := { s1.core with flags := fl2 } }
                                              have hden2 : FullDenseInv c F0 s2 :=
                                                fullDenseInv_with_flags hden1
                                                  (by simp [fl2, hden1.lengths.core_ok.flags_len])
                                              have htmk2 : TmkZero s2 := htmk1.congr rfl rfl
                                              s6a_m6_call hNbrs
                                              refine ⟨c, F0, s2, R, rfl, hden2, htmk2, hm, ?_⟩
                                              intro nn mclr3 ws2_3 m3 _ hl3 hnn_le _ hm3
                                              have hcv2_le := hden2.lengths.core_ok.cur_vars_le
                                              let s3 : FullState := { s2 with
                                                core := { s2.core with min_clr := mclr3 },
                                                scratch := { s2.scratch with work_stk2 := ws2_3 } }
                                              have hden3 : FullDenseInv c F0 s3 :=
                                                fullDenseInv_with_min_clr_work_stk2 hden2
                                                  hl3.core_ok.min_clr_len_arr
                                                  hl3.scratch_ok.work_stk2_len
                                              have htmk3 : TmkZero s3 := htmk2.congr rfl rfl
                                              c0_hsteps_nogrp; s6a_m6_call hBveVar
                                              refine ⟨c, F0, s3, R, rfl, hden3, htmk3, hv_lt,
                                                hm3, ?_⟩
                                              intro st s4 m4 hden4 htmk4 hcv4 hfu4 _ hst20 hm4
                                              have hfu4' := Nat.le_trans hfu4 hfuh
                                              have hcv4_le := hden4.lengths.core_ok.cur_vars_le
                                              have hhl_s4 : (hl_h - 1#64).toNat ≤
                                                  s4.core.cur_vars := by
                                                dsimp only [s3, s2, s1] at hcv4; rw [hhl_dec]; omega
                                              have htr_s4 : (tr_h + 1#64).toNat ≤ bve_lim.toNat :=
                                                by omega
                                              c0_hsplit
                                              · c0_hsteps!; exact hQ 20#64 s4 m4 hden4 htmk4 hfu4'
                                                  (Or.inr rfl) (fun _ => hst20 hc) hm4
                                              · c0_hsplit
                                                · c0_hsteps!; exact hQ 20#64 s4 m4 hden4 htmk4
                                                    hfu4' (Or.inr rfl)
                                                    (fun _ => hden4.inconsistent_unsat hc) hm4
                                                · c0_hsplit
                                                  · c0_hsteps!; exact hBh (tr_h + 1#64, hl_h - 1#64,
                                                      re_h, ()) m4 ⟨s4, htr_s4, hhl_s4, hden4,
                                                        htmk4, hfu4', hm4⟩
                                                  · refine wp_join_state (ts := [i64, .bool])
                                                      (α := BitVec 64 × Bool × FullState)
                                                      (fun x => (x.1, x.2.1, ()))
                                                      (fun x mj =>
                                                        x.1.toNat ≤ x.2.2.core.cur_vars ∧
                                                        FullDenseInv c F0 x.2.2 ∧ TmkZero x.2.2 ∧
                                                        x.2.2.core.fuel.toNat ≤
                                                          s0.core.fuel.toNat ∧
                                                        (FullMem c x.2.2 ⋆ R) mj)
                                                      (fun _ ⟨hl_f, re_f, sf⟩ mf ⟨hhlf, hdenf,
                                                          htmkf, hfuf, hmf⟩ => by
                                                        c0_hsteps!; dsimp only at hhlf hdenf
                                                        have hcvf :=
                                                          hdenf.lengths.core_ok.cur_vars_le
                                                        have htr_sub : bve_lim.toNat - tr_h.toNat =
                                                            (bve_lim.toNat - (tr_h + 1#64).toNat) +
                                                              1 := by omega
                                                        refine hLh ((bve_lim.toNat - (tr_h +
                                                            1#64).toNat) * (c.max_vars + 1) +
                                                            hl_f.toNat) (tr_h + 1#64, hl_f, re_f,
                                                            ()) mf ?_ ⟨sf, htr_s4, hhlf, rfl, hdenf,
                                                            htmkf, hfuf, hmf⟩
                                                        rw [htr_sub, Nat.add_mul, Nat.one_mul]
                                                        omega)
                                                      (fun Jn hJn => by
                                                        refine wp_join0 (P := fun mj => mj = m4)
                                                          (fun _ mj hmj => by
                                                            have hmj4 : (FullMem c s4 ⋆ R) mj :=
                                                              hmj ▸ hm4
                                                            c0_hsteps_nogrp
                                                            refine wp_join_state_pure
                                                              (ts := [.bool]) (α := Bool)
                                                              (fun b => (b, ())) (fun _ => True)
                                                              (fun _ re_1 _ => by
                                                                rw [Blocks.get_here]; dsimp only
                                                                exact s6a_elim_bve_rearm_loop_wp Γ
                                                                  hPush (hl_dec1 := hl_h - 1)
                                                                  (fun hl_f re_f mf ⟨sf, hhlf,
                                                                      hdenf, htmkf, hfuf, hmf⟩ =>
                                                                    hJn (hl_f, re_f, sf) mf ⟨hhlf,
                                                                      hdenf, htmkf, hfuf, hmf⟩)
                                                                  hhl_s4 (Nat.le_trans hnn_le hcv4)
                                                                  hden4 htmk4 hfu4' hmj4)
                                                              (fun Jre hJre => by
                                                                c0_hsplit <;> {
                                                                  c0_hsteps!; exact hJre _ trivial
                                                                }))
                                                          (fun Jth hJth => by
                                                            c0_hsplit
                                                            · c0_hsteps!; exact hJth m4 rfl
                                                            · c0_hsplit
                                                              · c0_hsteps!; exact hJth m4 rfl
                                                              · c0_hsteps!
                                                                exact hJn (hl_h - 1#64, re_h, s4)
                                                                  m4 ⟨hhl_s4, hden4, htmk4, hfu4',
                                                                    hm4⟩))
                                    · c0_hsteps!; exact hbrk_h
                                  · c0_hsteps!; exact hbrk_h
                                · c0_hsteps!; exact hbrk_h
                              · c0_hsteps!; exact hbrk_h
                            · c0_hsteps!; exact hbrk_h
                          · intro _ Lh _ hLh; c0_hsteps!
                            exact hLh _ (tried, hl_p, false, ()) mp
                              ⟨sp, htr_le, hhlp_le, rfl, hdensp, htmksp, hfuu', hmp⟩
                    · intro Lp hLp; c0_hsteps!
                      exact hLp su.core.cur_vars (0#64, 0#64, ()) mi
                        ⟨ws1, su.scratch.sim_sig, hws1, hdwu.1.scratch_ok.sim_sig_len,
                         Nat.zero_le _, by simp, Nat.zero_le _, hmi⟩
                · intro Li hLi; c0_hsteps!
                  exact hLi su.core.cur_vars (0#64, ()) mu
                    ⟨su.scratch.work_stk1, hws1u, Nat.zero_le _, by simp, hmu⟩
              · c0_hsteps!
                exact hQ 20#64 su mu hdenu htmku' hfuu' (Or.inr rfl)
                  (fun _ => hfu_uns (by simpa using hc)) hmu
            · c0_hsteps!; exact hbrk_r
          · c0_hsteps!; exact hbrk_r
        · c0_hsteps!; exact hbrk_r
      · c0_hsteps!; exact hbrk_r
    · c0_hsteps!; exact hbrk_r
  · intro _ Lr _ hLr; c0_hsteps!
    exact hLr 16 (0#64, 0#64, false, 0#64, ()) mc
      ⟨sz, Nat.zero_le _, rfl, Nat.zero_le _, Nat.zero_le _, hdenz, htmkz, Nat.le_refl _, hmc⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
