/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullLuckyLemmas
import LeanQbe.T.Logic.C0Step
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M6.0` Lucky Probing `S1.5` Bridge (`FullM6LuckyS15`)

Bridges `full_lucky_scan` and `full_lucky` directly onto `FullM6BcpS15.fullBcpS15Spec`
(permitting `s'.scratch.delayed` updates from `full_bcp_s15`), without editing
frozen `FullLuckyLemmas{,1,2}.lean`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6LuckyS15

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open Full.FullLuckyHelpers
open scoped Full.FullArenaTactics Full.FullLuckyTactics

private theorem bv64_four : BitVec.ofNat 64 4 = (4 : BitVec 64) := rfl
private theorem bv64_144 : BitVec.ofNat 64 144 = (144 : BitVec 64) := rfl
private theorem bv64_160 : BitVec.ofNat 64 160 = (160 : BitVec 64) := rfl
private theorem bv64_168 : BitVec.ofNat 64 168 = (168 : BitVec 64) := rfl
private theorem bv64_520 : BitVec.ofNat 64 520 = (520 : BitVec 64) := rfl
private theorem bv64_768 : BitVec.ofNat 64 768 = (768 : BitVec 64) := rfl
private theorem bv64_776 : BitVec.ofNat 64 776 = (776 : BitVec 64) := rfl

/-- Shared `full_assign(lit, -1); full_propagate()` decision tail from post-frame-store state. -/
private theorem call_assign_prop_decide_s15_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s_init : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {lit : BitVec 32} {v : Nat} {k_prop : Tup Val [i64] → Expr Val Cont [i64]}
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hProp : ∀ args m Q X, fullBcpS15Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hsp : FullSparseInv c F0 s) (hfl : s.core.fuel.toNat ≤ s_init.core.fuel.toNat)
    (hv_lt : v < s.core.cur_vars) (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8)
    (hlit_v : lit.toNat / 2 = v)
    (hm : (FullMem c { s with core := { s.core with
      cur_level := s.core.cur_level + 1
      frame_trail := s.core.frame_trail.set (s.core.cur_level + 1)
        (BitVec.ofNat 32 s.core.trail_end)
      frame_dec := s.core.frame_dec.set (s.core.cur_level + 1) lit } } ⋆ R) m)
    (hK : ∀ (r : BitVec 64) (F_cur : List (List Nat)) (s_asn s_p : FullState) (mp : Mem 64),
      s_p.LengthsOk c → FullSparseInv c F0 s_p → FullWitnessInv c F0 F_cur s_p.core →
      s_p.core.cur_level = s.core.cur_level + 1 → s_p.core.cur_vars = s.core.cur_vars →
      s_p.core.fuel.toNat ≤ s_init.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → FullConflictOkW F_cur s_p) → FullTrailExt s_asn.core s_p.core →
      s.core.trail_end < s_asn.core.trail_end → s_asn.core.trl[s.core.trail_end]? = some lit →
      s_asn.core.lvl[v]?.getD 0#32 = BitVec.ofNat 32 (s.core.cur_level + 1) →
      (FullMem c s_p ⋆ R) mp → wp Γ Q X (k_prop (r, PUnit.unit)) mp) :
    wp Γ Q X (@Expr.call Val Cont [i64] "full_assign" [i64, i32, i32] []
      (Arg.var c.hdr, Arg.var lit, Arg.imm (4294967295 : BitVec 32), PUnit.unit) fun _ =>
      @Expr.call Val Cont [i64] "full_propagate" [i64] [i64]
        (Arg.var c.hdr, PUnit.unit) k_prop) m := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hsp.1.lengths.core_ok.cur_vars_le
  have hte_le := hsp.1.lengths.core_ok.trail_end_le
  obtain ⟨_, hw0⟩ := hsp.1.witness
  have hcl0 := hw0.cur_level_le
  have hpr0 := lucky_decide_preserves_fullSparseInv hsp hv_lt hval0 hlit_v
    (unas' := 0#64) (unfl' := 0#64)
    (List.length_replicate (n := c.max_vars) (a := (0 : BitVec 32)))
    (List.length_replicate (n := c.max_vars) (a := (0 : BitVec 8)))
  have hte_lt := hpr0.2.2.1
  have hnlvl_le := hpr0.2.2.2.1
  have hval_lit := hpr0.2.2.2.2
  let ftrl' := s.core.frame_trail.set (s.core.cur_level + 1) (BitVec.ofNat 32 s.core.trail_end)
  let fdec' := s.core.frame_dec.set (s.core.cur_level + 1) lit
  let s_dec : FullState :=
    { s with core := { s.core with
      cur_level := s.core.cur_level + 1, frame_trail := ftrl', frame_dec := fdec' } }
  have hdec_len : s_dec.LengthsOk c := by
    refine { hsp.1.lengths with core_ok := { hsp.1.lengths.core_ok with
      frame_trail_len := by
        change ftrl'.length = c.max_vars + 1
        simp [ftrl', hsp.1.lengths.core_ok.frame_trail_len]
      frame_dec_len := by
        change fdec'.length = c.max_vars + 1
        simp [fdec', hsp.1.lengths.core_ok.frame_dec_len] } }
  have hcl_lt32 : s_dec.core.cur_level < 2 ^ 32 := by
    change s.core.cur_level + 1 < 2 ^ 32; omega
  have hnot_pre : ¬ (s_dec.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s_dec.core.trail_end ∨
      s_dec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
    change ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
      s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
    rw [hlit_v, hval_lit]; simp; omega
  c0_call hAssign
  refine ⟨c, s_dec, R, rfl, hdec_len, hcl_lt32, hm, ?_⟩
  have hcl_ne0 : s_dec.core.cur_level ≠ 0 := by change s.core.cur_level + 1 ≠ 0; omega
  dsimp only [vals, Arg.val]
  simp only [hnot_pre, ↓reduceIte, hcl_ne0]
  intro flags' unass' phases' ma hfl_len hph_len hma
  have hpr := lucky_decide_preserves_fullSparseInv hsp hv_lt hval0 hlit_v
    (unas' := unass') (unfl' := s_dec.core.unflushed) hfl_len hph_len
  let s_asn : FullState :=
    { core := { s_dec.core with
        unassigned := unass', unflushed := s_dec.core.unflushed,
        trail_end := s_dec.core.trail_end + 1,
        vals := (s_dec.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 255#8,
        flags := flags',
        lvl := s_dec.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 s_dec.core.cur_level),
        rsns := s_dec.core.rsns.set (lit.toNat / 2) 4294967295#32,
        trl := s_dec.core.trl.set s_dec.core.trail_end lit,
        trail_pos := s_dec.core.trail_pos.set (lit.toNat / 2)
          (BitVec.ofNat 32 s_dec.core.trail_end) }
      scratch := { s_dec.scratch with phases := phases' } }
  have hsp_asn0 : FullSparseInv c F0 _ := hpr.1
  have hsp_asn : FullSparseInv c F0 s_asn := by
    simpa only [s_asn, s_dec, ftrl', fdec', hlit_v] using hsp_asn0
  obtain ⟨F_cur_a, hw_a⟩ := hsp_asn.1.witness
  c0_call hProp
  refine ⟨c, F0, F_cur_a, s_asn, R, rfl, hsp_asn.1.lengths, hw_a, hsp_asn.2.2.2.2, hma, ?_⟩
  dsimp only
  intro r vals' flags'' lvl' rsns' trl' tp' te' prop' unass'' unfl'' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases'' del' mp
    hlen_p hw_p htr_p hperm_p _ hfl_p hr_or h0 h1 h2 hnoop hmp
  let s_p : FullState :=
    { core := { s_asn.core with
        unassigned := unass'', wlen := wlen', wusable := wu', unflushed := unfl'',
        trail_end := te', propagated := prop', fuel := fuel', confl_ref := cref',
        confl_type := ctype', confl_lit0 := c0', confl_lit1 := c1', oom := oom',
        vals := vals', flags := flags'', lvl := lvl', rsns := rsns', trl := trl',
        trail_pos := tp', wvec := wvec', arena := arena', wstk := wstk' }
      scratch := { s_asn.scratch with
        search_ticks := ticks', phases := phases'', wsort := wsort', delayed := del' } }
  have hsp_p : FullSparseInv c F0 s_p :=
    fullSparseInv_of_fullPropagate hsp_asn hlen_p hw_p hperm_p rfl rfl rfl rfl rfl
  have hte_asn : s.core.trail_end < s_asn.core.trail_end := by
    change s.core.trail_end < s.core.trail_end + 1; omega
  have htrl_asn : s_asn.core.trl[s.core.trail_end]? = some lit := by
    change (s.core.trl.set s.core.trail_end lit)[s.core.trail_end]? = some lit
    rw [List.getElem?_set_self]; have := hsp.1.lengths.core_ok.trl_len; omega
  have hlvl_asn : s_asn.core.lvl[v]?.getD 0#32 = BitVec.ofNat 32 (s.core.cur_level + 1) := by
    change (s.core.lvl.set (lit.toNat / 2)
      (BitVec.ofNat 32 (s.core.cur_level + 1)))[v]?.getD 0#32 = _
    rw [hlit_v, List.getElem?_set_self]; simp
    have := hsp.1.lengths.core_ok.lvl_len; omega
  exact hK r F_cur_a s_asn s_p mp hlen_p hsp_p hw_p rfl rfl (Nat.le_trans hfl_p hfl)
    hr_or (fun hr1 => (h1 hr1).2.2) htr_p hte_asn htrl_asn hlvl_asn hmp

/-- Pre-step bounds for `nlvl := cur_level + 1` frame stores and guard `nlvl ≤ max_vars`. -/
theorem decide_nlvl_ok {c : FullCfg} {F0 : CNF Nat} {s : FullState} {v : Nat}
    (hsp : FullSparseInv c F0 s) (hv_lt : v < s.core.cur_vars)
    (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8) :
    s.core.trail_end < s.core.cur_vars ∧
    s.core.cur_level + 1 < 2 ^ 64 ∧
    s.core.cur_level + 1 ≤ c.max_vars ∧
    (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat = s.core.cur_level + 1 ∧
    (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat < s.core.frame_trail.length ∧
    (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat < s.core.frame_dec.length ∧
    ¬ ((BitVec.ofNat 64 c.max_vars).toNat <
      (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat) := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hsp.1.lengths.core_ok.cur_vars_le
  obtain ⟨_, hw0⟩ := hsp.1.witness
  have hcl0 := hw0.cur_level_le
  have hte_lt := trail_end_lt_of_unassigned_var hw0 hv_lt hval0
  have hnlvl_lt64 : s.core.cur_level + 1 < 2 ^ 64 := by omega
  have hnlvl_bv : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat = s.core.cur_level + 1 := by
    bv_omega
  have hnlvl_le : s.core.cur_level + 1 ≤ c.max_vars := by omega
  have hft_len : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat < s.core.frame_trail.length := by
    rw [hnlvl_bv, hsp.1.lengths.core_ok.frame_trail_len]; omega
  have hfd_len : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat < s.core.frame_dec.length := by
    rw [hnlvl_bv, hsp.1.lengths.core_ok.frame_dec_len]; omega
  have hnlvl_ne : ¬ ((BitVec.ofNat 64 c.max_vars).toNat <
      (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat) := by
    rw [hnlvl_bv, Full.FullLuckyTactics.bv64_ofNat_toNat (by omega)]; omega
  exact ⟨hte_lt, hnlvl_lt64, hnlvl_le, hnlvl_bv, hft_len, hfd_len, hnlvl_ne⟩

/-- `cur_level ≤ 1` conflict analysis + re-propagation branch of `full_lucky_scan`. -/
private theorem scan_ana_branch_s15_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur1 : List (List Nat)} {s_init s_p1 : FullState}
    {R : Mem 64 → Prop} {mp1 : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jbt : Cont [i64]} {karg : Val i64}
    (hProp : ∀ args m Q X, fullBcpS15Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hAna : ∀ args m Q X, fullAnalyzeSpec args m Q X →
      Γ "full_analyze" [i64] [i64] args m Q X)
    (hsp1 : FullSparseInv c F0 s_p1) (hw1 : FullWitnessInv c F0 F_cur1 s_p1.core)
    (hcl_eq1 : s_p1.core.cur_level = 1) (hcf1 : FullConflictOkW F_cur1 s_p1)
    (hfl_p1 : s_p1.core.fuel.toNat ≤ s_init.core.fuel.toNat)
    (hmp1 : (FullMem c s_p1 ⋆ R) mp1)
    (hret2 : ∀ (s_b : FullState) mb,
      FullSparseInv c F0 s_b → s_b.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (FullMem c s_b ⋆ R) mb →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit)) mb)
    (hret2_otfs : ∀ (s_b : FullState) mb,
      FullOtfsInvW c F0 F_cur1 s_b → s_b.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (FullMem c s_b ⋆ R) mb →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit)) mb)
    (hunsat : ∀ (s_u : FullState) mu,
      s_u.LengthsOk c → s_u.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      F0.Unsat → (FullMem c s_u ⋆ R) mu → Q (20#64, PUnit.unit) mu)
    (hJbt : ∀ (s_o : FullState) mo,
      s_o.core.cur_vars = s_p1.core.cur_vars →
      FullSparseInv c F0 s_o → s_o.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (FullMem c s_o ⋆ R) mo → Jbt (karg, PUnit.unit) mo) :
    wp Γ Q X (@Expr.call Val Cont [i64] "full_analyze" [i64] [i64]
      (Arg.var c.hdr, PUnit.unit) fun p_43 =>
      Expr.let_ (op2 (.cmp .eq i64) (Arg.var p_43.fst) (Arg.imm (20 : BitVec 64))) fun p_44 =>
        Expr.jnz (Arg.var p_44.fst) (Expr.ret (Arg.imm (20 : BitVec 64), PUnit.unit))
          (Expr.let_ (op2 (.cmp .ne i64) (Arg.var p_43.fst) (Arg.imm (1 : BitVec 64)))
            fun p_45 =>
              Expr.jnz (Arg.var p_45.fst)
                (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
                  (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
                  fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit))
                (@Expr.call Val Cont [i64] "full_propagate" [i64] [i64]
                  (Arg.var c.hdr, PUnit.unit) fun p_46 =>
                  Expr.let_ (op2 (.cmp .eq i64) (Arg.var p_46.fst) (Arg.imm (1 : BitVec 64)))
                    fun p_47 =>
                      Expr.jnz (Arg.var p_47.fst)
                        (Expr.ret (Arg.imm (20 : BitVec 64), PUnit.unit))
                        (Expr.let_
                          (op2 (.cmp .eq i64) (Arg.var p_46.fst) (Arg.imm (2 : BitVec 64)))
                          fun p_48 =>
                            Expr.jnz (Arg.var p_48.fst)
                              (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
                                (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
                                fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit))
                              (Expr.jump Jbt (Arg.var karg, PUnit.unit)))))) mp1 := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hlen1 := hsp1.1.lengths
  have hcv_le := hlen1.core_ok.cur_vars_le
  have hte_le := hlen1.core_ok.trail_end_le
  have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by have := hw1.cur_level_le; omega
  have hsw1 : FullSparseInvW c F0 F_cur1 s_p1 := ⟨hlen1, hw1, hsp1.2⟩
  c0_call hAna
  refine ⟨c, F0, F_cur1, s_p1, R, rfl, hsw1, hcf1, hmp1, ?_⟩
  intro ra s_a ma hlen_a hra hcv_a hfl_a hws_a huns_a hotfs_a h1_a hm_a
  flk_unmdata; flk_to_group
  · flk_steps
    have hra20 : ra = 20#64 := by assumption
    exact hunsat s_a ma hlen_a (Nat.le_trans hfl_a hfl_p1) (huns_a hra20) hm_a
  · have hne20 : ra ≠ 20#64 := by assumption
    have hne1 : ra ≠ 1#64 := by assumption
    have hra0 : ra = 0#64 := by
      rcases hra with rfl | rfl | rfl
      · rfl
      · exact absurd rfl hne1
      · exact absurd rfl hne20
    exact hret2_otfs s_a ma (hotfs_a hra0) (Nat.le_trans hfl_a hfl_p1) hm_a
  · have hra1 : ra = 1#64 := by assumption
    obtain ⟨hsw_a, hcl_lt_a⟩ := h1_a hra1
    have hcl0_a : s_a.core.cur_level = 0 := by omega
    c0_call hProp
    refine ⟨c, F0, F_cur1, s_a, R, rfl, hsw_a.1, hsw_a.2.1, hsw_a.2.2.2.2.2, hm_a, ?_⟩
    dsimp only
    intro r3 vals3 flags3 lvl3 rsns3 trl3 tp3 te3 prop3 unass3 unfl3
      wvec3 arena3 wstk3 wlen3 wu3 fuel3 ctype3 cref3 c03 c13 oom3
      ticks3 wsort3 phases3 del3 mp3 hlen3 hw3 htr3 hperm3 _ hfl3 hr3 h0_3 h1_3 h2_3 hnoop3 hmp3
    let s_p3 : FullState :=
      { core := { s_a.core with
          unassigned := unass3, wlen := wlen3, wusable := wu3, unflushed := unfl3,
          trail_end := te3, propagated := prop3, fuel := fuel3, confl_ref := cref3,
          confl_type := ctype3, confl_lit0 := c03, confl_lit1 := c13, oom := oom3,
          vals := vals3, flags := flags3, lvl := lvl3, rsns := rsns3, trl := trl3,
          trail_pos := tp3, wvec := wvec3, arena := arena3, wstk := wstk3 }
        scratch := { s_a.scratch with
          search_ticks := ticks3, phases := phases3, wsort := wsort3, delayed := del3 } }
    have hsp3 : FullSparseInv c F0 s_p3 :=
      fullSparseInv_of_fullPropagate ⟨⟨hsw_a.1, F_cur1, hsw_a.2.1⟩, hsw_a.2.2⟩
        hlen3 hw3 hperm3 rfl rfl rfl rfl rfl
    have hcl0_3 : s_p3.core.cur_level = 0 := hcl0_a
    have hfl_3 : s_p3.core.fuel.toNat ≤ s_init.core.fuel.toNat :=
      Nat.le_trans hfl3 (Nat.le_trans hfl_a hfl_p1)
    flk_unmdata; flk_to_group
    · flk_steps
      have hr3_1 : r3 = 1#64 := by assumption
      have hunsat3 : F0.Unsat :=
        level0_unsat_of_conflict_okW hw3 hcl0_3 (h1_3 hr3_1).2.2
      exact hunsat s_p3 mp3 hlen3 hfl_3 hunsat3 hmp3
    · exact hret2 s_p3 mp3 hsp3 hfl_3 hmp3
    · flk_steps
      exact hJbt s_p3 mp3 hcv_a hsp3 hfl_3 hmp3


/-! ## `full_lucky_scan` parametric `Func.wp` proof -/

theorem full_lucky_scan_s15_wp (Γ : Env)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hProp : ∀ args m Q X, fullBcpS15Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hAna : ∀ args m Q X, fullAnalyzeSpec args m Q X →
      Γ "full_analyze" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullLuckyScanSpec args m Q X →
      Func.wp Γ full_lucky_scan_body args m Q X := by
  rintro ⟨h, pol?, fwd?, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hm, hQ⟩
  flk_to_group
  have hret_bt : ∀ r (s_b : FullState) mb,
      FullSparseInv c F0 s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s_b ⋆ R) mb → (r = 0#64 ∨ r = 2#64) →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm r, PUnit.unit)) mb := by
    intro r s_b mb hsb hfl_b hmb hr_or
    refine call_backtrack0_ret_wp hBt hsb hfl_b hmb fun s' m' hlen' hfl' hsp' hcl0' hm' => ?_
    exact hQ r s' m' hlen' (by rcases hr_or with rfl | rfl <;> simp) hfl'
      (fun h => by rcases hr_or with rfl | rfl <;> cases h) (fun _ => ⟨hsp', hcl0'⟩)
      (fun _ => hsp'.2.2.2.1.2) hm'
  have hret_otfs_bt : ∀ F_cur (s_b : FullState) mb,
      FullOtfsInvW c F0 F_cur s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s_b ⋆ R) mb →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit)) mb := by
    intro F_cur s_b mb hotfs hfl_b hmb
    refine call_backtrack0_otfs_ret2_wp hBt hotfs hfl_b hmb
      fun s' m' hlen' hfl' hsp' hcl0' hm' => ?_
    exact hQ 2#64 s' m' hlen' (Or.inr (Or.inl rfl)) hfl'
      (fun h => absurd h (by decide)) (fun _ => ⟨hsp', hcl0'⟩) (fun _ => hsp'.2.2.2.1.2) hm'
  refine wp_loop_group (ts := [i64])
    (fun rem (idx, _) ml => ∃ st : FullState,
      rem = s.core.cur_vars - idx.toNat ∧ idx.toNat ≤ s.core.cur_vars ∧
      st.core.cur_vars = s.core.cur_vars ∧ FullSparseInv c F0 st ∧
      st.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st ⋆ R) ml) ?_ ?_
  · rintro Jloop rem ⟨idx, ⟨⟩⟩ ml ih ⟨st, rfl, hidx_le, hcv_eq, hst, hfl, hml⟩
    have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
    have hcv_le := hst.1.lengths.core_ok.cur_vars_le
    dsimp [Blocks.get]
    simp only [wp_let, Op.wp, OpCode.wp, vals, Arg.val, liftCmp, CmpOp.evalBits, Ty.hasFloat]
    rw [wp_jnz]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun hult => ?_, fun _ => ?_⟩
    · have hidx_lt : idx.toNat < s.core.cur_vars := by
        have h1 : BitVec.ult idx (BitVec.ofNat 64 s.core.cur_vars) = true := hult
        rw [BitVec.ult, decide_eq_true_eq, Full.FullLuckyTactics.bv64_ofNat_toNat (by omega)] at h1
        exact h1
      have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 :=
        Full.FullLuckyTactics.bv64_add1_toNat (by omega)
      refine wp_join_group (ts := [i64]) (fun (v, _) mv =>
          mv = ml ∧ v.toNat < st.core.cur_vars) ?_ ?_
      · rintro Jv ⟨v, ⟨⟩⟩ _ ⟨rfl, hv_lt⟩
        dsimp [Blocks.get]
        refine wp_join_group (ts := []) (fun _ mn =>
            ∃ st' : FullState, st'.core.cur_vars = s.core.cur_vars ∧
              FullSparseInv c F0 st' ∧ st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st' ⋆ R) mn) ?_ ?_
        · rintro Jnext ⟨⟩ mn ⟨st', hcv', hst', hfl', hmn⟩
          dsimp [Blocks.get]
          flk_steps
          exact ih (s.core.cur_vars - (idx.toNat + 1)) (idx + 1#64, PUnit.unit) mn (by omega)
            ⟨st', by simp [hidx1_nat], by omega, hcv', hst', hfl', hmn⟩
        · intro Jnext hJnext
          have hv_fl : v.toNat < st.core.flags.length := by
            have := hst.1.lengths.core_ok.flags_len; omega
          have hv2_vl : (v <<< 1#64).toNat < st.core.vals.length := by
            have := hst.1.lengths.core_ok.vals_len
            rw [Full.FullLuckyTactics.bv64_shl1_toNat (by omega)]; omega
          flk_unmdata
          simp only [bv64_four, bv64_144, bv64_160, bv64_168, bv64_768]
          flk_to_group
          · exact hret_bt 2#64 st _ hst hfl hml (Or.inr rfl)
          · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using hc
            have hfl_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
              Full.FullLuckyTactics.bv64_sub1_toNat hfl_ne
            have hval0 : st.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
              have h2v : (v <<< 1#64).toNat = 2 * v.toNat :=
                Full.FullLuckyTactics.bv64_shl1_toNat (by omega)
              have h_eq : BitVec.signExtend 32 st.core.vals[2 * v.toNat % 2 ^ 64] = 0#32 := by
                assumption
              have h_mod : 2 * v.toNat % 2 ^ 64 = 2 * v.toNat := by
                have := c.hmaxv; unfold dimacsBound at this
                have := hst.1.lengths.core_ok.cur_vars_le; omega
              rw [Full.FullLuckyTactics.bv8_sext32_eq0_iff] at h_eq
              have hv2_lt : 2 * v.toNat < st.core.vals.length := by
                rw [← h2v]; exact hv2_vl
              have h_eq0 : st.core.vals[2 * v.toNat] = 0#8 := by simpa [h_mod] using h_eq
              simp [List.getElem?_eq_getElem hv2_lt, h_eq0]
            let st1 : FullState :=
              { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
            have hst1 : FullSparseInv c F0 st1 := FullSparseInv.with_fuel hst (st.core.fuel - 1#64)
            have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
              change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat; rw [hfl_sub]; omega
            refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                (FullMem c st1 ⋆ R) mlit ∧ lit.toNat / 2 = v.toNat) ?_ ?_
            · rintro Jlit ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_v⟩
              dsimp [Blocks.get]
              obtain ⟨hte_lt1, _, _, hnlvl_bv, hft_len, hfd_len, hnlvl_ne⟩ :=
                decide_nlvl_ok hst1 hv_lt hval0
              have hte32_1 : st1.core.trail_end < 2 ^ 32 := by
                have := hst1.1.lengths.core_ok.cur_vars_le; omega
              flk_unmdata
              simp only [bv64_four, bv64_144, bv64_160, bv64_768]
              c0_steps!
              rw [hnlvl_bv, Full.FullLuckyTactics.bv64_trunc32_ofNat hte32_1] at *
              refine call_assign_prop_decide_s15_wp (R := R) hAssign hProp hst1 hfl1 hv_lt hval0
                hlit_v (by assumption) fun r1 F_cur1 s_asn1 s_p1 mp1 hlen1 hsp1 hw1 hcl1 hcv1
                  hfl_p1 hr1 hcf1 htr1 hte1 htrl1 hlvl1 hmp1 => ?_
              flk_unmdata
              flk_to_group
              · exact hret_bt 2#64 s_p1 mp1 hsp1 hfl_p1 hmp1 (Or.inr rfl)
              · refine wp_join_group (ts := [i64]) (fun (_, _) m_a =>
                    ∃ s_a : FullState, s_a.core.cur_vars = s.core.cur_vars ∧
                      FullSparseInv c F0 s_a ∧ s_a.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullMem c s_a ⋆ R) m_a) ?_ ?_
                · rintro Jafter2 ⟨_, ⟨⟩⟩ m_a ⟨s_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                  dsimp [Blocks.get]; flk_steps
                  exact hJnext PUnit.unit m_a ⟨s_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                · intro Jafter2 hJafter2
                  flk_unmdata; flk_to_group
                  · have hr1_eq : r1 = 1#64 := by assumption
                    refine wp_join_group (ts := [i64]) (fun (_, _) m_a =>
                        ∃ s_a : FullState, s_a.core.cur_vars = s.core.cur_vars ∧
                          FullSparseInv c F0 s_a ∧ s_a.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullMem c s_a ⋆ R) m_a) ?_ ?_
                    · rintro Jbt ⟨_, ⟨⟩⟩ m_a ⟨s_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                      dsimp [Blocks.get]; flk_steps
                      exact hJafter2 _ m_a ⟨s_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                    · intro Jbt hJbt
                      flk_unmdata
                      simp only [bv64_168]
                      flk_to_group
                      · have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by
                          have := hw1.cur_level_le
                          have := hlen1.core_ok.trail_end_le
                          have := hlen1.core_ok.cur_vars_le; omega
                        have hcl_mod : 1 < s_p1.core.cur_level % 2 ^ 64 := by simpa using hc
                        have hcl_gt1 : 1 < s_p1.core.cur_level := by omega
                        have hcl_bv : (BitVec.ofNat 64 s_p1.core.cur_level - 1#64).toNat =
                            st1.core.cur_level := by
                          rw [hcl1]; bv_omega
                        have hcl_ne1 : s_p1.core.cur_level - 1 < s_p1.core.cur_level := by omega
                        c0_call hBt
                        refine ⟨c, s_p1, R, rfl, hlen1, hcl_lt64,
                          fun _ => by
                            have := hlen1.core_ok.cur_vars_le
                            rw [hcl_bv, hcl1] at *; omega,
                          hw1.trail_lits_lt, hmp1, ?_⟩
                        dsimp only
                        intro vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b mb
                          hlen_b hte_b hprop_b hcl_b hps_b hsh_b htrl_b hbv_b hwt_b hot_b hmb
                        let s_b : FullState :=
                          { core := { s_p1.core with
                              vals := vals_b, lvl := lvl_b, rsns := rsns_b, trl := trl_b,
                              trail_pos := tp_b, trail_end := te_b, propagated := prop_b,
                              cur_level := cl_b, unassigned := unass_b }
                            scratch := sc_b }
                        have hcl_b' : s_b.core.cur_level = st1.core.cur_level := by
                          change cl_b = st1.core.cur_level
                          rw [hcl_b, hcl_bv, hcl1]; omega
                        have hsp_b : FullSparseInv c F0 s_b :=
                          fullSparseInv_of_fullBacktrack hsp1 hlen_b
                            (hwt_b F0 F_cur1 hw1 (by rw [hcl_bv, hcl1]; omega))
                            rfl rfl rfl rfl rfl hps_b.1.1 hps_b.1.2
                        have hv_lt_b : v.toNat < s_b.core.cur_vars := by
                          change v.toNat < s_p1.core.cur_vars
                          rw [hcv1]; exact hv_lt
                        have hval0_b : s_b.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
                          refine scan_backtrack_unassigned hlit_v hte1 htrl1 hlvl1 ?_ htr1
                            (by rw [hcv1]; exact Nat.mul_lt_mul_of_pos_left hv_lt (by decide)) ?_
                          · change st1.core.cur_level + 1 < 2 ^ 32; omega
                          · intro l hl
                            have := (hbv_b ⟨F0, F_cur1, Or.inl hw1⟩).1 l hl
                            simpa [hcl_bv] using this
                        flk_unmdata
                        c0_step; (repeat flk_strip); c0_step
                        · exact hret_bt 2#64 s_b mb hsp_b hfl_p1 hmb (Or.inr rfl)
                        · have hfl_ne_b : s_b.core.fuel ≠ 0#64 := hc
                          have hfl_sub_b : (s_b.core.fuel - 1#64).toNat =
                              s_b.core.fuel.toNat - 1 :=
                            Full.FullLuckyTactics.bv64_sub1_toNat hfl_ne_b
                          let s_b1 : FullState :=
                            { s_b with core := { s_b.core with fuel := s_b.core.fuel - 1#64 } }
                          have hsb1 : FullSparseInv c F0 s_b1 :=
                            FullSparseInv.with_fuel hsp_b (s_b.core.fuel - 1#64)
                          have hfl_b1 : s_b1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            change (s_b.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat
                            rw [hfl_sub_b]
                            have : s_b.core.fuel.toNat ≤ s.core.fuel.toNat := hfl_p1
                            omega
                          have hval0_b1 : s_b1.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := hval0_b
                          obtain ⟨_, _, _, hnlvl_b1, hft_b1, hfd_b1, hne_b1⟩ :=
                            decide_nlvl_ok hsb1 hv_lt_b hval0_b1
                          have hte32_b1 : s_b1.core.trail_end < 2 ^ 32 := by
                            have := hsb1.1.lengths.core_ok.cur_vars_le; omega
                          flk_unmdata
                          c0_steps!
                          rw [hnlvl_b1, Full.FullLuckyTactics.bv64_trunc32_ofNat hte32_b1] at *
                          refine call_assign_prop_decide_s15_wp (R := R) hAssign hProp hsb1 hfl_b1
                            hv_lt_b hval0_b1
                            ((Full.FullLuckyHelpers.bv32_xor1_div2 lit).trans hlit_v)
                            (by assumption)
                            fun r2 F_cur2 s_asn2 s_p2 mp2 hlen2 hsp2 hw2 hcl2 hcv2 hfl_p2 hr2 hcf2
                              htr2 hte2 htrl2 hlvl2 hmp2 => ?_
                          flk_unmdata; flk_to_group
                          · exact hret_bt 2#64 s_p2 mp2 hsp2 hfl_p2 hmp2 (Or.inr rfl)
                          · exact hret_bt 0#64 s_p2 mp2 hsp2 hfl_p2 hmp2 (Or.inl rfl)
                          · flk_steps
                            exact hJbt _ mp2 ⟨s_p2, by
                              change s_p2.core.cur_vars = s.core.cur_vars
                              rw [hcv2]; change s_b.core.cur_vars = s.core.cur_vars
                              change s_p1.core.cur_vars = s.core.cur_vars
                              rw [hcv1]; exact hcv_eq, hsp2, hfl_p2, hmp2⟩
                      · have hcl_mod : s_p1.core.cur_level % 2 ^ 64 ≤ 1 := by simpa using hc
                        have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by
                          have := hw1.cur_level_le
                          have := hlen1.core_ok.trail_end_le
                          have := hlen1.core_ok.cur_vars_le; omega
                        have hcl_eq1 : s_p1.core.cur_level = 1 := by omega
                        refine scan_ana_branch_s15_wp hProp hAna hsp1 hw1 hcl_eq1 (hcf1 hr1_eq)
                          hfl_p1 hmp1
                          (fun s_b mb hsb hfl_b hmb =>
                            hret_bt 2#64 s_b mb hsb hfl_b hmb (Or.inr rfl))
                          (fun s_b mb hotfs hfl_b hmb => hret_otfs_bt F_cur1 s_b mb hotfs hfl_b hmb)
                          (fun s_u mu hlen_u hfl_u huns hmu =>
                            hQ 20#64 s_u mu hlen_u (Or.inr (Or.inr (Or.inr rfl))) hfl_u
                              (fun _ => huns) (fun h => by rcases h with h | h <;> cases h)
                              (fun h => by cases h) hmu)
                          (fun s_o mo hcv_o hsp_o hfl_o hmo =>
                            hJbt _ mo ⟨s_o, by
                              change s_o.core.cur_vars = s.core.cur_vars
                              rw [hcv_o]; change s_p1.core.cur_vars = s.core.cur_vars
                              rw [hcv1]; exact hcv_eq, hsp_o, hfl_o, hmo⟩)
                  · flk_steps
                    exact hJafter2 _ mp1 ⟨s_p1, by
                      change s_p1.core.cur_vars = s.core.cur_vars
                      rw [hcv1]; exact hcv_eq, hsp1, hfl_p1, hmp1⟩
            · intro Jlit hJlit; flk_steps
              · have hl : (BitVec.setWidth 32 (v <<< 1)).toNat = 2 * v.toNat := by bv_omega
                exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
              · have h_eq1 : (v <<< 1) = (v <<< 1#64) := rfl
                have hl : (BitVec.setWidth 32 (v <<< 1) ||| 1#32).toNat = 2 * v.toNat + 1 := by
                  rw [h_eq1]; exact Full.FullLuckyTactics.bv32_shl1_or1_trunc32_toNat (by omega)
                exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
          · exact hJnext PUnit.unit _ ⟨st, hcv_eq, hst, hfl, hml⟩
          · exact hJnext PUnit.unit _ ⟨st, hcv_eq, hst, hfl, hml⟩

      · intro Jv hJv
        flk_steps
        · exact hJv _ ml ⟨rfl, by rw [hcv_eq]; exact hidx_lt⟩
        · have hsub_nat : (BitVec.ofNat 64 s.core.cur_vars - 1#64 - idx).toNat =
              s.core.cur_vars - 1 - idx.toNat := by
            have hlt1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
              Full.FullLuckyTactics.bv64_ofNat_toNat (by omega)
            bv_omega
          exact hJv _ ml ⟨rfl, by rw [hsub_nat, hcv_eq]; omega⟩
    · flk_steps
      exact hQ 10#64 st ml hst.1.lengths (Or.inr (Or.inr (Or.inl rfl))) hfl
        (fun h => absurd h (by decide)) (fun h => by rcases h with h | h <;> cases h)
        (fun _ => hst.2.2.2.1.2) hml
  · intro Jloop hJloop; flk_steps
    exact hJloop s.core.cur_vars (0#64, PUnit.unit) m
      ⟨s, by simp, Nat.zero_le _, rfl, hsp, Nat.le_refl _, hm⟩

theorem full_lucky_s15_wp (Γ : Env)
    (hPolar : ∀ args m Q X, fullLuckyPolarSpec args m Q X →
      Γ "full_lucky_polar" [i64] [i64] args m Q X)
    (hScan : ∀ args m Q X, fullLuckyScanSpec args m Q X →
      Γ "full_lucky_scan" [i64, .bool, .bool] [i64] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hProp : ∀ args m Q X, fullBcpS15Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullLuckySpec args m Q X →
      Func.wp Γ full_lucky_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hm, hQ⟩
  unfold full_lucky_body
  dsimp only [Func.wp]
  (try simp only [bv64_520])
  flk_steps
  let s0 : FullState := { s with core := { s.core with probing := 1#64 } }
  have hsp0 : FullSparseInv c F0 s0 := FullSparseInv.with_probing hsp 1#64
  have hcl0' : s0.core.cur_level = 0 := hcl0
  c0_call hPolar
  refine ⟨c, F0, s0, R, rfl, hsp0.1, by assumption, ?_⟩
  intro p2 hr2
  flk_unmdata
  flk_to_group
  · have hret_bt : ∀ r (s_b : FullState) mb,
        FullSparseInv c F0 s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
        (FullMem c s_b ⋆ R) mb → (r = 0#64 ∨ r = 2#64) →
        wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
          (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
          fun _ => Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.hdr, Arg.imm (520 : BitVec 64), PUnit.unit) }
            fun p => Expr.store (t := i64) (Arg.imm (0 : BitVec 64)) (Arg.var p.fst)
              (Expr.ret (Arg.imm r, PUnit.unit))) mb := by
      intro r s_b mb hsb hfl_b hmb hr_or
      refine call_backtrack0_probing0_ret_wp hBt hsb hfl_b hmb
        fun s' m' hlen' hfl' hpr' hsp' hcl0' hm' => ?_
      exact hQ r s' m' hlen' (by rcases hr_or with rfl | rfl <;> simp) hfl' hpr'
        (fun h => by rcases hr_or with rfl | rfl <;> cases h)
        (fun _ => ⟨hsp', hcl0'⟩) (fun _ => hsp'.2.2.2.1.2) hm'
    refine wp_loop_group (ts := [i64])
      (fun rem (idx, _) ml => ∃ st : FullState,
        rem = s.core.cur_vars - idx.toNat ∧ idx.toNat ≤ s.core.cur_vars ∧
        st.core.cur_vars = s.core.cur_vars ∧ FullSparseInv c F0 st ∧
        st.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st ⋆ R) ml) ?_ ?_
    · rintro Jloop rem ⟨idx, ⟨⟩⟩ ml ih ⟨st, rfl, hidx_le, hcv_eq, hst, hfl, hml⟩
      have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
      have hcv_le := hst.1.lengths.core_ok.cur_vars_le
      dsimp [Blocks.get]
      (try simp only [bv64_520, bv64_776])
      flk_unmdata
      flk_to_group
      · have hidx_lt : idx.toNat < st.core.cur_vars := by
          have hmod := Nat.mod_eq_of_lt (by omega : st.core.cur_vars < 2 ^ 64)
          simp only [hmod] at *
          assumption
        have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 :=
          Full.FullLuckyTactics.bv64_add1_toNat (by omega)
        refine wp_join_group (ts := []) (fun _ mn =>
            ∃ st' : FullState, st'.core.cur_vars = s.core.cur_vars ∧
              FullSparseInv c F0 st' ∧ st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st' ⋆ R) mn) ?_ ?_
        · rintro Jnext ⟨⟩ mn ⟨st', hcv', hst', hfl', hmn⟩
          dsimp [Blocks.get]; flk_steps
          exact ih (s.core.cur_vars - (idx.toNat + 1)) (idx + 1#64, PUnit.unit) mn (by omega)
            ⟨st', by simp [hidx1_nat], by omega, hcv', hst', hfl', hmn⟩
        · intro Jnext hJnext
          have hidx_fl : idx.toNat < st.core.flags.length := by
            have := hst.1.lengths.core_ok.flags_len; omega
          have hidx2_vl : (idx <<< 1#64).toNat < st.core.vals.length := by
            have := hst.1.lengths.core_ok.vals_len
            rw [Full.FullLuckyTactics.bv64_shl1_toNat (by omega)]; omega
          flk_unmdata
          (try simp only [bv64_four, bv64_144, bv64_160, bv64_168, bv64_768])
          flk_to_group
          · exact hret_bt 2#64 st _ hst hfl (by assumption) (Or.inr rfl)
          · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using ‹_›
            have hfl_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
              Full.FullLuckyTactics.bv64_sub1_toNat hfl_ne
            have hval0 : st.core.vals[2 * idx.toNat]?.getD 0#8 = 0#8 := by
              have h2v : (idx <<< 1#64).toNat = 2 * idx.toNat :=
                Full.FullLuckyTactics.bv64_shl1_toNat (by omega)
              have h_eq : BitVec.signExtend 32 st.core.vals[2 * idx.toNat % 2 ^ 64] = 0#32 := by
                assumption
              have h_mod : 2 * idx.toNat % 2 ^ 64 = 2 * idx.toNat := by omega
              rw [Full.FullLuckyTactics.bv8_sext32_eq0_iff] at h_eq
              have h2_lt : 2 * idx.toNat < st.core.vals.length := by
                rw [← h2v]; exact hidx2_vl
              have h_eq0 : st.core.vals[2 * idx.toNat] = 0#8 := by simpa [h_mod] using h_eq
              simp [List.getElem?_eq_getElem h2_lt, h_eq0]
            let st1 : FullState :=
              { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
            have hst1 : FullSparseInv c F0 st1 := FullSparseInv.with_fuel hst (st.core.fuel - 1#64)
            have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
              change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat; rw [hfl_sub]; omega
            refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                (FullMem c st1 ⋆ R) mlit ∧ lit.toNat / 2 = idx.toNat) ?_ ?_
            · rintro Jlit ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_v⟩
              dsimp [Blocks.get]
              obtain ⟨_, _, _, hnlvl_bv, hft_len, hfd_len, hnlvl_ne⟩ :=
                decide_nlvl_ok hst1 hidx_lt hval0
              have hte32_1 : st1.core.trail_end < 2 ^ 32 := by
                have := hst1.1.lengths.core_ok.cur_vars_le; omega
              flk_unmdata
              (try simp only [bv64_four, bv64_144, bv64_160, bv64_768])
              c0_steps!
              rw [hnlvl_bv, Full.FullLuckyTactics.bv64_trunc32_ofNat hte32_1] at *
              refine call_assign_prop_decide_s15_wp (R := R) hAssign hProp hst1 hfl1 hidx_lt hval0
                hlit_v (by assumption) fun r1 _ _ s_p1 mp1 _ hsp1 _ _ hcv1
                  hfl_p1 _ _ _ _ _ _ hmp1 => ?_
              flk_unmdata; flk_to_group
              · exact hret_bt 0#64 s_p1 mp1 hsp1 hfl_p1 hmp1 (Or.inl rfl)
              · flk_steps
                exact hJnext PUnit.unit mp1 ⟨s_p1, by
                  change s_p1.core.cur_vars = s.core.cur_vars
                  rw [hcv1]; exact hcv_eq, hsp1, hfl_p1, hmp1⟩
            · intro Jlit hJlit; flk_steps
              · have hl : (BitVec.setWidth 32 (idx <<< 1)).toNat = 2 * idx.toNat := by bv_omega
                exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
              · have h_eq1 : (idx <<< 1) = (idx <<< 1#64) := rfl
                have hl : (BitVec.setWidth 32 (idx <<< 1) ||| 1#32).toNat =
                    2 * idx.toNat + 1 := by
                  rw [h_eq1]; exact Full.FullLuckyTactics.bv32_shl1_or1_trunc32_toNat (by omega)
                exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
          · exact hJnext PUnit.unit _ ⟨st, hcv_eq, hst, hfl, hml⟩
          · exact hJnext PUnit.unit _ ⟨st, hcv_eq, hst, hfl, hml⟩
      · flk_steps
        let st' : FullState := { st with core := { st.core with probing := 0#64 } }
        exact hQ 10#64 st' _ (lengthsOk_with_probing hst.1.lengths 0#64)
          (Or.inr (Or.inr (Or.inl rfl))) hfl rfl
          (fun h => absurd h (by decide)) (fun h => by rcases h with h | h <;> cases h)
          (fun _ => hst.2.2.2.1.2) (by assumption)
    · intro Jloop hJloop; flk_steps
      exact hJloop s.core.cur_vars (0#64, PUnit.unit) _
        ⟨s0, by simp, Nat.zero_le _, rfl, hsp0, Nat.le_refl _, by assumption⟩
  · let LuckyRet : Tup Val [i64] → Mem 64 → Prop := fun (r, _) mr =>
      ∃ sr : FullState, sr.LengthsOk c ∧ (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        sr.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (r = 20#64 → F0.Unsat) ∧
        (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 sr ∧ sr.core.cur_level = 0) ∧
        (r = 10#64 → sr.scratch.extend_len ≤ c.extend_cap) ∧ (FullMem c sr ⋆ R) mr
    c0_call hScan
    refine ⟨c, F0, s0, R, rfl, hsp0, hcl0', by assumption, ?_⟩
    intro r1 s1 m1 hlen1 hr1 hfl1 huns1 h02_1 h10_1 hm1
    flk_unmdata; flk_to_group
    refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
    · rintro JsA ⟨rA, ⟨⟩⟩ mA ⟨srA, hlenA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
      dsimp [Blocks.get]; flk_unmdata; flk_to_group
      refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
      · rintro JsB ⟨rB, ⟨⟩⟩ mB ⟨srB, hlenB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
        dsimp [Blocks.get]; flk_unmdata; flk_to_group
        refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
        · rintro JsC ⟨rC, ⟨⟩⟩ mC ⟨srC, hlenC, hrC, hflC, hunsC, h02C, h10C, hmC⟩
          dsimp [Blocks.get]; flk_unmdata; (try simp only [bv64_520]); flk_steps
          let s' : FullState := { srC with core := { srC.core with probing := 0#64 } }
          exact hQ rC s' _ (lengthsOk_with_probing hlenC 0#64) hrC hflC rfl hunsC
            (fun h => let ⟨hsp_c, hcl_c⟩ := h02C h; ⟨FullSparseInv.with_probing hsp_c 0#64, hcl_c⟩)
            (fun h => h10C h) (by assumption)
        · intro JsC hJsC
          flk_unmdata; flk_to_group
          · have hrB0 : rB = 0#64 := by assumption
            obtain ⟨hspB, hcl0B⟩ := h02B (Or.inl hrB0)
            c0_call hScan
            refine ⟨c, F0, srB, R, rfl, hspB, hcl0B, hmB, ?_⟩
            intro r4 s4 m4 hlen4 hr4 hfl4 huns4 h02_4 h10_4 hm4
            flk_steps
            exact hJsC _ m4 ⟨s4, hlen4, hr4, Nat.le_trans hfl4 hflB, huns4, h02_4, h10_4, hm4⟩
          · flk_steps
            exact hJsC _ mB ⟨srB, hlenB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
      · intro JsB hJsB
        flk_unmdata; flk_to_group
        · have hrA0 : rA = 0#64 := by assumption
          obtain ⟨hspA, hcl0A⟩ := h02A (Or.inl hrA0)
          c0_call hScan
          refine ⟨c, F0, srA, R, rfl, hspA, hcl0A, hmA, ?_⟩
          intro r3 s3 m3 hlen3 hr3 hfl3 huns3 h02_3 h10_3 hm3
          flk_steps
          exact hJsB _ m3 ⟨s3, hlen3, hr3, Nat.le_trans hfl3 hflA, huns3, h02_3, h10_3, hm3⟩
        · flk_steps
          exact hJsB _ mA ⟨srA, hlenA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
    · intro JsA hJsA
      flk_unmdata; flk_to_group
      · have hr10 : r1 = 0#64 := by assumption
        obtain ⟨hsp1, hcl01⟩ := h02_1 (Or.inl hr10)
        c0_call hScan
        refine ⟨c, F0, s1, R, rfl, hsp1, hcl01, hm1, ?_⟩
        intro r2 s2 m2 hlen2 hr2 hfl2 huns2 h02_2 h10_2 hm2
        flk_steps
        exact hJsA _ m2 ⟨s2, hlen2, hr2, Nat.le_trans hfl2 hfl1, huns2, h02_2, h10_2, hm2⟩
      · flk_steps
        exact hJsA _ m1 ⟨s1, hlen1, hr1, hfl1, huns1, h02_1, h10_1, hm1⟩

end LeanQbe.T.Examples.Kissat.FullM6LuckyS15
