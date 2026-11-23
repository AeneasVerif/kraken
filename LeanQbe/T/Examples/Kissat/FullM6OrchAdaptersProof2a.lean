module

public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M6.0` Orchestrator Adapter Proofs — Part 2a (`failed_lit` Helpers)

Pure state-invariant, bitvector-index, arena-clause, and post-loop transition lemmas shared across
the branches of `FullM6OrchAdaptersProof2` (`full_ana_failed_lit_m6_hdr_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6OrchAdapters

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6MinShrink

theorem p2_bv32_lit_neq_ff {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    l ≠ 0xFFFFFFFF#32 := by
  intro h
  have h0 := congrArg BitVec.toNat h
  rw [show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 from rfl] at h0
  omega

theorem p2_getElem_congr_list {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

theorem p2_bv64_add1_eq {x : Nat} (hx : x + 1 < 2 ^ 64) :
    BitVec.ofNat 64 x + 1 = BitVec.ofNat 64 (x + 1) :=
  BitVec.eq_of_toNat_eq (by
    rw [show (1 : BitVec 64) = 1#64 from rfl,
      fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
      bv64_ofNat_toNat (by omega), bv64_ofNat_toNat hx])

theorem p2_bv64_sub1_eq {x : Nat} (hpos : 0 < x) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x - 1 = BitVec.ofNat 64 (x - 1) :=
  BitVec.eq_of_toNat_eq (by
    rw [show (1 : BitVec 64) = 1#64 from rfl,
      fl_bv64_sub1_toNat (by rw [bv64_ofNat_toNat hx]; omega),
      bv64_ofNat_toNat hx, bv64_ofNat_toNat (by omega)])

theorem p2_bv32_lshr_eq {q : BitVec 32} :
    BitVec.ofNat 32 (q.toNat / 2) = q >>> 1 :=
  BitVec.eq_of_toNat_eq (by rw [bv32_ofNat_toNat (by omega), bv32_lshr_1])

theorem p2_clear_ok {c : FullCfg} {s s_f : FullState} {cut : Nat}
    (hok : FailedStateOk c s s_f cut) {mrk' : List (BitVec 8)}
    (hml : mrk'.length = c.max_vars)
    (hmrk0 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) :
    let s_c : FullState := { s_f with core := { s_f.core with mrk := mrk', min_clr_len := 0 } }
    FailedStateOk c s s_c cut := by
  intro s_c
  refine ⟨⟨{ hok.len.core_ok with mrk_len := hml, min_clr_len_le := Nat.zero_le _ },
    hok.len.scratch_ok⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only [s_c]; rw [hok.core]
  · dsimp only [s_c]; rw [hok.scr]
  · exact ⟨Nat.zero_le _, by simp [s_c], fun _ hk => absurd hk (Nat.not_lt_zero _),
      fun v hv hnz => absurd (hmrk0 v hv) hnz⟩
  · have hcv_le := hok.len.core_ok.cur_vars_le
    have hcv_eq : s_f.core.cur_vars = s.core.cur_vars := by rw [hok.core]
    exact fl_mb_empty (fun v hv => hmrk0 v (by omega))

theorem p2_post_otfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s s_t : FullState} {ucnt_f : Nat}
    (hcut : FullCutInvW c F0 F_cur cut s) (hcl1 : s.core.cur_level = 1)
    (hok_t : FailedStateOk c s s_t cut)
    (ht_tmp : s_t.core.tmp_len = ucnt_f + 1)
    {mrk_b : List (BitVec 8)} {mcl_b : Nat} {sc_b : FullScratch}
    (hlen_b : FullState.LengthsOk c
      { core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b }, scratch := sc_b })
    (hcov_b : FullAnaMarksCov c
      { core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b }, scratch := sc_b })
    (hpres_b : FullExtScratchPres s_t
      { core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b }, scratch := sc_b })
    (hws2_b : sc_b.work_stk2 = s_t.scratch.work_stk2)
    {mrk_c : List (BitVec 8)} (hml_c : mrk_c.length = c.max_vars)
    (hclr_c : FullAnaMarksCov c
        { core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b }, scratch := sc_b } →
      ∀ v < c.max_vars, mrk_c[v]?.getD 0#8 = 0#8) :
    let s_b : FullState :=
      { core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b }, scratch := sc_b }
    let s_c : FullState := { s_b with core := { s_b.core with mrk := mrk_c, min_clr_len := 0 } }
    s_c.LengthsOk c ∧ FullOtfsInvW c F0 F_cur s_c ∧
    FullOtfsWitnessInv c F0 F_cur s_c.core ∧
    s_c.core.cur_level = 1 ∧ s_c.core.cur_vars = s.core.cur_vars ∧
    s_c.core.fuel = s.core.fuel ∧ s_c.core.dense_mode = s.core.dense_mode ∧
    s_c.scratch.work_stk2 = s.scratch.work_stk2 ∧ s_c.core.tmp = s_t.core.tmp := by
  intro s_b s_c
  obtain ⟨hlen0, hw0, hlm0, hnd0, hext0, hdm0⟩ := hcut
  have hsc_eq : s_c.core = { s.core with
      mrk := mrk_c, tmp := s_t.core.tmp, tmp_cnt := s.core.tmp_cnt,
      tmp_len := ucnt_f + 1, min_clr_len := 0 } := by
    dsimp only [s_c, s_b]; rw [← ht_tmp]
    exact congrArg (fun k => { k with mrk := mrk_c, min_clr_len := 0 }) hok_t.core
  have hlen_c : s_c.LengthsOk c :=
    ⟨{ hlen_b.core_ok with mrk_len := hml_c, min_clr_len_le := Nat.zero_le _ }, hlen_b.scratch_ok⟩
  have hw_c : FullWitnessCutInv c F0 F_cur cut s_c.core := by
    rw [hsc_eq]
    exact Full.deduce_same_core_cut hw0 mrk_c s_t.core.tmp s.core.tmp_cnt (ucnt_f + 1) 0
  have hmrk_c : ∀ v < c.max_vars, s_c.core.mrk[v]?.getD 0#8 = 0#8 := hclr_c hcov_b
  have hnd_c : FullArenaVarsNodup s_c := by
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
      fullArenaClauseGarb fullArenaClauseGarbCore fullArenaClauseLits
      fullArenaClauseLitsCore fullArenaClauseSizeCore fullArenaHdrCore
    rw [hsc_eq]; exact hnd0
  have hext_pres_c : FullExtScratchPres s s_c :=
    ⟨by dsimp only [s_c, s_b]; exact hpres_b.1.trans (by rw [hok_t.scr]),
     by dsimp only [s_c, s_b]; exact hpres_b.2.trans (by rw [hok_t.scr])⟩
  have hsc_otfs : FullOtfsInvW c F0 F_cur s_c :=
    ⟨hlen_c, hw_c.toFullOtfsWitnessInv, ⟨hmrk_c, fun l hl => by rw [hsc_eq]; exact hlm0.2 l hl⟩,
     hnd_c, FullExtScratchOk.of_pres hext0 hext_pres_c (fun _ hr => by
       unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rw [hsc_eq]; exact hr),
     by rw [hsc_eq]; exact hdm0⟩
  exact ⟨hlen_c, hsc_otfs, hw_c.toFullOtfsWitnessInv, by rw [hsc_eq]; exact hcl1,
    by rw [hsc_eq], by rw [hsc_eq], by rw [hsc_eq],
    by dsimp only [s_c, s_b]; exact hws2_b.trans (by rw [hok_t.scr]), rfl⟩

theorem p2_bt_sp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s_c : FullState}
    (hsc_otfs : FullOtfsInvW c F0 F_cur s_c) (hcl_c : s_c.core.cur_level = 1)
    (hcv_c : s_c.core.cur_vars = s.core.cur_vars) (hfu_c : s_c.core.fuel = s.core.fuel)
    (hdm_c : s_c.core.dense_mode = s.core.dense_mode)
    (hws2_c : s_c.scratch.work_stk2 = s.scratch.work_stk2)
    {vals_bt : List (BitVec 8)} {lvl_bt rsns_bt trl_bt tp_bt : List (BitVec 32)}
    {te_bt prop_bt cl_bt : Nat} {unass_bt : BitVec 64} {sc_bt : FullScratch}
    (hbt_len : FullState.LengthsOk c
      { core := { s_c.core with
          vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
          trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
          cur_level := cl_bt, unassigned := unass_bt },
        scratch := sc_bt })
    (hbt_cl : cl_bt = Nat.min s_c.core.cur_level 0)
    (hbt_pres : FullProbeScratchPres s_c
      { core := { s_c.core with
          vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
          trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
          cur_level := cl_bt, unassigned := unass_bt },
        scratch := sc_bt })
    (hbt_wo : ∀ F0' F_cur', FullOtfsWitnessInv c F0' F_cur' s_c.core → 0 < s_c.core.cur_level →
      Full.FullWitnessInv c F0' F_cur' { s_c.core with
        vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
        trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
        cur_level := cl_bt, unassigned := unass_bt }) :
    let s_bt : FullState :=
      { core := { s_c.core with
          vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
          trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
          cur_level := cl_bt, unassigned := unass_bt },
        scratch := sc_bt }
    Full.FullSparseInvW c F0 F_cur s_bt ∧ s_bt.core.cur_level = 0 ∧
    s_bt.core.cur_vars = s.core.cur_vars ∧ s_bt.core.fuel = s.core.fuel ∧
    s_bt.core.dense_mode = s.core.dense_mode ∧ s_bt.scratch.work_stk2 = s.scratch.work_stk2 ∧
    s_bt.core.tmp = s_c.core.tmp := by
  intro s_bt
  have hw_bt := hbt_wo F0 F_cur hsc_otfs.2.1 (by omega)
  have hsp : Full.FullSparseInvW c F0 F_cur s_bt := by
    refine ⟨hbt_len, hw_bt, hsc_otfs.2.2.1, ?_,
      FullExtScratchOk.of_pres hsc_otfs.2.2.2.2.1 hbt_pres.1
        (fun _ h => by unfold fullArenaClauseRefs fullArenaClauseRefsCore at h ⊢; exact h),
      hsc_otfs.2.2.2.2.2⟩
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
      fullArenaClauseGarb fullArenaClauseGarbCore fullArenaClauseLits
      fullArenaClauseLitsCore fullArenaClauseSizeCore fullArenaHdrCore
    exact hsc_otfs.2.2.2.1
  exact ⟨hsp, by dsimp only [s_bt]; rw [hbt_cl]; exact Nat.min_zero _,
    hcv_c, hfu_c, hdm_c, hbt_pres.2.2.1.trans hws2_c, rfl⟩

theorem p2_lvl_pos_of_lt {c : FullCfg} {s s1 : FullState} {cut v : Nat}
    (hok : FailedStateOk c s s1 cut) (hv_lt : v < s1.core.lvl.length)
    (hpos : (0#32).toNat < (s1.core.lvl[v]'hv_lt).toNat) :
    0 < (s.core.lvl[v]?.getD 0#32).toNat := by
  have heql : s1.core.lvl[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 := by rw [hok.core]
  rw [← heql, List.getElem?_eq_getElem hv_lt, Option.getD_some]
  exact hpos

theorem p2_lvl0_of_nlt {c : FullCfg} {s s1 : FullState} {cut v : Nat}
    (hok : FailedStateOk c s s1 cut) (hv_lt : v < s1.core.lvl.length)
    (hno : ¬ (0#32).toNat < (s1.core.lvl[v]'hv_lt).toNat) :
    (s.core.lvl[v]?.getD 0#32).toNat = 0 := by
  have heql : s1.core.lvl[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 := by rw [hok.core]
  rw [← heql, List.getElem?_eq_getElem hv_lt, Option.getD_some]
  have h0 : (0#32 : BitVec 32).toNat = 0 := rfl
  omega

theorem p2_push_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut t : Nat}
    {s s1 : FullState} {q : BitVec 32}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hcl1 : s.core.cur_level = 1)
    (hok : FailedStateOk c s s1 cut) (ht_le : t ≤ s.core.trail_end)
    (hq_lt : q.toNat < 2 * s.core.cur_vars)
    (hmrk0 : s1.core.mrk[q.toNat / 2]?.getD 0#8 = 0#8)
    (hlvl_pos : 0 < (s.core.lvl[q.toNat / 2]?.getD 0#32).toNat)
    (hq_t : ∃ m < t, (s.core.trl[m]?.getD 0#32).toNat = q.toNat ^^^ 1)
    (hq_cut : ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = q.toNat ^^^ 1) :
    let ov := q.toNat / 2
    let s2 : FullState :=
      { core := { s1.core with mrk := s1.core.mrk.set ov 1#8,
                               min_clr_len := s1.core.min_clr_len + 1 }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len (q >>> 1) } }
    s1.core.min_clr_len < s.core.cur_vars ∧
    s1.core.min_clr_len < 2 ^ 64 ∧
    (BitVec.ofNat 64 s1.core.min_clr_len).toNat < s1.scratch.work_stk1.length ∧
    (BitVec.ofNat 64 s1.core.min_clr_len + 1).toNat = s1.core.min_clr_len + 1 ∧
    FailedStateOk c s s2 cut ∧
    (flIdxs s.core s2.core.mrk t).length = (flIdxs s.core s1.core.mrk t).length + 1 ∧
    (∀ l ∈ flLits s.core s1.core.mrk t, l ∈ flLits s.core s2.core.mrk t) ∧
    ((cnfOfClauses F_cur).EntailsClause (cnfClause [q.toNat ^^^ 1]) ∨
      q.toNat ∈ flLits s.core s2.core.mrk t) := by
  intro ov s2
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hok.len.core_ok.cur_vars_le
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
  have hov_lt : ov < s.core.cur_vars := Nat.div_lt_of_lt_mul hq_lt
  obtain ⟨hmcl_lt, hok2, hlen2, hpres2, hin2⟩ :=
    fl_mark_lit_push hw hcl1 hok ht_le hq_lt hmrk0 hlvl_pos hq_t hq_cut
  have hmcl_eq : BitVec.ofNat 32 ov = q >>> 1 := p2_bv32_lshr_eq
  have hmcl64 : s1.core.min_clr_len < 2 ^ 64 := by omega
  have hws_lt : (BitVec.ofNat 64 s1.core.min_clr_len).toNat < s1.scratch.work_stk1.length := by
    rw [bv64_ofNat_toNat hmcl64, hok.len.scratch_ok.work_stk1_len]; omega
  have hmcl1 : (BitVec.ofNat 64 s1.core.min_clr_len + 1).toNat = s1.core.min_clr_len + 1 := by
    rw [show (1 : BitVec 64) = 1#64 from rfl,
      fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat hmcl64]; omega), bv64_ofNat_toNat hmcl64]
  refine ⟨hmcl_lt, hmcl64, hws_lt, hmcl1,
    by simpa only [s2, ov, hmcl_eq] using hok2,
    by simpa only [s2, ov, hmcl_eq] using hlen2,
    by simpa only [s2, ov, hmcl_eq] using hpres2,
    by simpa only [s2, ov, hmcl_eq] using hin2⟩

theorem p2_arena_clause_sz {c : FullCfg} {s s1 : FullState}
    (hcl : s.LengthsOk c) (hl1 : s1.LengthsOk c) (hcore : s1.core.arena = s.core.arena)
    (_hal_eq : s1.core.arena_len = s.core.arena_len) {r32 : BitVec 32} {cref : Nat}
    (hr_eq : r32.toNat = cref)
    (hwf : cref + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore s.core cref ∧
      cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena_len ∧
      s.core.arena_len ≤ c.arena_cap ∧ c.arena_cap = s.core.arena.length) :
    let rsz := s1.core.arena[(r32.setWidth 64 + 2#64).toNat]'(by
      have := c.harena; unfold dimacsBound at this
      rw [hl1.core_ok.arena_len_arr, BitVec.toNat_add, fl_bv32_setWidth64,
        show (2#64 : BitVec 64).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega : r32.toNat + 2 < 2 ^ 64)]
      have := hcl.core_ok.arena_len_le; omega)
    (r32.setWidth 64 + 2#64).toNat < s1.core.arena.length ∧
    rsz.toNat = fullArenaClauseSizeCore s.core r32.toNat ∧
    cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length ∧
    (fullArenaClauseLitsCore s.core cref).length = rsz.toNat := by
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hal_le := hl1.core_ok.arena_len_le
  have hadd2 : (r32.setWidth 64 + 2#64).toNat < s1.core.arena.length := by
    rw [hl1.core_ok.arena_len_arr, BitVec.toNat_add, fl_bv32_setWidth64,
      show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega : r32.toNat + 2 < 2 ^ 64)]
    omega
  have hrsz_eq : (s1.core.arena[(r32.setWidth 64 + 2#64).toNat]'hadd2).toNat =
      fullArenaClauseSizeCore s.core r32.toNat := by
    rw [hr_eq]; unfold fullArenaClauseSizeCore
    have hidx : cref + 2 < s.core.arena.length := by
      rw [hcl.core_ok.arena_len_arr]; have := hcl.core_ok.arena_len_le; omega
    have hget : s1.core.arena[(r32.setWidth 64 + 2#64).toNat]'hadd2 =
        s.core.arena[cref + 2]'hidx := by
      refine p2_getElem_congr_list hcore ?_
      rw [BitVec.toNat_add, fl_bv32_setWidth64, show (2#64 : BitVec 64).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega : r32.toNat + 2 < 2 ^ 64), hr_eq]
    rw [hget, List.getElem?_eq_getElem hidx, Option.getD_some]
  have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    rw [hcl.core_ok.arena_len_arr]; exact Nat.le_trans hwf.2.2.1 hcl.core_ok.arena_len_le
  have hlen_lits : (fullArenaClauseLitsCore s.core cref).length =
      (s1.core.arena[(r32.setWidth 64 + 2#64).toNat]'hadd2).toNat := by
    rw [fl_arenaClauseLitsCore_length hbd, ← hr_eq]; exact hrsz_eq.symm
  exact ⟨hadd2, hrsz_eq, hbd, hlen_lits⟩

theorem p2_arena_clause_lit {c : FullCfg} {s sj : FullState}
    (_hcl : s.LengthsOk c) (_hlj : sj.LengthsOk c) (hcore : sj.core.arena = s.core.arena)
    {r32 j : BitVec 32} {cref : Nat} (hr_eq : r32.toNat = cref)
    (hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length)
    (hj_lt : j.toNat < fullArenaClauseSizeCore s.core cref) :
    have har_cap := c.harena
    let _ := har_cap
    have hlt_ar : (r32.setWidth 64 + 3#64 + j.setWidth 64).toNat < sj.core.arena.length := by
      have := c.harena; unfold dimacsBound at this
      have : sj.core.arena.length = s.core.arena.length := by rw [hcore]
      rw [this, BitVec.toNat_add, BitVec.toNat_add, fl_bv32_setWidth64, fl_bv32_setWidth64,
        show (3#64 : BitVec 64).toNat = 3 from rfl,
        Nat.mod_eq_of_lt (by omega : r32.toNat + 3 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : r32.toNat + 3 + j.toNat < 2 ^ 64), hr_eq]
      omega
    (r32.setWidth 64 + 3#64 + j.setWidth 64).toNat < sj.core.arena.length ∧
    j.toNat < (fullArenaClauseLitsCore s.core cref).length ∧
    (fullArenaClauseLitsCore s.core cref)[j.toNat]'(by
      rw [fl_arenaClauseLitsCore_length hbd]; exact hj_lt) =
      (sj.core.arena[(r32.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hlt_ar).toNat ∧
    (sj.core.arena[(r32.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hlt_ar).toNat ∈
      fullArenaClauseLitsCore s.core cref := by
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hlen_eq : sj.core.arena.length = s.core.arena.length := by rw [hcore]
  have har_j : cref + 3 + j.toNat < s.core.arena.length := by omega
  have hlt_ar : (r32.setWidth 64 + 3#64 + j.setWidth 64).toNat < sj.core.arena.length := by
    rw [hlen_eq, BitVec.toNat_add, BitVec.toNat_add, fl_bv32_setWidth64, fl_bv32_setWidth64,
      show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega : r32.toNat + 3 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : r32.toNat + 3 + j.toNat < 2 ^ 64), hr_eq]
    exact har_j
  have hlen_lits : j.toNat < (fullArenaClauseLitsCore s.core cref).length := by
    rw [fl_arenaClauseLitsCore_length hbd]; exact hj_lt
  have hget : (fullArenaClauseLitsCore s.core cref)[j.toNat]'hlen_lits =
      (sj.core.arena[(r32.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hlt_ar).toNat := by
    rw [fl_arenaClauseLitsCore_getElem hbd hj_lt hlen_lits har_j]
    refine congrArg BitVec.toNat (p2_getElem_congr_list hcore.symm ?_)
    rw [BitVec.toNat_add, BitVec.toNat_add, fl_bv32_setWidth64, fl_bv32_setWidth64,
      show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega : r32.toNat + 3 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : r32.toNat + 3 + j.toNat < 2 ^ 64), hr_eq]
  refine ⟨hlt_ar, hlen_lits, hget, ?_⟩
  rw [← hget]; exact List.getElem_mem _

end LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
