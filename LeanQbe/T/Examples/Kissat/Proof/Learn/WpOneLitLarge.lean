/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Learn.WpOneLitHelpers
public import LeanQbe.T.Examples.Kissat.Src.Learn
import LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Large-Clause Branch for `full_one_lit_confl` (`Proof.Learn.WpOneLitLarge`)

Proves `oneLit_large_branch_wp` directly on `Src.Learn.full_one_lit_confl_body` when
`s.core.confl_type ≠ 1#64` (`0` legacy imports, `0` `@[expose]` on theorems/sections,
`<= 100` cols, every decl `<= 450` lines).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Learn

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Learn
open LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers

private theorem oneLit_scan_take_hi {s : FullState} {cref forcedv li : BitVec 32}
    {i : Nat} {clvlv jlvlv cntv ll : BitVec 64}
    (hcl_le : clvlv.toNat ≤ s.core.cur_level)
    (hi0 : i = 0 → clvlv = 0#64 ∧ jlvlv = 0#64 ∧ cntv = 0#64 ∧ forcedv = 0xFFFFFFFF#32)
    (hipos : 0 < i → 1 ≤ cntv.toNat ∧
      (∀ q < i, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat / 2]?.getD
        0#32).toNat ≤ clvlv.toNat) ∧
      (∃ q < i, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat / 2]?.getD
        0#32).toNat = clvlv.toNat))
    (hli_get : s.core.arena[cref.toNat + 3 + i]?.getD 0#32 = li)
    (hll_val : ll.toNat = (s.core.lvl[(s.core.arena[cref.toNat + 3 + i]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat)
    (hll_c0_lt : ll.toNat ≤ s.core.cur_level)
    (hjcond : cntv = 0#64 ∨ (cntv ≠ 0#64 ∧ clvlv.toNat < ll.toNat)) :
    let jl' := if cntv = 0#64 then 0#64 else clvlv
    ll.toNat ≤ s.core.cur_level ∧ jl'.toNat ≤ s.core.cur_level ∧
    1 ≤ (1#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64).toNat ≤ i + 1 ∧
    (∀ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat ≤ ll.toNat) ∧
    (∃ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat = ll.toNat) ∧
    ((1#64 : BitVec 64) = 1#64 → ∃ q_f < i + 1,
      li = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 ∧
      (s.core.lvl[li.toNat / 2]?.getD 0#32).toNat = ll.toNat ∧
      (0 < ll.toNat → jl'.toNat < ll.toNat) ∧
      ∀ q' < i + 1, q' ≠ q_f →
        (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat /
          2]?.getD 0#32).toNat ≤ jl'.toNat) := by
  intro jl'
  have hall_i : ∀ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat ≤ ll.toNat := fun q hq => by
    by_cases hqi : q = i
    · subst hqi; exact Nat.le_of_eq hll_val.symm
    · rcases hjcond with hc0 | hlt_c
      · cases Nat.eq_zero_or_pos i with
        | inl hi => subst hi; omega
        | inr hip => have := (hipos hip).1; rw [hc0] at this; simp at this
      · have hpi : 0 < i := Nat.lt_of_le_of_ne (Nat.zero_le _) fun he =>
          hlt_c.1 (hi0 he.symm).2.2.1
        exact Nat.le_trans ((hipos hpi).2.1 q (by omega)) (Nat.le_of_lt hlt_c.2)
  refine ⟨hll_c0_lt, by dsimp only [jl']; split; simp; exact hcl_le, Nat.le_refl 1,
    Nat.le_trans (by decide) (Nat.le_add_left 1 i), hall_i,
    ⟨i, Nat.lt_succ_self i, by rw [← hll_val]⟩, fun _ => ⟨i, Nat.lt_succ_self i,
      hli_get.symm, by rw [← hli_get]; exact hll_val.symm,
      fun _ => ?_, fun q' hq' _ => ?_⟩⟩
  · dsimp only [jl']; split; simp [‹0 < ll.toNat›]; exact (hjcond.resolve_left ‹_›).2
  · dsimp only [jl']; split
    · rename_i hc0; cases Nat.eq_zero_or_pos i with
      | inl hi => subst hi; omega
      | inr hip => have := (hipos hip).1; rw [hc0] at this; simp at this
    · rename_i hne0
      have hpi : 0 < i := Nat.lt_of_le_of_ne (Nat.zero_le _) fun he =>
        hne0 (hi0 he.symm).2.2.1
      exact (hipos hpi).2.1 q' (by omega)

private theorem oneLit_scan_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut csz_val : Nat} {s : FullState} {cref : BitVec 32}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hcr_ref : s.core.confl_ref.toNat ∈
      fullArenaClauseRefs s) (hcr_ng : fullArenaClauseGarb s s.core.confl_ref.toNat = false)
    (hcr_f : ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
      s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hcref_eq : cref.toNat = s.core.confl_ref.toNat) (hcsz_bd : cref.toNat + 3 + csz_val ≤
      s.core.arena_len) (har_le : s.core.arena_len ≤ c.arena_cap)
    (har_len : s.core.arena.length = c.arena_cap) (hcsz_val : csz_val =
      fullArenaClauseSize s cref.toNat)
    (hscan_lits : ∀ q < csz_val,
      let l := s.core.arena[cref.toNat + 3 + q]?.getD 0#32
      l.toNat ∈ fullArenaClauseLits s cref.toNat ∧ l.toNat < 2 * s.core.cur_vars ∧
      (s.core.lvl[l.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
    (hall_le : ∀ q < csz_val, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat ≤ 0) : F0.Unsat := by
  have hsz_core : fullArenaClauseSizeCore s.core s.core.confl_ref.toNat = csz_val := by
    unfold fullArenaClauseSize at hcsz_val; rw [← hcref_eq, hcsz_val]
  refine unsat_of_level0_conflict hw hcr_ref hcr_ng fun l hl => ?_
  rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_core, ← hcref_eq]; omega)] at hl
  obtain ⟨q, hq, hql⟩ := hl
  have hq' : q < csz_val := by rwa [hsz_core] at hq
  have hbd_q : cref.toNat + 3 + q < s.core.arena.length := by omega
  have hql' : (s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat = l := by
    rw [List.getElem?_eq_getElem hbd_q, Option.getD_some]
    exact (congrArg BitVec.toNat (getElem_eq_of_idx (by omega))).trans hql
  have hlv0 := hall_le q hq'
  exact ⟨hcr_f l (by rw [← hql', ← hcref_eq]; exact (hscan_lits q hq').1),
    Nat.eq_zero_of_le_zero (by rwa [hql'] at hlv0)⟩

private theorem oneLit_large_exit0_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut1 : Nat} {s s1 s_cur : FullState} {cref : BitVec 32} {clvlv : BitVec 64}
    (hbin : s.core.confl_type ≠ 1#64) (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvlv.toNat)
    (hcref_eq : cref.toNat = s.core.confl_ref.toNat)
    (hvals_c : s_cur.core.vals = s1.core.vals) (hlvl_c : s_cur.core.lvl = s1.core.lvl)
    (htrl_c : s_cur.core.trl = s1.core.trl) (hcl_c : s_cur.core.cur_level = clvlv.toNat)
    (hct_c : s_cur.core.confl_type = s1.core.confl_type)
    (hcr_c : s_cur.core.confl_ref = s1.core.confl_ref)
    (hcref_c : cref.toNat ∈ fullArenaClauseRefsCore s_cur.core)
    (hng_c : fullArenaClauseGarbCore s_cur.core cref.toNat = false)
    (hlits_c : ∀ q, q ∈ fullArenaClauseLitsCore s_cur.core cref.toNat ↔
      q ∈ fullArenaClauseLits s s.core.confl_ref.toNat) :
    FullConflictOkCut F_cur cut1 s_cur := by
  have hct_ne1 : s_cur.core.confl_type ≠ 1#64 := by rw [hct_c, hobt.confl_type_eq]; exact hbin
  rcases hobt.confl1 with ⟨hcf1_w, hcf1_cut⟩
  rcases hcf1_w with ⟨hbad, _⟩ | ⟨hct2, _, _, hf1⟩
  · exact absurd (hobt.confl_type_eq.symm.trans hbad) hbin
  · have hlits_s1 : ∀ l, l ∈ fullArenaClauseLits s_cur s_cur.core.confl_ref.toNat →
        l ∈ fullArenaClauseLits s1 s1.core.confl_ref.toNat := by
      intro l hl; rw [fullArenaClauseLits, hcr_c, hobt.confl_ref_eq, ← hcref_eq] at hl
      have hls := (hlits_c l).mp hl
      simpa only [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore,
        hobt.confl_ref_eq, hcref_eq, hobt.arena_eq] using hls
    refine ⟨Or.inr ⟨hct_c.trans hct2, ?_, ?_, fun l hl => ?_⟩, ?_⟩
    · rw [hcr_c, hobt.confl_ref_eq, ← hcref_eq]; exact hcref_c
    · rw [hcr_c, hobt.confl_ref_eq, ← hcref_eq]; exact hng_c
    · rw [hvals_c]; exact hf1 l (hlits_s1 l hl)
    · rw [ite_eq_right hct_ne1]
      rw [ite_eq_right (fun h => hbin (hobt.confl_type_eq.symm.trans h))] at hcf1_cut
      intro l hl hlv; rw [hlvl_c, hcl_c, ← hobt.cl1_eq] at hlv
      obtain ⟨m_t, hm_cut, hm_eq⟩ := hcf1_cut l (hlits_s1 l hl) hlv
      exact ⟨m_t, hm_cut, by rw [htrl_c]; exact hm_eq⟩

private theorem oneLit_large_exit1_prep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut1 csz_val q_f : Nat} {s s1 s_cur : FullState} {cref forcedv : BitVec 32}
    {clvlv jlvlv : BitVec 64}
    (hlen : s.LengthsOk c) (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvlv.toNat)
    (hcr_f : ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
      s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hcref_eq : cref.toNat = s.core.confl_ref.toNat) (hcsz_bd : cref.toNat + 3 + csz_val ≤
      s.core.arena_len) (hcsz_val : csz_val = fullArenaClauseSize s cref.toNat)
    (hscan_lits : ∀ q < csz_val,
      let l := s.core.arena[cref.toNat + 3 + q]?.getD 0#32
      l.toNat ∈ fullArenaClauseLits s cref.toNat ∧ l.toNat < 2 * s.core.cur_vars ∧
      (s.core.lvl[l.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
    (hcl_pos : 0 < clvlv.toNat)
    (hqf_lt : q_f < csz_val) (hfq_eq : forcedv = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32)
    (hfq_lv : (s.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvlv.toNat)
    (hjl_lt : 0 < clvlv.toNat → jlvlv.toNat < clvlv.toNat)
    (hoth : ∀ q' < csz_val, q' ≠ q_f →
      (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat / 2]?.getD
        0#32).toNat ≤ jlvlv.toNat)
    (hvals_c : s_cur.core.vals = s1.core.vals) (hlvl_c : s_cur.core.lvl = s1.core.lvl)
    (hlits_c : ∀ q, q ∈ fullArenaClauseLitsCore s_cur.core cref.toNat ↔
      q ∈ fullArenaClauseLits s s.core.confl_ref.toNat) :
    forcedv.toNat ∈ fullArenaClauseLitsCore s_cur.core cref.toNat ∧
    (∀ q ∈ fullArenaClauseLitsCore s_cur.core cref.toNat, q = forcedv.toNat ∨
      (s_cur.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
        (s_cur.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat)) ∧
    (s_cur.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvlv.toNat ∧
    forcedv.toNat < 2 * s.core.cur_vars := by
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hforced_m := hscan_lits q_f hqf_lt; rw [← hfq_eq] at hforced_m
  refine ⟨(hlits_c forcedv.toNat).mpr (by simpa only [fullArenaClauseLits, hcref_eq] using
    hforced_m.1), fun q hq => ?_, ?_, hforced_m.2.1⟩
  · have hqs := (hlits_c q).mp hq
    rw [fullArenaClauseLits, ← hcref_eq, mem_fullArenaClauseLitsCore_iff (by
      rw [show fullArenaClauseSizeCore s.core cref.toNat = csz_val from hcsz_val.symm, har_len]
      exact Nat.le_trans hcsz_bd har_le)] at hqs
    obtain ⟨p, hp, hpeq⟩ := hqs
    have hp_lt : p < csz_val := by simpa only [hcsz_val, fullArenaClauseSize, hcref_eq] using hp
    have hqp : (s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat = q := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hpeq]
    by_cases hpf : p = q_f
    · left; subst hpf; rw [← hqp, ← hfq_eq]
    · right
      have hq_lt2 : q < 2 * s.core.cur_vars := by rw [← hqp]; exact (hscan_lits p hp_lt).2.1
      have hle_j : (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat := by
        rw [← hqp]; exact hoth p hp_lt hpf
      have hql_le : (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ clvlv.toNat :=
        Nat.le_trans hle_j (Nat.le_of_lt (hjl_lt hcl_pos))
      have hqf_s : s.core.vals[q]?.getD 0#8 = 0xFF#8 := hcr_f q (by
        rw [← hqp]; simpa [fullArenaClauseLits, hcref_eq] using (hscan_lits p hp_lt).1)
      refine ⟨by rw [hvals_c, hobt.vals_keep q hq_lt2 hql_le, hqf_s],
        by rw [hlvl_c, hobt.lvl_keep q hq_lt2 hqf_s hql_le]; exact hle_j⟩
  · rw [hlvl_c, hobt.lvl_keep _ hforced_m.2.1 (hcr_f _ (hcref_eq ▸ hforced_m.1)) (by omega)]
    exact hfq_lv

private theorem oneLit_arena_off3_bds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut1 : Nat} {s_cur : FullState} {cref : BitVec 32} {csz_val pos_n : Nat}
    (hlen_c : s_cur.LengthsOk c) (hw_c : FullWitnessCutInv c F0 F_cur cut1 s_cur.core)
    (hcref_c : cref.toNat ∈ fullArenaClauseRefsCore s_cur.core)
    (hng_c : fullArenaClauseGarbCore s_cur.core cref.toNat = false)
    (hsz_c : fullArenaClauseSizeCore s_cur.core cref.toNat = csz_val)
    (hpos_lt : pos_n < csz_val) (hcr32 : cref.toNat < 2 ^ 31 - 1)
    (hcsz_bd_c : cref.toNat + 3 + csz_val ≤ s_cur.core.arena_len) :
    let idx := (cref.setWidth 64 + 3 + (BitVec.ofNat 32 pos_n).setWidth 64).toNat
    ∃ (hbd : idx < s_cur.core.arena.length),
      idx = cref.toNat + 3 + pos_n ∧
      s_cur.core.arena[idx]'hbd = s_cur.core.arena[cref.toNat + 3 + pos_n]?.getD 0#32 ∧
      (s_cur.core.arena[cref.toNat + 3 + pos_n]?.getD 0#32).toNat < 2 * s_cur.core.cur_vars ∧
      ((s_cur.core.arena[idx]'hbd >>> 1).setWidth 64).toNat < s_cur.core.lvl.length := by
  have har_len_c := hlen_c.core_ok.arena_len_arr
  have har_le_c := hlen_c.core_ok.arena_len_le
  have hlvl_len_c := hlen_c.core_ok.lvl_len
  have hcv_le_c := hlen_c.core_ok.cur_vars_le
  have hc_ar := c.harena; have hc_mv := c.hmaxv; unfold dimacsBound at hc_ar hc_mv
  have hcr_z : (cref.setWidth 64 + 3 + (BitVec.ofNat 32 pos_n).setWidth 64).toNat =
      cref.toNat + 3 + pos_n := by
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
      zext_toNat (BitVec.ofNat 32 pos_n) (by decide), Proof.Spec.bv32_ofNat_toNat (by omega),
      show (3 : BitVec 64).toNat = 3 from rfl]; omega
  have hbd : (cref.setWidth 64 + 3 + (BitVec.ofNat 32 pos_n).setWidth 64).toNat <
      s_cur.core.arena.length := by rw [hcr_z, har_len_c]; omega
  have heq : s_cur.core.arena[(cref.setWidth 64 + 3 +
      (BitVec.ofNat 32 pos_n).setWidth 64).toNat]'hbd =
      s_cur.core.arena[cref.toNat + 3 + pos_n]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by rw [har_len_c]; omega), Option.getD_some]
    exact getElem_eq_of_idx hcr_z
  have hlt : (s_cur.core.arena[cref.toNat + 3 + pos_n]?.getD 0#32).toNat <
      2 * s_cur.core.cur_vars := by
    have hm : (s_cur.core.arena[cref.toNat + 3 + pos_n]?.getD 0#32).toNat ∈
        fullArenaClauseLitsCore s_cur.core cref.toNat := by
      rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_c]; omega)]
      exact ⟨pos_n, by rw [hsz_c]; omega,
        by rw [List.getElem?_eq_getElem (by rw [har_len_c]; omega), Option.getD_some]⟩
    exact hw_c.arena.lits_lt cref.toNat hcref_c hng_c _ hm
  have hlt_l : ((s_cur.core.arena[(cref.setWidth 64 + 3 +
      (BitVec.ofNat 32 pos_n).setWidth 64).toNat]'hbd >>> 1).setWidth 64).toNat <
      s_cur.core.lvl.length := by
    rw [bv_c0_zext32_64, bv32_lshr_1, heq, hlvl_len_c]; omega
  exact ⟨hbd, hcr_z, heq, hlt, hlt_l⟩

private structure OneLitPosInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut1 csz_val : Nat) (cref : BitVec 32) (clvlv : BitVec 64)
    (s s1 s_cur : FullState) : Prop where
  len : s_cur.LengthsOk c
  hw : FullWitnessCutInv c F0 F_cur cut1 s_cur.core
  marks : FullLitMarksClear c s_cur
  nodup : FullArenaVarsNodup s_cur
  ext : FullExtScratchOk c s_cur
  cv : s_cur.core.cur_vars = s.core.cur_vars
  cl : s_cur.core.cur_level = clvlv.toNat
  fuel : s_cur.core.fuel = s.core.fuel
  ws2 : s_cur.scratch.work_stk2 = s.scratch.work_stk2
  dm : s_cur.core.dense_mode = 0#64
  prob : s_cur.core.probing = s.core.probing
  vals : s_cur.core.vals = s1.core.vals
  lvl : s_cur.core.lvl = s1.core.lvl
  trl : s_cur.core.trl = s1.core.trl
  te : s_cur.core.trail_end = s1.core.trail_end
  arlen : s_cur.core.arena_len = s1.core.arena_len
  ct : s_cur.core.confl_type = s1.core.confl_type
  cr : s_cur.core.confl_ref = s1.core.confl_ref
  cref_mem : cref.toNat ∈ fullArenaClauseRefsCore s_cur.core
  ng : fullArenaClauseGarbCore s_cur.core cref.toNat = false
  sz : fullArenaClauseSizeCore s_cur.core cref.toNat = csz_val
  lits : ∀ q, q ∈ fullArenaClauseLitsCore s_cur.core cref.toNat ↔
    q ∈ fullArenaClauseLits s s.core.confl_ref.toNat

private theorem oneLit_scan_lits_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut csz_val : Nat} {s : FullState} {cref : BitVec 32}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hcr_ref : s.core.confl_ref.toNat ∈ fullArenaClauseRefs s)
    (hcr_ng : fullArenaClauseGarb s s.core.confl_ref.toNat = false)
    (hcr_f : ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
      s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hcref_eq : cref.toNat = s.core.confl_ref.toNat)
    (hcsz_val : csz_val = fullArenaClauseSize s cref.toNat)
    (hcsz_bd : cref.toNat + 3 + csz_val ≤ s.core.arena_len)
    (har_le : s.core.arena_len ≤ c.arena_cap) (har_len : s.core.arena.length = c.arena_cap) :
    ∀ q < csz_val,
      let l := s.core.arena[cref.toNat + 3 + q]?.getD 0#32
      l.toNat ∈ fullArenaClauseLits s cref.toNat ∧ l.toNat < 2 * s.core.cur_vars ∧
      (s.core.lvl[l.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level := fun q hq => by
  have hq' : q < fullArenaClauseSizeCore s.core cref.toNat := by
    simpa only [hcsz_val, fullArenaClauseSize] using hq
  have hbd_q : cref.toNat + 3 + q < s.core.arena.length := by omega
  have hm' : (s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core cref.toNat := by
    rw [mem_fullArenaClauseLitsCore_iff (by
      rw [show fullArenaClauseSizeCore s.core cref.toNat = csz_val from hcsz_val.symm]; omega)]
    exact ⟨q, hq', by rw [List.getElem?_eq_getElem hbd_q, Option.getD_some]⟩
  have hlt := hw.arena.lits_lt s.core.confl_ref.toNat hcr_ref hcr_ng _
    (by simpa [hcref_eq] using hm')
  obtain ⟨m0, hm0, hm0_eq⟩ := (hw.vals_false_iff _ hlt).mp
    (hcr_f _ (by simpa [fullArenaClauseLits, hcref_eq] using hm'))
  have hlvl_le := hw.lvl_le m0 hm0; rw [hm0_eq, fullInv_var_xor1] at hlvl_le
  rw [← hcref_eq] at hlt hlvl_le
  exact ⟨by simpa [fullArenaClauseLits, hcref_eq] using hm', hlt, hlvl_le⟩

private theorem oneLit_large_bt_lt {c : FullCfg} {csz_val : Nat} {s : FullState}
    {cref : BitVec 32} {clvlv : BitVec 64} (hbin : s.core.confl_type ≠ 1#64)
    (hcref_eq : cref.toNat = s.core.confl_ref.toNat)
    (hcsz_val : csz_val = fullArenaClauseSize s cref.toNat)
    (hcsz_bd : cref.toNat + 3 + csz_val ≤ s.core.arena_len)
    (har_le : s.core.arena_len ≤ c.arena_cap) (har_len : s.core.arena.length = c.arena_cap)
    (hall_le : ∀ q < csz_val, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat ≤ clvlv.toNat) :
    ∀ l, (s.core.confl_type = 1#64 ∧
        (l = s.core.confl_lit0.toNat ∨ l = s.core.confl_lit1.toNat)) ∨
        (s.core.confl_type ≠ 1#64 ∧ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat) →
        (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvlv.toNat := fun l hl => by
  rcases hl with ⟨hbad, _⟩ | ⟨_, hmem⟩
  · exact absurd hbad hbin
  · rw [fullArenaClauseLits, ← hcref_eq, mem_fullArenaClauseLitsCore_iff (by
      rw [show fullArenaClauseSizeCore s.core cref.toNat = csz_val from hcsz_val.symm, har_len]
      exact Nat.le_trans hcsz_bd har_le)] at hmem
    obtain ⟨q, hq, hql⟩ := hmem
    have hq' : q < csz_val := by simpa only [hcsz_val, fullArenaClauseSize] using hq
    have hql' : (s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat = l := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hql]
    rw [← hql']; exact hall_le q hq'

private theorem oneLit_bv32_add1 {k : Nat} : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]; omega)

private theorem oneLit_bv64_pos {x : BitVec 64} (h : x ≠ 0#64) : 0 < x.toNat :=
  Nat.pos_of_ne_zero fun hz => h (BitVec.eq_of_toNat_eq hz)

public section

/-- Large-clause branch of `full_one_lit_confl` when `s.core.confl_type ≠ 1#64`. -/
theorem oneLit_large_branch_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hDet : ∀ args m Q X, fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hUnw : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hmarks : FullLitMarksClear c s)
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hcut_le : cut ≤ s.core.trail_end) (hconfl : FullConflictOkCut F_cur cut s)
    (hbin : s.core.confl_type ≠ 1#64) (hm : (FullMem c s ⋆ R) m)
    (hQ : OneLitPost c F0 F_cur s R Q) :
    Func.wp Γ full_one_lit_confl_body (c.hdr, ()) m Q X := by
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hmaxv := c.hmaxv; have harena := c.harena; unfold dimacsBound at hmaxv harena
  have har32 : c.arena_cap < 2 ^ 31 - 1 := by omega
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hconfl0 : FullConflictOkCut F_cur cut s := hconfl
  have hcr_lg : s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
      ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
    rcases hconfl.1 with ⟨h1, _⟩ | ⟨_, href, hng, hf⟩
    · exact absurd h1 hbin
    · exact ⟨href, hng, hf⟩
  obtain ⟨hcr_ref, hcr_ng, hcr_f⟩ := hcr_lg
  have hwf := hw.arena.refs_wf s.core.confl_ref.toNat hcr_ref
  have hwf_bd : s.core.confl_ref.toNat + 3 + fullArenaClauseSizeCore s.core
      s.core.confl_ref.toNat ≤ s.core.arena_len := Nat.le_trans hwf.2.2.1 hwf.2.2.2.1
  have hwf1 := hwf.1; have hwf21 := hwf.2.1; clear hwf
  have hcr_lt : s.core.confl_ref.toNat < 2 ^ 31 - 1 := by omega
  unfold Func.wp full_one_lit_confl_body
  c0_hsteps_nogrp
  · let cref := s.core.confl_ref.setWidth 32
    have hcref_eq : cref.toNat = s.core.confl_ref.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hcr32 : cref.toNat < 2 ^ 31 - 1 := by omega
    have hcsz_ge3 : 3 ≤ fullArenaClauseSize s cref.toNat := by
      unfold fullArenaClauseSize; rw [hcref_eq]; exact hwf21
    let csz_val := fullArenaClauseSize s cref.toNat
    have hcsz_bd : cref.toNat + 3 + csz_val ≤ s.core.arena_len := by
      dsimp only [csz_val]; unfold fullArenaClauseSize; rw [hcref_eq]
      have := hwf_bd; omega
    have hcsz_lt32 : csz_val < 2 ^ 32 := by
      dsimp only [csz_val]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      exact (s.core.arena[cref.toNat + 2]?.getD 0#32).isLt
    have hcref_bd2 : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
      rw [BitVec.toNat_add, zext_toNat cref (by decide)]; simp only [BitVec.reduceToNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hcsz_get : s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by omega) =
        BitVec.ofNat 32 csz_val := by
      apply BitVec.eq_of_toNat_eq
      rw [Proof.Spec.bv32_ofNat_toNat hcsz_lt32, getElem_eq_of_idx (hj := by omega) hcref_bd2]
      unfold csz_val fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hc_idx2 : (s.core.confl_ref.toNat % 2 ^ 32 +
        BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
      simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
    have hcsz_get_c0 {hpa} : (s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
        BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'hpa).toNat = csz_val := by
      rw [getElem_eq_of_idx (hj := by omega) hc_idx2]
      unfold csz_val fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hscan_lits :=
      oneLit_scan_lits_ok hw hcr_ref hcr_ng hcr_f hcref_eq rfl hcsz_bd har_le har_len
    refine wp_loop_group (fun rem (clvlv, jlvlv, cntv, forcedv, iv, ()) ml => ∃ i : Nat,
      ml = m ∧ rem = csz_val - i ∧ iv = BitVec.ofNat 32 i ∧
      OneLitScanInv s cref forcedv csz_val i clvlv jlvlv cntv) ?_ ?_
    · rintro L rem ⟨clvlv, jlvlv, cntv, forcedv, iv, ⟨⟩⟩ ml ih
        ⟨i, rfl, rfl, rfl, hile, hcl_le, hjl_le, hcnt_le, hi0, hipos, huniq⟩
      c0_hsteps_nogrp
      · have hilt : i < csz_val := by
          have hb : (BitVec.ofNat 32 i).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by omega)).toNat := ‹_›
          rw [hcsz_get, Proof.Spec.bv32_ofNat_toNat (Nat.lt_of_le_of_lt hile hcsz_lt32),
            Proof.Spec.bv32_ofNat_toNat hcsz_lt32] at hb; exact hb
        obtain ⟨hl_mem, hl_lt, hl_le⟩ := hscan_lits i hilt
        let li := s.core.arena[cref.toNat + 3 + i]'(by omega)
        let ll : BitVec 64 := (s.core.lvl[li.toNat / 2]?.getD 0#32).setWidth 64
        obtain ⟨hz_bd, hc_bd, hcr_i_bd, hli_get, hll_val, hli_idx, hli_lvl, hc0_lvl, hll_at'⟩ :=
          oneLit_scan_bds hlen hcv_le har32 hcsz_bd hilt hl_lt rfl
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64, i64, i32]) (fun (cl', jl', cnt', f', ()) ml2 =>
          ml2 = ml ∧ cl'.toNat ≤ s.core.cur_level ∧ jl'.toNat ≤ s.core.cur_level ∧
          1 ≤ cnt'.toNat ∧ cnt'.toNat ≤ i + 1 ∧
          (∀ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat /
            2]?.getD 0#32).toNat ≤ cl'.toNat) ∧
          (∃ q < i + 1, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat /
            2]?.getD 0#32).toNat = cl'.toNat) ∧
          (cnt' = 1#64 → ∃ q_f < i + 1, f' = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 ∧
            (s.core.lvl[f'.toNat / 2]?.getD 0#32).toNat = cl'.toNat ∧
            (0 < cl'.toNat → jl'.toNat < cl'.toNat) ∧
            ∀ q' < i + 1, q' ≠ q_f →
              (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat / 2]?.getD
                0#32).toNat ≤ jl'.toNat)) ?_ ?_
        · rintro _ ⟨cl', jl', cnt', f', ⟨⟩⟩ ml2
            ⟨rfl, hcl', hjl', hcnt1, hcnt_le', hall', hex', hu'⟩
          c0_hsteps
          rw [show BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) from
            BitVec.eq_of_toNat_eq (by bv_omega)]
          exact ih (csz_val - (i + 1)) _ ml2 (Nat.sub_lt (Nat.sub_pos_of_lt hilt) Nat.zero_lt_one)
            ⟨i + 1, rfl, rfl, rfl, hilt, hcl', hjl', hcnt_le', fun h0 => Nat.noConfusion h0,
              fun _ => ⟨hcnt1, hall', hex'⟩, fun _ => hu'⟩
        · intro Js1 hJs1
          have hll_c0_lt : ll.toNat ≤ s.core.cur_level := by rw [hll_val]; exact hl_le
          have hll_c0 {hpa hpl} :
              (s.core.lvl[(s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                3 + i % 2 ^ 32) % 2 ^ 64]'hpa).toNat / 2]'hpl).toNat = ll.toNat := by
            have hbd : li.toNat / 2 < s.core.lvl.length := by
              have h := hli_lvl; rw [bv_c0_zext32_64, bv32_lshr_1, hli_idx] at h; exact h
            have hc_idx : (s.core.confl_ref.toNat % 2 ^ 32 + 3 + i % 2 ^ 32) % 2 ^ 64 =
                cref.toNat + 3 + i := by omega
            have har_eq : s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                3 + i % 2 ^ 32) % 2 ^ 64]'hpa = li := by
              rw [getElem_eq_of_idx (hj := by omega) hc_idx, ← hli_get,
                List.getElem?_eq_getElem (by omega), Option.getD_some]
            rw [hll_val, hli_get, List.getElem?_eq_getElem hbd, Option.getD_some]
            exact congrArg BitVec.toNat (getElem_eq_of_idx (congrArg (·.toNat / 2) har_eq))
          have hll_bv_c0 {hpa hpl} : BitVec.setWidth 64 (s.core.lvl[(s.core.arena[(
              s.core.confl_ref.toNat % 2 ^ 32 + 3 +
              i % 2 ^ 32) % 2 ^ 64]'hpa).toNat / 2]'hpl) = ll := by
            apply BitVec.eq_of_toNat_eq; rw [zext_toNat _ (by decide), hll_c0]
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun () ml2 =>
            ml = ml2 ∧ (cntv = 0#64 ∨ (cntv ≠ 0#64 ∧ clvlv.toNat < ll.toNat))) ?_ ?_
          · rintro _ ⟨⟩ ml2 ⟨rfl, hjcond⟩
            refine wp_join_group (ts := [i64]) (fun (jl', ()) ml2 =>
              ml = ml2 ∧ jl' = if cntv = 0#64 then 0#64 else clvlv) ?_ ?_
            · rintro _ ⟨jl', ⟨⟩⟩ ml2 ⟨rfl, rfl⟩
              have hli_at' : ∀ pf, s.core.arena[((s.core.confl_ref.setWidth 32).setWidth 64 + 3 +
                  (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = li := fun _ =>
                (getElem_eq_of_idx (hj := hz_bd) rfl).trans hli_idx
              c0_hsteps; rw [hll_at', hli_at']
              exact hJs1 _ ml ⟨rfl, oneLit_scan_take_hi hcl_le hi0 hipos hli_get hll_val
                hll_c0_lt hjcond⟩
            · intro Jjl hJjl; c0_hsteps
              · exact hJjl (0#64, ()) ml ⟨rfl, by rw [ite_eq_left (by simpa using ‹cntv = 0›)]⟩
              · exact hJjl (clvlv, ()) ml
                  ⟨rfl, by rw [ite_eq_right (fun h => ‹¬ cntv = 0› (by simpa using h))]⟩
          · intro Jif hJif; c0_hsteps_nogrp
            · exact hJif () ml ⟨rfl, Or.inl (by simpa using ‹cntv = 0›)⟩
            · exact hJif () ml ⟨rfl, Or.inr ⟨fun h => ‹¬ cntv = 0› (by simpa using h),
                by rw [hll_c0] at hc; exact hc⟩⟩
            · have hne0 : cntv ≠ 0#64 := fun h => ‹¬ cntv = 0› (by simpa using h)
              have hpi : 0 < i := Nat.lt_of_le_of_ne (Nat.zero_le _) fun he =>
                hne0 (hi0 he.symm).2.2.1
              have hle_ll : ll.toNat ≤ clvlv.toNat := by rw [hll_c0] at hc; exact Nat.not_lt.mp hc
              refine wp_join_group (ts := [i64, i64]) (fun (jl', cnt', ()) ml2 =>
                ml = ml2 ∧ jl'.toNat ≤ s.core.cur_level ∧ 1 ≤ cnt'.toNat ∧
                cnt'.toNat ≤ i + 1 ∧
                (cnt' = 1#64 → ∃ q_f < i + 1,
                  forcedv = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 ∧
                  (s.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvlv.toNat ∧
                  (0 < clvlv.toNat → jl'.toNat < clvlv.toNat) ∧
                  ∀ q' < i + 1, q' ≠ q_f →
                    (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat / 2]?.getD
                      0#32).toNat ≤ jl'.toNat)) ?_ ?_
              · rintro _ ⟨jl', cnt', ⟨⟩⟩ ml2 ⟨rfl, hjl', hcnt1', hcnt_le', hu'⟩
                c0_hsteps
                exact hJs1 (clvlv, jl', cnt', forcedv, ()) ml
                  ⟨rfl, hcl_le, hjl', hcnt1', hcnt_le', fun q hq => by
                      by_cases hqi : q = i
                      · subst hqi; rw [← hll_val]; exact hle_ll
                      · exact (hipos hpi).2.1 q (by omega),
                    (hipos hpi).2.2.imp fun q ⟨hq, hqe⟩ => ⟨by omega, hqe⟩, hu'⟩
              · intro Js2 hJs2; c0_hsteps_nogrp
                · have heq_ll : ll = clvlv := by rw [hll_bv_c0] at hc; exact hc
                  refine wp_join_group (ts := [i64]) (fun (jl', ()) ml2 =>
                    ml = ml2 ∧ jl'.toNat ≤ s.core.cur_level) ?_ ?_
                  · rintro _ ⟨jl', ⟨⟩⟩ ml2 ⟨rfl, hjl'⟩; c0_hsteps
                    have hcnt_lt64 : cntv.toNat + 1 < 2 ^ 64 :=
                      Nat.lt_trans
                        (Nat.succ_lt_succ (Nat.lt_of_le_of_lt (Nat.le_trans hcnt_le hile)
                          hcsz_lt32))
                        (by decide)
                    have h1 := (hipos hpi).1
                    refine hJs2 _ ml ⟨rfl, hjl',
                      by rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]
                         rw [Nat.mod_eq_of_lt hcnt_lt64]; exact Nat.le_add_left 1 _,
                      by rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]
                         rw [Nat.mod_eq_of_lt hcnt_lt64]; exact Nat.succ_le_succ hcnt_le,
                      fun heq => by
                        have := congrArg BitVec.toNat heq; rw [BitVec.toNat_add] at this
                        simp only [BitVec.reduceToNat] at this
                        rw [Nat.mod_eq_of_lt hcnt_lt64] at this; omega⟩
                  · intro Jj hJj; c0_hsteps
                    · rw [hll_at']; exact hJj (ll, ()) ml ⟨rfl, hll_c0_lt⟩
                    · exact hJj (jlvlv, ()) ml ⟨rfl, hjl_le⟩
                · have hlt_ll : ll.toNat < clvlv.toNat := Nat.lt_of_le_of_ne hle_ll fun h =>
                    (fun hn => by rw [hll_bv_c0] at hc; exact hc hn) (BitVec.eq_of_toNat_eq h)
                  refine wp_join_group (ts := [i64]) (fun (jl', ()) ml2 =>
                    ml = ml2 ∧ jl'.toNat ≤ s.core.cur_level ∧
                    (cntv = 1#64 → 0 < clvlv.toNat → jl'.toNat < clvlv.toNat) ∧
                    ll.toNat ≤ jl'.toNat ∧ jlvlv.toNat ≤ jl'.toNat) ?_ ?_
                  · rintro _ ⟨jl', ⟨⟩⟩ ml2 ⟨rfl, hjl', hj_lt, hll_j, hj_j⟩; c0_hsteps
                    refine hJs2 _ ml ⟨rfl, hjl', (hipos hpi).1, by omega, fun h1 => ?_⟩
                    obtain ⟨q_f, hqf_lt, hf_eq, hf_lv, _, hoth⟩ := huniq hpi h1
                    refine ⟨q_f, by omega, hf_eq, hf_lv, hj_lt h1, fun q' hq' hq'n => ?_⟩
                    by_cases hqi : q' = i
                    · subst hqi; rw [← hll_val]; exact hll_j
                    · exact Nat.le_trans
                        (hoth q' (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hq') hqi) hq'n) hj_j
                  · intro Jj hJj; c0_hsteps
                    · rw [hll_at']
                      exact hJj (ll, ()) ml ⟨rfl, hll_c0_lt, fun _ _ => hlt_ll, Nat.le_refl _,
                        by have hgt : jlvlv.toNat < ll.toNat := by rw [hll_c0] at hc; exact hc
                           omega⟩
                    · exact hJj (jlvlv, ()) ml ⟨rfl, hjl_le,
                        fun h1 hpos => let ⟨_, _, _, _, hjl_lt, _⟩ := huniq hpi h1; hjl_lt hpos,
                        by rw [hll_c0] at hc; exact Nat.not_lt.mp hc, Nat.le_refl _⟩
      · have hi_ge : csz_val ≤ i := by
          have hnot : ¬ (BitVec.ofNat 32 i).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by omega)).toNat := ‹_›
          rw [hcsz_get, Proof.Spec.bv32_ofNat_toNat (Nat.lt_of_le_of_lt hile hcsz_lt32),
            Proof.Spec.bv32_ofNat_toNat hcsz_lt32] at hnot
          exact Nat.not_lt.mp hnot
        have hieq : i = csz_val := Nat.le_antisymm hile hi_ge; subst hieq
        have hcsz_pos : 0 < csz_val := by omega
        obtain ⟨_, hall_le, _⟩ := hipos hcsz_pos
        have hcl0 : clvlv = 0#64 := ‹_›
        have hunsat : F0.Unsat :=
          oneLit_scan_unsat hw hcr_ref hcr_ng hcr_f hcref_eq hcsz_bd har_le har_len rfl
            hscan_lits fun q hq => by have := hall_le q hq; rwa [hcl0] at this
        c0_clean; c0_steps
        exact hQ 20#64 s ml hlen (Or.inr (Or.inr (Or.inr rfl))) rfl rfl rfl hdm rfl hmarks
          hnd hext (fun h => absurd h hbin) (fun _ => ⟨hunsat, rfl⟩)
          (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm
      · have hi_ge : csz_val ≤ i := by
          have hnot : ¬ (BitVec.ofNat 32 i).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by omega)).toNat := ‹_›
          rw [hcsz_get, Proof.Spec.bv32_ofNat_toNat (Nat.lt_of_le_of_lt hile hcsz_lt32),
            Proof.Spec.bv32_ofNat_toNat hcsz_lt32] at hnot
          exact Nat.not_lt.mp hnot
        have hieq : i = csz_val := Nat.le_antisymm hile hi_ge; subst hieq
        have hcsz_pos : 0 < csz_val := by omega
        obtain ⟨_, hall_le, _⟩ := hipos hcsz_pos
        have hbt_lt := oneLit_large_bt_lt hbin hcref_eq rfl hcsz_bd har_le har_len hall_le
        have hcl_pos : 0 < clvlv.toNat := oneLit_bv64_pos ‹_›
        · refine wp_join_group (ts := []) (fun () m1 =>
            ∃ s1 cut1, OneLitBtInv c F0 F_cur s s1 cut1 clvlv.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
          · rintro _ ⟨⟩ m1 ⟨s1, cut1, hobt, hm1⟩
            clear ih hi0 hile hcnt_le hjl_le hcsz_get hwf1 hwf21 hwf_bd
            have hcref1_ref : cref.toNat ∈ fullArenaClauseRefsCore s1.core := by
              simpa only [fullArenaClauseRefsCore, hobt.arena_eq, hobt.arena_len_eq,
                hcref_eq] using hcr_ref
            have hcref1_ng : fullArenaClauseGarbCore s1.core cref.toNat = false := by
              simpa only [fullArenaClauseGarbCore, fullArenaHdrCore, hobt.arena_eq,
                hcref_eq] using hcr_ng
            have hcref1_sz : fullArenaClauseSizeCore s1.core cref.toNat = csz_val := by
              dsimp only [csz_val]; unfold fullArenaClauseSize fullArenaClauseSizeCore
              rw [hobt.arena_eq, hcref_eq]
            have hconfl_eq1 : ∀ q, q ∈ fullArenaClauseLitsCore s1.core cref.toNat ↔
                q ∈ fullArenaClauseLits s s.core.confl_ref.toNat := fun q => by
              simp only [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore,
                hobt.arena_eq, hcref_eq]
            c0_clean; c0_steps
            refine wp_loop_group (fun rem (posv, ()) ml_cur =>
              ∃ (pos_n : Nat) (s_cur : FullState),
                rem = 2 - pos_n ∧ pos_n ≤ 2 ∧ posv = BitVec.ofNat 32 pos_n ∧
                OneLitPosInv c F0 F_cur cut1 csz_val cref clvlv s s1 s_cur ∧
                (FullMem c s_cur ⋆ R) ml_cur) ?_ ?_
            · rintro L_pos rem ⟨posv, ⟨⟩⟩ ml_cur ih_pos
                ⟨pos_n, s_cur, rfl, hpos_le2, rfl, hp_inv, hm_c⟩
              c0_hsteps_nogrp
              · have hpos_lt2 : pos_n < 2 := by
                  have hb : (BitVec.ofNat 32 pos_n).toNat < (2#32).toNat := ‹_›
                  rw [Proof.Spec.bv32_ofNat_toNat (Nat.lt_of_le_of_lt hpos_le2 (by decide))] at hb
                  exact hb
                have hcsz_bd_c : cref.toNat + 3 + csz_val ≤ s_cur.core.arena_len := by
                  rw [hp_inv.arlen, hobt.arena_len_eq]; exact hcsz_bd
                obtain ⟨hpos_bd, hcr_pos_z, hlit_pos_eq, hlit_pos_lt, hlit_pos_bd_lvl⟩ :=
                  oneLit_arena_off3_bds hp_inv.len hp_inv.hw hp_inv.cref_mem hp_inv.ng hp_inv.sz
                    (show pos_n < csz_val by omega) hcr32 hcsz_bd_c
                have hpos_bd' : (BitVec.setWidth 64 (BitVec.setWidth 32 s.core.confl_ref) + 3 +
                    BitVec.setWidth 64 (BitVec.ofNat 32 pos_n)).toNat <
                    s_cur.core.arena.length := hpos_bd
                c0_hsteps_nogrp
                refine wp_loop_group (fun r2 (hlv, hpv, jv, ()) ml2 => ∃ j_n hp_n : Nat,
                  ml2 = ml_cur ∧ r2 = csz_val - j_n ∧ pos_n + 1 ≤ j_n ∧ j_n ≤ csz_val ∧
                  jv = BitVec.ofNat 32 j_n ∧ pos_n ≤ hp_n ∧ hp_n < j_n ∧
                  hpv = BitVec.ofNat 32 hp_n) ?_ ?_
                · rintro L_j r2 ⟨hlv, hpv, jv, ⟨⟩⟩ ml2 ih_j
                    ⟨j_n, hp_n, rfl, rfl, hj_lo, hj_le, rfl, hhp_lo, hhp_lt, rfl⟩
                  clear hDet hBt hAss hw hmarks hnd hext hcut_le hconfl hconfl0 hscan_lits
                    hall_le hbt_lt hcl_pos hobt huniq hmax32 hcv_le hlvl_len hcl_lt64
                  c0_hsteps_nogrp
                  · have hj_lt : j_n < csz_val := by
                      have hcsz_bd_c' : cref.toNat + 2 < s.core.arena.length := by omega
                      have hb : j_n % 2 ^ 32 < (s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                          BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                            rw [hc_idx2]; exact hcsz_bd_c')).toNat := ‹_›
                      rw [hcsz_get_c0, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hj_le hcsz_lt32)] at hb
                      exact hb
                    obtain ⟨hj_bd, _, _, _, hcand_lvl⟩ :=
                      oneLit_arena_off3_bds hp_inv.len hp_inv.hw hp_inv.cref_mem hp_inv.ng
                        hp_inv.sz hj_lt hcr32 hcsz_bd_c
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i32, i32]) (fun p ml3 => ∃ hp'' : Nat,
                      ml3 = ml2 ∧ pos_n ≤ hp'' ∧ hp'' < j_n + 1 ∧
                      p.2.1 = BitVec.ofNat 32 hp'') ?_ ?_
                    · rintro _ ⟨hl', hp', ⟨⟩⟩ ml3 ⟨hp'', rfl, hlo'', hlt'', rfl⟩
                      c0_clean; c0_steps
                      rw [oneLit_bv32_add1]
                      exact ih_j (csz_val - (j_n + 1)) (hl', BitVec.ofNat 32 hp'',
                        BitVec.ofNat 32 (j_n + 1), ()) ml3 (by omega)
                        ⟨j_n + 1, hp'', rfl, rfl, by omega, by omega, rfl, hlo'', hlt'', rfl⟩
                    · intro Jhl hJhl; c0_clean; c0_split
                      · c0_steps; exact hJhl (_, BitVec.ofNat 32 j_n, ()) ml2
                          ⟨j_n, rfl, by omega, by omega, rfl⟩
                      · c0_steps; exact hJhl (_, BitVec.ofNat 32 hp_n, ()) ml2
                          ⟨hp_n, rfl, hhp_lo, by omega, rfl⟩
                  · have hj_ge : csz_val ≤ j_n := by
                      have hcsz_bd_c' : cref.toNat + 2 < s.core.arena.length := by omega
                      have hnot : ¬ j_n % 2 ^ 32 < (s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 +
                          BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                            rw [hc_idx2]; exact hcsz_bd_c')).toNat := ‹_›
                      rw [hcsz_get_c0, Nat.mod_eq_of_lt (by omega)] at hnot
                      exact Nat.not_lt.mp hnot
                    have hj_eq : j_n = csz_val := Nat.le_antisymm hj_le hj_ge; subst hj_eq
                    refine wp_join_group (ts := []) (fun () mb =>
                      ∃ s_nxt : FullState,
                        OneLitPosInv c F0 F_cur cut1 csz_val cref clvlv s s1 s_nxt ∧
                        (FullMem c s_nxt ⋆ R) mb) ?_ ?_
                    · rintro _ ⟨⟩ mb ⟨s_nxt, hnxt_inv, hm_x⟩
                      c0_clean; c0_steps
                      rw [oneLit_bv32_add1]
                      exact ih_pos (2 - (pos_n + 1)) (BitVec.ofNat 32 (pos_n + 1), ()) mb
                        (by omega) ⟨pos_n + 1, s_nxt, rfl, by omega, rfl, hnxt_inv, hm_x⟩
                    · intro Jinc hJinc
                      c0_hsteps_nogrp
                      · have hhp_ne : hp_n ≠ pos_n := fun h => by
                          subst h; exact ‹BitVec.ofNat 32 hp_n ≠ BitVec.ofNat 32 hp_n› rfl
                        obtain ⟨hhp_bd, _, hhigh_eq, hhigh_lt, _⟩ :=
                          oneLit_arena_off3_bds hp_inv.len hp_inv.hw hp_inv.cref_mem hp_inv.ng
                            hp_inv.sz hhp_lt hcr32 hcsz_bd_c
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun () mb =>
                          ∃ s_nxt : FullState,
                            OneLitPosInv c F0 F_cur cut1 csz_val cref clvlv s s1 s_nxt ∧
                            (FullMem c s_nxt ⋆ R) mb) ?_ ?_
                        · rintro _ ⟨⟩ mb hm_nxt; c0_clean; c0_steps; exact hJinc () mb hm_nxt
                        · intro Jsw hJsw
                          rw [hlit_pos_eq, hhigh_eq]
                          exact oneLit_swap_push_branch_wp hDefrag hUnw hPush hp_inv.len hp_inv.hw
                            hp_inv.marks hp_inv.nodup hp_inv.ext hbin hcr32 hcsz_ge3 hpos_lt2
                            hhp_lt hhp_ne hcsz_bd_c hp_inv.cref_mem hp_inv.ng hp_inv.sz rfl rfl
                            hhigh_lt ⟨hp_inv.cv, hp_inv.cl, hp_inv.fuel, hp_inv.ws2, hp_inv.dm,
                              hp_inv.prob⟩
                            hp_inv.lits hm_c hQ (fun mb ⟨s_nxt, hlen_x, hw_x, hmk_x, hnd_x, hext_x,
                              hcv_x, hcl_x, hfu_x, hws2_x, hdm_x, hpr_x, hvals_x, hlvl_x,
                              htrl_x, hte_x, harlen_x, hct_x, hcr_x, hcref_x, hng_x, hsz_x,
                              hlits_x, hm_x⟩ =>
                                hJsw () mb ⟨s_nxt,
                                  ⟨hlen_x, hw_x, hmk_x, hnd_x, hext_x, hcv_x, hcl_x, hfu_x, hws2_x,
                                   hdm_x, hpr_x, hvals_x.trans hp_inv.vals,
                                   hlvl_x.trans hp_inv.lvl, htrl_x.trans hp_inv.trl,
                                   hte_x.trans hp_inv.te, harlen_x.trans hp_inv.arlen,
                                   hct_x.trans hp_inv.ct, hcr_x.trans hp_inv.cr,
                                   hcref_x, hng_x, hsz_x, hlits_x⟩, hm_x⟩) _ _ rfl rfl
                      · exact hJinc () ml2 ⟨s_cur, hp_inv, hm_c⟩
                · intro L_j hL_j; c0_clean; c0_steps
                  rw [oneLit_bv32_add1]
                  exact hL_j (csz_val - (pos_n + 1)) (s_cur.core.lvl[(BitVec.setWidth 64
                    (s_cur.core.arena[(cref.setWidth 64 + 3 + (BitVec.ofNat 32 pos_n).setWidth
                    64).toNat]'hpos_bd >>> 1)).toNat]'hlit_pos_bd_lvl, BitVec.ofNat 32 pos_n,
                    BitVec.ofNat 32 (pos_n + 1), ()) ml_cur
                    ⟨pos_n + 1, pos_n, rfl, rfl, Nat.le_refl _, by omega, rfl, Nat.le_refl _,
                     Nat.lt_succ_self _, rfl⟩
              · have hpos_ge2 : 2 ≤ pos_n := by
                  have hnot : ¬ (BitVec.ofNat 32 pos_n).toNat < (2#32).toNat := ‹_›
                  rw [Proof.Spec.bv32_ofNat_toNat (by omega)] at hnot; exact Nat.not_lt.mp hnot
                have hpos_eq2 : pos_n = 2 := Nat.le_antisymm hpos_le2 hpos_ge2; subst hpos_eq2
                have hconfl_cur := oneLit_large_exit0_confl hbin hobt hcref_eq hp_inv.vals
                  hp_inv.lvl hp_inv.trl hp_inv.cl hp_inv.ct hp_inv.cr hp_inv.cref_mem hp_inv.ng
                  hp_inv.lits
                exact hQ 0#64 s_cur ml_cur hp_inv.len (Or.inl rfl) hp_inv.cv hp_inv.fuel hp_inv.ws2
                  hp_inv.dm hp_inv.prob hp_inv.marks hp_inv.nodup hp_inv.ext (fun _ h => by cases h)
                  (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
                  (fun _ => ⟨cut1, by rw [hp_inv.te]; exact hobt.cut1_le, hp_inv.hw,
                    by rw [hp_inv.cl]; exact hcl_pos, by rw [hp_inv.cl]; exact hcl_le,
                    hconfl_cur⟩)
                  hm_c
              · have hpos_ge2 : 2 ≤ pos_n := by
                  have hnot : ¬ (BitVec.ofNat 32 pos_n).toNat < (2#32).toNat := ‹_›
                  rw [Proof.Spec.bv32_ofNat_toNat (by omega)] at hnot; exact Nat.not_lt.mp hnot
                have hpos_eq2 : pos_n = 2 := Nat.le_antisymm hpos_le2 hpos_ge2; subst hpos_eq2
                have hcnt_eq1 : cntv = 1#64 := by
                  have hnot : ¬ 1 < cntv.toNat := by simpa only [BitVec.reduceToNat] using ‹_›
                  exact BitVec.eq_of_toNat_eq (by simp only [BitVec.reduceToNat]; omega)
                obtain ⟨q_f, hqf_lt, hfq_eq, hfq_lv, hjl_lt, hoth⟩ := huniq hcsz_pos hcnt_eq1
                obtain ⟨hfm_c, hoth_c, hflv_c, hfm_lt⟩ := oneLit_large_exit1_prep hlen hobt hcr_f
                  hcref_eq hcsz_bd rfl hscan_lits hcl_pos hqf_lt hfq_eq hfq_lv hjl_lt hoth
                  hp_inv.vals hp_inv.lvl hp_inv.lits
                exact oneLit_large_tail_exec_wp hDet hBt hAss hcl_le hcl_pos (hjl_lt hcl_pos)
                  hcr32 hp_inv.cref_mem hp_inv.ng hfm_c hoth_c hp_inv.len hp_inv.hw hp_inv.marks
                  hp_inv.nodup hp_inv.ext hp_inv.cl hp_inv.cv hp_inv.fuel hp_inv.ws2 hp_inv.dm
                  hp_inv.prob hflv_c hfm_lt hm_c hQ
            · intro L_pos hL_pos; c0_clean; c0_steps
              exact hL_pos 2 (0#32, ()) m1 ⟨0, s1, rfl, Nat.zero_le _, rfl,
                ⟨hobt.len1, hobt.hw1, hobt.marks1, hobt.nodup1, hobt.ext1, hobt.cv_eq,
                 hobt.cl1_eq, hobt.fuel_eq, hobt.ws2_eq, hobt.dm0, hobt.prob_eq, rfl, rfl, rfl,
                 rfl, rfl, rfl, rfl, hcref1_ref, hcref1_ng, hcref1_sz, hconfl_eq1⟩, hm1⟩
          · intro Jbt hJbt; c0_hsteps_nogrp
            · have hlt_cl : s.core.cur_level > clvlv.toNat := by
                have hb : clvlv.toNat < (BitVec.ofNat 64 s.core.cur_level).toNat := ‹_›
                rw [Proof.Spec.bv64_ofNat_toNat hcl_lt64] at hb; exact hb
              c0_call hBt
              refine ⟨c, s, R, rfl, hlen, hcl_lt64,
                fun _ => by have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega,
                hw.trail_lits_lt, hm, ?_⟩
              dsimp only
              intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 hlen1 _ _ hcl1 hpres _ _
                hvl1 _ hw1 hm1
              have hcl1_eq : cl1 = clvlv.toNat := by rw [hcl1]; omega
              obtain ⟨hvs1, hls1⟩ := hvl1 ⟨F0, F_cur, Or.inr hw.toFullOtfsWitnessInv⟩
              obtain ⟨cut1, hobt⟩ := oneLit_after_bt hlen hdm hw hmarks hnd hext hcut_le hconfl0
                hcl_pos (Nat.le_trans (le_refl _) hcl_le) hbt_lt
                (Or.inr ⟨hlt_cl, hlen1, hcl1_eq, rfl, hpres.2.2.1, hpres.1.1, hpres.1.2, hdm, rfl,
                  rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvs1, hls1,
                  hw1 F0 F_cur hw.toFullOtfsWitnessInv (by omega)⟩)
              exact hJbt () m1 ⟨_, cut1, hobt, hm1⟩
            · have hle_cl : s.core.cur_level ≤ clvlv.toNat := by
                have hnot : ¬ clvlv.toNat < (BitVec.ofNat 64 s.core.cur_level).toNat := ‹_›
                rw [Proof.Spec.bv64_ofNat_toNat hcl_lt64] at hnot; omega
              obtain ⟨cut1, hobt⟩ := oneLit_after_bt hlen hdm hw hmarks hnd hext hcut_le hconfl0
                hcl_pos hcl_le hbt_lt (Or.inl ⟨hle_cl, rfl⟩)
              exact hJbt () ml ⟨s, cut1, hobt, hm⟩
    · intro Jscan hJscan; c0_clean; c0_steps
      exact hJscan csz_val (0#64, 0#64, 0#64, 0xFFFFFFFF#32, 0#32, ()) m
        ⟨0, rfl, rfl, rfl, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _,
          fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun h => by omega, fun h => by omega⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Learn
