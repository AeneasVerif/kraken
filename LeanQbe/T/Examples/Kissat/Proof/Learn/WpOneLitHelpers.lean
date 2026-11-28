/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Shared Helpers for `full_one_lit_confl` (`Proof.Learn.WpOneLitHelpers`)

Defines `OneLitBtInv`, `OneLitPost`, `OneLitScanInv`, `oneLitTailExpr`, and the ported sub-lemmas
for backtrack invariant propagation, scan bounds, chrono assign, watch-stack headroom, and large
clause watch-push swap (`0` legacy imports, `0` `@[expose]` on theorems/sections, `<= 100` cols).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Learn

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers

public section

structure OneLitBtInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s1 : FullState) (cut1 clvl : Nat) : Prop where
  cut1_le : cut1 ≤ s1.core.trail_end
  hw1 : FullWitnessCutInv c F0 F_cur cut1 s1.core
  len1 : s1.LengthsOk c
  cl1_eq : s1.core.cur_level = clvl
  cl_pos : 0 < clvl
  cl_le : clvl ≤ s.core.cur_level
  cv_eq : s1.core.cur_vars = s.core.cur_vars
  fuel_eq : s1.core.fuel = s.core.fuel
  ws2_eq : s1.scratch.work_stk2 = s.scratch.work_stk2
  dm0 : s1.core.dense_mode = 0#64
  prob_eq : s1.core.probing = s.core.probing
  wvec_eq : s1.core.wvec = s.core.wvec
  wstk_eq : s1.core.wstk = s.core.wstk
  wlen_eq : s1.core.wlen = s.core.wlen
  wus_eq : s1.core.wusable = s.core.wusable
  marks1 : FullLitMarksClear c s1
  nodup1 : FullArenaVarsNodup s1
  ext1 : FullExtScratchOk c s1
  confl1 : FullConflictOkCut F_cur cut1 s1
  vals_keep : ∀ l < 2 * s.core.cur_vars,
    (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl →
    s1.core.vals[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8
  lvl_keep : ∀ l < 2 * s.core.cur_vars,
    s.core.vals[l]?.getD 0#8 = 0xFF#8 →
    (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl →
    s1.core.lvl[l / 2]?.getD 0#32 = s.core.lvl[l / 2]?.getD 0#32
  arena_eq : s1.core.arena = s.core.arena
  arena_len_eq : s1.core.arena_len = s.core.arena_len
  confl_type_eq : s1.core.confl_type = s.core.confl_type
  confl_ref_eq : s1.core.confl_ref = s.core.confl_ref

@[expose] def OneLitPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r s' m',
    s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
    s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
    s'.scratch.work_stk2 = s.scratch.work_stk2 →
    s'.core.dense_mode = 0#64 → s'.core.probing = s.core.probing →
    FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
    (s.core.confl_type = 1#64 → r ≠ 2#64) →
    (r = 20#64 → F0.Unsat ∧ s' = s) →
    (r = 1#64 → FullWitnessInv c F0 F_cur s'.core ∧ s'.core.cur_level < s.core.cur_level) →
    (r = 2#64 → FullOtfsWitnessInv c F0 F_cur s'.core) →
    (r = 0#64 → ∃ cut' ≤ s'.core.trail_end,
      FullWitnessCutInv c F0 F_cur cut' s'.core ∧ 0 < s'.core.cur_level ∧
      s'.core.cur_level ≤ s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem oneLit_opaque_state {s_old : FullState} (k : FullCoreState) (sc : FullScratch)
    {P : FullState → Prop} (h : P s_old) (hk : k = s_old.core) (hsc : sc = s_old.scratch) :
    ∃ s : FullState, s.core = k ∧ s.scratch = sc ∧ P s :=
  ⟨s_old, hk.symm, hsc.symm, h⟩

theorem oneLit_fullMem_of_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s1 ⋆ R) m) (hc : s1.core = s2.core) (hs : s1.scratch = s2.scratch) :
    (FullMem c s2 ⋆ R) m := by
  have heq : s1 = s2 := by cases s1; cases s2; simp only at hc hs; simp [hc, hs]
  exact heq ▸ hm

theorem oneLit_otfsInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k) (oom' : BitVec 64) :
    FullOtfsWitnessInv c F0 F_cur { k with oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem oneLit_canonCut_with_watches {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} {wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' oom' : BitVec 64} (hw : FullWitnessCutInv c F0 F_cur cut k)
    (hmw : ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' }) :
    FullWitnessCutInv c F0 F_cur cut
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hmw
    reason_inv_cut := hw.reason_inv_cut
    reason_lit_mem_cut := hw.reason_lit_mem_cut }

theorem oneLit_after_bt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut clvl : Nat} {s s1 : FullState} (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hmarks : FullLitMarksClear c s)
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hcut_le : cut ≤ s.core.trail_end) (hconfl : FullConflictOkCut F_cur cut s)
    (hcl_pos : 0 < clvl) (hcl_le : clvl ≤ s.core.cur_level)
    (hbt_lt : ∀ l, (s.core.confl_type = 1#64 ∧
        (l = s.core.confl_lit0.toNat ∨ l = s.core.confl_lit1.toNat)) ∨
      (s.core.confl_type ≠ 1#64 ∧ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat) →
      (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl)
    (hs1 : s.core.cur_level ≤ clvl ∧ s1 = s ∨
      clvl < s.core.cur_level ∧ s1.LengthsOk c ∧ s1.core.cur_level = clvl ∧
      s1.core.fuel = s.core.fuel ∧ s1.scratch.work_stk2 = s.scratch.work_stk2 ∧
      s1.scratch.last_learned = s.scratch.last_learned ∧
      s1.scratch.extend_len = s.scratch.extend_len ∧
      s1.core.dense_mode = 0#64 ∧ s1.core.probing = s.core.probing ∧
      s1.core.cur_vars = s.core.cur_vars ∧ s1.core.wvec = s.core.wvec ∧
      s1.core.wstk = s.core.wstk ∧ s1.core.wlen = s.core.wlen ∧ s1.core.wusable = s.core.wusable ∧
      s1.core.mrk = s.core.mrk ∧ s1.core.lit_mark = s.core.lit_mark ∧
      s1.core.arena = s.core.arena ∧ s1.core.arena_len = s.core.arena_len ∧
      s1.core.confl_type = s.core.confl_type ∧ s1.core.confl_lit0 = s.core.confl_lit0 ∧
      s1.core.confl_lit1 = s.core.confl_lit1 ∧ s1.core.confl_ref = s.core.confl_ref ∧
      (∀ l < 2 * s.core.cur_vars, s1.core.vals[l]?.getD 0#8 =
        if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl then s.core.vals[l]?.getD 0#8 else 0#8) ∧
      (∀ i < s.core.trail_end, let v := (s.core.trl[i]?.getD 0#32).toNat / 2
        s1.core.lvl[v]?.getD 0#32 =
          if (s.core.lvl[v]?.getD 0#32).toNat ≤ clvl then s.core.lvl[v]?.getD 0#32 else 0#32) ∧
      FullWitnessInv c F0 F_cur s1.core) :
    ∃ cut1, OneLitBtInv c F0 F_cur s s1 cut1 clvl := by
  rcases hs1 with ⟨hle, rfl⟩ | ⟨_, hlen1, hcl1, hfu1, hws2, hll1, hel1, hdm1, hpr1, hcv1, hwv1,
      hws1, hwl1, hwu1, hmk1, hlm1, har1, hal1, hct1, hc01, hc11, hcr1, hvals1, hlvl1, hw1⟩
  · exact ⟨cut, hcut_le, hw, hlen, by omega, hcl_pos, hcl_le, rfl, rfl, rfl, hdm, rfl, rfl, rfl,
      rfl, rfl, hmarks, hnd, hext, hconfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl,
      rfl, rfl⟩
  · have hrefs : fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s.core := by
      simp [fullArenaClauseRefsCore, har1, hal1]
    have hmarks1 : FullLitMarksClear c s1 :=
      ⟨fun v hv => by rw [hmk1]; exact hmarks.1 v hv,
       fun l hl => by rw [hlm1]; exact hmarks.2 l hl⟩
    have hnd1 : FullArenaVarsNodup s1 := fun r hr hng => by
      change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs] at hr
      change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup
      simp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har1]
      exact hnd r hr (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, har1] using hng)
    have hext1 : FullExtScratchOk c s1 := ⟨fun i hi => by
      change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s1.core
      rw [hrefs, hll1]; exact hext.1 i hi, by rw [hel1]; exact hext.2⟩
    have hconfl1 : FullConflictOkCut F_cur s1.core.trail_end s1 := by
      refine FullConflictOkW.toCut hw1 ?_
      rcases hconfl.1 with ⟨hbin, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨hct2, href, hng, hf⟩
      · left; rw [hct1, hc01, hc11, hcv1]
        have hf0' : s1.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hvals1 _ h0lt, ite_eq_left (hbt_lt _ (Or.inl ⟨hbin, Or.inl rfl⟩)), hf0]
        have hf1' : s1.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hvals1 _ h1lt, ite_eq_left (hbt_lt _ (Or.inl ⟨hbin, Or.inr rfl⟩)), hf1]
        exact ⟨hbin, h0lt, h1lt, hf0', hf1', hent⟩
      · right
        have hne1 : s.core.confl_type ≠ 1#64 := by rw [hct2]; decide
        have hgarb : fullArenaClauseGarb s1 s.core.confl_ref.toNat =
            fullArenaClauseGarb s s.core.confl_ref.toNat := by
          simp [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, har1]
        have hlits : fullArenaClauseLits s1 s.core.confl_ref.toNat =
            fullArenaClauseLits s s.core.confl_ref.toNat := by
          simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, har1]
        rw [hct1, hcr1, show fullArenaClauseRefs s1 = fullArenaClauseRefs s from hrefs,
          hgarb, hlits]
        refine ⟨hct2, href, hng, fun l hl => ?_⟩
        have hllt := hw.arena.lits_lt _ href hng l hl
        rw [hvals1 l hllt, ite_eq_left (hbt_lt l (Or.inr ⟨hne1, hl⟩)), hf l hl]
    refine ⟨s1.core.trail_end, Nat.le_refl _, hw1.toCut, hlen1, hcl1, hcl_pos,
      hcl_le, hcv1, hfu1, hws2, hdm1, hpr1, hwv1, hws1, hwl1, hwu1, hmarks1, hnd1, hext1, hconfl1,
      fun l hl hle => by rw [hvals1 l hl, ite_eq_left hle], fun l hl hfl hle => ?_, har1, hal1,
      hct1, hcr1⟩
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hl).mp hfl
    have hv := hlvl1 i hi; dsimp only at hv; rw [hieq, fullInv_var_xor1] at hv
    rw [hv, ite_eq_left hle]

end

private structure OneLitTailPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sb : FullState) (cut1 clvl jlvl : Nat) (forced rsn : BitVec 32) : Prop where
  len : sb.LengthsOk c
  hw : FullWitnessCutInv c F0 F_cur cut1 sb.core
  marks : FullLitMarksClear c sb
  nd : FullArenaVarsNodup sb
  ext : FullExtScratchOk c sb
  cl_eq : sb.core.cur_level = clvl
  cl_le : clvl ≤ s.core.cur_level
  cv_eq : sb.core.cur_vars = s.core.cur_vars
  fu_eq : sb.core.fuel = s.core.fuel
  ws2_eq : sb.scratch.work_stk2 = s.scratch.work_stk2
  dm0 : sb.core.dense_mode = 0#64
  prob_eq : sb.core.probing = s.core.probing
  forced_lt : forced.toNat < 2 * sb.core.cur_vars
  forced_lvl : (sb.core.lvl[forced.toNat / 2]?.getD 0#32).toNat = clvl
  rsn_ne : rsn ≠ 0xFFFFFFFF#32
  rsn_pre :
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * sb.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, ot]) ∧
      sb.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (sb.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl
    else
      rsn.toNat ∈ fullArenaClauseRefsCore sb.core ∧
      fullArenaClauseGarbCore sb.core rsn.toNat = false ∧
      forced.toNat ∈ fullArenaClauseLitsCore sb.core rsn.toNat ∧
      ∀ q ∈ fullArenaClauseLitsCore sb.core rsn.toNat,
        q = forced.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
          (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl)

private theorem oneLit_after_bt_assign_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl jlvl nlvl : Nat} {s s1 s2 : FullState}
    {forced rsn : BitVec 32} {jlvlv : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]}
    {X : XPost} {m2 : Mem 64}
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hpre : OneLitTailPre c F0 F_cur s s1 cut1 clvl jlvl forced rsn)
    (hjv_eq : jlvlv.toNat = jlvl) (hj_lt32 : jlvl < 2 ^ 32)
    (hjlvl_le : jlvl ≤ nlvl) (hnlvl_lt : nlvl < clvl)
    (hs2_len : s2.LengthsOk c) (hs2_cl : s2.core.cur_level = nlvl)
    (hs2_fu : s2.core.fuel = s1.core.fuel) (hs2_ws2 : s2.scratch.work_stk2 = s1.scratch.work_stk2)
    (hs2_ll : s2.scratch.last_learned = s1.scratch.last_learned)
    (hs2_el : s2.scratch.extend_len = s1.scratch.extend_len)
    (hs2_dm : s2.core.dense_mode = 0#64) (hs2_pr : s2.core.probing = s1.core.probing)
    (hs2_cv : s2.core.cur_vars = s1.core.cur_vars)
    (hs2_mk : s2.core.mrk = s1.core.mrk) (hs2_lm : s2.core.lit_mark = s1.core.lit_mark)
    (hs2_ar : s2.core.arena = s1.core.arena) (hs2_al : s2.core.arena_len = s1.core.arena_len)
    (hs2_vals : ∀ l < 2 * s1.core.cur_vars, s2.core.vals[l]?.getD 0#8 =
      if (s1.core.lvl[l / 2]?.getD 0#32).toNat ≤ nlvl then s1.core.vals[l]?.getD 0#8 else 0#8)
    (hs2_lvl : ∀ i < s1.core.trail_end, let v := (s1.core.trl[i]?.getD 0#32).toNat / 2
      s2.core.lvl[v]?.getD 0#32 =
        if (s1.core.lvl[v]?.getD 0#32).toNat ≤ nlvl then s1.core.lvl[v]?.getD 0#32 else 0#32)
    (hw2 : FullWitnessInv c F0 F_cur s2.core) (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : OneLitPost c F0 F_cur s R Q) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
        (Arg.var c.hdr, Arg.var forced, Arg.var rsn, Arg.var (jlvlv.setWidth 32), ())
        fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())) m2 := by
  have htr_eq : jlvlv.setWidth 32 = BitVec.ofNat 32 jlvl := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, hjv_eq, Proof.Spec.bv32_ofNat_toNat hj_lt32,
      Nat.mod_eq_of_lt hj_lt32])
  have hf_un : s2.core.vals[forced.toNat]?.getD 0#8 = 0#8 := by
    rw [hs2_vals _ hpre.forced_lt, ite_eq_right (by have := hpre.forced_lvl; omega)]
  have hte2_lt : s2.core.trail_end < s2.core.cur_vars :=
    hw2.trail_end_lt_of_unassigned (hs2_cv ▸ hpre.forced_lt) hf_un
  have hng_guard : ¬ (s2.core.cur_vars ≤ forced.toNat / 2 ∨
      c.max_vars ≤ s2.core.trail_end ∨ s2.core.vals[forced.toNat]?.getD 0#8 ≠ 0#8) :=
    not_or.mpr ⟨Nat.not_le.mpr (Nat.div_lt_of_lt_mul (hs2_cv ▸ hpre.forced_lt)),
      not_or.mpr ⟨Nat.not_le.mpr (Nat.lt_of_lt_of_le hte2_lt hs2_len.core_ok.cur_vars_le),
        fun h => h hf_un⟩⟩
  c0_call hAss
  refine ⟨c, s2, R, rfl, hs2_len, hm2, ?_⟩
  simp only [hng_guard, ↓reduceIte]
  intro fl' unass3 ph' m3 hfl3 hph3 hm3
  let v := forced.toNat / 2
  let rsn' := if jlvlv.setWidth 32 = 0#32 then 0xFFFFFFFF#32 else rsn
  let s3 : FullState :=
    { s2 with
      core :=
        { s2.core with
          vals := (s2.core.vals.set forced.toNat 1#8).set (forced.toNat ^^^ 1) 0xFF#8
          flags := fl', lvl := s2.core.lvl.set v (jlvlv.setWidth 32)
          rsns := s2.core.rsns.set v rsn', trl := s2.core.trl.set s2.core.trail_end forced
          trail_pos := s2.core.trail_pos.set v (BitVec.ofNat 32 s2.core.trail_end)
          trail_end := s2.core.trail_end + 1, unassigned := unass3
          unflushed := if jlvlv.setWidth 32 = 0#32
            then s2.core.unflushed + 1#64 else s2.core.unflushed }
      scratch := { s2.scratch with phases := ph' } }
  have hsc3 : s3.scratch.LengthsOk c := { hs2_len.scratch_ok with phases_len := hph3 }
  have h_s2_false : ∀ q < 2 * s1.core.cur_vars, s1.core.vals[q]?.getD 0#8 = 0xFF#8 →
      (s1.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl →
      ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s2.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl := fun q hq hqf hql => by
    have hqf2 : s2.core.vals[q]?.getD 0#8 = 0xFF#8 := by
      rw [hs2_vals q hq, ite_eq_left (by omega), hqf]
    obtain ⟨m, hm, hmeq⟩ := (hw2.vals_false_iff q (hs2_cv ▸ hq)).mp hqf2
    obtain ⟨i, hi, hieq⟩ := (hpre.hw.vals_false_iff q hq).mp hqf
    have hlv := hs2_lvl i hi; dsimp only at hlv; rw [hieq, fullInv_var_xor1] at hlv
    exact ⟨m, hm, hmeq, by rw [hlv, ite_eq_left (by omega)]; exact hql⟩
  have hrsn_pre := hpre.rsn_pre
  have hl0 : jlvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat]) := by
    intro hj0; subst hj0; by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hrsn_pre; obtain ⟨hot_lt, hent, hot_f, hot_lv⟩ := hrsn_pre
      obtain ⟨m, hm, hmeq, hml0⟩ := h_s2_false _ hot_lt hot_f hot_lv
      have htr0 : (s2.core.lvl[(s2.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        rw [hmeq, fullInv_var_xor1]; omega
      exact entails_of_mem_or_false hent fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        exact hl.elim (fun h => h ▸ Or.inl List.mem_cons_self) fun h =>
          Or.inr (h ▸ by have hs := hw2.level0_sound m hm htr0; rwa [hmeq] at hs)
    · rw [ite_eq_right hbin] at hrsn_pre; obtain ⟨h1, h2, _, h4⟩ := hrsn_pre
      have h1' : rsn.toNat ∈ fullArenaClauseRefsCore s2.core := by
        simpa [fullArenaClauseRefsCore, hs2_ar, hs2_al] using h1
      have h2' : fullArenaClauseGarbCore s2.core rsn.toNat = false := by
        simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hs2_ar] using h2
      exact entails_of_mem_or_false (hw2.arena.entails rsn.toNat h1' h2') fun q hq => by
        have hq1 : q ∈ fullArenaClauseLitsCore s1.core rsn.toNat := by
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs2_ar] using hq
        rcases h4 q hq1 with rfl | ⟨hqf, hql⟩
        · exact Or.inl List.mem_cons_self
        · obtain ⟨m, hm, hmeq, hml⟩ := h_s2_false q (hs2_cv ▸ hw2.arena.lits_lt _ h1' h2' q hq)
            hqf hql
          have htr0 : (s2.core.lvl[(s2.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0
              := by rw [hmeq, fullInv_var_xor1]; omega
          exact Or.inr (by have hs := hw2.level0_sound m hm htr0; rwa [hmeq] at hs)
  have hrsn2 : 0 < jlvl → rsn ≠ 0xFFFFFFFF#32 →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s2.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause
          (cnfClause [forced.toNat, ot]) ∧
        ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s2.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s2.core ∧
        fullArenaClauseGarbCore s2.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s2.core rsn.toNat,
          q = forced.toNat ∨ ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s2.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl := by
    intro _ _; by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hrsn_pre ⊢; obtain ⟨hot_lt, hent, hot_f, hot_lv⟩ := hrsn_pre
      exact ⟨hs2_cv ▸ hot_lt, hent, h_s2_false _ hot_lt hot_f hot_lv⟩
    · rw [ite_eq_right hbin] at hrsn_pre ⊢; obtain ⟨h1, h2, _, h4⟩ := hrsn_pre
      have h1' : rsn.toNat ∈ fullArenaClauseRefsCore s2.core := by
        simpa [fullArenaClauseRefsCore, hs2_ar, hs2_al] using h1
      have h2' : fullArenaClauseGarbCore s2.core rsn.toNat = false := by
        simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hs2_ar] using h2
      refine ⟨h1', h2', fun q hq => ?_⟩
      have hq1 : q ∈ fullArenaClauseLitsCore s1.core rsn.toNat := by
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs2_ar] using hq
      exact (h4 q hq1).elim Or.inl fun ⟨hqf, hql⟩ =>
        Or.inr (h_s2_false q (hs2_cv ▸ hw2.arena.lits_lt _ h1' h2' q hq) hqf hql)
  have hrsn_mem2 : 0 < jlvl → rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      forced.toNat ∈ fullArenaClauseLitsCore s2.core rsn.toNat := fun _ _ hlg => by
    rw [ite_eq_right (fun h => absurd hlg h)] at hrsn_pre
    simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs2_ar] using hrsn_pre.2.2.1
  obtain ⟨hlen3_pre, hw3_pre⟩ := chronoAssign_preserves_fullWitness hw2 hs2_len hsc3 hfl3
    (hs2_cv ▸ hpre.forced_lt) hf_un (hs2_cl ▸ hjlvl_le) (fun _ => hpre.rsn_ne) hl0 hrsn2
    hrsn_mem2 (unassigned' := unass3) (unflushed' := s3.core.unflushed)
  have hj_z : (jlvlv.setWidth 32 = 0#32) ↔ jlvl = 0 := by
    rw [htr_eq]; constructor
    · intro h; simpa [Proof.Spec.bv32_ofNat_toNat hj_lt32] using congrArg BitVec.toNat h
    · intro h; simp [h]
  have hrsn_eq : (if jlvlv.setWidth 32 = 0#32 then 0xFFFFFFFF#32 else rsn) =
      if jlvl = 0 then 0xFFFFFFFF#32 else rsn := by
    by_cases hj : jlvl = 0
    · rw [ite_eq_left (hj_z.mpr hj), ite_eq_left hj]
    · rw [ite_eq_right (fun h => hj (hj_z.mp h)), ite_eq_right hj]
  have hs3_eq : { s2 with
      core := { s2.core with
        vals := (s2.core.vals.set forced.toNat 1#8).set (forced.toNat ^^^ 1) 0xFF#8
        flags := fl', lvl := s2.core.lvl.set v (BitVec.ofNat 32 jlvl)
        rsns := s2.core.rsns.set v (if jlvl = 0 then 0xFFFFFFFF#32 else rsn)
        trl := s2.core.trl.set s2.core.trail_end forced
        trail_pos := s2.core.trail_pos.set v (BitVec.ofNat 32 s2.core.trail_end)
        trail_end := s2.core.trail_end + 1, unassigned := unass3, unflushed := s3.core.unflushed }
      scratch := { s2.scratch with phases := ph' } } = s3 := by
    dsimp only [s3, rsn', v]; rw [hrsn_eq, htr_eq]
  have hlen3 : s3.LengthsOk c := hs3_eq ▸ hlen3_pre
  have hw3 : FullWitnessInv c F0 F_cur s3.core :=
    congrArg FullState.core hs3_eq ▸ hw3_pre
  have hmarks3 : FullLitMarksClear c s3 :=
    ⟨fun w hw => by change s2.core.mrk[w]?.getD 0#8 = 0#8; rw [hs2_mk]; exact hpre.marks.1 w hw,
     fun l hl => by
       change s2.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hs2_lm]; exact hpre.marks.2 l hl⟩
  have hrefs : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s1.core := by
    simp [fullArenaClauseRefsCore, s3, hs2_ar, hs2_al]
  have hnd3 : FullArenaVarsNodup s3 := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s3.core at hr; rw [hrefs] at hr
    change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup
    simp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s3, hs2_ar]
    exact hpre.nd r hr (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, s3, hs2_ar] using hng)
  have hext3 : FullExtScratchOk c s3 := ⟨fun i hi => by
    change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s3.core; rw [hrefs, hs2_ll]; exact hpre.ext.1 i hi,
    by change s2.scratch.extend_len ≤ c.extend_cap; rw [hs2_el]; exact hpre.ext.2⟩
  c0_hsteps
  exact hQ 1#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (hs2_cv.trans hpre.cv_eq)
    (hs2_fu.trans hpre.fu_eq) (hs2_ws2.trans hpre.ws2_eq) hs2_dm (hs2_pr.trans hpre.prob_eq)
    hmarks3 hnd3 hext3 (fun _ h => by cases h) (fun h => by cases h)
    (fun _ => ⟨hw3, by dsimp [s3]; have := hpre.cl_le; omega⟩)
    (fun h => by cases h) (fun h => by cases h)
    (oneLit_fullMem_of_eq hm3 rfl rfl)

public section

@[expose] def OneLitScanInv (s : FullState) (cref forcedv : BitVec 32)
    (csz_val i : Nat) (clvlv jlvlv cntv : BitVec 64) : Prop :=
  i ≤ csz_val ∧ clvlv.toNat ≤ s.core.cur_level ∧ jlvlv.toNat ≤ s.core.cur_level ∧
  cntv.toNat ≤ i ∧
  (i = 0 → clvlv = 0#64 ∧ jlvlv = 0#64 ∧ cntv = 0#64 ∧ forcedv = 0xFFFFFFFF#32) ∧
  (0 < i → 1 ≤ cntv.toNat ∧
    (∀ q < i, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat ≤ clvlv.toNat) ∧
    (∃ q < i, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat = clvlv.toNat)) ∧
  (0 < i → cntv = 1#64 → ∃ q_f < i,
    forcedv = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 ∧
    (s.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvlv.toNat ∧
    (0 < clvlv.toNat → jlvlv.toNat < clvlv.toNat) ∧
    ∀ q' < i, q' ≠ q_f →
      (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat / 2]?.getD
        0#32).toNat ≤ jlvlv.toNat)

theorem oneLit_scan_bds {c : FullCfg} {s : FullState} {cref : BitVec 32}
    {csz_val i : Nat} (hlen : s.LengthsOk c) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcap : c.arena_cap < 2 ^ 31 - 1) (hcsz_bd : cref.toNat + 3 + csz_val ≤ s.core.arena_len)
    (hilt : i < csz_val) (hl_lt : (s.core.arena[cref.toNat + 3 + i]?.getD 0#32).toNat <
      2 * s.core.cur_vars) (hcref_eq : cref = s.core.confl_ref.setWidth 32) :
    let li := s.core.arena[cref.toNat + 3 + i]'(by
      have := hlen.core_ok.arena_len_arr; have := hlen.core_ok.arena_len_le; omega)
    let ll : BitVec 64 := (s.core.lvl[li.toNat / 2]?.getD 0#32).setWidth 64
    ∃ (hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat <
        s.core.arena.length)
      (hc_bd : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
        i % 2 ^ 32) % 2 ^ 64 < s.core.arena.length),
      (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat = cref.toNat + 3 + i ∧
      s.core.arena[cref.toNat + 3 + i]?.getD 0#32 = li ∧
      ll.toNat = (s.core.lvl[(s.core.arena[cref.toNat + 3 + i]?.getD 0#32).toNat / 2]?.getD
        0#32).toNat ∧
      s.core.arena[(cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat]'hz_bd = li ∧
      ((s.core.arena[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 i).setWidth 64).toNat]'hz_bd >>> 1).setWidth 64).toNat <
        s.core.lvl.length ∧
      (s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
        i % 2 ^ 32) % 2 ^ 64]'hc_bd).toNat / 2 < s.core.lvl.length ∧
      (∀ pf1 pf2, BitVec.setWidth 64 (s.core.lvl[(BitVec.setWidth 64
        (s.core.arena[((s.core.confl_ref.setWidth 32).setWidth 64 + 3 +
          (BitVec.ofNat 32 i).setWidth 64).toNat]'pf1 >>> 1)).toNat]'pf2) = ll) := by
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hcr_i_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat =
      cref.toNat + 3 + i := by
    have : cref.toNat < 2 ^ 31 - 1 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
      zext_toNat (BitVec.ofNat 32 i) (by decide), Proof.Spec.bv32_ofNat_toNat (by omega)]
    simp only [BitVec.reduceToNat]; omega
  have hcr_eq : cref.toNat = s.core.confl_ref.toNat % 2 ^ 32 := by
    rw [hcref_eq, BitVec.toNat_setWidth]
  have hc_idx : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
      i % 2 ^ 32) % 2 ^ 64 = cref.toNat + 3 + i := by
    rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl, ← hcr_eq]; omega
  have hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat <
      s.core.arena.length := by rw [hcr_i_bd]; omega
  have hc_bd : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
      i % 2 ^ 32) % 2 ^ 64 < s.core.arena.length := by rw [hc_idx]; omega
  intro li ll
  have hli_get : s.core.arena[cref.toNat + 3 + i]?.getD 0#32 = li := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hll_val : ll.toNat = (s.core.lvl[(s.core.arena[cref.toNat + 3 + i]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat := by
    dsimp only [ll, li]; rw [hli_get, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    exact Nat.lt_trans (BitVec.isLt _) (by decide)
  have hli_idx : ∀ pf, s.core.arena[(cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = li := fun _ => getElem_eq_of_idx hcr_i_bd
  have hli_var : li.toNat / 2 < s.core.cur_vars := by
    rw [← hli_get]; exact Nat.div_lt_of_lt_mul hl_lt
  have hbd_lvl : li.toNat / 2 < s.core.lvl.length := by
    rw [hlvl_len]; exact Nat.lt_of_lt_of_le hli_var hcv_le
  refine ⟨hz_bd, hc_bd, hcr_i_bd, hli_get, hll_val, hli_idx hz_bd, ?_, ?_, fun pf1 pf2 => ?_⟩
  · rw [bv_c0_zext32_64, bv32_lshr_1, hli_idx hz_bd]; exact hbd_lvl
  · rw [getElem_eq_of_idx hc_idx]; exact hbd_lvl
  · dsimp only [ll]; congr 1; rw [List.getElem?_eq_getElem hbd_lvl, Option.getD_some]
    exact getElem_eq_of_idx (by
      rw [bv_c0_zext32_64, bv32_lshr_1]
      have ha_li : s.core.arena[((s.core.confl_ref.setWidth 32).setWidth 64 + 3 +
          (BitVec.ofNat 32 i).setWidth 64).toNat]'pf1 = li :=
        (getElem_eq_of_idx (hj := hz_bd)
          (by rw [← hcref_eq, show (3 : BitVec 64) = 3#64 from rfl])).trans (hli_idx hz_bd)
      rw [ha_li])

@[expose] def oneLitTailExpr (hdr jlvlv : BitVec 64) (forcedv cref : BitVec 32) :
    Expr Val Cont [i64] :=
  Expr.call (as := [i64, i64]) "full_det_new_level" (Arg.var hdr, Arg.var jlvlv, ())
    fun (p_29 : Tup Val [i64]) =>
      Expr.call (as := [i64, i64]) "full_backtrack_ac_fid" (Arg.var hdr, Arg.var p_29.fst, ())
        fun (_ : Tup Val []) =>
          Expr.let_ (Op.mk (.trunc 64 32) (Arg.var jlvlv, ())) fun p_31 =>
            Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
              (Arg.var hdr, Arg.var forcedv, Arg.var cref, Arg.var p_31.fst, ())
              fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())

theorem oneLit_large_tail_exec_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl : Nat} {s sb : FullState}
    {cref forcedv : BitVec 32} {jlvlv : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]}
    {X : XPost} {mb : Mem 64}
    (hDet : ∀ args m Q X, Proof.Learn.Spec.detNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hobt_le : clvl ≤ s.core.cur_level) (hcl_pos : 0 < clvl) (hjl_lt : jlvlv.toNat < clvl)
    (hcr32 : cref.toNat < 2 ^ 31 - 1)
    (hbref : cref.toNat ∈ fullArenaClauseRefsCore sb.core)
    (hbng : fullArenaClauseGarbCore sb.core cref.toNat = false)
    (hbfmem : forcedv.toNat ∈ fullArenaClauseLitsCore sb.core cref.toNat)
    (hbfoth : ∀ q ∈ fullArenaClauseLitsCore sb.core cref.toNat,
      q = forcedv.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
        (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat))
    (hblen : sb.LengthsOk c) (hbw : FullWitnessCutInv c F0 F_cur cut1 sb.core)
    (hbmk : FullLitMarksClear c sb) (hbnd : FullArenaVarsNodup sb)
    (hbext : FullExtScratchOk c sb) (hbcl : sb.core.cur_level = clvl)
    (hbcv : sb.core.cur_vars = s.core.cur_vars) (hbfu : sb.core.fuel = s.core.fuel)
    (hbws2 : sb.scratch.work_stk2 = s.scratch.work_stk2) (hbdm : sb.core.dense_mode = 0#64)
    (hbpr : sb.core.probing = s.core.probing)
    (hf_lvl_sb : (sb.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvl)
    (hf_lt : forcedv.toNat < 2 * s.core.cur_vars)
    (hmb : (FullMem c sb ⋆ R) mb) (hQ : OneLitPost c F0 F_cur s R Q) :
    wp Γ Q X (oneLitTailExpr c.hdr jlvlv forcedv cref) mb := by
  have hj_lt_cl : jlvlv.toNat < sb.core.cur_level := by rw [hbcl]; exact hjl_lt
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold oneLitTailExpr; c0_call hDet
  dsimp only [Proof.Learn.Spec.detNewLevelSpec]
  refine FullContract.intro (w := ()) hblen (by
    have := hbw.cur_level_le; have := hblen.core_ok.trail_end_le
    have := hblen.core_ok.cur_vars_le; omega) hmb ?_
  rintro ⟨nlvl, ⟨⟩⟩ _ mb' _ ⟨hsb', _, hnlvl⟩ hm_b'
  rw [hsb'] at hm_b'
  obtain ⟨hjl_le_nl, hnl_lt⟩ := hnlvl (by omega) hj_lt_cl
  dsimp only at hjl_le_nl hnl_lt
  rw [hbcl] at hnl_lt
  c0_call hBt
  refine ⟨c, sb, R, rfl, hblen, by
    have := hbw.cur_level_le; have := hblen.core_ok.trail_end_le
    have := hblen.core_ok.cur_vars_le; omega,
    fun h => by have := hbw.cur_level_le; have := hblen.core_ok.trail_end_le
                have := hblen.core_ok.cur_vars_le; omega,
    hbw.trail_lits_lt, hm_b', ?_⟩
  dsimp only
  intro vals2 lvl2 rsns2 trl2 tp2 te2 prop2 cl2 unass2 sc2 m2 hlen2 _ _ hcl2 hpres _ _ hvl2 _ hw2
    hm2
  have hcl2_eq : cl2 = nlvl.toNat := by rw [hcl2, hbcl]; omega
  have hw2' := hw2 F0 F_cur hbw.toFullOtfsWitnessInv (by rw [hbcl]; exact hnl_lt)
  obtain ⟨hvals2, hlvl2⟩ := hvl2 ⟨F0, F_cur, Or.inr hbw.toFullOtfsWitnessInv⟩
  have hcref_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcr32
  have hcref_lg : (cref &&& 0x80000000#32) = 0#32 :=
    (bv32_lit_lo31_props (Nat.lt_trans hcr32 (by omega))).2.2
  have hrsn_pre :
      if (cref &&& 0x80000000#32) ≠ 0#32 then
        let ot := (cref &&& 0x7FFFFFFF#32).toNat
        ot < 2 * sb.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause
          (cnfClause [forcedv.toNat, ot]) ∧
        sb.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (sb.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvlv.toNat
      else
        cref.toNat ∈ fullArenaClauseRefsCore sb.core ∧
        fullArenaClauseGarbCore sb.core cref.toNat = false ∧
        forcedv.toNat ∈ fullArenaClauseLitsCore sb.core cref.toNat ∧
        ∀ q ∈ fullArenaClauseLitsCore sb.core cref.toNat,
          q = forcedv.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
            (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat) := by
    rw [ite_eq_right (fun h => absurd hcref_lg h)]; exact ⟨hbref, hbng, hbfmem, hbfoth⟩
  let hpre : OneLitTailPre c F0 F_cur s sb cut1 clvl jlvlv.toNat forcedv cref :=
    ⟨hblen, hbw, hbmk, hbnd, hbext, hbcl, hobt_le, hbcv, hbfu, hbws2, hbdm, hbpr,
      hbcv ▸ hf_lt, hf_lvl_sb, hcref_ne, hrsn_pre⟩
  c0_hsteps_nogrp
  exact oneLit_after_bt_assign_wp hAss hpre rfl
    (by have := fullInv_max_vars_lt32 c; have := hbw.cur_level_le
        have := hblen.core_ok.trail_end_le; omega)
    hjl_le_nl hnl_lt hlen2 hcl2_eq rfl hpres.2.2.1 hpres.1.1 hpres.1.2 hbdm rfl rfl rfl rfl rfl
    rfl hvals2 hlvl2 hw2' hm2 hQ

theorem wstack_ensure2_ret2_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Jd : Cont []}
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hmw : ModeWatchesInv F_cur s.core) (hm : (FullMem c s ⋆ R) m)
    (hOom : ∀ (s_i : FullState) (wv_i ws_i : List (BitVec 32)) (wl_i : Nat)
      (wu_i : BitVec 64) (wso_i : List (BitVec 32)) (ml_o : Mem 64),
      s_i.core = { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i } →
      s_i.scratch = { s.scratch with wsort := wso_i } →
      s_i.LengthsOk c → ModeWatchesInv F_cur s_i.core →
      (FullMem c { s_i with core := { s_i.core with oom := 1#64 } } ⋆ R) ml_o →
      Q (2#64, ()) ml_o)
    (hJd : ∀ xs ml_d,
      (∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat) (wu_d : BitVec 64)
        (wso_d : List (BitVec 32)),
        s_d.core = { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d } ∧
        s_d.scratch = { s.scratch with wsort := wso_d } ∧
        s_d.LengthsOk c ∧ ModeWatchesInv F_cur s_d.core ∧
        (FullMem c s_d ⋆ R) ml_d) →
      Jd xs ml_d) :
    wp Γ Q X
      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_49 =>
       Expr.load i64 (Arg.var p_49.fst) fun ld =>
       Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_50 =>
       Expr.load i64 (Arg.var p_50.fst) fun ld_9 =>
       Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_9, ())) fun p_51 =>
       Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p_51.fst, Arg.imm 2, ())) fun p_52 =>
       Expr.jnz (Arg.var p_52.fst)
         (Expr.group (fun (_ : Tup Cont [[]]) =>
             Blocks.cons (fun (_ : Tup Val []) =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_54 =>
               Expr.load i64 (Arg.var p_54.fst) fun ld =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_55 =>
               Expr.load i64 (Arg.var p_55.fst) fun ld_10 =>
               Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_10, ())) fun p_56 =>
               Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                 (Arg.var p_56.fst, Arg.imm 2, ())) fun p_57 =>
               Expr.jnz (Arg.var p_57.fst)
                 (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p =>
                  Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                    (Expr.ret (Arg.imm 2#64, ())))
                 (Expr.jump Jd ())) Blocks.nil)
           fun Js =>
           Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun p_53 =>
           Expr.load i64 (Arg.var p_53.fst) fun ld =>
           Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_54 =>
           Expr.jnz (Arg.var p_54.fst)
             (Expr.call (rs := [i64]) (as := [i64]) (bs := [])
               "full_wstack_defrag" (Arg.var c.hdr, ()) fun (_ : Tup Val []) =>
               Expr.jump Js.fst ())
             (Expr.jump Js.fst ()))
         (Expr.jump Jd ())) m := by
  have hcv_lt32 : s.core.cur_vars < 2 ^ 32 := by
    have := hlen.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *; omega
  have hwcap_lt64 : c.wcap < 2 ^ 64 := by
    have := c.hwcap; unfold dimacsBound at *; omega
  have hwlen_le : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  have hlay0 : WatchStackLayout s.core := by
    have h := hmw; unfold ModeWatchesInv at h
    simp only [hdm, ↓reduceIte] at h; exact h.layout
  c0_hsteps_nogrp
  · refine wp_join_group (ts := []) (fun () ml_i =>
      ∃ (s_i : FullState) (wv_i ws_i : List (BitVec 32)) (wl_i : Nat)
        (wu_i : BitVec 64) (wso_i : List (BitVec 32)),
        s_i.core = { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i } ∧
        s_i.scratch = { s.scratch with wsort := wso_i } ∧
        s_i.LengthsOk c ∧ ModeWatchesInv F_cur s_i.core ∧ (FullMem c s_i ⋆ R) ml_i) ?_ ?_
    · rintro _ ⟨⟩ ml_i ⟨s_i, wv_i, ws_i, wl_i, wu_i, wso_i, hsi_c, hsi_sc, hlen_i, hmw_i, hm_i⟩
      have hwli_le : s_i.core.wlen ≤ c.wcap := hlen_i.core_ok.wlen_le
      c0_hsteps
      · exact hOom s_i wv_i ws_i wl_i wu_i wso_i _ hsi_c hsi_sc hlen_i hmw_i (by assumption)
      · exact hJd () ml_i ⟨s_i, wv_i, ws_i, wl_i, wu_i, wso_i, hsi_c, hsi_sc, hlen_i, hmw_i, hm_i⟩
    · intro Ji hJi
      c0_hsteps_nogrp
      · c0_call hDefrag
        refine ⟨c, s, R, rfl, hlen, hlay0, hm,
          fun wv_i ws_i wl_i wso_i ml_i hlen_i hlay_i _ hpres hm_i => ?_⟩
        obtain ⟨s_i, hsi_c, hsi_sc, hm_i'⟩ :
            ∃ s_i : FullState,
              s_i.core = { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i,
                                       wusable := 0#64 } ∧
              s_i.scratch = { s.scratch with wsort := wso_i } ∧
              (FullMem c s_i ⋆ R) ml_i :=
          ⟨_, rfl, rfl, hm_i⟩
        have hmw_i : ModeWatchesInv F_cur s_i.core := by
          rw [hsi_c]
          exact fullWstackDefrag_preserves_modeWatchesInv hmw hlay_i rfl rfl
            (fun _ hr => hr) hpres
        have hlen_i' : s_i.LengthsOk c :=
          ⟨by rw [hsi_c]; exact hlen_i.core_ok, by rw [hsi_sc]; exact hlen_i.scratch_ok⟩
        exact hJi () ml_i ⟨s_i, wv_i, ws_i, wl_i, 0#64, wso_i, hsi_c, hsi_sc, hlen_i', hmw_i,
          hm_i'⟩
      · exact hJi () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
          s.scratch.wsort, rfl, rfl, hlen, hmw, hm⟩
  · exact hJd () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
      s.scratch.wsort, rfl, rfl, hlen, hmw, hm⟩

theorem oneLit_swap_arena_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut1 : Nat} {s_in : FullState} {cref : BitVec 32} {csz_val i j : Nat}
    (hlen : s_in.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut1 s_in.core)
    (hnd : FullArenaVarsNodup s_in) (hext : FullExtScratchOk c s_in)
    (href : cref.toNat ∈ fullArenaClauseRefsCore s_in.core)
    (hng : fullArenaClauseGarbCore s_in.core cref.toNat = false)
    (hsz : fullArenaClauseSizeCore s_in.core cref.toNat = csz_val)
    (hi : i < csz_val) (hj : j < csz_val) (li lj : BitVec 32)
    (hli : li = s_in.core.arena[cref.toNat + 3 + i]?.getD 0#32)
    (hlj : lj = s_in.core.arena[cref.toNat + 3 + j]?.getD 0#32) :
    let ar' := (s_in.core.arena.set (cref.toNat + 3 + i) lj).set (cref.toNat + 3 + j) li
    let s' : FullState := { s_in with core := { s_in.core with arena := ar' } }
    s'.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut1 s'.core ∧
    FullArenaVarsNodup s' ∧ FullExtScratchOk c s' ∧
    fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s_in.core ∧
    cref.toNat ∈ fullArenaClauseRefsCore s'.core ∧
    fullArenaClauseGarbCore s'.core cref.toNat = false ∧
    fullArenaClauseSizeCore s'.core cref.toNat = csz_val ∧
    (fullArenaClauseLitsCore s'.core cref.toNat).Perm
      (fullArenaClauseLitsCore s_in.core cref.toNat) := by
  intro ar' s'
  have har_len := hlen.core_ok.arena_len_arr
  obtain ⟨hw', hrefs', hsz', hng', hperm', hother'⟩ :=
    swapCl_preserves_fullWitnessCut hlen.core_ok hw href (i := i)
      (j := j) (by rw [hsz]; exact hi) (by rw [hsz]; exact hj)
  have har_sym : (s_in.core.arena.set (cref.toNat + 3 + i)
      (s_in.core.arena[cref.toNat + 3 + j]?.getD 0#32)).set (cref.toNat + 3 + j)
      (s_in.core.arena[cref.toNat + 3 + i]?.getD 0#32) = ar' := by
    dsimp only [ar']; rw [← hli, ← hlj]
  have hw_s' : FullWitnessCutInv c F0 F_cur cut1 s'.core := by
    simpa only [s', ← har_sym] using hw'
  have hrefs_s' : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s_in.core := by
    simpa only [s', ← har_sym] using hrefs'
  have hperm_s' : (fullArenaClauseLitsCore s'.core cref.toNat).Perm
      (fullArenaClauseLitsCore s_in.core cref.toNat) := by
    simpa only [s', ← har_sym] using hperm'
  have hsz_s' : fullArenaClauseSizeCore s'.core cref.toNat = csz_val := by
    rw [show fullArenaClauseSizeCore s'.core cref.toNat =
      fullArenaClauseSizeCore s_in.core cref.toNat from by simpa only [s', ← har_sym] using hsz',
      hsz]
  have hng_s' : fullArenaClauseGarbCore s'.core cref.toNat = false := by
    simpa only [s', ← har_sym, hng] using hng'
  have hnd_s' : FullArenaVarsNodup s' := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs_s'] at hr
    by_cases hrc : r = cref.toNat
    · subst r; exact (hperm_s'.map (· / 2)).nodup_iff.mpr (hnd _ hr hng)
    · have ho := hother' r hr hrc; change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [show fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s_in.core r from by
        simpa only [s', ← har_sym] using ho.2.2]
      change fullArenaClauseGarbCore s'.core r = false at hngr
      simp only [s', ← har_sym] at hngr; rw [ho.2.1] at hngr; exact hnd r hr hngr
  exact ⟨⟨{ hlen.core_ok with arena_len_arr := by simp [s', ar', har_len] }, hlen.scratch_ok⟩,
    hw_s', hnd_s', ⟨fun k hk => by
      change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s'.core
      rw [hrefs_s']; exact hext.1 k hk, hext.2⟩,
    hrefs_s', by rw [hrefs_s']; exact href, hng_s', hsz_s', hperm_s'⟩

end

private theorem oneLit_oom2_finish {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut1 clvl : Nat} {s s_in s_i : FullState} {wv_i ws_i wso_i : List (BitVec 32)}
    {wl_i : Nat} {wu_i : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]} {ml_o : Mem 64}
    (hw_in : FullWitnessCutInv c F0 F_cur cut1 s_in.core)
    (hmk_in : FullLitMarksClear c s_in) (hnd_in : FullArenaVarsNodup s_in)
    (hext_in : FullExtScratchOk c s_in) (hbin : s.core.confl_type ≠ 1#64)
    (h_stat_in : s_in.core.cur_vars = s.core.cur_vars ∧ s_in.core.cur_level = clvl ∧
      s_in.core.fuel = s.core.fuel ∧ s_in.scratch.work_stk2 = s.scratch.work_stk2 ∧
      s_in.core.dense_mode = 0#64 ∧ s_in.core.probing = s.core.probing)
    (hsi_c : s_i.core = { s_in.core with wvec := wv_i, wstk := ws_i, wlen := wl_i,
                                         wusable := wu_i })
    (hsi_sc : s_i.scratch = { s_in.scratch with wsort := wso_i })
    (hlen_i : s_i.LengthsOk c) (hmw_i : ModeWatchesInv F_cur s_i.core)
    (hm_o : (FullMem c { s_i with core := { s_i.core with oom := 1#64 } } ⋆ R) ml_o)
    (hQ : OneLitPost c F0 F_cur s R Q) : Q (2#64, ()) ml_o := by
  obtain ⟨hcv_in, _, hfu_in, hws2_in, hdm_in, hpr_in⟩ := h_stat_in
  have hw_i : FullWitnessCutInv c F0 F_cur cut1 s_i.core := by
    rw [hsi_c] at hmw_i ⊢; exact oneLit_canonCut_with_watches hw_in hmw_i
  let s_io : FullState := { s_i with core := { s_i.core with oom := 1#64 } }
  have hnd_io : FullArenaVarsNodup s_io := fun r hr hgr => by
    change r ∈ fullArenaClauseRefsCore s_i.core at hr
    have hrf : fullArenaClauseRefsCore s_i.core = fullArenaClauseRefsCore s_in.core := by
      simp [fullArenaClauseRefsCore, hsi_c]
    rw [hrf] at hr
    change ((fullArenaClauseLitsCore s_i.core r).map (· / 2)).Nodup
    rw [show fullArenaClauseLitsCore s_i.core r = fullArenaClauseLitsCore s_in.core r by
      simp [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hsi_c]]
    exact hnd_in r hr (by
      dsimp only [s_io] at hgr; change fullArenaClauseGarbCore s_in.core r = false
      simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hsi_c] using hgr)
  have hext_io : FullExtScratchOk c s_io := ⟨fun i hi => by
    change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s_i.core
    have hrf : fullArenaClauseRefsCore s_i.core = fullArenaClauseRefsCore s_in.core := by
      simp [fullArenaClauseRefsCore, hsi_c]
    have hll : s_i.scratch.last_learned = s_in.scratch.last_learned := by rw [hsi_sc]
    rw [hrf, hll]; exact hext_in.1 i hi,
    by change s_i.scratch.extend_len ≤ c.extend_cap; rw [hsi_sc]; exact hext_in.2⟩
  have hmk_io : FullLitMarksClear c s_io :=
    ⟨fun v hv => by change s_i.core.mrk[v]?.getD 0#8 = 0#8; rw [hsi_c]; exact hmk_in.1 v hv,
     fun l hl => by
       change s_i.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hsi_c]; exact hmk_in.2 l hl⟩
  exact hQ 2#64 s_io ml_o ⟨{ hlen_i.core_ok with }, hlen_i.scratch_ok⟩
    (Or.inr (Or.inr (Or.inl rfl)))
    (by dsimp [s_io]; rw [hsi_c]; exact hcv_in)
    (by dsimp [s_io]; rw [hsi_c]; exact hfu_in)
    (by dsimp [s_io]; rw [hsi_sc]; exact hws2_in)
    (by dsimp [s_io]; rw [hsi_c]; exact hdm_in)
    (by dsimp [s_io]; rw [hsi_c]; exact hpr_in)
    hmk_io hnd_io hext_io (fun h => absurd h hbin) (fun h => by cases h) (fun h => by cases h)
    (fun _ => oneLit_otfsInv_with_oom hw_i.toFullOtfsWitnessInv 1#64) (fun h => by cases h)
    hm_o

public section

theorem oneLit_swap_push_branch_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl pos_n hp_n csz_val : Nat} {s s_in : FullState}
    {cref lit_pos high_lit : BitVec 32} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {Js_out : Cont []} {m_in : Mem 64}
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hlen_in : s_in.LengthsOk c) (hw_in : FullWitnessCutInv c F0 F_cur cut1 s_in.core)
    (hmk_in : FullLitMarksClear c s_in) (hnd_in : FullArenaVarsNodup s_in)
    (hext_in : FullExtScratchOk c s_in)
    (hbin : s.core.confl_type ≠ 1#64)
    (hcr32 : cref.toNat < 2 ^ 31 - 1) (hcsz_ge3 : 3 ≤ csz_val)
    (hpos_lt2 : pos_n < 2) (hhp_lt : hp_n < csz_val) (hhp_ne : hp_n ≠ pos_n)
    (hcsz_bd : cref.toNat + 3 + csz_val ≤ s_in.core.arena_len)
    (hcref_in : cref.toNat ∈ fullArenaClauseRefsCore s_in.core)
    (hng_in : fullArenaClauseGarbCore s_in.core cref.toNat = false)
    (hsz_in : fullArenaClauseSizeCore s_in.core cref.toNat = csz_val)
    (hlit_pos : lit_pos = s_in.core.arena[cref.toNat + 3 + pos_n]?.getD 0#32)
    (hhigh : high_lit = s_in.core.arena[cref.toNat + 3 + hp_n]?.getD 0#32)
    (hhi_lt : high_lit.toNat < 2 * s_in.core.cur_vars)
    (h_stat_in : s_in.core.cur_vars = s.core.cur_vars ∧ s_in.core.cur_level = clvl ∧
      s_in.core.fuel = s.core.fuel ∧ s_in.scratch.work_stk2 = s.scratch.work_stk2 ∧
      s_in.core.dense_mode = 0#64 ∧ s_in.core.probing = s.core.probing)
    (h_confl_eq : ∀ q, q ∈ fullArenaClauseLitsCore s_in.core cref.toNat ↔
      q ∈ fullArenaClauseLits s s.core.confl_ref.toNat)
    (hm_in : (FullMem c s_in ⋆ R) m_in) (hQ : OneLitPost c F0 F_cur s R Q)
    (hJs : ∀ mb,
      (∃ s_out : FullState,
        s_out.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut1 s_out.core ∧
        FullLitMarksClear c s_out ∧ FullArenaVarsNodup s_out ∧
        FullExtScratchOk c s_out ∧
        s_out.core.cur_vars = s.core.cur_vars ∧ s_out.core.cur_level = clvl ∧
        s_out.core.fuel = s.core.fuel ∧ s_out.scratch.work_stk2 = s.scratch.work_stk2 ∧
        s_out.core.dense_mode = 0#64 ∧ s_out.core.probing = s.core.probing ∧
        s_out.core.vals = s_in.core.vals ∧ s_out.core.lvl = s_in.core.lvl ∧
        s_out.core.trl = s_in.core.trl ∧
        s_out.core.trail_end = s_in.core.trail_end ∧ s_out.core.arena_len = s_in.core.arena_len ∧
        s_out.core.confl_type = s_in.core.confl_type ∧
        s_out.core.confl_ref = s_in.core.confl_ref ∧
        cref.toNat ∈ fullArenaClauseRefsCore s_out.core ∧
        fullArenaClauseGarbCore s_out.core cref.toNat = false ∧
        fullArenaClauseSizeCore s_out.core cref.toNat = csz_val ∧
        (∀ q, q ∈ fullArenaClauseLitsCore s_out.core cref.toNat ↔
          q ∈ fullArenaClauseLits s s.core.confl_ref.toNat) ∧
        (FullMem c s_out ⋆ R) mb) → Js_out () mb) :
    ∀ posv hpv : BitVec 32, posv = BitVec.ofNat 32 pos_n → hpv = BitVec.ofNat 32 hp_n →
      wp Γ Q X
        (Expr.let_ (Op.mk (.cmp .ugt i32 .bool rfl) (Arg.var hpv, Arg.imm 1, ())) fun p_42 =>
         Expr.jnz (Arg.var p_42.fst)
           (Expr.let_ (Op.mk (.xor i32) (Arg.var posv, Arg.imm 1, ())) fun p_43 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_44 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var p_44.fst, Arg.imm 3, ())) fun p_45 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_43.fst, ())) fun p_46 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var p_45.fst, Arg.var p_46.fst, ())) fun p_47 =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var p_47.fst, Arg.imm 4, ())) fun p_48 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_48.fst, ())) fun p_49 =>
            Expr.load i32 (Arg.var p_49.fst) fun oth =>
            Expr.group (fun (_Js : Tup Cont [[]]) => Blocks.cons (fun (_ : Tup Val []) =>
              Expr.let_ (Op.mk (.and i32) (Arg.var oth, Arg.imm 2147483647, ())) fun p_50 =>
              Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "full_watch_push"
                (Arg.var c.hdr, Arg.var high_lit, Arg.var p_50.fst, Arg.var cref,
                  Arg.imm 2, ()) fun p_51 =>
              Expr.jnz (Arg.var p_51.fst)
                (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_52 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var p_52.fst, Arg.imm 3, ())) fun p_53 =>
                 Expr.let_ (Op.mk (.zext 32 64) (Arg.var posv, ())) fun p_54 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var p_53.fst, Arg.var p_54.fst, ())) fun p_55 =>
                 Expr.let_ (Op.mk (.mul i64) (Arg.var p_55.fst, Arg.imm 4, ())) fun p_56 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_56.fst, ())) fun p_57 =>
                 Expr.store (t := i32) (Arg.var high_lit) (Arg.var p_57.fst)
                   (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_58 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var p_58.fst, Arg.imm 3, ())) fun p_59 =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var hpv, ())) fun p_60 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var p_59.fst, Arg.var p_60.fst, ()))
                      fun p_61 =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var p_61.fst, Arg.imm 4, ())) fun p_62 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_62.fst, ()))
                      fun p_63 =>
                    Expr.store (t := i32) (Arg.var lit_pos) (Arg.var p_63.fst)
                      (Expr.call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
                        (Arg.var c.hdr, Arg.var lit_pos, Arg.var cref, ()) fun _ =>
                        Expr.jump Js_out ())))
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p =>
                 Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                   (Expr.ret (Arg.imm 2, ())))
              ) Blocks.nil) fun _Js =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_49 =>
            Expr.load i64 (Arg.var p_49.fst) fun ld =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_50 =>
            Expr.load i64 (Arg.var p_50.fst) fun ld_9 =>
            Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_9, ())) fun p_51 =>
            Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
              (Arg.var p_51.fst, Arg.imm 2, ())) fun p_52 =>
            Expr.jnz (Arg.var p_52.fst)
              (Expr.group (fun (_ : Tup Cont [[]]) =>
                  Blocks.cons (fun (_ : Tup Val []) =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_54 =>
                    Expr.load i64 (Arg.var p_54.fst) fun ld =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_55 =>
                    Expr.load i64 (Arg.var p_55.fst) fun ld_10 =>
                    Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_10, ())) fun p_56 =>
                    Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                      (Arg.var p_56.fst, Arg.imm 2, ())) fun p_57 =>
                    Expr.jnz (Arg.var p_57.fst)
                      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p =>
                       Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                         (Expr.ret (Arg.imm 2, ())))
                      (Expr.jump _Js.fst ())) Blocks.nil)
                fun Js =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun p_53 =>
                Expr.load i64 (Arg.var p_53.fst) fun ld =>
                Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                  (Arg.var ld, Arg.imm 0, ())) fun p_54 =>
                Expr.jnz (Arg.var p_54.fst)
                  (Expr.call (rs := [i64]) (as := [i64]) (bs := [])
                    "full_wstack_defrag" (Arg.var c.hdr, ()) fun _ => Expr.jump Js.fst ())
                  (Expr.jump Js.fst ()))
              (Expr.jump _Js.fst ()))
         (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 3, ())) fun p =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.var posv, ())) fun p_42 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.var p_42.fst, ())) fun p =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
          Expr.store (t := i32) (Arg.var high_lit) (Arg.var p.fst)
            (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p =>
             Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 3, ())) fun p =>
             Expr.let_ (Op.mk (.zext 32 64) (Arg.var hpv, ())) fun p_43 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.var p_43.fst, ())) fun p =>
             Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
             Expr.store (t := i32) (Arg.var lit_pos) (Arg.var p.fst)
               (Expr.jump Js_out ())))) m_in := by
  rintro posv hpv rfl rfl
  have ⟨hcv_in, hcl_in, hfu_in, hws2_in, hdm_in, hpr_in⟩ := h_stat_in
  have har_len_in := hlen_in.core_ok.arena_len_arr
  have har_le_in := hlen_in.core_ok.arena_len_le
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have hcr_pos_z : (cref.setWidth 64 + 3 + (BitVec.ofNat 32 pos_n).setWidth 64).toNat =
      cref.toNat + 3 + pos_n := by
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
      zext_toNat (BitVec.ofNat 32 pos_n) (by decide), Proof.Spec.bv32_ofNat_toNat (by omega),
      show (3 : BitVec 64).toNat = 3 from rfl]; omega
  have hcr_hp_z : (cref.setWidth 64 + 3 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat =
      cref.toNat + 3 + hp_n := by
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
      zext_toNat (BitVec.ofNat 32 hp_n) (by decide), Proof.Spec.bv32_ofNat_toNat (by omega),
      show (3 : BitVec 64).toNat = 3 from rfl]; omega
  c0_hsteps_nogrp
  · let oth_n := pos_n ^^^ 1
    have hoth_lt2 : oth_n < 2 := by
      rcases (by omega : pos_n = 0 ∨ pos_n = 1) with rfl | rfl <;> decide
    have hxor_bv : (BitVec.ofNat 32 pos_n ^^^ (1 : BitVec 32)) = BitVec.ofNat 32 oth_n := by
      apply BitVec.eq_of_toNat_eq
      rcases (by omega : pos_n = 0 ∨ pos_n = 1) with rfl | rfl <;> decide
    have hcr_oth_z : (cref.setWidth 64 + 3 +
        ((BitVec.ofNat 32 pos_n) ^^^ 1).setWidth 64).toNat = cref.toNat + 3 + oth_n := by
      rw [hxor_bv, BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
        zext_toNat (BitVec.ofNat 32 oth_n) (by decide), Proof.Spec.bv32_ofNat_toNat (by omega),
        show (3 : BitVec 64).toNat = 3 from rfl]; omega
    have hcr_oth_bd : (cref.setWidth 64 + 3 +
        ((BitVec.ofNat 32 pos_n) ^^^ 1).setWidth 64).toNat < s_in.core.arena.length := by
      rw [hcr_oth_z, har_len_in]; omega
    let oth := s_in.core.arena[(cref.setWidth 64 + 3 +
      ((BitVec.ofNat 32 pos_n) ^^^ 1).setWidth 64).toNat]'hcr_oth_bd
    have hoth_lt_vars : oth.toNat < 2 * s_in.core.cur_vars := by
      have hoth_mem : oth.toNat ∈ fullArenaClauseLitsCore s_in.core cref.toNat := by
        rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_in]; omega)]
        exact ⟨oth_n, by rw [hsz_in]; omega, by
          dsimp only [oth]; exact congrArg BitVec.toNat (getElem_eq_of_idx hcr_oth_z.symm)⟩
      exact hw_in.arena.lits_lt cref.toNat hcref_in hng_in _ hoth_mem
    have hoth_31 : oth.toNat < 2 ^ 31 - 1 := by
      have := hlen_in.core_ok.cur_vars_le; omega
    have hoth_31' : oth.toNat < 2 ^ 31 := by omega
    have hoth_m_ne : oth &&& 0x7FFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [(bv32_lit_lo31_props hoth_31').1]; exact bv32_lit_neq_ff hoth_31
    have hoth_m_and : ((oth &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
      rw [(bv32_lit_lo31_props hoth_31').1]; exact (bv32_lit_lo31_props hoth_31').2.2
    have hhi_31 : high_lit.toNat < 2 ^ 31 - 1 := by
      have := hlen_in.core_ok.cur_vars_le; omega
    have hcr_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcr32
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun () ml_d =>
      ∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat) (wu_d : BitVec 64)
        (wso_d : List (BitVec 32)),
        s_d.core = { s_in.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d } ∧
        s_d.scratch = { s_in.scratch with wsort := wso_d } ∧
        s_d.LengthsOk c ∧ ModeWatchesInv F_cur s_d.core ∧ (FullMem c s_d ⋆ R) ml_d) ?_ ?_
    · rintro _ ⟨⟩ ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc, hlen_d, hmw_d, hm_d⟩
      clear hm_in
      have hsd_dm : s_d.core.dense_mode = 0#64 := by rw [hsd_c]; exact hdm_in
      have hsd_cv : s_d.core.cur_vars = s_in.core.cur_vars := by rw [hsd_c]
      have hsd_cref : cref.toNat ∈ fullArenaClauseRefsCore s_d.core := by
        change cref.toNat ∈ fullArenaClauseRefsCore s_in.core at hcref_in
        rwa [show fullArenaClauseRefsCore s_d.core = fullArenaClauseRefsCore s_in.core by
          simp [fullArenaClauseRefsCore, hsd_c]]
      have hlay_d : WatchStackLayout s_d.core := by
        have h := hmw_d; unfold ModeWatchesInv at h; rw [ite_eq_left hsd_dm] at h; exact h.layout
      c0_hsteps_nogrp
      c0_call hPush
      refine ⟨c, s_d, R, rfl, hlen_d, hlay_d, fun h => absurd h (by decide),
        fun _ => ⟨hoth_m_ne, hcr_ne⟩, hm_d,
        fun ok_p wv_p ws_p wl_p wu_p wso_p m_p hlen_p hlay_p hoth_p hT hF hm_p => ?_⟩
      clear hm_d
      obtain ⟨s_p, hsp_d_eq, hm_p'⟩ : ∃ s_p : FullState,
          s_p = { s_d with
            core := { s_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p }
            scratch := { s_d.scratch with wsort := wso_p } } ∧
          (FullMem c s_p ⋆ R) m_p := ⟨_, rfl, hm_p⟩
      clear hm_p
      have hsp_c : s_p.core = { s_in.core with
          wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } := by
        rw [hsp_d_eq]; dsimp only; rw [hsd_c]
      have hsp_sc : s_p.scratch = { s_in.scratch with wsort := wso_p } := by
        rw [hsp_d_eq]; dsimp only; rw [hsd_sc]
      have hlen_p' : s_p.LengthsOk c := by
        rw [hsp_d_eq]; exact ⟨{ hlen_p.core_ok with }, hlen_p.scratch_ok⟩
      by_cases hok_c : ok_p = true
      · subst hok_c
        obtain ⟨_, _, hsz_p, hsame_p, hw0_p, hw1_p⟩ := hT rfl
        have hm_wp : ModeWatchesInv F_cur s_p.core := by
          have hsp_d_c : s_p.core = { s_d.core with
              wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } :=
            congrArg FullState.core hsp_d_eq
          rw [hsp_d_c]
          exact watchPush_large_preserves hsd_dm hmw_d (by rw [hsd_cv]; exact hhi_lt)
            hlay_p hoth_p hsz_p hsame_p hw0_p (hw1_p rfl) hoth_m_and (by omega) hsd_cref
        have hw_p : FullWitnessCutInv c F0 F_cur cut1 s_p.core := by
          rw [hsp_c] at hm_wp ⊢; exact oneLit_canonCut_with_watches hw_in hm_wp
        have hnd_p : FullArenaVarsNodup s_p := fun r hr hgr => by
          change r ∈ fullArenaClauseRefsCore s_p.core at hr
          have hrf : fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s_in.core := by
            simp [fullArenaClauseRefsCore, hsp_c]
          rw [hrf] at hr; change ((fullArenaClauseLitsCore s_p.core r).map (· / 2)).Nodup
          rw [show fullArenaClauseLitsCore s_p.core r = fullArenaClauseLitsCore s_in.core r by
            simp [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hsp_c]]
          exact hnd_in r hr (by
            change fullArenaClauseGarbCore s_in.core r = false
            simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hsp_c] using hgr)
        have hext_p : FullExtScratchOk c s_p := ⟨fun i hi => by
          change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s_p.core
          have hrf : fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s_in.core := by
            simp [fullArenaClauseRefsCore, hsp_c]
          have hll : s_p.scratch.last_learned = s_in.scratch.last_learned := by rw [hsp_sc]
          rw [hrf, hll]; exact hext_in.1 i hi,
          by change s_p.scratch.extend_len ≤ c.extend_cap; rw [hsp_sc]; exact hext_in.2⟩
        have hcref_p : cref.toNat ∈ fullArenaClauseRefsCore s_p.core := by
          simpa [fullArenaClauseRefsCore, hsp_c] using hcref_in
        have hng_p : fullArenaClauseGarbCore s_p.core cref.toNat = false := by
          simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hsp_c] using hng_in
        have hsz_p' : fullArenaClauseSizeCore s_p.core cref.toNat = csz_val := by
          simpa [fullArenaClauseSizeCore, hsp_c] using hsz_in
        have hsp_ar : s_p.core.arena = s_in.core.arena := by rw [hsp_c]
        have hsp_pos_bd : (cref.setWidth 64 + 3 +
            (BitVec.ofNat 32 pos_n).setWidth 64).toNat < s_p.core.arena.length := by
          rw [hcr_pos_z, hsp_ar, har_len_in]; omega
        have hsp_hp_bd : (cref.setWidth 64 + 3 +
            (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
            (s_p.core.arena.set (cref.setWidth 64 + 3 +
              (BitVec.ofNat 32 pos_n).setWidth 64).toNat high_lit).length := by
          rw [List.length_set, hcr_hp_z, hsp_ar, har_len_in]; omega
        obtain ⟨hlen_sw, hw_sw, hnd_sw, hext_sw, hrefs_sw, hcref_sw, hng_sw, hsz_sw, hperm_sw⟩ :=
          oneLit_swap_arena_inv hlen_p' hw_p hnd_p hext_p hcref_p hng_p hsz_p' (i := pos_n)
            (j := hp_n) (by omega) hhp_lt lit_pos high_lit (by rw [hsp_ar]; exact hlit_pos)
            (by rw [hsp_ar]; exact hhigh)
        let ar_sw := (s_p.core.arena.set (cref.toNat + 3 + pos_n) high_lit).set
          (cref.toNat + 3 + hp_n) lit_pos
        let ar_raw := (s_p.core.arena.set (cref.setWidth 64 + 3 +
          (BitVec.ofNat 32 pos_n).setWidth 64).toNat high_lit).set
          (cref.setWidth 64 + 3 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat lit_pos
        have har_eq_sw : ar_raw = ar_sw := by
          dsimp only [ar_raw, ar_sw]; rw [hcr_pos_z, hcr_hp_z]
        let s_sw : FullState := { s_p with core := { s_p.core with arena := ar_sw } }
        have hlay_sw : WatchStackLayout s_sw.core := by
          have h := hw_sw.watches; unfold ModeWatchesInv at h
          rw [ite_eq_left (by change s_p.core.dense_mode = 0#64; rw [hsp_c]; exact hdm_in)] at h
          exact h.layout
        c0_hsteps_nogrp
        · have hm_sw : (FullMem c s_sw ⋆ R) _ :=
            oneLit_fullMem_of_eq (s1 := { s_p with core := { s_p.core with arena := ar_raw } })
              (by assumption) (congrArg (fun a => { s_p.core with arena := a }) har_eq_sw) rfl
          c0_call hUnw
          refine ⟨c, s_sw, R, rfl, hlen_sw, hlay_sw, hm_sw,
            fun wv_u ws_u wu_u m_u hlen_u _ hmw_u hm_u => ?_⟩
          let s_out : FullState :=
            { s_sw with core := { s_sw.core with wvec := wv_u, wstk := ws_u, wusable := wu_u } }
          have hlen_out : s_out.LengthsOk c := ⟨hlen_u.core_ok, hlen_u.scratch_ok⟩
          have hw_out : FullWitnessCutInv c F0 F_cur cut1 s_out.core :=
            oneLit_canonCut_with_watches hw_sw (hmw_u F_cur hw_sw.watches)
          have hm_out' : FullLitMarksClear c s_out :=
            ⟨fun v hv => by
               change s_p.core.mrk[v]?.getD 0#8 = 0#8; rw [hsp_c]; exact hmk_in.1 v hv,
             fun l hl => by
               change s_p.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hsp_c]; exact hmk_in.2 l hl⟩
          have hnd_out : FullArenaVarsNodup s_out := fun r hr hgr => by
            change r ∈ fullArenaClauseRefsCore s_out.core at hr
            have hr' : r ∈ fullArenaClauseRefsCore s_sw.core := hr
            have hg' : fullArenaClauseGarbCore s_sw.core r = false := hgr
            exact hnd_sw r hr' hg'
          have hlits_out : ∀ q, q ∈ fullArenaClauseLitsCore s_out.core cref.toNat ↔
              q ∈ fullArenaClauseLits s s.core.confl_ref.toNat := fun q => by
            change q ∈ fullArenaClauseLitsCore s_sw.core cref.toNat ↔ _
            rw [hperm_sw.mem_iff]
            simpa only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hsp_c] using
              h_confl_eq q
          c0_hsteps
          exact hJs _ ⟨s_out, hlen_out, hw_out, hm_out', hnd_out, hext_sw,
            by rw [show s_out.core.cur_vars = s_in.core.cur_vars by simp [s_out, s_sw, hsp_c]]
               exact hcv_in,
            by rw [show s_out.core.cur_level = s_in.core.cur_level by simp [s_out, s_sw, hsp_c]]
               exact hcl_in,
            by rw [show s_out.core.fuel = s_in.core.fuel by simp [s_out, s_sw, hsp_c]]
               exact hfu_in,
            by rw [show s_out.scratch.work_stk2 = s_in.scratch.work_stk2 by
                 simp [s_out, s_sw, hsp_sc]]; exact hws2_in,
            by rw [show s_out.core.dense_mode = s_in.core.dense_mode by simp [s_out, s_sw, hsp_c]]
               exact hdm_in,
            by rw [show s_out.core.probing = s_in.core.probing by simp [s_out, s_sw, hsp_c]]
               exact hpr_in,
            by simp [s_out, s_sw, hsp_c],
            by simp [s_out, s_sw, hsp_c],
            by simp [s_out, s_sw, hsp_c], by simp [s_out, s_sw, hsp_c],
            by simp [s_out, s_sw, hsp_c], by simp [s_out, s_sw, hsp_c],
            by simp [s_out, s_sw, hsp_c], hcref_sw, hng_sw, hsz_sw, hlits_out, hm_u⟩
        · exfalso; exact Bool.noConfusion ‹_›
      · have hok_f : ok_p = false := Bool.eq_false_iff.mpr hok_c
        subst hok_f
        obtain ⟨hsame_f, _⟩ := hF rfl
        have hsp_d_c : s_p.core = { s_d.core with
            wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } :=
          congrArg FullState.core hsp_d_eq
        have hm_wpf : ModeWatchesInv F_cur s_p.core := by
          rw [hsp_d_c]
          exact watchPush_fail_preserves hsd_dm hmw_d hlay_p fun l hl =>
            if hle : l = high_lit.toNat then
              by subst l; exact hsame_f (by rw [hsd_cv]; exact hhi_lt)
            else hoth_p l hl hle
        c0_hsteps
        exact oneLit_oom2_finish hw_in hmk_in hnd_in hext_in hbin h_stat_in hsp_c hsp_sc
          hlen_p' hm_wpf (by assumption) hQ
    · intro Jd hJd
      have hmw_in : ModeWatchesInv F_cur s_in.core := hw_in.watches
      exact wstack_ensure2_ret2_wp hDefrag hlen_in hdm_in hmw_in hm_in
        (fun s_i wv_i ws_i wl_i wu_i wso_i ml_o hsi_c hsi_sc hlen_i hmw_i hm_o =>
          oneLit_oom2_finish hw_in hmk_in hnd_in hext_in hbin h_stat_in hsi_c hsi_sc hlen_i
            hmw_i hm_o hQ)
        hJd
  · have hin_pos_bd : (cref.setWidth 64 + 3 +
        (BitVec.ofNat 32 pos_n).setWidth 64).toNat < s_in.core.arena.length := by
      rw [hcr_pos_z, har_len_in]; omega
    have hin_hp_bd : (cref.setWidth 64 + 3 +
        (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
        (s_in.core.arena.set (cref.setWidth 64 + 3 +
          (BitVec.ofNat 32 pos_n).setWidth 64).toNat high_lit).length := by
      rw [List.length_set, hcr_hp_z, har_len_in]; omega
    obtain ⟨hlen_sw, hw_sw, hnd_sw, hext_sw, _, hcref_sw, hng_sw, hsz_sw, hperm_sw⟩ :=
      oneLit_swap_arena_inv hlen_in hw_in hnd_in hext_in hcref_in hng_in hsz_in
        (i := pos_n) (j := hp_n) (by omega) hhp_lt lit_pos high_lit hlit_pos hhigh
    let ar_sw := (s_in.core.arena.set (cref.toNat + 3 + pos_n) high_lit).set
      (cref.toNat + 3 + hp_n) lit_pos
    let ar_raw := (s_in.core.arena.set (cref.setWidth 64 + 3 +
      (BitVec.ofNat 32 pos_n).setWidth 64).toNat high_lit).set
      (cref.setWidth 64 + 3 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat lit_pos
    have har_eq_sw : ar_raw = ar_sw := by
      dsimp only [ar_raw, ar_sw]; rw [hcr_pos_z, hcr_hp_z]
    let s_out : FullState := { s_in with core := { s_in.core with arena := ar_sw } }
    c0_hsteps
    have hm_out : (FullMem c s_out ⋆ R) _ :=
      oneLit_fullMem_of_eq (s1 := { s_in with core := { s_in.core with arena := ar_raw } })
        (by assumption) (congrArg (fun a => { s_in.core with arena := a }) har_eq_sw) rfl
    exact hJs _ ⟨s_out, hlen_sw, hw_sw, hmk_in, hnd_sw, hext_sw, hcv_in, hcl_in, hfu_in,
      hws2_in, hdm_in, hpr_in, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcref_sw, hng_sw, hsz_sw,
      fun q => by
        change q ∈ fullArenaClauseLitsCore s_out.core cref.toNat ↔ _
        rw [hperm_sw.mem_iff]; exact h_confl_eq q,
      hm_out⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Learn
