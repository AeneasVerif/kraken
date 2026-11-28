/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp2a
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1

/-!
# Kissat BVE `Func.wp` Helpers — Part 2b (`Wp2b`: transitions for `full_bve_var_m7_wp`)

Pure arithmetic, separation-invariant transport, `FullResBufOkW` congruence, and per-step
transition lemmas for `full_bve_var_m7_wp` (`Wp2.lean`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec

/-! ## 1. `FullResBufOkW` Congruence & Pure BitVec Helpers -/

public theorem bve_resBuf_congr {F_cur : List (List Nat)} {s s' : FullState}
    {r_end r0 : Nat}
    (hrb : FullResBufOkW F_cur s r_end r0)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hle : r0 ≤ r_end)
    (hscr : ∀ idx, r0 ≤ idx → idx < r_end →
      s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) :
    FullResBufOkW F_cur s' r_end r0 := by
  induction hrb with
  | nil => exact FullResBufOkW.nil
  | cons hp hsz hlits hnd hent hrest ih =>
    rename_i p sz
    have hsp : s'.scratch.scratch_buf[p]? = s.scratch.scratch_buf[p]? :=
      hscr p (Nat.le_refl p) (by omega)
    have hsarg : ∀ k < sz, s'.scratch.scratch_buf[p + 1 + k]? = s.scratch.scratch_buf[p + 1 + k]? :=
      fun k hk => hscr (p + 1 + k) (by omega) (by omega)
    have hmapv :
        List.map (fun k => (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2)
          (List.range sz) =
        List.map (fun k => (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2)
          (List.range sz) := by
      apply List.map_congr_left
      intro k hk; simp only [List.mem_range] at hk; simp [hsarg k hk]
    have hmapl :
        List.map (fun k => (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat)
          (List.range sz) =
        List.map (fun k => (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat)
          (List.range sz) := by
      apply List.map_congr_left
      intro k hk; simp only [List.mem_range] at hk; simp [hsarg k hk]
    refine FullResBufOkW.cons hp (by rw [hsp]; exact hsz)
      (fun k hk => by rw [hsarg k hk, hcv]; exact hlits k hk)
      (by rw [hmapv]; exact hnd) (by rw [hmapl]; exact hent)
      (ih (by omega) fun idx h1 h2 => hscr idx (by omega) h2)

public theorem bve_cur_vars_lt31 {c : FullCfg} {s : FullState}
    (hlok : FullState.LengthsOk c s) : s.core.cur_vars < 2 ^ 31 := by
  have h1 := hlok.core_ok.cur_vars_le
  have h2 := c.hmaxv
  unfold dimacsBound at h2
  omega

public theorem bve_scratch_cap_lt32 {c : FullCfg} : c.scratch_cap < 2 ^ 32 := by
  have h := c.hscr
  unfold dimacsBound at h
  omega

public theorem bve_bv32_shl1 {v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    (v <<< 1#32).toNat = 2 * v.toNat := by
  simp [BitVec.toNat_shiftLeft]; omega

public theorem bve_bv32_shl1_or1 {v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    ((v <<< 1#32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hsh : (v <<< 1#32).toNat = 2 * v.toNat := bve_bv32_shl1 hv
  have hor : ((v <<< 1#32) ||| 1#32).toNat = (v <<< 1#32).toNat ||| 1 := by
    simp [BitVec.toNat_or]
  rw [hor, hsh]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero =>
    have hm : (2 * v.toNat) % 2 = 0 := by omega
    have hm1 : (2 * v.toNat + 1) % 2 = 1 := by omega
    simp [Nat.testBit, hm, hm1]
  | succ j =>
    have hd : (2 * v.toNat + 1) / 2 = v.toNat := by omega
    have hm2 : (2 * v.toNat) / 2 = v.toNat := by omega
    simp [Nat.testBit_succ, hm2, hd]

public theorem bve_i8_slt0_eq_ff {x : BitVec 8}
    (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) (hslt : x.slt 0#8 = true) :
    x = 0xFF#8 := by
  rcases hx with rfl | rfl | rfl
  · simp at hslt
  · simp at hslt
  · rfl

public theorem bve_u32_mask_word_idx {m8 : Bool} {i : BitVec 32} {occ scap : Nat}
    (hocc : occ ≤ bveOccLim m8) (hi : i.toNat < occ) (hm8 : m8 = decide (16384 ≤ scap)) :
    bvePosMask m8 + (i >>> 5#32).toNat < bveROff m8 ∧
    bveNegMask m8 + (i >>> 5#32).toNat < bveROff m8 ∧
    ((BitVec.ofNat 32 (bvePosMask m8) + (i >>> 5#32)).toNat =
      bvePosMask m8 + (i >>> 5#32).toNat) ∧
    ((BitVec.ofNat 32 (bveNegMask m8) + (i >>> 5#32)).toNat =
      bveNegMask m8 + (i >>> 5#32).toNat) := by
  have hbi : BitVec.ofNat 32 i.toNat = i := by simp
  have hshift : (i >>> 5#32).toNat = i.toNat / 32 := by
    simp [Nat.shiftRight_eq_div_pow]
  have hbm := bve_mask_idx_lt hocc hi hm8
  rw [hbi] at hbm
  have hro : bveROff m8 ≤ 4192 := by cases m8 <;> simp [bveROff]
  have hpm : bvePosMask m8 < 2 ^ 32 := by cases m8 <;> simp [bvePosMask]
  have hnm : bveNegMask m8 < 2 ^ 32 := by cases m8 <;> simp [bveNegMask]
  refine ⟨hbm.1, hbm.2, ?_, ?_⟩
  · simp [BitVec.toNat_add, Nat.mod_eq_of_lt hpm, Nat.shiftRight_eq_div_pow]; omega
  · simp [BitVec.toNat_add, Nat.mod_eq_of_lt hnm, Nat.shiftRight_eq_div_pow]; omega

/-! ## 2. `full_set_inactive`, `bve_cnt`, `oom`, Early-UNSAT Transitions -/

public theorem bve_set_inactive_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {flags' : List (BitVec 32)} {unass' : BitVec 64} {sc' : FullScratch}
    {r_end r0 : Nat}
    (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hrb : FullResBufOkW F_cur s r_end r0) (hle : r0 ≤ r_end)
    (hlok' : FullState.LengthsOk c
      { core := { s.core with unassigned := unass', flags := flags' }, scratch := sc' })
    (hp : FullProbeScratchPres s
      { core := { s.core with unassigned := unass', flags := flags' }, scratch := sc' }) :
    let s' : FullState :=
      { core := { s.core with unassigned := unass', flags := flags' }, scratch := sc' }
    FullDenseInvW c F0 F_cur s' ∧ TmkZero s' ∧ FullResBufOkW F_cur s' r_end r0 := by
  intro s'
  have hfw := fullDenseInvW_with_flags_unassigned hdw hlok'.core_ok.flags_len unass'
  have hdw' : FullDenseInvW c F0 F_cur s' :=
    ⟨hlok', hfw.2.1, hfw.2.2.1, hfw.2.2.2.1,
     FullExtScratchOk.of_pres hfw.2.2.2.2.1 hp.1 (fun _ hr => hr), hfw.2.2.2.2.2⟩
  have htmk' : TmkZero s' := by
    intro v hv
    have htm := hp.2.2.2.1
    dsimp [s'] at htm ⊢; rw [htm]; exact htmk v hv
  have hrb' : FullResBufOkW F_cur s' r_end r0 :=
    bve_resBuf_congr hrb rfl hle (fun _ _ _ => by rw [hp.2.2.2.2.1])
  exact ⟨hdw', htmk', hrb'⟩

public theorem bve_bveCnt_add1_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {r_end r0 : Nat}
    (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hrb : FullResBufOkW F_cur s r_end r0) (hle : r0 ≤ r_end) :
    let s' : FullState :=
      { core := s.core, scratch := { s.scratch with bve_cnt := s.scratch.bve_cnt + 1#64 } }
    FullDenseInvW c F0 F_cur s' ∧ TmkZero s' ∧ FullResBufOkW F_cur s' r_end r0 := by
  intro s'
  refine ⟨fullDenseInvW_with_bve_cnt hdw (s.scratch.bve_cnt + 1#64), htmk,
    bve_resBuf_congr hrb rfl hle (fun _ _ _ => rfl)⟩

public theorem bve_oom_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s : FullState}
    (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hcv : s.core.cur_vars = s_start.core.cur_vars)
    (hfl : s.core.fuel.toNat ≤ s_start.core.fuel.toNat) :
    let s' : FullState := { core := { s.core with oom := 1#64 }, scratch := s.scratch }
    FullDenseInv c F0 s' ∧ TmkZero s' ∧
      s_start.core.cur_vars ≤ s'.core.cur_vars ∧
      s'.core.fuel.toNat ≤ s_start.core.fuel.toNat := by
  intro s'
  exact ⟨fullDenseInv_with_oom hdw.toDense 1#64, htmk, by dsimp [s']; omega, by dsimp [s']; omega⟩

private theorem bve_denseInvW_with_incon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    (hcur : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with inconsistent := 1#64 }, scratch := s.scratch } := by
  let s' : FullState := { core := { s.core with inconsistent := 1#64 }, scratch := s.scratch }
  have ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
    f18, f19, f20, f21, f22, f23, f24, f25⟩ := hdw.1.core_ok
  have hlok' : FullState.LengthsOk c s' :=
    ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
      f18, f19, f20, f21, f22, f23, f24, f25⟩,
     hdw.1.scratch_ok⟩
  have hw := hdw.2.1
  have har' : FullArenaClausesInv c F_cur s'.core :=
    ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt, hw.arena.entails⟩
  have hwat' : ModeWatchesInv F_cur s'.core :=
    hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    ⟨hw.ext_sound, fun _ => hcur, har', hwat', hw.cur_level_le, hw.trail_lits_lt,
     hw.trail_vars_nodup, hw.vals_domain, hw.vals_true_iff, hw.vals_false_iff, hw.lvl_le,
     hw.dec_earliest, hw.levels_inhabited, hw.level0_sound, hw.trail_pos_inv, hw.level0_rsn_none,
     hw.frame_trail_lt, hw.frame_trail_mono, hw.frame_trail_before_lt, hw.frame_dec_lt,
     hw.reason_inv, hw.reason_lit_mem⟩
  exact ⟨hlok', hw', ⟨hdw.2.2.1.1, hdw.2.2.1.2⟩, hdw.2.2.2.1,
    FullExtScratchOk.of_pres hdw.2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr => hr, hdw.2.2.2.2.2⟩

public theorem bve_rlen0_ret20 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s : FullState} (res_sz' : BitVec 64)
    (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hcv : s.core.cur_vars = s_start.core.cur_vars)
    (hfl : s.core.fuel.toNat ≤ s_start.core.fuel.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map BitVec.toNat (List.take 0 s.core.tmp)))) :
    let s1 : FullState := { core := s.core, scratch := { s.scratch with res_sz := res_sz' } }
    let s2 : FullState := { core := { s1.core with inconsistent := 1#64 }, scratch := s1.scratch }
    FullDenseInv c F0 s2 ∧ TmkZero s2 ∧
      s_start.core.cur_vars ≤ s2.core.cur_vars ∧
      s2.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧ F0.Unsat := by
  intro s1 s2
  have hcur : (cnfOfClauses F_cur).Unsat := unsat_of_entails_nil (by simpa using hent)
  have hunsat : F0.Unsat := hdw.2.1.ext_sound.2 hcur
  have hdw1 : FullDenseInvW c F0 F_cur s1 := fullDenseInvW_with_res_sz hdw res_sz'
  have hdw2 : FullDenseInvW c F0 F_cur s2 := bve_denseInvW_with_incon hdw1 hcur
  exact ⟨hdw2.toDense, htmk, by dsimp [s2, s1]; omega, by dsimp [s2, s1]; omega, hunsat⟩

public theorem bve_rlen1_conflict_ret20 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s : FullState} (res_sz' : BitVec 64)
    (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hcv : s.core.cur_vars = s_start.core.cur_vars)
    (hfl : s.core.fuel.toNat ≤ s_start.core.fuel.toNat)
    (hul_lt : (s.core.tmp[0]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (htmp_ne : s.core.tmp ≠ [])
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map BitVec.toNat (List.take 1 s.core.tmp))))
    (hslt : (s.core.vals[(s.core.tmp[0]?.getD 0#32).toNat]?.getD 0#8).slt 0#8 = true) :
    let s1 : FullState := { core := s.core, scratch := { s.scratch with res_sz := res_sz' } }
    let s2 : FullState := { core := { s1.core with inconsistent := 1#64 }, scratch := s1.scratch }
    FullDenseInv c F0 s2 ∧ TmkZero s2 ∧
      s_start.core.cur_vars ≤ s2.core.cur_vars ∧
      s2.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧ F0.Unsat := by
  intro s1 s2
  have hneg : s.core.vals[(s.core.tmp[0]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 :=
    bve_i8_slt0_eq_ff (hdw.2.1.vals_domain _ hul_lt) hslt
  have hcur : (cnfOfClauses F_cur).Unsat := by
    cases htmp : s.core.tmp with
    | nil => exact absurd htmp htmp_ne
    | cons u us =>
      simp only [htmp, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil] at hent
      simp only [htmp, List.getElem?_cons_zero, Option.getD_some] at hul_lt hneg
      exact elim_unsat_of_lit_and_neg hent
        (elim_vals_neg_entails hdw.2.1 hdw.2.2.2.2.2.1 hul_lt hneg)
  have hunsat : F0.Unsat := hdw.2.1.ext_sound.2 hcur
  have hdw1 : FullDenseInvW c F0 F_cur s1 := fullDenseInvW_with_res_sz hdw res_sz'
  have hdw2 : FullDenseInvW c F0 F_cur s2 := bve_denseInvW_with_incon hdw1 hcur
  exact ⟨hdw2.toDense, htmk, by dsimp [s2, s1]; omega, by dsimp [s2, s1]; omega, hunsat⟩

/-! ## 3. Collect, Gates & Main Loop `BveVarLoopsInv` Transitions -/

public theorem bve_collect2_congr {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {scr' : List (BitVec 32)} {np v : Nat} {m8 : Bool}
    (hnp : np ≤ bveOccLim m8)
    (hro : bveROff m8 ≤ c.scratch_cap)
    (hhold : ∀ i < c.scratch_cap, i < bveOccLim m8 ∨ bveOccLim m8 + bveOccLim m8 ≤ i →
      scr'[i]? = s.scratch.scratch_buf[i]?)
    (hent : ∀ i < np, FullBveEntryOkW F_cur s (2 * v) (s.scratch.scratch_buf[i]?.getD 0#32)) :
    let s' : FullState := { core := s.core, scratch := { s.scratch with scratch_buf := scr' } }
    ∀ i < np, FullBveEntryOkW F_cur s' (2 * v) (s'.scratch.scratch_buf[i]?.getD 0#32) := by
  intro s' i hi
  have hbm1 : bveOccLim m8 + bveOccLim m8 ≤ bvePosMask m8 := by
    cases m8 <;> simp [bveOccLim, bvePosMask]
  have hbm2 : bvePosMask m8 ≤ bveROff m8 := by
    cases m8 <;> simp [bvePosMask, bveROff]
  have hlt : i < c.scratch_cap := by omega
  have hscr : s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]? :=
    hhold i hlt (Or.inl (by omega))
  simpa [s', hscr] using bveEntry_congr_core (s' := s') (hent i hi) rfl rfl rfl

public theorem bve_loops_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s : FullState} {m8 : Bool} {v np nn : BitVec 32}
    {r_off : BitVec 64} {ext_ok : Bool} {m : Mem 64} {R : Mem 64 → Prop}
    (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hcv : s.core.cur_vars = s_start.core.cur_vars)
    (hfl : s.core.fuel.toNat ≤ s_start.core.fuel.toNat)
    (hent_p : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hent_n : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32))
    (hro : r_off.toNat = bveROff m8) (hro2 : r_off.toNat ≤ c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m) :
    BveVarLoopsInv c F0 F_cur s_start m8 v np nn r_off 0#64 0#64 ext_ok s.scratch.res_sz s m R := by
  refine ⟨hdw, htmk, hcv, hfl, hent_p, hent_n, by omega, hro2, ?_, hm⟩
  rw [hro]; exact FullResBufOkW.nil

public theorem bve_gates_post_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s0 s1 : FullState} {m8 : Bool} {v np nn : BitVec 32}
    {r_off : BitVec 64} {m1 : Mem 64} {R : Mem 64 → Prop}
    (hcv0 : s0.core.cur_vars = s_start.core.cur_vars)
    (hfl0 : s0.core.fuel.toNat ≤ s_start.core.fuel.toNat)
    (hent_p0 : ∀ i < np.toNat, FullBveEntryOkW F_cur s0 (2 * v.toNat)
      (s0.scratch.scratch_buf[i]?.getD 0#32))
    (hent_n0 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s0 (2 * v.toNat + 1)
      (s0.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32))
    (hro : r_off.toNat = bveROff m8) (hro2 : r_off.toNat ≤ c.scratch_cap)
    (hdw1 : FullDenseInvW c F0 F_cur s1) (htmk1 : TmkZero s1)
    (hcv1 : s1.core.cur_vars = s0.core.cur_vars)
    (har1 : s1.core.arena = s0.core.arena) (hal1 : s1.core.arena_len = s0.core.arena_len)
    (hfl1 : s1.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hscp : ∀ i < np.toNat, s1.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?)
    (hscn : ∀ j < nn.toNat,
      s1.scratch.scratch_buf[bveOccLim m8 + j]? = s0.scratch.scratch_buf[bveOccLim m8 + j]?)
    (hm1 : (FullMem c s1 ⋆ R) m1) :
    BveVarLoopsInv c F0 F_cur s_start m8 v np nn
      r_off 0#64 0#64 true s1.scratch.res_sz s1 m1 R := by
  have hp := bve_entries_congr hcv1 har1 hal1 (off := 0)
    (fun i hi => by simpa using hscp i hi) (fun i hi => by simpa using hent_p0 i hi)
  refine ⟨hdw1, htmk1, hcv1.trans hcv0, Nat.le_trans hfl1 hfl0,
    (fun i hi => by simpa using hp i hi),
    bve_entries_congr hcv1 har1 hal1 (off := bveOccLim m8) hscn hent_n0,
    by omega, hro2, ?_, hm1⟩
  rw [hro]; exact FullResBufOkW.nil

public theorem bve_loops_incon_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s : FullState} {m8 : Bool} {v np nn : BitVec 32}
    {rp r_cnt w_est res_sz : BitVec 64} {fit : Bool} {m : Mem 64} {R : Mem 64 → Prop}
    (hinv : BveVarLoopsInv c F0 F_cur s_start m8 v np nn rp r_cnt w_est fit res_sz s m R)
    (hin : s.core.inconsistent ≠ 0#64) :
    FullDenseInv c F0 s ∧ TmkZero s ∧
      s_start.core.cur_vars ≤ s.core.cur_vars ∧
      s.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧ F0.Unsat :=
  ⟨hinv.1.toDense, hinv.2.1, by have := hinv.2.2.1; omega, hinv.2.2.2.1,
   hinv.1.toDense.inconsistent_unsat hin⟩

public theorem bve_loops_resSz_store {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s : FullState} {m8 : Bool} {v np nn : BitVec 32}
    {rp r_cnt w_est res_sz : BitVec 64} {fit : Bool} {m m' : Mem 64} {R : Mem 64 → Prop}
    (hinv : BveVarLoopsInv c F0 F_cur s_start m8 v np nn rp r_cnt w_est fit res_sz s m R)
    (hm' : (FullMem c { core := s.core, scratch := { s.scratch with res_sz := res_sz } } ⋆ R) m') :
    let s' : FullState := { core := s.core, scratch := { s.scratch with res_sz := res_sz } }
    FullDenseInvW c F0 F_cur s' ∧ TmkZero s' ∧
      s'.core.cur_vars = s_start.core.cur_vars ∧
      s'.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s' (2 * v.toNat)
        (s'.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s' (2 * v.toNat + 1)
        (s'.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32)) ∧
      bveROff m8 ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
      FullResBufOkW F_cur s' rp.toNat (bveROff m8) ∧ (FullMem c s' ⋆ R) m' := by
  intro s'
  have h1 := fullDenseInvW_with_res_sz hinv.1 res_sz
  have hp := bve_entries_congr (s := s) (s' := s') rfl rfl rfl (off := 0)
    (fun _ _ => rfl) (fun i hi => by simpa using hinv.2.2.2.2.1 i hi)
  have hn := bve_entries_congr (s := s) (s' := s') rfl rfl rfl (off := bveOccLim m8)
    (fun _ _ => rfl) hinv.2.2.2.2.2.1
  have hrb := bve_resBuf_congr (s' := s') hinv.2.2.2.2.2.2.2.2.1 rfl
    hinv.2.2.2.2.2.2.1 (fun _ _ _ => rfl)
  exact ⟨h1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, (by simpa using hp), hn,
    hinv.2.2.2.2.2.2.1, hinv.2.2.2.2.2.2.2.1, hrb, hm'⟩

public theorem bve_loops_rlen1_assign {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s : FullState} {m8 : Bool} {v np nn : BitVec 32}
    {rp r_cnt w_est res_sz : BitVec 64} {fit : Bool} {m m' : Mem 64} {R : Mem 64 → Prop}
    {flags' : List (BitVec 32)} {unass' : BitVec 64} {phases' : List (BitVec 8)}
    (hinv : BveVarLoopsInv c F0 F_cur s_start m8 v np nn rp r_cnt w_est fit res_sz s m R)
    (htmp_lt : 1 ≤ s.core.tmp.length)
    (hul_lt : (s.core.tmp[0]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[(s.core.tmp[0]?.getD 0#32).toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map BitVec.toNat (List.take 1 s.core.tmp))))
    (hfll : flags'.length = c.max_vars) (hphl : phases'.length = c.max_vars)
    (hm' : (FullMem c
      { core := { s.core with
          unassigned := unass', unflushed := s.core.unflushed + 1#64,
          trail_end := s.core.trail_end + 1,
          vals := (s.core.vals.set (s.core.tmp[0]?.getD 0#32).toNat 1#8).set
            ((s.core.tmp[0]?.getD 0#32).toNat ^^^ 1) 0xFF#8,
          flags := flags',
          lvl := s.core.lvl.set ((s.core.tmp[0]?.getD 0#32).toNat / 2) 0#32,
          rsns := s.core.rsns.set ((s.core.tmp[0]?.getD 0#32).toNat / 2) 0xFFFFFFFF#32,
          trl := s.core.trl.set s.core.trail_end (s.core.tmp[0]?.getD 0#32),
          trail_pos := s.core.trail_pos.set ((s.core.tmp[0]?.getD 0#32).toNat / 2)
            (BitVec.ofNat 32 s.core.trail_end) }
        scratch := { s.scratch with phases := phases' } } ⋆ R) m') :
    let ul := s.core.tmp[0]?.getD 0#32
    let s' : FullState :=
      { core := { s.core with
          unassigned := unass', unflushed := s.core.unflushed + 1#64,
          trail_end := s.core.trail_end + 1,
          vals := (s.core.vals.set ul.toNat 1#8).set (ul.toNat ^^^ 1) 0xFF#8,
          flags := flags',
          lvl := s.core.lvl.set (ul.toNat / 2) 0#32,
          rsns := s.core.rsns.set (ul.toNat / 2) 0xFFFFFFFF#32,
          trl := s.core.trl.set s.core.trail_end ul,
          trail_pos := s.core.trail_pos.set (ul.toNat / 2)
            (BitVec.ofNat 32 s.core.trail_end) }
        scratch := { s.scratch with phases := phases' } }
    BveVarLoopsInv c F0 F_cur s_start m8 v np nn rp r_cnt w_est fit res_sz s' m' R := by
  intro ul s'
  have hent1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]) := by
    cases htmp : s.core.tmp with
    | nil => simp [htmp] at htmp_lt
    | cons u us => simpa [ul, htmp] using hent
  have hdw' : FullDenseInvW c F0 F_cur s' :=
    bve_assign0_preserves_fullDenseInvW hinv.1 hul_lt hun hent1 hfll hphl
  have htmk' : TmkZero s' := hinv.2.1
  have hp := bve_entries_congr (s := s) (s' := s') rfl rfl rfl (off := 0)
    (fun _ _ => rfl) (fun i hi => by simpa using hinv.2.2.2.2.1 i hi)
  have hn := bve_entries_congr (s := s) (s' := s') rfl rfl rfl (off := bveOccLim m8)
    (fun _ _ => rfl) hinv.2.2.2.2.2.1
  have hrb := bve_resBuf_congr (s' := s') hinv.2.2.2.2.2.2.2.2.1 rfl
    hinv.2.2.2.2.2.2.1 (fun _ _ _ => rfl)
  exact ⟨hdw', htmk', hinv.2.2.1, hinv.2.2.2.1, (by simpa using hp), hn,
    hinv.2.2.2.2.2.2.1, hinv.2.2.2.2.2.2.2.1, hrb, hm'⟩

/-! ## 4. Copy Loop `BveCopyInv` & Post-Loop Transitions -/

@[expose] public def BveCopyInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (rp : BitVec 64) (tl : Nat) (k : BitVec 32)
    (s : FullState) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧
  s.core.cur_vars = s0.core.cur_vars ∧ s.core.fuel = s0.core.fuel ∧
  s.core.arena = s0.core.arena ∧ s.core.arena_len = s0.core.arena_len ∧
  s.core.tmp = s0.core.tmp ∧ s.core.tmp_len = s0.core.tmp_len ∧
  (∀ idx < rp.toNat, s.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?) ∧
  (s.scratch.scratch_buf[rp.toNat]?.getD 0#32).toNat = tl ∧
  k.toNat ≤ tl ∧
  (∀ q < k.toNat,
    s.scratch.scratch_buf[rp.toNat + 1 + q]? = some (s0.core.tmp[q]?.getD 0#32)) ∧
  (FullMem c s ⋆ R) m

public theorem bve_copy_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {rp : BitVec 64} {tl : Nat} {m' : Mem 64} {R : Mem 64 → Prop}
    (hdw : FullDenseInvW c F0 F_cur s0) (htmk : TmkZero s0)
    (hrp : rp.toNat < c.scratch_cap) (htl_lt32 : tl < 2 ^ 32)
    (hm' : (FullMem c
      { core := s0.core,
        scratch := { s0.scratch with
          scratch_buf := s0.scratch.scratch_buf.set rp.toNat (BitVec.ofNat 32 tl) } } ⋆ R) m') :
    BveCopyInv c F0 F_cur s0 rp tl 0#32
      { core := s0.core,
        scratch := { s0.scratch with
          scratch_buf := s0.scratch.scratch_buf.set rp.toNat (BitVec.ofNat 32 tl) } }
      m' R := by
  have hscr_len : (s0.scratch.scratch_buf.set rp.toNat (BitVec.ofNat 32 tl)).length =
      c.scratch_cap := by
    simp [hdw.1.scratch_ok.scratch_buf_len]
  have hsz : ((s0.scratch.scratch_buf.set rp.toNat (BitVec.ofNat 32 tl))[rp.toNat]?.getD
      0#32).toNat = tl := by
    rw [List.getElem?_set_self (by rw [hdw.1.scratch_ok.scratch_buf_len]; exact hrp),
      Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl_lt32]
  refine ⟨fullDenseInvW_with_scratch_buf hdw hscr_len, htmk, rfl, rfl, rfl, rfl, rfl, rfl,
    (fun idx hidx => by dsimp; rw [List.getElem?_set_ne (by omega)]),
    hsz, Nat.zero_le tl, (fun q hq => by simp at hq), hm'⟩

public theorem bve_copy_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {rp : BitVec 64} {tl : Nat} {k : BitVec 32}
    {m m' : Mem 64} {R : Mem 64 → Prop}
    (hinv : BveCopyInv c F0 F_cur s0 rp tl k s m R)
    (hk : k.toNat < tl) (hbd : rp.toNat + 1 + tl ≤ c.scratch_cap)
    (htmp_lt : k.toNat < s.core.tmp.length)
    (hm'' : (FullMem c
      { core := s.core,
        scratch := { s.scratch with
          scratch_buf := s.scratch.scratch_buf.set (rp.toNat + 1 + k.toNat)
            (s.core.tmp[k.toNat]) } } ⋆ R) m') :
    BveCopyInv c F0 F_cur s0 rp tl (k + 1#32)
      { core := s.core,
        scratch := { s.scratch with
          scratch_buf := s.scratch.scratch_buf.set (rp.toNat + 1 + k.toNat)
            (s.core.tmp[k.toNat]) } }
      m' R := by
  obtain ⟨hdw, htmk, hcv, hfl, har, hal, htmp, htl, hpre, hsz, _, hcopy, _⟩ := hinv
  have hsc32 := bve_scratch_cap_lt32 (c := c)
  have htl32 : tl < 2 ^ 32 := by omega
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
    simp [BitVec.toNat_add]; omega
  have hlen' : (s.scratch.scratch_buf.set (rp.toNat + 1 + k.toNat)
      (s.core.tmp[k.toNat])).length = c.scratch_cap := by
    simp [hdw.1.scratch_ok.scratch_buf_len]
  refine ⟨fullDenseInvW_with_scratch_buf hdw hlen', htmk,
    hcv, hfl, har, hal, htmp, htl,
    (fun idx hidx => by
      dsimp; rw [List.getElem?_set_ne (by omega)]; exact hpre idx hidx),
    (by dsimp; rw [List.getElem?_set_ne (by omega)]; exact hsz),
    (by rw [hk1]; omega),
    (fun q hq => by
      rw [hk1] at hq
      by_cases hqk : q = k.toNat
      · subst hqk; dsimp
        rw [List.getElem?_set_self (by rw [hdw.1.scratch_ok.scratch_buf_len]; omega)]
        congr 1
        have heq := congrArg (fun l => l[k.toNat]?.getD 0#32) htmp
        rw [← heq, List.getElem?_eq_getElem htmp_lt, Option.getD_some]
      · dsimp; rw [List.getElem?_set_ne (by omega)]
        exact hcopy q (by omega)),
    hm''⟩

public theorem bve_copy_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s0 s : FullState} {m8 : Bool} {v np nn : BitVec 32}
    {rp r_cnt w_est res_sz : BitVec 64} {tl : Nat} {k : BitVec 32}
    {m0 m : Mem 64} {R : Mem 64 → Prop}
    (hinv0 : BveVarLoopsInv c F0 F_cur s_start m8 v np nn rp r_cnt w_est true res_sz s0 m0 R)
    (hnp : np.toNat ≤ bveOccLim m8) (hnn : nn.toNat ≤ bveOccLim m8)
    (hc : BveCopyInv c F0 F_cur s0 rp tl k s m R)
    (hkeq : ¬ (k.toNat < tl)) (hrp_new : rp.toNat + 1 + tl ≤ c.scratch_cap)
    (htl_len : tl ≤ s0.core.tmp.length)
    (hbd : ∀ q < tl, (s0.core.tmp[q]?.getD 0#32).toNat < 2 * s0.core.cur_vars)
    (hnodup : (List.map (fun x => x.toNat / 2) (List.take tl s0.core.tmp)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map BitVec.toNat (List.take tl s0.core.tmp)))) :
    BveVarLoopsInv c F0 F_cur s_start m8 v np nn
      (rp + 1#64 + BitVec.ofNat 64 tl) (r_cnt + 1#64) w_est true res_sz s m R := by
  obtain ⟨_, _, hcv0, hfl0, hent_p0, hent_n0, hro0, _, hrb0, _⟩ := hinv0
  obtain ⟨hdw, htmk, hcv, hfl, har, hal, _, _, hpre, hsz, hk_le, hcopy, hm⟩ := hc
  have hk_eq : k.toNat = tl := by omega
  have hsc64 : c.scratch_cap < 2 ^ 64 := by
    have := bve_scratch_cap_lt32 (c := c); omega
  have hrp_sum : (rp + 1#64 + BitVec.ofNat 64 tl).toNat = rp.toNat + 1 + tl := by
    have h2 : (rp + 1#64).toNat = rp.toNat + 1 := by
      simp [BitVec.toNat_add]; omega
    simp [BitVec.toNat_add, h2]; omega
  have hrp1 : bveROff m8 ≤ (rp + 1#64 + BitVec.ofNat 64 tl).toNat := by omega
  have hrp2 : (rp + 1#64 + BitVec.ofNat 64 tl).toNat ≤ c.scratch_cap := by omega
  have hocc_roff : bveOccLim m8 + bveOccLim m8 ≤ bveROff m8 := by
    cases m8 <;> simp [bveOccLim, bveROff]
  have hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32) := by
    simpa using bve_entries_congr (s := s0) (s' := s) hcv har hal
      (off := 0) (fun i hi => by simpa using hpre i (by omega))
      (fun i hi => by simpa using hent_p0 i hi)
  have hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32) :=
    bve_entries_congr (s := s0) (s' := s) hcv har hal
      (off := bveOccLim m8) (fun j hj => hpre _ (by omega)) hent_n0
  have hrb : FullResBufOkW F_cur s (rp + 1#64 + BitVec.ofNat 64 tl).toNat (bveROff m8) := by
    rw [hrp_sum]
    exact bve_copy_post_resbuf_ok hcv htl_len hpre hsz
      (fun q hq => hcopy q (by omega)) hbd hnodup hent hrb0
  have hfl_le : s.core.fuel.toNat ≤ s_start.core.fuel.toNat := by
    rw [hfl]; exact hfl0
  exact ⟨hdw, htmk, hcv.trans hcv0, hfl_le, hp, hn, hrp1, hrp2, hrb, hm⟩

public theorem bve_defrag_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {rp : Nat} {m8 : Bool} {wv' ws' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hrb : FullResBufOkW F_cur s rp (bveROff m8)) (hrp : bveROff m8 ≤ rp)
    (hlok' : FullState.LengthsOk c
      { core := { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' }
        scratch := { s.scratch with wsort := wsort' } })
    (hlay' : WatchStackLayout
      { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' })
    (hwat' : ∀ l < 2 * s.core.cur_vars,
      let s' : FullState :=
        { core := { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' }
          scratch := { s.scratch with wsort := wsort' } }
      fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          ws'[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) :
    let s' : FullState :=
      { core := { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' }
        scratch := { s.scratch with wsort := wsort' } }
    FullDenseInvW c F0 F_cur s' ∧ TmkZero s' ∧
      FullResBufOkW F_cur s' rp (bveROff m8) := by
  intro s'
  exact ⟨bve_defrag_preserves_fullDenseInvW hdw hlok' hlay' hwat', htmk,
    bve_resBuf_congr hrb rfl hrp (fun _ _ _ => rfl)⟩

public theorem bve_weaken1_post {F_cur : List (List Nat)}
    {s s' : FullState} {rp off cnt : Nat} {m8 : Bool}
    (hrb : FullResBufOkW F_cur s rp (bveROff m8)) (hrp : bveROff m8 ≤ rp)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hscr : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hwk : ∀ i < cnt, FullBveWeakItemOk s.core (s.scratch.scratch_buf[off + i]?.getD 0#32)) :
    FullResBufOkW F_cur s' rp (bveROff m8) ∧
      ∀ i < cnt, FullBveWeakItemOk s'.core (s'.scratch.scratch_buf[off + i]?.getD 0#32) :=
  ⟨bve_resBuf_congr hrb hcv hrp (fun _ _ _ => by rw [hscr]),
   bve_weak_items_congr hcv hrefs hscr hwk⟩

public theorem bve_commit_ret_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s0 s1 : FullState} {r : BitVec 64}
    (hdw : FullDenseInvW c F0 F_cur s1) (htmk : TmkZero s1)
    (hcv0 : s0.core.cur_vars = s_start.core.cur_vars)
    (hcv1 : s1.core.cur_vars = s0.core.cur_vars)
    (hfl0 : s0.core.fuel.toNat ≤ s_start.core.fuel.toNat)
    (hfl1 : s1.core.fuel = s0.core.fuel)
    (hr : r = 1#64 ∨ r = 2#64 ∨ r = 20#64) (hun : r = 20#64 → F0.Unsat) :
    FullDenseInv c F0 s1 ∧ TmkZero s1 ∧
      s_start.core.cur_vars ≤ s1.core.cur_vars ∧
      s1.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) := by
  have hfle : s1.core.fuel.toNat ≤ s_start.core.fuel.toNat := by rw [hfl1]; exact hfl0
  exact ⟨hdw.toDense, htmk, by omega, hfle, hr, hun⟩

public theorem bve_flush_ret_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s0 s1 s2 : FullState} {ok : Bool}
    (hdw : FullDenseInvW c F0 F_cur s2) (htmk : TmkZero s2)
    (hcv0 : s0.core.cur_vars = s_start.core.cur_vars)
    (hcv1 : s1.core.cur_vars = s0.core.cur_vars)
    (hcv2 : s2.core.cur_vars = s1.core.cur_vars)
    (hfl0 : s0.core.fuel.toNat ≤ s_start.core.fuel.toNat)
    (hfl1 : s1.core.fuel = s0.core.fuel)
    (hfl2 : s2.core.fuel = s1.core.fuel)
    (hun : ok = false → F0.Unsat) :
    let r := if ok then 1#64 else 20#64
    FullDenseInv c F0 s2 ∧ TmkZero s2 ∧
      s_start.core.cur_vars ≤ s2.core.cur_vars ∧
      s2.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) := by
  have hfle : s2.core.fuel.toNat ≤ s_start.core.fuel.toNat := by
    rw [hfl2, hfl1]; exact hfl0
  cases ok <;> simp [hun]
  · exact ⟨hdw.toDense, htmk, by omega, hfle⟩
  · exact ⟨hdw.toDense, htmk, by omega, hfle⟩

end LeanQbe.T.Examples.Kissat.Proof.Eliminate
