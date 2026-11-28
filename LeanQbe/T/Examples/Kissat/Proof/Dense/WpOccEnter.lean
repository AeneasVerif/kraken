/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dense.Helpers

/-!
# Kissat Dense Occurrence Counter & Enter-Dense WP Proofs (`Proof.Dense.WpOccEnter`)

Parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` `@[expose]` on
theorems/lemmas/sections, `0` legacy imports, `<= 100` cols) for:
1. `full_dense_occ_cnt_fid` (`Spec.fullDenseOccCntSpec`)
2. `full_enter_dense_ex_fid` (`Spec.fullEnterDenseExM6Spec`)
3. `full_enter_dense` (`Spec.fullEnterDenseM6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dense

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Dense
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local macro "dr_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_dense_occ_cnt_fid` -/

/-- `full_dense_occ_cnt_fid` WP proof (`Spec.fullDenseOccCntSpec`). -/
theorem full_dense_occ_cnt_fid_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullDenseOccCntSpec a m Q X →
      Func.wp Γ full_dense_occ_cnt_fid_body a m Q X := by
  rintro ⟨h, lit, cap, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hlit, hm, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr
  have h2l_lt : 2 * lit.toNat < s.core.wvec.length := by rw [hwv_len]; omega
  have h2l1_lt : 2 * lit.toNat + 1 < s.core.wvec.length := by rw [hwv_len]; omega
  have h2l_idx : ((BitVec.setWidth 64 lit) <<< (1 : Nat)).toNat = 2 * lit.toNat := by bv_omega
  have h2l1_idx : (((BitVec.setWidth 64 lit) <<< (1 : Nat)) + 1#64).toNat =
      2 * lit.toNat + 1 := by bv_omega
  have hbd_lit := hlay.bounds lit.toNat hlit
  have hwo_eq : fullWatchOffCore s.core lit.toNat =
      (s.core.wvec[2 * lit.toNat]'h2l_lt).toNat := by
    unfold fullWatchOffCore; rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
  have hwsz_eq : fullWatchSizeCore s.core lit.toNat =
      (s.core.wvec[2 * lit.toNat + 1]'h2l1_lt).toNat := by
    unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
  have hwl_le : s.core.wlen ≤ s.core.wstk.length := by rw [hws_len]; exact hlen.core_ok.wlen_le
  unfold Func.wp full_dense_occ_cnt_fid_body
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps_nogrp; exact hQ _
  · let off64 := BitVec.setWidth 64 (s.core.wvec[2 * lit.toNat]'h2l_lt)
    let sz64 := BitVec.setWidth 64 (s.core.wvec[2 * lit.toNat + 1]'h2l1_lt)
    let end64 := off64 + sz64
    have hoff64 : off64.toNat = fullWatchOffCore s.core lit.toNat := by
      dsimp only [off64]; rw [hwo_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hsz64 : sz64.toNat = fullWatchSizeCore s.core lit.toNat := by
      dsimp only [sz64]; rw [hwsz_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hend64 : end64.toNat = off64.toNat + sz64.toNat := by
      dsimp only [end64]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hoff64_c0 :
        BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(by
          rw [h2l_idx]; exact h2l_lt)) = off64 :=
      congrArg (BitVec.setWidth 64)
        (dense_getElem_congr h2l_idx (by rw [h2l_idx]; exact h2l_lt) h2l_lt)
    c0_hsteps_nogrp
    refine wp_loop_group (ts := [i64, i64])
      (fun rem (p, cnt, ()) mp => mp = m ∧ off64.toNat ≤ p.toNat ∧
        rem = end64.toNat - p.toNat) ?_
      (fun Lp hLp => by
        c0_hsteps!
        rw [hoff64_c0]
        exact hLp (end64.toNat - off64.toNat) (off64, 0#64, ()) m ⟨rfl, Nat.le_refl _, rfl⟩)
    rintro Lp rem ⟨p, cnt, ⟨⟩⟩ mp hLp ⟨hm_eq, hp_ge, rfl⟩
    subst hm_eq
    c0_hsplit
    · have hp_lt_end : p.toNat < end64.toNat := by
        have hlt_c := hc
        have h2l_m : (2 * lit.toNat) % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
        have h2l1_m : (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 :=
          Nat.mod_eq_of_lt (by omega)
        have h2l_eq := congrArg BitVec.toNat
          (dense_getElem_congr h2l_m (by rw [h2l_m]; exact h2l_lt) h2l_lt)
        have h2l1_eq := congrArg BitVec.toNat
          (dense_getElem_congr h2l1_m (by rw [h2l1_m]; exact h2l1_lt) h2l1_lt)
        simp only [show (1 : BitVec 64).toNat = 1 from rfl, h2l_eq, h2l1_eq] at hlt_c
        rw [Nat.mod_eq_of_lt (by
          have : (s.core.wvec[2 * lit.toNat]'h2l_lt).toNat = off64.toNat := by
            dsimp only [off64]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have : (s.core.wvec[2 * lit.toNat + 1]'h2l1_lt).toNat = sz64.toNat := by
            dsimp only [sz64]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          omega)] at hlt_c
        have h_off : (s.core.wvec[2 * lit.toNat]'h2l_lt).toNat = off64.toNat := by
          dsimp only [off64]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have h_sz : (s.core.wvec[2 * lit.toNat + 1]'h2l1_lt).toNat = sz64.toNat := by
          dsimp only [sz64]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        omega
      have hp_wstk : p.toNat < s.core.wstk.length := by omega
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
        (fun p' mp' => mp' = mp ∧ p.toNat < p'.toNat)
        (fun _ p' mp' ⟨hmp'_eq, hp'_gt⟩ => by
          subst hmp'_eq
          c0_hsteps_nogrp
          c0_hsplit
          · c0_hsteps!; exact hQ _
          · have hp'_le_dec : end64.toNat - p'.toNat < end64.toNat - p.toNat := by omega
            c0_hsteps!
            exact hLp (end64.toNat - p'.toNat) (p', cnt + 1#64, ()) mp' hp'_le_dec
              ⟨rfl, by omega, rfl⟩)
        (fun Jp hJp => by
          c0_hsplit
          · have hp1 : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
            c0_hsteps!; exact hJp (p + 1#64) mp ⟨rfl, by omega⟩
          · have hp2 : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
            c0_hsteps!; exact hJp (p + 2#64) mp ⟨rfl, by omega⟩)
    · c0_hsteps!; exact hQ _

/-! ## 2. `full_enter_dense_ex_fid` Local Invariants & Watch Helpers -/

private def M6EnterOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s st : FullState) : Prop :=
  st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧ FullLitMarksClear c st ∧
  FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
  st.core.cur_level = 0 ∧ st.core.cur_vars = s.core.cur_vars ∧
  st.core.fuel.toNat ≤ s.core.fuel.toNat

private theorem denseSlice_to_watch {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) :
    WatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hn hl he _ ih => exact .bin hp hf hn hl he ih
  | occ hp hp1 hf _ hl hr _ ih => exact .large hp hp1 hf hl hr ih

private theorem denseWatchesInv_to_watch {F_cur : List (List Nat)} {k : FullCoreState}
    (hd : DenseWatchesInv F_cur k) : WatchesInv F_cur k :=
  ⟨hd.layout, fun l hl => denseSlice_to_watch (hd.slices l hl)⟩

private theorem denseSlice_relocate_append_occ {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat} {w0 cref : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hrefs : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hcref : k'.wstk[p' + rem + 1]? = some cref)
    (hfl : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : cref.toNat < 0x80000000) (hr : cref.toNat ∈ fullArenaClauseRefsCore k') :
    DenseWatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty =>
    exact .occ (by simpa using hw0) (by simpa using hcref) hfl hsz hlt hr .empty
  | @bin p rem w hp hf hn hltb hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) hent
      (ih (p' := p' + 1)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcref))
  | @occ p rem w c hp hc hf hs hl hcr _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hwstk 1 (by omega)).trans hc)
      hf hs hl (hrefs c.toNat hcr)
      (ih (p' := p' + 2)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcref))

private theorem enter_fullWitnessInv_unsat_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (huns : F0.Unsat) :
    FullWitnessInv c F0 ([] :: F_cur) { k with inconsistent := 1#64 } := by
  have hnil_uns : (cnfOfClauses ([] :: F_cur)).Unsat := by
    rw [CNF.unsat_iff_not_sat]; intro α hsat
    rw [cnf_sat_cnfOfClauses_iff] at hsat
    have h0 := (clause_sat_cnfClause_iff α []).mp (hsat [] List.mem_cons_self)
    rcases h0 with ⟨_, hmem, _⟩; exact nomatch hmem
  have hent : (cnfOfClauses ([] :: F_cur)).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; intro α hsat
    exfalso; exact (CNF.unsat_iff_not_sat.mp hnil_uns) α hsat
  exact
    { ext_sound := ⟨fun cl hcl => by
        rcases List.mem_cons.mp hcl with rfl | hmem
        · exact fun _ hx => nomatch hx
        · exact hw.ext_sound.1 cl hmem, fun _ => huns⟩
      inconsistent_sound := fun _ => hnil_uns
      arena :=
        { len_ok := hw.arena.len_ok
          refs_wf := hw.arena.refs_wf
          shrk_term := hw.arena.shrk_term
          lits_lt := hw.arena.lits_lt
          entails := fun r hr hng => CNF.entails_clause_trans hent (hw.arena.entails r hr hng) }
      watches := (hw.watches.mono hent).with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
      cur_level_le := hw.cur_level_le
      trail_lits_lt := hw.trail_lits_lt
      trail_vars_nodup := hw.trail_vars_nodup
      vals_domain := hw.vals_domain
      vals_true_iff := hw.vals_true_iff
      vals_false_iff := hw.vals_false_iff
      lvl_le := hw.lvl_le
      dec_earliest := hw.dec_earliest
      levels_inhabited := hw.levels_inhabited
      level0_sound := fun i hi hl0 => CNF.entails_clause_trans hent (hw.level0_sound i hi hl0)
      trail_pos_inv := hw.trail_pos_inv
      level0_rsn_none := hw.level0_rsn_none
      frame_trail_lt := hw.frame_trail_lt
      frame_trail_mono := hw.frame_trail_mono
      frame_trail_before_lt := hw.frame_trail_before_lt
      frame_dec_lt := hw.frame_dec_lt
      reason_inv := fun idx hidx hrs => by
        have h := hw.reason_inv idx hidx hrs
        dsimp only at h ⊢
        split at h <;> split
        · exact ⟨h.1, CNF.entails_clause_trans hent h.2.1, h.2.2⟩
        · rename_i h1 h2; exact absurd h1 h2
        · rename_i h1 h2; exact absurd h2 h1
        · exact h
      reason_lit_mem := hw.reason_lit_mem }

private theorem enter_markGarb_denseOk {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sP : FullState}
    (hokP : M6EnterOk c F0 F_cur s sP) (hdP : DenseWatchesInv F_cur sP.core)
    (hdmP : sP.core.dense_mode = 0#64) {p : Nat} (hp_in : p ∈ fullArenaClauseRefsCore sP.core)
    (ag' ni' : BitVec 64) :
    let sG : FullState :=
      { sP with core :=
        { sP.core with
          arena := sP.core.arena.set p (fullArenaHdrCore sP.core p ||| 0x00080000#32)
          arena_garbage := ag', num_irred := ni' } }
    M6EnterOk c F0 F_cur s sG ∧ DenseWatchesInv F_cur sG.core := by
  intro sG
  have hlenP := hokP.1.core_ok
  have har_len : p < sP.core.arena.length := by
    have hwf := hokP.2.1.arena.refs_wf p hp_in
    have := hlenP.arena_len_le; have := hlenP.arena_len_arr; omega
  obtain ⟨hrefsG, hinvArG⟩ := FullArenaClausesInv.markGarb hokP.2.1.arena hlenP hp_in ag'
  have hrefs_eq : fullArenaClauseRefs sG = fullArenaClauseRefs sP := by
    change fullArenaClauseRefsCore sG.core = fullArenaClauseRefsCore sP.core
    unfold fullArenaClauseRefsCore at hrefsG ⊢; exact hrefsG
  have hlenG : sG.LengthsOk c :=
    ⟨{ hlenP with arena_len_arr := by simp [sG, hlenP.arena_len_arr] }, hokP.1.scratch_ok⟩
  have hdG : DenseWatchesInv F_cur sG.core :=
    ⟨hdP.layout.with_wstk rfl rfl rfl rfl, fun l hl => by
      have h' := DenseWatchSliceOk.mono (k := sP.core) (k' := sG.core)
        (by rw [CNF.entails_def]; exact fun _ q => q) (Nat.le_refl _)
        (fun r hr => hrefsG ▸ hr) (fun _ _ _ => rfl) (hdP.slices l hl)
      simpa only [sG, fullWatchOffCore, fullWatchSizeCore] using h'⟩
  have hwG : FullWitnessInv c F0 F_cur sG.core :=
    { hokP.2.1 with
      arena := { hinvArG with len_ok := hinvArG.len_ok }
      watches := by rw [ModeWatchesInv, ite_eq_left hdmP]; exact denseWatchesInv_to_watch hdG
      reason_inv := fun idx hidx hrsn => by
        exfalso; apply hrsn; exact hokP.2.1.level0_rsn_none idx hidx (by
          have := hokP.2.1.lvl_le idx hidx; have := hokP.2.2.2.2.2.1; omega)
      reason_lit_mem := fun idx hidx hrsn _ => by
        exfalso; apply hrsn; exact hokP.2.1.level0_rsn_none idx hidx (by
          have := hokP.2.1.lvl_le idx hidx; have := hokP.2.2.2.2.2.1; omega) }
  have hsz_eq : ∀ r ∈ fullArenaClauseRefs sP,
      fullArenaClauseSize sG r = fullArenaClauseSize sP r := fun r hr => by
    have hwf_p := hokP.2.1.arena.refs_wf p hp_in
    have hwf_r := hokP.2.1.arena.refs_wf r hr
    unfold fullArenaClauseSize fullArenaClauseSizeCore; dsimp only [sG]
    by_cases heq : r = p
    · subst heq; rw [List.getElem?_set_ne (by omega)]
    · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
      · have := hokP.2.1.arena.disjoint hr hp_in hlt; rw [List.getElem?_set_ne (by omega)]
      · have := hokP.2.1.arena.disjoint hp_in hr hgt; rw [List.getElem?_set_ne (by omega)]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefs sP,
      fullArenaClauseGarb sG r = (if r = p then true else fullArenaClauseGarb sP r) := by
    intro r hr; unfold fullArenaClauseGarb fullArenaClauseGarbCore
    by_cases heq : r = p
    · subst heq; simp only [↓reduceIte]
      have hset : sG.core.arena[r]? = some (fullArenaHdrCore sP.core r ||| 0x00080000#32) :=
        List.getElem?_set_self har_len
      change (sG.core.arena[r]?.getD 0#32 &&& 0x00080000#32 != 0#32) = true
      simp [hset, BitVec.and_or_distrib_right]
    · simp only [heq, ↓reduceIte]
      have hhdr : fullArenaHdrCore sG.core r = fullArenaHdrCore sP.core r := by
        unfold fullArenaHdrCore; dsimp only [sG]; rw [List.getElem?_set_ne (Ne.symm heq)]
      change (fullArenaHdrCore sG.core r &&& 0x00080000#32 != 0#32) =
        (fullArenaHdrCore sP.core r &&& 0x00080000#32 != 0#32)
      rw [hhdr]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefs sP,
      fullArenaClauseLits sG r = fullArenaClauseLits sP r := fun r hr => by
    have hwf_p := hokP.2.1.arena.refs_wf p hp_in
    have hwf_r := hokP.2.1.arena.refs_wf r hr
    have hszr := hsz_eq r hr
    refine (fullArenaClauseLitsCore_eq_of_hold ?_ ?_ hszr.symm ?_).symm
    · change r + 3 + fullArenaClauseSize sG r ≤ sG.core.arena.length
      rw [hszr, hlenG.1.arena_len_arr]
      change r + 3 + fullArenaClauseSizeCore sP.core r ≤ c.arena_cap
      have := hwf_r.2.2.1; have := hwf_r.2.2.2.1; have := hlenP.arena_len_le; omega
    · change r + 3 + fullArenaClauseSize sG r ≤ sP.core.arena.length
      rw [hszr]; change r + 3 + fullArenaClauseSizeCore sP.core r ≤ sP.core.arena.length
      rw [hlenP.arena_len_arr]
      have := hwf_r.2.2.1; have := hwf_r.2.2.2.1; have := hlenP.arena_len_le; omega
    · intro j hj
      change j < fullArenaClauseSize sG r at hj
      rw [hszr] at hj; change j < fullArenaClauseSizeCore sP.core r at hj
      by_cases heq : r = p
      · subst heq; dsimp only [sG]; rw [List.getElem?_set_ne (by omega)]
      · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
        · have := hokP.2.1.arena.disjoint hr hp_in hlt
          dsimp only [sG]; rw [List.getElem?_set_ne (by omega)]
        · have := hokP.2.1.arena.disjoint hp_in hr hgt
          dsimp only [sG]; rw [List.getElem?_set_ne (by omega)]
  have hndG : FullArenaVarsNodup sG := fun r hr hng => by
    have hr0 : r ∈ fullArenaClauseRefs sP := hrefs_eq ▸ hr
    rw [hgarb_eq r hr0] at hng; split at hng
    · contradiction
    · rw [hlits_eq r hr0]; exact hokP.2.2.2.1 r hr0 hng
  have hllG : FullLastLearnedWf sG := fun i hi => by
    change sG.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sG.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sG
    rw [hrefs_eq]; exact hokP.2.2.2.2.1.1 i hi
  exact ⟨⟨hlenG, hwG, hokP.2.2.1, hndG, ⟨hllG, hokP.2.2.2.2.1.2⟩,
    hokP.2.2.2.2.2.1, hokP.2.2.2.2.2.2.1, hokP.2.2.2.2.2.2.2⟩, hdG⟩

private theorem denseSlice_relocate {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hrefs : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : DenseWatchSliceOk F_cur k lit p rem) :
    DenseWatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w hp hf hn hltb hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) hent
      (ih fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
  | @occ p rem w c hp hc hf hs hl hcr _ ih =>
    exact .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hwstk 1 (by omega)).trans hc)
      hf hs hl (hrefs c.toNat hcr)
      (ih fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))

private theorem enter_watch_push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sK : FullState} {lit w0 w1 : BitVec 32} {ok : Bool}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hokK : M6EnterOk c F0 F_cur s sK) (hdK : DenseWatchesInv F_cur sK.core)
    (hdmK : sK.core.dense_mode = 0#64)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefsCore sK.core) :
    let sK' : FullState :=
      { sK with
        core := { sK.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { sK.scratch with wsort := wsort' } }
    sK'.LengthsOk c → WatchStackLayout sK'.core →
    (∀ l < 2 * sK.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize sK' l = fullWatchSize sK l ∧
      ∀ i < fullWatchSize sK l,
        sK'.core.wstk[fullWatchOff sK' l + i]? = sK.core.wstk[fullWatchOff sK l + i]?) →
    (ok = true →
      lit.toNat < 2 * sK.core.cur_vars ∧
      fullWatchSize sK' lit.toNat = fullWatchSize sK lit.toNat + 2 ∧
      (∀ i < fullWatchSize sK lit.toNat,
        sK'.core.wstk[fullWatchOff sK' lit.toNat + i]? =
          sK.core.wstk[fullWatchOff sK lit.toNat + i]?) ∧
      sK'.core.wstk[fullWatchOff sK' lit.toNat + fullWatchSize sK lit.toNat]? = some w0 ∧
      sK'.core.wstk[fullWatchOff sK' lit.toNat + fullWatchSize sK lit.toNat + 1]? = some w1) →
    (ok = false → lit.toNat < 2 * sK.core.cur_vars →
      fullWatchSize sK' lit.toNat = fullWatchSize sK lit.toNat ∧
      ∀ i < fullWatchSize sK lit.toNat,
        sK'.core.wstk[fullWatchOff sK' lit.toNat + i]? =
          sK.core.wstk[fullWatchOff sK lit.toNat + i]?) →
    M6EnterOk c F0 F_cur s sK' ∧ DenseWatchesInv F_cur sK'.core := by
  intro sK' hlen' hlay' hoth hokT hokF
  have hslices : ∀ l < 2 * sK'.core.cur_vars,
      DenseWatchSliceOk F_cur sK'.core l (fullWatchOffCore sK'.core l)
        (fullWatchSizeCore sK'.core l) := by
    intro l hl
    by_cases hll : l = lit.toNat
    · subst hll
      cases ok with
      | true =>
        obtain ⟨_, hsz_eq, hpre, hw0, hw1⟩ := hokT rfl
        have h' := denseSlice_relocate_append_occ (k := sK.core) (k' := sK'.core)
          (Nat.le_refl _) (fun _ r => r) hpre (hdK.slices lit.toNat hl) hw0 hw1 hflag hsz hlt
          href
        exact denseSlice_congr rfl
          (by simpa [fullWatchSizeCore, fullWatchSize] using hsz_eq.symm) h'
      | false =>
        obtain ⟨hsz_eq, hpre⟩ := hokF rfl hl
        have h' := denseSlice_relocate (k := sK.core) (k' := sK'.core)
          (Nat.le_refl _) (fun _ r => r) hpre (hdK.slices lit.toNat hl)
        exact denseSlice_congr rfl
          (by simpa [fullWatchSizeCore, fullWatchSize] using hsz_eq.symm) h'
    · obtain ⟨hsz_eq, hpre⟩ := hoth l hl hll
      have h' := denseSlice_relocate (k := sK.core) (k' := sK'.core)
        (Nat.le_refl _) (fun _ r => r) hpre (hdK.slices l hl)
      exact denseSlice_congr rfl
        (by simpa [fullWatchSizeCore, fullWatchSize] using hsz_eq.symm) h'
  have hd' : DenseWatchesInv F_cur sK'.core := ⟨hlay', hslices⟩
  have hw' : FullWitnessInv c F0 F_cur sK'.core :=
    { hokK.2.1 with
      arena := { hokK.2.1.arena with len_ok := hokK.2.1.arena.len_ok }
      watches := by rw [ModeWatchesInv, ite_eq_left hdmK]; exact denseWatchesInv_to_watch hd' }
  exact ⟨⟨hlen', hw', hokK.2.2.1, hokK.2.2.2.1, hokK.2.2.2.2.1,
    hokK.2.2.2.2.2.1, hokK.2.2.2.2.2.2.1, hokK.2.2.2.2.2.2.2⟩, hd'⟩

/-! ## 3. `full_enter_dense_ex_fid` `had_unfl` & `connect_large` Sub-Proofs -/

private theorem enter_had_unfl_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext1 : List (BitVec 64)} {s s1 : FullState}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {Junfl : Cont []} {m1 : Mem 64}
    (hSweep : Γ.Has "full_arena_sweep" Proof.Spec.fullArenaSweepSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hFlush : Γ.Has "full_flush_trail" PropSearch.Spec.flushTrailM6Spec)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hsp1 : FullSparseInv c F0 s1) (hcl1 : s1.core.cur_level = 0)
    (hcv1 : s1.core.cur_vars = s.core.cur_vars)
    (hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm1 : (FullM6HdrMem c ext1 s1 ⋆ R) m1)
    (hJunfl : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → (M6HdrExtInitOk ext1 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext1 ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (FullM6HdrMem c ext' s' ⋆ R) m' → Junfl () m')
    (hret_f : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → (M6HdrExtInitOk ext1 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext1 ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (false, ()) m') :
    Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ()) (fun (sr_d, ()) =>
      Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var sr_d, Arg.imm 2, ())) fun (b2, ()) =>
      Expr.jnz (Arg.var b2)
        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) fun (pi, ()) =>
          Expr.store (t := i64) (Arg.imm 1) (Arg.var pi) (Expr.ret (Arg.imm false, ())))
        (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
          (fun (pr, ()) =>
          Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var pr, Arg.imm 1, ())) fun (bp, ()) =>
          Expr.jnz (Arg.var bp)
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) fun (pi, ()) =>
              Expr.store (t := i64) (Arg.imm 1) (Arg.var pi) (Expr.ret (Arg.imm false, ())))
            (Expr.call (as := [i64]) (bs := [i64]) "full_flush_trail" (Arg.var c.hdr, ())
              (fun (fr2, ()) =>
              Expr.let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var fr2, Arg.imm 1, ()))
                fun (bf2, ()) =>
              Expr.jnz (Arg.var bf2) (Expr.ret (Arg.imm false, ()))
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun (pu, ()) =>
                  Expr.store (t := i64) (Arg.imm 0) (Arg.var pu) (Expr.jump Junfl ())))))))
    |> fun e => wp Γ Q X e m1 := by
  dsimp only
  let Rext1 : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R
  have hm1_f := fullM6HdrMem_focus_full hm1
  obtain ⟨F_cur1, hw1⟩ := hsp1.1.witness
  dr_call hSweep
  refine ⟨c, F0, F_cur1, s1, Rext1, rfl, hsp1.1.lengths, hw1, hsp1.2.2.1, hsp1.2.2.2.2,
    fun hpos => by omega, hm1_f, ?_⟩
  intro sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
    fred' ni' nr' nb' oom' sc' mA sA hlenA _ hextA _ hllA hwA hndA _ _ _ hsr2 _ hmA
  have hspA : FullSparseInv c F0 sA :=
    ⟨⟨hlenA, ⟨F_cur1, hwA⟩⟩, hsp1.2.1, hndA, ⟨hllA, hextA ▸ hsp1.2.2.2.1.2⟩, hsp1.2.2.2.2⟩
  c0_hsplit
  · have hsr2_eq : sr = 2#64 := hc
    have huns := (hsr2 hsr2_eq).2
    let sAi : FullState := { sA with core := { sA.core with inconsistent := 1#64 } }
    have hlenAi : sAi.LengthsOk c :=
      ⟨{ hlenA.core_ok with vals_len := hlenA.core_ok.vals_len }, hlenA.scratch_ok⟩
    have hwAi := enter_fullWitnessInv_unsat_inconsistent hwA huns
    have hspAi : FullSparseInv c F0 sAi :=
      ⟨⟨hlenAi, ⟨[] :: F_cur1, hwAi⟩⟩, hsp1.2.1, hndA, hspA.2.2.2.1, hsp1.2.2.2.2⟩
    c0_hsteps_nogrp
    exact hret_f ext1 sAi _ hext1 (fun h => ⟨h, M6ExtW2bPres.refl ext1⟩) hspAi hcl1 hcv1 hfu1
      (fullM6HdrMem_unfocus_full (by assumption))
  · c0_hsteps_nogrp; dr_call hProp
    refine ⟨c, F0, F_cur1, ext1, sA, R, rfl, hcfg, hext1, hlenA, hwA, hsp1.2.2.2.2,
      fullM6HdrMem_unfocus_full hmA, ?_⟩
    intro pr extB valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB arenaB wstkB wlenB
      wuB fuelB ctypeB crefB c0B c1B oomB scB mB sB
      hextB_ok hextB_w2b hlenB hwB _ _ harenaB hprB _ _ _ _ hfuB _ _ hpr1 _ _ hmB
    have hndB : FullArenaVarsNodup sB := fun r hr hng => by
      dsimp only [FullArenaVarsNodup, fullArenaClauseRefs] at hr ⊢
      rw [harenaB.2.1] at hr
      rw [show fullArenaClauseGarb sB r = fullArenaClauseGarbCore sB.core r from rfl,
        (harenaB.2.2 r hr).2.1] at hng
      rw [show fullArenaClauseLits sB r = fullArenaClauseLitsCore sB.core r from rfl]
      exact ((harenaB.2.2 r hr).2.2.map (fun x => x / 2)).nodup_iff.mpr (hndA r hr hng)
    have hllB : FullLastLearnedWf sB := fun i hi => by
      change scB.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
        (scB.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefsCore sB.core
      rw [hprB.1.1, harenaB.2.1]; exact hllA i hi
    have hfuB' : sB.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuB hfu1
    have hspB : FullSparseInv c F0 sB :=
      ⟨⟨hlenB, ⟨F_cur1, hwB⟩⟩, hsp1.2.1, hndB, ⟨hllB, hprB.1.2 ▸ hspA.2.2.2.1.2⟩, hsp1.2.2.2.2⟩
    have hmB_f := fullM6HdrMem_focus_full hmB
    c0_hsteps_nogrp
    c0_hsplit
    · have hpr1_eq : pr = 1#64 := hc
      have hconfl := (hpr1 hpr1_eq).2.2
      have huns : F0.Unsat := level0_unsat_of_conflict_okW hwB hcl1 hconfl
      let sBi : FullState := { sB with core := { sB.core with inconsistent := 1#64 } }
      have hlenBi : sBi.LengthsOk c :=
        ⟨{ hlenB.core_ok with vals_len := hlenB.core_ok.vals_len }, hlenB.scratch_ok⟩
      have hwBi := enter_fullWitnessInv_unsat_inconsistent hwB huns
      have hspBi : FullSparseInv c F0 sBi :=
        ⟨⟨hlenBi, ⟨[] :: F_cur1, hwBi⟩⟩, hsp1.2.1, hndB, hspB.2.2.2.1, hsp1.2.2.2.2⟩
      c0_hsteps_nogrp
      exact hret_f extB sBi _ hextB_ok hextB_w2b hspBi hcl1 hcv1 hfuB'
        (fullM6HdrMem_unfocus_full (by assumption))
    · c0_hsteps_nogrp; dr_call hFlush
      refine ⟨c, F0, extB, sB, R, rfl, FullM6HdrInv.mk_inv hcfg hextB_ok hspB, hmB, ?_⟩
      intro fr2 extC sC mC hextC_ok hextC_w2b hinvC _ _ _ _ _ _ hcvC _ hfuC hclC_fn _ _ _ hmC
      have hext1C := dense_m6_extInit_trans hextB_w2b hextC_w2b
      have hspC := hinvC.sparse
      have hclC : sC.core.cur_level = 0 := hclC_fn hcl1
      have hfuC' : sC.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuC hfuB'
      have hcvC' : sC.core.cur_vars = s.core.cur_vars := hcvC.trans hcv1
      c0_hsplit
      · c0_hsteps_nogrp
        exact hret_f extC sC mC hextC_ok hext1C hspC hclC hcvC' hfuC' hmC
      · have hmC_f := fullM6HdrMem_focus_full hmC
        obtain ⟨F_curC, hcwC⟩ := hspC.1.witness
        let sCu : FullState := { sC with core := { sC.core with unflushed := 0#64 } }
        have hlenCu : sCu.LengthsOk c :=
          ⟨{ hspC.1.lengths.core_ok with vals_len := hspC.1.lengths.core_ok.vals_len },
            hspC.1.lengths.scratch_ok⟩
        have hwCu := fullWitnessInv_with_unflushed hcwC 0#64
        have hspCu : FullSparseInv c F0 sCu :=
          ⟨⟨hlenCu, ⟨F_curC, hwCu⟩⟩, hspC.2.1, hspC.2.2.1, hspC.2.2.2.1, hspC.2.2.2.2⟩
        c0_hsteps_nogrp
        exact hJunfl extC sCu _ hextC_ok hext1C hspCu hclC hcvC' hfuC'
          (fullM6HdrMem_unfocus_full (by assumption))

private def enterEDflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (enterEDflt a, enterEDflt b)
private def enterEDfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (enterEDflt t, enterEDfltT r)
private def enterEDrop {rs} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | n + 1, .let_ (ts := ts) _ k => enterEDrop n (k (enterEDfltT ts))
  | n + 1, .load (.bits 32) _ k => enterEDrop n (k 0#32)
  | n + 1, .load (.bits 64) _ k => enterEDrop n (k 0#64)
  | n + 1, .store _ _ k => enterEDrop n k
  | _, e => e
private def enterEGrp0 {rs} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) _ k => k (J, ())
  | _ => .hlt
private def enterEGrp0Body {rs} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ =>
      match bs (J, ()) with | .cons b _ => b ()
  | _ => .hlt
private def enterEJnzF {rs} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt
private def enterECall {rs} : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := bs) _ _ k => k (enterEDfltT bs) | _ => .hlt

private def enterConnectE (h : BitVec 64) (cl : Bool) (Jdone : Cont []) :
    Expr Val Cont [.bool] :=
  let dJ : Cont [] := fun _ _ => True
  let e1 := enterEDrop 20 (full_enter_dense_ex_fid_body Val Cont (h, cl, ()))
  let e2 := enterEDrop 20 (enterEGrp0Body dJ e1)
  let e3 := enterEDrop 20 (enterEJnzF e2)
  let e4 := enterEDrop 20 (enterEJnzF e3)
  let e5 := enterEDrop 20 (enterECall e4)
  let e6 := enterEDrop 20 (enterEJnzF e5)
  let e7 := enterEDrop 20 (enterEGrp0Body dJ e6)
  let e8 := enterEDrop 20 (enterECall e7)
  enterEGrp0 Jdone e8

private theorem enter_connect_arena_next_eq {c : FullCfg} {F0 : CNF Nat}
    {F_cur3 : List (List Nat)} {s s4 sP sN : FullState} {p : BitVec 64}
    (hc_ar : c.arena_cap < 2 ^ 30)
    (hokP : M6EnterOk c F0 F_cur3 s sP) (hokN : M6EnterOk c F0 F_cur3 s sN)
    (halenP : sP.core.arena_len = s4.core.arena_len)
    (halenN : sN.core.arena_len = s4.core.arena_len)
    (hrefsN : fullArenaClauseRefs sN = fullArenaClauseRefs sP)
    (hp_in : p.toNat ∈ fullArenaClauseRefs sP)
    (hp_trunc : (p.setWidth 32).toNat = p.toNat) :
    ((BitVec.ofNat 32 (fullArenaNextOff sN.core.arena sN.core.arena_len
        (p.setWidth 32).toNat)).setWidth 64).toNat =
      fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat := by
  have hp_wf := hokP.2.1.arena.refs_wf p.toNat hp_in
  have halP := hokP.1.core_ok.arena_len_le
  have hnb := fullArenaNextOff_bounds (ar := sP.core.arena) (alen := sP.core.arena_len)
    (cref := p.toNat) hp_wf.1
  have hnxt_mem := fullArenaClauseRefs_next_mem hokP.2.1.arena hp_in
  have har_n : fullArenaNextOff sN.core.arena sN.core.arena_len p.toNat =
      fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat :=
    Classical.byContradiction fun hne => by
      have hnbN := fullArenaNextOff_bounds (ar := sN.core.arena) (alen := sN.core.arena_len)
        (cref := p.toNat) (by omega)
      have hp_inN : p.toNat ∈ fullArenaClauseRefsCore sN.core := by
        change p.toNat ∈ fullArenaClauseRefs sN; rw [hrefsN]; exact hp_in
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have hnxtN := fullArenaClauseRefs_next_mem hokN.2.1.arena hp_inN
        have hmemP : fullArenaNextOff sN.core.arena sN.core.arena_len p.toNat ∈
            fullArenaClauseRefs sP := by
          rw [← hrefsN]
          rcases hnxtN with hend | hmem
          · exact absurd (hend.trans (halenN.trans halenP.symm)) (by omega)
          · exact hmem
        have := fullArenaScanRefs_disjoint hp_in hmemP (by omega)
        omega
      · rcases hnxt_mem with hend | hmem
        · exact absurd (hend.trans (halenP.trans halenN.symm)) (by omega)
        · have hmemN : fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat ∈
              fullArenaClauseRefsCore sN.core := by
            change fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat ∈
              fullArenaClauseRefs sN
            rw [hrefsN]; exact hmem
          have := fullArenaScanRefs_disjoint hp_inN hmemN hnb.1
          omega
  have hlt_32 : fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat < 2 ^ 32 := by omega
  have hlt_64 : fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat < 2 ^ 64 := by omega
  rw [hp_trunc, har_n, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_32]
  exact Nat.mod_eq_of_lt hlt_64

private theorem enter_connect_sat_loop_lit_lt {c : FullCfg} {F0 : CNF Nat}
    {F_cur3 : List (List Nat)} {s sP : FullState} {p : BitVec 64} {ks : BitVec 32}
    (hokP : M6EnterOk c F0 F_cur3 s sP) (hp_in : p.toNat ∈ fullArenaClauseRefs sP)
    (hp_wf : p.toNat + 3 ≤ sP.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore sP.core p.toNat ∧
      p.toNat + 3 + fullArenaClauseSizeCore sP.core p.toNat ≤
        fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat ∧
      fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat ≤ sP.core.arena_len ∧
      (fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat = sP.core.arena_len ∨
       fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat + 3 ≤ sP.core.arena_len))
    (hp2_lt : (p + 2#64).toNat < sP.core.arena.length)
    (hsz_eq : (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat =
      fullArenaClauseSizeCore sP.core p.toNat)
    (hk_lt : ks.toNat < (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat)
    (hidx_eq : (p + 3#64 + ks.setWidth 64).toNat = p.toNat + 3 + ks.toNat)
    (hidx_lt : (p + 3#64 + ks.setWidth 64).toNat < sP.core.arena.length)
    (hng_hdr : (sP.core.arena[p.toNat]'(by
      have := hokP.1.core_ok.arena_len_le; have := hokP.1.core_ok.arena_len_arr; omega) &&&
        (0x00080000#32 ||| 0x00400000#32)) = 0#32) :
    (sP.core.arena[(p + 3#64 + ks.setWidth 64).toNat]'hidx_lt).toNat < sP.core.vals.length := by
  have haarP := hokP.1.core_ok.arena_len_arr
  have halP := hokP.1.core_ok.arena_len_le
  have hng : fullArenaClauseGarb sP p.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have h0 : (sP.core.arena[p.toNat]'(by omega) &&& 0x00080000#32) = 0#32 := by
      have hmask_eq : (0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32 =
          (0x00080000#32 : BitVec 32) := by decide
      have h1 := congrArg (· &&& 0x00080000#32) hng_hdr
      rw [BitVec.zero_and, BitVec.and_assoc, hmask_eq] at h1
      exact h1
    rw [h0]; rfl
  have hmem_k : (sP.core.arena[(p + 3#64 + ks.setWidth 64).toNat]'hidx_lt).toNat ∈
      fullArenaClauseLits sP p.toNat := by
    unfold fullArenaClauseLits
    rw [mem_fullArenaClauseLitsCore_iff (by rw [← hsz_eq]; omega)]
    refine ⟨ks.toNat, by rw [← hsz_eq]; exact hk_lt, ?_⟩
    rw [dense_getElem_congr hidx_eq hidx_lt (by rw [hsz_eq] at hk_lt; omega)]
  have := hokP.2.1.arena.lits_lt p.toNat hp_in hng _ hmem_k
  rw [hokP.1.core_ok.vals_len]
  have := hokP.1.core_ok.cur_vars_le; omega

private theorem enter_dense_connect_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur3 : List (List Nat)} {ext ext3 : List (BitVec 64)} {s s4 : FullState}
    {connect_large : Bool} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {Jdone : Cont []} {m4 : Mem 64}
    (hSweep : Γ.Has "full_arena_sweep" Proof.Spec.fullArenaSweepSpec)
    (hWatchPush : Γ.Has "full_watch_push" Proof.Spec.fullWatchPushSpec)
    (hArenaNext : Γ.Has "full_arena_next" Proof.Spec.fullArenaNextSpec)
    (hcfg : FullM6HdrCfgOk c) (hext3 : M6HdrExtOk ext3)
    (hext3_init : M6HdrExtInitOk ext → M6HdrExtInitOk ext3 ∧ M6ExtW2bPres ext ext3)
    (hok4 : M6EnterOk c F0 F_cur3 s s4) (hd4 : DenseWatchesInv F_cur3 s4.core)
    (hdm4 : s4.core.dense_mode = 0#64)
    (hm4 : (FullMem c s4 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m4)
    (hJdone : ∀ mEnd, (∃ sP : FullState, M6EnterOk c F0 F_cur3 s sP ∧
      DenseWatchesInv F_cur3 sP.core ∧ sP.core.dense_mode = 0#64 ∧
      (FullMem c sP ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) mEnd) → Jdone () mEnd)
    (hQ : ∀ (res : Bool) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrCfgOk c → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (res = true → FullDenseInv c F0 s' ∧ (connect_large = false →
        s'.core.cur_level = 0 ∧ s'.core.dense_mode ≠ 0#64)) →
      (res = false → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (res, ()) m') :
    wp Γ Q X (enterConnectE c.hdr connect_large Jdone) m4 := by
  have har_cap := c.harena; have hmaxv := c.hmaxv; unfold dimacsBound at har_cap hmaxv
  let Rext3 : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R
  dsimp only [enterConnectE, enterEGrp0, enterEGrp0Body, enterEJnzF, enterECall, enterEDrop,
    enterEDfltT, enterEDflt, full_enter_dense_ex_fid_body]
  c0_hsplit
  · c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (p, ()) mP => p.toNat ≤ s4.core.arena_len ∧
        (p.toNat = s4.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s4) ∧
        ∃ sP : FullState,
          M6EnterOk c F0 F_cur3 s sP ∧ DenseWatchesInv F_cur3 sP.core ∧
          sP.core.arena_len = s4.core.arena_len ∧ sP.core.dense_mode = 0#64 ∧
          fullArenaClauseRefs sP = fullArenaClauseRefs s4 ∧
          (FullMem c sP ⋆ Rext3) mP)
      (fun (p, ()) _ => s4.core.arena_len - p.toNat)
      (fun JP hLoopP => by
        c0_hsteps_nogrp
        refine hLoopP (0#64, ()) m4 ⟨Nat.zero_le _, ?_, s4, hok4, hd4, rfl, hdm4, rfl, hm4⟩
        by_cases hz : s4.core.arena_len = 0
        · exact Or.inl hz.symm
        · exact Or.inr (fullArenaClauseRefs_zero_mem hok4.2.1.arena (Nat.pos_of_ne_zero hz)))
      (fun JP ⟨p, ⟨⟩⟩ mP ⟨hp_le, hp_mem, sP, hokP, hdP, halenP, hdmP, hrefsP, hmP⟩
          hLoopP => ?_)
    have halP := hokP.1.core_ok.arena_len_le
    have haarP := hokP.1.core_ok.arena_len_arr
    c0_hsplit
    · have hp_lt : p.toNat < sP.core.arena_len := by omega
      have hp_in : p.toNat ∈ fullArenaClauseRefs sP := by
        rw [hrefsP]; exact hp_mem.resolve_left (by omega)
      have hp_wf := hokP.2.1.arena.refs_wf p.toNat hp_in
      have hp_lt32 : p.toNat < 2 ^ 32 := by omega
      have hp_trunc : (p.setWidth 32).toNat = p.toNat := by bv_omega
      have hnb := fullArenaNextOff_bounds (ar := sP.core.arena) (alen := sP.core.arena_len)
        (cref := p.toNat) hp_wf.1
      have hnxt_mem := fullArenaClauseRefs_next_mem hokP.2.1.arena hp_in
      c0_hsteps_nogrp
      refine wp_join_state0 (α := FullState)
        (fun sN mN => M6EnterOk c F0 F_cur3 s sN ∧ DenseWatchesInv F_cur3 sN.core ∧
          sN.core.arena_len = s4.core.arena_len ∧ sN.core.dense_mode = 0#64 ∧
          fullArenaClauseRefs sN = fullArenaClauseRefs sP ∧ (FullMem c sN ⋆ Rext3) mN)
        (fun _ sN mN ⟨hokN, hdN, halenN, hdmN, hrefsN, hmN⟩ => by
          c0_hsteps_nogrp; dr_call hArenaNext
          refine ⟨c, sN, Rext3, rfl, hokN.1, hmN, ?_⟩
          have hn_eq := enter_connect_arena_next_eq (by omega) hokP hokN halenP halenN
            hrefsN hp_in hp_trunc
          c0_hsteps_nogrp
          refine hLoopP (_, ()) mN (by dsimp only [Arg.val]; rw [hn_eq]; omega)
            ⟨by dsimp only [Arg.val]; rw [hn_eq]; omega, ?_, sN, hokN, hdN, halenN, hdmN,
             hrefsN.trans hrefsP, hmN⟩
          dsimp only [Arg.val]; rw [hn_eq]
          rcases hnxt_mem with hend | hmem
          · exact Or.inl (hend.trans halenP)
          · exact Or.inr (hrefsP ▸ hmem))
        (fun JN hJN => by
          have hsz_eq : (sP.core.arena[(p + 2#64).toNat]'(by
              have : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
              omega)).toNat = fullArenaClauseSizeCore sP.core p.toNat := by
            have hp2 : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
            unfold fullArenaClauseSizeCore
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hp2]
          have hsz_ge3 : 3 ≤ (sP.core.arena[(p + 2#64).toNat]'(by
              have : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
              omega)).toNat := by rw [hsz_eq]; exact hp_wf.2.1
          have hsz_lt31 : (sP.core.arena[(p + 2#64).toNat]'(by
              have : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
              omega)).toNat < 2 ^ 31 := by
            rw [hsz_eq]; have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; omega
          have hmask := bv32_mask_7fffffff_props hsz_ge3 hsz_lt31
          have hp_lt31 : (p.setWidth 32).toNat < 0x80000000 := by rw [hp_trunc]; omega
          have hp_neff : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun heq => by
            rw [heq] at hp_lt31; revert hp_lt31; decide
          c0_hsteps_nogrp
          · have hng_hdr : (sP.core.arena[p.toNat]'(by omega) &&&
                (0x00080000#32 ||| 0x00400000#32)) = 0#32 := by assumption
            refine wp_join_state (ts := [.bool, i32]) (α := Bool × BitVec 32)
              (fun (b, k) => (b, k, ()))
              (fun _ ms => ms = mP)
              (fun _ ⟨sat, k⟩ ms hms => by
                subst ms
                refine wp_join_state (ts := [i32]) (α := BitVec 32 × FullState)
                  (fun (k', _) => (k', ()))
                  (fun (_, sEnd) mEnd => M6EnterOk c F0 F_cur3 s sEnd ∧
                    DenseWatchesInv F_cur3 sEnd.core ∧
                    sEnd.core.arena_len = s4.core.arena_len ∧
                    sEnd.core.dense_mode = 0#64 ∧
                    fullArenaClauseRefs sEnd = fullArenaClauseRefs sP ∧
                    (FullMem c sEnd ⋆ Rext3) mEnd)
                  (fun _ ⟨_, sEnd⟩ mEnd h => by
                    dsimp only at h; c0_hsteps_nogrp; exact hJN sEnd mEnd h)
                  (fun Jend hJend => by
                    c0_hsplit
                    · have hp2_mod : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                      let sz64 : BitVec 64 :=
                        (sP.core.arena[p.toNat + 2]'(by omega)).setWidth 64
                      have hsz64_any : ∀ h',
                          (sP.core.arena[(p + 2#64).toNat]'h').setWidth 64 = sz64 :=
                        fun _ => congrArg (BitVec.setWidth 64)
                          (dense_getElem_congr hp2_mod _ (by omega))
                      have hhdr_any : ∀ h',
                          sP.core.arena[p.toNat]'h' = fullArenaHdrCore sP.core p.toNat :=
                        fun _ => by
                          unfold fullArenaHdrCore
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      have hg1 := enter_markGarb_denseOk hokP hdP hdmP hp_in
                        (sP.core.arena_garbage + 3#64 + sz64) (sP.core.num_irred - 1#64)
                      have hg2 := enter_markGarb_denseOk hokP hdP hdmP hp_in
                        (sP.core.arena_garbage + 3#64 + sz64) sP.core.num_irred
                      have hset_refs : ∀ ni'', fullArenaClauseRefs
                          { sP with core := { sP.core with
                            arena := sP.core.arena.set p.toNat
                              (fullArenaHdrCore sP.core p.toNat ||| 0x00080000#32),
                            arena_garbage := sP.core.arena_garbage + 3#64 + sz64,
                            num_irred := ni'' } } = fullArenaClauseRefs sP := fun ni'' => by
                        unfold fullArenaClauseRefs fullArenaClauseRefsCore
                        exact (hokP.2.1.arena.markGarb hokP.1.core_ok hp_in
                          (sP.core.arena_garbage + 3#64 + sz64)).1
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [])
                        (fun () mG => ∃ ni'',
                          let sG : FullState :=
                            { sP with core := { sP.core with
                              arena := sP.core.arena.set p.toNat
                                (fullArenaHdrCore sP.core p.toNat ||| 0x00080000#32),
                              arena_garbage := sP.core.arena_garbage + 3#64 + sz64,
                              num_irred := ni'' } }
                          M6EnterOk c F0 F_cur3 s sG ∧ DenseWatchesInv F_cur3 sG.core ∧
                          sG.core.arena_len = s4.core.arena_len ∧
                          sG.core.dense_mode = 0#64 ∧
                          fullArenaClauseRefs sG = fullArenaClauseRefs sP ∧
                          (FullMem c sG ⋆ Rext3) mG)
                        (fun _ ⟨⟩ mG ⟨ni'', hokG, hdG, halG, hdmG, hrefsG, hmG⟩ => by
                          c0_hsteps_nogrp
                          exact hJend (k, _) mG ⟨hokG, hdG, halG, hdmG, hrefsG, hmG⟩)
                        (fun Jnir hJnir => by
                          have hp2_2 : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := by bv_omega
                          have hsz64_ofn : BitVec.setWidth 64
                              (sP.core.arena[(p + (2 : BitVec 64)).toNat]'(by
                                rw [hp2_2]; omega)) = sz64 := hsz64_any _
                          c0_hsplit
                          · c0_hsteps_nogrp
                            simp only [show (524288 : BitVec 32) = 524288#32 from rfl,
                              show (3 : BitVec 64) = 3#64 from rfl,
                              show (1 : BitVec 64) = 1#64 from rfl] at *
                            exact hJnir () _ ⟨sP.core.num_irred - 1#64, hg1.1, hg1.2,
                              halenP, hdmP, hset_refs _, by
                                rw [hhdr_any _, hsz64_ofn] at *; assumption⟩
                          · c0_hsteps_nogrp
                            simp only [show (524288 : BitVec 32) = 524288#32 from rfl,
                              show (3 : BitVec 64) = 3#64 from rfl] at *
                            exact hJnir () _ ⟨sP.core.num_irred, hg2.1, hg2.2, halenP,
                              hdmP, hset_refs _, by
                                rw [hhdr_any _, hsz64_ofn] at *; assumption⟩)
                    · c0_hsteps_nogrp
                      refine wp_loop_inv (ts := [i32])
                        (fun (kw, ()) mK =>
                          kw.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'(by
                            have : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                            omega)).toNat ∧
                          ∃ sK : FullState,
                            M6EnterOk c F0 F_cur3 s sK ∧ DenseWatchesInv F_cur3 sK.core ∧
                            sK.core.arena_len = s4.core.arena_len ∧ sK.core.dense_mode = 0#64 ∧
                            fullArenaClauseRefs sK = fullArenaClauseRefs sP ∧
                            (FullMem c sK ⋆ Rext3) mK)
                        (fun (kw, ()) _ =>
                          (sP.core.arena[(p + 2#64).toNat]'(by
                            have : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                            omega)).toNat - kw.toNat)
                        (fun JK hLoopK => by
                          c0_hsteps_nogrp
                          exact hLoopK (0#32, ()) mP ⟨Nat.zero_le _, sP, hokP, hdP,
                            halenP, hdmP, rfl, hmP⟩)
                        (fun JK ⟨kw, ⟨⟩⟩ mK
                            ⟨hk_le, sK, hokK, hdK, halenK, hdmK, hrefsK, hmK⟩
                            hLoopK => ?_)
                      have haarK := hokK.1.core_ok.arena_len_arr
                      c0_hsplit
                      · have hk_lt : kw.toNat < (sP.core.arena[(p + 2#64).toNat]'(by
                            have : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                            omega)).toNat := hc
                        have hidx_eq : (p + 3#64 + kw.setWidth 64).toNat =
                            p.toNat + 3 + kw.toNat := by
                          have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; bv_omega
                        have hidx_lt : (p + 3#64 + kw.setWidth 64).toNat <
                            sK.core.arena.length := by
                          rw [hidx_eq]; rw [hsz_eq] at hk_lt
                          have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                          have := hokK.1.core_ok.arena_len_le; omega
                        c0_hsteps_nogrp; dr_call hWatchPush
                        refine ⟨c, sK, Rext3, rfl, hokK.1, hdK.layout, by simp,
                          fun _ => ⟨hmask.2.1, hp_neff⟩, hmK,
                          fun ok wvecK' wstkK' wlenK' wuK' wsortK' mK' hlenK' hlayK'
                            hothK' hokT hokF hmK' => ?_⟩
                        dsimp only [Arg.val] at hokT hokF
                        let sK' : FullState :=
                          { sK with
                            core := { sK.core with wvec := wvecK', wstk := wstkK',
                                                   wlen := wlenK', wusable := wuK' }
                            scratch := { sK.scratch with wsort := wsortK' } }
                        have hp_inK : (p.setWidth 32).toNat ∈
                            fullArenaClauseRefsCore sK.core := by
                          change (p.setWidth 32).toNat ∈ fullArenaClauseRefs sK
                          rw [hrefsK, hp_trunc]; exact hp_in
                        obtain ⟨hokK', hdK'⟩ := enter_watch_push hokK hdK hdmK hmask.1
                          hmask.2.2 hp_lt31 hp_inK hlenK' hlayK' hothK'
                          (fun ht => by
                            obtain ⟨hl, _, hsz', hpre', hw0', hw1'⟩ := hokT ht
                            exact ⟨hl, hsz', hpre', hw0', hw1' rfl⟩)
                          (fun hf hl => (hokF hf).1 hl)
                        c0_hsplit
                        · have hk1 : (kw + 1#32).toNat = kw.toNat + 1 := by bv_omega
                          c0_hsteps_nogrp
                          exact hLoopK (kw + 1#32, ()) mK' (by dsimp only; rw [hk1]; omega)
                            ⟨by omega, sK', hokK', hdK', halenK, hdmK, hrefsK, hmK'⟩
                        · let sOom : FullState :=
                            { sK' with core := { sK'.core with oom := 0#64 } }
                          have hlenOom : sOom.LengthsOk c :=
                            ⟨{ hlenK'.core_ok with vals_len := hlenK'.core_ok.vals_len },
                              hlenK'.scratch_ok⟩
                          have hwOom := fullWitnessInv_with_oom hokK'.2.1 0#64
                          have hpos_al : 0 < sOom.core.arena_len := by
                            dsimp only [sOom, sK']; rw [halenK, ← halenP]; omega
                          c0_hsteps_nogrp; dr_call hSweep
                          refine ⟨c, F0, F_cur3, sOom, Rext3, rfl, hlenOom, hwOom,
                            hokK'.2.2.2.1, hdmK,
                            fun hpos => absurd (hokK'.2.2.2.2.2.1 ▸ hpos) (Nat.lt_irrefl 0),
                            (by assumption), ?_⟩
                          intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ scS mS sS
                            hlenS _ hextS _ hllS hwS hndS _ _ _ _ _ hmS
                          have hspS : FullSparseInv c F0 sS :=
                            ⟨⟨hlenS, ⟨F_cur3, hwS⟩⟩, hokK'.2.2.1, hndS,
                              ⟨hllS, hextS ▸ hokK'.2.2.2.2.1.2⟩, hdmK⟩
                          c0_hsteps_nogrp
                          exact hQ false ext3 sS _ hcfg hext3 hext3_init hlenS hokK'.2.2.1
                            hndS hspS.2.2.2.1 hokK'.2.2.2.2.2.2.1 hokK'.2.2.2.2.2.2.2
                            (by simp) (fun _ => ⟨hspS, hokK'.2.2.2.2.2.1⟩)
                            (fullM6HdrMem_unfocus_full hmS)
                      · c0_hsteps_nogrp
                        exact hJend (kw, sK) mK
                          ⟨hokK, hdK, halenK, hdmK, hrefsK, hmK⟩))
              (fun Jsat hJsat => by
                c0_hsteps_nogrp
                refine wp_loop_inv (ts := [i32])
                  (fun (ks, ()) mK => mK = mP ∧
                    ks.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'(by
                      have : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                      omega)).toNat)
                  (fun (ks, ()) _ =>
                    (sP.core.arena[(p + 2#64).toNat]'(by
                      have : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                      omega)).toNat - ks.toNat)
                  (fun Js hLs => by
                    c0_hsteps_nogrp; exact hLs (0#32, ()) mP ⟨rfl, Nat.zero_le _⟩)
                  (fun Js ⟨ks, ⟨⟩⟩ mK ⟨hmK_eq, hk_le⟩ hLs => by
                    subst mK
                    c0_hsplit
                    · have hk_lt : ks.toNat < (sP.core.arena[(p + 2#64).toNat]'(by
                          have : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                          omega)).toNat := hc
                      have hk1 : (ks + 1#32).toNat = ks.toNat + 1 := by bv_omega
                      have hidx_eq : (p + 3#64 + ks.setWidth 64).toNat =
                          p.toNat + 3 + ks.toNat := by
                        have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; bv_omega
                      have hidx_lt : (p + 3#64 + ks.setWidth 64).toNat <
                          sP.core.arena.length := by
                        rw [hidx_eq]; rw [hsz_eq] at hk_lt
                        have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                        have := hokP.1.core_ok.arena_len_le; omega
                      have hlit_lt := enter_connect_sat_loop_lit_lt hokP hp_in hp_wf _
                        hsz_eq hk_lt hidx_eq hidx_lt hng_hdr
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun () mJ => mJ = mP)
                        (fun _ ⟨⟩ mJ hmJ => by
                          subst mJ; c0_hsteps_nogrp
                          exact hLs (ks + 1#32, ()) mP (by dsimp only; rw [hk1]; omega)
                            ⟨rfl, by omega⟩)
                        (fun Js_3 hJs3 => by
                          c0_hsteps_nogrp
                          c0_hsplit
                          · c0_hsteps_nogrp; exact hJsat (true, ks) mP rfl
                          · c0_hsteps_nogrp; exact hJs3 () mP rfl
                          all_goals (c0_hsteps_nogrp; try exact hJs3 () mP rfl))
                    · c0_hsteps_nogrp; exact hJsat (false, ks) mP rfl))
          · c0_hsteps_nogrp; exact hJN sP mP ⟨hokP, hdP, halenP, hdmP, rfl, hmP⟩)
    · c0_hsteps_nogrp; exact hJdone mP ⟨sP, hokP, hdP, hdmP, hmP⟩
  · c0_hsteps_nogrp; exact hJdone m4 ⟨s4, hok4, hd4, hdm4, hm4⟩

/-! ## 4. Top-Level `full_enter_dense_ex_fid` & `full_enter_dense` -/

/-- `full_enter_dense_ex_fid` WP proof (`Spec.fullEnterDenseExM6Spec`). -/
theorem full_enter_dense_ex_fid_wp (Γ : Env)
    (hBacktrack : Γ.Has "full_backtrack" Proof.Spec.fullBacktrackSpec)
    (hFlush : Γ.Has "full_flush_trail" PropSearch.Spec.flushTrailM6Spec)
    (hSweep : Γ.Has "full_arena_sweep" Proof.Spec.fullArenaSweepSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hSweepBins : Γ.Has "full_sweep_bins" Proof.Spec.fullSweepBinsSpec)
    (hWatchPush : Γ.Has "full_watch_push" Proof.Spec.fullWatchPushSpec)
    (hArenaNext : Γ.Has "full_arena_next" Proof.Spec.fullArenaNextSpec) :
    ∀ a m Q X, Spec.fullEnterDenseExM6Spec a m Q X →
      Func.wp Γ full_enter_dense_ex_fid_body a m Q X := by
  rintro ⟨h, connect_large, ⟨⟩⟩ m Q X
    ⟨c, F0, ext, s, R, rfl, hcfg, hext, hlen, hcore, hlm, hnd, hext_ok, hdm_oom, hm, hQ⟩
  obtain ⟨F_cur, hw0⟩ := hcore.witness
  have har_cap := c.harena; have hmaxv := c.hmaxv; unfold dimacsBound at har_cap hmaxv
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  let Rext0 : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
  have hm0_f := fullM6HdrMem_focus_full hm
  unfold Func.wp full_enter_dense_ex_fid_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullCoreInv c F0 s1 ∧ FullLitMarksClear c s1 ∧ FullArenaVarsNodup s1 ∧
      FullExtScratchOk c s1 ∧ s1.core.cur_level = 0 ∧ s1.core.cur_vars = s.core.cur_vars ∧
      s1.core.fuel = s.core.fuel ∧ (s1.core.dense_mode ≠ 0#64 → s1.core.oom = 0#64) ∧
      (FullMem c s1 ⋆ Rext0) m1) ?_ ?_
  · rintro _ s1 m1 ⟨hcore1, hlm1, hnd1, hext_ok1, hcl1, hcv1, hfu1, hdm_oom1, hm1⟩
    clear hm hcore hw0 hlm hnd hext_ok
    c0_hsplit
    · have hdm1_z : s1.core.dense_mode = 0#64 :=
        Classical.byContradiction fun hnz => absurd (hdm_oom1 hnz) hc
      have hsp1 : FullSparseInv c F0 s1 := ⟨hcore1, hlm1, hnd1, hext_ok1, hdm1_z⟩
      c0_hsteps_nogrp
      exact hQ false ext s1 _ hcfg hext (fun h => ⟨h, M6ExtW2bPres.refl ext⟩)
        hcore1.lengths hlm1 hnd1 hext_ok1 hcv1 (by rw [hfu1]; exact Nat.le_refl _) (by simp)
        (fun _ => ⟨hsp1, hcl1⟩) (fullM6HdrMem_unfocus_full hm1)
    c0_hsplit
    · have hden1 : FullDenseInv c F0 s1 := ⟨hcore1, hlm1, hnd1, hext_ok1, hcl1, hc⟩
      c0_hsteps_nogrp
      exact hQ true ext s1 _ hcfg hext (fun h => ⟨h, M6ExtW2bPres.refl ext⟩)
        hcore1.lengths hlm1 hnd1 hext_ok1 hcv1 (by rw [hfu1]; exact Nat.le_refl _)
        (fun _ => ⟨hden1, fun _ => ⟨hcl1, hc⟩⟩) (by simp) (fullM6HdrMem_unfocus_full hm1)
    have hsp1 : FullSparseInv c F0 s1 := ⟨hcore1, hlm1, hnd1, hext_ok1, hc⟩
    c0_hsteps_nogrp; dr_call hFlush
    refine ⟨c, F0, ext, s1, R, rfl, FullM6HdrInv.mk_inv hcfg hext hsp1,
      fullM6HdrMem_unfocus_full hm1, ?_⟩
    intro fr1 ext2 s2 m2 hext2_ok hext2_init hinv2 _ _ _ _ _ _ hcv2 _ hfu2 hcl2_fn _ _ _ hm2
    have hsp2 := hinv2.sparse
    have hcl2 : s2.core.cur_level = 0 := hcl2_fn hcl1
    have hcv2' : s2.core.cur_vars = s.core.cur_vars := hcv2.trans hcv1
    have hfu2' : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [← hfu1]; exact hfu2
    c0_hsplit
    · c0_hsteps_nogrp
      exact hQ false ext2 s2 m2 hcfg hext2_ok hext2_init hsp2.1.lengths hsp2.2.1 hsp2.2.2.1
        hsp2.2.2.2.1 hcv2' hfu2' (by simp) (fun _ => ⟨hsp2, hcl2⟩) hm2
    c0_hsteps_nogrp
    refine wp_join_state0 (α := List (BitVec 64) × FullState)
      (fun (ext3, s3) m3 => M6HdrExtOk ext3 ∧
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext3 ∧ M6ExtW2bPres ext ext3) ∧
        FullSparseInv c F0 s3 ∧ s3.core.cur_level = 0 ∧ s3.core.cur_vars = s.core.cur_vars ∧
        s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext3 s3 ⋆ R) m3) ?_ ?_
    · rintro _ ⟨ext3, s3⟩ m3 ⟨hext3, hext3_init, hsp3, hcl3, hcv3, hfu3, hm3⟩
      obtain ⟨F_cur3, hspw3⟩ := hsp3.exists_witness
      have hm3_f := fullM6HdrMem_focus_full hm3
      let Rext3 : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R
      c0_hsteps_nogrp; dr_call hSweepBins
      refine ⟨c, F0, F_cur3, s3, Rext3, rfl, hspw3.1, hspw3.2.1, hm3_f, ?_⟩
      intro wvec4 wstk4 wlen4 nb4 wsort4 m4 s4 hlen4 _ hd4 hw4 hm4
      have hok4 : M6EnterOk c F0 F_cur3 s s4 :=
        ⟨hlen4, hw4, hspw3.2.2.1, hspw3.2.2.2.1, hspw3.2.2.2.2.1, hcl3, hcv3, hfu3⟩
      have hdone_fn : ∀ (sP : FullState) (mFin : Mem 64),
          M6EnterOk c F0 F_cur3 s sP → DenseWatchesInv F_cur3 sP.core →
          sP.core.dense_mode = 0#64 →
          (FullMem c { sP with core := { sP.core with dense_mode := 1#64 } } ⋆ Rext3) mFin →
          Q (true, ()) mFin := fun sP mFin hokP hdP _ hmFin => by
        let sFin : FullState := { sP with core := { sP.core with dense_mode := 1#64 } }
        have hlenFin : sFin.LengthsOk c :=
          ⟨{ hokP.1.core_ok with vals_len := hokP.1.core_ok.vals_len }, hokP.1.scratch_ok⟩
        have hwFin := fullWitnessInv_with_dense_mode_nz hokP.2.1 hdP (dm := 1#64) (by decide)
        have hdmFin : sFin.core.dense_mode ≠ 0#64 := by dsimp only [sFin]; decide
        have hdenFin : FullDenseInv c F0 sFin :=
          ⟨⟨hlenFin, ⟨F_cur3, hwFin⟩⟩, hokP.2.2.1, hokP.2.2.2.1, hokP.2.2.2.2.1,
            hokP.2.2.2.2.2.1, hdmFin⟩
        exact hQ true ext3 sFin mFin hcfg hext3 hext3_init hlenFin hokP.2.2.1 hokP.2.2.2.1
          hokP.2.2.2.2.1 hokP.2.2.2.2.2.2.1 hokP.2.2.2.2.2.2.2
          (fun _ => ⟨hdenFin, fun _ => ⟨hokP.2.2.2.2.2.1, hdmFin⟩⟩) (by simp)
          (fullM6HdrMem_unfocus_full hmFin)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun () mEnd => ∃ sP : FullState,
          M6EnterOk c F0 F_cur3 s sP ∧ DenseWatchesInv F_cur3 sP.core ∧
          sP.core.dense_mode = 0#64 ∧ (FullMem c sP ⋆ Rext3) mEnd)
        (fun _ ⟨⟩ mEnd ⟨sP, hokP, hdP, hdmP, _⟩ => by
          c0_hsteps_nogrp
          exact hdone_fn sP _ hokP hdP hdmP (by assumption))
        (fun Jdone hJdone => by
          dsimp only [Blocks.get]
          change wp Γ Q X (enterConnectE c.hdr connect_large Jdone) m4
          exact enter_dense_connect_wp hSweep hWatchPush hArenaNext hcfg hext3 hext3_init hok4
            hd4 hspw3.2.2.2.2.2 hm4 (fun mEnd h => hJdone () mEnd h) hQ)
    · intro Ju hJu
      c0_hsplit
      · exact enter_had_unfl_wp hSweep hProp hFlush hcfg hext2_ok hsp2 hcl2 hcv2' hfu2' hm2
          (fun ext3 s3 m3 he3 he3i hsp3 hcl3 hcv3 hfu3 hm3 =>
            hJu (ext3, s3) m3
              ⟨he3, dense_m6_extInit_trans hext2_init he3i, hsp3, hcl3, hcv3, hfu3, hm3⟩)
          (fun ext3 s3 m3 he3 he3i hsp3 hcl3 hcv3 hfu3 hm3 =>
            hQ false ext3 s3 m3 hcfg he3 (dense_m6_extInit_trans hext2_init he3i)
              hsp3.1.lengths hsp3.2.1 hsp3.2.2.1 hsp3.2.2.2.1 hcv3 hfu3 (by simp)
              (fun _ => ⟨hsp3, hcl3⟩) hm3)
      · c0_hsteps_nogrp
        exact hJu (ext2, s2) m2 ⟨hext2_ok, hext2_init, hsp2, hcl2, hcv2', hfu2', hm2⟩
  · intro J1 hJ1; c0_hsplit
    · c0_hsteps_nogrp; dr_call hBacktrack
      refine ⟨c, s, Rext0, rfl, hlen, hclv_lt, fun _ => by
        have := hw0.cur_level_le; have := hlen.core_ok.trail_end_le
        have := hlen.core_ok.cur_vars_le; omega,
        hw0.trail_lits_lt, hm0_f, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 s1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur hw0 (Nat.zero_le _)
      have hcl1' : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
      have hll1 : FullLastLearnedWf s1 := fun i hi => by
        change sc1.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
          (sc1.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s
        rw [hprsc1.1.1]; exact hext_ok.1 i hi
      have hcore1 : FullCoreInv c F0 s1 := ⟨hlen1, ⟨F_cur, hw1⟩⟩
      have hext1' : FullExtScratchOk c s1 := ⟨hll1, hprsc1.1.2 ▸ hext_ok.2⟩
      c0_hsteps_nogrp
      exact hJ1 s1 m1 ⟨hcore1, hlm, hnd, hext1', hcl1', rfl, rfl, hdm_oom, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at this; exact this
      c0_hsteps_nogrp
      exact hJ1 s m ⟨hcore, hlm, hnd, hext_ok, hcl0, rfl, rfl, hdm_oom, hm0_f⟩

/-- `full_enter_dense` WP proof (`Spec.fullEnterDenseM6Spec`). -/
theorem full_enter_dense_wp (Γ : Env)
    (hEx : Γ.Has "full_enter_dense_ex_fid" Spec.fullEnterDenseExM6Spec) :
    ∀ a m Q X, Spec.fullEnterDenseM6Spec a m Q X →
      Func.wp Γ full_enter_dense_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X
    ⟨c, F0, ext, s, R, rfl, hcfg, hext, hlen, hcore, hlm, hnd, hext_ok, hdm_oom, hm, hQ⟩
  unfold Func.wp full_enter_dense_body
  c0_hsteps_nogrp; dr_call hEx
  refine ⟨c, F0, ext, s, R, rfl, hcfg, hext, hlen, hcore, hlm, hnd, hext_ok, hdm_oom, hm, ?_⟩
  intro ok ext' s' m' hcfg' hext' hext'_init hlen' hlm' hnd' hext_ok' hcv' hfu' hok_t hok_f hm'
  exact hQ ok ext' s' m' hcfg' hext' hext'_init hlen' hlm' hnd' hext_ok' hcv' hfu'
    (fun h => (hok_t h).1) hok_f hm'

end LeanQbe.T.Examples.Kissat.Proof.Dense
