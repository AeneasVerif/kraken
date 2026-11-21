module

public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Stage-4 Watch & Probe-Prop Preservation Helpers (`Stage 4`, Part 2)

Provides:
1. `Stage4PropInvs`: `FullSparseInv`/`FullSparseProbeInv` projections, `withEmptyModeWatches` /
   `fullWitnessInv_replace_watches` transfers, and `fullAssign_trailExtCore`.
2. `SplitWatches`: `FullSplitWatchesInv` and its `.init`, `.with_nonwatch`, `.write_bin`,
   `.write_large`, `.after_push`, `.finish`, `.advance_rem` operations.
3. `ProbePropHelpers`: `unitAssignLvl_preserves_witness`, `arena_swap*`, and
   `clause_falsified_of_find_repl_none`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullProbeTransSpecs

namespace FullProbeTransHelpers

section Stage4PropInvs

theorem fullSparseInv_toProbe {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : FullSparseProbeInv c F0 s :=
  ⟨h.1, h.2.1.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem fullSparseInv_ofProbe {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseProbeInv c F0 s)
    (hlm : ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8) :
    FullSparseInv c F0 s :=
  ⟨h.1, ⟨h.2.1, hlm⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem fullSparseInvW_toSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullSparseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullExtScratchOk_of_pres {c : FullCfg} {s s' : FullState} (h : FullExtScratchOk c s)
    (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullExtScratchOk c s' := by
  refine ⟨fun i hi => ?_, by simpa [hpres.2] using h.2⟩
  rcases h.1 i hi with hff | href
  · left; simpa [hpres.1] using hff
  · right; simpa [hpres.1] using hsub _ href

theorem fullSparseProbeInv_of_probeScratchPres {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hlen' : s'.LengthsOk c) (hm0 : FullMrkZero c s') (hnd : FullArenaVarsNodup s')
    (hext : FullExtScratchOk c s) (hpres : FullProbeScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s')
    (hdm : s'.core.dense_mode = 0#64) (hw : ∃ F_cur, FullWitnessInv c F0 F_cur s'.core) :
    FullSparseProbeInv c F0 s' :=
  ⟨⟨hlen', hw⟩, hm0, hnd, fullExtScratchOk_of_pres hext hpres.1 hsub, hdm⟩

theorem fullSparseInv_with_scratch_pres {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hex : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } := by
  refine ⟨h.1.with_scratch ⟨h.1.lengths.core_ok, hok⟩ rfl,
    h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  refine ⟨fun i hi => ?_, by simpa [hex] using h.2.2.2.1.2⟩
  simpa [FullLastLearnedWf, fullArenaClauseRefs, hll] using h.2.2.2.1.1 i hi

theorem fullSparseProbeInv_with_scratch_pres {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseProbeInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hex : sc'.extend_len = s.scratch.extend_len) :
    FullSparseProbeInv c F0 { s with scratch := sc' } := by
  refine ⟨h.1.with_scratch ⟨h.1.lengths.core_ok, hok⟩ rfl,
    h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  refine ⟨fun i hi => ?_, by simpa [hex] using h.2.2.2.1.2⟩
  simpa [FullLastLearnedWf, fullArenaClauseRefs, hll] using h.2.2.2.1.1 i hi

theorem fullArenaVarsNodup_of_arena_eq {s s' : FullState} (h : FullArenaVarsNodup s)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len) :
    FullArenaVarsNodup s' := by
  intro r hr hg
  have h1 : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    simp [fullArenaClauseRefs, fullArenaClauseRefsCore, har, hal]
  have h2 : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := by
    simp [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, har]
  have h3 : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
    simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, har]
  rw [h1] at hr; rw [h2] at hg; rw [h3]; exact h r hr hg

theorem fullArenaVarsNodup_of_lits_perm {s s' : FullState} (h : FullArenaVarsNodup s)
    (href : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hper : ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s' r = false →
      fullArenaClauseGarb s r = false ∧
      (fullArenaClauseLits s' r).Perm (fullArenaClauseLits s r)) :
    FullArenaVarsNodup s' := by
  intro r hr hg; rw [href] at hr
  obtain ⟨hg0, hp⟩ := hper r hr hg
  exact (hp.map (· / 2)).nodup_iff.mpr (h r hr hg0)

theorem fullArenaVarsNodup_of_permEq {s s' : FullState} (h : FullArenaVarsNodup s)
    (hp : FullArenaPermEq s.core s'.core) : FullArenaVarsNodup s' :=
  fullArenaVarsNodup_of_lits_perm h hp.2.1 fun r hr hg =>
    ⟨(hp.2.2 r hr).2.1.symm.trans hg, (hp.2.2 r hr).2.2⟩

theorem fullLastLearnedWf_of_refs_eq {s s' : FullState} (h : FullLastLearnedWf s)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (href : fullArenaClauseRefs s' = fullArenaClauseRefs s) : FullLastLearnedWf s' := by
  intro i hi; simpa [FullLastLearnedWf, hll, href] using h i hi

/-- Empty-watch core state (`wvec = 0, wlen = 0`) reusing `FullInv2` core preservation. -/
abbrev withEmptyModeWatches (c : FullCfg) (s : FullState) : FullState :=
  { s with core := { s.core with wvec := List.replicate (4 * c.max_vars) 0#32, wlen := 0 } }

theorem modeWatchesInv_empty (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (hcv : s.core.cur_vars ≤ c.max_vars) :
    ModeWatchesInv F_cur (withEmptyModeWatches c s).core := by
  by_cases hc : s.core.dense_mode = 0#64
  · have hwo : ∀ l < 2 * s.core.cur_vars,
        fullWatchOffCore { (withEmptyModeWatches c s).core with dense_mode := 0#64 } l = 0 :=
      fun l hl => by
        unfold fullWatchOffCore withEmptyModeWatches
        simp [show 2 * l < 4 * c.max_vars by omega]
    have hwsz : ∀ l < 2 * s.core.cur_vars,
        fullWatchSizeCore { (withEmptyModeWatches c s).core with dense_mode := 0#64 } l = 0 :=
      fun l hl => by
        unfold fullWatchSizeCore withEmptyModeWatches
        simp [show 2 * l + 1 < 4 * c.max_vars by omega]
    dsimp only [withEmptyModeWatches] at hwo hwsz
    simp only [ModeWatchesInv, hc, ↓reduceIte]
    exact WatchesInv.of_slices
      (fun l hl => by rw [hwo l hl, hwsz l hl]; exact Nat.zero_le _)
      (fun l hl hp => by rw [hwsz l hl] at hp; exact absurd hp (by omega))
      (fun l1 _ h1 _ _ hp1 _ => by rw [hwsz l1 h1] at hp1; exact absurd hp1 (by omega))
      (fun l hl => by rw [hwo l hl, hwsz l hl]; exact .empty)
  · have hwo : ∀ l < 2 * s.core.cur_vars,
        fullWatchOffCore (withEmptyModeWatches c s).core l = 0 := fun l hl => by
      unfold fullWatchOffCore withEmptyModeWatches
      simp [show 2 * l < 4 * c.max_vars by omega]
    have hwsz : ∀ l < 2 * s.core.cur_vars,
        fullWatchSizeCore (withEmptyModeWatches c s).core l = 0 := fun l hl => by
      unfold fullWatchSizeCore withEmptyModeWatches
      simp [show 2 * l + 1 < 4 * c.max_vars by omega]
    dsimp only [withEmptyModeWatches] at hwo hwsz
    simp only [ModeWatchesInv, hc, ↓reduceIte]
    exact DenseWatchesInv.of_slices
      (fun l hl => by rw [hwo l hl, hwsz l hl]; exact Nat.zero_le _)
      (fun l hl hp => by rw [hwsz l hl] at hp; exact absurd hp (by omega))
      (fun l1 _ h1 _ _ hp1 _ => by rw [hwsz l1 h1] at hp1; exact absurd hp1 (by omega))
      (fun l hl => by rw [hwo l hl, hwsz l hl]; exact .empty)

theorem fullWitnessInv_replace_watches {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k1 k2 : FullCoreState} (hw : FullWitnessInv c F0 F_cur k1)
    (hcur : k2.cur_vars = k1.cur_vars) (har : k2.arena = k1.arena)
    (hal : k2.arena_len = k1.arena_len) (hcl : k2.cur_level = k1.cur_level)
    (hte : k2.trail_end = k1.trail_end) (htrl : k2.trl = k1.trl)
    (hval : k2.vals = k1.vals) (hlvl : k2.lvl = k1.lvl) (hrsn : k2.rsns = k1.rsns)
    (htp : k2.trail_pos = k1.trail_pos) (hft : k2.frame_trail = k1.frame_trail)
    (hfd : k2.frame_dec = k1.frame_dec) (hinc : k2.inconsistent = k1.inconsistent)
    (_hlen2 : k2.LengthsOk c) (hwat2 : ModeWatchesInv F_cur k2) :
    FullWitnessInv c F0 F_cur k2 := by
  have hrefs : fullArenaClauseRefsCore k2 = fullArenaClauseRefsCore k1 := by
    simp [fullArenaClauseRefsCore, har, hal]
  have hsz : ∀ r, fullArenaClauseSizeCore k2 r = fullArenaClauseSizeCore k1 r := fun r => by
    simp [fullArenaClauseSizeCore, har]
  have hgarb : ∀ r, fullArenaClauseGarbCore k2 r = fullArenaClauseGarbCore k1 r := fun r => by
    simp [fullArenaClauseGarbCore, fullArenaHdrCore, har]
  have hlits : ∀ r, fullArenaClauseLitsCore k2 r = fullArenaClauseLitsCore k1 r := fun r => by
    simp [fullArenaClauseLitsCore, hsz r, har]
  have harInv : FullArenaClausesInv c F_cur k2 :=
    { len_ok := by rw [hal]; exact hw.arena.len_ok
      refs_wf := fun r hr => by
        rw [hrefs] at hr
        simpa [har, hal, hsz r] using hw.arena.refs_wf r hr
      shrk_term := fun r hr hsh => by
        rw [hrefs] at hr
        have hsh' : (fullArenaHdrCore k1 r &&& 0x00800000#32) ≠ 0#32 := by
          simpa [fullArenaHdrCore, har] using hsh
        obtain ⟨t, ht1, ht2, hs⟩ := hw.arena.shrk_term r hr hsh'
        exact ⟨t, by simpa [hsz r] using ht1, by simpa [hal] using ht2, by simpa [har] using hs⟩
      lits_lt := fun r hr hg l hl => by
        rw [hrefs] at hr; rw [hgarb r] at hg; rw [hlits r] at hl; rw [hcur]
        exact hw.arena.lits_lt r hr hg l hl
      entails := fun r hr hg => by
        rw [hrefs] at hr; rw [hgarb r] at hg; rw [hlits r]
        exact hw.arena.entails r hr hg }
  refine
    ⟨by simpa only [hcur] using hw.ext_sound,
     by simpa only [hinc] using hw.inconsistent_sound,
     harInv, hwat2,
     by simpa only [hcl, hte] using hw.cur_level_le,
     fun i hi => by simpa only [htrl, hcur] using hw.trail_lits_lt i (hte ▸ hi),
     fun i j hi hj heq => hw.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj)
       (by simpa only [htrl] using heq),
     fun l hl => by simpa only [hval] using hw.vals_domain l (hcur ▸ hl),
     fun l hl => by simpa only [hval, hte, htrl] using hw.vals_true_iff l (hcur ▸ hl),
     fun l hl => by simpa only [hval, hte, htrl] using hw.vals_false_iff l (hcur ▸ hl),
     fun i hi => by simpa only [hlvl, htrl, hcl] using hw.lvl_le i (hte ▸ hi),
     fun i j hi hj h1 h2 => hw.dec_earliest i j (hte ▸ hi) (hte ▸ hj)
       (by simpa only [hlvl, htrl] using h1) (by simpa only [hlvl, htrl, hrsn] using h2),
     fun L h1 h2 => by
       simpa only [hte, hlvl, htrl] using hw.levels_inhabited L h1 (hcl ▸ h2),
     fun i hi h0 => by
       simpa only [htrl] using hw.level0_sound i (hte ▸ hi) (by simpa only [hlvl, htrl] using h0),
     fun i hi => by simpa only [htp, htrl] using hw.trail_pos_inv i (hte ▸ hi),
     fun idx hidx h0 => by
       simpa only [hrsn, htrl] using
         hw.level0_rsn_none idx (hte ▸ hidx) (by simpa only [hlvl, htrl] using h0),
     fun L hL => by simpa only [hft, hte] using hw.frame_trail_lt L (hcl ▸ hL),
     fun L1 L2 h1 h2 => by simpa only [hft] using hw.frame_trail_mono L1 L2 h1 (hcl ▸ h2),
     fun L h1 h2 i hi => by
       simpa only [hlvl, htrl] using
         hw.frame_trail_before_lt L h1 (hcl ▸ h2) i (by simpa only [hft] using hi),
     fun L h1 h2 => by simpa only [hfd, hcur] using hw.frame_dec_lt L h1 (hcl ▸ h2),
     fun idx hidx hne => by
       have hrs := hw.reason_inv idx (hte ▸ hidx) (by simpa only [htrl, hrsn] using hne)
       simpa only [htrl, hrsn, hcur, hlvl, hrefs, hgarb, hlits] using hrs,
     fun idx hidx hne hlg => by
       simpa only [htrl, hlits, hrsn] using
         hw.reason_lit_mem idx (hte ▸ hidx)
           (by simpa only [htrl, hrsn] using hne) (by simpa only [htrl, hrsn] using hlg)⟩

theorem fullWitnessInv_to_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core) :
    FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core :=
  fullWitnessInv_replace_watches hw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    { hlen with wvec_len := by simp, wlen_le := Nat.zero_le _ }
    (modeWatchesInv_empty c F_cur s hlen.cur_vars_le)

theorem fullWitnessInv_of_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.core.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hwat : ModeWatchesInv F_cur s.core) : FullWitnessInv c F0 F_cur s.core :=
  fullWitnessInv_replace_watches hnw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hlen hwat

theorem fullCoreInv_to_nw {c : FullCfg} {F0 : CNF Nat} {s : FullState} (h : FullCoreInv c F0 s) :
    FullCoreInv c F0 (withEmptyModeWatches c s) := by
  obtain ⟨F_cur, hw⟩ := h.witness
  exact ⟨⟨{ h.lengths.core_ok with wvec_len := by simp, wlen_le := Nat.zero_le _ },
    h.lengths.scratch_ok⟩, F_cur, fullWitnessInv_to_nw h.lengths.core_ok hw⟩

theorem fullCoreInv_of_nw {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hnw : FullCoreInv c F0 (withEmptyModeWatches c s)) (hlen : s.LengthsOk c)
    (hwat : ∀ F_cur, FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core →
      ModeWatchesInv F_cur s.core) : FullCoreInv c F0 s := by
  obtain ⟨F_cur, hw⟩ := hnw.witness
  exact ⟨hlen, F_cur, fullWitnessInv_of_nw hlen.core_ok hw (hwat F_cur hw)⟩

theorem fullAssign_trailExtCore {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} (hlen : st.LengthsOk c) (hw : FullWitnessInv c F0 F_cur st.core)
    {lit rsn : BitVec 32} {alvl : Nat} {flags' : List (BitVec 32)} {phases' : List (BitVec 8)}
    {unass' unfl' : BitVec 64} (hlit : lit.toNat < 2 * st.core.cur_vars)
    (hun : st.core.vals[lit.toNat]?.getD 0#8 = 0#8) (halvl : alvl = st.core.cur_level) :
    let v := lit.toNat / 2
    let rsn' := if alvl = 0 then 0xFFFFFFFF#32 else rsn
    let st' : FullState :=
      { st with
        core := { st.core with
          vals := (st.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
          flags := flags', lvl := st.core.lvl.set v (BitVec.ofNat 32 alvl)
          rsns := st.core.rsns.set v rsn', trl := st.core.trl.set st.core.trail_end lit
          trail_pos := st.core.trail_pos.set v (BitVec.ofNat 32 st.core.trail_end)
          trail_end := st.core.trail_end + 1, unassigned := unass', unflushed := unfl' }
        scratch := { st.scratch with phases := phases' } }
    TrailExtCore st.core st'.core := by
  intro v rsn' st'
  have hmv := fullInv_max_vars_lt32 c
  have hte_lt : st.core.trail_end < st.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcur_lt : alvl < 2 ^ 32 := by have := hw.cur_level_le; omega
  refine ⟨by dsimp [st']; omega, fun i hi => ?_, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · dsimp [st']; exact List.getElem?_set_ne (by omega)
  · dsimp [st']
    have hnone := (hw.vals_zero_iff hlit).mp hun
    exact List.getElem?_set_ne (Ne.symm (hnone i hi))
  · have hi_eq : i = st.core.trail_end := by dsimp [st'] at hi2; omega
    have htrl_l := hlen.core_ok.trl_len; have hlvl_l := hlen.core_ok.lvl_len
    subst hi_eq; dsimp [st']
    rw [List.getElem?_set_self (by omega), Option.getD_some,
      List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hcur_lt, halvl]

end Stage4PropInvs

section SplitWatches

structure FullSplitWatchesInv (F_cur : List (List Nat)) (st : FullCoreState)
    (not_lit off q p end_v : Nat) : Prop where
  layout : WatchStackLayout st
  off_eq : fullWatchOffCore st not_lit = off
  sz_eq : fullWatchSizeCore st not_lit = end_v - off
  sz_pos : 0 < end_v - off
  q_ge : off ≤ q
  q_le_p : q ≤ p
  p_le_end : p ≤ end_v
  other_slices : ∀ l < 2 * st.cur_vars, l ≠ not_lit →
    WatchSliceOk F_cur st l (fullWatchOffCore st l) (fullWatchSizeCore st l)
  kept_slice : WatchSliceOk F_cur st not_lit off (q - off)
  rem_slice : WatchSliceOk F_cur st not_lit p (end_v - p)

theorem FullSplitWatchesInv.init {F_cur : List (List Nat)} {k : FullCoreState} {not_lit : Nat}
    (hnot_lt : not_lit < 2 * k.cur_vars) (hwat : WatchesInv F_cur k)
    (hpos : 0 < fullWatchSizeCore k not_lit) :
    FullSplitWatchesInv F_cur k not_lit (fullWatchOffCore k not_lit)
      (fullWatchOffCore k not_lit) (fullWatchOffCore k not_lit)
      (fullWatchOffCore k not_lit + fullWatchSizeCore k not_lit) :=
  { layout := hwat.layout, off_eq := rfl, sz_eq := by omega, sz_pos := by omega
    q_ge := Nat.le_refl _, q_le_p := Nat.le_refl _, p_le_end := by omega
    other_slices := fun l hl _ => hwat.slices l hl
    kept_slice := by simp only [Nat.sub_self]; exact .empty
    rem_slice := by simpa only [Nat.add_sub_cancel_left] using hwat.slices not_lit hnot_lt }

theorem FullSplitWatchesInv.with_nonwatch {F_cur : List (List Nat)} {k k' : FullCoreState}
    {not_lit off q p end_v : Nat} (h : FullSplitWatchesInv F_cur k not_lit off q p end_v)
    (hvars : k'.cur_vars = k.cur_vars) (hwv : k'.wvec = k.wvec) (hws : k'.wstk = k.wstk)
    (hwl : k'.wlen = k.wlen)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k') :
    FullSplitWatchesInv F_cur k' not_lit off q p end_v := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) :=
    by rw [CNF.entails_def]; exact fun _ hx => hx
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l :=
    fun l => by unfold fullWatchOffCore; rw [hwv]
  have hwsz : ∀ l, fullWatchSizeCore k' l = fullWatchSizeCore k l :=
    fun l => by unfold fullWatchSizeCore; rw [hwv]
  refine
    { layout := h.layout.with_wstk hvars hwv hws hwl
      off_eq := by rw [hwo]; exact h.off_eq
      sz_eq := by rw [hwsz]; exact h.sz_eq
      sz_pos := h.sz_pos, q_ge := h.q_ge, q_le_p := h.q_le_p, p_le_end := h.p_le_end
      other_slices := fun l hl hne => by
        rw [hwo, hwsz]
        exact (h.other_slices l (hvars ▸ hl) hne).mono hF (by omega) hsub
          fun _ _ _ => by rw [hws]
      kept_slice := h.kept_slice.mono hF (by omega) hsub fun _ _ _ => by rw [hws]
      rem_slice := h.rem_slice.mono hF (by omega) hsub fun _ _ _ => by rw [hws] }

theorem FullSplitWatchesInv.write_bin {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p end_v : Nat} {w0 : BitVec 32}
    (h : FullSplitWatchesInv F_cur k not_lit off q (p + 1) end_v)
    (hnot_lt : not_lit < 2 * k.cur_vars) (hqp : q ≤ p) (hq_lt : q < k.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [not_lit, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hmax : k.cur_vars ≤ c.max_vars) :
    FullSplitWatchesInv F_cur { k with wstk := k.wstk.set q w0 } not_lit off (q + 1)
      (p + 1) end_v := by
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hne_ff : w0 ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hlt
    have hmask : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 0x7FFFFFFF := by decide
    omega
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) :=
    by rw [CNF.entails_def]; exact fun _ hx => hx
  let k' : FullCoreState := { k with wstk := k.wstk.set q w0 }
  have hq_range : off ≤ q ∧ q < end_v := ⟨h.q_ge, by have := h.p_le_end; omega⟩
  refine
    { layout :=
        { bounds := h.layout.bounds
          pos_off := h.layout.pos_off
          disjoint := h.layout.disjoint
          no_sentinel := fun l hl idx hidx => by
            change (k.wstk.set q w0)[fullWatchOffCore k l + idx]? ≠ some 0xFFFFFFFF#32
            by_cases he : fullWatchOffCore k l + idx = q
            · rw [he, List.getElem?_set_self hq_lt]; simp [hne_ff]
            · rw [List.getElem?_set_ne (Ne.symm he)]; exact h.layout.no_sentinel l hl idx hidx }
      off_eq := h.off_eq, sz_eq := h.sz_eq, sz_pos := h.sz_pos
      q_ge := by omega, q_le_p := by omega, p_le_end := h.p_le_end
      other_slices := fun l hl hne => by
        change WatchSliceOk F_cur k' l (fullWatchOffCore k l) (fullWatchSizeCore k l)
        by_cases hsz0 : fullWatchSizeCore k l = 0
        · rw [hsz0]; exact .empty
        · have hdisj := h.layout.disjoint l not_lit hl hnot_lt hne (by omega)
            (by rw [h.sz_eq]; exact h.sz_pos)
          rw [h.off_eq, h.sz_eq] at hdisj
          exact WatchSliceOk.mono (k := k) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
            (fun idx h1 h2 => by
              change fullWatchOffCore k l ≤ idx at h1
              change idx < fullWatchOffCore k l + fullWatchSizeCore k l at h2
              exact List.getElem?_set_ne (by omega))
            (h.other_slices l hl hne)
      kept_slice := by
        have hsub : q + 1 - off = (q - off) + 1 := by have := h.q_ge; omega
        rw [hsub]
        refine watchSlice_append_bin (k := k) (k' := k') (p' := off) (Nat.le_refl _)
          (fun _ hr => hr) (fun idx hk => List.getElem?_set_ne (by omega))
          h.kept_slice ?_ hflag hne_ff hlt hent
        have hadd : off + (q - off) = q := by have := h.q_ge; omega
        rw [hadd]; exact List.getElem?_set_self hq_lt
      rem_slice := WatchSliceOk.mono (k := k) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
        (fun idx h1 _ => List.getElem?_set_ne (by omega)) h.rem_slice }

theorem FullSplitWatchesInv.write_large {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p end_v : Nat} {w0 cref : BitVec 32}
    (h : FullSplitWatchesInv F_cur k not_lit off q (p + 2) end_v)
    (hnot_lt : not_lit < 2 * k.cur_vars) (hqp : q ≤ p)
    (hq_lt : q < k.wstk.length) (hq1_lt : q + 1 < k.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefsCore k) :
    FullSplitWatchesInv F_cur { k with wstk := (k.wstk.set q w0).set (q + 1) cref }
      not_lit off (q + 2) (p + 2) end_v := by
  have hne_w0 : w0 ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hflag; exact absurd hflag (by decide)
  have hne_cr : cref ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hlt
    have : (0xFFFFFFFF#32).toNat = 0xFFFFFFFF := by decide
    omega
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) :=
    by rw [CNF.entails_def]; exact fun _ hx => hx
  let k' : FullCoreState := { k with wstk := (k.wstk.set q w0).set (q + 1) cref }
  have hq_range : off ≤ q ∧ q + 1 < end_v := ⟨h.q_ge, by have := h.p_le_end; omega⟩
  refine
    { layout :=
        { bounds := h.layout.bounds
          pos_off := h.layout.pos_off
          disjoint := h.layout.disjoint
          no_sentinel := fun l hl idx hidx => by
            change ((k.wstk.set q w0).set (q + 1) cref)[fullWatchOffCore k l + idx]? ≠
              some 0xFFFFFFFF#32
            by_cases h1 : fullWatchOffCore k l + idx = q + 1
            · rw [h1, List.getElem?_set_self (by simp; exact hq1_lt)]; simp [hne_cr]
            · rw [List.getElem?_set_ne (Ne.symm h1)]
              by_cases h0 : fullWatchOffCore k l + idx = q
              · rw [h0, List.getElem?_set_self hq_lt]; simp [hne_w0]
              · rw [List.getElem?_set_ne (Ne.symm h0)]; exact h.layout.no_sentinel l hl idx hidx }
      off_eq := h.off_eq, sz_eq := h.sz_eq, sz_pos := h.sz_pos
      q_ge := by omega, q_le_p := by omega, p_le_end := h.p_le_end
      other_slices := fun l hl hne => by
        change WatchSliceOk F_cur k' l (fullWatchOffCore k l) (fullWatchSizeCore k l)
        by_cases hsz0 : fullWatchSizeCore k l = 0
        · rw [hsz0]; exact .empty
        · have hdisj := h.layout.disjoint l not_lit hl hnot_lt hne (by omega)
            (by rw [h.sz_eq]; exact h.sz_pos)
          rw [h.off_eq, h.sz_eq] at hdisj
          exact WatchSliceOk.mono (k := k) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
            (fun idx h1 h2 => by
              change fullWatchOffCore k l ≤ idx at h1
              change idx < fullWatchOffCore k l + fullWatchSizeCore k l at h2
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
            (h.other_slices l hl hne)
      kept_slice := by
        have hsub : q + 2 - off = (q - off) + 2 := by have := h.q_ge; omega
        rw [hsub]
        refine watchSlice_append_large (k := k) (k' := k') (p' := off) (Nat.le_refl _)
          (fun _ hr => hr)
          (fun idx hk => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
          h.kept_slice ?_ ?_ hflag hlt href
        · have hadd : off + (q - off) = q := by have := h.q_ge; omega
          rw [hadd, List.getElem?_set_ne (by omega)]; exact List.getElem?_set_self hq_lt
        · have hadd : off + (q - off) + 1 = q + 1 := by have := h.q_ge; omega
          rw [hadd]; exact List.getElem?_set_self (by simp; exact hq1_lt)
      rem_slice := WatchSliceOk.mono (k := k) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
        (fun idx h1 _ => by
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
        h.rem_slice }

theorem FullSplitWatchesInv.after_push {F_cur : List (List Nat)} {k k' : FullCoreState}
    {not_lit repl off q p end_v : Nat} {w0 cref : BitVec 32} {pok : Bool}
    (h : FullSplitWatchesInv F_cur k not_lit off q p end_v) (hvars : k'.cur_vars = k.cur_vars)
    (hnot_lt : not_lit < 2 * k.cur_vars) (hrepl_lt : repl < 2 * k.cur_vars) (hne : repl ≠ not_lit)
    (href_eq : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k)
    (hlay' : WatchStackLayout k')
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefsCore k)
    (hpres_other : ∀ l < 2 * k.cur_vars, l ≠ repl →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hpok_t : pok = true →
      fullWatchSizeCore k' repl = fullWatchSizeCore k repl + 2 ∧
      (∀ idx < fullWatchSizeCore k repl,
        k'.wstk[fullWatchOffCore k' repl + idx]? = k.wstk[fullWatchOffCore k repl + idx]?) ∧
      k'.wstk[fullWatchOffCore k' repl + fullWatchSizeCore k repl]? = some w0 ∧
      k'.wstk[fullWatchOffCore k' repl + fullWatchSizeCore k repl + 1]? = some cref)
    (hpok_f : pok = false →
      fullWatchSizeCore k' repl = fullWatchSizeCore k repl ∧
      ∀ idx < fullWatchSizeCore k repl,
        k'.wstk[fullWatchOffCore k' repl + idx]? = k.wstk[fullWatchOffCore k repl + idx]?) :
    let off' := fullWatchOffCore k' not_lit
    FullSplitWatchesInv F_cur k' not_lit off' (off' + (q - off)) (off' + (p - off))
      (off' + (end_v - off)) := by
  intro off'
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) :=
    by rw [CNF.entails_def]; exact fun _ hx => hx
  have hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k' :=
    fun _ hr => href_eq ▸ hr
  obtain ⟨hsz_not, hget_not⟩ := hpres_other not_lit hnot_lt (Ne.symm hne)
  rw [h.off_eq, h.sz_eq] at hget_not
  refine
    { layout := hlay', off_eq := rfl
      sz_eq := by rw [hsz_not, h.sz_eq]; omega
      sz_pos := by have := h.sz_pos; omega
      q_ge := by omega
      q_le_p := by have := h.q_ge; have := h.q_le_p; omega
      p_le_end := by have := h.q_ge; have := h.q_le_p; have := h.p_le_end; omega
      other_slices := fun l hl hln => by
        have hl0 : l < 2 * k.cur_vars := by omega
        by_cases hlr : l = repl
        · subst hlr
          cases pok with
          | false =>
            obtain ⟨hsz_r, hget_r⟩ := hpok_f rfl
            rw [hsz_r]
            exact watchSlice_relocate hF (by omega) hsub hget_r (h.other_slices l hl0 hln)
          | true =>
            obtain ⟨hsz_r, hget_r, hw0, hcr⟩ := hpok_t rfl
            rw [hsz_r]
            exact watchSlice_append_large (by omega) hsub hget_r (h.other_slices l hl0 hln) hw0 hcr
              hflag hlt (hsub _ href)
        · obtain ⟨hsz_l, hget_l⟩ := hpres_other l hl0 hlr
          rw [hsz_l]
          exact watchSlice_relocate hF (by omega) hsub hget_l (h.other_slices l hl0 hln)
      kept_slice := by
        rw [show off' + (q - off) - off' = q - off by omega]
        refine watchSlice_relocate hF (by omega) hsub (fun idx hk => ?_) h.kept_slice
        exact hget_not idx (by have := h.q_le_p; have := h.p_le_end; omega)
      rem_slice := by
        have hrem_len : off' + (end_v - off) - (off' + (p - off)) = end_v - p := by
          have := h.q_ge; have := h.q_le_p; have := h.p_le_end; omega
        rw [hrem_len]
        refine watchSlice_relocate hF (by omega) hsub (fun idx hk => ?_) h.rem_slice
        have hk' := hget_not ((p - off) + idx) (by have := h.q_ge; have := h.q_le_p; omega)
        have h1 : off' + (p - off + idx) = off' + (p - off) + idx := by omega
        have h2 : off + (p - off + idx) = p + idx := by have := h.q_ge; have := h.q_le_p; omega
        rwa [h1, h2] at hk' }

theorem FullSplitWatchesInv.finish {c : FullCfg} {F_cur : List (List Nat)} {k0 : FullCoreState}
    {not_lit off q0 p0 end_v : Nat} {wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (h : FullSplitWatchesInv F_cur k0 not_lit off q0 p0 end_v)
    (hnot_lt : not_lit < 2 * k0.cur_vars) (hcv_le : k0.cur_vars ≤ c.max_vars)
    (hwv_len : k0.wvec.length = 4 * c.max_vars) (hwcap : c.wcap < 2 * dimacsBound)
    (hwlen_le : k0.wlen ≤ c.wcap)
    (hkeep_pre : ∀ k, off ≤ k → k < q0 → wstk'[k]? = k0.wstk[k]?)
    (hkeep_suf : ∀ k < end_v - p0, wstk'[q0 + k]? = k0.wstk[p0 + k]?)
    (hkeep_out : ∀ k, (k < off ∨ end_v ≤ k) → wstk'[k]? = k0.wstk[k]?) :
    let q_fin := q0 + (end_v - p0)
    let k' : FullCoreState :=
      { k0 with
        wstk := wstk'
        wvec := k0.wvec.set (2 * not_lit + 1) (BitVec.ofNat 32 (q_fin - off))
        wusable := wu' }
    WatchesInv F_cur k' := by
  intro q_fin k'
  unfold dimacsBound at hwcap
  have hnot_bd : off + (end_v - off) ≤ k0.wlen := by
    have := h.layout.bounds not_lit hnot_lt; rwa [h.off_eq, h.sz_eq] at this
  have hqfin_le : q_fin ≤ end_v := by
    dsimp only [q_fin]; have := h.q_le_p; have := h.p_le_end; omega
  have hsz_lt32 : q_fin - off < 2 ^ 32 := by omega
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k0 l := fun l => by
    unfold fullWatchOffCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_ne : ∀ l, l ≠ not_lit → fullWatchSizeCore k' l = fullWatchSizeCore k0 l :=
    fun l hne => by unfold fullWatchSizeCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_not : fullWatchSizeCore k' not_lit = q_fin - off := by
    unfold fullWatchSizeCore; dsimp only [k']
    rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hsz_lt32]
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) :=
    by rw [CNF.entails_def]; exact fun _ hx => hx
  have hslice_not : WatchSliceOk F_cur k' not_lit off (q_fin - off) := by
    have hpre : WatchSliceOk F_cur k' not_lit off (q0 - off) :=
      WatchSliceOk.mono (k := k0) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
        (fun idx hk1 hk2 => hkeep_pre idx hk1 (by have := h.q_ge; omega)) h.kept_slice
    have hsuf : WatchSliceOk F_cur k' not_lit q0 (end_v - p0) :=
      watchSlice_relocate (k := k0) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
        hkeep_suf h.rem_slice
    have hsum : q_fin - off = (q0 - off) + (end_v - p0) := by
      dsimp only [q_fin]; have := h.q_ge; omega
    have hadd : off + (q0 - off) = q0 := by have := h.q_ge; omega
    rw [hsum]; exact watchSlice_append hpre (hadd.symm ▸ hsuf)
  have hslice_all :
      ∀ l < 2 * k'.cur_vars,
        WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l) := by
    intro l hl
    by_cases hln : l = not_lit
    · subst hln; rw [hwo, h.off_eq, hwsz_not]; exact hslice_not
    · rw [hwo, hwsz_ne l hln]
      by_cases hsz0 : fullWatchSizeCore k0 l = 0
      · rw [hsz0]; exact .empty
      · have hdisj := h.layout.disjoint l not_lit hl hnot_lt hln (by omega)
          (by rw [h.sz_eq]; exact h.sz_pos)
        rw [h.off_eq, h.sz_eq] at hdisj
        exact WatchSliceOk.mono (k := k0) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
          (fun idx hk1 hk2 => hkeep_out idx (by omega)) (h.other_slices l hl hln)
  have hbounds :
      ∀ l < 2 * k'.cur_vars, fullWatchOffCore k' l + fullWatchSizeCore k' l ≤ k'.wlen := by
    intro l hl
    by_cases hln : l = not_lit
    · subst hln; rw [hwo, h.off_eq, hwsz_not]; dsimp only [k']; omega
    · rw [hwo, hwsz_ne l hln]; exact h.layout.bounds l hl
  refine WatchesInv.of_slices hbounds (fun l hl hp => ?_) (fun l1 l2 h1 h2 hne hp1 hp2 => ?_)
    hslice_all
  · rw [hwo]
    by_cases hln : l = not_lit
    · subst hln; exact h.layout.pos_off l hl (by rw [h.sz_eq]; exact h.sz_pos)
    · exact h.layout.pos_off l hl (by rwa [← hwsz_ne l hln])
  · rw [hwo, hwo]
    by_cases h1n : l1 = not_lit
    · subst h1n; rw [h.off_eq, hwsz_not, hwsz_ne l2 (Ne.symm hne)]
      have hd := h.layout.disjoint l1 l2 h1 h2 hne (by rw [h.sz_eq]; exact h.sz_pos)
        (by rwa [← hwsz_ne l2 (Ne.symm hne)])
      rw [h.off_eq, h.sz_eq] at hd; omega
    · by_cases h2n : l2 = not_lit
      · subst h2n; rw [h.off_eq, hwsz_not, hwsz_ne l1 h1n]
        have hd := h.layout.disjoint l1 l2 h1 h2 hne (by rwa [← hwsz_ne l1 h1n])
          (by rw [h.sz_eq]; exact h.sz_pos)
        rw [h.off_eq, h.sz_eq] at hd; omega
      · rw [hwsz_ne l1 h1n, hwsz_ne l2 h2n]
        exact h.layout.disjoint l1 l2 h1 h2 hne (by rwa [← hwsz_ne l1 h1n])
          (by rwa [← hwsz_ne l2 h2n])

theorem FullSplitWatchesInv.advance_rem {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p p' end_v : Nat}
    (h : FullSplitWatchesInv F_cur k not_lit off q p end_v) (hqp' : q ≤ p') (hp' : p' ≤ end_v)
    (hrem' : WatchSliceOk F_cur k not_lit p' (end_v - p')) :
    FullSplitWatchesInv F_cur k not_lit off q p' end_v :=
  { h with q_le_p := hqp', p_le_end := hp', rem_slice := hrem' }

end SplitWatches

section ProbePropHelpers

theorem unitAssignLvl_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} (hlen : st.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c st).core)
    {other rsn : BitVec 32} {alvl : BitVec 32} {not_lit : Nat}
    {flags' : List (BitVec 32)} {phases' : List (BitVec 8)} {unass' unfl' : BitVec 64}
    (hother_lt : other.toNat < 2 * st.core.cur_vars)
    (hfll : flags'.length = c.max_vars) (hph : phases'.length = c.max_vars)
    (hun : st.core.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_lt : not_lit < 2 * st.core.cur_vars)
    (hnot_false : st.core.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (halvl_pos : 0 < alvl.toNat) (halvl_le : alvl.toNat ≤ st.core.cur_level)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32)
    (hrsn :
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * st.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [other.toNat, ot]) ∧
        ∃ k < st.core.trail_end, (st.core.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (st.core.lvl[ot / 2]?.getD 0#32).toNat ≤ alvl.toNat
      else
        rsn.toNat ∈ fullArenaClauseRefsCore st.core ∧
        fullArenaClauseGarbCore st.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore st.core rsn.toNat,
          q = other.toNat ∨ ∃ k < st.core.trail_end, (st.core.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
            (st.core.lvl[q / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hrsn_mem : (rsn &&& 0x80000000#32) = 0#32 →
      other.toNat ∈ fullArenaClauseLitsCore st.core rsn.toNat) :
    let v := other.toNat / 2
    let st' : FullState :=
      { st with
        core := { st.core with
          vals := (st.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
          flags := flags', lvl := st.core.lvl.set v alvl
          rsns := st.core.rsns.set v rsn, trl := st.core.trl.set st.core.trail_end other
          trail_pos := st.core.trail_pos.set v (BitVec.ofNat 32 st.core.trail_end)
          trail_end := st.core.trail_end + 1, unassigned := unass', unflushed := unfl' }
        scratch := { st.scratch with phases := phases' } }
    FullWitnessInv c F0 F_cur (withEmptyModeWatches c st').core ∧
    st'.core.vals[not_lit]?.getD 0#8 = 0xFF#8 := by
  intro v st'
  have hcl := hlen.core_ok
  have hte_lt : st.core.trail_end < st.core.cur_vars :=
    hw.trail_end_lt_of_unassigned hother_lt hun
  have hnot_var : ∀ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hother_lt).mp hun
  have hnlit_lt : (other.toNat ^^^ 1) < 2 * st.core.cur_vars := litNeg_lt_two_mul hother_lt
  have hne_lit : other.toNat ^^^ 1 ≠ other.toNat := litNeg_ne_self other.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : st.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_lt32 : st.core.trail_end < 2 ^ 32 := by
    have := fullInv_max_vars_lt32 c; omega
  have hcv' : (withEmptyModeWatches c st').core.cur_vars = st.core.cur_vars := rfl
  have hte' : (withEmptyModeWatches c st').core.trail_end = st.core.trail_end + 1 := rfl
  have hclv' : (withEmptyModeWatches c st').core.cur_level = st.core.cur_level := rfl
  have hnw_te : (withEmptyModeWatches c st).core.trail_end = st.core.trail_end := rfl
  have hnw_cv : (withEmptyModeWatches c st).core.cur_vars = st.core.cur_vars := rfl
  have hnw_cl : (withEmptyModeWatches c st).core.cur_level = st.core.cur_level := rfl
  have hnw_trl : (withEmptyModeWatches c st).core.trl = st.core.trl := rfl
  have hnw_lvl : (withEmptyModeWatches c st).core.lvl = st.core.lvl := rfl
  have htrl_get : ∀ i < st.core.trail_end + 1,
      ((withEmptyModeWatches c st').core.trl[i]?.getD 0#32).toNat =
        if i = st.core.trail_end then other.toNat else (st.core.trl[i]?.getD 0#32).toNat :=
    fun i _ => by
      by_cases he : i = st.core.trail_end
      · subst he; simp [st', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
      · simp [st', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < st.core.cur_vars,
      ((withEmptyModeWatches c st').core.lvl[w]?.getD 0#32).toNat =
        if w = v then alvl.toNat else (st.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [st', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt)]
    · simp [st', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * st.core.cur_vars,
      (withEmptyModeWatches c st').core.vals[l]?.getD 0#8 =
        if l = other.toNat ^^^ 1 then 0xFF#8 else if l = other.toNat then 1#8
        else st.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = other.toNat ^^^ 1
    · subst h1; simp only [st', ↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · simp only [st', h1, ↓reduceIte]
      rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = other.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < st.core.cur_vars,
      (withEmptyModeWatches c st').core.rsns[w]?.getD 0xFFFFFFFF#32 =
        if w = v then rsn else st.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [st', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [st', he, List.getElem?_set_ne (Ne.symm he)]
  have hwat' : ModeWatchesInv F_cur (withEmptyModeWatches c st').core :=
    modeWatchesInv_empty c F_cur st' hcl.cur_vars_le
  have hnw_cur_lvl : (withEmptyModeWatches c st).core.cur_level ≤ st.core.trail_end :=
    hw.cur_level_le
  have hw_trl_lt :
      ∀ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat < 2 * st.core.cur_vars :=
    hw.trail_lits_lt
  have hw_nodup : ∀ i j, i < st.core.trail_end → j < st.core.trail_end →
      (st.core.trl[i]?.getD 0#32).toNat / 2 = (st.core.trl[j]?.getD 0#32).toNat / 2 → i = j :=
    hw.trail_vars_nodup
  have hw_vtrue : ∀ l < 2 * st.core.cur_vars,
      st.core.vals[l]?.getD 0#8 = 1#8 ↔
        ∃ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat = l :=
    hw.vals_true_iff
  have hw_vfalse : ∀ l < 2 * st.core.cur_vars,
      st.core.vals[l]?.getD 0#8 = 0xFF#8 ↔
        ∃ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat = l ^^^ 1 :=
    hw.vals_false_iff
  have hw_lvl_le : ∀ i < st.core.trail_end,
      (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ st.core.cur_level :=
    hw.lvl_le
  have hw_dec_e : ∀ i j, i < st.core.trail_end → j < st.core.trail_end →
      (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      (st.core.lvl[(st.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
      (0 < (st.core.lvl[(st.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
        st.core.rsns[(st.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) →
      j ≤ i := hw.dec_earliest
  have hw_lvl0_snd : ∀ i < st.core.trail_end,
      (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(st.core.trl[i]?.getD 0#32).toNat]) :=
    hw.level0_sound
  have hw_lvl0_rsn : ∀ idx < st.core.trail_end,
      (st.core.lvl[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
      st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        0xFFFFFFFF#32 :=
    hw.level0_rsn_none
  have hw' : FullWitnessInv c F0 F_cur (withEmptyModeWatches c st').core := by
    refine ⟨hw.ext_sound, hw.inconsistent_sound,
      { hw.arena with len_ok := hw.arena.len_ok }, hwat', by rw [hclv', hte']; omega,
      fun i hi => by
        rw [hte'] at hi; rw [hcv', htrl_get i hi]; split
        · exact hother_lt
        · exact hw_trl_lt i (by omega),
      fun i j hi hj hveq => by
        rw [hte'] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
        split at hveq <;> split at hveq
        · omega
        · exact absurd hveq.symm (hnot_var j (by omega))
        · exact absurd hveq (hnot_var i (by omega))
        · exact hw_nodup i j (by omega) (by omega) hveq,
      fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl]
        split; · exact Or.inr (Or.inr rfl)
        split; · exact Or.inr (Or.inl rfl)
        exact hw.vals_domain l hl,
      fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte']; constructor
        · intro h1
          by_cases hn : l = other.toNat ^^^ 1
          · simp [hn] at h1
          · simp only [hn, ↓reduceIte] at h1
            by_cases hp : l = other.toNat
            · exact ⟨st.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hp]⟩
            · simp only [hp, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw_vtrue l hl).mp h1
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ st.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = st.core.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
            have h1 : l ≠ other.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ other.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw_vtrue l hl).mpr ⟨i, by omega, heq⟩,
      fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte']; constructor
        · intro h1
          by_cases hn : l = other.toNat ^^^ 1
          · exact ⟨st.core.trail_end, by omega, by
              rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hn]
              exact (litNeg_litNeg _).symm⟩
          · simp only [hn, ↓reduceIte] at h1
            by_cases hp : l = other.toNat
            · simp [hp] at h1
            · simp only [hp, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw_vfalse l hl).mp h1
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ st.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = st.core.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have hl_eq : l = other.toNat ^^^ 1 := by
              have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
              rw [h1] at h; exact h.symm
            simp [hl_eq]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
            have h1 : l ≠ other.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ other.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw_vfalse l hl).mpr ⟨i, by omega, heq⟩,
      fun i hi => by
        rw [hte'] at hi; rw [hclv', htrl_get i hi]
        by_cases hie : i = st.core.trail_end
        · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp [halvl_le]
        · have hilt : i < st.core.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hlvl_get _ (by have := hw_trl_lt i hilt; omega)]
          simp only [hnot_var i hilt, ↓reduceIte]; exact hw_lvl_le i hilt,
      fun i j hi hj hleq hdec => by
        rw [hte'] at hi hj; rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
        by_cases hje : j = st.core.trail_end
        · subst hje; simp only [↓reduceIte] at hdec
          rw [hrsn_get v (by omega)] at hdec; exact absurd hdec.2 (by simp [hrsn_ne])
        · by_cases hie : i = st.core.trail_end
          · omega
          · have hilt : i < st.core.trail_end := by omega
            have hjlt : j < st.core.trail_end := by omega
            simp only [hie, hje, ↓reduceIte] at hleq hdec
            rw [hlvl_get _ (by have := hw_trl_lt i hilt; omega),
              hlvl_get _ (by have := hw_trl_lt j hjlt; omega)] at hleq
            rw [hlvl_get _ (by have := hw_trl_lt j hjlt; omega),
              hrsn_get _ (by have := hw_trl_lt j hjlt; omega)] at hdec
            simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
            exact hw_dec_e i j hilt hjlt hleq hdec,
      fun L hL1 hLle => by
        rw [hclv'] at hLle; obtain ⟨i, hi, hli⟩ := hw.levels_inhabited L hL1 hLle
        rw [hnw_te] at hi
        refine ⟨i, by rw [hte']; omega, ?_⟩
        rw [htrl_get i (by omega)]; simp only [show i ≠ st.core.trail_end by omega, ↓reduceIte]
        rw [hlvl_get _ (by have := hw_trl_lt i hi; exact Nat.div_lt_of_lt_mul this)]
        simp [hnot_var i hi, hli],
      fun i hi hli => by
        rw [hte'] at hi; rw [htrl_get i hi] at hli ⊢
        by_cases hie : i = st.core.trail_end
        · simp only [hie, ↓reduceIte] at hli
          rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli; omega
        · have hilt : i < st.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get _ (by have := hw_trl_lt i hilt; omega)] at hli
          simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hw_lvl0_snd i hilt hli,
      fun i hi => by
        rw [hte'] at hi; rw [htrl_get i hi]
        by_cases hie : i = st.core.trail_end
        · subst hie; simp only [↓reduceIte, st']
          rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < st.core.trail_end := by omega
          simp only [hie, ↓reduceIte, st']
          rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]; exact hw.trail_pos_inv i hilt,
      fun idx hidx hli => by
        rw [hte'] at hidx; rw [htrl_get idx hidx] at hli ⊢
        by_cases hie : idx = st.core.trail_end
        · simp only [hie, ↓reduceIte] at hli
          rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli; omega
        · have hilt : idx < st.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢
          have hnv := hnot_var idx hilt
          rw [hlvl_get _ (by have := hw_trl_lt idx hilt; omega)] at hli
          simp only [hnv, ↓reduceIte] at hli
          rw [hrsn_get _ (by have := hw_trl_lt idx hilt; omega)]
          simp only [hnv, ↓reduceIte]; exact hw_lvl0_rsn idx hilt hli,
      fun L hL => by
        rw [hclv'] at hL
        have := hw.frame_trail_lt L hL
        rw [hnw_te] at this
        rw [hte']; exact Nat.le_trans this (Nat.le_succ _),
      hw.frame_trail_mono,
      fun L hL1 hLle i hi => by
        rw [hclv'] at hLle
        have hlt_te : i < st.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle)
        rw [htrl_get i (by omega)]; simp only [show i ≠ st.core.trail_end by omega, ↓reduceIte]
        rw [hlvl_get _ (by have := hw_trl_lt i hlt_te; omega)]
        simp only [hnot_var i hlt_te, ↓reduceIte]; exact hw.frame_trail_before_lt L hL1 hLle i hi,
      hw.frame_dec_lt,
      fun idx hidx hne => by
        rw [hte'] at hidx; rw [htrl_get idx hidx] at hne ⊢
        by_cases hie : idx = st.core.trail_end
        · simp only [hie, ↓reduceIte] at hne ⊢
          rw [hrsn_get v (by omega)] at hne ⊢; simp only [↓reduceIte] at hne ⊢
          by_cases hb : (rsn &&& 0x80000000#32) ≠ 0#32
          · rw [ite_eq_left hb] at hrsn ⊢
            obtain ⟨hot_lt, hent, m, hm, hmeq, hlvl_le⟩ := hrsn
            refine ⟨hot_lt, hent, m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ st.core.trail_end by omega, hmeq]
            · have hot_v : (rsn &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
                intro heqv; have hme := hnot_var m hm; rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get v (by omega), hlvl_get _ (by omega)]
              rw [ite_eq_left rfl, ite_eq_right hot_v]; exact hlvl_le
          · rw [ite_eq_right hb] at hrsn ⊢
            refine ⟨hrsn.1, hrsn.2.1, fun q hq => ?_⟩
            have hq' : q ∈ fullArenaClauseLitsCore st.core rsn.toNat := by
              simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, st',
                withEmptyModeWatches] using hq
            refine (hrsn.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ⟨m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ st.core.trail_end by omega, hmeq]
            · have hq_lt : q < 2 * st.core.cur_vars :=
                hw.arena.lits_lt _ hrsn.1 hrsn.2.1 q hq'
              have hqv : q / 2 ≠ v := by
                intro heqv; have hme := hnot_var m hm; rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get v (by omega), hlvl_get _ (by omega)]; simpa [hqv] using hlvl_le
        · have hilt : idx < st.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hne ⊢; have hnv := hnot_var idx hilt
          rw [hrsn_get _ (by have := hw_trl_lt idx hilt; omega)] at hne ⊢
          simp only [hnv, ↓reduceIte] at hne ⊢
          have hrs := hw.reason_inv idx hilt hne
          by_cases hb : (st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
          · rw [ite_eq_left hb] at hrs ⊢
            obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
            refine ⟨hrs.1, hrs.2.1, m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ st.core.trail_end by omega, hmeq]
            · have hot_v : ((st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
                intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get _ (by exact Nat.div_lt_of_lt_mul (by rw [← hnw_cv]; exact hrs.1)),
                hlvl_get _ (by have := hw_trl_lt idx hilt; omega)]
              rw [ite_eq_right hot_v, ite_eq_right hnv]; exact hlvl_le
          · rw [ite_eq_right hb] at hrs ⊢
            refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
            have hq' : q ∈ fullArenaClauseLitsCore st.core
                (st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32).toNat := by
              simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, st',
                withEmptyModeWatches] using hq
            refine (hrs.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ⟨m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ st.core.trail_end by omega, hmeq]
            · have hq_lt : q < 2 * st.core.cur_vars :=
                hw.arena.lits_lt _ hrs.1 hrs.2.1 q hq'
              have hqv : q / 2 ≠ v := by
                intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get _ (by omega), hlvl_get _ (by have := hw_trl_lt idx hilt; omega)]
              simpa [hnv, hqv] using hlvl_le,
      fun idx hidx hne hlg => by
        rw [hte'] at hidx; rw [htrl_get idx hidx] at hne hlg ⊢
        by_cases hie : idx = st.core.trail_end
        · simp only [hie, ↓reduceIte] at hne hlg ⊢
          rw [hrsn_get v (by omega)] at hne hlg ⊢; simp only [↓reduceIte] at hne hlg ⊢
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, st',
            withEmptyModeWatches] using hrsn_mem hlg
        · have hilt : idx < st.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hne hlg ⊢; have hnv := hnot_var idx hilt
          rw [hrsn_get _ (by have := hw_trl_lt idx hilt; omega)] at hne hlg ⊢
          simp only [hnv, ↓reduceIte] at hne hlg ⊢
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, st',
            withEmptyModeWatches] using hw.reason_lit_mem idx hilt hne hlg⟩
  refine ⟨hw', ?_⟩
  obtain ⟨i, hi, heq⟩ := (hw_vfalse not_lit hnot_lt).mp hnot_false
  refine (hw'.vals_false_iff not_lit hnot_lt).mpr ⟨i, by rw [hte']; omega, ?_⟩
  rw [htrl_get i (by omega)]; simp [show i ≠ st.core.trail_end by omega, heq]

private theorem list_count_set {α : Type} [DecidableEq α] (xs : List α) (i : Nat) (v a : α)
    (hi : i < xs.length) :
    (xs.set i v).count a + (if xs[i] == a then 1 else 0) =
      xs.count a + (if v == a then 1 else 0) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [List.set, List.count_cons]; omega
    | succ i =>
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ]
      have := ih i (by simpa using hi); omega

private theorem list_swap_perm {α : Type} [DecidableEq α] (xs : List α) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Perm xs := by
  rw [List.perm_iff_count]
  intro a
  have h1 := list_count_set xs i xs[j] a hi
  have h2 := list_count_set (xs.set i xs[j]) j xs[i] a (by simpa using hj)
  by_cases hij : i = j
  · subst hij; simp only [List.getElem_set_self (by simpa using hj)] at h2; omega
  · simp only [List.getElem_set_ne hij] at h2; omega

theorem arena_swap_preserves_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    {cref k1 k2 : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefs s)
    (hk1 : k1 < fullArenaClauseSize s cref) (hk2 : k2 < fullArenaClauseSize s cref) :
    have hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length := by
      have h1 : cref + 3 + fullArenaClauseSize s cref ≤
          fullArenaNextOff s.core.arena s.core.arena_len cref := (hw.arena.refs_wf cref hcref).2.2.1
      have h2 : fullArenaNextOff s.core.arena s.core.arena_len cref ≤ s.core.arena_len :=
        (hw.arena.refs_wf cref hcref).2.2.2.1
      have h3 := hlen.core_ok.arena_len_le
      have h4 := hlen.core_ok.arena_len_arr
      omega
    let l1 := s.core.arena[cref + 3 + k1]'(by omega)
    let l2 := s.core.arena[cref + 3 + k2]'(by omega)
    let arena' := ((s.core.arena.set (cref + 1) srch).set (cref + 3 + k1) l2).set (cref + 3 + k2) l1
    let s' : FullState := { s with core := { s.core with arena := arena' } }
    FullWitnessInv c F0 F_cur (withEmptyModeWatches c s').core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      (fullArenaClauseLits s' r).Perm (fullArenaClauseLits s r)) := by
  intro hbd l1 l2 arena' s'
  have hcl := hlen.core_ok
  have hw_refs : ∀ r ∈ fullArenaClauseRefs s,
      r + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSize s r ∧
      r + 3 + fullArenaClauseSize s r ≤ fullArenaNextOff s.core.arena s.core.arena_len r ∧
      fullArenaNextOff s.core.arena s.core.arena_len r ≤ s.core.arena_len ∧
      (fullArenaNextOff s.core.arena s.core.arena_len r = s.core.arena_len ∨
        fullArenaNextOff s.core.arena s.core.arena_len r + 3 ≤ s.core.arena_len) :=
    fun r hr => hw.arena.refs_wf r hr
  have hw_disj : ∀ r1 r2, r1 ∈ fullArenaClauseRefs s → r2 ∈ fullArenaClauseRefs s →
      r1 < r2 → fullArenaNextOff s.core.arena s.core.arena_len r1 ≤ r2 :=
    fun _ _ h1 h2 hlt => fullArenaScanRefs_disjoint h1 h2 hlt
  have hwf_cref := hw_refs cref hcref
  have har_set0 : arena'[cref]? = s.core.arena[cref]? := by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har_set2 : arena'[cref + 2]? = s.core.arena[cref + 2]? := by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har_out : ∀ i, (i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i) →
      arena'[i]? = s.core.arena[i]? := fun i hi => by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    refine fullArenaClauseRefsCore_congr rfl fun r hr => ?_
    by_cases hrc : r = cref
    · subst hrc
      exact fullArenaNextOff_congr_block har_set0 har_set2
        fun k hk1' _ => har_out k (Or.inr hk1')
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj := hw_disj r cref hr hcref hlt
        have hr_bd := hw_refs r hr
        exact fullArenaNextOff_congr_block (har_out r (Or.inl (by omega)))
          (har_out (r + 2) (Or.inl (by omega))) fun k _ hk2' => har_out k (Or.inl (by omega))
      · have hdisj := hw_disj cref r hcref hr hgt
        have hcd := hwf_cref.2.2.1
        exact fullArenaNextOff_congr_block (har_out r (Or.inr (by omega)))
          (har_out (r + 2) (Or.inr (by omega))) fun k _ _ => har_out k (Or.inr (by omega))
  have hout : ∀ r ∈ fullArenaClauseRefs s, r ≠ cref →
      fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref ∨
      cref + 3 + fullArenaClauseSize s cref ≤ r :=
    fun r hr hne => (Nat.lt_or_gt_of_ne hne).elim
      (fun h => Or.inl (hw_disj r cref hr hcref h))
      (fun h => Or.inr (by
        have := hw_disj cref r hcref hr h
        have := hwf_cref.2.2.1; omega))
  have hsz_eq : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r := fun r hr => by
    unfold fullArenaClauseSize fullArenaClauseSizeCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst hrc; rw [har_set2]
    · rcases hout r hr hrc with hlt | hgt
      · have h3 := (hw_refs r hr).2.1; have h4 := (hw_refs r hr).2.2.1
        rw [har_out (r + 2) (Or.inl (by omega))]
      · rw [har_out (r + 2) (Or.inr (by omega))]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r := fun r hr => by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst hrc; rw [har_set0]
    · rcases hout r hr hrc with hlt | hgt
      · have := (hw_refs r hr).1; have := (hw_refs r hr).2.1; have := (hw_refs r hr).2.2.1
        rw [har_out r (Or.inl (by omega))]
      · rw [har_out r (Or.inr hgt)]
  have hlits_perm : ∀ r ∈ fullArenaClauseRefs s,
      (fullArenaClauseLits s' r).Perm (fullArenaClauseLits s r) := fun r hr => by
    have hbd_r : r + 3 + fullArenaClauseSize s r ≤ s.core.arena.length := by
      have h1 := (hw_refs r hr).2.2.1
      have h2 := (hw_refs r hr).2.2.2.1
      have h3 := hcl.arena_len_le; have h4 := hcl.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst hrc
      have hlist_set : ∀ (xs : List (BitVec 32)) (i : Nat) (v : BitVec 32)
          (hi : r + 3 ≤ i) (hi2 : i < r + 3 + fullArenaClauseSize s r)
          (hxl : r + 3 + fullArenaClauseSize s r ≤ xs.length),
          ((xs.set i v).drop (r + 3)).take (fullArenaClauseSize s r) =
            (((xs.drop (r + 3)).take (fullArenaClauseSize s r)).set (i - (r + 3)) v) := by
        intro xs i v hi1 hi2 hxl
        apply List.ext_getElem
        · simp [List.length_take, List.length_drop]
        · intro j hj1 _
          simp only [List.length_take, List.length_drop] at hj1
          have hj : j < fullArenaClauseSize s r := by omega
          rw [List.getElem_take, List.getElem_drop, List.getElem_set]
          by_cases he : i = r + 3 + j
          · simp [he]
          · rw [ite_eq_right (by omega), List.getElem_set_ne (by omega)]
            simp [List.getElem_take, List.getElem_drop]
      have hstep0 :
          (((s.core.arena.set (r + 1) srch).drop (r + 3)).take (fullArenaClauseSize s r)) =
            (s.core.arena.drop (r + 3)).take (fullArenaClauseSize s r) := by
        apply List.ext_getElem
        · simp [List.length_take, List.length_drop]
        · intro j hj1 _
          simp only [List.length_take, List.length_drop] at hj1
          have hj : j < fullArenaClauseSize s r := by omega
          simp [List.getElem_take, List.getElem_drop,
            List.getElem_set_ne (by omega : r + 1 ≠ r + 3 + j)]
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      rw [show fullArenaClauseSizeCore s'.core r = fullArenaClauseSize s' r from rfl,
        hsz_eq r hr]; dsimp only [s', arena']
      rw [hlist_set _ (r + 3 + k2) l1 (by omega) (by omega) (by simp; omega)]
      rw [hlist_set _ (r + 3 + k1) l2 (by omega) (by omega) (by simp; omega)]
      rw [hstep0]
      have hlen_sub : ((s.core.arena.drop (r + 3)).take (fullArenaClauseSize s r)).length =
          fullArenaClauseSize s r := by
        rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
      have hl1_eq : l1 = ((s.core.arena.drop (r + 3)).take (fullArenaClauseSize s r))[k1]'(
          by omega) := by simp [l1, List.getElem_take, List.getElem_drop]
      have hl2_eq : l2 = ((s.core.arena.drop (r + 3)).take (fullArenaClauseSize s r))[k2]'(
          by omega) := by simp [l2, List.getElem_take, List.getElem_drop]
      have hk1' : r + 3 + k1 - (r + 3) = k1 := by omega
      have hk2' : r + 3 + k2 - (r + 3) = k2 := by omega
      rw [hk1', hk2', hl1_eq, hl2_eq]
      exact (list_swap_perm ((s.core.arena.drop (r + 3)).take (fullArenaClauseSize s r))
        k1 k2 (by omega) (by omega)).map BitVec.toNat
    · have hhold : ∀ j < fullArenaClauseSize s r,
          s'.core.arena[r + 3 + j]? = s.core.arena[r + 3 + j]? :=
        fun j hj => by
          rcases hout r hr hrc with hlt | hgt
          · have := (hw_refs r hr).2.2.1; exact har_out (r + 3 + j) (Or.inl (by omega))
          · exact har_out (r + 3 + j) (Or.inr (by omega))
      have heq := fullArenaClauseLitsCore_eq_of_hold hbd_r (by simp [s', arena', hbd_r])
        (hsz_eq r hr) hhold
      change fullArenaClauseLits s' r = fullArenaClauseLits s r at heq
      rw [heq]
  have hmem_iff : ∀ r ∈ fullArenaClauseRefs s,
      ∀ l, l ∈ fullArenaClauseLits s' r ↔ l ∈ fullArenaClauseLits s r :=
    fun r hr l => (hlits_perm r hr).mem_iff
  have hnxt : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
      fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst hrc
      exact fullArenaNextOff_congr_block har_set0 har_set2 fun k hk1' _ => har_out k (Or.inr hk1')
    · rcases hout r hr hrc with hlt | hgt
      · have hr_bd := hw_refs r hr
        exact fullArenaNextOff_congr_block (har_out r (Or.inl (by omega)))
          (har_out (r + 2) (Or.inl (by omega))) fun k _ hk2' => har_out k (Or.inl (by omega))
      · exact fullArenaNextOff_congr_block (har_out r (Or.inr hgt))
          (har_out (r + 2) (Or.inr (by omega))) fun k _ _ => har_out k (Or.inr (by omega))
  have harena' : FullArenaClausesInv c F_cur (withEmptyModeWatches c s').core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; have hr0 : r ∈ fullArenaClauseRefs s := hrefs ▸ hr
      have hwf := hw_refs r hr0
      change _ ∧ _ ∧ _ ∧ _ ∧ _
      rw [show (withEmptyModeWatches c s').core.arena = arena' from rfl,
        hnxt r hr0, show fullArenaClauseSizeCore (withEmptyModeWatches c s').core r =
          fullArenaClauseSize s' r from rfl, hsz_eq r hr0]
      exact hwf
    · intro r hr hsh; have hr0 : r ∈ fullArenaClauseRefs s := hrefs ▸ hr
      have hsh0 :
          (fullArenaHdrCore (withEmptyModeWatches c s).core r &&& 0x00800000#32) ≠ 0#32 := by
        unfold fullArenaHdrCore at hsh ⊢
        by_cases hrc : r = cref
        · subst hrc; rwa [show (withEmptyModeWatches c s').core.arena[r]? = arena'[r]? from rfl,
            har_set0] at hsh
        · rcases hout r hr0 hrc with hlt | hgt
          · have := (hw_refs r hr0).1; have := (hw_refs r hr0).2.1
            have := (hw_refs r hr0).2.2.1
            rwa [show (withEmptyModeWatches c s').core.arena[r]? = arena'[r]? from rfl,
              har_out r (Or.inl (by omega))] at hsh
          · rwa [show (withEmptyModeWatches c s').core.arena[r]? = arena'[r]? from rfl,
              har_out r (Or.inr hgt)] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr0 hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore (withEmptyModeWatches c s).core r) :=
        by
          have hr3 := (hw_refs r hr0).1
          have : r < s.core.arena.length := by
            have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
          unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      have hsh_ar : (s.core.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, ht0_al, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw_refs r hr0).1 hsh_ar ht1 ht2 hsent
      have ht_out : t0 < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ t0 := by
        by_cases hrc : r = cref
        · subst hrc; right; exact ht0_lo
        · rcases hout r hr0 hrc with hlt | hgt
          · left; omega
          · right; omega
      have hsz_t0 : fullArenaClauseSize s' r = fullArenaClauseSize s r := hsz_eq r hr0
      refine ⟨t0, ?_, Nat.lt_of_le_of_lt ht0_al ht2, ?_⟩
      · show r + 3 + fullArenaClauseSize s' r ≤ t0
        rw [hsz_t0]; exact ht0_lo
      · change arena'[t0]? = some 0xFFFFFFFF#32; rw [har_out t0 ht_out]; exact ht0_sent
    · intro r hr hng l hl; have hr0 : r ∈ fullArenaClauseRefs s := hrefs ▸ hr
      rw [show fullArenaClauseGarbCore (withEmptyModeWatches c s').core r =
        fullArenaClauseGarb s' r from rfl, hgarb_eq r hr0] at hng
      rw [show fullArenaClauseLitsCore (withEmptyModeWatches c s').core r =
        fullArenaClauseLits s' r from rfl, hmem_iff r hr0 l] at hl
      exact hw.arena.lits_lt r hr0 hng l hl
    · intro r hr hng; have hr0 : r ∈ fullArenaClauseRefs s := hrefs ▸ hr
      rw [show fullArenaClauseGarbCore (withEmptyModeWatches c s').core r =
        fullArenaClauseGarb s' r from rfl, hgarb_eq r hr0] at hng
      have hent0 := hw.arena.entails r hr0 hng
      rw [CNF.entails_clause_def] at hent0 ⊢
      intro α hα
      obtain ⟨l, hl1, hl2⟩ := (clause_sat_cnfClause_iff α _).mp (hent0 α hα)
      exact (clause_sat_cnfClause_iff α _).mpr ⟨l, (hmem_iff r hr0 l).mpr hl1, hl2⟩
  refine ⟨{ hw with
    arena := harena'
    watches := modeWatchesInv_empty c F_cur s' hcl.cur_vars_le
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne
      by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        have hr0 : _ ∈ fullArenaClauseRefs s := hrs.1
        have hrf' : _ ∈ fullArenaClauseRefs s' := hrefs ▸ hr0
        refine ⟨hrf', (hgarb_eq _ hr0).trans hrs.2.1, fun q hq => ?_⟩
        exact hrs.2.2 q ((hmem_iff _ hr0 q).mp hq)
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      exact (hmem_iff _ hrs.1 _).mpr (hw.reason_lit_mem idx hidx hne hlg) },
    hrefs, fun r hr => ⟨hsz_eq r hr, hgarb_eq r hr, hlits_perm r hr⟩⟩

theorem arena_setSrch_preserves_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    {cref : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefs s) :
    let s' : FullState :=
      { s with core := { s.core with arena := s.core.arena.set (cref + 1) srch } }
    FullWitnessInv c F0 F_cur (withEmptyModeWatches c s').core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      (fullArenaClauseLits s' r).Perm (fullArenaClauseLits s r)) := by
  have h3 : 3 ≤ fullArenaClauseSize s cref := (hw.arena.refs_wf cref hcref).2.1
  have hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length := by
    have h1 : cref + 3 + fullArenaClauseSize s cref ≤
        fullArenaNextOff s.core.arena s.core.arena_len cref := (hw.arena.refs_wf cref hcref).2.2.1
    have h2 : fullArenaNextOff s.core.arena s.core.arena_len cref ≤ s.core.arena_len :=
      (hw.arena.refs_wf cref hcref).2.2.2.1
    have h4 := hlen.core_ok.arena_len_le; have h5 := hlen.core_ok.arena_len_arr; omega
  have hsw := arena_swap_preserves_nw hlen hw (cref := cref) (k1 := 0) (k2 := 0) (srch := srch)
    hcref (by omega) (by omega)
  have heq_ar : ((s.core.arena.set (cref + 1) srch).set (cref + 3 + 0)
      (s.core.arena[cref + 3 + 0]'(by omega))).set (cref + 3 + 0)
      (s.core.arena[cref + 3 + 0]'(by omega)) = s.core.arena.set (cref + 1) srch := by
    apply List.ext_getElem (by simp)
    intro i hi _
    by_cases h1 : i = cref + 3 + 0
    · subst h1; simp [List.getElem_set_ne (by omega : cref + 1 ≠ cref + 3 + 0)]
    · rw [List.getElem_set_ne (Ne.symm h1), List.getElem_set_ne (Ne.symm h1)]
  simpa only [heq_ar] using hsw

theorem arena_swapLits_preserves_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    {cref k1 k2 : Nat} (hcref : cref ∈ fullArenaClauseRefs s)
    (hk1 : k1 < fullArenaClauseSize s cref) (hk2 : k2 < fullArenaClauseSize s cref) :
    have hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length := by
      have h1 : cref + 3 + fullArenaClauseSize s cref ≤
          fullArenaNextOff s.core.arena s.core.arena_len cref := (hw.arena.refs_wf cref hcref).2.2.1
      have h2 : fullArenaNextOff s.core.arena s.core.arena_len cref ≤ s.core.arena_len :=
        (hw.arena.refs_wf cref hcref).2.2.2.1
      have h3 := hlen.core_ok.arena_len_le; have h4 := hlen.core_ok.arena_len_arr; omega
    let l1 := s.core.arena[cref + 3 + k1]'(by omega)
    let l2 := s.core.arena[cref + 3 + k2]'(by omega)
    let s' : FullState :=
      { s with core := { s.core with
        arena := (s.core.arena.set (cref + 3 + k1) l2).set (cref + 3 + k2) l1 } }
    FullWitnessInv c F0 F_cur (withEmptyModeWatches c s').core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      (fullArenaClauseLits s' r).Perm (fullArenaClauseLits s r)) := by
  intro hbd l1 l2 s'
  have h1lt : cref + 1 < s.core.arena.length := by omega
  have hsw := arena_swap_preserves_nw hlen hw (cref := cref) (k1 := k1) (k2 := k2)
    (srch := s.core.arena[cref + 1]'h1lt) hcref hk1 hk2
  have heq : s.core.arena.set (cref + 1) (s.core.arena[cref + 1]'h1lt) = s.core.arena :=
    List.set_getElem_self h1lt
  simpa only [heq] using hsw

def fullFindReplBad (st : FullState) (cref k : Nat) : Prop :=
  let cand := (st.core.arena[cref + 3 + k]?.getD 0#32).toNat
  2 * st.core.cur_vars ≤ cand ∨
  ((st.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true

theorem clause_falsified_of_find_repl_none {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} (_hlen : st.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c st).core)
    {cref not_lit other : Nat} (hcref : cref ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st cref = false)
    (hbd : cref + 3 + fullArenaClauseSize st cref ≤ st.core.arena.length)
    (hother_at : (st.core.arena[cref + 3]'(by
      have h3 : 3 ≤ fullArenaClauseSize st cref := (hw.arena.refs_wf cref hcref).2.1
      omega)).toNat = other)
    (hnot_at : (st.core.arena[cref + 4]'(by
      have h3 : 3 ≤ fullArenaClauseSize st cref := (hw.arena.refs_wf cref hcref).2.1
      omega)).toNat = not_lit)
    (hnot_false : st.core.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hfind : ∀ k, 2 ≤ k → k < fullArenaClauseSize st cref → fullFindReplBad st cref k) :
    ∀ l ∈ fullArenaClauseLits st cref, l = other ∨ st.core.vals[l]?.getD 0#8 = 0xFF#8 := by
  intro l hl
  have hbd' : cref + 3 + fullArenaClauseSizeCore st.core cref ≤ st.core.arena.length := hbd
  obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd').mp hl
  have hk' : k < fullArenaClauseSize st cref := hk
  match k with
  | 0 => exact Or.inl (by simpa using hget.symm.trans hother_at)
  | 1 =>
    have h4 : (st.core.arena[cref + 3 + 1]'(by omega)).toNat = not_lit := hnot_at
    exact Or.inr (by rw [← hget, h4]; exact hnot_false)
  | k' + 2 =>
    have hlt : l < 2 * st.core.cur_vars := hw.arena.lits_lt cref hcref hng l hl
    have hf := hfind (k' + 2) (by omega) hk'
    unfold fullFindReplBad at hf
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget] at hf
    have hslt := hf.resolve_left (by omega)
    exact Or.inr ((i8_vals_slt0 (hw.vals_domain l hlt)).mp hslt)

end ProbePropHelpers

end FullProbeTransHelpers

end LeanQbe.T.Examples.Kissat.Full
