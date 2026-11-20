module

public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas3
import all Kraken.Mem
import all Kraken.Separation

/-! # Kissat `D-Full` `full_probe_prop_lit` Split Proof Helpers (`Stage 4`, Part 4) -/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullProbeTransSpecs FullProbeTransHelpers
open scoped FullArenaTactics FullProbeTransTactics

namespace FullProbeTransHelpers

section SharedStateHelpers

private theorem modeWatchesInv_congr {F_cur : List (List Nat)} {k1 k2 : FullCoreState}
    (h1 : ModeWatchesInv F_cur k1) (hcur : k2.cur_vars = k1.cur_vars)
    (har : k2.arena = k1.arena) (hal : k2.arena_len = k1.arena_len)
    (hwv : k2.wvec = k1.wvec) (hws : k2.wstk = k1.wstk) (hwl : k2.wlen = k1.wlen)
    (hdm : k2.dense_mode = k1.dense_mode) : ModeWatchesInv F_cur k2 := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hsub : ∀ r ∈ fullArenaClauseRefsCore k1, r ∈ fullArenaClauseRefsCore k2 := fun r hr => by
    unfold fullArenaClauseRefsCore at hr ⊢; rw [har, hal]; exact hr
  unfold ModeWatchesInv at h1 ⊢; rw [hdm]
  split at h1
  · rename_i hc; rw [ite_eq_left hc]
    refine WatchesInv.of_slices
      (fun l hl => by
        have := h1.layout.bounds l (hcur ▸ hl)
        dsimp only [fullWatchOffCore, fullWatchSizeCore] at this ⊢; rwa [hwv, hwl])
      (fun l hl hp => by
        have := h1.layout.pos_off l (hcur ▸ hl)
        dsimp only [fullWatchOffCore, fullWatchSizeCore] at this hp ⊢; rw [hwv] at hp ⊢
        exact this hp)
      (fun l1 l2 h1l h2l hne hp1 hp2 => by
        have := h1.layout.disjoint l1 l2 (hcur ▸ h1l) (hcur ▸ h2l) hne
        dsimp only [fullWatchOffCore, fullWatchSizeCore] at this hp1 hp2 ⊢
        rw [hwv] at hp1 hp2 ⊢; exact this hp1 hp2)
      (fun l hl => by
        have hwo : fullWatchOffCore k2 l = fullWatchOffCore k1 l := by
          unfold fullWatchOffCore; rw [hwv]
        have hwsz : fullWatchSizeCore k2 l = fullWatchSizeCore k1 l := by
          unfold fullWatchSizeCore; rw [hwv]
        rw [hwo, hwsz]
        exact (h1.slices l (hcur ▸ hl)).mono hF (by omega) hsub fun _ _ _ => by rw [hws])
  · rename_i hc; rw [ite_eq_right hc]
    refine DenseWatchesInv.of_slices
      (fun l hl => by
        have := h1.layout.bounds l (hcur ▸ hl)
        dsimp only [fullWatchOffCore, fullWatchSizeCore] at this ⊢; rwa [hwv, hwl])
      (fun l hl hp => by
        have := h1.layout.pos_off l (hcur ▸ hl)
        dsimp only [fullWatchOffCore, fullWatchSizeCore] at this hp ⊢; rw [hwv] at hp ⊢
        exact this hp)
      (fun l1 l2 h1l h2l hne hp1 hp2 => by
        have := h1.layout.disjoint l1 l2 (hcur ▸ h1l) (hcur ▸ h2l) hne
        dsimp only [fullWatchOffCore, fullWatchSizeCore] at this hp1 hp2 ⊢
        rw [hwv] at hp1 hp2 ⊢; exact this hp1 hp2)
      (fun l hl => by
        have hwo : fullWatchOffCore k2 l = fullWatchOffCore k1 l := by
          unfold fullWatchOffCore; rw [hwv]
        have hwsz : fullWatchSizeCore k2 l = fullWatchSizeCore k1 l := by
          unfold fullWatchSizeCore; rw [hwv]
        rw [hwo, hwsz]
        exact (h1.slices l (hcur ▸ hl)).mono hF (by omega) hsub fun _ _ _ => by rw [hws])

theorem fullWitnessInv_congr_ctrl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k1 k2 : FullCoreState} (hw : FullWitnessInv c F0 F_cur k1) (hlen2 : k2.LengthsOk c)
    (hcur : k2.cur_vars = k1.cur_vars) (har : k2.arena = k1.arena)
    (hal : k2.arena_len = k1.arena_len) (hcl : k2.cur_level = k1.cur_level)
    (hte : k2.trail_end = k1.trail_end) (htrl : k2.trl = k1.trl)
    (hval : k2.vals = k1.vals) (hlvl : k2.lvl = k1.lvl) (hrsn : k2.rsns = k1.rsns)
    (htp : k2.trail_pos = k1.trail_pos) (hft : k2.frame_trail = k1.frame_trail)
    (hfd : k2.frame_dec = k1.frame_dec) (hinc : k2.inconsistent = k1.inconsistent)
    (hwv : k2.wvec = k1.wvec) (hws : k2.wstk = k1.wstk) (hwl : k2.wlen = k1.wlen)
    (hdm : k2.dense_mode = k1.dense_mode) : FullWitnessInv c F0 F_cur k2 :=
  fullWitnessInv_replace_watches hw hcur har hal hcl hte htrl hval hlvl hrsn htp hft hfd hinc
    hlen2 (modeWatchesInv_congr hw.watches hcur har hal hwv hws hwl hdm)

theorem fullWitnessInv_nw_upd_watches {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hlen' : s'.core.LengthsOk c)
    (hcur : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hcl : s'.core.cur_level = s.core.cur_level)
    (hte : s'.core.trail_end = s.core.trail_end) (htrl : s'.core.trl = s.core.trl)
    (hval : s'.core.vals = s.core.vals) (hlvl : s'.core.lvl = s.core.lvl)
    (hrsn : s'.core.rsns = s.core.rsns) (htp : s'.core.trail_pos = s.core.trail_pos)
    (hft : s'.core.frame_trail = s.core.frame_trail) (hfd : s'.core.frame_dec = s.core.frame_dec)
    (hinc : s'.core.inconsistent = s.core.inconsistent) :
    FullWitnessInv c F0 F_cur (withEmptyModeWatches c s').core :=
  fullWitnessInv_replace_watches hw hcur har hal hcl hte htrl hval hlvl hrsn htp hft hfd hinc
    { hlen' with wvec_len := by simp, wlen_le := Nat.zero_le _ }
    (modeWatchesInv_empty c F_cur s' hlen'.cur_vars_le)

theorem fullTrailRsnsExt_refl (k : FullCoreState) : FullTrailRsnsExt k k :=
  ⟨⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩, fun _ _ => rfl⟩

theorem fullTrailRsnsExt_trans {k k1 k2 : FullCoreState}
    (h1 : FullTrailRsnsExt k k1) (h2 : FullTrailRsnsExt k1 k2) : FullTrailRsnsExt k k2 := by
  refine ⟨⟨Nat.le_trans h1.1.1 h2.1.1, fun i hi => ?_, fun i hi => ?_⟩, fun i hi => ?_⟩
  · exact (h2.1.2.1 i (by have := h1.1.1; omega)).trans (h1.1.2.1 i hi)
  · have hlt1 : i < k1.trail_end := by have := h1.1.1; omega
    have htr := h1.1.2.1 i hi; have h2l := h2.1.2.2 i hlt1
    rw [htr] at h2l; exact h2l.trans (h1.1.2.2 i hi)
  · have hlt1 : i < k1.trail_end := by have := h1.1.1; omega
    have htr := h1.1.2.1 i hi; have h2r := h2.2 i hlt1
    rw [htr] at h2r; exact h2r.trans (h1.2 i hi)

theorem fullTrailRsnsExt_congr {k1 k2 : FullCoreState} (hte : k2.trail_end = k1.trail_end)
    (htrl : k2.trl = k1.trl) (hlvl : k2.lvl = k1.lvl) (hrsn : k2.rsns = k1.rsns) :
    FullTrailRsnsExt k1 k2 :=
  ⟨⟨by omega, fun i _ => by rw [htrl], fun i _ => by rw [hlvl]⟩, fun i _ => by rw [hrsn]⟩

theorem fullTrailRsnsExt_of_assign_lvl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {lit rsn alvl : BitVec 32}
    {flags' : List (BitVec 32)} {unass' unfl' : BitVec 64}
    (hlit : lit.toNat < 2 * k.cur_vars) (hun : k.vals[lit.toNat]?.getD 0#8 = 0#8) :
    let v := lit.toNat / 2
    let k' : FullCoreState :=
      { k with
        vals := (k.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn
        trl := k.trl.set k.trail_end lit
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unass', unflushed := unfl' }
    FullTrailRsnsExt k k' := by
  have hnone := (hw.vals_zero_iff hlit).mp hun
  refine ⟨⟨Nat.le_succ _, fun i hi => List.getElem?_set_ne (by omega),
    fun i hi => List.getElem?_set_ne (Ne.symm (hnone i hi))⟩,
    fun i hi => List.getElem?_set_ne (Ne.symm (hnone i hi))⟩

theorem fullHbrBufOkW_push {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hbuf : FullHbrBufOkW F_cur s s.core.tmp_cnt)
    (hlt_cv : s.core.tmp_cnt < s.core.cur_vars) {a b : BitVec 32}
    (ha : a.toNat < 2 * s.core.cur_vars) (hb : b.toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) :
    let hn := s.core.tmp_cnt
    let s' : FullState :=
      { s with
        core := { s.core with tmp_cnt := hn + 1 }
        scratch := { s.scratch with
          work_stk2 := (s.scratch.work_stk2.set (2 * hn) a).set (2 * hn + 1) b } }
    s'.LengthsOk c ∧ FullHbrBufOkW F_cur s' s'.core.tmp_cnt := by
  intro hn s'
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws2_len := hlen.scratch_ok.work_stk2_len
  have hi2 : 2 * s.core.tmp_cnt + 1 < s.scratch.work_stk2.length := by omega
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with cur_vars_le := hcv_le },
      { hlen.scratch_ok with work_stk2_len := by simp [s', hws2_len] }⟩
  refine ⟨hlen', by change hn + 1 ≤ s.core.cur_vars; omega, fun i hi => ?_⟩
  change i < hn + 1 at hi
  by_cases hie : i = hn
  · subst hie; dsimp only [s']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some,
      List.getElem?_set_self (by simp; exact hi2), Option.getD_some]
    exact ⟨ha, hb, hent⟩
  · have hi0 : i < hn := by omega
    obtain ⟨ha0, hb0, he0⟩ := hbuf.2 i hi0
    dsimp only [s']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact ⟨ha0, hb0, he0⟩

theorem fullHbrBufOkW_congr {F_cur : List (List Nat)} {s s' : FullState} {n : Nat}
    (h : FullHbrBufOkW F_cur s n) (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hws : s'.scratch.work_stk2 = s.scratch.work_stk2) : FullHbrBufOkW F_cur s' n := by
  simpa only [FullHbrBufOkW, hcv, hws] using h

end SharedStateHelpers

section PropLitProofHelpers

private theorem pt_vals_slt0_of_eq {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (heq : vals[i]'hi = 0xFF#8) : ((vals[i]'hi).signExtend 32).slt 0#32 = true := by
  rw [heq]; decide

theorem pt_vals_eq_0_of_flags {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (hdom : vals[i]?.getD 0#8 = 0#8 ∨ vals[i]?.getD 0#8 = 1#8 ∨ vals[i]?.getD 0#8 = 0xFF#8)
    (hnsgt : ¬ (0#32).slt ((vals[i]'hi).signExtend 32) = true)
    (hnslt : ¬ ((vals[i]'hi).signExtend 32).slt 0#32 = true) : vals[i]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hdom ⊢
  rcases hdom with h0 | h1 | hff <;> (first
    | exact h0 | exact absurd (by rw [h1]; decide) hnsgt | exact absurd (by rw [hff]; decide) hnslt)

theorem pt_vals_eq_ff_of_nsge {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (hdom : vals[i]?.getD 0#8 = 0#8 ∨ vals[i]?.getD 0#8 = 1#8 ∨ vals[i]?.getD 0#8 = 0xFF#8)
    (hnsge : ¬ (0#32).sle ((vals[i]'hi).signExtend 32) = true) : vals[i]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hdom ⊢
  rcases hdom with h0 | h1 | hff <;> (first
    | exact absurd (by rw [h0]; decide) hnsge | exact absurd (by rw [h1]; decide) hnsge | exact hff)

private theorem pt_vals_eq_1_of_sgt {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (hdom : vals[i]?.getD 0#8 = 0#8 ∨ vals[i]?.getD 0#8 = 1#8 ∨ vals[i]?.getD 0#8 = 0xFF#8)
    (hsgt : (0#32).slt ((vals[i]'hi).signExtend 32) = true) : vals[i]?.getD 0#8 = 1#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hdom ⊢; exact (i8_vals_sgt0 hdom).mp hsgt

theorem pt_vals_eq_ff_of_slt {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (hdom : vals[i]?.getD 0#8 = 0#8 ∨ vals[i]?.getD 0#8 = 1#8 ∨ vals[i]?.getD 0#8 = 0xFF#8)
    (hslt : ((vals[i]'hi).signExtend 32).slt 0#32 = true) : vals[i]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hdom ⊢; exact (i8_vals_slt0 hdom).mp hslt

private theorem pt_vals_ne_ff_of_slt_false {vals : List (BitVec 8)} {i : Nat}
    (hi : i < vals.length) (hv : vals[i]?.getD 0#8 = 0xFF#8) :
    ((vals[i]'hi).signExtend 32).slt 0#32 = true := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hv; rw [hv]; decide

theorem arena_swapLits_keep_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    {cref k1 k2 : Nat} (hcref : cref ∈ fullArenaClauseRefs s)
    (hk1 : k1 < fullArenaClauseSize s cref) (hk2 : k2 < fullArenaClauseSize s cref) :
    have hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length := by
      have h1 := (hw.arena.refs_wf cref hcref).2.2.1
      have h2 := (hw.arena.refs_wf cref hcref).2.2.2.1
      dsimp only [fullArenaClauseSize, withEmptyModeWatches, fullArenaClauseSizeCore] at h1 h2 ⊢
      have h3 := hlen.core_ok.arena_len_le; have h4 := hlen.core_ok.arena_len_arr; omega
    let l1 := s.core.arena[cref + 3 + k1]'(by omega)
    let l2 := s.core.arena[cref + 3 + k2]'(by omega)
    let s' : FullState :=
      { s with core := { s.core with
        arena := (s.core.arena.set (cref + 3 + k1) l2).set (cref + 3 + k2) l1 } }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyModeWatches c s').core ∧
    FullArenaVarsNodup s' ∧ FullExtScratchOk c s' ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      (fullArenaClauseLits s' r).Perm (fullArenaClauseLits s r)) := by
  intro hbd l1 l2 s'
  obtain ⟨hw', hrefs, hper⟩ := arena_swapLits_preserves_nw hlen hw hcref hk1 hk2
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with arena_len_arr := by simp [s', hlen.core_ok.arena_len_arr] },
      hlen.scratch_ok⟩
  refine ⟨hlen', hw', fullArenaVarsNodup_of_lits_perm hnd hrefs fun r hr hg =>
    ⟨(hper r hr).2.1.symm.trans hg, (hper r hr).2.2⟩,
    ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl hrefs, hext.2⟩, hrefs, hper⟩

private theorem arena_swap_keep_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    {cref k1 k2 : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefs s)
    (hk1 : k1 < fullArenaClauseSize s cref) (hk2 : k2 < fullArenaClauseSize s cref) :
    have hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length := by
      have h1 := (hw.arena.refs_wf cref hcref).2.2.1
      have h2 := (hw.arena.refs_wf cref hcref).2.2.2.1
      dsimp only [fullArenaClauseSize, withEmptyModeWatches, fullArenaClauseSizeCore] at h1 h2 ⊢
      have h3 := hlen.core_ok.arena_len_le; have h4 := hlen.core_ok.arena_len_arr; omega
    let l1 := s.core.arena[cref + 3 + k1]'(by omega)
    let l2 := s.core.arena[cref + 3 + k2]'(by omega)
    let arena' := ((s.core.arena.set (cref + 1) srch).set (cref + 3 + k1) l2).set (cref + 3 + k2) l1
    let s' : FullState := { s with core := { s.core with arena := arena' } }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyModeWatches c s').core ∧
    FullArenaVarsNodup s' ∧ FullExtScratchOk c s' ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      (fullArenaClauseLits s' r).Perm (fullArenaClauseLits s r)) := by
  intro hbd l1 l2 arena' s'
  obtain ⟨hw', hrefs, hper⟩ := arena_swap_preserves_nw hlen hw hcref hk1 hk2 (srch := srch)
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with arena_len_arr := by simp [s', arena', hlen.core_ok.arena_len_arr] },
      hlen.scratch_ok⟩
  refine ⟨hlen', hw', fullArenaVarsNodup_of_lits_perm hnd hrefs fun r hr hg =>
    ⟨(hper r hr).2.1.symm.trans hg, (hper r hr).2.2⟩,
    ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl hrefs, hext.2⟩, hrefs, hper⟩

private theorem arena_setSrch_keep_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    {cref : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefs s) :
    let s' : FullState :=
      { s with core := { s.core with arena := s.core.arena.set (cref + 1) srch } }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyModeWatches c s').core ∧
    FullArenaVarsNodup s' ∧ FullExtScratchOk c s' ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  obtain ⟨hw', hrefs, hper⟩ := arena_setSrch_preserves_nw hlen hw hcref (srch := srch)
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with arena_len_arr := by simp [s', hlen.core_ok.arena_len_arr] },
      hlen.scratch_ok⟩
  exact ⟨hlen', hw', fullArenaVarsNodup_of_lits_perm hnd hrefs fun r hr hg =>
    ⟨(hper r hr).2.1.symm.trans hg, (hper r hr).2.2⟩,
    ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl hrefs, hext.2⟩, hrefs⟩

private theorem propLit_tail_inv_upd_wstk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {not_lit off q0 p0 end_v : Nat} {wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen : st.LengthsOk c)
    (hw_nw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c st).core)
    (hsplit : FullSplitWatchesInv F_cur st.core not_lit off q0 p0 end_v)
    (hnot_lt : not_lit < 2 * st.core.cur_vars)
    (hwsl : wstk'.length = c.wcap)
    (hkeep_pre : ∀ k, off ≤ k → k < q0 → wstk'[k]? = st.core.wstk[k]?)
    (hkeep_suf : ∀ k < end_v - p0, wstk'[q0 + k]? = st.core.wstk[p0 + k]?)
    (hkeep_out : ∀ k, (k < off ∨ end_v ≤ k) → wstk'[k]? = st.core.wstk[k]?)
    (hmrk0 : FullMrkZero c st) (hnd : FullArenaVarsNodup st) (hext : FullExtScratchOk c st)
    (hdm : st.core.dense_mode = 0#64) (hcl1 : st.core.cur_level = 1)
    (hcv : st.core.cur_vars = s0.core.cur_vars) (hfu : st.core.fuel = s0.core.fuel)
    (hlm : st.core.lit_mark = s0.core.lit_mark) (hws1 : st.scratch.work_stk1 = s0.scratch.work_stk1)
    (htr : FullTrailRsnsExt s0.core st.core) (hhbr : FullHbrBufOkW F_cur st st.core.tmp_cnt) :
    let q_fin := q0 + (end_v - p0)
    let st' : FullState :=
      { st with core := { st.core with
        wstk := wstk'
        wvec := st.core.wvec.set (2 * not_lit + 1) (BitVec.ofNat 32 (q_fin - off))
        wusable := wu' } }
    st'.LengthsOk c ∧ FullWitnessInv c F0 F_cur st'.core ∧ FullMrkZero c st' ∧
    FullArenaVarsNodup st' ∧ FullExtScratchOk c st' ∧ st'.core.dense_mode = 0#64 ∧
    st'.core.cur_level = 1 ∧ st'.core.cur_vars = s0.core.cur_vars ∧ st'.core.fuel = s0.core.fuel ∧
    st'.core.lit_mark = s0.core.lit_mark ∧ st'.scratch.work_stk1 = s0.scratch.work_stk1 ∧
    FullTrailRsnsExt s0.core st'.core ∧ FullHbrBufOkW F_cur st' st'.core.tmp_cnt := by
  intro q_fin st'
  have hcl := hlen.core_ok
  have hwat' : WatchesInv F_cur st'.core :=
    hsplit.finish hnot_lt hcl.cur_vars_le hcl.wvec_len c.hwcap hcl.wlen_le hkeep_pre hkeep_suf
      hkeep_out
  have hlen' : st'.LengthsOk c := ⟨{ hcl with
    wvec_len := by simp [st', hcl.wvec_len], wstk_len_arr := by simp [st', hwsl] },
    hlen.scratch_ok⟩
  have hmwat' : ModeWatchesInv F_cur st'.core := by
    unfold ModeWatchesInv; rw [ite_eq_left (by simp [st', hdm])]; exact hwat'
  have hw_nw' : FullWitnessInv c F0 F_cur (withEmptyModeWatches c st').core :=
    fullWitnessInv_nw_upd_watches hw_nw hlen'.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl
  have hw' := fullWitnessInv_of_nw hlen'.core_ok hw_nw' hmwat'
  refine ⟨hlen', hw', hmrk0, fullArenaVarsNodup_of_arena_eq hnd rfl rfl, ?_, hdm, hcl1, hcv, hfu,
    hlm, hws1, htr, hhbr⟩
  refine ⟨fun i hi => by
    simpa [FullLastLearnedWf, fullArenaClauseRefs, fullArenaClauseRefsCore] using hext.1 i hi,
    hext.2⟩

def propLitTailInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (not_lit : BitVec 32) :
    Tup Val [i64, i64, i64, i64, Ty.bool] → Mem 64 → Prop :=
  fun (off_v, p_v, q_v, end_v, confl_v, ()) ml =>
    ∃ st : FullState,
      st.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyModeWatches c st).core ∧
      FullMrkZero c st ∧ FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
      st.core.dense_mode = 0#64 ∧ st.core.cur_level = 1 ∧
      st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
      st.core.lit_mark = s.core.lit_mark ∧ st.scratch.work_stk1 = s.scratch.work_stk1 ∧
      FullTrailRsnsExt s.core st.core ∧ FullHbrBufOkW F_cur st st.core.tmp_cnt ∧
      FullSplitWatchesInv F_cur st.core not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
        end_v.toNat ∧
      (confl_v = true → st.core.oom ≠ 0#64 ∨ FullConflictOkW F_cur st) ∧
      (confl_v = false → st.core.oom = 0#64 ∧ p_v = end_v) ∧
      (FullMem c st ⋆ R) ml

theorem propLitTail_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {not_lit : BitVec 32} (hnot_lt : not_lit.toNat < 2 * s.core.cur_vars)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 1 → s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.lit_mark = s.core.lit_mark → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      FullTrailRsnsExt s.core s'.core → FullHbrBufOkW F_cur s' s'.core.tmp_cnt →
      (ok = false → s'.core.oom ≠ 0#64 ∨ FullConflictOkW F_cur s') →
      (ok = true → s'.core.oom = 0#64) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    {h_arg pWvec pWstk : Val i64} {n_arg : Val i32}
    (hh : h_arg = c.hdr) (hwv : pWvec = c.pWvec) (hws : pWstk = c.pWstk)
    (hn : n_arg = not_lit)
    {off_v p_v q_v end_v : Val i64} {confl_v : Val .bool} {ml : Mem 64}
    (htail : propLitTailInv c F0 F_cur s R not_lit (off_v, p_v, q_v, end_v, confl_v, ()) ml) :
    wp Γ Q X
      (Expr.group (sig := [[i64, i64]]) (fun Js => Blocks.cons (fun p_36 =>
        Expr.let_ ⟨.cmp .ult i64, (.var p_36.fst, .var end_v, ())⟩ fun p_37 =>
        Expr.jnz (.var p_37.fst)
          (Expr.let_ ⟨.mul i64, (.var p_36.snd.fst, .imm 4, ())⟩ fun p =>
           Expr.let_ ⟨.add i64, (.var pWstk, .var p.fst, ())⟩ fun p =>
           Expr.let_ ⟨.mul i64, (.var p_36.fst, .imm 4, ())⟩ fun p_38 =>
           Expr.let_ ⟨.add i64, (.var pWstk, .var p_38.fst, ())⟩ fun p_39 =>
           Expr.load i32 (.var p_39.fst) fun ld =>
           Expr.store (.var ld) (.var p.fst)
             (Expr.let_ ⟨.add i64, (.var p_36.snd.fst, .imm 1, ())⟩ fun p =>
              Expr.let_ ⟨.add i64, (.var p_36.fst, .imm 1, ())⟩ fun p_40 =>
              Expr.jump Js.fst (.var p_40.fst, .var p.fst, ())))
          (Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p_38 =>
            Expr.let_ ⟨.cmp .ult i64, (.var p_38.fst, .var end_v, ())⟩ fun p_39 =>
            Expr.jnz (.var p_39.fst)
              (Expr.let_ ⟨.mul i64, (.var p_38.fst, .imm 4, ())⟩ fun p =>
               Expr.let_ ⟨.add i64, (.var pWstk, .var p.fst, ())⟩ fun p =>
               Expr.store (t := i32) (.imm 4294967295) (.var p.fst)
                 (Expr.let_ ⟨.add i64, (.var p_38.fst, .imm 1, ())⟩ fun p =>
                  Expr.jump Js.fst (.var p.fst, ())))
              (Expr.let_ ⟨.zext 32 64, (.var n_arg, ())⟩ fun p_40 =>
               Expr.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_41 =>
               Expr.let_ ⟨.shl i64, (.var p_40.fst, .var p_41.fst, ())⟩ fun p_42 =>
               Expr.let_ ⟨.add i64, (.var p_42.fst, .imm 1, ())⟩ fun p_43 =>
               Expr.let_ ⟨.mul i64, (.var p_43.fst, .imm 4, ())⟩ fun p_44 =>
               Expr.let_ ⟨.add i64, (.var pWvec, .var p_44.fst, ())⟩ fun p_45 =>
               Expr.let_ ⟨.sub i64, (.var p_36.snd.fst, .var off_v, ())⟩ fun p_46 =>
               Expr.let_ ⟨.trunc 64 32, (.var p_46.fst, ())⟩ fun p_47 =>
               Expr.store (.var p_47.fst) (.var p_45.fst)
                 (Expr.let_ ⟨.add i64, (.var h_arg, .imm 464, ())⟩ fun p_48 =>
                  Expr.load i64 (.var p_48.fst) fun ld =>
                  Expr.let_ ⟨.sub i64, (.var end_v, .var p_36.snd.fst, ())⟩ fun p_49 =>
                  Expr.let_ ⟨.add i64, (.var ld, .var p_49.fst, ())⟩ fun p_50 =>
                  Expr.let_ ⟨.add i64, (.var h_arg, .imm 464, ())⟩ fun p_51 =>
                  Expr.store (.var p_50.fst) (.var p_51.fst)
                    (Expr.let_ ⟨.not .bool, (.var confl_v, ())⟩ fun p_52 =>
                     Expr.ret (.var p_52.fst, ()))))) .nil)
            fun Js => Expr.jump Js.fst (.var p_36.snd.fst, ()))) .nil)
        fun Js => Expr.jump Js.fst (.var p_v, .var q_v, ())) ml := by
  subst hh hwv hws; subst n_arg
  rcases htail with ⟨st, hlen, hw_nw, hmrk0, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1, htr, hhbr,
    hsplit, hconfl_t, hconfl_f, hml⟩
  have hcl := hlen.core_ok
  have hnot_lt' : not_lit.toNat < 2 * st.core.cur_vars := hcv ▸ hnot_lt
  have hend_le : end_v.toNat ≤ st.core.wstk.length := by
    have := hsplit.layout.bounds not_lit.toNat hnot_lt'
    rw [hsplit.off_eq, hsplit.sz_eq] at this
    have := hcl.wlen_le; have := hcl.wstk_len_arr; omega
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hcl.cur_vars_le
  have hq_ge := hsplit.q_ge
  have hqp := hsplit.q_le_p
  have hpe := hsplit.p_le_end
  refine wp_loop_inv
    (fun (pt, qt, ()) m1 => ∃ wstk1,
      q_v.toNat ≤ qt.toNat ∧ qt.toNat ≤ pt.toNat ∧ p_v.toNat ≤ pt.toNat ∧ pt.toNat ≤ end_v.toNat ∧
      qt.toNat - q_v.toNat = pt.toNat - p_v.toNat ∧
      (∀ k, (k < q_v.toNat ∨ pt.toNat ≤ k) → wstk1[k]? = st.core.wstk[k]?) ∧
      (∀ k < qt.toNat - q_v.toNat, wstk1[q_v.toNat + k]? = st.core.wstk[p_v.toNat + k]?) ∧
      wstk1.length = c.wcap ∧
      (FullMem c { st with core := { st.core with wstk := wstk1 } } ⋆ R) m1)
    (fun (pt, _qt, ()) _ => end_v.toNat - pt.toNat)
    (fun J1 hL1 => ?_)
    (fun J1 (pt, qt, ()) m1
      ⟨wstk1, hqt_q, hqt_pt, hpt_p, hpt_e, hdiff, hk_out, hk_suf, hwlen1, hm1⟩ hL1 => ?_)
  · pt_steps_nogrp
    exact hL1 (p_v, q_v, ()) ml ⟨st.core.wstk, Nat.le_refl _, hqp, Nat.le_refl _, hpe, by omega,
      fun _ _ => rfl, fun _ hk => by omega, hcl.wstk_len_arr, hml⟩
  · pt_steps_nogrp
    · have hpt_lt : pt.toNat < end_v.toNat := by pt_bound
      have hqt_lt : qt.toNat < c.wcap := by
        have := hcl.wstk_len_arr; omega
      have hpt_lt' : pt.toNat < c.wcap := by
        have := hcl.wstk_len_arr; omega
      have hpt1 : pt.toNat + 1 < 2 ^ 64 := by
        have := c.hwcap; unfold dimacsBound at this; omega
      have hqt1 : qt.toNat + 1 < 2 ^ 64 := by omega
      pt_steps_nogrp
      refine hL1 (pt + 1#64, qt + 1#64, ()) m
        (by dsimp only; rw [bv64_add1_toNat hpt1]; omega)
        ⟨wstk1.set qt.toNat (wstk1[pt.toNat]'(hwlen1 ▸ hpt_lt')),
          by rw [bv64_add1_toNat hqt1]; omega,
          by rw [bv64_add1_toNat hqt1, bv64_add1_toNat hpt1]; omega,
          by rw [bv64_add1_toNat hpt1]; omega,
          by rw [bv64_add1_toNat hpt1]; omega,
          by rw [bv64_add1_toNat hqt1, bv64_add1_toNat hpt1]; omega,
          fun k hk => by
            rw [bv64_add1_toNat hpt1] at hk
            rw [List.getElem?_set_ne (by omega)]
            exact hk_out k (by rcases hk with h | h; exact Or.inl h; exact Or.inr (by omega)),
          fun k hk => by
            rw [bv64_add1_toNat hqt1] at hk
            by_cases hke : k = qt.toNat - q_v.toNat
            · subst hke
              have hqadd : q_v.toNat + (qt.toNat - q_v.toNat) = qt.toNat := by omega
              rw [hqadd, List.getElem?_set_self (hwlen1 ▸ hqt_lt)]
              have hpadd : p_v.toNat + (qt.toNat - q_v.toNat) = pt.toNat := by omega
              rw [hpadd]
              have hpout := hk_out pt.toNat (Or.inr (Nat.le_refl _))
              rw [← hpout, List.getElem?_eq_getElem (by omega)]
            · rw [List.getElem?_set_ne (by omega)]
              exact hk_suf k (by omega),
          by simp [hwlen1], hm⟩
    · have hpt_eq : pt = end_v := BitVec.eq_of_toNat_eq (by pt_bound)
      have hqt_eq : qt.toNat = q_v.toNat + (end_v.toNat - p_v.toNat) := by
        rw [hpt_eq] at hdiff hpt_e hqt_pt; omega
      refine wp_loop_inv
        (fun (k_v, ()) m2 => ∃ wstk2,
          qt.toNat ≤ k_v.toNat ∧ k_v.toNat ≤ end_v.toNat ∧
          (∀ j, (j < qt.toNat ∨ end_v.toNat ≤ j) → wstk2[j]? = wstk1[j]?) ∧
          wstk2.length = c.wcap ∧
          (FullMem c { st with core := { st.core with wstk := wstk2 } } ⋆ R) m2)
        (fun (k_v, ()) _ => end_v.toNat - k_v.toNat)
        (fun J2 hL2 => ?_)
        (fun J2 (k_v, ()) m2 ⟨wstk2, hqk, hke, hj_pres, hwlen2, hm2⟩ hL2 => ?_)
      · pt_steps_nogrp
        exact hL2 (qt, ()) m1 ⟨wstk1, Nat.le_refl _, by omega, fun _ _ => rfl, hwlen1, hm1⟩
      · pt_steps_nogrp
        · have hk_lt : k_v.toNat < end_v.toNat := by pt_bound
          have hk_cap : k_v.toNat < c.wcap := by
            have := hcl.wstk_len_arr; omega
          have hk1 : k_v.toNat + 1 < 2 ^ 64 := by
            have := c.hwcap; unfold dimacsBound at this; omega
          pt_steps_nogrp
          exact hL2 (k_v + 1#64, ()) m (by dsimp only; rw [bv64_add1_toNat hk1]; omega)
            ⟨wstk2.set k_v.toNat 0xFFFFFFFF#32,
              by rw [bv64_add1_toNat hk1]; omega,
              by rw [bv64_add1_toNat hk1]; omega,
              fun j hj => by rw [List.getElem?_set_ne (by omega)]; exact hj_pres j hj,
              by simp [hwlen2], hm⟩
        · have hnot_w1_lt : ((not_lit.setWidth 64 <<< 1) + 1#64).toNat < st.core.wvec.length := by
            rw [hcl.wvec_len, bv64_add1_toNat (by
              rw [bv64_shl1_toNat (by rw [bv_c0_zext32_64]; omega)]; rw [bv_c0_zext32_64]; omega),
              bv64_shl1_toNat (by rw [bv_c0_zext32_64]; omega), bv_c0_zext32_64]
            omega
          have hfin := propLit_tail_inv_upd_wstk hlen hw_nw hsplit hnot_lt' hwlen2
            (fun j hj1 hj2 => (hj_pres j (Or.inl (by omega))).trans (hk_out j (Or.inl (by omega))))
            (fun j hj => (hj_pres (q_v.toNat + j) (Or.inl (by omega))).trans
              (hk_suf j (by omega)))
            (fun j hj => (hj_pres j (by rcases hj with h | h; left; omega; right; exact h)).trans
              (hk_out j (by rcases hj with h | h; left; omega; right; rw [hpt_eq]; exact h)))
            hmrk0 hnd hext hdm hcl1 hcv hfu hlm hws1 htr hhbr
            (wu' := st.core.wusable + (end_v - qt))
          have hwvec_idx : ((not_lit.setWidth 64 <<< 1) + 1).toNat = 2 * not_lit.toNat + 1 := by
            have hsh : (not_lit.setWidth 64 <<< 1).toNat = 2 * not_lit.toNat := by
              rw [bv64_shl1_toNat (by rw [bv_c0_zext32_64]; omega), bv_c0_zext32_64]
            rw [show (1 : BitVec 64) = 1#64 from rfl, bv64_add1_toNat (by rw [hsh]; omega), hsh]
          have hdiff_bv : (qt - off_v).setWidth 32 = BitVec.ofNat 32 (q_v.toNat +
              (end_v.toNat - p_v.toNat) - off_v.toNat) := by
            apply BitVec.eq_of_toNat_eq
            have hsub_n : (qt - off_v).toNat = qt.toNat - off_v.toNat := by bv_omega
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hsub_n, hqt_eq]
          pt_steps_nogrp
          rw [hwvec_idx, hdiff_bv] at hm
          exact hQ (!confl_v) _ m hfin.1 hfin.2.1 hfin.2.2.1 hfin.2.2.2.1 hfin.2.2.2.2.1
            hfin.2.2.2.2.2.1 hfin.2.2.2.2.2.2.1 hfin.2.2.2.2.2.2.2.1 hfin.2.2.2.2.2.2.2.2.1
            hfin.2.2.2.2.2.2.2.2.2.1 hfin.2.2.2.2.2.2.2.2.2.2.1 hfin.2.2.2.2.2.2.2.2.2.2.2.1
            hfin.2.2.2.2.2.2.2.2.2.2.2.2
            (fun hff => hconfl_t (by cases confl_v <;> simp_all))
            (fun htr' => (hconfl_f (by cases confl_v <;> simp_all)).1) hm

private theorem bv32_msb_zero_of_lt {x : BitVec 32} (hx : x.toNat < 0x80000000) :
    (x &&& 0x80000000#32) = 0#32 := by
  have h := bv32_mask7f_msb_zero x
  have hm : x &&& 0x7FFFFFFF#32 = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  rwa [hm] at h

private theorem arena_lit_ne_of_nodup {s : FullState} {cref k1 k2 : Nat}
    (hnd : FullArenaVarsNodup s) (hcref : cref ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref = false)
    (hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length)
    (hk1 : k1 < fullArenaClauseSize s cref) (hk2 : k2 < fullArenaClauseSize s cref)
    (hne : k1 ≠ k2) :
    (s.core.arena[cref + 3 + k1]'(by omega)).toNat ≠
      (s.core.arena[cref + 3 + k2]'(by omega)).toNat := by
  have hnod := hnd cref hcref hng
  have hlen : ((fullArenaClauseLits s cref).map (· / 2)).length = fullArenaClauseSize s cref := by
    rw [List.length_map]
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    rw [List.length_map, List.length_take, List.length_drop, Nat.min_eq_left]
    change fullArenaClauseSize s cref ≤ s.core.arena.length - (cref + 3); omega
  have hpw := List.pairwise_iff_getElem.mp hnod
  have hget : ∀ k (hk : k < fullArenaClauseSize s cref),
      ((fullArenaClauseLits s cref).map (· / 2))[k]'(by omega) =
        (s.core.arena[cref + 3 + k]'(by omega)).toNat / 2 := fun k hk => by
    rw [List.getElem_map]
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp [List.getElem_take, List.getElem_drop]
  intro heq
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd ((hget k1 hk1).trans (congrArg (· / 2) heq) |>.trans (hget k2 hk2).symm)
      (hpw k1 k2 (by omega) (by omega) hlt)
  · exact absurd ((hget k2 hk2).trans (congrArg (· / 2) heq.symm) |>.trans (hget k1 hk1).symm)
      (hpw k2 k1 (by omega) (by omega) hgt)

def propLitMainInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (not_lit : BitVec 32) :
    Tup Val [i64, i64, i64, i64] → Mem 64 → Prop :=
  fun (off_v, p_v, q_v, end_v, ()) ml =>
    ∃ st : FullState,
      st.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyModeWatches c st).core ∧
      FullMrkZero c st ∧ FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
      st.core.dense_mode = 0#64 ∧ st.core.cur_level = 1 ∧
      st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
      st.core.lit_mark = s.core.lit_mark ∧ st.scratch.work_stk1 = s.scratch.work_stk1 ∧
      FullTrailRsnsExt s.core st.core ∧ FullHbrBufOkW F_cur st st.core.tmp_cnt ∧
      FullSplitWatchesInv F_cur st.core not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
        end_v.toNat ∧
      st.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧ st.core.oom = 0#64 ∧
      (FullMem c st ⋆ R) ml

def propLitLargeExpr (h_arg pVals pWvec pWstk pArena pHstk : Val i64)
    (not_lit : Val i32) (nlits_v : Val i64) (cr_v w0_v l0_v : Val i32)
    (off_v p2_v q_v end_v : Val i64) (Jtail : Cont [i64, i64, i64, i64, Ty.bool])
    (Jloop : Cont [i64, i64, i64, i64]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ ⟨.zext 32 64, (.var l0_v, ())⟩ fun p_77 =>
  Expr.let_ ⟨.cmp .uge i64, (.var p_77.fst, .var nlits_v, ())⟩ fun p_78 =>
  Expr.jnz (.var p_78.fst)
    (Expr.jump Jloop (.var off_v, .var p2_v, .var q_v, .var end_v, ()))
    (Expr.let_ ⟨.zext 32 64, (.var l0_v, ())⟩ fun p_79 =>
     Expr.let_ ⟨.add i64, (.var pVals, .var p_79.fst, ())⟩ fun p_80 =>
     Expr.load i8 (.var p_80.fst) fun ld =>
     Expr.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p_81 =>
     Expr.let_ ⟨.sext 8 32, (.var ld, ())⟩ fun p_82 =>
     Expr.let_ ⟨.sext 8 32, (.var p_81.fst, ())⟩ fun p_83 =>
     Expr.let_ ⟨.cmp .sgt i32, (.var p_82.fst, .var p_83.fst, ())⟩ fun p_84 =>
     Expr.jnz (.var p_84.fst)
       (Expr.let_ ⟨.mul i64, (.var q_v, .imm 4, ())⟩ fun p =>
        Expr.let_ ⟨.add i64, (.var pWstk, .var p.fst, ())⟩ fun p =>
        Expr.let_ ⟨.and i32, (.var l0_v, .imm 2147483647, ())⟩ fun p_85 =>
        Expr.store (.var p_85.fst) (.var p.fst)
          (Expr.let_ ⟨.add i64, (.var q_v, .imm 1, ())⟩ fun p =>
           Expr.let_ ⟨.mul i64, (.var p.fst, .imm 4, ())⟩ fun p =>
           Expr.let_ ⟨.add i64, (.var pWstk, .var p.fst, ())⟩ fun p =>
           Expr.store (.var cr_v) (.var p.fst)
             (Expr.let_ ⟨.add i64, (.var q_v, .imm 2, ())⟩ fun p =>
              Expr.jump Jloop (.var off_v, .var p2_v, .var p.fst, .var end_v, ()))))
       (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_85 =>
        Expr.call "full_find_repl" (as := [i64, i64]) (bs := [i64]) (.var h_arg, .var p_85.fst, ())
          fun p_86 =>
        Expr.let_ ⟨.cmp .ne i64, (.var p_86.fst, .imm 4294967295, ())⟩ fun p_87 =>
        Expr.jnz (.var p_87.fst)
          (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_88 =>
           Expr.let_ ⟨.add i64, (.var p_88.fst, .imm 3, ())⟩ fun p_89 =>
           Expr.let_ ⟨.add i64, (.var p_89.fst, .var p_86.fst, ())⟩ fun p_90 =>
           Expr.let_ ⟨.mul i64, (.var p_90.fst, .imm 4, ())⟩ fun p_91 =>
           Expr.let_ ⟨.add i64, (.var pArena, .var p_91.fst, ())⟩ fun p_92 =>
           Expr.load i32 (.var p_92.fst) fun ld =>
           Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_93 =>
           Expr.let_ ⟨.add i64, (.var p_93.fst, .imm 4, ())⟩ fun p_94 =>
           Expr.let_ ⟨.mul i64, (.var p_94.fst, .imm 4, ())⟩ fun p_95 =>
           Expr.let_ ⟨.add i64, (.var pArena, .var p_95.fst, ())⟩ fun p_96 =>
           Expr.store (.var ld) (.var p_96.fst)
             (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_97 =>
              Expr.let_ ⟨.add i64, (.var p_97.fst, .imm 3, ())⟩ fun p_98 =>
              Expr.let_ ⟨.add i64, (.var p_98.fst, .var p_86.fst, ())⟩ fun p_99 =>
              Expr.let_ ⟨.mul i64, (.var p_99.fst, .imm 4, ())⟩ fun p_100 =>
              Expr.let_ ⟨.add i64, (.var pArena, .var p_100.fst, ())⟩ fun p_101 =>
              Expr.store (.var not_lit) (.var p_101.fst)
                (Expr.let_ ⟨.sub i64, (.var p2_v, .var off_v, ())⟩ fun p_102 =>
                 Expr.let_ ⟨.sub i64, (.var q_v, .var off_v, ())⟩ fun p_103 =>
                 Expr.let_ ⟨.sub i64, (.var end_v, .var off_v, ())⟩ fun p_104 =>
                 Expr.let_ ⟨.and i32, (.var l0_v, .imm 2147483647, ())⟩ fun p_105 =>
                 Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                   (.var h_arg, .var ld, .var p_105.fst, .var cr_v, .imm 2, ()) fun p_106 =>
                 Expr.let_ ⟨.zext 32 64, (.var not_lit, ())⟩ fun p_107 =>
                 Expr.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_108 =>
                 Expr.let_ ⟨.shl i64, (.var p_107.fst, .var p_108.fst, ())⟩ fun p_109 =>
                 Expr.let_ ⟨.mul i64, (.var p_109.fst, .imm 4, ())⟩ fun p_110 =>
                 Expr.let_ ⟨.add i64, (.var pWvec, .var p_110.fst, ())⟩ fun p_111 =>
                 Expr.load i32 (.var p_111.fst) fun ld_16 =>
                 Expr.let_ ⟨.zext 32 64, (.var ld_16, ())⟩ fun p_112 =>
                 Expr.let_ ⟨.add i64, (.var p_112.fst, .var p_102.fst, ())⟩ fun p_113 =>
                 Expr.let_ ⟨.add i64, (.var p_112.fst, .var p_103.fst, ())⟩ fun p_114 =>
                 Expr.let_ ⟨.add i64, (.var p_112.fst, .var p_104.fst, ())⟩ fun p_115 =>
                 Expr.jnz (.var p_106.fst)
                   (Expr.jump Jloop (.var p_112.fst, .var p_113.fst, .var p_114.fst,
                     .var p_115.fst, ()))
                   (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_116 =>
                    Expr.let_ ⟨.add i64, (.var p_116.fst, .imm 4, ())⟩ fun p_117 =>
                    Expr.let_ ⟨.mul i64, (.var p_117.fst, .imm 4, ())⟩ fun p_118 =>
                    Expr.let_ ⟨.add i64, (.var pArena, .var p_118.fst, ())⟩ fun p_119 =>
                    Expr.store (.var not_lit) (.var p_119.fst)
                      (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_120 =>
                       Expr.let_ ⟨.add i64, (.var p_120.fst, .imm 3, ())⟩ fun p_121 =>
                       Expr.let_ ⟨.add i64, (.var p_121.fst, .var p_86.fst, ())⟩ fun p_122 =>
                       Expr.let_ ⟨.mul i64, (.var p_122.fst, .imm 4, ())⟩ fun p_123 =>
                       Expr.let_ ⟨.add i64, (.var pArena, .var p_123.fst, ())⟩ fun p_124 =>
                       Expr.store (.var ld) (.var p_124.fst)
                         (Expr.let_ ⟨.mul i64, (.var p_114.fst, .imm 4, ())⟩ fun p_125 =>
                          Expr.let_ ⟨.add i64, (.var pWstk, .var p_125.fst, ())⟩ fun p_126 =>
                          Expr.store (.var w0_v) (.var p_126.fst)
                            (Expr.let_ ⟨.add i64, (.var p_114.fst, .imm 1, ())⟩ fun p_127 =>
                             Expr.let_ ⟨.mul i64, (.var p_127.fst, .imm 4, ())⟩ fun p_128 =>
                             Expr.let_ ⟨.add i64, (.var pWstk, .var p_128.fst, ())⟩ fun p_129 =>
                             Expr.store (.var cr_v) (.var p_129.fst)
                               (Expr.let_ ⟨.add i64, (.var p_114.fst, .imm 2, ())⟩ fun p_130 =>
                                Expr.let_ ⟨.add i64, (.var h_arg, .imm 760, ())⟩ fun p =>
                                Expr.store (t := i64) (.imm 1) (.var p.fst)
                                  (Expr.jump Jtail (.var p_112.fst, .var p_113.fst,
                                    .var p_130.fst, .var p_115.fst, .imm true, ()))))))))))
          (Expr.let_ ⟨.mul i64, (.var q_v, .imm 4, ())⟩ fun p_88 =>
           Expr.let_ ⟨.add i64, (.var pWstk, .var p_88.fst, ())⟩ fun p_89 =>
           Expr.let_ ⟨.and i32, (.var l0_v, .imm 2147483647, ())⟩ fun p_90 =>
           Expr.store (.var p_90.fst) (.var p_89.fst)
             (Expr.let_ ⟨.add i64, (.var q_v, .imm 1, ())⟩ fun p_91 =>
              Expr.let_ ⟨.mul i64, (.var p_91.fst, .imm 4, ())⟩ fun p_92 =>
              Expr.let_ ⟨.add i64, (.var pWstk, .var p_92.fst, ())⟩ fun p_93 =>
              Expr.store (.var cr_v) (.var p_93.fst)
                (Expr.let_ ⟨.add i64, (.var q_v, .imm 2, ())⟩ fun p_94 =>
                 Expr.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p_95 =>
                 Expr.let_ ⟨.sext 8 32, (.var ld, ())⟩ fun p_96 =>
                 Expr.let_ ⟨.sext 8 32, (.var p_95.fst, ())⟩ fun p_97 =>
                 Expr.let_ ⟨.cmp .slt i32, (.var p_96.fst, .var p_97.fst, ())⟩ fun p_98 =>
                 Expr.jnz (.var p_98.fst)
                   (Expr.let_ ⟨.add i64, (.var h_arg, .imm 528, ())⟩ fun p_99 =>
                    Expr.store (t := i64) (.imm 2) (.var p_99.fst)
                      (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_100 =>
                       Expr.let_ ⟨.add i64, (.var h_arg, .imm 176, ())⟩ fun p =>
                       Expr.store (.var p_100.fst) (.var p.fst)
                         (Expr.jump Jtail (.var off_v, .var p2_v, .var p_94.fst,
                           .var end_v, .imm true, ()))))
                   (Expr.call "full_hbr_dom" (as := [i64, i32, i32]) (bs := [i32])
                      (.var h_arg, .var cr_v, .var l0_v, ()) fun p_99 =>
                    Expr.group (sig := [[]]) (fun Js => Blocks.cons (fun _p_100 =>
                      Expr.call "full_assign_lvl" (as := [i64, i32, i32, i32]) (bs := [])
                        (.var h_arg, .var l0_v, .var cr_v, .imm 1, ()) fun _p =>
                      Expr.jump Jloop (.var off_v, .var p2_v, .var p_94.fst, .var end_v, ()))
                      .nil)
                    fun Js =>
                    Expr.let_ ⟨.cmp .ne i32, (.var p_99.fst, .imm 4294967295, ())⟩ fun p_100 =>
                    Expr.jnz (.var p_100.fst)
                      (Expr.let_ ⟨.add i64, (.var h_arg, .imm 184, ())⟩ fun p_101 =>
                       Expr.load i64 (.var p_101.fst) fun ld =>
                       Expr.let_ ⟨.add i64, (.var h_arg, .imm 776, ())⟩ fun p_102 =>
                       Expr.load i64 (.var p_102.fst) fun ld_16 =>
                       Expr.let_ ⟨.cmp .ult i64, (.var ld, .var ld_16, ())⟩ fun p_103 =>
                       Expr.jnz (.var p_103.fst)
                         (Expr.let_ ⟨.add i64, (.var h_arg, .imm 184, ())⟩ fun p_104 =>
                          Expr.load i64 (.var p_104.fst) fun ld =>
                          Expr.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_105 =>
                          Expr.let_ ⟨.shl i64, (.var ld, .var p_105.fst, ())⟩ fun p_106 =>
                          Expr.let_ ⟨.mul i64, (.var p_106.fst, .imm 4, ())⟩ fun p_107 =>
                          Expr.let_ ⟨.add i64, (.var pHstk, .var p_107.fst, ())⟩ fun p_108 =>
                          Expr.let_ ⟨.xor i32, (.var p_99.fst, .imm 1, ())⟩ fun p_109 =>
                          Expr.store (.var p_109.fst) (.var p_108.fst)
                            (Expr.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_110 =>
                             Expr.let_ ⟨.shl i64, (.var ld, .var p_110.fst, ())⟩ fun p_111 =>
                             Expr.let_ ⟨.add i64, (.var p_111.fst, .imm 1, ())⟩ fun p_112 =>
                             Expr.let_ ⟨.mul i64, (.var p_112.fst, .imm 4, ())⟩ fun p_113 =>
                             Expr.let_ ⟨.add i64, (.var pHstk, .var p_113.fst, ())⟩ fun p_114 =>
                             Expr.store (.var l0_v) (.var p_114.fst)
                               (Expr.let_ ⟨.add i64, (.var ld, .imm 1, ())⟩ fun p_115 =>
                                Expr.let_ ⟨.add i64, (.var h_arg, .imm 184, ())⟩ fun p =>
                                Expr.store (.var p_115.fst) (.var p.fst)
                                  (Expr.jump Js.fst ()))))
                         (Expr.jump Js.fst ()))
                      (Expr.jump Js.fst ())))))))

theorem propLitLarge_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st : FullState} {R : Mem 64 → Prop}
    {not_lit : BitVec 32}
    (hFindRepl : ∀ args m Q X, fullFindReplSpec args m Q X →
      Γ "full_find_repl" [i64, i64] [i64] args m Q X)
    (hWatchPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hHbrDom : ∀ args m Q X, fullHbrDomSpec args m Q X →
      Γ "full_hbr_dom" [i64, i32, i32] [i32] args m Q X)
    (hAssignLvl : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    {Jtail : Cont [i64, i64, i64, i64, Ty.bool]} {Jloop : Cont [i64, i64, i64, i64]}
    {h_arg pVals pWvec pWstk pArena pHstk nlits_v off_v p_prev p2_v q_v end_v : Val i64}
    {cr_v w0_v l0_v : Val i32} {ml : Mem 64}
    (hnot_lt : not_lit.toNat < 2 * s.core.cur_vars)
    (hJtail : ∀ args m, propLitTailInv c F0 F_cur s R not_lit args m → Jtail args m)
    (hJloop : ∀ off_r p_r q_r end_r m,
      propLitMainInv c F0 F_cur s R not_lit (off_r, p_r, q_r, end_r, ()) m →
      end_r.toNat - p_r.toNat = end_v.toNat - p2_v.toNat →
      Jloop (off_r, p_r, q_r, end_r, ()) m)
    (hh : h_arg = c.hdr) (hpv : pVals = c.pVals) (hpwv : pWvec = c.pWvec)
    (hpws : pWstk = c.pWstk) (hpa : pArena = c.pArena) (hphs : pHstk = c.pWorkStk2)
    (hnl : nlits_v = BitVec.ofNat 64 s.core.cur_vars <<< 1)
    (hp2_eq : p2_v.toNat = p_prev.toNat + 2)
    (hlen : st.LengthsOk c) (hw_nw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c st).core)
    (hmrk0 : FullMrkZero c st) (hnd : FullArenaVarsNodup st) (hext : FullExtScratchOk c st)
    (hdm : st.core.dense_mode = 0#64) (hcl1 : st.core.cur_level = 1)
    (hcv : st.core.cur_vars = s.core.cur_vars) (hfu : st.core.fuel = s.core.fuel)
    (hlm : st.core.lit_mark = s.core.lit_mark) (hws1 : st.scratch.work_stk1 = s.scratch.work_stk1)
    (htr : FullTrailRsnsExt s.core st.core) (hhbr : FullHbrBufOkW F_cur st st.core.tmp_cnt)
    (hsplit : FullSplitWatchesInv F_cur st.core not_lit.toNat off_v.toNat q_v.toNat p2_v.toNat
      end_v.toNat)
    (hqp : q_v.toNat ≤ p_prev.toNat)
    (hnot_false : st.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8) (hoom0 : st.core.oom = 0#64)
    (hflag : (w0_v &&& 0x80000000#32) = 0#32)
    (hcr_lt : cr_v.toNat < 0x80000000) (hcr_ref : cr_v.toNat ∈ fullArenaClauseRefs st)
    (hcr_ng : fullArenaClauseGarb st cr_v.toNat = false)
    (hcr_sz : 3 ≤ fullArenaClauseSize st cr_v.toNat)
    (hcr_bd : cr_v.toNat + 3 + fullArenaClauseSize st cr_v.toNat ≤ st.core.arena_len)
    (hcr_arr : cr_v.toNat + 3 + fullArenaClauseSize st cr_v.toNat ≤ st.core.arena.length)
    (hl0_at : (st.core.arena[cr_v.toNat + 3]'(by omega)).toNat = l0_v.toNat)
    (hnot_at : (st.core.arena[cr_v.toNat + 4]'(by omega)).toNat = not_lit.toNat)
    (hml : (FullMem c st ⋆ R) ml) :
    wp Γ Q X
      (propLitLargeExpr h_arg pVals pWvec pWstk pArena pHstk not_lit nlits_v cr_v w0_v l0_v
        off_v p2_v q_v end_v Jtail Jloop)
      ml := by
  subst hh hpv hpwv hpws hpa hphs hnl
  have hcl := hlen.core_ok
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hcl.cur_vars_le
  have hnot_lt' : not_lit.toNat < 2 * st.core.cur_vars := hcv ▸ hnot_lt
  have hsz_pos_cr : 0 < fullArenaClauseSizeCore st.core cr_v.toNat := by
    change 0 < fullArenaClauseSize st cr_v.toNat; omega
  have hl0_mem : l0_v.toNat ∈ fullArenaClauseLits st cr_v.toNat :=
    (mem_fullArenaClauseLitsCore_iff hcr_arr).mpr ⟨0, hsz_pos_cr, hl0_at⟩
  have hl0_lt : l0_v.toNat < 2 * st.core.cur_vars :=
    hw_nw.arena.lits_lt cr_v.toNat hcr_ref hcr_ng _ hl0_mem
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< 1).toNat = 2 * st.core.cur_vars := by
    rw [bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
      bv64_ofNat_toNat (by omega), hcv]
  have hq_lt : q_v.toNat < st.core.wstk.length := by
    have := hsplit.layout.bounds not_lit.toNat hnot_lt'
    rw [hsplit.off_eq, hsplit.sz_eq] at this
    have := hcl.wlen_le; have := hcl.wstk_len_arr; have := hsplit.p_le_end; omega
  have hq1_lt : q_v.toNat + 1 < st.core.wstk.length := by
    have := hsplit.layout.bounds not_lit.toNat hnot_lt'
    rw [hsplit.off_eq, hsplit.sz_eq] at this
    have := hcl.wlen_le; have := hcl.wstk_len_arr; have := hsplit.p_le_end; omega
  have hsplit_prev : FullSplitWatchesInv F_cur st.core not_lit.toNat off_v.toNat q_v.toNat
      (p_prev.toNat + 2) end_v.toNat := by
    simpa only [← hp2_eq] using hsplit
  have hq2_64 : q_v.toNat + 2 < 2 ^ 64 := by
    have := c.hwcap; unfold dimacsBound at this; have := hcl.wstk_len_arr; omega
  have hq1_bv : (q_v + 1).toNat = q_v.toNat + 1 := by bv_omega
  have hw0l_eq : l0_v &&& 0x7FFFFFFF#32 = l0_v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hw0l_msb : ((l0_v &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 :=
    bv32_mask7f_msb_zero l0_v
  have hl0_64 : (l0_v.setWidth 64).toNat < (BitVec.ofNat 64 s.core.cur_vars <<< 1).toNat := by
    rw [bv_c0_zext32_64, hnl_eq]; exact hl0_lt
  have hl0_val_lt : l0_v.toNat < st.core.vals.length := by rw [hcl.vals_len]; omega
  have hl0_val64 : (l0_v.setWidth 64).toNat < st.core.vals.length := by
    rw [bv_c0_zext32_64]; exact hl0_val_lt
  have hcr64 : (cr_v.setWidth 64).toNat = cr_v.toNat := bv_c0_zext32_64 _
  unfold propLitLargeExpr
  pt_steps_nogrp
  · exfalso; pt_clear_big
    have hcv_m : s.core.cur_vars < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hcv_m, Nat.mod_eq_of_lt (by omega)] at hc; omega
  · have hsw := hsplit_prev.write_large hnot_lt' hqp hq_lt hq1_lt hw0l_msb hcr_lt hcr_ref
    let st' : FullState := { st with core := { st.core with
      wstk := (st.core.wstk.set q_v.toNat (l0_v &&& 0x7FFFFFFF#32)).set
        (q_v.toNat + 1) cr_v } }
    have hsw2 : FullSplitWatchesInv F_cur st'.core not_lit.toNat off_v.toNat
        (q_v + 2#64).toNat p2_v.toNat end_v.toNat := by
      have hq2 : (q_v + 2#64).toNat = q_v.toNat + 2 := by bv_omega
      simpa only [st', hq2, hp2_eq] using hsw
    have hlen' : st'.LengthsOk c :=
      ⟨{ hcl with wstk_len_arr := (by simp [st', hcl.wstk_len_arr]) }, hlen.scratch_ok⟩
    have hw' := fullWitnessInv_nw_upd_watches hw_nw hlen'.core_ok rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl
    rw [hq1_bv] at hm
    refine hJloop off_v p2_v (q_v + 2#64) end_v m
      ⟨st', hlen', hw', hmrk0, fullArenaVarsNodup_of_arena_eq hnd rfl rfl,
        ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩, hdm, hcl1, hcv, hfu, hlm, hws1,
        htr, hhbr, hsw2, hnot_false, hoom0, hm⟩ rfl
  · have hnsgt : ¬ (0#32).slt ((st.core.vals[l0_v.toNat]'hl0_val_lt).signExtend 32) = true := by
      pt_clear_big; simp [hc]
    pt_steps_nogrp
    c0_call hFindRepl
    refine ⟨c, st, R, rfl, hlen, by rw [hcr64]; omega, by rw [hcr64]; exact hcr_sz,
      by rw [hcr64]; exact hcr_bd, hml, ?_, ?_⟩
    ·
        intro hfind_none
        rw [hcr64] at hfind_none
        have hfals := clause_falsified_of_find_repl_none hlen hw_nw hcr_ref hcr_ng hcr_arr
          hl0_at hnot_at hnot_false hfind_none
        have hsw := hsplit_prev.write_large hnot_lt' hqp hq_lt hq1_lt hw0l_msb hcr_lt hcr_ref
        let st_w : FullState := { st with core := { st.core with
          wstk := (st.core.wstk.set q_v.toNat (l0_v &&& 0x7FFFFFFF#32)).set
            (q_v.toNat + 1) cr_v } }
        have hsw2 : FullSplitWatchesInv F_cur st_w.core not_lit.toNat off_v.toNat
            (q_v + 2#64).toNat p2_v.toNat end_v.toNat := by
          have hq2 : (q_v + 2#64).toNat = q_v.toNat + 2 := by bv_omega
          simpa only [st_w, hq2, hp2_eq] using hsw
        have hlen_w : st_w.LengthsOk c :=
          ⟨{ hcl with wstk_len_arr := (by simp [st_w, hcl.wstk_len_arr]) }, hlen.scratch_ok⟩
        have hw_w := fullWitnessInv_nw_upd_watches hw_nw hlen_w.core_ok
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hext_w : FullExtScratchOk c st_w :=
          ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩
        have hnd_w : FullArenaVarsNodup st_w := fullArenaVarsNodup_of_arena_eq hnd rfl rfl
        pt_steps_nogrp
        · rw [hq1_bv] at hm
          have hslt : ((st.core.vals[l0_v.toNat]'hl0_val_lt).signExtend 32).slt 0#32 = true := by
            pt_clear_big; exact hc
          have hl0_ff : st.core.vals[l0_v.toNat]?.getD 0#8 = 0xFF#8 :=
            pt_vals_eq_ff_of_slt hl0_val_lt (hw_nw.vals_domain _ hl0_lt) hslt
          let st_c : FullState := { st_w with core := { st_w.core with
            confl_type := 2#64, confl_ref := cr_v.setWidth 64 } }
          have hlen_c : st_c.LengthsOk c :=
            ⟨{ hlen_w.core_ok with cur_vars_le := hcv_le }, hlen_w.scratch_ok⟩
          have hw_c := fullWitnessInv_nw_upd_watches hw_w hlen_c.core_ok
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          have hconfl_ok : FullConflictOkW F_cur st_c := by
            refine Or.inr ⟨by simp [st_c], hcr_ref, hcr_ng, fun l hl => ?_⟩
            have hcr_eq : (cr_v.setWidth 64).toNat = cr_v.toNat := by bv_omega
            rw [hcr_eq] at hl; rcases hfals l hl with rfl | hff <;> first | exact hl0_ff | exact hff
          refine hJtail (off_v, p2_v, q_v + 2#64, end_v, true, ()) m
            ⟨st_c, hlen_c, hw_c, hmrk0, fullArenaVarsNodup_of_arena_eq hnd_w rfl rfl,
              ⟨fullLastLearnedWf_of_refs_eq hext_w.1 rfl rfl, hext_w.2⟩, hdm, hcl1, hcv, hfu,
              hlm, hws1, htr, hhbr, hsw2.with_nonwatch rfl rfl rfl rfl fun _ h => h,
              fun _ => Or.inr hconfl_ok, fun hf => (by cases hf), hm⟩
        · rw [hq1_bv] at hm
          have hnslt : ¬ ((st.core.vals[l0_v.toNat]'hl0_val_lt).signExtend 32).slt 0#32 =
              true := by pt_clear_big; simp [hc]
          have hl0_0 : st.core.vals[l0_v.toNat]?.getD 0#8 = 0#8 :=
            pt_vals_eq_0_of_flags hl0_val_lt (hw_nw.vals_domain _ hl0_lt) hnsgt hnslt
          c0_call hHbrDom
          refine ⟨c, F0, F_cur, st_w, R, rfl, hlen_w,
            ⟨List.replicate (4 * c.max_vars) 0#32, st_w.core.wstk, 0, hw_w⟩,
            hmrk0, hcl1, hcr_ref, hcr_ng, ?_, fun l hl hne => ?_, hm, ?_⟩
          · simpa [st_w, fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSize,
              fullArenaClauseSizeCore] using hl0_mem
          · have hfl := hfals l (by simpa [st_w, fullArenaClauseLits, fullArenaClauseLitsCore,
              fullArenaClauseSize, fullArenaClauseSizeCore] using hl)
            exact hfl.resolve_left hne
          · dsimp only; intro dom mrk' mclr' mh hlen_h hmrk_h hdom hm_h
            let st_h : FullState := { st_w with core := { st_w.core with
              mrk := mrk', min_clr := mclr' } }
            have hw_h := fullWitnessInv_nw_upd_watches hw_w hlen_h.core_ok rfl rfl rfl rfl rfl rfl
              rfl rfl rfl rfl rfl rfl rfl
            have hsw_h := hsw2.with_nonwatch (k' := st_h.core) rfl rfl rfl rfl fun _ h => h
            have hext_h : FullExtScratchOk c st_h :=
              ⟨fullLastLearnedWf_of_refs_eq hext_w.1 rfl rfl, hext_w.2⟩
            have hnd_h : FullArenaVarsNodup st_h := fullArenaVarsNodup_of_arena_eq hnd_w rfl rfl
            have hhbr_h : FullHbrBufOkW F_cur st_h st_h.core.tmp_cnt :=
              fullHbrBufOkW_congr hhbr rfl rfl
            refine wp_join_group
              (fun () m_j => ∃ st_j : FullState,
                st_j.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_j).core ∧
                FullMrkZero c st_j ∧ FullArenaVarsNodup st_j ∧ FullExtScratchOk c st_j ∧
                st_j.core.dense_mode = 0#64 ∧ st_j.core.cur_level = 1 ∧
                st_j.core.cur_vars = s.core.cur_vars ∧ st_j.core.fuel = s.core.fuel ∧
                st_j.core.lit_mark = s.core.lit_mark ∧
                st_j.scratch.work_stk1 = s.scratch.work_stk1 ∧
                FullTrailRsnsExt s.core st_j.core ∧ FullHbrBufOkW F_cur st_j st_j.core.tmp_cnt ∧
                FullSplitWatchesInv F_cur st_j.core not_lit.toNat off_v.toNat (q_v + 2#64).toNat
                  p2_v.toNat end_v.toNat ∧
                st_j.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧ st_j.core.oom = 0#64 ∧
                st_j.core.vals[l0_v.toNat]?.getD 0#8 = 0#8 ∧ cr_v.toNat ∈ fullArenaClauseRefs st_j ∧
                fullArenaClauseGarb st_j cr_v.toNat = false ∧
                (∀ q ∈ fullArenaClauseLits st_j cr_v.toNat,
                  q = l0_v.toNat ∨ st_j.core.vals[q]?.getD 0#8 = 0xFF#8) ∧
                l0_v.toNat ∈ fullArenaClauseLits st_j cr_v.toNat ∧ (FullMem c st_j ⋆ R) m_j)
              (fun _ () m_j ⟨st_j, hj_len, hj_nw, hj_mrk, hj_nd, hj_ext, hj_dm, hj_cl1, hj_cv,
                hj_fu, hj_lm, hj_ws1, hj_tr, hj_hbr, hj_sw, hj_nf, hj_oom, hj_l00, hj_cref,
                hj_cng, hj_fals, hj_l0m, hm_j⟩ => by
                pt_steps_nogrp
                c0_call hAssignLvl
                refine ⟨c, st_j, R, rfl, hj_len, hm_j, ?_⟩
                have hl0_j : l0_v.toNat < 2 * st_j.core.cur_vars := by
                  rw [hj_cv, ← hcv]; exact hl0_lt
                have hte_j : st_j.core.trail_end < st_j.core.cur_vars :=
                  hj_nw.trail_end_lt_of_unassigned hl0_j hj_l00
                have hno_j : ¬ (st_j.core.cur_vars ≤ l0_v.toNat / 2 ∨
                    c.max_vars ≤ st_j.core.trail_end ∨
                    st_j.core.vals[l0_v.toNat]?.getD 0#8 ≠ 0#8) := by
                  have := hj_len.core_ok.cur_vars_le
                  intro hbad; rcases hbad with h1 | h2 | h3 <;> first | omega | exact h3 hj_l00
                rw [ite_eq_right hno_j]; dsimp only
                intro flags' unass' phases' m_a hfll hph hm_a
                have hnot_j : not_lit.toNat < 2 * st_j.core.cur_vars := by rw [hj_cv]; exact hnot_lt
                have hcr_msb : (cr_v &&& 0x80000000#32) = 0#32 := bv32_msb_zero_of_lt hcr_lt
                have hcr_ne_ff : cr_v ≠ 0xFFFFFFFF#32 := fun h => by
                  rw [h] at hcr_lt; exact absurd hcr_lt (by decide)
                have hu := unitAssignLvl_preserves_witness hj_len hj_nw (other := l0_v)
                  (rsn := cr_v) (alvl := 1#32) (not_lit := not_lit.toNat) (flags' := flags')
                  (phases' := phases') (unass' := unass') (unfl' := st_j.core.unflushed) hl0_j
                  hfll hph hj_l00 hnot_j hj_nf (by decide) (by rw [hj_cl1]; decide) hcr_ne_ff
                  (by
                    rw [ite_eq_right (by intro hc; exact hc hcr_msb)]
                    refine ⟨hj_cref, hj_cng, fun q hq => ?_⟩
                    rcases hj_fals q hq with rfl | hq_ff
                    · exact Or.inl rfl
                    · right
                      have hq_lt : q < 2 * st_j.core.cur_vars :=
                        hj_nw.arena.lits_lt _ hj_cref hj_cng q hq
                      obtain ⟨k, hk, hkeq⟩ := (hj_nw.vals_false_iff q hq_lt).mp hq_ff
                      have hk_lvl := hj_nw.lvl_le k hk
                      dsimp only [withEmptyModeWatches] at hk_lvl
                      have hqvar : (st_j.core.trl[k]?.getD 0#32).toNat / 2 = q / 2 := by
                        rw [hkeq]; exact fullInv_var_xor1 q
                      rw [hqvar, hj_cl1] at hk_lvl
                      exact ⟨k, hk, hkeq, by simpa using hk_lvl⟩)
                  (fun _ => hj_l0m)
                dsimp only at hu hm_a
                let st_a : FullState :=
                  { st_j with
                    core := { st_j.core with
                      vals := (st_j.core.vals.set l0_v.toNat 1#8).set (l0_v.toNat ^^^ 1) 0xFF#8
                      flags := flags', lvl := st_j.core.lvl.set (l0_v.toNat / 2) 1#32
                      rsns := st_j.core.rsns.set (l0_v.toNat / 2) cr_v
                      trl := st_j.core.trl.set st_j.core.trail_end l0_v
                      trail_pos := st_j.core.trail_pos.set (l0_v.toNat / 2)
                        (BitVec.ofNat 32 st_j.core.trail_end)
                      trail_end := st_j.core.trail_end + 1, unassigned := unass' }
                    scratch := { st_j.scratch with phases := phases' } }
                have hlen_a : st_a.LengthsOk c :=
                  ⟨{ hj_len.core_ok with
                      vals_len := (by simp [st_a, hj_len.core_ok.vals_len]),
                      flags_len := (by simp [st_a, hfll]),
                      lvl_len := (by simp [st_a, hj_len.core_ok.lvl_len]),
                      rsns_len := (by simp [st_a, hj_len.core_ok.rsns_len]),
                      trl_len := (by simp [st_a, hj_len.core_ok.trl_len]),
                      trail_pos_len := (by simp [st_a, hj_len.core_ok.trail_pos_len]),
                      trail_end_le := (by simp [st_a]; omega),
                      propagated_le :=
                        (by simp [st_a]; have := hj_len.core_ok.propagated_le; omega) },
                    { hj_len.scratch_ok with phases_len := (by simp [st_a, hph]) }⟩
                have htr_ja := fullTrailRsnsExt_trans
                  (fullTrailRsnsExt_congr (k1 := st_j.core)
                    (k2 := (withEmptyModeWatches c st_j).core) rfl rfl rfl rfl)
                  (fullTrailRsnsExt_trans
                    (fullTrailRsnsExt_of_assign_lvl (rsn := cr_v) (alvl := 1#32)
                      (flags' := flags') (unass' := unass') (unfl' := st_j.core.unflushed)
                      hj_nw hl0_j hj_l00)
                    (fullTrailRsnsExt_congr (k2 := st_a.core) rfl rfl rfl rfl))
                have htr_a := fullTrailRsnsExt_trans hj_tr htr_ja
                refine hJloop off_v p2_v (q_v + 2#64) end_v m_a ⟨st_a, hlen_a, hu.1,
                  fun w hw => hj_mrk w hw, fullArenaVarsNodup_of_arena_eq hj_nd rfl rfl,
                  ⟨fullLastLearnedWf_of_refs_eq hj_ext.1 rfl rfl, hj_ext.2⟩, hj_dm, hj_cl1,
                  hj_cv, hj_fu, hj_lm, hj_ws1, htr_a, fullHbrBufOkW_congr hj_hbr rfl rfl,
                  hj_sw.with_nonwatch rfl rfl rfl rfl fun _ h => h, hu.2, hj_oom, hm_a⟩ rfl)
              (fun Jh hJh => by
                have hdone_base : ∀ (st_x : FullState) (mx : Mem 64), st_x.LengthsOk c →
                    FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_x).core →
                    FullMrkZero c st_x → FullArenaVarsNodup st_x → FullExtScratchOk c st_x →
                    st_x.core.dense_mode = 0#64 → st_x.core.cur_level = 1 →
                    st_x.core.cur_vars = s.core.cur_vars → st_x.core.fuel = s.core.fuel →
                    st_x.core.lit_mark = s.core.lit_mark →
                    st_x.scratch.work_stk1 = s.scratch.work_stk1 →
                    FullTrailRsnsExt s.core st_x.core → FullHbrBufOkW F_cur st_x st_x.core.tmp_cnt →
                    FullSplitWatchesInv F_cur st_x.core not_lit.toNat off_v.toNat
                      (q_v + 2#64).toNat p2_v.toNat end_v.toNat →
                    st_x.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 → st_x.core.oom = 0#64 →
                    st_x.core.vals[l0_v.toNat]?.getD 0#8 = 0#8 →
                    cr_v.toNat ∈ fullArenaClauseRefs st_x → fullArenaClauseGarb st_x cr_v.toNat =
                      false → (∀ q ∈ fullArenaClauseLits st_x cr_v.toNat,
                      q = l0_v.toNat ∨ st_x.core.vals[q]?.getD 0#8 = 0xFF#8) →
                    l0_v.toNat ∈ fullArenaClauseLits st_x cr_v.toNat → (FullMem c st_x ⋆ R) mx →
                    wp Γ Q X (Expr.jump Jh ()) mx := by
                  intro st_x mx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                    x20 x21 hm_x
                  pt_steps_nogrp; exact hJh () mx ⟨st_x, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10,
                    x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, hm_x⟩
                have hl0_w : l0_v.toNat ∈ fullArenaClauseLits st_h cr_v.toNat := by
                  simpa [st_h, st_w, fullArenaClauseLits, fullArenaClauseLitsCore,
                    fullArenaClauseSize, fullArenaClauseSizeCore] using hl0_mem
                have hfals_h : ∀ q ∈ fullArenaClauseLits st_h cr_v.toNat,
                    q = l0_v.toNat ∨ st_h.core.vals[q]?.getD 0#8 = 0xFF#8 := fun q hq => hfals q
                  (by simpa [st_h, st_w, fullArenaClauseLits, fullArenaClauseLitsCore,
                    fullArenaClauseSize, fullArenaClauseSizeCore] using hq)
                pt_steps_nogrp
                · obtain ⟨hdom_lt, hent_dom⟩ := hdom.resolve_left (by pt_clear_big; assumption)
                  have h_tc_le : st_h.core.tmp_cnt ≤ st_h.core.cur_vars := hhbr_h.1
                  have hcv_h : st_h.core.cur_vars ≤ c.max_vars := hlen_h.core_ok.cur_vars_le
                  have htc_lt : st_h.core.tmp_cnt < st_h.core.cur_vars := by
                    pt_clear_big
                    have hlt : st_h.core.tmp_cnt % 2 ^ 64 < st_h.core.cur_vars % 2 ^ 64 := by
                      assumption
                    rw [Nat.mod_eq_of_lt (by omega : st_h.core.cur_vars < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
                  have hshl_h : (BitVec.ofNat 64 st_h.core.tmp_cnt <<< 1).toNat =
                      2 * st_h.core.tmp_cnt := by
                    rw [bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                      bv64_ofNat_toNat (by omega)]
                  have h_idx0 : (BitVec.ofNat 64 st_h.core.tmp_cnt <<<
                      ((1#32 : BitVec 32).signExtend 64).toNat).toNat = 2 * st_h.core.tmp_cnt := by
                    simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl]
                      using hshl_h
                  have h_idx1 : ((BitVec.ofNat 64 st_h.core.tmp_cnt <<<
                      ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat =
                      2 * st_h.core.tmp_cnt + 1 := by
                    rw [bv64_add1_toNat (by rw [h_idx0]; omega), h_idx0]
                  have hws2_i0 : (BitVec.ofNat 64 st_h.core.tmp_cnt <<<
                      ((1#32 : BitVec 32).signExtend 64).toNat).toNat <
                      st_h.scratch.work_stk2.length := by
                    rw [hlen_h.scratch_ok.work_stk2_len, h_idx0]; omega
                  have hws2_i1 : ((BitVec.ofNat 64 st_h.core.tmp_cnt <<<
                      ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat <
                      st_h.scratch.work_stk2.length := by
                    rw [hlen_h.scratch_ok.work_stk2_len, h_idx1]; omega
                  have hpush := fullHbrBufOkW_push hlen_h hhbr_h htc_lt
                    (a := dom ^^^ 1#32) (b := l0_v)
                    (by rw [bv32_toNat_xor1]; exact litNeg_lt_two_mul hdom_lt) hl0_lt
                    (by rw [bv32_toNat_xor1]; exact hent_dom)
                  have h_tc_bv : (BitVec.ofNat 64 st_h.core.tmp_cnt + 1).toNat =
                      st_h.core.tmp_cnt + 1 := by
                    change (BitVec.ofNat 64 st_h.core.tmp_cnt + 1#64).toNat = _
                    rw [bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                      bv64_ofNat_toNat (by omega)]
                  have h_idx1_c0 : (BitVec.ofNat 64 st_h.core.tmp_cnt <<< 1 + 1).toNat =
                      2 * st_h.core.tmp_cnt + 1 := by
                    simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                      show (1#64 : BitVec 64) = 1 from rfl] using h_idx1
                  pt_steps_nogrp
                  let st_p := { st_h with
                    core := { st_h.core with tmp_cnt := st_h.core.tmp_cnt + 1 }
                    scratch := { st_h.scratch with
                      work_stk2 := (st_h.scratch.work_stk2.set (2 * st_h.core.tmp_cnt)
                        (dom ^^^ 1#32)).set (2 * st_h.core.tmp_cnt + 1) l0_v } }
                  have hw_p := fullWitnessInv_nw_upd_watches hw_h hpush.1.core_ok rfl rfl rfl rfl
                    rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  have hm_p : (FullMem c st_p ⋆ R) m := by
                    dsimp only [st_h] at hshl_h h_tc_bv h_idx1_c0; dsimp only [st_p, st_h]
                    simpa only [hshl_h, h_tc_bv, h_idx1_c0,
                      show (1#32 : BitVec 32) = 1 from rfl] using hm
                  exact hdone_base st_p m hpush.1 hw_p hmrk_h (fullArenaVarsNodup_of_arena_eq hnd_h
                    rfl rfl) ⟨fullLastLearnedWf_of_refs_eq hext_h.1 rfl rfl, hext_h.2⟩ hdm hcl1 hcv
                    hfu hlm hws1 htr hpush.2 (hsw_h.with_nonwatch (k' := st_p.core) rfl rfl rfl rfl
                    fun _ h => h) hnot_false hoom0 hl0_0 hcr_ref hcr_ng hfals_h hl0_w hm_p
                · exact hdone_base st_h mh hlen_h hw_h hmrk_h hnd_h hext_h hdm hcl1 hcv hfu hlm
                    hws1 htr hhbr_h hsw_h hnot_false hoom0 hl0_0 hcr_ref hcr_ng hfals_h hl0_w hm_h
                · exact hdone_base st_h mh hlen_h hw_h hmrk_h hnd_h hext_h hdm hcl1 hcv hfu hlm
                    hws1 htr hhbr_h hsw_h hnot_false hoom0 hl0_0 hcr_ref hcr_ng hfals_h hl0_w hm_h)
    ·
        intro r m_fr hr_lo hr_hi ⟨hrepl_lt, _hrepl_nslt⟩ hm_fr
        rw [hcr64] at hr_hi hrepl_lt hm_fr
        let st_fr : FullState := { st with core := { st.core with
          arena := st.core.arena.set (cr_v.toNat + 1) (BitVec.ofNat 32 r) } }
        have hfr_set : st_fr.LengthsOk c ∧
            FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_fr).core ∧
            FullArenaVarsNodup st_fr ∧ FullExtScratchOk c st_fr ∧
            fullArenaClauseRefs st_fr = fullArenaClauseRefs st :=
          arena_setSrch_keep_inv hlen hw_nw hnd hext hcr_ref (srch := BitVec.ofNat 32 r)
        obtain ⟨hlen_fr, hw_fr, hnd_fr, hext_fr, hrefs_fr⟩ := hfr_set
        have hcr_ref_fr : cr_v.toNat ∈ fullArenaClauseRefs st_fr := hrefs_fr ▸ hcr_ref
        have hcr_sz_fr : fullArenaClauseSize st_fr cr_v.toNat =
            fullArenaClauseSize st cr_v.toNat := by
          unfold fullArenaClauseSize fullArenaClauseSizeCore; dsimp only [st_fr]
          rw [List.getElem?_set_ne (by omega)]
        have hcr_ng_fr : fullArenaClauseGarb st_fr cr_v.toNat = false := by
          unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [st_fr]
          rw [List.getElem?_set_ne (by omega)]; exact hcr_ng
        have hcr_arr_fr : cr_v.toNat + 3 + fullArenaClauseSize st_fr cr_v.toNat ≤
            st_fr.core.arena.length := by simpa [st_fr, hcr_sz_fr] using hcr_arr
        have hnot_fr : (st_fr.core.arena[cr_v.toNat + 4]'(by omega)).toNat = not_lit.toNat := by
          dsimp only [st_fr]; rw [List.getElem_set_ne (by omega)]; exact hnot_at
        have hl_repl_idx : cr_v.toNat + 3 + r < st_fr.core.arena.length := by omega
        have hrepl_get : st_fr.core.arena[cr_v.toNat + 3 + r]'hl_repl_idx =
            st.core.arena[cr_v.toNat + 3 + r]'(by omega) := by
          dsimp only [st_fr]; rw [List.getElem_set_ne (by omega)]
        let repl := st.core.arena[cr_v.toNat + 3 + r]'(by omega)
        have hrepl_lt' : repl.toNat < 2 * st.core.cur_vars := by
          simpa [repl, List.getElem?_eq_getElem (by omega : cr_v.toNat + 3 + r <
            st.core.arena.length)] using hrepl_lt
        have hrepl_ne_not : repl.toNat ≠ not_lit.toNat := by
          have hne := arena_lit_ne_of_nodup hnd_fr hcr_ref_fr hcr_ng_fr hcr_arr_fr
            (k1 := r) (k2 := 1) (by omega) (by omega) (by omega)
          intro heq; apply hne
          have hnot_fr' : (st_fr.core.arena[cr_v.toNat + 3 + 1]'(by omega)).toNat =
              not_lit.toNat := by
            simpa only [show cr_v.toNat + 3 + 1 = cr_v.toNat + 4 by omega] using hnot_fr
          rw [hnot_fr', hrepl_get]; exact heq
        have hr_32 : r < 2 ^ 32 := by
          have : fullArenaClauseSize st cr_v.toNat < 2 ^ 32 := BitVec.isLt _; omega
        have hr_idx64 : (cr_v.setWidth 64 + 3#64 + BitVec.ofNat 64 r).toNat =
            cr_v.toNat + 3 + r := by bv_omega
        have hcr4_idx64 : (cr_v.setWidth 64 + 4#64).toNat = cr_v.toNat + 4 := by bv_omega
        have hsw_lits := arena_swapLits_keep_inv hlen_fr hw_fr hnd_fr hext_fr
          hcr_ref_fr (k1 := 1) (k2 := r) (by omega) (by omega)
        dsimp only at hsw_lits
        have hl1_idx_fr : cr_v.toNat + 3 + 1 < st_fr.core.arena.length := by omega
        have hl1_sw_eq : st_fr.core.arena[cr_v.toNat + 3 + 1]'hl1_idx_fr = not_lit :=
          BitVec.eq_of_toNat_eq (by
            simpa only [show cr_v.toNat + 3 + 1 = cr_v.toNat + 4 by omega] using hnot_fr)
        have hl2_sw_eq : st_fr.core.arena[cr_v.toNat + 3 + r]'hl_repl_idx = repl := hrepl_get
        let ar_sw := (st_fr.core.arena.set (cr_v.toNat + 4) repl).set (cr_v.toNat + 3 + r) not_lit
        have har_sw_eq : (st_fr.core.arena.set (cr_v.toNat + 3 + 1)
            (st_fr.core.arena[cr_v.toNat + 3 + r]'hl_repl_idx)).set (cr_v.toNat + 3 + r)
            (st_fr.core.arena[cr_v.toNat + 3 + 1]'hl1_idx_fr) = ar_sw := by
          simp only [hl1_sw_eq, hl2_sw_eq]; rfl
        rw [har_sw_eq] at hsw_lits
        let st_sw : FullState := { st_fr with core := { st_fr.core with arena := ar_sw } }
        obtain ⟨hlen_sw, hw_sw, hnd_sw, hext_sw, hrefs_sw', _⟩ :=
          (hsw_lits : st_sw.LengthsOk c ∧
            FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_sw).core ∧
            FullArenaVarsNodup st_sw ∧ FullExtScratchOk c st_sw ∧
            fullArenaClauseRefs st_sw = fullArenaClauseRefs st_fr ∧
            ∀ r0 ∈ fullArenaClauseRefs st_fr, fullArenaClauseSize st_sw r0 =
              fullArenaClauseSize st_fr r0 ∧
              fullArenaClauseGarb st_sw r0 = fullArenaClauseGarb st_fr r0 ∧
              (fullArenaClauseLits st_sw r0).Perm (fullArenaClauseLits st_fr r0))
        have hrefs_sw : fullArenaClauseRefs st_sw = fullArenaClauseRefs st :=
          hrefs_sw'.trans hrefs_fr
        have hfr_r64 : (cr_v.setWidth 64 + 3#64 + BitVec.ofNat 64 r).toNat <
            st_fr.core.arena.length := by rw [hr_idx64]; exact hl_repl_idx
        have hfr_464 : (cr_v.setWidth 64 + 4#64).toNat < st_fr.core.arena.length := by
          rw [hcr4_idx64]; omega
        pt_step; pt_step
        · pt_steps_nogrp
          have hpr_sub : (p2_v - off_v).toNat = p2_v.toNat - off_v.toNat := by
            have := hsplit.q_ge; have := hsplit.q_le_p; bv_omega
          have hqr_sub : (q_v - off_v).toNat = q_v.toNat - off_v.toNat := by
            have := hsplit.q_ge; bv_omega
          have her_sub : (end_v - off_v).toNat = end_v.toNat - off_v.toNat := by
            have := hsplit.q_ge; have := hsplit.q_le_p; have := hsplit.p_le_end; bv_omega
          have hr_idx_c0 : (cr_v.setWidth 64 + 3 + BitVec.ofNat 64 r).toNat =
              cr_v.toNat + 3 + r := by bv_omega
          have hcr4_c0 : (cr_v.setWidth 64 + 4).toNat = cr_v.toNat + 4 := by bv_omega
          have hfr_r64_c0 : (cr_v.setWidth 64 + 3 + BitVec.ofNat 64 r).toNat <
              st_fr.core.arena.length := by rw [hr_idx_c0]; exact hl_repl_idx
          have hld_c0 : (st.core.arena.set (cr_v.toNat + 1) (BitVec.ofNat 32 r))[(cr_v.setWidth 64
              + 3 + BitVec.ofNat 64 r).toNat]'hfr_r64_c0 = repl := Option.some_inj.mp (by
            rw [← List.getElem?_eq_getElem hfr_r64_c0, hr_idx_c0]
            exact (List.getElem?_eq_getElem hl_repl_idx).trans (congrArg some hrepl_get))
          have hm_sw_ar : (FullMem c st_sw ⋆ R) m := by
            dsimp only [st_sw, st_fr, ar_sw]
            simp only [hr_idx_c0, hcr4_c0] at hm; rwa [show (st.core.arena.set (cr_v.toNat + 1)
              (BitVec.ofNat 32 r))[cr_v.toNat + 3 + r]'hl_repl_idx = repl from hrepl_get] at hm
          c0_call hWatchPush
          refine ⟨c, st_sw, R, rfl, hlen_sw,
            (hsplit.with_nonwatch (k' := st_sw.core) rfl rfl rfl rfl fun r0 hr0 => by
              rw [show fullArenaClauseRefsCore st_sw.core = fullArenaClauseRefs st_sw from rfl,
                hrefs_sw]; exact hr0).layout, fun h1 => (by cases h1),
            fun _ => ⟨fun heq => by
              have hlt : (l0_v &&& 0x7FFFFFFF#32).toNat < 0x80000000 := by rw [hw0l_eq]; omega
              rw [show l0_v &&& 0x7FFFFFFF#32 = 0xFFFFFFFF#32 from heq] at hlt
              exact absurd hlt (by decide),
              fun heq => absurd (heq ▸ hcr_lt) (by decide)⟩, hm_sw_ar, ?_⟩
          dsimp only
          intro pok wvec' wstk' wlen' wu' wsort' m_wp hlen_wp hlay_wp hpres_other
            hpok_t hpok_f hm_wp
          let st_wp : FullState := { st_sw with
            core := { st_sw.core with
              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
            scratch := { st_sw.scratch with wsort := wsort' } }
          have hnot_shl : (not_lit.setWidth 64 <<<
              ((1#32 : BitVec 32).signExtend 64).toNat).toNat = 2 * not_lit.toNat := by
            rw [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
              bv64_shl1_toNat (by rw [bv_c0_zext32_64]; omega), bv_c0_zext32_64]
          have hwvec_not : (not_lit.setWidth 64 <<<
              ((1#32 : BitVec 32).signExtend 64).toNat).toNat < st_wp.core.wvec.length := by
            rw [hlen_wp.core_ok.wvec_len, hnot_shl]; omega
          have hwvec_off : (st_wp.core.wvec[(not_lit.setWidth 64 <<<
              ((1#32 : BitVec 32).signExtend 64).toNat).toNat]'hwvec_not).toNat =
              fullWatchOffCore st_wp.core not_lit.toNat := by
            unfold fullWatchOffCore
            rw [← hnot_shl, List.getElem?_eq_getElem hwvec_not, Option.getD_some]
          have hsw_orig := hsplit.with_nonwatch (k' := st_sw.core) rfl rfl rfl rfl fun r0 hr0 => by
            rw [show fullArenaClauseRefsCore st_sw.core = fullArenaClauseRefs st_sw from rfl,
              hrefs_sw]; exact hr0
          simp only [hld_c0] at hpres_other hpok_t hpok_f
          dsimp only [fullWatchSize, fullWatchOff] at hpres_other hpok_t hpok_f
          change WatchStackLayout st_wp.core at hlay_wp
          have hap := hsw_orig.after_push (k' := st_wp.core) rfl hnot_lt' hrepl_lt' hrepl_ne_not rfl
            hlay_wp hw0l_msb hcr_lt (by change cr_v.toNat ∈ fullArenaClauseRefs st_sw
                                        rw [hrefs_sw]; exact hcr_ref) hpres_other
            (fun hpt => by
              have h2 := hpok_t hpt; exact ⟨h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2 rfl⟩)
            (fun hpf => (hpok_f hpf).1 hrepl_lt')
          dsimp only at hap
          have hend_wp_bd : fullWatchOffCore st_wp.core not_lit.toNat +
              (end_v.toNat - off_v.toNat) ≤ st_wp.core.wlen := by
            have := hlay_wp.bounds not_lit.toNat hnot_lt'; have := hap.sz_eq; omega
          have hwp_wcap := c.hwcap; unfold dimacsBound at hwp_wcap
          have hwp_wlen_le : st_wp.core.wlen ≤ c.wcap := hlen_wp.core_ok.wlen_le
          have hoff_lt64 : fullWatchOffCore st_wp.core not_lit.toNat + (end_v.toNat - off_v.toNat) <
              2 ^ 64 := by omega
          let off'_bv := (st_wp.core.wvec[(not_lit.setWidth 64 <<<
            ((1#32 : BitVec 32).signExtend 64).toNat).toNat]'hwvec_not).setWidth 64
          have hoff'_eq : off'_bv.toNat = fullWatchOffCore st_wp.core not_lit.toNat := by
            rw [bv_c0_zext32_64, hwvec_off]
          have hp2'_eq : (off'_bv + (p2_v - off_v)).toNat =
              off'_bv.toNat + (p2_v.toNat - off_v.toNat) := by
            rw [BitVec.toNat_add, hoff'_eq, hpr_sub,
              Nat.mod_eq_of_lt (by have := hsplit.p_le_end; omega)]
          have hq'_eq : (off'_bv + (q_v - off_v)).toNat =
              off'_bv.toNat + (q_v.toNat - off_v.toNat) := by
            rw [BitVec.toNat_add, hoff'_eq, hqr_sub,
              Nat.mod_eq_of_lt (by have := hsplit.q_le_p; have := hsplit.p_le_end; omega)]
          have hend'_eq : (off'_bv + (end_v - off_v)).toNat =
              off'_bv.toNat + (end_v.toNat - off_v.toNat) := by
            rw [BitVec.toNat_add, hoff'_eq, her_sub, Nat.mod_eq_of_lt hoff_lt64]
          have hap' : FullSplitWatchesInv F_cur st_wp.core not_lit.toNat off'_bv.toNat
              (off'_bv + (q_v - off_v)).toNat (off'_bv + (p2_v - off_v)).toNat
              (off'_bv + (end_v - off_v)).toNat := by
            simpa only [hoff'_eq, hp2'_eq, hq'_eq, hend'_eq] using hap
          pt_steps_nogrp
          · have hpok_eq : pok = true := by pt_clear_big; exact hc
            rw [hpok_eq] at *
            have hw_wp := fullWitnessInv_nw_upd_watches (s := st_sw) (s' := st_wp) hw_sw
              hlen_wp.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            have htr_wp := fullTrailRsnsExt_trans htr (fullTrailRsnsExt_congr rfl rfl rfl rfl)
            refine hJloop off'_bv (off'_bv + (p2_v - off_v)) (off'_bv + (q_v - off_v))
                (off'_bv + (end_v - off_v)) m_wp
              ⟨st_wp, hlen_wp, hw_wp, hmrk0, fullArenaVarsNodup_of_arena_eq hnd_sw rfl rfl,
                ⟨fullLastLearnedWf_of_refs_eq hext_sw.1 rfl rfl, hext_sw.2⟩, hdm, hcl1, hcv,
                hfu, hlm, hws1, htr_wp, fullHbrBufOkW_congr hhbr rfl rfl, hap', hnot_false,
                hoom0, hm_wp⟩ (by
                  rw [hend'_eq, hp2'_eq]; have := hsplit.q_ge; have := hsplit.q_le_p
                  have := hsplit.p_le_end; omega)
          · have hpok_eq : pok = false := by pt_clear_big; cases pok <;> simp_all
            have har_len_wp : st_wp.core.arena.length = st.core.arena.length := by
              simp [st_wp, st_sw, ar_sw, st_fr]
            have hsz_wp : fullArenaClauseSize st_wp cr_v.toNat =
                fullArenaClauseSize st cr_v.toNat := by
              unfold fullArenaClauseSize fullArenaClauseSizeCore; dsimp only [st_wp, st_sw, ar_sw,
                st_fr]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega)]
            have har_wp_bd : cr_v.toNat + 3 + fullArenaClauseSize st_wp cr_v.toNat ≤
                st_wp.core.arena.length := by rw [hsz_wp, har_len_wp]; exact hcr_arr
            have hsw_rb := arena_swapLits_keep_inv hlen_wp
              (fullWitnessInv_nw_upd_watches (s := st_sw) (s' := st_wp) hw_sw hlen_wp.core_ok
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
              (fullArenaVarsNodup_of_arena_eq hnd_sw rfl rfl)
              ⟨fullLastLearnedWf_of_refs_eq hext_sw.1 rfl rfl, hext_sw.2⟩
              (by change cr_v.toNat ∈ fullArenaClauseRefs st_sw; rw [hrefs_sw]; exact hcr_ref)
              (k1 := 1) (k2 := r) (by rw [hsz_wp]; omega) (hsz_wp ▸ hr_hi)
            dsimp only at hsw_rb
            have h4 : cr_v.toNat + 3 + 1 = cr_v.toNat + 4 := by omega
            have hr_1_eq : (st_wp.core.arena[cr_v.toNat + 3 + 1]'(by omega)) = repl := by
              apply Option.some_inj.mp; rw [← List.getElem?_eq_getElem (by omega)]
              dsimp only [st_wp, st_sw, ar_sw]
              rw [List.getElem?_set_ne (by omega), h4, List.getElem?_set_self]
              all_goals first | rfl | (simp [st_fr]; omega)
            have hr_r_eq : (st_wp.core.arena[cr_v.toNat + 3 + r]'(by omega)) = not_lit := by
              apply Option.some_inj.mp; rw [← List.getElem?_eq_getElem (by omega)]
              dsimp only [st_wp, st_sw, ar_sw]; rw [List.getElem?_set_self]
              all_goals first | rfl | (simp [st_fr]; omega)
            rw [hr_1_eq, hr_r_eq] at hsw_rb
            have hq_bd := hsplit.q_ge; have hqp_bd := hsplit.q_le_p; have hpe_bd := hsplit.p_le_end
            have hwstk_q' : (off'_bv + (q_v - off_v)).toNat < st_wp.core.wstk.length := by
              rw [hlen_wp.core_ok.wstk_len_arr, hq'_eq, hoff'_eq]; omega
            have hwstk_q1' : (off'_bv + (q_v - off_v)).toNat + 1 < st_wp.core.wstk.length := by
              rw [hlen_wp.core_ok.wstk_len_arr, hq'_eq, hoff'_eq]; omega
            have hq'2_64 : (off'_bv + (q_v - off_v)).toNat + 2 < 2 ^ 64 := by
              rw [hq'_eq, hoff'_eq]; omega
            have hq'1_bv : ((off'_bv + (q_v - off_v)) + 1).toNat =
                (off'_bv + (q_v - off_v)).toNat + 1 := by bv_omega
            have hwstk_q1'_bv : ((off'_bv + (q_v - off_v)) + 1#64).toNat <
                st_wp.core.wstk.length := by
              rw [show (1#64 : BitVec 64) = 1 from rfl, hq'1_bv]; exact hwstk_q1'
            have hp_prev'_eq : (off'_bv + (p2_v - off_v)).toNat =
                (off'_bv.toNat + (p_prev.toNat - off_v.toNat)) + 2 := by
              rw [hp2'_eq, hoff'_eq, hp2_eq]; omega
            have hap_prev : FullSplitWatchesInv F_cur st_wp.core not_lit.toNat off'_bv.toNat
                (off'_bv + (q_v - off_v)).toNat (off'_bv.toNat + (p_prev.toNat - off_v.toNat) + 2)
                (off'_bv + (end_v - off_v)).toNat := by simpa only [← hp_prev'_eq] using hap'
            let ar_rb := (st_wp.core.arena.set (cr_v.toNat + 4) not_lit).set (cr_v.toNat + 3 + r)
              repl
            have har_rb_eq : (st_wp.core.arena.set (cr_v.toNat + 3 + 1) not_lit).set
                (cr_v.toNat + 3 + r) repl = ar_rb := rfl
            rw [har_rb_eq] at hsw_rb
            let st_rb : FullState := { st_wp with core := { st_wp.core with arena := ar_rb } }
            have hap_rb := hap_prev.with_nonwatch (k' := st_rb.core) rfl rfl rfl rfl
              fun r0 hr0 => by
                change r0 ∈ fullArenaClauseRefs st_rb; rw [hsw_rb.2.2.2.2.1]; exact hr0
            have hw_wl := hap_rb.write_large hnot_lt' (by rw [hq'_eq, hoff'_eq]; omega) hwstk_q'
              hwstk_q1' hflag hcr_lt (by
                change cr_v.toNat ∈ fullArenaClauseRefs st_rb; rw [hsw_rb.2.2.2.2.1]
                change cr_v.toNat ∈ fullArenaClauseRefs st_sw; rw [hrefs_sw]; exact hcr_ref)
            let wstk_fin := (st_wp.core.wstk.set (off'_bv + (q_v - off_v)).toNat w0_v).set
              ((off'_bv + (q_v - off_v)).toNat + 1) cr_v
            let st_oom : FullState :=
              { st_rb with core := { st_rb.core with wstk := wstk_fin, oom := 1#64 } }
            have hw_wl' : FullSplitWatchesInv F_cur st_oom.core not_lit.toNat off'_bv.toNat
                ((off'_bv + (q_v - off_v)) + 2#64).toNat (off'_bv + (p2_v - off_v)).toNat
                (off'_bv + (end_v - off_v)).toNat := by
              have hq_p2 : ((off'_bv + (q_v - off_v)) + 2#64).toNat =
                  (off'_bv + (q_v - off_v)).toNat + 2 := by bv_omega
              simpa only [hq_p2, hp_prev'_eq] using
                hw_wl.with_nonwatch (k' := st_oom.core) rfl rfl rfl rfl fun _ h => h
            have hlen_oom : st_oom.LengthsOk c :=
              ⟨{ hsw_rb.1.core_ok with
                wstk_len_arr := (by
                  rw [List.length_set, List.length_set]; exact hlen_wp.core_ok.wstk_len_arr) },
                hsw_rb.1.scratch_ok⟩
            have hw_oom := fullWitnessInv_nw_upd_watches (s := st_rb) (s' := st_oom)
              (hsw_rb.2.1 : FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_rb).core)
              hlen_oom.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            have hwp_464 : (cr_v.setWidth 64 + 4).toNat < st_wp.core.arena.length := by
              rw [hcr4_c0, har_len_wp]; omega
            have hwp_r64 : (cr_v.setWidth 64 + 3 + BitVec.ofNat 64 r).toNat <
                st_wp.core.arena.length := by rw [hr_idx_c0, har_len_wp]; omega
            pt_steps_nogrp
            have hm_oom : (FullMem c st_oom ⋆ R) m := by
              simp only [st_oom, st_rb, st_wp, ar_rb, wstk_fin, hcr4_c0, hr_idx_c0] at hm ⊢
              have hoff'_defeq :
                  BitVec.setWidth 64 (wvec'[(BitVec.setWidth 64 not_lit <<< 1).toNat]'
                    (by simpa only [st_wp,
                      show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl] using
                      hwvec_not)) = off'_bv := rfl
              rw [hoff'_defeq, show (st.core.arena.set (cr_v.toNat + 1) (BitVec.ofNat 32 r))[
                cr_v.toNat + 3 + r]'hl_repl_idx = repl from hrepl_get, hq'1_bv] at hm
              rw [show (1#64 : BitVec 64) = 1 from rfl]; exact hm
            exact hJtail (off'_bv, off'_bv + (p2_v - off_v), (off'_bv + (q_v - off_v)) + 2#64,
                off'_bv + (end_v - off_v), true, ()) m
              ⟨st_oom, hlen_oom, hw_oom, hmrk0, fullArenaVarsNodup_of_arena_eq hsw_rb.2.2.1 rfl rfl,
                ⟨fullLastLearnedWf_of_refs_eq hsw_rb.2.2.2.1.1 rfl rfl, hsw_rb.2.2.2.1.2⟩,
                hdm, hcl1, hcv, hfu, hlm, hws1,
                fullTrailRsnsExt_trans htr (fullTrailRsnsExt_congr rfl rfl rfl rfl),
                fullHbrBufOkW_congr hhbr rfl rfl, hw_wl', fun _ => Or.inl (by simp [st_oom]),
                fun hf => (by cases hf), hm_oom⟩
        · exfalso; pt_clear_big
          have hsz32 : fullArenaClauseSize st cr_v.toNat < 2 ^ 32 := BitVec.isLt _
          have hto := congrArg BitVec.toNat (by assumption : BitVec.ofNat 64 r = 4294967295#64)
          rw [bv64_ofNat_toNat (by omega),
            show (4294967295#64).toNat = 4294967295 from rfl] at hto; omega

end PropLitProofHelpers

end FullProbeTransHelpers

end LeanQbe.T.Examples.Kissat.Full
