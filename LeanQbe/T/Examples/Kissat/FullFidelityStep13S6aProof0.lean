/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullM7BcpHot
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlush
public import LeanQbe.T.Examples.Kissat.FullM4Compact
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM7Walk
public import LeanQbe.T.Examples.Kissat.FullM7Search
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullLuckyLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard `S6a` — Proof Group 0

Callee-parametric `(Γ : Env)` Step-13 `Func.wp` lift theorems (`0` `@[expose]` on theorems/lemmas,
`0` `import all`, `0` cross-shard `S0..S5` imports, every theorem `<= 350` LOC, file `< 1,500` LOC):
1. `full_propagate_step13_wp` / `full_propagate_step13_s3_wp` (`FullM7BcpHot.full_bcp_hot_body`)
2. `full_flush_trail_step13_wp` (`FullM6CompactFlush.full_flush_trail_body`)
3. `full_compact_flush_step13_wp` (`FullFidelityStep9.full_compact_flush_body`)
4. `full_compact_step13_wp` (`FullM4Compact.full_compact_body`)
5. `full_rebuild_watches_nosort_fid_step13_wp`
   (`FullFidelityStep10.full_rebuild_watches_nosort_fid_body`)
6. `full_rebuild_watches_step13_wp` (`FullFidelityStep9.full_rebuild_watches_body`)
7. `full_parse_body_step13_wp` (`FullM6Orch.full_parse_body_body`)
8. `full_walk_step13_wp` (`FullM7Walk.full_walk_warmup_m7_body` — `full_walk` /
   `full_walk_warmup_m7`)
9. `full_simplify_m6_step13_wp` (`FullM6Orch.full_simplify_m6_body`)
10. `full_lucky_late_m7_step13_wp` (`FullM7Search.full_lucky_late_m7_body`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6CompactFlush
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7Walk
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ## 0. Shared Proof0 Tactics & Invariant Helpers -/

local macro "s6p0_strip" : tactic =>
  `(tactic| first | apply FullM6Hdr.m6h_strip_32_64 | apply FullM6Hdr.m6h_strip_8_32 |
    apply FullM6Hdr.m6h_strip_8_64)
local elab "s6p0_hsteps_ns" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000
local macro "s6p0_steps" : tactic =>
  `(tactic| (
    (try change LeanQbe.T.Func.wp _ _ _ _ _ _)
    (first | (s6p0_strip; repeat s6p0_strip) | skip)
    s6p0_hsteps_ns
    repeat (any_goals (s6p0_strip; repeat s6p0_strip); s6p0_hsteps_ns)))
local macro "s6p0_jnz" h:ident : tactic =>
  `(tactic| (rw [wp_jnz]; dsimp only [Arg.val]; refine ⟨fun $h => ?_, fun $h => ?_⟩))

private theorem s6p0_bv64_ofNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem s6p0_bv64_add1 {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

theorem s6p0_bv64_sub1 {x : BitVec 64} (hx : x ≠ 0#64) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hx0 : 0 < x.toNat := Nat.pos_of_ne_zero fun h0 => hx (BitVec.eq_of_toNat_eq h0)
  rw [BitVec.toNat_sub]; simp; omega

private theorem s6p0_sext8_64_eq0 (b : BitVec 8) (h : BitVec.signExtend 64 b = 0#64) :
    b = 0#8 := by
  revert b; decide

theorem s6p0_sext8_32_eq0 (b : BitVec 8) (h : BitVec.signExtend 32 b = 0#32) :
    b = 0#8 := by
  revert b; decide

theorem s6p0_arenaPermEq_trans {s0 s1 s2 : FullCoreState}
    (h01 : FullArenaPermEq s0 s1) (h12 : FullArenaPermEq s1 s2) :
    FullArenaPermEq s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, fun r hr => by
    have h1 : r ∈ fullArenaClauseRefsCore s1 := h01.2.1 ▸ hr
    have p1 := h01.2.2 r hr; have p2 := h12.2.2 r h1
    exact ⟨p2.1.trans p1.1, p2.2.1.trans p1.2.1, p2.2.2.trans p1.2.2⟩⟩

private theorem s6p0_arenaVarsNodup_perm {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hnd : FullArenaVarsNodup s) :
    FullArenaVarsNodup s' := by
  intro r hr hgb; change r ∈ fullArenaClauseRefs s' at hr
  have hmem : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rw [hap.2.1] at hr; exact hr
  have hperm := hap.2.2 r hmem; unfold fullArenaClauseGarb at hgb; rw [hperm.2.1] at hgb
  exact (List.Perm.map (fun x => x / 2) hperm.2.2).nodup_iff.mpr (hnd r hmem hgb)

private theorem s6p0_level0_unsat_fcur {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : (cnfOfClauses F_cur).Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_)
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

theorem s6p0_level0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat :=
  hw.ext_sound.2 (s6p0_level0_unsat_fcur hw hl0 hc)

private theorem s6p0_sparseInvW_of_bt0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                            trail_pos := tp', trail_end := te', propagated := prop',
                            cur_level := 0, unassigned := unass' }
      scratch := sc' } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    cur_level := 0, unassigned := unass' })
    (hll' : sc'.last_learned = s.scratch.last_learned)
    (hext' : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                              trail_pos := tp', trail_end := te', propagated := prop',
                              cur_level := 0, unassigned := unass' }
        scratch := sc' } :=
  ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1,
    FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll', hext'⟩ (fun _ hr => hr), hsp.2.2.2.2.2⟩

abbrev s6p0BcpSt (s : FullState) (vals' : List (BitVec 8))
    (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat) (unass' unfl' : BitVec 64)
    (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
    (wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64) (sc' : FullScratch) : FullState :=
  { s with
    core :=
      { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
        trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
        unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
        wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
        confl_lit0 := c0', confl_lit1 := c1', oom := oom' },
    scratch := sc' }

theorem s6p0_sparseInv_of_bcp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' : List (BitVec 32)} {te' prop' : Nat} {unass' unfl' : BitVec 64}
    {wvec' arena' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (hlen' : (s6p0BcpSt s vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena'
      wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc').LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur (s6p0BcpSt s vals' flags' lvl' rsns' trl' tp' te' prop' unass'
      unfl' wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc').core)
    (hperm' : FullArenaPermEq s.core (s6p0BcpSt s vals' flags' lvl' rsns' trl' tp' te' prop'
      unass' unfl' wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc').core)
    (hscp' : FullProbeScratchPres { s with scratch := { s.scratch with
      search_ticks := sc'.search_ticks, wsort := sc'.wsort, phases := sc'.phases,
      delayed := sc'.delayed } }
      (s6p0BcpSt s vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
        wlen' wu' fuel' ctype' cref' c0' c1' oom' sc')) :
    FullSparseInvW c F0 F_cur (s6p0BcpSt s vals' flags' lvl' rsns' trl' tp' te' prop' unass'
      unfl' wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc') :=
  have hsp0 := fullSparseInv_of_step13Bcp hsp.toSparse hlen' hw' hperm' hscp'
  ⟨hlen', hw', hsp0.2.1, hsp0.2.2.1, hsp0.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s6p0_unmapSlice_relocate {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} {lit : Nat} :
    ∀ {rem p p' : Nat}, (∀ i < rem, k'.wstk[p' + i]? = k.wstk[p + i]?) →
      FullM4Compact.CompactUnmapBinSliceOk ncv inv F_cur k lit p rem →
      FullM4Compact.CompactUnmapBinSliceOk ncv inv F_cur k' lit p' rem
  | 0, _, _, _, _ => .empty
  | _ + 1, _, _, heq, .bin hw hbin hns hlt hent htail =>
    .bin ((heq 0 (Nat.zero_lt_succ _)).trans hw) hbin hns hlt hent
      (s6p0_unmapSlice_relocate (fun i hi => by
        simpa [Nat.add_left_comm, Nat.add_assoc, Nat.add_comm] using heq (i + 1) (by omega)) htail)

private theorem s6p0_unmapBins_relocate {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {s s' : FullState}
    (h : FullM4Compact.CompactUnmapBinsOk ncv inv F_cur s.core)
    (hcv : s'.core.cur_vars = s.core.cur_vars) (hncv : ncv ≤ s.core.cur_vars)
    (hlay : WatchStackLayout s'.core)
    (hw : ∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
      ∀ idx < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + idx]? = s.core.wstk[fullWatchOff s l + idx]?) :
    FullM4Compact.CompactUnmapBinsOk ncv inv F_cur s'.core :=
  ⟨hlay, fun l hl1 hl2 => (hw l (by omega)).1.trans (h.empty_hi l hl1 (by omega)),
   fun l hl => by
     obtain ⟨hsz, hs⟩ := hw l (by omega)
     change FullM4Compact.CompactUnmapBinSliceOk ncv inv F_cur s'.core l (fullWatchOff s' l)
       (fullWatchSize s' l)
     rw [hsz]; exact s6p0_unmapSlice_relocate (fun i hi => hs i hi) (h.slices l hl)⟩

/-! ## 1. `full_propagate` (`FullM7BcpHot.full_bcp_hot_body`) -/

/-- Step-13 Option-A lift for `full_propagate` (`FullM7BcpHot.full_bcp_hot_body`) against
`step13BcpM6Spec`, calling `full_propagate_ignore_hot` with `step13PropagateIgnoreM6Spec`. -/
theorem full_propagate_step13_wp (Γ : Env)
    (hIgnHot : ∀ a m Q X, step13PropagateIgnoreM6Spec a m Q X →
      Γ "full_propagate_ignore_hot" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, step13BcpM6Spec a m Q X →
      Func.wp Γ FullM7BcpHot.full_bcp_hot_body a m Q X := by
  rw [show FullM7BcpHot.full_bcp_hot_body =
      fun _ _ ⟨v, ()⟩ =>
        Expr.call (as := [i64, i64]) (bs := [i64]) "full_propagate_ignore_hot"
          (Arg.var v, Arg.imm (t := i64) 0xFFFFFFFF#64, ())
          (fun ⟨x, ()⟩ => Expr.ret (Arg.var x, ())) by t_kernel_rfl]
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, ext, s, R, rfl, hcfg, hext, hlen, hw, hdm0, hm, hQ⟩
  unfold Func.wp
  refine wp_call_of_spec _ _
    (hIgnHot _ m _ _ ⟨c, F0, F_cur, ext, s, R, rfl, hcfg, hext, hlen, hw, hdm0, hm, ?_⟩)
  dsimp only
  intro r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
    wu' fuel' ctype' cref' c0' c1' oom' sc' m' hext' hinit' hlen' hw' htr' hperm' hscp' hrr' hdl'
    hprob' hdel' hfl' hr hr0 hr1 hr2 hnoop hm'
  exact hQ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
    wu' fuel' ctype' cref' c0' c1' oom' sc' m' hext' hinit' hlen' hw' htr' hperm' hscp' hrr' hdl'
    hprob' hdel' hfl' hr (fun h0 => let ⟨hp, _, ho, hf⟩ := hr0 h0; ⟨hp, ho, hf⟩)
    (fun h1 => let ⟨hf, ho, hc, _⟩ := hr1 h1; ⟨hf, ho, hc⟩) hr2 hnoop hm'

/-- Step-13 `S3` view of `full_propagate` (`step13BcpM6S3Spec`). -/
theorem full_propagate_step13_s3_wp (Γ : Env)
    (hIgnHot : ∀ a m Q X, step13PropagateIgnoreM6Spec a m Q X →
      Γ "full_propagate_ignore_hot" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, step13BcpM6S3Spec a m Q X →
      Func.wp Γ FullM7BcpHot.full_bcp_hot_body a m Q X :=
  fun _ _ _ _ h => full_propagate_step13_wp Γ hIgnHot _ _ _ _ (step13BcpM6Spec_to_s3 h)

/-! ## 2. `full_flush_trail` & `full_compact_flush` -/

/-- Step-13 Option-A lift for `full_flush_trail` (`FullM6CompactFlush.full_flush_trail_body`)
against `step13FlushTrailM6Spec`. -/
theorem full_flush_trail_step13_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, step13FlushTrailM6Spec a m Q X →
      Func.wp Γ full_flush_trail_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  obtain ⟨F_cur, hspw0⟩ := hinv.sparse.exists_witness
  have hcfg := hinv.cfgOk; have hext := hinv.extOk
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
    have := hspw0.1.core_ok.cur_vars_le; omega
  unfold Func.wp full_flush_trail_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hsplit
  · have hinc : s.core.inconsistent ≠ 0#64 := by c0_bound
    c0_hsteps
    exact hQ 20#64 ext s m hinv (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _) id
      (fun _ => hspw0.2.1.ext_sound.2 (hspw0.2.1.inconsistent_sound hinc))
      (fun h1 => absurd h1 (by decide)) (fun _ => Or.inr hinc) hm
  · have hinc0 : s.core.inconsistent = 0#64 := by c0_bound
    c0_hsteps_nogrp
    refine wp_join_group (ts := [])
      (fun () m1 => ∃ s1 : FullState, FullM6HdrInvW c F0 F_cur ext s1 ∧ s1.core.cur_level = 0 ∧
        s1.core.inconsistent = 0#64 ∧ s1.core.cur_vars = s.core.cur_vars ∧
        s1.core.fuel = s.core.fuel ∧ (s.core.cur_level = 0 → s1 = s) ∧
        (FullM6HdrMem c ext s1 ⋆ R) m1)
      (fun _ () m1 ⟨s1, hspw1, hcl1, hinc1, hcv1, hfu1, heq1, hm1⟩ => by
        rw [Blocks.get_here]
        refine wp_m6Hdr_focus_frame hm1 fun _ => ?_
        c0_hsteps_nogrp
        · c0_hsteps
          exact hQ 0#64 ext s1 _ hspw1.toInv (Or.inl rfl) hcv1 (by rw [hfu1]; exact Nat.le_refl _)
            (fun _ => hcl1) (fun h => by cases h) (fun h => by cases h)
            (fun _ => Or.inl hcl1) (fullM6HdrMem_unfocus_full (by assumption))
        · have hoom1 : s1.core.oom = 0#64 := by c0_bound
          refine wp_join_group (ts := [])
            (fun () m2 => ∃ (s2 : FullState) (ext2 : List (BitVec 64)),
              FullM6HdrInvW c F0 F_cur ext2 s2 ∧ s2.core.cur_level = 0 ∧
              s2.core.propagated = s2.core.trail_end ∧ s2.core.oom = 0#64 ∧
              s2.core.inconsistent = 0#64 ∧ s2.core.cur_vars = s.core.cur_vars ∧
              s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
                s2.core.fuel.toNat < s.core.fuel.toNat) ∧
              (FullM6HdrMem c ext2 s2 ⋆ R) m2)
            (fun _ () m2
                ⟨s2, ext2, hinv2, hcl2, hpt2, hoom2, hinc2, hcv2, hfu2, hstrict2, hm2⟩ => by
              rw [Blocks.get_here]
              refine wp_m6Hdr_focus_frame hm2 fun _ => ?_
              c0_hsteps; c0_split <;> first
                | (exfalso; have hne : s2.core.oom ≠ 0#64 := by c0_bound; exact hne hoom2)
                | skip
              have hspw2 := hinv2.sparseW
              let s3 : FullState :=
                { s2 with
                  core :=
                    { s2.core with
                      unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64 } }
              have hlen3 : s3.LengthsOk c :=
                ⟨{ hspw2.1.core_ok with vals_len := hspw2.1.core_ok.vals_len }, hspw2.1.scratch_ok⟩
              have hw3 : FullWitnessInv c F0 F_cur s3.core :=
                { fullWitnessInv_with_unflushed hspw2.2.1 0#64 with
                  arena := { hspw2.2.1.arena with len_ok := hspw2.2.1.arena.len_ok }
                  watches := hspw2.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
              have hspw3 : FullSparseInvW c F0 F_cur s3 :=
                ⟨hlen3, hw3, hspw2.2.2.1, hspw2.2.2.2.1, hspw2.2.2.2.2.1, hspw2.2.2.2.2.2⟩
              c0_hsteps
              exact hQ 1#64 ext2 s3 _ (FullM6HdrInvW.mk_inv hcfg hinv2.extOk hspw3).toInv
                (Or.inr (Or.inl rfl)) hcv2 hfu2 (fun _ => hcl2)
                (fun h20 => absurd h20 (by decide))
                (fun _ => ⟨hcl2, hpt2, hoom2, rfl, hinc2, hstrict2⟩)
                (fun hne => absurd rfl hne) (fullM6HdrMem_unfocus_full (by assumption)))
            (fun Jp hJp => by
              c0_hsplit
              · have hlt_pt : s1.core.propagated < s1.core.trail_end := by
                  have := hspw1.sparseW.1.core_ok.trail_end_le
                  have := hspw1.sparseW.1.core_ok.cur_vars_le
                  have := hspw1.sparseW.1.core_ok.propagated_le
                  have hbv : BitVec.ult (BitVec.ofNat 64 s1.core.propagated)
                      (BitVec.ofNat 64 s1.core.trail_end) = true := by c0_bound
                  simp only [BitVec.ult, BitVec.toNat_ofNat] at hbv
                  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hbv
                  exact of_decide_eq_true hbv
                have hspw1 := hspw1.sparseW
                c0_hsteps; c0_call hProp
                refine ⟨c, F0, F_cur, ext, s1, R, rfl, hcfg, hext, hspw1.1, hspw1.2.1,
                  hspw1.2.2.2.2.2, hm1, ?_⟩
                intro pr ext2 vals2 flags2 lvl2 rsns2 trl2 tp2 te2 prop2 unass2 unfl2 wvec2
                  arena2 wstk2 wlen2 wu2 fuel2 ctype2 cref2 c0_2 c1_2 oom2 sc2 m2 s2
                  hext2 _ hlen2 hw2 _ hperm2 hscp2 _ _ _ _ hfu2 hr_dom hpr0 hpr1 _ _ hm2
                have hspw2 := s6p0_sparseInv_of_bcp hspw1 hlen2 hw2 hperm2 hscp2
                have hinv2 := FullM6HdrInvW.mk_inv hcfg hext2 hspw2
                have hcl2 : s2.core.cur_level = 0 := hcl1
                have hcv2 : s2.core.cur_vars = s.core.cur_vars := hcv1
                have hfu2' : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  change fuel2.toNat ≤ s.core.fuel.toNat; rw [← hfu1]; exact hfu2
                refine wp_m6Hdr_focus_frame hm2 fun _ => ?_
                s6p0_steps; s6p0_jnz hpr1_j
                · have hpr1_eq : pr = 1#64 := by simpa using hpr1_j
                  obtain ⟨_, _, hc2⟩ := hpr1 hpr1_eq
                  have hunsat_fc := s6p0_level0_unsat_fcur hw2 hcl2 hc2
                  s6p0_steps
                  let s2' : FullState :=
                    { s2 with core := { s2.core with inconsistent := 1#64 } }
                  have hlen2' : s2'.LengthsOk c :=
                    ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
                  have hw2' : FullWitnessInv c F0 F_cur s2'.core :=
                    { hw2 with
                      inconsistent_sound := fun _ => hunsat_fc
                      arena := { hw2.arena with len_ok := hw2.arena.len_ok }
                      watches := hw2.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
                  have hspw2' : FullSparseInvW c F0 F_cur s2' :=
                    ⟨hlen2', hw2', hspw2.2.2.1, hspw2.2.2.2.1, hspw2.2.2.2.2.1,
                      hspw2.2.2.2.2.2⟩
                  exact hQ 20#64 ext2 s2' _ (FullM6HdrInvW.mk_inv hcfg hext2 hspw2').toInv
                    (Or.inr (Or.inr rfl)) hcv2 hfu2' (fun _ => hcl2)
                    (fun _ => hw2.ext_sound.2 hunsat_fc) (fun h1 => absurd h1 (by decide))
                    (fun _ => Or.inr (by intro h; simp [s2'] at h))
                    (fullM6HdrMem_unfocus_full (by assumption))
                · s6p0_steps; s6p0_jnz hpr2_j
                  · s6p0_steps
                    exact hQ 0#64 ext2 s2 _ hinv2.toInv (Or.inl rfl) hcv2 hfu2' (fun _ => hcl2)
                      (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide))
                      (fun _ => Or.inl hcl2) (fullM6HdrMem_unfocus_full (by assumption))
                  · have hpr_eq0 : pr = 0#64 := by simpa using hpr2_j
                    obtain ⟨hpt2, _, hstrict_fn⟩ := hpr0 hpr_eq0
                    s6p0_steps; s6p0_jnz hoom2_j
                    · s6p0_steps
                      exact hQ 0#64 ext2 s2 _ hinv2.toInv (Or.inl rfl) hcv2 hfu2' (fun _ => hcl2)
                        (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide))
                        (fun _ => Or.inl hcl2) (fullM6HdrMem_unfocus_full (by assumption))
                    · have hoom2 : s2.core.oom = 0#64 := by simpa using hoom2_j
                      have hstrict2 : s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
                          s2.core.fuel.toNat < s.core.fuel.toNat := by
                        intro hl0 hlt; have hs_eq := heq1 hl0; subst hs_eq
                        exact hstrict_fn hlt
                      s6p0_steps
                      exact hJp () _ ⟨s2, ext2, hinv2, hcl2, hpt2, hoom2, hinc1, hcv2, hfu2',
                        hstrict2, fullM6HdrMem_unfocus_full (by assumption)⟩
              · have heq_pt : s1.core.propagated = s1.core.trail_end := by
                  have := hspw1.sparseW.1.core_ok.trail_end_le
                  have := hspw1.sparseW.1.core_ok.cur_vars_le
                  have := hspw1.sparseW.1.core_ok.propagated_le
                  have hbv : BitVec.ult (BitVec.ofNat 64 s1.core.propagated)
                      (BitVec.ofNat 64 s1.core.trail_end) = false := by c0_bound
                  simp only [BitVec.ult, BitVec.toNat_ofNat] at hbv
                  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hbv
                  simp only [decide_eq_false_iff_not, not_lt] at hbv; omega
                have hstrict : s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
                    s1.core.fuel.toNat < s.core.fuel.toNat := fun hl0 hlt => by
                  rw [heq1 hl0] at heq_pt; omega
                c0_hsteps
                exact hJp () m1 ⟨s1, ext, hspw1, hcl1, heq_pt, hoom1, hinc1, hcv1,
                  by rw [hfu1]; exact Nat.le_refl _, hstrict, hm1⟩))
      (fun Jb hJb => by
        c0_hsplit
        · have hcl_ne0 : s.core.cur_level ≠ 0 := fun h0 =>
            (by c0_bound : BitVec.ofNat 64 s.core.cur_level ≠ 0#64) (by simp [h0])
          c0_hsteps; c0_call hBacktrack
          refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hspw0.1, hclv_lt, fun _ => by
              have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
              have := hspw0.1.core_ok.cur_vars_le; omega,
            hspw0.2.1.trail_lits_lt, hmf, ?_⟩
          intro vals' lvl' rsns' trl' tp' te' prop' unass' _ _ m1 s1 hlen1 _ _ hcl1 hpres1 _ _ _
            hwf1 _ hm1
          have hcl1' : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
          have hw1 := hwf1 F0 F_cur hspw0.2.1 (Nat.zero_le _)
          have hspw1 : FullSparseInvW c F0 F_cur s1 :=
            ⟨hlen1, hw1, hspw0.2.2.1, hspw0.2.2.2.1,
              FullExtScratchOk.of_pres hspw0.2.2.2.2.1 hpres1.1 (fun _ hr => hr),
              hspw0.2.2.2.2.2⟩
          c0_hsteps
          exact hJb () _ ⟨s1, FullM6HdrInvW.mk_inv hcfg hext hspw1, hcl1', hinc0, rfl, rfl,
            fun h0 => absurd h0 hcl_ne0, fullM6HdrMem_unfocus_full hm1⟩
        · have hcl0 : s.core.cur_level = 0 := by c0_bound
          c0_hsteps
          exact hJb () m ⟨s, FullM6HdrInvW.mk_inv hcfg hext hspw0, hcl0, hinc0, rfl, rfl,
            fun _ => rfl, hm⟩)

/-- Step-13 Option-A lift for `full_compact_flush` (`FullFidelityStep9.full_compact_flush_body`)
against `step13CompactFlushM6Spec`. -/
theorem full_compact_flush_step13_wp (Γ : Env)
    (hFlush : ∀ a m Q X, step13FlushTrailM6Spec a m Q X →
      Γ "full_flush_trail" [i64] [i64] a m Q X) :
    ∀ a m Q X, step13CompactFlushM6Spec a m Q X →
      Func.wp Γ FullFidelityStep9.full_compact_flush_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp FullFidelityStep9.full_compact_flush_body
  c0_hsteps; c0_call hFlush
  refine ⟨c, F0, ext, s, R, rfl, hinv, hm, ?_⟩
  intro fr ext1 s1 m1 hinv1 hfr hcv1 hfu1 _ h20_1 h1_1 _ hm1
  exact hQ fr ext1 s1 m1 hinv1 hfr hcv1 hfu1 h20_1
    (fun h1 => let ⟨hcl, hpt, hoo, huf, hin, _⟩ := h1_1 h1; ⟨hcl, hpt, hoo, huf, hin⟩) hm1

/-! ## 3. `full_compact` (`FullM4Compact.full_compact_body`) -/

/-- Step-13 Option-A lift for `full_compact` (`FullM4Compact.full_compact_body`) against
`step13CompactM6Spec`. -/
theorem full_compact_step13_wp (Γ : Env)
    (hfl : ∀ a m Q X, step13CompactFlushM6Spec a m Q X →
      Γ "full_compact_flush" [i64] [i64] a m Q X)
    (hmk : ∀ a m Q X, fullCompactMarkLiveSpec a m Q X → Γ "full_compact_mark_live" [i64] [] a m Q X)
    (hmp : ∀ a m Q X, fullCompactAssignMapSpec a m Q X →
      Γ "full_compact_assign_map" [i64] [i64] a m Q X)
    (hre : ∀ a m Q X, fullCompactRecordExtSpec a m Q X →
      Γ "full_compact_record_ext" [i64, i64, i64] [.bool] a m Q X)
    (hbn : ∀ a m Q X, fullCompactBinsSpec a m Q X →
      Γ "full_compact_bins" [i64, i64, i64] [] a m Q X)
    (hdf : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X)
    (har : ∀ a m Q X, fullCompactArenaSpec a m Q X →
      Γ "full_compact_arena" [i64, i64] [i64] a m Q X)
    (hvr : ∀ a m Q X, fullCompactVarsSpec a m Q X →
      Γ "full_compact_vars" [i64, i64, i64] [] a m Q X)
    (hvm : ∀ a m Q X, fullCompactVmtfSpec a m Q X →
      Γ "full_compact_vmtf" [i64, i64] [] a m Q X)
    (hhp : ∀ a m Q X, fullCompactHeapSpec a m Q X →
      Γ "full_compact_heap" [i64, i64] [] a m Q X)
    (hrw : ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Γ "full_rewatch_arena" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, step13CompactM6Spec a m Q X →
      Func.wp Γ full_compact_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_compact_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hsteps_nogrp; c0_hsplit
  · have hdm_ne : s.core.dense_mode ≠ 0#64 := by c0_bound
    exact absurd hinv.sparse.2.2.2.2 hdm_ne
  · c0_hsteps_nogrp; c0_call hfl
    refine ⟨c, F0, ext, s, R, rfl, hinv, fullM6HdrMem_unfocus_full hmf, ?_⟩
    intro cr ext1 s1 m1 hinv1 hcr hcv1 hfu1 h20_1 h1_1 hm1
    c0_hsteps_nogrp; c0_hsplit
    · have hne1 : cr ≠ 1#64 := by c0_bound
      rcases hcr with rfl | rfl | rfl
      · c0_hsteps_nogrp
        exact hQ 0#64 c ext1 s1 m1 (FullCfgCompat.refl c) hinv1 (Or.inl rfl)
          (by omega) hfu1 (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide)) hm1
      · exact absurd rfl hne1
      · c0_hsteps_nogrp
        exact hQ 20#64 c ext1 s1 m1 (FullCfgCompat.refl c) hinv1 (Or.inr (Or.inr rfl))
          (by omega) hfu1 (fun _ => h20_1 rfl) (fun h1 => absurd h1 (by decide)) hm1
    · have hcr1 : cr = 1#64 := by
        rcases hcr with rfl | rfl | rfl <;> first | rfl | contradiction
      obtain ⟨hcl1, hpt1, hoom1, hunf1, hinc1⟩ := h1_1 hcr1
      obtain ⟨F1, hw1⟩ := hinv1.sparse.1.witness
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      c0_hsteps_nogrp; c0_hsplit
      · exact hQ 1#64 c ext1 s1 _ (FullCfgCompat.refl c) hinv1 (Or.inr (Or.inl rfl))
          (by omega) hfu1 (fun h20 => absurd h20 (by decide)) (fun _ => hcl1)
          (fullM6HdrMem_unfocus_full (by assumption))
      · c0_hsteps_nogrp; c0_call hmk
        let spW1 : FullSparseInvW c F0 F1 s1 :=
          ⟨hinv1.sparse.lengths, hw1, hinv1.sparse.2.1, hinv1.sparse.2.2.1,
            hinv1.sparse.2.2.2.1, hinv1.sparse.2.2.2.2⟩
        refine ⟨c, F0, F1, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, spW1, hm1f, ?_⟩
        intro ws1' m2 s2 hsp2 hm2
        c0_hsteps_nogrp; c0_call hmp
        refine ⟨c, s2, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hsp2.1, hm2, ?_⟩
        intro ncv ws1_3 ws2_3 m3 s3 hlen3 hbij3 hm3
        have hncv_le : ncv.toNat ≤ s1.core.cur_vars := hbij3.ncv_le
        have hfu3 : s3.core.fuel.toNat ≤ s.core.fuel.toNat := hfu1
        c0_hsteps_nogrp; c0_hsplit
        · exact hQ 1#64 c ext1 s3 _ (FullCfgCompat.refl c)
            (FullM6HdrInv.mk_inv hinv1.cfgOk hinv1.extOk
              ⟨⟨hlen3, ⟨F1, hw1⟩⟩, hinv1.sparse.2.1, hinv1.sparse.2.2.1,
                hinv1.sparse.2.2.2.1, hinv1.sparse.2.2.2.2⟩)
            (Or.inr (Or.inl rfl)) (by change s1.core.cur_vars ≤ s.core.cur_vars; omega) hfu3
            (fun h20 => absurd h20 (by decide)) (fun _ => hcl1)
            (fullM6HdrMem_unfocus_full (by assumption))
        · c0_hsteps_nogrp; c0_call hre
          have hcv_bv : (BitVec.ofNat 64 s1.core.cur_vars).toNat = s1.core.cur_vars := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
              have := hinv1.sparse.lengths.core_ok.cur_vars_le; have := c.hmaxv
              unfold dimacsBound at *; omega)]
          refine ⟨c, s3, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen3, by rw [hcv_bv],
            by rw [hcv_bv]; exact hncv_le, hinv1.sparse.2.2.2.1.2, hm3, ?_⟩
          intro ok_re ext_stk4 ext_len4 m4 s4 hlen4 h_el4 hrec4 _ hm4
          c0_hsteps_nogrp; c0_hsplit
          · have hok_re_t : ok_re = true := by c0_bound
            subst hok_re_t
            let spW4 : FullSparseInvW c F0 F1 s4 := ⟨hlen4, hw1, hinv1.sparse.2.1,
              hinv1.sparse.2.2.1, ⟨hinv1.sparse.2.2.2.1.1, h_el4⟩, hinv1.sparse.2.2.2.2⟩
            c0_hsteps_nogrp; c0_call hbn
            refine ⟨c, F0, F1, s4, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, spW4, by rw [hcv_bv],
              by rw [hcv_bv]; exact hncv_le,
              (by have heq : _ := hcv_bv; rw [heq]; exact hbij3), hm4, ?_⟩
            intro wvec5 wstk5 wu5 nb5 m5 s5 hlen5 hbn5 hm5
            c0_hsteps_nogrp; c0_call hdf
            refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen5, hbn5.1, hm5, ?_⟩
            intro wvec6 wstk6 wlen6 wsort6 m6 s6 hlen6 hlay6 _ hwlist6 hm6
            c0_hsteps_nogrp; c0_call har
            refine ⟨c, F0, F1, ncv.toNat, s6, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen6,
              (by rw [hcv_bv]; exact hw1.ext_sound),
              (by dsimp only [s6, s5, s4, s3, s2]; exact ⟨hw1.arena.len_ok, hw1.arena.refs_wf,
                hw1.arena.shrk_term, hw1.arena.lits_lt, hw1.arena.entails⟩),
              hinv1.sparse.2.2.1, hinv1.sparse.2.2.2.2, hcl1,
              (by dsimp only [s6, s5, s4, s3, s2]; rw [hcv_bv]), (by rw [hcv_bv]; exact hncv_le),
              (by dsimp only [s6, s5, s4, s3, s2]; rw [hcv_bv]; exact hbij3), ?_, ?_, ?_, hm6, ?_⟩
            · intro l hl; exact hw1.vals_domain l (by rw [← hcv_bv]; exact hl)
            · intro l hl hfv
              obtain ⟨i, hi, heq⟩ := (hw1.vals_false_iff l (by rw [← hcv_bv]; exact hl)).mp hfv
              have hs := hw1.level0_sound i hi (by have := hw1.lvl_le i hi; omega)
              rwa [heq] at hs
            · exact s6p0_unmapBins_relocate hbn5 rfl
                (by dsimp only [s5, s4, s3, s2]; have := hcv_bv; omega) hlay6 hwlist6
            intro st_a ar7 al7 fred7 ni7 nr7 wvec7 wstk7 wlen7 wu7 nb7 oom7 ll7 ws7 m7 s7
              hlen7 hst_dom hu7 hoom7 hbin7 har7 hll7 hm7
            c0_hsteps_nogrp; c0_call hvr
            refine ⟨c, s7, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen7,
              by dsimp only [s7, s6, s5, s4, s3, s2]; rw [hcv_bv], by rw [hcv_bv]; exact hncv_le,
              fun nv hnv => (hbij3.inv_ok nv hnv).elim fun ov ⟨hov, _, _, hi, _⟩ => by
                have hmx := c.hmaxv; unfold dimacsBound at hmx; have : ov < s1.core.cur_vars := hov
                have := hinv1.sparse.lengths.core_ok.cur_vars_le
                rw [hi, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                exact hcv_bv.symm ▸ hov, hm7, ?_⟩
            intro c' vals8 fl8 lvl8 rsns8 ft0_8 fd0_8 sc8 m8 s8
              hcomp hlen8 hft0_8 hvals8 hpres8 hws1_8 hws2_8 hm8
            c0_hsteps_nogrp; c0_call hvm
            refine ⟨c', s8, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, hcomp.hdr.symm, hlen8,
              (hcomp.max_vars ▸ Nat.le_trans hncv_le hinv1.sparse.lengths.core_ok.cur_vars_le),
              hm8, ?_⟩
            intro sc9 m9 s9 hlen9 hpres9 hws1_9 hws2_9 hm9
            c0_hsteps_nogrp; c0_call hhp
            refine ⟨c', s9, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, hcomp.hdr.symm, hlen9,
              (hcomp.max_vars ▸ Nat.le_trans hncv_le hinv1.sparse.lengths.core_ok.cur_vars_le),
              hm9, ?_⟩
            intro sc10 m10 s10 hlen10 hpres10 hws1_10 hws2_10 hm10
            have hbin10 : CompactUnmapBinsOk ncv.toNat sc10.work_stk2 F1 s10.core := by
              rw [hws2_10, hws2_9, hws2_8]; exact hbin7.with_vars rfl (by omega) rfl rfl rfl
            have har10 : CompactArenaOk c' ncv.toNat sc10.work_stk2 F1 s10.core := by
              rw [hws2_10, hws2_9, hws2_8]; have ha := har7.with_core rfl rfl; exact ⟨ha.len_ok,
                ha.refs_wf, ha.no_shrk, ha.no_garb, ha.lits_lt, ha.nodup, ha.entails⟩
            have hlm10 := FullLitMarksClear.of_compat hcomp hinv1.sparse.2.1
            have hext10 : FullExtScratchOk c' s10 := ⟨FullLastLearnedWf.of_refs_subset hll7
              (hpres10.1.trans (hpres9.1.trans hpres8.1)) (fun _ hr => hr),
              by rw [hcomp.extend_cap, hpres10.2, hpres9.2, hpres8.2]; exact h_el4⟩
            have hcfg' := M6HdrCfgOk_of_le (hcomp.hdr ▸ M6HdrCfgOk_le hinv1.cfgOk)
            have hm10' : (FullMem c' s10 ⋆ (m6ExtMem (m6ExtAddr c'.hdr) ext1 ⋆ R)) m10 := by
              rw [hcomp.hdr]; exact hm10
            have hvals10 : ∀ l < 2 * s10.core.cur_vars, s10.core.vals[l]?.getD 0#8 = 0#8 := by
              intro l hl; have hcv10 : s10.core.cur_vars = ncv.toNat := rfl
              have := hncv_le; have := hinv1.sparse.lengths.core_ok.cur_vars_le
              have := hcomp.max_vars; have h1 : l < 2 * c'.max_vars := by omega
              have h2 : l < 2 * (BitVec.ofNat 64 s1.core.cur_vars).toNat := by rw [hcv_bv]; omega
              change vals8[l]?.getD 0#8 = 0#8; rw [hvals8 l h1 h2]; rfl
            have hft0 : (s10.core.frame_trail[0]?.getD 0#32).toNat = 0 := by
              have := hlen7.core_ok.frame_trail_len; dsimp [s10, s9, s8]
              rw [List.getElem?_set_self (by omega), Option.getD_some, hft0_8]; rfl
            have hnd10 : FullArenaVarsNodup s10 := fun r hr _ => har10.nodup r hr
            have hle_ncv : ncv.toNat ≤ s.core.cur_vars := by omega
            clear hm10; rw [← hcomp.hdr]; c0_hsteps_nogrp; c0_hsplit
            · have hst2 : st_a = 2#64 := by c0_bound
              let s11 := { s10 with core := { s10.core with inconsistent := 1#64 } }
              have hw11 : FullWitnessInv c' F0 [[]] s11.core := fullWitnessInv_compact_unsat
                (hu7 hst2) (hbin10.with_vars rfl (Nat.le_refl _) rfl rfl rfl)
                (har10.with_core rfl rfl) rfl hinv1.sparse.2.2.2.2 rfl rfl hft0 hvals10
              c0_hsteps; exact hQ 20#64 c' ext1 s11 _ hcomp (FullM6HdrInv.mk_inv hcfg' hinv1.extOk
                ⟨⟨⟨{ hlen10.core_ok with }, hlen10.scratch_ok⟩, ⟨_, hw11⟩⟩, hlm10, hnd10, hext10,
                  hinv1.sparse.2.2.2.2⟩) (Or.inr (Or.inr rfl)) hle_ncv hfu3 (fun _ => hu7 hst2)
                (fun h1 => absurd h1 (by decide)) (fullM6HdrMem_unfocus_full (by assumption))
            · have hst3 : st_a = 3#64 := by c0_bound
              let s11 := { s10 with core := { s10.core with oom := 1#64 } }
              have hwb := fullWitnessInv_compact_build hw1.ext_sound (ncv := ncv.toNat)
                (k := s11.core) (hbin10.with_vars rfl (Nat.le_refl _) rfl rfl rfl)
                (har10.with_core rfl rfl) rfl hinc1 hinv1.sparse.2.2.2.2 rfl rfl hft0 hvals10
              c0_hsteps; exact hQ 0#64 c' ext1 s11 _ hcomp (FullM6HdrInv.mk_inv hcfg' hinv1.extOk
                ⟨⟨⟨{ hlen10.core_ok with }, hlen10.scratch_ok⟩, ⟨_, hwb.1⟩⟩, hlm10, hnd10, hext10,
                  hinv1.sparse.2.2.2.2⟩) (Or.inl rfl) hle_ncv hfu3 (fun h => absurd h (by decide))
                (fun h => absurd h (by decide)) (fullM6HdrMem_unfocus_full (by assumption))
            · have hst0 : st_a = 0#64 := by
                rcases hst_dom with rfl | rfl | rfl <;> first | rfl | contradiction
              obtain ⟨hw10, _⟩ := fullWitnessInv_compact_build hw1.ext_sound hbin10 har10 rfl
                hinc1 hinv1.sparse.2.2.2.2 rfl rfl hft0 hvals10
              c0_hsteps_nogrp; c0_call hrw; refine ⟨c', F0, stateClausesCore s10.core, s10,
                m6ExtMem (m6ExtAddr c'.hdr) ext1 ⋆ R, rfl, hlen10, hw10, hinv1.sparse.2.2.2.2,
                by have := hlen10.core_ok.arena_len_le; have := c'.harena; unfold dimacsBound at *
                   rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
                fun r hr => ⟨har10.no_garb r hr, har10.no_shrk r hr⟩, hm10', ?_⟩
              intro ok11 ar11 wvec11 wstk11 wlen11 wu11 oom11 ws11 m11 _ hlen11 hw11 hnd11
                hrefs hoom_f _ hm11
              let s11 : FullState := { s10 with
                core := { s10.core with
                  arena := ar11, wvec := wvec11, wstk := wstk11, wlen := wlen11,
                  wusable := wu11, oom := oom11 },
                scratch := { s10.scratch with wsort := ws11 } }
              have hsp11 : FullSparseInv c' F0 s11 := ⟨⟨hlen11, ⟨_, hw11⟩⟩, hlm10, hnd11 hnd10,
                FullExtScratchOk.of_pres hext10 ⟨rfl, rfl⟩ (fun r hr => by rw [hrefs]; exact hr),
                hinv1.sparse.2.2.2.2⟩
              c0_hsteps_nogrp; c0_hsplit
              · have hok_t : ok11 = true := by c0_bound
                c0_hsteps; exact hQ 1#64 c' ext1 s11 _ hcomp (FullM6HdrInv.mk_inv hcfg' hinv1.extOk
                  hsp11) (Or.inr (Or.inl rfl)) hle_ncv hfu3 (fun h20 => absurd h20 (by decide))
                  (fun _ => rfl) (fullM6HdrMem_unfocus_full hm11)
              · have hok_f : ok11 = false := by c0_bound
                have hoom_1 := hoom_f hok_f
                exact hQ 0#64 c' ext1 s11 _ hcomp (FullM6HdrInv.mk_inv hcfg' hinv1.extOk hsp11)
                  (Or.inl rfl) hle_ncv hfu3 (fun h20 => absurd h20 (by decide))
                  (fun h1 => absurd h1 (by decide))
                  (fullM6HdrMem_unfocus_full (by simpa [s11, hoom_1] using (by assumption)))
          · have hok_re_f : ok_re = false := by c0_bound
            obtain ⟨_, hel_eq⟩ := (hrec4 hok_re_f); c0_hsteps; exact hQ 1#64 c ext1 s4 _
              (FullCfgCompat.refl c) (FullM6HdrInv.mk_inv hinv1.cfgOk hinv1.extOk
                ⟨⟨hlen4, ⟨F1, hw1⟩⟩, hinv1.sparse.2.1, hinv1.sparse.2.2.1,
                  FullExtScratchOk.of_pres hinv1.sparse.2.2.2.1 ⟨rfl, hel_eq⟩ (fun _ hr => hr),
                  hinv1.sparse.2.2.2.2⟩) (Or.inr (Or.inl rfl))
              (by change s1.core.cur_vars ≤ s.core.cur_vars; omega) hfu3
              (fun h20 => absurd h20 (by decide)) (fun _ => hcl1) (fullM6HdrMem_unfocus_full hm4)

/-! ## 4. `full_rebuild_watches_nosort_fid` & `full_rebuild_watches` -/

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
