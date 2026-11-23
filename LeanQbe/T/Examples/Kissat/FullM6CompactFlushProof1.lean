module

public import LeanQbe.T.Examples.Kissat.FullM6CompactFlush
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat M6 Compact, Root Trail Flush & Binary Dedup Proofs — Part 1

Parametric `(Γ : Env)` `Func.wp` UNSAT-only proofs (`0` SAT/model proofs):
1. `full_flush_trail_wp` (`fullFlushTrailSpec`): clean root-level backtrack + propagate +
   `unflushed`/`confl_*` reset with strict `fuel` decrease when propagating at root.
2. `full_compact_needed_m6cf_wp` (`fullCompactNeededM6Spec`): upstream `10%` compaction trigger
   (`dead * 10 > cur_vars`, `cur_level = 0`, `dense_mode = 0`).
3. `full_compact_flush_m6cf_wp` (`FullM4Compact.fullCompactFlushSpec`): fixpoint root flush +
   arena sweep loop over `full_flush_trail`.
4. `full_extend_push2_m6cf_tmk_wp` / `full_extend_push2_m6cf_wp`: root-false skip in binary
   witness push (`FullFastBveBudgets.fullExtendPush2TmkSpec`, `Full.fullExtendPush2Spec`).
5. `full_extend_push_cl_m6cf_tmk_wp` / `full_extend_push_cl_m6cf_wp`: root-false skip in clause
   witness push (`FullFastBveBudgets.fullExtendPushClTmkSpec`, `Full.fullExtendPushClSpec`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullM6CompactFlush

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM4Compact
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. New M6 Contracts (`fullFlushTrailSpec`, `fullCompactNeededM6Spec`) -/

/-- Specification for `full_flush_trail`: backtracks to level 0, checks OOM, propagates any
unpropagated root units (setting `inconsistent = 1` on conflict), and clears `unflushed` and
conflict metadata while preserving `FullSparseInv`. -/
@[expose] public def fullFlushTrailSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s'.core.cur_level = 0 ∧ s'.core.propagated = s'.core.trail_end ∧
        s'.core.oom = 0#64 ∧ s'.core.unflushed = 0#64 ∧ s'.core.inconsistent = 0#64 ∧
        (s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
          s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r ≠ 1#64 → s'.core.cur_level = 0 ∨ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Specification for `full_compact_needed_m6cf`: read-only check returning `true` only at root
level in sparse mode when `0 < cur_vars` and strictly more than `10%` of variables are inactive
(`10 * (cur_vars - unassigned) > cur_vars`). -/
@[expose] public def fullCompactNeededM6Spec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ res : Bool,
      (res = true → s.core.cur_level = 0 ∧ s.core.dense_mode = 0#64 ∧
        0 < s.core.cur_vars ∧ s.core.unassigned.toNat < s.core.cur_vars ∧
        s.core.cur_vars < 10 * (s.core.cur_vars - s.core.unassigned.toNat)) →
      Q (res, ()) m

/-! ## 2. Shared Sparse/Witness Transition Helpers -/

section SharedHelpers

public theorem m6cf_fullWitnessInv_with_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with inconsistent := inc' } :=
  { hw with
    inconsistent_sound := fun _ => hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

public theorem m6cf_fullSparseInvW_with_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    m6cf_fullWitnessInv_with_inc hsp.2.1 hu inc',
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

public theorem m6cf_fullSparseInvW_with_meta {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (unfl' cref' ctype' : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with unflushed := unfl', confl_ref := cref',
                                     confl_type := ctype' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    { hsp.2.1 with
      arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
      watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

public theorem m6cf_fullMem_cast {c : FullCfg} {s s' : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (heq : s = s') : (FullMem c s' ⋆ R) m :=
  heq ▸ hm

public theorem m6cf_level0_fcur_unsat_of_confl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) :
    (cnfOfClauses F_cur).Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
  · refine unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_)
    right
    have hlt := hw.arena.lits_lt _ href hng l hl
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
    rwa [heq] at hs

public theorem m6cf_fullSparseInvW_after_bt0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hpres : FullExtScratchPres s s') (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm : s'.core.dense_mode = s.core.dense_mode) :
    FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
      change r ∈ fullArenaClauseRefsCore s'.core at hr
      unfold fullArenaClauseRefsCore at hr ⊢; rw [har, hal] at hr; exact hr
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
      rwa [har] at hng
    have hl : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hl]; exact hsp.2.2.2.1 r hr0 hng0
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [har, hal]; exact href

public theorem m6cf_fullSparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := by rw [← hperm.2.1]; exact hr
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 r hr0
    exact (hsp.2.2.2.1 r hr0 (hgb.symm.trans hng)).perm (hp.symm.map (· / 2))
  · exact hsp.2.2.2.2.1.of_pres hpres fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr

public theorem m6cf_fullSparseInvW_after_sweep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hnd' : FullArenaVarsNodup s') (hll' : FullLastLearnedWf s')
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) : FullSparseInvW c F0 F_cur s' :=
  ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩,
    hnd', ⟨hll', hext' ▸ hsp.2.2.2.2.1.2⟩, hdm.trans hsp.2.2.2.2.2⟩

end SharedHelpers

/-! ## 3. `full_flush_trail_wp` (`fullFlushTrailSpec`) -/

section FlushTrailProof

public theorem full_flush_trail_del_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateDelSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullFlushTrailSpec a m Q X → Func.wp Γ full_flush_trail_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hm, hQ⟩
  obtain ⟨F_cur, hspw0⟩ := hsp0.exists_witness
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
    have := hspw0.1.core_ok.cur_vars_le; omega
  unfold Func.wp full_flush_trail_body
  c0_hsplit
  · -- `h->inconsistent != 0`: return 20 immediately
    have hinc : s.core.inconsistent ≠ 0#64 := by c0_bound
    c0_hsteps
    exact hQ 20#64 s m hsp0 (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _) id
      (fun _ => hspw0.2.1.ext_sound.2 (hspw0.2.1.inconsistent_sound hinc))
      (fun h1 => absurd h1 (by decide)) (fun _ => Or.inr hinc) hm
  · -- `h->inconsistent == 0`
    have hinc0 : s.core.inconsistent = 0#64 := by c0_bound
    c0_hsteps_nogrp
    refine wp_join_state0 (α := FullState)
      (fun s1 m1 =>
        FullSparseInvW c F0 F_cur s1 ∧ s1.core.cur_level = 0 ∧
        s1.core.inconsistent = 0#64 ∧ s1.core.cur_vars = s.core.cur_vars ∧
        s1.core.fuel = s.core.fuel ∧
        (s.core.cur_level = 0 → s1 = s) ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
    · rintro _ s1 m1 ⟨hspw1, hcl1, hinc1, hcv1, hfu1, heq1, hm1⟩
      clear hm hsp0 hspw0
      have hprop_le1 := hspw1.1.core_ok.propagated_le
      have hte_le1 := hspw1.1.core_ok.trail_end_le
      have hcv_le1 := hspw1.1.core_ok.cur_vars_le
      c0_hsplit
      · -- `h->oom != 0`: return 0
        c0_hsteps
        exact hQ 0#64 s1 m1 hspw1.toSparse (Or.inl rfl) hcv1 (by rw [hfu1]; exact Nat.le_refl _)
          (fun _ => hcl1) (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide))
          (fun _ => Or.inl hcl1) hm1
      · have hoom1 : s1.core.oom = 0#64 := by c0_bound
        c0_hsteps_nogrp
        refine wp_join_state0 (α := FullState)
          (fun s2 m2 =>
            FullSparseInvW c F0 F_cur s2 ∧ s2.core.cur_level = 0 ∧
            s2.core.propagated = s2.core.trail_end ∧ s2.core.oom = 0#64 ∧
            s2.core.inconsistent = 0#64 ∧ s2.core.cur_vars = s.core.cur_vars ∧
            s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
              s2.core.fuel.toNat < s.core.fuel.toNat) ∧ (FullMem c s2 ⋆ R) m2) ?_ ?_
        · rintro _ s2 m2 ⟨hspw2, hcl2, hpr2, hoom2, hinc2, hcv2, hfu2, hstrict2, hm2⟩
          c0_hsteps
          let s3 : FullState :=
            { s2 with core := { s2.core with unflushed := 0#64, confl_ref := 0xFFFFFFFF#64,
                                             confl_type := 0#64 } }
          have hspw3 := m6cf_fullSparseInvW_with_meta hspw2 0#64 0xFFFFFFFF#64 0#64
          exact hQ 1#64 s3 _ hspw3.toSparse (Or.inr (Or.inl rfl)) hcv2 hfu2 (fun _ => hcl2)
            (fun h20 => absurd h20 (by decide))
            (fun _ => ⟨hcl2, hpr2, hoom2, rfl, hinc2, hstrict2⟩)
            (fun hne => absurd rfl hne) hm
        · intro Jp hJp
          c0_hsplit
          · -- `h->propagated < h->trail_end`: call `full_propagate`
            have hlt_pt : s1.core.propagated < s1.core.trail_end := by c0_bound
            c0_hsteps; c0_call hProp
            refine ⟨c, F0, F_cur, s1, R, rfl, hspw1.1, hspw1.2.1, hspw1.2.2.2.2.2, hm1, ?_⟩
            intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel2 _ _ _ _ _ _ _ _ delayed2 m2 s2
              hlen2 hw2 _ hperm2 hfl2 _ hpr0 hpr1 _ _ hm2
            have hspw2 := m6cf_fullSparseInvW_of_perm hspw1 hlen2 hw2 hperm2 rfl rfl rfl ⟨rfl, rfl⟩
            have hcl2 : s2.core.cur_level = 0 := hcl1
            have hcv2 : s2.core.cur_vars = s.core.cur_vars := hcv1
            have hfu2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by
              dsimp only [s2]; rw [← hfu1]; exact hfl2
            c0_hsplit
            · -- `pr == 1`: root conflict -> set `inconsistent = 1`, return 20
              have hpr_eq : pr = 1#64 := by c0_bound
              have hu_fc := m6cf_level0_fcur_unsat_of_confl hw2 hcl2 (hpr1 hpr_eq).2.2
              have hspw_inc := m6cf_fullSparseInvW_with_inc hspw2 hu_fc 1#64
              c0_hsteps
              exact hQ 20#64 { s2 with core := { s2.core with inconsistent := 1#64 } } _
                hspw_inc.toSparse (Or.inr (Or.inr rfl)) hcv2 hfu2 (fun _ => hcl2)
                (fun _ => hw2.ext_sound.2 hu_fc) (fun h1 => absurd h1 (by decide))
                (fun _ => Or.inl hcl2) hm
            · c0_hsplit
              · -- `pr != 0`: return 0
                c0_hsteps
                exact hQ 0#64 s2 m2 hspw2.toSparse (Or.inl rfl) hcv2 hfu2 (fun _ => hcl2)
                  (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide))
                  (fun _ => Or.inl hcl2) hm2
              · c0_hsplit
                · -- `oom != 0`: return 0
                  c0_hsteps
                  exact hQ 0#64 s2 m2 hspw2.toSparse (Or.inl rfl) hcv2 hfu2 (fun _ => hcl2)
                    (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide))
                    (fun _ => Or.inl hcl2) hm2
                · -- `pr == 0` and `oom == 0`
                  have hpr_eq0 : pr = 0#64 := by c0_bound
                  obtain ⟨hpt2, hoom2_fn, hstrict_fn⟩ := hpr0 hpr_eq0
                  have hoom2 : s2.core.oom = 0#64 := hoom2_fn hoom1
                  have hstrict2 : s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
                      s2.core.fuel.toNat < s.core.fuel.toNat := by
                    intro _ _
                    have hlt := hstrict_fn hlt_pt
                    dsimp only [s2]; rw [← hfu1]; exact hlt
                  c0_hsteps
                  exact hJp s2 m2 ⟨hspw2, hcl2, hpt2, hoom2, hinc1, hcv2, hfu2, hstrict2, hm2⟩
          · -- `h->propagated >= h->trail_end`: already propagated
            have hge_pt : s1.core.trail_end ≤ s1.core.propagated := by c0_bound
            have heq_pt : s1.core.propagated = s1.core.trail_end := by omega
            have hstrict : s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
                s1.core.fuel.toNat < s.core.fuel.toNat := fun hcl0 hlt => by
              have hs1 := heq1 hcl0; rw [hs1] at heq_pt; omega
            c0_hsteps
            exact hJp s1 m1 ⟨hspw1, hcl1, heq_pt, hoom1, hinc1, hcv1,
              by rw [hfu1]; exact Nat.le_refl _, hstrict, hm1⟩
    · intro Jb hJb
      c0_hsplit
      · -- `cur_level != 0`: call `full_backtrack(h, 0)`
        have hcl_ne0 : s.core.cur_level ≠ 0 := fun h0 =>
          (by c0_bound : BitVec.ofNat 64 s.core.cur_level ≠ 0#64) (by simp [h0])
        c0_hsteps; c0_call hBacktrack
        refine ⟨c, s, R, rfl, hspw0.1, hclv_lt, fun _ => by
            have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
            have := hspw0.1.core_ok.cur_vars_le; omega,
          hspw0.2.1.trail_lits_lt, hm, ?_⟩
        intro _ _ _ _ _ _ _ _ _ _ m1 s1 hlen1 _ _ hcl1 hpres1 _ _ _ hwf1 _ hm1
        have hcl1' : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
        have hw1 := hwf1 F0 F_cur hspw0.2.1 (Nat.zero_le _)
        have hspw1 := m6cf_fullSparseInvW_after_bt0 hspw0 hlen1 hw1 hpres1.1 rfl rfl rfl rfl rfl
        c0_hsteps
        exact hJb s1 m1 ⟨hspw1, hcl1', hinc0, rfl, rfl, fun h0 => absurd h0 hcl_ne0, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by c0_bound
        c0_hsteps
        exact hJb s m ⟨hspw0, hcl0, hinc0, rfl, rfl, fun _ => rfl, hm⟩

public theorem full_flush_trail_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullFlushTrailSpec a m Q X → Func.wp Γ full_flush_trail_body a m Q X :=
  full_flush_trail_del_wp Γ hBacktrack
    (fun a m Q X h => hProp a m Q X (fullPropagateSpec_of_del h))

end FlushTrailProof

/-! ## 4. `full_compact_needed_m6cf_wp` (`fullCompactNeededM6Spec`) -/

section CompactNeededProof

public theorem full_compact_needed_m6cf_wp (Γ : Env) :
    ∀ a m Q X, fullCompactNeededM6Spec a m Q X →
      Func.wp Γ full_compact_needed_m6cf_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl_lt, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_compact_needed_m6cf_body
  c0_hsteps <;>
    first
    | (exact hQ false fun hf => Bool.noConfusion hf)
    | (refine hQ _ fun hres => ?_
       have hcl0 : s.core.cur_level = 0 := by c0_bound
       have hdm0 : s.core.dense_mode = 0#64 := by c0_bound
       have hcv_pos : 0 < s.core.cur_vars := by c0_bound
       have hun_lt : s.core.unassigned.toNat < s.core.cur_vars := by c0_bound
       have h10 : s.core.cur_vars < 10 * (s.core.cur_vars - s.core.unassigned.toNat) := by
         have hsub : (BitVec.ofNat 64 s.core.cur_vars - s.core.unassigned).toNat =
             s.core.cur_vars - s.core.unassigned.toNat := by bv_omega
         have hmul : ((BitVec.ofNat 64 s.core.cur_vars - s.core.unassigned) * 10#64).toNat =
             (s.core.cur_vars - s.core.unassigned.toNat) * 10 := by
           rw [BitVec.toNat_mul, hsub, show (10#64 : BitVec 64).toNat = 10 from rfl,
             Nat.mod_eq_of_lt (by omega)]
         have hgt : BitVec.ult (BitVec.ofNat 64 s.core.cur_vars)
             ((BitVec.ofNat 64 s.core.cur_vars - s.core.unassigned) * 10#64) = true := hres
         rw [BitVec.ult_iff_toNat_lt, hmul, BitVec.toNat_ofNat,
           Nat.mod_eq_of_lt (by omega)] at hgt
         omega
       exact ⟨hcl0, hdm0, hcv_pos, hun_lt, h10⟩)

end CompactNeededProof

/-! ## 5. `full_compact_flush_m6cf_wp` (`FullM4Compact.fullCompactFlushSpec`) -/

section CompactFlushProof

public theorem full_compact_flush_m6cf_wp (Γ : Env)
    (hFlush : ∀ a m Q X, fullFlushTrailSpec a m Q X →
      Γ "full_flush_trail" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCompactFlushSpec a m Q X →
      Func.wp Γ full_compact_flush_m6cf_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hm, hQ⟩
  unfold Func.wp full_compact_flush_m6cf_body
  c0_hsteps; c0_call hFlush
  refine ⟨c, F0, s, R, rfl, hsp0, hm, ?_⟩
  intro fr s1 m1 hsp1 hfr hcv1 hfu1 _ h20_1 h1_1 _ hm1
  c0_hsplit
  · have hne1 : fr ≠ 1#64 := by c0_bound
    c0_hsteps
    exact hQ fr s1 m1 hsp1 hfr hcv1 hfu1 h20_1 (fun h1 => absurd h1 hne1) hm1
  · have hfr1 : fr = 1#64 := by c0_bound
    obtain ⟨hcl1, hpt1, hoom1, hunfl1, hinc1, _⟩ := h1_1 hfr1
    c0_hsteps_nogrp
    refine wp_join_state0 (α := FullState)
      (fun sE mE =>
        FullSparseInv c F0 sE ∧ sE.core.cur_vars = s.core.cur_vars ∧
        sE.core.fuel.toNat ≤ s.core.fuel.toNat ∧ sE.core.cur_level = 0 ∧
        sE.core.propagated = sE.core.trail_end ∧ sE.core.oom = 0#64 ∧
        sE.core.inconsistent = 0#64 ∧ (FullMem c sE ⋆ R) mE)
      (fun _ sE mE ⟨hspE, hcvE, hfuE, hclE, hptE, hoomE, hincE, hmE⟩ => by
        obtain ⟨F_curE, hspwE⟩ := hspE.exists_witness
        c0_hsteps
        let sF : FullState := { sE with core := { sE.core with unflushed := 0#64 } }
        have hspwF : FullSparseInvW c F0 F_curE sF :=
          m6cf_fullSparseInvW_with_meta hspwE 0#64 sE.core.confl_ref sE.core.confl_type
        exact hQ 1#64 sF _ hspwF.toSparse (Or.inr (Or.inl rfl)) hcvE hfuE
          (fun h20 => absurd h20 (by decide))
          (fun _ => ⟨hclE, hptE, hoomE, rfl, hincE⟩) hm)
      (fun Jbrk hJbrk => ?_)
    refine wp_while_state0 (α := FullState) (μ := fun st => st.core.fuel.toNat)
      (fun sL mL =>
        FullSparseInv c F0 sL ∧ sL.core.cur_vars = s.core.cur_vars ∧
        sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ sL.core.cur_level = 0 ∧
        sL.core.propagated = sL.core.trail_end ∧ sL.core.oom = 0#64 ∧
        sL.core.inconsistent = 0#64 ∧ (FullMem c sL ⋆ R) mL)
      (fun _ hL => by
        c0_hsteps
        exact hL s1 m1 ⟨hsp1, hcv1, hfu1, hcl1, hpt1, hoom1, hinc1, hm1⟩)
      (fun _ sL mL ⟨hspL, hcvL, hfuL, hclL, hptL, hoomL, hincL, hmL⟩ hLoop => ?_)
    obtain ⟨F_curL, hspwL⟩ := hspL.exists_witness
    c0_hsplit
    · -- `while (true)` true branch
      c0_hsplit
      · -- `oom != 0`: return 0
        c0_hsteps
        exact hQ 0#64 sL mL hspL (Or.inl rfl) hcvL hfuL
          (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide)) hmL
      · c0_hsplit
        · -- `fuel == 0`: return 0
          c0_hsteps
          exact hQ 0#64 sL mL hspL (Or.inl rfl) hcvL hfuL
            (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide)) hmL
        · c0_hsteps; c0_call hSweep
          refine ⟨c, F0, F_curL, sL, R, rfl, hspwL.1, hspwL.2.1, hspwL.2.2.2.1, hspwL.2.2.2.2.2,
            fun hpos => absurd hclL (by omega), hmL, ?_⟩
          intro sr _ _ _ _ _ _ te2 _ _ _ _ _ _ _ _ _ _ _ _ oom2 sc2 m2 s2
            hlen2 hsr hext2 _ hll2 hw2 hnd2 hoom01 _ hsr1 hsr2 _ hm2
          have hspw2 : FullSparseInvW c F0 F_curL s2 :=
            m6cf_fullSparseInvW_after_sweep hspwL hlen2 hw2 hnd2 hll2 hext2 rfl rfl rfl
          have hcl2 : s2.core.cur_level = 0 := hclL
          have hcv2 : s2.core.cur_vars = s.core.cur_vars := hcvL
          have hfu2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfuL
          c0_hsplit
          · -- `sr == 2`: UNSAT
            have hsr2_eq : sr = 2#64 := by c0_bound
            c0_hsteps
            exact hQ 20#64 s2 m2 hspw2.toSparse (Or.inr (Or.inr rfl)) hcv2 hfu2
              (fun _ => (hsr2 hsr2_eq).2) (fun h1 => absurd h1 (by decide)) hm2
          · c0_hsplit
            · -- `sr == 3`: OOM -> return 0
              c0_hsteps
              exact hQ 0#64 s2 m2 hspw2.toSparse (Or.inl rfl) hcv2 hfu2
                (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide)) hm2
            · c0_hsplit
              · -- `oom != 0`: return 0
                c0_hsteps
                exact hQ 0#64 s2 m2 hspw2.toSparse (Or.inl rfl) hcv2 hfu2
                  (fun h20 => absurd h20 (by decide)) (fun h1 => absurd h1 (by decide)) hm2
              · have hoom2 : s2.core.oom = 0#64 := by c0_bound
                have hsr_ne2 : sr ≠ 2#64 := by c0_bound
                have hsr_ne3 : sr ≠ 3#64 := by c0_bound
                have hsr01 : sr = 0#64 ∨ sr = 1#64 := by
                  rcases hsr with h | h | h | h
                  · exact Or.inl h
                  · exact Or.inr h
                  · exact absurd h hsr_ne2
                  · exact absurd h hsr_ne3
                have hprop_le2 := hlen2.core_ok.propagated_le
                have hte_le2 := hlen2.core_ok.trail_end_le
                have hcv_le2 := hlen2.core_ok.cur_vars_le
                have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
                c0_hsteps_nogrp
                refine wp_join_state0 (α := FullState)
                  (fun sC mC =>
                    sC.core.propagated < sC.core.trail_end ∧ sC.core.cur_level = 0 ∧
                    sC.core.cur_vars = s.core.cur_vars ∧
                    sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    sC.core.fuel.toNat = sL.core.fuel.toNat ∧
                    FullSparseInv c F0 sC ∧ (FullMem c sC ⋆ R) mC)
                  (fun _ sC mC ⟨hlt_pt, hclC, hcvC, hfuC, hfuEq, hspC, hmC⟩ => by
                    c0_hsteps; c0_call hFlush
                    refine ⟨c, F0, sC, R, rfl, hspC, hmC, ?_⟩
                    intro pr s3 m3 hsp3 hpr hcv3 hfu3 _ h20_3 h1_3 _ hm3
                    have hcv3' : s3.core.cur_vars = s.core.cur_vars := hcv3.trans hcvC
                    have hfu3' : s3.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu3 hfuC
                    c0_hsplit
                    · have hne1 : pr ≠ 1#64 := by c0_bound
                      c0_hsteps
                      exact hQ pr s3 m3 hsp3 hpr hcv3' hfu3' h20_3
                        (fun h1 => absurd h1 hne1) hm3
                    · have hpr1 : pr = 1#64 := by c0_bound
                      obtain ⟨hcl3, hpt3, hoom3, _, hinc3, hstrict3⟩ := h1_3 hpr1
                      have hlt_fuel : s3.core.fuel.toNat < sL.core.fuel.toNat := by
                        rw [← hfuEq]; exact hstrict3 hclC hlt_pt
                      c0_hsteps
                      exact hLoop s3 m3 hlt_fuel
                        ⟨hsp3, hcv3', hfu3', hcl3, hpt3, hoom3, hinc3, hm3⟩)
                  (fun Jcont hJcont => ?_)
                c0_hsplit
                · -- `sr == 0`
                  c0_hsplit
                  · -- `propagated >= trail_end`: break!
                    have hge_pt2 : s2.core.trail_end ≤ s2.core.propagated := by c0_bound
                    have heq_pt2 : s2.core.propagated = s2.core.trail_end := by omega
                    c0_hsteps
                    exact hJbrk s2 m2
                      ⟨hspw2.toSparse, hcv2, hfu2, hcl2, heq_pt2, hoom2, hincL, hm2⟩
                  · -- `propagated < trail_end`: flush and continue loop
                    have hlt_pt2 : s2.core.propagated < s2.core.trail_end := by c0_bound
                    c0_hsteps
                    exact hJcont s2 m2 ⟨hlt_pt2, hcl2, hcv2, hfu2, rfl, hspw2.toSparse, hm2⟩
                · -- `sr != 0` (`sr == 1`), so `sL.core.trail_end < te2`
                  have hsr1_eq : sr = 1#64 := hsr01.resolve_left (by c0_bound)
                  have hlt_pt2 : s2.core.propagated < s2.core.trail_end := by
                    have hte_inc := (hsr1 hsr1_eq).2
                    change sL.core.propagated < te2
                    rw [hptL]; exact hte_inc
                  c0_hsteps
                  exact hJcont s2 m2 ⟨hlt_pt2, hcl2, hcv2, hfu2, rfl, hspw2.toSparse, hm2⟩
    · exfalso; exact Bool.noConfusion hc

end CompactFlushProof

/-! ## 6. `full_extend_push2_m6cf` (`TmkZero`-Preserving + Canonical) -/

section ExtendPush2Proof

public theorem full_extend_push2_m6cf_tmk_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPush2TmkSpec a m Q X →
      Func.wp Γ full_extend_push2_m6cf_body a m Q X := by
  rintro ⟨h, blk_lit, other, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  have hcap : c.extend_cap < dimacsBound := c.hext
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hcap hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  have hesl := hlen.scratch_ok.extend_stk_len
  have hnlits : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_shl1_toNat (by omega), h1]
  unfold Func.wp full_extend_push2_m6cf_body
  c0_hsteps_nogrp
  -- Join after `bool skip_ot = ...`
  refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True) ?_ ?_
  · intro _ skip_ot _
    c0_hsteps_nogrp
    -- Join after `u64 need = skip_ot ? 1ULL : 2ULL;`
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
      (fun need => need = (if skip_ot then 1#64 else 2#64)) ?_ ?_
    · intro _ need hneed
      have hneed_nat : need.toNat = if skip_ot then 1 else 2 := by
        rw [hneed]; cases skip_ot <;> rfl
      have hneed_pos : 1 ≤ need.toNat := by rw [hneed_nat]; cases skip_ot <;> decide
      c0_hsplit
      · -- `extend_len > extend_cap` (impossible under `hel`, returns false)
        c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
      · c0_hsplit
        · -- `need > extend_cap - extend_len`: returns false
          c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
        · have hsub_eq : (BitVec.ofNat 64 c.extend_cap -
              BitVec.ofNat 64 s.scratch.extend_len).toNat =
              c.extend_cap - s.scratch.extend_len := by bv_omega
          have hfit : s.scratch.extend_len + need.toNat ≤ c.extend_cap := by
            have hle : need.toNat ≤ (BitVec.ofNat 64 c.extend_cap -
                BitVec.ofNat 64 s.scratch.extend_len).toNat := by c0_bound
            rw [hsub_eq] at hle; omega
          have hi0 : (BitVec.ofNat 64 s.scratch.extend_len).toNat <
              s.scratch.extend_stk.length := by
            rw [hesl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := List (BitVec 32))
            (fun ext1 m1 => ext1.length = c.extend_cap ∧
              (FullMem c { s with scratch := { s.scratch with extend_stk := ext1 } } ⋆ R) m1)
            ?_ ?_
          · rintro _ ext1 m1 ⟨hext1, hm1⟩
            have hadd_eq : (BitVec.ofNat 64 s.scratch.extend_len + need).toNat =
                s.scratch.extend_len + need.toNat := by
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)]
            c0_hsteps
            let s' : FullState :=
              { s with scratch := { s.scratch with
                extend_stk := ext1,
                extend_len := (BitVec.ofNat 64 s.scratch.extend_len + need).toNat } }
            exact hQ (true, ()) s' _ rfl
              (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := hext1 })
              ⟨rfl, by dsimp only [s']; rw [hadd_eq]; exact hfit, rfl, rfl⟩
              (m6cf_fullMem_cast hm rfl)
          · intro Jw hJw
            c0_hsplit
            · -- `skip_ot = true`: skip `other`
              c0_hsteps
              exact hJw _ _ ⟨by simp [hesl], hm⟩
            · -- `skip_ot = false`: `need = 2`, write `other` at `p + 1`
              have hsf : skip_ot = false := by cases skip_ot <;> simp_all
              have hneed2 : need.toNat = 2 := by rw [hneed_nat, hsf]; rfl
              have h0_el : (BitVec.ofNat 64 s.scratch.extend_len).toNat =
                  s.scratch.extend_len := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have hi1 : (BitVec.ofNat 64 s.scratch.extend_len + 1#64).toNat <
                  (s.scratch.extend_stk.set (BitVec.ofNat 64 s.scratch.extend_len).toNat
                    ((blk_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32)).length := by
                rw [List.length_set, hesl, BitVec.toNat_add, h0_el,
                  show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                omega
              c0_hsteps
              exact hJw _ _ ⟨by simp [hesl], hm⟩
    · intro Jn hJn
      c0_hsplit <;> (c0_hsteps; exact hJn _ (by simp_all))
  · intro Js hJs
    c0_hsplit
    · have hot_lt : (other &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
        have h1 : ((other &&& 0x7FFFFFFF#32).setWidth 64).toNat <
            ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        rw [zext_toNat _ (by decide), hnlits] at h1; exact h1
      have hot_v : ((other &&& 0x7FFFFFFF#32).setWidth 64).toNat < s.core.vals.length := by
        rw [zext_toNat _ (by decide), hv_len]; omega
      have hot_l : (((other &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat <
          s.core.lvl.length := by
        rw [zext_toNat _ (by decide), bv32_shr1_toNat, hl_len]; omega
      c0_hsteps <;> exact hJs _ trivial
    · c0_hsteps; exact hJs false trivial

public theorem full_extend_push2_m6cf_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPush2Spec a m Q X →
      Func.wp Γ full_extend_push2_m6cf_body a m Q X := by
  rintro ⟨h_ptr, blk, ot, ⟨⟩⟩ m Q X ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact full_extend_push2_m6cf_tmk_wp Γ _ m Q X
    ⟨c, s, R, hpre, hlen, hm,
      fun r s' m' hcore hlen' ⟨h1, h2, h3, _⟩ hm' => hQ r s' m' hcore hlen' ⟨h1, h2, h3⟩ hm'⟩

end ExtendPush2Proof

/-! ## 7. `full_extend_push_cl_m6cf` (`TmkZero`-Preserving + Canonical) -/

section ExtendPushClProof

private def extLitSkip (vals : List (BitVec 8)) (lvl : List (BitVec 32))
    (nlits : Nat) (lit : BitVec 32) : Bool :=
  decide (lit.toNat < nlits ∧
    lvl[lit.toNat / 2]?.getD 0#32 = 0#32 ∧
    ((vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 = true)

private def extLitKeep (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) (j : Nat) : Bool :=
  let lit := (ar[cref + 3 + j]?.getD 0#32) &&& 0x7FFFFFFF#32
  decide (lit ≠ bl) && !(extLitSkip vals lvl nlits lit)

private def extKeepCount (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    extKeepCount ar vals lvl cref nlits bl n +
      if extLitKeep ar vals lvl cref nlits bl n then 1 else 0

private theorem extKeepCount_zero (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) :
    extKeepCount ar vals lvl cref nlits bl 0 = 0 := rfl

private theorem extKeepCount_succ (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) (n : Nat) :
    extKeepCount ar vals lvl cref nlits bl (n + 1) =
      extKeepCount ar vals lvl cref nlits bl n +
        if extLitKeep ar vals lvl cref nlits bl n then 1 else 0 := rfl

private theorem extKeepCount_le (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) :
    ∀ n, extKeepCount ar vals lvl cref nlits bl n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    rw [extKeepCount_succ]
    have ih := extKeepCount_le ar vals lvl cref nlits bl n
    split <;> omega

private theorem extKeepCount_mono (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) :
    ∀ {a b}, a ≤ b →
      extKeepCount ar vals lvl cref nlits bl a ≤ extKeepCount ar vals lvl cref nlits bl b
  | a, b, hab => by
    induction hab with
    | refl => exact Nat.le_refl _
    | step _ ih =>
      rw [extKeepCount_succ]
      split <;> omega

private theorem extLitKeep_eq_true {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {lvl : List (BitVec 32)} {cref nlits j : Nat} {bl lit : BitVec 32}
    (hlit : (ar[cref + 3 + j]?.getD 0#32) &&& 0x7FFFFFFF#32 = lit)
    (hne : lit ≠ bl)
    (hnskip : ¬ (lit.toNat < nlits ∧ lvl[lit.toNat / 2]?.getD 0#32 = 0#32 ∧
      ((vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 = true)) :
    extLitKeep ar vals lvl cref nlits bl j = true := by
  unfold extLitKeep extLitSkip; rw [hlit]; simp [hne, hnskip]

private theorem extLitKeep_eq_false_skip {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {lvl : List (BitVec 32)} {cref nlits j : Nat} {bl lit : BitVec 32}
    (hlit : (ar[cref + 3 + j]?.getD 0#32) &&& 0x7FFFFFFF#32 = lit)
    (hlt : lit.toNat < nlits) (hlvl : lvl[lit.toNat / 2]?.getD 0#32 = 0#32)
    (hval : ((vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 = true) :
    extLitKeep ar vals lvl cref nlits bl j = false := by
  unfold extLitKeep extLitSkip; rw [hlit]; simp [hlt, hlvl, hval]

private theorem extLitKeep_eq_false_bl {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {lvl : List (BitVec 32)} {cref nlits j : Nat} {bl : BitVec 32}
    (heq : (ar[cref + 3 + j]?.getD 0#32) &&& 0x7FFFFFFF#32 = bl) :
    extLitKeep ar vals lvl cref nlits bl j = false := by
  unfold extLitKeep; rw [heq]; simp

public theorem full_extend_push_cl_m6cf_tmk_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPushClTmkSpec a m Q X →
      Func.wp Γ full_extend_push_cl_m6cf_body a m Q X := by
  rintro ⟨h, blk_lit, cref, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  have haca : c.arena_cap < 2 * dimacsBound := c.harena
  have heca : c.extend_cap < dimacsBound := c.hext
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at haca heca hmx
  have harl := hlen.core_ok.arena_len_arr
  have hale := hlen.core_ok.arena_len_le
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  have hesl := hlen.scratch_ok.extend_stk_len
  have h2bv : (2 : BitVec 64).toNat = 2 := rfl
  have h3bv : (3 : BitVec 64).toNat = 3 := rfl
  have h2cv : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 = 2 * s.core.cur_vars := by omega
  have hnlits : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_shl1_toNat (by omega), h1]
  unfold Func.wp full_extend_push_cl_m6cf_body
  c0_hsplit
  · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
  · have hcr3 : cref.toNat + 3 ≤ s.core.arena_len := by bv_omega
    have hcr2_eq : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
    have hcr2_mod : (cref.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cref.toNat + 2 := by
      rw [h2bv, Nat.mod_eq_of_lt (by omega)]
    have hcr2_lt : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by
      rw [hcr2_eq, harl]; omega
    let szBv : BitVec 32 := s.core.arena[cref.toNat + 2]'(by omega)
    let sz : Nat := szBv.toNat
    c0_hsplit
    · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
    · have hc3sz : cref.toNat + 3 + sz ≤ s.core.arena_len := by
        have h1 := hc
        simp only [hcr2_mod, h3bv] at h1
        have hsz32 := szBv.isLt
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
        change ¬ s.core.arena_len < cref.toNat + 3 + sz at h1
        omega
      let bl : BitVec 32 := blk_lit &&& 0x7FFFFFFF#32
      let cnt :=
        extKeepCount s.core.arena s.core.vals s.core.lvl cref.toNat (2 * s.core.cur_vars) bl
      c0_hsteps_nogrp
      -- Pass 1: count kept literals (`keep = cnt sz`)
      refine wp_loop_inv
        (fun (keep, i, ()) m1 =>
          i.toNat ≤ sz ∧ keep.toNat = cnt i.toNat ∧ m1 = m)
        (fun (_, i, ()) _ => sz - i.toNat)
        (fun J1 hLoop1 => by
          c0_hsteps; exact hLoop1 (0#64, 0#32, ()) m ⟨Nat.zero_le _, rfl, rfl⟩)
        (fun J1 ⟨keep, i, ⟨⟩⟩ m1 ⟨hi_le, hkeep_eq, hm1⟩ hLoop1 => ?_)
      rcases hm1.symm with rfl
      c0_hsplit
      · -- `i < sz`
        have hi_lt : i.toNat < sz := by
          have h1 := hc; simp only [hcr2_mod] at h1; exact h1
        have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := bv32_add1 (by omega)
        have hli_eq : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
            cref.toNat + 3 + i.toNat := by bv_omega
        have hli_mod : (cref.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
            cref.toNat + 3 + i.toNat := by rw [h3bv, Nat.mod_eq_of_lt (by omega)]
        have hli_lt : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < s.core.arena.length := by
          rw [hli_eq, harl]; omega
        let lit : BitVec 32 :=
          (s.core.arena[cref.toNat + 3 + i.toNat]'(by omega)) &&& 0x7FFFFFFF#32
        have hlit_ar :
            (s.core.arena[cref.toNat + 3 + i.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32 = lit := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hkeep_ub : keep.toNat ≤ i.toNat := hkeep_eq ▸ extKeepCount_le ..
        have hkp1_eq : (keep + 1#64).toNat = keep.toNat + 1 := bv64_add1 (by omega)
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun k => (k, ()))
          (fun k => k.toNat = cnt (i.toNat + 1)) ?_ ?_
        · intro _ k hk
          c0_hsteps
          exact hLoop1 (k, i + 1#32, ()) m (by dsimp only; rw [hi1_eq]; omega)
            ⟨by rw [hi1_eq]; omega, by rw [hi1_eq]; exact hk, rfl⟩
        · intro Jk hJk
          c0_hsplit
          · -- `lit != bl`
            have hne_bl : lit ≠ bl := by
              have h1 := hc; simp only [hli_mod] at h1; exact h1
            c0_hsteps_nogrp
            -- Join block `Js : Cont []` for `keep = keep + 1ULL; jump Jk`
            refine wp_join_state0 (α := Unit)
              (fun _ m' => m' = m ∧
                extLitKeep s.core.arena s.core.vals s.core.lvl cref.toNat
                  (2 * s.core.cur_vars) bl i.toNat = true) ?_ ?_
            · rintro _ ⟨⟩ m' ⟨rfl, htk⟩
              c0_hsteps
              exact hJk (keep + 1#64) (by
                dsimp only [cnt]; rw [extKeepCount_succ, htk, hkp1_eq, hkeep_eq]; rfl)
            · intro Js hJs
              c0_hsplit
              · -- `lit < nlits`
                have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
                  have h1 := hc; simp only [hli_mod, h2cv] at h1; exact h1
                have hlit_lvl_bd : lit.toNat / 2 < s.core.lvl.length := by rw [hl_len]; omega
                have hlit_val_bd : lit.toNat < s.core.vals.length := by rw [hv_len]; omega
                have hlit_val_load :
                    (BitVec.setWidth 64
                      (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hli_lt &&&
                        0x7FFFFFFF#32)).toNat < s.core.vals.length := by
                  rw [zext_toNat _ (by decide)]; simp only [hli_eq]; exact hlit_val_bd
                c0_hsplit
                · -- `lvl == 0`
                  have hlvl0 : s.core.lvl[lit.toNat / 2]?.getD 0#32 = 0#32 := by
                    have h1 := hc; simp only [hli_mod] at h1
                    rw [List.getElem?_eq_getElem hlit_lvl_bd, Option.getD_some]; exact h1
                  c0_hsplit
                  · -- `vals < 0`: root-false -> SKIP!
                    have hvf : ((s.core.vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 =
                        true := by
                      have h1 := hc; simp only [hli_mod] at h1
                      rw [List.getElem?_eq_getElem hlit_val_bd, Option.getD_some]; exact h1
                    have hfk := extLitKeep_eq_false_skip (bl := bl) hlit_ar hlit_lt hlvl0 hvf
                    c0_hsteps
                    exact hJk keep (by
                      dsimp only [cnt]; rw [extKeepCount_succ, hfk]; simpa using hkeep_eq)
                  · -- `vals >= 0`: KEEP!
                    have hvnf : ((s.core.vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 ≠
                        true := by
                      have h1 := hc; simp only [hli_mod] at h1
                      rw [List.getElem?_eq_getElem hlit_val_bd, Option.getD_some]
                      intro ht; exact Bool.noConfusion (h1.symm.trans ht)
                    c0_hsteps
                    exact hJs () m
                      ⟨rfl, extLitKeep_eq_true hlit_ar hne_bl (fun ⟨_, _, hv⟩ => hvnf hv)⟩
                · -- `lvl != 0`: KEEP!
                  have hlvlne : s.core.lvl[lit.toNat / 2]?.getD 0#32 ≠ 0#32 := by
                    have h1 := hc; simp only [hli_mod] at h1
                    rw [List.getElem?_eq_getElem hlit_lvl_bd, Option.getD_some]; exact h1
                  c0_hsteps
                  exact hJs () m
                    ⟨rfl, extLitKeep_eq_true hlit_ar hne_bl (fun ⟨_, h0, _⟩ => hlvlne h0)⟩
              · -- `lit >= nlits`: KEEP!
                have hlit_ge : ¬ lit.toNat < 2 * s.core.cur_vars := by
                  have h1 := hc; simp only [hli_mod, h2cv] at h1; exact h1
                c0_hsteps
                exact hJs () m
                  ⟨rfl, extLitKeep_eq_true hlit_ar hne_bl (fun ⟨hlt, _, _⟩ => hlit_ge hlt)⟩
          · -- `lit == bl`: SKIP!
            have heq_bl :
                (s.core.arena[cref.toNat + 3 + i.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32 = bl := by
              rw [hlit_ar]; have h1 := hc; simp only [hli_mod] at h1; exact h1
            have hfk := extLitKeep_eq_false_bl (vals := s.core.vals) (lvl := s.core.lvl)
              (nlits := 2 * s.core.cur_vars) heq_bl
            c0_hsteps
            exact hJk keep (by
              dsimp only [cnt]; rw [extKeepCount_succ, hfk]; simpa using hkeep_eq)
      · -- Exit Pass 1 (`i = sz`, `keep = cnt sz`)
        have hi_eq : i.toNat = sz := by
          have h1 := hc; simp only [hcr2_mod] at h1; dsimp only [sz, szBv] at hi_le ⊢; omega
        rw [hi_eq] at hkeep_eq
        have hkeep_ub : keep.toNat ≤ sz := hkeep_eq ▸ extKeepCount_le ..
        have hneed_eq : (1#64 + keep).toNat = 1 + keep.toNat := by bv_omega
        clear hLoop1 J1
        c0_hsplit
        · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
        · c0_hsplit
          · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
          · have hsub_eq : (BitVec.ofNat 64 c.extend_cap -
                BitVec.ofNat 64 s.scratch.extend_len).toNat =
                c.extend_cap - s.scratch.extend_len := by bv_omega
            have hfit : s.scratch.extend_len + 1 + keep.toNat ≤ c.extend_cap := by
              have hle : (1#64 + keep).toNat ≤ (BitVec.ofNat 64 c.extend_cap -
                  BitVec.ofNat 64 s.scratch.extend_len).toNat := by c0_bound
              rw [hneed_eq, hsub_eq] at hle; omega
            have h0_el : (BitVec.ofNat 64 s.scratch.extend_len).toNat = s.scratch.extend_len := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have hp0_lt : (BitVec.ofNat 64 s.scratch.extend_len).toNat <
                s.scratch.extend_stk.length := by rw [hesl, h0_el]; omega
            c0_hsteps_nogrp
            -- Pass 2: write kept literals (`J2 : Cont [i32, i64]`, `(i2, p, ())`)
            refine wp_loop_inv
              (fun (i2, p, ()) m2 =>
                i2.toNat ≤ sz ∧ p.toNat = s.scratch.extend_len + 1 + cnt i2.toNat ∧
                ∃ ext2 : List (BitVec 32), ext2.length = c.extend_cap ∧
                  (FullMem c { s with scratch := { s.scratch with extend_stk := ext2 } } ⋆ R) m2)
              (fun (i2, _, ()) _ => sz - i2.toNat)
              (fun J2 hLoop2 => by
                c0_hsteps
                refine hLoop2 (0#32, BitVec.ofNat 64 s.scratch.extend_len + 1#64, ()) _
                  ⟨Nat.zero_le _, ?_, _, by simp [hesl], hm⟩
                have h032 : (0#32 : BitVec 32).toNat = 0 := rfl
                rw [h032]; dsimp only [cnt]; rw [extKeepCount_zero]
                rw [BitVec.toNat_add, h0_el, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)])
              (fun J2 ⟨i2, p, ⟨⟩⟩ m2 ⟨hi2_le, hp_eq, ext2, hext2, hm2⟩ hLoop2 => ?_)
            c0_hsplit
            · -- `i2 < sz`
              have hi2_lt : i2.toNat < sz := by
                have h1 := hc; simp only [hcr2_mod] at h1; exact h1
              have hi2_1 : (i2 + 1#32).toNat = i2.toNat + 1 := bv32_add1 (by omega)
              have hli2_eq : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat =
                  cref.toNat + 3 + i2.toNat := by bv_omega
              have hli2_mod : (cref.toNat + (3 : BitVec 64).toNat + i2.toNat) % 2 ^ 64 =
                  cref.toNat + 3 + i2.toNat := by rw [h3bv, Nat.mod_eq_of_lt (by omega)]
              have hli2_lt : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat <
                  s.core.arena.length := by rw [hli2_eq, harl]; omega
              let lit2 : BitVec 32 :=
                (s.core.arena[cref.toNat + 3 + i2.toNat]'(by omega)) &&& 0x7FFFFFFF#32
              have hlit2_ar :
                  (s.core.arena[cref.toNat + 3 + i2.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32 =
                  lit2 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcnt_le_keep : cnt (i2.toNat + 1) ≤ keep.toNat :=
                hkeep_eq ▸ extKeepCount_mono _ _ _ _ _ _ (by omega)
              c0_hsteps_nogrp
              refine wp_join_state1 (t := i64) (α := BitVec 64 × List (BitVec 32)) Prod.fst
                (fun ⟨p', ext'⟩ m' =>
                  p'.toNat = s.scratch.extend_len + 1 + cnt (i2.toNat + 1) ∧
                  ext'.length = c.extend_cap ∧
                  (FullMem c { s with scratch := { s.scratch with extend_stk := ext' } } ⋆ R) m')
                ?_ ?_
              · rintro _ ⟨p', ext'⟩ m' ⟨hp'eq, hext', hm'⟩
                c0_hsteps
                exact hLoop2 (i2 + 1#32, p', ()) m' (by dsimp only; rw [hi2_1]; omega)
                  ⟨by rw [hi2_1]; omega, by rw [hi2_1]; exact hp'eq, ext', hext', hm'⟩
              · intro Jw hJw
                c0_hsplit
                · -- `lit2 != bl`
                  have hne_bl : lit2 ≠ bl := by
                    have h1 := hc; simp only [hli2_mod] at h1; exact h1
                  c0_hsteps_nogrp
                  -- Join block `Js : Cont []` for `ext[p] = lit2; p = p + 1ULL; jump Jw`
                  refine wp_join_state0 (α := Unit)
                    (fun _ m' => m' = m2 ∧
                      extLitKeep s.core.arena s.core.vals s.core.lvl cref.toNat
                        (2 * s.core.cur_vars) bl i2.toNat = true) ?_ ?_
                  · rintro _ ⟨⟩ m' ⟨rfl, htk⟩
                    have hstep : cnt (i2.toNat + 1) = cnt i2.toNat + 1 := by
                      dsimp only [cnt]; rw [extKeepCount_succ, htk]; rfl
                    have hp_lt : p.toNat < ext2.length := by rw [hext2]; omega
                    have hp1 : (p + 1#64).toNat =
                        s.scratch.extend_len + 1 + cnt (i2.toNat + 1) := by
                      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega), hp_eq, hstep]; omega
                    c0_hsteps
                    exact hJw (p + 1#64, _) _ ⟨hp1, by simp [hext2], hm⟩
                  · intro Js hJs
                    c0_hsplit
                    · -- `lit2 < nlits`
                      have hlit_lt : lit2.toNat < 2 * s.core.cur_vars := by
                        have h1 := hc; simp only [hli2_mod, h2cv] at h1; exact h1
                      have hlit_lvl_bd : lit2.toNat / 2 < s.core.lvl.length := by
                        rw [hl_len]; omega
                      have hlit_val_bd : lit2.toNat < s.core.vals.length := by
                        rw [hv_len]; omega
                      have hlit_val_load :
                          (BitVec.setWidth 64
                            (s.core.arena[(cref.setWidth 64 + 3#64 +
                              i2.setWidth 64).toNat]'hli2_lt &&&
                              0x7FFFFFFF#32)).toNat < s.core.vals.length := by
                        rw [zext_toNat _ (by decide)]; simp only [hli2_eq]; exact hlit_val_bd
                      c0_hsplit
                      · -- `lvl == 0`
                        have hlvl0 : s.core.lvl[lit2.toNat / 2]?.getD 0#32 = 0#32 := by
                          have h1 := hc; simp only [hli2_mod] at h1
                          rw [List.getElem?_eq_getElem hlit_lvl_bd, Option.getD_some]; exact h1
                        c0_hsplit
                        · -- `vals < 0`: root-false -> SKIP!
                          have hvf : ((s.core.vals[lit2.toNat]?.getD 0#8).signExtend 32).slt
                              0#32 = true := by
                            have h1 := hc; simp only [hli2_mod] at h1
                            rw [List.getElem?_eq_getElem hlit_val_bd, Option.getD_some]; exact h1
                          have hfk := extLitKeep_eq_false_skip (bl := bl) hlit2_ar hlit_lt hlvl0 hvf
                          c0_hsteps
                          exact hJw (p, ext2) m2
                            ⟨by dsimp only [cnt]; rw [extKeepCount_succ, hfk]; simpa using hp_eq,
                             hext2, hm2⟩
                        · -- `vals >= 0`: WRITE!
                          have hvnf : ((s.core.vals[lit2.toNat]?.getD 0#8).signExtend 32).slt
                              0#32 ≠ true := by
                            have h1 := hc; simp only [hli2_mod] at h1
                            rw [List.getElem?_eq_getElem hlit_val_bd, Option.getD_some]
                            intro ht; exact Bool.noConfusion (h1.symm.trans ht)
                          c0_hsteps
                          exact hJs () m2 ⟨rfl, extLitKeep_eq_true hlit2_ar hne_bl
                            (fun ⟨_, _, hv⟩ => hvnf hv)⟩
                      · -- `lvl != 0`: WRITE!
                        have hlvlne : s.core.lvl[lit2.toNat / 2]?.getD 0#32 ≠ 0#32 := by
                          have h1 := hc; simp only [hli2_mod] at h1
                          rw [List.getElem?_eq_getElem hlit_lvl_bd, Option.getD_some]; exact h1
                        c0_hsteps
                        exact hJs () m2 ⟨rfl, extLitKeep_eq_true hlit2_ar hne_bl
                          (fun ⟨_, h0, _⟩ => hlvlne h0)⟩
                    · -- `lit2 >= nlits`: WRITE!
                      have hlit_ge : ¬ lit2.toNat < 2 * s.core.cur_vars := by
                        have h1 := hc; simp only [hli2_mod, h2cv] at h1; exact h1
                      c0_hsteps
                      exact hJs () m2 ⟨rfl, extLitKeep_eq_true hlit2_ar hne_bl
                        (fun ⟨hlt, _, _⟩ => hlit_ge hlt)⟩
                · -- `lit2 == bl`: SKIP!
                  have heq_bl :
                      (s.core.arena[cref.toNat + 3 + i2.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32 =
                      bl := by
                    rw [hlit2_ar]; have h1 := hc; simp only [hli2_mod] at h1; exact h1
                  have hfk := extLitKeep_eq_false_bl (vals := s.core.vals) (lvl := s.core.lvl)
                    (nlits := 2 * s.core.cur_vars) heq_bl
                  c0_hsteps
                  exact hJw (p, ext2) m2
                    ⟨by dsimp only [cnt]; rw [extKeepCount_succ, hfk]; simpa using hp_eq,
                     hext2, hm2⟩
            · -- Exit Pass 2 (`i2 = sz`): `h->extend_len = p; return true`
              have hi2_eq : i2.toNat = sz := by
                have h1 := hc; simp only [hcr2_mod] at h1; dsimp only [sz, szBv] at hi2_le ⊢; omega
              rw [hi2_eq, ← hkeep_eq] at hp_eq
              c0_hsteps
              let s' : FullState :=
                { s with scratch := { s.scratch with extend_stk := ext2, extend_len := p.toNat } }
              exact hQ (true, ()) s' _ rfl
                (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := hext2 })
                ⟨rfl, by dsimp only [s']; omega, rfl, rfl⟩
                (m6cf_fullMem_cast hm rfl)

public theorem full_extend_push_cl_m6cf_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPushClSpec a m Q X →
      Func.wp Γ full_extend_push_cl_m6cf_body a m Q X := by
  rintro ⟨h_ptr, blk, cref, ⟨⟩⟩ m Q X ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact full_extend_push_cl_m6cf_tmk_wp Γ _ m Q X
    ⟨c, s, R, hpre, hlen, hm,
      fun r s' m' hcore hlen' ⟨h1, h2, h3, _⟩ hm' => hQ r s' m' hcore hlen' ⟨h1, h2, h3⟩ hm'⟩

end ExtendPushClProof

end LeanQbe.T.Examples.Kissat.FullM6CompactFlush
