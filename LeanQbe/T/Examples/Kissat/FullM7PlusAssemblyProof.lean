/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM7BvaGuFixProof
public import LeanQbe.T.Examples.Kissat.FullM7CompactFixProof
public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiersProof
public import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTieProof
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` `M7Plus` (`PLUS_T8_tie1_bb20`) Closed Assembly Proof (`FullM7PlusAssemblyProof`)

Complete closed `0`-hook UNSAT-only verification of `m7PlusModule` (`410` fns, `0` `@[expose]`,
`0` `sorry` / `axiom`, `0` SAT model finding proofs):
1. Local `FullM4Compact.fullCompactNeededSpec`-backed `full_preprocess_m6` and
   `full_simplify_m6` WP bridges matching `m7fix_1pct` (`FullM7CompactFix`).
2. `mpExtraRows` (`33` hot-BCP, vivification helper, and `full_compact_needed` rows) + closed
   `M7PlusEnv` / `m7PlusEnv` over `m7PlusBaseEnv`.
3. Closed `m7Plus_checkAcyclic`, `m7PlusEnv_noExit`, `m7Plus_moduleOk`, UNSAT-only source & host
   soundness (`m7Plus_solve_bytes_sound`, `m7Plus_solve_bytes_host_sound`), and concrete Tier-3b
   UNSAT non-vacuity (`m7Plus_unsat_nv`, `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Plus

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
open LeanQbe.T.Examples.Kissat.FullM7CompactFix
open LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
open LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
open LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. `FullM4Compact.fullCompactNeededSpec` Preprocess/Simplify Bridges -/

private theorem mp_fullInv_of_backtrack0 {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState}
    (hinv : FullM6HdrInv c F0 ext s) :
    s.core.cur_level < 2 ^ 64 ∧
    ((0#64 : BitVec 64).toNat < s.core.cur_level → (0#64 : BitVec 64).toNat < c.max_vars) ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) := by
  obtain ⟨_, hw⟩ := hinv.sparse.1.witness
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hte := hinv.sparse.lengths.core_ok.trail_end_le
  have hcv := hinv.sparse.lengths.core_ok.cur_vars_le
  have hcl := hw.cur_level_le
  exact ⟨by omega, fun _ => by omega, hw.trail_lits_lt⟩

private theorem mp_conflict_level0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private theorem mp_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', FullM6BcpS15.fullBcpS15Spec (c.hdr, ()) m Q' X' →
      Γ "full_propagate" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → s'.core.cur_level = s.core.cur_level →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom _ hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' rfl htr' hperm' hfu' hdom hr1
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem full_preprocess_m6_compact_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, Full.fullLuckySpec a m Q X →
      Γ "full_lucky" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, FullM6Orch.m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ full_preprocess_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6PreprocessSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_preprocess_m6_body
  obtain ⟨F_cur, hw0⟩ := hinv.sparse.1.witness
  have hinvW0 : FullM6HdrInvW c F0 F_cur ext s :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk ⟨hinv.sparse.lengths, hw0, hinv.sparse.2.1,
      hinv.sparse.2.2.1, hinv.sparse.2.2.2.1, hinv.sparse.2.2.2.2⟩
  c0_hsteps_nogrp
  refine mp_call_bcp rfl (fun _ _ h => hProp _ _ _ _ h) hinvW0 hm
    fun r1 s1 m1 hinvW1 hcl1 _ _ hfu1 _ hr1_1 hm1 => ?_
  have hinv1 := hinvW1.toInv
  have hcl1' : s1.core.cur_level = 0 := by rw [hcl1]; exact hcl0
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · exact hQ 20#64 c ext s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths hinv1.cfgOk
      hinv1.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu1
      (fun _ => mp_conflict_level0_unsat hinvW1.sparseW.2.1 hcl1' (hr1_1 ‹_›).2.2)
      (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm1f)
  · exact hQ 0#64 c ext s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths hinv1.cfgOk
      hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm1f)
  · exact hQ 0#64 c ext s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths hinv1.cfgOk
      hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm1f)
  · refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
      refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
      c0_hsteps_nogrp
      · exact hQ 10#64 c ext s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.sparse.lengths
          hinv2.cfgOk hinv2.extOk (Or.inr (Or.inr (Or.inl rfl))) hfu2
          (fun h => by cases h) (fun h => by cases h)
          (fun _ => hinv2.sparse.2.2.2.1.2) (fullM6HdrMem_unfocus hm2f)
      · c0_call hLucky
        refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hcl2, hm2f,
          fun lk s3 m3 hlen3 hlk hfu3 _ hu3 hsp3 h10_3 hm3 => ?_⟩
        have hm3' := fullM6HdrMem_unfocus hm3
        have hfu3' := Nat.le_trans hfu3 hfu2
        let mkInv3 : lk ≠ 20#64 → lk ≠ 10#64 →
            FullM6HdrInv c F0 ext s3 ∧ s3.core.cur_level = 0 := fun h20 h10 =>
          let h02 : lk = 0#64 ∨ lk = 2#64 := by
            rcases hlk with rfl | rfl | rfl | rfl <;>
              (first | exact Or.inl rfl | exact Or.inr rfl | contradiction)
          let ⟨hs3, hc3⟩ := hsp3 h02
          ⟨FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hs3, hc3⟩
        c0_hsteps_nogrp
        · rw [‹lk = 20#64›]
          exact hQ 20#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv2.cfgOk
            hinv2.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu3' (fun _ => hu3 ‹_›)
            (fun h => by cases h) (fun h => by cases h) hm3'
        · rw [‹lk = 10#64›]
          exact hQ 10#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv2.cfgOk
            hinv2.extOk (Or.inr (Or.inr (Or.inl rfl))) hfu3' (fun _ => by cases ‹_›)
            (fun h => by cases h) (fun _ => h10_3 ‹_›) hm3'
        · obtain ⟨hinv3, _⟩ := mkInv3 ‹_› ‹_›
          exact hQ 20#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv3.cfgOk
            hinv3.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu3'
            (fun _ => fullM6HdrInv_inconsistent_unsat hinv3 ‹_›)
            (fun h => by cases h) (fun h => by cases h) hm3'
        · obtain ⟨hinv3, _⟩ := mkInv3 ‹_› ‹_›
          exact hQ 0#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv3.cfgOk
            hinv3.extOk (Or.inl rfl) hfu3' (fun h => by cases h)
            (fun h => by cases h) (fun h => by cases h) hm3'
        · obtain ⟨hinv3, _⟩ := mkInv3 ‹_› ‹_›
          exact hQ 0#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv3.cfgOk
            hinv3.extOk (Or.inl rfl) hfu3' (fun h => by cases h)
            (fun h => by cases h) (fun h => by cases h) hm3'
        · obtain ⟨hinv3, hcl3⟩ := mkInv3 ‹_› ‹_›
          let hm3f := hm3
          -- First optional `compact_needed` -> `full_compact`.
          refine wp_join_group (fun (_ : Tup Val []) m4 => ∃ c4 s4,
              FullM4Compact.FullCfgCompat c c4 ∧ FullM6HdrInv c4 F0 ext s4 ∧
              s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c4 ext s4 ⋆ R) m4) ?_ ?_
          · rintro _ _ m4 ⟨c4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩
            rw [← hcmp4.hdr]
            refine wp_m6Hdr_focus_frame hm4 fun hm4f => ?_
            c0_hsteps_nogrp
            · exact hQ 20#64 c4 ext s4 m4 hcmp4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (Or.inr (Or.inr (Or.inr rfl))) hfu4
                (fun _ => fullM6HdrInv_inconsistent_unsat hinv4 ‹_›)
                (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm4f)
            · exact hQ 0#64 c4 ext s4 m4 hcmp4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (Or.inl rfl) hfu4 (fun h => by cases h)
                (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm4f)
            · exact hQ 10#64 c4 ext s4 m4 hcmp4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (Or.inr (Or.inr (Or.inl rfl))) hfu4 (fun h => by cases h)
                (fun h => by cases h) (fun _ => hinv4.sparse.2.2.2.1.2)
                (fullM6HdrMem_unfocus hm4f)
            · c0_call hScale
              refine ⟨c4, s4, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl, hinv4.sparse.lengths,
                hm4f, fun sd1 => ?_⟩
              c0_hsteps_nogrp; c0_call hScale
              refine ⟨c4, _, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl,
                (fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings).1,
                by assumption, fun sd2 => ?_⟩
              c0_hsteps_nogrp
              have hst4 := fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings
              have hst4' := fullState_upd_elim_step hst4.1 sd2 s4.scratch.eliminations
                s4.scratch.elim_bound
              have hinv4' := fullM6HdrInv_of_probeStep hinv4 (probeStep_trans hst4 hst4')
              have hm4' := fullM6HdrMem_unfocus (by assumption)
              c0_call hProbe
              refine FullM6Orch.m6ProbeSpec_of hinv4' (by rw [hst4'.2.1, hst4.2.1]; exact hcl4) hm4'
                fun r5 ext5 s5 m5 hlen5 hext5 hfu5 hr5 hu5 h15 hm5 => ?_
              have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hst4'.2.1, hst4.2.1] at hfu5; exact Nat.le_trans hfu5 hfu4
              c0_hsteps_nogrp
              · exact hQ 20#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv4'.cfgOk hext5
                  (Or.inr (Or.inr (Or.inr rfl))) hfu5' (fun _ => hu5 ‹_›)
                  (fun h => by cases h) (fun h => by cases h) hm5
              · obtain ⟨hinv5, hcl5⟩ := h15 (hr5.resolve_right ‹_›)
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
                c0_hsteps_nogrp
                · exact hQ 20#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv5.cfgOk hext5
                    (Or.inr (Or.inr (Or.inr rfl))) hfu5'
                    (fun _ => fullM6HdrInv_inconsistent_unsat hinv5 ‹_›)
                    (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm5f)
                · exact hQ 0#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv5.cfgOk hext5
                    (Or.inl rfl) hfu5' (fun h => by cases h)
                    (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm5f)
                · exact hQ 0#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv5.cfgOk hext5
                    (Or.inl rfl) hfu5' (fun h => by cases h)
                    (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm5f)
                · -- Second optional `compact_needed` -> `full_compact`.
                  refine wp_join_group (fun (_ : Tup Val []) m6 => ∃ c6 s6,
                      FullM4Compact.FullCfgCompat c c6 ∧ FullM6HdrInv c6 F0 ext5 s6 ∧
                      s6.core.cur_level = 0 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullM6HdrMem c6 ext5 s6 ⋆ R) m6) ?_ ?_
                  · rintro _ _ m6 ⟨c6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
                    rw [hcmp4.hdr, ← hcmp6.hdr]
                    refine wp_m6Hdr_focus_frame hm6 fun hm6f => ?_
                    c0_hsteps_nogrp
                    · exact hQ 20#64 c6 ext5 s6 m6 hcmp6 hinv6.sparse.lengths hinv6.cfgOk
                        hinv6.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu6
                        (fun _ => fullM6HdrInv_inconsistent_unsat hinv6 ‹_›)
                        (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm6f)
                    · exact hQ 0#64 c6 ext5 s6 m6 hcmp6 hinv6.sparse.lengths hinv6.cfgOk
                        hinv6.extOk (Or.inl rfl) hfu6 (fun h => by cases h)
                        (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm6f)
                    · exact hQ 10#64 c6 ext5 s6 m6 hcmp6 hinv6.sparse.lengths hinv6.cfgOk
                        hinv6.extOk (Or.inr (Or.inr (Or.inl rfl))) hfu6 (fun h => by cases h)
                        (fun h => by cases h) (fun _ => hinv6.sparse.2.2.2.1.2)
                        (fullM6HdrMem_unfocus hm6f)
                    · c0_call hScale
                      refine ⟨c6, s6, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                        hinv6.sparse.lengths, hm6f, fun sd3 => ?_⟩
                      c0_hsteps_nogrp; c0_call hScale
                      refine ⟨c6, _, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                        (fullState_upd_probe_step hinv6.sparse.lengths sd3 s6.scratch.probings).1,
                        by assumption, fun sd4 => ?_⟩
                      c0_hsteps_nogrp
                      have hst6 := fullState_upd_probe_step hinv6.sparse.lengths sd3
                        s6.scratch.probings
                      have hst6' := fullState_upd_elim_step hst6.1 sd4 s6.scratch.eliminations
                        s6.scratch.elim_bound
                      have hinv6' := fullM6HdrInv_of_probeStep hinv6
                        (probeStep_trans hst6 hst6')
                      exact hQ 1#64 c6 ext5 _ _ hcmp6 hinv6'.sparse.lengths hinv6'.cfgOk
                        hinv6'.extOk (Or.inr (Or.inl rfl))
                        (by rw [hst6'.2.1, hst6.2.1]; exact hfu6) (fun h => by cases h)
                        (fun _ => ⟨hinv6', by rw [hst6'.2.1, hst6.2.1]; exact hcl6⟩)
                        (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
                  · intro JC2 hJC2
                    c0_hsteps_nogrp; c0_call hCompNeed
                    refine ⟨c4, s5, m6ExtMem (m6ExtAddr c4.hdr) ext5 ⋆ R, rfl, hlen5,
                      by have := hlen5.core_ok.trail_end_le; have := hlen5.core_ok.cur_vars_le
                         have := c4.hmaxv; unfold dimacsBound at *; omega,
                      hm5f, fun need _ => ?_⟩
                    c0_hsteps_nogrp
                    · c0_call hCompact
                      refine ⟨c4, F0, s5, m6ExtMem (m6ExtAddr c4.hdr) ext5 ⋆ R, rfl, hinv5.sparse,
                        hm5f, fun rC c6 s6 m6 hcmpC hspC hrC _ hfuC huC h1C hm6 => ?_⟩
                      have hcfg6 := M6HdrCfgOk_of_le
                        (by rw [hcmpC.hdr]; exact M6HdrCfgOk_le hinv5.cfgOk)
                      have hinv6 := FullM6HdrInv.mk_inv hcfg6 hext5 hspC
                      have hm6' := fullM6HdrMem_unfocus (hcmpC.hdr ▸ hm6)
                      have hcmp6 := hcmp4.trans hcmpC
                      have hfu6 := Nat.le_trans hfuC hfu5'
                      c0_hsteps_nogrp
                      · exact hQ 20#64 c6 ext5 s6 m6 hcmp6 hspC.lengths hcfg6 hext5
                          (Or.inr (Or.inr (Or.inr rfl))) hfu6 (fun _ => huC ‹_›)
                          (fun h => by cases h) (fun h => by cases h) hm6'
                      · exact hQ 0#64 c6 ext5 s6 m6 hcmp6 hspC.lengths hcfg6 hext5
                          (Or.inl rfl) hfu6 (fun h => by cases h)
                          (fun h => by cases h) (fun h => by cases h) hm6'
                      · exact hJC2 () m6 ⟨c6, s6, hcmp6, hinv6, h1C ‹_›, hfu6, hm6'⟩
                    · exact hJC2 () m5 ⟨c4, s5, hcmp4, hinv5, hcl5, hfu5',
                        fullM6HdrMem_unfocus hm5f⟩
          · intro JC1 hJC1
            c0_hsteps_nogrp; c0_call hCompNeed
            refine ⟨c, s3, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen3,
              by have := hlen3.core_ok.trail_end_le; have := hlen3.core_ok.cur_vars_le
                 have := c.hmaxv; unfold dimacsBound at *; omega,
              hm3f, fun need _ => ?_⟩
            c0_hsteps_nogrp
            · c0_call hCompact
              refine ⟨c, F0, s3, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv3.sparse,
                hm3f, fun rC c4 s4 m4 hcmp4 hsp4 hrC _ hfu4 huC h1C hm4 => ?_⟩
              have hcfg4 := M6HdrCfgOk_of_le (by rw [hcmp4.hdr]; exact M6HdrCfgOk_le hinv3.cfgOk)
              have hinv4 := FullM6HdrInv.mk_inv hcfg4 hinv3.extOk hsp4
              have hm4' := fullM6HdrMem_unfocus (hcmp4.hdr ▸ hm4)
              have hfu4' := Nat.le_trans hfu4 hfu3'
              c0_hsteps_nogrp
              · exact hQ 20#64 c4 ext s4 m4 hcmp4 hsp4.lengths hcfg4 hinv4.extOk
                  (Or.inr (Or.inr (Or.inr rfl))) hfu4' (fun _ => huC ‹_›)
                  (fun h => by cases h) (fun h => by cases h) hm4'
              · exact hQ 0#64 c4 ext s4 m4 hcmp4 hsp4.lengths hcfg4 hinv4.extOk
                  (Or.inl rfl) hfu4' (fun h => by cases h)
                  (fun h => by cases h) (fun h => by cases h) hm4'
              · exact hJC1 () m4 ⟨c4, s4, hcmp4, hinv4, h1C ‹_›, hfu4', hm4'⟩
            · exact hJC1 () m3 ⟨c, s3, FullM4Compact.FullCfgCompat.refl c, hinv3, hcl3, hfu3',
                fullM6HdrMem_unfocus hm3f⟩
    · intro J2 hJ2; c0_hsteps_nogrp
      · refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
        obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
        c0_hsteps_nogrp; c0_call hSweep
        refine ⟨c, F0, F_cur1, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
          hinv1.sparse.lengths, hw1, hinv1.sparse.2.2.1, hinv1.sparse.2.2.2.2,
          fun hpos => by omega, hm1f,
          fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen'
            wu' fred' ni' nr' nb' oom' sc' mS hlenS hsr hexlenS hws2S hllS hwS hndS
            _ _ _ h20S _ hmS => ?_⟩
        have hmS' := fullM6HdrMem_unfocus hmS
        let sSc : FullCoreState :=
          { s1.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
        let sS : FullState := { core := sSc, scratch := sc' }
        have hinvWS : FullM6HdrInvW c F0 F_cur1 ext sS :=
          FullM6HdrInvW.mk_inv hinv1.cfgOk hinv1.extOk
            ⟨hlenS, hwS, hinv1.sparse.2.1, hndS,
              ⟨hllS, (by
                change sc'.extend_len ≤ c.extend_cap
                rw [hexlenS]; exact hinv1.sparse.2.2.2.1.2)⟩,
              hinv1.sparse.2.2.2.2⟩
        c0_hsteps_nogrp
        · exact hQ 20#64 c ext sS mS (FullM4Compact.FullCfgCompat.refl c) hlenS hinvWS.cfgOk
            hinvWS.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu1 (fun _ => (h20S ‹_›).2)
            (fun h => by cases h) (fun h => by cases h) hmS'
        · refine mp_call_bcp rfl (fun _ _ h => hProp _ _ _ _ h) hinvWS hmS'
            fun pr sP mP hinvWP hclP _ _ hfuP _ hrP1 hmP => ?_
          have hinvP := hinvWP.toInv
          have hfuP' := Nat.le_trans hfuP hfu1
          c0_hsteps_nogrp
          · exact hQ 20#64 c ext sP mP (FullM4Compact.FullCfgCompat.refl c) hinvP.sparse.lengths
              hinvP.cfgOk hinvP.extOk (Or.inr (Or.inr (Or.inr rfl))) hfuP'
              (fun _ => mp_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hcl1') (hrP1 ‹_›).2.2)
              (fun h => by cases h) (fun h => by cases h) hmP
          · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
            c0_hsteps_nogrp
            have hinvP' : FullM6HdrInv c F0 ext
                { sP with core := { sP.core with unflushed := 0#64 } } :=
              FullM6HdrInv.mk_inv hinvP.cfgOk hinvP.extOk
                ⟨⟨⟨{ hinvP.sparse.lengths.core_ok with
                      vals_len := hinvP.sparse.lengths.core_ok.vals_len },
                    hinvP.sparse.lengths.scratch_ok⟩,
                  ⟨F_cur1, { hinvWP.sparseW.2.1 with
                    arena := { hinvWP.sparseW.2.1.arena with
                      len_ok := hinvWP.sparseW.2.1.arena.len_ok }
                    watches := hinvWP.sparseW.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                      (fun _ r => r) }⟩⟩,
                  hinvP.sparse.2.1, hinvP.sparse.2.2.1, hinvP.sparse.2.2.2.1,
                  hinvP.sparse.2.2.2.2⟩
            exact hJ2 () _ ⟨_, hinvP', hclP ▸ hcl1', hfuP', fullM6HdrMem_unfocus (by assumption)⟩
      · exact hJ2 () m1 ⟨s1, hinv1, hcl1', hfu1, fullM6HdrMem_unfocus hm1f⟩


private theorem full_simplify_m6_compact_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProbe : ∀ a m Q X, FullM6Orch.m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Γ "full_eliminate_m6" [i64, .bool] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Func.wp Γ full_simplify_m6_body a m Q X := by
  rintro ⟨h, dp, de, ⟨⟩⟩ m Q X hs
  rcases fullM6SimplifySpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_simplify_m6_body
  -- Step 1: backtrack to 0 if needed.
  refine wp_join_group (fun (_ : Tup Val []) m0 => ∃ s0, FullM6HdrInv c F0 ext s0 ∧
      s0.core.cur_level = 0 ∧ s0.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext s0 ⋆ R) m0) ?_ ?_
  · rintro _ _ m0 ⟨s0, hinv0, hcl0, hfu0, hm0⟩
    -- Step 2: optional `do_probe -> full_probe_m6(h, false)`.
    refine wp_join_group (fun (_ : Tup Val []) m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
        s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
    · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      c0_hsteps_nogrp
      · exact hQ 0#64 c ext1 s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths
          hinv1.cfgOk hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h) hm1
      · exact hQ 0#64 c ext1 s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths
          hinv1.cfgOk hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h) hm1
      · -- Step 3: optional `do_elim -> full_eliminate_m6(h, false)`.
        refine wp_join_group (fun (_ : Tup Val []) m2 => ∃ s2, FullM6HdrInv c F0 ext1 s2 ∧
            s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullM6HdrMem c ext1 s2 ⋆ R) m2) ?_ ?_
        · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
          refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
          c0_hsteps_nogrp
          · exact hQ 20#64 c ext1 s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.sparse.lengths
              hinv2.cfgOk hinv2.extOk (Or.inr (Or.inr rfl)) hfu2
              (fun _ => fullM6HdrInv_inconsistent_unsat hinv2 ‹_›) (fun h => by cases h) hm2
          · exact hQ 0#64 c ext1 s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.sparse.lengths
              hinv2.cfgOk hinv2.extOk (Or.inl rfl) hfu2
              (fun h => by cases h) (fun h => by cases h) hm2
          · -- Step 4: optional `compact_needed` -> `full_compact`.
            refine wp_join_group (fun (_ : Tup Val []) m3 => ∃ c3 s3,
                FullM4Compact.FullCfgCompat c c3 ∧
                FullM6HdrInv c3 F0 ext1 s3 ∧ s3.core.cur_level = 0 ∧
                s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c3 ext1 s3 ⋆ R) m3) ?_ ?_
            · rintro _ _ m3 ⟨c3, s3, hcmp3, hinv3, hcl3, hfu3, hm3⟩
              rw [← hcmp3.hdr]
              refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_
              c0_hsteps_nogrp
              · exact hQ 20#64 c3 ext1 s3 m3 hcmp3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inr (Or.inr rfl)) hfu3
                  (fun _ => fullM6HdrInv_inconsistent_unsat hinv3 ‹_›) (fun h => by cases h) hm3
              · exact hQ 0#64 c3 ext1 s3 m3 hcmp3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inl rfl) hfu3 (fun h => by cases h) (fun h => by cases h) hm3
              · exact hQ 1#64 c3 ext1 s3 m3 hcmp3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inr (Or.inl rfl)) hfu3 (fun h => by cases h)
                  (fun _ => ⟨hinv3, hcl3⟩) hm3
            · intro J3 hJ3
              c0_hsteps_nogrp; c0_call hCompNeed
              refine ⟨c, s2, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv2.sparse.lengths,
                by have := hinv2.sparse.lengths.core_ok.trail_end_le
                   have := hinv2.sparse.lengths.core_ok.cur_vars_le
                   have := c.hmaxv; unfold dimacsBound at *; omega,
                hm2f, fun need _ => ?_⟩
              c0_hsteps_nogrp
              · c0_call hCompact
                refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv2.sparse,
                  hm2f, fun rC c3 s3 m3 hcmp3 hsp3 hrC _ hfu3 hu3 h13 hm3 => ?_⟩
                have hcfg3 := M6HdrCfgOk_of_le (by rw [hcmp3.hdr]; exact M6HdrCfgOk_le hinv2.cfgOk)
                have hinv3 := FullM6HdrInv.mk_inv hcfg3 hinv2.extOk hsp3
                have hm3' := fullM6HdrMem_unfocus (hcmp3.hdr ▸ hm3)
                have hfu3' := Nat.le_trans hfu3 hfu2
                c0_hsteps_nogrp
                · exact hQ 20#64 c3 ext1 s3 m3 hcmp3 hsp3.lengths hcfg3 hinv3.extOk
                    (Or.inr (Or.inr rfl)) hfu3' (fun _ => hu3 ‹_›)
                    (fun h => by cases h) hm3'
                · exact hQ 0#64 c3 ext1 s3 m3 hcmp3 hsp3.lengths hcfg3 hinv3.extOk
                    (Or.inl rfl) hfu3' (fun h => by cases h) (fun h => by cases h) hm3'
                · exact hJ3 () m3 ⟨c3, s3, hcmp3, hinv3, h13 hc, hfu3', hm3'⟩
              · exact hJ3 () m2 ⟨c, s2, FullM4Compact.FullCfgCompat.refl c, hinv2, hcl2, hfu2, hm2⟩
        · intro J2 hJ2
          c0_hsteps_nogrp
          · c0_call hElim
            refine ⟨c, F0, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv1.sparse, hcl1,
              hm1f, fun rE s2 m2 hsp2 hcl2 hfu2 hr2 hu2 hm2 => ?_⟩
            have hinv2 := FullM6HdrInv.mk_inv hinv1.cfgOk hinv1.extOk hsp2
            have hm2' := fullM6HdrMem_unfocus hm2
            c0_hsteps_nogrp
            · exact hQ 20#64 c ext1 s2 m2 (FullM4Compact.FullCfgCompat.refl c) hsp2.lengths
                hinv2.cfgOk hinv2.extOk (Or.inr (Or.inr rfl)) (Nat.le_trans hfu2 hfu1)
                (fun _ => hu2 ‹_›) (fun h => by cases h) hm2'
            · exact hJ2 () m2 ⟨s2, hinv2, hcl2, Nat.le_trans hfu2 hfu1, hm2'⟩
          · exact hJ2 () m1 ⟨s1, hinv1, hcl1, hfu1, hm1⟩
    · intro J1 hJ1; c0_hsteps_nogrp
      · c0_call hProbe
        refine FullM6Orch.m6ProbeSpec_of hinv0 hcl0 hm0
          fun rP ext1 s1 m1 hlen1 hext1 hfu1 hr1 hu1 h11 hm1 => ?_
        have hfu1' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [← hfu0]; exact hfu1
        c0_hsteps_nogrp
        · exact hQ 20#64 c ext1 s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1 hinv0.cfgOk hext1
            (Or.inr (Or.inr rfl)) hfu1' (fun _ => hu1 ‹_›) (fun h => by cases h) hm1
        · obtain ⟨hinv1, hcl1⟩ := h11 (hr1.resolve_right ‹_›)
          exact hJ1 () m1 ⟨ext1, s1, hinv1, hcl1, hfu1', hm1⟩
      · exact hJ1 () m0 ⟨ext, s0, hinv0, hcl0, by rw [hfu0]; exact Nat.le_refl _, hm0⟩
  · intro J0 hJ0
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp
    · obtain ⟨hcl_lt, htl_bd, htrl_bd⟩ := mp_fullInv_of_backtrack0 hinv
      obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
      c0_call hBacktrack
      refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse.lengths,
        hcl_lt, htl_bd, htrl_bd, hmf, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass'
          sc' m' hlen' hte' hprop' hcl' _ hsc _ _ hwi _ hm' => ?_⟩
      have hcl0' : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
      let s0c : FullCoreState :=
        { s.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
      let s0 : FullState := { core := s0c, scratch := sc' }
      obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := hsc
      have hsp0 : FullSparseInv c F0 s0 :=
        ⟨⟨hlen', F_cur, hwi F0 F_cur hw (Nat.zero_le _)⟩,
          by unfold FullLitMarksClear FullMrkZero; exact hinv.sparse.2.1,
          by unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb
               fullArenaClauseLits; exact hinv.sparse.2.2.1,
          FullExtScratchOk.of_pres hinv.sparse.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
          hinv.sparse.2.2.2.2⟩
      exact hJ0 () _ ⟨s0, FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp0,
        hcl0', rfl, fullM6HdrMem_unfocus hm'⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have := hinv.sparse.1.witness.choose_spec.cur_level_le
        have := hinv.sparse.lengths.core_ok.trail_end_le
        have := hinv.sparse.lengths.core_ok.cur_vars_le
        have := c.hmaxv; unfold dimacsBound at *
        have hnot : ¬ 0 < s.core.cur_level % 2 ^ 64 := ‹_›
        rw [Nat.mod_eq_of_lt (by omega)] at hnot; omega
      exact hJ0 () m ⟨s, hinv, hcl0, rfl, hm⟩


/-! ## 2. Closed `M7PlusEnv` & Hot-BCP/Vivification/Compact Helper Table -/

def mpHasBinFn : Fn :=
  ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.full_has_bin_body⟩

def mpExtraBaseFns : List Fn :=
  [ ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
  , FullM7BcpHot.m7PropLitOvfFn
  , FullM7BcpHot.m7PropChronoFn
  , mpHasBinFn ] ++
  FullM6VivBackbone.m6VivBackbone_fns.take 1 ++
  (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25

def mpExtraBaseRows : List SpecEntry :=
  [ ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
  , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
      FullM7BcpHot.fullPropChronoHotSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩ ] ++
  FullM6VivBackbone.m6VivBackboneSpecTable.take 1 ++
  (FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 25

def mpExtraRows : List SpecEntry :=
  mpExtraBaseRows ++
  [ ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_compact_needed", [i64], [.bool], FullM4Compact.fullCompactNeededSpec, true⟩ ]

private theorem mpExtraRows_nodup : (mpExtraRows.map SpecEntry.name).Nodup := by
  show ([ "m6_hdr_init", "m6_ext_ensure_init", "full_prop_lit_ovf_hot", "full_prop_chrono_hot"
    , "full_has_bin", "full_add_bin_m6"
    , "full_viv_unreason_m6", "full_viv_watch_rank_m6", "full_viv_best_watch_m6"
    , "full_viv_simplify_m6", "full_viv_commit_m6", "full_viv_mark_garb_m6"
    , "full_viv_subsumes_bin_m6", "full_viv_subsumes_cl_m6", "full_viv_deduce_m6"
    , "full_viv_best_implied_m6", "full_viv_reestablish_m6", "full_viv_inst_check_m6"
    , "full_viv_inst_m6", "full_viv_finish_m6", "full_viv_sort_counts_m6"
    , "full_viv_has_l0_m6", "full_viv_l0_simp_m6", "full_viv_reuse_prefix_m6"
    , "full_viv_clause_m6", "full_viv_tier_match_m6", "full_viv_collect_m6"
    , "full_viv_count_m6", "full_viv_keys_m6", "full_viv_sort_sched_m6"
    , "full_viv_clear_tier_m6", "full_vivify_tier_m6_hdr", "full_compact_needed" ] :
      List String).Nodup
  decide

private theorem mpExtraRows_noExit : ∀ e ∈ mpExtraRows, e.noExit = true := by
  intro e he
  exact List.all_eq_true.mp (by t_kernel_rfl : mpExtraRows.all (·.noExit) = true) e he

private theorem mp_ofTable_name_mem {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    ∀ {tbl : List SpecEntry},
    Env.ofTable tbl nm as bs xs m Q X → nm ∈ tbl.map SpecEntry.name
  | [], h => False.elim h
  | e :: _, h => by
    by_cases hnm : e.name = nm
    · rw [← hnm]; exact List.mem_cons_self
    · rw [Env.ofTable_cons_ne hnm] at h
      exact List.mem_cons_of_mem _ (mp_ofTable_name_mem h)


/-- Closed `M7Plus` environment extending `m7PlusBaseEnv` with `mpExtraRows` (`31` base helpers,
`full_vivify_tier_m6_hdr`, and `FullM4Compact.fullCompactNeededSpec`). -/
inductive M7PlusEnv (Γ : Env) : Env where
  | base {f as bs xs m Q X} :
      f ≠ "full_vivify_tier_m6_hdr" →
      f ≠ "full_compact_needed" →
      Γ f as bs xs m Q X → M7PlusEnv Γ f as bs xs m Q X
  | extra {f as bs xs m Q X} :
      Env.ofTable mpExtraRows f as bs xs m Q X →
      M7PlusEnv Γ f as bs xs m Q X

/-- Canonical closed `Env` for `m7PlusModule` (`410` fns, `0` hooks, zero SAT model proofs). -/
def m7PlusEnv : Env := M7PlusEnv m7PlusBaseEnv

theorem m7PlusEnv_noExit : ∀ f as bs xs m Q X X',
    m7PlusEnv f as bs xs m Q X → m7PlusEnv f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  cases h with
  | base h1 h2 hb => exact .base h1 h2 (m7PlusBaseEnv_noExit _ _ _ _ _ _ _ _ hb)
  | extra he => exact .extra (Env.ofTable_noExit mpExtraRows_noExit _ _ _ _ _ _ _ _ he)

theorem m7PlusEnv_solve_bytes_iff {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7PlusEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      m7PlusSolveBytesSpec xs m Q (fun _ _ _ _ => False) := by
  constructor
  · intro h
    cases h with
    | base _ _ hb => exact m7PlusBase_solve_bytes_iff.mp hb
    | extra he => exact False.elim (absurd (mp_ofTable_name_mem he) (by decide))
  · intro hs
    exact M7PlusEnv.base (by decide) (by decide) (m7PlusBase_solve_bytes_iff.mpr hs)

theorem m7PlusEnv_solve_bytes {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m7PlusSolveBytesSpec xs m Q X) :
    m7PlusEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  m7PlusEnv_solve_bytes_iff.mpr (m7PlusSolveBytesSpec_monoX hs)

private theorem mp_extra_at {Γ : Env} (i : Nat) (nm : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hi : mpExtraRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → M7PlusEnv Γ nm as bs xs m Q X := fun xs m Q X hs =>
  M7PlusEnv.extra (Env.ofTable_of_mem (List.mem_of_getElem? hi) mpExtraRows_nodup
    (hno xs m Q X hs))

private theorem mp_extra_elim {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ mpExtraRows)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable mpExtraRows nm as bs xs m Q X) :
    sp xs m Q (fun _ _ _ _ => False) :=
  env_ofTable_elim_of_mem hmem mpExtraRows_nodup h

private theorem mp_extra_elim_cast {e : SpecEntry} {fn : Fn}
    (hmem : e ∈ mpExtraRows)
    (hnm : e.name = fn.name) (has : e.as = fn.as) (hrs : e.rs = fn.rs)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Env.ofTable mpExtraRows fn.name fn.as fn.rs xs m Q X) :
    e.cast has hrs xs m Q X := by
  cases e with
  | mk enm eas ers esp enx =>
    dsimp only at hnm has hrs
    cases hnm; cases has; cases hrs
    exact env_ofTable_elim_of_mem hmem mpExtraRows_nodup h

private theorem mp_tableImpl_getElem {Γ : Env} :
    ∀ {fs : List Fn} {rs : List SpecEntry} (i : Nat)
      (h1 : i < fs.length) (h2 : i < rs.length),
      TableImpl Γ fs rs → SpecEntry.Impl Γ (fs[i]'h1) (rs[i]'h2)
  | [], _, i, h1, _, _ => absurd h1 (Nat.not_lt_zero i)
  | _ :: _, [], _, _, _, ht => False.elim ht
  | _ :: _, _ :: _, 0, _, _, ht => ht.1
  | _ :: _, _ :: _, i + 1, h1, h2, ht =>
    mp_tableImpl_getElem i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2) ht.2

private def mpBadNames : List Sym :=
  [ "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr", "full_compact_needed"
  , "full_probe_tail_m6", "full_probe_m6", "full_preprocess_m6", "full_simplify_m6"
  , "full_search_m6", "kissat_solve_bytes_m6", "full_preprocess", "full_search"
  , "kissat_solve_bytes" ]

private def mpOkName (f : Sym) : Bool :=
  !(mpBadNames.any (· == f))

mutual
private def mpNoCallBad {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → Bool
  | .let_ _ k => mpNoCallBad (k (Tup.units _))
  | .load _ _ k => mpNoCallBad (k ())
  | .store _ _ k => mpNoCallBad k
  | .call f _ k => mpOkName f && mpNoCallBad (k (Tup.units _))
  | .jnz _ t e => mpNoCallBad t && mpNoCallBad e
  | .jump _ _ | .ret _ | .hlt | .exit _ _ => true
  | .group (sig := sig) bodies k =>
      mpBlocksNoCallBad (bodies (Tup.units sig)) && mpNoCallBad (k (Tup.units sig))

private def mpBlocksNoCallBad {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => mpNoCallBad (b (Tup.units _)) && mpBlocksNoCallBad bs
end

mutual
private theorem mp_callsOk_filter {allowed : List SigEntry}
    {exits : List Sym} {rs : List Ty} :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    e.callsOk allowed exits → mpNoCallBad e = true →
    e.callsOk (allowed.filter (fun s => mpOkName s.1)) exits
  | .let_ _ k, hc, hn => mp_callsOk_filter (k (Tup.units _)) hc hn
  | .load _ _ k, hc, hn => mp_callsOk_filter (k ()) hc hn
  | .store _ _ k, hc, hn => mp_callsOk_filter k hc hn
  | .call f (as := _) (bs := bs) _ k, hc, hn => by
    change (mpOkName f && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨List.mem_filter.mpr ⟨hc.1, h1⟩, mp_callsOk_filter (k (Tup.units bs)) hc.2 h2⟩
  | .jnz _ t e, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨mp_callsOk_filter t hc.1 h1, mp_callsOk_filter e hc.2 h2⟩
  | .jump _ _, hc, _ | .ret _, hc, _ | .hlt, hc, _ | .exit _ _, hc, _ => hc
  | .group (sig := sig) bodies k, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨mp_blocksCallsOk_filter (bodies (Tup.units sig)) hc.1 h1,
      mp_callsOk_filter (k (Tup.units sig)) hc.2 h2⟩

private theorem mp_blocksCallsOk_filter {allowed : List SigEntry}
    {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    bs.callsOk allowed exits → mpBlocksNoCallBad bs = true →
    bs.callsOk (allowed.filter (fun s => mpOkName s.1)) exits
  | _, .nil, _, _ => trivial
  | _, .cons b bs, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨mp_callsOk_filter (b (Tup.units _)) hc.1 h1, mp_blocksCallsOk_filter bs hc.2 h2⟩
end

private theorem mp_all_nonbad_no_bad :
    (m7Fns.filter (fun fn => mpOkName fn.name)).all
      (fun fn => mpNoCallBad (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))) =
      true := by
  t_kernel_rfl

private theorem mp_extraBaseFns_sigs :
    mpExtraBaseRows.map (fun e => (e.name, e.as, e.rs)) = mpExtraBaseFns.map Fn.sig := by
  t_kernel_rfl

private theorem mp_fn_81 : m7Fns[81]? = some FullM7BcpHot.m7PropLitOvfFn := by
  rw [m7_get_p1 (by decide)]; t_kernel_rfl

private theorem mp_fn_82 : m7Fns[82]? = some FullM7BcpHot.m7PropChronoFn := by
  rw [m7_get_p1 (by decide)]; t_kernel_rfl

private theorem mp_extraBaseFns_sub : ∀ f ∈ mpExtraBaseFns, f ∈ m7Fns := by
  have hf54 : m7Fns[54]? = some ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩ := by
    rw [m7_get_p1 (by decide)]; t_kernel_rfl
  have hf56 : m7Fns[56]? = some ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩ := by
    rw [m7_get_p1 (by decide)]; t_kernel_rfl
  have hf175 : m7Fns[175]? = some mpHasBinFn := by
    rw [show (175 : Nat) = 112 + 63 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hf177 : (m7FnsPart2.drop 65).take 1 = FullM6VivBackbone.m6VivBackbone_fns.take 1 := by
    t_kernel_rfl
  have hfViv : (m7FnsPart2.drop 79).take 25 =
      (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25 := by t_kernel_rfl
  intro f hf
  simp only [mpExtraBaseFns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with ((rfl | rfl | rfl | rfl | rfl) | hab) | hviv
  · exact List.mem_of_getElem? hf54
  · exact List.mem_of_getElem? hf56
  · exact List.mem_of_getElem? mp_fn_81
  · exact List.mem_of_getElem? mp_fn_82
  · exact List.mem_of_getElem? hf175
  · rw [← hf177] at hab
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_of_mem_drop (List.mem_of_mem_take hab)))
  · rw [← hfViv] at hviv
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_of_mem_drop (List.mem_of_mem_take hviv)))

private theorem mp_hasBin_wp (Γ : Env) :
    ∀ a m Q X, Full.fullHasBinSpec a m Q X → Func.wp Γ Full.full_has_bin_body a m Q X := by
  have hf97 : Full.fullFns[97]? = some mpHasBinFn := by t_kernel_rfl
  have hndF : ((Full.fullSpecTable Full.fullSolveBytesSpec).map SpecEntry.name).Nodup := by
    have hm := congrArg (List.map Prod.fst) (Full.fullSpecTable_sigs Full.fullSolveBytesSpec)
    have hn : (Full.fullSpecTable Full.fullSolveBytesSpec).map SpecEntry.name =
        Full.fullFns.map Fn.name := by
      simpa only [List.map_map, Function.comp_def, Fn.sig] using hm
    exact tbl_nodup_of_sigs (M := Full.fullModule) Full.full_acyclic hn
  have hrow97 : (Full.fullSpecTable Full.fullSolveBytesSpec)[97]? =
      some ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩ := by
    t_kernel_rfl
  obtain ⟨pre, post, hsp⟩ := List.append_of_mem (List.mem_of_getElem? hf97)
  have ⟨hwf, _, hwp⟩ := Full.fullEnv_moduleOk.fnsOk pre mpHasBinFn post hsp
  have hcalls : mpHasBinFn.callsOk [] [] := Fn.callsOk_of_checkCallsOk (by t_kernel_rfl)
  intro xs m Q X hspec
  have henv : Full.fullEnv "full_has_bin" [i64, i32, i32] [.bool] xs m Q X :=
    Env.ofTable_of_mem (List.mem_of_getElem? hrow97) hndF hspec
  exact wp_env_agree_of_callsOk
    (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units _))
    hcalls (fun _ _ _ h => nomatch h) m (hwp xs m Q X henv)


private theorem mp_base_at {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7PlusBaseTable)
    (hne1 : nm ≠ "full_vivify_tier_m6_hdr" := by decide)
    (hne2 : nm ≠ "full_compact_needed" := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → m7PlusEnv nm as bs xs m Q X := fun xs m Q X hsp =>
  M7PlusEnv.base hne1 hne2 (m7PlusBase_row_mem hmem hno xs m Q X hsp)


/-! ## 3. Closed `410/410` `m7Plus_moduleOk`, UNSAT Soundness & Tier-3b UNSAT Non-Vacuity -/

private theorem mp_ne_of_find_none {r0 g : Fn} (hrm : r0 ∈ m7PlusRepls)
    (hfind : m7PlusRepls.find? (fun r => r.name == g.name) = none) :
    g.name ≠ r0.name := by
  intro heq
  have h1 : (m7PlusRepls.find? (fun r => r.name == g.name)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨r0, hrm, by simp [heq]⟩
  rw [hfind] at h1
  cases h1

private theorem mp_idx_403 : m7Fns[403]? = some m6oPreprocessM6Fn := by
  rw [show (403 : Nat) = 276 + 127 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mp_idx_404 : m7Fns[404]? = some m6oSimplifyM6Fn := by
  rw [show (404 : Nat) = 276 + 128 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mp_idx_405 :
    m7Fns[405]? = some ⟨"full_search_m6", [i64], [i64], FullM7.full_search_m6_body⟩ := by
  rw [show (405 : Nat) = 276 + 129 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mp_idx_406 : m7Fns[406]? = some FullM6Orch.m6oSolveBytesM6Fn := by
  rw [show (406 : Nat) = 276 + 130 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mp_idx_407 :
    m7Fns[407]? = some ⟨"full_preprocess", [i64], [i64], FullM6Orch.full_preprocess_body⟩ := by
  rw [show (407 : Nat) = 276 + 131 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mp_idx_408 :
    m7Fns[408]? = some ⟨"full_search", [i64], [i64], FullM6Orch.full_search_body⟩ := by
  rw [show (408 : Nat) = 276 + 132 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mp_idx_409 : m7Fns[409]? = some FullM6Orch.m6oSolveBytesFn := by
  rw [show (409 : Nat) = 276 + 133 by rfl, m7_get_p3]; t_kernel_rfl

private def mpMidEnv : Env :=
  fun f as bs xs m Q X => mpOkName f = true ∧ m7PlusBaseEnv f as bs xs m Q X

theorem m7Plus_checkAcyclic : m7PlusModule.checkAcyclic = true := m7Plus_acyclic

private theorem mpSpliceModule_moduleOk {Γ Γ' : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) {repls : List Fn}
    (hchk : ({ M with fns := mpSpliceFns repls M.fns } : LeanQbe.T.Module).checkAcyclic = true)
    (hrWf : ∀ r ∈ repls, r.Wf)
    (hCallee : ∀ f as bs xs m Q X, Γ f as bs xs m Q X → Γ' f as bs xs m Q X)
    (hFnWp : ∀ g ∈ M.fns, repls.find? (fun x => x.name == g.name) = none →
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Func.wp Γ' g.body xs m Q X) ∨
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Γ g.name g.as g.rs xs m Q X))
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X,
      Γ' r.name r.as r.rs xs m Q X → Func.wp Γ' r.body xs m Q X) :
    ModuleOk Γ' { M with fns := mpSpliceFns repls M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic hchk (mpSpliceFns_wf hwfOrig hrWf) ?_
  intro fn hmem
  rcases List.mem_map.mp hmem with ⟨g, hg, rfl⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | some r =>
    intro xs m Q X hspec
    exact hrWp r (List.mem_of_find?_eq_some h) xs m Q X hspec
  | none =>
    intro xs m Q X hspec
    rcases hFnWp g hg h with hNew | hPull
    · exact hNew xs m Q X hspec
    · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
      have ⟨hwfG, hcallsG, hwpG⟩ := hM.fnsOk pre g post hsplit
      exact wp_env_agree_of_callsOk
        (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
        hcallsG (fun f as bs _ => hCallee f as bs) m
        (hwpG xs m Q X (hPull xs m Q X hspec))

/-- Closed `410/410` `ModuleOk` certifying `m7PlusModule` (`PLUS_T8_tie1_bb20`) under `m7PlusEnv`
with `0` external hooks, `0` `sorry`/`axiom`, and zero SAT model proofs. -/
theorem m7Plus_moduleOk : ModuleOk m7PlusEnv m7PlusModule := by
  have hnd := m7PlusBaseTable_nodup
  have hbaseOk := m7PlusBase_moduleOk
  have hc1 := m7PlusPart1Callees_of_sub m7PlusBase_part1_mem
  have hc1p := m7PlusPart1PfxCallees_of_sub m7PlusBase_part1_mem
  have hc1Tail := m7PlusPart1TailCallees_of_sub m7PlusBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7PlusBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7PlusBase_part2_mem
  have hc2gu := m7Part2BvaGuRows_of_sub m7PlusBase_part2_mem
  have hc3 := m7PlusPart3Callees_of_sub m7PlusBase_part3Pfx_mem
  have hc3p := m7PlusPart3PfxCallees_of_sub m7PlusBase_part3Pfx_mem
  have rWp := m7PlusBase_pfx_mem _ m7PlusOrchPfxRows_specs.watchPush
  have rWd := m7PlusBase_pfx_mem _ m7PlusOrchPfxRows_specs.wstackDefrag
  have rArSwp := mp_base_at (m7PlusBase_pfx_mem _ m7PlusOrchPfxRows_specs.arenaSweep)
  have rSwpDense := mp_base_at m7PlusBase_sweepDenseM6_mem
  have rProbeTailMem := m7PlusBase_probeTailM6_mem
  have rProbeMem := m7PlusBase_probeM6_mem
  have rPreM6Mem := m7PlusBase_pfx_mem _ m7PlusOrchPfxRows_specs.preprocessM6
  have rSimpM6Mem := m7PlusBase_pfx_mem _ m7PlusOrchPfxRows_specs.simplifyM6
  have rBt := mp_base_at hc1.backtrack
  have rUnw := mp_base_at hc1.unwatchLarge
  have rAu := mp_base_at hc2.addUnit
  have rAsg := mp_base_at hc1.assign
  have rALvl := mp_base_at hc1.assignLvl
  have rPI := mp_base_at hc1.propagateIgn
  have rNext := mp_base_at hc1.arenaNext
  have rWpEnv := mp_base_at rWp
  have rWdEnv := mp_base_at rWd
  have rProp := mp_base_at hc1.propagate
  have rPropS15 := m7_fullPropagate_to_bcpS15 rProp
  have rSync := mp_base_at hc1.hdrSyncLegacy
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rGetWm := mp_base_at hc1.hdrGetWm
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rSetWm := mp_base_at hc1.hdrSetWm
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rDelay := mp_base_at hc1p.delaying
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rRedD := mp_base_at hc1p.reduceDelay
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rBumpD := mp_base_at hc1p.bumpDelay
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rIlog := mp_base_at hc1.ilog10
  have rScaleM5 := mp_base_at hc1.scaleDeltaM5
  have rScaleD := mp_base_at hc1.scaleDelta
  have rInitFresh := mp_base_at m7PlusP3InitFreshVar_mem
  have rAddBin := mp_base_at hc2.addBin
  have rAddBinCan := m6_add_bin_m6_to_canon rAddBin
  have rAllocCl := mp_base_at hc1.allocCl
  have rDelBin := mp_base_at hc2.deleteBinary
  have rAnaLit := mp_base_at hc2p.analyzeLit
  have rFixedBytes := mp_base_at m7PlusBase_fixedBytes_mem
  have rDedup := mp_base_at m7PlusP3DedupBins_mem
  have rFlushUnits := mp_base_at m7PlusBase_denseFlushUnits_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit _ _ _ _ h)
  have rFlushLg := mp_base_at m7PlusBase_fwdFlushLarge_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullFwdFlushLargeM6Spec_noExit _ _ _ _ h)
  have rReconn := mp_base_at m7PlusBase_fwdReconnIrred_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullFwdReconnectIrredM6Spec_noExit _ _ _ _ h)
  have rCheckCl := mp_base_at m7PlusBase_fwdCheckCl_mem
    (hno := FullM7BveGates.fullFwdCheckClM7Spec_noExit)
  have rConnSub := mp_base_at m7PlusBase_fwdConnSub_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullFwdConnectSubsumerM6Spec_noExit _ _ _ _ h)
  have rColSort := mp_base_at m7PlusBase_fwdColSort_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullFwdCollectSortM6Spec_noExit _ _ _ _ h)
  have rElimDticks := mp_base_at m7PlusP3ElimDticks_mem
  have rEnterDense := mp_base_at hc2.enterDense
  have rMinU64 := mp_base_at m7PlusP3MinU64_mem
  have rFwdSub := mp_base_at (m7PlusBase_bve_mem _ m7PlusBveRows_specs.fwdSub)
  have rElimBve := mp_base_at m7PlusBase_elimBveM7_mem
  have rFactor := mp_base_at m7PlusP3Factor_mem
  have rRebuild := mp_base_at hc2.rebuildWatches
  have rElimM6 := mp_base_at (m7PlusBase_bve_mem _ m7PlusBveRows_specs.eliminateM6)
  have rLucky := mp_base_at hc2p.lucky
  have rCompact := mp_base_at hc3p.compact
  have rCompNeed := mp_extra_at (Γ := m7PlusBaseEnv) 32 "full_compact_needed" [i64] [.bool]
    FullM4Compact.fullCompactNeededSpec rfl
  have rBackbone := mp_base_at hc2p.backboneM6
  have rTrans := mp_base_at hc2p.transitiveM6
  have rProbeRun := mp_base_at hc2p.probeRun
  have rVivM6 := mp_base_at hc2p.vivifyM6Hdr
    (hno := fun _ _ _ _ h => m6aVivifySpec_monoX h)
  have rDticks := mp_base_at hc3p.probeDticks
    (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rCongDense := mp_base_at hc2p.congruenceDense
  have rSubst := mp_base_at hc2p.substitute
  have rProbeTail := mp_base_at rProbeTailMem
    (hno := fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
  have rProbe := mp_base_at rProbeMem
    (hno := fun _ _ _ _ h => FullM6Orch.m6ProbeSpec_monoX h)
  have rInit := mp_extra_at (Γ := m7PlusBaseEnv) 0 "m6_hdr_init" [i64] [] m6HdrInitSpec rfl
    (fun _ _ _ _ h => m6HdrInitSpec_monoX h)
  have rEnsure := mp_extra_at (Γ := m7PlusBaseEnv) 1 "m6_ext_ensure_init" [i64] []
    m6ExtEnsureInitSpec rfl (fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)
  have rOvf := mp_extra_at (Γ := m7PlusBaseEnv) 2 "full_prop_lit_ovf_hot" [i64, i32, i32, i32]
    [.bool] FullM7BcpHot.fullPropLitOvfHotSpec rfl
  have rChrono := mp_extra_at (Γ := m7PlusBaseEnv) 3 "full_prop_chrono_hot" [i64, i64] [.bool]
    FullM7BcpHot.fullPropChronoHotSpec rfl
  have rHb := mp_extra_at (Γ := m7PlusBaseEnv) 4 "full_has_bin" [i64, i32, i32] [.bool]
    Full.fullHasBinSpec rfl
  have rAb6 := mp_extra_at (Γ := m7PlusBaseEnv) 5 "full_add_bin_m6" [i64, i32, i32] [i64]
    FullM6VivBackbone.fullAddBinM6Spec rfl
  have rVivTier := mp_extra_at (Γ := m7PlusBaseEnv) 31 _ _ _ _ rfl
    (fun _ _ _ _ h => m6aVivifyTierSpec_monoX h)
  have r0 := mp_extra_at (Γ := m7PlusBaseEnv) 6 _ _ _ _ rfl
  have r1 := mp_extra_at (Γ := m7PlusBaseEnv) 7 _ _ _ _ rfl
  have r2 := mp_extra_at (Γ := m7PlusBaseEnv) 8 _ _ _ _ rfl
  have r3 := mp_extra_at (Γ := m7PlusBaseEnv) 9 _ _ _ _ rfl
  have r4 := mp_extra_at (Γ := m7PlusBaseEnv) 10 _ _ _ _ rfl
  have r5 := mp_extra_at (Γ := m7PlusBaseEnv) 11 _ _ _ _ rfl
  have r6 := mp_extra_at (Γ := m7PlusBaseEnv) 12 _ _ _ _ rfl
  have r7 := mp_extra_at (Γ := m7PlusBaseEnv) 13 _ _ _ _ rfl
  have r8 := mp_extra_at (Γ := m7PlusBaseEnv) 14 _ _ _ _ rfl
  have r9 := mp_extra_at (Γ := m7PlusBaseEnv) 15 _ _ _ _ rfl
  have r10 := mp_extra_at (Γ := m7PlusBaseEnv) 16 _ _ _ _ rfl
  have r11 := mp_extra_at (Γ := m7PlusBaseEnv) 17 _ _ _ _ rfl
  have r12 := mp_extra_at (Γ := m7PlusBaseEnv) 18 _ _ _ _ rfl
  have r13 := mp_extra_at (Γ := m7PlusBaseEnv) 19 _ _ _ _ rfl
  have r14 := mp_extra_at (Γ := m7PlusBaseEnv) 20 _ _ _ _ rfl
  have r15 := mp_extra_at (Γ := m7PlusBaseEnv) 21 _ _ _ _ rfl
  have r16 := mp_extra_at (Γ := m7PlusBaseEnv) 22 _ _ _ _ rfl
  have r17 := mp_extra_at (Γ := m7PlusBaseEnv) 23 _ _ _ _ rfl
  have r18 := mp_extra_at (Γ := m7PlusBaseEnv) 24 _ _ _ _ rfl
  have r19 := mp_extra_at (Γ := m7PlusBaseEnv) 25 _ _ _ _ rfl
  have r20 := mp_extra_at (Γ := m7PlusBaseEnv) 26 _ _ _ _ rfl
  have r21 := mp_extra_at (Γ := m7PlusBaseEnv) 27 _ _ _ _ rfl
  have r22 := mp_extra_at (Γ := m7PlusBaseEnv) 28 _ _ _ _ rfl
  have r23 := mp_extra_at (Γ := m7PlusBaseEnv) 29 _ _ _ _ rfl
  have r24 := mp_extra_at (Γ := m7PlusBaseEnv) 30 _ _ _ _ rfl
  have hExtraImpl : TableImpl m7PlusEnv mpExtraBaseFns mpExtraBaseRows := by
    have h5 : TableImpl m7PlusEnv
        [ ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
        , ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
        , FullM7BcpHot.m7PropLitOvfFn
        , FullM7BcpHot.m7PropChronoFn
        , mpHasBinFn ]
        [ ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
        , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
        , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
            FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
        , ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
            FullM7BcpHot.fullPropChronoHotSpec, true⟩
        , ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩ ] :=
      ⟨ SpecEntry.Impl.of (m6_hdr_init_wp m7PlusEnv)
      , SpecEntry.Impl.of (m6_ext_ensure_init_wp m7PlusEnv rInit)
      , SpecEntry.Impl.of (FullM7BcpHot.full_prop_lit_ovf_hot_wp m7PlusEnv rWpEnv)
      , SpecEntry.Impl.of (FullM7BcpHot.full_prop_chrono_hot_wp m7PlusEnv rWdEnv rUnw rWpEnv)
      , SpecEntry.Impl.of (mp_hasBin_wp m7PlusEnv), trivial ⟩
    have hAbImpl : TableImpl m7PlusEnv (FullM6VivBackbone.m6VivBackbone_fns.take 1)
        (FullM6VivBackbone.m6VivBackboneSpecTable.take 1) := by
      rw [show FullM6VivBackbone.m6VivBackbone_fns.take 1 =
          [⟨"full_add_bin_m6", [i64, i32, i32], [i64],
            FullM6VivBackbone.full_add_bin_m6_body⟩] from rfl]
      exact ⟨SpecEntry.Impl.of
        (FullM6VivBackbone.full_add_bin_m6_ext_wp m7PlusEnv rHb rALvl rWpEnv), trivial⟩
    have hVivImpl : TableImpl m7PlusEnv ((FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25)
        ((FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 25) := by
      rw [show (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25 =
          [ ⟨"full_viv_unreason_m6", [i64, i32], [], FullM6VivBackbone.full_viv_unreason_m6_body⟩
          , ⟨"full_viv_watch_rank_m6", [i64, i32], [i64],
              FullM6VivBackbone.full_viv_watch_rank_m6_body⟩
          , ⟨"full_viv_best_watch_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_best_watch_m6_body⟩
          , ⟨"full_viv_simplify_m6", [i64, i32], [i64],
              FullM6VivBackbone.full_viv_simplify_m6_body⟩
          , ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64],
              FullM6VivBackbone.full_viv_commit_m6_body⟩
          , ⟨"full_viv_mark_garb_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_mark_garb_m6_body⟩
          , ⟨"full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_subsumes_bin_m6_body⟩
          , ⟨"full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_subsumes_cl_m6_body⟩
          , ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32],
              FullM6VivBackbone.full_viv_deduce_m6_body⟩
          , ⟨"full_viv_best_implied_m6", [i64, i32], [i32],
              FullM6VivBackbone.full_viv_best_implied_m6_body⟩
          , ⟨"full_viv_reestablish_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_reestablish_m6_body⟩
          , ⟨"full_viv_inst_check_m6", [i64, i32, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_inst_check_m6_body⟩
          , ⟨"full_viv_inst_m6", [i64, i32, i32], [i64],
              FullM6VivBackbone.full_viv_inst_m6_body⟩
          , ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64],
              FullM6VivBackbone.full_viv_finish_m6_body⟩
          , ⟨"full_viv_sort_counts_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_sort_counts_m6_body⟩
          , ⟨"full_viv_has_l0_m6", [i64, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_has_l0_m6_body⟩
          , ⟨"full_viv_l0_simp_m6", [i64, i32, i32], [i64],
              FullM6VivBackbone.full_viv_l0_simp_m6_body⟩
          , ⟨"full_viv_reuse_prefix_m6", [i64, i32, i32], [],
              FullM6VivBackbone.full_viv_reuse_prefix_m6_body⟩
          , ⟨"full_viv_clause_m6", [i64, i32], [i64],
              FullM6VivBackbone.full_viv_clause_m6_body⟩
          , ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool],
              FullM6VivBackbone.full_viv_tier_match_m6_body⟩
          , ⟨"full_viv_collect_m6", [i64, i64], [i64],
              FullM6VivBackbone.full_viv_collect_m6_body⟩
          , ⟨"full_viv_count_m6", [i64, i64], [],
              FullM6VivBackbone.full_viv_count_m6_body⟩
          , ⟨"full_viv_keys_m6", [i64, i64], [], FullM6VivBackbone.full_viv_keys_m6_body⟩
          , ⟨"full_viv_sort_sched_m6", [i64, i64], [],
              FullM6VivBackbone.full_viv_sort_sched_m6_body⟩
          , ⟨"full_viv_clear_tier_m6", [i64, i64], [],
              FullM6VivBackbone.full_viv_clear_tier_m6_body⟩ ] from rfl]
      exact ⟨ SpecEntry.Impl.of (FullM6VivBackbone.full_viv_unreason_m6_wp m7PlusEnv rBt)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_watch_rank_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_watch_m6_wp m7PlusEnv r1)
        , SpecEntry.Impl.of
            (FullM6VivBackbone.full_viv_simplify_m6_wp m7PlusEnv rUnw rAu rAb6 rWpEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_commit_m6_wp m7PlusEnv
            rBt rUnw rAu rAb6 rWpEnv r0 r2)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_mark_garb_m6_wp m7PlusEnv r0 rUnw)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_bin_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_cl_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_deduce_m6_wp m7PlusEnv r6 r7)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_implied_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reestablish_m6_wp m7PlusEnv rBt)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_check_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_m6_wp m7PlusEnv
            rBt rAsg rPI r8 r11 r4)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_finish_m6_wp m7PlusEnv
            r8 r5 rBt r4 r10 r12)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_counts_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_has_l0_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_l0_simp_m6_wp m7PlusEnv r15 rBt r3)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reuse_prefix_m6_wp m7PlusEnv rBt)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clause_m6_wp m7PlusEnv
            r16 r14 r17 r9 rAsg rPI rBt r13)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_tier_match_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_collect_m6_wp m7PlusEnv rNext r19)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_count_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_keys_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_sched_m6_wp m7PlusEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clear_tier_m6_wp m7PlusEnv rNext r19)
        , trivial ⟩
    exact tableImpl_append rfl (tableImpl_append rfl h5 hAbImpl) hVivImpl
  have hnotExtra : ∀ (nm : Sym) {as bs xs m Q X}, nm ∉ mpExtraRows.map SpecEntry.name →
      Env.ofTable mpExtraRows nm as bs xs m Q X → False := by
    intro _ _ _ _ _ _ _ hni he; exact hni (mp_ofTable_name_mem he)
  have hTailWp := mpOrchTail_wp m7PlusEnv
    (mp_base_at hc3.luckyLateM7 (hno := fun _ _ _ _ h => FullM7Search.m7LuckyLateSpec_monoX h))
    (mp_base_at hc1Tail.1 (hno := fun _ _ _ _ h => fullM6MemInitExactSpec_monoX h))
    (mp_base_at (m7PlusBase_pfx_mem _ m7PlusOrchPfxRows_specs.parseBody))
    rProp
    (mp_base_at hc2.analyzeM6 (hno := fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h))
    (mp_base_at (m7PlusBase_pfx_mem _ m7PlusOrchPfxRows_specs.reduceM6)
      (hno := fun _ _ _ _ h => m6ReduceSpec_monoX h))
    (mp_base_at hc3.switchModeM7 (hno := fun _ _ _ _ h => FullM7Search.m7SwitchModeSpec_monoX h))
    (mp_base_at hc2.restartDue)
    (mp_base_at hc2.restart)
    (mp_base_at (m7PlusBase_pfx_mem _ m7PlusOrchPfxRows_specs.reorderM6))
    (mp_base_at hc2.rephase (hno := fun _ _ _ _ h => m7RephaseSpec_monoX h))
    (mp_base_at rPreM6Mem (hno := fun _ _ _ _ h => fullM6PreprocessSpec_monoX h))
    (mp_base_at rSimpM6Mem (hno := fun _ _ _ _ h => fullM6SimplifySpec_monoX h))
    (mp_base_at hc3.decideM7 (hno := fun _ _ _ _ h => FullM7Search.m7DecideSpec_monoX h))
    (mp_base_at hc2.extend)
    (mp_base_at hc1Tail.2)
    (mp_base_at m7PlusBase_searchM6_mem (hno := fun _ _ _ _ h => fullM6SearchSpec_monoX h))
    (mp_base_at (m7PlusBase_tail_mem _ (m7PlusOrchTail_solve_mem m7PlusSolveBytesSpec).1)
      (hno := fun _ _ _ _ h => m7PlusSolveBytesSpec_monoX h))
  have hwfOrig : ∀ f ∈ m7Module.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hbaseOk.fnsOk pre f post hsplit).1
  have hMidOk : ModuleOk mpMidEnv m7Module := by
    refine LeanQbe.T.Module.moduleOk_of_checkAcyclic m7_acyclic hwfOrig ?_
    intro g hg xs m Q X hrow
    rcases hrow with ⟨hnbad, hb⟩
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    have ⟨hwfG, hcallsG, hwpG⟩ := hbaseOk.fnsOk pre g post hsplit
    have hnoBad : mpNoCallBad
        (g.body (fun _ => Unit) (fun _ => Unit) (Tup.units g.as)) = true :=
      List.all_eq_true.mp mp_all_nonbad_no_bad g (List.mem_filter.mpr ⟨hg, hnbad⟩)
    exact wp_env_agree_of_callsOk
      (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
      (mp_callsOk_filter _ hcallsG hnoBad)
      (fun f as bs hmem' _ _ _ _ hc => ⟨(List.mem_filter.mp hmem').2, hc⟩)
      m (hwpG xs m Q X hb)
  refine mpSpliceModule_moduleOk hMidOk m7Plus_acyclic m7PlusRepls_wf ?_ ?_ ?_
  · intro f _ _ _ _ _ _ ⟨hok, hb⟩
    exact M7PlusEnv.base
      (fun heq => by subst heq; simp [mpOkName, mpBadNames] at hok)
      (fun heq => by subst heq; simp [mpOkName, mpBadNames] at hok) hb
  · intro g hg hfind
    change g ∈ m7Fns at hg
    have hneViv : g.name ≠ "full_vivify_m6_hdr" := mp_ne_of_find_none (r0 := m7pVivifyFn)
      (by simp [m7PlusRepls, m7ParityVivTiersPatchFns]) hfind
    have hneVt : g.name ≠ "full_vivify_tier_m6_hdr" :=
      mp_ne_of_find_none (r0 := m7pVivifyTierFn)
        (by simp [m7PlusRepls, m7ParityVivTiersPatchFns]) hfind
    have hneCn : g.name ≠ "full_compact_needed" :=
      mp_ne_of_find_none (r0 := m7fixCompactNeededFn)
        (by simp [m7PlusRepls, m7PlusTailRepls]) hfind
    have hnePt : g.name ≠ "full_probe_tail_m6" := mp_ne_of_find_none (r0 := m7btProbeTailFn)
      (by simp [m7PlusRepls, m7PlusTailRepls, m7ParityBvaTiePatchFns]) hfind
    have hnePm : g.name ≠ "full_probe_m6" := mp_ne_of_find_none (r0 := m7btProbeFn)
      (by simp [m7PlusRepls, m7PlusTailRepls, m7ParityBvaTiePatchFns]) hfind
    by_cases h403 : g.name = "full_preprocess_m6"
    · refine Or.inl fun xs m Q X hrow => ?_
      have hgeq : g = m6oPreprocessM6Fn := fn_eq_of_mem_idx m7_names_nodup hg mp_idx_403 h403
      subst hgeq
      cases hrow with
      | base _ _ hb =>
        exact full_preprocess_m6_compact_wp m7PlusEnv rPropS15 rArSwp rLucky rCompNeed
          rCompact rScaleM5 rProbe xs m Q X
          (fullM6PreprocessSpec_monoX (m7PlusBase_elim_of_mem rPreM6Mem hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · by_cases h404 : g.name = "full_simplify_m6"
      · refine Or.inl fun xs m Q X hrow => ?_
        have hgeq : g = m6oSimplifyM6Fn := fn_eq_of_mem_idx m7_names_nodup hg mp_idx_404 h404
        subst hgeq
        cases hrow with
        | base _ _ hb =>
          exact full_simplify_m6_compact_wp m7PlusEnv rBt rProbe rElimM6 rCompNeed rCompact
            xs m Q X (fullM6SimplifySpec_monoX (m7PlusBase_elim_of_mem rSimpM6Mem hb))
        | extra he => exact False.elim (hnotExtra _ (by decide) he)
      · by_cases h405 : g.name = "full_search_m6"
        · refine Or.inl fun xs m Q X hrow => ?_
          have hgeq : g = ⟨"full_search_m6", [i64], [i64], FullM7.full_search_m6_body⟩ :=
            fn_eq_of_mem_idx m7_names_nodup hg mp_idx_405 h405
          subst hgeq
          cases hrow with
          | base _ _ hb =>
            exact hTailWp.1 xs m Q X
              (fullM6SearchSpec_monoX (m7PlusBase_elim_of_mem m7PlusBase_searchM6_mem hb))
          | extra he => exact False.elim (hnotExtra _ (by decide) he)
        · by_cases h406 : g.name = "kissat_solve_bytes_m6"
          · refine Or.inl fun xs m Q X hrow => ?_
            have hgeq : g = FullM6Orch.m6oSolveBytesM6Fn :=
              fn_eq_of_mem_idx m7_names_nodup hg mp_idx_406 h406
            subst hgeq
            cases hrow with
            | base _ _ hb =>
              exact hTailWp.2.1 xs m Q X (m7PlusSolveBytesSpec_monoX (m7PlusBase_elim_of_mem
                (m7PlusBase_tail_mem _ (m7PlusOrchTail_solve_mem m7PlusSolveBytesSpec).1) hb))
            | extra he => exact False.elim (hnotExtra _ (by decide) he)
          · by_cases h407 : g.name = "full_preprocess"
            · refine Or.inl fun xs m Q X hrow => ?_
              have hgeq : g = ⟨"full_preprocess", [i64], [i64], FullM6Orch.full_preprocess_body⟩ :=
                fn_eq_of_mem_idx m7_names_nodup hg mp_idx_407 h407
              subst hgeq
              cases hrow with
              | base _ _ hb =>
                exact hTailWp.2.2.1 xs m Q X (fullM6PreprocessSpec_monoX
                  (m7PlusBase_elim_of_mem m7PlusBase_preprocess_mem hb))
              | extra he => exact False.elim (hnotExtra _ (by decide) he)
            · by_cases h408 : g.name = "full_search"
              · refine Or.inl fun xs m Q X hrow => ?_
                have hgeq : g = ⟨"full_search", [i64], [i64], FullM6Orch.full_search_body⟩ :=
                  fn_eq_of_mem_idx m7_names_nodup hg mp_idx_408 h408
                subst hgeq
                cases hrow with
                | base _ _ hb =>
                  exact hTailWp.2.2.2.1 xs m Q X
                    (fullM6SearchSpec_monoX (m7PlusBase_elim_of_mem m7PlusBase_search_mem hb))
                | extra he => exact False.elim (hnotExtra _ (by decide) he)
              · by_cases h409 : g.name = "kissat_solve_bytes"
                · refine Or.inl fun xs m Q X hrow => ?_
                  have hgeq : g = FullM6Orch.m6oSolveBytesFn :=
                    fn_eq_of_mem_idx m7_names_nodup hg mp_idx_409 h409
                  subst hgeq
                  cases hrow with
                  | base _ _ hb =>
                    exact hTailWp.2.2.2.2 xs m Q X (m7PlusSolveBytesSpec_monoX
                      (m7PlusBase_elim_of_mem
                        (m7PlusBase_tail_mem _
                          (m7PlusOrchTail_solve_mem m7PlusSolveBytesSpec).2) hb))
                  | extra he => exact False.elim (hnotExtra _ (by decide) he)
                · have hok_g : mpOkName g.name = true := by
                    simp [mpOkName, mpBadNames, Ne.symm hneVt, Ne.symm hneViv, Ne.symm hneCn,
                      Ne.symm hnePt, Ne.symm hnePm, Ne.symm h403, Ne.symm h404, Ne.symm h405,
                      Ne.symm h406, Ne.symm h407, Ne.symm h408, Ne.symm h409]
                  by_cases hex : g.name ∈ mpExtraBaseRows.map SpecEntry.name
                  · refine Or.inl fun xs m Q X hrow => ?_
                    cases hrow with
                    | base _ _ hb =>
                      obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
                      have ⟨hwfG, hcallsG, hwpG⟩ := hbaseOk.fnsOk pre g post hsplit
                      have hnoBad : mpNoCallBad
                          (g.body (fun _ => Unit) (fun _ => Unit) (Tup.units g.as)) = true :=
                        List.all_eq_true.mp mp_all_nonbad_no_bad g
                          (List.mem_filter.mpr ⟨hg, hok_g⟩)
                      exact wp_env_agree_of_callsOk
                        (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
                        (mp_callsOk_filter _ hcallsG hnoBad)
                        (fun f as bs hmem' _ _ _ _ hc => by
                          have hfl := (List.mem_filter.mp hmem').2
                          exact M7PlusEnv.base
                            (fun heq => by subst heq; simp [mpOkName, mpBadNames] at hfl)
                            (fun heq => by subst heq; simp [mpOkName, mpBadNames] at hfl) hc)
                        m (hwpG xs m Q X hb)
                    | extra he =>
                      have hm_n := mp_ofTable_name_mem he
                      have hbase_mem : g.name ∈ mpExtraBaseRows.map SpecEntry.name := by
                        simpa [mpExtraRows, List.map_append, hneVt, hneCn] using hm_n
                      rcases List.mem_map.mp hbase_mem with ⟨r, hr, hnm⟩
                      rcases List.mem_iff_getElem.mp hr with ⟨idx, hidx, rfl⟩
                      have hlen_e : mpExtraBaseFns.length = mpExtraBaseRows.length := by
                        have hl := congrArg List.length mp_extraBaseFns_sigs
                        simpa only [List.length_map] using hl.symm
                      have hidx_f : idx < mpExtraBaseFns.length := hlen_e ▸ hidx
                      have hf_idx : mpExtraBaseFns[idx]'hidx_f ∈ mpExtraBaseFns :=
                        List.getElem_mem hidx_f
                      have hsig_eq : (mpExtraBaseRows[idx].name, mpExtraBaseRows[idx].as,
                          mpExtraBaseRows[idx].rs) = (mpExtraBaseFns[idx]'hidx_f).sig := by
                        have hopt := congrArg (fun l => l[idx]?) mp_extraBaseFns_sigs
                        rw [List.getElem?_map, List.getElem?_eq_getElem hidx, List.getElem?_map,
                          List.getElem?_eq_getElem hidx_f] at hopt
                        exact Option.some.inj hopt
                      have hfn_eq_name : (mpExtraBaseFns[idx]'hidx_f).name = g.name :=
                        (congrArg Prod.fst hsig_eq).symm.trans hnm
                      have hg_eq : g = mpExtraBaseFns[idx]'hidx_f := by
                        have hm1 := mp_extraBaseFns_sub _ hf_idx
                        rcases List.mem_iff_getElem.mp hg with ⟨i1, hi1, rfl⟩
                        rcases List.mem_iff_getElem.mp hm1 with ⟨i2, hi2, heq2⟩
                        have heq_idx : i1 = i2 := idx_eq_of_name_nodup m7_names_nodup
                          (List.getElem?_eq_getElem hi2) (List.getElem?_eq_getElem hi1)
                          (by rw [heq2]; exact hfn_eq_name.symm)
                        subst heq_idx
                        exact heq2
                      subst hg_eq
                      have hImpl_idx : SpecEntry.Impl m7PlusEnv (mpExtraBaseFns[idx]'hidx_f)
                          (mpExtraBaseRows[idx]'hidx) :=
                        mp_tableImpl_getElem idx hidx_f hidx hExtraImpl
                      have r_in_extra : mpExtraBaseRows[idx] ∈ mpExtraRows :=
                        List.mem_append_left _ (List.getElem_mem hidx)
                      rcases hImpl_idx with ⟨⟨hn, ha, hr_⟩, hwp⟩
                      exact hwp xs m Q X (mp_extra_elim_cast r_in_extra hn ha hr_ he)
                  · refine Or.inr fun xs m Q X hrow => ?_
                    cases hrow with
                    | base _ _ hb => exact ⟨hok_g, hb⟩
                    | extra he =>
                      have hni : g.name ∉ mpExtraRows.map SpecEntry.name := by
                        simpa [mpExtraRows, List.map_append, hneVt, hneCn] using hex
                      exact False.elim (hnotExtra _ hni he)
  · intro r hr xs m Q X hrow
    simp only [m7PlusRepls, m7ParityVivTiersPatchFns, m7PlusTailRepls, m7ParityBvaTiePatchFns,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with
      (rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
    · cases hrow with
      | base _ _ hb =>
        exact m6_hdr_sync_legacy_tiers_wp m7PlusEnv rEnsure xs m Q X
          (m6HdrW2aSpec_monoX (m7PlusBase_elim_of_mem hc1.hdrSyncLegacy hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_propagate_ignore_hot_wp m7PlusEnv rOvf rChrono xs m Q X
          (m7PlusBase_elim_of_mem hc1.propIgnoreHot hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_propagate_ignore_canon_hot_wp m7PlusEnv rOvf rChrono xs m Q X
          (m7PlusBase_elim_of_mem hc1.propagateIgn hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base hne _ _ => exact absurd rfl hne
      | extra he =>
        have hspec : m6aVivifyTierSpec xs m Q X :=
          m6aVivifyTierSpec_monoX (mp_extra_elim (List.mem_of_getElem? (i := 31) rfl) he)
        exact FullM7ParityVivTiers.full_vivify_tier_m6_hdr_wp m7PlusEnv rBt r20 r21 r22 r23 r18
          rPropS15 r24 xs m Q X hspec
    · cases hrow with
      | base _ _ hb =>
        exact FullM7ParityVivTiers.full_vivify_m6_hdr_wp m7PlusEnv rBt rSync rGetWm rVivTier
          xs m Q X (m6aVivifySpec_monoX (m7PlusBase_elim_of_mem hc2p.vivifyM6Hdr hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_bva_commit_m7_wp m7PlusEnv rWdEnv rInitFresh rAddBinCan rAllocCl rWpEnv
          rDelBin rUnw xs m Q X (m7PlusBase_elim_of_mem m7PlusBase_bvaCommit_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_analyze_rsn_m7_wp m7PlusEnv rAnaLit xs m Q X
          (m7PlusBase_elim_of_mem hc2gu.2 hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hne _ => exact absurd rfl hne
      | extra he =>
        have hspec : FullM4Compact.fullCompactNeededSpec xs m Q X :=
          mp_extra_elim (List.mem_of_getElem? (i := 32) rfl) he
        exact full_compact_needed_m7fix_wp m7PlusEnv xs m Q X hspec
    · cases hrow with
      | base _ _ hb =>
        exact full_compact_mark_live_m7fix_wp m7PlusEnv rNext xs m Q X
          (m7PlusBase_elim_of_mem m7PlusBase_compactMarkLive_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_compact_vars_m7fix_wp m7PlusEnv xs m Q X
          (m7PlusBase_elim_of_mem m7PlusBase_compactVars_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_sweep_copy_m7fix_wp m7PlusEnv rALvl rWpEnv xs m Q X
          (m7PlusBase_elim_of_mem m7PlusBase_sweepCopy_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_calc_max_v_m7v5_wp m7PlusEnv rFixedBytes xs m Q X
          (m7PlusBase_elim_of_mem m7PlusBase_calcMaxV_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact m7Plus_forward_sub_wp m7PlusEnv rDedup rFlushUnits rColSort rFlushLg rCheckCl
          rConnSub rNext rReconn xs m Q X
          (m7PlusBase_elim_of_mem (m7PlusBase_bve_mem _ m7PlusBveRows_specs.fwdSub) hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact m7PlusEliminate_wp m7PlusEnv rElimDticks rIlog rScaleD rEnterDense rMinU64
          rFwdSub rElimBve rFactor rRebuild xs m Q X
          (m7PlusBase_elim_of_mem (m7PlusBase_bve_mem _ m7PlusBveRows_specs.eliminateM6) hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_bva_pick_cand_bt_wp m7PlusEnv xs m Q X
          (m7PlusBase_elim_of_mem m7PlusBase_bvaPickCand_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_probe_tail_bt_wp m7PlusEnv rBackbone rTrans rMinU64 rProbeRun rVivM6
          xs m Q X (m6ProbeTailSpec_monoX (m7PlusBase_elim_of_mem rProbeTailMem hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ _ hb =>
        exact full_probe_bt_wp m7PlusEnv rDticks rIlog rScaleM5 rEnterDense rDelay rCongDense
          rRebuild rSetWm rRedD rBumpD rSwpDense rSubst rProbeTail rBackbone rMinU64 rFactor
          xs m Q X (FullM6Orch.m6ProbeSpec_monoX (m7PlusBase_elim_of_mem rProbeMem hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)

theorem m7Plus_solveBytes_mem : FullM6Orch.m6oSolveBytesFn ∈ m7PlusModule.fns := by
  unfold m7PlusModule m7PlusFns
  exact mpSpliceFns_mem_of_ne m7oSolveBytesFn_mem fun r hr => by
    simp only [m7PlusRepls, m7ParityVivTiersPatchFns, m7PlusTailRepls, m7ParityBvaTiePatchFns,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with
      (rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> decide

/-- Top-level UNSAT-only `kissat_solve_bytes` soundness theorem for `m7PlusModule` (`410` fns)
under closed `m7PlusEnv` (`0` hooks, zero SAT model proofs). -/
theorem m7Plus_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m7PlusEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7Plus_solveBytes_mem
  have hfn := (m7Plus_moduleOk.fnsOk pre _ post hsplit).2.2
  refine hfn _ m _ (fun _ _ _ _ => False)
    (m7PlusEnv_solve_bytes (m7PlusSolveBytesSpec_intro hcfit hwfit hm ?_))
  intro r m' hdom h20 _ hmem
  exact ⟨hdom, h20, hmem⟩

/-- Host-framed machine-memory UNSAT lift for `m7PlusModule` (`(Eq m' ⋆ F_host) st_dmem`). -/
theorem m7Plus_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem :=
  ⟨hq.1, hq.2.1, sep_mono (fun _ hm0 => by subst hm0; exact hq.2.2) hdmem⟩

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for
`m7PlusModule` on `8,192 B` `nvM6UnsatInitMem` (`0` SAT model proofs). -/
theorem m7Plus_unsat_nv :
    Func.wp m7PlusEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7Plus_solveBytes_mem
  have hfn := (m7Plus_moduleOk.fnsOk pre _ post hsplit).2.2
  have hm0 : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn _ _ _ (fun _ _ _ _ => False)
    (m7PlusEnv_solve_bytes (m7PlusSolveBytesSpec_intro (by decide) (by decide) hm0 ?_))
  intro r m' _ _ htr hm'
  have hr20 : r = 20#64 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound
    (by decide) nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

end LeanQbe.T.Examples.Kissat.FullM7Plus
