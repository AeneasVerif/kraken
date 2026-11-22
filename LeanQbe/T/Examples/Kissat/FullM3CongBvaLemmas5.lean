module

public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas4

/-!
# Kissat `D-Full` M3b Congruence & BVA/BVE Proofs — Part 5 (`#9`–`#11` Orchestrators)

Builds on `FullM3CongBvaLemmas4` to prove parametric `(Γ : Env)` `Func.wp` contracts for the
remaining orchestrators:
- `m3_fast_probe_tail_wp`: `FullFast.full_probe_tail_body` against `schedProbeTailSpec`
- **#9 (`full_probe`)**: `m3_probe_wp` (pure-3-CNF bypass removed, `m3CongruenceDenseSpec` +
  `fullSweepDenseSpec` + `fullRebuildWatchesSpec` + `schedProbeTailSpec`)
- **#10 (`full_eliminate`)**: `m3_eliminate_wp` (`fullForwardSubFastSpec`, `TmkZero` init,
  `m3ElimBveSpec`, zero-churn `elim_bound := 0` save/restore around `fullFactorHeapSpec`)
- **#11 (`full_preprocess`)**: `m3_preprocess_wp` (pure-3-CNF bypass removed).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM3CongBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open Kraken.Bedrock2.Test

section Orchestrators

open scoped FullArenaTactics M3HeadTactics

private theorem fullDenseInv_with_tmk {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {tmki : List (BitVec 32)}
    (htl : tmki.length = 2 * c.max_vars) :
    FullDenseInv c F0 { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fullDenseInv_with_tarjan_mark h htl

private theorem tmkZero_of_init_loop {s : FullState}
    {tmki : List (BitVec 32)} (hinit : ∀ k < s.core.cur_vars, tmki[k]?.getD 0#32 = 0#32) :
    TmkZero { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fun v hv => hinit v hv

/-- `Func.wp` proof for `FullFast.full_probe_tail_body` against `schedProbeTailSpec`. -/
theorem m3_fast_probe_tail_wp (Γ : Env)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunFastSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifyFastSpec a m Q X →
      Γ "full_vivify" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeTailSpec a m Q X →
      Func.wp Γ FullFast.full_probe_tail_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp FullFast.full_probe_tail_body
  c0_hsteps_nogrp
  -- Join after optional `full_transitive(h, dticks * 2 + 20000)`
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
      c0_hsteps; c0_call hMin; intro pbud _
      c0_hsteps_nogrp
      -- Join after optional `full_probe_run(h, pbud)`
      refine wp_join_state0 (α := FullState)
        (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
          c0_hsteps; c0_call hMin; intro v1 _
          c0_hsteps; c0_call hMin; intro v0 _
          c0_hsteps; c0_call hViv; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
          intro r3 s3 m3 hinv3 hcl3 _ _ hfu3 _ hu3 hm3
          have hcl3' := hcl3 hcl2
          c0_hsteps
          · exact hQ 20#64 s3 m3 hinv3 hcl3' (by omega) (Or.inr rfl) (fun _ => hu3 hc) hm3
          c0_call hViv; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
          intro r4 s4 m4 hinv4 hcl4 _ _ hfu4 _ hu4 hm4
          have hcl4' := hcl4 hcl3'
          c0_hsteps
          · exact hQ 20#64 s4 m4 hinv4 hcl4' (by omega) (Or.inr rfl) (fun _ => hu4 hc) hm4
          c0_call hViv; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
          intro r5 s5 m5 hinv5 hcl5 _ _ hfu5 _ hu5 hm5
          have hcl5' := hcl5 hcl4'
          c0_hsteps
          · exact hQ 20#64 s5 m5 hinv5 hcl5' (by omega) (Or.inr rfl) (fun _ => hu5 hc) hm5
          exact hQ 1#64 s5 m5 hinv5 hcl5' (by omega) (Or.inl rfl) (fun h => by cases h) hm5)
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hPRun; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
            intro rp s2 m2 hinv2 hcl2 _ _ hfu2 _ hup2 hm2
            have hcl2' := hcl2 hcl1
            c0_hsteps
            · exact hQ 20#64 s2 m2 hinv2 hcl2' (by omega) (Or.inr rfl) (fun _ => hup2 hc) hm2
            exact hJ2 s2 m2 ⟨hinv2, hcl2', by omega, hm2⟩
          · c0_hsteps; exact hJ2 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; c0_call hTrans; refine ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
        intro rt s1 m1 hinv1 hcl1 _ _ hfu1 _ hut1 hm1
        have hcl1' := hcl1 hcl0
        c0_hsteps
        · exact hQ 20#64 s1 m1 hinv1 hcl1' hfu1 (Or.inr rfl) (fun _ => hut1 hc) hm1
        exact hJ1 s1 m1 ⟨hinv1, hcl1', hfu1, hm1⟩
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

/-- **#9 (`full_probe`)**: removes the `num_binary < 4` dense bypass and runs
`m3CongruenceDenseSpec` + `fullSweepDenseSpec` + `fullRebuildWatchesSpec` +
`schedProbeTailSpec`. -/
theorem m3_probe_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedProbeDticksSpec a m Q X →
      Γ "full_probe_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hCong : ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense" [i64, i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, schedProbeTailSpec a m Q X →
      Γ "full_probe_tail" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m3ProbeSpec a m Q X → Func.wp Γ full_probe_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_body
  c0_hsteps; c0_call hDticks; refine ⟨c, s, R, rfl, hinv.lengths, hm, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  -- Join 1: after `if (!initial)` header-limit update
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, hcl0', hfu0, hm0⟩ => by
      c0_hsteps_nogrp
      -- Join 2: after first optional `full_substitute`
      refine wp_join_state0 (α := FullState)
        (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
          s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
        (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
          c0_hsteps_nogrp
          -- Join 3: `do_dense` boolean computation (`initial || num_binary * 3 >= num_irred`)
          refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
            (fun _ _ _ => by
              c0_hsteps_nogrp
              -- Join 4: after `if (do_dense)` dense congruence + sweeping block
              refine wp_join_state0 (α := FullState)
                (fun s5 m5 => FullSparseInv c F0 s5 ∧ s5.core.cur_level = 0 ∧
                  s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s5 ⋆ R) m5)
                (fun _ s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩ => by
                  c0_hsteps_nogrp
                  -- Join 5: after second optional `full_substitute`
                  refine wp_join_state0 (α := FullState)
                    (fun s6 m6 => FullSparseInv c F0 s6 ∧ s6.core.cur_level = 0 ∧
                      s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s6 ⋆ R) m6)
                    (fun _ s6 m6 ⟨hinv6, hcl6, hfu6, hm6⟩ => by
                      c0_hsteps_nogrp
                      -- Join 6: after `if (!initial && full_probe_tail(h, dticks) == 20ULL)`
                      refine wp_join_state0 (α := FullState)
                        (fun s7 m7 => FullSparseInv c F0 s7 ∧ s7.core.cur_level = 0 ∧
                          s7.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s7 ⋆ R) m7)
                        (fun _ s7 m7 ⟨hinv7, hcl7, hfu7, hm7⟩ => by
                          c0_hsteps
                          let s8 : FullState :=
                            { s7 with scratch := { s7.scratch with
                              fwd_sub_cnt := s7.scratch.search_ticks } }
                          have hinv8 : FullSparseInv c F0 s8 :=
                            fullSparseInv_with_scratch_keep hinv7 { hinv7.lengths.scratch_ok with }
                              rfl rfl
                          exact hQ 1#64 s8 _ hinv8.lengths hfu7 (Or.inl rfl) (fun h => by cases h)
                            (fun _ => ⟨hinv8, hcl7⟩) hm)
                        (fun J6 hJ6 => by
                          c0_hsplit
                          · c0_hsteps; exact hJ6 s6 m6 ⟨hinv6, hcl6, hfu6, hm6⟩
                          · c0_hsteps; c0_call hTail
                            refine ⟨c, F0, s6, R, rfl, hinv6, hcl6, hm6, ?_⟩
                            intro rt s7 m7 hinv7 hcl7 hfu7 _ hut7 hm7; c0_hsteps
                            · exact hQ 20#64 s7 m7 hinv7.lengths (by omega) (Or.inr rfl)
                                (fun _ => hut7 hc) (fun h => by cases h) hm7
                            exact hJ6 s7 m7 ⟨hinv7, hcl7, by omega, hm7⟩))
                    (fun J5 hJ5 => by
                      c0_hsplit
                      · c0_hsteps; c0_call hSubst; refine ⟨c, F0, s5, R, rfl, hinv5, hm5, ?_⟩
                        intro rs s6 m6 hinv6 hcl6 hfu6 _ hus6 hm6; c0_hsteps
                        · exact hQ 20#64 s6 m6 hinv6.lengths (by omega) (Or.inr rfl)
                            (fun _ => hus6 hc) (fun h => by cases h) hm6
                        exact hJ5 s6 m6 ⟨hinv6, hcl6, by omega, hm6⟩
                      · c0_hsteps; exact hJ5 s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩))
                (fun J4 hJ4 => by
                  c0_hsplit
                  · c0_hsteps; c0_call hEnter; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
                    intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2; c0_hsplit
                    · have hden2 : FullDenseInv c F0 s2 := hok_d hc
                      c0_hsteps; c0_call hMin; intro sweep_bud _
                      c0_hsteps; c0_call hCong; refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
                      intro rc s3 m3 hden3 _ hfu3 _ hu3 hm3
                      have hfu3' : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hfu3]; exact Nat.le_trans hfu2 hfu1
                      c0_hsteps
                      · c0_call hReb; refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                        intro _ s3' m3' hsp3' _ hfu3_s _ _ hm3'; c0_hsteps
                        exact hQ 20#64 s3' m3' hsp3'.lengths (by omega) (Or.inr rfl)
                          (fun _ => hu3 hc) (fun h => by cases h) hm3'
                      · c0_call hSweep; refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                        intro rsw s4 m4 hden4 _ hfu4 _ hu4 hm4
                        have hfu4' : s4.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
                        c0_hsteps
                        · c0_call hReb; refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                          intro _ s4' m4' hsp4' _ hfu4_s _ _ hm4'; c0_hsteps
                          exact hQ 20#64 s4' m4' hsp4'.lengths (by omega) (Or.inr rfl)
                            (fun _ => hu4 hc) (fun h => by cases h) hm4'
                        · c0_call hReb; refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                          intro rr s5 m5 hsp5 hcl5 hfu5 _ hu5 hm5; c0_hsteps
                          · exact hQ 20#64 s5 m5 hsp5.lengths (by omega) (Or.inr rfl)
                              (fun _ => hu5 hc) (fun h => by cases h) hm5
                          exact hJ4 s5 m5 ⟨hsp5, hcl5, by omega, hm5⟩
                    · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
                      c0_hsteps
                      · exact hQ 20#64 s2 m2 hsp2.lengths (by omega) (Or.inr rfl)
                          (fun _ => hsp2.inconsistent_unsat hc) (fun h => by cases h) hm2
                      · exact hJ4 s2 m2 ⟨hsp2, hcl2, by omega, hm2⟩
                  · c0_hsteps; exact hJ4 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
            (fun Jd hJd => by c0_hsteps <;> exact hJd _ trivial))
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hSubst; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
            intro rs1 s1 m1 hinv1 hcl1 hfu1 _ hus1 hm1; c0_hsteps
            · exact hQ 20#64 s1 m1 hinv1.lengths (by omega) (Or.inr rfl)
                (fun _ => hus1 hc) (fun h => by cases h) hm1
            exact hJ2 s1 m1 ⟨hinv1, hcl1, by omega, hm1⟩
          · c0_hsteps; exact hJ2 s0 m0 ⟨hinv0, hcl0', hfu0, hm0⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩
      · c0_hsteps
        let s0a : FullState :=
          { s with scratch := { s.scratch with probings := s.scratch.probings + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv.lengths.core_ok, { hinv.lengths.scratch_ok with }⟩
        c0_call hIlog; intro logp _ _
        c0_hsteps; c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
        intro delta
        c0_hsteps
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with probe_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          fullSparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

/-- **#10 (`full_eliminate`)**: uses `fullForwardSubFastSpec`, zeroes `tarjan_mark[0..cv)`
to establish `TmkZero`, calls `m3ElimBveSpec`, and saves/clears `elim_bound := 0`/restores
around `fullFactorHeapSpec`. -/
theorem m3_eliminate_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X → Γ "full_elim_bve" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorHeapSpec a m Q X → Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, m3EliminateSpec a m Q X → Func.wp Γ full_eliminate_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_eliminate_body
  c0_hsteps; c0_call hDticks; refine ⟨c, s, R, rfl, hinv.lengths, hm, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  -- Join 1: after `if (!initial)` limit/bound update
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, _, hfu0, hm0⟩ => by
      c0_hsteps; c0_call hEnter; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
      intro ok s1 m1 hcl1 hfu1 hok_d hfail_s hm1
      c0_hsplit
      · have hden1 : FullDenseInv c F0 s1 := hok_d hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ fbud _ => by
            c0_hsteps; c0_call hMin; intro _ _
            c0_hsteps; c0_call hFwd; refine ⟨c, F0, s1, R, rfl, hden1, hm1, ?_⟩
            intro fs s2 m2 hden2 _ hfu2 _ huf2 hm2
            let s2r : FullState :=
              { s2 with scratch := { s2.scratch with fwd_sub_cnt := s1.scratch.fwd_sub_cnt } }
            have hden2r : FullDenseInv c F0 s2r :=
              fullDenseInv_with_scratch_keep hden2 { hden2.lengths.scratch_ok with } rfl rfl
            have hfu2r : s2r.core.fuel.toNat ≤ s.core.fuel.toNat := by
              change s2.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfu2]; omega
            c0_hsplit
            · c0_hsteps; c0_call hReb; refine ⟨c, F0, s2r, R, rfl, hden2r, hm, ?_⟩
              intro _ s3 m3 hsp3 hcl3 hfu3 _ _ hm3; c0_hsteps
              exact hQ 20#64 s3 m3 hsp3 hcl3 (by omega) (Or.inr rfl) (fun _ => huf2 hc) hm3
            · let cv2 := s2r.core.cur_vars
              have hcv2_le : cv2 ≤ c.max_vars := hden2r.lengths.core_ok.cur_vars_le
              have hmx := c.hmaxv; unfold dimacsBound at hmx
              have hcv2_64 : cv2 < 2 ^ 64 := by omega
              have htl2 := hden2r.lengths.scratch_ok.tarjan_mark_len
              m3_steps
              refine wp_loop_inv
                (fun (ti, ()) mt => ∃ tmki : List (BitVec 32),
                  tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv2 ∧
                  (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                  (FullMem c { s2r with scratch :=
                    { s2r.scratch with tarjan_mark := tmki } } ⋆ R) mt)
                (fun (ti, ()) _ => cv2 - ti.toNat)
                (fun Jt hJt => by
                  m3_steps; exact hJt (0#64, ()) m
                    ⟨s2r.scratch.tarjan_mark, htl2, Nat.zero_le _, fun _ h => by simp at h, hm⟩)
                (fun Jt (ti, ()) mt ⟨tmki, htli, hti_le, hinit, hmt⟩ iht => ?_)
              m3_split_fast
              · have hti_lt : ti.toNat < cv2 := by
                  have hlt := bv64_ult_lt hc
                  change ti.toNat < (BitVec.ofNat 64 cv2).toNat at hlt
                  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv2_64] at hlt
                have hti_arr : ti.toNat < tmki.length := by omega
                have hti1 : (ti + 1#64).toNat = ti.toNat + 1 :=
                  bv64_add1_toNat (n := cv2) hti_lt hcv2_64
                m3_steps
                exact iht (ti + 1#64, ()) m (by dsimp only; omega)
                  ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega,
                   fun k hk => by
                     rw [hti1] at hk
                     by_cases hkt : k = ti.toNat
                     · subst hkt; rw [List.getElem?_set_self (by omega), Option.getD_some]
                     · rw [List.getElem?_set_ne (Ne.symm hkt)]; exact hinit k (by omega),
                   hm⟩
              · have hti_eq : ti.toNat = cv2 := by
                  have hnot := bv64_ult_not_lt hc
                  change ¬ ti.toNat < (BitVec.ofNat 64 cv2).toNat at hnot
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv2_64] at hnot
                  omega
                rw [hti_eq] at hinit
                let s2t : FullState :=
                  { s2r with scratch := { s2r.scratch with tarjan_mark := tmki } }
                have hden2t : FullDenseInv c F0 s2t := fullDenseInv_with_tmk hden2r htli
                have htmk2 : TmkZero s2t := tmkZero_of_init_loop hinit
                have hfu2t : s2t.core.fuel.toNat ≤ s.core.fuel.toNat := hfu2r
                clear hc
                c0_hsteps_nogrp
                refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                  (fun b => (b, ())) (fun _ => True)
                  (fun _ bve_lim _ => by
                    c0_hsteps; c0_call hBve; refine ⟨c, F0, s2t, R, rfl, hden2t, htmk2, hmt, ?_⟩
                    intro res s3 m3 hden3 _ hfu3 hres_dom hres_u hm3
                    c0_hsteps_nogrp
                    -- Join after optional zero-churn `full_factor`
                    refine wp_join_state0 (α := FullState)
                      (fun sf mf => FullDenseInv c F0 sf ∧
                        sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf)
                      (fun _ sf mf ⟨hdenf, hfuf, hmf⟩ => by
                        c0_hsteps; c0_call hReb; refine ⟨c, F0, sf, R, rfl, hdenf, hmf, ?_⟩
                        intro rr se me hspe hcle hfue _ hue hme
                        let se' : FullState :=
                          { se with scratch :=
                            { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                        have hspe' : FullSparseInv c F0 se' :=
                          fullSparseInv_with_scratch_keep hspe
                            { hspe.lengths.scratch_ok with } rfl rfl
                        have hfue' : se'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                          change se.core.fuel.toNat ≤ s.core.fuel.toNat; omega
                        c0_hsteps
                        · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                            (fun _ => hres_u hc) hm
                        · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                            (fun _ => hue hc) hm
                        · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                            (fun _ => hspe'.inconsistent_unsat hc) hm
                        · exact hQ 1#64 se' _ hspe' hcle hfue' (Or.inl rfl)
                            (fun h => by cases h) hm)
                      (fun Jf hJf => by
                        c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_join_state0 (α := FullState)
                            (fun sg mg => FullDenseInv c F0 sg ∧
                              sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sg ⋆ R) mg)
                            (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                              c0_hsteps_nogrp
                              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                                (fun b => (b, ())) (fun _ => True)
                                (fun _ _ _ => by
                                  c0_hsteps; c0_call hMin; intro fact_bud _
                                  c0_hsteps
                                  let sg0 : FullState :=
                                    { sg with scratch :=
                                      { sg.scratch with elim_bound := 0#64 } }
                                  have hdeng0 : FullDenseInv c F0 sg0 :=
                                    fullDenseInv_with_scratch_keep hdeng
                                      { hdeng.lengths.scratch_ok with } rfl rfl
                                  c0_call hFact; refine ⟨c, F0, sg0, R, rfl, hdeng0, hm, ?_⟩
                                  intro _ sf0 mf0 hdenf0 _ hfuf0 _ hmf0
                                  c0_hsteps
                                  let sf : FullState :=
                                    { sf0 with scratch :=
                                      { sf0.scratch with elim_bound := sg.scratch.elim_bound } }
                                  have hdenf : FullDenseInv c F0 sf :=
                                    fullDenseInv_with_scratch_keep hdenf0
                                      { hdenf0.lengths.scratch_ok with } rfl rfl
                                  exact hJf sf _ ⟨hdenf, by
                                    change sf0.core.fuel.toNat ≤ s.core.fuel.toNat
                                    rw [hfuf0]; exact hfug, hm⟩)
                                (fun Jfb hJfb => by c0_hsteps <;> exact hJfb _ trivial))
                            (fun Jdo hJdo => by
                              c0_hsteps
                              · exact hJdo s3 m3 ⟨hden3, by omega, hm3⟩
                              · exact hJdo s3 m3 ⟨hden3, by omega, hm3⟩
                              · exact hJf s3 m3 ⟨hden3, by omega, hm3⟩)
                        · c0_hsteps; exact hJf s3 m3 ⟨hden3, by omega, hm3⟩))
                  (fun Jb hJb => by
                    c0_hsteps
                    · exact hJb _ trivial
                    · c0_call hMin; intro b _; exact hJb b trivial))
          (fun Jfb hJfb => by c0_hsteps <;> exact hJfb _ trivial)
      · have hsp1 : FullSparseInv c F0 s1 := hfail_s hc
        let s1' : FullState :=
          { s1 with scratch := { s1.scratch with fwd_str_cnt := s1.scratch.search_ticks } }
        have hsp1' : FullSparseInv c F0 s1' :=
          fullSparseInv_with_scratch_keep hsp1 { hsp1.lengths.scratch_ok with } rfl rfl
        have hfu1' : s1'.core.fuel.toNat ≤ s.core.fuel.toNat := by
          change s1.core.fuel.toNat ≤ s.core.fuel.toNat; omega
        c0_hsteps
        · exact hQ 20#64 s1' _ hsp1' hcl1 hfu1' (Or.inr rfl)
            (fun _ => hsp1'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s1' _ hsp1' hcl1 hfu1' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩
      · c0_hsteps
        let s0a : FullState :=
          { s with scratch := { s.scratch with eliminations := s.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv.lengths.core_ok, { hinv.lengths.scratch_ok with }⟩
        c0_call hIlog; intro loge _ _
        c0_hsteps; c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
        intro delta
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          fullSparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        let s0c : FullState :=
          { s0b with scratch :=
            { s0b.scratch with elim_bound := s0b.scratch.elim_bound + 2#64 } }
        have hinv0c : FullSparseInv c F0 s0c :=
          fullSparseInv_with_scratch_keep hinv0b { hinv0b.lengths.scratch_ok with } rfl rfl
        c0_hsteps
        · exact hJ1 s0c _ ⟨hinv0c, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

/-- **#11 (`full_preprocess`)**: pure-3-CNF (`num_binary == 0`) bypass removed; always runs
`full_probe(h, true)` and `full_eliminate(h, true)` against canonical `Full.fullPreprocessSpec`. -/
theorem m3_preprocess_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, m3ProbeSpec a m Q X → Γ "full_probe" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, m3EliminateSpec a m Q X →
      Γ "full_eliminate" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, m3PreprocessSpec a m Q X → Func.wp Γ full_preprocess_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  obtain ⟨F_cur, hspW⟩ := hinv.exists_witness
  unfold Func.wp full_preprocess_body
  c0_hsteps; c0_call hProp
  refine ⟨c, F0, F_cur, s, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hm, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s1
    hlen1 hw1 _ hperm1 hfu1 _ _ hpr1 _ _ hm1
  have hspW1 : FullSparseInvW c F0 F_cur s1 :=
    ⟨hlen1, hw1, ⟨fun v hv => hspW.2.2.1.1 v hv, fun l hl => hspW.2.2.1.2 l hl⟩,
     fun ref href hng => by
       have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm1.2.1 ▸ href
       obtain ⟨_, hgb, hp⟩ := hperm1.2.2 ref href0
       exact (hp.map (· / 2)).nodup_iff.mpr (hspW.2.2.2.1 ref href0 (hgb.symm.trans hng)),
     hspW.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun ref href => by
       change ref ∈ fullArenaClauseRefsCore s1.core; rw [hperm1.2.1]; exact href,
     hspW.2.2.2.2.2⟩
  have hcl1 : s1.core.cur_level = 0 := hcl0
  c0_hsplit
  · c0_hsteps
    exact hQ 20#64 s1 m1 hlen1 (Or.inr (Or.inr (Or.inr rfl))) hfu1
      (fun _ => level0_unsat_of_conflict_okW (s := s1) hw1 hcl1 (hpr1 hc).2.2)
      (fun h => by cases h) (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  -- Join after `if (h->unflushed > 0ULL)`
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
      c0_hsplit
      · c0_hsteps
        exact hQ 10#64 s2 m2 hinv2.lengths (Or.inr (Or.inr (Or.inl rfl))) hfu2
          (fun h => by cases h) (fun h => by cases h) (fun _ => hinv2.2.2.2.1.2) hm2
      c0_hsteps; c0_call hScale; refine ⟨c, s2, R, rfl, hinv2.lengths, hm2, ?_⟩
      intro plim
      c0_hsteps
      let s2a : FullState := { s2 with scratch := { s2.scratch with probe_limit := plim } }
      have hinv2a : FullSparseInv c F0 s2a :=
        fullSparseInv_with_scratch_keep hinv2 { hinv2.lengths.scratch_ok with } rfl rfl
      c0_call hScale; refine ⟨c, s2a, R, rfl, hinv2a.lengths, hm, ?_⟩
      intro elim
      c0_hsteps
      let s2b : FullState := { s2a with scratch := { s2a.scratch with elim_limit := elim } }
      have hinv2b : FullSparseInv c F0 s2b :=
        fullSparseInv_with_scratch_keep hinv2a { hinv2a.lengths.scratch_ok with } rfl rfl
      have hfu2b : s2b.core.fuel.toNat ≤ s.core.fuel.toNat := hfu2
      c0_call hProbe; refine ⟨c, F0, s2b, R, rfl, hinv2b, hcl2, hm, ?_⟩
      intro rp s3 m3 hlen3 hfu3 hrp_dom hup3 hsp3 hm3
      have hfu3' : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
      c0_hsteps
      · exact hQ 20#64 s3 m3 hlen3 (Or.inr (Or.inr (Or.inr rfl))) hfu3'
          (fun _ => hup3 hc) (fun h => by cases h) (fun h => by cases h) hm3
      · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) hfu3' (fun h => by cases h)
          (fun h => by cases h) (fun h => by cases h) hm3
      · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) hfu3' (fun h => by cases h)
          (fun h => by cases h) (fun h => by cases h) hm3
      obtain ⟨hinv3, hcl3⟩ := hsp3 (hrp_dom.resolve_right (by assumption))
      c0_call hElim; refine ⟨c, F0, s3, R, rfl, hinv3, hcl3, hm3, ?_⟩
      intro re s4 m4 hinv4 hcl4 hfu4 _ hue4 hm4
      have hfu4' : s4.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
      c0_hsteps
      · exact hQ 20#64 s4 m4 hinv4.lengths (Or.inr (Or.inr (Or.inr rfl))) hfu4'
          (fun _ => hue4 hc) (fun h => by cases h) (fun h => by cases h) hm4
      · exact hQ 20#64 s4 m4 hinv4.lengths (Or.inr (Or.inr (Or.inr rfl))) hfu4'
          (fun _ => hinv4.inconsistent_unsat hc) (fun h => by cases h) (fun h => by cases h) hm4
      · exact hQ 0#64 s4 m4 hinv4.lengths (Or.inl rfl) hfu4' (fun h => by cases h)
          (fun h => by cases h) (fun h => by cases h) hm4
      · exact hQ 10#64 s4 m4 hinv4.lengths (Or.inr (Or.inr (Or.inl rfl))) hfu4'
          (fun h => by cases h) (fun h => by cases h) (fun _ => hinv4.2.2.2.1.2) hm4
      c0_call hScale; refine ⟨c, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
      intro plim2
      c0_hsteps
      let s4a : FullState := { s4 with scratch := { s4.scratch with probe_limit := plim2 } }
      have hinv4a : FullSparseInv c F0 s4a :=
        fullSparseInv_with_scratch_keep hinv4 { hinv4.lengths.scratch_ok with } rfl rfl
      c0_call hScale; refine ⟨c, s4a, R, rfl, hinv4a.lengths, hm, ?_⟩
      intro elim2
      c0_hsteps
      let s4b : FullState := { s4a with scratch := { s4a.scratch with elim_limit := elim2 } }
      have hinv4b : FullSparseInv c F0 s4b :=
        fullSparseInv_with_scratch_keep hinv4a { hinv4a.lengths.scratch_ok with } rfl rfl
      exact hQ 1#64 s4b _ hinv4b.lengths (Or.inr (Or.inl rfl)) hfu4'
        (fun h => by cases h) (fun _ => ⟨hinv4b, hcl4⟩) (fun h => by cases h) hm)
    (fun Ju hJu => by
      c0_hsplit
      · c0_hsteps; c0_call hSweep
        refine ⟨c, F0, F_cur, s1, R, rfl, hspW1.1, hspW1.2.1, hspW1.2.2.2.1, hspW1.2.2.2.2.2,
          fun hpos => by omega, hm1, ?_⟩
        intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc1a m1a s1a
          hlen1a _ hext1a _ hll1a hw1a hnd1a _ _ _ hsr2 _ hm1a
        have hspW1a : FullSparseInvW c F0 F_cur s1a :=
          ⟨hlen1a, hw1a, hspW1.2.2.1, hnd1a,
           ⟨hll1a, hext1a.symm ▸ hspW1.2.2.2.2.1.2⟩, hspW1.2.2.2.2.2⟩
        have hcl1a : s1a.core.cur_level = 0 := hcl1
        c0_hsteps
        · exact hQ 20#64 s1a m1a hlen1a (Or.inr (Or.inr (Or.inr rfl))) hfu1
            (fun _ => (hsr2 hc).2) (fun h => by cases h) (fun h => by cases h) hm1a
        c0_call hProp
        refine ⟨c, F0, F_cur, s1a, R, rfl, hspW1a.1, hspW1a.2.1, hspW1a.2.2.2.2.2, hm1a, ?_⟩
        intro pr1b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel1b _ _ _ _ _ _ _ _ m1b s1b
          hlen1b hw1b _ hperm1b hfl1b _ _ hpr1b_1 _ _ hm1b
        have hspW1b : FullSparseInvW c F0 F_cur s1b :=
          ⟨hlen1b, hw1b, hspW1a.2.2.1,
           fun ref href hng => by
             have href0 : ref ∈ fullArenaClauseRefsCore s1a.core := hperm1b.2.1 ▸ href
             obtain ⟨_, hgb, hp⟩ := hperm1b.2.2 ref href0
             exact (hp.map (· / 2)).nodup_iff.mpr (hspW1a.2.2.2.1 ref href0 (hgb.symm.trans hng)),
           hspW1a.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun ref href => by
             change ref ∈ fullArenaClauseRefsCore s1b.core; rw [hperm1b.2.1]; exact href,
           hspW1a.2.2.2.2.2⟩
        have hfu1b : s1b.core.fuel.toNat ≤ s.core.fuel.toNat := by
          have h1 : s1a.core.fuel.toNat ≤ s.core.fuel.toNat := hfu1
          dsimp only [s1b]; omega
        c0_hsteps
        · exact hQ 20#64 s1b m1b hlen1b (Or.inr (Or.inr (Or.inr rfl))) hfu1b
            (fun _ => level0_unsat_of_conflict_okW (s := s1b) hw1b hcl1a (hpr1b_1 hc).2.2)
            (fun h => by cases h) (fun h => by cases h) hm1b
        have hspW1c : FullSparseInvW c F0 F_cur
            { s1b with core := { s1b.core with unflushed := 0#64 } } :=
          ⟨⟨{ hspW1b.1.core_ok with }, hspW1b.1.scratch_ok⟩,
           { hspW1b.2.1 with
             arena := { hspW1b.2.1.arena with len_ok := hspW1b.2.1.arena.len_ok }
             watches := hspW1b.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
           hspW1b.2.2.1, hspW1b.2.2.2.1, hspW1b.2.2.2.2.1, hspW1b.2.2.2.2.2⟩
        exact hJu _ _ ⟨hspW1c.toSparse, hcl1a, hfu1b, hm⟩
      · c0_hsteps; exact hJu s1 m1 ⟨hspW1.toSparse, hcl1, hfu1, hm1⟩)

end Orchestrators

end LeanQbe.T.Examples.Kissat.FullM3CongBva
