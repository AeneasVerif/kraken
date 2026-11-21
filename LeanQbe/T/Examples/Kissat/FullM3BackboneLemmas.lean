module

public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullProof
public import LeanQbe.T.Examples.Kissat.FullDeduce1UipNv
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M3c Backbone & Wrap-Around `probe_run` Hub, `ModuleOk`, & Non-Vacuity (`Part 2`)

Re-exports `FullM3BackboneLemmas1` (`m3_probe_run_cursor_wp`, `m3_probe_run_wp`,
`m3_probe_run_fast_wp`, `m3_backbone_lit_entails_wp`, `m3_backbone_lit_wp`, `m3_backbone_wp`) and
completes:
1. **`Func.wp` proofs for the M3c orchestrators**:
   - `m3_probe_tail_wp` (`FullFastSched.schedProbeTailSpec`)
   - `m3_probe_wp` (`FullFastSched.schedProbeSpec`)
   - `m3_probe_full_wp` (`Full.fullProbeSpec` for `FullProbeFull.full_probe_body`)
2. **Closed `20`-row `m3BackboneLocalEnv` & `m3BackboneLocal_moduleOk`** covering all `5` M3c
   functions in `m3BackboneLocalModule`.
3. **Unconditional `168/168` closed-module `ModuleOk` for `m3BackboneFullModule`**
   (`externs := []`, `exits := []`):
   - `mkM3BackboneFullEnv_moduleOk`, `m3BackboneFullEnv_moduleOk`, `m3BackboneFullUnsatEnv_moduleOk`
   - `m3BackboneFull_solve_bytes_correct`: end-to-end `kissat_solve_bytes` UNSAT soundness
   - `m3BackboneFull_unsat_nonvacuous`: concrete `4096`-byte `Mem 64` `kissat_solve_bytes` UNSAT
     non-vacuity (`fullNvUnsatBytes` → `20#64 ∧ fullNvUnsatCnf.Unsat`, `XPost := False`).
4. **Per-function concrete `Mem 64` UNSAT non-vacuity (`XPost := False`)** for `full_probe_run`,
   `full_backbone_lit` (explicit unit-entailment contract), `full_backbone`, `full_probe_tail`,
   `full_probe`, and `FullProbeFull.full_probe`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3Backbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open Kraken.Bedrock2.Test

/-! ## 1. M2 Dense Congruence / Sweep Extern Contracts & Orchestrator `Func.wp` Proofs (`3` fns) -/

section Orchestrators

/-- Dense-mode congruence extern contract (`full_congruence_dense(h, tick_lim)` in `FullFast`). -/
def m3CongruenceDenseSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Dense-mode sweeping extern contract (`full_sweep_dense(h, budget, tick_lim)` in `FullFast`). -/
def m3SweepDenseSpec : Spec [i64, i64, i64] [i64] := fun (h, _budget, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem m3_sparse_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

open scoped FullArenaTactics

/-- `Func.wp` proof for M3c `full_probe_tail(h, dticks)` against `schedProbeTailSpec`. -/
theorem m3_probe_tail_wp (Γ : Env)
    (hBone : ∀ a m Q X, fullBackboneSpec a m Q X →
      Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifyFastSpec a m Q X →
      Γ "full_vivify" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeTailSpec a m Q X → Func.wp Γ full_probe_tail_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_tail_body
  c0_hsteps_nogrp
  -- Join 1: after optional `full_backbone`
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      -- Join 2: after optional `full_transitive`
      refine wp_join_state0 (α := FullState)
        (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
          c0_hsteps; c0_call hMin; intro pbud _
          c0_hsteps_nogrp
          -- Join 3: after optional `full_probe_run`
          refine wp_join_state0 (α := FullState)
            (fun s3 m3 => FullSparseInv c F0 s3 ∧ s3.core.cur_level = 0 ∧
              s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s3 ⋆ R) m3)
            (fun _ s3 m3 ⟨hinv3, hcl3, hfu3, hm3⟩ => by
              c0_hsteps; c0_call hMin; intro v1 _
              c0_hsteps; c0_call hMin; intro v0 _
              c0_hsteps; c0_call hViv; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
              intro r4 s4 m4 hinv4 hcl4 _ _ hfu4 _ hu4 hm4
              have hcl4' := hcl4 hcl3
              c0_hsteps
              · exact hQ 20#64 s4 m4 hinv4 hcl4' (by omega) (Or.inr rfl) (fun _ => hu4 hc) hm4
              c0_call hViv; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
              intro r5 s5 m5 hinv5 hcl5 _ _ hfu5 _ hu5 hm5
              have hcl5' := hcl5 hcl4'
              c0_hsteps
              · exact hQ 20#64 s5 m5 hinv5 hcl5' (by omega) (Or.inr rfl) (fun _ => hu5 hc) hm5
              c0_call hViv; refine ⟨c, F0, s5, R, rfl, hinv5, hm5, ?_⟩
              intro r6 s6 m6 hinv6 hcl6 _ _ hfu6 _ hu6 hm6
              have hcl6' := hcl6 hcl5'
              c0_hsteps
              · exact hQ 20#64 s6 m6 hinv6 hcl6' (by omega) (Or.inr rfl) (fun _ => hu6 hc) hm6
              exact hQ 1#64 s6 m6 hinv6 hcl6' (by omega) (Or.inl rfl) (fun h => by cases h) hm6)
            (fun J3 hJ3 => by
              c0_hsplit
              · c0_hsteps; c0_call hPRun; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
                intro rp s3 m3 hinv3 hcl3 _ hfu3 _ hup3 _ hm3; c0_hsteps
                · exact hQ 20#64 s3 m3 hinv3 hcl3 (by omega) (Or.inr rfl) (fun _ => hup3 hc) hm3
                exact hJ3 s3 m3 ⟨hinv3, hcl3, by omega, hm3⟩
              · c0_hsteps; exact hJ3 s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩))
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hTrans; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
            intro rt s2 m2 hinv2 hcl2 _ _ hfu2 _ hut2 hm2
            have hcl2' := hcl2 hcl1
            c0_hsteps
            · exact hQ 20#64 s2 m2 hinv2 hcl2' (by omega) (Or.inr rfl) (fun _ => hut2 hc) hm2
            exact hJ2 s2 m2 ⟨hinv2, hcl2', by omega, hm2⟩
          · c0_hsteps; exact hJ2 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; c0_call hBone; refine ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
        intro rb s1 m1 hinv1 hcl1 _ hfu1 _ hub1 hm1; c0_hsteps
        · exact hQ 20#64 s1 m1 hinv1 hcl1 hfu1 (Or.inr rfl) (fun _ => hub1 hc) hm1
        exact hJ1 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

/-- `Func.wp` proof for M3c `full_probe(h, initial)` against `schedProbeSpec`. -/
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
    (hCongD : ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hSweepD : ∀ a m Q X, m3SweepDenseSpec a m Q X →
      Γ "full_sweep_dense" [i64, i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, fullBackboneSpec a m Q X →
      Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, schedProbeTailSpec a m Q X →
      Γ "full_probe_tail" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeSpec a m Q X → Func.wp Γ full_probe_body a m Q X := by
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
          -- Join 3: `do_dense` boolean computation
          refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
            (fun _ _ _ => by
              c0_hsteps_nogrp
              -- Join 4: after `if (do_dense)` dense congruence + sweeping block
              refine wp_join_state0 (α := FullState)
                (fun s4 m4 => FullSparseInv c F0 s4 ∧ s4.core.cur_level = 0 ∧
                  s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s4 ⋆ R) m4)
                (fun _ s4 m4 ⟨hinv4, hcl4, hfu4, hm4⟩ => by
                  c0_hsteps_nogrp
                  -- Join 5: after second optional `full_substitute`
                  refine wp_join_state0 (α := FullState)
                    (fun s5 m5 => FullSparseInv c F0 s5 ∧ s5.core.cur_level = 0 ∧
                      s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s5 ⋆ R) m5)
                    (fun _ s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩ => by
                      c0_hsteps_nogrp
                      -- Join 6: after `if (initial) { ... } else { full_probe_tail ... }`
                      refine wp_join_state0 (α := FullState)
                        (fun s6 m6 => FullSparseInv c F0 s6 ∧ s6.core.cur_level = 0 ∧
                          s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s6 ⋆ R) m6)
                        (fun _ s6 m6 ⟨hinv6, hcl6, hfu6, hm6⟩ => by
                          c0_hsteps
                          let s7 : FullState :=
                            { s6 with scratch := { s6.scratch with
                              fwd_sub_cnt := s6.scratch.search_ticks } }
                          have hinv7 : FullSparseInv c F0 s7 :=
                            m3_sparse_with_scratch_keep hinv6 { hinv6.lengths.scratch_ok with }
                              rfl rfl
                          exact hQ 1#64 s7 _ hinv7.lengths hfu6 (Or.inl rfl) (fun h => by cases h)
                            (fun _ => ⟨hinv7, hcl6⟩) hm)
                        (fun J6 hJ6 => by
                          c0_hsplit
                          · -- `initial == true`: backbone → transitive → probe_run
                            c0_hsteps_nogrp
                            refine wp_join_state0 (α := FullState)
                              (fun sa ma => FullSparseInv c F0 sa ∧ sa.core.cur_level = 0 ∧
                                sa.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sa ⋆ R) ma)
                              (fun _ sa ma ⟨hinva, hcla, hfua, hma⟩ => by
                                c0_hsteps_nogrp
                                refine wp_join_state0 (α := FullState)
                                  (fun sb mb => FullSparseInv c F0 sb ∧ sb.core.cur_level = 0 ∧
                                    sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sb ⋆ R) mb)
                                  (fun _ sb mb ⟨hinvb, hclb, hfub, hmb⟩ => by
                                    c0_hsteps; c0_call hMin; intro pbud0 _
                                    c0_hsteps_nogrp; c0_hsplit
                                    · c0_hsteps; c0_call hPRun
                                      refine ⟨c, F0, sb, R, rfl, hinvb, hmb, ?_⟩
                                      intro rp sc mc hinvc hclc _ hfuc _ hupc _ hmc; c0_hsteps
                                      · exact hQ 20#64 sc mc hinvc.lengths (by omega) (Or.inr rfl)
                                          (fun _ => hupc hc) (fun h => by cases h) hmc
                                      exact hJ6 sc mc ⟨hinvc, hclc, by omega, hmc⟩
                                    · c0_hsteps; exact hJ6 sb mb ⟨hinvb, hclb, hfub, hmb⟩)
                                  (fun Jb hJb => by
                                    c0_hsplit
                                    · c0_hsteps; c0_call hTrans
                                      refine ⟨c, F0, sa, R, rfl, hinva, hma, ?_⟩
                                      intro rt sb mb hinvb hclb _ _ hfub _ hutb hmb
                                      have hclb' := hclb hcla
                                      c0_hsteps
                                      · exact hQ 20#64 sb mb hinvb.lengths (by omega) (Or.inr rfl)
                                          (fun _ => hutb hc) (fun h => by cases h) hmb
                                      exact hJb sb mb ⟨hinvb, hclb', by omega, hmb⟩
                                    · c0_hsteps; exact hJb sa ma ⟨hinva, hcla, hfua, hma⟩))
                              (fun Ja hJa => by
                                c0_hsplit
                                · c0_hsteps; c0_call hBone
                                  refine ⟨c, F0, s5, R, rfl, hinv5, hm5, ?_⟩
                                  intro rb sa ma hinva hcla _ hfua _ huba hma; c0_hsteps
                                  · exact hQ 20#64 sa ma hinva.lengths (by omega) (Or.inr rfl)
                                      (fun _ => huba hc) (fun h => by cases h) hma
                                  exact hJa sa ma ⟨hinva, hcla, by omega, hma⟩
                                · c0_hsteps; exact hJa s5 m5 ⟨hinv5, hcl5, hfu5, hm5⟩)
                          · -- `initial == false`: `full_probe_tail`
                            c0_hsteps; c0_call hTail
                            refine ⟨c, F0, s5, R, rfl, hinv5, hcl5, hm5, ?_⟩
                            intro rt s6 m6 hinv6 hcl6 hfu6 _ hut6 hm6; c0_hsteps
                            · exact hQ 20#64 s6 m6 hinv6.lengths (by omega) (Or.inr rfl)
                                (fun _ => hut6 hc) (fun h => by cases h) hm6
                            exact hJ6 s6 m6 ⟨hinv6, hcl6, by omega, hm6⟩))
                    (fun J5 hJ5 => by
                      c0_hsplit
                      · c0_hsteps; c0_call hSubst; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
                        intro rs s5 m5 hinv5 hcl5 hfu5 _ hus5 hm5; c0_hsteps
                        · exact hQ 20#64 s5 m5 hinv5.lengths (by omega) (Or.inr rfl)
                            (fun _ => hus5 hc) (fun h => by cases h) hm5
                        exact hJ5 s5 m5 ⟨hinv5, hcl5, by omega, hm5⟩
                      · c0_hsteps; exact hJ5 s4 m4 ⟨hinv4, hcl4, hfu4, hm4⟩))
                (fun J4 hJ4 => by
                  c0_hsplit
                  · -- `do_dense == true`: dense congruence + sweeping + rebuild
                    c0_hsteps; c0_call hEnter; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
                    intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
                    c0_hsplit
                    · have hden2 : FullDenseInv c F0 s2 := hok_d hc
                      c0_hsteps; c0_call hMin; intro sbud _
                      c0_hsteps; c0_call hCongD; refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
                      intro rc s3 m3 hden3 hfu3 _ huc3 hm3
                      c0_hsplit
                      · c0_hsteps; c0_call hReb; refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                        intro _ s3r m3r hsp3r _ hfu3r _ _ hm3r; c0_hsteps
                        exact hQ 20#64 s3r m3r hsp3r.lengths (by omega) (Or.inr rfl)
                          (fun _ => huc3 hc) (fun h => by cases h) hm3r
                      · c0_hsteps; c0_call hSweepD; refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                        intro rw4 s4 m4 hden4 hfu4 _ huw4 hm4
                        c0_hsplit
                        · c0_hsteps; c0_call hReb; refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                          intro _ s4r m4r hsp4r _ hfu4r _ _ hm4r; c0_hsteps
                          exact hQ 20#64 s4r m4r hsp4r.lengths (by omega) (Or.inr rfl)
                            (fun _ => huw4 hc) (fun h => by cases h) hm4r
                        · c0_hsteps; c0_call hReb; refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                          intro rrb s4r m4r hsp4r hcl4r hfu4r _ hurb hm4r; c0_hsteps
                          · exact hQ 20#64 s4r m4r hsp4r.lengths (by omega) (Or.inr rfl)
                              (fun _ => hurb hc) (fun h => by cases h) hm4r
                          exact hJ4 s4r m4r ⟨hsp4r, hcl4r, by omega, hm4r⟩
                    · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
                      c0_hsteps
                      · exact hQ 20#64 s2 m2 hsp2.lengths (by omega) (Or.inr rfl)
                          (fun _ => hsp2.inconsistent_unsat hc) (fun h => by cases h) hm2
                      exact hJ4 s2 m2 ⟨hsp2, hcl2, by omega, hm2⟩
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
          m3_sparse_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

/-- `Func.wp` proof for 1-arg `FullProbeFull.full_probe_body` against canonical
`Full.fullProbeSpec` (inserts `full_backbone(h, 200000ULL)` ahead of `full_transitive`). -/
theorem m3_probe_full_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hCong : ∀ a m Q X, fullCongruenceSpec a m Q X → Γ "full_congruence" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullSweepSatSpec a m Q X → Γ "full_sweep_sat" [i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, fullBackboneSpec a m Q X → Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveSpec a m Q X → Γ "full_transitive" [i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunSpec a m Q X → Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifySpec a m Q X → Γ "full_vivify" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullProbeSpec a m Q X → Func.wp Γ FullProbeFull.full_probe_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, _, hm, hQ⟩
  unfold Func.wp FullProbeFull.full_probe_body; c0_hsteps
  c0_call hIsqrt; intro r_sq _ _ _; c0_hsteps
  let s0 : FullState :=
    { s with
      scratch := { s.scratch with
        probings := s.scratch.probings + 1#64
        probe_limit := s.scratch.conflicts + 500#64 * r_sq } }
  have hinv0 : FullSparseInv c F0 s0 :=
    m3_sparse_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
  have hfu0 : s0.core.fuel = s.core.fuel := rfl
  c0_call hSubst; refine ⟨c, F0, s0, R, rfl, hinv0, hm, ?_⟩
  intro r1 s1 m1 hsp1 _ hfu1 _ hu1 hm1; rw [hfu0] at hfu1; c0_hsteps
  · exact hQ 20#64 s1 m1 hsp1.lengths hfu1 (Or.inr rfl) (fun _ => hu1 hc) (fun h => by cases h) hm1
  c0_call hCong; refine ⟨c, F0, s1, R, rfl, hsp1, hm1, ?_⟩
  intro r2 s2 m2 hfu2 hr2 hsp2 h20_2 hm2; c0_hsteps
  · obtain ⟨hu2, hlen2⟩ := h20_2 hc
    exact hQ 20#64 s2 m2 hlen2 (Nat.le_trans hfu2 hfu1) (Or.inr rfl) (fun _ => hu2)
      (fun h => by cases h) hm2
  have hinv2 : FullSparseInv c F0 s2 := hsp2 (hr2.resolve_right hc)
  c0_call hSubst; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
  intro r3 s3 m3 hsp3 _ hfu3 _ hu3 hm3; c0_hsteps
  · exact hQ 20#64 s3 m3 hsp3.lengths (by omega) (Or.inr rfl) (fun _ => hu3 hc)
      (fun h => by cases h) hm3
  c0_call hSweep; refine ⟨c, F0, s3, R, rfl, hsp3, hm3, ?_⟩
  intro r4 s4 m4 hsp4 _ hfu4 _ hu4 hm4; c0_hsteps
  · exact hQ 20#64 s4 m4 hsp4.lengths (by omega) (Or.inr rfl) (fun _ => hu4 hc)
      (fun h => by cases h) hm4
  c0_call hBone; refine ⟨c, F0, s4, R, rfl, hsp4, hm4, ?_⟩
  intro rb sb mb hspb _ _ hfub _ hub hmb; c0_hsteps
  · exact hQ 20#64 sb mb hspb.lengths (by omega) (Or.inr rfl) (fun _ => hub hc)
      (fun h => by cases h) hmb
  c0_call hTrans; refine ⟨c, F0, sb, R, rfl, hspb, hmb, ?_⟩
  intro r5 s5 m5 hsp5 _ _ hfu5 _ hu5 hm5; c0_hsteps
  · exact hQ 20#64 s5 m5 hsp5.lengths (by omega) (Or.inr rfl) (fun _ => hu5 hc)
      (fun h => by cases h) hm5
  c0_call hPRun; refine ⟨c, F0, s5, R, rfl, hsp5, hm5, ?_⟩
  intro r6 s6 m6 hsp6 _ _ hfu6 _ hu6 hm6; c0_hsteps
  · exact hQ 20#64 s6 m6 hsp6.lengths (by omega) (Or.inr rfl) (fun _ => hu6 hc)
      (fun h => by cases h) hm6
  c0_call hViv; refine ⟨c, F0, s6, R, rfl, hsp6, hm6, ?_⟩
  intro r7 s7 m7 hsp7 _ _ hfu7 _ hu7 hm7; c0_hsteps
  · exact hQ 20#64 s7 m7 hsp7.lengths (by omega) (Or.inr rfl) (fun _ => hu7 hc)
      (fun h => by cases h) hm7
  c0_call hViv; refine ⟨c, F0, s7, R, rfl, hsp7, hm7, ?_⟩
  intro r8 s8 m8 hsp8 _ _ hfu8 _ hu8 hm8; c0_hsteps
  · exact hQ 20#64 s8 m8 hsp8.lengths (by omega) (Or.inr rfl) (fun _ => hu8 hc)
      (fun h => by cases h) hm8
  c0_call hViv; refine ⟨c, F0, s8, R, rfl, hsp8, hm8, ?_⟩
  intro r9 s9 m9 hsp9 hcl9 _ hfu9 _ hu9 hm9; c0_hsteps
  · exact hQ 20#64 s9 m9 hsp9.lengths (by omega) (Or.inr rfl) (fun _ => hu9 hc)
      (fun h => by cases h) hm9
  exact hQ 1#64 s9 m9 hsp9.lengths (by omega) (Or.inl rfl) (fun h => by cases h)
    (fun _ => ⟨hsp9, hcl9⟩) hm9

end Orchestrators

/-! ## 2. Closed `20`-Row Local Module `ModuleOk` (`m3BackboneLocalModule`) -/

section LocalModuleOk

/-- `20`-row specification table (`5` M3c functions + `15` externs, all `noExit = true`). -/
def m3BackboneLocalSpecTable : List SpecEntry :=
  [ ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunCursorSpec, true⟩
  , ⟨"full_backbone_lit", [i64, i32], [i64], fullBackboneLitSpec, true⟩
  , ⟨"full_backbone", [i64, i64], [i64], fullBackboneSpec, true⟩
  , ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
  , ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  , ⟨"full_probe_assume_pair", [i64, i32], [i64], fullProbeAssumePairSpec, true⟩
  , ⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩
  , ⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩
  , ⟨"full_sweep_dense", [i64, i64, i64], [i64], m3SweepDenseSpec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩ ]

theorem m3BackboneLocalSpecTable_nodup :
    (m3BackboneLocalSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m3BackboneLocalSpecTable_noExit :
    ∀ e ∈ m3BackboneLocalSpecTable, e.noExit = true := by
  intro e he
  have hall : m3BackboneLocalSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

/-- Closed environment for the standalone `5`-function M3c compilation unit. -/
def m3BackboneLocalEnv : Env := Env.ofTable m3BackboneLocalSpecTable

theorem m3BackboneLocalEnv_noExit :
    ∀ f as bs xs m Q X X',
      m3BackboneLocalEnv f as bs xs m Q X → m3BackboneLocalEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m3BackboneLocalSpecTable_noExit

private theorem localEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m3BackboneLocalSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m3BackboneLocalEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m3BackboneLocalSpecTable_nodup
      (hno xs m Q X hs)

theorem m3_probe_run_local_impl :
    SpecEntry.Impl m3BackboneLocalEnv
      ⟨"full_probe_run", [i64, i64], [i64], full_probe_run_body⟩
      ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunCursorSpec, true⟩ :=
  SpecEntry.Impl.of (m3_probe_run_cursor_wp m3BackboneLocalEnv
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h)))

theorem m3_backbone_lit_local_impl :
    SpecEntry.Impl m3BackboneLocalEnv
      ⟨"full_backbone_lit", [i64, i32], [i64], full_backbone_lit_body⟩
      ⟨"full_backbone_lit", [i64, i32], [i64], fullBackboneLitSpec, true⟩ :=
  SpecEntry.Impl.of (m3_backbone_lit_wp m3BackboneLocalEnv
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h)))

theorem m3_backbone_local_impl :
    SpecEntry.Impl m3BackboneLocalEnv
      ⟨"full_backbone", [i64, i64], [i64], full_backbone_body⟩
      ⟨"full_backbone", [i64, i64], [i64], fullBackboneSpec, true⟩ :=
  SpecEntry.Impl.of (m3_backbone_wp m3BackboneLocalEnv
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h)))

theorem m3_probe_tail_local_impl :
    SpecEntry.Impl m3BackboneLocalEnv
      ⟨"full_probe_tail", [i64, i64], [i64], full_probe_tail_body⟩
      ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩ :=
  SpecEntry.Impl.of (m3_probe_tail_wp m3BackboneLocalEnv
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h)))

theorem m3_probe_local_impl :
    SpecEntry.Impl m3BackboneLocalEnv
      ⟨"full_probe", [i64, .bool], [i64], full_probe_body⟩
      ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩ :=
  SpecEntry.Impl.of (m3_probe_wp m3BackboneLocalEnv
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h))
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h)))

theorem m3BackboneLocal_allFns_wf : AllFns Fn.Wf m3BackboneLocalModule.fns :=
  ⟨full_probe_run_wf, full_backbone_lit_wf, full_backbone_wf,
    full_probe_tail_wf, full_probe_wf, trivial⟩

theorem m3BackboneLocal_tableImpl :
    TableImpl m3BackboneLocalEnv m3BackboneLocalModule.fns m3BackboneLocalSpecTable :=
  ⟨m3_probe_run_local_impl, m3_backbone_lit_local_impl, m3_backbone_local_impl,
    m3_probe_tail_local_impl, m3_probe_local_impl, trivial⟩

/-- Headline `ModuleOk` certifying all `5` M3c functions in `m3BackboneLocalModule`. -/
theorem m3BackboneLocal_moduleOk : ModuleOk m3BackboneLocalEnv m3BackboneLocalModule :=
  Env.ofTable_moduleOk m3BackboneLocal_acyclic m3BackboneLocal_allFns_wf m3BackboneLocal_tableImpl

end LocalModuleOk

/-! ## 3. Unconditional `168/168` Closed-Module `ModuleOk` (`m3BackboneFullModule`) -/

section ClosedFullModuleOk

/-- `168`-row specification table matching `m3BackboneFullFns` row-by-row:
every original `Full.fullSpecTable mainSpec` row is preserved verbatim, with `full_backbone_lit`
and `full_backbone` inserted at indices `114..115`. -/
def m3BackboneFullSpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  let base := fullSpecTable mainSpec
  base.take 114 ++
  [ ⟨"full_backbone_lit", [i64, i32], [i64], fullBackboneLitSpec, true⟩
  , ⟨"full_backbone", [i64, i64], [i64], fullBackboneSpec, true⟩ ] ++
  base.drop 114

def mkM3BackboneFullEnv (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (m3BackboneFullSpecTable mainSpec)

/-- Closed `168`-function environment for `m3BackboneFullModule` (`fullSolveBytesSpec`). -/
def m3BackboneFullEnv : Env := mkM3BackboneFullEnv fullSolveBytesSpec

/-- Closed `168`-function environment for concrete UNSAT non-vacuity (`fullUnsatWitnessSpec`). -/
def m3BackboneFullUnsatEnv : Env := mkM3BackboneFullEnv fullUnsatWitnessSpec

theorem m3BackboneFullSpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ m3BackboneFullSpecTable mainSpec, e.noExit = true := by
  intro e he
  have hall : (m3BackboneFullSpecTable mainSpec).all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m3BackboneFullSpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3BackboneFullSpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) =
      m3BackboneFullFns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

private theorem m3BackboneFullFns_nodup : (m3BackboneFullFns.map Fn.name).Nodup := by
  have hchk := m3BackboneFull_acyclic
  simp only [m3BackboneFullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem m3BackboneFullSpecTable_nodup
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m3BackboneFullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (m3BackboneFullSpecTable mainSpec).map SpecEntry.name =
      m3BackboneFullFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (m3BackboneFullSpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]; exact m3BackboneFullFns_nodup

theorem mkM3BackboneFullEnv_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkM3BackboneFullEnv mainSpec f as bs xs m Q X →
      mkM3BackboneFullEnv mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (m3BackboneFullSpecTable_noExit mainSpec)

theorem m3BackboneFullEnv_noExit :
    ∀ f as bs xs m Q X X',
      m3BackboneFullEnv f as bs xs m Q X → m3BackboneFullEnv f as bs xs m Q X' :=
  mkM3BackboneFullEnv_noExit fullSolveBytesSpec

theorem m3BackboneFullUnsatEnv_noExit :
    ∀ f as bs xs m Q X X',
      m3BackboneFullUnsatEnv f as bs xs m Q X → m3BackboneFullUnsatEnv f as bs xs m Q X' :=
  mkM3BackboneFullEnv_noExit fullUnsatWitnessSpec

private theorem mkM3BackboneFullEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m3BackboneFullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM3BackboneFullEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (m3BackboneFullSpecTable_nodup mainSpec)
      (hno xs m Q X h)

private theorem env_ofTable_sub {tbl₁ tbl₂ : List SpecEntry}
    (hsub : ∀ e ∈ tbl₁, e ∈ tbl₂) (hnd₂ : (tbl₂.map SpecEntry.name).Nodup) :
    ∀ f as bs xs m Q X, Env.ofTable tbl₁ f as bs xs m Q X → Env.ofTable tbl₂ f as bs xs m Q X := by
  induction tbl₁ with
  | nil => intro _ _ _ _ _ _ _ h; exact h.elim
  | cons e es ih =>
    intro f as bs xs m Q X h
    rcases h with ⟨⟨rfl, rfl, rfl⟩, he⟩ | ⟨_, hes⟩
    · exact Env.ofTable_of_mem (hsub e List.mem_cons_self) hnd₂ he
    · exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) f as bs xs m Q X hes

private theorem mkFullEnv_le_mkM3BackboneFullEnv
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X,
      mkFullEnv mainSpec f as bs xs m Q X → mkM3BackboneFullEnv mainSpec f as bs xs m Q X := by
  refine env_ofTable_sub ?_ (m3BackboneFullSpecTable_nodup mainSpec)
  intro e he
  have hsp : e ∈ (fullSpecTable mainSpec).take 114 ++ (fullSpecTable mainSpec).drop 114 := by
    rwa [List.take_append_drop]
  simp only [m3BackboneFullSpecTable, List.mem_append] at hsp ⊢
  rcases hsp with h1 | h2
  · exact Or.inl (Or.inl h1)
  · exact Or.inr h2

private theorem specEntry_impl_env_mono {Γ₁ Γ₂ : Env} {fn : Fn} {e : SpecEntry}
    (hΓ : ∀ f as bs xs m P E, Γ₁ f as bs xs m P E → Γ₂ f as bs xs m P E)
    (h : SpecEntry.Impl Γ₁ fn e) : SpecEntry.Impl Γ₂ fn e :=
  let ⟨hsig, hwp⟩ := h
  ⟨hsig, fun xs m Q X hs => wp_env_mono hΓ _ m (hwp xs m Q X hs)⟩

private theorem tableImpl_env_mono {Γ₁ Γ₂ : Env}
    (hΓ : ∀ f as bs xs m P E, Γ₁ f as bs xs m P E → Γ₂ f as bs xs m P E) :
    ∀ {fs : List Fn} {es : List SpecEntry}, TableImpl Γ₁ fs es → TableImpl Γ₂ fs es
  | [], _, _ => trivial
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨specEntry_impl_env_mono hΓ h1, tableImpl_env_mono hΓ h2⟩

private theorem tableImpl_append {Γ : Env} :
    ∀ {fs₁ fs₂ : List Fn} {es₁ es₂ : List SpecEntry},
      fs₁.length = es₁.length →
      TableImpl Γ fs₁ es₁ → TableImpl Γ fs₂ es₂ →
      TableImpl Γ (fs₁ ++ fs₂) (es₁ ++ es₂)
  | [], _, [], _, _, _, h2 => h2
  | _ :: _, _, [], _, hlen, _, _ => by simp at hlen
  | [], _, _ :: _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _, _ :: _, _, hlen, ⟨ha, hb⟩, h2 =>
      ⟨ha, tableImpl_append (Nat.succ.inj hlen) hb h2⟩

private theorem tableImpl_take {Γ : Env} :
    ∀ (n : Nat) {fs : List Fn} {es : List SpecEntry},
      TableImpl Γ fs es → TableImpl Γ (fs.take n) (es.take n)
  | 0, _, _, _ => trivial
  | _ + 1, [], _, _ => trivial
  | _ + 1, _ :: _, [], h => h.elim
  | n + 1, _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h1, tableImpl_take n h2⟩

private theorem tableImpl_drop {Γ : Env} :
    ∀ (n : Nat) {fs : List Fn} {es : List SpecEntry},
      TableImpl Γ fs es → TableImpl Γ (fs.drop n) (es.drop n)
  | 0, _, _, h => h
  | _ + 1, [], _, _ => trivial
  | _ + 1, _ :: _, [], h => h.elim
  | n + 1, _ :: _, _ :: _, ⟨_, h2⟩ => tableImpl_drop n h2

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

/-- Unconditional `168/168` row-by-row `TableImpl` for `m3BackboneFullFns` against
`m3BackboneFullSpecTable mainSpec`, transferring all `164` unchanged rows directly from
`Full.mkFullEnv_tableImpl` via `wp_env_mono` and discharging the `4` M3c rows (`full_probe_run`,
`full_backbone_lit`, `full_backbone`, `FullProbeFull.full_probe`). -/
theorem mkM3BackboneFullEnv_tableImpl
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkM3BackboneFullEnv mainSpec) m3BackboneFullFns
      (m3BackboneFullSpecTable mainSpec) := by
  let Γ := mkM3BackboneFullEnv mainSpec
  have hbase : TableImpl Γ Full.fullFns (fullSpecTable mainSpec) :=
    tableImpl_env_mono (mkFullEnv_le_mkM3BackboneFullEnv mainSpec)
      (mkFullEnv_tableImpl mainSpec hweaken)
  have hlen_f : Full.fullFns.length = 166 := by t_kernel_rfl
  have hlen_e : (fullSpecTable mainSpec).length = 166 := by
    have h := congrArg List.length (fullSpecTable_sigs mainSpec)
    simpa only [List.length_map, hlen_f] using h
  -- Rewrite `m3BackboneFullSpecTable` to match the `7`-segment split of `m3BackboneFullFns`
  have heq_tbl : m3BackboneFullSpecTable mainSpec =
      (fullSpecTable mainSpec).take 111 ++
      ((fullSpecTable mainSpec).drop 111).take 1 ++
      ((fullSpecTable mainSpec).drop 112).take 2 ++
      [ ⟨"full_backbone_lit", [i64, i32], [i64], fullBackboneLitSpec, true⟩
      , ⟨"full_backbone", [i64, i64], [i64], fullBackboneSpec, true⟩ ] ++
      ((fullSpecTable mainSpec).drop 114).take 46 ++
      ((fullSpecTable mainSpec).drop 160).take 1 ++
      (fullSpecTable mainSpec).drop 161 := by
    have h1 : (fullSpecTable mainSpec).take 114 =
        (fullSpecTable mainSpec).take 111 ++
        ((fullSpecTable mainSpec).drop 111).take 1 ++
        ((fullSpecTable mainSpec).drop 112).take 2 := by
      have ha := List.take_add (l := fullSpecTable mainSpec) (i := 111) (j := 3)
      have hb := List.take_add (l := (fullSpecTable mainSpec).drop 111) (i := 1) (j := 2)
      rw [List.drop_drop] at hb
      simpa only [List.append_assoc] using ha.trans (congrArg _ hb)
    have h2 : (fullSpecTable mainSpec).drop 114 =
        ((fullSpecTable mainSpec).drop 114).take 46 ++
        ((fullSpecTable mainSpec).drop 160).take 1 ++
        (fullSpecTable mainSpec).drop 161 := by
      have ha := (List.take_append_drop 46 ((fullSpecTable mainSpec).drop 114)).symm
      have hb := (List.take_append_drop 1 ((fullSpecTable mainSpec).drop 160)).symm
      rw [List.drop_drop] at ha hb
      simpa only [List.append_assoc] using ha.trans (congrArg _ hb)
    unfold m3BackboneFullSpecTable; dsimp only
    conv => lhs; rw [h1, h2]
    simp only [List.append_assoc]
  have hrow111 : ((fullSpecTable mainSpec).drop 111).take 1 =
      [⟨"full_probe_run", [i64, i64], [i64], fullProbeRunSpec, true⟩] := rfl
  have hrow160 : ((fullSpecTable mainSpec).drop 160).take 1 =
      [⟨"full_probe", [i64], [i64], fullProbeSpec, true⟩] := rfl
  have hfn111 : m3Backbone_fns.take 1 =
      [⟨"full_probe_run", [i64, i64], [i64], full_probe_run_body⟩] := rfl
  have hfn114 : (m3Backbone_fns.drop 1).take 2 =
      [ ⟨"full_backbone_lit", [i64, i32], [i64], full_backbone_lit_body⟩
      , ⟨"full_backbone", [i64, i64], [i64], full_backbone_body⟩ ] := rfl
  have hfn160 : FullProbeFull.fullProbeM3_fns =
      [⟨"full_probe", [i64], [i64], FullProbeFull.full_probe_body⟩] := rfl
  -- Prove the 4 M3c rows under `Γ`
  have h_bt := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  have h_prop := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  have h_au := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 102
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  have h_ap := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 110
    ⟨"full_probe_assume_pair", [i64, i32], [i64], fullProbeAssumePairSpec, true⟩
  have h_prun := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 111
    ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunSpec, true⟩
  have h_trans := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 113
    ⟨"full_transitive", [i64], [i64], fullTransitiveSpec, true⟩
  have h_blit := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 114
    ⟨"full_backbone_lit", [i64, i32], [i64], fullBackboneLitSpec, true⟩
  have h_bone := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 115
    ⟨"full_backbone", [i64, i64], [i64], fullBackboneSpec, true⟩
  have h_isqrt := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 8
    ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  have h_viv := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 121
    ⟨"full_vivify", [i64, i64], [i64], fullVivifySpec, true⟩
  have h_subst := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 127
    ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  have h_cong := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 139
    ⟨"full_congruence", [i64], [i64], fullCongruenceSpec, true⟩
  have h_sweep := mkM3BackboneFullEnv_row_at (mainSpec := mainSpec) 146
    ⟨"full_sweep_sat", [i64], [i64], fullSweepSatSpec, true⟩
  have himpl_prun : TableImpl Γ (m3Backbone_fns.take 1)
      (((fullSpecTable mainSpec).drop 111).take 1) := by
    rw [hfn111, hrow111]
    exact ⟨SpecEntry.Impl.of (m3_probe_run_wp Γ h_bt h_ap), trivial⟩
  have himpl_bone : TableImpl Γ ((m3Backbone_fns.drop 1).take 2)
      [ ⟨"full_backbone_lit", [i64, i32], [i64], fullBackboneLitSpec, true⟩
      , ⟨"full_backbone", [i64, i64], [i64], fullBackboneSpec, true⟩ ] := by
    rw [hfn114]
    exact ⟨SpecEntry.Impl.of (m3_backbone_lit_wp Γ h_au),
      SpecEntry.Impl.of (m3_backbone_wp Γ h_bt h_prop h_blit), trivial⟩
  have himpl_probe : TableImpl Γ FullProbeFull.fullProbeM3_fns
      (((fullSpecTable mainSpec).drop 160).take 1) := by
    rw [hfn160, hrow160]
    exact ⟨SpecEntry.Impl.of (m3_probe_full_wp Γ
      h_isqrt h_subst h_cong h_sweep h_bone h_trans h_prun h_viv), trivial⟩
  have hm3len : m3Backbone_fns.length = 5 := by t_kernel_rfl
  have hm3full : FullProbeFull.fullProbeM3_fns.length = 1 := by t_kernel_rfl
  -- Assemble all 7 segments cleanly
  rw [heq_tbl]; unfold m3BackboneFullFns
  refine tableImpl_append ?_ (tableImpl_append ?_ (tableImpl_append ?_ (tableImpl_append ?_
    (tableImpl_append ?_ (tableImpl_append ?_
      (tableImpl_take 111 hbase) himpl_prun)
      (tableImpl_take 2 (tableImpl_drop 112 hbase)))
      himpl_bone)
      (tableImpl_take 46 (tableImpl_drop 114 hbase)))
      himpl_probe)
    (tableImpl_drop 161 hbase)
  · simp [hlen_f, hlen_e, hm3len, hm3full]
  · simp [hlen_f, hlen_e, hm3len]
  · simp [hlen_f, hlen_e, hm3len]
  · simp [hlen_f, hlen_e, hm3len]
  · simp [hlen_f, hlen_e, hm3len]
  · simp [hlen_f, hlen_e]

/-- Unconditional `168/168` `ModuleOk` for `m3BackboneFullModule` under `mkM3BackboneFullEnv`. -/
theorem mkM3BackboneFullEnv_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ModuleOk (mkM3BackboneFullEnv mainSpec) m3BackboneFullModule :=
  Env.ofTable_moduleOk m3BackboneFull_acyclic (allFns_of_forall m3BackboneFullFns_wf)
    (mkM3BackboneFullEnv_tableImpl mainSpec hweaken)

/-- Unconditional `168/168` `ModuleOk` for closed `m3BackboneFullModule` (`externs := []`). -/
theorem m3BackboneFullEnv_moduleOk : ModuleOk m3BackboneFullEnv m3BackboneFullModule :=
  mkM3BackboneFullEnv_moduleOk fullSolveBytesSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec)

/-- Unconditional `168/168` `ModuleOk` for concrete UNSAT non-vacuity environment
`m3BackboneFullUnsatEnv`. -/
theorem m3BackboneFullUnsatEnv_moduleOk : ModuleOk m3BackboneFullUnsatEnv m3BackboneFullModule :=
  mkM3BackboneFullEnv_moduleOk fullUnsatWitnessSpec
    (fun _ _ _ _ => fullSolveBytesCoreSpec_of_unsatWitness)

/-- Headline source-level UNSAT soundness of `kissat_solve_bytes` under the closed `168`-function
M3c environment `m3BackboneFullEnv`. -/
theorem m3BackboneFull_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m3BackboneFullEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  wp_env_mono (mkFullEnv_le_mkM3BackboneFullEnv fullSolveBytesSpec) _ m
    (full_solve_bytes_correct hcfit hwfit hm)

/-- Closed `168`-function concrete `Mem 64` UNSAT non-vacuity (`XPost := False`):
`kissat_solve_bytes` returns `20#64` and proves `fullNvUnsatCnf.Unsat` on `fullNvUnsatBytes`
(`4096`-byte work buffer, `fuel = 16`). -/
theorem m3BackboneFull_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m3BackboneFullUnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun rs _ => rs = (20#64, ()) ∧ fullNvUnsatCnf.Unsat) (fun _ _ _ _ => False) :=
  wp_env_mono (mkFullEnv_le_mkM3BackboneFullEnv fullUnsatWitnessSpec) _ _ full_unsat_nonvacuous

end ClosedFullModuleOk

/-! ## 4. Per-Function Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section PerFnNonVacuity

private theorem m3Nv_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact WatchSliceOk.empty
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact hent0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · have : fullArenaClauseRefs nvOneLitState = [] := rfl; simp [this] at hr

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for wrap-around `full_probe_run`. -/
theorem nv_m3_probe_run :
    Func.wp m3BackboneLocalEnv full_probe_run_body
      (nvOneLitCfg.hdr, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.probing = 0#64 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_probe_run_local_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, m3Nv_sparseW.toSparse, hm,
      fun r s' m' hsp hcl hpr _ hr _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl, hpr, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_backbone_lit` under its
explicit semantic unit-entailment specification `fullBackboneLitEntailsSpec`. -/
theorem nv_m3_backbone_lit_entails :
    Func.wp m3BackboneLocalEnv full_backbone_lit_body
      (nvOneLitCfg.hdr, 0#32, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧ s'.core.cur_level = 0 ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 1#64 → (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0])) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_backbone_lit_entails_wp m3BackboneLocalEnv
    (localEnv_row (by simp [m3BackboneLocalSpecTable]) (fun _ _ _ _ h => h)) _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvOneLitState, emp, rfl, m3Nv_sparseW, rfl, hm,
      fun r s' m' hspW hcl _ _ hr hent _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨s', hspW, hcl, hr, fun h1 => (hent h1).2, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_backbone`. -/
theorem nv_m3_backbone :
    Func.wp m3BackboneLocalEnv full_backbone_body
      (nvOneLitCfg.hdr, 65536#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.probing = 0#64 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_backbone_local_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, m3Nv_sparseW.toSparse, hm,
      fun r s' m' hsp hcl hpr _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl, hpr, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_probe_tail`. -/
theorem nv_m3_probe_tail :
    Func.wp m3BackboneLocalEnv full_probe_tail_body
      (nvOneLitCfg.hdr, 1024#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_probe_tail_local_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, m3Nv_sparseW.toSparse, rfl, hm,
      fun r s' m' hsp hcl _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_probe(h, initial)`. -/
theorem nv_m3_probe :
    Func.wp m3BackboneLocalEnv full_probe_body
      (nvOneLitCfg.hdr, true, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_probe_local_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, m3Nv_sparseW.toSparse, rfl, hm,
      fun r s' m' hlen _ hr _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hlen, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for closed `168`-fn
`FullProbeFull.full_probe`. -/
theorem nv_m3_probe_full :
    Func.wp m3BackboneFullEnv FullProbeFull.full_probe_body
      (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m3_probe_full_wp m3BackboneFullEnv
    (mkM3BackboneFullEnv_row_at (mainSpec := fullSolveBytesSpec) 8
      ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩)
    (mkM3BackboneFullEnv_row_at (mainSpec := fullSolveBytesSpec) 127
      ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩)
    (mkM3BackboneFullEnv_row_at (mainSpec := fullSolveBytesSpec) 139
      ⟨"full_congruence", [i64], [i64], fullCongruenceSpec, true⟩)
    (mkM3BackboneFullEnv_row_at (mainSpec := fullSolveBytesSpec) 146
      ⟨"full_sweep_sat", [i64], [i64], fullSweepSatSpec, true⟩)
    (mkM3BackboneFullEnv_row_at (mainSpec := fullSolveBytesSpec) 115
      ⟨"full_backbone", [i64, i64], [i64], fullBackboneSpec, true⟩)
    (mkM3BackboneFullEnv_row_at (mainSpec := fullSolveBytesSpec) 113
      ⟨"full_transitive", [i64], [i64], fullTransitiveSpec, true⟩)
    (mkM3BackboneFullEnv_row_at (mainSpec := fullSolveBytesSpec) 111
      ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunSpec, true⟩)
    (mkM3BackboneFullEnv_row_at (mainSpec := fullSolveBytesSpec) 121
      ⟨"full_vivify", [i64, i64], [i64], fullVivifySpec, true⟩)
    _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, m3Nv_sparseW.toSparse, rfl, hm,
      fun r s' m' hlen _ hr _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hlen, hr, nvDeduceF0_unsat, hm'⟩⟩

end PerFnNonVacuity

end LeanQbe.T.Examples.Kissat.FullM3Backbone
