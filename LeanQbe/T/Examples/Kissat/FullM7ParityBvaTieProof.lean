module

public import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullM7Splice
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
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
# Kissat `D-Full` M7 Parity BVA Tie-Break + `bb20` Proofs (`FullM7ParityBvaTieProof`)

M1-clean UNSAT-only proofs (`public section`, zero expose attrs, zero all-imports, zero SAT proofs):
1. `full_bva_pick_cand_bt_wp`: certifies `FullBvaHeap.fullBvaPickCandSpec` (callee-free) with the
   1-line symmetry-preserving tie-break `|| (deg == best_deg && clit < best_lit)`.
2. `full_probe_tail_bt_wp`: certifies `FullM6Orch.m6ProbeTailSpec` with `backboneeffort = 20`
   per mille (`(dticks / 50ULL) + 65536ULL`).
3. `full_probe_bt_wp`: certifies `FullM6Orch.m6ProbeSpec` adapting `FullM7BvaV5Fix.full_probe_m7v5`
   with `(dticks / 50ULL) + 65536ULL`.
4. Closed `22`-row `m7ParityBvaTieSpecTable`, `m7ParityBvaTieEnv`, `m7ParityBvaTie_tableImpl`,
   `m7ParityBvaTie_moduleOk`, `FullM7Splice.patchFns`/`patchRows` exports
   (`m7ParityBvaTiePatchRows`, `m7btBvaPickCandFn_impl`, `m7btProbeTailFn_impl`,
   `m7btProbeFn_impl`, `m7ParityBvaTiePatch_tableImpl`), and concrete `Mem 64` UNSAT NV
   (`XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. `full_bva_pick_cand_bt` (`FullBvaHeap.fullBvaPickCandSpec`) -/

/-- Callee-free parametric `Func.wp` proof for `full_bva_pick_cand_bt` against canonical
`FullBvaHeap.fullBvaPickCandSpec`. -/
theorem full_bva_pick_cand_bt_wp (Γ : Env) :
    ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Func.wp Γ full_bva_pick_cand_bt_body args m Q X := by
  rintro ⟨h, ncntd, f0, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hf0_lt, hnc_le, hcntd_ok, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hsc.wsort_len; have hws1_len := hsc.work_stk1_len
  c0_hsteps
  refine wp_loop_inv
    (fun (best_c, best_deg, best_lit, ci, ()) ml =>
      ml = m ∧ ci.toNat ≤ ncntd.toNat ∧
      (2 ≤ best_c.toNat → best_lit.toNat < 2 * s.core.cur_vars))
    (fun (_, _, _, ci, _) _ => ncntd.toNat - ci.toNat)
    (fun J1 hJ1 => by
      c0_hsteps
      exact hJ1 (0#32, 0#32, 0xFFFFFFFF#32, 0#32, ()) m
        ⟨rfl, Nat.zero_le _, fun h => by simp only [bv_c0] at h; omega⟩)
    (fun J1 (best_c, best_deg, best_lit, ci, ()) ml ⟨hml, hci_le, hbl_ok⟩ ih1 => ?_)
  rcases hml with rfl
  c0_hsteps_nogrp
  · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
    have hci64 : (BitVec.setWidth 64 ci).toNat = ci.toNat := by c0_bound
    have hclit_lt :
        (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
      have := hcntd_ok ci.toNat hci_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
    have h2clit :
        ((BitVec.setWidth 64 (s.scratch.work_stk1[ci.toNat]'(by omega)) <<< (1 : Nat)) + 1).toNat =
          2 * (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat + 1 := by
      change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
    have hclit_wvec :
        ((BitVec.setWidth 64
          (s.scratch.work_stk1[(BitVec.setWidth 64 ci).toNat]'(by rw [hci64]; omega)) <<<
            (1 : Nat)) + 1).toNat < s.core.wvec.length := by
      simp only [hci64, h2clit, hwv_len]; omega
    c0_hsteps
    all_goals first
      | exact ih1 (_, _, _, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, fun _ => by simpa only [hci64] using hclit_lt⟩
      | exact ih1 (_, _, best_lit, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, hbl_ok⟩
  · let mkSt (ws : List (BitVec 32)) : FullState :=
      { core := { s.core with repr := s.core.repr, min_clr := s.core.min_clr,
                              tmp_cnt := s.core.tmp_cnt, tmp_len := s.core.tmp_len }
        scratch := { s.scratch with wsort := ws, ant_sz := s.scratch.ant_sz,
                                    sim_sig := s.scratch.sim_sig,
                                    shrink_stk := s.scratch.shrink_stk } }
    c0_hsteps
    refine wp_loop_inv
      (fun (ci, ()) m2 => ∃ ws2,
        ci.toNat ≤ ncntd.toNat ∧ ws2.length = 2 * c.max_vars ∧
        (FullMem c (mkSt ws2) ⋆ R) m2)
      (fun (ci, ()) _ => ncntd.toNat - ci.toNat)
      (fun J2 hJ2 => by
        c0_hsteps
        exact hJ2 (0#32, ()) ml ⟨s.scratch.wsort, Nat.zero_le _, hws_len, hm⟩)
      (fun J2 (ci, ()) m2 ⟨ws2, hci_le, hws2_len, hm2⟩ ih2 => ?_)
    dsimp only [mkSt] at hm2
    c0_hsteps_nogrp
    · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
      have hclit_lt :
          (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        have := hcntd_ok ci.toNat hci_lt
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
      c0_hsteps
      exact ih2 (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
        ⟨_, by rw [hci1]; omega, by rw [List.length_set]; exact hws2_len, hm⟩
    · have hinv_fin : FullDenseInvNoLm c F0 F_cur (mkSt ws2) :=
        fullDenseInvNoLm_with_core_aux hinv hcl.repr_len hcl.min_clr_len_arr hcl.tmp_len_arr
          hcl.flags_len hcl.tmp_len_le { hsc with wsort_len := hws2_len } rfl rfl
      c0_hsteps
      · exact hQ 0xFFFFFFFF#32 s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin (Or.inl rfl) hm2
      · exact hQ best_lit s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin
          (Or.inr (hbl_ok (by c0_bound))) hm2

/-! ## 2. `full_probe_tail_bt` (`FullM6Orch.m6ProbeTailSpec`) -/

/-- Parametric `Func.wp` proof for `full_probe_tail_bt` against canonical
`FullM6Orch.m6ProbeTailSpec` with `backboneeffort = 20` per mille. -/
theorem full_probe_tail_bt_wp (Γ : Env)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hProbeRun : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, m6aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Func.wp Γ full_probe_tail_bt_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X hs
  rcases m6ProbeTailSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, _hcl0, hm, hQ⟩
  unfold Func.wp full_probe_tail_bt_body
  refine wp_join_group (ts := []) (fun _ m1 => ∃ s1, FullM6HdrInv c F0 ext s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullM6HdrMem c ext s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨s1, hinv1, _hcl1, hfu1, hm1⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, _hcl2, hfu2, hm2⟩
      c0_hsteps_nogrp; c0_call hMin; intro pbud _; c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun _ m3 => ∃ s3, FullM6HdrInv c F0 ext s3 ∧
          s3.core.cur_level = 0 ∧ s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullM6HdrMem c ext s3 ⋆ R) m3) ?_ ?_
      · rintro _ _ m3 ⟨s3, hinv3, _hcl3, hfu3, hm3⟩
        c0_hsteps_nogrp; c0_call hViv
        refine m6aVivifySpec_of hinv3.cfgOk hinv3.extOk hinv3.sparse hm3
          fun r4 ext4 s4 m4 ⟨hext4, _⟩ hsp4 ⟨hcl4, _⟩ hfu4 hdom4 hu4 hm4 => ?_
        have hinv4 := FullM6HdrInv.mk_inv hinv3.cfgOk hext4 hsp4
        c0_hsteps_nogrp
        · exact hQ 20#64 ext4 s4 m4 hsp4.lengths hext4 (Nat.le_trans hfu4 hfu3)
            (Or.inr rfl) (fun _ => hu4 ‹_›) (fun h => by cases h) hm4
        · exact hQ 1#64 ext4 s4 m4 hsp4.lengths hext4 (Nat.le_trans hfu4 hfu3)
            (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinv4, hcl4⟩) hm4
      · intro J3 hJ3
        refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
        c0_hsteps_nogrp
        · c0_call hProbeRun
          refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hm2f,
            fun r3 s3 m3 hsp3 hcl3 _ hfu3 hdom3 hu3 _ hm3 => ?_⟩
          have hinv3 := FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hsp3
          have hm3' := fullM6HdrMem_unfocus hm3
          c0_hsteps_nogrp
          · exact hQ 20#64 ext s3 m3 hsp3.lengths hinv3.extOk (Nat.le_trans hfu3 hfu2)
              (Or.inr rfl) (fun _ => hu3 ‹_›) (fun h => by cases h) hm3'
          · exact hJ3 () m3 ⟨s3, hinv3, hcl3, Nat.le_trans hfu3 hfu2, hm3'⟩
        · exact hJ3 () m2 ⟨s2, hinv2, _hcl2, hfu2, hm2⟩
    · intro J2 hJ2
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      c0_hsteps_nogrp
      · c0_call hTrans
        refine ⟨c, F0, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv1.sparse, hm1f,
          fun r2 s2 m2 hsp2 hcl2 _ _ hfu2 hdom2 hu2 hm2 => ?_⟩
        have hinv2 := FullM6HdrInv.mk_inv hinv1.cfgOk hinv1.extOk hsp2
        have hm2' := fullM6HdrMem_unfocus hm2
        c0_hsteps_nogrp
        · exact hQ 20#64 ext s2 m2 hsp2.lengths hinv2.extOk (Nat.le_trans hfu2 hfu1)
            (Or.inr rfl) (fun _ => hu2 ‹_›) (fun h => by cases h) hm2'
        · exact hJ2 () m2 ⟨s2, hinv2, hcl2 _hcl1, Nat.le_trans hfu2 hfu1, hm2'⟩
      · exact hJ2 () m1 ⟨s1, hinv1, _hcl1, hfu1, hm1⟩
  · intro J1 hJ1
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp
    · c0_call hBackbone
      refine ⟨c, F0, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse, hmf,
        fun r1 s1 m1 hsp1 hcl1 _ hfu1 hdom1 hu1 hm1 => ?_⟩
      have hinv1 := FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp1
      have hm1' := fullM6HdrMem_unfocus hm1
      c0_hsteps_nogrp
      · exact hQ 20#64 ext s1 m1 hsp1.lengths hinv1.extOk hfu1
          (Or.inr rfl) (fun _ => hu1 ‹_›) (fun h => by cases h) hm1'
      · exact hJ1 () m1 ⟨s1, hinv1, hcl1, hfu1, hm1'⟩
    · exact hJ1 () m ⟨s, hinv, _hcl0, Nat.le_refl _, hm⟩

/-! ## 3. `full_probe_bt` (`FullM6Orch.m6ProbeSpec`) -/

private theorem bt_probe_ret_wm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s0 s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    {args : Tup (Arg Val) [i64, i64, i64]}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hk_ret : k () = .ret (Arg.imm r, ()))
    (hargs : vals args = (c.hdr, 0#64, BitVec.ofNat 64 s.scratch.search_ticks.toNat, ()) ∨
      vals args = (c.hdr, 0#64, s.scratch.search_ticks, ()))
    (hSetWm : ∀ a m' Q' X', m6HdrW2aSpec [i64, i64] [] a m' Q' X' →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m' Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hfu : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hr : r = 1#64 ∨ r = 20#64) (hu : r = 20#64 → F0.Unsat)
    (h1 : r = 1#64 → FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (.call "m6_hdr_set_watermark" (as := [i64, i64, i64]) (bs := []) args k) m := by
  have hargs' : ∃ v, vals args = (c.hdr, 0#64, v, ()) :=
    hargs.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  obtain ⟨v, hv⟩ := hargs'
  refine m6Hdr_call_m6HdrW2a hv (fun _ _ h => hSetWm _ _ _ _ h) hcfg hext hlen hm
    fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
  rw [hk_ret]; c0_hsteps_nogrp
  exact hQ ext' s' m' hlen' hext' (by rw [hc']; exact hfu) hr hu
    (fun h => let ⟨hi, hcl⟩ := h1 h
      ⟨fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hi hlen' hc' hms') hext',
        by rw [hc']; exact hcl⟩) hm'

/-- Parametric `Func.wp` proof for `full_probe_bt` against canonical `FullM6Orch.m6ProbeSpec`. -/
theorem full_probe_bt_wp (Γ : Env)
    (hDticks : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweep : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, Full.fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X →
      Func.wp Γ full_probe_bt_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_bt_body
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDticks _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths hm
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := by rw [hc0]; exact hcl0
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ mW => ∃ extW sW, FullM6HdrInv c F0 extW sW ∧
        sW.core.cur_level = 0 ∧ sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c extW sW ⋆ R) mW) ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ mW ⟨extW, sW, hinvW, hclW, hfuW, hmW⟩
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun _ mT => ∃ extT sT, FullM6HdrInv c F0 extT sT ∧
          sT.core.cur_level = 0 ∧ sT.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullM6HdrMem c extT sT ⋆ R) mT) ?_ ?_
      · rintro _ _ mT ⟨extT, sT, hinvT, hclT, hfuT, hmT⟩
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mRet => ∃ extRet sRet,
            FullM6HdrInv c F0 extRet sRet ∧ sRet.core.cur_level = 0 ∧
            sRet.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extRet sRet ⋆ R) mRet)
          ?_ ?_
        · rintro _ _ mRet ⟨extRet, sRet, hinvRet, hclRet, hfuRet, hmRet⟩
          refine wp_m6Hdr_focus_frame hmRet fun hmRetf => ?_
          c0_hsteps_nogrp
          exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvRet.cfgOk hinvRet.extOk
            hinvRet.sparse.lengths hfuRet (Or.inl rfl) (fun h => by cases h)
            (fun _ => ⟨hinvRet, hclRet⟩) (fullM6HdrMem_unfocus hmRetf) (hQ 1#64)
        · intro Jret hJret; c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun _ mInc => ∃ extInc sInc,
              FullM6HdrInv c F0 extInc sInc ∧ sInc.core.cur_level = 0 ∧
              sInc.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extInc sInc ⋆ R) mInc)
            ?_ ?_
          · rintro _ _ mInc ⟨extInc, sInc, hinvInc, hclInc, hfuInc, hmInc⟩
            refine wp_m6Hdr_focus_frame hmInc fun hmIncf => ?_
            c0_hsteps_nogrp
            · exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvInc.cfgOk hinvInc.extOk
                hinvInc.sparse.lengths hfuInc (Or.inr rfl)
                (fun _ => fullM6HdrInv_inconsistent_unsat hinvInc ‹_›)
                (fun h => by cases h) (fullM6HdrMem_unfocus hmIncf) (hQ 20#64)
            · exact hJret () mInc
                ⟨extInc, sInc, hinvInc, hclInc, hfuInc, fullM6HdrMem_unfocus hmIncf⟩
          · intro Jinc hJinc; c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mF0 => ∃ extF0 sF0,
                FullM6HdrInv c F0 extF0 sF0 ∧ sF0.core.cur_level = 0 ∧
                sF0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extF0 sF0 ⋆ R) mF0)
              ?_ ?_
            · rintro _ _ mF0 ⟨extF0, sF0, hinvF0, hclF0, hfuF0, hmF0⟩
              refine wp_m6Hdr_focus_frame hmF0 fun hmTf => ?_
              c0_hsteps_nogrp
              · c0_call hEnter
                refine ⟨c, F0, sF0, m6ExtMem (m6ExtAddr c.hdr) extF0 ⋆ R, rfl, hinvF0.sparse,
                  hmTf, fun ok sF mF hclF hfuF hdenF hspF hmF => ?_⟩
                have hmF' := fullM6HdrMem_unfocus hmF
                c0_hsteps_nogrp
                · have hdenF' := hdenF ‹_›
                  refine wp_join_group (ts := [i64]) (fun _ mB => mB = mF)
                    (fun _ ⟨fbud0, ⟨⟩⟩ mB hmB => by
                      subst hmB
                      c0_hsteps_nogrp; c0_call hMin; intro fbud _; c0_hsteps_nogrp
                      c0_call hFactor
                      refine ⟨c, F0, sF, m6ExtMem (m6ExtAddr c.hdr) extF0 ⋆ R, rfl, hdenF',
                        hmF, fun _ sFc mFc hdenFc _ hfuFc _ hmFc => ?_⟩
                      c0_hsteps_nogrp; c0_call hRebuild
                      refine ⟨c, F0, sFc, m6ExtMem (m6ExtAddr c.hdr) extF0 ⋆ R, rfl, hdenFc,
                        hmFc, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvF0.cfgOk hinvF0.extOk hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      have hfuR' : sR.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hfuFc] at hfuR; exact Nat.le_trans hfuR (Nat.le_trans hfuF hfuF0)
                      c0_hsteps_nogrp
                      · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                        c0_hsteps_nogrp
                        exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                          hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                          (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                      · exact hJret () mR ⟨extF0, sR, hinvR, hclR, hfuR', hmR'⟩)
                    (fun _ hJ0 => by c0_hsteps_nogrp <;> exact hJ0 (_, ()) mF rfl)
                · have hinvF := FullM6HdrInv.mk_inv hinvF0.cfgOk hinvF0.extOk (hspF ‹_›)
                  exact hJinc () mF ⟨extF0, sF, hinvF, hclF, Nat.le_trans hfuF hfuF0, hmF'⟩
            · intro Jfact hJfact
              refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
              c0_hsteps_nogrp
              · exact hJfact () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
              · exact hJfact () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
              · exact hJfact () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
              · exact hJinc () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
      · intro JT hJT; c0_hsteps_nogrp
        · refine wp_m6Hdr_focus_frame hmW fun hmWf => ?_
          c0_hsteps_nogrp
          · c0_call hBackbone
            refine ⟨c, F0, sW, m6ExtMem (m6ExtAddr c.hdr) extW ⋆ R, rfl, hinvW.sparse, hmWf,
              fun rB sB mB hspB hclB _ hfuB hdB huB hmB => ?_⟩
            have hinvB := FullM6HdrInv.mk_inv hinvW.cfgOk hinvW.extOk hspB
            have hmB' := fullM6HdrMem_unfocus hmB
            c0_hsteps_nogrp
            · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
              c0_hsteps_nogrp
              exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                hinvB.sparse.lengths (Nat.le_trans hfuB hfuW) (Or.inr rfl)
                (fun _ => huB ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
            · exact hJT () mB ⟨extW, sB, hinvB, hclB, Nat.le_trans hfuB hfuW, hmB'⟩
          · exact hJT () mW ⟨extW, sW, hinvW, hclW, hfuW, fullM6HdrMem_unfocus hmWf⟩
        · c0_call hTail
          refine m6ProbeTailSpec_of hinvW hclW hmW
            fun rT extT sT mT hlT heT hfuT hdT huT h1T hmT => ?_
          c0_hsteps_nogrp
          · refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
            c0_hsteps_nogrp
            exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvW.cfgOk heT hlT
              (Nat.le_trans hfuT hfuW) (Or.inr rfl) (fun _ => huT ‹_›)
              (fun h => by cases h) (fullM6HdrMem_unfocus hmTf) (hQ 20#64)
          · exact hJT () mT ⟨extT, sT, (h1T (hdT.resolve_right ‹_›)).1,
              (h1T (hdT.resolve_right ‹_›)).2, Nat.le_trans hfuT hfuW, hmT⟩
    · intro JW hJW; c0_hsteps_nogrp
      refine wp_loop_inv (fun (round, ()) mL => round.toNat ≤ 2 ∧
          ∃ extL sL, FullM6HdrInv c F0 extL sL ∧ sL.core.cur_level = 0 ∧
            sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extL sL ⋆ R) mL)
        (fun (round, ()) _ => 2 - round.toNat)
        (fun JL hJL => by
          c0_hsteps_nogrp
          exact hJL (0#64, ()) m1 ⟨Nat.zero_le _, ext1, s1, hinv1, hcl1,
            by rw [hfu1]; exact Nat.le_refl _, hm1⟩)
        (fun JL (round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ hJL => ?_)
      · refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
        c0_hsteps_nogrp
        · have hnd_lt : round.toNat < 2 := BitVec.lt_def.mp ‹_›
          have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
          refine wp_join_group (ts := []) (fun _ mD => ∃ extD sD, FullM6HdrInv c F0 extD sD ∧
              sD.core.cur_level = 0 ∧ sD.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c extD sD ⋆ R) mD) ?_ ?_
          · rintro _ _ mD ⟨extD, sD, hinvD, hclD, hfuD, hmD⟩
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mS => ∃ extS sS, FullM6HdrInv c F0 extS sS ∧
                sS.core.cur_level = 0 ∧ sS.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c extS sS ⋆ R) mS) ?_ ?_
            · rintro _ _ mS ⟨extS, sS, hinvS, hclS, hfuS, hmS⟩
              refine wp_m6Hdr_focus_frame hmS fun hmSf => ?_
              c0_hsteps_nogrp
              · exact hJW (round, ()) mS ⟨extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
              · exact hJL (round + 1#64, ()) mS (by dsimp only; omega)
                  ⟨by omega, extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
            · intro JS hJS; refine wp_m6Hdr_focus_frame hmD fun hmDf => ?_
              c0_hsteps_nogrp
              · c0_call hSubst
                refine ⟨c, F0, sD, m6ExtMem (m6ExtAddr c.hdr) extD ⋆ R, rfl, hinvD.sparse, hmDf,
                  fun rS sS mS hspS hclS hfuS hdS huS hmS => ?_⟩
                have hinvS := FullM6HdrInv.mk_inv hinvD.cfgOk hinvD.extOk hspS
                have hmS' := fullM6HdrMem_unfocus hmS
                c0_hsteps_nogrp
                · refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                  c0_hsteps_nogrp
                  exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvS.cfgOk hinvS.extOk
                    hinvS.sparse.lengths (Nat.le_trans hfuS hfuD) (Or.inr rfl)
                    (fun _ => huS ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmSf) (hQ 20#64)
                · exact hJS () mS ⟨extD, sS, hinvS, hclS, Nat.le_trans hfuS hfuD, hmS'⟩
              · exact hJS () mD ⟨extD, sD, hinvD, hclD, hfuD, fullM6HdrMem_unfocus hmDf⟩
          · intro JD hJD
            c0_hsteps_nogrp; c0_call hEnter
            refine ⟨c, F0, sL, m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R, rfl, hinvL.sparse, hmLf,
              fun ok sE mE hclE hfuE hdenE hspE hmE => ?_⟩
            have hmE' := fullM6HdrMem_unfocus hmE
            c0_hsteps_nogrp
            · have hdenE' := hdenE ‹_›
              refine wp_join_group (ts := []) (fun _ mC => ∃ extC sC,
                  FullM6HdrCfgOk c ∧ M6HdrExtOk extC ∧ FullDenseInv c F0 sC ∧
                  sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullM6HdrMem c extC sC ⋆ R) mC) ?_ ?_
              · rintro _ _ mC ⟨extC, sC, _, hextC, hdenC, hfuC, hmC⟩
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun _ mW2 => ∃ extW2 sW2,
                    FullM6HdrCfgOk c ∧ M6HdrExtOk extW2 ∧ FullDenseInv c F0 sW2 ∧
                    sW2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c extW2 sW2 ⋆ R) mW2) ?_ ?_
                · rintro _ _ mW2 ⟨extW2, sW2, _, hextW2, hdenW2, hfuW2, hmW2⟩
                  refine wp_m6Hdr_focus_frame hmW2 fun hmW2f => ?_
                  c0_hsteps_nogrp; c0_call hRebuild
                  refine ⟨c, F0, sW2, m6ExtMem (m6ExtAddr c.hdr) extW2 ⋆ R, rfl, hdenW2, hmW2f,
                    fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                  have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextW2 hspR
                  have hmR' := fullM6HdrMem_unfocus hmR
                  have hfuR' := Nat.le_trans hfuR hfuW2
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                      hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · exact hJD () mR ⟨extW2, sR, hinvR, hclR, hfuR', hmR'⟩
                · intro JW2 hJW2
                  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                    hinvL.cfgOk hextC hdenC.lengths hmC
                    fun ⟨del2, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                  have hdenCd := fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres
                  have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcCd]; exact hfuC
                  c0_hsteps_nogrp
                  · exact hJW2 () mCd ⟨extCd, sCd, hinvL.cfgOk, hextCd, hdenCd, hfuCd, hmCd⟩
                  · refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                    c0_hsteps_nogrp; c0_call hSweep
                    refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenCd,
                      hmCdf, fun rS sS mS hdenS _ hfuS _ huS hmS => ?_⟩
                    have hfuS' := Nat.le_trans hfuS hfuCd
                    c0_hsteps_nogrp
                    · c0_call hRebuild
                      refine ⟨c, F0, sS, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenS, hmS,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuS') (Or.inr rfl)
                        (fun _ => huS ‹_›) (fun h => by cases h)
                        (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                    · have hmS' := fullM6HdrMem_unfocus hmS
                      refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                          M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                          sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                        (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ =>
                          hJW2 () mSd ⟨extSd, sSd, hinvL.cfgOk, hextSd, hdenSd, hfuSd, hmSd⟩) ?_
                      intro JSd hJSd; c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                          M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                          sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                        (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ => by
                          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                            hinvL.cfgOk hextSd hdenSd.lengths hmSd
                            fun _ extSd' sSd' mSd' hcSd hlSd hmsSd hextSd' _ hmSd' => ?_
                          exact hJSd () mSd' ⟨extSd', sSd', hextSd',
                            fullDenseInv_of_core_eq hdenSd hlSd hcSd hmsSd.extPres,
                            by rw [hcSd]; exact hfuSd, hmSd'⟩) ?_
                      intro JSdb hJSdb
                      refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                      c0_hsteps_nogrp
                      · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                          hinvL.cfgOk hextCd hdenS.lengths (fullM6HdrMem_unfocus hmSf)
                          fun _ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
                        exact hJSd () mSd ⟨extSd, sSd, hextSd,
                          fullDenseInv_of_core_eq hdenS hlSd hcSd hmsSd.extPres,
                          by rw [hcSd]; exact hfuS', hmSd⟩
                      · exact hJSdb () mS
                          ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
                      · exact hJSdb () mS
                          ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
              · intro JC hJC
                refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                  hinvL.cfgOk hinvL.extOk hdenE'.lengths hmE'
                  fun ⟨del1, ⟨⟩⟩ extEd sEd mEd hcEd hlEd hmsEd hextEd _ hmEd => ?_
                have hdenEd := fullDenseInv_of_core_eq hdenE' hlEd hcEd hmsEd.extPres
                have hfuEd : sEd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hcEd]; exact Nat.le_trans hfuE hfuL
                c0_hsteps_nogrp
                · exact hJC () mEd ⟨extEd, sEd, hinvL.cfgOk, hextEd, hdenEd, hfuEd, hmEd⟩
                · refine wp_m6Hdr_focus_frame hmEd fun hmEdf => ?_
                  c0_hsteps_nogrp; c0_call hCong
                  refine ⟨c, F0, sEd, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenEd, hmEdf,
                    fun rC sC mC hdenC _ hfuC hdomC huC hmC => ?_⟩
                  have hfuC' : sC.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfuC]; exact hfuEd
                  c0_hsteps_nogrp
                  · c0_call hRebuild
                    refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenC, hmC,
                      fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                    have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextEd hspR
                    have hmR' := fullM6HdrMem_unfocus hmR
                    refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                      hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                      (fun _ => huC ‹_›) (fun h => by cases h)
                      (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · have hmC' := fullM6HdrMem_unfocus hmC
                    refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                        M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                        sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                      (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ =>
                        hJC () mCd ⟨extCd, sCd, hinvL.cfgOk, hextCd, hdenCd, hfuCd, hmCd⟩) ?_
                    intro JCd hJCd; c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                        M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                        sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                      (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ => by
                        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                          hinvL.cfgOk hextCd hdenCd.lengths hmCd
                          fun _ extCd' sCd' mCd' hcCd hlSd hmsCd hextCd' _ hmCd' => ?_
                        exact hJCd () mCd' ⟨extCd', sCd', hextCd',
                          fullDenseInv_of_core_eq hdenCd hlSd hcCd hmsCd.extPres,
                          by rw [hcCd]; exact hfuCd, hmCd'⟩) ?_
                    intro JCdb hJCdb
                    refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                    c0_hsteps_nogrp
                    · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                        hinvL.cfgOk hextEd hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                        fun _ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                      exact hJCd () mCd ⟨extCd, sCd, hextCd,
                        fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres,
                        by rw [hcCd]; exact hfuC', hmCd⟩
                    · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                    · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
            · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hinvL.extOk (hspE ‹_›)
              refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
              c0_hsteps_nogrp
              exact bt_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hinvE.extOk
                hinvE.sparse.lengths (Nat.le_trans hfuE hfuL) (Or.inr rfl)
                (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
            · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hinvL.extOk (hspE ‹_›)
              exact hJD () mE ⟨extL, sE, hinvE, hclE, Nat.le_trans hfuE hfuL, hmE'⟩
        · exact hJW (round, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, fullM6HdrMem_unfocus hmLf⟩
  · intro J1 hJ1; c0_hsteps_nogrp
    · exact hJ1 () m0 ⟨ext0, s0, hinv0, hcl0', hc0 ▸ rfl, hm0⟩
    · refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
      c0_hsteps_nogrp; c0_call hIlog; intro logp _ _
      c0_hsteps_nogrp; c0_call hScale
      refine ⟨c, _, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl,
        (fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
          (s0.scratch.probings + 1#64)).1, by assumption, fun sd => ?_⟩
      c0_hsteps_nogrp
      have hst1 := fullState_upd_probe_step hinv0.sparse.lengths
        (s0.scratch.conflicts + sd) (s0.scratch.probings + 1#64)
      have hinv1 := fullM6HdrInv_of_probeStep hinv0 hst1
      exact hJ1 () _ ⟨ext0, _, hinv1, hst1.2.1 ▸ hcl0',
        by rw [hst1.2.1, hc0], fullM6HdrMem_unfocus (by assumption)⟩

/-! ## 4. Closed `22`-Row `SpecTable`, `Env`, `TableImpl`, `ModuleOk`, & `patchFns`/`patchRows` -/

section ModuleOkSection

/-- Closed `22`-row specification table for `m7ParityBvaTieModule` (`3` fns + `19` externs). -/
def m7ParityBvaTieSpecTable : List SpecEntry :=
  [ ⟨"full_bva_pick_cand_bt", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  , ⟨"full_probe_tail_bt", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_probe_bt", [i64, .bool], [i64], m6ProbeSpec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  , ⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullM3CongBva.fullFactorHeapSpec, true⟩ ]

theorem m7ParityBvaTieSpecTable_length : m7ParityBvaTieSpecTable.length = 22 := by t_kernel_rfl

theorem m7ParityBvaTieSpecTable_sigs :
    m7ParityBvaTieSpecTable.map (fun e => (e.name, e.as, e.rs)) = m7ParityBvaTieModule.sigs := by
  t_kernel_rfl

theorem m7ParityBvaTieSpecTable_nodup : (m7ParityBvaTieSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m7ParityBvaTieSpecTable_noExit : ∀ e ∈ m7ParityBvaTieSpecTable, e.noExit = true :=
  fun e he =>
    List.all_eq_true.mp (by rfl : m7ParityBvaTieSpecTable.all SpecEntry.noExit = true) e he

/-- Closed environment induced by `m7ParityBvaTieSpecTable`. -/
def m7ParityBvaTieEnv : Env := Env.ofTable m7ParityBvaTieSpecTable

theorem m7ParityBvaTieEnv_noExit : ∀ f as bs xs m Q X X',
    m7ParityBvaTieEnv f as bs xs m Q X → m7ParityBvaTieEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7ParityBvaTieSpecTable_noExit

private theorem m7btEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs} (idx : Nat)
    (hmem : m7ParityBvaTieSpecTable[idx]? = some (⟨nm, as, bs, sp, true⟩ : SpecEntry))
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m7ParityBvaTieEnv nm as bs xs m Q X := fun xs m Q X hs =>
  Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) (List.mem_of_getElem? hmem)
    m7ParityBvaTieSpecTable_nodup (hno xs m Q X hs)

private theorem m7bt_bva_pick_cand_env_wp : ∀ a m Q X, fullBvaPickCandSpec a m Q X →
    Func.wp m7ParityBvaTieEnv full_bva_pick_cand_bt_body a m Q X :=
  full_bva_pick_cand_bt_wp m7ParityBvaTieEnv

private theorem m7bt_probe_tail_env_wp : ∀ a m Q X, m6ProbeTailSpec a m Q X →
    Func.wp m7ParityBvaTieEnv full_probe_tail_bt_body a m Q X :=
  full_probe_tail_bt_wp m7ParityBvaTieEnv
    (m7btEnv_row 3 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 4 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 5 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 6 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 7 rfl fun _ _ _ _ h => m6aVivifySpec_monoX h)

private theorem m7bt_probe_env_wp : ∀ a m Q X, m6ProbeSpec a m Q X →
    Func.wp m7ParityBvaTieEnv full_probe_bt_body a m Q X :=
  full_probe_bt_wp m7ParityBvaTieEnv
    (m7btEnv_row 8 rfl fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7btEnv_row 9 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 10 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 11 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 12 rfl fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7btEnv_row 13 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 14 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 15 rfl fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7btEnv_row 16 rfl fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7btEnv_row 17 rfl fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7btEnv_row 18 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 19 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 20 rfl fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
    (m7btEnv_row 3 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 5 rfl fun _ _ _ _ h => h)
    (m7btEnv_row 21 rfl fun _ _ _ _ h => h)

theorem m7bt_bva_pick_cand_impl : SpecEntry.Impl m7ParityBvaTieEnv
    ⟨"full_bva_pick_cand_bt", [i64, i32, i32], [i32], full_bva_pick_cand_bt_body⟩
    ⟨"full_bva_pick_cand_bt", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩ :=
  SpecEntry.Impl.of m7bt_bva_pick_cand_env_wp

theorem m7bt_probe_tail_impl : SpecEntry.Impl m7ParityBvaTieEnv
    ⟨"full_probe_tail_bt", [i64, i64], [i64], full_probe_tail_bt_body⟩
    ⟨"full_probe_tail_bt", [i64, i64], [i64], m6ProbeTailSpec, true⟩ :=
  SpecEntry.Impl.of m7bt_probe_tail_env_wp

theorem m7bt_probe_impl : SpecEntry.Impl m7ParityBvaTieEnv
    ⟨"full_probe_bt", [i64, .bool], [i64], full_probe_bt_body⟩
    ⟨"full_probe_bt", [i64, .bool], [i64], m6ProbeSpec, true⟩ :=
  SpecEntry.Impl.of m7bt_probe_env_wp

theorem m7btBvaPickCandFn_impl : SpecEntry.Impl m7ParityBvaTieEnv m7btBvaPickCandFn
    ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩ :=
  SpecEntry.Impl.of m7bt_bva_pick_cand_env_wp

theorem m7btProbeTailFn_impl : SpecEntry.Impl m7ParityBvaTieEnv m7btProbeTailFn
    ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ :=
  SpecEntry.Impl.of m7bt_probe_tail_env_wp

theorem m7btProbeFn_impl : SpecEntry.Impl m7ParityBvaTieEnv m7btProbeFn
    ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :=
  SpecEntry.Impl.of m7bt_probe_env_wp

theorem m7ParityBvaTie_allFns_wf : AllFns Fn.Wf m7ParityBvaTieModule.fns :=
  ⟨full_bva_pick_cand_bt_wf, full_probe_tail_bt_wf, full_probe_bt_wf, trivial⟩

theorem m7ParityBvaTie_tableImpl :
    TableImpl m7ParityBvaTieEnv m7ParityBvaTieModule.fns m7ParityBvaTieSpecTable :=
  ⟨m7bt_bva_pick_cand_impl, m7bt_probe_tail_impl, m7bt_probe_impl, trivial⟩

/-- Closed `ModuleOk` certifying `m7ParityBvaTieModule` under `m7ParityBvaTieEnv` (`0` exits). -/
theorem m7ParityBvaTie_moduleOk : ModuleOk m7ParityBvaTieEnv m7ParityBvaTieModule :=
  Env.ofTable_moduleOk m7ParityBvaTie_acyclic m7ParityBvaTie_allFns_wf m7ParityBvaTie_tableImpl

/-- `FullM7Splice.patchRows`-ready `3`-row replacement table preserving exact `m7SpecTable` specs.
-/
def m7ParityBvaTiePatchRows : List SpecEntry :=
  [ ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ ]

theorem m7ParityBvaTiePatchRows_sigs :
    m7ParityBvaTiePatchRows.map (fun e => (e.name, e.as, e.rs)) =
      m7ParityBvaTiePatchFns.map Fn.sig := by
  t_kernel_rfl

theorem m7ParityBvaTiePatchRows_noExit :
    m7ParityBvaTiePatchRows.all SpecEntry.noExit = true := by
  rfl

/-- `TableImpl` for `m7ParityBvaTiePatchFns` against `m7ParityBvaTiePatchRows` under
`m7ParityBvaTieEnv`. -/
theorem m7ParityBvaTiePatch_tableImpl :
    TableImpl m7ParityBvaTieEnv m7ParityBvaTiePatchFns m7ParityBvaTiePatchRows :=
  ⟨m7btBvaPickCandFn_impl, m7btProbeTailFn_impl, m7btProbeFn_impl, trivial⟩

/-- Generic `TableImpl` lift for `FullM7Splice.patchFns` / `patchRows` under any callee env `Γ`.
-/
theorem m7ParityBvaTiePatch_tableImpl_of (Γ : Env)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hProbeRun : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, m6aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X)
    (hDticks : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweep : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, Full.fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    TableImpl Γ m7ParityBvaTiePatchFns m7ParityBvaTiePatchRows :=
  ⟨ SpecEntry.Impl.of (full_bva_pick_cand_bt_wp Γ)
  , SpecEntry.Impl.of (full_probe_tail_bt_wp Γ hBackbone hTrans hMin hProbeRun hViv)
  , SpecEntry.Impl.of (full_probe_bt_wp Γ hDticks hIlog hScale hEnter hDelay hCong hRebuild
      hSetWm hRedD hBumpD hSweep hSubst hTail hBackbone hMin hFactor)
  , trivial ⟩

end ModuleOkSection

/-! ## 5. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteUnsatNv

private theorem nvM7bt_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl; have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore nvOneLitState.core → False := fun _ hr => by
    rw [show fullArenaClauseRefsCore nvOneLitState.core = [] from rfl] at hr; cases hr
  have hi0 : ∀ i, i < nvOneLitState.core.trail_end → i = 0 := fun _ hi => by rw [hte] at hi; omega
  have hL0 : ∀ L, L ≤ nvOneLitState.core.cur_level → L = 0 := fun _ hL => by rw [hcl] at hL; omega
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact .empty)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) :=
    CNF.entails_clause_def.mpr fun _ hα =>
      (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim,
        fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hi0 i hi]; decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hi0 i hi, hi0 j hj]
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hi0 i hi]; exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hp => by rw [hi0 j hj] at hp; exact absurd hp.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hi0 i hi]; exact hent0
      trail_pos_inv := fun i hi => by rw [hi0 i hi]; rfl
      level0_rsn_none := fun i hi _ => by rw [hi0 i hi]; rfl
      frame_trail_lt := fun L hL => by rw [hL0 L hL]; decide
      frame_trail_mono := fun L1 L2 h12 hL2 => by
        rw [hL0 L1 (by omega), hL0 L2 hL2]; exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => absurd rfl (hi0 i hi ▸ hne)
      reason_lit_mem := fun i hi hne => absurd rfl (hi0 i hi ▸ hne) }
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => (hr0 r hr).elim,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by simp only [nvOneLitState, nvOneLitScratch,
      List.getElem?_replicate, show i < 16 by omega, ↓reduceIte, Option.getD_some],
      Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem nvM7bt_hdrMem_emp :
    (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
  rw [sep_emp]; exact nvM6HdrMem_ok

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_pick_cand_bt` on
`nvBvaDenseMem` with `ncntd = 2#32` (exercising both loops). -/
theorem nv_m7bt_bva_pick_cand :
    Func.wp m7ParityBvaTieEnv full_bva_pick_cand_bt_body
      (nvOneLitCfg.hdr, 2#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  refine m7bt_bva_pick_cand_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW, by decide, by decide, ?_, hm,
      fun r _ _ _ _ _ _ _ _ m' hnl hr hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, hr, nvDeduceF0_unsat, hm'⟩⟩
  intro i hi
  have hi' : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_probe_tail_bt` on
`nvM6HdrMem`. -/
theorem nv_m7bt_probe_tail :
    Func.wp m7ParityBvaTieEnv full_probe_tail_bt_body (nvOneLitCfg.hdr, 1024#64, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  m7bt_probe_tail_impl.2 _ _ _ _
    (m6ProbeTailSpec_of
      (FullM6HdrInvW.mk_inv nvM6HdrCfg_ok nvM6ExtWords_ok nvM7bt_sparseW).toInv
      rfl nvM7bt_hdrMem_emp
      fun r ext' s' m' _ _ _ hr' hu' h1' hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hr', hu', h1', hm'⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_probe_bt` on `nvM6HdrMem`.
-/
theorem nv_m7bt_probe :
    Func.wp m7ParityBvaTieEnv full_probe_bt_body (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  m7bt_probe_impl.2 _ _ _ _
    (m6ProbeSpec_of
      (FullM6HdrInvW.mk_inv nvM6HdrCfg_ok nvM6ExtWords_ok nvM7bt_sparseW).toInv
      rfl nvM7bt_hdrMem_emp
      fun r ext' s' m' _ _ _ hr' hu' h1' hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hr', hu', h1', hm'⟩)

end ConcreteUnsatNv

end LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
