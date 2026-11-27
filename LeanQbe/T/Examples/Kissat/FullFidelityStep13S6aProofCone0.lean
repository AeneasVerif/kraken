/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelitySweep
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofCone0
import LeanQbe.T.Examples.Kissat.FullM8SweepV2ConeProof
import LeanQbe.T.Examples.Kissat.FullM6SweepProofConeLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 13 Shard `S6a` — `full_m6_sweep_cone` Helpers (`Cone0`)

Step-13 `glue_used[33]` (`K6HwmClean`) adapters over `FullFidelitySweepProofCone0`:
1. `step13ConeMask`, `S13GuOk`, `Step13Cone{,Saved,Scan}Base`, and `FullDenseInvW` / `K6HwmClean`
   preservation helpers.
2. `step13_cone_init_ok`, push/rollback/wvec adapters, `step13_cone_call_add_clause`,
   and `step13_cone_exit_post`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullFidelitySweep
open Kraken.Bedrock2.Test

@[expose] public section

/-! ## 1. Step-13 Cone Mask, `S13GuOk`, and Base Structures -/

/-- Like `fidConeMask`, also masking `glue_used` (only entry `33` is updated). -/
def step13ConeMask (t : FullState) : FullState :=
  { t with
    core := { t.core with tmp := [] }
    scratch := { t.scratch with
      work_stk1 := [], tarjan_mark := [], glue_used := [], scratch_buf := [] } }

/-- Step-13 `glue_used` side-condition across `full_m6_sweep_cone`. -/
def S13GuOk (L : K6Layout) (s st : FullState) : Prop :=
  (∀ i < 64, i ≠ 33 → st.scratch.glue_used[i]? = s.scratch.glue_used[i]?) ∧
    K6HwmClean L (st.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L st.scratch.scratch_buf)

/-- Base loop invariant for Step-13 `full_m6_sweep_cone`. -/
structure Step13ConeBase (F_cur : List (List Nat)) (L : K6Layout) (mvC : BitVec 32)
    (c : FullCfg) (s : FullState) (cv qi_l : BitVec 32) (nv nc : Nat)
    (st : FullState) : Prop where
  hlen : st.LengthsOk c
  hag : AgreesExcept step13ConeMask s st
  hgu : S13GuOk L s st
  hcone : FidConeInv F_cur L mvC st nv nc
  htmk : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1)
  hwk : (st.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat

/-- Saved-`nv` rollback invariant for Step-13 `full_m6_sweep_cone`. -/
structure Step13ConeSavedBase (F_cur : List (List Nat)) (L : K6Layout) (mvC : BitVec 32)
    (c : FullCfg) (s : FullState) (cv qi_l saved_nv : BitVec 32)
    (ws0 scr0 : List (BitVec 32)) (nv nc : Nat) (st : FullState) : Prop
    extends Step13ConeBase F_cur L mvC c s cv qi_l nv nc st where
  hsav_le : saved_nv.toNat ≤ nv
  hscr : st.scratch.scratch_buf = scr0
  hws : ∀ j < saved_nv.toNat, st.scratch.work_stk1[j]? = ws0[j]?

/-- Clause-scan invariant for Step-13 `full_m6_sweep_cone`. -/
structure Step13ConeScanBase (F_cur : List (List Nat)) (L : K6Layout) (mvC : BitVec 32)
    (c : FullCfg) (s : FullState) (cv qi_l saved_nv : BitVec 32)
    (ws0 scr0 : List (BitVec 32)) (cr : BitVec 32) (nv nc cnt idx : Nat)
    (st : FullState) : Prop
    extends Step13ConeSavedBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0 nv nc st where
  hlts : ∀ j < cnt, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv
  hcov : ∀ i < idx,
    let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
    s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st.core.tmp.take cnt).map fun x => m6ConeLift st.scratch.work_stk1 x.toNat
  hvars : ∀ j < cnt, ∃ p < idx,
    (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 =
      (st.scratch.work_stk1[(st.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  hnd : ∀ j1 j2, j1 < cnt → j2 < cnt → j1 ≠ j2 →
    (st.core.tmp[j1]?.getD 0#32).toNat / 2 ≠ (st.core.tmp[j2]?.getD 0#32).toNat / 2

/-- Remaining memory footprint excluding `hdrTailWords`, `scratch_buf`, `glue_used`, and `tmp`. -/
def s13SweepAddRestTmpGlue (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  FullCoreByteArrs c s.core ⋆
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
    array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
    array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig ⋆
    array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
    array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
  c.pad

end

public section

/-! ## 2. Mask Projections & `FullDenseInvW` / `K6HwmClean` Preservation -/

theorem step13ConeMask_core_eq {s st : FullState} (h : AgreesExcept step13ConeMask s st) :
    st.core = { s.core with tmp := st.core.tmp } :=
  congrArg (fun t : FullState => { t.core with tmp := st.core.tmp }) h

theorem step13ConeMask_state_eq {s st : FullState} (h : AgreesExcept step13ConeMask s st)
    (tmp' ws1' tmk' scr' gu' : List (BitVec 32)) :
    ({ st with
        core := { st.core with tmp := tmp' }
        scratch := { st.scratch with
          work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr', glue_used := gu' } } :
      FullState) =
      { s with
        core := { s.core with tmp := tmp' }
        scratch := { s.scratch with
          work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr', glue_used := gu' } } := by
  unfold AgreesExcept at h
  have h1 := congrArg (fun t : FullState =>
    FullState.mk { t.core with tmp := tmp' } { t.scratch with
      work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr', glue_used := gu' }) h
  exact h1

private theorem denseWatchSliceOk_with_tmp {F_cur : List (List Nat)} {k : FullCoreState}
    {tmp' : List (BitVec 32)} {lit p rem : Nat}
    (h : DenseWatchSliceOk F_cur k lit p rem) :
    DenseWatchSliceOk F_cur { k with tmp := tmp' } lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hw hb hn hlt hent _ ih => exact .bin hw hb hn hlt hent ih
  | occ hw0 hw1 hb h3 hlt href _ ih => exact .occ hw0 hw1 hb h3 hlt href ih

private theorem fullWitnessInv_with_tmp {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {tmp' : List (BitVec 32)}
    (hw : FullWitnessInv c F0 F_cur k) (hdm : k.dense_mode ≠ 0#64) :
    FullWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { ext_sound := hw.ext_sound
    inconsistent_sound := hw.inconsistent_sound
    arena :=
      { len_ok := hw.arena.len_ok
        refs_wf := hw.arena.refs_wf
        shrk_term := hw.arena.shrk_term
        lits_lt := hw.arena.lits_lt
        entails := hw.arena.entails }
    watches := by
      have hdw : DenseWatchesInv F_cur k := by
        have hm := hw.watches; unfold ModeWatchesInv at hm; simp [hdm] at hm; exact hm
      unfold ModeWatchesInv
      simp only [hdm, ↓reduceIte]
      exact
        { layout :=
            { bounds := hdw.layout.bounds
              pos_off := hdw.layout.pos_off
              disjoint := hdw.layout.disjoint
              no_sentinel := hdw.layout.no_sentinel }
          slices := fun l hl => denseWatchSliceOk_with_tmp (hdw.slices l hl) }
    cur_level_le := hw.cur_level_le
    trail_lits_lt := hw.trail_lits_lt
    trail_vars_nodup := hw.trail_vars_nodup
    vals_domain := hw.vals_domain
    vals_true_iff := hw.vals_true_iff
    vals_false_iff := hw.vals_false_iff
    lvl_le := hw.lvl_le
    dec_earliest := hw.dec_earliest
    levels_inhabited := hw.levels_inhabited
    level0_sound := hw.level0_sound
    trail_pos_inv := hw.trail_pos_inv
    level0_rsn_none := hw.level0_rsn_none
    frame_trail_lt := hw.frame_trail_lt
    frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := hw.frame_trail_before_lt
    frame_dec_lt := hw.frame_dec_lt
    reason_inv := hw.reason_inv
    reason_lit_mem := hw.reason_lit_mem }

theorem step13ConeMask_preserves_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (h : AgreesExcept step13ConeMask s st) (hlen : st.LengthsOk c)
    (hdw : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur st := by
  have hc := step13ConeMask_core_eq h
  unfold AgreesExcept at h
  have hll := congrArg (fun t : FullState => t.scratch.last_learned) h
  change st.scratch.last_learned = s.scratch.last_learned at hll
  have hel := congrArg (fun t : FullState => t.scratch.extend_len) h
  change st.scratch.extend_len = s.scratch.extend_len at hel
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]; exact fullWitnessInv_with_tmp hdw.2.1 hdw.2.2.2.2.2.2
  · have hlm := hdw.2.2.1
    unfold FullLitMarksClear FullMrkZero at hlm ⊢
    rw [hc]; exact hlm
  · have hnd := hdw.2.2.2.1
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits at hnd ⊢
    rw [hc]; exact hnd
  · have hsc := hdw.2.2.2.2.1
    unfold FullExtScratchOk FullLastLearnedWf fullArenaClauseRefs at hsc ⊢
    rw [hc, hll, hel]; exact hsc
  · rw [hc]; exact hdw.2.2.2.2.2.1
  · rw [hc]; exact hdw.2.2.2.2.2.2

theorem s13GuOk_with_core_tmp {L : K6Layout} {s st : FullState} {tmp' : List (BitVec 32)}
    (h : S13GuOk L s st) :
    S13GuOk L s { st with core := { st.core with tmp := tmp' } } := h

theorem s13GuOk_with_ws_tmk {L : K6Layout} {s st : FullState} {ws' tmk' : List (BitVec 32)}
    (h : S13GuOk L s st) :
    S13GuOk L s { st with scratch := { st.scratch with work_stk1 := ws', tarjan_mark := tmk' } } :=
  h

theorem s13GuOk_trans_step {L : K6Layout} {s0 st : FullState} {gu' scr' : List (BitVec 32)}
    (h : S13GuOk L s0 st)
    (hgu : ∀ i < 64, i ≠ 33 → gu'[i]? = st.scratch.glue_used[i]?)
    (hwm : K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr')) :
    S13GuOk L s0 { st with scratch := { st.scratch with scratch_buf := scr', glue_used := gu' } } :=
  ⟨fun i hi h33 => (hgu i hi h33).trans (h.1 i hi h33), hwm⟩

theorem k6HwmClean_putHdr_nv {L : K6Layout} {hw : BitVec 32} {ks : K6State} {f : K6HdrField}
    {v : BitVec 32} (h : K6HwmClean L hw ks) : K6HwmClean L hw (ks.putHdr f v) := by
  have h1 : (ks.putHdr f v).lvlArr = ks.lvlArr := by cases f <;> rfl
  have h2 : (ks.putHdr f v).rsn = ks.rsn := by cases f <;> rfl
  have h3 : (ks.putHdr f v).flags = ks.flags := by cases f <;> rfl
  have h4 : (ks.putHdr f v).vals = ks.vals := by cases f <;> rfl
  have h5 : (ks.putHdr f v).whead = ks.whead := by cases f <;> rfl
  unfold K6HwmClean at h ⊢
  rwa [h1, h2, h3, h4, h5]

theorem k6HwmClean_putArr_qnext {L : K6Layout} {hw : BitVec 32} {ks : K6State} {idx : Nat}
    {v : BitVec 32} (h : K6HwmClean L hw ks) :
    K6HwmClean L hw (ks.putArr .qnext idx v) := by
  simpa [K6HwmClean, K6State.putArr] using h

/-! ## 3. Adapters for `Base` / `SavedBase` / `ScanBase` -/

theorem Step13ConeBase.toFid {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s : FullState} {cv qi_l : BitVec 32} {nv nc : Nat} {st : FullState}
    (hb : Step13ConeBase F_cur L mvC c s cv qi_l nv nc st) :
    FidConeBase F_cur L mvC c st cv qi_l nv nc st :=
  ⟨hb.hlen, agreesExcept_refl fidConeMask st, hb.hcone, hb.htmk, hb.hwk⟩

theorem Step13ConeSavedBase.toFid {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s : FullState} {cv qi_l saved_nv : BitVec 32} {ws0 scr0 : List (BitVec 32)}
    {nv nc : Nat} {st : FullState}
    (hb : Step13ConeSavedBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0 nv nc st) :
    FidConeSavedBase F_cur L mvC c st cv qi_l saved_nv ws0 scr0 nv nc st :=
  ⟨hb.toStep13ConeBase.toFid, hb.hsav_le, hb.hscr, hb.hws⟩

theorem Step13ConeScanBase.toFid {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s : FullState} {cv qi_l saved_nv : BitVec 32} {ws0 scr0 : List (BitVec 32)}
    {cr : BitVec 32} {nv nc cnt idx : Nat} {st : FullState}
    (hb : Step13ConeScanBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0 cr nv nc cnt idx st) :
    FidConeScanBase F_cur L mvC c st cv qi_l saved_nv ws0 scr0 cr nv nc cnt idx st := by
  have hc := step13ConeMask_core_eq hb.hag
  refine ⟨hb.toStep13ConeSavedBase.toFid, hb.hlts, ?_, ?_, hb.hnd⟩
  · intro i hi; have h := hb.hcov i hi; rwa [hc]
  · intro j hj; have h := hb.hvars j hj; rwa [hc]

theorem step13_cone_init_ok {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s : FullState} {scr0 gu0 : List (BitVec 32)} {mvC root_v : BitVec 32}
    (hs : s.LengthsOk c) (hLscr : L.scrLen = c.scratch_cap)
    (hmv1 : 1 ≤ mvC.toNat) (hmv2 : mvC.toNat ≤ L.maxV)
    (hrv : root_v.toNat < s.core.cur_vars) (htmk0 : M6TmkZero s)
    (hs' : ({ s with scratch := { s.scratch with scratch_buf := scr0, glue_used := gu0 } } :
      FullState).LengthsOk c)
    (hgu_other : ∀ i < 64, i ≠ 33 → gu0[i]? = s.scratch.glue_used[i]?)
    (hwm0 : K6HwmClean L (gu0[33]?.getD 0#32) (k6StateOfScratch L scr0))
    (hinv0 : ∀ P, K6Inv L P (k6StateOfScratch L scr0))
    (hsync0 : K6TrailSynced (k6StateOfScratch L scr0))
    (hnv0 : (k6StateOfScratch L scr0).nv = mvC)
    (hnc0 : (k6StateOfScratch L scr0).nc = 0#32)
    (hlvl0 : (k6StateOfScratch L scr0).lvl = 0#32)
    (htrl0 : (k6StateOfScratch L scr0).trl_end = 0#32)
    (hna0 : (k6StateOfScratch L scr0).nassump = 0#32) :
    let s1 : FullState :=
      { s with scratch := { s.scratch with
        work_stk1 := s.scratch.work_stk1.set 0 root_v
        tarjan_mark := s.scratch.tarjan_mark.set root_v.toNat 1#32
        scratch_buf := scr0
        glue_used := gu0 } }
    s1.LengthsOk c ∧ AgreesExcept step13ConeMask s s1 ∧ S13GuOk L s s1 ∧
      FidConeInv F_cur L mvC s1 1 0 := by
  let s_gu : FullState := { s with scratch := { s.scratch with glue_used := gu0 } }
  have hs_gu : s_gu.LengthsOk c :=
    ⟨hs.core_ok, { hs.scratch_ok with glue_used_len := hs'.scratch_ok.glue_used_len }⟩
  obtain ⟨hlen1, _, hinv1⟩ := fidConeInv_init (F_cur := F_cur) hs_gu hLscr hmv1 hmv2 hrv
    htmk0 hs'.scratch_ok.scratch_buf_len hinv0 hsync0 hnv0 hnc0 hlvl0 htrl0 hna0
  exact ⟨hlen1, rfl, ⟨hgu_other, hwm0⟩, hinv1⟩

theorem step13_cone_push_var_step_ok {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l saved_nv nv v_new : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {nc_w : Nat}
    (hb : Step13ConeSavedBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0 nv.toNat nc_w st)
    (h_nv : nv.toNat < mvC.toNat) (hv_cv : v_new.toNat < s.core.cur_vars)
    (h_un : st.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 = 0#32)
    (h_qi : qi_l.toNat < nv.toNat) :
    let st' :=
      { st with scratch := { st.scratch with
        work_stk1 := st.scratch.work_stk1.set nv.toNat v_new
        tarjan_mark := st.scratch.tarjan_mark.set v_new.toNat (nv + 1#32) } }
    nv.toNat < s.core.cur_vars ∧ (nv + 1#32).toNat = nv.toNat + 1 ∧
      nv.toNat ≠ qi_l.toNat ∧ cv.toNat ≠ v_new.toNat ∧
      Step13ConeSavedBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0 (nv + 1#32).toNat nc_w st' ∧
      st'.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 ≠ 0#32 := by
  have hc := step13ConeMask_core_eq hb.hag
  have hv_cv_st : v_new.toNat < st.core.cur_vars := by rw [hc]; exact hv_cv
  have hr := fid_cone_push_var_step_ok hb.hlen (agreesExcept_refl fidConeMask st) hb.hcone
    h_nv hv_cv_st h_un hb.hsav_le h_qi hb.hws hb.htmk hb.hwk
  rcases hr with ⟨h1, h2, h3, h4, hlen', _, hcone', hws', htmk', hwk', hnz'⟩
  have h1' : nv.toNat < s.core.cur_vars := by rw [hc] at h1; exact h1
  have hsav := hb.hsav_le
  have hag' : AgreesExcept step13ConeMask s _ := agreesExcept_trans hb.hag rfl
  exact ⟨h1', h2, h3, h4,
    ⟨⟨hlen', hag', hb.hgu, hcone', htmk', hwk'⟩, by omega, hb.hscr, hws'⟩, hnz'⟩

theorem step13_cone_push_var_base_ok {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l nv v_new : BitVec 32} {nc_w : Nat}
    (hb : Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat nc_w st)
    (h_nv : nv.toNat < mvC.toNat) (hv_cv : v_new.toNat < s.core.cur_vars)
    (h_un : st.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 = 0#32)
    (h_qi : qi_l.toNat < nv.toNat) :
    let st' :=
      { st with scratch := { st.scratch with
        work_stk1 := st.scratch.work_stk1.set nv.toNat v_new
        tarjan_mark := st.scratch.tarjan_mark.set v_new.toNat (nv + 1#32) } }
    nv.toNat < s.core.cur_vars ∧ (nv + 1#32).toNat = nv.toNat + 1 ∧
      nv.toNat ≠ qi_l.toNat ∧ cv.toNat ≠ v_new.toNat ∧
      Step13ConeBase F_cur L mvC c s cv qi_l (nv + 1#32).toNat nc_w st' ∧
      st'.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 ≠ 0#32 := by
  have hb' : Step13ConeSavedBase F_cur L mvC c s cv qi_l nv
      st.scratch.work_stk1 st.scratch.scratch_buf nv.toNat nc_w st :=
    ⟨hb, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  have hr := step13_cone_push_var_step_ok hb' h_nv hv_cv h_un h_qi
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1.toStep13ConeBase, hr.2.2.2.2.2⟩

theorem step13_cone_rollback_step {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s st_r : FullState} {scr0 ws0 : List (BitVec 32)}
    {saved_nv nv_r cv qi_l : BitVec 32} {nc_w : Nat}
    (hlen : st_r.LengthsOk c) (hag : AgreesExcept step13ConeMask s st_r)
    (hgu : S13GuOk L s st_r) (hcone : FidConeInv F_cur L mvC st_r nv_r.toNat nc_w)
    (hs1 : 1 ≤ saved_nv.toNat) (hlt : saved_nv.toNat < nv_r.toNat)
    (hqi : qi_l.toNat < saved_nv.toNat) (hscr : st_r.scratch.scratch_buf = scr0)
    (hbdd : K6LitsBounded saved_nv.toNat (k6StateOfScratch L scr0))
    (htrl : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * saved_nv.toNat)
    (hws : ∀ j < saved_nv.toNat, st_r.scratch.work_stk1[j]? = ws0[j]?)
    (htmk : st_r.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1)) :
    (nv_r - 1#32).toNat = nv_r.toNat - 1 ∧
      ((nv_r - 1#32).setWidth 64).toNat < st_r.scratch.work_stk1.length ∧
      ∀ hvr_ws : ((nv_r - 1#32).setWidth 64).toNat < st_r.scratch.work_stk1.length,
        let vr_raw := st_r.scratch.work_stk1[((nv_r - 1#32).setWidth 64).toNat]'hvr_ws
        let st' : FullState :=
          { st_r with scratch := { st_r.scratch with
            tarjan_mark := st_r.scratch.tarjan_mark.set vr_raw.toNat 0#32 } }
        (vr_raw.setWidth 64).toNat < st_r.scratch.tarjan_mark.length ∧
          st'.LengthsOk c ∧ AgreesExcept step13ConeMask s st' ∧ S13GuOk L s st' ∧
          FidConeInv F_cur L mvC st' (nv_r - 1#32).toNat nc_w ∧
          st'.scratch.scratch_buf = scr0 ∧
          (∀ j < saved_nv.toNat, st'.scratch.work_stk1[j]? = ws0[j]?) ∧
          st'.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1) := by
  have hr := fid_cone_rollback_step hlen (agreesExcept_refl fidConeMask st_r) hcone hs1 hlt hqi
    hscr hbdd htrl hws htmk
  refine ⟨hr.1, hr.2.1, fun hvr => ?_⟩
  obtain ⟨h1, h2, _, h4, h5, h6, h7⟩ := hr.2.2 hvr
  exact ⟨h1, h2, agreesExcept_trans hag rfl, hgu, h4, h5, h6, h7⟩

theorem step13_cone_pop_var_ok {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s st_r : FullState} {scr0 ws0 : List (BitVec 32)}
    {saved_nv nv_r : BitVec 32} {nc_w : Nat}
    (hlen : st_r.LengthsOk c) (hag : AgreesExcept step13ConeMask s st_r)
    (hgu : S13GuOk L s st_r) (hcone : FidConeInv F_cur L mvC st_r nv_r.toNat nc_w)
    (hs1 : 1 ≤ saved_nv.toNat) (hlt : saved_nv.toNat < nv_r.toNat)
    (hscr : st_r.scratch.scratch_buf = scr0)
    (hbdd : K6LitsBounded saved_nv.toNat (k6StateOfScratch L scr0))
    (htrl : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * saved_nv.toNat)
    (hws : ∀ j < saved_nv.toNat, st_r.scratch.work_stk1[j]? = ws0[j]?) :
    let nv' := nv_r - 1#32
    let vr := st_r.scratch.work_stk1[nv'.toNat]?.getD 0#32
    nv'.toNat = nv_r.toNat - 1 ∧ vr.toNat < st_r.scratch.tarjan_mark.length ∧
      let tmk' := st_r.scratch.tarjan_mark.set vr.toNat 0#32
      let st' : FullState :=
        { st_r with scratch := { st_r.scratch with tarjan_mark := tmk' } }
      st'.LengthsOk c ∧ AgreesExcept step13ConeMask s st' ∧ S13GuOk L s st' ∧
        FidConeInv F_cur L mvC st' nv'.toNat nc_w ∧ st'.scratch.scratch_buf = scr0 ∧
        (∀ j < saved_nv.toNat, st'.scratch.work_stk1[j]? = ws0[j]?) := by
  have hr := fidConeInv_pop_var hlen (agreesExcept_refl fidConeMask st_r) hcone
    hs1 hlt hscr hbdd htrl hws
  obtain ⟨h1, h2, hlen', _, hcone', hscr', hws'⟩ := hr
  exact ⟨h1, h2, hlen', agreesExcept_trans hag rfl, hgu, hcone', hscr', hws'⟩

theorem step13_cone_wvec_facts {c : FullCfg} {s st_x : FullState} {F_cur : List (List Nat)}
    {lit : BitVec 32} (hlen : s.LengthsOk c) (hlen_x : st_x.LengthsOk c)
    (hag : AgreesExcept step13ConeMask s st_x) (hdw : DenseWatchesInv F_cur s.core)
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars) :
    let wOff := (st_x.core.wvec[(lit.setWidth 64 <<< 1).toNat]'(by
      have := hlen.core_ok.wvec_len; have := hlen_x.core_ok.wvec_len
      have := (step13ConeMask_core_eq hag); have := hlen.core_ok.cur_vars_le
      have := c.hmaxv; unfold dimacsBound at *; bv_omega)).setWidth 64
    let wSz := (st_x.core.wvec[(lit.setWidth 64 <<< 1 + 1#64).toNat]'(by
      have := hlen.core_ok.wvec_len; have := hlen_x.core_ok.wvec_len
      have := (step13ConeMask_core_eq hag); have := hlen.core_ok.cur_vars_le
      have := c.hmaxv; unfold dimacsBound at *; bv_omega)).setWidth 64
    wOff.toNat = fullWatchOffCore s.core lit.toNat ∧
      wSz.toNat = fullWatchSizeCore s.core lit.toNat ∧
      (wOff + wSz).toNat = fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat ∧
      wOff.toNat ≤ (wOff + wSz).toNat ∧
      (wOff + wSz).toNat - wOff.toNat = fullWatchSizeCore s.core lit.toNat ∧
      (wOff + wSz).toNat ≤ s.core.wstk.length ∧
      2 * lit.toNat % 2 ^ 64 = (lit.setWidth 64 <<< 1).toNat ∧
      (2 * lit.toNat + 1) % 2 ^ 64 = (lit.setWidth 64 <<< 1 + 1#64).toNat := by
  have hc := step13ConeMask_core_eq hag
  let s_st : FullState := { st_x with core := st_x.core }
  have hdw_st : DenseWatchesInv F_cur st_x.core :=
    { layout :=
        { bounds := fun l hl => by rw [hc] at hl ⊢; exact hdw.layout.bounds l hl
          pos_off := fun l hl hp => by rw [hc] at hl hp ⊢; exact hdw.layout.pos_off l hl hp
          disjoint := fun l1 l2 h1 h2 hn hp1 hp2 => by
            rw [hc] at h1 h2 hp1 hp2 ⊢; exact hdw.layout.disjoint l1 l2 h1 h2 hn hp1 hp2
          no_sentinel := fun l hl i hi => by
            rw [hc] at hl hi ⊢; exact hdw.layout.no_sentinel l hl i hi }
      slices := fun l hl => by
        rw [hc] at hl ⊢; exact denseWatchSliceOk_with_tmp (hdw.slices l hl) }
  have hlit_st : lit.toNat < 2 * st_x.core.cur_vars := by rw [hc]; exact hlit_lt
  have hr := fid_cone_wvec_facts hlen_x hlen_x (agreesExcept_refl fidConeMask st_x) hdw_st hlit_st
  dsimp only at hr ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
  have hwo := congrArg (fun k => fullWatchOffCore k lit.toNat) hc
  change fullWatchOffCore st_x.core lit.toNat = fullWatchOffCore s.core lit.toNat at hwo
  have hws := congrArg (fun k => fullWatchSizeCore k lit.toNat) hc
  change fullWatchSizeCore st_x.core lit.toNat = fullWatchSizeCore s.core lit.toNat at hws
  have hwl := congrArg (fun k => k.wstk.length) hc
  change st_x.core.wstk.length = s.core.wstk.length at hwl
  rw [hwo] at h1 h3; rw [hws] at h2 h3 h5; rw [hwl] at h6
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## 4. `step13_cone_call_add_clause` and `step13_cone_exit_post` -/

private theorem coneLift_semEntails {F_cur : List (List Nat)} {ws xs : List (BitVec 32)}
    {sz nv : Nat} (hlts : ∀ j < sz, (xs[j]?.getD 0#32).toNat < 2 * nv)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((xs.take sz).map fun x => m6ConeLift ws x.toNat))) :
    SemEntails (ConeModelSet F_cur ws nv) ((xs.take sz).map BitVec.toNat) := by
  intro β ⟨α, hα, hβ⟩
  have hsat := (Std.Sat.CNF.entails_clause_def.mp hent) α hα
  obtain ⟨lit, hmem, htrue⟩ := Std.Sat.CNF.Clause.sat_iff_exists_mem_eq.mp hsat
  rw [← Std.Sat.CNF.Clause.mem_literals_iff, cnfClause,
    Std.Sat.CNF.Clause.literals_ofLiterals, List.mem_map] at hmem
  rcases hmem with ⟨y, hy, rfl⟩
  rw [List.mem_map] at hy
  rcases hy with ⟨x, hx, rfl⟩
  refine Std.Sat.CNF.Clause.sat_iff_exists_mem_eq.mpr ⟨litToLiteral x.toNat, ?_, ?_⟩
  · rw [← Std.Sat.CNF.Clause.mem_literals_iff, cnfClause,
      Std.Sat.CNF.Clause.literals_ofLiterals, List.mem_map]
    exact ⟨x.toNat, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩
  · obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
    have hi_sz : i < sz := lt_of_lt_of_le hi (List.length_take_le sz xs)
    have hi_len : i < xs.length := lt_of_lt_of_le hi (List.length_take_le' sz xs)
    have hx_eq : xs[i]?.getD 0#32 = x := by
      rw [List.getElem_take] at hxi
      simp [hi_len, hxi]
    have hlt : x.toNat < 2 * nv := by simpa [hx_eq] using hlts i hi_sz
    have h1 : CNF.Clause.Sat α (cnfClause [m6ConeLift ws x.toNat]) := by
      refine Std.Sat.CNF.Clause.sat_iff_exists_mem_eq.mpr
        ⟨litToLiteral (m6ConeLift ws x.toNat), ?_, htrue⟩
      rw [← Std.Sat.CNF.Clause.mem_literals_iff, cnfClause,
        Std.Sat.CNF.Clause.literals_ofLiterals]
      exact List.mem_singleton.mpr rfl
    have h2 := coneLift_sat_iff.mpr h1
    obtain ⟨l2, hm2, ht2⟩ := Std.Sat.CNF.Clause.sat_iff_exists_mem_eq.mp h2
    rw [← Std.Sat.CNF.Clause.mem_literals_iff, cnfClause,
      Std.Sat.CNF.Clause.literals_ofLiterals, List.mem_map] at hm2
    rcases hm2 with ⟨z, hz, rfl⟩
    rw [List.mem_singleton] at hz; subst hz
    have hfst : (litToLiteral x.toNat).fst < nv := by
      simp only [litToLiteral, litVar]; omega
    rwa [← hβ _ hfst] at ht2

theorem s13_focus_addCl_tmp_glue {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆
      (s13SweepAddRestTmpGlue c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrMetaArrs FullScrDynArrs at hm
  unfold s13SweepAddRestTmpGlue
  exact sep_cast hm (by ac_rfl)

theorem s13_unfocus_addCl_tmp_glue {c : FullCfg} {s : FullState} {scr' gu' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m' : Mem 64} :
    let s' : FullState :=
      { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }
    (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆
      array (t := i32) c.pScratchBuf scr' ⋆
      array (t := i32) c.pGlueUsed gu' ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆
      (s13SweepAddRestTmpGlue c s ⋆ R)) m' →
    (FullMem c s' ⋆ R) m' := by
  intro s' hm'
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrMetaArrs FullScrDynArrs
  unfold s13SweepAddRestTmpGlue at hm'
  exact sep_cast hm' (by ac_rfl)

private theorem scr_eq_of_k6_eq {L : K6Layout} {scr scr' : List (BitVec 32)}
    (hl1 : scr.length = L.scrLen) (hl2 : scr'.length = L.scrLen)
    (hpref : ∀ i < L.k6Base, scr'[i]? = scr[i]?)
    (hks : k6StateOfScratch L scr' = k6StateOfScratch L scr) : scr' = scr := by
  have hle1 : L.k6Fixed ≤ (scr.drop L.k6Base).length := by
    rw [List.length_drop, hl1]; unfold K6Layout.scrLen; omega
  have hle2 : L.k6Fixed ≤ (scr'.drop L.k6Base).length := by
    rw [List.length_drop, hl2]; unfold K6Layout.scrLen; omega
  have hdrop : scr'.drop L.k6Base = scr.drop L.k6Base := by
    have ht := congrArg K6State.toSlab hks
    simpa only [k6StateOfScratch, K6State.toSlab_ofSlab hle2, K6State.toSlab_ofSlab hle1] using ht
  have htk1 : L.k6Base ≤ scr.length := by rw [hl1]; unfold K6Layout.scrLen; omega
  have htk2 : L.k6Base ≤ scr'.length := by rw [hl2]; unfold K6Layout.scrLen; omega
  have htake : scr'.take L.k6Base = scr.take L.k6Base := by
    apply List.ext_getElem (by rw [List.length_take_of_le htk2, List.length_take_of_le htk1])
    intro i hi1 hi2
    rw [List.length_take_of_le htk2] at hi1
    have hq := hpref i hi1
    have h1 : i < scr'.length := by omega
    have h2 : i < scr.length := by omega
    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.some.injEq] at hq
    simpa [List.getElem_take] using hq
  rw [← List.take_append_drop L.k6Base scr', ← List.take_append_drop L.k6Base scr, htake, hdrop]

theorem step13_cone_call_add_clause {Γ : Env}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s0 st : FullState} {nv nc sz : BitVec 32} {aHdr aTmp : Arg Val i64} {aSz : Arg Val i32}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont [i64]}
    (haHdr : aHdr.val = c.hdr) (haTmp : aTmp.val = c.pTmp) (haSz : aSz.val = sz)
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hst : st.LengthsOk c) (hag : AgreesExcept step13ConeMask s0 st)
    (hgu : S13GuOk L s0 st) (hcone : FidConeInv F_cur L mvC st nv.toNat nc.toNat)
    (hnc_lt : nc.toNat < L.maxOrig) (hsz28 : sz.toNat < 2 ^ 28)
    (hsz_le : sz.toNat ≤ st.core.tmp.length)
    (hlts : ∀ j < sz.toNat, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st.core.tmp.take sz.toNat).map fun x => m6ConeLift st.scratch.work_stk1 x.toNat)))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (ok : Bool) (st' : FullState) (m' : Mem 64),
      st'.LengthsOk c → AgreesExcept step13ConeMask s0 st' → S13GuOk L s0 st' →
      FidConeInv F_cur L mvC st' nv.toNat (if ok = true then nc + 1#32 else nc).toNat →
      (ok = false → st'.scratch.scratch_buf = st.scratch.scratch_buf) →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (.call (as := [i64, i64, i32]) "full_k6_add_clause" (aHdr, aTmp, aSz, ()) k) m := by
  subst haSz
  refine wp_call_of_spec _ _ (hAddCl _ _ _ _ ?_)
  refine ⟨c, st, ConeModelSet F_cur st.scratch.work_stk1 nv.toNat, L,
    st.scratch.scratch_buf, st.scratch.glue_used, st.core.tmp, s13SweepAddRestTmpGlue c st ⋆ R,
    haHdr, hst, rfl, rfl, hLscr, hLmv, hcone.k6_inv, hcone.k6_sync, hcone.k6_lvl, hsz_le, hsz28,
    fun i hi => by rw [hcone.k6_nv]; have := hlts i hi; have := hcone.nv_le_mvC; omega,
    coneLift_semEntails hlts hent, hgu.2, ?_, ?_⟩
  · rw [haTmp]; exact sep_cast (s13_focus_addCl_tmp_glue hm) (by ac_rfl)
  intro ok scr' gu' m' ks0 ks' s_cl hst' hpref hgu' hwm' hinv' hsync' hlvl' hnv' hna' hassump
    hfalse hlen2 hbdd hm'
  let st' : FullState :=
    { st with scratch := { st.scratch with scratch_buf := scr', glue_used := gu' } }
  have hnc_add : (if ok = true then nc + 1#32 else nc).toNat ≤ L.maxOrig := by
    have hmax := L.hmaxV
    have hmo : L.maxOrig = 3 * L.maxV := rfl
    cases ok <;> simp
    · exact le_of_lt hnc_lt
    · have hwrap : nc.toNat + 1 < 2 ^ 32 := by omega
      rw [Nat.mod_eq_of_lt hwrap]
      omega
  have hag' : AgreesExcept step13ConeMask s0 st' := agreesExcept_trans hag rfl
  have hb_all := hbdd nv.toNat hlts hcone.k6_bdd hcone.k6_trl_bdd
  have hcone' : FidConeInv F_cur L mvC st' nv.toNat
      (if ok = true then nc + 1#32 else nc).toNat :=
    { nv_ge1 := hcone.nv_ge1
      nv_le_mvC := hcone.nv_le_mvC
      mvC_leMax := hcone.mvC_leMax
      nv_le_cv := hcone.nv_le_cv
      nc_le := hnc_add
      scr_len := by rw [hst'.scratch_ok.scratch_buf_len, hLscr]
      k6_inv := hinv'
      k6_sync := hsync'
      k6_nv := hnv'.trans hcone.k6_nv
      k6_lvl := hlvl'
      k6_na := hna'.trans hcone.k6_na
      k6_bdd := hb_all.1
      k6_trl_bdd := hb_all.2
      fwd := hcone.fwd
      rev := hcone.rev }
  rw [haTmp] at hm'
  have hm_out : (FullMem c st' ⋆ R) m' :=
    s13_unfocus_addCl_tmp_glue (sep_cast hm' (by ac_rfl))
  have hfalse_scr : ok = false → st'.scratch.scratch_buf = st.scratch.scratch_buf := fun hok =>
    scr_eq_of_k6_eq hcone.scr_len hcone'.scr_len hpref (hfalse hok)
  exact hk ok st' m' hst' hag' (s13GuOk_trans_step hgu hgu' hwm') hcone' hfalse_scr rfl rfl hm_out

private def P_hwm_mem (L : K6Layout) (pScr : BitVec 64) (hw : BitVec 32)
    (m₁ : Mem 64) : Prop :=
  hw = 0xFFFFFFFF#32 ∨ (hw.toNat ≤ L.maxV ∧ ∀ v, hw.toNat ≤ v → v < L.maxV →
    loadVal m₁ i32 (L.kPtr pScr + BitVec.ofNat 64 (4 * L.oLvl) +
      (BitVec.ofNat 32 v).setWidth 64 * 4) = some 0#32 ∧
    loadVal m₁ i32 (L.kPtr pScr + BitVec.ofNat 64 (4 * L.oRsn) +
      (BitVec.ofNat 32 v).setWidth 64 * 4) = some 0xFFFFFFFF#32 ∧
    loadVal m₁ i32 (L.kPtr pScr + BitVec.ofNat 64 (4 * L.oFlags) +
      (BitVec.ofNat 32 v).setWidth 64 * 4) = some 0#32 ∧
    loadVal m₁ i32 (L.kPtr pScr + BitVec.ofNat 64 (4 * L.oVals) +
      (BitVec.ofNat 32 (2 * v)).setWidth 64 * 4) = some 0#32 ∧
    loadVal m₁ i32 (L.kPtr pScr + BitVec.ofNat 64 (4 * L.oVals) +
      (BitVec.ofNat 32 (2 * v + 1)).setWidth 64 * 4) = some 0#32 ∧
    loadVal m₁ i32 (L.kPtr pScr + BitVec.ofNat 64 (4 * L.oWHead) +
      (BitVec.ofNat 32 (2 * v)).setWidth 64 * 4) = some 0xFFFFFFFF#32 ∧
    loadVal m₁ i32 (L.kPtr pScr + BitVec.ofNat 64 (4 * L.oWHead) +
      (BitVec.ofNat 32 (2 * v + 1)).setWidth 64 * 4) = some 0xFFFFFFFF#32)

private theorem P_hwm_mem_of_k6 {L : K6Layout} {pScr : BitVec 64} {hw : BitVec 32} {ks : K6State}
    {R1 : Mem 64 → Prop} {m₁ : Mem 64}
    (hwm : K6HwmClean L hw ks) (hm : (K6MemA L (L.kPtr pScr) ks ⋆ R1) m₁) :
    P_hwm_mem L pScr hw m₁ := by
  have hmax := L.hmaxV
  rcases hwm with rfl | ⟨hle, hall⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨hle, fun v hv1 hv2 => ?_⟩
    obtain ⟨hlv, hrs, hfl, hv0, hv1e, hw0, hw1⟩ := hall v hv1 hv2
    have hvn : (BitVec.ofNat 32 v).toNat = v := by simp; omega
    have hv20 : (BitVec.ofNat 32 (2 * v)).toNat = 2 * v := by simp; omega
    have hv21 : (BitVec.ofNat 32 (2 * v + 1)).toNat = 2 * v + 1 := by simp; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := K6MemATactics.load_k6_lvlArr (i := BitVec.ofNat 32 v)
        (by unfold K6MemATactics.szV; omega) hm
      rwa [hvn, hlv] at this
    · have := K6MemATactics.load_k6_rsn (i := BitVec.ofNat 32 v)
        (by unfold K6MemATactics.szV; omega) hm
      rwa [hvn, hrs] at this
    · have := K6MemATactics.load_k6_flags (i := BitVec.ofNat 32 v)
        (by unfold K6MemATactics.szV; omega) hm
      rwa [hvn, hfl] at this
    · have := K6MemATactics.load_k6_vals (i := BitVec.ofNat 32 (2 * v))
        (by unfold K6MemATactics.sz2V; omega) hm
      rwa [hv20, hv0] at this
    · have := K6MemATactics.load_k6_vals (i := BitVec.ofNat 32 (2 * v + 1))
        (by unfold K6MemATactics.sz2V; omega) hm
      rwa [hv21, hv1e] at this
    · have := K6MemATactics.load_k6_whead (i := BitVec.ofNat 32 (2 * v))
        (by unfold K6MemATactics.sz2V; omega) hm
      rwa [hv20, hw0] at this
    · have := K6MemATactics.load_k6_whead (i := BitVec.ofNat 32 (2 * v + 1))
        (by unfold K6MemATactics.sz2V; omega) hm
      rwa [hv21, hw1] at this

private theorem k6HwmClean_of_P_hwm {L : K6Layout} {pScr : BitVec 64} {hw : BitVec 32}
    {ks : K6State} {R1 : Mem 64 → Prop} {m₁ : Mem 64}
    (hp : P_hwm_mem L pScr hw m₁) (hm : (K6MemA L (L.kPtr pScr) ks ⋆ R1) m₁) :
    K6HwmClean L hw ks := by
  have hmax := L.hmaxV
  rcases hp with rfl | ⟨hle, hall⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨hle, fun v hv1 hv2 => ?_⟩
    obtain ⟨hlv, hrs, hfl, hv0, hv1e, hw0, hw1⟩ := hall v hv1 hv2
    have hvn : (BitVec.ofNat 32 v).toNat = v := by simp; omega
    have hv20 : (BitVec.ofNat 32 (2 * v)).toNat = 2 * v := by simp; omega
    have hv21 : (BitVec.ofNat 32 (2 * v + 1)).toNat = 2 * v + 1 := by simp; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h := (K6MemATactics.load_k6_lvlArr (i := BitVec.ofNat 32 v)
        (by unfold K6MemATactics.szV; omega) hm).symm.trans hlv
      rw [hvn] at h; exact Option.some.inj h
    · have h := (K6MemATactics.load_k6_rsn (i := BitVec.ofNat 32 v)
        (by unfold K6MemATactics.szV; omega) hm).symm.trans hrs
      rw [hvn] at h; exact Option.some.inj h
    · have h := (K6MemATactics.load_k6_flags (i := BitVec.ofNat 32 v)
        (by unfold K6MemATactics.szV; omega) hm).symm.trans hfl
      rw [hvn] at h; exact Option.some.inj h
    · have h := (K6MemATactics.load_k6_vals (i := BitVec.ofNat 32 (2 * v))
        (by unfold K6MemATactics.sz2V; omega) hm).symm.trans hv0
      rw [hv20] at h; exact Option.some.inj h
    · have h := (K6MemATactics.load_k6_vals (i := BitVec.ofNat 32 (2 * v + 1))
        (by unfold K6MemATactics.sz2V; omega) hm).symm.trans hv1e
      rw [hv21] at h; exact Option.some.inj h
    · have h := (K6MemATactics.load_k6_whead (i := BitVec.ofNat 32 (2 * v))
        (by unfold K6MemATactics.sz2V; omega) hm).symm.trans hw0
      rw [hv20] at h; exact Option.some.inj h
    · have h := (K6MemATactics.load_k6_whead (i := BitVec.ofNat 32 (2 * v + 1))
        (by unfold K6MemATactics.sz2V; omega) hm).symm.trans hw1
      rw [hv21] at h; exact Option.some.inj h

theorem step13_cone_exit_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {L : K6Layout} {mvC : BitVec 32} {s st_e : FullState} {R : Mem 64 → Prop}
    {Q : Post [i64]} {nv nc : BitVec 32} {m : Mem 64}
    (hinv : FullDenseInvW c F0 F_cur s) (hcap : k6MinScr ≤ c.scratch_cap)
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hlen : st_e.LengthsOk c) (hag : AgreesExcept step13ConeMask s st_e)
    (hgu : S13GuOk L s st_e) (hcone : FidConeInv F_cur L mvC st_e nv.toNat nc.toNat)
    (hm : (K6MemA L (L.kPtr c.pScratchBuf)
      (((((((k6StateOfScratch L st_e.scratch.scratch_buf).putHdr .nv nv).putHdr .unass
        (nv - (k6StateOfScratch L st_e.scratch.scratch_buf).trl_end)).putHdr .qlast
        (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr .qnext
        (nv.toNat - 1) 0xFFFFFFFF#32) ⋆ (FullK6Frame c L st_e ⋆ R)) m)
    (hQ : ∀ (r : BitVec 64) (tmp' ws1' tmk' scr' gu' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp' }
          scratch := { s.scratch with
            work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr', glue_used := gu' } }
      let nv' := (r &&& 0xFFFF#64).toNat
      let nc' := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.vals = s.core.vals →
      s'.core.inconsistent = s.core.inconsistent → M6SweepConeOk F_cur s' nv' →
      nc' ≤ 3 * k6MaxV c.scratch_cap → r.toNat = nv' + nc' * 2 ^ 16 →
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
      (∃ L' : K6Layout, L'.scrLen = c.scratch_cap ∧ L'.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L' (gu'[33]?.getD 0#32) (k6StateOfScratch L' scr')) →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nv', (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Q ((nv.setWidth 64 ||| nc.setWidth 64 <<< 16), ()) m := by
  let hw := st_e.scratch.glue_used[33]?.getD 0#32
  have hwm_new : K6HwmClean L hw
      (((((((k6StateOfScratch L st_e.scratch.scratch_buf).putHdr .nv nv).putHdr .unass
        (nv - (k6StateOfScratch L st_e.scratch.scratch_buf).trl_end)).putHdr .qlast
        (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr .qnext
        (nv.toNat - 1) 0xFFFFFFFF#32) :=
    k6HwmClean_putArr_qnext (k6HwmClean_putHdr_nv (k6HwmClean_putHdr_nv (k6HwmClean_putHdr_nv
      (k6HwmClean_putHdr_nv (k6HwmClean_putHdr_nv hgu.2)))))
  have hP_m : P_hwm_mem L c.pScratchBuf hw m := P_hwm_mem_of_k6 hwm_new hm
  have hinv_e := step13ConeMask_preserves_dense hag hlen hinv
  have hwrap := fid_cone_exit_post (Q := fun res m₁ => P_hwm_mem L c.pScratchBuf hw m₁ → Q res m₁)
    hinv_e hcap hLscr hLmv hlen (agreesExcept_refl fidConeMask st_e) hcone hm ?_
  · exact hwrap hP_m
  · intro r tmp' ws1' tmk' scr' m' s'_fid nv' nc' hfl' hvl' hic' hm6' hnc' hrn' hle' hr_eq htmk'
      hm'_mem hPm'
    have hst_eq := step13ConeMask_state_eq hag tmp' ws1' tmk' scr' st_e.scratch.glue_used
    have hc := step13ConeMask_core_eq hag
    have hscr_len : s'_fid.scratch.scratch_buf.length = L.scrLen := by
      change scr'.length = L.scrLen
      rw [hfl'.1.scratch_ok.scratch_buf_len, hLscr]
    have hka' : (K6MemA L (L.kPtr c.pScratchBuf) (k6StateOfScratch L scr') ⋆
        (FullK6Frame c L s'_fid ⋆ R)) m' := by
      have hm'_f := hm'_mem
      rw [fullMem_eq_k6Frame hscr_len] at hm'_f
      exact k6Mem_to_amem (K6State.shapesOk_ofSlab_eq (by
        rw [List.length_drop, hscr_len]; unfold K6Layout.scrLen; omega))
        (sep_cast hm'_f (by ac_rfl))
    have hhwm' : K6HwmClean L hw (k6StateOfScratch L scr') := k6HwmClean_of_P_hwm hPm' hka'
    change s'_fid = _ at hst_eq
    rw [hst_eq] at hfl' hrn' hm'_mem
    have hcv_eq : st_e.core.cur_vars = s.core.cur_vars := by rw [hc]
    rw [hcv_eq] at htmk'
    exact hQ r tmp' ws1' tmk' scr' st_e.scratch.glue_used m' hfl' rfl rfl rfl rfl hrn' hle'
      hr_eq hgu.1 ⟨L, hLscr, hLmv, hhwm'⟩ htmk' hm'_mem

theorem s13_upd_tmp {s st : FullState} (tmp' : List (BitVec 32))
    (hag : AgreesExcept step13ConeMask s st) :
    AgreesExcept step13ConeMask s { st with core := { st.core with tmp := tmp' } } :=
  hag.update (fun x => { x with core := { x.core with tmp := tmp' } }) fun _ => rfl

theorem bv32_ofNat_sub1 {n : Nat} (hn : n + 1 < 2 ^ 32) :
    BitVec.ofNat 32 (n + 1) - 1#32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
  have hle : (1#32 : BitVec 32) ≤ BitVec.ofNat 32 (n + 1) := by
    rw [BitVec.le_def, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega
  rw [BitVec.toNat_sub_of_le hle, h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]; omega

theorem fid_shl_256_props {p : BitVec 32} (hp : p.toNat ≤ 5) :
    (256#32 <<< (p.toNat % 32)).toNat = 256 * 2 ^ p.toNat ∧ 1 ≤ 256 * 2 ^ p.toNat := by
  have hpow : 2 ^ p.toNat ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hp
  rw [Nat.mod_eq_of_lt (by omega), BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    show (256#32 : BitVec 32).toNat = 256 from rfl,
    Nat.mod_eq_of_lt (by omega : 256 * 2 ^ p.toNat < 2 ^ 32)]
  exact ⟨rfl, by have := Nat.one_le_two_pow (n := p.toNat); omega⟩

theorem fid_shl_1024_eq {p : BitVec 32} (hp : p.toNat ≤ 5) :
    (1024#32 <<< (p.toNat % 32)).toNat = 1024 * 2 ^ p.toNat := by
  have hpow : 2 ^ p.toNat ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hp
  rw [Nat.mod_eq_of_lt (by omega), BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    show (1024#32 : BitVec 32).toNat = 1024 from rfl,
    Nat.mod_eq_of_lt (by omega : 1024 * 2 ^ p.toNat < 2 ^ 32)]

theorem s13_tmk_ov_at (st : FullState) (ov : BitVec 32)
    (hl : ov.toNat < st.scratch.tarjan_mark.length) :
    (BitVec.setWidth 64 ov).toNat = ov.toNat ∧
    st.scratch.tarjan_mark[ov.toNat]?.getD 0#32 =
      st.scratch.tarjan_mark[(BitVec.setWidth 64 ov).toNat] := by
  have h1 : (BitVec.setWidth 64 ov).toNat = ov.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ov.isLt (by decide))]
  refine ⟨h1, ?_⟩; simp only [h1, List.getElem?_eq_getElem hl, Option.getD_some]

theorem s13_vals_slt_zero_eq_255 {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {l : Nat}
    (hw : FullWitnessInv c F0 F_cur s.core) (hl : l < 2 * s.core.cur_vars)
    (hlt : (BitVec.signExtend 32 (s.core.vals[l]?.getD 0#8)).slt 0#32 = true) :
    s.core.vals[l]?.getD 0#8 = 255#8 := by
  rcases hw.vals_domain l hl with h0 | h1 | h255
  · rw [h0] at hlt; exact absurd hlt (by decide)
  · rw [h1] at hlt; exact absurd hlt (by decide)
  · exact h255

theorem s13_k6StateOfScratch_set25 (L : K6Layout) (scr : List (BitVec 32))
    (v : BitVec 32) (hlen : scr.length = L.scrLen) :
    let scr' := scr.set (L.k6Base + 25) v
    let ks := k6StateOfScratch L scr
    let ks' := k6StateOfScratch L scr'
    ks'.nv = ks.nv ∧ ks'.nc = ks.nc ∧ ks'.lvl = ks.lvl ∧
    ks'.trl_end = ks.trl_end ∧ ks'.nassump = ks.nassump ∧
    (K6TrailSynced ks → K6TrailSynced ks') ∧
    (∀ P, K6Inv L P ks → K6Inv L P ks') ∧
    (∀ hw, K6HwmClean L hw ks → K6HwmClean L hw ks') := by
  intro scr' ks ks'
  have hL := L.hmaxV; have hA := L.hacap
  have hscr_len : L.k6Base + 32 ≤ L.scrLen := by
    dsimp [K6Layout.k6Base, K6Layout.scrLen, K6Layout.oArena]; omega
  have hxs : List.drop L.k6Base scr' = (List.drop L.k6Base scr).set 25 v := by
    dsimp [scr']; rw [List.drop_set, ite_eq_right (by omega)]; simp
  have hget : ∀ i, i < 25 → (List.drop L.k6Base scr')[i]? = (List.drop L.k6Base scr)[i]? :=
    fun i hi => by rw [hxs, List.getElem?_set_ne (by omega)]
  have hdrop : ∀ k, 32 ≤ k →
      List.drop k (List.drop L.k6Base scr') = List.drop k (List.drop L.k6Base scr) :=
    fun k hk => by rw [hxs, List.drop_set, ite_eq_left (by omega)]
  have ⟨hnv, hnc, hlvl, hprop, htrl_end, hunass, hincons, hnassump, hacap, hmV,
      hmO, hmC, halen, hnkl, hnana, hlvlArr, hrsn, hqp, hqn, hqs, htrl, hfl, hana, hkl,
      hass, hvals, hwh, hwn, hwb, hco, hcs, har⟩ :
      ks'.nv = ks.nv ∧ ks'.nc = ks.nc ∧ ks'.lvl = ks.lvl ∧ ks'.prop = ks.prop ∧
      ks'.trl_end = ks.trl_end ∧ ks'.unass = ks.unass ∧ ks'.incons = ks.incons ∧
      ks'.nassump = ks.nassump ∧ ks'.acap = ks.acap ∧ ks'.max_v = ks.max_v ∧
      ks'.max_orig = ks.max_orig ∧ ks'.max_cl = ks.max_cl ∧ ks'.alen = ks.alen ∧
      ks'.nkl = ks.nkl ∧ ks'.nana = ks.nana ∧ ks'.lvlArr = ks.lvlArr ∧ ks'.rsn = ks.rsn ∧
      ks'.qprev = ks.qprev ∧ ks'.qnext = ks.qnext ∧ ks'.qstampArr = ks.qstampArr ∧
      ks'.trl = ks.trl ∧ ks'.flags = ks.flags ∧ ks'.ana = ks.ana ∧ ks'.kl = ks.kl ∧
      ks'.assump = ks.assump ∧ ks'.vals = ks.vals ∧ ks'.whead = ks.whead ∧
      ks'.wnext = ks.wnext ∧ ks'.wblit = ks.wblit ∧ ks'.clOff = ks.clOff ∧
      ks'.clSz = ks.clSz ∧ ks'.arena = ks.arena := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp [ks', ks, k6StateOfScratch, K6State.ofSlab] <;>
      first | (rw [hget _ (by decide)]) | (rw [hdrop _ (by
        dsimp [K6Layout.oLvl, K6Layout.oRsn, K6Layout.oQPrev, K6Layout.oQNext, K6Layout.oQStamp,
          K6Layout.oTrl, K6Layout.oFlags, K6Layout.oAna, K6Layout.oKl, K6Layout.oAssump,
          K6Layout.oVals, K6Layout.oWHead, K6Layout.oWNext, K6Layout.oWBlit, K6Layout.oClOff,
          K6Layout.oClSz, K6Layout.oArena]; omega)])
  have hht7 : ks'.hdrTail.length = 7 := by
    dsimp [ks', k6StateOfScratch, K6State.ofSlab]
    rw [List.length_take, List.length_drop, List.length_drop, List.length_set, hlen]; omega
  have hcl_sz : ∀ cid, k6ClauseSize ks' cid = k6ClauseSize ks cid :=
    fun c => by simp [k6ClauseSize, hcs]
  have hcl_off : ∀ cid, k6ClauseOff ks' cid = k6ClauseOff ks cid :=
    fun c => by simp [k6ClauseOff, hco]
  have hcl_lits : ∀ cid, k6ClauseLits ks' cid = k6ClauseLits ks cid := fun cid => by
    dsimp [k6ClauseLits]; rw [hcl_sz, hcl_off, har]
  have htrl_lits : k6TrailLits ks' = k6TrailLits ks := by simp [k6TrailLits, htrl_end, htrl]
  refine ⟨hnv, hnc, hlvl, htrl_end, hnassump,
    fun hts i hi => by rw [htrl_end] at hi; rw [htrl, hvals]; exact hts i hi,
    fun P ⟨hsh, hcl, hwa, has, hrs⟩ => ⟨⟨hht7, by rw [hlvlArr]; exact hsh.lvlArr_len,
      by rw [hrsn]; exact hsh.rsn_len, by rw [hqp]; exact hsh.qprev_len,
      by rw [hqn]; exact hsh.qnext_len, by rw [hqs]; exact hsh.qstampArr_len,
      by rw [htrl]; exact hsh.trl_len, by rw [hfl]; exact hsh.flags_len,
      by rw [hana]; exact hsh.ana_len, by rw [hkl]; exact hsh.kl_len,
      by rw [hass]; exact hsh.assump_len, by rw [hvals]; exact hsh.vals_len,
      by rw [hwh]; exact hsh.whead_len, by rw [hwn]; exact hsh.wnext_len,
      by rw [hwb]; exact hsh.wblit_len, by rw [hco]; exact hsh.clOff_len,
      by rw [hcs]; exact hsh.clSz_len, by rw [har]; exact hsh.arena_len⟩,
      ⟨by rw [hacap]; exact hcl.acap_eq, by rw [hmV]; exact hcl.max_v_eq,
        by rw [hmO]; exact hcl.max_orig_eq, by rw [hmC]; exact hcl.max_cl_eq,
        by rw [hnv]; exact hcl.nv_le, by rw [hnc]; exact hcl.nc_le,
        by rw [halen]; exact hcl.alen_le, by rw [hnassump]; exact hcl.nassump_le,
        by rw [hnkl]; exact hcl.nkl_le, by rw [hnana]; exact hcl.nana_le,
        fun cid hcid => by
          rw [hnc] at hcid; simpa [hcl_sz, hcl_off, hcl_lits, halen, hnv] using hcl.cl_wf cid hcid,
        fun c1 c2 hc1 hc2 => by
          rw [hnc] at hc2; simpa [hcl_off, hcl_sz] using hcl.cl_mono c1 c2 hc1 hc2,
        fun hi => by rw [hincons] at hi; exact hcl.incons_ok hi,
        fun i hi => by rw [hnassump] at hi; rw [hnv, hass]; exact hcl.assump_ok i hi,
        fun v hv => by rw [hnv] at hv; rw [hfl]; exact hcl.flags_clean v hv⟩,
      by simpa [K6WatchesOk, hnv, hwn, hwh, hnc, hcl_sz, har, hcl_off, hwb, hcl_lits] using hwa,
      ⟨by rw [htrl_end, hnv]; exact has.trl_end_le, by rw [hprop, htrl_end]; exact has.prop_le,
        by rw [hunass, htrl_end, hnv]; exact has.unass_eq,
        fun l hl => by rw [hnv] at hl; rw [hvals]; exact has.vals_dom l hl,
        fun l hl => by rw [hnv] at hl; rw [hvals]; exact has.vals_neg_iff l hl,
        fun l hl => by rw [hnv] at hl; rw [hvals, htrl_end, htrl]; exact has.vals_nz_iff_trl l hl,
        by rw [htrl_lits]; exact has.trl_nodup,
        fun l hl => by rw [htrl_lits] at hl; rw [hnv]; exact has.trl_lt l hl,
        fun v hv => by rw [hnv] at hv; rw [hlvlArr, hlvl]; exact has.trl_lvl_le v hv,
        fun v hv hz => by
          rw [hnv] at hv; rw [hvals] at hz; rw [hlvlArr, hrsn]; exact has.unass_lvl_zero v hv hz,
        fun i j hij hj => by
          rw [htrl_end] at hj; rw [hlvlArr, htrl]; exact has.trl_lvl_mono i j hij hj,
        fun i j hji hi hgt heql => by
          rw [htrl_end] at hi; rw [htrl] at hgt heql ⊢; rw [hlvlArr] at hgt heql; rw [hrsn]
          exact has.dec_earliest i j hji hi hgt heql,
        fun i hi => by rw [htrl_end] at hi; rw [hlvlArr, htrl, hvals]; exact has.lvl0_ok i hi⟩,
      fun i hi => by rw [htrl_end] at hi; simpa [htrl, hrsn, hnc, hcl_lits] using hrs i hi⟩,
    fun hw hc => by
      rcases hc with rfl | ⟨hle, hc⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hle, fun v h1 h2 => by
          simpa [hlvlArr, hrsn, hfl, hvals, hwh] using hc v h1 h2⟩⟩

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
