/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.LemmasCommon

/-!
# Cone Extraction Invariants & Transition Lemmas (`Proof.Sweep.LemmasCone`)

Non-legacy `CanonicalEnv` support for `full_m6_sweep_cone` (`Src.Sweep`):
- `step13ConeMask`, `S13GuOk` (upgraded with `2 ≤ nv → nv ≤ gu[33] ∨ gu[33] = 0xFFFFFFFF#32`),
  `FidConeInv`, `Step13ConeBase`, `Step13ConeSavedBase`, and `Step13ConeScanBase`.
- `s13_focus_addCl` / `s13_unfocus_addCl` and `step13_cone_call_add_clause` (via
  `step13K6AddClauseHwSpec`).
- Initialization (`step13_cone_init_ok`), push/pop rollback (`step13_cone_push_var_step_ok`,
  `step13_cone_pop_var_ok`), occurrence-scan step (`fid_cone_k_unassigned_step`,
  `s13_scan_tmp_step`, `s13_scan_skip_step`), `wvec` layout facts, and `step13_cone_exit_post`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
open FullArenaTactics
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. Mask, `S13GuOk`, & Cone Invariants -/

/-- State mask exposing the mutable cone fields (`tmp`, `work_stk1`, `tarjan_mark`,
`scratch_buf`, `glue_used`) while freezing all other solver fields. -/
@[expose] def step13ConeMask (s : FullState) : FullState :=
  { core := { s.core with tmp := [] }
    scratch :=
      { s.scratch with
        work_stk1 := []
        tarjan_mark := []
        scratch_buf := []
        glue_used := [] } }

theorem s13ConeMask_core_eq {s st : FullState} (h : AgreesExcept step13ConeMask s st) :
    st.core = { s.core with tmp := st.core.tmp } := by
  have hc : ({ st.core with tmp := [] } : FullCoreState) = { s.core with tmp := [] } :=
    congrArg FullState.core h
  cases h1 : st.core; cases h2 : s.core
  rw [h1, h2] at hc; cases hc; rfl

theorem s13_cur_vars_eq {s st : FullState} (h : AgreesExcept step13ConeMask s st) :
    st.core.cur_vars = s.core.cur_vars := by rw [s13ConeMask_core_eq h]

theorem s13_arena_eq {s st : FullState} (h : AgreesExcept step13ConeMask s st) :
    st.core.arena = s.core.arena := by rw [s13ConeMask_core_eq h]

theorem s13_arena_len_eq {s st : FullState} (h : AgreesExcept step13ConeMask s st) :
    st.core.arena_len = s.core.arena_len := by rw [s13ConeMask_core_eq h]

theorem s13_vals_eq {s st : FullState} (h : AgreesExcept step13ConeMask s st) :
    st.core.vals = s.core.vals := by rw [s13ConeMask_core_eq h]

theorem s13_wvec_eq {s st : FullState} (h : AgreesExcept step13ConeMask s st) :
    st.core.wvec = s.core.wvec := by rw [s13ConeMask_core_eq h]

theorem s13_wstk_eq {s st : FullState} (h : AgreesExcept step13ConeMask s st) :
    st.core.wstk = s.core.wstk := by rw [s13ConeMask_core_eq h]

theorem s13_upd_tmp {s st : FullState} (tmp' : List (BitVec 32))
    (h : AgreesExcept step13ConeMask s st) :
    AgreesExcept step13ConeMask s { st with core := { st.core with tmp := tmp' } } :=
  h.update (fun x => { x with core := { x.core with tmp := tmp' } }) fun _ => rfl

theorem s13_upd_tmk {s st : FullState} (tmk' : List (BitVec 32))
    (h : AgreesExcept step13ConeMask s st) :
    AgreesExcept step13ConeMask s { st with scratch := { st.scratch with tarjan_mark := tmk' } } :=
  h.update (fun x => { x with scratch := { x.scratch with tarjan_mark := tmk' } }) fun _ => rfl

theorem s13_upd_tmk_ws1 {s st : FullState} (tmk' ws1' : List (BitVec 32))
    (h : AgreesExcept step13ConeMask s st) :
    AgreesExcept step13ConeMask s
      { st with scratch := { st.scratch with tarjan_mark := tmk', work_stk1 := ws1' } } :=
  h.update
    (fun x => { x with scratch := { x.scratch with tarjan_mark := tmk', work_stk1 := ws1' } })
    fun _ => rfl

theorem s13ConeMask_preserves_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hag : AgreesExcept step13ConeMask s st)
    (hlen : st.LengthsOk c) (hdw : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur st := by
  have hc0 := s13ConeMask_core_eq hag
  generalize st.core.tmp = tmp' at hc0
  have hll : st.scratch.last_learned = s.scratch.last_learned := hag.get (·.scratch.last_learned)
  have hex : st.scratch.extend_len = s.scratch.extend_len := hag.get (·.scratch.extend_len)
  have hw_orig := hdw.2.1
  have hw' : FullWitnessInv c F0 F_cur { s.core with tmp := tmp' } :=
    { hw_orig with
      arena := { hw_orig.arena with len_ok := hw_orig.arena.len_ok }
      watches := hw_orig.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc0]; exact hw'
  · have hmc := hdw.2.2.1
    exact ⟨fun v hv => by simpa [hc0] using hmc.1 v hv,
      fun l hl => by simpa [hc0] using hmc.2 l hl⟩
  · have hnda := hdw.2.2.2.1; intro r hr hng
    dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits] at hr hng ⊢
    simp only [fullArenaClauseRefsCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore, hc0]
      at hr hng ⊢
    exact hnda r hr hng
  · refine ⟨fun i hi => ?_, by simpa [hex] using hdw.2.2.2.2.1.2⟩
    have h1 := hdw.2.2.2.2.1.1 i hi
    dsimp only at h1 ⊢; rw [hll, fullArenaClauseRefs, hc0]; exact h1
  · rw [hc0]; exact hdw.2.2.2.2.2.1
  · rw [hc0]; exact hdw.2.2.2.2.2.2

/-- High-water-mark cleanliness & `glue_used[33]` monotonicity relative to active cone size `nv`. -/
structure S13GuOk (L : K6Layout) (s0 : FullState) (nv : Nat)
    (st : FullState) : Prop where
  gu_other : ∀ i < 64, i ≠ 33 → st.scratch.glue_used[i]? = s0.scratch.glue_used[i]?
  hwm_clean : K6HwmClean L (st.scratch.glue_used[33]?.getD 0#32)
    (k6StateOfScratch L st.scratch.scratch_buf)
  hwm_ge : 2 ≤ nv →
    st.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
    nv ≤ (st.scratch.glue_used[33]?.getD 0#32).toNat

theorem s13GuOk_with_core_tmp {L : K6Layout} {s0 st : FullState} {nv : Nat}
    {tmp' : List (BitVec 32)} (h : S13GuOk L s0 nv st) :
    S13GuOk L s0 nv { st with core := { st.core with tmp := tmp' } } :=
  ⟨h.gu_other, h.hwm_clean, h.hwm_ge⟩

theorem s13GuOk_with_tmk_ws1 {L : K6Layout} {s0 st : FullState} {nv : Nat}
    {tmk' ws1' : List (BitVec 32)} (h : S13GuOk L s0 nv st) :
    S13GuOk L s0 nv
      { st with scratch := { st.scratch with tarjan_mark := tmk', work_stk1 := ws1' } } :=
  ⟨h.gu_other, h.hwm_clean, h.hwm_ge⟩

theorem S13GuOk.mono_le {L : K6Layout} {s0 st : FullState} {n1 n2 : Nat}
    (hle : n1 ≤ n2) (h : S13GuOk L s0 n2 st) : S13GuOk L s0 n1 st :=
  ⟨h.gu_other, h.hwm_clean, fun h2 => by
    rcases h.hwm_ge (by omega) with heq | hnv
    · exact Or.inl heq
    · exact Or.inr (by omega)⟩

/-- Core cone-extraction bijection and `K6` subsolver invariant at counts `(nv, nc)`. -/
structure FidConeInv (F_cur : List (List Nat)) (L : K6Layout) (mvC : BitVec 32)
    (st : FullState) (nv nc : Nat) : Prop where
  nv_ge1 : 1 ≤ nv
  nv_le_mvC : nv ≤ mvC.toNat
  mvC_leMax : mvC.toNat ≤ L.maxV
  nv_le_cv : nv ≤ st.core.cur_vars
  nc_le : nc ≤ L.maxOrig
  scr_len : st.scratch.scratch_buf.length = L.scrLen
  k6_inv : K6Inv L (ConeModelSet F_cur st.scratch.work_stk1 nv)
    (k6StateOfScratch L st.scratch.scratch_buf)
  k6_sync : K6TrailSynced (k6StateOfScratch L st.scratch.scratch_buf)
  k6_nv : (k6StateOfScratch L st.scratch.scratch_buf).nv = mvC
  k6_lvl : (k6StateOfScratch L st.scratch.scratch_buf).lvl = 0#32
  k6_na : (k6StateOfScratch L st.scratch.scratch_buf).nassump = 0#32
  k6_bdd : K6LitsBounded nv (k6StateOfScratch L st.scratch.scratch_buf)
  k6_trl_bdd : ∀ l ∈ k6TrailLits (k6StateOfScratch L st.scratch.scratch_buf), l < 2 * nv
  fwd : ∀ i < nv,
    (st.scratch.work_stk1[i]?.getD 0#32).toNat < st.core.cur_vars ∧
    st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32 =
      BitVec.ofNat 32 (i + 1)
  rev : ∀ v < st.core.cur_vars,
    st.scratch.tarjan_mark[v]?.getD 0#32 = 0#32 ∨
    ∃ i < nv, (st.scratch.work_stk1[i]?.getD 0#32).toNat = v ∧
      st.scratch.tarjan_mark[v]?.getD 0#32 = BitVec.ofNat 32 (i + 1)

theorem fidConeInv_tmp_irrel {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {st : FullState} {nv nc : Nat} {tmp' : List (BitVec 32)}
    (h : FidConeInv F_cur L mvC st nv nc) :
    FidConeInv F_cur L mvC { st with core := { st.core with tmp := tmp' } } nv nc :=
  ⟨h.nv_ge1, h.nv_le_mvC, h.mvC_leMax, h.nv_le_cv, h.nc_le, h.scr_len, h.k6_inv, h.k6_sync,
   h.k6_nv, h.k6_lvl, h.k6_na, h.k6_bdd, h.k6_trl_bdd, h.fwd, h.rev⟩

/-- Base invariant when processing active cone variable `cv = work_stk1[qi_l]`. -/
structure Step13ConeBase (F_cur : List (List Nat)) (L : K6Layout) (mvC : BitVec 32)
    (c : FullCfg) (s : FullState) (cv qi_l : BitVec 32) (nv nc : Nat)
    (st : FullState) : Prop where
  hlen : st.LengthsOk c
  hag : AgreesExcept step13ConeMask s st
  hgu : S13GuOk L s nv st
  hcone : FidConeInv F_cur L mvC st nv nc
  htmk : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1)
  hwk : (st.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat

/-- Rollback-aware base invariant extending from checkpoint `savedNv`, `(ws0, scr0)`. -/
structure Step13ConeSavedBase (F_cur : List (List Nat)) (L : K6Layout)
    (mvC : BitVec 32) (c : FullCfg) (s : FullState) (cv qi_l savedNv : BitVec 32)
    (ws0 scr0 : List (BitVec 32)) (nv nc : Nat) (st : FullState) : Prop where
  hlen : st.LengthsOk c
  hag : AgreesExcept step13ConeMask s st
  hgu_sav : S13GuOk L s savedNv.toNat st
  hcone : FidConeInv F_cur L mvC st nv nc
  htmk : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1)
  hwk : (st.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat
  hsav_le : savedNv.toNat ≤ nv
  hscr : st.scratch.scratch_buf = scr0
  hws : ∀ j < savedNv.toNat, st.scratch.work_stk1[j]? = ws0[j]?

theorem Step13ConeSavedBase.ofBase {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {nc : Nat} (hb : Step13ConeBase F_cur L mvC c s cv qi_l savedNv.toNat nc st) :
    Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv
      st.scratch.work_stk1 st.scratch.scratch_buf savedNv.toNat nc st :=
  ⟨hb.hlen, hb.hag, hb.hgu, hb.hcone, hb.htmk, hb.hwk, Nat.le_refl _, rfl, fun _ _ => rfl⟩

theorem Step13ConeSavedBase.toStep13ConeBase {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {nc : Nat}
    (hsb : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 savedNv.toNat nc st) :
    Step13ConeBase F_cur L mvC c s cv qi_l savedNv.toNat nc st :=
  ⟨hsb.hlen, hsb.hag, hsb.hgu_sav, hsb.hcone, hsb.htmk, hsb.hwk⟩

/-- Occurrence-clause literal scan invariant tracking `tmp[0 ..< cnt]` and new vars. -/
structure Step13ConeScanBase (F_cur : List (List Nat)) (L : K6Layout)
    (mvC : BitVec 32) (c : FullCfg) (s : FullState) (cv qi_l savedNv : BitVec 32)
    (ws0 scr0 : List (BitVec 32)) (cr : BitVec 32) (nv nc cnt idx : Nat)
    (st : FullState) : Prop where
  toStep13ConeSavedBase :
    Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv nc st
  hlts : ∀ j < cnt, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv
  hcov : ∀ i < idx,
    let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
    s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
    l ∈ (st.core.tmp.take cnt).map (fun x => m6ConeLift st.scratch.work_stk1 x.toNat)
  hvars : ∀ j < cnt, ∃ p < idx,
    (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 =
      (st.scratch.work_stk1[(st.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  hnd : ∀ j1 j2, j1 < cnt → j2 < cnt → j1 ≠ j2 →
    (st.core.tmp[j1]?.getD 0#32).toNat / 2 ≠ (st.core.tmp[j2]?.getD 0#32).toNat / 2
  hsav_vars : ∀ v, savedNv.toNat ≤ v → v < nv →
    ∃ i < cnt, (st.core.tmp[i]?.getD 0#32).toNat / 2 = v

theorem Step13ConeScanBase.hlen {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {cr : BitVec 32} {nv nc cnt idx : Nat}
    (h : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr nv nc cnt idx st) :
    st.LengthsOk c := h.toStep13ConeSavedBase.hlen

theorem Step13ConeScanBase.hag {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {cr : BitVec 32} {nv nc cnt idx : Nat}
    (h : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr nv nc cnt idx st) :
    AgreesExcept step13ConeMask s st := h.toStep13ConeSavedBase.hag

theorem Step13ConeScanBase.hgu_sav {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {cr : BitVec 32} {nv nc cnt idx : Nat}
    (h : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr nv nc cnt idx st) :
    S13GuOk L s savedNv.toNat st := h.toStep13ConeSavedBase.hgu_sav

theorem Step13ConeScanBase.hcone {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {cr : BitVec 32} {nv nc cnt idx : Nat}
    (h : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr nv nc cnt idx st) :
    FidConeInv F_cur L mvC st nv nc := h.toStep13ConeSavedBase.hcone

theorem Step13ConeScanBase.htmk {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {cr : BitVec 32} {nv nc cnt idx : Nat}
    (h : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr nv nc cnt idx st) :
    st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1) :=
  h.toStep13ConeSavedBase.htmk

theorem Step13ConeScanBase.hwk {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {cr : BitVec 32} {nv nc cnt idx : Nat}
    (h : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr nv nc cnt idx st) :
    (st.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat :=
  h.toStep13ConeSavedBase.hwk

theorem Step13ConeScanBase.hsav_le {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {cr : BitVec 32} {nv nc cnt idx : Nat}
    (h : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr nv nc cnt idx st) :
    savedNv.toNat ≤ nv := h.toStep13ConeSavedBase.hsav_le

theorem Step13ConeScanBase.hscr {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {cr : BitVec 32} {nv nc cnt idx : Nat}
    (h : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr nv nc cnt idx st) :
    st.scratch.scratch_buf = scr0 := h.toStep13ConeSavedBase.hscr

theorem Step13ConeScanBase.hws {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st : FullState} {cv qi_l savedNv : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {cr : BitVec 32} {nv nc cnt idx : Nat}
    (h : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr nv nc cnt idx st) :
    ∀ j < savedNv.toNat, st.scratch.work_stk1[j]? = ws0[j]? :=
  h.toStep13ConeSavedBase.hws

/-! ## 2. Pure Arithmetic, `tarjan_mark`, `vals`, & `wvec` Helpers -/

theorem bv32_ofNat_sub1 {n : Nat} (_hn : n + 1 < 2 ^ 32) :
    BitVec.ofNat 32 (n + 1) - 1#32 = BitVec.ofNat 32 n := by bv_omega

theorem s13_tmk_ov_at (st : FullState) (ov : BitVec 32)
    (hlt : ov.toNat < st.scratch.tarjan_mark.length) :
    (BitVec.setWidth 64 ov).toNat = ov.toNat ∧
      st.scratch.tarjan_mark[(BitVec.setWidth 64 ov).toNat] =
        st.scratch.tarjan_mark[ov.toNat]?.getD 0#32 := by
  have h1 : (BitVec.setWidth 64 ov).toNat = ov.toNat := by simp
  refine ⟨h1, ?_⟩
  have hq : st.scratch.tarjan_mark[(BitVec.setWidth 64 ov).toNat]? =
      st.scratch.tarjan_mark[ov.toNat]? := by rw [h1]
  rw [List.getElem?_eq_getElem (by rw [h1]; exact hlt), List.getElem?_eq_getElem hlt] at hq
  injection hq with heq; rw [heq, List.getElem?_eq_getElem hlt, Option.getD_some]

theorem s13_tmk_at (st : FullState) (lit_k : BitVec 32)
    (hltm : lit_k.toNat / 2 < st.scratch.tarjan_mark.length) :
    (lit_k >>> 1#32).toNat = lit_k.toNat / 2 ∧
      (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat = lit_k.toNat / 2 ∧
      st.scratch.tarjan_mark[(BitVec.setWidth 64 (lit_k >>> 1#32)).toNat] =
        st.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 := by
  have hv : (lit_k >>> 1#32).toNat = lit_k.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt64 : lit_k.toNat / 2 < 2 ^ 64 := by have := lit_k.isLt; omega
  have hv64 : (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat = lit_k.toNat / 2 := by
    rw [BitVec.toNat_setWidth, hv, Nat.mod_eq_of_lt hlt64]
  refine ⟨hv, hv64, ?_⟩
  have hq : st.scratch.tarjan_mark[(BitVec.setWidth 64 (lit_k >>> 1#32)).toNat]? =
      st.scratch.tarjan_mark[lit_k.toNat / 2]? := by rw [hv64]
  rw [List.getElem?_eq_getElem (by rw [hv64]; exact hltm), List.getElem?_eq_getElem hltm] at hq
  injection hq with heq; rw [heq, List.getElem?_eq_getElem hltm, Option.getD_some]

theorem s13_vals_slt_zero_eq_255 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) {l : Nat}
    (hlt : l < 2 * s.core.cur_vars) (hs : (s.core.vals[l]?.getD 0#8).slt 0#8 = true) :
    s.core.vals[l]?.getD 0#8 = 255#8 := by
  rcases hw.vals_domain l hlt with hv | hv | hv <;> simp [hv] at hs ⊢

theorem s13_sext8_255 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) {l : Nat}
    (hlt : l < 2 * s.core.cur_vars)
    (hsgt : (0#32).slt (BitVec.signExtend 32 (s.core.vals[l]?.getD 0#8)) = false)
    (hne0 : s.core.vals[l]?.getD 0#8 ≠ 0#8) :
    s.core.vals[l]?.getD 0#8 = 255#8 := by
  rcases hw.vals_domain l hlt with hv | hv | hv <;> simp [hv] at hsgt hne0 ⊢

theorem fid_cone_hp_wstk {s st : FullState} {p wEnd : BitVec 64}
    (hwstk : st.core.wstk = s.core.wstk) (hp : p.toNat < wEnd.toNat)
    (hend : wEnd.toNat ≤ s.core.wstk.length) : p.toNat < st.core.wstk.length := by
  rw [hwstk]; omega

theorem fid_cone_wstk_p_toNat_eq (p : BitVec 64) (hp : p.toNat < 2 ^ 63) :
    (p + 1#64).toNat = p.toNat + 1 :=
  m6_bv64_add1 hp

theorem fid_cone_sub_sub_eq (a b c : Nat) : a - b - c = a - (b + c) :=
  Nat.sub_sub a b c

theorem fid_cone_load_kptr_hdr {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {st : FullState} {nv nc : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hc : FidConeInv F_cur L mvC st nv nc) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 6 * 4) =
      some (k6StateOfScratch L st.scratch.scratch_buf).incons ∧
    loadVal m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 4 * 4) =
      some (k6StateOfScratch L st.scratch.scratch_buf).trl_end := by
  have hm1 := hm; rw [fullMem_eq_k6Frame hc.scr_len] at hm1
  have hm2 : (K6Mem L (L.kPtr c.pScratchBuf) (k6StateOfScratch L st.scratch.scratch_buf) ⋆
      (FullK6Frame c L st ⋆ R)) m := sep_ac hm1
  have ha := k6Mem_to_amem hc.k6_inv.shapes hm2
  exact ⟨K6MemATactics.load_k6_incons ha, K6MemATactics.load_k6_trl_end ha⟩

theorem step13_cone_wvec_facts {c : FullCfg} {F_cur : List (List Nat)}
    {s st_k : FullState} {lit : BitVec 32}
    (hlen_s : s.LengthsOk c) (hlen_k : st_k.LengthsOk c)
    (hag : AgreesExcept step13ConeMask s st_k)
    (hdw : DenseWatchesInv F_cur s.core) (hlit : lit.toNat < 2 * s.core.cur_vars) :
    let hcv := hlen_s.core_ok.cur_vars_le
    let hdb := c.hmaxv
    have hv0 : 2 * lit.toNat = (BitVec.setWidth 64 lit <<< 1).toNat := by
      have : 2 * lit.toNat < 2 ^ 64 := by unfold dimacsBound at hdb; omega
      simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega : lit.toNat * 2 < 2 ^ 64)]; omega
    have hv1 : 2 * lit.toNat + 1 = (BitVec.setWidth 64 lit <<< 1 + 1#64).toNat := by
      have _hbd : 2 * lit.toNat + 1 < 2 ^ 64 := by unfold dimacsBound at hdb; omega
      simp [BitVec.toNat_add, ← hv0, Nat.mod_eq_of_lt _hbd]
    have hi0 : (BitVec.setWidth 64 lit <<< 1).toNat < st_k.core.wvec.length := by
      rw [← hv0, hlen_k.core_ok.wvec_len]; omega
    have hi1 : (BitVec.setWidth 64 lit <<< 1 + 1#64).toNat < st_k.core.wvec.length := by
      rw [← hv1, hlen_k.core_ok.wvec_len]; omega
    let wOff := BitVec.setWidth 64 (st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'hi0)
    let wSz := BitVec.setWidth 64 (st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat]'hi1)
    let wEnd := wOff + wSz
    wOff.toNat = (s.core.wvec[2 * lit.toNat]?.getD 0#32).toNat ∧
    wSz.toNat = (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).toNat ∧
    wEnd.toNat = (s.core.wvec[2 * lit.toNat]?.getD 0#32).toNat +
      (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).toNat ∧
    wOff.toNat ≤ wEnd.toNat ∧
    wEnd.toNat - wOff.toNat = (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).toNat ∧
    wEnd.toNat ≤ s.core.wstk.length ∧
    2 * lit.toNat = (BitVec.setWidth 64 lit <<< 1).toNat ∧
    2 * lit.toNat + 1 = (BitVec.setWidth 64 lit <<< 1 + 1#64).toNat := by
  have hcv := hlen_s.core_ok.cur_vars_le; have hdb := c.hmaxv
  have hv0 : 2 * lit.toNat = (BitVec.setWidth 64 lit <<< 1).toNat := by
    have hbd : 2 * lit.toNat < 2 ^ 64 := by unfold dimacsBound at hdb; omega
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : lit.toNat * 2 < 2 ^ 64)]; omega
  have hv1 : 2 * lit.toNat + 1 = (BitVec.setWidth 64 lit <<< 1 + 1#64).toNat := by
    have hbd : 2 * lit.toNat + 1 < 2 ^ 64 := by unfold dimacsBound at hdb; omega
    simp [BitVec.toNat_add, ← hv0, Nat.mod_eq_of_lt hbd]
  have hi0 : (BitVec.setWidth 64 lit <<< 1).toNat < st_k.core.wvec.length := by
    rw [← hv0, hlen_k.core_ok.wvec_len]; omega
  have hi1 : (BitVec.setWidth 64 lit <<< 1 + 1#64).toNat < st_k.core.wvec.length := by
    rw [← hv1, hlen_k.core_ok.wvec_len]; omega
  have hwvec_eq := s13_wvec_eq hag
  have hs0_lt : 2 * lit.toNat < s.core.wvec.length := by rw [← hwvec_eq, hv0]; exact hi0
  have hs1_lt : 2 * lit.toNat + 1 < s.core.wvec.length := by rw [← hwvec_eq, hv1]; exact hi1
  have hw0 : (BitVec.setWidth 64 (st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'hi0)).toNat =
      (s.core.wvec[2 * lit.toNat]?.getD 0#32).toNat := by
    have hq :
        st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]? =
        s.core.wvec[2 * lit.toNat]? := by
      rw [hwvec_eq, hv0]
    rw [List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hs0_lt] at hq
    rw [BitVec.toNat_setWidth, List.getElem?_eq_getElem hs0_lt, Option.getD_some]
    injection hq with heq
    have h32 : (s.core.wvec[2 * lit.toNat]'hs0_lt).toNat < 2 ^ 64 :=
      Nat.lt_trans (BitVec.isLt _) (by decide)
    rw [heq, Nat.mod_eq_of_lt h32]
  have hw1 :
      (BitVec.setWidth 64 (st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat]'hi1)).toNat =
        (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).toNat := by
    have hq : st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat]? =
        s.core.wvec[2 * lit.toNat + 1]? := by rw [hwvec_eq, hv1]
    rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hs1_lt] at hq
    rw [BitVec.toNat_setWidth, List.getElem?_eq_getElem hs1_lt, Option.getD_some]
    injection hq with heq
    have h32 : (s.core.wvec[2 * lit.toNat + 1]'hs1_lt).toNat < 2 ^ 64 :=
      Nat.lt_trans (BitVec.isLt _) (by decide)
    rw [heq, Nat.mod_eq_of_lt h32]
  have hend : (BitVec.setWidth 64 (st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'hi0) +
      BitVec.setWidth 64 (st_k.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat]'hi1)).toNat =
      (s.core.wvec[2 * lit.toNat]?.getD 0#32).toNat +
      (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).toNat := by
    have h0_32 : (s.core.wvec[2 * lit.toNat]?.getD 0#32).toNat < 2 ^ 32 := BitVec.isLt _
    have h1_32 : (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).toNat < 2 ^ 32 := BitVec.isLt _
    rw [BitVec.toNat_add, hw0, hw1, Nat.mod_eq_of_lt (by omega)]
  have hbd_layout := hdw.layout.bounds lit.toNat hlit
  have hwl := hlen_s.core_ok.wlen_le
  have hws := hlen_s.core_ok.wstk_len_arr
  dsimp only [fullWatchOffCore, fullWatchSizeCore] at hbd_layout
  refine ⟨hw0, hw1, hend, by omega, by omega, by omega, hv0, hv1⟩

theorem m6_cone_cnt_le_nv {tmp : List (BitVec 32)} {cnt nv : Nat}
    (hlts : ∀ j < cnt, (tmp[j]?.getD 0#32).toNat < 2 * nv)
    (hnd : ∀ j1 j2, j1 < cnt → j2 < cnt → j1 ≠ j2 →
      (tmp[j1]?.getD 0#32).toNat / 2 ≠ (tmp[j2]?.getD 0#32).toNat / 2) :
    cnt ≤ nv := by
  let xs := (List.range cnt).map fun j => (tmp[j]?.getD 0#32).toNat / 2
  have hnd_xs : xs.Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
    simp only [xs, List.length_map, List.length_range] at hi hj
    simp only [xs, List.getElem_map, List.getElem_range]
    exact hnd i j hi hj (Nat.ne_of_lt hij)
  have hle := k6_nodup_subset_length (n := nv) hnd_xs fun v hv => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range] at hj; have := hlts j hj; omega
  simpa [xs] using hle

theorem m6_cone_unit_tmp_prep {c : FullCfg} {F_cur : List (List Nat)}
    {st : FullState} {nv qi0 pol u : BitVec 32} {litN : Nat}
    (hlen : st.LengthsOk c) (htmp0 : 0 < st.core.tmp.length)
    (hqi : qi0.toNat < nv.toNat) (_hnv_lt31 : nv.toNat < 2 ^ 31)
    (hpol : pol.toNat < 2)
    (hu_eq : u.toNat = 2 * qi0.toNat + pol.toNat)
    (hlit_eq : 2 * (st.scratch.work_stk1[qi0.toNat]?.getD 0#32).toNat + pol.toNat = litN)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [litN])) :
    let st' : FullState := { st with core := { st.core with tmp := st.core.tmp.set 0 u } }
    st'.LengthsOk c ∧
    (∀ j < 1, (st'.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st'.core.tmp.take 1).map (fun x => m6ConeLift st'.scratch.work_stk1 x.toNat))) := by
  intro st'
  have htm := hlen.core_ok.tmp_len_arr
  refine ⟨⟨{ hlen.core_ok with tmp_len_arr := by simp [st', htm] }, hlen.scratch_ok⟩,
    fun j hj => ?_, ?_⟩
  · have hj0 : j = 0 := by omega
    subst hj0; dsimp only [st']
    rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
  · have htk : st'.core.tmp.take 1 = [u] := by
      dsimp only [st']
      cases ht : st.core.tmp with
      | nil => simp [ht] at htmp0
      | cons _ _ => simp
    have hlift : m6ConeLift st.scratch.work_stk1 u.toNat = litN := by
      rw [hu_eq, show pol.toNat = litN % 2 by omega]
      exact coneLift_of_tmk_pair rfl (by omega)
    rw [htk]; simpa only [List.map_cons, List.map_nil, st', hlift] using hent

theorem m6_entails_singleton_of_dup {F : CNF Nat} {l : Nat}
    (h : F.EntailsClause (cnfClause [l, l])) : F.EntailsClause (cnfClause [l]) :=
  m6_entails_unit_of_dup h

theorem m6_entails_fst_of_snd_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l0 l1 : Nat} (hl1 : l1 < 2 * k.cur_vars) (hf1 : k.vals[l1]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0, l1])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l0]) := by
  rw [CNF.entails_clause_def] at hent ⊢
  intro α hα
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff α [l0, l1]).mp (hent α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hxl0 | hxl1
  · rw [hxl0] at hxs; exact (clause_sat_cnfClause_iff α [l0]).mpr ⟨l0, List.mem_cons_self, hxs⟩
  · rw [hxl1] at hxs
    exact absurd ((sat_cnfClause_singleton α l1).mpr hxs)
      (m6_lvl0_false_not_sat hw hcl0 hl1 hf1 hα)

/-! ## 3. `K6` Memory Focusing & `full_k6_add_clause` Bridge (`step13K6AddClauseHwSpec`) -/

/-- Rest of `FullMem` when exposing `hdrTail`, `scratch_buf`, `glue_used`, and `tmp`. -/
@[expose] def s13SweepAddRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
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
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ c.pad

theorem s13_focus_addCl {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆ (s13SweepAddRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrMetaArrs
    FullScrDynArrs at hm
  unfold s13SweepAddRest; ecancel

theorem s13_unfocus_addCl {c : FullCfg} {s : FullState} {scr' gu' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 (c.hdr + 32) (hdrTailWords c
        { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }) ⋆
      array (t := i32) c.pScratchBuf scr' ⋆
      array (t := i32) c.pGlueUsed gu' ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆ (s13SweepAddRest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } } ⋆ R)
      m := by
  let sc' : FullScratch := { s.scratch with scratch_buf := scr', glue_used := gu' }
  change (array64 (c.hdr + 32) (hdrTailWords c { core := s.core, scratch := sc' }) ⋆
    array (t := i32) c.pScratchBuf scr' ⋆
    array (t := i32) c.pGlueUsed gu' ⋆
    array (t := i32) c.pTmp s.core.tmp ⋆ (s13SweepAddRest c s ⋆ R)) m at hm
  have hSB : FullScrByteArrs c sc' = FullScrByteArrs c s.scratch := rfl
  have hSA : FullScrU32A c sc' = FullScrU32A c s.scratch := rfl
  have hSW : FullScrWksArrs c sc' = FullScrWksArrs c s.scratch := rfl
  have hsc : sc'.score = s.scratch.score := rfl
  have hss : sc'.sim_sig = s.scratch.sim_sig := rfl
  have hsl : sc'.last_learned = s.scratch.last_learned := rfl
  have hgu : sc'.glue_used = gu' := rfl
  have hd : sc'.delayed = s.scratch.delayed := rfl
  have hr : sc'.red_refs = s.scratch.red_refs := rfl
  have he : sc'.extend_stk = s.scratch.extend_stk := rfl
  have hsb : sc'.scratch_buf = scr' := rfl
  change (FullMem c { s with scratch := sc' } ⋆ R) m
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrMetaArrs
    FullScrDynArrs
  unfold s13SweepAddRest at hm
  rw [hSB, hSA, hSW, hsc, hss, hsl, hgu, hd, hr, he, hsb]
  ecancel

private theorem s13_addCl_gu_ok {L : K6Layout} {s0 st : FullState}
    {savedNv nv sz : BitVec 32} {scr' gu' : List (BitVec 32)}
    (hsav_le : savedNv.toNat ≤ nv.toNat)
    (hgu_sav : S13GuOk L s0 savedNv.toNat st)
    (hnew_in_tmp : savedNv.toNat < nv.toNat →
      ∃ i < sz.toNat, (st.core.tmp[i]?.getD 0#32).toNat / 2 + 1 = nv.toNat)
    (hgu_other : ∀ i < 64, i ≠ 33 → gu'[i]? = st.scratch.glue_used[i]?)
    (hclean' : K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr'))
    (hhw_mon : (st.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∧ gu'[33]? = some 0xFFFFFFFF#32) ∨
      (st.scratch.glue_used[33]? ≠ some 0xFFFFFFFF#32 ∧ gu'[33]? ≠ some 0xFFFFFFFF#32 ∧
       (st.scratch.glue_used[33]?.getD 0#32).toNat ≤ (gu'[33]?.getD 0#32).toNat ∧
       (gu'[33]?.getD 0#32).toNat ≤ L.maxV ∧
       ∀ i < sz.toNat, (st.core.tmp[i]?.getD 0#32).toNat / 2 + 1 ≤ (gu'[33]?.getD 0#32).toNat)) :
    let st' : FullState :=
      { st with scratch := { st.scratch with scratch_buf := scr', glue_used := gu' } }
    S13GuOk L s0 savedNv.toNat st' ∧ S13GuOk L s0 nv.toNat st' := by
  intro st'
  have hoth : ∀ i < 64, i ≠ 33 → st'.scratch.glue_used[i]? = s0.scratch.glue_used[i]? :=
    fun i hi h33 => (hgu_other i hi h33).trans (hgu_sav.gu_other i hi h33)
  have hcl : K6HwmClean L (st'.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L st'.scratch.scratch_buf) := hclean'
  have hge_sav : 2 ≤ savedNv.toNat →
      st'.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
      savedNv.toNat ≤ (st'.scratch.glue_used[33]?.getD 0#32).toNat := by
    intro h2
    rcases hgu_sav.hwm_ge h2 with hff | hle
    · rcases hhw_mon with ⟨_, hff'⟩ | ⟨hne, _⟩
      · exact Or.inl hff'
      · exact absurd hff hne
    · rcases hhw_mon with ⟨_, hff'⟩ | ⟨_, _, hmon, _⟩
      · exact Or.inl hff'
      · exact Or.inr (Nat.le_trans hle hmon)
  refine ⟨⟨hoth, hcl, hge_sav⟩, ⟨hoth, hcl, fun h2 => ?_⟩⟩
  rcases Nat.lt_or_eq_of_le hsav_le with hlt | heq
  · obtain ⟨i, hi, hid⟩ := hnew_in_tmp hlt
    rcases hhw_mon with ⟨_, hff'⟩ | ⟨_, _, _, _, hxs⟩
    · exact Or.inl hff'
    · exact Or.inr (by rw [← hid]; exact hxs i hi)
  · rw [← heq]; exact hge_sav (by omega)

theorem step13_cone_call_add_clause {Γ : Env}
    (hAddCl : Γ.Has "full_k6_add_clause" step13K6AddClauseHwSpec)
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s0 st : FullState} {savedNv nv nc sz : BitVec 32} {aSz : Arg Val i32}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont [i64]}
    (haSz : aSz.val = sz) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hlen : st.LengthsOk c) (hag : AgreesExcept step13ConeMask s0 st)
    (hsav_le : savedNv.toNat ≤ nv.toNat) (hgu_sav : S13GuOk L s0 savedNv.toNat st)
    (hnew_in_tmp : savedNv.toNat < nv.toNat →
      ∃ i < sz.toNat, (st.core.tmp[i]?.getD 0#32).toNat / 2 + 1 = nv.toNat)
    (hcone : FidConeInv F_cur L mvC st nv.toNat nc.toNat)
    (hnc : nc.toNat < L.maxOrig) (hsz28 : sz.toNat < 2 ^ 28)
    (hsz_tmp : sz.toNat ≤ st.core.tmp.length)
    (hlts : ∀ j < sz.toNat, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st.core.tmp.take sz.toNat).map (fun x => m6ConeLift st.scratch.work_stk1 x.toNat))))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (ok : Bool) (st' : FullState) (m' : Mem 64),
      st'.LengthsOk c → AgreesExcept step13ConeMask s0 st' →
      S13GuOk L s0 savedNv.toNat st' →
      (ok = true → S13GuOk L s0 nv.toNat st') →
      FidConeInv F_cur L mvC st' nv.toNat (if ok then nc + 1#32 else nc).toNat →
      (ok = false → st'.scratch.scratch_buf = st.scratch.scratch_buf) →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i32]) (bs := [.bool])
      "full_k6_add_clause" (Arg.var c.hdr, Arg.var c.pTmp, aSz, ()) k) m := by
  have hm_L := L.hmaxV; have hnv_mvC := hcone.nv_le_mvC; have hmvC_L := hcone.mvC_leMax
  have hnv_le : nv.toNat ≤ L.maxV := Nat.le_trans hnv_mvC hmvC_L
  have hlts_ks : ∀ j < sz.toNat,
      (st.core.tmp[j]?.getD 0#32).toNat <
        2 * (k6StateOfScratch L st.scratch.scratch_buf).nv.toNat := fun j hj => by
    rw [hcone.k6_nv]; have := hlts j hj; omega
  have hsem : SemEntails (ConeModelSet F_cur st.scratch.work_stk1 nv.toNat)
      ((st.core.tmp.take sz.toNat).map BitVec.toNat) := by
    refine semEntails_coneModelSet_of_entails (fun l hl => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      have hjl : j < sz.toNat := by rw [List.length_take] at hj; omega
      have hxj := hlts j hjl
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hxj
      rwa [List.getElem_take]
    · simp only [List.map_map]; simpa [Function.comp_def] using hent
  refine wp_call_of_spec _ k ?_
  dsimp only [vals]; rw [Arg.val_var, haSz]
  refine hAddCl (c.hdr, c.pTmp, sz, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, st, ConeModelSet F_cur st.scratch.work_stk1 nv.toNat, L, st.scratch.scratch_buf,
      st.scratch.glue_used, st.core.tmp, s13SweepAddRest c st ⋆ R,
      rfl, hlen, rfl, rfl, hL_len, hL_mv, hcone.k6_inv, hcone.k6_sync, hcone.k6_lvl,
      hsz_tmp, hsz28, hlts_ks, hsem, hgu_sav.hwm_clean, s13_focus_addCl hm,
      fun ok scr' gu' m' hlen' hpre hgu_oth hclean' hK' hsy' hlvl' hnv' hna' _
        hfalse _ hbdd' hhw_mon hm' => ?_⟩
  let st' : FullState :=
    { st with scratch := { st.scratch with scratch_buf := scr', glue_used := gu' } }
  have hsl : scr'.length = c.scratch_cap := hlen'.scratch_ok.scratch_buf_len
  have hag' : AgreesExcept step13ConeMask s0 st' := hag.update _ (fun _ => rfl)
  obtain ⟨hgu_sav', hgu_nv'⟩ :=
    s13_addCl_gu_ok hsav_le hgu_sav hnew_in_tmp hgu_oth hclean' hhw_mon
  have hm_un := s13_unfocus_addCl hm'
  obtain ⟨hbdd_nv, htrl_nv⟩ := hbdd' nv.toNat hlts hcone.k6_bdd hcone.k6_trl_bdd
  have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := by unfold K6Layout.maxOrig at hnc; bv_omega
  have hscr_false : ok = false → st'.scratch.scratch_buf = st.scratch.scratch_buf := fun hok => by
    have hks_eq := hfalse hok
    have hscr_L : st.scratch.scratch_buf.length = L.scrLen := hcone.scr_len
    have hscr'_L : scr'.length = L.scrLen := hsl.trans hL_len.symm
    have hkb_le : L.k6Base ≤ st.scratch.scratch_buf.length := by
      rw [hscr_L]; unfold K6Layout.scrLen; omega
    have hkb_le' : L.k6Base ≤ scr'.length := by rw [hscr'_L]; unfold K6Layout.scrLen; omega
    have hfix0 : L.k6Fixed ≤ (st.scratch.scratch_buf.drop L.k6Base).length := by
      rw [List.length_drop, hscr_L]; unfold K6Layout.scrLen; omega
    have hfix' : L.k6Fixed ≤ (scr'.drop L.k6Base).length := by
      rw [List.length_drop, hscr'_L]; unfold K6Layout.scrLen; omega
    have htk_eq : scr'.take L.k6Base = st.scratch.scratch_buf.take L.k6Base := by
      apply List.ext_getElem
      · rw [List.length_take_of_le hkb_le', List.length_take_of_le hkb_le]
      · intro i hi1 _
        have hi : i < L.k6Base := by rw [List.length_take_of_le hkb_le'] at hi1; exact hi1
        rw [List.getElem_take, List.getElem_take]
        exact Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by omega), ← List.getElem?_eq_getElem (by omega)]
          exact hpre i hi)
    have hdrop_eq : scr'.drop L.k6Base = st.scratch.scratch_buf.drop L.k6Base := by
      rw [← K6State.toSlab_ofSlab hfix', ← K6State.toSlab_ofSlab hfix0]
      exact congrArg K6State.toSlab hks_eq
    dsimp only [st']
    rw [← List.take_append_drop L.k6Base scr', htk_eq, hdrop_eq, List.take_append_drop]
  cases ok
  · exact hk false st' m' hlen' hag' hgu_sav' (fun h => by cases h)
      { hcone with scr_len := hsl.trans hL_len.symm, k6_inv := hK', k6_sync := hsy',
                   k6_nv := hnv'.trans hcone.k6_nv, k6_lvl := hlvl',
                   k6_na := hna'.trans hcone.k6_na, k6_bdd := hbdd_nv, k6_trl_bdd := htrl_nv }
      hscr_false rfl rfl hm_un
  · exact hk true st' m' hlen' hag' hgu_sav' (fun _ => hgu_nv')
      { hcone with nc_le := by simp only [↓reduceIte, hnc1]; omega,
                   scr_len := hsl.trans hL_len.symm, k6_inv := hK', k6_sync := hsy',
                   k6_nv := hnv'.trans hcone.k6_nv, k6_lvl := hlvl',
                   k6_na := hna'.trans hcone.k6_na, k6_bdd := hbdd_nv, k6_trl_bdd := htrl_nv }
      hscr_false rfl rfl hm_un

/-! ## 4. Push, Pop, Occurrence Scan, Init, & Exit Transitions -/

private theorem coneModelSet_push_var {F_cur : List (List Nat)} {ws : List (BitVec 32)}
    {nv : Nat} {v : BitVec 32} (β : Nat → Bool)
    (h : ConeModelSet F_cur (ws.set nv v) (nv + 1) β) :
    ConeModelSet F_cur ws nv β := by
  rcases h with ⟨α, hα, hβ⟩
  refine ⟨α, hα, fun i hi => ?_⟩
  have h1 := hβ i (by omega)
  rwa [List.getElem?_set_ne (by omega)] at h1

private theorem fidConeInv_push_var {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s : FullState} {nv nc : Nat} {ov : BitVec 32}
    (hlen : s.LengthsOk c) (hcone : FidConeInv F_cur L mvC s nv nc)
    (hnv_lt : nv < mvC.toNat) (hov : ov.toNat < s.core.cur_vars)
    (hmiss : s.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0#32) :
    nv < s.core.cur_vars ∧
    let s' : FullState :=
      { s with scratch :=
        { s.scratch with
          tarjan_mark := s.scratch.tarjan_mark.set ov.toNat (BitVec.ofNat 32 (nv + 1))
          work_stk1 := s.scratch.work_stk1.set nv ov } }
    FidConeInv F_cur L mvC s' (nv + 1) nc := by
  have hm := L.hmaxV
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len
  have htm_len := hlen.scratch_ok.tarjan_mark_len
  have hmvC_le := hcone.mvC_leMax
  have hne_ov : ∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ ov.toNat := fun i hi heq => by
    have hti := (hcone.fwd i hi).2; rw [heq, hmiss] at hti
    have htn := congrArg BitVec.toNat hti
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32)] at htn; omega
  have hnv_lt_cv : nv < s.core.cur_vars :=
    m6_inj_lt_of_missing (fun i => (s.scratch.work_stk1[i]?.getD 0#32).toNat)
      (fun i j hi hj heq => by
        have hti := (hcone.fwd i hi).2; have htj := (hcone.fwd j hj).2
        rw [heq] at hti
        have htn := congrArg BitVec.toNat (hti.symm.trans htj)
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)] at htn; omega)
      (fun i hi => (hcone.fwd i hi).1) hov hne_ov
  refine ⟨hnv_lt_cv, ?_⟩
  intro s'
  have hwk_lt : ∀ i < nv, s'.scratch.work_stk1[i]? = s.scratch.work_stk1[i]? := fun i hi =>
    List.getElem?_set_ne (by omega)
  have hwk_nv : s'.scratch.work_stk1[nv]? = some ov := List.getElem?_set_self (by omega)
  exact
    { nv_ge1 := by omega
      nv_le_mvC := by omega
      mvC_leMax := hcone.mvC_leMax
      nv_le_cv := by dsimp [s']; omega
      nc_le := hcone.nc_le
      scr_len := hcone.scr_len
      k6_inv := hcone.k6_inv.mono_P (fun β hβ => coneModelSet_push_var β hβ)
      k6_sync := hcone.k6_sync
      k6_nv := hcone.k6_nv
      k6_lvl := hcone.k6_lvl
      k6_na := hcone.k6_na
      k6_bdd := ⟨fun cid hcid l hl => Nat.lt_trans (hcone.k6_bdd.1 cid hcid l hl) (by omega),
                 fun w hw => Nat.lt_trans (hcone.k6_bdd.2 w hw) (by omega)⟩
      k6_trl_bdd := fun l hl => Nat.lt_trans (hcone.k6_trl_bdd l hl) (by omega)
      fwd := fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [hwk_lt i hi']
          have hne := hne_ov i hi'
          refine ⟨(hcone.fwd i hi').1, ?_⟩
          dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hne)]; exact (hcone.fwd i hi').2
        · rw [hwk_nv, Option.getD_some]
          refine ⟨hov, ?_⟩
          dsimp only [s']; rw [List.getElem?_set_self (by omega), Option.getD_some]
      rev := fun v hv => by
        dsimp only [s']
        by_cases hvo : v = ov.toNat
        · subst hvo; right; refine ⟨nv, by omega, ?_, ?_⟩
          · rw [hwk_nv, Option.getD_some]
          · rw [List.getElem?_set_self (by omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm hvo)]
          rcases hcone.rev v hv with hz | ⟨i, hi, hwi, hti⟩
          · exact Or.inl hz
          · exact Or.inr ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hwi, hti⟩ }

theorem step13_cone_push_var_step_ok {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st_k : FullState} {ws0 scr0 : List (BitVec 32)}
    {cv qi_l savedNv nv_k ov : BitVec 32} {nc_w : Nat}
    (hsb : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv_k.toNat nc_w st_k)
    (hnv_lt : nv_k.toNat < mvC.toNat) (hov : ov.toNat < s.core.cur_vars)
    (hmiss : st_k.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0#32)
    (hqi_lt : qi_l.toNat < nv_k.toNat) :
    let st_push : FullState :=
      { core := st_k.core
        scratch :=
          { st_k.scratch with
            work_stk1 := st_k.scratch.work_stk1.set nv_k.toNat ov
            tarjan_mark := st_k.scratch.tarjan_mark.set ov.toNat (nv_k + 1#32) } }
    nv_k.toNat < st_k.core.cur_vars ∧
    (nv_k + 1#32).toNat = nv_k.toNat + 1 ∧
    st_push.LengthsOk c ∧ AgreesExcept step13ConeMask s st_push ∧
    Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0
      (nv_k + 1#32).toNat nc_w st_push ∧
    (st_push.scratch.work_stk1[nv_k.toNat]?.getD 0#32).toNat = ov.toNat := by
  intro st_push
  have hm := L.hmaxV; have hmvC := hsb.hcone.mvC_leMax
  have hnv1 : (nv_k + 1#32).toNat = nv_k.toNat + 1 := m6_bv32_add1 (by omega)
  have hov_k : ov.toNat < st_k.core.cur_vars := by rw [s13_cur_vars_eq hsb.hag]; exact hov
  obtain ⟨hnv_cv, hcone_p⟩ := fidConeInv_push_var hsb.hlen hsb.hcone hnv_lt hov_k hmiss
  have hbv : nv_k + 1#32 = BitVec.ofNat 32 (nv_k.toNat + 1) := (m6_bv32_ofNat_add1 nv_k).symm
  have hst_eq : st_push =
      { st_k with scratch :=
        { st_k.scratch with
          tarjan_mark := st_k.scratch.tarjan_mark.set ov.toNat (BitVec.ofNat 32 (nv_k.toNat + 1))
          work_stk1 := st_k.scratch.work_stk1.set nv_k.toNat ov } } := by
    dsimp only [st_push]; rw [hbv]
  have hwk_len := hsb.hlen.scratch_ok.work_stk1_len
  have htm_len := hsb.hlen.scratch_ok.tarjan_mark_len
  have hcv_le := hsb.hlen.core_ok.cur_vars_le
  have hcv_ne_ov : cv.toNat ≠ ov.toNat := fun heq => by
    have ht := hsb.htmk; rw [heq, hmiss] at ht
    have htn := congrArg BitVec.toNat ht
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qi_l.toNat + 1 < 2 ^ 32)] at htn
    omega
  refine ⟨hnv_cv, hnv1,
    ⟨hsb.hlen.core_ok, { hsb.hlen.scratch_ok with
      work_stk1_len := by simp [st_push, hwk_len]
      tarjan_mark_len := by simp [st_push, htm_len] }⟩,
    s13_upd_tmk_ws1 _ _ hsb.hag, ?_, ?_⟩
  · refine ⟨⟨hsb.hlen.core_ok, { hsb.hlen.scratch_ok with
        work_stk1_len := by simp [st_push, hwk_len]
        tarjan_mark_len := by simp [st_push, htm_len] }⟩,
      s13_upd_tmk_ws1 _ _ hsb.hag,
      ⟨hsb.hgu_sav.gu_other, hsb.hgu_sav.hwm_clean, hsb.hgu_sav.hwm_ge⟩,
      by rw [hst_eq, hnv1]; exact hcone_p,
      ?_, ?_, by rw [hnv1]; have := hsb.hsav_le; omega, hsb.hscr, ?_⟩
    · dsimp only [st_push]; rw [List.getElem?_set_ne (Ne.symm hcv_ne_ov)]; exact hsb.htmk
    · dsimp only [st_push]
      rw [List.getElem?_set_ne (by omega : nv_k.toNat ≠ qi_l.toNat)]; exact hsb.hwk
    · intro j hj; dsimp only [st_push]; rw [List.getElem?_set_ne (by have := hsb.hsav_le; omega)]
      exact hsb.hws j hj
  · dsimp only [st_push]; rw [List.getElem?_set_self (by omega), Option.getD_some]

private theorem m6_cnfClause_sat_congr {cl : List Nat} {β β' : Nat → Bool} {nv : Nat}
    (hlt : ∀ l ∈ cl, l < 2 * nv) (hag : ∀ i < nv, β i = β' i) :
    (cnfClause cl).Sat β ↔ (cnfClause cl).Sat β' := by
  simp only [clause_sat_cnfClause_iff]
  constructor
  · rintro ⟨l, hl, hs⟩; refine ⟨l, hl, ?_⟩
    have := hlt l hl; rw [show litVar l = l / 2 from rfl, ← hag (l / 2) (by omega)]; exact hs
  · rintro ⟨l, hl, hs⟩; refine ⟨l, hl, ?_⟩
    have := hlt l hl; rw [show litVar l = l / 2 from rfl, hag (l / 2) (by omega)]; exact hs

private theorem m6_k6Inv_restrict_nv {F_cur : List (List Nat)} {L : K6Layout}
    {ws : List (BitVec 32)} {ks : K6State} {nv_r nv' : Nat}
    (hinv : K6Inv L (ConeModelSet F_cur ws nv_r) ks)
    (hbdd : K6LitsBounded nv' ks) (htrl : ∀ l ∈ k6TrailLits ks, l < 2 * nv') :
    K6Inv L (ConeModelSet F_cur ws nv') ks := by
  have hlift : ∀ β, ConeModelSet F_cur ws nv' β →
      ∃ β', ConeModelSet F_cur ws nv_r β' ∧ ∀ i < nv', β i = β' i := by
    rintro β ⟨α, hα, hagree⟩
    exact ⟨fun i => α (ws[i]?.getD 0#32).toNat, ⟨α, hα, fun _ _ => rfl⟩, hagree⟩
  exact
    { shapes := hinv.shapes
      clauses :=
        { hinv.clauses with
          cl_wf := fun cid hc =>
            let w := hinv.clauses.cl_wf cid hc
            ⟨w.1, w.2.1, w.2.2.1, fun β hβ =>
              let ⟨β', hβ', hag⟩ := hlift β hβ
              (m6_cnfClause_sat_congr (fun l hl => hbdd.1 cid hc l hl) hag).mpr (w.2.2.2 β' hβ')⟩
          incons_ok := fun hi β hβ =>
            let ⟨β', hβ', _⟩ := hlift β hβ
            hinv.clauses.incons_ok hi β' hβ' }
      watches := hinv.watches
      assign :=
        { hinv.assign with
          lvl0_ok := fun i hi hl0 =>
            let w := hinv.assign.lvl0_ok i hi hl0
            ⟨w.1, w.2.1, fun β hβ =>
              let ⟨β', hβ', hag⟩ := hlift β hβ
              have hte : ks.trl_end.toNat ≤ ks.trl.length := by
                rw [hinv.shapes.trl_len]
                exact Nat.le_trans hinv.assign.trl_end_le hinv.clauses.nv_le
              (m6_cnfClause_sat_congr
                (fun l hl => by
                  simp only [List.mem_singleton] at hl; subst hl
                  exact htrl _ (k6_mem_trailLits_of_lt hi hte))
                hag).mpr (w.2.2 β' hβ')⟩ }
      reasons := hinv.reasons }

theorem step13_cone_pop_var_ok {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s st_r : FullState} {scr0 ws0 : List (BitVec 32)}
    {saved_nv nv_r : BitVec 32} {nc_w : Nat}
    (hl_r : st_r.LengthsOk c) (ha_r : AgreesExcept step13ConeMask s st_r)
    (hgu_r : S13GuOk L s saved_nv.toNat st_r) (hc_r : FidConeInv F_cur L mvC st_r nv_r.toNat nc_w)
    (hsav_ge1 : 1 ≤ saved_nv.toNat) (hsav_lt : saved_nv.toNat < nv_r.toNat)
    (hscr_eq : st_r.scratch.scratch_buf = scr0)
    (hbdd_s : K6LitsBounded saved_nv.toNat (k6StateOfScratch L scr0))
    (htrl_s : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * saved_nv.toNat)
    (hws_sav : ∀ j < saved_nv.toNat, st_r.scratch.work_stk1[j]? = ws0[j]?) :
    let nv' := nv_r - 1#32
    let vr := st_r.scratch.work_stk1[nv'.toNat]?.getD 0#32
    let tmk' := st_r.scratch.tarjan_mark.set vr.toNat 0#32
    let st' : FullState := { st_r with scratch := { st_r.scratch with tarjan_mark := tmk' } }
    nv'.toNat = nv_r.toNat - 1 ∧ vr.toNat < st_r.scratch.tarjan_mark.length ∧
    st'.LengthsOk c ∧ AgreesExcept step13ConeMask s st' ∧ S13GuOk L s saved_nv.toNat st' ∧
    FidConeInv F_cur L mvC st' nv'.toNat nc_w ∧ st'.scratch.scratch_buf = scr0 ∧
    (∀ j < saved_nv.toNat, st'.scratch.work_stk1[j]? = ws0[j]?) := by
  intro nv' vr tmk' st'
  have hm := L.hmaxV; have hmvC := hc_r.mvC_leMax
  have hnv1 : nv'.toNat = nv_r.toNat - 1 := by dsimp only [nv']; bv_omega
  have hnv_le : nv'.toNat ≤ nv_r.toNat := by rw [hnv1]; omega
  have hsav_le : saved_nv.toNat ≤ nv'.toNat := by rw [hnv1]; omega
  have hnv_le_mvC := hc_r.nv_le_mvC
  have hcv_le := hl_r.core_ok.cur_vars_le
  have htm_len := hl_r.scratch_ok.tarjan_mark_len
  have hfwd_last := hc_r.fwd nv'.toNat (by omega)
  have hvr_lt_cv : vr.toNat < st_r.core.cur_vars := hfwd_last.1
  have hvr_bd : vr.toNat < st_r.scratch.tarjan_mark.length := by rw [htm_len]; omega
  have hne_vr : ∀ i < nv'.toNat, (st_r.scratch.work_stk1[i]?.getD 0#32).toNat ≠ vr.toNat :=
    fun i hi heq => by
      have hti := (hc_r.fwd i (by omega)).2
      rw [heq, hfwd_last.2] at hti
      have htn := congrArg BitVec.toNat hti
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : nv'.toNat + 1 < 2 ^ 32)] at htn; omega
  refine ⟨hnv1, hvr_bd,
    ⟨hl_r.core_ok, { hl_r.scratch_ok with tarjan_mark_len := by simp [st', tmk', htm_len] }⟩,
    s13_upd_tmk tmk' ha_r, ⟨hgu_r.gu_other, hgu_r.hwm_clean, hgu_r.hwm_ge⟩, ?_, hscr_eq, hws_sav⟩
  exact
    { nv_ge1 := by rw [hnv1]; omega
      nv_le_mvC := by rw [hnv1]; omega
      mvC_leMax := hmvC
      nv_le_cv := by dsimp [st']; have := hc_r.nv_le_cv; omega
      nc_le := hc_r.nc_le
      scr_len := hc_r.scr_len
      k6_inv := by
        dsimp only [st']
        exact m6_k6Inv_restrict_nv hc_r.k6_inv
          (by rw [hscr_eq]; exact ⟨fun cid hcid l hl => by have := hbdd_s.1 cid hcid l hl; omega,
              fun w hw => by have := hbdd_s.2 w hw; omega⟩)
          (fun l hl => by rw [hscr_eq] at hl; have := htrl_s l hl; omega)
      k6_sync := hc_r.k6_sync
      k6_nv := hc_r.k6_nv
      k6_lvl := hc_r.k6_lvl
      k6_na := hc_r.k6_na
      k6_bdd := by
        rw [hscr_eq]; exact ⟨fun cid hcid l hl => by have := hbdd_s.1 cid hcid l hl; omega,
          fun w hw => by have := hbdd_s.2 w hw; omega⟩
      k6_trl_bdd := fun l hl => by rw [hscr_eq] at hl; have := htrl_s l hl; omega
      fwd := fun i hi => by
        dsimp only [st']
        have hti := hc_r.fwd i (by omega)
        rw [List.getElem?_set_ne (Ne.symm (hne_vr i hi))]; exact hti
      rev := fun v hv => by
        dsimp only [st']
        by_cases hvv : v = vr.toNat
        · subst hvv; left; rw [List.getElem?_set_self (by omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm hvv)]
          rcases hc_r.rev v hv with hz | ⟨i, hi, hwi, hti⟩
          · exact Or.inl hz
          · right
            have hne_i : i ≠ nv'.toNat := fun heq => by subst heq; exact hvv hwi.symm
            exact ⟨i, by omega, hwi, hti⟩ }

theorem fid_cone_k_unassigned_step {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s st_k st_u : FullState}
    {cr sz k cnt nv_k nv_u lit_k : BitVec 32} {saved_nv ilv nc_w : Nat}
    (hlu : st_u.LengthsOk c) (htmpu_eq : st_u.core.tmp = st_k.core.tmp)
    (hwku_eq : ∀ j < nv_k.toNat, st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?)
    (_hsav_k : saved_nv ≤ nv_k.toNat) (hnvku : nv_k.toNat ≤ nv_u.toNat)
    (hstep_new : ∀ v, nv_k.toNat ≤ v → v < nv_u.toNat → v = ilv)
    (hnvu_max : nv_u.toNat ≤ L.maxV) (hk_lt : k.toNat < sz.toNat)
    (hsz_cv : sz.toNat ≤ s.core.cur_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcnt_le : cnt.toNat ≤ k.toNat)
    (hlit_ar : (s.core.arena[cr.toNat + 3 + k.toNat]?.getD 0#32).toNat = lit_k.toNat)
    (hilv : ilv < nv_u.toNat)
    (hwlv : (st_u.scratch.work_stk1[ilv]?.getD 0#32).toNat = lit_k.toNat / 2)
    (htlv_v : st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 = BitVec.ofNat 32 (ilv + 1))
    (hlts_k : ∀ j < cnt.toNat, (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat)
    (hcov_k : ∀ i < k.toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_k.core.tmp.take cnt.toNat).map
        (fun x => m6ConeLift st_k.scratch.work_stk1 x.toNat))
    (hvars_k : ∀ j < cnt.toNat, ∃ p < k.toNat,
      (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 =
        (st_k.scratch.work_stk1[(st_k.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hnd_k : ∀ j1 j2, j1 < cnt.toNat → j2 < cnt.toNat → j1 ≠ j2 →
      (st_k.core.tmp[j1]?.getD 0#32).toNat / 2 ≠ (st_k.core.tmp[j2]?.getD 0#32).toNat / 2)
    (hsav_vars_k : ∀ v, saved_nv ≤ v → v < nv_k.toNat →
      ∃ i < cnt.toNat, (st_k.core.tmp[i]?.getD 0#32).toNat / 2 = v)
    (hnd_cl : ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup)
    (hcr_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (_hc_u : FidConeInv F_cur L mvC st_u nv_u.toNat nc_w) :
    let new_l : BitVec 32 :=
      (((st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32) - 1#32) <<< (1 : Nat)) |||
        (lit_k &&& 1#32)
    let st_u' : FullState :=
      { st_u with core := { st_u.core with tmp := st_u.core.tmp.set cnt.toNat new_l } }
    (cnt + 1#32).toNat = cnt.toNat + 1 ∧ st_u'.LengthsOk c ∧
    (∀ j < (cnt + 1#32).toNat, (st_u'.core.tmp[j]?.getD 0#32).toNat < 2 * nv_u.toNat) ∧
    (∀ i < (k + 1#32).toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_u'.core.tmp.take (cnt + 1#32).toNat).map
        (fun x => m6ConeLift st_u'.scratch.work_stk1 x.toNat)) ∧
    (∀ j < (cnt + 1#32).toNat, ∃ p < (k + 1#32).toNat,
      (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 =
        (st_u'.scratch.work_stk1[(st_u'.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
    (∀ j1 j2, j1 < (cnt + 1#32).toNat → j2 < (cnt + 1#32).toNat → j1 ≠ j2 →
      (st_u'.core.tmp[j1]?.getD 0#32).toNat / 2 ≠ (st_u'.core.tmp[j2]?.getD 0#32).toNat / 2) ∧
    (∀ v, saved_nv ≤ v → v < nv_u.toNat →
      ∃ i < (cnt + 1#32).toNat, (st_u'.core.tmp[i]?.getD 0#32).toNat / 2 = v) := by
  intro new_l st_u'
  have hmL := L.hmaxV
  have htmp_u := hlu.core_ok.tmp_len_arr
  have htmp_k : st_k.core.tmp.length = c.max_vars := htmpu_eq ▸ htmp_u
  have hdb : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcnt_lt32 : cnt.toNat < 2 ^ 31 := by unfold dimacsBound at hdb; omega
  have hk_lt32 : k.toNat < 2 ^ 31 := by unfold dimacsBound at hdb; omega
  have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := m6_bv32_add1 (by omega)
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := m6_bv32_add1 (by omega)
  have hm1 : BitVec.ofNat 32 (ilv + 1) - 1#32 = BitVec.ofNat 32 ilv :=
    bv32_ofNat_sub1 (by omega)
  have hnew_n : new_l.toNat = 2 * ilv + lit_k.toNat % 2 := by
    simp only [new_l, htlv_v, hm1]
    have := m6_bv32_shl1_or_and1 (BitVec.ofNat 32 ilv) lit_k
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ilv < 2 ^ 32)] using this
  have hnew_lift : m6ConeLift st_u'.scratch.work_stk1 new_l.toNat = lit_k.toNat := by
    rw [hnew_n]; exact coneLift_of_tmk_pair hwlv rfl
  have htake_u' : st_u'.core.tmp.take (cnt + 1#32).toNat =
      st_u.core.tmp.take cnt.toNat ++ [new_l] := by
    have hlen_tk : (st_u.core.tmp.take cnt.toNat).length = cnt.toNat := by simp [htmp_u]; omega
    rw [hcnt1]; dsimp only [st_u']; apply List.ext_getElem; · simp [htmp_u]; omega
    intro j hj1 _; have hj : j < cnt.toNat + 1 := by simp [htmp_u] at hj1; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [List.getElem_take, List.getElem_set_ne (by omega : cnt.toNat ≠ j),
        List.getElem_append_left (by omega), List.getElem_take]
    · simp [List.getElem_take, List.getElem_set_self, List.getElem_append_right, hlen_tk]
  have hcl_vlen : ((fullArenaClauseLits s cr.toNat).map (· / 2)).length = sz.toNat := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    rw [List.length_map, List.length_map, List.length_take, List.length_drop, ← hsz_core]
    exact Nat.min_eq_left (by omega)
  have hne_prev : ∀ j < cnt.toNat,
      (st_k.core.tmp[j]?.getD 0#32).toNat / 2 ≠ ilv := fun j hj heq => by
    obtain ⟨p, hp, hpeq⟩ := hvars_k j hj
    have hj_lt := hlts_k j hj
    have hwk_p := hwku_eq _ (by omega : (st_k.core.tmp[j]?.getD 0#32).toNat / 2 < nv_k.toNat)
    rw [heq] at hwk_p hpeq
    have hvar_eq : (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 = lit_k.toNat / 2 := by
      rw [hpeq, ← hwk_p, hwlv]
    have hp_v : p < ((fullArenaClauseLits s cr.toNat).map (· / 2)).length := by omega
    have hk_v : k.toNat < ((fullArenaClauseLits s cr.toNat).map (· / 2)).length := by omega
    have hinj := k6_list_nodup_getElem_inj hnd_cl hp_v hk_v
    have hgp : ((fullArenaClauseLits s cr.toNat).map (· / 2))[p]'hp_v =
        (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 := by
      refine Option.some.inj ?_
      rw [← List.getElem?_eq_getElem hp_v]
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      have hbd_p : cr.toNat + 3 + p < s.core.arena.length := by omega
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_take_of_lt (by omega),
        List.getElem?_drop, List.getElem?_eq_getElem hbd_p]
      simp only [Option.map_some, Option.getD_some]
    have hgk : ((fullArenaClauseLits s cr.toNat).map (· / 2))[k.toNat]'hk_v =
        lit_k.toNat / 2 := by
      refine Option.some.inj ?_
      rw [← List.getElem?_eq_getElem hk_v]
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      have hbd_k : cr.toNat + 3 + k.toNat < s.core.arena.length := by omega
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_take_of_lt (by omega),
        List.getElem?_drop, ← hlit_ar, List.getElem?_eq_getElem hbd_k]
      simp only [Option.map_some, Option.getD_some]
    have hpk := hinj (by rw [hgp, hgk, hvar_eq])
    omega
  refine ⟨hcnt1, ⟨{ hlu.core_ok with tmp_len_arr := by simp [st_u', htmp_u] }, hlu.scratch_ok⟩,
    fun j hj => ?_, fun i hi => ?_, fun j hj => ?_,
    fun j1 j2 hj1 hj2 hne => ?_, fun v hv1 hv2 => ?_⟩
  · rw [hcnt1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · dsimp only [st_u']; rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j), htmpu_eq]
      exact Nat.lt_of_lt_of_le (hlts_k j hlt) (by omega)
    · dsimp only [st_u']; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
  · rw [hk1] at hi; rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · rcases hcov_k i hlt with hfals | hmem
      · exact Or.inl hfals
      · right; rw [htake_u', List.map_append]; apply List.mem_append_left
        rcases List.mem_map.mp hmem with ⟨x, hx, heq_l⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have hj_cnt : j < cnt.toNat := by simp at hj; omega
        have hx_lt := hlts_k j hj_cnt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_lt
        have hwk_eq_x : st_u.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? =
            st_k.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? :=
          hwku_eq _ (by omega)
        have hel : st_u.core.tmp[j]'(by omega) = st_k.core.tmp[j]'(by omega) := by
          simp only [htmpu_eq]
        refine List.mem_map.mpr ⟨st_u.core.tmp[j]'(by omega), ?_, ?_⟩
        · have hmem' : (st_u.core.tmp.take cnt.toNat)[j]'(by simp [htmp_u]; omega) ∈
              st_u.core.tmp.take cnt.toNat := List.getElem_mem _
          rwa [List.getElem_take] at hmem'
        · rw [List.getElem_take] at heq_l
          dsimp only [m6ConeLift, st_u'] at heq_l ⊢
          rw [hel, hwk_eq_x]; exact heq_l
    · right; rw [htake_u', List.map_append]
      exact List.mem_append_right _ (by simp [hlit_ar, hnew_lift])
  · rw [hcnt1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · obtain ⟨p, hp, hpeq⟩ := hvars_k j hlt
      have hj_lt := hlts_k j hlt
      refine ⟨p, by omega, ?_⟩
      dsimp only [st_u']
      rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j), htmpu_eq, hwku_eq _ (by omega)]
      exact hpeq
    · refine ⟨k.toNat, by rw [hk1]; omega, ?_⟩
      dsimp only [st_u']
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        show new_l.toNat / 2 = ilv by omega, hwlv, hlit_ar]
  · rw [hcnt1] at hj1 hj2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj1 with h1 | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj2 with h2 | rfl
    · dsimp only [st_u']
      rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j1),
        List.getElem?_set_ne (by omega : cnt.toNat ≠ j2), htmpu_eq]
      exact hnd_k j1 j2 h1 h2 hne
    · dsimp only [st_u']
      rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j1),
        List.getElem?_set_self (by omega), Option.getD_some, htmpu_eq,
        show new_l.toNat / 2 = ilv by omega]
      exact hne_prev j1 h1
    · dsimp only [st_u']
      rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j2),
        List.getElem?_set_self (by omega), Option.getD_some, htmpu_eq,
        show new_l.toNat / 2 = ilv by omega]
      exact (hne_prev j2 h2).symm
    · exact False.elim (hne rfl)
  · by_cases hvn : v < nv_k.toNat
    · obtain ⟨i, hi, hid⟩ := hsav_vars_k v hv1 hvn
      refine ⟨i, by rw [hcnt1]; omega, ?_⟩
      dsimp only [st_u']
      rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ i), htmpu_eq]
      exact hid
    · refine ⟨cnt.toNat, by rw [hcnt1]; omega, ?_⟩
      dsimp only [st_u']
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        show new_l.toNat / 2 = ilv by omega, hstep_new v (by omega) hv2]

theorem s13_scan_tmp_step {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st_k st_u : FullState}
    {cv qi_l savedNv nv_k nv_u cr sz cnt idx lit_k : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {nc_w ilv : Nat}
    (hsb : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
      nv_k.toNat nc_w cnt.toNat idx.toNat st_k)
    (hsu : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv_u.toNat nc_w st_u)
    (htmp_eq : st_u.core.tmp = st_k.core.tmp)
    (hws_eq : ∀ j, j < nv_k.toNat → st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?)
    (hnv_le : nv_k.toNat ≤ nv_u.toNat)
    (hstep_new : ∀ v, nv_k.toNat ≤ v → v < nv_u.toNat → v = ilv)
    (hidx_lt : idx.toNat < sz.toNat)
    (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hcnt_le : cnt.toNat ≤ idx.toNat)
    (hlit_at : (s.core.arena[cr.toNat + 3 + idx.toNat]?.getD 0#32).toNat = lit_k.toNat)
    (hilv_lt : ilv < nv_u.toNat)
    (hilv_ws : (st_u.scratch.work_stk1[ilv]?.getD 0#32).toNat = lit_k.toNat / 2)
    (hilv_tmk : st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 = BitVec.ofNat 32 (ilv + 1))
    (hnodup : (List.map (fun x => x / 2) (fullArenaClauseLits s cr.toNat)).Nodup)
    (har_len : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat) :
    let new_l := (st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 - 1#32) <<< 1 |||
      lit_k &&& 1#32
    let st_u' : FullState :=
      { core := { st_u.core with tmp := st_u.core.tmp.set cnt.toNat new_l }
        scratch := st_u.scratch }
    (cnt + 1#32).toNat = cnt.toNat + 1 ∧ (idx + 1#32).toNat = idx.toNat + 1 ∧
      Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
        nv_u.toNat nc_w (cnt + 1#32).toNat (idx + 1#32).toNat st_u' := by
  intro new_l st_u'
  have hnv_max : nv_u.toNat ≤ L.maxV := Nat.le_trans hsu.hcone.nv_le_mvC hsu.hcone.mvC_leMax
  have hku := fid_cone_k_unassigned_step hsu.hlen htmp_eq hws_eq hsb.hsav_le hnv_le hstep_new
    hnv_max hidx_lt hsz_cv (by rw [← s13_cur_vars_eq hsb.hag]; exact hsb.hlen.core_ok.cur_vars_le)
    hcnt_le hlit_at hilv_lt hilv_ws hilv_tmk hsb.hlts hsb.hcov hsb.hvars hsb.hnd hsb.hsav_vars
    hnodup har_len hsz_eq hsu.hcone
  have hku1 : (cnt + 1#32).toNat = cnt.toNat + 1 := hku.1
  have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := by
    have : idx.toNat + 1 < 2 ^ 32 := by omega
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt this]
  refine ⟨hku1, hidx1, ?_⟩
  have hlen' : FullState.LengthsOk c st_u' := hku.2.1
  have hag' : AgreesExcept step13ConeMask s st_u' := hsu.hag
  have hgu' : S13GuOk L s savedNv.toNat st_u' :=
    ⟨hsu.hgu_sav.gu_other, hsu.hgu_sav.hwm_clean, hsu.hgu_sav.hwm_ge⟩
  have hc0 := hsu.hcone
  have hcone' : FidConeInv F_cur L mvC st_u' nv_u.toNat nc_w :=
    ⟨hc0.nv_ge1, hc0.nv_le_mvC, hc0.mvC_leMax, hc0.nv_le_cv, hc0.nc_le, hc0.scr_len,
     hc0.k6_inv, hc0.k6_sync, hc0.k6_nv, hc0.k6_lvl, hc0.k6_na, hc0.k6_bdd,
     hc0.k6_trl_bdd, hc0.fwd, hc0.rev⟩
  refine ⟨⟨hlen', hag', hgu', hcone', hsu.htmk, hsu.hwk, hsu.hsav_le, hsu.hscr, hsu.hws⟩,
    hku.2.2.1, fun i hi => hku.2.2.2.1 i hi, hku.2.2.2.2.1, hku.2.2.2.2.2.1, hku.2.2.2.2.2.2⟩

theorem s13_scan_skip_step {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {c : FullCfg} {s st_k : FullState}
    {cv qi_l savedNv nv_k cr sz cnt idx : BitVec 32}
    {ws0 scr0 : List (BitVec 32)} {nc_w : Nat}
    (hsb : Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
      nv_k.toNat nc_w cnt.toNat idx.toNat st_k)
    (hidx_lt : idx.toNat < sz.toNat)
    (hfal : s.core.vals[(s.core.arena[cr.toNat + 3 + idx.toNat]?.getD 0#32).toNat]?.getD 0#8 =
      255#8) :
    (idx + 1#32).toNat = idx.toNat + 1 ∧
      Step13ConeScanBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 cr
        nv_k.toNat nc_w cnt.toNat (idx + 1#32).toNat st_k := by
  have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := by
    have : idx.toNat + 1 < 2 ^ 32 := by omega
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt this]
  refine ⟨hidx1, hsb.toStep13ConeSavedBase, hsb.hlts, ?_, ?_, hsb.hnd, hsb.hsav_vars⟩
  · intro i hi
    have hi' : i < idx.toNat + 1 := by omega
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with hlt | rfl
    · exact hsb.hcov i hlt
    · exact Or.inl hfal
  · intro j hj
    rcases hsb.hvars j hj with ⟨p, hp, hpe⟩
    exact ⟨p, by omega, hpe⟩

theorem s13_k6StateOfScratch_set25 (L : K6Layout) (scr : List (BitVec 32)) (v : BitVec 32)
    (hlen : scr.length = L.scrLen) :
    let ks := k6StateOfScratch L scr
    let ks' := k6StateOfScratch L (scr.set (L.k6Base + 25) v)
    ks'.nv = ks.nv ∧ ks'.nc = ks.nc ∧ ks'.lvl = ks.lvl ∧ ks'.trl_end = ks.trl_end ∧
      ks'.nassump = ks.nassump ∧
      (K6TrailSynced ks → K6TrailSynced ks') ∧
      (∀ P, K6Inv L P ks → K6Inv L P ks') ∧
      (∀ hw, K6HwmClean L hw ks → K6HwmClean L hw ks') := by
  have hinv_eq := m6_k6StateOfScratch_set25 L scr v hlen.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hinv_eq]; rfl
  · rw [hinv_eq]; rfl
  · rw [hinv_eq]; rfl
  · rw [hinv_eq]; rfl
  · rw [hinv_eq]; rfl
  · intro hts; rw [hinv_eq]
    intro i hi; exact hts i hi
  · intro P hinv; rw [hinv_eq]; exact k6PutHdr25_inv v hinv
  · intro hw hcl; rw [hinv_eq]; exact k6HwmClean_putHdr25 v hcl

theorem step13_cone_init_ok {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s : FullState} {scr0 gu0 : List (BitVec 32)} {mv32 root_v : BitVec 32}
    (hs : s.LengthsOk c) (_hL : L.scrLen = c.scratch_cap)
    (hmv_eq : mv32 = BitVec.ofNat 32 L.maxV) (hmv_nat : mv32.toNat ≤ L.maxV)
    (hrv : root_v.toNat < s.core.cur_vars) (htmk0 : M6TmkZero s) (hscr_len : scr0.length = L.scrLen)
    (hsi : ({ s with scratch :=
      { s.scratch with glue_used := gu0, scratch_buf := scr0 } } : FullState).LengthsOk c)
    (hgu_i : ∀ i < 64, i ≠ 33 → gu0[i]? = s.scratch.glue_used[i]?)
    (hclean_i : K6HwmClean L (gu0[33]?.getD 0#32) (k6StateOfScratch L scr0))
    (hinv_i : ∀ P, K6Inv L P (k6StateOfScratch L scr0))
    (hts_i : K6TrailSynced (k6StateOfScratch L scr0))
    (hnv_i : (k6StateOfScratch L scr0).nv = mv32)
    (hnc_i : (k6StateOfScratch L scr0).nc = 0#32)
    (hlvl_i : (k6StateOfScratch L scr0).lvl = 0#32)
    (htrl_i : (k6StateOfScratch L scr0).trl_end = 0#32)
    (hna_i : (k6StateOfScratch L scr0).nassump = 0#32) :
    let s1 : FullState :=
      { s with scratch :=
        { s.scratch with
          work_stk1 := s.scratch.work_stk1.set 0 root_v
          tarjan_mark := s.scratch.tarjan_mark.set root_v.toNat 1#32
          glue_used := gu0
          scratch_buf := scr0 } }
    s1.LengthsOk c ∧ AgreesExcept step13ConeMask s s1 ∧ S13GuOk L s 1 s1 ∧
      FidConeInv F_cur L mv32 s1 1 0 := by
  intro s1
  have hm := L.hmaxV
  have hmv_val : mv32.toNat = L.maxV := by
    rw [hmv_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcv_le := hs.core_ok.cur_vars_le
  have hws_len := hs.scratch_ok.work_stk1_len
  have htm_len := hs.scratch_ok.tarjan_mark_len
  have hlen1 : s1.LengthsOk c :=
    ⟨hs.core_ok, { hsi.scratch_ok with
      work_stk1_len := by simp [s1, hws_len]
      tarjan_mark_len := by simp [s1, htm_len] }⟩
  have hag1 : AgreesExcept step13ConeMask s s1 := by
    dsimp [AgreesExcept, step13ConeMask, s1]
  have hgu1 : S13GuOk L s 1 s1 := ⟨hgu_i, hclean_i, fun h => by omega⟩
  have hinv_k := hinv_i (ConeModelSet F_cur s1.scratch.work_stk1 1)
  have hcl_wf0 : ∀ cid < (k6StateOfScratch L scr0).nc.toNat, False := fun cid hcid => by
    rw [hnc_i] at hcid; simp at hcid
  have htrl_emp : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * 1 := fun l hl => by
    unfold k6TrailLits at hl; rw [htrl_i] at hl; simp at hl
  refine ⟨hlen1, hag1, hgu1, ?_⟩
  exact
    { nv_ge1 := by omega
      nv_le_mvC := by omega
      mvC_leMax := hmv_nat
      nv_le_cv := by dsimp [s1]; omega
      nc_le := by omega
      scr_len := hscr_len
      k6_inv := hinv_k
      k6_sync := hts_i
      k6_nv := hnv_i
      k6_lvl := hlvl_i
      k6_na := hna_i
      k6_bdd := ⟨fun cid hc => absurd hc (hcl_wf0 cid), fun w hw => by
        have hnc0 : (k6StateOfScratch L s1.scratch.scratch_buf).nc = 0#32 := hnc_i
        rw [hnc0] at hw; simp at hw⟩
      k6_trl_bdd := htrl_emp
      fwd := fun i hi => by
        have hi0 : i = 0 := by omega
        subst hi0
        have hws0 : (s1.scratch.work_stk1[0]?.getD 0#32).toNat = root_v.toNat := by
          dsimp only [s1]; rw [List.getElem?_set_self (by omega), Option.getD_some]
        refine ⟨by dsimp only [s1]; rw [hws0]; exact hrv, ?_⟩
        dsimp only [s1]; rw [List.getElem?_set_self (by omega), Option.getD_some,
          List.getElem?_set_self (by omega), Option.getD_some]
      rev := fun v hv => by
        dsimp only [s1]
        by_cases hvr : v = root_v.toNat
        · subst hvr; right; refine ⟨0, by omega, ?_, ?_⟩
          · rw [List.getElem?_set_self (by omega), Option.getD_some]
          · rw [List.getElem?_set_self (by omega), Option.getD_some]
        · left; rw [List.getElem?_set_ne (Ne.symm hvr)]; exact htmk0 v hv }

theorem step13_cone_exit_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {L : K6Layout} {mvC nv nc : BitVec 32} {s st_e : FullState}
    {R : Mem 64 → Prop} {m4 : Mem 64} {Q : Post [i64]}
    (hdense : FullDenseInvW c F0 F_cur s)
    (hmin_scr : k6MinScr ≤ c.scratch_cap)
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hlen_e : st_e.LengthsOk c) (hag_e : AgreesExcept step13ConeMask s st_e)
    (hgu_e : S13GuOk L s nv.toNat st_e)
    (hcone_e : FidConeInv F_cur L mvC st_e nv.toNat nc.toNat)
    (hm4 : (K6MemA L (L.kPtr c.pScratchBuf)
        (((((((k6StateOfScratch L st_e.scratch.scratch_buf).putHdr .nv nv).putHdr
          .unass (nv - (k6StateOfScratch L st_e.scratch.scratch_buf).trl_end)).putHdr
          .qlast (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr
          .qnext (nv.toNat - 1) 4294967295#32) ⋆ (FullK6Frame c L st_e ⋆ R)) m4)
    (hQ : ∀ (r : BitVec 64) (tmp' ws1' tmk' scr' gu' : List (BitVec 32)) (m' : Mem 64),
      have s' : FullState :=
        { core := { s.core with tmp := tmp' }
          scratch := { s.scratch with
            work_stk1 := ws1', tarjan_mark := tmk', glue_used := gu', scratch_buf := scr' } }
      let nvN := (r &&& 65535#64).toNat
      let ncN := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.vals = s.core.vals →
      s'.core.inconsistent = s.core.inconsistent →
      M6SweepConeOk F_cur s' nvN → ncN ≤ 3 * k6MaxV c.scratch_cap →
      r.toNat = nvN + ncN * 2 ^ 16 →
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
      (∃ L', L'.scrLen = c.scratch_cap ∧ L'.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L' (gu'[33]?.getD 0#32) (k6StateOfScratch L' scr') ∧
        (2 ≤ nvN → gu'[33]? = some 0xFFFFFFFF#32 ∨ nvN ≤ (gu'[33]?.getD 0#32).toNat)) →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nvN, (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Q ((nv.setWidth 64) ||| ((nc.setWidth 64) <<< 16#64), ()) m4 := by
  have ⟨hinv', hsync', hnv'⟩ := k6ShrinkNv_preserves_inv hcone_e.k6_inv hcone_e.k6_sync
    hcone_e.nv_ge1 hcone_e.nv_le_mvC hcone_e.mvC_leMax hcone_e.k6_nv hcone_e.k6_lvl
    hcone_e.k6_na hcone_e.k6_bdd hcone_e.k6_trl_bdd
  have hst_scr : st_e.scratch.scratch_buf.length = c.scratch_cap :=
    hlen_e.scratch_ok.scratch_buf_len
  obtain ⟨hsl, _, hof, hm_full⟩ := m6_join_k6_ofSlab hLscr hst_scr hinv'.shapes hm4
  let scr' := st_e.scratch.scratch_buf.take L.k6Base ++
    (((((((k6StateOfScratch L st_e.scratch.scratch_buf).putHdr .nv nv).putHdr
      .unass (nv - (k6StateOfScratch L st_e.scratch.scratch_buf).trl_end)).putHdr
      .qlast (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr
      .qnext (nv.toNat - 1) 4294967295#32).toSlab
  let st_f : FullState := { st_e with scratch := { st_e.scratch with scratch_buf := scr' } }
  have hc0 := s13ConeMask_core_eq hag_e
  have hsc0 : (step13ConeMask st_e).scratch = (step13ConeMask s).scratch :=
    congrArg FullState.scratch hag_e
  have hst_eq : st_f =
      { core := { s.core with tmp := st_e.core.tmp }
        scratch := { s.scratch with
          work_stk1 := st_e.scratch.work_stk1, tarjan_mark := st_e.scratch.tarjan_mark,
          glue_used := st_e.scratch.glue_used, scratch_buf := scr' } } := by
    cases st_e with | mk c1 sc1 => cases s with | mk c2 sc2 =>
    dsimp only [step13ConeMask, st_f] at hc0 hsc0 ⊢
    cases sc1; cases sc2; cases hsc0; rw [hc0]
  have hlen_f : st_f.LengthsOk c :=
    ⟨hlen_e.core_ok, { hlen_e.scratch_ok with scratch_buf_len := hsl }⟩
  have hag_f : AgreesExcept step13ConeMask s st_f := hag_e.update _ (fun _ => rfl)
  have hdense_f : FullDenseInvW c F0 F_cur st_f := s13ConeMask_preserves_dense hag_f hlen_f hdense
  have hm_L := L.hmaxV; have hac := L.hacap
  have hnc_max : nc.toNat ≤ 3 * k6MaxV c.scratch_cap := by
    rw [← hLmv]; exact hcone_e.nc_le
  have ⟨hnv_p, hnc_p, hr_p⟩ := m6_pack_nv_nc nv nc
    (by have := hm_L; have := hcone_e.nv_le_mvC; have := hcone_e.mvC_leMax; omega)
    (by have := hLmv; omega)
  have hsh_eq : (nc.setWidth 64 <<< 16#64) = (nc.setWidth 64 <<< (16 : Nat)) := rfl
  have hlt_dim : c.scratch_cap < dimacsBound := c.hscr
  have hnv_eq : BitVec.ofNat 32 nv.toNat = nv := BitVec.eq_of_toNat_eq (by
    have := hm_L; have := hcone_e.nv_le_mvC; have := hcone_e.mvC_leMax
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hcone_ok : M6SweepConeOk F_cur st_f nv.toNat := by
    have hL_eq : k6LayoutOfCap st_f.scratch.scratch_buf.length (by rw [hsl]; exact hmin_scr)
        (by rw [hsl]; exact hlt_dim) = L :=
      k6LayoutOfCap_eq (hLscr.trans hsl.symm) (by rw [hsl]; exact hLmv)
        (by rw [hsl]; exact hmin_scr) (by rw [hsl]; exact hlt_dim)
    refine ⟨hcone_e.nv_ge1,
      by dsimp [st_f]; rw [hsl, ← hLmv]; exact Nat.le_trans hcone_e.nv_le_mvC hcone_e.mvC_leMax,
      by dsimp [st_f]; exact hcone_e.nv_le_cv,
      by dsimp [st_f]; exact fun i hi => (hcone_e.fwd i hi).1,
      ?_, by rw [hsl]; exact hmin_scr, by rw [hsl]; exact hlt_dim, ?_⟩
    · have hk_inv : K6Inv L (ConeModelSet F_cur st_f.scratch.work_stk1 nv.toNat)
          (k6StateOfScratch L st_f.scratch.scratch_buf) := by
        dsimp only [st_f]; rw [hof]; exact hinv'
      exact hk_inv.to_scratchInv (hsl.trans hLscr.symm) (by rw [hsl]; exact hLmv)
        (by rw [hsl]; exact hmin_scr) (by rw [hsl]; exact hlt_dim)
    · rw [hL_eq]; dsimp only [st_f]; rw [hof, hnv', hnv_eq]
  have hclean' : K6HwmClean L (st_f.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L scr') := by
    dsimp only [st_f]; rw [hof]
    rcases hgu_e.hwm_clean with hff | ⟨hle, hcl⟩
    · exact Or.inl hff
    · exact Or.inr ⟨hle, hcl⟩
  have hrev_tmk : ∀ v < s.core.cur_vars,
      st_f.scratch.tarjan_mark[v]?.getD 0#32 ≠ 0#32 →
      ∃ i < ((BitVec.setWidth 64 nv ||| BitVec.setWidth 64 nc <<< 16#64) &&& 65535#64).toNat,
        (st_f.scratch.work_stk1[i]?.getD 0#32).toNat = v := by
    intro v hv hne; rw [hsh_eq, hnv_p]
    have hv' : v < st_e.core.cur_vars := by rw [s13_cur_vars_eq hag_e]; exact hv
    rcases hcone_e.rev v hv' with h0 | ⟨i, hi, hwi, _⟩
    · exact absurd h0 hne
    · exact ⟨i, hi, hwi⟩
  have hres := hQ (nv.setWidth 64 ||| nc.setWidth 64 <<< 16#64)
    st_e.core.tmp st_e.scratch.work_stk1 st_e.scratch.tarjan_mark scr'
    st_e.scratch.glue_used m4
  have hm_f : (FullMem c st_f ⋆ R) m4 := hm_full
  rw [hst_eq] at hdense_f hcone_ok hm_f
  refine hres hdense_f (by simp) (by simp) (by simp) (by simp) ?_ ?_ ?_ hgu_e.gu_other
    ⟨L, hLscr, hLmv, hclean',
      fun h2 => by rw [hsh_eq, hnv_p] at h2 ⊢; exact hgu_e.hwm_ge h2⟩ hrev_tmk hm_f
  · rw [hsh_eq, hnv_p]; exact hcone_ok
  · rw [hsh_eq, hnc_p]; exact hnc_max
  · rw [hsh_eq, hnv_p, hnc_p]; exact hr_p

end LeanQbe.T.Examples.Kissat.Proof.Sweep
