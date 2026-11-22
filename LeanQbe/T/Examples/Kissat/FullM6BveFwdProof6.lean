module

public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof3
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof5
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-2 `PR-W2D` (`RC-22`) Proofs — Part 6 (Cluster 4: Max-Heap BVE & Orchestrator)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
- `full_bve_var_key_m6_wp`, `full_bve_heap_{up,down,push,pop}_m6_wp` (BVE max-heap scoring &
  priority queue on `work_stk1` + `sim_sig`).
- `full_bve_collect_nbrs_m6_wp` (directly certifies `FullM3CongBva.m3ElimCollectNbrsSpec`).
- `full_elim_bve_m6_wp` (directly certifies canonical `FullM3CongBva.m3ElimBveSpec`, with
  max-heap scheduling, `FL_ELIM_C` neighbor re-arming, and completion-gated `elim_bound`
  progression `0 -> 1 -> 2 -> 4 -> 8 -> 16`).
- `full_eliminate_m6_wp` (directly certifies canonical `FullFastSched.schedEliminateSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6BveFwd

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m6_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Pure Framing Helpers -/

private theorem m6_denseInv_with_ws1_ss {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {ws1' : List (BitVec 32)} {ss' : List (BitVec 64)}
    (hws1 : ws1'.length = 2 * c.max_vars) (hss : ss'.length = c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  let sc' : FullScratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' }
  exact (m6_fullDenseInvW_with_scratch hdw (sc' := sc')
    { hdw.1.scratch_ok with work_stk1_len := hws1, sim_sig_len := hss } rfl rfl).toDense

private theorem m6_denseInv_with_scratch_keep6 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {scr' : FullScratch}
    (hok : scr'.LengthsOk c) (hll : scr'.last_learned = s.scratch.last_learned)
    (hel : scr'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := scr' } :=
  fullDenseInv_with_scratch_keep h hok hll hel

private theorem m6_sparseInv_with_scratch_keep6 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {scr' : FullScratch}
    (hok : scr'.LengthsOk c) (hll : scr'.last_learned = s.scratch.last_learned)
    (hel : scr'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := scr' } :=
  fullSparseInv_with_scratch_keep h hok hll hel

private theorem m6_tmkZero_of_init {s : FullState} {tmki : List (BitVec 32)}
    (hinit : ∀ k < s.core.cur_vars, tmki[k]?.getD 0#32 = 0#32) :
    TmkZero { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fun v hv => hinit v hv

private theorem m6_denseInv_with_flags6 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } :=
  fullDenseInv_with_flags h hfl

private theorem m6_shr1_lt {p : BitVec 64} (hp : 0 < p.toNat) :
    ((p - 1#64) >>> (1 : Nat)).toNat = (p.toNat - 1) / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  have hlt : p.toNat < 2 ^ 64 := p.isLt
  have h1 : (2 ^ 64 - 1 + p.toNat) % 2 ^ 64 = p.toNat - 1 := by omega
  rw [h1]

private theorem m6_shl1_add1_toNat {p : BitVec 64} (hp : p.toNat < 2 ^ 30) :
    ((p <<< (1 : Nat)) + 1#64).toNat = 2 * p.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

private theorem m6_bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
private theorem m6_bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl

/-! ## 2. BVE Max-Heap Key & Priority Queue Specs + `Func.wp` Proofs -/

/-- Contract for `full_bve_var_key_m6`: pure read-only BVE max-heap priority key computation. -/
def fullBveVarKeyM6Spec : Spec [i64, i32] [i64] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

theorem fullBveVarKeyM6Spec_noExit :
    ∀ xs m Q X, fullBveVarKeyM6Spec xs m Q X →
      fullBveVarKeyM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveVarKeyM6Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r : BitVec 64, Q (r, ()) m) :
    fullBveVarKeyM6Spec (h, v, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hm, hQ⟩

/-- Parametric `Func.wp` proof for `full_bve_var_key_m6`. -/
theorem full_bve_var_key_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBveVarKeyM6Spec a m Q X →
      Func.wp Γ full_bve_var_key_m6_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold Func.wp full_bve_var_key_m6_body
  c0_hsplit
  · c0_hsteps!; exact hQ 0#64
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
    have hwv1 : ((v.setWidth 64 <<< (2 : Nat)) + 1#64).toNat < s.core.wvec.length := by
      rw [hlen.core_ok.wvec_len]; c0_bound
    have hwv3 : ((v.setWidth 64 <<< (2 : Nat)) + 3#64).toNat < s.core.wvec.length := by
      rw [hlen.core_ok.wvec_len]; c0_bound
    have hv_sc : (v.setWidth 64).toNat < s.scratch.score.length := by
      rw [hlen.scratch_ok.score_len, m6_zext32_toNat]; omega
    have hv_qs : (v.setWidth 64).toNat < s.scratch.q_stamp.length := by
      rw [hlen.scratch_ok.q_stamp_len, m6_zext32_toNat]; omega
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
      (fun _ _ _ => by
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
              (fun _ => True)
              (fun _ _ _ => by c0_hsteps!; exact hQ _)
              (fun Jr hJr => by c0_hsplit <;> (c0_hsteps!; exact hJr _ trivial)))
          (fun Jn hJn => by c0_hsplit <;> (c0_hsteps!; exact hJn _ trivial)))
      (fun Jp hJp => by c0_hsplit <;> (c0_hsteps!; exact hJp _ trivial))

/-- Contract for `full_bve_heap_up_m6`: sifts `v` up in the `work_stk1` max-heap. -/
def fullBveHeapUpM6Spec : Spec [i64, i64, i32] [] := fun (h, _hlen, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' → Q () m'

theorem fullBveHeapUpM6Spec_noExit :
    ∀ xs m Q X, fullBveHeapUpM6Spec xs m Q X →
      fullBveHeapUpM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveHeapUpM6Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h hlen : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hl : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' → Q () m') :
    fullBveHeapUpM6Spec (h, hlen, v, ()) m Q X :=
  ⟨c, s, R, hh, hl, hm, hQ⟩

/-- Parametric `Func.wp` proof for `full_bve_heap_up_m6`. -/
theorem full_bve_heap_up_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBveHeapUpM6Spec a m Q X →
      Func.wp Γ full_bve_heap_up_m6_body a m Q X := by
  rintro ⟨h, hlen, v, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hl0.core_ok.cur_vars_le
  have hws1_0 := hl0.scratch_ok.work_stk1_len
  have hss_0 := hl0.scratch_ok.sim_sig_len
  unfold Func.wp full_bve_heap_up_m6_body
  c0_hsplit
  · c0_hsteps!; exact hQ s.scratch.work_stk1 m0 hws1_0 hm0
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
    c0_hsplit
    · c0_hsteps!; exact hQ s.scratch.work_stk1 m0 hws1_0 hm0
    · have hhl_le : hlen.toNat ≤ s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
      have hmv_eq : (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat =
          (c.max_vars + v.toNat) % 2 ^ 64 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, m6_zext32_toNat]
        exact congrArg (· % 2 ^ 64) (congrArg (· + v.toNat) (Nat.mod_eq_of_lt (by omega)))
      have hmv_v : (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat <
          s.scratch.work_stk1.length := by rw [hws1_0]; c0_bound
      have hv_ss : (v.setWidth 64).toNat < s.scratch.sim_sig.length := by
        rw [hss_0, m6_zext32_toNat]; omega
      c0_hsplit
      · c0_hsteps!; exact hQ s.scratch.work_stk1 m0 hws1_0 hm0
      · have hp0_lt : (s.scratch.work_stk1[(BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat]'
            hmv_v).toNat < hlen.toNat := by
          rw [m6_getElem_congr hmv_eq hmv_v (by rw [← hmv_eq]; exact hmv_v)]; omega
        c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
          (fun (pb, ()) mb => ∃ ws1 : List (BitVec 32),
            ws1.length = 2 * c.max_vars ∧ pb.toNat < hlen.toNat ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) mb)
          (fun rem (p, ()) mp => ∃ ws1 : List (BitVec 32),
            ws1.length = 2 * c.max_vars ∧ p.toNat < hlen.toNat ∧ rem = p.toNat ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) mp)
          ?_ ?_ ?_
        · rintro _ ⟨pb, ⟨⟩⟩ mb ⟨ws1, hws1, hpb_lt, hmb⟩
          have hpb_b : pb.toNat < ws1.length := by omega
          have hmv_vb : (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat < ws1.length := by
            rw [hws1]; c0_bound
          c0_hsteps!
          exact hQ _ _ (by simp [hws1]) hm
        · rintro B L rem ⟨p, ⟨⟩⟩ mp hB hL ⟨ws1, hws1, hp_lt, rfl, hmp⟩
          c0_hsplit
          · have hp_pos : 0 < p.toNat := hc
            have hpar_eq : ((p - 1#64) >>> (1 : Nat)).toNat = (p.toNat - 1) / 2 :=
              m6_shr1_lt hp_pos
            have hpar_lt : ((p - 1#64) >>> (1 : Nat)).toNat < p.toNat := by omega
            have hpar_b : ((p - 1#64) >>> (1 : Nat)).toNat < ws1.length := by omega
            let pv := ws1[((p - 1#64) >>> (1 : Nat)).toNat]'hpar_b
            c0_hsplit
            · c0_hsteps!; exact hB (p, ()) mp ⟨ws1, hws1, hp_lt, hmp⟩
            · have hpv_lt : pv.toNat < s.core.cur_vars := by
                have hc' : ¬s.core.cur_vars % 2 ^ 64 ≤ pv.toNat := hc
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc'
                omega
              have hpv_ss : (pv.setWidth 64).toNat < s.scratch.sim_sig.length := by
                rw [hss_0, m6_zext32_toNat]; omega
              c0_hsplit
              · c0_hsteps!; exact hB (p, ()) mp ⟨ws1, hws1, hp_lt, hmp⟩
              · have hp_b : p.toNat < ws1.length := by omega
                have hmv_pv : (BitVec.ofNat 64 c.max_vars + pv.setWidth 64).toNat <
                    ws1.length := by rw [hws1]; c0_bound
                c0_hsteps!
                exact hL ((p - 1#64) >>> (1 : Nat)).toNat ((p - 1#64) >>> (1 : Nat), ()) _
                  hpar_lt ⟨_, by simp [hws1], by omega, rfl, hm⟩
          · c0_hsteps!; exact hB (p, ()) mp ⟨ws1, hws1, hp_lt, hmp⟩
        · intro _ L _ hL; c0_hsteps!
          exact hL _ (_, ()) m0 ⟨s.scratch.work_stk1, hws1_0, by
            rw [m6_zext32_toNat]; exact hp0_lt, rfl, hm0⟩

/-- Contract for `full_bve_heap_down_m6`: sifts `v` down in the `work_stk1` max-heap. -/
def fullBveHeapDownM6Spec : Spec [i64, i64, i32] [] := fun (h, _hlen, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' → Q () m'

theorem fullBveHeapDownM6Spec_noExit :
    ∀ xs m Q X, fullBveHeapDownM6Spec xs m Q X →
      fullBveHeapDownM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveHeapDownM6Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h hlen : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hl : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' → Q () m') :
    fullBveHeapDownM6Spec (h, hlen, v, ()) m Q X :=
  ⟨c, s, R, hh, hl, hm, hQ⟩

/-- Parametric `Func.wp` proof for `full_bve_heap_down_m6`. -/
theorem full_bve_heap_down_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBveHeapDownM6Spec a m Q X →
      Func.wp Γ full_bve_heap_down_m6_body a m Q X := by
  rintro ⟨h, hlen, v, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hl0.core_ok.cur_vars_le
  have hws1_0 := hl0.scratch_ok.work_stk1_len
  have hss_0 := hl0.scratch_ok.sim_sig_len
  unfold Func.wp full_bve_heap_down_m6_body
  c0_hsplit
  · c0_hsteps!; exact hQ s.scratch.work_stk1 m0 hws1_0 hm0
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
    c0_hsplit
    · c0_hsteps!; exact hQ s.scratch.work_stk1 m0 hws1_0 hm0
    · have hhl_le : hlen.toNat ≤ s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
      have hmv_eq : (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat =
          (c.max_vars + v.toNat) % 2 ^ 64 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, m6_zext32_toNat]
        exact congrArg (· % 2 ^ 64) (congrArg (· + v.toNat) (Nat.mod_eq_of_lt (by omega)))
      have hmv_v : (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat <
          s.scratch.work_stk1.length := by rw [hws1_0]; c0_bound
      have hv_ss : (v.setWidth 64).toNat < s.scratch.sim_sig.length := by
        rw [hss_0, m6_zext32_toNat]; omega
      c0_hsplit
      · c0_hsteps!; exact hQ s.scratch.work_stk1 m0 hws1_0 hm0
      · have hp0_lt : (s.scratch.work_stk1[(BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat]'
            hmv_v).toNat < hlen.toNat := by
          rw [m6_getElem_congr hmv_eq hmv_v (by rw [← hmv_eq]; exact hmv_v)]; omega
        c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
          (fun (pb, ()) mb => ∃ ws1 : List (BitVec 32),
            ws1.length = 2 * c.max_vars ∧ pb.toNat < hlen.toNat ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) mb)
          (fun rem (p, ()) mp => ∃ ws1 : List (BitVec 32),
            ws1.length = 2 * c.max_vars ∧ p.toNat < hlen.toNat ∧
            rem = hlen.toNat - p.toNat ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) mp)
          ?_ ?_ ?_
        · rintro _ ⟨pb, ⟨⟩⟩ mb ⟨ws1, hws1, hpb_lt, hmb⟩
          have hpb_b : pb.toNat < ws1.length := by omega
          have hmv_vb : (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat < ws1.length := by
            rw [hws1]; c0_bound
          c0_hsteps!
          exact hQ _ _ (by simp [hws1]) hm
        · rintro B L rem ⟨p, ⟨⟩⟩ mp hB hL ⟨ws1, hws1, hp_lt, rfl, hmp⟩
          c0_hsplit
          · have hl_eq : ((p <<< (1 : Nat)) + 1#64).toNat = 2 * p.toNat + 1 :=
              m6_shl1_add1_toNat (by omega)
            c0_hsplit
            · c0_hsteps!; exact hB (p, ()) mp ⟨ws1, hws1, hp_lt, hmp⟩
            · have hl_lt : ((p <<< (1 : Nat)) + 1#64).toNat < hlen.toNat := by
                rw [m6_bv64_one_toNat,
                  Nat.mod_eq_of_lt (by omega : 2 * p.toNat + 1 < 18446744073709551616)] at hc
                rw [hl_eq]; omega
              have hl_b : ((p <<< (1 : Nat)) + 1#64).toNat < ws1.length := by omega
              let bv0 := ws1[((p <<< (1 : Nat)) + 1#64).toNat]'hl_b
              c0_hsplit
              · c0_hsteps!; exact hB (p, ()) mp ⟨ws1, hws1, hp_lt, hmp⟩
              · have hbv0_lt : bv0.toNat < s.core.cur_vars := by
                  have hidx_hc : (2 * p.toNat + BitVec.toNat (1 : BitVec 64)) %
                      18446744073709551616 = ((p <<< (1 : Nat)) + 1#64).toNat := by
                    rw [m6_bv64_one_toNat, hl_eq]; omega
                  have hws_hc : ws1[(2 * p.toNat + BitVec.toNat (1 : BitVec 64)) %
                      18446744073709551616]'(by rw [hidx_hc]; exact hl_b) = bv0 :=
                    m6_getElem_congr hidx_hc _ hl_b
                  rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                  have hc' : ¬s.core.cur_vars ≤ bv0.toNat := by rwa [hws_hc] at hc
                  omega
                have hbv0_ss : (bv0.setWidth 64).toNat < s.scratch.sim_sig.length := by
                  rw [hss_0, m6_zext32_toNat]; omega
                c0_hsteps_nogrp
                refine wp_join_state_pure (ts := [i32, i64, i64])
                  (α := BitVec 32 × BitVec 64 × BitVec 64)
                  (fun x => (x.1, x.2.1, x.2.2, ()))
                  (fun x => x.1.toNat < s.core.cur_vars ∧
                    p.toNat < x.2.2.toNat ∧ x.2.2.toNat < hlen.toNat)
                  (fun _ ⟨bv, bk, best⟩ ⟨hbv_lt, hp_best, hbest_lt⟩ => by
                    dsimp only at hbv_lt hp_best hbest_lt
                    c0_hsplit
                    · c0_hsteps!; exact hB (p, ()) mp ⟨ws1, hws1, hp_lt, hmp⟩
                    · have hp_b : p.toNat < ws1.length := by omega
                      have hmv_bv : (BitVec.ofNat 64 c.max_vars + bv.setWidth 64).toNat <
                          ws1.length := by rw [hws1]; c0_bound
                      c0_hsteps!
                      exact hL (hlen.toNat - best.toNat) (best, ()) _ (by omega)
                        ⟨_, by simp [hws1], hbest_lt, rfl, hm⟩)
                  (fun Jr hJr => by
                    have hr_eq : (((p <<< (1 : Nat)) + 1#64) + 1#64).toNat = 2 * p.toNat + 2 := by
                      rw [BitVec.toNat_add, hl_eq]; simp; omega
                    c0_hsplit
                    · have hr_lt : (((p <<< (1 : Nat)) + 1#64) + 1#64).toNat < hlen.toNat := by
                        rw [m6_bv64_one_toNat,
                          Nat.mod_eq_of_lt
                            (by omega : 2 * p.toNat + 1 + 1 < 18446744073709551616)] at hc
                        rw [hr_eq]; omega
                      have hr_b : (((p <<< (1 : Nat)) + 1#64) + 1#64).toNat < ws1.length := by
                        omega
                      let rv := ws1[(((p <<< (1 : Nat)) + 1#64) + 1#64).toNat]'hr_b
                      c0_hsteps_nogrp
                      refine LeanQbe.T.wp_unroll_group fun Jin hJin => ?_
                      c0_hsplit
                      · have hrv_lt : rv.toNat < s.core.cur_vars := by
                          have hidx_hc : (2 * p.toNat + BitVec.toNat (1 : BitVec 64) +
                              BitVec.toNat (1 : BitVec 64)) % 18446744073709551616 =
                              (((p <<< (1 : Nat)) + 1#64) + 1#64).toNat := by
                            rw [m6_bv64_one_toNat, hr_eq]; omega
                          have hws_hc : ws1[(2 * p.toNat + BitVec.toNat (1 : BitVec 64) +
                              BitVec.toNat (1 : BitVec 64)) % 18446744073709551616]'(by
                                rw [hidx_hc]; exact hr_b) = rv :=
                            m6_getElem_congr hidx_hc _ hr_b
                          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                          have hc' : rv.toNat < s.core.cur_vars := by rwa [hws_hc] at hc
                          exact hc'
                        have hrv_ss : (rv.setWidth 64).toNat < s.scratch.sim_sig.length := by
                          rw [hss_0, m6_zext32_toNat]; omega
                        c0_hsplit
                        · c0_hsteps!
                          refine hJr (rv, s.scratch.sim_sig[(rv.setWidth 64).toNat]'hrv_ss,
                            ((p <<< (1 : Nat)) + 1#64) + 1#64) ⟨hrv_lt, ?_, hr_lt⟩
                          dsimp only; rw [hr_eq]; omega
                        · c0_hsteps!
                          refine hJr (bv0, s.scratch.sim_sig[(bv0.setWidth 64).toNat]'hbv0_ss,
                            (p <<< (1 : Nat)) + 1#64) ⟨hbv0_lt, ?_, hl_lt⟩
                          dsimp only; rw [hl_eq]; omega
                      · c0_hsteps!
                        refine hJr (bv0, s.scratch.sim_sig[(bv0.setWidth 64).toNat]'hbv0_ss,
                          (p <<< (1 : Nat)) + 1#64) ⟨hbv0_lt, ?_, hl_lt⟩
                        dsimp only; rw [hl_eq]; omega
                    · c0_hsteps!
                      refine hJr (bv0, s.scratch.sim_sig[(bv0.setWidth 64).toNat]'hbv0_ss,
                        (p <<< (1 : Nat)) + 1#64) ⟨hbv0_lt, ?_, hl_lt⟩
                      dsimp only; rw [hl_eq]; omega)
          · cases hc
        · intro _ L _ hL; c0_hsteps!
          exact hL _ (_, ()) m0 ⟨s.scratch.work_stk1, hws1_0, by
            rw [m6_zext32_toNat]; exact hp0_lt, rfl, hm0⟩

/-- Contract for `full_bve_heap_push_m6`: inserts or updates `v` in the `work_stk1`/`sim_sig`
max-heap, preserving `hlen ≤ cur_vars`. -/
def fullBveHeapPushM6Spec : Spec [i64, i64, i32] [i64] := fun (h, hlen, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ hlen' ws1' ss' m',
      ws1'.length = 2 * c.max_vars → ss'.length = c.max_vars →
      (hlen.toNat ≤ s.core.cur_vars → hlen'.toNat ≤ s.core.cur_vars) →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } ⋆
        R) m' →
      Q (hlen', ()) m'

theorem fullBveHeapPushM6Spec_noExit :
    ∀ xs m Q X, fullBveHeapPushM6Spec xs m Q X →
      fullBveHeapPushM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveHeapPushM6Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h hlen : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hh : h = c.hdr) (hl : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ hlen' ws1' ss' m',
      ws1'.length = 2 * c.max_vars → ss'.length = c.max_vars →
      (hlen.toNat ≤ s.core.cur_vars → hlen'.toNat ≤ s.core.cur_vars) →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } ⋆
        R) m' →
      Q (hlen', ()) m') :
    fullBveHeapPushM6Spec (h, hlen, v, ()) m Q X :=
  ⟨c, s, R, hh, hl, hm, hQ⟩

/-- Parametric `Func.wp` proof for `full_bve_heap_push_m6`. -/
theorem full_bve_heap_push_m6_wp (Γ : Env)
    (hKey : ∀ a m Q X, fullBveVarKeyM6Spec a m Q X →
      Γ "full_bve_var_key_m6" [i64, i32] [i64] a m Q X)
    (hUp : ∀ a m Q X, fullBveHeapUpM6Spec a m Q X →
      Γ "full_bve_heap_up_m6" [i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fullBveHeapDownM6Spec a m Q X →
      Γ "full_bve_heap_down_m6" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBveHeapPushM6Spec a m Q X →
      Func.wp Γ full_bve_heap_push_m6_body a m Q X := by
  rintro ⟨h, hlen, v, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hl0.core_ok.cur_vars_le
  have hws1_0 := hl0.scratch_ok.work_stk1_len
  have hss_0 := hl0.scratch_ok.sim_sig_len
  unfold Func.wp full_bve_heap_push_m6_body
  c0_hsplit
  · c0_hsteps!; exact hQ hlen s.scratch.work_stk1 s.scratch.sim_sig m0 hws1_0 hss_0 id hm0
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
    c0_hsplit
    · c0_hsteps!; exact hQ hlen s.scratch.work_stk1 s.scratch.sim_sig m0 hws1_0 hss_0 id hm0
    · have hhl_le : hlen.toNat ≤ s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
      c0_hsteps_nogrp
      m6_call hKey
      refine fullBveVarKeyM6Spec_intro rfl hl0 hm0 ?_
      intro nk
      have hv_ss : (v.setWidth 64).toNat < s.scratch.sim_sig.length := by
        rw [hss_0, m6_zext32_toNat]; omega
      have hmv_v : (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat <
          s.scratch.work_stk1.length := by rw [hws1_0]; c0_bound
      let ss1 := s.scratch.sim_sig.set (v.setWidth 64).toNat nk
      let s1 : FullState := { s with scratch := { s.scratch with sim_sig := ss1 } }
      have hss1_l : ss1.length = c.max_vars := by simp only [ss1, List.length_set, hss_0]
      have hl1 : s1.LengthsOk c := ⟨hl0.core_ok, { hl0.scratch_ok with sim_sig_len := hss1_l }⟩
      c0_hsplit
      · refine wp_join0 (P := fun mj => ∃ ws1' : List (BitVec 32),
          ws1'.length = 2 * c.max_vars ∧
          (FullMem c { s1 with scratch := { s1.scratch with work_stk1 := ws1' } } ⋆ R) mj)
          (fun _ mj ⟨ws1', hws1', hmj⟩ => by
            c0_hsteps!; exact hQ hlen ws1' ss1 mj hws1' (by simp [ss1, hss_0]) id hmj)
          (fun J1 hJ1 => by
            c0_hsplit
            · c0_hsteps_nogrp
              m6_call hUp
              refine fullBveHeapUpM6Spec_intro rfl hl1 hm ?_
              intro ws1' m1 hws1' hm1
              c0_hsteps!; exact hJ1 m1 ⟨ws1', hws1', hm1⟩
            · refine wp_join0 (P := fun mj => ∃ ws1' : List (BitVec 32),
                ws1'.length = 2 * c.max_vars ∧
                (FullMem c { s1 with scratch := { s1.scratch with work_stk1 := ws1' } } ⋆ R) mj)
                (fun _ mj h => by c0_hsteps!; exact hJ1 mj h)
                (fun _ hJ2 => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    m6_call hDown
                    refine fullBveHeapDownM6Spec_intro rfl hl1 hm ?_
                    intro ws1' m1 hws1' hm1
                    c0_hsteps!; exact hJ2 m1 ⟨ws1', hws1', hm1⟩
                  · c0_hsteps!; exact hJ2 _ ⟨s.scratch.work_stk1, hws1_0, hm⟩))
      · c0_hsplit
        · c0_hsteps!; exact hQ hlen s.scratch.work_stk1 ss1 _ hws1_0 (by simp [ss1, hss_0]) id hm
        · have hhl_lt : hlen.toNat < s.core.cur_vars := by
            rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
          have hhl_b : hlen.toNat < s.scratch.work_stk1.length := by omega
          have hhl1 : (hlen + 1#64).toNat = hlen.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          let ws1_a := (s.scratch.work_stk1.set hlen.toNat v).set
            (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat (hlen.setWidth 32)
          let s2 : FullState :=
            { s1 with scratch := { s1.scratch with work_stk1 := ws1_a } }
          have hws1a_l : ws1_a.length = 2 * c.max_vars := by
            simp only [ws1_a, List.length_set, hws1_0]
          have hl2 : s2.LengthsOk c :=
            ⟨hl1.core_ok, { hl1.scratch_ok with work_stk1_len := hws1a_l }⟩
          m6_call hUp
          refine fullBveHeapUpM6Spec_intro rfl hl2 hm ?_
          intro ws1' m1 hws1' hm1
          c0_hsteps!
          exact hQ (hlen + 1#64) ws1' ss1 m1 hws1' (by simp [ss1, hss_0])
            (fun _ => by omega) hm1

/-- Contract for `full_bve_heap_pop_m6`: pops the max element of the `work_stk1` heap. -/
def fullBveHeapPopM6Spec : Spec [i64, i64] [i32] := fun (h, _hlen, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ v ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q (v, ()) m'

theorem fullBveHeapPopM6Spec_noExit :
    ∀ xs m Q X, fullBveHeapPopM6Spec xs m Q X →
      fullBveHeapPopM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveHeapPopM6Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h hlen : BitVec 64} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hl : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ v ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q (v, ()) m') :
    fullBveHeapPopM6Spec (h, hlen, ()) m Q X :=
  ⟨c, s, R, hh, hl, hm, hQ⟩

/-- Parametric `Func.wp` proof for `full_bve_heap_pop_m6`. -/
theorem full_bve_heap_pop_m6_wp (Γ : Env)
    (hDown : ∀ a m Q X, fullBveHeapDownM6Spec a m Q X →
      Γ "full_bve_heap_down_m6" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBveHeapPopM6Spec a m Q X →
      Func.wp Γ full_bve_heap_pop_m6_body a m Q X := by
  rintro ⟨h, hlen, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hl0.core_ok.cur_vars_le
  have hws1_0 := hl0.scratch_ok.work_stk1_len
  unfold Func.wp full_bve_heap_pop_m6_body
  c0_hsplit
  · c0_hsteps!; exact hQ 0xFFFFFFFF#32 s.scratch.work_stk1 m0 hws1_0 hm0
  · have hhl_ne : hlen ≠ 0#64 := hc
    have hhl_pos : 0 < hlen.toNat :=
      Classical.byContradiction fun h0 =>
        hhl_ne (BitVec.eq_of_toNat_eq (Nat.eq_zero_of_not_pos h0))
    c0_hsplit
    · c0_hsteps!; exact hQ 0xFFFFFFFF#32 s.scratch.work_stk1 m0 hws1_0 hm0
    · have hhl_le : hlen.toNat ≤ s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
      have h0_ws1 : 0 < s.scratch.work_stk1.length := by omega
      let top := s.scratch.work_stk1[0]'h0_ws1
      c0_hsteps_nogrp
      refine wp_join0 (P := fun mj => ∃ ws1 : List (BitVec 32),
        ws1.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) mj)
        (fun _ m1 ⟨ws1, hws1, hm1⟩ => by
          have hnlen_eq : (hlen - 1#64).toNat = hlen.toNat - 1 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join0 (P := fun mj => ∃ ws1' : List (BitVec 32),
            ws1'.length = 2 * c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) mj)
            (fun _ m2 ⟨ws1', hws1', hm2⟩ => by
              c0_hsteps! <;> exact hQ _ ws1' m2 hws1' hm2)
            (fun Jn hJn => by
              c0_hsplit
              · have hnl_b : (hlen - 1#64).toNat < ws1.length := by omega
                have h0_b : 0 < ws1.length := by omega
                let last := ws1[(hlen - 1#64).toNat]'hnl_b
                let ws1_a := ws1.set 0 last
                c0_hsteps_nogrp
                refine wp_join0 (P := fun mj => ∃ ws1' : List (BitVec 32),
                  ws1'.length = 2 * c.max_vars ∧
                  (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) mj)
                  (fun _ mj h => by c0_hsteps!; exact hJn mj h)
                  (fun _ hJl => by
                    c0_hsplit
                    · have hlast_lt : last.toNat < s.core.cur_vars := by
                        have hidx_l :
                            (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + hlen.toNat) % 2 ^ 64 =
                              (hlen - 1#64).toNat := by
                          rw [m6_bv64_one_toNat]; c0_bound
                        have hws_hc :
                            ws1[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) +
                                hlen.toNat) % 2 ^ 64]'(by rw [hidx_l]; exact hnl_b) =
                              last :=
                          m6_getElem_congr hidx_l _ hnl_b
                        have hlt_cv : s.core.cur_vars < 2 ^ 64 := by omega
                        rw [Nat.mod_eq_of_lt hlt_cv] at hc
                        rwa [hws_hc] at hc
                      have hmv_last : (BitVec.ofNat 64 c.max_vars + last.setWidth 64).toNat <
                          ws1_a.length := by simp [ws1_a, hws1]; c0_bound
                      c0_hsteps_nogrp
                      let ws1_b := ws1_a.set
                        (BitVec.ofNat 64 c.max_vars + last.setWidth 64).toNat 0#32
                      let sb : FullState :=
                        { s with scratch := { s.scratch with work_stk1 := ws1_b } }
                      have hws1b_l : ws1_b.length = 2 * c.max_vars := by
                        simp only [ws1_b, ws1_a, List.length_set, hws1]
                      have hlb : sb.LengthsOk c :=
                        ⟨hl0.core_ok, { hl0.scratch_ok with work_stk1_len := hws1b_l }⟩
                      m6_call hDown
                      refine fullBveHeapDownM6Spec_intro rfl hlb hm ?_
                      intro ws1' m2 hws1' hm2
                      c0_hsteps!; exact hJl m2 ⟨ws1', hws1', hm2⟩
                    · c0_hsteps!; exact hJl _ ⟨ws1_a, by simp [ws1_a, hws1], hm⟩)
              · c0_hsteps!; exact hJn m1 ⟨ws1, hws1, hm1⟩))
        (fun Jt hJt => by
          c0_hsplit
          · have htop_lt : top.toNat < s.core.cur_vars := by
              simp only [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)]
                at hc
              exact hc
            have hmv_top : (BitVec.ofNat 64 c.max_vars + top.setWidth 64).toNat <
                s.scratch.work_stk1.length := by rw [hws1_0]; c0_bound
            c0_hsteps!
            exact hJt _ ⟨_, by simp [hws1_0], hm⟩
          · c0_hsteps!; exact hJt m0 ⟨s.scratch.work_stk1, hws1_0, hm0⟩)

/-! ## 3. `full_bve_collect_nbrs_m6_wp` (Canonical `m3ElimCollectNbrsSpec`) -/

/-- Parametric `Func.wp` proof for `full_bve_collect_nbrs_m6`, directly certifying canonical
`FullM3CongBva.m3ElimCollectNbrsSpec`. -/
theorem full_bve_collect_nbrs_m6_wp (Γ : Env) :
    ∀ a m Q X, m3ElimCollectNbrsSpec a m Q X →
      Func.wp Γ full_bve_collect_nbrs_m6_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hden0, _htmk0, hm0, hQ⟩
  obtain ⟨F_cur, hdw0⟩ := hden0.exists_witness
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac
  have hlen0 := hdw0.1
  let cv := s.core.cur_vars
  have hcv_le : cv ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  have hml0 := hlen0.core_ok.min_clr_len_arr
  have hwl0 := hlen0.scratch_ok.work_stk2_len
  have hfl_len := hlen0.core_ok.flags_len
  have hv_len := hlen0.core_ok.vals_len
  have hwv_len := hlen0.core_ok.wvec_len
  have hws_len := hlen0.core_ok.wstk_len_arr
  have hwlen_le := hlen0.core_ok.wlen_le
  have har_len := hlen0.core_ok.arena_len_arr
  have hal_le := hlen0.core_ok.arena_len_le
  have hdw_s0 : DenseWatchesInv F_cur s.core := by
    have := hdw0.2.1.watches; unfold ModeWatchesInv at this
    simpa only [hdw0.2.2.2.2.2.2, ne_eq, not_false_eq_true, ↓reduceIte] using this
  let colSt := fun (mclr ws2 : List (BitVec 32)) =>
    ({ s with
      core := { s.core with min_clr := mclr },
      scratch := { s.scratch with work_stk2 := ws2 } } : FullState)
  unfold Func.wp full_bve_collect_nbrs_m6_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64, i32])
    (fun rem_s (nn, side, ()) ms => ∃ (mclr ws2 : List (BitVec 32)),
      mclr.length = c.max_vars ∧ ws2.length = 2 * c.max_vars ∧
      side.toNat ≤ 2 ∧ rem_s = 2 - side.toNat ∧ nn.toNat ≤ cv ∧
      (∀ k < nn.toNat, (ws2[k]?.getD 0#32).toNat < cv) ∧
      (FullMem c (colSt mclr ws2) ⋆ R) ms)
    ?_ ?_
  · rintro Ls rem_s ⟨nn, side, ⟨⟩⟩ ms hLs ⟨mclr, ws2, hml, hwl, hside_le, rfl, hnn_le, hsub, hms⟩
    c0_hsplit
    · have hside_lt : side.toNat < 2 := hc
      have hside1 : (side + 1#32).toNat = side.toNat + 1 := by c0_bound
      let lit := (v <<< (1 : Nat)) ||| side
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i64]) (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
        (fun x => (x.1, ()))
        (fun x mj => x.2.1.length = c.max_vars ∧ x.2.2.length = 2 * c.max_vars ∧
          x.1.toNat ≤ cv ∧ (∀ k < x.1.toNat, (x.2.2[k]?.getD 0#32).toNat < cv) ∧
          (FullMem c (colSt x.2.1 x.2.2) ⋆ R) mj)
        (fun _ ⟨nn', mclr', ws2'⟩ mj ⟨hml', hwl', hnn', hsub', hmj⟩ => by
          c0_hsteps!
          exact hLs (2 - (side + 1#32).toNat) (nn', side + 1#32, ()) mj (by omega)
            ⟨mclr', ws2', hml', hwl', by omega, rfl, hnn', hsub', hmj⟩)
        (fun Jlit hJlit => by
          c0_hsplit
          · have hlit_lt : lit.toNat < 2 * cv := by
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
              exact Nat.lt_of_lt_of_le hc (Nat.mod_le _ _)
            have hbd := hdw_s0.layout.bounds lit.toNat hlit_lt
            unfold fullWatchOffCore fullWatchSizeCore at hbd
            have hw0 : (lit.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by
              rw [hwv_len]; c0_bound
            have hw1 : ((lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < s.core.wvec.length := by
              rw [hwv_len]; c0_bound
            let off := (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hw0).setWidth 64
            let sz_l :=
              (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hw1).setWidth 64
            let end_p := off + sz_l
            have hoff_eq : off.toNat = fullWatchOffCore s.core lit.toNat := by
              unfold off fullWatchOffCore
              rw [m6_zext32_toNat, List.getElem?_eq_getElem (by rw [hwv_len]; omega),
                Option.getD_some]
              exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
            have hsz_eq : sz_l.toNat = fullWatchSizeCore s.core lit.toNat := by
              unfold sz_l fullWatchSizeCore
              rw [m6_zext32_toNat, List.getElem?_eq_getElem (by rw [hwv_len]; omega),
                Option.getD_some]
              exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
            have hbd_sum : off.toNat + sz_l.toNat ≤ s.core.wlen := by
              rw [hoff_eq, hsz_eq]; exact hbd
            have hend_eq : end_p.toNat = off.toNat + sz_l.toNat := by
              dsimp only [end_p]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            have hsum_c0 :
                ((s.core.wvec[2 * lit.toNat % 2 ^ 64]'(by rw [hwv_len]; omega)).toNat +
                  (s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hwv_len, m6_bv64_one_toNat]; omega)).toNat) % 2 ^ 64 = end_p.toNat := by
              have h1 : (s.core.wvec[2 * lit.toNat % 2 ^ 64]'(by
                  rw [hwv_len]; omega)).toNat = off.toNat := by
                rw [hoff_eq]; unfold fullWatchOffCore
                rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
                exact congrArg BitVec.toNat (m6_getElem_congr (by omega)
                  (by rw [hwv_len]; omega) (by rw [hwv_len]; omega))
              have h2 : (s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hwv_len, m6_bv64_one_toNat]; omega)).toNat = sz_l.toNat := by
                rw [hsz_eq]; unfold fullWatchSizeCore
                rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
                exact congrArg BitVec.toNat (m6_getElem_congr (by
                  rw [m6_bv64_one_toNat]; omega)
                  (by rw [hwv_len, m6_bv64_one_toNat]; omega) (by rw [hwv_len]; omega))
              rw [h1, h2, Nat.mod_eq_of_lt (by omega), hend_eq]
            c0_hsteps_nogrp
            refine wp_loop_break_group (brkTs := [i64, i64]) (lpTs := [i64, i64])
              (fun (nn_b, _, ()) mb => ∃ mclr_b ws2_b : List (BitVec 32),
                mclr_b.length = c.max_vars ∧ ws2_b.length = 2 * c.max_vars ∧
                nn_b.toNat ≤ cv ∧ (∀ k < nn_b.toNat, (ws2_b[k]?.getD 0#32).toNat < cv) ∧
                (FullMem c (colSt mclr_b ws2_b) ⋆ R) mb)
              (fun rem_p (nn_p, p, ()) mp => ∃ mclr_p ws2_p : List (BitVec 32),
                mclr_p.length = c.max_vars ∧ ws2_p.length = 2 * c.max_vars ∧
                p.toNat ≤ end_p.toNat ∧ rem_p = end_p.toNat - p.toNat ∧ nn_p.toNat ≤ cv ∧
                (∀ k < nn_p.toNat, (ws2_p[k]?.getD 0#32).toNat < cv) ∧
                DenseWatchSliceOk F_cur s.core lit.toNat p.toNat rem_p ∧
                (FullMem c (colSt mclr_p ws2_p) ⋆ R) mp)
              ?_ ?_ ?_
            · rintro _ ⟨nn_b, _, ⟨⟩⟩ mb ⟨mclr_b, ws2_b, hmlb, hwlb, hnnb, hsubb, hmb⟩
              c0_hsteps!; exact hJlit (nn_b, mclr_b, ws2_b) mb ⟨hmlb, hwlb, hnnb, hsubb, hmb⟩
            · rintro Bp Lp rem_p ⟨nn_p, p, ⟨⟩⟩ mp hBp hLp
                ⟨mclr_p, ws2_p, hmlp, hwlp, hp_le, hrem_p, hnnp, hsubp, hslice, hmp⟩
              c0_hsplit
              · have hp_lt : p.toNat < end_p.toNat := by
                  dsimp only [colSt] at hc
                  have hs_eq := hsum_c0; dsimp only [lit] at hs_eq
                  rw [hs_eq] at hc; exact hc
                have hp_ws : p.toNat < s.core.wstk.length := by omega
                have hp1 : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
                cases hslice with
                | empty => omega
                | @bin _ rem1 w0 hwp hflag _ _ _ hrest =>
                  have hw0_eq : s.core.wstk[p.toNat]'hp_ws = w0 := by
                    rw [List.getElem?_eq_getElem hp_ws] at hwp; exact Option.some.inj hwp
                  c0_hsplit
                  · let u := (w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [i64])
                      (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                      (fun x => (x.1, ()))
                      (fun x mj => x.2.1.length = c.max_vars ∧ x.2.2.length = 2 * c.max_vars ∧
                        x.1.toNat ≤ cv ∧ (∀ k < x.1.toNat, (x.2.2[k]?.getD 0#32).toNat < cv) ∧
                        (FullMem c (colSt x.2.1 x.2.2) ⋆ R) mj)
                      (fun _ ⟨nn_j, mclr_j, ws2_j⟩ mj ⟨hmlj, hwlj, hnnj, hsubj, hmj⟩ => by
                        c0_hsteps!
                        exact hLp rem1 (nn_j, p + 1#64, ()) mj (by omega)
                          ⟨mclr_j, ws2_j, hmlj, hwlj, by omega, by omega, hnnj, hsubj,
                           by rw [hp1]; exact hrest, hmj⟩)
                      (fun Ju hJu => by
                        c0_hsplit
                        · c0_hsplit
                          · have hu_lt : u.toNat < cv := by
                              rw [hw0_eq, Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)]
                                at hc
                              simp only [u, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                Nat.pow_one]
                              exact hc
                            have hu_fl : (u.setWidth 64).toNat < s.core.flags.length := by
                              rw [hfl_len, m6_zext32_toNat]; omega
                            have hu_fl' : ((((s.core.wstk[p.toNat]'hp_ws &&&
                                  0x7FFFFFFF#32) >>> (1 : Nat)).setWidth 64)).toNat <
                                s.core.flags.length := by rw [hw0_eq]; exact hu_fl
                            c0_hsplit
                            · have hu_vl : (u.setWidth 64 <<< (1 : Nat)).toNat <
                                  s.core.vals.length := by rw [hv_len]; c0_bound
                              have hu_vl' : (((((s.core.wstk[p.toNat]'hp_ws &&&
                                    0x7FFFFFFF#32) >>> (1 : Nat)).setWidth 64) <<<
                                    (1 : Nat))).toNat < s.core.vals.length := by
                                rw [hw0_eq]; exact hu_vl
                              c0_hsplit
                              · have hu_mc : (u.setWidth 64).toNat < mclr_p.length := by
                                  rw [hmlp, m6_zext32_toNat]; omega
                                have hu_mc' : ((((s.core.wstk[p.toNat]'hp_ws &&&
                                      0x7FFFFFFF#32) >>> (1 : Nat)).setWidth 64)).toNat <
                                    mclr_p.length := by rw [hw0_eq]; exact hu_mc
                                c0_hsplit
                                · c0_hsplit
                                  · have hnn_lt : nn_p.toNat < cv := by
                                      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)]
                                        at hc
                                      exact hc
                                    have hnn_b : nn_p.toNat < ws2_p.length := by omega
                                    have hnn1 : (nn_p + 1#64).toNat = nn_p.toNat + 1 := by c0_bound
                                    c0_hsteps!
                                    let u_stk :=
                                      (s.core.wstk[p.toNat]'hp_ws &&& 0x7FFFFFFF#32) >>> (1 : Nat)
                                    exact hJu (nn_p + 1#64,
                                        mclr_p.set (u_stk.setWidth 64).toNat 1#32,
                                        ws2_p.set nn_p.toNat u_stk) _
                                      ⟨by simp only [List.length_set, hmlp],
                                       by simp only [List.length_set, hwlp],
                                       by rw [hnn1]; exact hnn_lt,
                                       fun k hk => by
                                         rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hnn1 ▸ hk))
                                           with h | h
                                         · rw [List.getElem?_set_ne (by omega)]; exact hsubp k h
                                         · subst h
                                           rw [List.getElem?_set_self hnn_b, Option.getD_some]
                                           have heq : u_stk = u := by
                                             dsimp only [u_stk, u]; rw [hw0_eq]
                                           rw [heq]; exact hu_lt, hm⟩
                                  · c0_hsteps!; exact hJu (nn_p, mclr_p, ws2_p) mp
                                      ⟨hmlp, hwlp, hnnp, hsubp, hmp⟩
                                · c0_hsteps!; exact hJu (nn_p, mclr_p, ws2_p) mp
                                    ⟨hmlp, hwlp, hnnp, hsubp, hmp⟩
                              · c0_hsteps!; exact hJu (nn_p, mclr_p, ws2_p) mp
                                  ⟨hmlp, hwlp, hnnp, hsubp, hmp⟩
                            · c0_hsteps!; exact hJu (nn_p, mclr_p, ws2_p) mp
                                ⟨hmlp, hwlp, hnnp, hsubp, hmp⟩
                          · c0_hsteps!; exact hJu (nn_p, mclr_p, ws2_p) mp
                              ⟨hmlp, hwlp, hnnp, hsubp, hmp⟩
                        · c0_hsteps!; exact hJu (nn_p, mclr_p, ws2_p) mp
                            ⟨hmlp, hwlp, hnnp, hsubp, hmp⟩)
                  · rw [hw0_eq] at hc; exact absurd hc hflag
                | @occ _ rem2 w0 cr hwp hwp1 hflag _ _ href hrest =>
                  have hw0_eq : s.core.wstk[p.toNat]'hp_ws = w0 := by
                    rw [List.getElem?_eq_getElem hp_ws] at hwp; exact Option.some.inj hwp
                  have hp1_lt : (p + 1#64).toNat < end_p.toNat := by omega
                  have hp1_ws : (p + 1#64).toNat < s.core.wstk.length := by omega
                  have hp1_c0 : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                      p.toNat + 1 := by simp; omega
                  have hcr_eq :
                      s.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hws_len]; omega) = cr := by
                    rw [List.getElem?_eq_getElem (by rw [hws_len]; omega)] at hwp1
                    exact (m6_getElem_congr hp1_c0 _ _).trans (Option.some.inj hwp1)
                  have hcr_eq' : s.core.wstk[(p + 1#64).toNat]'hp1_ws = cr :=
                    (m6_getElem_congr (by c0_bound) _ _).trans hcr_eq
                  have hcr_eq_col :
                      (colSt mclr_p ws2_p).core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_ws = cr :=
                    hcr_eq'
                  have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
                  have hwf_cr := hdw0.2.1.arena.refs_wf cr.toNat href
                  have hcr_ar : (cr.setWidth 64).toNat < s.core.arena.length := by
                    rw [har_len, m6_zext32_toNat]; omega
                  have hcr_ar_stk :
                      ((s.core.wstk[(p + 1#64).toNat]'hp1_ws).setWidth 64).toNat <
                        s.core.arena.length := by rw [hcr_eq']; exact hcr_ar
                  have hcr_ar_stk0 :
                      ((s.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hws_len]; omega)).setWidth 64).toNat < s.core.arena.length := by
                    rw [hcr_eq]; exact hcr_ar
                  c0_hsplit
                  · rw [hw0_eq] at hc; exact absurd hflag hc
                  · c0_hsplit
                    · dsimp only [colSt] at hc
                      have hs_eq := hsum_c0; dsimp only [lit] at hs_eq
                      rw [hs_eq] at hc; omega
                    · c0_hsplit
                      · c0_hsteps!
                        exact hLp rem2 (nn_p, p + 1#64 + 1#64, ()) mp (by omega)
                          ⟨mclr_p, ws2_p, hmlp, hwlp, by omega, by omega, hnnp, hsubp,
                           by rw [hp2]; exact hrest, hmp⟩
                      · simp only [hcr_eq_col] at hc ⊢
                        have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by
                          rw [har_len]; c0_bound
                        have hcr2_col :
                            (cr.setWidth 64 + 2#64).toNat <
                              (colSt mclr_p ws2_p).core.arena.length := hcr2_ar
                        let sz_c := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
                        have hsz_c_eq : sz_c.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                          unfold sz_c fullArenaClauseSizeCore
                          rw [List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
                          exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                        c0_hsteps_nogrp
                        refine wp_loop_group (ts := [i64, i32])
                          (fun rem_k (nn_k, k, ()) mk => ∃ mclr_k ws2_k : List (BitVec 32),
                            mclr_k.length = c.max_vars ∧ ws2_k.length = 2 * c.max_vars ∧
                            k.toNat ≤ sz_c.toNat ∧ rem_k = sz_c.toNat - k.toNat ∧
                            nn_k.toNat ≤ cv ∧
                            (∀ i < nn_k.toNat, (ws2_k[i]?.getD 0#32).toNat < cv) ∧
                            (FullMem c (colSt mclr_k ws2_k) ⋆ R) mk)
                          ?_ ?_
                        · rintro Lk rem_k ⟨nn_k, k, ⟨⟩⟩ mk hLk
                            ⟨mclr_k, ws2_k, hmlk, hwlk, hk_le, rfl, hnnk, hsubk, hmk⟩
                          have hsz_c0 :
                              (colSt mclr_k ws2_k).core.arena[(cr.toNat +
                                BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                                  change (cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 <
                                    s.core.arena.length
                                  rw [har_len]; simp; omega) = sz_c :=
                            m6_getElem_congr (by c0_bound) _ _
                          c0_hsplit
                          · have hk_lt : k.toNat < sz_c.toNat := by rw [hsz_c0] at hc; exact hc
                            have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                            have hcri : (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                                s.core.arena.length := by rw [har_len]; c0_bound
                            let u :=
                              (s.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hcri) >>>
                                (1 : Nat)
                            c0_hsteps_nogrp
                            refine wp_join_state (ts := [i64])
                              (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                              (fun x => (x.1, ()))
                              (fun x mj => x.2.1.length = c.max_vars ∧
                                x.2.2.length = 2 * c.max_vars ∧ x.1.toNat ≤ cv ∧
                                (∀ i < x.1.toNat, (x.2.2[i]?.getD 0#32).toNat < cv) ∧
                                (FullMem c (colSt x.2.1 x.2.2) ⋆ R) mj)
                              (fun _ ⟨nn_j, mclr_j, ws2_j⟩ mj ⟨hmlj, hwlj, hnnj, hsubj, hmj⟩ => by
                                c0_hsteps!
                                exact hLk (sz_c.toNat - (k + 1#32).toNat) (nn_j, k + 1#32, ()) mj
                                  (by omega) ⟨mclr_j, ws2_j, hmlj, hwlj, by omega, rfl, hnnj,
                                    hsubj, hmj⟩)
                              (fun Ju hJu => by
                                c0_hsplit
                                · c0_hsplit
                                  · have hu_lt : u.toNat < cv := by
                                      have hu_eq : (cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                          k.toNat) % 2 ^ 64 =
                                          (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat := by
                                        rw [m6_bv64_three_toNat]; c0_bound
                                      have hcol_eq :
                                          (colSt mclr_k ws2_k).core.arena[(cr.toNat +
                                              BitVec.toNat (3 : BitVec 64) + k.toNat) % 2 ^ 64]'(by
                                                change (cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                                    k.toNat) % 2 ^ 64 < s.core.arena.length
                                                rw [hu_eq]; exact hcri) =
                                            s.core.arena[(cr.setWidth 64 + 3#64 +
                                              k.setWidth 64).toNat]'hcri :=
                                        m6_getElem_congr hu_eq _ hcri
                                      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)]
                                        at hc
                                      simp only [u, BitVec.toNat_ushiftRight,
                                        Nat.shiftRight_eq_div_pow, Nat.pow_one]
                                      rwa [hcol_eq] at hc
                                    have hu_fl : (u.setWidth 64).toNat < s.core.flags.length := by
                                      rw [hfl_len, m6_zext32_toNat]; omega
                                    c0_hsplit
                                    · have hu_vl : (u.setWidth 64 <<< (1 : Nat)).toNat <
                                          s.core.vals.length := by rw [hv_len]; c0_bound
                                      c0_hsplit
                                      · have hu_mc : (u.setWidth 64).toNat < mclr_k.length := by
                                          rw [hmlk, m6_zext32_toNat]; omega
                                        c0_hsplit
                                        · c0_hsplit
                                          · have hnn_lt : nn_k.toNat < cv := by
                                              rw [Nat.mod_eq_of_lt
                                                (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                                              exact hc
                                            have hnn_b : nn_k.toNat < ws2_k.length := by omega
                                            have hnn1 : (nn_k + 1#64).toNat = nn_k.toNat + 1 := by
                                              c0_bound
                                            c0_hsteps!
                                            exact hJu (nn_k + 1#64,
                                                mclr_k.set (u.setWidth 64).toNat 1#32,
                                                ws2_k.set nn_k.toNat u) _
                                              ⟨by simp only [List.length_set, hmlk],
                                               by simp only [List.length_set, hwlk],
                                               by rw [hnn1]; exact hnn_lt,
                                               fun i hi => by
                                                 rcases Nat.lt_or_eq_of_le
                                                     (Nat.lt_succ_iff.mp (hnn1 ▸ hi)) with h | h
                                                 · rw [List.getElem?_set_ne (by omega)]
                                                   exact hsubk i h
                                                 · subst h
                                                   rw [List.getElem?_set_self hnn_b,
                                                     Option.getD_some]
                                                   exact hu_lt, hm⟩
                                          · c0_hsteps!; exact hJu (nn_k, mclr_k, ws2_k) mk
                                              ⟨hmlk, hwlk, hnnk, hsubk, hmk⟩
                                        · c0_hsteps!; exact hJu (nn_k, mclr_k, ws2_k) mk
                                            ⟨hmlk, hwlk, hnnk, hsubk, hmk⟩
                                      · c0_hsteps!; exact hJu (nn_k, mclr_k, ws2_k) mk
                                          ⟨hmlk, hwlk, hnnk, hsubk, hmk⟩
                                    · c0_hsteps!; exact hJu (nn_k, mclr_k, ws2_k) mk
                                        ⟨hmlk, hwlk, hnnk, hsubk, hmk⟩
                                  · c0_hsteps!; exact hJu (nn_k, mclr_k, ws2_k) mk
                                      ⟨hmlk, hwlk, hnnk, hsubk, hmk⟩
                                · c0_hsteps!; exact hJu (nn_k, mclr_k, ws2_k) mk
                                    ⟨hmlk, hwlk, hnnk, hsubk, hmk⟩)
                          · c0_hsteps!
                            exact hLp rem2 (nn_k, p + 1#64 + 1#64, ()) mk (by omega)
                              ⟨mclr_k, ws2_k, hmlk, hwlk, by omega, by omega, hnnk, hsubk,
                               by rw [hp2]; exact hrest, hmk⟩
                        · intro Lk hLk; c0_hsteps!
                          exact hLk sz_c.toNat (nn_p, 0#32, ()) mp
                            ⟨mclr_p, ws2_p, hmlp, hwlp, Nat.zero_le _, by simp, hnnp, hsubp, hmp⟩
              · c0_hsteps!
                exact hBp (nn_p, p, ()) mp ⟨mclr_p, ws2_p, hmlp, hwlp, hnnp, hsubp, hmp⟩
            · intro _ Lp _ hLp; c0_hsteps!
              exact hLp sz_l.toNat (nn, off, ()) ms
                ⟨mclr, ws2, hml, hwl, by omega, by omega, hnn_le, hsub,
                 by rw [hoff_eq, hsz_eq]; exact hdw_s0.slices lit.toNat hlit_lt, hms⟩
          · c0_hsteps!; exact hJlit (nn, mclr, ws2) ms ⟨hml, hwl, hnn_le, hsub, hms⟩)
    · -- Clear `mclr[nbrs[0 ..< nn)]` and return `nn`
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64])
        (fun rem_c (ci, ()) mc => ∃ mclr_c : List (BitVec 32),
          mclr_c.length = c.max_vars ∧ ci.toNat ≤ nn.toNat ∧ rem_c = nn.toNat - ci.toNat ∧
          (FullMem c (colSt mclr_c ws2) ⋆ R) mc)
        ?_ ?_
      · rintro Lc rem_c ⟨ci, ⟨⟩⟩ mc hLc ⟨mclr_c, hmlc, hci_le, rfl, hmc⟩
        c0_hsplit
        · have hci_lt : ci.toNat < nn.toNat := hc
          have hci_w : ci.toNat < ws2.length := by omega
          have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by c0_bound
          have hu_lt : (ws2[ci.toNat]'hci_w).toNat < cv := by
            have := hsub ci.toNat hci_lt
            rwa [List.getElem?_eq_getElem hci_w, Option.getD_some] at this
          have hu_mc : ((ws2[ci.toNat]'hci_w).setWidth 64).toNat < mclr_c.length := by
            rw [hmlc, m6_zext32_toNat]; omega
          c0_hsteps!
          exact hLc (nn.toNat - (ci + 1#64).toNat) (ci + 1#64, ()) _ (by omega)
            ⟨_, by dsimp only [colSt]; rw [List.length_set, hmlc], by omega, rfl, hm⟩
        · c0_hsteps!
          exact hQ nn mclr_c ws2 mc
            ⟨{ hlen0.core_ok with min_clr_len_arr := hmlc },
             { hlen0.scratch_ok with work_stk2_len := hwl }⟩ hnn_le hsub hmc
      · intro Lc hLc; c0_hsteps!
        exact hLc nn.toNat (0#64, ()) ms ⟨mclr, hml, Nat.zero_le _, by simp, hms⟩
  · intro Ls hLs; c0_hsteps!
    exact hLs 2 (0#64, 0#32, ()) m0
      ⟨s.core.min_clr, s.scratch.work_stk2, hml0, hwl0, Nat.zero_le _, rfl, Nat.zero_le _,
       fun _ h => by simp at h, hm0⟩

/-! ## 4. `full_elim_bve_m6_wp` (Canonical `m3ElimBveSpec`) -/

/-- Parametric `Func.wp` proof for `full_elim_bve_m6`, directly certifying canonical
`FullM3CongBva.m3ElimBveSpec` (max-heap scheduling, `FL_ELIM_C` neighbor re-arming, and
completion-gated `elim_bound` progression `0 -> 1 -> 2 -> 4 -> 8 -> 16`). -/
theorem full_elim_bve_m6_wp (Γ : Env)
    (hFlush : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m6" [i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, fullBveHeapPushM6Spec a m Q X →
      Γ "full_bve_heap_push_m6" [i64, i64, i32] [i64] a m Q X)
    (hPop : ∀ a m Q X, fullBveHeapPopM6Spec a m Q X →
      Γ "full_bve_heap_pop_m6" [i64, i64] [i32] a m Q X)
    (hNbrs : ∀ a m Q X, m3ElimCollectNbrsSpec a m Q X →
      Γ "full_bve_collect_nbrs_m6" [i64, i32] [i64] a m Q X)
    (hBveVar : ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m6" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m3ElimBveSpec a m Q X →
      Func.wp Γ full_elim_bve_m6_body a m Q X := by
  rintro ⟨h, bve_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, htmk0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv0_le := hden0.lengths.core_ok.cur_vars_le
  have hmcl0 := hden0.lengths.core_ok.min_clr_len_arr
  unfold Func.wp full_elim_bve_m6_body
  c0_hsteps_nogrp
  -- Zero stale `min_clr[0..cur_vars)` marks left by `full_min_mark`/`full_hbr_dom`
  refine wp_loop_group (ts := [i64])
    (fun rem_c (ci, ()) mc => ∃ mclrc : List (BitVec 32),
      mclrc.length = c.max_vars ∧ ci.toNat ≤ s0.core.cur_vars ∧
      rem_c = s0.core.cur_vars - ci.toNat ∧
      (FullMem c { s0 with core := { s0.core with min_clr := mclrc } } ⋆ R) mc)
    ?_ (fun Lc hLc => by
      c0_hsteps!
      exact hLc s0.core.cur_vars (0#64, ()) m0
        ⟨s0.core.min_clr, hmcl0, Nat.zero_le _, by simp, hm0⟩)
  rintro Lc rem_c ⟨ci, ⟨⟩⟩ mc hLc ⟨mclrc, hmclrc, hci_le, rfl, hmc⟩
  c0_hsplit
  · have hci_lt : ci.toNat < s0.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hmcl_b : ci.toNat < mclrc.length := by omega
    have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by c0_bound
    c0_hsteps!
    exact hLc (s0.core.cur_vars - (ci + 1#64).toNat) (ci + 1#64, ()) _ (by omega)
      ⟨_, by simp [hmclrc], by omega, rfl, hm⟩
  let sz : FullState := { s0 with core := { s0.core with min_clr := mclrc } }
  have hdenz : FullDenseInv c F0 sz := by
    obtain ⟨F_cur, hw0⟩ := hden0.exists_witness
    exact FullDenseInvW.toDense
      ⟨⟨{ hw0.1.core_ok with min_clr_len_arr := hmclrc }, hw0.1.scratch_ok⟩,
       fullWitnessInv_with_min_clr hw0.2.1 mclrc, hw0.2.2.1, hw0.2.2.2.1,
       hw0.2.2.2.2.1, hw0.2.2.2.2.2.1, hw0.2.2.2.2.2.2⟩
  have htmkz : TmkZero sz := htmk0.congr rfl rfl
  c0_hsteps_nogrp
  -- Outer 16-round BVE loop
  refine wp_loop_break_group (brkTs := [i64, i64, .bool, i64]) (lpTs := [i64, i64, .bool, i64])
    (fun (_tr, _hl, _lre, _rd, ()) mb => ∃ sb : FullState,
      FullDenseInv c F0 sb ∧ TmkZero sb ∧ sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sb ⋆ R) mb)
    (fun rem_r (tried, hlen, _lre, round, ()) mr => ∃ sr : FullState,
      round.toNat ≤ 16 ∧ rem_r = 16 - round.toNat ∧
      tried.toNat ≤ bve_lim.toNat ∧ hlen.toNat ≤ sr.core.cur_vars ∧
      FullDenseInv c F0 sr ∧ TmkZero sr ∧ sr.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sr ⋆ R) mr)
    ?_ ?_ ?_
  · -- Post-outer-loop: completion-gated `elim_bound` progression (`0->1->2->4->8->16`) & return
    rintro _ ⟨_tr, _hl, _lre, _rd, ⟨⟩⟩ mb ⟨sb, hdenb, htmkb, hfub, hmb⟩
    c0_hsteps_nogrp
    refine wp_join0 (P := fun mf => ∃ sf : FullState,
      FullDenseInv c F0 sf ∧ TmkZero sf ∧ sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sf ⋆ R) mf)
      (fun _ mf ⟨sf, hdenf, htmkf, hfuf, hmf⟩ => by
        c0_hsteps!
        · exact hQ 20#64 sf mf hdenf htmkf hfuf (Or.inr rfl)
            (fun _ => hdenf.inconsistent_unsat hc) hmf
        · exact hQ 1#64 sf mf hdenf htmkf hfuf (Or.inl rfl) (fun h => by cases h) hmf)
      (fun Jf hJf => by
        c0_hsplit
        · have hcvb := hdenb.lengths.core_ok.cur_vars_le
          have hflb := hdenb.lengths.core_ok.flags_len
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
            (fun _ comp _ => by
              c0_hsteps_nogrp
              refine wp_join0 (P := fun mj => ∃ sj : FullState,
                  FullDenseInv c F0 sj ∧ TmkZero sj ∧ sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                  (FullMem c sj ⋆ R) mj)
                (fun _ mj h => by c0_hsteps!; exact hJf mj h)
                (fun _ hJc => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join0 (P := fun mj => ∃ sj : FullState,
                        FullDenseInv c F0 sj ∧ TmkZero sj ∧
                        sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj)
                      (fun _ mj h => by c0_hsteps!; exact hJc mj h)
                      (fun _ hJc2 => by
                        c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                            (fun x => (x, ())) (fun _ => True)
                            (fun _ nb0 _ => by
                              c0_hsteps_nogrp
                              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                                (fun x => (x, ())) (fun _ => True)
                                (fun _ nb _ => by
                                  c0_hsteps_nogrp
                                  let sb1 : FullState :=
                                    { sb with scratch := { sb.scratch with elim_bound := nb } }
                                  have hden1 : FullDenseInv c F0 sb1 :=
                                    m6_denseInv_with_scratch_keep6 hdenb
                                      { hdenb.lengths.scratch_ok with
                                        walk_vals_len := hdenb.lengths.scratch_ok.walk_vals_len }
                                      rfl rfl
                                  refine wp_loop_group (ts := [i64])
                                    (fun rem_k (k, ()) mk => ∃ flk : List (BitVec 32),
                                      flk.length = c.max_vars ∧ k.toNat ≤ sb.core.cur_vars ∧
                                      rem_k = sb.core.cur_vars - k.toNat ∧
                                      (FullMem c
                                        { sb1 with core := { sb1.core with flags := flk } } ⋆ R)
                                        mk)
                                    ?_ ?_
                                  · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk
                                      ⟨flk, hflk, hk_le, rfl, hmk⟩
                                    c0_hsplit
                                    · have hk_lt : k.toNat < sb.core.cur_vars := by
                                        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                      have hk_b : k.toNat < flk.length := by omega
                                      have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                                      c0_hsteps!
                                      exact hLk (sb.core.cur_vars - (k + 1#64).toNat)
                                        (k + 1#64, ()) _ (by omega)
                                        ⟨_, by simp [hflk], by omega, rfl, hm⟩
                                    · c0_hsteps!
                                      let sf : FullState :=
                                        { sb1 with core := { sb1.core with flags := flk } }
                                      exact hJc2 mk ⟨sf, m6_denseInv_with_flags6 hden1 hflk,
                                        htmkb.congr rfl rfl, hfub, hmk⟩
                                  · intro Lk hLk; c0_hsteps!
                                    exact hLk sb.core.cur_vars (0#64, ()) _
                                      ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hm⟩)
                                (fun Jm hJm => by c0_hsplit <;> (c0_hsteps!; exact hJm _ trivial)))
                            (fun Jb hJb => by c0_hsplit <;> (c0_hsteps!; exact hJb _ trivial))
                        · c0_hsteps!; exact hJc2 mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)
                  · c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i64])
                      (fun rem_k (k, ()) mk => ∃ flk : List (BitVec 32),
                        flk.length = c.max_vars ∧ k.toNat ≤ sb.core.cur_vars ∧
                        rem_k = sb.core.cur_vars - k.toNat ∧
                        (FullMem c { sb with core := { sb.core with flags := flk } } ⋆ R) mk)
                      ?_ ?_
                    · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk ⟨flk, hflk, hk_le, rfl, hmk⟩
                      c0_hsplit
                      · have hk_lt : k.toNat < sb.core.cur_vars := by
                          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                        have hk_b : k.toNat < flk.length := by omega
                        have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                        c0_hsteps!
                        exact hLk (sb.core.cur_vars - (k + 1#64).toNat) (k + 1#64, ()) _ (by omega)
                          ⟨_, by simp [hflk], by omega, rfl, hm⟩
                      · c0_hsteps!
                        let sf : FullState := { sb with core := { sb.core with flags := flk } }
                        exact hJc mk ⟨sf, m6_denseInv_with_flags6 hdenb hflk, htmkb.congr rfl rfl,
                          hfub, hmk⟩
                    · intro Lk hLk; c0_hsteps!
                      exact hLk sb.core.cur_vars (0#64, ()) mb
                        ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hmb⟩))
            (fun Jc hJc => by c0_hsteps! <;> exact hJc _ trivial)
        · c0_hsteps!; exact hJf mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)
  · -- Outer loop body
    rintro Br Lr rem_r ⟨tried, hlen, lre, round, ⟨⟩⟩ mr hBr hLr
      ⟨sr, hrd_le, rfl, htr_le, hhl_le, hdenr, htmkr, hfur, hmr⟩
    have hbrk_r : Br (tried, hlen, lre, round, ()) mr :=
      hBr (tried, hlen, lre, round, ()) mr ⟨sr, hdenr, htmkr, hfur, hmr⟩
    c0_hsplit
    · have hrd_lt : round.toNat < 16 := hc
      have hrd1 : (round + 1#64).toNat = round.toNat + 1 := by c0_bound
      c0_hsplit
      · have htr_lt : tried.toNat < bve_lim.toNat := hc
        c0_hsplit
        · c0_hsplit
          · c0_hsplit
            · c0_hsteps_nogrp
              obtain ⟨F_cur, hdwr⟩ := hdenr.exists_witness
              m6_call hFlush
              refine fullDenseFlushUnitsM6Spec_intro rfl hdwr hmr ?_
              intro ok_u su mu hdwu hcvu _ hfuu _ htmku _ _ _ _ _ hfu_uns hmu
              have hdenu : FullDenseInv c F0 su := hdwu.toDense
              have htmku' : TmkZero su := htmkr.congr hcvu htmku
              have hfuu' : su.core.fuel.toNat ≤ s0.core.fuel.toNat := by rw [hfuu]; exact hfur
              c0_hsplit
              · have hcvu_le := hdwu.1.core_ok.cur_vars_le
                have hws1u := hdwu.1.scratch_ok.work_stk1_len
                c0_hsteps_nogrp
                -- Reset `hp[mv + 0 ..< mv + cv]` to `0xFFFFFFFF`
                refine wp_loop_group (ts := [i64])
                  (fun rem_i (i, ()) mi => ∃ ws1 : List (BitVec 32),
                    ws1.length = 2 * c.max_vars ∧ i.toNat ≤ su.core.cur_vars ∧
                    rem_i = su.core.cur_vars - i.toNat ∧
                    (FullMem c { su with scratch := { su.scratch with work_stk1 := ws1 } } ⋆ R) mi)
                  ?_ ?_
                · rintro Li rem_i ⟨i, ⟨⟩⟩ mi hLi ⟨ws1, hws1, hi_le, rfl, hmi⟩
                  c0_hsplit
                  · have hi_lt : i.toNat < su.core.cur_vars := by
                      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                    have hmv_i : (BitVec.ofNat 64 c.max_vars + i).toNat < ws1.length := by
                      rw [hws1]; c0_bound
                    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                    c0_hsteps!
                    exact hLi (su.core.cur_vars - (i + 1#64).toNat) (i + 1#64, ()) _ (by omega)
                      ⟨_, by simp [hws1], by omega, rfl, hm⟩
                  · let su1 : FullState :=
                      { su with scratch := { su.scratch with work_stk1 := ws1 } }
                    have hdenu1 : FullDenseInv c F0 su1 :=
                      m6_denseInv_with_ws1_ss hdenu hws1 hdwu.1.scratch_ok.sim_sig_len
                    c0_hsteps_nogrp
                    -- Populate max-heap with active unassigned `FL_ELIM_C` candidates
                    refine wp_loop_group (ts := [i64, i64])
                      (fun rem_p (hl_p, ip, ()) mp => ∃ (ws1p : List (BitVec 32))
                          (ssp : List (BitVec 64)),
                        let sp : FullState :=
                          { su with scratch :=
                            { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                        ws1p.length = 2 * c.max_vars ∧ ssp.length = c.max_vars ∧
                        ip.toNat ≤ su.core.cur_vars ∧ rem_p = su.core.cur_vars - ip.toNat ∧
                        hl_p.toNat ≤ su.core.cur_vars ∧ (FullMem c sp ⋆ R) mp)
                      ?_ ?_
                    · rintro Lp rem_p ⟨hl_p, ip, ⟨⟩⟩ mp hLp
                        ⟨ws1p, ssp, hws1p, hssp, hip_le, rfl, hhlp_le, hmp⟩
                      let sp : FullState :=
                        { su with scratch :=
                          { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                      c0_hsplit
                      · have hip_lt : ip.toNat < su.core.cur_vars := by
                          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                        have hip1 : (ip + 1#64).toNat = ip.toNat + 1 := by c0_bound
                        have hip_fl : ip.toNat < su.core.flags.length := by
                          rw [hdwu.1.core_ok.flags_len]; omega
                        have hip_vl : (ip <<< (1 : Nat)).toNat < su.core.vals.length := by
                          rw [hdwu.1.core_ok.vals_len]; c0_bound
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i64])
                          (α := BitVec 64 × List (BitVec 32) × List (BitVec 64))
                          (fun x => (x.1, ()))
                          (fun x mj =>
                            let sj : FullState :=
                              { su with scratch :=
                                { su.scratch with work_stk1 := x.2.1, sim_sig := x.2.2 } }
                            x.2.1.length = 2 * c.max_vars ∧ x.2.2.length = c.max_vars ∧
                            x.1.toNat ≤ su.core.cur_vars ∧ (FullMem c sj ⋆ R) mj)
                          (fun _ ⟨hl_j, ws1j, ssj⟩ mj ⟨hws1j, hssj, hhlj, hmj⟩ => by
                            c0_hsteps!
                            exact hLp (su.core.cur_vars - (ip + 1#64).toNat)
                              (hl_j, ip + 1#64, ()) mj (by omega)
                              ⟨ws1j, ssj, hws1j, hssj, by omega, rfl, hhlj, hmj⟩)
                          (fun Jp hJp => by
                            c0_hsplit
                            · c0_hsplit
                              · c0_hsteps_nogrp
                                m6_call hPush
                                refine fullBveHeapPushM6Spec_intro rfl
                                  (m6_denseInv_with_ws1_ss hdenu hws1p hssp).lengths hmp ?_
                                intro hl_n ws1n ssn mn hws1n hssn hhln hmn
                                c0_hsteps!
                                exact hJp (hl_n, ws1n, ssn) mn
                                  ⟨hws1n, hssn, hhln hhlp_le, hmn⟩
                              · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                                  ⟨hws1p, hssp, hhlp_le, hmp⟩
                            · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                                ⟨hws1p, hssp, hhlp_le, hmp⟩)
                      · have hdensp : FullDenseInv c F0 sp :=
                          m6_denseInv_with_ws1_ss hdenu hws1p hssp
                        have htmksp : TmkZero sp := htmku'.congr rfl rfl
                        c0_hsplit
                        · c0_hsteps!
                          exact hBr (tried, hl_p, false, round, ()) mp
                            ⟨sp, hdensp, htmksp, hfuu', hmp⟩
                        · -- Inner max-heap elimination loop
                          c0_hsteps_nogrp
                          refine wp_loop_break_group
                            (brkTs := [i64, i64, .bool]) (lpTs := [i64, i64, .bool])
                            (fun (tr_b, hl_b, re_b, ()) mb => ∃ sb : FullState,
                              tr_b.toNat ≤ bve_lim.toNat ∧ hl_b.toNat ≤ sb.core.cur_vars ∧
                              FullDenseInv c F0 sb ∧ TmkZero sb ∧
                              sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sb ⋆ R) mb)
                            (fun rem_h (tr_h, hl_h, re_h, ()) mh => ∃ sh : FullState,
                              tr_h.toNat ≤ bve_lim.toNat ∧ hl_h.toNat ≤ sh.core.cur_vars ∧
                              rem_h = (bve_lim.toNat - tr_h.toNat) * (c.max_vars + 1) +
                                hl_h.toNat ∧
                              FullDenseInv c F0 sh ∧ TmkZero sh ∧
                              sh.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sh ⋆ R) mh)
                            ?_ ?_ ?_
                          · rintro _ ⟨tr_b, hl_b, re_b, ⟨⟩⟩ mb
                              ⟨sb, htrb, hhlb, hdenb, htmkb, hfub, hmb⟩
                            c0_hsplit
                            · c0_hsteps!
                              exact hLr (16 - (round + 1#64).toNat)
                                (tr_b, hl_b, re_b, round + 1#64, ()) mb (by omega)
                                ⟨sb, by omega, rfl, htrb, hhlb, hdenb, htmkb, hfub, hmb⟩
                            · c0_hsteps!
                              exact hBr (tr_b, hl_b, re_b, round, ()) mb
                                ⟨sb, hdenb, htmkb, hfub, hmb⟩
                          · rintro Bh Lh rem_h ⟨tr_h, hl_h, re_h, ⟨⟩⟩ mh hBh hLh
                              ⟨sh, htrh, hhlh, rfl, hdenh, htmkh, hfuh, hmh⟩
                            have hbrk_h : Bh (tr_h, hl_h, re_h, ()) mh :=
                              hBh (tr_h, hl_h, re_h, ()) mh
                                ⟨sh, htrh, hhlh, hdenh, htmkh, hfuh, hmh⟩
                            c0_hsplit
                            · have hhl_pos : 0 < hl_h.toNat := hc
                              have hhl_dec : (hl_h - 1#64).toNat = hl_h.toNat - 1 := by c0_bound
                              c0_hsplit
                              · have htrh_lt : tr_h.toNat < bve_lim.toNat := hc
                                have htrh1 : (tr_h + 1#64).toNat = tr_h.toNat + 1 := by c0_bound
                                c0_hsplit
                                · c0_hsplit
                                  · c0_hsplit
                                    · c0_hsteps_nogrp
                                      m6_call hPop
                                      refine fullBveHeapPopM6Spec_intro rfl hdenh.lengths hmh ?_
                                      intro v ws1_1 m1 hws1_1 hm1
                                      let s1 : FullState :=
                                        { sh with scratch :=
                                          { sh.scratch with work_stk1 := ws1_1 } }
                                      have hden1 : FullDenseInv c F0 s1 :=
                                        m6_denseInv_with_ws1_ss hdenh hws1_1
                                          hdenh.lengths.scratch_ok.sim_sig_len
                                      have htmk1 : TmkZero s1 := htmkh.congr rfl rfl
                                      have hcv1_le := hden1.lengths.core_ok.cur_vars_le
                                      have hhl_dec1 : (hl_h - 1#64).toNat ≤ s1.core.cur_vars := by
                                        dsimp only [s1]; rw [hhl_dec]; omega
                                      c0_hsplit
                                      · c0_hsteps!
                                        exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                          (by rw [hhl_dec]; omega)
                                          ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                      · c0_hsplit
                                        · c0_hsteps!
                                          exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                            (by rw [hhl_dec]; omega)
                                            ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                        · have hv_lt : v.toNat < s1.core.cur_vars := by
                                            rw [Nat.mod_eq_of_lt
                                              (by omega : s1.core.cur_vars < 2 ^ 64)] at hc
                                            omega
                                          have hv_fl : (v.setWidth 64).toNat <
                                              s1.core.flags.length := by
                                            rw [hden1.lengths.core_ok.flags_len, m6_zext32_toNat]
                                            omega
                                          have hv_vl : (v.setWidth 64 <<< (1 : Nat)).toNat <
                                              s1.core.vals.length := by
                                            rw [hden1.lengths.core_ok.vals_len]; c0_bound
                                          c0_hsplit
                                          · c0_hsteps!
                                            exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                              (by rw [hhl_dec]; omega)
                                              ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                          · c0_hsplit
                                            · c0_hsteps!
                                              exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                                (by rw [hhl_dec]; omega)
                                                ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                            · c0_hsteps_nogrp
                                              let fl2 := s1.core.flags.set (v.setWidth 64).toNat
                                                (s1.core.flags[(v.setWidth 64).toNat]'hv_fl &&&
                                                  ~~~16#32)
                                              let s2 : FullState :=
                                                { s1 with core := { s1.core with flags := fl2 } }
                                              have hden2 : FullDenseInv c F0 s2 :=
                                                m6_denseInv_with_flags6 hden1
                                                  (by simp [fl2, hden1.lengths.core_ok.flags_len])
                                              have htmk2 : TmkZero s2 := htmk1.congr rfl rfl
                                              m6_call hNbrs
                                              refine ⟨c, F0, s2, R, rfl, hden2, htmk2, hm, ?_⟩
                                              intro nn mclr3 ws2_3 m3 _s3_n hl3 hnn_le hws2_lt hm3
                                              have hcv2_le := hden2.lengths.core_ok.cur_vars_le
                                              have hnn_mv : nn.toNat ≤ c.max_vars :=
                                                Nat.le_trans hnn_le hcv2_le
                                              let s3 : FullState :=
                                                { s2 with
                                                  core := { s2.core with min_clr := mclr3 },
                                                  scratch :=
                                                    { s2.scratch with work_stk2 := ws2_3 } }
                                              have hden3 : FullDenseInv c F0 s3 :=
                                                fullDenseInv_with_min_clr_work_stk2 hden2
                                                  hl3.core_ok.min_clr_len_arr
                                                  hl3.scratch_ok.work_stk2_len
                                              have htmk3 : TmkZero s3 := htmk2.congr rfl rfl
                                              c0_hsteps_nogrp
                                              m6_call hBveVar
                                              refine ⟨c, F0, s3, R, rfl, hden3, htmk3, hv_lt,
                                                hm3, ?_⟩
                                              intro st s4 m4 hden4 htmk4 hcv4 hfu4 hst_d hst20 hm4
                                              have hfu4' : s4.core.fuel.toNat ≤
                                                  s0.core.fuel.toNat := Nat.le_trans hfu4 hfuh
                                              have hcv4_le := hden4.lengths.core_ok.cur_vars_le
                                              have hhl_s4 : (hl_h - 1#64).toNat ≤
                                                  s4.core.cur_vars := by
                                                dsimp only [s3, s2, s1] at hcv4
                                                rw [hhl_dec]; omega
                                              have htr_s4 : (tr_h + 1#64).toNat ≤
                                                  bve_lim.toNat := by omega
                                              c0_hsplit
                                              · c0_hsteps!
                                                exact hQ 20#64 s4 m4 hden4 htmk4 hfu4'
                                                  (Or.inr rfl) (fun _ => hst20 hc) hm4
                                              · c0_hsplit
                                                · c0_hsteps!
                                                  exact hQ 20#64 s4 m4 hden4 htmk4 hfu4'
                                                    (Or.inr rfl)
                                                    (fun _ => hden4.inconsistent_unsat hc) hm4
                                                · c0_hsplit
                                                  · c0_hsteps!
                                                    exact hBh (tr_h + 1#64, hl_h - 1#64, re_h, ())
                                                      m4 ⟨s4, htr_s4, hhl_s4, hden4, htmk4,
                                                        hfu4', hm4⟩
                                                  · -- Neighbor `FL_ELIM_C` re-arm + max-heap push
                                                    have hcont_4 : ∀ (hl_f : BitVec 64)
                                                        (re_f : Bool) (sf : FullState)
                                                        (mf : Mem 64),
                                                        hl_f.toNat ≤ sf.core.cur_vars →
                                                        FullDenseInv c F0 sf → TmkZero sf →
                                                        sf.core.fuel.toNat ≤ s0.core.fuel.toNat →
                                                        (FullMem c sf ⋆ R) mf →
                                                        Lh (tr_h + 1#64, hl_f, re_f, ()) mf :=
                                                      fun hl_f re_f sf mf hhlf hdenf htmkf hfuf
                                                          hmf => by
                                                        have hcvf :=
                                                          hdenf.lengths.core_ok.cur_vars_le
                                                        have htr_sub : bve_lim.toNat - tr_h.toNat =
                                                            (bve_lim.toNat - (tr_h + 1#64).toNat) +
                                                              1 := by omega
                                                        refine hLh
                                                          ((bve_lim.toNat - (tr_h + 1#64).toNat) *
                                                            (c.max_vars + 1) + hl_f.toNat)
                                                          (tr_h + 1#64, hl_f, re_f, ()) mf ?_
                                                          ⟨sf, htr_s4, hhlf, rfl, hdenf, htmkf,
                                                            hfuf, hmf⟩
                                                        rw [htr_sub, Nat.add_mul, Nat.one_mul]
                                                        omega
                                                    refine wp_join_state (ts := [i64, .bool])
                                                      (α := BitVec 64 × Bool × FullState)
                                                      (fun x => (x.1, x.2.1, ()))
                                                      (fun x mj =>
                                                        x.1.toNat ≤ x.2.2.core.cur_vars ∧
                                                        FullDenseInv c F0 x.2.2 ∧ TmkZero x.2.2 ∧
                                                        x.2.2.core.fuel.toNat ≤
                                                          s0.core.fuel.toNat ∧
                                                        (FullMem c x.2.2 ⋆ R) mj)
                                                      (fun _ ⟨hl_f, re_f, sf⟩ mf
                                                          ⟨hhlf, hdenf, htmkf, hfuf, hmf⟩ => by
                                                        c0_hsteps!
                                                        exact hcont_4 hl_f re_f sf mf hhlf hdenf
                                                          htmkf hfuf hmf)
                                                      (fun Jn hJn => by
                                                        refine wp_join0 (P := fun mj => mj = m4)
                                                          (fun _ mj hmj => by
                                                            have hmj4 : (FullMem c s4 ⋆ R) mj :=
                                                              hmj ▸ hm4
                                                            let mkFl := @m6_denseInv_with_flags6
                                                            let mkWs := @m6_denseInv_with_ws1_ss
                                                            let mkPsh :=
                                                              @fullBveHeapPushM6Spec_intro
                                                            c0_hsteps_nogrp
                                                            refine wp_join_state_pure
                                                              (ts := [.bool]) (α := Bool)
                                                              (fun b => (b, ())) (fun _ => True)
                                                              (fun _ re_1 _ => by
                                                                c0_hsteps_nogrp
                                                                refine wp_loop_group
                                                                  (ts := [i64, i64])
                                                                  (fun rem_k (hl_k, k, ()) mk =>
                                                                    ∃ sk : FullState,
                                                                      k.toNat ≤ nn.toNat ∧
                                                                      rem_k = nn.toNat - k.toNat ∧
                                                                      hl_k.toNat ≤
                                                                        sk.core.cur_vars ∧
                                                                      sk.core.cur_vars =
                                                                        s4.core.cur_vars ∧
                                                                      FullDenseInv c F0 sk ∧
                                                                      TmkZero sk ∧
                                                                      sk.core.fuel.toNat ≤
                                                                        s0.core.fuel.toNat ∧
                                                                      (FullMem c sk ⋆ R) mk)
                                                                  ?_ ?_
                                                                · rintro Lk rem_k ⟨hl_k, k, ⟨⟩⟩ mk
                                                                    hLk ⟨sk, hk_le, rfl, hhlk, hcvk,
                                                                      hdenk, htmkk, hfuk, hmk⟩
                                                                  have hlkl := hdenk.lengths
                                                                  c0_hsplit
                                                                  · have hk_lt :
                                                                        k.toNat < nn.toNat := hc
                                                                    have hk1 : (k + 1#64).toNat =
                                                                        k.toNat + 1 := by c0_bound
                                                                    have hws2_k :=
                                                                      hlkl.scratch_ok.work_stk2_len
                                                                    have hk_w : k.toNat <
                                                                        sk.scratch.work_stk2.length
                                                                        := by omega
                                                                    let uk :=
                                                                      sk.scratch.work_stk2[
                                                                        k.toNat]'hk_w
                                                                    c0_hsteps_nogrp
                                                                    refine wp_join_state
                                                                      (ts := [i64])
                                                                      (α := BitVec 64 × FullState)
                                                                      (fun x => (x.1, ()))
                                                                      (fun x mj =>
                                                                        x.1.toNat ≤
                                                                          x.2.core.cur_vars ∧
                                                                        x.2.core.cur_vars =
                                                                          s4.core.cur_vars ∧
                                                                        FullDenseInv c F0 x.2 ∧
                                                                        TmkZero x.2 ∧
                                                                        x.2.core.fuel.toNat ≤
                                                                          s0.core.fuel.toNat ∧
                                                                        (FullMem c x.2 ⋆ R) mj)
                                                                      (fun _ ⟨hl_j, sj⟩ mj
                                                                          ⟨hhlj, hcvj, hdenj, htmkj,
                                                                            hfuj, hmj⟩ => by
                                                                        c0_hsteps!
                                                                        exact hLk
                                                                          (nn.toNat -
                                                                            (k + 1#64).toNat)
                                                                          (hl_j, k + 1#64, ()) mj
                                                                          (by omega)
                                                                          ⟨sj, by omega, rfl, hhlj,
                                                                            hcvj, hdenj, htmkj,
                                                                            hfuj, hmj⟩)
                                                                      (fun Jk hJk => by
                                                                        c0_hsplit
                                                                        · have huk_lt : uk.toNat <
                                                                              sk.core.cur_vars := by
                                                                            rw [← hcvk,
                                                                              Nat.mod_eq_of_lt
                                                                                (by omega :
                                                                                  sk.core.cur_vars <
                                                                                    2 ^ 64)] at hc
                                                                            exact hc
                                                                          have hflk_l :=
                                                                            hlkl.core_ok.flags_len
                                                                          have huk_fl :
                                                                              (uk.setWidth
                                                                                64).toNat <
                                                                                sk.core.flags.length
                                                                              := by
                                                                            rw [hflk_l,
                                                                              m6_zext32_toNat]
                                                                            omega
                                                                          c0_hsplit
                                                                          · have hvlk_l :=
                                                                              hlkl.core_ok.vals_len
                                                                            have huk_vl :
                                                                                (uk.setWidth 64 <<<
                                                                                  (1 : Nat)).toNat <
                                                                                sk.core.vals.length
                                                                                := by
                                                                              rw [hvlk_l]; c0_bound
                                                                            c0_hsplit
                                                                            · c0_hsteps_nogrp
                                                                              let u64 :=
                                                                                (uk.setWidth
                                                                                  64).toNat
                                                                              let fl_u :=
                                                                                sk.core.flags.set
                                                                                  u64
                                                                                  (sk.core.flags[
                                                                                    u64]'huk_fl |||
                                                                                    16#32)
                                                                              let su_k :
                                                                                  FullState :=
                                                                                { sk with core :=
                                                                                  { sk.core with
                                                                                    flags :=
                                                                                      fl_u } }
                                                                              have hflu_l :
                                                                                  fl_u.length =
                                                                                    c.max_vars := by
                                                                                simp only [fl_u,
                                                                                  List.length_set,
                                                                                  hflk_l]
                                                                              have hden_u :=
                                                                                mkFl (fl' := fl_u)
                                                                                  hdenk hflu_l
                                                                              m6_call hPush
                                                                              refine mkPsh rfl
                                                                                hden_u.lengths
                                                                                hm ?_
                                                                              intro hl_p ws1p ssp
                                                                                mp_ hws1p hssp hhlp
                                                                                hmp_
                                                                              c0_hsteps!
                                                                              let s_pu :
                                                                                FullState :=
                                                                                { su_k with
                                                                                  scratch :=
                                                                                    { su_k.scratch
                                                                                      with
                                                                                      work_stk1 :=
                                                                                        ws1p,
                                                                                      sim_sig :=
                                                                                        ssp } }
                                                                              exact hJk
                                                                                (hl_p, s_pu)
                                                                                mp_
                                                                                ⟨hhlp hhlk, hcvk,
                                                                                 mkWs hden_u hws1p
                                                                                   hssp,
                                                                                 htmkk.congr rfl
                                                                                   rfl,
                                                                                 hfuk, hmp_⟩
                                                                            · c0_hsteps!
                                                                              exact hJk (hl_k, sk)
                                                                                mk ⟨hhlk, hcvk,
                                                                                  hdenk, htmkk,
                                                                                  hfuk, hmk⟩
                                                                          · c0_hsteps!
                                                                            exact hJk (hl_k, sk) mk
                                                                              ⟨hhlk, hcvk, hdenk,
                                                                                htmkk, hfuk, hmk⟩
                                                                        · c0_hsteps!
                                                                          exact hJk (hl_k, sk) mk
                                                                            ⟨hhlk, hcvk, hdenk,
                                                                              htmkk, hfuk, hmk⟩)
                                                                  · c0_hsteps!
                                                                    exact hJn (hl_k, re_1, sk) mk
                                                                      ⟨hhlk, hdenk, htmkk, hfuk,
                                                                        hmk⟩
                                                                · intro Lk hLk; c0_hsteps!
                                                                  exact hLk nn.toNat
                                                                    (hl_h - 1#64, 0#64, ()) mj
                                                                    ⟨s4, Nat.zero_le _, by simp,
                                                                     by omega, rfl, hden4, htmk4,
                                                                     hfu4', hmj4⟩)
                                                              (fun Jre hJre => by
                                                                c0_hsplit <;>
                                                                  (c0_hsteps!;
                                                                    exact hJre _ trivial)))
                                                          (fun Jth hJth => by
                                                            c0_hsplit
                                                            · c0_hsteps!; exact hJth m4 rfl
                                                            · c0_hsplit
                                                              · c0_hsteps!; exact hJth m4 rfl
                                                              · c0_hsteps!
                                                                exact hJn (hl_h - 1#64, re_h, s4) m4
                                                                  ⟨by omega, hden4, htmk4, hfu4',
                                                                    hm4⟩))
                                    · c0_hsteps!; exact hbrk_h
                                  · c0_hsteps!; exact hbrk_h
                                · c0_hsteps!; exact hbrk_h
                              · c0_hsteps!; exact hbrk_h
                            · c0_hsteps!; exact hbrk_h
                          · intro _ Lh _ hLh; c0_hsteps!
                            exact hLh _ (tried, hl_p, false, ()) mp
                              ⟨sp, htr_le, hhlp_le, rfl, hdensp, htmksp, hfuu', hmp⟩
                    · intro Lp hLp; c0_hsteps!
                      exact hLp su.core.cur_vars (0#64, 0#64, ()) mi
                        ⟨ws1, su.scratch.sim_sig, hws1, hdwu.1.scratch_ok.sim_sig_len,
                         Nat.zero_le _, by simp, Nat.zero_le _, hmi⟩
                · intro Li hLi; c0_hsteps!
                  exact hLi su.core.cur_vars (0#64, ()) mu
                    ⟨su.scratch.work_stk1, hws1u, Nat.zero_le _, by simp, hmu⟩
              · c0_hsteps!
                exact hQ 20#64 su mu hdenu htmku' hfuu' (Or.inr rfl)
                  (fun _ => hfu_uns (by simpa using hc)) hmu
            · c0_hsteps!; exact hbrk_r
          · c0_hsteps!; exact hbrk_r
        · c0_hsteps!; exact hbrk_r
      · c0_hsteps!; exact hbrk_r
    · c0_hsteps!; exact hbrk_r
  · intro _ Lr _ hLr; c0_hsteps!
    exact hLr 16 (0#64, 0#64, false, 0#64, ()) mc
      ⟨sz, Nat.zero_le _, rfl, Nat.zero_le _, Nat.zero_le _, hdenz, htmkz, Nat.le_refl _, hmc⟩

/-! ## 5. `full_eliminate_m6_wp` (Canonical `FullFastSched.schedEliminateSpec`) -/

/-- Parametric `Func.wp` proof for `full_eliminate_m6`, directly certifying canonical
`FullFastSched.schedEliminateSpec`. -/
theorem full_eliminate_m6_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m6" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m6" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorHeapSpec a m Q X → Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedEliminateSpec a m Q X →
      Func.wp Γ full_eliminate_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hinv0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_eliminate_m6_body
  c0_hsteps_nogrp
  m6_call hDticks
  refine ⟨c, s0, R, rfl, hinv0.lengths, hm0, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  -- Join 1: after `if (!initial)` interval update
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, _, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      m6_call hEnter
      refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
      intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
      c0_hsplit
      · have hden2 : FullDenseInv c F0 s2 := hok_d hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun b => (b, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            m6_call hMin; intro fbud _
            c0_hsteps_nogrp
            m6_call hFwd
            refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
            intro fs s3 m3 hden3 hcv3 hfu3 _ huf3 hm3
            have hcv2_le := hden2.lengths.core_ok.cur_vars_le
            let s3r : FullState :=
              { s3 with scratch := { s3.scratch with fwd_sub_cnt := s2.scratch.fwd_sub_cnt } }
            have hden3r : FullDenseInv c F0 s3r :=
              m6_denseInv_with_scratch_keep6 hden3
                { hden3.lengths.scratch_ok with
                  walk_vals_len := hden3.lengths.scratch_ok.walk_vals_len } rfl rfl
            have hfu3r : s3r.core.fuel.toNat ≤ s0.core.fuel.toNat := by
              change s3.core.fuel.toNat ≤ s0.core.fuel.toNat; rw [hfu3]; omega
            c0_hsplit
            · c0_hsteps_nogrp
              m6_call hReb
              refine ⟨c, F0, s3r, R, rfl, hden3r, hm, ?_⟩
              intro _ s4 m4 hsp4 hcl4 hfu4 _ _ hm4
              c0_hsteps!
              exact hQ 20#64 s4 m4 hsp4 hcl4 (by omega) (Or.inr rfl) (fun _ => huf3 hc) hm4
            · -- Zero `tmk[0 ..< cv)` to establish `TmkZero` before `full_elim_bve_m6`
              let cv3 := s3r.core.cur_vars
              have hcv3_le : cv3 ≤ c.max_vars := hden3r.lengths.core_ok.cur_vars_le
              have htl3 := hden3r.lengths.scratch_ok.tarjan_mark_len
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i64])
                (fun rem_t (ti, ()) mt => ∃ tmki : List (BitVec 32),
                  tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv3 ∧ rem_t = cv3 - ti.toNat ∧
                  (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                  (FullMem c { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } } ⋆
                    R) mt)
                ?_ ?_
              · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨tmki, htli, hti_le, rfl, hinit, hmt⟩
                c0_hsplit
                · have hti_lt : ti.toNat < cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                  have hti_b : ti.toNat < tmki.length := by omega
                  have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by c0_bound
                  c0_hsteps!
                  exact hLt (cv3 - (ti + 1#64).toNat) (ti + 1#64, ()) _ (by omega)
                    ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega, rfl, fun k hk => by
                       rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hti1 ▸ hk)) with h | h
                       · rw [List.getElem?_set_ne (by omega)]; exact hinit k h
                       · subst h; rw [List.getElem?_set_self hti_b, Option.getD_some], hm⟩
                · have hti_eq : ti.toNat = cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc
                    change ¬ti.toNat < cv3 at hc
                    omega
                  rw [hti_eq] at hinit
                  let s3t : FullState :=
                    { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } }
                  have hden3t : FullDenseInv c F0 s3t :=
                    m6_denseInv_with_scratch_keep6 hden3r
                      { hden3r.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
                  have htmk3t : TmkZero s3t := m6_tmkZero_of_init hinit
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                    (fun b => (b, ())) (fun _ => True)
                    (fun _ bve_lim _ => by
                      c0_hsteps_nogrp
                      m6_call hBve
                      refine ⟨c, F0, s3t, R, rfl, hden3t, htmk3t, hmt, ?_⟩
                      intro res s4 m4 hden4 _ hfu4 _ hres_u hm4
                      have hfu4' : s4.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        dsimp only [s3t, s3r] at hfu4
                        have hfu3' : s3.core.fuel.toNat ≤ s0.core.fuel.toNat := hfu3r
                        omega
                      c0_hsteps_nogrp
                      -- Join after optional `full_factor` (saving/restoring `elim_bound`)
                      refine wp_join_state0 (α := FullState)
                        (fun sf mf => FullDenseInv c F0 sf ∧
                          sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf)
                        (fun _ sf mf ⟨hdenf, hfuf, hmf⟩ => by
                          c0_hsteps_nogrp
                          m6_call hReb
                          refine ⟨c, F0, sf, R, rfl, hdenf, hmf, ?_⟩
                          intro rr se me hspe hcle hfue _ hue hme
                          let se' : FullState :=
                            { se with scratch :=
                              { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                          have hspe' : FullSparseInv c F0 se' :=
                            m6_sparseInv_with_scratch_keep6 hspe
                              { hspe.lengths.scratch_ok with
                                walk_vals_len := hspe.lengths.scratch_ok.walk_vals_len } rfl rfl
                          have hfue' : se'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                            change se.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
                          c0_hsteps!
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
                                sg.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sg ⋆ R) mg)
                              (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                                c0_hsteps_nogrp
                                refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                                  (fun b => (b, ())) (fun _ => True)
                                  (fun _ _ _ => by
                                    c0_hsteps_nogrp
                                    m6_call hMin; intro fact_bud _
                                    c0_hsteps_nogrp
                                    let sg0 : FullState :=
                                      { sg with scratch := { sg.scratch with elim_bound := 0#64 } }
                                    have hdeng0 : FullDenseInv c F0 sg0 :=
                                      m6_denseInv_with_scratch_keep6 hdeng
                                        { hdeng.lengths.scratch_ok with
                                          walk_vals_len := hdeng.lengths.scratch_ok.walk_vals_len }
                                        rfl rfl
                                    m6_call hFact
                                    refine ⟨c, F0, sg0, R, rfl, hdeng0, hm, ?_⟩
                                    intro _ sf0 mf0 hdenf0 _ hfuf0 _ hmf0
                                    c0_hsteps!
                                    let sf1 : FullState :=
                                      { sf0 with scratch :=
                                        { sf0.scratch with elim_bound := sg.scratch.elim_bound } }
                                    have hdenf1 : FullDenseInv c F0 sf1 :=
                                      m6_denseInv_with_scratch_keep6 hdenf0
                                        { hdenf0.lengths.scratch_ok with
                                          walk_vals_len :=
                                            hdenf0.lengths.scratch_ok.walk_vals_len }
                                        rfl rfl
                                    exact hJf sf1 _ ⟨hdenf1, by
                                      change sf0.core.fuel.toNat ≤ s0.core.fuel.toNat
                                      rw [hfuf0]; exact hfug, hm⟩)
                                  (fun Jfb hJfb => by
                                    c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial)))
                              (fun Jdo hJdo => by
                                c0_hsteps!
                                · exact hJdo s4 m4 ⟨hden4, hfu4', hm4⟩
                                · exact hJdo s4 m4 ⟨hden4, hfu4', hm4⟩
                                · exact hJf s4 m4 ⟨hden4, hfu4', hm4⟩)
                          · c0_hsteps!; exact hJf s4 m4 ⟨hden4, hfu4', hm4⟩))
                    (fun Jb hJb => by
                      c0_hsplit
                      · c0_hsteps!; exact hJb _ trivial
                      · c0_hsteps_nogrp; m6_call hMin; intro b _; c0_hsteps!; exact hJb b trivial)
              · intro Lt hLt; c0_hsteps!
                exact hLt cv3 (0#64, ()) _
                  ⟨s3r.scratch.tarjan_mark, htl3, Nat.zero_le _, by simp,
                   fun _ h => by simp at h, hm⟩)
          (fun Jfb hJfb => by c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial))
      · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
        let s2' : FullState :=
          { s2 with scratch := { s2.scratch with fwd_str_cnt := s2.scratch.search_ticks } }
        have hsp2' : FullSparseInv c F0 s2' :=
          m6_sparseInv_with_scratch_keep6 hsp2
            { hsp2.lengths.scratch_ok with
              walk_vals_len := hsp2.lengths.scratch_ok.walk_vals_len } rfl rfl
        have hfu2' : s2'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
          change s2.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
        c0_hsteps!
        · exact hQ 20#64 s2' _ hsp2' hcl2 hfu2' (Or.inr rfl)
            (fun _ => hsp2'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s2' _ hsp2' hcl2 hfu2' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps!; exact hJ1 s0 m0 ⟨hinv0, hcl0, Nat.le_refl _, hm0⟩
      · c0_hsteps_nogrp
        let s0a : FullState :=
          { s0 with scratch := { s0.scratch with eliminations := s0.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv0.lengths.core_ok,
           { hinv0.lengths.scratch_ok with
             walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }⟩
        m6_call hIlog; intro loge _ _
        c0_hsteps_nogrp
        m6_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
        intro delta
        c0_hsteps!
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          m6_sparseInv_with_scratch_keep6 hinv0
            { hinv0.lengths.scratch_ok with
              walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len } rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

end LeanQbe.T.Examples.Kissat.FullM6BveFwd
