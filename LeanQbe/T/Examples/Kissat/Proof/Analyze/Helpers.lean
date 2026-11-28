/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Examples.Kissat.Ref.Base
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb

/-!
# Shared Canonical Helpers for `Kissat.Proof.Analyze` (`Proof.Analyze.Helpers`)

Purely canonical helper lemmas over `Proof.Spec.*`, `Proof.*.Spec`, `Ref.*`, and `Logic.*`
(`0` legacy `Full*` imports, `0` `Proof.Learn.Wp*`/`Helpers` imports, `0` `@[expose]` on theorems,
`<= 100` cols).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers

open Std Std.Sat
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
open LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Pure `BitVec` / `Nat` / `List` Lemmas -/

theorem fa_strip_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem fa_strip_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem fa_strip_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

theorem fl_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  have h : x >>> 1#32 = x >>> (1 : Nat) := rfl
  rw [h, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem fl_bv32_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp

theorem fl_bv32_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64)]

theorem fl_xor1_div2 (n : Nat) : (n ^^^ 1) / 2 = n / 2 :=
  nat_xor1_div2 n

theorem fl_bv64_add1_toNat {k n : BitVec 64} (hk : k.toNat < n.toNat) :
    (k + 1#64).toNat = k.toNat + 1 :=
  bv64_add1_toNat hk

theorem fl_bv32_add1_toNat {k : BitVec 32} {ub : Nat} (hk : k.toNat < ub) (hub : ub < 2 ^ 32) :
    (k + 1#32).toNat = k.toNat + 1 := by
  have : k.toNat + 1 < 2 ^ 32 := by omega
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt this]

theorem list_set_congr {α : Type} {xs : List α} {i j : Nat} {v w : α}
    (hij : i = j) (hvw : v = w) : xs.set i v = xs.set j w := by
  subst hij; subst hvw; rfl

theorem getElem_eq_of_idx {α : Type} {xs : List α} {i j : Nat}
    (hij : i = j) : xs[i]? = xs[j]? := by
  subst hij; rfl

theorem ofNat64_pos {n : Nat} (h : ¬ BitVec.ofNat 64 n = 0#64) : 0 < n := by
  rcases n with _ | k
  · exact absurd rfl h
  · omega

theorem ofNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64) (h : BitVec.ofNat 64 n = 0#64) : n = 0 := by
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using this

theorem ofNat64_eq_one {n : Nat} (hn : n < 2 ^ 64) (h : BitVec.ofNat 64 n = 1#64) : n = 1 := by
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using this

theorem p2_bv32_lit_neq_ff {l cv : Nat} (hlt : l < 2 * cv) (hcv : cv ≤ 2 ^ 30) :
    BitVec.ofNat 32 l ≠ 0xFFFFFFFF#32 := by
  intro heq
  have h1 := congrArg BitVec.toNat heq
  have hlt32 : l < 2 ^ 32 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32] at h1
  have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := by decide
  omega

theorem p2_bv64_add1_eq {k n : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : k < 2 ^ 64 := by omega
  have h2 : k + 1 < 2 ^ 64 := by omega
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]

theorem p2_bv64_sub1_eq {k : Nat} (hk : 0 < k) (hk64 : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]; omega))]
  have hsub : k - 1 < 2 ^ 64 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hsub]

theorem fl_i8_sext32_eq0_iff (x : BitVec 8) :
    BitVec.signExtend 32 x = 0#32 ↔ x = 0#8 := by
  constructor
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro k hk
    have hk' := congrArg (·[k]) h
    simpa [BitVec.getElem_signExtend, hk] using hk'
  · rintro rfl; decide

theorem fl_i8_slt0_neg_iff {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    BitVec.slt x 0#8 = true ↔ BitVec.signExtend 32 x ≠ 0#32 ∧ x ≠ 1#8 := by
  rcases hx with rfl | rfl | rfl <;> decide

theorem fl_i8_pos_of_not_sle {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8)
    (hs : BitVec.slt x 0#8 = false) (hz : BitVec.signExtend 32 x ≠ 0#32) : x = 1#8 := by
  rcases hx with rfl | rfl | rfl <;> simp_all <;> revert hs hz <;> decide

theorem fl_take_succ_forall {α : Type} [Inhabited α] {xs : List α} {P : α → Prop} {k : Nat}
    (hk : k < xs.length) (hprev : ∀ x ∈ xs.take k, P x)
    (hcur : P (xs[k]?.getD default)) :
    ∀ x ∈ xs.take (k + 1), P x := by
  rw [List.take_succ_eq_append_getElem hk]
  intro x hx
  rcases List.mem_append.mp hx with hp | hc
  · exact hprev x hp
  · rw [List.mem_singleton.mp hc]
    simpa [List.getElem?_eq_getElem hk] using hcur

/-! ## 2. Scratch Lengths, `FullWitnessCutInv`, & `FullOtfsInvW` Helpers -/

theorem fullScratch_lengthsOk_of_arr_len {c : FullCfg} {sc sc' : FullScratch}
    (h : sc.LengthsOk c)
    (h0 : sc'.walk_vals.length = sc.walk_vals.length)
    (h1 : sc'.phases.length = sc.phases.length)
    (h2 : sc'.phases_target.length = sc.phases_target.length)
    (h3 : sc'.phases_best.length = sc.phases_best.length)
    (h4 : sc'.walk_best.length = sc.walk_best.length)
    (h5 : sc'.heap.length = sc.heap.length)
    (h6 : sc'.pos.length = sc.pos.length)
    (h7 : sc'.shrink_stk.length = sc.shrink_stk.length)
    (h8 : sc'.q_prev.length = sc.q_prev.length)
    (h9 : sc'.q_next.length = sc.q_next.length)
    (h10 : sc'.q_stamp.length = sc.q_stamp.length)
    (h11 : sc'.wsort.length = sc.wsort.length)
    (h12 : sc'.work_stk1.length = sc.work_stk1.length)
    (h13 : sc'.work_stk2.length = sc.work_stk2.length)
    (h14 : sc'.tarjan_mark.length = sc.tarjan_mark.length)
    (h15 : sc'.tarjan_reach.length = sc.tarjan_reach.length)
    (h16 : sc'.score.length = sc.score.length)
    (h17 : sc'.sim_sig.length = sc.sim_sig.length)
    (h18 : sc'.glue_used.length = sc.glue_used.length)
    (h19 : sc'.last_learned.length = sc.last_learned.length)
    (h20 : sc'.delayed.length = sc.delayed.length)
    (h21 : sc'.red_refs.length = sc.red_refs.length)
    (h22 : sc'.extend_stk.length = sc.extend_stk.length)
    (h23 : sc'.scratch_buf.length = sc.scratch_buf.length) : sc'.LengthsOk c :=
  { walk_vals_len := h0 ▸ h.walk_vals_len
    phases_len := h1 ▸ h.phases_len
    phases_target_len := h2 ▸ h.phases_target_len
    phases_best_len := h3 ▸ h.phases_best_len
    walk_best_len := h4 ▸ h.walk_best_len
    heap_len_arr := h5 ▸ h.heap_len_arr
    pos_len := h6 ▸ h.pos_len
    shrink_stk_len := h7 ▸ h.shrink_stk_len
    q_prev_len := h8 ▸ h.q_prev_len
    q_next_len := h9 ▸ h.q_next_len
    q_stamp_len := h10 ▸ h.q_stamp_len
    wsort_len := h11 ▸ h.wsort_len
    work_stk1_len := h12 ▸ h.work_stk1_len
    work_stk2_len := h13 ▸ h.work_stk2_len
    tarjan_mark_len := h14 ▸ h.tarjan_mark_len
    tarjan_reach_len := h15 ▸ h.tarjan_reach_len
    score_len := h16 ▸ h.score_len
    sim_sig_len := h17 ▸ h.sim_sig_len
    glue_used_len := h18 ▸ h.glue_used_len
    last_learned_len := h19 ▸ h.last_learned_len
    delayed_len_arr := h20 ▸ h.delayed_len_arr
    red_refs_len := h21 ▸ h.red_refs_len
    extend_stk_len := h22 ▸ h.extend_stk_len
    scratch_buf_len := h23 ▸ h.scratch_buf_len }

theorem FullWitnessCutInv.to_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (hcut : k.trail_end ≤ cut) : FullWitnessInv c F0 F_cur k :=
  { ext_sound := h.ext_sound, inconsistent_sound := h.inconsistent_sound
    arena := h.arena, watches := h.watches, cur_level_le := h.cur_level_le
    trail_lits_lt := h.trail_lits_lt, trail_vars_nodup := h.trail_vars_nodup
    vals_domain := h.vals_domain, vals_true_iff := h.vals_true_iff
    vals_false_iff := h.vals_false_iff, lvl_le := h.lvl_le, dec_earliest := h.dec_earliest
    levels_inhabited := h.levels_inhabited, level0_sound := h.level0_sound
    trail_pos_inv := h.trail_pos_inv, level0_rsn_none := h.level0_rsn_none
    frame_trail_lt := h.frame_trail_lt, frame_trail_mono := h.frame_trail_mono
    frame_trail_before_lt := h.frame_trail_before_lt, frame_dec_lt := h.frame_dec_lt
    reason_inv := fun idx hidx => h.reason_inv_cut idx (by omega)
    reason_lit_mem := fun idx hidx => h.reason_lit_mem_cut idx (by omega) }

theorem FullWitnessCutInv.shrink_cut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut cut' : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (hle : cut' ≤ cut) : FullWitnessCutInv c F0 F_cur cut' k :=
  { h with
    cut_le := Nat.le_trans hle h.cut_le
    reason_inv_cut := fun idx hidx => h.reason_inv_cut idx (by omega)
    reason_lit_mem_cut := fun idx hidx => h.reason_lit_mem_cut idx (by omega) }

theorem FullWitnessCutInv.vals_zero_iff {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) {l : Nat}
    (hl : l < 2 * k.cur_vars) :
    k.vals[l]?.getD 0#8 = 0#8 ↔ ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  constructor
  · intro hz i hi hvar
    rcases (litVar_eq_iff _ l).mp hvar with h1 | h2
    · have ht := (h.vals_true_iff l hl).mpr ⟨i, hi, h1⟩; rw [hz] at ht; cases ht
    · have hf := (h.vals_false_iff l hl).mpr ⟨i, hi, h2⟩; rw [hz] at hf; cases hf
  · intro hnone
    rcases h.vals_domain l hl with h0 | h1 | h2
    · exact h0
    · obtain ⟨i, hi, heq⟩ := (h.vals_true_iff l hl).mp h1; exact absurd (by rw [heq]) (hnone i hi)
    · obtain ⟨i, hi, heq⟩ := (h.vals_false_iff l hl).mp h2
      exact absurd (by rw [heq, fullInv_var_xor1]) (hnone i hi)

theorem FullOtfsWitnessInv.with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k) (tmp' : List (BitVec 32)) :
    FullOtfsWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem FullOtfsInvW.of_safetySlice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullOtfsInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullOtfsInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.2.1
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs; rwa [heq]

theorem FullOtfsInvW.with_conflicts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) (k' : BitVec 64) :
    FullOtfsInvW c F0 F_cur { s with scratch := { s.scratch with conflicts := k' } } :=
  FullOtfsInvW.of_safetySlice h ⟨h.1.core_ok, { h.1.scratch_ok with }⟩ rfl ⟨rfl, rfl⟩

theorem FullConflictOkW.with_scratch {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflictOkW F_cur s) (sc' : FullScratch) :
    FullConflictOkW F_cur { s with scratch := sc' } := h

theorem deduce_same_core_cut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s' : FullState}
    (hinv : FullCutInvW c F0 F_cur cut s) (hlen' : s'.LengthsOk c)
    (hcore : s'.core = s.core) (hpres : FullExtScratchPres s s') :
    FullCutInvW c F0 F_cur cut s' := by
  refine ⟨hlen', hcore ▸ hinv.2.1, ?_, ?_, ?_, hcore ▸ hinv.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact hinv.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hcore]; exact hinv.2.2.2.1
  · exact FullExtScratchOk.of_pres hinv.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs; rwa [hcore]

theorem s13b_push_marksCov_gen {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hcov : FullAnaMarksCov c s) {v : Nat}
    (hv : v < s.core.cur_vars) (hun : s.core.mrk[v]?.getD 0#8 = 0#8)
    {val : BitVec 8} (hval : val ≠ 0#8) :
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            mrk := s.core.mrk.set v val
            min_clr_len := s.core.min_clr_len + 1 }
        scratch :=
          { s.scratch with
            work_stk1 := s.scratch.work_stk1.set s.core.min_clr_len (BitVec.ofNat 32 v) } }
    FullAnaMarksCov c s' := by
  dsimp only
  rcases hcov with ⟨hmcl_le, hnd, hent, hcov⟩
  have hmax32 : c.max_vars < 2 ^ 32 := fullInv_max_vars_lt32 c
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hv32 : v < 2 ^ 32 := by omega
  have hmiss : ∀ i < s.core.min_clr_len,
      (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ v := by
    intro i hi heq
    have hm := (hent i hi).2
    rw [heq, hun] at hm
    exact hm rfl
  have hwlen : s.core.min_clr_len ≤ s.scratch.work_stk1.length := by
    rw [hlen.scratch_ok.work_stk1_len]; omega
  have htk_len : (s.scratch.work_stk1.take s.core.min_clr_len).length = s.core.min_clr_len := by
    rw [List.length_take, Nat.min_eq_left hwlen]
  have hmap_len : ((s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat).length =
      s.core.min_clr_len := by rw [List.length_map, htk_len]
  have hmcl_lt_cv : s.core.min_clr_len < s.core.cur_vars := by
    refine inj_lt_of_missing (fun i => (s.scratch.work_stk1[i]?.getD 0#32).toNat)
      ?_ (fun i hi => (hent i hi).1) hv hmiss
    intro i j hi hj heq
    by_cases hij : i = j
    · exact hij
    · have hpw := List.pairwise_iff_getElem.mp hnd
      have hi_stk := Nat.lt_of_lt_of_le hi hwlen
      have hj_stk := Nat.lt_of_lt_of_le hj hwlen
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · have hne := hpw i j (by rw [hmap_len]; exact hi) (by rw [hmap_len]; exact hj) hlt
        simp [List.getElem_take, List.getElem?_eq_getElem hi_stk,
          List.getElem?_eq_getElem hj_stk] at heq hne
        exact absurd heq hne
      · have hne := hpw j i (by rw [hmap_len]; exact hj) (by rw [hmap_len]; exact hi) hgt
        simp [List.getElem_take, List.getElem?_eq_getElem hi_stk,
          List.getElem?_eq_getElem hj_stk] at heq hne
        exact absurd heq.symm hne
  have hstk_len : s.core.min_clr_len < s.scratch.work_stk1.length := by
    rw [hlen.scratch_ok.work_stk1_len]; omega
  have hmrk_len : v < s.core.mrk.length := by rw [hlen.core_ok.mrk_len]; omega
  have htk_eq : (s.scratch.work_stk1.set s.core.min_clr_len (BitVec.ofNat 32 v)).take
      s.core.min_clr_len = s.scratch.work_stk1.take s.core.min_clr_len := by
    apply List.ext_getElem
    · rw [List.length_take, List.length_take, List.length_set, Nat.min_eq_left hwlen]
    · intro i hi1 hi2
      have him : i < s.core.min_clr_len := by
        have := (List.length_take_le s.core.min_clr_len s.scratch.work_stk1); omega
      simp [List.getElem_take, List.getElem_set_ne (by omega : s.core.min_clr_len ≠ i)]
  have htake : ((s.scratch.work_stk1.set s.core.min_clr_len (BitVec.ofNat 32 v)).take
      (s.core.min_clr_len + 1)).map BitVec.toNat =
      (s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat ++ [v] := by
    have hlt : s.core.min_clr_len <
        (s.scratch.work_stk1.set s.core.min_clr_len (BitVec.ofNat 32 v)).length := by
      simpa [List.length_set] using hstk_len
    rw [List.take_succ_eq_append_getElem hlt]
    simp only [List.map_append, List.map_singleton]
    rw [List.getElem_set_self (by simpa [List.length_set] using hstk_len),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv32, htk_eq]
  refine ⟨by change s.core.min_clr_len + 1 ≤ s.core.cur_vars; omega, ?_, ?_, ?_⟩
  · change (((s.scratch.work_stk1.set s.core.min_clr_len (BitVec.ofNat 32 v)).take
        (s.core.min_clr_len + 1)).map BitVec.toNat).Nodup
    rw [htake, List.nodup_append]
    refine ⟨hnd, by simp, fun a ha b hb heq => ?_⟩
    rw [List.mem_singleton.mp hb] at heq
    rw [List.mem_map] at ha
    obtain ⟨x, hx, hxv⟩ := ha
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have hilen : i < s.core.min_clr_len := by
      rw [List.length_take, Nat.min_eq_left hwlen] at hi; exact hi
    have hix' : s.scratch.work_stk1[i]'(by omega) = x := by
      simpa [List.getElem_take] using hix
    have heq' : (s.scratch.work_stk1[i]?.getD 0#32).toNat = v := by
      rw [List.getElem?_eq_getElem (by omega : i < s.scratch.work_stk1.length)]
      simpa [hix', heq] using hxv
    exact hmiss i hilen heq'
  · intro k hk
    change k < s.core.min_clr_len + 1 at hk
    by_cases hlt : k < s.core.min_clr_len
    · have hk1 : ((s.scratch.work_stk1.set s.core.min_clr_len (BitVec.ofNat 32 v))[k]?.getD
          0#32).toNat = (s.scratch.work_stk1[k]?.getD 0#32).toNat := by
        simp [List.getElem?_set_ne (by omega : s.core.min_clr_len ≠ k)]
      have hne_v : (s.scratch.work_stk1[k]?.getD 0#32).toNat ≠ v := hmiss k hlt
      refine ⟨by change _ < s.core.cur_vars; simpa [hk1] using (hent k hlt).1, ?_⟩
      change (s.core.mrk.set v val)[_]?.getD 0#8 ≠ 0#8
      simpa [hk1, List.getElem?_set_ne (Ne.symm hne_v)] using (hent k hlt).2
    · have hk_eq : k = s.core.min_clr_len := by omega
      subst hk_eq
      have hsk : ((s.scratch.work_stk1.set s.core.min_clr_len (BitVec.ofNat 32 v))[
          s.core.min_clr_len]?.getD 0#32).toNat = v := by
        simp [List.getElem?_set_self hstk_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv32]
      refine ⟨by change _ < s.core.cur_vars; simpa [hsk] using hv, ?_⟩
      change (s.core.mrk.set v val)[_]?.getD 0#8 ≠ 0#8
      simpa [hsk, List.getElem?_set_self hmrk_len] using hval
  · intro w hw hmw
    change w < c.max_vars at hw
    change (s.core.mrk.set v val)[w]?.getD 0#8 ≠ 0#8 at hmw
    by_cases hwv : w = v
    · subst hwv
      refine ⟨s.core.min_clr_len, by change s.core.min_clr_len < s.core.min_clr_len + 1; omega, ?_⟩
      change ((s.scratch.work_stk1.set s.core.min_clr_len (BitVec.ofNat 32 w))[
          s.core.min_clr_len]?.getD 0#32).toNat = w
      simp [List.getElem?_set_self hstk_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv32]
    · have hmw0 : s.core.mrk[w]?.getD 0#8 ≠ 0#8 := by
        simpa [List.getElem?_set_ne (Ne.symm hwv)] using hmw
      obtain ⟨i, hi, hieq⟩ := hcov w hw hmw0
      refine ⟨i, by change i < s.core.min_clr_len + 1; omega, ?_⟩
      change ((s.scratch.work_stk1.set s.core.min_clr_len (BitVec.ofNat 32 v))[i]?.getD
          0#32).toNat = w
      simpa [List.getElem?_set_ne (by omega : s.core.min_clr_len ≠ i)] using hieq

/-! ## 3. Upstream Capability Projections Missing from `Limits.Spec` / `Minimize.Spec` -/

theorem has_full_tick_rel {Γ : Env} (h : Γ.Sat Limits.Spec.specs) :
    Γ.Has "full_tick_rel" Proof.Spec.fullTickRelSpec :=
  Env.Sat.has h (List.getElem_mem (l := Limits.Spec.specs) (n := 2) (by decide))
    Limits.Spec.fullTickRelSpec_xfree

theorem has_full_ema_update {Γ : Env} (h : Γ.Sat Limits.Spec.specs) :
    Γ.Has "full_ema_update" Proof.Spec.fullEmaUpdateSpec :=
  Env.Sat.has h (List.getElem_mem (l := Limits.Spec.specs) (n := 4) (by decide))
    Limits.Spec.fullEmaUpdateSpec_xfree

theorem has_full_min_shrink {Γ : Env} (h : Γ.Sat Minimize.Spec.specs) :
    Γ.Has "full_min_shrink_m6" Minimize.Spec.fullMinShrinkSpec :=
  Env.Sat.has h (List.getElem_mem (l := Minimize.Spec.specs) (n := 5) (by decide))
    Minimize.Spec.fullMinShrinkSpec_xfree

/-! ## 4. Failed-Literal Analysis Pure & State-Invariance Lemmas -/

theorem fl_unsat_of_unit_pair {F_cur : List (List Nat)} {F0 : CNF Nat}
    (hunsat : (cnfOfClauses F_cur).Unsat → F0.Unsat)
    {u : Nat} (hu1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u]))
    (hu2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u ^^^ 1])) :
    F0.Unsat := by
  refine hunsat (unsat_of_entails_nil (entails_of_mem_or_false hu1 fun l hl => ?_))
  rw [List.mem_singleton.mp hl]
  right
  simpa [litNeg] using hu2

@[expose] def flIdxs (mrk : List (BitVec 8)) (trl : List (BitVec 32)) : Nat → List Nat
  | 0 => []
  | i + 1 =>
    let p := (trl[i]?.getD 0#32).toNat
    if mrk[p / 2]?.getD 0#8 ≠ 0#8 then i :: flIdxs mrk trl i else flIdxs mrk trl i

@[expose] def flLits (mrk : List (BitVec 8)) (trl : List (BitVec 32)) (i : Nat) : List Nat :=
  (flIdxs mrk trl i).map fun j => (trl[j]?.getD 0#32).toNat ^^^ 1

theorem flIdxs_length_le (mrk : List (BitVec 8)) (trl : List (BitVec 32)) (i : Nat) :
    (flIdxs mrk trl i).length ≤ i := by
  induction i with
  | zero => simp [flIdxs]
  | succ i ih =>
    rw [flIdxs]
    by_cases h : mrk[(trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 <;>
      simp [h] <;> omega

theorem flIdxs_eq_nil_of_zero {mrk : List (BitVec 8)} {trl : List (BitVec 32)} {i : Nat}
    (hz : ∀ j < i, mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) :
    flIdxs mrk trl i = [] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [flIdxs, ite_eq_right (by simpa using hz i (by omega))]
    exact ih fun j hj => hz j (by omega)

theorem flIdxs_congr {mrk mrk' : List (BitVec 8)} {trl : List (BitVec 32)} {i : Nat}
    (h : ∀ j < i,
      mrk'[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 =
      mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8) :
    flIdxs mrk' trl i = flIdxs mrk trl i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [flIdxs, flIdxs]
    have hi : mrk'[(trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 =
        mrk[(trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 := h i (by omega)
    dsimp only
    rw [hi, ih fun j hj => h j (by omega)]

theorem flLits_congr_idxs {mrk mrk' : List (BitVec 8)} {trl : List (BitVec 32)} {i i' : Nat}
    (h : flIdxs mrk trl i = flIdxs mrk' trl i') :
    flLits mrk trl i = flLits mrk' trl i' := by
  unfold flLits; rw [h]

theorem flIdxs_eq_of_unmarked_above {mrk : List (BitVec 8)} {trl : List (BitVec 32)}
    {i j : Nat} (hij : i ≤ j)
    (hun : ∀ k, i ≤ k → k < j → mrk[(trl[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) :
    flIdxs mrk trl j = flIdxs mrk trl i := by
  induction j with
  | zero => rw [show i = 0 by omega]
  | succ j ih =>
    by_cases hlt : i ≤ j
    · rw [flIdxs, ite_eq_right (by simpa using hun j hlt (by omega))]
      exact ih hlt fun k hk1 hk2 => hun k hk1 (by omega)
    · rw [show i = j + 1 by omega]

theorem flIdxs_succ_marked {mrk : List (BitVec 8)} {trl : List (BitVec 32)} {i : Nat}
    (hm : mrk[(trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    flIdxs mrk trl (i + 1) = i :: flIdxs mrk trl i := by
  rw [flIdxs, ite_eq_left hm]

theorem flLits_eq_singleton_of_first {mrk : List (BitVec 8)} {trl : List (BitVec 32)} {idx : Nat}
    (hz : ∀ j < idx, mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8)
    (hm : mrk[(trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    flLits mrk trl (idx + 1) = [(trl[idx]?.getD 0#32).toNat ^^^ 1] := by
  unfold flLits
  rw [flIdxs_succ_marked hm, flIdxs_eq_nil_of_zero hz]
  simp

theorem fl_assign0_preserves_sparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0)
    {lit : BitVec 32} (hlt : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    {flags' : List (BitVec 32)} {phases' : List (BitVec 8)} {unass' : BitVec 64}
    (hfll : flags'.length = c.max_vars) (hphl : phases'.length = c.max_vars) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v 0#32
            rsns := s.core.rsns.set v 0xFFFFFFFF#32
            trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            trail_end := s.core.trail_end + 1
            unassigned := unass', unflushed := s.core.unflushed + 1#64 }
        scratch := { s.scratch with phases := phases' } }
    FullSparseInvW c F0 F_cur s' := by
  intro v s'
  have hw := hinv.2.1
  have hcl := hinv.1.core_ok
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlt hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * s.core.cur_vars := litNeg_lt_two_mul hlt
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlt).mp hun
  have htrl_lt : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
    intro i hi
    by_cases he : i = s.core.trail_end
    · subst he
      simpa [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)] using hlt
    · simpa [s', List.getElem?_set_ne (Ne.symm he)] using hw.trail_lits_lt i (by omega)
  have hnodup : ∀ i j, i < s'.core.trail_end → j < s'.core.trail_end →
      (s'.core.trl[i]?.getD 0#32).toNat / 2 = (s'.core.trl[j]?.getD 0#32).toNat / 2 → i = j := by
    intro i j hi hj heq
    have hte_len : s.core.trail_end < s.core.trl.length := by rw [hcl.trl_len]; exact hte_max
    by_cases hi_e : i = s.core.trail_end <;> by_cases hj_e : j = s.core.trail_end
    · omega
    · subst hi_e
      have h1 : (s'.core.trl[s.core.trail_end]?.getD 0#32).toNat / 2 = v := by
        simp [s', List.getElem?_set_self hte_len, v]
      have h2 : (s'.core.trl[j]?.getD 0#32).toNat / 2 = (s.core.trl[j]?.getD 0#32).toNat / 2 := by
        simp [s', List.getElem?_set_ne (Ne.symm hj_e)]
      exact absurd (h1.symm.trans (heq.trans h2)).symm
        (hnot_var j (by change j < s.core.trail_end + 1 at hj; omega))
    · subst hj_e
      have h1 : (s'.core.trl[i]?.getD 0#32).toNat / 2 = (s.core.trl[i]?.getD 0#32).toNat / 2 := by
        simp [s', List.getElem?_set_ne (Ne.symm hi_e)]
      have h2 : (s'.core.trl[s.core.trail_end]?.getD 0#32).toNat / 2 = v := by
        simp [s', List.getElem?_set_self hte_len, v]
      exact absurd ((h1.symm.trans heq).trans h2)
        (hnot_var i (by change i < s.core.trail_end + 1 at hi; omega))
    · have hi' : i < s.core.trail_end := by change i < s.core.trail_end + 1 at hi; omega
      have hj' : j < s.core.trail_end := by change j < s.core.trail_end + 1 at hj; omega
      have h1 : (s'.core.trl[i]?.getD 0#32).toNat / 2 = (s.core.trl[i]?.getD 0#32).toNat / 2 := by
        simp [s', List.getElem?_set_ne (Ne.symm hi_e)]
      have h2 : (s'.core.trl[j]?.getD 0#32).toNat / 2 = (s.core.trl[j]?.getD 0#32).toNat / 2 := by
        simp [s', List.getElem?_set_ne (Ne.symm hj_e)]
      exact hw.trail_vars_nodup i j hi' hj' ((h1.symm.trans heq).trans h2)
  have hlen' : s'.LengthsOk c :=
    ⟨⟨by simp [s', List.length_set, hcl.vals_len], hcl.lit_mark_len, hcl.mrk_len, hfll,
      by simp [s', List.length_set, hcl.lvl_len],
      by simp [s', List.length_set, hcl.rsns_len],
      by simp [s', List.length_set, hcl.trl_len],
      by simp [s', List.length_set, hcl.trail_pos_len],
      hcl.tmp_len_arr, hcl.min_clr_len_arr, hcl.frame_trail_len, hcl.frame_dec_len,
      hcl.wvec_len, hcl.repr_len, hcl.min_stk_len, hcl.arena_len_arr, hcl.wstk_len_arr,
      hcl.cur_vars_ge, hcl.cur_vars_le, hcl.arena_len_le, hcl.wlen_le,
      by show s.core.trail_end + 1 ≤ s.core.cur_vars; omega,
      by have := hcl.propagated_le; show s.core.propagated ≤ s.core.trail_end + 1; omega,
      hcl.tmp_len_le, hcl.min_clr_len_le⟩,
     fullScratch_lengthsOk_of_arr_len hinv.1.scratch_ok rfl
       (by simp [s', hphl, hinv.1.scratch_ok.phases_len]) rfl rfl rfl rfl rfl rfl rfl rfl rfl
       rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  have hval1 : s.core.vals.length = 2 * c.max_vars := hcl.vals_len
  have hlt0 : lit.toNat < s.core.vals.length := by rw [hval1]; have := hcl.cur_vars_le; omega
  have hlt2 : (lit.toNat ^^^ 1) < (s.core.vals.set lit.toNat 1#8).length := by
    rw [List.length_set, hval1]; have := hcl.cur_vars_le; omega
  have htrl_lt_len : s.core.trail_end < s.core.trl.length := by rw [hcl.trl_len]; exact hte_max
  have hvals_dom : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 = 0#8 ∨ s'.core.vals[l]?.getD 0#8 = 1#8 ∨
        s'.core.vals[l]?.getD 0#8 = 0xFF#8 := by
    intro l hl
    by_cases hn : l = lit.toNat ^^^ 1
    · subst hn; simp [s', List.getElem?_set_self hlt2]
    · by_cases hp : l = lit.toNat
      · subst hp
        change ((s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)[lit.toNat]?.getD
            0#8 = 0#8 ∨ _
        rw [List.getElem?_set_ne hne_lit, List.getElem?_set_self hlt0]
        exact Or.inr (Or.inl rfl)
      · change ((s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)[l]?.getD 0#8 =
            0#8 ∨ _
        rw [List.getElem?_set_ne (Ne.symm hn), List.getElem?_set_ne (Ne.symm hp)]
        exact hw.vals_domain l hl
  have hval_true : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 = 1#8 ↔
        ∃ i < s.core.trail_end + 1, (s'.core.trl[i]?.getD 0#32).toNat = l := by
    intro l hl
    constructor
    · intro h1
      by_cases hn : l = lit.toNat ^^^ 1
      · subst hn; simp [s', List.getElem?_set_self hlt2] at h1
      · by_cases hp : l = lit.toNat
        · subst hp
          exact ⟨s.core.trail_end, by omega, by simp [s', List.getElem?_set_self htrl_lt_len]⟩
        · have h0 : s.core.vals[l]?.getD 0#8 = 1#8 := by
            change ((s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)[l]?.getD
                0#8 = 1#8 at h1
            rwa [List.getElem?_set_ne (Ne.symm hn), List.getElem?_set_ne (Ne.symm hp)] at h1
          obtain ⟨i, hi, hiq⟩ := (hw.vals_true_iff l hl).mp h0
          exact ⟨i, by omega, by
            simpa [s', List.getElem?_set_ne (by omega : s.core.trail_end ≠ i)] using hiq⟩
    · rintro ⟨i, hi, hiq⟩
      by_cases he : i = s.core.trail_end
      · subst he
        have hl_eq : lit.toNat = l := by
          simpa [s', List.getElem?_set_self htrl_lt_len] using hiq
        subst hl_eq
        change ((s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)[lit.toNat]?.getD
            0#8 = 1#8
        rw [List.getElem?_set_ne hne_lit, List.getElem?_set_self hlt0]; rfl
      · have hiq0 : (s.core.trl[i]?.getD 0#32).toNat = l := by
          simpa [s', List.getElem?_set_ne (Ne.symm he)] using hiq
        have hvar_ne : l / 2 ≠ v := by rw [← hiq0]; exact hnot_var i (by omega)
        have hne_p : lit.toNat ≠ l := fun h => hvar_ne (by rw [← h])
        have hne_n : lit.toNat ^^^ 1 ≠ l := fun h => hvar_ne (by rw [← h, nat_xor1_div2])
        change ((s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)[l]?.getD 0#8 = 1#8
        rw [List.getElem?_set_ne hne_n, List.getElem?_set_ne hne_p]
        exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, hiq0⟩
  have hval_false : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 = 0xFF#8 ↔
        ∃ i < s.core.trail_end + 1, (s'.core.trl[i]?.getD 0#32).toNat = l ^^^ 1 := by
    intro l hl
    constructor
    · intro hf
      by_cases hn : l = lit.toNat ^^^ 1
      · subst hn
        exact ⟨s.core.trail_end, by omega, by
          simp [s', List.getElem?_set_self htrl_lt_len, Nat.xor_assoc]⟩
      · by_cases hp : l = lit.toNat
        · subst hp
          have hset :
              ((s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)[lit.toNat]?.getD
              0#8 = 1#8 := by
            rw [List.getElem?_set_ne hne_lit, List.getElem?_set_self hlt0]; rfl
          change _ = 0xFF#8 at hf; rw [hset] at hf; cases hf
        · have h0 : s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
            change ((s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)[l]?.getD
                0#8 = 0xFF#8 at hf
            rwa [List.getElem?_set_ne (Ne.symm hn), List.getElem?_set_ne (Ne.symm hp)] at hf
          obtain ⟨i, hi, hiq⟩ := (hw.vals_false_iff l hl).mp h0
          exact ⟨i, by omega, by
            simpa [s', List.getElem?_set_ne (by omega : s.core.trail_end ≠ i)] using hiq⟩
    · rintro ⟨i, hi, hiq⟩
      by_cases he : i = s.core.trail_end
      · subst he
        have hlt_eq : lit.toNat = l ^^^ 1 := by
          simpa [s', List.getElem?_set_self htrl_lt_len] using hiq
        have hl_eq : l = lit.toNat ^^^ 1 := by
          have := (congrArg (· ^^^ 1) hlt_eq).symm; simpa [Nat.xor_assoc] using this
        subst hl_eq
        simp [s', List.getElem?_set_self hlt2]
      · have hiq0 : (s.core.trl[i]?.getD 0#32).toNat = l ^^^ 1 := by
          simpa [s', List.getElem?_set_ne (Ne.symm he)] using hiq
        have hvar_ne : l / 2 ≠ v := by
          rw [← nat_xor1_div2 l, ← hiq0]; exact hnot_var i (by omega)
        have hne_p : lit.toNat ≠ l := fun h => hvar_ne (by rw [← h])
        have hne_n : lit.toNat ^^^ 1 ≠ l := fun h => hvar_ne (by rw [← h, nat_xor1_div2])
        change ((s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)[l]?.getD 0#8 = 0xFF#8
        rw [List.getElem?_set_ne hne_n, List.getElem?_set_ne hne_p]
        exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, hiq0⟩
  have hlvl_le : ∀ i < s.core.trail_end + 1,
      (s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ 0 := by
    intro i hi
    by_cases he : i = s.core.trail_end
    · subst he
      have htrl_s : (s'.core.trl[s.core.trail_end]?.getD 0#32).toNat / 2 = v := by
        simp [s', List.getElem?_set_self htrl_lt_len, v]
      rw [htrl_s]
      simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt)]
    · have hi0 : i < s.core.trail_end := by omega
      have htrl_s : (s'.core.trl[i]?.getD 0#32).toNat = (s.core.trl[i]?.getD 0#32).toNat := by
        simp [s', List.getElem?_set_ne (by omega : s.core.trail_end ≠ i)]
      have hne_v : v ≠ (s.core.trl[i]?.getD 0#32).toNat / 2 := (hnot_var i hi0).symm
      have hl0i := hw.lvl_le i hi0; rw [hl0] at hl0i
      simpa [s', htrl_s, List.getElem?_set_ne hne_v] using hl0i
  have hrsn_none : ∀ i < s.core.trail_end + 1,
      s'.core.rsns[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        0xFFFFFFFF#32 := by
    intro i hi
    by_cases he : i = s.core.trail_end
    · subst he
      have htrl_s : (s'.core.trl[s.core.trail_end]?.getD 0#32).toNat / 2 = v := by
        simp [s', List.getElem?_set_self htrl_lt_len, v]
      rw [htrl_s]; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · have hi0 : i < s.core.trail_end := by omega
      have htrl_s : (s'.core.trl[i]?.getD 0#32).toNat = (s.core.trl[i]?.getD 0#32).toNat := by
        simp [s', List.getElem?_set_ne (by omega : s.core.trail_end ≠ i)]
      have hne_v : v ≠ (s.core.trl[i]?.getD 0#32).toNat / 2 := (hnot_var i hi0).symm
      have hl0i := hw.lvl_le i hi0; rw [hl0] at hl0i
      simpa [s', htrl_s, List.getElem?_set_ne hne_v] using
        hw.level0_rsn_none i hi0 (by omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { ext_sound := hw.ext_sound
      inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
      cur_level_le := by rw [show s'.core.cur_level = 0 from hl0]; exact Nat.zero_le _
      trail_lits_lt := htrl_lt
      trail_vars_nodup := hnodup
      vals_domain := hvals_dom
      vals_true_iff := hval_true
      vals_false_iff := hval_false
      lvl_le := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        change _ ≤ s.core.cur_level
        have := hlvl_le i hi; omega
      dec_earliest := fun _ j _ hj _ ⟨hpos, _⟩ => by
        change j < s.core.trail_end + 1 at hj
        exact absurd hpos (by have := hlvl_le j hj; omega)
      levels_inhabited := fun L h1 h2 => by
        change L ≤ s.core.cur_level at h2; omega
      level0_sound := fun i hi hli => by
        change i < s.core.trail_end + 1 at hi
        by_cases he : i = s.core.trail_end
        · subst he
          simpa [s', List.getElem?_set_self htrl_lt_len] using hent
        · have hi0 : i < s.core.trail_end := by omega
          have htrl_s : (s'.core.trl[i]?.getD 0#32).toNat = (s.core.trl[i]?.getD 0#32).toNat := by
            simp [s', List.getElem?_set_ne (by omega : s.core.trail_end ≠ i)]
          have hne_v : v ≠ (s.core.trl[i]?.getD 0#32).toNat / 2 := (hnot_var i hi0).symm
          rw [show (s'.core.trl[i]?.getD 0#32).toNat = (s.core.trl[i]?.getD 0#32).toNat from htrl_s]
          exact hw.level0_sound i hi0 (by
            simpa [s', htrl_s, List.getElem?_set_ne hne_v] using hli)
      trail_pos_inv := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        by_cases he : i = s.core.trail_end
        · subst he
          have htrl_s : (s'.core.trl[s.core.trail_end]?.getD 0#32).toNat / 2 = v := by
            simp [s', List.getElem?_set_self htrl_lt_len, v]
          rw [show (s'.core.trl[s.core.trail_end]?.getD 0#32).toNat / 2 = v from htrl_s]
          simp [s', List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte_lt32]
        · have hi0 : i < s.core.trail_end := by omega
          have htrl_s : (s'.core.trl[i]?.getD 0#32).toNat = (s.core.trl[i]?.getD 0#32).toNat := by
            simp [s', List.getElem?_set_ne (by omega : s.core.trail_end ≠ i)]
          have hne_v : v ≠ (s.core.trl[i]?.getD 0#32).toNat / 2 := (hnot_var i hi0).symm
          simpa [s', htrl_s, List.getElem?_set_ne hne_v] using hw.trail_pos_inv i hi0
      level0_rsn_none := fun i hi _ => hrsn_none i hi
      frame_trail_lt := fun L hL => by
        have hL0 : L = 0 := by rw [show s'.core.cur_level = 0 from hl0] at hL; omega
        subst hL0
        exact Nat.le_trans (hw.frame_trail_lt 0 (by omega))
          (by show s.core.trail_end ≤ s.core.trail_end + 1; omega)
      frame_trail_mono := fun L1 L2 h12 hL2 => by
        have hL0 : L2 = 0 := by rw [show s'.core.cur_level = 0 from hl0] at hL2; omega
        have hL1 : L1 = 0 := by omega
        subst hL0; subst hL1; exact Nat.le_refl _
      frame_trail_before_lt := fun L _ h2 => by
        change L ≤ s.core.cur_level at h2; omega
      frame_dec_lt := fun L _ h2 => by
        change L ≤ s.core.cur_level at h2; omega
      reason_inv := fun i hi hne => absurd (hrsn_none i hi) hne
      reason_lit_mem := fun i hi hne _ => absurd (hrsn_none i hi) hne }
  exact ⟨hlen', hw', hinv.2.2.1, hinv.2.2.2.1,
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr), hinv.2.2.2.2.2⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
