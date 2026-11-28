/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Helpers
public import LeanQbe.T.Examples.Kissat.Src.Dense
import LeanQbe.T.Logic.ControlComb

/-!
# Flat-Env WP Proofs for Dense Propagation (`full_m6_dense_prop_lit`, `full_m6_dense_prop`)

Proves `Spec.fullDensePropLitSpec` and `Spec.fullDensePropSpec` directly on `CanonicalEnv`
without legacy imports (`0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dense

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Dense
open scoped FullArenaTactics

local macro "dr_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Pure Helpers for Dense Propagation Invariants, Slices & Clause Scanning -/

private theorem dp_not_mem_erase {a : Nat} : ∀ {xs : List Nat}, xs.Nodup → a ∉ xs.erase a
  | [], _, h => by simp at h
  | x :: xs, hnd, hx => by
    rw [List.nodup_cons] at hnd
    by_cases hxa : x = a
    · subst hxa; simp at hx; exact hnd.1 hx
    · simp only [List.erase_cons, beq_false_of_ne hxa] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hxa rfl
      · exact dp_not_mem_erase hnd.2 hx'

private theorem dp_nodup_lt_len_le : ∀ {N : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < N) → xs.length ≤ N
  | 0, [], _, _ => Nat.zero_le 0
  | 0, x :: _, _, h => False.elim (Nat.not_lt_zero x (h x List.mem_cons_self))
  | N + 1, xs, hnd, hlt => by
    have hnd_e : (xs.erase N).Nodup := hnd.erase N
    have hlt_e : ∀ x ∈ xs.erase N, x < N := fun x hx => by
      have hmem := List.mem_of_mem_erase hx
      have hne : x ≠ N := fun heq => by subst heq; exact dp_not_mem_erase hnd hx
      have := hlt x hmem
      omega
    have hle := dp_nodup_lt_len_le hnd_e hlt_e
    by_cases hm : N ∈ xs
    · have hlen := List.length_erase_of_mem hm
      omega
    · rw [List.erase_of_not_mem hm] at hle
      omega

private theorem dp_nodup_range_map {f : Nat → Nat} : ∀ n,
    (∀ i < n, ∀ j < n, f i = f j → i = j) → ((List.range n).map f).Nodup
  | 0, _ => by simp
  | n + 1, hinj => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.nodup_append]
    refine ⟨dp_nodup_range_map n (fun i hi j hj => hinj i (by omega) j (by omega)), by simp,
      fun a ha b hb heq => ?_⟩
    simp only [List.mem_map, List.mem_range] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    obtain ⟨i, hi, rfl⟩ := ha
    subst hb
    exact absurd (hinj i (by omega) n (Nat.lt_succ_self n) heq) (by omega)

private theorem dp_div2_eq_cases (a b : Nat) (h : a / 2 = b / 2) : a = b ∨ a = b ^^^ 1 := by
  by_cases h0 : a.testBit 0 = b.testBit 0
  · left; apply Nat.eq_of_testBit_eq; intro k
    cases k with
    | zero => exact h0
    | succ k => simp [← Nat.testBit_div_two, h]
  · right; apply Nat.eq_of_testBit_eq; intro k
    cases k with
    | zero => rw [Nat.testBit_xor]; cases ha : a.testBit 0 <;> cases hb : b.testBit 0 <;> simp_all
    | succ k =>
      have h1 : (1 : Nat).testBit (k + 1) = false :=
        Nat.testBit_lt_two_pow (Nat.one_lt_pow (Nat.succ_ne_zero k) (by decide))
      rw [← Nat.testBit_div_two, h, Nat.testBit_div_two, Nat.testBit_xor, h1, Bool.xor_false]

private theorem dp_trail_lt_of_unassigned {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlk : FullCoreState.LengthsOk c k) (hw : FullWitnessInv c F0 F_cur k)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hun : k.vals[l]?.getD 0#8 = 0#8) :
    k.trail_end < c.max_vars := by
  let f : Nat → Nat := fun i => (k.trl[i]?.getD 0#32).toNat / 2
  let vs := (List.range k.trail_end).map f
  have hnd_vs : vs.Nodup := dp_nodup_range_map k.trail_end fun i hi j hj =>
    hw.trail_vars_nodup i j hi hj
  have hnot : l / 2 ∉ vs := by
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨i, hi, heq⟩ := hm
    rw [List.mem_range] at hi
    rcases dp_div2_eq_cases (k.trl[i]?.getD 0#32).toNat l heq with h | h
    · have ht := (hw.vals_true_iff l hl).mpr ⟨i, hi, h⟩
      rw [hun] at ht; revert ht; decide
    · have hf := (hw.vals_false_iff l hl).mpr ⟨i, hi, h⟩
      rw [hun] at hf; revert hf; decide
  have hnd : (l / 2 :: vs).Nodup := List.nodup_cons.mpr ⟨hnot, hnd_vs⟩
  have hlt : ∀ x ∈ (l / 2 :: vs), x < k.cur_vars := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · rw [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [List.mem_range] at hi
      have := hw.trail_lits_lt i hi
      dsimp only [f]
      omega
  have hlen := dp_nodup_lt_len_le hnd hlt
  have hlen_vs : (l / 2 :: vs).length = k.trail_end + 1 := by simp [vs]
  rw [hlen_vs] at hlen
  have := hlk.cur_vars_le
  omega

theorem dp_val_mem {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hb : l < k.vals.length) :
    k.vals[l]'hb = 0#8 ∨ k.vals[l]'hb = 1#8 ∨ k.vals[l]'hb = 0xFF#8 := by
  have hd := hw.vals_domain l hl
  simpa [List.getElem?_eq_getElem hb] using hd

theorem dp_pres_refl (s : FullState) : DensePropPres s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dp_pres_trans {s0 s1 s2 : FullState}
    (h1 : DensePropPres s0 s1) (h2 : DensePropPres s1 s2) : DensePropPres s0 s2 := by
  rcases h1 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩
  rcases h2 with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
    b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11, b12.trans a12, b13.trans a13⟩

private theorem dp_inv_with_phases {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {phases' : List (BitVec 8)} (hp : phases'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with phases := phases' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with phases_len := hp }⟩, h.2⟩

theorem dp_inv_set_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat)
    (ct cr cl0 cl1 : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with inconsistent := 1#64, confl_type := ct,
                                     confl_ref := cr, confl_lit0 := cl0, confl_lit1 := cl1 } } := by
  rcases h with ⟨⟨hc, hs⟩, hw, hlm, hnd, hext, hcl, hdm⟩
  refine ⟨⟨⟨hc.vals_len, hc.lit_mark_len, hc.mrk_len, hc.flags_len, hc.lvl_len, hc.rsns_len,
      hc.trl_len, hc.trail_pos_len, hc.tmp_len_arr, hc.min_clr_len_arr, hc.frame_trail_len,
      hc.frame_dec_len, hc.wvec_len, hc.repr_len, hc.min_stk_len, hc.arena_len_arr,
      hc.wstk_len_arr, hc.cur_vars_ge, hc.cur_vars_le, hc.arena_len_le, hc.wlen_le,
      hc.trail_end_le, hc.propagated_le, hc.tmp_len_le, hc.min_clr_len_le⟩, hs⟩,
    ⟨hw.ext_sound, fun _ => hu,
      ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt,
        hw.arena.entails⟩,
      hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr),
      hw.cur_level_le, hw.trail_lits_lt,
      hw.trail_vars_nodup, hw.vals_domain, hw.vals_true_iff, hw.vals_false_iff, hw.lvl_le,
      hw.dec_earliest, hw.levels_inhabited, hw.level0_sound, hw.trail_pos_inv,
      hw.level0_rsn_none, hw.frame_trail_lt, hw.frame_trail_mono, hw.frame_trail_before_lt,
      hw.frame_dec_lt, hw.reason_inv, hw.reason_lit_mem⟩,
    hlm, hnd, hext, hcl, hdm⟩

private theorem dp_inv_confl1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat)
    (ct cl0 cl1 : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with inconsistent := 1#64, confl_type := ct,
                                     confl_lit0 := cl0, confl_lit1 := cl1 } } :=
  dp_inv_set_confl h hu ct s.core.confl_ref cl0 cl1

private theorem dp_inv_confl_ref {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat)
    (ct cr : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with inconsistent := 1#64, confl_type := ct,
                                     confl_ref := cr } } :=
  dp_inv_set_confl h hu ct cr s.core.confl_lit0 s.core.confl_lit1

theorem dp_slice_mono {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw : k'.wstk = k.wstk) (hcv : k'.cur_vars = k.cur_vars)
    (hr : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k) :
    DenseWatchSliceOk F_cur k' lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hw0 hm hff hlt hent _ ih =>
    exact .bin (by rw [hw]; exact hw0) hm hff (by rw [hcv]; exact hlt) hent ih
  | occ hw0 hcr hm h3 hlt href _ ih =>
    exact .occ (by rw [hw]; exact hw0) (by rw [hw]; exact hcr) hm h3 hlt
      (by rw [hr]; exact href) ih

theorem dp_arena_lits_forall {k : FullCoreState} {r : Nat}
    (hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length)
    {P : Nat → Prop}
    (h : ∀ j (hj : j < fullArenaClauseSizeCore k r),
      P (k.arena[r + 3 + j]'(by omega)).toNat) :
    ∀ l ∈ fullArenaClauseLitsCore k r, P l := by
  intro l hl
  unfold fullArenaClauseLitsCore at hl
  rw [List.mem_map] at hl
  obtain ⟨w, hw, rfl⟩ := hl
  rw [List.mem_iff_getElem] at hw
  obtain ⟨j, hj, rfl⟩ := hw
  rw [List.length_take, List.length_drop] at hj
  have hj_sz : j < fullArenaClauseSizeCore k r := by omega
  rw [List.getElem_take, List.getElem_drop]
  exact h j hj_sz

theorem dp_arena_lit_lt {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k r = false)
    (hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length)
    {j : Nat} (hj : j < fullArenaClauseSizeCore k r) :
    (k.arena[r + 3 + j]'(by omega)).toNat < 2 * k.cur_vars := by
  apply ha.lits_lt r hr hng
  unfold fullArenaClauseLitsCore
  rw [List.mem_map]
  refine ⟨k.arena[r + 3 + j]'(by omega), ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨j, ?_, ?_⟩
  · rw [List.length_take, List.length_drop]; omega
  · rw [List.getElem_take, List.getElem_drop]

theorem dp_dense_watches {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) :
    DenseWatchesInv F_cur s.core := by
  have h1 := h.2.1.watches
  rw [ModeWatchesInv] at h1
  have hne : (s.core.dense_mode = 0#64) = False := eq_false h.2.2.2.2.2.2
  simp only [hne, ↓reduceIte] at h1
  exact h1

theorem dp_not_lit_lt {lit : BitVec 32} {cv : Nat}
    (h : (lit ^^^ 1#32).toNat < 2 * cv) : lit.toNat < 2 * cv := by
  have hx := dense_bv32_xor1_toNat lit
  have hdiv : lit.toNat / 2 = (lit.toNat ^^^ 1) / 2 := by
    apply Nat.eq_of_testBit_eq; intro k
    have h1 : (1 : Nat).testBit (k + 1) = false :=
      Nat.testBit_lt_two_pow (Nat.one_lt_pow (Nat.succ_ne_zero k) (by decide))
    simp [Nat.testBit_div_two, Nat.testBit_xor, h1]
  omega

theorem dp_not_not_lit {lit : BitVec 32} :
    (lit ^^^ 1#32).toNat ^^^ 1 = lit.toNat := by
  rw [dense_bv32_xor1_toNat, Nat.xor_assoc]
  simp

theorem dp_garb_false_of_hdr {k : FullCoreState} {cref : Nat} (hbd : cref < k.arena.length)
    (hhdr : (k.arena[cref]'hbd &&& 0x00080000#32) = 0#32) :
    fullArenaClauseGarbCore k cref = false := by
  unfold fullArenaClauseGarbCore fullArenaHdrCore
  rw [List.getElem?_eq_getElem hbd, Option.getD_some, hhdr]
  decide

private theorem dp_close_lit_q_true {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sF : FullState} {R : Mem 64 → Prop} {mF : Mem 64} {Q : Post [.bool]}
    (hinvF : FullDenseInvW c F0 F_cur sF) (hpresF : DensePropPres s sF)
    (hpropF : sF.core.propagated = s.core.propagated) (hteF : s.core.trail_end ≤ sF.core.trail_end)
    (hincF : sF.core.inconsistent = s.core.inconsistent) (hmF : (FullMem c sF ⋆ R) mF)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.propagated = s.core.propagated →
      s.core.trail_end ≤ s'.core.trail_end → s'.core.repr = s.core.repr →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (ok = true → s'.core.inconsistent = s.core.inconsistent) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (true, ()) mF := by
  rcases hpresF with ⟨p1, p2, p3, p4, p5, p6, p7, -, p9, p10, p11, -, p13⟩
  exact hQ true sF mF hinvF p1 p3 hpropF hteF p4 p2 p5 p6 p7 p9 p10 p11 p13
    (by simp) (fun _ => hincF) hmF

private theorem dp_close_lit_q_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sF : FullState} {R : Mem 64 → Prop} {mF : Mem 64} {Q : Post [.bool]}
    (hinvF : FullDenseInvW c F0 F_cur sF) (hpresF : DensePropPres s sF)
    (hpropF : sF.core.propagated = s.core.propagated) (hteF : s.core.trail_end ≤ sF.core.trail_end)
    (hunsat : F0.Unsat) (hinc : sF.core.inconsistent ≠ 0#64) (hmF : (FullMem c sF ⋆ R) mF)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.propagated = s.core.propagated →
      s.core.trail_end ≤ s'.core.trail_end → s'.core.repr = s.core.repr →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (ok = true → s'.core.inconsistent = s.core.inconsistent) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (false, ()) mF := by
  rcases hpresF with ⟨p1, p2, p3, p4, p5, p6, p7, -, p9, p10, p11, -, p13⟩
  exact hQ false sF mF hinvF p1 p3 hpropF hteF p4 p2 p5 p6 p7 p9 p10 p11 p13
    (fun _ => ⟨hunsat, hinc⟩) (fun h => by cases h) hmF

@[expose] def DpOccScanInv (k : FullCoreState) (cref sz : Nat)
    (hsz_eq : sz = fullArenaClauseSizeCore k cref)
    (hbd : cref + 3 + sz ≤ k.arena.length) (unass unit_lit : BitVec 32)
    (bound : Nat) (hbnd : bound ≤ sz) : Prop :=
  (unass = 0#32 ∧ ∀ q (hq : q < bound),
    k.vals[(k.arena[cref + 3 + q]'(by omega)).toNat]?.getD 0#8 = 0xFF#8) ∨
  (unass = 1#32 ∧ ∃ q0, ∃ _ : q0 < bound,
    have hq0_sz : q0 < sz := by omega
    have hq0 : cref + 3 + q0 < k.arena.length := by omega
    unit_lit.toNat = (k.arena[cref + 3 + q0]'hq0).toNat ∧
    k.vals[unit_lit.toNat]?.getD 0#8 = 0#8 ∧
    ∀ q (hq : q < bound), q ≠ q0 →
      k.vals[(k.arena[cref + 3 + q]'(by omega)).toNat]?.getD 0#8 = 0xFF#8)

theorem dp_occ_scan_step {k : FullCoreState} {cref sz : Nat}
    {hsz_eq : sz = fullArenaClauseSizeCore k cref} {hbd : cref + 3 + sz ≤ k.arena.length}
    {unass unit_lit lit_j : BitVec 32} {j : Nat} (hj : j < sz)
    (hlit : lit_j = k.arena[cref + 3 + j]'(by omega))
    (hinv : DpOccScanInv k cref sz hsz_eq hbd unass unit_lit j (by omega)) :
    (k.vals[lit_j.toNat]?.getD 0#8 = 0#8 →
      ((unass = 0#32 →
        DpOccScanInv k cref sz hsz_eq hbd 1#32 lit_j (j + 1) (by omega)) ∧
       (unass ≠ 0#32 → unass = 1#32))) ∧
    (k.vals[lit_j.toNat]?.getD 0#8 = 0xFF#8 →
      DpOccScanInv k cref sz hsz_eq hbd unass unit_lit (j + 1) (by omega)) := by
  refine ⟨fun hv0 => ⟨fun hu0 => ?_, fun hne => ?_⟩, fun hvff => ?_⟩
  · right
    rcases hinv with ⟨-, hall⟩ | ⟨hu1, -⟩
    · refine ⟨rfl, j, Nat.lt_succ_self j, by rw [hlit], hv0, fun q hq _ => ?_⟩
      exact hall q (by omega)
    · rw [hu1] at hu0; cases hu0
  · rcases hinv with ⟨hu0, -⟩ | ⟨hu1, -⟩
    · exact absurd hu0 hne
    · exact hu1
  · rcases hinv with ⟨hu0, hall⟩ | ⟨hu1, q0, hq0, heq0, hv0, hall⟩
    · refine Or.inl ⟨hu0, fun q hq => ?_⟩
      by_cases hqj : q = j
      · subst hqj; rw [← hlit]; exact hvff
      · exact hall q (by omega)
    · refine Or.inr ⟨hu1, q0, by omega, heq0, hv0, fun q hq hnq => ?_⟩
      by_cases hqj : q = j
      · subst hqj; rw [← hlit]; exact hvff
      · exact hall q (by omega) hnq

theorem dp_occ_all_false_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {cref sz : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    (hgarb : fullArenaClauseGarbCore k cref = false)
    (hsz_eq : sz = fullArenaClauseSizeCore k cref)
    (hbd : cref + 3 + sz ≤ k.arena.length)
    (hall : ∀ q (hq : q < sz),
      k.vals[(k.arena[cref + 3 + q]'(by omega)).toNat]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).Unsat := by
  apply dense_clause_all_false_unsat hw hcl0 (hw.arena.entails cref href hgarb)
    (hw.arena.lits_lt cref href hgarb)
  exact dp_arena_lits_forall (hsz_eq ▸ hbd) fun j hj => hall j (by rw [hsz_eq]; exact hj)

theorem dp_occ_unit_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {cref sz : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    (hgarb : fullArenaClauseGarbCore k cref = false)
    (hsz_eq : sz = fullArenaClauseSizeCore k cref)
    (hbd : cref + 3 + sz ≤ k.arena.length) {unit_lit : BitVec 32}
    {q0 : Nat} (hq0 : q0 < sz)
    (heq0 : unit_lit.toNat = (k.arena[cref + 3 + q0]'(by omega)).toNat)
    (_hv0 : k.vals[unit_lit.toNat]?.getD 0#8 = 0#8)
    (hall : ∀ q (hq : q < sz), q ≠ q0 →
      k.vals[(k.arena[cref + 3 + q]'(by omega)).toNat]?.getD 0#8 = 0xFF#8) :
    unit_lit.toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [unit_lit.toNat]) := by
  have hlt_u : unit_lit.toNat < 2 * k.cur_vars := by
    rw [heq0]
    exact dp_arena_lit_lt hw.arena href hgarb (hsz_eq ▸ hbd) (by rw [← hsz_eq]; exact hq0)
  refine ⟨hlt_u, dense_clause_one_unass_entails hw hcl0 (hw.arena.entails cref href hgarb)
    (hw.arena.lits_lt cref href hgarb) ?_⟩
  intro l hl hne
  unfold fullArenaClauseLitsCore at hl
  rw [List.mem_map] at hl
  obtain ⟨w, hmw, rfl⟩ := hl
  rw [List.mem_iff_getElem] at hmw
  obtain ⟨q, hq, rfl⟩ := hmw
  rw [List.length_take, List.length_drop] at hq
  have hq_sz : q < sz := by rw [hsz_eq]; omega
  rw [List.getElem_take, List.getElem_drop]
  by_cases hqq0 : q = q0
  · subst hqq0
    exfalso; apply hne
    simp only [List.getElem_take, List.getElem_drop]; rw [heq0]
  · exact hall q hq_sz hqq0

private theorem dp_assign_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} (hinvL : FullDenseInvW c F0 F_cur sL) (hpresL : DensePropPres s sL)
    (hteL : s.core.trail_end ≤ sL.core.trail_end)
    {not_lit ul : BitVec 32} {p_next end_off : Nat}
    (hlt_u : ul.toNat < 2 * sL.core.cur_vars)
    (hv0 : sL.core.vals[ul.toNat]?.getD 0#8 = 0#8)
    (hent_u : (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]))
    {flags' : List (BitVec 32)} (hfl : flags'.length = c.max_vars)
    (unass' : BitVec 64) {phases' : List (BitVec 8)} (hph : phases'.length = c.max_vars)
    (hslice : DenseWatchSliceOk F_cur sL.core not_lit.toNat p_next (end_off - p_next)) :
    let sA : FullState :=
      { sL with
        core := { sL.core with
          vals := (sL.core.vals.set ul.toNat 1#8).set (ul.toNat ^^^ 1) 255#8,
          flags := flags', lvl := sL.core.lvl.set (ul.toNat / 2) 0#32,
          rsns := sL.core.rsns.set (ul.toNat / 2) 4294967295#32,
          trl := sL.core.trl.set sL.core.trail_end ul,
          trail_pos := sL.core.trail_pos.set (ul.toNat / 2)
            (BitVec.ofNat 32 sL.core.trail_end),
          unassigned := unass', unflushed := sL.core.unflushed + 1#64,
          trail_end := sL.core.trail_end + 1 }
        scratch := { sL.scratch with phases := phases' } }
    FullDenseInvW c F0 F_cur sA ∧ DensePropPres s sA ∧ s.core.trail_end ≤ sA.core.trail_end ∧
      DenseWatchSliceOk F_cur sA.core not_lit.toNat p_next (end_off - p_next) := by
  have hinvA0 := fullDenseInvW_assignLvl0 hinvL hlt_u hv0 hent_u hfl unass'
    (sL.core.unflushed + 1#64)
  exact ⟨dp_inv_with_phases hinvA0 hph, dp_pres_trans hpresL (dp_pres_refl sL),
    by dsimp only; omega, dp_slice_mono hslice rfl rfl rfl⟩

theorem dp_bv64_shl1_nat (x : Nat) (hx : 2 * x < 2 ^ 64) :
    (BitVec.ofNat 64 x <<< 1#64).toNat = 2 * x := by
  have hlt : 2 * (BitVec.ofNat 64 x).toNat < 2 ^ 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hx
  have h := dense_bv64_shl1_bv (BitVec.ofNat 64 x) hlt
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h

theorem dp_val_ff_of_sle_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hb : l < k.vals.length)
    (hf : (0#32).sle (BitVec.signExtend 32 (k.vals[l]'hb)) = false) :
    k.vals[l]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hb]
  rcases dp_val_mem hw hl hb with hv | hv | hv <;> rw [hv] at hf ⊢
  · revert hf; decide
  · revert hf; decide
  · rfl

theorem dp_val_ff_of_slt_true {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hb : l < k.vals.length)
    (ht : (BitVec.signExtend 32 (k.vals[l]'hb)).slt 0#32 = true) :
    k.vals[l]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hb]
  rcases dp_val_mem hw hl hb with hv | hv | hv <;> rw [hv] at ht ⊢
  · revert ht; decide
  · revert ht; decide
  · rfl

theorem dp_val_zero_of_slt_slt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hb : l < k.vals.length)
    (h1 : (0#32).slt (BitVec.signExtend 32 (k.vals[l]'hb)) = false)
    (h2 : (BitVec.signExtend 32 (k.vals[l]'hb)).slt 0#32 = false) :
    k.vals[l]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hb]
  rcases dp_val_mem hw hl hb with hv | hv | hv <;> rw [hv] at h1 h2 ⊢
  · rfl
  · revert h1; decide
  · revert h2; decide

theorem dp_val_0_or_ff_of_slt_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hb : l < k.vals.length)
    (hf : (0#32).slt (BitVec.signExtend 32 (k.vals[l]'hb)) = false) :
    k.vals[l]?.getD 0#8 = 0#8 ∨ k.vals[l]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hb]
  rcases dp_val_mem hw hl hb with hv | hv | hv <;> rw [hv] at hf ⊢
  · exact Or.inl rfl
  · revert hf; decide
  · exact Or.inr rfl

theorem dp_val_zero_of_sext_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hb : l < k.vals.length) (heq : BitVec.signExtend 32 (k.vals[l]'hb) = 0#32) :
    k.vals[l]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hb]
  rcases dp_val_mem hw hl hb with hv | hv | hv <;> rw [hv] at heq ⊢
  · rfl
  · revert heq; decide
  · revert heq; decide

theorem dp_val_ff_of_slt_ne {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hb : l < k.vals.length)
    (h1 : (0#32).slt (BitVec.signExtend 32 (k.vals[l]'hb)) = false)
    (h2 : BitVec.signExtend 32 (k.vals[l]'hb) ≠ 0#32) :
    k.vals[l]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hb]
  rcases dp_val_mem hw hl hb with hv | hv | hv <;> rw [hv] at h1 h2 ⊢
  · exact absurd rfl h2
  · revert h1; decide
  · rfl

private theorem dp_mem_congr {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := h ▸ hm

theorem dp_get_congr {α : Type _} {xs : List α} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (h : i = j) :
    xs[i]'hi = xs[j]'hj := by subst h; rfl

private theorem dp_bin_step_setup {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} (hinvL : FullDenseInvW c F0 F_cur sL) (hpresL : DensePropPres s sL)
    {lit : BitVec 32} {p : BitVec 64} {end_off : Nat}
    (hp_bd : p.toNat < sL.core.wstk.length) (hp1_eq : (p + 1#64).toNat = p.toNat + 1)
    {w0 : BitVec 32} (hw0 : w0 = sL.core.wstk[p.toNat]'hp_bd)
    (hslice_n : DenseWatchSliceOk F_cur sL.core (lit ^^^ 1#32).toNat (p.toNat + 1)
      (end_off - p.toNat - 1))
    (hbin_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(lit ^^^ 1#32).toNat, w0.toNat &&& 0x7FFFFFFF]))
    (hoth_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * sL.core.cur_vars)
    (hlit_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let other := w0 &&& 0x7FFFFFFF#32
    ¬ (2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ other.toNat) ∧
    other.toNat < sL.core.vals.length ∧
    (BitVec.setWidth 64 other).toNat < sL.core.vals.length ∧
    DenseWatchSliceOk F_cur sL.core (lit ^^^ 1#32).toNat
      (p + 1#64).toNat (end_off - (p + 1#64).toNat) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [other.toNat]) := by
  subst hw0
  have hlkL := hinvL.1.core_ok
  have hcv_ltL : 2 * sL.core.cur_vars < 2 ^ 64 := by
    have := c.hmaxv; unfold dimacsBound at this; have := hlkL.cur_vars_le; omega
  have hnot_le : ¬ (2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤
      (sL.core.wstk[p.toNat]'hp_bd &&& 0x7FFFFFFF#32).toNat) := by
    have hcv64 : s.core.cur_vars < 2 ^ 64 := by rw [← hpresL.1]; omega
    have hcv_lt0 : 2 * s.core.cur_vars < 2 ^ 64 := by rw [← hpresL.1]; exact hcv_ltL
    rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt hcv_lt0, ← hpresL.1]; omega
  have hoth_bd : (sL.core.wstk[p.toNat]'hp_bd &&& 0x7FFFFFFF#32).toNat < sL.core.vals.length := by
    have := hlkL.vals_len; have := hlkL.cur_vars_le; omega
  have hoth_bv_bd : (BitVec.setWidth 64
      (sL.core.wstk[p.toNat]'hp_bd &&& 0x7FFFFFFF#32)).toNat < sL.core.vals.length := by
    rw [dense_zext32_toNat]; exact hoth_bd
  have hslice_n' : DenseWatchSliceOk F_cur sL.core (lit ^^^ 1#32).toNat
      (p + 1#64).toNat (end_off - (p + 1#64).toNat) := by
    rw [hp1_eq]
    simpa [show end_off - p.toNat - 1 = end_off - (p.toNat + 1) by omega] using hslice_n
  have hent_oth : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(sL.core.wstk[p.toNat]'hp_bd &&& 0x7FFFFFFF#32).toNat]) := by
    have hl' : (cnfOfClauses F_cur).EntailsClause (cnfClause [(lit ^^^ 1#32).toNat ^^^ 1]) := by
      rwa [dp_not_not_lit]
    have hr := dense_resolve_bin_unit hbin_ent (Or.inl rfl) hl'
    simpa [BitVec.toNat_and] using hr
  exact ⟨hnot_le, hoth_bd, hoth_bv_bd, hslice_n', hent_oth⟩

private theorem dp_occ_bad_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} (hinvL : FullDenseInvW c F0 F_cur sL) (hpresL : DensePropPres s sL)
    {lit_idx lit_j : BitVec 32} (hlj_mod : lit_idx = lit_j)
    (hlj_lt : lit_j.toNat < 2 * sL.core.cur_vars)
    (hge : ¬ lit_idx.toNat < 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64) : False := by
  have hlkL := hinvL.1.core_ok
  have := c.hmaxv; unfold dimacsBound at this
  have := hlkL.cur_vars_le
  have hcv64 : s.core.cur_vars < 2 ^ 64 := by rw [← hpresL.1]; omega
  have hcv_lt0 : 2 * s.core.cur_vars < 2 ^ 64 := by rw [← hpresL.1]; omega
  rw [hlj_mod, Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt hcv_lt0, ← hpresL.1] at hge
  exact hge hlj_lt

theorem dp_lit_wvec_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) (lit : BitVec 32)
    (hnot_lt : (lit ^^^ 1#32).toNat < 2 * s.core.cur_vars) :
    let nl := lit ^^^ 1#32
    (BitVec.setWidth 64 nl <<< 1#64).toNat = 2 * nl.toNat ∧
    (BitVec.setWidth 64 nl <<< 1#64).toNat < s.core.wvec.length ∧
    (BitVec.setWidth 64 nl <<< 1#64 + 1#64).toNat = 2 * nl.toNat + 1 ∧
    (BitVec.setWidth 64 nl <<< 1#64 + 1#64).toNat < s.core.wvec.length ∧
    2 * (lit.toNat ^^^ 1) % 2 ^ 64 < s.core.wvec.length ∧
    (2 * (lit.toNat ^^^ 1) + BitVec.toNat 1#64) % 2 ^ 64 < s.core.wvec.length := by
  intro nl
  have hlk := hinv.1.core_ok
  have hnot_ze : (BitVec.setWidth 64 nl).toNat = nl.toNat := dense_zext32_toNat nl
  have h2nl_lt : 2 * nl.toNat + 1 < s.core.wvec.length := by
    dsimp only [nl]; have := hlk.wvec_len; have := hlk.cur_vars_le; omega
  have hshl : (BitVec.setWidth 64 nl <<< 1#64).toNat = 2 * nl.toNat := by
    have hlt_nl : 2 * (BitVec.setWidth 64 nl).toNat < 2 ^ 64 := by
      rw [hnot_ze]; have := hlk.cur_vars_le; omega
    rw [dense_bv64_shl1_bv _ hlt_nl, hnot_ze]
  have h1 : 1 < 2 ^ 64 := by decide
  have hnl1_64 : 2 * nl.toNat + 1 < 2 ^ 64 := by have := hlk.cur_vars_le; omega
  have hshl1 : (BitVec.setWidth 64 nl <<< 1#64 + 1#64).toNat = 2 * nl.toNat + 1 := by
    rw [BitVec.toNat_add, hshl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hnl1_64]
  have hxor_nl : lit.toNat ^^^ 1 = nl.toNat := (dense_bv32_xor1_toNat lit).symm
  have hm0 : 2 * (lit.toNat ^^^ 1) % 2 ^ 64 < s.core.wvec.length := by
    rw [hxor_nl, ← hshl]; rw [hshl]; omega
  have hm1 : (2 * (lit.toNat ^^^ 1) + BitVec.toNat 1#64) % 2 ^ 64 < s.core.wvec.length := by
    rw [hxor_nl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hnl1_64]; exact h2nl_lt
  exact ⟨hshl, by rw [hshl]; omega, hshl1, by rw [hshl1]; exact h2nl_lt, hm0, hm1⟩

theorem dp_lit_end_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) (lit : BitVec 32)
    (hnot_lt : (lit ^^^ 1#32).toNat < 2 * s.core.cur_vars)
    {h2nl_shl : (BitVec.setWidth 64 (lit ^^^ 1#32) <<< 1#64).toNat < s.core.wvec.length}
    {h2nl_shl1 : (BitVec.setWidth 64 (lit ^^^ 1#32) <<< 1#64 + 1#64).toNat < s.core.wvec.length}
    {hm0 : 2 * (lit.toNat ^^^ 1) % 2 ^ 64 < s.core.wvec.length}
    {hm1 : (2 * (lit.toNat ^^^ 1) + BitVec.toNat 1#64) % 2 ^ 64 < s.core.wvec.length} :
    let nl := lit ^^^ 1#32
    let off := s.core.wvec[(BitVec.setWidth 64 nl <<< 1#64).toNat]'h2nl_shl
    let sz := s.core.wvec[(BitVec.setWidth 64 nl <<< 1#64 + 1#64).toNat]'h2nl_shl1
    let end_off : BitVec 64 := BitVec.setWidth 64 off + BitVec.setWidth 64 sz
    off.toNat = fullWatchOffCore s.core nl.toNat ∧
    sz.toNat = fullWatchSizeCore s.core nl.toNat ∧
    end_off.toNat = off.toNat + sz.toNat ∧ end_off.toNat ≤ c.wcap ∧
    (s.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'hm0).toNat +
      (s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat 1#64) % 2 ^ 64]'hm1).toNat < 2 ^ 64 ∧
    ((s.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'hm0).toNat +
      (s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat 1#64) % 2 ^ 64]'hm1).toNat) % 2 ^ 64 =
      end_off.toNat := by
  intro nl off sz end_off
  obtain ⟨hshl, _, hshl1, _, _, _⟩ := dp_lit_wvec_bounds hinv lit hnot_lt
  have hlk := hinv.1.core_ok
  have hw0 : off.toNat = fullWatchOffCore s.core nl.toNat := by
    have hget : s.core.wvec[2 * nl.toNat]? = some off := by
      rw [← hshl, List.getElem?_eq_getElem h2nl_shl]
    unfold fullWatchOffCore; rw [hget]; rfl
  have hsz : sz.toNat = fullWatchSizeCore s.core nl.toNat := by
    have hget : s.core.wvec[2 * nl.toNat + 1]? = some sz := by
      rw [← hshl1, List.getElem?_eq_getElem h2nl_shl1]
    unfold fullWatchSizeCore; rw [hget]; rfl
  have hdw0 := dp_dense_watches hinv
  have hwb := hdw0.layout.bounds nl.toNat hnot_lt
  have hwcap_lt : c.wcap < 2 ^ 31 := by have := c.hwcap; unfold dimacsBound at this; omega
  have hwl_le : s.core.wlen ≤ c.wcap := hlk.wlen_le
  have hend_nat : end_off.toNat = off.toNat + sz.toNat := by
    dsimp only [end_off]; rw [BitVec.toNat_add, dense_zext32_toNat, dense_zext32_toNat,
      Nat.mod_eq_of_lt]; rw [hw0, hsz]; omega
  have hend_le : end_off.toNat ≤ c.wcap := by rw [hend_nat, hw0, hsz]; omega
  have hxor_nl : lit.toNat ^^^ 1 = nl.toNat := (dense_bv32_xor1_toNat lit).symm
  have h1 : 1 < 2 ^ 64 := by decide
  have hnl1_64 : 2 * nl.toNat + 1 < 2 ^ 64 := by have := hlk.cur_vars_le; omega
  have hnl0_64 : 2 * nl.toNat < 2 ^ 64 := by omega
  have hg0 : s.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'hm0 = off :=
    dp_get_congr hm0 h2nl_shl (by rw [hxor_nl, Nat.mod_eq_of_lt hnl0_64, hshl])
  have hg1 : s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat 1#64) % 2 ^ 64]'hm1 = sz :=
    dp_get_congr hm1 h2nl_shl1
      (by rw [hxor_nl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hnl1_64, hshl1])
  have hlt64 : (s.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'hm0).toNat +
      (s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat 1#64) % 2 ^ 64]'hm1).toNat < 2 ^ 64 := by
    rw [hg0, hg1, ← hend_nat]; exact end_off.isLt
  have hbv : ((s.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'hm0).toNat +
      (s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat 1#64) % 2 ^ 64]'hm1).toNat) % 2 ^ 64 =
      end_off.toNat := by
    rw [hg0, hg1, ← hend_nat, Nat.mod_eq_of_lt end_off.isLt]
  exact ⟨hw0, hsz, hend_nat, hend_le, hlt64, hbv⟩

theorem dp_occ_mark_garb_bv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} (hinvL : FullDenseInvW c F0 F_cur sL) (hpresL : DensePropPres s sL)
    {cref idx : Nat} (hidx : idx = cref) (hcr_ref : cref ∈ fullArenaClauseRefsCore sL.core)
    (hidx_bd : idx < sL.core.arena.length)
    {not_lit : BitVec 32} {p2 end_off : Nat}
    (hslice2 : DenseWatchSliceOk F_cur sL.core not_lit.toNat p2 (end_off - p2))
    (ag' : BitVec 64) :
    let hdr' := sL.core.arena[idx]'hidx_bd ||| 0x00080000#32
    let ar' := sL.core.arena.set idx hdr'
    let sG : FullState :=
      { sL with core := { sL.core with arena := ar', arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur sG ∧ DensePropPres s sG ∧
      DenseWatchSliceOk F_cur sG.core not_lit.toNat p2 (end_off - p2) := by
  subst hidx
  intro hdr' ar' sG
  have hlkL := hinvL.1.core_ok
  have har_len : ar'.length = c.arena_cap := by
    dsimp only [ar']; rw [List.length_set, hlkL.arena_len_arr]
  have har_eq : ar' = sL.core.arena.set idx (fullArenaHdr sL idx ||| 524288#32) := by
    dsimp only [ar', hdr', fullArenaHdr, fullArenaHdrCore]
    rw [List.getElem?_eq_getElem hidx_bd]; rfl
  obtain ⟨hinvG, hrefsG⟩ := fullDenseInvW_markGarb hinvL hcr_ref har_len har_eq (ag' := ag')
  exact ⟨hinvG, dp_pres_trans hpresL ⟨rfl, rfl, rfl, rfl, hrefsG, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩, dp_slice_mono hslice2 rfl rfl hrefsG⟩

theorem dp_occ_scan_cast {k : FullCoreState} {cref sz : Nat}
    {hsz_eq : sz = fullArenaClauseSizeCore k cref} {hbd : cref + 3 + sz ≤ k.arena.length}
    {unass ul : BitVec 32} {b1 b2 : Nat} (heq : b1 = b2) {h1 : b1 ≤ sz} {h2 : b2 ≤ sz}
    (h : DpOccScanInv k cref sz hsz_eq hbd unass ul b1 h1) :
    DpOccScanInv k cref sz hsz_eq hbd unass ul b2 h2 := by
  subst heq; exact h

theorem dp_occ_cref_setup {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sL : FullState} (hinvL : FullDenseInvW c F0 F_cur sL)
    {p : BitVec 64} {end_off : Nat} (hend_le : end_off ≤ c.wcap)
    (hp2_le : p.toNat + 2 ≤ end_off) (hp1_eq : (p + 1#64).toNat = p.toNat + 1)
    {cref32 : BitVec 32} (hcr_ref : cref32.toNat ∈ fullArenaClauseRefsCore sL.core)
    (hw_cr : sL.core.wstk[p.toNat + 1]? = some cref32) :
    ∃ (hp1_bd : (p + 1#64).toNat < sL.core.wstk.length)
      (hp1_m_bd : (p.toNat + BitVec.toNat 1#64) % 2 ^ 64 < sL.core.wstk.length)
      (hcr_bd : cref32.toNat < sL.core.arena.length)
      (hcr2_bd : cref32.toNat + 2 < sL.core.arena.length)
      (hcr_m_bd : (sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat <
        sL.core.arena.length)
      (hcr2_m_bd : ((sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
        BitVec.toNat 2#64) % 2 ^ 64 < sL.core.arena.length),
      sL.core.wstk[(p + 1#64).toNat]'hp1_bd = cref32 ∧
      sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd = cref32 ∧
      (p + 2#64).toNat = p.toNat + 2 ∧
      p + (1 : BitVec 64) + (1 : BitVec 64) = p + 2#64 ∧
      (BitVec.setWidth 64 cref32).toNat = cref32.toNat ∧
      (BitVec.setWidth 64 (sL.core.wstk[(p + 1#64).toNat]'hp1_bd)).toNat <
        sL.core.arena.length ∧
      ¬ (sL.core.arena_len % 2 ^ 64 < ((sL.core.wstk[(p.toNat + BitVec.toNat 1#64) %
        2 ^ 64]'hp1_m_bd).toNat + BitVec.toNat 3#64) % 2 ^ 64) ∧
      sL.core.arena[(sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat]'
        hcr_m_bd = sL.core.arena[cref32.toNat]'hcr_bd ∧
      sL.core.arena[((sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
        BitVec.toNat 2#64) % 2 ^ 64]'hcr2_m_bd = sL.core.arena[cref32.toNat + 2]'hcr2_bd ∧
      (sL.core.arena[cref32.toNat + 2]'hcr2_bd).toNat =
        fullArenaClauseSizeCore sL.core cref32.toNat ∧
      ¬ ((sL.core.arena[cref32.toNat + 2]'hcr2_bd).toNat < 3) ∧
      ¬ (sL.core.arena_len % 2 ^ 64 < ((sL.core.wstk[(p.toNat + BitVec.toNat 1#64) %
        2 ^ 64]'hp1_m_bd).toNat + BitVec.toNat 3#64 + (sL.core.arena[((sL.core.wstk[(p.toNat +
          BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat + BitVec.toNat 2#64) % 2 ^ 64]'
          hcr2_m_bd).toNat) % 2 ^ 64) ∧
      cref32.toNat + 3 + (sL.core.arena[cref32.toNat + 2]'hcr2_bd).toNat ≤
        sL.core.arena.length := by
  have hlkL := hinvL.1.core_ok
  have hwL := hinvL.2.1
  have hp1_bd : (p + 1#64).toNat < sL.core.wstk.length := by
    rw [hlkL.wstk_len_arr, hp1_eq]; omega
  have h1_lt : 1 < 2 ^ 64 := by decide
  have h2_lt : 2 < 2 ^ 64 := by decide
  have h3_lt : 3 < 2 ^ 64 := by decide
  have hp1_lt64 : p.toNat + 1 < 2 ^ 64 := by
    have := c.hwcap; unfold dimacsBound at this; omega
  have hp1_mod : (p.toNat + BitVec.toNat 1#64) % 2 ^ 64 = (p + 1#64).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt, hp1_eq, Nat.mod_eq_of_lt hp1_lt64]
  have hp1_m_bd : (p.toNat + BitVec.toNat 1#64) % 2 ^ 64 < sL.core.wstk.length := by
    rw [hp1_mod]; exact hp1_bd
  have hcr_wstk : sL.core.wstk[(p + 1#64).toNat]'hp1_bd = cref32 := by
    have h1 : sL.core.wstk[p.toNat + 1]?.getD 0#32 = cref32 := by rw [hw_cr]; rfl
    have hp1_nat : p.toNat + 1 < sL.core.wstk.length := by omega
    rw [List.getElem?_eq_getElem hp1_nat, Option.getD_some] at h1
    exact (dp_get_congr hp1_bd hp1_nat hp1_eq).trans h1
  have hcr_w_bv : sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd = cref32 :=
    (dp_get_congr hp1_m_bd hp1_bd hp1_mod).trans hcr_wstk
  have hwf_c := hwL.arena.refs_wf cref32.toNat hcr_ref
  have har_len_lt : c.arena_cap < 2 ^ 30 := by
    have := c.harena; unfold dimacsBound at this; omega
  have hcr_bd : cref32.toNat < sL.core.arena.length := by
    rw [hlkL.arena_len_arr]; have := hwf_c.1; have := hlkL.arena_len_le; omega
  have hcr2_bd : cref32.toNat + 2 < sL.core.arena.length := by
    rw [hlkL.arena_len_arr]; have := hwf_c.1; have := hlkL.arena_len_le; omega
  have hcr_m_bd : (sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat <
      sL.core.arena.length := by
    rw [hcr_w_bv]; exact hcr_bd
  have hcr2_lt64 : cref32.toNat + 2 < 2 ^ 64 := by omega
  have hcr2_mod : ((sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
      BitVec.toNat 2#64) % 2 ^ 64 = cref32.toNat + 2 := by
    rw [hcr_w_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt, Nat.mod_eq_of_lt hcr2_lt64]
  have hcr2_m_bd : ((sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
      BitVec.toNat 2#64) % 2 ^ 64 < sL.core.arena.length := by
    rw [hcr2_mod]; exact hcr2_bd
  have hp2_lt64 : p.toNat + 2 < 2 ^ 64 := by
    have := c.hwcap; unfold dimacsBound at this; omega
  have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt, Nat.mod_eq_of_lt hp2_lt64]
  have hp2_bv : p + (1 : BitVec 64) + (1 : BitVec 64) = p + 2#64 := by
    rw [BitVec.add_assoc]; rfl
  have hcr_ze : (BitVec.setWidth 64 cref32).toNat = cref32.toNat := dense_zext32_toNat cref32
  have ha0_mem : (BitVec.setWidth 64 (sL.core.wstk[(p + 1#64).toNat]'hp1_bd)).toNat <
      sL.core.arena.length := by
    rw [hcr_wstk, hcr_ze]; exact hcr_bd
  have har_hdr_bv : sL.core.arena[(sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'
      hp1_m_bd).toNat]'hcr_m_bd = sL.core.arena[cref32.toNat]'hcr_bd :=
    dp_get_congr hcr_m_bd hcr_bd (by rw [hcr_w_bv])
  have hsz_bv : sL.core.arena[((sL.core.wstk[(p.toNat + BitVec.toNat 1#64) % 2 ^ 64]'
      hp1_m_bd).toNat + BitVec.toNat 2#64) % 2 ^ 64]'hcr2_m_bd =
      sL.core.arena[cref32.toNat + 2]'hcr2_bd :=
    dp_get_congr hcr2_m_bd hcr2_bd hcr2_mod
  have hsz_eq : (sL.core.arena[cref32.toNat + 2]'hcr2_bd).toNat =
      fullArenaClauseSizeCore sL.core cref32.toNat := by
    unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem hcr2_bd]; rfl
  have hal64 : sL.core.arena_len < 2 ^ 64 := by have := hlkL.arena_len_le; omega
  have hcr3_64 : cref32.toNat + 3 < 2 ^ 64 := by omega
  have hnot_lt_a3 : ¬ (sL.core.arena_len % 2 ^ 64 < ((sL.core.wstk[(p.toNat +
      BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat + BitVec.toNat 3#64) % 2 ^ 64) := by
    rw [hcr_w_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3_lt,
      Nat.mod_eq_of_lt hal64, Nat.mod_eq_of_lt hcr3_64]
    have := hwf_c.1; omega
  have hnot_lt3 : ¬ ((sL.core.arena[cref32.toNat + 2]'hcr2_bd).toNat < 3) := by
    rw [hsz_eq]; have := hwf_c.2.1; omega
  have hcr_end64 : cref32.toNat + 3 + (sL.core.arena[cref32.toNat + 2]'hcr2_bd).toNat < 2 ^ 64 := by
    rw [hsz_eq]; have := hwf_c.2.2.1; have := hwf_c.2.2.2.1; omega
  have hnot_gt_a : ¬ (sL.core.arena_len % 2 ^ 64 < ((sL.core.wstk[(p.toNat + BitVec.toNat 1#64) %
      2 ^ 64]'hp1_m_bd).toNat + BitVec.toNat 3#64 + (sL.core.arena[((sL.core.wstk[(p.toNat +
        BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat + BitVec.toNat 2#64) % 2 ^ 64]'
        hcr2_m_bd).toNat) % 2 ^ 64) := by
    rw [hsz_bv, hcr_w_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3_lt,
      Nat.mod_eq_of_lt hal64, Nat.mod_eq_of_lt hcr_end64, hsz_eq]
    have := hwf_c.2.2.1; have := hwf_c.2.2.2.1; omega
  have hbd_c : cref32.toNat + 3 + (sL.core.arena[cref32.toNat + 2]'hcr2_bd).toNat ≤
      sL.core.arena.length := by
    rw [hsz_eq]; have := hwf_c.2.2.1; have := hwf_c.2.2.2.1
    have := hlkL.arena_len_le; rw [hlkL.arena_len_arr]; omega
  exact ⟨hp1_bd, hp1_m_bd, hcr_bd, hcr2_bd, hcr_m_bd, hcr2_m_bd, hcr_wstk, hcr_w_bv, hp2_eq,
    hp2_bv, hcr_ze, ha0_mem, hnot_lt_a3, har_hdr_bv, hsz_bv, hsz_eq, hnot_lt3, hnot_gt_a,
    hbd_c⟩

theorem dp_occ_lit_setup {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sL : FullState} (hinvL : FullDenseInvW c F0 F_cur sL)
    {cref32 j : BitVec 32} (hcr_ref : cref32.toNat ∈ fullArenaClauseRefsCore sL.core)
    (hng : fullArenaClauseGarbCore sL.core cref32.toNat = false)
    {szc32 : BitVec 32} (hsz_c : szc32.toNat = fullArenaClauseSizeCore sL.core cref32.toNat)
    (hbd_c : cref32.toNat + 3 + szc32.toNat ≤ sL.core.arena.length)
    (hj_lt : j.toNat < szc32.toNat)
    {p_wstk_bv p_wstk_mod : BitVec 32} (hw_bv : p_wstk_bv = cref32) (hw_mod : p_wstk_mod = cref32) :
    let lit_j := sL.core.arena[cref32.toNat + 3 + j.toNat]'(by omega)
    ∃ (ha_lit_bd : (BitVec.setWidth 64 p_wstk_bv + 3#64 + BitVec.setWidth 64 j).toNat <
        sL.core.arena.length)
      (hcr_lit_m_bd : (p_wstk_mod.toNat + BitVec.toNat 3#64 + j.toNat) % 2 ^ 64 <
        sL.core.arena.length)
      (hlj_bd : lit_j.toNat < sL.core.vals.length)
      (hlj_m_bd : (sL.core.arena[(p_wstk_mod.toNat + BitVec.toNat 3#64 + j.toNat) % 2 ^ 64]'
        hcr_lit_m_bd).toNat < sL.core.vals.length),
      (j + 1#32).toNat = j.toNat + 1 ∧
      sL.core.arena[(BitVec.setWidth 64 p_wstk_bv + 3#64 + BitVec.setWidth 64 j).toNat]'
        ha_lit_bd = lit_j ∧
      sL.core.arena[(p_wstk_mod.toNat + BitVec.toNat 3#64 + j.toNat) % 2 ^ 64]'
        hcr_lit_m_bd = lit_j ∧
      lit_j.toNat < 2 * sL.core.cur_vars ∧
      sL.core.vals[(sL.core.arena[(p_wstk_mod.toNat + BitVec.toNat 3#64 + j.toNat) % 2 ^ 64]'
        hcr_lit_m_bd).toNat]'hlj_m_bd = sL.core.vals[lit_j.toNat]'hlj_bd := by
  subst p_wstk_bv; subst p_wstk_mod
  intro lit_j
  have hlkL := hinvL.1.core_ok
  have hwL := hinvL.2.1
  have har_bd_lt : c.arena_cap < 2 ^ 30 := by
    have := c.harena; unfold dimacsBound at this; omega
  have hbd_len : cref32.toNat + 3 + szc32.toNat ≤ c.arena_cap := by
    rw [← hlkL.arena_len_arr]; exact hbd_c
  have hcr3_64 : cref32.toNat + 3 < 2 ^ 64 := by omega
  have hcr_j_64 : cref32.toNat + 3 + j.toNat < 2 ^ 64 := by omega
  have hj1_lt32 : j.toNat + 1 < 2 ^ 32 := by omega
  have h1_32 : 1 < 2 ^ 32 := by decide
  have h3_64 : 3 < 2 ^ 64 := by decide
  have hj1_eq : (j + 1#32).toNat = j.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_32, Nat.mod_eq_of_lt hj1_lt32]
  have hcr_ze := dense_zext32_toNat cref32
  have hj_ze := dense_zext32_toNat j
  have hlit_bv_eq : (BitVec.setWidth 64 cref32 + 3#64 + BitVec.setWidth 64 j).toNat =
      cref32.toNat + 3 + j.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hcr_ze, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h3_64, Nat.mod_eq_of_lt hcr3_64, hj_ze, Nat.mod_eq_of_lt hcr_j_64]
  have hlit_m_eq : (cref32.toNat + BitVec.toNat 3#64 + j.toNat) % 2 ^ 64 =
      cref32.toNat + 3 + j.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3_64, Nat.mod_eq_of_lt hcr_j_64]
  have ha_lit_bd : (BitVec.setWidth 64 cref32 + 3#64 + BitVec.setWidth 64 j).toNat <
      sL.core.arena.length := by
    rw [hlit_bv_eq]; omega
  have hcr_lit_m_bd : (cref32.toNat + BitVec.toNat 3#64 + j.toNat) % 2 ^ 64 <
      sL.core.arena.length := by
    rw [hlit_m_eq]; omega
  have hlj_bd0 : cref32.toNat + 3 + j.toNat < sL.core.arena.length := by omega
  have hlj_bv : sL.core.arena[(BitVec.setWidth 64 cref32 + 3#64 + BitVec.setWidth 64 j).toNat]'
      ha_lit_bd = lit_j :=
    dp_get_congr ha_lit_bd hlj_bd0 hlit_bv_eq
  have hlj_mod : sL.core.arena[(cref32.toNat + BitVec.toNat 3#64 + j.toNat) % 2 ^ 64]'
      hcr_lit_m_bd = lit_j :=
    dp_get_congr hcr_lit_m_bd hlj_bd0 hlit_m_eq
  have hlj_lt : lit_j.toNat < 2 * sL.core.cur_vars :=
    dp_arena_lit_lt hwL.arena hcr_ref hng (hsz_c ▸ hbd_c) (by rw [← hsz_c]; exact hj_lt)
  have hlj_bd : lit_j.toNat < sL.core.vals.length := by
    have := hlkL.vals_len; have := hlkL.cur_vars_le; omega
  have hlj_m_bd : (sL.core.arena[(cref32.toNat + BitVec.toNat 3#64 + j.toNat) % 2 ^ 64]'
      hcr_lit_m_bd).toNat < sL.core.vals.length := by
    rw [hlj_mod]; exact hlj_bd
  have hval_mod := dp_get_congr hlj_m_bd hlj_bd (by rw [hlj_mod])
  exact ⟨ha_lit_bd, hcr_lit_m_bd, hlj_bd, hlj_m_bd, hj1_eq, hlj_bv, hlj_mod, hlj_lt, hval_mod⟩

/-! ## 2. `full_m6_dense_prop_lit_wp` (`Spec.fullDensePropLitSpec`) -/

theorem full_m6_dense_prop_lit_wp (Γ : Env)
    (hAssign : Γ.Has "full_assign_lvl" fullAssignLvlSpec)
    (a : Tup Val [i64, i32]) (m : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hPre : Spec.fullDensePropLitSpec a m Q X) :
    Func.wp Γ full_m6_dense_prop_lit_body a m Q X := by
  rcases a with ⟨h, lit, ⟨⟩⟩
  rcases hPre with ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  have hlk := hinv.1.core_ok
  have hw := hinv.2.1
  have hcl0 := hinv.2.2.2.2.2.1
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 64 := by
    have := c.hmaxv; unfold dimacsBound at this; have := hlk.cur_vars_le; omega
  have hcv_shl : (BitVec.ofNat 64 s.core.cur_vars <<< 1#64).toNat = 2 * s.core.cur_vars :=
    dp_bv64_shl1_nat _ hcv_lt
  let not_lit : BitVec 32 := lit ^^^ 1#32
  have hnot_ze : (BitVec.setWidth 64 not_lit).toNat = not_lit.toNat := dense_zext32_toNat not_lit
  c0_hstraight
  c0_hsplit
  · c0_hsteps_nogrp
    exact dp_close_lit_q_true hinv (dp_pres_refl s) rfl (le_refl _) rfl hm hQ
  · have hnot_lt : not_lit.toNat < 2 * s.core.cur_vars := by
      have hhc : ¬ 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ lit.toNat ^^^ 1 := by assumption
      have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt hcv_lt,
        ← dense_bv32_xor1_toNat] at hhc
      exact Nat.lt_of_not_le hhc
    have hnot_bd : not_lit.toNat < s.core.vals.length := by
      have := hlk.vals_len; have := hlk.cur_vars_le; omega
    c0_hstraight
    c0_hsplit
    · c0_hsteps_nogrp
      exact dp_close_lit_q_true hinv (dp_pres_refl s) rfl (le_refl _) rfl hm hQ
    · have hnot_ff : s.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
        have hsf : (0#32).sle (BitVec.signExtend 32 (s.core.vals[not_lit.toNat]'hnot_bd)) =
            false := by
          have hhc : (0#32).sle
              (BitVec.signExtend 32 (s.core.vals[lit.toNat ^^^ 1])) = false := by assumption
          simpa only [← dense_bv32_xor1_toNat] using hhc
        exact dp_val_ff_of_sle_false hw hnot_lt hnot_bd hsf
      have hlit_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) := by
        have h0 := dense_vals_false_entails hw hcl0 hnot_lt hnot_ff
        have hxor : (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat := by rw [Nat.xor_assoc]; simp
        simpa [not_lit, dense_bv32_xor1_toNat, hxor] using h0
      obtain ⟨hshl_eq, h2nl_shl, hshl1_eq, h2nl_shl1, hm0_bd, hm1_bd⟩ :=
        dp_lit_wvec_bounds hinv lit hnot_lt
      c0_hstraight
      let off := s.core.wvec[(BitVec.setWidth 64 not_lit <<< 1#64).toNat]'h2nl_shl
      let sz := s.core.wvec[(BitVec.setWidth 64 not_lit <<< 1#64 + 1#64).toNat]'h2nl_shl1
      let end_off : BitVec 64 := BitVec.setWidth 64 off + BitVec.setWidth 64 sz
      obtain ⟨hoff_eq, hsz_w_eq, hend_nat, hend_le, _, hend_bv⟩ :=
        dp_lit_end_eq hinv lit hnot_lt (hm0 := hm0_bd) (hm1 := hm1_bd)
      have hdw0 := dp_dense_watches hinv
      have hwcap_lt : c.wcap < 2 ^ 31 := by have := c.hwcap; unfold dimacsBound at this; omega
      refine wp_join_group (ts := [i64])
        (fun _ mF => ∃ sF, FullDenseInvW c F0 F_cur sF ∧ DensePropPres s sF ∧
          s.core.trail_end ≤ sF.core.trail_end ∧ sF.core.propagated = s.core.propagated ∧
          sF.core.inconsistent = s.core.inconsistent ∧ (FullMem c sF ⋆ R) mF)
        (fun _ _ mF ⟨sF, hinvF, hpresF, hteF, hpropF, hincF, hmF⟩ => by
          c0_hsteps_nogrp
          exact dp_close_lit_q_true hinvF hpresF hpropF hteF hincF hmF hQ)
        ?_
      intro L40 hL40
      refine wp_loop_inv (ts := [i64])
        (fun (p, _) mL => ∃ sL, FullDenseInvW c F0 F_cur sL ∧ DensePropPres s sL ∧
          s.core.trail_end ≤ sL.core.trail_end ∧ sL.core.propagated = s.core.propagated ∧
          sL.core.inconsistent = s.core.inconsistent ∧ p.toNat ≤ end_off.toNat ∧
          DenseWatchSliceOk F_cur sL.core not_lit.toNat p.toNat (end_off.toNat - p.toNat) ∧
          (FullMem c sL ⋆ R) mL)
        (fun (p, _) _ => end_off.toNat - p.toNat)
        (fun L41 hL41 => by
          c0_hsteps_nogrp
          have hslice0 : DenseWatchSliceOk F_cur s.core not_lit.toNat
              (BitVec.setWidth 64 off).toNat
              (end_off.toNat - (BitVec.setWidth 64 off).toNat) := by
            rw [dense_zext32_toNat, hend_nat, Nat.add_sub_cancel_left, hoff_eq, hsz_w_eq]
            exact hdw0.slices not_lit.toNat hnot_lt
          exact hL41 (BitVec.setWidth 64 off, ()) m ⟨s, hinv, dp_pres_refl s, le_refl _, rfl, rfl,
            (by dsimp only [not_lit, end_off, off, sz]; rw [dense_zext32_toNat, hend_nat]
                exact Nat.le_add_right _ _),
            hslice0, hm⟩)
        (fun L41 ⟨p, ⟨⟩⟩ mL ⟨sL, hinvL, hpresL, hteL, hpropL, hincL, hp_le, hsliceL, hmL⟩ hLp => by
          have hlkL := hinvL.1.core_ok
          have hwL := hinvL.2.1
          have hcl0L := hinvL.2.2.2.2.2.1
          c0_hsplit
          · have hhc : p.toNat < ((s.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'hm0_bd).toNat +
                (s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat 1#64) % 2 ^ 64]'hm1_bd).toNat) %
                2 ^ 64 := by assumption
            have hp_lt : p.toNat < end_off.toNat := hend_bv ▸ hhc
            have hrem_pos : 0 < end_off.toNat - p.toNat := by omega
            have hp_bd : p.toNat < sL.core.wstk.length := by rw [hlkL.wstk_len_arr]; omega
            c0_hstraight
            let w0 := sL.core.wstk[p.toNat]'hp_bd
            have hp1_lt64 : p.toNat + 1 < 2 ^ 64 := by omega
            have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by
              have h1_lt : 1 < 2 ^ 64 := by decide
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt,
                Nat.mod_eq_of_lt hp1_lt64]
            c0_hsplit
            · have hbin_step := denseSlice_step_bin hsliceL hrem_pos
                (List.getElem?_eq_getElem hp_bd) (by assumption)
              let other := w0 &&& 0x7FFFFFFF#32
              have hoth_lt : other.toNat < 2 * sL.core.cur_vars := hbin_step.2.1
              obtain ⟨hnot_oth_le, hoth_bd, hoth_bv_bd, hslice_n', hent_oth⟩ :=
                dp_bin_step_setup hinvL hpresL hp_bd hp1_eq rfl hbin_step.2.2.2 hbin_step.2.2.1
                  hoth_lt hlit_ent
              c0_hstraight
              c0_hsplit
              · exact False.elim (hnot_oth_le (by assumption))
              · c0_hstraight
                c0_hsplit
                · c0_hsteps_nogrp
                  exact hLp (p + 1#64, ()) mL (by dsimp only; rw [hp1_eq]; omega)
                    ⟨sL, hinvL, hpresL, hteL, hpropL, hincL, by rw [hp1_eq]; omega,
                     hslice_n', hmL⟩
                · c0_hstraight
                  c0_hsplit
                  · have h2 : (BitVec.signExtend 32 (sL.core.vals[other.toNat]'hoth_bd)).slt 0#32 =
                        true := by assumption
                    have hoth_ff := dp_val_ff_of_slt_true hwL hoth_lt hoth_bd h2
                    have hunsat : (cnfOfClauses F_cur).Unsat :=
                      dense_unsat_of_lit_neg hent_oth
                        (dense_vals_false_entails hwL hcl0L hoth_lt hoth_ff)
                    c0_hstraight
                    refine dp_close_lit_q_false
                      (dp_inv_confl1 hinvL hunsat 1#64 (BitVec.setWidth 64 not_lit)
                        (BitVec.setWidth 64 other))
                      hpresL hpropL hteL (hwL.ext_sound.2 hunsat) (by dsimp only; decide)
                      (by dsimp only [not_lit, other, w0]; assumption) hQ
                  · have h1 : (0#32).slt (BitVec.signExtend 32
                        (sL.core.vals[other.toNat]'hoth_bd)) = false := by assumption
                    have h2 : (BitVec.signExtend 32 (sL.core.vals[other.toNat]'hoth_bd)).slt 0#32 =
                        false := by assumption
                    have hoth_zero := dp_val_zero_of_slt_slt hwL hoth_lt hoth_bd h1 h2
                    have hte_lt := dp_trail_lt_of_unassigned hlkL hwL hoth_lt hoth_zero
                    c0_hstraight; dr_call hAssign
                    have hcond_f : ¬ (sL.core.cur_vars ≤ other.toNat / 2 ∨
                        c.max_vars ≤ sL.core.trail_end ∨
                        sL.core.vals[other.toNat]?.getD 0#8 ≠ 0#8) := by
                      simp [hoth_zero]; omega
                    refine ⟨c, sL, R, rfl, hinvL.1, hmL, ?_⟩
                    dsimp only [other, w0] at hcond_f
                    simp only [Arg.val, show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                      eq_false hcond_f, ↓reduceIte]
                    intro flags' unass' phases' mA hfl hph hmA
                    obtain ⟨hinvA, hpresA, hteA, hsliceA⟩ := dp_assign_step hinvL hpresL hteL
                      hoth_lt hoth_zero hent_oth hfl unass' hph hslice_n'
                    c0_hsteps_nogrp
                    exact hLp (p + 1#64, ()) mA (by dsimp only; rw [hp1_eq]; omega)
                      ⟨_, hinvA, hpresA, hteA, hpropL, hincL, by rw [hp1_eq]; omega,
                       hsliceA, hmA⟩
            · have hocc_step := denseSlice_step_occ hsliceL hrem_pos
                (List.getElem?_eq_getElem hp_bd) (by assumption)
              rcases hocc_step with ⟨cref32, h2rem, hw_cr, h3w, hcr_lt31, hcr_ref, hslice_n2⟩
              c0_hstraight
              c0_hsplit
              · c0_hsteps_nogrp
                exact hL40 _ mL ⟨sL, hinvL, hpresL, hteL, hpropL, hincL, hmL⟩
              · have hp2_le : p.toNat + 2 ≤ end_off.toNat := by
                  have h := h2rem
                  dsimp only [end_off, off, sz] at h ⊢
                  rw [hend_nat] at h ⊢
                  omega
                obtain ⟨hp1_bd, hp1_m_bd, hcr_bd, hcr2_bd, hcr_m_bd, hcr2_m_bd,
                    hcr_wstk, hcr_w_bv, hp2_eq, hp2_bv, hcr_ze, ha0_mem,
                    hnot_lt_a3, har_hdr_bv, hsz_bv, hsz_eq, hnot_lt3, hnot_gt_a, hbd_c⟩ :=
                  dp_occ_cref_setup hinvL hend_le hp2_le hp1_eq hcr_ref hw_cr
                c0_hstraight
                c0_hsplit
                · exact False.elim (hnot_lt_a3 (by assumption))
                · have hslice2 : DenseWatchSliceOk F_cur sL.core not_lit.toNat
                      (p + 2#64).toNat (end_off.toNat - (p + 2#64).toNat) := by
                    rw [hp2_eq]
                    simpa [show end_off.toNat - p.toNat - 2 =
                      end_off.toNat - (p.toNat + 2) by omega] using hslice_n2
                  c0_hstraight
                  c0_hsplit
                  · c0_hsteps_nogrp
                    rw [hp2_bv]
                    exact hLp (p + 2#64, ()) mL (by dsimp only; rw [hp2_eq]; omega)
                      ⟨sL, hinvL, hpresL, hteL, hpropL, hincL, by rw [hp2_eq]; omega, hslice2, hmL⟩
                  · have hng_hdr : sL.core.arena[cref32.toNat]'hcr_bd &&& 524288#32 = 0#32 := by
                      have hhc : sL.core.arena[(sL.core.wstk[(p.toNat + BitVec.toNat 1#64) %
                          2 ^ 64]'hp1_m_bd).toNat]'hcr_m_bd &&& 524288#32 = 0#32 := by assumption
                      rwa [har_hdr_bv] at hhc
                    have hng := dp_garb_false_of_hdr hcr_bd hng_hdr
                    c0_hstraight
                    c0_hsplit
                    · have hhc : (sL.core.arena[((sL.core.wstk[(p.toNat + BitVec.toNat 1#64) %
                          2 ^ 64]'hp1_m_bd).toNat + BitVec.toNat 2#64) %
                          2 ^ 64]'hcr2_m_bd).toNat < 3 := by assumption
                      rw [hsz_bv] at hhc
                      exact False.elim (hnot_lt3 hhc)
                    · c0_hstraight; c0_hsplit
                      · exact False.elim (hnot_gt_a (by assumption))
                      · let szc32 := sL.core.arena[cref32.toNat + 2]'hcr2_bd
                        have hsz_c : szc32.toNat =
                            fullArenaClauseSizeCore sL.core cref32.toNat := hsz_eq
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := [.bool, i32, i32, i32])
                          (fun (sat, unass, ul, _) m79 => m79 = mL ∧ (sat = true ∨
                            (sat = false ∧ unass = 0#32 ∧ DpOccScanInv sL.core cref32.toNat
                              szc32.toNat hsz_c hbd_c 0#32 ul szc32.toNat (le_refl _)) ∨
                            (sat = false ∧ unass = 1#32 ∧ DpOccScanInv sL.core cref32.toNat
                              szc32.toNat hsz_c hbd_c 1#32 ul szc32.toNat (le_refl _)) ∨
                            (sat = false ∧ unass ≠ 0#32 ∧ unass ≠ 1#32)))
                          (fun _ ⟨sat, unass, ul, _⟩ m79 ⟨hm79, h79⟩ => by
                            subst m79
                            c0_hsplit
                            · c0_hsteps_nogrp
                              obtain ⟨hinvG, hpresG, hsliceG⟩ := dp_occ_mark_garb_bv hinvL hpresL
                                (by rw [hcr_wstk, hcr_ze]) hcr_ref ha0_mem hslice2 _
                              rw [hp2_bv]
                              exact hLp (p + 2#64, ()) _ (by dsimp only; rw [hp2_eq]; omega)
                                ⟨_, hinvG, hpresG, hteL, hpropL, hincL, by rw [hp2_eq]; omega,
                                 hsliceG, by assumption⟩
                            · c0_hsplit
                              · have hc0 : unass = 0#32 := by assumption
                                subst hc0
                                have h0 : DpOccScanInv sL.core cref32.toNat szc32.toNat hsz_c
                                      hbd_c 0#32 ul szc32.toNat (le_refl _) := by
                                  have hsf : sat = false := by
                                    first
                                    | exact (by assumption)
                                    | exact Bool.eq_false_iff.mpr (by assumption)
                                  rcases h79 with h | ⟨-, -, hs⟩ | ⟨-, h1, -⟩ | ⟨-, hn0, -⟩
                                  · rw [hsf] at h; cases h
                                  · exact hs
                                  · cases h1
                                  · exact absurd rfl hn0
                                rcases h0 with ⟨-, hall⟩ | ⟨h1, -⟩
                                · have hunsat := dp_occ_all_false_unsat hwL hcl0L hcr_ref hng
                                    hsz_c hbd_c hall
                                  c0_hsteps_nogrp
                                  exact dp_close_lit_q_false
                                    (dp_inv_confl_ref hinvL hunsat 2#64
                                      (BitVec.setWidth 64 (sL.core.wstk[(p + 1#64).toNat]'hp1_bd)))
                                    hpresL hpropL hteL (hwL.ext_sound.2 hunsat)
                                    (by dsimp only; decide) (by assumption) hQ
                                · cases h1
                              · refine wp_join_group (ts := [])
                                  (fun _ m85 => ∃ s85, FullDenseInvW c F0 F_cur s85 ∧
                                    DensePropPres s s85 ∧ s.core.trail_end ≤ s85.core.trail_end ∧
                                    s85.core.propagated = s.core.propagated ∧
                                    s85.core.inconsistent = s.core.inconsistent ∧
                                    DenseWatchSliceOk F_cur s85.core not_lit.toNat
                                      (p + 2#64).toNat (end_off.toNat - (p + 2#64).toNat) ∧
                                    (FullMem c s85 ⋆ R) m85)
                                  (fun _ _ m85 ⟨s85, hinv85, hpres85, hte85, hprop85, hinc85,
                                      hslice85, hm85⟩ => by
                                    c0_hsteps_nogrp
                                    rw [hp2_bv]
                                    exact hLp (p + 2#64, ()) m85 (by dsimp only; rw [hp2_eq]; omega)
                                      ⟨s85, hinv85, hpres85, hte85, hprop85, hinc85,
                                       by rw [hp2_eq]; omega, hslice85, hm85⟩) ?_
                                intro L85 hL85
                                c0_hsplit
                                · have hc1 : unass = 1#32 := by assumption
                                  subst hc1
                                  have h1 : DpOccScanInv sL.core cref32.toNat szc32.toNat hsz_c
                                        hbd_c 1#32 ul szc32.toNat (le_refl _) := by
                                    have hsf : sat = false := by
                                      first
                                      | exact (by assumption)
                                      | exact Bool.eq_false_iff.mpr (by assumption)
                                    rcases h79 with h | ⟨-, h0, -⟩ | ⟨-, -, hs⟩ | ⟨-, -, hn1⟩
                                    · rw [hsf] at h; cases h
                                    · cases h0
                                    · exact hs
                                    · exact absurd rfl hn1
                                  rcases h1 with ⟨h01, -⟩ | ⟨-, q0, hq0, heq0, hv0, hall⟩
                                  · cases h01
                                  · obtain ⟨hlt_u, hent_u⟩ := dp_occ_unit_entails hwL hcl0L hcr_ref
                                      hng hsz_c hbd_c hq0 heq0 hv0 hall
                                    have hul_bd : ul.toNat < sL.core.vals.length := by
                                      have := hlkL.vals_len; have := hlkL.cur_vars_le; omega
                                    c0_hstraight; c0_hsplit
                                    · have hte_lt := dp_trail_lt_of_unassigned hlkL hwL hlt_u hv0
                                      c0_hstraight; dr_call hAssign
                                      have hcond_f : ¬ (sL.core.cur_vars ≤ ul.toNat / 2 ∨
                                          c.max_vars ≤ sL.core.trail_end ∨
                                          sL.core.vals[ul.toNat]?.getD 0#8 ≠ 0#8) := by
                                        simp [hv0]; omega
                                      refine ⟨c, sL, R, rfl, hinvL.1, hmL, ?_⟩
                                      simp only [Arg.val, eq_false hcond_f, ↓reduceIte]
                                      intro flags' unass' phases' mA hfl hph hmA
                                      obtain ⟨hinvA, hpresA, hteA, hsliceA⟩ := dp_assign_step hinvL
                                        hpresL hteL hlt_u hv0 hent_u hfl unass' hph hslice2
                                      c0_hsteps_nogrp
                                      exact hL85 () mA
                                        ⟨_, hinvA, hpresA, hteA, hpropL, hincL, hsliceA, hmA⟩
                                    · exfalso
                                      have hnz : (sL.core.vals[ul.toNat]'hul_bd).signExtend 32 ≠
                                          0#32 := by assumption
                                      apply hnz
                                      rw [List.getElem?_eq_getElem hul_bd, Option.getD_some] at hv0
                                      rw [hv0]; decide
                                · c0_hsteps_nogrp
                                  exact hL85 () mL ⟨sL, hinvL, hpresL, hteL, hpropL, hincL,
                                    hslice2, hmL⟩) ?_
                        intro L79 hL79
                        refine wp_loop_inv (ts := [i32, i32, i32])
                          (fun (unass, ul, j, _) m80 => m80 = mL ∧
                            ∃ hj : j.toNat ≤ szc32.toNat,
                              DpOccScanInv sL.core cref32.toNat szc32.toNat hsz_c hbd_c
                                unass ul j.toNat hj)
                          (fun (_, _, j, _) _ => szc32.toNat - j.toNat)
                          (fun L80 hL80 => by
                            c0_hsteps_nogrp
                            exact hL80 (0#32, 0xFFFFFFFF#32, 0#32, ()) mL
                              ⟨rfl, by simp, Or.inl ⟨rfl, fun _ hq => by simp at hq⟩⟩)
                          (fun L80 ⟨unass, ul, j, ⟨⟩⟩ m80 ⟨hm80, hj_le, hscan⟩ hLp80 => by
                            subst m80
                            c0_hsplit
                            · have hj_lt : j.toNat < szc32.toNat := by
                                have hhc : j.toNat < (sL.core.arena[((sL.core.wstk[(p.toNat +
                                    BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
                                    BitVec.toNat 2#64) % 2 ^ 64]'hcr2_m_bd).toNat := by assumption
                                rwa [hsz_bv] at hhc
                              obtain ⟨ha_lit_bd, hcr_lit_m_bd, hlj_bd, hlj_m_bd, hj1_eq, hlj_bv,
                                  hlj_mod, hlj_lt, hval_lit_mod⟩ :=
                                dp_occ_lit_setup hinvL hcr_ref hng hsz_c hbd_c hj_lt
                                  hcr_wstk hcr_w_bv
                              c0_hstraight
                              let lit_j := sL.core.arena[cref32.toNat + 3 + j.toNat]'(by omega)
                              have hlj_bv1 : sL.core.arena[(BitVec.setWidth 64
                                  (sL.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_bd) +
                                  (3 : BitVec 64) + BitVec.setWidth 64 j).toNat]'ha_lit_bd =
                                  lit_j := hlj_bv
                              refine wp_join_group (ts := [.bool, i32, i32])
                                (fun (_, u', ul', _) m92 => m92 = mL ∧
                                  DpOccScanInv sL.core cref32.toNat szc32.toNat hsz_c hbd_c
                                    u' ul' (j.toNat + 1) (Nat.succ_le_of_lt hj_lt))
                                (fun _ ⟨_, u', ul', ⟨⟩⟩ m92 ⟨hm92, hinv92⟩ => by
                                  c0_hsteps_nogrp
                                  exact hLp80 (u', ul', j + 1#32, ()) m92
                                    (by dsimp only; rw [hj1_eq]; omega)
                                    ⟨hm92, by rw [hj1_eq]; omega,
                                     dp_occ_scan_cast hj1_eq.symm hinv92⟩) ?_
                              intro L92 hL92
                              c0_hsplit
                              · have hlj_bv_bd : (BitVec.setWidth 64 (sL.core.arena[(BitVec.setWidth
                                    64 (sL.core.wstk[(p + 1#64).toNat]'hp1_bd) + 3#64 +
                                    BitVec.setWidth 64 j).toNat]'ha_lit_bd)).toNat <
                                    sL.core.vals.length := by
                                  rw [hlj_bv, dense_zext32_toNat]; exact hlj_bd
                                c0_hstraight; c0_hsplit
                                · exact hL79 (true, unass, ul, j, ()) mL ⟨rfl, Or.inl rfl⟩
                                · have hsgt_f : (0#32).slt (BitVec.signExtend 32
                                      (sL.core.vals[lit_j.toNat]'hlj_bd)) = false := by
                                    have hhc : (0#32).slt (BitVec.signExtend 32
                                        (sL.core.vals[(sL.core.arena[((sL.core.wstk[(p.toNat +
                                          BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
                                          BitVec.toNat 3#64 + j.toNat) % 2 ^ 64]'
                                          hcr_lit_m_bd).toNat]'hlj_m_bd)) = false := by assumption
                                    rwa [hval_lit_mod] at hhc
                                  have hstep := dp_occ_scan_step hj_lt rfl hscan
                                  refine wp_join_group (ts := [i32, i32])
                                    (fun (u', ul', _) m102 => m102 = mL ∧
                                      DpOccScanInv sL.core cref32.toNat szc32.toNat hsz_c hbd_c
                                        u' ul' (j.toNat + 1) (Nat.succ_le_of_lt hj_lt))
                                    (fun _ ⟨u', ul', ⟨⟩⟩ m102 ⟨hm102, hinv102⟩ => by
                                      c0_hsteps_nogrp
                                      exact hL92 (false, u', ul', ()) m102 ⟨hm102, hinv102⟩) ?_
                                  intro L102 hL102
                                  c0_hstraight; c0_hsplit
                                  · have heq0 : BitVec.signExtend 32
                                        (sL.core.vals[lit_j.toNat]'hlj_bd) = 0#32 := by
                                      have hhc : BitVec.signExtend 32
                                          (sL.core.vals[(sL.core.arena[((sL.core.wstk[(p.toNat +
                                            BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
                                            BitVec.toNat 3#64 + j.toNat) % 2 ^ 64]'
                                            hcr_lit_m_bd).toNat]'hlj_m_bd) = 0#32 := by assumption
                                      rwa [hval_lit_mod] at hhc
                                    have hv0 := dp_val_zero_of_sext_eq hwL hlj_lt hlj_bd heq0
                                    c0_hstraight; c0_hsplit
                                    · have hne : unass ≠ 0#32 := fun hu0 => by
                                        subst hu0
                                        have h1 : BitVec.toNat (1 : BitVec 32) <
                                            (BitVec.toNat 0#32 + BitVec.toNat (1 : BitVec 32)) %
                                              2 ^ 32 := by assumption
                                        exact absurd h1 (by decide)
                                      have hu1 : unass = 1#32 := (hstep.1 hv0).2 hne
                                      c0_hsteps_nogrp
                                      rw [hlj_bv1]
                                      exact hL79 (false, unass + (1 : BitVec 32), lit_j, j, ())
                                        mL ⟨rfl, Or.inr (Or.inr (Or.inr
                                          ⟨rfl, by rw [hu1]; decide, by rw [hu1]; decide⟩))⟩
                                    · have hu0 : unass = 0#32 := by
                                        rcases hscan with ⟨h0, -⟩ | ⟨h1, -⟩
                                        · exact h0
                                        · subst h1
                                          exact absurd (by
                                            decide : BitVec.toNat (1 : BitVec 32) <
                                              (BitVec.toNat 1#32 + BitVec.toNat (1 : BitVec 32)) %
                                                2 ^ 32)
                                            (by assumption)
                                      c0_hsteps_nogrp
                                      rw [hlj_bv1]
                                      exact hL102 (unass + (1 : BitVec 32), lit_j, ()) mL
                                        ⟨rfl, by rw [hu0]; exact (hstep.1 hv0).1 hu0⟩
                                  · have hne0 : BitVec.signExtend 32
                                        (sL.core.vals[lit_j.toNat]'hlj_bd) ≠ 0#32 := by
                                      have hhc : BitVec.signExtend 32
                                          (sL.core.vals[(sL.core.arena[((sL.core.wstk[(p.toNat +
                                            BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
                                            BitVec.toNat 3#64 + j.toNat) % 2 ^ 64]'
                                            hcr_lit_m_bd).toNat]'hlj_m_bd) ≠ 0#32 := by assumption
                                      rwa [hval_lit_mod] at hhc
                                    have hvff := dp_val_ff_of_slt_ne hwL hlj_lt hlj_bd hsgt_f hne0
                                    exact hL102 (unass, ul, ()) mL ⟨rfl, hstep.2 hvff⟩
                              · exact False.elim (dp_occ_bad_lit_lt hinvL hpresL hlj_mod hlj_lt
                                  (by assumption))
                            · c0_hsteps_nogrp
                              have hjeq : j.toNat = szc32.toNat := by
                                have hhc : ¬ j.toNat < (sL.core.arena[((sL.core.wstk[(p.toNat +
                                    BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
                                    BitVec.toNat 2#64) % 2 ^ 64]'hcr2_m_bd).toNat := by
                                  assumption
                                rw [hsz_bv] at hhc; omega
                              rcases hscan with ⟨hu0, hall⟩ | ⟨hu1, q0, hq0, heq0, hv0, hall⟩
                              · exact hL79 (false, unass, ul, j, ()) mL
                                  ⟨rfl, Or.inr (Or.inl ⟨rfl, hu0,
                                    Or.inl ⟨rfl, fun q hq => hall q (hjeq ▸ hq)⟩⟩)⟩
                              · exact hL79 (false, unass, ul, j, ()) mL
                                  ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, hu1, Or.inr ⟨rfl, q0,
                                    hjeq ▸ hq0, heq0, hv0,
                                    fun q hq => hall q (hjeq ▸ hq)⟩⟩))⟩)
          · c0_hsteps_nogrp
            exact hL40 (p, ()) mL ⟨sL, hinvL, hpresL, hteL, hpropL, hincL, hmL⟩)

/-! ## 3. `full_m6_dense_prop_wp` (`Spec.fullDensePropSpec`) -/

private theorem dp_prop_meas {c : FullCfg} {sL : FullState} {R : Mem 64 → Prop} {mL : Mem 64}
    (hlk : FullCoreState.LengthsOk c sL.core) (hm : (FullMem c sL ⋆ R) mL) :
    c.max_vars - ((loadVal mL i64 (HdrWordField.propagated.addr c)).getD 0#64).toNat =
      c.max_vars - sL.core.propagated := by
  rw [fullHdr_load .propagated hm]
  have hp_le : sL.core.propagated ≤ c.max_vars :=
    le_trans hlk.propagated_le (le_trans hlk.trail_end_le hlk.cur_vars_le)
  have hlt : sL.core.propagated < 2 ^ 64 := by
    have := c.hmaxv; unfold dimacsBound at this; omega
  simp [HdrWordField.get, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

private def DpLoopPres (s s' : FullState) : Prop :=
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.arena_len = s.core.arena_len ∧
  s'.core.fuel = s.core.fuel ∧
  s'.core.repr = s.core.repr ∧
  fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.glue_used = s.scratch.glue_used

private theorem dp_loop_pres_refl (s : FullState) : DpLoopPres s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem dp_loop_pres_trans {s0 s1 s2 : FullState}
    (h1 : DpLoopPres s0 s1) (h2 : DpLoopPres s1 s2) : DpLoopPres s0 s2 := by
  rcases h1 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
  rcases h2 with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11⟩

theorem full_m6_dense_prop_wp (Γ : Env)
    (hPropLit : Γ.Has "full_m6_dense_prop_lit" Spec.fullDensePropLitSpec)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hPre : Spec.fullDensePropSpec a m Q X) :
    Func.wp Γ full_m6_dense_prop_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hPre with ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [])
    (fun _ mL => ∃ sL, FullDenseInvW c F0 F_cur sL ∧ DpLoopPres s sL ∧ (FullMem c sL ⋆ R) mL)
    (fun _ mL => c.max_vars - ((loadVal mL i64 (HdrWordField.propagated.addr c)).getD 0#64).toNat)
    (fun L3 hL3 => by
      c0_hsteps_nogrp
      exact hL3 () m ⟨s, hinv, dp_loop_pres_refl s, hm⟩)
    (fun L3 ⟨⟩ mL ⟨sL, hinvL, hpresL, hmL⟩ hLp => by
      have hlkL := hinvL.1.core_ok
      refine wp_join_group (ts := [])
        (fun _ mE => ∃ sE, FullDenseInvW c F0 F_cur sE ∧ DpLoopPres s sE ∧
          (FullMem c sE ⋆ R) mE)
        (fun _ _ mE ⟨sE, hinvE, hpresE, hmE⟩ => by
          c0_hsteps_nogrp
          rcases hpresE with ⟨p1, p2, p3, p4, p5, p6, p7, p9, p10, p11, p13⟩
          have hwE := hinvE.2.1
          by_cases hinc : sE.core.inconsistent = 0#64
          · have hbeq : (sE.core.inconsistent == 0) = true := beq_iff_eq.mpr hinc
            rw [hbeq]
            exact hQ true sE mE hinvE p1 p3 p4 p2 p5 p6 p7 p9 p10 p11 p13
              ⟨fun _ => hinc, fun _ => rfl⟩ (fun hf => by cases hf) hmE
          · have hbeq : (sE.core.inconsistent == 0) = false := beq_false_of_ne hinc
            rw [hbeq]
            have hunsat : F0.Unsat := hwE.ext_sound.2 (hwE.inconsistent_sound hinc)
            exact hQ false sE mE hinvE p1 p3 p4 p2 p5 p6 p7 p9 p10 p11 p13
              ⟨fun hf => False.elim (Bool.false_ne_true hf), fun h0 => absurd h0 hinc⟩
              (fun _ => ⟨hunsat, hinc⟩) hmE)
        ?_
      intro L4 hL4
      c0_hsteps_nogrp
      · have hmeas_L := dp_prop_meas hlkL hmL
        have hpr_lt : sL.core.propagated < sL.core.trail_end := by
          have hc' : sL.core.propagated % 2 ^ 64 < sL.core.trail_end % 2 ^ 64 := by assumption
          have h1 : sL.core.propagated < 2 ^ 64 := by
            have := c.hmaxv; unfold dimacsBound at this
            have := hlkL.propagated_le; have := hlkL.trail_end_le
            have := hlkL.cur_vars_le; omega
          have h2 : sL.core.trail_end < 2 ^ 64 := by
            have := c.hmaxv; unfold dimacsBound at this
            have := hlkL.trail_end_le; have := hlkL.cur_vars_le; omega
          rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hc'
        have hpr_bd : sL.core.propagated < sL.core.trl.length := by
          have := hlkL.trl_len; have := hlkL.trail_end_le; have := hlkL.cur_vars_le; omega
        have hpr_lt64 : sL.core.propagated < 2 ^ 64 := by
          have := c.hmaxv; unfold dimacsBound at this
          have := hlkL.trail_end_le; have := hlkL.cur_vars_le; omega
        have hpr_p1_lt : sL.core.propagated + 1 < 2 ^ 64 := by omega
        have h1_lt : 1 < 2 ^ 64 := by decide
        have hpr_bd' : (BitVec.ofNat 64 sL.core.propagated).toNat < sL.core.trl.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpr_lt64]; exact hpr_bd
        have hpr_inc : (BitVec.ofNat 64 sL.core.propagated + 1#64).toNat =
            sL.core.propagated + 1 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hpr_lt64, Nat.mod_eq_of_lt h1_lt, Nat.mod_eq_of_lt hpr_p1_lt]
        c0_hsteps_nogrp
        let s0 := { sL with core := { sL.core with propagated := sL.core.propagated + 1 } }
        have hinv0 := fullDenseInvW_with_prop hinvL (Nat.succ_le_of_lt hpr_lt)
        have hpres0 : DpLoopPres s s0 := dp_loop_pres_trans hpresL (dp_loop_pres_refl sL)
        dr_call hPropLit
        refine ⟨c, F0, F_cur, s0, R, rfl, hinv0,
          (by dsimp only [s0]; rw [← hpr_inc]; assumption),
          fun ok s1 m1 hinv1 hcv1 hfl1 hprop1 _ hrepr1 hal1 href1 htm1 htr1 hsb1 hs11 hs21 hg1
            hf1 ht1 hm1 => ?_⟩
        have hpres1 : DpLoopPres s s1 := dp_loop_pres_trans hpres0
          ⟨hcv1, hal1, hfl1, hrepr1, href1, htm1, htr1, hsb1, hs11, hs21, hg1⟩
        c0_hsplit
        · have hmeas : c.max_vars -
              ((loadVal m1 i64 (HdrWordField.propagated.addr c)).getD 0#64).toNat <
              c.max_vars -
              ((loadVal mL i64 (HdrWordField.propagated.addr c)).getD 0#64).toNat := by
            rw [dp_prop_meas hinv1.1.core_ok hm1, hmeas_L, hprop1]
            have hlk1 := hinv1.1.core_ok
            have := hlk1.propagated_le; have := hlk1.trail_end_le; have := hlk1.cur_vars_le
            dsimp only [s0] at *
            omega
          c0_hsteps_nogrp
          exact hLp () m1 hmeas ⟨s1, hinv1, hpres1, hm1⟩
        · have hok_f : ok = false := by
            first | exact (by assumption) | exact Bool.eq_false_iff.mpr (by assumption)
          c0_hsteps_nogrp
          rcases hpres1 with ⟨p1, p2, p3, p4, p5, p6, p7, p9, p10, p11, p13⟩
          exact hQ false s1 m1 hinv1 p1 p3 p4 p2 p5 p6 p7 p9 p10 p11 p13
            ⟨fun h => False.elim (Bool.false_ne_true h), fun h0 => absurd h0 (hf1 hok_f).2⟩
            (fun _ => hf1 hok_f) hm1
      · exact hL4 () mL ⟨sL, hinvL, hpresL, hmL⟩
      · exact hL4 () mL ⟨sL, hinvL, hpresL, hmL⟩)

end LeanQbe.T.Examples.Kissat.Proof.Dense
