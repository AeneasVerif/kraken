/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Src.Heap
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb

/-!
# Soundness Proofs for `Kissat.Src.Heap` (`Proof.Heap.Wp`)

Proves parametric `(Γ : Env)` `Func.wp` theorems for all `4` functions in `Src.Heap.fns`:
1. `full_heap_up_wp` against `fullHeapUpSpec`.
2. `full_heap_down_wp` against `fullHeapDownSpec`.
3. `full_heap_push_wp` against `fullHeapPushSpec`.
4. `full_heap_pop_wp` against `fullHeapPopSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Heap

open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Heap
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem heap_hlen_upd_hp_ps {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hp' ps' : List (BitVec 32)) (hl' : Nat)
    (hhp : hp'.length = c.max_vars) (hps : ps'.length = c.max_vars) :
    ({ s with scratch :=
      { s.scratch with heap := hp', pos := ps', heap_len := hl' } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with heap_len_arr := hhp, pos_len := hps }⟩

private theorem heap_h2i1_64 (k : Nat) (hk : k < 2 ^ 29) :
    (2 * k + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * k + 1 :=
  Nat.mod_eq_of_lt (by simp; omega)

private theorem heap_probePres_upd_hp_ps {s0 s1 : FullState}
    (h : FullProbeScratchPres s0 s1) (hp' ps' : List (BitVec 32)) (hl' : Nat) :
    FullProbeScratchPres s0
      { s1 with scratch := { s1.scratch with heap := hp', pos := ps', heap_len := hl' } } := h

private theorem heap_finish {Q : Post []} {c : FullCfg} {s s' : FullState}
    {R : Mem 64 → Prop} {m' : Mem 64} {P : FullState → Prop}
    (hQ : ∀ (_ : Tup Val []) (s1 : FullState) (m1 : Mem 64),
      PreservesCoreSlice (fullSafetySlice c).coreProj s s1 →
      (fullSafetySlice c).safe s1 → P s1 →
      ((fullSafetySlice c).mem s1 ⋆ R) m1 → Q () m1)
    (hm : ((fullSafetySlice c).mem s' ⋆ R) m')
    (hc : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hl : (fullSafetySlice c).safe s') (hp : P s') : Q () m' :=
  hQ () s' m' hc hl hp hm

private theorem heap_call_up_spec {Q : Post []} {X : XPost} {c : FullCfg} {s0 : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {v : BitVec 32}
    (hm : (FullMem c s0 ⋆ R) m0)
    (hlen : s0.LengthsOk c)
    (hcont : ∀ (r : Tup Val []) (s' : FullState) (m' : Mem 64),
      PreservesCoreSlice (fullSafetySlice c).coreProj s0 s' →
      (fullSafetySlice c).safe s' →
      (FullProbeScratchPres s0 s' ∧
        ∃ hp' ps', s'.scratch = { s0.scratch with heap := hp', pos := ps' }) →
      ((fullSafetySlice c).mem s' ⋆ R) m' → Q r m') :
    fullHeapUpSpec (c.hdr, v, ()) m0 Q X :=
  ⟨c, s0, R, rfl, hlen, hm, hcont⟩

private theorem heap_call_down_spec {Q : Post []} {X : XPost} {c : FullCfg} {s0 : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {v : BitVec 32}
    (hm : (FullMem c s0 ⋆ R) m0)
    (hlen : s0.LengthsOk c)
    (hcont : ∀ (r : Tup Val []) (s' : FullState) (m' : Mem 64),
      PreservesCoreSlice (fullSafetySlice c).coreProj s0 s' →
      (fullSafetySlice c).safe s' →
      (s'.scratch.heap_len = s0.scratch.heap_len ∧ FullProbeScratchPres s0 s') →
      ((fullSafetySlice c).mem s' ⋆ R) m' → Q r m') :
    fullHeapDownSpec (c.hdr, v, ()) m0 Q X :=
  ⟨c, s0, R, rfl, hlen, hm, hcont⟩

private theorem heap_pop_j1 {c : FullCfg} {s s_nl s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    {J1 : Cont []}
    (hJ1 : ∀ (s' : FullState) (xs : Tup Val []) (ml : Mem 64),
      ((fullSafetySlice c).mem s' ⋆ R) ml →
      PreservesCoreSlice (fullSafetySlice c).coreProj s_nl s' →
      (fullSafetySlice c).safe s' →
      (s'.scratch.heap_len = s_nl.scratch.heap_len ∧ FullProbeScratchPres s s') →
      J1 xs ml)
    (hm : (FullMem c s1 ⋆ R) m1)
    (hc : PreservesCoreSlice FullState.core s_nl s1)
    (hl : s1.LengthsOk c)
    (hh : s1.scratch.heap_len = s_nl.scratch.heap_len)
    (hp : FullProbeScratchPres s s1) : J1 () m1 :=
  hJ1 s1 () m1 hm hc hl ⟨hh, hp⟩

/-- Soundness proof for `full_heap_up` against canonical `fullHeapUpSpec`. -/
theorem full_heap_up_wp (Γ : Env) :
    ∀ a m Q X, fullHeapUpSpec a m Q X → Func.wp Γ full_heap_up_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len; obtain hsl := hsok.score_len
  unfold Func.wp full_heap_up_body
  c0_hsteps
  · exact hQ () s m rfl hlen ⟨fullProbeScratchPres_refl s, s.scratch.heap, s.scratch.pos, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨fullProbeScratchPres_refl s, s.scratch.heap, s.scratch.pos, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨fullProbeScratchPres_refl s, s.scratch.heap, s.scratch.pos, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨fullProbeScratchPres_refl s, s.scratch.heap, s.scratch.pos, rfl⟩ hm
  · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
    have hhlen_le : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ s.core.cur_vars := by c0_bound
    refine wp_loop_safety_slice_pure (ts := [i32]) (fullSafetySlice c) s R
      (fun s1 (i, ()) =>
        i.toNat < (BitVec.ofNat 64 s.scratch.heap_len).toNat ∧ s1.LengthsOk c ∧
        FullProbeScratchPres s s1 ∧ s1.scratch.heap_len = s.scratch.heap_len ∧
        ∃ hp' ps', s1.scratch = { s.scratch with heap := hp', pos := ps' })
      (fun (i, ()) => i.toNat)
      (fun J hLoop => ?_)
      (fun J s1 (i, ()) m1 hcore1 hlen1 ⟨hi1, hs1, hpr1, hhl1_eq, hp1, ps1, hsc1⟩ hm1
        hLoop1 => ?_)
    · c0_hsteps
      refine hLoop s (_, ()) m hm rfl hlen ⟨?_, hlen, fullProbeScratchPres_refl s, rfl,
        s.scratch.heap, s.scratch.pos, rfl⟩
      c0_bound
    · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hm1 hlen1
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hs1.scratch_ok
      obtain hhl1 := hsok1.heap_len_arr; obtain hpl1 := hsok1.pos_len
      obtain hsl1 := hsok1.score_len
      have hi_lt_mx : i.toNat < c.max_vars := by omega
      c0_hsteps_nogrp
      · refine heap_finish hQ (by assumption) ?_ ?_ ?_
        · exact hcore1
        · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
            (by rw [List.length_set, hpl1])
        · exact ⟨heap_probePres_upd_hp_ps hpr1 _ _ _, _, _, by rw [hsc1]⟩
      · have hi_pos : 0 < i.toNat := by c0_bound
        have hshr1 : (i - 1) >>> (1 : BitVec 32) = (i - 1) >>> 1 := rfl
        have hip_eq : ((i - 1) >>> (1 : BitVec 32)).toNat = (i.toNat - 1) / 2 := by
          rw [hshr1, bv32_lshr_1]
          have := i.isLt
          bv_omega
        have hip_lt : ((i - 1) >>> (1 : BitVec 32)).toNat < i.toNat := by rw [hip_eq]; omega
        have hpp64 : (BitVec.setWidth 64 ((i - 1) >>> (1 : BitVec 32))).toNat =
            (i.toNat - 1) / 2 := by
          rw [BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by have := ((i - 1) >>> (1 : BitVec 32)).isLt; omega), hip_eq]
        have hcv1 : s1.core.cur_vars = s.core.cur_vars := congrArg FullCoreState.cur_vars hceq1
        have hp_v_lt_raw : (s1.scratch.heap[(i - 1).toNat / 2]'(by
            rw [hhl1]; bv_omega)).toNat < s.core.cur_vars := by
          rw [← hcv1]; c0_bound
        have hp_v_eq :
            (s1.scratch.heap[(BitVec.setWidth 64 ((i - 1) >>> (1 : BitVec 32))).toNat]'(by
              rw [hhl1, hpp64]; omega)) =
            s1.scratch.heap[(i - 1).toNat / 2]'(by rw [hhl1]; bv_omega) := by
          congr 1; try (rw [hpp64]; try bv_omega)
        have hp_v_lt :
            (s1.scratch.heap[(BitVec.setWidth 64 ((i - 1) >>> (1 : BitVec 32))).toNat]'(by
              rw [hhl1, hpp64]; omega)).toNat < s.core.cur_vars := by
          rw [hp_v_eq]; exact hp_v_lt_raw
        have hsc_lt1 :
            (s1.scratch.heap[(BitVec.setWidth 64 ((i - 1) >>> (1 : BitVec 32))).toNat]'(by
              rw [hhl1, hpp64]; omega)).toNat < s1.scratch.score.length := by
          rw [hsl1]; omega
        have hsc_lt2 : v.toNat < s1.scratch.score.length := by rw [hsl1]; omega
        have hpv_pos_lt :
            (s1.scratch.heap[(BitVec.setWidth 64 ((i - 1) >>> (1 : BitVec 32))).toNat]'(by
              rw [hhl1, hpp64]; omega)).toNat < s1.scratch.pos.length := by
          rw [hpl1]; omega
        c0_hsteps_nogrp
        · refine heap_finish hQ (by assumption) ?_ ?_ ?_
          · exact hcore1
          · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
              (by rw [List.length_set, hpl1])
          · exact ⟨heap_probePres_upd_hp_ps hpr1 _ _ _, _, _, by rw [hsc1]⟩
        · c0_steps
          refine hLoop1 _ (((i - 1) >>> (1 : BitVec 32)), ()) _ (by assumption)
            (by dsimp only; exact hip_lt) ?_ ?_ ?_
          · rfl
          · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
              (by rw [List.length_set, hpl1])
          · refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · exact Nat.lt_trans hip_lt hi1
            · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
                (by rw [List.length_set, hpl1])
            · exact heap_probePres_upd_hp_ps hpr1 _ _ _
            · dsimp only; exact hhl1_eq
            · exact ⟨_, _, by simp only [hsc1]; rfl⟩
      · refine heap_finish hQ (by assumption) ?_ ?_ ?_
        · exact hcore1
        · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
            (by rw [List.length_set, hpl1])
        · exact ⟨heap_probePres_upd_hp_ps hpr1 _ _ _, _, _, by rw [hsc1]⟩

/-- Soundness proof for `full_heap_down` against canonical `fullHeapDownSpec`. -/
theorem full_heap_down_wp (Γ : Env) :
    ∀ a m Q X, fullHeapDownSpec a m Q X → Func.wp Γ full_heap_down_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len; obtain hsl := hsok.score_len
  unfold Func.wp full_heap_down_body
  c0_hsteps
  · exact hQ () s m rfl hlen ⟨rfl, fullProbeScratchPres_refl s⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, fullProbeScratchPres_refl s⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, fullProbeScratchPres_refl s⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, fullProbeScratchPres_refl s⟩ hm
  · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
    have hhlen_le : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ s.core.cur_vars := by c0_bound
    refine wp_loop_safety_slice_pure (ts := [i32]) (fullSafetySlice c) s R
      (fun s1 (i, ()) =>
        i.toNat < (BitVec.ofNat 64 s.scratch.heap_len).toNat ∧ s1.LengthsOk c ∧
        FullProbeScratchPres s s1 ∧ s1.scratch.heap_len = s.scratch.heap_len ∧
        ∃ hp' ps', s1.scratch = { s.scratch with heap := hp', pos := ps' })
      (fun (i, ()) => (BitVec.ofNat 64 s.scratch.heap_len).toNat - i.toNat)
      (fun J hLoop => ?_)
      (fun J s1 (i, ()) m1 hcore1 hlen1 ⟨hi1, hs1, hpr1, hhl1_eq, hp1, ps1, hsc1⟩ hm1
        hLoop1 => ?_)
    · c0_hsteps
      refine hLoop s (_, ()) m hm rfl hlen ⟨?_, hlen, fullProbeScratchPres_refl s, rfl,
        s.scratch.heap, s.scratch.pos, rfl⟩
      c0_bound
    · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hm1 hlen1
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hs1.scratch_ok
      obtain hhl1 := hsok1.heap_len_arr; obtain hpl1 := hsok1.pos_len
      obtain hsl1 := hsok1.score_len
      have hi_lt_mx : i.toNat < c.max_vars := by omega
      c0_hsteps_nogrp
      · refine heap_finish hQ (by assumption) ?_ ?_ ?_
        · exact hcore1
        · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
            (by rw [List.length_set, hpl1])
        · exact ⟨by rw [hhl1_eq], heap_probePres_upd_hp_ps hpr1 _ _ _⟩
      · refine heap_finish hQ (by assumption) ?_ ?_ ?_
        · exact hcore1
        · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
            (by rw [List.length_set, hpl1])
        · exact ⟨by rw [hhl1_eq], heap_probePres_upd_hp_ps hpr1 _ _ _⟩
      · have hhl_mod_lt : s.scratch.heap_len % 2 ^ 64 < 2 ^ 29 := by
          have : (BitVec.ofNat 64 s.scratch.heap_len).toNat = s.scratch.heap_len % 2 ^ 64 := rfl
          omega
        have hleft_lt : (2 * i.toNat + 1) < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
          rw [heap_h2i1_64 i.toNat (by omega)] at *
          c0_bound
        refine wp_join_safety_slice (ts := [i64, i32, i64]) (fullSafetySlice c) s1 R
          (fun _ => True) trivial
          (fun s2 p =>
            i.toNat < p.fst.toNat ∧
            p.fst.toNat < (BitVec.ofNat 64 s.scratch.heap_len).toNat ∧
            p.snd.fst.toNat < s.core.cur_vars ∧
            s2 = s1 ∧ s2.scratch.heap_len = s.scratch.heap_len)
          (fun J2 s2 (cp', cv', csc', ()) m2 hcore2 hlen2 _ ⟨hgt, hlt, hcv_mv, hs2_eq, _⟩ hm2 => ?_)
          (fun J2 hJ2 => ?_)
        · subst hs2_eq
          dsimp only at hgt hlt hcv_mv
          rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hm2 hlen2
          c0_hsteps_nogrp
          · refine heap_finish hQ (by assumption) ?_ ?_ ?_
            · exact hcore1
            · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
                (by rw [List.length_set, hpl1])
            · exact ⟨by rw [hhl1_eq], heap_probePres_upd_hp_ps hpr1 _ _ _⟩
          · c0_steps
            refine hLoop1 _ (cp'.setWidth 32, ()) _ (by assumption) ?_ ?_ ?_ ?_
            · dsimp only
              have hcp32 : (cp'.setWidth 32).toNat = cp'.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              omega
            · rfl
            · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
                (by rw [List.length_set, hpl1])
            · refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hlt
              · exact heap_hlen_upd_hp_ps hs1 _ _ _ (by rw [List.length_set, hhl1])
                  (by rw [List.length_set, hpl1])
              · exact heap_probePres_upd_hp_ps hpr1 _ _ _
              · dsimp only; exact hhl1_eq
              · dsimp only; rw [hsc1]; exact ⟨_, _, rfl⟩
        · have hsh_p : (BitVec.setWidth 64 i <<< (1 : Nat)).toNat = 2 * i.toNat := by
            rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (by have := i.isLt; omega), Nat.shiftLeft_eq]
            omega
          have hcp_nat : ((BitVec.setWidth 64 i <<< (1 : Nat)) + 1).toNat = 2 * i.toNat + 1 := by
            rw [BitVec.toNat_add, hsh_p]; simp; omega
          have hsp_eq : ((BitVec.setWidth 64 i <<< (1 : Nat)) + 1 + 1).toNat =
              2 * i.toNat + 2 := by
            rw [BitVec.toNat_add, hcp_nat]; simp; omega
          have hleft_v_lt : (s1.scratch.heap[(BitVec.setWidth 64 i <<< (1 : Nat) + 1).toNat]'(by
              rw [hhl1, hcp_nat]; omega)).toNat < s.core.cur_vars := by
            have hget : s1.scratch.heap[(BitVec.setWidth 64 i <<< (1 : Nat) + 1).toNat]'(by
                  rw [hhl1, hcp_nat]; omega) =
                s1.scratch.heap[(2 * i.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hhl1]; bv_omega) := by
              congr 1; rw [hcp_nat]; simp; omega
            rw [hget]; c0_bound
          c0_hsteps
          all_goals
            refine hJ2 s1 _ _ hm1 rfl hs1 ⟨?_, ?_, ?_, rfl, hhl1_eq⟩
            · dsimp only; first | (rw [hsp_eq]; omega) | (rw [hcp_nat]; omega)
            · dsimp only
              first
              | (rw [hcp_nat]; exact hleft_lt)
              | (rw [hsp_eq]
                 have h1 : (2 * i.toNat + BitVec.toNat (1 : BitVec 64) +
                     BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s.scratch.heap_len % 2 ^ 64 := by
                   assumption
                 change (2 * i.toNat + 1 + 1) % 2 ^ 64 <
                   (BitVec.ofNat 64 s.scratch.heap_len).toNat at h1
                 rw [Nat.add_assoc, Nat.mod_eq_of_lt (by omega)] at h1
                 exact h1)
            · dsimp only
              first
              | exact hleft_v_lt
              | (have h1 : (2 * i.toNat + BitVec.toNat (1 : BitVec 64) +
                     BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s.scratch.heap_len % 2 ^ 64 := by
                   assumption
                 change (2 * i.toNat + 1 + 1) % 2 ^ 64 <
                   (BitVec.ofNat 64 s.scratch.heap_len).toNat at h1
                 rw [Nat.add_assoc, Nat.mod_eq_of_lt (by omega)] at h1
                 have hget : s1.scratch.heap[(BitVec.setWidth 64 i <<< (1 : Nat) + 1 + 1).toNat]'(by
                     rw [hhl1, hsp_eq]; omega) =
                   s1.scratch.heap[(2 * i.toNat + BitVec.toNat (1 : BitVec 64) +
                     BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                     rw [hhl1]; change (2 * i.toNat + 1 + 1) % 2 ^ 64 < c.max_vars
                     rw [Nat.add_assoc, Nat.mod_eq_of_lt (by omega)]; omega) := by
                   congr 1; rw [hsp_eq]; simp; omega
                 rw [hget]; c0_bound)
      all_goals exact absurd (by assumption : true = false) (by decide)

/-- Soundness proof for `full_heap_push` against canonical `fullHeapPushSpec`. -/
theorem full_heap_push_wp (Γ : Env)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullHeapPushSpec a m Q X → Func.wp Γ full_heap_push_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len
  unfold Func.wp full_heap_push_body
  c0_hsteps
  all_goals first
  | exact hQ () s m rfl hlen
      ⟨(fullProbeScratchPres_refl s).1, (fullProbeScratchPres_refl s).2.1,
       (fullProbeScratchPres_refl s).2.2.1, (fullProbeScratchPres_refl s).2.2.2.1,
       (fullProbeScratchPres_refl s).2.2.2.2.1, (fullProbeScratchPres_refl s).2.2.2.2.2.1,
       (fullProbeScratchPres_refl s).2.2.2.2.2.2.1, (fullProbeScratchPres_refl s).2.2.2.2.2.2.2,
       s.scratch.heap, s.scratch.pos, s.scratch.heap_len, rfl⟩ hm
  | (c0_call hUp
     have hfit_hl : s.scratch.heap_len % 2 ^ 64 < s.core.cur_vars := by c0_bound
     have hfit_v : v.toNat < s.core.cur_vars := by c0_bound
     refine heap_call_up_spec (by assumption) ?_ ?_
     · exact heap_hlen_upd_hp_ps hlen _ _ _ (by rw [List.length_set, hhl])
         (by rw [List.length_set, hpl])
     · intro _ s' m' hcore' hlen' ⟨hpr', hp', ps', hsc'⟩ hm'
       exact hQ () s' m' ((PreservesCoreSlice.of_update _ s _ (fun _ => rfl)).trans hcore')
         hlen' ⟨hpr'.1, hpr'.2.1, hpr'.2.2.1, hpr'.2.2.2.1, hpr'.2.2.2.2.1,
           hpr'.2.2.2.2.2.1, hpr'.2.2.2.2.2.2.1, hpr'.2.2.2.2.2.2.2,
           hp', ps', _, by rw [hsc']⟩ hm')

/-- Soundness proof for `full_heap_pop` against canonical `fullHeapPopSpec`. -/
theorem full_heap_pop_wp (Γ : Env)
    (hDown : ∀ a m Q X, fullHeapDownSpec a m Q X → Γ "full_heap_down" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullHeapPopSpec a m Q X → Func.wp Γ full_heap_pop_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len
  obtain hnlen_sub : 0 < s.scratch.heap_len ∧ s.scratch.heap_len ≤ s.core.cur_vars →
      (BitVec.ofNat 64 s.scratch.heap_len - 1).toNat = s.scratch.heap_len - 1 := by
    rintro ⟨hpos, hle⟩
    have h1 := bv64_ofNat_toNat (n := s.scratch.heap_len) (by omega)
    have h2 : 0 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by omega
    bv_omega
  unfold Func.wp full_heap_pop_body
  c0_hsteps_nogrp
  · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨Or.inl rfl, fun ⟨hpos, hle⟩ => by
      have h1 : (BitVec.ofNat 64 s.scratch.heap_len).toNat = 0 := by
        rw [bv64_ofNat_toNat (by omega)] at *; c0_bound
      rw [bv64_ofNat_toNat (by omega)] at h1; omega, fullProbeScratchPres_refl s⟩ hm
  · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨Or.inl rfl, fun ⟨_, hle⟩ => by
      have h1 : s.core.cur_vars < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
      rw [bv64_ofNat_toNat (by omega)] at h1; omega, fullProbeScratchPres_refl s⟩ hm
  · have hpos_hl : 0 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
    have hle_hl : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ s.core.cur_vars := by c0_bound
    have h0_hl : 0 < s.scratch.heap.length := by rw [hhl]; omega
    c0_hsteps_nogrp
    let s_nl : FullState := { s with scratch := { s.scratch with
        heap_len := (BitVec.ofNat 64 s.scratch.heap_len - 1#64).toNat } }
    have hlen_nl : s_nl.LengthsOk c :=
      heap_hlen_upd_hp_ps hlen _ _ _ hhl hpl
    refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s_nl R (fun _ => True) trivial
      (fun s1 _ => s1.scratch.heap_len = s_nl.scratch.heap_len ∧ FullProbeScratchPres s s1)
      (fun J1 s1 _ m1 hcore1 hlen1 _ ⟨hhl1, hpr1⟩ hm1 => ?_)
      (fun J1 hJ1 => ?_)
    · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hm1 hlen1
      refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R (fun _ => True) trivial
        (fun s2 _ => s2.scratch.heap_len = s_nl.scratch.heap_len ∧ FullProbeScratchPres s s2)
        (fun J2 s2 _ m2 hcore2 hlen2 _ ⟨hhl2, hpr2⟩ hm2 => ?_)
        (fun J2 hJ2 => ?_)
      · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hm2 hlen2
        c0_hsteps_nogrp
        · exact hQ (0xFFFFFFFF#64, ()) s2 m2 (hcore1.trans hcore2) hlen2
            ⟨Or.inl rfl, fun h => by rw [hhl2]; exact hnlen_sub h, hpr2⟩ hm2
        · have hv0_lt : (s.scratch.heap[0]'h0_hl).toNat < s.core.cur_vars := by
            simp only [Nat.zero_mod, OfNat.ofNat] at *; c0_bound
          exact hQ _ s2 m2 (hcore1.trans hcore2) hlen2
            ⟨Or.inr (by exact hv0_lt),
             fun h => by rw [hhl2]; exact hnlen_sub h, hpr2⟩ hm2
      · have hsp : (BitVec.ofNat 64 s.scratch.heap_len - 1#64).toNat < c.max_vars := by bv_omega
        have h0 : 0 < c.max_vars := by omega
        have hhl1_len := hlen1.scratch_ok.heap_len_arr
        have hpl1_len := hlen1.scratch_ok.pos_len
        c0_hsteps_nogrp
        · have hlast_lt : (s.scratch.heap[(BitVec.ofNat 64 s.scratch.heap_len - 1#64).toNat]'(by
              rw [hhl]; exact hsp)).toNat < c.max_vars := by
            c0_bound
          have hhl1_pos : 0 < s1.scratch.heap.length := by omega
          have hpl1_last : (s.scratch.heap[(BitVec.ofNat 64 s.scratch.heap_len - 1#64).toNat]'(by
              rw [hhl]; exact hsp)).toNat < s1.scratch.pos.length := by
            rw [hpl1_len]; exact hlast_lt
          dsimp only
          refine wp_store_sep (by
            simpa [Arg.val_var] using
              FullArenaTactics.store_full_heap (i := 0) _ hhl1_pos hm1) ?_
          intro m2 hm2
          clear hm1 m1
          c0_hsteps
          c0_call hDown
          refine heap_call_down_spec (by assumption) ?_ ?_
          · exact heap_hlen_upd_hp_ps hlen1 _ _ _ (by rw [List.length_set, hhl1_len])
              (by rw [List.length_set, hpl1_len])
          · intro _ s3 m3 hcore3 hlen3 ⟨hhl3, hpr3⟩ hm3
            exact hJ2 s3 () m3 hm3
              ((PreservesCoreSlice.of_update _ s1 _ (fun _ => rfl)).trans hcore3) hlen3
              ⟨hhl3.trans hhl1, fullProbeScratchPres_trans hpr1 hpr3⟩
        · exact hJ2 s1 () m1 hm1 rfl hlen1 ⟨hhl1, hpr1⟩
        · exact hJ2 s1 () m1 hm1 rfl hlen1 ⟨hhl1, hpr1⟩
    · try dsimp only [fullSafetySlice] at *
      c0_hsteps_nogrp
      · refine heap_pop_j1 hJ1 (by assumption) ?_ ?_ ?_ ?_
        · rfl
        · exact heap_hlen_upd_hp_ps hlen _ _ _ hhl (by simp [hpl])
        · rfl
        · exact fullProbeScratchPres_refl s
      · refine heap_pop_j1 hJ1 (by assumption) ?_ ?_ ?_ ?_
        · rfl
        · exact heap_hlen_upd_hp_ps hlen _ _ _ hhl (by simp [hpl])
        · rfl
        · exact fullProbeScratchPres_refl s

end LeanQbe.T.Examples.Kissat.Proof.Heap
