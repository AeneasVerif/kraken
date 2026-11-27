/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Src.Decide
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb

/-!
# Soundness Proofs for `Kissat.Src.Decide` — Part 0 (`Proof.Decide.Wp0`)

Proves `full_next_dec_var_wp` against `Proof.Spec.fullNextDecVarSpec` (`0` legacy imports,
`0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Decide

open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Decide
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem bv8_sext32_eq_zero (x : BitVec 8) (h : x.signExtend 32 = 0#32) : x = 0#8 := by
  ext i hi
  have h1 := congrArg (·[i]) h
  simpa [BitVec.getElem_signExtend, hi, show i < 32 by omega] using h1

private theorem bv64_shl1_toNat_lt {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt h]

private theorem fullMem_with_heap_len_mod {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (FullMem c { s with scratch := { s.scratch with
      heap_len := s.scratch.heap_len % 2 ^ 64 } } ⋆ R) m := by
  have hword : BitVec.ofNat 64 (s.scratch.heap_len % 2 ^ 64) =
      BitVec.ofNat 64 s.scratch.heap_len := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
  have hhdr : hdrTailWords c { s with scratch := { s.scratch with
      heap_len := s.scratch.heap_len % 2 ^ 64 } } = hdrTailWords c s := by
    unfold hdrTailWords HdrWordField.tailChunk0 HdrWordField.tailChunk1
      HdrWordField.tailChunk2 HdrWordField.tailChunk3
    simp only [hword]
  simpa only [FullMem, FullCoreArrays, FullScratchArrays, FullScrByteArrs, FullScrU32A,
    FullScrWksArrs, FullScrMetaArrs, FullScrDynArrs, hhdr] using hm

private theorem heap_len_mod_lengthsOk {c : FullCfg} {s : FullState} (h : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      heap_len := s.scratch.heap_len % 2 ^ 64 } } : FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with walk_vals_len := h.scratch_ok.walk_vals_len }⟩

private theorem qsearch_upd_lengthsOk {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    (idx stamp : BitVec 64) :
    ({ s with scratch := { s.scratch with
      q_search_idx := idx, q_search_stamp := stamp } } : FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with walk_vals_len := h.scratch_ok.walk_vals_len }⟩

private theorem next_dec_found_ret {c : FullCfg} {s s' : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m' : Mem 64} {r : BitVec 64}
    (hQ : ∀ (r : Tup Val [i64]) (s1 : FullState) (m1 : Mem 64),
      PreservesCoreSlice (fullSafetySlice c).coreProj s s1 →
      (fullSafetySlice c).safe s1 →
      (FullExtScratchPres s s1 ∧
        (r.1 = 0xFFFFFFFFFFFFFFFF#64 ∨
          r.1.toNat < s.core.cur_vars ∧ s.core.vals[2 * r.1.toNat]?.getD 0#8 = 0#8)) →
      ((fullSafetySlice c).mem s1 ⋆ R) m1 → Q r m1)
    (hcore : s'.core = s.core) (hlen' : s'.LengthsOk c)
    (hext' : FullExtScratchPres s s') (hr : r.toNat < s.core.cur_vars)
    (hv_lt : 2 * r.toNat < s'.core.vals.length)
    (hval : s'.core.vals[2 * r.toNat]'hv_lt = 0#8) (hm' : (FullMem c s' ⋆ R) m') :
    Q (r, ()) m' := by
  refine hQ (r, ()) s' m' hcore hlen' ⟨hext', Or.inr ⟨hr, ?_⟩⟩ hm'
  rw [List.getElem?_eq_getElem (by rwa [← hcore]), Option.getD_some]
  simpa [hcore] using hval

private theorem next_dec_not_found_ret {c : FullCfg} {s s' : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m' : Mem 64}
    (hQ : ∀ (r : Tup Val [i64]) (s1 : FullState) (m1 : Mem 64),
      PreservesCoreSlice (fullSafetySlice c).coreProj s s1 →
      (fullSafetySlice c).safe s1 →
      (FullExtScratchPres s s1 ∧
        (r.1 = 0xFFFFFFFFFFFFFFFF#64 ∨
          r.1.toNat < s.core.cur_vars ∧ s.core.vals[2 * r.1.toNat]?.getD 0#8 = 0#8)) →
      ((fullSafetySlice c).mem s1 ⋆ R) m1 → Q r m1)
    (hcore : s'.core = s.core) (hlen' : s'.LengthsOk c)
    (hext' : FullExtScratchPres s s') (hm' : (FullMem c s' ⋆ R) m') :
    Q (0xFFFFFFFFFFFFFFFF#64, ()) m' :=
  hQ (0xFFFFFFFFFFFFFFFF#64, ()) s' m' hcore hlen' ⟨hext', Or.inl rfl⟩ hm'

/-- Soundness proof for `full_next_dec_var` against canonical `fullNextDecVarSpec`. -/
theorem full_next_dec_var_wp (Γ : Env)
    (hPop : ∀ a m Q X, fullHeapPopSpec a m Q X → Γ "full_heap_pop" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullNextDecVarSpec a m Q X → Func.wp Γ full_next_dec_var_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  obtain hcv_le := hlen.core_ok.cur_vars_le
  unfold Func.wp full_next_dec_var_body
  c0_hsteps_nogrp
  refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s R (fun _ => True) trivial
    (fun s1 _ => FullExtScratchPres s s1)
    (fun Jf s1 _ m1 hcore1 hs1 _ hext1 hm1 => ?_) (fun Jf hJf => ?_)
  · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hs1 hm1
    have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hs1.core_ok.cur_vars_le
    c0_hsteps_nogrp
    refine wp_loop_safety_slice (fullSafetySlice c) s1 R (fun _ => True) trivial
      (fun s2 (v, ()) => v.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s2)
      (fun (v, ()) => s.core.cur_vars - v.toNat)
      (fun Jv hJv => ?_)
      (fun Jv s2 (v, ()) m2 hcore2 hs2 _ ⟨hvle, hext2⟩ hm2 hJv => ?_)
    · c0_hsteps; exact hJv s1 (0#64, ()) m1 hm1 rfl hs1 ⟨by simp, hext1⟩
    · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hs2 hm2
      have hfl2 := hs2.core_ok.flags_len
      have hvl2 := hs2.core_ok.vals_len
      c0_hsteps_nogrp
      · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
        have hv_fl : v.toNat < s2.core.flags.length := by
          rw [hfl2]; exact Nat.lt_of_lt_of_le hv_lt hcv_le
        have hv2_lt : (v <<< (1 : Nat)).toNat < s2.core.vals.length := by
          rw [hvl2, bv64_shl1_toNat_lt (by omega)]; omega
        have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
        refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s2 R (fun _ => True) trivial
          (fun s3 _ => FullExtScratchPres s s3)
          (fun Js s3 _ m3 hcore3 hs3 _ hext3 hm3 => ?_) (fun Js hJs => ?_)
        · rw [Blocks.get_here]; c0_hsteps
          exact hJv s3 (v + 1#64, ()) m3 hm3 (by dsimp only; rw [hv1]; omega)
            hcore3 hs3 ⟨by rw [hv1]; omega, hext3⟩
        · c0_hsteps_nogrp
          · have hmod : 2 * v.toNat % 2 ^ 64 = 2 * v.toNat := Nat.mod_eq_of_lt (by omega)
            have hval_v : s2.core.vals[2 * v.toNat]'(by rw [hvl2]; omega) = 0#8 :=
              bv8_sext32_eq_zero _ (by simpa only [hmod] using (by assumption :
                (s2.core.vals[2 * v.toNat % 2 ^ 64]).signExtend 32 = 0#32))
            exact next_dec_found_ret hQ (hcore1.trans hcore2) hs2 hext2 hv_lt _ hval_v hm2
          · exact hJs s2 () m2 hm2 rfl hs2 hext2
          · exact hJs s2 () m2 hm2 rfl hs2 hext2
      · exact next_dec_not_found_ret hQ (hcore1.trans hcore2) hs2 hext2 hm2
  · c0_hsplit
    · c0_hsteps_nogrp
      refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) s R (fun _ => True) trivial
        (fun s1 _ => FullExtScratchPres s s1)
        (fun Js s1 _ m1 hcore1 hs1 _ hext1 hm1 => ?_) (fun Js hJs => ?_)
      · rw [Blocks.get_here]; c0_hsteps; exact hJf s1 () m1 hm1 hcore1 hs1 hext1
      · let s0 := { s with scratch := { s.scratch with heap_len := s.scratch.heap_len % 2 ^ 64 } }
        have hm0 : (FullMem c s0 ⋆ R) m := fullMem_with_heap_len_mod hm
        have hlen0 : s0.LengthsOk c := heap_len_mod_lengthsOk hlen
        refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) s0 R
          (fun _ => True) trivial
          (fun s1 (hl, ()) => hl = BitVec.ofNat 64 s1.scratch.heap_len ∧
            s1.scratch.heap_len < 2 ^ 64 ∧ FullExtScratchPres s s1)
          (fun (hl, ()) => hl.toNat)
          (fun Jh hJh => ?_)
          (fun Jh s1 (hl, ()) m1 hcore1 hs1 _ ⟨hhl_eq1, hhl_lt1, hext1⟩ hm1 hJh => ?_)
        · c0_hsteps
          exact hJh s0 (BitVec.ofNat 64 s.scratch.heap_len, ()) m hm0 rfl hlen0
            ⟨by apply BitVec.eq_of_toNat_eq; simp [s0, BitVec.toNat_ofNat],
             Nat.mod_lt _ (by decide), fullExtScratchPres_refl s⟩
        · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hs1 hm1
          have hcore1s : s1.core = s.core := hcore1
          have hhl1 := hs1.scratch_ok.heap_len_arr
          have hfl1 := hs1.core_ok.flags_len
          have hvl1 := hs1.core_ok.vals_len
          have hhl_toNat : hl.toNat = s1.scratch.heap_len := by
            rw [hhl_eq1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhl_lt1]
          c0_hsteps_nogrp
          · have hpos1 : 0 < s1.scratch.heap_len := by
              have hc1 : 0 < hl.toNat := by c0_bound
              rwa [hhl_toNat] at hc1
            have hle1 : s1.scratch.heap_len ≤ s.core.cur_vars := by
              have hc2 : hl.toNat ≤ s.core.cur_vars % 2 ^ 64 := by c0_bound
              rwa [hhl_toNat, Nat.mod_eq_of_lt (by omega)] at hc2
            have hhp0_lt : 0 < s1.scratch.heap.length := by rw [hhl1]; omega
            let top := s1.scratch.heap[0]'hhp0_lt
            c0_hsteps_nogrp
            · exact hJs s1 (hl, ()) m1 hm1 hcore1s hs1 hext1
            · have hzt : (top.setWidth 64).toNat = top.toNat := zext_toNat _ (by decide)
              have htop_eq : s1.scratch.heap[(0 : Nat) % 2 ^ 64]'(by
                  rw [Nat.zero_mod]; exact hhp0_lt) = top := by
                rw [← Option.some_inj,
                  ← List.getElem?_eq_getElem (by rw [Nat.zero_mod]; exact hhp0_lt),
                  Nat.zero_mod, List.getElem?_eq_getElem hhp0_lt]
              have htop_lt : top.toNat < s.core.cur_vars := by
                have hc' := (by assumption :
                  ¬ s.core.cur_vars % 2 ^ 64 ≤
                    (s1.scratch.heap[(0 : Nat) % 2 ^ 64]'(by
                      rw [Nat.zero_mod]; exact hhp0_lt)).toNat)
                rw [htop_eq] at hc'
                have h1 : top.toNat < s.core.cur_vars % 2 ^ 64 := by omega
                rwa [Nat.mod_eq_of_lt (by omega)] at h1
              have htop_fl : (top.setWidth 64).toNat < s1.core.flags.length := by
                rw [hfl1, hzt]; omega
              have htop2_lt : ((top.setWidth 64) <<< (1 : Nat)).toNat < s1.core.vals.length := by
                rw [hvl1, bv64_shl1_toNat_lt (by rw [hzt]; omega), hzt]
                omega
              refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R
                (fun _ => True) trivial
                (fun s2 _ => s2.scratch.heap_len = s1.scratch.heap_len ∧
                  FullExtScratchPres s s2)
                (fun Jpop s2 _ m2 hcore2 hs2 _ ⟨hhl_eq2, hext2⟩ hm2 => ?_)
                (fun Jpop hJpop => ?_)
              · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hs2 hm2
                c0_hsteps_nogrp; c0_call hPop
                refine ⟨c, s2, R, rfl, hs2, hm2, fun _ s3 m3 hcore3 hs3 ⟨_, hdec, hpres3⟩ hm3 => ?_⟩
                dsimp only [fullSafetySlice] at hcore3 hs3 hm3
                have hs3_eq := hdec ⟨by rw [hhl_eq2]; exact hpos1,
                  by rw [hhl_eq2, hcore2, hcore1s]; exact hle1⟩
                c0_hsteps
                exact hJh s3 (BitVec.ofNat 64 s3.scratch.heap_len, ()) m3 hm3
                  (by
                    dsimp only
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hs3_eq, hhl_eq2]; omega),
                      hhl_toNat, hs3_eq, hhl_eq2]
                    omega)
                  (hcore2.trans hcore3) hs3
                  ⟨rfl, by rw [hs3_eq, hhl_eq2]; omega,
                   fullExtScratchPres_trans hext2 hpres3.1⟩
              · c0_hsteps_nogrp
                · have hmodt : (2 * top.toNat) % 2 ^ 64 = 2 * top.toNat :=
                    Nat.mod_eq_of_lt (by omega)
                  have hidx0 : 2 * (s1.scratch.heap[(0 : Nat) % 2 ^ 64]'(by
                      rw [Nat.zero_mod]; exact hhp0_lt)).toNat % 2 ^ 64 <
                      s1.core.vals.length := by
                    rw [htop_eq, hmodt, hvl1]; omega
                  have hc' := (by assumption :
                    (s1.core.vals[2 * (s1.scratch.heap[(0 : Nat) % 2 ^ 64]'(by
                      rw [Nat.zero_mod]; exact hhp0_lt)).toNat % 2 ^ 64]'hidx0).signExtend 32 =
                      0#32)
                  have hc'' : (s1.core.vals[2 * top.toNat]'(by rw [hvl1]; omega)).signExtend 32 =
                      0#32 := by
                    have hget : s1.core.vals[2 * top.toNat]'(by rw [hvl1]; omega) =
                        s1.core.vals[2 * (s1.scratch.heap[(0 : Nat) % 2 ^ 64]'(by
                          rw [Nat.zero_mod]; exact hhp0_lt)).toNat % 2 ^ 64]'hidx0 := by
                      rw [← Option.some_inj,
                        ← List.getElem?_eq_getElem (by rw [hvl1]; omega),
                        ← List.getElem?_eq_getElem hidx0, htop_eq, hmodt]
                    rw [hget]; exact hc'
                  have hval_t : s1.core.vals[2 * (top.setWidth 64).toNat]'(by
                      rw [hvl1, hzt]; omega) = 0#8 :=
                    bv8_sext32_eq_zero _ (by simpa only [hzt] using hc'')
                  exact next_dec_found_ret hQ hcore1s hs1 hext1
                    (by simpa only [BitVec.toNat_ofNat, Nat.zero_mod, hzt, top] using htop_lt)
                    _ hval_t hm1
                · exact hJpop s1 () m1 hm1 rfl hs1 ⟨rfl, hext1⟩
                · exact hJpop s1 () m1 hm1 rfl hs1 ⟨rfl, hext1⟩
          · exact hJs s1 (hl, ()) m1 hm1 hcore1s hs1 hext1
          · exact hJs s1 (hl, ()) m1 hm1 hcore1s hs1 hext1
    · c0_hsteps_nogrp
      refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s R
        (fun _ => True) trivial
        (fun s1 (cur, steps, ()) => steps.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s1)
        (fun (_, steps, ()) => s.core.cur_vars - steps.toNat)
        (fun J1 hJ1 => ?_)
        (fun J1 s1 (cur, steps, ()) m1 hcore1 hs1 _ ⟨hst1, hext1⟩ hm1 hJ1 => ?_)
      · c0_hsteps
        exact hJ1 s (s.scratch.q_search_idx, 0#64, ()) m hm rfl hlen
          ⟨by simp, fullExtScratchPres_refl s⟩
      · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hs1 hm1
        have hcore1s : s1.core = s.core := hcore1
        have hfl1 := hs1.core_ok.flags_len
        have hvl1 := hs1.core_ok.vals_len
        have hqpl1 := hs1.scratch_ok.q_prev_len
        have hqsl1 := hs1.scratch_ok.q_stamp_len
        refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R (fun _ => True) trivial
          (fun s2 _ => FullExtScratchPres s s2)
          (fun J2w s2 _ m2 hcore2 hs2 _ hext2 hm2 => ?_) (fun J2w hJ2w => ?_)
        · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hs2 hm2
          have hcore2s : s2.core = s.core := hcore1.trans hcore2
          c0_hsteps_nogrp
          refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s2 R
            (fun _ => True) trivial
            (fun s3 (cur2, steps2, ()) =>
              steps2.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s3)
            (fun (_, steps2, ()) => s.core.cur_vars - steps2.toNat)
            (fun J2 hJ2 => ?_)
            (fun J2 s3 (cur2, steps2, ()) m3 hcore3 hs3 _ ⟨hst3, hext3⟩ hm3 hJ2 => ?_)
          · c0_hsteps
            exact hJ2 s2 (s2.scratch.q_last, 0#64, ()) m2 hm2 rfl hs2 ⟨by simp, hext2⟩
          · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore3 hs3 hm3
            have hcore3s : s3.core = s.core := Eq.trans hcore3 hcore2s
            have hfl3 := hs3.core_ok.flags_len
            have hvl3 := hs3.core_ok.vals_len
            have hqpl3 := hs3.scratch_ok.q_prev_len
            have hqsl3 := hs3.scratch_ok.q_stamp_len
            c0_hsteps_nogrp
            · have hcur2_lt : cur2.toNat < s.core.cur_vars := by
                have h1 := (by assumption : cur2.toNat < s.core.cur_vars % 2 ^ 64)
                rwa [Nat.mod_eq_of_lt (by omega)] at h1
              have hst2_lt : steps2.toNat < s.core.cur_vars := by
                have h1 := (by assumption : steps2.toNat < s.core.cur_vars % 2 ^ 64)
                rwa [Nat.mod_eq_of_lt (by omega)] at h1
              have hcur2_fl : cur2.toNat < s3.core.flags.length := by rw [hfl3]; omega
              have hcur22_lt : (cur2 <<< (1 : Nat)).toNat < s3.core.vals.length := by
                rw [hvl3, bv64_shl1_toNat_lt (by omega)]; omega
              have hcur2_qp : cur2.toNat < s3.scratch.q_prev.length := by rw [hqpl3]; omega
              have hcur2_qs : cur2.toNat < s3.scratch.q_stamp.length := by rw [hqsl3]; omega
              have hst2' : (steps2 + 1#64).toNat = steps2.toNat + 1 := by bv_omega
              refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s3 R
                (fun _ => True) trivial
                (fun s4 _ => FullExtScratchPres s s4)
                (fun Jnxt s4 _ m4 hcore4 hs4 _ hext4 hm4 => ?_) (fun Jnxt hJnxt => ?_)
              · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore4 hs4 hm4
                have hqpl4 := hs4.scratch_ok.q_prev_len
                c0_hsteps
                exact hJ2 s4 ((s4.scratch.q_prev[cur2.toNat]'(by rw [hqpl4]; omega)).setWidth 64,
                  steps2 + 1#64, ()) m4 hm4 (by dsimp only; rw [hst2']; omega)
                  hcore4 hs4 ⟨by rw [hst2']; omega, hext4⟩
              · c0_hsteps_nogrp
                · have hmod2 : 2 * cur2.toNat % 2 ^ 64 = 2 * cur2.toNat :=
                    Nat.mod_eq_of_lt (by omega)
                  have hval_c2 : s3.core.vals[2 * cur2.toNat]'(by rw [hvl3]; omega) = 0#8 :=
                    bv8_sext32_eq_zero _ (by simpa only [hmod2] using (by assumption :
                      (s3.core.vals[2 * cur2.toNat % 2 ^ 64]).signExtend 32 = 0#32))
                  c0_hsteps
                  let qss2 := (s3.scratch.q_stamp[cur2.toNat]'hcur2_qs).setWidth 64
                  let s3' : FullState :=
                    { s3 with scratch :=
                      { s3.scratch with q_search_idx := cur2, q_search_stamp := qss2 } }
                  exact next_dec_found_ret (s' := s3') hQ hcore3s
                    (qsearch_upd_lengthsOk hs3 cur2 qss2)
                    hext3 hcur2_lt (by rw [hvl3]; omega) hval_c2
                    (by dsimp only [s3', qss2]; exact hm)
                · exact hJnxt s3 () m3 hm3 rfl hs3 hext3
                · exact hJnxt s3 () m3 hm3 rfl hs3 hext3
            · exact hJf s3 () m3 hm3 hcore3s hs3 hext3
            · exact hJf s3 () m3 hm3 hcore3s hs3 hext3
        · c0_hsteps_nogrp
          · have hcur_lt : cur.toNat < s.core.cur_vars := by
              have h1 := (by assumption : cur.toNat < s.core.cur_vars % 2 ^ 64)
              rwa [Nat.mod_eq_of_lt (by omega)] at h1
            have hst_lt : steps.toNat < s.core.cur_vars := by
              have h1 := (by assumption : steps.toNat < s.core.cur_vars % 2 ^ 64)
              rwa [Nat.mod_eq_of_lt (by omega)] at h1
            have hcur_fl : cur.toNat < s1.core.flags.length := by rw [hfl1]; omega
            have hcur2_lt : (cur <<< (1 : Nat)).toNat < s1.core.vals.length := by
              rw [hvl1, bv64_shl1_toNat_lt (by omega)]; omega
            have hcur_qp : cur.toNat < s1.scratch.q_prev.length := by rw [hqpl1]; omega
            have hcur_qs : cur.toNat < s1.scratch.q_stamp.length := by rw [hqsl1]; omega
            have hst1' : (steps + 1#64).toNat = steps.toNat + 1 := by bv_omega
            refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R
              (fun _ => True) trivial
              (fun s2 _ => FullExtScratchPres s s2)
              (fun Jnxt s2 _ m2 hcore2 hs2 _ hext2 hm2 => ?_) (fun Jnxt hJnxt => ?_)
            · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hs2 hm2
              have hqpl2 := hs2.scratch_ok.q_prev_len
              c0_hsteps
              exact hJ1 s2 ((s2.scratch.q_prev[cur.toNat]'(by rw [hqpl2]; omega)).setWidth 64,
                steps + 1#64, ()) m2 hm2 (by dsimp only; rw [hst1']; omega)
                hcore2 hs2 ⟨by rw [hst1']; omega, hext2⟩
            · c0_hsteps_nogrp
              · have hmod1 : 2 * cur.toNat % 2 ^ 64 = 2 * cur.toNat := Nat.mod_eq_of_lt (by omega)
                have hval_c1 : s1.core.vals[2 * cur.toNat]'(by rw [hvl1]; omega) = 0#8 :=
                  bv8_sext32_eq_zero _ (by simpa only [hmod1] using (by assumption :
                    (s1.core.vals[2 * cur.toNat % 2 ^ 64]).signExtend 32 = 0#32))
                c0_hsteps
                let qss1 := (s1.scratch.q_stamp[cur.toNat]'hcur_qs).setWidth 64
                let s1' : FullState :=
                  { s1 with scratch :=
                    { s1.scratch with q_search_idx := cur, q_search_stamp := qss1 } }
                exact next_dec_found_ret (s' := s1') hQ hcore1s (qsearch_upd_lengthsOk hs1 cur qss1)
                  hext1 hcur_lt (by rw [hvl1]; omega) hval_c1
                  (by dsimp only [s1', qss1]; exact hm)
              · exact hJnxt s1 () m1 hm1 rfl hs1 hext1
              · exact hJnxt s1 () m1 hm1 rfl hs1 hext1
          · exact hJ2w s1 () m1 hm1 rfl hs1 hext1
          · exact hJ2w s1 () m1 hm1 rfl hs1 hext1

end LeanQbe.T.Examples.Kissat.Proof.Decide
