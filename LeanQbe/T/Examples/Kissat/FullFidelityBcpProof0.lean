/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBcp
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
import all LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullHeurWalkLemmas1
import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Hot-Loop Caching & Delayed-Watch Flush Proofs (`FullFidelityBcpProof0`)

Plain `public section` (`0` `@[expose]`, `0` `public import all`, `std3` axioms only;
private `import all` of `FullM6HdrProof0` (for `M6HdrExtInitOk`)):
1. `full_heap_down_fid_wp` (`Full.fullHeapDownSpec`, hoisted `nvars = h->cur_vars` and `sc[sv]`).
2. `full_heap_pop_fid_wp` (`Full.fullHeapPopSpec`, hoisted `nvars` and `hlen`).
3. `full_next_dec_var_fid_wp` (`Full.fullNextDecVarSpec`, split stable/focused pointer loads).
4. `m6_hdr_decide_fid_fast_wp` (`FullM6Hdr.m6HdrDecideSpec`, fast inline magic check).
5. `fidPropFlushDelSpec` & `full_prop_flush_del_fid_wp` (linear `h->delayed` flush preserving
   both `WatchesInv` and `SplitWatchesInv`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBcp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullHeurWalkSpecs
open LeanQbe.T.Examples.Kissat.Full.FullWalkExtSpecs
open LeanQbe.T.Examples.Kissat.Full.FullWalkExtHelpers
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullHeurWalkTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullWalkExtTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

private theorem fid_bv64_ofNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem fid_hlen_upd_hp_ps {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hp' ps' : List (BitVec 32)) (hl' : Nat)
    (hhp : hp'.length = c.max_vars) (hps : ps'.length = c.max_vars) :
    ({ s with scratch :=
      { s.scratch with heap := hp', pos := ps', heap_len := hl' } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with heap_len_arr := hhp, pos_len := hps }⟩

private theorem fid_sext32_eq_zero {x : BitVec 8}
    (h : BitVec.signExtend 32 x = 0#32) : x = 0#8 := by
  apply BitVec.eq_of_toInt_eq
  have h1 := congrArg BitVec.toInt h
  rw [BitVec.toInt_signExtend_of_le (by decide)] at h1
  exact h1

private theorem fid_probePres_refl (s : FullState) : Full.FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem fid_probePres_upd_hp_ps {s0 s1 : FullState}
    (h : Full.FullProbeScratchPres s0 s1) (hp' ps' : List (BitVec 32)) (hl' : Nat) :
    Full.FullProbeScratchPres s0
      { s1 with scratch := { s1.scratch with heap := hp', pos := ps', heap_len := hl' } } := h

/-! ## 1. `full_heap_down_fid_wp` & `full_heap_pop_fid_wp` -/

/-- Canonical `Full.fullHeapDownSpec` proof for `full_heap_down_fid_body`. -/
theorem full_heap_down_fid_wp (Γ : Env) :
    ∀ a m Q X, Full.fullHeapDownSpec a m Q X → Func.wp Γ full_heap_down_fid_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len; obtain hsl := hsok.score_len
  unfold Func.wp full_heap_down_fid_body
  c0_steps
  · exact hQ () s m rfl hlen ⟨rfl, fid_probePres_refl s⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, fid_probePres_refl s⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, fid_probePres_refl s⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, fid_probePres_refl s⟩ hm
  · obtain hv : v.toNat < s.core.cur_vars := by c0_bound
    obtain hhle : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ s.core.cur_vars := by c0_bound
    obtain hp0_lt : (s.scratch.pos[(v.setWidth 64).toNat]'(by
        rw [zext_toNat _ (by decide)]; omega)).toNat <
        (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
      have : (s.scratch.pos[(v.setWidth 64).toNat]'(by
          rw [zext_toNat _ (by decide)]; omega)).toNat < s.scratch.heap_len % 2 ^ 64 := by
        c0_bound
      simpa [BitVec.toNat_ofNat] using this
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
      (fun s1 (p, ()) => p.toNat < (BitVec.ofNat 64 s.scratch.heap_len).toNat ∧
        s1.scratch.heap_len = s.scratch.heap_len ∧
        Full.FullProbeScratchPres s s1)
      (fun (p, ()) => (BitVec.ofNat 64 s.scratch.heap_len).toNat - p.toNat)
      (fun J hLoop => ?_)
      (fun J s1 (p, ()) m1 hcore1 hlen1 ⟨hp, hhl_eq, hpr1⟩ hm1 hLoop1 => ?_)
    · c0_steps
      exact hLoop s (_, ()) m hm rfl hlen ⟨hp0_lt, rfl, fid_probePres_refl s⟩
    · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok
      obtain hhl1 := hsok1.heap_len_arr; obtain hpl1 := hsok1.pos_len
      obtain hsl1 := hsok1.score_len
      obtain hp_mv : p.toNat < c.max_vars := by omega
      obtain hsh_p : (p.setWidth 64 <<< (1 : Nat)).toNat = 2 * p.toNat := by
        rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]; simp [Nat.shiftLeft_eq]; omega
      obtain hcp_toNat : ((p.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * p.toNat + 1 := by
        rw [BitVec.toNat_add, hsh_p]; simp; omega
      refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
      c0_split
      · c0_steps
        refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore1.update _
        · exact fid_hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
        · exact ⟨hhl_eq, fid_probePres_upd_hp_ps hpr1 _ _ _⟩
      · have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hceq1]
        have hhlen64 : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ c.max_vars := by omega
        have hcp_lt : 2 * p.toNat + 1 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
          have : (BitVec.setWidth 64 p <<< (1 : Nat) + 1).toNat <
              (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
          rw [hcp_toNat] at this; exact this
        have hcp_hlt :
            (BitVec.setWidth 64 p <<< (1 : Nat) + 1).toNat < s1.scratch.heap.length := by
          rw [hhl1, hcp_toNat]; omega
        refine wp_load_of (FullArenaTactics.c0_load_full_heap hcp_hlt hm1) ?_
        c0_split
        · c0_steps
          refine hQ () _ m ?_ ?_ ?_ hm
          · exact hcore1.update _
          · exact fid_hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
          · exact ⟨hhl_eq, fid_probePres_upd_hp_ps hpr1 _ _ _⟩
        · have hcv_lt : (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) +
              1).toNat]'hcp_hlt).toNat < s.core.cur_vars := by
            have : (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) +
                1).toNat]'hcp_hlt).toNat < s1.core.cur_vars := by
              rw [hceq1] at *; c0_bound
            omega
          have hcv_sc : (BitVec.setWidth 64 (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) +
              1).toNat]'hcp_hlt)).toNat < s1.scratch.score.length := by
            rw [zext_toNat _ (by decide)]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i32, i64])
            (fun (cp', cv', _csc', ()) m2 => p.toNat < cp'.toNat ∧
              cp'.toNat < (BitVec.ofNat 64 s.scratch.heap_len).toNat ∧
              cv'.toNat < s.core.cur_vars ∧ m1 = m2)
            (fun _ (cp', cv', csc', ()) m2 ⟨hgt, hlt, hcv_mv, hm2⟩ => ?_) ?_
          · rcases hm2 with rfl; c0_steps
            · refine hQ () _ m ?_ ?_ ?_ hm
              · exact hcore1.update _
              · exact fid_hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
              · exact ⟨hhl_eq, fid_probePres_upd_hp_ps hpr1 _ _ _⟩
            · have hcp32 : (cp'.setWidth 32).toNat = cp'.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              refine hLoop1 _ (cp'.setWidth 32, ()) m hm (by dsimp only; omega) rfl ?_
                ⟨by dsimp only; omega, hhl_eq, fid_probePres_upd_hp_ps hpr1 _ _ _⟩
              exact fid_hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
          · intro Jm hJm; c0_steps
            · have hsp_eq : (BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat =
                  2 * p.toNat + 2 := by
                rw [BitVec.toNat_add, hcp_toNat]; simp; omega
              have hsp_lt : 2 * p.toNat + 2 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
                have : (BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat <
                    (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
                omega
              have hsv_mv : (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat]'(
                  by rw [hhl1, hsp_eq]; omega)).toNat < s.core.cur_vars := by
                have h0 : s1.scratch.heap[(2 * p.toNat + 1 + 1) % 2 ^ 64].toNat <
                    s.core.cur_vars % 2 ^ 64 := by assumption
                have hidx_eq : (2 * p.toNat + 1 + 1) % 2 ^ 64 =
                    (BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat := by
                  rw [hsp_eq]; omega
                simp only [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h0
                simpa only [hidx_eq] using h0
              exact hJm ((BitVec.setWidth 64 p <<< (1 : Nat)) + 1 + 1, _, _, ()) m1
                ⟨by rw [hsp_eq]; omega, by rw [hsp_eq]; omega, hsv_mv, rfl⟩
            all_goals
              refine hJm _ _ ⟨by rw [hcp_toNat]; omega,
                by rw [hcp_toNat]; omega,
                hcv_lt, rfl⟩

/-- Canonical `Full.fullHeapPopSpec` proof for `full_heap_pop_fid_body`. -/
theorem full_heap_pop_fid_wp (Γ : Env)
    (hDown : ∀ a m Q X, Full.fullHeapDownSpec a m Q X →
      Γ "full_heap_down" [i64, i32] [] a m Q X) :
    ∀ a m Q X, Full.fullHeapPopSpec a m Q X → Func.wp Γ full_heap_pop_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len
  obtain hnlen_sub : 0 < s.scratch.heap_len ∧ s.scratch.heap_len ≤ s.core.cur_vars →
      (BitVec.ofNat 64 s.scratch.heap_len - 1).toNat = s.scratch.heap_len - 1 :=
    fun ⟨hpos, hle⟩ => by
      have h1 := fid_bv64_ofNat (n := s.scratch.heap_len) (by omega)
      have : 0 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by omega
      bv_omega
  unfold Func.wp full_heap_pop_fid_body
  c0_hsteps_nogrp
  · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨Or.inl rfl, fun ⟨hpos, hle⟩ => by
      have h0 : BitVec.ofNat 64 s.scratch.heap_len = 0 := by assumption
      have h1 := congrArg BitVec.toNat h0
      rw [fid_bv64_ofNat (by omega)] at h1; simp at h1; omega, fid_probePres_refl s⟩ hm
  · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨Or.inl rfl, fun ⟨_, hle⟩ => by
      have h0 : s.core.cur_vars % 2 ^ 64 < s.scratch.heap_len % 2 ^ 64 := by assumption
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : s.scratch.heap_len < 2 ^ 64)] at h0; omega,
      fid_probePres_refl s⟩ hm
  · have hhl_pos : 0 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
      have hne : BitVec.ofNat 64 s.scratch.heap_len ≠ 0 := by assumption
      exact Nat.pos_of_ne_zero fun h0 => hne (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hhl_le : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ s.core.cur_vars := by
      have h := (by assumption : ¬ s.core.cur_vars % 2 ^ 64 < s.scratch.heap_len % 2 ^ 64)
      rw [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h; omega
    have h0_hlt : (BitVec.ofNat 64 0).toNat < s.scratch.heap.length := by simp; omega
    have hnl_lt : (BitVec.ofNat 64 s.scratch.heap_len - 1).toNat < s.scratch.heap.length := by
      have : (BitVec.ofNat 64 s.scratch.heap_len - 1).toNat =
          (BitVec.ofNat 64 s.scratch.heap_len).toNat - 1 := by bv_omega
      omega
    c0_hsteps_nogrp
    let s_nl : FullState :=
      { s with scratch := { s.scratch with
          heap_len := (BitVec.ofNat 64 s.scratch.heap_len - 1#64).toNat } }
    have hlen_nl : s_nl.LengthsOk c :=
      fid_hlen_upd_hp_ps hlen _ _ _ hhl hpl
    refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s R (fun _ => True) trivial
      (fun s1 _ => s1.scratch.heap_len = (BitVec.ofNat 64 s.scratch.heap_len - 1#64).toNat ∧
        Full.FullProbeScratchPres s s1)
      (fun J1 s1 _ m1 hcore1 hs1 _ ⟨hhl1, hpr1⟩ hm1 => by
        dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs1 hm1
        have hhl1_ok : 0 < s.scratch.heap_len ∧ s.scratch.heap_len ≤ s.core.cur_vars →
            s1.scratch.heap_len = s.scratch.heap_len - 1 := fun h => by rw [hhl1]; exact hnlen_sub h
        have hhl1_arr := hs1.scratch_ok.heap_len_arr
        have hpl1_arr := hs1.scratch_ok.pos_len
        have h0_s1 : (BitVec.ofNat 64 0).toNat < s1.scratch.heap.length := by
          simp [hhl1_arr]; omega
        c0_hsteps_nogrp
        · refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R (fun _ => True) trivial
            (fun s2 _ => s2.scratch.heap_len = s1.scratch.heap_len ∧
              Full.FullProbeScratchPres s s2)
            (fun J2 s2 _ m2 hcore2 hs2 _ ⟨hhl2, hpr2⟩ hm2 => by
              dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                fullSafetySlice_safe] at hs2 hm2
              c0_hsteps_nogrp
              · exact hQ (0xFFFFFFFF#64, ()) s2 m2 (hcore1.trans hcore2) hs2
                  ⟨Or.inl rfl, fun h => by rw [hhl2]; exact hhl1_ok h, hpr2⟩ hm2
              · exact hQ _ s2 m2 (hcore1.trans hcore2) hs2
                  ⟨Or.inr (by
                    have h := (by assumption :
                      ¬ s.core.cur_vars % 2 ^ 64 ≤ (s.scratch.heap[0]'(by omega)).toNat)
                    rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h
                    have hlt : (s.scratch.heap[0]'(by omega)).toNat < s.core.cur_vars := by omega
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    exact hlt),
                    fun h => by rw [hhl2]; exact hhl1_ok h, hpr2⟩ hm2)
            (fun J2 hJ2 => by
              c0_hsteps_nogrp
              · let last_v := s.scratch.heap[(BitVec.ofNat 64 s.scratch.heap_len - 1).toNat]'hnl_lt
                let s1_dn : FullState :=
                  { s1 with scratch := { s1.scratch with
                      heap := s1.scratch.heap.set 0 last_v
                      pos := s1.scratch.pos.set last_v.toNat 0#32 } }
                have hm_dn : (FullMem c s1_dn ⋆ R) m := by
                  refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                  dsimp only [s1_dn, last_v]; congr 1
                refine wp_safety_slice_call (s := s1_dn) hDown (fun _ => True) trivial rfl ?_ hm_dn
                  fun _ s3 m3 hcore3 hs3 _ ⟨hhl3, hpr3⟩ hm3 => ?_
                · exact fid_hlen_upd_hp_ps hs1 _ _ _ (by simp [hhl1_arr]) (by simp [hpl1_arr])
                · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                    fullSafetySlice_safe] at hs3 hm3
                  have hpr_s3 : Full.FullProbeScratchPres s s3 :=
                    ⟨⟨hpr3.1.1.trans hpr1.1.1, hpr3.1.2.trans hpr1.1.2⟩,
                     hpr3.2.1.trans hpr1.2.1, hpr3.2.2.1.trans hpr1.2.2.1,
                     hpr3.2.2.2.1.trans hpr1.2.2.2.1, hpr3.2.2.2.2.1.trans hpr1.2.2.2.2.1,
                     hpr3.2.2.2.2.2.1.trans hpr1.2.2.2.2.2.1,
                     hpr3.2.2.2.2.2.2.1.trans hpr1.2.2.2.2.2.2.1,
                     hpr3.2.2.2.2.2.2.2.trans hpr1.2.2.2.2.2.2.2⟩
                  exact hJ2 s3 () m3 hm3 hcore3 hs3 ⟨hhl3, hpr_s3⟩
              · exact hJ2 s1 () m1 hm1 rfl hs1 ⟨rfl, hpr1⟩
              · exact hJ2 s1 () m1 hm1 rfl hs1 ⟨rfl, hpr1⟩))
      (fun J1 hJ1 => by
        c0_hsteps_nogrp
        · exact hJ1 { s_nl with scratch := { s_nl.scratch with pos := _ } } () _
            (by simpa only [s_nl, show (1 : BitVec 64) = 1#64 from rfl] using (by assumption : _))
            rfl (fid_hlen_upd_hp_ps hlen _ _ _ hhl (by simp [hpl]))
            ⟨rfl, fid_probePres_refl s⟩
        · exact hJ1 s_nl () _
            (by simpa only [s_nl, show (1 : BitVec 64) = 1#64 from rfl] using (by assumption : _))
            rfl hlen_nl ⟨rfl, fid_probePres_refl s⟩)

/-! ## 2. `full_next_dec_var_fid_wp` -/

/-- Canonical `Full.fullNextDecVarSpec` proof for `full_next_dec_var_fid_body`. -/
theorem full_next_dec_var_fid_wp (Γ : Env)
    (hPop : ∀ a m Q X, Full.fullHeapPopSpec a m Q X → Γ "full_heap_pop" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullNextDecVarSpec a m Q X → Func.wp Γ full_next_dec_var_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain hvl0 := hlen.core_ok.vals_len
  obtain hfl0 := hlen.core_ok.flags_len
  unfold Func.wp full_next_dec_var_fid_body
  c0_to_group
  refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s R (fun _ => True) trivial
    (fun s1 _ => s1.scratch.last_learned = s.scratch.last_learned ∧
      s1.scratch.extend_len = s.scratch.extend_len)
    (fun Jf s1 _ m1 hcore1 hs1 _ ⟨hll1, hel1⟩ hm1 => ?_) (fun Jf hJf => ?_)
  · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs1 hm1
    have heq1 := fullCoreState_agrees_with_scratch hcore1
    obtain hcv_le1 := hs1.core_ok.cur_vars_le
    obtain hfl1 := hs1.core_ok.flags_len
    obtain hvl1 := hs1.core_ok.vals_len
    c0_steps
    refine wp_loop_safety_slice (fullSafetySlice c) s1 R (fun _ => True) trivial
      (fun s2 ((v : BitVec 64), ()) => v.toNat ≤ s.core.cur_vars ∧
        s2.scratch.last_learned = s.scratch.last_learned ∧
        s2.scratch.extend_len = s.scratch.extend_len)
      (fun ((v : BitVec 64), ()) => s.core.cur_vars - v.toNat)
      (fun Jv hJv => ?_)
      (fun Jv s2 ((v : BitVec 64), ()) m2 hcore2 hs2 _ ⟨hvle, hll2, hel2⟩ hm2 hJv => ?_)
    · c0_steps; exact hJv s1 (0#64, ()) m1 hm1 rfl hs1 ⟨by simp, hll1, hel1⟩
    · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs2 hm2
      have heq2 := fullCoreState_agrees_with_scratch hcore2
      obtain hfl2 := hs2.core_ok.flags_len
      obtain hvl2 := hs2.core_ok.vals_len
      rw [Blocks.get_here]; dsimp only
      rw [wp_let_ult64_2]
      refine wp_jnz_of (fun hc_v => ?_) (fun _ => ?_)
      · simp only [Arg.val_var] at hc_v; c0_cond hc_v
        have hv_lt : v.toNat < s.core.cur_vars := by omega
        have hv_fl : v.toNat < s2.core.flags.length := by rw [hfl2]; omega
        have hv1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
        refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s2 R (fun _ => True) trivial
          (fun s3 _ => s3.scratch.last_learned = s.scratch.last_learned ∧
            s3.scratch.extend_len = s.scratch.extend_len)
          (fun Js s3 _ m3 hcore3 hs3 _ ⟨hll3, hel3⟩ hm3 => ?_) (fun Js hJs => ?_)
        · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
            fullSafetySlice_safe] at hs3 hm3
          c0_steps
          exact hJv s3 (v + 1, ()) m3 hm3 (by dsimp only; rw [hv1]; omega) hcore3 hs3
            ⟨by rw [hv1]; omega, hll3, hel3⟩
        · have hv2_lt' : (2 * v.toNat % 2 ^ 64) < s2.core.vals.length := by
            rw [hvl2, Nat.mod_eq_of_lt (by omega)]; omega
          repeat (first
            | rw [wp_let_sext32_64_2] | rw [wp_let_mul64_2]
            | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
          dsimp only
          refine wp_load_of (FullArenaTactics.c0_load_full_flags hv_fl hm2) ?_
          rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
          refine wp_jnz_of (fun hc_fl => ?_) (fun _ => ?_)
          · simp only [Arg.val_var, Arg.val_imm, bne_iff_ne, ne_eq] at hc_fl
            repeat (first
              | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
            dsimp only
            refine wp_load_of (FullArenaTactics.c0_load_full_vals (s := s2) ?_ hm2) ?_
            · simp only [BitVec.toNat_shiftLeft, Arg.val_var, Arg.val_imm]
              rw [show (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 from rfl]
              simp only [Nat.shiftLeft_eq, Nat.pow_one]
              rw [Nat.mul_comm]; exact hv2_lt'
            · repeat (first
                | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_eq32_2])
              dsimp only
              refine wp_jnz_of (fun hc_val => ?_) (fun _ => ?_)
              · simp only [Arg.val_var] at hc_val; c0_cond hc_val
                have hval_v : s2.core.vals[2 * v.toNat % 2 ^ 64]'(by
                    rw [hvl2, Nat.mod_eq_of_lt (by omega)]; omega) = 0#8 :=
                  fid_sext32_eq_zero hc_val
                simp only [heq2, heq1, Nat.mod_eq_of_lt (by omega : 2 * v.toNat < 2 ^ 64)]
                  at hval_v
                exact hQ (v, ()) s2 m2 (hcore1.trans hcore2) hs2
                  ⟨⟨hll2, hel2⟩, Or.inr ⟨hv_lt,
                    by rw [List.getElem?_eq_getElem (by omega : 2 * v.toNat < _)]
                       simpa using hval_v⟩⟩ hm2
              · exact hJs s2 () m2 hm2 rfl hs2 ⟨hll2, hel2⟩
          · exact hJs s2 () m2 hm2 rfl hs2 ⟨hll2, hel2⟩
      · exact hQ (0xFFFFFFFFFFFFFFFF#64, ()) s2 m2 (hcore1.trans hcore2) hs2
          ⟨⟨hll2, hel2⟩, Or.inl rfl⟩ hm2
  · c0_split
    · clear hc
      c0_to_group
      refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) s R (fun _ => True) trivial
        (fun s1 _ => s1.scratch.last_learned = s.scratch.last_learned ∧
          s1.scratch.extend_len = s.scratch.extend_len)
        (fun Js s1 _ m1 hcore1 hs1 _ ⟨hll1, hel1⟩ hm1 => ?_) (fun Js hJs => ?_)
      · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
          fullSafetySlice_safe] at hs1 hm1
        c0_steps; exact hJf s1 () m1 hm1 hcore1 hs1 ⟨hll1, hel1⟩
      · let s0 : FullState :=
          { s with scratch := { s.scratch with heap_len := s.scratch.heap_len % 2 ^ 64 } }
        have hm0 : (FullMem c s0 ⋆ R) m := by rwa [FullMem_with_heap_len_mod]
        refine wp_loop_safety_slice_state (ts := [i64]) (fullSafetySlice c) s0 R
          (fun _ => True) trivial
          (fun s1 (hl_v, ()) => hl_v = BitVec.ofNat 64 s1.scratch.heap_len ∧
            s1.scratch.heap_len < 2 ^ 64 ∧
            s1.scratch.last_learned = s.scratch.last_learned ∧
            s1.scratch.extend_len = s.scratch.extend_len)
          (fun s1 _ => s1.scratch.heap_len)
          (fun Jh hJh => ?_)
          (fun Jh s1 (hl_v, ()) m1 hcore1 hs1 _ ⟨hhl_v, hhl_lt1, hll1, hel1⟩ hm1 hJh => ?_)
        · c0_steps
          have hmod_bv : BitVec.ofNat 64 s.scratch.heap_len =
              BitVec.ofNat 64 (s.scratch.heap_len % 2 ^ 64) := by
            apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
          exact hJh s0 (BitVec.ofNat 64 s.scratch.heap_len, ()) m hm0 rfl
            ⟨hlen.core_ok, { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩
            ⟨hmod_bv, Nat.mod_lt _ (by decide), rfl, rfl⟩
        · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
            fullSafetySlice_safe] at hs1 hm1
          subst hhl_v
          have heq1 := fullCoreState_agrees_with_scratch hcore1
          obtain hhl1 := hs1.scratch_ok.heap_len_arr
          obtain hfl1 := hs1.core_ok.flags_len
          obtain hvl1 := hs1.core_ok.vals_len
          rw [Blocks.get_here]; try dsimp only
          rw [wp_let_ugt64_2]; dsimp only
          refine wp_jnz_of (fun hc_gt0 => ?_) (fun _ => ?_)
          · simp only [Arg.val_var] at hc_gt0; c0_cond hc_gt0
            have hpos1 : 0 < s1.scratch.heap_len := by
              rw [Nat.mod_eq_of_lt hhl_lt1] at hc_gt0; exact hc_gt0
            rw [wp_let_ule64_2]; dsimp only
            refine wp_jnz_of (fun hc_lecv => ?_) (fun _ => ?_)
            · simp only [Arg.val_var] at hc_lecv; c0_cond hc_lecv
              have hle1 : s1.scratch.heap_len ≤ s.core.cur_vars := by
                rw [Nat.mod_eq_of_lt hhl_lt1,
                  Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_lecv
                exact hc_lecv
              let top := s1.scratch.heap[0]'(by omega)
              have hhp0 : loadVal m1 i32
                  (c.pHeap + (BitVec.signExtend 64 (0 : BitVec 32)) * 4) = some top := by
                have hraw := FullArenaTactics.c0_load_full_heap (s := s1)
                  (i := BitVec.signExtend 64 0)
                  (by rw [show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl]; omega)
                  hm1
                simpa only [show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl] using
                  hraw
              rw [wp_let_sext32_64_2, wp_let_mul64_2, wp_let_add64_2]; dsimp only
              refine wp_load_of hhp0 ?_
              rw [wp_let_zext32_2, wp_let_uge64_2]; dsimp only
              refine wp_jnz_of (fun _ => ?_) (fun hc_tlt => ?_)
              · exact hJs s1 (BitVec.ofNat 64 s1.scratch.heap_len, ()) m1 hm1 hcore1 hs1
                  ⟨hll1, hel1⟩
              · simp only [Arg.val_var] at hc_tlt
                have htop_lt : top.toNat < s.core.cur_vars := by
                  have h1 :
                      ¬ (BitVec.ofNat 64 s.core.cur_vars).toNat ≤ (top.setWidth 64).toNat := by
                    simpa [BitVec.ule] using hc_tlt
                  rw [zext_toNat _ (by decide), BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1
                  omega
                have htop2_lt : ((top.setWidth 64) <<< (1 : Nat)).toNat < s1.core.vals.length := by
                  rw [hvl1, BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]
                  simp [Nat.shiftLeft_eq]; omega
                refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R
                  (fun _ => True) trivial
                  (fun s2 _ => s2.scratch.heap_len = s1.scratch.heap_len ∧
                    s2.scratch.last_learned = s.scratch.last_learned ∧
                    s2.scratch.extend_len = s.scratch.extend_len)
                  (fun Jpop s2 _ m2 hcore2 hs2 _ ⟨hhl_eq2, hll2, hel2⟩ hm2 => ?_)
                  (fun Jpop hJpop => ?_)
                · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                    fullSafetySlice_safe] at hs2 hm2
                  have heq2 := fullCoreState_agrees_with_scratch hcore2
                  c0_steps
                  c0_call hPop
                  refine ⟨c, s2, R, rfl, hs2, hm2, ?_⟩
                  intro _ s3 m3 hcore3 hs3 ⟨_, hdec, hpres3⟩ hm3
                  have hs3_eq := hdec ⟨by rw [hhl_eq2]; exact hpos1,
                    by rw [hhl_eq2, heq2, heq1]; exact hle1⟩
                  dsimp only [fullSafetySlice_mem] at hm3
                  refine wp_load_of (FullArenaTactics.load_full_heap_len hm3) ?_
                  exact hJh s3 (BitVec.ofNat 64 s3.scratch.heap_len, ()) m3 hm3
                    (by rw [hs3_eq, hhl_eq2]; omega) (hcore2.trans hcore3) hs3
                    ⟨rfl, by rw [hs3_eq, hhl_eq2]; omega,
                      hpres3.1.1.trans hll2, hpres3.1.2.trans hel2⟩
                · repeat (first
                    | rw [wp_let_sext32_64_2] | rw [wp_let_zext32_2]
                    | rw [wp_let_mul64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                  dsimp only
                  refine wp_load_of (FullArenaTactics.c0_load_full_flags
                    (s := s1) (by
                      simp only [Arg.val_var]; rw [hfl1, zext_toNat _ (by decide)]; omega) hm1) ?_
                  rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
                  refine wp_jnz_of (fun hc_flt => ?_) (fun _ => ?_)
                  · repeat (first
                      | rw [wp_let_sext32_64_2] | rw [wp_let_zext32_2]
                      | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                    dsimp only
                    refine wp_load_of (FullArenaTactics.c0_load_full_vals
                      (s := s1) htop2_lt hm1) ?_
                    repeat (first
                      | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_eq32_2])
                    dsimp only
                    refine wp_jnz_of (fun hc_valt => ?_) (fun _ => ?_)
                    · simp only [Arg.val_var] at hc_valt; c0_cond hc_valt
                      have hval_t : s1.core.vals[((top.setWidth 64) <<< (1 : Nat)).toNat]'(by
                          omega) = 0#8 := fid_sext32_eq_zero hc_valt
                      have h2t : ((top.setWidth 64) <<< (1 : Nat)).toNat = 2 * top.toNat := by
                        rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]
                        simp [Nat.shiftLeft_eq]; omega
                      have hzt : (top.setWidth 64).toNat = top.toNat := zext_toNat _ (by decide)
                      simp only [heq1] at hval_t
                      rw [wp_let_zext32_2]; dsimp only
                      exact hQ (top.setWidth 64, ()) s1 m1 hcore1 hs1 ⟨⟨hll1, hel1⟩, Or.inr ⟨by
                        rw [hzt]; exact htop_lt,
                        by rw [hzt, List.getElem?_eq_getElem (by omega : 2 * top.toNat < _)]
                           simpa [h2t] using hval_t⟩⟩ hm1
                    · exact hJpop s1 () m1 hm1 rfl hs1 ⟨rfl, hll1, hel1⟩
                  · exact hJpop s1 () m1 hm1 rfl hs1 ⟨rfl, hll1, hel1⟩
            · exact hJs s1 (BitVec.ofNat 64 s1.scratch.heap_len, ()) m1 hm1 hcore1 hs1 ⟨hll1, hel1⟩
          · exact hJs s1 (BitVec.ofNat 64 s1.scratch.heap_len, ()) m1 hm1 hcore1 hs1 ⟨hll1, hel1⟩
    · clear hc
      c0_steps
      refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s R
        (fun _ => True) trivial
        (fun s1 ((cur : BitVec 64), (steps : BitVec 64), ()) =>
          steps.toNat ≤ s.core.cur_vars ∧
          s1.scratch.last_learned = s.scratch.last_learned ∧
          s1.scratch.extend_len = s.scratch.extend_len)
        (fun (_, (steps : BitVec 64), ()) => s.core.cur_vars - steps.toNat)
        (fun J1 hJ1 => ?_)
        (fun J1 s1 ((cur : BitVec 64), (steps : BitVec 64), ()) m1 hcore1 hs1 _
            ⟨hst1, hll1, hel1⟩ hm1 hJ1 => ?_)
      · c0_steps; exact hJ1 s (s.scratch.q_search_idx, 0#64, ()) m hm rfl hlen ⟨by simp, rfl, rfl⟩
      · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
          fullSafetySlice_safe] at hs1 hm1
        have heq1 := fullCoreState_agrees_with_scratch hcore1
        obtain hfl1 := hs1.core_ok.flags_len
        obtain hvl1 := hs1.core_ok.vals_len
        obtain hqpl1 := hs1.scratch_ok.q_prev_len
        obtain hqsl1 := hs1.scratch_ok.q_stamp_len
        rw [Blocks.get_here]; dsimp only
        refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R (fun _ => True) trivial
          (fun s2 _ => s2.scratch.last_learned = s.scratch.last_learned ∧
            s2.scratch.extend_len = s.scratch.extend_len)
          (fun J2w s2 _ m2 hcore2 hs2 _ ⟨hll2, hel2⟩ hm2 => ?_) (fun J2w hJ2w => ?_)
        · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
            fullSafetySlice_safe] at hs2 hm2
          have heq2 := fullCoreState_agrees_with_scratch hcore2
          obtain hfl2 := hs2.core_ok.flags_len
          obtain hvl2 := hs2.core_ok.vals_len
          obtain hqpl2 := hs2.scratch_ok.q_prev_len
          obtain hqsl2 := hs2.scratch_ok.q_stamp_len
          rw [Blocks.get_here]; try dsimp only
          rw [wp_let_add64_2]
          refine wp_load_of (FullArenaTactics.load_full_q_last hm2) ?_
          refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s2 R
            (fun _ => True) trivial
            (fun s3 ((cur2 : BitVec 64), (steps2 : BitVec 64), ()) =>
              steps2.toNat ≤ s.core.cur_vars ∧
              s3.scratch.last_learned = s.scratch.last_learned ∧
              s3.scratch.extend_len = s.scratch.extend_len)
            (fun (_, (steps2 : BitVec 64), ()) => s.core.cur_vars - steps2.toNat)
            (fun J2 hJ2 => ?_)
            (fun J2 s3 ((cur2 : BitVec 64), (steps2 : BitVec 64), ()) m3 hcore3 hs3 _
                ⟨hst3, hll3, hel3⟩ hm3 hJ2 => ?_)
          · c0_steps
            exact hJ2 s2 (s2.scratch.q_last, 0#64, ()) m2 hm2 rfl hs2 ⟨by simp, hll2, hel2⟩
          · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
              fullSafetySlice_safe] at hs3 hm3
            have heq3 := fullCoreState_agrees_with_scratch hcore3
            obtain hfl3 := hs3.core_ok.flags_len
            obtain hvl3 := hs3.core_ok.vals_len
            obtain hqpl3 := hs3.scratch_ok.q_prev_len
            obtain hqsl3 := hs3.scratch_ok.q_stamp_len
            rw [Blocks.get_here]; dsimp only
            rw [wp_let_ult64_2]; dsimp only
            refine wp_jnz_of (fun hc_c2 => ?_) (fun _ => ?_)
            · simp only [Arg.val_var] at hc_c2; c0_cond hc_c2
              have hcur2_lt : cur2.toNat < s.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_c2
                exact hc_c2
              rw [wp_let_ult64_2]; dsimp only
              refine wp_jnz_of (fun hc_st2 => ?_) (fun _ => ?_)
              · simp only [Arg.val_var] at hc_st2; c0_cond hc_st2
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_st2
                have hcur22_lt : (cur2 <<< (1 : Nat)).toNat < s3.core.vals.length := by
                  rw [hvl3, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                have hst2' : (steps2 + 1).toNat = steps2.toNat + 1 := by bv_omega
                refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s3 R
                  (fun _ => True) trivial
                  (fun s4 _ => s4.scratch.last_learned = s.scratch.last_learned ∧
                    s4.scratch.extend_len = s.scratch.extend_len)
                  (fun Jnxt s4 _ m4 hcore4 hs4 _ ⟨hll4, hel4⟩ hm4 => ?_) (fun Jnxt hJnxt => ?_)
                · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                    fullSafetySlice_safe] at hs4 hm4
                  obtain hqpl4 := hs4.scratch_ok.q_prev_len
                  c0_steps
                  exact hJ2 s4 ((s4.scratch.q_prev[cur2.toNat]'(by omega)).setWidth 64,
                    steps2 + 1, ()) m4 hm4 (by dsimp only; rw [hst2']; omega) hcore4 hs4
                    ⟨by rw [hst2']; omega, hll4, hel4⟩
                · repeat (first
                    | rw [wp_let_sext32_64_2] | rw [wp_let_mul64_2]
                    | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                  dsimp only
                  refine wp_load_of (FullArenaTactics.c0_load_full_flags
                    (s := s3) (by simp only [Arg.val_var]; rw [hfl3]; omega) hm3) ?_
                  rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
                  refine wp_jnz_of (fun hc_fl2 => ?_) (fun _ => ?_)
                  · repeat (first
                      | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                    dsimp only
                    refine wp_load_of (FullArenaTactics.c0_load_full_vals
                      (s := s3) hcur22_lt hm3) ?_
                    repeat (first
                      | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_eq32_2])
                    dsimp only
                    refine wp_jnz_of (fun hc_val2 => ?_) (fun _ => ?_)
                    · simp only [Arg.val_var] at hc_val2; c0_cond hc_val2
                      have hval_c2 : s3.core.vals[(cur2 <<< (1 : Nat)).toNat]'(by omega) =
                          0#8 := fid_sext32_eq_zero hc_val2
                      have h2c : (cur2 <<< (1 : Nat)).toNat = 2 * cur2.toNat := by
                        rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                      let qss2 := (s3.scratch.q_stamp[cur2.toNat]'(by rw [hqsl3]; omega)).setWidth
                        64
                      let s3' : FullState :=
                        { s3 with scratch :=
                          { s3.scratch with q_search_idx := cur2, q_search_stamp := qss2 } }
                      rw [wp_let_add64_2]; dsimp only
                      refine wp_load_of (FullArenaTactics.load_full_q_stamp_ptr hm3) ?_
                      rw [wp_let_add64_2]; dsimp only
                      refine wp_store_sep (FullArenaTactics.store_full_q_search_idx cur2 hm3) ?_
                      intro m3a hm3a
                      repeat (first | rw [wp_let_mul64_2] | rw [wp_let_add64_2])
                      dsimp only
                      refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
                        (s := _) (by simp only [Arg.val_var]; rw [hqsl3]; omega) hm3a) ?_
                      repeat (first | rw [wp_let_zext32_2] | rw [wp_let_add64_2])
                      dsimp only
                      refine wp_store_sep (FullArenaTactics.store_full_q_search_stamp _ hm3a) ?_
                      intro m3b hm3b
                      simp only [heq3, heq2, heq1] at hval_c2
                      exact hQ (cur2, ()) s3' m3b (hcore1.trans (hcore2.trans hcore3))
                        ⟨hs3.core_ok,
                          { hs3.scratch_ok with walk_vals_len := hs3.scratch_ok.walk_vals_len }⟩
                        ⟨⟨hll3, hel3⟩, Or.inr ⟨hcur2_lt,
                          by rw [List.getElem?_eq_getElem (by omega : 2 * cur2.toNat < _)]
                             simpa [h2c] using hval_c2⟩⟩ hm3b
                    · exact hJnxt s3 () m3 hm3 rfl hs3 ⟨hll3, hel3⟩
                  · exact hJnxt s3 () m3 hm3 rfl hs3 ⟨hll3, hel3⟩
              · exact hJf s3 () m3 hm3 (hcore1.trans (hcore2.trans hcore3)) hs3 ⟨hll3, hel3⟩
            · exact hJf s3 () m3 hm3 (hcore1.trans (hcore2.trans hcore3)) hs3 ⟨hll3, hel3⟩
        · rw [wp_let_ult64_2]; dsimp only
          refine wp_jnz_of (fun hc_c1 => ?_) (fun _ => ?_)
          · simp only [Arg.val_var] at hc_c1; c0_cond hc_c1
            have hcur_lt : cur.toNat < s.core.cur_vars := by
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_c1
              exact hc_c1
            rw [wp_let_ult64_2]; dsimp only
            refine wp_jnz_of (fun hc_st1 => ?_) (fun _ => ?_)
            · simp only [Arg.val_var] at hc_st1; c0_cond hc_st1
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_st1
              have hcur2_lt : (cur <<< (1 : Nat)).toNat < s1.core.vals.length := by
                rw [hvl1, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
              have hst1' : (steps + 1).toNat = steps.toNat + 1 := by bv_omega
              refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R
                (fun _ => True) trivial
                (fun s2 _ => s2.scratch.last_learned = s.scratch.last_learned ∧
                  s2.scratch.extend_len = s.scratch.extend_len)
                (fun Jnxt s2 _ m2 hcore2 hs2 _ ⟨hll2, hel2⟩ hm2 => ?_) (fun Jnxt hJnxt => ?_)
              · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                  fullSafetySlice_safe] at hs2 hm2
                obtain hqpl2 := hs2.scratch_ok.q_prev_len
                c0_steps
                exact hJ1 s2 ((s2.scratch.q_prev[cur.toNat]'(by omega)).setWidth 64,
                  steps + 1, ()) m2 hm2 (by dsimp only; rw [hst1']; omega) hcore2 hs2
                  ⟨by rw [hst1']; omega, hll2, hel2⟩
              · repeat (first
                  | rw [wp_let_sext32_64_2] | rw [wp_let_mul64_2]
                  | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                dsimp only
                refine wp_load_of (FullArenaTactics.c0_load_full_flags
                  (s := s1) (by simp only [Arg.val_var]; rw [hfl1]; omega) hm1) ?_
                rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
                refine wp_jnz_of (fun hc_fl1 => ?_) (fun _ => ?_)
                · repeat (first
                    | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                  dsimp only
                  refine wp_load_of (FullArenaTactics.c0_load_full_vals
                    (s := s1) hcur2_lt hm1) ?_
                  repeat (first
                    | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_eq32_2])
                  dsimp only
                  refine wp_jnz_of (fun hc_val1 => ?_) (fun _ => ?_)
                  · simp only [Arg.val_var] at hc_val1; c0_cond hc_val1
                    have hval_c1 : s1.core.vals[(cur <<< (1 : Nat)).toNat]'(by omega) =
                        0#8 := fid_sext32_eq_zero hc_val1
                    have h2c : (cur <<< (1 : Nat)).toNat = 2 * cur.toNat := by
                      rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                    let qss1 := (s1.scratch.q_stamp[cur.toNat]'(by rw [hqsl1]; omega)).setWidth 64
                    let s1' : FullState :=
                      { s1 with scratch :=
                        { s1.scratch with q_search_idx := cur, q_search_stamp := qss1 } }
                    rw [wp_let_add64_2]; dsimp only
                    refine wp_load_of (FullArenaTactics.load_full_q_stamp_ptr hm1) ?_
                    rw [wp_let_add64_2]; dsimp only
                    refine wp_store_sep (FullArenaTactics.store_full_q_search_idx cur hm1) ?_
                    intro m1a hm1a
                    repeat (first | rw [wp_let_mul64_2] | rw [wp_let_add64_2])
                    dsimp only
                    refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
                      (s := _) (by simp only [Arg.val_var]; rw [hqsl1]; omega) hm1a) ?_
                    repeat (first | rw [wp_let_zext32_2] | rw [wp_let_add64_2])
                    dsimp only
                    refine wp_store_sep (FullArenaTactics.store_full_q_search_stamp _ hm1a) ?_
                    intro m1b hm1b
                    simp only [heq1] at hval_c1
                    exact hQ (cur, ()) s1' m1b hcore1
                      ⟨hs1.core_ok,
                        { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len }⟩
                      ⟨⟨hll1, hel1⟩, Or.inr ⟨hcur_lt,
                        by rw [List.getElem?_eq_getElem (by omega : 2 * cur.toNat < _)]
                           simpa [h2c] using hval_c1⟩⟩ hm1b
                  · exact hJnxt s1 () m1 hm1 rfl hs1 ⟨hll1, hel1⟩
                · exact hJnxt s1 () m1 hm1 rfl hs1 ⟨hll1, hel1⟩
            · exact hJ2w s1 () m1 hm1 rfl hs1 ⟨hll1, hel1⟩
          · exact hJ2w s1 () m1 hm1 rfl hs1 ⟨hll1, hel1⟩

/-! ## 3. `m6_hdr_decide_fid_fast_wp` -/

/-- Canonical `FullM6Hdr.m6HdrDecideSpec` proof for `m6_hdr_decide_fid_fast_body`, proving that
the inline steady-state check (`e[M6W_MAGIC] == M6_HDR_MAGIC && (st >> 63) != 0`) preserves
`M6HdrExtInitOk` without calling `m6_hdr_dr_init`. -/
theorem m6_hdr_decide_fid_fast_wp (Γ : Env)
    (hDecide : ∀ a m Q X, m7DecideSpec a m Q X →
      Γ "full_decide_m7" [i64] [i64] a m Q X)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X →
      Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDecideSpec a m Q X → Func.wp Γ m6_hdr_decide_fid_fast_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩ := m6HdrDecideSpec_elim hs
  have hcfg := hinv.cfgOk
  have hext := hinv.extOk
  have hcore0 := hinv.coreInv
  unfold Func.wp m6_hdr_decide_fid_fast_body
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_call_of_spec _ _ (hDecide _ _ _ _ ?_)
  refine m7DecideSpec_of hcore0 ((fullM6HdrMem_iff ..).mp hm)
    fun r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m1
      hinv1 hpres1 hdom h0 h1 hm1 => ?_
  let s1 : FullState :=
    { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', frame_trail := ftrl',
                            frame_dec := fdec', trail_end := te', cur_level := cl',
                            unassigned := unass', unflushed := unfl' }
      scratch := sc' }
  c0_hsteps_nogrp
  · exact hQ 0#64 vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext m1
      (FullM6HdrCoreInv.mk_inv hcfg hext hinv1) hpres1 (Or.inl rfl)
      (fun _ => h0 hc) (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm1)
  · have hr1 : r = 1#64 := hdom.resolve_left hc
    have hl1 : ext.length = 288 := hext.len
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (st4, ()) m4 => ∃ ext4 : List (BitVec 64),
        M6HdrExtInitOk ext4 ∧
        (M6HdrExtInitOk ext → M6ExtW2aPres ext ext4) ∧
        ext4[1]? = some st4 ∧
        (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext4 ⋆ R)) m4)
      (fun _ ⟨st4, ⟨⟩⟩ m4 ⟨ext4, hinit4, hw4, hst4_eq, hm4⟩ => by
        have hl4 : ext4.length = 288 := hinit4.toOk.len
        let mask56 : BitVec 64 := (1#64 <<< 56) - 1#64
        let hi4 := st4 &&& ~~~mask56
        let decs4 := st4 &&& mask56
        let ext4' := ext4.set 1 (hi4 ||| (decs4 + 1#64))
        c0_hsteps
        · refine hQ 1#64 vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc'
            ext4' _ (FullM6HdrCoreInv.mk_inv hcfg (hinit4.set_pos _ (by decide)).toOk hinv1)
            hpres1 (Or.inr rfl) (fun h => by cases h)
            (fun _ => ⟨(h1 hr1).1, (h1 hr1).2.1, hinit4.set_pos _ (by decide),
              fun hi => (hw4 hi).trans (M6ExtW2aPres.set_w2b _ (by decide) (by decide))⟩)
            ((fullM6HdrMem_iff ..).mpr ?_)
          simpa [ext4', hi4, decs4, mask56] using (by assumption : _)
        · exact hQ 1#64 vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc'
            ext4 m4 (FullM6HdrCoreInv.mk_inv hcfg hinit4.toOk hinv1) hpres1 (Or.inr rfl)
            (fun h => by cases h) (fun _ => ⟨(h1 hr1).1, (h1 hr1).2.1, hinit4, hw4⟩)
            ((fullM6HdrMem_iff ..).mpr hm4)) ?_
    intro Jst hJst
    refine wp_join_group (ts := [])
      (fun _ m_in => (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m_in)
      (fun _ ⟨⟩ m_in hm_in => by
        c0_hsteps_nogrp
        refine LeanQbe.T.wp_call_of_spec _ _ (hDrInit _ _ _ _ ?_)
        refine m6HdrDrMutSpec_of hcfg hext hinv1.lengths ((fullM6HdrMem_iff ..).mpr hm_in)
          fun ext4 m4 hinit4 hw4 hm4 => ?_
        have hl4 : ext4.length = 288 := hinit4.toOk.len
        rw [fullM6HdrMem_iff] at hm4
        c0_hsteps
        exact hJst (ext4[1]'(by omega), ()) m4
          ⟨ext4, hinit4, hw4, List.getElem?_eq_getElem (by omega), hm4⟩) ?_
    intro Jinit hJinit
    c0_hsteps_nogrp
    · exact hJinit () m1 hm1
    · exact hJinit () m1 hm1
    · have hmag_eq : ext[0]'(by omega) = fullM6HdrMagic := by
        simpa [fullM6HdrMagic] using (by assumption : _)
      have hinit1 : M6HdrExtInitOk ext :=
        ⟨hext, by rw [List.getElem?_eq_getElem (by omega), hmag_eq]⟩
      exact hJst (ext[1]'(by omega), ()) m1
        ⟨ext, hinit1, fun _ => M6ExtW2aPres.refl ext,
          List.getElem?_eq_getElem (by omega), hm1⟩

/-! ## 4. Linear Delayed-Watch Flush (`fidPropFlushDelSpec` & `full_prop_flush_del_fid_wp`) -/

/-- Unified contract for `full_prop_flush_del_fid(h, di)`: flushes `del[0 ..< 3 * dlen)` via
hoisted fast-path watch appends + cold `full_watch_push`, preserving `LengthsOk`,
`WatchStackLayout`, `WatchesInv` (post-scan), and `SplitWatchesInv` with `off'` rebase
(mid-scan overflow), while leaving all non-watch header fields (`trail_end`, `fuel`, `propagated`,
`unassigned`, `unflushed`, `search_ticks`, `delayed`) untouched. -/
def fidPropFlushDelSpec : Spec [i64, i64] [.bool] :=
  fun (h, di, ()) m Q _ =>
    ∃ (c : FullCfg) (F_cur : List (List Nat)) (st : FullState) (R : Mem 64 → Prop)
      (dlen skip_lit : Nat),
      h = c.hdr ∧ st.LengthsOk c ∧ WatchStackLayout st.core ∧
      di.toNat = 3 * dlen ∧ dlen ≤ c.delayed_cap ∧
      DelayedWatchesOk st.core st.scratch.delayed dlen skip_lit ∧
      (FullMem c st ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wu' wsort' m',
        let st' : FullState :=
          { st with
            core := { st.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
            scratch := { st.scratch with wsort := wsort' } }
        st'.LengthsOk c → WatchStackLayout st'.core →
        (WatchesInv F_cur st.core → WatchesInv F_cur st'.core) →
        (skip_lit < 2 * st.core.cur_vars →
          ∀ off q p end_v, SplitWatchesInv F_cur st.core skip_lit off q p end_v →
            let off' := fullWatchOffCore st'.core skip_lit
            SplitWatchesInv F_cur st'.core skip_lit off'
              (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) →
        (FullMem c st' ⋆ R) m' → Q (ok, ()) m'

theorem fidPropFlushDelSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : fidPropFlushDelSpec xs m Q X) : fidPropFlushDelSpec xs m Q X' := h

private def fidFlushDisk (wl_d : Nat) (wu_d : BitVec 64) (st : FullState) : FullState :=
  { st with core := { st.core with wlen := wl_d, wusable := wu_d } }

private theorem fid_repl_empty_layout {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c) {lit w0 cref : BitVec 32}
    (hlit : lit.toNat < 2 * k.cur_vars)
    (hw_pos : 1 ≤ k.wlen)
    (hrsz0 : fullWatchSizeCore k lit.toNat = 0)
    (hfit2 : k.wlen + 2 ≤ c.wcap)
    (hw0_f : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000) :
    let wend := k.wlen
    let k' : FullCoreState :=
      { k with
        wstk := (k.wstk.set wend w0).set (wend + 1) cref
        wvec := (k.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 wend)).set
          (2 * lit.toNat + 1) 2#32
        wlen := wend + 2 }
    k'.LengthsOk c ∧ WatchStackLayout k' ∧
    (∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l) ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?) ∧
    fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
    (∀ j < fullWatchSizeCore k lit.toNat,
      k'.wstk[fullWatchOffCore k' lit.toNat + j]? =
        k.wstk[fullWatchOffCore k lit.toNat + j]?) ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some cref := by
  intro wend k'
  have hwc := c.hwcap; have hmaxv := c.hmaxv; unfold dimacsBound at hwc hmaxv
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len; have hws := hlen.wstk_len_arr
  have hwend_32 : wend < 2 ^ 32 := by dsimp [wend]; omega
  have h2l_lt : 2 * lit.toNat < k.wvec.length := by rw [hwv]; omega
  have h2l1_lt : 2 * lit.toNat + 1 < k.wvec.length := by rw [hwv]; omega
  have hw0_lt : wend < k.wstk.length := by rw [hws]; dsimp [wend]; omega
  have hw1_lt : wend + 1 < k.wstk.length := by rw [hws]; dsimp [wend]; omega
  have hoff_lit : fullWatchOffCore k' lit.toNat = wend := by
    unfold fullWatchOffCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h2l_lt, Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwend_32]
  have hsz_lit : fullWatchSizeCore k' lit.toNat = 2 := by
    unfold fullWatchSizeCore; dsimp [k']
    rw [List.getElem?_set_self (by rw [List.length_set]; exact h2l1_lt), Option.getD_some]; rfl
  have hoff_ne : ∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l := by
    intro l hne; unfold fullWatchOffCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hsz_ne : ∀ l, l ≠ lit.toNat → fullWatchSizeCore k' l = fullWatchSizeCore k l := by
    intro l hne; unfold fullWatchSizeCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hwstk_ne : ∀ j < wend, k'.wstk[j]? = k.wstk[j]? := by
    intro j hj; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hlen' : k'.LengthsOk c :=
    { hlen with
      wstk_len_arr := by simp [k', hws]
      wvec_len := by simp [k', hwv]
      wlen_le := by dsimp [k', wend]; exact hfit2 }
  have hlay' : WatchStackLayout k' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl
      by_cases hll : l = lit.toNat
      · subst hll; rw [hoff_lit, hsz_lit]; dsimp [k']; omega
      · rw [hoff_ne l hll, hsz_ne l hll]
        exact Nat.le_trans (hlay.bounds l hl) (by dsimp [k']; omega)
    · intro l hl hpos
      by_cases hll : l = lit.toNat
      · subst hll; rw [hoff_lit]; exact hw_pos
      · rw [hoff_ne l hll]; rw [hsz_ne l hll] at hpos; exact hlay.pos_off l hl hpos
    · intro l1 l2 h1 h2 hne hp1 hp2
      by_cases hl1 : l1 = lit.toNat
      · subst hl1; have hl2 : l2 ≠ lit.toNat := hne.symm
        rw [hsz_ne l2 hl2] at hp2 ⊢; rw [hoff_lit, hoff_ne l2 hl2]
        exact Or.inr (hlay.bounds l2 h2)
      · by_cases hl2 : l2 = lit.toNat
        · subst hl2; rw [hsz_ne l1 hl1] at hp1 ⊢; rw [hoff_ne l1 hl1, hoff_lit]
          exact Or.inl (hlay.bounds l1 h1)
        · rw [hsz_ne l1 hl1] at hp1 ⊢; rw [hsz_ne l2 hl2] at hp2 ⊢
          rw [hoff_ne l1 hl1, hoff_ne l2 hl2]; exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
    · intro l hl idx hidx
      by_cases hll : l = lit.toNat
      · subst hll; rw [hsz_lit] at hidx; rw [hoff_lit]
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_of_lt_of_eq hidx rfl) with h0 | rfl
        · have hi0 : idx = 0 := by omega
          subst hi0; dsimp [k']
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
          intro heq; have h := Option.some.inj heq
          rw [h] at hw0_f; exact absurd hw0_f (by decide)
        · dsimp [k']
          rw [List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]
          intro heq; have h := Option.some.inj heq
          rw [h] at hcr_lt; revert hcr_lt; decide
      · rw [hsz_ne l hll] at hidx; rw [hoff_ne l hll]
        have hb := hlay.bounds l hl
        rw [hwstk_ne (fullWatchOffCore k l + idx) (by omega)]
        exact hlay.no_sentinel l hl idx hidx
  refine ⟨hlen', hlay', hoff_ne, ?_, by rw [hsz_lit, hrsz0], fun j hj => by omega, ?_, ?_⟩
  · intro l hl hne
    refine ⟨hsz_ne l hne, fun j hj => ?_⟩
    rw [hoff_ne l hne]
    exact hwstk_ne _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (hlay.bounds l hl))
  · rw [hoff_lit, hrsz0, Nat.add_zero]
    dsimp [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
  · rw [hoff_lit, hrsz0, Nat.add_zero]
    dsimp [k']; rw [List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]

/-- Proof of hoisted `full_prop_flush_del_fid_body` against `fidPropFlushDelSpec`. -/
theorem full_prop_flush_del_fid_wp (Γ : Env)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fidPropFlushDelSpec a m Q X → Func.wp Γ full_prop_flush_del_fid_body a m Q X := by
  rintro ⟨h, di, ⟨⟩⟩ m0 Q X
    ⟨c, F_cur, st0, R, dlen, skip_lit, rfl, hlen0, hlay0, hdi_eq, hdlen_le, hdel0, hm0, hQ⟩
  have hdelc : c.delayed_cap < dimacsBound := c.hdel
  have hwc : c.wcap < 2 * dimacsBound := c.hwcap
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hdelc hwc hmaxv
  unfold Func.wp full_prop_flush_del_fid_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (wlen_v, wu_v, j_v, ()) mj => ∃ (st : FullState) (wl_d : Nat) (wu_d : BitVec 64)
      (idx : Nat),
      wlen_v = BitVec.ofNat 64 st.core.wlen ∧ wu_v = st.core.wusable ∧
      j_v.toNat = 3 * idx ∧ idx ≤ dlen ∧
      st.core = { st0.core with
        wvec := st.core.wvec, wstk := st.core.wstk,
        wlen := st.core.wlen, wusable := st.core.wusable } ∧
      st.scratch = { st0.scratch with wsort := st.scratch.wsort } ∧
      st.LengthsOk c ∧ WatchStackLayout st.core ∧
      (WatchesInv F_cur st0.core → WatchesInv F_cur st.core) ∧
      (skip_lit < 2 * st0.core.cur_vars →
        ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
          let off' := fullWatchOffCore st.core skip_lit
          SplitWatchesInv F_cur st.core skip_lit off'
            (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) ∧
      (FullMem c (fidFlushDisk wl_d wu_d st) ⋆ R) mj)
    (fun (_, _, j_v, ()) _ => 3 * dlen - j_v.toNat) ?_ ?_
  · intro Jl hJl
    c0_hsteps
    refine hJl (BitVec.ofNat 64 st0.core.wlen, st0.core.wusable, 0#64, ()) m0
      ⟨st0, st0.core.wlen, st0.core.wusable, 0, rfl, rfl, by decide, Nat.zero_le _,
       by cases st0.core; rfl, by cases st0.scratch; rfl, hlen0, hlay0, fun h => h, ?_,
       by simpa [fidFlushDisk] using hm0⟩
    intro _ off q p end_v hsw
    have hoff := hsw.off_eq
    have hq_ge := hsw.q_ge; have hq_le := hsw.q_le_p; have hp_le := hsw.p_le_end
    have h1 : fullWatchOffCore st0.core skip_lit = off := hoff
    simpa [h1, show off + (q - off) = q by omega, show off + (p - off) = p by omega,
      show off + (end_v - off) = end_v by omega] using hsw
  · rintro Jl ⟨wlen_v, wu_v, j_v, ⟨⟩⟩ mj ⟨st, wl_d, wu_d, idx, hwlen_v, hwu_v, hj_eq, hidx_le,
      hcore_eq, hsc_eq, hlen, hlay, hwat_pres, hsw_pres, hmj⟩ hJl
    subst hwlen_v hwu_v
    have hdel_len := hlen.scratch_ok.delayed_len_arr
    have hcv_le := hlen.core_ok.cur_vars_le
    have hwv_len := hlen.core_ok.wvec_len
    have hws_len := hlen.core_ok.wstk_len_arr
    have hwlen_le := hlen.core_ok.wlen_le
    have hcv_eq : st.core.cur_vars = st0.core.cur_vars := by rw [hcore_eq]
    have har_eq : st.core.arena = st0.core.arena := by rw [hcore_eq]
    have hal_eq : st.core.arena_len = st0.core.arena_len := by rw [hcore_eq]
    have href_eq : fullArenaClauseRefsCore st.core = fullArenaClauseRefsCore st0.core := by
      unfold fullArenaClauseRefsCore; rw [har_eq, hal_eq]
    have hdel_eq : st.scratch.delayed = st0.scratch.delayed := by rw [hsc_eq]
    have hdisk_del : (fidFlushDisk wl_d wu_d st).scratch.delayed = st.scratch.delayed := rfl
    have hdisk_wv : (fidFlushDisk wl_d wu_d st).core.wvec = st.core.wvec := rfl
    have hdisk_ws : (fidFlushDisk wl_d wu_d st).core.wstk = st.core.wstk := rfl
    have hdisk_del_len : (fidFlushDisk wl_d wu_d st).scratch.delayed.length = 3 * c.delayed_cap :=
      hdel_len
    have hdisk_wv_len : (fidFlushDisk wl_d wu_d st).core.wvec.length = 4 * c.max_vars := hwv_len
    have hdisk_ws_len : (fidFlushDisk wl_d wu_d st).core.wstk.length = c.wcap := hws_len
    rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    · have hlt_j : j_v.toNat < di.toNat := hc
      have hidx_lt : idx < dlen := by omega
      have h3i_lt : 3 * idx + 2 < st.scratch.delayed.length := by omega
      have hj1_nat : (j_v + 1#64).toNat = 3 * idx + 1 := by
        rw [BitVec.toNat_add, hj_eq]; change (3 * idx + 1) % 2 ^ 64 = 3 * idx + 1
        exact Nat.mod_eq_of_lt (by omega)
      have hj2_nat : (j_v + 2#64).toNat = 3 * idx + 2 := by
        rw [BitVec.toNat_add, hj_eq]; change (3 * idx + 2) % 2 ^ 64 = 3 * idx + 2
        exact Nat.mod_eq_of_lt (by omega)
      have hj3_nat : (j_v + 3#64).toNat = 3 * (idx + 1) := by
        rw [BitVec.toNat_add, hj_eq]; change (3 * idx + 3) % 2 ^ 64 = 3 * (idx + 1)
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      obtain ⟨hrlit_lt, hrlit_ne, hrw0_f, hrcr_lt, hrcr_ref⟩ := hdel0 idx hidx_lt
      have hrlit_get : st.scratch.delayed[j_v.toNat]'(by omega) =
          st0.scratch.delayed[3 * idx]?.getD 0#32 := by
        rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj_eq]
      have hrw0_get : st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega) =
          st0.scratch.delayed[3 * idx + 1]?.getD 0#32 := by
        rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj1_nat]
      have hrcr_get : st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega) =
          st0.scratch.delayed[3 * idx + 2]?.getD 0#32 := by
        rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj2_nat]
      let rw_v := st.scratch.delayed[j_v.toNat]'(by omega)
      let ow_v := st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega)
      let cr_v := st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega)
      have hrw_lt : rw_v.toNat < 2 * st.core.cur_vars := by
        dsimp only [rw_v]; rw [hrlit_get, hcv_eq]; exact hrlit_lt
      have hrw_ne : rw_v.toNat ≠ skip_lit := by
        dsimp only [rw_v]; rw [hrlit_get]; exact hrlit_ne
      have how_f : (ow_v &&& 0x80000000#32) = 0#32 := by
        dsimp only [ow_v]; rw [hrw0_get]; exact hrw0_f
      have hcr_lt_st : cr_v.toNat < 0x80000000 := by
        dsimp only [cr_v]; rw [hrcr_get]; exact hrcr_lt
      have hcr_ref_st : cr_v.toNat ∈ fullArenaClauseRefsCore st.core := by
        dsimp only [cr_v]; rw [hrcr_get, href_eq]; exact hrcr_ref
      have how_ne : ow_v ≠ 0xFFFFFFFF#32 := fun heq => by
        rw [heq] at how_f; exact absurd how_f (by decide)
      have hcr_ne : cr_v ≠ 0xFFFFFFFF#32 := fun heq => by
        rw [heq] at hcr_lt_st; revert hcr_lt_st; decide
      have hrw64_nat : (rw_v.setWidth 64 <<< (1 : Nat)).toNat = 2 * rw_v.toNat := by
        rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]; simp [Nat.shiftLeft_eq]; omega
      have hrw64p1_nat : ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * rw_v.toNat + 1 := by
        rw [BitVec.toNat_add, hrw64_nat]; change (2 * rw_v.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hwv_i0 : (rw_v.setWidth 64 <<< (1 : Nat)).toNat < st.core.wvec.length := by
        rw [hwv_len, hrw64_nat]; omega
      have hwv_i1 : ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < st.core.wvec.length := by
        rw [hwv_len, hrw64p1_nat]; omega
      let roff_w := st.core.wvec[(rw_v.setWidth 64 <<< (1 : Nat)).toNat]'hwv_i0
      let rsz_w := st.core.wvec[((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hwv_i1
      have hroff_eq : (roff_w.setWidth 64).toNat = fullWatchOffCore st.core rw_v.toNat := by
        rw [zext_toNat _ (by decide)]; unfold fullWatchOffCore
        rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
        exact congrArg BitVec.toNat (by simp [roff_w, hrw64_nat])
      have hrsz_eq : (rsz_w.setWidth 64).toNat = fullWatchSizeCore st.core rw_v.toNat := by
        rw [zext_toNat _ (by decide)]; unfold fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
        exact congrArg BitVec.toNat (by simp [rsz_w, hrw64p1_nat])
      have hbd_rw := hlay.bounds rw_v.toNat hrw_lt
      have hrend_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64).toNat =
          fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat := by
        rw [BitVec.toNat_add, hroff_eq, hrsz_eq, Nat.mod_eq_of_lt (by omega)]
      have hrend1_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 1#64).toNat =
          fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 1 := by
        rw [BitVec.toNat_add, hrend_nat]; change (_ + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hrend2_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 2#64).toNat =
          fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 2 := by
        rw [BitVec.toNat_add, hrend_nat]; change (_ + 2) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hwl_nat : (BitVec.ofNat 64 st.core.wlen).toNat = st.core.wlen :=
        fid_bv64_ofNat (by omega)
      have hwl1_nat : (BitVec.ofNat 64 st.core.wlen + 1#64).toNat = st.core.wlen + 1 := by
        rw [BitVec.toNat_add, hwl_nat]; change (_ + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hwl2_nat : (BitVec.ofNat 64 st.core.wlen + 2#64).toNat = st.core.wlen + 2 := by
        rw [BitVec.toNat_add, hwl_nat]; change (_ + 2) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hwc_nat : (BitVec.ofNat 64 c.wcap).toNat = c.wcap := fid_bv64_ofNat (by omega)
      c0_hsteps_nogrp
      -- Join point after the 4-way if/else-if/else chain
      refine wp_join_group (ts := [i64, i64])
        (fun (wlen_n, wu_n, ()) mn => ∃ (st_n : FullState) (wl_dn : Nat) (wu_dn : BitVec 64),
          wlen_n = BitVec.ofNat 64 st_n.core.wlen ∧ wu_n = st_n.core.wusable ∧
          st_n.core = { st0.core with
            wvec := st_n.core.wvec, wstk := st_n.core.wstk,
            wlen := st_n.core.wlen, wusable := st_n.core.wusable } ∧
          st_n.scratch = { st0.scratch with wsort := st_n.scratch.wsort } ∧
          st_n.LengthsOk c ∧ WatchStackLayout st_n.core ∧
          (WatchesInv F_cur st0.core → WatchesInv F_cur st_n.core) ∧
          (skip_lit < 2 * st0.core.cur_vars →
            ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
              let off' := fullWatchOffCore st_n.core skip_lit
              SplitWatchesInv F_cur st_n.core skip_lit off'
                (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) ∧
          (FullMem c (fidFlushDisk wl_dn wu_dn st_n) ⋆ R) mn)
        (fun _ ⟨wlen_n, wu_n, ⟨⟩⟩ mn ⟨st_n, wl_dn, wu_dn, hwl_n, hwu_n, hcn, hscn, hln, hlyn,
            hwn, hswn, hmn⟩ => by
          c0_hsteps
          exact hJl (wlen_n, wu_n, j_v + 3#64, ()) mn (by dsimp only; rw [hj_eq, hj3_nat]; omega)
            ⟨st_n, wl_dn, wu_dn, idx + 1, hwl_n, hwu_n, hj3_nat, by omega, hcn, hscn, hln, hlyn,
              hwn, hswn, hmn⟩) ?_
      intro Jnext hJnext
      have hrv_w0 : (fidFlushDisk wl_d wu_d st).core.wvec[
          2 * (fidFlushDisk wl_d wu_d st).scratch.delayed[j_v.toNat].toNat % 2 ^ 64]'(by
            dsimp only [fidFlushDisk]
            change 2 * rw_v.toNat % 2 ^ 64 < st.core.wvec.length
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat < 2 ^ 64)]; omega) =
          roff_w := by
        dsimp only [fidFlushDisk, roff_w]
        congr 1
      have hrv_w1 : (fidFlushDisk wl_d wu_d st).core.wvec[
          (2 * (fidFlushDisk wl_d wu_d st).scratch.delayed[j_v.toNat].toNat + 1) % 2 ^ 64]'(by
            dsimp only [fidFlushDisk]
            change (2 * rw_v.toNat + 1) % 2 ^ 64 < st.core.wvec.length
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]; omega) =
          rsz_w := by
        dsimp only [fidFlushDisk, rsz_w]
        congr 1
        change (2 * rw_v.toNat + 1) % 2 ^ 64 = (rw_v.setWidth 64 <<< (1 : Nat) + 1#64).toNat
        rw [hrw64p1_nat, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]
      have hrv_w0_s : st.core.wvec[2 * rw_v.toNat % 2 ^ 64]'(by
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat < 2 ^ 64)]; omega) =
          roff_w := by simpa only [fidFlushDisk] using hrv_w0
      have hrv_w1_s : st.core.wvec[(2 * rw_v.toNat + 1) % 2 ^ 64]'(by
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]; omega) =
          rsz_w := by simpa only [fidFlushDisk] using hrv_w1
      have hroff_t : roff_w.toNat = fullWatchOffCore st.core rw_v.toNat := by
        rw [← hroff_eq, zext_toNat _ (by decide)]
      have hrsz_t : rsz_w.toNat = fullWatchSizeCore st.core rw_v.toNat := by
        rw [← hrsz_eq, zext_toNat _ (by decide)]
      refine wp_join_group (ts := [])
        (fun _ m2 => (FullMem c (fidFlushDisk wl_d wu_d st) ⋆ R) m2)
        (fun _ ⟨⟩ m2 hm2 => by
          rw [Blocks.get_here]; dsimp only
          refine wp_join_group (ts := [i64, i64])
            (fun p mn => wp Γ Q X (.jump Jnext (.var p.1, .var p.2.1, ())) mn)
            (fun _ p mn h => by rw [Blocks.get_here]; exact h) ?_
          intro Jnext2 hJnext2
          refine wp_join_group (ts := [])
            (fun _ m3 => (FullMem c (fidFlushDisk wl_d wu_d st) ⋆ R) m3)
            (fun _ ⟨⟩ m3 hm3 => by
              rw [Blocks.get_here]; dsimp only
              refine wp_join_group (ts := [i64, i64])
                (fun p mn => wp Γ Q X (.jump Jnext2 (.var p.1, .var p.2.1, ())) mn)
                (fun _ p mn h => by rw [Blocks.get_here]; exact h) ?_
              intro Jnext3 hJnext3
              refine wp_join_group (ts := [])
                (fun _ mc => (FullMem c (fidFlushDisk wl_d wu_d st) ⋆ R) mc)
                (fun _ ⟨⟩ mc hmc => by
                  -- Cold fallback: sync wlen & wu, call full_watch_push
                  rw [Blocks.get_here]; dsimp only
                  c0_hsteps_nogrp
                  have hmc_sync : (FullMem c st ⋆ R) m := by
                    simpa only [fidFlushDisk, hwl_nat] using hm
                  refine LeanQbe.T.wp_call_of_spec _ _ (hPush _ _ _ _ ?_)
                  refine ⟨c, st, R, rfl, hlen, hlay, fun h => absurd h (by decide),
                    fun _ => ⟨how_ne, hcr_ne⟩, hmc_sync,
                    fun pok wvec' wstk' wlen' wu' wsort' mp hlen_p hlay_p hpres_o
                      hpok_t hpok_f hmp => ?_⟩
                  let st_p : FullState :=
                    { st with
                      core := { st.core with wvec := wvec', wstk := wstk',
                                             wlen := wlen', wusable := wu' }
                      scratch := { st.scratch with wsort := wsort' } }
                  have hcore_p : st_p.core = { st0.core with
                      wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } := by
                    dsimp only [st_p]; rw [hcore_eq]
                  have hsc_p : st_p.scratch = { st0.scratch with wsort := wsort' } := by
                    dsimp only [st_p]; rw [hsc_eq]
                  have hst_p_eq : st_p =
                      { st0 with
                        core := { st0.core with wvec := wvec', wstk := wstk',
                                                wlen := wlen', wusable := wu' }
                        scratch := { st0.scratch with wsort := wsort' } } := by
                    cases h1 : st_p; rw [h1] at hcore_p hsc_p; dsimp only at hcore_p hsc_p
                    rw [hcore_p, hsc_p]
                  unfold fullWatchSize fullWatchOff at hpres_o hpok_t hpok_f
                  c0_hsteps_nogrp
                  · have hpok_eq : pok = true := by assumption
                    have ⟨_, _, hsz_p, hpre_p, hw0_p, hw1_p⟩ := hpok_t hpok_eq
                    have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core)
                      (k' := st_p.core) (lit := rw_v) (w0 := ow_v) (cref := cr_v)
                      (skip_lit := skip_lit) rfl rfl hlay_p hrw_lt how_f hcr_lt_st hcr_ref_st
                      hpres_o ⟨hsz_p, hpre_p, hw0_p, hw1_p rfl⟩
                    refine hJnext (BitVec.ofNat 64 wlen', wu', ()) mp
                      ⟨st_p, wlen', wu', rfl, rfl, hcore_p, hsc_p, hlen_p, hlay_p,
                       fun hw0 => hstep.1 (hwat_pres hw0), ?_,
                       by simpa [fidFlushDisk, st_p] using hmp⟩
                    intro hsk off q p end_v hsw0
                    have hsw1 := hsw_pres hsk off q p end_v hsw0
                    have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
                      (fullWatchOffCore st.core skip_lit)
                      (fullWatchOffCore st.core skip_lit + (q - off))
                      (fullWatchOffCore st.core skip_lit + (p - off))
                      (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                    simpa [Nat.add_sub_cancel_left] using hsw2
                  · have hpok_eq : pok = false := by
                      cases pok
                      · rfl
                      · cases (by assumption : true = false)
                    have hstep := s15_flush_step_false_preserves (F_cur := F_cur)
                      (k := st.core) (k' := st_p.core) (lit := rw_v) (skip_lit := skip_lit)
                      rfl rfl hlay_p hpres_o (hpok_f hpok_eq).1
                    refine hQ false wvec' wstk' wlen' wu' wsort' mp
                      (hst_p_eq ▸ hlen_p) (hcore_p ▸ hlay_p)
                      (fun hw0 => hcore_p ▸ hstep.1 (hwat_pres hw0)) ?_ (hst_p_eq ▸ hmp)
                    intro hsk off q p end_v hsw0
                    have hsw1 := hsw_pres hsk off q p end_v hsw0
                    have hsw2 := hstep.2 (hcv_eq ▸ hsk)
                      (fullWatchOffCore st.core skip_lit)
                      (fullWatchOffCore st.core skip_lit + (q - off))
                      (fullWatchOffCore st.core skip_lit + (p - off))
                      (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                    simpa [Nat.add_sub_cancel_left, ← hcore_p] using hsw2) ?_
              -- Case 3: rsz == 0 && wlen > 0 && wlen + 2 <= wcap
              intro Jc3 hJc3
              c0_hsplit
              · have hrsz0 : fullWatchSizeCore st.core rw_v.toNat = 0 := by
                  have h := congrArg BitVec.toNat (hc : _)
                  rw [hrv_w1, hrsz_eq] at h; simpa using h
                c0_hsplit
                · have hw_pos : 1 ≤ st.core.wlen := by
                    have h := hc
                    rw [Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] at h
                    simp at h; omega
                  c0_hsplit
                  · have hfit2 : st.core.wlen + 2 ≤ c.wcap := by
                      have h := hc
                      rw [Nat.mod_eq_of_lt (by omega : st.core.wlen + 2 < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : c.wcap < 2 ^ 64)] at h; exact h
                    have hwv_set_lt : (rw_v.setWidth 64 <<< (1 : Nat) + 1).toNat <
                        ((fidFlushDisk wl_d wu_d st).core.wvec.set
                          (rw_v.setWidth 64 <<< (1 : Nat)).toNat
                          ((BitVec.ofNat 64 st.core.wlen).setWidth 32)).length := by
                      rw [List.length_set, hdisk_wv_len, show (1 : BitVec 64) = 1#64 from rfl,
                        hrw64p1_nat]; omega
                    c0_hsteps_nogrp
                    obtain ⟨hlen_k, hlay_k, _, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
                      fid_repl_empty_layout hlay hlen.core_ok hrw_lt hw_pos hrsz0 hfit2 how_f
                        hcr_lt_st
                    let st_n : FullState :=
                      { st with core :=
                          { st.core with
                            wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                            wvec := (st.core.wvec.set (2 * rw_v.toNat)
                              (BitVec.ofNat 32 st.core.wlen)).set (2 * rw_v.toNat + 1) 2#32
                            wlen := st.core.wlen + 2 } }
                    have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core)
                      (k' := st_n.core) (lit := rw_v) (w0 := ow_v) (cref := cr_v)
                      (skip_lit := skip_lit) rfl rfl hlay_k hrw_lt how_f hcr_lt_st hcr_ref_st
                      hpres_o ⟨hsz_k, hpre_k, hw0_k, hw1_k⟩
                    have hwl_bv :
                        BitVec.ofNat 64 st.core.wlen + 2#64 =
                          BitVec.ofNat 64 (st.core.wlen + 2) := by
                      apply BitVec.eq_of_toNat_eq; rw [hwl2_nat, fid_bv64_ofNat (by omega)]
                    have htr32 :
                        (BitVec.ofNat 64 st.core.wlen).setWidth 32 =
                          BitVec.ofNat 32 st.core.wlen := by
                      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
                    refine hJnext (BitVec.ofNat 64 st.core.wlen + 2#64, st.core.wusable, ()) m
                      ⟨st_n, wl_d, wu_d, hwl_bv, rfl, by dsimp [st_n]; rw [hcore_eq], hsc_eq,
                       ⟨hlen_k, hlen.scratch_ok⟩, hlay_k,
                       fun hw0 => hstep.1 (hwat_pres hw0), ?_, ?_⟩
                    · intro hsk off q p end_v hsw0
                      have hsw1 := hsw_pres hsk off q p end_v hsw0
                      have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
                        (fullWatchOffCore st.core skip_lit)
                        (fullWatchOffCore st.core skip_lit + (q - off))
                        (fullWatchOffCore st.core skip_lit + (p - off))
                        (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                      simpa [Nat.add_sub_cancel_left] using hsw2
                    · refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                      unfold fidFlushDisk; dsimp only [st_n]; congr 1; congr 1
                      · congr 1; congr 1
                      · congr 1; congr 1
                  · exact hJc3 () m3 hm3
                · exact hJc3 () m3 hm3
              · exact hJc3 () m3 hm3) ?_
          -- Case 2: rsz > 0 && roff + rsz == wlen && wlen + 2 <= wcap
          intro Jc2 hJc2
          c0_hsplit
          · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
              have h := hc
              simp only [hrv_w1, hrsz_t] at h; simpa using h
            have hoff_pos := hlay.pos_off rw_v.toNat hrw_lt hrsz_pos
            c0_hsplit
            · have hend_wlen : fullWatchOffCore st.core rw_v.toNat +
                  fullWatchSizeCore st.core rw_v.toNat = st.core.wlen := by
                have h := congrArg BitVec.toNat (hc : _)
                simpa only [hrv_w0, hrv_w1, hrend_nat, hwl_nat] using h
              c0_hsplit
              · have hfit2 : st.core.wlen + 2 ≤ c.wcap := by
                  have h := hc
                  rw [Nat.mod_eq_of_lt (by omega : st.core.wlen + 2 < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : c.wcap < 2 ^ 64)] at h; exact h
                c0_hsteps_nogrp
                obtain ⟨hlen_k, hlay_k, _, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
                  s15_append_end_layout hlay hlen.core_ok hrw_lt hoff_pos hend_wlen hfit2 how_f
                    hcr_lt_st
                let sz0 := fullWatchSizeCore st.core rw_v.toNat
                let st_n : FullState :=
                  { st with core :=
                      { st.core with
                        wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                        wvec := st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                        wlen := st.core.wlen + 2 } }
                have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core)
                  (k' := st_n.core) (lit := rw_v) (w0 := ow_v) (cref := cr_v)
                  (skip_lit := skip_lit) rfl rfl (by simpa [st_n, hend_wlen] using hlay_k) hrw_lt
                  how_f hcr_lt_st hcr_ref_st (by simpa [st_n, hend_wlen] using hpres_o)
                  ⟨by simpa [st_n, hend_wlen] using hsz_k, by simpa [st_n, hend_wlen] using hpre_k,
                   by simpa [st_n, hend_wlen] using hw0_k, by simpa [st_n, hend_wlen] using hw1_k⟩
                have hwl_bv :
                    BitVec.ofNat 64 st.core.wlen + 2#64 = BitVec.ofNat 64 (st.core.wlen + 2) := by
                  apply BitVec.eq_of_toNat_eq; rw [hwl2_nat, fid_bv64_ofNat (by omega)]
                have hsz_bv :
                    (rsz_w.setWidth 64 + 2#64).setWidth 32 = BitVec.ofNat 32 (sz0 + 2) := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_setWidth, BitVec.toNat_add, hrsz_eq, BitVec.toNat_ofNat]
                  change ((sz0 + 2) % 2 ^ 64) % 2 ^ 32 = (sz0 + 2) % 2 ^ 32
                  rw [Nat.mod_eq_of_lt (by omega : sz0 + 2 < 2 ^ 64)]
                refine hJnext (BitVec.ofNat 64 st.core.wlen + 2#64, st.core.wusable, ()) m
                  ⟨st_n, wl_d, wu_d, hwl_bv, rfl, by dsimp [st_n]; rw [hcore_eq], hsc_eq,
                   ⟨by simpa [st_n, hend_wlen] using hlen_k, hlen.scratch_ok⟩,
                   by simpa [st_n, hend_wlen] using hlay_k,
                   fun hw0 => hstep.1 (hwat_pres hw0), ?_, ?_⟩
                · intro hsk off q p end_v hsw0
                  have hsw1 := hsw_pres hsk off q p end_v hsw0
                  have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
                    (fullWatchOffCore st.core skip_lit)
                    (fullWatchOffCore st.core skip_lit + (q - off))
                    (fullWatchOffCore st.core skip_lit + (p - off))
                    (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                  simpa [Nat.add_sub_cancel_left] using hsw2
                · refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                  unfold fidFlushDisk; dsimp only [st_n]; congr 1; congr 1
                  · congr 1
                  · congr 1; congr 1
              · exact hJc2 () m2 hm2
            · exact hJc2 () m2 hm2
          · exact hJc2 () m2 hm2) ?_
      -- Main Case 1 (sentinel reuse) vs falling through to Case 2
      intro Jc1 hJc1
      c0_hsplit
      · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
          have h := hc
          simp only [hrv_w1, hrsz_t] at h; simpa using h
        have hoff_pos := hlay.pos_off rw_v.toNat hrw_lt hrsz_pos
        c0_hsplit
        · have hend2_le : fullWatchOffCore st.core rw_v.toNat +
              fullWatchSizeCore st.core rw_v.toNat + 2 ≤ st.core.wlen := by
            have h := hc
            simp only [hrv_w0, hrv_w1, hroff_t, hrsz_t] at h
            rw [Nat.mod_eq_of_lt (by omega :
                fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 2 <
                  2 ^ 64),
              Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] at h; exact h
          have hws_i0 : (roff_w.setWidth 64 + rsz_w.setWidth 64).toNat <
              (fidFlushDisk wl_d wu_d st).core.wstk.length := by
            rw [hdisk_ws_len, hrend_nat]; omega
          have hws_i1 : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 1).toNat <
              (fidFlushDisk wl_d wu_d st).core.wstk.length := by
            rw [hdisk_ws_len, show (1 : BitVec 64) = 1#64 from rfl, hrend1_nat]; omega
          c0_hsplit
          · have hsent0 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
                fullWatchSizeCore st.core rw_v.toNat]? = some 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem (by rw [hws_len]; omega)]
              have h := hc
              dsimp only [fidFlushDisk] at h
              refine congrArg some (Eq.trans ?_ h)
              congr 1
              change fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat =
                (st.core.wvec[2 * rw_v.toNat % 2 ^ 64].toNat +
                  st.core.wvec[(2 * rw_v.toNat + 1) % 2 ^ 64].toNat) % 2 ^ 64
              rw [hrv_w0_s, hrv_w1_s, hroff_t, hrsz_t,
                Nat.mod_eq_of_lt (by omega :
                  fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat <
                    2 ^ 64)]
            c0_hsplit
            · have hsent1 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
                  fullWatchSizeCore st.core rw_v.toNat + 1]? = some 0xFFFFFFFF#32 := by
                rw [List.getElem?_eq_getElem (by rw [hws_len]; omega)]
                have h := hc
                dsimp only [fidFlushDisk] at h
                refine congrArg some (Eq.trans ?_ h)
                congr 1
                change fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat +
                    1 = (st.core.wvec[2 * rw_v.toNat % 2 ^ 64].toNat +
                      st.core.wvec[(2 * rw_v.toNat + 1) % 2 ^ 64].toNat + 1) % 2 ^ 64
                rw [hrv_w0_s, hrv_w1_s, hroff_t, hrsz_t,
                  Nat.mod_eq_of_lt (by omega :
                    fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 1 <
                      2 ^ 64)]
              let sz0 := fullWatchSizeCore st.core rw_v.toNat
              let wend0 := fullWatchOffCore st.core rw_v.toNat + sz0
              have hsz_bv : (rsz_w.setWidth 64 + 2#64).setWidth 32 = BitVec.ofNat 32 (sz0 + 2) := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_setWidth, BitVec.toNat_add, hrsz_eq, BitVec.toNat_ofNat]
                change ((sz0 + 2) % 2 ^ 64) % 2 ^ 32 = (sz0 + 2) % 2 ^ 32
                rw [Nat.mod_eq_of_lt (by omega : sz0 + 2 < 2 ^ 64)]
              have hfin : ∀ (wu_n : BitVec 64) (mn : Mem 64),
                  (FullMem c (fidFlushDisk wl_d wu_d
                    { st with core :=
                        { st.core with
                          wstk := (st.core.wstk.set wend0 ow_v).set (wend0 + 1) cr_v
                          wvec := st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                          wusable := wu_n } }) ⋆ R) mn →
                  wp Γ Q X (Expr.jump Jnext (Arg.var (BitVec.ofNat 64 st.core.wlen),
                    Arg.var wu_n, ())) mn := by
                intro wu_n mn hmn
                obtain ⟨hlen_k, hlay_k, _, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
                  s15_append_sentinel_layout hlay hlen.core_ok (wu' := wu_n) hrw_lt hoff_pos
                    hend2_le hsent0 hsent1 how_f hcr_lt_st
                let st_n : FullState :=
                  { st with core :=
                      { st.core with
                        wstk := (st.core.wstk.set wend0 ow_v).set (wend0 + 1) cr_v
                        wvec := st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                        wusable := wu_n } }
                have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core)
                  (k' := st_n.core) (lit := rw_v) (w0 := ow_v) (cref := cr_v) (skip_lit := skip_lit)
                  rfl rfl hlay_k hrw_lt how_f hcr_lt_st hcr_ref_st hpres_o
                  ⟨hsz_k, hpre_k, hw0_k, hw1_k⟩
                refine hJnext (BitVec.ofNat 64 st.core.wlen, wu_n, ()) mn
                  ⟨st_n, wl_d, wu_d, rfl, rfl, by dsimp [st_n]; rw [hcore_eq], hsc_eq,
                   ⟨hlen_k, hlen.scratch_ok⟩, hlay_k, fun hw0 => hstep.1 (hwat_pres hw0), ?_, hmn⟩
                intro hsk off q p end_v hsw0
                have hsw1 := hsw_pres hsk off q p end_v hsw0
                have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
                  (fullWatchOffCore st.core skip_lit)
                  (fullWatchOffCore st.core skip_lit + (q - off))
                  (fullWatchOffCore st.core skip_lit + (p - off))
                  (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                simpa [Nat.add_sub_cancel_left] using hsw2
              c0_hsteps
              · refine hfin (st.core.wusable - 2#64) m ?_
                refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                unfold fidFlushDisk; dsimp only [wend0, sz0]; congr 1; congr 1
                · congr 1
                · congr 1; congr 1
              · refine hfin st.core.wusable m ?_
                refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                unfold fidFlushDisk; dsimp only [wend0, sz0]; congr 1; congr 1
                · congr 1
                · congr 1; congr 1
            · exact hJc1 () mj hmj
          · exact hJc1 () mj hmj
        · exact hJc1 () mj hmj
      · exact hJc1 () mj hmj
    · c0_hsteps_nogrp
      have hst_eq : st =
          { st0 with
            core := { st0.core with
              wvec := st.core.wvec, wstk := st.core.wstk,
              wlen := st.core.wlen, wusable := st.core.wusable }
            scratch := { st0.scratch with wsort := st.scratch.wsort } } := by
        cases st; cases st0; simp only [FullState.mk.injEq] at *; exact ⟨hcore_eq, hsc_eq⟩
      have hm_sync : (FullMem c st ⋆ R) (by assumption : Mem 64) := by
        simpa [fidFlushDisk] using (by assumption : _)
      exact hQ true st.core.wvec st.core.wstk st.core.wlen st.core.wusable st.scratch.wsort _
        (hst_eq ▸ hlen) (hcore_eq ▸ hlay) (fun hw0 => hcore_eq ▸ hwat_pres hw0)
        (fun hsk off q p end_v hsw0 => by simpa [← hcore_eq] using hsw_pres hsk off q p end_v hsw0)
        (hst_eq ▸ hm_sync)

end LeanQbe.T.Examples.Kissat.FullFidelityBcp
