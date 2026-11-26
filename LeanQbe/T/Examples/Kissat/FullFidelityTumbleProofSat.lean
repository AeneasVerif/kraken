/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
import LeanQbe.T.Examples.Kissat.FullM4Proof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 11 PR 2 SAT Unpermutation Proofs (`FullFidelityTumbleProofSat`)

Proves `Full.fullExtendSpec` (`fullExtendSlice`: mutates ONLY `core.vals`, zero changes to
`kissat_solve_bytes_m6`) for:
1. `full_extend_core_fid_wp`: direct reuse of `FullM4.m4_extend_wp`.
2. `full_unperm_fid_wp`: two-pass even/odd `vals[]`-only unpermutation reading `extend_stk`
   read-only (`0` writes outside `core.vals`).
3. `full_extend_tum_wp`: sequential composition of `full_extend_core_fid` and `full_unperm_fid`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityTumble

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

private theorem bv64_shl1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 63) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

private theorem bv64_shl1_or1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 63) :
    ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 := by
  have hs : (v <<< (1 : Nat)).toNat = 2 * v.toNat := bv64_shl1_toNat hv
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_or, hs, h1]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    simp [Nat.testBit_succ, show (2 * v.toNat + 1) / 2 = v.toNat by omega,
      show (2 * v.toNat) / 2 = v.toNat by omega]

private theorem fullExtendSlice_set_vals {c : FullCfg} {s : FullState}
    (i : Nat) (v : BitVec 8) :
    PreservesCoreSlice (fullExtendSlice c).coreProj s
      { s with core := { s.core with vals := s.core.vals.set i v } } :=
  rfl

private theorem fullExtendSlice_set_vals_len {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (i : Nat) (v : BitVec 8) :
    ({ s with core := { s.core with vals := s.core.vals.set i v } } : FullState).LengthsOk c :=
  ⟨{ hlen.core_ok with vals_len := by simp [hlen.core_ok.vals_len] }, hlen.scratch_ok⟩

/-- Direct reuse of `FullM4.m4_extend_wp` for `full_extend_core_fid` (`Full.fullExtendSpec`). -/
theorem full_extend_core_fid_wp (Γ : Env) :
    ∀ a m Q X, fullExtendSpec a m Q X → Func.wp Γ fidStep11ExtendCoreFn.body a m Q X :=
  FullM4.m4_extend_wp Γ

/-- Two-pass even/odd `vals[]`-only unpermutation `full_unperm_fid` satisfies exact
`Full.fullExtendSpec` (`fullExtendSlice`). -/
theorem full_unperm_fid_wp (Γ : Env) :
    ∀ a m Q X, fullUnpermFidSpec a m Q X → Func.wp Γ full_unperm_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hlen hm hQ
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hext : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at hmax hext
  have hesl : s.scratch.extend_stk.length = c.extend_cap := hlen.scratch_ok.extend_stk_len
  unfold Func.wp full_unperm_fid_body
  c0_hsteps_nogrp
  · -- `len == 0`
    exact hQ () s m rfl hlen trivial hm
  · -- `0 < len ≤ extend_cap` (`len > extend_cap` auto-discharged by `hel`)
    have hlen_pos : 0 < s.scratch.extend_len := by
      have hne : ¬ BitVec.ofNat 64 s.scratch.extend_len = 0#64 := by assumption
      exact Nat.pos_of_ne_zero fun hz => hne (by rw [hz])
    have h0_lt : (BitVec.ofNat 64 0).toNat < s.scratch.extend_stk.length := by
      rw [hesl]; simp only [BitVec.toNat_ofNat]; omega
    c0_hsteps_nogrp
    · -- `head` is not `EXT_BLK_FLAG | EXT_PERM_FLAG`
      exact hQ () s m rfl hlen trivial hm
    · -- `mv > mx`
      exact hQ () s m rfl hlen trivial hm
    · -- `1 + mv > len`
      exact hQ () s m rfl hlen trivial hm
    · -- `mv ≤ mx` and `1 + mv ≤ len`
      have hmv_le_mx : ((s.scratch.extend_stk[0]'(by simpa using h0_lt) &&&
          536870911#32).setWidth 64).toNat ≤ c.max_vars := by
        have h1 : ¬ c.max_vars % 2 ^ 64 <
            (s.scratch.extend_stk[OfNat.ofNat 0 % 2 ^ 64]'(by simpa using h0_lt) &&&
              536870911#32).toNat := by assumption
        have h2 : c.max_vars % 2 ^ 64 = c.max_vars := Nat.mod_eq_of_lt (by omega)
        have h3 : ((s.scratch.extend_stk[0]'(by simpa using h0_lt) &&&
            536870911#32).setWidth 64).toNat =
            (s.scratch.extend_stk[OfNat.ofNat 0 % 2 ^ 64]'(by simpa using h0_lt) &&&
              536870911#32).toNat := by
          simp only [BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt]
          have := (s.scratch.extend_stk[0]'(by simpa using h0_lt) &&& 536870911#32).isLt; omega
        omega
      let mv_bv : BitVec 64 :=
        (s.scratch.extend_stk[0]'(by simpa using h0_lt) &&& 536870911#32).setWidth 64
      have hmv_to : mv_bv.toNat ≤ c.max_vars := hmv_le_mx
      have h1mv_le_len : 1 + mv_bv.toNat ≤ s.scratch.extend_len := by
        have h1 : ¬ s.scratch.extend_len % 2 ^ 64 <
            (BitVec.toNat (1 : BitVec 64) +
              (s.scratch.extend_stk[OfNat.ofNat 0 % 2 ^ 64]'(by simpa using h0_lt) &&&
                536870911#32).toNat) % 2 ^ 64 := by assumption
        have h2 : mv_bv.toNat =
            (s.scratch.extend_stk[OfNat.ofNat 0 % 2 ^ 64]'(by simpa using h0_lt) &&&
              536870911#32).toNat := by
          dsimp only [mv_bv]; simp only [BitVec.toNat_setWidth]
          rw [Nat.mod_eq_of_lt]
          have := (s.scratch.extend_stk[0]'(by simpa using h0_lt) &&& 536870911#32).isLt; omega
        have h3 : s.scratch.extend_len % 2 ^ 64 = s.scratch.extend_len :=
          Nat.mod_eq_of_lt (by omega)
        have h4 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
        rw [h4, ← h2, h3] at h1
        have h5 : (1 + mv_bv.toNat) % 2 ^ 64 = 1 + mv_bv.toNat := Nat.mod_eq_of_lt (by omega)
        omega
      -- Pass 1: `while (e < mv)`
      refine wp_while_state
        (fun (p : BitVec 64 × FullState) => (p.1, ()))
        (fun p => mv_bv.toNat - p.1.toNat)
        (fun p ml =>
          p.1.toNat ≤ mv_bv.toNat ∧
          PreservesCoreSlice (fullExtendSlice c).coreProj s p.2 ∧
          p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) ml)
        (fun J hJ => by c0_hsteps; exact hJ (0#64, s) m ⟨Nat.zero_le _, rfl, hlen, hm⟩)
        (fun J ⟨e, s1⟩ m1 ⟨hele, hcore1, hs1, hm1⟩ ih1 => ?_)
      dsimp only at hele hcore1 hs1 hm1 ih1 ⊢
      have hpres1 := fullExtend_preserves_nonVals hcore1
      have hesk1 : s1.scratch.extend_stk.length = c.extend_cap :=
        hs1.scratch_ok.extend_stk_len
      have hvl1 : s1.core.vals.length = 2 * c.max_vars := hs1.core_ok.vals_len
      c0_hsteps_nogrp
      · have he_lt : e.toNat < mv_bv.toNat := by assumption
        have he1 : (e + 1#64).toNat = e.toNat + 1 := by simp only [bv_c0]; omega
        have h1e_lt : (1#64 + e).toNat < s1.scratch.extend_stk.length := by
          rw [hesk1]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i8])
          (fun _ m2 => (FullMem c s1 ⋆ R) m2)
          (fun J2 ⟨pv, ⟨⟩⟩ m2 hm2 => by
            have he_or1 : ((e <<< (1 : Nat)) ||| 1#64).toNat < s1.core.vals.length := by
              rw [hvl1, bv64_shl1_or1_toNat (by omega)]; omega
            c0_hsteps
            exact ih1 (e + 1#64, _) _ (by dsimp only; rw [he1]; omega)
              ⟨by rw [he1]; omega,
               hcore1.trans (fullExtendSlice_set_vals _ _),
               fullExtendSlice_set_vals_len hs1 _ _, ‹_›⟩)
          (fun J2 hJ2 => by
            c0_hsteps_nogrp
            · have hiv_lt :
                  ((s1.scratch.extend_stk[(1#64 + e).toNat]'h1e_lt).setWidth 64).toNat <
                    c.max_vars := by
                have h1 :
                    (s1.scratch.extend_stk[(1#64 + e).toNat]'h1e_lt).toNat <
                      c.max_vars % 2 ^ 64 := by assumption
                simp only [BitVec.toNat_setWidth]
                have := (s1.scratch.extend_stk[(1#64 + e).toNat]'h1e_lt).isLt
                omega
              have hiv2 :
                  (((s1.scratch.extend_stk[(1#64 + e).toNat]'h1e_lt).setWidth 64) <<<
                    (1 : Nat)).toNat < s1.core.vals.length := by
                rw [hvl1, bv64_shl1_toNat (by omega)]; omega
              c0_hsteps
              · exact hJ2 (BitVec.ofNat 8 255, ()) m1 hm1
              · exact hJ2 (1#8, ()) m1 hm1
            · exact hJ2 (1#8, ()) m1 hm1)
      · -- Exit Pass 1 -> Pass 2: `while (e < mv)`
        refine wp_while_state
          (fun (p : BitVec 64 × FullState) => (p.1, ()))
          (fun p => mv_bv.toNat - p.1.toNat)
          (fun p ml =>
            (FullMem c p.2 ⋆ R) ml ∧
            p.1.toNat ≤ mv_bv.toNat ∧
            PreservesCoreSlice (fullExtendSlice c).coreProj s p.2 ∧
            p.2.LengthsOk c)
          (fun J2 hJ2 => by
            c0_hsteps; exact hJ2 (0#64, s1) m1 ⟨hm1, Nat.zero_le _, hcore1, hs1⟩)
          (fun J2 ⟨e2, s2⟩ m2 ⟨hm2, he2le, hcore2, hs2⟩ ih2 => ?_)
        dsimp only at he2le hcore2 hs2 hm2 ih2 ⊢
        have hvl2 : s2.core.vals.length = 2 * c.max_vars := hs2.core_ok.vals_len
        c0_hsteps_nogrp
        · have he2_lt : e2.toNat < mv_bv.toNat := by assumption
          have he2_1 : (e2 + 1#64).toNat = e2.toNat + 1 := by simp only [bv_c0]; omega
          have he2_or1 : ((e2 <<< (1 : Nat)) ||| 1#64).toNat < s2.core.vals.length := by
            rw [hvl2, bv64_shl1_or1_toNat (by omega)]; omega
          have he2_shl : (e2 <<< (1 : Nat)).toNat < s2.core.vals.length := by
            rw [hvl2, bv64_shl1_toNat (by omega)]; omega
          c0_hsteps_nogrp
          let s2a : FullState :=
            { s2 with core := { s2.core with
                vals := s2.core.vals.set (e2 <<< (1 : Nat)).toNat
                  (s2.core.vals[((e2 <<< (1 : Nat)) ||| 1#64).toNat]'he2_or1) } }
          have hcore2a : PreservesCoreSlice (fullExtendSlice c).coreProj s s2a :=
            hcore2.trans (fullExtendSlice_set_vals _ _)
          have hs2a : s2a.LengthsOk c := fullExtendSlice_set_vals_len hs2 _ _
          have he2_or1a : ((e2 <<< (1 : Nat)) ||| 1#64).toNat < s2a.core.vals.length := by
            rw [hs2a.core_ok.vals_len, bv64_shl1_or1_toNat (by omega)]; omega
          refine wp_join_group (ts := [i32])
            (fun _ m3 => (FullMem c s2a ⋆ R) m3) ?_ ?_
          · rintro J3 ⟨nv, ⟨⟩⟩ m3 hm3
            clear hm
            c0_hsteps
            exact ih2 (e2 + 1#64, _) m (by dsimp only; rw [he2_1]; omega)
              ⟨hm, by rw [he2_1]; omega,
               hcore2a.trans (fullExtendSlice_set_vals _ _),
               fullExtendSlice_set_vals_len hs2a _ _⟩
          · intro J3 hJ3
            c0_hsteps
            · exact hJ3 (_, ()) m hm
            · exact hJ3 (_, ()) m hm
        · exact hQ () s2 m2 hcore2 hs2 trivial hm2

/-- Top-level `full_extend_tum` (`full_extend_core_fid` followed by `full_unperm_fid`) satisfies
exact canonical `Full.fullExtendSpec` (`fullExtendSlice`, zero orchestrator changes). -/
theorem full_extend_tum_wp (Γ : Env)
    (hCore : ∀ a m Q X, fullExtendSpec a m Q X →
      Γ "full_extend_core_fid" [i64] [] a m Q X)
    (hUnperm : ∀ a m Q X, fullUnpermFidSpec a m Q X →
      Γ "full_unperm_fid" [i64] [] a m Q X) :
    ∀ a m Q X, fullExtendSpec a m Q X → Func.wp Γ full_extend_tum_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hlen hm hQ
  unfold Func.wp full_extend_tum_body
  c0_call hCore
  refine ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, fun _ s1 m1 hcore1 hlen1 _ hm1 => ?_⟩
  have hpres1 := fullExtend_preserves_nonVals hcore1
  have hel1 : s1.scratch.extend_len ≤ c.extend_cap := by rw [hpres1.1]; exact hel
  c0_call hUnperm
  refine ⟨c, s1, R, ⟨rfl, hel1⟩, hlen1, hm1, fun _ s2 m2 hcore2 hlen2 _ hm2 => ?_⟩
  c0_hsteps
  exact hQ () s2 m2 (hcore1.trans hcore2) hlen2 trivial hm2

end LeanQbe.T.Examples.Kissat.FullFidelityTumble

end
