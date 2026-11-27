/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3SearchRestart
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Spec
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Examples.Kissat.FullSpec2

/-!
# Kissat Fidelity Step 13 Shard S3-B Proofs — Part 1b (`FullFidelityStep13S3SearchRestartProof1b`)

Callee-parametric (`Γ : Env`, `XPost := False`, `0` SAT model proofs) `Func.wp` proofs for the
next `5` functions in `FullFidelityStep13S3SearchRestart`:
1. `full_m7_state_init_step13_wp` (`step13M7StateInitSpec`)
2. `full_randec_var_lvl_fid_step13_wp` (`step13RandecVarLvlSpec`)
3. `full_randec_var_m7_step13_wp` (`FullM7Search.m7RandecVarSpec`)
4. `full_ema_swap_m7_step13_wp` (`step13EmaSwapSpec`)
5. `full_switch_mode_m7_step13_wp` (`step13SwitchModeM6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM7Search
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. Shared Helpers -/

section Helpers

private theorem sr1b_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := by bv_omega

private theorem sr1b_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem sr1b_shl1 {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt h]

private theorem sr1b_probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem sr1b_probePres_trans {s0 s1 s2 : FullState}
    (h1 : FullProbeScratchPres s0 s1) (h2 : FullProbeScratchPres s1 s2) :
    FullProbeScratchPres s0 s2 :=
  ⟨⟨h2.1.1.trans h1.1.1, h2.1.2.trans h1.1.2⟩,
   h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2⟩

private theorem sr1b_call_get64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hGet : ∀ a m Q X, m7Get64Spec a m Q X → Γ "full_m7_get64" [i64, i64] [i64] a m Q X)
    {c : FullCfg} {idx : BitVec 64} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, idx, ())) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ v : BitVec 64,
      v = (if idx.toNat < 63 then m7Get64Val s.scratch.glue_used idx.toNat else 0#64) →
      wp Γ Q X (k (v, ())) m) :
    wp Γ Q X (.call "full_m7_get64" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hGet _ _ _ _ (m7Get64Spec_of hlen hm (hk _ rfl))

private theorem sr1b_call_set64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hSet : ∀ a m Q X, m7Set64Spec a m Q X → Γ "full_m7_set64" [i64, i64, i64] [] a m Q X)
    {c : FullCfg} {idx val : BitVec 64} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, idx, val, ())) (hidx_lo : 36 ≤ idx.toNat)
    (hidx_hi : idx.toNat < 63) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c →
      s'.scratch = { s.scratch with
        glue_used := m7Set64List s.scratch.glue_used idx.toNat val } →
      FullProbeScratchPres s s' → M7GuPrefixPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_m7_set64" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hSet _ _ _ _ (m7Set64Spec_of hlen hm ?_)
  dsimp only
  simp only [hidx_hi, ↓reduceIte]
  intro hlen' m' hm'
  exact hk { s with scratch := { s.scratch with
      glue_used := m7Set64List s.scratch.glue_used idx.toNat val } }
    m' rfl hlen' rfl (sr1b_probePres_refl _) (M7GuPrefixPres.of_set64 _ hidx_lo) hm'

private theorem sr1b_m7InitOk_of_set64_ge38 {gu : List (BitVec 32)} {idx : Nat} (val : BitVec 64)
    (hinit : M7StateInitOk gu) (hge : 38 ≤ idx) : M7StateInitOk (m7Set64List gu idx val) :=
  M7StateInitOk.of_set64 hinit hge val

private theorem sr1b_probePres_of_gu {s1 s2 : FullState} {gu : List (BitVec 32)}
    (h : s2.scratch = { s1.scratch with glue_used := gu }) : FullProbeScratchPres s1 s2 :=
  ⟨⟨by rw [h], by rw [h]⟩, by rw [h], by rw [h], by rw [h], by rw [h],
    by rw [h], by rw [h], by rw [h]⟩

end Helpers

/-! ## 2. `full_m7_state_init`, `full_randec_var_lvl_fid`, `full_randec_var_m7`, `ema_swap_m7` -/

/-- Step-13 `full_m7_state_init` (`init_exp = 0x3FF0000000000000ULL`) satisfies
`step13M7StateInitSpec`. -/
theorem full_m7_state_init_step13_wp (Γ : Env)
    (hGet64 : ∀ a m Q X, m7Get64Spec a m Q X → Γ "full_m7_get64" [i64, i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m7Set64Spec a m Q X → Γ "full_m7_set64" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, step13M7StateInitSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_m7_state_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [Func.wp, FullFidelityStep13S3.full_m7_state_init_body]
  c0_hsteps_nogrp
  refine sr1b_call_get64 (idx := 36#64) hGet64 rfl hlen hm fun mg hmg => ?_
  c0_hsteps_nogrp
  · have hok : M7StateInitOk s.scratch.glue_used := by
      refine M7StateInitOk.of_fields hlen.scratch_ok.glue_used_len ?_
      have h36 : (36#64 : BitVec 64).toNat < 63 := by decide
      simp only [h36, ↓reduceIte] at hmg
      change mg = m7Get64Val s.scratch.glue_used 36 at hmg
      rw [m7GuMagicIdx_eq, m7SearchMagic_eq, ← hmg]; exact hc
    exact hQ s.scratch.glue_used m hlen hok (M7GuPrefixPres.refl s) hm
  · refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen hm
      fun s1 m1 hcore1 hlen1 hsc1 _ hpre1 hm1 => ?_
    have hinit1 : M7StateInitOk s1.scratch.glue_used := by
      refine M7StateInitOk.of_fields hlen1.scratch_ok.glue_used_len ?_
      rw [m7GuMagicIdx_eq, m7SearchMagic_eq, hsc1]
      exact m7Get64Val_set64_self _ (by rw [hlen.scratch_ok.glue_used_len]; decide)
    refine wp_join_group (ts := [i64]) (fun _ m2 => m1 = m2)
      (fun _ ⟨cm, ⟨⟩⟩ m2 hm2 => ?_)
      (fun Jcm hJcm => by c0_hsteps <;> exact hJcm (_, ()) m1 rfl)
    rcases hm2 with rfl
    c0_hsteps_nogrp
    refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen1 hm1
      fun s2 m2 hcore2 hlen2 hsc2 _ hpre2 hm2 => ?_
    have hinit2 : M7StateInitOk s2.scratch.glue_used := by
      rw [hsc2]; exact sr1b_m7InitOk_of_set64_ge38 _ hinit1 (by decide)
    have hpre20 : M7GuPrefixPres s s2 := M7GuPrefixPres.trans hpre1 hpre2
    c0_hsteps_nogrp
    refine wp_join_group (ts := [])
      (fun _ m3 => ∃ gu3, let s3 : FullState := { s with scratch := { s.scratch with
        glue_used := gu3 } }
        s3.LengthsOk c ∧ M7StateInitOk gu3 ∧ M7GuPrefixPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
      (fun _ ⟨⟩ m3 ⟨gu3, hlen3, hinit3, hpre3, hm3⟩ => by
        let s3 : FullState := { s with scratch := { s.scratch with glue_used := gu3 } }
        c0_hsteps_nogrp
        refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen3 hm3
          fun s4 m4 hcore4 hlen4 hsc4 _ hpre4 hm4 => ?_; c0_hsteps_nogrp
        refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen4 hm4
          fun s5 m5 hcore5 hlen5 hsc5 _ hpre5 hm5 => ?_; c0_hsteps_nogrp
        refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen5 hm5
          fun s6 m6 hcore6 hlen6 hsc6 _ hpre6 hm6 => ?_; c0_hsteps_nogrp
        refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen6 hm6
          fun s7 m7 hcore7 hlen7 hsc7 _ hpre7 hm7 => ?_
        have hinit7 : M7StateInitOk s7.scratch.glue_used := by
          rw [hsc7, hsc6, hsc5, hsc4]
          exact sr1b_m7InitOk_of_set64_ge38 _ (sr1b_m7InitOk_of_set64_ge38 _
            (sr1b_m7InitOk_of_set64_ge38 _ (sr1b_m7InitOk_of_set64_ge38 _ hinit3 (by decide))
              (by decide)) (by decide)) (by decide)
        have hpre7 : M7GuPrefixPres s s7 :=
          hpre3.trans (hpre4.trans (hpre5.trans (hpre6.trans hpre7)))
        have hs7_eq : s7 = { s with scratch :=
            { s.scratch with glue_used := s7.scratch.glue_used } } := by
          cases s7; dsimp only [s3] at hcore4 hcore5 hcore6 hcore7 hsc4 hsc5 hsc6 hsc7 ⊢
          simp [hcore7, hcore6, hcore5, hcore4, hsc7, hsc6, hsc5, hsc4]
        c0_hsteps; exact hQ s7.scratch.glue_used m7 (by rwa [← hs7_eq]) hinit7
          (by rwa [← hs7_eq]) (by rwa [← hs7_eq]))
      (fun Je hJe => by
        have hs2_eq : s2 = { s with scratch :=
            { s.scratch with glue_used := s2.scratch.glue_used } } := by
          cases s2; dsimp only at hcore1 hcore2 hsc1 hsc2 ⊢
          simp [hcore2.trans hcore1, hsc2, hsc1]
        c0_hsplit
        · c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen2 hm2
            fun sa1 ma1 hca1 hla1 hsa1 _ hpa1 hma1 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla1 hma1
            fun sa2 ma2 hca2 hla2 hsa2 _ hpa2 hma2 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla2 hma2
            fun sa3 ma3 hca3 hla3 hsa3 _ hpa3 hma3 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla3 hma3
            fun sa4 ma4 hca4 hla4 hsa4 _ hpa4 hma4 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla4 hma4
            fun sa5 ma5 hca5 hla5 hsa5 _ hpa5 hma5 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla5 hma5
            fun sa6 ma6 hca6 hla6 hsa6 _ hpa6 hma6 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla6 hma6
            fun sa7 ma7 hca7 hla7 hsa7 _ hpa7 hma7 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla7 hma7
            fun sa8 ma8 hca8 hla8 hsa8 _ hpa8 hma8 => ?_
          have hia8 : M7StateInitOk sa8.scratch.glue_used := by
            rw [hsa8, hsa7, hsa6, hsa5, hsa4, hsa3, hsa2, hsa1]
            iterate 8 (refine sr1b_m7InitOk_of_set64_ge38 _ ?_ (by decide))
            exact hinit2
          have hsa8_eq : sa8 = { s with scratch :=
              { s.scratch with glue_used := sa8.scratch.glue_used } } := by
            cases sa8; dsimp only at *; rw [hs2_eq] at hsa1
            simp [hca8, hca7, hca6, hca5, hca4, hca3, hca2, hca1, hcore2, hcore1,
              hsa8, hsa7, hsa6, hsa5, hsa4, hsa3, hsa2, hsa1]
          c0_hsteps; exact hJe () ma8 ⟨sa8.scratch.glue_used, by rwa [← hsa8_eq], hia8,
            (by rw [← hsa8_eq]; exact hpre20.trans (hpa1.trans (hpa2.trans (hpa3.trans (hpa4.trans
              (hpa5.trans (hpa6.trans (hpa7.trans hpa8)))))))), by rwa [← hsa8_eq]⟩
        · c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen2 hm2
            fun sa1 ma1 hca1 hla1 hsa1 _ hpa1 hma1 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla1 hma1
            fun sa2 ma2 hca2 hla2 hsa2 _ hpa2 hma2 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla2 hma2
            fun sa3 ma3 hca3 hla3 hsa3 _ hpa3 hma3 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla3 hma3
            fun sa4 ma4 hca4 hla4 hsa4 _ hpa4 hma4 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla4 hma4
            fun sa5 ma5 hca5 hla5 hsa5 _ hpa5 hma5 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla5 hma5
            fun sa6 ma6 hca6 hla6 hsa6 _ hpa6 hma6 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla6 hma6
            fun sa7 ma7 hca7 hla7 hsa7 _ hpa7 hma7 => ?_; c0_hsteps_nogrp
          refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla7 hma7
            fun sa8 ma8 hca8 hla8 hsa8 _ hpa8 hma8 => ?_
          have hia8 : M7StateInitOk sa8.scratch.glue_used := by
            rw [hsa8, hsa7, hsa6, hsa5, hsa4, hsa3, hsa2, hsa1]
            iterate 8 (refine sr1b_m7InitOk_of_set64_ge38 _ ?_ (by decide))
            exact hinit2
          have hsa8_eq : sa8 = { s with scratch :=
              { s.scratch with glue_used := sa8.scratch.glue_used } } := by
            cases sa8; dsimp only at *; rw [hs2_eq] at hsa1
            simp [hca8, hca7, hca6, hca5, hca4, hca3, hca2, hca1, hcore2, hcore1,
              hsa8, hsa7, hsa6, hsa5, hsa4, hsa3, hsa2, hsa1]
          c0_hsteps; exact hJe () ma8 ⟨sa8.scratch.glue_used, by rwa [← hsa8_eq], hia8,
            (by rw [← hsa8_eq]; exact hpre20.trans (hpa1.trans (hpa2.trans (hpa3.trans (hpa4.trans
              (hpa5.trans (hpa6.trans (hpa7.trans hpa8)))))))), by rwa [← hsa8_eq]⟩)

/-- Step-13 `full_randec_var_lvl_fid` satisfies `step13RandecVarLvlSpec`. -/
theorem full_randec_var_lvl_fid_step13_wp (Γ : Env)
    (hInit : ∀ a m Q X, step13M7StateInitSpec a m Q X →
      Γ "full_m7_state_init" [i64] [] a m Q X)
    (hGet64 : ∀ a m Q X, m7Get64Spec a m Q X → Γ "full_m7_get64" [i64, i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m7Set64Spec a m Q X → Γ "full_m7_set64" [i64, i64, i64] [] a m Q X)
    (hLog : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hTo : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hLcg : ∀ a m Q X, m7LcgNextSpec a m Q X → Γ "full_lcg_next_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, step13RandecVarLvlSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_randec_var_lvl_fid_body a m Q X := by
  rintro ⟨h, max_lvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hcv_le := hlen.core_ok.cur_vars_le
  have hretFF : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' →
      M7GuPrefixPres s s' → (FullMem c s' ⋆ R) m' → Q (0xFFFFFFFFFFFFFFFF#64, ()) m' :=
    fun s' m' hc' hl' hp' hg' hm' => hQ (0xFFFFFFFFFFFFFFFF#64, ()) s' m' hc' hl'
      ⟨hp', hg', Or.inl rfl⟩ hm'
  dsimp only [Func.wp, FullFidelityStep13S3.full_randec_var_lvl_fid_body]
  c0_hsplit
  · c0_hsteps; exact hretFF s m rfl hlen (sr1b_probePres_refl _) (M7GuPrefixPres.refl _) hm
  have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h => hc (by rw [h]; rfl)
  clear hc; c0_hsplit
  · c0_hsteps; exact hretFF s m rfl hlen (sr1b_probePres_refl _) (M7GuPrefixPres.refl _) hm
  clear hc; c0_hsplit
  · c0_hsteps; exact hretFF s m rfl hlen (sr1b_probePres_refl _) (M7GuPrefixPres.refl _) hm
  clear hc; c0_hsteps_nogrp
  c0_call hInit
  refine ⟨c, s, R, rfl, hlen, hm, fun gu1 m1 hlen1 _ hpre1 hm1 => ?_⟩
  let s1 : FullState := { s with scratch := { s.scratch with glue_used := gu1 } }
  c0_hsteps_nogrp
  refine sr1b_call_get64 hGet64 rfl hlen1 hm1 fun rem0 _ => ?_
  c0_hsteps_nogrp
  refine sr1b_call_get64 hGet64 rfl hlen1 hm1 fun lc0 _ => ?_
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (rem1, ()) m2 => ∃ s2, s2.core = s.core ∧ s2.LengthsOk c ∧
      FullProbeScratchPres s s2 ∧ M7GuPrefixPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ ⟨rem1, ⟨⟩⟩ m2 ⟨s2, hcore2, hlen2, hps2, hpre2, hm2⟩ => ?_)
    (fun Jc hJc => by
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ mA => m1 = mA)
          (fun _ ⟨rem', ⟨⟩⟩ mA hmA => by
            rcases hmA with rfl; c0_hsteps_nogrp
            refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen1 hm1
              fun sA mA hca hla _ hpsa hpa hma => ?_
            c0_hsteps_nogrp
            refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla hma
              fun sB mB hcb hlb _ hpsb hpb hmb => ?_
            c0_hsteps; exact hJc (rem', ()) mB ⟨sB, hcb.trans hca, hlb,
              sr1b_probePres_trans hpsa hpsb, hpre1.trans (hpa.trans hpb), hmb⟩)
          (fun Jd hJd => by c0_hsteps <;> exact hJd (_, ()) m1 rfl)
      · c0_hsteps; exact hJc (rem0, ()) m1 ⟨s1, rfl, hlen1, sr1b_probePres_refl _, hpre1, hm1⟩)
  refine wp_join_group (ts := [i64])
    (fun _ m3 => ∃ s3, s3.core = s.core ∧ s3.LengthsOk c ∧ FullProbeScratchPres s s3 ∧
      M7GuPrefixPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
    (fun _ ⟨_, ⟨⟩⟩ m3 ⟨s3, hcore3, hlen3, hps3, hpre3, hm3⟩ => ?_)
    (fun Jr hJr => by
      c0_hsplit
      · c0_hsplit
        · c0_hsteps; exact hretFF s2 m2 hcore2 hlen2 hps2 hpre2 hm2
        · c0_hsteps_nogrp
          refine sr1b_call_get64 hGet64 rfl hlen2 hm2 fun lim _ => ?_
          c0_hsplit
          · c0_hsteps; exact hretFF s2 m2 hcore2 hlen2 hps2 hpre2 hm2
          · c0_hsteps_nogrp
            refine sr1b_call_get64 hGet64 rfl hlen2 hm2 fun seq0 _ => ?_
            c0_hsteps_nogrp
            refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen2 hm2
              fun sA mA hca hla _ hpsa hpa hma => ?_
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ mB => mA = mB)
              (fun _ ⟨qarg, ⟨⟩⟩ mB hmB => by
                rcases hmB with rfl; c0_hsteps_nogrp
                c0_call hLog; intro lg; c0_hsteps_nogrp
                c0_call hMul; intro _; c0_hsteps_nogrp
                c0_call hTo; intro _; c0_hsteps_nogrp
                refine wp_join_group (ts := [i64]) (fun _ mC => mA = mC)
                  (fun _ ⟨len, ⟨⟩⟩ mC hmC => by
                    rcases hmC with rfl; c0_hsteps_nogrp
                    c0_call hMul; intro _; c0_hsteps_nogrp
                    c0_call hTo; intro _; c0_hsteps_nogrp
                    refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hla hma
                      fun sB mB hcb hlb _ hpsb hpb hmb => ?_
                    c0_hsteps_nogrp
                    refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlb hmb
                      fun sC mC hcc hlc _ hpsc hpc hmc => ?_
                    c0_hsteps
                    exact hJr (len, ()) mC ⟨sC, hcc.trans (hcb.trans (hca.trans hcore2)),
                      hlc, sr1b_probePres_trans hps2
                        (sr1b_probePres_trans hpsa (sr1b_probePres_trans hpsb hpsc)),
                      hpre2.trans (hpa.trans (hpb.trans hpc)), hmc⟩)
                  (fun Jl hJl => by c0_hsteps <;> exact hJl (_, ()) mA rfl))
              (fun Jq hJq => by c0_hsteps <;> exact hJq (_, ()) mA rfl)
      · c0_hsteps; exact hJr (rem1, ()) m2 ⟨s2, hcore2, hlen2, hps2, hpre2, hm2⟩)
  -- Random sampling loop (`tries < max_tries`)
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (mt, ()) m4 => m3 = m4 ∧ mt.toNat ≤ 16396)
    (fun _ ⟨mt, ⟨⟩⟩ m4 ⟨hm4, hmt⟩ => ?_)
    (fun Jm hJm => by
      c0_hsplit
      · have hcv4k : s.core.cur_vars < 4096 := by
          rw [show (4096 : BitVec 64).toNat = 4096 from rfl,
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
        c0_hsteps; exact hJm (_, ()) m3 ⟨rfl, by
          have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
            bv64_ofNat_toNat (by omega)
          rw [BitVec.toNat_add, BitVec.toNat_mul, hcv64,
            show (4 : BitVec 64).toNat = 4 from rfl, show (16 : BitVec 64).toNat = 16 from rfl,
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars * 4 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars * 4 + 16 < 2 ^ 64)]; omega⟩
      · c0_hsteps; exact hJm (16384#64, ()) m3 ⟨rfl, by decide⟩)
  rcases hm4 with rfl
  refine wp_loop_group (ts := [i64])
    (fun fnT ⟨tr, ⟨⟩⟩ mT => tr.toNat ≤ mt.toNat ∧ fnT = mt.toNat - tr.toNat ∧
      ∃ sT, sT.core = s.core ∧ sT.LengthsOk c ∧ FullProbeScratchPres s sT ∧
        M7GuPrefixPres s sT ∧ (FullMem c sT ⋆ R) mT) ?_ ?_
  · intro JT fnT ⟨tr, ⟨⟩⟩ mT hJT ⟨htr_le, hfnT, sT, hcoreT, hlenT, hpsT, hpreT, hmT⟩
    c0_hsplit
    · have htr_lt : tr.toNat < mt.toNat := hc
      clear hc
      have htr1 : (tr + 1).toNat = tr.toNat + 1 := sr1b_add1 (by omega)
      c0_hsteps_nogrp
      refine wp_call_of_spec _ _ (hLcg _ _ _ _ (m7LcgNextSpec_of hlenT hmT ?_))
      intro lcg sU mU hcoreU hlenU ⟨_, hscU⟩ hmU
      have hcoreU0 : sU.core = s.core := hcoreU.trans hcoreT
      have hpsU : FullProbeScratchPres s sU :=
        sr1b_probePres_trans hpsT ⟨⟨by rw [hscU], by rw [hscU]⟩, by rw [hscU], by rw [hscU],
          by rw [hscU], by rw [hscU], by rw [hscU], by rw [hscU], by rw [hscU]⟩
      have hpreU : M7GuPrefixPres s sU :=
        hpreT.trans (M7GuPrefixPres.of_forall fun k _ => by rw [hscU])
      let idx := lcg % BitVec.ofNat 64 s.core.cur_vars
      have hidx_lt : idx.toNat < s.core.cur_vars := by
        dsimp only [idx]; rw [BitVec.toNat_umod, bv64_ofNat_toNat (by omega)]
        exact Nat.mod_lt _ hcv_pos
      have hidx_fl : idx.toNat < sU.core.flags.length := by
        rw [hcoreU0, hlen.core_ok.flags_len]; omega
      have h2idx_eq : (idx <<< (1 : Nat)).toNat = 2 * idx.toNat := sr1b_shl1 (by omega)
      have h2idx_v : (idx <<< (1 : Nat)).toNat < sU.core.vals.length := by
        rw [h2idx_eq, hcoreU0, hlen.core_ok.vals_len]; omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun _ mN => mU = mN)
        (fun _ ⟨⟩ mN hmN => by
          rcases hmN with rfl; c0_hsteps
          exact hJT (mt.toNat - (tr.toNat + 1)) _ mU (by omega)
            ⟨by rw [htr1]; omega, by rw [htr1], sU, hcoreU0, hlenU, hpsU, hpreU, hmU⟩)
        (fun Jc hJc => by
          c0_hsplit; rotate_left; · c0_hsteps; exact hJc () mU rfl
          have hfl_ne : (sU.core.flags[idx.toNat]'hidx_fl &&& 1#32) ≠ 0#32 := hc
          clear hc
          c0_hsplit; rotate_left; · c0_hsteps; exact hJc () mU rfl
          c0_hsteps
          refine hQ (idx, ()) sU mU hcoreU0 hlenU ⟨hpsU, hpreU, Or.inr ⟨hidx_lt, ?_, ?_⟩⟩ hmU
          · dsimp only
            rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.flags_len]; omega),
              Option.getD_some]
            simpa [hcoreU0] using hfl_ne
          · dsimp only
            rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.vals_len]; omega),
              Option.getD_some]
            have hv0 : (sU.core.vals[2 * idx.toNat]'(by
                rw [hcoreU0, hlen.core_ok.vals_len]; omega)).signExtend 32 = 0#32 := by
              have h2eq : 2 * idx.toNat % 2 ^ 64 = 2 * idx.toNat :=
                Nat.mod_eq_of_lt (by omega)
              have hmod2 : 2 * (lcg % BitVec.ofNat 64 s.core.cur_vars).toNat % 2 ^ 64 =
                  2 * idx.toNat := h2eq
              simpa only [hmod2] using hc
            have hv8 : sU.core.vals[2 * idx.toNat]'(by
                rw [hcoreU0, hlen.core_ok.vals_len]; omega) = 0#8 := by
              ext i hi; have h1 := congrArg (·[i]) hv0
              simp [BitVec.getElem_signExtend, hi] at h1; simp [h1]
            simpa [hcoreU0] using hv8)
    · c0_hsteps; exact hretFF sT mT hcoreT hlenT hpsT hpreT hmT
  · intro JT hJT; c0_hsteps
    exact hJT mt.toNat (0#64, ()) m3
      ⟨Nat.zero_le _, by simp, s3, hcore3, hlen3, hps3, hpre3, hm3⟩

/-- Step-13 `full_randec_var_m7` forwards to `full_randec_var_lvl_fid(h, 0)` and satisfies
`FullM7Search.m7RandecVarSpec`. -/
theorem full_randec_var_m7_step13_wp (Γ : Env)
    (hLvl : ∀ a m Q X, step13RandecVarLvlSpec a m Q X →
      Γ "full_randec_var_lvl_fid" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m7RandecVarSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_randec_var_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, R, rfl, hlen, hm, hQ⟩ := m7RandecVarSpec_elim hs
  dsimp only [Func.wp, FullFidelityStep13S3.full_randec_var_m7_body]
  c0_call hLvl
  exact ⟨c, s, R, rfl, hlen, hm, fun ⟨r, ⟨⟩⟩ s' m' hc hl hp hm' => hQ r s' m' hc hl hp hm'⟩

/-- Step-13 `full_ema_swap_m7` (`init_exp = 0x3FF0000000000000ULL`) satisfies
`step13EmaSwapSpec`. -/
theorem full_ema_swap_m7_step13_wp (Γ : Env)
    (hInit : ∀ a m Q X, step13M7StateInitSpec a m Q X →
      Γ "full_m7_state_init" [i64] [] a m Q X)
    (hGet64 : ∀ a m Q X, m7Get64Spec a m Q X → Γ "full_m7_get64" [i64, i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m7Set64Spec a m Q X → Γ "full_m7_set64" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, step13EmaSwapSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_ema_swap_m7_body a m Q X := by
  rintro ⟨h, old_m, new_m, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  dsimp only [Func.wp, FullFidelityStep13S3.full_ema_swap_m7_body]
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (om, ()) m1 => m = m1 ∧ (om = 0#64 ∨ om = 1#64))
    (fun _ ⟨om, ⟨⟩⟩ m1 ⟨hm1, hom⟩ => ?_)
    (fun J hJ => by c0_hsteps; · exact hJ (1#64, ()) m ⟨rfl, Or.inr rfl⟩
                    · exact hJ (0#64, ()) m ⟨rfl, Or.inl rfl⟩)
  rcases hm1 with rfl
  refine wp_join_group (ts := [i64]) (fun (nm, ()) m2 => m = m2 ∧ (nm = 0#64 ∨ nm = 1#64))
    (fun _ ⟨nm, ⟨⟩⟩ m2 ⟨hm2, hnm⟩ => ?_)
    (fun J hJ => by c0_hsteps; · exact hJ (1#64, ()) m ⟨rfl, Or.inr rfl⟩
                    · exact hJ (0#64, ()) m ⟨rfl, Or.inl rfl⟩)
  rcases hm2 with rfl
  c0_hsteps_nogrp
  let s1 : FullState := { s with scratch := { s.scratch with stable := om } }
  have hlen1 : s1.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
  c0_call hInit
  refine ⟨c, s1, R, rfl, hlen1, ‹_›, fun gu1 m1 hlen2 hinit2 hpre2 hm1 => ?_⟩
  let s2 : FullState := { s1 with scratch := { s1.scratch with glue_used := gu1 } }
  c0_hsteps_nogrp
  let s3 : FullState := { s2 with scratch := { s2.scratch with stable := nm } }
  have hlen3 : s3.LengthsOk c := ⟨hlen2.core_ok, { hlen2.scratch_ok with }⟩
  refine wp_join_group (ts := [i64])
    (fun (ob, ()) m3 => (FullMem c s3 ⋆ R) m3 ∧ (ob = 40#64 ∨ ob = 48#64))
    (fun _ ⟨ob, ⟨⟩⟩ m3 ⟨hm3, hob⟩ => ?_)
    (fun J hJ => by c0_hsteps; · exact hJ (40#64, ()) _ ⟨‹_›, Or.inl rfl⟩
                    · exact hJ (48#64, ()) _ ⟨‹_›, Or.inr rfl⟩)
  have hob_lo : 40 ≤ ob.toNat := by rcases hob with rfl | rfl <;> decide
  have hob_hi : ob.toNat ≤ 48 := by rcases hob with rfl | rfl <;> decide
  c0_hsteps_nogrp
  refine sr1b_call_set64 (idx := ob) hSet64 rfl (by omega) (by omega) hlen3 hm3
    fun sa1 ma1 hca1 hla1 hsa1 hpsa1 hpa1 hma1 => ?_; c0_hsteps_nogrp
  refine sr1b_call_set64 (idx := ob + 2#64) hSet64 rfl (by bv_omega) (by bv_omega) hla1 hma1
    fun sa2 ma2 hca2 hla2 hsa2 hpsa2 hpa2 hma2 => ?_; c0_hsteps_nogrp
  refine sr1b_call_set64 (idx := ob + 4#64) hSet64 rfl (by bv_omega) (by bv_omega) hla2 hma2
    fun sa3 ma3 hca3 hla3 hsa3 hpsa3 hpa3 hma3 => ?_; c0_hsteps_nogrp
  refine sr1b_call_set64 (idx := ob + 6#64) hSet64 rfl (by bv_omega) (by bv_omega) hla3 hma3
    fun sa4 ma4 hca4 hla4 hsa4 hpsa4 hpa4 hma4 => ?_; c0_hsteps_nogrp
  have hinit4 : M7StateInitOk sa4.scratch.glue_used := by
    rw [hsa4, hsa3, hsa2, hsa1]
    exact sr1b_m7InitOk_of_set64_ge38 _ (sr1b_m7InitOk_of_set64_ge38 _
      (sr1b_m7InitOk_of_set64_ge38 _ (sr1b_m7InitOk_of_set64_ge38 _ hinit2 (by omega))
        (by bv_omega)) (by bv_omega)) (by bv_omega)
  have hcore4 : sa4.core = s.core := hca4.trans (hca3.trans (hca2.trans hca1))
  have hpre_s1 : M7GuPrefixPres s s1 := M7GuPrefixPres.of_forall fun _ _ => rfl
  have hpre_s3 : M7GuPrefixPres s2 s3 := M7GuPrefixPres.of_forall fun _ _ => rfl
  have hpre4 : M7GuPrefixPres s sa4 :=
    hpre_s1.trans (hpre2.trans (hpre_s3.trans (hpa1.trans (hpa2.trans (hpa3.trans hpa4)))))
  have hps4 : FullProbeScratchPres s sa4 :=
    sr1b_probePres_trans (sr1b_probePres_refl _)
      (sr1b_probePres_trans hpsa1 (sr1b_probePres_trans hpsa2 (sr1b_probePres_trans hpsa3 hpsa4)))
  refine sr1b_call_get64 hGet64 rfl hla4 hma4 fun msk0 _ => ?_
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (nb, ()) m4 => m4 = ma4 ∧ (nb = 40#64 ∨ nb = 48#64))
    (fun _ ⟨nb, ⟨⟩⟩ m4 ⟨hm4, hnb⟩ => ?_)
    (fun J hJ => by c0_hsteps; · exact hJ (40#64, ()) ma4 ⟨rfl, Or.inl rfl⟩
                    · exact hJ (48#64, ()) ma4 ⟨rfl, Or.inr rfl⟩)
  subst hm4
  have hnb_lo : 40 ≤ nb.toNat := by rcases hnb with rfl | rfl <;> decide
  have hnb_hi : nb.toNat ≤ 48 := by rcases hnb with rfl | rfl <;> decide
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (msk1, ()) m5 => ∃ s5, s5.core = s.core ∧ s5.LengthsOk c ∧ FullProbeScratchPres s s5 ∧
      M7GuPrefixPres s s5 ∧ M7StateInitOk s5.scratch.glue_used ∧ (FullMem c s5 ⋆ R) m5)
    (fun _ ⟨msk1, ⟨⟩⟩ m5 ⟨s5, hcore5, hlen5, hps5, hpre5, hinit5, hm5⟩ => by
      c0_hsteps_nogrp
      refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen5 hm5
        fun s6 m6 hcore6 hlen6 hsc6 hps6 hpre6 hm6 => ?_
      have hinit6 : M7StateInitOk s6.scratch.glue_used := by
        rw [hsc6]; exact sr1b_m7InitOk_of_set64_ge38 _ hinit5 (by decide)
      c0_hsteps; exact hQ () s6 m6 (hcore6.trans hcore5) hlen6
        ⟨sr1b_probePres_trans hps5 hps6, hpre5.trans hpre6, hinit6⟩ hm6)
    (fun Jm hJm => by
      c0_hsplit
      · c0_hsteps_nogrp
        refine sr1b_call_get64 hGet64 rfl hla4 hma4 fun v1 _ => ?_; c0_hsteps_nogrp
        let sb1 : FullState := { sa4 with scratch := { sa4.scratch with ema_fast_biased := v1 } }
        have hlb1 : sb1.LengthsOk c := ⟨hla4.core_ok, { hla4.scratch_ok with }⟩
        refine sr1b_call_get64 hGet64 rfl hlb1 ‹_› fun v2 _ => ?_; c0_hsteps_nogrp
        let sb2 : FullState := { sb1 with scratch := { sb1.scratch with ema_fast_exp := v2 } }
        have hlb2 : sb2.LengthsOk c := ⟨hla4.core_ok, { hla4.scratch_ok with }⟩
        refine sr1b_call_get64 hGet64 rfl hlb2 ‹_› fun v3 _ => ?_; c0_hsteps_nogrp
        let sb3 : FullState := { sb2 with scratch := { sb2.scratch with ema_slow_biased := v3 } }
        have hlb3 : sb3.LengthsOk c := ⟨hla4.core_ok, { hla4.scratch_ok with }⟩
        refine sr1b_call_get64 hGet64 rfl hlb3 ‹_› fun v4 _ => ?_; c0_hsteps
        let sb4 : FullState := { sb3 with scratch := { sb3.scratch with ema_slow_exp := v4 } }
        have hpre_sb4 : M7GuPrefixPres sa4 sb4 := M7GuPrefixPres.of_forall fun _ _ => rfl
        exact hJm (_, ()) _ ⟨sb4, hcore4, ⟨hla4.core_ok, { hla4.scratch_ok with }⟩, hps4,
          hpre4.trans hpre_sb4, hinit4, ‹_›⟩
      · c0_hsteps_nogrp
        let sc0 : FullState := { sa4 with scratch := { sa4.scratch with
          ema_fast_biased := 0#64, ema_fast_exp := 0x3FF0000000000000#64,
          ema_slow_biased := 0#64, ema_slow_exp := 0x3FF0000000000000#64 } }
        have hlc0 : sc0.LengthsOk c := ⟨hla4.core_ok, { hla4.scratch_ok with }⟩
        refine sr1b_call_set64 (idx := nb) hSet64 rfl (by omega) (by omega) hlc0 ‹_›
          fun sc1 mc1 hcc1 hlc1 hsc1 hpsc1 hpc1 hmc1 => ?_; c0_hsteps_nogrp
        refine sr1b_call_set64 (idx := nb + 2#64) hSet64 rfl (by bv_omega) (by bv_omega) hlc1 hmc1
          fun sc2 mc2 hcc2 hlc2 hsc2 hpsc2 hpc2 hmc2 => ?_; c0_hsteps_nogrp
        refine sr1b_call_set64 (idx := nb + 4#64) hSet64 rfl (by bv_omega) (by bv_omega) hlc2 hmc2
          fun sc3 mc3 hcc3 hlc3 hsc3 hpsc3 hpc3 hmc3 => ?_; c0_hsteps_nogrp
        refine sr1b_call_set64 (idx := nb + 6#64) hSet64 rfl (by bv_omega) (by bv_omega) hlc3 hmc3
          fun sc4 mc4 hcc4 hlc4 hsc4 hpsc4 hpc4 hmc4 => ?_; c0_hsteps
        have hic4 : M7StateInitOk sc4.scratch.glue_used := by
          rw [hsc4, hsc3, hsc2, hsc1]
          exact sr1b_m7InitOk_of_set64_ge38 _ (sr1b_m7InitOk_of_set64_ge38 _
            (sr1b_m7InitOk_of_set64_ge38 _ (sr1b_m7InitOk_of_set64_ge38 _ hinit4 (by omega))
              (by bv_omega)) (by bv_omega)) (by bv_omega)
        have hpre_sc0 : M7GuPrefixPres sa4 sc0 := M7GuPrefixPres.of_forall fun _ _ => rfl
        exact hJm (_, ()) mc4 ⟨sc4, hcc4.trans (hcc3.trans (hcc2.trans (hcc1.trans hcore4))),
          hlc4, sr1b_probePres_trans hps4 (sr1b_probePres_trans hpsc1 (sr1b_probePres_trans hpsc2
            (sr1b_probePres_trans hpsc3 hpsc4))),
          hpre4.trans (hpre_sc0.trans (hpc1.trans (hpc2.trans (hpc3.trans hpc4)))), hic4, hmc4⟩)

/-! ## 3. `full_switch_mode_m7` (`step13SwitchModeM6Spec`) -/

section SwitchModeStep13

open scoped FullM6Hdr.M6HdrTactics

/-- Step-13 `full_switch_mode_m7` satisfies `step13SwitchModeM6Spec`: `FullM6HdrMem`-threaded
mode switch calling `m6_wm4_{get,set}`, `m6_hdr_dr_init`, `full_heap_{up,down,push}`,
`full_ema_swap_m7`, `full_ilog10`, `full_m7_{get,set}64`, and `f64u_*`. -/
theorem full_switch_mode_m7_step13_wp (Γ : Env)
    (hWm4Get : ∀ a m Q X, m6HdrW2aSpec [] [i64] a m Q X →
      Γ "m6_wm4_get" [i64] [i64] a m Q X)
    (hWm4Set : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_wm4_set" [i64, i64] [] a m Q X)
    (hHeapUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hHeapDown : ∀ a m Q X, fullHeapDownSpec a m Q X → Γ "full_heap_down" [i64, i32] [] a m Q X)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X → Γ "full_heap_push" [i64, i32] [] a m Q X)
    (hNlog : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_nlogpown" [i64, i64] [i64] a m Q X)
    (hTo : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hEmaSwap : ∀ a m Q X, step13EmaSwapSpec a m Q X →
      Γ "full_ema_swap_m7" [i64, i64, i64] [] a m Q X)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_init" [i64] [] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hGet64 : ∀ a m Q X, m7Get64Spec a m Q X → Γ "full_m7_get64" [i64, i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m7Set64Spec a m Q X → Γ "full_m7_set64" [i64, i64, i64] [] a m Q X)
    (hLog : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, step13SwitchModeM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_switch_mode_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hcv_le := hlen.core_ok.cur_vars_le
  rw [fullM6HdrMem_iff] at hm
  dsimp only [Func.wp, FullFidelityStep13S3.full_switch_mode_m7_body]
  refine wp_join_group (ts := [i64, i64])
    (fun _ mJ => ∃ extJ sJ, sJ.core = s.core ∧ sJ.LengthsOk c ∧ FullProbeScratchPres s sJ ∧
      M6HdrExtOk extJ ∧ (FullMem c sJ ⋆ (array64 (c.hdr - 2304) extJ ⋆ R)) mJ)
    (fun _ ⟨om, nm, ⟨⟩⟩ mJ ⟨extJ, sJ, hcoreJ, hlenJ, hpsJ, hextJ, hmJ⟩ => ?_)
    (fun Js hJs => ?_)
  · -- Shared tail after mode switch
    c0_hsteps_nogrp
    let sJ1 : FullState := { sJ with scratch := { sJ.scratch with
      switched := sJ.scratch.switched + 1#64, mode_count := sJ.scratch.mode_count + 1#64 } }
    have hlenJ1 : sJ1.LengthsOk c := ⟨hlenJ.core_ok, { hlenJ.scratch_ok with }⟩
    c0_call hEmaSwap
    refine ⟨c, sJ1, array64 (c.hdr - 2304) extJ ⋆ R, rfl, hlenJ1, ‹_›, ?_⟩
    rintro ⟨⟩ sSw mSw hcoreSw hlenSw ⟨hpsSw, _, _⟩ hmSw
    dsimp only [PreservesCoreSlice, fullSafetySlice] at hcoreSw hlenSw hmSw
    have hcoreSw0 : sSw.core = s.core := hcoreSw.trans hcoreJ
    have hpsSw0 : FullProbeScratchPres s sSw := sr1b_probePres_trans hpsJ hpsSw
    c0_hsteps_nogrp; c0_call hDrInit
    refine m6HdrDrMutSpec_of hcfg hextJ hlenSw ((fullM6HdrMem_iff ..).mpr hmSw)
      fun extD mD hinitD _ hmD => ?_
    have hlD : extD.length = 288 := hinitD.toOk.len
    have h1_lt : 1 < extD.length := by rw [hlD]; decide
    rw [fullM6HdrMem_iff] at hmD
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (mbit, ()) mD1 => (∃ extD1 : List (BitVec 64), extD1.length = 288 ∧
        (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD1 ⋆ R)) mD1) ∧
        (mbit = 0#64 ∨ mbit = 1#64))
      (fun _ ⟨mbit, ⟨⟩⟩ mD1 ⟨⟨extD1, hlD1, hmD1⟩, hmbit⟩ => ?_)
      (fun Jm hJm => by
        c0_hsteps
        · exact hJm (1#64, ()) _ ⟨⟨_, by rw [List.length_set, hlD], hm⟩, Or.inr rfl⟩
        · exact hJm (0#64, ()) _ ⟨⟨_, by rw [List.length_set, hlD], hm⟩, Or.inl rfl⟩)
    have hidx2_eq : ((2 : BitVec 64) + mbit).toNat = 2 + mbit.toNat := by
      rcases hmbit with rfl | rfl <;> decide
    have hidx2_lt : ((2 : BitVec 64) + mbit).toNat < extD1.length := by
      rw [hlD1, hidx2_eq]; rcases hmbit with rfl | rfl <;> decide
    c0_hsteps_nogrp
    have ⟨extD2, hlD2, hmD2⟩ : ∃ extD2 : List (BitVec 64), extD2.length = 288 ∧
        (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) m :=
      ⟨_, by rw [List.length_set, hlD1], hm⟩
    have hextD2 : M6HdrExtOk extD2 := M6HdrExtOk.of_len hlD2
    clear hm
    c0_hstep; c0_hsplit
    · -- Focused mode post-switch: restart_limit + randec update
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun _ mR => (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) mR)
        (fun _ ⟨d, ⟨⟩⟩ mR hmR => ?_)
        (fun Jd hJd => ?_)
      rotate_left
      · c0_hsplit; rotate_left; · c0_hsteps; exact hJd (1#64, ()) _ ‹_›
        refine wp_join_group (ts := [i64])
          (fun _ mA => (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) mA)
          (fun _ ⟨rc, ⟨⟩⟩ mA hmA => by
            c0_hsteps_nogrp; c0_call hIlog; intro d10 _ _; c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun _ mB => (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) mB)
              (fun _ ⟨d', ⟨⟩⟩ mB hmB => by c0_hsteps; exact hJd (d', ()) mB hmB)
              (fun J2 hJ2 => by c0_hsteps <;> exact hJ2 (_, ()) mA hmA))
          (fun J1 hJ1 => by c0_hsteps <;> exact hJ1 (_, ()) _ ‹_›)
      c0_hsteps_nogrp
      let sR0 : FullState := { sSw with scratch := { sSw.scratch with
        restart_limit := sSw.scratch.conflicts + d } }
      have hlenR0 : sR0.LengthsOk c := ⟨hlenSw.core_ok, { hlenSw.scratch_ok with }⟩
      refine sr1b_call_get64 hGet64 rfl hlenR0 ‹_› fun rem0 _ => ?_; c0_hsteps_nogrp
      refine sr1b_call_get64 hGet64 rfl hlenR0 ‹_› fun lc0 _ => ?_; c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun (rem1, ()) m1 => ∃ s1, s1.core = s.core ∧ s1.LengthsOk c ∧
          FullProbeScratchPres s s1 ∧
          (FullMem c s1 ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) m1)
        (fun _ ⟨rem1, ⟨⟩⟩ m1 ⟨s1, hcore1, hlen1, hps1, hm1⟩ => ?_)
        (fun Jc hJc => ?_)
      rotate_left
      · c0_hsplit; rotate_left
        · c0_hsteps; exact hJc (rem0, ()) _ ⟨sR0, hcoreSw0, hlenR0, hpsSw0, ‹_›⟩
        c0_hsteps_nogrp; refine wp_join_group (ts := [i64])
          (fun _ mA => (FullMem c sR0 ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) mA)
          (fun _ ⟨rem', ⟨⟩⟩ mA hmA => by
            c0_hsteps_nogrp
            refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlenR0 hmA
              fun sA mA hca hla _ hpsa _ hma => ?_
            c0_hsteps; exact hJc (rem', ()) mA ⟨sA, hca.trans hcoreSw0, hla,
              sr1b_probePres_trans hpsSw0 hpsa, hma⟩)
          (fun Jsub hJsub => by c0_hsteps <;> exact hJsub (_, ()) _ ‹_›)
      c0_hsteps_nogrp
      refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen1 hm1
        fun s2 m2 hcore2 hlen2 _ hps2 _ hm2 => ?_
      have hcore20 : s2.core = s.core := hcore2.trans hcore1
      have hps20 : FullProbeScratchPres s s2 := sr1b_probePres_trans hps1 hps2
      c0_hsteps_nogrp; c0_hstep; c0_hsplit
      · refine sr1b_call_get64 hGet64 rfl hlen2 hm2 fun seq0 _ => ?_; c0_hsteps_nogrp
        refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen2 hm2
          fun s3 m3 hcore3 hlen3 _ hps3 _ hm3 => ?_; c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ m4 => m3 = m4)
          (fun _ ⟨qarg, ⟨⟩⟩ m4 hm4 => by
            rcases hm4 with rfl; c0_hsteps_nogrp
            c0_call hLog; intro _; c0_hsteps_nogrp; c0_call hMul; intro _; c0_hsteps_nogrp
            c0_call hTo; intro _; c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m5 => m3 = m5)
              (fun _ ⟨rlen, ⟨⟩⟩ m5 hm5 => by
                rcases hm5 with rfl; c0_hsteps_nogrp
                c0_call hMul; intro _; c0_hsteps_nogrp; c0_call hTo; intro _; c0_hsteps_nogrp
                refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen3 hm3
                  fun s4 m4 hcore4 hlen4 _ hps4 _ hm4 => ?_; c0_hsteps_nogrp
                refine sr1b_call_set64 hSet64 rfl (by decide) (by decide) hlen4 hm4
                  fun s5 m5 hcore5 hlen5 _ hps5 _ hm5 => ?_; c0_hsteps
                exact hQ extD2 s5 m5 (hcore5.trans (hcore4.trans (hcore3.trans hcore20))) hlen5
                  (sr1b_probePres_trans hps20 (sr1b_probePres_trans hps3
                    (sr1b_probePres_trans hps4 hps5))) hextD2 ((fullM6HdrMem_iff ..).mpr hm5))
              (fun Jr hJr => by c0_hsteps <;> exact hJr (_, ()) m3 rfl))
          (fun Jq hJq => by c0_hsteps <;> exact hJq (_, ()) m3 rfl)
      · c0_hsteps
        exact hQ extD2 s2 m2 hcore20 hlen2 hps20 hextD2 ((fullM6HdrMem_iff ..).mpr hm2)
    · c0_hsteps
      exact hQ extD2 sSw _ hcoreSw0 hlenSw hpsSw0 hextD2 ((fullM6HdrMem_iff ..).mpr ‹_›)
  · -- Pre-join: Focused -> Stable vs Stable -> Focused
    c0_hsplit
    · -- `h->stable == 0` (Focused -> Stable)
      c0_hsplit
      · c0_hsteps
        exact hQ ext s m rfl hlen (sr1b_probePres_refl _) hext ((fullM6HdrMem_iff ..).mpr hm)
      c0_hsteps_nogrp
      let s1 : FullState := { s with scratch := { s.scratch with stable := 1#64 } }
      refine wp_join_group (ts := [i64])
        (fun _ m1 => (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
        (fun _ ⟨dticks, ⟨⟩⟩ m1 hm1 => ?_)
        (fun Jd hJd => by c0_hsteps <;> exact hJd (_, ()) _ ‹_›)
      c0_hsteps_nogrp
      let s2 : FullState := { s1 with scratch := { s1.scratch with
        mode_tick_lim := s1.scratch.search_ticks + dticks,
        mode_saved_ticks := s1.scratch.search_ticks } }
      refine wp_join_group (ts := [i64])
        (fun _ m2 => (FullMem c s2 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m2)
        (fun _ ⟨rp, ⟨⟩⟩ m2 hm2 => ?_)
        (fun Jr hJr => by
          c0_hsplit; · c0_hsplit <;> (c0_hsteps; exact hJr (_, ()) _ ‹_›)
          · c0_hsteps; exact hJr (_, ()) _ ‹_›)
      c0_hsteps_nogrp
      let s3 : FullState := { s2 with scratch := { s2.scratch with
        rel_wait := rp, rel_u := 1#64, rel_v := 1#64, rel_trigger := 0#64 } }
      have hlen3 : s3.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
      c0_call hWm4Get
      refine m6HdrW2aSpec_of rfl hcfg hext hlen3 ((fullM6HdrMem_iff ..).mpr ‹_›)
        fun ⟨wm4, ⟨⟩⟩ ext1 s4 m4 hcore4 hlen4 hm4p hext1 _ hm4 => ?_
      rw [fullM6HdrMem_iff] at hm4
      have hps4 : FullProbeScratchPres s s4 := hm4p.probePres
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun _ m5 => ∃ ext5 s5, s5.core = s.core ∧ s5.LengthsOk c ∧ FullProbeScratchPres s s5 ∧
          M6HdrExtOk ext5 ∧ (FullMem c s5 ⋆ (array64 (c.hdr - 2304) ext5 ⋆ R)) m5)
        (fun _ ⟨_, ⟨⟩⟩ m5 ⟨ext5, s5, hcore5, hlen5, hps5, hext5, hm5⟩ => ?_)
        (fun Jw hJw => ?_)
      · -- Push active vars onto heap (`v < cv`)
        refine wp_loop_group (ts := [i64])
          (fun fn ⟨v, ⟨⟩⟩ mV => v.toNat ≤ s.core.cur_vars ∧ fn = s.core.cur_vars - v.toNat ∧
            ∃ sV, sV.core = s.core ∧ sV.LengthsOk c ∧ FullProbeScratchPres s sV ∧
              (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext5 ⋆ R)) mV) ?_ ?_
        · intro JV fn ⟨v, ⟨⟩⟩ mV hJV ⟨hv_le, hfn, sV, hcoreV, hlenV, hpsV, hmV⟩
          c0_hsplit
          · have hv_lt : v.toNat < s.core.cur_vars := by
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
            have hv1 : (v + 1).toNat = v.toNat + 1 := sr1b_add1 (by omega)
            have hv_fl : v.toNat < sV.core.flags.length := by
              rw [hcoreV, hlen.core_ok.flags_len]; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [])
              (fun _ mN => ∃ sN, sN.core = s.core ∧ sN.LengthsOk c ∧
                FullProbeScratchPres s sN ∧
                (FullMem c sN ⋆ (array64 (c.hdr - 2304) ext5 ⋆ R)) mN)
              (fun _ ⟨⟩ mN ⟨sN, hcoreN, hlenN, hpsN, hmN⟩ => by
                c0_hsteps; exact hJV (s.core.cur_vars - (v.toNat + 1)) _ mN (by omega)
                  ⟨by rw [hv1]; omega, by rw [hv1], sN, hcoreN, hlenN, hpsN, hmN⟩)
              (fun Jn hJn => by
                c0_hsplit
                · c0_hsteps_nogrp
                  refine wp_call_of_spec _ _ (hHeapPush _ _ _ _
                    ⟨c, sV, array64 (c.hdr - 2304) ext5 ⋆ R, rfl, hlenV, hmV, ?_⟩)
                  rintro ⟨⟩ sN mN hcoreN hlenN hpostN hmN
                  dsimp only [PreservesCoreSlice, fullSafetySlice] at hcoreN hlenN hmN
                  have hpsN : FullProbeScratchPres sV sN :=
                    ⟨hpostN.1, hpostN.2.1, hpostN.2.2.1, hpostN.2.2.2.1, hpostN.2.2.2.2.1,
                      hpostN.2.2.2.2.2.1, hpostN.2.2.2.2.2.2.1, hpostN.2.2.2.2.2.2.2.1⟩
                  c0_hsteps; exact hJn () mN ⟨sN, hcoreN.trans hcoreV, hlenN,
                    sr1b_probePres_trans hpsV hpsN, hmN⟩
                · c0_hsteps; exact hJn () mV ⟨sV, hcoreV, hlenV, hpsV, hmV⟩)
          · c0_hsteps
            exact hJs (0#64, 1#64, ()) mV ⟨ext5, sV, hcoreV, hlenV, hpsV, hext5, hmV⟩
        · intro JV hJV; c0_hsteps
          exact hJV s.core.cur_vars (0#64, ()) m5
            ⟨Nat.zero_le _, by simp, s5, hcore5, hlen5, hps5, hm5⟩
      · -- `if (wm4 & 1 == 0)` init heap vs remove inactive vars
        c0_hsplit
        · refine wp_loop_group (ts := [i64])
            (fun fn ⟨v, ⟨⟩⟩ mV => v.toNat ≤ s.core.cur_vars ∧ fn = s.core.cur_vars - v.toNat ∧
              ∃ sV, sV.core = s.core ∧ sV.LengthsOk c ∧ FullProbeScratchPres s sV ∧
                (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mV) ?_ ?_
          · intro JV fn ⟨v, ⟨⟩⟩ mV hJV ⟨hv_le, hfn, sV, hcoreV, hlenV, hpsV, hmV⟩
            c0_hsplit
            · have hv_lt : v.toNat < s.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
              have hv1 : (v + 1).toNat = v.toNat + 1 := sr1b_add1 (by omega)
              have hv_ps : v.toNat < sV.scratch.pos.length := by
                rw [hlenV.scratch_ok.pos_len]; omega
              c0_hsteps
              let sV' : FullState := { sV with scratch := { sV.scratch with
                pos := sV.scratch.pos.set v.toNat 0xFFFFFFFF#32 } }
              have hlenV' : sV'.LengthsOk c := ⟨hlenV.core_ok,
                { hlenV.scratch_ok with pos_len := by simp [sV', hlenV.scratch_ok.pos_len] }⟩
              exact hJV (s.core.cur_vars - (v.toNat + 1)) _ _ (by omega)
                ⟨by rw [hv1]; omega, by rw [hv1], sV', hcoreV, hlenV', hpsV, ‹_›⟩
            · c0_hsteps_nogrp
              let sZ : FullState := { sV with scratch := { sV.scratch with heap_len := 0 } }
              have hlenZ : sZ.LengthsOk c := ⟨hlenV.core_ok, { hlenV.scratch_ok with }⟩
              c0_call hWm4Set
              refine m6HdrW2aSpec_of rfl hcfg hext1 hlenZ ((fullM6HdrMem_iff ..).mpr ‹_›)
                fun ⟨⟩ ext2 sZ2 mZ2 hcoreZ2 hlenZ2 hmZ2p hext2 _ hmZ2 => ?_
              rw [fullM6HdrMem_iff] at hmZ2; c0_hsteps
              exact hJw (_, ()) mZ2 ⟨ext2, sZ2, hcoreZ2.trans hcoreV, hlenZ2,
                sr1b_probePres_trans hpsV hmZ2p.probePres, hext2, hmZ2⟩
          · intro JV hJV; c0_hsteps
            exact hJV s.core.cur_vars (0#64, ()) m4
              ⟨Nat.zero_le _, by simp, s4, hcore4, hlen4, hps4, hm4⟩
        · -- Remove inactive vars from heap
          refine wp_loop_group (ts := [i64])
            (fun fn ⟨v, ⟨⟩⟩ mV => v.toNat ≤ s.core.cur_vars ∧ fn = s.core.cur_vars - v.toNat ∧
              ∃ sV, sV.core = s.core ∧ sV.LengthsOk c ∧ FullProbeScratchPres s sV ∧
                (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mV) ?_ ?_
          · intro JV fn ⟨v, ⟨⟩⟩ mV hJV ⟨hv_le, hfn, sV, hcoreV, hlenV, hpsV, hmV⟩
            c0_hsplit
            · have hv_lt : v.toNat < s.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
              have hv1 : (v + 1).toNat = v.toNat + 1 := sr1b_add1 (by omega)
              have hv_fl : v.toNat < sV.core.flags.length := by
                rw [hcoreV, hlen.core_ok.flags_len]; omega
              have hv_ps : v.toNat < sV.scratch.pos.length := by
                rw [hlenV.scratch_ok.pos_len]; omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ mN => ∃ sN, sN.core = s.core ∧ sN.LengthsOk c ∧
                  FullProbeScratchPres s sN ∧
                  (FullMem c sN ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mN)
                (fun _ ⟨⟩ mN ⟨sN, hcoreN, hlenN, hpsN, hmN⟩ => by
                  c0_hsteps; exact hJV (s.core.cur_vars - (v.toNat + 1)) _ mN (by omega)
                    ⟨by rw [hv1]; omega, by rw [hv1], sN, hcoreN, hlenN, hpsN, hmN⟩)
                (fun Jn hJn => by
                  c0_hsplit; rotate_left
                  · c0_hsteps; exact hJn () mV ⟨sV, hcoreV, hlenV, hpsV, hmV⟩
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [])
                    (fun _ mN => ∃ sN, sN.core = s.core ∧ sN.LengthsOk c ∧
                      FullProbeScratchPres s sN ∧
                      (FullMem c sN ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mN)
                    (fun _ ⟨⟩ mN h => by c0_hsteps; exact hJn () mN h)
                    (fun Je hJe => by
                      refine wp_join_group (ts := [])
                        (fun _ mE => (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mE)
                        (fun _ ⟨⟩ mE hmE => by
                          c0_hsteps
                          let sN : FullState := { sV with scratch := { sV.scratch with
                            pos := sV.scratch.pos.set v.toNat 0xFFFFFFFF#32 } }
                          exact hJe () _ ⟨sN, hcoreV, ⟨hlenV.core_ok, { hlenV.scratch_ok with
                            pos_len := by simp [sN, hlenV.scratch_ok.pos_len] }⟩, hpsV, ‹_›⟩)
                        (fun Jelse hJelse => by
                          c0_hsplit; rotate_left; · c0_hsteps; exact hJelse () mV hmV
                          have hn_pos : 0 < (BitVec.ofNat 64 sV.scratch.heap_len).toNat := by
                            simpa using hc
                          c0_hsplit; rotate_left; · c0_hsteps; exact hJelse () mV hmV
                          have hn_le : (BitVec.ofNat 64 sV.scratch.heap_len).toNat ≤
                              s.core.cur_vars := by
                            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                            simpa using hc
                          c0_hsplit; rotate_left; · c0_hsteps; exact hJelse () mV hmV
                          have hp_lt : (sV.scratch.pos[v.toNat]'hv_ps).toNat <
                              (BitVec.ofNat 64 sV.scratch.heap_len).toNat := hc
                          have hp_hp : ((sV.scratch.pos[v.toNat]'hv_ps).setWidth 64).toNat <
                              sV.scratch.heap.length := by
                            rw [sr1b_zext32, hlenV.scratch_ok.heap_len_arr]; omega
                          c0_hsplit; rotate_left; · c0_hsteps; exact hJelse () mV hmV
                          have hn1_eq : (BitVec.ofNat 64 sV.scratch.heap_len - 1#64).toNat =
                              (BitVec.ofNat 64 sV.scratch.heap_len).toNat - 1 := by bv_omega
                          have hn1_hp : (BitVec.ofNat 64 sV.scratch.heap_len - 1#64).toNat <
                              sV.scratch.heap.length := by
                            rw [hn1_eq, hlenV.scratch_ok.heap_len_arr]; omega
                          c0_hsteps_nogrp
                          let last_v := sV.scratch.heap[(BitVec.ofNat 64 sV.scratch.heap_len -
                            1#64).toNat]'hn1_hp
                          let sV1 : FullState := { sV with scratch := { sV.scratch with
                            heap_len := (BitVec.ofNat 64 sV.scratch.heap_len - 1#64).toNat } }
                          refine wp_join_group (ts := [])
                            (fun _ mA => ∃ sA, sA.core = s.core ∧ sA.LengthsOk c ∧
                              FullProbeScratchPres s sA ∧
                              (FullMem c sA ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mA)
                            (fun _ ⟨⟩ mA ⟨sA, hcoreA, hlenA, hpsA, hmA⟩ => by
                              c0_hstep; c0_hsplit; rotate_left
                              · c0_hsteps; exact hJe () mA ⟨sA, hcoreA, hlenA, hpsA, hmA⟩
                              have hv_psA : v.toNat < sA.scratch.pos.length := by
                                rw [hlenA.scratch_ok.pos_len]; omega
                              c0_hsteps_nogrp; c0_hstep
                              let sA1 : FullState := { sA with scratch := { sA.scratch with
                                pos := sA.scratch.pos.set v.toNat 0xFFFFFFFF#32 } }
                              have hlenA1 : sA1.LengthsOk c := ⟨hlenA.core_ok,
                                { hlenA.scratch_ok with
                                  pos_len := by simp [sA1, hlenA.scratch_ok.pos_len] }⟩
                              c0_hsplit; rotate_left
                              · c0_hsteps; exact hJe () _ ⟨sA1, hcoreA, hlenA1, hpsA, ‹_›⟩
                              have hlast_lt : (last_v.setWidth 64).toNat < s.core.cur_vars := by
                                rw [sr1b_zext32]; dsimp only [last_v]
                                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                                simpa only [hn1_eq, BitVec.toNat_ofNat,
                                  show (1 : BitVec 64).toNat = 1 from rfl,
                                  show (2 ^ 64 - 1 + sV.scratch.heap_len) % 2 ^ 64 =
                                    sV.scratch.heap_len % 2 ^ 64 - 1 by omega] using hc
                              have hp_hpA : ((sV.scratch.pos[v.toNat]'hv_ps).setWidth 64).toNat <
                                  sA1.scratch.heap.length := by
                                rw [sr1b_zext32, hlenA1.scratch_ok.heap_len_arr]; omega
                              have hlast_psA : (last_v.setWidth 64).toNat <
                                  sA1.scratch.pos.length := by
                                rw [hlenA1.scratch_ok.pos_len]; omega
                              c0_hsteps_nogrp
                              let sA2 : FullState := { sA1 with scratch := { sA1.scratch with
                                heap := sA1.scratch.heap.set
                                  ((sV.scratch.pos[v.toNat]'hv_ps).setWidth 64).toNat last_v,
                                pos := sA1.scratch.pos.set (last_v.setWidth 64).toNat
                                  (sV.scratch.pos[v.toNat]'hv_ps) } }
                              have hlenA2 : sA2.LengthsOk c := ⟨hlenA1.core_ok,
                                { hlenA1.scratch_ok with
                                  heap_len_arr := by simp [sA2, hlenA1.scratch_ok.heap_len_arr]
                                  pos_len := by simp [sA2, hlenA1.scratch_ok.pos_len] }⟩
                              refine wp_call_of_spec _ _ (hHeapUp _ _ _ _
                                ⟨c, sA2, array64 (c.hdr - 2304) ext1 ⋆ R, rfl, hlenA2, ‹_›, ?_⟩)
                              rintro ⟨⟩ sU mU hcoreU hlenU ⟨hpsU, _⟩ hmU; c0_hsteps_nogrp
                              refine wp_call_of_spec _ _ (hHeapDown _ _ _ _
                                ⟨c, sU, array64 (c.hdr - 2304) ext1 ⋆ R, rfl, hlenU, hmU, ?_⟩)
                              rintro ⟨⟩ sD mD hcoreD hlenD ⟨_, hpsD⟩ hmD; c0_hsteps
                              exact hJe () mD ⟨sD, Eq.trans hcoreD (Eq.trans hcoreU hcoreA), hlenD,
                                sr1b_probePres_trans hpsA (sr1b_probePres_trans hpsU hpsD), hmD⟩)
                            (fun Jla hJla => by
                              c0_hsplit
                              · have hlast_lt : (last_v.setWidth 64).toNat < s.core.cur_vars := by
                                  rw [sr1b_zext32]; dsimp only [last_v]
                                  rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                                  simpa only [hn1_eq, BitVec.toNat_ofNat,
                                    show (1 : BitVec 64).toNat = 1 from rfl,
                                    show (2 ^ 64 - 1 + sV.scratch.heap_len) % 2 ^ 64 =
                                      sV.scratch.heap_len % 2 ^ 64 - 1 by omega] using hc
                                have hlast_ps : (last_v.setWidth 64).toNat <
                                    sV1.scratch.pos.length := by
                                  rw [hlenV.scratch_ok.pos_len]; omega
                                c0_hsteps
                                let sA : FullState := { sV1 with scratch := { sV1.scratch with
                                  pos := sV1.scratch.pos.set (last_v.setWidth 64).toNat
                                    0xFFFFFFFF#32 } }
                                exact hJla () _ ⟨sA, hcoreV, ⟨hlenV.core_ok,
                                  { hlenV.scratch_ok with
                                    pos_len := by
                                      rw [List.length_set]; exact hlenV.scratch_ok.pos_len }⟩,
                                  hpsV, ‹_›⟩
                              · c0_hsteps; exact hJla () _ ⟨sV1, hcoreV,
                                  ⟨hlenV.core_ok, { hlenV.scratch_ok with }⟩, hpsV, ‹_›⟩))))
            · c0_hsteps; exact hJw (_, ()) mV ⟨ext1, sV, hcoreV, hlenV, hpsV, hext1, hmV⟩
          · intro JV hJV; c0_hsteps
            exact hJV s.core.cur_vars (0#64, ()) m4
              ⟨Nat.zero_le _, by simp, s4, hcore4, hlen4, hps4, hm4⟩
    · -- `h->stable != 0` (Stable -> Focused)
      c0_hsplit
      · c0_hsteps
        exact hQ ext s m rfl hlen (sr1b_probePres_refl _) hext ((fullM6HdrMem_iff ..).mpr hm)
      c0_hsteps_nogrp
      let s1 : FullState := { s with scratch := { s.scratch with stable := 0#64 } }
      c0_call hNlog; intro _; c0_hsteps_nogrp
      c0_call hTo; intro rTo; c0_hsteps_nogrp
      let s2 : FullState := { s1 with scratch := { s1.scratch with
        mode_confl_lim := s1.scratch.conflicts + 1000#64 * rTo,
        mode_saved_ticks := s1.scratch.search_ticks, q_search_idx := s1.scratch.q_last } }
      refine wp_join_group (ts := [])
        (fun _ m3 => ∃ qss : BitVec 64,
          (FullMem c { s2 with scratch := { s2.scratch with q_search_stamp := qss } } ⋆
            (array64 (c.hdr - 2304) ext ⋆ R)) m3)
        (fun _ ⟨⟩ m3 ⟨qss, hm3⟩ => by
          let s3 : FullState := { s2 with scratch := { s2.scratch with q_search_stamp := qss } }
          c0_hsteps; exact hJs (1#64, 0#64, ()) m3 ⟨ext, s3, rfl,
            ⟨hlen.core_ok, { hlen.scratch_ok with }⟩, sr1b_probePres_refl _, hext, hm3⟩)
        (fun Jq hJq => by
          c0_hsplit
          · have hql_lt : s.scratch.q_last.toNat < s.core.cur_vars := by
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
            have hql_qs : s.scratch.q_last.toNat < s.scratch.q_stamp.length := by
              rw [hlen.scratch_ok.q_stamp_len]; omega
            c0_hsteps; exact hJq () _ ⟨_, ‹_›⟩
          · c0_hsteps; exact hJq () _ ⟨s2.scratch.q_search_stamp, ‹_›⟩)

end SwitchModeStep13

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
