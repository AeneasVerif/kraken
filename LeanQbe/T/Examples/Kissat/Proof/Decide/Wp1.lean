/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Src.Decide
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb

/-!
# Soundness Proofs for `Kissat.Src.Decide` — Part 1 (`Proof.Decide.Wp1`)

Proves `full_randec_var_lvl_fid_wp` (`fullRandecVarLvlSpec`) and `full_randec_var_m7_wp`
(`fullRandecVarSpec`) (`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
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
open LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
open LeanQbe.T.Examples.Kissat.Src.Decide
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem bv8_sext32_eq0 (x : BitVec 8) (h : x.signExtend 32 = 0#32) : x = 0#8 := by
  ext i hi
  have h1 := congrArg (·[i]) h
  simpa [BitVec.getElem_signExtend, hi, show i < 32 by omega] using h1

private theorem bv64_shl1_lt {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt h]

private theorem m7_set64_lengthsOk {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (idx : Nat) (val : BitVec 64) :
    ({ s with scratch := { s.scratch with
      glue_used := if idx < 63 then m7Set64List s.scratch.glue_used idx val
                   else s.scratch.glue_used } } : FullState).LengthsOk c := by
  refine ⟨hlen.core_ok, { hlen.scratch_ok with glue_used_len := ?_ }⟩
  split
  · rw [m7Set64List_length]; exact hlen.scratch_ok.glue_used_len
  · exact hlen.scratch_ok.glue_used_len

private theorem m7_set64_guPres {s : FullState} {idx : Nat} (val : BitVec 64) (hge : 36 ≤ idx) :
    M7GuPrefixPres s { s with scratch := { s.scratch with
      glue_used := if idx < 63 then m7Set64List s.scratch.glue_used idx val
                   else s.scratch.glue_used } } := by
  intro k hk
  split
  · exact m7Set64List_get_lt val (by omega)
  · rfl

private theorem call_get64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
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
  exact hGet _ _ _ _ ⟨c, s, R, rfl, hlen, hm, hk _ rfl⟩

private theorem call_set64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hSet : ∀ a m Q X, m7Set64Spec a m Q X → Γ "full_m7_set64" [i64, i64, i64] [] a m Q X)
    {c : FullCfg} {idx val : BitVec 64} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, idx, val, ())) (hidx_lo : 36 ≤ idx.toNat)
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c →
      FullExtScratchPres s s' → M7GuPrefixPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_m7_set64" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hSet _ _ _ _ ⟨c, s, R, rfl, hlen, hm, fun m' hm' => ?_⟩
  let s' : FullState := { s with scratch := { s.scratch with
    glue_used := if idx.toNat < 63 then m7Set64List s.scratch.glue_used idx.toNat val
                 else s.scratch.glue_used } }
  exact hk s' m' rfl (m7_set64_lengthsOk hlen idx.toNat val) ⟨rfl, rfl⟩
    (m7_set64_guPres val hidx_lo) hm'

private theorem lcg_lengthsOk {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (rng' : BitVec 64) :
    ({ s with scratch := { s.scratch with rng_state := rng' } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩

private theorem lcg_extPres {s sT : FullState} (h : FullExtScratchPres s sT)
    (rng' : BitVec 64) :
    FullExtScratchPres s { sT with scratch := { sT.scratch with rng_state := rng' } } := h

private theorem lcg_guPres {s sT : FullState} (h : M7GuPrefixPres s sT)
    (rng' : BitVec 64) :
    M7GuPrefixPres s { sT with scratch := { sT.scratch with rng_state := rng' } } := h

/-- Soundness proof for `full_randec_var_lvl_fid` against `fullRandecVarLvlSpec`. -/
theorem full_randec_var_lvl_fid_wp (Γ : Env)
    (hInit : ∀ a m Q X, step13M7StateInitSpec a m Q X →
      Γ "full_m7_state_init" [i64] [] a m Q X)
    (hGet64 : ∀ a m Q X, m7Get64Spec a m Q X → Γ "full_m7_get64" [i64, i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m7Set64Spec a m Q X → Γ "full_m7_set64" [i64, i64, i64] [] a m Q X)
    (hLog : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hTo : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hLcg : ∀ a m Q X, m7LcgNextSpec a m Q X → Γ "full_lcg_next_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullRandecVarLvlSpec a m Q X →
      Func.wp Γ full_randec_var_lvl_fid_body a m Q X := by
  rintro ⟨h, max_lvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hcv_le := hlen.core_ok.cur_vars_le
  have hretFF : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      M7GuPrefixPres s s' → (FullMem c s' ⋆ R) m' → Q (0xFFFFFFFFFFFFFFFF#64, ()) m' :=
    fun s' m' hc' hl' hp' hg' hm' =>
      hQ (0xFFFFFFFFFFFFFFFF#64, ()) s' m' hc' hl' ⟨hp', hg', Or.inl rfl⟩ hm'
  unfold Func.wp full_randec_var_lvl_fid_body
  c0_hsplit
  · c0_hsteps; exact hretFF s m rfl hlen (fullExtScratchPres_refl _) (M7GuPrefixPres.refl _) hm
  have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h => hc (by rw [h]; rfl)
  clear hc; c0_hsplit
  · c0_hsteps; exact hretFF s m rfl hlen (fullExtScratchPres_refl _) (M7GuPrefixPres.refl _) hm
  clear hc; c0_hsplit
  · c0_hsteps; exact hretFF s m rfl hlen (fullExtScratchPres_refl _) (M7GuPrefixPres.refl _) hm
  clear hc; c0_hsteps_nogrp
  c0_call hInit
  refine ⟨c, s, R, rfl, hlen, hm, fun _ s1 m1 hcore1 hlen1 ⟨hext1, hpre1, _⟩ hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hcore1 hlen1 hm1
  c0_hsteps_nogrp
  refine call_get64 hGet64 rfl hlen1 hm1 fun rem0 _ => ?_
  c0_hsteps_nogrp
  refine call_get64 hGet64 rfl hlen1 hm1 fun lc0 _ => ?_
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (rem1, ()) m2 => ∃ s2, s2.core = s.core ∧ s2.LengthsOk c ∧
      FullExtScratchPres s s2 ∧ M7GuPrefixPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ ⟨rem1, ⟨⟩⟩ m2 ⟨s2, hcore2, hlen2, hext2, hpre2, hm2⟩ => ?_)
    (fun Jc hJc => by
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ mA => m1 = mA)
          (fun _ ⟨rem', ⟨⟩⟩ mA hmA => by
            rcases hmA with rfl; c0_hsteps_nogrp
            refine call_set64 hSet64 rfl (by decide) hlen1 hm1
              fun sA mA hca hla hesa hpa hma => ?_
            c0_hsteps_nogrp
            refine call_set64 hSet64 rfl (by decide) hla hma
              fun sB mB hcb hlb hesb hpb hmb => ?_
            c0_hsteps
            exact hJc (rem', ()) mB ⟨sB, hcb.trans (hca.trans hcore1), hlb,
              fullExtScratchPres_trans hext1 (fullExtScratchPres_trans hesa hesb),
              hpre1.trans (hpa.trans hpb), hmb⟩)
          (fun Jd hJd => by c0_hsteps <;> exact hJd (_, ()) m1 rfl)
      · c0_hsteps; exact hJc (rem0, ()) m1 ⟨s1, hcore1, hlen1, hext1, hpre1, hm1⟩)
  refine wp_join_group (ts := [i64])
    (fun _ m3 => ∃ s3, s3.core = s.core ∧ s3.LengthsOk c ∧ FullExtScratchPres s s3 ∧
      M7GuPrefixPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
    (fun _ ⟨_, ⟨⟩⟩ m3 ⟨s3, hcore3, hlen3, hext3, hpre3, hm3⟩ => ?_)
    (fun Jr hJr => by
      c0_hsplit
      · c0_hsplit
        · c0_hsteps; exact hretFF s2 m2 hcore2 hlen2 hext2 hpre2 hm2
        · c0_hsteps_nogrp
          refine call_get64 hGet64 rfl hlen2 hm2 fun lim _ => ?_
          c0_hsplit
          · c0_hsteps; exact hretFF s2 m2 hcore2 hlen2 hext2 hpre2 hm2
          · c0_hsteps_nogrp
            refine call_get64 hGet64 rfl hlen2 hm2 fun seq0 _ => ?_
            c0_hsteps_nogrp
            refine call_set64 hSet64 rfl (by decide) hlen2 hm2
              fun sA mA hca hla hesa hpa hma => ?_
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
                    refine call_set64 hSet64 rfl (by decide) hla hma
                      fun sB mB hcb hlb hesb hpb hmb => ?_
                    c0_hsteps_nogrp
                    refine call_set64 hSet64 rfl (by decide) hlb hmb
                      fun sC mC hcc hlc hesc hpc hmc => ?_
                    c0_hsteps
                    exact hJr (len, ()) mC ⟨sC, hcc.trans (hcb.trans (hca.trans hcore2)), hlc,
                      fullExtScratchPres_trans hext2
                        (fullExtScratchPres_trans hesa (fullExtScratchPres_trans hesb hesc)),
                      hpre2.trans (hpa.trans (hpb.trans hpc)), hmc⟩)
                  (fun Jl hJl => by c0_hsteps <;> exact hJl (_, ()) mA rfl))
              (fun Jq hJq => by c0_hsteps <;> exact hJq (_, ()) mA rfl)
      · c0_hsteps; exact hJr (rem1, ()) m2 ⟨s2, hcore2, hlen2, hext2, hpre2, hm2⟩)
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (mt, ()) m4 => m3 = m4 ∧ mt.toNat ≤ 16396)
    (fun _ ⟨mt, ⟨⟩⟩ m4 ⟨hm4, hmt⟩ => ?_)
    (fun Jm hJm => by
      c0_hsplit
      · have hcv4k : s.core.cur_vars < 4096 := by
          have h1 := hc
          rw [show (4096 : BitVec 64).toNat = 4096 from rfl,
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1
          exact h1
        c0_hsteps; exact hJm (_, ()) m3 ⟨rfl, by
          have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          rw [BitVec.toNat_add, BitVec.toNat_mul, hcv64,
            show (4 : BitVec 64).toNat = 4 from rfl, show (16 : BitVec 64).toNat = 16 from rfl,
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars * 4 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars * 4 + 16 < 2 ^ 64)]
          omega⟩
      · c0_hsteps; exact hJm (16384#64, ()) m3 ⟨rfl, by decide⟩)
  rcases hm4 with rfl
  refine wp_loop_group (ts := [i64])
    (fun fnT ⟨tr, ⟨⟩⟩ mT => tr.toNat ≤ mt.toNat ∧ fnT = mt.toNat - tr.toNat ∧
      ∃ sT, sT.core = s.core ∧ sT.LengthsOk c ∧ FullExtScratchPres s sT ∧
        M7GuPrefixPres s sT ∧ (FullMem c sT ⋆ R) mT) ?_ ?_
  · intro JT fnT ⟨tr, ⟨⟩⟩ mT hJT ⟨htr_le, hfnT, sT, hcoreT, hlenT, hextT, hpreT, hmT⟩
    c0_hsplit
    · have htr_lt : tr.toNat < mt.toNat := hc
      clear hc
      have htr1 : (tr + 1#64).toNat = tr.toNat + 1 := by bv_omega
      c0_hsteps_nogrp
      c0_call hLcg
      refine ⟨c, sT, R, rfl, hlenT, hmT, fun mU hmU => ?_⟩
      generalize m7LcgNextVal sT.scratch.rng_state = rngU at hmU ⊢
      let sU : FullState := { sT with scratch := { sT.scratch with rng_state := rngU } }
      have hcoreU0 : sU.core = s.core := hcoreT
      have hlenU : sU.LengthsOk c := lcg_lengthsOk hlenT rngU
      have hextU : FullExtScratchPres s sU := lcg_extPres hextT rngU
      have hpreU : M7GuPrefixPres s sU := lcg_guPres hpreT rngU
      let idx := (rngU >>> 32) % BitVec.ofNat 64 s.core.cur_vars
      have hidx_lt : idx.toNat < s.core.cur_vars := by
        dsimp only [idx]
        rw [BitVec.toNat_umod, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)]
        exact Nat.mod_lt _ hcv_pos
      have hidx_fl : idx.toNat < sU.core.flags.length := by
        rw [hcoreU0, hlen.core_ok.flags_len]; omega
      have h2idx_eq : (idx <<< (1 : Nat)).toNat = 2 * idx.toNat := bv64_shl1_lt (by omega)
      have h2idx_v : (idx <<< (1 : Nat)).toNat < sU.core.vals.length := by
        rw [h2idx_eq, hcoreU0, hlen.core_ok.vals_len]; omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun _ mN => mU = mN)
        (fun _ ⟨⟩ mN hmN => by
          rcases hmN with rfl; c0_hsteps
          exact hJT (mt.toNat - (tr.toNat + 1)) _ mU (by omega)
            ⟨by rw [show (tr + 1).toNat = tr.toNat + 1 from htr1]; omega,
             by rw [show (tr + 1).toNat = tr.toNat + 1 from htr1],
             sU, hcoreU0, hlenU, hextU, hpreU, hmU⟩)
        (fun Jc hJc => by
          c0_hsplit; rotate_left; · c0_hsteps; exact hJc () mU rfl
          have hfl_ne : (sU.core.flags[idx.toNat]'hidx_fl &&& 1#32) ≠ 0#32 := hc
          clear hc
          c0_hsplit; rotate_left; · c0_hsteps; exact hJc () mU rfl
          c0_hsteps
          refine hQ (idx, ()) sU mU hcoreU0 hlenU ⟨hextU, hpreU, Or.inr ⟨hidx_lt, ?_, ?_⟩⟩ hmU
          · dsimp only
            rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.flags_len]; omega),
              Option.getD_some]
            simpa [hcoreU0] using hfl_ne
          · dsimp only
            rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.vals_len]; omega),
              Option.getD_some]
            have hmod2 : 2 * idx.toNat % 2 ^ 64 = 2 * idx.toNat := Nat.mod_eq_of_lt (by omega)
            have hv0 : (sU.core.vals[2 * idx.toNat]'(by
                rw [hcoreU0, hlen.core_ok.vals_len]; omega)).signExtend 32 = 0#32 := by
              have hget : sU.core.vals[2 * idx.toNat]'(by
                    rw [hcoreU0, hlen.core_ok.vals_len]; omega) =
                  sT.core.vals[2 * idx.toNat % 2 ^ 64]'(by
                    rw [hmod2, hcoreT, hlen.core_ok.vals_len]; omega) := by
                rw [← Option.some_inj, ← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem,
                  hmod2]
              rw [hget]; exact hc
            have hv8 := bv8_sext32_eq0 _ hv0
            simpa [hcoreU0] using hv8)
    · c0_hsteps; exact hretFF sT mT hcoreT hlenT hextT hpreT hmT
  · intro JT hJT; c0_hsteps
    exact hJT mt.toNat (0#64, ()) m3
      ⟨Nat.zero_le _, by simp, s3, hcore3, hlen3, hext3, hpre3, hm3⟩

/-- Soundness proof for `full_randec_var_m7` against canonical `fullRandecVarSpec`. -/
theorem full_randec_var_m7_wp (Γ : Env)
    (hLvl : ∀ a m Q X, fullRandecVarLvlSpec a m Q X →
      Γ "full_randec_var_lvl_fid" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullRandecVarSpec a m Q X → Func.wp Γ full_randec_var_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp full_randec_var_m7_body
  c0_call hLvl
  exact ⟨c, s, R, rfl, hlen, hm, fun r s' m' hc hl hp hm' => hQ r s' m' hc hl hp hm'⟩

end LeanQbe.T.Examples.Kissat.Proof.Decide
