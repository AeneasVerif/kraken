/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Float64
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import Lean.Elab.Tactic
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# WP Proofs for `Kissat.Src.Float64` Part 1 (`Wp1`)

Canonical `Func.wp` proofs for the remaining `5` functions of `Src.Float64.fns`:
`f64u_inv_u64`, `f64u_log10_u64`, `f64u_nlogpown`, `m6_wm4_get`, `m6_wm4_set`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Float64

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Float64
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics

local macro "f64_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

private theorem wp_pure_group {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (hbody : ∀ (J : Cont ts) xs, wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m)
    (hentry : ∀ (J : Cont ts), (∀ xs, J xs m) → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_group (fun _ m1 => m1 = m) (fun J xs _ hm => hm ▸ hbody J xs)
    (fun J hJ => hentry J (fun xs => hJ xs m rfl))

local macro "f64_pure_step" : tactic =>
  `(tactic| (
    f64_hsteps_nogrp
    all_goals try first
      | (apply_assumption; done)
      | refine wp_pure_group (fun _ _ => ?_) (fun _ _ => ?_)
      | c0_hsplit))

local macro "f64_pure_acyclic" : tactic =>
  `(tactic| (
    f64_pure_step; f64_pure_step; f64_pure_step; f64_pure_step
    f64_pure_step; f64_pure_step; f64_pure_step; f64_pure_step))

private theorem inv_d_round_ne_zero {x msb : BitVec 64}
    (hmsb_lt : msb.toNat < 64) (hlo : 2 ^ msb.toNat ≤ x.toNat) (hgt : 52 < msb.toNat) :
    let sh := msb - 52#64
    let m0 := x >>> sh
    m0 ≠ 0#64 ∧ (m0 + 1#64 ≠ 0#64) ∧ ((m0 + 1#64) >>> 1 ≠ 0#64) := by
  have hsh : (msb - 52#64).toNat = msb.toNat - 52 := by
    rw [BitVec.toNat_sub, show (52#64 : BitVec 64).toNat = 52 from rfl]; omega
  have hm0 : (x >>> (msb - 52#64)).toNat = x.toNat / 2 ^ (msb.toNat - 52) := by
    change (x >>> (msb - 52#64).toNat).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsh]
  have hpow : 2 ^ msb.toNat = 2 ^ 52 * 2 ^ (msb.toNat - 52) := by
    rw [← Nat.pow_add, show 52 + (msb.toNat - 52) = msb.toNat by omega]
  have hm_ge : 2 ^ 52 ≤ (x >>> (msb - 52#64)).toNat := by
    rw [hm0]
    exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).mpr (by rw [← hpow]; exact hlo)
  have hx_lt : x.toNat < 2 ^ 64 := x.isLt
  have hsh_ge : 1 ≤ msb.toNat - 52 := by omega
  have h2_le : 2 ≤ 2 ^ (msb.toNat - 52) :=
    Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by omega) hsh_ge)
  have h64_le : 2 ^ 64 ≤ 2 ^ 63 * 2 ^ (msb.toNat - 52) := by
    rw [show (2 ^ 64 : Nat) = 2 ^ 63 * 2 by decide]
    exact Nat.mul_le_mul_left _ h2_le
  have hm_lt : (x >>> (msb - 52#64)).toNat < 2 ^ 63 := by
    rw [hm0]
    exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).mpr (Nat.lt_of_lt_of_le hx_lt h64_le)
  have hlt64 : 2 ^ 63 + 1 < 2 ^ 64 := by decide
  have hm1_to : (x >>> (msb - 52#64) + 1#64).toNat = (x >>> (msb - 52#64)).toNat + 1 := by
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hshr1 : ((x >>> (msb - 52#64) + 1#64) >>> 1).toNat =
      ((x >>> (msb - 52#64)).toNat + 1) / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hm1_to]
  have h52 : 2 ^ 52 = 2 ^ 51 * 2 := by decide
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at this; omega
  · have := congrArg BitVec.toNat h; rw [hm1_to, BitVec.toNat_ofNat] at this; omega
  · have := congrArg BitVec.toNat h; rw [hshr1, BitVec.toNat_ofNat] at this
    have : 2 ^ 51 ≤ ((x >>> (msb - 52#64)).toNat + 1) / 2 :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    omega

theorem f64u_inv_u64_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uMsb64Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure1Spec a m Q X → Func.wp Γ f64u_inv_u64_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure1Spec] at hQ
  unfold Func.wp f64u_inv_u64_body
  f64_hsteps_nogrp
  · exact hQ _
  · exact hQ _
  · c0_call hMsb; intro msb hmsb
    obtain ⟨hmsb_lt, hlo, hhi⟩ := hmsb (by assumption)
    f64_hsteps_nogrp
    · exact hQ _
    · refine wp_join_group
        (fun (st : Tup Val [i64, i64, i64]) m1 => m1 = m ∧ st.2.1 ≠ 0#64)
        (fun _ ⟨exp0, d, d_msb, ⟨⟩⟩ ml ⟨hm_eq, hd⟩ => ?_)
        (fun J hJ => ?_)
      · rw [hm_eq]
        f64_hsteps_nogrp
        · refine wp_pure_group
            (fun _ _ => by f64_hsteps_nogrp; c0_call hPack; intro _; f64_hsteps_nogrp; exact hQ _)
            (fun _ _ => by f64_pure_acyclic)
        · refine wp_pure_group
            (fun _ _ => by f64_hsteps_nogrp; c0_call hPack; intro _; f64_hsteps_nogrp; exact hQ _)
            (fun _ _ => by f64_pure_acyclic)
        · refine wp_loop_inv
            (fun (st : Tup Val [i64, i64, i64]) ml2 => ml2 = m)
            (fun (st : Tup Val [i64, i64, i64]) _ => st.1.toNat)
            (fun J2 hJ2 => by f64_hsteps_nogrp; exact hJ2 _ m rfl)
            (fun J2 ⟨s2, q, rem, ⟨⟩⟩ ml2 hm_eq2 hJ2 => ?_)
          · rw [hm_eq2]
            f64_hsteps_nogrp
            · have hs2pos : 0 < s2.toNat := by c0_bound
              refine wp_join_group
                (fun (st : Tup Val [i64]) m1 =>
                  m1 = m ∧ 1 ≤ st.1.toNat ∧ st.1.toNat ≤ s2.toNat)
                (fun _ ⟨st, ⟨⟩⟩ _ ⟨hm_eq3, hst1, hstle⟩ => by
                  rw [hm_eq3]
                  f64_hsteps_nogrp
                  exact hJ2 (s2 - st, _, _, ()) m (by
                    rw [BitVec.toNat_sub]
                    dsimp only at hst1 hstle ⊢
                    have hs2lt := s2.isLt
                    have h1 : 2 ^ 64 - st.toNat + s2.toNat =
                        (s2.toNat - st.toNat) + 2 ^ 64 * 1 := by omega
                    rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
                    omega) rfl)
                (fun J3 hJ3 => by
                  c0_hsplit <;> f64_hsteps_nogrp
                  · have h11 : 11 ≤ s2.toNat := by c0_bound
                    exact hJ3 (11#64, ()) m ⟨rfl, by decide, h11⟩
                  · exact hJ3 (s2, ()) m ⟨rfl, hs2pos, Nat.le_refl _⟩)
            · refine wp_pure_group
                (fun _ _ => by
                  f64_hsteps_nogrp; c0_call hPack; intro _; f64_hsteps_nogrp; exact hQ _)
                (fun _ _ => by f64_pure_acyclic)
      · c0_hsplit
        · have hmsb_gt : 52 < msb.toNat := by c0_bound
          have ⟨hd0, hd1, hd2⟩ := inv_d_round_ne_zero hmsb_lt hlo hmsb_gt
          have hsub64 : (msb - 52#64).toNat < 64 := by
            rw [BitVec.toNat_sub, show (52#64 : BitVec 64).toNat = 52 from rfl]; omega
          have hx_shr : x >>> ((msb - 52).toNat % 64) = x >>> (msb - 52#64) := by
            rw [show (52 : BitVec 64) = 52#64 from rfl, Nat.mod_eq_of_lt hsub64]; rfl
          have h1eq : (1 : BitVec 64) = 1#64 := rfl
          rw [← hx_shr] at hd0 hd1 hd2
          rw [← h1eq] at hd1 hd2
          f64_hsteps_nogrp
          refine wp_join_group
            (fun (st : Tup Val [i64, i64]) m1 => m1 = m ∧ st.2.1 ≠ 0#64)
            (fun _ ⟨msb', m', ⟨⟩⟩ _ ⟨hm1, hm'⟩ => by
              rw [hm1]; f64_hsteps_nogrp; exact hJ (_, _, _, ()) m ⟨rfl, hm'⟩)
            (fun J2 hJ2 => by
              refine wp_pure_group (fun _ _ => ?_)
                (fun _ _ => by f64_pure_acyclic; all_goals exact hJ2 (_, _, ()) m ⟨rfl, hd0⟩)
              f64_hsteps_nogrp
              refine wp_join_group
                (fun (st : Tup Val [i64, i64]) m1 => m1 = m ∧ st.2.1 ≠ 0#64)
                (fun _ ⟨msb2, m2, ⟨⟩⟩ _ ⟨hm2, hm2_ne⟩ => by
                  rw [hm2]; f64_hsteps_nogrp; exact hJ2 (_, _, ()) m ⟨rfl, hm2_ne⟩)
                (fun J3 hJ3 => by
                  c0_hsplit <;> f64_hsteps_nogrp
                  · refine hJ3 _ m ⟨rfl, ?_⟩; exact hd2
                  · refine hJ3 _ m ⟨rfl, ?_⟩; exact hd1))
        · f64_hsteps_nogrp; exact hJ (_, _, _, ()) m ⟨rfl, by assumption⟩

theorem f64u_log10_u64_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec)
    (hMul128 : Γ.Has "u64_mul128" u64Mul128Spec) :
    ∀ a m Q X, f64uPure1Spec a m Q X → Func.wp Γ f64u_log10_u64_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure1Spec] at hQ
  unfold Func.wp f64u_log10_u64_body
  f64_hsteps_nogrp
  · exact hQ _
  · c0_call hMsb; intro _; f64_hsteps_nogrp
    refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by f64_pure_acyclic)
    f64_hsteps_nogrp
    refine wp_loop_inv
      (fun (st : Tup Val [i64, i64, i64]) ml => ml = m ∧ st.2.2.1.toNat ≤ 64)
      (fun (st : Tup Val [i64, i64, i64]) _ => 64 - st.2.2.1.toNat)
      (fun J hJ => by f64_hsteps_nogrp; exact hJ _ m ⟨rfl, by dsimp only; decide⟩)
      (fun J ⟨z, exp, sh, ⟨⟩⟩ ml ⟨hm_eq, hsh⟩ hJ => ?_)
    subst hm_eq
    f64_hsteps_nogrp
    · have hshlt : sh.toNat < 64 := by c0_bound
      c0_call hMul128; intro _ _
      f64_hsteps_nogrp
      refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by f64_pure_acyclic)
      f64_hsteps_nogrp
      exact hJ (_, _, sh + 1#64, ()) ml
        (by dsimp; rw [Nat.mod_eq_of_lt (by have := sh.isLt; omega)]; omega)
        ⟨rfl, by dsimp; rw [Nat.mod_eq_of_lt (by have := sh.isLt; omega)]; omega⟩
    · f64_hsteps_nogrp
      c0_call hMul128; intro _ _
      f64_pure_acyclic
      all_goals
        first
        | (c0_call hPack; intro _; f64_pure_acyclic)
        | (c0_call hMsb; intro _; f64_pure_acyclic;
            all_goals try (c0_call hPack; intro _; f64_pure_acyclic))

theorem f64u_nlogpown_wp (Γ : Env)
    (hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_nlogpown_body a m Q X := by
  rintro ⟨count, exponent, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure2Spec] at hQ
  unfold Func.wp f64u_nlogpown_body
  refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by f64_pure_acyclic)
  f64_hsteps_nogrp
  c0_call hLog; intro _
  f64_hsteps_nogrp
  refine wp_loop_inv
    (fun (st : Tup Val [i64, i64]) ml => ml = m ∧ st.2.1.toNat ≤ exponent.toNat)
    (fun (st : Tup Val [i64, i64]) _ => exponent.toNat - st.2.1.toNat)
    (fun J hJ => by f64_hsteps_nogrp; exact hJ _ m ⟨rfl, Nat.zero_le _⟩)
    (fun J ⟨factor, i, ⟨⟩⟩ ml ⟨hm_eq, hi⟩ hJ => ?_)
  subst hm_eq
  f64_hsteps_nogrp
  · have hilt : i.toNat < exponent.toNat := by c0_bound
    c0_call hMul; intro _
    f64_hsteps_nogrp
    exact hJ (_, i + 1#64, ()) ml
      (by dsimp; rw [Nat.mod_eq_of_lt (by have := exponent.isLt; omega)]; omega)
      ⟨rfl, by dsimp; rw [Nat.mod_eq_of_lt (by have := exponent.isLt; omega)]; omega⟩
  · c0_call hFrom; intro _
    f64_hsteps_nogrp
    c0_call hMul; intro _
    f64_hsteps_nogrp; exact hQ _

theorem m6_wm4_get_wp (Γ : Env) :
    ∀ a m Q X, m6Wm4GetSpec a m Q X → Func.wp Γ m6_wm4_get_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  unfold Func.wp m6_wm4_get_body
  rw [fullM6HdrMem_iff] at hm
  have hlt0 : 0 < ext.length := by have := hext.len; omega
  have hlt28 : (224#64 : BitVec 64).toNat / 8 < ext.length := by
    have := hext.len; rw [show (224#64 : BitVec 64).toNat = 224 from rfl]; omega
  have ha : c.hdr - 2304#64 = m6ExtAddr c.hdr := rfl
  f64_hsteps_nogrp
  · exact hQ 0#64 ((fullM6HdrMem_iff ..).mpr hm)
  · exact hQ _ ((fullM6HdrMem_iff ..).mpr hm)

theorem m6_wm4_set_wp (Γ : Env) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X → Func.wp Γ m6_wm4_set_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X hW
  obtain ⟨c, ext, s, R, hc, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hW
  subst hc
  unfold Func.wp m6_wm4_set_body
  rw [fullM6HdrMem_iff] at hm
  have hlt0 : 0 < ext.length := by have := hext.len; omega
  have hlt28 : (224#64 : BitVec 64).toNat / 8 < ext.length := by
    have := hext.len; rw [show (224#64 : BitVec 64).toNat = 224 from rfl]; omega
  f64_hsteps_nogrp
  · exact hQ () ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) ((fullM6HdrMem_iff ..).mpr hm)
  · refine hQ () (ext.set 28 v) s _ rfl hlen (M6HdrScratchPres.refl s) ?_ ?_ ?_
    · exact M6HdrExtOk.of_len (by simp [hext.len])
    · intro hi
      exact ⟨hi.set_pos v (by omega), M6ExtW2bPres.set_ge8 v (by omega)⟩
    · rw [fullM6HdrMem_iff]
      simpa only [show (224#64 : BitVec 64).toNat / 8 = 28 from rfl] using ‹_›

end LeanQbe.T.Examples.Kissat.Proof.Float64
