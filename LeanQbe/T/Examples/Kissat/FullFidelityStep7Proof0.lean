/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.FullM5OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas2
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import all LeanQbe.T.Examples.Kissat.FullM5OrchProof0
import all LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import all LeanQbe.T.Examples.Kissat.FullM7WalkProof0
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat Fidelity Step 7 Proofs — Shard 0 (`FullFidelityStep7Proof0`)

UNSAT-only (`0` SAT model proofs), `X`-polymorphic `Func.wp` soundness theorems for the Step-7
pure-C0 replacements `full_calc_max_v` (`bva_cap ≤ 32768`), `full_calc_scr_cap_m5` (`8M` cap),
`m6_hdr_init` (`watermarks[1] = 0`), `full_walk_cb_inv_m7` (fixed parity guard), plus the
caller rewires `full_init_state_m5` (`8M` scratch cap) and `full_walk_m7` (`step7CbInvSpec`).
-/

set_option autoImplicit false

local elab "s7_hsteps_nj" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. `full_calc_max_v` (`bva_cap ≤ 32768`) -/

section CalcMaxV

open Full.FullParseInitSpecs
open Full.FullParseInitHelpers
open scoped Full.FullParseInitTactics

private abbrev s7BvaCap (avail mv nc f0 : Nat) : Nat :=
  if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
    min 32768 (((avail - f0) - nc * 48 - 4096) / 2688)
  else 0

private def s7CalcMaxV (avail mv nc f0 : Nat) : Nat :=
  let max_v := mv + s7BvaCap avail mv nc f0
  let fixed := fullFixedBytes max_v
  if avail < fixed ∨ avail - fixed < nc * 40 + 136 then mv else max_v

private theorem s7BvaCap_le (avail mv nc f0 : Nat) : s7BvaCap avail mv nc f0 ≤ 32768 := by
  unfold s7BvaCap; split <;> omega

private theorem s7CalcMaxV_fits {avail mv nc : Nat}
    (hfit : fullFixedBytes mv + nc * 40 + 136 ≤ avail) :
    fullFixedBytes (s7CalcMaxV avail mv nc (fullFixedBytes mv)) + nc * 40 + 136 ≤ avail := by
  unfold s7CalcMaxV; dsimp only; split <;> omega

private theorem s7_bv64_ofNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
private theorem s7_bv64_mul (x : BitVec 64) (k : Nat) :
    x * BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat * k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]
private theorem s7_bv64_ult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, s7_bv64_ofNat ha, s7_bv64_ofNat hb]
private theorem s7_bv64_sub {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by have := a.isLt; rw [BitVec.toNat_sub]; omega

private theorem s7CalcMaxV_eq1 {avail mv nc f0 : Nat}
    (hlt : avail < fullFixedBytes (mv + s7BvaCap avail mv nc f0)) :
    s7CalcMaxV avail mv nc f0 = mv := by
  unfold s7CalcMaxV; dsimp only; exact ite_eq_left_iff.mpr fun h => absurd (Or.inl hlt) h
private theorem s7CalcMaxV_eq2 {avail mv nc f0 : Nat}
    (hlt : avail - fullFixedBytes (mv + s7BvaCap avail mv nc f0) < nc * 40 + 136) :
    s7CalcMaxV avail mv nc f0 = mv := by
  unfold s7CalcMaxV; dsimp only; exact ite_eq_left_iff.mpr fun h => absurd (Or.inr hlt) h
private theorem s7CalcMaxV_eq3 {avail mv nc f0 : Nat}
    (h1 : ¬ avail < fullFixedBytes (mv + s7BvaCap avail mv nc f0))
    (h2 : ¬ avail - fullFixedBytes (mv + s7BvaCap avail mv nc f0) < nc * 40 + 136) :
    s7CalcMaxV avail mv nc f0 = mv + s7BvaCap avail mv nc f0 := by
  unfold s7CalcMaxV; dsimp only; exact ite_eq_right_iff.mpr fun h => absurd h (by omega)

private theorem s7_calc_max_v_post_wp (Γ : Env)
    (hFixed : ∀ a m Q X, Full.fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hQ : Q (BitVec.ofNat 64 (s7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var mv,
        Arg.var (BitVec.ofNat 64 (s7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat)), ()))
        fun p =>
      Expr.call "full_fixed_bytes" (as := [i64]) (bs := [i64]) (Arg.var p.fst, ()) fun p_1 =>
      Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var avail, Arg.var p_1.fst, ()))
        fun p_2 =>
      Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.var mv, ()))
        (Expr.let_ (Op.mk (.sub i64) (Arg.var avail, Arg.var p_1.fst, ())) fun p_2 =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 40, ())) fun p_3 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_3.fst, Arg.imm 136, ())) fun p_4 =>
          Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
            (Arg.var p_2.fst, Arg.var p_4.fst, ())) fun p_2 =>
          Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.var mv, ()))
            (Expr.ret (Arg.var p.fst, ())))) m := by
  let bva := s7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat
  have hbva_le : bva ≤ 32768 := s7BvaCap_le _ _ _ _
  have hmv_b := hmv; have hnc_b := hnc; unfold dimacsBound at hmv_b hnc_b
  let max_v := mv.toNat + bva
  have hmax_bd : max_v < 2 * dimacsBound := by unfold dimacsBound; omega
  have hfx_lt : fullFixedBytes max_v < 2 ^ 64 := by have := fullFixedBytes_lt hmax_bd; omega
  have hmv_add : mv + BitVec.ofNat 64 bva = BitVec.ofNat 64 max_v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, s7_bv64_ofNat (by omega), s7_bv64_ofNat (by omega),
      Nat.mod_eq_of_lt (by omega)]
  c0_hsteps_nogrp; rw [hmv_add]
  refine wp_call_of_spec _ _ (hFixed _ _ _ _ ⟨?_, ?_⟩)
  · dsimp only [Arg.val_var]; rw [s7_bv64_ofNat (by omega)]; exact hmax_bd
  · dsimp only [Arg.val_var]; rw [s7_bv64_ofNat (by omega)]
    have hav_lt := avail.isLt
    c0_hsteps_nogrp
    · have hlt1 : avail.toNat < fullFixedBytes max_v := by
        rwa [Nat.mod_eq_of_lt hfx_lt] at hc
      rw [s7CalcMaxV_eq1 hlt1, BitVec.ofNat_toNat] at hQ; exact hQ
    · rename_i hge1; rw [Nat.mod_eq_of_lt hfx_lt] at hge1
      have hm1 : (2 ^ 64 - fullFixedBytes max_v + avail.toNat) % 2 ^ 64 =
          avail.toNat - fullFixedBytes max_v := by omega
      have hm2 : (nc.toNat * 40 + 136) % 2 ^ 64 = nc.toNat * 40 + 136 :=
        Nat.mod_eq_of_lt (by omega)
      have hlt2 : avail.toNat - fullFixedBytes max_v < nc.toNat * 40 + 136 := by
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt, hm1, hm2] using hc
      rw [s7CalcMaxV_eq2 hlt2, BitVec.ofNat_toNat] at hQ; exact hQ
    · rename_i hge1; rw [Nat.mod_eq_of_lt hfx_lt] at hge1
      have hm1 : (2 ^ 64 - fullFixedBytes max_v + avail.toNat) % 2 ^ 64 =
          avail.toNat - fullFixedBytes max_v := by omega
      have hm2 : (nc.toNat * 40 + 136) % 2 ^ 64 = nc.toNat * 40 + 136 :=
        Nat.mod_eq_of_lt (by omega)
      have hge2 : ¬ avail.toNat - fullFixedBytes max_v < nc.toNat * 40 + 136 := by
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt, hm1, hm2] using hc
      rw [s7CalcMaxV_eq3 hge1 hge2] at hQ; exact hQ

private theorem s7_bva_ult_eq (avail f0 nc : Val i64) (hfle : f0.toNat ≤ avail.toNat)
    (hnc : nc.toNat < dimacsBound) :
    ((nc * (48 : BitVec 64) + 8192).ult (avail - f0)) =
      decide (nc.toNat * 48 + 8192 < avail.toNat - f0.toNat) := by
  have hnc_b := hnc; unfold dimacsBound at hnc_b; have hav_lt := avail.isLt
  have hrem_eq : avail - f0 = BitVec.ofNat 64 (avail.toNat - f0.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [s7_bv64_sub hfle, s7_bv64_ofNat (by omega)]
  have hnc48 : nc * (48 : BitVec 64) + (8192 : BitVec 64) =
      BitVec.ofNat 64 (nc.toNat * 48 + 8192) := by
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, s7_bv64_mul]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, s7_bv64_ofNat (by omega),
      show (8192 : BitVec 64).toNat = 8192 from rfl, s7_bv64_ofNat (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hrem_eq, hnc48, s7_bv64_ult (by omega) (by omega)]

private abbrev s7BvaMinExpr (nc remv : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_4 =>
    Expr.let_ (Op.mk (.sub i64) (Arg.var remv, Arg.var p_4.fst, ())) fun p_5 =>
    Expr.let_ (Op.mk (.sub i64) (Arg.var p_5.fst, Arg.imm 4096, ())) fun p_6 =>
    Expr.let_ (Op.mk (.udiv 64) (Arg.var p_6.fst, Arg.imm 2688, ())) fun p_7 =>
    Expr.group (sig := [[i64]])
      (fun _ => Blocks.cons (fun p_8 => Expr.jump J (Arg.var p_8.fst, ())) Blocks.nil)
      fun Js =>
        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.imm 32768, Arg.var p_7.fst, ()))
          fun p =>
        Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 32768, ()))
          (Expr.jump Js.fst (Arg.var p_7.fst, ()))

private theorem s7_calc_bva_min_wp (Γ : Env)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J : Cont [i64]}
    (hmv_ge : 2 ≤ mv.toNat) (hnc : nc.toNat < dimacsBound) (hfle : f0.toNat ≤ avail.toNat)
    (hgt : nc.toNat * 48 + 8192 < avail.toNat - f0.toNat)
    (hJ : ∀ xs m_1, xs.1 = BitVec.ofNat 64 (s7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧
      m_1 = m → J xs m_1) :
    wp Γ Q X (s7BvaMinExpr nc (BitVec.ofNat 64 (avail.toNat - f0.toNat)) J) m := by
  have hnc_b := hnc; unfold dimacsBound at hnc_b; have hav_lt := avail.isLt
  let rem0 := avail.toNat - f0.toNat
  let max_bva := (rem0 - nc.toNat * 48 - 4096) / 2688
  dsimp only [s7BvaMinExpr]; fp_head_steps
  have h48 : (nc * (48 : BitVec 64)).toNat = nc.toNat * 48 := by
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, s7_bv64_mul,
      s7_bv64_ofNat (by omega)]
  have hsub1 : (BitVec.ofNat 64 rem0 - nc * (48 : BitVec 64)).toNat = rem0 - nc.toNat * 48 := by
    rw [s7_bv64_sub (by rw [s7_bv64_ofNat (by dsimp [rem0]; omega), h48]; dsimp [rem0]; omega),
      s7_bv64_ofNat (by dsimp [rem0]; omega), h48]
  have hsub3 : BitVec.ofNat 64 rem0 - nc * (48 : BitVec 64) - (4096 : BitVec 64) =
      BitVec.ofNat 64 (rem0 - nc.toNat * 48 - 4096) := by
    apply BitVec.eq_of_toNat_eq; have h4096 : (4096 : BitVec 64).toNat = 4096 := rfl
    rw [s7_bv64_sub (by rw [hsub1, h4096]; dsimp [rem0]; omega), hsub1, h4096,
      s7_bv64_ofNat (by dsimp [rem0]; omega)]
  rw [hsub3]; apply wp_udiv_of
  · dsimp only [Arg.val_imm]; intro h; have := congrArg BitVec.toNat h; simp at this
  · dsimp only [Arg.val_var, Arg.val_imm]
    have hmb64 : max_bva < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by dsimp [rem0]; omega)
    have hdiv_eq : BitVec.ofNat 64 (rem0 - nc.toNat * 48 - 4096) / (2688 : BitVec 64) =
        BitVec.ofNat 64 max_bva := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_udiv, s7_bv64_ofNat (by dsimp [rem0]; omega),
        show (2688 : BitVec 64).toNat = 2688 from rfl, s7_bv64_ofNat hmb64]
    rw [hdiv_eq]
    refine wp_join_group (ts := [i64]) (fun v mx =>
      v.1 = BitVec.ofNat 64 (s7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧ mx = m) ?_ ?_
    · rintro _ ⟨bx_v, ⟨⟩⟩ mx ⟨rfl, rfl⟩
      simp only [Blocks.get_here]; fp_head_steps; exact hJ (_, ()) _ ⟨rfl, rfl⟩
    · intro Jm hJm; fp_head_steps
      rw [show (32768 : BitVec 64) = BitVec.ofNat 64 32768 from rfl,
        s7_bv64_ult (by omega) hmb64]
      refine wp_jnz_of (fun hclt => ?_) (fun hcge => ?_)
      · dsimp only [Arg.val_var] at hclt; rw [decide_eq_true_eq] at hclt; fp_head_steps
        refine hJm (_, ()) m ⟨?_, rfl⟩; unfold s7BvaCap
        rw [ite_eq_left_iff.mpr fun h => absurd (And.intro hmv_ge hgt) h]
        exact congrArg (BitVec.ofNat 64) (Nat.min_eq_left (Nat.le_of_lt hclt)).symm
      · dsimp only [Arg.val_var] at hcge; rw [decide_eq_false_iff_not] at hcge; fp_head_steps
        refine hJm (_, ()) m ⟨?_, rfl⟩; unfold s7BvaCap
        rw [ite_eq_left_iff.mpr fun h => absurd (And.intro hmv_ge hgt) h]
        exact congrArg (BitVec.ofNat 64) (Nat.min_eq_right (Nat.le_of_not_gt hcge)).symm

private theorem s7_calc_max_v_bva_wp (Γ : Env)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J : Cont [i64]}
    (hnc : nc.toNat < dimacsBound) (hfle : f0.toNat ≤ avail.toNat)
    (hJ : ∀ xs m_1, xs.1 = BitVec.ofNat 64 (s7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧
      m_1 = m → J xs m_1) :
    wp Γ Q X (Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl) (Arg.var mv, Arg.imm 2, ())) fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_1 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_1.fst, Arg.imm 8192, ())) fun p_2 =>
          Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var (avail - f0), Arg.var p_2.fst, ()))
            fun p_3 =>
            Expr.jnz (Arg.var p_3.fst) (s7BvaMinExpr nc (avail - f0) J)
              (Expr.jump J (Arg.imm 0, ())))
        (Expr.jump J (Arg.imm 0, ()))) m := by
  have hav_lt := avail.isLt
  have hrem_eq : avail - f0 = BitVec.ofNat 64 (avail.toNat - f0.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [s7_bv64_sub hfle, s7_bv64_ofNat (by omega)]
  fp_head_steps
  have hule2 : ((2 : BitVec 64).ule mv) = decide (2 ≤ mv.toNat) := by simp [BitVec.ule]
  rw [hule2]
  refine wp_jnz_of (fun hmv_ge => ?_) (fun hmv_lt => ?_)
  · dsimp only [Arg.val_var] at hmv_ge; rw [decide_eq_true_eq] at hmv_ge; fp_head_steps
    rw [s7_bva_ult_eq avail f0 nc hfle hnc]
    refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
    · dsimp only [Arg.val_var] at hgt; rw [decide_eq_true_eq] at hgt; fp_head_steps
      rw [hrem_eq]; exact s7_calc_bva_min_wp Γ hmv_ge hnc hfle hgt hJ
    · dsimp only [Arg.val_var] at hle; rw [decide_eq_false_iff_not] at hle; fp_head_steps
      refine hJ (0#64, ()) m ⟨?_, rfl⟩; unfold s7BvaCap
      rw [ite_eq_right_iff.mpr fun h => absurd h.2 hle]
  · dsimp only [Arg.val_var] at hmv_lt; rw [decide_eq_false_iff_not] at hmv_lt; fp_head_steps
    refine hJ (0#64, ()) m ⟨?_, rfl⟩; unfold s7BvaCap
    rw [ite_eq_right_iff.mpr fun h => absurd h.1 hmv_lt]

private theorem s7_calc_max_v_exact_wp (Γ : Env)
    (hFixed : ∀ a m Q X, Full.fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hle : f0.toNat ≤ avail.toNat)
    (hQ : Q (BitVec.ofNat 64 (s7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    Func.wp Γ fidStep7CalcMaxVFn.body (avail, mv, nc, f0, ()) m Q X := by
  unfold Func.wp fidStep7CalcMaxVFn FullFidelityStep7.full_calc_max_v_body; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun v mb =>
    v.1 = BitVec.ofNat 64 (s7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧ mb = m) ?_ ?_
  · rintro _ ⟨bv_v, ⟨⟩⟩ mb ⟨rfl, rfl⟩
    simp only [Blocks.get_here]; exact s7_calc_max_v_post_wp Γ hFixed hmv hnc hQ
  · intro J hJ; exact s7_calc_max_v_bva_wp Γ hnc hle hJ

/-- Step-7 `full_calc_max_v` (`bva_cap = min 32768 ((rem0 - 48 nc - 4096) / 2688)`) satisfies
`Full.fullCalcMaxVSpec`. -/
theorem full_calc_max_v_step7_wp (Γ : Env)
    (hFixed : ∀ a m Q X, Full.fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullCalcMaxVSpec a m Q X →
      Func.wp Γ fidStep7CalcMaxVFn.body a m Q X := by
  rintro ⟨avail, mv, nc, f0, ⟨⟩⟩ m Q X ⟨hmv, hnc, hf0, hle, hQ⟩
  have hbva_le := s7BvaCap_le avail.toNat mv.toNat nc.toNat f0.toNat
  have hmv_b : mv.toNat < 2 ^ 28 := hmv; have hnc_b : nc.toNat < 2 ^ 28 := hnc
  have hret_lt : s7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat < 2 * dimacsBound := by
    unfold s7CalcMaxV dimacsBound at *; dsimp only; split <;> omega
  have hret_toNat := s7_bv64_ofNat (n := s7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat)
    (by unfold dimacsBound at hret_lt; omega)
  refine s7_calc_max_v_exact_wp Γ hFixed hmv hnc (by omega) ?_
  refine hQ _ (by rw [hret_toNat]; unfold s7CalcMaxV; dsimp only; split <;> omega)
    (by rw [hret_toNat]; exact hret_lt)
    (by rw [hret_toNat, hf0]; exact s7CalcMaxV_fits (by omega))

end CalcMaxV

/-! ## 2. `full_calc_scr_cap_m5` (`8M` cap) & `full_init_state_m5` Rewire -/

section ScrCap

open Full.FullParseInitSpecs
open Full.FullParseInitHelpers
open scoped Full.FullParseInitTactics
open FullM5Orch

private def s7CalcScrCap (rem : Nat) : Nat :=
  if rem < 8192 then 0 else
    let c := if 16384 ≤ rem then rem / 16 else rem / 32
    ((min c 8388608) / 2) * 2

private theorem s7CalcScrCap_le (rem : Nat) : s7CalcScrCap rem ≤ 8388608 := by
  unfold s7CalcScrCap; split; omega; dsimp only; split <;> omega

private theorem s7CalcScrCap_four_mul_le (rem : Nat) :
    4 * s7CalcScrCap rem ≤ rem / 4 := by
  unfold s7CalcScrCap; split; omega; dsimp only; split <;> omega

private theorem s7_bv64_ule_nat {a b : BitVec 64} : a.ule b = decide (a.toNat ≤ b.toNat) := by
  simp [BitVec.ule]

private theorem s7_bv64_ult_nat {a b : BitVec 64} : a.ult b = decide (a.toNat < b.toNat) := by
  simp [BitVec.ult]

private theorem s7_fp_shr4 (x : BitVec 64) :
    x >>> (((4 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (x.toNat / 16) := by
  have h := fp_shr_sext4 x.isLt; rwa [bv_ofNat_toNat_eq x] at h

private theorem s7_fp_shr5 (x : BitVec 64) :
    x >>> (((5 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (x.toNat / 32) := by
  have h := fp_shr_sext5 x.isLt; rwa [bv_ofNat_toNat_eq x] at h

local macro "s7_fp_jnz_t" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_true_eq] at $h:ident; fp_head_steps))
local macro "s7_fp_jnz_f" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_false_iff_not] at $h:ident;
   fp_head_steps))

/-- Step-7 `full_calc_scr_cap_m5` (`8M` cap) satisfies `fullCalcScrCapOfSpec 8388608`. -/
theorem full_calc_scr_cap_m5_step7_wp (Γ : Env) :
    ∀ a m Q X, fullCalcScrCapOfSpec 8388608 a m Q X →
      Func.wp Γ fidStep7CalcScrCapM5Fn.body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X hQ
  have hle := s7CalcScrCap_le rem.toNat
  have h4 := s7CalcScrCap_four_mul_le rem.toNat
  have hQ' := hQ (BitVec.ofNat 64 (s7CalcScrCap rem.toNat))
    (by rw [bv64_ofNat_toNat (by omega)]; exact hle)
    (fun hlt => by unfold s7CalcScrCap; simp [hlt])
    (by rw [bv64_ofNat_toNat (by omega)]; exact h4)
  show Func.wp Γ FullFidelityStep7.full_calc_scr_cap_m5_body _ m Q X
  unfold Func.wp FullFidelityStep7.full_calc_scr_cap_m5_body; fp_head_steps
  rw [s7_bv64_ult_nat, show (8192 : BitVec 64).toNat = 8192 from rfl]
  refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
  · s7_fp_jnz_t hlt
    have heq : s7CalcScrCap rem.toNat = 0 := by unfold s7CalcScrCap; simp [hlt]
    rw [heq] at hQ'; exact hQ'
  · s7_fp_jnz_f hge
    refine wp_join_group (fun (v : Tup Val [i64]) mc0 =>
      v.1 = BitVec.ofNat 64 (if 16384 ≤ rem.toNat then rem.toNat / 16 else rem.toNat / 32) ∧
        mc0 = m) ?_ ?_
    · rintro _ ⟨c0, ⟨⟩⟩ mc0 ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
      let raw := if 16384 ≤ rem.toNat then rem.toNat / 16 else rem.toNat / 32
      have hraw64 : raw < 2 ^ 64 := by dsimp [raw]; have := rem.isLt; split <;> omega
      refine wp_join_group
        (fun (v : Tup Val [i64]) mc1 => v.1 = BitVec.ofNat 64 (min raw 8388608) ∧ mc1 = mc0)
        ?_ ?_
      · rintro _ ⟨c1, ⟨⟩⟩ mc1 ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
        rw [fp_and_not1, bv64_ofNat_toNat (by omega)]
        have heq : s7CalcScrCap rem.toNat = (min raw 8388608 / 2) * 2 := by
          unfold s7CalcScrCap; simp [hge, raw]
        rw [heq] at hQ'; exact hQ'
      · intro J1 hJ1; fp_head_steps
        rw [show (8388608 : BitVec 64) = BitVec.ofNat 64 8388608 from rfl,
          bv_ult_eq (by decide) hraw64]
        refine wp_jnz_of (fun hgt => ?_) (fun hle2 => ?_)
        · s7_fp_jnz_t hgt; refine hJ1 (_, ()) mc0 ⟨?_, rfl⟩; rw [Nat.min_eq_right (by omega)]
        · s7_fp_jnz_f hle2; refine hJ1 (_, ()) mc0 ⟨?_, rfl⟩; rw [Nat.min_eq_left (by omega)]
    · intro J0 hJ0; fp_head_steps
      rw [show (16384 : BitVec 64).ule rem = decide (16384 ≤ rem.toNat) from by
        rw [s7_bv64_ule_nat]; rfl]
      refine wp_jnz_of (fun hge2 => ?_) (fun hlt2 => ?_)
      · s7_fp_jnz_t hge2; rw [s7_fp_shr4 rem]; exact hJ0 (_, ()) m ⟨by simp [hge2], rfl⟩
      · s7_fp_jnz_f hlt2; rw [s7_fp_shr5 rem]; exact hJ0 (_, ()) m ⟨by simp [hlt2], rfl⟩

/-- Rewired `full_init_state_m5` against `Full.fullInitStateSpec` with the Step-7 `8M`
`full_calc_scr_cap_m5` contract (`fullCalcScrCapOfSpec 8388608`). -/
theorem full_init_state_m5_step7_wp (Γ : Env)
    (hHdr : ∀ a m Q X, Kissat.kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hFixed : ∀ a m Q X, Full.fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    (hMaxV : ∀ a m Q X, Full.fullCalcMaxVSpec a m Q X →
      Γ "full_calc_max_v" [i64, i64, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullCalcExtCapM5Spec a m Q X →
      Γ "full_calc_ext_cap_m5" [i64] [i64] a m Q X)
    (hScr : ∀ a m Q X, fullCalcScrCapOfSpec 8388608 a m Q X →
      Γ "full_calc_scr_cap_m5" [i64] [i64] a m Q X)
    (hArenas : ∀ a m Q X, Full.fullInitArenasSpec a m Q X →
      Γ "full_init_arenas" [i64, i64, i64, i64] [] a m Q X)
    (hInitHdr : ∀ a m Q X, Full.fullInitHdrSpec a m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] a m Q X)
    (hZt1 : ∀ a m Q X, Full.fullZeroTables1Spec a m Q X →
      Γ "full_zero_tables1" [i64] [] a m Q X)
    (hZt2 : ∀ a m Q X, Full.fullZeroTables2Spec a m Q X →
      Γ "full_zero_tables2" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Func.wp Γ FullM5Orch.full_init_state_m5_body a m Q X :=
  full_init_state_m5_wp_of_cap 8388608 (by unfold dimacsBound; omega) Γ hHdr hFixed hMaxV hExt
    hScr hArenas hInitHdr hZt1 hZt2

end ScrCap

/-! ## 3. `m6_hdr_init` (`watermarks[1] = 0`) -/

section HdrInit

open FullM6Hdr
open scoped FullM6Hdr.M6HdrTactics

/-- Step-7 `m6_hdr_init` (`e[25] = 0`) satisfies the unchanged `FullM6Hdr.m6HdrInitSpec`. -/
theorem m6_hdr_init_step7_wp (Γ : Env) :
    ∀ a m Q X, m6HdrInitSpec a m Q X → Func.wp Γ fidStep7M6HdrInitFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  rw [fullM6HdrMem_iff] at hm
  show Func.wp Γ FullFidelityStep7.m6_hdr_init_body _ m Q X
  unfold Func.wp FullFidelityStep7.m6_hdr_init_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (i, ()) m1 => i.toNat ≤ 288 ∧ ∃ ext1 : List (BitVec 64),
      ext1.length = 288 ∧ (FullMem c s ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) m1)
    (fun (i, ()) _ => 288 - i.toNat)
    (fun L hL => by c0_hsteps; exact hL (0#64, ()) m ⟨by simp, ext, hext.len, hm⟩)
    (fun L (i, ()) m1 ⟨hi_le, ext1, hl1, hm1⟩ ih => ?_)
  c0_hsteps
  · have hi_lt : i.toNat < 288 := by c0_bound
    have hi_len : i.toNat < ext1.length := by rw [hl1]; exact hi_lt
    c0_hsteps
    exact ih _ _ (by c0_bound) ⟨by c0_bound, ext1.set i.toNat 0, by simp [hl1], by assumption⟩
  · have h288 : ext1.length = 288 := hl1
    c0_hsteps
    refine hQ _ _ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    refine ⟨by simp only [List.length_set, h288, fullM6ExtWords], ?_⟩
    rw [show (0 : BitVec 64).toNat = 0 from rfl,
      List.getElem?_set_self (by simp only [List.length_set, h288]; omega)]
    rfl

end HdrInit

/-! ## 4. `full_walk_cb_inv_m7` (`step7CbInvSpec`) & `full_walk_m7` Rewire -/

section WalkCbInv

open FullM7Walk

private theorem s7_cb_piece_le {base coef lo hi avg : BitVec 64}
    (hb : base.toNat ≤ 4000) (hc : coef.toNat ≤ 2500)
    (h1 : lo.toNat ≤ avg.toNat) (h2 : avg.toNat < hi.toNat)
    (hd : hi.toNat - lo.toNat ≤ 65536) :
    (base + ((coef * (avg - lo)) >>> (16 : Nat))).toNat ≤ 600000 := by
  have hsub : (avg - lo).toNat < 65536 := by
    rw [BitVec.toNat_sub]; have := avg.isLt; have := lo.isLt; omega
  have hprod : (coef * (avg - lo)).toNat ≤ 2500 * 65536 := by
    have hm := Nat.mul_le_mul hc (Nat.le_of_lt hsub)
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]; exact hm
  have hsh : ((coef * (avg - lo)) >>> (16 : Nat)).toNat ≤ 2500 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  rw [BitVec.toNat_add]; omega

/-- Step-7 `full_walk_cb_inv_m7` (fixed `walk_cnt_stat & 1` parity guard) satisfies
`step7CbInvSpec` (`1 ≤ r ≤ 32768`, state unchanged). -/
theorem full_walk_cb_inv_m7_step7_wp (Γ : Env) :
    ∀ a m Q X, step7CbInvSpec a m Q X → Func.wp Γ fidStep7WalkCbInvM7Fn.body a m Q X := by
  rintro ⟨h, ncl, tot_lits, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hret_def : Q (32768#64, ()) m :=
    hQ (32768#64, ()) s m rfl hlen ⟨rfl, by decide, by decide⟩ hm
  show Func.wp Γ FullFidelityStep7.full_walk_cb_inv_m7_body _ m Q X
  unfold Func.wp FullFidelityStep7.full_walk_cb_inv_m7_body
  s7_hsteps_nj
  · exact hret_def
  · exact hret_def
  · refine wp_join_group (ts := [i64]) (fun (occ, ()) m1 =>
        (FullMem c s ⋆ R) m1 ∧ occ.toNat ≤ 0x0000FFFFFFFFFFFF) ?_ ?_
    · rintro _ ⟨occ, ⟨⟩⟩ m1 ⟨hm1, hocc_le⟩
      s7_hsteps_nj
      refine wp_join_group (ts := [i64]) (fun (cb, ()) m2 =>
          (FullMem c s ⋆ R) m2 ∧ cb.toNat ≤ 600000) ?_ ?_
      · rintro _ ⟨cb, ⟨⟩⟩ m2 ⟨hm2, hcb_ub⟩
        s7_hsteps_nj
        refine wp_join_group (ts := [i64]) (fun (cb', ()) m3 =>
            (FullMem c s ⋆ R) m3 ∧ 2000 ≤ cb'.toNat ∧ cb'.toNat ≤ 600000) ?_ ?_
        · rintro _ ⟨cb', ⟨⟩⟩ m3 ⟨hm3, hcb1, hcb2⟩
          have hcb'_ne : cb' ≠ 0#64 := by
            intro hz; have := congrArg BitVec.toNat hz; simp at this; omega
          s7_hsteps_nj
          refine wp_join_group (ts := [i64]) (fun (inv, ()) m4 =>
              (FullMem c s ⋆ R) m4 ∧ 1 ≤ inv.toNat ∧ inv.toNat ≤ 65536) ?_ ?_
          · rintro _ ⟨inv, ⟨⟩⟩ m4 ⟨hm4, hinv1, hinv2⟩
            s7_hsteps_nj
            refine wp_join_group (ts := [i64]) (fun (inv', ()) m5 =>
                (FullMem c s ⋆ R) m5 ∧ 1 ≤ inv'.toNat ∧ inv'.toNat ≤ 32768) ?_ ?_
            · rintro _ ⟨inv', ⟨⟩⟩ m5 ⟨hm5, hi1, hi2⟩
              s7_hsteps_nj
              exact hQ (inv', ()) s m5 rfl hlen ⟨rfl, hi1, hi2⟩ hm5
            · intro Jf hJf; s7_hsteps_nj
              · exact hJf (32768#64, ()) m4 ⟨hm4, by decide, by decide⟩
              · exact hJf (inv, ()) m4 ⟨hm4, hinv1, by c0_bound⟩
          · intro Ji hJi; s7_hsteps_nj
            · exact hJi (1#64, ()) m3 ⟨hm3, by decide, by decide⟩
            · have hnum_le : ((65536000 : BitVec 64) + cb' >>> (1 : Nat)).toNat ≤ 65836000 := by
                c0_bound
              have hdiv_le :
                  (((65536000 : BitVec 64) + cb' >>> (1 : Nat)) / cb').toNat ≤ 65536 := by
                rw [BitVec.toNat_udiv]
                have hmul : 65836000 ≤ cb'.toNat * 65536 :=
                  Nat.le_trans (show 65836000 ≤ 2000 * 65536 by decide)
                    (Nat.mul_le_mul_right 65536 hcb1)
                exact Nat.div_le_of_le_mul (Nat.le_trans hnum_le hmul)
              have hnz : (((65536000 : BitVec 64) + cb' >>> (1 : Nat)) / cb') ≠ 0#64 := ‹_›
              have hpos : 1 ≤ (((65536000 : BitVec 64) + cb' >>> (1 : Nat)) / cb').toNat :=
                Nat.pos_of_ne_zero fun h0 => hnz (BitVec.eq_of_toNat_eq h0)
              exact hJi (_, ()) m3 ⟨hm3, hpos, hdiv_le⟩
        · intro Jc hJc; s7_hsteps_nj
          · exact hJc (2000#64, ()) m2 ⟨hm2, by decide, by decide⟩
          · exact hJc (cb, ()) m2 ⟨hm2, by c0_bound, hcb_ub⟩
      · intro Jb hJb; s7_hsteps_nj
        · have havg_lt : (occ <<< (16 : Nat) / ncl).toNat < 196608 := by c0_bound
          have hm500 : (500#64 * (occ <<< (16 : Nat) / ncl)).toNat < 500 * 196608 := by
            rw [BitVec.toNat_mul, show (500#64 : BitVec 64).toNat = 500 from rfl,
              Nat.mod_eq_of_lt (by omega)]; omega
          have hd : (500#64 * (occ <<< (16 : Nat) / ncl) / 196608#64).toNat ≤ 500 := by
            rw [BitVec.toNat_udiv, show (196608#64 : BitVec 64).toNat = 196608 from rfl]
            omega
          have hcb_le :
              (2000#64 + 500#64 * (occ <<< (16 : Nat) / ncl) / 196608#64).toNat ≤ 600000 := by
            rw [BitVec.toNat_add, show (2000#64 : BitVec 64).toNat = 2000 from rfl]; omega
          exact hJb (_, ()) m1 ⟨hm1, hcb_le⟩
        · refine wp_join_group (ts := [i64]) (fun (cb1, ()) m2 =>
              (FullMem c s ⋆ R) m2 ∧ cb1.toNat ≤ 600000)
            (fun _ ⟨cb1, ⟨⟩⟩ m2 hm2 => hJb (cb1, ()) m2 hm2) ?_
          intro Jb1 hJb1; s7_hsteps_nj
          · exact hJb1 (_, ()) m1 ⟨hm1, s7_cb_piece_le (base := 2500#64) (coef := 350#64)
              (lo := 196608#64) (hi := 262144#64) (by decide) (by decide)
              (by c0_bound) (by c0_bound) (by decide)⟩
          · refine wp_join_group (ts := [i64]) (fun (cb2, ()) m2 =>
                (FullMem c s ⋆ R) m2 ∧ cb2.toNat ≤ 600000)
              (fun _ ⟨cb2, ⟨⟩⟩ m2 hm2 => hJb1 (cb2, ()) m2 hm2) ?_
            intro Jb2 hJb2; s7_hsteps_nj
            · exact hJb2 (_, ()) m1 ⟨hm1, s7_cb_piece_le (base := 2850#64) (coef := 850#64)
                (lo := 262144#64) (hi := 327680#64) (by decide) (by decide)
                (by c0_bound) (by c0_bound) (by decide)⟩
            · refine wp_join_group (ts := [i64]) (fun (cb3, ()) m2 =>
                  (FullMem c s ⋆ R) m2 ∧ cb3.toNat ≤ 600000)
                (fun _ ⟨cb3, ⟨⟩⟩ m2 hm2 => hJb2 (cb3, ()) m2 hm2) ?_
              intro Jb3 hJb3; s7_hsteps_nj
              · exact hJb3 (_, ()) m1 ⟨hm1, s7_cb_piece_le (base := 3700#64) (coef := 1400#64)
                  (lo := 327680#64) (hi := 393216#64) (by decide) (by decide)
                  (by c0_bound) (by c0_bound) (by decide)⟩
              · refine wp_join_group (ts := [i64]) (fun (ex, ()) m2 =>
                    (FullMem c s ⋆ R) m2 ∧ ex.toNat ≤ 2621440) ?_ ?_
                · rintro _ ⟨ex, ⟨⟩⟩ m2 ⟨hm2, hex⟩
                  s7_hsteps_nj
                  have hr_le : (((2300 : BitVec 64) * ex) >>> (16 : Nat)).toNat ≤ 92000 := by
                    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul,
                      show (2300 : BitVec 64).toNat = 2300 from rfl,
                      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]; omega
                  have hcb5 :
                      (5100#64 + (((2300 : BitVec 64) * ex) >>> (16 : Nat))).toNat ≤ 600000 := by
                    rw [BitVec.toNat_add, show (5100#64 : BitVec 64).toNat = 5100 from rfl]
                    omega
                  exact hJb3 (_, ()) m2 ⟨hm2, hcb5⟩
                · intro Jex hJex; s7_hsteps_nj
                  · exact hJex (2621440#64, ()) m1 ⟨hm1, by decide⟩
                  · exact hJex (_, ()) m1 ⟨hm1, by c0_bound⟩
    · intro Jo hJo; s7_hsteps_nj
      · exact hJo (0x0000FFFFFFFFFFFF#64, ()) m ⟨hm, by decide⟩
      · exact hJo (tot_lits, ()) m ⟨hm, by c0_bound⟩

/-- Rewired `full_walk_m7` against `Full.fullWalkSpec` with the Step-7 `step7CbInvSpec` contract
for `full_walk_cb_inv_m7`. -/
theorem full_walk_m7_step7_wp (Γ : Env)
    (hInitVals : ∀ a m Q X, m7InitValsSpec a m Q X →
      Γ "full_walk_init_vals_m7" [i64] [] a m Q X)
    (hCollect : ∀ a m Q X, m7CollectSpec a m Q X →
      Γ "full_walk_collect_m7" [i64] [i64] a m Q X)
    (hCbInv : ∀ a m Q X, step7CbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    (hInitTable : ∀ a m Q X, m7InitTableSpec a m Q X →
      Γ "full_walk_init_table_m7" [i64, i64] [] a m Q X)
    (hBuildOcc : ∀ a m Q X, m7BuildOccSpec a m Q X →
      Γ "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X)
    (hEffort : ∀ a m Q X, m7EffortSpec a m Q X →
      Γ "full_walk_effort_m7" [i64, i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, m7PickSpec a m Q X →
      Γ "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X)
    (hFlip : ∀ a m Q X, m7FlipSpec a m Q X →
      Γ "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hSaveMin : ∀ a m Q X, m7SaveMinSpec a m Q X →
      Γ "full_walk_save_min_m7" [i64, i64, Ty.bool] [] a m Q X) :
    ∀ a m Q X, Full.fullWalkSpec a m Q X → Func.wp Γ full_walk_m7_body a m Q X :=
  fun a m Q X hS => full_walk_m7_wp_gen Γ hInitVals hCollect hCbInv hInitTable hBuildOcc
    hEffort hPick hFlip hSaveMin a m Q X hS

end WalkCbInv

end LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0

end
