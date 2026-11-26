/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep9MemShrink
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof0
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5Proof
public import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof1
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.Examples.Kissat.DimacsLemmas1
import LeanQbe.T.Logic.BitVec
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Step-9 Experimental `MemShrinkV5` Leaf Proofs (`FullFidelityStep9MemShrinkProof0`, `S9-P0.3`)

M1-clean UNSAT-only leaf WP proofs (`public section`, zero exposed theorems):
1. `s9msCalcMaxVSpec` & `full_calc_max_v_s9ms_wp`: Step-7 `cand = 32768ULL` BVA cap.
2. `s9msCalcScrCapSpec` & `full_calc_scr_cap_m5_s9ms_wp`: `scr_cap = 8388608ULL` cap.
3. Reuses of the `12` unchanged `FullM7MemShrinkV5` WP proofs plus `full_init_state_m5_s9ms_wp`
   and `full_init_state_s9ms_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep9MemShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullParseInitHelpers
open LeanQbe.T.Examples.Kissat.Full.FullParseInitSpecs
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullFidelityStep9
open LeanQbe.T.Examples.Kissat.FullM7MemShrink hiding
  full_fill_u64_m7_body full_fill_u64_m7_wf full_trans_bytes_m7_body full_trans_bytes_m7_wf
open LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5 hiding
  full_fill_u64_m7_body full_fill_u64_m7_wf full_trans_bytes_m7_body full_trans_bytes_m7_wf
  full_calc_max_v_m7v5_body full_calc_max_v_m7v5_wf
open scoped FullArenaTactics FullParseInitTactics
open Kraken.Bedrock2.Test

/-! ## 1. Step-9 `cand = 32768` BVA Sizing (`s9msCalcMaxVSpec`) -/
section CalcMaxVV5

/-- V5 BVA headroom (`cand = 32768ULL`, Step-9 S9-P0.3) matching `full_calc_max_v`. -/
def s9msBvaCap (avail mv nc f0 : Nat) : Nat :=
  if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
    min 32768 (((avail - f0) - nc * 48 - 4096) / 2688)
  else 0

/-- Variable capacity limit selected by `full_calc_max_v`. -/
def s9msCalcMaxV (avail mv nc f0 : Nat) : Nat :=
  let cand := mv + s9msBvaCap avail mv nc f0
  let need := m7FixedBytes cand + m7TransBytes cand
  if avail < need ∨ avail - need < nc * 40 + 136 then mv else cand

theorem s9msBvaCap_eq (avail mv nc f0 : Nat) :
    s9msBvaCap avail mv nc f0 =
      if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
        min 32768 (((avail - f0) - nc * 48 - 4096) / 2688)
      else 0 := by unfold s9msBvaCap; rfl

theorem s9msCalcMaxV_eq (avail mv nc f0 : Nat) :
    s9msCalcMaxV avail mv nc f0 =
      let cand := mv + s9msBvaCap avail mv nc f0
      let need := m7FixedBytes cand + m7TransBytes cand
      if avail < need ∨ avail - need < nc * 40 + 136 then mv else cand := by
  unfold s9msCalcMaxV; rfl

theorem s9msBvaCap_le (avail mv nc f0 : Nat) : s9msBvaCap avail mv nc f0 ≤ 32768 := by
  unfold s9msBvaCap; split <;> omega

private theorem s9msBvaCap_zero1 {avail mv nc f0 : Nat}
    (h : ¬ nc * 48 + 8192 < avail - f0) : s9msBvaCap avail mv nc f0 = 0 := by
  unfold s9msBvaCap; simp [h]

private theorem s9msBvaCap_zero2 {avail mv nc f0 : Nat}
    (h : ¬ 2 ≤ mv) : s9msBvaCap avail mv nc f0 = 0 := by
  unfold s9msBvaCap; simp [h]

theorem s9msCalcMaxV_ge {avail mv nc f0 : Nat} : mv ≤ s9msCalcMaxV avail mv nc f0 := by
  unfold s9msCalcMaxV; dsimp only
  by_cases h : avail < m7FixedBytes (mv + s9msBvaCap avail mv nc f0) +
      m7TransBytes (mv + s9msBvaCap avail mv nc f0) ∨
      avail - (m7FixedBytes (mv + s9msBvaCap avail mv nc f0) +
        m7TransBytes (mv + s9msBvaCap avail mv nc f0)) < nc * 40 + 136
  · simp [h]
  · simp only [h, ↓reduceIte]; omega

theorem s9msCalcMaxV_lt {avail mv nc f0 : Nat} (hmv : mv < dimacsBound) :
    s9msCalcMaxV avail mv nc f0 < 2 * dimacsBound := by
  have hb := s9msBvaCap_le avail mv nc f0
  unfold s9msCalcMaxV dimacsBound at *; dsimp only
  by_cases h : avail < m7FixedBytes (mv + s9msBvaCap avail mv nc f0) +
      m7TransBytes (mv + s9msBvaCap avail mv nc f0) ∨
      avail - (m7FixedBytes (mv + s9msBvaCap avail mv nc f0) +
        m7TransBytes (mv + s9msBvaCap avail mv nc f0)) < nc * 40 + 136
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

theorem s9msCalcMaxV_fits {avail mv nc f0 : Nat}
    (hbase : m7FixedBytes mv + m7TransBytes mv + nc * 40 + 136 ≤ avail) :
    m7FixedBytes (s9msCalcMaxV avail mv nc f0) +
      m7TransBytes (s9msCalcMaxV avail mv nc f0) + nc * 40 + 136 ≤ avail := by
  unfold s9msCalcMaxV; dsimp only
  by_cases h : avail < m7FixedBytes (mv + s9msBvaCap avail mv nc f0) +
      m7TransBytes (mv + s9msBvaCap avail mv nc f0) ∨
      avail - (m7FixedBytes (mv + s9msBvaCap avail mv nc f0) +
        m7TransBytes (mv + s9msBvaCap avail mv nc f0)) < nc * 40 + 136
  · simp only [h, ↓reduceIte]; exact hbase
  · simp only [h, ↓reduceIte]; omega

/-- Contract for V5 `full_calc_max_v` (`cand = 32768ULL`). -/
def s9msCalcMaxVSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (avail, mv, nc, f0, _) m Q _ =>
    mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧ f0.toNat ≤ avail.toNat ∧
    Q (BitVec.ofNat 64 (s9msCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m

theorem s9msCalcMaxVSpec_eq (avail mv nc f0 : BitVec 64) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    s9msCalcMaxVSpec (avail, mv, nc, f0, ()) m Q X =
      (mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧ f0.toNat ≤ avail.toNat ∧
       Q (BitVec.ofNat 64 (s9msCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) := by rfl

private def s9msCalcMaxVTailExpr (avail mv nc bva : Val i64) : Expr Val Cont [i64] :=
  Expr.let_
    { sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var mv, Arg.var bva, ()) } fun p_3 =>
  Expr.call (as := [i64]) (rs := [i64]) "full_fixed_bytes" (Arg.var p_3.fst, ())
    fun (p_4 : Tup Val [i64]) =>
  Expr.call (as := [i64]) (rs := [i64]) "full_trans_bytes_m7" (Arg.var p_3.fst, ())
    fun (p_5 : Tup Val [i64]) =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var p_4.fst, Arg.var p_5.fst, ()) } fun p_6 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.cmp .ult i64,
      args := (Arg.var avail, Arg.var p_6.fst, ()) } fun p_7 =>
  Expr.jnz (Arg.var p_7.fst)
    (Expr.ret (Arg.var mv, ()))
    (Expr.let_
       { sig := [i64, i64], code := OpCode.sub i64,
         args := (Arg.var avail, Arg.var p_6.fst, ()) } fun p_8 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.mul i64,
         args := (Arg.var nc, Arg.imm 40, ()) } fun p_9 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.add i64,
         args := (Arg.var p_9.fst, Arg.imm 136, ()) } fun p_10 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.cmp .ult i64,
         args := (Arg.var p_8.fst, Arg.var p_10.fst, ()) } fun p_11 =>
     Expr.jnz (Arg.var p_11.fst)
       (Expr.ret (Arg.var mv, ()))
       (Expr.ret (Arg.var p_3.fst, ())))

private def s9msCalcMaxVCapMinExpr (nc rem : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64,
      args := (Arg.var nc, Arg.imm 48, ()) } fun p =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.sub i64,
      args := (Arg.var rem, Arg.var p.fst, ()) } fun p =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.sub i64,
      args := (Arg.var p.fst, Arg.imm 4096, ()) } fun p =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.udiv 64,
      args := (Arg.var p.fst, Arg.imm 2688, ()) } fun (p : Tup Val [i64]) =>
  Expr.group (sig := [[i64]])
    (fun _ => Blocks.cons (fun (p : Tup Val [i64]) => Expr.jump J (Arg.var p.fst, ())) Blocks.nil)
    fun Js =>
    Expr.let_
      { sig := [i64, i64], code := OpCode.cmp .ult i64,
        args := (Arg.imm 32768, Arg.var p.fst, ()) } fun p_10 =>
    Expr.jnz (Arg.var p_10.fst)
      (Expr.jump Js.fst (Arg.imm 32768, ()))
      (Expr.jump Js.fst (Arg.var p.fst, ()))

private def s9msCalcMaxVBvaExpr (mv nc rem : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_
    { sig := [i64, i64], code := OpCode.cmp .uge i64,
      args := (Arg.var mv, Arg.imm 2, ()) } fun p_2 =>
  Expr.jnz (Arg.var p_2.fst)
    (Expr.let_
       { sig := [i64, i64], code := OpCode.mul i64,
         args := (Arg.var nc, Arg.imm 48, ()) } fun p_3 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.add i64,
         args := (Arg.var p_3.fst, Arg.imm 8192, ()) } fun p_4 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.cmp .ugt i64,
         args := (Arg.var rem, Arg.var p_4.fst, ()) } fun p_5 =>
     Expr.jnz (Arg.var p_5.fst)
       (s9msCalcMaxVCapMinExpr nc rem J)
       (Expr.jump J (Arg.imm 0, ())))
    (Expr.jump J (Arg.imm 0, ()))

private theorem s9msCalcMaxV_body_eq (avail mv nc f0 : Val i64) :
    full_calc_max_v_body Val Cont (avail, mv, nc, f0, ()) =
      Expr.let_
        { sig := [i64, i64], code := OpCode.sub i64,
          args := (Arg.var avail, Arg.var f0, ()) } fun p_1 =>
      Expr.group (sig := [[i64]])
        (fun _ => Blocks.cons (fun (p_2 : Tup Val [i64]) =>
          s9msCalcMaxVTailExpr avail mv nc p_2.fst) Blocks.nil)
        (fun Js => s9msCalcMaxVBvaExpr mv nc p_1.fst Js.fst) := rfl

private theorem s9msCalcMaxVTail_wp (Γ : Env)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hq : Q (BitVec.ofNat 64 (s9msCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (s9msCalcMaxVTailExpr avail mv nc
      (BitVec.ofNat 64 (s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat))) m := by
  rw [envSpec_eq] at hFixed hTrans
  unfold s9msCalcMaxVTailExpr
  c0_hsteps
  let cand := mv.toNat + s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat
  have hcand_lt : cand < 2 * dimacsBound := by
    have := s9msBvaCap_le avail.toNat mv.toNat nc.toNat f0.toNat
    unfold dimacsBound at *; omega
  have hcand_bv : mv + BitVec.ofNat 64 (s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) =
      BitVec.ofNat 64 cand := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, cand]
  have hfix_lt := m7FixedBytes_lt hcand_lt
  have htr_lt := m7TransBytes_lt hcand_lt
  refine ⟨fun r m1 => r = (BitVec.ofNat 64 (m7FixedBytes cand), ()) ∧ m1 = m, X, ?_, ?_,
    fun _ _ _ _ h => h⟩
  · apply hFixed
    rw [m7FixedBytesSpec_eq]; dsimp only [vals, Arg.val]
    rw [hcand_bv]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
    exact ⟨hcand_lt, rfl, trivial⟩
  rintro ⟨fixv, _⟩ m1 ⟨hfx, hm1⟩
  have hfx1 : fixv = BitVec.ofNat 64 (m7FixedBytes cand) := congrArg Prod.fst hfx
  subst hfx1; subst m1
  c0_hsteps
  refine ⟨fun r m2 => r = (BitVec.ofNat 64 (m7TransBytes cand), ()) ∧ m2 = m, X, ?_, ?_,
    fun _ _ _ _ h => h⟩
  · apply hTrans
    rw [m7TransBytesSpec_eq]; dsimp only [vals, Arg.val]
    rw [hcand_bv]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
    exact ⟨hcand_lt, rfl, trivial⟩
  rintro ⟨trv, _⟩ m2 ⟨htr, hm2⟩
  have htr1 : trv = BitVec.ofNat 64 (m7TransBytes cand) := congrArg Prod.fst htr
  subst htr1; subst m2
  run_tac for _ in [:64] do
    if !(← LeanQbe.T.C0HeadStep.headStepOnce { splitJnz := false, unrollGroup := false })
    then break
  let need := m7FixedBytes cand + m7TransBytes cand
  have hneed_bv : BitVec.ofNat 64 (m7FixedBytes cand) + BitVec.ofNat 64 (m7TransBytes cand) =
      BitVec.ofNat 64 need := by rw [← BitVec.ofNat_add]
  rw [hneed_bv]
  c0_hsplit
  · c0_hsteps
    have hlt : avail.toNat < need := by
      rw [Nat.mod_eq_of_lt (by omega : need < 2 ^ 64)] at hc; exact hc
    have hres : s9msCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat = mv.toNat := by
      unfold s9msCalcMaxV; simp [hlt, need, cand]
    simpa [hres] using hq
  · run_tac for _ in [:64] do
      if !(← LeanQbe.T.C0HeadStep.headStepOnce { splitJnz := false, unrollGroup := false })
      then break
    have hge : need ≤ avail.toNat := by
      rw [Nat.mod_eq_of_lt (by omega : need < 2 ^ 64)] at hc; omega
    have hneed_lt : need < 2 ^ 64 := lt_of_le_of_lt hge avail.isLt
    have hsub_bv2 : (2 ^ 64 - need % 2 ^ 64 + avail.toNat) % 2 ^ 64 =
        avail.toNat - need := by
      rw [Nat.mod_eq_of_lt hneed_lt]; omega
    c0_hsplit
    · c0_hsteps
      rw [show BitVec.toNat 40 = 40 from by decide,
        show BitVec.toNat 136 = 136 from by decide] at hc
      have hlt2 : avail.toNat - need < nc.toNat * 40 + 136 := by
        unfold dimacsBound at hnc
        rw [hsub_bv2, Nat.mod_eq_of_lt (by omega)] at hc
        exact hc
      have hres : s9msCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat = mv.toNat := by
        unfold s9msCalcMaxV; simp [hlt2, need, cand]
      simpa [hres] using hq
    · c0_hsteps
      rw [show BitVec.toNat 40 = 40 from by decide,
        show BitVec.toNat 136 = 136 from by decide] at hc
      have hge2 : ¬avail.toNat - need < nc.toNat * 40 + 136 := by
        unfold dimacsBound at hnc
        rw [hsub_bv2, Nat.mod_eq_of_lt (by omega)] at hc
        exact hc
      have hres : s9msCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat = cand := by
        unfold s9msCalcMaxV; simp [show ¬avail.toNat < need by omega, hge2, cand, need]
      simpa [hres, hcand_bv] using hq

private theorem s9msCalcMaxVCapMin_wp (Γ : Env) (Q : Post [i64]) (X : XPost)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (J : Cont [i64])
    (hmv2 : 2 ≤ mv.toNat) (hnc : nc.toNat < dimacsBound)
    (hrem_gt : nc.toNat * 48 + 8192 < avail.toNat - f0.toNat)
    (hrem_eq : (avail - f0).toNat = avail.toNat - f0.toNat)
    (hJ : J (BitVec.ofNat 64 (s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (s9msCalcMaxVCapMinExpr nc (avail - f0) J) m := by
  unfold s9msCalcMaxVCapMinExpr
  have hnc64 : nc.toNat * 48 + 8192 < 2 ^ 64 := by unfold dimacsBound at *; omega
  c0_hsteps_nogrp
  have hle1 : nc * 48 ≤ avail - f0 := by
    change (nc * 48).toNat ≤ (avail - f0).toNat
    rw [hrem_eq, BitVec.toNat_mul, show BitVec.toNat 48 = 48 by decide,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hsub1 : (avail - f0 - nc * 48).toNat = avail.toNat - f0.toNat - nc.toNat * 48 := by
    rw [BitVec.toNat_sub_of_le hle1, hrem_eq, BitVec.toNat_mul,
      show BitVec.toNat 48 = 48 by decide, Nat.mod_eq_of_lt (by omega)]
  have hle2 : (4096 : BitVec 64) ≤ avail - f0 - nc * 48 := by
    change (4096 : BitVec 64).toNat ≤ _
    rw [hsub1, show (4096 : BitVec 64).toNat = 4096 by decide]; omega
  have hsub2 : (avail - f0 - nc * 48 - 4096).toNat =
      avail.toNat - f0.toNat - nc.toNat * 48 - 4096 := by
    rw [BitVec.toNat_sub_of_le hle2, hsub1]; rfl
  have hdiv_lt : (avail.toNat - f0.toNat - nc.toNat * 48 - 4096) / 2688 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) avail.isLt)))
  have hmb : (avail - f0 - nc * 48 - 4096) / 2688 =
      BitVec.ofNat 64 (((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, hsub2, show BitVec.toNat 2688 = 2688 by decide, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hdiv_lt).symm
  have hfin : s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat =
      min 32768 (((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688) := by
    unfold s9msBvaCap; simp [hmv2, hrem_gt]
  have hdiv_eq : ((avail - f0 - nc * 48 - 4096) / 2688).toNat =
      ((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688 := by
    rw [hmb, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hdiv_lt
  refine wp_join_state1 (α := Unit)
    (proj := fun _ => BitVec.ofNat 64 (s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat))
    (Inv := fun _ m'' => m'' = m) ?_ ?_
  · rintro _ _ m'' hm''; subst m''
    c0_hsteps
    exact hJ
  · intro J3 hJ3; c0_hsplit
    · c0_hsteps
      rw [show BitVec.toNat 32768 = 32768 from by decide, hdiv_eq] at hc
      have hlt : 32768 < ((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688 := hc
      rw [show (32768 : BitVec 64) =
        BitVec.ofNat 64 (s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) from by
        rw [hfin, Nat.min_eq_left (Nat.le_of_lt hlt)]; rfl]
      exact hJ3 () m rfl
    · c0_hsteps
      rw [show BitVec.toNat 32768 = 32768 from by decide, hdiv_eq] at hc
      have hle : ((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688 ≤ 32768 :=
        Nat.le_of_not_lt hc
      have h_lhs : (avail - f0 - nc * 48 - 4096) / 2688 =
          BitVec.ofNat 64 (s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) := by
        rw [hmb, hfin, Nat.min_eq_right hle]
      rw [h_lhs]; exact hJ3 () m rfl

private theorem s9msCalcMaxVBva_wp (Γ : Env) (Q : Post [i64]) (X : XPost)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (J : Cont [i64])
    (_hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound) (hf0 : f0.toNat ≤ avail.toNat)
    (hJ : J (BitVec.ofNat 64 (s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (s9msCalcMaxVBvaExpr mv nc (avail - f0) J) m := by
  unfold s9msCalcMaxVBvaExpr
  have hnc64 : nc.toNat * 48 + 8192 < 2 ^ 64 := by unfold dimacsBound at *; omega
  have hrem_eq : (avail - f0).toNat = avail.toNat - f0.toNat := by
    simp [BitVec.toNat_sub]; omega
  have hbound_nat : (nc * 48 + 8192 : BitVec 64).toNat = nc.toNat * 48 + 8192 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul,
      show (48 : BitVec 64).toNat = 48 from by decide,
      show (8192 : BitVec 64).toNat = 8192 from by decide,
      Nat.mod_eq_of_lt (by omega : nc.toNat * 48 < 2 ^ 64), Nat.mod_eq_of_lt hnc64]
  c0_hsplit
  · rw [show (2 : BitVec 64).toNat = 2 from by decide] at hc
    have hmv2 : 2 ≤ mv.toNat := hc
    run_tac for _ in [:16] do
      if !(← LeanQbe.T.C0HeadStep.headStepOnce { splitJnz := false, unrollGroup := false })
      then break
    rw [wp_jnz]
    constructor
    · intro h
      have hlt : (nc * 48 + 8192).ult (avail - f0) = true := h
      rw [BitVec.ult, hbound_nat, hrem_eq] at hlt
      exact s9msCalcMaxVCapMin_wp Γ Q X avail mv nc f0 m J hmv2 hnc
        (of_decide_eq_true hlt) hrem_eq hJ
    · intro h
      have hge : (nc * 48 + 8192).ult (avail - f0) = false := h
      rw [BitVec.ult, hbound_nat, hrem_eq] at hge
      have hle : ¬ nc.toNat * 48 + 8192 < avail.toNat - f0.toNat := by
        simpa using of_decide_eq_false hge
      c0_hsteps
      rw [s9msBvaCap_zero1 hle] at hJ
      exact hJ
  · c0_hsteps
    rw [show (2 : BitVec 64).toNat = 2 from by decide] at hc
    rw [s9msBvaCap_zero2 hc] at hJ
    exact hJ

theorem full_calc_max_v_wp (Γ : Env)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec) :
    ∀ a m Q X, s9msCalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_body a m Q X := by
  rintro ⟨avail, mv, nc, f0, _⟩ m Q X ⟨hmv, hnc, hf0, hq⟩
  dsimp only [Func.wp]
  rw [s9msCalcMaxV_body_eq]
  c0_hsteps_nogrp
  refine wp_join_state1 (α := Unit)
    (proj := fun _ => BitVec.ofNat 64 (s9msBvaCap avail.toNat mv.toNat nc.toNat f0.toNat))
    (Inv := fun _ m' => m' = m) ?_ ?_
  · rintro _ _ m' hm'; subst m'
    exact s9msCalcMaxVTail_wp Γ hFixed hTrans avail mv nc f0 m Q X hmv hnc hq
  · intro J hJ
    exact s9msCalcMaxVBva_wp Γ Q X avail mv nc f0 m J hmv hnc hf0 (hJ () m rfl)

end CalcMaxVV5

/-! ## 2. Step-9 `scr_cap = 8388608` Sizing (`s9msCalcScrCapSpec`) -/

section CalcScrCapS9Ms

/-- Exact `scratch_buf` capacity policy for `S9-P0.3` (`max 8388608ULL`). -/
def s9msCalcScrCap (rem : Nat) : Nat :=
  if rem < 8192 then 0
  else
    let raw := if 16384 ≤ rem then rem / 16 else rem / 32
    ((min raw 8388608) / 2) * 2

theorem s9msCalcScrCap_eq (rem : Nat) :
    s9msCalcScrCap rem =
      if rem < 8192 then 0
      else ((min (if 16384 ≤ rem then rem / 16 else rem / 32) 8388608) / 2) * 2 := by
  unfold s9msCalcScrCap; rfl

theorem s9msCalcScrCap_le (rem : Nat) : s9msCalcScrCap rem ≤ 8388608 := by
  unfold s9msCalcScrCap; split; omega; dsimp only; split <;> omega

theorem s9msCalcScrCap_lt (rem : Nat) : s9msCalcScrCap rem < dimacsBound := by
  have := s9msCalcScrCap_le rem; unfold dimacsBound; omega

theorem s9msCalcScrCap_4le (rem : Nat) : 4 * s9msCalcScrCap rem ≤ rem / 4 := by
  unfold s9msCalcScrCap; split; omega; dsimp only; split <;> omega

/-- Contract for `S9-P0.3` `full_calc_scr_cap_m5` (`scr_cap ≤ 8388608`). -/
def s9msCalcScrCapSpec : Spec [i64] [i64] := fun (rem, _) m Q _ =>
  Q (BitVec.ofNat 64 (s9msCalcScrCap rem.toNat), ()) m

theorem s9msCalcScrCapSpec_eq (rem : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    s9msCalcScrCapSpec (rem, ()) m Q X = Q (BitVec.ofNat 64 (s9msCalcScrCap rem.toNat), ()) m := by
  unfold s9msCalcScrCapSpec; rfl

theorem full_calc_scr_cap_m5_s9ms_wp (Γ : Env) :
    ∀ a m Q X, s9msCalcScrCapSpec a m Q X → Func.wp Γ full_calc_scr_cap_m5_body a m Q X := by
  rintro ⟨rem, _⟩ m Q X hq
  dsimp only [s9msCalcScrCapSpec] at hq
  unfold full_calc_scr_cap_m5_body; dsimp only [Func.wp]
  c0_hsteps_nogrp; c0_hsplit
  · c0_hsteps
    rw [show BitVec.toNat 8192 = 8192 from by decide] at hc
    have hz : s9msCalcScrCap rem.toNat = 0 := by unfold s9msCalcScrCap; simp [hc]
    simpa [hz] using hq
  · c0_hsteps_nogrp
    rw [show BitVec.toNat 8192 = 8192 from by decide] at hc
    have hge : 8192 ≤ rem.toNat := by omega
    let raw := if 16384 ≤ rem.toNat then rem.toNat / 16 else rem.toNat / 32
    have hraw_lt : raw < 2 ^ 64 := by dsimp [raw]; split <;> omega
    refine wp_join_state1 (α := Unit) (proj := fun _ => BitVec.ofNat 64 raw)
      (Inv := fun _ m' => m' = m) ?_ ?_
    · rintro J _ m' hm'; subst m'
      c0_hsteps_nogrp
      refine wp_join_state1 (α := Unit) (proj := fun _ => BitVec.ofNat 64 (min raw 8388608))
        (Inv := fun _ m'' => m'' = m) ?_ ?_
      · rintro J2 _ m'' hm''; subst m''
        c0_hsteps
        have hcap : BitVec.ofNat 64 (min raw 8388608) &&& ~~~1 =
            BitVec.ofNat 64 (s9msCalcScrCap rem.toNat) := by
          rw [fp_and_not1,
            show (BitVec.ofNat 64 (min raw 8388608)).toNat = min raw 8388608 by simp [raw]; omega]
          unfold s9msCalcScrCap; simp [show ¬rem.toNat < 8192 by omega, raw]
        rw [hcap]; exact hq
      · intro J2 hJ2; c0_hsplit
        · c0_hsteps
          rw [show BitVec.toNat 8388608 = 8388608 from by decide,
            Nat.mod_eq_of_lt hraw_lt] at hc
          rw [show (8388608 : BitVec 64) = BitVec.ofNat 64 (min raw 8388608) from by
            simp [Nat.min_eq_right (by omega : 8388608 ≤ raw)]]
          exact hJ2 () m rfl
        · c0_hsteps
          rw [show BitVec.toNat 8388608 = 8388608 from by decide,
            Nat.mod_eq_of_lt hraw_lt] at hc
          rw [show BitVec.ofNat 64 raw = BitVec.ofNat 64 (min raw 8388608) from by
            rw [Nat.min_eq_left (by omega : raw ≤ 8388608)]]
          exact hJ2 () m rfl
    · intro J hJ; c0_hsplit
      · c0_hsteps
        rw [show BitVec.toNat 16384 = 16384 from by decide] at hc
        have hsh : rem >>> 4 = BitVec.ofNat 64 raw := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
            show (2 ^ 4 : Nat) = 16 by decide, BitVec.toNat_ofNat]
          dsimp only [raw]; simp only [hc, ite_true]
          exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) rem.isLt)).symm
        rw [hsh]; exact hJ () m rfl
      · c0_hsteps
        rw [show BitVec.toNat 16384 = 16384 from by decide] at hc
        have hsh : rem >>> 5 = BitVec.ofNat 64 raw := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
            show (2 ^ 5 : Nat) = 32 by decide, BitVec.toNat_ofNat]
          dsimp only [raw]; simp only [hc, ite_false]
          exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) rem.isLt)).symm
        rw [hsh]; exact hJ () m rfl

end CalcScrCapS9Ms

/-! ## 3. Reuses of Unchanged Functions & `full_init_state_m5_s9ms_wp` -/

section InitWiring

theorem full_fill_u64_s9ms_wp (Γ : Env) :
    ∀ a m Q X, m7FillU64Spec a m Q X → Func.wp Γ fidStep9FillU64Fn.body a m Q X :=
  FullM7MemShrinkV5.full_fill_u64_m7ms_wp Γ

theorem full_zero_tables1_s9ms_wp (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec) :
    ∀ a m Q X, m7ZeroTables1Spec a m Q X → Func.wp Γ fidStep9MsZeroTables1Fn.body a m Q X :=
  FullM7MemShrinkV5.full_zero_tables1_m7ms_wp Γ hFill

theorem full_zero_tables2_s9ms_wp (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec) :
    ∀ a m Q X, m7ZeroTables2Spec a m Q X → Func.wp Γ fidStep9MsZeroTables2Fn.body a m Q X :=
  FullM7MemShrinkV5.full_zero_tables2_m7ms_wp Γ hFill

theorem full_fixed_bytes_s9ms_wp (Γ : Env) :
    ∀ a m Q X, m7FixedBytesSpec a m Q X → Func.wp Γ fidStep9MsFixedBytesFn.body a m Q X :=
  FullM7MemShrinkV5.full_fixed_bytes_m7ms_wp Γ

theorem full_trans_bytes_s9ms_wp (Γ : Env) :
    ∀ a m Q X, m7TransBytesSpec a m Q X → Func.wp Γ fidStep9MsTransBytesFn.body a m Q X :=
  FullM7MemShrinkV5.full_trans_bytes_m7ms_wp Γ

theorem full_init_ptrs_s9ms_wp (Γ : Env) :
    ∀ a m Q X, m7InitPtrsSpec a m Q X → Func.wp Γ fidStep9MsInitPtrsFn.body a m Q X :=
  FullM7MemShrinkV5.full_init_ptrs_m7ms_wp Γ

theorem full_init_hdr_s9ms_wp (Γ : Env) :
    ∀ a m Q X, m7InitHdrSpec a m Q X → Func.wp Γ fidStep9MsInitHdrFn.body a m Q X :=
  FullM7MemShrinkV5.full_init_hdr_m7ms_wp Γ

theorem full_calc_ext_cap_s9ms_wp (Γ : Env) :
    ∀ a m Q X, m7CalcExtCapSpec a m Q X → Func.wp Γ fidStep9MsCalcExtCapM5Fn.body a m Q X :=
  FullM7MemShrinkV5.full_calc_ext_cap_m7ms_wp Γ

theorem full_init_arenas_s9ms_wp (Γ : Env)
    (hPtrs : EnvSpec Γ "full_init_ptrs" m7InitPtrsSpec) :
    ∀ a m Q X, m7InitArenasSpec a m Q X → Func.wp Γ fidStep9MsInitArenasFn.body a m Q X :=
  FullM7MemShrinkV5.full_init_arenas_m7ms_wp Γ hPtrs

theorem full_compact_vars_s9ms_wp (Γ : Env) :
    ∀ a m Q X, FullM7MemShrinkV5.m7msCompactVarsSpec a m Q X →
      Func.wp Γ fidStep9MsCompactVarsFn.body a m Q X :=
  FullM7MemShrinkV5.full_compact_vars_m7ms_wp Γ
private def msInitExtCap (nc rem : Nat) : Nat :=
  let dyn := fullInitDelCap rem * 12 + 4 * m7CalcExtCap rem + 4 * s9msCalcScrCap rem
  if rem < dyn + nc * 40 + 136 then 0 else m7CalcExtCap rem

private def msInitScrCap (nc rem : Nat) : Nat :=
  let dyn := fullInitDelCap rem * 12 + 4 * m7CalcExtCap rem + 4 * s9msCalcScrCap rem
  if rem < dyn + nc * 40 + 136 then 0 else s9msCalcScrCap rem

private def msInitDyn (nc rem : Nat) : Nat :=
  fullInitDelCap rem * 12 + 4 * msInitExtCap nc rem + 4 * msInitScrCap nc rem

private theorem msInitDyn_le {nc rem : Nat} (hrem : nc * 40 + 136 ≤ rem) :
    msInitDyn nc rem + 40 ≤ rem := by
  unfold msInitDyn msInitExtCap msInitScrCap fullInitDelCap; dsimp only
  split <;> split <;> omega

private theorem msInitArenas_le {nc avail_dyn : Nat} (hrem : nc * 40 + 136 ≤ avail_dyn) :
    let rem := avail_dyn - msInitDyn nc avail_dyn
    8 * fullInitAp rem + 8 * fullInitWp rem + 8 * fullInitRp rem + msInitDyn nc avail_dyn ≤
      avail_dyn := by
  have hd := msInitDyn_le hrem
  have h1 := fullInitAp_add_rp_le (avail_dyn - msInitDyn nc avail_dyn)
  have h2 : fullInitWp (avail_dyn - msInitDyn nc avail_dyn) ≤
      (avail_dyn - msInitDyn nc avail_dyn) / 8 -
      fullInitAp (avail_dyn - msInitDyn nc avail_dyn) -
      fullInitRp (avail_dyn - msInitDyn nc avail_dyn) := Nat.min_le_left _ _
  omega

private theorem msInitWp_ge_one {rem : Nat} (hrem : 40 ≤ rem) : 1 ≤ fullInitWp rem := by
  unfold fullInitWp fullInitRp fullInitAp; omega

private theorem ms_hdr_region_rejoin {cnf_ptr hdr_addr mv' nc' cur' val' : BitVec 64}
    {avail : Nat} {cnfBytes : List UInt8} {w140 : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hav : 1152 ≤ avail) (hle : avail ≤ 2 ^ 64) (hw : w140.length = 140)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv' nc' cur' val' ⋆
      array64 (hdr_addr + 32) w140 ⋆
      region (hdr_addr + 1152) (avail - 1152) ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m := by
  have h1 : (dimacsState hdr_addr mv' nc' cur' val' ⋆
      (array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail - 1152) ⋆
        bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  have h2 : (region hdr_addr 32 ⋆
      (array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail - 1152) ⋆
        bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_mono (P' := region hdr_addr 32) (fun _ hd => dimacsState_to_region hd) h1
  have h3 : (array64 (hdr_addr + 32) w140 ⋆
      (region hdr_addr 32 ⋆ region (hdr_addr + 1152) (avail - 1152) ⋆
        bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac h2
  rw [array64_eq_word8Array] at h3
  have h4 : (region (hdr_addr + 32) 1120 ⋆
      (region hdr_addr 32 ⋆ region (hdr_addr + 1152) (avail - 1152) ⋆
        bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_mono (P' := region (hdr_addr + 32) 1120)
      (fun _ hw8 => by simpa [hw] using word8Array_to_region (by omega) hw8) h3
  have h5 : ((region (hdr_addr + 32) 1120 ⋆ region (hdr_addr + 1152) (avail - 1152)) ⋆
      (region hdr_addr 32 ⋆ bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac h4
  have h6 : (region (hdr_addr + 32) (avail - 32) ⋆
      (region hdr_addr 32 ⋆ bytes cnf_ptr cnfBytes ⋆ R)) m := by
    refine sep_mono (fun _ hr => ?_) h5
    rw [show avail - 32 = 1120 + (avail - 1152) by omega, region_split (by omega),
      show (hdr_addr + 32) + BitVec.ofNat 64 1120 = hdr_addr + 1152 by
        rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
          show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl, ptr_add_ofNat]]
    exact hr
  have h7 : ((region hdr_addr 32 ⋆ region (hdr_addr + 32) (avail - 32)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac h6
  have h8 : (region hdr_addr avail ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := by
    refine sep_mono (fun _ hr => ?_) h7
    rw [show avail = 32 + (avail - 32) by omega, region_split (by omega),
      show hdr_addr + BitVec.ofNat 64 32 = hdr_addr + 32 from rfl]
    exact hr
  exact sep_ac h8

private theorem ms_peel_res_i8 (a : BitVec 64) (n pad rest : Nat) (hn : n ≤ pad)
    (hfit : pad + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a (pad + rest) ⋆ R) m) :
    ∃ xs : List (BitVec 8), xs.length = n ∧
      (region (a + BitVec.ofNat 64 pad) rest ⋆
        ((array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 n) (pad - n)) ⋆ R)) m := by
  rw [region_split hfit] at hm
  have h1 : (region a pad ⋆ (region (a + BitVec.ofNat 64 pad) rest ⋆ R)) m := sep_ac hm
  have h2 : (((fun m1 => ∃ xs : List (BitVec 8), xs.length = n ∧ array (t := i8) a xs m1) ⋆
      region (a + BitVec.ofNat 64 n) (pad - n)) ⋆
      (region (a + BitVec.ofNat 64 pad) rest ⋆ R)) m := sep_mono (fun _ hr => by
    rw [show pad = n + (pad - n) by omega, region_split (by omega)] at hr
    exact sep_mono (fun _ h => region_to_array_i8 n (by omega) h) hr) h1
  have h3 : ((fun m1 => ∃ xs : List (BitVec 8), xs.length = n ∧ array (t := i8) a xs m1) ⋆
      (region (a + BitVec.ofNat 64 n) (pad - n) ⋆
        (region (a + BitVec.ofNat 64 pad) rest ⋆ R))) m := by
    rw [sep_assoc] at h2; exact h2
  obtain ⟨xs, h4⟩ := sep_ex_l.mp h3
  obtain ⟨hxs, h5⟩ := sep_pure_l.mp h4
  exact ⟨xs, hxs, sep_ac h5⟩

private theorem ms_peel_res_u32 (a : BitVec 64) (n pad rest : Nat) (hn : 4 * n ≤ pad)
    (hfit : pad + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a (pad + rest) ⋆ R) m) :
    ∃ xs : List (BitVec 32), xs.length = n ∧
      (region (a + BitVec.ofNat 64 pad) rest ⋆
        ((array (t := i32) a xs ⋆ region (a + BitVec.ofNat 64 (4 * n)) (pad - 4 * n)) ⋆ R)) m := by
  rw [region_split hfit] at hm
  have h1 : (region a pad ⋆ (region (a + BitVec.ofNat 64 pad) rest ⋆ R)) m := sep_ac hm
  have h2 : (((fun m1 => ∃ xs : List (BitVec 32), xs.length = n ∧ array (t := i32) a xs m1) ⋆
      region (a + BitVec.ofNat 64 (4 * n)) (pad - 4 * n)) ⋆
      (region (a + BitVec.ofNat 64 pad) rest ⋆ R)) m := sep_mono (fun _ hr => by
    rw [show pad = 4 * n + (pad - 4 * n) by omega, region_split (by omega)] at hr
    exact sep_mono (fun _ h => region_to_array_i32 n (by omega) h) hr) h1
  have h3 : ((fun m1 => ∃ xs : List (BitVec 32), xs.length = n ∧ array (t := i32) a xs m1) ⋆
      (region (a + BitVec.ofNat 64 (4 * n)) (pad - 4 * n) ⋆
        (region (a + BitVec.ofNat 64 pad) rest ⋆ R))) m := by
    rw [sep_assoc] at h2; exact h2
  obtain ⟨xs, h4⟩ := sep_ex_l.mp h3
  obtain ⟨hxs, h5⟩ := sep_pure_l.mp h4
  exact ⟨xs, hxs, sep_ac h5⟩

private theorem ms_peel_arr32 (a : BitVec 64) (n rest : Nat)
    (hfit : 4 * n + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a (4 * n + rest) ⋆ R) m) :
    ∃ xs : List (BitVec 32), xs.length = n ∧
      (region (a + BitVec.ofNat 64 (4 * n)) rest ⋆ (array (t := i32) a xs ⋆ R)) m := by
  rw [region_split hfit] at hm
  have h1 : (region a (4 * n) ⋆ (region (a + BitVec.ofNat 64 (4 * n)) rest ⋆ R)) m := sep_ac hm
  have h2 := sep_mono (fun _ h => region_to_array_i32 n (by omega) h) h1
  obtain ⟨xs, h3⟩ := sep_ex_l.mp h2
  obtain ⟨hxs, h4⟩ := sep_pure_l.mp h3
  exact ⟨xs, hxs, sep_ac h4⟩

private theorem ms_peel_arr64 (a : BitVec 64) (n rest : Nat)
    (hfit : 8 * n + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a (8 * n + rest) ⋆ R) m) :
    ∃ xs : List (BitVec 64), xs.length = n ∧
      (region (a + BitVec.ofNat 64 (8 * n)) rest ⋆ (array64 a xs ⋆ R)) m := by
  rw [region_split hfit] at hm
  have h1 : (region a (8 * n) ⋆ (region (a + BitVec.ofNat 64 (8 * n)) rest ⋆ R)) m := sep_ac hm
  have h2 := sep_mono (fun _ h => region_to_array64 n (by omega) h) h1
  obtain ⟨xs, h3⟩ := sep_ex_l.mp h2
  obtain ⟨hxs, h4⟩ := sep_pure_l.mp h3
  exact ⟨xs, hxs, sep_ac h4⟩

private theorem ms_peel_reg (a : BitVec 64) (n rest : Nat) (hfit : n + rest ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (region a (n + rest) ⋆ R) m) :
    (region (a + BitVec.ofNat 64 n) rest ⋆ (region a n ⋆ R)) m := by
  rw [region_split hfit] at hm
  exact Eq.mp (congrFun (by ac_rfl) m) hm

private structure MsInitArrs (c : MemShrinkCfg) where
  (vals mrk lit_mark phases phases_target phases_best : List (BitVec 8))
  (flags lvl rsns trl trail_pos tmp min_clr : List (BitVec 32))
  (heap pos shrink_stk q_prev q_next q_stamp frame_trail frame_dec : List (BitVec 32))
  (wvec min_stk glue_used last_learned arena wstk delayed red_refs extend_stk scratch_buf :
    List (BitVec 32))
  (score : List (BitVec 64))
  (hvals : vals.length = 2 * c.max_vars) (hmrk : mrk.length = c.max_vars)
  (hlm : lit_mark.length = 2 * c.max_vars) (hph : phases.length = c.max_vars)
  (hpht : phases_target.length = c.max_vars) (hphb : phases_best.length = c.max_vars)
  (hfl : flags.length = c.max_vars) (hlv : lvl.length = c.max_vars)
  (hrs : rsns.length = c.max_vars) (htr : trl.length = c.max_vars)
  (htp : trail_pos.length = c.max_vars) (htm : tmp.length = c.max_vars)
  (hmc : min_clr.length = c.max_vars) (hhp : heap.length = c.max_vars)
  (hps : pos.length = c.max_vars) (hss : shrink_stk.length = c.max_vars)
  (hqp : q_prev.length = c.max_vars) (hqn : q_next.length = c.max_vars)
  (hqs : q_stamp.length = c.max_vars) (hft : frame_trail.length = c.max_vars + 1)
  (hfd : frame_dec.length = c.max_vars + 1) (hwv : wvec.length = 4 * c.max_vars)
  (hmst : min_stk.length = 2 * c.minDepth) (hgu : glue_used.length = 64)
  (hll : last_learned.length = 16) (har : arena.length = c.arena_cap)
  (hwk : wstk.length = c.wcap) (hdl : delayed.length = 3 * c.delayed_cap)
  (hrr : red_refs.length = c.red_cap) (hex : extend_stk.length = c.extend_cap)
  (hsc_b : scratch_buf.length = c.scratch_cap) (hscr : score.length = c.max_vars)

private def msInitState (c : MemShrinkCfg) (d_cur d_val fuel : BitVec 64) (a : MsInitArrs c) :
    FullState :=
  { core :=
      { d_cur := d_cur, d_val := d_val, cur_vars := c.mv, unassigned := BitVec.ofNat 64 c.mv
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0xFFFFFFFF#64, num_irred := 0#64, num_redundant := 0#64
        num_binary := 0#64, unflushed := 0#64, probing := 0#64, trail_end := 0
        propagated := 0, cur_level := 0, fuel := fuel, confl_ref := 0xFFFFFFFF#64
        confl_type := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
        min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
        inconsistent := 0#64, vals := a.vals, lit_mark := a.lit_mark, mrk := a.mrk
        flags := a.flags, lvl := a.lvl, rsns := a.rsns, trl := a.trl, trail_pos := a.trail_pos
        tmp := a.tmp, min_clr := a.min_clr, frame_trail := a.frame_trail
        frame_dec := a.frame_dec, wvec := a.wvec, repr := [], min_stk := a.min_stk
        arena := a.arena, wstk := a.wstk }
    scratch :=
      { heap_len := c.mv, scinc := 1#64 <<< 28, rel_period := 1024#64, rel_limit := 1048576#64
        rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64, rel_trigger := 0#64
        conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64, delayed_len := 0
        stable := 0#64, switched := 0#64, mode_count := 0#64, mode_confl_lim := 1000#64
        mode_tick_lim := 0#64, mode_saved_ticks := 0#64, search_ticks := 0#64
        q_first := if c.mv == 0 then 0xFFFFFFFF#64 else 0#64
        q_last := if c.mv == 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_idx := if c.mv == 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_stamp := BitVec.ofNat 64 c.mv, q_cur_stamp := BitVec.ofNat 64 c.mv
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64
        ema_fast_exp := 1#64 <<< 24, ema_slow_biased := 0#64, ema_slow_exp := 1#64 <<< 24
        extend_len := 0
        rng_state := 0x9E3779B97F4A7C15#64 ^^^ BitVec.ofNat 64 (c.mv + 1)
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 2000#64
        probings := 0#64, elim_limit := 5000#64, eliminations := 0#64, elim_bound := 0#64
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64
        subst_cnt := 0#64, cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64
        bce_cnt := 0#64, bva_cnt := 0#64, walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64
        fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := 0#64, walk_vals := []
        phases := a.phases, phases_target := a.phases_target, phases_best := a.phases_best
        walk_best := [], heap := a.heap, pos := a.pos, shrink_stk := a.shrink_stk
        q_prev := a.q_prev, q_next := a.q_next, q_stamp := a.q_stamp, wsort := []
        work_stk1 := [], work_stk2 := [], tarjan_mark := [], tarjan_reach := []
        score := a.score, sim_sig := [], glue_used := a.glue_used
        last_learned := a.last_learned, delayed := a.delayed, red_refs := a.red_refs
        extend_stk := a.extend_stk, scratch_buf := a.scratch_buf } }

private theorem ms_init_lengthsOk (c : MemShrinkCfg) (hw1 : 1 ≤ c.wcap)
    (d_cur d_val fuel : BitVec 64) (a : MsInitArrs c) :
    MemShrinkLengthsOk c (msInitState c d_cur d_val fuel a) :=
  { vals_len := a.hvals, lit_mark_len := a.hlm, mrk_len := a.hmrk, flags_len := a.hfl
    lvl_len := a.hlv, rsns_len := a.hrs, trl_len := a.htr, trail_pos_len := a.htp
    tmp_len_arr := a.htm, min_clr_len_arr := a.hmc, frame_trail_len := a.hft
    frame_dec_len := a.hfd, wvec_len := a.hwv, min_stk_len := a.hmst, arena_len_arr := a.har
    wstk_len_arr := a.hwk, phases_len := a.hph, phases_target_len := a.hpht
    phases_best_len := a.hphb, heap_len_arr := a.hhp, pos_len := a.hps, shrink_stk_len := a.hss
    q_prev_len := a.hqp, q_next_len := a.hqn, q_stamp_len := a.hqs, score_len := a.hscr
    glue_used_len := a.hgu, last_learned_len := a.hll, delayed_len_arr := a.hdl
    red_refs_len := a.hrr, extend_stk_len := a.hex, scratch_buf_len := a.hsc_b
    cur_vars_ge := by have := c.hbva; dsimp [msInitState]; omega
    cur_vars_le := by have := c.hbva; dsimp [msInitState]; omega
    arena_len_le := by dsimp [msInitState]; omega
    wlen_le := by dsimp [msInitState]; exact hw1
    trail_end_le := by dsimp [msInitState]; omega
    propagated_le := by dsimp [msInitState]; omega
    tmp_len_le := by dsimp [msInitState]; omega
    min_clr_len_le := by dsimp [msInitState]; omega
    heap_len_le := by have := c.hbva; dsimp [msInitState]; omega
    delayed_len_le := by dsimp [msInitState]; omega
    extend_len_le := by dsimp [msInitState]; omega }

private theorem ms_pack5 {A1 A2 A3 A4 A5 Q R : Mem 64 → Prop} {m : Mem 64}
    (hQ : Q = (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5))
    (hm : (A5 ⋆ (A4 ⋆ (A3 ⋆ (A2 ⋆ (A1 ⋆ R))))) m) : (Q ⋆ R) m := by
  rw [hQ]; exact sep_ac hm

private theorem ms_pack6 {A1 A2 A3 A4 A5 A6 Q R : Mem 64 → Prop} {m : Mem 64}
    (hQ : Q = (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6))
    (hm : (A6 ⋆ (A5 ⋆ (A4 ⋆ (A3 ⋆ (A2 ⋆ (A1 ⋆ R)))))) m) : (Q ⋆ R) m := by
  rw [hQ]; exact sep_ac hm

private theorem ms_pack7 {A1 A2 A3 A4 A5 A6 A7 Q R : Mem 64 → Prop} {m : Mem 64}
    (hQ : Q = (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6 ⋆ A7))
    (hm : (A7 ⋆ (A6 ⋆ (A5 ⋆ (A4 ⋆ (A3 ⋆ (A2 ⋆ (A1 ⋆ R))))))) m) : (Q ⋆ R) m := by
  rw [hQ]; exact sep_ac hm

private theorem ms_pack8 {A1 A2 A3 A4 A5 A6 A7 A8 Q R : Mem 64 → Prop} {m : Mem 64}
    (hQ : Q = (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8))
    (hm : (A8 ⋆ (A7 ⋆ (A6 ⋆ (A5 ⋆ (A4 ⋆ (A3 ⋆ (A2 ⋆ (A1 ⋆ R)))))))) m) : (Q ⋆ R) m := by
  rw [hQ]; exact sep_ac hm

private def msSegBytes (c : MemShrinkCfg) (v mk ph pht phb : List (BitVec 8)) : Mem 64 → Prop :=
  (array (t := i8) c.pVals v ⋆
    region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars)) (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
  (array (t := i8) c.pMark mk ⋆
    region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (array (t := i8) c.pPhases ph ⋆
    region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (array (t := i8) c.pPhasesTarget pht ⋆
    region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (array (t := i8) c.pPhasesBest phb ⋆
    region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars))

private def msSegU32A (c : MemShrinkCfg)
    (fl lv rs tr tp tm hp ps : List (BitVec 32)) : Mem 64 → Prop :=
  (array (t := i32) c.pFlags fl ⋆
    region (c.pFlags + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pLevel lv ⋆
    region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pReason rs ⋆
    region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrail tr ⋆
    region (c.pTrail + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrailPos tp ⋆
    region (c.pTrailPos + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTmp tm ⋆
    region (c.pTmp + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pHeap hp ⋆
    region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pPos ps ⋆
    region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars))

private def msSegU32B (c : MemShrinkCfg)
    (mc ss qp qn qs ft fd : List (BitVec 32)) : Mem 64 → Prop :=
  (array (t := i32) c.pMinClr mc ⋆
    region (c.pMinClr + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pShrinkStk ss ⋆
    region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQPrev qp ⋆
    region (c.pQPrev + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQNext qn ⋆
    region (c.pQNext + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQStamp qs ⋆
    region (c.pQStamp + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pFrameTrail ft ⋆
    region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
      (u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
  (array (t := i32) c.pFrameDec fd ⋆
    region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
      (u32FullBytes c.max_vars - 4 * (c.max_vars + 1)))

private def msSegTailA (c : MemShrinkCfg) (wv ms gu ll : List (BitVec 32))
    (sc : List (BitVec 64)) : Mem 64 → Prop :=
  array (t := i32) c.pWvec wv ⋆ array64 c.pScore sc ⋆ array (t := i32) c.pMinStk ms ⋆
  array (t := i32) c.pGlueUsed gu ⋆ array (t := i32) c.pLastLearned ll

private def msSegTailB (c : MemShrinkCfg) (ar wk dl rr ex sb : List (BitVec 32)) : Mem 64 → Prop :=
  array (t := i32) c.pArena ar ⋆ array (t := i32) c.pWstk wk ⋆ array (t := i32) c.pDelayed dl ⋆
  array (t := i32) c.pRedRefs rr ⋆ array (t := i32) c.pExtendStk ex ⋆
  array (t := i32) c.pScratchBuf sb

private theorem ms_peel_segBytes (c : MemShrinkCfg) (rest : Nat)
    (hfit : valsBytes c.max_vars + 4 * markBytes c.max_vars + rest ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pVals (valsBytes c.max_vars + 4 * markBytes c.max_vars + rest) ⋆ R) m) :
    ∃ vals mrk ph pht phb : List (BitVec 8),
      vals.length = 2 * c.max_vars ∧ mrk.length = c.max_vars ∧ ph.length = c.max_vars ∧
      pht.length = c.max_vars ∧ phb.length = c.max_vars ∧
      (msSegBytes c vals mrk ph pht phb ⋆ region c.pFlags rest ⋆ R) m := by
  have hvb : 2 * c.max_vars ≤ valsBytes c.max_vars := by unfold valsBytes; omega
  have hmb : c.max_vars ≤ markBytes c.max_vars := by unfold markBytes; omega
  rw [show valsBytes c.max_vars + 4 * markBytes c.max_vars + rest =
      valsBytes c.max_vars + (4 * markBytes c.max_vars + rest) by omega] at hm
  obtain ⟨vals, hv, hm⟩ := ms_peel_res_i8 c.pVals (2 * c.max_vars) (valsBytes c.max_vars)
    (4 * markBytes c.max_vars + rest) hvb (by omega) hm
  rw [← MemShrinkCfg.pMark_eq, show 4 * markBytes c.max_vars + rest =
      markBytes c.max_vars + (3 * markBytes c.max_vars + rest) by omega] at hm
  obtain ⟨mrk, hmk, hm⟩ := ms_peel_res_i8 c.pMark c.max_vars (markBytes c.max_vars)
    (3 * markBytes c.max_vars + rest) hmb (by omega) hm
  rw [← MemShrinkCfg.pPhases_eq, show 3 * markBytes c.max_vars + rest =
      markBytes c.max_vars + (2 * markBytes c.max_vars + rest) by omega] at hm
  obtain ⟨ph, hph, hm⟩ := ms_peel_res_i8 c.pPhases c.max_vars (markBytes c.max_vars)
    (2 * markBytes c.max_vars + rest) hmb (by omega) hm
  rw [← MemShrinkCfg.pPhasesTarget_eq, show 2 * markBytes c.max_vars + rest =
      markBytes c.max_vars + (markBytes c.max_vars + rest) by omega] at hm
  obtain ⟨pht, hpht, hm⟩ := ms_peel_res_i8 c.pPhasesTarget c.max_vars (markBytes c.max_vars)
    (markBytes c.max_vars + rest) hmb (by omega) hm
  rw [← MemShrinkCfg.pPhasesBest_eq] at hm
  obtain ⟨phb, hphb, hm⟩ := ms_peel_res_i8 c.pPhasesBest c.max_vars (markBytes c.max_vars)
    rest hmb (by omega) hm
  rw [← MemShrinkCfg.pFlags_eq] at hm
  have hm' : (region c.pFlags rest ⋆ (msSegBytes c vals mrk ph pht phb ⋆ R)) m :=
    sep_mono_r (fun _ h => ms_pack5 (by unfold msSegBytes; rfl) h) hm
  exact ⟨vals, mrk, ph, pht, phb, hv, hmk, hph, hpht, hphb, sep_ac hm'⟩

private theorem ms_peel_segU32A (c : MemShrinkCfg) (rest : Nat)
    (hfit : 8 * u32FullBytes c.max_vars + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pFlags (8 * u32FullBytes c.max_vars + rest) ⋆ R) m) :
    ∃ fl lv rs tr tp tm hp ps : List (BitVec 32),
      fl.length = c.max_vars ∧ lv.length = c.max_vars ∧ rs.length = c.max_vars ∧
      tr.length = c.max_vars ∧ tp.length = c.max_vars ∧ tm.length = c.max_vars ∧
      hp.length = c.max_vars ∧ ps.length = c.max_vars ∧
      (msSegU32A c fl lv rs tr tp tm hp ps ⋆ region c.pMinClr rest ⋆ R) m := by
  have hub : 4 * c.max_vars ≤ u32FullBytes c.max_vars := by unfold u32FullBytes; omega
  rw [show 8 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (7 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨fl, hfl, hm⟩ := ms_peel_res_u32 c.pFlags c.max_vars (u32FullBytes c.max_vars)
    (7 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pLevel_eq, show 7 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (6 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨lv, hlv, hm⟩ := ms_peel_res_u32 c.pLevel c.max_vars (u32FullBytes c.max_vars)
    (6 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pReason_eq, show 6 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (5 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨rs, hrs, hm⟩ := ms_peel_res_u32 c.pReason c.max_vars (u32FullBytes c.max_vars)
    (5 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pTrail_eq, show 5 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (4 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨tr, htr, hm⟩ := ms_peel_res_u32 c.pTrail c.max_vars (u32FullBytes c.max_vars)
    (4 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pTrailPos_eq, show 4 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (3 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨tp, htp, hm⟩ := ms_peel_res_u32 c.pTrailPos c.max_vars (u32FullBytes c.max_vars)
    (3 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pTmp_eq, show 3 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (2 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨tm, htm, hm⟩ := ms_peel_res_u32 c.pTmp c.max_vars (u32FullBytes c.max_vars)
    (2 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pHeap_eq, show 2 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨hp, hhp, hm⟩ := ms_peel_res_u32 c.pHeap c.max_vars (u32FullBytes c.max_vars)
    (u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pPos_eq] at hm
  obtain ⟨ps, hps, hm⟩ := ms_peel_res_u32 c.pPos c.max_vars (u32FullBytes c.max_vars)
    rest hub (by omega) hm
  rw [← MemShrinkCfg.pMinClr_eq] at hm
  have hm' : (region c.pMinClr rest ⋆ (msSegU32A c fl lv rs tr tp tm hp ps ⋆ R)) m :=
    sep_mono_r (fun _ h => ms_pack8 (by unfold msSegU32A; rfl) h) hm
  exact ⟨fl, lv, rs, tr, tp, tm, hp, ps, hfl, hlv, hrs, htr, htp, htm, hhp, hps, sep_ac hm'⟩

private theorem ms_peel_segU32B (c : MemShrinkCfg) (rest : Nat)
    (hfit : 7 * u32FullBytes c.max_vars + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pMinClr (7 * u32FullBytes c.max_vars + rest) ⋆ R) m) :
    ∃ mc ss qp qn qs ft fd : List (BitVec 32),
      mc.length = c.max_vars ∧ ss.length = c.max_vars ∧ qp.length = c.max_vars ∧
      qn.length = c.max_vars ∧ qs.length = c.max_vars ∧
      ft.length = c.max_vars + 1 ∧ fd.length = c.max_vars + 1 ∧
      (msSegU32B c mc ss qp qn qs ft fd ⋆ region c.pWvec rest ⋆ R) m := by
  have hub : 4 * c.max_vars ≤ u32FullBytes c.max_vars := by unfold u32FullBytes; omega
  have hub1 : 4 * (c.max_vars + 1) ≤ u32FullBytes c.max_vars := by unfold u32FullBytes; omega
  rw [show 7 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (6 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨mc, hmc, hm⟩ := ms_peel_res_u32 c.pMinClr c.max_vars (u32FullBytes c.max_vars)
    (6 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pShrinkStk_eq, show 6 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (5 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨ss, hss, hm⟩ := ms_peel_res_u32 c.pShrinkStk c.max_vars (u32FullBytes c.max_vars)
    (5 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pQPrev_eq, show 5 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (4 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨qp, hqp, hm⟩ := ms_peel_res_u32 c.pQPrev c.max_vars (u32FullBytes c.max_vars)
    (4 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pQNext_eq, show 4 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (3 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨qn, hqn, hm⟩ := ms_peel_res_u32 c.pQNext c.max_vars (u32FullBytes c.max_vars)
    (3 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pQStamp_eq, show 3 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (2 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨qs, hqs, hm⟩ := ms_peel_res_u32 c.pQStamp c.max_vars (u32FullBytes c.max_vars)
    (2 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pFrameTrail_eq, show 2 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨ft, hft, hm⟩ := ms_peel_res_u32 c.pFrameTrail (c.max_vars + 1) (u32FullBytes c.max_vars)
    (u32FullBytes c.max_vars + rest) hub1 (by omega) hm
  rw [← MemShrinkCfg.pFrameDec_eq] at hm
  obtain ⟨fd, hfd, hm⟩ := ms_peel_res_u32 c.pFrameDec (c.max_vars + 1) (u32FullBytes c.max_vars)
    rest hub1 (by omega) hm
  rw [← MemShrinkCfg.pWvec_eq] at hm
  have hm' : (region c.pWvec rest ⋆ (msSegU32B c mc ss qp qn qs ft fd ⋆ R)) m :=
    sep_mono_r (fun _ h => ms_pack7 (by unfold msSegU32B; rfl) h) hm
  exact ⟨mc, ss, qp, qn, qs, ft, fd, hmc, hss, hqp, hqn, hqs, hft, hfd, sep_ac hm'⟩

private theorem ms_peel_segTailA (c : MemShrinkCfg) (rest : Nat)
    (hfit : 24 * c.max_vars + 8 * c.minDepth + 320 + rest ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pWvec (24 * c.max_vars + 8 * c.minDepth + 320 + rest) ⋆ R) m) :
    ∃ wv ms gu ll : List (BitVec 32), ∃ sc : List (BitVec 64),
      wv.length = 4 * c.max_vars ∧ sc.length = c.max_vars ∧ ms.length = 2 * c.minDepth ∧
      gu.length = 64 ∧ ll.length = 16 ∧
      (msSegTailA c wv ms gu ll sc ⋆ region c.pArena rest ⋆ R) m := by
  rw [show 24 * c.max_vars + 8 * c.minDepth + 320 + rest =
      4 * (4 * c.max_vars) + (8 * c.max_vars + 8 * c.minDepth + 320 + rest) by omega] at hm
  obtain ⟨wv, hwv, hm⟩ := ms_peel_arr32 c.pWvec (4 * c.max_vars)
    (8 * c.max_vars + 8 * c.minDepth + 320 + rest) (by omega) hm
  rw [show 4 * (4 * c.max_vars) = 16 * c.max_vars by omega, ← MemShrinkCfg.pScore_eq,
    show 8 * c.max_vars + 8 * c.minDepth + 320 + rest =
      8 * c.max_vars + (8 * c.minDepth + 320 + rest) by omega] at hm
  obtain ⟨sc, hsc, hm⟩ := ms_peel_arr64 c.pScore c.max_vars
    (8 * c.minDepth + 320 + rest) (by omega) hm
  rw [← MemShrinkCfg.pMinStk_eq, show 8 * c.minDepth + 320 + rest =
      4 * (2 * c.minDepth) + (320 + rest) by omega] at hm
  obtain ⟨ms, hms, hm⟩ := ms_peel_arr32 c.pMinStk (2 * c.minDepth)
    (320 + rest) (by omega) hm
  rw [show 4 * (2 * c.minDepth) = 8 * c.minDepth by omega, ← MemShrinkCfg.pGlueUsed_eq,
    show 320 + rest = 4 * 64 + (64 + rest) by omega] at hm
  obtain ⟨gu, hgu, hm⟩ := ms_peel_arr32 c.pGlueUsed 64 (64 + rest) (by omega) hm
  rw [show (4 * 64 : Nat) = 256 by decide, ← MemShrinkCfg.pLastLearned_eq,
    show 64 + rest = 4 * 16 + rest by omega] at hm
  obtain ⟨ll, hll, hm⟩ := ms_peel_arr32 c.pLastLearned 16 rest (by omega) hm
  rw [show (4 * 16 : Nat) = 64 by decide, ← MemShrinkCfg.pArena_eq] at hm
  have hm' : (region c.pArena rest ⋆ (msSegTailA c wv ms gu ll sc ⋆ R)) m :=
    sep_mono_r (fun _ h => ms_pack5 (by unfold msSegTailA; rfl) h) hm
  exact ⟨wv, ms, gu, ll, sc, hwv, hsc, hms, hgu, hll, sep_ac hm'⟩

private theorem ms_peel_segTailB (c : MemShrinkCfg) (rest : Nat)
    (hfit : 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + rest ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pArena (4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap +
      4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest) ⋆ R) m) :
    ∃ ar wk dl rr ex sb : List (BitVec 32),
      ar.length = c.arena_cap ∧ wk.length = c.wcap ∧ dl.length = 3 * c.delayed_cap ∧
      rr.length = c.red_cap ∧ ex.length = c.extend_cap ∧ sb.length = c.scratch_cap ∧
      (msSegTailB c ar wk dl rr ex sb ⋆ region c.pTrans rest ⋆ R) m := by
  rw [show 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + rest =
      4 * c.arena_cap + (4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨ar, har, hm⟩ := ms_peel_arr32 c.pArena c.arena_cap
    (4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap +
      4 * c.scratch_cap + rest) (by omega) hm
  rw [← MemShrinkCfg.pWstk_eq, show 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + rest = 4 * c.wcap + (12 * c.delayed_cap +
      4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨wk, hwk, hm⟩ := ms_peel_arr32 c.pWstk c.wcap
    (12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest)
    (by omega) hm
  rw [← MemShrinkCfg.pDelayed_eq, show 12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap +
      4 * c.scratch_cap + rest = 4 * (3 * c.delayed_cap) + (4 * c.red_cap + 4 * c.extend_cap +
      4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨dl, hdl, hm⟩ := ms_peel_arr32 c.pDelayed (3 * c.delayed_cap)
    (4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest) (by omega) hm
  rw [show 4 * (3 * c.delayed_cap) = 12 * c.delayed_cap by omega, ← MemShrinkCfg.pRedRefs_eq,
    show 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest =
      4 * c.red_cap + (4 * c.extend_cap + 4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨rr, hrr, hm⟩ := ms_peel_arr32 c.pRedRefs c.red_cap
    (4 * c.extend_cap + 4 * c.scratch_cap + rest) (by omega) hm
  rw [← MemShrinkCfg.pExtendStk_eq, show 4 * c.extend_cap + 4 * c.scratch_cap + rest =
      4 * c.extend_cap + (4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨ex, hex, hm⟩ := ms_peel_arr32 c.pExtendStk c.extend_cap
    (4 * c.scratch_cap + rest) (by omega) hm
  rw [← MemShrinkCfg.pScratchBuf_eq] at hm
  obtain ⟨sb, hsb, hm⟩ := ms_peel_arr32 c.pScratchBuf c.scratch_cap rest (by omega) hm
  rw [← MemShrinkCfg.pTrans_eq] at hm
  have hm' : (region c.pTrans rest ⋆ (msSegTailB c ar wk dl rr ex sb ⋆ R)) m :=
    sep_mono_r (fun _ h => ms_pack6 (by unfold msSegTailB; rfl) h) hm
  exact ⟨ar, wk, dl, rr, ex, sb, har, hwk, hdl, hrr, hex, hsb, sep_ac hm'⟩

private theorem ms_peel_segTrans (c : MemShrinkCfg)
    (hfit : m7TransBytes c.max_vars + c.slack ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pTrans (m7TransBytes c.max_vars + c.slack) ⋆ R) m) :
    ∃ lit_mark : List (BitVec 8), lit_mark.length = 2 * c.max_vars ∧
      ((array (t := i8) c.pLitMark lit_mark ⋆
        region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
        MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R) m := by
  have hvb : 2 * c.max_vars ≤ valsBytes c.max_vars := by unfold valsBytes; omega
  rw [m7TransBytes_def] at hfit hm
  rw [show 56 * c.max_vars + valsBytes c.max_vars + c.slack =
      8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (valsBytes c.max_vars + c.slack))))))) by omega] at hm
  have h1 := ms_peel_reg c.pTrans (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (8 * c.max_vars + (8 * c.max_vars + (valsBytes c.max_vars + c.slack)))))))
    (by omega) hm
  rw [← MemShrinkCfg.pWorkStk1_eq] at h1
  have h2 := ms_peel_reg c.pWorkStk1 (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (8 * c.max_vars + (valsBytes c.max_vars + c.slack)))))) (by omega) h1
  rw [← MemShrinkCfg.pWorkStk2_eq] at h2
  have h3 := ms_peel_reg c.pWorkStk2 (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (valsBytes c.max_vars + c.slack))))) (by omega) h2
  rw [← MemShrinkCfg.pTarjanMark_eq] at h3
  have h4 := ms_peel_reg c.pTarjanMark (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (valsBytes c.max_vars + c.slack)))) (by omega) h3
  rw [← MemShrinkCfg.pTarjanReach_eq] at h4
  have h5 := ms_peel_reg c.pTarjanReach (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (valsBytes c.max_vars + c.slack))) (by omega) h4
  rw [← MemShrinkCfg.pRepr_eq] at h5
  have h6 := ms_peel_reg c.pRepr (8 * c.max_vars)
    (8 * c.max_vars + (valsBytes c.max_vars + c.slack)) (by omega) h5
  rw [← MemShrinkCfg.pSimSig_eq] at h6
  have h7 := ms_peel_reg c.pSimSig (8 * c.max_vars)
    (valsBytes c.max_vars + c.slack) (by omega) h6
  rw [← MemShrinkCfg.pLitMark_eq] at h7
  obtain ⟨lm, hlm, h8⟩ := ms_peel_res_i8 c.pLitMark (2 * c.max_vars) (valsBytes c.max_vars)
    c.slack hvb (by omega) h7
  rw [← MemShrinkCfg.pSlack_eq] at h8
  have h8a : (region c.pSlack c.slack ⋆
      ((array (t := i8) c.pLitMark lm ⋆
        region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
      (MemShrinkTransRegions c ⋆ R))) m := by
    refine sep_mono_r (fun _ h1 => ?_) h8
    refine sep_mono_r (fun _ h2 => ?_) h1
    exact ms_pack7 (by rw [MemShrinkTransRegions_eq, MemShrinkCfg.pWsort_eq]) h2
  exact ⟨lm, hlm, sep_ac h8a⟩

private def msR5 (c : MemShrinkCfg) : Nat := m7TransBytes c.max_vars + c.slack
private def msR4 (c : MemShrinkCfg) : Nat :=
  4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
  4 * c.extend_cap + 4 * c.scratch_cap + msR5 c
private def msR3 (c : MemShrinkCfg) : Nat := 24 * c.max_vars + 8 * c.minDepth + 320 + msR4 c
private def msR2 (c : MemShrinkCfg) : Nat := 7 * u32FullBytes c.max_vars + msR3 c
private def msR1 (c : MemShrinkCfg) : Nat := 8 * u32FullBytes c.max_vars + msR2 c

private theorem ms_arrs_pack_res (c : MemShrinkCfg) (d_cur d_val fuel : BitVec 64)
    (a : MsInitArrs c) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : ((array (t := i8) c.pLitMark a.lit_mark ⋆
        region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
        MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆
        (msSegTailB c a.arena a.wstk a.delayed a.red_refs a.extend_stk a.scratch_buf ⋆
        msSegTailA c a.wvec a.min_stk a.glue_used a.last_learned a.score ⋆
        msSegU32B c a.min_clr a.shrink_stk a.q_prev a.q_next a.q_stamp a.frame_trail
          a.frame_dec ⋆
        msSegU32A c a.flags a.lvl a.rsns a.trl a.trail_pos a.tmp a.heap a.pos ⋆
        msSegBytes c a.vals a.mrk a.phases a.phases_target a.phases_best ⋆ R)) m) :
    (MemShrinkResArrays c (msInitState c d_cur d_val fuel a) ⋆
      MemShrinkLitMark c (msInitState c d_cur d_val fuel a) ⋆
      MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R) m := by
  have hB : msSegBytes c a.vals a.mrk a.phases a.phases_target a.phases_best =
      MemShrinkResBytes c (msInitState c d_cur d_val fuel a) := by
    rw [MemShrinkResBytes_eq]; dsimp only [msInitState]; unfold msSegBytes; rfl
  have hUA : msSegU32A c a.flags a.lvl a.rsns a.trl a.trail_pos a.tmp a.heap a.pos =
      MemShrinkResU32A c (msInitState c d_cur d_val fuel a) := by
    rw [MemShrinkResU32A_eq]; dsimp only [msInitState]; unfold msSegU32A; rfl
  have hUB : msSegU32B c a.min_clr a.shrink_stk a.q_prev a.q_next a.q_stamp a.frame_trail
      a.frame_dec = MemShrinkResU32B c (msInitState c d_cur d_val fuel a) := by
    rw [MemShrinkResU32B_eq]; dsimp only [msInitState]; unfold msSegU32B; rfl
  have hTl : (msSegTailA c a.wvec a.min_stk a.glue_used a.last_learned a.score ⋆
      msSegTailB c a.arena a.wstk a.delayed a.red_refs a.extend_stk a.scratch_buf) =
      MemShrinkResTail c (msInitState c d_cur d_val fuel a) := by
    rw [MemShrinkResTail_eq]; dsimp only [msInitState]
    unfold msSegTailA msSegTailB; ac_rfl
  have hLM : (array (t := i8) c.pLitMark a.lit_mark ⋆
      region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
        (valsBytes c.max_vars - 2 * c.max_vars)) =
      MemShrinkLitMark c (msInitState c d_cur d_val fuel a) := by
    rw [MemShrinkLitMark_eq]; dsimp only [msInitState]
  rw [hLM, hB, hUA, hUB] at hm
  have hm' : ((msSegTailA c a.wvec a.min_stk a.glue_used a.last_learned a.score ⋆
      msSegTailB c a.arena a.wstk a.delayed a.red_refs a.extend_stk a.scratch_buf) ⋆
      MemShrinkResBytes c (msInitState c d_cur d_val fuel a) ⋆
      MemShrinkResU32A c (msInitState c d_cur d_val fuel a) ⋆
      MemShrinkResU32B c (msInitState c d_cur d_val fuel a) ⋆
      MemShrinkLitMark c (msInitState c d_cur d_val fuel a) ⋆
      MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R) m := sep_ac hm
  rw [hTl] at hm'
  rw [MemShrinkResArrays_eq]
  exact sep_ac hm'

private theorem ms_avail_fit (c : MemShrinkCfg) :
    valsBytes c.max_vars + 4 * markBytes c.max_vars + msR1 c ≤ 2 ^ 64 := by
  have hav_fit : c.avail < 2 ^ 64 := by have := c.havail_fit; omega
  have hsz := c.hsize
  unfold msR1 msR2 msR3 msR4 msR5
  rw [MemShrinkCfg.slack_eq, MemShrinkCfg.minDepth_eq, m7FixedBytes_def, m7TransBytes_def]
  rw [m7FixedBytes_def, m7TransBytes_def] at hsz
  omega

private theorem ms_avail_len (c : MemShrinkCfg) (h1152 : 1152 ≤ c.avail) :
    c.avail - 1152 = valsBytes c.max_vars + 4 * markBytes c.max_vars + msR1 c := by
  have hsz := c.hsize
  unfold msR1 msR2 msR3 msR4 msR5
  rw [MemShrinkCfg.slack_eq, MemShrinkCfg.minDepth_eq, m7FixedBytes_def, m7TransBytes_def]
  rw [m7FixedBytes_def, m7TransBytes_def] at hsz
  omega

private theorem ms_peel_front (c : MemShrinkCfg) {R : Mem 64 → Prop} {m : Mem 64} {P : Prop}
    (hm : (region c.pVals (valsBytes c.max_vars + 4 * markBytes c.max_vars + msR1 c) ⋆ R) m)
    (k : ∀ (vals mrk ph pht phb : List (BitVec 8))
      (fl lv rs tr tp tm mc hp ps ss qp qn qs ft fd : List (BitVec 32)),
      vals.length = 2 * c.max_vars → mrk.length = c.max_vars → ph.length = c.max_vars →
      pht.length = c.max_vars → phb.length = c.max_vars → fl.length = c.max_vars →
      lv.length = c.max_vars → rs.length = c.max_vars → tr.length = c.max_vars →
      tp.length = c.max_vars → tm.length = c.max_vars → mc.length = c.max_vars →
      hp.length = c.max_vars → ps.length = c.max_vars → ss.length = c.max_vars →
      qp.length = c.max_vars → qn.length = c.max_vars → qs.length = c.max_vars →
      ft.length = c.max_vars + 1 → fd.length = c.max_vars + 1 →
      (region c.pWvec (msR3 c) ⋆
        (msSegU32B c mc ss qp qn qs ft fd ⋆ msSegU32A c fl lv rs tr tp tm hp ps ⋆
        msSegBytes c vals mrk ph pht phb ⋆ R)) m → P) : P := by
  have hfit := ms_avail_fit c
  obtain ⟨vals, mrk, ph, pht, phb, hv, hmk, hph, hpht, hphb, hm⟩ :=
    ms_peel_segBytes c (msR1 c) hfit hm
  have hm : (region c.pFlags (msR1 c) ⋆ (msSegBytes c vals mrk ph pht phb ⋆ R)) m := sep_ac hm
  rw [msR1] at hm
  have h1 : 8 * u32FullBytes c.max_vars + msR2 c ≤ msR1 c := by unfold msR1; omega
  obtain ⟨fl, lv, rs, tr, tp, tm, hp, ps, hfl, hlv, hrs, htr, htp, htm, hhp, hps, hm⟩ :=
    ms_peel_segU32A c (msR2 c) (by omega) hm
  have hm : (region c.pMinClr (msR2 c) ⋆ (msSegU32A c fl lv rs tr tp tm hp ps ⋆
      msSegBytes c vals mrk ph pht phb ⋆ R)) m := sep_ac hm
  rw [msR2] at hm
  have h2 : 7 * u32FullBytes c.max_vars + msR3 c ≤ msR2 c := by unfold msR2; omega
  obtain ⟨mc, ss, qp, qn, qs, ft, fd, hmc, hss, hqp, hqn, hqs, hft, hfd, hm⟩ :=
    ms_peel_segU32B c (msR3 c) (by omega) hm
  have hm : (region c.pWvec (msR3 c) ⋆ (msSegU32B c mc ss qp qn qs ft fd ⋆
      msSegU32A c fl lv rs tr tp tm hp ps ⋆ msSegBytes c vals mrk ph pht phb ⋆ R)) m := sep_ac hm
  exact k vals mrk ph pht phb fl lv rs tr tp tm mc hp ps ss qp qn qs ft fd
    hv hmk hph hpht hphb hfl hlv hrs htr htp htm hmc hhp hps hss hqp hqn hqs hft hfd hm

private theorem ms_peel_back (c : MemShrinkCfg) {R : Mem 64 → Prop} {m : Mem 64} {P : Prop}
    (hfit3 : msR3 c ≤ 2 ^ 64) (hm : (region c.pWvec (msR3 c) ⋆ R) m)
    (k : ∀ (lm : List (BitVec 8)) (wv ms gu ll ar wk dl rr ex sb : List (BitVec 32))
      (sc : List (BitVec 64)),
      lm.length = 2 * c.max_vars → wv.length = 4 * c.max_vars → ms.length = 2 * c.minDepth →
      gu.length = 64 → ll.length = 16 → ar.length = c.arena_cap → wk.length = c.wcap →
      dl.length = 3 * c.delayed_cap → rr.length = c.red_cap → ex.length = c.extend_cap →
      sb.length = c.scratch_cap → sc.length = c.max_vars →
      ((array (t := i8) c.pLitMark lm ⋆
        region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
        MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆
        (msSegTailB c ar wk dl rr ex sb ⋆ msSegTailA c wv ms gu ll sc ⋆ R)) m → P) : P := by
  rw [msR3] at hm
  have h3 : 24 * c.max_vars + 8 * c.minDepth + 320 + msR4 c ≤ msR3 c := by unfold msR3; omega
  obtain ⟨wv, ms, gu, ll, sc, hwv, hsc, hms, hgu, hll, hm⟩ :=
    ms_peel_segTailA c (msR4 c) (by omega) hm
  have hm : (region c.pArena (msR4 c) ⋆ (msSegTailA c wv ms gu ll sc ⋆ R)) m := sep_ac hm
  rw [msR4] at hm
  have h4 : 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + msR5 c ≤ msR4 c := by unfold msR4; omega
  obtain ⟨ar, wk, dl, rr, ex, sb, har, hwk, hdl, hrr, hex, hsb, hm⟩ :=
    ms_peel_segTailB c (msR5 c) (by omega) hm
  have hm : (region c.pTrans (msR5 c) ⋆
      (msSegTailB c ar wk dl rr ex sb ⋆ msSegTailA c wv ms gu ll sc ⋆ R)) m := sep_ac hm
  rw [msR5] at hm
  have h5 : m7TransBytes c.max_vars + c.slack ≤ msR5 c := by unfold msR5; omega
  obtain ⟨lm, hlm, hm⟩ := ms_peel_segTrans c (by omega) hm
  exact k lm wv ms gu ll ar wk dl rr ex sb sc
    hlm hwv hms hgu hll har hwk hdl hrr hex hsb hsc hm

private theorem ms_region_to_mem (c : MemShrinkCfg) (d_cur d_val fuel : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h1152 : 1152 ≤ c.avail)
    (hm : (region (c.hdr + 1152) (c.avail - 1152) ⋆ R) m) :
    ∃ a : MsInitArrs c,
      (MemShrinkResArrays c (msInitState c d_cur d_val fuel a) ⋆
        MemShrinkLitMark c (msInitState c d_cur d_val fuel a) ⋆
        MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R) m := by
  have hfit3 : msR3 c ≤ 2 ^ 64 := by
    have := ms_avail_fit c; unfold msR1 msR2 at this; omega
  rw [ms_avail_len c h1152,
    show c.hdr + 1152 = c.pVals by rw [MemShrinkCfg.pVals_eq]; rfl] at hm
  refine ms_peel_front c hm fun vals mrk ph pht phb fl lv rs tr tp tm mc hp ps ss qp qn qs
      ft fd hv hmk hph hpht hphb hfl hlv hrs htr htp htm hmc hhp hps hss hqp hqn hqs hft hfd hm1 =>
    ms_peel_back c hfit3 hm1 fun lm wv ms gu ll ar wk dl rr ex sb sc hlm hwv hms hgu hll har hwk
        hdl hrr hex hsb hsc hm2 => ?_
  let a : MsInitArrs c :=
    ⟨vals, mrk, lm, ph, pht, phb, fl, lv, rs, tr, tp, tm, mc, hp, ps, ss, qp, qn, qs, ft, fd,
      wv, ms, gu, ll, ar, wk, dl, rr, ex, sb, sc, hv, hmk, hlm, hph, hpht, hphb, hfl, hlv, hrs,
      htr, htp, htm, hmc, hhp, hps, hss, hqp, hqn, hqs, hft, hfd, hwv, hms, hgu, hll, har, hwk, hdl,
      hrr, hex, hsb, hsc⟩
  refine ⟨a, @ms_arrs_pack_res c d_cur d_val fuel a R m ?_⟩
  dsimp only [a]; exact sep_ac hm2

private theorem ms_forall_lt_succ {n : Nat} {P : Nat → Prop}
    (h0 : P n) (hs : ∀ i < n, P i) : ∀ i < n + 1, P i := fun i hi =>
  if h : i = n then h ▸ h0 else hs i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) h)

private theorem ms_list_eq_35 {a b : List (BitVec 64)} (ha : a.length = 35) (hb : b.length = 35)
    (h : ∀ i < 35, a[i]? = b[i]?) : a = b := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < 35
  · exact h i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

private theorem ms_bv_ofNat_mul (k n : Nat) :
    BitVec.ofNat 64 k * BitVec.ofNat 64 n = BitVec.ofNat 64 (k * n) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

private theorem ms_hdrTail_eq (c : MemShrinkCfg) (avail_dyn : Nat)
    (har_c : c.arena_cap = 2 * fullInitAp avail_dyn)
    (hwk_c : c.wcap = 2 * fullInitWp avail_dyn)
    (hrr_c : c.red_cap = 2 * fullInitRp avail_dyn)
    (d_cur d_val fuel : BitVec 64) (a : MsInitArrs c)
    {w0 w1 w2 w3 : List (BitVec 64)}
    (hw0l : w0.length = 35) (hw1l : w1.length = 35)
    (hw2l : w2.length = 35) (hw3l : w3.length = 35) :
    let w1' := w1.set 17 (BitVec.ofNat 64 c.delayed_cap)
    let w3'' := (w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7 (BitVec.ofNat 64 c.scratch_cap)
    let s0 := msInitState c d_cur d_val fuel a
    m7HdrW0 c.mv fuel (m7ArenasW0 c.hdr c.max_vars avail_dyn w0) = m7HdrTailWords0 c s0 ∧
    m7HdrW1 (m7ArenasW1 c.hdr c.max_vars avail_dyn c.delayed_cap c.extend_cap c.scratch_cap w1') =
      m7HdrTailWords1 c s0 ∧
    m7HdrW2 c.mv c.max_vars (m7ArenasW2 c.hdr c.max_vars avail_dyn
      c.delayed_cap c.extend_cap c.scratch_cap w2) = m7HdrTailWords2 c s0 ∧
    m7HdrW3 c.mv (m7ArenasW3 c.hdr c.max_vars avail_dyn c.delayed_cap
      c.extend_cap c.scratch_cap w3'') = m7HdrTailWords3 c s0 := by
  dsimp only
  have hAr : c.hdr + BitVec.ofNat 64 (m7FixedBytes c.max_vars) = c.pArena := by
    simp only [m7FixedBytes_def, MemShrinkCfg.pArena_eq, MemShrinkCfg.pLastLearned_eq,
      MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pMinStk_eq, MemShrinkCfg.pScore_eq,
      MemShrinkCfg.pWvec_eq, MemShrinkCfg.pFrameDec_eq, MemShrinkCfg.pFrameTrail_eq,
      MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pQNext_eq, MemShrinkCfg.pQPrev_eq,
      MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pMinClr_eq, MemShrinkCfg.pPos_eq,
      MemShrinkCfg.pHeap_eq, MemShrinkCfg.pTmp_eq, MemShrinkCfg.pTrailPos_eq,
      MemShrinkCfg.pTrail_eq, MemShrinkCfg.pReason_eq, MemShrinkCfg.pLevel_eq,
      MemShrinkCfg.pFlags_eq, MemShrinkCfg.pPhasesBest_eq, MemShrinkCfg.pPhasesTarget_eq,
      MemShrinkCfg.pPhases_eq, MemShrinkCfg.pMark_eq, MemShrinkCfg.pVals_eq,
      MemShrinkCfg.minDepth_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hWs : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn) = c.pWstk := by
    rw [MemShrinkCfg.pWstk_eq, har_c]; congr 2; omega
  have hDl : c.pWstk + BitVec.ofNat 64 (8 * fullInitWp avail_dyn) = c.pDelayed := by
    rw [MemShrinkCfg.pDelayed_eq, hwk_c]; congr 2; omega
  have hRr : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn + 8 * fullInitWp avail_dyn) +
      BitVec.ofNat 64 (12 * c.delayed_cap) = c.pRedRefs := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, hWs, hDl, MemShrinkCfg.pRedRefs_eq]
  have hEx : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn + 8 * fullInitWp avail_dyn +
      12 * c.delayed_cap + 8 * fullInitRp avail_dyn) = c.pExtendStk := by
    rw [MemShrinkCfg.pExtendStk_eq, MemShrinkCfg.pRedRefs_eq, MemShrinkCfg.pDelayed_eq,
      MemShrinkCfg.pWstk_eq, har_c, hwk_c, hrr_c]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hSc : c.pExtendStk + BitVec.ofNat 64 (4 * c.extend_cap) = c.pScratchBuf :=
    (MemShrinkCfg.pScratchBuf_eq c).symm
  have hTr1 : c.pRedRefs + BitVec.ofNat 64 (8 * fullInitRp avail_dyn + 4 * c.extend_cap +
      4 * c.scratch_cap) = c.pTrans := by
    rw [MemShrinkCfg.pTrans_eq, MemShrinkCfg.pScratchBuf_eq, MemShrinkCfg.pExtendStk_eq, hrr_c]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hTr2 : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn + 8 * fullInitWp avail_dyn +
      12 * c.delayed_cap + 8 * fullInitRp avail_dyn + 4 * c.extend_cap + 4 * c.scratch_cap) =
      c.pTrans := by
    rw [MemShrinkCfg.pTrans_eq, MemShrinkCfg.pScratchBuf_eq, MemShrinkCfg.pExtendStk_eq,
      MemShrinkCfg.pRedRefs_eq, MemShrinkCfg.pDelayed_eq, MemShrinkCfg.pWstk_eq,
      har_c, hwk_c, hrr_c]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hTr3 : c.pScratchBuf + BitVec.ofNat 64 (4 * c.scratch_cap) = c.pTrans :=
    (MemShrinkCfg.pTrans_eq c).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hp10 : (m7PtrsW0 c.hdr c.max_vars w0)[10]! = c.pArena := by
      rw [getElem!_pos (c := m7PtrsW0 c.hdr c.max_vars w0) (i := 10)
          (by simp [m7PtrsW0_eq, List.length_set, hw0l]), ← hAr]
      exact Option.some.inj
        ((List.getElem?_eq_getElem (by simp [m7PtrsW0_eq, List.length_set, hw0l])).symm.trans
          (m7PtrsW0_10 c.hdr c.max_vars hw0l))
    rw [m7HdrW0_eq, m7ArenasW0_eq, hp10, m7PtrsW0_eq, m7HdrTailWords0_eq]
    dsimp only [msInitState]
    rw [har_c, hwk_c, hWs, hDl, ← MemShrinkCfg.pVals_eq, ← MemShrinkCfg.pMark_eq,
      ← MemShrinkCfg.pPhases_eq, ← MemShrinkCfg.pPhasesTarget_eq, ← MemShrinkCfg.pPhasesBest_eq,
      ← MemShrinkCfg.pFlags_eq, ← MemShrinkCfg.pLevel_eq, ← MemShrinkCfg.pReason_eq,
      ← MemShrinkCfg.pTrail_eq, ← MemShrinkCfg.pTrailPos_eq, ← MemShrinkCfg.pTmp_eq,
      ← MemShrinkCfg.pHeap_eq, ← MemShrinkCfg.pPos_eq, ← MemShrinkCfg.pMinClr_eq,
      ← MemShrinkCfg.pShrinkStk_eq, ← MemShrinkCfg.pQPrev_eq, ← MemShrinkCfg.pQNext_eq,
      ← MemShrinkCfg.pQStamp_eq, ← MemShrinkCfg.pFrameTrail_eq, ← MemShrinkCfg.pFrameDec_eq,
      ← MemShrinkCfg.pWvec_eq, ← MemShrinkCfg.pScore_eq, ← MemShrinkCfg.minDepth_eq,
      ← MemShrinkCfg.pMinStk_eq, ← MemShrinkCfg.pGlueUsed_eq, ← MemShrinkCfg.pLastLearned_eq,
      ← MemShrinkCfg.pArena_eq]
    apply ms_list_eq_35 (by simp [List.length_set, hw0l]) (by simp)
    iterate 35
      (apply ms_forall_lt_succ
       · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_set,
           List.length_set, hw0l, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte] <;> rfl)
    intro i hi; omega
  · rw [m7HdrW1_eq, m7ArenasW1_eq, m7PtrsW1_eq, m7HdrTailWords1_eq]
    dsimp only [msInitState]
    simp only [ms_bv_ofNat_mul, hAr, hRr, hTr1, hrr_c, MemShrinkCfg.pWsort_eq,
      MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pMinStk_eq, MemShrinkCfg.pScore_eq,
      MemShrinkCfg.pWvec_eq, MemShrinkCfg.pFrameDec_eq, MemShrinkCfg.pFrameTrail_eq,
      MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pQNext_eq, MemShrinkCfg.pQPrev_eq,
      MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pMinClr_eq, MemShrinkCfg.pPos_eq,
      MemShrinkCfg.pHeap_eq, MemShrinkCfg.pTmp_eq, MemShrinkCfg.pTrailPos_eq,
      MemShrinkCfg.pTrail_eq, MemShrinkCfg.pReason_eq, MemShrinkCfg.pLevel_eq,
      MemShrinkCfg.pFlags_eq, MemShrinkCfg.pPhasesBest_eq, MemShrinkCfg.pPhasesTarget_eq,
      MemShrinkCfg.pPhases_eq, MemShrinkCfg.pMark_eq, MemShrinkCfg.pVals_eq,
      MemShrinkCfg.minDepth_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    apply ms_list_eq_35 (by simp [List.length_set, hw1l]) (by simp)
    iterate 35
      (apply ms_forall_lt_succ
       · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_set,
           List.length_set, hw1l, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte] <;>
         first | rfl | (apply congrArg some; congr 2; omega))
    intro i hi; omega
  · have hpFl : c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars + 4 * markBytes c.max_vars) =
        c.pFlags := by
      simp only [MemShrinkCfg.pFlags_eq, MemShrinkCfg.pPhasesBest_eq,
        MemShrinkCfg.pPhasesTarget_eq, MemShrinkCfg.pPhases_eq, MemShrinkCfg.pMark_eq,
        MemShrinkCfg.pVals_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    have hpFT : c.pFlags + 13#64 * BitVec.ofNat 64 (u32FullBytes c.max_vars) = c.pFrameTrail := by
      rw [show (13#64 : BitVec 64) = BitVec.ofNat 64 13 from rfl, ms_bv_ofNat_mul]
      simp only [MemShrinkCfg.pFrameTrail_eq, MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pQNext_eq,
        MemShrinkCfg.pQPrev_eq, MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pMinClr_eq,
        MemShrinkCfg.pPos_eq, MemShrinkCfg.pHeap_eq, MemShrinkCfg.pTmp_eq,
        MemShrinkCfg.pTrailPos_eq, MemShrinkCfg.pTrail_eq, MemShrinkCfg.pReason_eq,
        MemShrinkCfg.pLevel_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    have hpW1 : c.pTrans + BitVec.ofNat 64 (8 * c.max_vars) = c.pWorkStk1 := by
      rw [MemShrinkCfg.pWorkStk1_eq]
    have hpW2 : c.pTrans + BitVec.ofNat 64 (16 * c.max_vars) = c.pWorkStk2 := by
      simp only [MemShrinkCfg.pWorkStk2_eq, MemShrinkCfg.pWorkStk1_eq, BitVec.add_assoc,
        ← BitVec.ofNat_add]; congr 2; omega
    have hpTM : c.pTrans + BitVec.ofNat 64 (24 * c.max_vars) = c.pTarjanMark := by
      simp only [MemShrinkCfg.pTarjanMark_eq, ← hpW2, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    have hpRp : c.pTrans + BitVec.ofNat 64 (40 * c.max_vars) = c.pRepr := by
      simp only [MemShrinkCfg.pRepr_eq, MemShrinkCfg.pTarjanReach_eq, ← hpTM, BitVec.add_assoc,
        ← BitVec.ofNat_add]; congr 2; omega
    have hpSS : c.pTrans + BitVec.ofNat 64 (48 * c.max_vars) = c.pSimSig := by
      simp only [MemShrinkCfg.pSimSig_eq, ← hpRp, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    have hpLM : c.pTrans + BitVec.ofNat 64 (56 * c.max_vars) = c.pLitMark := by
      simp only [MemShrinkCfg.pLitMark_eq, ← hpSS, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    have hbva : c.max_vars - c.mv = c.bva_cap := by have := c.hbva; omega
    rw [m7HdrW2_eq, m7ArenasW2_eq, m7PtrsW2_eq, m7HdrTailWords2_eq]
    dsimp only [msInitState]
    rw [hAr, hTr2, hpFl, hpFT, ← MemShrinkCfg.pFrameDec_eq, hpLM, hpRp, hpSS, hpW1, hpW2, hpTM,
      hbva]
    apply ms_list_eq_35 (by simp [List.length_set, hw2l]) (by simp)
    iterate 35
      (apply ms_forall_lt_succ
       · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_set,
           List.length_set, hw2l, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte] <;> rfl)
    intro i hi; omega
  · have hpTR : c.pTrans + BitVec.ofNat 64 (32 * c.max_vars) = c.pTarjanReach := by
      simp only [MemShrinkCfg.pTarjanReach_eq, MemShrinkCfg.pTarjanMark_eq,
        MemShrinkCfg.pWorkStk2_eq, MemShrinkCfg.pWorkStk1_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    have hpWV : c.pTrans + BitVec.ofNat 64 (40 * c.max_vars) = c.pWalkVals := by
      simp only [MemShrinkCfg.pWalkVals_eq, MemShrinkCfg.pRepr_eq, ← hpTR, BitVec.add_assoc,
        ← BitVec.ofNat_add]; congr 2; omega
    have hpWB : c.pTrans + BitVec.ofNat 64 (48 * c.max_vars) = c.pWalkBest := by
      simp only [MemShrinkCfg.pWalkBest_eq, MemShrinkCfg.pSimSig_eq, ← MemShrinkCfg.pWalkVals_eq,
        ← hpWV, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    have hpLL : c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars + 4 * markBytes c.max_vars +
        15 * u32FullBytes c.max_vars + 24 * c.max_vars + 8 * fullMinDepthOf c.max_vars) +
        BitVec.ofNat 64 256 = c.pLastLearned := by
      rw [MemShrinkCfg.pLastLearned_eq]; congr 1
      simp only [MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pMinStk_eq, MemShrinkCfg.pScore_eq,
        MemShrinkCfg.pWvec_eq, MemShrinkCfg.pFrameDec_eq, MemShrinkCfg.pFrameTrail_eq,
        MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pQNext_eq, MemShrinkCfg.pQPrev_eq,
        MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pMinClr_eq, MemShrinkCfg.pPos_eq,
        MemShrinkCfg.pHeap_eq, MemShrinkCfg.pTmp_eq, MemShrinkCfg.pTrailPos_eq,
        MemShrinkCfg.pTrail_eq, MemShrinkCfg.pReason_eq, MemShrinkCfg.pLevel_eq,
        MemShrinkCfg.pFlags_eq, MemShrinkCfg.pPhasesBest_eq, MemShrinkCfg.pPhasesTarget_eq,
        MemShrinkCfg.pPhases_eq, MemShrinkCfg.pMark_eq, MemShrinkCfg.pVals_eq,
        MemShrinkCfg.minDepth_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [m7HdrW3_eq, m7ArenasW3_eq, m7PtrsW3_eq, m7HdrTailWords3_eq]
    dsimp only [msInitState]
    rw [hAr, hEx, hSc, hTr3, hpTR, hpWV, hpWB, hpLL]
    apply ms_list_eq_35 (by simp [List.length_set, hw3l]) (by simp)
    iterate 35
      (apply ms_forall_lt_succ
       · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_set,
           List.length_set, hw3l, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte] <;> rfl)
    intro i hi; omega

private theorem ms_hdrTail4_words (c : MemShrinkCfg) (s : FullState) :
    hdrTail4 c.hdr (m7HdrTailWords0 c s) (m7HdrTailWords1 c s)
      (m7HdrTailWords2 c s) (m7HdrTailWords3 c s) =
      array64 (c.hdr + 32) (m7HdrTailWords c s) := by
  have ht0 : (m7HdrTailWords0 c s).length = 35 := by rw [m7HdrTailWords0_eq]; simp
  have ht1 : (m7HdrTailWords1 c s).length = 35 := by rw [m7HdrTailWords1_eq]; simp
  have ht2 : (m7HdrTailWords2 c s).length = 35 := by rw [m7HdrTailWords2_eq]; simp
  have ht3 : (m7HdrTailWords3 c s).length = 35 := by rw [m7HdrTailWords3_eq]; simp
  rw [hdrTail4_eq_array64 ht0 ht1 ht2 ht3, m7HdrTailWords_eq]

theorem full_init_state_m5_s9ms_wp (Γ : Env)
    (hHdr : EnvSpec Γ "kissat_parse_header" kissatParseHeaderSpec)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (hMaxV : EnvSpec Γ "full_calc_max_v" s9msCalcMaxVSpec)
    (hExt : EnvSpec Γ "full_calc_ext_cap_m5" m7CalcExtCapSpec)
    (hScr : EnvSpec Γ "full_calc_scr_cap_m5" s9msCalcScrCapSpec)
    (hArenas : EnvSpec Γ "full_init_arenas" m7InitArenasSpec)
    (hInitHdr : EnvSpec Γ "full_init_hdr" m7InitHdrSpec)
    (hZt1 : EnvSpec Γ "full_zero_tables1" m7ZeroTables1Spec)
    (hZt2 : EnvSpec Γ "full_zero_tables2" m7ZeroTables2Spec) :
    ∀ a m Q X, m7InitStateSpec a m Q X → Func.wp Γ full_init_state_m5_body a m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, _⟩ m Q X hsp
  rw [m7InitStateSpec_eq] at hsp
  rcases hsp with ⟨cnfBytes, R, rfl, hcfit, hfit_avail, hav1152, hm_in, hfails, hsucc⟩
  have hav_le : avail.toNat ≤ 2 ^ 64 := by omega
  have hm0 : (region hdr_addr 32 ⋆ (region (hdr_addr + 32) 1120 ⋆
      (region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)))) m := by
    have ha1 : avail.toNat = 32 + (avail.toNat - 32) := by omega
    have ha2 : avail.toNat - 32 = 1120 + (avail.toNat - 1152) := by omega
    rw [ha1, region_split (by omega), ha2, region_split (by omega),
      show hdr_addr + BitVec.ofNat 64 32 = hdr_addr + 32 from rfl,
      show (hdr_addr + 32) + BitVec.ofNat 64 1120 = hdr_addr + 1152 by
        rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
          show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl, ptr_add_ofNat]] at hm_in
    exact sep_ac hm_in
  have hm0a := sep_mono (fun _ hr => region32_to_dimacsState hr) hm0
  obtain ⟨mv0, hm0a⟩ := sep_ex_l.mp hm0a
  obtain ⟨nc0, hm0a⟩ := sep_ex_l.mp hm0a
  obtain ⟨cur0, hm0a⟩ := sep_ex_l.mp hm0a
  obtain ⟨val0, hm0a⟩ := sep_ex_l.mp hm0a
  have hm0b : (region (hdr_addr + 32) 1120 ⋆ (dimacsState hdr_addr mv0 nc0 cur0 val0 ⋆
      region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_ac hm0a
  have hm0c := sep_mono (fun _ hw => region_to_array64 140 (by decide) hw) hm0b
  obtain ⟨w140, hm0c⟩ := sep_ex_l.mp hm0c
  obtain ⟨hw140, hm0c⟩ := sep_pure_l.mp hm0c
  have hm_pre : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv0 nc0 cur0 val0 ⋆
      array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R) m :=
    sep_ac hm0c
  rw [envSpec_eq] at hHdr hFixed hTrans hMaxV hExt hScr hArenas hInitHdr hZt1 hZt2
  unfold full_init_state_m5_body; dsimp only [Func.wp]
  apply wp_call_of_spec; apply hHdr
  refine ⟨mv0, nc0, cur0, val0, cnfBytes, array64 (hdr_addr + 32) w140 ⋆
    region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R, rfl, hcfit,
    Eq.mp (congrFun (by ac_rfl) m) hm_pre, ?_⟩
  cases hhdr : parseHeader cnfBytes with
  | none =>
    intro mv' nc' cur' val' m1 hm1
    dsimp only [Arg.val] at hm1
    refine wp_jnz_of (fun hc => by cases hc) (fun _ => ?_)
    c0_hsteps
    have hm1_r : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv' nc' cur' val' ⋆
        array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R) m1 :=
      Eq.mp (congrFun (by ac_rfl) m1) hm1
    have hm1' := ms_hdr_region_rejoin hav1152 hav_le hw140 hm1_r
    exact hfails m1 hm1' (fun _ _ _ h => by rw [hhdr] at h; cases h)
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    intro j m1 hmv_bd hnc_bd hj_le hdrop hm1
    dsimp only [Arg.val] at hm1
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    · have hm1s : (array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
            cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
          (bytes cnf_ptr cnfBytes ⋆ array64 (hdr_addr + 32) w140 ⋆
            region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m1 := by
        have hm1_d := hm1; unfold dimacsState at hm1_d
        exact Eq.mp (congrFun (by ac_rfl) m1) hm1_d
      refine wp_load_array64 (i := 0) (by simp [Arg.val]) (by simp) hm1s ?_
      c0_hstep
      refine wp_load_array64 (i := 1) (by simp [Arg.val]) (by simp) hm1s ?_
      dsimp only [List.getElem_cons_zero, List.getElem_cons_succ]
      have hmv2 : mv < 2 * dimacsBound := by unfold dimacsBound at *; omega
      have hmv_tonat : (BitVec.ofNat 64 mv).toNat = mv := by
        simp [BitVec.toNat_ofNat]; unfold dimacsBound at *; omega
      have hnc_tonat : (BitVec.ofNat 64 nc).toNat = nc := by
        simp [BitVec.toNat_ofNat]; unfold dimacsBound at *; omega
      apply wp_call_of_spec; apply hFixed; rw [m7FixedBytesSpec_eq]
      refine ⟨by dsimp [vals, Arg.val]; rw [hmv_tonat]; exact hmv2, ?_⟩
      dsimp only [vals, Arg.val]; rw [hmv_tonat]
      apply wp_call_of_spec; apply hTrans; rw [m7TransBytesSpec_eq]
      refine ⟨by dsimp [vals, Arg.val]; rw [hmv_tonat]; exact hmv2, ?_⟩
      dsimp only [vals, Arg.val]; rw [hmv_tonat]
      have hfx_lt := m7FixedBytes_lt hmv2
      have htr_lt := m7TransBytes_lt hmv2
      have htot_lt : m7FixedBytes mv + m7TransBytes mv < 2 ^ 64 := by omega
      c0_hsplit
      · c0_hsteps
        have hm1_r : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
            (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
            array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R) m1 :=
          Eq.mp (congrFun (by ac_rfl) m1) hm1
        have hm1' := ms_hdr_region_rejoin hav1152 hav_le hw140 hm1_r
        refine hfails m1 hm1' fun mv' nc' rest' h' => ?_
        rw [hhdr] at h'; rcases Option.some.inj h' with ⟨rfl, rfl, rfl⟩
        rw [Nat.mod_eq_of_lt htot_lt] at hc
        omega
      · have hge_mv : m7FixedBytes mv + m7TransBytes mv ≤ avail.toNat := by
          rw [Nat.mod_eq_of_lt htot_lt] at hc; omega
        c0_hsplit
        · c0_hsteps
          have hm1_r : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
              (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
              array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆
              R) m1 :=
            Eq.mp (congrFun (by ac_rfl) m1) hm1
          have hm1' := ms_hdr_region_rejoin hav1152 hav_le hw140 hm1_r
          refine hfails m1 hm1' fun mv' nc' rest' h' => ?_
          rw [hhdr] at h'; rcases Option.some.inj h' with ⟨rfl, rfl, rfl⟩
          have hnc40 : nc * 40 + 136 < 2 ^ 64 := by unfold dimacsBound at *; omega
          have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
          have hav_lt : avail.toNat < 2 ^ 64 := avail.isLt
          rw [Nat.mod_eq_of_lt htot_lt, Nat.mod_eq_of_lt hnc64,
            show BitVec.toNat 40 = 40 by decide, show BitVec.toNat 136 = 136 by decide,
            Nat.mod_eq_of_lt hnc40,
            show 2 ^ 64 - (m7FixedBytes mv + m7TransBytes mv) + avail.toNat =
              2 ^ 64 + (avail.toNat - (m7FixedBytes mv + m7TransBytes mv)) by omega,
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hc
          omega
        · have hbase : m7FixedBytes mv + m7TransBytes mv + nc * 40 + 136 ≤ avail.toNat := by
            have hnc40 : nc * 40 + 136 < 2 ^ 64 := by unfold dimacsBound at *; omega
            have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
            have hav_lt : avail.toNat < 2 ^ 64 := avail.isLt
            rw [Nat.mod_eq_of_lt htot_lt, Nat.mod_eq_of_lt hnc64,
              show BitVec.toNat 40 = 40 by decide, show BitVec.toNat 136 = 136 by decide,
              Nat.mod_eq_of_lt hnc40,
              show 2 ^ 64 - (m7FixedBytes mv + m7TransBytes mv) + avail.toNat =
                2 ^ 64 + (avail.toNat - (m7FixedBytes mv + m7TransBytes mv)) by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hc
            omega
          let mx := s9msCalcMaxV avail.toNat mv nc (m7FixedBytes mv)
          have hmx_ge : mv ≤ mx := s9msCalcMaxV_ge
          have hmx_lt : mx < 2 * dimacsBound := s9msCalcMaxV_lt hmv_bd
          have hmx_fits : m7FixedBytes mx + m7TransBytes mx + nc * 40 + 136 ≤ avail.toNat :=
            s9msCalcMaxV_fits hbase
          have hfx_lt64 : m7FixedBytes mv < 2 ^ 64 := by omega
          apply wp_call_of_spec; apply hMaxV; rw [s9msCalcMaxVSpec_eq]
          refine ⟨?_, ?_, ?_, ?_⟩
          · dsimp only [vals, Arg.val]; rw [hmv_tonat]; exact hmv_bd
          · dsimp only [vals, Arg.val]; rw [hnc_tonat]; exact hnc_bd
          · dsimp only [vals, Arg.val]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt64]; omega
          · dsimp only [vals, Arg.val]; rw [hmv_tonat, hnc_tonat]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt64]
            apply wp_call_of_spec; apply hTrans; rw [m7TransBytesSpec_eq]
            refine ⟨by dsimp [vals, Arg.val]; rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]; exact hmx_lt, ?_⟩
            dsimp only [vals, Arg.val]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
            apply wp_call_of_spec; apply hFixed; rw [m7FixedBytesSpec_eq]
            refine ⟨by dsimp [vals, Arg.val]; rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]; exact hmx_lt, ?_⟩
            dsimp only [vals, Arg.val]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
            have hfx_mx_lt : m7FixedBytes mx < 2 ^ 64 :=
              Nat.lt_trans (m7FixedBytes_lt hmx_lt) (by decide)
            have htr_mx_lt : m7TransBytes mx < 2 ^ 64 :=
              Nat.lt_trans (m7TransBytes_lt hmx_lt) (by decide)
            have hmx_fx_le : m7FixedBytes mx ≤ avail.toNat := by omega
            have hrem_fx_eq : avail - BitVec.ofNat 64 (m7FixedBytes mx) =
                BitVec.ofNat 64 (avail.toNat - m7FixedBytes mx) := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_sub_of_le (by
                rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_mx_lt]
                exact hmx_fx_le),
                BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_mx_lt,
                Nat.mod_eq_of_lt (by omega)]
            c0_hsplit
            · exfalso
              have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
              have hav_lt : avail.toNat < 2 ^ 64 := avail.isLt
              rw [Nat.mod_eq_of_lt hfx_mx_lt, Nat.mod_eq_of_lt hnc64,
                show BitVec.toNat 40 = 40 by decide, show BitVec.toNat 136 = 136 by decide] at hc
              change (2 ^ 64 - m7FixedBytes mx + avail.toNat) % 2 ^ 64 <
                (m7TransBytes mx + nc * 40 + 136) % 2 ^ 64 at hc
              rw [Nat.mod_eq_of_lt (by omega : m7TransBytes mx + nc * 40 + 136 < 2 ^ 64),
                show 2 ^ 64 - m7FixedBytes mx + avail.toNat =
                  2 ^ 64 + (avail.toNat - m7FixedBytes mx) by omega,
                Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hc
              omega
            · let avail_dyn := avail.toNat - (m7FixedBytes mx + m7TransBytes mx)
              have hav_dyn_ge : nc * 40 + 136 ≤ avail_dyn := by omega
              have hav_dyn_eq : (avail - BitVec.ofNat 64 (m7FixedBytes mx)) -
                  BitVec.ofNat 64 (m7TransBytes mx) = BitVec.ofNat 64 avail_dyn := by
                apply BitVec.eq_of_toNat_eq
                rw [hrem_fx_eq, BitVec.toNat_sub_of_le (by
                  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt htr_mx_lt, Nat.mod_eq_of_lt (by omega)]; omega),
                  BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt htr_mx_lt, Nat.mod_eq_of_lt (by omega),
                  Nat.mod_eq_of_lt (by omega)]
                omega
              refine wp_join_state1 (fun x : BitVec 64 => x)
                (fun del_cap m2 => del_cap = BitVec.ofNat 64 (fullInitDelCap avail_dyn) ∧ m2 = m1)
                ?_ ?_
              · rintro J403 del_cap m2 ⟨rfl, hm2_eq⟩; subst m2
                dsimp only [Blocks.get_here]
                have hdyn_toNat : (BitVec.ofNat 64 avail_dyn).toNat = avail_dyn := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                have hav_dyn' : avail - BitVec.ofNat 64 (m7FixedBytes (s9msCalcMaxV avail.toNat mv
                    nc (m7FixedBytes mv))) - BitVec.ofNat 64 (m7TransBytes (s9msCalcMaxV
                    avail.toNat mv nc (m7FixedBytes mv))) = BitVec.ofNat 64 avail_dyn :=
                  hav_dyn_eq
                apply wp_call_of_spec; apply hExt; rw [m7CalcExtCapSpec_eq]
                dsimp only [vals, lift2, Arg.val]; rw [hav_dyn', hdyn_toNat]
                apply wp_call_of_spec; apply hScr; rw [s9msCalcScrCapSpec_eq]
                dsimp only [vals, Arg.val]; rw [hdyn_toNat]
                c0_hsteps_nogrp
                refine wp_join_state (ts := [i64, i64, i64])
                  (fun p : BitVec 64 × BitVec 64 × BitVec 64 => (p.1, p.2.1, p.2.2, ()))
                  (fun p m3 =>
                    p = (BitVec.ofNat 64 (msInitExtCap nc avail_dyn),
                         BitVec.ofNat 64 (msInitScrCap nc avail_dyn),
                         BitVec.ofNat 64 (msInitDyn nc avail_dyn)) ∧ m3 = m1)
                  ?_ ?_
                · rintro J632 p m3 ⟨rfl, hm3_eq⟩; subst m3
                  dsimp only [Blocks.get_here]
                  have hdyn_le := msInitDyn_le hav_dyn_ge
                  let rem := avail_dyn - msInitDyn nc avail_dyn
                  have hrem_ge40 : 40 ≤ rem := by omega
                  have har_fits := msInitArenas_le hav_dyn_ge
                  dsimp only at har_fits
                  have hw1 : 1 ≤ 2 * fullInitWp rem := by
                    have := msInitWp_ge_one hrem_ge40; omega
                  have hext_bd0 : msInitExtCap nc avail_dyn < dimacsBound := by
                    have := m7CalcExtCap_lt avail_dyn
                    unfold msInitExtCap; dsimp only; split
                    · unfold dimacsBound; omega
                    · exact this
                  have hscr_bd0 : msInitScrCap nc avail_dyn < dimacsBound := by
                    have := s9msCalcScrCap_lt avail_dyn
                    unfold msInitScrCap; dsimp only; split
                    · unfold dimacsBound; omega
                    · exact this
                  let c : MemShrinkCfg :=
                    { hdr := hdr_addr, avail := avail.toNat, mv := mv, max_vars := mx
                      bva_cap := mx - mv, nc := nc
                      arena_cap := 2 * fullInitAp rem, wcap := 2 * fullInitWp rem
                      delayed_cap := fullInitDelCap avail_dyn
                      red_cap := 2 * fullInitRp rem
                      extend_cap := msInitExtCap nc avail_dyn
                      scratch_cap := msInitScrCap nc avail_dyn
                      hbva := by omega
                      hmv := hmv_bd
                      hmaxv := hmx_lt
                      hnc := hnc_bd
                      harena := fullInitAp_lt
                      hwcap := fullInitWp_lt
                      hdel := fullInitDelCap_lt
                      hred := fullInitRp_lt
                      hext := hext_bd0
                      hscr := hscr_bd0
                      havail_fit := hfit_avail
                      hsize := by
                        have hsum_ar : 8 * fullInitAp rem + 8 * fullInitWp rem +
                            8 * fullInitRp rem + msInitDyn nc avail_dyn ≤ avail_dyn := har_fits
                        dsimp only [rem] at hsum_ar ⊢
                        unfold msInitDyn at hsum_ar ⊢
                        omega }
                  have hm1_w : (array64 (hdr_addr + 32) w140 ⋆
                      (array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                        cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆
                        region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m1 := by
                    have hm1_d := hm1; unfold dimacsState at hm1_d
                    exact Eq.mp (congrFun (by ac_rfl) m1) hm1_d
                  let w0 := w140.take 35
                  let w1 := (w140.drop 35).take 35
                  let w2 := (w140.drop 70).take 35
                  let w3 := (w140.drop 105).take 35
                  have lw0 : w0.length = 35 := by simp [w0, hw140]
                  have lw1 : w1.length = 35 := by simp [w1, hw140]
                  have lw2 : w2.length = 35 := by simp [w2, hw140]
                  have lw3 : w3.length = 35 := by simp [w3, hw140]
                  have hm1_a : (array64 (hdr_addr + 312) w1 ⋆
                      (array64 (hdr_addr + 32) w0 ⋆ array64 (hdr_addr + 592) w2 ⋆
                        array64 (hdr_addr + 872) w3 ⋆
                        array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                          cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆
                        region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m1 := by
                    have hm1_ht := array64_to_hdrTail4 hw140 hm1_w
                    have hm1_a0 := sep_mono (fun _ h => h.2.2.2.2) hm1_ht
                    exact Eq.mp (congrFun (by ac_rfl) m1) hm1_a0
                  c0_hstep
                  refine wp_store_array64 (base := hdr_addr + 312) (i := 17)
                    (by dsimp only [Arg.val]; rw [BitVec.add_assoc]; rfl) (by omega) hm1_a
                    fun m2 hm2 => ?_
                  have hm2_s : (array64 (hdr_addr + 872) w3 ⋆
                      (array64 (hdr_addr + 32) w0 ⋆
                        array64 (hdr_addr + 312) (w1.set 17 (BitVec.ofNat 64 c.delayed_cap)) ⋆
                        array64 (hdr_addr + 592) w2 ⋆
                        array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                          cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆
                        region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m2 :=
                    Eq.mp (congrFun (by ac_rfl) m2) hm2
                  c0_hstep
                  refine wp_store_array64 (base := hdr_addr + 872) (i := 4)
                    (by dsimp only [Arg.val]; rw [BitVec.add_assoc]; rfl) (by omega) hm2_s
                    fun m3 hm3 => ?_
                  c0_hstep
                  refine wp_store_array64 (base := hdr_addr + 872) (i := 7)
                    (by dsimp only [Arg.val]; rw [BitVec.add_assoc]; rfl) (by simp [lw3]) hm3
                    fun m4 hm4 => ?_
                  have hm4_ht : (hdrTail4 hdr_addr w0 (w1.set 17 (BitVec.ofNat 64 c.delayed_cap))
                      w2 ((w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7
                        (BitVec.ofNat 64 c.scratch_cap)) ⋆
                      (array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                        cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆
                        region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m4 := by
                    have hm4' : ((array64 (hdr_addr + 32) w0 ⋆
                        array64 (hdr_addr + 312) (w1.set 17 (BitVec.ofNat 64 c.delayed_cap)) ⋆
                        array64 (hdr_addr + 592) w2 ⋆
                        array64 (hdr_addr + 872) ((w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7
                          (BitVec.ofNat 64 c.scratch_cap))) ⋆
                        (array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                          cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                          bytes cnf_ptr cnfBytes ⋆
                          region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m4 :=
                      Eq.mp (congrFun (by ac_rfl) m4) hm4
                    exact sep_mono (fun _ h => ⟨lw0, by simp [lw1], lw2, by simp [lw3], h⟩) hm4'
                  have hrem_eq : BitVec.ofNat 64 avail_dyn -
                      BitVec.ofNat 64 (msInitDyn nc avail_dyn) = BitVec.ofNat 64 rem := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_sub_of_le (by
                      rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
                      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                      Nat.mod_eq_of_lt (by omega)]
                  c0_hsteps
                  apply wp_call_of_spec; apply hArenas; rw [m7InitArenasSpec_eq]
                  refine ⟨rfl, ?_, ?_, c.delayed_cap, c.extend_cap, c.scratch_cap,
                    w0, w1.set 17 (BitVec.ofNat 64 c.delayed_cap), w2,
                    (w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7 (BitVec.ofNat 64 c.scratch_cap),
                    array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                      cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                      bytes cnf_ptr cnfBytes ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R,
                    c.hdel, c.hext, c.hscr, ?_, ?_, ?_, hm4_ht, fun m5 hm5 => ?_⟩
                  · dsimp [vals, Arg.val]; rw [BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]; exact hmx_lt
                  · have := c.havail_fit
                    have := c.hsize
                    dsimp [vals, Arg.val]; rw [BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
                    change c.hdr.toNat + m7FixedBytes c.max_vars < 2 ^ 64
                    omega
                  · simp [lw1]
                  · simp [lw3]
                  · simp [lw3]
                  · have hmx_toNat :
                        (BitVec.ofNat 64 (s9msCalcMaxV avail.toNat mv nc (m7FixedBytes mv))).toNat =
                          mx := by
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
                    have hrem_toNat : (BitVec.ofNat 64 avail_dyn -
                        BitVec.ofNat 64 (msInitDyn nc avail_dyn)).toNat = rem := by
                      rw [hrem_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                    dsimp only [vals, Arg.val] at hm5
                    rw [hmx_toNat, hrem_toNat] at hm5
                    c0_hsteps
                    apply wp_call_of_spec; apply hInitHdr; rw [m7InitHdrSpec_eq]
                    refine ⟨?_, ?_,
                      m7ArenasW0 hdr_addr mx rem w0,
                      m7ArenasW1 hdr_addr mx rem c.delayed_cap c.extend_cap c.scratch_cap
                        (w1.set 17 (BitVec.ofNat 64 c.delayed_cap)),
                      m7ArenasW2 hdr_addr mx rem c.delayed_cap c.extend_cap c.scratch_cap w2,
                      m7ArenasW3 hdr_addr mx rem c.delayed_cap c.extend_cap c.scratch_cap
                        ((w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7
                          (BitVec.ofNat 64 c.scratch_cap)),
                      array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                        cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R,
                      hm5, fun m6 hm6 => ?_⟩
                    · dsimp [vals, Arg.val]; rw [hmv_tonat, hmx_toNat]; exact hmx_ge
                    · dsimp [vals, Arg.val]; rw [hmx_toNat]; exact hmx_lt
                    · dsimp only [vals, Arg.val] at hm6
                      rw [hmv_tonat, hmx_toNat] at hm6
                      have hm6_r : (region (hdr_addr + 1152) (avail.toNat - 1152) ⋆
                          (hdrTail4 hdr_addr
                            (m7HdrW0 c.mv fuel (m7ArenasW0 c.hdr c.max_vars rem w0))
                            (m7HdrW1 (m7ArenasW1 c.hdr c.max_vars rem c.delayed_cap c.extend_cap
                              c.scratch_cap (w1.set 17 (BitVec.ofNat 64 c.delayed_cap))))
                            (m7HdrW2 c.mv c.max_vars (m7ArenasW2 c.hdr c.max_vars rem c.delayed_cap
                              c.extend_cap c.scratch_cap w2))
                            (m7HdrW3 c.mv (m7ArenasW3 c.hdr c.max_vars rem c.delayed_cap
                              c.extend_cap c.scratch_cap
                              ((w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7
                                (BitVec.ofNat 64 c.scratch_cap)))) ⋆
                            array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                              cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                            bytes cnf_ptr cnfBytes ⋆ R)) m6 := Eq.mp (congrFun (by ac_rfl) m6) hm6
                      obtain ⟨a, ha⟩ := ms_region_to_mem c (cnf_ptr + BitVec.ofNat 64 j)
                        (BitVec.ofNat 64 nc) fuel hav1152 hm6_r
                      let s0 := msInitState c (cnf_ptr + BitVec.ofNat 64 j)
                        (BitVec.ofNat 64 nc) fuel a
                      obtain ⟨ht0, ht1, ht2, ht3⟩ := ms_hdrTail_eq c rem rfl rfl rfl
                        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) fuel a
                        lw0 lw1 lw2 lw3
                      rw [ht0, ht1, ht2, ht3,
                        show hdr_addr = c.hdr from rfl, ms_hdrTail4_words c s0] at ha
                      have hm6_s0 : (MemShrinkMem c s0 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m6 := by
                        rw [MemShrinkMem_eq]; unfold dimacsState
                        exact Eq.mp (congrFun (by ac_rfl) m6) ha
                      have hlen0 := ms_init_lengthsOk c hw1 (cnf_ptr + BitVec.ofNat 64 j)
                        (BitVec.ofNat 64 nc) fuel a
                      c0_hsteps
                      apply wp_call_of_spec; apply hZt1; rw [m7ZeroTables1Spec_eq]
                      refine ⟨c, s0, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen0, hm6_s0,
                        fun s1 m7 hsc1 hvals1 hlm1 hwvec1 hmin1 hgu1 hll1 hlen1 hm7 => ?_⟩
                      c0_hsteps
                      apply wp_call_of_spec; apply hZt2; rw [m7ZeroTables2Spec_eq]
                      refine ⟨c, s1, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen1, hm7,
                        fun s2 m8 hsc2 hvals2 hlm2 hwvec2 hmin2 hgu2 hll2 hmrk2 hlen2 hm8 => ?_⟩
                      c0_hsteps
                      have hsc := fullHdrScalarsEq_trans hsc2 hsc1
                      rw [fullHdrScalarsEq_eq] at hsc
                      rcases hsc with ⟨hd1, hd2, hcv, hun, har_l, hwk_l, hte, hpr, hcl, hfl_s, hcr,
                        htc, htl, hmc, hmcf, hoo, hin, hni, hnr, hnb, huf, hpb, hdm, hex_l, hpl,
                        hel⟩
                      dsimp only [s0, msInitState] at hd1 hd2 hcv hun har_l hwk_l hte hpr hcl hfl_s
                      dsimp only [s0, msInitState] at hcr htc htl hmc hmcf hoo hin hni hnr hnb huf
                      dsimp only [s0, msInitState] at hpb hdm hex_l hpl hel
                      refine hsucc c s2 j rest m8 rfl rfl hhdr hj_le hdrop
                        (m7_init_sparse_inv c hlen2 hmrk2 (hlm2.trans hlm1) (hll2.trans hll1) hex_l)
                        hcv hun hd1 hd2 har_l hwk_l hte hpr hcl hfl_s hcr htc htl hmc hmcf hoo
                        hin hni hnr hnb huf hpb hdm (hvals2.trans hvals1) (hwvec2.trans hwvec1)
                        hmrk2 (hlm2.trans hlm1) hex_l hpl hel (Eq.mp (congrFun (by ac_rfl) m8) hm8)
                · intro J632 hJ632
                  have hext_le : m7CalcExtCap avail_dyn ≤ 4194304 := m7CalcExtCap_le avail_dyn
                  have hscr_le : s9msCalcScrCap avail_dyn ≤ 8388608 := s9msCalcScrCap_le avail_dyn
                  have hdel_le : fullInitDelCap avail_dyn ≤ 4096 := by
                    unfold fullInitDelCap; split <;> omega
                  let dyn0 := fullInitDelCap avail_dyn * 12 + 4 * m7CalcExtCap avail_dyn +
                    4 * s9msCalcScrCap avail_dyn
                  have hd0_lt : dyn0 + (nc * 40 + 136) < 2 ^ 64 := by
                    dsimp [dyn0]; unfold dimacsBound at *; omega
                  have hsh2_ext : BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<<
                      ((BitVec.signExtend 64 2#32).toNat % 64) =
                      BitVec.ofNat 64 (4 * m7CalcExtCap avail_dyn) := by
                    rw [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide]
                    apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                  have hsh2_scr : BitVec.ofNat 64 (s9msCalcScrCap avail_dyn) <<<
                      ((BitVec.signExtend 64 2#32).toNat % 64) =
                      BitVec.ofNat 64 (4 * s9msCalcScrCap avail_dyn) := by
                    rw [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide]
                    apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                  have hdel_mul_bv : BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64 =
                      BitVec.ofNat 64 (fullInitDelCap avail_dyn * 12) := by
                    rw [show (12#64 : BitVec 64) = BitVec.ofNat 64 12 from rfl, ms_bv_ofNat_mul]
                  have hdyn0_bv : BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64 +
                      BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<< 2 +
                      BitVec.ofNat 64 (s9msCalcScrCap avail_dyn) <<< 2 = BitVec.ofNat 64 dyn0 := by
                    have he2 : BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<< 2 =
                        BitVec.ofNat 64 (4 * m7CalcExtCap avail_dyn) := by
                      simpa [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide] using
                        hsh2_ext
                    have hs2 : BitVec.ofNat 64 (s9msCalcScrCap avail_dyn) <<< 2 =
                        BitVec.ofNat 64 (4 * s9msCalcScrCap avail_dyn) := by
                      simpa [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide] using
                        hsh2_scr
                    rw [hdel_mul_bv, he2, hs2, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
                  have hav_d64 : avail_dyn < 2 ^ 64 := by omega
                  have hdel64 : fullInitDelCap avail_dyn < 2 ^ 64 := by omega
                  have hext64 : m7CalcExtCap avail_dyn < 2 ^ 64 := by omega
                  have hscr64 : s9msCalcScrCap avail_dyn < 2 ^ 64 := by omega
                  have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
                  have hsum64 : dyn0 + nc * 40 + 136 < 2 ^ 64 := by omega
                  c0_hsplit
                  · rw [Nat.mod_eq_of_lt hav_d64, Nat.mod_eq_of_lt hdel64, Nat.mod_eq_of_lt hext64,
                      Nat.mod_eq_of_lt hscr64, Nat.mod_eq_of_lt hnc64,
                      show BitVec.toNat 12 = 12 by decide, show BitVec.toNat 40 = 40 by decide,
                      show BitVec.toNat 136 = 136 by decide,
                      show (2 ^ OfNat.ofNat 2 : Nat) = 4 by decide,
                      Nat.mul_comm (m7CalcExtCap avail_dyn) 4,
                      Nat.mul_comm (s9msCalcScrCap avail_dyn) 4] at hc
                    change avail_dyn < (dyn0 + nc * 40 + 136) % 2 ^ 64 at hc
                    rw [Nat.mod_eq_of_lt hsum64] at hc
                    refine hJ632 (0#64, 0#64, BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64) m1
                      ⟨?_, rfl⟩
                    unfold msInitDyn msInitExtCap msInitScrCap; dsimp only
                    have hlt_d : avail_dyn < fullInitDelCap avail_dyn * 12 +
                        4 * m7CalcExtCap avail_dyn + 4 * s9msCalcScrCap avail_dyn +
                        nc * 40 + 136 := by
                      dsimp only [dyn0] at hc; omega
                    simp only [hlt_d, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
                    rw [hdel_mul_bv]
                  · rw [Nat.mod_eq_of_lt hav_d64, Nat.mod_eq_of_lt hdel64, Nat.mod_eq_of_lt hext64,
                      Nat.mod_eq_of_lt hscr64, Nat.mod_eq_of_lt hnc64,
                      show BitVec.toNat 12 = 12 by decide, show BitVec.toNat 40 = 40 by decide,
                      show BitVec.toNat 136 = 136 by decide,
                      show (2 ^ OfNat.ofNat 2 : Nat) = 4 by decide,
                      Nat.mul_comm (m7CalcExtCap avail_dyn) 4,
                      Nat.mul_comm (s9msCalcScrCap avail_dyn) 4] at hc
                    change ¬ avail_dyn < (dyn0 + nc * 40 + 136) % 2 ^ 64 at hc
                    rw [Nat.mod_eq_of_lt hsum64] at hc
                    refine hJ632 (BitVec.ofNat 64 (m7CalcExtCap avail_dyn),
                      BitVec.ofNat 64 (s9msCalcScrCap avail_dyn),
                      BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64 +
                        BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<< 2 +
                        BitVec.ofNat 64 (s9msCalcScrCap avail_dyn) <<< 2) m1 ⟨?_, rfl⟩
                    rw [hdyn0_bv]
                    unfold msInitDyn msInitExtCap msInitScrCap; dsimp only
                    have hge_d : ¬ avail_dyn < fullInitDelCap avail_dyn * 12 +
                        4 * m7CalcExtCap avail_dyn + 4 * s9msCalcScrCap avail_dyn +
                        nc * 40 + 136 := by
                      dsimp only [dyn0] at hc; omega
                    simp only [hge_d, ↓reduceIte]; rfl
              · intro J403 hJ403
                have h524 : BitVec.toNat (524288 : BitVec 64) = 524288 := by decide
                have hdyn_toNat : (BitVec.ofNat 64 avail_dyn).toNat = avail_dyn := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                have hdyn' : avail - BitVec.ofNat 64 (m7FixedBytes (s9msCalcMaxV avail.toNat mv nc
                    (m7FixedBytes mv))) - BitVec.ofNat 64 (m7TransBytes (s9msCalcMaxV avail.toNat
                    mv nc (m7FixedBytes mv))) = BitVec.ofNat 64 avail_dyn := hav_dyn_eq
                c0_hsplit
                · have hge : 524288 ≤ avail_dyn := by
                    dsimp only [lift2, Arg.val] at hc
                    rw [hdyn', hdyn_toNat, h524] at hc
                    exact hc
                  refine hJ403 4096#64 m1 ⟨?_, rfl⟩
                  unfold fullInitDelCap; split <;> first | rfl | omega
                · have hlt : avail_dyn < 524288 := by
                    dsimp only [lift2, Arg.val] at hc
                    rw [hdyn', hdyn_toNat, h524] at hc
                    omega
                  refine hJ403 8#64 m1 ⟨?_, rfl⟩
                  unfold fullInitDelCap; split <;> first | rfl | omega

theorem full_init_state_s9ms_wp (Γ : Env)
    (hM5 : EnvSpec Γ "full_init_state_m5" m7InitStateSpec) :
    ∀ a m Q X, m7InitStateSpec a m Q X →
      Func.wp Γ full_init_state_body a m Q X := by
  rintro ⟨p1, p2, p3, p4, p5, _⟩ m Q X hsp
  rw [envSpec_eq] at hM5
  unfold full_init_state_body; dsimp only [Func.wp]
  c0_hsteps
  exact wp_call_of_spec _ _ (hM5 _ _ _ _ hsp)

end InitWiring
end LeanQbe.T.Examples.Kissat.FullFidelityStep9MemShrink

end
