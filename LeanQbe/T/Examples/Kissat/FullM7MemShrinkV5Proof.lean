/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof0
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof
public import LeanQbe.T.Examples.Kissat.FullM6Hdr
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
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
# Kissat Memory-Shrink V5 Wiring Proofs (`FullM7MemShrinkV5Proof`)

M1-clean UNSAT-only proofs (`public section`, `0` `@[expose]`, `0` `import all`, `0` SAT proofs)
certifying `FullM7MemShrinkV5` with zero changes to frozen `FullM6Hdr*.lean` or
`FullM7MemShrinkProof*.lean`:
1. **V5 BVA Parity (`m7V5CalcMaxVSpec`, `full_calc_max_v_m7v5_wp`)**: fixes Cause B by
   removing the `(mv >> 1) + 16` cap (`cand = 4096ULL`) while accounting for `m7FixedBytes +
   m7TransBytes`.
2. **Definitional & Renamed Canonical Wiring**: reuses all `9` identical `FullM7MemShrink` WP
   proofs (`rfl`), transports `full_init_arenas_m7ms_wp` (`"full_init_ptrs"` via
   `FullM7BveGates.func_wp_of_rename`), proves `full_init_state_m7ms_wp` and
   `full_init_state_wrap_m7ms_wp` directly against `m7InitStateSpec`.
3. **Walk-Best Aliasing Guard (`full_compact_vars_m7ms_wp`, `m7msCompactVarsSpec`)**: proves
   Cause C variable compaction over `MemShrinkCompactMem` (preserving `fl'[nv] = fl[inv[nv]]`
   and keeping `pWalkBest`/`pSimSig` and `s.scratch.walk_best`/`sim_sig` completely untouched).
4. **Additive `MemShrinkM6HdrMem` & Framing (`0` Edits to `FullM6Hdr*.lean`)**: extends
   `MemShrinkMem` with `m6ExtMem (m6ExtAddr c.hdr) ext`, proves `memShrinkMem_to_region`,
   `memShrinkM6HdrMem_to_region`, `memShrinkM6Hdr_frame`, `m6_hdr_init_ms_wp`, and
   `full_m6_mem_init_ms_wp`.
5. **Closed `ModuleOk` & Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`)**:
   - `m7msStandalone_moduleOk : ModuleOk m7msEnv m7msStandaloneModule` (`14` fns + `1` extern).
   - `m7msM6_moduleOk : ModuleOk m7msM6Env m7msM6Module` (`16` fns + `1` extern).
   - `nv_m7ms_m6_mem_init_tiny` (`1,000 B < 3,456 B`) & `nv_m7ms_m6_mem_init_4k`
     (`(x1) ∧ (~x1)` on `6,400 B`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullParseInitHelpers
open LeanQbe.T.Examples.Kissat.Full.FullParseInitSpecs
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM7MemShrink hiding
  full_fill_u64_m7_body full_fill_u64_m7_wf full_trans_bytes_m7_body full_trans_bytes_m7_wf
open scoped FullArenaTactics FullParseInitTactics
open Kraken.Bedrock2.Test

/-! ## 1. V5 BVA Sizing (`m7V5CalcMaxVSpec` & `full_calc_max_v_m7v5_wp`) -/

section CalcMaxVV5

/-- V5 BVA headroom (`cand = 4096ULL`, Cause B fix) matching `full_calc_max_v_m7v5`. -/
def m7V5BvaCap (avail mv nc f0 : Nat) : Nat :=
  if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
    min 4096 (((avail - f0) - nc * 48 - 4096) / 2688)
  else 0

/-- Variable capacity limit selected by `full_calc_max_v_m7v5`. -/
def m7V5CalcMaxV (avail mv nc f0 : Nat) : Nat :=
  let cand := mv + m7V5BvaCap avail mv nc f0
  let need := m7FixedBytes cand + m7TransBytes cand
  if avail < need ∨ avail - need < nc * 40 + 136 then mv else cand

theorem m7V5BvaCap_eq (avail mv nc f0 : Nat) :
    m7V5BvaCap avail mv nc f0 =
      if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
        min 4096 (((avail - f0) - nc * 48 - 4096) / 2688)
      else 0 := by unfold m7V5BvaCap; rfl

theorem m7V5CalcMaxV_eq (avail mv nc f0 : Nat) :
    m7V5CalcMaxV avail mv nc f0 =
      let cand := mv + m7V5BvaCap avail mv nc f0
      let need := m7FixedBytes cand + m7TransBytes cand
      if avail < need ∨ avail - need < nc * 40 + 136 then mv else cand := by
  unfold m7V5CalcMaxV; rfl

theorem m7V5BvaCap_le (avail mv nc f0 : Nat) : m7V5BvaCap avail mv nc f0 ≤ 4096 := by
  unfold m7V5BvaCap; split <;> omega

private theorem m7V5BvaCap_zero1 {avail mv nc f0 : Nat}
    (h : ¬ nc * 48 + 8192 < avail - f0) : m7V5BvaCap avail mv nc f0 = 0 := by
  unfold m7V5BvaCap; simp [h]

private theorem m7V5BvaCap_zero2 {avail mv nc f0 : Nat}
    (h : ¬ 2 ≤ mv) : m7V5BvaCap avail mv nc f0 = 0 := by
  unfold m7V5BvaCap; simp [h]

theorem m7V5CalcMaxV_ge {avail mv nc f0 : Nat} : mv ≤ m7V5CalcMaxV avail mv nc f0 := by
  unfold m7V5CalcMaxV; dsimp only
  by_cases h : avail < m7FixedBytes (mv + m7V5BvaCap avail mv nc f0) +
      m7TransBytes (mv + m7V5BvaCap avail mv nc f0) ∨
      avail - (m7FixedBytes (mv + m7V5BvaCap avail mv nc f0) +
        m7TransBytes (mv + m7V5BvaCap avail mv nc f0)) < nc * 40 + 136
  · simp [h]
  · simp only [h, ↓reduceIte]; omega

theorem m7V5CalcMaxV_lt {avail mv nc f0 : Nat} (hmv : mv < dimacsBound) :
    m7V5CalcMaxV avail mv nc f0 < 2 * dimacsBound := by
  have hb := m7V5BvaCap_le avail mv nc f0
  unfold m7V5CalcMaxV dimacsBound at *; dsimp only
  by_cases h : avail < m7FixedBytes (mv + m7V5BvaCap avail mv nc f0) +
      m7TransBytes (mv + m7V5BvaCap avail mv nc f0) ∨
      avail - (m7FixedBytes (mv + m7V5BvaCap avail mv nc f0) +
        m7TransBytes (mv + m7V5BvaCap avail mv nc f0)) < nc * 40 + 136
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

theorem m7V5CalcMaxV_fits {avail mv nc f0 : Nat}
    (hbase : m7FixedBytes mv + m7TransBytes mv + nc * 40 + 136 ≤ avail) :
    m7FixedBytes (m7V5CalcMaxV avail mv nc f0) +
      m7TransBytes (m7V5CalcMaxV avail mv nc f0) + nc * 40 + 136 ≤ avail := by
  unfold m7V5CalcMaxV; dsimp only
  by_cases h : avail < m7FixedBytes (mv + m7V5BvaCap avail mv nc f0) +
      m7TransBytes (mv + m7V5BvaCap avail mv nc f0) ∨
      avail - (m7FixedBytes (mv + m7V5BvaCap avail mv nc f0) +
        m7TransBytes (mv + m7V5BvaCap avail mv nc f0)) < nc * 40 + 136
  · simp only [h, ↓reduceIte]; exact hbase
  · simp only [h, ↓reduceIte]; omega

/-- Contract for V5 `full_calc_max_v_m7v5` (`cand = 4096ULL`). -/
def m7V5CalcMaxVSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (avail, mv, nc, f0, _) m Q _ =>
    mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧ f0.toNat ≤ avail.toNat ∧
    Q (BitVec.ofNat 64 (m7V5CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m

theorem m7V5CalcMaxVSpec_eq (avail mv nc f0 : BitVec 64) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    m7V5CalcMaxVSpec (avail, mv, nc, f0, ()) m Q X =
      (mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧ f0.toNat ≤ avail.toNat ∧
       Q (BitVec.ofNat 64 (m7V5CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) := by rfl

private def m7V5CalcMaxVTailExpr (avail mv nc bva : Val i64) : Expr Val Cont [i64] :=
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

private def m7V5CalcMaxVCapMinExpr (nc rem : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
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
        args := (Arg.imm 4096, Arg.var p.fst, ()) } fun p_10 =>
    Expr.jnz (Arg.var p_10.fst)
      (Expr.jump Js.fst (Arg.imm 4096, ()))
      (Expr.jump Js.fst (Arg.var p.fst, ()))

private def m7V5CalcMaxVBvaExpr (mv nc rem : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
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
       (m7V5CalcMaxVCapMinExpr nc rem J)
       (Expr.jump J (Arg.imm 0, ())))
    (Expr.jump J (Arg.imm 0, ()))

private theorem m7V5CalcMaxV_body_eq (avail mv nc f0 : Val i64) :
    full_calc_max_v_m7v5_body Val Cont (avail, mv, nc, f0, ()) =
      Expr.let_
        { sig := [i64, i64], code := OpCode.sub i64,
          args := (Arg.var avail, Arg.var f0, ()) } fun p_1 =>
      Expr.group (sig := [[i64]])
        (fun _ => Blocks.cons (fun (p_2 : Tup Val [i64]) =>
          m7V5CalcMaxVTailExpr avail mv nc p_2.fst) Blocks.nil)
        (fun Js => m7V5CalcMaxVBvaExpr mv nc p_1.fst Js.fst) := rfl

private theorem m7V5CalcMaxVTail_wp (Γ : Env)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hq : Q (BitVec.ofNat 64 (m7V5CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (m7V5CalcMaxVTailExpr avail mv nc
      (BitVec.ofNat 64 (m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat))) m := by
  rw [envSpec_eq] at hFixed hTrans
  unfold m7V5CalcMaxVTailExpr
  c0_hsteps
  let cand := mv.toNat + m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat
  have hcand_lt : cand < 2 * dimacsBound := by
    have := m7V5BvaCap_le avail.toNat mv.toNat nc.toNat f0.toNat
    unfold dimacsBound at *; omega
  have hcand_bv : mv + BitVec.ofNat 64 (m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) =
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
    have hres : m7V5CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat = mv.toNat := by
      unfold m7V5CalcMaxV; simp [hlt, need, cand]
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
      have hres : m7V5CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat = mv.toNat := by
        unfold m7V5CalcMaxV; simp [hlt2, need, cand]
      simpa [hres] using hq
    · c0_hsteps
      rw [show BitVec.toNat 40 = 40 from by decide,
        show BitVec.toNat 136 = 136 from by decide] at hc
      have hge2 : ¬avail.toNat - need < nc.toNat * 40 + 136 := by
        unfold dimacsBound at hnc
        rw [hsub_bv2, Nat.mod_eq_of_lt (by omega)] at hc
        exact hc
      have hres : m7V5CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat = cand := by
        unfold m7V5CalcMaxV; simp [show ¬avail.toNat < need by omega, hge2, cand, need]
      simpa [hres, hcand_bv] using hq

private theorem m7V5CalcMaxVCapMin_wp (Γ : Env) (Q : Post [i64]) (X : XPost)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (J : Cont [i64])
    (hmv2 : 2 ≤ mv.toNat) (hnc : nc.toNat < dimacsBound)
    (hrem_gt : nc.toNat * 48 + 8192 < avail.toNat - f0.toNat)
    (hrem_eq : (avail - f0).toNat = avail.toNat - f0.toNat)
    (hJ : J (BitVec.ofNat 64 (m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (m7V5CalcMaxVCapMinExpr nc (avail - f0) J) m := by
  unfold m7V5CalcMaxVCapMinExpr
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
  have hfin : m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat =
      min 4096 (((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688) := by
    unfold m7V5BvaCap; simp [hmv2, hrem_gt]
  have hdiv_eq : ((avail - f0 - nc * 48 - 4096) / 2688).toNat =
      ((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688 := by
    rw [hmb, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hdiv_lt
  refine wp_join_state1 (α := Unit)
    (proj := fun _ => BitVec.ofNat 64 (m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat))
    (Inv := fun _ m'' => m'' = m) ?_ ?_
  · rintro _ _ m'' hm''; subst m''
    c0_hsteps
    exact hJ
  · intro J3 hJ3; c0_hsplit
    · c0_hsteps
      rw [show BitVec.toNat 4096 = 4096 from by decide, hdiv_eq] at hc
      have hlt : 4096 < ((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688 := hc
      rw [show (4096 : BitVec 64) =
        BitVec.ofNat 64 (m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) from by
        rw [hfin, Nat.min_eq_left (Nat.le_of_lt hlt)]; rfl]
      exact hJ3 () m rfl
    · c0_hsteps
      rw [show BitVec.toNat 4096 = 4096 from by decide, hdiv_eq] at hc
      have hle : ((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688 ≤ 4096 :=
        Nat.le_of_not_lt hc
      have h_lhs : (avail - f0 - nc * 48 - 4096) / 2688 =
          BitVec.ofNat 64 (m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) := by
        rw [hmb, hfin, Nat.min_eq_right hle]
      rw [h_lhs]; exact hJ3 () m rfl

private theorem m7V5CalcMaxVBva_wp (Γ : Env) (Q : Post [i64]) (X : XPost)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (J : Cont [i64])
    (_hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound) (hf0 : f0.toNat ≤ avail.toNat)
    (hJ : J (BitVec.ofNat 64 (m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (m7V5CalcMaxVBvaExpr mv nc (avail - f0) J) m := by
  unfold m7V5CalcMaxVBvaExpr
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
      exact m7V5CalcMaxVCapMin_wp Γ Q X avail mv nc f0 m J hmv2 hnc
        (of_decide_eq_true hlt) hrem_eq hJ
    · intro h
      have hge : (nc * 48 + 8192).ult (avail - f0) = false := h
      rw [BitVec.ult, hbound_nat, hrem_eq] at hge
      have hle : ¬ nc.toNat * 48 + 8192 < avail.toNat - f0.toNat := by
        simpa using of_decide_eq_false hge
      c0_hsteps
      rw [m7V5BvaCap_zero1 hle] at hJ
      exact hJ
  · c0_hsteps
    rw [show (2 : BitVec 64).toNat = 2 from by decide] at hc
    rw [m7V5BvaCap_zero2 hc] at hJ
    exact hJ

theorem full_calc_max_v_m7v5_wp (Γ : Env)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec) :
    ∀ a m Q X, m7V5CalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_m7v5_body a m Q X := by
  rintro ⟨avail, mv, nc, f0, _⟩ m Q X ⟨hmv, hnc, hf0, hq⟩
  dsimp only [Func.wp]
  rw [m7V5CalcMaxV_body_eq]
  c0_hsteps_nogrp
  refine wp_join_state1 (α := Unit)
    (proj := fun _ => BitVec.ofNat 64 (m7V5BvaCap avail.toNat mv.toNat nc.toNat f0.toNat))
    (Inv := fun _ m' => m' = m) ?_ ?_
  · rintro _ _ m' hm'; subst m'
    exact m7V5CalcMaxVTail_wp Γ hFixed hTrans avail mv nc f0 m Q X hmv hnc hq
  · intro J hJ
    exact m7V5CalcMaxVBva_wp Γ Q X avail mv nc f0 m J hmv hnc hf0 (hJ () m rfl)

end CalcMaxVV5

/-! ## 2. `9` Definitional Reuses, Renamed `init_arenas`, `init_state` & Wrapper -/

section InitWiring

theorem full_fill_u64_m7ms_wp (Γ : Env) :
    ∀ a m Q X, m7FillU64Spec a m Q X → Func.wp Γ full_fill_u64_m7_body a m Q X :=
  full_fill_u64_m7_wp Γ

theorem full_zero_tables1_m7ms_wp (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec) :
    ∀ a m Q X, m7ZeroTables1Spec a m Q X → Func.wp Γ full_zero_tables1_m7ms_body a m Q X :=
  full_zero_tables1_m7_wp Γ hFill

theorem full_zero_tables2_m7ms_wp (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec) :
    ∀ a m Q X, m7ZeroTables2Spec a m Q X → Func.wp Γ full_zero_tables2_m7ms_body a m Q X :=
  full_zero_tables2_m7_wp Γ hFill

theorem full_fixed_bytes_m7ms_wp (Γ : Env) :
    ∀ a m Q X, m7FixedBytesSpec a m Q X → Func.wp Γ full_fixed_bytes_m7ms_body a m Q X :=
  full_fixed_bytes_m7_wp Γ

theorem full_trans_bytes_m7ms_wp (Γ : Env) :
    ∀ a m Q X, m7TransBytesSpec a m Q X → Func.wp Γ full_trans_bytes_m7_body a m Q X :=
  full_trans_bytes_m7_wp Γ

theorem full_init_ptrs_m7ms_wp (Γ : Env) :
    ∀ a m Q X, m7InitPtrsSpec a m Q X → Func.wp Γ full_init_ptrs_m7ms_body a m Q X :=
  full_init_ptrs_m7_wp Γ

theorem full_init_hdr_m7ms_wp (Γ : Env) :
    ∀ a m Q X, m7InitHdrSpec a m Q X → Func.wp Γ full_init_hdr_m7ms_body a m Q X :=
  full_init_hdr_m7_wp Γ

theorem full_calc_ext_cap_m7ms_wp (Γ : Env) :
    ∀ a m Q X, m7CalcExtCapSpec a m Q X → Func.wp Γ full_calc_ext_cap_m7ms_body a m Q X :=
  full_calc_ext_cap_m7_wp Γ

theorem full_calc_scr_cap_m7ms_wp (Γ : Env) :
    ∀ a m Q X, m7CalcScrCapSpec a m Q X → Func.wp Γ full_calc_scr_cap_m7ms_body a m Q X :=
  full_calc_scr_cap_m7_wp Γ

private def msArenasRename : Sym → Sym
  | "full_init_ptrs_m7" => "full_init_ptrs"
  | s => s

local macro "ms_rename_step" : tactic =>
  `(tactic| (first
    | exact FullM7BveGates.ExprRename.jump
    | exact FullM7BveGates.ExprRename.ret
    | exact FullM7BveGates.ExprRename.hlt
    | exact FullM7BveGates.BlocksRename.nil
    | (apply FullM7BveGates.ExprRename.let_; intro _)
    | (apply FullM7BveGates.ExprRename.load; intro _)
    | apply FullM7BveGates.ExprRename.store
    | (apply FullM7BveGates.ExprRename.call _ _ rfl; intro _)
    | apply FullM7BveGates.ExprRename.jnz
    | (apply FullM7BveGates.ExprRename.group <;> intro _)
    | (apply FullM7BveGates.BlocksRename.cons; intro _)))

theorem full_init_arenas_m7ms_wp (Γ : Env)
    (hPtrs : EnvSpec Γ "full_init_ptrs" m7InitPtrsSpec) :
    ∀ a m Q X, m7InitArenasSpec a m Q X → Func.wp Γ full_init_arenas_m7ms_body a m Q X := by
  have hPtrs' : EnvSpec (fun f as bs => Γ (msArenasRename f) as bs)
      "full_init_ptrs_m7" m7InitPtrsSpec := by
    simpa [envSpec_eq, msArenasRename] using hPtrs
  refine FullM7BveGates.func_wp_of_rename msArenasRename full_init_arenas_m7_body
    full_init_arenas_m7ms_body ?_ Γ
    (full_init_arenas_m7_wp (fun f as bs => Γ (msArenasRename f) as bs) hPtrs')
  intro _; dsimp only [full_init_arenas_m7_body, full_init_arenas_m7ms_body]
  repeat ms_rename_step

private def msInitExtCap (nc rem : Nat) : Nat :=
  let dyn := fullInitDelCap rem * 12 + 4 * m7CalcExtCap rem + 4 * m7CalcScrCap rem
  if rem < dyn + nc * 40 + 136 then 0 else m7CalcExtCap rem

private def msInitScrCap (nc rem : Nat) : Nat :=
  let dyn := fullInitDelCap rem * 12 + 4 * m7CalcExtCap rem + 4 * m7CalcScrCap rem
  if rem < dyn + nc * 40 + 136 then 0 else m7CalcScrCap rem

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
        MemShrinkCfg.pPos_eq, MemShrinkCfg.pHeap_eq, MemShrinkCfg.pTmp_eq, MemShrinkCfg.pTrailPos_eq,
        MemShrinkCfg.pTrail_eq, MemShrinkCfg.pReason_eq, MemShrinkCfg.pLevel_eq, BitVec.add_assoc,
        ← BitVec.ofNat_add]; congr 2; omega
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
      simp only [MemShrinkCfg.pTarjanReach_eq, MemShrinkCfg.pTarjanMark_eq, MemShrinkCfg.pWorkStk2_eq,
        MemShrinkCfg.pWorkStk1_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
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

theorem full_init_state_m7ms_wp (Γ : Env)
    (hHdr : EnvSpec Γ "kissat_parse_header" kissatParseHeaderSpec)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (hMaxV : EnvSpec Γ "full_calc_max_v" m7V5CalcMaxVSpec)
    (hExt : EnvSpec Γ "full_calc_ext_cap_m5" m7CalcExtCapSpec)
    (hScr : EnvSpec Γ "full_calc_scr_cap_m5" m7CalcScrCapSpec)
    (hArenas : EnvSpec Γ "full_init_arenas" m7InitArenasSpec)
    (hInitHdr : EnvSpec Γ "full_init_hdr" m7InitHdrSpec)
    (hZt1 : EnvSpec Γ "full_zero_tables1" m7ZeroTables1Spec)
    (hZt2 : EnvSpec Γ "full_zero_tables2" m7ZeroTables2Spec) :
    ∀ a m Q X, m7InitStateSpec a m Q X → Func.wp Γ full_init_state_m7ms_body a m Q X := by
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
  unfold full_init_state_m7ms_body; dsimp only [Func.wp]
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
          let mx := m7V5CalcMaxV avail.toNat mv nc (m7FixedBytes mv)
          have hmx_ge : mv ≤ mx := m7V5CalcMaxV_ge
          have hmx_lt : mx < 2 * dimacsBound := m7V5CalcMaxV_lt hmv_bd
          have hmx_fits : m7FixedBytes mx + m7TransBytes mx + nc * 40 + 136 ≤ avail.toNat :=
            m7V5CalcMaxV_fits hbase
          have hfx_lt64 : m7FixedBytes mv < 2 ^ 64 := by omega
          apply wp_call_of_spec; apply hMaxV; rw [m7V5CalcMaxVSpec_eq]
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
                have hav_dyn' : avail - BitVec.ofNat 64 (m7FixedBytes (m7V5CalcMaxV avail.toNat mv
                    nc (m7FixedBytes mv))) - BitVec.ofNat 64 (m7TransBytes (m7V5CalcMaxV
                    avail.toNat mv nc (m7FixedBytes mv))) = BitVec.ofNat 64 avail_dyn :=
                  hav_dyn_eq
                apply wp_call_of_spec; apply hExt; rw [m7CalcExtCapSpec_eq]
                dsimp only [vals, lift2, Arg.val]; rw [hav_dyn', hdyn_toNat]
                apply wp_call_of_spec; apply hScr; rw [m7CalcScrCapSpec_eq]
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
                    have := m7CalcScrCap_lt avail_dyn
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
                        (BitVec.ofNat 64 (m7V5CalcMaxV avail.toNat mv nc (m7FixedBytes mv))).toNat =
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
                  have hscr_le : m7CalcScrCap avail_dyn ≤ 1048576 := m7CalcScrCap_le avail_dyn
                  have hdel_le : fullInitDelCap avail_dyn ≤ 4096 := by
                    unfold fullInitDelCap; split <;> omega
                  let dyn0 := fullInitDelCap avail_dyn * 12 + 4 * m7CalcExtCap avail_dyn +
                    4 * m7CalcScrCap avail_dyn
                  have hd0_lt : dyn0 + (nc * 40 + 136) < 2 ^ 64 := by
                    dsimp [dyn0]; unfold dimacsBound at *; omega
                  have hsh2_ext : BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<<
                      ((BitVec.signExtend 64 2#32).toNat % 64) =
                      BitVec.ofNat 64 (4 * m7CalcExtCap avail_dyn) := by
                    rw [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide]
                    apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                  have hsh2_scr : BitVec.ofNat 64 (m7CalcScrCap avail_dyn) <<<
                      ((BitVec.signExtend 64 2#32).toNat % 64) =
                      BitVec.ofNat 64 (4 * m7CalcScrCap avail_dyn) := by
                    rw [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide]
                    apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                  have hdel_mul_bv : BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64 =
                      BitVec.ofNat 64 (fullInitDelCap avail_dyn * 12) := by
                    rw [show (12#64 : BitVec 64) = BitVec.ofNat 64 12 from rfl, ms_bv_ofNat_mul]
                  have hdyn0_bv : BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64 +
                      BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<< 2 +
                      BitVec.ofNat 64 (m7CalcScrCap avail_dyn) <<< 2 = BitVec.ofNat 64 dyn0 := by
                    have he2 : BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<< 2 =
                        BitVec.ofNat 64 (4 * m7CalcExtCap avail_dyn) := by
                      simpa [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide] using
                        hsh2_ext
                    have hs2 : BitVec.ofNat 64 (m7CalcScrCap avail_dyn) <<< 2 =
                        BitVec.ofNat 64 (4 * m7CalcScrCap avail_dyn) := by
                      simpa [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide] using
                        hsh2_scr
                    rw [hdel_mul_bv, he2, hs2, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
                  have hav_d64 : avail_dyn < 2 ^ 64 := by omega
                  have hdel64 : fullInitDelCap avail_dyn < 2 ^ 64 := by omega
                  have hext64 : m7CalcExtCap avail_dyn < 2 ^ 64 := by omega
                  have hscr64 : m7CalcScrCap avail_dyn < 2 ^ 64 := by omega
                  have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
                  have hsum64 : dyn0 + nc * 40 + 136 < 2 ^ 64 := by omega
                  c0_hsplit
                  · rw [Nat.mod_eq_of_lt hav_d64, Nat.mod_eq_of_lt hdel64, Nat.mod_eq_of_lt hext64,
                      Nat.mod_eq_of_lt hscr64, Nat.mod_eq_of_lt hnc64,
                      show BitVec.toNat 12 = 12 by decide, show BitVec.toNat 40 = 40 by decide,
                      show BitVec.toNat 136 = 136 by decide,
                      show (2 ^ OfNat.ofNat 2 : Nat) = 4 by decide,
                      Nat.mul_comm (m7CalcExtCap avail_dyn) 4,
                      Nat.mul_comm (m7CalcScrCap avail_dyn) 4] at hc
                    change avail_dyn < (dyn0 + nc * 40 + 136) % 2 ^ 64 at hc
                    rw [Nat.mod_eq_of_lt hsum64] at hc
                    refine hJ632 (0#64, 0#64, BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64) m1
                      ⟨?_, rfl⟩
                    unfold msInitDyn msInitExtCap msInitScrCap; dsimp only
                    have hlt_d : avail_dyn < fullInitDelCap avail_dyn * 12 +
                        4 * m7CalcExtCap avail_dyn + 4 * m7CalcScrCap avail_dyn +
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
                      Nat.mul_comm (m7CalcScrCap avail_dyn) 4] at hc
                    change ¬ avail_dyn < (dyn0 + nc * 40 + 136) % 2 ^ 64 at hc
                    rw [Nat.mod_eq_of_lt hsum64] at hc
                    refine hJ632 (BitVec.ofNat 64 (m7CalcExtCap avail_dyn),
                      BitVec.ofNat 64 (m7CalcScrCap avail_dyn),
                      BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64 +
                        BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<< 2 +
                        BitVec.ofNat 64 (m7CalcScrCap avail_dyn) <<< 2) m1 ⟨?_, rfl⟩
                    rw [hdyn0_bv]
                    unfold msInitDyn msInitExtCap msInitScrCap; dsimp only
                    have hge_d : ¬ avail_dyn < fullInitDelCap avail_dyn * 12 +
                        4 * m7CalcExtCap avail_dyn + 4 * m7CalcScrCap avail_dyn +
                        nc * 40 + 136 := by
                      dsimp only [dyn0] at hc; omega
                    simp only [hge_d, ↓reduceIte]; rfl
              · intro J403 hJ403
                have h524 : BitVec.toNat (524288 : BitVec 64) = 524288 := by decide
                have hdyn_toNat : (BitVec.ofNat 64 avail_dyn).toNat = avail_dyn := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                have hdyn' : avail - BitVec.ofNat 64 (m7FixedBytes (m7V5CalcMaxV avail.toNat mv nc
                    (m7FixedBytes mv))) - BitVec.ofNat 64 (m7TransBytes (m7V5CalcMaxV avail.toNat
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

theorem full_init_state_wrap_m7ms_wp (Γ : Env)
    (hM5 : EnvSpec Γ "full_init_state_m5" m7InitStateSpec) :
    ∀ a m Q X, m7InitStateSpec a m Q X →
      Func.wp Γ full_init_state_wrap_m7ms_body a m Q X := by
  rintro ⟨p1, p2, p3, p4, p5, _⟩ m Q X hsp
  rw [envSpec_eq] at hM5
  unfold full_init_state_wrap_m7ms_body; dsimp only [Func.wp]
  c0_hsteps
  exact wp_call_of_spec _ _ (hM5 _ _ _ _ hsp)

end InitWiring

/-! ## 3. `full_compact_vars_m7ms` Over `MemShrinkMem` (`0` `walk_best` Aliasing) -/

section CompactVarsMs

/-- `MemShrinkCfg` compatibility across variable compaction (`mv` may decrease, pointers fixed). -/
structure MemShrinkCfgCompat (c c' : MemShrinkCfg) : Prop where
  hdr : c'.hdr = c.hdr
  avail : c'.avail = c.avail
  mv_le : c'.mv ≤ c.mv
  max_vars : c'.max_vars = c.max_vars
  nc : c'.nc = c.nc
  arena_cap : c'.arena_cap = c.arena_cap
  wcap : c'.wcap = c.wcap
  delayed_cap : c'.delayed_cap = c.delayed_cap
  red_cap : c'.red_cap = c.red_cap
  extend_cap : c'.extend_cap = c.extend_cap
  scratch_cap : c'.scratch_cap = c.scratch_cap

theorem MemShrinkCfgCompat.refl (c : MemShrinkCfg) : MemShrinkCfgCompat c c :=
  ⟨rfl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Shrink `mv` to `mv' ≤ c.mv` and grow `bva_cap` to `c.max_vars - mv'` cleanly. -/
def memShrinkCfgShrinkMv (c : MemShrinkCfg) (mv' : Nat) (hle : mv' ≤ c.mv) : MemShrinkCfg where
  hdr := c.hdr
  avail := c.avail
  mv := mv'
  max_vars := c.max_vars
  bva_cap := c.max_vars - mv'
  nc := c.nc
  arena_cap := c.arena_cap
  wcap := c.wcap
  delayed_cap := c.delayed_cap
  red_cap := c.red_cap
  extend_cap := c.extend_cap
  scratch_cap := c.scratch_cap
  hbva := by have := c.hbva; omega
  hmv := Nat.lt_of_le_of_lt hle c.hmv
  hmaxv := c.hmaxv
  hnc := c.hnc
  harena := c.harena
  hwcap := c.hwcap
  hdel := c.hdel
  hred := c.hred
  hext := c.hext
  hscr := c.hscr
  havail_fit := c.havail_fit
  hsize := c.hsize

theorem MemShrinkCfgCompat.shrinkMv (c : MemShrinkCfg) (mv' : Nat) (hle : mv' ≤ c.mv) :
    MemShrinkCfgCompat c (memShrinkCfgShrinkMv c mv' hle) :=
  ⟨rfl, rfl, hle, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Transient pool view borrowing `pWorkStk2` as `array (t := i32) c.pWorkStk2 ws2`
while leaving all other 6 transient slices (`wsort`, `work_stk1`, `tarjan_*`, `repr/walk_vals`,
`sim_sig/walk_best`) untouched. -/
def MemShrinkTransWithWs2 (c : MemShrinkCfg) (ws2 : List (BitVec 32)) : Mem 64 → Prop :=
  region c.pWsort (8 * c.max_vars) ⋆
  region c.pWorkStk1 (8 * c.max_vars) ⋆
  array (t := i32) c.pWorkStk2 ws2 ⋆
  region c.pTarjanMark (8 * c.max_vars) ⋆
  region c.pTarjanReach (8 * c.max_vars) ⋆
  region c.pRepr (8 * c.max_vars) ⋆
  region c.pSimSig (8 * c.max_vars)

/-- `MemShrinkMem` with `pWorkStk2` explicitly exposed as `inv : List (BitVec 32)`. -/
def MemShrinkCompactMem (c : MemShrinkCfg) (s : FullState) (ws2 : List (BitVec 32)) :
    Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
  MemShrinkResArrays c s ⋆
  MemShrinkLitMark c s ⋆
  MemShrinkTransWithWs2 c ws2 ⋆
  region c.pSlack c.slack

theorem memShrinkCompactMem_to_mem {c : MemShrinkCfg} {s : FullState} {ws2 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (hws2 : ws2.length = 2 * c.max_vars)
    (hm : (MemShrinkCompactMem c s ws2 ⋆ R) m) : (MemShrinkMem c s ⋆ R) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  rw [MemShrinkMem_eq, MemShrinkTransRegions_eq]
  unfold MemShrinkCompactMem MemShrinkTransWithWs2 at hm
  have hm0 : (array (t := i32) c.pWorkStk2 ws2 ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆ MemShrinkResArrays c s ⋆
        MemShrinkLitMark c s ⋆ region c.pWsort (8 * c.max_vars) ⋆
        region c.pWorkStk1 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
        region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars) ⋆ region c.pSlack c.slack ⋆ R)) m := sep_ac hm
  have h1 : (region c.pWorkStk2 (8 * c.max_vars) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆ MemShrinkResArrays c s ⋆
        MemShrinkLitMark c s ⋆ region c.pWsort (8 * c.max_vars) ⋆
        region c.pWorkStk1 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
        region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars) ⋆ region c.pSlack c.slack ⋆ R)) m :=
    sep_mono (fun _ ha => by
      have hreg := i32_exact_to_reg (xs := ws2) (by rw [hws2]; omega) ha
      simpa [hws2, show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega] using hreg) hm0
  exact sep_ac h1

theorem memShrinkMem_borrow_ws2 {c : MemShrinkCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (MemShrinkMem c s ⋆ R) m) :
    ∃ ws2 : List (BitVec 32), ws2.length = 2 * c.max_vars ∧
      (MemShrinkCompactMem c s ws2 ⋆ R) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  rw [MemShrinkMem_eq, MemShrinkTransRegions_eq] at hm
  have h0 : (region c.pWorkStk2 (8 * c.max_vars) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆ MemShrinkResArrays c s ⋆
        MemShrinkLitMark c s ⋆ region c.pWsort (8 * c.max_vars) ⋆
        region c.pWorkStk1 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
        region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars) ⋆ region c.pSlack c.slack ⋆ R)) m := sep_ac hm
  have h1 := sep_mono (fun _ (r : region c.pWorkStk2 (8 * c.max_vars) _) =>
    reg_to_i32_exact (n := 2 * c.max_vars) (by omega)
      (by simpa [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega] using r)) h0
  obtain ⟨ws2, h2⟩ := sep_ex_l.mp h1
  obtain ⟨hl, h3⟩ := sep_pure_l.mp h2
  unfold MemShrinkCompactMem MemShrinkTransWithWs2
  exact ⟨ws2, hl, sep_ac h3⟩

/-- Specification of `full_compact_vars_m7ms`: rewrites active resident arrays using `inv`
in `pWorkStk2`, preserves `fl'[nv] = fl[inv[nv]]`, clears dead tails and `values[0..2*old_cv)`,
and leaves `pSimSig/pWalkBest` (`s'.scratch.walk_best = s.scratch.walk_best`, `sim_sig`) untouched. -/
def m7msCompactVarsSpec : Spec [i64, i64, i64] [] :=
  fun (h, old_cv, ncv, _) m Q _ =>
    ∃ (c : MemShrinkCfg) (s : FullState) (inv : List (BitVec 32)) (R : Mem 64 → Prop),
      h = c.hdr ∧ MemShrinkLengthsOk c s ∧ old_cv.toNat = s.core.cur_vars ∧
      ncv.toNat ≤ old_cv.toNat ∧ inv.length = 2 * c.max_vars ∧
      (∀ nv < ncv.toNat, (inv[nv]?.getD 0#32).toNat < old_cv.toNat) ∧
      (MemShrinkCompactMem c s inv ⋆ R) m ∧
      ∀ (c' : MemShrinkCfg) (vals' lvl' rsns' : List (BitVec 32))
        (ft0' fd0' : BitVec 32) (sc' : FullScratch) (vals8' : List (BitVec 8)) (m' : Mem 64),
        let s' : FullState :=
          { core := { s.core with vals := vals8', flags := vals', lvl := lvl', rsns := rsns',
                                  frame_trail := s.core.frame_trail.set 0 ft0',
                                  frame_dec := s.core.frame_dec.set 0 fd0',
                                  trail_end := 0, propagated := 0, cur_level := 0,
                                  unflushed := 0#64, confl_ref := 0xFFFFFFFF#64,
                                  confl_type := 0#64, cur_vars := ncv.toNat, unassigned := ncv }
            scratch := sc' }
        MemShrinkCfgCompat c c' → c'.mv ≤ ncv.toNat → (ncv.toNat < c.mv → c'.mv = ncv.toNat) →
        MemShrinkLengthsOk c' s' → ft0' = 0#32 →
        (∀ l < 2 * old_cv.toNat, vals8'[l]? = some 0#8) →
        Full.FullExtScratchPres s s' →
        sc'.walk_best = s.scratch.walk_best → sc'.sim_sig = s.scratch.sim_sig →
        ((∀ nv < ncv.toNat, nv ≤ (inv[nv]?.getD 0#32).toNat) →
          (∀ nv < ncv.toNat, vals'[nv]? = s.core.flags[(inv[nv]?.getD 0#32).toNat]?) ∧
          (∀ v, ncv.toNat ≤ v → v < old_cv.toNat → vals'[v]? = some 0#32)) →
        (MemShrinkCompactMem c' s' inv ⋆ R) m' → Q () m'

def msCompactRest (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop) :
    Mem 64 → Prop :=
  (region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars)) (valsBytes c.max_vars - 2 * c.max_vars) ⋆
   (array (t := i8) c.pMark s.core.mrk ⋆
     region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
   region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars) ⋆
   region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars) ⋆
   region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (region (c.pFlags + BitVec.ofNat 64 (4 * c.max_vars))
     (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
   region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
     (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
   region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
     (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
   (array (t := i32) c.pTrail s.core.trl ⋆
     region (c.pTrail + BitVec.ofNat 64 (4 * c.max_vars))
       (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
   (array (t := i32) c.pTrailPos s.core.trail_pos ⋆
     region (c.pTrailPos + BitVec.ofNat 64 (4 * c.max_vars))
       (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
   (array (t := i32) c.pTmp s.core.tmp ⋆
     region (c.pTmp + BitVec.ofNat 64 (4 * c.max_vars))
       (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
   (array (t := i32) c.pHeap s.scratch.heap ⋆
     region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars))
       (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
   region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars))
     (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  ((array (t := i32) c.pMinClr s.core.min_clr ⋆
     region (c.pMinClr + BitVec.ofNat 64 (4 * c.max_vars))
       (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
   (array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
     region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.max_vars))
       (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
   region (c.pQPrev + BitVec.ofNat 64 (4 * c.max_vars))
     (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
   region (c.pQNext + BitVec.ofNat 64 (4 * c.max_vars))
     (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
   region (c.pQStamp + BitVec.ofNat 64 (4 * c.max_vars))
     (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
   region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
     (u32FullBytes c.max_vars - 4 * (c.max_vars + 1)) ⋆
   region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
     (u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
  (array (t := i32) c.pWvec s.core.wvec ⋆
   array (t := i32) c.pMinStk s.core.min_stk ⋆
   array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
   array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
   array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
   array (t := i32) c.pDelayed s.scratch.delayed ⋆
   array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
   array (t := i32) c.pScratchBuf s.scratch.scratch_buf) ⋆
  MemShrinkLitMark c s ⋆
  region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
  region c.pTarjanMark (8 * c.max_vars) ⋆ region c.pTarjanReach (8 * c.max_vars) ⋆
  region c.pRepr (8 * c.max_vars) ⋆ region c.pSimSig (8 * c.max_vars) ⋆
  region c.pSlack c.slack ⋆ R

def msCompactFocused (c : MemShrinkCfg) (mvv : BitVec 64) (s : FullState)
    (ws2 : List (BitVec 32)) : Mem 64 → Prop :=
  dimacsState c.hdr mvv (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
  array (t := i8) c.pVals s.core.vals ⋆
  array (t := i32) c.pFlags s.core.flags ⋆
  array (t := i32) c.pLevel s.core.lvl ⋆
  array (t := i32) c.pReason s.core.rsns ⋆
  array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
  array (t := i32) c.pFrameDec s.core.frame_dec ⋆
  array (t := i8) c.pPhases s.scratch.phases ⋆
  array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
  array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
  array64 c.pScore s.scratch.score ⋆
  array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
  array (t := i32) c.pQPrev s.scratch.q_prev ⋆
  array (t := i32) c.pQNext s.scratch.q_next ⋆
  array (t := i32) c.pPos s.scratch.pos ⋆
  array (t := i32) c.pWorkStk2 ws2

private theorem msCompact_focus {c : MemShrinkCfg} {s : FullState} {ws2 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (MemShrinkCompactMem c s ws2 ⋆ R) m) :
    (msCompactFocused c (BitVec.ofNat 64 c.mv) s ws2 ⋆ msCompactRest c s R) m := by
  unfold MemShrinkCompactMem MemShrinkTransWithWs2 at hm
  rw [MemShrinkResArrays_eq, MemShrinkResBytes_eq, MemShrinkResU32A_eq, MemShrinkResU32B_eq,
    MemShrinkResTail_eq] at hm
  unfold msCompactFocused msCompactRest
  exact sep_ac hm

private theorem msCompact_unfocus {c : MemShrinkCfg} {s : FullState} {ws2 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (msCompactFocused c (BitVec.ofNat 64 c.mv) s ws2 ⋆ msCompactRest c s R) m) :
    (MemShrinkCompactMem c s ws2 ⋆ R) m := by
  unfold MemShrinkCompactMem MemShrinkTransWithWs2
  rw [MemShrinkResArrays_eq, MemShrinkResBytes_eq, MemShrinkResU32A_eq, MemShrinkResU32B_eq,
    MemShrinkResTail_eq]
  unfold msCompactFocused msCompactRest at hm
  exact sep_ac hm

private theorem m7HdrTailWords_set94 (c : MemShrinkCfg) (s : FullState) (mv' : Nat)
    (hle : mv' ≤ c.mv) :
    (m7HdrTailWords c s).set 94 (BitVec.ofNat 64 (c.max_vars - mv')) =
      m7HdrTailWords (memShrinkCfgShrinkMv c mv' hle) s := by
  rw [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq, m7HdrTailWords2_eq,
    m7HdrTailWords3_eq, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq]
  simp only [List.cons_append, List.nil_append, List.set_cons_succ, List.set_cons_zero]
  simp only [MemShrinkCfg.minDepth_eq, MemShrinkCfg.pVals_eq, MemShrinkCfg.pMark_eq,
    MemShrinkCfg.pPhases_eq, MemShrinkCfg.pPhasesTarget_eq, MemShrinkCfg.pPhasesBest_eq,
    MemShrinkCfg.pFlags_eq, MemShrinkCfg.pLevel_eq, MemShrinkCfg.pReason_eq,
    MemShrinkCfg.pTrail_eq, MemShrinkCfg.pTrailPos_eq, MemShrinkCfg.pTmp_eq,
    MemShrinkCfg.pHeap_eq, MemShrinkCfg.pPos_eq, MemShrinkCfg.pMinClr_eq,
    MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pQPrev_eq, MemShrinkCfg.pQNext_eq,
    MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pFrameTrail_eq, MemShrinkCfg.pFrameDec_eq,
    MemShrinkCfg.pWvec_eq, MemShrinkCfg.pScore_eq, MemShrinkCfg.pMinStk_eq,
    MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pLastLearned_eq, MemShrinkCfg.pArena_eq,
    MemShrinkCfg.pWstk_eq, MemShrinkCfg.pDelayed_eq, MemShrinkCfg.pRedRefs_eq,
    MemShrinkCfg.pExtendStk_eq, MemShrinkCfg.pScratchBuf_eq, MemShrinkCfg.pTrans_eq,
    MemShrinkCfg.pWsort_eq, MemShrinkCfg.pWorkStk1_eq, MemShrinkCfg.pWorkStk2_eq,
    MemShrinkCfg.pTarjanMark_eq, MemShrinkCfg.pTarjanReach_eq, MemShrinkCfg.pRepr_eq,
    MemShrinkCfg.pWalkVals_eq, MemShrinkCfg.pSimSig_eq, MemShrinkCfg.pWalkBest_eq,
    MemShrinkCfg.pLitMark_eq]
  rfl

private theorem msCompactRest_shrinkMv (c : MemShrinkCfg) (mv' : Nat) (hle : mv' ≤ c.mv)
    (s : FullState) (R : Mem 64 → Prop) :
    msCompactRest (memShrinkCfgShrinkMv c mv' hle) s R = msCompactRest c s R := by
  simp only [msCompactRest, MemShrinkLitMark_eq, MemShrinkCfg.minDepth_eq, MemShrinkCfg.pVals_eq,
    MemShrinkCfg.pMark_eq, MemShrinkCfg.pPhases_eq, MemShrinkCfg.pPhasesTarget_eq,
    MemShrinkCfg.pPhasesBest_eq, MemShrinkCfg.pFlags_eq, MemShrinkCfg.pLevel_eq,
    MemShrinkCfg.pReason_eq, MemShrinkCfg.pTrail_eq, MemShrinkCfg.pTrailPos_eq,
    MemShrinkCfg.pTmp_eq, MemShrinkCfg.pHeap_eq, MemShrinkCfg.pPos_eq, MemShrinkCfg.pMinClr_eq,
    MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pQPrev_eq, MemShrinkCfg.pQNext_eq,
    MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pFrameTrail_eq, MemShrinkCfg.pFrameDec_eq,
    MemShrinkCfg.pWvec_eq, MemShrinkCfg.pScore_eq, MemShrinkCfg.pMinStk_eq,
    MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pLastLearned_eq, MemShrinkCfg.pArena_eq,
    MemShrinkCfg.pWstk_eq, MemShrinkCfg.pDelayed_eq, MemShrinkCfg.pRedRefs_eq,
    MemShrinkCfg.pExtendStk_eq, MemShrinkCfg.pScratchBuf_eq, MemShrinkCfg.pTrans_eq,
    MemShrinkCfg.pWsort_eq, MemShrinkCfg.pWorkStk1_eq, MemShrinkCfg.pWorkStk2_eq,
    MemShrinkCfg.pTarjanMark_eq, MemShrinkCfg.pTarjanReach_eq, MemShrinkCfg.pRepr_eq,
    MemShrinkCfg.pSimSig_eq, MemShrinkCfg.pLitMark_eq, MemShrinkCfg.pSlack_eq,
    MemShrinkCfg.slack_eq]
  rfl

private theorem ms_hdr_load_eq {c : MemShrinkCfg} {s : FullState} {mvv : BitVec 64}
    {ws2 : List (BitVec 32)} {F : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 140) (off v : BitVec 64)
    (hv : (m7HdrTailWords c s)[i]? = some v)
    (hoff : c.hdr + off = (c.hdr + 32) + BitVec.ofNat 64 (8 * i))
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + off) = some v := by
  have hi_len : i < (m7HdrTailWords c s).length := by rw [m7HdrTailWords_length]; exact hi
  have heq : (m7HdrTailWords c s)[i]'hi_len = v := by
    simpa [List.getElem?_eq_getElem hi_len] using hv
  have h1 : (array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
      (dimacsState c.hdr mvv (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pFlags s.core.flags ⋆
        array (t := i32) c.pLevel s.core.lvl ⋆ array (t := i32) c.pReason s.core.rsns ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        array (t := i8) c.pPhases s.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pWorkStk2 ws2 ⋆ F)) m := by
    unfold msCompactFocused at hm; exact sep_ac hm
  rw [hoff, ← heq]; exact loadVal_array64 hi_len h1

private theorem ms_hdr_store_eq {c : MemShrinkCfg} {s s' : FullState} {mvv : BitVec 64}
    {ws2 : List (BitVec 32)} {F : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 140) (off v : BitVec 64)
    (hoff : c.hdr + off = (c.hdr + 32) + BitVec.ofNat 64 (8 * i))
    (hset : (m7HdrTailWords c s).set i v = m7HdrTailWords c s')
    (harr :
      (array (t := i8) c.pVals s'.core.vals ⋆ array (t := i32) c.pFlags s'.core.flags ⋆
        array (t := i32) c.pLevel s'.core.lvl ⋆ array (t := i32) c.pReason s'.core.rsns ⋆
        array (t := i32) c.pFrameTrail s'.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s'.core.frame_dec ⋆
        array (t := i8) c.pPhases s'.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s'.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s'.scratch.phases_best ⋆
        array64 c.pScore s'.scratch.score ⋆ array (t := i32) c.pQStamp s'.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s'.scratch.q_prev ⋆ array (t := i32) c.pQNext s'.scratch.q_next ⋆
        array (t := i32) c.pPos s'.scratch.pos) =
      (array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pFlags s.core.flags ⋆
        array (t := i32) c.pLevel s.core.lvl ⋆ array (t := i32) c.pReason s.core.rsns ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        array (t := i8) c.pPhases s.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pPos s.scratch.pos))
    (hd1 : s'.core.d_cur = s.core.d_cur) (hd2 : s'.core.d_val = s.core.d_val)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + off) ∧
      (msCompactFocused c mvv s' ws2 ⋆ F) (storeMem m i64 (c.hdr + off) v) := by
  have hi_len : i < (m7HdrTailWords c s).length := by rw [m7HdrTailWords_length]; exact hi
  have h1 : (array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
      (dimacsState c.hdr mvv (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        (array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pFlags s.core.flags ⋆
        array (t := i32) c.pLevel s.core.lvl ⋆ array (t := i32) c.pReason s.core.rsns ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        array (t := i8) c.pPhases s.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pPos s.scratch.pos) ⋆ array (t := i32) c.pWorkStk2 ws2 ⋆ F)) m := by
    unfold msCompactFocused at hm; exact sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 v hi_len h1
  rw [← hoff] at hok hst
  rw [hset] at hst
  refine ⟨hok, ?_⟩
  unfold msCompactFocused
  rw [hd1, hd2]
  have h1' : (array64 (c.hdr + 32) (m7HdrTailWords c s') ⋆
      (dimacsState c.hdr mvv (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        (array (t := i8) c.pVals s'.core.vals ⋆ array (t := i32) c.pFlags s'.core.flags ⋆
        array (t := i32) c.pLevel s'.core.lvl ⋆ array (t := i32) c.pReason s'.core.rsns ⋆
        array (t := i32) c.pFrameTrail s'.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s'.core.frame_dec ⋆
        array (t := i8) c.pPhases s'.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s'.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s'.scratch.phases_best ⋆
        array64 c.pScore s'.scratch.score ⋆ array (t := i32) c.pQStamp s'.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s'.scratch.q_prev ⋆ array (t := i32) c.pQNext s'.scratch.q_next ⋆
        array (t := i32) c.pPos s'.scratch.pos) ⋆ array (t := i32) c.pWorkStk2 ws2 ⋆ F))
      (storeMem m i64 (c.hdr + off) v) := by
    rw [harr]; exact hst
  exact sep_ac h1'

namespace MsCompactTactics

private theorem m4 (a i : BitVec 64) : a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
private theorem m8 (a i : BitVec 64) : a + i * 8 = a + BitVec.ofNat 64 (8 * i.toNat) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]
private theorem bvId (i : BitVec 64) : BitVec.ofNat 64 i.toNat = i := @bv_ofNat_toNat_eq 64 i

section HeaderLoads
variable {c : MemShrinkCfg} {mvv : BitVec 64} {s : FullState} {ws2 : List (BitVec 32)}
  {F : Mem 64 → Prop} {m : Mem 64}

private theorem gMH (i : Nat) (off : BitVec 64) (v : BitVec 64) (hi : i < 140)
    (hv : (m7HdrTailWords c s)[i]? = some v := by
      simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl)
    (hoff : c.hdr + off = (c.hdr + 32) + BitVec.ofNat 64 (8 * i) := by
      rw [BitVec.add_assoc]; rfl)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) : loadVal m i64 (c.hdr + off) = some v :=
  ms_hdr_load_eq i hi off v hv hoff hm

private theorem ms_focus_dimacs {c : MemShrinkCfg} {mvv : BitVec 64} {s : FullState}
    {ws2 : List (BitVec 32)} {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    (dimacsState c.hdr mvv (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      ((array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
        array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pFlags s.core.flags ⋆
        array (t := i32) c.pLevel s.core.lvl ⋆ array (t := i32) c.pReason s.core.rsns ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        array (t := i8) c.pPhases s.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pWorkStk2 ws2) ⋆ F)) m := by
  unfold msCompactFocused at hm; exact sep_ac hm

private theorem ms_unfocus_dimacs {c : MemShrinkCfg} {mvv : BitVec 64} {s : FullState}
    {ws2 : List (BitVec 32)} {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState c.hdr mvv (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      ((array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
        array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pFlags s.core.flags ⋆
        array (t := i32) c.pLevel s.core.lvl ⋆ array (t := i32) c.pReason s.core.rsns ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        array (t := i8) c.pPhases s.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pWorkStk2 ws2) ⋆ F)) m) :
    (msCompactFocused c mvv s ws2 ⋆ F) m := by
  unfold msCompactFocused; exact sep_ac hm

@[scoped c0_load] theorem load_ms_mv (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 c.hdr = some mvv :=
  load_dimacs_mv (ms_focus_dimacs hm)
@[scoped c0_load] theorem load_ms_max_vars (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 768) = some (BitVec.ofNat 64 c.max_vars) :=
  gMH 92 768 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_vals_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 64) = some c.pVals :=
  gMH 4 64 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_flags_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 800) = some c.pFlags :=
  gMH 96 800 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_level_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 80) = some c.pLevel :=
  gMH 6 80 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_reason_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 88) = some c.pReason :=
  gMH 7 88 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_frame_trail_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 832) = some c.pFrameTrail :=
  gMH 100 832 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_frame_dec_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 840) = some c.pFrameDec :=
  gMH 101 840 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_phases_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 224) = some c.pPhases :=
  gMH 24 224 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_phases_target_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 392) = some c.pPhasesTarget :=
  gMH 45 392 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_phases_best_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 400) = some c.pPhasesBest :=
  gMH 46 400 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_score_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 216) = some c.pScore :=
  gMH 23 216 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_q_stamp_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 384) = some c.pQStamp :=
  gMH 44 384 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_q_prev_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 368) = some c.pQPrev :=
  gMH 42 368 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_q_next_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 376) = some c.pQNext :=
  gMH 43 376 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_pos_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 208) = some c.pPos :=
  gMH 22 208 _ (by omega) (hm := hm)
@[scoped c0_load] theorem load_ms_work_stk2_ptr (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.hdr + 856) = some c.pWorkStk2 :=
  gMH 103 856 _ (by omega) (hm := hm)

end HeaderLoads

section HeaderStores
variable {c : MemShrinkCfg} {mvv : BitVec 64} {s : FullState} {ws2 : List (BitVec 32)}
  {F : Mem 64 → Prop} {m : Mem 64}

private theorem sMH (i : Nat) (off v : BitVec 64) (s' : FullState) (hi : i < 140)
    (hset : (m7HdrTailWords c s).set i v = m7HdrTailWords c s' := by
      simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl)
    (harr :
      (array (t := i8) c.pVals s'.core.vals ⋆ array (t := i32) c.pFlags s'.core.flags ⋆
        array (t := i32) c.pLevel s'.core.lvl ⋆ array (t := i32) c.pReason s'.core.rsns ⋆
        array (t := i32) c.pFrameTrail s'.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s'.core.frame_dec ⋆
        array (t := i8) c.pPhases s'.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s'.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s'.scratch.phases_best ⋆
        array64 c.pScore s'.scratch.score ⋆ array (t := i32) c.pQStamp s'.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s'.scratch.q_prev ⋆ array (t := i32) c.pQNext s'.scratch.q_next ⋆
        array (t := i32) c.pPos s'.scratch.pos) =
      (array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pFlags s.core.flags ⋆
        array (t := i32) c.pLevel s.core.lvl ⋆ array (t := i32) c.pReason s.core.rsns ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        array (t := i8) c.pPhases s.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pPos s.scratch.pos) := by rfl)
    (hd1 : s'.core.d_cur = s.core.d_cur := by rfl)
    (hd2 : s'.core.d_val = s.core.d_val := by rfl)
    (hoff : c.hdr + off = (c.hdr + 32) + BitVec.ofNat 64 (8 * i) := by
      rw [BitVec.add_assoc]; rfl)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + off) ∧
      (msCompactFocused c mvv s' ws2 ⋆ F) (storeMem m i64 (c.hdr + off) v) :=
  ms_hdr_store_eq i hi off v hoff hset harr hd1 hd2 hm

@[scoped c0_store] theorem store_ms_trail_end (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 144) ∧
      (msCompactFocused c mvv { s with core := { s.core with trail_end := v.toNat } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 144) v) :=
  sMH 14 144 v _ (by omega)
    (hset := by
      simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq, @bv_ofNat_toNat_eq 64 v]; rfl)
    (hm := hm)

@[scoped c0_store] theorem store_ms_propagated (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 152) ∧
      (msCompactFocused c mvv { s with core := { s.core with propagated := v.toNat } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 152) v) :=
  sMH 15 152 v _ (by omega)
    (hset := by
      simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq, @bv_ofNat_toNat_eq 64 v]; rfl)
    (hm := hm)

@[scoped c0_store] theorem store_ms_cur_level (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 160) ∧
      (msCompactFocused c mvv { s with core := { s.core with cur_level := v.toNat } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 160) v) :=
  sMH 16 160 v _ (by omega)
    (hset := by
      simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq, @bv_ofNat_toNat_eq 64 v]; rfl)
    (hm := hm)

@[scoped c0_store] theorem store_ms_unflushed (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 512) ∧
      (msCompactFocused c mvv { s with core := { s.core with unflushed := v } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 512) v) :=
  sMH 60 512 v _ (by omega) (hm := hm)

@[scoped c0_store] theorem store_ms_confl_ref (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 176) ∧
      (msCompactFocused c mvv { s with core := { s.core with confl_ref := v } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 176) v) :=
  sMH 18 176 v _ (by omega) (hm := hm)

@[scoped c0_store] theorem store_ms_confl_type (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 528) ∧
      (msCompactFocused c mvv { s with core := { s.core with confl_type := v } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 528) v) :=
  sMH 62 528 v _ (by omega) (hm := hm)

@[scoped c0_store] theorem store_ms_target_assigned (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 648) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with target_assigned := v } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 648) v) :=
  sMH 77 648 v _ (by omega) (hm := hm)

@[scoped c0_store] theorem store_ms_best_assigned (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 656) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with best_assigned := v } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 656) v) :=
  sMH 78 656 v _ (by omega) (hm := hm)

@[scoped c0_store] theorem store_ms_cur_vars (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 776) ∧
      (msCompactFocused c mvv { s with core := { s.core with cur_vars := v.toNat } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 776) v) :=
  sMH 93 776 v _ (by omega)
    (hset := by
      simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq, @bv_ofNat_toNat_eq 64 v]; rfl)
    (hm := hm)

@[scoped c0_store] theorem store_ms_unassigned (v : BitVec 64)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.hdr + 792) ∧
      (msCompactFocused c mvv { s with core := { s.core with unassigned := v } } ws2 ⋆ F)
        (storeMem m i64 (c.hdr + 792) v) :=
  sMH 95 792 v _ (by omega) (hm := hm)

end HeaderStores

section ArrayAccess
variable {c : MemShrinkCfg} {mvv : BitVec 64} {s : FullState} {ws2 : List (BitVec 32)}
  {F : Mem 64 → Prop} {m : Mem 64}

private theorem arrG8 {a : BitVec 64} {xs : List (BitVec 8)} {Q : Mem 64 → Prop} {i : Nat}
    {m0 : Mem 64} (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ Q) m0) :
    loadVal m0 i8 (a + BitVec.ofNat 64 i) = some xs[i] := by
  simpa [Ty.bytes, Ty.size, i8] using loadVal_array (t := i8) (by decide) hi h
private theorem arrP8 {a : BitVec 64} {xs : List (BitVec 8)} {Q : Mem 64 → Prop} {i : Nat}
    {m0 : Mem 64} (v : BitVec 8) (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ Q) m0) :
    storeOk m0 i8 (a + BitVec.ofNat 64 i) ∧ (array (t := i8) a (xs.set i v) ⋆ Q)
      (storeMem m0 i8 (a + BitVec.ofNat 64 i) v) := by
  simpa [Ty.bytes, Ty.size, i8] using store_array (t := i8) v (by decide) hi h
private theorem arrG32 {a : BitVec 64} {xs : List (BitVec 32)} {Q : Mem 64 → Prop} {i : Nat}
    {m0 : Mem 64} (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ Q) m0) :
    loadVal m0 i32 (a + BitVec.ofNat 64 (4 * i)) = some xs[i] :=
  loadVal_array (t := i32) (by decide) hi h
private theorem arrP32 {a : BitVec 64} {xs : List (BitVec 32)} {Q : Mem 64 → Prop} {i : Nat}
    {m0 : Mem 64} (v : BitVec 32) (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ Q) m0) :
    storeOk m0 i32 (a + BitVec.ofNat 64 (4 * i)) ∧ (array (t := i32) a (xs.set i v) ⋆ Q)
      (storeMem m0 i32 (a + BitVec.ofNat 64 (4 * i)) v) :=
  store_array (t := i32) v (by decide) hi h

private def msRestExcept (c : MemShrinkCfg) (mvv : BitVec 64) (s : FullState)
    (ws2 : List (BitVec 32)) (idx : Nat) (F : Mem 64 → Prop) : Mem 64 → Prop :=
  (if idx = 0 then emp else array (t := i8) c.pVals s.core.vals) ⋆
  (if idx = 1 then emp else array (t := i32) c.pFlags s.core.flags) ⋆
  (if idx = 2 then emp else array (t := i32) c.pLevel s.core.lvl) ⋆
  (if idx = 3 then emp else array (t := i32) c.pReason s.core.rsns) ⋆
  (if idx = 4 then emp else array (t := i32) c.pFrameTrail s.core.frame_trail) ⋆
  (if idx = 5 then emp else array (t := i32) c.pFrameDec s.core.frame_dec) ⋆
  (if idx = 6 then emp else array (t := i8) c.pPhases s.scratch.phases) ⋆
  (if idx = 7 then emp else array (t := i8) c.pPhasesTarget s.scratch.phases_target) ⋆
  (if idx = 8 then emp else array (t := i8) c.pPhasesBest s.scratch.phases_best) ⋆
  (if idx = 9 then emp else array64 c.pScore s.scratch.score) ⋆
  (if idx = 10 then emp else array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
  (if idx = 11 then emp else array (t := i32) c.pQPrev s.scratch.q_prev) ⋆
  (if idx = 12 then emp else array (t := i32) c.pQNext s.scratch.q_next) ⋆
  (if idx = 13 then emp else array (t := i32) c.pPos s.scratch.pos) ⋆
  (if idx = 14 then emp else array (t := i32) c.pWorkStk2 ws2) ⋆
  (dimacsState c.hdr mvv (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆ F)

@[scoped c0_store] theorem store_ms_vals {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.core.vals.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i8 (c.pVals + i) ∧
      (msCompactFocused c mvv { s with core := { s.core with vals := s.core.vals.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i8 (c.pVals + i) v) := by
  have hm' : (array (t := i8) c.pVals s.core.vals ⋆ msRestExcept c mvv s ws2 0 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [emp_sep]; exact sep_ac hm
  obtain ⟨hok, hst⟩ := arrP8 v hi hm'
  rw [bvId] at hok hst
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [emp_sep] at hst; exact sep_ac hst

@[scoped c0_load] theorem load_ms_ws2 {i : BitVec 64} (hi : i.toNat < ws2.length)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i32 (c.pWorkStk2 + i * 4) = some ws2[i.toNat] := by
  have hm' : (array (t := i32) c.pWorkStk2 ws2 ⋆ msRestExcept c mvv s ws2 14 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]; exact arrG32 hi hm'

@[scoped c0_load] theorem load_ms_flags {i : BitVec 64} (hi : i.toNat < s.core.flags.length)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i32 (c.pFlags + i * 4) = some s.core.flags[i.toNat] := by
  have hm' : (array (t := i32) c.pFlags s.core.flags ⋆ msRestExcept c mvv s ws2 1 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]; exact arrG32 hi hm'

@[scoped c0_store] theorem store_ms_flags {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.core.flags.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pFlags + i * 4) ∧
      (msCompactFocused c mvv { s with core := { s.core with flags := s.core.flags.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i32 (c.pFlags + i * 4) v) := by
  have hm' : (array (t := i32) c.pFlags s.core.flags ⋆ msRestExcept c mvv s ws2 1 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]
  obtain ⟨hok, hst⟩ := arrP32 v hi hm'
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_store] theorem store_ms_lvl {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.core.lvl.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pLevel + i * 4) ∧
      (msCompactFocused c mvv { s with core := { s.core with lvl := s.core.lvl.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i32 (c.pLevel + i * 4) v) := by
  have hm' : (array (t := i32) c.pLevel s.core.lvl ⋆ msRestExcept c mvv s ws2 2 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]
  obtain ⟨hok, hst⟩ := arrP32 v hi hm'
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_store] theorem store_ms_rsns {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.core.rsns.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pReason + i * 4) ∧
      (msCompactFocused c mvv { s with core := { s.core with rsns := s.core.rsns.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i32 (c.pReason + i * 4) v) := by
  have hm' : (array (t := i32) c.pReason s.core.rsns ⋆ msRestExcept c mvv s ws2 3 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]
  obtain ⟨hok, hst⟩ := arrP32 v hi hm'
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_store] theorem store_ms_frame_trail0 (v : BitVec 32)
    (hi : 0 < s.core.frame_trail.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 c.pFrameTrail ∧
      (msCompactFocused c mvv
        { s with core := { s.core with frame_trail := s.core.frame_trail.set 0 v } }
        ws2 ⋆ F) (storeMem m i32 c.pFrameTrail v) := by
  have hm' : (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
      msRestExcept c mvv s ws2 4 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  obtain ⟨hok, hst⟩ := arrP32 (i := 0) v hi hm'
  rw [BitVec.add_zero] at hok hst
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_store] theorem store_ms_frame_trail0_add0 (v : BitVec 32)
    (hi : 0 < s.core.frame_trail.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pFrameTrail + 0#64) ∧
      (msCompactFocused c mvv
        { s with core := { s.core with frame_trail := s.core.frame_trail.set 0 v } }
        ws2 ⋆ F) (storeMem m i32 (c.pFrameTrail + 0#64) v) := by
  simpa using store_ms_frame_trail0 v hi hm

@[scoped c0_store] theorem store_ms_frame_trail0_mul4 (v : BitVec 32)
    (hi : 0 < s.core.frame_trail.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pFrameTrail + BitVec.ofNat 64 0 * 4) ∧
      (msCompactFocused c mvv
        { s with core := { s.core with frame_trail := s.core.frame_trail.set 0 v } }
        ws2 ⋆ F) (storeMem m i32 (c.pFrameTrail + BitVec.ofNat 64 0 * 4) v) := by
  simpa using store_ms_frame_trail0 v hi hm

@[scoped c0_store] theorem store_ms_frame_dec0 (v : BitVec 32)
    (hi : 0 < s.core.frame_dec.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 c.pFrameDec ∧
      (msCompactFocused c mvv
        { s with core := { s.core with frame_dec := s.core.frame_dec.set 0 v } }
        ws2 ⋆ F) (storeMem m i32 c.pFrameDec v) := by
  have hm' : (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
      msRestExcept c mvv s ws2 5 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  obtain ⟨hok, hst⟩ := arrP32 (i := 0) v hi hm'
  rw [BitVec.add_zero] at hok hst
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_store] theorem store_ms_frame_dec0_add0 (v : BitVec 32)
    (hi : 0 < s.core.frame_dec.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pFrameDec + 0#64) ∧
      (msCompactFocused c mvv
        { s with core := { s.core with frame_dec := s.core.frame_dec.set 0 v } }
        ws2 ⋆ F) (storeMem m i32 (c.pFrameDec + 0#64) v) := by
  simpa using store_ms_frame_dec0 v hi hm

@[scoped c0_store] theorem store_ms_frame_dec0_mul4 (v : BitVec 32)
    (hi : 0 < s.core.frame_dec.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pFrameDec + BitVec.ofNat 64 0 * 4) ∧
      (msCompactFocused c mvv
        { s with core := { s.core with frame_dec := s.core.frame_dec.set 0 v } }
        ws2 ⋆ F) (storeMem m i32 (c.pFrameDec + BitVec.ofNat 64 0 * 4) v) := by
  simpa using store_ms_frame_dec0 v hi hm

@[scoped c0_load] theorem load_ms_phases {i : BitVec 64} (hi : i.toNat < s.scratch.phases.length)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i8 (c.pPhases + i) = some s.scratch.phases[i.toNat] := by
  have hm' : (array (t := i8) c.pPhases s.scratch.phases ⋆ msRestExcept c mvv s ws2 6 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  have h := arrG8 hi hm'; rwa [bvId] at h

@[scoped c0_store] theorem store_ms_phases {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.scratch.phases.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i8 (c.pPhases + i) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with phases := s.scratch.phases.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i8 (c.pPhases + i) v) := by
  have hm' : (array (t := i8) c.pPhases s.scratch.phases ⋆ msRestExcept c mvv s ws2 6 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  obtain ⟨hok, hst⟩ := arrP8 v hi hm'
  rw [bvId] at hok hst
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_load] theorem load_ms_phases_target {i : BitVec 64}
    (hi : i.toNat < s.scratch.phases_target.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i8 (c.pPhasesTarget + i) = some s.scratch.phases_target[i.toNat] := by
  have hm' : (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
      msRestExcept c mvv s ws2 7 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  have h := arrG8 hi hm'; rwa [bvId] at h

@[scoped c0_store] theorem store_ms_phases_target {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.scratch.phases_target.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i8 (c.pPhasesTarget + i) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with phases_target := s.scratch.phases_target.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i8 (c.pPhasesTarget + i) v) := by
  have hm' : (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
      msRestExcept c mvv s ws2 7 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  obtain ⟨hok, hst⟩ := arrP8 v hi hm'
  rw [bvId] at hok hst
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_load] theorem load_ms_phases_best {i : BitVec 64}
    (hi : i.toNat < s.scratch.phases_best.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i8 (c.pPhasesBest + i) = some s.scratch.phases_best[i.toNat] := by
  have hm' : (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
      msRestExcept c mvv s ws2 8 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  have h := arrG8 hi hm'; rwa [bvId] at h

@[scoped c0_store] theorem store_ms_phases_best {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.scratch.phases_best.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i8 (c.pPhasesBest + i) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with phases_best := s.scratch.phases_best.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i8 (c.pPhasesBest + i) v) := by
  have hm' : (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
      msRestExcept c mvv s ws2 8 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  obtain ⟨hok, hst⟩ := arrP8 v hi hm'
  rw [bvId] at hok hst
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_load] theorem load_ms_score {i : BitVec 64} (hi : i.toNat < s.scratch.score.length)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i64 (c.pScore + i * 8) = some s.scratch.score[i.toNat] := by
  have hm' : (array64 c.pScore s.scratch.score ⋆ msRestExcept c mvv s ws2 9 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m8]; exact loadVal_array64 hi hm'

@[scoped c0_store] theorem store_ms_score {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < s.scratch.score.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i64 (c.pScore + i * 8) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with score := s.scratch.score.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i64 (c.pScore + i * 8) v) := by
  have hm' : (array64 c.pScore s.scratch.score ⋆ msRestExcept c mvv s ws2 9 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m8]
  obtain ⟨hok, hst⟩ := store_array64 v hi hm'
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_load] theorem load_ms_q_stamp {i : BitVec 64} (hi : i.toNat < s.scratch.q_stamp.length)
    (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    loadVal m i32 (c.pQStamp + i * 4) = some s.scratch.q_stamp[i.toNat] := by
  have hm' : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      msRestExcept c mvv s ws2 10 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]; exact arrG32 hi hm'

@[scoped c0_store] theorem store_ms_q_stamp {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.scratch.q_stamp.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pQStamp + i * 4) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with q_stamp := s.scratch.q_stamp.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i32 (c.pQStamp + i * 4) v) := by
  have hm' : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      msRestExcept c mvv s ws2 10 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]
  obtain ⟨hok, hst⟩ := arrP32 v hi hm'
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_store] theorem store_ms_q_prev {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.scratch.q_prev.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pQPrev + i * 4) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with q_prev := s.scratch.q_prev.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i32 (c.pQPrev + i * 4) v) := by
  have hm' : (array (t := i32) c.pQPrev s.scratch.q_prev ⋆
      msRestExcept c mvv s ws2 11 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]
  obtain ⟨hok, hst⟩ := arrP32 v hi hm'
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_store] theorem store_ms_q_next {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.scratch.q_next.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pQNext + i * 4) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with q_next := s.scratch.q_next.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i32 (c.pQNext + i * 4) v) := by
  have hm' : (array (t := i32) c.pQNext s.scratch.q_next ⋆
      msRestExcept c mvv s ws2 12 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]
  obtain ⟨hok, hst⟩ := arrP32 v hi hm'
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

@[scoped c0_store] theorem store_ms_pos {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.scratch.pos.length) (hm : (msCompactFocused c mvv s ws2 ⋆ F) m) :
    storeOk m i32 (c.pPos + i * 4) ∧
      (msCompactFocused c mvv
        { s with scratch := { s.scratch with pos := s.scratch.pos.set i.toNat v } }
        ws2 ⋆ F) (storeMem m i32 (c.pPos + i * 4) v) := by
  have hm' : (array (t := i32) c.pPos s.scratch.pos ⋆
      msRestExcept c mvv s ws2 13 F) m := by
    unfold msCompactFocused at hm; unfold msRestExcept
    simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false]
    rw [sep_emp]; exact sep_ac hm
  rw [m4]
  obtain ⟨hok, hst⟩ := arrP32 v hi hm'
  refine ⟨hok, ?_⟩
  unfold msCompactFocused; unfold msRestExcept at hst
  simp only [Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
    m7HdrTailWords2_eq, m7HdrTailWords3_eq] at hst ⊢
  rw [sep_emp] at hst; exact sep_ac hst

end ArrayAccess

end MsCompactTactics

open scoped MsCompactTactics

private theorem ms_store_mv_mid {c : MemShrinkCfg} {s : FullState} {ws2 : List (BitVec 32)}
    {F : Mem 64 → Prop} {m : Mem 64} (mv' : BitVec 64)
    (hm : (msCompactFocused c (BitVec.ofNat 64 c.mv) s ws2 ⋆ F) m) :
    storeOk m i64 c.hdr ∧
      (msCompactFocused c mv' s ws2 ⋆ F) (storeMem m i64 c.hdr mv') := by
  obtain ⟨hok, hst⟩ := store_dimacs_mv mv' (MsCompactTactics.ms_focus_dimacs hm)
  exact ⟨hok, MsCompactTactics.ms_unfocus_dimacs hst⟩

private theorem ms_store_bva_mid {c : MemShrinkCfg} {mvv : BitVec 64} {mv' : Nat}
    (hle : mv' ≤ c.mv) (hmvv : mvv = BitVec.ofNat 64 mv')
    {s s0 : FullState} {ws2 : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hrest : msCompactRest c s0 R = msCompactRest c s R)
    (hm : (msCompactFocused c mvv s ws2 ⋆ msCompactRest c s0 R) m) :
    storeOk m i64 (c.hdr + 784) ∧
      (MemShrinkCompactMem (memShrinkCfgShrinkMv c mv' hle) s ws2 ⋆ R)
        (storeMem m i64 (c.hdr + 784) (BitVec.ofNat 64 (c.max_vars - mv'))) := by
  let c' := memShrinkCfgShrinkMv c mv' hle
  have hm_mv : (msCompactFocused c (BitVec.ofNat 64 mv') s ws2 ⋆ msCompactRest c s R) m := by
    rw [← hmvv, ← hrest]; exact hm
  have h1 : (array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 mv') (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        (array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pFlags s.core.flags ⋆
        array (t := i32) c.pLevel s.core.lvl ⋆ array (t := i32) c.pReason s.core.rsns ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        array (t := i8) c.pPhases s.scratch.phases ⋆
        array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pWorkStk2 ws2 ⋆
        msCompactRest c s R))) m := by
    unfold msCompactFocused at hm_mv; exact sep_ac hm_mv
  obtain ⟨hok, hst⟩ := store_array64 (i := 94) (BitVec.ofNat 64 (c.max_vars - mv'))
    (by rw [m7HdrTailWords_length]; decide) h1
  have hptr : c.hdr + 32 + BitVec.ofNat 64 (8 * 94) = c.hdr + 784 := by
    rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 94) = 784 by decide]
  rw [hptr] at hok hst
  rw [m7HdrTailWords_set94 c s mv' hle] at hst
  have hst' : (msCompactFocused c' (BitVec.ofNat 64 c'.mv) s ws2 ⋆ msCompactRest c' s R)
      (storeMem m i64 (c.hdr + 784) (BitVec.ofNat 64 (c.max_vars - mv'))) := by
    rw [msCompactRest_shrinkMv c mv' hle s R]
    unfold msCompactFocused
    simp only [MemShrinkCfg.minDepth_eq, MemShrinkCfg.pVals_eq, MemShrinkCfg.pMark_eq,
      MemShrinkCfg.pPhases_eq, MemShrinkCfg.pPhasesTarget_eq, MemShrinkCfg.pPhasesBest_eq,
      MemShrinkCfg.pFlags_eq, MemShrinkCfg.pLevel_eq, MemShrinkCfg.pReason_eq,
      MemShrinkCfg.pTrail_eq, MemShrinkCfg.pTrailPos_eq, MemShrinkCfg.pTmp_eq,
      MemShrinkCfg.pHeap_eq, MemShrinkCfg.pPos_eq, MemShrinkCfg.pMinClr_eq,
      MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pQPrev_eq, MemShrinkCfg.pQNext_eq,
      MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pFrameTrail_eq, MemShrinkCfg.pFrameDec_eq,
      MemShrinkCfg.pWvec_eq, MemShrinkCfg.pScore_eq, MemShrinkCfg.pMinStk_eq,
      MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pLastLearned_eq, MemShrinkCfg.pArena_eq,
      MemShrinkCfg.pWstk_eq, MemShrinkCfg.pDelayed_eq, MemShrinkCfg.pRedRefs_eq,
      MemShrinkCfg.pExtendStk_eq, MemShrinkCfg.pScratchBuf_eq, MemShrinkCfg.pTrans_eq,
      MemShrinkCfg.pWorkStk1_eq, MemShrinkCfg.pWorkStk2_eq]
    simp only [MemShrinkCfg.minDepth_eq, MemShrinkCfg.pVals_eq, MemShrinkCfg.pMark_eq,
      MemShrinkCfg.pPhases_eq, MemShrinkCfg.pPhasesTarget_eq, MemShrinkCfg.pPhasesBest_eq,
      MemShrinkCfg.pFlags_eq, MemShrinkCfg.pLevel_eq, MemShrinkCfg.pReason_eq,
      MemShrinkCfg.pTrail_eq, MemShrinkCfg.pTrailPos_eq, MemShrinkCfg.pTmp_eq,
      MemShrinkCfg.pHeap_eq, MemShrinkCfg.pPos_eq, MemShrinkCfg.pMinClr_eq,
      MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pQPrev_eq, MemShrinkCfg.pQNext_eq,
      MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pFrameTrail_eq, MemShrinkCfg.pFrameDec_eq,
      MemShrinkCfg.pWvec_eq, MemShrinkCfg.pScore_eq, MemShrinkCfg.pMinStk_eq,
      MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pLastLearned_eq, MemShrinkCfg.pArena_eq,
      MemShrinkCfg.pWstk_eq, MemShrinkCfg.pDelayed_eq, MemShrinkCfg.pRedRefs_eq,
      MemShrinkCfg.pExtendStk_eq, MemShrinkCfg.pScratchBuf_eq, MemShrinkCfg.pTrans_eq,
      MemShrinkCfg.pWorkStk1_eq, MemShrinkCfg.pWorkStk2_eq] at hst
    exact sep_ac hst
  exact ⟨hok, msCompact_unfocus hst'⟩

private theorem ms_compact_vars_lengths {c c' : MemShrinkCfg} {s : FullState}
    {vals8 : List (BitVec 8)} {fl3 lvl3 rsns3 : List (BitVec 32)}
    {ph2 pt2 pb2 : List (BitVec 8)} {sc3 : List (BitVec 64)}
    {qs3 qp3 qn3 ps3 : List (BitVec 32)} {ncv tgt_asg bst_asg : BitVec 64}
    (hlen : MemShrinkLengthsOk c s) (hcompat : MemShrinkCfgCompat c c')
    (hcv_ge' : c'.mv ≤ ncv.toNat) (hmv_lt_max : ncv.toNat ≤ c.max_vars)
    (hvl1 : vals8.length = 2 * c.max_vars)
    (hfl3 : fl3.length = c.max_vars) (hlv3 : lvl3.length = c.max_vars)
    (hrs3 : rsns3.length = c.max_vars) (hph2 : ph2.length = c.max_vars)
    (hpt2 : pt2.length = c.max_vars) (hpb2 : pb2.length = c.max_vars)
    (hsc3 : sc3.length = c.max_vars) (hqs3 : qs3.length = c.max_vars)
    (hqp3 : qp3.length = c.max_vars) (hqn3 : qn3.length = c.max_vars)
    (hps3 : ps3.length = c.max_vars) :
    MemShrinkLengthsOk c'
      { core := { s.core with
          vals := vals8, flags := fl3, lvl := lvl3, rsns := rsns3,
          frame_trail := s.core.frame_trail.set 0 0#32,
          frame_dec := s.core.frame_dec.set 0 0xFFFFFFFF#32,
          trail_end := 0, propagated := 0, cur_level := 0,
          unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
          cur_vars := ncv.toNat, unassigned := ncv }
        scratch := { s.scratch with
          phases := ph2, phases_target := pt2, phases_best := pb2,
          score := sc3, q_stamp := qs3, q_prev := qp3, q_next := qn3, pos := ps3,
          target_assigned := tgt_asg, best_assigned := bst_asg } } := by
  obtain ⟨_, _, _, hmax, _, har, hwc, hdel, hred, hext, hscr⟩ := hcompat
  exact
    { vals_len := hmax ▸ hvl1
      lit_mark_len := hmax ▸ hlen.lit_mark_len
      mrk_len := hmax ▸ hlen.mrk_len
      flags_len := hmax ▸ hfl3
      lvl_len := hmax ▸ hlv3
      rsns_len := hmax ▸ hrs3
      trl_len := hmax ▸ hlen.trl_len
      trail_pos_len := hmax ▸ hlen.trail_pos_len
      tmp_len_arr := hmax ▸ hlen.tmp_len_arr
      min_clr_len_arr := hmax ▸ hlen.min_clr_len_arr
      frame_trail_len := hmax ▸ (by rw [List.length_set]; exact hlen.frame_trail_len)
      frame_dec_len := hmax ▸ (by rw [List.length_set]; exact hlen.frame_dec_len)
      wvec_len := hmax ▸ hlen.wvec_len
      min_stk_len := by
        rw [MemShrinkCfg.minDepth_eq, hmax, ← MemShrinkCfg.minDepth_eq c]; exact hlen.min_stk_len
      arena_len_arr := har ▸ hlen.arena_len_arr
      wstk_len_arr := hwc ▸ hlen.wstk_len_arr
      phases_len := hmax ▸ hph2
      phases_target_len := hmax ▸ hpt2
      phases_best_len := hmax ▸ hpb2
      heap_len_arr := hmax ▸ hlen.heap_len_arr
      pos_len := hmax ▸ hps3
      shrink_stk_len := hmax ▸ hlen.shrink_stk_len
      q_prev_len := hmax ▸ hqp3
      q_next_len := hmax ▸ hqn3
      q_stamp_len := hmax ▸ hqs3
      score_len := hmax ▸ hsc3
      glue_used_len := hlen.glue_used_len
      last_learned_len := hlen.last_learned_len
      delayed_len_arr := hdel ▸ hlen.delayed_len_arr
      red_refs_len := hred ▸ hlen.red_refs_len
      extend_stk_len := hext ▸ hlen.extend_stk_len
      scratch_buf_len := hscr ▸ hlen.scratch_buf_len
      cur_vars_ge := hcv_ge'
      cur_vars_le := hmax ▸ hmv_lt_max
      arena_len_le := har ▸ hlen.arena_len_le
      wlen_le := hwc ▸ hlen.wlen_le
      trail_end_le := Nat.zero_le _
      propagated_le := Nat.zero_le _
      tmp_len_le := hmax ▸ hlen.tmp_len_le
      min_clr_len_le := hmax ▸ hlen.min_clr_len_le
      heap_len_le := hmax ▸ hlen.heap_len_le
      delayed_len_le := hdel ▸ hlen.delayed_len_le
      extend_len_le := hext ▸ hlen.extend_len_le }

private def MsFlPres (s : FullState) (inv : List (BitVec 32)) (ncv : BitVec 64) (nv : Nat)
    (fl2 : List (BitVec 32)) : Prop :=
  (∀ k < ncv.toNat, k ≤ (inv[k]?.getD 0#32).toNat) →
    (∀ k < nv, fl2[k]? = s.core.flags[(inv[k]?.getD 0#32).toNat]?) ∧
    (∀ j, nv ≤ j → fl2[j]? = s.core.flags[j]?)

private def MsFlPres3 (s : FullState) (inv : List (BitVec 32)) (ncv : BitVec 64)
    (fl3 : List (BitVec 32)) (hi : Nat) : Prop :=
  ((∀ k < ncv.toNat, k ≤ (inv[k]?.getD 0#32).toNat) →
    ∀ k < ncv.toNat, fl3[k]? = s.core.flags[(inv[k]?.getD 0#32).toNat]?) ∧
  (∀ v, ncv.toNat ≤ v → v < hi → fl3[v]? = some 0#32)

private theorem bv64_add1_lt {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 by decide, Nat.mod_eq_of_lt h]

theorem full_compact_vars_m7ms_wp (Γ : Env) :
    ∀ a m Q X, m7msCompactVarsSpec a m Q X →
      Func.wp Γ full_compact_vars_m7ms_body a m Q X := by
  rintro ⟨h, old_cv, ncv, ⟨⟩⟩ m Q X
    ⟨c, s, inv, R, rfl, hlen, hold, hncv_le, hinv_len, hinv_ok, hm0, hQ⟩
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcv_le := hlen.cur_vars_le
  have hcv2_lt64 : 2 * old_cv.toNat < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
  have hcv_lt64 : old_cv.toNat < 2 ^ 64 := by omega
  have hncv_lt64 : ncv.toNat < 2 ^ 64 := by omega
  have hv_len := hlen.vals_len
  have hfl_len := hlen.flags_len
  have hlv_len := hlen.lvl_len
  have hrs_len := hlen.rsns_len
  have hft_len := hlen.frame_trail_len
  have hfd_len := hlen.frame_dec_len
  have hph_len := hlen.phases_len
  have hpt_len := hlen.phases_target_len
  have hpb_len := hlen.phases_best_len
  have hsc_len := hlen.score_len
  have hqs_len := hlen.q_stamp_len
  have hqp_len := hlen.q_prev_len
  have hqn_len := hlen.q_next_len
  have hps_len := hlen.pos_len
  have hm := msCompact_focus hm0
  unfold Func.wp full_compact_vars_m7ms_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (l, ()) m1 =>
      l.toNat ≤ 2 * old_cv.toNat ∧
      ∃ vals1 : List (BitVec 8), vals1.length = 2 * c.max_vars ∧
        (∀ i < l.toNat, vals1[i]? = some 0#8) ∧
        (msCompactFocused c (BitVec.ofNat 64 c.mv)
          { s with core := { s.core with vals := vals1 } } inv ⋆ msCompactRest c s R) m1)
    (fun (l, ()) _ => 2 * old_cv.toNat - l.toNat)
    (fun J1 hLoop1 => by
      c0_hsteps
      exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.core.vals, hv_len, fun _ h => by simp at h, hm⟩)
    (fun J1 ⟨l, ⟨⟩⟩ m1 ⟨hl_le, vals1, hvl1, hz1, hm1⟩ hLoop1 => ?_)
  c0_hsplit
  · have hl_lt : l.toNat < 2 * old_cv.toNat := by
      have h1 := hc
      rw [show (2 : Nat) ^ (OfNat.ofNat 1 : Nat) = 2 by rfl, Nat.mul_comm,
        Nat.mod_eq_of_lt hcv2_lt64] at h1
      exact h1
    have hl1_eq : (l + 1#64).toNat = l.toNat + 1 :=
      bv64_add1_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hl_lt) hcv2_lt64)
    have hl_vals : l.toNat < vals1.length :=
      hvl1 ▸ Nat.lt_of_lt_of_le hl_lt (Nat.mul_le_mul_left 2 (hold ▸ hcv_le))
    c0_hsteps
    refine hLoop1 (l + 1#64, ()) _
      (by dsimp only; rw [hl1_eq]; exact Nat.sub_lt_sub_left hl_lt (Nat.lt_succ_self _))
      ⟨by rw [hl1_eq]; exact Nat.succ_le_of_lt hl_lt, vals1.set l.toNat 0#8,
       by rw [List.length_set, hvl1], fun i hi => ?_, by assumption⟩
    rw [hl1_eq] at hi
    by_cases hil : i = l.toNat
    · subst hil; exact List.getElem?_set_self hl_vals
    · rw [List.getElem?_set_ne (Ne.symm hil)]
      exact hz1 i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hil)
  · clear hLoop1 J1
    have hl_eq : l.toNat = 2 * old_cv.toNat := by
      have h1 := hc
      rw [show (2 : Nat) ^ (OfNat.ofNat 1 : Nat) = 2 by rfl, Nat.mul_comm,
        Nat.mod_eq_of_lt hcv2_lt64] at h1
      exact Nat.le_antisymm hl_le (Nat.le_of_not_lt h1)
    rw [hl_eq] at hz1
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (tgt_asg, bst_asg, nv, ()) m2 =>
        nv.toNat ≤ ncv.toNat ∧
        ∃ fl2 lvl2 rsns2 : List (BitVec 32),
          fl2.length = c.max_vars ∧ lvl2.length = c.max_vars ∧ rsns2.length = c.max_vars ∧
          MsFlPres s inv ncv nv.toNat fl2 ∧
          ∃ ph2 pt2 pb2 : List (BitVec 8),
            ph2.length = c.max_vars ∧ pt2.length = c.max_vars ∧ pb2.length = c.max_vars ∧
            ∃ sc2 : List (BitVec 64), sc2.length = c.max_vars ∧
              ∃ qs2 : List (BitVec 32), qs2.length = c.max_vars ∧
                (msCompactFocused c (BitVec.ofNat 64 c.mv)
                  { core := { s.core with vals := vals1, flags := fl2, lvl := lvl2, rsns := rsns2 }
                    scratch := { s.scratch with phases := ph2, phases_target := pt2,
                                                  phases_best := pb2, score := sc2,
                                                  q_stamp := qs2 } }
                  inv ⋆ msCompactRest c s R) m2)
      (fun (_, _, nv, ()) _ => ncv.toNat - nv.toNat)
      (fun J2 hLoop2 => by
        c0_hsteps
        exact hLoop2 (0#64, 0#64, 0#64, ()) m1 ⟨Nat.zero_le _, s.core.flags, s.core.lvl,
          s.core.rsns, hfl_len, hlv_len, hrs_len,
          (fun _ => ⟨(fun _ h => by cases h), fun _ _ => rfl⟩),
          s.scratch.phases, s.scratch.phases_target, s.scratch.phases_best,
          hph_len, hpt_len, hpb_len, s.scratch.score, hsc_len, s.scratch.q_stamp,
          hqs_len, hm1⟩)
      (fun J2 ⟨tgt_asg, bst_asg, nv, ⟨⟩⟩ m2 ⟨hnv_le2, fl2, lvl2, rsns2, hfl2, hlv2, hrs2, hflp2,
          ph2, pt2, pb2, hph2, hpt2, hpb2, sc2, hsc2, qs2, hqs2, hm2⟩ hLoop2 => ?_)
    c0_hsplit
    · clear hm1
      have hnv_lt : nv.toNat < ncv.toNat := hc
      have hnv_cm : nv.toNat < c.max_vars :=
        Nat.lt_of_lt_of_le hnv_lt (Nat.le_trans hncv_le (hold ▸ hcv_le))
      have hnv_ws2 : nv.toNat < inv.length := hinv_len ▸
        Nat.lt_of_lt_of_le hnv_cm (Nat.le_mul_of_pos_left _ Nat.zero_lt_two)
      have hov_lt : (inv[nv.toNat]'hnv_ws2).toNat < old_cv.toNat := by
        simpa [List.getElem?_eq_getElem hnv_ws2] using hinv_ok nv.toNat hnv_lt
      have hov64_lt : ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat < old_cv.toNat := by
        rw [zext_toNat _ (by decide)]; exact hov_lt
      have hov_cm : ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat < c.max_vars :=
        Nat.lt_of_lt_of_le hov64_lt (hold ▸ hcv_le)
      have hnv_fl2 : nv.toNat < fl2.length := hfl2 ▸ hnv_cm
      have hov_fl2 : ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat < fl2.length := hfl2 ▸ hov_cm
      have hnv_ph2 : nv.toNat < ph2.length := hph2 ▸ hnv_cm
      have hov_ph2 : ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat < ph2.length := hph2 ▸ hov_cm
      have hnv_pt2 : nv.toNat < pt2.length := hpt2 ▸ hnv_cm
      have hov_pt2 : ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat < pt2.length := hpt2 ▸ hov_cm
      have hnv_pb2 : nv.toNat < pb2.length := hpb2 ▸ hnv_cm
      have hov_pb2 : ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat < pb2.length := hpb2 ▸ hov_cm
      have hnv_sc2 : nv.toNat < sc2.length := hsc2 ▸ hnv_cm
      have hov_sc2 : ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat < sc2.length := hsc2 ▸ hov_cm
      have hnv_qs2 : nv.toNat < qs2.length := hqs2 ▸ hnv_cm
      have hov_qs2 : ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat < qs2.length := hqs2 ▸ hov_cm
      have hnv_lv2 : nv.toNat < lvl2.length := hlv2 ▸ hnv_cm
      have hnv_rs2 : nv.toNat < rsns2.length := hrs2 ▸ hnv_cm
      have hnv1_eq : (nv + 1#64).toNat = nv.toNat + 1 :=
        bv64_add1_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hnv_lt) hncv_lt64)
      have hflp2' : MsFlPres s inv ncv (nv.toNat + 1) (fl2.set nv.toNat
          (fl2[((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat]'hov_fl2)) := by
        intro hord
        have ⟨hpre, hpost⟩ := hflp2 hord
        have hself : nv.toNat ≤ (inv[nv.toNat]?.getD 0#32).toNat := hord nv.toNat hnv_lt
        have hov_eq : ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat =
            (inv[nv.toNat]?.getD 0#32).toNat := by
          rw [zext_toNat _ (by decide), List.getElem?_eq_getElem hnv_ws2, Option.getD_some]
        have hfl_ov := hpost _ (hov_eq ▸ hself)
        constructor
        · intro k hk
          by_cases hkn : k = nv.toNat
          · subst hkn
            rw [List.getElem?_set_self hnv_fl2, ← hov_eq, ← List.getElem?_eq_getElem hov_fl2]
            exact hfl_ov
          · rw [List.getElem?_set_ne (Ne.symm hkn)]
            exact hpre k (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn)
        · intro j hj
          rw [List.getElem?_set_ne (Nat.ne_of_lt hj)]
          exact hpost j (Nat.le_trans (Nat.le_succ _) hj)
      let ov := ((inv[nv.toNat]'hnv_ws2).setWidth 64).toNat
      let fl2' := fl2.set nv.toNat (fl2[ov]'hov_fl2)
      let lvl2' := lvl2.set nv.toNat 0#32
      let rsns2' := rsns2.set nv.toNat 0xFFFFFFFF#32
      let ph2' := ph2.set nv.toNat (ph2[ov]'hov_ph2)
      let pt2' := pt2.set nv.toNat (pt2[ov]'hov_pt2)
      let pb2' := pb2.set nv.toNat (pb2[ov]'hov_pb2)
      let sc2' := sc2.set nv.toNat (sc2[ov]'hov_sc2)
      let qs2' := qs2.set nv.toNat (qs2[ov]'hov_qs2)
      c0_hsteps <;>
        exact hLoop2 (_, _, nv + 1#64, ()) _
          (by dsimp only; rw [hnv1_eq]; exact Nat.sub_lt_sub_left hnv_lt (Nat.lt_succ_self _))
          ⟨by rw [hnv1_eq]; exact Nat.succ_le_of_lt hnv_lt,
           fl2', lvl2', rsns2',
           by rw [List.length_set]; exact hfl2,
           by rw [List.length_set]; exact hlv2,
           by rw [List.length_set]; exact hrs2,
           by rw [hnv1_eq]; exact hflp2',
           ph2', pt2', pb2',
           by rw [List.length_set]; exact hph2,
           by rw [List.length_set]; exact hpt2,
           by rw [List.length_set]; exact hpb2,
           sc2', by rw [List.length_set]; exact hsc2,
           qs2', by rw [List.length_set]; exact hqs2,
           by assumption⟩
    · clear hLoop2 J2 hm1
      have hnv_eq : nv.toNat = ncv.toNat :=
        Nat.le_antisymm hnv_le2 (Nat.le_of_not_lt hc)
      rw [hnv_eq] at hflp2
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (v, ()) m3 =>
          ncv.toNat ≤ v.toNat ∧ v.toNat ≤ old_cv.toNat ∧
          ∃ fl3 lvl3 rsns3 qp3 qn3 qs3 ps3 : List (BitVec 32),
            fl3.length = c.max_vars ∧ lvl3.length = c.max_vars ∧ rsns3.length = c.max_vars ∧
            qp3.length = c.max_vars ∧ qn3.length = c.max_vars ∧ qs3.length = c.max_vars ∧
            ps3.length = c.max_vars ∧ MsFlPres3 s inv ncv fl3 v.toNat ∧
            ∃ sc3 : List (BitVec 64), sc3.length = c.max_vars ∧
              (msCompactFocused c (BitVec.ofNat 64 c.mv)
                { core := { s.core with vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3 }
                  scratch := { s.scratch with phases := ph2, phases_target := pt2,
                                                phases_best := pb2, score := sc3,
                                                q_stamp := qs3, q_prev := qp3,
                                                q_next := qn3, pos := ps3 } }
                inv ⋆ msCompactRest c s R) m3)
        (fun (v, ()) _ => old_cv.toNat - v.toNat)
        (fun J3 hLoop3 => by
          c0_hsteps
          exact hLoop3 (ncv, ()) m2 ⟨Nat.le_refl _, hncv_le, fl2, lvl2, rsns2, s.scratch.q_prev,
            s.scratch.q_next, qs2, s.scratch.pos, hfl2, hlv2, hrs2, hqp_len, hqn_len, hqs2,
            hps_len, ⟨(fun hord => (hflp2 hord).1), fun _ h1 h2 =>
              absurd h2 (Nat.not_lt_of_ge h1)⟩, sc2, hsc2, hm2⟩)
        (fun J3 ⟨v, ⟨⟩⟩ m3 ⟨hnv_v, hv_le3, fl3, lvl3, rsns3, qp3, qn3, qs3, ps3,
            hfl3, hlv3, hrs3, hqp3, hqn3, hqs3, hps3, hflp3, sc3, hsc3, hm3⟩ hLoop3 => ?_)
      c0_hsplit
      · clear hm2
        have hv_lt : v.toNat < old_cv.toNat := hc
        have hv_cm : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt (hold ▸ hcv_le)
        have hv_fl3 : v.toNat < fl3.length := hfl3 ▸ hv_cm
        have hv_lv3 : v.toNat < lvl3.length := hlv3 ▸ hv_cm
        have hv_rs3 : v.toNat < rsns3.length := hrs3 ▸ hv_cm
        have hv_sc3 : v.toNat < sc3.length := hsc3 ▸ hv_cm
        have hv_qs3 : v.toNat < qs3.length := hqs3 ▸ hv_cm
        have hv_qp3 : v.toNat < qp3.length := hqp3 ▸ hv_cm
        have hv_qn3 : v.toNat < qn3.length := hqn3 ▸ hv_cm
        have hv_ps3 : v.toNat < ps3.length := hps3 ▸ hv_cm
        have hv1_eq : (v + 1#64).toNat = v.toNat + 1 :=
          bv64_add1_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hv_lt) hcv_lt64)
        have hflp3' : MsFlPres3 s inv ncv (fl3.set v.toNat 0#32) (v.toNat + 1) := by
          constructor
          · intro hord k hk
            rw [List.getElem?_set_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hk hnv_v))]
            exact hflp3.1 hord k hk
          · intro u hu1 hu2
            by_cases huv : u = v.toNat
            · subst huv; exact List.getElem?_set_self hv_fl3
            · rw [List.getElem?_set_ne (Ne.symm huv)]
              exact hflp3.2 u hu1 (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hu2) huv)
        c0_hsteps
        exact hLoop3 (v + 1#64, ()) _
          (by dsimp only; rw [hv1_eq]; exact Nat.sub_lt_sub_left hv_lt (Nat.lt_succ_self _))
          ⟨by rw [hv1_eq]; exact Nat.le_trans hnv_v (Nat.le_succ _),
           by rw [hv1_eq]; exact Nat.succ_le_of_lt hv_lt,
           fl3.set v.toNat 0#32, lvl3.set v.toNat 0#32, rsns3.set v.toNat 0xFFFFFFFF#32,
           qp3.set v.toNat 0xFFFFFFFF#32, qn3.set v.toNat 0xFFFFFFFF#32, qs3.set v.toNat 0#32,
           ps3.set v.toNat 0xFFFFFFFF#32,
           by rw [List.length_set]; exact hfl3,
           by rw [List.length_set]; exact hlv3,
           by rw [List.length_set]; exact hrs3,
           by rw [List.length_set]; exact hqp3,
           by rw [List.length_set]; exact hqn3,
           by rw [List.length_set]; exact hqs3,
           by rw [List.length_set]; exact hps3,
           by rw [hv1_eq]; exact hflp3',
           sc3.set v.toNat 0#64, by rw [List.length_set]; exact hsc3,
           by assumption⟩
      · have hv_eq : v.toNat = old_cv.toNat :=
          Nat.le_antisymm hv_le3 (Nat.le_of_not_lt hc)
        rw [hv_eq] at hflp3
        have hft0 : 0 < s.core.frame_trail.length := by rw [hft_len]; exact Nat.zero_lt_succ _
        have hfd0 : 0 < s.core.frame_dec.length := by rw [hfd_len]; exact Nat.zero_lt_succ _
        clear hLoop3 J3 hm2 hinv_ok hncv_lt64 hfl_len hlv_len hrs_len hph_len hpt_len
          hpb_len hsc_len hqs_len hqp_len hqn_len hps_len hmax_lt hcv2_lt64 hcv_lt64 hv_len
        have hc_mv_lt : c.mv < 2 ^ 64 := Nat.lt_trans c.hmv (by unfold dimacsBound; decide)
        have hmax_lt64 : c.max_vars < 2 ^ 64 := Nat.lt_trans c.hmaxv (by unfold dimacsBound; decide)
        have hmv_lt_max : ncv.toNat ≤ c.max_vars := Nat.le_trans hncv_le (hold ▸ hcv_le)
        have hncv_bv : ncv = BitVec.ofNat 64 ncv.toNat := (@bv_ofNat_toNat_eq 64 ncv).symm
        have hsub_bv : BitVec.ofNat 64 c.max_vars - ncv =
            BitVec.ofNat 64 (c.max_vars - ncv.toNat) :=
          (congrArg (BitVec.ofNat 64 c.max_vars - ·) hncv_bv).trans
            (bv_sub_ofNat hmv_lt_max hmax_lt64)
        let sc_final : FullScratch :=
          { s.scratch with
            phases := ph2, phases_target := pt2, phases_best := pb2,
            score := sc3, q_stamp := qs3, q_prev := qp3, q_next := qn3, pos := ps3,
            target_assigned := tgt_asg, best_assigned := bst_asg }
        let s_final : FullState :=
          { core := { s.core with
              vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3,
              frame_trail := s.core.frame_trail.set 0 0#32,
              frame_dec := s.core.frame_dec.set 0 0xFFFFFFFF#32,
              trail_end := 0, propagated := 0, cur_level := 0,
              unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
              cur_vars := ncv.toNat, unassigned := ncv }
            scratch := sc_final }
        have hm3_focus : (msCompactFocused c (BitVec.ofNat 64 c.mv)
            { core := { s.core with vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3 }
              scratch := { s.scratch with phases := ph2, phases_target := pt2,
                                            phases_best := pb2, score := sc3,
                                            q_stamp := qs3, q_prev := qp3,
                                            q_next := qn3, pos := ps3 } }
            inv ⋆ msCompactRest c s R) m3 := hm3
        have hc_rest_eq : ∀ (sA : FullState),
            sA.core.mrk = s.core.mrk → sA.core.trl = s.core.trl →
            sA.core.trail_pos = s.core.trail_pos → sA.core.tmp = s.core.tmp →
            sA.core.min_clr = s.core.min_clr → sA.core.wvec = s.core.wvec →
            sA.core.min_stk = s.core.min_stk → sA.core.arena = s.core.arena →
            sA.core.wstk = s.core.wstk → sA.core.lit_mark = s.core.lit_mark →
            sA.scratch.heap = s.scratch.heap → sA.scratch.shrink_stk = s.scratch.shrink_stk →
            sA.scratch.glue_used = s.scratch.glue_used →
            sA.scratch.last_learned = s.scratch.last_learned →
            sA.scratch.delayed = s.scratch.delayed →
            sA.scratch.red_refs = s.scratch.red_refs →
            sA.scratch.extend_stk = s.scratch.extend_stk →
            sA.scratch.scratch_buf = s.scratch.scratch_buf →
            msCompactRest c sA R = msCompactRest c s R := by
          intro sA h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
          simp only [msCompactRest, MemShrinkLitMark_eq, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
            h11, h12, h13, h14, h15, h16, h17, h18]
        have hrest_eq : msCompactRest c s_final R = msCompactRest c s R := by
          dsimp only [s_final, sc_final]
          exact hc_rest_eq _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun () mJ =>
            ∃ c' : MemShrinkCfg, MemShrinkCfgCompat c c' ∧ c'.mv ≤ ncv.toNat ∧
              (ncv.toNat < c.mv → c'.mv = ncv.toNat) ∧
              (MemShrinkCompactMem c' s_final inv ⋆ R) mJ)
          (fun _ ⟨⟩ mJ ⟨c', hcompat', hcv_ge', hmv_eq', hmJ⟩ => by
            c0_hsteps
            exact hQ c' fl3 lvl3 rsns3 0#32 0xFFFFFFFF#32 sc_final vals1 mJ hcompat' hcv_ge'
              hmv_eq' (ms_compact_vars_lengths hlen hcompat' hcv_ge' hmv_lt_max hvl1 hfl3 hlv3
                hrs3 hph2 hpt2 hpb2 hsc3 hqs3 hqp3 hqn3 hps3)
              rfl (fun l hl => hz1 l hl) ⟨rfl, rfl⟩ rfl rfl
              (fun hord => ⟨hflp3.1 hord, hflp3.2⟩) hmJ)
          (fun Jmv hJmv => ?_)
        c0_hsplit
        · have hlt_mv : ncv.toNat < c.mv := by
            have h1 : ncv.toNat < (BitVec.ofNat 64 c.mv).toNat := hc
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc_mv_lt] at h1
          let c' := memShrinkCfgShrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv)
          refine wp_store_sep (ms_store_mv_mid ncv (by assumption)) ?_
          intro m4 hm4
          c0_hsteps_nogrp
          refine wp_store_sep (by
            rw [hsub_bv]
            exact ms_store_bva_mid (s := s_final) (s0 := s) (ws2 := inv)
              (Nat.le_of_lt hlt_mv) hncv_bv hrest_eq.symm hm4) ?_
          intro m5 hm5
          c0_hsteps
          exact hJmv () m5 ⟨c', MemShrinkCfgCompat.shrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv),
            Nat.le_refl _, fun _ => rfl, hm5⟩
        · have hge_mv : c.mv ≤ ncv.toNat := by
            have h1 : ¬ ncv.toNat < (BitVec.ofNat 64 c.mv).toNat := hc
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc_mv_lt] at h1
            exact Nat.le_of_not_lt h1
          c0_hsteps
          exact hJmv () _ ⟨c, MemShrinkCfgCompat.refl c, hge_mv,
            fun h => absurd h (Nat.not_lt_of_ge hge_mv),
            by
              refine msCompact_unfocus ?_
              rw [hrest_eq]
              dsimp only [s_final, sc_final]
              assumption⟩

end CompactVarsMs

/-! ## 4. Additive `MemShrinkM6HdrMem` & `FullM6Hdr` Framing (`0` Edits to `FullM6Hdr*.lean`) -/

section M6HdrFramingMs

/-- No-underflow geometry condition ensuring `c.hdr - 2304#64` fits cleanly in `[0, 2^64)`. -/
def MemShrinkM6HdrCfgOk (c : MemShrinkCfg) : Prop :=
  fullM6ExtBytes ≤ c.hdr.toNat

/-- Spatial separation predicate prepending `2,304 B` `M6HdrExt` directly before `MemShrinkMem`. -/
def MemShrinkM6HdrMem (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState) :
    Mem 64 → Prop :=
  array64 (m6ExtAddr c.hdr) ext ⋆ MemShrinkMem c s

/-- Combined initialization & `M6HdrExt` invariant under `MemShrinkCfg`. -/
def MemShrinkM6HdrInv (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState) : Prop :=
  MemShrinkM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ MemShrinkSparseInv c s

private theorem sep_swap_ms {P Q R : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ (Q ⋆ R)) m) : (Q ⋆ (P ⋆ R)) m := by
  rw [← sep_assoc, sep_comm P Q, sep_assoc] at h; exact h

theorem memShrinkM6HdrMem_iff (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop) (m : Mem 64) :
    (MemShrinkM6HdrMem c ext s ⋆ R) m ↔
      (MemShrinkMem c s ⋆ (array64 (m6ExtAddr c.hdr) ext ⋆ R)) m := by
  unfold MemShrinkM6HdrMem
  constructor
  · intro h; rw [sep_assoc] at h; exact sep_swap_ms h
  · intro h; rw [sep_assoc]; exact sep_swap_ms h

theorem memShrinkM6Hdr_frame {c : MemShrinkCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {P : (FullState → Mem 64 → Prop) → Prop}
    (hfn : ∀ F : Mem 64 → Prop,
      (MemShrinkMem c s ⋆ F) m → P (fun s' m' => (MemShrinkMem c s' ⋆ F) m'))
    (hm : (MemShrinkM6HdrMem c ext s ⋆ R) m) :
    P (fun s' m' => (MemShrinkM6HdrMem c ext s' ⋆ R) m') := by
  have h1 := hfn (array64 (m6ExtAddr c.hdr) ext ⋆ R)
    ((memShrinkM6HdrMem_iff c ext s R m).mp hm)
  have heq :
      (fun s' m' => (MemShrinkMem c s' ⋆ (array64 (m6ExtAddr c.hdr) ext ⋆ R)) m') =
      (fun s' m' => (MemShrinkM6HdrMem c ext s' ⋆ R) m') := by
    funext s' m'; exact propext (memShrinkM6HdrMem_iff c ext s' R m').symm
  rwa [heq] at h1

private theorem ms_step_reg {P : Mem 64 → Prop} {m0 : Mem 64} {n1 n2 : Nat} {a1 a2 : BitVec 64}
    (h : (region a1 n1 ⋆ (region a2 n2 ⋆ P)) m0)
    (hadd : a2 = a1 + BitVec.ofNat 64 n1) (hfit : n1 + n2 ≤ 2 ^ 64) :
    (region a1 (n1 + n2) ⋆ P) m0 := by
  rw [← sep_assoc, hadd] at h
  rwa [region_merge_eq rfl hfit] at h

private theorem ms_step_reg2 {m0 : Mem 64} {n1 n2 : Nat} {a1 a2 : BitVec 64}
    (h : (region a1 n1 ⋆ region a2 n2) m0)
    (hadd : a2 = a1 + BitVec.ofNat 64 n1) (hfit : n1 + n2 ≤ 2 ^ 64) :
    region a1 (n1 + n2) m0 := by
  rw [hadd] at h
  rwa [region_merge_eq rfl hfit] at h

private theorem ms_pad_merge_i8 {a : BitVec 64} {xs : List (BitVec 8)} {tot : Nat} {m : Mem 64}
    (hx : xs.length ≤ tot) (hfit : tot ≤ 2 ^ 64)
    (hm : (array (t := i8) a xs ⋆
      region (a + BitVec.ofNat 64 xs.length) (tot - xs.length)) m) :
    region a tot m := by
  have h1 := sep_mono (fun _ ha => i8_exact_to_reg (xs := xs) (by omega) ha) hm
  rw [region_merge_eq (a := a) (n1 := xs.length) (n2 := tot - xs.length)
    (n := tot) (by omega) hfit] at h1
  exact h1

private theorem ms_pad_merge_i32 {a : BitVec 64} {xs : List (BitVec 32)} {tot : Nat} {m : Mem 64}
    (hx : 4 * xs.length ≤ tot) (hfit : tot ≤ 2 ^ 64)
    (hm : (array (t := i32) a xs ⋆
      region (a + BitVec.ofNat 64 (4 * xs.length)) (tot - 4 * xs.length)) m) :
    region a tot m := by
  have h1 := sep_mono (fun _ ha => i32_exact_to_reg (xs := xs) (by omega) ha) hm
  rw [region_merge_eq (a := a) (n1 := 4 * xs.length) (n2 := tot - 4 * xs.length)
    (n := tot) (by omega) hfit] at h1
  exact h1

private theorem ms_pad_merge_i8_len {a : BitVec 64} {xs : List (BitVec 8)} {n tot : Nat}
    {m : Mem 64} (hlen : xs.length = n) (hx : n ≤ tot) (hfit : tot ≤ 2 ^ 64)
    (hm : (array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 n) (tot - n)) m) :
    region a tot m := by
  subst hlen; exact ms_pad_merge_i8 hx hfit hm

private theorem ms_pad_merge_i32_len {a : BitVec 64} {xs : List (BitVec 32)} {n tot : Nat}
    {m : Mem 64} (hlen : xs.length = n) (hx : 4 * n ≤ tot) (hfit : tot ≤ 2 ^ 64)
    (hm : (array (t := i32) a xs ⋆ region (a + BitVec.ofNat 64 (4 * n)) (tot - 4 * n)) m) :
    region a tot m := by
  subst hlen; exact ms_pad_merge_i32 hx hfit hm

private theorem ms_add_step {a1 a2 a3 : BitVec 64} {n1 n2 : Nat}
    (h12 : a2 = a1 + BitVec.ofNat 64 n1) (h23 : a3 = a2 + BitVec.ofNat 64 n2) :
    a3 = a1 + BitVec.ofNat 64 (n1 + n2) := by
  rw [h23, h12, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem ms_segBytes_to_reg (c : MemShrinkCfg) {s : FullState} {m : Mem 64}
    (hlen : MemShrinkLengthsOk c s)
    (hfit : valsBytes c.max_vars + 4 * markBytes c.max_vars ≤ 2 ^ 64)
    (hm : MemShrinkResBytes c s m) :
    region c.pVals (valsBytes c.max_vars + 4 * markBytes c.max_vars) m := by
  have hv_ge : 2 * c.max_vars ≤ valsBytes c.max_vars := by unfold valsBytes; omega
  have hm_ge : c.max_vars ≤ markBytes c.max_vars := by unfold markBytes; omega
  rw [MemShrinkResBytes_eq] at hm
  have hr0 : (region c.pVals (valsBytes c.max_vars) ⋆ region c.pMark (markBytes c.max_vars) ⋆
      region c.pPhases (markBytes c.max_vars) ⋆ region c.pPhasesTarget (markBytes c.max_vars) ⋆
      region c.pPhasesBest (markBytes c.max_vars)) m := by
    refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ hx => ms_pad_merge_i8_len hlen.vals_len hv_ge (by omega) hx)
      (fun _ hx => ms_pad_merge_i8_len hlen.mrk_len hm_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i8_len hlen.phases_len hm_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i8_len hlen.phases_target_len hm_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i8_len hlen.phases_best_len hm_ge (by omega) hx) m hm
  have hr : (region c.pVals (valsBytes c.max_vars) ⋆ (region c.pMark (markBytes c.max_vars) ⋆
      (region c.pPhases (markBytes c.max_vars) ⋆ (region c.pPhasesTarget (markBytes c.max_vars) ⋆
      region c.pPhasesBest (markBytes c.max_vars))))) m := sep_ac hr0
  have a1 := MemShrinkCfg.pMark_eq c
  have s1 := ms_step_reg hr a1 (by omega)
  have a2 := ms_add_step a1 (MemShrinkCfg.pPhases_eq c)
  have s2 := ms_step_reg s1 a2 (by omega)
  have a3 := ms_add_step a2 (MemShrinkCfg.pPhasesTarget_eq c)
  have s3 := ms_step_reg s2 a3 (by omega)
  have a4 := ms_add_step a3 (MemShrinkCfg.pPhasesBest_eq c)
  have s4 := ms_step_reg2 s3 a4 (by omega)
  simpa only [show valsBytes c.max_vars + markBytes c.max_vars + markBytes c.max_vars +
      markBytes c.max_vars + markBytes c.max_vars =
      valsBytes c.max_vars + 4 * markBytes c.max_vars by omega] using s4

private theorem ms_segU32A_to_reg (c : MemShrinkCfg) {s : FullState} {m : Mem 64}
    (hlen : MemShrinkLengthsOk c s) (hfit : 8 * u32FullBytes c.max_vars ≤ 2 ^ 64)
    (hm : MemShrinkResU32A c s m) :
    region c.pFlags (8 * u32FullBytes c.max_vars) m := by
  have hu_ge : 4 * c.max_vars ≤ u32FullBytes c.max_vars := by unfold u32FullBytes; omega
  rw [MemShrinkResU32A_eq] at hm
  have hr0 : (region c.pFlags (u32FullBytes c.max_vars) ⋆ region c.pLevel (u32FullBytes c.max_vars) ⋆
      region c.pReason (u32FullBytes c.max_vars) ⋆ region c.pTrail (u32FullBytes c.max_vars) ⋆
      region c.pTrailPos (u32FullBytes c.max_vars) ⋆ region c.pTmp (u32FullBytes c.max_vars) ⋆
      region c.pHeap (u32FullBytes c.max_vars) ⋆ region c.pPos (u32FullBytes c.max_vars)) m := by
    refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ hx => ms_pad_merge_i32_len hlen.flags_len hu_ge (by omega) hx)
      (fun _ hx => ms_pad_merge_i32_len hlen.lvl_len hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.rsns_len hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.trl_len hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.trail_pos_len hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.tmp_len_arr hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.heap_len_arr hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.pos_len hu_ge (by omega) hx) m hm
  have hr : (region c.pFlags (u32FullBytes c.max_vars) ⋆ (region c.pLevel (u32FullBytes c.max_vars) ⋆
      (region c.pReason (u32FullBytes c.max_vars) ⋆ (region c.pTrail (u32FullBytes c.max_vars) ⋆
      (region c.pTrailPos (u32FullBytes c.max_vars) ⋆ (region c.pTmp (u32FullBytes c.max_vars) ⋆
      (region c.pHeap (u32FullBytes c.max_vars) ⋆ region c.pPos (u32FullBytes c.max_vars)))))))) m :=
    sep_ac hr0
  have a1 := MemShrinkCfg.pLevel_eq c
  have s1 := ms_step_reg hr a1 (by omega)
  have a2 := ms_add_step a1 (MemShrinkCfg.pReason_eq c)
  have s2 := ms_step_reg s1 a2 (by omega)
  have a3 := ms_add_step a2 (MemShrinkCfg.pTrail_eq c)
  have s3 := ms_step_reg s2 a3 (by omega)
  have a4 := ms_add_step a3 (MemShrinkCfg.pTrailPos_eq c)
  have s4 := ms_step_reg s3 a4 (by omega)
  have a5 := ms_add_step a4 (MemShrinkCfg.pTmp_eq c)
  have s5 := ms_step_reg s4 a5 (by omega)
  have a6 := ms_add_step a5 (MemShrinkCfg.pHeap_eq c)
  have s6 := ms_step_reg s5 a6 (by omega)
  have a7 := ms_add_step a6 (MemShrinkCfg.pPos_eq c)
  have s7 := ms_step_reg2 s6 a7 (by omega)
  simpa only [show u32FullBytes c.max_vars + u32FullBytes c.max_vars + u32FullBytes c.max_vars +
      u32FullBytes c.max_vars + u32FullBytes c.max_vars + u32FullBytes c.max_vars +
      u32FullBytes c.max_vars + u32FullBytes c.max_vars =
      8 * u32FullBytes c.max_vars by omega] using s7

private theorem ms_segU32B_to_reg (c : MemShrinkCfg) {s : FullState} {m : Mem 64}
    (hlen : MemShrinkLengthsOk c s) (hfit : 7 * u32FullBytes c.max_vars ≤ 2 ^ 64)
    (hm : MemShrinkResU32B c s m) :
    region c.pMinClr (7 * u32FullBytes c.max_vars) m := by
  have hu_ge : 4 * c.max_vars ≤ u32FullBytes c.max_vars := by unfold u32FullBytes; omega
  have hu1_ge : 4 * (c.max_vars + 1) ≤ u32FullBytes c.max_vars := by unfold u32FullBytes; omega
  rw [MemShrinkResU32B_eq] at hm
  have hr0 : (region c.pMinClr (u32FullBytes c.max_vars) ⋆
      region c.pShrinkStk (u32FullBytes c.max_vars) ⋆ region c.pQPrev (u32FullBytes c.max_vars) ⋆
      region c.pQNext (u32FullBytes c.max_vars) ⋆ region c.pQStamp (u32FullBytes c.max_vars) ⋆
      region c.pFrameTrail (u32FullBytes c.max_vars) ⋆
      region c.pFrameDec (u32FullBytes c.max_vars)) m := by
    refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ hx => ms_pad_merge_i32_len hlen.min_clr_len_arr hu_ge (by omega) hx)
      (fun _ hx => ms_pad_merge_i32_len hlen.shrink_stk_len hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.q_prev_len hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.q_next_len hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.q_stamp_len hu_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.frame_trail_len hu1_ge (by omega) hx))
      (fun _ hx => ms_pad_merge_i32_len hlen.frame_dec_len hu1_ge (by omega) hx) m hm
  have hr : (region c.pMinClr (u32FullBytes c.max_vars) ⋆
      (region c.pShrinkStk (u32FullBytes c.max_vars) ⋆ (region c.pQPrev (u32FullBytes c.max_vars) ⋆
      (region c.pQNext (u32FullBytes c.max_vars) ⋆ (region c.pQStamp (u32FullBytes c.max_vars) ⋆
      (region c.pFrameTrail (u32FullBytes c.max_vars) ⋆
      region c.pFrameDec (u32FullBytes c.max_vars))))))) m := sep_ac hr0
  have a1 := MemShrinkCfg.pShrinkStk_eq c
  have s1 := ms_step_reg hr a1 (by omega)
  have a2 := ms_add_step a1 (MemShrinkCfg.pQPrev_eq c)
  have s2 := ms_step_reg s1 a2 (by omega)
  have a3 := ms_add_step a2 (MemShrinkCfg.pQNext_eq c)
  have s3 := ms_step_reg s2 a3 (by omega)
  have a4 := ms_add_step a3 (MemShrinkCfg.pQStamp_eq c)
  have s4 := ms_step_reg s3 a4 (by omega)
  have a5 := ms_add_step a4 (MemShrinkCfg.pFrameTrail_eq c)
  have s5 := ms_step_reg s4 a5 (by omega)
  have a6 := ms_add_step a5 (MemShrinkCfg.pFrameDec_eq c)
  have s6 := ms_step_reg2 s5 a6 (by omega)
  simpa only [show u32FullBytes c.max_vars + u32FullBytes c.max_vars + u32FullBytes c.max_vars +
      u32FullBytes c.max_vars + u32FullBytes c.max_vars + u32FullBytes c.max_vars +
      u32FullBytes c.max_vars = 7 * u32FullBytes c.max_vars by omega] using s6

private theorem ms_segTail_to_reg (c : MemShrinkCfg) {s : FullState} {m : Mem 64}
    (hlen : MemShrinkLengthsOk c s)
    (hfit : 24 * c.max_vars + 8 * c.minDepth + 320 + 4 * c.arena_cap + 4 * c.wcap +
      12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap ≤ 2 ^ 64)
    (hm : MemShrinkResTail c s m) :
    region c.pWvec (24 * c.max_vars + 8 * c.minDepth + 320 + 4 * c.arena_cap + 4 * c.wcap +
      12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap) m := by
  have hm_pre :
      (region c.pWvec (16 * c.max_vars) ⋆ region c.pScore (8 * c.max_vars) ⋆
       region c.pMinStk (8 * c.minDepth) ⋆ region c.pGlueUsed 256 ⋆ region c.pLastLearned 64 ⋆
       region c.pArena (4 * c.arena_cap) ⋆ region c.pWstk (4 * c.wcap) ⋆
       region c.pDelayed (12 * c.delayed_cap) ⋆ region c.pRedRefs (4 * c.red_cap) ⋆
       region c.pExtendStk (4 * c.extend_cap) ⋆ region c.pScratchBuf (4 * c.scratch_cap)) m := by
    rw [MemShrinkResTail_eq] at hm
    refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (sep_mono2 (sep_mono2
      (fun _ ha => by
        simpa [hlen.wvec_len, show 4 * (4 * c.max_vars) = 16 * c.max_vars by omega] using
          i32_exact_to_reg (by rw [hlen.wvec_len]; omega) ha)
      (fun _ ha => by
        simpa [hlen.score_len] using i64_exact_to_reg (by rw [hlen.score_len]; omega) ha))
      (fun _ ha => by
        simpa [hlen.min_stk_len, show 4 * (2 * c.minDepth) = 8 * c.minDepth by omega] using
          i32_exact_to_reg (by rw [hlen.min_stk_len]; omega) ha))
      (fun _ ha => by
        simpa [hlen.glue_used_len] using i32_exact_to_reg (by rw [hlen.glue_used_len]; omega) ha))
      (fun _ ha => by
        simpa [hlen.last_learned_len] using
          i32_exact_to_reg (by rw [hlen.last_learned_len]; omega) ha))
      (fun _ ha => by
        simpa [hlen.arena_len_arr] using
          i32_exact_to_reg (by rw [hlen.arena_len_arr]; omega) ha))
      (fun _ ha => by
        simpa [hlen.wstk_len_arr] using
          i32_exact_to_reg (by rw [hlen.wstk_len_arr]; omega) ha))
      (fun _ ha => by
        simpa [hlen.delayed_len_arr, show 4 * (3 * c.delayed_cap) = 12 * c.delayed_cap by omega]
          using i32_exact_to_reg (by rw [hlen.delayed_len_arr]; omega) ha))
      (fun _ ha => by
        simpa [hlen.red_refs_len] using i32_exact_to_reg (by rw [hlen.red_refs_len]; omega) ha))
      (fun _ ha => by
        simpa [hlen.extend_stk_len] using
          i32_exact_to_reg (by rw [hlen.extend_stk_len]; omega) ha))
      (fun _ ha => by
        simpa [hlen.scratch_buf_len] using
          i32_exact_to_reg (by rw [hlen.scratch_buf_len]; omega) ha) m hm
  have hrA0 : (region c.pWvec (16 * c.max_vars) ⋆ (region c.pScore (8 * c.max_vars) ⋆
      (region c.pMinStk (8 * c.minDepth) ⋆ (region c.pGlueUsed 256 ⋆ region c.pLastLearned 64))) ⋆
      (region c.pArena (4 * c.arena_cap) ⋆ (region c.pWstk (4 * c.wcap) ⋆
      (region c.pDelayed (12 * c.delayed_cap) ⋆ (region c.pRedRefs (4 * c.red_cap) ⋆
      (region c.pExtendStk (4 * c.extend_cap) ⋆ region c.pScratchBuf (4 * c.scratch_cap))))))) m :=
    sep_ac hm_pre
  have hA : ∀ x, (region c.pWvec (16 * c.max_vars) ⋆ (region c.pScore (8 * c.max_vars) ⋆
      (region c.pMinStk (8 * c.minDepth) ⋆ (region c.pGlueUsed 256 ⋆
      region c.pLastLearned 64)))) x →
      region c.pWvec (24 * c.max_vars + 8 * c.minDepth + 320) x := fun x hx => by
    have a1 := MemShrinkCfg.pScore_eq c
    have s1 := ms_step_reg hx a1 (by omega)
    have a2 := ms_add_step a1 (MemShrinkCfg.pMinStk_eq c)
    have s2 := ms_step_reg s1 a2 (by omega)
    have a3 := ms_add_step a2 (MemShrinkCfg.pGlueUsed_eq c)
    have s3 := ms_step_reg s2 a3 (by omega)
    have a4 := ms_add_step a3 (MemShrinkCfg.pLastLearned_eq c)
    have s4 := ms_step_reg2 s3 a4 (by omega)
    simpa only [show 16 * c.max_vars + 8 * c.max_vars + 8 * c.minDepth + 256 + 64 =
      24 * c.max_vars + 8 * c.minDepth + 320 by omega] using s4
  have hB : ∀ x, (region c.pArena (4 * c.arena_cap) ⋆ (region c.pWstk (4 * c.wcap) ⋆
      (region c.pDelayed (12 * c.delayed_cap) ⋆ (region c.pRedRefs (4 * c.red_cap) ⋆
      (region c.pExtendStk (4 * c.extend_cap) ⋆ region c.pScratchBuf (4 * c.scratch_cap)))))) x →
      region c.pArena (4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
        4 * c.extend_cap + 4 * c.scratch_cap) x := fun x hx => by
    have b1 := MemShrinkCfg.pWstk_eq c
    have t1 := ms_step_reg hx b1 (by omega)
    have b2 := ms_add_step b1 (MemShrinkCfg.pDelayed_eq c)
    have t2 := ms_step_reg t1 b2 (by omega)
    have b3 := ms_add_step b2 (MemShrinkCfg.pRedRefs_eq c)
    have t3 := ms_step_reg t2 b3 (by omega)
    have b4 := ms_add_step b3 (MemShrinkCfg.pExtendStk_eq c)
    have t4 := ms_step_reg t3 b4 (by omega)
    have b5 := ms_add_step b4 (MemShrinkCfg.pScratchBuf_eq c)
    exact ms_step_reg2 t4 b5 (by omega)
  have hm2 := sep_mono2 hA hB m hrA0
  have hAr_add : c.pArena =
      c.pWvec + BitVec.ofNat 64 (24 * c.max_vars + 8 * c.minDepth + 320) := by
    have a1 := MemShrinkCfg.pScore_eq c
    have a2 := ms_add_step a1 (MemShrinkCfg.pMinStk_eq c)
    have a3 := ms_add_step a2 (MemShrinkCfg.pGlueUsed_eq c)
    have a4 := ms_add_step a3 (MemShrinkCfg.pLastLearned_eq c)
    have a5 := ms_add_step a4 (MemShrinkCfg.pArena_eq c)
    simpa only [show 16 * c.max_vars + 8 * c.max_vars + 8 * c.minDepth + 256 + 64 =
      24 * c.max_vars + 8 * c.minDepth + 320 by omega] using a5
  simpa only [Nat.add_assoc] using ms_step_reg2 hm2 hAr_add (by omega)

private theorem ms_segTrans_to_reg (c : MemShrinkCfg) {s : FullState} {m : Mem 64}
    (hlen : MemShrinkLengthsOk c s)
    (hfit : m7TransBytes c.max_vars + c.slack ≤ 2 ^ 64)
    (hm : (MemShrinkLitMark c s ⋆ MemShrinkTransRegions c ⋆ region c.pSlack c.slack) m) :
    region c.pTrans (m7TransBytes c.max_vars + c.slack) m := by
  have hv_ge : 2 * c.max_vars ≤ valsBytes c.max_vars := by unfold valsBytes; omega
  have htb : m7TransBytes c.max_vars = 56 * c.max_vars + valsBytes c.max_vars :=
    m7TransBytes_def c.max_vars
  rw [MemShrinkLitMark_eq, MemShrinkTransRegions_eq] at hm
  have hm_lit : ((array (t := i8) c.pLitMark s.core.lit_mark ⋆
      region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
        (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
      (region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
       region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
       region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
       region c.pSimSig (8 * c.max_vars) ⋆ region c.pSlack c.slack)) m := sep_ac hm
  have hm0 : (region c.pWsort (8 * c.max_vars) ⋆ (region c.pWorkStk1 (8 * c.max_vars) ⋆
      (region c.pWorkStk2 (8 * c.max_vars) ⋆ (region c.pTarjanMark (8 * c.max_vars) ⋆
      (region c.pTarjanReach (8 * c.max_vars) ⋆ (region c.pRepr (8 * c.max_vars) ⋆
      (region c.pSimSig (8 * c.max_vars) ⋆ (region c.pLitMark (valsBytes c.max_vars) ⋆
       region c.pSlack c.slack)))))))) m := by
    have hm1 :
        (region c.pLitMark (valsBytes c.max_vars) ⋆
          (region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
           region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
           region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
           region c.pSimSig (8 * c.max_vars) ⋆ region c.pSlack c.slack)) m :=
      sep_mono (fun _ hx => ms_pad_merge_i8_len hlen.lit_mark_len hv_ge (by omega) hx) hm_lit
    exact sep_ac hm1
  rw [MemShrinkCfg.pWsort_eq] at hm0
  have a1 := MemShrinkCfg.pWorkStk1_eq c
  have s1 := ms_step_reg hm0 a1 (by omega)
  have a2 := ms_add_step a1 (MemShrinkCfg.pWorkStk2_eq c)
  have s2 := ms_step_reg s1 a2 (by omega)
  have a3 := ms_add_step a2 (MemShrinkCfg.pTarjanMark_eq c)
  have s3 := ms_step_reg s2 a3 (by omega)
  have a4 := ms_add_step a3 (MemShrinkCfg.pTarjanReach_eq c)
  have s4 := ms_step_reg s3 a4 (by omega)
  have a5 := ms_add_step a4 (MemShrinkCfg.pRepr_eq c)
  have s5 := ms_step_reg s4 a5 (by omega)
  have a6 := ms_add_step a5 (MemShrinkCfg.pSimSig_eq c)
  have s6 := ms_step_reg s5 a6 (by omega)
  have a7 := ms_add_step a6 (MemShrinkCfg.pLitMark_eq c)
  have s7 := ms_step_reg s6 a7 (by omega)
  have a8 := ms_add_step a7 (MemShrinkCfg.pSlack_eq c)
  have s8 := ms_step_reg2 s7 a8 (by omega)
  simpa only [htb, show 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars +
      8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + valsBytes c.max_vars + c.slack =
      56 * c.max_vars + valsBytes c.max_vars + c.slack by omega] using s8

/-- Collapses `MemShrinkMem c s` (`1,152 B` header + `90 B/var` fixed + dynamic + `58 B/var`
transient + `c.slack`) back into a single contiguous workspace `region c.hdr c.avail`. -/
theorem memShrinkMem_to_region {c : MemShrinkCfg} {s : FullState} {m : Mem 64}
    (hlen : MemShrinkLengthsOk c s) (hm : MemShrinkMem c s m) :
    region c.hdr c.avail m := by
  have hfit := c.havail_fit
  have hsz := c.hsize
  have hmd_le : c.minDepth ≤ 1000 := by
    rw [MemShrinkCfg.minDepth_eq]; exact fullMinDepthOf_le c.max_vars
  have hfb : m7FixedBytes c.max_vars = 1472 + valsBytes c.max_vars + 4 * markBytes c.max_vars +
      15 * u32FullBytes c.max_vars + 24 * c.max_vars + 8 * c.minDepth := by
    rw [m7FixedBytes_def, MemShrinkCfg.minDepth_eq]; omega
  have htb : m7TransBytes c.max_vars = 56 * c.max_vars + valsBytes c.max_vars :=
    m7TransBytes_def c.max_vars
  have htot_le : m7FixedBytes c.max_vars + m7TransBytes c.max_vars + 4 * c.arena_cap + 4 * c.wcap +
      12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + c.slack =
      c.avail := by
    rw [MemShrinkCfg.slack_eq]; omega
  rw [MemShrinkMem_eq, MemShrinkResArrays_eq] at hm
  have hm0 : (region c.hdr 32 ⋆ (region (c.hdr + 32) 1120 ⋆
      (region c.pVals (valsBytes c.max_vars + 4 * markBytes c.max_vars) ⋆
      (region c.pFlags (8 * u32FullBytes c.max_vars) ⋆
      (region c.pMinClr (7 * u32FullBytes c.max_vars) ⋆
      (region c.pWvec (24 * c.max_vars + 8 * c.minDepth + 320 + 4 * c.arena_cap + 4 * c.wcap +
        12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap) ⋆
       region c.pTrans (m7TransBytes c.max_vars + c.slack))))))) m := by
    have hm1 : ((dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (m7HdrTailWords c s)) ⋆
        ((((MemShrinkResBytes c s ⋆ MemShrinkResU32A c s) ⋆ MemShrinkResU32B c s) ⋆
          MemShrinkResTail c s) ⋆
         (MemShrinkLitMark c s ⋆ MemShrinkTransRegions c ⋆ region c.pSlack c.slack))) m :=
      sep_ac hm
    have hb : ∀ x, MemShrinkResBytes c s x →
        region c.pVals (valsBytes c.max_vars + 4 * markBytes c.max_vars) x :=
      fun _ h => ms_segBytes_to_reg c hlen (by omega) h
    have hua : ∀ x, MemShrinkResU32A c s x → region c.pFlags (8 * u32FullBytes c.max_vars) x :=
      fun _ h => ms_segU32A_to_reg c hlen (by omega) h
    have hub : ∀ x, MemShrinkResU32B c s x → region c.pMinClr (7 * u32FullBytes c.max_vars) x :=
      fun _ h => ms_segU32B_to_reg c hlen (by omega) h
    have htl : ∀ x, MemShrinkResTail c s x →
        region c.pWvec (24 * c.max_vars + 8 * c.minDepth + 320 + 4 * c.arena_cap + 4 * c.wcap +
          12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap) x :=
      fun _ h => ms_segTail_to_reg c hlen (by omega) h
    have htr : ∀ x, (MemShrinkLitMark c s ⋆ MemShrinkTransRegions c ⋆ region c.pSlack c.slack) x →
        region c.pTrans (m7TransBytes c.max_vars + c.slack) x :=
      fun _ h => ms_segTrans_to_reg c hlen (by omega) h
    have hc : ∀ x, (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (m7HdrTailWords c s)) x →
        (region c.hdr 32 ⋆ region (c.hdr + 32) 1120) x :=
      sep_mono2 (fun _ => dimacsState_to_region)
        (fun _ ha => by
          have htl_len : (m7HdrTailWords c s).length = 140 := m7HdrTailWords_length c s
          simpa [htl_len] using i64_exact_to_reg (by omega) ha)
    have hres := sep_mono2 (sep_mono2 (sep_mono2 hb hua) hub) htl
    have hall := sep_mono2 hc (sep_mono2 hres htr) m hm1
    exact sep_ac hall
  have r1 := ms_step_reg hm0 (rfl : c.hdr + 32 = c.hdr + BitVec.ofNat 64 32) (by omega)
  have aV : c.pVals = c.hdr + BitVec.ofNat 64 (32 + 1120) := MemShrinkCfg.pVals_eq c
  have r2 := ms_step_reg r1 aV (by omega)
  have aFl : c.pFlags = c.hdr + BitVec.ofNat 64 (32 + 1120 + (valsBytes c.max_vars +
      4 * markBytes c.max_vars)) := by
    have h1 := ms_add_step aV (MemShrinkCfg.pMark_eq c)
    have h2 := ms_add_step h1 (MemShrinkCfg.pPhases_eq c)
    have h3 := ms_add_step h2 (MemShrinkCfg.pPhasesTarget_eq c)
    have h4 := ms_add_step h3 (MemShrinkCfg.pPhasesBest_eq c)
    have h5 := ms_add_step h4 (MemShrinkCfg.pFlags_eq c)
    simpa only [show 32 + 1120 + valsBytes c.max_vars + markBytes c.max_vars +
      markBytes c.max_vars + markBytes c.max_vars + markBytes c.max_vars =
      32 + 1120 + (valsBytes c.max_vars + 4 * markBytes c.max_vars) by omega] using h5
  have r3 := ms_step_reg r2 aFl (by omega)
  have aMC : c.pMinClr = c.hdr + BitVec.ofNat 64 (32 + 1120 + (valsBytes c.max_vars +
      4 * markBytes c.max_vars) + 8 * u32FullBytes c.max_vars) := by
    have h1 := ms_add_step aFl (MemShrinkCfg.pLevel_eq c)
    have h2 := ms_add_step h1 (MemShrinkCfg.pReason_eq c)
    have h3 := ms_add_step h2 (MemShrinkCfg.pTrail_eq c)
    have h4 := ms_add_step h3 (MemShrinkCfg.pTrailPos_eq c)
    have h5 := ms_add_step h4 (MemShrinkCfg.pTmp_eq c)
    have h6 := ms_add_step h5 (MemShrinkCfg.pHeap_eq c)
    have h7 := ms_add_step h6 (MemShrinkCfg.pPos_eq c)
    have h8 := ms_add_step h7 (MemShrinkCfg.pMinClr_eq c)
    simpa only [Nat.add_assoc, show u32FullBytes c.max_vars + (u32FullBytes c.max_vars +
      (u32FullBytes c.max_vars + (u32FullBytes c.max_vars + (u32FullBytes c.max_vars +
      (u32FullBytes c.max_vars + (u32FullBytes c.max_vars + u32FullBytes c.max_vars)))))) =
      8 * u32FullBytes c.max_vars by omega] using h8
  have r4 := ms_step_reg r3 aMC (by omega)
  have aWv : c.pWvec = c.hdr + BitVec.ofNat 64 (32 + 1120 + (valsBytes c.max_vars +
      4 * markBytes c.max_vars) + 8 * u32FullBytes c.max_vars + 7 * u32FullBytes c.max_vars) := by
    have h1 := ms_add_step aMC (MemShrinkCfg.pShrinkStk_eq c)
    have h2 := ms_add_step h1 (MemShrinkCfg.pQPrev_eq c)
    have h3 := ms_add_step h2 (MemShrinkCfg.pQNext_eq c)
    have h4 := ms_add_step h3 (MemShrinkCfg.pQStamp_eq c)
    have h5 := ms_add_step h4 (MemShrinkCfg.pFrameTrail_eq c)
    have h6 := ms_add_step h5 (MemShrinkCfg.pFrameDec_eq c)
    have h7 := ms_add_step h6 (MemShrinkCfg.pWvec_eq c)
    simpa only [Nat.add_assoc, show u32FullBytes c.max_vars + (u32FullBytes c.max_vars +
      (u32FullBytes c.max_vars + (u32FullBytes c.max_vars + (u32FullBytes c.max_vars +
      (u32FullBytes c.max_vars + u32FullBytes c.max_vars))))) =
      7 * u32FullBytes c.max_vars by omega] using h7
  have r5 := ms_step_reg r4 aWv (by omega)
  have aTr : c.pTrans = c.hdr + BitVec.ofNat 64 (32 + 1120 + (valsBytes c.max_vars +
      4 * markBytes c.max_vars) + 8 * u32FullBytes c.max_vars + 7 * u32FullBytes c.max_vars +
      (24 * c.max_vars + 8 * c.minDepth + 320 + 4 * c.arena_cap + 4 * c.wcap +
      12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap)) := by
    have h1 := ms_add_step aWv (MemShrinkCfg.pScore_eq c)
    have h2 := ms_add_step h1 (MemShrinkCfg.pMinStk_eq c)
    have h3 := ms_add_step h2 (MemShrinkCfg.pGlueUsed_eq c)
    have h4 := ms_add_step h3 (MemShrinkCfg.pLastLearned_eq c)
    have h5 := ms_add_step h4 (MemShrinkCfg.pArena_eq c)
    have h6 := ms_add_step h5 (MemShrinkCfg.pWstk_eq c)
    have h7 := ms_add_step h6 (MemShrinkCfg.pDelayed_eq c)
    have h8 := ms_add_step h7 (MemShrinkCfg.pRedRefs_eq c)
    have h9 := ms_add_step h8 (MemShrinkCfg.pExtendStk_eq c)
    have h10 := ms_add_step h9 (MemShrinkCfg.pScratchBuf_eq c)
    have h11 := ms_add_step h10 (MemShrinkCfg.pTrans_eq c)
    simpa only [Nat.add_assoc, show 16 * c.max_vars + (8 * c.max_vars + (8 * c.minDepth +
      (256 + (64 + (4 * c.arena_cap + (4 * c.wcap + (12 * c.delayed_cap +
      (4 * c.red_cap + (4 * c.extend_cap + 4 * c.scratch_cap))))))))) =
      24 * c.max_vars + 8 * c.minDepth + 320 + 4 * c.arena_cap + 4 * c.wcap +
      12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap by omega]
      using h11
  have r6 := ms_step_reg2 r5 aTr (by omega)
  simpa only [show 32 + 1120 + (valsBytes c.max_vars + 4 * markBytes c.max_vars) +
      8 * u32FullBytes c.max_vars + 7 * u32FullBytes c.max_vars +
      (24 * c.max_vars + 8 * c.minDepth + 320 + 4 * c.arena_cap + 4 * c.wcap +
      12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap) +
      (m7TransBytes c.max_vars + c.slack) = c.avail by omega] using r6

/-- Collapses `MemShrinkM6HdrMem c ext s` (`2,304 B` `M6HdrExt` + `MemShrinkMem c s`) into
`region (m6ExtAddr c.hdr) (fullM6ExtBytes + c.avail)`. -/
theorem memShrinkM6HdrMem_to_region {c : MemShrinkCfg} {ext : List (BitVec 64)} {s : FullState}
    {m : Mem 64} (hcfg : MemShrinkM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hlen : MemShrinkLengthsOk c s) (hm : MemShrinkM6HdrMem c ext s m) :
    region (m6ExtAddr c.hdr) (fullM6ExtBytes + c.avail) m := by
  unfold MemShrinkM6HdrMem at hm
  have hfit : fullM6ExtBytes + c.avail ≤ 2 ^ 64 := by
    have := c.havail_fit; unfold MemShrinkM6HdrCfgOk at hcfg; omega
  have hreg : (region (m6ExtAddr c.hdr) fullM6ExtBytes ⋆ region c.hdr c.avail) m := by
    refine sep_mono2 (fun _ hf => ?_) (fun _ hf => memShrinkMem_to_region hlen hf) m hm
    have h1 := array_to_region (t := i64) (xs := ext)
      (by simp [Ty.bytes, Ty.size, i64, hext.len]) ((array64_eq_array _ ext) ▸ hf)
    simpa [Ty.bytes, Ty.size, i64, hext.len, fullM6ExtBytes] using h1
  have hreg' : (region (m6ExtAddr c.hdr) fullM6ExtBytes ⋆
      region (m6ExtAddr c.hdr + BitVec.ofNat 64 fullM6ExtBytes) c.avail) m := by
    rwa [m6ExtAddr_add_bytes c.hdr]
  have hmg := region_merge_eq (a := m6ExtAddr c.hdr) (n1 := fullM6ExtBytes) (n2 := c.avail)
    rfl hfit
  rw [hmg] at hreg'
  exact hreg'

/-- Initialized `M6HdrExt` predicate (`ext.length = 288` and `ext[0]? = some fullM6HdrMagic`). -/
def MsM6HdrExtInitOk (ext : List (BitVec 64)) : Prop :=
  ext.length = fullM6ExtWords ∧ ext[0]? = some fullM6HdrMagic

theorem MsM6HdrExtInitOk.toOk {ext : List (BitVec 64)} (h : MsM6HdrExtInitOk ext) :
    M6HdrExtOk ext :=
  M6HdrExtOk.of_len h.1

def m6HdrInitMsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ MemShrinkM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ MemShrinkLengthsOk c s ∧
    (MemShrinkM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' m', MsM6HdrExtInitOk ext' → (MemShrinkM6HdrMem c ext' s ⋆ R) m' → Q () m'

def fullM6MemInitMsSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cend, work_base, avail, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_base.toNat + avail.toNat < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m' →
        (avail.toNat < fullM6HdrTotalBytes ∨
          ∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
            avail.toNat - fullM6ExtBytes < m7FixedBytes mv + m7TransBytes mv + nc * 40 + 136) →
        Q (0#64, ()) m') ∧
      (∀ (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState) (j : Nat) (rest : List UInt8)
          (m' : Mem 64),
        c.hdr = work_base + BitVec.ofNat 64 fullM6ExtBytes →
        c.avail = avail.toNat - fullM6ExtBytes →
        MemShrinkM6HdrInv c ext s → MsM6HdrExtInitOk ext →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        s.core.cur_vars = c.mv → s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
        s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
        s.core.oom = 0#64 → s.core.inconsistent = 0#64 →
        (bytes cnf_ptr cnfBytes ⋆ MemShrinkM6HdrMem c ext s ⋆ R) m' →
        Q (c.hdr, ()) m')

theorem m6HdrInitMsSpec_of {c : MemShrinkCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : MemShrinkM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : MemShrinkLengthsOk c s)
    (hm : (MemShrinkM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' m', MsM6HdrExtInitOk ext' → (MemShrinkM6HdrMem c ext' s ⋆ R) m' → Q () m') :
    m6HdrInitMsSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩

theorem m6HdrInitMsSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m6HdrInitMsSpec xs m Q X) : m6HdrInitMsSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem fullM6MemInitMsSpec_of {cnf_ptr cend work_base avail fuel : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcend : cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_base.toNat + avail.toNat < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m)
    (hFail : ∀ m', (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m' →
      (avail.toNat < fullM6HdrTotalBytes ∨
        ∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat - fullM6ExtBytes < m7FixedBytes mv + m7TransBytes mv + nc * 40 + 136) →
      Q (0#64, ()) m')
    (hOk : ∀ (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState) (j : Nat) (rest : List UInt8)
        (m' : Mem 64),
      c.hdr = work_base + BitVec.ofNat 64 fullM6ExtBytes →
      c.avail = avail.toNat - fullM6ExtBytes →
      MemShrinkM6HdrInv c ext s → MsM6HdrExtInitOk ext →
      parseHeader cnfBytes = some (c.mv, c.nc, rest) →
      j ≤ cnfBytes.length → cnfBytes.drop j = rest →
      s.core.cur_vars = c.mv → s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
      s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
      s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
      s.core.oom = 0#64 → s.core.inconsistent = 0#64 →
      (bytes cnf_ptr cnfBytes ⋆ MemShrinkM6HdrMem c ext s ⋆ R) m' →
      Q (c.hdr, ()) m') :
    fullM6MemInitMsSpec (cnf_ptr, cend, work_base, avail, fuel, ()) m Q X :=
  ⟨cnfBytes, R, hcend, hfit, hwfit, hm, hFail, hOk⟩

theorem fullM6MemInitMsSpec_monoX {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost}
    (h : fullM6MemInitMsSpec xs m Q X) : fullM6MemInitMsSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

namespace MsM6Tactics

private theorem m8_eq (a i : BitVec 64) : a + i * 8 = a + BitVec.ofNat 64 (8 * i.toNat) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]

private theorem shl3_eq {a i : BitVec 64} (hi : i.toNat < 2 ^ 61) :
    a + (i <<< (((3 : BitVec 32).signExtend 64).toNat % 64)) =
      a + BitVec.ofNat 64 (8 * i.toNat) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [show ((3 : BitVec 32).signExtend 64).toNat % 64 = 3 from rfl,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem ms_hdr_load {c : MemShrinkCfg} {s : FullState} {F : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 140) (off v : BitVec 64)
    (hv : (m7HdrTailWords c s)[i]? = some v)
    (hoff : c.hdr + off = (c.hdr + 32) + BitVec.ofNat 64 (8 * i))
    (hm : (MemShrinkMem c s ⋆ F) m) : loadVal m i64 (c.hdr + off) = some v := by
  have hi_len : i < (m7HdrTailWords c s).length := by rw [m7HdrTailWords_length]; exact hi
  have heq : (m7HdrTailWords c s)[i]'hi_len = v := by
    simpa [List.getElem?_eq_getElem hi_len] using hv
  rw [MemShrinkMem_eq] at hm
  have h1 : (array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        MemShrinkResArrays c s ⋆ MemShrinkLitMark c s ⋆ MemShrinkTransRegions c ⋆
        region c.pSlack c.slack ⋆ F)) m := sep_ac hm
  rw [hoff, ← heq]; exact loadVal_array64 hi_len h1

@[scoped c0_load] theorem load_ms_switched {c : MemShrinkCfg} {s : FullState}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (MemShrinkMem c s ⋆ F) m) :
    loadVal m i64 (c.hdr + 560) = some s.scratch.switched := by
  refine ms_hdr_load 66 (by omega) 560 _ ?_ (by rw [BitVec.add_assoc]; rfl) hm
  simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq, m7HdrTailWords2_eq,
    m7HdrTailWords3_eq]; rfl

@[scoped c0_load] theorem load_ms_fwd_sub_cnt {c : MemShrinkCfg} {s : FullState}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (MemShrinkMem c s ⋆ F) m) :
    loadVal m i64 (c.hdr + 1120) = some s.scratch.fwd_sub_cnt := by
  refine ms_hdr_load 136 (by omega) 1120 _ ?_ (by rw [BitVec.add_assoc]; rfl) hm
  simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq, m7HdrTailWords2_eq,
    m7HdrTailWords3_eq]; rfl

@[scoped c0_load] theorem load_ms_fwd_str_cnt {c : MemShrinkCfg} {s : FullState}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (MemShrinkMem c s ⋆ F) m) :
    loadVal m i64 (c.hdr + 1128) = some s.scratch.fwd_str_cnt := by
  refine ms_hdr_load 137 (by omega) 1128 _ ?_ (by rw [BitVec.add_assoc]; rfl) hm
  simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq, m7HdrTailWords2_eq,
    m7HdrTailWords3_eq]; rfl

@[scoped c0_load] theorem load_ms_m6Ext_mul8 {c : MemShrinkCfg} {s : FullState} {a i : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : i.toNat < ext.length) :
    loadVal m i64 (a + i * 8) = some (ext[i.toNat]'hi) := by
  rw [m8_eq]; exact loadVal_array64 hi (sep_swap_ms hm)

@[scoped c0_store] theorem store_ms_m6Ext_mul8 {c : MemShrinkCfg} {s : FullState} {a i : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : i.toNat < ext.length) :
    storeOk m i64 (a + i * 8) ∧
      (MemShrinkMem c s ⋆ (array64 a (ext.set i.toNat v) ⋆ R)) (storeMem m i64 (a + i * 8) v) := by
  rw [m8_eq]
  obtain ⟨hok, hst⟩ := store_array64 v hi (sep_swap_ms hm)
  exact ⟨hok, sep_swap_ms hst⟩

@[scoped c0_load] theorem load_ms_m6Ext_zero {c : MemShrinkCfg} {s : FullState} {a : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : 0 < ext.length) :
    loadVal m i64 a = some (ext[0]'hi) := by
  simpa using loadVal_array64 (i := 0) hi (sep_swap_ms hm)

@[scoped c0_store] theorem store_ms_m6Ext_zero {c : MemShrinkCfg} {s : FullState} {a : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : 0 < ext.length) :
    storeOk m i64 a ∧
      (MemShrinkMem c s ⋆ (array64 a (ext.set 0 v) ⋆ R)) (storeMem m i64 a v) := by
  obtain ⟨hok, hst⟩ := store_array64 (i := 0) v hi (sep_swap_ms hm)
  exact ⟨by simpa using hok, by simpa using sep_swap_ms hst⟩

@[scoped c0_load] theorem load_ms_m6Ext_add0 {c : MemShrinkCfg} {s : FullState} {a : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : 0 < ext.length) :
    loadVal m i64 (a + 0) = some (ext[0]'hi) := by
  simpa using load_ms_m6Ext_zero hm hi

@[scoped c0_store] theorem store_ms_m6Ext_add0 {c : MemShrinkCfg} {s : FullState} {a : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : 0 < ext.length) :
    storeOk m i64 (a + 0) ∧
      (MemShrinkMem c s ⋆ (array64 a (ext.set 0 v) ⋆ R)) (storeMem m i64 (a + 0) v) := by
  simpa using store_ms_m6Ext_zero v hm hi

@[scoped c0_load] theorem load_ms_m6Ext_shl3 {c : MemShrinkCfg} {s : FullState} {a i : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : i.toNat < ext.length)
    (hb : i.toNat < 2 ^ 61) :
    loadVal m i64 (a + (i <<< (((3 : BitVec 32).signExtend 64).toNat % 64))) =
      some (ext[i.toNat]'hi) := by
  rw [shl3_eq hb]; exact loadVal_array64 hi (sep_swap_ms hm)

@[scoped c0_store] theorem store_ms_m6Ext_shl3 {c : MemShrinkCfg} {s : FullState} {a i : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : i.toNat < ext.length)
    (hb : i.toNat < 2 ^ 61) :
    storeOk m i64 (a + (i <<< (((3 : BitVec 32).signExtend 64).toNat % 64))) ∧
      (MemShrinkMem c s ⋆ (array64 a (ext.set i.toNat v) ⋆ R))
        (storeMem m i64 (a + (i <<< (((3 : BitVec 32).signExtend 64).toNat % 64))) v) := by
  rw [shl3_eq hb]
  obtain ⟨hok, hst⟩ := store_array64 v hi (sep_swap_ms hm)
  exact ⟨hok, sep_swap_ms hst⟩

@[scoped c0_load] theorem load_ms_m6Ext_const {c : MemShrinkCfg} {s : FullState} {a k : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hmod : k.toNat % 8 = 0)
    (hi : k.toNat / 8 < ext.length) :
    loadVal m i64 (a + k) = some (ext[k.toNat / 8]'hi) := by
  have hk : a + k = a + BitVec.ofNat 64 (8 * (k.toNat / 8)) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  rw [hk]; exact loadVal_array64 hi (sep_swap_ms hm)

@[scoped c0_store] theorem store_ms_m6Ext_const {c : MemShrinkCfg} {s : FullState} {a k : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (MemShrinkMem c s ⋆ (array64 a ext ⋆ R)) m) (hmod : k.toNat % 8 = 0)
    (hi : k.toNat / 8 < ext.length) :
    storeOk m i64 (a + k) ∧
      (MemShrinkMem c s ⋆ (array64 a (ext.set (k.toNat / 8) v) ⋆ R)) (storeMem m i64 (a + k) v) := by
  have hk : a + k = a + BitVec.ofNat 64 (8 * (k.toNat / 8)) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  rw [hk]
  obtain ⟨hok, hst⟩ := store_array64 v hi (sep_swap_ms hm)
  exact ⟨hok, sep_swap_ms hst⟩

end MsM6Tactics

open scoped MsM6Tactics

theorem m6_hdr_init_ms_wp (Γ : Env) :
    ∀ a m Q X, m6HdrInitMsSpec a m Q X → Func.wp Γ m6_hdr_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  rw [memShrinkM6HdrMem_iff, m6ExtAddr_eq] at hm
  unfold Func.wp m6_hdr_init_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (i, ()) m1 => i.toNat ≤ 288 ∧ ∃ ext1 : List (BitVec 64),
      ext1.length = 288 ∧ (MemShrinkMem c s ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) m1)
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
    refine hQ _ _ ?_ ((memShrinkM6HdrMem_iff ..).mpr (by rw [m6ExtAddr_eq]; assumption))
    refine ⟨by simp only [List.length_set, h288, fullM6ExtWords], ?_⟩
    rw [show (0 : BitVec 64).toNat = 0 from rfl,
      List.getElem?_set_self (by simp only [List.length_set, h288]; omega)]
    rfl

private theorem ms_sep_init_split {A B C R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C) ⋆ R) m) : (A ⋆ C ⋆ (B ⋆ R)) m := by
  rw [sep_assoc] at h ⊢
  have h1 : (A ⋆ (B ⋆ (C ⋆ R))) m :=
    sep_mono2 (fun _ x => x) (fun _ x => by rwa [sep_assoc] at x) m h
  exact sep_mono2 (fun _ x => x) (fun _ x => sep_swap_ms x) m h1

private theorem ms_sep_init_merge {A B C R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ C ⋆ (B ⋆ R)) m) : (A ⋆ (B ⋆ C) ⋆ R) m := by
  rw [sep_assoc] at h ⊢
  have h1 : (A ⋆ (B ⋆ (C ⋆ R))) m :=
    sep_mono2 (fun _ x => x) (fun _ x => sep_swap_ms x) m h
  rw [← sep_assoc B C R] at h1
  exact h1

private theorem ms_sep_init_pull_ext {A F E R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ F ⋆ (E ⋆ R)) m) : (E ⋆ (A ⋆ F ⋆ R)) m := by
  rw [sep_assoc] at h
  have h1 : (A ⋆ (E ⋆ (F ⋆ R))) m :=
    sep_mono2 (fun _ x => x) (fun _ x => sep_swap_ms x) m h
  have h2 := sep_swap_ms h1
  rwa [← sep_assoc A F R] at h2

private theorem ms_sep_init_pack {E A F R : Mem 64 → Prop} {m : Mem 64}
    (h : (E ⋆ (A ⋆ F ⋆ R)) m) : ((E ⋆ F) ⋆ (A ⋆ R)) m := by
  have h1 : (E ⋆ (A ⋆ (F ⋆ R))) m := by rwa [sep_assoc A F R] at h
  have h2 := sep_swap_ms h1
  have h3 : (A ⋆ ((E ⋆ F) ⋆ R)) m :=
    sep_mono2 (fun _ x => x) (fun _ x => (congrFun (sep_assoc E F R) _).mpr x) m h2
  exact sep_swap_ms h3

private theorem ms_sep_init_unpack {H A R : Mem 64 → Prop} {m : Mem 64}
    (h : (H ⋆ (A ⋆ R)) m) : (A ⋆ H ⋆ R) m := by
  have h1 := sep_swap_ms h
  rwa [← sep_assoc A H R] at h1

private theorem ms_bv64_max_sub_ult_false {wb av : BitVec 64}
    (hfit : wb.toNat + av.toNat < 2 ^ 64) :
    (((18446744073709551615 : BitVec 64) - av).ult wb) = false := by
  have hav := av.isLt
  have hmax : (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : ((18446744073709551615 : BitVec 64) - av).toNat = 2 ^ 64 - 1 - av.toNat := by
    rw [BitVec.toNat_sub, hmax]
    have h1 : 2 ^ 64 - av.toNat + (2 ^ 64 - 1) = (2 ^ 64 - 1 - av.toNat) + 2 ^ 64 := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ult, hsub, decide_eq_false_iff_not]; omega

private theorem ms_init_sub_eq {av : BitVec 64} (hge : fullM6HdrTotalBytes ≤ av.toNat) :
    (av - 2304).toNat = av.toNat - fullM6ExtBytes := by
  rw [BitVec.toNat_sub, show (2304 : BitVec 64).toNat = 2304 from rfl]
  unfold fullM6ExtBytes fullM6HdrTotalBytes at *; omega

private theorem ms_init_hdr_toNat {wb av : BitVec 64} (hfit : wb.toNat + av.toNat < 2 ^ 64)
    (hge : fullM6HdrTotalBytes ≤ av.toNat) :
    (wb + 2304).toNat = wb.toNat + fullM6ExtBytes := by
  rw [BitVec.toNat_add, show (2304 : BitVec 64).toNat = 2304 from rfl]
  unfold fullM6ExtBytes fullM6HdrTotalBytes at *
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem ms_init_ext_fit : 8 * fullM6ExtWords ≤ 2 ^ 64 := by
  unfold fullM6ExtWords; decide

theorem full_m6_mem_init_ms_wp (Γ : Env)
    (hInitState : EnvSpec Γ "full_init_state" m7InitStateSpec)
    (hHdrInit : EnvSpec Γ "m6_hdr_init" m6HdrInitMsSpec) :
    ∀ a m Q X, fullM6MemInitMsSpec a m Q X → Func.wp Γ full_m6_mem_init_body a m Q X := by
  rintro ⟨cnf_ptr, cend, work_base, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, hcend, hfit, hwfit, hm, hFail, hOk⟩
  rw [envSpec_eq] at hInitState hHdrInit
  unfold Func.wp full_m6_mem_init_body; wp_unfold
  have hult_av : avail.ult 3456 = decide (avail.toNat < fullM6HdrTotalBytes) := by
    rw [BitVec.ult, show (3456 : BitVec 64).toNat = fullM6HdrTotalBytes from rfl]
  rw [hult_av]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hlt => hFail m hm (Or.inl hlt), fun hnot_lt => ?_⟩
  have hge3456 : fullM6HdrTotalBytes ≤ avail.toNat := Nat.le_of_not_lt hnot_lt
  rw [ms_bv64_max_sub_ult_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  have hav_le : avail.toNat ≤ 2 ^ 64 := Nat.le_of_lt avail.isLt
  have hsub_eq : (avail - 2304).toNat = avail.toNat - fullM6ExtBytes :=
    ms_init_sub_eq hge3456
  have hhdr_to : (work_base + 2304).toNat = work_base.toNat + fullM6ExtBytes :=
    ms_init_hdr_toNat hwfit hge3456
  have hhdr_bv : work_base + (2304 : BitVec 64) =
      work_base + BitVec.ofNat 64 fullM6ExtBytes := by
    unfold fullM6ExtBytes; rfl
  have hsum_av : fullM6ExtBytes + (avail.toNat - fullM6ExtBytes) = avail.toNat :=
    Nat.add_sub_of_le (Nat.le_trans (by decide : fullM6ExtBytes ≤ fullM6HdrTotalBytes) hge3456)
  have hrem_fit :
      work_base.toNat + fullM6ExtBytes + (avail.toNat - fullM6ExtBytes) < 2 ^ 64 := by
    rw [Nat.add_assoc, hsum_av]; exact hwfit
  have hrem_ge : 1152 ≤ avail.toNat - fullM6ExtBytes :=
    Nat.le_sub_of_add_le (by exact hge3456)
  have hsplit : (bytes cnf_ptr cnfBytes ⋆
      region (work_base + 2304) (avail - 2304).toNat ⋆
      (region work_base fullM6ExtBytes ⋆ R)) m := by
    have hm1 : (bytes cnf_ptr cnfBytes ⋆
        (region work_base fullM6ExtBytes ⋆
          region (work_base + BitVec.ofNat 64 fullM6ExtBytes)
            (avail.toNat - fullM6ExtBytes)) ⋆ R) m := by
      rw [region_merge_eq (a := work_base) (n1 := fullM6ExtBytes)
        (n2 := avail.toNat - fullM6ExtBytes) (n := avail.toNat) hsum_av hav_le]
      exact hm
    rw [hsub_eq, hhdr_bv]; exact ms_sep_init_split hm1
  c0_call hInitState
  rw [m7InitStateSpec_eq]
  refine ⟨cnfBytes, region work_base fullM6ExtBytes ⋆ R, hcend, hfit,
    by rw [hhdr_to, hsub_eq]; exact hrem_fit,
    by rw [hsub_eq]; exact hrem_ge, hsplit, ?_, ?_⟩
  · intro m1 hm1 hfail1
    wp_unfold
    have hre : (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m1 := by
      have hm2 : (bytes cnf_ptr cnfBytes ⋆
          (region work_base fullM6ExtBytes ⋆
            region (work_base + BitVec.ofNat 64 fullM6ExtBytes)
              (avail.toNat - fullM6ExtBytes)) ⋆ R) m1 := by
        rw [hsub_eq, hhdr_bv] at hm1; exact ms_sep_init_merge hm1
      rw [region_merge_eq (a := work_base) (n1 := fullM6ExtBytes)
        (n2 := avail.toNat - fullM6ExtBytes) (n := avail.toNat) hsum_av hav_le] at hm2
      exact hm2
    exact hFail m1 hre (Or.inr fun mv nc rest hp => by
      have := hfail1 mv nc rest hp; rwa [hsub_eq] at this)
  · intro c s j rest m1 hchdr hcavail hparse hj hdrop hsp hcv _unass hdcur _dval hal hwl hte hpr hcl
      hfu _cref _tc _tl _mcl _mcf hoom hinc _ni _nr _nb _uf _pb _dm _vals _wv _mrk _lm _el _pl _ell hm1
    have hcfg : MemShrinkM6HdrCfgOk c := by
      unfold MemShrinkM6HdrCfgOk; rw [hchdr, hhdr_to]; exact Nat.le_add_left ..
    have hwa : m6ExtAddr c.hdr = work_base := by
      rw [hchdr]; exact m6ExtAddr_of_add_imm work_base
    have hm1' : (region work_base (8 * fullM6ExtWords) ⋆
        (bytes cnf_ptr cnfBytes ⋆ MemShrinkMem c s ⋆ R)) m1 := by
      have h0 := ms_sep_init_pull_ext hm1
      simpa only [show fullM6ExtBytes = 8 * fullM6ExtWords from rfl] using h0
    have hm2 := sep_mono (fun _ (hr : region work_base (8 * fullM6ExtWords) _) =>
      region_to_array64 fullM6ExtWords ms_init_ext_fit hr) hm1'
    obtain ⟨ext0, hm3⟩ := sep_ex_l.mp hm2
    obtain ⟨hext0_len, hm4⟩ := sep_pure_l.mp hm3
    have hm_ext : (MemShrinkM6HdrMem c ext0 s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m1 := by
      have h1 : (array64 (m6ExtAddr c.hdr) ext0 ⋆
          (bytes cnf_ptr cnfBytes ⋆ MemShrinkMem c s ⋆ R)) m1 := by
        rw [hwa]; exact hm4
      unfold MemShrinkM6HdrMem; exact ms_sep_init_pack h1
    have hsp_len : MemShrinkLengthsOk c s := ((MemShrinkSparseInv_eq c s).mp hsp).1
    c0_hsteps_nogrp
    · c0_call hHdrInit
      refine ⟨c, ext0, s, bytes cnf_ptr cnfBytes ⋆ R, hchdr.symm, hcfg,
        M6HdrExtOk.of_len (by simpa [fullM6ExtWords] using hext0_len), hsp_len, hm_ext,
        fun ext1 m2 hinit1 hm2 => ?_⟩
      c0_hsteps
      rw [← hchdr]
      exact hOk c ext1 s j rest m2 (hchdr.trans hhdr_bv) (by rwa [hsub_eq] at hcavail)
        ⟨hcfg, hinit1.toOk, hsp⟩ hinit1 hparse hj hdrop hcv hdcur hal hwl hte hpr hcl hfu
        hoom hinc (ms_sep_init_unpack hm2)
    · cases hc

end M6HdrFramingMs

/-! ## 5. Closed `ModuleOk` (`14`-fn Standalone & `16`-fn `+FullM6Hdr`) & UNSAT NV -/

section ModuleOkSection

private theorem m7msCompactVarsSpec_monoX {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : m7msCompactVarsSpec xs m Q X) :
    m7msCompactVarsSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ (fs : List Fn), (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | f :: fs, h => ⟨h f (.head _), allFns_of_forall fs fun g hg => h g (.tail _ hg)⟩

/-- Closed `15`-row spec table for `m7msStandaloneModule` (`14` defined fns + `1` extern). -/
def m7msSpecTable : List SpecEntry :=
  [ ⟨"full_fill_u64_m7", [i64, i64, i64], [], m7FillU64Spec, true⟩
  , ⟨"full_zero_tables1", [i64], [], m7ZeroTables1Spec, true⟩
  , ⟨"full_zero_tables2", [i64], [], m7ZeroTables2Spec, true⟩
  , ⟨"full_fixed_bytes", [i64], [i64], m7FixedBytesSpec, true⟩
  , ⟨"full_init_ptrs", [i64, i64, i64], [], m7InitPtrsSpec, true⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], m7InitHdrSpec, true⟩
  , ⟨"full_trans_bytes_m7", [i64], [i64], m7TransBytesSpec, true⟩
  , ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], m7V5CalcMaxVSpec, true⟩
  , ⟨"full_calc_ext_cap_m5", [i64], [i64], m7CalcExtCapSpec, true⟩
  , ⟨"full_calc_scr_cap_m5", [i64], [i64], m7CalcScrCapSpec, true⟩
  , ⟨"full_init_arenas", [i64, i64, i64, i64], [], m7InitArenasSpec, true⟩
  , ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], m7InitStateSpec, true⟩
  , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], m7InitStateSpec, true⟩
  , ⟨"full_compact_vars", [i64, i64, i64], [], m7msCompactVarsSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩ ]

theorem m7msSpecTable_length : m7msSpecTable.length = 15 := by
  unfold m7msSpecTable; rfl

theorem m7msSpecTable_nodup : (m7msSpecTable.map SpecEntry.name).Nodup := by
  unfold m7msSpecTable; decide

theorem m7msSpecTable_noExit : ∀ e ∈ m7msSpecTable, e.noExit = true := by
  intro e he
  unfold m7msSpecTable at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

/-- Closed specification environment for `m7msStandaloneModule`. -/
def m7msEnv : Env := Env.ofTable m7msSpecTable

private theorem m7msEnv_row {i : Nat} (nm : Sym) {as rs : List Ty} (sp : Spec as rs)
    (hi : m7msSpecTable[i]? = some ⟨nm, as, rs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    EnvSpec m7msEnv nm sp := by
  rw [envSpec_eq]; intro xs m Q X h
  exact Env.ofTable_of_mem (List.mem_of_getElem? hi) m7msSpecTable_nodup
    (by simp only [SpecEntry.eff, ↓reduceIte]; exact hno xs m Q X h)

private theorem m7msStandalone_tableImpl_gen (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    (hZt1 : EnvSpec Γ "full_zero_tables1" m7ZeroTables1Spec)
    (hZt2 : EnvSpec Γ "full_zero_tables2" m7ZeroTables2Spec)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hPtrs : EnvSpec Γ "full_init_ptrs" m7InitPtrsSpec)
    (hHdr : EnvSpec Γ "full_init_hdr" m7InitHdrSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (hMaxV : EnvSpec Γ "full_calc_max_v" m7V5CalcMaxVSpec)
    (hExt : EnvSpec Γ "full_calc_ext_cap_m5" m7CalcExtCapSpec)
    (hScr : EnvSpec Γ "full_calc_scr_cap_m5" m7CalcScrCapSpec)
    (hArenas : EnvSpec Γ "full_init_arenas" m7InitArenasSpec)
    (hM5 : EnvSpec Γ "full_init_state_m5" m7InitStateSpec)
    (hParse : EnvSpec Γ "kissat_parse_header" kissatParseHeaderSpec)
    {tail : List SpecEntry} :
    TableImpl Γ m7msStandaloneFns (m7msSpecTable.take 14 ++ tail) :=
  ⟨ SpecEntry.Impl.of (full_fill_u64_m7ms_wp Γ)
  , SpecEntry.Impl.of (full_zero_tables1_m7ms_wp Γ hFill)
  , SpecEntry.Impl.of (full_zero_tables2_m7ms_wp Γ hFill)
  , SpecEntry.Impl.of (full_fixed_bytes_m7ms_wp Γ)
  , SpecEntry.Impl.of (full_init_ptrs_m7ms_wp Γ)
  , SpecEntry.Impl.of (full_init_hdr_m7ms_wp Γ)
  , SpecEntry.Impl.of (full_trans_bytes_m7ms_wp Γ)
  , SpecEntry.Impl.of (full_calc_max_v_m7v5_wp Γ hFixed hTrans)
  , SpecEntry.Impl.of (full_calc_ext_cap_m7ms_wp Γ)
  , SpecEntry.Impl.of (full_calc_scr_cap_m7ms_wp Γ)
  , SpecEntry.Impl.of (full_init_arenas_m7ms_wp Γ hPtrs)
  , SpecEntry.Impl.of (full_init_state_m7ms_wp Γ hParse hFixed hTrans hMaxV hExt hScr hArenas
      hHdr hZt1 hZt2)
  , SpecEntry.Impl.of (full_init_state_wrap_m7ms_wp Γ hM5)
  , SpecEntry.Impl.of (full_compact_vars_m7ms_wp Γ)
  , trivial ⟩

theorem m7ms_tableImpl : TableImpl m7msEnv m7msStandaloneModule.fns m7msSpecTable := by
  have h14 : m7msSpecTable = m7msSpecTable.take 14 ++
      [⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩] := by
    unfold m7msSpecTable; rfl
  rw [h14]
  exact m7msStandalone_tableImpl_gen m7msEnv
    (m7msEnv_row "full_fill_u64_m7" m7FillU64Spec (i := 0) rfl
      fun xs m Q X h => by rw [m7FillU64Spec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_zero_tables1" m7ZeroTables1Spec (i := 1) rfl
      fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables1Spec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_zero_tables2" m7ZeroTables2Spec (i := 2) rfl
      fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables2Spec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_fixed_bytes" m7FixedBytesSpec (i := 3) rfl
      fun xs m Q X h => by rw [m7FixedBytesSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_init_ptrs" m7InitPtrsSpec (i := 4) rfl
      fun ⟨h1, h2, h3, ⟨⟩⟩ m Q X h => by rw [m7InitPtrsSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_init_hdr" m7InitHdrSpec (i := 5) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitHdrSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_trans_bytes_m7" m7TransBytesSpec (i := 6) rfl
      fun xs m Q X h => by rw [m7TransBytesSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_calc_max_v" m7V5CalcMaxVSpec (i := 7) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7V5CalcMaxVSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_calc_ext_cap_m5" m7CalcExtCapSpec (i := 8) rfl
      fun xs m Q X h => by rw [m7CalcExtCapSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_calc_scr_cap_m5" m7CalcScrCapSpec (i := 9) rfl
      fun xs m Q X h => by rw [m7CalcScrCapSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_init_arenas" m7InitArenasSpec (i := 10) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitArenasSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_init_state_m5" m7InitStateSpec (i := 11) rfl
      fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "kissat_parse_header" kissatParseHeaderSpec (i := 14) rfl
      fun _ _ _ _ h => h)

/-- Closed `ModuleOk` certifying all `14` canonical MemShrink V5 functions + `1` extern. -/
theorem m7msStandalone_moduleOk : ModuleOk m7msEnv m7msStandaloneModule :=
  Env.ofTable_moduleOk m7msStandalone_acyclic
    (allFns_of_forall m7msStandaloneFns m7msStandaloneFns_wf) m7ms_tableImpl

/-- Canonical `m6_hdr_init` entry wired over `MemShrinkM6HdrMem`. -/
def m6HdrInitMsFn : Fn := ⟨"m6_hdr_init", [i64], [], FullM6Hdr.m6_hdr_init_body⟩

/-- Canonical `full_m6_mem_init` entry carving `2,304 B` `M6HdrExt` + `MemShrinkMem`. -/
def fullM6MemInitMsFn : Fn :=
  ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], FullM6Hdr.full_m6_mem_init_body⟩

/-- Unified `16`-function standalone `FullM7MemShrinkV5 + FullM6Hdr` module (`1` extern, `0` exits). -/
def m7msM6Module : LeanQbe.T.Module :=
  { fns := m7msStandaloneFns ++ [m6HdrInitMsFn, fullM6MemInitMsFn]
  , externs := m7msStandaloneExterns
  , exits := [] }

theorem m7msM6_fns_wf : AllFns Fn.Wf m7msM6Module.fns := by
  refine allFns_of_forall _ fun f hf => ?_
  simp only [m7msM6Module, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with hf | rfl | rfl
  · exact m7msStandaloneFns_wf f hf
  · exact FullM6Hdr.m6_hdr_init_wf
  · exact FullM6Hdr.full_m6_mem_init_wf

theorem m7msM6_acyclic : m7msM6Module.checkAcyclic = true := by
  t_kernel_rfl

/-- Closed `17`-row spec table for `m7msM6Module` (`16` defined fns + `1` extern). -/
def m7msM6SpecTable : List SpecEntry :=
  m7msSpecTable.take 14 ++
  [ ⟨"m6_hdr_init", [i64], [], m6HdrInitMsSpec, true⟩
  , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitMsSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩ ]

theorem m7msM6SpecTable_length : m7msM6SpecTable.length = 17 := by
  unfold m7msM6SpecTable m7msSpecTable; rfl

theorem m7msM6SpecTable_nodup : (m7msM6SpecTable.map SpecEntry.name).Nodup := by
  unfold m7msM6SpecTable m7msSpecTable; decide

theorem m7msM6SpecTable_noExit : ∀ e ∈ m7msM6SpecTable, e.noExit = true := by
  intro e he
  unfold m7msM6SpecTable m7msSpecTable at he
  simp only [List.take, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Closed specification environment for `m7msM6Module`. -/
def m7msM6Env : Env := Env.ofTable m7msM6SpecTable

private theorem m7msM6Env_row {i : Nat} (nm : Sym) {as rs : List Ty} (sp : Spec as rs)
    (hi : m7msM6SpecTable[i]? = some ⟨nm, as, rs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    EnvSpec m7msM6Env nm sp := by
  rw [envSpec_eq]; intro xs m Q X h
  exact Env.ofTable_of_mem (List.mem_of_getElem? hi) m7msM6SpecTable_nodup
    (by simp only [SpecEntry.eff, ↓reduceIte]; exact hno xs m Q X h)

private theorem tableImpl_append_cons {Γ : Env} {fs1 fs2 : List Fn} {sp1 sp2 : List SpecEntry}
    (h1 : fs1.length = sp1.length)
    (ht1 : TableImpl Γ fs1 (sp1 ++ sp2))
    (ht2 : TableImpl Γ fs2 sp2) :
    TableImpl Γ (fs1 ++ fs2) (sp1 ++ sp2) := by
  induction fs1 generalizing sp1 with
  | nil =>
    cases sp1 with
    | nil => exact ht2
    | cons _ _ => simp at h1
  | cons f fs ih =>
    cases sp1 with
    | nil => simp at h1
    | cons e es =>
      simp only [List.length_cons, Nat.succ.injEq] at h1
      simp only [List.cons_append, TableImpl] at ht1 ⊢
      exact ⟨ht1.1, ih h1 ht1.2⟩

theorem m7msM6_tableImpl : TableImpl m7msM6Env m7msM6Module.fns m7msM6SpecTable := by
  have h14 : TableImpl m7msM6Env m7msStandaloneFns (m7msSpecTable.take 14 ++
      [ ⟨"m6_hdr_init", [i64], [], m6HdrInitMsSpec, true⟩
      , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitMsSpec, true⟩
      , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩ ]) :=
    m7msStandalone_tableImpl_gen m7msM6Env
      (m7msM6Env_row "full_fill_u64_m7" m7FillU64Spec (i := 0) rfl
        fun xs m Q X h => by rw [m7FillU64Spec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_zero_tables1" m7ZeroTables1Spec (i := 1) rfl
        fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables1Spec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_zero_tables2" m7ZeroTables2Spec (i := 2) rfl
        fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables2Spec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_fixed_bytes" m7FixedBytesSpec (i := 3) rfl
        fun xs m Q X h => by rw [m7FixedBytesSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_init_ptrs" m7InitPtrsSpec (i := 4) rfl
        fun ⟨h1, h2, h3, ⟨⟩⟩ m Q X h => by rw [m7InitPtrsSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_init_hdr" m7InitHdrSpec (i := 5) rfl
        fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitHdrSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_trans_bytes_m7" m7TransBytesSpec (i := 6) rfl
        fun xs m Q X h => by rw [m7TransBytesSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_calc_max_v" m7V5CalcMaxVSpec (i := 7) rfl
        fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7V5CalcMaxVSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_calc_ext_cap_m5" m7CalcExtCapSpec (i := 8) rfl
        fun xs m Q X h => by rw [m7CalcExtCapSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_calc_scr_cap_m5" m7CalcScrCapSpec (i := 9) rfl
        fun xs m Q X h => by rw [m7CalcScrCapSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_init_arenas" m7InitArenasSpec (i := 10) rfl
        fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitArenasSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "full_init_state_m5" m7InitStateSpec (i := 11) rfl
        fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "kissat_parse_header" kissatParseHeaderSpec (i := 16) rfl
        fun _ _ _ _ h => h)
  have hm6_hdr : SpecEntry.Impl m7msM6Env m6HdrInitMsFn
      ⟨"m6_hdr_init", [i64], [], m6HdrInitMsSpec, true⟩ :=
    SpecEntry.Impl.of (m6_hdr_init_ms_wp m7msM6Env)
  have hfull_m6 : SpecEntry.Impl m7msM6Env fullM6MemInitMsFn
      ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitMsSpec, true⟩ :=
    SpecEntry.Impl.of (full_m6_mem_init_ms_wp m7msM6Env
      (m7msM6Env_row "full_init_state" m7InitStateSpec (i := 12) rfl
        fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
      (m7msM6Env_row "m6_hdr_init" m6HdrInitMsSpec (i := 14) rfl
        fun _ _ _ _ h => m6HdrInitMsSpec_monoX h))
  exact tableImpl_append_cons (sp1 := m7msSpecTable.take 14)
    (by unfold m7msSpecTable; rfl) h14 ⟨hm6_hdr, hfull_m6, trivial⟩

private theorem fullM6MemInitMsFn_impl : SpecEntry.Impl m7msM6Env fullM6MemInitMsFn
    ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitMsSpec, true⟩ :=
  SpecEntry.Impl.of (full_m6_mem_init_ms_wp m7msM6Env
    (m7msM6Env_row "full_init_state" m7InitStateSpec (i := 12) rfl
      fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
    (m7msM6Env_row "m6_hdr_init" m6HdrInitMsSpec (i := 14) rfl
      fun _ _ _ _ h => m6HdrInitMsSpec_monoX h))

/-- Closed `ModuleOk` certifying all `16` functions of `m7msM6Module` (standalone V5 +
`FullM6Hdr` zero-edit prefix framing) with `1` extern and `0` exits. -/
theorem m7msM6_moduleOk : ModuleOk m7msM6Env m7msM6Module :=
  Env.ofTable_moduleOk m7msM6_acyclic m7msM6_fns_wf m7msM6_tableImpl

end ModuleOkSection

/-! ## 6. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteUnsatNv

/-- Concrete `1`-variable, `2`-clause UNSAT formula `(x1) ∧ (~x1)`. -/
def nvMsUnsatCnf : CNF Nat :=
  CNF.empty |>.add (CNF.Clause.ofLiterals [(1, true)]) |>.add (CNF.Clause.ofLiterals [(1, false)])

theorem nvMsUnsatCnf_unsat : nvMsUnsatCnf.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hsat
  rw [nvMsUnsatCnf, CNF.sat_add, CNF.sat_add] at hsat
  rcases hsat with ⟨hc2, hc1, _⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hc1 hc2
  obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := hc1
  obtain ⟨⟨v2, p2⟩, hm2, he2⟩ := hc2
  rw [← CNF.Clause.mem_literals_iff] at hm1 hm2
  simp at hm1 hm2
  rcases hm1 with ⟨rfl, rfl⟩
  rcases hm2 with ⟨rfl, rfl⟩
  rw [he1] at he2
  exact nomatch he2

/-- DIMACS bytes for `"p cnf 1 2\n1 0\n-1 0\n"` (`19` bytes). -/
def nvMsUnsatBytes : List UInt8 :=
  [ 0x70, 0x20, 0x63, 0x6e, 0x66, 0x20, 0x31, 0x20, 0x32, 0x0a
  , 0x31, 0x20, 0x30, 0x0a, 0x2d, 0x31, 0x20, 0x30, 0x0a ]

theorem nvMsUnsat_header :
    parseHeader nvMsUnsatBytes = some (1, 2, nvMsUnsatBytes.drop 9) := by
  unfold nvMsUnsatBytes; rfl

def nvMsCnfPtr : BitVec 64 := 0x1000#64
def nvMsHdrPtr : BitVec 64 := nvMsCnfPtr + BitVec.ofNat 64 nvMsUnsatBytes.length

private theorem nv_ms_mem_split (base : BitVec 64) (k : Nat)
    (hk : nvMsUnsatBytes.length + k ≤ 2 ^ 64) :
    (bytes base nvMsUnsatBytes ⋆
      region (base + BitVec.ofNat 64 nvMsUnsatBytes.length) k ⋆ emp)
      ((nvMsUnsatBytes ++ List.replicate k (0 : UInt8)).At base) := by
  rw [sep_emp]
  have e := Mem.At_append_sep nvMsUnsatBytes (List.replicate k (0 : UInt8)) base
    (by simpa using hk)
  have hbase : (Eq (nvMsUnsatBytes.At base) ⋆
      Eq ((List.replicate k (0 : UInt8)).At (base + BitVec.ofNat 64 nvMsUnsatBytes.length)))
      ((nvMsUnsatBytes ++ List.replicate k (0 : UInt8)).At base) :=
    (congrFun e _).mp rfl
  exact sep_mono2 (fun _ h => h)
    (fun _ h => ⟨List.replicate k (0 : UInt8), by simp, h.symm⟩) _ hbase

/-- Concrete `Mem 64` holding `nvMsUnsatBytes` at `0x1000` and `4,096 B` workspace. -/
def nvMsInitMem : Mem 64 :=
  (nvMsUnsatBytes ++ List.replicate 4096 (0 : UInt8)).At nvMsCnfPtr

/-- Concrete `Mem 64` memory with `nvMsUnsatBytes` at `0x2000` + `1,000 B` undersized workspace. -/
def nvMsTinyInitMem : Mem 64 :=
  (nvMsUnsatBytes ++ List.replicate 1000 (0 : UInt8)).At 0x2000#64

/-- Concrete `Mem 64` memory with `nvMsUnsatBytes` at `0x2000` + `6,400 B` workspace
(`2,304 B` `M6HdrExt` + `4,096 B` `MemShrinkMem`). -/
def nvMs4kInitMem : Mem 64 :=
  (nvMsUnsatBytes ++ List.replicate 6400 (0 : UInt8)).At 0x2000#64

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`, `0` SAT proofs) for `full_init_state_m7ms`
on `(x1) ∧ (~x1)` with `4,096 B` budget (`mv = 1`, `nc = 2`, `avail = 4096`). -/
theorem nv_m7ms_init_state_unsat :
    Func.wp m7msEnv full_init_state_m7ms_body
      (nvMsCnfPtr, nvMsCnfPtr + BitVec.ofNat 64 nvMsUnsatBytes.length,
        nvMsHdrPtr, 4096#64, 16#64, ())
      nvMsInitMem
      (fun (r, ()) m' =>
        r = true ∧ ∃ c s,
          c.hdr = nvMsHdrPtr ∧ c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧
          nvMsUnsatCnf.Unsat ∧ MemShrinkSparseInv c s ∧
          (bytes nvMsCnfPtr nvMsUnsatBytes ⋆ MemShrinkMem c s) m')
      (fun _ _ _ _ => False) := by
  have hm := nv_ms_mem_split nvMsCnfPtr 4096 (by unfold nvMsUnsatBytes; decide)
  apply full_init_state_m7ms_wp m7msEnv
    (m7msEnv_row "kissat_parse_header" kissatParseHeaderSpec (i := 14) rfl fun _ _ _ _ h => h)
    (m7msEnv_row "full_fixed_bytes" m7FixedBytesSpec (i := 3) rfl
      fun xs m Q X h => by rw [m7FixedBytesSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_trans_bytes_m7" m7TransBytesSpec (i := 6) rfl
      fun xs m Q X h => by rw [m7TransBytesSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_calc_max_v" m7V5CalcMaxVSpec (i := 7) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7V5CalcMaxVSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_calc_ext_cap_m5" m7CalcExtCapSpec (i := 8) rfl
      fun xs m Q X h => by rw [m7CalcExtCapSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_calc_scr_cap_m5" m7CalcScrCapSpec (i := 9) rfl
      fun xs m Q X h => by rw [m7CalcScrCapSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_init_arenas" m7InitArenasSpec (i := 10) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitArenasSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_init_hdr" m7InitHdrSpec (i := 5) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitHdrSpec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_zero_tables1" m7ZeroTables1Spec (i := 1) rfl
      fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables1Spec_eq] at h ⊢; exact h)
    (m7msEnv_row "full_zero_tables2" m7ZeroTables2Spec (i := 2) rfl
      fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables2Spec_eq] at h ⊢; exact h)
  rw [m7InitStateSpec_eq]
  refine ⟨nvMsUnsatBytes, emp, rfl,
    (by unfold nvMsCnfPtr nvMsUnsatBytes; decide),
    (by unfold nvMsHdrPtr nvMsCnfPtr nvMsUnsatBytes; decide),
    (by decide),
    (by unfold nvMsHdrPtr nvMsInitMem; exact hm), ?_, ?_⟩
  · intro _ _ hfail
    have hlt := hfail 1 2 (nvMsUnsatBytes.drop 9) nvMsUnsat_header
    have hge : ¬ (4096#64).toNat < m7FixedBytes 1 + m7TransBytes 1 + 2 * 40 + 136 := by
      simp only [m7FixedBytes_def, m7TransBytes_def]
      unfold valsBytes markBytes u32FullBytes fullMinDepthOf; decide
    exact absurd hlt hge
  · intro c s j rest m' hhdr hav hph _ _ hsp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ hm'
    rw [sep_emp] at hm'
    simp only [nvMsUnsat_header, Option.some.injEq, Prod.mk.injEq] at hph
    refine ⟨rfl, c, s, hhdr, by simpa using hav, hph.1.symm, hph.2.1.symm,
      nvMsUnsatCnf_unsat, hsp, hm'⟩

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_m6_mem_init` on an undersized `1,000 B`
workspace (`< 3,456 B`): returns `0#64` cleanly without underflow and preserves memory. -/
theorem nv_m7ms_m6_mem_init_tiny :
    Func.wp m7msM6Env FullM6Hdr.full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length, 1000#64, 16#64, ())
      nvMsTinyInitMem
      (fun (r, ()) m' => r = 0#64 ∧ nvMsUnsatCnf.Unsat ∧
        (bytes 0x2000#64 nvMsUnsatBytes ⋆
          region (0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length) 1000) m')
      (fun _ _ _ _ => False) := by
  have hm := nv_ms_mem_split 0x2000#64 1000 (by unfold nvMsUnsatBytes; decide)
  apply full_m6_mem_init_ms_wp m7msM6Env
    (m7msM6Env_row "full_init_state" m7InitStateSpec (i := 12) rfl
      fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
    (m7msM6Env_row "m6_hdr_init" m6HdrInitMsSpec (i := 14) rfl
      fun _ _ _ _ h => m6HdrInitMsSpec_monoX h)
  refine fullM6MemInitMsSpec_of rfl (by unfold nvMsUnsatBytes; decide) (by decide)
    (by unfold nvMsTinyInitMem; exact hm)
    (fun m' hm' _ => by rw [sep_emp] at hm'; exact ⟨rfl, nvMsUnsatCnf_unsat, hm'⟩)
    (fun c _ _ _ _ _ _ hcavail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
      have hcav0 : c.avail = 0 := by simpa [fullM6ExtBytes] using hcavail
      have hfx : 1472 ≤ m7FixedBytes c.max_vars := by simp only [m7FixedBytes_def]; omega
      have := c.hsize; omega)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`, `0` SAT proofs) for `full_m6_mem_init`
on `(x1) ∧ (~x1)` with `6,400 B` workspace: carves `2,304 B` initialized `M6HdrExt` + `4,096 B`
`MemShrinkMem` (`c.mv = 1`, `c.nc = 2`) and returns `work_base + 2304`. -/
theorem nv_m7ms_m6_mem_init_4k :
    Func.wp m7msM6Env FullM6Hdr.full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length, 6400#64, 16#64, ())
      nvMs4kInitMem
      (fun (r, ()) m' => ∃ (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState),
        r = c.hdr ∧ c.hdr = (0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length) +
          BitVec.ofNat 64 fullM6ExtBytes ∧
        c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧ nvMsUnsatCnf.Unsat ∧
        MsM6HdrExtInitOk ext ∧ MemShrinkM6HdrInv c ext s ∧
        (bytes 0x2000#64 nvMsUnsatBytes ⋆ MemShrinkM6HdrMem c ext s) m')
      (fun _ _ _ _ => False) := by
  have hm := nv_ms_mem_split 0x2000#64 6400 (by unfold nvMsUnsatBytes; decide)
  apply full_m6_mem_init_ms_wp m7msM6Env
    (m7msM6Env_row "full_init_state" m7InitStateSpec (i := 12) rfl
      fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
    (m7msM6Env_row "m6_hdr_init" m6HdrInitMsSpec (i := 14) rfl
      fun _ _ _ _ h => m6HdrInitMsSpec_monoX h)
  refine fullM6MemInitMsSpec_of rfl (by unfold nvMsUnsatBytes; decide) (by decide)
    (by unfold nvMs4kInitMem; exact hm)
    (fun _ _ hfail => by
      rcases hfail with h1 | h2
      · exact absurd h1 (by decide)
      · have hlt := h2 1 2 (nvMsUnsatBytes.drop 9) nvMsUnsat_header
        have hge : ¬ (6400#64).toNat - fullM6ExtBytes <
            m7FixedBytes 1 + m7TransBytes 1 + 2 * 40 + 136 := by
          simp only [m7FixedBytes_def, m7TransBytes_def]
          unfold valsBytes markBytes u32FullBytes fullMinDepthOf fullM6ExtBytes; decide
        exact absurd hlt hge)
    (fun c ext s j rest m' hchdr hcavail hinv hext_init hparse _ _ _ _ _ _ _ _ _ _ _ _ hm' => by
      rw [sep_emp] at hm'
      simp only [nvMsUnsat_header, Option.some.injEq, Prod.mk.injEq] at hparse
      have hcav4k : c.avail = 4096 := by simpa [fullM6ExtBytes] using hcavail
      exact ⟨c, ext, s, rfl, hchdr, hcav4k, hparse.1.symm, hparse.2.1.symm,
        nvMsUnsatCnf_unsat, hext_init, hinv, hm'⟩)

end ConcreteUnsatNv

end LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5

end
