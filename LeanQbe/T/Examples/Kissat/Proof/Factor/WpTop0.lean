/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# BVA Literal Trial Sub-Loops & Exit Phase WP (`Proof.Factor.WpTop0`)

Helpers, packed BVA matrix invariants, step-loop WP, exit-phase WP, and `step0_post_exit_wp`
for `full_bva_try_lit_wp` (`0` legacy imports, `0` placeholders, `XPost`-polymorphic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

/-! ## 1. Dynamic Matrix, BitVec & Lit-Mark Helpers -/

private theorem top_bv32_sc_add_step_sub1 {sc : Nat} {step : BitVec 32}
    (hsc : sc ≤ 256) (hst1 : 1 ≤ step.toNat) (hst_sc : step.toNat ≤ sc) :
    (BitVec.ofNat 32 sc + step - 1#32).toNat = sc + (step.toNat - 1) := by
  have h1 : (BitVec.ofNat 32 sc + step).toNat = sc + step.toNat := by
    simp only [bv_c0, Nat.mod_eq_of_lt (by omega : sc < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : sc + step.toNat < 2 ^ 32)]
  have h2 : 1#32 ≤ BitVec.ofNat 32 sc + step := by
    rw [BitVec.le_def, h1, show (1#32 : BitVec 32).toNat = 1 from rfl]; omega
  rw [BitVec.toNat_sub_of_le h2, h1, show (1#32 : BitVec 32).toNat = 1 from rfl]; omega

private theorem top_bv64_sc_add_step_sub1 {sc : Nat} {step : BitVec 32}
    (hsc : sc ≤ 256) (hst1 : 1 ≤ step.toNat) (hst_sc : step.toNat ≤ sc) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step - 1#32)).toNat = sc + (step.toNat - 1) := by
  rw [fid_bv64_32, top_bv32_sc_add_step_sub1 hsc hst1 hst_sc]

private theorem top_getElem_eq_of_eq {α : Type _} {xs ys : List α} {i j : Nat}
    (hl : xs = ys) (hij : i = j) (hi : i < xs.length) (hj : j < ys.length) :
    xs[i]'hi = ys[j]'hj := by subst hl; subst hij; rfl

private theorem top_clear_lm_done {c : FullCfg} {stf : FullState}
    {lmi : List (BitVec 8)} {stepf : Nat}
    (hmrk : ∀ v < c.max_vars, stf.core.mrk[v]?.getD 0#8 = 0#8)
    (hlmi_hi : ∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hlmi_only : ∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r, stepf ≤ r ∧ r < stepf ∧ (stf.scratch.scratch_buf[r]?.getD 0#32).toNat = l) :
    FullLitMarksClear c { stf with core := { stf.core with lit_mark := lmi } } := by
  refine ⟨hmrk, fun l hl => ?_⟩
  have hhi := hlmi_hi l hl
  have hlo : (lmi[l]?.getD 0#8 &&& 1#8) = 0#8 := by
    apply Classical.byContradiction; intro hne
    obtain ⟨r, hr1, hr2, _⟩ := hlmi_only l hl hne; omega
  have hcomb : (lmi[l]?.getD 0#8 &&& 0xFE#8) ||| (lmi[l]?.getD 0#8 &&& 1#8) =
      lmi[l]?.getD 0#8 := by
    rw [← BitVec.and_or_distrib_left, show (0xFE#8 ||| 1#8) = 0xFF#8 from by decide]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    have := (lmi[l]?.getD 0#8).isLt
    exact (Nat.and_two_pow_sub_one_eq_mod _ 8).trans (Nat.mod_eq_of_lt this)
  rw [← hcomb, hhi, hlo]; decide

private theorem top_lm1_init {maxv cap sc : Nat} {sb : List (BitVec 32)}
    {lm : List (BitVec 8)} {f0 qn hdr_sz : BitVec 32}
    (hsc_pos : 0 < sc) (h4sc : 4 * sc ≤ cap) (hsb_l : sb.length = cap)
    (hlm_l : lm.length = 2 * maxv) (hf0_lt : f0.toNat < 2 * maxv)
    (hlm_zero : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8) :
    let sb1 := (((sb.set 0 f0).set sc hdr_sz).set (2 * sc) qn).set (3 * sc) hdr_sz
    let lm1 := lm.set f0.toNat 1#8
    (∀ l < 2 * maxv, (lm1[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
    (∀ r < 1, (lm1[(sb1[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
    (∀ l < 2 * maxv, (lm1[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < 1, (sb1[r]?.getD 0#32).toNat = l) := by
  intro sb1 lm1
  have hs0 : sb1[0]?.getD 0#32 = f0 := by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  refine ⟨fun l hl => ?_, fun r hr => ?_, fun l hl hne => ?_⟩
  · dsimp only [lm1]
    by_cases hlf : l = f0.toNat
    · subst hlf; rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
    · rw [List.getElem?_set_ne (Ne.symm hlf), hlm_zero l hl]; decide
  · have hr0 : r = 0 := by omega
    subst hr0; rw [hs0]; dsimp only [lm1]
    rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
  · dsimp only [lm1] at hne
    by_cases hlf : l = f0.toNat
    · subst hlf; exact ⟨0, by omega, by rw [hs0]⟩
    · rw [List.getElem?_set_ne (Ne.symm hlf), hlm_zero l hl] at hne; exact absurd rfl hne

private theorem top_extend_lm {maxv cap sc step bump max_new : Nat}
    {lm : List (BitVec 8)} {sb2 sb3 : List (BitVec 32)} {bl new_qn nrow_off par_off : BitVec 32}
    (hsc_pos : 0 < sc) (hstep_sc : step < sc) (hlm_l : lm.length = 2 * maxv)
    (hsb3_l : sb3.length = cap) (hbl_lt : bl.toNat < 2 * maxv) (hnrow_eq : nrow_off.toNat = bump)
    (hpar_eq : par_off.toNat = bump + max_new) (h4sc_bump : 4 * sc ≤ bump)
    (hpar_cap : par_off.toNat + max_new ≤ cap)
    (hpres : ∀ idx < cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) → sb3[idx]? = sb2[idx]?)
    (hhi : ∀ l < 2 * maxv, (lm[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hset : ∀ r < step, (lm[(sb2[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8)
    (honly : ∀ l < 2 * maxv, (lm[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < step, (sb2[r]?.getD 0#32).toNat = l) :
    let lm4 := lm.set bl.toNat 1#8
    let sb4 := (((sb3.set step bl).set (sc + step) nrow_off).set (2 * sc + step) new_qn).set
      (3 * sc + step) par_off
    (∀ l < 2 * maxv, (lm4[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
    (∀ r < step + 1, (lm4[(sb4[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
    (∀ l < 2 * maxv, (lm4[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < step + 1, (sb4[r]?.getD 0#32).toNat = l) := by
  intro lm4 sb4
  have hget_r : ∀ r < step, sb4[r]? = sb2[r]? := fun r hr => by
    dsimp only [sb4]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hpres r (by omega) (by omega) (by omega)
  have hget_step : sb4[step]?.getD 0#32 = bl := by
    dsimp only [sb4]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  refine ⟨fun l hl => ?_, fun r hr => ?_, fun l hl hne => ?_⟩
  · dsimp only [lm4]; by_cases hlb : l = bl.toNat
    · subst hlb; rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
    · rw [List.getElem?_set_ne (Ne.symm hlb)]; exact hhi l hl
  · dsimp only [lm4]; by_cases hrs : r < step
    · rw [hget_r r hrs]; by_cases hlb : (sb2[r]?.getD 0#32).toNat = bl.toNat
      · rw [hlb, List.getElem?_set_self (by omega), Option.getD_some]; decide
      · rw [List.getElem?_set_ne (Ne.symm hlb)]; exact hset r hrs
    · have hr_eq : r = step := by omega
      subst hr_eq; rw [hget_step, List.getElem?_set_self (by omega), Option.getD_some]; decide
  · dsimp only [lm4] at hne ⊢; by_cases hlb : l = bl.toNat
    · subst hlb; exact ⟨step, by omega, by rw [hget_step]⟩
    · rw [List.getElem?_set_ne (Ne.symm hlb)] at hne
      obtain ⟨r, hr, heq⟩ := honly l hl hne; exact ⟨r, by omega, by rw [hget_r r hr, heq]⟩

private theorem top_matrixInv_substep {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {k step bump : Nat} (hk1 : 1 ≤ k) (hk_le : k ≤ step)
    (h : FidBvaMatrixInv c F_cur s step bump) : FidBvaMatrixInv c F_cur s k bump := by
  rcases h with ⟨hsc, _, hss, hb1, hb2, hrows⟩
  exact ⟨hsc, hk1, Nat.le_trans hk_le hss, hb1, hb2,
    fun r hr => hrows r (Nat.lt_of_lt_of_le hr hk_le)⟩

private theorem top_matrixInv_step1 {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb : List (BitVec 32)} {f0 r0n : BitVec 32} {sc : Nat}
    (hsc_eq : sc = fidStepsCap c.scratch_cap)
    (hsc_pos : 0 < sc) (hsc_le : sc ≤ 256) (hsb_len : sb.length = c.scratch_cap)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hq2 : 2 ≤ r0n.toNat)
    (hr0n_le : 4 * sc + r0n.toNat ≤ c.scratch_cap)
    (hrow0 : ∀ m < r0n.toNat, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s f0.toNat (sb[4 * sc + m]?.getD 0#32) res ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))) :
    let hdr_sz := BitVec.ofNat 32 (4 * sc)
    let sb1 := (((sb.set 0 f0).set sc hdr_sz).set (2 * sc) r0n).set (3 * sc) hdr_sz
    FidBvaMatrixInv c F_cur { s with scratch := { s.scratch with scratch_buf := sb1 } }
      1 (4 * sc + r0n.toNat) := by
  intro hdr_sz sb1
  have hsc_cap : 4 * sc ≤ c.scratch_cap := hsc_eq ▸ fidStepsCap_mul4_le c.scratch_cap
  have hget0 : sb1[0]?.getD 0#32 = f0 := by
    dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have hget_sc : sb1[sc]?.getD 0#32 = hdr_sz := by
    dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
  have hget_2sc : sb1[2 * sc]?.getD 0#32 = r0n := by
    dsimp only [sb1]; rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set, List.length_set]; omega), Option.getD_some]
  have hget_3sc : sb1[3 * sc]?.getD 0#32 = hdr_sz := by
    dsimp only [sb1]; rw [List.getElem?_set_self
      (by rw [List.length_set, List.length_set, List.length_set]; omega), Option.getD_some]
  have hhdr_sz_nat : hdr_sz.toNat = 4 * sc := by
    simp only [hdr_sz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 4 * sc < 2 ^ 32)]
  unfold FidBvaMatrixInv; dsimp only; rw [← hsc_eq]
  refine ⟨hsc_pos, Nat.le_refl 1, by omega, by omega, hr0n_le, fun r hr => ?_⟩
  have hr0 : r = 0 := by omega
  subst hr0
  rw [Nat.add_zero, Nat.add_zero, Nat.add_zero, hget0, hget_sc, hget_2sc, hget_3sc, hhdr_sz_nat]
  refine ⟨hf0_lt, Nat.le_refl _, hq2, by omega, fun h0 => by omega, fun m hm => ?_⟩
  have hm_sb : sb1[4 * sc + m]?.getD 0#32 = sb[4 * sc + m]?.getD 0#32 := by
    dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  obtain ⟨res, hres_lt, hres_nd, hok, hent⟩ := hrow0 m hm
  refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun h0 => by omega⟩
  · rw [hm_sb]; exact fidBvaRowEntryOk_congr rfl rfl rfl hok
  · have ht0 : t = 0 := by omega
    subst ht0; rw [hget0]; exact hent

private theorem top_matrixInv_extend_step {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb' : List (BitVec 32)} {step bump max_new sc : Nat}
    {best_lit new_qn nrow_off par_off : BitVec 32}
    (hsc_eq : sc = fidStepsCap c.scratch_cap) (hstep1 : 1 ≤ step) (hstep_sc : step < sc)
    (hmat : FidBvaMatrixInv c F_cur s step bump) (hsb'_len : sb'.length = c.scratch_cap)
    (hbest_lt : best_lit.toNat < 2 * s.core.cur_vars) (hnrow_eq : nrow_off.toNat = bump)
    (hpar_eq : par_off.toNat = bump + max_new) (hpar_cap : par_off.toNat + max_new ≤ c.scratch_cap)
    (hnq_le : new_qn.toNat ≤ max_new) (hnq2 : 2 ≤ new_qn.toNat)
    (hpres : ∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?)
    (hnew : ∀ nm < new_qn.toNat,
      let pi := (sb'[par_off.toNat + nm]?.getD 0#32).toNat
      pi < (s.scratch.scratch_buf[2 * sc + (step - 1)]?.getD 0#32).toNat ∧
      ∃ res : List Nat, (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
        FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[(s.scratch.scratch_buf[sc + (step - 1)]?.getD 0#32).toNat +
            pi]?.getD 0#32) res ∧
        FidBvaRowEntryOk F_cur s best_lit.toNat (sb'[nrow_off.toNat + nm]?.getD 0#32) res ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))) :
    let bump' := par_off.toNat + new_qn.toNat
    let sb2 := (((sb'.set step best_lit).set (sc + step) nrow_off).set (2 * sc + step) new_qn).set
      (3 * sc + step) par_off
    FidBvaMatrixInv c F_cur { s with scratch := { s.scratch with scratch_buf := sb2 } }
      (step + 1) bump' := by
  intro bump' sb2; subst hsc_eq
  unfold FidBvaMatrixInv at hmat ⊢; dsimp only at hmat ⊢
  rcases hmat with ⟨hsc_pos, _, hsc_step, hb1, hb2, hrows⟩
  have hget_lt : ∀ idx < bump, idx ≠ step → idx ≠ fidStepsCap c.scratch_cap + step →
      idx ≠ 2 * fidStepsCap c.scratch_cap + step → idx ≠ 3 * fidStepsCap c.scratch_cap + step →
      sb2[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi h1 h2 h3 h4 => by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (Ne.symm h4), List.getElem?_set_ne (Ne.symm h3),
      List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]
    exact hpres idx (by omega) (by omega) (by omega)
  have hget_step : sb2[step]?.getD 0#32 = best_lit := by
    dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have hget_sc_step : sb2[fidStepsCap c.scratch_cap + step]?.getD 0#32 = nrow_off := by
    dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
  have hget_2sc_step : sb2[2 * fidStepsCap c.scratch_cap + step]?.getD 0#32 = new_qn := by
    dsimp only [sb2]; rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set, List.length_set]; omega), Option.getD_some]
  have hget_3sc_step : sb2[3 * fidStepsCap c.scratch_cap + step]?.getD 0#32 = par_off := by
    dsimp only [sb2]; rw [List.getElem?_set_self
      (by rw [List.length_set, List.length_set, List.length_set]; omega), Option.getD_some]
  have hget_nrow : ∀ nm < new_qn.toNat, sb2[nrow_off.toNat + nm]? = sb'[nrow_off.toNat + nm]? :=
    fun nm hnm => by
      dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hget_par : ∀ nm < new_qn.toNat, sb2[par_off.toNat + nm]? = sb'[par_off.toNat + nm]? :=
    fun nm hnm => by
      dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have gnat : ∀ idx < bump, idx ≠ step → idx ≠ fidStepsCap c.scratch_cap + step →
      idx ≠ 2 * fidStepsCap c.scratch_cap + step → idx ≠ 3 * fidStepsCap c.scratch_cap + step →
      (sb2[idx]?.getD 0#32).toNat = (s.scratch.scratch_buf[idx]?.getD 0#32).toNat :=
    fun idx hi h1 h2 h3 h4 => congrArg (fun o => (o.getD 0#32).toNat) (hget_lt idx hi h1 h2 h3 h4)
  refine ⟨hsc_pos, by omega, by omega, by dsimp only [bump']; omega, by dsimp only [bump']; omega,
    fun r hr => ?_⟩
  by_cases hre : r < step
  · obtain ⟨hfr, hro1, hq2, hro2, hpo, hm⟩ := hrows r hre
    have hfr_eq := gnat r (by omega) (by omega) (by omega) (by omega) (by omega)
    have hro_eq := gnat (fidStepsCap c.scratch_cap + r) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have hqn_eq := gnat (2 * fidStepsCap c.scratch_cap + r) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    have hpo_eq := gnat (3 * fidStepsCap c.scratch_cap + r) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    rw [hfr_eq, hro_eq, hqn_eq, hpo_eq]
    refine ⟨hfr, hro1, hq2, by dsimp only [bump']; omega,
      fun hr0 => ⟨(hpo hr0).1, by have := (hpo hr0).2; dsimp only [bump']; omega⟩,
      fun m hm_lt => ?_⟩
    obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar_row⟩ := hm m hm_lt
    have hcell_eq := hget_lt
      ((s.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat + m)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
    · rw [hcell_eq]; exact fidBvaRowEntryOk_congr rfl rfl rfl hok
    · rw [hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hent t ht
    · obtain ⟨hpi, hpok⟩ := hpar_row hr0; obtain ⟨_, hpo2⟩ := hpo hr0
      obtain ⟨_, _, _, hpro_le, _, _⟩ := hrows (r - 1) (by omega)
      have hpv := hget_lt
        ((s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat + m)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      have hpq := gnat (2 * fidStepsCap c.scratch_cap + (r - 1)) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hpf := gnat (r - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hpr := gnat (fidStepsCap c.scratch_cap + (r - 1)) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hpc := hget_lt
        ((s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat +
          (s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
            r]?.getD 0#32).toNat + m]?.getD 0#32).toNat)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpr, hpv, hpc, hpq, hpf]; exact ⟨hpi, fidBvaRowEntryOk_congr rfl rfl rfl hpok⟩
  · have hreq : r = step := by omega
    subst r
    rw [hget_step, hget_sc_step, hget_2sc_step, hget_3sc_step]
    refine ⟨hbest_lt, by omega, hnq2, by dsimp only [bump']; omega,
      fun _ => ⟨by omega, by dsimp only [bump']; omega⟩, fun nm hnm => ?_⟩
    obtain ⟨hpi, res, hres_lt, hres_nd, hpok, hok, hent_lt, hent_b⟩ := hnew nm hnm
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun _ => ?_⟩
    · rw [hget_nrow nm hnm]; exact fidBvaRowEntryOk_congr rfl rfl rfl hok
    · by_cases hte : t < step
      · rw [hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hent_lt t hte
      · have hts : t = step := by omega
        subst hts; rw [hget_step]; exact hent_b
    · obtain ⟨_, _, _, hpro_le, _, _⟩ := hrows (step - 1) (by omega)
      have hpv := hget_par nm hnm
      have hpq := gnat (2 * fidStepsCap c.scratch_cap + (step - 1)) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hpf := gnat (step - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hpr := gnat (fidStepsCap c.scratch_cap + (step - 1)) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hpc := hget_lt ((s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (step - 1)]?.getD
          0#32).toNat + (sb'[par_off.toNat + nm]?.getD 0#32).toNat)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpv, hpq, hpf, hpr, hpc]; exact ⟨hpi, fidBvaRowEntryOk_congr rfl rfl rfl hpok⟩

private theorem top_matrixInv_of_filter_pres {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {sb' : List (BitVec 32)} {step bump max_new : Nat}
    {nrow_off par_off : BitVec 32} (hmat : FidBvaMatrixInv c F_cur s step bump)
    (hnrow_eq : nrow_off.toNat = bump) (hpar_ge : bump ≤ par_off.toNat)
    (hpres : ∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?) :
    FidBvaMatrixInv c F_cur
      { s with scratch := { s.scratch with scratch_buf := sb' } } step bump := by
  unfold FidBvaMatrixInv at hmat ⊢; dsimp only at hmat ⊢
  rcases hmat with ⟨hsc_pos, hs1, hss, hb1, hb2, hrows⟩
  have hget_lt : ∀ idx < bump, sb'[idx]? = s.scratch.scratch_buf[idx]? :=
    fun idx hi => hpres idx (by omega) (by omega) (by omega)
  have gnat : ∀ idx < bump, (sb'[idx]?.getD 0#32).toNat =
      (s.scratch.scratch_buf[idx]?.getD 0#32).toNat :=
    fun idx hi => congrArg (fun o => (o.getD 0#32).toNat) (hget_lt idx hi)
  refine ⟨hsc_pos, hs1, hss, hb1, hb2, fun r hr => ?_⟩
  obtain ⟨hfr, hro1, hq2, hro2, hpo, hm⟩ := hrows r hr
  rw [gnat r (by omega), gnat (fidStepsCap c.scratch_cap + r) (by omega),
    gnat (2 * fidStepsCap c.scratch_cap + r) (by omega),
    gnat (3 * fidStepsCap c.scratch_cap + r) (by omega)]
  refine ⟨hfr, hro1, hq2, hro2, hpo, fun m hm_lt => ?_⟩
  obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar_row⟩ := hm m hm_lt
  refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
  · rw [hget_lt _ (by omega)]; exact fidBvaRowEntryOk_congr rfl rfl rfl hok
  · rw [hget_lt t (by omega)]; exact hent t ht
  · obtain ⟨hpi, hpok⟩ := hpar_row hr0
    have hpro := (hrows (r - 1) (by omega)).2.2.2.1; have hpo2 := (hpo hr0).2
    have hpv := hget_lt
      ((s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat + m)
      (by omega)
    have hpq := gnat (2 * fidStepsCap c.scratch_cap + (r - 1)) (by omega)
    have hpf := gnat (r - 1) (by omega)
    have hpr := gnat (fidStepsCap c.scratch_cap + (r - 1)) (by omega)
    have hpc := hget_lt
      ((s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat +
        (s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
          r]?.getD 0#32).toNat + m]?.getD 0#32).toNat) (by omega)
    rw [hpv, hpq, hpf, hpr, hpc]; exact ⟨hpi, fidBvaRowEntryOk_congr rfl rfl rfl hpok⟩

private def StepExitBody (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (sc : Nat) (step best_k : BitVec 32) (bump : Nat) (stl : FullState)
    (ml : Mem 64) : Prop :=
  (FullMem c stl ⋆ R) ml ∧ stl.LengthsOk c ∧ FullWitnessInv c F0 F_cur stl.core ∧
  FullArenaVarsNodup stl ∧ FullExtScratchOk c stl ∧ stl.core.cur_level = 0 ∧
  stl.core.dense_mode ≠ 0#64 ∧ stl.core.cur_vars = s.core.cur_vars ∧ stl.core.fuel = s.core.fuel ∧
  stl.core.arena = s.core.arena ∧ stl.core.arena_len = s.core.arena_len ∧
  stl.core.mrk = s.core.mrk ∧ stl.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  stl.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ 1 ≤ step.toNat ∧ step.toNat ≤ sc ∧
  4 * sc ≤ bump ∧ bump ≤ c.scratch_cap ∧ FidBvaMatrixInv c F_cur stl step.toNat bump ∧
  (best_k = 0#32 ∨ (1 ≤ best_k.toNat ∧ best_k.toNat < step.toNat)) ∧
  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
  (∀ r < step.toNat,
    (stl.core.lit_mark[(stl.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
    ∃ r < step.toNat, (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l)

private def StepInvBody (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (sc : Nat) (step cur_qn best_k : BitVec 32) (bump : Nat) (stl : FullState)
    (ml : Mem 64) : Prop :=
  (FullMem c stl ⋆ R) ml ∧ stl.LengthsOk c ∧ FullWitnessInv c F0 F_cur stl.core ∧
  FullArenaVarsNodup stl ∧ FullExtScratchOk c stl ∧ stl.core.cur_level = 0 ∧
  stl.core.dense_mode ≠ 0#64 ∧ stl.core.cur_vars = s.core.cur_vars ∧ stl.core.fuel = s.core.fuel ∧
  stl.core.arena = s.core.arena ∧ stl.core.arena_len = s.core.arena_len ∧
  stl.core.mrk = s.core.mrk ∧ stl.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  stl.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ 1 ≤ step.toNat ∧ step.toNat ≤ sc ∧
  4 * sc ≤ bump ∧ bump ≤ c.scratch_cap ∧
  cur_qn.toNat = (stl.scratch.scratch_buf[2 * sc + (step.toNat - 1)]?.getD 0#32).toNat ∧
  FidBvaMatrixInv c F_cur stl step.toNat bump ∧
  (best_k = 0#32 ∨ (1 ≤ best_k.toNat ∧ best_k.toNat < step.toNat)) ∧
  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
  (∀ r < step.toNat,
    (stl.core.lit_mark[(stl.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
    ∃ r < step.toNat, (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l)

private theorem stepExitBody_of_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {sc : Nat} {step cur_qn best_k : BitVec 32}
    {bump : Nat} {stl : FullState} {ml : Mem 64}
    (h : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump stl ml) :
    StepExitBody c F0 F_cur s R sc step best_k bump stl ml := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    _, h19, h20, h21, h22, h23⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩

/-! ## 2. Sub-ASTs & Step-Loop / Exit-Phase WP -/

public section

@[expose, reducible] def fidTryLitStepBlock (V : Ty → Type) (L : List Ty → Type)
    (cap_2 : Tup V [i32]) (cap_3 : Tup V [i64, i32, i64]) (cap_4 : V i64) (cap_5 : Tup V [i64])
    (Jex : Tup L [[i32, i32, i32, i32, i64]]) (cap_7 cap_8 cap_9 : V i64) :
    Tup L [[i32, i32, i32, i32, i64]] → Blocks V L [.bool] [[i32, i32, i32, i32, i64]] :=
  fun Js => Blocks.cons (fun p =>
    Expr.let_ (Op.mk (.cmp .ult i32) (Arg.var p.snd.fst, Arg.var cap_2.fst, ())) fun p_1 =>
    Expr.jnz (Arg.var p_1.fst) (Expr.let_ (Op.mk (.cmp .uge i32)
      (Arg.var p.snd.snd.fst, Arg.imm 2, ())) fun p_2 =>
    Expr.jnz (Arg.var p_2.fst) (Expr.let_ (Op.mk (.add i64)
      (Arg.var cap_3.fst, Arg.imm 1136, ())) fun p_3 =>
    Expr.load i64 (Arg.var p_3.fst) fun ld => Expr.let_ (Op.mk (.cmp .ugt i64)
      (Arg.var ld, Arg.imm 0, ())) fun p_4 =>
    Expr.jnz (Arg.var p_4.fst) (Expr.let_ (Op.mk (.add i32)
      (Arg.var cap_2.fst, Arg.var p.snd.fst, ())) fun p_5 =>
    Expr.let_ (Op.mk (.sub i32) (Arg.var p_5.fst, Arg.imm 1, ())) fun p_6 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_6.fst, ())) fun p_7 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_7.fst, Arg.imm 4, ())) fun p_8 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var cap_4, Arg.var p_8.fst, ())) fun p_9 =>
    Expr.load i32 (Arg.var p_9.fst) fun ld =>
    Expr.call (as := [i64, i32, i32, i64]) (bs := [i32]) "full_bva_scan_cands"
      (Arg.var cap_3.fst, Arg.var ld, Arg.var p.snd.snd.fst, Arg.var cap_5.fst, ()) fun p_10 =>
    Expr.call (as := [i64, i32, i32]) (bs := [i32]) "full_bva_pick_cand"
      (Arg.var cap_3.fst, Arg.var p_10.fst, Arg.var cap_3.snd.fst, ()) fun p_11 =>
    Expr.let_ (Op.mk (.cmp .eq i32) (Arg.var p_11.fst, Arg.imm 4294967295, ())) fun p_12 =>
    Expr.jnz (Arg.var p_12.fst) (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst,
      Arg.var p.snd.snd.fst, Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ()))
    (Expr.let_ (Op.mk (.add i64) (Arg.var cap_3.fst, Arg.imm 1136, ())) fun p_13 =>
    Expr.load i64 (Arg.var p_13.fst) fun ld_1 =>
    Expr.let_ (Op.mk (.cmp .eq i64) (Arg.var ld_1, Arg.imm 0, ())) fun p_14 =>
    Expr.jnz (Arg.var p_14.fst) (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst,
      Arg.var p.snd.snd.fst, Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ()))
    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.fst, ())) fun p_15 =>
    Expr.let_ (Op.mk (.sub i64) (Arg.var cap_7, Arg.var p_15.fst, ())) fun p_16 =>
    Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p_16.fst, ())) fun p_17 =>
    Expr.let_ (Op.mk (.lshr i32) (Arg.var p_17.fst, Arg.imm 1, ())) fun p_18 =>
    Expr.group (sig := [[i32]]) (fun _Js_1 => Blocks.cons (fun p_19 =>
    Expr.let_ (Op.mk (.cmp .ult i32) (Arg.var p_19.fst, Arg.imm 2, ())) fun p_20 =>
    Expr.jnz (Arg.var p_20.fst) (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst,
      Arg.var p.snd.snd.fst, Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ()))
    (Expr.let_ (Op.mk (.add i32) (Arg.var p.fst, Arg.var p_19.fst, ())) fun p_21 =>
    Expr.call (as := [i64, i32, i32, i32, i32, i32]) (bs := [i32]) "full_bva_filter_row"
      (Arg.var cap_3.fst, Arg.var ld, Arg.var p.fst, Arg.var p_21.fst,
       Arg.var p.snd.snd.fst, Arg.var p_11.fst, ()) fun p_22 =>
    Expr.let_ (Op.mk (.cmp .ult i32) (Arg.var p_22.fst, Arg.imm 2, ())) fun p_23 =>
    Expr.jnz (Arg.var p_23.fst) (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst,
      Arg.var p_22.fst, Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ()))
    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.snd.fst, ())) fun p_24 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_24.fst, Arg.imm 4, ())) fun p_25 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var cap_4, Arg.var p_25.fst, ())) fun p_26 =>
    Expr.store (Arg.var p_11.fst) (Arg.var p_26.fst)
    (Expr.let_ (Op.mk (.add i32) (Arg.var cap_2.fst, Arg.var p.snd.fst, ())) fun p_27 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_27.fst, ())) fun p_28 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_28.fst, Arg.imm 4, ())) fun p_29 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var cap_4, Arg.var p_29.fst, ())) fun p_30 =>
    Expr.store (Arg.var p.fst) (Arg.var p_30.fst)
    (Expr.let_ (Op.mk (.mul i32) (Arg.imm 2, Arg.var cap_2.fst, ())) fun p_31 =>
    Expr.let_ (Op.mk (.add i32) (Arg.var p_31.fst, Arg.var p.snd.fst, ())) fun p_32 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_32.fst, ())) fun p_33 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_33.fst, Arg.imm 4, ())) fun p_34 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var cap_4, Arg.var p_34.fst, ())) fun p_35 =>
    Expr.store (Arg.var p_22.fst) (Arg.var p_35.fst)
    (Expr.let_ (Op.mk (.mul i32) (Arg.imm 3, Arg.var cap_2.fst, ())) fun p_36 =>
    Expr.let_ (Op.mk (.add i32) (Arg.var p_36.fst, Arg.var p.snd.fst, ())) fun p_37 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_37.fst, ())) fun p_38 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_38.fst, Arg.imm 4, ())) fun p_39 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var cap_4, Arg.var p_39.fst, ())) fun p_40 =>
    Expr.store (Arg.var p_21.fst) (Arg.var p_40.fst)
    (Expr.let_ (Op.mk (.add i32) (Arg.var p_21.fst, Arg.var p_22.fst, ())) fun p_41 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_11.fst, ())) fun p_42 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var cap_8, Arg.var p_42.fst, ())) fun p_43 =>
    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 1, ())) fun p_44 =>
    Expr.store (Arg.var p_44.fst) (Arg.var p_43.fst)
    (Expr.let_ (Op.mk (.add i32) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p_45 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_45.fst, ())) fun p_46 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_22.fst, ())) fun p_47 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_46.fst, Arg.var p_47.fst, ())) fun p_48 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var p_46.fst, Arg.var p_47.fst, ())) fun p_49 =>
    Expr.group (sig := [[i32, i64]]) (fun _Js_2 => Blocks.cons (fun q => Expr.jump Js.fst
      (Arg.var p_41.fst, Arg.var p_45.fst, Arg.var p_22.fst, Arg.var q.fst, Arg.var q.snd.fst,
       ())) Blocks.nil) fun Js =>
    Expr.let_ (Op.mk (.cmp .ugt i64) (Arg.var p_48.fst, Arg.var p_49.fst, ())) fun p_50 =>
    Expr.jnz (Arg.var p_50.fst)
    (Expr.let_ (Op.mk (.sub i64) (Arg.var p_48.fst, Arg.var p_49.fst, ())) fun p_51 =>
    Expr.group (sig := [[i32, i64]]) (fun _Js_2 => Blocks.cons (fun q =>
      Expr.jump Js.fst (Arg.var q.fst, Arg.var q.snd.fst, ())) Blocks.nil) fun Js =>
    Expr.let_ (Op.mk (.cmp .ugt i64) (Arg.var p_51.fst, Arg.var cap_9, ())) fun p_52 =>
    Expr.jnz (Arg.var p_52.fst)
    (Expr.let_ (Op.mk (.cmp .ugt i64) (Arg.var p_51.fst, Arg.var p.snd.snd.snd.snd.fst, ()))
      fun p_53 =>
    Expr.jnz (Arg.var p_53.fst)
    (Expr.let_ (Op.mk (.sub i32) (Arg.var p_45.fst, Arg.imm 1, ())) fun q =>
      Expr.jump Js.fst (Arg.var q.fst, Arg.var p_51.fst, ()))
    (Expr.jump Js.fst (Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())))
    (Expr.jump Js.fst (Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())))
    (Expr.jump Js.fst (Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ()))))))))))
      Blocks.nil)
    fun Js => Expr.let_ (Op.mk (.cmp .ugt i32)
      (Arg.var p_18.fst, Arg.var p.snd.snd.fst, ())) fun p_19 =>
    Expr.jnz (Arg.var p_19.fst) (Expr.jump Js.fst (Arg.var p.snd.snd.fst, ()))
      (Expr.jump Js.fst (Arg.var p_18.fst, ())))))
    (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst,
      Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())))
    (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst,
      Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())))
    (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst,
      Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ()))) Blocks.nil

@[expose, reducible] def step7TryLitExitBlock (V : Ty → Type) (L : List Ty → Type)
    (ecap_2 ecap_3 : V i64) (ecap_4 : Tup V [i64, i32, i64]) :
    Tup L [[i32, i32, i32, i32, i64]] → Blocks V L [.bool] [[i32, i32, i32, i32, i64]] :=
  fun _Js => Blocks.cons (fun p =>
    Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun p_1 =>
    Expr.let_ (Op.mk (.cmp .ult i32) (Arg.var p_1.fst, Arg.var p.snd.fst, ())) fun p_2 =>
    Expr.jnz (Arg.var p_2.fst)
    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_1.fst, ())) fun p =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ecap_2, Arg.var p.fst, ())) fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ecap_3, Arg.var p.fst, ())) fun p =>
    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_3 =>
    Expr.store (Arg.var p_3.fst) (Arg.var p.fst)
    (Expr.let_ (Op.mk (.add i32) (Arg.var p_1.fst, Arg.imm 1, ())) fun p =>
      Expr.jump Js.fst (Arg.var p.fst, ())))
    (Expr.let_ (Op.mk (.cmp .eq i32) (Arg.var p.snd.snd.snd.fst, Arg.imm 0, ())) fun p_3 =>
    Expr.jnz (Arg.var p_3.fst) (Expr.ret (Arg.imm false, ()))
    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.snd.snd.snd.fst, ())) fun p_4 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ecap_4.fst, Arg.imm 1144, ())) fun p_5 =>
    Expr.store (Arg.var p_4.fst) (Arg.var p_5.fst)
    (Expr.call (as := [i64, i32]) (bs := [.bool]) "full_bva_commit"
      (Arg.var ecap_4.fst, Arg.var p.snd.snd.snd.fst, ()) fun p =>
    Expr.ret (Arg.var p.fst, ()))))) Blocks.nil) fun Js => Expr.jump Js.fst (Arg.imm 0, ()))
    Blocks.nil

end

private theorem top_layout_one {c : FullCfg} {s : FullState} : Step7BvaLayout c s 1 :=
  ⟨fun _ hr hr0 => absurd hr0 (by omega), fun _ _ hrr hr' => absurd hrr (by omega)⟩

private theorem top_layout_of_pre {c : FullCfg} {s s' : FullState} {step bump : Nat}
    (hstep : step ≤ fidStepsCap c.scratch_cap) (h4 : 4 * fidStepsCap c.scratch_cap ≤ bump)
    (hpres : ∀ idx < bump, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : Step7BvaLayout c s step) : Step7BvaLayout c s' step := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun r hr hr0 => ?_, fun r r' hrr hr' => ?_⟩
  · rw [hpres _ (by omega), hpres _ (by omega), hpres _ (by omega)]; exact h1 r hr hr0
  · rw [hpres _ (by omega), hpres _ (by omega), hpres _ (by omega),
      hpres _ (by omega), hpres _ (by omega)]
    exact h2 r r' hrr hr'

private theorem top_layout_extend {c : FullCfg} {F_cur : List (List Nat)} {s st : FullState}
    {sb3 : List (BitVec 32)} {step bump max_new : Nat}
    {best_lit new_qn nrow_off par_off : BitVec 32}
    (hstep1 : 1 ≤ step) (hstep_sc : step < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s step bump) (hlay : Step7BvaLayout c s step)
    (hsb3_len : sb3.length = c.scratch_cap) (hnrow_eq : nrow_off.toNat = bump)
    (hpar_eq : par_off.toNat = bump + max_new) (hnq_le : new_qn.toNat ≤ max_new)
    (hmax_le : max_new ≤
      (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + (step - 1)]?.getD 0#32).toNat)
    (h4 : 4 * fidStepsCap c.scratch_cap ≤ bump)
    (hpres : ∀ idx < bump, sb3[idx]? = s.scratch.scratch_buf[idx]?)
    (hst : st.scratch.scratch_buf =
      (((sb3.set step best_lit).set (fidStepsCap c.scratch_cap + step) nrow_off).set
        (2 * fidStepsCap c.scratch_cap + step) new_qn).set
        (3 * fidStepsCap c.scratch_cap + step) par_off) :
    Step7BvaLayout c st (step + 1) := by
  have h4c := fidStepsCap_mul4_le c.scratch_cap
  obtain ⟨_, _, _, _, _, hrows⟩ := hmat; obtain ⟨hl1, hl2⟩ := hlay
  have g_pre : ∀ idx < bump, idx ≠ step → idx ≠ fidStepsCap c.scratch_cap + step →
      idx ≠ 2 * fidStepsCap c.scratch_cap + step → idx ≠ 3 * fidStepsCap c.scratch_cap + step →
      st.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi h1 h2 h3 h4 => by
    rw [hst, List.getElem?_set_ne (Ne.symm h4), List.getElem?_set_ne (Ne.symm h3),
      List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]
    exact hpres idx hi
  have hro_s : st.scratch.scratch_buf[fidStepsCap c.scratch_cap + step]?.getD 0#32 = nrow_off := by
    rw [hst, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
  have hqn_s : st.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + step]?.getD 0#32 =
      new_qn := by
    rw [hst, List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set, List.length_set]; omega), Option.getD_some]
  have hpo_s : st.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + step]?.getD 0#32 =
      par_off := by
    rw [hst, List.getElem?_set_self
      (by rw [List.length_set, List.length_set, List.length_set]; omega), Option.getD_some]
  refine ⟨fun r hr hr0 => ?_, fun r r' hrr hr' => ?_⟩
  · by_cases hrs : r < step
    · rw [g_pre (fidStepsCap c.scratch_cap + r)
          (by omega) (by omega) (by omega) (by omega) (by omega),
        g_pre (2 * fidStepsCap c.scratch_cap + r)
          (by omega) (by omega) (by omega) (by omega) (by omega),
        g_pre (3 * fidStepsCap c.scratch_cap + r)
          (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl1 r hrs hr0
    · rw [show r = step by omega, hro_s, hqn_s, hpo_s, hnrow_eq, hpar_eq]; omega
  · by_cases hrs' : r' < step
    · rw [g_pre (fidStepsCap c.scratch_cap + r)
          (by omega) (by omega) (by omega) (by omega) (by omega),
        g_pre (2 * fidStepsCap c.scratch_cap + r)
          (by omega) (by omega) (by omega) (by omega) (by omega),
        g_pre (3 * fidStepsCap c.scratch_cap + r)
          (by omega) (by omega) (by omega) (by omega) (by omega),
        g_pre (fidStepsCap c.scratch_cap + r')
          (by omega) (by omega) (by omega) (by omega) (by omega),
        g_pre (2 * fidStepsCap c.scratch_cap + r')
          (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl2 r r' hrr hrs'
    · have hr_st : r < step := by omega
      rw [show r' = step by omega,
        g_pre (fidStepsCap c.scratch_cap + r)
          (by omega) (by omega) (by omega) (by omega) (by omega),
        g_pre (2 * fidStepsCap c.scratch_cap + r)
          (by omega) (by omega) (by omega) (by omega) (by omega),
        g_pre (3 * fidStepsCap c.scratch_cap + r)
          (by omega) (by omega) (by omega) (by omega) (by omega),
        hro_s, hqn_s, hnrow_eq]
      obtain ⟨_, _, _, hro2, hpo, _⟩ := hrows r hr_st
      have hq : (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + (step - 1)]?.getD
          0#32).toNat ≤ (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r]?.getD
          0#32).toNat := by
        by_cases hre : r = step - 1
        · exact Nat.le_of_eq (by rw [hre])
        · exact (hl2 r (step - 1) (by omega) (by omega)).1
      exact ⟨by omega, hro2, fun hr0 => (hpo hr0).2⟩

private theorem top_exit_phase_wp (Γ : Env)
    (hCommit : Γ.Has "full_bva_commit" step7BvaCommitSpec)
    {Q : Post [.bool]} {X : XPost} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s stl : FullState} {R : Mem 64 → Prop} {f0 bump step cur_qn best_k : BitVec 32}
    {init_cv0 best_red : BitVec 64} {ml : Mem 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hlm : FullLitMarksClear c s)
    (hlay : Step7BvaLayout c stl step.toNat)
    (hexit : StepExitBody c F0 F_cur s R (fidStepsCap c.scratch_cap) step best_k bump.toNat stl ml)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → ∃ bk, Step7BvaCommittedOk c s' bk) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (Blocks.get (step7TryLitExitBlock Val Cont c.pScratchBuf c.pLitMark
        (c.hdr, f0, init_cv0, ()) ((fun _ _ => False), ()))
      .here (bump, step, cur_qn, best_k, best_red, ())) ml := by
  let sc_n := fidStepsCap c.scratch_cap
  have hmx : c.max_vars < 2 * 2 ^ 28 := by simpa only [dimacsBound] using c.hmaxv
  have hsc_le : sc_n ≤ 256 := fidStepsCap_le_256 c.scratch_cap
  obtain ⟨hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl,
    hall, hmrkl, html, htrl, hst1, hst_sc, hbump_ge, hbump_le,
    hmatl, hbkl, hlml_hi, hlml_set, hlml_only⟩ := hexit
  dsimp only [step7TryLitExitBlock, Blocks.get]
  refine wp_loop_inv (ts := [i32])
    (fun (ci, ()) mc => ∃ lmi : List (BitVec 8),
      (FullMem c { stl with core := { stl.core with lit_mark := lmi } } ⋆ R) mc ∧
      lmi.length = 2 * c.max_vars ∧ ci.toNat ≤ step.toNat ∧
      (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
        ∃ r, ci.toNat ≤ r ∧ r < step.toNat ∧
          (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l))
    (fun (ci, _) _ => step.toNat - ci.toNat)
    (fun Jci hJci => hJci (0#32, ()) ml ⟨stl.core.lit_mark, hml, hlenl.core_ok.lit_mark_len,
      Nat.zero_le _, hlml_hi, fun l hl hne =>
        let ⟨r, hr, heq⟩ := hlml_only l hl hne; ⟨r, Nat.zero_le _, hr, heq⟩⟩)
    (fun Jci (ci, ()) mc ⟨lmi, hmc, hlmi_l, hci_le, hlmi_hi, hlmi_only⟩ ihci => ?_)
  c0_hsplit
  · have hci_lt : ci.toNat < step.toNat := by assumption
    have hci_sb : (BitVec.setWidth 64 ci).toNat < stl.scratch.scratch_buf.length := by
      rw [fid_bv64_32, hlenl.scratch_ok.scratch_buf_len]; omega
    have hci_sb' : ci.toNat < stl.scratch.scratch_buf.length := by
      simpa only [fid_bv64_32] using hci_sb
    have hci_lm : (BitVec.setWidth 64
        (stl.scratch.scratch_buf[(BitVec.setWidth 64 ci).toNat]'hci_sb)).toNat < lmi.length := by
      have hr_lt := (hmatl.2.2.2.2.2 ci.toNat hci_lt).1
      rw [List.getElem?_eq_getElem hci_sb', Option.getD_some] at hr_lt
      rw [fid_bv64_32, hlmi_l]; exact Nat.lt_of_lt_of_le hr_lt (Nat.mul_le_mul_left 2 (by omega))
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := fid_bv32_add1 (by omega)
    c0_hsteps_nogrp
    exact ihci (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
      ⟨lmi.set (stl.scratch.scratch_buf[ci.toNat]'hci_sb').toNat 0#8,
       by simpa only [fid_bv64_32] using hm, by rw [List.length_set, hlmi_l],
       by rw [hci1]; exact hci_lt,
       fun l hl => by
         by_cases he : l = (stl.scratch.scratch_buf[ci.toNat]'hci_sb').toNat
         · subst he; rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
         · rw [List.getElem?_set_ne (Ne.symm he)]; exact hlmi_hi l hl,
       fun l hl hne => by
         by_cases he : l = (stl.scratch.scratch_buf[ci.toNat]'hci_sb').toNat
         · subst he; rw [List.getElem?_set_self (by omega), Option.getD_some] at hne
           exact absurd rfl hne
         · rw [List.getElem?_set_ne (Ne.symm he)] at hne
           obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
           have hner : r ≠ ci.toNat := fun h => by
             subst h; rw [List.getElem?_eq_getElem hci_sb', Option.getD_some] at heq
             exact he heq.symm
           exact ⟨r, by rw [hci1]; omega, hr2, heq⟩⟩
  · have hlm_clr_done :
        FullLitMarksClear c { stl with core := { stl.core with lit_mark := lmi } } := by
      refine top_clear_lm_done (stepf := step.toNat)
        (fun v hv => by have := hlm.1 v hv; rwa [hmrkl]) hlmi_hi (fun l hl hne => ?_)
      obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
      have hci_eq : ci.toNat = step.toNat := by
        have h1 : ¬ ci.toNat < step.toNat := by assumption
        omega
      rw [hci_eq] at hr1; exact ⟨r, hr1, hr2, heq⟩
    let stc : FullState := { stl with core := { stl.core with lit_mark := lmi } }
    have hinv_clr : FullDenseInvW c F0 F_cur stc :=
      ⟨⟨{ hlenl.core_ok with lit_mark_len := hlmi_l }, hlenl.scratch_ok⟩,
       fullWitnessInv_with_litMark hwl lmi, hlm_clr_done, hndl, hextl, hlv0l, hdml⟩
    have hmat_c : FidBvaMatrixInv c F_cur stc step.toNat bump.toNat :=
      fidBvaMatrixInv_congr (s := stl) (s' := stc) rfl rfl rfl rfl hmatl
    c0_hsplit
    · exact hQ false stc mc hinv_clr.toDense (hcvl ▸ Nat.le_refl _)
        (fun h => by contradiction) (fun h => by contradiction) hfuell html htrl hmc
    · have hbk1 : 1 ≤ best_k.toNat := by
        rcases hbkl with rfl | ⟨h1, _⟩; exact absurd rfl (by assumption); exact h1
      have hbk_lt_sc : best_k.toNat < sc_n := by
        rcases hbkl with rfl | ⟨_, h2⟩
        · exact absurd rfl (by assumption)
        · exact Nat.lt_of_lt_of_le h2 hst_sc
      c0_hsteps_nogrp
      let st_tc : FullState :=
        { stc with scratch := { stc.scratch with res_sz := BitVec.setWidth 64 best_k } }
      have hinv_tc : FullDenseInvW c F0 F_cur st_tc :=
        fullDenseInv_with_core_aux (tc' := stc.core.tmp_cnt) (tl' := stc.core.tmp_len)
          (sc' := st_tc.scratch) hinv_clr hinv_clr.1.core_ok.repr_len
          hinv_clr.1.core_ok.min_clr_len_arr hinv_clr.1.core_ok.tmp_len_arr
          hinv_clr.1.core_ok.flags_len hinv_clr.1.core_ok.tmp_len_le
          { hinv_clr.1.scratch_ok with } rfl rfl
      have hmat_tc : Step7BvaMatrixInv c F_cur st_tc (best_k.toNat + 1) bump.toNat :=
        ⟨fidBvaMatrixInv_congr (s := stc) rfl rfl rfl rfl
          (top_matrixInv_substep (k := best_k.toNat + 1) (by omega) (by
            rcases hbkl with rfl | ⟨_, h2⟩; exact absurd rfl (by assumption); exact h2) hmat_c),
         Step7BvaLayout.congr (s := stl) rfl (Step7BvaLayout.mono (by
            rcases hbkl with rfl | ⟨_, h2⟩; exact absurd rfl (by assumption); omega) hlay)⟩
      refine wp_call_of_spec _ _ (hCommit _ _ _ _ ?_)
      refine ⟨c, F0, F_cur, st_tc, R, bump.toNat, rfl, hinv_tc, hbk1, hbk_lt_sc, hmat_tc,
        (BitVec.ofNat_toNat 64 best_k).symm, hm,
        fun ok s' m' hinv' hcv' hcv_inc hok' hfuel' htm' htr' hm' => ?_⟩
      exact hQ ok s' m' hinv' (by rw [← hcvl]; exact hcv')
        (fun h => by rw [← hcvl]; exact hcv_inc h) (fun h => ⟨best_k.toNat, hok' h⟩)
        (hfuel'.trans hfuell) (htm'.trans html) (htr'.trans htrl) hm'

private theorem top_step_scan_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s stl : FullState} {R : Mem 64 → Prop} {sc bump : Nat}
    {step cur_qn best_k : BitVec 32} {ml : Mem 64}
    (hinv : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump stl ml)
    (hsc_eq : sc = fidStepsCap c.scratch_cap) :
    let ro := (stl.scratch.scratch_buf[sc + (step.toNat - 1)]?.getD 0#32).toNat
    ro + cur_qn.toNat ≤ c.scratch_cap ∧
    ∀ qi < cur_qn.toNat,
      let w := stl.scratch.scratch_buf[ro + qi]?.getD 0#32
      if w &&& 0x80000000#32 ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * stl.core.cur_vars
      else w.toNat ∈ fullArenaClauseRefs stl ∧ fullArenaClauseGarb stl w.toNat = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hqn, hmat, _, _, _, _⟩ := hinv
  have hrow := hmat.2.2.2.2.2 (step.toNat - 1) (by omega)
  have hro_le := hrow.2.2.2.1
  have hqn_eq : cur_qn.toNat = (stl.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
      (step.toNat - 1)]?.getD 0#32).toNat := hsc_eq ▸ hqn
  refine ⟨by rw [hsc_eq]; omega, fun qi hqi => ?_⟩
  rw [hsc_eq]; obtain ⟨_, _, _, hok, _⟩ := hrow.2.2.2.2.2 qi (hqn_eq ▸ hqi)
  unfold FidBvaRowEntryOk at hok; split at hok
  · rename_i hbin; rw [ite_eq_left hbin]; exact hok.1
  · rename_i hbin; rw [ite_eq_right hbin]; exact ⟨hok.1, hok.2.1⟩

private theorem top_step_upd_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s stl st1 st2 st3 : FullState} {R : Mem 64 → Prop} {sc bump max_new : Nat}
    {step cur_qn best_k best_lit nrow_off par_off new_qn : BitVec 32} {ml m3 : Mem 64}
    (hinv : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump stl ml)
    (hsc_eq : sc = fidStepsCap c.scratch_cap) (hsc_pos : 0 < sc) (hsc_le : sc ≤ 256)
    (hstep_lt : step.toNat < sc)
    (hden1 : st1.core = stl.core ∧ st1.scratch.scratch_buf = stl.scratch.scratch_buf ∧
      st1.scratch.tarjan_mark = stl.scratch.tarjan_mark ∧
      st1.scratch.tarjan_reach = stl.scratch.tarjan_reach)
    (hden2 : FullDenseInvNoLm c F0 F_cur st2)
    (hst2_eq : st2.core.cur_vars = st1.core.cur_vars ∧ st2.core.fuel = st1.core.fuel ∧
      st2.core.arena = st1.core.arena ∧ st2.core.arena_len = st1.core.arena_len ∧
      st2.core.lit_mark = st1.core.lit_mark ∧ st2.core.mrk = st1.core.mrk ∧
      st2.scratch.tarjan_mark = st1.scratch.tarjan_mark ∧
      st2.scratch.tarjan_reach = st1.scratch.tarjan_reach ∧
      st2.scratch.scratch_buf = st1.scratch.scratch_buf)
    (hbl_lt : best_lit.toNat < 2 * st1.core.cur_vars)
    (hst3 : st3 = { st2 with scratch := { st2.scratch with
      scratch_buf := st3.scratch.scratch_buf, ant_sz := st3.scratch.ant_sz } })
    (hsb3_len : st3.scratch.scratch_buf.length = c.scratch_cap)
    (hnrow : nrow_off.toNat = bump) (hpar : par_off.toNat = bump + max_new)
    (hpar_cap : par_off.toNat + max_new ≤ c.scratch_cap) (hnqn_le : new_qn.toNat ≤ max_new)
    (hnqn2 : 2 ≤ new_qn.toNat)
    (hkeep3 : ∀ idx < c.scratch_cap, ¬(nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬(par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      st3.scratch.scratch_buf[idx]? = stl.scratch.scratch_buf[idx]?)
    (hrows3 : ∀ nm < new_qn.toNat,
      let pi := (st3.scratch.scratch_buf[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res, (∀ x ∈ res, x < 2 * st2.core.cur_vars) ∧
        (res.map (· / 2)).Nodup ∧
        FidBvaRowEntryOk F_cur st2 (stl.scratch.scratch_buf[step.toNat - 1]?.getD 0#32).toNat
          (stl.scratch.scratch_buf[(stl.scratch.scratch_buf[sc + (step.toNat - 1)]?.getD
            0#32).toNat + pi]?.getD 0#32) res ∧
        FidBvaRowEntryOk F_cur st2 best_lit.toNat
          (st3.scratch.scratch_buf[nrow_off.toNat + nm]?.getD 0#32) res ∧
        (∀ t < step.toNat, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((stl.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res)))
    {bk' : BitVec 32} (hbk' : bk' = best_k ∨ bk' = step)
    (hm4 : (FullMem c { st3 with
      core := { st3.core with lit_mark := st3.core.lit_mark.set best_lit.toNat 1#8 },
      scratch := { st3.scratch with
        scratch_buf := (((st3.scratch.scratch_buf.set step.toNat best_lit).set
          (sc + step.toNat) nrow_off).set (2 * sc + step.toNat) new_qn).set
          (3 * sc + step.toNat) par_off } } ⋆ R) m3) :
    StepInvBody c F0 F_cur s R sc (step + 1#32) new_qn bk' (par_off.toNat + new_qn.toNat)
      { st3 with
        core := { st3.core with lit_mark := st3.core.lit_mark.set best_lit.toNat 1#8 },
        scratch := { st3.scratch with
          scratch_buf := (((st3.scratch.scratch_buf.set step.toNat best_lit).set
            (sc + step.toNat) nrow_off).set (2 * sc + step.toNat) new_qn).set
            (3 * sc + step.toNat) par_off } } m3 := by
  obtain ⟨_, hlen_l, _, _, _, _, _, hcv_l, hfu_l, har_l, hal_l, hmrk_l, htm_l, htr_l,
    hstep1, _, h4sc_b, _, hqn_l, hmat_l, hbk_l, hlm_hi, hlm_set, hlm_only⟩ := hinv
  let sb4 := (((st3.scratch.scratch_buf.set step.toNat best_lit).set
    (sc + step.toNat) nrow_off).set (2 * sc + step.toNat) new_qn).set (3 * sc + step.toNat) par_off
  let lm4 := st3.core.lit_mark.set best_lit.toNat 1#8
  let st4 : FullState :=
    { st3 with core := { st3.core with lit_mark := lm4 },
               scratch := { st3.scratch with scratch_buf := sb4 } }
  have hmx := c.hmaxv; have hsc_c := c.hscr; unfold dimacsBound at hmx hsc_c
  have hcv2_le : st2.core.cur_vars ≤ c.max_vars := hden2.1.core_ok.cur_vars_le
  have hst3_len : st3.LengthsOk c := by
    rw [hst3]; exact ⟨hden2.1.core_ok, { hden2.1.scratch_ok with scratch_buf_len := hsb3_len }⟩
  have hlm4_len : lm4.length = 2 * c.max_vars := by
    dsimp only [lm4]; rw [List.length_set, hst3, hden2.1.core_ok.lit_mark_len]
  have hsb4_len : sb4.length = c.scratch_cap := by simp [sb4, hsb3_len]
  have hst4_len : st4.LengthsOk c :=
    ⟨{ hst3_len.core_ok with lit_mark_len := hlm4_len },
     { hst3_len.scratch_ok with scratch_buf_len := hsb4_len }⟩
  have hw4 : FullWitnessInv c F0 F_cur st4.core := by
    dsimp only [st4]; rw [hst3]; exact fullWitnessInv_with_litMark hden2.2.1 lm4
  have hnd4 : FullArenaVarsNodup st4 := by
    unfold FullArenaVarsNodup; dsimp only [st4]; rw [hst3]; exact hden2.2.2.1
  have hext4 : FullExtScratchOk c st4 := by
    dsimp only [st4]; rw [hst3]
    exact FullExtScratchOk.of_pres hden2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr => hr
  have hstep1_bv : (step + 1#32).toNat = step.toNat + 1 := fid_bv32_add1 (by omega)
  have hmat2 : FidBvaMatrixInv c F_cur st2 step.toNat bump :=
    fidBvaMatrixInv_congr (by rw [hst2_eq.1, hden1.1]) (by rw [hst2_eq.2.2.1, hden1.1])
      (by rw [hst2_eq.2.2.2.1, hden1.1]) (hst2_eq.2.2.2.2.2.2.2.2.trans hden1.2.1) hmat_l
  have hkeep3' : ∀ idx < c.scratch_cap,
      ¬(nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬(par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      st3.scratch.scratch_buf[idx]? = st2.scratch.scratch_buf[idx]? := fun idx hi h1 h2 => by
    rw [hst2_eq.2.2.2.2.2.2.2.2, hden1.2.1]; exact hkeep3 idx hi h1 h2
  have hrows3' : ∀ nm < new_qn.toNat,
      let pi := (st3.scratch.scratch_buf[par_off.toNat + nm]?.getD 0#32).toNat
      pi < (st2.scratch.scratch_buf[2 * sc + (step.toNat - 1)]?.getD 0#32).toNat ∧
        ∃ res, (∀ x ∈ res, x < 2 * st2.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
          FidBvaRowEntryOk F_cur st2 (st2.scratch.scratch_buf[step.toNat - 1]?.getD 0#32).toNat
            (st2.scratch.scratch_buf[(st2.scratch.scratch_buf[sc + (step.toNat - 1)]?.getD
              0#32).toNat + pi]?.getD 0#32) res ∧
          FidBvaRowEntryOk F_cur st2 best_lit.toNat
            (st3.scratch.scratch_buf[nrow_off.toNat + nm]?.getD 0#32) res ∧
          (∀ t < step.toNat, (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((st2.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res)) := fun nm hnm => by
    have hr := hrows3 nm hnm; rw [hst2_eq.2.2.2.2.2.2.2.2, hden1.2.1]
    exact ⟨by simpa [← hsc_eq, ← hqn_l] using hr.1, hr.2⟩
  have hmat_ext := top_matrixInv_extend_step (c := c) (F_cur := F_cur) (s := st2)
    (sb' := st3.scratch.scratch_buf) (step := step.toNat) (bump := bump) (max_new := max_new)
    (sc := sc) (best_lit := best_lit) (new_qn := new_qn) (nrow_off := nrow_off) (par_off := par_off)
    hsc_eq hstep1 hstep_lt hmat2 hsb3_len (by omega) hnrow hpar hpar_cap hnqn_le hnqn2
    hkeep3' hrows3'
  have hlm4 := top_extend_lm (maxv := c.max_vars) (cap := c.scratch_cap) (sc := sc)
    (step := step.toNat) (bump := bump) (max_new := max_new) (lm := st2.core.lit_mark)
    (sb2 := stl.scratch.scratch_buf) (sb3 := st3.scratch.scratch_buf) (bl := best_lit)
    (new_qn := new_qn) (nrow_off := nrow_off) (par_off := par_off) hsc_pos hstep_lt
    (by rw [hst2_eq.2.2.2.2.1, hden1.1]; exact hlen_l.core_ok.lit_mark_len) hsb3_len (by omega)
    hnrow hpar h4sc_b hpar_cap hkeep3 (by rw [hst2_eq.2.2.2.2.1, hden1.1]; exact hlm_hi)
    (by rw [hst2_eq.2.2.2.2.1, hden1.1]; exact hlm_set)
    (by rw [hst2_eq.2.2.2.2.1, hden1.1]; exact hlm_only)
  have hst3_lm : st3.core.lit_mark = st2.core.lit_mark := by rw [hst3]
  have hst4_st2 : st4.core.cur_vars = st2.core.cur_vars ∧ st4.core.fuel = st2.core.fuel ∧
      st4.core.arena = st2.core.arena ∧ st4.core.arena_len = st2.core.arena_len ∧
      st4.core.mrk = st2.core.mrk ∧ st4.core.cur_level = st2.core.cur_level ∧
      st4.core.dense_mode = st2.core.dense_mode ∧
      st4.scratch.tarjan_mark = st2.scratch.tarjan_mark ∧
      st4.scratch.tarjan_reach = st2.scratch.tarjan_reach := by
    dsimp only [st4]; rw [hst3]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcqn4 : new_qn.toNat =
      (st4.scratch.scratch_buf[2 * sc + ((step + 1#32).toNat - 1)]?.getD 0#32).toNat := by
    change new_qn.toNat = (sb4[2 * sc + ((step + 1#32).toNat - 1)]?.getD 0#32).toNat
    rw [hstep1_bv, show step.toNat + 1 - 1 = step.toNat from by omega]; dsimp only [sb4]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hsb3_len]; omega),
      Option.getD_some]
  refine ⟨hm4, hst4_len, hw4, hnd4, hext4, by rw [hst4_st2.2.2.2.2.2.1]; exact hden2.2.2.2.2.1,
    by rw [hst4_st2.2.2.2.2.2.2.1]; exact hden2.2.2.2.2.2,
    by rw [hst4_st2.1, hst2_eq.1, hden1.1]; exact hcv_l,
    by rw [hst4_st2.2.1, hst2_eq.2.1, hden1.1]; exact hfu_l,
    by rw [hst4_st2.2.2.1, hst2_eq.2.2.1, hden1.1]; exact har_l,
    by rw [hst4_st2.2.2.2.1, hst2_eq.2.2.2.1, hden1.1]; exact hal_l,
    by rw [hst4_st2.2.2.2.2.1, hst2_eq.2.2.2.2.2.1, hden1.1]; exact hmrk_l,
    by rw [hst4_st2.2.2.2.2.2.2.2.1, hst2_eq.2.2.2.2.2.2.1, hden1.2.2.1]; exact htm_l,
    by rw [hst4_st2.2.2.2.2.2.2.2.2, hst2_eq.2.2.2.2.2.2.2.1, hden1.2.2.2]; exact htr_l,
    by rw [hstep1_bv]; omega, by rw [hstep1_bv]; omega, by omega, by omega, hcqn4,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hmat4 : FidBvaMatrixInv c F_cur st4 (step.toNat + 1) (par_off.toNat + new_qn.toNat) :=
      @fidBvaMatrixInv_congr c F_cur
        { st2 with scratch := { st2.scratch with scratch_buf := sb4 } } st4 (step.toNat + 1)
        (par_off.toNat + new_qn.toNat) hst4_st2.1 hst4_st2.2.2.1 hst4_st2.2.2.2.1 rfl hmat_ext
    rwa [hstep1_bv]
  · rcases hbk' with rfl | rfl
    · rcases hbk_l with rfl | ⟨h1, h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, by rw [hstep1_bv]; omega⟩
    · exact Or.inr ⟨hstep1, by rw [hstep1_bv]; omega⟩
  · dsimp only [st4]; rw [hst3_lm]; exact hlm4.1
  · rw [hstep1_bv]; dsimp only [st4]; rw [hst3_lm]; exact hlm4.2.1
  · intro l hl hnz; rw [hstep1_bv]; dsimp only [st4] at hnz
    rw [hst3_lm] at hnz; exact hlm4.2.2 l hl hnz

private theorem top_step_iter_wp (Γ : Env)
    (hScan : Γ.Has "full_bva_scan_cands" step13BvaScanCandsSpec)
    (hPick : Γ.Has "full_bva_pick_cand" step13BvaPickCandSpec)
    (hFilter : Γ.Has "full_bva_filter_row" fidBvaFilterRowSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {f0_bv : BitVec 32}
    {init_cv init_lits lim_bv : BitVec 64} {sc bump : Nat}
    {bump_bv step cur_qn best_k : BitVec 32} {best_red : BitVec 64} {stl : FullState}
    {ml : Mem 64} {Jex Js : Tup Cont [[i32, i32, i32, i32, i64]]}
    (hsc_eq : sc = fidStepsCap c.scratch_cap) (hsc_pos : 0 < sc) (hsc_le : sc ≤ 256)
    (hf0_lt : f0_bv.toNat < 2 * s.core.cur_vars) (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hbump_bv : bump_bv.toNat = bump) (hlay : Step7BvaLayout c stl step.toNat)
    (hinv : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump stl ml)
    (hJex : ∀ bump' step' cur_qn' best_k' best_red' st_e m_e, Step7BvaLayout c st_e step'.toNat →
      StepExitBody c F0 F_cur s R sc step' best_k' bump' st_e m_e →
      Jex.fst (BitVec.ofNat 32 bump', step', cur_qn', best_k', best_red', ()) m_e)
    (hJs : ∀ bump' step' cur_qn' best_k' best_red' st_n m_n, Step7BvaLayout c st_n step'.toNat →
      StepInvBody c F0 F_cur s R sc step' cur_qn' best_k' bump' st_n m_n →
      step.toNat < sc → step'.toNat > step.toNat →
      Js.fst (BitVec.ofNat 32 bump', step', cur_qn', best_k', best_red', ()) m_n) :
    wp Γ Q X ((fidTryLitStepBlock Val Cont (BitVec.ofNat 32 sc, ()) (c.hdr, f0_bv, init_cv, ())
        c.pScratchBuf (init_lits, ()) Jex (BitVec.ofNat 64 c.scratch_cap) c.pLitMark lim_bv
        Js).get Member.here (bump_bv, step, cur_qn, best_k, best_red, ())) ml := by
  have hmx := c.hmaxv; have har_b := c.harena; have hsc_c := c.hscr
  unfold dimacsBound at hmx har_b hsc_c
  have ⟨hm_l, hlen_l, hw_l, hnodup_l, hext_l, hcl0_l, hdm_l, hcv_l, hfu_l, har_l, hal_l,
    hmrk_l, htm_l, htr_l, hstep1, hstep_sc, h4sc_b, hbump_cap, hqn_l, hmat_l, hbk_l, hlm_hi,
    hlm_set, hlm_only⟩ := hinv
  have hsb_len := hlen_l.scratch_ok.scratch_buf_len
  have heq_b : BitVec.ofNat 32 bump = bump_bv :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hbump_bv])
  dsimp only [fidTryLitStepBlock, Blocks.get]
  c0_hfast
  · rename_i hstep_bv hcqn2
    have hstep_lt : step.toNat < sc := by rwa [Nat.mod_eq_of_lt (by omega)] at hstep_bv
    have hro_idx : (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step - 1)).toNat <
        stl.scratch.scratch_buf.length := by
      rw [hsb_len, show (1 : BitVec 32) = 1#32 from rfl,
        top_bv64_sc_add_step_sub1 hsc_le hstep1 hstep_sc]; omega
    c0_hfast
    obtain ⟨hro_qn_cap, hscan_rows⟩ := top_step_scan_ok hinv hsc_eq
    have hro_nat : ∀ h, (stl.scratch.scratch_buf[(BitVec.setWidth 64
        (BitVec.ofNat 32 sc + step - 1)).toNat]'h).toNat =
        (stl.scratch.scratch_buf[sc + (step.toNat - 1)]?.getD 0#32).toNat := fun h => by
      rw [List.getElem?_eq_getElem (by rw [hsb_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (top_getElem_eq_of_eq rfl
        (by rw [show (1 : BitVec 32) = 1#32 from rfl]
            exact top_bv64_sc_add_step_sub1 hsc_le hstep1 hstep_sc) h _)
    apply wp_call_of_spec; apply hScan _ _ _ X
    dsimp only [step13BvaScanCandsSpec, vals_nil, vals_cons, Arg.val_var]
    refine ⟨c, F0, F_cur, stl, R, rfl, hlen_l, hw_l, hnodup_l, hext_l, hcl0_l, hdm_l,
      (by omega), hlm_hi, (by rw [hro_nat _]; exact hro_qn_cap),
      (by simpa only [hro_nat] using hscan_rows), hm_l,
      fun ncntd wsort1 ws1_1 ws2_1 ant1 m1 hlen1 hnc1 hws1_ok hm1 => ?_⟩
    let st1 : FullState := { stl with scratch := { stl.scratch with
      ant_sz := ant1, wsort := wsort1, work_stk1 := ws1_1, work_stk2 := ws2_1 } }
    have hst1_den : FullDenseInvNoLm c F0 F_cur st1 :=
      ⟨hlen1, hw_l, hnodup_l, FullExtScratchOk.of_pres hext_l ⟨rfl, rfl⟩ fun _ hr => hr,
       hcl0_l, hdm_l⟩
    apply wp_call_of_spec; apply hPick _ _ _ X
    dsimp only [step13BvaPickCandSpec, vals_nil, vals_cons, Arg.val_var]
    refine ⟨c, F0, F_cur, st1, R, rfl, hst1_den, (by dsimp only [st1]; omega), hnc1,
      (fun i hi => (hws1_ok i hi).2), hm1,
      fun best_lit repr2 mclr2 tc2 tl2 wsort2 ant2 sig2 shrk2 m2 hden2 hbl_dom hm2 => ?_⟩
    let st2 : FullState := { st1 with
      core := { st1.core with tmp_cnt := tc2, tmp_len := tl2, min_clr := mclr2, repr := repr2 }
      scratch := { st1.scratch with
        ant_sz := ant2, wsort := wsort2, shrink_stk := shrk2, sim_sig := sig2 } }
    have hst2_l : st2.core.cur_vars = stl.core.cur_vars ∧ st2.core.fuel = stl.core.fuel ∧
        st2.core.arena = stl.core.arena ∧ st2.core.arena_len = stl.core.arena_len ∧
        st2.core.lit_mark = stl.core.lit_mark ∧ st2.core.mrk = stl.core.mrk ∧
        st2.scratch.tarjan_mark = stl.scratch.tarjan_mark ∧
        st2.scratch.tarjan_reach = stl.scratch.tarjan_reach ∧
        st2.scratch.scratch_buf = stl.scratch.scratch_buf :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hinv2 : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump st2 m2 :=
      ⟨hm2, hden2.1, hden2.2.1, hden2.2.2.1, hden2.2.2.2.1, hden2.2.2.2.2.1, hden2.2.2.2.2.2,
       hcv_l, hfu_l, har_l, hal_l, hmrk_l, htm_l, htr_l, hstep1, hstep_sc, h4sc_b, hbump_cap,
       hqn_l, fidBvaMatrixInv_congr rfl rfl rfl rfl hmat_l, hbk_l, hlm_hi, hlm_set, hlm_only⟩
    have hlay2 : Step7BvaLayout c st2 step.toNat := Step7BvaLayout.congr rfl hlay
    c0_hfast_nogrp
    · rw [← heq_b]
      exact hJex bump step cur_qn best_k best_red st2 m2 hlay2 (stepExitBody_of_inv hinv2)
    · rw [← heq_b]
      exact hJex bump step cur_qn best_k best_red st2 m2 hlay2 (stepExitBody_of_inv hinv2)
    · have hbl_ne : best_lit ≠ 0xFFFFFFFF#32 := by assumption
      have hbl_lt : best_lit.toNat < 2 * st2.core.cur_vars :=
        hbl_dom.elim (fun h => absurd h hbl_ne) id
      let max_new0 := ((BitVec.ofNat 64 c.scratch_cap - bump_bv.setWidth 64).setWidth 32) >>>
        (1 : Nat)
      have hmn0 : max_new0.toNat = (c.scratch_cap - bump) / 2 := by
        dsimp only [max_new0]
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one,
          BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          hbump_bv, Nat.mod_eq_of_lt (by omega : bump < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
          show (2 ^ 64 - bump + c.scratch_cap) % 2 ^ 64 = c.scratch_cap - bump by omega,
          Nat.mod_eq_of_lt (by omega : c.scratch_cap - bump < 2 ^ 32)]
      refine wp_join_group (ts := [i32]) (fun mn_v m_j =>
          m_j = m2 ∧ mn_v.fst.toNat = min ((c.scratch_cap - bump) / 2) cur_qn.toNat) ?_ ?_
      · intro _ ⟨mn_bv, _⟩ m_j ⟨hm_eq, hmn_nat⟩; dsimp only at hmn_nat; subst m_j
        c0_hfast
        · rw [← heq_b]
          exact hJex bump step cur_qn best_k best_red st2 m2 hlay2 (stepExitBody_of_inv hinv2)
        · have hmn2 : 2 ≤ mn_bv.toNat := by c0_bound
          have hmn_cap : bump + 2 * mn_bv.toNat ≤ c.scratch_cap := by omega
          have hpar_nat : (bump_bv + mn_bv).toNat = bump + mn_bv.toNat := by c0_bound
          have hpar_cap : (bump_bv + mn_bv).toNat + mn_bv.toNat ≤ c.scratch_cap := by omega
          have hmn_diff : (bump_bv + mn_bv).toNat - bump_bv.toNat = mn_bv.toNat := by omega
          have hmat2 : FidBvaMatrixInv c F_cur st2 step.toNat bump :=
            fidBvaMatrixInv_congr rfl rfl rfl rfl hmat_l
          apply wp_call_of_spec; apply hFilter _ _ _ X
          dsimp only [fidBvaFilterRowSpec, vals_nil, vals_cons, Arg.val_var]
          refine ⟨c, F0, F_cur, st2, R, step.toNat, bump, rfl, hden2.1, hden2.2.1, hden2.2.2.1,
            hden2.2.2.2.1, hden2.2.2.2.2.1, hden2.2.2.2.2.2, hsc_eq ▸ hsc_pos, hstep1,
            hsc_eq ▸ hstep_lt, (by dsimp only [st2, st1]; rw [hro_nat _, hsc_eq]),
            (by rw [← hsc_eq]; exact hqn_l), hbump_bv, (by omega), (by rw [hpar_nat]; omega),
            hbl_lt, hmat2, hlm_hi, hlm_set, hm2,
            fun new_qn sb3 ant3 m3 hlen3 hnqn_le hkeep3 hrows3 hm3 => ?_⟩
          rw [hmn_diff] at hnqn_le hkeep3; simp only [hro_nat] at hrows3
          let st3 : FullState := { st2 with scratch := { st2.scratch with
            scratch_buf := sb3, ant_sz := ant3 } }
          have hsb3_len := hlen3.scratch_ok.scratch_buf_len
          c0_hfast
          · have hnqn_lt2 : new_qn.toNat < 2 := by assumption
            have hmat3 : FidBvaMatrixInv c F_cur st3 step.toNat bump :=
              fidBvaMatrixInv_congr (s' := st3) rfl rfl rfl rfl
                (top_matrixInv_of_filter_pres (max_new := mn_bv.toNat) (nrow_off := bump_bv)
                  (par_off := bump_bv + mn_bv) hmat2 hbump_bv (by omega) hkeep3)
            have hlm_set3 : ∀ r < step.toNat,
                st3.core.lit_mark[(st3.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD
                  0#8 &&& 1#8 ≠ 0#8 := fun r hr => by
              dsimp only [st3]; rw [hkeep3 r (by omega) (by omega) (by omega)]; exact hlm_set r hr
            have hlm_only3 : ∀ l < 2 * c.max_vars, st3.core.lit_mark[l]?.getD 0#8 &&& 1#8 ≠ 0#8 →
                ∃ r < step.toNat, (st3.scratch.scratch_buf[r]?.getD 0#32).toNat = l :=
              fun l hl hnz => by
                obtain ⟨r, hr, heq⟩ := hlm_only l hl hnz
                refine ⟨r, hr, ?_⟩
                dsimp only [st3]; rwa [hkeep3 r (by omega) (by omega) (by omega)]
            have hlay3 : Step7BvaLayout c st3 step.toNat :=
              top_layout_of_pre (hsc_eq ▸ Nat.le_of_lt hstep_lt) (hsc_eq ▸ h4sc_b)
                (fun idx hi => hkeep3 idx (by omega) (by omega) (by omega)) hlay2
            rw [← heq_b]
            exact hJex bump step new_qn best_k best_red st3 m3 hlay3
              (stepExitBody_of_inv ⟨hm3, hlen3, hden2.2.1, hden2.2.2.1,
                FullExtScratchOk.of_pres hden2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
                hden2.2.2.2.2.1, hden2.2.2.2.2.2, hcv_l, hfu_l, har_l, hal_l, hmrk_l, htm_l, htr_l,
                hstep1, hstep_sc, h4sc_b, hbump_cap, rfl, hmat3, hbk_l, hlm_hi, hlm_set3,
                hlm_only3⟩)
          · have hnqn2 : 2 ≤ new_qn.toNat := by c0_bound
            have hcv2_le := hden2.1.core_ok.cur_vars_le
            have hs3_0 : (BitVec.setWidth 64 step).toNat < st3.scratch.scratch_buf.length := by
              rw [hsb3_len]; c0_bound
            have hs3_1 : (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step)).toNat <
                (st3.scratch.scratch_buf.set (BitVec.setWidth 64 step).toNat best_lit).length := by
              rw [List.length_set, hsb3_len]; c0_bound
            have hs3_2 : (BitVec.setWidth 64 (2#32 * BitVec.ofNat 32 sc + step)).toNat <
                ((st3.scratch.scratch_buf.set (BitVec.setWidth 64 step).toNat best_lit).set
                  (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step)).toNat bump_bv).length := by
              rw [List.length_set, List.length_set, hsb3_len]; c0_bound
            have hs3_3 : (BitVec.setWidth 64 (3#32 * BitVec.ofNat 32 sc + step)).toNat <
                (((st3.scratch.scratch_buf.set (BitVec.setWidth 64 step).toNat best_lit).set
                  (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step)).toNat bump_bv).set
                  (BitVec.setWidth 64 (2#32 * BitVec.ofNat 32 sc + step)).toNat new_qn).length := by
              rw [List.length_set, List.length_set, List.length_set, hsb3_len]; c0_bound
            have hlm_b : (BitVec.setWidth 64 best_lit).toNat < st3.core.lit_mark.length := by
              dsimp only [st3]; rw [hden2.1.core_ok.lit_mark_len]; c0_bound
            c0_hfast_nogrp
            have hi0 : (BitVec.setWidth 64 step).toNat = step.toNat := fid_bv64_32 step
            have hi1 : (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step)).toNat =
                sc + step.toNat := by
              rw [fid_bv64_32, BitVec.toNat_add, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : sc < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
            have hi2 : (BitVec.setWidth 64 (2#32 * BitVec.ofNat 32 sc + step)).toNat =
                2 * sc + step.toNat := by
              rw [fid_bv64_32, BitVec.toNat_add, BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2
                from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sc < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : 2 * sc < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
            have hi3 : (BitVec.setWidth 64 (3#32 * BitVec.ofNat 32 sc + step)).toNat =
                3 * sc + step.toNat := by
              rw [fid_bv64_32, BitVec.toNat_add, BitVec.toNat_mul, show (3#32 : BitVec 32).toNat = 3
                from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sc < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : 3 * sc < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
            have heq_sb : (((st3.scratch.scratch_buf.set
                  (BitVec.setWidth 64 step).toNat best_lit).set
                  (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step)).toNat bump_bv).set
                  (BitVec.setWidth 64 (2#32 * BitVec.ofNat 32 sc + step)).toNat new_qn).set
                  (BitVec.setWidth 64 (3#32 * BitVec.ofNat 32 sc + step)).toNat
                  (bump_bv + mn_bv) =
                (((st3.scratch.scratch_buf.set step.toNat best_lit).set
                  (sc + step.toNat) bump_bv).set (2 * sc + step.toNat) new_qn).set
                  (3 * sc + step.toNat) (bump_bv + mn_bv) := by rw [hi0, hi1, hi2, hi3]
            have heq_lm : st3.core.lit_mark.set (BitVec.setWidth 64 best_lit).toNat
                  (BitVec.setWidth 8 1#32) = st3.core.lit_mark.set best_lit.toNat 1#8 := by
              rw [fid_bv64_32 best_lit, show BitVec.setWidth 8 1#32 = 1#8 from rfl]
            let sb4 := (((st3.scratch.scratch_buf.set step.toNat best_lit).set
              (sc + step.toNat) bump_bv).set (2 * sc + step.toNat) new_qn).set
              (3 * sc + step.toNat) (bump_bv + mn_bv)
            let st4 : FullState := { st3 with
              core := { st3.core with lit_mark := st3.core.lit_mark.set best_lit.toNat 1#8 },
              scratch := { st3.scratch with scratch_buf := sb4 } }
            have hm4 : (FullMem c st4 ⋆ R) m := by
              dsimp only [st4, sb4]; rw [← heq_sb, ← heq_lm]; exact hm
            refine wp_join_group (ts := [i32, i64]) (fun bk_tup mk =>
                mk = m ∧ (bk_tup.fst = best_k ∨ bk_tup.fst = step)) ?_ ?_
            · intro _ ⟨bk', br', _⟩ mk ⟨hm_eq, hbk'⟩; dsimp only at hbk'; subst mk; c0_hfast
              have hstep_gt : (step + 1#32).toNat > step.toNat := by
                rw [fid_bv32_add1 (by omega)]; omega
              have hbump'_eq : (bump_bv + mn_bv).toNat + new_qn.toNat =
                  ((bump_bv + mn_bv) + new_qn).toNat := by
                rw [BitVec.toNat_add (bump_bv + mn_bv) new_qn, hpar_nat,
                  Nat.mod_eq_of_lt (by omega)]
              have hinv4 := top_step_upd_ok (st2 := st2) (max_new := mn_bv.toNat) hinv hsc_eq
                hsc_pos hsc_le hstep_lt ⟨rfl, rfl, rfl, rfl⟩ hden2 hst2_l hbl_lt rfl hsb3_len
                hbump_bv hpar_nat hpar_cap (by omega) hnqn2 hkeep3 hrows3 hbk' hm4
              have heq_bv' : BitVec.ofNat 32 ((bump_bv + mn_bv).toNat + new_qn.toNat) =
                  bump_bv + mn_bv + new_qn := BitVec.eq_of_toNat_eq
                (by rw [hbump'_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
              have hlay4 : Step7BvaLayout c st4 (step + 1#32).toNat := by
                rw [fid_bv32_add1 (by omega)]
                exact top_layout_extend (best_lit := best_lit) hstep1 (hsc_eq ▸ hstep_lt) hmat_l
                  hlay hsb3_len hbump_bv hpar_nat hnqn_le (by rw [← hsc_eq, ← hqn_l]; omega)
                  (hsc_eq ▸ h4sc_b) (fun idx hi => hkeep3 idx (by omega) (by omega) (by omega))
                  (by dsimp only [st4, sb4]; rw [← hsc_eq])
              rw [← heq_bv']
              exact hJs ((bump_bv + mn_bv).toNat + new_qn.toNat) (step + 1#32) new_qn
                bk' br' st4 m hlay4 hinv4 hstep_lt hstep_gt
            · intro Js2 hJs2; c0_hfast
              all_goals first
                | (have hbk_step : (step + 1 - 1 : BitVec 32) = step := BitVec.eq_of_toNat_eq (by
                    rw [BitVec.toNat_sub, BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl]
                    omega)
                   rw [hbk_step]; exact hJs2 (step, _, ()) m ⟨rfl, Or.inr rfl⟩)
                | exact hJs2 (best_k, best_red, ()) m ⟨rfl, Or.inl rfl⟩
      · intro _ hJmn; c0_hfast
        · rw [hbump_bv, show (2 ^ 64 - bump + c.scratch_cap) % 2 ^ 64 = c.scratch_cap - bump
            by omega, Nat.mod_eq_of_lt (by omega)] at hc
          exact hJmn (cur_qn, ()) m2 ⟨rfl, by dsimp only; rw [Nat.min_eq_right (by omega)]⟩
        · rw [hbump_bv, show (2 ^ 64 - bump + c.scratch_cap) % 2 ^ 64 = c.scratch_cap - bump
            by omega, Nat.mod_eq_of_lt (by omega)] at hc
          exact hJmn (max_new0, ()) m2 ⟨rfl, by dsimp only; rw [hmn0, Nat.min_eq_left (by omega)]⟩
  all_goals exact
    heq_b ▸ hJex bump step cur_qn best_k best_red stl ml hlay (stepExitBody_of_inv hinv)

private theorem top_step_loop_wp (Γ : Env)
    (hScan : Γ.Has "full_bva_scan_cands" step13BvaScanCandsSpec)
    (hPick : Γ.Has "full_bva_pick_cand" step13BvaPickCandSpec)
    (hFilter : Γ.Has "full_bva_filter_row" fidBvaFilterRowSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {f0_bv : BitVec 32}
    {init_cv init_lits lim_bv : BitVec 64} {sc : Nat} {m0 : Mem 64}
    {Jex : Tup Cont [[i32, i32, i32, i32, i64]]}
    {entry : Tup Cont [[i32, i32, i32, i32, i64]] → Expr Val Cont [.bool]}
    (hsc_eq : sc = fidStepsCap c.scratch_cap) (hsc_pos : 0 < sc) (hsc_le : sc ≤ 256)
    (hf0_lt : f0_bv.toNat < 2 * s.core.cur_vars) (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hentry : ∀ J : Cont [i32, i32, i32, i32, i64],
      (∀ (bump_bv stp cqn bk : BitVec 32) (bred : BitVec 64) (m_lp : Mem 64),
        (∃ bp st_lp, bump_bv.toNat = bp ∧ Step7BvaLayout c st_lp stp.toNat ∧
          StepInvBody c F0 F_cur s R sc stp cqn bk bp st_lp m_lp) →
        J (bump_bv, stp, cqn, bk, bred, ()) m_lp) → wp Γ Q X (entry (J, ())) m0)
    (hJex : ∀ bump' step' cur_qn' best_k' best_red' st_e m_e, Step7BvaLayout c st_e step'.toNat →
      StepExitBody c F0 F_cur s R sc step' best_k' bump' st_e m_e →
      Jex.fst (BitVec.ofNat 32 bump', step', cur_qn', best_k', best_red', ()) m_e) :
    wp Γ Q X (Expr.group (fidTryLitStepBlock Val Cont (BitVec.ofNat 32 sc, ())
        (c.hdr, f0_bv, init_cv, ()) c.pScratchBuf (init_lits, ()) Jex
        (BitVec.ofNat 64 c.scratch_cap) c.pLitMark lim_bv) entry) m0 := by
  have hsc_c := c.hscr; unfold dimacsBound at hsc_c
  refine wp_loop_inv (fun (bump_bv, stp, cqn, bk, bred, _) m_lp => ∃ bp st_lp,
      bump_bv.toNat = bp ∧ Step7BvaLayout c st_lp stp.toNat ∧
      StepInvBody c F0 F_cur s R sc stp cqn bk bp st_lp m_lp)
    (fun (_, stp, _) _ => sc - stp.toNat)
    (fun J hJ => hentry J (fun _ _ _ _ _ m_lp h => hJ _ m_lp h))
    (fun _ (_, stp, cqn, bk, bred, _) m_lp ⟨bp, st_lp, hbp_bv, hlay_lp, hinv_lp⟩ ih =>
      top_step_iter_wp Γ hScan hPick hFilter hsc_eq hsc_pos hsc_le hf0_lt hil_le hbp_bv
        hlay_lp hinv_lp hJex fun bp' stp' cqn' bk' bred' st_n m_n hlay_n hinv_n hlt_sc hgt =>
        ih (BitVec.ofNat 32 bp', stp', cqn', bk', bred', ()) m_n (by dsimp only; omega)
          ⟨bp', st_n, by
            have hbp_lt := hinv_n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)], hlay_n, hinv_n⟩)

public section

@[expose] def step0RowOk (F_cur : List (List Nat)) (s : FullState) (f0 : Nat)
    (sb : List (BitVec 32)) (sc r0n : Nat) : Prop :=
  ∀ j < r0n, ∃ res, (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
    FidBvaRowEntryOk F_cur s f0 (sb[4 * sc + j]?.getD 0#32) res ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause (f0 :: res))

theorem step0_post_exit_wp (Γ : Env)
    (hScan : Γ.Has "full_bva_scan_cands" step13BvaScanCandsSpec)
    (hPick : Γ.Has "full_bva_pick_cand" step13BvaPickCandSpec)
    (hFilter : Γ.Has "full_bva_filter_row" fidBvaFilterRowSpec)
    (hCommit : Γ.Has "full_bva_commit" step7BvaCommitSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {f0 r0n : BitVec 32}
    {init_cv init_lits lim_bv : BitVec 64} {sb : List (BitVec 32)} {asz_cur : BitVec 64}
    {m_cur : Mem 64} (hlen : FullState.LengthsOk c s) (hwit : FullWitnessInv c F0 F_cur s.core)
    (hlm : FullLitMarksClear c s) (hnodup : FullArenaVarsNodup s)
    (hext : FullExtScratchOk c s) (hlev : s.core.cur_level = 0) (hdm : s.core.dense_mode ≠ 0#64)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hsb_l : sb.length = c.scratch_cap) (hsc_pos : 0 < fidStepsCap c.scratch_cap)
    (hsc_le : fidStepsCap c.scratch_cap ≤ 256)
    (h4sc : 4 * fidStepsCap c.scratch_cap + r0n.toNat ≤ c.scratch_cap) (hr0n_ge2 : 2 ≤ r0n.toNat)
    (hrows : step0RowOk F_cur s f0.toNat sb (fidStepsCap c.scratch_cap) r0n.toNat)
    (hm_cur : (FullMem c
      { core := { s.core with lit_mark := s.core.lit_mark.set f0.toNat 1#8 }
        scratch := { s.scratch with
          scratch_buf := (((sb.set 0 f0).set (fidStepsCap c.scratch_cap)
            (BitVec.ofNat 32 (4 * fidStepsCap c.scratch_cap))).set
            (2 * fidStepsCap c.scratch_cap) r0n).set
            (3 * fidStepsCap c.scratch_cap) (BitVec.ofNat 32 (4 * fidStepsCap c.scratch_cap))
          ant_sz := asz_cur } } ⋆ R) m_cur)
    (hpost : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → ∃ bk, Step7BvaCommittedOk c s' bk) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    let sc := fidStepsCap c.scratch_cap
    wp Γ Q X (Expr.group
      (step7TryLitExitBlock Val Cont c.pScratchBuf c.pLitMark (c.hdr, f0, init_cv, ()))
      (fun Jex => Expr.group (fidTryLitStepBlock Val Cont (BitVec.ofNat 32 sc, ())
          (c.hdr, f0, init_cv, ()) c.pScratchBuf (init_lits, ()) Jex
          (BitVec.ofNat 64 c.scratch_cap) c.pLitMark lim_bv)
        (fun Js => Expr.jump Js.fst (Arg.var (BitVec.ofNat 32 (4 * sc) + r0n),
          Arg.imm 1, Arg.var r0n, Arg.imm 0, Arg.imm 0, ())))) m_cur := by
  intro sc; have hmx := c.hmaxv; have hsc_c := c.hscr; unfold dimacsBound at hmx hsc_c
  have hcl := hlen.core_ok; have hsc := hlen.scratch_ok; have hcv_le := hcl.cur_vars_le
  let hdr_sz := BitVec.ofNat 32 (4 * sc)
  let sb1 := (((sb.set 0 f0).set sc hdr_sz).set (2 * sc) r0n).set (3 * sc) hdr_sz
  let lm1 := s.core.lit_mark.set f0.toNat 1#8
  let st1 : FullState :=
    { core := { s.core with lit_mark := lm1 },
      scratch := { s.scratch with scratch_buf := sb1, ant_sz := asz_cur } }
  have hlen1 : FullState.LengthsOk c st1 :=
    ⟨{ hcl with lit_mark_len := by simp only [st1, lm1, List.length_set, hcl.lit_mark_len] },
     { hsc with scratch_buf_len := by simp only [st1, sb1, List.length_set, hsb_l] }⟩
  have hwit1 : FullWitnessInv c F0 F_cur st1.core := fullWitnessInv_with_litMark hwit lm1
  have hmat0 := top_matrixInv_step1 (c := c) (F_cur := F_cur) (s := s) (sb := sb)
    (f0 := f0) (r0n := r0n) (sc := sc) rfl hsc_pos hsc_le hsb_l hf0_lt hr0n_ge2 h4sc hrows
  have hmat1 : FidBvaMatrixInv c F_cur st1 (1#32).toNat (4 * sc + r0n.toNat) := by
    simpa only [show (1#32).toNat = 1 from rfl] using
      fidBvaMatrixInv_congr (s' := st1) rfl rfl rfl rfl hmat0
  have hlm_init := top_lm1_init (maxv := c.max_vars) (cap := c.scratch_cap)
    (sc := sc) (sb := sb) (lm := s.core.lit_mark) (f0 := f0) (qn := r0n) (hdr_sz := hdr_sz)
    hsc_pos (by omega) hsb_l hcl.lit_mark_len (by omega) hlm.2
  have hinv1 : StepInvBody c F0 F_cur s R sc 1#32 r0n 0#32 (4 * sc + r0n.toNat) st1 m_cur := by
    refine ⟨hm_cur, hlen1, hwit1, hnodup, hext, hlev, hdm, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by decide, Nat.succ_le_of_lt hsc_pos, by omega, h4sc, ?_, hmat1, Or.inl rfl,
      hlm_init.1, ?_, ?_⟩
    · have hbd2 : 2 * sc < sb1.length := by simp [sb1, hsb_l]; omega
      have hr0_eq : sb1[2 * sc]?.getD 0#32 = r0n := by
        simp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by
          simp only [List.length_set]; omega), Option.getD_some]
      simpa only [st1, show (1#32).toNat = 1 from rfl, show 2 * sc + (1 - 1) = 2 * sc from by omega,
        List.getElem?_eq_getElem hbd2, Option.getD_some] using (congrArg BitVec.toNat hr0_eq).symm
    · intro r hr; have hr0 : r = 0 := by have : (1#32).toNat = 1 := rfl; omega
      subst hr0; simpa [st1] using hlm_init.2.1 0 (by decide)
    · intro l hl hget; obtain ⟨r, hr, hget'⟩ := hlm_init.2.2 l hl (by simpa [st1] using hget)
      exact ⟨r, by have : (1#32).toNat = 1 := rfl; omega, by simpa [st1] using hget'⟩
  refine wp_join_group (fun (bp_bv, stp_bv, cqn_bv, bk_bv, br_bv, _) ml_e =>
      ∃ bp' st_e, bp_bv = BitVec.ofNat 32 bp' ∧ Step7BvaLayout c st_e stp_bv.toNat ∧
        StepExitBody c F0 F_cur s R sc stp_bv bk_bv bp' st_e ml_e) ?_ ?_
  · intro _ ⟨bp_bv, stp_bv, cqn_bv, bk_bv, br_bv, _⟩ ml_e ⟨bp', st_e, hbp, hlay, hex⟩; subst hbp
    have hbp_le : bp' ≤ c.scratch_cap := by
      rcases hex with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbp_le, _⟩; exact hbp_le
    have hex' : StepExitBody c F0 F_cur s R (fidStepsCap c.scratch_cap)
        stp_bv bk_bv (BitVec.ofNat 32 bp').toNat st_e ml_e := by
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact top_exit_phase_wp Γ hCommit hcv_le hlm hlay hex' hpost
  · intro Jex hJex
    refine top_step_loop_wp Γ hScan hPick hFilter rfl hsc_pos hsc_le hf0_lt hil_le ?_
      (fun bump' step' cur_qn' best_k' best_red' st_e m_e hlay hex =>
        hJex _ m_e ⟨bump', st_e, rfl, hlay, hex⟩)
    intro Js hJs; c0_hsteps_nogrp; apply hJs
    refine ⟨4 * sc + r0n.toNat, st1, ?_, top_layout_one, hinv1⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 4 * sc < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega)]

theorem top_rowEntryOk_of_large_f0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cr f0 : BitVec 32} (href : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hsz3 : 3 ≤ fullArenaClauseSizeCore s.core cr.toNat)
    (hsz5 : fullArenaClauseSizeCore s.core cr.toNat ≤ 5)
    (hf0_mem : f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat) :
    ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s f0.toNat cr res ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)) := by
  let C := fullArenaClauseLitsCore s.core cr.toNat
  let res := C.filter (· != f0.toNat)
  have hC_lt := hinv.2.1.arena.lits_lt cr.toNat href hng
  have hC_nd_vars : (C.map (· / 2)).Nodup := hinv.2.2.2.1 cr.toNat href hng
  have hC_nd : C.Nodup := nodup_of_map_div2 hC_nd_vars
  have hC_ent := hinv.2.1.arena.entails cr.toNat href hng
  have hres_sub : res.Sublist C := List.filter_sublist
  have hperm_er : res.Perm (C.erase f0.toNat) := by
    have hp := (List.perm_cons_erase hf0_mem).filter (· != f0.toNat)
    have he : (f0.toNat :: C.erase f0.toNat).filter (· != f0.toNat) = C.erase f0.toNat := by
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun y hy => by
        have hne : y ≠ f0.toNat := fun h => by
          subst h; exact (List.nodup_cons.mp (hC_nd.perm (List.perm_cons_erase hf0_mem))).1 hy
        simp [hne]
    rwa [he] at hp
  have hC_perm : C.Perm (f0.toNat :: res) :=
    (List.perm_cons_erase hf0_mem).trans (hperm_er.symm.cons f0.toNat)
  have hwf := hinv.2.1.arena.refs_wf cr.toNat href
  have hal := hinv.1.core_ok.arena_len_le
  have hab := c.harena; unfold dimacsBound at hab
  have hcr_not_bin : (cr &&& 0x80000000#32) = 0#32 :=
    fid_bv32_bin_flag_zero_of_lt (by omega)
  refine ⟨res, fun x hx => hC_lt x (hres_sub.subset hx), hC_nd_vars.sublist (hres_sub.map _), ?_,
    clause_entails_of_perm hC_perm hC_ent⟩
  unfold FidBvaRowEntryOk; rw [ite_eq_right (fun h => h hcr_not_bin)]
  exact ⟨href, hng, hsz3, hsz5, hf0_mem, List.Perm.refl _, hC_perm⟩

theorem fid_sc_pos_of_ne_zero {cap : Nat} (h : BitVec.ofNat 32 (fidStepsCap cap) ≠ 0#32) :
    0 < fidStepsCap cap := by
  have := fidStepsCap_le_256 cap; apply Classical.byContradiction; intro h0
  have hz : fidStepsCap cap = 0 := by omega
  rw [hz] at h; contradiction

theorem fid_wp_call_steps_cap (Γ : Env)
    (hSteps : Γ.Has "full_bva_steps_cap_fid" fidBvaStepsCapSpec)
    {rs : List Ty} {Q : Post rs} {X : XPost} {x : BitVec 64} {m : Mem 64}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hk : wp Γ Q X (k (BitVec.ofNat 32 (fidStepsCap x.toNat), ())) m) :
    wp Γ Q X (Expr.call (as := [i64]) "full_bva_steps_cap_fid" (Arg.var x, ()) k) m :=
  wp_call_of_spec _ _ (hSteps _ _ _ _ hk)

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
