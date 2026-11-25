/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVA Proofs — Part 2b0 (`full_bva_try_lit` helpers)

Helper lemmas and loop invariants (`public section`, `0` banned tokens, `XPost`-polymorphic)
for `FullFidelityBvaProof2`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics FullBvaFwdTactics

/-! ## 1. Helper Theorems for Dynamic Matrix & BitVec Arithmetic -/

theorem bv64_shl1_lit_toNat (f0 : BitVec 32) :
    (BitVec.setWidth 64 f0 <<< 1#64).toNat = 2 * f0.toNat := by
  simp [BitVec.toNat_shiftLeft]; omega

theorem bv64_shl1_lit_add1_toNat (f0 : BitVec 32) :
    ((BitVec.setWidth 64 f0 <<< 1#64) + 1#64).toNat = 2 * f0.toNat + 1 := by
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft]; omega

theorem fid_bv32_add1_n {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by simp only [bv_c0]; omega

theorem fid_bv64_add1_n {tz : BitVec 64} (h : tz.toNat + 1 < 2 ^ 64) :
    (tz + 1#64).toNat = tz.toNat + 1 := by simp only [bv_c0]; omega

theorem fid_bv64_add2_n {ct : BitVec 32} :
    (BitVec.setWidth 64 ct + 2).toNat = ct.toNat + 2 := by
  change (BitVec.setWidth 64 ct + 2#64).toNat = _; simp only [bv_c0]; omega

theorem fid_bv64_add3_n {ct tj : BitVec 32} :
    (BitVec.setWidth 64 ct + 3 + BitVec.setWidth 64 tj).toNat = ct.toNat + 3 + tj.toNat := by
  change (BitVec.setWidth 64 ct + 3#64 + BitVec.setWidth 64 tj).toNat = _; simp only [bv_c0]; omega

theorem fid_bv64_add2_mod {x : BitVec 32} :
    (x.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = x.toNat + 2 := by
  rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega

theorem fid_bv64_sub_shl2 {cap sc : Nat} (hcap : cap < 2 ^ 64) (hsc : 4 * sc ≤ cap)
    (hsc_le : sc ≤ 256) :
    (BitVec.ofNat 64 cap - BitVec.setWidth 64 (BitVec.ofNat 32 sc <<< (2 : BitVec 32))).toNat =
      cap - 4 * sc := by
  have h1 : (BitVec.ofNat 32 sc <<< (2 : BitVec 32)) = BitVec.ofNat 32 (4 * sc) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  rw [h1]
  have h2 : BitVec.setWidth 64 (BitVec.ofNat 32 (4 * sc)) = BitVec.ofNat 64 (4 * sc) := by
    apply BitVec.eq_of_toNat_eq
    simp only [fid_bv64_32, bv_c0]; omega
  rw [h2]
  have hle : BitVec.ofNat 64 (4 * sc) ≤ BitVec.ofNat 64 cap := by
    rw [BitVec.le_def]; simp only [bv_c0]; omega
  have hsub := BitVec.toNat_sub_of_le hle
  simp only [bv_c0] at hsub ⊢
  omega

theorem fid_bv64_div3 (x : BitVec 64) : (x / (3 : BitVec 64)).toNat = x.toNat / 3 := by
  simp [BitVec.toNat_udiv]

theorem fid_bv32_mul_n {a : BitVec 32} {b : Nat} (ha : a.toNat = b) {k : Nat}
    (hk : k * b < 2 ^ 32) (hk_lt : k < 2 ^ 32) :
    ((BitVec.ofNat 32 k) * a).toNat = k * b := by
  simp only [bv_c0, ha]
  rw [Nat.mod_eq_of_lt hk_lt, Nat.mod_eq_of_lt hk]

theorem fid_bv32_sc_add_step_sub1 {sc : Nat} {step : BitVec 32}
    (hsc : sc ≤ 256) (hst1 : 1 ≤ step.toNat) (hst_sc : step.toNat ≤ sc) :
    (BitVec.ofNat 32 sc + step - 1#32).toNat = sc + (step.toNat - 1) := by
  have hsc_mod : sc % 2 ^ 32 = sc := Nat.mod_eq_of_lt (by omega)
  have hsum_mod : (sc + step.toNat) % 2 ^ 32 = sc + step.toNat := Nat.mod_eq_of_lt (by omega)
  have h1 : (BitVec.ofNat 32 sc + step).toNat = sc + step.toNat := by
    simp only [bv_c0, hsc_mod, hsum_mod]
  have h2 : 1#32 ≤ (BitVec.ofNat 32 sc + step) := by
    rw [BitVec.le_def, h1, show (1#32 : BitVec 32).toNat = 1 from rfl]; omega
  rw [BitVec.toNat_sub_of_le h2, h1]
  change sc + step.toNat - (1#32 : BitVec 32).toNat = _
  rw [show ((1#32 : BitVec 32)).toNat = 1 from rfl]
  omega

theorem fid_bv64_sc_add_step_sub1 {sc : Nat} {step : BitVec 32}
    (hsc : sc ≤ 256) (hst1 : 1 ≤ step.toNat) (hst_sc : step.toNat ≤ sc) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step - 1#32)).toNat = sc + (step.toNat - 1) := by
  rw [fid_bv64_32, fid_bv32_sc_add_step_sub1 hsc hst1 hst_sc]

theorem fid_bv32_ksc_add_step {k sc : Nat} {step : BitVec 32}
    (hk : k ≤ 3) (hsc : sc ≤ 256) (hst_sc : step.toNat ≤ sc) :
    (BitVec.ofNat 32 (k * sc) + step).toNat = k * sc + step.toNat := by
  have h_bound : k * sc ≤ 768 := Nat.le_trans (Nat.mul_le_mul_right sc hk) (by omega)
  have hmod : (k * sc) % 2 ^ 32 = k * sc := Nat.mod_eq_of_lt (by omega)
  have hmod_sum : (k * sc + step.toNat) % 2 ^ 32 = k * sc + step.toNat :=
    Nat.mod_eq_of_lt (by omega)
  simp only [bv_c0, hmod, hmod_sum]

theorem fid_bv32_mul_sc_add_step {k sc : Nat} {step : BitVec 32}
    (hk : k ≤ 3) (hsc : sc ≤ 256) (hst_sc : step.toNat ≤ sc) :
    ((BitVec.ofNat 32 k) * (BitVec.ofNat 32 sc) + step).toNat = k * sc + step.toNat := by
  have h_bound : k * sc ≤ 768 := Nat.le_trans (Nat.mul_le_mul_right sc hk) (by omega)
  have h1 : k % 2 ^ 32 = k := Nat.mod_eq_of_lt (by omega)
  have h2 : sc % 2 ^ 32 = sc := Nat.mod_eq_of_lt (by omega)
  have h3 : (k * sc) % 2 ^ 32 = k * sc := Nat.mod_eq_of_lt (by omega)
  have hm : (BitVec.ofNat 32 k * BitVec.ofNat 32 sc) = BitVec.ofNat 32 (k * sc) := by
    apply BitVec.eq_of_toNat_eq
    simp only [bv_c0, h1, h2, h3]
  rw [hm]
  exact fid_bv32_ksc_add_step hk hsc hst_sc

@[expose] def FidBvaTouchedInv (c : FullCfg) (stc : FullState) (R : Mem 64 → Prop)
    (nt : BitVec 64) (st : FullState) (m : Mem 64) : Prop :=
  st.core = stc.core ∧
  st.scratch.scratch_buf = stc.scratch.scratch_buf ∧
  st.scratch.tarjan_mark = stc.scratch.tarjan_mark ∧
  st.scratch.tarjan_reach = stc.scratch.tarjan_reach ∧
  st.scratch.last_learned = stc.scratch.last_learned ∧
  st.scratch.extend_len = stc.scratch.extend_len ∧
  st.scratch.LengthsOk c ∧
  nt.toNat ≤ 2 * stc.core.cur_vars ∧
  (∀ k < nt.toNat, (st.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * stc.core.cur_vars) ∧
  (FullMem c st ⋆ R) m

theorem fid_bva_touched_push {c : FullCfg} {stc st : FullState} {R : Mem 64 → Prop}
    {nt : BitVec 64} {m : Mem 64} {l : BitVec 32} {idx : Nat}
    (_hcv_le : stc.core.cur_vars ≤ c.max_vars) (_hmx : c.max_vars < 2 * 2 ^ 28)
    (hnt_lt : nt.toNat < 2 * stc.core.cur_vars) (hl_lt : l.toNat < 2 * stc.core.cur_vars)
    (hcore : st.core = stc.core) (hsb : st.scratch.scratch_buf = stc.scratch.scratch_buf)
    (htm : st.scratch.tarjan_mark = stc.scratch.tarjan_mark)
    (htr : st.scratch.tarjan_reach = stc.scratch.tarjan_reach)
    (hll : st.scratch.last_learned = stc.scratch.last_learned)
    (hel : st.scratch.extend_len = stc.scratch.extend_len)
    (hscl : st.scratch.LengthsOk c)
    (hws2_ok : ∀ k < nt.toNat,
      (st.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * stc.core.cur_vars)
    (hm : (FullMem c { st with scratch := { st.scratch with
      wsort := st.scratch.wsort.set idx 1#32,
      work_stk2 := st.scratch.work_stk2.set nt.toNat l } } ⋆ R) m) :
    FidBvaTouchedInv c stc R (nt + 1#64) { st with scratch := { st.scratch with
      wsort := st.scratch.wsort.set idx 1#32,
      work_stk2 := st.scratch.work_stk2.set nt.toNat l } } m := by
  have hws_l := hscl.wsort_len
  have hws2_l := hscl.work_stk2_len
  have hnt1 : (nt + 1#64).toNat = nt.toNat + 1 := by simp only [bv_c0]; omega
  refine ⟨hcore, hsb, htm, htr, hll, hel,
    { hscl with wsort_len := by simp [hws_l], work_stk2_len := by simp [hws2_l] },
    by omega, fun k hk => ?_, hm⟩
  rw [hnt1] at hk
  by_cases hkn : k = nt.toNat
  · subst hkn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hl_lt
  · rw [List.getElem?_set_ne (Ne.symm hkn)]; exact hws2_ok k (by omega)

theorem fid_bva_touched_clear_step {c : FullCfg} {stc stm stz : FullState}
    {R : Mem 64 → Prop} {ntm tz : BitVec 64} {m : Mem 64} {idx : Nat}
    (htz_lt : tz.toNat < ntm.toNat) (htz1 : (tz + 1#64).toNat = tz.toNat + 1)
    (hcorez : stz.core = stc.core) (hsbz : stz.scratch.scratch_buf = stc.scratch.scratch_buf)
    (htmz : stz.scratch.tarjan_mark = stc.scratch.tarjan_mark)
    (htrz : stz.scratch.tarjan_reach = stc.scratch.tarjan_reach)
    (hllz : stz.scratch.last_learned = stc.scratch.last_learned)
    (helz : stz.scratch.extend_len = stc.scratch.extend_len)
    (hws2z : stz.scratch.work_stk2 = stm.scratch.work_stk2)
    (hsclz : stz.scratch.LengthsOk c)
    (hm : (FullMem c { stz with scratch :=
      { stz.scratch with wsort := stz.scratch.wsort.set idx 0#32 } } ⋆ R) m) :
    ∃ stz' : FullState, (tz + 1#64).toNat ≤ ntm.toNat ∧ stz'.core = stc.core ∧
      stz'.scratch.scratch_buf = stc.scratch.scratch_buf ∧
      stz'.scratch.tarjan_mark = stc.scratch.tarjan_mark ∧
      stz'.scratch.tarjan_reach = stc.scratch.tarjan_reach ∧
      stz'.scratch.last_learned = stc.scratch.last_learned ∧
      stz'.scratch.extend_len = stc.scratch.extend_len ∧
      stz'.scratch.work_stk2 = stm.scratch.work_stk2 ∧
      stz'.scratch.LengthsOk c ∧ (FullMem c stz' ⋆ R) m :=
  ⟨{ stz with scratch := { stz.scratch with wsort := stz.scratch.wsort.set idx 0#32 } },
   by rw [htz1]; exact htz_lt, hcorez, hsbz, htmz, htrz, hllz, helz, hws2z,
   { hsclz with wsort_len := by rw [List.length_set, hsclz.wsort_len] }, hm⟩

theorem fid_bva_try_lit_clear_lm_step {sb : List (BitVec 32)} {lmi : List (BitVec 8)}
    {maxv si stepf : Nat} (hsi_lt : si < stepf) (hsi_sb : si < sb.length)
    (hlmi_l : lmi.length = 2 * maxv)
    (hxl_lt : (sb[si]'hsi_sb).toNat < 2 * maxv)
    (hlmi_hi : ∀ l < 2 * maxv, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hlmi_only : ∀ l < 2 * maxv, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r, si ≤ r ∧ r < stepf ∧ (sb[r]?.getD 0#32).toNat = l) :
    let xl := (sb[si]'hsi_sb).toNat
    let lmi' := lmi.set xl ((lmi[xl]'(by omega)) &&& 0xFE#8)
    (∀ l < 2 * maxv, (lmi'[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
    (∀ l < 2 * maxv, (lmi'[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r, si + 1 ≤ r ∧ r < stepf ∧ (sb[r]?.getD 0#32).toNat = l) := by
  intro xl lmi'
  refine ⟨fun l hl => ?_, fun l hl hne => ?_⟩
  · dsimp only [lmi']
    by_cases hlx : l = xl
    · subst hlx; rw [List.getElem?_set_self (by omega), Option.getD_some]
      have h0 := hlmi_hi xl hl
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
      rw [BitVec.and_assoc, show (0xFE#8 &&& 0xFE#8) = 0xFE#8 from by decide]; exact h0
    · rw [List.getElem?_set_ne (Ne.symm hlx)]; exact hlmi_hi l hl
  · dsimp only [lmi'] at hne
    by_cases hlx : l = xl
    · subst hlx; rw [List.getElem?_set_self (by omega), Option.getD_some] at hne
      rw [BitVec.and_assoc, show (0xFE#8 &&& 1#8) = 0#8 from by decide,
        BitVec.and_zero] at hne
      exact absurd rfl hne
    · rw [List.getElem?_set_ne (Ne.symm hlx)] at hne
      obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
      have hne_r : r ≠ si := fun h => by
        subst h; dsimp only [xl] at hlx
        rw [List.getElem?_eq_getElem hsi_sb, Option.getD_some] at heq
        exact hlx heq.symm
      exact ⟨r, by omega, hr2, heq⟩

theorem fid_bva_try_lit_clear_lm_done {c : FullCfg} {stf : FullState}
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
    rw [← BitVec.and_or_distrib_left,
      show (0xFE#8 ||| 1#8) = 0xFF#8 from by decide,
      show ∀ x : BitVec 8, x &&& 0xFF#8 = x from fun x => by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and]
        have := x.isLt; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 8 |>.trans
          (Nat.mod_eq_of_lt this)]
  rw [← hcomb, hhi, hlo]; decide

theorem fid_bva_try_lit_lm1_init {maxv cap sc : Nat} {sb : List (BitVec 32)}
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

theorem fid_bva_try_lit_extend_lm {maxv cap sc step bump max_new : Nat}
    {lm : List (BitVec 8)} {sb2 sb3 : List (BitVec 32)}
    {bl new_qn nrow_off par_off : BitVec 32}
    (hsc_pos : 0 < sc) (hstep_sc : step < sc)
    (hlm_l : lm.length = 2 * maxv) (hsb3_l : sb3.length = cap)
    (hbl_lt : bl.toNat < 2 * maxv)
    (hnrow_eq : nrow_off.toNat = bump) (hpar_eq : par_off.toNat = bump + max_new)
    (h4sc_bump : 4 * sc ≤ bump) (hpar_cap : par_off.toNat + max_new ≤ cap)
    (hpres : ∀ idx < cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb3[idx]? = sb2[idx]?)
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
    apply hpres r (by omega) (by omega) (by omega)
  have hget_step : sb4[step]?.getD 0#32 = bl := by
    dsimp only [sb4]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  refine ⟨fun l hl => ?_, fun r hr => ?_, fun l hl hne => ?_⟩
  · dsimp only [lm4]
    by_cases hlb : l = bl.toNat
    · subst hlb; rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
    · rw [List.getElem?_set_ne (Ne.symm hlb)]; exact hhi l hl
  · dsimp only [lm4]
    by_cases hrs : r < step
    · rw [hget_r r hrs]
      by_cases hlb : (sb2[r]?.getD 0#32).toNat = bl.toNat
      · rw [hlb, List.getElem?_set_self (by omega), Option.getD_some]; decide
      · rw [List.getElem?_set_ne (Ne.symm hlb)]; exact hset r hrs
    · have hr_eq : r = step := by omega
      subst hr_eq; rw [hget_step, List.getElem?_set_self (by omega), Option.getD_some]; decide
  · dsimp only [lm4] at hne ⊢
    by_cases hlb : l = bl.toNat
    · subst hlb; refine ⟨step, by omega, ?_⟩
      rw [hget_step]
    · rw [List.getElem?_set_ne (Ne.symm hlb)] at hne
      obtain ⟨r, hr, heq⟩ := honly l hl hne
      refine ⟨r, by omega, ?_⟩
      rw [hget_r r hr, heq]

theorem fid_bva_matrixInv_substep {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {k step bump : Nat} (hk1 : 1 ≤ k) (hk_le : k ≤ step)
    (h : FidBvaMatrixInv c F_cur s step bump) :
    FidBvaMatrixInv c F_cur s k bump := by
  rcases h with ⟨hsc, hs1, hss, hb1, hb2, hrows⟩
  refine ⟨hsc, hk1, Nat.le_trans hk_le hss, hb1, hb2, fun r hr => ?_⟩
  exact hrows r (Nat.lt_of_lt_of_le hr hk_le)

theorem fidBvaRowEntryOk_of_large_f0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
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
  have hres_nd : (res.map (· / 2)).Nodup := hC_nd_vars.sublist (hres_sub.map _)
  have hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars := fun x hx => hC_lt x (hres_sub.subset hx)
  have hperm_er : res.Perm (C.erase f0.toNat) := by
    have hp := (List.perm_cons_erase hf0_mem).filter (· != f0.toNat)
    have he : (f0.toNat :: C.erase f0.toNat).filter (· != f0.toNat) = C.erase f0.toNat := by
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun y hy => by
        have hne : y ≠ f0.toNat := fun h => by
          subst h
          exact (List.nodup_cons.mp (hC_nd.perm (List.perm_cons_erase hf0_mem))).1 hy
        simp [hne]
    rwa [he] at hp
  have hC_perm : C.Perm (f0.toNat :: res) :=
    (List.perm_cons_erase hf0_mem).trans (hperm_er.symm.cons f0.toNat)
  have hcr_not_bin : (cr &&& 0x80000000#32) = 0#32 := by
    have hwf := hinv.2.1.arena.refs_wf cr.toNat href
    have hal := hinv.1.core_ok.arena_len_le
    have hab := c.harena; unfold dimacsBound at hab
    exact fid_bv32_bin_flag_zero_of_lt (by omega)
  refine ⟨res, hres_lt, hres_nd, ?_, clause_entails_of_perm hC_perm hC_ent⟩
  unfold FidBvaRowEntryOk
  rw [ite_eq_right (fun h => h hcr_not_bin)]
  exact ⟨href, hng, hsz3, hsz5, hf0_mem, List.Perm.refl _, hC_perm⟩

theorem fidBvaMatrixInv_step1 {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb : List (BitVec 32)} {f0 : BitVec 32} {r0n : BitVec 32} {sc : Nat}
    (hsc_eq : sc = fidStepsCap c.scratch_cap)
    (hsc_pos : 0 < sc) (hsc_le : sc ≤ 256)
    (hsb_len : sb.length = c.scratch_cap)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars)
    (hq2 : 2 ≤ r0n.toNat)
    (hr0n_le : 4 * sc + r0n.toNat ≤ c.scratch_cap)
    (hrow0 : ∀ m < r0n.toNat, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s f0.toNat (sb[4 * sc + m]?.getD 0#32) res ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))) :
    let hdr_sz := BitVec.ofNat 32 (4 * sc)
    let bump := 4 * sc + r0n.toNat
    let sb1 := (((sb.set 0 f0).set sc hdr_sz).set (2 * sc) r0n).set (3 * sc) hdr_sz
    FidBvaMatrixInv c F_cur { s with scratch := { s.scratch with scratch_buf := sb1 } } 1 bump := by
  intro hdr_sz bump sb1
  have hsc_cap : 4 * sc ≤ c.scratch_cap := by
    subst hsc_eq; exact fidStepsCap_mul4_le c.scratch_cap
  have hsb1_len : sb1.length = c.scratch_cap := by
    dsimp only [sb1]; simp [hsb_len]
  have hget0 : sb1[0]?.getD 0#32 = f0 := by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have hget_sc : sb1[sc]?.getD 0#32 = hdr_sz := by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
  have hget_2sc : sb1[2 * sc]?.getD 0#32 = r0n := by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set, List.length_set]; omega), Option.getD_some]
  have hget_3sc : sb1[3 * sc]?.getD 0#32 = hdr_sz := by
    dsimp only [sb1]
    rw [List.getElem?_set_self
      (by rw [List.length_set, List.length_set, List.length_set]; omega), Option.getD_some]
  have hhdr_sz_nat : hdr_sz.toNat = 4 * sc := by
    dsimp only [hdr_sz]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 4 * sc < 2 ^ 32)]
  unfold FidBvaMatrixInv
  dsimp only
  rw [← hsc_eq]
  refine ⟨hsc_pos, Nat.le_refl 1, by omega, by omega, hr0n_le, fun r hr => ?_⟩
  have hr0 : r = 0 := by omega
  subst hr0
  rw [Nat.add_zero, Nat.add_zero, Nat.add_zero]
  rw [hget0, hget_sc, hget_2sc, hget_3sc, hhdr_sz_nat]
  refine ⟨hf0_lt, Nat.le_refl (4 * sc), hq2, by omega, fun h0 => by omega, fun m hm => ?_⟩
  have hm_sb : sb1[4 * sc + m]?.getD 0#32 = sb[4 * sc + m]?.getD 0#32 := by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  obtain ⟨res, hres_lt, hres_nd, hok, hent⟩ := hrow0 m hm
  refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun h0 => by omega⟩
  · rw [hm_sb]; exact fidBvaRowEntryOk_congr rfl rfl rfl hok
  · have ht0 : t = 0 := by omega
    subst ht0; rw [hget0]; exact hent

theorem fidBvaMatrixInv_extend_step {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb' : List (BitVec 32)} {step bump max_new sc : Nat}
    {best_lit new_qn nrow_off par_off : BitVec 32}
    (hsc_eq : sc = fidStepsCap c.scratch_cap)
    (hstep1 : 1 ≤ step) (hstep_sc : step < sc)
    (hmat : FidBvaMatrixInv c F_cur s step bump)
    (hsb'_len : sb'.length = c.scratch_cap)
    (hbest_lt : best_lit.toNat < 2 * s.core.cur_vars)
    (hnrow_eq : nrow_off.toNat = bump)
    (hpar_eq : par_off.toNat = bump + max_new)
    (hpar_cap : par_off.toNat + max_new ≤ c.scratch_cap)
    (hnq_le : new_qn.toNat ≤ max_new)
    (hnq2 : 2 ≤ new_qn.toNat)
    (hpres : ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?)
    (hnew : ∀ nm < new_qn.toNat,
      let pi := (sb'[par_off.toNat + nm]?.getD 0#32).toNat
      pi < (s.scratch.scratch_buf[2 * sc + (step - 1)]?.getD 0#32).toNat ∧
      ∃ res : List Nat,
        (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
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
    FidBvaMatrixInv c F_cur { s with scratch := { s.scratch with scratch_buf := sb2 } } (step + 1)
      bump' := by
  intro bump' sb2
  subst hsc_eq
  unfold FidBvaMatrixInv at hmat ⊢
  dsimp only at hmat ⊢
  rcases hmat with ⟨hsc_pos, _, hsc_step, hb1, hb2, hrows⟩
  have h4sc_bump : 4 * fidStepsCap c.scratch_cap ≤ bump' := by dsimp only [bump']; omega
  have hbump'_cap : bump' ≤ c.scratch_cap := by dsimp only [bump']; omega
  have hsb2_len : sb2.length = c.scratch_cap := by dsimp only [sb2]; simp [hsb'_len]
  have hget_lt : ∀ idx < c.scratch_cap, idx ≠ step →
      idx ≠ fidStepsCap c.scratch_cap + step →
      idx ≠ 2 * fidStepsCap c.scratch_cap + step →
      idx ≠ 3 * fidStepsCap c.scratch_cap + step →
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb2[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi h1 h2 h3 h4 h5 h6 => by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (Ne.symm h4), List.getElem?_set_ne (Ne.symm h3),
      List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]
    exact hpres idx hi h5 h6
  have hget_step : sb2[step]?.getD 0#32 = best_lit := by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have hget_sc_step : sb2[fidStepsCap c.scratch_cap + step]?.getD 0#32 = nrow_off := by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
  have hget_2sc_step : sb2[2 * fidStepsCap c.scratch_cap + step]?.getD 0#32 = new_qn := by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set, List.length_set]; omega), Option.getD_some]
  have hget_3sc_step : sb2[3 * fidStepsCap c.scratch_cap + step]?.getD 0#32 = par_off := by
    dsimp only [sb2]
    rw [List.getElem?_set_self
      (by rw [List.length_set, List.length_set, List.length_set]; omega), Option.getD_some]
  have hget_nrow : ∀ nm < new_qn.toNat,
      sb2[nrow_off.toNat + nm]? = sb'[nrow_off.toNat + nm]? := fun nm hnm => by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hget_par : ∀ nm < new_qn.toNat,
      sb2[par_off.toNat + nm]? = sb'[par_off.toNat + nm]? := fun nm hnm => by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  refine ⟨hsc_pos, by omega, by omega, h4sc_bump, hbump'_cap, fun r hr => ?_⟩
  by_cases hre : r < step
  · obtain ⟨hfr, hro1, hq2, hro2, hpo, hm⟩ := hrows r hre
    have hfr_eq : (sb2[r]?.getD 0#32).toNat = (s.scratch.scratch_buf[r]?.getD 0#32).toNat :=
      congrArg (fun o => (o.getD 0#32).toNat)
        (hget_lt r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    have hro_eq : (sb2[fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat =
        (s.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat :=
      congrArg (fun o => (o.getD 0#32).toNat)
        (hget_lt (fidStepsCap c.scratch_cap + r) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega))
    have hqn_eq : (sb2[2 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat =
        (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat :=
      congrArg (fun o => (o.getD 0#32).toNat)
        (hget_lt (2 * fidStepsCap c.scratch_cap + r) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega))
    have hpo_eq : (sb2[3 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat =
        (s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat :=
      congrArg (fun o => (o.getD 0#32).toNat)
        (hget_lt (3 * fidStepsCap c.scratch_cap + r) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega))
    rw [hfr_eq, hro_eq, hqn_eq, hpo_eq]
    refine ⟨hfr, hro1, hq2, by omega, fun hr0 => ?_, fun m hm_lt => ?_⟩
    · obtain ⟨hpo1, hpo2⟩ := hpo hr0
      exact ⟨hpo1, by omega⟩
    · obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar_row⟩ := hm m hm_lt
      have hcell_eq : sb2[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat +
          m]? =
          s.scratch.scratch_buf[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]?.getD
            0#32).toNat + m]? :=
        hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
      · rw [hcell_eq]; exact fidBvaRowEntryOk_congr rfl rfl rfl hok
      · have ht_lt : t < step := by omega
        have ht_eq : sb2[t]? = s.scratch.scratch_buf[t]? :=
          hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        rw [ht_eq]; exact hent t ht
      · obtain ⟨hpi, hpok⟩ := hpar_row hr0
        obtain ⟨hpo1, hpo2⟩ := hpo hr0
        have hpar_val_eq : sb2[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD
            0#32).toNat + m]? =
            s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD
              0#32).toNat + m]? :=
          hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hprev_q_eq : (sb2[2 * fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat =
            (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat :=
          congrArg (fun o => (o.getD 0#32).toNat)
            (hget_lt (2 * fidStepsCap c.scratch_cap + (r - 1)) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega))
        have hprev_f_eq : (sb2[r - 1]?.getD 0#32).toNat =
            (s.scratch.scratch_buf[r - 1]?.getD 0#32).toNat :=
          congrArg (fun o => (o.getD 0#32).toNat)
            (hget_lt (r - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega))
        have hprev_ro_eq : (sb2[fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat =
            (s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat :=
          congrArg (fun o => (o.getD 0#32).toNat)
            (hget_lt (fidStepsCap c.scratch_cap + (r - 1)) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega))
        obtain ⟨_, hprev_ro_ge, _, hprev_ro_le, _, _⟩ := hrows (r - 1) (by omega)
        have hprev_cell_eq : sb2[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (r - 1)]?.getD
            0#32).toNat +
            (s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD
              0#32).toNat + m]?.getD 0#32).toNat]? =
            s.scratch.scratch_buf[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (r - 1)]?.getD
              0#32).toNat +
            (s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD
              0#32).toNat + m]?.getD 0#32).toNat]? :=
          hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        rw [hprev_ro_eq, hpar_val_eq, hprev_cell_eq, hprev_q_eq, hprev_f_eq]
        exact ⟨hpi, fidBvaRowEntryOk_congr rfl rfl rfl hpok⟩
  · have hreq : r = step := by omega
    subst r
    rw [hget_step, hget_sc_step, hget_2sc_step, hget_3sc_step]
    refine ⟨hbest_lt, by omega, hnq2, by dsimp only [bump']; omega,
      fun _ => ⟨by omega, by dsimp only [bump']; omega⟩, fun nm hnm => ?_⟩
    obtain ⟨hpi, res, hres_lt, hres_nd, hpok, hok, hent_lt, hent_b⟩ := hnew nm hnm
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun _ => ?_⟩
    · rw [hget_nrow nm hnm]; exact fidBvaRowEntryOk_congr rfl rfl rfl hok
    · by_cases hte : t < step
      · rw [hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hent_lt t hte
      · have hts : t = step := by omega
        subst hts; rw [hget_step]; exact hent_b
    · have hpar_val_eq : sb2[par_off.toNat + nm]? = sb'[par_off.toNat + nm]? := hget_par nm hnm
      have hprev_q_eq : (sb2[2 * fidStepsCap c.scratch_cap + (step - 1)]?.getD 0#32).toNat =
          (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + (step - 1)]?.getD 0#32).toNat :=
        congrArg (fun o => (o.getD 0#32).toNat)
          (hget_lt (2 * fidStepsCap c.scratch_cap + (step - 1)) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega))
      have hprev_f_eq : (sb2[step - 1]?.getD 0#32).toNat =
          (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat :=
        congrArg (fun o => (o.getD 0#32).toNat)
          (hget_lt (step - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega))
      have hprev_ro_eq : (sb2[fidStepsCap c.scratch_cap + (step - 1)]?.getD 0#32).toNat =
          (s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (step - 1)]?.getD 0#32).toNat :=
        congrArg (fun o => (o.getD 0#32).toNat)
          (hget_lt (fidStepsCap c.scratch_cap + (step - 1)) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega))
      obtain ⟨_, hprev_ro_ge, _, hprev_ro_le, _, _⟩ := hrows (step - 1) (by omega)
      have hprev_cell_eq : sb2[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap +
          (step - 1)]?.getD 0#32).toNat +
          (sb'[par_off.toNat + nm]?.getD 0#32).toNat]? =
          s.scratch.scratch_buf[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap +
            (step - 1)]?.getD 0#32).toNat +
          (sb'[par_off.toNat + nm]?.getD 0#32).toNat]? :=
        hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpar_val_eq, hprev_q_eq, hprev_f_eq, hprev_ro_eq, hprev_cell_eq]
      exact ⟨hpi, fidBvaRowEntryOk_congr rfl rfl rfl hpok⟩

theorem fidBvaMatrixInv_of_filter_pres {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {sb' : List (BitVec 32)} {step bump max_new : Nat}
    {nrow_off par_off : BitVec 32}
    (hmat : FidBvaMatrixInv c F_cur s step bump)
    (hnrow_eq : nrow_off.toNat = bump)
    (hpar_ge : bump ≤ par_off.toNat)
    (hpres : ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?) :
    FidBvaMatrixInv c F_cur { s with scratch := { s.scratch with scratch_buf := sb' } }
      step bump := by
  unfold FidBvaMatrixInv at hmat ⊢
  dsimp only at hmat ⊢
  rcases hmat with ⟨hsc_pos, hs1, hss, hb1, hb2, hrows⟩
  have hget_lt : ∀ idx < bump, sb'[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi => by
    apply hpres idx (by omega) (by omega) (by omega)
  refine ⟨hsc_pos, hs1, hss, hb1, hb2, fun r hr => ?_⟩
  obtain ⟨hfr, hro1, hq2, hro2, hpo, hm⟩ := hrows r hr
  have hfr_eq : (sb'[r]?.getD 0#32).toNat = (s.scratch.scratch_buf[r]?.getD 0#32).toNat :=
    congrArg (fun o => (o.getD 0#32).toNat) (hget_lt r (by omega))
  have hro_eq : (sb'[fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat =
      (s.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat :=
    congrArg (fun o => (o.getD 0#32).toNat) (hget_lt (fidStepsCap c.scratch_cap + r) (by omega))
  have hqn_eq : (sb'[2 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat =
      (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat :=
    congrArg (fun o => (o.getD 0#32).toNat) (hget_lt (2 * fidStepsCap c.scratch_cap + r) (by omega))
  have hpo_eq : (sb'[3 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat =
      (s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat :=
    congrArg (fun o => (o.getD 0#32).toNat) (hget_lt (3 * fidStepsCap c.scratch_cap + r) (by omega))
  rw [hfr_eq, hro_eq, hqn_eq, hpo_eq]
  refine ⟨hfr, hro1, hq2, hro2, fun hr0 => ?_, fun m hm_lt => ?_⟩
  · obtain ⟨hpo1, hpo2⟩ := hpo hr0
    exact ⟨hpo1, hpo2⟩
  · obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar_row⟩ := hm m hm_lt
    have hcell_eq : sb'[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]?.getD 0#32).toNat +
        m]? =
        s.scratch.scratch_buf[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]?.getD
          0#32).toNat + m]? :=
      hget_lt _ (by omega)
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
    · rw [hcell_eq]; exact fidBvaRowEntryOk_congr rfl rfl rfl hok
    · have ht_eq : sb'[t]? = s.scratch.scratch_buf[t]? := hget_lt t (by omega)
      rw [ht_eq]; exact hent t ht
    · obtain ⟨hpi, hpok⟩ := hpar_row hr0
      have hpar_val_eq : sb'[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD
          0#32).toNat + m]? =
          s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD
            0#32).toNat + m]? :=
        hget_lt _ (by have := (hpo hr0).2; omega)
      have hprev_q_eq : (sb'[2 * fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat =
          (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat :=
        congrArg (fun o => (o.getD 0#32).toNat)
          (hget_lt (2 * fidStepsCap c.scratch_cap + (r - 1)) (by omega))
      have hprev_f_eq : (sb'[r - 1]?.getD 0#32).toNat =
          (s.scratch.scratch_buf[r - 1]?.getD 0#32).toNat :=
        congrArg (fun o => (o.getD 0#32).toNat) (hget_lt (r - 1) (by omega))
      have hprev_ro_eq : (sb'[fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat =
          (s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (r - 1)]?.getD 0#32).toNat :=
        congrArg (fun o => (o.getD 0#32).toNat)
          (hget_lt (fidStepsCap c.scratch_cap + (r - 1)) (by omega))
      have hprev_cell_eq : sb'[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (r - 1)]?.getD
          0#32).toNat +
          (s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD
            0#32).toNat + m]?.getD 0#32).toNat]? =
          s.scratch.scratch_buf[(s.scratch.scratch_buf[fidStepsCap c.scratch_cap + (r - 1)]?.getD
            0#32).toNat +
          (s.scratch.scratch_buf[(s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]?.getD
            0#32).toNat + m]?.getD 0#32).toNat]? :=
        hget_lt _ (by have := (hrows (r - 1) (by omega)).2.2.2.1; omega)
      rw [hpar_val_eq, hprev_q_eq, hprev_f_eq, hprev_ro_eq, hprev_cell_eq]
      exact ⟨hpi, fidBvaRowEntryOk_congr rfl rfl rfl hpok⟩

@[expose] def StepExitBody (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (sc : Nat)
    (step best_k : BitVec 32) (bump : Nat) (stl : FullState) (ml : Mem 64) : Prop :=
  (FullMem c stl ⋆ R) ml ∧
  stl.LengthsOk c ∧ FullWitnessInv c F0 F_cur stl.core ∧
  FullArenaVarsNodup stl ∧ FullExtScratchOk c stl ∧
  stl.core.cur_level = 0 ∧ stl.core.dense_mode ≠ 0#64 ∧
  stl.core.cur_vars = s.core.cur_vars ∧ stl.core.fuel = s.core.fuel ∧
  stl.core.arena = s.core.arena ∧ stl.core.arena_len = s.core.arena_len ∧
  stl.core.mrk = s.core.mrk ∧
  stl.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  stl.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
  1 ≤ step.toNat ∧ step.toNat ≤ sc ∧
  4 * sc ≤ bump ∧ bump ≤ c.scratch_cap ∧
  FidBvaMatrixInv c F_cur stl step.toNat bump ∧
  (best_k = 0#32 ∨ (1 ≤ best_k.toNat ∧ best_k.toNat < step.toNat)) ∧
  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
  (∀ r < step.toNat,
    (stl.core.lit_mark[(stl.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
    ∃ r < step.toNat, (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l)

@[expose] def StepInvBody (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (sc : Nat)
    (step cur_qn best_k : BitVec 32) (bump : Nat) (stl : FullState) (ml : Mem 64) : Prop :=
  (FullMem c stl ⋆ R) ml ∧
  stl.LengthsOk c ∧ FullWitnessInv c F0 F_cur stl.core ∧
  FullArenaVarsNodup stl ∧ FullExtScratchOk c stl ∧
  stl.core.cur_level = 0 ∧ stl.core.dense_mode ≠ 0#64 ∧
  stl.core.cur_vars = s.core.cur_vars ∧ stl.core.fuel = s.core.fuel ∧
  stl.core.arena = s.core.arena ∧ stl.core.arena_len = s.core.arena_len ∧
  stl.core.mrk = s.core.mrk ∧
  stl.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  stl.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
  1 ≤ step.toNat ∧ step.toNat ≤ sc ∧
  4 * sc ≤ bump ∧ bump ≤ c.scratch_cap ∧
  cur_qn.toNat = (stl.scratch.scratch_buf[2 * sc + (step.toNat - 1)]?.getD 0#32).toNat ∧
  FidBvaMatrixInv c F_cur stl step.toNat bump ∧
  (best_k = 0#32 ∨ (1 ≤ best_k.toNat ∧ best_k.toNat < step.toNat)) ∧
  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
  (∀ r < step.toNat,
    (stl.core.lit_mark[(stl.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
    ∃ r < step.toNat, (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l)

theorem stepExitBody_of_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {sc : Nat}
    {step cur_qn best_k : BitVec 32} {bump : Nat} {stl : FullState} {ml : Mem 64}
    (h : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump stl ml) :
    StepExitBody c F0 F_cur s R sc step best_k bump stl ml := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    _, h19, h20, h21, h22, h23⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩

theorem fid_sc_pos_of_ne_zero {cap : Nat}
    (h : (BitVec.ofNat 32 (fidStepsCap cap)) ≠ 0#32) :
    0 < fidStepsCap cap := by
  have _hle := fidStepsCap_le_256 cap
  apply Classical.byContradiction; intro h0
  have hz : fidStepsCap cap = 0 := by omega
  rw [hz] at h; contradiction

theorem fid_wp_call_steps_cap (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    {rs : List Ty} {Q : Post rs} {X : XPost}
    {x : BitVec 64} {m : Mem 64} {k : Tup Val [i32] → Expr Val Cont rs}
    (hk : wp Γ Q X (k (BitVec.ofNat 32 (fidStepsCap x.toNat), ())) m) :
    wp Γ Q X (Expr.call (as := [i64]) "full_bva_steps_cap_fid" (Arg.var x, ()) k) m :=
  wp_call_of_spec _ _ (hSteps _ _ _ _ hk)


@[expose, reducible] def fidTryLitStepBlock
    (V : Ty → Type) (L : List Ty → Type)
    (cap_2 : Tup V [i32]) (cap_3 : Tup V [i64, i32, i64])
    (cap_4 : V i64) (cap_5 : Tup V [i64])
    (Jex : Tup L [[i32, i32, i32, i32, i64]]) (cap_7 cap_8 cap_9 : V i64) :
    Tup L [[i32, i32, i32, i32, i64]] →
    Blocks V L [Ty.bool] [[i32, i32, i32, i32, i64]] :=
  fun Js =>
    Blocks.cons (fun p =>
    Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
      args := (Arg.var p.snd.fst,
      Arg.var cap_2.fst,
      ()) }
    fun p_1 =>
    Expr.jnz (Arg.var p_1.fst) (Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
      args := (Arg.var p.snd.snd.fst,
      Arg.imm 2,
      ()) }
    fun p_2 =>
    Expr.jnz (Arg.var p_2.fst) (Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.add i64,
      args := (Arg.var cap_3.fst,
      Arg.imm 1136,
      ()) }
    fun p_3 =>
    Expr.load i64 (Arg.var p_3.fst) fun ld =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
      args := (Arg.var ld,
      Arg.imm 0,
      ()) }
    fun p_4 =>
    Expr.jnz (Arg.var p_4.fst) (Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.add i32,
      args := (Arg.var cap_2.fst,
      Arg.var p.snd.fst,
      ()) }
    fun p_5 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.sub i32, args := (Arg.var p_5.fst, Arg.imm 1, ()) }
    fun p_6 =>
    Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_6.fst, ()) }
    fun p_7 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_7.fst, Arg.imm 4, ()) }
    fun p_8 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var cap_4, Arg.var p_8.fst, ()) }
    fun p_9 =>
    Expr.load i32 (Arg.var p_9.fst) fun ld =>
    Expr.call (as := [i64, i32, i32, i64]) (bs := [i32]) "full_bva_scan_cands" (Arg.var
      cap_3.fst, Arg.var ld, Arg.var
      p.snd.snd.fst,
      Arg.var cap_5.fst, ()) fun p_10 =>
    Expr.call (as := [i64, i32, i32]) (bs := [i32]) "full_bva_pick_cand" (Arg.var cap_3.fst,
      Arg.var p_10.fst, Arg.var
      cap_3.snd.fst,
      ()) fun p_11 =>
    Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
      args := (Arg.var p_11.fst,
      Arg.imm 4294967295,
      ()) }
    fun p_12 =>
    Expr.jnz (Arg.var p_12.fst) (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var
      p.snd.snd.fst, Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())) (Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.add i64,
      args := (Arg.var cap_3.fst,
      Arg.imm 1136,
      ()) }
    fun p_13 =>
    Expr.load i64 (Arg.var p_13.fst) fun ld_1 =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
      args := (Arg.var ld_1,
      Arg.imm 0,
      ()) }
    fun p_14 =>
    Expr.jnz (Arg.var p_14.fst) (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var
      p.snd.snd.fst, Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) }
    fun p_15 =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.sub i64,
      args := (Arg.var cap_7,
      Arg.var p_15.fst,
      ()) }
    fun p_16 =>
    Expr.let_
    { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var p_16.fst, ()) }
    fun p_17 =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.lshr i32, args := (Arg.var p_17.fst, Arg.imm 1, ()) }
    fun p_18 =>
    Expr.group (sig := [[i32]]) (fun _Js_1 =>
    Blocks.cons (fun p_19 =>
    Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
      args := (Arg.var p_19.fst,
      Arg.imm 2,
      ()) }
    fun p_20 =>
    Expr.jnz (Arg.var p_20.fst) (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var
      p.snd.snd.fst, Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())) (Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.add i32,
      args := (Arg.var p.fst,
      Arg.var p_19.fst,
      ()) }
    fun p_21 =>
    Expr.call (as := [i64, i32, i32, i32, i32, i32]) (bs := [i32]) "full_bva_filter_row"
      (Arg.var cap_3.fst, Arg.var ld, Arg.var
      p.fst, Arg.var
      p_21.fst, Arg.var p.snd.snd.fst, Arg.var p_11.fst, ()) fun p_22 =>
    Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
      args := (Arg.var p_22.fst,
      Arg.imm 2,
      ()) }
    fun p_23 =>
    Expr.jnz (Arg.var p_23.fst) (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var
      p_22.fst, Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.snd.fst, ()) }
    fun p_24 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_24.fst, Arg.imm 4, ()) }
    fun p_25 =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.add i64,
      args := (Arg.var cap_4,
      Arg.var p_25.fst,
      ()) }
    fun p_26 =>
    Expr.store (Arg.var p_11.fst) (Arg.var p_26.fst) (Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.add i32,
      args := (Arg.var cap_2.fst,
      Arg.var p.snd.fst,
      ()) }
    fun p_27 =>
    Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_27.fst, ()) }
    fun p_28 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_28.fst, Arg.imm 4, ()) }
    fun p_29 =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.add i64,
      args := (Arg.var cap_4,
      Arg.var p_29.fst,
      ()) }
    fun p_30 =>
    Expr.store (Arg.var p.fst) (Arg.var p_30.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.mul i32, args := (Arg.imm 2, Arg.var cap_2.fst, ()) }
    fun p_31 =>
    Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.add i32,
      args := (Arg.var p_31.fst,
      Arg.var p.snd.fst,
      ()) }
    fun p_32 =>
    Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_32.fst, ()) }
    fun p_33 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_33.fst, Arg.imm 4, ()) }
    fun p_34 =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.add i64,
      args := (Arg.var cap_4,
      Arg.var p_34.fst,
      ()) }
    fun p_35 =>
    Expr.store (Arg.var p_22.fst) (Arg.var p_35.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.mul i32, args := (Arg.imm 3, Arg.var cap_2.fst, ()) }
    fun p_36 =>
    Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.add i32,
      args := (Arg.var p_36.fst,
      Arg.var p.snd.fst,
      ()) }
    fun p_37 =>
    Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_37.fst, ()) }
    fun p_38 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_38.fst, Arg.imm 4, ()) }
    fun p_39 =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.add i64,
      args := (Arg.var cap_4,
      Arg.var p_39.fst,
      ()) }
    fun p_40 =>
    Expr.store (Arg.var p_21.fst) (Arg.var p_40.fst) (Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.add i32,
      args := (Arg.var p_21.fst,
      Arg.var p_22.fst,
      ()) }
    fun p_41 =>
    Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_11.fst, ()) }
    fun p_42 =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.add i64,
      args := (Arg.var cap_8,
      Arg.var p_42.fst,
      ()) }
    fun p_43 =>
    Expr.let_
    { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 1, ()) }
    fun p_44 =>
    Expr.store (Arg.var p_44.fst) (Arg.var p_43.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p.snd.fst, Arg.imm 1, ()) }
    fun p_45 =>
    Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_45.fst, ()) }
    fun p_46 =>
    Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_22.fst, ()) }
    fun p_47 =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.mul i64,
      args := (Arg.var p_46.fst,
      Arg.var p_47.fst,
      ()) }
    fun p_48 =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.add i64,
      args := (Arg.var p_46.fst,
      Arg.var p_47.fst,
      ()) }
    fun p_49 =>
    Expr.group (sig := [[i32, i64]]) (fun _Js_2 =>
    Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p_41.fst, Arg.var p_45.fst, Arg.var p_22.fst, Arg.var p.fst,
      Arg.var p.snd.fst, ())) Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
      args := (Arg.var p_48.fst,
      Arg.var p_49.fst,
      ()) }
    fun p_50 =>
    Expr.jnz (Arg.var p_50.fst) (Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.sub i64,
      args := (Arg.var p_48.fst,
      Arg.var p_49.fst,
      ()) }
    fun p_51 =>
    Expr.group (sig := [[i32, i64]]) (fun _Js_2 =>
    Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
      args := (Arg.var p_51.fst,
      Arg.var cap_9,
      ()) }
    fun p_52 =>
    Expr.jnz (Arg.var p_52.fst) (Expr.let_
    { sig := [i64,
      i64],
      code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
      args := (Arg.var p_51.fst,
      Arg.var p.snd.snd.snd.snd.fst,
      ()) }
    fun p_53 =>
    Expr.jnz (Arg.var p_53.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.sub i32, args := (Arg.var p_45.fst, Arg.imm 1, ()) }
    fun p =>
    Expr.jump Js.fst (Arg.var p.fst, Arg.var p_51.fst, ())) (Expr.jump Js.fst (Arg.var
      p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ()))) (Expr.jump Js.fst (Arg.var
      p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ()))) (Expr.jump Js.fst (Arg.var
      p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())))))))))) Blocks.nil) fun Js =>
    Expr.let_
    { sig := [i32,
      i32],
      code := OpCode.cmp CmpOp.ugt i32 Ty.bool rfl,
      args := (Arg.var p_18.fst,
      Arg.var p.snd.snd.fst,
      ()) }
    fun p_19 =>
    Expr.jnz (Arg.var p_19.fst) (Expr.jump Js.fst (Arg.var p.snd.snd.fst, ())) (Expr.jump
      Js.fst (Arg.var p_18.fst, ()))))) (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst,
      Arg.var p.snd.snd.fst, Arg.var p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ())))
      (Expr.jump Jex.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, Arg.var
      p.snd.snd.snd.fst, Arg.var p.snd.snd.snd.snd.fst, ()))) (Expr.jump Jex.fst (Arg.var
      p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, Arg.var p.snd.snd.snd.fst, Arg.var
      p.snd.snd.snd.snd.fst, ()))) Blocks.nil


@[expose, reducible] def fidTryLitExitBlock
    (V : Ty → Type) (L : List Ty → Type)
    (ecap_2 ecap_3 : V i64)
    (ecap_4 : Tup V [i64, i32, i64])
    (ecap_5 : Tup V [i32])
    (ecap_6 : V i64) :
    Tup L [[i32, i32, i32, i32, i64]] →
    Blocks V L [Ty.bool] [[i32, i32, i32, i32, i64]] :=
    fun _Js =>
    Blocks.cons (fun p =>
    Expr.group (sig := [[i32]]) (fun Js =>
    Blocks.cons (fun p_1 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl, args := (Arg.var
      p_1.fst, Arg.var p.snd.fst, ()) } fun p_2 =>
    Expr.jnz (Arg.var p_2.fst)
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_1.fst, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ())
      } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_2, Arg.var p.fst,
      ()) } fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_3, Arg.var p.fst,
      ()) } fun p =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_3 =>
    Expr.store (Arg.var p_3.fst) (Arg.var p.fst)
    (
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_1.fst, Arg.imm 1,
      ()) } fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ())))
    (
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl, args := (Arg.var
      p.snd.snd.snd.fst, Arg.imm 0, ()) } fun p_3 =>
    Expr.jnz (Arg.var p_3.fst) (
    Expr.ret (Arg.imm false, ()))
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_4.fst, Arg.imm
      856, ()) } fun p_4 =>
    Expr.load i64 (Arg.var p_4.fst) fun ld =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_4.fst, Arg.imm
      408, ()) } fun p_5 =>
    Expr.load i64 (Arg.var p_5.fst) fun ld_1 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_4.fst, Arg.imm
      776, ()) } fun p_6 =>
    Expr.load i64 (Arg.var p_6.fst) fun ld_2 =>
    Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_7 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.var ld_2, Arg.var p_7.fst,
      ()) } fun p_8 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p.snd.snd.snd.fst,
      Arg.imm 1, ()) } fun p_9 =>
    Expr.group (sig := [[i64, i32]]) (fun Js =>
    Blocks.cons (fun p_10 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl, args := (Arg.var
      p_10.snd.fst, Arg.var p_9.fst, ()) } fun p_11 =>
    Expr.jnz (Arg.var p_11.fst)
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_10.snd.fst, ()) } fun
      p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ())
      } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_2, Arg.var p.fst,
      ()) } fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld_3 =>
    Expr.group (sig := [[i64]]) (fun _Js_1 =>
    Blocks.cons (fun p =>
    Expr.let_ { sig := [i32, i32], code := OpCode.xor i32, args := (Arg.var ld_3, Arg.imm 1, ()) }
      fun p_12 =>
    Expr.group (sig := [[i64]]) (fun _Js_2 =>
    Blocks.cons (fun p =>
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_10.snd.fst, Arg.imm
      1, ()) } fun p_13 =>
    Expr.jump Js.fst (Arg.var p.fst, Arg.var p_13.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_12.fst, ()) } fun p_13
      =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_13.fst, Arg.imm 4,
      ()) } fun p_14 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_1, Arg.var
      p_14.fst, ()) } fun p_15 =>
    Expr.load i32 (Arg.var p_15.fst) fun ld_4 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl, args := (Arg.var
      ld_4, Arg.imm 0, ()) } fun p_16 =>
    Expr.jnz (Arg.var p_16.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl, args := (Arg.var
      p.fst, Arg.var p_8.fst, ()) } fun p_17 =>
    Expr.jnz (Arg.var p_17.fst)
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_12.fst, ()) } fun p_18
      =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_18.fst, Arg.imm 4,
      ()) } fun p_19 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_1, Arg.var
      p_19.fst, ()) } fun p_20 =>
    Expr.store (t := i32) (Arg.imm 1) (Arg.var p_20.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ())
      } fun p_21 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.var p_21.fst,
      ()) } fun p_22 =>
    Expr.store (Arg.var p_12.fst) (Arg.var p_22.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 1, ())
      } fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ())))) (
    Expr.jump Js.fst (Arg.var p.fst, ()))) (
    Expr.jump Js.fst (Arg.var p.fst, ())))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_3, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ())
      } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_1, Arg.var p.fst,
      ()) } fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld_4 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl, args := (Arg.var
      ld_4, Arg.imm 0, ()) } fun p =>
    Expr.jnz (Arg.var p.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl, args := (Arg.var
      p_10.fst, Arg.var p_8.fst, ()) } fun p =>
    Expr.jnz (Arg.var p.fst)
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_3, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ())
      } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_1, Arg.var p.fst,
      ()) } fun p =>
    Expr.store (t := i32) (Arg.imm 1) (Arg.var p.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_10.fst, Arg.imm 4,
      ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.var p.fst, ())
      } fun p =>
    Expr.store (Arg.var ld_3) (Arg.var p.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_10.fst, Arg.imm 1,
      ()) } fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ())))) (
    Expr.jump Js.fst (Arg.var p_10.fst, ()))) (
    Expr.jump Js.fst (Arg.var p_10.fst, ())))
    (
    Expr.let_ { sig := [i32, i32], code := OpCode.mul i32, args := (Arg.imm 2, Arg.var ecap_5.fst,
      ()) } fun p_12 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_12.fst, Arg.var
      p.snd.snd.snd.fst, ()) } fun p_13 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_13.fst, ()) } fun p_14
      =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_14.fst, Arg.imm 4,
      ()) } fun p_15 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_2, Arg.var
      p_15.fst, ()) } fun p_16 =>
    Expr.load i32 (Arg.var p_16.fst) fun ld_3 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.snd.snd.snd.fst, ()) }
      fun p_17 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_17.fst, Arg.imm 4,
      ()) } fun p_18 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_2, Arg.var
      p_18.fst, ()) } fun p_19 =>
    Expr.load i32 (Arg.var p_19.fst) fun ld_4 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var ecap_5.fst, Arg.var
      p.snd.snd.snd.fst, ()) } fun p_20 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_20.fst, ()) } fun p_21
      =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_21.fst, Arg.imm 4,
      ()) } fun p_22 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_2, Arg.var
      p_22.fst, ()) } fun p_23 =>
    Expr.load i32 (Arg.var p_23.fst) fun ld_5 =>
    Expr.group (sig := [[i64, i32]]) (fun Js =>
    Blocks.cons (fun p_24 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl, args := (Arg.var
      p_24.snd.fst, Arg.var ld_3, ()) } fun p_25 =>
    Expr.jnz (Arg.var p_25.fst)
    (
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var ld_5, Arg.var
      p_24.snd.fst, ()) } fun p =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ())
      } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_2, Arg.var p.fst,
      ()) } fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld_6 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p_24.snd.fst, Arg.imm
      1, ()) } fun p =>
    Expr.group (sig := [[i64]]) (fun _Js_1 =>
    Blocks.cons (fun p_26 =>
    Expr.jump Js.fst (Arg.var p_26.fst, Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld_6, Arg.imm
      2147483648, ()) } fun p =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl, args := (Arg.var
      p.fst, Arg.imm 0, ()) } fun p =>
    Expr.jnz (Arg.var p.fst)
    (
    Expr.let_ { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld_6, Arg.imm
      2147483647, ()) } fun p =>
    Expr.group (sig := [[i64]]) (fun _Js_1 =>
    Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p_26 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_26.fst, Arg.imm 4,
      ()) } fun p_27 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_1, Arg.var
      p_27.fst, ()) } fun p_28 =>
    Expr.load i32 (Arg.var p_28.fst) fun ld_7 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl, args := (Arg.var
      ld_7, Arg.imm 0, ()) } fun p_29 =>
    Expr.jnz (Arg.var p_29.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl, args := (Arg.var
      p_24.fst, Arg.var p_8.fst, ()) } fun p_30 =>
    Expr.jnz (Arg.var p_30.fst)
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) } fun p_31 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_31.fst, Arg.imm 4,
      ()) } fun p_32 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_1, Arg.var
      p_32.fst, ()) } fun p_33 =>
    Expr.store (t := i32) (Arg.imm 1) (Arg.var p_33.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_24.fst, Arg.imm 4,
      ()) } fun p_34 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.var p_34.fst,
      ()) } fun p_35 =>
    Expr.store (Arg.var p.fst) (Arg.var p_35.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_24.fst, Arg.imm 1,
      ()) } fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ())))) (
    Expr.jump Js.fst (Arg.var p_24.fst, ()))) (
    Expr.jump Js.fst (Arg.var p_24.fst, ())))
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_6, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 2, ())
      } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ())
      } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_6, Arg.var p.fst,
      ()) } fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld_7 =>
    Expr.group (sig := [[i64, i32]]) (fun Js_1 =>
    Blocks.cons (fun p =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl, args := (Arg.var
      p.snd.fst, Arg.var ld_7, ()) } fun p_26 =>
    Expr.jnz (Arg.var p_26.fst)
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_6, ()) } fun p_27 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_27.fst, Arg.imm 3,
      ()) } fun p_28 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.snd.fst, ()) } fun
      p_29 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_28.fst, Arg.var
      p_29.fst, ()) } fun p_30 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_30.fst, Arg.imm 4,
      ()) } fun p_31 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_6, Arg.var
      p_31.fst, ()) } fun p_32 =>
    Expr.load i32 (Arg.var p_32.fst) fun ld_8 =>
    Expr.group (sig := [[i64]]) (fun _Js =>
    Blocks.cons (fun p_33 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var p.snd.fst, Arg.imm 1,
      ()) } fun p =>
    Expr.jump Js_1.fst (Arg.var p_33.fst, Arg.var p.fst, ()))
    Blocks.nil) fun Js =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl, args := (Arg.var
      ld_8, Arg.var ld_4, ()) } fun p_33 =>
    Expr.jnz (Arg.var p_33.fst)
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_8, ()) } fun p_34 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_34.fst, Arg.imm 4,
      ()) } fun p_35 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_1, Arg.var
      p_35.fst, ()) } fun p_36 =>
    Expr.load i32 (Arg.var p_36.fst) fun ld_9 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl, args := (Arg.var
      ld_9, Arg.imm 0, ()) } fun p_37 =>
    Expr.jnz (Arg.var p_37.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl, args := (Arg.var
      p.fst, Arg.var p_8.fst, ()) } fun p_38 =>
    Expr.jnz (Arg.var p_38.fst)
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_8, ()) } fun p_39 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_39.fst, Arg.imm 4,
      ()) } fun p_40 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_1, Arg.var
      p_40.fst, ()) } fun p_41 =>
    Expr.store (t := i32) (Arg.imm 1) (Arg.var p_41.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ())
      } fun p_42 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.var p_42.fst,
      ()) } fun p_43 =>
    Expr.store (Arg.var ld_8) (Arg.var p_43.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 1, ())
      } fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ())))) (
    Expr.jump Js.fst (Arg.var p.fst, ()))) (
    Expr.jump Js.fst (Arg.var p.fst, ()))) (
    Expr.jump Js.fst (Arg.var p.fst, ()))) (
    Expr.jump Js.fst (Arg.var p.fst, ())))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.var p_24.fst, Arg.imm 0, ()))) (
    Expr.group (sig := [[i64]]) (fun Js =>
    Blocks.cons (fun p_26 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl, args := (Arg.var
      p_26.fst, Arg.var p_24.fst, ()) } fun p_27 =>
    Expr.jnz (Arg.var p_27.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_26.fst, Arg.imm 4,
      ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.var p.fst, ())
      } fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ())
      } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_1, Arg.var p.fst,
      ()) } fun p =>
    Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_26.fst, Arg.imm 1,
      ()) } fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ())))
    (
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ecap_4.fst, Arg.imm
      1144, ()) } fun p_28 =>
    Expr.store (Arg.var p_24.fst) (Arg.var p_28.fst) (
    Expr.call (as := [i64, i32]) (bs := [Ty.bool]) "full_bva_commit" (Arg.var ecap_4.fst, Arg.var
      p.snd.snd.snd.fst, ()) fun p =>
    Expr.ret (Arg.var p.fst, ()))))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, ())))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.var p_10.fst, Arg.imm 0, ())))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ()))))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, ()))
    Blocks.nil
end LeanQbe.T.Examples.Kissat.FullFidelityBva
