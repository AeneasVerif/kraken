module

public import LeanQbe.T.Examples.LratBytesSpec
public import Kraken.SeparationTactics
import all Kraken.Mem
import all Kraken.Separation

/-!
# `lbReadAddLits` (and `lbRupCheck` in Stepping-Stone 2): correctness in `LeanQbe.T`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.ProofUtil

/-! ## 1. Zig-zag decoding and `lbReadAddLits_correct` -/

private theorem zigzag_eq {u : Nat} (_hu : u < 2 ^ 28) :
    let v : BitVec 64 := BitVec.ofNat 64 (u / 2)
    let sbit : BitVec 64 := BitVec.ofNat 64 u &&& 1
    let mask : BitVec 64 := 0 - sbit
    (v ^^^ mask) - mask = decodeZigZag u := by
  dsimp only [decodeZigZag]
  have hmask : (0 : BitVec 64) - (BitVec.ofNat 64 u &&& 1) = if u % 2 == 1 then -1 else 0 := by
    grind
  rw [hmask, negif]

theorem lbReadAddLits_correct (Γ : Env) :
    ∀ args m Q X, lbReadAddLitsSpec args m Q X → Func.spec Γ lbReadAddLits args m Q X := by
  rintro _ m Q X ⟨c, prf_ptr, prfBytes, idx0, poolUsed, poolRem, ptrs, table, PoolUsed, R,
    rfl, hprf_fit, hidx0, hm, hQ⟩
  unfold lbReadAddLits Func.spec Func.wp
  obtain ⟨hsum, htbl, hpu, hm_u⟩ := workState_sep.mp (sep_ac hm :
    (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆
      (Eq (prfBytes.At prf_ptr) ⋆ R)) m)
  let c_ptr : BitVec 64 := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let cur0 : BitVec 64 := prf_ptr + BitVec.ofNat 64 idx0
  have hcptr_ne0 : c_ptr ≠ 0 := c.pcur_ne_zero (by omega)
  have hm_hdr :
      (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
        (wsFixed c ptrs PoolUsed ⋆ region c_ptr (4 * poolRem) ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    unfold wsFixed; exact sep_cast hm_u (by dsimp only [c_ptr, cur0]; ac_rfl)
  wp_unfold
  refine ⟨_, loadl_hdr 0 (by decide) hm_hdr (by simp),
    _, loadl_hdr 7 (by decide) hm_hdr rfl,
    _, loadl_hdr 8 (by decide) hm_hdr rfl,
    _, loadl_hdr 9 (by decide) hm_hdr rfl, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  refine wp_join_group (fun () m' =>
    readAddLitsPure c.mv poolRem (prfBytes.drop idx0) = none ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m') ?_ ?_
  · rintro _ ⟨⟩ m' ⟨hnone, hreg⟩
    dsimp only [Blocks.get_here]; wp_unfold
    exact hQ 0 m' (by rw [hnone]; exact ⟨rfl, hreg⟩)
  intro Jfail hJfail
  have collapseFail : ∀ (acc : List (BitVec 64)) (rem : Nat) (m' : Mem 64),
      acc.length + rem = poolRem →
      readAddLitsPure c.mv poolRem (prfBytes.drop idx0) = none →
      (Eq (prfBytes.At prf_ptr) ⋆
        (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
          int4Array c_ptr acc.reverse ⋆
          region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) ⋆ R) m' →
      Jfail () m' := fun acc rem m' hlen_rem hnone hm' =>
    hJfail () m' ⟨hnone, wsFixed_fail_collapse c htbl.1 (by omega) hpu hm'⟩
  -- `@rd_loop(%cur, %wcur)`
  refine wp_loop_group (fun fuel (cur_v, wcur_v, ()) m' => ∃ (idx rem : Nat) (acc : List (BitVec 64)),
    (prfBytes.drop idx).length < fuel ∧ idx ≤ prfBytes.length ∧ acc.length + rem = poolRem ∧
    (∀ x ∈ acc, IsValidLit c.mv x) ∧
    cur_v = prf_ptr + BitVec.ofNat 64 idx ∧ wcur_v = c_ptr + BitVec.ofNat 64 (4 * acc.length) ∧
    readAddLitsPure c.mv poolRem (prfBytes.drop idx0) =
      readAddLitsAux fuel c.mv rem acc (prfBytes.drop idx) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
        int4Array c_ptr acc.reverse ⋆
        region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) ⋆ R) m') ?_ ?_
  · rintro Jloop fuel ⟨cur_v, wcur_v, ⟨⟩⟩ m' ih
      ⟨idx, rem, acc, hfuel_gt, hidx, hrem_sum, hacc_valid, rfl, rfl, hpure, hm'⟩
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    let wcur : BitVec 64 := c_ptr + BitVec.ofNat 64 (4 * acc.length)
    have hwcur_eq : wcur = c.pbase + BitVec.ofNat 64 (4 * (c.poolInts - rem)) := by grind
    dsimp only [Blocks.get_here]
    wp_unfold
    refine ⟨fun hfull => ?_, fun hnfull => ?_⟩
    · obtain rfl : rem = 0 := (c.pcur_eq_plim_iff (by omega)).mp (hwcur_eq ▸ hfull)
      simp only [readAddLitsAux, beq_self_eq_true, ↓reduceIte] at hpure
      exact collapseFail acc 0 m' hrem_sum hpure hm'
    · have hrem_pos : 0 < rem := Nat.pos_of_ne_zero fun h0 => hnfull (by
        rw [show c_ptr + BitVec.ofNat 64 (4 * acc.length) = wcur from rfl, hwcur_eq]
        exact (c.pcur_eq_plim_iff (by omega)).mpr h0)
      have hrem_b : (rem == 0) = false := beq_false_of_ne (by omega)
      refine readLeb128_spec hprf_fit hidx rfl rfl (by ecancel)
        (fun hleb_none => ?_)
        (fun u bs' hleb_some hu _ hbs' _ => ?_)
      · simp only [readAddLitsAux, hrem_b, Bool.false_eq_true, ↓reduceIte, hleb_none] at hpure
        exact collapseFail acc rem m' hrem_sum hpure hm'
      · let idx' := prfBytes.length - bs'.length
        have hidx'_le : idx' ≤ prfBytes.length := by omega
        wp_unfold
        refine bv_eq_zero_branch (by omega : u < 2 ^ 64) (fun hu0 => ?_) (fun hu_ne0 => ?_)
        · subst hu0
          simp only [readAddLitsAux, hrem_b, Bool.false_eq_true, ↓reduceIte, hleb_some] at hpure
          have hfa := c.fit_active; unfold WorkCfg.activeBytes at hfa
          obtain ⟨ok_z, hpu', hm1_hdr⟩ := wsFixed_finish_clause hrem_pos (by omega) hpu hm'
          let cur2 : BitVec 64 := prf_ptr + BitVec.ofNat 64 idx'
          let pcur' : BitVec 64 := c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (acc.length + 1)))
          have hwcur2_eq : wcur + 4 = pcur' := by dsimp [wcur, c_ptr, pcur']; grind
          obtain ⟨ok_p64, hm2⟩ := store_word8Array (i := 8) (wcur + 4)
            (by simp [WorkCfg.hdrWords]) hm1_hdr
          obtain ⟨ok_p72, hm3⟩ := store_word8Array (i := 9) cur2 (by simp [WorkCfg.hdrWords]) hm2
          refine ⟨ok_z, ok_p64, ok_p72, ?_⟩
          have hhdr_end : ((c.hdrWords c_ptr cur0).set 8 (wcur + 4)).set 9 cur2 =
              c.hdrWords pcur' cur2 := by rw [hwcur2_eq]; rfl
          rw [hhdr_end] at hm3
          have hws_done :
              (WorkState c (poolUsed + (acc.reverse.length + 1)) (rem - 1) cur2
                ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr acc.reverse) ⋆
                (Eq (prfBytes.At prf_ptr) ⋆ R)) _ :=
            workState_sep.mpr ⟨by simp; omega, TableRel.frame_right _ htbl,
              by simpa using hpu', by
                unfold wsFixed at hm3
                exact sep_cast hm3
                  (by dsimp only [c_ptr, pcur']; simp only [List.length_reverse]; ac_rfl)⟩
          have hm_done :
              (Eq (prfBytes.At prf_ptr) ⋆
                WorkState c (poolUsed + (acc.reverse.length + 1)) (rem - 1) cur2
                  ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr acc.reverse) ⋆ R) _ := sep_ac hws_done
          have hvalid_clits : ∀ x ∈ acc.reverse, IsValidLit c.mv x :=
            fun x hx => hacc_valid x (List.mem_reverse.mp hx)
          have hwcur_cptr : wcur = c_ptr ↔ acc.length = 0 := by grind
          grind
        · have hpure_step :
              readAddLitsAux (fuel' + 1) c.mv rem acc (prfBytes.drop idx) =
                (let v := u / 2
                 if v == 0 || c.mv < v then none
                 else readAddLitsAux fuel' c.mv (rem - 1) (decodeZigZag u :: acc) bs') := by
            cases u with
            | zero => exact absurd rfl hu_ne0
            | succ _ =>
              simp only [readAddLitsAux, hrem_b, Bool.false_eq_true, ↓reduceIte, hleb_some]
          rw [hpure_step] at hpure
          rw [bv_shr_one (by omega : u < 2 ^ 64)]
          have hmv_lt64 : c.mv < 2 ^ 64 := by have := c.hmv; unfold dimacsBound at this; omega
          refine bv_eq_zero_branch (by omega : u / 2 < 2 ^ 64)
            (fun _ => by grind) (fun hv_ne0 => ?_)
          refine ult_branch hmv_lt64 (by omega : u / 2 < 2 ^ 64)
            (fun _ => by grind) (fun hnlt => ?_)
          have hv_ne0_b : ((u / 2) == 0) = false := beq_false_of_ne hv_ne0
          have hv_le_b : decide (c.mv < u / 2) = false := decide_eq_false hnlt
          simp only [hv_ne0_b, hv_le_b, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hpure
          rw [zigzag_eq hu]
          have hfa := c.fit_active; unfold WorkCfg.activeBytes at hfa
          obtain ⟨ok_lit, hm1_next⟩ := wsFixed_push_lit (decodeZigZag u) hrem_pos (by omega) hm'
          have hlit_valid := isValidLit_decodeZigZag hu (by omega) (by omega) c.hmv
          refine ⟨ok_lit, ih fuel' _ _ (by omega)
            ⟨idx', rem - 1, decodeZigZag u :: acc, by rw [← hbs']; omega, by omega,
              by simp; omega, by grind, rfl, by simp only [List.length_cons, ptr4],
              by rwa [← hbs'], hm1_next⟩⟩
  · intro Jloop hJloop; wp_unfold
    have hm_init :
        (Eq (prfBytes.At prf_ptr) ⋆
          (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
            int4Array c_ptr ([] : List (BitVec 64)).reverse ⋆
            region (c_ptr + BitVec.ofNat 64 (4 * ([] : List (BitVec 64)).length)) (4 * poolRem)) ⋆
          R) m := by
      simp only [List.reverse_nil, int4Array_nil, List.length_nil, Nat.mul_zero, BitVec.add_zero]
      have hemp_r : (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆ emp) =
          (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed) := by simp [sep_emp]
      rw [hemp_r]; unfold wsFixed
      exact sep_cast hm_u (by dsimp only [c_ptr, cur0]; ac_rfl)
    exact hJloop ((prfBytes.drop idx0).length + 1) _ _
      ⟨idx0, poolRem, [], by omega, hidx0, by simp, by simp,
        rfl, by simp [c_ptr], rfl, hm_init⟩

end LeanQbe.T.Examples.LratBytes
