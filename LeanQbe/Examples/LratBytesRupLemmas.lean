module

public import LeanQbe.Examples.LratBytesSpec
public import LeanQbe.Examples.LratRupLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# `lbReadAddLits` and `lbRupCheck`: correctness

The RUP loops of `lb_rup_check` work on the same values and trail arrays as lrat_trim's
`br_check_clause_non_strictly_by_propagation`, and `LratBytes.lean` repeats its inline helpers
`assignedLit` and `backtrack` verbatim. This file therefore reuses, from `LratRupLemmas.lean`
(`LeanQbe.LratRup`), the propagation state `PState` with `pstate_sep`, and the specifications
`assignedLit_spec` and `backtrack_spec`. That is the one place where the `LratBytes` proofs depend on
the lrat_trim proofs.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.LratRup
open ProofUtil

/-! ## 1. `WorkCfg` layout helpers, zig-zag decoding, and `lbReadAddLits_correct` -/

private theorem zigzag_eq {u : Nat} (hu : u < 2 ^ 28) :
    let v : Val := BitVec.ofNat 64 (u / 2)
    let sbit : Val := BitVec.ofNat 64 u &&& 1
    let mask : Val := 0 - sbit
    (v ^^^ mask) - mask = decodeZigZag u := by
  dsimp only [decodeZigZag]
  have hmask : (0 : Val) - (BitVec.ofNat 64 u &&& 1) = if u % 2 == 1 then -1 else 0 := by
    grind
  rw [hmask, negif]

private abbrev wsFixed (c : WorkCfg) (ptrs : List Val) (PoolUsed : Mem 64 → Prop) :
    Mem 64 → Prop :=
  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tb c.tRaw ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆
  word8Array c.cb ptrs ⋆
  PoolUsed

theorem lbReadAddLits_correct (Γ : Env) :
    ∀ args m Q X, lbReadAddLitsSpec args m Q X → Func.spec Γ lbReadAddLits args m Q X := by
  rintro _ m Q X ⟨c, prf_ptr, prfBytes, idx0, poolUsed, poolRem, ptrs, table, PoolUsed, R,
    rfl, hprf_fit, hidx0, hm, hQ⟩
  unfold lbReadAddLits Func.spec
  have hm_ws0 :
      (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆
        (Eq (prfBytes.At prf_ptr) ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨hsum, htbl, hpu, hm_u⟩ := workState_sep.mp hm_ws0
  let c_ptr : Val := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let cur0 : Val := prf_ptr + BitVec.ofNat 64 idx0
  have hpbase_fit : c.pbase.toNat + 4 * c.poolInts < 2 ^ 64 := by
    have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
    have := c.toNat_cb; have := c.toNat_pbase; unfold WorkCfg.activeBytes at *; omega
  have hcptr_ne0 : c_ptr ≠ 0 := c.pcur_ne_zero (by omega)
  have hm_hdr :
      (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
        (wsFixed c ptrs PoolUsed ⋆ region c_ptr (4 * poolRem) ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m :=
    sep_cast hm_u (by dsimp only [c_ptr, cur0, wsFixed]; ac_rfl)
  wp_unfold
  refine ⟨_, loadl_hdr 0 (by decide) hm_hdr (by simp),
    _, loadl_hdr 7 (by decide) hm_hdr rfl,
    _, loadl_hdr 8 (by decide) hm_hdr rfl,
    _, loadl_hdr 9 (by decide) hm_hdr rfl, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  -- `@fail`: returns 0 when `readAddLitsPure = none` and memory collapses to `region c.hdr c.activeBytes`
  apply wp_join (fun as m' => as = [] ∧
    readAddLitsPure c.mv poolRem (prfBytes.drop idx0) = none ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
  · rintro _ m' ⟨rfl, hnone, hreg⟩
    wp_unfold
    exact hQ 0 m' (by rw [hnone]; exact ⟨rfl, hreg⟩)
  intro Jfail hJfail
  have collapseFail : ∀ (acc : List Val) (rem : Nat) (m' : Mem 64),
      acc.length + rem = poolRem →
      readAddLitsPure c.mv poolRem (prfBytes.drop idx0) = none →
      (Eq (prfBytes.At prf_ptr) ⋆
        (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
          int4Array c_ptr acc.reverse ⋆
          region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) ⋆ R) m' →
      Jfail [] m' := by
    intro acc rem m' hlen_rem hnone hm'
    have hm1 :
        ((word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
          (int4Array c_ptr acc.reverse ⋆
            region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem))) ⋆
          (Eq (prfBytes.At prf_ptr) ⋆ R)) m' := sep_ac hm'
    have hm2 :
        ((word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
          region c_ptr (4 * poolRem)) ⋆
          (Eq (prfBytes.At prf_ptr) ⋆ R)) m' := by
      refine sep_mono (sep_mono2 (fun _ h => h) fun f hf => ?_) hm1
      rw [← region_merge_eq (a := c_ptr) (n1 := 4 * acc.length) (n2 := 4 * rem) (n := 4 * poolRem) (by omega) (by omega)]
      exact sep_mono (fun _ g => by simpa using int4Array_to_region (by simp; omega) g) hf
    have hws' : (WorkState c poolUsed poolRem cur0 ptrs table PoolUsed ⋆ (Eq (prfBytes.At prf_ptr) ⋆ R)) m' :=
      workState_sep.mpr ⟨hsum, htbl, hpu, sep_cast hm2 (by dsimp only [c_ptr, wsFixed]; ac_rfl)⟩
    exact hJfail [] m' ⟨rfl, hnone, sep_ac (sep_mono (fun _ => WorkState.to_region) hws')⟩
  -- `@rd_loop(%cur, %wcur)`
  apply wp_loop (fun fuel as m' => ∃ (idx rem : Nat) (acc : List Val),
    (prfBytes.drop idx).length < fuel ∧
    idx ≤ prfBytes.length ∧
    acc.length + rem = poolRem ∧
    (∀ x ∈ acc, IsValidLit c.mv x) ∧
    as = [prf_ptr + BitVec.ofNat 64 idx, c_ptr + BitVec.ofNat 64 (4 * acc.length)] ∧
    readAddLitsPure c.mv poolRem (prfBytes.drop idx0) =
      readAddLitsAux fuel c.mv rem acc (prfBytes.drop idx) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
        int4Array c_ptr acc.reverse ⋆
        region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) ⋆ R) m')
  · rintro Jloop fuel as m' ⟨idx, rem, acc, hfuel_gt, hidx, hrem_sum, hacc_valid, rfl, hpure, hm'⟩ ih
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    let wcur : Val := c_ptr + BitVec.ofNat 64 (4 * acc.length)
    have hwcur_eq : wcur = c.pbase + BitVec.ofNat 64 (4 * (c.poolInts - rem)) := by
      grind
    wp_unfold
    refine ⟨fun hfull => ?_, fun hnfull => ?_⟩
    · have hrem0 : rem = 0 := (c.pcur_eq_plim_iff (by omega)).mp (hwcur_eq ▸ hfull)
      subst hrem0
      simp only [readAddLitsAux, beq_self_eq_true, ↓reduceIte] at hpure
      exact collapseFail acc 0 m' hrem_sum hpure hm'
    · have hrem_pos : 0 < rem := Nat.pos_of_ne_zero fun h0 => hnfull (by
        rw [show c_ptr + BitVec.ofNat 64 (4 * acc.length) = wcur from rfl, hwcur_eq]
        exact (c.pcur_eq_plim_iff (by omega)).mpr h0)
      have hrem_b : (rem == 0) = false := beq_false_of_ne (by omega)
      have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
          ((word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
            int4Array c_ptr acc.reverse ⋆
            region wcur (4 * rem)) ⋆ R)) m' :=
        sep_cast hm' (by dsimp only [wcur]; ac_rfl)
      refine readLeb128_spec hprf_fit hidx rfl rfl hm_prf
        (fun hleb_none => ?_)
        (fun u bs' hleb_some hu hlen_lt hbs' hidx_lt => ?_)
      · simp only [readAddLitsAux, hrem_b, Bool.false_eq_true, ↓reduceIte, hleb_none] at hpure
        exact collapseFail acc rem m' hrem_sum hpure hm'
      · let idx' := prfBytes.length - bs'.length
        have hidx'_le : idx' ≤ prfBytes.length := by omega
        wp_unfold
        refine (bv_eq_zero_branch (by omega : u < 2 ^ 64)
          (fun hu0 => ?_) (fun hu_ne0 => ?_))
        · subst hu0
          simp only [readAddLitsAux, hrem_b, Bool.false_eq_true, ↓reduceIte, hleb_some] at hpure
          obtain ⟨ok_z, hm1⟩ := region_pop_store_int4 0 hrem_pos (by omega)
            (sep_cast hm' (by dsimp only [wcur]; ac_rfl) :
              (region wcur (4 * rem) ⋆ (Eq (prfBytes.At prf_ptr) ⋆ word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
                wsFixed c ptrs PoolUsed ⋆ int4Array c_ptr acc.reverse ⋆ R)) m')
          refine ⟨ok_z, ?_⟩
          let clits := acc.reverse
          have hzt : ZeroTermInts c_ptr clits = (int4Array c_ptr clits ⋆ int4 wcur 0) := by
            rw [zeroTermInts_eq_append, List.length_reverse]
          have hm1_hdr :
              (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
                (ZeroTermInts c_ptr clits ⋆ region (wcur + 4) (4 * (rem - 1)) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆ wsFixed c ptrs PoolUsed ⋆ R))
                (storeMem m' .w wcur 0) :=
            hzt ▸ sep_cast hm1 (by dsimp only [clits]; ac_rfl)
          let cur2 : Val := prf_ptr + BitVec.ofNat 64 idx'
          obtain ⟨ok_p64, hm2⟩ := storel_word8Array (i := 8) (wcur + 4)
            (by simp [WorkCfg.hdrWords]) hm1_hdr
          refine ⟨ok_p64, ?_⟩
          obtain ⟨ok_p72, hm3⟩ := storel_word8Array (i := 9) cur2
            (by simp [WorkCfg.hdrWords]) hm2
          refine ⟨ok_p72, ?_⟩
          have hwcur2_eq :
              wcur + 4 = c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (clits.length + 1))) := by
            grind
          have hhdr_end :
              ((c.hdrWords c_ptr cur0).set 8 (wcur + 4)).set 9 cur2 =
                c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (clits.length + 1)))) cur2 := by
            rw [← hwcur2_eq]; rfl
          rw [hhdr_end] at hm3
          have hr_next :
              region (wcur + 4) (4 * (rem - 1)) =
                region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (clits.length + 1))))
                  (4 * (rem - 1)) :=
            congrArg (fun x => region x (4 * (rem - 1))) hwcur2_eq
          have hpu' : ∀ f, (PoolUsed ⋆ ZeroTermInts c_ptr clits) f →
              region c.pbase (4 * (poolUsed + (clits.length + 1))) f := by
            intro f hf
            have hr_zt : ∀ g, ZeroTermInts c_ptr clits g → region c_ptr (4 * (clits.length + 1)) g :=
              fun _ hg => zeroTermInts_to_region (by simp [clits]; omega) hg
            have heq_p : 4 * (poolUsed + (clits.length + 1)) = 4 * poolUsed + 4 * (clits.length + 1) := by
              omega
            rw [heq_p, region_split (by simp [clits]; omega)]
            exact sep_mono2 hpu hr_zt f hf
          have hws_done :
              (WorkState c (poolUsed + (clits.length + 1)) (rem - 1) cur2
                ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr clits) ⋆
                (Eq (prfBytes.At prf_ptr) ⋆ R)) _ :=
            workState_sep.mpr ⟨by simp [clits]; omega, TableRel.frame_right _ htbl, hpu',
              sep_cast hm3 (by dsimp only [wsFixed]; rw [hr_next]; ac_rfl)⟩
          have hm_done :
              (Eq (prfBytes.At prf_ptr) ⋆
                WorkState c (poolUsed + (clits.length + 1)) (rem - 1) cur2
                  ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr clits) ⋆ R) _ :=
            sep_cast hws_done (by ac_rfl)
          have hvalid_clits : ∀ x ∈ clits, IsValidLit c.mv x :=
            fun x hx => hacc_valid x (List.mem_reverse.mp hx)
          have hwcur_cptr : wcur = c_ptr ↔ acc.length = 0 := by
            grind
          grind
        · have hpure_step :
              readAddLitsAux (fuel' + 1) c.mv rem acc (prfBytes.drop idx) =
                (let v := u / 2
                 if v == 0 || c.mv < v then none
                 else readAddLitsAux fuel' c.mv (rem - 1) (decodeZigZag u :: acc) bs') := by
            cases u with
            | zero => exact absurd rfl hu_ne0
            | succ _ => simp only [readAddLitsAux, hrem_b, Bool.false_eq_true, ↓reduceIte, hleb_some]
          rw [hpure_step] at hpure
          rw [bv_shr_one (by omega : u < 2 ^ 64)]
          have hmv_lt64 : c.mv < 2 ^ 64 := by
            have := c.hmv; unfold dimacsBound at this; omega
          refine bv_eq_zero_branch (by omega : u / 2 < 2 ^ 64)
            (fun hv0 => ?_) (fun hv_ne0 => ?_)
          · grind
          · have hv_pos : 1 ≤ u / 2 := by omega
            have hv_ne0_b : ((u / 2) == 0) = false := beq_false_of_ne hv_ne0
            refine ult_branch hmv_lt64 (by omega : u / 2 < 2 ^ 64)
              (fun hmv_lt_v => ?_) (fun hnlt => ?_)
            · grind
            · have hv_le_mv : u / 2 ≤ c.mv := by omega
              have hv_le_b : decide (c.mv < u / 2) = false := decide_eq_false (by omega)
              simp only [hv_ne0_b, hv_le_b, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hpure
              rw [zigzag_eq hu]
              obtain ⟨ok_lit, hm1⟩ := region_pop_store_int4 (decodeZigZag u) hrem_pos (by omega)
                (sep_cast hm' (by dsimp only [wcur]; ac_rfl) :
                  (region wcur (4 * rem) ⋆ (Eq (prfBytes.At prf_ptr) ⋆ word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
                    wsFixed c ptrs PoolUsed ⋆ int4Array c_ptr acc.reverse ⋆ R)) m')
              refine ⟨ok_lit, ?_⟩
              have harr_snoc :
                  int4Array c_ptr (decodeZigZag u :: acc).reverse =
                    (int4Array c_ptr acc.reverse ⋆ int4 wcur (decodeZigZag u)) := by
                rw [List.reverse_cons, int4Array_append, List.length_reverse]
                simp [wcur, sep_emp]
              have hm1_next :
                  (Eq (prfBytes.At prf_ptr) ⋆
                    (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
                      int4Array c_ptr (decodeZigZag u :: acc).reverse ⋆
                      region (c_ptr + BitVec.ofNat 64 (4 * (decodeZigZag u :: acc).length))
                        (4 * (rem - 1))) ⋆ R)
                    (storeMem m' .w wcur (decodeZigZag u)) := by
                have hwcur_step :
                    wcur + 4 = c_ptr + BitVec.ofNat 64 (4 * (decodeZigZag u :: acc).length) := by
                  simp only [wcur, List.length_cons, ptr4]
                rw [hwcur_step] at hm1
                rw [harr_snoc]
                exact sep_cast hm1 (by ac_rfl)
              have hlit_valid := isValidLit_decodeZigZag hu hv_pos hv_le_mv c.hmv
              refine ih fuel' _ _ (by omega)
                ⟨idx', rem - 1, decodeZigZag u :: acc, ?_, by omega, by simp; omega, ?_,
                  ?_, ?_, hm1_next⟩
              · rw [← hbs']; omega
              · grind
              · simp only [List.length_cons, ptr4]; rfl
              · rwa [← hbs']
  · intro Jloop hJloop
    wp_unfold
    have hm_init :
        (Eq (prfBytes.At prf_ptr) ⋆
          (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
            int4Array c_ptr ([] : List Val).reverse ⋆
            region (c_ptr + BitVec.ofNat 64 (4 * ([] : List Val).length)) (4 * poolRem)) ⋆ R) m := by
      simp only [List.reverse_nil, int4Array_nil, List.length_nil, Nat.mul_zero, BitVec.add_zero]
      have hemp_r : (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆ emp) =
          (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed) := by simp [sep_emp]
      rw [hemp_r]
      exact sep_cast hm_u (by dsimp only [c_ptr, cur0, wsFixed]; ac_rfl)
    exact hJloop ((prfBytes.drop idx0).length + 1) _ _
      ⟨idx0, poolRem, [], by omega, hidx0, by simp, by simp,
        by simp [cur0, c_ptr], rfl, hm_init⟩

/-! ## 3. `assignLitChecked_spec`, `rupPhase1_spec`, `rupInner_spec`, and `lbRupCheck_correct` -/

private theorem assignBytes_getD {mv : Nat} (assign : Assignment) {lit : Val}
    (hlit : IsValidLit mv lit) :
    (assignBytes mv assign).getD (bvAbs lit).toNat 0 = assignByte assign (toLiteral lit).1 := by
  have hi : (bvAbs lit).toNat < mv + 1 := by have := hlit.2.2.1; omega
  have hi' : (bvAbs lit).toNat < (assignBytes mv assign).length := by simpa using hi
  simp only [List.getD, List.getElem?_eq_getElem hi', Option.getD_some,
    getElem_assignBytes mv assign hi, toLiteral]

theorem assignLitChecked_spec {Γ : Env} {Q : Post} {X : XPost} {fail : Cont}
    {vb tb tlim te wlit idx : Val} {mv : Nat}
    {assign : Assignment} {trail tf : List Val} {R : Mem 64 → Prop}
    {m : Mem 64} {k : Val → Expr Val Cont}
    (hwlit : IsValidLit mv wlit) (hidx : idx = bvAbs wlit)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb te assign trail tf (mv + 1) ⋆ R) m)
    (hfail : trail.length = mv + 1 → fail [] m)
    (hk : ∀ m' tf',
      trail.length ≠ mv + 1 →
      (PState mv vb tb (te + 4)
        (assign.insert (toLiteral wlit).1 (toLiteral wlit).2)
        (trail ++ [wlit]) tf' (mv + 1) ⋆ R) m' →
      wp Γ Q X (k (te + 4)) [] [] m') :
    wp Γ Q X (assignLitChecked fail vb tlim te wlit idx k) [] [] m := by
  obtain ⟨hte, hcov, htv, hlen, hm0⟩ := pstate_sep.mp hm
  unfold assignLitChecked
  subst hidx hte htlim
  wp_unfold
  refine ⟨fun hfull => ?_, fun hnfull => ?_⟩
  · grind
  · have hne_len : trail.length ≠ mv + 1 := by
      intro heq; apply hnfull; rw [heq]
    rcases tf with _ | ⟨t0, tf'⟩
    · simp at hlen; exact absurd hlen hne_len
    rw [show (BitVec.sshiftRight wlit 63 ||| 1) = bvSignByte wlit from rfl]
    have hi : (toLiteral wlit).1 < (assignBytes mv assign).length := by
      simp [toLiteral]; have := hwlit.2.2.1; omega
    rw [sep_assoc] at hm0
    obtain ⟨ok1, hm1⟩ := storeb_byte1Array (bvSignByte wlit) hi hm0
    rw [assignBytes_set_insert mv assign hwlit, sep_comm_l] at hm1
    obtain ⟨ok2, hm2⟩ := storew_int4Array (i := trail.length) wlit (by simp) hm1
    rw [show (trail ++ t0 :: tf').set trail.length wlit = (trail ++ [wlit]) ++ tf' by
      simp [List.set_append_right]] at hm2
    have ha : vb + bvAbs wlit = vb + BitVec.ofNat 64 (toLiteral wlit).1 := by
      simp [toLiteral]
    rw [ha]
    refine ⟨ok1, ok2, hk _ tf' hne_len
      (pstate_sep.mpr ⟨?_, trailCoversAssign_insert wlit hcov, ?_, ?_, sep_cast hm2 (by ac_rfl)⟩)⟩
    · grind
    · grind
    · simp at hlen ⊢; omega

theorem rupPhase1_spec {Γ : Env} {Q : Post} {X : XPost} {fail taut ph2 : Cont}
    {vb tb tlim c_ptr cur0 : Val} {mv : Nat} {clits tf0 : List Val}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hvalid : ∀ x ∈ clits, IsValidLit mv x)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb tb Assignment.empty [] tf0 (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m)
    (hfail : ∀ m' te assign trail tf,
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 = .fail →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' →
      fail [] m')
    (htaut : ∀ m' te assign trail tf,
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 = .taut →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' →
      taut [cur0, te] m')
    (hph2 : ∀ m' te assign trail tf,
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 =
        .ok (assignBytes mv assign) trail.length →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' →
      ph2 [cur0, te] m') :
    wp Γ Q X (rupPhase1 fail taut ph2 vb tlim c_ptr tb cur0) [] [] m := by
  unfold rupPhase1
  have h32 : ∀ x ∈ clits, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ clits, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  apply wp_loop (fun r as m' => ∃ (i : Nat) (te : Val) (assign : Assignment) (trail tf : List Val),
    as = [c_ptr + BitVec.ofNat 64 (4 * i), te] ∧
    i ≤ clits.length ∧ r = clits.length - i ∧
    (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' ∧
    rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 =
      rupPhase1Pure mv (clits.drop i) (assignBytes mv assign) trail.length)
  · rintro J r as m' ⟨i, te, assign, trail, tf, rfl, hi, rfl, hm', hpure⟩ ih
    wp_unfold
    obtain ⟨_, _, _, _, hm0⟩ := pstate_sep.mp hm'
    have hld := loadsw_zeroTerm hi h32 (by rw [sep_comm_l] at hm0; exact hm0)
    refine ⟨_, hld, fun hnz => ?_, fun hz => ?_⟩
    · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i)] at hnz
      have hlt := (zeroTermGet_ne_zero_iff hi hne0).mp hnz
      simp only [zeroTermGet, hlt, ↓reduceDIte]
      have hlit := hvalid clits[i] (List.getElem_mem hlt)
      rw [List.drop_eq_getElem_cons hlt] at hpure
      simp only [rupPhase1Pure, assignBytes_getD assign hlit] at hpure
      refine assignedLit_spec hlit (by rw [sep_assoc] at hm0; exact hm0) ?_
      wp_unfold
      refine ⟨fun hneg => ?_, fun hnneg => ?_⟩
      · simp only [hneg, ↓reduceIte] at hpure
        exact ih _ _ _ (by omega) ⟨i + 1, te, assign, trail, tf, by rw [ptr4], hlt, rfl, hm', hpure⟩
      · refine ⟨fun hpos => ?_, fun hnpos => ?_⟩
        · grind
        · rw [show (0 : Val) - clits[i] = -clits[i] by simp]
          refine assignLitChecked_spec (isValidLit_neg hlit) (bvAbs_neg hlit).symm htlim htfit hm'
            (fun hfull => ?_)
            (fun m'' tf' hne_len hm'' => ?_)
          · grind
          · have hfull_f : (trail.length == mv + 1) = false := beq_eq_false_iff_ne.mpr hne_len
            simp only [hnneg, hnpos, hfull_f, Bool.false_eq_true, ↓reduceIte] at hpure
            have hidx_neg : (bvAbs clits[i]).toNat = (toLiteral (-clits[i])).1 := by
              simp [toLiteral, bvAbs_neg hlit]
            rw [hidx_neg, assignBytes_set_insert mv assign (isValidLit_neg hlit)] at hpure
            wp_unfold
            exact ih _ _ _ (by omega)
              ⟨i + 1, te + 4, _, trail ++ [-clits[i]], tf', by rw [ptr4], hlt, rfl, hm'', by simpa using hpure⟩
    · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i), Classical.not_not] at hz
      obtain rfl := (zeroTermGet_eq_zero_iff hi hne0).mp hz
      simp only [List.drop_length, rupPhase1Pure] at hpure
      exact hph2 m' te assign trail tf hpure hm'
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, tb, Assignment.empty, [], tf0, by simp, Nat.zero_le _, rfl, hm,
      by simp [assignBytes_empty]⟩

theorem rupInner_spec {Γ : Env} {Q : Post} {X : XPost} {fail done : Cont}
    {vb tb tlim als te0 : Val} {mv : Nat} {alits : List Val}
    {curAssign : Assignment} {curTrail curTf : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hvalid : ∀ x ∈ alits, IsValidLit mv x)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb te0 curAssign curTrail curTf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m)
    (hfail : ∀ m' te assign trail tf,
      rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length = none →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' →
      fail [] m')
    (hdone : ∀ m' unit te assign trail tf,
      rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length =
        some (unit, assignBytes mv assign, trail.length) →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' →
      done [unit, te] m') :
    wp Γ Q X (rupInner fail done vb tlim als te0) [] [] m := by
  unfold rupInner
  have h32 : ∀ x ∈ alits, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ alits, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  apply wp_loop (fun r as m' => ∃ (i : Nat) (unit te : Val) (assign : Assignment) (trail tf : List Val),
    as = [als + BitVec.ofNat 64 (4 * i), unit, te] ∧
    i ≤ alits.length ∧ r = alits.length - i ∧
    (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' ∧
    rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length =
      rupInnerPure mv (alits.drop i) unit (assignBytes mv assign) trail.length)
  · rintro J r as m' ⟨i, unit, te, assign, trail, tf, rfl, hi, rfl, hm', hpure⟩ ih
    wp_unfold
    obtain ⟨_, _, _, _, hm0⟩ := pstate_sep.mp hm'
    have hld := loadsw_zeroTerm hi h32 (by rw [sep_comm_l] at hm0; exact hm0)
    refine ⟨_, hld, fun hnz => ?_, fun hz => ?_⟩
    · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i)] at hnz
      have hlt := (zeroTermGet_ne_zero_iff hi hne0).mp hnz
      simp only [zeroTermGet, hlt, ↓reduceDIte]
      have hlit := hvalid alits[i] (List.getElem_mem hlt)
      rw [List.drop_eq_getElem_cons hlt] at hpure
      simp only [rupInnerPure, assignBytes_getD assign hlit] at hpure
      refine assignedLit_spec hlit (by rw [sep_assoc] at hm0; exact hm0) ?_
      wp_unfold
      let val := evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]
      refine ⟨fun hneg => ?_, fun hnneg => ?_⟩
      · rw [show (0 : Val) - alits[i] = -alits[i] by simp]
        refine ⟨fun heq => ?_, fun hne => ?_⟩
        · grind
        · have hne_b : (unit == -alits[i]) = false := beq_eq_false_iff_ne.mpr hne
          simp only [hneg, hne_b, Bool.false_eq_true, ↓reduceIte] at hpure
          exact ih _ _ _ (by omega) ⟨i + 1, unit, te, assign, trail, tf, by rw [ptr4], hlt, rfl, hm', hpure⟩
      · simp only [hnneg, Bool.false_eq_true, ↓reduceIte] at hpure
        let stepUnit : Option (Val × List Val × Nat) :=
          if val == 0 then
            if trail.length == mv + 1 then none
            else
              rupInnerPure mv (alits.drop (i + 1)) alits[i]
                ((assignBytes mv assign).set (bvAbs alits[i]).toNat (bvSignByte alits[i]))
                (trail.length + 1)
          else
            rupInnerPure mv (alits.drop (i + 1)) alits[i] (assignBytes mv assign) trail.length
        apply wp_join (fun as m'' => as = [] ∧ m'' = m' ∧
          rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length = stepUnit)
        · rintro _ m_su ⟨rfl, hm_su, hpure_su⟩
          rw [hm_su]
          wp_unfold
          dsimp only [stepUnit, val] at hpure_su
          refine ⟨fun hvz => ?_, fun hnvz => ?_⟩
          · simp only [hvz, beq_self_eq_true, ↓reduceIte] at hpure_su
            refine assignLitChecked_spec hlit rfl htlim htfit hm'
              (fun hfull => ?_)
              (fun m'' tf' hne_len hm'' => ?_)
            · grind
            · have hfull_f : (trail.length == mv + 1) = false := beq_eq_false_iff_ne.mpr hne_len
              simp only [hfull_f, Bool.false_eq_true, ↓reduceIte] at hpure_su
              have hidx_pos : (bvAbs alits[i]).toNat = (toLiteral alits[i]).1 := rfl
              rw [hidx_pos, assignBytes_set_insert mv assign hlit] at hpure_su
              wp_unfold
              exact ih _ _ _ (by omega)
                ⟨i + 1, alits[i], te + 4, _, trail ++ [alits[i]], tf',
                  by rw [ptr4], hlt, rfl, hm'', by simpa using hpure_su⟩
          · have hvz_f : (val == 0) = false := beq_eq_false_iff_ne.mpr hnvz
            dsimp only [val] at hvz_f
            simp only [hvz_f, Bool.false_eq_true, ↓reduceIte] at hpure_su
            exact ih _ _ _ (by omega)
              ⟨i + 1, alits[i], te, assign, trail, tf, by rw [ptr4], hlt, rfl, hm', hpure_su⟩
        · intro Jsu hJsu
          wp_unfold
          refine ⟨fun htu => ?_, fun hntu => ?_⟩
          · have htu_b : (lo32 unit != 0) = true := bne_iff_ne.mpr htu
            grind
          · have hntu_b : (lo32 unit != 0) = false := by
              rw [Bool.eq_false_iff, ne_eq, bne_iff_ne]; exact hntu
            grind
    · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i), Classical.not_not] at hz
      obtain rfl := (zeroTermGet_eq_zero_iff hi hne0).mp hz
      simp only [List.drop_length, rupInnerPure] at hpure
      exact hdone m' unit te assign trail tf hpure hm'
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, 0, te0, curAssign, curTrail, curTf, by simp, Nat.zero_le _, rfl, hm, rfl⟩

private abbrev wsRupRest (c : WorkCfg) (pcur cur0 : Val) (ptrs : List Val)
    (PoolUsed : Mem 64 → Prop) (poolRem : Nat) : Mem 64 → Prop :=
  word8Array c.hdr (c.hdrWords pcur cur0) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆
  word8Array c.cb ptrs ⋆
  PoolUsed ⋆
  region pcur (4 * poolRem)

private theorem trail_to_tRaw_region (c : WorkCfg) {xs : List Val} (hx : xs.length = c.mv + 1)
    {f : Mem 64} (hf : int4Array c.tb xs f) : region c.tb c.tRaw f := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
  have htr : 4 * xs.length = c.tRaw := by unfold WorkCfg.tRaw; omega
  unfold WorkCfg.activeBytes WorkCfg.tRaw at *
  simpa [htr] using int4Array_to_region (by omega) hf

private theorem pstate_rupRest_to_region {c : WorkCfg} {poolUsed poolRem : Nat}
    {cur0 te : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {assign : Assignment} {trail tf : List Val} {m : Mem 64}
    (hsum : poolUsed + poolRem = c.poolInts)
    (htbl : TableRel c.mv c.cap ptrs table PoolUsed)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hm : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur0 ptrs PoolUsed poolRem) m) :
    region c.hdr c.activeBytes m := by
  obtain ⟨_, _, _, hlen, hm0⟩ := pstate_sep.mp hm
  obtain ⟨hplen, _, _⟩ := htbl
  have := c.fit_active
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hvb : c.mv + 1 ≤ c.vBytes := by unfold WorkCfg.vBytes; omega
  have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
  unfold WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  have hm_ord :
      (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
        byte1Array c.vb (assignBytes c.mv assign) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        int4Array c.tb (trail ++ tf) ⋆
        region c.tlim (c.tBytes - c.tRaw) ⋆
        word8Array c.cb ptrs ⋆
        PoolUsed ⋆
        region pcur (4 * poolRem)) m :=
    sep_cast hm0 (by dsimp only [pcur, wsRupRest]; ac_rfl)
  have hm1 : (region c.hdr 80 ⋆
      region c.vb (c.mv + 1) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      region c.tb c.tRaw ⋆
      region c.tlim (c.tBytes - c.tRaw) ⋆
      region c.cb (8 * c.cap) ⋆
      region c.pbase (4 * poolUsed) ⋆
      region pcur (4 * poolRem)) m :=
    sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ hf => by simpa [WorkCfg.hdrWords] using word8Array_to_region (by simp [WorkCfg.hdrWords]) hf)
      (fun _ hf => by simpa using byte1Array_to_region (by simp; omega) hf))
      (fun _ h => h))
      (fun _ hf => trail_to_tRaw_region c (by rw [List.length_append]; exact hlen) hf))
      (fun _ h => h))
      (fun _ hf => by simpa [hplen] using word8Array_to_region (by rw [hplen]; omega) hf))
      hpu) (fun _ h => h) m hm_ord
  exact workCfg_regions_to_activeBytes c hsum hm1

private abbrev wsRupTail (c : WorkCfg) (prf_ptr pcur cur0 : Val) (prfBytes : List UInt8)
    (ptrs : List Val) (poolRem : Nat) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  Eq (prfBytes.At prf_ptr) ⋆ word8Array c.hdr (c.hdrWords pcur cur0) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆ word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R

private theorem wsRup_focus {c : WorkCfg} {prf_ptr pcur cur0 ptr : Val} {prfBytes : List UInt8}
    {ptrs lits : List Val} {PoolUsed R_sub R : Mem 64 → Prop} {poolRem : Nat}
    {te : Val} {assign : Assignment} {trail tf : List Val} {m : Mem 64}
    (hpu : PoolUsed = (ZeroTermInts ptr lits ⋆ R_sub))
    (hm : (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m) :
    (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      (ZeroTermInts ptr lits ⋆ (R_sub ⋆ wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R))) m := by
  have hm' : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆ PoolUsed ⋆
      wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R) m := by
    dsimp only [wsRupRest, wsRupTail] at hm ⊢; exact sep_ac hm
  rw [hpu] at hm'
  exact sep_ac hm'

private theorem wsRup_unfocus {c : WorkCfg} {prf_ptr pcur cur0 ptr : Val} {prfBytes : List UInt8}
    {ptrs lits : List Val} {PoolUsed R_sub R : Mem 64 → Prop} {poolRem : Nat}
    {te : Val} {assign : Assignment} {trail tf : List Val} {m : Mem 64}
    (hpu : PoolUsed = (ZeroTermInts ptr lits ⋆ R_sub))
    (hm : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      (ZeroTermInts ptr lits ⋆ (R_sub ⋆ wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R))) m) :
    (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m := by
  have hm' : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆ (ZeroTermInts ptr lits ⋆ R_sub) ⋆
      wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R) m := sep_ac hm
  rw [← hpu] at hm'
  dsimp only [wsRupRest, wsRupTail] at hm' ⊢
  exact sep_ac hm'

private theorem wsRup_load_cb {c : WorkCfg} {prf_ptr pcur cur0 : Val} {prfBytes : List UInt8}
    {ptrs : List Val} {PoolUsed R : Mem 64 → Prop} {poolRem aid : Nat}
    {te : Val} {assign : Assignment} {trail tf : List Val} {m : Mem 64}
    (haid : aid < ptrs.length)
    (hm : (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m) :
    loadVal m .l .l true (c.cb + BitVec.ofNat 64 (8 * aid)) = some (ptrs[aid]'haid) := by
  dsimp only [wsRupRest] at hm
  have hm_cb : (word8Array c.cb ptrs ⋆
      (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        word8Array c.hdr (c.hdrWords pcur cur0) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        region c.tlim (c.tBytes - c.tRaw) ⋆ PoolUsed ⋆ region pcur (4 * poolRem) ⋆ R)) m := sep_ac hm
  exact loadl_word8Array haid hm_cb

theorem lbRupCheck_correct (Γ : Env) :
    ∀ args m Q X, lbRupCheckSpec args m Q X → Func.spec Γ lbRupCheck args m Q X := by
  rintro _ m Q X ⟨c, id, c_ptr, prf_ptr, prfBytes, idx0, poolUsed, poolRem, clits, ptrs,
    table, PoolUsed, R, rfl, hid_cap, hprf_fit, hidx0, hvalid_c, ⟨R_c, hpu_c⟩, hm, hQ⟩
  unfold lbRupCheck Func.spec
  have hm_ws0 :
      (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆
        (Eq (prfBytes.At prf_ptr) ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨hsum, htbl, hpu, hm_u⟩ := workState_sep.mp hm_ws0
  let pcur : Val := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let cur0 : Val := prf_ptr + BitVec.ofNat 64 idx0
  have hcap_fit : 8 * c.cap < 2 ^ 64 := by
    have := c.fit_active; unfold WorkCfg.activeBytes at this; omega
  have htfit : c.tb.toNat + 4 * (c.mv + 1) < 2 ^ 64 := by
    have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
    have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
    unfold WorkCfg.activeBytes WorkCfg.tRaw at *; omega
  have hm_hdr :
      (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
        (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
          region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆
          region c.tlim (c.tBytes - c.tRaw) ⋆
          word8Array c.cb ptrs ⋆
          PoolUsed ⋆
          region pcur (4 * poolRem) ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m :=
    sep_cast hm_u (by dsimp only [pcur, cur0]; ac_rfl)
  wp_unfold
  refine ⟨_, loadl_hdr 3 (by decide) hm_hdr rfl,
    _, loadl_hdr 4 (by decide) hm_hdr rfl,
    _, loadl_hdr 5 (by decide) hm_hdr rfl,
    _, loadl_hdr 6 (by decide) hm_hdr rfl,
    _, loadl_hdr 9 (by decide) hm_hdr rfl, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  -- `@fail()`
  apply wp_join (fun as m' => as = [] ∧
    rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
  · rintro _ m' ⟨rfl, hnone, hreg⟩
    wp_unfold
    grind
  intro Jfail hJfail
  have goFail : ∀ (te : Val) (assign : Assignment) (trail tf : List Val) (m' : Mem 64),
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none →
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m' →
      Jfail [] m' := by
    intro te assign trail tf m' hnone hm'
    have hm1 :
        ((PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
          wsRupRest c pcur cur0 ptrs PoolUsed poolRem) ⋆
          (Eq (prfBytes.At prf_ptr) ⋆ R)) m' :=
      sep_cast hm' (by ac_rfl)
    have hreg := sep_mono (fun _ => pstate_rupRest_to_region hsum htbl hpu) hm1
    exact hJfail [] m' ⟨rfl, hnone, sep_cast hreg (by ac_rfl)⟩
  -- `@consume(%ccur, %cte)`
  apply wp_join (fun as m' => ∃ (idx_c : Nat) (cte : Val) (assign : Assignment) (trail tf : List Val),
    as = [prf_ptr + BitVec.ofNat 64 idx_c, cte] ∧
    idx_c ≤ prfBytes.length ∧
    rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
      consumeHintsPure id table (prfBytes.drop idx_c) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      PState c.mv c.vb c.tb cte assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
  · rintro _ m_c ⟨idx_c, cte, assign_c, trail_c, tf_c, rfl, hidx_c, hpure_c, hm_c⟩
    wp_unfold
    -- `@cloop(%p)`
    apply wp_loop (fun fuel as m' => ∃ (idx : Nat),
      (prfBytes.drop idx).length < fuel ∧
      idx ≤ prfBytes.length ∧
      as = [prf_ptr + BitVec.ofNat 64 idx] ∧
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
        consumeHintsAux fuel id table (prfBytes.drop idx) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
    · rintro Jcloop fuel as m' ⟨idx, hfuel_gt, hidx, rfl, hpure, hm'⟩ ih
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      wp_unfold
      have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
          (PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
            wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R)) m' :=
        sep_cast hm' (by ac_rfl)
      refine readLeb128_spec hprf_fit hidx rfl rfl hm_prf
        (fun hleb_none => ?_)
        (fun u bs' hleb_some hu hlen_lt hbs' _ => ?_)
      · simp only [consumeHintsAux, hleb_none] at hpure
        exact goFail cte assign_c trail_c tf_c m' hpure hm'
      · let idx' := prfBytes.length - bs'.length
        have hidx'_le : idx' ≤ prfBytes.length := by omega
        wp_unfold
        refine bv_eq_zero_branch (by omega : u < 2 ^ 64)
          (fun hu0 => ?_) (fun hu_ne0 => ?_)
        · subst hu0
          simp only [consumeHintsAux, hleb_some] at hpure
          obtain ⟨hte_c, hcov_c, htv_c, hlen_c, hm_ps⟩ := pstate_sep.mp
            (sep_cast hm' (by ac_rfl) :
              (PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
                (Eq (prfBytes.At prf_ptr) ⋆ wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R)) m')
          have hmv_lt := c.hmv
          unfold dimacsBound at hmv_lt
          refine backtrack_spec hte_c htv_c (by omega) hcov_c hm_ps (fun m_bt hm_bt => ?_)
          wp_unfold
          have hm_bt_tr :
              (int4Array c.tb (trail_c ++ tf_c) ⋆
                (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
                  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                  region c.tlim (c.tBytes - c.tRaw) ⋆
                  word8Array c.cb ptrs ⋆ PoolUsed ⋆ region pcur (4 * poolRem) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆ R)) m_bt :=
            sep_cast hm_bt (by dsimp only [wsRupRest]; ac_rfl)
          have hm_bt_reg :
              (region c.tb c.tRaw ⋆
                (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
                  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                  region c.tlim (c.tBytes - c.tRaw) ⋆
                  word8Array c.cb ptrs ⋆ PoolUsed ⋆ region pcur (4 * poolRem) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆ R)) m_bt :=
            sep_mono
              (fun _ hf => trail_to_tRaw_region c (by rw [List.length_append]; exact hlen_c) hf)
              hm_bt_tr
          have hm_bt_hdr :
              (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
                  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                  region c.tb c.tRaw ⋆
                  region c.tlim (c.tBytes - c.tRaw) ⋆
                  word8Array c.cb ptrs ⋆ PoolUsed ⋆ region pcur (4 * poolRem) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆ R)) m_bt :=
            sep_cast hm_bt_reg (by ac_rfl)
          let p2 : Val := prf_ptr + BitVec.ofNat 64 idx'
          obtain ⟨ok_p72, hm_fin⟩ := storel_word8Array (i := 9) p2
            (by simp [WorkCfg.hdrWords]) hm_bt_hdr
          refine ⟨ok_p72, ?_⟩
          have hhdr_eq : (c.hdrWords pcur cur0).set 9 p2 = c.hdrWords pcur p2 := rfl
          rw [hhdr_eq] at hm_fin
          have hws_fin :
              (WorkState c poolUsed poolRem p2 ptrs table PoolUsed ⋆
                (Eq (prfBytes.At prf_ptr) ⋆ R))
                (storeMem m_bt .l (c.hdr + 72) p2) :=
            workState_sep.mpr ⟨hsum, htbl, hpu, sep_cast hm_fin (by dsimp only [pcur]; ac_rfl)⟩
          refine hQ 1 _ ?_
          rw [hpure]
          exact ⟨rfl, hbs', hidx'_le, sep_cast hws_fin (by ac_rfl)⟩
        · obtain ⟨u_pred, hu_succ⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
          rw [hu_succ] at hleb_some
          simp only [consumeHintsAux, hleb_some] at hpure
          rw [← hu_succ] at hpure hleb_some
          refine bv_odd_branch (by omega : u < 2 ^ 64)
            (fun hodd_b => ?_) (fun heven_b => ?_)
          · grind
          · simp only [heven_b, Bool.false_eq_true, ↓reduceIte] at hpure
            rw [bv_shr_one (by omega : u < 2 ^ 64)]
            let aid := u / 2
            refine ult_branch (by omega : u / 2 < 2 ^ 64) (by omega : id < 2 ^ 64)
              (fun haid_lt => ?_) (fun hnaid_lt => ?_)
            · have haid_cap : aid < c.cap := by omega
              simp only [haid_lt, ↓reduceIte] at hpure
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)]
              obtain ⟨hplen, htlen, hrel⟩ := htbl
              have hld_cb := wsRup_load_cb (hplen ▸ haid_cap) hm'
              refine ⟨_, hld_cb, fun hact => ?_, fun hnact => ?_⟩
              · have hspec_a := hrel aid haid_cap
                rw [List.getElem?_eq_getElem (htlen ▸ haid_cap)] at hpure
                cases ht_a : table[u / 2]'(htlen ▸ haid_cap) with
                | none => rw [ht_a] at hspec_a; exact absurd hspec_a hact
                | some alits =>
                  simp only [ht_a] at hpure
                  refine ih fuel' _ _ (by omega) ⟨idx', ?_, hidx'_le, rfl, ?_, hm'⟩
                  · rw [← hbs']; omega
                  · rwa [← hbs']
              · grind
            · grind
    · intro Jcloop hJcloop
      wp_unfold
      exact hJcloop ((prfBytes.drop idx_c).length + 1) _ _
        ⟨idx_c, by omega, hidx_c, rfl, hpure_c, hm_c⟩
  intro Jconsume hJconsume
  -- `@ph2(%hcur, %hte)`
  apply wp_join (fun as m' => ∃ (hte : Val) (assign : Assignment) (trail tf : List Val),
    as = [cur0, hte] ∧
    rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
      rupPhase2Aux ((prfBytes.drop idx0).length + 1) c.mv id table
        (assignBytes c.mv assign) trail.length (prfBytes.drop idx0) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      PState c.mv c.vb c.tb hte assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
  · rintro _ m_p2 ⟨hte, assign0, trail0, tf0_p2, rfl, hpure_p2, hm_p2⟩
    wp_unfold
    -- `@outer(%p, %t)`
    apply wp_loop (fun fuel as m' => ∃ (idx : Nat) (te : Val)
      (assign : Assignment) (trail tf : List Val),
      (prfBytes.drop idx).length < fuel ∧
      idx ≤ prfBytes.length ∧
      as = [prf_ptr + BitVec.ofNat 64 idx, te] ∧
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
        rupPhase2Aux fuel c.mv id table (assignBytes c.mv assign) trail.length
          (prfBytes.drop idx) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
    · rintro Jouter fuel as m' ⟨idx, te, assign, trail, tf, hfuel_gt, hidx, rfl, hpure, hm'⟩ ih
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      wp_unfold
      have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
          (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
            wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R)) m' :=
        sep_cast hm' (by ac_rfl)
      refine readLeb128_spec hprf_fit hidx rfl rfl hm_prf
        (fun hleb_none => ?_)
        (fun u bs' hleb_some hu hlen_lt hbs' _ => ?_)
      · simp only [rupPhase2Aux, hleb_none] at hpure
        exact goFail te assign trail tf m' hpure hm'
      · let idx' := prfBytes.length - bs'.length
        have hidx'_le : idx' ≤ prfBytes.length := by omega
        wp_unfold
        refine bv_eq_zero_branch (by omega : u < 2 ^ 64)
          (fun hu0 => ?_) (fun hu_ne0 => ?_)
        · subst hu0
          simp only [rupPhase2Aux, hleb_some] at hpure
          exact goFail te assign trail tf m' hpure hm'
        · obtain ⟨u_pred, hu_succ⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
          rw [hu_succ] at hleb_some
          simp only [rupPhase2Aux, hleb_some] at hpure
          rw [← hu_succ] at hpure hleb_some
          refine bv_odd_branch (by omega : u < 2 ^ 64)
            (fun hodd_b => ?_) (fun heven_b => ?_)
          · grind
          · simp only [heven_b, Bool.false_eq_true, ↓reduceIte] at hpure
            rw [bv_shr_one (by omega : u < 2 ^ 64)]
            let aid := u / 2
            refine ult_branch (by omega : u / 2 < 2 ^ 64) (by omega : id < 2 ^ 64)
              (fun haid_lt => ?_) (fun hnaid_lt => ?_)
            · have haid_cap : aid < c.cap := by omega
              simp only [haid_lt, ↓reduceIte] at hpure
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)]
              obtain ⟨hplen, htlen, hrel⟩ := htbl
              have hld_cb := wsRup_load_cb (hplen ▸ haid_cap) hm'
              refine ⟨_, hld_cb, fun hact => ?_, fun hnact => ?_⟩
              · have hspec_a := hrel aid haid_cap
                rw [List.getElem?_eq_getElem (htlen ▸ haid_cap)] at hpure
                cases ht_a : table[u / 2]'(htlen ▸ haid_cap) with
                | none => rw [ht_a] at hspec_a; exact absurd hspec_a hact
                | some alits =>
                  rw [ht_a] at hspec_a
                  simp only [ht_a] at hpure
                  obtain ⟨_, hvalid_a, R_a, hpu_a⟩ := hspec_a
                  -- `@idone(%unit, %t2)`
                  apply wp_join (fun as m'' => ∃ (unit t2 : Val)
                    (assign2 : Assignment) (trail2 tf2 : List Val),
                    as = [unit, t2] ∧
                    rupInnerPure c.mv alits 0 (assignBytes c.mv assign) trail.length =
                      some (unit, assignBytes c.mv assign2, trail2.length) ∧
                    (Eq (prfBytes.At prf_ptr) ⋆
                      PState c.mv c.vb c.tb t2 assign2 trail2 tf2 (c.mv + 1) ⋆
                      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m'')
                  · rintro _ m'' ⟨unit, t2, assign2, trail2, tf2, rfl, hinner_ok, hm''⟩
                    wp_unfold
                    simp only [hinner_ok] at hpure
                    refine ⟨fun htu => ?_, fun hntu => ?_⟩
                    · have htu_b : (lo32 unit != 0) = true := bne_iff_ne.mpr htu
                      simp only [htu_b, ↓reduceIte] at hpure
                      refine ih fuel' _ _ (by omega)
                        ⟨idx', t2, assign2, trail2, tf2, ?_, hidx'_le, rfl, ?_, hm''⟩
                      · rw [← hbs']; omega
                      · rwa [← hbs']
                    · have hntu_b : (lo32 unit != 0) = false := by
                        rw [Bool.eq_false_iff, ne_eq, bne_iff_ne]; exact hntu
                      grind
                  · intro Jidone hJidone
                    refine rupInner_spec hvalid_a rfl htfit (wsRup_focus hpu_a hm')
                      (fun m'' t2 assign2 trail2 tf2 hinner_none hm''_in => ?_)
                      (fun m'' unit t2 assign2 trail2 tf2 hinner_ok hm''_in => ?_)
                    · simp only [hinner_none] at hpure
                      exact goFail t2 assign2 trail2 tf2 m'' hpure (wsRup_unfocus hpu_a hm''_in)
                    · exact hJidone _ m'' ⟨unit, t2, assign2, trail2, tf2, rfl, hinner_ok,
                        wsRup_unfocus hpu_a hm''_in⟩
              · grind
            · grind
    · intro Jouter hJouter
      wp_unfold
      exact hJouter ((prfBytes.drop idx0).length + 1) _ _
        ⟨idx0, hte, assign0, trail0, tf0_p2, by omega, hidx0, rfl, hpure_p2, hm_p2⟩
  intro Jph2 hJph2
  -- Entry: convert `region c.tb c.tRaw` to `int4Array c.tb tf0` and invoke `rupPhase1_spec`
  have hm_tb :
      (region c.tb (4 * (c.mv + 1)) ⋆
        (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
          wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    have : c.tRaw = 4 * (c.mv + 1) := rfl
    rw [← this]
    exact sep_cast hm_u (by dsimp only [pcur, cur0, wsRupRest]; ac_rfl)
  obtain ⟨f_t, f_o, hu_t, hd_t, hf_t, hf_o⟩ := hm_tb
  have hmv_lt := c.hmv
  unfold dimacsBound at hmv_lt
  obtain ⟨tf0, htf0_len, htf0_arr⟩ := region_to_int4Array (c.mv + 1) (by omega) hf_t
  have hm_arr :
      ((byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆ int4Array c.tb ([] ++ tf0)) ⋆
        (wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    have h1 : (int4Array c.tb tf0 ⋆
        (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
          wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m :=
      ⟨f_t, f_o, hu_t, hd_t, htf0_arr, hf_o⟩
    simpa only [List.nil_append] using sep_cast h1 (by ac_rfl)
  have hm_ps0 :
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb c.tb Assignment.empty [] tf0 (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m :=
    sep_ac (pstate_sep.mpr ⟨by simp, trailCoversAssign_empty c.mv, by simp, by simp [htf0_len], hm_arr⟩ :
      (PState c.mv c.vb c.tb c.tb Assignment.empty [] tf0 (c.mv + 1) ⋆
        (wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m)
  refine rupPhase1_spec hvalid_c rfl htfit (wsRup_focus hpu_c hm_ps0)
    (fun m' te assign trail tf hp1_fail hm' => ?_)
    (fun m' te assign trail tf hp1_taut hm' => ?_)
    (fun m' te assign trail tf hp1_ok hm' => ?_)
  · exact goFail te assign trail tf m' (by unfold rupCheckPure; rw [hp1_fail])
      (wsRup_unfocus hpu_c hm')
  · exact hJconsume _ m' ⟨idx0, te, assign, trail, tf, rfl, hidx0,
      by unfold rupCheckPure; rw [hp1_taut], wsRup_unfocus hpu_c hm'⟩
  · exact hJph2 _ m' ⟨te, assign, trail, tf, rfl,
      by unfold rupCheckPure; rw [hp1_ok], wsRup_unfocus hpu_c hm'⟩

/-! ## 4. Pure RUP soundness (`rupCheckPure_sound`) -/

private theorem cnf_append_left {f1 f2 g : CNF Nat} (h : CNF.Entails f1 f2) :
    CNF.Entails (f1 ++ g) (f2 ++ g) :=
  CNF.entails_append_of_entails (CNF.entails_trans CNF.append_entails_left h)
    CNF.append_entails_right

private theorem unsat_of_entailsClause_all_falsified {F : CNF Nat}
    {initAssign curAssign : Assignment} {c : CNF.Clause Nat}
    (hc : CNF.EntailsClause F c)
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, curAssign.get? lit.1 = some !lit.2) :
    CNF.Unsat (F ++ initAssign.toCNF) := by
  have hF_add : CNF.Entails F (F.add c) := CNF.entails_add_iff.mpr ⟨CNF.entails_refl F, hc⟩
  have hadd_F : CNF.Entails (F.add c) F := (CNF.entails_add_iff.mp (CNF.entails_refl (F.add c))).1
  have hent' : CNF.Entails (F.add c ++ initAssign.toCNF) (F.add c ++ curAssign.toCNF) :=
    CNF.entails_trans (cnf_append_left hadd_F) (CNF.entails_trans hent (cnf_append_left hF_add))
  exact CNF.unsat_of_entails_unsat
    (unsat_of_all_falsified (CNF.mem_add.mpr (Or.inl rfl)) hent' hall)
    (cnf_append_left hF_add)

private theorem entails_insert_of_entailsClause_unit_prop {F : CNF Nat}
    {initAssign curAssign : Assignment} {c : CNF.Clause Nat} {unit : Literal Nat}
    (hc : CNF.EntailsClause F c)
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, lit = unit ∨ curAssign.get? lit.1 = some !lit.2) :
    CNF.Entails (F ++ initAssign.toCNF) (F ++ (curAssign.insert unit.1 unit.2).toCNF) := by
  have hF_add : CNF.Entails F (F.add c) := CNF.entails_add_iff.mpr ⟨CNF.entails_refl F, hc⟩
  have hadd_F : CNF.Entails (F.add c) F := (CNF.entails_add_iff.mp (CNF.entails_refl (F.add c))).1
  have hent' : CNF.Entails (F.add c ++ initAssign.toCNF) (F.add c ++ curAssign.toCNF) :=
    CNF.entails_trans (cnf_append_left hadd_F) (CNF.entails_trans hent (cnf_append_left hF_add))
  exact CNF.entails_trans (cnf_append_left hF_add)
    (CNF.entails_trans (entails_insert_of_unit_prop (CNF.mem_add.mpr (Or.inl rfl)) hent' hall)
      (cnf_append_left hadd_F))

private theorem rupPhase1Pure_loop_sound {mv : Nat} {clits : List Val}
    (hvalid : ∀ x ∈ clits, IsValidLit mv x) :
    ∀ (rem i : Nat) (assign : Assignment) (trailLen : Nat),
      i ≤ clits.length →
      rem = clits.length - i →
      (∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral ↔ assign.get? x.1 = some !x.2) →
      (rupPhase1Pure mv (clits.drop i) (assignBytes mv assign) trailLen = .taut →
        ∃ atom pol, (atom, pol) ∈ toClause clits ∧ (atom, !pol) ∈ toClause clits) ∧
      (∀ vals' trailLen',
        rupPhase1Pure mv (clits.drop i) (assignBytes mv assign) trailLen = .ok vals' trailLen' →
        ∃ assign', vals' = assignBytes mv assign' ∧
          ∀ x : Literal Nat, x ∈ toClause clits ↔ assign'.get? x.1 = some !x.2)
  | 0, i, assign, trailLen, hi, hrem, hinv => by
    obtain rfl : i = clits.length := by omega
    simp only [List.drop_length, rupPhase1Pure]
    refine ⟨fun h => (nomatch h), fun vals' trailLen' h => ?_⟩
    injection h with hvals _
    subst hvals
    rw [List.take_length] at hinv
    exact ⟨assign, rfl, fun x => by rw [← CNF.Clause.mem_literals_iff, literals_toClause, hinv x]⟩
  | rem + 1, i, assign, trailLen, _, hrem, hinv => by
    have hlt : i < clits.length := by omega
    have hlit : IsValidLit mv clits[i] := hvalid clits[i] (List.getElem_mem hlt)
    have hcases := evalAssignedLit_cases assign hlit
    rw [List.drop_eq_getElem_cons hlt]
    simp only [rupPhase1Pure, assignBytes_getD assign hlit]
    cases hneg : (evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i]).slt 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hpos : (0 : Val).slt (evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i])
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hfull : (trailLen == mv + 1)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hidx_neg : (bvAbs clits[i]).toNat = (toLiteral (-clits[i])).1 := by
            simp [toLiteral, bvAbs_neg hlit]
          rw [hidx_neg, assignBytes_set_insert mv assign (isValidLit_neg hlit)]
          have hun := (hcases.2.2 ⟨hneg, hpos⟩).1
          exact rupPhase1Pure_loop_sound hvalid rem (i + 1)
            (assign.insert (toLiteral (-clits[i])).1 (toLiteral (-clits[i])).2)
            (trailLen + 1) hlt (by omega) (phase1_step_insert hlt hlit hinv hun)
        · grind
      · simp only [↓reduceIte]
        exact ⟨fun _ => phase1_step_tautology hlt hinv (hcases.2.1 ⟨hneg, hpos⟩),
          fun _ _ h => (nomatch h)⟩
    · simp only [↓reduceIte]
      exact rupPhase1Pure_loop_sound hvalid rem (i + 1) assign trailLen hlt (by omega)
        (phase1_step_already_falsified hlt hinv (hcases.1 hneg))

private def PureInnerSt (mv : Nat) (alits : List Val) (curAssign : Assignment)
    (i : Nat) (unit : Val) (assign : Assignment) : Prop :=
  (unit = 0 ∧ assign = curAssign ∧
    ∀ x : Literal Nat, x ∈ (alits.take i).map toLiteral → curAssign.get? x.1 = some !x.2) ∨
  (unit ≠ 0 ∧ IsValidLit mv unit ∧ assign.get? (toLiteral unit).1 = some (toLiteral unit).2 ∧
    ((curAssign.get? (toLiteral unit).1 = none ∧
      assign = curAssign.insert (toLiteral unit).1 (toLiteral unit).2) ∨ assign = curAssign) ∧
    ∀ x : Literal Nat, x ∈ (alits.take i).map toLiteral →
      x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2)

private theorem lo32_bne_zero_of_valid {mv : Nat} {unit : Val}
    (hu : unit ≠ 0) (huv : IsValidLit mv unit) :
    (lo32 unit != 0) = true :=
  bne_iff_ne.mpr ((truthy_iff unit huv.1).mpr hu)

private theorem rupInnerPure_loop_sound {mv : Nat} {alits : List Val} {F : CNF Nat}
    {initAssign curAssign : Assignment}
    (hvalid : ∀ x ∈ alits, IsValidLit mv x)
    (hcl : CNF.EntailsClause F (toClause alits))
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF)) :
    ∀ (rem i : Nat) (unit : Val) (assign : Assignment) (trailLen : Nat)
      (unit' : Val) (vals' : List Val) (trailLen' : Nat),
      i ≤ alits.length →
      rem = alits.length - i →
      PureInnerSt mv alits curAssign i unit assign →
      rupInnerPure mv (alits.drop i) unit (assignBytes mv assign) trailLen =
        some (unit', vals', trailLen') →
      ((lo32 unit' != 0) = false ∧ CNF.Unsat (F ++ initAssign.toCNF)) ∨
      ((lo32 unit' != 0) = true ∧ ∃ assign', vals' = assignBytes mv assign' ∧
        CNF.Entails (F ++ initAssign.toCNF) (F ++ assign'.toCNF))
  | 0, i, unit, assign, trailLen, unit', vals', trailLen', hi, hrem, hst, hres => by
    obtain rfl : i = alits.length := by omega
    simp only [List.drop_length, rupInnerPure] at hres
    cases hres
    rw [PureInnerSt, List.take_length] at hst
    rcases hst with ⟨rfl, rfl, hall⟩ | ⟨hu, huv, _, hrel, hinv⟩
    · refine Or.inl ⟨by decide, unsat_of_entailsClause_all_falsified hcl hent fun x hx => ?_⟩
      rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx
      exact hall x hx
    · refine Or.inr ⟨lo32_bne_zero_of_valid hu huv, assign, rfl, ?_⟩
      rcases hrel with ⟨_, rfl⟩ | rfl
      · exact entails_insert_of_entailsClause_unit_prop hcl hent fun x hx => by
          rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx
          exact hinv x hx
      · exact hent
  | rem + 1, i, unit, assign, trailLen, unit', vals', trailLen', _, hrem, hst, hres => by
    have hlt : i < alits.length := by omega
    have hlit : IsValidLit mv alits[i] := hvalid alits[i] (List.getElem_mem hlt)
    have hcases := evalAssignedLit_cases assign hlit
    rw [List.drop_eq_getElem_cons hlt] at hres
    simp only [rupInnerPure, assignBytes_getD assign hlit] at hres
    cases hneg : (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]).slt 0
    · simp only [hneg, Bool.false_eq_true, ↓reduceIte] at hres
      let stepUnit : Option (Val × List Val × Nat) :=
        if evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] == 0 then
          if trailLen == mv + 1 then none
          else
            rupInnerPure mv (alits.drop (i + 1)) alits[i]
              ((assignBytes mv assign).set (bvAbs alits[i]).toNat (bvSignByte alits[i]))
              (trailLen + 1)
        else
          rupInnerPure mv (alits.drop (i + 1)) alits[i] (assignBytes mv assign) trailLen
      have hsu : (unit = 0 ∨ unit = alits[i]) ∧ stepUnit = some (unit', vals', trailLen') := by
        rcases hst with ⟨rfl, _⟩ | ⟨hu, huv, _⟩
        · grind
        · rw [lo32_bne_zero_of_valid hu huv] at hres
          grind
      obtain ⟨hu_cases, hres_su⟩ := hsu
      dsimp only [stepUnit] at hres_su
      cases hvz : (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] == 0)
      · have hnv0 : evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] ≠ 0 :=
          beq_eq_false_iff_ne.mp hvz
        simp only [hvz, Bool.false_eq_true, ↓reduceIte] at hres_su
        have hpos : (0 : Val).slt
            (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]) = true := by
          grind
        have hsat := hcases.2.1 ⟨hneg, hpos⟩
        have hst' : PureInnerSt mv alits curAssign (i + 1) alits[i] assign := by
          rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨hu, huv, hus, hrel, hinv⟩
          · exact Or.inr ⟨hlit.2.1, hlit, hsat, Or.inr rfl, phase2_inner_new_unit hlt hinv⟩
          · rcases hu_cases with rfl | rfl
            · exact absurd rfl hu
            · exact Or.inr ⟨hu, huv, hus, hrel, phase2_inner_dup_unit hlt rfl hinv⟩
        exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) alits[i] assign trailLen
          unit' vals' trailLen' hlt (by omega) hst' hres_su
      · have hv0 : evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] = 0 :=
          eq_of_beq hvz
        have hun : assign.get? (toLiteral alits[i]).1 = none :=
          (hcases.2.2 ⟨hneg, by rw [hv0]; decide⟩).1
        simp only [hvz, ↓reduceIte] at hres_su
        cases hfull : (trailLen == mv + 1)
        · simp only [hfull, Bool.false_eq_true, ↓reduceIte] at hres_su
          rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨hu, _, hus, _, _⟩
          · have hidx_pos : (bvAbs alits[i]).toNat = (toLiteral alits[i]).1 := rfl
            rw [hidx_pos, assignBytes_set_insert mv assign hlit] at hres_su
            have hst' : PureInnerSt mv alits assign (i + 1) alits[i]
                (assign.insert (toLiteral alits[i]).1 (toLiteral alits[i]).2) :=
              Or.inr ⟨hlit.2.1, hlit, Assignment.get?_insert_of_eq rfl,
                Or.inl ⟨hun, rfl⟩, phase2_inner_new_unit hlt hinv⟩
            exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) alits[i]
              (assign.insert (toLiteral alits[i]).1 (toLiteral alits[i]).2)
              (trailLen + 1) unit' vals' trailLen' hlt (by omega) hst' hres_su
          · grind
        · simp [hfull] at hres_su
    · have hfals := hcases.1 hneg
      simp only [hneg, ↓reduceIte] at hres
      cases heq : (unit == -alits[i])
      · have hne : unit ≠ -alits[i] := beq_eq_false_iff_ne.mp heq
        simp only [heq, Bool.false_eq_true, ↓reduceIte] at hres
        have hst' : PureInnerSt mv alits curAssign (i + 1) unit assign := by
          rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨hu, huv, hus, hrel, hinv⟩
          · exact Or.inl ⟨rfl, rfl, phase2_inner_falsified_unit0 hlt hinv hfals⟩
          · exact Or.inr ⟨hu, huv, hus, hrel,
              phase2_inner_falsified_unit_ne0 hlt hlit hus hrel hinv hfals hne⟩
        exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) unit assign trailLen
          unit' vals' trailLen' hlt (by omega) hst' hres
      · simp [heq] at hres

private theorem rupPhase2Aux_sound {mv id : Nat} {table : List (Option (List Val))} {F : CNF Nat}
    {initAssign : Assignment}
    (htable : ∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
      (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits)) :
    ∀ (fuel : Nat) (curAssign : Assignment) (trailLen : Nat) (bs bs_out : List UInt8),
      CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF) →
      rupPhase2Aux fuel mv id table (assignBytes mv curAssign) trailLen bs = some bs_out →
      CNF.Unsat (F ++ initAssign.toCNF)
  | 0, _, _, _, _, _, hp2 => nomatch hp2
  | fuel + 1, curAssign, trailLen, bs, bs_out, hent, hp2 => by
    cases hleb : readLeb128Pure bs with
    | none => simp only [rupPhase2Aux, hleb] at hp2; nomatch hp2
    | some p =>
      rcases p with ⟨u, bs'⟩
      cases u with
      | zero => simp only [rupPhase2Aux, hleb] at hp2; nomatch hp2
      | succ u_pred =>
        simp only [rupPhase2Aux, hleb] at hp2
        cases hodd : ((u_pred + 1) % 2 != 0)
        · rw [hodd] at hp2
          simp only [Bool.false_eq_true, ↓reduceIte] at hp2
          by_cases haid : (u_pred + 1) / 2 < id
          · simp only [haid, ↓reduceIte] at hp2
            cases htbl : table[(u_pred + 1) / 2]? with
            | none => simp only [htbl] at hp2; nomatch hp2
            | some opt =>
              cases opt with
              | none => simp only [htbl] at hp2; nomatch hp2
              | some alits =>
                simp only [htbl] at hp2
                obtain ⟨halits_valid, halits_ent⟩ := htable ((u_pred + 1) / 2) haid alits htbl
                cases hinner : rupInnerPure mv alits 0 (assignBytes mv curAssign) trailLen with
                | none => simp only [hinner] at hp2; nomatch hp2
                | some res =>
                  rcases res with ⟨unit, vals', trailLen'⟩
                  simp only [hinner] at hp2
                  have hsound := rupInnerPure_loop_sound halits_valid halits_ent hent
                    alits.length 0 0 curAssign trailLen unit vals' trailLen'
                    (Nat.zero_le _) (by simp) (Or.inl ⟨rfl, rfl, by simp⟩)
                    (by simpa using hinner)
                  rcases hsound with ⟨_, hunsat⟩ | ⟨hu_t, assign', rfl, hent'⟩
                  · exact hunsat
                  · simp only [hu_t, ↓reduceIte] at hp2
                    exact rupPhase2Aux_sound htable fuel assign' trailLen' bs' bs_out hent' hp2
          · simp [haid] at hp2
        · rw [hodd] at hp2; nomatch hp2

theorem rupCheckPure_sound {mv id : Nat} {clits : List Val}
    {table : List (Option (List Val))} {bs bs' : List UInt8} {F : CNF Nat}
    (hmv : mv < dimacsBound)
    (hclits : ∀ x ∈ clits, IsValidLit mv x)
    (htable : ∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
      (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits))
    (hrup : rupCheckPure mv id clits table bs = some bs') :
    CNF.EntailsClause F (toClause clits) := by
  let _ := hmv
  unfold rupCheckPure at hrup
  have he : List.replicate (mv + 1) (0 : Val) = assignBytes mv Assignment.empty :=
    (assignBytes_empty mv).symm
  rw [he] at hrup
  have hp1_sound := rupPhase1Pure_loop_sound hclits clits.length 0 Assignment.empty 0
    (Nat.zero_le _) (by simp) (by simp)
  rw [List.drop_zero] at hp1_sound
  cases hp1 : rupPhase1Pure mv clits (assignBytes mv Assignment.empty) 0 with
  | fail => rw [hp1] at hrup; nomatch hrup
  | taut => exact entailsClause_of_tautology (hp1_sound.1 hp1)
  | ok vals trailLen =>
    rw [hp1] at hrup
    dsimp only at hrup
    obtain ⟨initAssign, rfl, hiff⟩ := hp1_sound.2 vals trailLen hp1
    exact entailsClause_of_unsat_of_iff_falsified hiff
      (rupPhase2Aux_sound htable (bs.length + 1) initAssign trailLen bs bs'
        (CNF.entails_refl _) hrup)

end LeanQbe.LratBytes
