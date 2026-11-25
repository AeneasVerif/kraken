module

public import LeanQbe.T.Examples.LratBytesSpec
import Kraken.SeparationTactics
import all Kraken.Separation
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Logic.ProofKit

/-!
# `lbReadAddLits` and `lbRupCheck`: correctness and pure RUP soundness in `LeanQbe.T`

Self-contained typed-IR proofs of:
1. `lbReadAddLits_correct` (zig-zag LEB128 literal decoding).
2. Propagation-state helpers (`PState`, `assignedLit_pstate`, `store_assignLit_pstate`,
   `backtrack_spec`) and `rupPhase1_spec` / `rupInner_spec` / `lbRupCheck_correct`.
3. Pure RUP soundness (`rupCheckPure_sound`, via `InnerSt` and Kraken's `LratTrimRupProof`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.ProofKit
open LeanQbe.T.C0HeadStep

@[local bv_c0] private theorem bv_c0_list_length_cons {α : Type _} (x : α) (xs : List α) :
    (x :: xs).length = xs.length + 1 := rfl
@[local bv_c0] private theorem bv_c0_list_length_set {α : Type _} (xs : List α) (i : Nat) (v : α) :
    (xs.set i v).length = xs.length := List.length_set
@[local bv_c0] private theorem bv_c0_hdrWords_length (c : WorkCfg) (pcur cur : BitVec 64) :
    (c.hdrWords pcur cur).length = 10 := rfl
@[local bv_c0] private theorem bv_c0_dimacsBound : dimacsBound = 2 ^ 28 := rfl

@[local c0_load] private theorem c0_load_word8Array_zero {a : BitVec 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (word8Array a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i64 a = some (xs[0]'hi) := by
  simpa using load_word8Array (i := 0) hi h

@[local c0_load] private theorem c0_load_word8Array_off {a off : BitVec 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (h : (word8Array a xs ⋆ R) m)
    (hdiv : off.toNat % 8 = 0) (hi : off.toNat / 8 < xs.length) :
    loadVal m i64 (a + off) = some (xs[off.toNat / 8]'hi) := by
  have heq : BitVec.ofNat 64 (8 * (off.toNat / 8)) = off := by c0_bv_omega
  simpa [heq] using load_word8Array (i := off.toNat / 8) hi h

@[local c0_store] private theorem c0_store_word8Array_off {a off : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (word8Array a xs ⋆ R) m) (hdiv : off.toNat % 8 = 0) (hi : off.toNat / 8 < xs.length) :
    storeOk m i64 (a + off) ∧
      (word8Array a (xs.set (off.toNat / 8) v) ⋆ R) (storeMem m i64 (a + off) v) := by
  have heq : BitVec.ofNat 64 (8 * (off.toNat / 8)) = off := by c0_bv_omega
  simpa [heq] using store_word8Array (i := off.toNat / 8) v hi h

/-! ## 1. Zig-zag decoding and `lbReadAddLits_correct` -/

private theorem zigzag_eq {u : Nat} (_hu : u < 2 ^ 28) :
    let v : BitVec 64 := BitVec.ofNat 64 (u / 2)
    let mask : BitVec 64 := 0 - (BitVec.ofNat 64 u &&& 1)
    (v ^^^ mask) - mask = decodeZigZag u := by
  dsimp only [decodeZigZag]
  rw [show (0 : BitVec 64) - (BitVec.ofNat 64 u &&& 1) = if u % 2 == 1 then -1 else 0 by grind,
    negif]

private structure RdLoopSt where
  fuel : Nat
  idx : Nat
  rem : Nat
  acc : List (BitVec 64)

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
  c0_hsteps_nogrp
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero,
    BitVec.reduceToNat, Nat.reduceDiv]
  refine wp_join0 (fun m' => readAddLitsPure c.mv poolRem (prfBytes.drop idx0) = none ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
    (fun _ m' ⟨hnone, hreg⟩ => by c0_hstraight; exact hQ 0 m' (by rw [hnone]; exact ⟨rfl, hreg⟩)) ?_
  intro Jfail hJfail
  have collapseFail : ∀ (acc : List (BitVec 64)) (rem : Nat) (m' : Mem 64),
      acc.length + rem = poolRem → readAddLitsPure c.mv poolRem (prfBytes.drop idx0) = none →
      (Eq (prfBytes.At prf_ptr) ⋆ (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
        wsFixed c ptrs PoolUsed ⋆ int4Array c_ptr acc.reverse ⋆
        region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) ⋆ R) m' → Jfail () m' :=
    fun acc rem m' hlen_rem hnone hm' =>
      hJfail m' ⟨hnone, wsFixed_fail_collapse c htbl.1 (by omega) hpu hm'⟩
  refine wp_while_state (fun st : RdLoopSt =>
      (prf_ptr + BitVec.ofNat 64 st.idx, c_ptr + BitVec.ofNat 64 (4 * st.acc.length), ()))
    (fun st => st.fuel)
    (fun st m' => (prfBytes.drop st.idx).length < st.fuel ∧ st.idx ≤ prfBytes.length ∧
      st.acc.length + st.rem = poolRem ∧ (∀ x ∈ st.acc, IsValidLit c.mv x) ∧
      readAddLitsPure c.mv poolRem (prfBytes.drop idx0) =
        readAddLitsAux st.fuel c.mv st.rem st.acc (prfBytes.drop st.idx) ∧
      (Eq (prfBytes.At prf_ptr) ⋆ (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
        wsFixed c ptrs PoolUsed ⋆ int4Array c_ptr st.acc.reverse ⋆
        region (c_ptr + BitVec.ofNat 64 (4 * st.acc.length)) (4 * st.rem)) ⋆ R) m')
    (fun Jloop hJloop => by
      wp_unfold
      have hm_init : (Eq (prfBytes.At prf_ptr) ⋆ (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
          wsFixed c ptrs PoolUsed ⋆ int4Array c_ptr ([] : List (BitVec 64)).reverse ⋆
          region (c_ptr + BitVec.ofNat 64 (4 * ([] : List (BitVec 64)).length))
            (4 * poolRem)) ⋆ R) m := by
        simp only [List.reverse_nil, int4Array_nil, List.length_nil, Nat.mul_zero,
          BitVec.add_zero, sep_emp]
        unfold wsFixed; exact sep_cast hm_u (by dsimp only [c_ptr, cur0]; ac_rfl)
      simpa only [List.length_nil, Nat.mul_zero, BitVec.add_zero] using
        hJloop ⟨(prfBytes.drop idx0).length + 1, idx0, poolRem, []⟩ m
          ⟨by dsimp; omega, hidx0, by simp, by simp, rfl, hm_init⟩)
    (fun Jloop ⟨fuel, idx, rem, acc⟩ m' ⟨hfuel_gt, hidx, hrem_sum, hacc_valid, hpure, hm'⟩ ih => by
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by dsimp at hfuel_gt; omega⟩
      let wcur : BitVec 64 := c_ptr + BitVec.ofNat 64 (4 * acc.length)
      have hwcur_eq : wcur = c.pbase + BitVec.ofNat 64 (4 * (c.poolInts - rem)) := by grind
      dsimp only [Blocks.get_here] at *; wp_unfold
      refine ⟨fun hfull => ?_, fun hnfull => ?_⟩
      · obtain rfl : rem = 0 := (c.pcur_eq_plim_iff (by omega)).mp (hwcur_eq ▸ hfull)
        rw [readAddLitsAux] at hpure; simp only [beq_self_eq_true, ↓reduceIte] at hpure
        exact collapseFail acc 0 m' hrem_sum hpure hm'
      · have hrem_pos : 0 < rem := Nat.pos_of_ne_zero fun h0 => hnfull (by
          rw [show c_ptr + BitVec.ofNat 64 (4 * acc.length) = wcur from rfl, hwcur_eq]
          exact (c.pcur_eq_plim_iff (by omega)).mpr h0)
        have hrem_b : (rem == 0) = false := beq_false_of_ne (by omega)
        refine readLeb128_spec hprf_fit hidx rfl rfl (by ecancel)
          (fun hleb_none => by
            rw [readAddLitsAux, hleb_none] at hpure
            simp only [hrem_b, Bool.false_eq_true, ↓reduceIte] at hpure
            exact collapseFail acc rem m' hrem_sum hpure hm')
          fun u bs' hleb_some hu _ hbs' _ => ?_
        let idx' := prfBytes.length - bs'.length
        have hidx'_le : idx' ≤ prfBytes.length := by omega
        wp_unfold
        refine bv_eq_zero_branch (by omega : u < 2 ^ 64) (fun hu0 => ?_) (fun hu_ne0 => ?_)
        · subst hu0; rw [readAddLitsAux, hleb_some] at hpure
          simp only [hrem_b, Bool.false_eq_true, ↓reduceIte] at hpure
          have hfa := c.fit_active; unfold WorkCfg.activeBytes at hfa
          obtain ⟨ok_z, hpu', hm1_hdr⟩ := wsFixed_finish_clause hrem_pos (by omega) hpu hm'
          let cur2 : BitVec 64 := prf_ptr + BitVec.ofNat 64 idx'
          let pcur' : BitVec 64 := c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (acc.length + 1)))
          have hwcur2_eq : wcur + 4 = pcur' := by dsimp [wcur, c_ptr, pcur']; grind
          obtain ⟨ok_p64, hm2⟩ := store_word8Array (i := 8) (wcur + 4)
            (by simp [WorkCfg.hdrWords]) hm1_hdr
          obtain ⟨ok_p72, hm3⟩ := store_word8Array (i := 9) cur2 (by simp [WorkCfg.hdrWords]) hm2
          refine ⟨ok_z, ok_p64, ok_p72, ?_⟩
          rw [show ((c.hdrWords c_ptr cur0).set 8 (wcur + 4)).set 9 cur2 =
              c.hdrWords pcur' cur2 by rw [hwcur2_eq]; rfl] at hm3
          have hws_done : (WorkState c (poolUsed + (acc.reverse.length + 1)) (rem - 1) cur2
              ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr acc.reverse) ⋆
              (Eq (prfBytes.At prf_ptr) ⋆ R)) _ :=
            workState_sep.mpr ⟨by simp; omega, TableRel.frame_right _ htbl, by simpa using hpu', by
              unfold wsFixed at hm3; exact sep_cast hm3
                (by dsimp only [c_ptr, pcur']; simp only [List.length_reverse]; ac_rfl)⟩
          have hvalid_clits : ∀ x ∈ acc.reverse, IsValidLit c.mv x :=
            fun x hx => hacc_valid x (List.mem_reverse.mp hx)
          have hm_done : (Eq (prfBytes.At prf_ptr) ⋆
              WorkState c (poolUsed + (acc.reverse.length + 1)) (rem - 1) cur2
                ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr acc.reverse) ⋆ R) _ := sep_ac hws_done
          have hwcur_cptr : wcur = c_ptr ↔ acc.length = 0 := by grind
          grind
        · have hpure_step : readAddLitsAux (fuel' + 1) c.mv rem acc (prfBytes.drop idx) =
              (let v := u / 2
               if v == 0 || c.mv < v then none
               else readAddLitsAux fuel' c.mv (rem - 1) (decodeZigZag u :: acc) bs') := by
            cases u with
            | zero => exact absurd rfl hu_ne0
            | succ _ =>
              rw [readAddLitsAux, hleb_some]; simp only [hrem_b, Bool.false_eq_true, ↓reduceIte]
          rw [hpure_step] at hpure; rw [bv_shr_one (by omega : u < 2 ^ 64)]
          have hmv_lt64 : c.mv < 2 ^ 64 := by have := c.hmv; unfold dimacsBound at this; omega
          refine bv_eq_zero_branch (by omega : u / 2 < 2 ^ 64)
            (fun _ => by grind) (fun hv_ne0 => ?_)
          refine ult_branch hmv_lt64 (by omega : u / 2 < 2 ^ 64)
            (fun _ => by grind) (fun hnlt => ?_)
          simp only [beq_false_of_ne hv_ne0, decide_eq_false hnlt, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte] at hpure
          rw [zigzag_eq hu]
          have hfa := c.fit_active; unfold WorkCfg.activeBytes at hfa
          obtain ⟨ok_lit, hm1_next⟩ := wsFixed_push_lit (decodeZigZag u) hrem_pos (by omega) hm'
          have hlit_valid := isValidLit_decodeZigZag hu (by omega) (by omega) c.hmv
          refine ⟨ok_lit, ?_⟩
          simpa only [List.length_cons, ptr4] using
            ih ⟨fuel', idx', rem - 1, decodeZigZag u :: acc⟩ _ (by dsimp; omega)
              ⟨by dsimp; rw [← hbs']; omega, by dsimp; omega, by simp; omega, by grind,
                by rwa [← hbs'], hm1_next⟩)

/-! ## 2. Propagation state (`PState`), inline helpers, and `InnerSt` -/

private theorem assignBytes_getD {mv : Nat} (assign : Assignment) {lit : BitVec 64}
    (hlit : IsValidLit mv lit) :
    (assignBytes mv assign).getD (bvAbs lit).toNat 0 = assignByte assign (toLiteral lit).1 := by
  have hi : (bvAbs lit).toNat < mv + 1 := by have := hlit.2.2.1; omega
  have hi' : (bvAbs lit).toNat < (assignBytes mv assign).length := by simpa using hi
  simp [List.getD, List.getElem?_eq_getElem hi', getElem_assignBytes mv assign hi, toLiteral]

private theorem backtrack_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vb tb te : BitVec 64} {mv : Nat} {assign : Assignment} {trail tf : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} {kc : Expr Val Cont rs}
    (hte : te = tb + BitVec.ofNat 64 (4 * trail.length))
    (hvalid : ∀ t ∈ trail, IsValidLit mv t) (hlen : 4 * trail.length < 2 ^ 64)
    (hcov : TrailCoversAssign mv assign trail)
    (hm : ((byte1Array vb (assignBytes mv assign) ⋆ int4Array tb (trail ++ tf)) ⋆ R) m)
    (hk : ∀ m',
      ((byte1Array vb (assignBytes mv Assignment.empty) ⋆ int4Array tb (trail ++ tf)) ⋆ R) m' →
      wp Γ Q X kc m') :
    wp Γ Q X (backtrack vb tb te kc) m := by
  unfold backtrack
  refine wp_while_state (fun i => (tb + BitVec.ofNat 64 (4 * i), ()))
    (fun i => trail.length - i)
    (fun i m' => i ≤ trail.length ∧
      ((byte1Array vb (clearTrailBytes (assignBytes mv assign) (trail.take i)) ⋆
        int4Array tb (trail ++ tf)) ⋆ R) m')
    (fun J hJ => by wp_unfold; simpa using hJ 0 m ⟨Nat.zero_le _, by simpa using hm⟩)
    (fun J i m' ⟨hi, hm'⟩ ih => by
      dsimp only [Blocks.get_here] at *; wp_unfold
      refine ⟨fun heq => ?_, fun hne => ?_⟩
      · obtain rfl : i = trail.length := by grind
        rw [List.take_length, clearTrailBytes_assignBytes hcov] at hm'; exact hk m' hm'
      · have hlt : i < trail.length := by grind
        have hv := hvalid trail[i] (List.getElem_mem hlt)
        rw [sep_assoc, sep_comm_l] at hm'
        have hld := load_int4Array (i := i) (by simp; omega) hm'
        rw [List.getElem_append_left hlt] at hld
        refine ⟨_, hld, ?_⟩
        rw [sext32 _ hv.1, sar63, negif,
          show (if trail[i].slt 0 = true then -trail[i] else trail[i]) =
            BitVec.ofNat 64 (bvAbs trail[i]).toNat from (ofNat_bvAbs_toNat _).symm]
        rw [sep_comm_l] at hm'
        have hidx : (bvAbs trail[i]).toNat <
            (clearTrailBytes (assignBytes mv assign) (trail.take i)).length := by
          simp; have := hv.2.2.1; omega
        have ⟨ok, hm1⟩ := store_byte1Array 0#8 hidx hm'
        rw [show (0#8).setWidth 64 = (0 : BitVec 64) from rfl,
          clearTrailBytes_take_succ _ trail hlt] at hm1
        exact ⟨ok, by rw [ptr4]; exact ih (i + 1) _ (by omega) ⟨hlt, by rwa [sep_assoc]⟩⟩)

/-- Values array represents `assign`, trail array holds `trail ++ tf` (length `N`),
and `te` points just after `trail`. -/
private def PState (mv : Nat) (vb tb te : BitVec 64) (assign : Assignment)
    (trail tf : List (BitVec 64)) (N : Nat) : Mem 64 → Prop := fun m =>
  te = tb + BitVec.ofNat 64 (4 * trail.length) ∧ TrailCoversAssign mv assign trail ∧
    (∀ t ∈ trail, IsValidLit mv t) ∧ trail.length + tf.length = N ∧
    (byte1Array vb (assignBytes mv assign) ⋆ int4Array tb (trail ++ tf)) m

private theorem pstate_sep {mv : Nat} {vb tb te : BitVec 64} {assign : Assignment}
    {trail tf : List (BitVec 64)} {N : Nat} {F : Mem 64 → Prop} {m : Mem 64} :
    (PState mv vb tb te assign trail tf N ⋆ F) m ↔
      te = tb + BitVec.ofNat 64 (4 * trail.length) ∧ TrailCoversAssign mv assign trail ∧
      (∀ t ∈ trail, IsValidLit mv t) ∧ trail.length + tf.length = N ∧
      ((byte1Array vb (assignBytes mv assign) ⋆ int4Array tb (trail ++ tf)) ⋆ F) m := by
  unfold PState; simp only [sep_pure_l]

private theorem assignedLit_pstate {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vb tb te lit : BitVec 64} {mv N : Nat} {assign : Assignment}
    {trail tf : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {k : BitVec 64 → BitVec 64 → Expr Val Cont rs} (hlit : IsValidLit mv lit)
    (hm : (PState mv vb tb te assign trail tf N ⋆ R) m)
    (hk : wp Γ Q X (k (bvAbs lit) (evalAssignedLit (assignByte assign (toLiteral lit).1) lit)) m) :
    wp Γ Q X (assignedLit vb lit k) m := by
  have hm' := (pstate_sep.1 hm).2.2.2.2; rw [sep_assoc] at hm'
  unfold assignedLit; wp_unfold; simp only [sar63, negif]
  have hi' : (bvAbs lit).toNat < mv + 1 := by have := hlit.2.2.1; omega
  have hld : loadVal m i8 (vb + bvAbs lit) =
      some ((assignByte assign (toLiteral lit).1).setWidth 8) := by
    have hld' := load_byte1Array (by simpa using hi') hm'
    rw [ofNat_bvAbs_toNat] at hld'
    simpa [getElem_assignBytes mv assign hi', toLiteral] using hld'
  refine ⟨_, hld, ?_⟩; rw [sext8 _ (isInt8_assignByte _ _)]; exact hk

private theorem store_assignLit_pstate {mv N : Nat} {vb tb te wlit : BitVec 64}
    {assign : Assignment} {trail tf : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hwlit : IsValidLit mv wlit)
    (hm : (PState mv vb tb te assign trail tf N ⋆ R) m) (hcap : 1 ≤ tf.length) :
    storeOk m i8 (vb + bvAbs wlit) ∧
    storeOk (storeMem m i8 (vb + bvAbs wlit) ((bvSignByte wlit).setWidth 8)) i32 te ∧
    ∃ tf', tf'.length + 1 = tf.length ∧
      (PState mv vb tb (te + 4) (assign.insert (toLiteral wlit).1 (toLiteral wlit).2)
        (trail ++ [wlit]) tf' N ⋆ R)
        (storeMem (storeMem m i8 (vb + bvAbs wlit) ((bvSignByte wlit).setWidth 8)) i32 te
          (wlit.setWidth 32)) := by
  obtain ⟨hte, hcov, htv, hlen, hm0⟩ := pstate_sep.1 hm
  rcases tf with _ | ⟨t0, tf'⟩; · simp at hcap
  subst hte
  have hi : (toLiteral wlit).1 < (assignBytes mv assign).length := by
    simp [toLiteral]; have := hwlit.2.2.1; omega
  rw [sep_assoc] at hm0
  have ⟨ok1, hm1⟩ := store_byte1Array64 (bvSignByte wlit) hi hm0
  rw [assignBytes_set_insert mv assign hwlit, sep_comm_l] at hm1
  have ⟨ok2, hm2⟩ := store_int4Array64 (i := trail.length) wlit (by simp) hm1
  rw [show (trail ++ t0 :: tf').set trail.length wlit = (trail ++ [wlit]) ++ tf' by
    simp [List.set_append_right]] at hm2
  rw [show vb + bvAbs wlit = vb + BitVec.ofNat 64 (toLiteral wlit).1 by simp [toLiteral]]
  refine ⟨ok1, ok2, tf', rfl, pstate_sep.2 ⟨by grind, trailCoversAssign_insert wlit hcov,
    by grind, by simp at hlen ⊢; omega, sep_cast hm2 (by ac_rfl)⟩⟩

private def InnerSt (mv : Nat) (clits : List (BitVec 64)) (curAssign : Assignment) (i : Nat)
    (unit : BitVec 64) (assign : Assignment) : Prop :=
  (unit = 0 ∧ assign = curAssign ∧
      ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral → curAssign.get? x.1 = some !x.2) ∨
  (unit ≠ 0 ∧ IsValidLit mv unit ∧ assign.get? (toLiteral unit).1 = some (toLiteral unit).2 ∧
      ((curAssign.get? (toLiteral unit).1 = none ∧
        assign = curAssign.insert (toLiteral unit).1 (toLiteral unit).2) ∨ assign = curAssign) ∧
      ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral →
        x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2)

private theorem innerSt_step_falsified {mv : Nat} {clits : List (BitVec 64)}
    {curAssign : Assignment} {i : Nat} {unit : BitVec 64} {assign : Assignment}
    (hlt : i < clits.length) (hlit : IsValidLit mv clits[i])
    (hst : InnerSt mv clits curAssign i unit assign)
    (hfals : assign.get? (toLiteral clits[i]).1 = some !(toLiteral clits[i]).2)
    (hne : unit ≠ -clits[i]) : InnerSt mv clits curAssign (i + 1) unit assign := by
  rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨hu, huv, hus, hrel, hinv⟩
  · exact Or.inl ⟨rfl, rfl, phase2_inner_falsified_unit0 hlt hinv hfals⟩
  · exact Or.inr ⟨hu, huv, hus, hrel,
      phase2_inner_falsified_unit_ne0 hlt hlit hus hrel hinv hfals hne⟩

private theorem innerSt_step_unassigned {mv : Nat} {clits : List (BitVec 64)}
    {curAssign : Assignment} {i : Nat} {unit : BitVec 64} {assign : Assignment}
    (hlt : i < clits.length) (hlit : IsValidLit mv clits[i])
    (hst : InnerSt mv clits curAssign i unit assign)
    (hu : unit = 0 ∨ unit = clits[i]) (hun : assign.get? (toLiteral clits[i]).1 = none) :
    unit = 0 ∧ assign = curAssign ∧
      InnerSt mv clits curAssign (i + 1) clits[i]
        (curAssign.insert (toLiteral clits[i]).1 (toLiteral clits[i]).2) := by
  rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨_, _, hus, _, _⟩
  · exact ⟨rfl, rfl, Or.inr ⟨hlit.2.1, hlit, Assignment.get?_insert_of_eq rfl,
      Or.inl ⟨hun, rfl⟩, phase2_inner_new_unit hlt hinv⟩⟩
  · grind

private theorem innerSt_step_satisfied {mv : Nat} {clits : List (BitVec 64)}
    {curAssign : Assignment} {i : Nat} {unit : BitVec 64} {assign : Assignment}
    (hlt : i < clits.length) (hlit : IsValidLit mv clits[i])
    (hst : InnerSt mv clits curAssign i unit assign) (hu : unit = 0 ∨ unit = clits[i])
    (hsat : assign.get? (toLiteral clits[i]).1 = some (toLiteral clits[i]).2) :
    InnerSt mv clits curAssign (i + 1) clits[i] assign := by
  rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨hu', huv, hus, hrel, hinv⟩
  · exact Or.inr ⟨hlit.2.1, hlit, hsat, Or.inr rfl, phase2_inner_new_unit hlt hinv⟩
  · rcases hu with rfl | rfl
    · exact absurd rfl hu'
    · exact Or.inr ⟨hu', huv, hus, hrel, phase2_inner_dup_unit hlt rfl hinv⟩

/-! ## 3. `assignLitChecked_spec`, `rupPhase1_spec`, `rupInner_spec`, and `lbRupCheck_correct` -/

private theorem assignLitChecked_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fail : Cont []} {vb tb tlim te wlit idx : BitVec 64} {mv : Nat}
    {assign : Assignment} {trail tf : List (BitVec 64)} {R : Mem 64 → Prop}
    {m : Mem 64} {k : BitVec 64 → Expr Val Cont rs}
    (hwlit : IsValidLit mv wlit) (hidx : idx = bvAbs wlit)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb te assign trail tf (mv + 1) ⋆ R) m)
    (hfail : trail.length = mv + 1 → fail () m)
    (hk : ∀ m' tf', trail.length ≠ mv + 1 →
      (PState mv vb tb (te + 4) (assign.insert (toLiteral wlit).1 (toLiteral wlit).2)
        (trail ++ [wlit]) tf' (mv + 1) ⋆ R) m' → wp Γ Q X (k (te + 4)) m') :
    wp Γ Q X (assignLitChecked fail vb tlim te wlit idx k) m := by
  obtain ⟨hte, _, _, hlen, _⟩ := pstate_sep.mp hm
  unfold assignLitChecked; subst hidx htlim; wp_unfold
  refine ⟨fun _ => by grind, fun hnfull => ?_⟩
  have hne_len : trail.length ≠ mv + 1 := fun heq => hnfull (by rw [hte, heq])
  rw [show (BitVec.sshiftRight wlit 63 ||| 1) = bvSignByte wlit from rfl]
  obtain ⟨ok1, ok2, tf', _, hm'⟩ := store_assignLit_pstate hwlit hm (by omega)
  exact ⟨ok1, ok2, hk _ tf' hne_len hm'⟩

private structure Phase1St where
  i : Nat
  te : BitVec 64
  assign : Assignment
  trail : List (BitVec 64)
  tf : List (BitVec 64)

private theorem rupPhase1_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fail : Cont []} {taut ph2 : Cont [i64, i64]}
    {vb tb tlim c_ptr cur0 : BitVec 64} {mv : Nat} {clits tf0 : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hvalid : ∀ x ∈ clits, IsValidLit mv x)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1))) (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb tb Assignment.empty [] tf0 (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m)
    (hfail : ∀ m' te assign trail tf,
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 = .fail →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' →
      fail () m')
    (htaut : ∀ m' te assign trail tf,
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 = .taut →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' →
      taut (cur0, te, ()) m')
    (hph2 : ∀ m' te assign trail tf,
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 =
        .ok (assignBytes mv assign) trail.length →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' →
      ph2 (cur0, te, ()) m') :
    wp Γ Q X (rupPhase1 fail taut ph2 vb tlim c_ptr tb cur0) m := by
  unfold rupPhase1
  have h32 : ∀ x ∈ clits, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ clits, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  refine wp_while_state (fun st : Phase1St => (c_ptr + BitVec.ofNat 64 (4 * st.i), st.te, ()))
    (fun st => clits.length - st.i)
    (fun st m' => st.i ≤ clits.length ∧
      (PState mv vb tb st.te st.assign st.trail st.tf (mv + 1) ⋆
        (ZeroTermInts c_ptr clits ⋆ R)) m' ∧
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 =
        rupPhase1Pure mv (clits.drop st.i) (assignBytes mv st.assign) st.trail.length)
    (fun J hJ => by
      wp_unfold; simpa only [Nat.mul_zero, BitVec.add_zero] using
        hJ ⟨0, tb, Assignment.empty, [], tf0⟩ m
          ⟨Nat.zero_le _, by simpa using hm, by simp [assignBytes_empty]⟩)
    (fun J ⟨i, te, assign, trail, tf⟩ m' ⟨hi, hm', hpure⟩ ih => by
      dsimp only [Blocks.get_here] at *; wp_unfold
      refine zeroTerm_jnz_step hi h32 hne0 (by ecancel) (fun hlt => ?_) (fun heq => ?_)
      · have hlit := hvalid clits[i] (List.getElem_mem hlt)
        rw [sext32 _ hlit.1, List.drop_eq_getElem_cons hlt] at *; rw [rupPhase1Pure] at hpure
        dsimp only at hpure; rw [assignBytes_getD assign hlit] at hpure
        refine assignedLit_pstate hlit hm' ?_; wp_unfold
        refine ⟨fun hneg => ?_, fun hnneg => ⟨fun _ => by grind, fun hnpos => ?_⟩⟩
        · simp only [hneg, ↓reduceIte] at hpure
          simpa only [ptr4] using
            ih ⟨i + 1, te, assign, trail, tf⟩ m' (by dsimp; omega) ⟨hlt, hm', hpure⟩
        · rw [show (0 : BitVec 64) - clits[i] = -clits[i] by simp]
          refine assignLitChecked_spec (isValidLit_neg hlit) (bvAbs_neg hlit).symm htlim htfit hm'
            (fun _ => by grind) (fun m'' tf' hne_len hm'' => ?_)
          simp only [hnneg, hnpos, beq_eq_false_iff_ne.mpr hne_len, Bool.false_eq_true, ↓reduceIte]
            at hpure
          rw [show (bvAbs clits[i]).toNat = (toLiteral (-clits[i])).1
              from by simp [toLiteral, bvAbs_neg hlit],
            assignBytes_set_insert mv assign (isValidLit_neg hlit)] at hpure
          wp_unfold; simpa only [ptr4] using
            ih ⟨i + 1, te + 4, _, trail ++ [-clits[i]], tf'⟩ m'' (by dsimp; omega)
              ⟨hlt, hm'', by simpa using hpure⟩
      · subst heq; rw [List.drop_length, rupPhase1Pure] at hpure
        exact hph2 m' te assign trail tf hpure hm')

private structure InnerLoopSt where
  i : Nat
  unit : BitVec 64
  te : BitVec 64
  assign : Assignment
  trail : List (BitVec 64)
  tf : List (BitVec 64)

private theorem rupInner_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fail : Cont []} {done : Cont [i64, i64]}
    {vb tb tlim als te0 : BitVec 64} {mv : Nat} {alits : List (BitVec 64)}
    {curAssign : Assignment} {curTrail curTf : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hvalid : ∀ x ∈ alits, IsValidLit mv x) (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb te0 curAssign curTrail curTf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m)
    (hfail : ∀ m' te assign trail tf,
      rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length = none →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' →
      fail () m')
    (hdone : ∀ m' unit te assign trail tf,
      rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length =
        some (unit, assignBytes mv assign, trail.length) →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' →
      done (unit, te, ()) m') :
    wp Γ Q X (rupInner fail done vb tlim als te0) m := by
  unfold rupInner
  have h32 : ∀ x ∈ alits, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ alits, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  refine wp_while_state (fun st : InnerLoopSt =>
      (als + BitVec.ofNat 64 (4 * st.i), st.unit, st.te, ()))
    (fun st => alits.length - st.i)
    (fun st m' => st.i ≤ alits.length ∧
      (PState mv vb tb st.te st.assign st.trail st.tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' ∧
      rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length =
        rupInnerPure mv (alits.drop st.i) st.unit (assignBytes mv st.assign) st.trail.length)
    (fun J hJ => by
      wp_unfold; simpa only [Nat.mul_zero, BitVec.add_zero] using
        hJ ⟨0, 0, te0, curAssign, curTrail, curTf⟩ m ⟨Nat.zero_le _, by simpa using hm, rfl⟩)
    (fun J ⟨i, unit, te, assign, trail, tf⟩ m' ⟨hi, hm', hpure⟩ ih => by
      dsimp only [Blocks.get_here] at *; wp_unfold
      refine zeroTerm_jnz_step hi h32 hne0 (by ecancel) (fun hlt => ?_) (fun heq => ?_)
      · have hlit := hvalid alits[i] (List.getElem_mem hlt)
        rw [sext32 _ hlit.1, List.drop_eq_getElem_cons hlt] at *; rw [rupInnerPure] at hpure
        dsimp only at hpure; rw [assignBytes_getD assign hlit] at hpure
        refine assignedLit_pstate hlit hm' ?_; wp_unfold
        let val := evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]
        refine ⟨fun hneg => ?_, fun hnneg => ?_⟩
        · rw [show (0 : BitVec 64) - alits[i] = -alits[i] by simp]
          refine ⟨fun _ => by grind, fun hne => ?_⟩
          simp only [hneg, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte] at hpure
          simpa only [ptr4] using
            ih ⟨i + 1, unit, te, assign, trail, tf⟩ m' (by dsimp; omega) ⟨hlt, hm', hpure⟩
        · simp only [hnneg, Bool.false_eq_true, ↓reduceIte] at hpure
          let stepUnit : Option (BitVec 64 × List (BitVec 64) × Nat) :=
            if val == 0 then
              if trail.length == mv + 1 then none
              else rupInnerPure mv (alits.drop (i + 1)) alits[i]
                ((assignBytes mv assign).set (bvAbs alits[i]).toNat (bvSignByte alits[i]))
                (trail.length + 1)
            else rupInnerPure mv (alits.drop (i + 1)) alits[i] (assignBytes mv assign) trail.length
          refine wp_join0 (fun m'' => m'' = m' ∧
            rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length = stepUnit)
            (fun _ m'' ⟨hm'', hpure_su⟩ => by
              subst m''; wp_unfold; dsimp only [stepUnit, val] at hpure_su
              refine ⟨fun hvz => ?_, fun hnvz => ?_⟩
              · simp only [hvz, beq_self_eq_true, ↓reduceIte] at hpure_su
                refine assignLitChecked_spec hlit rfl htlim htfit hm'
                  (fun _ => by grind) (fun m'' tf' hne_len hm'' => ?_)
                simp only [beq_eq_false_iff_ne.mpr hne_len, Bool.false_eq_true, ↓reduceIte]
                  at hpure_su
                have hidx_pos : (bvAbs alits[i]).toNat = (toLiteral alits[i]).1 := rfl
                rw [hidx_pos, assignBytes_set_insert mv assign hlit] at hpure_su
                wp_unfold; simpa only [ptr4] using
                  ih ⟨i + 1, alits[i], te + 4, _, trail ++ [alits[i]], tf'⟩ m'' (by dsimp; omega)
                    ⟨hlt, hm'', by simpa using hpure_su⟩
              · have hvz_f : (val == 0) = false := beq_eq_false_iff_ne.mpr hnvz
                dsimp only [val] at hvz_f
                simp only [hvz_f, Bool.false_eq_true, ↓reduceIte] at hpure_su
                simpa only [ptr4] using
                  ih ⟨i + 1, alits[i], te, assign, trail, tf⟩ m' (by dsimp; omega)
                    ⟨hlt, hm', hpure_su⟩) ?_
          intro Jsu hJsu; wp_unfold
          refine ⟨fun htu => by have : (unit != 0) = true := bne_iff_ne.mpr htu; grind,
            fun hntu => by have : (unit != 0) = false := bne_eq_false_iff_eq.mpr hntu; grind⟩
      · subst heq; rw [List.drop_length, rupInnerPure] at hpure
        exact hdone m' unit te assign trail tf hpure hm')

private abbrev wsRupRest (c : WorkCfg) (pcur cur0 : BitVec 64) (ptrs : List (BitVec 64))
    (PoolUsed : Mem 64 → Prop) (poolRem : Nat) : Mem 64 → Prop :=
  word8Array c.hdr (c.hdrWords pcur cur0) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆ word8Array c.cb ptrs ⋆ PoolUsed ⋆ region pcur (4 * poolRem)

private theorem trail_to_tRaw_region (c : WorkCfg) {xs : List (BitVec 64)}
    (hx : xs.length = c.mv + 1) {f : Mem 64} (hf : int4Array c.tb xs f) :
    region c.tb c.tRaw f := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
  have htr : 4 * xs.length = c.tRaw := by unfold WorkCfg.tRaw; omega
  unfold WorkCfg.activeBytes WorkCfg.tRaw at *; simpa [htr] using int4Array_to_region (by omega) hf

private theorem pstate_rupRest_to_region {c : WorkCfg} {poolUsed poolRem : Nat}
    {cur0 te : BitVec 64} {ptrs : List (BitVec 64)} {table : List (Option (List (BitVec 64)))}
    {PoolUsed : Mem 64 → Prop} {assign : Assignment} {trail tf : List (BitVec 64)} {m : Mem 64}
    (hsum : poolUsed + poolRem = c.poolInts) (htbl : TableRel c.mv c.cap ptrs table PoolUsed)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hm : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur0 ptrs PoolUsed poolRem) m) :
    region c.hdr c.activeBytes m := by
  obtain ⟨_, _, _, hlen, hm0⟩ := pstate_sep.mp hm; obtain ⟨hplen, _, _⟩ := htbl
  have := c.fit_active; have hmv := c.hmv; unfold dimacsBound at hmv
  unfold WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  have hm_l : (((((((word8Array c.hdr (c.hdrWords pcur cur0) ⋆
      byte1Array c.vb (assignBytes c.mv assign)) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1))) ⋆
      int4Array c.tb (trail ++ tf)) ⋆ region c.tlim (c.tBytes - c.tRaw)) ⋆
      word8Array c.cb ptrs) ⋆ PoolUsed) ⋆ region pcur (4 * poolRem)) m :=
    sep_cast hm0 (by dsimp only [pcur, wsRupRest]; ac_rfl)
  refine workCfg_regions_to_activeBytes c hsum (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ hf => by
        simpa [WorkCfg.hdrWords] using word8Array_to_region (by simp [WorkCfg.hdrWords]) hf)
      (fun _ hf => by simpa using byte1Array_to_region (by simp; omega) hf))
      (fun _ h => h))
      (fun _ hf => trail_to_tRaw_region c (by rw [List.length_append]; exact hlen) hf))
      (fun _ h => h))
      (fun _ hf => by simpa [hplen] using word8Array_to_region (by rw [hplen]; omega) hf))
    hpu) (fun _ h => h) m hm_l)

private abbrev wsRupTail (c : WorkCfg) (prf_ptr pcur cur0 : BitVec 64) (prfBytes : List UInt8)
    (ptrs : List (BitVec 64)) (poolRem : Nat) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  Eq (prfBytes.At prf_ptr) ⋆ word8Array c.hdr (c.hdrWords pcur cur0) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆ word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R

private theorem wsRup_focus_iff {c : WorkCfg} {prf_ptr pcur cur0 ptr : BitVec 64}
    {prfBytes : List UInt8} {ptrs lits : List (BitVec 64)} {PoolUsed R_sub R : Mem 64 → Prop}
    {poolRem : Nat} {te : BitVec 64} {assign : Assignment} {trail tf : List (BitVec 64)}
    {m : Mem 64} (hpu : PoolUsed = (ZeroTermInts ptr lits ⋆ R_sub)) :
    (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m ↔
    (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆ (ZeroTermInts ptr lits ⋆
      (R_sub ⋆ wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R))) m := by
  constructor <;> intro hm
  · have h : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆ PoolUsed ⋆
        wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R) m := by
      dsimp only [wsRupRest, wsRupTail] at hm ⊢; exact sep_ac hm
    rw [hpu] at h; exact sep_ac h
  · have h : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        (ZeroTermInts ptr lits ⋆ R_sub) ⋆
        wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R) m := sep_ac hm
    rw [← hpu] at h; dsimp only [wsRupRest, wsRupTail] at h ⊢; exact sep_ac h

private structure RupState where
  idx : Nat
  te : BitVec 64
  assign : Assignment
  trail : List (BitVec 64)
  tf : List (BitVec 64)

private structure RupOuterSt extends RupState where
  fuel : Nat

private structure IdoneSt where
  unit : BitVec 64
  te : BitVec 64
  assign : Assignment
  trail : List (BitVec 64)
  tf : List (BitVec 64)

theorem lbRupCheck_correct (Γ : Env) :
    ∀ args m Q X, lbRupCheckSpec args m Q X → Func.spec Γ lbRupCheck args m Q X := by
  rintro _ m Q X ⟨c, id, c_ptr, prf_ptr, prfBytes, idx0, poolUsed, poolRem, clits, ptrs,
    table, PoolUsed, R, rfl, hid_cap, hprf_fit, hidx0, hvalid_c, ⟨R_c, hpu_c⟩, hm, hQ⟩
  unfold lbRupCheck Func.spec Func.wp
  obtain ⟨hsum, htbl, hpu, hm_u⟩ := workState_sep.mp (sep_ac hm :
    (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆
      (Eq (prfBytes.At prf_ptr) ⋆ R)) m)
  let pcur : BitVec 64 := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let cur0 : BitVec 64 := prf_ptr + BitVec.ofNat 64 idx0
  have htfit : c.tb.toNat + 4 * (c.mv + 1) < 2 ^ 64 := by
    have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
    have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
    unfold WorkCfg.activeBytes WorkCfg.tRaw at *; omega
  have hm_hdr :
      (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
        (wsFixed c ptrs PoolUsed ⋆ region pcur (4 * poolRem) ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    unfold wsFixed; exact sep_cast hm_u (by dsimp only [pcur, cur0]; ac_rfl)
  c0_hsteps_nogrp
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero,
    BitVec.reduceToNat, Nat.reduceDiv]
  refine wp_join0 (fun m' => rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
    (fun _ m' ⟨hnone, hreg⟩ => by c0_hstraight; grind) ?_
  intro Jfail hJfail
  have goFail : ∀ (te : BitVec 64) (assign : Assignment) (trail tf : List (BitVec 64))
      (m' : Mem 64), rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none →
      (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m' → Jfail () m' := by
    intro te assign trail tf m' hnone hm'
    exact hJfail m' ⟨hnone, sep_ac (sep_mono (fun _ => pstate_rupRest_to_region hsum htbl hpu)
      (sep_ac hm' : ((PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem) ⋆ (Eq (prfBytes.At prf_ptr) ⋆ R)) m'))⟩
  have rupStep : ∀ {idx : Nat} {te : BitVec 64} {assign : Assignment}
      {trail tf : List (BitVec 64)} {m' : Mem 64}
      {kZero : BitVec 64 → Expr Val Cont [i64]}
      {kHint : BitVec 64 → BitVec 64 → Expr Val Cont [i64]},
      idx ≤ prfBytes.length →
      (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m' →
      (readLeb128Pure (prfBytes.drop idx) = none →
        rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none) →
      (∀ bs', readLeb128Pure (prfBytes.drop idx) = some (0, bs') →
        bs' = prfBytes.drop (prfBytes.length - bs'.length) →
        prfBytes.length - bs'.length ≤ prfBytes.length →
        wp Γ Q X (kZero (prf_ptr + BitVec.ofNat 64 (prfBytes.length - bs'.length))) m') →
      (∀ u_pred bs', readLeb128Pure (prfBytes.drop idx) = some (u_pred + 1, bs') →
        (((u_pred + 1) % 2 != 0) = true ∨ ¬ ((u_pred + 1) / 2 < id) ∨
          table[(u_pred + 1) / 2]? = some none) →
        rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none) →
      (∀ u_pred bs' alits R_a,
        readLeb128Pure (prfBytes.drop idx) = some (u_pred + 1, bs') →
        bs'.length < (prfBytes.drop idx).length →
        bs' = prfBytes.drop (prfBytes.length - bs'.length) →
        prfBytes.length - bs'.length ≤ prfBytes.length →
        (u_pred + 1) % 2 = 0 → (u_pred + 1) / 2 < id →
        table[(u_pred + 1) / 2]? = some (some alits) → (∀ x ∈ alits, IsValidLit c.mv x) →
        ∀ als, PoolUsed = (ZeroTermInts als alits ⋆ R_a) →
        wp Γ Q X (kHint als (prf_ptr + BitVec.ofNat 64 (prfBytes.length - bs'.length))) m') →
      wp Γ Q X
        (readLeb128 Jfail (prf_ptr + BitVec.ofNat 64 idx)
          (prf_ptr + BitVec.ofNat 64 prfBytes.length)
          fun u p2 => tqbe {
            %uz:b = ceql ⟨.var u⟩, 0
            jnz %uz, { ⟨kZero p2⟩ }, {
              %odd:l = and ⟨.var u⟩, 1
              %is_odd:b = cnel %odd, 0
              jnz %is_odd, { ⟨.jump Jfail ()⟩ }, {
                %aid:l = shr ⟨.var u⟩, 1
                %lt_id:b = cultl %aid, ⟨.var (BitVec.ofNat 64 id)⟩
                jnz %lt_id, {
                  %off:l = shl %aid, 3
                  %slot:l = add ⟨.var c.cb⟩, %off
                  %als:l = load %slot
                  %act:b = cnel %als, 0
                  jnz %act, { ⟨kHint als p2⟩ }, { ⟨.jump Jfail ()⟩ }
                }, { ⟨.jump Jfail ()⟩ } } } }) m' := by
    intro idx te assign trail tf m' kZero kHint hidx hm' hnone_leb hzero hbad hhint
    have hfa := c.fit_active; unfold WorkCfg.activeBytes at hfa
    refine readLeb128_spec hprf_fit hidx rfl rfl (by ecancel)
      (fun hnone => goFail _ _ _ _ _ (hnone_leb hnone) hm')
      (fun u bs' hleb hu hlt hbs' _ => ?_)
    have hidx'_le : prfBytes.length - bs'.length ≤ prfBytes.length := by omega
    wp_unfold
    refine bv_eq_zero_branch (by omega : u < 2 ^ 64)
      (fun hu0 => by subst hu0; exact hzero bs' hleb hbs' hidx'_le) (fun hu_ne0 => ?_)
    obtain ⟨u_pred, hu_succ⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩; subst hu_succ
    refine bv_odd_branch (u := u_pred + 1) (by omega : u_pred + 1 < 2 ^ 64)
      (fun hodd => goFail _ _ _ _ _ (hbad u_pred bs' hleb (Or.inl hodd)) hm') (fun _ => ?_)
    rw [bv_shr_one (by omega : u_pred + 1 < 2 ^ 64)]
    refine ult_branch (by omega : (u_pred + 1) / 2 < 2 ^ 64) (by omega : id < 2 ^ 64)
      (fun haid_lt => ?_)
      (fun hge => goFail _ _ _ _ _ (hbad u_pred bs' hleb (Or.inr (Or.inl hge))) hm')
    have haid_cap : (u_pred + 1) / 2 < c.cap := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (u_pred + 1) / 2 < 2 ^ 64)]
    obtain ⟨hplen, htlen, hrel⟩ := htbl
    have hspec_a := hrel ((u_pred + 1) / 2) haid_cap
    have hget : table[(u_pred + 1) / 2]? = some (table[(u_pred + 1) / 2]'(htlen ▸ haid_cap)) :=
      List.getElem?_eq_getElem (htlen ▸ haid_cap)
    refine ⟨_, load_word8Array (hplen ▸ haid_cap) (by dsimp only [wsRupRest] at hm'; ecancel), ?_⟩
    cases ht_a : table[(u_pred + 1) / 2]'(htlen ▸ haid_cap) with
    | none =>
      rw [ht_a] at hspec_a hget
      exact ⟨fun h => absurd hspec_a h,
        fun _ => goFail _ _ _ _ _ (hbad u_pred bs' hleb (Or.inr (Or.inr hget))) hm'⟩
    | some alits =>
      rw [ht_a] at hspec_a hget; obtain ⟨hne, hvalid_a, R_a, hpu_a⟩ := hspec_a
      exact ⟨fun _ => hhint u_pred bs' alits R_a hleb hlt hbs' hidx'_le (by grind) haid_lt
        hget hvalid_a _ hpu_a, fun h => absurd h hne⟩
  refine wp_join_state (fun st : RupState => (prf_ptr + BitVec.ofNat 64 st.idx, st.te, ()))
    (fun st m' => st.idx ≤ prfBytes.length ∧
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
        consumeHintsPure id table (prfBytes.drop st.idx) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb st.te st.assign st.trail st.tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
    (fun _ ⟨idx_c, cte, assign_c, trail_c, tf_c⟩ m_c ⟨hidx_c, hpure_c, hm_c⟩ => by
      dsimp only at *
      refine wp_while_state1 (fun st : Nat × Nat => prf_ptr + BitVec.ofNat 64 st.2)
        (fun st => st.1)
        (fun st m' => (prfBytes.drop st.2).length < st.1 ∧ st.2 ≤ prfBytes.length ∧
          rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
            consumeHintsAux st.1 id table (prfBytes.drop st.2) ∧
          (Eq (prfBytes.At prf_ptr) ⋆
            PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
            wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
        (fun Jcloop hJcloop => by
          wp_unfold; exact hJcloop ((prfBytes.drop idx_c).length + 1, idx_c) m_c
            ⟨by dsimp; omega, hidx_c, hpure_c, hm_c⟩)
        (fun Jcloop ⟨fuel, idx⟩ m' ⟨hfuel_gt, hidx, hpure, hm'⟩ ih => by
          obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by dsimp at hfuel_gt; omega⟩
          dsimp only [Blocks.get_here] at *
          refine rupStep hidx hm'
            (fun hnone => by rw [consumeHintsAux.eq_2, hnone] at hpure; exact hpure)
            (fun bs' hleb hbs' hidx'_le => by
              rw [consumeHintsAux.eq_2, hleb] at hpure
              obtain ⟨hte_c, hcov_c, htv_c, hlen_c, hm_ps⟩ := pstate_sep.mp (sep_ac hm' :
                (PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
                  (Eq (prfBytes.At prf_ptr) ⋆ wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R)) m')
              have hmv_lt := c.hmv; unfold dimacsBound at hmv_lt
              refine backtrack_spec hte_c htv_c (by omega) hcov_c hm_ps (fun m_bt hm_bt => ?_)
              have hm_bt_hdr :
                  (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                    (wsFixed c ptrs PoolUsed ⋆ region pcur (4 * poolRem) ⋆
                      Eq (prfBytes.At prf_ptr) ⋆ R)) m_bt := by
                unfold wsFixed
                exact sep_cast (sep_mono (P' := region c.tb c.tRaw)
                  (fun _ hf => trail_to_tRaw_region c (by rw [List.length_append]; exact hlen_c) hf)
                  (sep_ac hm_bt : (int4Array c.tb (trail_c ++ tf_c) ⋆
                    (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
                      Eq (prfBytes.At prf_ptr) ⋆ wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆
                      R)) m_bt))
                  (by dsimp only [wsRupRest]; ac_rfl)
              c0_hsteps
              let p2 : BitVec 64 := prf_ptr + BitVec.ofNat 64 (prfBytes.length - bs'.length)
              have hws_fin : (WorkState c poolUsed poolRem p2 ptrs table PoolUsed ⋆
                  (Eq (prfBytes.At prf_ptr) ⋆ R)) _ :=
                workState_sep.mpr ⟨hsum, htbl, hpu, by
                  unfold wsFixed at hm; simp only [BitVec.reduceToNat, Nat.reduceDiv] at hm
                  have hhdr_eq : (c.hdrWords pcur cur0).set 9 p2 = c.hdrWords pcur p2 := rfl
                  rw [← hhdr_eq]; exact sep_cast hm (by dsimp only [pcur, p2]; ac_rfl)⟩
              exact hQ 1 _ (by rw [hpure]; exact ⟨rfl, hbs', hidx'_le, sep_ac hws_fin⟩))
            (fun u_pred bs' hleb hbad => by
              rw [consumeHintsAux.eq_2, hleb] at hpure
              rcases hbad with hodd | hge | hnone
              · simp only [hodd, ↓reduceIte] at hpure; exact hpure
              all_goals grind)
            (fun u_pred bs' alits _ hleb hlt hbs' hidx'_le heven haid hsome _ _ _ => by
              rw [consumeHintsAux.eq_2, hleb] at hpure
              have heven_b : ((u_pred + 1) % 2 != 0) = false := by simp [heven]
              simp only [heven_b, Bool.false_eq_true, ↓reduceIte, haid, hsome] at hpure
              exact ih ⟨fuel', prfBytes.length - bs'.length⟩ _ (by dsimp; omega)
                ⟨by dsimp; rw [← hbs']; omega, hidx'_le, by rwa [← hbs'], hm'⟩))) ?_
  intro Jconsume hJconsume
  refine wp_join_state (fun st : RupState => (cur0, st.te, ()))
    (fun st m' => st.idx = idx0 ∧
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
        rupPhase2Aux ((prfBytes.drop idx0).length + 1) c.mv id table
          (assignBytes c.mv st.assign) st.trail.length (prfBytes.drop idx0) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb st.te st.assign st.trail st.tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
    (fun _ ⟨_, hte, assign0, trail0, tf0_p2⟩ m_p2 ⟨_, hpure_p2, hm_p2⟩ => by
      dsimp only at *
      refine wp_while_state (fun st : RupOuterSt =>
          (prf_ptr + BitVec.ofNat 64 st.idx, st.te, ()))
        (fun st => st.fuel)
        (fun st m' => (prfBytes.drop st.idx).length < st.fuel ∧ st.idx ≤ prfBytes.length ∧
          rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
            rupPhase2Aux st.fuel c.mv id table (assignBytes c.mv st.assign) st.trail.length
              (prfBytes.drop st.idx) ∧
          (Eq (prfBytes.At prf_ptr) ⋆
            PState c.mv c.vb c.tb st.te st.assign st.trail st.tf (c.mv + 1) ⋆
            wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
        (fun Jouter hJouter => by
          wp_unfold
          exact hJouter ⟨⟨idx0, hte, assign0, trail0, tf0_p2⟩, (prfBytes.drop idx0).length + 1⟩
            m_p2 ⟨by dsimp; omega, hidx0, hpure_p2, by simpa [cur0] using hm_p2⟩)
        (fun Jouter ⟨⟨idx, te, assign, trail, tf⟩, fuel⟩ m' ⟨hfuel_gt, hidx, hpure, hm'⟩ ih => by
          obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by dsimp at hfuel_gt; omega⟩
          dsimp only [Blocks.get_here] at *
          refine rupStep hidx hm'
            (fun hnone => by rw [rupPhase2Aux.eq_2, hnone] at hpure; exact hpure)
            (fun bs' hleb _ _ => by
              rw [rupPhase2Aux.eq_2, hleb] at hpure; exact goFail te assign trail tf m' hpure hm')
            (fun u_pred bs' hleb hbad => by
              rw [rupPhase2Aux.eq_2, hleb] at hpure; dsimp only at hpure
              rcases hbad with hodd | hge | hnone
              · simp only [hodd, ↓reduceIte] at hpure; exact hpure
              all_goals grind)
            (fun u_pred bs' alits R_a hleb hlt hbs' hidx'_le heven haid hsome hvalid_a _ hpu_a => by
              rw [rupPhase2Aux.eq_2, hleb] at hpure; dsimp only at hpure
              have heven_b : ((u_pred + 1) % 2 != 0) = false := by simp [heven]
              simp only [heven_b, Bool.false_eq_true, ↓reduceIte, haid, hsome] at hpure
              let idx' := prfBytes.length - bs'.length
              refine wp_join_state (fun st : IdoneSt => (st.unit, st.te, ()))
                (fun st m'' => rupInnerPure c.mv alits 0 (assignBytes c.mv assign) trail.length =
                    some (st.unit, assignBytes c.mv st.assign, st.trail.length) ∧
                  (Eq (prfBytes.At prf_ptr) ⋆
                    PState c.mv c.vb c.tb st.te st.assign st.trail st.tf (c.mv + 1) ⋆
                    wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m'')
                (fun _ ⟨unit, t2, assign2, trail2, tf2⟩ m'' ⟨hinner_ok, hm''⟩ => by
                  dsimp only [Blocks.get_here] at *; wp_unfold; simp only [hinner_ok] at hpure
                  refine ⟨fun htu => ?_, fun hntu => ?_⟩
                  · simp only [bne_iff_ne.mpr htu, ↓reduceIte] at hpure
                    exact ih ⟨⟨idx', t2, assign2, trail2, tf2⟩, fuel'⟩ _ (by dsimp; omega)
                      ⟨by dsimp; rw [← hbs']; omega, hidx'_le, by rwa [← hbs'], hm''⟩
                  · simp only [bne_eq_false_iff_eq.mpr hntu, Bool.false_eq_true, ↓reduceIte]
                      at hpure
                    exact hJconsume ⟨idx', t2, assign2, trail2, tf2⟩ m''
                      ⟨hidx'_le, by rwa [← hbs'], hm''⟩)
                (fun Jidone hJidone => by
                  refine rupInner_spec hvalid_a rfl htfit ((wsRup_focus_iff hpu_a).mp hm')
                    (fun m'' t2 assign2 trail2 tf2 hinner_none hm''_in => by
                      simp only [hinner_none] at hpure
                      exact goFail t2 assign2 trail2 tf2 m'' hpure
                        ((wsRup_focus_iff hpu_a).mpr hm''_in))
                    (fun m'' unit t2 assign2 trail2 tf2 hinner_ok hm''_in =>
                      hJidone ⟨unit, t2, assign2, trail2, tf2⟩ m''
                        ⟨hinner_ok, (wsRup_focus_iff hpu_a).mpr hm''_in⟩))))) ?_
  intro Jph2 hJph2
  have hm_tb : (region c.tb (4 * (c.mv + 1)) ⋆
      (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    change (region c.tb c.tRaw ⋆ _) m
    exact sep_cast hm_u (by dsimp only [pcur, cur0, wsRupRest]; ac_rfl)
  obtain ⟨f_t, f_o, hu_t, hd_t, hf_t, hf_o⟩ := hm_tb
  have hmv_lt := c.hmv; unfold dimacsBound at hmv_lt
  obtain ⟨tf0, htf0_len, htf0_arr⟩ := region_to_int4Array (c.mv + 1) (by omega) hf_t
  have hm_arr :
      ((byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆ int4Array c.tb ([] ++ tf0)) ⋆
      (wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    simpa only [List.nil_append] using sep_ac (show (int4Array c.tb tf0 ⋆
      (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m from
      ⟨f_t, f_o, hu_t, hd_t, htf0_arr, hf_o⟩)
  have hm_ps0 : (Eq (prfBytes.At prf_ptr) ⋆
      PState c.mv c.vb c.tb c.tb Assignment.empty [] tf0 (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m :=
    sep_ac (pstate_sep.mpr ⟨by simp, trailCoversAssign_empty c.mv, by simp,
      (by simp; exact htf0_len), hm_arr⟩ :
      (PState c.mv c.vb c.tb c.tb Assignment.empty [] tf0 (c.mv + 1) ⋆
        (wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m)
  refine rupPhase1_spec hvalid_c rfl htfit ((wsRup_focus_iff hpu_c).mp hm_ps0)
    (fun m' te assign trail tf hp1_fail hm' =>
      goFail te assign trail tf m' (by rw [rupCheckPure, hp1_fail])
        ((wsRup_focus_iff hpu_c).mpr hm'))
    (fun m' te assign trail tf hp1_taut hm' =>
      hJconsume ⟨idx0, te, assign, trail, tf⟩ m'
        ⟨hidx0, by rw [rupCheckPure, hp1_taut], (wsRup_focus_iff hpu_c).mpr hm'⟩)
    (fun m' te assign trail tf hp1_ok hm' =>
      hJph2 ⟨idx0, te, assign, trail, tf⟩ m'
        ⟨rfl, by rw [rupCheckPure, hp1_ok], (wsRup_focus_iff hpu_c).mpr hm'⟩)

/-! ## 4. Pure RUP soundness (`rupCheckPure_sound`) -/

private theorem cnf_append_left {f1 f2 g : CNF Nat} (h : CNF.Entails f1 f2) :
    CNF.Entails (f1 ++ g) (f2 ++ g) :=
  CNF.entails_append_of_entails (CNF.entails_trans CNF.append_entails_left h)
    CNF.append_entails_right

private theorem entails_add_of_entailsClause {F : CNF Nat} {initAssign curAssign : Assignment}
    {c : CNF.Clause Nat} (hc : CNF.EntailsClause F c)
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF)) :
    CNF.Entails F (F.add c) ∧ CNF.Entails (F.add c) F ∧
      CNF.Entails (F.add c ++ initAssign.toCNF) (F.add c ++ curAssign.toCNF) := by
  have hF_add := CNF.entails_add_iff.mpr ⟨CNF.entails_refl F, hc⟩
  have hadd_F := (CNF.entails_add_iff.mp (CNF.entails_refl (F.add c))).1
  exact ⟨hF_add, hadd_F,
    CNF.entails_trans (cnf_append_left hadd_F) (CNF.entails_trans hent (cnf_append_left hF_add))⟩

private theorem unsat_of_entailsClause_all_falsified {F : CNF Nat}
    {initAssign curAssign : Assignment} {c : CNF.Clause Nat} (hc : CNF.EntailsClause F c)
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, curAssign.get? lit.1 = some !lit.2) :
    CNF.Unsat (F ++ initAssign.toCNF) := by
  obtain ⟨hF_add, _, hent'⟩ := entails_add_of_entailsClause hc hent
  exact CNF.unsat_of_entails_unsat
    (unsat_of_all_falsified (CNF.mem_add.mpr (Or.inl rfl)) hent' hall) (cnf_append_left hF_add)

private theorem entails_insert_of_entailsClause_unit_prop {F : CNF Nat}
    {initAssign curAssign : Assignment} {c : CNF.Clause Nat} {unit : Literal Nat}
    (hc : CNF.EntailsClause F c) (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, lit = unit ∨ curAssign.get? lit.1 = some !lit.2) :
    CNF.Entails (F ++ initAssign.toCNF) (F ++ (curAssign.insert unit.1 unit.2).toCNF) := by
  obtain ⟨hF_add, hadd_F, hent'⟩ := entails_add_of_entailsClause hc hent
  exact CNF.entails_trans (cnf_append_left hF_add)
    (CNF.entails_trans (entails_insert_of_unit_prop (CNF.mem_add.mpr (Or.inl rfl)) hent' hall)
      (cnf_append_left hadd_F))

private theorem rupPhase1Pure_loop_sound {mv : Nat} {clits : List (BitVec 64)}
    (hvalid : ∀ x ∈ clits, IsValidLit mv x) :
    ∀ (rem i : Nat) (assign : Assignment) (trailLen : Nat),
      i ≤ clits.length → rem = clits.length - i →
      (∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral ↔ assign.get? x.1 = some !x.2) →
      (rupPhase1Pure mv (clits.drop i) (assignBytes mv assign) trailLen = .taut →
        ∃ atom pol, (atom, pol) ∈ toClause clits ∧ (atom, !pol) ∈ toClause clits) ∧
      (∀ vals' trailLen',
        rupPhase1Pure mv (clits.drop i) (assignBytes mv assign) trailLen = .ok vals' trailLen' →
        ∃ assign', vals' = assignBytes mv assign' ∧
          ∀ x : Literal Nat, x ∈ toClause clits ↔ assign'.get? x.1 = some !x.2)
  | 0, i, assign, trailLen, hi, hrem, hinv => by
    obtain rfl : i = clits.length := by omega
    rw [List.drop_length, rupPhase1Pure.eq_1]
    refine ⟨fun h => (nomatch h), fun vals' trailLen' h => ?_⟩
    injection h with hvals _; subst hvals; rw [List.take_length] at hinv
    exact ⟨assign, rfl, fun x => by rw [← CNF.Clause.mem_literals_iff, literals_toClause, hinv x]⟩
  | rem + 1, i, assign, trailLen, _, hrem, hinv => by
    have hlt : i < clits.length := by omega
    have hlit : IsValidLit mv clits[i] := hvalid clits[i] (List.getElem_mem hlt)
    have hcases := evalAssignedLit_cases assign hlit
    rw [List.drop_eq_getElem_cons hlt, rupPhase1Pure.eq_2]; dsimp only
    rw [assignBytes_getD assign hlit]
    cases hneg : (evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i]).slt 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let eval := evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i]
      cases hpos : (0 : BitVec 64).slt eval <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · cases hfull : (trailLen == mv + 1) <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · rw [show (bvAbs clits[i]).toNat = (toLiteral (-clits[i])).1 by
              simp [toLiteral, bvAbs_neg hlit],
            assignBytes_set_insert mv assign (isValidLit_neg hlit)]
          exact rupPhase1Pure_loop_sound hvalid rem (i + 1)
            (assign.insert (toLiteral (-clits[i])).1 (toLiteral (-clits[i])).2)
            (trailLen + 1) hlt (by omega)
            (phase1_step_insert hlt hlit hinv (hcases.2.2 ⟨hneg, hpos⟩).1)
        · grind
      · exact ⟨fun _ => phase1_step_tautology hlt hinv (hcases.2.1 ⟨hneg, hpos⟩),
          fun _ _ h => (nomatch h)⟩
    · simp only [↓reduceIte]
      exact rupPhase1Pure_loop_sound hvalid rem (i + 1) assign trailLen hlt (by omega)
        (phase1_step_already_falsified hlt hinv (hcases.1 hneg))

private theorem rupInnerPure_loop_sound {mv : Nat} {alits : List (BitVec 64)} {F : CNF Nat}
    {initAssign curAssign : Assignment} (hvalid : ∀ x ∈ alits, IsValidLit mv x)
    (hcl : CNF.EntailsClause F (toClause alits))
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF)) :
    ∀ (rem i : Nat) (unit : BitVec 64) (assign : Assignment) (trailLen : Nat)
      (unit' : BitVec 64) (vals' : List (BitVec 64)) (trailLen' : Nat),
      i ≤ alits.length → rem = alits.length - i → InnerSt mv alits curAssign i unit assign →
      rupInnerPure mv (alits.drop i) unit (assignBytes mv assign) trailLen =
        some (unit', vals', trailLen') →
      ((unit' != 0) = false ∧ CNF.Unsat (F ++ initAssign.toCNF)) ∨
      ((unit' != 0) = true ∧ ∃ assign', vals' = assignBytes mv assign' ∧
        CNF.Entails (F ++ initAssign.toCNF) (F ++ assign'.toCNF))
  | 0, i, unit, assign, trailLen, unit', vals', trailLen', hi, hrem, hst, hres => by
    obtain rfl : i = alits.length := by omega
    rw [List.drop_length, rupInnerPure.eq_1] at hres
    cases hres; rw [InnerSt, List.take_length] at hst
    rcases hst with ⟨rfl, rfl, hall⟩ | ⟨hu, _, _, hrel, hinv⟩
    · refine Or.inl ⟨by decide, unsat_of_entailsClause_all_falsified hcl hent fun x hx => ?_⟩
      rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx; exact hall x hx
    · refine Or.inr ⟨bne_iff_ne.mpr hu, assign, rfl, ?_⟩
      rcases hrel with ⟨_, rfl⟩ | rfl
      · exact entails_insert_of_entailsClause_unit_prop hcl hent fun x hx => by
          rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx; exact hinv x hx
      · exact hent
  | rem + 1, i, unit, assign, trailLen, unit', vals', trailLen', _, hrem, hst, hres => by
    have hlt : i < alits.length := by omega
    have hlit : IsValidLit mv alits[i] := hvalid alits[i] (List.getElem_mem hlt)
    have hcases := evalAssignedLit_cases assign hlit
    rw [List.drop_eq_getElem_cons hlt, rupInnerPure.eq_2] at hres; dsimp only at hres
    rw [assignBytes_getD assign hlit] at hres
    cases hneg : (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]).slt 0 <;>
      simp only [hneg, Bool.false_eq_true, ↓reduceIte] at hres
    · let stepUnit : Option (BitVec 64 × List (BitVec 64) × Nat) :=
        if evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] == 0 then
          if trailLen == mv + 1 then none
          else rupInnerPure mv (alits.drop (i + 1)) alits[i]
            ((assignBytes mv assign).set (bvAbs alits[i]).toNat (bvSignByte alits[i]))
            (trailLen + 1)
        else rupInnerPure mv (alits.drop (i + 1)) alits[i] (assignBytes mv assign) trailLen
      obtain ⟨hu_cases, hres_su⟩ :
          (unit = 0 ∨ unit = alits[i]) ∧ stepUnit = some (unit', vals', trailLen') := by
        rcases hst with ⟨rfl, _⟩ | ⟨hu, _, _⟩
        · grind
        · rw [bne_iff_ne.mpr hu] at hres; grind
      dsimp only [stepUnit] at hres_su
      cases hvz : (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] == 0) <;>
        simp only [hvz, Bool.false_eq_true, ↓reduceIte] at hres_su
      · have hpos : (0 : BitVec 64).slt
            (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]) = true := by grind
        exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) alits[i] assign trailLen
          unit' vals' trailLen' hlt (by omega)
          (innerSt_step_satisfied hlt hlit hst hu_cases (hcases.2.1 ⟨hneg, hpos⟩)) hres_su
      · have hv0 : evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] = 0 :=
          eq_of_beq hvz
        have hun : assign.get? (toLiteral alits[i]).1 = none :=
          (hcases.2.2 ⟨hneg, by rw [hv0]; decide⟩).1
        cases hfull : (trailLen == mv + 1)
        · simp only [hfull, Bool.false_eq_true, ↓reduceIte] at hres_su
          obtain ⟨rfl, rfl, hst'⟩ := innerSt_step_unassigned hlt hlit hst hu_cases hun
          have hidx_pos : (bvAbs alits[i]).toNat = (toLiteral alits[i]).1 := rfl
          rw [hidx_pos, assignBytes_set_insert mv assign hlit] at hres_su
          exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) alits[i]
            (assign.insert (toLiteral alits[i]).1 (toLiteral alits[i]).2)
            (trailLen + 1) unit' vals' trailLen' hlt (by omega) hst' hres_su
        · simp [hfull] at hres_su
    · cases heq : (unit == -alits[i])
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hres
        exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) unit assign trailLen
          unit' vals' trailLen' hlt (by omega)
          (innerSt_step_falsified hlt hlit hst (hcases.1 hneg) (beq_eq_false_iff_ne.mp heq)) hres
      · simp [heq] at hres

private theorem rupPhase2Aux_sound {mv id : Nat} {table : List (Option (List (BitVec 64)))}
    {F : CNF Nat} {initAssign : Assignment}
    (htable : ∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
      (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits)) :
    ∀ (fuel : Nat) (curAssign : Assignment) (trailLen : Nat) (bs bs_out : List UInt8),
      CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF) →
      rupPhase2Aux fuel mv id table (assignBytes mv curAssign) trailLen bs = some bs_out →
      CNF.Unsat (F ++ initAssign.toCNF)
  | 0, _, _, _, _, _, hp2 => nomatch hp2
  | fuel + 1, curAssign, trailLen, bs, bs_out, hent, hp2 => by
    rcases hleb : readLeb128Pure bs with _ | ⟨_ | u_pred, bs'⟩
    · rw [rupPhase2Aux.eq_2, hleb] at hp2; nomatch hp2
    · rw [rupPhase2Aux.eq_2, hleb] at hp2; nomatch hp2
    rw [rupPhase2Aux.eq_2, hleb] at hp2
    split at hp2 <;> try contradiction
    all_goals cases ‹some (u_pred + 1, bs') = _›
    cases hodd : ((u_pred + 1) % 2 != 0)
    · rw [hodd] at hp2; simp only [Bool.false_eq_true, ↓reduceIte] at hp2
      by_cases haid : (u_pred + 1) / 2 < id
      · simp only [haid, ↓reduceIte] at hp2
        rcases htbl : table[(u_pred + 1) / 2]? with _ | opt <;> rw [htbl] at hp2
        · nomatch hp2
        rcases opt with _ | alits
        · nomatch hp2
        dsimp only at hp2
        obtain ⟨halits_valid, halits_ent⟩ := htable ((u_pred + 1) / 2) haid alits htbl
        rcases hinner : rupInnerPure mv alits 0 (assignBytes mv curAssign) trailLen with
          _ | ⟨unit, vals', trailLen'⟩
        · rw [hinner] at hp2; nomatch hp2
        rw [hinner] at hp2; dsimp only at hp2
        rcases rupInnerPure_loop_sound halits_valid halits_ent hent alits.length 0 0 curAssign
            trailLen unit vals' trailLen' (Nat.zero_le _) (by simp) (Or.inl ⟨rfl, rfl, by simp⟩)
            (by simpa using hinner) with ⟨_, hunsat⟩ | ⟨hu_t, assign', rfl, hent'⟩
        · exact hunsat
        · simp only [hu_t, ↓reduceIte] at hp2
          exact rupPhase2Aux_sound htable fuel assign' trailLen' bs' bs_out hent' hp2
      · simp [haid] at hp2
    · rw [hodd] at hp2; nomatch hp2

theorem rupCheckPure_sound {mv id : Nat} {clits : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8} {F : CNF Nat}
    (_hmv : mv < dimacsBound) (hclits : ∀ x ∈ clits, IsValidLit mv x)
    (htable : ∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
      (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits))
    (hrup : rupCheckPure mv id clits table bs = some bs') :
    CNF.EntailsClause F (toClause clits) := by
  rw [rupCheckPure, ← assignBytes_empty mv] at hrup
  have hp1_sound := rupPhase1Pure_loop_sound hclits clits.length 0 Assignment.empty 0
    (Nat.zero_le _) (by simp) (by simp)
  rw [List.drop_zero] at hp1_sound
  cases hp1 : rupPhase1Pure mv clits (assignBytes mv Assignment.empty) 0 with
  | fail => rw [hp1] at hrup; nomatch hrup
  | taut => exact entailsClause_of_tautology (hp1_sound.1 hp1)
  | ok vals trailLen =>
    rw [hp1] at hrup; dsimp only at hrup
    obtain ⟨initAssign, rfl, hiff⟩ := hp1_sound.2 vals trailLen hp1
    exact entailsClause_of_unsat_of_iff_falsified hiff
      (rupPhase2Aux_sound htable (bs.length + 1) initAssign trailLen bs bs'
        (CNF.entails_refl _) hrup)

end LeanQbe.T.Examples.LratBytes
