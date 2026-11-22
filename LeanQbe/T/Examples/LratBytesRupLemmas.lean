module

public import LeanQbe.T.Examples.LratBytesSpec
import Kraken.SeparationTactics
import all Kraken.Separation

/-!
# `lbReadAddLits` and `lbRupCheck`: correctness and pure RUP soundness in `LeanQbe.T`

Self-contained (`G5`) typed-IR proofs of:
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

private theorem readAddLitsAux_succ (fuel mv poolRem : Nat) (acc : List (BitVec 64))
    (bs : List UInt8) :
    readAddLitsAux (fuel + 1) mv poolRem acc bs =
      (if poolRem == 0 then none
       else match readLeb128Pure bs with
       | none => none
       | some (0, bs') => some (acc.reverse, poolRem - 1, bs')
       | some (u, bs') =>
         let v := u / 2
         if v == 0 || mv < v then none
         else readAddLitsAux fuel mv (poolRem - 1) (decodeZigZag u :: acc) bs') := rfl

private theorem rupPhase1Pure_nil (mv : Nat) (vals : List (BitVec 64)) (trailLen : Nat) :
    rupPhase1Pure mv [] vals trailLen = .ok vals trailLen := rfl

private theorem rupPhase1Pure_cons (mv : Nat) (lit : BitVec 64)
    (lits vals : List (BitVec 64)) (trailLen : Nat) :
    rupPhase1Pure mv (lit :: lits) vals trailLen =
      (let val := evalAssignedLit (vals.getD (bvAbs lit).toNat 0) lit
       if val.slt 0 then rupPhase1Pure mv lits vals trailLen
       else if (0 : BitVec 64).slt val then .taut
       else if trailLen == mv + 1 then .fail
       else rupPhase1Pure mv lits (vals.set (bvAbs lit).toNat (bvSignByte (-lit)))
         (trailLen + 1)) := rfl

private theorem rupInnerPure_nil (mv : Nat) (unit : BitVec 64) (vals : List (BitVec 64))
    (trailLen : Nat) :
    rupInnerPure mv [] unit vals trailLen = some (unit, vals, trailLen) := rfl

private theorem rupInnerPure_cons (mv : Nat) (lit : BitVec 64) (lits : List (BitVec 64))
    (unit : BitVec 64) (vals : List (BitVec 64)) (trailLen : Nat) :
    rupInnerPure mv (lit :: lits) unit vals trailLen =
      (let val := evalAssignedLit (vals.getD (bvAbs lit).toNat 0) lit
       if val.slt 0 then
         if unit == -lit then none else rupInnerPure mv lits unit vals trailLen
       else
         let stepUnit : Option (BitVec 64 × List (BitVec 64) × Nat) :=
           if val == 0 then
             if trailLen == mv + 1 then none
             else rupInnerPure mv lits lit (vals.set (bvAbs lit).toNat (bvSignByte lit))
               (trailLen + 1)
           else rupInnerPure mv lits lit vals trailLen
         if unit != 0 then (if unit == lit then stepUnit else none) else stepUnit) := rfl

private theorem consumeHintsAux_succ (fuel id : Nat)
    (table : List (Option (List (BitVec 64)))) (bs : List UInt8) :
    consumeHintsAux (fuel + 1) id table bs =
      (match readLeb128Pure bs with
       | none => none
       | some (0, bs') => some bs'
       | some (u, bs') =>
         if u % 2 != 0 then none
         else
           let aid := u / 2
           if aid < id then
             match table[aid]? with
             | some (some _) => consumeHintsAux fuel id table bs'
             | _ => none
           else none) := rfl

private theorem rupPhase2Aux_succ (fuel mv id : Nat)
    (table : List (Option (List (BitVec 64)))) (vals : List (BitVec 64))
    (trailLen : Nat) (bs : List UInt8) :
    rupPhase2Aux (fuel + 1) mv id table vals trailLen bs =
      (match readLeb128Pure bs with
       | none => none
       | some (0, _) => none
       | some (u, bs') =>
         if u % 2 != 0 then none
         else
           let aid := u / 2
           if aid < id then
             match table[aid]? with
             | some (some alits) =>
               match rupInnerPure mv alits 0 vals trailLen with
               | none => none
               | some (unit, vals', trailLen') =>
                 if unit != 0 then rupPhase2Aux fuel mv id table vals' trailLen' bs'
                 else consumeHintsPure id table bs'
             | _ => none
           else none) := rfl

private theorem rupPhase2Aux_succ_some_nz {fuel mv id : Nat}
    {table : List (Option (List (BitVec 64)))} {vals : List (BitVec 64)}
    {trailLen : Nat} {bs : List UInt8} {u_pred : Nat} {bs' : List UInt8}
    (h : readLeb128Pure bs = some (u_pred + 1, bs')) :
    rupPhase2Aux (fuel + 1) mv id table vals trailLen bs =
      (if (u_pred + 1) % 2 != 0 then none
       else if (u_pred + 1) / 2 < id then
         match table[(u_pred + 1) / 2]? with
         | some (some alits) =>
           match rupInnerPure mv alits 0 vals trailLen with
           | none => none
           | some (unit, vals', trailLen') =>
             if unit != 0 then rupPhase2Aux fuel mv id table vals' trailLen' bs'
             else consumeHintsPure id table bs'
         | _ => none
       else none) := by
  rw [rupPhase2Aux_succ, h]; rfl

private theorem rupCheckPure_def (mv id : Nat) (clits : List (BitVec 64))
    (table : List (Option (List (BitVec 64)))) (bs : List UInt8) :
    rupCheckPure mv id clits table bs =
      (match rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 with
       | .fail => none
       | .taut => consumeHintsPure id table bs
       | .ok vals trailLen => rupPhase2Aux (bs.length + 1) mv id table vals trailLen bs) := rfl

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
  refine wp_loop_group (fun fuel (cur_v, wcur_v, ()) m' =>
    ∃ (idx rem : Nat) (acc : List (BitVec 64)),
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
      rw [readAddLitsAux_succ] at hpure
      simp only [beq_self_eq_true, ↓reduceIte] at hpure
      exact collapseFail acc 0 m' hrem_sum hpure hm'
    · have hrem_pos : 0 < rem := Nat.pos_of_ne_zero fun h0 => hnfull (by
        rw [show c_ptr + BitVec.ofNat 64 (4 * acc.length) = wcur from rfl, hwcur_eq]
        exact (c.pcur_eq_plim_iff (by omega)).mpr h0)
      have hrem_b : (rem == 0) = false := beq_false_of_ne (by omega)
      refine readLeb128_spec hprf_fit hidx rfl rfl (by ecancel)
        (fun hleb_none => ?_)
        (fun u bs' hleb_some hu _ hbs' _ => ?_)
      · rw [readAddLitsAux_succ, hleb_none] at hpure
        simp only [hrem_b, Bool.false_eq_true, ↓reduceIte] at hpure
        exact collapseFail acc rem m' hrem_sum hpure hm'
      · let idx' := prfBytes.length - bs'.length
        have hidx'_le : idx' ≤ prfBytes.length := by omega
        wp_unfold
        refine bv_eq_zero_branch (by omega : u < 2 ^ 64) (fun hu0 => ?_) (fun hu_ne0 => ?_)
        · subst hu0
          rw [readAddLitsAux_succ, hleb_some] at hpure
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
              rw [readAddLitsAux_succ, hleb_some]
              simp only [hrem_b, Bool.false_eq_true, ↓reduceIte]
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

/-! ## 2. Propagation state (`PState`), inline helpers, and `InnerSt` -/

private theorem abs_eq (lit : BitVec 64) :
    (lit ^^^ lit.sshiftRight 63) - lit.sshiftRight 63 = bvAbs lit := by
  rw [sar63, negif]; rfl

private theorem negif_eq (b lit : BitVec 64) :
    (b ^^^ lit.sshiftRight 63) - lit.sshiftRight 63 = evalAssignedLit b lit := by
  rw [sar63, negif]; rfl

private theorem assignBytes_getD {mv : Nat} (assign : Assignment) {lit : BitVec 64}
    (hlit : IsValidLit mv lit) :
    (assignBytes mv assign).getD (bvAbs lit).toNat 0 = assignByte assign (toLiteral lit).1 := by
  have hi : (bvAbs lit).toNat < mv + 1 := by have := hlit.2.2.1; omega
  have hi' : (bvAbs lit).toNat < (assignBytes mv assign).length := by simpa using hi
  simp [List.getD, List.getElem?_eq_getElem hi', getElem_assignBytes mv assign hi, toLiteral]

private theorem assignedLit_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vb lit : BitVec 64} {mv : Nat} {assign : Assignment} {R : Mem 64 → Prop} {m : Mem 64}
    {k : BitVec 64 → BitVec 64 → Expr Val Cont rs}
    (hlit : IsValidLit mv lit) (hm : (byte1Array vb (assignBytes mv assign) ⋆ R) m)
    (hk : wp Γ Q X (k (bvAbs lit) (evalAssignedLit (assignByte assign (toLiteral lit).1) lit)) m) :
    wp Γ Q X (assignedLit vb lit k) m := by
  unfold assignedLit; wp_unfold; simp only [abs_eq, negif_eq]
  have hi' : (bvAbs lit).toNat < mv + 1 := by have := hlit.2.2.1; omega
  have hi : (bvAbs lit).toNat < (assignBytes mv assign).length := by simpa using hi'
  have hld : loadVal m i8 (vb + bvAbs lit) =
      some ((assignByte assign (toLiteral lit).1).setWidth 8) := by
    rw [← ofNat_bvAbs_toNat lit]
    simpa [getElem_assignBytes mv assign hi', toLiteral] using load_byte1Array hi hm
  refine ⟨_, hld, ?_⟩
  rw [sext8 _ (isInt8_assignByte _ _)]
  exact hk

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
  refine wp_loop_group (fun r (t_v, ()) m => ∃ i, i ≤ trail.length ∧ r = trail.length - i ∧
    t_v = tb + BitVec.ofNat 64 (4 * i) ∧
    ((byte1Array vb (clearTrailBytes (assignBytes mv assign) (trail.take i)) ⋆
      int4Array tb (trail ++ tf)) ⋆ R) m) ?_ ?_
  · rintro J r ⟨t_v, ⟨⟩⟩ m ih ⟨i, hi, rfl, rfl, hm⟩
    dsimp only [Blocks.get_here]; wp_unfold
    refine ⟨fun heq => ?_, fun hne => ?_⟩
    · obtain rfl : i = trail.length := by grind
      rw [List.take_length, clearTrailBytes_assignBytes hcov] at hm
      exact hk m hm
    · have hlt : i < trail.length := by grind
      have hv := hvalid trail[i] (List.getElem_mem hlt)
      have hget : (trail ++ tf)[i]'(by simp; omega) = trail[i] := List.getElem_append_left hlt
      rw [sep_assoc, sep_comm_l] at hm
      have hld := load_int4Array (i := i) (by simp; omega) hm
      rw [hget] at hld
      refine ⟨_, hld, ?_⟩
      rw [sext32 _ hv.1, abs_eq, ← ofNat_bvAbs_toNat]
      rw [sep_comm_l] at hm
      have hidx : (bvAbs trail[i]).toNat <
          (clearTrailBytes (assignBytes mv assign) (trail.take i)).length := by
        simp; have := hv.2.2.1; omega
      have ⟨ok, hm1⟩ := store_byte1Array 0#8 hidx hm
      rw [show (0#8).setWidth 64 = (0 : BitVec 64) from rfl,
          clearTrailBytes_take_succ _ trail hlt] at hm1
      exact ⟨ok, ih _ _ _ (by omega) ⟨i + 1, hlt, rfl, by rw [ptr4], by rwa [sep_assoc]⟩⟩
  · intro J hJ; wp_unfold
    exact hJ _ _ _ ⟨0, Nat.zero_le _, rfl, by simp, by simpa using hm⟩

/-- The values array represents `assign`, the trail array holds `trail` and then the free space
`tf` (total length `N`), and `te` points just after `trail`. -/
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
  have hm' := (pstate_sep.1 hm).2.2.2.2
  rw [sep_assoc] at hm'
  exact assignedLit_spec hlit hm' hk

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
  rcases tf with _ | ⟨t0, tf'⟩
  · simp at hcap
  subst hte
  have hi : (toLiteral wlit).1 < (assignBytes mv assign).length := by
    simp [toLiteral]; have := hwlit.2.2.1; omega
  rw [sep_assoc] at hm0
  have ⟨ok1, hm1⟩ := store_byte1Array64 (bvSignByte wlit) hi hm0
  rw [assignBytes_set_insert mv assign hwlit, sep_comm_l] at hm1
  have ⟨ok2, hm2⟩ := store_int4Array64 (i := trail.length) wlit (by simp) hm1
  rw [show (trail ++ t0 :: tf').set trail.length wlit = (trail ++ [wlit]) ++ tf' by
    simp [List.set_append_right]] at hm2
  have ha : vb + bvAbs wlit = vb + BitVec.ofNat 64 (toLiteral wlit).1 := by simp [toLiteral]
  rw [ha]
  refine ⟨ok1, ok2, tf', rfl, pstate_sep.2 ⟨by grind, trailCoversAssign_insert wlit hcov,
    by grind, by simp at hlen ⊢; omega, sep_cast hm2 (by ac_rfl)⟩⟩

/-- The state of the inner loop after `i` literals of the antecedent: no unit yet and everything
falsified, or a unit literal `unit` that is now true and everything else falsified. -/
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
    (hst : InnerSt mv clits curAssign i unit assign)
    (hu : unit = 0 ∨ unit = clits[i])
    (hsat : assign.get? (toLiteral clits[i]).1 = some (toLiteral clits[i]).2) :
    InnerSt mv clits curAssign (i + 1) clits[i] assign := by
  rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨hu', huv, hus, hrel, hinv⟩
  · exact Or.inr ⟨hlit.2.1, hlit, hsat, Or.inr rfl, phase2_inner_new_unit hlt hinv⟩
  · rcases hu with rfl | rfl
    · exact absurd rfl hu'
    · exact Or.inr ⟨hu', huv, hus, hrel, phase2_inner_dup_unit hlt rfl hinv⟩

/-! ## 3. `assignLitChecked_spec`, `rupPhase1_spec`, `rupInner_spec`, and `lbRupCheck_correct` -/

private theorem assignLitChecked_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fail : Cont []}
    {vb tb tlim te wlit idx : BitVec 64} {mv : Nat}
    {assign : Assignment} {trail tf : List (BitVec 64)} {R : Mem 64 → Prop}
    {m : Mem 64} {k : BitVec 64 → Expr Val Cont rs}
    (hwlit : IsValidLit mv wlit) (hidx : idx = bvAbs wlit)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb te assign trail tf (mv + 1) ⋆ R) m)
    (hfail : trail.length = mv + 1 → fail () m)
    (hk : ∀ m' tf',
      trail.length ≠ mv + 1 →
      (PState mv vb tb (te + 4)
        (assign.insert (toLiteral wlit).1 (toLiteral wlit).2)
        (trail ++ [wlit]) tf' (mv + 1) ⋆ R) m' →
      wp Γ Q X (k (te + 4)) m') :
    wp Γ Q X (assignLitChecked fail vb tlim te wlit idx k) m := by
  obtain ⟨hte, _, _, hlen, _⟩ := pstate_sep.mp hm
  unfold assignLitChecked; subst hidx htlim; wp_unfold
  refine ⟨fun _ => by grind, fun hnfull => ?_⟩
  have hne_len : trail.length ≠ mv + 1 := fun heq => hnfull (by rw [hte, heq])
  rw [show (BitVec.sshiftRight wlit 63 ||| 1) = bvSignByte wlit from rfl]
  obtain ⟨ok1, ok2, tf', _, hm'⟩ := store_assignLit_pstate hwlit hm (by omega)
  exact ⟨ok1, ok2, hk _ tf' hne_len hm'⟩

private theorem rupPhase1_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fail : Cont []} {taut ph2 : Cont [i64, i64]}
    {vb tb tlim c_ptr cur0 : BitVec 64} {mv : Nat} {clits tf0 : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hvalid : ∀ x ∈ clits, IsValidLit mv x)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
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
  refine wp_loop_group (fun r (l_v, te_v, ()) m' =>
    ∃ (i : Nat) (te : BitVec 64) (assign : Assignment) (trail tf : List (BitVec 64)),
      l_v = c_ptr + BitVec.ofNat 64 (4 * i) ∧ te_v = te ∧ i ≤ clits.length ∧ r = clits.length - i ∧
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' ∧
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 =
        rupPhase1Pure mv (clits.drop i) (assignBytes mv assign) trail.length) ?_ ?_
  · rintro J r ⟨l_v, te, ⟨⟩⟩ m' ih ⟨i, te', assign, trail, tf, rfl, rfl, hi, rfl, hm', hpure⟩
    dsimp only [Blocks.get_here]; wp_unfold
    refine zeroTerm_jnz_step hi h32 hne0 (by ecancel) (fun hlt => ?_) (fun heq => ?_)
    · have hlit := hvalid clits[i] (List.getElem_mem hlt)
      rw [sext32 _ hlit.1]
      rw [List.drop_eq_getElem_cons hlt] at hpure
      rw [rupPhase1Pure_cons, assignBytes_getD assign hlit] at hpure
      refine assignedLit_pstate hlit hm' ?_
      wp_unfold
      refine ⟨fun hneg => ?_, fun hnneg => ⟨fun _ => by grind, fun hnpos => ?_⟩⟩
      · simp only [hneg, ↓reduceIte] at hpure
        exact ih _ _ _ (by omega) ⟨i + 1, te, assign, trail, tf, by rw [ptr4], rfl, hlt, rfl,
          hm', hpure⟩
      · rw [show (0 : BitVec 64) - clits[i] = -clits[i] by simp]
        refine assignLitChecked_spec (isValidLit_neg hlit) (bvAbs_neg hlit).symm htlim htfit hm'
          (fun _ => by grind) (fun m'' tf' hne_len hm'' => ?_)
        have hfull_f : (trail.length == mv + 1) = false := beq_eq_false_iff_ne.mpr hne_len
        simp only [hnneg, hnpos, hfull_f, Bool.false_eq_true, ↓reduceIte] at hpure
        have hidx_neg : (bvAbs clits[i]).toNat = (toLiteral (-clits[i])).1 := by
          simp [toLiteral, bvAbs_neg hlit]
        rw [hidx_neg, assignBytes_set_insert mv assign (isValidLit_neg hlit)] at hpure
        wp_unfold
        exact ih _ _ _ (by omega) ⟨i + 1, te + 4, _, trail ++ [-clits[i]], tf',
          by rw [ptr4], rfl, hlt, rfl, hm'', by simpa using hpure⟩
    · subst heq; rw [List.drop_length, rupPhase1Pure_nil] at hpure
      exact hph2 m' te assign trail tf hpure hm'
  · intro J hJ; wp_unfold
    exact hJ _ _ _ ⟨0, tb, Assignment.empty, [], tf0, by simp, rfl, Nat.zero_le _, rfl, hm,
      by simp [assignBytes_empty]⟩

private theorem rupInner_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fail : Cont []} {done : Cont [i64, i64]}
    {vb tb tlim als te0 : BitVec 64} {mv : Nat} {alits : List (BitVec 64)}
    {curAssign : Assignment} {curTrail curTf : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hvalid : ∀ x ∈ alits, IsValidLit mv x)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
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
  refine wp_loop_group (fun r (l_v, unit_v, te_v, ()) m' =>
    ∃ (i : Nat) (unit te : BitVec 64) (assign : Assignment) (trail tf : List (BitVec 64)),
      l_v = als + BitVec.ofNat 64 (4 * i) ∧ unit_v = unit ∧ te_v = te ∧
      i ≤ alits.length ∧ r = alits.length - i ∧
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' ∧
      rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length =
        rupInnerPure mv (alits.drop i) unit (assignBytes mv assign) trail.length) ?_ ?_
  · rintro J r ⟨l_v, unit, te, ⟨⟩⟩ m' ih
      ⟨i, unit', te', assign, trail, tf, rfl, rfl, rfl, hi, rfl, hm', hpure⟩
    dsimp only [Blocks.get_here]; wp_unfold
    refine zeroTerm_jnz_step hi h32 hne0 (by ecancel) (fun hlt => ?_) (fun heq => ?_)
    · have hlit := hvalid alits[i] (List.getElem_mem hlt)
      rw [sext32 _ hlit.1]
      rw [List.drop_eq_getElem_cons hlt] at hpure
      rw [rupInnerPure_cons, assignBytes_getD assign hlit] at hpure
      refine assignedLit_pstate hlit hm' ?_
      wp_unfold
      let val := evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]
      refine ⟨fun hneg => ?_, fun hnneg => ?_⟩
      · rw [show (0 : BitVec 64) - alits[i] = -alits[i] by simp]
        refine ⟨fun _ => by grind, fun hne => ?_⟩
        have hne_b : (unit == -alits[i]) = false := beq_eq_false_iff_ne.mpr hne
        simp only [hneg, hne_b, Bool.false_eq_true, ↓reduceIte] at hpure
        exact ih _ _ _ (by omega)
          ⟨i + 1, unit, te, assign, trail, tf, by rw [ptr4], rfl, rfl, hlt, rfl, hm', hpure⟩
      · simp only [hnneg, Bool.false_eq_true, ↓reduceIte] at hpure
        let stepUnit : Option (BitVec 64 × List (BitVec 64) × Nat) :=
          if val == 0 then
            if trail.length == mv + 1 then none
            else
              rupInnerPure mv (alits.drop (i + 1)) alits[i]
                ((assignBytes mv assign).set (bvAbs alits[i]).toNat (bvSignByte alits[i]))
                (trail.length + 1)
          else
            rupInnerPure mv (alits.drop (i + 1)) alits[i] (assignBytes mv assign) trail.length
        refine wp_join_group (fun () m'' => m'' = m' ∧
          rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length = stepUnit) ?_ ?_
        · rintro _ ⟨⟩ _ ⟨rfl, hpure_su⟩
          dsimp only [Blocks.get_here]; wp_unfold
          dsimp only [stepUnit, val] at hpure_su
          refine ⟨fun hvz => ?_, fun hnvz => ?_⟩
          · simp only [hvz, beq_self_eq_true, ↓reduceIte] at hpure_su
            refine assignLitChecked_spec hlit rfl htlim htfit hm'
              (fun _ => by grind) (fun m'' tf' hne_len hm'' => ?_)
            have hfull_f : (trail.length == mv + 1) = false := beq_eq_false_iff_ne.mpr hne_len
            simp only [hfull_f, Bool.false_eq_true, ↓reduceIte] at hpure_su
            have hidx_pos : (bvAbs alits[i]).toNat = (toLiteral alits[i]).1 := rfl
            rw [hidx_pos, assignBytes_set_insert mv assign hlit] at hpure_su
            wp_unfold
            exact ih _ _ _ (by omega) ⟨i + 1, alits[i], te + 4, _, trail ++ [alits[i]], tf',
              by rw [ptr4], rfl, rfl, hlt, rfl, hm'', by simpa using hpure_su⟩
          · have hvz_f : (val == 0) = false := beq_eq_false_iff_ne.mpr hnvz
            dsimp only [val] at hvz_f
            simp only [hvz_f, Bool.false_eq_true, ↓reduceIte] at hpure_su
            exact ih _ _ _ (by omega)
              ⟨i + 1, alits[i], te, assign, trail, tf, by rw [ptr4], rfl, rfl, hlt, rfl, hm',
                hpure_su⟩
        · intro Jsu hJsu; wp_unfold
          refine ⟨fun htu => ?_, fun hntu => ?_⟩
          · have : (unit != 0) = true := bne_iff_ne.mpr htu; grind
          · have : (unit != 0) = false := bne_eq_false_iff_eq.mpr hntu; grind
    · subst heq; rw [List.drop_length, rupInnerPure_nil] at hpure
      exact hdone m' unit te assign trail tf hpure hm'
  · intro J hJ; wp_unfold
    exact hJ _ _ _ ⟨0, 0, te0, curAssign, curTrail, curTf, by simp, rfl, rfl, Nat.zero_le _, rfl,
      hm, rfl⟩

private abbrev wsRupRest (c : WorkCfg) (pcur cur0 : BitVec 64) (ptrs : List (BitVec 64))
    (PoolUsed : Mem 64 → Prop) (poolRem : Nat) : Mem 64 → Prop :=
  word8Array c.hdr (c.hdrWords pcur cur0) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆
  word8Array c.cb ptrs ⋆
  PoolUsed ⋆
  region pcur (4 * poolRem)

private theorem trail_to_tRaw_region (c : WorkCfg) {xs : List (BitVec 64)}
    (hx : xs.length = c.mv + 1) {f : Mem 64} (hf : int4Array c.tb xs f) :
    region c.tb c.tRaw f := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
  have htr : 4 * xs.length = c.tRaw := by unfold WorkCfg.tRaw; omega
  unfold WorkCfg.activeBytes WorkCfg.tRaw at *
  simpa [htr] using int4Array_to_region (by omega) hf

private theorem pstate_rupRest_to_region {c : WorkCfg} {poolUsed poolRem : Nat}
    {cur0 te : BitVec 64} {ptrs : List (BitVec 64)} {table : List (Option (List (BitVec 64)))}
    {PoolUsed : Mem 64 → Prop} {assign : Assignment} {trail tf : List (BitVec 64)} {m : Mem 64}
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
  unfold WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  have hm_ord :
      (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
        byte1Array c.vb (assignBytes c.mv assign) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        int4Array c.tb (trail ++ tf) ⋆
        region c.tlim (c.tBytes - c.tRaw) ⋆
        word8Array c.cb ptrs ⋆ PoolUsed ⋆ region pcur (4 * poolRem)) m :=
    sep_cast hm0 (by dsimp only [pcur, wsRupRest]; ac_rfl)
  refine workCfg_regions_to_activeBytes c hsum ?_
  exact sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ hf => by
      simpa [WorkCfg.hdrWords] using word8Array_to_region (by simp [WorkCfg.hdrWords]) hf)
    (fun _ hf => by simpa using byte1Array_to_region (by simp; omega) hf))
    (fun _ h => h))
    (fun _ hf => trail_to_tRaw_region c (by rw [List.length_append]; exact hlen) hf))
    (fun _ h => h))
    (fun _ hf => by simpa [hplen] using word8Array_to_region (by rw [hplen]; omega) hf))
    hpu) (fun _ h => h) m hm_ord

private abbrev wsRupTail (c : WorkCfg) (prf_ptr pcur cur0 : BitVec 64) (prfBytes : List UInt8)
    (ptrs : List (BitVec 64)) (poolRem : Nat) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  Eq (prfBytes.At prf_ptr) ⋆ word8Array c.hdr (c.hdrWords pcur cur0) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆ word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R

private theorem wsRup_focus {c : WorkCfg} {prf_ptr pcur cur0 ptr : BitVec 64}
    {prfBytes : List UInt8} {ptrs lits : List (BitVec 64)} {PoolUsed R_sub R : Mem 64 → Prop}
    {poolRem : Nat} {te : BitVec 64} {assign : Assignment} {trail tf : List (BitVec 64)}
    {m : Mem 64}
    (hpu : PoolUsed = (ZeroTermInts ptr lits ⋆ R_sub))
    (hm : (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m) :
    (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆ (ZeroTermInts ptr lits ⋆
      (R_sub ⋆ wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R))) m := by
  have hm' : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆ PoolUsed ⋆
      wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R) m := by
    dsimp only [wsRupRest, wsRupTail] at hm ⊢; exact sep_ac hm
  rw [hpu] at hm'; exact sep_ac hm'

private theorem wsRup_unfocus {c : WorkCfg} {prf_ptr pcur cur0 ptr : BitVec 64}
    {prfBytes : List UInt8} {ptrs lits : List (BitVec 64)} {PoolUsed R_sub R : Mem 64 → Prop}
    {poolRem : Nat} {te : BitVec 64} {assign : Assignment} {trail tf : List (BitVec 64)}
    {m : Mem 64}
    (hpu : PoolUsed = (ZeroTermInts ptr lits ⋆ R_sub))
    (hm : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆ (ZeroTermInts ptr lits ⋆
      (R_sub ⋆ wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R))) m) :
    (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m := by
  have hm' : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      (ZeroTermInts ptr lits ⋆ R_sub) ⋆
      wsRupTail c prf_ptr pcur cur0 prfBytes ptrs poolRem R) m := sep_ac hm
  rw [← hpu] at hm'
  dsimp only [wsRupRest, wsRupTail] at hm' ⊢; exact sep_ac hm'

private theorem wsRup_load_cb {c : WorkCfg} {prf_ptr pcur cur0 : BitVec 64}
    {prfBytes : List UInt8} {ptrs : List (BitVec 64)} {PoolUsed R : Mem 64 → Prop}
    {poolRem aid : Nat} {te : BitVec 64} {assign : Assignment} {trail tf : List (BitVec 64)}
    {m : Mem 64} (haid : aid < ptrs.length)
    (hm : (Eq (prfBytes.At prf_ptr) ⋆ PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m) :
    loadVal m i64 (c.cb + BitVec.ofNat 64 (8 * aid)) = some (ptrs[aid]'haid) := by
  dsimp only [wsRupRest] at hm
  exact load_word8Array haid (by ecancel)

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
  wp_unfold
  refine ⟨_, loadl_hdr 3 (by decide) hm_hdr rfl,
    _, loadl_hdr 4 (by decide) hm_hdr rfl,
    _, loadl_hdr 5 (by decide) hm_hdr rfl,
    _, loadl_hdr 6 (by decide) hm_hdr rfl,
    _, loadl_hdr 9 (by decide) hm_hdr rfl, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  -- `@fail()`
  refine wp_join_group (fun () m' =>
    rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m') ?_ ?_
  · rintro _ ⟨⟩ m' ⟨hnone, hreg⟩; dsimp only [Blocks.get_here]; wp_unfold; grind
  intro Jfail hJfail
  have goFail : ∀ (te : BitVec 64) (assign : Assignment) (trail tf : List (BitVec 64))
      (m' : Mem 64),
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none →
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m' →
      Jfail () m' := by
    intro te assign trail tf m' hnone hm'
    have hm1 : ((PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem) ⋆
        (Eq (prfBytes.At prf_ptr) ⋆ R)) m' := sep_ac hm'
    exact hJfail () m' ⟨hnone,
      sep_ac (sep_mono (fun _ => pstate_rupRest_to_region hsum htbl hpu) hm1)⟩
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
    obtain ⟨u_pred, hu_succ⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
    subst hu_succ
    refine bv_odd_branch (u := u_pred + 1) (by omega : u_pred + 1 < 2 ^ 64)
      (fun hodd => goFail _ _ _ _ _ (hbad u_pred bs' hleb (Or.inl hodd)) hm') (fun heven_b => ?_)
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
    refine ⟨_, wsRup_load_cb (hplen ▸ haid_cap) hm', ?_⟩
    cases ht_a : table[(u_pred + 1) / 2]'(htlen ▸ haid_cap) with
    | none =>
      rw [ht_a] at hspec_a hget
      exact ⟨fun h => absurd hspec_a h,
        fun _ => goFail _ _ _ _ _ (hbad u_pred bs' hleb (Or.inr (Or.inr hget))) hm'⟩
    | some alits =>
      rw [ht_a] at hspec_a hget
      obtain ⟨hne, hvalid_a, R_a, hpu_a⟩ := hspec_a
      exact ⟨fun _ => hhint u_pred bs' alits R_a hleb hlt hbs' hidx'_le (by grind) haid_lt
        hget hvalid_a _ hpu_a, fun h => absurd h hne⟩
  -- `@consume(%ccur, %cte)`
  refine wp_join_group (fun (ccur_v, cte_v, ()) m' =>
    ∃ (idx_c : Nat) (cte : BitVec 64) (assign : Assignment) (trail tf : List (BitVec 64)),
      ccur_v = prf_ptr + BitVec.ofNat 64 idx_c ∧ cte_v = cte ∧ idx_c ≤ prfBytes.length ∧
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
        consumeHintsPure id table (prfBytes.drop idx_c) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb cte assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m') ?_ ?_
  · rintro _ ⟨ccur_v, cte, ⟨⟩⟩ m_c
      ⟨idx_c, cte', assign_c, trail_c, tf_c, rfl, rfl, hidx_c, hpure_c, hm_c⟩
    dsimp only [Blocks.get_here]
    -- `@cloop(%p)`
    refine wp_loop_group (fun fuel (p_v, ()) m' => ∃ (idx : Nat),
      (prfBytes.drop idx).length < fuel ∧ idx ≤ prfBytes.length ∧
      p_v = prf_ptr + BitVec.ofNat 64 idx ∧
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
        consumeHintsAux fuel id table (prfBytes.drop idx) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m') ?_ ?_
    · rintro Jcloop fuel ⟨p_v, ⟨⟩⟩ m' ih ⟨idx, hfuel_gt, hidx, rfl, hpure, hm'⟩
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      dsimp only [Blocks.get_here]
      refine rupStep hidx hm'
        (fun hnone => by rw [consumeHintsAux_succ, hnone] at hpure; exact hpure)
        (fun bs' hleb hbs' hidx'_le => ?_)
        (fun u_pred bs' hleb hbad => by
          rw [consumeHintsAux_succ, hleb] at hpure
          rcases hbad with hodd | hge | hnone
          · simp only [hodd, ↓reduceIte] at hpure; exact hpure
          · grind
          · grind)
        (fun u_pred bs' alits _ hleb hlt hbs' hidx'_le heven haid hsome _ _ _ => by
          rw [consumeHintsAux_succ, hleb] at hpure
          have heven_b : ((u_pred + 1) % 2 != 0) = false := by simp [heven]
          simp only [heven_b, Bool.false_eq_true, ↓reduceIte, haid, hsome] at hpure
          exact ih fuel' _ _ (by omega)
            ⟨prfBytes.length - bs'.length, by rw [← hbs']; omega, hidx'_le, rfl,
              by rwa [← hbs'], hm'⟩)
      · rw [consumeHintsAux_succ, hleb] at hpure
        obtain ⟨hte_c, hcov_c, htv_c, hlen_c, hm_ps⟩ := pstate_sep.mp (sep_ac hm' :
          (PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
            (Eq (prfBytes.At prf_ptr) ⋆ wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R)) m')
        have hmv_lt := c.hmv; unfold dimacsBound at hmv_lt
        refine backtrack_spec hte_c htv_c (by omega) hcov_c hm_ps (fun m_bt hm_bt => ?_)
        wp_unfold
        have hm_bt_hdr :
            (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
              (wsFixed c ptrs PoolUsed ⋆ region pcur (4 * poolRem) ⋆
                Eq (prfBytes.At prf_ptr) ⋆ R)) m_bt := by
          unfold wsFixed
          exact sep_cast (sep_mono (P' := region c.tb c.tRaw)
            (fun _ hf => trail_to_tRaw_region c (by rw [List.length_append]; exact hlen_c) hf)
            (sep_ac hm_bt :
              (int4Array c.tb (trail_c ++ tf_c) ⋆
                (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆
                  wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R)) m_bt))
            (by dsimp only [wsRupRest]; ac_rfl)
        let p2 : BitVec 64 := prf_ptr + BitVec.ofNat 64 (prfBytes.length - bs'.length)
        obtain ⟨ok_p72, hm_fin⟩ := store_word8Array (i := 9) p2
          (by simp [WorkCfg.hdrWords]) hm_bt_hdr
        have hhdr_eq : (c.hdrWords pcur cur0).set 9 p2 = c.hdrWords pcur p2 := rfl
        rw [hhdr_eq] at hm_fin
        have hws_fin : (WorkState c poolUsed poolRem p2 ptrs table PoolUsed ⋆
            (Eq (prfBytes.At prf_ptr) ⋆ R)) (storeMem m_bt i64 (c.hdr + 72) p2) :=
          workState_sep.mpr ⟨hsum, htbl, hpu, by
            unfold wsFixed at hm_fin; exact sep_cast hm_fin (by dsimp only [pcur]; ac_rfl)⟩
        exact ⟨ok_p72, hQ 1 _ (by rw [hpure]; exact ⟨rfl, hbs', hidx'_le, sep_ac hws_fin⟩)⟩
    · intro Jcloop hJcloop; wp_unfold
      exact hJcloop ((prfBytes.drop idx_c).length + 1) _ _
        ⟨idx_c, by omega, hidx_c, rfl, hpure_c, hm_c⟩
  intro Jconsume hJconsume
  -- `@ph2(%hcur, %hte)`
  refine wp_join_group (fun (hcur_v, hte_v, ()) m' =>
    ∃ (hte : BitVec 64) (assign : Assignment) (trail tf : List (BitVec 64)),
      hcur_v = cur0 ∧ hte_v = hte ∧
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
        rupPhase2Aux ((prfBytes.drop idx0).length + 1) c.mv id table
          (assignBytes c.mv assign) trail.length (prfBytes.drop idx0) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb hte assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m') ?_ ?_
  · rintro _ ⟨hcur_v, hte, ⟨⟩⟩ m_p2 ⟨hte', assign0, trail0, tf0_p2, rfl, rfl, hpure_p2, hm_p2⟩
    dsimp only [Blocks.get_here]
    -- `@outer(%p, %t)`
    refine wp_loop_group (fun fuel (p_v, t_v, ()) m' =>
      ∃ (idx : Nat) (te : BitVec 64) (assign : Assignment) (trail tf : List (BitVec 64)),
        (prfBytes.drop idx).length < fuel ∧ idx ≤ prfBytes.length ∧
        p_v = prf_ptr + BitVec.ofNat 64 idx ∧ t_v = te ∧
        rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
          rupPhase2Aux fuel c.mv id table (assignBytes c.mv assign) trail.length
            (prfBytes.drop idx) ∧
        (Eq (prfBytes.At prf_ptr) ⋆
          PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
          wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m') ?_ ?_
    · rintro Jouter fuel ⟨p_v, te, ⟨⟩⟩ m' ih
        ⟨idx, te', assign, trail, tf, hfuel_gt, hidx, rfl, rfl, hpure, hm'⟩
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      dsimp only [Blocks.get_here]
      refine rupStep hidx hm'
        (fun hnone => by rw [rupPhase2Aux_succ, hnone] at hpure; exact hpure)
        (fun bs' hleb _ _ => by
          rw [rupPhase2Aux_succ, hleb] at hpure
          exact goFail te assign trail tf m' hpure hm')
        (fun u_pred bs' hleb hbad => by
          rw [rupPhase2Aux_succ_some_nz hleb] at hpure
          rcases hbad with hodd | hge | hnone
          · simp only [hodd, ↓reduceIte] at hpure; exact hpure
          · grind
          · grind)
        (fun u_pred bs' alits R_a hleb hlt hbs' hidx'_le heven haid hsome hvalid_a _ hpu_a => ?_)
      rw [rupPhase2Aux_succ_some_nz hleb] at hpure
      have heven_b : ((u_pred + 1) % 2 != 0) = false := by simp [heven]
      simp only [heven_b, Bool.false_eq_true, ↓reduceIte, haid, hsome] at hpure
      let idx' := prfBytes.length - bs'.length
      -- `@idone(%unit, %t2)`
      refine wp_join_group (fun (unit_v, t2_v, ()) m'' =>
        ∃ (unit t2 : BitVec 64) (assign2 : Assignment) (trail2 tf2 : List (BitVec 64)),
          unit_v = unit ∧ t2_v = t2 ∧
          rupInnerPure c.mv alits 0 (assignBytes c.mv assign) trail.length =
            some (unit, assignBytes c.mv assign2, trail2.length) ∧
          (Eq (prfBytes.At prf_ptr) ⋆
            PState c.mv c.vb c.tb t2 assign2 trail2 tf2 (c.mv + 1) ⋆
            wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m'') ?_ ?_
      · rintro _ ⟨unit, t2, ⟨⟩⟩ m''
          ⟨unit', t2', assign2, trail2, tf2, rfl, rfl, hinner_ok, hm''⟩
        dsimp only [Blocks.get_here]; wp_unfold
        simp only [hinner_ok] at hpure
        refine ⟨fun htu => ?_, fun hntu => ?_⟩
        · have htu_b : (unit != 0) = true := bne_iff_ne.mpr htu
          simp only [htu_b, ↓reduceIte] at hpure
          exact ih fuel' _ _ (by omega) ⟨idx', t2, assign2, trail2, tf2,
            by rw [← hbs']; omega, hidx'_le, rfl, rfl, by rwa [← hbs'], hm''⟩
        · have : (unit != 0) = false := bne_eq_false_iff_eq.mpr hntu
          grind
      · intro Jidone hJidone
        refine rupInner_spec hvalid_a rfl htfit (wsRup_focus hpu_a hm')
          (fun m'' t2 assign2 trail2 tf2 hinner_none hm''_in => ?_)
          (fun m'' unit t2 assign2 trail2 tf2 hinner_ok hm''_in => ?_)
        · simp only [hinner_none] at hpure
          exact goFail t2 assign2 trail2 tf2 m'' hpure (wsRup_unfocus hpu_a hm''_in)
        · exact hJidone _ m'' ⟨unit, t2, assign2, trail2, tf2, rfl, rfl, hinner_ok,
            wsRup_unfocus hpu_a hm''_in⟩
    · intro Jouter hJouter; wp_unfold
      exact hJouter ((prfBytes.drop idx0).length + 1) _ _
        ⟨idx0, hte, assign0, trail0, tf0_p2, by omega, hidx0, rfl, rfl, hpure_p2, hm_p2⟩
  intro Jph2 hJph2
  -- Entry: convert `region c.tb c.tRaw` to `int4Array c.tb tf0` and invoke `rupPhase1_spec`
  have hm_tb :
      (region c.tb (4 * (c.mv + 1)) ⋆
        (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
          wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    change (region c.tb c.tRaw ⋆ _) m
    exact sep_cast hm_u (by dsimp only [pcur, cur0, wsRupRest]; ac_rfl)
  obtain ⟨f_t, f_o, hu_t, hd_t, hf_t, hf_o⟩ := hm_tb
  have hmv_lt := c.hmv; unfold dimacsBound at hmv_lt
  obtain ⟨tf0, htf0_len, htf0_arr⟩ := region_to_int4Array (c.mv + 1) (by omega) hf_t
  have hm_arr :
      ((byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆ int4Array c.tb ([] ++ tf0)) ⋆
        (wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    have h1 : (int4Array c.tb tf0 ⋆ (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m :=
      ⟨f_t, f_o, hu_t, hd_t, htf0_arr, hf_o⟩
    simpa only [List.nil_append] using sep_ac h1
  have hm_ps0 :
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb c.tb Assignment.empty [] tf0 (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m :=
    sep_ac (pstate_sep.mpr ⟨by simp, trailCoversAssign_empty c.mv, by simp,
      by simp [htf0_len], hm_arr⟩ :
      (PState c.mv c.vb c.tb c.tb Assignment.empty [] tf0 (c.mv + 1) ⋆
        (wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m)
  refine rupPhase1_spec hvalid_c rfl htfit (wsRup_focus hpu_c hm_ps0)
    (fun m' te assign trail tf hp1_fail hm' =>
      goFail te assign trail tf m' (by rw [rupCheckPure_def, hp1_fail])
        (wsRup_unfocus hpu_c hm'))
    (fun m' te assign trail tf hp1_taut hm' =>
      hJconsume _ m' ⟨idx0, te, assign, trail, tf, rfl, rfl, hidx0,
        by rw [rupCheckPure_def, hp1_taut], wsRup_unfocus hpu_c hm'⟩)
    (fun m' te assign trail tf hp1_ok hm' =>
      hJph2 _ m' ⟨te, assign, trail, tf, rfl, rfl,
        by rw [rupCheckPure_def, hp1_ok], wsRup_unfocus hpu_c hm'⟩)

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
  have hF_add : CNF.Entails F (F.add c) := CNF.entails_add_iff.mpr ⟨CNF.entails_refl F, hc⟩
  have hadd_F : CNF.Entails (F.add c) F := (CNF.entails_add_iff.mp (CNF.entails_refl (F.add c))).1
  exact ⟨hF_add, hadd_F,
    CNF.entails_trans (cnf_append_left hadd_F) (CNF.entails_trans hent (cnf_append_left hF_add))⟩

private theorem unsat_of_entailsClause_all_falsified {F : CNF Nat}
    {initAssign curAssign : Assignment} {c : CNF.Clause Nat}
    (hc : CNF.EntailsClause F c)
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, curAssign.get? lit.1 = some !lit.2) :
    CNF.Unsat (F ++ initAssign.toCNF) := by
  obtain ⟨hF_add, _, hent'⟩ := entails_add_of_entailsClause hc hent
  exact CNF.unsat_of_entails_unsat
    (unsat_of_all_falsified (CNF.mem_add.mpr (Or.inl rfl)) hent' hall)
    (cnf_append_left hF_add)

private theorem entails_insert_of_entailsClause_unit_prop {F : CNF Nat}
    {initAssign curAssign : Assignment} {c : CNF.Clause Nat} {unit : Literal Nat}
    (hc : CNF.EntailsClause F c)
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF))
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
    rw [List.drop_length, rupPhase1Pure_nil]
    refine ⟨fun h => (nomatch h), fun vals' trailLen' h => ?_⟩
    injection h with hvals _; subst hvals; rw [List.take_length] at hinv
    exact ⟨assign, rfl, fun x => by rw [← CNF.Clause.mem_literals_iff, literals_toClause, hinv x]⟩
  | rem + 1, i, assign, trailLen, _, hrem, hinv => by
    have hlt : i < clits.length := by omega
    have hlit : IsValidLit mv clits[i] := hvalid clits[i] (List.getElem_mem hlt)
    have hcases := evalAssignedLit_cases assign hlit
    rw [List.drop_eq_getElem_cons hlt]
    rw [rupPhase1Pure_cons, assignBytes_getD assign hlit]
    dsimp only
    cases hneg : (evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i]).slt 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let eval := evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i]
      cases hpos : (0 : BitVec 64).slt eval
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hfull : (trailLen == mv + 1)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hidx_neg : (bvAbs clits[i]).toNat = (toLiteral (-clits[i])).1 := by
            simp [toLiteral, bvAbs_neg hlit]
          rw [hidx_neg, assignBytes_set_insert mv assign (isValidLit_neg hlit)]
          exact rupPhase1Pure_loop_sound hvalid rem (i + 1)
            (assign.insert (toLiteral (-clits[i])).1 (toLiteral (-clits[i])).2)
            (trailLen + 1) hlt (by omega)
            (phase1_step_insert hlt hlit hinv (hcases.2.2 ⟨hneg, hpos⟩).1)
        · grind
      · simp only [↓reduceIte]
        exact ⟨fun _ => phase1_step_tautology hlt hinv (hcases.2.1 ⟨hneg, hpos⟩),
          fun _ _ h => (nomatch h)⟩
    · simp only [↓reduceIte]
      exact rupPhase1Pure_loop_sound hvalid rem (i + 1) assign trailLen hlt (by omega)
        (phase1_step_already_falsified hlt hinv (hcases.1 hneg))

private theorem rupInnerPure_loop_sound {mv : Nat} {alits : List (BitVec 64)} {F : CNF Nat}
    {initAssign curAssign : Assignment}
    (hvalid : ∀ x ∈ alits, IsValidLit mv x)
    (hcl : CNF.EntailsClause F (toClause alits))
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF)) :
    ∀ (rem i : Nat) (unit : BitVec 64) (assign : Assignment) (trailLen : Nat)
      (unit' : BitVec 64) (vals' : List (BitVec 64)) (trailLen' : Nat),
      i ≤ alits.length → rem = alits.length - i →
      InnerSt mv alits curAssign i unit assign →
      rupInnerPure mv (alits.drop i) unit (assignBytes mv assign) trailLen =
        some (unit', vals', trailLen') →
      ((unit' != 0) = false ∧ CNF.Unsat (F ++ initAssign.toCNF)) ∨
      ((unit' != 0) = true ∧ ∃ assign', vals' = assignBytes mv assign' ∧
        CNF.Entails (F ++ initAssign.toCNF) (F ++ assign'.toCNF))
  | 0, i, unit, assign, trailLen, unit', vals', trailLen', hi, hrem, hst, hres => by
    obtain rfl : i = alits.length := by omega
    rw [List.drop_length, rupInnerPure_nil] at hres
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
    rw [List.drop_eq_getElem_cons hlt] at hres
    rw [rupInnerPure_cons, assignBytes_getD assign hlit] at hres
    dsimp only at hres
    cases hneg : (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]).slt 0
    · simp only [hneg, Bool.false_eq_true, ↓reduceIte] at hres
      let stepUnit : Option (BitVec 64 × List (BitVec 64) × Nat) :=
        if evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] == 0 then
          if trailLen == mv + 1 then none
          else
            rupInnerPure mv (alits.drop (i + 1)) alits[i]
              ((assignBytes mv assign).set (bvAbs alits[i]).toNat (bvSignByte alits[i]))
              (trailLen + 1)
        else
          rupInnerPure mv (alits.drop (i + 1)) alits[i] (assignBytes mv assign) trailLen
      obtain ⟨hu_cases, hres_su⟩ :
          (unit = 0 ∨ unit = alits[i]) ∧ stepUnit = some (unit', vals', trailLen') := by
        rcases hst with ⟨rfl, _⟩ | ⟨hu, _, _⟩
        · grind
        · rw [bne_iff_ne.mpr hu] at hres; grind
      dsimp only [stepUnit] at hres_su
      cases hvz : (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] == 0)
      · simp only [hvz, Bool.false_eq_true, ↓reduceIte] at hres_su
        have hpos : (0 : BitVec 64).slt
            (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]) = true := by grind
        exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) alits[i] assign trailLen
          unit' vals' trailLen' hlt (by omega)
          (innerSt_step_satisfied hlt hlit hst hu_cases (hcases.2.1 ⟨hneg, hpos⟩)) hres_su
      · have hv0 : evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] = 0 :=
          eq_of_beq hvz
        have hun : assign.get? (toLiteral alits[i]).1 = none :=
          (hcases.2.2 ⟨hneg, by rw [hv0]; decide⟩).1
        simp only [hvz, ↓reduceIte] at hres_su
        cases hfull : (trailLen == mv + 1)
        · simp only [hfull, Bool.false_eq_true, ↓reduceIte] at hres_su
          obtain ⟨rfl, rfl, hst'⟩ := innerSt_step_unassigned hlt hlit hst hu_cases hun
          have hidx_pos : (bvAbs alits[i]).toNat = (toLiteral alits[i]).1 := rfl
          rw [hidx_pos, assignBytes_set_insert mv assign hlit] at hres_su
          exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) alits[i]
            (assign.insert (toLiteral alits[i]).1 (toLiteral alits[i]).2)
            (trailLen + 1) unit' vals' trailLen' hlt (by omega) hst' hres_su
        · simp [hfull] at hres_su
    · simp only [hneg, ↓reduceIte] at hres
      cases heq : (unit == -alits[i])
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
    · rw [rupPhase2Aux_succ, hleb] at hp2; nomatch hp2
    · rw [rupPhase2Aux_succ, hleb] at hp2; nomatch hp2
    rw [rupPhase2Aux_succ_some_nz hleb] at hp2
    cases hodd : ((u_pred + 1) % 2 != 0)
    · rw [hodd] at hp2; simp only [Bool.false_eq_true, ↓reduceIte] at hp2
      by_cases haid : (u_pred + 1) / 2 < id
      · simp only [haid, ↓reduceIte] at hp2
        rcases htbl : table[(u_pred + 1) / 2]? with _ | _ | alits
        · rw [htbl] at hp2; nomatch hp2
        · rw [htbl] at hp2; nomatch hp2
        rw [htbl] at hp2; dsimp only at hp2
        obtain ⟨halits_valid, halits_ent⟩ := htable ((u_pred + 1) / 2) haid alits htbl
        rcases hinner : rupInnerPure mv alits 0 (assignBytes mv curAssign) trailLen with
          _ | ⟨unit, vals', trailLen'⟩
        · rw [hinner] at hp2; nomatch hp2
        rw [hinner] at hp2; dsimp only at hp2
        have hsound := rupInnerPure_loop_sound halits_valid halits_ent hent
          alits.length 0 0 curAssign trailLen unit vals' trailLen'
          (Nat.zero_le _) (by simp) (Or.inl ⟨rfl, rfl, by simp⟩) (by simpa using hinner)
        rcases hsound with ⟨_, hunsat⟩ | ⟨hu_t, assign', rfl, hent'⟩
        · exact hunsat
        · simp only [hu_t, ↓reduceIte] at hp2
          exact rupPhase2Aux_sound htable fuel assign' trailLen' bs' bs_out hent' hp2
      · simp [haid] at hp2
    · rw [hodd] at hp2; nomatch hp2

theorem rupCheckPure_sound {mv id : Nat} {clits : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8} {F : CNF Nat}
    (_hmv : mv < dimacsBound)
    (hclits : ∀ x ∈ clits, IsValidLit mv x)
    (htable : ∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
      (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits))
    (hrup : rupCheckPure mv id clits table bs = some bs') :
    CNF.EntailsClause F (toClause clits) := by
  rw [rupCheckPure_def] at hrup
  rw [← assignBytes_empty mv] at hrup
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
