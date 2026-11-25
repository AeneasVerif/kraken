module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof3
import all Kraken.Mem
import all Kraken.Separation

/-!
# Signed `Int` Conversion Proofs (`lcnf_int_conv_wp`, `Milestone R1`, Part 6)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open BigNumRt

local macro "sep_ac" : tactic =>
  `(tactic| exact sep_cast_ac (by assumption) (by ac_rfl))

local macro "sep_use " t:term : tactic =>
  `(tactic| exact sep_cast_ac $t (by ac_rfl))

private abbrev mkMpz1Obj (p : BitVec 64) (other : Nat) (limbs : List (BitVec 64)) : LcnfObj :=
  { addr := p, rc := 1#32, csSz := 24, other := other, tag := mpzTag,
    cap := 1, arrSize := 1, limbs := limbs }

private theorem mem_of_cell64 {a v : BitVec 64} {m : Mem 64} (h : cell64 a v m) : a ∈ m := by
  by_cases hmem : a ∈ m
  · exact hmem
  · have hget : m.get? a = none := by
      rw [Std.ExtHashMap.get?_eq_getElem?]
      exact Std.ExtHashMap.getElem?_eq_none hmem
    have h1 : (cell64 a v ⋆ emp) m := by rw [sep_emp]; exact h
    have hld := loadVal_cell64 h1
    have hnone := loadVal_of_unmapped m i64 a ⟨0, by decide, by simpa using hget⟩
    rw [hld] at hnone
    cases hnone

private theorem lcnfObjMem_cell64 {o : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (lcnfObjMem o ⋆ R) m) : ∃ P, (cell64 o.addr o.header ⋆ P) m := by
  dsimp only [lcnfObjMem] at h
  split at h
  · repeat rw [sep_assoc] at h
    exact ⟨_, h⟩
  · split at h
    · repeat rw [sep_assoc] at h
      exact ⟨_, h⟩
    · split at h
      · repeat rw [sep_assoc] at h
        exact ⟨_, h⟩
      · split at h
        · repeat rw [sep_assoc] at h
          exact ⟨_, h⟩
        · split at h
          · repeat rw [sep_assoc] at h
            exact ⟨_, h⟩
          · repeat rw [sep_assoc] at h
            exact ⟨_, h⟩

private theorem lcnfObjMem_mem_head {o : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (lcnfObjMem o ⋆ R) m) : o.addr ∈ m := by
  rcases lcnfObjMem_cell64 h with ⟨P, m1, m2, hun, _, hm1, _⟩
  exact hun ▸ Std.ExtHashMap.mem_union_of_left (mem_of_cell64 hm1)

private theorem lcnfHeap_addr_nodup : ∀ {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64},
    (lcnfHeap objs ⋆ R) m → (objs.map LcnfObj.addr).Nodup
  | [], _, _, _ => List.nodup_nil
  | o :: os, R, m, h => by
    rw [lcnfHeap, sep_assoc] at h
    have hnd : (os.map LcnfObj.addr).Nodup := by
      have h' : (lcnfHeap os ⋆ (lcnfObjMem o ⋆ R)) m := by
        rw [sep_comm (lcnfObjMem o), sep_assoc, sep_comm R] at h
        exact h
      exact lcnfHeap_addr_nodup h'
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩
    rcases List.mem_map.mp hmem with ⟨o', ho', had⟩
    have ⟨idx, hlt, hidx⟩ := List.mem_iff_getElem.mp ho'
    rw [lcnfHeap_focus os hlt, hidx, sep_assoc (lcnfObjMem o')] at h
    rcases h with ⟨m1, m2, _, hinter, hm1, hm2⟩
    have ha1 : o.addr ∈ m1 := lcnfObjMem_mem_head (R := emp) (by rw [sep_emp]; exact hm1)
    have ha2 : o.addr ∈ m2 := had ▸ lcnfObjMem_mem_head hm2
    have hai : o.addr ∈ m1.inter m2 := Std.ExtHashMap.mem_inter_iff.mpr ⟨ha1, ha2⟩
    rw [hinter] at hai
    exact Std.ExtHashMap.not_mem_empty hai

private theorem mem_addr_nodup_eq {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup) :
    ∀ {o1 o2 : LcnfObj}, o1 ∈ objs → o2 ∈ objs → o1.addr = o2.addr → o1 = o2 := by
  induction objs with
  | nil => simp
  | cons x xs ih =>
    intro o1 o2 h1 h2 had
    have ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exact False.elim (hx (List.mem_map.mpr ⟨o2, h2', had.symm⟩))
    · exact False.elim (hx (List.mem_map.mpr ⟨o1, h1', had⟩))
    · exact ih hxs h1' h2' had

private theorem nonPersistReach_of_mpz {objs : List LcnfObj} {a : BitVec 64}
    (hnd : (objs.map LcnfObj.addr).Nodup)
    (hmpz : ∃ objA ∈ objs, objA.addr = a ∧ objA.tag = mpzTag)
    {x : BitVec 64} (hreach : NonPersistReach objs a x) : x = a := by
  induction hreach with
  | refl _ => rfl
  | @step _ _ _ hstep _ _ ih =>
    subst ih
    rcases hmpz with ⟨objA, hAmem, hAaddr, hAtag⟩
    rcases hstep with ⟨o, homem, hoaddr, hv⟩
    have ho_eq : o = objA := mem_addr_nodup_eq hnd homem hAmem (hoaddr.trans hAaddr.symm)
    subst ho_eq
    simp [LcnfObj.childFields, hAtag, mpzTag, closureTag, arrayTag] at hv

private theorem decColdRel_preserves_of_mpz {objs objs' : List LcnfObj} {a : BitVec 64}
    (hnd : (objs.map LcnfObj.addr).Nodup)
    (hmpz : ∃ objA ∈ objs, objA.addr = a ∧ objA.tag = mpzTag)
    (hdec : DecColdRel a objs objs') :
    ∀ o ∈ objs, o.addr ≠ a →
      ∃ o' ∈ objs', o'.addr = o.addr ∧ o'.tag = o.tag ∧ o'.other = o.other ∧
        o'.arrSize = o.arrSize ∧ o'.cap = o.cap ∧ o'.limbs = o.limbs ∧ o'.Wf := by
  rcases hdec with ⟨_, hwf, _, _, hback, _, _, hzero, hpos⟩
  intro o ho hne
  have ho_wf := hwf o ho
  have hex : ∃ o' ∈ objs', o'.addr = o.addr := by
    by_cases hrc : o.rc = 0#32
    · rcases hzero o ho hrc with ⟨o', ho', had', _⟩
      exact ⟨o', ho', had'⟩
    · have hrc_pos : 0 < o.rc.toInt := by
        have h0 : 0 ≤ o.rc.toInt := ho_wf.2.2.1
        by_cases hlt : 0 < o.rc.toInt
        · exact hlt
        · have hzero_int : o.rc.toInt = 0 := by omega
          apply False.elim (hrc ?_)
          apply BitVec.eq_of_toInt_eq
          simpa using hzero_int
      have hnotfreed : ¬(o ∈ freedObjs objs objs') := by
        intro hfr
        have hrch := ((hpos o ho hrc_pos).2 hfr).2
        exact hne (nonPersistReach_of_mpz hnd hmpz hrch)
      simp only [freedObjs, List.mem_filter, Bool.not_eq_true', Bool.eq_false_iff,
        List.contains_eq_mem, List.mem_map] at hnotfreed
      by_cases hex' : ∃ o' ∈ objs', o'.addr = o.addr
      · exact hex'
      · exact False.elim (hnotfreed ⟨ho, by simp [hex']⟩)
  rcases hex with ⟨o', ho', had'⟩
  rcases hback o' ho' with ⟨o'wf, _, o0, ho0, had0, _, hoth, htag, _, _, hcap, hsz, _, _, _, hlimbs,
    _⟩
  have ho_eq : o0 = o := mem_addr_nodup_eq hnd ho0 ho (had0.trans had')
  subst ho_eq
  exact ⟨o', ho', had', htag, hoth, hsz, hcap, hlimbs, o'wf⟩

private theorem decNatRel_preserves_of_mpz {a : BitVec 64} {st st' : RtC0State}
    {objs objs' : List LcnfObj} (hha : (a &&& 1#64) = 0#64)
    (hwf : ∀ o ∈ objs, o.Wf) (hnd : (objs.map LcnfObj.addr).Nodup)
    (hmpz : ∃ objA ∈ objs, objA.addr = a ∧ objA.tag = mpzTag)
    (hdec : DecNatRel a st st' objs objs') :
    ∀ o ∈ objs, o.addr ≠ a →
      ∃ o' ∈ objs', o'.addr = o.addr ∧ o'.tag = o.tag ∧ o'.other = o.other ∧
        o'.arrSize = o.arrSize ∧ o'.cap = o.cap ∧ o'.limbs = o.limbs ∧ o'.Wf := by
  rcases hdec with ⟨hne, _⟩ | ⟨_, _, _, _, _, rfl, rfl⟩ | ⟨_, i, hi, had_i, _, rfl, rfl⟩ | ⟨_, _, _,
    hcold⟩
  · exact absurd hha hne
  · intro o ho _
    exact ⟨o, ho, rfl, rfl, rfl, rfl, rfl, rfl, hwf o ho⟩
  · intro o ho hne
    rcases List.mem_iff_getElem.mp ho with ⟨j, hj, rfl⟩
    have hne_ji : j ≠ i := fun hji => by subst hji; exact hne had_i
    have hmem : objs[j] ∈ objs.set i (objs[i].withRc (objs[i].rc - 1#32)) := by
      refine List.mem_iff_getElem.mpr ⟨j, by simpa using hj, ?_⟩
      simp [List.getElem_set_ne (Ne.symm hne_ji)]
    exact ⟨objs[j], hmem, rfl, rfl, rfl, rfl, rfl, rfl, hwf objs[j] (List.getElem_mem hj)⟩
  · exact decColdRel_preserves_of_mpz hnd hmpz hcold

private theorem bv64_ofInt_small_enc {a : BitVec 64}
    (hlo : -(2 ^ 62 : Int) ≤ a.toInt) (hhi : a.toInt < 2 ^ 62) :
    (a <<< (1#64 : BitVec 64) ||| 1#64) = BitVec.ofInt 64 (2 * a.toInt + 1) := by
  by_cases hnonneg : 0 ≤ a.toInt
  · have hlt : a.toNat < 2 ^ 62 := by
      rw [BitVec.toInt_eq_toNat_cond] at hnonneg hhi
      split at hnonneg <;> omega
    have hto : (a.toNat : Int) = a.toInt := by
      rw [BitVec.toInt_eq_toNat_cond]
      split
      · rfl
      · omega
    rw [← hto]
    exact bv64_ofInt_pos_enc hlt
  · have hneg : a.toInt < 0 := by omega
    let x : BitVec 64 := 0#64 - a
    have ha_eq : a = 0#64 - x := by simp [x]
    have hx_le : x.toNat ≤ 2 ^ 62 := by
      have ha_ge : 2 ^ 63 ≤ a.toNat := by
        rw [BitVec.toInt_eq_toNat_cond] at hneg
        split at hneg <;> omega
      have ha_int : a.toInt = (a.toNat : Int) - 2 ^ 64 := by
        rw [BitVec.toInt_eq_toNat_cond]
        split
        · omega
        · rfl
      have hx_nat : x.toNat = 2 ^ 64 - a.toNat := by
        simp only [x, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      omega
    have hx_int : -((x.toNat : Int)) = a.toInt := by
      have ha_ge : 2 ^ 63 ≤ a.toNat := by
        rw [BitVec.toInt_eq_toNat_cond] at hneg
        split at hneg <;> omega
      have ha_int : a.toInt = (a.toNat : Int) - 2 ^ 64 := by
        rw [BitVec.toInt_eq_toNat_cond]
        split
        · omega
        · rfl
      have hx_nat : x.toNat = 2 ^ 64 - a.toNat := by
        simp only [x, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      omega
    rw [← hx_int, ha_eq]
    exact bv64_ofInt_neg_enc hx_le

private theorem bv64_neg_abs_of_slt {a : BitVec 64} (hlt : a.toInt < 0) :
    (0#64 - a).toNat = a.toInt.natAbs ∧ 0#64 - a ≠ 0#64 := by
  have ha_ge : 2 ^ 63 ≤ a.toNat := by
    rw [BitVec.toInt_eq_toNat_cond] at hlt
    split at hlt <;> omega
  have ha_int : a.toInt = (a.toNat : Int) - 2 ^ 64 := by
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · omega
    · rfl
  have hsub : (0#64 - a).toNat = 2 ^ 64 - a.toNat := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine ⟨by omega, fun h => ?_⟩
  have h0 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h0
  omega

private theorem bv64_sge0_toNat {a : BitVec 64} (hge : 0 ≤ a.toInt) :
    a.toNat = a.toInt.natAbs := by
  rw [BitVec.toInt_eq_toNat_cond] at hge ⊢
  split at hge <;> omega

private theorem natAbs_lt_2p64_of_bv64 {a : BitVec 64} : a.toInt.natAbs ≤ 2 ^ 63 := by
  have hlo := BitVec.le_toInt a
  have hhi := @BitVec.toInt_lt 64 a
  omega

private theorem mpz_single_limb_intRep
    {p : BitVec 64} {mag : BitVec 64} {negBit : Bool} {z : Int}
    (_hpa : (p &&& 1#64) = 0#64)
    (hobj0 : (mkMpz1Obj p 0 [0#64]).Wf)
    (hmag : mag.toNat = z.natAbs) (hnz : mag ≠ 0#64)
    (hsign : negBit = true ↔ z < 0) (hrange : z < -(2 ^ 62 : Int) ∨ 2 ^ 62 ≤ z) :
    let obj : LcnfObj := mkMpz1Obj p (if negBit then 1 else 0) [mag]
    obj.Wf ∧ mpzIntCanon obj z := by
  intro obj
  have hoth_lt : obj.other < 256 := by cases negBit <;> simp [obj]
  have hwf : obj.Wf := by
    rcases hobj0 with ⟨h1, h2, h3, h4, _, h6, h7, h8, h9, hrest⟩
    simp only [mpzTag, ↓reduceIte] at hrest ⊢
    have htb : obj.totalBytes = 24 := by
      simp only [obj, LcnfObj.totalBytes, BigNumRt.mpzTag, BigNumRt.arrayTag,
        BigNumRt.sarrayTag, BigNumRt.stringTag, show (250 : Nat) ≠ 246 by decide,
        show (250 : Nat) ≠ 248 by decide, show (250 : Nat) ≠ 249 by decide, ↓reduceIte]
    have htb0 : (mkMpz1Obj p 0 [0#64]).totalBytes = 24 := by
      simp only [LcnfObj.totalBytes, BigNumRt.mpzTag, BigNumRt.arrayTag,
        BigNumRt.sarrayTag, BigNumRt.stringTag, show (250 : Nat) ≠ 246 by decide,
        show (250 : Nat) ≠ 248 by decide, show (250 : Nat) ≠ 249 by decide, ↓reduceIte]
    refine ⟨h1, h2, h3, h4, hoth_lt, h6, ?_, ?_, ?_, by simp [obj], hrest.2.1, hrest.2.2⟩
    · rw [htb]; rw [htb0] at h7; exact h7
    · rw [htb]; rw [htb0] at h8; exact h8
    · rw [htb]
  refine ⟨hwf, hwf, rfl, ?_, rfl, by simp [obj], by simp [obj, mpzMaxLimbs], ?_, ?_, ?_, hrange⟩
  · cases negBit <;> simp [obj]
  · simpa [obj] using hnz
  · simp [obj, limbsVal, hmag]
  · constructor
    · intro h1; apply hsign.mp
      cases negBit <;> simp [obj] at h1 ⊢
    · intro hz; have ht := hsign.mpr hz
      simp [obj, ht]

private theorem alloc1_mpz_call_wp {rt : BitVec 64} {m : Mem 64} {rs : List Ty}
    {Q : Post rs} {X : XPost} {k : Tup Val [i64] → Expr Val Cont rs}
    (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64)) (R : Mem 64 → Prop)
    (hb : st.Bounded48) (halloc : canAllocBytes st 24)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ R) m)
    (hk : ∀ (p : BitVec 64) (st' : RtC0State) (m1 : Mem 64),
      (mkMpz1Obj p 0 [0#64]).Wf → (p &&& 1#64) = 0#64 → st'.PreservesMeta st →
      st'.rem ≤ st.rem → st'.Bounded48 →
      (bigNumRtInv rt st' scr scrLimbs ⋆ lcnfObjMem (mkMpz1Obj p 0 [0#64]) ⋆ R) m1 →
      wp rtR1Env Q X (k (p, ())) m1) :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "lcnf_nat_alloc" (Arg.var rt, Arg.imm 1,
        ()) k) m := by
  refine wp_call_ret1 _ _ (fun p m1 =>
    ∃ (st' : RtC0State),
      let obj0 : LcnfObj := mkMpz1Obj p 0 [0#64]
      obj0.Wf ∧ (p &&& 1#64) = 0#64 ∧ st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧ st'.Bounded48 ∧
      (bigNumRtInv rt st' scr scrLimbs ⋆ lcnfObjMem obj0 ⋆ R) m1) ?_ ?_
  · refine rtR1Env_lcnf_nat_alloc ?_
    dsimp only [lcnfNatAllocSpec, vals, Arg.val]
    have hmax : max 1 (BitVec.toNat (1 : BitVec 64)) = 1 := by decide
    have hby : 16 + 8 * max 1 (BitVec.toNat (1 : BitVec 64)) = 24 := by decide
    refine ⟨st, cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrLimbs ⋆ R,
      by decide, hb, by rw [hby]; exact halloc, ?_, fun p st' m1 hobj0 hpa hpm hrem hb' hm1 => ?_⟩
    · dsimp only [bigNumRtInv] at hm ⊢
      exact (by ac_rfl : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrLimbs) ⋆ R =
        (rtC0Inv rt st ⋆ (cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 scr scrLimbs ⋆ R))) ▸ hm
    · have hif : (if 24 < 65536 then 24 else 0) = 24 := by decide
      have hrep1 : List.replicate 1 (0#64 : BitVec 64) = [0#64] := rfl
      rw [hby, hmax, hif, hrep1] at hobj0 hm1
      refine ⟨st', hobj0, hpa, hpm, hrem, hb', ?_⟩
      dsimp only [bigNumRtInv]
      exact (by ac_rfl : (rtC0Inv rt st' ⋆ lcnfObjMem _ ⋆
        (cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 scr scrLimbs ⋆ R)) =
        ((rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 scr scrLimbs) ⋆ lcnfObjMem _ ⋆ R)) ▸ hm1
  · rintro p m1 ⟨st', hobj0, hpa, hpm, hrem, hb', hm1⟩
    exact hk p st' m1 hobj0 hpa hpm hrem hb' hm1

private theorem alloc1_store_limb_ret_wp {rt p mag : BitVec 64} {st : RtC0State}
    {scr : BitVec 64} {scrLimbs : List (BitVec 64)} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (negBit : Bool) (z : Int) (hwf : BigNumRtWf rt st scr scrLimbs)
    (hpa : (p &&& 1#64) = 0#64)
    (hobj0 : (mkMpz1Obj p 0 [0#64]).Wf)
    (hmag : mag.toNat = z.natAbs) (hnz : mag ≠ 0#64)
    (hsign : negBit = true ↔ z < 0) (hrange : z < -(2 ^ 62 : Int) ∨ 2 ^ 62 ≤ z)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆
      lcnfObjMem (mkMpz1Obj p (if negBit then 1 else 0) [0#64]) ⋆
      lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.imm 2, Arg.imm 8, ()) }
        fun p_9 => Expr.let_
          { sig := [i64, i64], code := OpCode.add i64,
            args := (Arg.var p, Arg.var p_9.fst, ()) } fun p_10 =>
        Expr.store (t := i64) (Arg.var (mag : Val i64)) (Arg.var p_10.fst) (Expr.ret (Arg.var p,
          ()))) m := by
  c0_let_simp
  let obj_pre : LcnfObj := mkMpz1Obj p (if negBit then 1 else 0) [0#64]
  let obj1 : LcnfObj := { obj_pre with limbs := [mag] }
  have hm_arr : (array64 (p + 16#64) [0#64] ⋆
      (bigNumRtInv rt st scr scrLimbs ⋆ cell64 p obj_pre.header ⋆
        cell64 (p + 8#64) obj_pre.mpzMeta ⋆ lcnfHeap objs ⋆ R)) m := by
    rw [lcnfObjMem_mpz_eq rfl] at hm
    exact (by ac_rfl : (bigNumRtInv rt st scr scrLimbs ⋆
      (cell64 p obj_pre.header ⋆ cell64 (p + 8#64) obj_pre.mpzMeta ⋆
        array64 (p + 16#64) [0#64]) ⋆ lcnfHeap objs ⋆ R) =
      (array64 (p + 16#64) [0#64] ⋆
        (bigNumRtInv rt st scr scrLimbs ⋆ cell64 p obj_pre.header ⋆
          cell64 (p + 8#64) obj_pre.mpzMeta ⋆ lcnfHeap objs ⋆ R))) ▸ hm
  refine wp_store_array64 (base := p + 16#64) (xs := [0#64]) (i := 0)
    (by simp) (by decide) hm_arr ?_
  intro m2 hm2
  rw [wp_ret]
  dsimp only [vals, Arg.val]
  have hcanon := mpz_single_limb_intRep hpa hobj0 hmag hnz hsign hrange
  have hrep' : intRep p z (obj1 :: objs) := by
    have hn : ¬(-(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62) := by omega
    simp only [intRep, hn, ↓reduceIte]
    exact ⟨hpa, obj1, List.mem_cons_self, rfl, hcanon.2⟩
  have hm2' : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap (obj1 :: objs) ⋆ R) m2 := by
    have heq_hdr : obj1.header = obj_pre.header := rfl
    have heq_meta : obj1.mpzMeta = obj_pre.mpzMeta := rfl
    have hobj1_mem : lcnfObjMem obj1 =
        cell64 p obj1.header ⋆ cell64 (p + 8#64) obj1.mpzMeta ⋆ array64 (p + 16#64) [mag] :=
      lcnfObjMem_mpz_eq rfl
    rw [lcnfHeap_cons_eq, hobj1_mem, heq_hdr, heq_meta]
    dsimp only [Arg.val] at hm2
    have hset : ([0#64] : List (BitVec 64)).set 0 mag = [mag] := rfl
    rw [hset] at hm2
    exact (by ac_rfl : (array64 (p + 16#64) [mag] ⋆
        (bigNumRtInv rt st scr scrLimbs ⋆ cell64 p obj_pre.header ⋆
          cell64 (p + 8#64) obj_pre.mpzMeta ⋆ lcnfHeap objs ⋆ R)) =
      (bigNumRtInv rt st scr scrLimbs ⋆
        ((cell64 p obj_pre.header ⋆ cell64 (p + 8#64) obj_pre.mpzMeta ⋆
          array64 (p + 16#64) [mag]) ⋆ lcnfHeap objs) ⋆ R)) ▸ hm2
  exact hQ p st scrLimbs (obj1 :: objs) m2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (Nat.le_refl _) hwf hrep' (fun _ h => List.mem_cons_of_mem _ h) hm2'

private theorem alloc1_set_neg_header_wp {p : BitVec 64} {m : Mem 64} {rs : List Ty}
    {Q : Post rs} {X : XPost} {k : Expr Val Cont rs}
    (R : Mem 64 → Prop)
    (hobj0 : (mkMpz1Obj p 0 [0#64]).Wf)
    (hm : (lcnfObjMem (mkMpz1Obj p 0 [0#64]) ⋆ R) m)
    (hk : ∀ m', (lcnfObjMem (mkMpz1Obj p 1 [0#64]) ⋆ R) m' → wp rtR1Env Q X k m') :
    wp rtR1Env Q X
      (Expr.load i64 (Arg.var p) fun ld =>
        Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 48, ()) } fun p_9 =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.shl i64,
            args := (Arg.imm 1, Arg.var p_9.fst, ()) } fun p_10 =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.or i64,
            args := (Arg.var ld, Arg.var p_10.fst, ()) } fun p_11 =>
        Expr.store (Arg.var p_11.fst) (Arg.var p) k) m := by
  let obj0 : LcnfObj := mkMpz1Obj p 0 [0#64]
  let obj1 : LcnfObj := { obj0 with other := 1 }
  have hm0 : (cell64 p obj0.header ⋆ (cell64 (p + 8#64) obj0.mpzMeta ⋆
      array64 (p + 16#64) [0#64] ⋆ R)) m := by
    rw [lcnfObjMem_mpz_eq rfl] at hm
    exact (by ac_rfl : ((cell64 p obj0.header ⋆ cell64 (p + 8#64) obj0.mpzMeta ⋆
        array64 (p + 16#64) [0#64]) ⋆ R) =
      (cell64 p obj0.header ⋆ (cell64 (p + 8#64) obj0.mpzMeta ⋆
        array64 (p + 16#64) [0#64] ⋆ R))) ▸ hm
  refine wp_load_cell64 hm0 ?_
  c0_let_simp
  refine wp_store_cell64 hm0 ?_
  intro m' hm'
  change (cell64 p (obj0.header ||| 1#64 <<< 48#64) ⋆
    (cell64 (p + 8#64) obj0.mpzMeta ⋆ array64 (p + 16#64) [0#64] ⋆ R)) m' at hm'
  have hhdr : obj0.header ||| 1#64 <<< 48#64 = obj1.header :=
    LcnfObj.header_or_other_one obj0 hobj0.2.2.2.1 rfl
  rw [hhdr] at hm'
  apply hk m'
  rw [lcnfObjMem_mpz_eq rfl]
  exact (by ac_rfl : (cell64 p obj1.header ⋆ (cell64 (p + 8#64) obj0.mpzMeta ⋆
      array64 (p + 16#64) [0#64] ⋆ R)) =
    ((cell64 p obj1.header ⋆ cell64 (p + 8#64) obj1.mpzMeta ⋆
      array64 (p + 16#64) [0#64]) ⋆ R)) ▸ hm'

private theorem lcnf_int_conv_ofNat_wp {rt a : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (R : Mem 64 → Prop)
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (aVal : Nat) (z : Int) (hz : z = ↑aVal) (hrep : natRep a aVal objs)
    (halloc : 2 ^ 62 ≤ aVal ∧ aVal < 2 ^ 63 → canAllocBytes st 24)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.let_ { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var a, Arg.imm 1, ()) }
        fun p_2 => Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool (by decide),
            args := (Arg.var p_2.fst, Arg.imm 0, ()) }
          fun p_3 => Expr.jnz (Arg.var p_3.fst)
            (Expr.let_
              { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_4 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.lshr i64,
                  args := (Arg.var a, Arg.var p_4.fst, ()) } fun p_5 =>
              Expr.let_
                { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 62, ()) } fun p_6 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.shl i64,
                  args := (Arg.imm 1, Arg.var p_6.fst, ()) } fun p_7 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (by decide),
                  args := (Arg.var p_5.fst, Arg.var p_7.fst, ()) } fun p_8 =>
              Expr.jnz (Arg.var p_8.fst)
                (Expr.let_
                  { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.shl i64,
                      args := (Arg.var p_5.fst, Arg.var p.fst, ()) } fun p =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.or i64,
                      args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
                        Expr.ret (Arg.var p.fst, ()))
                (Expr.call (as := [i64, i64]) (bs := [i64]) "lcnf_nat_alloc"
                    (Arg.var rt, Arg.imm 1, ()) fun p =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.imm 2, Arg.imm 8, ()) } fun p_9 =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p.fst, Arg.var p_9.fst, ()) } fun p_10 =>
                  Expr.store (t := i64) (Arg.var p_5.fst) (Arg.var p_10.fst)
                    (Expr.ret (Arg.var p.fst, ()))))
            (Expr.ret (Arg.var a, ()))) m := by
  c0_let_simp
  by_cases ha_tag : a &&& 1#64 = 0#64
  · refine jnz_false (by simp [ha_tag]) ?_
    rw [wp_ret]
    dsimp only [vals, Arg.val]
    have hbig : ¬aVal < 2 ^ 63 := by
      intro hlt
      simp only [natRep, hlt, ↓reduceIte] at hrep
      rw [hrep] at ha_tag
      have hodd : (BitVec.ofNat 64 (2 * aVal + 1) &&& 1#64) = 1#64 := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
        have hlt2 : 2 * aVal + 1 < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hlt2, show (1 : Nat) % 2 ^ 64 = 1 by decide, Nat.and_one_is_mod]
        omega
      rw [hodd] at ha_tag; cases ha_tag
    simp only [natRep, hbig, ↓reduceIte] at hrep
    rcases hrep with ⟨_, obj, hom, had, hcanon⟩
    have hrep_int : intRep a z objs := by
      have hge : ¬(-(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62) := by omega
      simp only [intRep, hge, ↓reduceIte]
      refine ⟨ha_tag, obj, hom, had, ?_⟩
      subst hz; exact mpzNatCanon_to_int hcanon
    exact hQ a st scrLimbs objs m ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (Nat.le_refl _) hwf hrep_int (fun _ h => h) hm
  · refine jnz_true (by simp [ha_tag]) ?_
    c0_let_simp
    have hlt63 : aVal < 2 ^ 63 := by
      by_cases hlt : aVal < 2 ^ 63
      · exact hlt
      · simp only [natRep, hlt, ↓reduceIte] at hrep
        exact False.elim (ha_tag hrep.1)
    simp only [natRep, hlt63, ↓reduceIte] at hrep
    have hv_eq : a >>> 1 = BitVec.ofNat 64 aVal := by
      subst hrep; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hv_eq]
    have hpow62 : ((1 : BitVec 64) <<< 62 : BitVec 64) = BitVec.ofNat 64 (2 ^ 62) := by decide
    rw [hpow62]
    by_cases h62 : aVal < 2 ^ 62
    · have hult : BitVec.ofNat 64 aVal < BitVec.ofNat 64 (2 ^ 62) := by
        change (BitVec.ofNat 64 aVal).toNat < (BitVec.ofNat 64 (2 ^ 62)).toNat
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        exact h62
      refine jnz_true (by simpa [BitVec.ult] using hult) ?_
      c0_let_simp
      have hbv_lt : (BitVec.ofNat 64 aVal).toNat < 2 ^ 62 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h62
      have henc := bv64_ofInt_pos_enc hbv_lt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at henc
      have hrep_int : intRep ((BitVec.ofNat 64 aVal <<< 1) ||| 1#64) z objs := by
        have hin : -(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62 := by omega
        simp only [intRep, hin]
        subst hz
        exact henc
      exact hQ _ st scrLimbs objs m ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (Nat.le_refl _) hwf hrep_int (fun _ h => h) hm
    · have hnult : ¬(BitVec.ofNat 64 aVal < BitVec.ofNat 64 (2 ^ 62)) := by
        change ¬((BitVec.ofNat 64 aVal).toNat < (BitVec.ofNat 64 (2 ^ 62)).toNat)
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      refine jnz_false (by simpa [BitVec.ult] using hnult) ?_
      have hm_assoc : (bigNumRtInv rt st scr scrLimbs ⋆ (lcnfHeap objs ⋆ R)) m :=
        (by rw [sep_assoc] : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) =
          (bigNumRtInv rt st scr scrLimbs ⋆ (lcnfHeap objs ⋆ R))) ▸ hm
      refine alloc1_mpz_call_wp st scr scrLimbs (lcnfHeap objs ⋆ R) hwf.1
        (halloc ⟨by omega, hlt63⟩) hm_assoc ?_
      intro p st' m1 hobj0 hpa hpmeta hrem hb' hm1
      have hmag_nat : (BitVec.ofNat 64 aVal).toNat = z.natAbs := by
        subst hz; simp only [BitVec.toNat_ofNat, Int.natAbs_natCast]
        exact Nat.mod_eq_of_lt (by omega)
      have hmag_nz : BitVec.ofNat 64 aVal ≠ 0#64 := by
        intro h; have ht := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at ht; rw [Nat.mod_eq_of_lt (by omega)] at ht; omega
      have hwf' : BigNumRtWf rt st' scr scrLimbs :=
        ⟨hb', hwf.2.1, hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩
      have hm1' : (bigNumRtInv rt st' scr scrLimbs ⋆
          lcnfObjMem (mkMpz1Obj p (if false then 1 else 0) [0#64]) ⋆
          lcnfHeap objs ⋆ R) m1 := by
        exact sep_cast_ac hm1 (by ac_rfl)
      refine alloc1_store_limb_ret_wp false z hwf' hpa hobj0 hmag_nat hmag_nz
        (by
          constructor
          · intro h; cases h
          · intro hz'; omega) (by omega) hm1' ?_
      intro res st2 scrLimbs2 objs2 m2 hpmeta2 hrem2 hwf2 hrep2 hpres2 hm2
      exact hQ res st2 scrLimbs2 objs2 m2 (preservesMeta_trans hpmeta2 hpmeta)
        (Nat.le_trans hrem2 hrem) hwf2 hrep2 hpres2 hm2

private theorem lcnf_int_conv_op2_boxed_wp :
    ∀ {rt op a : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost},
      op.toNat = 2 → a &&& 1#64 = 0#64 → lcnfIntConvSpec (rt, op, a, ()) m Q X →
      Func.wp rtR1Env lcnf_int_conv.body (rt, op, a, ()) m Q X := by
  intro rt op a m Q X hop2 ha_tag ⟨st, scr, scrLimbs, objs, R, hwf, hm, hspec⟩
  change wp rtR1Env Q X (lcnf_int_conv_body Val Cont (rt, op, a, ())) m
  dsimp only [lcnf_int_conv_body]
  c0_let_simp
  have hne1 : (op == 1#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 1); subst h
    decide
  have hne13 : (op == 13#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 13); subst h
    decide
  have hne16 : (op == 16#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 16); subst h
    decide
  have heq2 : (op == 2#64) = true := by
    simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using hop2)
  refine jnz_false hne1 ?_; c0_let_simp
  refine jnz_false hne13 ?_; c0_let_simp
  refine jnz_false hne16 ?_; c0_let_simp
  refine jnz_true heq2 ?_
  simp only [hop2, show (2 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 13 by decide,
    show (2 : Nat) ≠ 16 by decide, ↓reduceIte] at hspec
  rcases hspec with ⟨aVal, hrep, htnMax, hboxPre, _, hQ⟩
  generalize hz : Int.negSucc aVal = z at hQ
  c0_let_simp
  refine jnz_false (by simp [ha_tag]) ?_
  have hbig : ¬aVal < 2 ^ 63 := by
    intro hlt
    simp only [natRep, hlt, ↓reduceIte] at hrep
    rw [hrep] at ha_tag
    have h1 : (BitVec.ofNat 64 (2 * aVal + 1) &&& 1#64).toNat = 0 :=
      congrArg BitVec.toNat ha_tag
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at h1
    have hlt64 : 2 * aVal + 1 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64),
      Nat.and_one_is_mod] at h1
    omega
  simp only [natRep, hbig, ↓reduceIte] at hrep
  rcases hrep with ⟨_, objA, hAmem, hAaddr, hAcanon⟩
  rcases hboxPre (by omega) with ⟨hscrLen, hworkCap, hwfAll, hclosed, hrcSound, hremAlloc⟩
  refine wp_call_ret1 _ _ (fun naW m1 =>
    naW = BitVec.ofNat 64 (limbLenNat aVal) ∧ m1 = m) ?_ ?_
  · refine rtR1Env_bn_nat_len ?_
    dsimp only [bnNatLenSpec, vals, Arg.val]
    refine ⟨aVal, objs, bigNumRtInv rt st scr scrLimbs ⋆ R,
      by simp only [natRep, hbig, ↓reduceIte]; exact ⟨ha_tag, objA, hAmem, hAaddr, hAcanon⟩,
      ?_, rfl, rfl⟩
    exact (by ac_rfl : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) =
      (lcnfHeap objs ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R))) ▸ hm
  · rintro naW m1 ⟨rfl, hm1⟩
    subst m1
    c0_let_simp
    have hna_le : limbLenNat aVal ≤ mpzMaxLimbs :=
      Nat.le_trans (limbLenNat_mono (by omega)) htnMax
    have hna_lt : limbLenNat aVal < 2 ^ 64 := by
      have : mpzMaxLimbs = 33554429 := rfl; omega
    have hnugt : BitVec.ult (33554429#64 : BitVec 64)
        (BitVec.ofNat 64 (limbLenNat aVal)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
      rw [Nat.mod_eq_of_lt hna_lt, Nat.mod_eq_of_lt (by decide : 33554429 < 2 ^ 64)]
      exact Nat.not_lt_of_le hna_le
    refine jnz_false hnugt ?_
    c0_let_simp
    have hadd1_eq : (BitVec.ofNat 64 (limbLenNat aVal) + (1 : BitVec 64)).toNat =
        limbLenNat aVal + 1 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        show BitVec.toNat (1 : BitVec 64) = 1 by decide]
      rw [Nat.mod_eq_of_lt hna_lt,
        Nat.mod_eq_of_lt (by have : mpzMaxLimbs = 33554429 := rfl; omega)]
    refine wp_call_ret1 _ _ (fun scrP m1 => scrP = scr ∧ m1 = m) ?_ ?_
    · refine rtR1Env_bn_require_scratch ?_
      dsimp only [bnRequireScratchSpec, vals, Arg.val]
      refine ⟨scr, BitVec.ofNat 64 scrLimbs.length,
        BigNumRt.rtC0Inv rt st ⋆ array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R,
        hwf.2.2.1, ?_, ?_, rfl, rfl⟩
      · rw [hadd1_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwf.2.2.2.2.1]; exact hscrLen
      · dsimp only [bigNumRtInv] at hm
        exact sep_cast_ac hm (by ac_rfl)
    · rintro scrP m1 ⟨hscrP, hm1⟩
      subst scrP; subst m1
      c0_let_simp
      have hfoc0 : (lcnfHeap objs ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R)) m :=
        sep_cast_ac hm (by ac_rfl)
      rcases lcnfHeap_mpz_focus hAmem hAcanon.2.1 hfoc0 with ⟨idx, hlt, hidx, hm_foc⟩
      have hm_add : (array64 (a + 16#64) objA.limbs ⋆ array64 scr scrLimbs ⋆
          (cell64 objA.addr objA.header ⋆ cell64 (objA.addr + 8#64) objA.mpzMeta ⋆
            lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1)) ⋆
            BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ R)) m := by
        rw [hAaddr]
        rw [hAaddr] at hm_foc
        dsimp only [bigNumRtInv] at hm_foc
        exact sep_cast_ac hm_foc (by ac_rfl)
      have hna_eq_limbs : (BitVec.ofNat 64 (limbLenNat aVal)).toNat = objA.limbs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt]
        rw [← hAcanon.2.2.2.2.2.2.2.1]
        exact limbLenNat_eq_length_of_trimmed (by
          intro h0; have := hAcanon.2.2.2.2.1; rw [h0] at this; simp at this)
          hAcanon.2.2.2.2.2.2.1
      refine wp_call_ret1 _ _ (fun outN m2 =>
        ∃ scrLimbs',
          outN = BitVec.ofNat 64 (limbLenNat (aVal + 1)) ∧
          scrLimbs'.length = scrLimbs.length ∧
          limbsVal (List.take (limbLenNat (aVal + 1)) scrLimbs') = aVal + 1 ∧
          (bigNumRtInv rt st scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m2) ?_ ?_
      · refine rtR1Env_bn_add_one ?_
        dsimp only [bnAddOneSpec, vals, Arg.val]
        refine ⟨objA.limbs, scrLimbs, _,
          by rw [hna_eq_limbs]; exact Nat.le_refl _,
          by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt]; exact hscrLen,
          by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt]
             have : mpzMaxLimbs = 33554429 := rfl; omega,
          hm_add, ?_⟩
        intro outXs' m2 hlenO _ hvalO hm2
        have htake_all : List.take (BitVec.ofNat 64 (limbLenNat aVal)).toNat objA.limbs =
            objA.limbs := by rw [hna_eq_limbs]; simp
        have hsum_eq : limbsVal (List.take (BitVec.ofNat 64 (limbLenNat aVal)).toNat objA.limbs) +
            1 = aVal + 1 := by rw [htake_all, hAcanon.2.2.2.2.2.2.2.1]
        rw [hsum_eq] at hvalO ⊢
        refine ⟨outXs', rfl, hlenO, hvalO, ?_⟩
        rw [← hAaddr] at hm2
        have hm2' : (cell64 objA.addr objA.header ⋆ cell64 (objA.addr + 8#64) objA.mpzMeta ⋆
            array64 (objA.addr + 16#64) objA.limbs ⋆
            (lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1)) ⋆
              (bigNumRtInv rt st scr outXs' ⋆ R))) m2 := by
          dsimp only [bigNumRtInv]
          rw [hlenO]
          exact sep_cast_ac hm2 (by ac_rfl)
        have hrest := lcnfHeap_mpz_restore hlt hidx hAcanon.2.1 hm2'
        exact sep_cast_ac hrest (by ac_rfl)
      · rintro outN m2 ⟨scrLimbs', rfl, hlen', hval', hm2⟩
        have hnd : (objs.map LcnfObj.addr).Nodup :=
          lcnfHeap_addr_nodup (R := bigNumRtInv rt st scr scrLimbs' ⋆ R)
            (sep_cast_ac hm2 (by ac_rfl))
        refine wp_call_ret0 _ _ (fun _ m3 =>
          ∃ st1 objs1,
            st1.PreservesMeta st ∧ st1.rem = st.rem ∧ st1.Bounded48 ∧
            (∀ o ∈ objs, o.addr ≠ a →
              ∃ o' ∈ objs1, o'.addr = o.addr ∧ o'.tag = o.tag ∧ o'.other = o.other ∧
                o'.arrSize = o.arrSize ∧ o'.cap = o.cap ∧ o'.limbs = o.limbs ∧ o'.Wf) ∧
            (bigNumRtInv rt st1 scr scrLimbs' ⋆ lcnfHeap objs1 ⋆ R) m3) ?_ ?_
        · refine rtR1Env_bn_dec_nat ?_
          dsimp only [bnDecNatSpec, vals, Arg.val]
          simp only [ha_tag, ne_eq, not_true_eq_false, ↓reduceIte]
          refine ⟨st, objs, cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
              array64 scr scrLimbs' ⋆ R,
            hworkCap, ?_, ⟨objA, hAmem, hAaddr⟩, hwfAll, hclosed,
            fun o ho had hrc1 => ?_, fun st1 objs1 m3 hdec hm3 => ?_⟩
          · dsimp only [bigNumRtInv] at hm2
            exact sep_cast_ac hm2 (by ac_rfl)
          · have ho_eq := mem_addr_nodup_eq hnd ho hAmem (had.trans hAaddr.symm)
            subst ho_eq; exact hrcSound o ho had hrc1
          · have hpm1 := hdec.preservesMeta
            have hrem1 := hdec.rem_eq
            have hb1 := RtC0State.bounded48_of_preserves hwf.1 hpm1
            have hpres1 := decNatRel_preserves_of_mpz ha_tag hwfAll hnd
              ⟨objA, hAmem, hAaddr, hAcanon.2.1⟩ hdec
            refine ⟨st1, objs1, hpm1, hrem1, hb1, hpres1, ?_⟩
            dsimp only [bigNumRtInv]
            exact sep_cast_ac hm3 (by ac_rfl)
        · rintro ⟨⟩ m3 ⟨st1, objs1, hpm1, hrem1, hb1, hpres1, hm3⟩
          have htn_lt : limbLenNat (aVal + 1) < 2 ^ 64 := by
            have : mpzMaxLimbs = 33554429 := rfl; omega
          have htn_le_scr : limbLenNat (aVal + 1) ≤ scrLimbs'.length := by
            have hmono1 := limbLenNat_add_one_le aVal; omega
          refine wp_call_ret1 _ _ (fun res m4 =>
            ∃ st2 objs2,
              st2.PreservesMeta st1 ∧ st2.rem ≤ st1.rem ∧ st2.Bounded48 ∧
              intRep res z objs2 ∧
              (∀ o ∈ objs1, o ∈ objs2) ∧
              (bigNumRtInv rt st2 scr scrLimbs' ⋆ lcnfHeap objs2 ⋆ R) m4) ?_ ?_
          · refine rtR1Env_bn_int_from_limbs ?_
            dsimp only [bnIntFromLimbsSpec, vals, Arg.val]
            have htn_bv : (BitVec.ofNat 64 (limbLenNat (aVal + 1))).toNat =
                limbLenNat (aVal + 1) := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htn_lt]
            have htrim_eq : trimLenLoop scrLimbs' (limbLenNat (aVal + 1)) =
                limbLenNat (aVal + 1) := by
              rw [← limbLenNat_trimLenLoop htn_le_scr, hval']
            have hval_eq : (if trimLenLoop scrLimbs'
                (BitVec.ofNat 64 (limbLenNat (aVal + 1))).toNat = 0
                then 0 else if (1 : BitVec 64) = 0#64 then
                  ↑(limbsVal (List.take (BitVec.ofNat 64 (limbLenNat (aVal + 1))).toNat scrLimbs'))
                else -↑(limbsVal (List.take (BitVec.ofNat 64 (limbLenNat (aVal + 1))).toNat
                  scrLimbs'))) = z := by
              rw [htn_bv, htrim_eq, hval', ← hz]
              have hpos : limbLenNat (aVal + 1) ≠ 0 :=
                Nat.ne_of_gt (limbLenNat_pos_iff.mpr (Nat.succ_pos aVal))
              simp [hpos, Int.negSucc_eq]
            refine ⟨st1, scrLimbs', objs1, cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆ R,
              by rw [htn_bv]; exact htn_le_scr, by rw [htn_bv]; exact htnMax, hb1,
              fun _ => Or.inr (by rw [htn_bv, htrim_eq, hrem1]; exact hremAlloc),
              ?_, fun res st2 objs2 m4 hpm2 hrem2 hb2 hrep2 _ hbox2 hm4 => ?_⟩
            · dsimp only [bigNumRtInv] at hm3
              exact sep_cast_ac hm3 (by ac_rfl)
            · rw [hval_eq] at hrep2
              have hpres_sub : ∀ o ∈ objs1, o ∈ objs2 := by
                rcases hbox2 (by rw [hval_eq, ← hz]; omega) with ⟨newObj, _, _, rfl⟩
                exact fun _ h => List.mem_cons_of_mem _ h
              refine ⟨st2, objs2, hpm2, hrem2, hb2, hrep2, hpres_sub, ?_⟩
              dsimp only [bigNumRtInv]
              exact sep_cast_ac hm4 (by ac_rfl)
          · rintro res m4 ⟨st2, objs2, hpm2, hrem2, hb2, hrep2, hpres2, hm4⟩
            rw [wp_ret]; dsimp only [vals, Arg.val]
            have hwf2 : BigNumRtWf rt st2 scr scrLimbs' :=
              BigNumRtWf.with_state_len hwf hb2 hlen'
            have hpres_all : ∀ o ∈ objs, o.addr ≠ a →
                ∃ o' ∈ objs2, o'.addr = o.addr ∧ o'.tag = o.tag ∧ o'.other = o.other ∧
                  o'.arrSize = o.arrSize ∧ o'.cap = o.cap ∧ o'.limbs = o.limbs ∧
                  (o.Wf → o'.Wf) := by
              intro o ho hne
              rcases hpres1 o ho hne with ⟨o', ho', h1, h2, h3, h4, h5, h6, h7⟩
              exact ⟨o', hpres2 o' ho', h1, h2, h3, h4, h5, h6, fun _ => h7⟩
            exact hQ res st2 scrLimbs' objs2 m4
              (preservesMeta_trans hpm2 hpm1) (by omega) hwf2 hrep2 hpres_all hm4

private theorem lcnf_int_conv_op2_small_wp :
    ∀ {rt op a : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost},
      op.toNat = 2 → a &&& 1#64 ≠ 0#64 → lcnfIntConvSpec (rt, op, a, ()) m Q X →
      Func.wp rtR1Env lcnf_int_conv.body (rt, op, a, ()) m Q X := by
  intro rt op a m Q X hop2 ha_tag ⟨st, scr, scrLimbs, objs, R, hwf, hm, hspec⟩
  change wp rtR1Env Q X (lcnf_int_conv_body Val Cont (rt, op, a, ())) m
  dsimp only [lcnf_int_conv_body]
  c0_let_simp
  have hne1 : (op == 1#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 1); subst h
    decide
  have hne13 : (op == 13#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 13); subst h
    decide
  have hne16 : (op == 16#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 16); subst h
    decide
  have heq2 : (op == 2#64) = true := by
    simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using hop2)
  refine jnz_false hne1 ?_; c0_let_simp
  refine jnz_false hne13 ?_; c0_let_simp
  refine jnz_false hne16 ?_; c0_let_simp
  refine jnz_true heq2 ?_
  simp only [hop2, show (2 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 13 by decide,
    show (2 : Nat) ≠ 16 by decide, ↓reduceIte] at hspec
  rcases hspec with ⟨aVal, hrep, _, _, hsmallAlloc, hQ⟩
  generalize hz : Int.negSucc aVal = z at hsmallAlloc hQ
  c0_let_simp
  refine jnz_true (by simp [ha_tag]) ?_
  c0_let_simp
  have hlt63 : aVal < 2 ^ 63 := by
    by_cases hlt : aVal < 2 ^ 63
    · exact hlt
    · simp only [natRep, hlt, ↓reduceIte] at hrep; exact False.elim (ha_tag hrep.1)
  simp only [natRep, hlt63, ↓reduceIte] at hrep
  have hv_eq : (a >>> 1) + (1 : BitVec 64) = BitVec.ofNat 64 (aVal + 1) := by
    subst hrep; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      show BitVec.toNat (1 : BitVec 64) = 1 by decide]
    rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hv_eq]
  have hpow62 : ((1 : BitVec 64) <<< 62 : BitVec 64) = BitVec.ofNat 64 (2 ^ 62) := by decide
  rw [hpow62]
  by_cases hle62 : aVal + 1 ≤ 2 ^ 62
  · have hule : BitVec.ule (BitVec.ofNat 64 (aVal + 1)) (BitVec.ofNat 64 (2 ^ 62)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      exact hle62
    refine jnz_true hule ?_
    c0_let_simp
    have hbv_le : (BitVec.ofNat 64 (aVal + 1)).toNat ≤ 2 ^ 62 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hle62
    have henc := bv64_ofInt_neg_enc hbv_le
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at henc
    have hneg_eq : (-↑(aVal + 1) : Int) = z := by
      rw [← hz, Int.negSucc_eq]; omega
    rw [hneg_eq] at henc
    have hrep' : intRep (((0#64 - BitVec.ofNat 64 (aVal + 1)) <<< 1) ||| 1#64) z objs := by
      have hin : -(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62 := by
        rw [← hz, Int.negSucc_eq]; omega
      simp only [intRep, hin]; exact henc
    exact hQ _ st scrLimbs objs m ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (Nat.le_refl _) hwf hrep'
      (fun o ho _ => ⟨o, ho, rfl, rfl, rfl, rfl, rfl, rfl, fun h => h⟩) hm
  · have hz_lt : z < -(2 ^ 62 : Int) := by rw [← hz, Int.negSucc_eq]; omega
    have hule : BitVec.ule (BitVec.ofNat 64 (aVal + 1)) (BitVec.ofNat 64 (2 ^ 62)) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    refine jnz_false hule ?_
    refine alloc1_mpz_call_wp st scr scrLimbs (lcnfHeap objs ⋆ R) hwf.1
      (hsmallAlloc ⟨hlt63, hz_lt⟩) (sep_cast_ac hm (by ac_rfl)) ?_
    intro p st' m1 hobj0 hpa hpmeta hrem hb' hm1
    have hwf' : BigNumRtWf rt st' scr scrLimbs :=
      ⟨hb', hwf.2.1, hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩
    have hm1' : (lcnfObjMem (mkMpz1Obj p 0 [0#64]) ⋆
        (bigNumRtInv rt st' scr scrLimbs ⋆ lcnfHeap objs ⋆ R)) m1 :=
      sep_cast_ac hm1 (by ac_rfl)
    refine alloc1_set_neg_header_wp _ hobj0 hm1' ?_
    intro m2 hm2
    have hm2' : (bigNumRtInv rt st' scr scrLimbs ⋆
        lcnfObjMem (mkMpz1Obj p 1 [0#64]) ⋆
        lcnfHeap objs ⋆ R) m2 :=
      sep_cast_ac hm2 (by ac_rfl)
    have hmag_nat : (BitVec.ofNat 64 (aVal + 1)).toNat = z.natAbs := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ← hz, Int.natAbs_negSucc]
    have hmag_nz : BitVec.ofNat 64 (aVal + 1) ≠ 0#64 := by
      intro h; have ht := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      have h0n : (0#64 : BitVec 64).toNat = 0 := rfl; rw [h0n] at ht; omega
    refine alloc1_store_limb_ret_wp true z hwf' hpa hobj0
      hmag_nat hmag_nz (by rw [← hz]; simp [Int.negSucc_eq]) (Or.inl hz_lt) hm2' ?_
    intro res st3 scrLimbs3 objs3 m3 hpmeta3 hrem3 hwf3 hrep3 hpres3 hm3
    exact hQ res st3 scrLimbs3 objs3 m3
      (preservesMeta_trans hpmeta3 hpmeta) (Nat.le_trans hrem3 hrem)
      hwf3 hrep3 (fun o ho _ => ⟨o, hpres3 o ho, rfl, rfl, rfl, rfl, rfl, rfl, fun h => h⟩)
      hm3

private theorem lcnf_int_conv_op2_wp :
    ∀ {rt op a : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost},
      op.toNat = 2 → lcnfIntConvSpec (rt, op, a, ()) m Q X →
      Func.wp rtR1Env lcnf_int_conv.body (rt, op, a, ()) m Q X := by
  intro rt op a m Q X hop2 hspec
  by_cases ha_tag : a &&& 1#64 = 0#64
  · exact lcnf_int_conv_op2_boxed_wp hop2 ha_tag hspec
  · exact lcnf_int_conv_op2_small_wp hop2 ha_tag hspec

private theorem lcnf_int_conv_op39_wp :
    ∀ {rt op a : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost},
      op.toNat ≠ 1 → op.toNat ≠ 13 → op.toNat ≠ 16 → op.toNat ≠ 2 →
      lcnfIntConvSpec (rt, op, a, ()) m Q X →
      Func.wp rtR1Env lcnf_int_conv.body (rt, op, a, ()) m Q X := by
  intro rt op a m Q X hop1 hop13 hop16 hop2 ⟨st, scr, scrLimbs, objs, R, hwf, hm, hspec⟩
  change wp rtR1Env Q X (lcnf_int_conv_body Val Cont (rt, op, a, ())) m
  dsimp only [lcnf_int_conv_body]
  c0_let_simp
  have hne1 : (op == 1#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop1; subst h; decide
  have hne13 : (op == 13#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop13; subst h; decide
  have hne16 : (op == 16#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop16; subst h; decide
  have hne2 : (op == 2#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop2; subst h; decide
  refine jnz_false hne1 ?_; c0_let_simp
  refine jnz_false hne13 ?_; c0_let_simp
  refine jnz_false hne16 ?_; c0_let_simp
  refine jnz_false hne2 ?_
  simp only [hop1, hop13, hop16, hop2, ↓reduceIte] at hspec
  have hop39 : op.toNat = 3 ∨ op.toNat = 9 := by
    by_cases h3 : op.toNat = 3
    · exact Or.inl h3
    · by_cases h9 : op.toNat = 9
      · exact Or.inr h9
      · simp only [h3, h9, ↓reduceIte] at hspec
  have hshared : ∃ z : Int, intRep a z objs ∧
      (z ≠ 0 → limbLenNat z.natAbs ≤ scrLimbs.length ∧
        ((if op.toNat = 3 then -z < -(2 ^ 62 : Int) ∨ 2 ^ 62 ≤ -z else 2 ^ 63 ≤ z.natAbs) →
          canAllocBytes st (16 + 8 * limbLenNat z.natAbs))) ∧
      (∀ res st' scrLimbs' objs' m',
        st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
        (if op.toNat = 3 then intRep res (-z) objs' else natRep res z.natAbs objs') →
        (∀ o ∈ objs, o ∈ objs') →
        (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') := by
    rcases hop39 with h3 | h9
    · have hne9 : op.toNat ≠ 9 := by omega
      simp only [h3, ↓reduceIte] at hspec ⊢
      rcases hspec with ⟨z, hrep, hpre, hQ⟩
      exact ⟨z, hrep, hpre, fun res st' sl' objs' m' a b c d e f =>
        hQ res st' sl' objs' m' a b c d e f⟩
    · have hne3 : op.toNat ≠ 3 := by omega
      simp only [h9, ↓reduceIte] at hspec ⊢
      rcases hspec with ⟨z, hrep, hpre, hQ⟩
      exact ⟨z, hrep, hpre, fun res st' sl' objs' m' a b c d e f =>
        hQ res st' sl' objs' m' a b c d e f⟩
  rcases hshared with ⟨z, hrep, hzPre, hQ⟩
  refine wp_call_ret1 _ _ (fun naW m1 =>
    naW = BitVec.ofNat 64 (limbLenNat z.natAbs) ∧ m1 = m) ?_ ?_
  · refine rtR1Env_bn_int_len ?_
    dsimp only [bnIntLenSpec, vals, Arg.val]
    refine ⟨z, objs, bigNumRtInv rt st scr scrLimbs ⋆ R, hrep, ?_, rfl, rfl⟩
    exact (by ac_rfl : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) =
      (lcnfHeap objs ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R))) ▸ hm
  · rintro naW m1 ⟨rfl, hm1⟩
    subst m1
    c0_let_simp
    have hna_le : limbLenNat z.natAbs ≤ mpzMaxLimbs := limbLenNat_le_max_of_intRep hrep
    have hna_lt : limbLenNat z.natAbs < 2 ^ 64 := by
      have : mpzMaxLimbs = 33554429 := rfl; omega
    by_cases hz0 : z = 0
    · subst hz0
      have heq0 : (BitVec.ofNat 64 (limbLenNat (0 : Int).natAbs) == 0#64) = true := by decide
      refine jnz_true heq0 ?_; rw [wp_ret]; dsimp only [vals, Arg.val]
      have hres : if op.toNat = 3 then intRep 1#64 (-(0 : Int)) objs
          else natRep 1#64 (0 : Int).natAbs objs := by
        split
        · simp [intRep]
        · simp [natRep]
      exact hQ 1#64 st scrLimbs objs m ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (Nat.le_refl _) hwf hres (fun _ h => h) hm
    · have hpos_len : 0 < limbLenNat z.natAbs := limbLenNat_pos_iff.mpr (by omega)
      have hne0 : (BitVec.ofNat 64 (limbLenNat z.natAbs) == 0#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h
        have ht := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt] at ht
        have h0n : (0#64 : BitVec 64).toNat = 0 := rfl; rw [h0n] at ht; omega
      refine jnz_false hne0 ?_
      c0_let_simp
      have hnugt : BitVec.ult (33554429#64 : BitVec 64)
          (BitVec.ofNat 64 (limbLenNat z.natAbs)) = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
        rw [Nat.mod_eq_of_lt hna_lt, Nat.mod_eq_of_lt (by decide : 33554429 < 2 ^ 64)]
        exact Nat.not_lt_of_le hna_le
      refine jnz_false hnugt ?_
      rcases hzPre hz0 with ⟨hscrLen, halloc⟩
      refine wp_call_ret1 _ _ (fun scrP m1 => scrP = scr ∧ m1 = m) ?_ ?_
      · refine rtR1Env_bn_require_scratch ?_
        dsimp only [bnRequireScratchSpec, vals, Arg.val]
        refine ⟨scr, BitVec.ofNat 64 scrLimbs.length,
          BigNumRt.rtC0Inv rt st ⋆ array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R,
          hwf.2.2.1, ?_, ?_, rfl, rfl⟩
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hwf.2.2.2.2.1]; exact hscrLen
        · dsimp only [bigNumRtInv] at hm
          exact sep_cast_ac hm (by ac_rfl)
      · rintro scrP m1 ⟨hscrP, hm1⟩
        subst scrP; subst m1
        refine wp_call_ret1 _ _ (fun info m2 =>
          ∃ scrLimbs',
            info = ((BitVec.ofNat 64 (limbLenNat z.natAbs) <<< 1#64) |||
              (if z < 0 then 1#64 else 0#64)) ∧
            scrLimbs'.length = scrLimbs.length ∧
            limbsVal (List.take (limbLenNat z.natAbs) scrLimbs') = z.natAbs ∧
            (bigNumRtInv rt st scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m2) ?_ ?_
        · refine rtR1Env_bn_load_int ?_
          dsimp only [bnLoadIntSpec, vals, Arg.val]
          refine ⟨z, objs, scrLimbs, BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ R,
            hrep, hscrLen, ?_, fun xs' m2 hlen' hval' _ hm2 => ?_⟩
          · dsimp only [bigNumRtInv] at hm
            exact sep_cast_ac hm (by ac_rfl)
          · refine ⟨xs', rfl, hlen', hval', ?_⟩
            dsimp only [bigNumRtInv]; rw [hlen']
            exact sep_cast_ac hm2 (by ac_rfl)
        · rintro info m2 ⟨scrLimbs', rfl, hlen', hval', hm2⟩
          c0_let_simp

          have hbits := info_lshr1_and1 (len := limbLenNat z.natAbs)
            (negBit := if z < 0 then 1#64 else 0#64)
            (by have : mpzMaxLimbs = 33554429 := rfl; omega)
            (by by_cases h : z < 0 <;> simp [h])
          rw [hbits.1, hbits.2]
          have hna_bv : (BitVec.ofNat 64 (limbLenNat z.natAbs)).toNat = limbLenNat z.natAbs := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt]
          have hna_le_scr : limbLenNat z.natAbs ≤ scrLimbs'.length := by omega
          have htrim_eq : trimLenLoop scrLimbs' (limbLenNat z.natAbs) = limbLenNat z.natAbs := by
            rw [← limbLenNat_trimLenLoop hna_le_scr, hval']
          rcases hop39 with hop3 | hop9
          · have heq3 : (op == 3#64) = true := by
              simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using hop3)
            refine jnz_true heq3 ?_
            simp only [hop3, ↓reduceIte] at halloc hQ
            refine wp_join_group (fun xs m3 =>
              xs = ((if z < 0 then 0#64 else 1#64), ()) ∧ m3 = m2) ?_ ?_
            · rintro J ⟨negW, ⟨⟩⟩ m3 ⟨hnEq, hm3⟩
              injection hnEq with hnw; subst negW; subst m3
              rw [Blocks.get.eq_1]
              refine wp_call_ret1 _ _ (fun res m4 =>
                ∃ st' objs',
                  st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧ st'.Bounded48 ∧
                  intRep res (-z) objs' ∧ (∀ o ∈ objs, o ∈ objs') ∧
                  (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m4) ?_ ?_
              · refine rtR1Env_bn_int_from_limbs ?_
                dsimp only [bnIntFromLimbsSpec, vals, Arg.val]
                have hval_neg : (if trimLenLoop scrLimbs'
                    (BitVec.ofNat 64 (limbLenNat z.natAbs)).toNat = 0 then 0
                    else if (if z < 0 then 0#64 else 1#64) = 0#64 then
                      ↑(limbsVal (List.take (BitVec.ofNat 64
                        (limbLenNat z.natAbs)).toNat scrLimbs'))
                    else -↑(limbsVal (List.take (BitVec.ofNat 64 (limbLenNat z.natAbs)).toNat
                      scrLimbs'))) = -z := by
                  rw [hna_bv, htrim_eq, hval']
                  have hnz : limbLenNat z.natAbs ≠ 0 := by omega
                  simp only [hnz, ↓reduceIte]
                  by_cases hlt0 : z < 0
                  · simp [hlt0]; omega
                  · have hgt0 : 0 < z := by omega
                    simp [hlt0]; omega
                refine ⟨st, scrLimbs', objs, cell64 (rt + 33672#64) scr ⋆
                    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆ R,
                  by rw [hna_bv]; exact hna_le_scr, by rw [hna_bv]; exact hna_le, hwf.1,
                  fun hneg_r => by
                    rw [hval_neg] at hneg_r
                    rw [hna_bv, htrim_eq]
                    exact halloc hneg_r,
                  ?_, fun res st' objs' m4 hpm hrem hb' hrep' hsm hbg hm4 => ?_⟩
                · dsimp only [bigNumRtInv] at hm2; exact sep_cast_ac hm2 (by ac_rfl)
                · rw [hval_neg] at hrep' hsm hbg
                  have hpres : ∀ o ∈ objs, o ∈ objs' := by
                    by_cases hsm_c : -(2 ^ 62 : Int) ≤ -z ∧ -z < 2 ^ 62
                    · rw [hsm hsm_c]; exact fun _ h => h
                    · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
                      exact fun _ h => List.mem_cons_of_mem _ h
                  refine ⟨st', objs', hpm, hrem, hb', hrep', hpres, ?_⟩
                  dsimp only [bigNumRtInv]; exact sep_cast_ac hm4 (by ac_rfl)
              · rintro res m4 ⟨st', objs', hpm, hrem, hb', hrep', hpres, hm4⟩
                rw [wp_ret]; dsimp only [vals, Arg.val]
                exact hQ res st' scrLimbs' objs' m4 hpm hrem
                  (BigNumRtWf.with_state_len hwf hb' hlen') hrep' hpres hm4
            · intro J hJ
              c0_let_simp
              have heq_f : (BitVec.ofNat 64 (limbLenNat z.natAbs) == 0#64) = false := hne0
              refine jnz_false heq_f ?_
              c0_let_simp
              by_cases hlt0 : z < 0
              · simp only [hlt0, ↓reduceIte]
                have hsub1 : ((1 : BitVec 64) - 1#64) = 0#64 := by decide
                rw [hsub1]; exact hJ (0#64, ()) m2 ⟨by simp [hlt0], rfl⟩
              · simp only [hlt0, ↓reduceIte]
                have hsub0 : ((1 : BitVec 64) - 0#64) = 1#64 := by decide
                rw [hsub0]; exact hJ (1#64, ()) m2 ⟨by simp [hlt0], rfl⟩
          · have hne3' : (op == 3#64) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]
              intro h; apply (by omega : op.toNat ≠ 3); subst h; decide
            have heq9 : (op == 9#64) = true := by
              simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using hop9)
            have hne3n : op.toNat ≠ 3 := by omega
            refine jnz_false hne3' ?_
            c0_let_simp; refine jnz_true heq9 ?_
            simp only [hne3n, ↓reduceIte] at halloc hQ
            refine wp_call_ret1 _ _ (fun res m3 =>
              ∃ st' objs',
                st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧ st'.Bounded48 ∧
                natRep res z.natAbs objs' ∧ (∀ o ∈ objs, o ∈ objs') ∧
                (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m3) ?_ ?_
            · refine rtR1Env_bn_nat_from_limbs ?_
              dsimp only [bnNatFromLimbsSpec, vals, Arg.val]
              refine ⟨st, scrLimbs', objs, cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆ R,
                by rw [hna_bv]; exact hna_le_scr, by rw [hna_bv]; exact hna_le, hwf.1,
                fun h263 => by
                  rw [hna_bv, htrim_eq]; apply halloc
                  rw [hna_bv, hval'] at h263; exact h263,
                ?_, fun res st' objs' m3 hpm hrem hb' hrep' hsm hbg hm3 => ?_⟩
              · dsimp only [bigNumRtInv] at hm2; exact sep_cast_ac hm2 (by ac_rfl)
              · rw [hna_bv, hval'] at hrep' hsm hbg
                have hpres : ∀ o ∈ objs, o ∈ objs' := by
                  by_cases hlt63 : z.natAbs < 2 ^ 63
                  · rw [hsm hlt63]; exact fun _ h => h
                  · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
                    exact fun _ h => List.mem_cons_of_mem _ h
                refine ⟨st', objs', hpm, hrem, hb', hrep', hpres, ?_⟩
                dsimp only [bigNumRtInv]; exact sep_cast_ac hm3 (by ac_rfl)
            · rintro res m3 ⟨st', objs', hpm, hrem, hb', hrep', hpres, hm3⟩
              rw [wp_ret]; dsimp only [vals, Arg.val]
              exact hQ res st' scrLimbs' objs' m3 hpm hrem
                (BigNumRtWf.with_state_len hwf hb' hlen') hrep' hpres hm3



theorem lcnf_int_conv_wp :
    ∀ xs m Q X, lcnfIntConvSpec xs m Q X → Func.wp rtR1Env lcnf_int_conv.body xs m Q X := by
  rintro ⟨rt, op, a, ⟨⟩⟩ m Q X hfull
  by_cases hop2 : op.toNat = 2
  · exact lcnf_int_conv_op2_wp hop2 hfull
  · by_cases hop_other : op.toNat ≠ 1 ∧ op.toNat ≠ 13 ∧ op.toNat ≠ 16
    · exact lcnf_int_conv_op39_wp hop_other.1 hop_other.2.1 hop_other.2.2 hop2 hfull
    · rcases hfull with ⟨st, scr, scrLimbs, objs, R, hwf, hm, hspec⟩
      change wp rtR1Env Q X (lcnf_int_conv_body Val Cont (rt, op, a, ())) m
      dsimp only [lcnf_int_conv_body]
      c0_let_simp
      by_cases hop1 : op.toNat = 1
      · have heq1 : (op == 1#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using hop1)
        refine jnz_true heq1 ?_
        simp only [hop1, ↓reduceIte] at hspec
        rcases hspec with ⟨aVal, hrep, halloc, hQ⟩
        exact lcnf_int_conv_ofNat_wp st scr scrLimbs objs R hwf hm aVal ↑aVal rfl hrep halloc hQ
      · have hne1 : (op == 1#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop1; subst h; decide
        refine jnz_false hne1 ?_
        simp only [hop1, ↓reduceIte] at hspec
        c0_let_simp
        by_cases hop13 : op.toNat = 13
        · have heq13 : (op == 13#64) = true := by
            simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using hop13)
          refine jnz_true heq13 ?_
          simp only [hop13, ↓reduceIte] at hspec
          rcases hspec with ⟨halloc, hQ⟩
          c0_let_simp
          have hpow62 : ((1 : BitVec 64) <<< 62 : BitVec 64) = BitVec.ofNat 64 (2 ^ 62) := by decide
          rw [hpow62]
          refine wp_join_group (fun _ m0 =>
            (a.toInt < -(2 ^ 62 : Int) ∨ 2 ^ 62 ≤ a.toInt) ∧
            (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m0) ?_ ?_
          · rintro J ⟨⟩ m0 ⟨hrange, hm0⟩
            rw [Blocks.get.eq_1]
            refine wp_join_group (fun xs m1 =>
              ∃ negBool : Bool,
                xs = ((if negBool then 1#64 else 0#64), ()) ∧
                (negBool = true ↔ a.toInt < 0) ∧
                (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m1) ?_ ?_
            · rintro J1 ⟨negW, ⟨⟩⟩ m1 ⟨negBool, hnegEq, hsign, hm1⟩
              injection hnegEq with hnegW
              subst hnegW
              rw [Blocks.get.eq_1]
              refine wp_join_group (fun xs m2 =>
                ∃ mag : BitVec 64,
                  xs = (mag, ()) ∧ mag.toNat = a.toInt.natAbs ∧ mag ≠ 0#64 ∧
                  (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m2) ?_ ?_
              · rintro J2 ⟨mag, ⟨⟩⟩ m2 ⟨mag', hmagEq, hmagNat, hmagNz, hm2⟩
                injection hmagEq with hmag'
                subst hmag'
                rw [Blocks.get.eq_1]
                have hm2_assoc : (bigNumRtInv rt st scr scrLimbs ⋆ (lcnfHeap objs ⋆ R)) m2 :=
                  (by rw [sep_assoc] : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) =
                    (bigNumRtInv rt st scr scrLimbs ⋆ (lcnfHeap objs ⋆ R))) ▸ hm2
                refine alloc1_mpz_call_wp st scr scrLimbs (lcnfHeap objs ⋆ R) hwf.1
                  (halloc hrange) hm2_assoc ?_
                intro p st' m3 hobj0 hpa hpmeta hrem hb' hm3
                have hwf' : BigNumRtWf rt st' scr scrLimbs :=
                  ⟨hb', hwf.2.1, hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩
                refine wp_join_group (fun _ m4 =>
                  (bigNumRtInv rt st' scr scrLimbs ⋆
                    lcnfObjMem (mkMpz1Obj p (if negBool then 1 else 0) [0#64]) ⋆
                    lcnfHeap objs ⋆ R) m4) ?_ ?_
                · rintro J3 ⟨⟩ m4 hm4
                  rw [Blocks.get.eq_1]
                  refine alloc1_store_limb_ret_wp negBool a.toInt hwf' hpa hobj0
                    hmagNat hmagNz hsign hrange hm4 ?_
                  intro res st4 scrLimbs4 objs4 m5 hpmeta4 hrem4 hwf4 hrep4 hpres4 hm5
                  exact hQ res st4 scrLimbs4 objs4 m5 (preservesMeta_trans hpmeta4 hpmeta)
                    (Nat.le_trans hrem4 hrem) hwf4 hrep4 hpres4 hm5
                · intro J3 hJ3
                  c0_let_simp
                  cases negBool
                  · refine jnz_false (by decide) ?_
                    rw [wp_jump]
                    exact hJ3 () m3 (sep_cast_ac hm3 (by ac_rfl))
                  · refine jnz_true (by decide) ?_
                    have hm3' : (lcnfObjMem (mkMpz1Obj p 0 [0#64]) ⋆
                        (bigNumRtInv rt st' scr scrLimbs ⋆ lcnfHeap objs ⋆ R)) m3 :=
                      sep_cast_ac hm3 (by ac_rfl)
                    refine alloc1_set_neg_header_wp _ hobj0 hm3' ?_
                    intro m4 hm4
                    rw [wp_jump]
                    exact hJ3 () m4 (sep_cast_ac hm4 (by ac_rfl))
              · intro J2 hJ2
                c0_let_simp
                cases negBool
                · refine jnz_false (by decide) ?_; rw [wp_jump]
                  have hge : 0 ≤ a.toInt := by
                    by_cases h : 0 ≤ a.toInt
                    · exact h
                    · exact False.elim (by simpa using hsign.mpr (by omega))
                  have hmagNat := bv64_sge0_toNat hge
                  have hmagNz : a ≠ 0#64 := by
                    intro h0; subst h0; simp at hrange
                  exact hJ2 (a, ()) m1 ⟨a, rfl, hmagNat, hmagNz, hm1⟩
                · refine jnz_true (by decide) ?_
                  c0_let_simp
                  have hlt0 : a.toInt < 0 := hsign.mp rfl
                  have ⟨hmagNat, hmagNz⟩ := bv64_neg_abs_of_slt hlt0
                  exact hJ2 (0#64 - a, ()) m1 ⟨0#64 - a, rfl, hmagNat, hmagNz, hm1⟩
            · intro J1 hJ1
              c0_let_simp
              by_cases hlt0 : a.toInt < 0
              · have hslt : BitVec.slt a 0#64 = true := by
                  simp [BitVec.slt]; exact hlt0
                refine jnz_true hslt ?_; rw [wp_jump]
                exact hJ1 (1#64, ()) m0 ⟨true, rfl, by simp [hlt0], hm0⟩
              · have hnslt : BitVec.slt a 0#64 = false := by
                  simp [BitVec.slt]; omega
                refine jnz_false hnslt ?_; rw [wp_jump]
                exact hJ1 (0#64, ()) m0 ⟨false, rfl, by simp; omega, hm0⟩
          · intro J hJ
            c0_let_simp
            have hpos62 : (BitVec.ofNat 64 (2 ^ 62)).toInt = 2 ^ 62 := by decide
            have hneg62 : (-BitVec.ofNat 64 (2 ^ 62)).toInt = -(2 ^ 62) := by decide
            by_cases hlo : -(2 ^ 62 : Int) ≤ a.toInt
            · have hsge : BitVec.sle (-(BitVec.ofNat 64 (2 ^ 62))) a = true := by
                simp only [BitVec.sle, hneg62, decide_eq_true_eq]; exact hlo
              refine jnz_true hsge ?_
              c0_let_simp
              by_cases hhi : a.toInt < 2 ^ 62
              · have hslt : BitVec.slt a (BitVec.ofNat 64 (2 ^ 62)) = true := by
                  simp [BitVec.slt, hpos62]; exact hhi
                refine jnz_true hslt ?_
                c0_let_simp
                have hrep' : intRep (a <<< 1 ||| 1#64) a.toInt objs := by
                  have hin : -(2 ^ 62 : Int) ≤ a.toInt ∧ a.toInt < 2 ^ 62 := ⟨hlo, hhi⟩
                  simp only [intRep, hin]
                  exact bv64_ofInt_small_enc hlo hhi
                exact hQ _ st scrLimbs objs m ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                  (Nat.le_refl _) hwf hrep' (fun _ h => h) hm
              · have hnslt : BitVec.slt a (BitVec.ofNat 64 (2 ^ 62)) = false := by
                  simp only [BitVec.slt, hpos62, decide_eq_false_iff_not]; exact hhi
                refine jnz_false hnslt ?_; rw [wp_jump]
                exact hJ () m ⟨Or.inr (by omega), hm⟩
            · have hnsge : BitVec.sle (-(BitVec.ofNat 64 (2 ^ 62))) a = false := by
                simp only [BitVec.sle, hneg62, decide_eq_false_iff_not]; exact hlo
              refine jnz_false hnsge ?_; rw [wp_jump]
              exact hJ () m ⟨Or.inl (by omega), hm⟩
        · have hne13 : (op == 13#64) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop13; subst h; decide
          refine jnz_false hne13 ?_
          simp only [hop13, ↓reduceIte] at hspec
          c0_let_simp
          by_cases hop16 : op.toNat = 16
          · have heq16 : (op == 16#64) = true := by
              simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using hop16)
            refine jnz_true heq16 ?_
            simp only [hop16, ↓reduceIte] at hspec
            rcases hspec with ⟨z, hrep, hQ⟩
            c0_let_simp
            by_cases ha_tag : a &&& 1#64 = 0#64
            · refine jnz_false (by simp [ha_tag]) ?_
              have hbig : ¬(-(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62) := by
                intro hin
                simp only [intRep, hin] at hrep
                rw [hrep] at ha_tag
                have hodd : (BitVec.ofInt 64 (2 * z + 1) &&& 1#64) = 1#64 := by
                  exact (intSmallEnc_toInt hin.1 hin.2).1
                rw [hodd] at ha_tag; cases ha_tag
              simp only [intRep, hbig, ↓reduceIte] at hrep
              rcases hrep with ⟨_, obj, hom, had, hcanon⟩
              have hm_foc := hm
              have hfoc_step : ((lcnfHeap objs) ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R)) m :=
                (by ac_rfl : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) =
                  (lcnfHeap objs ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R))) ▸ hm_foc
              rcases lcnfHeap_mpz_focus hom hcanon.2.1 hfoc_step with ⟨idx, hlt, hidx, hmem⟩
              rw [had] at hmem
              have hmem' : (cell64 a obj.header ⋆ (cell64 (a + 8#64) obj.mpzMeta ⋆
                  array64 (a + 16#64) obj.limbs ⋆ lcnfHeap (objs.take idx) ⋆
                  lcnfHeap (objs.drop (idx + 1)) ⋆ bigNumRtInv rt st scr scrLimbs ⋆ R)) m :=
                sep_cast_ac hmem (by ac_rfl)
              refine wp_load_cell64 (a := Arg.var a) hmem' ?_
              refine wp_join_group (fun xs m' => xs = ((if 0 ≤ z then 1#64 else 0#64), ()) ∧
                m' = m) ?_ ?_
              · rintro J ⟨res, ⟨⟩⟩ m' ⟨hres, hm'⟩
                injection hres with hres'; subst res; subst m'
                rw [Blocks.get.eq_1, wp_ret]; dsimp only [vals, Arg.val]
                exact hQ m hm
              · intro J hJ
                c0_let_simp
                have hoth := LcnfObj.header_other_byte obj hcanon.1
                change ((obj.header >>> 48) &&& (255 : BitVec 64)) =
                  BitVec.ofNat 64 obj.other at hoth
                rw [hoth]
                by_cases hnonneg : 0 ≤ z
                · have hoth0 : obj.other = 0 := by
                    rcases hcanon.2.2.1 with h | h
                    · exact h
                    · exact False.elim ((by omega : ¬(z < 0)) (hcanon.2.2.2.2.2.2.2.2.1.mp h))
                  rw [hoth0]
                  refine jnz_true (by decide) ?_; rw [wp_jump]
                  exact hJ (1#64, ()) m ⟨by simp [hnonneg], rfl⟩
                · have hlt0 : z < 0 := by omega
                  have hoth1 : obj.other = 1 := by
                    rcases hcanon.2.2.1 with h | h
                    · have hne1 := hcanon.2.2.2.2.2.2.2.2.1.mpr hlt0; omega
                    · exact h
                  rw [hoth1]
                  refine jnz_false (by decide) ?_; rw [wp_jump]
                  exact hJ (0#64, ()) m ⟨by simp [hnonneg], rfl⟩
            · refine jnz_true (by simp only [bne_iff_ne, ne_eq]; exact ha_tag) ?_
              c0_let_simp
              have hin : -(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62 := by
                by_cases h : -(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62
                · exact h
                · simp only [intRep, h, ↓reduceIte] at hrep; exact False.elim (ha_tag hrep.1)
              simp only [intRep, hin] at hrep
              have hsh := (intSmallEnc_toInt hin.1 hin.2).2
              rw [← hrep] at hsh
              refine wp_join_group (fun xs m' => xs = ((if 0 ≤ z then 1#64 else 0#64), ()) ∧
                m' = m) ?_ ?_
              · rintro J ⟨res, ⟨⟩⟩ m' ⟨hres, hm'⟩
                injection hres with hres'; subst res; subst m'
                rw [Blocks.get.eq_1, wp_ret]; dsimp only [vals, Arg.val]
                exact hQ m hm
              · intro J hJ
                c0_let_simp
                by_cases hnonneg : 0 ≤ z
                · have hsge : BitVec.sle 0#64 (a.sshiftRight 1) = true := by
                    simp [BitVec.sle, hsh]; exact hnonneg
                  refine jnz_true hsge ?_; rw [wp_jump]
                  exact hJ (1#64, ()) m ⟨by simp [hnonneg], rfl⟩
                · have hnsge : BitVec.sle 0#64 (a.sshiftRight 1) = false := by
                    simp [BitVec.sle, hsh]; omega
                  refine jnz_false hnsge ?_; rw [wp_jump]
                  exact hJ (0#64, ()) m ⟨by simp [hnonneg], rfl⟩
          · have hne16 : (op == 16#64) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop16; subst h; decide
            refine jnz_false hne16 ?_
            simp only [hop16, ↓reduceIte] at hspec
            c0_let_simp
            exfalso; exact hop_other ⟨hop1, hop13, hop16⟩

end LeanQbe.T.LeanLCNF
