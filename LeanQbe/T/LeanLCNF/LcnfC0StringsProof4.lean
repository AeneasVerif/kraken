module

public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof4a
import LeanQbe.T.LeanLCNF.LcnfC0StringsProofAlloc
import LeanQbe.T.LeanLCNF.LcnfC0StringsProof1

/-!
# Soundness Proofs for `LcnfC0Strings`, Part 4: `lcnf_nat_to_str` (Phases 3–5)

Proves Phases 3–5 and `lcnf_nat_to_str_wp`, building on `LcnfC0StringsProof4a`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T Std.ExtHashMap

public section

/-! ## Phase 3: Boxed wrapper & Inner `tmp_mpz /= 10` loop -/

private theorem zero_store_pop_reassoc
    (rt c0 c8 c16 c24 reg1 b0 reg2 R : Mem 64 → Prop) :
    (rt ⋆ c0 ⋆ c8 ⋆ c16 ⋆ c24 ⋆ reg1 ⋆ b0 ⋆ reg2 ⋆ R) =
    (reg1 ⋆ (rt ⋆ c0 ⋆ c8 ⋆ c16 ⋆ c24 ⋆ b0 ⋆ reg2 ⋆ R)) := by
  simp only [Std.ExtHashMap.sep_assoc]
  rw [msep_left_comm c24 reg1, msep_left_comm c16 reg1, msep_left_comm c8 reg1,
    msep_left_comm c0 reg1, msep_left_comm rt reg1]

private theorem zero_store_pack_reassoc
    (b32 rt c0 c8 c16 c24 b0 reg2 R : Mem 64 → Prop) :
    (b32 ⋆ (rt ⋆ c0 ⋆ c8 ⋆ c16 ⋆ c24 ⋆ b0 ⋆ reg2 ⋆ R)) =
    (c0 ⋆ c8 ⋆ c16 ⋆ c24 ⋆ b32 ⋆ b0 ⋆ reg2 ⋆ (rt ⋆ R)) := by
  simp only [Std.ExtHashMap.sep_assoc]
  rw [msep_left_comm rt c0, msep_left_comm rt c8, msep_left_comm rt c16, msep_left_comm rt c24,
    msep_left_comm rt b0, msep_left_comm rt reg2]
  rw [msep_left_comm b32 c0, msep_left_comm b32 c8, msep_left_comm b32 c16,
    msep_left_comm b32 c24]

private theorem nat_to_str_zero_store_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt s : Val i64} {st1 : RtC0State} {m1 : Mem 64} {k : Expr Val Cont [i64]}
    (hm1 : (rtC0Inv rt st1 ⋆ cell64 s strHeaderWord ⋆ cell64 (s + 8#64) (1#64 + 1#64) ⋆
      cell64 (s + 16#64) 2#64 ⋆ cell64 (s + 24#64) 1#64 ⋆ region (s + 32#64) 1 ⋆
      bytes (s + 32#64 + 1#64) [0] ⋆
      region (s + 32#64 + 1#64 + 1#64) (strAllocBytes 2 - (32 + 1 + 1)) ⋆ R) m1)
    (hk : ∀ m2, (rtC0Inv rt st1 ⋆ lcnfObjMem (mkStrObj s 1#32 2 [UInt8.ofNat 48] 1) ⋆ R) m2 →
      wp rtR2bEnv Q X k m2) :
    wp rtR2bEnv Q X
      (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var s, Arg.imm 32, ())) fun p_6 =>
        Expr.let_ (Op.mk (OpCode.trunc 64 8) (Arg.imm (t := i64) 48, ())) fun p_7 =>
        Expr.store (Arg.var p_7.fst) (Arg.var p_6.fst) k) m1 := by
  have hm1' : (region (s + 32#64) 1 ⋆
      (rtC0Inv rt st1 ⋆ cell64 s strHeaderWord ⋆ cell64 (s + 8#64) (1#64 + 1#64) ⋆
        cell64 (s + 16#64) 2#64 ⋆ cell64 (s + 24#64) 1#64 ⋆ bytes (s + 32#64 + 1#64) [0] ⋆
        region (s + 32#64 + 1#64 + 1#64) (strAllocBytes 2 - (32 + 1 + 1)) ⋆ R)) m1 :=
    sep_cast hm1 (zero_store_pop_reassoc _ _ _ _ _ _ _ _ _)
  rcases region_pop_bytes (k := 1) (Nat.le_refl _) (by decide) hm1' with ⟨sBs0, hsLen, hsMem⟩
  rw [Nat.sub_self, region_zero, Std.ExtHashMap.sep_emp] at hsMem
  c0_let_simp; rw [show (32 : BitVec 64) = 32#64 from rfl]
  let b48 : BitVec 8 := 48#8
  have hst := bytes_set_store8_32 (a := s) (i := 0#64) b48 hsMem
    (by rw [show (0#64 : BitVec 64).toNat = 0 from rfl, hsLen]; omega) (by rw [hsLen]; omega)
  rw [BitVec.add_zero] at hst; rw [wp_store]; dsimp only [Arg.val_var]
  refine ⟨hst.1, ?_⟩
  have hlist : sBs0.set 0 (UInt8.ofNat b48.toNat) = [UInt8.ofNat 48] := by
    rcases sBs0 with _ | ⟨x0, _ | _⟩ <;> simp at hsLen
    simp [show UInt8.ofNat b48.toNat = UInt8.ofNat 48 from by decide]
  have hm2 := hst.2
  rw [show (0#64 : BitVec 64).toNat = 0 from rfl, hlist] at hm2
  have hmStr : (cell64 s strHeaderWord ⋆
      cell64 (s + 8#64) (BitVec.ofNat 64 ([UInt8.ofNat 48].length + 1)) ⋆
      cell64 (s + 16#64) (BitVec.ofNat 64 2) ⋆ cell64 (s + 24#64) (BitVec.ofNat 64 1) ⋆
      bytes (s + 32#64) [UInt8.ofNat 48] ⋆
      bytes (s + 32#64 + BitVec.ofNat 64 [UInt8.ofNat 48].length) [0] ⋆
      region (s + 32#64 + BitVec.ofNat 64 [UInt8.ofNat 48].length + 1#64)
        (strAllocBytes 2 - (32 + [UInt8.ofNat 48].length + 1)) ⋆ (rtC0Inv rt st1 ⋆ R))
      (storeMem m1 i8 (s + 32#64) b48) := by
    simp only [List.length_singleton,
      show 1#64 + 1#64 = BitVec.ofNat 64 (1 + 1) by decide] at hm2 ⊢
    exact sep_cast hm2 (zero_store_pack_reassoc _ _ _ _ _ _ _ _ _)
  exact hk _ (sep_cast (mkStrObj_mem_of_parts (by decide) (by decide) hmStr)
    (by rw [msep_left_comm, ← Std.ExtHashMap.sep_assoc]))

private theorem nat_to_str_boxed_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt n : Val i64} {st : RtC0State} {m : Mem 64}
    (hlt : (n >>> 1).toNat < 2 ^ 63)
    (hfree :
      let dec := natToDecimalBytes (n >>> 1).toNat
      st.hasFree (strAllocBytes (dec.length + 1)) ∨ strAllocBytes (dec.length + 1) ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ R) m)
    (hpost : ∀ s st' m',
      s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      let dec := natToDecimalBytes (n >>> 1).toNat
      let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
      StrCanon sObj → (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ R) m' → Q (s, ()) m') :
    wp rtR2bEnv Q X (boxedExpr rt n) m := by
  unfold boxedExpr
  have hsext : (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 := by decide
  rw [wp_let]; dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm]
  refine ⟨by decide, ?_⟩
  rw [wp_let]; dsimp only [Op.wp, OpCode.wp, vals, Arg.val_var, lift2]
  rw [hsext]
  rw [wp_let]
  dsimp only [Op.wp, OpCode.wp, vals, Arg.val_var, Arg.val_imm, liftCmp,
    CmpOp.evalBits, CmpOp.evalBool]
  rw [wp_jnz]; dsimp only [Arg.val_var]
  refine ⟨fun hz => ?_, fun hnz => ?_⟩
  · have hv0 : (n >>> 1) = 0#64 := by simpa using hz
    have hv0N : (n >>> 1).toNat = 0 := by rw [hv0]; rfl
    have hdec0 : natToDecimalBytes (n >>> 1).toNat = [UInt8.ofNat 48] := by
      rw [hv0N]
      unfold natToDecimalBytes
      simp
    rw [hdec0] at hfree
    dsimp only [List.length_singleton] at hfree
    apply wp_call_of_spec
    apply rtR2bEnv_r2b_str_alloc_cap
    dsimp only [r2bStrAllocCapSpec, vals, Arg.val_var, Arg.val_imm]
    have hbounds : (1 : BitVec 64).toNat < strMaxCap ∧
        (1 : BitVec 64).toNat < (2 : BitVec 64).toNat ∧ (2 : BitVec 64).toNat ≤ strMaxCap := by
      simp only [strMaxCap]; decide
    rw [ite_eq_left hbounds, show ((2 : BitVec 64).toNat) = 2 from rfl]
    refine ⟨st, R, hfree, hm, fun s st1 m1 hs0 hs8 hpr1 hrem1 _ hm1 => ?_⟩
    rw [show (1 : BitVec 64).toNat = 1 from rfl, show (1 : BitVec 64) = 1#64 from rfl] at hm1
    refine nat_to_str_zero_store_wp hm1 fun m2 hstrMem => ?_
    rw [wp_ret]; dsimp only [vals, Arg.val_var]
    have hcanon : StrCanon (mkStrObj s 1#32 2 [UInt8.ofNat 48] 1) :=
      mkStrObj_canon hs0 hs8 (by decide) (by decide) (by decide) (by decide)
    have hgoal := hpost s st1 m2 hs0 hs8 hpr1 hrem1
    dsimp only at hgoal
    rw [hdec0] at hgoal
    exact hgoal hcanon hstrMem
  · have hvNe : (n >>> 1) ≠ 0#64 := by simpa using hnz
    have hvPos : 0 < (n >>> 1).toNat :=
      Nat.pos_of_ne_zero fun h0 => hvNe (BitVec.eq_of_toNat_eq h0)
    have hdeq : natToDecimalBytes (n >>> 1).toNat = (natDigitsRev (n >>> 1).toNat).reverse := by
      unfold natToDecimalBytes; rw [ite_eq_right (by omega)]
    have hfree' :
        st.hasFree (strAllocBytes ((natDigitsRev (n >>> 1).toNat).length + 1)) ∨
          strAllocBytes ((natDigitsRev (n >>> 1).toNat).length + 1) ≤ st.rem := by
      simpa only [hdeq, List.length_reverse] using hfree
    let decRev := (natDigitsRev (n >>> 1).toNat).reverse
    have hpost' : ∀ s st' m',
        s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        StrCanon (mkStrObj s 1#32 (decRev.length + 1) decRev decRev.length) →
        (rtC0Inv rt st' ⋆
          lcnfObjMem (mkStrObj s 1#32 (decRev.length + 1) decRev decRev.length) ⋆ R) m' →
        Q (s, ()) m' := by
      intro s st' m' hs0 hs8 hpr hrem hcan hm'
      have hcan' : StrCanon (mkStrObj s 1#32 ((natToDecimalBytes (n >>> 1).toNat).length + 1)
          (natToDecimalBytes (n >>> 1).toNat) (natToDecimalBytes (n >>> 1).toNat).length) := by
        simpa only [decRev, ← hdeq] using hcan
      have hm'' : (rtC0Inv rt st' ⋆ lcnfObjMem (mkStrObj s 1#32
          ((natToDecimalBytes (n >>> 1).toNat).length + 1) (natToDecimalBytes (n >>> 1).toNat)
          (natToDecimalBytes (n >>> 1).toNat).length) ⋆ R) m' := by
        simpa only [decRev, ← hdeq] using hm'
      exact hpost s st' m' hs0 hs8 hpr hrem hcan' hm''
    exact nat_to_str_boxed_nonzero_wp hvPos hlt hfree' hm hpost'

private theorem nat_to_str_inner_div10_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {tmp curLenBv : Val i64} {tmpXs0 : List (BitVec 64)} {m : Mem 64}
    {k : Val i64 → Expr Val Cont [i64]}
    (hcurLe : curLenBv.toNat ≤ tmpXs0.length) (_htmpLen : tmpXs0.length < 2 ^ 64)
    (hm : (array64 (tmp + 16#64) tmpXs0 ⋆ R) m)
    (hk : ∀ remBv tmpXs m', remBv.toNat < 10 → tmpXs.length = tmpXs0.length →
      tmpXs.drop curLenBv.toNat = tmpXs0.drop curLenBv.toNat →
      10 * mpzLimbsVal (tmpXs.take curLenBv.toNat) + remBv.toNat =
        mpzLimbsVal (tmpXs0.take curLenBv.toNat) →
      (array64 (tmp + 16#64) tmpXs ⋆ R) m' → wp rtR2bEnv Q X (k remBv) m') :
    wp rtR2bEnv Q X (innerDiv10Expr tmp curLenBv k) m := by
  unfold innerDiv10Expr
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xsP mk =>
    match xsP with
    | (carry, j, PUnit.unit) =>
      ∃ tmpXs : List (BitVec 64),
        meas = j.toNat ∧ carry.toNat < 10 ∧ j.toNat ≤ curLenBv.toNat ∧
        tmpXs.length = tmpXs0.length ∧
        tmpXs.drop curLenBv.toNat = tmpXs0.drop curLenBv.toNat ∧
        mpzLimbsVal (tmpXs.take j.toNat) +
          (2 ^ 64) ^ j.toNat *
            (10 * mpzLimbsVal (List.drop j.toNat (tmpXs.take curLenBv.toNat)) + carry.toNat) =
          mpzLimbsVal (tmpXs0.take curLenBv.toNat) ∧
        (array64 (tmp + 16#64) tmpXs ⋆ R) mk
  apply wp_loop_group Inv
  · intro J meas xsP mk hIH hInv
    rcases xsP with ⟨carry, j, ⟨⟩⟩
    rcases hInv with ⟨tmpXs, hmeas, hcarry, hjLe, hlen, hdropEq, hinv, hmk⟩
    c0_step
    rw [wp_jnz]; dsimp only [Arg.val_var]
    refine ⟨fun hgt => ?_, fun hle0 => ?_⟩
    · rw [BitVec.ult, decide_eq_true_eq] at hgt
      have h0eq : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0eq] at hgt
      have hjPos : 0 < j.toNat := hgt
      have hj1 : (j - 1#64).toNat = j.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
          (by rw [show (1#64).toNat = 1 from rfl]; omega))]
        rfl
      have hlt : (j - 1#64).toNat < tmpXs.length := by omega
      c0_let_simp
      have hld := r2b_c0_load_array64_add16_mul8 (i := j - 1#64) hmk hlt
      try rw [show (16 : BitVec 64) = 16#64 from rfl]
      try rw [show (8 : BitVec 64) = 8#64 from rfl]
      try rw [show (1 : BitVec 64) = 1#64 from rfl]
      apply wp_load_of (v := tmpXs[(j - 1#64).toNat]) (by simpa [Arg.val_var] using hld)
      repeat rw [wp_let]; dsimp only [Op.wp, vals, Arg.val_var, Arg.val_imm, lift2]
      refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, ?_⟩
      c0_let_simp
      have h32s : (BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64 = 32 := by decide
      try rw [h32s]
      try rw [show (16 : BitVec 64) = 16#64 from rfl]
      try rw [show (8 : BitVec 64) = 8#64 from rfl]
      try rw [show (1 : BitVec 64) = 1#64 from rfl]
      try rw [show (10 : BitVec 64) = 10#64 from rfl]
      try rw [show (4294967295 : BitVec 64) = 4294967295#64 from rfl]
      let w := tmpXs[(j - 1#64).toNat]
      let hiBv := (carry <<< 32) ||| (w >>> 32)
      let q1 := hiBv / 10#64
      let r1 := hiBv % 10#64
      let loBv := (r1 <<< 32) ||| (w &&& 4294967295#64)
      let q2 := loBv / 10#64
      let r2 := loBv % 10#64
      let wNew := (q1 <<< 32) ||| q2
      have hst := r2b_c0_store_array64_add16_mul8 (i := j - 1#64) wNew hmk hlt
      rw [wp_store]; dsimp only [Arg.val_var]
      refine ⟨hst.1, ?_⟩
      rw [wp_jump]; dsimp only [vals, Arg.val_var]
      have hwSplit : w.toNat / 2 ^ 32 < 2 ^ 32 ∧ w.toNat % 2 ^ 32 < 2 ^ 32 ∧
          w.toNat = (w.toNat / 2 ^ 32) * 2 ^ 32 + w.toNat % 2 ^ 32 := by
        have hlt64 := w.isLt; omega
      have hsp := u32_split_div10_step carry.toNat (w.toNat / 2 ^ 32) (w.toNat % 2 ^ 32)
        hcarry hwSplit.1 hwSplit.2.1
      have hhiEq : hiBv.toNat = carry.toNat * 2 ^ 32 + w.toNat / 2 ^ 32 := by
        rw [bv64_pack32_toNat (by omega) (by rw [bv64_ushiftRight32]; exact hwSplit.1),
          bv64_ushiftRight32]
      have hq1Eq : q1.toNat = (carry.toNat * 2 ^ 32 + w.toNat / 2 ^ 32) / 10 := by
        rw [BitVec.toNat_udiv, show (10#64).toNat = 10 from rfl, hhiEq]
      have hr1Eq : r1.toNat = (carry.toNat * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 := by
        rw [BitVec.toNat_umod, show (10#64).toNat = 10 from rfl, hhiEq]
      have hloEq : loBv.toNat = r1.toNat * 2 ^ 32 + w.toNat % 2 ^ 32 := by
        have hr1Lt : r1.toNat < 2 ^ 32 := by rw [hr1Eq]; omega
        rw [bv64_pack32_toNat hr1Lt (by rw [bv64_and_mask32]; exact hwSplit.2.1),
          bv64_and_mask32]
      have hq2Eq : q2.toNat = (r1.toNat * 2 ^ 32 + w.toNat % 2 ^ 32) / 10 := by
        rw [BitVec.toNat_udiv, show (10#64).toNat = 10 from rfl, hloEq]
      have hr2Eq : r2.toNat = (r1.toNat * 2 ^ 32 + w.toNat % 2 ^ 32) % 10 := by
        rw [BitVec.toNat_umod, show (10#64).toNat = 10 from rfl, hloEq]
      have hwNewEq : wNew.toNat = q1.toNat * 2 ^ 32 + q2.toNat := by
        apply bv64_pack32_toNat
        · rw [hq1Eq]; exact hsp.1
        · rw [hq2Eq, hr1Eq]; exact hsp.2.1
      have hstep : carry.toNat * 2 ^ 64 + (tmpXs[j.toNat - 1]'(by omega)).toNat =
          10 * wNew.toNat + r2.toNat := by
        have hweq : tmpXs[j.toNat - 1]'(by omega) = w := by
          dsimp [w]; congr 1; exact hj1.symm
        rw [hweq, hwSplit.2.2, hwNewEq, hq1Eq, hq2Eq, hr2Eq, hr1Eq]
        exact hsp.2.2.2
      have hinvNext := mpz_div10_invariant_step (len := curLenBv.toNat) wNew hjPos hjLe
        (by omega) hstep hinv
      have hsetIdx : tmpXs.set (j.toNat - 1) wNew = tmpXs.set (j - 1#64).toNat wNew := by
        rw [hj1]
      rw [hsetIdx] at hinvNext
      have hdropNext : (tmpXs.set (j - 1#64).toNat wNew).drop curLenBv.toNat =
          tmpXs0.drop curLenBv.toNat := by
        rw [← hdropEq]
        apply List.ext_getElem
        · simp [List.length_drop, List.length_set]
        · intro idx hi1 hi2
          simp only [List.getElem_drop]
          rw [List.getElem_set_ne (by omega)]
      refine hIH (j - 1#64).toNat (r2, j - 1#64, ()) _ (by rw [hj1, hmeas]; omega)
        ⟨tmpXs.set (j - 1#64).toNat wNew, rfl, ?_, by rw [hj1]; omega, by simp [hlen],
          hdropNext, ?_, hst.2⟩
      · rw [hr2Eq, hr1Eq]; exact hsp.2.2.1
      · dsimp only at hinvNext; rw [← hj1] at hinvNext; exact hinvNext
    · rw [BitVec.ult, decide_eq_false_iff_not] at hle0
      have h0eq : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0eq] at hle0
      have hj0 : j.toNat = 0 := by omega
      rw [hj0, List.take_zero, mpzLimbsVal_nil, Nat.pow_zero, Nat.zero_add, Nat.one_mul,
        List.drop_zero] at hinv
      exact hk carry tmpXs mk hcarry hlen hdropEq hinv hmk
  · intro J hJ
    c0_step
    have hdropEmpty : List.drop curLenBv.toNat (tmpXs0.take curLenBv.toNat) = [] :=
      List.drop_eq_nil_of_le (by rw [List.length_take_of_le hcurLe]; exact Nat.le_refl _)
    refine hJ curLenBv.toNat (0#64, curLenBv, ()) m ⟨tmpXs0, rfl, by decide, Nat.le_refl _, rfl,
      rfl, ?_, hm⟩
    simp [hdropEmpty, mpzLimbsVal_nil]

/-! ## Phase 4: Outer decimal-digit extraction & byte-reversal loops -/

private theorem nat_to_str_outer_div_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {tmp buf cnBv : Val i64} {tmpXs0 : List (BitVec 64)} {bufBs0 : List UInt8}
    {m : Mem 64} {k : Val i64 → Expr Val Cont [i64]}
    (hcnPos : 1 ≤ cnBv.toNat) (hcnMax : cnBv.toNat ≤ mpzMaxLimbsNat)
    (htmpLen : tmpXs0.length = cnBv.toNat) (hbufLen : bufBs0.length = 20 * cnBv.toNat)
    (hlastNe : tmpXs0[cnBv.toNat - 1]'(by omega) ≠ 0#64)
    (hm : (array64 (tmp + 16#64) tmpXs0 ⋆ bytes (buf + 24#64) bufBs0 ⋆ R) m)
    (hk : ∀ dlenBv : Val i64, ∀ tmpXs bufBs m',
      let val := mpzLimbsVal (tmpXs0.take cnBv.toNat)
      dlenBv.toNat = (natDigitsRev val).length →
      1 ≤ dlenBv.toNat → dlenBv.toNat ≤ 20 * cnBv.toNat →
      tmpXs.length = cnBv.toNat → bufBs.length = 20 * cnBv.toNat →
      bufBs.take dlenBv.toNat = natDigitsRev val →
      (array64 (tmp + 16#64) tmpXs ⋆ bytes (buf + 24#64) bufBs ⋆ R) m' →
      wp rtR2bEnv Q X (k dlenBv) m') :
    wp rtR2bEnv Q X (outerDivExpr tmp buf cnBv (20#64 * cnBv) k) m := by
  unfold outerDivExpr
  let val := mpzLimbsVal (tmpXs0.take cnBv.toNat)
  have hvalPos : 0 < val := mpzLimbsVal_pos_of_last_ne hcnPos (by omega) hlastNe
  have hvalLtPow : val < (2 ^ 64) ^ cnBv.toNat := by
    have hlt := mpzLimbsVal_lt_pow (tmpXs0.take cnBv.toNat)
    rwa [List.length_take_of_le (by omega)] at hlt
  have hpow10 : val < 10 ^ (20 * cnBv.toNat) := by
    have hp := pow_64_lt_pow10_20 hcnPos
    rw [Nat.pow_mul]
    exact Nat.lt_trans hvalLtPow hp
  have hdigMax : (natDigitsRev val).length ≤ 20 * cnBv.toNat := natDigitsRev_length_le hpow10
  have hdigPos : 1 ≤ (natDigitsRev val).length := natDigitsRev_length_pos hvalPos
  have hmaxProd : (20#64 * cnBv).toNat = 20 * cnBv.toNat := by
    rw [BitVec.toNat_mul, show (20#64).toNat = 20 from rfl,
      Nat.mod_eq_of_lt (by unfold mpzMaxLimbsNat at hcnMax; omega)]
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xsP mk =>
    match xsP with
    | (dlen, curLen, PUnit.unit) =>
      ∃ (tmpXs : List (BitVec 64)) (bufBs : List UInt8),
        let V := mpzLimbsVal (tmpXs.take curLen.toNat)
        meas = V ∧
        curLen.toNat ≤ cnBv.toNat ∧
        tmpXs.length = cnBv.toNat ∧
        bufBs.length = 20 * cnBv.toNat ∧
        dlen.toNat ≤ (natDigitsRev val).length ∧
        (0 < curLen.toNat →
          ∃ h : curLen.toNat - 1 < tmpXs.length, tmpXs[curLen.toNat - 1]'h ≠ 0#64) ∧
        bufBs.take dlen.toNat = (natDigitsRev val).take dlen.toNat ∧
        (natDigitsRev val).take dlen.toNat ++ natDigitsRev V = natDigitsRev val ∧
        (array64 (tmp + 16#64) tmpXs ⋆ bytes (buf + 24#64) bufBs ⋆ R) mk
  apply wp_loop_group Inv
  · intro J meas xsP mk hIH hInv
    rcases xsP with ⟨dlen, curLen, ⟨⟩⟩
    rcases hInv with ⟨tmpXs, bufBs, hmeas, hcurLe, htmpL, hbufL, hdlenLe, hnz, hpref, hcat, hmk⟩
    c0_step
    rw [wp_jnz]; dsimp only [Arg.val_var]
    refine ⟨fun hgt => ?_, fun hle0 => ?_⟩
    · rw [BitVec.ult, decide_eq_true_eq] at hgt
      have h0eq : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0eq] at hgt
      have hcurPos : 0 < curLen.toNat := hgt
      obtain ⟨_hltCur, hlastCur⟩ := hnz hcurPos
      have hVpos : 0 < mpzLimbsVal (tmpXs.take curLen.toNat) :=
        mpzLimbsVal_pos_of_last_ne hcurPos (by omega) hlastCur
      have hmkT : (array64 (tmp + 16#64) tmpXs ⋆ (bytes (buf + 24#64) bufBs ⋆ R)) mk :=
        sep_cast hmk (by ac_rfl)
      refine nat_to_str_inner_div10_wp (by omega) (by unfold mpzMaxLimbsNat at hcnMax; omega)
        hmkT fun remBv tmpXs1 m1 hremLt htmp1L _ hdivEq hm1 => ?_
      refine LeanQbe.T.wp_unroll_group fun Jafter hJafter => ?_
      c0_step
      rw [wp_jnz]; dsimp only [Arg.val_var]
      have hdlenLt : dlen.toNat < (natDigitsRev val).length := by
        have hvp : 1 ≤ (natDigitsRev (mpzLimbsVal (tmpXs.take curLen.toNat))).length :=
          natDigitsRev_length_pos hVpos
        have hlenSum := congrArg List.length hcat
        rw [List.length_append, List.length_take_of_le hdlenLe] at hlenSum
        omega
      have hultTrue : BitVec.ult dlen (20#64 * cnBv) = true := by
        rw [BitVec.ult, decide_eq_true_eq, hmaxProd]
        omega
      refine ⟨fun _ => ?_, fun hbad => by simp [hultTrue] at hbad⟩
      c0_let_simp
      rw [show (24 : BitVec 64) = 24#64 from rfl, show (48 : BitVec 64) = 48#64 from rfl,
        show (1 : BitVec 64) = 1#64 from rfl]
      have hmB : (bytes (buf + 24#64) bufBs ⋆ (array64 (tmp + 16#64) tmpXs1 ⋆ R)) m1 :=
        sep_cast hm1 (by ac_rfl)
      have hst := bytes_set_store8 (a := buf) (i := dlen) (48#64 + remBv) hmB
        (by rw [hbufL]; omega) (by unfold mpzMaxLimbsNat at hcnMax; omega)
      rw [wp_store]; dsimp only [Arg.val_var]
      refine ⟨hst.1, ?_⟩
      c0_step
      apply hJafter
      c0_let_simp
      rw [← BitVec.truncate_eq_setWidth]
      have hm2 : (array64 (tmp + 16#64) tmpXs1 ⋆
          (bytes (buf + 24#64)
            (bufBs.set dlen.toNat (UInt8.ofNat (BitVec.truncate 8 (48#64 + remBv)).toNat)) ⋆ R))
          (storeMem m1 i8 (buf + 24#64 + dlen) (BitVec.truncate 8 (48#64 + remBv))) :=
        sep_cast hst.2 (by ac_rfl)
      change wp rtR2bEnv Q X (trimLimbsExpr tmp curLen
        (fun cnNext => Expr.jump J (Arg.var (dlen + 1#64), Arg.var cnNext, ()))) _
      refine nat_to_str_trim_limbs_wp (Q := Q) (X := X)
        (k := fun cnNext => Expr.jump J (Arg.var (dlen + 1#64), Arg.var cnNext, ()))
        (xs := tmpXs1) (sz := curLen) (by omega)
        (by unfold mpzMaxLimbsNat at hcnMax; omega) hm2 fun cnNext hcnNextEq hcnNextLe => ?_
      have hdivExit := mpz_div10_exit_eq hremLt hdivEq
      have htrimVal : mpzLimbsVal (tmpXs1.take cnNext.toNat) =
          mpzLimbsVal (tmpXs.take curLen.toNat) / 10 := by
        rw [hcnNextEq, trimZeroLimbsLen_val, hdivExit.2]
      have hdigStep := natDigitsRev_take_step hVpos hcat hdlenLt
      have hadd1 : (dlen + 1#64).toNat = dlen.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by unfold mpzMaxLimbsNat at hcnMax; omega)]
      have hbyteEq : UInt8.ofNat (BitVec.truncate 8 (48#64 + remBv)).toNat =
          UInt8.ofNat (48 + mpzLimbsVal (tmpXs.take curLen.toNat) % 10) := by
        have hlt256 : (48#64 + remBv).toNat = 48 + remBv.toNat := by
          rw [BitVec.toNat_add, show (48#64).toNat = 48 from rfl, Nat.mod_eq_of_lt (by omega)]
        rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, hlt256,
          Nat.mod_eq_of_lt (by omega), hdivExit.1]
      let bufBs2 := bufBs.set dlen.toNat (UInt8.ofNat (BitVec.truncate 8 (48#64 + remBv)).toNat)
      have hbuf2L : bufBs2.length = 20 * cnBv.toNat := by simp [bufBs2, hbufL]
      have hpref2 : bufBs2.take (dlen + 1#64).toNat =
          (natDigitsRev val).take (dlen + 1#64).toNat := by
        rw [hadd1, list_take_succ_append4 bufBs2 (by omega) (by rw [hbuf2L]; omega),
          list_take_succ_append4 (natDigitsRev val) (by omega) (by omega),
          list_take_set_of_le4 bufBs _ (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [hpref]
        have hgetSelf : bufBs2[dlen.toNat]'(by omega) =
            UInt8.ofNat (BitVec.truncate 8 (48#64 + remBv)).toNat :=
          List.getElem_set_self (by rw [List.length_set]; omega)
        simp only [hgetSelf, hbyteEq, hdigStep.1]
      have hcat2 : (natDigitsRev val).take (dlen + 1#64).toNat ++
          natDigitsRev (mpzLimbsVal (tmpXs1.take cnNext.toNat)) = natDigitsRev val := by
        rw [hadd1, htrimVal]
        exact hdigStep.2
      have hVlt : mpzLimbsVal (tmpXs1.take cnNext.toNat) < meas := by
        rw [htrimVal, hmeas]
        exact Nat.div_lt_self hVpos (by decide : 1 < 10)
      refine hIH _ (dlen + 1#64, cnNext, ()) _ hVlt
        ⟨tmpXs1, bufBs2, rfl, by omega, by omega, hbuf2L, by rw [hadd1]; omega, ?_, hpref2,
          hcat2, by dsimp only [bufBs2]; exact sep_cast hm2 (by ac_rfl)⟩
      intro hposNext
      have htrPos : 0 < trimZeroLimbsLen tmpXs1 curLen.toNat := by omega
      have hlast := trimZeroLimbsLen_last_ne tmpXs1 curLen.toNat (by omega) htrPos hcnNextEq
      exact ⟨by omega, hlast.2.2.2⟩
    · rw [BitVec.ult, decide_eq_false_iff_not] at hle0
      have h0eq : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0eq] at hle0
      have hcur0 : curLen.toNat = 0 := by omega
      rw [hcur0, List.take_zero, mpzLimbsVal_nil, natDigitsRev_zero, List.append_nil] at hcat
      have hdlenEq : dlen.toNat = (natDigitsRev val).length := by
        have hlenCat := congrArg List.length hcat
        rw [List.length_take_of_le hdlenLe] at hlenCat
        exact hlenCat
      rw [hcat] at hpref
      exact hk dlen tmpXs bufBs mk hdlenEq (by omega) (by omega) htmpL hbufL hpref hmk
  · intro J hJ
    c0_step
    refine hJ val (0#64, cnBv, ()) m ⟨tmpXs0, bufBs0, rfl, Nat.le_refl _, htmpLen, hbufLen,
      Nat.zero_le _, fun _ => ⟨by omega, hlastNe⟩, by simp, by simp [val], hm⟩

private theorem nat_to_str_rev_loop_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {buf s dlenBv : Val i64} {bufBs sBs0 : List UInt8} {m : Mem 64}
    {k : Expr Val Cont [i64]}
    (hdlenPos : 1 ≤ dlenBv.toNat) (hdlenBuf : dlenBv.toNat ≤ bufBs.length)
    (hbufFit : bufBs.length ≤ 2 ^ 64) (hsLen : sBs0.length = dlenBv.toNat)
    (hm : (bytes (buf + 24#64) bufBs ⋆ bytes (s + 32#64) sBs0 ⋆ R) m)
    (hk : ∀ m', (bytes (buf + 24#64) bufBs ⋆
        bytes (s + 32#64) (bufBs.take dlenBv.toNat).reverse ⋆ R) m' → wp rtR2bEnv Q X k m') :
    wp rtR2bEnv Q X (revLoopExpr buf s dlenBv k) m := by
  unfold revLoopExpr
  let rev := (bufBs.take dlenBv.toNat).reverse
  have hrevL : rev.length = dlenBv.toNat := by
    dsimp [rev]; rw [List.length_reverse, List.length_take_of_le hdlenBuf]
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xsP mk =>
    match xsP with
    | (idx, PUnit.unit) =>
      ∃ sBs : List UInt8,
        meas = dlenBv.toNat - idx.toNat ∧
        idx.toNat ≤ dlenBv.toNat ∧
        sBs.length = dlenBv.toNat ∧
        sBs.take idx.toNat = rev.take idx.toNat ∧
        (bytes (buf + 24#64) bufBs ⋆ bytes (s + 32#64) sBs ⋆ R) mk
  apply wp_loop_group Inv
  · intro J meas xsP mk hIH hInv
    rcases xsP with ⟨idx, ⟨⟩⟩
    rcases hInv with ⟨sBs, hmeas, hidxLe, hsL, htake, hmk⟩
    c0_step
    rw [wp_jnz]; dsimp only [Arg.val_var]
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · rw [BitVec.ult, decide_eq_true_eq] at hlt
      have hiLt : idx.toNat < dlenBv.toNat := hlt
      c0_let_simp
      rw [show (24 : BitVec 64) = 24#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
        show (32 : BitVec 64) = 32#64 from rfl]
      have hsrcSub : (dlenBv - 1#64 - idx).toNat = dlenBv.toNat - 1 - idx.toNat := by
        have h1 : (dlenBv - 1#64).toNat = dlenBv.toNat - 1 := by
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
            (by rw [show (1#64).toNat = 1 from rfl]; omega))]
          rfl
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1]; omega)), h1]
      have hmkB : (bytes (buf + 24#64) bufBs ⋆ (bytes (s + 32#64) sBs ⋆ R)) mk :=
        sep_cast hmk (by ac_rfl)
      have hld := r2_c0_load_bytes_bv (a := buf + 24#64) (i := dlenBv - 1#64 - idx) hmkB
        (by rw [hsrcSub]; omega) hbufFit
      apply wp_load_of (v := BitVec.ofNat 8 (bufBs[(dlenBv - 1#64 - idx).toNat]).toNat)
        (by simpa [Arg.val_var] using hld)
      c0_let_simp
      let bV := BitVec.ofNat 8 (bufBs[(dlenBv - 1#64 - idx).toNat]).toNat
      have hmS : (bytes (s + 32#64) sBs ⋆ (bytes (buf + 24#64) bufBs ⋆ R)) mk :=
        sep_cast hmk (by ac_rfl)
      have hst := bytes_set_store8_32 (a := s) (i := idx) bV hmS
        (by rw [hsL]; exact hiLt) (by omega)
      rw [wp_store]; dsimp only [Arg.val_var]
      refine ⟨hst.1, ?_⟩
      c0_step
      have hadd1 : (idx + 1#64).toNat = idx.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hm2 : (bytes (buf + 24#64) bufBs ⋆
          bytes (s + 32#64) (sBs.set idx.toNat (UInt8.ofNat bV.toNat)) ⋆ R)
          (storeMem mk i8 (s + 32#64 + idx) bV) :=
        sep_cast hst.2 (by
          rw [← Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm (bytes (s + 32#64) _)])
      refine hIH (dlenBv.toNat - (idx.toNat + 1)) (idx + 1#64, ()) _ (by omega)
        ⟨sBs.set idx.toNat (UInt8.ofNat bV.toNat), by rw [hadd1], by rw [hadd1]; omega,
          by simp [hsL], ?_, hm2⟩
      rw [hadd1,
        list_take_succ_append4 (sBs.set idx.toNat (UInt8.ofNat bV.toNat)) (by omega)
          (by simp [hsL]; omega),
        list_take_succ_append4 rev (by omega) (by rw [hrevL]; exact hiLt),
        list_take_set_of_le4 sBs _ (by omega)]
      have hsetSelf :
          (sBs.set idx.toNat (UInt8.ofNat bV.toNat))[idx.toNat]'(by simp [hsL]; omega) =
            UInt8.ofNat bV.toNat :=
        List.getElem_set_self (by rw [List.length_set]; omega)
      have hbEq : UInt8.ofNat bV.toNat = bufBs[(dlenBv - 1#64 - idx).toNat] := by
        have h1 : bV.toNat = (bufBs[(dlenBv - 1#64 - idx).toNat]).toNat := by
          dsimp [bV]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
        rw [h1]
        exact UInt8.ofNat_toNat
      have hrevGet : rev[idx.toNat]'(by rw [hrevL]; exact hiLt) =
          bufBs[(dlenBv - 1#64 - idx).toNat] := by
        dsimp [rev]
        rw [List.getElem_reverse
          (by rw [List.length_reverse, List.length_take_of_le hdlenBuf]; exact hiLt)]
        rw [List.getElem_take]
        congr 1
        rw [List.length_take_of_le hdlenBuf]
        have := dlenBv.isLt
        omega
      simp only [Nat.add_sub_cancel]
      rw [htake, hsetSelf, hbEq, hrevGet]
    · rw [BitVec.ult, decide_eq_false_iff_not] at hge
      have hiEq : idx.toNat = dlenBv.toNat := by
        have hnot : ¬ (idx.toNat < dlenBv.toNat) := hge
        omega
      have hsEq : sBs = rev := by
        have heq := htake
        rw [hiEq, List.take_of_length_le (Nat.le_of_eq hsL),
          List.take_of_length_le (Nat.le_of_eq hrevL)] at heq
        exact heq
      rw [hsEq] at hmk
      exact hk mk hmk
  · intro J hJ
    c0_step
    exact hJ dlenBv.toNat (0#64, ()) m ⟨sBs0, rfl, Nat.zero_le _, hsLen, by simp, hm⟩

/-! ## Phase 5: Post-trim MPZ orchestration & top-level `lcnf_nat_to_str_wp` -/

private theorem lcnfHeap_focus_obj {objs : List LcnfObj} {o : LcnfObj} (ho : o ∈ objs) :
    ∃ i, ∃ (hi : i < objs.length), objs[i] = o ∧
      lcnfHeap objs = lcnfObjMem o ⋆ (lcnfHeap (objs.take i) ⋆ lcnfHeap (objs.drop (i + 1))) := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ho
  have hf := lcnfHeap_focus objs hi
  rw [heq] at hf
  exact ⟨i, hi, heq, hf⟩

private theorem nat_to_str_mpz_free_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt tmp buf s cnBv : Val i64} {st : RtC0State} {sObj : LcnfObj} {tmpXsF : List (BitVec 64)}
    {m : Mem 64}
    (hbuf0 : buf ≠ 0#64) (hbuf8 : buf.toNat % 8 = 0)
    (htmp0 : tmp ≠ 0#64) (htmp8 : tmp.toNat % 8 = 0)
    (hcnLeMax : cnBv.toNat ≤ mpzMaxLimbsNat) (htmpFL : tmpXsF.length = cnBv.toNat)
    (hm : (lcnfObjMem sObj ⋆
      (rtC0Inv rt st ⋆ freeObjLayout buf (sarrayAllocBytes (20 * cnBv.toNat)) baHeaderWord ⋆
        array64 (tmp + 16#64) tmpXsF ⋆ cell64 tmp mpzHeaderWord ⋆
        cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m)
    (hk : ∀ st' m', st'.PreservesMeta st → st'.rem ≤ st.rem →
      (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ R) m' → Q (s, ()) m') :
    wp rtR2bEnv Q X (mpzFreeExpr rt tmp buf s) m := by
  unfold mpzFreeExpr
  apply wp_call_of_spec
  apply rtR2bEnv_lcnf_free_obj
  dsimp only [lcnfFreeObjSpec, vals, Arg.val_var]
  rw [ite_eq_right (fun h => h (bv64_and1_zero_of_mod8 hbuf8))]
  have hbsaLo : rtMinObjBytes ≤ sarrayAllocBytes (20 * cnBv.toNat) := by
    unfold rtMinObjBytes sarrayAllocBytes align8; omega
  have hbsaHi : sarrayAllocBytes (20 * cnBv.toNat) < rtMaxObjBytes := by
    unfold rtMaxObjBytes sarrayAllocBytes align8 mpzMaxLimbsNat at *; omega
  have hm' : (rtC0Inv rt st ⋆ freeObjLayout buf (sarrayAllocBytes (20 * cnBv.toNat)) baHeaderWord ⋆
      (lcnfObjMem sObj ⋆ array64 (tmp + 16#64) tmpXsF ⋆
        cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m := by
    refine sep_cast hm ?_
    simp only [Std.ExtHashMap.sep_assoc]
    iterate 2 rw [msep_left_comm (lcnfObjMem sObj)]
  refine ⟨st, baHeaderWord, sarrayAllocBytes (20 * cnBv.toNat),
    lcnfObjMem sObj ⋆ array64 (tmp + 16#64) tmpXsF ⋆
      cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R,
    hbuf0, hbuf8, hbsaLo, hbsaHi, align8_mod8 _, hm',
    fun st1 m1 hpr1 hrem1 _ hm1 => ?_⟩
  have htmpFree : freeObjLayout tmp (mpzAllocBytes cnBv.toNat) mpzHeaderWord =
      fun mx => ∃ w8 : BitVec 64,
        (w8 &&& 4294967295#64).toNat ≤ 33554429 ∧
        mpzAllocBytes cnBv.toNat = 16 + 8 * (w8 &&& 4294967295#64).toNat ∧
        ((cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) w8) ⋆
          region (tmp + 16#64) (mpzAllocBytes cnBv.toNat - 16)) mx := by
    unfold freeObjLayout
    have ht : (mpzHeaderWord >>> 56).toNat = mpzTag := by decide
    rw [ht, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl]
  have htmpLay : (rtC0Inv rt st1 ⋆
      (freeObjLayout tmp (mpzAllocBytes cnBv.toNat) mpzHeaderWord ⋆
        (lcnfObjMem sObj ⋆ R))) m1 := by
    have hm1a : (rtC0Inv rt st1 ⋆
        (((cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32))) ⋆
          region (tmp + 16#64) (mpzAllocBytes cnBv.toNat - 16)) ⋆
          (lcnfObjMem sObj ⋆ R))) m1 := by
      have hm1b : (rtC0Inv rt st1 ⋆
          (((cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32))) ⋆
            array64 (tmp + 16#64) tmpXsF) ⋆ (lcnfObjMem sObj ⋆ R))) m1 := by
        refine sep_cast hm1 ?_
        simp only [Std.ExtHashMap.sep_assoc]
        repeat rw [msep_left_comm _ (lcnfObjMem sObj)]
        repeat rw [msep_left_comm _ (array64 (tmp + 16#64) _)]
        repeat rw [msep_left_comm _ (cell64 (tmp + 8#64) _)]
        repeat rw [msep_left_comm _ (cell64 tmp _)]
        repeat rw [msep_left_comm _ (rtC0Inv rt st1)]
        try rfl
      refine sep_mono_r
        (fun _ x => sep_mono (fun _ y => sep_mono_r (fun _ z => ?_) y) x) hm1b
      have hrg := array64_to_region (by unfold mpzMaxLimbsNat at hcnLeMax; omega) z
      rw [htmpFL] at hrg
      unfold mpzAllocBytes
      simpa using hrg
    rw [htmpFree]
    refine sep_mono_r (fun _ x => sep_mono (fun _ y => ?_) x) hm1a
    have hlow := bv64_pack32_low (a := cnBv) (b := cnBv)
      (by unfold mpzMaxLimbsNat at hcnLeMax; omega)
    exact ⟨cnBv ||| (cnBv <<< 32),
      by rw [hlow]; unfold mpzMaxLimbsNat at hcnLeMax; omega,
      by rw [hlow]; rfl, y⟩
  apply wp_call_of_spec
  apply rtR2bEnv_lcnf_free_obj
  dsimp only [lcnfFreeObjSpec, vals, Arg.val_var]
  rw [ite_eq_right (fun h => h (bv64_and1_zero_of_mod8 htmp8))]
  have hmpzLo : rtMinObjBytes ≤ mpzAllocBytes cnBv.toNat := by
    unfold rtMinObjBytes mpzAllocBytes; omega
  have hmpzHi : mpzAllocBytes cnBv.toNat < rtMaxObjBytes := by
    unfold rtMaxObjBytes mpzAllocBytes mpzMaxLimbsNat at *; omega
  have hmpzMod : mpzAllocBytes cnBv.toNat % 8 = 0 := by unfold mpzAllocBytes; omega
  refine ⟨st1, mpzHeaderWord, mpzAllocBytes cnBv.toNat, lcnfObjMem sObj ⋆ R,
    htmp0, htmp8, hmpzLo, hmpzHi, hmpzMod,
    sep_cast htmpLay (Std.ExtHashMap.sep_assoc _ _ _).symm,
    fun st2 m2 hpr2 hrem2 _ hm2 => ?_⟩
  rw [wp_ret]; dsimp only [vals, Arg.val_var]
  exact hk st2 m2 (hpr1.trans hpr2) (by omega)
    (sep_cast hm2 (Std.ExtHashMap.sep_assoc _ _ _).symm)

private theorem rev_free_blk
    (bBuf bS rt S M b8 b0 b16 rBuf rest : Mem 64 → Prop) :
    (bBuf ⋆ bS ⋆ (rt ⋆ S ⋆ M ⋆ b8 ⋆ b0 ⋆ b16 ⋆ rBuf ⋆ rest)) =
    (S ⋆ bS ⋆ M ⋆ (rt ⋆ ((((b0 ⋆ b8) ⋆ b16) ⋆ (bBuf ⋆ rBuf)) ⋆ rest))) := by
  simp only [Std.ExtHashMap.sep_assoc]
  rw [msep_left_comm b8 b0,
    msep_left_comm bBuf bS, msep_left_comm bBuf rt, msep_left_comm bBuf S,
    msep_left_comm bBuf M, msep_left_comm bBuf b0, msep_left_comm bBuf b8,
    msep_left_comm bBuf b16,
    msep_left_comm rt S, msep_left_comm rt M, msep_left_comm bS S]

private theorem rev_free_reassoc
    (bBuf bS rt s0 s8 s16 s24 bS0 rS b8 b0 b16 rBuf r1 r2 r3 r4 : Mem 64 → Prop) :
    (bBuf ⋆ bS ⋆ (rt ⋆ s0 ⋆ s8 ⋆ s16 ⋆ s24 ⋆ bS0 ⋆ rS ⋆ b8 ⋆ b0 ⋆ b16 ⋆
      rBuf ⋆ r1 ⋆ r2 ⋆ r3 ⋆ r4)) =
    (s0 ⋆ s8 ⋆ s16 ⋆ s24 ⋆ bS ⋆ bS0 ⋆ rS ⋆
      (rt ⋆ ((((b0 ⋆ b8) ⋆ b16) ⋆ (bBuf ⋆ rBuf)) ⋆ (r1 ⋆ r2 ⋆ r3 ⋆ r4)))) := by
  have h := rev_free_blk bBuf bS rt (s0 ⋆ s8 ⋆ s16 ⋆ s24) (bS0 ⋆ rS)
    b8 b0 b16 rBuf (r1 ⋆ r2 ⋆ r3 ⋆ r4)
  simp only [Std.ExtHashMap.sep_assoc] at h ⊢
  exact h

private theorem nat_to_str_rev_free_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt tmp buf s dlenBv cnBv : Val i64} {st : RtC0State}
    {sBs0 bufBsF : List UInt8} {tmpXsF : List (BitVec 64)} {m : Mem 64} {val : Nat}
    (hs0 : s ≠ 0#64) (hs8 : s.toNat % 8 = 0)
    (hbuf0 : buf ≠ 0#64) (hbuf8 : buf.toNat % 8 = 0)
    (htmp0 : tmp ≠ 0#64) (htmp8 : tmp.toNat % 8 = 0)
    (hcnLeMax : cnBv.toNat ≤ mpzMaxLimbsNat)
    (hdlenPos : 1 ≤ dlenBv.toNat) (hdlenMax : dlenBv.toNat ≤ 20 * cnBv.toNat)
    (hadd1D : (dlenBv + 1#64).toNat = dlenBv.toNat + 1)
    (hvalPos : 0 < val) (hbufTake : bufBsF.take dlenBv.toNat = natDigitsRev val)
    (hsBs0L : sBs0.length = dlenBv.toNat) (htmpFL : tmpXsF.length = cnBv.toNat)
    (hbufFL : bufBsF.length = 20 * cnBv.toNat)
    (hm : (bytes (buf + 24#64) bufBsF ⋆ bytes (s + 32#64) sBs0 ⋆
      (rtC0Inv rt st ⋆ cell64 s strHeaderWord ⋆ cell64 (s + 8#64) (dlenBv + 1#64) ⋆
        cell64 (s + 16#64) (dlenBv + 1#64) ⋆ cell64 (s + 24#64) dlenBv ⋆
        bytes (s + 32#64 + dlenBv) [0] ⋆
        region (s + 32#64 + dlenBv + 1#64)
          (strAllocBytes (dlenBv.toNat + 1) - (32 + dlenBv.toNat + 1)) ⋆
        cell64 (buf + 8#64) dlenBv ⋆ cell64 buf baHeaderWord ⋆
        cell64 (buf + 16#64) (20#64 * cnBv) ⋆
        region (buf + 24#64 + BitVec.ofNat 64 (20 * cnBv.toNat))
          (sarrayAllocBytes (20 * cnBv.toNat) - 24 - 20 * cnBv.toNat) ⋆
        array64 (tmp + 16#64) tmpXsF ⋆ cell64 tmp mpzHeaderWord ⋆
        cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m)
    (hk : ∀ st' m', st'.PreservesMeta st → st'.rem ≤ st.rem →
      let dec := natToDecimalBytes val
      let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
      StrCanon sObj → (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ R) m' → Q (s, ()) m') :
    wp rtR2bEnv Q X (revFreeExpr rt tmp buf s dlenBv) m := by
  unfold revFreeExpr
  refine nat_to_str_rev_loop_wp hdlenPos (by rw [hbufFL]; exact hdlenMax)
    (by rw [hbufFL]; unfold mpzMaxLimbsNat at hcnLeMax; omega) hsBs0L hm fun m7 hm7 => ?_
  have hdecEq : natToDecimalBytes val = (bufBsF.take dlenBv.toNat).reverse := by
    rw [hbufTake]; unfold natToDecimalBytes; rw [ite_eq_right (by omega)]
  have hdecLen2 : (natToDecimalBytes val).length = dlenBv.toNat := by
    rw [hdecEq, List.length_reverse, List.length_take_of_le (by omega)]
  have hcapBv : BitVec.ofNat 64 (dlenBv.toNat + 1) = dlenBv + 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [bv64_toNat_ofNat_lt4 (by unfold mpzMaxLimbsNat at hcnLeMax; omega), hadd1D]
  have hdlenBv : BitVec.ofNat 64 dlenBv.toNat = dlenBv :=
    BitVec.eq_of_toNat_eq (bv64_toNat_ofNat_lt4 (by unfold mpzMaxLimbsNat at hcnLeMax; omega))
  let dec := natToDecimalBytes val
  let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
  have h20mul : (20#64 * cnBv).toNat = 20 * cnBv.toNat := by
    rw [BitVec.toNat_mul, show (20#64 : BitVec 64).toNat = 20 from rfl,
      Nat.mod_eq_of_lt (by unfold mpzMaxLimbsNat at hcnLeMax; omega)]
  have hsMem : (lcnfObjMem sObj ⋆
      (rtC0Inv rt st ⋆ freeObjLayout buf (sarrayAllocBytes (20 * cnBv.toNat)) baHeaderWord ⋆
        array64 (tmp + 16#64) tmpXsF ⋆
        cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m7 := by
    have hmStrP : (cell64 s strHeaderWord ⋆
        cell64 (s + 8#64) (BitVec.ofNat 64 (dec.length + 1)) ⋆
        cell64 (s + 16#64) (BitVec.ofNat 64 (dec.length + 1)) ⋆
        cell64 (s + 24#64) (BitVec.ofNat 64 dec.length) ⋆
        bytes (s + 32#64) dec ⋆
        bytes (s + 32#64 + BitVec.ofNat 64 dec.length) [0] ⋆
        region (s + 32#64 + BitVec.ofNat 64 dec.length + 1#64)
          (strAllocBytes (dec.length + 1) - (32 + dec.length + 1)) ⋆
        (rtC0Inv rt st ⋆
          freeObjLayout buf (sarrayAllocBytes (20 * cnBv.toNat)) baHeaderWord ⋆
          array64 (tmp + 16#64) tmpXsF ⋆
          cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m7 := by
      have hbufFree : freeObjLayout buf (sarrayAllocBytes (20 * cnBv.toNat)) baHeaderWord =
          fun mx => ∃ w16 : BitVec 64,
            w16.toNat ≤ 268435455 ∧
            sarrayAllocBytes (20 * cnBv.toNat) =
              align8 (24 + ((baHeaderWord >>> 48).toNat % 128) * w16.toNat) ∧
            (((cell64 buf baHeaderWord ⋆ region (buf + 8#64) 8) ⋆
              cell64 (buf + 16#64) w16) ⋆
              region (buf + 24#64) (sarrayAllocBytes (20 * cnBv.toNat) - 24)) mx := by
        unfold freeObjLayout
        have ht : (baHeaderWord >>> 56).toNat = sarrayTag := by decide
        rw [ht, ite_eq_right (by decide), ite_eq_left rfl]
      have hm7a : (cell64 s strHeaderWord ⋆
          cell64 (s + 8#64) (dlenBv + 1#64) ⋆
          cell64 (s + 16#64) (dlenBv + 1#64) ⋆
          cell64 (s + 24#64) dlenBv ⋆
          bytes (s + 32#64) (bufBsF.take dlenBv.toNat).reverse ⋆
          bytes (s + 32#64 + dlenBv) [0] ⋆
          region (s + 32#64 + dlenBv + 1#64)
            (strAllocBytes (dlenBv.toNat + 1) - (32 + dlenBv.toNat + 1)) ⋆
          (rtC0Inv rt st ⋆
            (freeObjLayout buf (sarrayAllocBytes (20 * cnBv.toNat)) baHeaderWord ⋆
              (array64 (tmp + 16#64) tmpXsF ⋆
                cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R))))
          m7 := by
        have hm7b : (cell64 s strHeaderWord ⋆
            cell64 (s + 8#64) (dlenBv + 1#64) ⋆
            cell64 (s + 16#64) (dlenBv + 1#64) ⋆
            cell64 (s + 24#64) dlenBv ⋆
            bytes (s + 32#64) (bufBsF.take dlenBv.toNat).reverse ⋆
            bytes (s + 32#64 + dlenBv) [0] ⋆
            region (s + 32#64 + dlenBv + 1#64)
              (strAllocBytes (dlenBv.toNat + 1) - (32 + dlenBv.toNat + 1)) ⋆
            (rtC0Inv rt st ⋆
              ((((cell64 buf baHeaderWord ⋆ region (buf + 8#64) 8) ⋆
                cell64 (buf + 16#64) (20#64 * cnBv)) ⋆
                region (buf + 24#64) (sarrayAllocBytes (20 * cnBv.toNat) - 24)) ⋆
                (array64 (tmp + 16#64) tmpXsF ⋆
                  cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R))))
            m7 := by
          have hcell8 : ∀ mx, (cell64 (buf + 8#64) dlenBv) mx → (region (buf + 8#64) 8) mx :=
            fun _ hx => cell64_to_region hx
          have hregBuf : ∀ mx,
              (bytes (buf + 24#64) bufBsF ⋆
                region (buf + 24#64 + BitVec.ofNat 64 (20 * cnBv.toNat))
                  (sarrayAllocBytes (20 * cnBv.toNat) - 24 - 20 * cnBv.toNat)) mx →
              region (buf + 24#64) (sarrayAllocBytes (20 * cnBv.toNat) - 24) mx := by
            intro mx hx
            have h1 := sep_mono (fun _ hb => bytes_to_region hb) hx
            rw [hbufFL] at h1
            exact (region_merge_eq (a := buf + 24#64) (n1 := 20 * cnBv.toNat)
              (n2 := sarrayAllocBytes (20 * cnBv.toNat) - 24 - 20 * cnBv.toNat)
              (n := sarrayAllocBytes (20 * cnBv.toNat) - 24)
              (by unfold sarrayAllocBytes align8; omega)
              (by unfold sarrayAllocBytes align8 mpzMaxLimbsNat at *; omega)) ▸ h1
          have hmRe : (cell64 s strHeaderWord ⋆ cell64 (s + 8#64) (dlenBv + 1#64) ⋆
              cell64 (s + 16#64) (dlenBv + 1#64) ⋆ cell64 (s + 24#64) dlenBv ⋆
              bytes (s + 32#64) (bufBsF.take dlenBv.toNat).reverse ⋆
              bytes (s + 32#64 + dlenBv) [0] ⋆
              region (s + 32#64 + dlenBv + 1#64)
                (strAllocBytes (dlenBv.toNat + 1) - (32 + dlenBv.toNat + 1)) ⋆
              (rtC0Inv rt st ⋆
                ((((cell64 buf baHeaderWord ⋆ cell64 (buf + 8#64) dlenBv) ⋆
                  cell64 (buf + 16#64) (20#64 * cnBv)) ⋆
                  (bytes (buf + 24#64) bufBsF ⋆
                    region (buf + 24#64 + BitVec.ofNat 64 (20 * cnBv.toNat))
                      (sarrayAllocBytes (20 * cnBv.toNat) - 24 - 20 * cnBv.toNat))) ⋆
                  (array64 (tmp + 16#64) tmpXsF ⋆
                    cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R))))
              m7 := by
            exact sep_cast hm7 (rev_free_reassoc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          exact sep_mono_r (fun _ x => sep_mono_r (fun _ y => sep_mono (fun _ z =>
            sep_mono2 (fun _ w => sep_mono (fun _ u => sep_mono_r hcell8 u) w)
              hregBuf _ z) y) x) hmRe
        rw [hbufFree]
        refine sep_mono_r (fun _ x => sep_mono_r (fun _ y => sep_mono (fun _ z => ?_) y) x) hm7b
        exact ⟨20#64 * cnBv, by rw [h20mul]; unfold mpzMaxLimbsNat at hcnLeMax; omega,
          by rw [h20mul, show (baHeaderWord >>> 48).toNat % 128 = 1 by decide, Nat.one_mul]; rfl,
          z⟩
      dsimp only [dec]; rw [hdecLen2, hdecEq, hcapBv, hdlenBv]
      have htail : (rtC0Inv rt st ⋆
          (freeObjLayout buf (sarrayAllocBytes (20 * cnBv.toNat)) baHeaderWord ⋆
            (array64 (tmp + 16#64) tmpXsF ⋆
              cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R))) =
          (rtC0Inv rt st ⋆
            freeObjLayout buf (sarrayAllocBytes (20 * cnBv.toNat)) baHeaderWord ⋆
            array64 (tmp + 16#64) tmpXsF ⋆
            cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R) := by
        simp only [Std.ExtHashMap.sep_assoc]
      exact htail ▸ hm7a
    exact mkStrObj_mem_of_parts
      (by dsimp only [dec]; rw [hdecLen2]; unfold strMaxCap mpzMaxLimbsNat at *; omega)
      (Nat.le_refl _) hmStrP
  have hcanonS : StrCanon sObj :=
    mkStrObj_canon hs0 hs8 (by decide) (Nat.le_refl _)
      (by dsimp only [dec]; rw [hdecLen2]; unfold strMaxCap mpzMaxLimbsNat at *; omega)
      (by dsimp only [dec]; rw [hdecLen2]; unfold mpzMaxLimbsNat at *; omega)
  exact nat_to_str_mpz_free_wp hbuf0 hbuf8 htmp0 htmp8 hcnLeMax htmpFL hsMem
    fun st' m' hpr' hrem' hm' => hk st' m' hpr' hrem' hcanonS hm'

private theorem nat_to_str_after_dec_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt tmp cnBv : Val i64} {st : RtC0State} {tmpXs : List (BitVec 64)} {m : Mem 64}
    {val : Nat}
    (htmp0 : tmp ≠ 0#64) (htmp8 : tmp.toNat % 8 = 0)
    (hcnPos : 1 ≤ cnBv.toNat) (hcnLeMax : cnBv.toNat ≤ mpzMaxLimbsNat)
    (htmpL : tmpXs.length = cnBv.toNat)
    (hlast : tmpXs[cnBv.toNat - 1]'(by omega) ≠ 0#64)
    (hval : mpzLimbsVal (tmpXs.take cnBv.toNat) = val)
    (hneed : sarrayAllocBytes (20 * cnBv.toNat) + strAllocBytes (20 * cnBv.toNat + 1) ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ array64 (tmp + 16#64) tmpXs ⋆ cell64 tmp mpzHeaderWord ⋆
      cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R) m)
    (hk : ∀ s st' m',
      s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      let dec := natToDecimalBytes val
      let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
      StrCanon sObj → (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ R) m' → Q (s, ()) m') :
    wp rtR2bEnv Q X (afterDecExpr rt tmp cnBv) m := by
  unfold afterDecExpr
  c0_let_simp
  have h20mul : (20 * cnBv).toNat = 20 * cnBv.toNat := by
    rw [BitVec.toNat_mul, show (20 : BitVec 64).toNat = 20 from rfl,
      Nat.mod_eq_of_lt (by unfold mpzMaxLimbsNat at hcnLeMax; omega)]
  have hsaLe : sarrayAllocBytes (20 * cnBv).toNat ≤ st.rem := by rw [h20mul]; omega
  apply wp_call_of_spec; apply rtR2bEnv_r2_alloc_sarray
  dsimp only [r2AllocSarraySpec, vals, Arg.val_var, Arg.val_imm]
  have hsaOk : (0 : BitVec 64).toNat ≤ (20 * cnBv).toNat ∧ (20 * cnBv).toNat ≤ baMaxCap :=
    ⟨by simp, by rw [h20mul]; unfold baMaxCap mpzMaxLimbsNat at *; omega⟩
  split
  case isFalse hc => exact absurd hsaOk hc
  rw [show baAllocBytes = sarrayAllocBytes from rfl]
  refine ⟨st, array64 (tmp + 16#64) tmpXs ⋆
      cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R,
    Or.inr hsaLe, sep_cast hm (by simp only [Std.ExtHashMap.sep_assoc]),
    fun buf st3 m4 hbuf0 hbuf8 hpr3 hrem3 hrem3Lo hm4 => ?_⟩
  have h20ge : 20 * cnBv.toNat ≤ sarrayAllocBytes (20 * cnBv).toNat - 24 := by
    rw [h20mul]; unfold sarrayAllocBytes align8; omega
  have hsaFit : sarrayAllocBytes (20 * cnBv).toNat - 24 ≤ 2 ^ 64 := by
    rw [h20mul]; unfold sarrayAllocBytes align8 mpzMaxLimbsNat at *; omega
  rw [h20mul] at h20ge hsaFit hm4
  have h4raw : (region (buf + 24#64) (sarrayAllocBytes (20 * cnBv.toNat) - 24) ⋆
      (rtC0Inv rt st3 ⋆ cell64 buf baHeaderWord ⋆ cell64 (buf + 8#64) 0#64 ⋆
        cell64 (buf + 16#64) (20 * cnBv) ⋆
        array64 (tmp + 16#64) tmpXs ⋆ cell64 tmp mpzHeaderWord ⋆
        cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m4 := by
    refine sep_cast hm4 ?_
    simp only [Std.ExtHashMap.sep_assoc]
    repeat rw [msep_left_comm _ (region (buf + 24#64) _)]
    try rfl
  have hbufPop := region_pop_bytes (a := buf + 24#64) (k := 20 * cnBv.toNat)
    h20ge hsaFit h4raw
  rcases hbufPop with ⟨bufBs0, hbufBs0L, hmBuf4⟩
  have hmOuter : (array64 (tmp + 16#64) tmpXs ⋆ bytes (buf + 24#64) bufBs0 ⋆
      (rtC0Inv rt st3 ⋆ cell64 buf baHeaderWord ⋆ cell64 (buf + 8#64) 0#64 ⋆
        cell64 (buf + 16#64) (20 * cnBv) ⋆
        region (buf + 24#64 + BitVec.ofNat 64 (20 * cnBv.toNat))
          (sarrayAllocBytes (20 * cnBv.toNat) - 24 - 20 * cnBv.toNat) ⋆
        cell64 tmp mpzHeaderWord ⋆
        cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m4 := by
    refine sep_cast hmBuf4 ?_
    simp only [Std.ExtHashMap.sep_assoc]
    iterate 4 rw [msep_left_comm (region (buf + 24#64 + _) _)]
    repeat rw [msep_left_comm _ (array64 (tmp + 16#64) _)]
  rw [show (20 : BitVec 64) * cnBv = 20#64 * cnBv from rfl]
  refine nat_to_str_outer_div_wp hcnPos hcnLeMax (by omega) hbufBs0L hlast hmOuter
    fun dlenBv tmpXsF bufBsF m5 hdlenEq hdlenPos hdlenMax htmpFL hbufFL hbufTake hm5 => ?_
  rw [hval] at hdlenEq hbufTake
  c0_let_simp
  have hmStoreLen : (cell64 (buf + 8#64) 0#64 ⋆
      (rtC0Inv rt st3 ⋆ cell64 buf baHeaderWord ⋆ cell64 (buf + 16#64) (20#64 * cnBv) ⋆
        region (buf + 24#64 + BitVec.ofNat 64 (20 * cnBv.toNat))
          (sarrayAllocBytes (20 * cnBv.toNat) - 24 - 20 * cnBv.toNat) ⋆
        array64 (tmp + 16#64) tmpXsF ⋆ bytes (buf + 24#64) bufBsF ⋆
        cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m5 := by
    refine sep_cast hm5 ?_
    simp only [Std.ExtHashMap.sep_assoc]
    iterate 5 rw [msep_left_comm (bytes (buf + 24#64) _)]
    iterate 5 rw [msep_left_comm (array64 (tmp + 16#64) _)]
    repeat rw [msep_left_comm _ (cell64 (buf + 8#64) _)]
    rfl
  have hstLen := store_cell64 dlenBv hmStoreLen
  rw [show (8 : BitVec 64) = 8#64 from rfl, wp_store]; dsimp only [Arg.val_var]
  refine ⟨hstLen.1, ?_⟩; c0_let_simp
  apply wp_call_of_spec; apply rtR2bEnv_r2b_str_alloc_cap
  dsimp only [r2bStrAllocCapSpec, vals, Arg.val_var]
  have hadd1D : (dlenBv + 1#64).toNat = dlenBv.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by unfold mpzMaxLimbsNat at hcnLeMax; omega)]
  have hsBounds : dlenBv.toNat < strMaxCap ∧ dlenBv.toNat < (dlenBv + 1#64).toNat ∧
      (dlenBv + 1#64).toNat ≤ strMaxCap := by
    rw [hadd1D]; unfold strMaxCap mpzMaxLimbsNat at *; omega
  rw [show (1 : BitVec 64) = 1#64 from rfl, ite_eq_left hsBounds, hadd1D]
  have hsRem : strAllocBytes (dlenBv.toNat + 1) ≤ st3.rem := by
    rw [h20mul] at hrem3Lo
    have hmo := strAllocBytes_mono4 (show dlenBv.toNat + 1 ≤ 20 * cnBv.toNat + 1 by omega); omega
  refine ⟨st3, cell64 (buf + 8#64) dlenBv ⋆ cell64 buf baHeaderWord ⋆
      cell64 (buf + 16#64) (20#64 * cnBv) ⋆
      region (buf + 24#64 + BitVec.ofNat 64 (20 * cnBv.toNat))
        (sarrayAllocBytes (20 * cnBv.toNat) - 24 - 20 * cnBv.toNat) ⋆
      array64 (tmp + 16#64) tmpXsF ⋆ bytes (buf + 24#64) bufBsF ⋆
      cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R,
    Or.inr hsRem, sep_cast hstLen.2 (by simp only [Std.ExtHashMap.sep_assoc]; rw [msep_left_comm]),
    fun s st4 m6 hs0 hs8 hpr4 hrem4 _ hm6 => ?_⟩
  have hm6' : (region (s + 32#64) dlenBv.toNat ⋆
      (rtC0Inv rt st4 ⋆ cell64 s strHeaderWord ⋆ cell64 (s + 8#64) (dlenBv + 1#64) ⋆
        cell64 (s + 16#64) (dlenBv + 1#64) ⋆ cell64 (s + 24#64) dlenBv ⋆
        bytes (s + 32#64 + dlenBv) [0] ⋆
        region (s + 32#64 + dlenBv + 1#64)
          (strAllocBytes (dlenBv.toNat + 1) - (32 + dlenBv.toNat + 1)) ⋆
        cell64 (buf + 8#64) dlenBv ⋆ cell64 buf baHeaderWord ⋆
        cell64 (buf + 16#64) (20#64 * cnBv) ⋆
        region (buf + 24#64 + BitVec.ofNat 64 (20 * cnBv.toNat))
          (sarrayAllocBytes (20 * cnBv.toNat) - 24 - 20 * cnBv.toNat) ⋆
        array64 (tmp + 16#64) tmpXsF ⋆ bytes (buf + 24#64) bufBsF ⋆
        cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m6 := by
    refine sep_cast hm6 ?_
    simp only [Std.ExtHashMap.sep_assoc]
    repeat rw [msep_left_comm _ (region (s + 32#64) _)]
  rcases region_pop_bytes (a := s + 32#64) (k := dlenBv.toNat) (Nat.le_refl _)
      (by unfold strMaxCap mpzMaxLimbsNat at *; omega) hm6' with ⟨sBs0, hsBs0L, hmS6⟩
  rw [Nat.sub_self, region_zero, Std.ExtHashMap.sep_emp] at hmS6
  have hvalPos : 0 < val := by
    rw [← hval]
    exact mpzLimbsVal_pos_of_last_ne hcnPos (by simp [htmpL])
      (by simpa [List.getElem_take] using hlast)
  have hmRev : (bytes (buf + 24#64) bufBsF ⋆ bytes (s + 32#64) sBs0 ⋆
      (rtC0Inv rt st4 ⋆ cell64 s strHeaderWord ⋆ cell64 (s + 8#64) (dlenBv + 1#64) ⋆
        cell64 (s + 16#64) (dlenBv + 1#64) ⋆ cell64 (s + 24#64) dlenBv ⋆
        bytes (s + 32#64 + dlenBv) [0] ⋆
        region (s + 32#64 + dlenBv + 1#64)
          (strAllocBytes (dlenBv.toNat + 1) - (32 + dlenBv.toNat + 1)) ⋆
        cell64 (buf + 8#64) dlenBv ⋆ cell64 buf baHeaderWord ⋆
        cell64 (buf + 16#64) (20#64 * cnBv) ⋆
        region (buf + 24#64 + BitVec.ofNat 64 (20 * cnBv.toNat))
          (sarrayAllocBytes (20 * cnBv.toNat) - 24 - 20 * cnBv.toNat) ⋆
        array64 (tmp + 16#64) tmpXsF ⋆ cell64 tmp mpzHeaderWord ⋆
        cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m6 := by
    refine sep_cast hmS6 ?_
    simp only [Std.ExtHashMap.sep_assoc]
    repeat rw [msep_left_comm _ (bytes (buf + 24#64) _)]
    try rfl
  refine nat_to_str_rev_free_wp hs0 hs8 hbuf0 hbuf8 htmp0 htmp8 hcnLeMax hdlenPos hdlenMax
    hadd1D hvalPos hbufTake hsBs0L htmpFL hbufFL hmRev fun st' m' hpr' hrem' hcan' hm' =>
      hk s st' m' hs0 hs8 (hpr3.trans (hpr4.trans hpr')) (by omega) hcan' hm'

private theorem after_trim_copy_reassoc
    (aTmp aN rt cT cT8 cN cN8 tD1 tD2 R : Mem 64 → Prop) :
    (aTmp ⋆ aN ⋆ (rt ⋆ cT ⋆ cT8 ⋆ cN ⋆ cN8 ⋆ tD1 ⋆ tD2 ⋆ R)) =
    (rt ⋆ ((cN ⋆ cN8 ⋆ aN) ⋆ (tD1 ⋆ tD2)) ⋆ (aTmp ⋆ cT ⋆ cT8 ⋆ R)) := by
  simp only [Std.ExtHashMap.sep_assoc]
  rw [msep_left_comm aN rt, msep_left_comm aN cT, msep_left_comm aN cT8,
    msep_left_comm aN cN, msep_left_comm aN cN8]
  rw [msep_left_comm cT8 cN, msep_left_comm cT8 cN8, msep_left_comm cT8 aN,
    msep_left_comm cT8 tD1, msep_left_comm cT8 tD2]
  rw [msep_left_comm cT cN, msep_left_comm cT cN8, msep_left_comm cT aN,
    msep_left_comm cT tD1, msep_left_comm cT tD2]
  rw [msep_left_comm aTmp rt, msep_left_comm aTmp cN, msep_left_comm aTmp cN8,
    msep_left_comm aTmp aN, msep_left_comm aTmp tD1, msep_left_comm aTmp tD2]

private theorem nat_to_str_after_trim_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt n cnBv : Val i64} {nObj : LcnfObj} {objs : List LcnfObj} {st : RtC0State} {m : Mem 64}
    (hnMem : nObj ∈ objs) (hnAddr : nObj.addr = n) (hcanon : MpzCanon nObj)
    (hwf : ∀ o ∈ objs, o.Wf)
    (hcnEq : cnBv.toNat = trimZeroLimbsLen nObj.limbs nObj.arrSize)
    (hcnLeArr : cnBv.toNat ≤ nObj.arrSize)
    (hrc1 : nObj.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound n objs)
    (hm : (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m)
    (hpost :
      let val := mpzLimbsVal (nObj.limbs.take nObj.arrSize)
      let dec := natToDecimalBytes val
      let cn := trimZeroLimbsLen nObj.limbs nObj.arrSize
      if cn = 0 then
        let bytes := strAllocBytes 2
        (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
        ∀ s st' objs' m',
          s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
          let sObj := mkStrObj s 1#32 2 [UInt8.ofNat 48] 1
          StrCanon sObj → DecObjRel n objs objs' →
          (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (s, ()) m'
      else if mpzMaxLimbsNat < cn then
        X "lcnf_panic" [i64, i64] (rt, panicCapCode, ()) m
      else
        let needRem := mpzAllocBytes cn + sarrayAllocBytes (20 * cn) + strAllocBytes (20 * cn + 1)
        needRem ≤ st.rem ∧
        ∀ s st' objs' m',
          s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
          let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
          StrCanon sObj → DecObjRel n objs objs' →
          (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (s, ()) m') :
    wp rtR2bEnv Q X (afterTrimExpr rt n cnBv) m := by
  unfold afterTrimExpr
  have hn0 : n ≠ 0#64 := hnAddr ▸ (hwf nObj hnMem).1
  have hnBit : (n &&& 1#64) = 0#64 := bv64_and1_zero_of_mod8 (hnAddr ▸ (hwf nObj hnMem).2.1)
  have hnoNull : ¬ (n = 0#64 ∨ (n &&& 1#64) ≠ 0#64) := by
    intro h; rcases h with h | h <;> contradiction
  rw [wp_let]
  dsimp only [Op.wp, OpCode.wp, vals, Arg.val_var, Arg.val_imm, liftCmp,
    CmpOp.evalBits, CmpOp.evalBool]
  rw [wp_jnz]; dsimp only [Arg.val_var]
  refine ⟨fun heq0 => ?_, fun hne0 => ?_⟩
  · have hcn0 : cnBv.toNat = 0 := by
      have hc : cnBv = 0#64 := by simpa using heq0
      rw [hc]; rfl
    have hcnTr0 : trimZeroLimbsLen nObj.limbs nObj.arrSize = 0 := by omega
    rw [ite_eq_left hcnTr0] at hpost
    rcases hpost with ⟨hfree, hkpost⟩
    apply wp_call_of_spec
    apply rtR2bEnv_r2b_str_alloc_cap
    dsimp only [r2bStrAllocCapSpec, vals, Arg.val_var, Arg.val_imm]
    have hbounds : (1 : BitVec 64).toNat < strMaxCap ∧
        (1 : BitVec 64).toNat < (2 : BitVec 64).toNat ∧ (2 : BitVec 64).toNat ≤ strMaxCap := by
      simp only [strMaxCap]; decide
    rw [ite_eq_left hbounds, show ((2 : BitVec 64).toNat) = 2 from rfl]
    refine ⟨st, lcnfHeap objs ⋆ R, hfree, sep_cast hm (Std.ExtHashMap.sep_assoc _ _ _),
      fun s st1 m1 hs0 hs8 hpr1 hrem1 _ hm1 => ?_⟩
    rw [show (1 : BitVec 64).toNat = 1 from rfl, show (1 : BitVec 64) = 1#64 from rfl] at hm1
    refine nat_to_str_zero_store_wp hm1 fun m2 hstrMem => ?_
    have hstrMem' : (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆
        (lcnfObjMem (mkStrObj s 1#32 2 [UInt8.ofNat 48] 1) ⋆ R)) m2 :=
      sep_cast hstrMem (by
        simp only [Std.ExtHashMap.sep_assoc]; rw [msep_left_comm (lcnfObjMem _)])
    have hcanon : StrCanon (mkStrObj s 1#32 2 [UInt8.ofNat 48] 1) :=
      mkStrObj_canon hs0 hs8 (by decide) (by decide) (by decide) (by decide)
    apply wp_call_of_spec
    apply rtR2bEnv_r2_dec_obj
    dsimp only [r2DecObjSpec, vals, Arg.val_var]
    rw [ite_eq_right hnoNull]
    refine ⟨st1, objs, lcnfObjMem (mkStrObj s 1#32 2 [UInt8.ofNat 48] 1) ⋆ R,
      ⟨nObj, hnMem, hnAddr, fun h1 => by
        have := hrc1 h1
        exact ⟨by unfold RtC0State.workCap; rw [← hpr1.2.2.2.2.2.1]; exact this.1, this.2⟩⟩,
      hwf, hstrMem', fun st2 objs' m3 hpr2 hrem2 hdec hm3 => ?_⟩
    rw [wp_ret]; dsimp only [vals, Arg.val_var]
    exact hkpost s st2 objs' m3 hs0 hs8 (hpr1.trans hpr2) (by omega) hcanon hdec
      (sep_cast hm3 (by
        simp only [Std.ExtHashMap.sep_assoc]; rw [msep_left_comm (lcnfHeap objs')]))
  · have hcnNe : cnBv ≠ 0#64 := by simpa using hne0
    have hcnPos : 1 ≤ cnBv.toNat :=
      Nat.pos_of_ne_zero fun h0 => hcnNe (BitVec.eq_of_toNat_eq h0)
    have hcnTrNe : trimZeroLimbsLen nObj.limbs nObj.arrSize ≠ 0 := by omega
    rw [ite_eq_right hcnTrNe] at hpost
    rw [wp_let]
    dsimp only [Op.wp, OpCode.wp, vals, Arg.val_var, Arg.val_imm, liftCmp,
      CmpOp.evalBits, CmpOp.evalBool]
    rw [wp_jnz]; dsimp only [Arg.val_var]
    refine ⟨fun hbig => ?_, fun hok => ?_⟩
    · rw [BitVec.ult, decide_eq_true_eq] at hbig
      have hmax : mpzMaxLimbsNat < trimZeroLimbsLen nObj.limbs nObj.arrSize := by
        unfold mpzMaxLimbsNat; have h1 : (13421770 : BitVec 64).toNat = 13421770 := rfl; omega
      rw [ite_eq_left hmax] at hpost
      rw [wp_exit]; dsimp only [vals, Arg.val_var, Arg.val_imm]
      exact hpost
    · rw [BitVec.ult, decide_eq_false_iff_not] at hok
      have hnotBig : ¬ mpzMaxLimbsNat < trimZeroLimbsLen nObj.limbs nObj.arrSize := by
        unfold mpzMaxLimbsNat; have h1 : (13421770 : BitVec 64).toNat = 13421770 := rfl; omega
      rw [ite_eq_right hnotBig] at hpost
      rcases hpost with ⟨hneed, hkpost⟩
      have hcnLeMax : cnBv.toNat ≤ mpzMaxLimbsNat := by omega
      have hmpzLe : mpzAllocBytes cnBv.toNat ≤ st.rem := by rw [← hcnEq] at hneed; omega
      apply wp_call_of_spec
      apply rtR2bEnv_r2b_alloc_mpz
      dsimp only [r2bAllocMpzSpec, vals, Arg.val_var]
      have hmpzCond : cnBv.toNat ≤ cnBv.toNat ∧ cnBv.toNat ≤ 33554429 :=
        ⟨Nat.le_refl _, by unfold mpzMaxLimbsNat at hcnLeMax; omega⟩
      rw [ite_eq_left hmpzCond]
      refine ⟨st, lcnfHeap objs ⋆ R, Or.inr hmpzLe,
        sep_cast hm (Std.ExtHashMap.sep_assoc _ _ _),
        fun tmp st1 m1 htmp0 htmp8 hpr1 hrem1 hrem1Lo hm1 => ?_⟩
      have hm1' : (region (tmp + 16#64) (8 * cnBv.toNat) ⋆
          ((rtC0Inv rt st1 ⋆ cell64 tmp mpzHeaderWord ⋆
            cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32))) ⋆ (lcnfHeap objs ⋆ R))) m1 :=
        sep_cast hm1 (by
          rw [Std.ExtHashMap.sep_comm _ (region (tmp + 16#64) _), Std.ExtHashMap.sep_assoc])
      have htmpArr0 := region_to_array64_sep (a := tmp + 16#64) (n := cnBv.toNat)
        (by unfold mpzMaxLimbsNat at hcnLeMax; omega) hm1'
      rcases htmpArr0 with ⟨tmpXs0, htmpXs0Len, hmTmpArr⟩
      obtain ⟨iObj, hiObj, _hAtN, hfocusN⟩ := lcnfHeap_focus_obj hnMem
      have hmpzTag := hcanon.2.2.2.2.2.1
      have hmemAll : (array64 (tmp + 16#64) tmpXs0 ⋆ array64 (n + 16#64) nObj.limbs ⋆
          (rtC0Inv rt st1 ⋆ cell64 tmp mpzHeaderWord ⋆
            cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆
            cell64 n nObj.header ⋆ cell64 (n + 8#64) nObj.mpzMeta ⋆
            lcnfHeap (objs.take iObj) ⋆ lcnfHeap (objs.drop (iObj + 1)) ⋆ R)) m1 := by
        have hm' := hmTmpArr
        rw [hfocusN, r2b_lcnfObjMem_mpz_eq hmpzTag, hnAddr] at hm'
        refine sep_cast hm' ?_
        simp only [Std.ExtHashMap.sep_assoc]
        repeat rw [msep_left_comm _ (array64 (n + 16#64) _)]
      have hcnLeLimbs : cnBv.toNat ≤ nObj.limbs.length := by
        have := hcanon.2.2.2.2.2.2.1; have := hcanon.2.2.2.2.2.2.2.1; omega
      refine nat_to_str_copy_loop_wp hcnLeLimbs htmpXs0Len
        (by unfold mpzMaxLimbsNat at hcnLeMax; omega) hmemAll
        fun tmpXs m2 htmpL htmpTake hm2 => ?_
      have hmHeap2 : (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆
          (array64 (tmp + 16#64) tmpXs ⋆ cell64 tmp mpzHeaderWord ⋆
            cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m2 := by
        have hm' : (rtC0Inv rt st1 ⋆
            ((cell64 n nObj.header ⋆ cell64 (n + 8#64) nObj.mpzMeta ⋆
              array64 (n + 16#64) nObj.limbs) ⋆
              (lcnfHeap (objs.take iObj) ⋆ lcnfHeap (objs.drop (iObj + 1)))) ⋆
            (array64 (tmp + 16#64) tmpXs ⋆ cell64 tmp mpzHeaderWord ⋆
              cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R)) m2 := by
          exact sep_cast hm2 (after_trim_copy_reassoc _ _ _ _ _ _ _ _ _ _)
        rw [← hnAddr, ← r2b_lcnfObjMem_mpz_eq hmpzTag, ← hfocusN] at hm'
        exact hm'
      apply wp_call_of_spec
      apply rtR2bEnv_r2_dec_obj
      dsimp only [r2DecObjSpec, vals, Arg.val_var]
      rw [ite_eq_right hnoNull]
      refine ⟨st1, objs, array64 (tmp + 16#64) tmpXs ⋆ cell64 tmp mpzHeaderWord ⋆
          cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ R,
        ⟨nObj, hnMem, hnAddr, fun h1 => by
          have := hrc1 h1
          exact ⟨by unfold RtC0State.workCap; rw [← hpr1.2.2.2.2.2.1]; exact this.1, this.2⟩⟩,
        hwf, hmHeap2, fun st2 objs' m3 hpr2 hrem2 hdec hm3 => ?_⟩
      have htrimLast := trimZeroLimbsLen_last_ne nObj.limbs nObj.arrSize
        (by have := hcanon.2.2.2.2.2.2.1; have := hcanon.2.2.2.2.2.2.2.1; omega)
        (by rw [← hcnEq]; exact hcnPos) hcnEq
      have htmpLast : tmpXs[cnBv.toNat - 1]'(by omega) ≠ 0#64 := by
        simp only [htmpTake, List.getElem_take]; exact htrimLast.2.2.2
      have hvalEq : mpzLimbsVal (tmpXs.take cnBv.toNat) =
          mpzLimbsVal (nObj.limbs.take nObj.arrSize) := by
        rw [htmpTake, List.take_of_length_le (List.length_take_le _ _),
          hcnEq, trimZeroLimbsLen_val]
      have hneed2 :
          sarrayAllocBytes (20 * cnBv.toNat) + strAllocBytes (20 * cnBv.toNat + 1) ≤ st2.rem := by
        rw [hcnEq] at hrem1Lo ⊢; omega
      have hm3' : (rtC0Inv rt st2 ⋆ array64 (tmp + 16#64) tmpXs ⋆ cell64 tmp mpzHeaderWord ⋆
          cell64 (tmp + 8#64) (cnBv ||| (cnBv <<< 32)) ⋆ (lcnfHeap objs' ⋆ R)) m3 := by
        refine sep_cast hm3 ?_
        simp only [Std.ExtHashMap.sep_assoc]; iterate 3 rw [msep_left_comm (lcnfHeap objs')]
      refine nat_to_str_after_dec_wp (R := lcnfHeap objs' ⋆ R) htmp0 htmp8 hcnPos hcnLeMax
        htmpL htmpLast hvalEq hneed2 hm3'
        fun s st' m' hs0 hs8 hpr' hrem' hcan' hm' =>
          hkpost s st' objs' m' hs0 hs8 (hpr1.trans (hpr2.trans hpr')) (by omega) hcan' hdec
            (sep_cast hm' (Std.ExtHashMap.sep_assoc _ _ _).symm)

theorem lcnf_nat_to_str_wp :
    ∀ xs m Q X, lcnfNatToStrSpec xs m Q X → Func.wp rtR2bEnv lcnf_nat_to_str_body xs m Q X := by
  intro ⟨rt, n, ⟨⟩⟩ m Q X ⟨st, val, objs, R, hnat, hwf, hm, hbody⟩
  dsimp only [Func.wp, Ty.hasFloat, List.any, lcnf_nat_to_str_body]
  try rw [if_neg (by decide)]
  repeat rw [wp_let]; dsimp only [Op.wp, OpCode.wp, vals, Arg.val_var, Arg.val_imm, lift2]
  rw [wp_jnz]; dsimp only [Arg.val_var]
  refine ⟨fun hsc => ?_, fun hptr => ?_⟩
  · have hbit : (n &&& 1#64) ≠ 0#64 := by
      simpa [liftCmp, CmpOp.evalBits, CmpOp.evalBool, bne_iff_ne] using hsc
    unfold NatInHeap at hnat
    rw [ite_eq_left hbit] at hnat
    rw [ite_eq_left hbit] at hbody
    subst hnat
    have hlt : (n >>> 1).toNat < 2 ^ 63 := by
      have hn64 := n.isLt
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    exact nat_to_str_boxed_wp (R := lcnfHeap objs ⋆ R) hlt hbody.1
      (sep_cast hm (Std.ExtHashMap.sep_assoc _ _ _)) fun s st' m' hs0 hs8 hpr hrem hcan hm' =>
        hbody.2 s st' m' hs0 hs8 hpr hrem hcan (sep_cast hm' (Std.ExtHashMap.sep_assoc _ _ _).symm)
  · have hzero : (n &&& 1#64) = 0#64 := by
      simpa [liftCmp, CmpOp.evalBits, CmpOp.evalBool, bne_iff_ne] using hptr
    have hnotBit : ¬ (n &&& 1#64) ≠ 0#64 := fun h => h hzero
    rw [ite_eq_right hnotBit] at hbody
    rcases hbody with ⟨nObj, hnMem, hnAddr, hcanon, hrc1, hbody⟩
    unfold NatInHeap at hnat
    rw [ite_eq_right hnotBit] at hnat
    rcases hnat with ⟨nObj', hnMem', hnAddr', _, hvalEq⟩
    have hmHeap : (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ R)) m :=
      sep_cast hm (by rw [Std.ExtHashMap.sep_assoc, msep_left_comm (rtC0Inv rt st)])
    have hsame := lcnfHeap_addr_uniq hmHeap hnMem hnAddr hnMem' hnAddr'
    subst hsame
    rw [hvalEq] at hbody
    obtain ⟨iObj, hiObj, _hAtN, hfocusN⟩ := lcnfHeap_focus_obj hnMem
    have hmpzTag := hcanon.2.2.2.2.2.1
    have hmemLoad : (cell64 (n + 8#64) nObj.mpzMeta ⋆
        (cell64 n nObj.header ⋆ array64 (n + 16#64) nObj.limbs ⋆
          lcnfHeap (objs.take iObj) ⋆ lcnfHeap (objs.drop (iObj + 1)) ⋆ rtC0Inv rt st ⋆ R)) m := by
      have hm' : (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ R)) m :=
        sep_cast hm (by rw [← Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm (rtC0Inv _ _),
          Std.ExtHashMap.sep_assoc])
      rw [hfocusN, r2b_lcnfObjMem_mpz_eq hmpzTag, hnAddr] at hm'
      refine sep_cast hm' ?_
      simp only [Std.ExtHashMap.sep_assoc]
      rw [msep_left_comm]
    c0_let_simp
    have hldMeta := loadVal_cell64 (a := n + 8#64) hmemLoad
    rw [show (8 : BitVec 64) = 8#64 from rfl]
    apply wp_load_of (v := nObj.mpzMeta) (by simpa [Arg.val_var] using hldMeta)
    repeat rw [wp_let]; dsimp only [Op.wp, OpCode.wp, vals, Arg.val_var, Arg.val_imm, lift2]
    refine ⟨by decide, ?_⟩
    have h32s : (BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64 = 32 := by decide
    rw [h32s, lcnfObjMem_mpz_meta_shift hcanon]
    have hszVal : (BitVec.ofNat 64 nObj.arrSize).toNat = nObj.arrSize := by
      have hleCap := hcanon.2.2.2.2.2.2.2.1
      have hcapMax := hcanon.2.2.2.2.2.2.2.2
      exact bv64_toNat_ofNat_lt4 (by omega)
    have hmArr : (array64 (n + 16#64) nObj.limbs ⋆
        (cell64 n nObj.header ⋆ cell64 (n + 8#64) nObj.mpzMeta ⋆
          lcnfHeap (objs.take iObj) ⋆ lcnfHeap (objs.drop (iObj + 1)) ⋆ rtC0Inv rt st ⋆ R)) m := by
      refine sep_cast hmemLoad ?_
      simp only [Std.ExtHashMap.sep_assoc]
      repeat rw [msep_left_comm _ (array64 (n + 16#64) _)]
      rw [msep_left_comm (cell64 (n + 8#64) _) (cell64 n _)]
    have hlimbsLen : nObj.limbs.length < 2 ^ 64 := by
      rw [hcanon.2.2.2.2.2.2.1]; have := hcanon.2.2.2.2.2.2.2.2; omega
    have hszLe : (BitVec.ofNat 64 nObj.arrSize).toNat ≤ nObj.limbs.length := by
      rw [hszVal, hcanon.2.2.2.2.2.2.1]; exact hcanon.2.2.2.2.2.2.2.1
    refine nat_to_str_trim_limbs_wp (Q := Q) (X := X) (k := fun cnBv => afterTrimExpr rt n cnBv)
      hszLe hlimbsLen hmArr fun cnBv hcnEq hcnLe => ?_
    rw [hszVal] at hcnEq hcnLe
    exact nat_to_str_after_trim_wp hnMem hnAddr hcanon hwf hcnEq hcnLe hrc1 hm hbody

end

end LeanQbe.T.LeanLCNF
