module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof3
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof4
import all Kraken.Mem
import all Kraken.Separation

/-!
# Top-Level `Nat` Bitwise & Slow Dispatchers (`lcnf_nat_bits_wp`, `lcnf_nat_slow_wp`, Part 5)
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

private theorem lcnf_nat_bits_tonat_wp
    (rt a b : BitVec 64) (aVal : Nat) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hwf : BigNumRtWf rt st scr scrLimbs) (ha : natRep a aVal objs)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natBitsPost 13 aVal b res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.group (sig := [[i64]])
        (fun _Js =>
          Blocks.cons
            (fun p_2 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                  args := (Arg.var b, Arg.imm 0, ()) } fun p_3 =>
                Expr.jnz (Arg.var p_3.fst) (Expr.ret (Arg.imm 0, ()))
                  (Expr.let_
                    { sig := [i64, i64],
                      code := OpCode.cmp CmpOp.uge i64 Ty.bool,
                      args := (Arg.var b, Arg.imm 64, ()) } fun p_4 =>
                    Expr.jnz (Arg.var p_4.fst) (Expr.ret (Arg.var p_2.fst, ()))
                      (Expr.let_
                        { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.imm 1, Arg.var b,
                          ()) }
                        fun p =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var p.fst,
                            Arg.imm 1, ()) }
                          fun p =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var p_2.fst,
                              Arg.var p.fst, ()) }
                            fun p => Expr.ret (Arg.var p.fst, ()))))
            Blocks.nil)
        fun Js =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var a, Arg.imm 1,
            ()) } fun p_2 =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool,
              args := (Arg.var p_2.fst, Arg.imm 0, ()) } fun p_3 =>
            Expr.jnz (Arg.var p_3.fst)
              (Expr.let_
                { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_4 =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var a, Arg.var p_4.fst,
                    ()) }
                  fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
              (Expr.let_
                { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var a, Arg.imm 8,
                  ()) } fun p_4 =>
                Expr.load i64 (Arg.var p_4.fst) fun ld =>
                  Expr.let_
                    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) } fun p_5 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var ld,
                        Arg.var p_5.fst, ()) }
                      fun p_6 =>
                      Expr.group (sig := [[i64]])
                        (fun _Js_1 => Blocks.cons (fun p =>
                          Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
                        fun Js_1 =>
                        Expr.let_
                          { sig := [i64, i64],
                            code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                            args := (Arg.var p_6.fst, Arg.imm 0, ()) } fun p_7 =>
                          Expr.jnz (Arg.var p_7.fst)
                            (Expr.let_
                              { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.imm 2,
                                Arg.imm 8, ()) }
                              fun p_8 =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var a,
                                  Arg.var p_8.fst, ()) }
                                fun p => Expr.load i64 (Arg.var p.fst) fun ld =>
                                  Expr.jump Js_1.fst (Arg.var ld, ()))
                            (Expr.jump Js_1.fst (Arg.imm 0, ())))) m := by
  apply wp_join_group (fun (xs : Tup Val [i64]) (m' : Mem 64) => xs.fst = BitVec.ofNat 64 aVal ∧
    m' = m)
  · intro _ xs m' ⟨hxs, hm'⟩
    rw [hm']
    simp only [Blocks.get]
    c0_let_simp
    by_cases hb0 : b = 0#64
    · subst hb0
      apply wp_jnz_true (by decide)
      c0_step
      refine hQ 0#64 st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
      simp [natBitsPost]
    · have hb_pos : 0 < b.toNat := Nat.pos_of_ne_zero fun hz => hb0 (BitVec.eq_of_toNat_eq
      (by simpa using hz))
      apply wp_jnz_false (beq_false_of_ne hb0)
      c0_let_simp
      by_cases hb64 : 64 ≤ b.toNat
      · apply wp_jnz_true
          (by rw [BitVec.ule]; exact decide_eq_true (by change 64 ≤ b.toNat; exact hb64))
        c0_step
        rw [hxs]
        refine hQ _ st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
        simp only [natBitsPost, ↓reduceIte, show b.toNat ≠ 0 by omega, hb64]
        exact ⟨trivial, trivial⟩
      · have hb_lt64 : b.toNat < 64 := by omega
        apply wp_jnz_false
          (by rw [BitVec.ule, decide_eq_false_iff_not]; change ¬ 64 ≤ b.toNat; omega)
        c0_let_simp
        refine hQ _ st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
        simp only [natBitsPost, ↓reduceIte, show b.toNat ≠ 0 by omega, hb64, hxs]
        refine ⟨trivial, ?_⟩
        apply BitVec.eq_of_toNat_eq
        have hb_mod : b.toNat % 64 = b.toNat := Nat.mod_eq_of_lt hb_lt64
        have hshl : ((1 : BitVec 64) <<< (b.toNat % 64)).toNat = 2 ^ b.toNat := by
          rw [hb_mod, BitVec.toNat_shiftLeft, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.one_shiftLeft]
          exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hb_lt64)
        have hpow_pos : 1 ≤ 2 ^ b.toNat := Nat.one_le_pow _ _ (by decide)
        have hsub : (((1 : BitVec 64) <<< (b.toNat % 64)) - (1 : BitVec 64)).toNat =
          2 ^ b.toNat - 1 := by
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
            (by rw [show (1 : BitVec 64).toNat = 1 from rfl, hshl]; exact hpow_pos)),
            hshl, show (1 : BitVec 64).toNat = 1 from rfl]
        rw [BitVec.toNat_and, hsub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.and_two_pow_sub_one_eq_mod]
        have hdvd : 2 ^ b.toNat ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
        rw [Nat.mod_mod_of_dvd _ hdvd]
        exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2)))
          (Nat.pow_lt_pow_right (by decide : 1 < 2) hb_lt64))).symm
  · intro Js hJs
    c0_let_simp
    by_cases ha_sm : aVal < 2 ^ 63
    · have hbit0 : (a &&& 1#64) ≠ 0#64 := by
        intro hz; have := (natRep_and_one_eq_zero_iff ha).mp hz; omega
      apply wp_jnz_true (by simp [hbit0])
      c0_let_simp
      rw [natRep_small_shr1_nat ha ha_sm]
      exact hJs (BitVec.ofNat 64 aVal, ()) m ⟨rfl, rfl⟩
    · have ha_box := ha
      dsimp only [natRep] at ha_box
      simp only [ha_sm, ↓reduceIte] at ha_box
      rcases ha_box with ⟨hbit0, obj, hmem, rfl, hcan⟩
      rcases hcan with ⟨hwfO, htag, _, harr, h1, hmax, _, hval, _⟩
      apply wp_jnz_false (by simp [hbit0])
      c0_let_simp
      have hm' : (lcnfHeap objs ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R)) m := by sep_use hm
      obtain ⟨idx, hlt, heq_idx, hm_foc⟩ := lcnfHeap_mpz_focus hmem htag hm'
      rw [wp_load]
      refine ⟨obj.mpzMeta, loadVal_cell64 (sep_mpz_swap2 hm_foc), ?_⟩
      c0_let_simp
      have hcap32 : obj.cap < 2 ^ 32 := by
        have h := hwfO.2.2.2.2.2.2.2.2.2
        simp [htag, mpzTag, closureTag, arrayTag, sarrayTag, stringTag] at h
        omega
      have harr32 : obj.arrSize < 2 ^ 32 := by rw [harr]; unfold mpzMaxLimbs at hmax; omega
      rw [mpzMeta_arrSize_nat obj hcap32 harr32]
      apply wp_join_group (fun (p : Tup Val [i64]) (m' : Mem 64) => p.fst = BitVec.ofNat 64 aVal ∧
        m' = m)
      · intro _ p m' hp; simp only [Blocks.get]; rw [wp_jump]; exact hJs p m' hp
      · intro Js_1 hJs_1
        have harr_pos : 0 < (BitVec.ofNat 64 obj.arrSize).toNat := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), harr]; omega
        c0_let_simp
        apply wp_jnz_true (by rw [BitVec.ult]; exact decide_eq_true harr_pos)
        c0_let_simp
        have ha0 : obj.addr + 16#64 =
            (obj.addr + 16#64) + BitVec.ofNat 64 (8 * 0) := by
          change obj.addr + 16#64 = (obj.addr + 16#64) + 0#64
          simp [BitVec.add_zero]
        rw [wp_load]
        refine ⟨obj.limbs[0]'(by omega), ?_, ?_⟩
        · rw [ha0]; exact loadVal_array64 (by omega) (sep_mpz_swap3 hm_foc)
        · rw [wp_jump]
          have hl0 : obj.limbs[0]'(by omega) = BitVec.ofNat 64 aVal := by
            have hne : obj.limbs ≠ [] := by intro h; simp [h] at h1
            obtain ⟨d, ds, hL⟩ := List.exists_cons_of_ne_nil hne
            have hval_cons : aVal = d.toNat + 2 ^ 64 * limbsVal ds := by
              rw [← hval, hL, limbsVal_cons]
            have hd0 : obj.limbs[0]'(by omega) = d := by simp [hL]
            rw [hd0]
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, hval_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt d.isLt]
          exact hJs_1 (obj.limbs[0]'(by omega), ()) m ⟨hl0, rfl⟩

private theorem lcnf_nat_bits_ofnat_wp
    (rt a : BitVec 64) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (hok : natBitsOk 14 a.toNat 0#64 objs scrLimbs.length st)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natBitsPost 14 a.toNat 0#64 res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 63, ()) } fun p_3 =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.imm 1, Arg.var p_3.fst,
            ()) } fun p_4 =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool,
              args := (Arg.var a, Arg.var p_4.fst, ()) } fun p_5 =>
            Expr.jnz (Arg.var p_5.fst)
              (Expr.let_
                { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_6 =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.var a, Arg.var p_6.fst,
                    ()) }
                  fun p =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.or i64, args := (Arg.var p.fst, Arg.imm 1,
                      ()) }
                    fun p => Expr.ret (Arg.var p.fst, ()))
              (Expr.call (as := [i64, i64]) (bs := [i64]) "lcnf_nat_alloc" (Arg.var rt, Arg.imm 1,
                ()) fun p_6 =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.imm 2, Arg.imm 8,
                    ()) } fun p_7 =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_6.fst,
                      Arg.var p_7.fst, ()) }
                    fun p_8 => Expr.store (t := i64) (Arg.var a) (Arg.var p_8.fst)
                      (Expr.ret (Arg.var p_6.fst, ())))) m := by
  c0_let_simp
  have hpow63 : ((1 : BitVec 64) <<< 63 : BitVec 64) = BitVec.ofNat 64 (2 ^ 63) := by decide
  rw [hpow63]
  by_cases ha_sm : a.toNat < 2 ^ 63
  · apply wp_jnz_true (by rw [BitVec.ult]; exact decide_eq_true (by simpa using ha_sm))
    c0_step
    refine hQ _ st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
    dsimp only [natBitsPost, natRep]
    simp only [show (14 : Nat) ≠ 13 by decide, ↓reduceIte, ha_sm]
    refine ⟨?_, fun o ho => ho⟩
    conv => lhs; rw [show a = BitVec.ofNat 64 a.toNat from by simp]
    exact bv64_encodeNat ha_sm
  · have hge : 2 ^ 63 ≤ a.toNat := by omega
    have hok' := hok
    dsimp only [natBitsOk] at hok'
    simp only [show (14 : Nat) ≠ 13 by decide, ↓reduceIte] at hok'
    have halloc := hok' hge
    apply wp_jnz_false (by rw [BitVec.ult, decide_eq_false_iff_not]; simp; omega)
    dsimp only [bigNumRtInv] at hm
    apply lcnf_nat_alloc_imm1_call_wp
      (R := cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R)
      hwf.1 halloc (by sep_use hm)
    intro p st' m1 obj0 hobjWf hp0 hmst hrem hb' hm1
    c0_let_simp
    have hm1' : (array64 (p + 16#64) [0#64] ⋆
        (cell64 p obj0.header ⋆ cell64 (p + 8#64) obj0.mpzMeta ⋆
          rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R)) m1 := by
      have hmem1 := lcnfObjMem_mpz_eq (o := obj0) rfl
      rw [hmem1] at hm1
      sep_use hm1
    obtain ⟨hsok, hm2⟩ := c0_store_array64_obj2_imm a hm1' (by decide)
    rw [wp_store]
    refine ⟨hsok, ?_⟩
    c0_step
    let newObj : LcnfObj :=
      { addr := p, rc := 1#32, csSz := 24, other := 0, tag := mpzTag, cap := 1, arrSize := 1,
        limbs := [a] }
    have hnew_mem : (bigNumRtInv rt st' scr scrLimbs ⋆ lcnfHeap (newObj :: objs) ⋆ R)
        (storeMem m1 i64 (p + 16#64) a) := by
      dsimp only [bigNumRtInv]
      rw [lcnfHeap_cons_eq, lcnfObjMem_mpz_eq rfl]
      have hset : ([0#64] : List (BitVec 64)).set 0 a = [a] := rfl
      rw [hset] at hm2
      sep_use hm2
    have hnewWf : newObj.Wf := by
      rcases hobjWf with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      dsimp [obj0] at h8
      exact ⟨h1, h2, h3, h4, h5, h6, h7,
        by simpa [newObj, LcnfObj.totalBytes, LcnfObj.arrSize] using h8⟩
    have ha_nz : a ≠ 0#64 := by
      intro h; rw [h] at hge; simp at hge
    have hnew_canon : mpzNatCanon newObj a.toNat := by
      refine ⟨hnewWf, rfl, rfl, rfl, by simp [newObj], by simp [newObj, mpzMaxLimbs], ?_, ?_, hge⟩
      · simpa [newObj] using ha_nz
      · simp [newObj, limbsVal]
    refine hQ p st' scrLimbs (newObj :: objs) _ hmst hrem
      (BigNumRtWf.with_state_len hwf hb' rfl) ?_ hnew_mem
    dsimp only [natBitsPost]
    simp only [show (14 : Nat) ≠ 13 by decide, ↓reduceIte]
    refine ⟨?_, fun o ho => List.mem_cons_of_mem _ ho⟩
    dsimp only [natRep]
    simp only [show ¬ a.toNat < 2 ^ 63 by omega, ↓reduceIte]
    exact ⟨hp0, newObj, List.mem_cons_self, rfl, hnew_canon⟩

private theorem lcnf_nat_bits_log2_wp
    (rt a : BitVec 64) (aVal : Nat) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hwf : BigNumRtWf rt st scr scrLimbs) (ha : natRep a aVal objs)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natBitsPost 19 aVal 0#64 res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var a, Arg.imm 1, ()) } fun p_4 =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool,
            args := (Arg.var p_4.fst, Arg.imm 0, ()) } fun p_5 =>
          Expr.jnz (Arg.var p_5.fst)
            (Expr.let_
              { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_6 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var a, Arg.var p_6.fst,
                  ()) } fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                    args := (Arg.var p.fst, Arg.imm 0, ()) } fun p_7 =>
                  Expr.jnz (Arg.var p_7.fst) (Expr.ret (Arg.imm 1, ()))
                    (Expr.let_
                      { sig := [i64], code := OpCode.clz 64, args := (Arg.var p.fst, ()) } fun p =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.imm 63,
                          Arg.var p.fst, ()) }
                        fun p =>
                        Expr.let_
                          { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1,
                            ()) } fun p_8 =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.var p.fst,
                              Arg.var p_8.fst, ()) }
                            fun p =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.or i64, args := (Arg.var p.fst,
                                Arg.imm 1, ()) }
                              fun p => Expr.ret (Arg.var p.fst, ())))
            (Expr.let_
              { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var a, Arg.imm 8,
                ()) } fun p_6 =>
              Expr.load i64 (Arg.var p_6.fst) fun ld =>
                Expr.let_
                  { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) } fun p_7 =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var ld,
                      Arg.var p_7.fst, ()) }
                    fun p_8 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var a, Arg.imm 16,
                        ()) }
                      fun p_9 =>
                      Expr.call (as := [i64, i64]) (bs := [i64]) "bn_trim" (Arg.var p_9.fst,
                        Arg.var p_8.fst, ())
                        fun p_10 =>
                        Expr.let_
                          { sig := [i64, i64],
                            code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                            args := (Arg.var p_10.fst, Arg.imm 0, ()) } fun p_11 =>
                          Expr.jnz (Arg.var p_11.fst) (Expr.ret (Arg.imm 1, ()))
                            (Expr.let_
                              { sig := [i64, i64], code := OpCode.add i64, args := (Arg.imm 2,
                                Arg.var p_10.fst, ()) }
                              fun p_12 =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.sub i64,
                                  args := (Arg.var p_12.fst, Arg.imm 1, ()) } fun p_13 =>
                                Expr.let_
                                  { sig := [i64, i64], code := OpCode.mul i64,
                                    args := (Arg.var p_13.fst, Arg.imm 8, ()) } fun p_14 =>
                                  Expr.let_
                                    { sig := [i64, i64], code := OpCode.add i64,
                                      args := (Arg.var a, Arg.var p_14.fst, ()) } fun p =>
                                    Expr.load i64 (Arg.var p.fst) fun ld =>
                                      Expr.let_
                                        { sig := [i64, i64], code := OpCode.mul i64,
                                          args := (Arg.var p_10.fst, Arg.imm 64, ()) } fun p =>
                                        Expr.let_
                                          { sig := [i64, i64], code := OpCode.sub i64,
                                            args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
                                          Expr.let_
                                            { sig := [i64], code := OpCode.clz 64,
                                              args := (Arg.var ld, ()) }
                                            fun p_15 =>
                                            Expr.let_
                                              { sig := [i64, i64], code := OpCode.sub i64,
                                                args := (Arg.var p.fst, Arg.var p_15.fst,
                                                  ()) } fun p =>
                                              Expr.let_
                                                { sig := [i32], code := OpCode.sext 32 64,
                                                  args := (Arg.imm 1, ()) }
                                                fun p_16 =>
                                                Expr.let_
                                                  { sig := [i64, i64], code := OpCode.shl i64,
                                                    args := (Arg.var p.fst, Arg.var p_16.fst,
                                                      ()) } fun p =>
                                                  Expr.let_
                                                    { sig := [i64, i64], code := OpCode.or i64,
                                                      args := (Arg.var p.fst, Arg.imm 1,
                                                        ()) } fun p =>
                                                    Expr.ret (Arg.var p.fst, ())))) m := by
  c0_let_simp
  by_cases ha_sm : aVal < 2 ^ 63
  · have hbit0 : (a &&& 1#64) ≠ 0#64 := by
      intro hz; have := (natRep_and_one_eq_zero_iff ha).mp hz; omega
    apply wp_jnz_true (by simp [hbit0])
    c0_let_simp
    rw [natRep_small_shr1_nat ha ha_sm]
    by_cases ha0 : aVal = 0
    · subst ha0
      apply wp_jnz_true (by decide)
      c0_step
      refine hQ 1#64 st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
      simp [natBitsPost, natRep]
    · have hne0 : (BitVec.ofNat 64 aVal == 0#64) = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        have := BitVec.toNat_eq.mp (beq_iff_eq.mp ht)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
          (by omega), show (0#64 : BitVec 64).toNat = 0 from rfl] at this
        omega
      apply wp_jnz_false hne0
      c0_let_simp
      have hx_nz : BitVec.ofNat 64 aVal ≠ 0#64 := by
        intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
          (by omega), show (0#64 : BitVec 64).toNat = 0 from rfl] at this
        omega
      have hclz : (BitVec.ofNat 64 aVal).clz.toNat < 64 := BitVec.clz_lt_iff_ne_zero.mpr hx_nz
      have hlog : aVal.log2 = 63 - (BitVec.ofNat 64 aVal).clz.toNat := by
        have h1 := limbsVal_log2 (xs := [BitVec.ofNat 64 aVal]) (List.cons_ne_nil _ _) hx_nz
        simpa [limbsVal, Nat.mod_eq_of_lt (by omega : aVal < 2 ^ 64)] using h1
      have hsub : (63 : BitVec 64) - (BitVec.ofNat 64 aVal).clz = BitVec.ofNat 64 aVal.log2 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
          (by rw [show (63 : BitVec 64).toNat = 63 from rfl]; omega)),
          show (63 : BitVec 64).toNat = 63 from rfl, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : aVal.log2 < 2 ^ 64), hlog]
      have hlog_lt : aVal.log2 < 2 ^ 63 := by rw [hlog]; omega
      have henc : ((BitVec.ofNat 64 aVal.log2 <<< (1 : Nat)) ||| (1 : BitVec 64)) =
          BitVec.ofNat 64 (2 * aVal.log2 + 1) := bv64_encodeNat hlog_lt
      rw [hsub, henc]
      refine hQ _ st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
      simp [natBitsPost, natRep, hlog_lt]
  · have ha_box := ha
    dsimp only [natRep] at ha_box
    simp only [ha_sm, ↓reduceIte] at ha_box
    rcases ha_box with ⟨hbit0, obj, hmem, rfl, hcan⟩
    rcases hcan with ⟨hwfO, htag, _, harr, h1, hmax, hlast, hval, _⟩
    apply wp_jnz_false (by simp [hbit0])
    c0_let_simp
    have hm' : (lcnfHeap objs ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R)) m := by sep_use hm
    obtain ⟨idx, hlt, heq_idx, hm_foc⟩ := lcnfHeap_mpz_focus hmem htag hm'
    rw [wp_load]
    refine ⟨obj.mpzMeta, loadVal_cell64 (sep_mpz_swap2 hm_foc), ?_⟩
    c0_let_simp
    have hcap32 : obj.cap < 2 ^ 32 := by
      have h := hwfO.2.2.2.2.2.2.2.2.2
      simp [htag, mpzTag, closureTag, arrayTag, sarrayTag, stringTag] at h
      omega
    have harr32 : obj.arrSize < 2 ^ 32 := by rw [harr]; unfold mpzMaxLimbs at hmax; omega
    rw [mpzMeta_arrSize_nat obj hcap32 harr32]
    have harr_bv : (BitVec.ofNat 64 obj.arrSize).toNat = obj.limbs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), harr]
    have hne : obj.limbs ≠ [] := by intro h; simp [h] at h1
    have htrim : trimLenLoop obj.limbs (BitVec.ofNat 64 obj.arrSize).toNat = obj.limbs.length := by
      rw [harr_bv, ← limbLenNat_trimLenLoop (le_refl _), List.take_length,
        limbLenNat_eq_length_of_trimmed hne hlast]
    apply bn_trim_call_wp (R := cell64 obj.addr obj.header ⋆ cell64 (obj.addr + 8#64) obj.mpzMeta ⋆
      ((lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆
        (bigNumRtInv rt st scr scrLimbs ⋆ R)))
      (by rw [harr_bv]; exact le_refl _) (by exact sep_mpz_swap3 hm_foc)
    rw [htrim]
    c0_let_simp
    have hnz_tn : (BitVec.ofNat 64 obj.limbs.length == 0#64) = false := by
      apply Bool.eq_false_iff.mpr; intro ht
      have := BitVec.toNat_eq.mp (beq_iff_eq.mp ht)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hmax; omega),
        show (0#64 : BitVec 64).toNat = 0 from rfl] at this
      omega
    apply wp_jnz_false hnz_tn
    c0_let_simp
    have ha_idx : obj.addr + (((2 : BitVec 64) +
      BitVec.ofNat 64 obj.limbs.length) - (1 : BitVec 64)) * (8 : BitVec 64) =
        (obj.addr + 16#64) + BitVec.ofNat 64 (8 * (obj.limbs.length - 1)) := by
      rw [BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      unfold mpzMaxLimbs at hmax
      simp [BitVec.toNat_mul, BitVec.toNat_add,
        Nat.mod_eq_of_lt (by omega : obj.limbs.length < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 + obj.limbs.length < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 8 * (obj.limbs.length - 1) < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 16 + 8 * (obj.limbs.length - 1) < 2 ^ 64)]
      omega
    rw [wp_load]
    refine ⟨obj.limbs[obj.limbs.length - 1]'(by omega), ?_, ?_⟩
    · rw [ha_idx]; exact loadVal_array64 (by omega) (sep_mpz_swap3 hm_foc)
    · c0_let_simp
      have hlast_el : obj.limbs[obj.limbs.length - 1] ≠ 0#64 := by
        have := list_getLast!_eq_getLast obj.limbs hne
        rw [List.getLast_eq_getElem hne] at this
        rwa [this] at hlast
      have hclz : obj.limbs[obj.limbs.length - 1].clz.toNat < 64 :=
        BitVec.clz_lt_iff_ne_zero.mpr hlast_el
      have hlog : aVal.log2 =
        64 * obj.limbs.length - 1 - obj.limbs[obj.limbs.length - 1].clz.toNat := by
        have h1' := limbsVal_log2 hne (by rwa [List.getLast_eq_getElem hne])
        rw [List.getLast_eq_getElem hne] at h1'
        rwa [hval] at h1'
      have hlog_lt : aVal.log2 < 2 ^ 63 := by
        unfold mpzMaxLimbs at hmax; omega
      have hlen_lt64 : obj.limbs.length < 2 ^ 64 := by unfold mpzMaxLimbs at hmax; omega
      have hmul_lt64 : 64 * obj.limbs.length < 2 ^ 64 := by unfold mpzMaxLimbs at hmax; omega
      have hexpr :
          ((BitVec.ofNat 64 obj.limbs.length * (64 : BitVec 64) - (1 : BitVec 64)) -
            obj.limbs[obj.limbs.length - 1].clz) = BitVec.ofNat 64 aVal.log2 := by
        apply BitVec.eq_of_toNat_eq
        unfold mpzMaxLimbs at hmax
        have hpos : 0 < obj.limbs.length := List.length_pos_iff.mpr hne
        have hmul : (BitVec.ofNat 64 obj.limbs.length * (64 : BitVec 64)).toNat =
          64 * obj.limbs.length := by
          rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (64 : BitVec 64).toNat = 64 from rfl,
            Nat.mod_eq_of_lt hlen_lt64, Nat.mul_comm _ 64, Nat.mod_eq_of_lt hmul_lt64]
        have hsub1 : (BitVec.ofNat 64 obj.limbs.length * (64 : BitVec 64) - (1 : BitVec 64)).toNat =
            64 * obj.limbs.length - 1 := by
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
            (by rw [show (1 : BitVec 64).toNat = 1 from rfl, hmul]; omega)),
            hmul, show (1 : BitVec 64).toNat = 1 from rfl]
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
          (by rw [hsub1]; omega)), hsub1, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : aVal.log2 < 2 ^ 64), hlog]
      have henc2 : ((BitVec.ofNat 64 aVal.log2 <<< (1 : Nat)) ||| (1 : BitVec 64)) =
          BitVec.ofNat 64 (2 * aVal.log2 + 1) := bv64_encodeNat hlog_lt
      rw [hexpr, henc2]
      refine hQ _ st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
      simp [natBitsPost, natRep, hlog_lt]

private theorem lcnf_nat_bits_shr_wp
    (rt a b : BitVec 64) (aVal bVal : Nat) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hwf : BigNumRtWf rt st scr scrLimbs) (ha : natRep a aVal objs) (hb : natRep b bVal objs)
    (hok : natBitsOk 9 aVal b objs scrLimbs.length st)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natBitsPost 9 aVal b res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var a, Arg.imm 1, ()) } fun p_5 =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool,
            args := (Arg.var p_5.fst, Arg.imm 0, ()) } fun p_6 =>
          Expr.jnz (Arg.var p_6.fst)
            (Expr.let_
              { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var b, Arg.imm 1,
                ()) } fun p_7 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                  args := (Arg.var p_7.fst, Arg.imm 0, ()) } fun p_8 =>
                Expr.jnz (Arg.var p_8.fst) (Expr.ret (Arg.imm 1, ()))
                  (Expr.let_
                    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_9 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var b,
                        Arg.var p_9.fst, ()) }
                      fun p_10 =>
                      Expr.let_
                        { sig := [i64, i64],
                          code := OpCode.cmp CmpOp.uge i64 Ty.bool,
                          args := (Arg.var p_10.fst, Arg.imm 64, ()) } fun p_11 =>
                        Expr.jnz (Arg.var p_11.fst) (Expr.ret (Arg.imm 1, ()))
                          (Expr.let_
                            { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1,
                              ()) } fun p_12 =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var a,
                                Arg.var p_12.fst, ()) }
                              fun p =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.lshr i64,
                                  args := (Arg.var p.fst, Arg.var p_10.fst, ()) } fun p =>
                                Expr.let_
                                  { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1,
                                    ()) } fun p_13 =>
                                  Expr.let_
                                    { sig := [i64, i64], code := OpCode.shl i64,
                                      args := (Arg.var p.fst, Arg.var p_13.fst, ()) } fun p =>
                                    Expr.let_
                                      { sig := [i64, i64], code := OpCode.or i64,
                                        args := (Arg.var p.fst, Arg.imm 1, ()) }
                                      fun p => Expr.ret (Arg.var p.fst, ()))))
            (Expr.let_
              { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var b, Arg.imm 1,
                ()) } fun p_7 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                  args := (Arg.var p_7.fst, Arg.imm 0, ()) } fun p_8 =>
                Expr.jnz (Arg.var p_8.fst) (Expr.ret (Arg.imm 1, ()))
                  (Expr.let_
                    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_9 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var b,
                        Arg.var p_9.fst, ()) }
                      fun p_10 =>
                      Expr.let_
                        { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 6,
                          ()) } fun p_11 =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var p_10.fst,
                            Arg.var p_11.fst, ()) }
                          fun p_12 =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var p_10.fst,
                              Arg.imm 63, ()) }
                            fun p_13 =>
                            Expr.call (as := [i64]) (bs := [i64]) "bn_nat_len" (Arg.var a,
                              ()) fun p_14 =>
                              Expr.group (sig := [[]])
                                (fun _Js =>
                                  Blocks.cons
                                    (fun _p_15 =>
                                      Expr.let_
                                        { sig := [i64, i64],
                                          code := OpCode.cmp CmpOp.uge i64 Ty.bool,
                                          args := (Arg.var p_12.fst, Arg.var p_14.fst,
                                            ()) } fun p_16 =>
                                        Expr.jnz (Arg.var p_16.fst) (Expr.ret (Arg.imm 1, ()))
                                          (Expr.exit (as := [i64, i64]) "lcnf_panic" (Arg.var rt,
                                            Arg.imm 2, ())))
                                    Blocks.nil)
                                fun Js =>
                                Expr.let_
                                  { sig := [i64, i64],
                                    code := OpCode.cmp CmpOp.uge i64 Ty.bool,
                                    args := (Arg.var p_12.fst, Arg.var p_14.fst, ()) } fun p_15 =>
                                  Expr.jnz (Arg.var p_15.fst) (Expr.jump Js.fst ())
                                    (Expr.let_
                                      { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                                        args := (Arg.var p_14.fst, Arg.imm 33554429,
                                          ()) } fun p_16 =>
                                      Expr.jnz (Arg.var p_16.fst) (Expr.jump Js.fst ())
                                        (Expr.let_
                                          { sig := [i64, i64], code := OpCode.mul i64,
                                            args := (Arg.imm 2, Arg.var p_14.fst, ()) } fun p_17 =>
                                          Expr.let_
                                            { sig := [i64, i64], code := OpCode.sub i64,
                                              args := (Arg.var p_17.fst, Arg.var p_12.fst,
                                                ()) } fun p_18 =>
                                            Expr.call (as := [i64,
                                              i64]) (bs := [i64]) "bn_require_scratch"
                                              (Arg.var rt, Arg.var p_18.fst, ()) fun p_19 =>
                                              Expr.call (as := [i64,
                                                i64]) (bs := [i64]) "bn_load_nat"
                                                (Arg.var a, Arg.var p_19.fst, ()) fun p_20 =>
                                                Expr.let_
                                                  { sig := [i64, i64], code := OpCode.mul i64,
                                                    args := (Arg.imm 8, Arg.var p_20.fst,
                                                      ()) } fun p_21 =>
                                                  Expr.let_
                                                    { sig := [i64, i64], code := OpCode.add i64,
                                                      args := (Arg.var p_19.fst, Arg.var p_21.fst,
                                                        ()) } fun p_22 =>
                                                    Expr.call (as := [i64, i64, i64, i64,
                                                      i64]) (bs := [i64]) "bn_shr"
                                                      (Arg.var p_19.fst, Arg.var p_20.fst,
                                                        Arg.var p_12.fst,
                                                       Arg.var p_13.fst, Arg.var p_22.fst, ())
                                                         fun p_23 =>
                                                      Expr.let_
                                                        { sig := [i64, i64], code := OpCode.mul i64,
                                                          args := (Arg.imm 8, Arg.var p_20.fst,
                                                            ()) } fun p_24 =>
                                                        Expr.let_
                                                          { sig := [i64, i64],
                                                            code := OpCode.add i64,
                                                            args := (Arg.var p_19.fst,
                                                              Arg.var p_24.fst, ()) } fun p_25 =>
                                                          Expr.call (as := [i64, i64,
                                                            i64]) (bs := [i64])
                                                            "bn_nat_from_limbs"
                                                            (Arg.var rt, Arg.var p_25.fst,
                                                              Arg.var p_23.fst, ())
                                                            fun p =>
                                                              Expr.ret (Arg.var p.fst,
                                                                ())))))) m := by
  have hret_shr0 : ∀ (hshr : aVal >>> bVal = 0),
      Q (1#64, ()) m := by
    intro hshr
    refine hQ 1#64 st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
    dsimp only [natBitsPost]
    simp only [show (9 : Nat) ≠ 13 by decide, show (9 : Nat) ≠ 14 by decide,
      show (9 : Nat) ≠ 19 by decide, ↓reduceIte]
    exact ⟨bVal, hb, fun o ho => ho, by simp [hshr, natRep]⟩
  have hbig_shift : 2 ^ 63 ≤ bVal → aVal >>> bVal = 0 := by
    intro hb63
    have hna_max := limbLenNat_le_max_of_natRep ha
    have hlt_pow : aVal < 2 ^ bVal := by
      refine Nat.lt_of_lt_of_le limbLenNat_lt_pow ?_
      apply Nat.pow_le_pow_right (by decide)
      unfold mpzMaxLimbs at hna_max; omega
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hlt_pow
  c0_let_simp
  by_cases ha_sm : aVal < 2 ^ 63
  · have hbitA : (a &&& 1#64) ≠ 0#64 := fun hz => by
      have := (natRep_and_one_eq_zero_iff ha).mp hz; omega
    apply wp_jnz_true (by simp [hbitA])
    c0_let_simp
    by_cases hb_sm : bVal < 2 ^ 63
    · have hbitB : (b &&& 1#64) ≠ 0#64 := fun hz => by
        have := (natRep_and_one_eq_zero_iff hb).mp hz; omega
      apply wp_jnz_false (by simp [hbitB])
      c0_let_simp
      rw [natRep_small_shr1_nat hb hb_sm]
      by_cases hb64 : 64 ≤ bVal
      · apply wp_jnz_true
          (by rw [BitVec.ule]; exact decide_eq_true (by
                rw [show (64 : BitVec 64).toNat = 64 from rfl, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega)]
                exact hb64))
        c0_step
        have hlt : aVal < 2 ^ bVal :=
          Nat.lt_of_lt_of_le ha_sm (Nat.pow_le_pow_right (by decide) (by omega))
        exact hret_shr0 (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hlt)
      · have hb_lt64 : bVal < 64 := by omega
        apply wp_jnz_false
          (by rw [BitVec.ule, decide_eq_false_iff_not]
              rw [show (64 : BitVec 64).toNat = 64 from rfl, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega)]
              omega)
        c0_let_simp
        rw [natRep_small_shr1_nat ha ha_sm]
        have hsh : BitVec.ofNat 64 aVal >>> ((BitVec.ofNat 64 bVal).toNat % 64) =
            BitVec.ofNat 64 (aVal >>> bVal) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : aVal < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : bVal < 2 ^ 64),
            Nat.mod_eq_of_lt hb_lt64,
            Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by omega))]
        have hres_lt : aVal >>> bVal < 2 ^ 63 :=
          Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha_sm
        have henc : ((BitVec.ofNat 64 (aVal >>> bVal) <<< (1 : Nat)) ||| (1 : BitVec 64)) =
            BitVec.ofNat 64 (2 * (aVal >>> bVal) + 1) := bv64_encodeNat hres_lt
        rw [hsh, henc]
        refine hQ _ st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
        dsimp only [natBitsPost]
        simp only [show (9 : Nat) ≠ 13 by decide, show (9 : Nat) ≠ 14 by decide,
          show (9 : Nat) ≠ 19 by decide, ↓reduceIte]
        exact ⟨bVal, hb, fun o ho => ho, by simp [natRep, hres_lt]⟩
    · have hbitB : (b &&& 1#64) = 0#64 := (natRep_and_one_eq_zero_iff hb).mpr (by omega)
      apply wp_jnz_true (by simp [hbitB])
      c0_step; exact hret_shr0 (hbig_shift (by omega))
  · have hbitA : (a &&& 1#64) = 0#64 := (natRep_and_one_eq_zero_iff ha).mpr (by omega)
    apply wp_jnz_false (by simp [hbitA])
    c0_let_simp
    by_cases hb_sm : bVal < 2 ^ 63
    · have hbitB : (b &&& 1#64) ≠ 0#64 := fun hz => by
        have := (natRep_and_one_eq_zero_iff hb).mp hz; omega
      apply wp_jnz_false (by simp [hbitB])
      c0_let_simp
      rw [natRep_small_shr1_nat hb hb_sm]
      have hws : BitVec.ofNat 64 bVal >>> (6 : Nat) = BitVec.ofNat 64 (bVal / 64) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        simp [Nat.shiftRight_eq_div_pow]
      have hbs : BitVec.ofNat 64 bVal &&& (63 : BitVec 64) = BitVec.ofNat 64 (bVal % 64) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (63 : BitVec 64).toNat = 63 from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bVal < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : bVal % 64 < 2 ^ 64)]
        exact Nat.and_two_pow_sub_one_eq_mod bVal 6
      rw [hws, hbs]
      rcases hwf with ⟨hb48, hrt64, hscr0, hscra, hscrlen, hscr64⟩
      have hwf' : BigNumRtWf rt st scr scrLimbs := ⟨hb48, hrt64, hscr0, hscra, hscrlen, hscr64⟩
      have hna_max : limbLenNat aVal ≤ mpzMaxLimbs := limbLenNat_le_max_of_natRep ha
      apply bn_nat_len_rt_call_wp ha hm
      apply wp_join_group (fun _ m' => limbLenNat aVal ≤ bVal / 64 ∧ aVal >>> bVal = 0 ∧ m' = m)
      · intro _ _ m' ⟨hle', hshr, hm'⟩
        dsimp only [Blocks.get]; rw [hm']
        c0_let_simp
        apply wp_jnz_true
          (by rw [BitVec.ule]; exact decide_eq_true (by
                rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt
                    (by unfold mpzMaxLimbs at hna_max; omega : limbLenNat aVal < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : bVal / 64 < 2 ^ 64)]
                exact hle'))
        c0_let_simp; exact hret_shr0 hshr
      · intro Js hJs
        c0_let_simp
        have hws_lt : bVal / 64 < 2 ^ 64 := by omega
        have hna_lt : limbLenNat aVal < 2 ^ 64 := by unfold mpzMaxLimbs at hna_max; omega
        by_cases hle : limbLenNat aVal ≤ bVal / 64
        · apply wp_jnz_true
            (by rw [BitVec.ule]; exact decide_eq_true (by
                  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt, Nat.mod_eq_of_lt hws_lt]
                  exact hle))
          have hlt : aVal < 2 ^ bVal := by
            refine Nat.lt_of_lt_of_le limbLenNat_lt_pow ?_
            apply Nat.pow_le_pow_right (by decide); omega
          have hshr0 : aVal >>> bVal = 0 := by
            rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hlt
          rw [wp_jump]; exact hJs () m ⟨hle, hshr0, rfl⟩
        · have hws_lt_na : bVal / 64 < limbLenNat aVal := by omega
          apply wp_jnz_false
            (by rw [BitVec.ule, decide_eq_false_iff_not]
                simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt, Nat.mod_eq_of_lt hws_lt]
                omega)
          c0_let_simp
          have huga : (33554429#64 : BitVec 64).ult (BitVec.ofNat 64 (limbLenNat aVal)) = false :=
            by
            apply Bool.eq_false_iff.mpr; intro ht
            have : (33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 (limbLenNat aVal)).toNat :=
              of_decide_eq_true ht
            rw [show (33554429#64 : BitVec 64).toNat = 33554429 from rfl,
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt] at this
            unfold mpzMaxLimbs at hna_max; omega
          apply wp_jnz_false huga
          c0_let_simp
          have hok' := hok
          dsimp only [natBitsOk] at hok'
          simp only [show (9 : Nat) ≠ 13 by decide, show (9 : Nat) ≠ 14 by decide,
            show (9 : Nat) ≠ 19 by decide, ↓reduceIte] at hok'
          rcases hok' with ⟨bVal', hb', hok9⟩
          have hb_eq : bVal' = bVal := by
            dsimp only [natRep] at hb hb'
            simp only [hb_sm, ↓reduceIte] at hb
            by_cases hb'_sm : bVal' < 2 ^ 63
            · simp only [hb'_sm, ↓reduceIte] at hb'
              have heq := congrArg BitVec.toNat (hb.symm.trans hb')
              rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)] at heq
              omega
            · exfalso
              simp only [hb'_sm, ↓reduceIte] at hb'
              have hb0 := hb'.1
              have : (BitVec.ofNat 64 (2 * bVal + 1) &&& 1#64) = 1#64 := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide), Nat.and_one_is_mod]
                omega
              rw [hb, this] at hb0; exact absurd hb0 (by decide)
          rw [hb_eq] at hb' hok9
          rcases hok9 with hbad | ⟨hneed, halloc⟩
          · exfalso; omega
          have hneed_bv :
              ((2 : BitVec 64) * BitVec.ofNat 64 (limbLenNat aVal) - BitVec.ofNat 64
                (bVal / 64)).toNat =
                2 * limbLenNat aVal - bVal / 64 := by
            have hmul_le : 2 * limbLenNat aVal < 2 ^ 64 := by unfold mpzMaxLimbs at hna_max; omega
            rw [BitVec.toNat_sub_of_le]
            · rw [BitVec.toNat_mul, show (2 : BitVec 64).toNat = 2 from rfl, BitVec.toNat_ofNat,
                BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt, Nat.mod_eq_of_lt hws_lt,
                Nat.mod_eq_of_lt hmul_le]
            · change (BitVec.ofNat 64 (bVal / 64)).toNat ≤
                  ((2 : BitVec 64) * BitVec.ofNat 64 (limbLenNat aVal)).toNat
              rw [BitVec.toNat_mul, show (2 : BitVec 64).toNat = 2 from rfl, BitVec.toNat_ofNat,
                BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt, Nat.mod_eq_of_lt hws_lt,
                Nat.mod_eq_of_lt hmul_le]
              omega
          apply bn_require_scratch_rt_call_wp hwf' (by rw [hneed_bv]; exact hneed) hm
          have hna_le_scr : limbLenNat aVal ≤ scrLimbs.length := by omega
          have hm_split := hm
          dsimp only [bigNumRtInv] at hm_split
          rw [array64_split_len hna_le_scr] at hm_split
          apply bn_load_nat_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 (scr +
              BitVec.ofNat 64 (8 * limbLenNat aVal)) (scrLimbs.drop (limbLenNat aVal)) ⋆ R)
            ha (by rw [List.length_take_of_le hna_le_scr]; exact le_refl _) (by sep_use hm_split)
          intro scrA' m1 hlenA hvalA _ hm1
          c0_let_simp
          have hna_bv : (BitVec.ofNat 64 (limbLenNat aVal)).toNat = limbLenNat aVal := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt]
          have hna_leA : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤ scrA'.length := by
            rw [hna_bv, hlenA, List.length_take_of_le hna_le_scr]; exact le_refl _
          have hws_bv : (BitVec.ofNat 64 (bVal / 64)).toNat = bVal / 64 := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hws_lt]
          have hbs_bv : (BitVec.ofNat 64 (bVal % 64)).toNat = bVal % 64 := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hout_le : (BitVec.ofNat 64 (limbLenNat aVal)).toNat - (BitVec.ofNat 64
            (bVal / 64)).toNat ≤
              (scrLimbs.drop (limbLenNat aVal)).length := by
            rw [hna_bv, hws_bv, List.length_drop]; omega
          have h8mul := bv64_mul8_of_lt (limbLenNat aVal) (by unfold mpzMaxLimbs at hna_max; omega)
          rw [h8mul]
          apply bn_shr_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ lcnfHeap objs ⋆ R)
            hna_leA (by rw [hbs_bv]; omega) (Or.inr hout_le) (by sep_use hm1)
          intro outXs' m2
          dsimp only
          intro hlenOut htnOut hvalOut hm2
          c0_let_simp
          try rw [h8mul] at htnOut hvalOut hm2 ⊢
          have hshift_eq : 64 * (BitVec.ofNat 64 (bVal / 64)).toNat +
            (BitVec.ofNat 64 (bVal % 64)).toNat = bVal := by
            rw [hws_bv, hbs_bv]; omega
          have hvalA' : limbsVal (scrA'.take (BitVec.ofNat 64 (limbLenNat aVal)).toNat) = aVal := by
            rwa [hna_bv]
          rw [hvalA', hshift_eq] at htnOut hvalOut ⊢
          have hres_le : limbLenNat (aVal >>> bVal) ≤ limbLenNat aVal :=
            limbLenNat_mono (Nat.shiftRight_le _ _)
          have hres_max : limbLenNat (aVal >>> bVal) ≤ mpzMaxLimbs := Nat.le_trans hres_le hna_max
          have htn_bv : (BitVec.ofNat 64 (limbLenNat (aVal >>> bVal))).toNat =
            limbLenNat (aVal >>> bVal) := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hres_max; omega)]
          have hvalOut' : limbsVal (outXs'.take (BitVec.ofNat 64 (limbLenNat
            (aVal >>> bVal))).toNat) =
              aVal >>> bVal := by rwa [htn_bv]
          have htrim : trimLenLoop outXs' (BitVec.ofNat 64 (limbLenNat (aVal >>> bVal))).toNat =
              limbLenNat (aVal >>> bVal) := by
            rw [htn_bv, ← limbLenNat_trimLenLoop (by rw [hlenOut]; exact htnOut), hvalOut]
          have h8mul_r : BitVec.ofNat 64 (8 * limbLenNat aVal) =
              BitVec.ofNat 64 (limbLenNat aVal) * (8 : BitVec 64) := by
            rw [← h8mul, BitVec.mul_comm]
          rw [h8mul_r] at hm2
          apply bn_nat_from_limbs_call_wp (R := cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrA' ⋆ R)
            (by rw [htn_bv, hlenOut]; exact htnOut)
            (by rw [htn_bv]; exact hres_max) hb48
            (fun hge => by rw [hvalOut'] at hge; rw [htrim]; exact halloc hge)
            (by sep_use hm2)
          intro p st' objs' m3 hmst hrem hb' hrep hsm hbg hm3
          c0_step
          have hlenA' : scrA'.length = limbLenNat aVal := by
            rw [hlenA, List.length_take_of_le hna_le_scr]
          have hlenTot : (scrA' ++ outXs').length = scrLimbs.length := by
            rw [List.length_append, hlenA', hlenOut, List.length_drop]; omega
          have hm3' : (bigNumRtInv rt st' scr (scrA' ++ outXs') ⋆ lcnfHeap objs' ⋆ R) m3 := by
            dsimp only [bigNumRtInv]
            try rw [h8mul, Nat.mul_comm 8 (limbLenNat aVal)] at hm3
            try rw [← h8mul_r, Nat.mul_comm 8 (limbLenNat aVal)] at hm3
            rw [hlenTot, array64_append, hlenA']; sep_use hm3
          rw [hvalOut'] at hrep hsm hbg
          refine hQ p st' (scrA' ++ outXs') objs' m3 hmst hrem
            (BigNumRtWf.with_state_len hwf' hb' hlenTot) ?_ hm3'
          dsimp only [natBitsPost]
          simp only [show (9 : Nat) ≠ 13 by decide, show (9 : Nat) ≠ 14 by decide,
            show (9 : Nat) ≠ 19 by decide, ↓reduceIte]
          refine ⟨bVal, hb, ?_, by simp [hrep]⟩
          intro o ho
          by_cases hs : aVal >>> bVal < 2 ^ 63
          · rw [hsm hs]; exact ho
          · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
            exact List.mem_cons_of_mem _ ho
    · have hbitB : (b &&& 1#64) = 0#64 := (natRep_and_one_eq_zero_iff hb).mpr (by omega)
      apply wp_jnz_true (by simp [hbitB])
      c0_step; exact hret_shr0 (hbig_shift (by omega))

private theorem lcnf_nat_bits_shl_wp
    (rt a b : BitVec 64) (aVal : Nat) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hwf : BigNumRtWf rt st scr scrLimbs) (ha : natRep a aVal objs)
    (hok : natBitsOk 15 aVal b objs scrLimbs.length st)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natBitsPost 15 aVal b res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64]) (bs := [i64]) "bn_nat_len" (Arg.var a, ()) fun p_6 =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
            args := (Arg.var p_6.fst, Arg.imm 0, ()) } fun p_7 =>
          Expr.jnz (Arg.var p_7.fst) (Expr.ret (Arg.imm 1, ()))
            (Expr.let_
              { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var b, Arg.imm 1,
                ()) } fun p_8 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                  args := (Arg.var p_8.fst, Arg.imm 0, ()) } fun p_9 =>
                Expr.jnz (Arg.var p_9.fst) (Expr.exit (as := [i64, i64]) "lcnf_panic" (Arg.var rt,
                  Arg.imm 3, ()))
                  (Expr.let_
                    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_10 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var b,
                        Arg.var p_10.fst, ()) }
                      fun p_11 =>
                      Expr.let_
                        { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 6,
                          ()) } fun p_12 =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var p_11.fst,
                            Arg.var p_12.fst, ()) }
                          fun p_13 =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var p_11.fst,
                              Arg.imm 63, ()) }
                            fun p_14 =>
                            Expr.group (sig := [[]])
                              (fun _Js =>
                                Blocks.cons
                                  (fun _p_15 =>
                                    Expr.exit (as := [i64, i64]) "lcnf_panic" (Arg.var rt,
                                      Arg.imm 3, ()))
                                  Blocks.nil)
                              fun Js =>
                              Expr.let_
                                { sig := [i64, i64],
                                  code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                                  args := (Arg.var p_6.fst, Arg.imm 33554429, ()) } fun p_15 =>
                                Expr.jnz (Arg.var p_15.fst) (Expr.jump Js.fst ())
                                  (Expr.let_
                                    { sig := [i64, i64],
                                      code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                                      args := (Arg.var p_13.fst, Arg.imm 33554428, ()) } fun p_16 =>
                                    Expr.jnz (Arg.var p_16.fst) (Expr.jump Js.fst ())
                                      (Expr.let_
                                        { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var p_6.fst, Arg.var p_13.fst,
                                            ()) } fun p_17 =>
                                        Expr.let_
                                          { sig := [i64, i64], code := OpCode.add i64,
                                            args := (Arg.var p_17.fst, Arg.imm 1, ()) } fun p_18 =>
                                          Expr.let_
                                            { sig := [i64, i64],
                                              code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                                              args := (Arg.var p_18.fst, Arg.imm 33554429,
                                                ()) } fun p_19 =>
                                            Expr.jnz (Arg.var p_19.fst) (Expr.jump Js.fst ())
                                              (Expr.let_
                                                { sig := [i64, i64], code := OpCode.mul i64,
                                                  args := (Arg.imm 2, Arg.var p_6.fst,
                                                    ()) } fun p_20 =>
                                                Expr.let_
                                                  { sig := [i64, i64], code := OpCode.add i64,
                                                    args := (Arg.var p_20.fst, Arg.var p_13.fst,
                                                      ()) } fun p_21 =>
                                                  Expr.let_
                                                    { sig := [i64, i64], code := OpCode.add i64,
                                                      args := (Arg.var p_21.fst, Arg.imm 1,
                                                        ()) } fun p_22 =>
                                                    Expr.call (as := [i64,
                                                      i64]) (bs := [i64]) "bn_require_scratch"
                                                      (Arg.var rt, Arg.var p_22.fst, ()) fun p_23 =>
                                                      Expr.call (as := [i64,
                                                        i64]) (bs := [i64]) "bn_load_nat"
                                                        (Arg.var a, Arg.var p_23.fst,
                                                          ()) fun p_24 =>
                                                        Expr.let_
                                                          { sig := [i64, i64],
                                                            code := OpCode.mul i64,
                                                            args := (Arg.imm 8, Arg.var p_24.fst,
                                                              ()) } fun p_25 =>
                                                          Expr.let_
                                                            { sig := [i64, i64],
                                                              code := OpCode.add i64,
                                                              args := (Arg.var p_23.fst,
                                                                Arg.var p_25.fst, ()) } fun p_26 =>
                                                            Expr.call (as := [i64, i64, i64, i64,
                                                              i64]) (bs := [i64])
                                                              "bn_shl"
                                                              (Arg.var p_23.fst, Arg.var p_24.fst,
                                                                Arg.var p_13.fst,
                                                               Arg.var p_14.fst, Arg.var p_26.fst,
                                                                 ()) fun p_27 =>
                                                              Expr.let_
                                                                { sig := [i64, i64],
                                                                  code := OpCode.mul i64,
                                                                  args := (Arg.imm 8,
                                                                    Arg.var p_24.fst, ()) }
                                                                      fun p_28 =>
                                                                Expr.let_
                                                                  { sig := [i64, i64],
                                                                    code := OpCode.add i64,
                                                                    args := (Arg.var p_23.fst,
                                                                      Arg.var p_28.fst, ()) }
                                                                  fun p_29 =>
                                                                  Expr.call (as := [i64, i64,
                                                                    i64]) (bs := [i64])
                                                                    "bn_nat_from_limbs"
                                                                    (Arg.var rt, Arg.var p_29.fst,
                                                                      Arg.var p_27.fst, ())
                                                                    fun p =>
                                                                      Expr.ret (Arg.var p.fst,
                                                                        ()))))))) m := by
  have hok' := hok
  dsimp only [natBitsOk] at hok'
  simp only [show (15 : Nat) ≠ 13 by decide, show (15 : Nat) ≠ 14 by decide,
    show (15 : Nat) ≠ 19 by decide, ↓reduceIte] at hok'
  rcases hok' with ⟨bVal, hb, hok15⟩
  simp only [show (15 : Nat) ≠ 9 by decide, ↓reduceIte] at hok15
  rcases hwf with ⟨hb48, hrt64, hscr0, hscra, hscrlen, hscr64⟩
  have hwf' : BigNumRtWf rt st scr scrLimbs := ⟨hb48, hrt64, hscr0, hscra, hscrlen, hscr64⟩
  have hna_max : limbLenNat aVal ≤ mpzMaxLimbs := limbLenNat_le_max_of_natRep ha
  have hna_lt : limbLenNat aVal < 2 ^ 64 := by unfold mpzMaxLimbs at hna_max; omega
  apply bn_nat_len_rt_call_wp ha hm
  by_cases ha0 : aVal = 0
  · subst ha0
    have hna0 : BitVec.ofNat 64 (limbLenNat 0) = 0#64 := rfl
    apply wp_jnz_true (by rw [hna0]; decide)
    c0_step
    refine hQ 1#64 st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf' ?_ hm
    dsimp only [natBitsPost]
    simp only [show (15 : Nat) ≠ 13 by decide, show (15 : Nat) ≠ 14 by decide,
      show (15 : Nat) ≠ 19 by decide, ↓reduceIte]
    exact ⟨bVal, hb, fun o ho => ho, by simp [natRep]⟩
  · have hna_pos : 0 < limbLenNat aVal := limbLenNat_pos_iff.mpr (Nat.pos_of_ne_zero ha0)
    have hna_nz : (BitVec.ofNat 64 (limbLenNat aVal) == 0#64) = false := by
      apply Bool.eq_false_iff.mpr; intro ht
      have := BitVec.toNat_eq.mp (beq_iff_eq.mp ht)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt,
        show (0#64 : BitVec 64).toNat = 0 from rfl] at this; omega
    rcases hok15 with h0 | ⟨hb_sm, hsum_max, hscr_need, halloc⟩
    · exact absurd h0 ha0
    apply wp_jnz_false hna_nz
    c0_let_simp
    have hbitB : (b &&& 1#64) ≠ 0#64 := fun hz => by
      have := (natRep_and_one_eq_zero_iff hb).mp hz; omega
    apply wp_jnz_false (by simp [hbitB])
    c0_let_simp
    rw [natRep_small_shr1_nat hb hb_sm]
    have hws_lt : bVal / 64 < 2 ^ 64 := by omega
    have hws : BitVec.ofNat 64 bVal >>> (6 : Nat) = BitVec.ofNat 64 (bVal / 64) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp [Nat.shiftRight_eq_div_pow]
    have hbs : BitVec.ofNat 64 bVal &&& (63 : BitVec 64) = BitVec.ofNat 64 (bVal % 64) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (63 : BitVec 64).toNat = 63 from rfl,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bVal < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : bVal % 64 < 2 ^ 64)]
      exact Nat.and_two_pow_sub_one_eq_mod bVal 6
    rw [hws, hbs]
    apply wp_join_group (fun _ _ => False)
    · intro _ _ _ hf; exact False.elim hf
    · intro Js _
      c0_let_simp
      have hna_le_max : limbLenNat aVal ≤ 33554429 := hna_max
      have hws_le_max : bVal / 64 ≤ 33554428 := by unfold mpzMaxLimbs at hsum_max; omega
      have hsum_le_max : limbLenNat aVal + bVal / 64 + 1 ≤ 33554429 := hsum_max
      have huga : (33554429#64 : BitVec 64).ult (BitVec.ofNat 64 (limbLenNat aVal)) = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        have : (33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 (limbLenNat aVal)).toNat :=
          of_decide_eq_true ht
        rw [show (33554429#64 : BitVec 64).toNat = 33554429 from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt] at this
        omega
      have hugw : (33554428#64 : BitVec 64).ult (BitVec.ofNat 64 (bVal / 64)) = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        have : (33554428#64 : BitVec 64).toNat < (BitVec.ofNat 64 (bVal / 64)).toNat :=
          of_decide_eq_true ht
        rw [show (33554428#64 : BitVec 64).toNat = 33554428 from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hws_lt] at this
        omega
      have hugs : (33554429#64 : BitVec 64).ult
          ((BitVec.ofNat 64 (limbLenNat aVal) + BitVec.ofNat 64 (bVal / 64)) + 1#64) = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        have : (33554429#64 : BitVec 64).toNat <
            ((BitVec.ofNat 64 (limbLenNat aVal) + BitVec.ofNat 64 (bVal / 64)) + 1#64).toNat :=
          of_decide_eq_true ht
        rw [show (33554429#64 : BitVec 64).toNat = 33554429 from rfl,
          BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hna_lt, Nat.mod_eq_of_lt hws_lt,
          Nat.mod_eq_of_lt (by omega : limbLenNat aVal + bVal / 64 < 2 ^ 64),
          show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : limbLenNat aVal + bVal / 64 + 1 < 2 ^ 64)] at this
        omega
      apply wp_jnz_false huga
      c0_let_simp
      apply wp_jnz_false hugw
      c0_let_simp
      apply wp_jnz_false hugs
      c0_let_simp
      have hneed_bv :
          (((2 : BitVec 64) * BitVec.ofNat 64 (limbLenNat aVal) + BitVec.ofNat 64 (bVal / 64)) +
            (1 : BitVec 64)).toNat = 2 * limbLenNat aVal + bVal / 64 + 1 := by
        have hlt : 2 * limbLenNat aVal + bVal / 64 + 1 < 2 ^ 64 := by
          unfold mpzMaxLimbs at hna_max hsum_max; omega
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul,
          show (2 : BitVec 64).toNat = 2 from rfl,
          BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt, Nat.mod_eq_of_lt hws_lt,
          Nat.mod_eq_of_lt (by omega : 2 * limbLenNat aVal < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 2 * limbLenNat aVal + bVal / 64 < 2 ^ 64),
          show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt]
      apply bn_require_scratch_rt_call_wp hwf' (by rw [hneed_bv]; exact hscr_need) hm
      have hna_le_scr : limbLenNat aVal ≤ scrLimbs.length := by omega
      have hm_split := hm
      dsimp only [bigNumRtInv] at hm_split
      rw [array64_split_len hna_le_scr] at hm_split
      apply bn_load_nat_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) (scrLimbs.drop (limbLenNat aVal)) ⋆ R)
        ha (by rw [List.length_take_of_le hna_le_scr]; exact le_refl _) (by sep_use hm_split)
      intro scrA' m1 hlenA hvalA _ hm1
      c0_let_simp
      have hna_bv : (BitVec.ofNat 64 (limbLenNat aVal)).toNat = limbLenNat aVal := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt]
      have hna_leA : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤ scrA'.length := by
        rw [hna_bv, hlenA, List.length_take_of_le hna_le_scr]; exact le_refl _
      have hws_bv : (BitVec.ofNat 64 (bVal / 64)).toNat = bVal / 64 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hws_lt]
      have hbs_bv : (BitVec.ofNat 64 (bVal % 64)).toNat = bVal % 64 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hout_le : (BitVec.ofNat 64 (bVal / 64)).toNat +
          (BitVec.ofNat 64 (limbLenNat aVal)).toNat + 1 ≤
            (scrLimbs.drop (limbLenNat aVal)).length := by
        rw [hws_bv, hna_bv, List.length_drop]; omega
      have hout_lt : (BitVec.ofNat 64 (bVal / 64)).toNat +
          (BitVec.ofNat 64 (limbLenNat aVal)).toNat + 1 < 2 ^ 64 := by
        rw [hws_bv, hna_bv]; unfold mpzMaxLimbs at hsum_max; omega
      have h8mul := bv64_mul8_of_lt (limbLenNat aVal) (by unfold mpzMaxLimbs at hna_max; omega)
      rw [h8mul]
      apply bn_shl_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ lcnfHeap objs ⋆ R)
        hna_leA (by rw [hbs_bv]; omega) (Or.inr hout_le) hout_lt (by sep_use hm1)
      intro outXs' m2
      dsimp only
      intro hlenOut htnOut hvalOut hm2
      c0_let_simp
      try rw [h8mul] at htnOut hvalOut hm2 ⊢
      have hshift_eq : 64 * (BitVec.ofNat 64 (bVal / 64)).toNat +
        (BitVec.ofNat 64 (bVal % 64)).toNat = bVal := by
        rw [hws_bv, hbs_bv]; omega
      have hvalA' : limbsVal (scrA'.take (BitVec.ofNat 64 (limbLenNat aVal)).toNat) = aVal := by
        rwa [hna_bv]
      rw [hvalA', hshift_eq] at htnOut hvalOut ⊢
      have hres_max : limbLenNat (aVal <<< bVal) ≤ mpzMaxLimbs := by
        refine Nat.le_trans ?_ hsum_max
        have hlt_pow : aVal <<< bVal < 2 ^ (64 * (limbLenNat aVal + bVal / 64 + 1)) := by
          rw [Nat.shiftLeft_eq]
          have ha_pow := limbLenNat_lt_pow (n := aVal)
          have hmul : aVal * 2 ^ bVal < 2 ^ (64 * limbLenNat aVal) * 2 ^ bVal :=
            Nat.mul_lt_mul_of_pos_right ha_pow (Nat.pow_pos (by decide))
          rw [← Nat.pow_add] at hmul
          refine Nat.lt_of_lt_of_le hmul (Nat.pow_le_pow_right (by decide) ?_)
          omega
        by_cases hz : aVal <<< bVal = 0
        · simp [hz, limbLenNat]
        · conv => lhs; unfold limbLenNat
          simp only [hz, ↓reduceIte]
          have hl := (Nat.div_lt_iff_lt_mul (by decide : 0 < 64)).mpr
            ((Nat.log2_lt hz).mpr (by rw [Nat.mul_comm] at hlt_pow; exact hlt_pow))
          omega
      have htn_bv : (BitVec.ofNat 64 (limbLenNat (aVal <<< bVal))).toNat =
        limbLenNat (aVal <<< bVal) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hres_max; omega)]
      have hvalOut' : limbsVal (outXs'.take (BitVec.ofNat 64 (limbLenNat (aVal <<< bVal))).toNat) =
          aVal <<< bVal := by rwa [htn_bv]
      have htrim : trimLenLoop outXs' (BitVec.ofNat 64 (limbLenNat (aVal <<< bVal))).toNat =
          limbLenNat (aVal <<< bVal) := by
        rw [htn_bv, ← limbLenNat_trimLenLoop (by rw [hlenOut]; exact htnOut), hvalOut]
      have h8mul_r : BitVec.ofNat 64 (8 * limbLenNat aVal) =
          BitVec.ofNat 64 (limbLenNat aVal) * (8 : BitVec 64) := by
        rw [← h8mul, BitVec.mul_comm]
      rw [h8mul_r] at hm2
      apply bn_nat_from_limbs_call_wp (R := cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrA' ⋆ R)
        (by rw [htn_bv, hlenOut]; exact htnOut)
        (by rw [htn_bv]; exact hres_max) hb48
        (fun hge => by rw [hvalOut'] at hge; rw [htrim]; exact halloc hge)
        (by sep_use hm2)
      intro p st' objs' m3 hmst hrem hb' hrep hsm hbg hm3
      c0_step
      have hlenA' : scrA'.length = limbLenNat aVal := by
        rw [hlenA, List.length_take_of_le hna_le_scr]
      have hlenTot : (scrA' ++ outXs').length = scrLimbs.length := by
        rw [List.length_append, hlenA', hlenOut, List.length_drop]; omega
      have hm3' : (bigNumRtInv rt st' scr (scrA' ++ outXs') ⋆ lcnfHeap objs' ⋆ R) m3 := by
        dsimp only [bigNumRtInv]
        try rw [h8mul, Nat.mul_comm 8 (limbLenNat aVal)] at hm3
        try rw [← h8mul_r, Nat.mul_comm 8 (limbLenNat aVal)] at hm3
        rw [hlenTot, array64_append, hlenA']
        sep_use hm3
      rw [hvalOut'] at hrep hsm hbg
      refine hQ p st' (scrA' ++ outXs') objs' m3 hmst hrem
        (BigNumRtWf.with_state_len hwf' hb' hlenTot) ?_ hm3'
      dsimp only [natBitsPost]
      simp only [show (15 : Nat) ≠ 13 by decide, show (15 : Nat) ≠ 14 by decide,
        show (15 : Nat) ≠ 19 by decide, show (15 : Nat) ≠ 9 by decide, ↓reduceIte]
      refine ⟨bVal, hb, ?_, by simp [hrep]⟩
      intro o ho
      by_cases hs : aVal <<< bVal < 2 ^ 63
      · rw [hsm hs]; exact ho
      · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
        exact List.mem_cons_of_mem _ ho

private theorem lcnf_nat_bits_bw_wp
    (rt op a b : BitVec 64) (aVal : Nat) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hwf : BigNumRtWf rt st scr scrLimbs) (ha : natRep a aVal objs)
    (hop : op.toNat ∈ [10, 11, 12])
    (hok : natBitsOk op.toNat aVal b objs scrLimbs.length st)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natBitsPost op.toNat aVal b res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64]) (bs := [i64]) "bn_nat_len" (Arg.var a, ()) fun p_6 =>
        Expr.call (as := [i64]) (bs := [i64]) "bn_nat_len" (Arg.var b, ()) fun p_7 =>
          Expr.group (sig := [[]])
            (fun _Js =>
              Blocks.cons (fun _p_8 =>
                Expr.exit (as := [i64, i64]) "lcnf_panic" (Arg.var rt, Arg.imm 2, ())) Blocks.nil)
            fun Js =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                args := (Arg.var p_6.fst, Arg.imm 33554429, ()) } fun p_8 =>
              Expr.jnz (Arg.var p_8.fst) (Expr.jump Js.fst ())
                (Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                    args := (Arg.var p_7.fst, Arg.imm 33554429, ()) } fun p_9 =>
                  Expr.jnz (Arg.var p_9.fst) (Expr.jump Js.fst ())
                    (Expr.group (sig := [[i64]])
                      (fun _Js =>
                        Blocks.cons
                          (fun p_10 =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_6.fst,
                                Arg.var p_7.fst, ()) }
                              fun p_11 =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var p_11.fst, Arg.var p_10.fst, ()) } fun p_12 =>
                                Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var p_12.fst, Arg.imm 1, ()) }
                                  fun p_13 =>
                                  Expr.call (as := [i64, i64]) (bs := [i64]) "bn_require_scratch"
                                    (Arg.var rt, Arg.var p_13.fst, ()) fun p_14 =>
                                    Expr.let_
                                      { sig := [i64, i64], code := OpCode.mul i64,
                                        args := (Arg.imm 8, Arg.var p_6.fst, ()) }
                                      fun p_15 =>
                                      Expr.let_
                                        { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var p_14.fst, Arg.var p_15.fst,
                                            ()) } fun p_16 =>
                                        Expr.let_
                                          { sig := [i64, i64], code := OpCode.add i64,
                                            args := (Arg.var p_6.fst, Arg.var p_7.fst,
                                              ()) } fun p_17 =>
                                          Expr.let_
                                            { sig := [i64, i64], code := OpCode.mul i64,
                                              args := (Arg.imm 8, Arg.var p_17.fst,
                                                ()) } fun p_18 =>
                                            Expr.let_
                                              { sig := [i64, i64], code := OpCode.add i64,
                                                args := (Arg.var p_14.fst, Arg.var p_18.fst,
                                                  ()) } fun p_19 =>
                                              Expr.call (as := [i64,
                                                i64]) (bs := [i64]) "bn_load_nat"
                                                (Arg.var a, Arg.var p_14.fst, ()) fun p_20 =>
                                                Expr.call (as := [i64,
                                                  i64]) (bs := [i64]) "bn_load_nat"
                                                  (Arg.var b, Arg.var p_16.fst, ()) fun p_21 =>
                                                  Expr.let_
                                                    { sig := [i64, i64], code := OpCode.sub i64,
                                                      args := (Arg.var op, Arg.imm 10,
                                                        ()) } fun p_22 =>
                                                    Expr.call (as := [i64, i64, i64, i64, i64,
                                                      i64]) (bs := [i64])
                                                      "bn_bitwise"
                                                      (Arg.var p_22.fst, Arg.var p_14.fst,
                                                        Arg.var p_20.fst,
                                                       Arg.var p_16.fst, Arg.var p_21.fst, Arg.var
                                                         p_19.fst, ())
                                                      fun p_23 =>
                                                      Expr.call (as := [i64, i64,
                                                        i64]) (bs := [i64]) "bn_nat_from_limbs"
                                                        (Arg.var rt, Arg.var p_19.fst,
                                                          Arg.var p_23.fst, ()) fun p =>
                                                        Expr.ret (Arg.var p.fst, ()))
                          Blocks.nil)
                      fun Js =>
                      Expr.let_
                        { sig := [i64, i64],
                          code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                          args := (Arg.var p_6.fst, Arg.var p_7.fst, ()) } fun p =>
                        Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.var p_6.fst, ()))
                          (Expr.jump Js.fst (Arg.var p_7.fst, ()))))) m := by
  have hnot13 : op.toNat ≠ 13 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop; omega
  have hnot14 : op.toNat ≠ 14 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop; omega
  have hnot19 : op.toNat ≠ 19 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop; omega
  have hnot9 : op.toNat ≠ 9 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop; omega
  have hnot15 : op.toNat ≠ 15 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop; omega
  have hok' := hok
  dsimp only [natBitsOk] at hok'
  simp only [hnot13, hnot14, hnot19, ↓reduceIte] at hok'
  rcases hok' with ⟨bVal, hb, hok_bw⟩
  simp only [hnot9, hnot15, hop, ↓reduceIte] at hok_bw
  rcases hok_bw with ⟨hneed, halloc⟩
  rcases hwf with ⟨hb48, hrt64, hscr0, hscra, hscrlen, hscr64⟩
  have hwf' : BigNumRtWf rt st scr scrLimbs := ⟨hb48, hrt64, hscr0, hscra, hscrlen, hscr64⟩
  have hna_max : limbLenNat aVal ≤ mpzMaxLimbs := limbLenNat_le_max_of_natRep ha
  have hnb_max : limbLenNat bVal ≤ mpzMaxLimbs := limbLenNat_le_max_of_natRep hb
  have hna_lt : limbLenNat aVal < 2 ^ 64 := by unfold mpzMaxLimbs at hna_max; omega
  have hnb_lt : limbLenNat bVal < 2 ^ 64 := by unfold mpzMaxLimbs at hnb_max; omega
  apply bn_nat_len_rt_call_wp ha hm
  apply bn_nat_len_rt_call_wp hb hm
  apply wp_join_group (fun _ _ => False)
  · intro _ _ _ hf; exact False.elim hf
  · intro Js_err _
    c0_let_simp
    have huga : (33554429#64 : BitVec 64).ult (BitVec.ofNat 64 (limbLenNat aVal)) = false := by
      apply Bool.eq_false_iff.mpr; intro ht
      have : (33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 (limbLenNat aVal)).toNat :=
        of_decide_eq_true ht
      rw [show (33554429#64 : BitVec 64).toNat = 33554429 from rfl,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt] at this
      unfold mpzMaxLimbs at hna_max; omega
    have hugb : (33554429#64 : BitVec 64).ult (BitVec.ofNat 64 (limbLenNat bVal)) = false := by
      apply Bool.eq_false_iff.mpr; intro ht
      have : (33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 (limbLenNat bVal)).toNat :=
        of_decide_eq_true ht
      rw [show (33554429#64 : BitVec 64).toNat = 33554429 from rfl,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnb_lt] at this
      unfold mpzMaxLimbs at hnb_max; omega
    apply wp_jnz_false huga
    c0_let_simp
    apply wp_jnz_false hugb
    apply wp_join_group
      (fun (p : Tup Val [i64]) (m' : Mem 64) =>
        p.fst = BitVec.ofNat 64 (max (limbLenNat aVal) (limbLenNat bVal)) ∧ m' = m)
    · intro _ p m' ⟨hp, hm'⟩
      subst hm'
      simp only [Blocks.get]
      c0_let_simp
      rw [hp]
      have hna_bv : (BitVec.ofNat 64 (limbLenNat aVal)).toNat = limbLenNat aVal := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt]
      have hnb_bv : (BitVec.ofNat 64 (limbLenNat bVal)).toNat = limbLenNat bVal := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnb_lt]
      have hmax_lt : max (limbLenNat aVal) (limbLenNat bVal) < 2 ^ 64 := by
        unfold mpzMaxLimbs at hna_max hnb_max; omega
      have hneed_bv : ((BitVec.ofNat 64 (limbLenNat aVal) + BitVec.ofNat 64 (limbLenNat bVal) +
          BitVec.ofNat 64 (max (limbLenNat aVal) (limbLenNat bVal))) + (1 : BitVec 64)).toNat =
          limbLenNat aVal + limbLenNat bVal + max (limbLenNat aVal) (limbLenNat bVal) + 1 := by
        have h1 : limbLenNat aVal + limbLenNat bVal < 2 ^ 64 := by
          unfold mpzMaxLimbs at hna_max hnb_max; omega
        have h2 : limbLenNat aVal + limbLenNat bVal + max (limbLenNat aVal) (limbLenNat bVal) <
          2 ^ 64 := by
          unfold mpzMaxLimbs at hna_max hnb_max; omega
        have h3 : limbLenNat aVal + limbLenNat bVal + max (limbLenNat aVal) (limbLenNat bVal) + 1 <
          2 ^ 64 := by
          unfold mpzMaxLimbs at hna_max hnb_max; omega
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, hna_bv, hnb_bv,
          BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hmax_lt, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
          show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h3]
      apply bn_require_scratch_rt_call_wp hwf' (by rw [hneed_bv]; exact hneed) hm
      c0_let_simp
      have h8a := bv64_mul8_of_lt (limbLenNat aVal) (by unfold mpzMaxLimbs at hna_max; omega)
      have hadd_ab : BitVec.ofNat 64 (limbLenNat aVal) + BitVec.ofNat 64 (limbLenNat bVal) =
          BitVec.ofNat 64 (limbLenNat aVal + limbLenNat bVal) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hna_bv, hnb_bv, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hna_max hnb_max; omega)]
      have h8ab := bv64_mul8_of_lt (limbLenNat aVal + limbLenNat bVal)
        (by unfold mpzMaxLimbs at hna_max hnb_max; omega)
      rw [h8a, hadd_ab, h8ab]
      have hna_le_scr : limbLenNat aVal ≤ scrLimbs.length := by omega
      have hnb_le_rest : limbLenNat bVal ≤ (scrLimbs.drop (limbLenNat aVal)).length := by
        rw [List.length_drop]; omega
      have hm_split := hm
      dsimp only [bigNumRtInv] at hm_split
      rw [array64_split_len hna_le_scr,
        array64_split_len (a := scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) hnb_le_rest,
        List.drop_drop,
        BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add] at hm_split
      apply bn_load_nat_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal))
          ((scrLimbs.drop (limbLenNat aVal)).take (limbLenNat bVal)) ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal)))
          (scrLimbs.drop (limbLenNat aVal + limbLenNat bVal)) ⋆ R)
        ha (by rw [List.length_take_of_le hna_le_scr]; exact le_refl _) (by sep_use hm_split)
      intro scrA' m1 hlenA hvalA _ hm1
      apply bn_load_nat_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrA' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal)))
          (scrLimbs.drop (limbLenNat aVal + limbLenNat bVal)) ⋆ R)
        hb (by rw [List.length_take_of_le hnb_le_rest]; exact le_refl _) (by sep_use hm1)
      intro scrB' m2 hlenB hvalB _ hm2
      c0_let_simp
      have hlenA' : scrA'.length = limbLenNat aVal := by
        rw [hlenA, List.length_take_of_le hna_le_scr]
      have hlenB' : scrB'.length = limbLenNat bVal := by
        rw [hlenB, List.length_take_of_le hnb_le_rest]
      have hop_sub : (op - 10#64 = 0#64 ∨ op - 10#64 = 1#64 ∨ op - 10#64 = 2#64) := by
        rcases (by simpa using hop : op.toNat = 10 ∨ op.toNat = 11 ∨ op.toNat = 12) with h | h | h
        · left; apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_sub_of_le (by change 10 ≤ op.toNat; omega), h]; decide
        · right; left; apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_sub_of_le (by change 10 ≤ op.toNat; omega), h]; decide
        · right; right; apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_sub_of_le (by change 10 ≤ op.toNat; omega), h]; decide
      have hout_bw : (if op - 10#64 = 0#64 then
          min (BitVec.ofNat 64 (limbLenNat aVal)).toNat (BitVec.ofNat 64 (limbLenNat bVal)).toNat
          else max (BitVec.ofNat 64 (limbLenNat aVal)).toNat (BitVec.ofNat 64
            (limbLenNat bVal)).toNat) ≤
          (scrLimbs.drop (limbLenNat aVal + limbLenNat bVal)).length := by
        rw [hna_bv, hnb_bv, List.length_drop]
        by_cases h0 : op - 10#64 = 0#64 <;> simp only [h0, ↓reduceIte] <;> omega
      have hna_leA' : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤ scrA'.length := by
        rw [hna_bv, hlenA']; exact le_refl _
      have hnb_leB' : (BitVec.ofNat 64 (limbLenNat bVal)).toNat ≤ scrB'.length := by
        rw [hnb_bv, hlenB']; exact le_refl _
      apply bn_bitwise_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ lcnfHeap objs ⋆ R)
        hop_sub hna_leA' hnb_leB' hout_bw (sep_ac hm2)
      intro outXs' m3
      dsimp only
      intro hlenOut htnOut hvalOut hm3
      have hvalA' : limbsVal (scrA'.take (BitVec.ofNat 64 (limbLenNat aVal)).toNat) = aVal := by
        rwa [hna_bv]
      have hvalB' : limbsVal (scrB'.take (BitVec.ofNat 64 (limbLenNat bVal)).toNat) = bVal := by
        rwa [hnb_bv]
      rw [hvalA', hvalB'] at htnOut hvalOut
      try rw [hvalA', hvalB']
      have hres_eq : (if op - 10#64 = 0#64 then Nat.land aVal bVal
          else if op - 10#64 = 1#64 then Nat.lor aVal bVal else Nat.xor aVal bVal) =
          (if op.toNat = 10 then Nat.land aVal bVal
          else if op.toNat = 11 then Nat.lor aVal bVal else Nat.xor aVal bVal) := by
        rcases (by simpa using hop : op.toNat = 10 ∨ op.toNat = 11 ∨ op.toNat = 12) with h | h | h
        · have heq : op = 10#64 := BitVec.eq_of_toNat_eq (by simpa using h)
          subst heq; simp
        · have heq : op = 11#64 := BitVec.eq_of_toNat_eq (by simpa using h)
          subst heq; simp
        · have heq : op = 12#64 := BitVec.eq_of_toNat_eq (by simpa using h)
          subst heq; simp
      rw [hres_eq] at htnOut hvalOut ⊢
      let resVal : Nat := if op.toNat = 10 then Nat.land aVal bVal
        else if op.toNat = 11 then Nat.lor aVal bVal else Nat.xor aVal bVal
      have hres_max : limbLenNat resVal ≤ mpzMaxLimbs := by
        by_cases h0 : resVal = 0
        · simp [h0, limbLenNat, mpzMaxLimbs]
        · have hle_max : limbLenNat resVal ≤ max (limbLenNat aVal) (limbLenNat bVal) := by
            have ha_pow := limbLenNat_lt_pow (n := aVal)
            have hb_pow := limbLenNat_lt_pow (n := bVal)
            have hk_pow : resVal < 2 ^ (64 * max (limbLenNat aVal) (limbLenNat bVal)) := by
              have ha_le := Nat.lt_of_lt_of_le ha_pow (Nat.pow_le_pow_right (by decide)
                (Nat.mul_le_mul_left 64 (Nat.le_max_left (limbLenNat aVal) (limbLenNat bVal))))
              have hb_le := Nat.lt_of_lt_of_le hb_pow (Nat.pow_le_pow_right (by decide)
                (Nat.mul_le_mul_left 64 (Nat.le_max_right (limbLenNat aVal) (limbLenNat bVal))))
              have hlt_bit : ∀ {n x y : Nat}, x < 2 ^ n → y < 2 ^ n →
                  Nat.land x y < 2 ^ n ∧ Nat.lor x y < 2 ^ n ∧ Nat.xor x y < 2 ^ n := by
                intro n x y hx hy
                refine ⟨Nat.lt_of_le_of_lt Nat.and_le_left hx, ?_, ?_⟩
                · exact Nat.or_lt_two_pow hx hy
                · exact Nat.xor_lt_two_pow hx hy
              have ⟨h1, h2, h3⟩ := hlt_bit ha_le hb_le
              dsimp only [resVal]
              split
              · exact h1
              · split
                · exact h2
                · exact h3
            conv => lhs; unfold limbLenNat
            simp only [h0, ↓reduceIte]
            have hdiv := (Nat.div_lt_iff_lt_mul (by decide : 0 < 64)).mpr
              ((Nat.log2_lt h0).mpr (by rw [Nat.mul_comm]; exact hk_pow))
            omega
          omega
      have htn_bv : (BitVec.ofNat 64 (limbLenNat resVal)).toNat = limbLenNat resVal := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hres_max; omega)]
      have hvalOut' : limbsVal (outXs'.take (BitVec.ofNat 64 (limbLenNat resVal)).toNat) = resVal :=
        by
        rwa [htn_bv]
      have htrim : trimLenLoop outXs' (BitVec.ofNat 64 (limbLenNat resVal)).toNat =
        limbLenNat resVal := by
        rw [htn_bv, ← limbLenNat_trimLenLoop (by rw [hlenOut]; exact htnOut), hvalOut]
      try rw [Nat.mul_comm (limbLenNat aVal) 8] at hm3
      apply bn_nat_from_limbs_call_wp (R := cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrA' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆ R)
        (by rw [htn_bv, hlenOut]; exact htnOut)
        (by rw [htn_bv]; exact hres_max) hb48
        (fun hge => by rw [hvalOut'] at hge; rw [htrim]; exact halloc hge)
        (by sep_use hm3)
      intro p st' objs' m4 hmst hrem hb' hrep hsm hbg hm4
      c0_step
      have hlenTot : (scrA' ++ scrB' ++ outXs').length = scrLimbs.length := by
        rw [List.length_append, List.length_append, hlenA', hlenB', hlenOut, List.length_drop]
        omega
      have hm4' : (bigNumRtInv rt st' scr (scrA' ++ scrB' ++ outXs') ⋆ lcnfHeap objs' ⋆ R) m4 := by
        dsimp only [bigNumRtInv]
        have hlenAB : (scrA' ++ scrB').length = limbLenNat aVal + limbLenNat bVal := by
          simp [hlenA', hlenB']
        rw [hlenTot, array64_append, hlenAB, array64_append, hlenA']
        sep_use hm4
      rw [hvalOut'] at hrep hsm hbg
      refine hQ p st' (scrA' ++ scrB' ++ outXs') objs' m4 hmst hrem
        (BigNumRtWf.with_state_len hwf' hb' hlenTot) ?_ hm4'
      dsimp only [natBitsPost]
      simp only [hnot13, hnot14, hnot19, ↓reduceIte]
      refine ⟨bVal, hb, ?_, ?_⟩
      · intro o ho
        by_cases hs : resVal < 2 ^ 63
        · rw [hsm hs]; exact ho
        · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
          exact List.mem_cons_of_mem _ ho
      · rcases (by simpa using hop : op.toNat = 10 ∨ op.toNat = 11 ∨ op.toNat = 12) with h | h | h
        · simp [h, resVal] at hrep ⊢; exact hrep
        · simp [h, resVal] at hrep ⊢; exact hrep
        · simp [h, resVal] at hrep ⊢; exact hrep
    · intro Js hJs
      c0_let_simp
      by_cases hgt : (BitVec.ofNat 64 (limbLenNat bVal)).ult (BitVec.ofNat 64 (limbLenNat aVal)) =
        true
      · apply wp_jnz_true hgt
        rw [wp_jump]
        have hmax_eq : max (limbLenNat aVal) (limbLenNat bVal) = limbLenNat aVal := by
          have : (BitVec.ofNat 64 (limbLenNat bVal)).toNat <
            (BitVec.ofNat 64 (limbLenNat aVal)).toNat :=
            of_decide_eq_true hgt
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt,
            Nat.mod_eq_of_lt hnb_lt] at this
          omega
        rw [hmax_eq] at hJs; exact hJs (BitVec.ofNat 64 (limbLenNat aVal), ()) m ⟨rfl, rfl⟩
      · have hgtf : (BitVec.ofNat 64 (limbLenNat bVal)).ult (BitVec.ofNat 64 (limbLenNat aVal)) =
        false :=
          Bool.eq_false_iff.mpr hgt
        apply wp_jnz_false hgtf
        rw [wp_jump]
        have hmax_eq : max (limbLenNat aVal) (limbLenNat bVal) = limbLenNat bVal := by
          have hnot : ¬ (BitVec.ofNat 64 (limbLenNat bVal)).toNat <
            (BitVec.ofNat 64 (limbLenNat aVal)).toNat :=
            fun h => hgt (decide_eq_true h)
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt,
            Nat.mod_eq_of_lt hnb_lt] at hnot
          omega
        rw [hmax_eq] at hJs; exact hJs (BitVec.ofNat 64 (limbLenNat bVal), ()) m ⟨rfl, rfl⟩

theorem lcnf_nat_bits_wp (xs : Tup Val [i64, i64, i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (h : lcnfNatBitsSpec xs m Q X) :
    Func.wp rtR1Env lcnf_nat_bits.body xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, aVal, R, hwf, ha_spec, hok, hm, hQ⟩
  dsimp only [Func.wp, lcnf_nat_bits, lcnf_nat_bits_body]
  c0_let_simp
  by_cases h13 : op = 13#64
  · subst h13
    have ha : natRep a aVal objs := by simpa using ha_spec
    apply wp_jnz_true (by decide)
    exact lcnf_nat_bits_tonat_wp rt a b aVal st scr scrLimbs objs R m Q X hwf ha hm hQ
  · have h13n : op.toNat ≠ 13 := fun h => h13 (BitVec.eq_of_toNat_eq (by simpa using h))
    apply wp_jnz_false (beq_false_of_ne h13)
    c0_let_simp
    by_cases h14 : op = 14#64
    · subst h14
      have ha_val : aVal = a.toNat := by simpa using ha_spec
      subst ha_val
      apply wp_jnz_true (by decide)
      have hok' := hok
      rw [show (14#64 : BitVec 64).toNat = 14 from rfl] at hok'
      dsimp only [natBitsOk] at hok'
      simp only [show (14 : Nat) ≠ 13 by decide, ↓reduceIte] at hok'
      exact lcnf_nat_bits_ofnat_wp rt a st scr scrLimbs objs R m Q X hwf hok' hm hQ
    · have h14n : op.toNat ≠ 14 := fun h => h14 (BitVec.eq_of_toNat_eq (by simpa using h))
      have ha : natRep a aVal objs := by simpa [h14n] using ha_spec
      apply wp_jnz_false (beq_false_of_ne h14)
      c0_let_simp
      by_cases h19 : op = 19#64
      · subst h19
        apply wp_jnz_true (by decide)
        exact lcnf_nat_bits_log2_wp rt a aVal st scr scrLimbs objs R m Q X hwf ha hm hQ
      · have h19n : op.toNat ≠ 19 := fun h => h19 (BitVec.eq_of_toNat_eq (by simpa using h))
        apply wp_jnz_false (beq_false_of_ne h19)
        c0_let_simp
        by_cases h9 : op = 9#64
        · subst h9
          have hb : ∃ bVal, natRep b bVal objs := by
            have hok' := hok
            dsimp only [natBitsOk] at hok'
            simp only [h13n, h14n, h19n, ↓reduceIte] at hok'
            exact ⟨hok'.choose, hok'.choose_spec.1⟩
          rcases hb with ⟨bVal, hb⟩
          apply wp_jnz_true (by decide)
          exact lcnf_nat_bits_shr_wp rt a b aVal bVal st scr scrLimbs objs R m Q X hwf ha hb hok hm
            hQ
        · have h9n : op.toNat ≠ 9 := fun h => h9 (BitVec.eq_of_toNat_eq (by simpa using h))
          apply wp_jnz_false (beq_false_of_ne h9)
          c0_let_simp
          by_cases h15 : op = 15#64
          · subst h15
            apply wp_jnz_true (by decide)
            exact lcnf_nat_bits_shl_wp rt a b aVal st scr scrLimbs objs R m Q X hwf ha hok hm hQ
          · have h15n : op.toNat ≠ 15 := fun h => h15 (BitVec.eq_of_toNat_eq (by simpa using h))
            have hop_bw : op.toNat ∈ [10, 11, 12] := by
              have hok' := hok
              dsimp only [natBitsOk] at hok'
              simp only [h13n, h14n, h19n, ↓reduceIte] at hok'
              rcases hok' with ⟨bVal, _, hok''⟩
              simp only [h9n, h15n, ↓reduceIte] at hok''
              split at hok''
              · assumption
              · exact False.elim hok''
            apply wp_jnz_false (beq_false_of_ne h15)
            exact lcnf_nat_bits_bw_wp rt op a b aVal st scr scrLimbs objs R m Q X hwf ha hop_bw hok
              hm hQ

private theorem lcnf_nat_bits_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt op a b : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal : Nat} {R : Mem 64 → Prop}
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (ha : if op.toNat = 14 then aVal = a.toNat else natRep a aVal objs)
    (hok : natBitsOk op.toNat aVal b objs scrLimbs.length st)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natBitsPost op.toNat aVal b res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "lcnf_nat_bits"
        (Arg.var rt, Arg.var op, Arg.var a, Arg.var b, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_lcnf_nat_bits
  exact ⟨st, scr, scrLimbs, objs, aVal, R, hwf, ha, hok, hm, hk⟩

theorem lcnf_nat_slow_wp (xs : Tup Val [i64, i64, i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (h : lcnfNatSlowSpec xs m Q X) :
    Func.wp rtR1Env lcnf_nat_slow.body xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, R, hwf, hm, hbody⟩
  dsimp only [Func.wp, lcnf_nat_slow, lcnf_nat_slow_body]
  apply wp_join_group
    (fun _ m' => op.toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17] ∧ m' = m ∧
      ∃ aVal bVal, natRep a aVal objs ∧ (op.toNat = 17 ∨ natRep b bVal objs) ∧
        natArithOk op.toNat aVal bVal scrLimbs.length st ∧
        ∀ res st' scrLimbs' objs' m'',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
          natArithPost op.toNat aVal bVal res objs objs' →
          (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m'' → Q (res, ()) m'')
  · intro _ _ m' ⟨_, hm', aVal, bVal, ha, hb, hok, hQ⟩
    rw [hm']
    simp only [Blocks.get]
    apply lcnf_nat_arith_call_wp hwf ha hb hok hm
    intro res st' scrLimbs' objs' m'' hmst hrem hwf' hpost hm''
    c0_step
    exact hQ res st' scrLimbs' objs' m'' hmst hrem hwf' hpost hm''
  · intro Js_arith hJs_arith
    apply wp_join_group
      (fun _ m' => op.toNat ∈ [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∧
        op.toNat ∉ [1, 2, 3, 4, 5, 6, 7, 8] ∧
        m' = m)
    · intro _ _ m' ⟨hop_hi, hop_n18, hm'⟩
      rw [hm']
      simp only [Blocks.get]
      c0_let_simp
      by_cases h17 : op = 17#64
      · subst h17
        apply wp_jnz_true (by decide)
        rw [wp_jump]
        rw [show (17#64 : BitVec 64).toNat = 17 from rfl] at hJs_arith hbody
        simp only [show (17 : Nat) ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17] by decide, ↓reduceIte] at hbody
        exact hJs_arith () m ⟨by decide, rfl, by simpa using hbody⟩
      · have h17n : op.toNat ≠ 17 := fun h => h17 (BitVec.eq_of_toNat_eq (by simpa using h))
        apply wp_jnz_false (beq_false_of_ne h17)
        have hop_n_arith : ¬ op.toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17] := by
          intro hm17; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm17 hop_n18
          omega
        simp only [hop_n_arith, ↓reduceIte] at hbody
        apply wp_join_group
          (fun _ m' => op.toNat ∈ [9, 10, 11, 12, 13, 14, 15, 19] ∧ m' = m ∧
            ∃ aVal, (if op.toNat = 14 then aVal = a.toNat else natRep a aVal objs) ∧
              natBitsOk op.toNat aVal b objs scrLimbs.length st ∧
              ∀ res st' scrLimbs' objs' m'',
                st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
                natBitsPost op.toNat aVal b res objs objs' →
                (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m'' → Q (res, ()) m'')
        · intro _ _ m'' ⟨_, hm'', aVal, ha, hok, hQ⟩
          rw [hm'']
          simp only [Blocks.get]
          apply lcnf_nat_bits_call_wp hwf ha hok hm
          intro res st' scrLimbs' objs' m3 hmst hrem hwf' hpost hm3
          c0_step
          exact hQ res st' scrLimbs' objs' m3 hmst hrem hwf' hpost hm3
        · intro Js_bits hJs_bits
          apply wp_join_group
            (fun _ m' => op.toNat ∈ [16, 18, 19] ∧ m' = m)
          · intro _ _ m'' ⟨hop_161819, hm''⟩
            rw [hm'']
            simp only [Blocks.get]
            c0_let_simp
            by_cases h19 : op = 19#64
            · subst h19
              apply wp_jnz_true (by decide)
              rw [wp_jump]
              rw [show (19#64 : BitVec 64).toNat = 19 from rfl] at hbody
              simp only [show (19 : Nat) ∈ [9, 10, 11, 12, 13, 14, 15, 19] by decide,
                ↓reduceIte] at hbody
              exact hJs_bits () m ⟨by decide, rfl, hbody⟩
            · have h19n : op.toNat ≠ 19 := fun h => h19 (BitVec.eq_of_toNat_eq (by simpa using h))
              have hop_n_bits : ¬ op.toNat ∈ [9, 10, 11, 12, 13, 14, 15, 19] := by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hop_161819 ⊢
                rcases hop_161819 with h | h | h <;> omega
              simp only [hop_n_bits, ↓reduceIte] at hbody
              apply wp_jnz_false (beq_false_of_ne h19)
              c0_let_simp
              by_cases h16 : op = 16#64
              · subst h16
                rw [show (16#64 : BitVec 64).toNat = 16 from rfl] at hbody
                simp only [↓reduceIte] at hbody
                rcases hbody with ⟨aVal, bVal, ha, hb, hok, hQ⟩
                apply wp_jnz_true (by decide)
                apply bn_nat_pow_call_wp hwf ha hb hok hm
                intro res st' scrLimbs' objs' m3 hmst hrem hwf' hrep _ hpres hm3
                c0_step
                exact hQ res st' scrLimbs' objs' m3 hmst hrem hwf' hrep hpres hm3
              · have h16n : op.toNat ≠ 16 := fun h => h16 (BitVec.eq_of_toNat_eq (by simpa using h))
                have h18n : op.toNat = 18 := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop_161819
                  omega
                have h18 : op = 18#64 := BitVec.eq_of_toNat_eq (by simpa using h18n)
                subst h18
                rw [show (18#64 : BitVec 64).toNat = 18 from rfl] at hbody
                simp only [show (18 : Nat) ≠ 16 by decide, ↓reduceIte] at hbody
                rcases hbody with ⟨aVal, bVal, ha, hb, hok, hQ⟩
                apply wp_jnz_false (beq_false_of_ne h16)
                c0_let_simp
                apply wp_jnz_true (by decide)
                apply bn_nat_gcd_call_wp hwf ha hb hok hm
                intro res st' scrLimbs' objs' m3 hmst hrem hwf' hrep hpres hm3
                c0_step
                exact hQ res st' scrLimbs' objs' m3 hmst hrem hwf' hrep hpres hm3
          · intro Js_hi hJs_hi
            c0_let_simp
            by_cases hge9 : 9 ≤ op.toNat
            · apply wp_jnz_true
                (by rw [BitVec.ule];
                    exact decide_eq_true (hge9 : (9#64 : BitVec 64).toNat ≤ op.toNat))
              c0_let_simp
              by_cases hle15 : op.toNat ≤ 15
              · apply wp_jnz_true
                  (by rw [BitVec.ule];
                      exact decide_eq_true (hle15 : op.toNat ≤ (15#64 : BitVec 64).toNat))
                rw [wp_jump]
                have hop_b : op.toNat ∈ [9, 10, 11, 12, 13, 14, 15, 19] := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
                simp only [hop_b, ↓reduceIte] at hbody
                exact hJs_bits () m ⟨hop_b, rfl, hbody⟩
              · apply wp_jnz_false
                  (by rw [BitVec.ule, decide_eq_false_iff_not]
                      exact (hle15 : ¬ op.toNat ≤ (15#64 : BitVec 64).toNat))
                rw [wp_jump]
                have hop16 : op.toNat ∈ [16, 18, 19] := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop_hi ⊢; omega
                exact hJs_hi () m ⟨hop16, rfl⟩
            · apply wp_jnz_false
                (by rw [BitVec.ule, decide_eq_false_iff_not]
                    exact (hge9 : ¬ (9#64 : BitVec 64).toNat ≤ op.toNat))
              rw [wp_jump]
              have hop16 : op.toNat ∈ [16, 18, 19] := by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hop_hi ⊢; omega
              exact hJs_hi () m ⟨hop16, rfl⟩
    · intro Js_lo hJs_lo
      c0_let_simp
      by_cases h18 : op.toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8]
      · have hge1 : 1 ≤ op.toNat := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h18; omega
        have hle8 : op.toNat ≤ 8 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h18; omega
        apply wp_jnz_true
          (by rw [BitVec.ule]; exact decide_eq_true (hge1 : (1#64 : BitVec 64).toNat ≤ op.toNat))
        c0_let_simp
        apply wp_jnz_true
          (by rw [BitVec.ule]; exact decide_eq_true (hle8 : op.toNat ≤ (8#64 : BitVec 64).toNat))
        rw [wp_jump]
        have h17 : op.toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h18 ⊢; omega
        simp only [h17, ↓reduceIte] at hbody
        exact hJs_arith () m ⟨h17, rfl, hbody⟩
      · have hop_hi : op.toNat ∈ [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] := by
          split at hbody <;> rename_i h1
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h18 ⊢; omega
          · split at hbody <;> rename_i h2
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2 ⊢; omega
            · split at hbody <;> rename_i h3
              · simp [h3]
              · split at hbody <;> rename_i h4
                · simp [h4]
                · exact False.elim hbody
        by_cases hge1 : 1 ≤ op.toNat
        · have hgt8 : 8 < op.toNat := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hop_hi; omega
          apply wp_jnz_true
            (by rw [BitVec.ule]; exact decide_eq_true (hge1 : (1#64 : BitVec 64).toNat ≤ op.toNat))
          c0_let_simp
          apply wp_jnz_false
            (by rw [BitVec.ule, decide_eq_false_iff_not]
                exact (Nat.not_le_of_gt hgt8 : ¬ op.toNat ≤ (8#64 : BitVec 64).toNat))
          rw [wp_jump]; exact hJs_lo () m ⟨hop_hi, h18, rfl⟩
        · exfalso
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hop_hi; omega


end LeanQbe.T.LeanLCNF
