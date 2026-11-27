module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof3
import all Kraken.Mem
import all Kraken.Separation

/-!
# Top-Level `Nat` Arithmetic Dispatcher (`lcnf_nat_arith_wp`, `Milestone R1`, Part 4)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

local macro "sep_ac" : tactic =>
  `(tactic| exact sep_cast_ac (by assumption) (by ac_rfl))

local macro "sep_use " t:term : tactic =>
  `(tactic| exact sep_cast_ac $t (by ac_rfl))

/-! ## 4. Top-Level `Nat` Dispatchers (`lcnf_nat_arith`, `lcnf_nat_bits`, `lcnf_nat_slow`) -/

theorem bn_nat_pow_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt a b : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal bVal : Nat} {R : Mem 64 → Prop}
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (ha : natRep a aVal objs) (hb : natRep b bVal objs)
    (hok : natPowOk aVal bVal scrLimbs.length st)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natRep res (aVal ^ bVal) objs' →
      (∀ o ∈ objs, o.addr = a ∨ o.addr = b → o ∈ objs') →
      (∀ o ∈ objs, o.addr ≠ res → o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_nat_pow"
        (Arg.var rt, Arg.var a, Arg.var b, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_nat_pow
  exact ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb, hok, hm, hk⟩

theorem bn_nat_gcd_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt a b : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal bVal : Nat} {R : Mem 64 → Prop}
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (ha : natRep a aVal objs) (hb : natRep b bVal objs)
    (hok : natGcdOk aVal bVal scrLimbs.length st)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natRep res (Nat.gcd aVal bVal) objs' →
      (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_nat_gcd"
        (Arg.var rt, Arg.var a, Arg.var b, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_nat_gcd
  exact ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb, hok, hm, hk⟩

theorem natRep_and_one_eq_zero_iff {a : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (h : natRep a n objs) : (a &&& 1#64) = 0#64 ↔ 2 ^ 63 ≤ n := by
  dsimp only [natRep] at h
  by_cases hn : n < 2 ^ 63
  · simp only [hn, ↓reduceIte] at h
    subst h
    have heq : BitVec.ofNat 64 (2 * n + 1) &&& 1#64 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp [Nat.and_two_pow_sub_one_eq_mod (2 * n + 1) 1]
    constructor <;> intro h0
    · rw [heq] at h0; exact absurd h0 (by decide)
    · omega
  · simp only [hn, ↓reduceIte] at h
    exact ⟨fun _ => by omega, fun _ => h.1⟩

private theorem natRep_small_shr1 {a : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (h : natRep a n objs) (hn : n < 2 ^ 63) : a >>> 1#64 = BitVec.ofNat 64 n := by
  dsimp only [natRep] at h
  simp only [hn, ↓reduceIte] at h
  subst h
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]
  omega

theorem natRep_small_shr1_nat {a : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (h : natRep a n objs) (hn : n < 2 ^ 63) : a >>> (1 : Nat) = BitVec.ofNat 64 n :=
  natRep_small_shr1 h hn

theorem mpzMeta_arrSize_nat (o : LcnfObj) (hc : o.cap < 2 ^ 32) (ha : o.arrSize < 2 ^ 32) :
    o.mpzMeta >>> (32 : Nat) = BitVec.ofNat 64 o.arrSize :=
  LcnfObj.mpzMeta_arrSize o hc ha

theorem bv64_encodeNat {n : Nat} (hn : n < 2 ^ 63) :
    ((BitVec.ofNat 64 n <<< 1#64) ||| 1#64) = BitVec.ofNat 64 (2 * n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  have hshl : (BitVec.ofNat 64 n <<< (1#64 : BitVec 64)).toNat = 2 * n := by
    simp [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : n * 2 < 2 ^ 64)]
    omega
  rw [hshl, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.mod_eq_of_lt
    (by omega : 2 * n + 1 < 2 ^ 64)]
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  | succ k =>
    have hpow : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
    have h1 : (1 : Nat).testBit (k + 1) = false := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hpow]
    have h2 : (2 * n).testBit (k + 1) = n.testBit k := by rw [Nat.testBit_succ]; simp
    have h3 : (2 * n + 1).testBit (k + 1) = n.testBit k := by
      rw [Nat.testBit_succ, show (2 * n + 1) / 2 = n by omega]
    simp [h1, h2, h3]

private theorem cmpResult64_eq0_iff (x y : Nat) : (cmpResult64 x y == 0#64) = true ↔ x = y := by
  dsimp only [cmpResult64]
  by_cases h1 : x < y
  · simp [h1]; omega
  · by_cases h2 : x > y
    · simp [h1, h2]; omega
    · simp [h1, h2]; omega

private theorem cmpResult64_slt0_iff (x y : Nat) : (cmpResult64 x y).slt 0#64 = true ↔ x < y := by
  dsimp only [cmpResult64]
  by_cases h1 : x < y
  · simp [h1]
  · by_cases h2 : x > y
    · simp [h1, h2]
    · simp [h1, h2]

private theorem cmpResult64_sle0_iff (x y : Nat) : (cmpResult64 x y).sle 0#64 = true ↔ x ≤ y := by
  dsimp only [cmpResult64]
  by_cases h1 : x < y
  · simp [h1]; omega
  · by_cases h2 : x > y
    · simp [h1, h2]
    · simp [h1, h2]; omega

theorem bv64_mul8_of_lt (k : Nat) (hk : 8 * k < 2 ^ 64) :
    (8 : BitVec 64) * BitVec.ofNat 64 k = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]

private theorem lcnf_nat_arith_pred_wp
    (rt a : BitVec 64) (aVal bVal : Nat) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hwf : BigNumRtWf rt st scr scrLimbs) (ha : natRep a aVal objs)
    (hok : natArithOk 17 aVal bVal scrLimbs.length st)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natArithPost 17 aVal bVal res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var a, Arg.imm 1, ()) } fun p_2 =>
        Expr.let_
          { sig := [i64, i64],
            code := OpCode.cmp CmpOp.ne i64 Ty.bool,
            args := (Arg.var p_2.fst, Arg.imm 0, ()) } fun p_3 =>
          Expr.jnz (Arg.var p_3.fst)
            (Expr.let_
              { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_4 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var a, Arg.var p_4.fst,
                  ()) }
                fun p =>
                Expr.let_
                  { sig := [i64, i64],
                    code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                    args := (Arg.var p.fst, Arg.imm 0, ()) } fun p_5 =>
                  Expr.jnz (Arg.var p_5.fst) (Expr.ret (Arg.imm 1, ()))
                    (Expr.let_
                      { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var p.fst,
                        Arg.imm 1, ()) } fun p =>
                      Expr.let_
                        { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1,
                          ()) } fun p_6 =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.var p.fst,
                            Arg.var p_6.fst, ()) }
                          fun p =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.or i64, args := (Arg.var p.fst,
                              Arg.imm 1, ()) }
                            fun p => Expr.ret (Arg.var p.fst, ())))
            (Expr.call (as := [i64]) (bs := [i64]) "bn_nat_len" (Arg.var a, ()) fun p_4 =>
              Expr.group (sig := [[]])
                (fun _Js =>
                  Blocks.cons
                    (fun _p_5 =>
                      Expr.let_
                        { sig := [i64, i64],
                          code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                          args := (Arg.var p_4.fst, Arg.imm 0, ()) } fun p_6 =>
                        Expr.jnz (Arg.var p_6.fst) (Expr.ret (Arg.imm 1, ()))
                          (Expr.exit (as := [i64, i64]) "lcnf_panic" (Arg.var rt, Arg.imm 2, ())))
                    Blocks.nil)
                fun Js =>
                Expr.let_
                  { sig := [i64, i64],
                    code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                    args := (Arg.var p_4.fst, Arg.imm 0, ()) } fun p_5 =>
                  Expr.jnz (Arg.var p_5.fst) (Expr.jump Js.fst ())
                    (Expr.let_
                      { sig := [i64, i64],
                        code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                        args := (Arg.var p_4.fst, Arg.imm 33554429, ()) } fun p_6 =>
                      Expr.jnz (Arg.var p_6.fst) (Expr.jump Js.fst ())
                        (Expr.let_
                          { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.imm 2,
                            Arg.var p_4.fst, ()) }
                          fun p_7 =>
                          Expr.call (as := [i64, i64]) (bs := [i64]) "bn_require_scratch"
                            (Arg.var rt, Arg.var p_7.fst, ()) fun p_8 =>
                            Expr.call (as := [i64, i64]) (bs := [i64]) "bn_load_nat"
                              (Arg.var a, Arg.var p_8.fst, ()) fun p_9 =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.mul i64,
                                  args := (Arg.imm 8, Arg.var p_9.fst, ()) } fun p_10 =>
                                Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var p_8.fst, Arg.var p_10.fst, ()) } fun p_11 =>
                                  Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_sub_one"
                                    (Arg.var p_8.fst, Arg.var p_9.fst, Arg.var p_11.fst,
                                      ()) fun p_12 =>
                                    Expr.let_
                                      { sig := [i64, i64], code := OpCode.mul i64,
                                        args := (Arg.imm 8, Arg.var p_9.fst, ()) } fun p_13 =>
                                      Expr.let_
                                        { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var p_8.fst, Arg.var p_13.fst,
                                            ()) } fun p_14 =>
                                        Expr.call (as := [i64, i64,
                                          i64]) (bs := [i64]) "bn_nat_from_limbs"
                                          (Arg.var rt, Arg.var p_14.fst, Arg.var p_12.fst,
                                            ()) fun p =>
                                          Expr.ret (Arg.var p.fst, ()))))) m := by
  c0_let_simp
  by_cases ha_sm : aVal < 2 ^ 63
  · have hbit0 : (a &&& 1#64) ≠ 0#64 := by
      intro hz
      have := (natRep_and_one_eq_zero_iff ha).mp hz
      omega
    apply wp_jnz_true (by simp [hbit0])
    c0_let_simp
    rw [natRep_small_shr1_nat ha ha_sm]
    by_cases ha0 : aVal = 0
    · subst ha0
      apply wp_jnz_true (by decide)
      c0_step
      refine hQ 1#64 st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
      dsimp only [natArithPost, natArithRes, natRep]
      exact ⟨rfl, fun o ho => ho⟩
    · have hne0 : (BitVec.ofNat 64 aVal == 0#64) = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        have := BitVec.toNat_eq.mp (beq_iff_eq.mp ht)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
          (by omega), show (0#64 : BitVec 64).toNat = 0 from rfl] at this
        omega
      apply wp_jnz_false hne0
      c0_let_simp
      have hsub : BitVec.ofNat 64 aVal - (1 : BitVec 64) = BitVec.ofNat 64 (aVal - 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub_of_le]
        · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        · change (1 : BitVec 64).toNat ≤ (BitVec.ofNat 64 aVal).toNat
          rw [show (1 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
            (by omega)]
          omega
      have henc : ((BitVec.ofNat 64 (aVal - 1) <<< (1 : Nat)) ||| (1 : BitVec 64)) =
          BitVec.ofNat 64 (2 * (aVal - 1) + 1) := bv64_encodeNat (by omega)
      rw [hsub, henc]
      refine hQ _ st scrLimbs objs m (preservesMeta_refl _) (Nat.le_refl _) hwf ?_ hm
      dsimp only [natArithPost, natArithRes]
      refine ⟨?_, fun o ho => ho⟩
      simp [natRep, show aVal - 1 < 2 ^ 63 by omega]
  · have hbit0 : (a &&& 1#64) = 0#64 := (natRep_and_one_eq_zero_iff ha).mpr (by omega)
    dsimp only [natArithOk] at hok
    simp only [↓reduceIte] at hok
    rcases hok with hlt | ⟨hscr_need, halloc⟩
    · exact absurd hlt ha_sm
    apply wp_jnz_false (by simp [hbit0])
    rcases hwf with ⟨hb, hrt64, hscr0, hscra, hscrlen, hscr64⟩
    have hna_max : limbLenNat aVal ≤ mpzMaxLimbs := limbLenNat_le_max_of_natRep ha
    have hna_pos : 0 < limbLenNat aVal := limbLenNat_pos_iff.mpr (by omega)
    have hwf' : BigNumRtWf rt st scr scrLimbs := ⟨hb, hrt64, hscr0, hscra, hscrlen, hscr64⟩
    apply bn_nat_len_rt_call_wp ha hm
    apply wp_join_group (fun _ _ => False)
    · intro _ _ _ hfalse; exact False.elim hfalse
    · intro Js hJs
      c0_let_simp
      have hna0 : (BitVec.ofNat 64 (limbLenNat aVal) == 0#64) = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        have := BitVec.toNat_eq.mp (beq_iff_eq.mp ht)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hna_max; omega),
          show (0#64 : BitVec 64).toNat = 0 from rfl] at this
        omega
      apply wp_jnz_false hna0
      have hugt : (33554429#64 : BitVec 64).ult (BitVec.ofNat 64 (limbLenNat aVal)) = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        have : (33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 (limbLenNat aVal)).toNat :=
          of_decide_eq_true ht
        rw [show (33554429#64 : BitVec 64).toNat = 33554429 from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hna_max; omega)] at this
        unfold mpzMaxLimbs at hna_max; omega
      apply wp_jnz_false hugt
      c0_let_simp
      have hneed_nat : ((2 : BitVec 64) * BitVec.ofNat 64 (limbLenNat aVal)).toNat =
        2 * limbLenNat aVal := by
        rw [BitVec.toNat_mul, show (2 : BitVec 64).toNat = 2 from rfl, BitVec.toNat_ofNat]
        unfold mpzMaxLimbs at hna_max; omega
      apply bn_require_scratch_rt_call_wp hwf' (by rw [hneed_nat]; exact hscr_need) hm
      have hna_le_scr : limbLenNat aVal ≤ scrLimbs.length := by omega
      have hm_split := hm
      dsimp only [bigNumRtInv] at hm_split
      rw [array64_split_len (k := limbLenNat aVal) hna_le_scr] at hm_split
      apply bn_load_nat_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) (scrLimbs.drop (limbLenNat aVal)) ⋆ R)
        ha (by rw [List.length_take_of_le hna_le_scr]; exact le_refl _) (by sep_use hm_split)
      intro scrA' m1 hlenA hvalA _ hm1
      c0_let_simp
      have hna_lt64 : limbLenNat aVal < 2 ^ 64 := by unfold mpzMaxLimbs at hna_max; omega
      have hna_bv : (BitVec.ofNat 64 (limbLenNat aVal)).toNat = limbLenNat aVal := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt64]
      have hna_leA' : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤ scrA'.length := by
        rw [hna_bv, hlenA, List.length_take_of_le hna_le_scr]; exact le_refl _
      have hna_leOut : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤
        (scrLimbs.drop (limbLenNat aVal)).length := by
        rw [List.length_drop, hna_bv]; omega
      have haVal_take : limbsVal (scrA'.take (BitVec.ofNat 64 (limbLenNat aVal)).toNat) = aVal := by
        rwa [hna_bv]
      have h8mul := bv64_mul8_of_lt (limbLenNat aVal) (by unfold mpzMaxLimbs at hna_max; omega)
      rw [h8mul]
      apply bn_sub_one_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ lcnfHeap objs ⋆ R)
        hna_leA' hna_leOut (Or.inr (by rw [haVal_take]; omega)) (by sep_use hm1)
      intro outXs' m2
      dsimp only
      intro hlenOut htlOut hvalOut hm2
      c0_let_simp
      rw [haVal_take] at htlOut hvalOut ⊢
      have htl_max : limbLenNat (aVal - 1) ≤ mpzMaxLimbs :=
        Nat.le_trans (limbLenNat_mono (Nat.sub_le aVal 1)) hna_max
      have htl_bv : (BitVec.ofNat 64 (limbLenNat (aVal - 1))).toNat = limbLenNat (aVal - 1) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at htl_max; omega)]
      have hvalOut' : limbsVal (outXs'.take (BitVec.ofNat 64 (limbLenNat (aVal - 1))).toNat) =
        aVal - 1 := by
        rwa [htl_bv]
      have htrimOut :
          trimLenLoop outXs' (BitVec.ofNat 64 (limbLenNat (aVal - 1))).toNat =
            limbLenNat (aVal - 1) := by
        rw [htl_bv, ← limbLenNat_trimLenLoop (by rw [hlenOut]; exact htlOut), hvalOut]
      have htl_leOut : (BitVec.ofNat 64 (limbLenNat (aVal - 1))).toNat ≤ outXs'.length := by
        rw [htl_bv, hlenOut]; exact htlOut
      have h8mul_r : BitVec.ofNat 64 (limbLenNat aVal) * (8 : BitVec 64) =
          BitVec.ofNat 64 (limbLenNat aVal * 8) := by
        rw [BitVec.mul_comm, h8mul, Nat.mul_comm]
      try rw [Nat.mul_comm 8 (limbLenNat aVal)] at hm2
      try rw [← h8mul_r] at hm2
      apply bn_nat_from_limbs_call_wp (R := cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrA' ⋆ R)
        htl_leOut (by rw [htl_bv]; exact htl_max) hb
        (fun hge => by rw [hvalOut'] at hge; rw [htrimOut]; exact halloc hge)
        (by sep_use hm2)
      intro p st' objs' m3 hmst hrem hb' hrep hsm hbg hm3
      c0_step
      have hlenA' : scrA'.length = limbLenNat aVal := by
        rw [hlenA, List.length_take_of_le hna_le_scr]
      have hlenTot : (scrA' ++ outXs').length = scrLimbs.length := by
        rw [List.length_append, hlenA', hlenOut, List.length_drop]; omega
      have hm3' : (bigNumRtInv rt st' scr (scrA' ++ outXs') ⋆ lcnfHeap objs' ⋆ R) m3 := by
        dsimp only [bigNumRtInv]
        rw [h8mul, Nat.mul_comm 8 (limbLenNat aVal)] at hm3
        rw [hlenTot, array64_append, hlenA']
        sep_use hm3
      have hwf3 : BigNumRtWf rt st' scr (scrA' ++ outXs') :=
        BigNumRtWf.with_state_len hwf' hb' hlenTot
      refine hQ p st' (scrA' ++ outXs') objs' m3 hmst hrem hwf3 ?_ hm3'
      dsimp only [natArithPost, natArithRes]
      rw [hvalOut'] at hrep hsm hbg
      refine ⟨hrep, fun o ho => ?_⟩
      by_cases hsub : aVal - 1 < 2 ^ 63
      · rw [hsm hsub]; exact ho
      · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
        exact List.mem_cons_of_mem _ ho

private theorem lcnf_nat_arith_op678_wp
    (rt op : BitVec 64) (aVal bVal : Nat) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs scrA' scrB' scrOut : List (BitVec 64))
    (objs : List LcnfObj) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (hop : op.toNat ∈ [6, 7, 8])
    (_hna_max : limbLenNat aVal ≤ mpzMaxLimbs) (_hnb_max : limbLenNat bVal ≤ mpzMaxLimbs)
    (hna_leA : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤ scrA'.length)
    (hnb_leB : (BitVec.ofNat 64 (limbLenNat bVal)).toNat ≤ scrB'.length)
    (hvalA' : limbsVal (scrA'.take (BitVec.ofNat 64 (limbLenNat aVal)).toNat) = aVal)
    (hvalB' : limbsVal (scrB'.take (BitVec.ofNat 64 (limbLenNat bVal)).toNat) = bVal)
    (hlenTot : (scrA' ++ scrB' ++ scrOut).length = scrLimbs.length)
    (hlenA : scrA'.length = limbLenNat aVal) (hlenB : scrB'.length = limbLenNat bVal)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrA' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) scrOut ⋆
      lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natArithPost op.toNat aVal bVal res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
          args := (Arg.var op, Arg.imm 6, ()) } fun p_23 =>
        Expr.jnz (Arg.var p_23.fst)
          (Expr.group (sig := [[i64]])
            (fun _Js => Blocks.cons (fun p => Expr.ret (Arg.var p.fst, ())) Blocks.nil) fun Js =>
            Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
              (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
               Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
               Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ()) fun p =>
              Expr.let_
                { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun p_24 =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                    args := (Arg.var p.fst, Arg.var p_24.fst, ()) } fun p =>
                  Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 1, ()))
                    (Expr.jump Js.fst (Arg.imm 0, ())))
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
              args := (Arg.var op, Arg.imm 7, ()) } fun p_24 =>
            Expr.jnz (Arg.var p_24.fst)
              (Expr.group (sig := [[i64]])
                (fun _Js => Blocks.cons (fun p =>
                  Expr.ret (Arg.var p.fst, ())) Blocks.nil) fun Js =>
                Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
                  (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                   Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                   Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ()) fun p =>
                  Expr.let_
                    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun p_25 =>
                    Expr.let_
                      { sig := [i64, i64],
                        code := OpCode.cmp CmpOp.slt i64 Ty.bool,
                        args := (Arg.var p.fst, Arg.var p_25.fst, ()) } fun p =>
                      Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 1, ()))
                        (Expr.jump Js.fst (Arg.imm 0, ())))
              (Expr.let_
                { sig := [i64, i64],
                  code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                  args := (Arg.var op, Arg.imm 8, ()) } fun p_25 =>
                Expr.jnz (Arg.var p_25.fst)
                  (Expr.group (sig := [[i64]])
                    (fun _Js => Blocks.cons (fun p =>
                      Expr.ret (Arg.var p.fst, ())) Blocks.nil) fun Js =>
                    Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
                      (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                       Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                       Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ()) fun p =>
                      Expr.let_
                        { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0,
                          ()) } fun p_26 =>
                        Expr.let_
                          { sig := [i64, i64],
                            code := OpCode.cmp CmpOp.sle i64 Ty.bool,
                            args := (Arg.var p.fst, Arg.var p_26.fst, ()) } fun p =>
                          Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 1, ()))
                            (Expr.jump Js.fst (Arg.imm 0, ())))
                  (Expr.exit (as := [i64, i64]) "lcnf_panic" (Arg.var rt, Arg.imm 5, ()))))) m := by
  have hm_big : (bigNumRtInv rt st scr (scrA' ++ scrB' ++ scrOut) ⋆ lcnfHeap objs ⋆ R) m := by
    dsimp only [bigNumRtInv]
    have hlenAB : (scrA' ++ scrB').length = limbLenNat aVal + limbLenNat bVal := by
      simp [hlenA, hlenB]
    rw [hlenTot, array64_append, hlenAB, array64_append, hlenA]
    sep_use hm
  have hret_cmp : ∀ (P : Prop) [Decidable P] (hp : op.toNat = 6 → (P ↔ aVal = bVal))
      (hp7 : op.toNat = 7 → (P ↔ aVal < bVal)) (hp8 : op.toNat = 8 → (P ↔ aVal ≤ bVal)),
      ∀ (r : BitVec 64) (m' : Mem 64),
        (r = if P then 1#64 else 0#64) ∧ m' = m → Q (r, ()) m' := by
    intro P _ hp6 hp7 hp8 r m' ⟨hr, hm'⟩
    rw [hm']
    refine hQ r st (scrA' ++ scrB' ++ scrOut) objs m (preservesMeta_refl _) (Nat.le_refl _)
      (BigNumRtWf.with_state_len hwf hwf.1 hlenTot) ?_ hm_big
    dsimp only [natArithPost]
    rcases (by simpa using hop : op.toNat = 6 ∨ op.toNat = 7 ∨ op.toNat = 8) with h6 | h7 | h8
    · simp only [h6, ↓reduceIte, hr]
      by_cases hP : P
      · have hab := (hp6 h6).mp hP; simp only [hP, ↓reduceIte, hab]; exact ⟨trivial, trivial⟩
      · have hnab := mt (hp6 h6).mpr hP; simp only [hP, ↓reduceIte, hnab]; exact ⟨trivial, trivial⟩
    · simp only [h7, ↓reduceIte, hr]
      by_cases hP : P
      · have hab := (hp7 h7).mp hP; simp only [hP, ↓reduceIte, hab]; exact ⟨trivial, trivial⟩
      · have hnab := mt (hp7 h7).mpr hP; simp only [hP, ↓reduceIte, hnab]; exact ⟨trivial, trivial⟩
    · simp only [h8, ↓reduceIte, hr]
      by_cases hP : P
      · have hab := (hp8 h8).mp hP; simp only [hP, ↓reduceIte, hab]; exact ⟨trivial, trivial⟩
      · have hnab := mt (hp8 h8).mpr hP; simp only [hP, ↓reduceIte, hnab]; exact ⟨trivial, trivial⟩
  let R_cmp : Mem 64 → Prop := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
    array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) scrOut ⋆
      lcnfHeap objs ⋆ R
  c0_let_simp
  by_cases h6 : op = 6#64
  · subst h6
    apply wp_jnz_true (by decide)
    apply wp_join_group (fun (xs : Tup Val [i64]) (m' : Mem 64) =>
      (xs.fst = if aVal = bVal then 1#64 else 0#64) ∧ m' = m)
    · intro _ xs m' ⟨hxs, hm'⟩
      simp only [Blocks.get]; rw [wp_ret]
      exact hret_cmp (aVal = bVal) (fun _ => Iff.rfl) (fun h => by simp at h) (fun h =>
        by simp at h) xs.fst m'
        ⟨hxs, hm'⟩
    · intro Js hJs
      apply bn_cmp_call_wp (R := R_cmp) hna_leA hnb_leB (by dsimp only [R_cmp]; sep_use hm)
      c0_let_simp; rw [hvalA', hvalB']
      by_cases heq : aVal = bVal
      · apply wp_jnz_true ((cmpResult64_eq0_iff aVal bVal).mpr heq)
        rw [wp_jump]; exact hJs (1#64, ()) m ⟨by simp [heq], rfl⟩
      · have hf0 : (cmpResult64 aVal bVal == 0#64) = false :=
          Bool.eq_false_iff.mpr fun ht => heq ((cmpResult64_eq0_iff aVal bVal).mp ht)
        apply wp_jnz_false hf0
        rw [wp_jump]; exact hJs (0#64, ()) m ⟨by simp [heq], rfl⟩
  · have h6f : (op == 6#64) = false := beq_false_of_ne h6
    apply wp_jnz_false h6f
    c0_let_simp
    by_cases h7 : op = 7#64
    · subst h7
      apply wp_jnz_true (by decide)
      apply wp_join_group (fun (xs : Tup Val [i64]) (m' : Mem 64) =>
        (xs.fst = if aVal < bVal then 1#64 else 0#64) ∧ m' = m)
      · intro _ xs m' ⟨hxs, hm'⟩
        simp only [Blocks.get]; rw [wp_ret]
        exact hret_cmp (aVal < bVal) (fun h => by simp at h) (fun _ => Iff.rfl) (fun h =>
          by simp at h) xs.fst m'
          ⟨hxs, hm'⟩
      · intro Js hJs
        apply bn_cmp_call_wp (R := R_cmp) hna_leA hnb_leB (by dsimp only [R_cmp]; sep_use hm)
        c0_let_simp; rw [hvalA', hvalB']
        by_cases hlt : aVal < bVal
        · apply wp_jnz_true ((cmpResult64_slt0_iff aVal bVal).mpr hlt)
          rw [wp_jump]; exact hJs (1#64, ()) m ⟨by simp [hlt], rfl⟩
        · have hf0 : (cmpResult64 aVal bVal).slt 0#64 = false :=
            Bool.eq_false_iff.mpr fun ht => hlt ((cmpResult64_slt0_iff aVal bVal).mp ht)
          apply wp_jnz_false hf0
          rw [wp_jump]; exact hJs (0#64, ()) m ⟨by simp [hlt], rfl⟩
    · have h7f : (op == 7#64) = false := beq_false_of_ne h7
      apply wp_jnz_false h7f
      c0_let_simp
      have h8 : op = 8#64 := by
        rcases (by simpa using hop : op.toNat = 6 ∨ op.toNat = 7 ∨ op.toNat = 8) with h | h | h
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h6
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h7
        · exact BitVec.eq_of_toNat_eq (by simpa using h)
      subst h8
      apply wp_jnz_true (by decide)
      apply wp_join_group (fun (xs : Tup Val [i64]) (m' : Mem 64) =>
        (xs.fst = if aVal ≤ bVal then 1#64 else 0#64) ∧ m' = m)
      · intro _ xs m' ⟨hxs, hm'⟩
        simp only [Blocks.get]; rw [wp_ret]
        exact hret_cmp (aVal ≤ bVal) (fun h => by simp at h) (fun h => by simp at h) (fun _ =>
          Iff.rfl) xs.fst m'
          ⟨hxs, hm'⟩
      · intro Js hJs
        apply bn_cmp_call_wp (R := R_cmp) hna_leA hnb_leB (by dsimp only [R_cmp]; sep_use hm)
        c0_let_simp; rw [hvalA', hvalB']
        by_cases hle : aVal ≤ bVal
        · apply wp_jnz_true ((cmpResult64_sle0_iff aVal bVal).mpr hle)
          rw [wp_jump]; exact hJs (1#64, ()) m ⟨by simp [hle], rfl⟩
        · have hf0 : (cmpResult64 aVal bVal).sle 0#64 = false :=
            Bool.eq_false_iff.mpr fun ht => hle ((cmpResult64_sle0_iff aVal bVal).mp ht)
          apply wp_jnz_false hf0
          rw [wp_jump]; exact hJs (0#64, ()) m ⟨by simp [hle], rfl⟩

private theorem lcnf_nat_arith_op123_wp
    (rt op : BitVec 64) (aVal bVal : Nat) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) (scrA' scrB' scrOut : List (BitVec 64))
    (objs : List LcnfObj) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (hop : op.toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8])
    (hlenA : scrA'.length = limbLenNat aVal) (hlenB : scrB'.length = limbLenNat bVal)
    (hvalA : limbsVal (scrA'.take (limbLenNat aVal)) = aVal)
    (hvalB : limbsVal (scrB'.take (limbLenNat bVal)) = bVal)
    (hlenTot : scrA'.length + scrB'.length + scrOut.length = scrLimbs.length)
    (hneed : 2 * (limbLenNat aVal + limbLenNat bVal) + 2 ≤ scrLimbs.length)
    (hna_max : limbLenNat aVal ≤ mpzMaxLimbs) (hnb_max : limbLenNat bVal ≤ mpzMaxLimbs)
    (hok : natArithOk op.toNat aVal bVal scrLimbs.length st)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrA' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) scrOut ⋆
      lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natArithPost op.toNat aVal bVal res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
          args := (Arg.var op, Arg.imm 1, ()) } fun p_18 =>
        Expr.jnz (Arg.var p_18.fst)
          (Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "bn_add"
            (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
             Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
             Arg.var (BitVec.ofNat 64 (limbLenNat bVal)),
             Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal +
               limbLenNat bVal))), ()) fun p_19 =>
            Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_nat_from_limbs"
              (Arg.var rt,
                Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))),
               Arg.var p_19.fst, ()) fun p => Expr.ret (Arg.var p.fst, ()))
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
              args := (Arg.var op, Arg.imm 2, ()) } fun p_19 =>
            Expr.jnz (Arg.var p_19.fst)
              (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
                (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                 Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                 Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ()) fun p_20 =>
                Expr.let_
                  { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun p_21 =>
                  Expr.let_
                    { sig := [i64, i64],
                      code := OpCode.cmp CmpOp.sle i64 Ty.bool,
                      args := (Arg.var p_20.fst, Arg.var p_21.fst, ()) } fun p_22 =>
                    Expr.jnz (Arg.var p_22.fst) (Expr.ret (Arg.imm 1, ()))
                      (Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "bn_sub"
                        (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                         Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                         Arg.var (BitVec.ofNat 64 (limbLenNat bVal)),
                         Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal +
                           limbLenNat bVal))), ()) fun p_23 =>
                        Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_nat_from_limbs"
                          (Arg.var rt,
                            Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal +
                              limbLenNat bVal))),
                           Arg.var p_23.fst, ()) fun p => Expr.ret (Arg.var p.fst, ())))
              (Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                  args := (Arg.var op, Arg.imm 3, ()) } fun p_20 =>
                Expr.jnz (Arg.var p_20.fst)
                  (Expr.let_
                    { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                      args := (Arg.var (BitVec.ofNat 64 (limbLenNat aVal)), Arg.imm 0,
                        ()) } fun p_21 =>
                    Expr.jnz (Arg.var p_21.fst) (Expr.ret (Arg.imm 1, ()))
                      (Expr.let_
                        { sig := [i64, i64],
                          code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                          args := (Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), Arg.imm 0,
                            ()) } fun p_22 =>
                        Expr.jnz (Arg.var p_22.fst) (Expr.ret (Arg.imm 1, ()))
                          (Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "bn_mul"
                            (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                             Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                             Arg.var (BitVec.ofNat 64 (limbLenNat bVal)),
                             Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal +
                               limbLenNat bVal))), ()) fun p_23 =>
                            Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_nat_from_limbs"
                              (Arg.var rt,
                                Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal +
                                  limbLenNat bVal))),
                               Arg.var p_23.fst, ()) fun p => Expr.ret (Arg.var p.fst, ()))))
                  (Expr.let_
                    { sig := [i64, i64],
                      code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                      args := (Arg.var op, Arg.imm 4, ()) } fun p_21 =>
                    Expr.jnz (Arg.var p_21.fst)
                      (Expr.let_
                        { sig := [i64, i64],
                          code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                          args := (Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), Arg.imm 0,
                            ()) } fun p_22 =>
                        Expr.jnz (Arg.var p_22.fst) (Expr.ret (Arg.imm 1, ()))
                          (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
                            (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                             Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                             Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ()) fun p_23 =>
                            Expr.let_
                              { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0,
                                ()) } fun p_24 =>
                              Expr.let_
                                { sig := [i64, i64],
                                  code := OpCode.cmp CmpOp.slt i64 Ty.bool,
                                  args := (Arg.var p_23.fst, Arg.var p_24.fst, ()) } fun p_25 =>
                                Expr.jnz (Arg.var p_25.fst) (Expr.ret (Arg.imm 1, ()))
                                  (Expr.let_
                                    { sig := [i64, i64], code := OpCode.mul i64,
                                      args := (Arg.imm 8,
                                        Arg.var (BitVec.ofNat 64 (limbLenNat aVal)), ()) }
                                          fun p_26 =>
                                    Expr.let_
                                      { sig := [i64, i64], code := OpCode.add i64,
                                        args :=
                                          (Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal +
                                            limbLenNat bVal))),
                                           Arg.var p_26.fst, ()) } fun p_27 =>
                                      Expr.call (as := [i64, i64, i64, i64, i64,
                                        i64]) (bs := []) "bn_divmod"
                                        (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                                         Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                                         Arg.var (BitVec.ofNat 64 (limbLenNat bVal)),
                                         Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal +
                                           limbLenNat bVal))),
                                         Arg.var p_27.fst, ()) fun _ =>
                                        Expr.call (as := [i64, i64,
                                          i64]) (bs := [i64]) "bn_nat_from_limbs"
                                          (Arg.var rt,
                                           Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal +
                                             limbLenNat bVal))),
                                           Arg.var (BitVec.ofNat 64 (limbLenNat aVal)), ()) fun p =>
                                          Expr.ret (Arg.var p.fst, ()))))
                      (Expr.let_
                        { sig := [i64, i64],
                          code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                          args := (Arg.var op, Arg.imm 5, ()) } fun p_22 =>
                        Expr.jnz (Arg.var p_22.fst)
                          (Expr.group (sig := [[]])
                            (fun _Js =>
                              Blocks.cons
                                (fun _ =>
                                  Expr.call (as := [i64, i64,
                                    i64]) (bs := [i64]) "bn_nat_from_limbs"
                                    (Arg.var rt, Arg.var scr,
                                     Arg.var (BitVec.ofNat 64 (limbLenNat aVal)), ()) fun p =>
                                    Expr.ret (Arg.var p.fst, ()))
                                Blocks.nil)
                            fun Js =>
                            Expr.let_
                              { sig := [i64, i64],
                                code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                                args := (Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), Arg.imm 0,
                                  ()) } fun p_23 =>
                              Expr.jnz (Arg.var p_23.fst) (Expr.jump Js.fst ())
                                (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
                                  (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                                   Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                                   Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ()) fun p_24 =>
                                  Expr.let_
                                    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0,
                                      ()) } fun p_25 =>
                                    Expr.let_
                                      { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.slt i64 Ty.bool,
                                        args := (Arg.var p_24.fst, Arg.var p_25.fst,
                                          ()) } fun p_26 =>
                                      Expr.jnz (Arg.var p_26.fst) (Expr.jump Js.fst ())
                                        (Expr.let_
                                          { sig := [i64, i64], code := OpCode.mul i64,
                                            args := (Arg.imm 8,
                                              Arg.var (BitVec.ofNat 64 (limbLenNat aVal)), ()) }
                                          fun p_27 =>
                                          Expr.let_
                                            { sig := [i64, i64], code := OpCode.add i64,
                                              args :=
                                                (Arg.var (scr +
                                                  BitVec.ofNat 64 (8 * (limbLenNat aVal +
                                                    limbLenNat bVal))),
                                                 Arg.var p_27.fst, ()) } fun p_28 =>
                                            Expr.call (as := [i64, i64, i64, i64, i64,
                                              i64]) (bs := []) "bn_divmod"
                                              (Arg.var scr,
                                                Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                                               Arg.var (scr +
                                                 BitVec.ofNat 64 (8 * limbLenNat aVal)),
                                               Arg.var (BitVec.ofNat 64 (limbLenNat bVal)),
                                               Arg.var (scr +
                                                 BitVec.ofNat 64 (8 * (limbLenNat aVal +
                                                   limbLenNat bVal))),
                                               Arg.var p_28.fst, ()) fun _ =>
                                              Expr.call (as := [i64, i64,
                                                i64]) (bs := [i64]) "bn_nat_from_limbs"
                                                (Arg.var rt, Arg.var p_28.fst,
                                                 Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ())
                                                   fun p =>
                                                Expr.ret (Arg.var p.fst, ()))))
                          (Expr.let_
                            { sig := [i64, i64],
                              code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                              args := (Arg.var op, Arg.imm 6, ()) } fun p_23 =>
                            Expr.jnz (Arg.var p_23.fst)
                              (Expr.group (sig := [[i64]])
                                (fun _Js => Blocks.cons (fun p =>
                                  Expr.ret (Arg.var p.fst, ())) Blocks.nil)
                                fun Js =>
                                Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
                                  (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                                   Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                                   Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ()) fun p =>
                                  Expr.let_
                                    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0,
                                      ()) } fun p_24 =>
                                    Expr.let_
                                      { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                                        args := (Arg.var p.fst, Arg.var p_24.fst, ()) } fun p =>
                                      Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 1, ()))
                                        (Expr.jump Js.fst (Arg.imm 0, ())))
                              (Expr.let_
                                { sig := [i64, i64],
                                  code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                                  args := (Arg.var op, Arg.imm 7, ()) } fun p_24 =>
                                Expr.jnz (Arg.var p_24.fst)
                                  (Expr.group (sig := [[i64]])
                                    (fun _Js => Blocks.cons (fun p =>
                                      Expr.ret (Arg.var p.fst, ())) Blocks.nil)
                                    fun Js =>
                                    Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
                                      (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                                       Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                                       Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ()) fun p =>
                                      Expr.let_
                                        { sig := [i32], code := OpCode.sext 32 64,
                                          args := (Arg.imm 0, ()) } fun p_25 =>
                                        Expr.let_
                                          { sig := [i64, i64],
                                            code := OpCode.cmp CmpOp.slt i64 Ty.bool,
                                            args := (Arg.var p.fst, Arg.var p_25.fst, ()) } fun p =>
                                          Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 1,
                                            ()))
                                            (Expr.jump Js.fst (Arg.imm 0, ())))
                                  (Expr.let_
                                    { sig := [i64, i64],
                                      code := OpCode.cmp CmpOp.eq i64 Ty.bool,
                                      args := (Arg.var op, Arg.imm 8, ()) } fun p_25 =>
                                    Expr.jnz (Arg.var p_25.fst)
                                      (Expr.group (sig := [[i64]])
                                        (fun _Js => Blocks.cons (fun p =>
                                          Expr.ret (Arg.var p.fst, ())) Blocks.nil)
                                        fun Js =>
                                        Expr.call (as := [i64, i64, i64,
                                          i64]) (bs := [i64]) "bn_cmp"
                                          (Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)),
                                           Arg.var (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)),
                                           Arg.var (BitVec.ofNat 64 (limbLenNat bVal)), ()) fun p =>
                                          Expr.let_
                                            { sig := [i32], code := OpCode.sext 32 64,
                                              args := (Arg.imm 0, ()) }
                                            fun p_26 =>
                                            Expr.let_
                                              { sig := [i64, i64],
                                                code := OpCode.cmp CmpOp.sle i64 Ty.bool,
                                                args := (Arg.var p.fst, Arg.var p_26.fst,
                                                  ()) } fun p =>
                                              Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 1,
                                                ()))
                                                (Expr.jump Js.fst (Arg.imm 0, ())))
                                      (Expr.exit (as := [i64, i64]) "lcnf_panic" (Arg.var rt,
                                        Arg.imm 5, ())))))))))) m := by
  have hna_bv : (BitVec.ofNat 64 (limbLenNat aVal)).toNat = limbLenNat aVal := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hna_max; omega)]
  have hnb_bv : (BitVec.ofNat 64 (limbLenNat bVal)).toNat = limbLenNat bVal := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hnb_max; omega)]
  have hna_leA : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤ scrA'.length := by omega
  have hnb_leB : (BitVec.ofNat 64 (limbLenNat bVal)).toNat ≤ scrB'.length := by omega
  have hvalA' : limbsVal (scrA'.take (BitVec.ofNat 64 (limbLenNat aVal)).toNat) = aVal := by
    rwa [hna_bv]
  have hvalB' : limbsVal (scrB'.take (BitVec.ofNat 64 (limbLenNat bVal)).toNat) = bVal := by
    rwa [hnb_bv]
  have hlenTot' : (scrA' ++ scrB' ++ scrOut).length = scrLimbs.length := by
    simp [hlenA, hlenB]; omega
  have hm_merge : ∀ {st' scrOut' objs' m'} (hlenO' : scrOut'.length = scrOut.length),
      (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr scrA' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) scrOut' ⋆
        lcnfHeap objs' ⋆ R) m' →
      st'.Bounded48 →
      ∃ scrLimbs', scrLimbs'.length = scrLimbs.length ∧ BigNumRtWf rt st' scr scrLimbs' ∧
        (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' := by
    intro st' scrOut' objs' m' hlenO' hm' hb'
    refine ⟨scrA' ++ scrB' ++ scrOut', by simp [hlenA, hlenB, hlenO']; omega,
      BigNumRtWf.with_state_len hwf hb' (by simp [hlenA, hlenB, hlenO']; omega), ?_⟩
    dsimp only [bigNumRtInv]
    have hlenAB : (scrA' ++ scrB').length = limbLenNat aVal + limbLenNat bVal := by
      simp [hlenA, hlenB]
    rw [show (scrA' ++ scrB' ++ scrOut').length =
      scrLimbs.length by simp [hlenA, hlenB, hlenO']; omega]
    rw [array64_append, hlenAB, array64_append, hlenA]
    sep_use hm'
  have hout_ge : limbLenNat aVal + limbLenNat bVal + 2 ≤ scrOut.length := by omega
  have hfinish : ∀ {res st' scrOut' objs' m'} (hlenO' : scrOut'.length = scrOut.length)
      (hmst : st'.PreservesMeta st) (hrem : st'.rem ≤ st.rem) (hb' : st'.Bounded48)
      (hpost : natArithPost op.toNat aVal bVal res objs objs')
      (hm' : (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr scrA' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) scrOut' ⋆
        lcnfHeap objs' ⋆ R) m'),
      Q (res, ()) m' := by
    intro res st' scrOut' objs' m' hlenO' hmst hrem hb' hpost hm'
    obtain ⟨scrLimbs', _, hwf', hm''⟩ := hm_merge hlenO' hm' hb'
    exact hQ res st' scrLimbs' objs' m' hmst hrem hwf' hpost hm''
  let R_abOut : Mem 64 → Prop := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ lcnfHeap objs ⋆ R
  let R_cmp : Mem 64 → Prop := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
    array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) scrOut ⋆
      lcnfHeap objs ⋆ R
  let R_outFrom : Mem 64 → Prop := cell64 (rt + 33672#64) scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrA' ⋆
    array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆ R
  have hfrom_out : ∀ (ok : natArithOk op.toNat aVal bVal scrLimbs.length st)
      {tnNat : Nat} {scrOut' : List (BitVec 64)} {m' : Mem 64},
      tnNat ≤ scrOut'.length → scrOut'.length = scrOut.length →
      limbsVal (scrOut'.take tnNat) = natArithRes op.toNat aVal bVal →
      limbLenNat (natArithRes op.toNat aVal bVal) = tnNat →
      op.toNat ∈ [1, 2, 3, 4, 5] →
      (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr scrA' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) scrOut' ⋆
        lcnfHeap objs ⋆ R) m' →
      wp rtR1Env Q X
        (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_nat_from_limbs"
          (Arg.var rt, Arg.var (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))),
           Arg.var (BitVec.ofNat 64 tnNat), ()) fun p => Expr.ret (Arg.var p.fst, ())) m' := by
    intro ok tnNat scrOut' m' htn_le hlenO' hvalO htn_eq hop15 hm'
    dsimp only [natArithOk] at ok
    simp only [show op.toNat ≠ 17 by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop15
      omega, hop15, ↓reduceIte] at ok
    rcases ok with ⟨_, hmax_res, halloc⟩
    have htn_max : tnNat ≤ mpzMaxLimbs := by rwa [← htn_eq]
    have htn_bv : (BitVec.ofNat 64 tnNat).toNat = tnNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at htn_max; omega)]
    have hvalO' : limbsVal (scrOut'.take (BitVec.ofNat 64 tnNat).toNat) =
      natArithRes op.toNat aVal bVal := by
      rwa [htn_bv]
    have htrim : trimLenLoop scrOut' (BitVec.ofNat 64 tnNat).toNat =
      limbLenNat (natArithRes op.toNat aVal bVal) := by
      rw [htn_bv, ← limbLenNat_trimLenLoop htn_le, hvalO]
    apply bn_nat_from_limbs_call_wp (R := R_outFrom) (by rwa [htn_bv]) (by rwa [htn_bv]) hwf.1
      (fun hge => by rw [hvalO'] at hge; rw [htrim]; exact halloc hge)
        (by dsimp only [R_outFrom]; sep_use hm')
    intro p st' objs' m2 hmst hrem hb' hrep hsm hbg hm2
    c0_step
    rw [hvalO'] at hrep hsm hbg
    refine hfinish hlenO' hmst hrem hb' ?_ (by dsimp only [R_outFrom] at hm2; sep_use hm2)
    dsimp only [natArithPost]
    have h6 : op.toNat ≠ 6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop15; omega
    have h7 : op.toNat ≠ 7 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop15; omega
    have h8 : op.toNat ≠ 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop15; omega
    simp only [h6, h7, h8, ↓reduceIte]
    refine ⟨hrep, fun o ho => ?_⟩
    by_cases hs : natArithRes op.toNat aVal bVal < 2 ^ 63
    · rw [hsm hs]; exact ho
    · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
      exact List.mem_cons_of_mem _ ho
  c0_let_simp
  by_cases h1 : op = 1#64
  · subst h1
    apply wp_jnz_true (by decide)
    have hout1 : max (BitVec.ofNat 64 (limbLenNat aVal)).toNat (BitVec.ofNat 64
      (limbLenNat bVal)).toNat + 1 ≤
        scrOut.length := by rw [hna_bv, hnb_bv]; omega
    have hlt1 : max (BitVec.ofNat 64 (limbLenNat aVal)).toNat (BitVec.ofNat 64
      (limbLenNat bVal)).toNat + 1 < 2 ^ 64 := by
      rw [hna_bv, hnb_bv]; unfold mpzMaxLimbs at hna_max hnb_max; omega
    apply bn_add_call_wp (R := R_abOut) hna_leA hnb_leB hout1 hlt1
      (by dsimp only [R_abOut]; sep_use hm)
    intro outXs' m1
    dsimp only
    intro hlenO' htnO hvalO hm1
    rw [hvalA', hvalB'] at htnO hvalO ⊢
    try rw [Nat.mul_comm (limbLenNat aVal) 8] at hm1
    exact hfrom_out hok (by rw [hlenO']; exact htnO) hlenO' hvalO rfl (by decide)
      (by dsimp only [R_abOut] at hm1; sep_use hm1)
  · apply wp_jnz_false (beq_false_of_ne h1)
    c0_let_simp
    by_cases h2 : op = 2#64
    · subst h2
      apply wp_jnz_true (by decide)
      apply bn_cmp_call_wp (R := R_cmp) hna_leA hnb_leB (by dsimp only [R_cmp]; sep_use hm)
      c0_let_simp
      rw [hvalA', hvalB']
      by_cases hle : aVal ≤ bVal
      · apply wp_jnz_true ((cmpResult64_sle0_iff aVal bVal).mpr hle)
        c0_step
        refine hfinish rfl (preservesMeta_refl _) (Nat.le_refl _) hwf.1 ?_ hm
        dsimp only [natArithPost, natArithRes, natRep]
        have hsub0 : aVal - bVal = 0 := by omega
        simp [hsub0]
      · have hgt : bVal ≤ aVal := by omega
        have hle_f : (cmpResult64 aVal bVal).sle 0#64 = false :=
          Bool.eq_false_iff.mpr fun ht => hle ((cmpResult64_sle0_iff aVal bVal).mp ht)
        apply wp_jnz_false hle_f
        have hout2 : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤ scrOut.length := by
          rw [hna_bv]; omega
        apply bn_sub_call_wp (R := R_abOut) hna_leA hnb_leB hout2
          (by rw [hvalA', hvalB']; exact hgt) (by dsimp only [R_abOut]; sep_use hm)
        intro outXs' m1
        dsimp only
        intro hlenO' htnO hvalO hm1
        rw [hvalA', hvalB'] at htnO hvalO
        try rw [hvalA', hvalB']
        try rw [Nat.mul_comm (limbLenNat aVal) 8] at hm1
        exact hfrom_out hok (by rw [hlenO']; exact htnO) hlenO' hvalO rfl (by decide)
          (by dsimp only [R_abOut] at hm1; sep_use hm1)
    · apply wp_jnz_false (beq_false_of_ne h2)
      c0_let_simp
      by_cases h3 : op = 3#64
      · subst h3
        apply wp_jnz_true (by decide)
        by_cases ha0 : aVal = 0
        · have hna0 : BitVec.ofNat 64 (limbLenNat aVal) = 0#64 := by simp [ha0, limbLenNat]
          apply wp_jnz_true (by rw [hna0]; decide)
          c0_step
          refine hfinish rfl (preservesMeta_refl _) (Nat.le_refl _) hwf.1 ?_ hm
          simp [natArithPost, natArithRes, natRep, ha0]
        · have hna_nz : (BitVec.ofNat 64 (limbLenNat aVal) == 0#64) = false := by
            apply Bool.eq_false_iff.mpr
            intro ht
            have := BitVec.toNat_eq.mp (beq_iff_eq.mp ht)
            rw [hna_bv, show (0#64 : BitVec 64).toNat = 0 from rfl] at this
            have := limbLenNat_pos_iff.mpr (Nat.pos_of_ne_zero ha0)
            omega
          apply wp_jnz_false hna_nz
          by_cases hb0 : bVal = 0
          · have hnb0 : BitVec.ofNat 64 (limbLenNat bVal) = 0#64 := by simp [hb0, limbLenNat]
            apply wp_jnz_true (by rw [hnb0]; decide)
            c0_step
            refine hfinish rfl (preservesMeta_refl _) (Nat.le_refl _) hwf.1 ?_ hm
            simp [natArithPost, natArithRes, natRep, hb0]
          · have hnb_nz : (BitVec.ofNat 64 (limbLenNat bVal) == 0#64) = false := by
              apply Bool.eq_false_iff.mpr
              intro ht
              have := BitVec.toNat_eq.mp (beq_iff_eq.mp ht)
              rw [hnb_bv, show (0#64 : BitVec 64).toNat = 0 from rfl] at this
              have := limbLenNat_pos_iff.mpr (Nat.pos_of_ne_zero hb0)
              omega
            apply wp_jnz_false hnb_nz
            have hout3 : (BitVec.ofNat 64 (limbLenNat aVal)).toNat +
                (BitVec.ofNat 64 (limbLenNat bVal)).toNat ≤ scrOut.length := by
              rw [hna_bv, hnb_bv]; omega
            have hlt3 : (BitVec.ofNat 64 (limbLenNat aVal)).toNat +
                (BitVec.ofNat 64 (limbLenNat bVal)).toNat < 2 ^ 64 := by
              rw [hna_bv, hnb_bv]; unfold mpzMaxLimbs at hna_max hnb_max; omega
            apply bn_mul_call_wp (R := R_abOut) hna_leA hnb_leB hout3 hlt3
              (by dsimp only [R_abOut]; sep_use hm)
            intro outXs' m1 hlenO' htnO hvalO hm1
            rw [hvalA', hvalB'] at htnO hvalO
            try rw [hvalA', hvalB']
            exact hfrom_out hok (by rw [hlenO']; exact htnO) hlenO' hvalO rfl (by decide)
              (by dsimp only [R_abOut] at hm1; sep_use hm1)
      · apply wp_jnz_false (beq_false_of_ne h3)
        c0_let_simp
        have h8mul := bv64_mul8_of_lt (limbLenNat aVal) (by unfold mpzMaxLimbs at hna_max; omega)
        by_cases h4 : op = 4#64
        · subst h4
          apply wp_jnz_true (by decide)
          by_cases hb0 : bVal = 0
          · have hnb0 : BitVec.ofNat 64 (limbLenNat bVal) = 0#64 := by simp [hb0, limbLenNat]
            apply wp_jnz_true (by rw [hnb0]; decide)
            c0_step
            refine hfinish rfl (preservesMeta_refl _) (Nat.le_refl _) hwf.1 ?_ hm
            simp [natArithPost, natArithRes, natRep, hb0]
          · have hnb_pos : 0 < limbLenNat bVal := limbLenNat_pos_iff.mpr (Nat.pos_of_ne_zero hb0)
            have hnb_nz : (BitVec.ofNat 64 (limbLenNat bVal) == 0#64) = false := by
              apply Bool.eq_false_iff.mpr; intro ht
              have := BitVec.toNat_eq.mp (beq_iff_eq.mp ht)
              rw [hnb_bv, show (0#64 : BitVec 64).toNat = 0 from rfl] at this; omega
            apply wp_jnz_false hnb_nz
            apply bn_cmp_call_wp (R := R_cmp) hna_leA hnb_leB (by dsimp only [R_cmp]; sep_use hm)
            c0_let_simp
            rw [hvalA', hvalB']
            by_cases hlt : aVal < bVal
            · apply wp_jnz_true ((cmpResult64_slt0_iff aVal bVal).mpr hlt)
              c0_step
              refine hfinish rfl (preservesMeta_refl _) (Nat.le_refl _) hwf.1 ?_ hm
              simp [natArithPost, natArithRes, natRep, Nat.div_eq_of_lt hlt]
            · have hge : bVal ≤ aVal := by omega
              have hna_pos : 0 < limbLenNat aVal := limbLenNat_pos_iff.mpr (by omega)
              have hlt_f : (cmpResult64 aVal bVal).slt 0#64 = false :=
                Bool.eq_false_iff.mpr fun ht => hlt ((cmpResult64_slt0_iff aVal bVal).mp ht)
              apply wp_jnz_false hlt_f
              c0_let_simp
              rw [h8mul]
              have hm_split := hm
              rw [array64_split_len
                (a := scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal)))
                (k := limbLenNat aVal) (by omega)] at hm_split
              try rw [Nat.mul_comm (limbLenNat aVal) 8] at hm_split
              have hq_len : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤
                  (scrOut.take (limbLenNat aVal)).length := by
                rw [List.length_take_of_le (by omega), hna_bv]; exact le_refl _
              have hr_len : (BitVec.ofNat 64 (limbLenNat bVal)).toNat ≤
                  (scrOut.drop (limbLenNat aVal)).length := by
                rw [List.length_drop, hnb_bv]; omega
              have hmsb : scrB'[(BitVec.ofNat 64 (limbLenNat bVal)).toNat - 1]! ≠ 0#64 := by
                rw [hnb_bv]
                exact limbsVal_msb_nz hnb_pos (by omega) (by conv => lhs; rw [← hnb_bv, hvalB'])
              apply bn_divmod_call_wp (R := R_abOut) (by rw [hna_bv]; exact hna_pos)
                (by rw [hnb_bv]; exact hnb_pos) hna_leA hnb_leB hq_len hr_len hmsb
                (by dsimp only [R_abOut]; sep_use hm_split)
              intro qXs' rXs' m1 hlenQ hlenR hvalQ _ hm1
              rw [hvalA', hvalB'] at hvalQ
              have hq_len' : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤ qXs'.length := by
                rw [hlenQ]; exact hq_len
              have hok' := hok
              rw [show (4#64 : BitVec 64).toNat = 4 from rfl] at hok'
              dsimp only [natArithOk] at hok'
              simp only [show (4 : Nat) ≠ 17 by omega, show (4 : Nat) ∈ [1, 2, 3, 4, 5] by decide,
                ↓reduceIte] at hok'
              rcases hok' with ⟨_, _, halloc⟩
              have hq_val : limbsVal (qXs'.take (limbLenNat aVal)) = aVal / bVal := by
                rwa [hna_bv] at hvalQ
              have htrimQ : trimLenLoop qXs' (BitVec.ofNat 64 (limbLenNat aVal)).toNat =
                  limbLenNat (aVal / bVal) := by
                rw [hna_bv, ← limbLenNat_trimLenLoop
                  (by rw [hlenQ, List.length_take_of_le (by omega)]; exact le_refl _),
                  hq_val]
              apply bn_nat_from_limbs_call_wp (R := cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrA' ⋆
                array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
                array64 ((scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) +
                  BitVec.ofNat 64 (8 * limbLenNat aVal)) rXs' ⋆ R)
                hq_len' (by rw [hna_bv]; exact hna_max) hwf.1
                (fun hge => by rw [hvalQ] at hge; rw [htrimQ]; exact halloc hge)
                (by dsimp only [R_abOut] at hm1; sep_use hm1)
              intro p st' objs' m2 hmst hrem hb' hrep hsm hbg hm2
              c0_step
              have hqr_len : (qXs' ++ rXs').length = scrOut.length := by
                rw [List.length_append, hlenQ, hlenR, List.length_take_of_le
                  (by omega), List.length_drop]
                omega
              have hq'_len : qXs'.length = limbLenNat aVal := by
                rw [hlenQ, List.length_take_of_le (by omega)]
              have hm2' : (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                array64 scr scrA' ⋆
                array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
                array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal)))
                  (qXs' ++ rXs') ⋆
                lcnfHeap objs' ⋆ R) m2 := by
                rw [array64_append, hq'_len]
                try rw [Nat.mul_comm (limbLenNat aVal) 8]
                sep_use hm2
              rw [hvalQ] at hrep hsm hbg
              refine hfinish hqr_len hmst hrem hb' ?_ hm2'
              dsimp only [natArithPost, natArithRes]
              refine ⟨hrep, fun o ho => ?_⟩
              by_cases hs : aVal / bVal < 2 ^ 63
              · rw [hsm hs]; exact ho
              · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
                exact List.mem_cons_of_mem _ ho
        · apply wp_jnz_false (beq_false_of_ne h4)
          c0_let_simp
          by_cases h5 : op = 5#64
          · subst h5
            apply wp_jnz_true (by decide)
            have hm_fromA :
                ∀ m',
                  (bVal = 0 ∨ aVal < bVal) →
                  (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                    array64 scr scrA' ⋆
                    array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
                    array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal +
                      limbLenNat bVal))) scrOut ⋆
                    lcnfHeap objs ⋆ R) m' →
                  wp rtR1Env Q X
                    (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_nat_from_limbs"
                      (Arg.var rt, Arg.var scr, Arg.var (BitVec.ofNat 64 (limbLenNat aVal)), ())
                      fun p => Expr.ret (Arg.var p.fst, ())) m' := by
              intro m' hcase hm'
              have hmod_eq : aVal % bVal = aVal := by
                rcases hcase with rfl | hlt
                · simp
                · exact Nat.mod_eq_of_lt hlt
              have hok' := hok
              rw [show (5#64 : BitVec 64).toNat = 5 from rfl] at hok'
              dsimp only [natArithOk] at hok'
              simp only [show (5 : Nat) ≠ 17 by omega, show (5 : Nat) ∈ [1, 2, 3, 4, 5] by decide,
                ↓reduceIte] at hok'
              rcases hok' with ⟨_, _, halloc⟩
              have hmod_res : natArithRes 5 aVal bVal = aVal := by
                simp [natArithRes, hmod_eq]
              rw [hmod_res] at halloc
              have ha_val' : limbsVal (scrA'.take (limbLenNat aVal)) = aVal := by
                rwa [hna_bv] at hvalA'
              have htrimA : trimLenLoop scrA' (BitVec.ofNat 64 (limbLenNat aVal)).toNat =
                  limbLenNat aVal := by
                rw [hna_bv, ← limbLenNat_trimLenLoop (by omega), ha_val']
              apply bn_nat_from_limbs_call_wp (R := cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
                array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) scrOut ⋆
                  R)
                hna_leA (by rw [hna_bv]; exact hna_max) hwf.1
                (fun hge => by rw [hvalA'] at hge; rw [htrimA]; exact halloc hge) (by sep_use hm')
              intro p st' objs' m2 hmst hrem hb' hrep hsm hbg hm2
              c0_step
              rw [hvalA'] at hrep hsm hbg
              refine hfinish rfl hmst hrem hb' ?_ (by sep_use hm2)
              dsimp only [natArithPost, natArithRes]
              rw [hmod_eq]
              refine ⟨hrep, fun o ho => ?_⟩
              by_cases hs : aVal < 2 ^ 63
              · rw [hsm hs]; exact ho
              · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
                exact List.mem_cons_of_mem _ ho
            apply wp_join_group
              (fun _ m' => (bVal = 0 ∨ aVal < bVal) ∧
                (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                  array64 scr scrA' ⋆
                  array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
                  array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) scrOut ⋆
                  lcnfHeap objs ⋆ R) m')
            · intro J _ m' ⟨hcase, hm'⟩
              simp only [Blocks.get]
              exact hm_fromA m' hcase hm'
            · intro Js hJs
              by_cases hb0 : bVal = 0
              · have hnb0 : BitVec.ofNat 64 (limbLenNat bVal) = 0#64 := by simp [hb0, limbLenNat]
                apply wp_jnz_true (by rw [hnb0]; decide)
                rw [wp_jump]; exact hJs () m ⟨Or.inl hb0, hm⟩
              · have hnb_pos : 0 < limbLenNat bVal :=
                limbLenNat_pos_iff.mpr (Nat.pos_of_ne_zero hb0)
                have hnb_nz : (BitVec.ofNat 64 (limbLenNat bVal) == 0#64) = false := by
                  apply Bool.eq_false_iff.mpr; intro ht
                  have := BitVec.toNat_eq.mp (beq_iff_eq.mp ht)
                  rw [hnb_bv, show (0#64 : BitVec 64).toNat = 0 from rfl] at this; omega
                apply wp_jnz_false hnb_nz
                apply bn_cmp_call_wp (R := R_cmp) hna_leA hnb_leB
                  (by dsimp only [R_cmp]; sep_use hm)
                c0_let_simp
                rw [hvalA', hvalB']
                by_cases hlt : aVal < bVal
                · apply wp_jnz_true ((cmpResult64_slt0_iff aVal bVal).mpr hlt)
                  rw [wp_jump]; exact hJs () m ⟨Or.inr hlt, hm⟩
                · have hge : bVal ≤ aVal := by omega
                  have hna_pos : 0 < limbLenNat aVal := limbLenNat_pos_iff.mpr (by omega)
                  have hlt_f : (cmpResult64 aVal bVal).slt 0#64 = false :=
                    Bool.eq_false_iff.mpr fun ht => hlt ((cmpResult64_slt0_iff aVal bVal).mp ht)
                  apply wp_jnz_false hlt_f
                  c0_let_simp
                  rw [h8mul]
                  have hm_split := hm
                  rw [array64_split_len
                    (a := scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal)))
                    (k := limbLenNat aVal) (by omega)] at hm_split
                  try rw [Nat.mul_comm (limbLenNat aVal) 8] at hm_split
                  have hq_len : (BitVec.ofNat 64 (limbLenNat aVal)).toNat ≤
                      (scrOut.take (limbLenNat aVal)).length := by
                    rw [List.length_take_of_le (by omega), hna_bv]; exact le_refl _
                  have hr_len : (BitVec.ofNat 64 (limbLenNat bVal)).toNat ≤
                      (scrOut.drop (limbLenNat aVal)).length := by
                    rw [List.length_drop, hnb_bv]; omega
                  have hmsb : scrB'[(BitVec.ofNat 64 (limbLenNat bVal)).toNat - 1]! ≠ 0#64 := by
                    rw [hnb_bv]
                    exact limbsVal_msb_nz hnb_pos (by omega) (by conv => lhs; rw [← hnb_bv, hvalB'])
                  apply bn_divmod_call_wp (R := R_abOut) (by rw [hna_bv]; exact hna_pos)
                    (by rw [hnb_bv]; exact hnb_pos) hna_leA hnb_leB hq_len hr_len hmsb
                    (by dsimp only [R_abOut]; sep_use hm_split)
                  intro qXs' rXs' m1 hlenQ hlenR _ hvalR hm1
                  rw [hvalA', hvalB'] at hvalR
                  have hr_len' : (BitVec.ofNat 64 (limbLenNat bVal)).toNat ≤ rXs'.length := by
                    rw [hlenR]; exact hr_len
                  have hok' := hok
                  rw [show (5#64 : BitVec 64).toNat = 5 from rfl] at hok'
                  dsimp only [natArithOk] at hok'
                  simp only [show (5 : Nat) ≠ 17 by omega, show (5 : Nat) ∈ [1, 2, 3, 4,
                    5] by decide, ↓reduceIte] at hok'
                  rcases hok' with ⟨_, _, halloc⟩
                  have hr_val : limbsVal (rXs'.take (limbLenNat bVal)) = aVal % bVal := by
                    rwa [hnb_bv] at hvalR
                  have htrimR : trimLenLoop rXs' (BitVec.ofNat 64 (limbLenNat bVal)).toNat =
                      limbLenNat (aVal % bVal) := by
                    rw [hnb_bv, ← limbLenNat_trimLenLoop
                      (by rw [hlenR, List.length_drop]; omega), hr_val]
                  apply bn_nat_from_limbs_call_wp (R := cell64 (rt + 33672#64) scr ⋆
                    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrA' ⋆
                    array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
                    array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal))) qXs' ⋆
                      R)
                    hr_len' (by rw [hnb_bv]; exact hnb_max) hwf.1
                    (fun hge => by rw [hvalR] at hge; rw [htrimR]; exact halloc hge)
                    (by dsimp only [R_abOut] at hm1; sep_use hm1)
                  intro p st' objs' m2 hmst hrem hb' hrep hsm hbg hm2
                  c0_step
                  have hqr_len : (qXs' ++ rXs').length = scrOut.length := by
                    rw [List.length_append, hlenQ, hlenR, List.length_take_of_le (by omega),
                      List.length_drop]; omega
                  have hq'_len : qXs'.length = limbLenNat aVal := by
                    rw [hlenQ, List.length_take_of_le (by omega)]
                  have hm2' : (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
                    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                    array64 scr scrA' ⋆
                    array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal)) scrB' ⋆
                    array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal + limbLenNat bVal)))
                      (qXs' ++ rXs') ⋆
                    lcnfHeap objs' ⋆ R) m2 := by
                    rw [array64_append, hq'_len]
                    try rw [Nat.mul_comm (limbLenNat aVal) 8]
                    sep_use hm2
                  rw [hvalR] at hrep hsm hbg
                  refine hfinish hqr_len hmst hrem hb' ?_ hm2'
                  dsimp only [natArithPost, natArithRes]
                  refine ⟨hrep, fun o ho => ?_⟩
                  by_cases hs : aVal % bVal < 2 ^ 63
                  · rw [hsm hs]; exact ho
                  · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
                    exact List.mem_cons_of_mem _ ho
          · apply wp_jnz_false (beq_false_of_ne h5)
            have hop678 : op.toNat ∈ [6, 7, 8] := by
              have : op.toNat ≠ 1 ∧ op.toNat ≠ 2 ∧ op.toNat ≠ 3 ∧ op.toNat ≠ 4 ∧ op.toNat ≠ 5 := by
                refine ⟨fun h => h1 (BitVec.eq_of_toNat_eq (by simpa using h)),
                  fun h => h2 (BitVec.eq_of_toNat_eq (by simpa using h)),
                  fun h => h3 (BitVec.eq_of_toNat_eq (by simpa using h)),
                  fun h => h4 (BitVec.eq_of_toNat_eq (by simpa using h)),
                  fun h => h5 (BitVec.eq_of_toNat_eq (by simpa using h))⟩
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hop ⊢
              omega
            exact lcnf_nat_arith_op678_wp rt op aVal bVal st scr scrLimbs scrA' scrB' scrOut objs R
              m
              Q X hwf hop678 hna_max hnb_max hna_leA hnb_leB hvalA' hvalB' hlenTot' hlenA hlenB hm
              hQ

theorem lcnf_nat_arith_wp (xs : Tup Val [i64, i64, i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (h : lcnfNatArithSpec xs m Q X) :
    Func.wp rtR1Env lcnf_nat_arith.body xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rcases h with ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb_opt, hok, hm, hQ⟩
  dsimp only [Func.wp, lcnf_nat_arith, lcnf_nat_arith_body]
  c0_let_simp
  by_cases h17 : op = 17#64
  · subst h17
    apply wp_jnz_true (by decide)
    exact lcnf_nat_arith_pred_wp rt a aVal bVal st scr scrLimbs objs R m Q X hwf ha hok hm hQ
  · have h17n : op.toNat ≠ 17 := fun h => h17 (BitVec.eq_of_toNat_eq (by simpa using h))
    have hb : natRep b bVal objs := by
      rcases hb_opt with h | h
      · exact absurd h h17n
      · exact h
    have hneed : 2 * (limbLenNat aVal + limbLenNat bVal) + 2 ≤ scrLimbs.length := by
      have hok' := hok
      dsimp only [natArithOk] at hok'
      simp only [h17n, ↓reduceIte] at hok'
      split at hok'
      · exact hok'.1
      · split at hok'
        · exact hok'
        · exact False.elim hok'
    have hop18 : op.toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8] := by
      have hok' := hok
      dsimp only [natArithOk] at hok'
      simp only [h17n, ↓reduceIte] at hok'
      split at hok' <;> rename_i h15
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h15 ⊢; omega
      · split at hok' <;> rename_i h68
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h68 ⊢; omega
        · exact False.elim hok'
    apply wp_jnz_false (beq_false_of_ne h17)
    rcases hwf with ⟨hb48, hrt64, hscr0, hscra, hscrlen, hscr64⟩
    have hwf' : BigNumRtWf rt st scr scrLimbs := ⟨hb48, hrt64, hscr0, hscra, hscrlen, hscr64⟩
    have hna_max : limbLenNat aVal ≤ mpzMaxLimbs := limbLenNat_le_max_of_natRep ha
    have hnb_max : limbLenNat bVal ≤ mpzMaxLimbs := limbLenNat_le_max_of_natRep hb
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
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hna_max; omega)] at this
        unfold mpzMaxLimbs at hna_max; omega
      have hugb : (33554429#64 : BitVec 64).ult (BitVec.ofNat 64 (limbLenNat bVal)) = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        have : (33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 (limbLenNat bVal)).toNat :=
          of_decide_eq_true ht
        rw [show (33554429#64 : BitVec 64).toNat = 33554429 from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hnb_max; omega)] at this
        unfold mpzMaxLimbs at hnb_max; omega
      apply wp_jnz_false huga
      apply wp_jnz_false hugb
      apply wp_join_group (fun _ m' => m' = m)
      · intro _ _ m' hm'
        subst hm'
        simp only [Blocks.get]
        c0_let_simp
        have hna_bv : (BitVec.ofNat 64 (limbLenNat aVal)).toNat = limbLenNat aVal := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hna_max; omega)]
        have hnb_bv : (BitVec.ofNat 64 (limbLenNat bVal)).toNat = limbLenNat bVal := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hnb_max; omega)]
        have hneed_bv :
            ((2 : BitVec 64) * (BitVec.ofNat 64 (limbLenNat aVal) +
              BitVec.ofNat 64 (limbLenNat bVal)) +
              (2 : BitVec 64)).toNat = 2 * (limbLenNat aVal + limbLenNat bVal) + 2 := by
          rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_add, hna_bv, hnb_bv]
          have hlt : 2 * (limbLenNat aVal + limbLenNat bVal) + 2 < 2 ^ 64 := by
            unfold mpzMaxLimbs at hna_max hnb_max; omega
          simp [Nat.mod_eq_of_lt (by omega : limbLenNat aVal + limbLenNat bVal < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 2 * (limbLenNat aVal + limbLenNat bVal) < 2 ^ 64),
            Nat.mod_eq_of_lt hlt]
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
        have hlenA' : scrA'.length = limbLenNat aVal := by
          rw [hlenA, List.length_take_of_le hna_le_scr]
        have hlenB' : scrB'.length = limbLenNat bVal := by
          rw [hlenB, List.length_take_of_le hnb_le_rest]
        have hlenTot : scrA'.length + scrB'.length +
            (scrLimbs.drop (limbLenNat aVal + limbLenNat bVal)).length = scrLimbs.length := by
          rw [hlenA', hlenB', List.length_drop]; omega
        exact lcnf_nat_arith_op123_wp rt op aVal bVal st scr scrLimbs scrA' scrB'
          (scrLimbs.drop (limbLenNat aVal + limbLenNat bVal)) objs R m2 Q X hwf' hop18 hlenA' hlenB'
          hvalA hvalB hlenTot hneed hna_max hnb_max hok (by sep_use hm2) hQ
      · intro Js hJs
        c0_let_simp
        by_cases hgt : (BitVec.ofNat 64 (limbLenNat bVal)).ult (BitVec.ofNat 64 (limbLenNat aVal)) =
          true
        · apply wp_jnz_true hgt
          rw [wp_jump]; exact hJs (BitVec.ofNat 64 (limbLenNat aVal), ()) m rfl
        · have hgtf : (BitVec.ofNat 64 (limbLenNat bVal)).ult (BitVec.ofNat 64 (limbLenNat aVal)) =
          false :=
            Bool.eq_false_iff.mpr hgt
          apply wp_jnz_false hgtf
          rw [wp_jump]; exact hJs (BitVec.ofNat 64 (limbLenNat bVal), ()) m rfl

theorem lcnf_nat_arith_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt op a b : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal bVal : Nat} {R : Mem 64 → Prop}
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (ha : natRep a aVal objs) (hb : op.toNat = 17 ∨ natRep b bVal objs)
    (hok : natArithOk op.toNat aVal bVal scrLimbs.length st)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natArithPost op.toNat aVal bVal res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "lcnf_nat_arith"
        (Arg.var rt, Arg.var op, Arg.var a, Arg.var b, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_lcnf_nat_arith
  exact ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb, hok, hm, hk⟩


end LeanQbe.T.LeanLCNF
