module

public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof0

/-!
# Dual-Arch WP Proof for `FactLoop` (`LcnfC0LoopDemoProof1`)

Section 2: strengthened `loopRtEnv` bump-arena specs (`lcnf_nat_alloc_rem_wp`,
`bn_nat_from_limbs_rem_wp`, `lcnf_nat_mul_arith_wp`, `lcnf_nat_mul_slow_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T LeanQbe.T.Frontend.C0 LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Std Std.ExtHashMap
open scoped LeanQbe.T.ProofUtil

/-! ## 2. Strengthened Runtime Arithmetic / Alloc Specs & `loopRtEnv` -/
@[expose] def mpzZeroObj (p : BitVec 64) (n' : Nat) : BigNumRt.LcnfObj :=
  let bytes := 16 + 8 * n'
  { addr := p, rc := 1#32, csSz := if bytes < 65536 then bytes else 0, other := 0,
    tag := BigNumRt.mpzTag, cap := n', arrSize := n', limbs := List.replicate n' 0#64 }
/-- `lcnfNatAllocSpec` retaining exact remaining
bump-arena lower bound `st.rem - bytes ≤ st'.rem`. -/
@[expose] def lcnfNatAllocRemSpec : Spec [i64, i64] [i64] :=
  fun (rt, nlimbs, ()) m Q _X =>
    let n' := max 1 nlimbs.toNat
    let bytes := 16 + 8 * n'
    ∃ (st : BigNumRt.RtC0State) (R : Mem 64 → Prop),
      nlimbs.toNat ≤ mpzMaxLimbs ∧
      st.Bounded48 ∧
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      (BigNumRt.rtC0Inv rt st ⋆ R) m ∧
      ∀ (p : BitVec 64) (st' : BigNumRt.RtC0State) (m' : Mem 64),
        (mpzZeroObj p n').Wf →
        p &&& 1#64 = 0#64 →
        st'.PreservesMeta st →
        st'.rem ≤ st.rem →
        st.rem - bytes ≤ st'.rem →
        st'.Bounded48 →
        (BigNumRt.rtC0Inv rt st' ⋆ BigNumRt.lcnfObjMem (mpzZeroObj p n') ⋆ R) m' →
        Q (p, ()) m'
/-- `bnNatFromLimbsSpec` retaining `newObj.rc = 1#32`, `st'.rem = st.rem` (small), and
`st.rem - (16 + 8 * tn) ≤ st'.rem` (boxed). -/
@[expose] def bnNatFromLimbsRemSpec : Spec [i64, i64, i64] [i64] :=
  fun (rt, buf, n, ()) m Q _X =>
    ∃ (st : BigNumRt.RtC0State) (bufXs : List (BitVec 64)) (objs : List BigNumRt.LcnfObj)
      (R : Mem 64 → Prop),
      let val := limbsVal (bufXs.take n.toNat)
      let tn := trimLenLoop bufXs n.toNat
      n.toNat ≤ bufXs.length ∧
      n.toNat ≤ mpzMaxLimbs ∧
      st.Bounded48 ∧
      (2 ^ 63 ≤ val → st.hasFree (16 + 8 * tn) ∨ 16 + 8 * tn ≤ st.rem) ∧
      (BigNumRt.rtC0Inv rt st ⋆ array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R) m ∧
      ∀ (p : BitVec 64) (st' : BigNumRt.RtC0State) (objs' : List BigNumRt.LcnfObj)
        (m' : Mem 64),
        st'.PreservesMeta st →
        st'.rem ≤ st.rem →
        st'.Bounded48 →
        natRep p val objs' →
        (val < 2 ^ 63 → st'.rem = st.rem ∧ objs' = objs) →
        (2 ^ 63 ≤ val →
          st.rem - (16 + 8 * tn) ≤ st'.rem ∧
          ∃ newObj, newObj.addr = p ∧ newObj.rc = 1#32 ∧ mpzNatCanon newObj val ∧
            objs' = newObj :: objs) →
        (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs' ⋆ R) m' →
        Q (p, ()) m'
/-- Multiplication (`op = 3#64`) specialization of `lcnf_nat_arith`. -/
@[expose] def loopNatMulArithSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (rt, op, a, b, ()) m Q _X =>
    op = 3#64 ∧
    ∃ (st : BigNumRt.RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
      (objs : List BigNumRt.LcnfObj) (aVal bVal : Nat) (R : Mem 64 → Prop),
      BigNumRtWf rt st scr scrLimbs ∧
      natRep a aVal objs ∧
      natRep b bVal objs ∧
      natArithOk 3 aVal bVal scrLimbs.length st ∧
      (bigNumRtInv rt st scr scrLimbs ⋆ BigNumRt.lcnfHeap objs ⋆ R) m ∧
      ∀ (res : BitVec 64) (st' : BigNumRt.RtC0State) (scrLimbs' : List (BitVec 64))
        (objs' : List BigNumRt.LcnfObj) (m' : Mem 64),
        st'.PreservesMeta st →
        st'.rem ≤ st.rem →
        scrLimbs'.length = scrLimbs.length →
        BigNumRtWf rt st' scr scrLimbs' →
        natRep res (aVal * bVal) objs' →
        (aVal * bVal < 2 ^ 63 → st'.rem = st.rem ∧ objs' = objs) →
        (2 ^ 63 ≤ aVal * bVal →
          st.rem - (16 + 8 * limbLenNat (aVal * bVal)) ≤ st'.rem ∧
          ∃ newObj, newObj.addr = res ∧ newObj.rc = 1#32 ∧ mpzNatCanon newObj (aVal * bVal) ∧
            objs' = newObj :: objs) →
        (bigNumRtInv rt st' scr scrLimbs' ⋆ BigNumRt.lcnfHeap objs' ⋆ R) m' →
        Q (res, ()) m'
/-- Multiplication (`op = 3#64`) specialization of `lcnf_nat_slow`. -/
@[expose] def loopNatMulSlowSpec : Spec [i64, i64, i64, i64] [i64] :=
  loopNatMulArithSpec
/-- Two-limb `mpz` specialization of `lcnf_nat_to_str` without requiring `nObj.csSz = 0`. -/
@[expose] def loopNatToStr2Spec : Spec [i64, i64] [i64] :=
  fun (rt, n, ()) m Q _X =>
    ∃ (st : BigNumRt.RtC0State) (nObj : BigNumRt.LcnfObj) (objs : List BigNumRt.LcnfObj)
      (val : Nat) (R : Mem 64 → Prop),
      (n &&& 1#64) = 0#64 ∧
      nObj ∈ objs ∧ nObj.addr = n ∧
      mpzNatCanon nObj val ∧
      nObj.limbs.length = 2 ∧
      (∀ o ∈ objs, o.Wf) ∧
      (nObj.rc = 1#32 →
        objs.length ≤ st.workCap ∧ BigNumRt.lcnfHeapClosed objs ∧ BigNumRt.RcSound n objs) ∧
      mpzAllocBytes 2 + sarrayAllocBytes 40 + strAllocBytes 41 ≤ st.rem ∧
      (BigNumRt.rtC0Inv rt st ⋆ BigNumRt.lcnfHeap objs ⋆ R) m ∧
      ∀ (s : BitVec 64) (st' : RtC0State) (objs' : List LcnfObj) (m' : Mem 64),
        s ≠ 0#64 → s.toNat % 8 = 0 →
        st'.PreservesMeta (b2rState st) → st'.rem ≤ st.rem →
        have dec := natToDecimalBytes val
        have sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
        StrCanon sObj →
        DecObjRel n (objs.map b2rObj) objs' →
        (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R) m' →
        Q (s, ()) m'
/-- Additional strengthened R1/R2b specifications adjoined to `rtC0CoreEnv` in `loopRtEnv`. -/
@[expose] def extraLoopRtEnv : Env := fun f as bs xs m Q X =>
  (∃ (h : as = [i64, i64] ∧ bs = [i64]),
    f = "lcnf_nat_alloc" ∧ lcnfNatAllocRemSpec (h.1 ▸ xs) m (h.2 ▸ Q) X) ∨
  (∃ (h : as = [i64, i64, i64] ∧ bs = [i64]),
    f = "bn_nat_from_limbs" ∧ bnNatFromLimbsRemSpec (h.1 ▸ xs) m (h.2 ▸ Q) X) ∨
  (∃ (h : as = [i64, i64, i64, i64] ∧ bs = [i64]),
    f = "lcnf_nat_arith" ∧ loopNatMulArithSpec (h.1 ▸ xs) m (h.2 ▸ Q) X) ∨
  (∃ (h : as = [i64, i64, i64, i64] ∧ bs = [i64]),
    f = "lcnf_nat_slow" ∧ loopNatMulSlowSpec (h.1 ▸ xs) m (h.2 ▸ Q) X) ∨
  (∃ (h : as = [i64, i64] ∧ bs = [i64]),
    f = "lcnf_nat_to_str" ∧ loopNatToStr2Spec (h.1 ▸ xs) m (h.2 ▸ Q) X)
/-- Runtime proof environment extending `rtC0CoreEnv` with `extraLoopRtEnv`. -/
@[expose] def loopRtEnv : Env := fun f as bs xs m Q X =>
  rtC0CoreEnv f as bs xs m Q X ∨ extraLoopRtEnv f as bs xs m Q X
theorem rtC0CoreEnv_le_loopRtEnv :
    ∀ g as bs xs m P E, rtC0CoreEnv g as bs xs m P E → loopRtEnv g as bs xs m P E :=
  fun _ _ _ _ _ _ _ h => Or.inl h
theorem rtR1Env_le_loopRtEnv :
    ∀ g as bs xs m P E, rtR1Env g as bs xs m P E → loopRtEnv g as bs xs m P E :=
  fun _ _ _ _ _ _ _ h => Or.inl (rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ h)
theorem mpzObjLimbs_wf {p : BitVec 64} {n' : Nat} {limbs : List (BitVec 64)}
    (hn1 : 1 ≤ n') (hnmax : n' ≤ mpzMaxLimbs)
    (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0) (hlen : limbs.length = n') :
    let bytes := 16 + 8 * n'
    ({ addr := p, rc := 1#32, csSz := if bytes < 65536 then bytes else 0, other := 0,
       tag := BigNumRt.mpzTag, cap := n', arrSize := n', limbs := limbs } :
       BigNumRt.LcnfObj).Wf := by
  unfold BigNumRt.LcnfObj.Wf BigNumRt.LcnfObj.totalBytes
  simp only [BigNumRt.mpzTag, closureTag, BigNumRt.arrayTag, BigNumRt.sarrayTag,
    BigNumRt.stringTag, BigNumRt.rtMinObjBytes, BigNumRt.rtMaxObjBytes, mpzMaxLimbs,
    hlen, show (250 = 245) = False by decide,
    show (250 = 246) = False by decide, show (250 = 248) = False by decide,
    show (250 = 249) = False by decide, ite_false, ite_true] at *
  refine ⟨hp0, hp8, by decide, ?_, by decide, by decide, by omega, by omega, by omega,
    trivial, hnmax, by omega⟩
  split <;> omega
theorem mpzObj_wf {p : BitVec 64} {n' : Nat}
    (hn1 : 1 ≤ n') (hnmax : n' ≤ mpzMaxLimbs)
    (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0) :
    (mpzZeroObj p n').Wf :=
  mpzObjLimbs_wf hn1 hnmax hp0 hp8 (List.length_replicate)
theorem align8_mpz_bytes (n' : Nat) : align8 (16 + 8 * n') = 16 + 8 * n' := by
  unfold align8
  omega
theorem wp_call_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {f : Sym} {as bs : List Ty} (args : Tup (Arg Val) as) (k : Tup Val bs → Expr Val Cont rs)
    (h : Γ f as bs (vals args) m (fun r m' => wp Γ Q X (k r) m') X) :
    wp Γ Q X (.call f (bs := bs) args k) m := by
  simp only [wp]
  exact ⟨_, X, h, fun _ _ hr => hr, fun _ _ _ _ he => he⟩
private theorem wp_call_step' {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {f : Sym} {as bs : List Ty} {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs}
    (h : Γ f as bs (vals args) m (fun r m' => wp Γ Q X (k r) m') X) :
    wp Γ Q X (.call f (bs := bs) args k) m :=
  wp_call_step args k h
theorem lcnf_nat_alloc_rem_wp (xs : Tup Val [i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    lcnfNatAllocRemSpec xs m Q X → Func.wp loopRtEnv lcnf_nat_alloc.body xs m Q X := by
  rcases xs with ⟨rt, nlimbs, ⟨⟩⟩
  rintro ⟨st, R, hmax, hb48, hroom, hm, hk⟩
  dsimp only [Func.wp, lcnf_nat_alloc, lcnf_nat_alloc_body]
  let n' := max 1 nlimbs.toNat
  let bytes := 16 + 8 * n'
  have hn1 : 1 ≤ n' := Nat.le_max_left 1 nlimbs.toNat
  have hnmax : n' ≤ mpzMaxLimbs := by dsimp only [n', mpzMaxLimbs] at hmax ⊢; omega
  have hnbv : (BitVec.ofNat 64 n').toNat = n' := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [mpzMaxLimbs] at hnmax; omega)]
  have hn'_eq : (if nlimbs = 0#64 then 1#64 else nlimbs) = BitVec.ofNat 64 n' := by
    by_cases h0 : nlimbs = 0#64
    · subst h0; simp [n']
    · have hpos : 0 < nlimbs.toNat := by
        refine Classical.byContradiction fun hle => ?_
        exact h0 (BitVec.eq_of_toNat_eq (by simp; omega))
      simp [h0, n', Nat.max_eq_right hpos, BitVec.ofNat_toNat]
  have hbytes_bv : (16#64 + 8#64 * BitVec.ofNat 64 n') = BitVec.ofNat 64 bytes := by
    apply BitVec.eq_of_toNat_eq
    have hlt : bytes < 2 ^ 64 := by dsimp only [bytes, mpzMaxLimbs] at hnmax ⊢; omega
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hnbv, bytes]
    omega
  refine wp_join_group (Γ := loopRtEnv)
    (fun (n'v, ()) m1 => m1 = m ∧ n'v = BitVec.ofNat 64 n') ?_ ?_
  · rintro J ⟨n'v, ⟨⟩⟩ m1 ⟨rfl, rfl⟩
    c0_hstraight
    have hnotgt : BitVec.ult 33554429#64 (BitVec.ofNat 64 n') = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, hnbv]
      dsimp only [mpzMaxLimbs] at hnmax; omega
    refine LeanQbe.T.wp_jnz_false (Γ := loopRtEnv) hnotgt ?_
    let csSz := if bytes < 65536 then bytes else 0
    have hblt : bytes < 2 ^ 64 := by dsimp only [bytes, mpzMaxLimbs] at hnmax ⊢; omega
    have hbytes_nat : (BitVec.ofNat 64 bytes).toNat = bytes := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hblt]
    have hcsSz_eq :
        (if BitVec.ult (16#64 + 8#64 * BitVec.ofNat 64 n') 65536#64 then
          16#64 + 8#64 * BitVec.ofNat 64 n' else 0#64) = BitVec.ofNat 64 csSz := by
      rw [hbytes_bv]
      by_cases hcs : bytes < 65536
      · have hult : BitVec.ult (BitVec.ofNat 64 bytes) 65536#64 = true := by
          simp only [BitVec.ult, decide_eq_true_eq, hbytes_nat]
          exact Nat.lt_of_lt_of_eq hcs rfl
        simp [hult, csSz, hcs]
      · have hult : BitVec.ult (BitVec.ofNat 64 bytes) 65536#64 = false := by
          simp only [BitVec.ult, decide_eq_false_iff_not, hbytes_nat]
          exact fun hlt => hcs (Nat.lt_of_lt_of_eq hlt rfl)
        simp [hult, csSz, hcs]
    c0_hstraight
    refine wp_join_group (Γ := loopRtEnv)
      (fun (csV, ()) m2 => m2 = m1 ∧ csV = BitVec.ofNat 64 csSz) ?_ ?_
    · rintro J2 ⟨csV, ⟨⟩⟩ m2 ⟨rfl, hcsV⟩
      c0_hsteps!
      apply wp_call_step
      apply rtC0CoreEnv_le_loopRtEnv
      apply rtC0CoreEnv_lcnf_alloc
      rw [b2r_rtC0Inv_eq] at hm
      have hbytes_arg : (16#64 + 8#64 * BitVec.ofNat 64 n') = BitVec.ofNat 64 bytes := hbytes_bv
      change lcnfAllocRemSpec (rt, (16#64 + 8#64 * BitVec.ofNat 64 n'), ()) m2 _ X
      rw [hbytes_arg]
      have hal8 : align8 (BitVec.ofNat 64 bytes).toNat = bytes := by
        rw [hbytes_nat]; exact align8_mpz_bytes n'
      have hle_max : (BitVec.ofNat 64 bytes).toNat ≤ 268435448 := by
        rw [hbytes_nat]; dsimp only [bytes, mpzMaxLimbs] at hnmax ⊢; omega
      have hmin : rtMinObjBytes ≤ align8 (BitVec.ofNat 64 bytes).toNat := by
        rw [hal8]; dsimp only [rtMinObjBytes, bytes]; omega
      have hmax_o : align8 (BitVec.ofNat 64 bytes).toNat < rtMaxObjBytes := by
        rw [hal8]; dsimp only [rtMaxObjBytes, bytes, mpzMaxLimbs] at hnmax ⊢; omega
      have hroom' : (b2rState st).hasFree (align8 (BitVec.ofNat 64 bytes).toNat) ∨
          align8 (BitVec.ofNat 64 bytes).toNat ≤ (b2rState st).rem := by
        rw [hal8]; exact hroom
      refine ⟨b2rState st, R, hle_max, hmin, hmax_o, hroom', hm, ?_⟩
      intro p st' m2 hp0 hp8 hmeta hrem_le hrem_lb hm2
      rw [hal8] at hm2 hrem_lb
      rw [sep_comm (rtC0Inv rt st'), sep_assoc] at hm2
      obtain ⟨w0, w1, dst, hdst_len, hm2'⟩ := region_to_mpz_parts hn1 hnmax hm2
      let obj : BigNumRt.LcnfObj :=
        { addr := p, rc := 1#32, csSz := csSz, other := 0, tag := BigNumRt.mpzTag,
          cap := n', arrSize := n', limbs := List.replicate n' 0#64 }
      have hobj_wf : obj.Wf := mpzObj_wf hn1 hnmax hp0 hp8
      have hh_hdr :
          (1#64 ||| csV <<< ((BitVec.signExtend 64 32#32).toNat % 64) |||
            250#64 <<< ((BitVec.signExtend 64 56#32).toNat % 64)) = obj.header := by
        subst hcsV
        rw [show (BitVec.signExtend 64 32#32).toNat % 64 = 32 from rfl,
          show (BitVec.signExtend 64 56#32).toNat % 64 = 56 from rfl]
        have h0s : (0#64 : BitVec 64) <<< 48 = 0#64 := rfl
        have h1s : (1#32 : BitVec 32).toNat = 1 := rfl
        simp only [obj, BigNumRt.LcnfObj.header, BigNumRt.mpzTag, h0s, h1s, BitVec.or_zero]
      have hh_meta :
          (BitVec.ofNat 64 n' |||
            BitVec.ofNat 64 n' <<< ((BitVec.signExtend 64 32#32).toNat % 64)) =
            obj.mpzMeta := by
        rw [show (BitVec.signExtend 64 32#32).toNat % 64 = 32 from rfl]
        rfl
      have hm2_w0 : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆
          array64 (p + 16#64) dst ⋆ R ⋆ rtC0Inv rt st')) m2 := sep_ac hm2'
      clear hm2 hm2'
      t_wp_unfold
      erw [hh_hdr, hh_meta]
      have hs1 := store_cell64 obj.header hm2_w0
      have hs2 := store_cell64 obj.mpzMeta (R := rtC0Inv rt st' ⋆ cell64 p obj.header ⋆
        array64 (p + 16#64) dst ⋆ R) (sep_ac hs1.2)
      refine ⟨hs1.1, hs2.1, ?_⟩
      refine wp_loop_inv (Γ := loopRtEnv)
        (fun (i, ()) m_cur =>
          i.toNat ≤ n' ∧
          (array64 (p + 16#64) (List.replicate i.toNat 0#64 ++ dst.drop i.toNat) ⋆
            rtC0Inv rt st' ⋆ cell64 p obj.header ⋆ cell64 (p + 8#64) obj.mpzMeta ⋆ R) m_cur)
        (fun (i, ()) _ => n' - i.toNat) ?_ ?_
      · intro J3 hJ3
        apply hJ3 (0#64, ()) _ ⟨Nat.zero_le _, ?_⟩
        simp only [BitVec.toNat_zero, List.replicate_zero, List.nil_append, List.drop_zero]
        exact sep_ac hs2.2
      · rintro J3 ⟨i, ⟨⟩⟩ m_cur ⟨hi_le, hm_cur⟩ hRec
        t_wp_unfold
        refine ⟨fun hc_t => ?_, fun hc_f => ?_⟩
        · have hilt : i.toNat < n' := by
            rw [BitVec.ult, decide_eq_true_eq, hnbv] at hc_t; exact hc_t
          have hlen_cur : (List.replicate i.toNat 0#64 ++ dst.drop i.toNat).length = n' := by
            simp only [List.length_append, List.length_replicate, List.length_drop, hdst_len]
            omega
          have hidx_cur : i.toNat < (List.replicate i.toNat 0#64 ++ dst.drop i.toNat).length := by
            omega
          have haddr_off :
              p + (2 + i) * 8 = (p + 16#64) + BitVec.ofNat 64 (8 * i.toNat) := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_mul]
            have h2 : (2 : BitVec 64).toNat = 2 := rfl
            have h8 : (8 : BitVec 64).toNat = 8 := rfl
            have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
            rw [h2, h8, h16, BitVec.toNat_ofNat]
            omega
          obtain ⟨hst_ok, hst_mem⟩ := store_array64 (a := p + 16#64) (0#64)
            (R := rtC0Inv rt st' ⋆ cell64 p obj.header ⋆ cell64 (p + 8#64) obj.mpzMeta ⋆ R)
            hidx_cur (sep_ac hm_cur)
          rw [zeroPrefix_set (dst := dst) (hdst_len.symm ▸ hilt)] at hst_mem
          have hi_inc : (i + 1#64).toNat = i.toNat + 1 := by
            have hsmall : i.toNat < 2 ^ 64 - 1 := by
              dsimp only [mpzMaxLimbs] at hnmax; omega
            simp [BitVec.toNat_add]
          erw [haddr_off]
          refine ⟨hst_ok, ?_⟩
          apply hRec (i + 1#64, ()) _ (by dsimp only; rw [hi_inc]; omega)
            ⟨by rw [hi_inc]; exact hilt, ?_⟩
          rw [hi_inc, show (0 : BitVec 64) = 0#64 from rfl]
          exact sep_ac hst_mem
        · have hieq : i.toNat = n' := by
            rw [BitVec.ult, decide_eq_false_iff_not, hnbv] at hc_f; omega
          rw [hieq, show dst.drop n' = [] from List.drop_eq_nil_of_le (le_of_eq hdst_len),
            List.append_nil] at hm_cur
          have hm_r2b :
              (cell64 obj.addr obj.header ⋆ cell64 (obj.addr + 8#64) obj.mpzMeta ⋆
                array64 (obj.addr + 16#64) obj.limbs ⋆
                (BigNumRt.rtC0Inv rt (r2bState st') ⋆ R)) m_cur := by
            rw [← r2b_rtC0Inv_eq]
            exact sep_ac hm_cur
          have hm_obj :
              (BigNumRt.rtC0Inv rt (r2bState st') ⋆ BigNumRt.lcnfObjMem obj ⋆ R) m_cur :=
            sep_ac (lcnfObjMem_mpz_intro (o := obj) rfl hm_r2b)
          have hp_align : p &&& 1#64 = 0#64 := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.and_one_is_mod]
            omega
          exact hk p (r2bState st') m_cur hobj_wf hp_align
            (by simpa [r2bState_b2rState] using r2bState_preservesMeta hmeta)
            (by simpa [r2bState_rem, b2rState_rem] using hrem_le)
            (by rw [r2bState_rem, ← b2rState_rem]; exact hrem_lb)
            (r2bState_bounded48 hb48 hmeta) hm_obj
    · intro J2 hJ2
      c0_hsteps!
      · have hlt : bytes < 65536 := by
          change (16 + 8 * (n' % 2 ^ 64)) % 2 ^ 64 < 65536 at hc
          have hblt : bytes < 2 ^ 64 := by dsimp only [bytes, mpzMaxLimbs] at hnmax ⊢; omega
          dsimp only [bytes] at hblt ⊢; omega
        exact hJ2 _ _ ⟨rfl, by simp [csSz, hlt, hbytes_bv]⟩
      · have hnlt : ¬ (bytes < 65536) := by
          change ¬ ((16 + 8 * (n' % 2 ^ 64)) % 2 ^ 64 < 65536) at hc
          have hblt : bytes < 2 ^ 64 := by dsimp only [bytes, mpzMaxLimbs] at hnmax ⊢; omega
          dsimp only [bytes] at hblt ⊢; omega
        exact hJ2 _ _ ⟨rfl, by simp [csSz, hnlt]⟩
  · intro J hJ
    c0_hsteps!
    · exact hJ _ _ ⟨rfl, by simp [n', hc]⟩
    · exact hJ _ _ ⟨rfl, by rw [← hn'_eq]; split <;> first | contradiction | rfl⟩
theorem preservesMeta_bn_refl (st : BigNumRt.RtC0State) : st.PreservesMeta st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
private theorem limbsVal_take_one {xs : List (BitVec 64)} (hne : 0 < xs.length) :
    limbsVal (xs.take 1) = (xs[0]).toNat := by
  cases xs with
  | nil => simp at hne
  | cons x _ => simp [limbsVal]
private theorem tn_eq_limbLen_of_ge {xs : List (BitVec 64)} {n : Nat}
    (hn : n ≤ xs.length) (hval_ge : 2 ^ 63 ≤ limbsVal (xs.take n)) :
    let tn := trimLenLoop xs n
    tn = limbLenNat (limbsVal (xs.take n)) := by
  intro tn
  have hle : tn ≤ n := trimLenLoop_le xs n
  have hval_eq : limbsVal (xs.take tn) = limbsVal (xs.take n) :=
    limbsVal_trimLenLoop xs n hn
  have hpos_val : limbsVal (xs.take n) ≠ 0 := by
    have h63 : 0 < 2 ^ 63 := by decide
    omega
  have htn_pos : 0 < tn := by
    refine Classical.byContradiction fun h0 => ?_
    have htn0 : tn = 0 := by omega
    rw [htn0, List.take_zero, limbsVal_nil] at hval_eq
    exact hpos_val hval_eq.symm
  have hlast := getLast_take_ne_zero xs n htn_pos hn
  have htk_len : (xs.take tn).length = tn := List.length_take_of_le (le_trans hle hn)
  have htk_ne : xs.take tn ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil] at htk_len
    omega
  have hlow := limbsVal_ge_pow_of_nonzero_last htk_ne (by
    rwa [list_getLast_eq_getLast! _ htk_ne])
  have hhi := limbsVal_lt_pow (xs.take tn)
  rw [htk_len, hval_eq] at hlow hhi
  simp only [limbLenNat, hpos_val, ↓reduceIte]
  have h1 : 64 * (tn - 1) ≤ (limbsVal (xs.take n)).log2 := (Nat.le_log2 hpos_val).mpr hlow
  have h2 : (limbsVal (xs.take n)).log2 < 64 * tn := (Nat.log2_lt hpos_val).mpr hhi
  omega
theorem bn_nat_from_limbs_rem_wp (xs : Tup Val [i64, i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    bnNatFromLimbsRemSpec xs m Q X → Func.wp loopRtEnv bn_nat_from_limbs.body xs m Q X := by
  rcases xs with ⟨rt, buf, n, ⟨⟩⟩
  rintro ⟨st, bufXs, objs, R, hn_len, hn_max, hb48, hroom, hm, hk⟩
  dsimp only [Func.wp, bn_nat_from_limbs, bn_nat_from_limbs_body]
  let val := limbsVal (bufXs.take n.toNat)
  let tn := trimLenLoop bufXs n.toNat
  have htn_le : tn ≤ n.toNat := trimLenLoop_le bufXs n.toNat
  have htn_len : tn ≤ bufXs.length := le_trans htn_le hn_len
  have htn_max : tn ≤ mpzMaxLimbs := le_trans htn_le hn_max
  have htn_lt64 : tn < 2 ^ 64 := by dsimp only [mpzMaxLimbs] at htn_max; omega
  have htn_bv : (BitVec.ofNat 64 tn).toNat = tn := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htn_lt64]
  have hval_eq : limbsVal (bufXs.take tn) = val := limbsVal_trimLenLoop bufXs n.toNat hn_len
  apply wp_call_step
  dsimp only [vals, Arg.val]
  apply rtR1Env_le_loopRtEnv
  apply rtR1Env_bn_trim
  refine ⟨bufXs, BigNumRt.rtC0Inv rt st ⋆ BigNumRt.lcnfHeap objs ⋆ R, hn_len, sep_ac hm, ?_⟩
  t_wp_unfold
  refine ⟨fun hc0 => ?_, fun hcn0 => ?_⟩
  · have htn0 : tn = 0 := by
      have hc0' : BitVec.ofNat 64 tn = 0#64 := by simpa using hc0
      have := congrArg BitVec.toNat hc0'
      simpa [htn_bv] using this
    have hval0 : val = 0 := by
      rw [← hval_eq, htn0, List.take_zero, limbsVal_nil]
    have hlt63 : val < 2 ^ 63 := by rw [hval0]; decide
    have hrep0 : natRep 1#64 val objs := by
      simp [natRep, hval0]
    exact hk 1#64 st objs m (preservesMeta_bn_refl st) (Nat.le_refl _) hb48 hrep0
      (fun _ => ⟨rfl, rfl⟩) (fun hge => absurd hlt63 (Nat.not_lt.mpr hge)) hm
  · have htn_pos : 0 < tn := by
      refine Classical.byContradiction fun hle => ?_
      have htn0 : tn = 0 := by omega
      apply hcn0
      rw [show trimLenLoop bufXs (BitVec.toNat n) = 0 from htn0]
      rfl
    refine wp_join_group (Γ := loopRtEnv) (fun () m1 => m1 = m ∧ 2 ^ 63 ≤ val) ?_ ?_
    · rintro J ⟨⟩ m1 ⟨rfl, hge63⟩
      t_wp_unfold
      apply wp_call_step
      dsimp only [vals, Arg.val]
      refine Or.inr (Or.inl ⟨⟨rfl, rfl⟩, rfl, ?_⟩)
      have hmax1 : max 1 tn = tn := Nat.max_eq_right htn_pos
      refine ⟨st, array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R,
        by rw [htn_bv]; exact htn_max, hb48,
        by rw [htn_bv, hmax1]; exact hroom hge63, sep_ac hm, ?_⟩
      intro p st' m2 hobj_wf hp_align hmeta hrem_le hrem_lb hb48' hm2
      rw [htn_bv, hmax1] at hm2 hrem_lb hobj_wf
      let obj0 := mpzZeroObj p tn
      have hm2_elim := lcnfObjMem_mpz_elim (o := obj0)
        (R := BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R)
        rfl (sep_ac hm2)
      t_wp_unfold
      apply wp_call_step
      dsimp only [vals, Arg.val]
      apply rtR1Env_le_loopRtEnv
      apply rtR1Env_bn_copy
      refine ⟨List.replicate tn 0#64, bufXs,
        BigNumRt.rtC0Inv rt st' ⋆ cell64 p obj0.header ⋆ cell64 (p + 8#64) obj0.mpzMeta ⋆
          BigNumRt.lcnfHeap objs ⋆ R,
        by rw [htn_bv, List.length_replicate]; exact Nat.le_refl _,
        by rw [htn_bv]; exact htn_len, sep_ac hm2_elim, ?_⟩
      intro m3 hm3
      rw [htn_bv, List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil] at hm3
      let finalObj : BigNumRt.LcnfObj :=
        { addr := p, rc := 1#32,
          csSz := if 16 + 8 * tn < 65536 then 16 + 8 * tn else 0,
          other := 0, tag := BigNumRt.mpzTag, cap := tn, arrSize := tn,
          limbs := bufXs.take tn }
      have hfinal_hdr : finalObj.header = obj0.header := rfl
      have hfinal_meta : finalObj.mpzMeta = obj0.mpzMeta := rfl
      have hfinal_canon : mpzNatCanon finalObj val := by
        have hlast := getLast_take_ne_zero bufXs n.toNat htn_pos hn_len
        have htk_len : (bufXs.take tn).length = tn := List.length_take_of_le htn_len
        have hwf : finalObj.Wf := mpzObjLimbs_wf htn_pos htn_max hobj_wf.1 hobj_wf.2.1 htk_len
        exact ⟨hwf, rfl, rfl, htk_len.symm, by rw [htk_len]; exact htn_pos,
          by rw [htk_len]; exact htn_max, hlast, hval_eq, hge63⟩
      have hm3_pre :
          (cell64 finalObj.addr finalObj.header ⋆ cell64 (finalObj.addr + 8#64) finalObj.mpzMeta ⋆
            array64 (finalObj.addr + 16#64) finalObj.limbs ⋆
            (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆
              BigNumRt.lcnfHeap objs ⋆ R)) m3 := by
        rw [← hfinal_hdr, ← hfinal_meta] at hm3
        exact sep_ac hm3
      have hm3' :
          (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆
            BigNumRt.lcnfHeap (finalObj :: objs) ⋆ R) m3 := by
        rw [BigNumRt.lcnfHeap_cons_eq]
        exact sep_ac (lcnfObjMem_mpz_intro (o := finalObj) rfl hm3_pre)
      have hrep : natRep p val (finalObj :: objs) := by
        simp only [natRep, Nat.not_lt.mpr hge63, ↓reduceIte]
        exact ⟨hp_align, finalObj, List.mem_cons_self, rfl, hfinal_canon⟩
      t_wp_unfold
      exact hk p st' (finalObj :: objs) m3 hmeta hrem_le hb48' hrep
        (fun hlt => absurd hlt (Nat.not_lt.mpr hge63))
        (fun _ => ⟨hrem_lb, finalObj, rfl, rfl, hfinal_canon, rfl⟩) hm3'
    · intro J hJ
      t_wp_unfold
      refine ⟨fun hc1 => ?_, fun hcn1 => ?_⟩
      · have htn1 : tn = 1 := by
          have hc1' : BitVec.ofNat 64 tn = 1#64 := by simpa using hc1
          have := congrArg BitVec.toNat hc1'
          simpa [htn_bv] using this
        have hlen_pos : 0 < bufXs.length := by omega
        have hld : loadVal m i64 (buf + (0#64 * 8#64)) = some bufXs[0] := by
          have ha : buf + (0#64 * 8#64) = buf + BitVec.ofNat 64 (8 * 0) := by simp
          rw [ha]
          exact loadVal_array64 (a := buf)
            (R := BigNumRt.rtC0Inv rt st ⋆ BigNumRt.lcnfHeap objs ⋆ R) hlen_pos (sep_ac hm)
        refine ⟨bufXs[0], hld, ?_⟩
        have hval_ld : val = bufXs[0].toNat := by
          rw [← hval_eq, htn1]
          exact limbsVal_take_one hlen_pos
        refine ⟨fun hlt_bv => ?_, fun hnlt_bv => ?_⟩
        · have hlt63 : bufXs[0].toNat < 2 ^ 63 := by
            have hs63 :
                ((1 : BitVec 64) <<< ((BitVec.signExtend 64 (63 : BitVec 32)).toNat % 64)).toNat =
                  2 ^ 63 := by decide
            rw [BitVec.ult, decide_eq_true_eq, hs63] at hlt_bv
            exact hlt_bv
          have hval_lt : val < 2 ^ 63 := by rw [hval_ld]; exact hlt63
          have henc :
              (bufXs[0] <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) |||
                (1 : BitVec 64)) =
                BitVec.ofNat 64 (2 * val + 1) := by
            rw [show (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 from rfl, hval_ld]
            exact bv64_ofNat_small_enc hlt63
          have hrep_s : natRep (BitVec.ofNat 64 (2 * val + 1)) val objs := by
            simp [natRep, hval_lt]
          rw [henc]
          exact hk (BitVec.ofNat 64 (2 * val + 1)) st objs m (preservesMeta_bn_refl st)
            (Nat.le_refl _) hb48 hrep_s (fun _ => ⟨rfl, rfl⟩)
            (fun hge => absurd hval_lt (Nat.not_lt.mpr hge)) hm
        · have hge63 : 2 ^ 63 ≤ val := by
            have hs63 :
                ((1 : BitVec 64) <<< ((BitVec.signExtend 64 (63 : BitVec 32)).toNat % 64)).toNat =
                  2 ^ 63 := by decide
            rw [BitVec.ult, decide_eq_false_iff_not, hs63] at hnlt_bv
            rw [hval_ld]
            omega
          exact hJ () m ⟨rfl, hge63⟩
      · have htn_ne1 : tn ≠ 1 := by
          intro h1
          apply hcn1
          dsimp only [tn] at h1
          rw [h1]
          rfl
        have htn_ge2 : 2 ≤ tn := by omega
        have hlast := getLast_take_ne_zero bufXs n.toNat htn_pos hn_len
        have htk_len : (bufXs.take tn).length = tn := List.length_take_of_le htn_len
        have htk_ne : bufXs.take tn ≠ [] := by
          intro h
          rw [h, List.length_nil] at htk_len
          omega
        have hlow := limbsVal_ge_pow_of_nonzero_last htk_ne (by
          rwa [list_getLast_eq_getLast! _ htk_ne])
        rw [htk_len, hval_eq] at hlow
        have hpow63 : 2 ^ 63 ≤ 2 ^ (64 * (tn - 1)) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        exact hJ () m ⟨rfl, le_trans hpow63 hlow⟩
private theorem limbLenNat_eq_zero_iff (v : Nat) : limbLenNat v = 0 ↔ v = 0 := by
  by_cases hv : v = 0
  · subst hv; simp [limbLenNat]
  · simp [limbLenNat, hv]
private theorem loop_array64_split3 (a : BitVec 64) (xs : List (BitVec 64)) {na nb : Nat}
    (hle : na + nb ≤ xs.length) :
    array64 a xs =
      (array64 a (xs.take na) ⋆
        array64 (a + BitVec.ofNat 64 (8 * na)) ((xs.drop na).take nb) ⋆
        array64 (a + BitVec.ofNat 64 (8 * (na + nb))) (xs.drop (na + nb))) := by
  have hlenA : (xs.take na).length = na := List.length_take_of_le (by omega)
  have hlenB : ((xs.drop na).take nb).length = nb := by
    rw [List.length_take_of_le (by simp; omega)]
  have h1 : xs = xs.take na ++ ((xs.drop na).take nb ++ xs.drop (na + nb)) := by
    conv => lhs; rw [← List.take_append_drop na xs]
    congr 1
    conv => lhs; rw [← List.take_append_drop nb (xs.drop na)]
    rw [List.drop_drop]
  have haddr : (a + BitVec.ofNat 64 (8 * na)) + BitVec.ofNat 64 (8 * nb) =
      a + BitVec.ofNat 64 (8 * (na + nb)) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, Nat.mul_add, Nat.add_assoc]
  conv => lhs; rw [h1]
  rw [array64_append, hlenA, array64_append, hlenB, haddr, sep_assoc]
private theorem loop_array64_join3 (a : BitVec 64) (xs ys zs : List (BitVec 64)) :
    (array64 a xs ⋆ array64 (a + BitVec.ofNat 64 (8 * xs.length)) ys ⋆
      array64 (a + BitVec.ofNat 64 (8 * (xs.length + ys.length))) zs) =
      array64 a (xs ++ ys ++ zs) := by
  have haddr : (a + BitVec.ofNat 64 (8 * xs.length)) + BitVec.ofNat 64 (8 * ys.length) =
      a + BitVec.ofNat 64 (8 * (xs.length + ys.length)) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, Nat.mul_add, Nat.add_assoc]
  rw [sep_assoc, ← haddr, ← array64_append, ← array64_append, List.append_assoc]
theorem lcnf_nat_mul_arith_wp (xs : Tup Val [i64, i64, i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    loopNatMulArithSpec xs m Q X → Func.wp loopRtEnv lcnf_nat_arith.body xs m Q X := by
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  rintro ⟨hop, st, scr, scrLimbs, objs, aVal, bVal, R, hwf, ha, hb, hok, hm, hk⟩
  subst hop
  dsimp only [Func.wp, lcnf_nat_arith, lcnf_nat_arith_body]
  t_wp_unfold
  refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
  let na := limbLenNat aVal
  let nb := limbLenNat bVal
  have hna_max : na ≤ mpzMaxLimbs := natRep_limbLen_le ha
  have hnb_max : nb ≤ mpzMaxLimbs := natRep_limbLen_le hb
  have hna_lt64 : na < 2 ^ 64 := by dsimp only [mpzMaxLimbs] at hna_max; omega
  have hnb_lt64 : nb < 2 ^ 64 := by dsimp only [mpzMaxLimbs] at hnb_max; omega
  have hna_bv : (BitVec.ofNat 64 na).toNat = na := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna_lt64]
  have hnb_bv : (BitVec.ofNat 64 nb).toNat = nb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnb_lt64]
  have hok_mul : 2 * (na + nb) + 2 ≤ scrLimbs.length ∧
      limbLenNat (aVal * bVal) ≤ mpzMaxLimbs ∧
      (2 ^ 63 ≤ aVal * bVal → canAllocBytes st (16 + 8 * limbLenNat (aVal * bVal))) := by
    simpa [natArithOk, natArithRes, na, nb] using hok
  rcases hok_mul with ⟨hscr_cap, hres_max, hres_room⟩
  rcases hwf with ⟨hb48, hrt64, hscr0, hscr8, hlen64, hscr_bnd⟩
  apply wp_call_step
  dsimp only [vals, Arg.val]
  apply rtR1Env_le_loopRtEnv
  apply rtR1Env_bn_nat_len
  refine ⟨aVal, objs, bigNumRtInv rt st scr scrLimbs ⋆ R, ha, sep_ac hm, ?_⟩
  apply wp_call_step
  dsimp only [vals, Arg.val]
  apply rtR1Env_le_loopRtEnv
  apply rtR1Env_bn_nat_len
  refine ⟨bVal, objs, bigNumRtInv rt st scr scrLimbs ⋆ R, hb, sep_ac hm, ?_⟩
  refine wp_join_group (Γ := loopRtEnv) (fun () _ => False) (fun _ _ _ hf => hf.elim) ?_
  intro J hJ
  t_wp_unfold
  have hmaxbv : (33554429#64 : BitVec 64).toNat = 33554429 := rfl
  have hna_notgt : BitVec.ult 33554429#64 (BitVec.ofNat 64 na) = false := by
    simp only [BitVec.ult, decide_eq_false_iff_not, hna_bv, hmaxbv]
    dsimp only [mpzMaxLimbs] at hna_max; omega
  have hnb_notgt : BitVec.ult 33554429#64 (BitVec.ofNat 64 nb) = false := by
    simp only [BitVec.ult, decide_eq_false_iff_not, hnb_bv, hmaxbv]
    dsimp only [mpzMaxLimbs] at hnb_max; omega
  refine ⟨fun ht => absurd ht (by
    rw [show (33554429 : BitVec 64) = 33554429#64 from rfl]
    dsimp only [na] at hna_notgt; rw [hna_notgt]; decide), fun _ => ?_⟩
  refine ⟨fun ht => absurd ht (by
    rw [show (33554429 : BitVec 64) = 33554429#64 from rfl]
    dsimp only [nb] at hnb_notgt; rw [hnb_notgt]; decide), fun _ => ?_⟩
  refine wp_join_group (Γ := loopRtEnv) (fun (_ : Tup Val [i64]) m1 => m1 = m) ?_ ?_
  · rintro J _ m1 rfl
    t_wp_unfold
    let need := 2 * (na + nb) + 2
    have h2bv : (2 : BitVec 64).toNat = 2 := rfl
    have h8bv : (8 : BitVec 64).toNat = 8 := rfl
    have hneed_bv :
        ((2 : BitVec 64) * (BitVec.ofNat 64 na + BitVec.ofNat 64 nb) + (2 : BitVec 64)) =
          BitVec.ofNat 64 need := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, h2bv, BitVec.toNat_ofNat, hna_bv, hnb_bv,
        need]
      omega
    have hneed_lt64 : need < 2 ^ 64 := by dsimp only [need]; omega
    have hneed_nat : (BitVec.ofNat 64 need).toNat = need := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hneed_lt64]
    have hcap_nat : (BitVec.ofNat 64 scrLimbs.length).toNat = scrLimbs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64]
    apply wp_call_step
    dsimp only [vals, Arg.val]
    apply rtR1Env_le_loopRtEnv
    apply rtR1Env_bn_require_scratch
    refine ⟨scr, BitVec.ofNat 64 scrLimbs.length,
      BigNumRt.rtC0Inv rt st ⋆ array64 scr scrLimbs ⋆ BigNumRt.lcnfHeap objs ⋆ R,
      hscr0, by erw [hneed_bv, hneed_nat, hcap_nat]; exact hscr_cap, ?_, ?_⟩
    · dsimp only [bigNumRtInv] at hm; exact sep_ac hm
    have hm_split :
        (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 scr (scrLimbs.take na) ⋆
          array64 (scr + BitVec.ofNat 64 (8 * na)) ((scrLimbs.drop na).take nb) ⋆
          array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) (scrLimbs.drop (na + nb)) ⋆
          BigNumRt.lcnfHeap objs ⋆ R) m1 := by
      dsimp only [bigNumRtInv] at hm
      rw [loop_array64_split3 scr scrLimbs (na := na) (nb := nb) (by omega)] at hm
      exact sep_ac hm
    t_wp_unfold
    have hoffB :
        (scr + (8 : BitVec 64) * BitVec.ofNat 64 (limbLenNat aVal)) =
          scr + BitVec.ofNat 64 (8 * na) := by
      apply BitVec.eq_of_toNat_eq
      dsimp only [na]
      simp [BitVec.toNat_add, BitVec.toNat_mul]
    have hoffOut :
        (scr + (8 : BitVec 64) *
          (BitVec.ofNat 64 (limbLenNat aVal) + BitVec.ofNat 64 (limbLenNat bVal))) =
          scr + BitVec.ofNat 64 (8 * (na + nb)) := by
      apply BitVec.eq_of_toNat_eq
      have hsum : na + nb < 2 ^ 64 := by
        dsimp only [mpzMaxLimbs] at hna_max hnb_max ⊢; omega
      have hmul : 8 * (na + nb) < 2 ^ 64 := by
        dsimp only [mpzMaxLimbs] at hna_max hnb_max ⊢; omega
      dsimp only [na, nb] at hna_lt64 hnb_lt64 hsum hmul ⊢
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8bv,
        Nat.mod_eq_of_lt hna_lt64, Nat.mod_eq_of_lt hnb_lt64, Nat.mod_eq_of_lt hsum,
        Nat.mod_eq_of_lt hmul]
    let aXs0 := scrLimbs.take na
    let bXs0 := (scrLimbs.drop na).take nb
    let outXs0 := scrLimbs.drop (na + nb)
    have ha0_len : aXs0.length = na := List.length_take_of_le (by omega)
    have hb0_len : bXs0.length = nb := List.length_take_of_le (by simp; omega)
    have hout0_len : outXs0.length = scrLimbs.length - (na + nb) := by simp [outXs0]
    apply wp_call_step
    dsimp only [vals, Arg.val]
    apply rtR1Env_le_loopRtEnv
    apply rtR1Env_bn_load_nat
    refine ⟨aVal, objs, aXs0,
      BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 (scr + BitVec.ofNat 64 (8 * na)) bXs0 ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) outXs0 ⋆ R,
      ha, ha0_len.symm ▸ Nat.le_refl _, sep_ac hm_split, ?_⟩
    intro aXs1 m1 ha1_len ha1_val _ hm1
    rw [ha0_len] at ha1_len
    apply wp_call_step
    dsimp only [vals, Arg.val]
    apply rtR1Env_le_loopRtEnv
    apply rtR1Env_bn_load_nat
    rw [hoffB]
    refine ⟨bVal, objs, bXs0,
      BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr aXs1 ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) outXs0 ⋆ R,
      hb, hb0_len.symm ▸ Nat.le_refl _, sep_ac hm1, ?_⟩
    intro bXs1 m2 hb1_len hb1_val _ hm2
    rw [hb0_len] at hb1_len
    t_wp_unfold
    refine ⟨fun h1 => absurd h1 (by decide), fun _ => ?_⟩
    refine ⟨fun h2 => absurd h2 (by decide), fun _ => ?_⟩
    refine ⟨fun _ => ?_, fun h3 => absurd h3 (by decide)⟩
    have hscr_len' : (aXs1 ++ bXs1 ++ outXs0).length = scrLimbs.length := by
      simp [ha1_len, hb1_len, hout0_len]; omega
    have hm2_full :
        (bigNumRtInv rt st scr (aXs1 ++ bXs1 ++ outXs0) ⋆ BigNumRt.lcnfHeap objs ⋆ R) m2 := by
      dsimp only [bigNumRtInv]
      rw [← loop_array64_join3 scr aXs1 bXs1 outXs0, ha1_len, hb1_len, hscr_len']
      exact sep_ac hm2
    have hwf' : BigNumRtWf rt st scr (aXs1 ++ bXs1 ++ outXs0) :=
      ⟨hb48, hrt64, hscr0, hscr8, by rw [hscr_len']; exact hlen64,
        by rw [hscr_len']; exact hscr_bnd⟩
    have hzeroRet : na = 0 ∨ nb = 0 → Q (1, ()) m2 := by
      intro hzn
      have hprod0 : aVal * bVal = 0 := by
        rcases hzn with h0 | h0
        · rw [(limbLenNat_eq_zero_iff aVal).mp h0, Nat.zero_mul]
        · rw [(limbLenNat_eq_zero_iff bVal).mp h0, Nat.mul_zero]
      have hlt63 : aVal * bVal < 2 ^ 63 := by rw [hprod0]; decide
      have hrep0 : natRep 1#64 (aVal * bVal) objs := by simp [natRep, hprod0]
      exact hk 1#64 st (aXs1 ++ bXs1 ++ outXs0) objs m2 (preservesMeta_bn_refl st)
        (Nat.le_refl _) hscr_len' hwf' hrep0 (fun _ => ⟨rfl, rfl⟩)
        (fun hge => absurd hlt63 (Nat.not_lt.mpr hge)) hm2_full
    refine ⟨fun hna0 => hzeroRet (Or.inl (by
      have hc := congrArg BitVec.toNat hna0
      simpa [hna_bv] using hc)), fun hna_nz => ?_⟩
    refine ⟨fun hnb0 => hzeroRet (Or.inr (by
      have hc := congrArg BitVec.toNat hnb0
      simpa [hnb_bv] using hc)), fun hnb_nz => ?_⟩
    have hna_pos : na ≠ 0 := fun h0 => hna_nz (by dsimp only [na] at h0; rw [h0]; rfl)
    have hnb_pos : nb ≠ 0 := fun h0 => hnb_nz (by dsimp only [nb] at h0; rw [h0]; rfl)
    rw [hoffOut]
    apply wp_call_step
    dsimp only [vals, Arg.val]
    apply rtR1Env_le_loopRtEnv
    apply rtR1Env_bn_mul
    have hlimA : limbsVal (aXs1.take (BitVec.ofNat 64 na).toNat) = aVal := by
      rwa [hna_bv]
    have hlimB : limbsVal (bXs1.take (BitVec.ofNat 64 nb).toNat) = bVal := by
      rwa [hnb_bv]
    let tn := limbLenNat (aVal * bVal)
    have htn_eq :
        limbLenNat (limbsVal (aXs1.take (BitVec.ofNat 64 na).toNat) *
          limbsVal (bXs1.take (BitVec.ofNat 64 nb).toNat)) = tn := by
      rw [hlimA, hlimB]
    refine ⟨aXs1, bXs1, outXs0,
      BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        BigNumRt.lcnfHeap objs ⋆ R,
      by rw [hna_bv, ha1_len]; exact Nat.le_refl _,
      by rw [hnb_bv, hb1_len]; exact Nat.le_refl _,
      by rw [hna_bv, hnb_bv, hout0_len]; omega,
      by rw [hna_bv, hnb_bv]; omega, sep_ac hm2, ?_⟩
    intro outXs1 m3 hout1_len htn_le hout1_val hm3
    rw [htn_eq] at htn_le hout1_val
    rw [hlimA, hlimB] at hout1_val
    have hout1_len' : outXs1.length = scrLimbs.length - (na + nb) := by omega
    have htn_lt64 : tn < 2 ^ 64 := by dsimp only [tn, mpzMaxLimbs] at hres_max; omega
    have htn_bv : (BitVec.ofNat 64 tn).toNat = tn := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htn_lt64]
    apply wp_call_step
    dsimp only [vals, Arg.val]
    refine Or.inr (Or.inr (Or.inl ⟨⟨rfl, rfl⟩, rfl, ?_⟩))
    rw [htn_eq]
    have htn_le' : (BitVec.ofNat 64 tn).toNat ≤ outXs1.length := by
      rw [htn_bv, hout1_len]; exact htn_le
    have htn_max' : (BitVec.ofNat 64 tn).toNat ≤ mpzMaxLimbs := by
      rw [htn_bv]; exact hres_max
    have hval3 : limbsVal (outXs1.take (BitVec.ofNat 64 tn).toNat) = aVal * bVal := by
      rwa [htn_bv]
    have htrim_eq : 2 ^ 63 ≤ aVal * bVal →
        trimLenLoop outXs1 tn = tn := by
      intro hge63
      have h := tn_eq_limbLen_of_ge (hout1_len ▸ htn_le) (by rwa [hout1_val])
      dsimp only at h
      rwa [hout1_val] at h
    have hroom_from :
        2 ^ 63 ≤ limbsVal (outXs1.take (BitVec.ofNat 64 tn).toNat) →
          st.hasFree (16 + 8 * trimLenLoop outXs1 (BitVec.ofNat 64 tn).toNat) ∨
            16 + 8 * trimLenLoop outXs1 (BitVec.ofNat 64 tn).toNat ≤ st.rem := by
      intro hge63
      rw [hval3] at hge63
      rw [htn_bv, htrim_eq hge63]
      exact hres_room hge63
    refine ⟨st, outXs1, objs,
      cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr aXs1 ⋆ array64 (scr + BitVec.ofNat 64 (8 * na)) bXs1 ⋆ R,
      htn_le', htn_max', hb48, hroom_from, sep_ac hm3, ?_⟩
    intro res st' objs' m4 hmeta hrem_le hb48' hrep hsm hbig hm4
    t_wp_unfold
    rw [hval3] at hrep hsm hbig
    have hlen4 : (aXs1 ++ bXs1 ++ outXs1).length = scrLimbs.length := by
      simp [ha1_len, hb1_len, hout1_len']; omega
    have hwf'' : BigNumRtWf rt st' scr (aXs1 ++ bXs1 ++ outXs1) :=
      ⟨hb48', hrt64, hscr0, hscr8, by rw [hlen4]; exact hlen64,
        by rw [hlen4]; exact hscr_bnd⟩
    have hm4' :
        (bigNumRtInv rt st' scr (aXs1 ++ bXs1 ++ outXs1) ⋆ BigNumRt.lcnfHeap objs' ⋆ R) m4 := by
      dsimp only [bigNumRtInv]
      rw [← loop_array64_join3 scr aXs1 bXs1 outXs1, ha1_len, hb1_len, hlen4]
      exact sep_ac hm4
    refine hk res st' (aXs1 ++ bXs1 ++ outXs1) objs' m4 hmeta hrem_le hlen4 hwf'' hrep hsm
      ?_ hm4'
    intro hge63
    have hbig' := hbig hge63
    rwa [htn_bv, htrim_eq hge63] at hbig'
  · intro J hJ
    t_wp_unfold
    exact ⟨fun _ => hJ _ _ rfl, fun _ => hJ _ _ rfl⟩
theorem lcnf_nat_mul_slow_wp (xs : Tup Val [i64, i64, i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    loopNatMulSlowSpec xs m Q X → Func.wp loopRtEnv lcnf_nat_slow.body xs m Q X := by
  intro hspec
  have hop : xs.2.1 = 3#64 := hspec.1
  rcases xs with ⟨rt, op, a, b, ⟨⟩⟩
  dsimp only at hop
  subst hop
  dsimp only [Func.wp, lcnf_nat_slow, lcnf_nat_slow_body]
  refine wp_join_group (Γ := loopRtEnv) (fun () m1 => m1 = m) ?_ ?_
  · rintro Js ⟨⟩ m1 rfl
    t_wp_unfold
    apply wp_call_step
    dsimp only [vals, Arg.val]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨rfl, rfl⟩, rfl, hspec⟩)))
  · intro Js hJs
    refine wp_join_group (Γ := loopRtEnv) (fun () _ => False) (fun _ _ _ hf => hf.elim) ?_
    intro J hJ
    t_wp_unfold
    refine ⟨fun _ => ⟨fun _ => hJs () m rfl,
      fun h => absurd (by decide : (3#64 : BitVec 64).ule 8 = true) (by rw [h]; decide)⟩,
      fun h => absurd (by decide : BitVec.ule 1 (3#64 : BitVec 64) = true) (by rw [h]; decide)⟩

end LeanQbe.T.LeanLCNF
