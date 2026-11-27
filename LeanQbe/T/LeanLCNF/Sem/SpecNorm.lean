module

public import LeanQbe.T.LeanLCNF.LcnfC0FullProof
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersSpec
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.Logic.MemLemmas

/-!
# Runtime Spec Normalization (`G-R1` & `G-R2`) for `LeanLCNF` Tier-H Semantics

R1 (`LcnfC0BigNumSpec`) states its contracts directly over `LcnfC0RtSpec`'s `RtC0State` /
`LcnfObj`, so Tier-H semantics (`Sem/H`) uses R1's `natRep`, `intRep`, `bigNumRtInv`, and Specs
verbatim. This module provides:

1. **`G-R1`**: every R1 `Nat`/`Int` contract lifts into the unified `rtC0CoreEnv`
   (`*Spec_le_rtC0CoreEnv`).
2. **`G-R2`**: coercions between R1's canonical `natRep` and R2b's `NatInHeap`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open Std.ExtHashMap

theorem mpzLimbsVal_eq_limbsVal : ∀ xs : List (BitVec 64), mpzLimbsVal xs = limbsVal xs
  | [] => rfl
  | x :: xs => by
    unfold mpzLimbsVal
    simp only [List.foldr_cons, limbsVal_cons]
    congr 2
    exact mpzLimbsVal_eq_limbsVal xs

/-! ## 1. R1 `Spec`s inside `rtC0CoreEnv` (`G-R1`) -/

theorem lcnfNatAllocSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : lcnfNatAllocSpec xs m Q X) : rtC0CoreEnv "lcnf_nat_alloc" [i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_nat_alloc h)

theorem bnDecNatSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : bnDecNatSpec xs m Q X) : rtC0CoreEnv "bn_dec_nat" [i64, i64] [] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_bn_dec_nat h)

theorem bnNatPowSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : bnNatPowSpec xs m Q X) : rtC0CoreEnv "bn_nat_pow" [i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_bn_nat_pow h)

theorem bnNatGcdSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : bnNatGcdSpec xs m Q X) : rtC0CoreEnv "bn_nat_gcd" [i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_bn_nat_gcd h)

theorem lcnfNatArithSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : lcnfNatArithSpec xs m Q X) :
    rtC0CoreEnv "lcnf_nat_arith" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_nat_arith h)

theorem lcnfNatBitsSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : lcnfNatBitsSpec xs m Q X) :
    rtC0CoreEnv "lcnf_nat_bits" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_nat_bits h)

theorem lcnfNatSlowSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : lcnfNatSlowSpec xs m Q X) :
    rtC0CoreEnv "lcnf_nat_slow" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_nat_slow h)

theorem lcnfIntConvSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : lcnfIntConvSpec xs m Q X) : rtC0CoreEnv "lcnf_int_conv" [i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_int_conv h)

theorem lcnfIntAddSubCmpSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : lcnfIntAddSubCmpSpec xs m Q X) :
    rtC0CoreEnv "lcnf_int_addsub_cmp" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_int_addsub_cmp h)

theorem lcnfIntMulDivSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : lcnfIntMulDivSpec xs m Q X) :
    rtC0CoreEnv "lcnf_int_muldiv" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_int_muldiv h)

theorem lcnfIntOpSpec_le_rtC0CoreEnv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : lcnfIntOpSpec xs m Q X) : rtC0CoreEnv "lcnf_int_op" [i64, i64, i64, i64] [i64] xs m Q X :=
  rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_int_op h)

/-! ## 2. Unified `Nat` Coercions (`natRep ↔ NatInHeap`, `G-R2`) -/

private theorem ofNat64_box_and1_ne {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n + 1) &&& 1#64) ≠ 0#64 := by
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  have hand : (BitVec.ofNat 64 (2 * n + 1) &&& 1#64) = 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, h1, Nat.and_one_is_mod, BitVec.toNat_ofNat, hmod]
    omega
  rw [hand]; decide

private theorem ofNat64_box_shr1 {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n + 1) >>> 1).toNat = n := by
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hmod, Nat.shiftRight_eq_div_pow,
    show (2 ^ 1 : Nat) = 2 by decide]
  omega

theorem natRep_to_natInHeap_small {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hs : n < 2 ^ 63) (hrep : natRep w n objs) : NatInHeap w n objs := by
  have hw : w = BitVec.ofNat 64 (2 * n + 1) := by
    simpa [natRep, hs] using hrep
  subst hw
  rw [NatInHeap, ite_eq_left (ofNat64_box_and1_ne hs), ofNat64_box_shr1 hs]

theorem mpzNatCanon_to_mpzCanon {obj : LcnfObj} {n : Nat}
    (hc : mpzNatCanon obj n) (hcs0 : obj.csSz = 0) :
    MpzCanon obj ∧ mpzLimbsVal (obj.limbs.take obj.arrSize) = n := by
  rcases hc with ⟨hwf, htag, hoth, harr, _, _, _, hval, _⟩
  rcases hwf with ⟨h0, h8, hrc, _, _, _, _, _, _, hkind⟩
  simp only [htag, show mpzTag = 250 from rfl, closureTag, arrayTag, sarrayTag, stringTag] at hkind
  rcases hkind with ⟨hlcap, hcap, _⟩
  have harrcap : obj.arrSize ≤ obj.cap := by omega
  refine ⟨⟨h0, h8, hrc, hcs0, hoth, htag, hlcap, harrcap, hcap⟩, ?_⟩
  rw [harr, List.take_length, mpzLimbsVal_eq_limbsVal, hval]

theorem natRep_to_natInHeap {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hrep : natRep w n objs) (hcs0 : ∀ o ∈ objs, o.addr = w → o.csSz = 0) :
    NatInHeap w n objs := by
  by_cases hs : n < 2 ^ 63
  · exact natRep_to_natInHeap_small hs hrep
  · simp only [natRep, hs, ↓reduceIte] at hrep
    rcases hrep with ⟨hw0, obj, hmem, had, hc⟩
    have hnot : ¬ ((w &&& 1#64) ≠ 0#64) := fun h => h hw0
    rw [NatInHeap, ite_eq_right hnot]
    obtain ⟨hmc, hval⟩ := mpzNatCanon_to_mpzCanon hc (hcs0 obj hmem had)
    exact ⟨obj, hmem, had, hmc, hval.symm⟩

theorem natInHeap_to_natRep_small {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hodd : (w &&& 1#64) ≠ 0#64) (hnih : NatInHeap w n objs) : natRep w n objs := by
  rw [NatInHeap, ite_eq_left hodd] at hnih
  have hsh : n = w.toNat / 2 := by
    rw [hnih, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (2 ^ 1 : Nat) = 2 by decide]
  have hlt : n < 2 ^ 63 := by
    have := w.isLt
    omega
  have hmod : w.toNat % 2 = 1 := by
    by_cases hm : w.toNat % 2 = 1
    · exact hm
    · exfalso
      apply hodd
      apply BitVec.eq_of_getElem_eq
      intro i hi
      cases i with
      | zero =>
        simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_and, BitVec.toNat_ofNat,
          Nat.testBit_zero]
        have hm0 : w.toNat % 2 = 0 := by omega
        simp [hm0]
      | succ k =>
        simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_and, BitVec.toNat_ofNat]
        rw [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
        have h1bit : (1 : Nat).testBit (k + 1) = false := by simp [Nat.testBit_succ]
        have h0bit : (0 : Nat).testBit (k + 1) = false := by simp
        simp [h1bit, h0bit]
  simp only [natRep, hlt, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem natInHeap_to_natRep {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hnih : NatInHeap w n objs)
    (hcanon : (w &&& 1#64) = 0#64 →
      ∃ obj ∈ objs, obj.addr = w ∧ MpzCanon obj ∧
        obj.arrSize = obj.limbs.length ∧ 1 ≤ obj.limbs.length ∧
        obj.limbs.getLast! ≠ 0#64 ∧ mpzLimbsVal obj.limbs = n ∧ 2 ^ 63 ≤ n) :
    natRep w n objs := by
  by_cases hodd : (w &&& 1#64) ≠ 0#64
  · exact natInHeap_to_natRep_small hodd hnih
  · have hw0 : (w &&& 1#64) = 0#64 := Decidable.not_not.mp hodd
    obtain ⟨obj, hmem, had, hmc, harr, hlen, hlast, hval, hge⟩ := hcanon hw0
    have hnot : ¬(n < 2 ^ 63) := Nat.not_lt.mpr hge
    simp only [natRep, hnot, ↓reduceIte]
    have hcapMax : obj.limbs.length ≤ mpzMaxLimbs := by
      have := hmc.2.2.2.2.2.2.1
      have := hmc.2.2.2.2.2.2.2.2
      unfold mpzMaxLimbs
      omega
    refine ⟨hw0, obj, hmem, had, hmc.wf, hmc.2.2.2.2.2.1, hmc.2.2.2.2.1,
      harr, hlen, hcapMax, hlast, ?_, hge⟩
    rw [← mpzLimbsVal_eq_limbsVal, hval]

end LeanQbe.T.LeanLCNF.Sem
