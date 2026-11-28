/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2Base
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA `ar_build_sp0` Helpers (`Arisca.Proof.Poly2Sp0Base`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) helper lemmas, loop-body WPs (`sp0_call_addQ_wp`,
`sp0_merge_exit_ok`, `sp0_k_body_wp`) for `ar_build_sp0`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly

/-! ## 1. Pure Helpers for `ar_build_sp0` -/

public theorem qMem_focus_q (s : ArCtxState) (qm : List (BitVec 32))
    (qs ql qh : List (BitVec 64)) (ix ix2 bx vqOff vq : List (BitVec 32))
    (vqSkip : List (BitVec 8)) :
    ∃ rest : Mem 64 → Prop,
      (qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip =
        (array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
          rest)) ∧
      (∀ (s' : ArCtxState) (qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64)),
        s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh →
        s'.ix = s.ix → s'.ix2 = s.ix2 → s'.bx = s.bx → s'.vq_off = s.vq_off →
        s'.vq = s.vq → s'.vq_skip = s.vq_skip → qm'.length = qm.length →
        qMem s' qm' qs' ql' qh' ix ix2 bx vqOff vq vqSkip =
          (array (t := i32) s'.qm qm' ⋆ array64 s'.qs qs' ⋆ array64 s'.ql ql' ⋆
            array64 s'.qh qh' ⋆ rest)) :=
  ⟨u32PadTail s.qm qm.length ⋆ arrayPad i32 s.ix ix ⋆ arrayPad i32 s.ix2 ix2 ⋆
    arrayPad i32 s.bx bx ⋆ arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆
    arrayPad i8 s.vq_skip vqSkip,
    by simp only [qMem, arrayPad_u32_unfold]; ac_rfl,
    fun s' qm' qs' ql' qh' hqm hqs hql hqh hix hix2 hbx hvqo hvq hvqs hlen => by
      simp only [qMem, arrayPad_u32_unfold, hqm, hqs, hql, hqh, hix, hix2, hbx, hvqo, hvq,
        hvqs, hlen]; ac_rfl⟩

private theorem sp0_outSum_append (w : Nat) (σ : Nat → Bool) :
    ∀ (xs : List Nat) (r j0 : Nat),
      outSum w σ (xs ++ [r]) j0 =
        outSum w σ xs j0 +
          BitVec.ofNat w (2 ^ (j0 + xs.length)) * bv w (σ (2 * (r / 2)) ^^ (r % 2 == 1))
  | [], r, j0 => by simp [outSum, BitVec.add_zero]
  | x :: xs, r, j0 => by
    simp only [List.cons_append, List.length_cons, outSum]
    rw [sp0_outSum_append w σ xs r (j0 + 1), ← BitVec.add_assoc,
      show j0 + 1 + xs.length = j0 + (xs.length + 1) by omega]

public theorem sp0_outSum_take_succ (w : Nat) (σ : Nat → Bool) (outRefArr : List (BitVec 32))
    {j : Nat} (hj : j < outRefArr.length) :
    outSum w σ ((outRefArr.take (j + 1)).map BitVec.toNat) 0 =
      outSum w σ ((outRefArr.take j).map BitVec.toNat) 0 +
        BitVec.ofNat w (2 ^ j) *
          bv w (σ (2 * ((outRefArr.getD j 0#32).toNat / 2)) ^^
            ((outRefArr.getD j 0#32).toNat % 2 == 1)) := by
  have htake : outRefArr.take (j + 1) = outRefArr.take j ++ [outRefArr[j]] :=
    List.take_add_one.trans (by simp [List.getElem?_eq_getElem hj])
  rw [htake, List.map_append, List.map_singleton, sp0_outSum_append,
    List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), Nat.zero_add,
    ← getD_eq_getElem outRefArr 0#32 hj]

public theorem sp0_out_step_odd (w : Nat) (σ : Nat → Bool) (rf : BitVec 32) {j : Nat}
    (hodd : (rf &&& 1#32) ≠ 0#32) {l0 h0 l1 h1 : BitVec 64}
    (hlh0 : coeff128 w l0 h0 = BitVec.ofNat w (2 ^ j))
    (hlh1 : coeff128 w l1 h1 = -coeff128 w l0 h0) :
    (if monoValL σ (addQSyms 0 0 0) then coeff128 w l0 h0 else 0#w) +
        (if monoValL σ (addQSyms 1 (2 * (rf >>> 1).toNat) 0) then coeff128 w l1 h1 else 0#w) =
      BitVec.ofNat w (2 ^ j) * bv w (σ (2 * (rf.toNat / 2)) ^^ (rf.toNat % 2 == 1)) := by
  have hrmod : rf.toNat % 2 = 1 := by
    have hand : (rf &&& 1#32).toNat = rf.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    have hne : rf.toNat % 2 ≠ 0 := by
      intro hz; apply hodd; apply BitVec.eq_of_toNat_eq; rw [hand, hz]; rfl
    rcases Nat.mod_two_eq_zero_or_one rf.toNat with h | h <;> omega
  have hsh : (rf >>> (1 : Nat)).toNat = rf.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  simp only [addQSyms, hlh1, hlh0, hrmod, hsh, beq_self_eq_true,
    show ((1 : Nat) = 0) = False by decide, ↓reduceIte]
  have hm0 : monoValL σ [] = true := rfl
  have hm1 : monoValL σ [2 * (rf.toNat / 2)] = σ (2 * (rf.toNat / 2)) := by
    show (σ (2 * (rf.toNat / 2)) && true) = _; simp
  rw [hm0, hm1]
  cases σ (2 * (rf.toNat / 2)) <;> simp [bv, ← BitVec.sub_eq_add_neg, BitVec.sub_self]

public theorem sp0_out_step_even (w : Nat) (σ : Nat → Bool) (rf : BitVec 32) {j : Nat}
    (heven : (rf &&& 1#32) = 0#32) {l0 h0 : BitVec 64}
    (hlh0 : coeff128 w l0 h0 = BitVec.ofNat w (2 ^ j)) :
    (if monoValL σ (addQSyms 1 (2 * (rf >>> 1).toNat) 0) then coeff128 w l0 h0 else 0#w) =
      BitVec.ofNat w (2 ^ j) * bv w (σ (2 * (rf.toNat / 2)) ^^ (rf.toNat % 2 == 1)) := by
  have hrmod : rf.toNat % 2 = 0 := by
    have hand : (rf &&& 1#32).toNat = rf.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    have heq := congrArg BitVec.toNat heven
    rw [hand] at heq; exact heq
  have hsh : (rf >>> (1 : Nat)).toNat = rf.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  simp only [addQSyms, hlh0, hrmod, hsh, show (0 == 1) = false by decide, Bool.xor_false,
    show ((1 : Nat) = 0) = False by decide, ↓reduceIte]
  have hm1 : monoValL σ [2 * (rf.toNat / 2)] = σ (2 * (rf.toNat / 2)) := by
    show (σ (2 * (rf.toNat / 2)) && true) = _; simp
  rw [hm1]
  cases σ (2 * (rf.toNat / 2)) <;> simp [bv]

public noncomputable def inTerm (w : Nat) (σ : Nat → Bool) (signed : Bool) (n x idx : Nat) :
    BitVec w :=
  (if signed = true ∧ idx + 1 = n then -BitVec.ofNat w (2 ^ idx) else BitVec.ofNat w (2 ^ idx)) *
    bv w (σ (2 * x))

private theorem sp0_inSum_append (w : Nat) (σ : Nat → Bool) (signed : Bool) (n : Nat) :
    ∀ (xs : List Nat) (x i0 : Nat),
      inSum w σ signed n (xs ++ [x]) i0 =
        inSum w σ signed n xs i0 + inTerm w σ signed n x (i0 + xs.length)
  | [], x, i0 => by simp [inSum, inTerm, BitVec.add_zero]
  | y :: xs, x, i0 => by
    simp only [List.cons_append, List.length_cons, inSum]
    rw [sp0_inSum_append w σ signed n xs x (i0 + 1), ← BitVec.add_assoc,
      show i0 + 1 + xs.length = i0 + (xs.length + 1) by omega]

private theorem sp0_inSum_take_succ (w : Nat) (σ : Nat → Bool) (signed : Bool) (n : Nat)
    (xs : List (BitVec 32)) {k : Nat} (hk : k < xs.length) :
    inSum w σ signed n ((xs.take (k + 1)).map BitVec.toNat) 0 =
      inSum w σ signed n ((xs.take k).map BitVec.toNat) 0 +
        inTerm w σ signed n (xs.getD k 0#32).toNat k := by
  have htake : xs.take (k + 1) = xs.take k ++ [xs[k]] :=
    List.take_add_one.trans (by simp [List.getElem?_eq_getElem hk])
  rw [htake, List.map_append, List.map_singleton, sp0_inSum_append,
    List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk), Nat.zero_add,
    ← getD_eq_getElem xs 0#32 hk]

public theorem sp0_inSum_drop_take_succ (w : Nat) (σ : Nat → Bool) (signed : Bool) (n : Nat)
    (xs : List (BitVec 32)) {k : Nat} (hk : n + k < xs.length) :
    inSum w σ signed n (((xs.drop n).take (k + 1)).map BitVec.toNat) 0 =
      inSum w σ signed n (((xs.drop n).take k).map BitVec.toNat) 0 +
        inTerm w σ signed n (xs.getD (n + k) 0#32).toNat k := by
  have hk_drop : k < (xs.drop n).length := by simp; omega
  rw [sp0_inSum_take_succ w σ signed n (xs.drop n) hk_drop]
  congr 2
  rw [getD_eq_getElem (xs.drop n) 0#32 hk_drop, List.getElem_drop,
    ← getD_eq_getElem xs 0#32 hk]

private theorem sp0_mul4_zero {w : Nat} {a b : BitVec w} (hab : a * b = 0#w)
    (x y : BitVec w) : (a * x) * (b * y) = 0#w := by
  rw [BitVec.mul_assoc, ← BitVec.mul_assoc x b y, BitVec.mul_comm x b,
    BitVec.mul_assoc b x y, ← BitVec.mul_assoc a b (x * y), hab, BitVec.zero_mul]

private theorem sp0_prod_term_ge {w i k : Nat} (hge : w ≤ i + k) (σ : Nat → Bool)
    (signed : Bool) (n xa xb : Nat) :
    inTerm w σ signed n xa i * inTerm w σ signed n xb k = 0#w := by
  have hpow : BitVec.ofNat w (2 ^ (i + k)) = 0#w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_zero_of_dvd]
    exact Nat.pow_dvd_pow 2 hge
  have hpow_mul : BitVec.ofNat w (2 ^ i) * BitVec.ofNat w (2 ^ k) = 0#w := by
    rw [← BitVec.ofNat_mul, ← Nat.pow_add, hpow]
  dsimp only [inTerm]
  split <;> split
  · rw [BitVec.neg_mul, BitVec.neg_mul, BitVec.neg_mul, BitVec.mul_neg, BitVec.neg_neg]
    exact sp0_mul4_zero hpow_mul _ _
  · rw [BitVec.neg_mul, BitVec.neg_mul, sp0_mul4_zero hpow_mul, BitVec.neg_zero]
  · rw [BitVec.neg_mul, BitVec.mul_neg, sp0_mul4_zero hpow_mul, BitVec.neg_zero]
  · exact sp0_mul4_zero hpow_mul _ _

private theorem sp0_prod_term_lt {w i k n : Nat} (hik : i + k < w) (hw128 : w ≤ 128)
    (σ : Nat → Bool) (signed : Bool) (va vb : Nat) {l h : BitVec 64}
    (hlh : coeff128 w l h =
      let isNeg := signed = true ∧ (decide (i + 1 = n) != decide (k + 1 = n))
      if isNeg then BitVec.ofNat w (2 ^ (i + k)) else -BitVec.ofNat w (2 ^ (i + k))) :
    (if monoValL σ
        (addQSyms (if 2 * va = 2 * vb then 1 else 2)
          (if 2 * va < 2 * vb then 2 * va else 2 * vb)
          (if 2 * va < 2 * vb then 2 * vb else 2 * va))
      then coeff128 w l h else 0#w) =
      -(inTerm w σ signed n va i * inTerm w σ signed n vb k) := by
  have _ := hik; have _ := hw128
  have hmval : monoValL σ
      (addQSyms (if 2 * va = 2 * vb then 1 else 2)
        (if 2 * va < 2 * vb then 2 * va else 2 * vb)
        (if 2 * va < 2 * vb then 2 * vb else 2 * va)) =
      (σ (2 * va) && σ (2 * vb)) := by
    by_cases heq : 2 * va = 2 * vb
    · have hva : va = vb := by omega
      subst hva
      simp only [Nat.lt_irrefl, ↓reduceIte, addQSyms, show (1 : Nat) ≠ 0 by decide,
        monoValL, Bool.and_true, Bool.and_self]
    · by_cases hlt : 2 * va < 2 * vb
      · simp only [heq, hlt, ↓reduceIte, addQSyms, show (2 : Nat) ≠ 0 by decide,
          show (2 : Nat) ≠ 1 by decide, monoValL, Bool.and_true]
      · simp only [heq, hlt, ↓reduceIte, addQSyms, show (2 : Nat) ≠ 0 by decide,
          show (2 : Nat) ≠ 1 by decide, monoValL, Bool.true_and, Bool.and_comm]
  rw [hmval, hlh]
  dsimp only [inTerm]
  have hmul : BitVec.ofNat w (2 ^ i) * BitVec.ofNat w (2 ^ k) = BitVec.ofNat w (2 ^ (i + k)) := by
    rw [← BitVec.ofNat_mul, ← Nat.pow_add]
  cases signed <;> cases hi1 : decide (i + 1 = n) <;> cases hk1 : decide (k + 1 = n) <;>
    cases σ (2 * va) <;> cases σ (2 * vb) <;>
    simp [bv, hmul] <;>
    try simp_all [of_decide_eq_true, of_decide_eq_false]

/-! ## 2. Loop Helpers & `ar_build_sp0_wp` (`Arisca.Src.Poly`) -/

@[expose] public def Sp0LoopState (s : ArCtxState) (pt qn : Nat) : ArCtxState :=
  { s with tn := 0#32, ptop := BitVec.ofNat 64 pt, qn := BitVec.ofNat 32 qn }

public theorem buildSp0_pack_mem {cx : BitVec 64} {s s' : ArCtxState}
    {bindArr inNetArr outRefArr partnerArr : List (BitVec 32)}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hs : s' = { s with
        tc := s'.tc, tn := s'.tn, ptop := s'.ptop, qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 })
    (hm : (arCtxMem cx s' ⋆ array (t := i32) s.bind bindArr ⋆
      array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
      array (t := i32) s.partner partnerArr ⋆
      tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s' qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m) :
    (arCtxMem cx s' ⋆ array (t := i32) s'.bind bindArr ⋆
      array (t := i32) s'.in_net inNetArr ⋆ array (t := i32) s'.out_ref outRefArr ⋆
      array (t := i32) s'.partner partnerArr ⋆
      tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s' qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m := by
  have hb : s'.bind = s.bind := by rw [hs]
  have hi : s'.in_net = s.in_net := by rw [hs]
  have ho : s'.out_ref = s.out_ref := by rw [hs]
  have hp : s'.partner = s.partner := by rw [hs]
  rw [hb, hi, ho, hp]; exact hm

public theorem sp0_call_addQ_wp (Γ : T.Env)
    (hAddQ : ∀ xs m Q X, arAddQSpec xs m Q X →
      Γ "ar_add_q" [i64, i32, i32, i32, i64, i64] [.bool] xs m Q X)
    {cx : Val i64} {alen as0 as1 : Arg Val i32} (lenN s0N s1N : Nat)
    {l h : Val i64} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost} {cont : Expr Val Cont [.bool]}
    {s sC : ArCtxState} {g : Aig} {bindArr inNetArr outRefArr partnerArr : List (BitVec 32)}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {pt qn : Nat} {pool0C pool1C qmC : List (BitVec 32)} {qsC qlC qhC : List (BitVec 64)}
    {restQ R : Mem 64 → Prop}
    (halen : alen.val.toNat = lenN) (has0 : as0.val.toNat = s0N) (has1 : as1.val.toNat = s1N)
    (hsC : sC = Sp0LoopState s pt qn)
    (hpt : pt ≤ s.pcap.toNat) (hqn : qn ≤ s.qcap.toNat)
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hnnets : s.n_nets.toNat ≤ 0x3FFFFFFF) (hnn2 : 2 * s.n_nets.toNat < 2 ^ 32)
    (hp0_len : pool0C.length = pool0.length) (hp1_len : pool1C.length = pool1.length)
    (hs_p0 : s.pcap.toNat ≤ pool0.length) (hs_p1 : s.pcap.toNat ≤ pool1.length)
    (hqm_len : qmC.length = qm.length) (hqs_len : qsC.length = qs.length)
    (hql_len : qlC.length = ql.length) (hqh_len : qhC.length = qh.length)
    (hs_qm : s.qcap.toNat ≤ qm.length) (hs_qs : s.qcap.toNat ≤ qs.length)
    (hs_ql : s.qcap.toNat ≤ ql.length) (hs_qh : s.qcap.toNat ≤ qh.length)
    (hMasks : MasksOk s.n_out.toNat s.mlo s.mhi)
    (hPart : ∀ ρ : Nat → Bool, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr)
    (hSlices : ∀ i < qn,
      MonoSliceOk (if s.pc.toNat = 0 then pool0C else pool1C) (qmC.getD i 0#32).toNat pt ∧
      ((if s.pc.toNat = 0 then pool0C else pool1C).getD
        (qmC.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : ∀ i < qn,
      MonoSorted (if s.pc.toNat = 0 then pool0C else pool1C) (qmC.getD i 0#32).toNat)
    (hSig : SigOk (if s.pc.toNat = 0 then pool0C else pool1C) qmC qsC qn)
    (hs01_lt : lenN = 2 → s0N < s1N)
    (hWords : monoTotalWords (if s.pc.toNat = 0 then pool0C else pool1C) qmC qn ≤ pt)
    (hm : (arCtxMem cx sC ⋆ array (t := i32) s.bind bindArr ⋆
      array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
      array (t := i32) s.partner partnerArr ⋆
      tMem sC tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0C pool1C ⋆
      array (t := i32) s.qm qmC ⋆ array64 s.qs qsC ⋆ array64 s.ql qlC ⋆
      array64 s.qh qhC ⋆ restQ ⋆ R) m)
    (hFail : ∀ {ptF qnF : Nat} {pool0F pool1F qmF : List (BitVec 32)}
        {qsF qlF qhF : List (BitVec 64)} {mF : Mem 64},
      ptF ≤ s.pcap.toNat → qnF ≤ s.qcap.toNat →
      pool0F.length = pool0.length → pool1F.length = pool1.length →
      qmF.length = qm.length → qsF.length = qs.length →
      qlF.length = ql.length → qhF.length = qh.length →
      (arCtxMem cx (Sp0LoopState s ptF qnF) ⋆ array (t := i32) s.bind bindArr ⋆
        array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
        array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s ptF qnF) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0F pool1F ⋆
        array (t := i32) s.qm qmF ⋆ array64 s.qs qsF ⋆ array64 s.ql qlF ⋆
        array64 s.qh qhF ⋆ restQ ⋆ R) mF →
      Q (false, ⟨⟩) mF)
    (hOk : ∀ (pt' qn' : Nat) (pool0' pool1' qm' : List (BitVec 32))
        (qs' ql' qh' : List (BitVec 64)) (m' : Mem 64),
      let srcPool := if s.pc.toNat = 0 then pool0C else pool1C
      let dstPool := if s.pc.toNat = 0 then pool0' else pool1'
      pt' ≤ s.pcap.toNat → qn' ≤ s.qcap.toNat →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      qm'.length = qm.length → qs'.length = qs.length →
      ql'.length = ql.length → qh'.length = qh.length →
      (∀ i < qn', MonoSliceOk dstPool (qm'.getD i 0#32).toNat pt' ∧
        (dstPool.getD (qm'.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ i < qn', MonoSorted dstPool (qm'.getD i 0#32).toNat) →
      SigOk dstPool qm' qs' qn' →
      monoTotalWords dstPool qm' qn' ≤ pt' →
      (∀ ρ : Nat → Bool,
        polyEval s.n_out.toNat (cSig g ρ bindArr) dstPool qm' ql' qh' qn' =
          polyEval s.n_out.toNat (cSig g ρ bindArr) srcPool qmC qlC qhC qn +
            (if monoValL (cSig g ρ bindArr) (addQSyms lenN s0N s1N)
             then coeff128 s.n_out.toNat l h else 0#(s.n_out.toNat))) →
      (arCtxMem cx (Sp0LoopState s pt' qn') ⋆ array (t := i32) s.bind bindArr ⋆
        array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
        array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s pt' qn') tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0' pool1' ⋆
        array (t := i32) s.qm qm' ⋆ array64 s.qs qs' ⋆ array64 s.ql ql' ⋆
        array64 s.qh qh' ⋆ restQ ⋆ R) m' →
      wp Γ Q X cont m') :
    wp Γ Q X (.call (as := [i64, i32, i32, i32, i64, i64]) (bs := [.bool]) "ar_add_q"
      (Arg.var cx, alen, as0, as1, Arg.var l, Arg.var h, ())
      (fun r => Expr.jnz (Arg.var r.1) cont (Expr.ret (Arg.imm false, ())))) m := by
  have hpt_toNat : (BitVec.ofNat 64 pt).toNat = pt := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pt < 2 ^ 64)]
  have hqn_toNat : (BitVec.ofNat 32 qn).toNat = qn := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qn < 2 ^ 32)]
  refine wp_call_of_spec _ _ (hAddQ _ m _ _
    ⟨sC, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0C, pool1C, qmC, qsC, qlC, qhC,
      partnerArr, fun σ => ∃ ρ : Nat → Bool, σ = cSig g ρ bindArr,
      array (t := i32) s.bind bindArr ⋆ array (t := i32) s.in_net inNetArr ⋆
        array (t := i32) s.out_ref outRefArr ⋆ restQ ⋆ R,
      by simp [hsC, Sp0LoopState, hpc], by simp [hsC, Sp0LoopState, htc],
      by simp [hsC, Sp0LoopState, hqn_toNat, hqn], by simp [hsC, Sp0LoopState, hqcap32],
      by simp [hsC, Sp0LoopState, hpt_toNat, hpt], by simp [hsC, Sp0LoopState, hpcap32],
      by simp [hsC, Sp0LoopState, hnnets], by simp [hsC, Sp0LoopState, hnn2],
      by simp [hsC, Sp0LoopState, hp0_len, hs_p0], by simp [hsC, Sp0LoopState, hp1_len, hs_p1],
      by simp [hsC, Sp0LoopState, hqm_len, hs_qm], by simp [hsC, Sp0LoopState, hqs_len, hs_qs],
      by simp [hsC, Sp0LoopState, hql_len, hs_ql], by simp [hsC, Sp0LoopState, hqh_len, hs_qh],
      by simp [hsC, Sp0LoopState, hMasks],
      ⟨cSig g (fun _ => false) bindArr, ⟨fun _ => false, rfl⟩⟩,
      fun _ ⟨ρ, hρ⟩ => hρ ▸ by simpa [hsC, Sp0LoopState] using hPart ρ,
      by simpa [hsC, Sp0LoopState, hpt_toNat, hqn_toNat] using hSlices,
      by simpa [hsC, Sp0LoopState, hqn_toNat] using hSorted,
      by simpa [hsC, Sp0LoopState, hqn_toNat] using hSig,
      by simpa [halen, has0, has1] using hs01_lt,
      by simpa [hsC, Sp0LoopState, hpt_toNat, hqn_toNat] using hWords,
      by simp only [hsC, Sp0LoopState] at hm ⊢; exact sep_cast hm (by ac_rfl),
      fun ok s' pool0' pool1' qm' qs' ql' qh' m'
        hqn' hpt' hs' hp0' hp1' hqm' hqs' hql' hqh' _ _ _ hOkPost hm' => ?_⟩)
  have hpt_bv : BitVec.ofNat 64 s'.ptop.toNat = s'.ptop := BitVec.eq_of_toNat_eq (by simp)
  have hqn_bv : BitVec.ofNat 32 s'.qn.toNat = s'.qn := BitVec.eq_of_toNat_eq (by simp)
  have hs'_eq : s' = Sp0LoopState s s'.ptop.toNat s'.qn.toNat := by
    rw [hs', hsC]; dsimp only [Sp0LoopState]
    rw [hpt_bv, hqn_bv]
  have hm_norm : (arCtxMem cx (Sp0LoopState s s'.ptop.toNat s'.qn.toNat) ⋆
      array (t := i32) s.bind bindArr ⋆ array (t := i32) s.in_net inNetArr ⋆
      array (t := i32) s.out_ref outRefArr ⋆ array (t := i32) s.partner partnerArr ⋆
      tMem (Sp0LoopState s s'.ptop.toNat s'.qn.toNat) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
        pool0' pool1' ⋆
      array (t := i32) s.qm qm' ⋆ array64 s.qs qs' ⋆ array64 s.ql ql' ⋆
      array64 s.qh qh' ⋆ restQ ⋆ R) m' := by
    have hs'_pt : s'.partner = s.partner := by rw [hs', hsC]; rfl
    have hs'_qm : s'.qm = s.qm := by rw [hs', hsC]; rfl
    have hs'_qs : s'.qs = s.qs := by rw [hs', hsC]; rfl
    have hs'_ql : s'.ql = s.ql := by rw [hs', hsC]; rfl
    have hs'_qh : s'.qh = s.qh := by rw [hs', hsC]; rfl
    rw [hs'_pt, hs'_qm, hs'_qs, hs'_ql, hs'_qh, hs'_eq] at hm'
    exact sep_cast hm' (by ac_rfl)
  cases ok
  · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
    c0_hstraight
    exact hFail (by simpa [hsC, Sp0LoopState] using hpt')
      (by simpa [hsC, Sp0LoopState] using hqn')
      (hp0'.trans hp0_len) (hp1'.trans hp1_len) (hqm'.trans hqm_len) (hqs'.trans hqs_len)
      (hql'.trans hql_len) (hqh'.trans hqh_len) hm_norm
  · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
    obtain ⟨hSl', hSorted', hSig', hW', hEv'⟩ := hOkPost rfl
    refine hOk s'.ptop.toNat s'.qn.toNat pool0' pool1' qm' qs' ql' qh' m'
      (by simpa [hsC, Sp0LoopState] using hpt') (by simpa [hsC, Sp0LoopState] using hqn')
      (hp0'.trans hp0_len) (hp1'.trans hp1_len) (hqm'.trans hqm_len) (hqs'.trans hqs_len)
      (hql'.trans hql_len) (hqh'.trans hqh_len)
      (by simpa [hsC, Sp0LoopState] using hSl')
      (by simpa [hsC, Sp0LoopState] using hSorted')
      (by simpa [hsC, Sp0LoopState] using hSig')
      (by simpa [hsC, Sp0LoopState] using hW')
      (fun ρ => by
        have hEv'' := hEv' (cSig g ρ bindArr) ⟨ρ, rfl⟩
        have hsC_nout : sC.n_out = s.n_out := by rw [hsC]; rfl
        rw [hsC_nout] at hEv''
        simp only [Arg.val] at hEv''
        simp only [Arg.val] at halen has0 has1
        simp only [hsC, Sp0LoopState, hqn_toNat, halen, has0, has1] at hEv'' ⊢
        exact hEv'')
      hm_norm

private theorem sp0_loop2_step_lt {w i k n : Nat} (hik : i + k < w) (hw128 : w ≤ 128)
    (σ : Nat → Bool) (signed : Bool) (outP inA inB prevP newP : BitVec w)
    (va vb : Nat) {l h : BitVec 64}
    (hprev : prevP = outP - inA - inTerm w σ signed n va i * inB)
    (hnew : newP = prevP +
      (if monoValL σ
          (addQSyms (if 2 * va = 2 * vb then 1 else 2)
            (if 2 * va < 2 * vb then 2 * va else 2 * vb)
            (if 2 * va < 2 * vb then 2 * vb else 2 * va))
        then coeff128 w l h else 0#w))
    (hlh : coeff128 w l h =
      let isNeg := signed = true ∧ (decide (i + 1 = n) != decide (k + 1 = n))
      if isNeg then BitVec.ofNat w (2 ^ (i + k)) else -BitVec.ofNat w (2 ^ (i + k))) :
    newP = outP - inA - inTerm w σ signed n va i * (inB + inTerm w σ signed n vb k) := by
  rw [hnew, hprev, sp0_prod_term_lt hik hw128 σ signed va vb hlh, BitVec.mul_add]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]

public theorem sp0_loop2_step_ge {w i k n : Nat} (hge : w ≤ i + k)
    (σ : Nat → Bool) (signed : Bool) (outP inA inB prevP : BitVec w) (va vb : Nat)
    (hprev : prevP = outP - inA - inTerm w σ signed n va i * inB) :
    prevP = outP - inA - inTerm w σ signed n va i * (inB + inTerm w σ signed n vb k) := by
  rw [hprev, BitVec.mul_add, sp0_prod_term_ge hge σ signed n va vb, BitVec.add_zero]

public theorem sp0_loop2_row_done {w : Nat} (σ : Nat → Bool) (signed : Bool) (n : Nat)
    (inNetArr : List (BitVec 32)) {i : Nat} (hi : i < inNetArr.length)
    (outP prevP inB : BitVec w)
    (hprev : prevP = outP -
      inSum w σ signed n ((inNetArr.take i).map BitVec.toNat) 0 * inB -
      inTerm w σ signed n (inNetArr.getD i 0#32).toNat i * inB) :
    prevP = outP -
      inSum w σ signed n ((inNetArr.take (i + 1)).map BitVec.toNat) 0 * inB := by
  rw [hprev, sp0_inSum_take_succ w σ signed n inNetArr hi, BitVec.add_mul]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]

private theorem sp0_done_eval_eq {s : ArCtxState} {g : Aig}
    {bindArr inNetArr outRefArr : List (BitVec 32)}
    (hBind : BindRep s g bindArr inNetArr outRefArr) (ρ : Nat → Bool) :
    outSum s.n_out.toNat (cSig g ρ bindArr) ((outRefArr.take s.n_out.toNat).map BitVec.toNat) 0 -
        inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) (g.I / 2)
          ((inNetArr.take (g.I / 2)).map BitVec.toNat) 0 *
        inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) (g.I / 2)
          (((inNetArr.drop (g.I / 2)).take (g.I / 2)).map BitVec.toNat) 0 =
      BitVec.ofNat s.n_out.toNat (outWord g ρ) -
        BitVec.ofInt s.n_out.toNat (inWord (decide (s.spec = 1#32)) (g.I / 2) ρ 0) *
          BitVec.ofInt s.n_out.toNat (inWord (decide (s.spec = 1#32)) (g.I / 2) ρ (g.I / 2)) := by
  have h1 := hBind.outSum_eq ρ
  have h2 := hBind.inSum_eq ρ (decide (s.spec = 1#32)) 0 (Or.inl rfl)
  have h3 := hBind.inSum_eq ρ (decide (s.spec = 1#32)) (g.I / 2) (Or.inr rfl)
  dsimp only at h1 h2 h3
  rw [List.drop_zero] at h2
  rw [h1, h2, h3]

private theorem sp0_isNeg_eq {spec : BitVec 32} {iV kV nV : BitVec 32} {n : Nat}
    (hn : nV.toNat = n) (hn_ge : 1 ≤ n) (hi : iV.toNat < n) (hk : kV.toNat < n) :
    (decide (spec = 1#32) &&
      (decide (iV = nV - 1#32) != decide (kV = nV - 1#32))) =
      (decide (spec = 1#32) && (decide (iV.toNat + 1 = n) != decide (kV.toNat + 1 = n))) := by
  have hi_eq : decide (iV = nV - 1#32) = decide (iV.toNat + 1 = n) := by
    apply decide_eq_decide.mpr
    constructor <;> intro h
    · have : iV.toNat = (nV - 1#32).toNat := congrArg BitVec.toNat h
      c0_bv_omega
    · apply BitVec.eq_of_toNat_eq; c0_bv_omega
  have hk_eq : decide (kV = nV - 1#32) = decide (kV.toNat + 1 = n) := by
    apply decide_eq_decide.mpr
    constructor <;> intro h
    · have : kV.toNat = (nV - 1#32).toNat := congrArg BitVec.toNat h
      c0_bv_omega
    · apply BitVec.eq_of_toNat_eq; c0_bv_omega
  rw [hi_eq, hk_eq]

public theorem sp0_merge_exit_ok (Γ : T.Env)
    (hMerge : ∀ xs m Q X, arMergeProductsSpec xs m Q X →
      Γ "ar_merge_products" [i64, i32] [] xs m Q X)
    {cx : Val i64} {Q : Post [.bool]} {X : XPost}
    {s : ArCtxState} {g : Aig} {bindArr inNetArr outRefArr partnerArr : List (BitVec 32)}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {pt3 qn3 : Nat} {pool0_3 pool1_3 qm3 : List (BitVec 32)} {qs3 ql3 qh3 : List (BitVec 64)}
    {restQ R : Mem 64 → Prop} {m3 : Mem 64}
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2) (htcap30 : s.tcap.toNat < 2 ^ 30)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32)
    (hpt3 : pt3 ≤ s.pcap.toNat) (hqn3 : qn3 ≤ s.qcap.toNat)
    (hqn_tcap : qn3 ≤ s.tcap.toNat)
    (htm0_len : s.tcap.toNat ≤ tm0.length) (htm1_len : s.tcap.toNat ≤ tm1.length)
    (hts0_len : s.tcap.toNat ≤ ts0.length) (htl0_len : s.tcap.toNat ≤ tl0.length)
    (hth0_len : s.tcap.toNat ≤ th0.length) (hts1_len : s.tcap.toNat ≤ ts1.length)
    (htl1_len : s.tcap.toNat ≤ tl1.length) (hth1_len : s.tcap.toNat ≤ th1.length)
    (hp0_3 : pool0_3.length = pool0.length) (hp1_3 : pool1_3.length = pool1.length)
    (hqm3 : qm3.length = qm.length) (hqs3 : qs3.length = qs.length)
    (hql3 : ql3.length = ql.length) (hqh3 : qh3.length = qh.length)
    (hp0_len : s.pcap.toNat ≤ pool0.length) (hp1_len : s.pcap.toNat ≤ pool1.length)
    (hqm_len : s.qcap.toNat ≤ qm.length) (hqs_len : s.qcap.toNat ≤ qs.length)
    (hql_len : s.qcap.toNat ≤ ql.length) (hqh_len : s.qcap.toNat ≤ qh.length)
    (hix_len : s.qcap.toNat ≤ ix.length) (hix2_len : s.qcap.toNat ≤ ix2.length)
    (hix_eq : ix.length = ix2.length)
    (hMasks : MasksOk s.n_out.toNat s.mlo s.mhi)
    (hBind : BindRep s g bindArr inNetArr outRefArr)
    (hSl3 : ∀ i < qn3,
      MonoSliceOk (if s.pc.toNat = 0 then pool0_3 else pool1_3) (qm3.getD i 0#32).toNat pt3 ∧
      ((if s.pc.toNat = 0 then pool0_3 else pool1_3).getD
        (qm3.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted3 : ∀ i < qn3,
      MonoSorted (if s.pc.toNat = 0 then pool0_3 else pool1_3) (qm3.getD i 0#32).toNat)
    (hSig3 : SigOk (if s.pc.toNat = 0 then pool0_3 else pool1_3) qm3 qs3 qn3)
    (hW3 : monoTotalWords (if s.pc.toNat = 0 then pool0_3 else pool1_3) qm3 qn3 ≤ pt3)
    (hEv3 : ∀ ρ : Nat → Bool,
      polyEval s.n_out.toNat (cSig g ρ bindArr)
          (if s.pc.toNat = 0 then pool0_3 else pool1_3) qm3 ql3 qh3 qn3 =
        outSum s.n_out.toNat (cSig g ρ bindArr)
            ((outRefArr.take s.n_out.toNat).map BitVec.toNat) 0 -
          inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) (g.I / 2)
            ((inNetArr.take (g.I / 2)).map BitVec.toNat) 0 *
          inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) (g.I / 2)
            (((inNetArr.drop (g.I / 2)).take (g.I / 2)).map BitVec.toNat) 0)
    (hqBack : ∀ s' qm' qs' ql' qh',
      s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh →
      s'.ix = s.ix → s'.ix2 = s.ix2 → s'.bx = s.bx →
      s'.vq_off = s.vq_off → s'.vq = s.vq → s'.vq_skip = s.vq_skip →
      qm'.length = qm.length →
      qMem s' qm' qs' ql' qh' ix ix2 bx vqOff vq vqSkip =
        (array (t := i32) s'.qm qm' ⋆ array64 s'.qs qs' ⋆ array64 s'.ql ql' ⋆
          array64 s'.qh qh' ⋆ restQ))
    (hm3 : (arCtxMem cx (Sp0LoopState s pt3 qn3) ⋆ array (t := i32) s.bind bindArr ⋆
      array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
      array (t := i32) s.partner partnerArr ⋆
      tMem (Sp0LoopState s pt3 qn3) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0_3 pool1_3 ⋆
      array (t := i32) s.qm qm3 ⋆ array64 s.qs qs3 ⋆ array64 s.ql ql3 ⋆
      array64 s.qh qh3 ⋆ restQ ⋆ R) m3)
    (hQ : ∀ (ok : Bool) (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
        (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
        (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
        (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      s'.pc.toNat < 2 → s'.tc.toNat < 2 → s'.tn.toNat ≤ s.tcap.toNat →
      s'.ptop.toNat ≤ s.pcap.toNat → s'.qn.toNat ≤ s.qcap.toNat →
      s' = { s with
        tc := s'.tc, tn := s'.tn, ptop := s'.ptop, qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
      ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      qm'.length = qm.length → qs'.length = qs.length →
      ql'.length = ql.length → qh'.length = qh.length →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
        ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
        ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      (ok = true →
        (∀ i < s'.tn.toNat,
          MonoSliceOk (if s'.pc.toNat = 0 then pool0' else pool1')
              ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat s'.ptop.toNat ∧
          ((if s'.pc.toNat = 0 then pool0' else pool1').getD
            ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        (∀ i < s'.tn.toNat,
          MonoSorted (if s'.pc.toNat = 0 then pool0' else pool1')
            ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat) ∧
        SigOk (if s'.pc.toNat = 0 then pool0' else pool1')
          (if s'.tc.toNat = 0 then tm0' else tm1') (if s'.tc.toNat = 0 then ts0' else ts1')
          s'.tn.toNat ∧
        monoTotalWords (if s'.pc.toNat = 0 then pool0' else pool1')
          (if s'.tc.toNat = 0 then tm0' else tm1') s'.tn.toNat ≤ s'.ptop.toNat ∧
        ∀ ρ : Nat → Bool,
        polyEval s.n_out.toNat (cSig g ρ bindArr)
            (if s'.pc.toNat = 0 then pool0' else pool1')
            (if s'.tc.toNat = 0 then tm0' else tm1')
            (if s'.tc.toNat = 0 then tl0' else tl1')
            (if s'.tc.toNat = 0 then th0' else th1')
            s'.tn.toNat =
          BitVec.ofNat s.n_out.toNat (outWord g ρ) -
            BitVec.ofInt s.n_out.toNat (inWord (decide (s.spec = 1#32)) (g.I / 2) ρ 0) *
              BitVec.ofInt s.n_out.toNat
                (inWord (decide (s.spec = 1#32)) (g.I / 2) ρ (g.I / 2))) →
      (arCtxMem cx s' ⋆
        array (t := i32) s'.bind bindArr ⋆ array (t := i32) s'.in_net inNetArr ⋆
        array (t := i32) s'.out_ref outRefArr ⋆ array (t := i32) s'.partner partnerArr ⋆
        tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
        qMem s' qm' qs' ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆ R) m' →
      Q (ok, ⟨⟩) m') :
    wp Γ Q X (.call (as := [i64, i32]) (bs := []) "ar_merge_products" (Arg.var cx, Arg.imm 0#32, ())
      (fun _ => .ret (Arg.imm true, ()))) m3 := by
  have hq3_back : qMem (Sp0LoopState s pt3 qn3) qm3 qs3 ql3 qh3 ix ix2 bx vqOff vq vqSkip =
      (array (t := i32) s.qm qm3 ⋆ array64 s.qs qs3 ⋆ array64 s.ql ql3 ⋆
        array64 s.qh qh3 ⋆ restQ) :=
    hqBack (Sp0LoopState s pt3 qn3) qm3 qs3 ql3 qh3 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hqm3
  let Rmg := array (t := i32) s.bind bindArr ⋆ array (t := i32) s.in_net inNetArr ⋆
    array (t := i32) s.out_ref outRefArr ⋆ array (t := i32) s.partner partnerArr ⋆ R
  have hpt3_nat : (Sp0LoopState s pt3 qn3).ptop.toNat = pt3 := by
    dsimp only [Sp0LoopState]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pt3 < 2 ^ 64)]
  have hqn3_nat : (Sp0LoopState s pt3 qn3).qn.toNat = qn3 := by
    dsimp only [Sp0LoopState]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qn3 < 2 ^ 32)]
  refine wp_call_of_spec _ _ (hMerge _ _ _ _
    ⟨Sp0LoopState s pt3 qn3, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1,
      pool0_3, pool1_3, qm3, qs3, ql3, qh3, ix, ix2, bx, vqOff, vq, vqSkip, Rmg,
      by simp [Sp0LoopState, hpc], by simp [Sp0LoopState, htc],
      by simp [Sp0LoopState], by simp [Sp0LoopState, hqn3],
      by simp [Sp0LoopState, hpt3],
      by simp [Sp0LoopState, htcap30], by simp [Sp0LoopState, hqcap32],
      by simp [Sp0LoopState, hqn_tcap], Nat.zero_le _, Nat.zero_le _,
      ⟨fun _ h0 => absurd h0 (Nat.not_lt_zero _),
        fun _ h0 => absurd h0 (Nat.not_lt_zero _)⟩,
      by simp [Sp0LoopState, htm0_len], by simp [Sp0LoopState, htm1_len],
      by simp [Sp0LoopState, hts0_len], by simp [Sp0LoopState, htl0_len],
      by simp [Sp0LoopState, hth0_len], by simp [Sp0LoopState, hts1_len],
      by simp [Sp0LoopState, htl1_len], by simp [Sp0LoopState, hth1_len],
      by simp [Sp0LoopState, hp0_3, hp0_len], by simp [Sp0LoopState, hp1_3, hp1_len],
      by simp [Sp0LoopState, hqm3, hqm_len], by simp [Sp0LoopState, hqs3, hqs_len],
      by simp [Sp0LoopState, hql3, hql_len], by simp [Sp0LoopState, hqh3, hqh_len],
      by simp [Sp0LoopState, hix_len], by simp [Sp0LoopState, hix2_len],
      by simp [Sp0LoopState, hMasks],
      fun _ h0 => absurd h0 (Nat.not_lt_zero _),
      fun i hi => by
        rw [hpt3_nat]
        have hpc_eq : (Sp0LoopState s pt3 qn3).pc.toNat = s.pc.toNat := rfl
        rw [hpc_eq]
        exact hSl3 i (by rw [hqn3_nat] at hi; exact hi),
      fun _ h0 => absurd h0 (Nat.not_lt_zero _),
      fun i hi => by
        have hpc_eq : (Sp0LoopState s pt3 qn3).pc.toNat = s.pc.toNat := rfl
        rw [hpc_eq]
        exact hSorted3 i (by rw [hqn3_nat] at hi; exact hi),
      sigOk_empty _ _ _,
      by rw [show (Sp0LoopState s pt3 qn3).pc.toNat = s.pc.toNat from rfl, hqn3_nat]; exact hSig3,
      by rw [hq3_back]; exact sep_cast hm3 (by dsimp only [Rmg]; ac_rfl),
      fun s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' ql' qh' ix' ix2' m'
        htc' _ htn' hs' htm0' htm1' hts0' htl0' hth0' hts1' htl1' hth1'
        hql' hqh' hix_swap _ _ _ hSl' hSorted' hSig' hW' _ hEv' hm' => by
        c0_hsteps
        have hs'_eq : s' = { s with
            tc := s'.tc, tn := s'.tn, ptop := s'.ptop,
            qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } := by
          rw [hs']; rfl
        have hs'_pc : s'.pc.toNat = s.pc.toNat := by rw [hs']; rfl
        have hs'_ptop : s'.ptop.toNat = pt3 := by rw [hs']; exact hpt3_nat
        have hs'_qn : s'.qn.toNat = qn3 := by rw [hs']; exact hqn3_nat
        have hix'_len : ix'.length = ix.length := by
          rcases hix_swap with ⟨_, _, h1, _⟩ | ⟨_, _, h1, _⟩ <;> omega
        have hix2'_len : ix2'.length = ix2.length := by
          rcases hix_swap with ⟨_, _, _, h2⟩ | ⟨_, _, _, h2⟩ <;> omega
        have hix'_sw : (s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
            ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
            (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
            ix'.length = ix2.length ∧ ix2'.length = ix.length) := by
          rcases hix_swap with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
          · exact Or.inl ⟨h1, h2, h3, h4⟩
          · exact Or.inr ⟨h1, h2, h3, h4⟩
        have hm'_ok : (arCtxMem cx s' ⋆
            array (t := i32) s'.bind bindArr ⋆ array (t := i32) s'.in_net inNetArr ⋆
            array (t := i32) s'.out_ref outRefArr ⋆ array (t := i32) s'.partner partnerArr ⋆
            tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0_3 pool1_3 ⋆
            qMem s' qm3 qs3 ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆ R) m' :=
          buildSp0_pack_mem (cx := cx) (s := s) (s' := s')
            (bindArr := bindArr) (inNetArr := inNetArr) (outRefArr := outRefArr)
            (partnerArr := partnerArr) (tm0 := tm0') (tm1 := tm1')
            (ts0 := ts0') (tl0 := tl0') (th0 := th0') (ts1 := ts1') (tl1 := tl1') (th1 := th1')
            (pool0 := pool0_3) (pool1 := pool1_3) (qm := qm3) (qs := qs3) (ql := ql') (qh := qh')
            (ix := ix') (ix2 := ix2') (bx := bx) (vqOff := vqOff) (vq := vq) (vqSkip := vqSkip)
            (R := R) hs'_eq (sep_cast hm' (by dsimp only [Rmg]; ac_rfl))
        refine hQ true s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1'
          pool0_3 pool1_3 qm3 qs3 ql' qh' ix' ix2' m'
          (by rw [hs']; simp [Sp0LoopState, hpc])
          (by rw [htc']; simp [Sp0LoopState]; omega)
          (by simpa [Sp0LoopState] using htn')
          (by rw [hs'_ptop]; exact hpt3)
          (by rw [hs'_qn]; exact hqn3)
          hs'_eq htm0' htm1' hts0' htl0' hth0' hts1' htl1' hth1'
          hp0_3 hp1_3 hqm3 hqs3 (hql'.trans hql3) (hqh'.trans hqh3)
          hix'_sw ?_ hm'_ok
        rintro _
        have htc_flip : ∀ {α : Type} (a b : α),
            (if s'.tc.toNat = 0 then a else b) =
              (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then b else a) := by
          intro α a b
          change (if s'.tc.toNat = 0 then a else b) = (if s.tc.toNat = 0 then b else a)
          have htc'_eq : s'.tc.toNat = 1 - s.tc.toNat := by simpa [Sp0LoopState] using htc'
          rcases bv32_lt2_cases htc with h0 | h1
          · simp only [h0, BitVec.toNat_zero, Nat.sub_zero, htc'_eq,
              show ¬ (1 : Nat) = 0 by decide, ↓reduceIte]
          · simp only [h1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_self,
              htc'_eq, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte]
        have hSl_res : ∀ i < s'.tn.toNat,
            MonoSliceOk (if s'.pc.toNat = 0 then pool0_3 else pool1_3)
                ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat s'.ptop.toNat ∧
            ((if s'.pc.toNat = 0 then pool0_3 else pool1_3).getD
              ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat 0#32).toNat + 1 <
              2 ^ 32 := by
          intro i hi
          rw [hs'_pc, hs'_ptop, ← hpt3_nat, htc_flip tm0' tm1']
          exact hSl' i hi
        have hSorted_res : ∀ i < s'.tn.toNat,
            MonoSorted (if s'.pc.toNat = 0 then pool0_3 else pool1_3)
              ((if s'.tc.toNat = 0 then tm0' else tm1').getD i 0#32).toNat := by
          intro i hi; rw [hs'_pc, htc_flip tm0' tm1']; exact hSorted' i hi
        have hSig_res : SigOk (if s'.pc.toNat = 0 then pool0_3 else pool1_3)
            (if s'.tc.toNat = 0 then tm0' else tm1')
            (if s'.tc.toNat = 0 then ts0' else ts1') s'.tn.toNat := by
          rw [hs'_pc, htc_flip tm0' tm1', htc_flip ts0' ts1']; exact hSig'
        have hW_res : monoTotalWords (if s'.pc.toNat = 0 then pool0_3 else pool1_3)
            (if s'.tc.toNat = 0 then tm0' else tm1') s'.tn.toNat ≤ s'.ptop.toNat := by
          rw [hs'_pc, hs'_ptop, htc_flip tm0' tm1']
          rw [show (Sp0LoopState s pt3 qn3).tn.toNat = 0 from rfl, hqn3_nat,
            show (Sp0LoopState s pt3 qn3).pc.toNat = s.pc.toNat from rfl] at hW'
          simp only [monoTotalWords, List.range_zero, List.foldl_nil, Nat.zero_add] at hW'
          exact le_trans hW' hW3
        refine ⟨hSl_res, hSorted_res, hSig_res, hW_res, fun ρ => ?_⟩
        have hnb0 : nonBxTermSum s.n_out.toNat (cSig g ρ bindArr)
            (if (Sp0LoopState s pt3 qn3).pc.toNat = 0 then pool0_3 else pool1_3)
            (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then tm0 else tm1)
            (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then tl0 else tl1)
            (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then th0 else th1) bx 0
            (Sp0LoopState s pt3 qn3).tn.toNat = 0#(s.n_out.toNat) := by
          simp [Sp0LoopState, nonBxTermSum, nonBxRangeSum]
        have hEvT : polyEval s.n_out.toNat (cSig g ρ bindArr)
              (if s'.pc.toNat = 0 then pool0_3 else pool1_3)
              (if s'.tc.toNat = 0 then tm0' else tm1')
              (if s'.tc.toNat = 0 then tl0' else tl1')
              (if s'.tc.toNat = 0 then th0' else th1') s'.tn.toNat =
            polyEval s.n_out.toNat (cSig g ρ bindArr)
              (if s.pc.toNat = 0 then pool0_3 else pool1_3) qm3 ql3 qh3 qn3 := by
          have hEvρ := hEv' (cSig g ρ bindArr)
          change polyEval s.n_out.toNat (cSig g ρ bindArr)
              (if (Sp0LoopState s pt3 qn3).pc.toNat = 0 then pool0_3 else pool1_3)
              (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then tm1' else tm0')
              (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then tl1' else tl0')
              (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then th1' else th0') s'.tn.toNat =
            nonBxTermSum s.n_out.toNat (cSig g ρ bindArr)
              (if (Sp0LoopState s pt3 qn3).pc.toNat = 0 then pool0_3 else pool1_3)
              (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then tm0 else tm1)
              (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then tl0 else tl1)
              (if (Sp0LoopState s pt3 qn3).tc.toNat = 0 then th0 else th1) bx 0
              (Sp0LoopState s pt3 qn3).tn.toNat +
            polyEval s.n_out.toNat (cSig g ρ bindArr)
              (if (Sp0LoopState s pt3 qn3).pc.toNat = 0 then pool0_3 else pool1_3)
              qm3 ql3 qh3 (Sp0LoopState s pt3 qn3).qn.toNat at hEvρ
          rw [hnb0, BitVec.zero_add, hqn3_nat,
            show (Sp0LoopState s pt3 qn3).pc.toNat = s.pc.toNat from rfl] at hEvρ
          rw [hs'_pc, htc_flip tm0' tm1', htc_flip tl0' tl1', htc_flip th0' th1']
          exact hEvρ
        rw [hEvT, hEv3 ρ]
        exact sp0_done_eval_eq hBind ρ⟩)

@[expose] public def sp0KBodyExpr (cx : Val i64) (nV iV kV : Val i32) (JJ : Cont []) :
    Expr Val Cont [.bool] :=
  match ar_build_sp0_body Val Cont (cx, ()) with
  | @Expr.let_ _ _ _ [.bits 64] _ k1 => match k1 (cx + 640#64, ()) with
    | @Expr.load _ _ _ (.bits 32) _ k2 => match k2 nV with
      | @Expr.let_ _ _ _ [.bits 32] _ k3 => match k3 (nV, ()) with
        | @Expr.let_ _ _ _ [.bits 64] _ k4 => match k4 (cx + 672#64, ()) with
          | .store _ _ k5 => match k5 with
            | @Expr.let_ _ _ _ [.bits 64] _ k6 => match k6 (cx + 424#64, ()) with
              | .store _ _ k7 => match k7 with
                | @Expr.let_ _ _ _ [.bits 64] _ k8 => match k8 (cx + 684#64, ()) with
                  | .store _ _ k9 => match k9 with
                    | @Expr.group _ _ _ [[.bits 32]] bsJ _ =>
                      match bsJ (fun _ _ => False, ()) with
                      | .cons bJ _ => match bJ (0#32, ()) with
                        | @Expr.let_ _ _ _ [.bits 64] _ kj1 => match kj1 (cx + 616#64, ()) with
                          | @Expr.load _ _ _ (.bits 32) _ kj2 => match kj2 0#32 with
                            | @Expr.let_ _ _ _ [.bool] _ kj3 => match kj3 (false, ()) with
                              | .jnz _ _ eI => match eI with
                                | @Expr.group _ _ _ [[.bits 32]] bsI _ =>
                                  match bsI (fun _ _ => False, ()) with
                                  | .cons bI _ => match bI (iV, ()) with
                                    | @Expr.let_ _ _ _ [.bool] _ ki1 => match ki1 (false, ()) with
                                      | .jnz _ eK _ => match eK with
                                        | @Expr.group _ _ _ [[.bits 32]] bsK _ =>
                                          match bsK (fun _ _ => False, ()) with
                                          | .cons bK _ => match bK (kV, ()) with
                                            | @Expr.let_ _ _ _ [.bool] _ kk1 =>
                                              match kk1 (false, ()) with
                                              | .jnz _ eKG _ => match eKG with
                                                | @Expr.group _ _ _ [[]] _ eBody => eBody (JJ, ())
                                                | _ => .ret (Arg.imm false, ())
                                              | _ => .ret (Arg.imm false, ())
                                            | _ => .ret (Arg.imm false, ())
                                          | _ => .ret (Arg.imm false, ())
                                        | _ => .ret (Arg.imm false, ())
                                      | _ => .ret (Arg.imm false, ())
                                    | _ => .ret (Arg.imm false, ())
                                  | _ => .ret (Arg.imm false, ())
                                | _ => .ret (Arg.imm false, ())
                              | _ => .ret (Arg.imm false, ())
                            | _ => .ret (Arg.imm false, ())
                          | _ => .ret (Arg.imm false, ())
                        | _ => .ret (Arg.imm false, ())
                      | _ => .ret (Arg.imm false, ())
                    | _ => .ret (Arg.imm false, ())
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

private theorem sp0_bool_ofNat_eq_decide {a b : Bool} {p q : Prop} [Decidable p] [Decidable q]
    (ha : a = true ↔ p) (hb : b = true ↔ q)
    (h : BitVec.ofNat 32 a.toNat = BitVec.ofNat 32 b.toNat) :
    decide p = decide q := by
  cases a <;> cases b <;> simp_all

private theorem sp0_bool_ofNat_ne_decide {a b : Bool} {p q : Prop} [Decidable p] [Decidable q]
    (ha : a = true ↔ p) (hb : b = true ↔ q)
    (h : BitVec.ofNat 32 a.toNat ≠ BitVec.ofNat 32 b.toNat) :
    decide p ≠ decide q := by
  cases a <;> cases b <;> simp_all

public theorem sp0_k_body_wp (Γ : T.Env)
    (hAddQ : ∀ xs m Q X, arAddQSpec xs m Q X →
      Γ "ar_add_q" [i64, i32, i32, i32, i64, i64] [.bool] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X →
      Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    (hCpow2 : ∀ xs m Q X, arCpow2Spec xs m Q X →
      Γ "ar_cpow2" [i64, i32] [i64, i64] xs m Q X)
    {cx : Val i64} {nV iV kV : Val i32} {JJ : Cont []}
    {Q : Post [.bool]} {X : XPost} {s : ArCtxState} {g : Aig}
    {bindArr inNetArr outRefArr partnerArr : List (BitVec 32)}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {restQ R : Mem 64 → Prop} {n ptK qnK : Nat}
    {pool0K pool1K qmK : List (BitVec 32)} {qsK qlK qhK : List (BitVec 64)} {mK : Mem 64}
    (hnV : nV = s.n_in >>> 1#32) (hn_eq : nV.toNat = n) (hn_ge1 : 1 ≤ n)
    (hi_lt : iV.toNat < n) (hk_lt : kV.toNat < n)
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2)
    (hptK : ptK ≤ s.pcap.toNat) (hqnK : qnK ≤ s.qcap.toNat)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hnnets : s.n_nets.toNat ≤ 0x3FFFFFFF) (hnn2 : 2 * s.n_nets.toNat < 2 ^ 32)
    (hp0K : pool0K.length = pool0.length) (hp1K : pool1K.length = pool1.length)
    (hs_p0 : s.pcap.toNat ≤ pool0.length) (hs_p1 : s.pcap.toNat ≤ pool1.length)
    (hqmK : qmK.length = qm.length) (hqsK : qsK.length = qs.length)
    (hqlK : qlK.length = ql.length) (hqhK : qhK.length = qh.length)
    (hs_qm : s.qcap.toNat ≤ qm.length) (hs_qs : s.qcap.toNat ≤ qs.length)
    (hs_ql : s.qcap.toNat ≤ ql.length) (hs_qh : s.qcap.toNat ≤ qh.length)
    (hMasks : MasksOk s.n_out.toNat s.mlo s.mhi) (hBind : BindRep s g bindArr inNetArr outRefArr)
    (hPart : ∀ ρ : Nat → Bool, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr)
    (h2n : 2 * n = g.I) (hi_in : iV.toNat < inNetArr.length)
    (hnk_in : n + kV.toNat < inNetArr.length)
    (hSlK : ∀ idx < qnK,
      MonoSliceOk (if s.pc.toNat = 0 then pool0K else pool1K) (qmK.getD idx 0#32).toNat ptK ∧
      ((if s.pc.toNat = 0 then pool0K else pool1K).getD
        (qmK.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSortedK : ∀ idx < qnK,
      MonoSorted (if s.pc.toNat = 0 then pool0K else pool1K) (qmK.getD idx 0#32).toNat)
    (hSigK : SigOk (if s.pc.toNat = 0 then pool0K else pool1K) qmK qsK qnK)
    (hWK : monoTotalWords (if s.pc.toNat = 0 then pool0K else pool1K) qmK qnK ≤ ptK)
    (hEvK : ∀ ρ : Nat → Bool,
      polyEval s.n_out.toNat (cSig g ρ bindArr)
          (if s.pc.toNat = 0 then pool0K else pool1K) qmK qlK qhK qnK =
        outSum s.n_out.toNat (cSig g ρ bindArr)
            ((outRefArr.take s.n_out.toNat).map BitVec.toNat) 0 -
          inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
            ((inNetArr.take iV.toNat).map BitVec.toNat) 0 *
          inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
            (((inNetArr.drop n).take n).map BitVec.toNat) 0 -
          inTerm s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
            (inNetArr.getD iV.toNat 0#32).toNat iV.toNat *
          inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
            (((inNetArr.drop n).take kV.toNat).map BitVec.toNat) 0)
    (hmK : (arCtxMem cx (Sp0LoopState s ptK qnK) ⋆ array (t := i32) s.bind bindArr ⋆
      array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
      array (t := i32) s.partner partnerArr ⋆
      tMem (Sp0LoopState s ptK qnK) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0K pool1K ⋆
      array (t := i32) s.qm qmK ⋆ array64 s.qs qsK ⋆ array64 s.ql qlK ⋆
      array64 s.qh qhK ⋆ restQ ⋆ R) mK)
    (hFail : ∀ {ptF qnF : Nat} {pool0F pool1F qmF : List (BitVec 32)}
        {qsF qlF qhF : List (BitVec 64)} {mF : Mem 64},
      ptF ≤ s.pcap.toNat → qnF ≤ s.qcap.toNat →
      pool0F.length = pool0.length → pool1F.length = pool1.length →
      qmF.length = qm.length → qsF.length = qs.length →
      qlF.length = ql.length → qhF.length = qh.length →
      (arCtxMem cx (Sp0LoopState s ptF qnF) ⋆ array (t := i32) s.bind bindArr ⋆
        array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
        array (t := i32) s.partner partnerArr ⋆
        tMem (Sp0LoopState s ptF qnF) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0F pool1F ⋆
        array (t := i32) s.qm qmF ⋆ array64 s.qs qsF ⋆ array64 s.ql qlF ⋆
        array64 s.qh qhF ⋆ restQ ⋆ R) mF →
      Q (false, ⟨⟩) mF)
    (hJJ : ∀ (ys : Tup Val []) (m' : Mem 64),
      (∃ (pt' qn' : Nat) (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64)),
        pt' ≤ s.pcap.toNat ∧ qn' ≤ s.qcap.toNat ∧
        pool0'.length = pool0.length ∧ pool1'.length = pool1.length ∧
        qm'.length = qm.length ∧ qs'.length = qs.length ∧
        ql'.length = ql.length ∧ qh'.length = qh.length ∧
        (∀ idx < qn',
          MonoSliceOk (if s.pc.toNat = 0 then pool0' else pool1') (qm'.getD idx 0#32).toNat pt' ∧
          ((if s.pc.toNat = 0 then pool0' else pool1').getD
            (qm'.getD idx 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        (∀ idx < qn',
          MonoSorted (if s.pc.toNat = 0 then pool0' else pool1') (qm'.getD idx 0#32).toNat) ∧
        SigOk (if s.pc.toNat = 0 then pool0' else pool1') qm' qs' qn' ∧
        monoTotalWords (if s.pc.toNat = 0 then pool0' else pool1') qm' qn' ≤ pt' ∧
        (∀ ρ : Nat → Bool,
          polyEval s.n_out.toNat (cSig g ρ bindArr)
              (if s.pc.toNat = 0 then pool0' else pool1') qm' ql' qh' qn' =
            outSum s.n_out.toNat (cSig g ρ bindArr)
                ((outRefArr.take s.n_out.toNat).map BitVec.toNat) 0 -
              inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                ((inNetArr.take iV.toNat).map BitVec.toNat) 0 *
              inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                (((inNetArr.drop n).take n).map BitVec.toNat) 0 -
              inTerm s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                (inNetArr.getD iV.toNat 0#32).toNat iV.toNat *
              inSum s.n_out.toNat (cSig g ρ bindArr) (decide (s.spec = 1#32)) n
                (((inNetArr.drop n).take (kV.toNat + 1)).map BitVec.toNat) 0) ∧
        (arCtxMem cx (Sp0LoopState s pt' qn') ⋆ array (t := i32) s.bind bindArr ⋆
          array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
          array (t := i32) s.partner partnerArr ⋆
          tMem (Sp0LoopState s pt' qn') tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0' pool1' ⋆
          array (t := i32) s.qm qm' ⋆ array64 s.qs qs' ⋆ array64 s.ql ql' ⋆
          array64 s.qh qh' ⋆ restQ ⋆ R) m') →
      JJ ys m') :
    wp Γ Q X (sp0KBodyExpr cx nV iV kV JJ) mK := by
  subst nV
  have hout_bd := hBind.out_bounds
  have hnin_lt := hBind.in_eq
  dsimp only [sp0KBodyExpr]
  c0_hsteps_nogrp
  · have hik_32 : iV.toNat + kV.toNat < 2 ^ 32 := by have := s.n_in.isLt; have := hBind.in_eq; omega
    have hik_toNat : (iV + kV).toNat = iV.toNat + kV.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hik_32]
    have hik_lt : iV.toNat + kV.toNat < s.n_out.toNat := by
      have hc' : (iV + kV).toNat < (Sp0LoopState s ptK qnK).n_out.toNat := hc
      simpa [Sp0LoopState, hik_toNat] using hc'
    have hnet_a := (hBind.in_ok iV.toNat (by omega)).1
    have hnet_b := (hBind.in_ok (n + kV.toNat) (by omega)).1
    let va := (inNetArr.getD iV.toNat 0#32).toNat
    let vb := (inNetArr.getD (n + kV.toNat) 0#32).toNat
    let Rcp2 := array (t := i32) s.bind bindArr ⋆
      array (t := i32) s.in_net inNetArr ⋆ array (t := i32) s.out_ref outRefArr ⋆
      array (t := i32) s.partner partnerArr ⋆
      tMem (Sp0LoopState s ptK qnK) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0K pool1K ⋆
      array (t := i32) s.qm qmK ⋆ array64 s.qs qsK ⋆ array64 s.ql qlK ⋆
      array64 s.qh qhK ⋆ restQ ⋆ R
    have hmK_in1 : (array (t := i32) s.in_net inNetArr ⋆
        (arCtxMem cx (Sp0LoopState s ptK qnK) ⋆ array (t := i32) s.bind bindArr ⋆
          array (t := i32) s.out_ref outRefArr ⋆ array (t := i32) s.partner partnerArr ⋆
          tMem (Sp0LoopState s ptK qnK) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0K pool1K ⋆
          array (t := i32) s.qm qmK ⋆ array64 s.qs qsK ⋆ array64 s.ql qlK ⋆
          array64 s.qh qhK ⋆ restQ ⋆ R)) mK :=
      sep_cast hmK (by ac_rfl)
    refine wp_load_arr32_idx (off := 0) (i := iV) (hm := hmK_in1) ?_ ?_ ?_
    · dsimp only [Arg.val, Sp0LoopState]
      rw [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    · simpa using hi_in
    c0_hsteps_nogrp
    have hnv_k : (s.n_in >>> 1#32 + kV).toNat = n + kV.toNat := by
      have h1 : (s.n_in >>> 1#32).toNat = n := hn_eq
      rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by have := s.n_in.isLt; omega)]
    have hnv_k_lt : (s.n_in >>> 1#32 + kV).toNat < inNetArr.length := by omega
    refine wp_load_arr32_idx (off := 0) (i := s.n_in >>> 1#32 + kV) (hm := hmK_in1) ?_ ?_ ?_
    · dsimp only [Arg.val, Sp0LoopState]
      rw [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    · simpa using hnv_k_lt
    c0_hsteps_nogrp
    apply wp_call_of_spec
    refine hCpow2 _ _ _ _
      ⟨Sp0LoopState s ptK qnK, Rcp2, by simpa [Sp0LoopState] using hMasks,
        sep_cast hmK (by dsimp only [Rcp2]; ac_rfl), fun l0 h0 hlh0 => ?_⟩
    have hlh0' : coeff128 s.n_out.toNat l0 h0 =
        BitVec.ofNat s.n_out.toNat (2 ^ (iV.toNat + kV.toNat)) := by
      simpa [Sp0LoopState, hik_toNat, show iV.toNat + kV.toNat < 128 by omega] using hlh0
    let isNeg : Bool :=
      decide (s.spec = 1#32) && (decide (iV.toNat + 1 = n) != decide (kV.toNat + 1 = n))
    c0_hsteps_nogrp
    refine wp_join_group (fun (v : Tup Val [.bool]) m' => m' = mK ∧ v.1 = isNeg) ?_ ?_
    · rintro Jb ⟨bNeg, ⟨⟩⟩ mB ⟨hmB, hbNeg⟩; subst mB
      dsimp only at hbNeg; subst hbNeg
      c0_hsteps_nogrp
      refine wp_join_group (fun (v : Tup Val [i64, i64]) m' =>
          m' = mK ∧ coeff128 s.n_out.toNat v.1 v.2.1 =
            if isNeg then BitVec.ofNat s.n_out.toNat (2 ^ (iV.toNat + kV.toNat))
            else -BitVec.ofNat s.n_out.toNat (2 ^ (iV.toNat + kV.toNat))) ?_ ?_
      · rintro Jlh ⟨l1, h1, ⟨⟩⟩ mLH ⟨hmLH, hlh1⟩; subst mLH
        have hlh1' : coeff128 s.n_out.toNat l1 h1 =
            if isNeg then BitVec.ofNat s.n_out.toNat (2 ^ (iV.toNat + kV.toNat))
            else -BitVec.ofNat s.n_out.toNat (2 ^ (iV.toNat + kV.toNat)) := by simpa using hlh1
        c0_hsteps_nogrp
        let xa := 2#32 * inNetArr[0 + iV.toNat]'(by simpa using hi_in)
        let xb := 2#32 * inNetArr[0 + (s.n_in >>> 1#32 + kV).toNat]'(by simpa using hnv_k_lt)
        have hxa_eq : xa.toNat = 2 * va := by
          dsimp only [xa, va]
          rw [← getD_eq_getElem inNetArr 0#32 (by simpa using hi_in), Nat.zero_add]; c0_bv_omega
        have hxb_eq : xb.toNat = 2 * vb := by
          dsimp only [xb, vb]
          rw [← getD_eq_getElem inNetArr 0#32 (by simpa using hnv_k_lt), Nat.zero_add, hnv_k]
          c0_bv_omega
        refine wp_join_group (fun (v : Tup Val [i32]) m' =>
            m' = mK ∧ v.1.toNat = (if 2 * va < 2 * vb then 2 * va else 2 * vb)) ?_ ?_
        · rintro J0 ⟨sy0, ⟨⟩⟩ mS0 ⟨hmS0, hsy0⟩; subst mS0
          have hsy0' : sy0.toNat = if 2 * va < 2 * vb then 2 * va else 2 * vb := by simpa using hsy0
          c0_hsteps_nogrp
          refine wp_join_group (fun (v : Tup Val [i32]) m' =>
              m' = mK ∧ v.1.toNat = (if 2 * va < 2 * vb then 2 * vb else 2 * va)) ?_ ?_
          · rintro J1 ⟨sy1, ⟨⟩⟩ mS1 ⟨hmS1, hsy1⟩; subst mS1
            have hsy1' : sy1.toNat =
                if 2 * va < 2 * vb then 2 * vb else 2 * va := by simpa using hsy1
            c0_hsteps_nogrp
            refine wp_join_group (fun (v : Tup Val [i32]) m' =>
                m' = mK ∧ v.1.toNat = (if 2 * va = 2 * vb then 1 else 2)) ?_ ?_
            · rintro J2 ⟨len, ⟨⟩⟩ mL2 ⟨hmL2, hlen⟩; subst mL2
              have hlen' : len.toNat = if 2 * va = 2 * vb then 1 else 2 := by simpa using hlen
              refine sp0_call_addQ_wp Γ hAddQ
                (if 2 * va = 2 * vb then 1 else 2)
                (if 2 * va < 2 * vb then 2 * va else 2 * vb)
                (if 2 * va < 2 * vb then 2 * vb else 2 * va)
                hlen' hsy0' hsy1'
                rfl hptK hqnK hpc htc hqcap32 hpcap32 hnnets hnn2 hp0K hp1K hs_p0 hs_p1
                hqmK hqsK hqlK hqhK hs_qm hs_qs hs_ql hs_qh hMasks hPart hSlK hSortedK hSigK
                (fun h2 => by
                  by_cases heq : 2 * va = 2 * vb
                  · simp [heq] at h2
                  · by_cases hlt : 2 * va < 2 * vb <;> simp [hlt] <;> omega)
                hWK hmK hFail
                (fun pt' qn' pool0' pool1' qm' qs' ql' qh' m'
                  hpt' hqn' hp0' hp1' hqm' hqs' hql' hqh' hSl' hSorted' hSig' hW' hEv' hm' => by
                  c0_hsteps
                  refine hJJ ⟨⟩ m' ⟨pt', qn', pool0', pool1', qm', qs', ql', qh',
                    hpt', hqn', hp0', hp1', hqm', hqs', hql', hqh', hSl', hSorted', hSig', hW',
                    ?_, hm'⟩
                  intro ρ
                  rw [sp0_inSum_drop_take_succ s.n_out.toNat (cSig g ρ bindArr)
                      (decide (s.spec = 1#32)) n inNetArr hnk_in]
                  exact sp0_loop2_step_lt hik_lt (by omega) (cSig g ρ bindArr)
                    (decide (s.spec = 1#32)) _ _ _ _ _ va vb (hEvK ρ) (hEv' ρ)
                    (by dsimp only [isNeg] at hlh1'; simpa only [Bool.and_eq_true] using hlh1'))
            · intro J2 hJ2; c0_hsteps_nogrp
              · c0_hsteps; refine hJ2 _ _ ⟨rfl, ?_⟩
                have heq : 2 * va = 2 * vb := by
                  rw [← hxa_eq, ← hxb_eq]; exact congrArg BitVec.toNat hc
                simp [heq]
              · c0_hsteps; refine hJ2 _ _ ⟨rfl, ?_⟩
                have hne : 2 * va ≠ 2 * vb := by
                  intro h; apply hc; apply BitVec.eq_of_toNat_eq
                  change xa.toNat = xb.toNat; rw [hxa_eq, hxb_eq, h]
                simp [hne]
          · intro J1 hJ1; c0_hsteps_nogrp
            · c0_hsteps; refine hJ1 _ _ ⟨rfl, ?_⟩
              have hlt : 2 * va < 2 * vb := by rw [← hxa_eq, ← hxb_eq]; exact hc
              simp only [hlt, ↓reduceIte]; exact hxb_eq
            · c0_hsteps; refine hJ1 _ _ ⟨rfl, ?_⟩
              have hnlt : ¬(2 * va < 2 * vb) := by rw [← hxa_eq, ← hxb_eq]; exact hc
              simp only [hnlt, ↓reduceIte]; exact hxa_eq
        · intro J0 hJ0; c0_hsteps_nogrp
          · c0_hsteps; refine hJ0 _ _ ⟨rfl, ?_⟩
            have hlt : 2 * va < 2 * vb := by rw [← hxa_eq, ← hxb_eq]; exact hc
            simp only [hlt, ↓reduceIte]; exact hxa_eq
          · c0_hsteps; refine hJ0 _ _ ⟨rfl, ?_⟩
            have hnlt : ¬(2 * va < 2 * vb) := by rw [← hxa_eq, ← hxb_eq]; exact hc
            simp only [hnlt, ↓reduceIte]; exact hxb_eq
      · intro Jlh hJlh; c0_hsteps_nogrp
        · c0_hsteps
          have his : isNeg = true := hc
          refine hJlh (l0, h0, ⟨⟩) mK ⟨rfl, ?_⟩
          dsimp only; rw [ite_eq_left his, hlh0']
        · c0_hsteps_nogrp
          let Rcn2 := array (t := i32) s.bind bindArr ⋆ array (t := i32) s.in_net inNetArr ⋆
            array (t := i32) s.out_ref outRefArr ⋆ array (t := i32) s.partner partnerArr ⋆
            tMem (Sp0LoopState s ptK qnK) tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0K pool1K ⋆
            array (t := i32) s.qm qmK ⋆ array64 s.qs qsK ⋆ array64 s.ql qlK ⋆
            array64 s.qh qhK ⋆ restQ ⋆ R
          refine wp_call_of_spec _ _ (hCneg _ _ _ _
            ⟨Sp0LoopState s ptK qnK, Rcn2, by simpa [Sp0LoopState] using hMasks,
              by exact sep_cast hmK (by dsimp only [Rcn2]; ac_rfl), fun l1 h1 hlh1 => ?_⟩)
          c0_hsteps
          have hc_neg : isNeg = false := Bool.eq_false_iff.mpr (by simpa using hc)
          have hlh1' : coeff128 s.n_out.toNat l1 h1 = -coeff128 s.n_out.toNat l0 h0 := hlh1
          refine hJlh (l1, h1, ⟨⟩) mK ⟨rfl, ?_⟩
          dsimp only; rw [ite_eq_right (by rw [hc_neg]; exact Bool.false_ne_true), hlh1', hlh0']
    · intro Jb hJb; c0_hsteps_nogrp
      · c0_hsteps; refine hJb (true, ⟨⟩) mK ⟨rfl, ?_⟩
        dsimp only [isNeg]
        have hsn := sp0_isNeg_eq (spec := s.spec) hn_eq hn_ge1 hi_lt hk_lt
        rw [← hsn]; symm; rw [Bool.and_eq_true, bne_iff_ne]
        refine ⟨decide_eq_true (by simpa [Sp0LoopState] using ‹_›),
          sp0_bool_ofNat_ne_decide beq_iff_eq beq_iff_eq (by
            simpa only [show (1 : BitVec 32) = 1#32 from rfl] using ‹_›)⟩
      · c0_hsteps; refine hJb (false, ⟨⟩) mK ⟨rfl, ?_⟩
        dsimp only [isNeg]
        have hsn := sp0_isNeg_eq (spec := s.spec) hn_eq hn_ge1 hi_lt hk_lt
        rw [← hsn]; symm; rw [Bool.and_eq_false_iff, bne_eq_false_iff_eq]
        right; exact sp0_bool_ofNat_eq_decide beq_iff_eq beq_iff_eq (by
          simpa only [show (1 : BitVec 32) = 1#32 from rfl] using hc)
      · c0_hsteps; refine hJb (false, ⟨⟩) mK ⟨rfl, ?_⟩
        dsimp only [isNeg]
        have hspec_ne : s.spec ≠ 1#32 := by simpa [Sp0LoopState] using hc
        rw [decide_eq_false hspec_ne, Bool.false_and]
  · have hik_32 : iV.toNat + kV.toNat < 2 ^ 32 := by have := s.n_in.isLt; have := hBind.in_eq; omega
    have hik_toNat : (iV + kV).toNat = iV.toNat + kV.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hik_32]
    have hik_ge : s.n_out.toNat ≤ iV.toNat + kV.toNat := by
      have hc' : ¬ (iV + kV).toNat < (Sp0LoopState s ptK qnK).n_out.toNat := hc
      simpa [Sp0LoopState, hik_toNat] using hc'
    c0_hsteps
    refine hJJ ⟨⟩ mK ⟨ptK, qnK, pool0K, pool1K, qmK, qsK, qlK, qhK,
      hptK, hqnK, hp0K, hp1K, hqmK, hqsK, hqlK, hqhK, hSlK, hSortedK, hSigK, hWK, ?_, hmK⟩
    intro ρ
    rw [sp0_inSum_drop_take_succ s.n_out.toNat (cSig g ρ bindArr)
      (decide (s.spec = 1#32)) n inNetArr hnk_in]
    exact sp0_loop2_step_ge hik_ge (cSig g ρ bindArr) (decide (s.spec = 1#32)) _ _ _ _ _ _ (hEvK ρ)

end LeanQbe.T.Examples.Arisca.Proof
