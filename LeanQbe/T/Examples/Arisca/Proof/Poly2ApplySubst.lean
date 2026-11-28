/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2ApplyVq
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA `ar_apply` Loop 4 Helpers & Exit Handler (`Arisca.Proof.Poly2ApplySubst`)

Pure substitution step invariants, vanishing-pair lemmas, loop invariants (`ApplyInnerInv`,
`ApplyOuterInv`), and `apply_outer_exit_wp` (`ar_merge_products` + final `polyEval` preservation)
supporting `ar_apply_wp` (`Arisca.Proof.Poly2`).
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

public section

/-! ## 1. Pure Helpers & Array Focus Wrappers -/

theorem arCtxMem_lengthsOk {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) : ArCtxLengthsOk s := by
  unfold arCtxMem at hm
  exact (sep_pure_l (φ := ArCtxLengthsOk s) (P := (arCtxTree cx s).eval) (R := R)).mp hm |>.1

theorem wp_load_arr8_u32 {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val i64} {k : Val i8 → Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 8)} {i : BitVec 32} {R : Mem 64 → Prop}
    (ha : a.val = base + BitVec.setWidth 64 i) (hi : i.toNat < xs.length)
    (hm : (array (t := i8) base xs ⋆ R) m)
    (hk : wp Γ Q X (k (xs[i.toNat]'hi)) m) :
    wp Γ Q X (.load i8 a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 ((i8 : Ty).bytes * i.toNat) := by
    rw [ha]; congr 1; apply BitVec.eq_of_toNat_eq
    have hi64 : i.toNat < 2 ^ 64 := lt_trans i.isLt (by decide)
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi64, show (i8 : Ty).bytes = 1 from rfl, Nat.one_mul,
      Nat.mod_eq_of_lt hi64]
  exact head_wp_load ha' (loadVal_array (t := i8) (i := i.toNat) (by decide) hi hm) hk

theorem polyEval_range_congr (nOut : Nat) (σ : Nat → Bool)
    (p1 p2 m1 m2 : List (BitVec 32)) (l1 l2 h1 h2 : List (BitVec 64)) (lo n : Nat)
    (h : ∀ k < n, termEval nOut σ p1 m1 l1 h1 (lo + k) = termEval nOut σ p2 m2 l2 h2 (lo + k)) :
    polyEvalRange nOut σ p1 m1 l1 h1 lo n = polyEvalRange nOut σ p2 m2 l2 h2 lo n := by
  induction n with
  | zero => simp [polyEvalRange_zero]
  | succ n ih =>
    rw [polyEvalRange_succ, polyEvalRange_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
      h n (Nat.lt_succ_self n)]

theorem apply_bv32_add1_lt {x : BitVec 32} {bound : Nat}
    (hx : x.toNat < bound) (hb : bound < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem apply_pt_plus_len {pt : BitVec 64} {outLen : BitVec 32} {pcap : Nat}
    (hle : pt.toNat + (outLen.toNat + 1) ≤ pcap) (hpcap : pcap < 2 ^ 32) :
    (pt + BitVec.setWidth 64 outLen + 1#64).toNat = pt.toNat + outLen.toNat + 1 := by
  have h1 : (BitVec.setWidth 64 outLen : BitVec 64).toNat = outLen.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans outLen.isLt (by decide))]
  have h2 : pt.toNat + outLen.toNat < 2 ^ 64 := by omega
  have h3 : pt.toNat + outLen.toNat + 1 < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]

theorem apply_bv32_of_pt {pt : BitVec 64} (hpt : pt.toNat < 2 ^ 32) :
    ((pt.setWidth 32 : BitVec 32)).toNat = pt.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpt]

theorem apply_cmul_zero {nOut : Nat} : coeff128 nOut 0#64 0#64 = 0#nOut := by
  simp [coeff128]

private theorem monoTotalWords_congr_prefix {p1 p2 m1 m2 : List (BitVec 32)} {n bd : Nat}
    (hsl : ∀ k < n, MonoSliceOk p1 (m1.getD k 0#32).toNat bd)
    (hp : ∀ idx < bd, p2.getD idx 0#32 = p1.getD idx 0#32)
    (hm : ∀ k < n, m2.getD k 0#32 = m1.getD k 0#32) :
    monoTotalWords p2 m2 n = monoTotalWords p1 m1 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [monoTotalWords_succ, monoTotalWords_succ,
      ih (fun j hj => hsl j (by omega)) (fun j hj => hm j (by omega)),
      hm k (Nat.lt_succ_self k), hp _ (hsl k (Nat.lt_succ_self k)).1]

theorem apply_emit_step_inv
    {sPt pt qn : Nat}
    {dstPool poolL out' qmL : List (BitVec 32)}
    {qsL qlL qhL : List (BitVec 64)}
    {sig l h : BitVec 64}
    (hspt : sPt ≤ pt) (hpt_len : pt ≤ poolL.length)
    (hpt'_32 : pt + (out'.getD 0 0#32).toNat + 1 < 2 ^ 32)
    (hqn_qm : qn < qmL.length) (hqn_qs : qn < qsL.length)
    (hout_len : out'.length = poolL.length - pt)
    (hout_sorted : MonoSorted out' 0)
    (hsig : ∀ x ∈ symListAt out' 0, (sig &&& sigBit (BitVec.ofNat 32 x)) ≠ 0#64)
    (hpref_dst : ∀ idx < sPt, poolL.getD idx 0#32 = dstPool.getD idx 0#32)
    (hqm_sl : ∀ i < qn,
      MonoSliceOk poolL (qmL.getD i 0#32).toNat pt ∧
      (poolL.getD (qmL.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hqm_sorted : ∀ i < qn, MonoSorted poolL (qmL.getD i 0#32).toNat)
    (hqm_sig : SigOk poolL qmL qsL qn)
    (hwords : sPt + monoTotalWords poolL qmL qn ≤ pt) :
    let pool' := poolL.take pt ++ out'
    let pt' := pt + (out'.getD 0 0#32).toNat + 1
    let qm' := qmL.set qn (BitVec.ofNat 32 pt)
    let qs' := qsL.set qn sig
    let _ql' := qlL.set qn l
    let _qh' := qhL.set qn h
    pool'.length = poolL.length ∧
    (∀ idx < sPt, pool'.getD idx 0#32 = dstPool.getD idx 0#32) ∧
    (∀ idx < pt, pool'.getD idx 0#32 = poolL.getD idx 0#32) ∧
    (∀ r ≤ (out'.getD 0 0#32).toNat, pool'.getD (pt + r) 0#32 = out'.getD r 0#32) ∧
    (∀ i < qn + 1,
      MonoSliceOk pool' (qm'.getD i 0#32).toNat pt' ∧
      (pool'.getD (qm'.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
    (∀ i < qn + 1, MonoSorted pool' (qm'.getD i 0#32).toNat) ∧
    SigOk pool' qm' qs' (qn + 1) ∧
    sPt + monoTotalWords pool' qm' (qn + 1) ≤ pt' := by
  intro pool' pt' qm' qs' _ql' _qh'
  have hpt32 : pt < 2 ^ 32 := by omega
  have hplen : pool'.length = poolL.length := by
    dsimp only [pool']; rw [List.length_append, List.length_take_of_le hpt_len, hout_len]; omega
  have hpre : ∀ idx < pt, pool'.getD idx 0#32 = poolL.getD idx 0#32 := by
    intro idx hidx
    dsimp only [pool']
    rw [list_getD_append_left _ _ 0#32 (by rw [List.length_take_of_le hpt_len]; exact hidx),
      list_getD_take poolL 0#32 hidx]
  have hpre_dst : ∀ idx < sPt, pool'.getD idx 0#32 = dstPool.getD idx 0#32 := fun idx hi => by
    rw [hpre idx (lt_of_lt_of_le hi hspt), hpref_dst idx hi]
  have hpt_take : (poolL.take pt).length = pt := List.length_take_of_le hpt_len
  have hcopied : ∀ r ≤ (out'.getD 0 0#32).toNat, pool'.getD (pt + r) 0#32 = out'.getD r 0#32 := by
    intro r _
    dsimp only [pool']
    rw [list_getD_append_right _ _ 0#32 (by rw [hpt_take]; omega), hpt_take,
      Nat.add_sub_cancel_left]
  have hlen0 : pool'.getD pt 0#32 = out'.getD 0 0#32 := by
    simpa only [Nat.add_zero] using hcopied 0 (Nat.zero_le _)
  have hpt_toNat : (BitVec.ofNat 32 pt).toNat = pt := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpt32]
  have hsym_new : symListAt pool' pt = symListAt out' 0 := by
    simp only [symListAt, hlen0, Nat.zero_add]
    apply List.map_congr_left
    intro r hr
    have hrlt := List.mem_range.mp hr
    rw [show pt + 1 + r = pt + (1 + r) by omega, hcopied (1 + r) (by omega)]
  have hslice_all : ∀ i < qn + 1,
      MonoSliceOk pool' (qm'.getD i 0#32).toNat pt' ∧
      (pool'.getD (qm'.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 := by
    intro i hi
    by_cases heq : i = qn
    · subst heq
      dsimp only [qm']
      have hlen_pt : (pool'.getD pt 0#32).toNat = (out'.getD 0 0#32).toNat :=
        congrArg BitVec.toNat hlen0
      rw [getD_set_eq qmL 0#32 _ hqn_qm, ite_eq_left rfl, hpt_toNat, hlen_pt]
      exact ⟨⟨by dsimp only [pt']; omega, by dsimp only [pt']; omega⟩, by omega⟩
    · have hi' : i < qn := by omega
      obtain ⟨hsl, h32⟩ := hqm_sl i hi'
      dsimp only [qm']
      rw [getD_set_eq qmL 0#32 _ hqn_qm, ite_eq_right heq]
      have hlen_keep : pool'.getD (qmL.getD i 0#32).toNat 0#32 =
          poolL.getD (qmL.getD i 0#32).toNat 0#32 := hpre _ hsl.1
      have hsl1 := hsl.1; have hsl2 := hsl.2
      dsimp only [pt']
      exact ⟨⟨by omega, by rw [hlen_keep]; omega⟩, by rw [hlen_keep]; exact h32⟩
  have hsorted_all : ∀ i < qn + 1, MonoSorted pool' (qm'.getD i 0#32).toNat := by
    intro i hi
    by_cases heq : i = qn
    · subst heq
      dsimp only [qm']
      rw [getD_set_eq qmL 0#32 _ hqn_qm, ite_eq_left rfl, hpt_toNat]
      simpa only [MonoSorted, hsym_new] using hout_sorted
    · have hi' : i < qn := by omega
      dsimp only [qm']
      rw [getD_set_eq qmL 0#32 _ hqn_qm, ite_eq_right heq]
      have heq_sym : symListAt pool' (qmL.getD i 0#32).toNat =
          symListAt poolL (qmL.getD i 0#32).toNat :=
        symListAt_congr_take (hqm_sl i hi').1 hpre
      simpa only [MonoSorted, heq_sym] using hqm_sorted i hi'
  have hsig_all : SigOk pool' qm' qs' (qn + 1) := by
    intro i hi x hx
    by_cases heq : i = qn
    · subst heq
      dsimp only [qm', qs']
      rw [getD_set_eq qmL 0#32 _ hqn_qm, ite_eq_left rfl, hpt_toNat, hsym_new] at hx
      rw [getD_set_eq qsL 0#64 _ hqn_qs, ite_eq_left rfl]
      exact hsig x hx
    · have hi' : i < qn := by omega
      dsimp only [qm', qs']
      rw [getD_set_eq qmL 0#32 _ hqn_qm, ite_eq_right heq] at hx
      rw [symListAt_congr_take (hqm_sl i hi').1 hpre] at hx
      rw [getD_set_eq qsL 0#64 _ hqn_qs, ite_eq_right heq]
      exact hqm_sig i hi' x hx
  have hwords_new : sPt + monoTotalWords pool' qm' (qn + 1) ≤ pt' := by
    have hwords_old : monoTotalWords pool' qmL qn = monoTotalWords poolL qmL qn :=
      monoTotalWords_congr_prefix (fun k hk => (hqm_sl k hk).1) hpre (fun _ _ => rfl)
    have hpref_qm : monoTotalWords pool' qm' qn = monoTotalWords pool' qmL qn :=
      monoTotalWords_congr_prefix (fun k hk => ⟨(hqm_sl k hk).1.1,
        by rw [hpre _ (hqm_sl k hk).1.1]; exact (hqm_sl k hk).1.2⟩) (fun _ _ => rfl)
        (fun k hk => by
          dsimp only [qm']; rw [getD_set_eq qmL 0#32 _ hqn_qm, ite_eq_right (by omega)])
    rw [monoTotalWords_succ, hpref_qm, hwords_old]
    dsimp only [qm']
    rw [getD_set_eq qmL 0#32 _ hqn_qm, ite_eq_left rfl, hpt_toNat, hlen0]
    dsimp only [pt']; omega
  exact ⟨hplen, hpre_dst, hpre, hcopied, hslice_all, hsorted_all, hsig_all, hwords_new⟩

theorem apply_emit_step_eval
    {nOut pt qn mOff mrOff : Nat}
    {curRp poolL out' qmL : List (BitVec 32)}
    {qlL qhL : List (BitVec 64)}
    {l h ccl cch rl rh : BitVec 64} {sym : BitVec 32} {σ : Nat → Bool}
    (hpt32 : pt < 2 ^ 32) (hpt_len : pt ≤ poolL.length)
    (hqn_qm : qn < qmL.length) (hqn_ql : qn < qlL.length) (hqn_qh : qn < qhL.length)
    (hout_syms : ∀ z, z ∈ symListAt out' 0 ↔
      (z ∈ symListAt poolL mOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt curRp mrOff)
    (hqm_sl : ∀ i < qn, MonoSliceOk poolL (qmL.getD i 0#32).toNat pt)
    (hcopied : ∀ r ≤ (out'.getD 0 0#32).toNat, (poolL.take pt ++ out').getD (pt + r) 0#32 =
      out'.getD r 0#32)
    (hc : coeff128 nOut l h = coeff128 nOut ccl cch * coeff128 nOut rl rh) :
    let pool' := poolL.take pt ++ out'
    let qm' := qmL.set qn (BitVec.ofNat 32 pt)
    let ql' := qlL.set qn l
    let qh' := qhL.set qn h
    polyEval nOut σ pool' qm' ql' qh' (qn + 1) =
      polyEval nOut σ poolL qmL qlL qhL qn +
        (if monoValL σ ((symListAt poolL mOff).filter (fun z => decide (z ≠ sym.toNat)))
         then coeff128 nOut ccl cch else 0#nOut) *
        (if monoValL σ (symListAt curRp mrOff) then coeff128 nOut rl rh else 0#nOut) := by
  intro pool' qm' ql' qh'
  have hpre : ∀ idx < pt, pool'.getD idx 0#32 = poolL.getD idx 0#32 := fun idx hidx => by
    dsimp only [pool']
    rw [list_getD_append_left _ _ 0#32 (by rw [List.length_take_of_le hpt_len]; exact hidx),
      list_getD_take poolL 0#32 hidx]
  have hlen0 : pool'.getD pt 0#32 = out'.getD 0 0#32 := by
    simpa only [Nat.add_zero] using hcopied 0 (Nat.zero_le _)
  have hpt_toNat : (BitVec.ofNat 32 pt).toNat = pt := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpt32]
  have hsym_new : symListAt pool' pt = symListAt out' 0 := by
    simp only [symListAt, hlen0, Nat.zero_add]
    apply List.map_congr_left
    intro r hr
    have hrlt := List.mem_range.mp hr
    rw [show pt + 1 + r = pt + (1 + r) by omega, hcopied (1 + r) (by omega)]
  have hpref_eval : polyEval nOut σ pool' qm' ql' qh' qn =
      polyEval nOut σ poolL qmL qlL qhL qn := by
    simp only [polyEval]
    apply polyEval_range_congr
    intro k hk
    have hlo0 : 0 + k = k := Nat.zero_add k
    have hk' : k < qn := by omega
    have hkne : k ≠ qn := by omega
    dsimp only [termEval, qm', ql', qh']
    rw [hlo0, getD_set_eq qmL 0#32 _ hqn_qm, getD_set_eq qlL 0#64 _ hqn_ql,
      getD_set_eq qhL 0#64 _ hqn_qh, ite_eq_right hkne, ite_eq_right hkne, ite_eq_right hkne,
      symListAt_congr_take (hqm_sl k hk') hpre]
  rw [polyEval_succ, hpref_eval]
  congr 1
  dsimp only [termEval, qm', ql', qh']
  rw [getD_set_eq qmL 0#32 _ hqn_qm, ite_eq_left rfl, hpt_toNat, hsym_new,
    getD_set_eq qlL 0#64 _ hqn_ql, ite_eq_left rfl,
    getD_set_eq qhL 0#64 _ hqn_qh, ite_eq_left rfl, hc]
  exact termEval_subst_prod hout_syms

theorem apply_van_step_true {nNets sym : Nat}
    {partnerArr curRp curRm vqOff vq dstPool : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {Valid : (Nat → Bool) → Prop} {r mOff qFin : Nat} {qq : BitVec 32}
    (hPart : ∀ σ, Valid σ → PartnerRep σ nNets partnerArr)
    (hvqRow : VqRowOk nNets sym partnerArr curRp curRm vqOff vq vqSkip Valid r qFin)
    (hsk0 : vqSkip.getD r 0#8 = 0#8)
    (hq0_qq : (vqOff.getD r 0#32).toNat ≤ qq.toNat)
    (hqq_q1 : qq.toNat < (vqOff.getD (r + 1) 0#32).toNat)
    (hmem : ∃ idx, 1 ≤ idx ∧ idx ≤ (dstPool.getD mOff 0#32).toNat ∧
      dstPool.getD (mOff + idx) 0#32 = vq.getD qq.toNat 0#32) :
    ∀ σ, Valid σ →
      (monoValL σ ((symListAt dstPool mOff).filter (fun z => decide (z ≠ sym))) &&
       monoValL σ (symListAt curRp (curRm.getD r 0#32).toNat)) = false := by
  intro σ hV
  obtain ⟨w, hw_mem, hw_even, hw_lt, hp_ne, hvq_eq, hvq_ne⟩ :=
    (hvqRow.2 hsk0).2.2 qq.toNat hq0_qq hqq_q1
  obtain ⟨idx, h1, h2, heq⟩ := hmem
  have hvq_mem : (vq.getD qq.toNat 0#32).toNat ∈ symListAt dstPool mOff := by
    rw [mem_symListAt_iff]
    exact ⟨idx, h1, h2, congrArg BitVec.toNat heq⟩
  exact monoValL_partner_conflict (hPart σ hV) hw_mem hw_even hw_lt hp_ne hvq_eq hvq_ne hvq_mem

theorem apply_van_zero_prod {nOut : Nat} {σ : Nat → Bool}
    {mSyms mrSyms : List Nat} {sym : Nat} {ccl cch rl rh : BitVec 64}
    (hvan : (monoValL σ (mSyms.filter (fun z => decide (z ≠ sym))) &&
      monoValL σ mrSyms) = false) :
    (if monoValL σ (mSyms.filter (fun z => decide (z ≠ sym)))
     then coeff128 nOut ccl cch else 0#nOut) *
      (if monoValL σ mrSyms then coeff128 nOut rl rh else 0#nOut) = 0#nOut := by
  by_cases h1 : monoValL σ (mSyms.filter (fun z => decide (z ≠ sym))) = true
  · rw [h1] at hvan
    have h2 : monoValL σ mrSyms = false := by cases h : monoValL σ mrSyms <;> simp_all
    simp [h2]
  · have h1f : monoValL σ (mSyms.filter (fun z => decide (z ≠ sym))) = false := by
      cases h : monoValL σ (mSyms.filter (fun z => decide (z ≠ sym))) <;> simp_all
    have h1f' : monoValL σ (mSyms.filter (fun z => !decide (z = sym))) = false := by
      simpa only [ne_eq, decide_not] using h1f
    simp [h1f']

end

/-! ## 2. Loop 4 Invariants, Context Bundle & Exit Handler -/

@[expose] public section

/-- Constant structural invariants and pre-Loop-4 guarantees for `ar_apply`. -/
structure ApplyLoopCtx (cx : BitVec 64) (sym : BitVec 32) (s0 s : ArCtxState)
    (tm0 tm1 pool0 pool1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
    (tm0_1 tm1_1 pool0_1 pool1_1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
    (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
    (partnerArr curRm : List (BitVec 32)) (curRl curRh : List (BitVec 64))
    (curRp : List (BitVec 32)) (Valid : (Nat → Bool) → Prop) (R rest4 : Mem 64 → Prop)
    (nb : BitVec 32) (slB slR : BitVec 64) (qFin : Nat) : Prop where
  hs1 : s = { s0 with pc := s.pc, ptop := s.ptop }
  hpc : s.pc.toNat < 2
  htc : s.tc.toNat < 2
  htn : s0.tn.toNat ≤ s0.tcap.toNat
  htcap30 : s0.tcap.toNat < 2 ^ 30
  hqcap32 : s0.qcap.toNat + 16 < 2 ^ 32
  hpcap32 : s0.pcap.toNat < 2 ^ 32
  hnb_pos : 0 < nb.toNat
  hnb_tn : nb.toNat ≤ s0.tn.toNat
  hnb_bx : nb.toNat ≤ bx.length
  hinc : strictIncBelow bx nb.toNat s0.tn.toNat
  hnb_nr_q : nb.toNat * s0.cur_nr.toNat ≤ s0.qcap.toNat
  hnb_nr_t : (s0.tn.toNat - nb.toNat) + nb.toNat * s0.cur_nr.toNat ≤ s0.tcap.toNat
  hslR : slR.toNat = rSymLenSum curRp curRm s0.cur_nr.toNat
  hslB : slB.toNat = bxSymLenSum (if s.pc.toNat = 0 then pool0_1 else pool1_1)
    (if s.tc.toNat = 0 then tm0_1 else tm1_1) bx nb.toNat
  hpt_cap : s.ptop.toNat + (s0.cur_nr.toNat * slB.toNat + nb.toNat * slR.toNat) ≤ s0.pcap.toNat
  htm0_len : s0.tcap.toNat ≤ tm0_1.length
  htm1_len : s0.tcap.toNat ≤ tm1_1.length
  hts0_len : s0.tcap.toNat ≤ ts0.length
  htl0_len : s0.tcap.toNat ≤ tl0.length
  hth0_len : s0.tcap.toNat ≤ th0.length
  hts1_len : s0.tcap.toNat ≤ ts1.length
  htl1_len : s0.tcap.toNat ≤ tl1.length
  hth1_len : s0.tcap.toNat ≤ th1.length
  hp0_len : s0.pcap.toNat ≤ pool0_1.length
  hp1_len : s0.pcap.toNat ≤ pool1_1.length
  hqm_len : s0.qcap.toNat ≤ qm.length
  hqs_len : s0.qcap.toNat ≤ qs.length
  hql_len : s0.qcap.toNat ≤ ql.length
  hqh_len : s0.qcap.toNat ≤ qh.length
  hix_len : s0.qcap.toNat ≤ ix.length
  hix2_len : s0.qcap.toNat ≤ ix2.length
  hvqOff_len : s0.qcap.toNat + 1 ≤ vqOff.length
  hvq_len : s0.pcap.toNat ≤ vq.length
  hvqSkip_len : s0.qcap.toNat ≤ vqSkip.length
  hqFin_le : qFin ≤ s0.pcap.toNat
  hcurNr_rm : s0.cur_nr.toNat ≤ curRm.length
  hcurNr_rl : s0.cur_nr.toNat ≤ curRl.length
  hcurNr_rh : s0.cur_nr.toNat ≤ curRh.length
  hMasks : MasksOk s0.modW s0.mlo s0.mhi
  hPart : ∀ σ, Valid σ → PartnerRep σ s0.n_nets.toNat partnerArr
  hCurR : ∀ σ, Valid σ →
    CurRRep s0.modW σ s0.cur_nr.toNat sym.toNat curRm curRl curRh curRp
  hcurSl : ∀ r < s0.cur_nr.toNat, MonoSliceOk curRp (curRm.getD r 0#32).toNat curRp.length
  hcurSo : ∀ r < s0.cur_nr.toNat, MonoSorted curRp (curRm.getD r 0#32).toNat
  hcurMr32 : ∀ r < s0.cur_nr.toNat, (curRp.getD (curRm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32
  hVqOk : ∀ r < s0.cur_nr.toNat,
    VqRowOk s0.n_nets.toNat sym.toNat partnerArr curRp curRm vqOff vq vqSkip Valid r qFin
  hSl1 : ∀ i < s0.tn.toNat,
    MonoSliceOk (if s.pc.toNat = 0 then pool0_1 else pool1_1)
      ((if s.tc.toNat = 0 then tm0_1 else tm1_1).getD i 0#32).toNat s.ptop.toNat ∧
    ((if s.pc.toNat = 0 then pool0_1 else pool1_1).getD
      ((if s.tc.toNat = 0 then tm0_1 else tm1_1).getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32
  hSo1 : ∀ i < s0.tn.toNat,
    MonoSorted (if s.pc.toNat = 0 then pool0_1 else pool1_1)
      ((if s.tc.toNat = 0 then tm0_1 else tm1_1).getD i 0#32).toNat
  hSi1 : SigOk (if s.pc.toNat = 0 then pool0_1 else pool1_1)
    (if s.tc.toNat = 0 then tm0_1 else tm1_1) (if s.tc.toNat = 0 then ts0 else ts1) s0.tn.toNat
  hTot1 : monoTotalWords (if s.pc.toNat = 0 then pool0_1 else pool1_1)
    (if s.tc.toNat = 0 then tm0_1 else tm1_1) s0.tn.toNat ≤ s.ptop.toNat
  hbxMem : ∀ b < nb.toNat, sym.toNat ∈ symListAt (if s.pc.toNat = 0 then pool0_1 else pool1_1)
    ((if s.tc.toNat = 0 then tm0_1 else tm1_1).getD (bx.getD b 0#32).toNat 0#32).toNat
  hSym1 : ∀ i < s0.tn.toNat,
    symListAt (if s.pc.toNat = 0 then pool0_1 else pool1_1)
      ((if s.tc.toNat = 0 then tm0_1 else tm1_1).getD i 0#32).toNat =
    symListAt (if s0.pc.toNat = 0 then pool0 else pool1)
      ((if s0.tc.toNat = 0 then tm0 else tm1).getD i 0#32).toNat
  htm0_eq : tm0_1.length = tm0.length
  htm1_eq : tm1_1.length = tm1.length
  hp0_eq : pool0_1.length = pool0.length
  hp1_eq : pool1_1.length = pool1.length
  htqPack : ∀ (s' : ArCtxState) (pool' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64)),
    s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl → s'.th = s.th → s'.pool = s.pool →
    s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh →
    s'.ix = s.ix → s'.ix2 = s.ix2 → s'.bx = s.bx → s'.vq_off = s.vq_off →
    s'.vq = s.vq → s'.vq_skip = s.vq_skip →
    pool'.length = (if s.pc.toNat = 0 then pool0_1 else pool1_1).length →
    qm'.length = qm.length → qs'.length = qs.length →
    ql'.length = ql.length → qh'.length = qh.length →
    (tMem s' tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1
      (if s.pc.toNat = 0 then pool' else pool0_1)
      (if s.pc.toNat = 0 then pool1_1 else pool') ⋆
     qMem s' qm' qs' ql' qh' ix ix2 bx vqOff vq vqSkip =
     (array (t := i32) (s.pool.getD s.pc.toNat 0#64) pool' ⋆
      array (t := i32) s.qm qm' ⋆ array64 s.qs qs' ⋆
      array64 s.ql ql' ⋆ array64 s.qh qh' ⋆ rest4))

def ApplyInnerInv (cx : BitVec 64) (sym : BitVec 32) (s : ArCtxState)
    (pool0 pool1 : List (BitVec 32)) (qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
    (curRm : List (BitVec 32)) (curRl curRh : List (BitVec 64))
    (curRp : List (BitVec 32)) (Valid : (Nat → Bool) → Prop) (Rloop4 : Mem 64 → Prop)
    (qnBase ptBase mOff : Nat) (cl ch : BitVec 64)
    (poolBase qmBase : List (BitVec 32)) (qlBase qhBase : List (BitVec 64))
    (qn : BitVec 32) (pt : BitVec 64) (r : BitVec 32) (m : Mem 64) : Prop :=
  let dstPool := if s.pc.toNat = 0 then pool0 else pool1
  let mLen := (dstPool.getD mOff 0#32).toNat
  r.toNat ≤ s.cur_nr.toNat ∧
  qnBase ≤ qn.toNat ∧ qn.toNat ≤ qnBase + r.toNat ∧
  ptBase ≤ pt.toNat ∧
  pt.toNat ≤ ptBase + r.toNat * mLen + rSymLenSum curRp curRm r.toNat ∧
  ∃ (poolL qmL : List (BitVec 32)) (qsL qlL qhL : List (BitVec 64)),
    poolL.length = dstPool.length ∧ qmL.length = qm.length ∧
    qsL.length = qs.length ∧ qlL.length = ql.length ∧ qhL.length = qh.length ∧
    (∀ idx < s.ptop.toNat, poolL.getD idx 0#32 = dstPool.getD idx 0#32) ∧
    (∀ i < qn.toNat,
      MonoSliceOk poolL (qmL.getD i 0#32).toNat pt.toNat ∧
      (poolL.getD (qmL.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
    (∀ i < qn.toNat, MonoSorted poolL (qmL.getD i 0#32).toNat) ∧
    SigOk poolL qmL qsL qn.toNat ∧
    s.ptop.toNat + monoTotalWords poolL qmL qn.toNat ≤ pt.toNat ∧
    (∀ bd : Nat, (∀ x ∈ symListAt dstPool mOff, x / 2 < bd) →
      SymsBound curRp curRm s.cur_nr.toNat bd →
      (∀ i < qnBase, ∀ x ∈ symListAt poolBase (qmBase.getD i 0#32).toNat, x / 2 < bd) →
      SymsBound poolL qmL qn.toNat bd) ∧
    (∀ σ, Valid σ →
      polyEval s.modW σ poolL qmL qlL qhL qn.toNat =
        polyEval s.modW σ poolBase qmBase qlBase qhBase qnBase +
          (List.range r.toNat).foldl (fun acc r0 =>
            acc + (if monoValL σ ((symListAt dstPool mOff).filter
                (fun z => decide (z ≠ sym.toNat)))
              then coeff128 s.modW cl ch else 0#(s.modW)) *
              termEval s.modW σ curRp curRm curRl curRh r0) 0#(s.modW)) ∧
    (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolL ⋆
      array (t := i32) s.qm qmL ⋆ array64 s.qs qsL ⋆
      array64 s.ql qlL ⋆ array64 s.qh qhL ⋆ Rloop4) m

def ApplyOuterInv (cx : BitVec 64) (s : ArCtxState)
    (tm0 tm1 pool0 pool1 : List (BitVec 32)) (tl0 th0 tl1 th1 : List (BitVec 64))
    (qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
    (bx curRm curRp : List (BitVec 32)) (nb : BitVec 32)
    (Valid : (Nat → Bool) → Prop) (Rloop4 : Mem 64 → Prop)
    (qn : BitVec 32) (pt : BitVec 64) (b : BitVec 32) (m : Mem 64) : Prop :=
  let dstPool := if s.pc.toNat = 0 then pool0 else pool1
  let dstTm := if s.tc.toNat = 0 then tm0 else tm1
  let srcTl := if s.tc.toNat = 0 then tl0 else tl1
  let srcTh := if s.tc.toNat = 0 then th0 else th1
  b.toNat ≤ nb.toNat ∧
  qn.toNat ≤ b.toNat * s.cur_nr.toNat ∧
  s.ptop.toNat ≤ pt.toNat ∧
  pt.toNat ≤ s.ptop.toNat +
    (b.toNat * rSymLenSum curRp curRm s.cur_nr.toNat +
      s.cur_nr.toNat * bxSymLenSum dstPool dstTm bx b.toNat) ∧
  ∃ (poolL qmL : List (BitVec 32)) (qsL qlL qhL : List (BitVec 64)),
    poolL.length = dstPool.length ∧ qmL.length = qm.length ∧
    qsL.length = qs.length ∧ qlL.length = ql.length ∧ qhL.length = qh.length ∧
    (∀ idx < s.ptop.toNat, poolL.getD idx 0#32 = dstPool.getD idx 0#32) ∧
    (∀ i < qn.toNat,
      MonoSliceOk poolL (qmL.getD i 0#32).toNat pt.toNat ∧
      (poolL.getD (qmL.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
    (∀ i < qn.toNat, MonoSorted poolL (qmL.getD i 0#32).toNat) ∧
    SigOk poolL qmL qsL qn.toNat ∧
    s.ptop.toNat + monoTotalWords poolL qmL qn.toNat ≤ pt.toNat ∧
    (∀ bd : Nat, SymsBound dstPool dstTm s.tn.toNat bd →
      SymsBound curRp curRm s.cur_nr.toNat bd → SymsBound poolL qmL qn.toNat bd) ∧
    (∀ σ, Valid σ →
      polyEval s.modW σ poolL qmL qlL qhL qn.toNat =
        bxTermSum s.modW σ dstPool dstTm srcTl srcTh bx b.toNat) ∧
    (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolL ⋆
      array (t := i32) s.qm qmL ⋆ array64 s.qs qsL ⋆
      array64 s.ql qlL ⋆ array64 s.qh qhL ⋆ Rloop4) m

end

public section

theorem apply_inner_row_done {cx : BitVec 64} {sym : BitVec 32} {s : ArCtxState}
    {tm0 tm1 pool0 pool1 : List (BitVec 32)} {tl0 th0 tl1 th1 : List (BitVec 64)}
    {qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {bx curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)}
    {curRp : List (BitVec 32)} {nb b qn : BitVec 32} {pt : BitVec 64}
    {Valid : (Nat → Bool) → Prop} {Rloop4 : Mem 64 → Prop}
    {qnBase ptBase mOff : Nat} {cl ch : BitVec 64}
    {poolBase qmBase : List (BitVec 32)} {qlBase qhBase : List (BitVec 64)} {mL : Mem 64}
    (hb_lt : b.toNat < nb.toNat) (hspt_base : s.ptop.toNat ≤ ptBase)
    (hOuterQn : qnBase ≤ b.toNat * s.cur_nr.toNat)
    (hOuterPt : ptBase ≤ s.ptop.toNat +
      (b.toNat * rSymLenSum curRp curRm s.cur_nr.toNat +
        s.cur_nr.toNat * bxSymLenSum (if s.pc.toNat = 0 then pool0 else pool1)
          (if s.tc.toNat = 0 then tm0 else tm1) bx b.toNat))
    (hOuterEval : ∀ σ, Valid σ →
      polyEval s.modW σ poolBase qmBase qlBase qhBase qnBase =
        bxTermSum s.modW σ (if s.pc.toNat = 0 then pool0 else pool1)
          (if s.tc.toNat = 0 then tm0 else tm1) (if s.tc.toNat = 0 then tl0 else tl1)
          (if s.tc.toNat = 0 then th0 else th1) bx b.toNat)
    (hmOff : mOff = ((if s.tc.toNat = 0 then tm0 else tm1).getD
      (bx.getD b.toNat 0#32).toNat 0#32).toNat)
    (hcl : cl = (if s.tc.toNat = 0 then tl0 else tl1).getD (bx.getD b.toNat 0#32).toNat 0#64)
    (hch : ch = (if s.tc.toNat = 0 then th0 else th1).getD (bx.getD b.toNat 0#32).toNat 0#64)
    (hbxMem : sym.toNat ∈ symListAt (if s.pc.toNat = 0 then pool0 else pool1) mOff)
    (hbx_tn : (bx.getD b.toNat 0#32).toNat < s.tn.toNat)
    (hOuterSy : ∀ bd : Nat,
      SymsBound (if s.pc.toNat = 0 then pool0 else pool1)
        (if s.tc.toNat = 0 then tm0 else tm1) s.tn.toNat bd →
      SymsBound curRp curRm s.cur_nr.toNat bd →
      ∀ i < qnBase, ∀ x ∈ symListAt poolBase (qmBase.getD i 0#32).toNat, x / 2 < bd)
    (hCurR : ∀ σ, Valid σ →
      CurRRep s.modW σ s.cur_nr.toNat sym.toNat curRm curRl curRh curRp)
    (hInner : ApplyInnerInv cx sym s pool0 pool1 qm qs ql qh curRm curRl curRh curRp
      Valid Rloop4 qnBase ptBase mOff cl ch poolBase qmBase qlBase qhBase qn pt s.cur_nr mL) :
    ApplyOuterInv cx s tm0 tm1 pool0 pool1 tl0 th0 tl1 th1 qm qs ql qh bx curRm curRp nb
      Valid Rloop4 qn pt (b + 1#32) mL := by
  obtain ⟨_, _, hqn_le, hpt_ge, hpt_le, poolL, qmL, qsL, qlL, qhL,
    hl1, hl2, hl3, hl4, hl5, hpre, hSl, hSo, hSi, hW, hSy, hEv, hm⟩ := hInner
  have hbp1 : (b + 1#32).toNat = b.toNat + 1 := apply_bv32_add1_lt hb_lt nb.isLt
  refine ⟨by rw [hbp1]; exact hb_lt, ?_, by omega, ?_, poolL, qmL, qsL, qlL, qhL,
    hl1, hl2, hl3, hl4, hl5, hpre, hSl, hSo, hSi, hW, ?_, ?_, hm⟩
  · rw [hbp1, Nat.succ_mul]; omega
  · rw [hbp1]
    have hbd := apply_row_budget_le (pool := if s.pc.toNat = 0 then pool0 else pool1)
      (tm := if s.tc.toNat = 0 then tm0 else tm1) (rp := curRp) (rm := curRm) (bx := bx)
      (nR := s.cur_nr.toNat) (b := b.toNat)
    dsimp only at hbd; rw [← hmOff] at hbd; omega
  · intro bd hSbT hSbR
    exact hSy bd (fun x hx => hSbT (bx.getD b.toNat 0#32).toNat hbx_tn x (hmOff ▸ hx))
      hSbR (hOuterSy bd hSbT hSbR)
  · intro σ hV
    rw [hbp1, bxTermSum_succ, ← hOuterEval σ hV, hEv σ hV]
    congr 1
    rw [apply_row_sum_eq hbxMem (hCurR σ hV).2.2.2.2]
    simp only [termEval, ← hmOff, hcl, hch]

theorem apply_inner_skip_step {cx : BitVec 64} {sym : BitVec 32} {s : ArCtxState}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)}
    {curRp : List (BitVec 32)} {r qn : BitVec 32} {pt : BitVec 64}
    {Valid : (Nat → Bool) → Prop} {Rloop4 : Mem 64 → Prop}
    {qnBase ptBase mOff : Nat} {cl ch : BitVec 64}
    {poolBase qmBase : List (BitVec 32)} {qlBase qhBase : List (BitVec 64)} {mL : Mem 64}
    (hr_lt : r.toNat < s.cur_nr.toNat)
    (hZero : ∀ σ, Valid σ →
      (if monoValL σ ((symListAt (if s.pc.toNat = 0 then pool0 else pool1) mOff).filter
          (fun z => decide (z ≠ sym.toNat)))
       then coeff128 s.modW cl ch else 0#(s.modW)) *
        termEval s.modW σ curRp curRm curRl curRh r.toNat = 0#(s.modW))
    (hInner : ApplyInnerInv cx sym s pool0 pool1 qm qs ql qh curRm curRl curRh curRp
      Valid Rloop4 qnBase ptBase mOff cl ch poolBase qmBase qlBase qhBase qn pt r mL) :
    ApplyInnerInv cx sym s pool0 pool1 qm qs ql qh curRm curRl curRh curRp
      Valid Rloop4 qnBase ptBase mOff cl ch poolBase qmBase qlBase qhBase qn pt (r + 1#32) mL := by
  obtain ⟨_, hqn_ge, hqn_le, hpt_ge, hpt_le, poolL, qmL, qsL, qlL, qhL,
    hl1, hl2, hl3, hl4, hl5, hpre, hSl, hSo, hSi, hW, hSy, hEv, hm⟩ := hInner
  have hrp1 : (r + 1#32).toNat = r.toNat + 1 := apply_bv32_add1_lt hr_lt s.cur_nr.isLt
  refine ⟨by omega, hqn_ge, by omega, hpt_ge, ?_, poolL, qmL, qsL, qlL, qhL,
    hl1, hl2, hl3, hl4, hl5, hpre, hSl, hSo, hSi, hW, hSy, ?_, hm⟩
  · rw [hrp1, rSymLenSum_succ, Nat.succ_mul]; omega
  · intro σ hV
    rw [hrp1, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hZero σ hV,
      BitVec.add_zero]
    exact hEv σ hV

theorem apply_outer_exit_wp (Γ : T.Env)
    (hMerge : ∀ xs m Q X, arMergeProductsSpec xs m Q X →
      Γ "ar_merge_products" [i64, i32] [] xs m Q X)
    {cx : BitVec 64} {sym : BitVec 32} {s0 s : ArCtxState}
    {tm0 tm1 pool0 pool1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {tm0_1 tm1_1 pool0_1 pool1_1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {partnerArr curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)}
    {curRp : List (BitVec 32)} {Valid : (Nat → Bool) → Prop} {R rest4 : Mem 64 → Prop}
    {nb qn : BitVec 32} {pt slB slR : BitVec 64} {qFin : Nat}
    {poolL qmL : List (BitVec 32)} {qsL qlL qhL : List (BitVec 64)} {mA : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hCtx : ApplyLoopCtx cx sym s0 s tm0 tm1 pool0 pool1 ts0 tl0 th0 ts1 tl1 th1
      tm0_1 tm1_1 pool0_1 pool1_1 qm qs ql qh ix ix2 bx vqOff vq vqSkip
      partnerArr curRm curRl curRh curRp Valid R rest4 nb slB slR qFin)
    (hqn_le : qn.toNat ≤ nb.toNat * s.cur_nr.toNat)
    (hpt_ge : s.ptop.toNat ≤ pt.toNat)
    (hpt_le : pt.toNat ≤ s.ptop.toNat +
      (nb.toNat * rSymLenSum curRp curRm s.cur_nr.toNat +
        s.cur_nr.toNat * bxSymLenSum (if s.pc.toNat = 0 then pool0_1 else pool1_1)
          (if s.tc.toNat = 0 then tm0_1 else tm1_1) bx nb.toNat))
    (hl1 : poolL.length = (if s.pc.toNat = 0 then pool0_1 else pool1_1).length)
    (hl2 : qmL.length = qm.length) (hl3 : qsL.length = qs.length)
    (hl4 : qlL.length = ql.length) (hl5 : qhL.length = qh.length)
    (hpre : ∀ idx < s.ptop.toNat,
      poolL.getD idx 0#32 = (if s.pc.toNat = 0 then pool0_1 else pool1_1).getD idx 0#32)
    (hSlq : ∀ i < qn.toNat,
      MonoSliceOk poolL (qmL.getD i 0#32).toNat pt.toNat ∧
      (poolL.getD (qmL.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSoq : ∀ i < qn.toNat, MonoSorted poolL (qmL.getD i 0#32).toNat)
    (hSiq : SigOk poolL qmL qsL qn.toNat)
    (hWq : s.ptop.toNat + monoTotalWords poolL qmL qn.toNat ≤ pt.toNat)
    (hSyq : ∀ bd : Nat,
      SymsBound (if s.pc.toNat = 0 then pool0_1 else pool1_1)
        (if s.tc.toNat = 0 then tm0_1 else tm1_1) s.tn.toNat bd →
      SymsBound curRp curRm s.cur_nr.toNat bd → SymsBound poolL qmL qn.toNat bd)
    (hEvq : ∀ σ, Valid σ →
      polyEval s.modW σ poolL qmL qlL qhL qn.toNat =
        bxTermSum s.modW σ (if s.pc.toNat = 0 then pool0_1 else pool1_1)
          (if s.tc.toNat = 0 then tm0_1 else tm1_1) (if s.tc.toNat = 0 then tl0 else tl1)
          (if s.tc.toNat = 0 then th0 else th1) bx nb.toNat)
    (hmA : (arCtxMem cx { s with ptop := pt, qn := qn } ⋆
      array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolL ⋆
      array (t := i32) s.qm qmL ⋆ array64 s.qs qsL ⋆
      array64 s.ql qlL ⋆ array64 s.qh qhL ⋆
      (array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
       array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
       rest4 ⋆ R)) mA)
    (hOk : ∀ (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
        (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
        (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
        (ix' ix2' bx' vqOff' vq' : List (BitVec 32)) (vqSkip' : List (BitVec 8))
        (m' : Mem 64),
      let srcPool0 := if s0.pc.toNat = 0 then pool0 else pool1
      let srcTm0 := if s0.tc.toNat = 0 then tm0 else tm1
      let srcTl0 := if s0.tc.toNat = 0 then tl0 else tl1
      let srcTh0 := if s0.tc.toNat = 0 then th0 else th1
      let dstPool := if s'.pc.toNat = 0 then pool0' else pool1'
      let dstTm := if s'.tc.toNat = 0 then tm0' else tm1'
      let dstTs := if s'.tc.toNat = 0 then ts0' else ts1'
      let dstTl := if s'.tc.toNat = 0 then tl0' else tl1'
      let dstTh := if s'.tc.toNat = 0 then th0' else th1'
      s'.pc.toNat < 2 → s'.tc.toNat < 2 →
      s'.ptop.toNat ≤ s0.pcap.toNat → s'.tn.toNat ≤ s0.tcap.toNat →
      s' = { s0 with
        tc := s'.tc, tn := s'.tn, pc := s'.pc, ptop := s'.ptop,
        qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
      ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      qm'.length = qm.length → qs'.length = qs.length →
      ql'.length = ql.length → qh'.length = qh.length →
      ((s'.ix = s0.ix ∧ s'.ix2 = s0.ix2 ∧
        ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s0.ix2 ∧ s'.ix2 = s0.ix ∧
        ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      bx'.length = bx.length → vqOff'.length = vqOff.length →
      vq'.length = vq.length → vqSkip'.length = vqSkip.length →
      (∀ i < s'.tn.toNat,
        MonoSliceOk dstPool (dstTm.getD i 0#32).toNat s'.ptop.toNat ∧
        (dstPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ i < s'.tn.toNat, MonoSorted dstPool (dstTm.getD i 0#32).toNat) →
      SigOk dstPool dstTm dstTs s'.tn.toNat →
      monoTotalWords dstPool dstTm s'.tn.toNat ≤ s'.ptop.toNat →
      (∀ bd : Nat, SymsBound srcPool0 srcTm0 s0.tn.toNat bd →
        SymsBound curRp curRm s0.cur_nr.toNat bd →
        SymsBound dstPool dstTm s'.tn.toNat bd) →
      (∀ σ, Valid σ →
        polyEval s0.modW σ dstPool dstTm dstTl dstTh s'.tn.toNat =
          polyEval s0.modW σ srcPool0 srcTm0 srcTl0 srcTh0 s0.tn.toNat) →
      (arCtxMem cx s' ⋆ array (t := i32) s'.partner partnerArr ⋆
        array (t := i32) s'.cur_rm curRm ⋆ array64 s'.cur_rl curRl ⋆
        array64 s'.cur_rh curRh ⋆ array (t := i32) s'.cur_rp curRp ⋆
        tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
        qMem s' qm' qs' ql' qh' ix' ix2' bx' vqOff' vq' vqSkip' ⋆ R) m' →
      Q (true, ⟨⟩) m') :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := []) "ar_merge_products"
      (Arg.var cx, Arg.var nb, ())
      (fun _ => (@Expr.ret Val Cont [Ty.bool] (Arg.imm true, ())))) mA := by
  let sA : ArCtxState := { s with ptop := pt, qn := qn }
  have hs1 := hCtx.hs1
  have hs_tc : s.tc = s0.tc := by conv => lhs; rw [hs1]
  have hs_tn : s.tn = s0.tn := by conv => lhs; rw [hs1]
  have hs_tcap : s.tcap = s0.tcap := by conv => lhs; rw [hs1]
  have hs_qcap : s.qcap = s0.qcap := by conv => lhs; rw [hs1]
  have hs_pcap : s.pcap = s0.pcap := by conv => lhs; rw [hs1]
  have hs_nout : s.modW = s0.modW := by rw [hs1]; rfl
  have hs_nr : s.cur_nr = s0.cur_nr := by conv => lhs; rw [hs1]
  have hs_mlo : s.mlo = s0.mlo := by conv => lhs; rw [hs1]
  have hs_mhi : s.mhi = s0.mhi := by conv => lhs; rw [hs1]
  have hs_ix : s.ix = s0.ix := by conv => lhs; rw [hs1]
  have hs_ix2 : s.ix2 = s0.ix2 := by conv => lhs; rw [hs1]
  have hsA_pc : sA.pc.toNat = s.pc.toNat := rfl
  have hsA_tc : sA.tc.toNat = s.tc.toNat := rfl
  have hsA_tn : sA.tn.toNat = s0.tn.toNat := by dsimp only [sA]; rw [hs_tn]
  have hsA_tcap : sA.tcap.toNat = s0.tcap.toNat := by dsimp only [sA]; rw [hs_tcap]
  have hsA_qcap : sA.qcap.toNat = s0.qcap.toNat := by dsimp only [sA]; rw [hs_qcap]
  have hsA_pcap : sA.pcap.toNat = s0.pcap.toNat := by dsimp only [sA]; rw [hs_pcap]
  have hsA_nout : sA.modW = s0.modW := by rw [← hs_nout]; rfl
  have hsA_pt : sA.ptop.toNat = pt.toNat := rfl
  have hsA_qn : sA.qn.toNat = qn.toNat := rfl
  let pool0A := if s.pc.toNat = 0 then poolL else pool0_1
  let pool1A := if s.pc.toNat = 0 then pool1_1 else poolL
  have hpoolA_sel : (if sA.pc.toNat = 0 then pool0A else pool1A) = poolL := by
    rw [hsA_pc]; dsimp only [pool0A, pool1A]
    by_cases hpc0 : s.pc.toNat = 0 <;> simp [hpc0]
  have hpool0A_len : pool0A.length = pool0_1.length := by
    dsimp only [pool0A]
    by_cases hpc0 : s.pc.toNat = 0 <;> simp [hpc0, hl1]
  have hpool1A_len : pool1A.length = pool1_1.length := by
    dsimp only [pool1A]
    by_cases hpc0 : s.pc.toNat = 0 <;> simp [hpc0, hl1]
  let dstTm1 := if s.tc.toNat = 0 then tm0_1 else tm1_1
  let dstTs1 := if s.tc.toNat = 0 then ts0 else ts1
  let dstTl1 := if s.tc.toNat = 0 then tl0 else tl1
  let dstTh1 := if s.tc.toNat = 0 then th0 else th1
  have hm_pack : (arCtxMem cx sA ⋆ tMem sA tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0A pool1A ⋆
      qMem sA qmL qsL qlL qhL ix ix2 bx vqOff vq vqSkip ⋆
      (array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
       array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
       R)) mA := by
    have hmA' := sep_cast hmA (by ac_rfl :
      (arCtxMem cx sA ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolL ⋆
        array (t := i32) s.qm qmL ⋆ array64 s.qs qsL ⋆ array64 s.ql qlL ⋆ array64 s.qh qhL ⋆
        (array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
         array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
         rest4 ⋆ R)) =
      (arCtxMem cx sA ⋆
        (array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolL ⋆
          array (t := i32) s.qm qmL ⋆ array64 s.qs qsL ⋆ array64 s.ql qlL ⋆ array64 s.qh qhL ⋆
          rest4) ⋆
        (array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
         array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
         R)))
    rw [← hCtx.htqPack sA poolL qmL qsL qlL qhL
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hl1 hl2 hl3 hl4 hl5] at hmA'
    exact sep_cast hmA' (by dsimp only [pool0A, pool1A]; ac_rfl)
  have hpt_cap' := hCtx.hpt_cap
  rw [hCtx.hslR, hCtx.hslB] at hpt_cap'
  have hnr_eq : s.cur_nr.toNat = s0.cur_nr.toNat := congrArg BitVec.toNat hs_nr
  have hpt_max : pt.toNat ≤ s0.pcap.toNat := by
    rw [hnr_eq] at hpt_le
    omega
  have hqn_le' : qn.toNat ≤ nb.toNat * s0.cur_nr.toNat := hnr_eq ▸ hqn_le
  have hqn_max : qn.toNat ≤ s0.qcap.toNat :=
    le_trans hqn_le' hCtx.hnb_nr_q
  have hSlt : ∀ i < s0.tn.toNat,
      MonoSliceOk poolL (dstTm1.getD i 0#32).toNat pt.toNat ∧
      (poolL.getD (dstTm1.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 := by
    intro i hi
    obtain ⟨hsl, h32⟩ := hCtx.hSl1 i hi
    have hlen_keep : poolL.getD (dstTm1.getD i 0#32).toNat 0#32 =
        (if s.pc.toNat = 0 then pool0_1 else pool1_1).getD (dstTm1.getD i 0#32).toNat 0#32 :=
      hpre _ hsl.1
    dsimp only [dstTm1] at hlen_keep ⊢
    exact ⟨⟨by have := hsl.1; omega, by rw [hlen_keep]; have := hsl.2; omega⟩,
      by rw [hlen_keep]; exact h32⟩
  have hSot : ∀ i < s0.tn.toNat, MonoSorted poolL (dstTm1.getD i 0#32).toNat := fun i hi => by
    have heq := symListAt_congr_take (hCtx.hSl1 i hi).1 hpre
    dsimp only [dstTm1]
    simpa only [MonoSorted, heq] using hCtx.hSo1 i hi
  have hSit : SigOk poolL dstTm1 dstTs1 s0.tn.toNat := fun i hi x hx => by
    rw [symListAt_congr_take (hCtx.hSl1 i hi).1 hpre] at hx
    exact hCtx.hSi1 i hi x hx
  refine wp_call_of_spec _ _ (hMerge ⟨cx, nb, ⟨⟩⟩ mA _ X
    ⟨sA, tm0_1, tm1_1, ts0, tl0, th0, ts1, tl1, th1, pool0A, pool1A,
      qmL, qsL, qlL, qhL, ix, ix2, bx, vqOff, vq, vqSkip,
      (array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
       array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆ R),
      by rw [hsA_pc]; exact hCtx.hpc, by rw [hsA_tc]; exact hCtx.htc,
      by rw [hsA_tn, hsA_tcap]; exact hCtx.htn,
      by rw [hsA_qn, hsA_qcap]; exact hqn_max,
      by rw [hsA_pt, hsA_pcap]; exact hpt_max,
      by rw [hsA_tcap]; exact hCtx.htcap30,
      by rw [hsA_qcap]; exact hCtx.hqcap32,
      by rw [hsA_tn, hsA_qn, hsA_tcap]; have := hCtx.hnb_nr_t; omega,
      by rw [hsA_tn]; exact hCtx.hnb_tn, hCtx.hnb_bx,
      by rw [hsA_tn]; exact hCtx.hinc,
      by rw [hsA_tcap]; exact hCtx.htm0_len, by rw [hsA_tcap]; exact hCtx.htm1_len,
      by rw [hsA_tcap]; exact hCtx.hts0_len, by rw [hsA_tcap]; exact hCtx.htl0_len,
      by rw [hsA_tcap]; exact hCtx.hth0_len, by rw [hsA_tcap]; exact hCtx.hts1_len,
      by rw [hsA_tcap]; exact hCtx.htl1_len, by rw [hsA_tcap]; exact hCtx.hth1_len,
      by rw [hsA_pcap, hpool0A_len]; exact hCtx.hp0_len,
      by rw [hsA_pcap, hpool1A_len]; exact hCtx.hp1_len,
      by rw [hsA_qcap, hl2]; exact hCtx.hqm_len, by rw [hsA_qcap, hl3]; exact hCtx.hqs_len,
      by rw [hsA_qcap, hl4]; exact hCtx.hql_len, by rw [hsA_qcap, hl5]; exact hCtx.hqh_len,
      by rw [hsA_qcap]; exact hCtx.hix_len, by rw [hsA_qcap]; exact hCtx.hix2_len,
      by change MasksOk sA.modW sA.mlo sA.mhi
         rw [hsA_nout, show sA.mlo = s0.mlo from hs_mlo, show sA.mhi = s0.mhi from hs_mhi]
         exact hCtx.hMasks,
      by rw [hpoolA_sel, hsA_tn, hsA_pt, hsA_tc]; exact hSlt,
      by rw [hpoolA_sel, hsA_qn, hsA_pt]; exact hSlq,
      by rw [hpoolA_sel, hsA_tn, hsA_tc]; exact hSot,
      by rw [hpoolA_sel, hsA_qn]; exact hSoq,
      by rw [hpoolA_sel, hsA_tn, hsA_tc]; exact hSit,
      by rw [hpoolA_sel, hsA_qn]; exact hSiq,
      hm_pack,
      fun s2 tm0_2 tm1_2 ts0_2 tl0_2 th0_2 ts1_2 tl1_2 th1_2 ql_2 qh_2 ix_2 ix2_2 m2
        htc2 htn2 htn_cap2 hs2 htm0_2 htm1_2 hts0_2 htl0_2 hth0_2 hts1_2 htl1_2 hth1_2
        hql_2 hqh_2 hix_cases _ _ _ hSl2 hSo2 hSi2 hW2 hSy2 hEv2 hm2 => by
        c0_hsteps_nogrp
        have hs2_eq : s2 = { s0 with
            tc := s2.tc, tn := s2.tn, pc := s2.pc, ptop := s2.ptop,
            qn := s2.qn, ix := s2.ix, ix2 := s2.ix2 } := by
          rw [hs2]; dsimp only [sA]; conv => lhs; rw [hs1]
        have hpc2 : s2.pc.toNat < 2 := by rw [hs2, hsA_pc]; exact hCtx.hpc
        have htc2' : s2.tc.toNat < 2 := by rw [htc2, hsA_tc]; omega
        have hpt2 : s2.ptop.toNat ≤ s0.pcap.toNat := by rw [hs2, hsA_pt]; exact hpt_max
        have htn_cap2' : s2.tn.toNat ≤ s0.tcap.toNat := by rw [← hsA_tcap]; exact htn_cap2
        have hix_cases' : ((s2.ix = s0.ix ∧ s2.ix2 = s0.ix2 ∧
              ix_2.length = ix.length ∧ ix2_2.length = ix2.length) ∨
             (s2.ix = s0.ix2 ∧ s2.ix2 = s0.ix ∧
              ix_2.length = ix2.length ∧ ix2_2.length = ix.length)) := by
          dsimp only [sA] at hix_cases; rw [hs_ix, hs_ix2] at hix_cases; exact hix_cases
        have hp_sel2 : (if s2.pc.toNat = 0 then pool0A else pool1A) = poolL := by
          rw [hs2]; exact hpoolA_sel
        have htc_1 : sA.tc.toNat = 0 ∨ sA.tc.toNat = 1 := by
          rw [hsA_tc]; have := hCtx.htc; omega
        have htc_sw_m : (if s2.tc.toNat = 0 then tm0_2 else tm1_2) =
            (if sA.tc.toNat = 0 then tm1_2 else tm0_2) := by
          rw [htc2]; rcases htc_1 with h0 | h1; · simp [h0]
          simp [h1]
        have htc_sw_s : (if s2.tc.toNat = 0 then ts0_2 else ts1_2) =
            (if sA.tc.toNat = 0 then ts1_2 else ts0_2) := by
          rw [htc2]; rcases htc_1 with h0 | h1; · simp [h0]
          simp [h1]
        have htc_sw_l : (if s2.tc.toNat = 0 then tl0_2 else tl1_2) =
            (if sA.tc.toNat = 0 then tl1_2 else tl0_2) := by
          rw [htc2]; rcases htc_1 with h0 | h1; · simp [h0]
          simp [h1]
        have htc_sw_h : (if s2.tc.toNat = 0 then th0_2 else th1_2) =
            (if sA.tc.toNat = 0 then th1_2 else th0_2) := by
          rw [htc2]; rcases htc_1 with h0 | h1; · simp [h0]
          simp [h1]
        refine hOk s2 tm0_2 tm1_2 ts0_2 tl0_2 th0_2 ts1_2 tl1_2 th1_2 pool0A pool1A
          qmL qsL ql_2 qh_2 ix_2 ix2_2 bx vqOff vq vqSkip m2
          hpc2 htc2' hpt2 htn_cap2' hs2_eq
          (htm0_2.trans hCtx.htm0_eq) (htm1_2.trans hCtx.htm1_eq) hts0_2 htl0_2 hth0_2
          hts1_2 htl1_2 hth1_2 (hpool0A_len.trans hCtx.hp0_eq) (hpool1A_len.trans hCtx.hp1_eq)
          hl2 hl3 (hql_2.trans hl4) (hqh_2.trans hl5)
            hix_cases' rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hp_sel2, hs2, hsA_pt, htc_sw_m]; intro i hi
          simpa only [hpoolA_sel, hsA_pt] using hSl2 i hi
        · rw [hp_sel2, htc_sw_m]; intro i hi; simpa only [hpoolA_sel] using hSo2 i hi
        · rw [hp_sel2, htc_sw_m, htc_sw_s]; simpa only [hpoolA_sel] using hSi2
        · have hpt2_eq : s2.ptop.toNat = pt.toNat := by rw [hs2, hsA_pt]
          rw [hp_sel2, hpt2_eq, htc_sw_m, hsA_tc]
          have hle := hW2; rw [hpoolA_sel, hsA_tn, hsA_qn, hsA_tc] at hle
          have hm_pre : monoTotalWords poolL (if s.tc.toNat = 0 then tm0_1 else tm1_1) s0.tn.toNat =
              monoTotalWords (if s.pc.toNat = 0 then pool0_1 else pool1_1)
                (if s.tc.toNat = 0 then tm0_1 else tm1_1) s0.tn.toNat :=
            monoTotalWords_congr_prefix (fun i hi => (hCtx.hSl1 i hi).1) hpre (fun _ _ => rfl)
          have := hCtx.hTot1
          omega
        · intro bd hSb0 hSbR
          have hSb1 :
              SymsBound (if s.pc.toNat = 0 then pool0_1 else pool1_1) dstTm1 s0.tn.toNat bd :=
            fun t ht x hx => by
              rw [hCtx.hSym1 t ht] at hx
              exact hSb0 t ht x hx
          have hSbT : SymsBound poolL dstTm1 s0.tn.toNat bd := fun t ht x hx => by
            rw [symListAt_congr_take (hCtx.hSl1 t ht).1 hpre] at hx
            exact hSb1 t ht x hx
          have hSbQ : SymsBound poolL qmL qn.toNat bd := by
            rw [← hs_tn] at hSb1
            exact hSyq bd hSb1 (by rw [hnr_eq]; exact hSbR)
          have hres := hSy2 bd (by rwa [hpoolA_sel, hsA_tn, hsA_tc])
            (by rwa [hpoolA_sel, hsA_qn])
          rw [hp_sel2, htc_sw_m]; simpa only [hpoolA_sel] using hres
        · intro σ hV
          rw [hp_sel2, htc_sw_m, htc_sw_l, htc_sw_h]
          have hev := hEv2 σ
          rw [hpoolA_sel, hsA_nout, hsA_tc, hsA_tn, hsA_qn] at hev
          have hEvq' := hEvq σ hV
          rw [hs_nout] at hEvq'
          rw [hev, hEvq']
          have hnbx_eq :
              nonBxTermSum s0.modW σ poolL dstTm1 dstTl1 dstTh1 bx nb.toNat s0.tn.toNat =
              nonBxTermSum s0.modW σ (if s0.pc.toNat = 0 then pool0 else pool1)
                (if s0.tc.toNat = 0 then tm0 else tm1) (if s0.tc.toNat = 0 then tl0 else tl1)
                (if s0.tc.toNat = 0 then th0 else th1) bx nb.toNat s0.tn.toNat := by
            apply nonBxRangeSum_congr hCtx.hnb_bx hCtx.hnb_bx (fun _ _ => rfl)
            · intro t ht
              rw [Nat.zero_add, symListAt_congr_take (hCtx.hSl1 t ht).1 hpre]
              exact hCtx.hSym1 t ht
            · intro t _; dsimp only [dstTl1, dstTh1]; rw [hs_tc]; exact ⟨rfl, rfl⟩
          have hbx_eq : bxTermSum s0.modW σ (if s.pc.toNat = 0 then pool0_1 else pool1_1)
                dstTm1 dstTl1 dstTh1 bx nb.toNat =
              bxTermSum s0.modW σ (if s0.pc.toNat = 0 then pool0 else pool1)
                (if s0.tc.toNat = 0 then tm0 else tm1) (if s0.tc.toNat = 0 then tl0 else tl1)
                (if s0.tc.toNat = 0 then th0 else th1) bx nb.toNat := by
            apply bxTermSum_congr (fun _ _ => rfl)
            · intro b hb; exact hCtx.hSym1 (bx.getD b 0#32).toNat (hCtx.hinc.1 b hb)
            · intro b _; dsimp only [dstTl1, dstTh1]; rw [hs_tc]; exact ⟨rfl, rfl⟩
          dsimp only [dstTm1, dstTl1, dstTh1] at hnbx_eq hbx_eq
          rw [hnbx_eq, hbx_eq]
          exact (polyEval_eq_nonBxTermSum_add_bxTermSum s0.modW σ
            (if s0.pc.toNat = 0 then pool0 else pool1) (if s0.tc.toNat = 0 then tm0 else tm1)
            (if s0.tc.toNat = 0 then tl0 else tl1) (if s0.tc.toNat = 0 then th0 else th1)
            bx hCtx.hinc hCtx.hnb_bx).symm
        · have hsp : s2.partner = s.partner := by rw [hs2]
          have hrm : s2.cur_rm = s.cur_rm := by rw [hs2]
          have hrl : s2.cur_rl = s.cur_rl := by rw [hs2]
          have hrh : s2.cur_rh = s.cur_rh := by rw [hs2]
          have hrp : s2.cur_rp = s.cur_rp := by rw [hs2]
          rw [hsp, hrm, hrl, hrh, hrp]
          exact sep_cast hm2 (by ac_rfl)⟩)

end

end LeanQbe.T.Examples.Arisca.Proof
