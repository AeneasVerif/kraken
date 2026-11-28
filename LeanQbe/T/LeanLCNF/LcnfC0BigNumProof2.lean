module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof2a
import all Kraken.Mem
import all Kraken.Separation
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Soundness Proofs for `LcnfC0BigNum` Multi-Limb Operations (`Milestone R1`, Part 2b)

Part B proofs of `rtR1Mod`: `bn_mul`, `bn_shl`, `bn_shr`, and phased `bn_divmod`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil

local macro "sep_ac" : tactic =>
  `(tactic| exact sep_cast_ac (by assumption) (by ac_rfl))

local macro "sep_use " t:term : tactic =>
  `(tactic| exact sep_cast_ac $t (by ac_rfl))

/-! ## 3. Part B Helpers & `bn_mul`, `bn_shl`, `bn_shr` -/

private theorem mul_inner_step_eq {outPre outNew aPrev carry carry' av cur s2 bj bPre bNext : Nat}
    {i j : Nat}
    (houtSwap : outNew + 2 ^ (64 * (i + j)) * cur = outPre + 2 ^ (64 * (i + j)) * s2)
    (hmac : s2 + 2 ^ 64 * carry' = cur + carry + av * bj)
    (hinv : outPre + 2 ^ (64 * (i + j)) * carry = aPrev + 2 ^ (64 * i) * (av * bPre))
    (hbNext : bNext = bPre + 2 ^ (64 * j) * bj) :
    outNew + 2 ^ (64 * (i + (j + 1))) * carry' = aPrev + 2 ^ (64 * i) * (av * bNext) := by
  have hpow : 2 ^ (64 * (i + (j + 1))) = 2 ^ (64 * (i + j)) * 2 ^ 64 := by
    rw [show 64 * (i + (j + 1)) = 64 * (i + j) + 64 by omega, Nat.pow_add]
  have hsplit : 2 ^ (64 * (i + j)) = 2 ^ (64 * i) * 2 ^ (64 * j) := by
    rw [Nat.mul_add, Nat.pow_add]
  have h0 : 2 ^ (64 * (i + j)) * (s2 + 2 ^ 64 * carry') =
      2 ^ (64 * (i + j)) * (cur + carry + av * bj) := congrArg (2 ^ (64 * (i + j)) * ·) hmac
  rw [Nat.mul_add (2 ^ (64 * (i + j))), ← Nat.mul_assoc, ← hpow,
      Nat.mul_add (2 ^ (64 * (i + j))), Nat.mul_add (2 ^ (64 * (i + j))),
      show 2 ^ (64 * (i + j)) * (av * bj) = 2 ^ (64 * i) * (av * (2 ^ (64 * j) * bj)) from by
        rw [hsplit]; ac_rfl] at h0
  have hnext : 2 ^ (64 * i) * (av * bNext) =
      2 ^ (64 * i) * (av * bPre) + 2 ^ (64 * i) * (av * (2 ^ (64 * j) * bj)) := by
    rw [hbNext, Nat.mul_add av, Nat.mul_add (2 ^ (64 * i))]
  rw [hnext]
  omega

private theorem shr_limbs_eq_of_lim (aXs outXs' : List (BitVec 64)) (na ws bs nres : Nat)
    (hbsLt : bs < 64) (hwsLt : ws < na) (hnres : nres = na - ws)
    (hna : na ≤ aXs.length) (hnout : nres ≤ outXs'.length)
    (hlast : outXs'[nres - 1]'(by omega) = (aXs[ws + (nres - 1)]'(by omega)) >>> bs)
    (hinit : ∀ j (hj : j + 1 < nres),
      outXs'[j]'(by omega) =
        ((aXs[ws + j]'(by omega)) >>> bs) ||| ((aXs[ws + j + 1]'(by omega)) <<< (64 - bs))) :
    limbsVal (outXs'.take nres) = limbsVal (aXs.take na) >>> (64 * ws + bs) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_shiftRight, limbsVal_take_testBit _ hnout, limbsVal_take_testBit _ hna]
  let j := k / 64
  let r := k % 64
  have hjr : k = 64 * j + r := by omega
  have hrLt : r < 64 := Nat.mod_lt _ (by omega)
  have hshiftEq : 64 * ws + bs + k = 64 * (ws + j) + (bs + r) := by omega
  by_cases hj : j < nres
  · have hj' : k / 64 < nres := hj
    simp only [hj', ↓reduceDIte]
    have bitR_lshr : ∀ (v : BitVec 64), (v >>> bs).toNat.testBit r =
        if r + bs < 64 then v.toNat.testBit (bs + r) else false := by
      intro v
      rw [BitVec.toNat_ushiftRight, Nat.testBit_shiftRight]
      by_cases hlt : r + bs < 64
      · simp only [hlt, ↓reduceIte]
      · simp only [hlt, ↓reduceIte]
        exact nat_testBit_false_of_lt
          (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
    have bitR_shl : ∀ (v : BitVec 64), (v <<< (64 - bs)).toNat.testBit r =
        if r + bs < 64 then false else v.toNat.testBit (r + bs - 64) := by
      intro v
      rw [BitVec.toNat_shiftLeft, Nat.testBit_mod_two_pow,
          show decide (r < 64) = true by exact decide_eq_true hrLt, Bool.true_and,
          Nat.testBit_shiftLeft]
      by_cases hlt : r + bs < 64
      · have hnot : ¬ (64 - bs ≤ r) := by omega
        simp only [hlt, ↓reduceIte, decide_eq_false hnot, Bool.false_and]
      · have hge : 64 - bs ≤ r := by omega
        have hsub : r - (64 - bs) = r + bs - 64 := by omega
        simp only [hlt, ↓reduceIte, decide_eq_true hge, Bool.true_and, hsub]
    by_cases hj1 : j + 1 < nres
    · rw [hinit j hj1, BitVec.toNat_or, Nat.testBit_or, bitR_lshr, bitR_shl]
      by_cases hrb : r + bs < 64
      · simp only [hrb, ↓reduceIte, Bool.or_false]
        have hdiv : (64 * ws + bs + k) / 64 = ws + j := by omega
        have hmod : (64 * ws + bs + k) % 64 = bs + r := by omega
        have hltNa : ws + j < na := by omega
        simp only [hdiv, hmod, hltNa, ↓reduceDIte]
      · simp only [hrb, ↓reduceIte, Bool.false_or]
        have hdiv : (64 * ws + bs + k) / 64 = ws + j + 1 := by omega
        have hmod : (64 * ws + bs + k) % 64 = r + bs - 64 := by omega
        have hltNa : ws + j + 1 < na := by omega
        simp only [hdiv, hmod, hltNa, ↓reduceDIte]
    · have hjEq : k / 64 = nres - 1 := by omega
      simp only [hjEq]
      rw [hlast, bitR_lshr]
      by_cases hrb : r + bs < 64
      · simp only [hrb, ↓reduceIte]
        have hdiv : (64 * ws + bs + k) / 64 = ws + (nres - 1) := by omega
        have hmod : (64 * ws + bs + k) % 64 = bs + r := by omega
        have hltNa : ws + (nres - 1) < na := by omega
        simp only [hdiv, hmod, hltNa, ↓reduceDIte]
      · simp only [hrb, ↓reduceIte]
        have hgeNa : ¬ (64 * ws + bs + k) / 64 < na := by omega
        simp only [hgeNa, ↓reduceDIte]
  · have hj' : ¬ k / 64 < nres := hj
    simp only [hj', ↓reduceDIte]
    have hgeNa : ¬ (64 * ws + bs + k) / 64 < na := by omega
    simp only [hgeNa, ↓reduceDIte]

private theorem bn_zero_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {dst n : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont rs}
    (hn : n.toNat ≤ xs.length) (hm : (array64 dst xs ⋆ R) m)
    (hk : ∀ m', (array64 dst (List.replicate n.toNat 0#64 ++ xs.drop n.toNat) ⋆ R) m' →
      wp rtR1Env Q X (k ()) m') :
    wp rtR1Env Q X (Expr.call (as := [i64, i64]) (bs := []) "bn_zero" (Arg.var dst, Arg.var n,
      ()) k) m := by
  apply wp_call_of
  apply rtR1Env_bn_zero
  exact ⟨xs, R, hn, hm, fun m' hm' => hk m' hm'⟩

private theorem bn_copy_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {dst src n : BitVec 64} {dstXs srcXs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont rs}
    (hdst : n.toNat ≤ dstXs.length) (hsrc : n.toNat ≤ srcXs.length)
    (hm : (array64 dst dstXs ⋆ array64 src srcXs ⋆ R) m)
    (hk : ∀ m', (array64 dst (srcXs.take n.toNat ++ dstXs.drop n.toNat) ⋆ array64 src srcXs ⋆
      R) m' →
      wp rtR1Env Q X (k ()) m') :
    wp rtR1Env Q X (Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
      (Arg.var dst, Arg.var src, Arg.var n, ()) k) m := by
  apply wp_call_of
  apply rtR1Env_bn_copy
  exact ⟨dstXs, srcXs, R, hdst, hsrc, hm, fun m' hm' => hk m' hm'⟩

private theorem bv64_mac_step_eq (a b cur carry : BitVec 64) :
    let lo := a * b
    let s1 := cur + lo + BitVec.ofNat 64 false.toNat
    let c1 := decide (2 ^ 64 ≤ cur.toNat + lo.toNat + false.toNat)
    let s2 := s1 + carry + BitVec.ofNat 64 false.toNat
    let c2 := decide (2 ^ 64 ≤ s1.toNat + carry.toNat + false.toNat)
    s2.toNat + 2 ^ 64 * ((BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) +
        (if c1 then (1 : BitVec 64) else 0)) +
        (if c2 then (1 : BitVec 64) else 0)).toNat =
      cur.toNat + carry.toNat + a.toNat * b.toNat := by
  have hlo : a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
  have hadd : ∀ x y : BitVec 64, x + y = BitVec.ofNat 64 (x.toNat + y.toNat) := by
    intro x y; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  have hm0 := mac_step_nat a b cur carry
  dsimp only at hm0 ⊢
  rw [show BitVec.ofNat 64 false.toNat = 0#64 from rfl, show false.toNat = 0 from rfl]
  simp only [Nat.add_zero, BitVec.add_zero, ← Nat.shiftRight_eq_div_pow]
  rw [hadd, hadd, hlo]
  simpa [← hlo, show (1 : BitVec 64) = 1#64 from rfl, show (0 : BitVec 64) = 0#64 from rfl] using
    hm0

theorem bn_mul_wp :
    ∀ xs m Q X, bnMulSpec xs m Q X → Func.wp rtR1Env bn_mul.body xs m Q X := by
  intro ⟨a, na, b, nb, out, ⟨⟩⟩ m Q X ⟨aXs, bXs, outXs, R, hna, hnb, hnout, hsum64, hm, hQ⟩
  dsimp only [Func.wp, bn_mul, bn_mul_body]
  c0_hsteps; dsimp only
  have hsum : (na + nb).toNat = na.toNat + nb.toNat := by c0_bv_omega
  refine bn_zero_call_wp (by omega) (sep_pick3_4 hm) fun m0 hm0 => ?_
  let nsum := na.toNat + nb.toNat
  rw [hsum] at hm0
  let out0 := List.replicate nsum 0#64 ++ outXs.drop nsum
  have hout0Len : out0.length = outXs.length := by dsimp [out0]; simp [List.length_drop]; omega
  have hout0Zero : ∀ k (hk : k < nsum), out0[k]'(by omega) = 0#64 := fun k hk => by
    dsimp [out0]; rw [List.getElem_append_left (by simp [hk]), List.getElem_replicate]
  c0_hsplit
  · have hna0 : na.toNat = 0 := by c0_bv_omega
    have hprod0 : limbsVal (aXs.take na.toNat) * limbsVal (bXs.take nb.toNat) = 0 := by simp [hna0]
    c0_hsteps; rw [hprod0] at hQ
    exact hQ out0 m0 hout0Len (by simp [limbLenNat]) (by simp [limbLenNat]) (sep_unpick3_4 hm0)
  · c0_hsplit
    · have hnb0 : nb.toNat = 0 := by c0_bv_omega
      have hprod0 : limbsVal (aXs.take na.toNat) * limbsVal (bXs.take nb.toNat) = 0 := by
        simp [hnb0]
      c0_hsteps; rw [hprod0] at hQ
      exact hQ out0 m0 hout0Len (by simp [limbLenNat]) (by simp [limbLenNat])
        (sep_unpick3_4 hm0)
    · have hnaPos : 0 < na.toNat := by c0_bv_omega
      have hnbPos : 0 < nb.toNat := by c0_bv_omega
      c0_hsteps_nogrp
      refine wp_cursor_up_loop 0 na.toNat na.isLt (α := List (BitVec 64))
        (fun iNat outXs' mL => outXs'.length = outXs.length ∧
          (∀ k (hk : k < nsum), iNat + nb.toNat ≤ k → ∀ (hko : k < outXs'.length),
            outXs'[k]'hko = 0#64) ∧
          limbsVal (outXs'.take (iNat + nb.toNat)) =
            limbsVal (aXs.take iNat) * limbsVal (bXs.take nb.toNat) ∧
          (array64 out outXs' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mL)
        (fun J hJ => by
          c0_hsteps
          refine hJ out0 m0 (Nat.zero_le _) ⟨hout0Len, fun k hk _ _ => hout0Zero k hk, ?_, hm0⟩
          have htake0 : out0.take nb.toNat = List.replicate nb.toNat 0#64 := by
            dsimp [out0]; rw [List.take_append_of_le_length (by simp; dsimp [nsum]; omega),
              List.take_replicate, Nat.min_eq_left (by dsimp [nsum]; omega)]
          rw [Nat.zero_add, htake0, limbsVal_replicate_zero, limbsVal_take_zero, Nat.zero_mul])
        ?_
      intro J iNat outXs' mL hiLe hiLt64 hiToNat ⟨hlenOut', hZeroTail, hProdInv, hmL⟩ hRec
      c0_hsplit
      · have hltNa : iNat < na.toNat := by c0_bv_omega
        have haLen : (BitVec.ofNat 64 iNat).toNat < aXs.length := by omega
        let av := aXs[iNat]'(Nat.lt_of_lt_of_le hltNa hna)
        c0_hsteps_nogrp
        refine wp_pair_up_loop 0 nb.toNat nb.isLt (α := List (BitVec 64))
          (fun jNat carry outXs'' mIn => outXs''.length = outXs.length ∧
            (∀ k (hk : k < nsum), iNat + nb.toNat ≤ k → ∀ (hko : k < outXs''.length),
              outXs''[k]'hko = 0#64) ∧
            limbsVal (outXs''.take (iNat + nb.toNat)) + 2 ^ (64 * (iNat + jNat)) * carry.toNat =
              limbsVal (aXs.take iNat) * limbsVal (bXs.take nb.toNat) +
                2 ^ (64 * iNat) * (av.toNat * limbsVal (bXs.take jNat)) ∧
            (array64 out outXs'' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mIn)
          (fun J1 hJ1 => by
            c0_hsteps
            exact hJ1 0#64 outXs' mL (Nat.zero_le _) ⟨hlenOut', hZeroTail, by simp [hProdInv],
              by simpa [av, hiToNat] using hmL⟩)
          ?_
        intro J1 jNat carry outXs'' mIn hjLe hjLt64 hjToNat
          ⟨hlenOut'', hZeroIn, hMacInv, hmIn⟩ hRecIn
        c0_hsplit
        · have hltNb : jNat < nb.toNat := by c0_bv_omega
          have hbLen : (BitVec.ofNat 64 jNat).toNat < bXs.length := by omega
          have hoLen : (BitVec.ofNat 64 iNat + BitVec.ofNat 64 jNat).toNat < outXs''.length := by
            c0_bv_omega
          have hijEq : (BitVec.ofNat 64 iNat + BitVec.ofNat 64 jNat).toNat = iNat + jNat := by
            c0_bv_omega
          c0_hsteps_nogrp
          let bj := bXs[jNat]'(Nat.lt_of_lt_of_le hltNb hnb)
          let cur := outXs''[iNat + jNat]'(by omega)
          let lo := av * bj
          let s1 := cur + lo + BitVec.ofNat 64 false.toNat
          let c1 := decide (2 ^ 64 ≤ cur.toNat + lo.toNat + false.toNat)
          let s2 := s1 + carry + BitVec.ofNat 64 false.toNat
          let c2 := decide (2 ^ 64 ≤ s1.toNat + carry.toNat + false.toNat)
          let cNext := BitVec.ofNat 64 (av.toNat * bj.toNat / 2 ^ 64) +
            (if c1 then (1 : BitVec 64) else 0) + (if c2 then (1 : BitVec 64) else 0)
          have hc1Eq : c1 = decide (2 ^ 64 ≤ outXs''[iNat + jNat].toNat +
              aXs[iNat].toNat * bXs[jNat].toNat % 2 ^ 64 + false.toNat) := by
            dsimp only [c1, cur, lo, av, bj]; rw [BitVec.toNat_mul]
          have hc2Eq : c2 = decide (2 ^ 64 ≤ (outXs''[iNat + jNat].toNat +
              aXs[iNat].toNat * bXs[jNat].toNat + false.toNat) % 2 ^ 64 +
              carry.toNat + false.toNat) := by
            dsimp only [c2, s1, cur, lo, av, bj]
            rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul]; simp
          simp only [hiToNat, hjToNat, hijEq] at hm ⊢
          refine wp_join_tup _ _ (fun p m1 => p.1 = (if c1 then (1 : BitVec 64) else 0) ∧ m1 = m)
            ?_ ?_
          · rintro ⟨w1, ⟨⟩⟩ m1 ⟨hw1, hm1⟩
            dsimp only at hw1 hm1; rw [hw1, hm1] at *
            c0_hsteps_nogrp
            refine wp_join_tup _ _ (fun p m2 => p.1 = (if c2 then (1 : BitVec 64) else 0) ∧ m2 = m)
              ?_ ?_
            · rintro ⟨w2, ⟨⟩⟩ m2 ⟨hw2, hm2⟩
              dsimp only at hw2 hm2; rw [hw2, hm2] at *
              c0_hsteps
              refine hRecIn cNext (outXs''.set (iNat + jNat) s2) m hltNb
                ⟨by simp [hlenOut''], fun k hk hik hko => by
                  rw [List.getElem_set_ne (by omega)]; exact hZeroIn k hk hik _, ?_, ?_⟩
              · exact mul_inner_step_eq
                  (limbsVal_take_set_of_lt outXs'' s2 (p := iNat + jNat) (M := iNat + nb.toNat)
                    (by omega) (by omega))
                  (bv64_mac_step_eq av bj cur carry) hMacInv
                  (limbsVal_take_succ (Nat.lt_of_lt_of_le hltNb hnb))
              · simpa [av, bj, cur, lo, s1, s2] using hm
            · intro Jc2 hJc2
              c0_hsplit
              · c0_hsteps
                exact hJc2 (1#64, ()) m ⟨by rw [hc2Eq, decide_eq_true (by assumption)]; rfl, rfl⟩
              · c0_hsteps
                exact hJc2 (0#64, ()) m ⟨by rw [hc2Eq, decide_eq_false (by assumption)]; rfl, rfl⟩
          · intro Jc1 hJc1
            c0_hsplit
            · c0_hsteps
              exact hJc1 (1#64, ()) m ⟨by rw [hc1Eq, decide_eq_true (by assumption)]; rfl, rfl⟩
            · c0_hsteps
              exact hJc1 (0#64, ()) m ⟨by rw [hc1Eq, decide_eq_false (by assumption)]; rfl, rfl⟩
        · have hjEqNb : jNat = nb.toNat := by c0_bv_omega
          subst hjEqNb
          have hoLenEnd : (BitVec.ofNat 64 iNat + nb).toNat < outXs''.length := by c0_bv_omega
          have inbToNat : (BitVec.ofNat 64 iNat + nb).toNat = iNat + nb.toNat := by c0_bv_omega
          c0_hsteps
          rw [inbToNat] at hm
          refine hRec (outXs''.set (iNat + nb.toNat) carry) m hltNa
            ⟨by simp [hlenOut''], fun k hk hik hko => by
              rw [List.getElem_set_ne (by omega)]; exact hZeroIn k hk (by omega) _, ?_, hm⟩
          rw [show iNat + 1 + nb.toNat = (iNat + nb.toNat) + 1 by omega,
            limbsVal_take_set_succ outXs'' carry (by omega), hMacInv,
            limbsVal_take_succ (Nat.lt_of_lt_of_le hltNa hna)]
          dsimp [av]; rw [← Nat.mul_assoc, ← Nat.add_mul]
      · have hiEqNa : iNat = na.toNat := by c0_bv_omega
        subst hiEqNa
        c0_hsteps
        rw [← bv64_ofNat_toNat (na + nb), hsum]
        exact bn_trim_tail_wp hsum64 (by omega) hmL hProdInv fun hLenLe hTakeEq =>
          hQ outXs' mL hlenOut' (by rw [hlenOut'] at hLenLe; exact hLenLe)
            hTakeEq (sep_unpick3_4 hmL)

theorem bn_shl_wp :
    ∀ xs m Q X, bnShlSpec xs m Q X → Func.wp rtR1Env bn_shl.body xs m Q X := by
  intro ⟨a, na, ws, bs, out, ⟨⟩⟩ m Q X ⟨aXs, outXs, R, hna, hbs, houtOr, hbound, hm, hQ⟩
  dsimp only [Func.wp, bn_shl, bn_shl_body]
  c0_hsplit
  · have hna0 : na.toNat = 0 := by c0_bv_omega
    have hres0 : limbsVal (aXs.take na.toNat) <<< (64 * ws.toNat + bs.toNat) = 0 := by simp [hna0]
    c0_hsteps; rw [hres0] at hQ
    exact hQ outXs m rfl (by simp [limbLenNat]) (by simp [limbLenNat]) hm
  · have hnaPos : 0 < na.toNat := by c0_bv_omega
    have houtLe : ws.toNat + na.toNat + 1 ≤ outXs.length := by rcases houtOr with h0 | hle <;> omega
    c0_hsteps
    refine bn_zero_call_wp (by omega) (sep_pick2_3 hm) fun m0 hm0 => ?_
    let out0 := List.replicate ws.toNat 0#64 ++ outXs.drop ws.toNat
    have hout0Len : out0.length = outXs.length := by dsimp [out0]; simp [List.length_drop]; omega
    have hwsnaEq : (ws + na).toNat = ws.toNat + na.toNat := by c0_bv_omega
    have hwsna1Eq : (ws + na + 1).toNat = ws.toNat + na.toNat + 1 := by c0_bv_omega
    c0_hsplit
    · have hbs0 : bs = 0#64 := by assumption
      c0_hsteps
      have hsp := array64_split2 out out0 ws.toNat (by omega)
      rw [← bv64_mul8_eq] at hsp
      have hmSplit : (array64 (out + 8 * ws) (out0.drop ws.toNat) ⋆
          array64 a aXs ⋆ (array64 out (out0.take ws.toNat) ⋆ R)) m0 := by
        rw [hsp] at hm0; exact sep_ac hm0
      refine bn_copy_call_wp (by rw [List.length_drop, hout0Len]; omega)
        hna hmSplit fun m1 hm1 => ?_
      let dstTail := aXs.take na.toNat ++ (out0.drop ws.toNat).drop na.toNat
      let out1 := out0.take ws.toNat ++ dstTail
      have hout1Len : out1.length = outXs.length := by
        dsimp [out1, dstTail]; simp [List.length_take, List.length_drop, hout0Len]; omega
      have hmJoined : (array64 out out1 ⋆ (array64 a aXs ⋆ R)) m1 := by
        have hlenWs : (out0.take ws.toNat).length = ws.toNat := by simp [hout0Len]; omega
        have happ := array64_append out (out0.take ws.toNat) dstTail
        rw [hlenWs, ← bv64_mul8_eq] at happ
        have hm1' : ((array64 out (out0.take ws.toNat) ⋆ array64 (out + 8 * ws) dstTail) ⋆
            (array64 a aXs ⋆ R)) m1 := sep_ac hm1
        rwa [← happ] at hm1'
      c0_hsteps
      rw [hwsnaEq] at hm
      let out2 := out1.set (ws.toNat + na.toNat) 0#64
      have hout2Val : limbsVal (out2.take (ws.toNat + na.toNat + 1)) =
          limbsVal (aXs.take na.toNat) <<< (64 * ws.toNat + bs.toNat) := by
        dsimp [out2]
        rw [limbsVal_take_set_succ out1 0#64 (by rw [hout1Len]; omega),
          show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
        have hout0Take : out0.take ws.toNat = List.replicate ws.toNat 0#64 := by
          dsimp [out0]
          rw [List.take_append_of_le_length (by simp), List.take_replicate, Nat.min_self]
        have hout1Take : out1.take (ws.toNat + na.toNat) =
            List.replicate ws.toNat 0#64 ++ aXs.take na.toNat := by
          dsimp [out1, dstTail]
          rw [hout0Take, List.take_append, List.take_of_length_le (by simp),
            List.length_replicate, show ws.toNat + na.toNat - ws.toNat = na.toNat by omega,
            List.take_append, List.take_of_length_le
              (by rw [List.length_take_of_le hna]; exact Nat.le_refl _),
            List.length_take_of_le hna, Nat.sub_self, List.take_zero, List.append_nil]
        rw [hout1Take, limbsVal_append, limbsVal_replicate_zero, Nat.zero_add,
          List.length_replicate, show bs.toNat = 0 by simp [hbs0], Nat.add_zero,
          Nat.shiftLeft_eq, Nat.mul_comm]
      rw [← bv64_ofNat_toNat (ws + na + 1), hwsna1Eq]
      exact bn_trim_tail_wp (by omega) (by simp [hout1Len]; exact houtLe) hm hout2Val
        fun hLenLe hTakeEq =>
          hQ out2 m (by simp [out2, hout1Len])
            (by rw [List.length_set, hout1Len] at hLenLe; exact hLenLe)
            hTakeEq (sep_unpick2_3 hm)
    · have hbsPos : 0 < bs.toNat := by c0_bv_omega
      have hbsMod : bs.toNat % 64 = bs.toNat := Nat.mod_eq_of_lt hbs
      have hsub64Nat : (64#64 - bs).toNat = 64 - bs.toNat := by
        rw [BitVec.toNat_sub_of_le (by change bs.toNat ≤ 64; omega)]; rfl
      have hsub64Mod : (64 - bs).toNat % 64 = 64 - bs.toNat := by
        rw [show (64 : BitVec 64) - bs = 64#64 - bs from rfl, hsub64Nat]
        exact Nat.mod_eq_of_lt (by omega)
      c0_hsteps_nogrp
      refine wp_pair_up_loop 0 na.toNat na.isLt (α := List (BitVec 64))
        (fun iNat carry outXs' mL => outXs'.length = outXs.length ∧ carry.toNat < 2 ^ bs.toNat ∧
          limbsVal (outXs'.take (ws.toNat + iNat)) + 2 ^ (64 * (ws.toNat + iNat)) * carry.toNat =
            limbsVal (aXs.take iNat) <<< (64 * ws.toNat + bs.toNat) ∧
          (array64 out outXs' ⋆ (array64 a aXs ⋆ R)) mL)
        (fun J hJ => by
          c0_hsteps
          refine hJ 0#64 out0 m0 (Nat.zero_le _) ⟨hout0Len, Nat.two_pow_pos _, ?_, hm0⟩
          have htake0 : out0.take ws.toNat = List.replicate ws.toNat 0#64 := by
            dsimp [out0]
            rw [List.take_append_of_le_length (by simp), List.take_replicate, Nat.min_self]
          rw [Nat.add_zero, htake0, limbsVal_replicate_zero, limbsVal_take_zero]; simp)
        ?_
      intro J iNat carry outXs' mL hiLe hiLt64 hiToNat
        ⟨hlenOut', hcarryLt, hShlInv, hmL⟩ hRec
      c0_hsplit
      · have hltNa : iNat < na.toNat := by c0_bv_omega
        have haLen : (BitVec.ofNat 64 iNat).toNat < aXs.length := by omega
        have hoLen : (ws + BitVec.ofNat 64 iNat).toNat < outXs'.length := by c0_bv_omega
        have hwsiEq : (ws + BitVec.ofNat 64 iNat).toNat = ws.toNat + iNat := by c0_bv_omega
        c0_hsteps
        let ld := aXs[iNat]'(Nat.lt_of_lt_of_le hltNa hna)
        let w := (ld <<< bs) ||| carry
        let carryNext := ld >>> (64#64 - bs)
        have hstep := shl_step_nat ld bs carry hbs hcarryLt
        simp only [hiToNat, hwsiEq] at hm ⊢
        rw [hbsMod, ← BitVec.shiftLeft_eq'] at hm
        rw [hsub64Mod, ← hsub64Nat, ← BitVec.ushiftRight_eq']
        refine hRec carryNext (outXs'.set (ws.toNat + iNat) w) m hltNa
          ⟨by simp [hlenOut'], hstep.2, ?_, hm⟩
        rw [show ws.toNat + (iNat + 1) = (ws.toNat + iNat) + 1 by omega,
          limbsVal_take_set_succ outXs' w (by omega),
          limbsVal_take_succ (Nat.lt_of_lt_of_le hltNa hna), Nat.shiftLeft_eq, Nat.add_mul]
        have hpow1 : 2 ^ (64 * (ws.toNat + iNat + 1)) = 2 ^ (64 * (ws.toNat + iNat)) * 2 ^ 64 := by
          rw [show 64 * (ws.toNat + iNat + 1) = 64 * (ws.toNat + iNat) + 64 by omega, Nat.pow_add]
        have hpow2 : 2 ^ (64 * (ws.toNat + iNat)) * 2 ^ bs.toNat =
            2 ^ (64 * iNat) * 2 ^ (64 * ws.toNat + bs.toNat) := by
          rw [Nat.mul_add, Nat.pow_add, Nat.pow_add]; ac_rfl
        have hshlInv' : limbsVal (outXs'.take (ws.toNat + iNat)) +
            2 ^ (64 * (ws.toNat + iNat)) * carry.toNat =
            limbsVal (aXs.take iNat) * 2 ^ (64 * ws.toNat + bs.toNat) := by
          simpa [Nat.shiftLeft_eq] using hShlInv
        calc limbsVal (outXs'.take (ws.toNat + iNat)) + 2 ^ (64 * (ws.toNat + iNat)) * w.toNat +
              2 ^ (64 * (ws.toNat + iNat + 1)) * carryNext.toNat
          _ = limbsVal (outXs'.take (ws.toNat + iNat)) +
              2 ^ (64 * (ws.toNat + iNat)) * (w.toNat + 2 ^ 64 * carryNext.toNat) := by
            rw [hpow1, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add]
          _ = limbsVal (outXs'.take (ws.toNat + iNat)) +
              2 ^ (64 * (ws.toNat + iNat)) * carry.toNat +
              (2 ^ (64 * (ws.toNat + iNat)) * 2 ^ bs.toNat) * ld.toNat := by
            rw [hstep.1, Nat.mul_add]; ac_rfl
          _ = _ := by rw [hshlInv', hpow2]; ac_rfl
      · have hiEqNa : iNat = na.toNat := by c0_bv_omega
        subst hiEqNa
        have hoLenEnd : (ws + na).toNat < outXs'.length := by c0_bv_omega
        c0_hsteps
        rw [hwsnaEq] at hm
        let out2 := outXs'.set (ws.toNat + na.toNat) carry
        have hout2Len : out2.length = outXs.length := by simp [out2, hlenOut']
        have hout2Val : limbsVal (out2.take (ws.toNat + na.toNat + 1)) =
            limbsVal (aXs.take na.toNat) <<< (64 * ws.toNat + bs.toNat) := by
          dsimp [out2]; rw [limbsVal_take_set_succ outXs' carry (by omega), hShlInv]
        rw [← bv64_ofNat_toNat (ws + na + 1), hwsna1Eq]
        exact bn_trim_tail_wp (by omega) (by rw [hout2Len]; exact houtLe) hm hout2Val
          fun hLenLe hTakeEq =>
            hQ out2 m hout2Len (by rw [hout2Len] at hLenLe; exact hLenLe) hTakeEq (sep_unpick2_3 hm)

theorem bn_shr_wp :
    ∀ xs m Q X, bnShrSpec xs m Q X → Func.wp rtR1Env bn_shr.body xs m Q X := by
  intro ⟨a, na, ws, bs, out, ⟨⟩⟩ m Q X ⟨aXs, outXs, R, hna, hbs, houtOr, hm, hQ⟩
  dsimp only [Func.wp, bn_shr, bn_shr_body]
  c0_hsplit
  · have hleWs : na.toNat ≤ ws.toNat := by c0_bv_omega
    have hltPow : limbsVal (aXs.take na.toNat) < 2 ^ (64 * ws.toNat + bs.toNat) :=
      Nat.lt_of_lt_of_le (limbsVal_take_lt_pow aXs na.toNat)
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hres0 : limbsVal (aXs.take na.toNat) >>> (64 * ws.toNat + bs.toNat) = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hltPow]
    c0_hsteps; rw [hres0] at hQ
    exact hQ outXs m rfl (by simp [limbLenNat]) (by simp [limbLenNat]) hm
  · have hwsLtNa : ws.toNat < na.toNat := by c0_bv_omega
    let nres := na.toNat - ws.toNat
    have hnresPos : 0 < nres := by dsimp [nres]; omega
    have hnresLeOut : nres ≤ outXs.length := by rcases houtOr with hle | hle <;> omega
    have hnresLt64 : nres < 2 ^ 64 := by dsimp [nres]; omega
    have hsubEq : (na - ws).toNat = nres := BitVec.toNat_sub_of_le (Nat.le_of_lt hwsLtNa)
    c0_hsplit
    · have hbs0 : bs = 0#64 := by assumption
      c0_hsteps
      have hsp := array64_split2 a aXs ws.toNat (by omega)
      rw [← bv64_mul8_eq] at hsp
      have hmSplit : (array64 out outXs ⋆ array64 (a + 8 * ws) (aXs.drop ws.toNat) ⋆
          (array64 a (aXs.take ws.toNat) ⋆ R)) m := by rw [hsp] at hm; exact sep_ac hm
      refine bn_copy_call_wp (by rw [hsubEq]; exact hnresLeOut)
        (by rw [hsubEq, List.length_drop]; dsimp [nres]; omega) hmSplit fun m1 hm1 => ?_
      rw [hsubEq] at hm1
      let out1 := (aXs.drop ws.toNat).take nres ++ outXs.drop nres
      have hout1Len : out1.length = outXs.length := by
        dsimp [out1]; simp [List.length_take, List.length_drop]; omega
      have hmRestored : (array64 out out1 ⋆ (array64 a aXs ⋆ R)) m1 := by
        have hjoin : (array64 a (aXs.take ws.toNat) ⋆
            array64 (a + 8 * ws) (aXs.drop ws.toNat) ⋆ (array64 out out1 ⋆ R)) m1 := sep_ac hm1
        rw [← sep_assoc, ← hsp] at hjoin; exact sep_ac hjoin
      have hout1Val : limbsVal (out1.take nres) =
          limbsVal (aXs.take na.toNat) >>> (64 * ws.toNat + bs.toNat) := by
        have hout1Take : out1.take nres = (aXs.drop ws.toNat).take nres := by
          dsimp [out1]; rw [List.take_append_of_le_length (by simp [List.length_drop]; omega),
            List.take_take, Nat.min_self]
        have haSplit : aXs.take na.toNat = aXs.take ws.toNat ++ (aXs.drop ws.toNat).take nres := by
          rw [show na.toNat = ws.toNat + nres by dsimp [nres]; omega, List.take_add]
        have haApp := congrArg limbsVal haSplit
        rw [limbsVal_append, List.length_take_of_le (by omega)] at haApp
        rw [hout1Take, show bs.toNat = 0 by simp [hbs0], Nat.add_zero, Nat.shiftRight_eq_div_pow,
          haApp, Nat.add_comm (limbsVal (aXs.take ws.toNat)), Nat.mul_add_div (Nat.two_pow_pos _),
          Nat.div_eq_of_lt (limbsVal_take_lt_pow aXs ws.toNat), Nat.add_zero]
      rw [← bv64_ofNat_toNat (na - ws), hsubEq]
      exact bn_trim_tail_wp hnresLt64 (by rw [hout1Len]; exact hnresLeOut) hmRestored hout1Val
        fun hLenLe hTakeEq =>
          hQ out1 m1 hout1Len (by rw [hout1Len] at hLenLe; exact hLenLe)
            hTakeEq (sep_unpick2_3 hmRestored)
    · have hbsPos : 0 < bs.toNat := by c0_bv_omega
      have hbsMod : bs.toNat % 64 = bs.toNat := Nat.mod_eq_of_lt hbs
      have hsub64Nat : (64#64 - bs).toNat = 64 - bs.toNat := by
        rw [BitVec.toNat_sub_of_le (by change bs.toNat ≤ 64; omega)]; rfl
      have hsub64Mod : (64 - bs).toNat % 64 = 64 - bs.toNat := by
        rw [show (64 : BitVec 64) - bs = 64#64 - bs from rfl, hsub64Nat]
        exact Nat.mod_eq_of_lt (by omega)
      c0_hsteps_nogrp
      refine wp_cursor_up_loop 0 (nres - 1) (by omega) (α := List (BitVec 64))
        (fun iNat outXs' mL => outXs'.length = outXs.length ∧
          (∀ j (hj : j < iNat) (hja : ws.toNat + j + 1 < aXs.length)
            (hjo : j < outXs'.length), outXs'[j]'hjo =
              ((aXs[ws.toNat + j]'(by omega)) >>> bs.toNat) |||
                ((aXs[ws.toNat + j + 1]) <<< (64 - bs.toNat))) ∧
          (array64 out outXs' ⋆ (array64 a aXs ⋆ R)) mL)
        (fun J hJ => by
          c0_hsteps
          exact hJ outXs m (Nat.zero_le _) ⟨rfl, fun _ hj _ _ => by omega, sep_pick2_3 hm⟩)
        ?_
      intro J iNat outXs' mL hiLe hiLt64 hiToNat ⟨hlenOut', hShrInv, hmL⟩ hRec
      c0_hsplit
      · have hi1Lt : iNat + 1 < nres := by c0_bv_omega
        have haLen1 : (ws + BitVec.ofNat 64 iNat).toNat < aXs.length := by c0_bv_omega
        have haLen2 : (ws + BitVec.ofNat 64 iNat + (1 : BitVec 64)).toNat < aXs.length := by
          c0_bv_omega
        have hoLen : (BitVec.ofNat 64 iNat).toNat < outXs'.length := by c0_bv_omega
        have hwsi : (ws + BitVec.ofNat 64 iNat).toNat = ws.toNat + iNat := by c0_bv_omega
        have hwsi1 : (ws + BitVec.ofNat 64 iNat + (1 : BitVec 64)).toNat = ws.toNat + iNat + 1 := by
          c0_bv_omega
        c0_hsteps
        let w := ((aXs[ws.toNat + iNat]'(by omega)) >>> bs.toNat) |||
          ((aXs[ws.toNat + iNat + 1]'(by omega)) <<< (64 - bs.toNat))
        simp only [hiToNat, hwsi, hwsi1] at hm
        rw [hbsMod, hsub64Mod] at hm
        refine hRec (outXs'.set iNat w) m (by omega)
          ⟨by simp [hlenOut'], fun j hj hja hjOut => ?_, hm⟩
        by_cases hjEq : j = iNat
        · subst hjEq; rw [List.getElem_set_self]
        · rw [List.getElem_set_ne (by omega)]
          exact hShrInv j (by omega) hja (by rw [List.length_set] at hjOut; exact hjOut)
      · have hiEqLast : iNat + 1 = nres := by c0_bv_omega
        have hresSub : (na - ws - (1 : BitVec 64)).toNat = nres - 1 := by
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hsubEq]; change 1 ≤ nres; omega),
            hsubEq]; rfl
        have hwsResSub : (ws + (na - ws) - (1 : BitVec 64)).toNat = ws.toNat + (nres - 1) := by
          rw [show ws + (na - ws) = na from by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_add, hsubEq, Nat.add_sub_of_le (Nat.le_of_lt hwsLtNa),
                Nat.mod_eq_of_lt na.isLt],
            BitVec.toNat_sub_of_le (by change 1 ≤ na.toNat; omega)]
          dsimp [nres]; omega
        have haLenL : (ws + (na - ws) - (1 : BitVec 64)).toNat < aXs.length := by
          rw [hwsResSub]; dsimp [nres] at *; omega
        have hoLenL : (na - ws - (1 : BitVec 64)).toNat < outXs'.length := by
          rw [hresSub]; omega
        c0_hsteps
        let wLast := (aXs[ws.toNat + (nres - 1)]'(by omega)) >>> bs.toNat
        simp only [hwsResSub] at hm
        rw [hresSub, hbsMod] at hm
        let out2 := outXs'.set (nres - 1) wLast
        have hout2Len : out2.length = outXs.length := by simp [out2, hlenOut']
        have hout2Val : limbsVal (out2.take nres) =
            limbsVal (aXs.take na.toNat) >>> (64 * ws.toNat + bs.toNat) := by
          refine shr_limbs_eq_of_lim aXs out2 na.toNat ws.toNat bs.toNat nres hbs hwsLtNa rfl hna
            (by rw [hout2Len]; exact hnresLeOut)
            (by dsimp [out2, wLast]; rw [List.getElem_set_self])
            fun j hj => by
              dsimp [out2]; rw [List.getElem_set_ne (by omega)]
              exact hShrInv j (by omega) (by dsimp [nres] at *; omega) (by omega)
        rw [← bv64_ofNat_toNat (na - ws), hsubEq]
        exact bn_trim_tail_wp hnresLt64 (by rw [hout2Len]; exact hnresLeOut) hm hout2Val
          fun hLenLe hTakeEq =>
            hQ out2 m hout2Len (by rw [hout2Len] at hLenLe; exact hLenLe) hTakeEq (sep_unpick2_3 hm)

/-! ## 4. Phased `bn_divmod` Helpers & `bn_divmod_wp` -/

private theorem bn_cmp_fixed_call_wp
    {rs : List Ty} {a b n : Val i64} {aXs bXs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs} {Q : Post rs} {X : XPost}
    (ha : n.toNat ≤ aXs.length) (hb : n.toNat ≤ bXs.length)
    (hm : (array64 a aXs ⋆ array64 b bXs ⋆ R) m)
    (hk : wp rtR1Env Q X (k (cmpResult64 (limbsVal (aXs.take n.toNat))
        (limbsVal (bXs.take n.toNat)), ())) m) :
    wp rtR1Env Q X (Expr.call "bn_cmp_fixed" (as := [i64, i64, i64]) (bs := [i64])
      (Arg.var a, Arg.var b, Arg.var n, ()) k) m := by
  apply wp_call_of (as := [i64, i64, i64]) (bs := [i64])
  change rtR1Env "bn_cmp_fixed" [i64, i64, i64] [i64] (a, b, n, ()) m _ X
  apply rtR1Env_bn_cmp_fixed
  exact ⟨aXs, bXs, R, ha, hb, hm, hk⟩

private theorem bv64_subb_step_eq (x y : BitVec 64) (bin bout : Bool)
    (hb : bout = true ↔ x.toNat < y.toNat + bin.toNat) :
    (x - y - BitVec.ofNat 64 bin.toNat).toNat + y.toNat + bin.toNat =
      x.toNat + bout.toNat * 2 ^ 64 := by
  have hx := x.isLt; have hy := y.isLt
  have hbin1 : bin.toNat ≤ 1 := bool_toNat_le_one bin
  have hbin : (BitVec.ofNat 64 bin.toNat).toNat = bin.toNat := bv64_bool_toNat bin
  have hlin : (x - y - BitVec.ofNat 64 bin.toNat).toNat =
      (2 * 2 ^ 64 + x.toNat - y.toNat - bin.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_sub, hbin, Nat.add_mod_mod]; congr 1; omega
  rw [hlin]
  cases hb_lt : decide (x.toNat < y.toNat + bin.toNat)
  · have hle : y.toNat + bin.toNat ≤ x.toNat := by
      simp only [decide_eq_false_iff_not] at hb_lt; omega
    have hbf : bout = false := Bool.eq_false_iff.mpr fun h => by have := hb.mp h; omega
    rw [hbf, show 2 * 2 ^ 64 + x.toNat - y.toNat - bin.toNat =
        2 ^ 64 * 2 + (x.toNat - y.toNat - bin.toNat) by omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    simp; omega
  · have hlt : x.toNat < y.toNat + bin.toNat := of_decide_eq_true hb_lt
    have hbt : bout = true := hb.mpr hlt
    rw [hbt, show 2 * 2 ^ 64 + x.toNat - y.toNat - bin.toNat =
        2 ^ 64 + (2 ^ 64 + x.toNat - y.toNat - bin.toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simp; omega

private theorem limbsVal_dvd_pow_of_low_zero (xs : List (BitVec 64)) (k n : Nat)
    (hk : k ≤ n) (hn : n ≤ xs.length) (hz : ∀ j (hj : j < k), xs[j]'(by omega) = 0#64) :
    2 ^ (64 * k) ∣ limbsVal (xs.take n) := by
  have hsplit : xs.take n = xs.take k ++ (xs.drop k).take (n - k) := by
    simpa [show k + (n - k) = n by omega] using List.take_add (l := xs) (i := k) (j := n - k)
  have hzero : limbsVal (xs.take k) = 0 := by
    refine limbsVal_zero_iff.mpr fun x hx => ?_
    rcases List.mem_iff_getElem.mp hx with ⟨j, hj, rfl⟩
    rw [List.length_take_of_le (by omega)] at hj
    rw [List.getElem_take]; exact hz j hj
  rw [hsplit, limbsVal_append, List.length_take_of_le (by omega), hzero, Nat.zero_add]
  exact Nat.dvd_mul_right _ _

private theorem nat_or_pow2_eq_add_of_pow_succ_dvd {m b : Nat} (hdvd : 2 ^ (b + 1) ∣ m) :
    m ||| (1 <<< b) = m + 2 ^ b := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]; obtain ⟨q, rfl⟩ := hdvd
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_or]
  have hbit0 : ∀ k n, (2 ^ (k + 1) * n).testBit k = false := fun k n => by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    simp
  rcases Nat.lt_trichotomy i b with hib | rfl | hib
  · obtain ⟨k, hk⟩ : ∃ k, b = i + 1 + k := ⟨b - (i + 1), by omega⟩
    rw [hk, show i + 1 + k + 1 = (i + 1) + (k + 1) by omega, Nat.pow_add 2 (i + 1) (k + 1),
      Nat.pow_add 2 (i + 1) k, Nat.mul_assoc, ← Nat.mul_add, hbit0, hbit0, hbit0]; rfl
  · have ht : (2 ^ i).testBit i = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_self (Nat.two_pow_pos _)]; simp
    rw [hbit0 i q, ht, Nat.testBit_eq_decide_div_mod_eq, Nat.pow_succ, Nat.mul_assoc,
      ← Nat.mul_add_one, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    simp
  · rw [nat_testBit_false_of_lt (Nat.pow_lt_pow_right Nat.one_lt_two hib), Bool.or_false,
      Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      show 2 ^ i = 2 ^ (b + 1) * 2 ^ (i - (b + 1)) by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)],
      ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      Nat.mul_add_div (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_succ_self b)),
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    simp

private theorem divmod_q_set_props {qHi : Nat} {qw : BitVec 64} {w' kNat : Nat}
    (hkPos : 0 < kNat) (hkLe : kNat ≤ 64)
    (hqHi : 2 ^ (64 * (w' + 1)) ∣ qHi) (hqw : 2 ^ kNat ∣ qw.toNat) :
    let k' := kNat - 1
    let pos' := 64 * w' + k'
    let qVal := qHi + 2 ^ (64 * w') * qw.toNat
    let qwNext := qw ||| (1#64 <<< k')
    2 ^ k' ∣ qwNext.toNat ∧
    qHi + 2 ^ (64 * w') * qwNext.toNat = qVal ||| (1 <<< pos') ∧
    (qVal ||| (1 <<< pos')) >>> pos' = 2 * (qVal >>> (pos' + 1)) + 1 ∧
    qVal >>> pos' = 2 * (qVal >>> (pos' + 1)) := by
  intro k' pos' qVal qwNext
  have hkEq : kNat = k' + 1 := by omega
  have hkLt64 : k' < 64 := by omega
  have h1shl : (1#64 <<< k').toNat = 2 ^ k' := by
    rw [BitVec.toNat_shiftLeft, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.shiftLeft_eq, Nat.one_mul,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right Nat.one_lt_two hkLt64)]
  have hqwDvd : 2 ^ (k' + 1) ∣ qw.toNat := hkEq ▸ hqw
  have hqwOr : qw.toNat ||| (1#64 <<< k').toNat = qw.toNat + 2 ^ k' := by
    conv => lhs; rw [h1shl, ← Nat.one_mul (2 ^ k'), ← Nat.shiftLeft_eq]
    exact nat_or_pow2_eq_add_of_pow_succ_dvd hqwDvd
  have hqwDvdNext : 2 ^ k' ∣ qwNext.toNat := by
    dsimp [qwNext]
    rw [hqwOr]
    exact Nat.dvd_add (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hqwDvd) (Nat.dvd_refl _)
  have hposDvd : 2 ^ (pos' + 1) ∣ qVal := by
    dsimp [qVal, pos']
    have h1 : 2 ^ (64 * w' + k' + 1) ∣ 2 ^ (64 * (w' + 1)) :=
      Nat.pow_dvd_pow 2 (by omega)
    refine Nat.dvd_add (Nat.dvd_trans (by simpa [Nat.add_assoc] using h1) hqHi) ?_
    rw [show 64 * w' + k' + 1 = 64 * w' + (k' + 1) by omega, Nat.pow_add]
    exact Nat.mul_dvd_mul_left _ hqwDvd
  have hqValOr : qVal ||| (1 <<< pos') = qVal + 2 ^ pos' :=
    nat_or_pow2_eq_add_of_pow_succ_dvd hposDvd
  have hqNextEq : qHi + 2 ^ (64 * w') * qwNext.toNat = qVal ||| (1 <<< pos') := by
    dsimp [qwNext, qVal, pos']
    rw [hqwOr, hqValOr, Nat.mul_add, Nat.add_assoc, ← Nat.pow_add]
  obtain ⟨qh, hqh⟩ := hposDvd
  have hdivSucc : qVal >>> (pos' + 1) = qh := by
    rw [Nat.shiftRight_eq_div_pow, hqh, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  have hdivPos : qVal >>> pos' = 2 * qh := by
    rw [Nat.shiftRight_eq_div_pow, hqh,
        show 2 ^ (pos' + 1) = 2 ^ pos' * 2 by rw [Nat.pow_succ],
        Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  have hdivAdd : (qVal ||| (1 <<< pos')) >>> pos' = 2 * qh + 1 := by
    rw [hqValOr, Nat.shiftRight_eq_div_pow, hqh,
        show 2 ^ (pos' + 1) = 2 ^ pos' * 2 by rw [Nat.pow_succ],
        Nat.mul_assoc, ← Nat.mul_add_one,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  refine ⟨hqwDvdNext, hqNextEq, ?_, ?_⟩
  · rw [hdivSucc, hdivAdd]
  · rw [hdivSucc, hdivPos]

private theorem divmod_post_sub_eq {rVal bVal inBit rShiftedVal cbit rSubVal nb : Nat} {br : Bool}
    (hr : rVal < bVal) (_hb : bVal < 2 ^ (64 * nb)) (hin : inBit ≤ 1)
    (hrShLt : rShiftedVal < 2 ^ (64 * nb)) (hcbit : cbit ≤ 1)
    (hsh : rShiftedVal + 2 ^ (64 * nb) * cbit = 2 * rVal + inBit)
    (hge : bVal ≤ 2 * rVal + inBit)
    (hrSubLt : rSubVal < 2 ^ (64 * nb))
    (hsub : rSubVal + bVal = rShiftedVal + (if br then 2 ^ (64 * nb) else 0)) :
    rSubVal = 2 * rVal + inBit - bVal := by
  by_cases hc0 : cbit = 0
  · rw [hc0, Nat.mul_zero, Nat.add_zero] at hsh
    rw [hsh] at hsub
    exact (sub_borrow_false_of_le hrSubLt hge hsub).2
  · have hc1 : cbit = 1 := by omega
    rw [hc1, Nat.mul_one] at hsh
    have hbr : br = true := by
      by_cases hbF : br = true
      · exact hbF
      · simp only [hbF, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hsub
        omega
    simp only [hbr, ↓reduceIte] at hsub
    omega

private theorem cmpResult64_sge0_iff (x y : Nat) :
    ((0#64).sle (cmpResult64 x y) = true ↔ y ≤ x) ∧
    (0 ≤ (cmpResult64 x y).toInt ↔ y ≤ x) := by
  dsimp [cmpResult64]
  by_cases hlt : x < y
  · simp only [hlt, ↓reduceIte]
    refine ⟨⟨fun h => absurd h Bool.false_ne_true, fun h => by omega⟩,
            ⟨fun h => absurd h (by decide), fun h => by omega⟩⟩
  · by_cases hgt : x > y
    · simp only [hlt, ↓reduceIte, hgt]
      refine ⟨⟨fun _ => by omega, fun _ => rfl⟩,
              ⟨fun _ => by omega, fun _ => by decide⟩⟩
    · simp only [hlt, ↓reduceIte, hgt]
      refine ⟨⟨fun _ => by omega, fun _ => rfl⟩,
              ⟨fun _ => by omega, fun _ => by decide⟩⟩

private theorem divmod_inBit_le_one (b : Bool) : (if b then 1 else 0) ≤ 1 := by
  cases b <;> simp

private theorem bn_divmod_fast1_post {a na b nb q r : BitVec 64}
    {aXs bXs qXs rXs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []}
    (hna1 : na.toNat = 1) (hnb1 : nb.toNat = 1) (ha0 : 0 < aXs.length)
    (hb0 : 0 < bXs.length) (hq0 : 0 < qXs.length) (hr0 : 0 < rXs.length)
    (hm : (array64 a aXs ⋆ array64 b bXs ⋆
      array64 q (qXs.set 0 (aXs[0] / bXs[0])) ⋆
      array64 r (rXs.set 0 (aXs[0] % bXs[0])) ⋆ R) m)
    (hQ : ∀ qXs' rXs' m', qXs'.length = qXs.length → rXs'.length = rXs.length →
      limbsVal (qXs'.take na.toNat) =
        limbsVal (aXs.take na.toNat) / limbsVal (bXs.take nb.toNat) →
      limbsVal (rXs'.take nb.toNat) =
        limbsVal (aXs.take na.toNat) % limbsVal (bXs.take nb.toNat) →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXs' ⋆ R) m' → Q () m') :
    Q () m := by
  let q1 := qXs.set 0 (aXs[0] / bXs[0])
  let r1 := rXs.set 0 (aXs[0] % bXs[0])
  have hTake1 : ∀ {xs : List (BitVec 64)} (h : 0 < xs.length),
      limbsVal (xs.take 1) = xs[0].toNat := fun {xs} h => by
    simp [list_take_succ_append h]
  have hq1Val : limbsVal (q1.take na.toNat) =
      limbsVal (aXs.take na.toNat) / limbsVal (bXs.take nb.toNat) := by
    dsimp [q1]
    rw [hna1, hnb1, hTake1 (by rw [List.length_set]; exact hq0), hTake1 ha0, hTake1 hb0,
      List.getElem_set_self, BitVec.toNat_udiv]
  have hr1Val : limbsVal (r1.take nb.toNat) =
      limbsVal (aXs.take na.toNat) % limbsVal (bXs.take nb.toNat) := by
    dsimp [r1]
    rw [hna1, hnb1, hTake1 (by rw [List.length_set]; exact hr0), hTake1 ha0, hTake1 hb0,
      List.getElem_set_self, BitVec.toNat_umod]
  exact hQ q1 r1 m (by rw [List.length_set]) (by rw [List.length_set]) hq1Val hr1Val hm

private def divmodShiftExpr (nb r inBitBv : BitVec 64)
    (exitExpr : Tup Val [i64, i64] → Expr Val Cont []) : Expr Val Cont [] :=
  Expr.group (sig := [[i64, i64]])
    (fun Js => Blocks.cons
      (fun p_16 =>
        Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool,
                    args := (Arg.var p_16.snd.fst, Arg.var nb, ()) } fun p_17 =>
        Expr.jnz (Arg.var p_17.fst)
          (Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                       args := (Arg.var p_16.snd.fst, Arg.imm 8, ()) } fun p_18 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var r, Arg.var p_18.fst, ()) } fun p_19 =>
           Expr.load i64 (Arg.var p_19.fst) fun ld =>
           Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                       args := (Arg.var p_16.snd.fst, Arg.imm 8, ()) } fun p_20 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var r, Arg.var p_20.fst, ()) } fun p =>
           Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) }
             fun p_21 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.shl i64,
                       args := (Arg.var ld, Arg.var p_21.fst, ()) } fun p_22 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.or i64,
                       args := (Arg.var p_22.fst, Arg.var p_16.fst, ()) } fun p_23 =>
           Expr.store (Arg.var p_23.fst) (Arg.var p.fst)
             (Expr.let_ { sig := [i32], code := OpCode.sext 32 64,
                          args := (Arg.imm 63, ()) } fun p =>
              Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                          args := (Arg.var ld, Arg.var p.fst, ()) } fun p =>
              Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var p_16.snd.fst, Arg.imm 1, ()) } fun p_24 =>
              Expr.jump Js.fst (Arg.var p.fst, Arg.var p_24.fst, ())))
          (exitExpr p_16))
      Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.var inBitBv, Arg.imm 0, ())

private def divmodGeExpr (b nb r cbit : BitVec 64)
    (geBody : Tup Val [Ty.bool] → Expr Val Cont []) : Expr Val Cont [] :=
  Expr.group (sig := [[Ty.bool]])
    (fun _Js => Blocks.cons geBody Blocks.nil)
    fun Js =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool,
                args := (Arg.var cbit, Arg.imm 0, ()) } fun p_18 =>
    Expr.jnz (Arg.var p_18.fst) (Expr.jump Js.fst (Arg.imm true, ()))
      (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_cmp_fixed"
        (Arg.var r, Arg.var b, Arg.var nb, ()) fun p =>
       Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) }
         fun p_19 =>
       Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.sge i64 Ty.bool,
                   args := (Arg.var p.fst, Arg.var p_19.fst, ()) } fun p =>
       Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm true, ()))
         (Expr.jump Js.fst (Arg.imm false, ())))

private def divmodSubExpr (b nb r : BitVec 64)
    (exitExpr : Tup Val [Ty.bool, i64] → Expr Val Cont []) : Expr Val Cont [] :=
  Expr.group (sig := [[Ty.bool, i64]])
    (fun Js_2 => Blocks.cons
      (fun p_19 =>
        Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool,
                    args := (Arg.var p_19.snd.fst, Arg.var nb, ()) } fun p_20 =>
        Expr.jnz (Arg.var p_20.fst)
          (Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                       args := (Arg.var p_19.snd.fst, Arg.imm 8, ()) } fun p_21 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var r, Arg.var p_21.fst, ()) } fun p_22 =>
           Expr.load i64 (Arg.var p_22.fst) fun ld =>
           Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                       args := (Arg.var p_19.snd.fst, Arg.imm 8, ()) } fun p_23 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var b, Arg.var p_23.fst, ()) } fun p_24 =>
           Expr.load i64 (Arg.var p_24.fst) fun ld_1 =>
           Expr.let_ { sig := [i64, i64, Ty.bool], code := OpCode.subb 64,
                       args := (Arg.var ld, Arg.var ld_1, Arg.var p_19.fst, ()) } fun p_25 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                       args := (Arg.var p_19.snd.fst, Arg.imm 8, ()) } fun p_26 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var r, Arg.var p_26.fst, ()) } fun p =>
           Expr.store (Arg.var p_25.fst) (Arg.var p.fst)
             (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var p_19.snd.fst, Arg.imm 1, ()) } fun p =>
              Expr.jump Js_2.fst (Arg.var p_25.snd.fst, Arg.var p.fst, ())))
          (exitExpr p_19))
      Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm false, Arg.imm 0, ())

private def divmodWordLoopExpr (a na b nb q r : BitVec 64) : Expr Val Cont [] :=
  Expr.group (sig := [[i64]])
    (fun Js =>
      Blocks.cons
        (fun p_6 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                      args := (Arg.var p_6.fst, Arg.imm 0, ()) } fun p_7 =>
          Expr.jnz (Arg.var p_7.fst)
            (Expr.let_ { sig := [i64, i64], code := OpCode.sub i64,
                         args := (Arg.var p_6.fst, Arg.imm 1, ()) } fun p_8 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p_8.fst, Arg.imm 8, ()) } fun p_9 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var a, Arg.var p_9.fst, ()) } fun p_10 =>
             Expr.load i64 (Arg.var p_10.fst) fun ld =>
             Expr.group (sig := [[i64, i64]])
               (fun Js_1 =>
                 Blocks.cons
                   (fun p_11 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                                 args := (Arg.var p_11.snd.fst, Arg.imm 0, ()) } fun p_12 =>
                     Expr.jnz (Arg.var p_12.fst)
                       (Expr.let_ { sig := [i64, i64], code := OpCode.sub i64,
                                    args := (Arg.var p_11.snd.fst, Arg.imm 1, ()) } fun p_13 =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                                    args := (Arg.var ld, Arg.var p_13.fst, ()) } fun p_14 =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.and i64,
                                    args := (Arg.var p_14.fst, Arg.imm 1, ()) } fun p_15 =>
                        divmodShiftExpr nb r p_15.fst fun p_16 =>
                          divmodGeExpr b nb r p_16.fst fun p_18 =>
                            Expr.group (sig := [[i64]])
                              (fun Js_k =>
                                Blocks.cons
                                  (fun p => Expr.jump Js_1.fst (Arg.var p.fst, Arg.var p_13.fst,
                                    ()))
                                  Blocks.nil)
                              fun Js_k =>
                              Expr.jnz (Arg.var p_18.fst)
                                (divmodSubExpr b nb r fun _ =>
                                  Expr.let_ { sig := [i64, i64], code := OpCode.shl i64,
                                              args := (Arg.imm 1, Arg.var p_13.fst, ()) } fun p =>
                                  Expr.let_ { sig := [i64, i64], code := OpCode.or i64,
                                              args := (Arg.var p_11.fst, Arg.var p.fst, ()) }
                                    fun p =>
                                  Expr.jump Js_k.fst (Arg.var p.fst, ()))
                                (Expr.jump Js_k.fst (Arg.var p_11.fst, ())))
                       (Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                    args := (Arg.var p_8.fst, Arg.imm 8, ()) } fun p_13 =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var q, Arg.var p_13.fst, ()) } fun p =>
                        Expr.store (Arg.var p_11.fst) (Arg.var p.fst)
                          (Expr.jump Js.fst (Arg.var p_8.fst, ()))))
                   Blocks.nil)
               fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, Arg.imm 64, ()))
            (Expr.ret ()))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.var na, ())

private theorem bn_divmod_shift_loop_wp
    {Q : Post []} {X : XPost} {a b q r nb inBitBv : BitVec 64}
    {aXs bXs qXs' rXs rXs'' : List (BitVec 64)} {R : Mem 64 → Prop} {mK : Mem 64}
    {exitExpr : Tup Val [i64, i64] → Expr Val Cont []}
    (_hnb : nb.toNat ≤ bXs.length) (hrLen' : rXs''.length = rXs.length)
    (hnr : nb.toNat ≤ rXs.length) (hinBitLt2 : inBitBv.toNat < 2)
    (hmK : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXs'' ⋆ R) mK)
    (hk : ∀ cbit rCur mS,
      rCur.length = rXs.length → cbit.toNat < 2 →
      limbsVal (rCur.take nb.toNat) + 2 ^ (64 * nb.toNat) * cbit.toNat =
        2 * limbsVal (rXs''.take nb.toNat) + inBitBv.toNat →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rCur ⋆ R) mS →
      wp rtR1Env Q X (exitExpr (cbit, nb, ())) mS) :
    wp rtR1Env Q X (divmodShiftExpr nb r inBitBv exitExpr) mK := by
  dsimp only [divmodShiftExpr]
  refine wp_pair_up_loop 0 nb.toNat nb.isLt (t0 := i64) (α := List (BitVec 64))
    (fun jNat cbit rCur mS =>
      rCur.length = rXs.length ∧ cbit.toNat < 2 ∧
      (∀ i (_hi1 : jNat ≤ i) (_hi2 : i < nb.toNat)
        (hir : i < rCur.length) (hi2r : i < rXs''.length), rCur[i]'hir = rXs''[i]'hi2r) ∧
      limbsVal (rCur.take jNat) + 2 ^ (64 * jNat) * cbit.toNat =
        2 * limbsVal ((rXs''.take nb.toNat).take jNat) + inBitBv.toNat ∧
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rCur ⋆ R) mS)
    (fun Js hJs => by
      c0_hsteps_nogrp
      exact hJs inBitBv rXs'' mK (Nat.zero_le _)
        ⟨hrLen', hinBitLt2, fun _ _ _ _ _ => rfl, by simp, hmK⟩)
    ?_
  intro Js jNat cbit rCur mS hjLe hjLt64 hjToNat ⟨hrLenS, hcLt, hrRem, hShInv, hmS⟩ hRecS
  c0_hsplit
  · have hjLtNb : jNat < nb.toNat := by c0_bv_omega
    let rj := rXs''[jNat]'(by omega)
    have hrjEq : rCur[jNat]'(by omega) = rj :=
      hrRem jNat (le_refl _) hjLtNb (by omega) (by omega)
    let rjNext := (rj <<< 1) ||| cbit
    let cNext := rj >>> 63
    have hstep := shl_step_nat rj 1#64 cbit nat_lt_1_64 (by simpa using hcLt)
    rw [show (64#64 - 1#64 : BitVec 64) = 63#64 from rfl] at hstep
    have hcNextLt : cNext.toNat < 2 := by simpa [cNext] using hstep.2
    have hoLenS : (BitVec.ofNat 64 jNat).toNat < rCur.length := by rw [hjToNat]; omega
    c0_hsteps
    simp only [hjToNat, hrjEq] at hm ⊢
    have hmS' : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆
        array64 r (rCur.set jNat rjNext) ⋆ R) m := by
      have hm2 : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆
          array64 r (rCur.set jNat (cbit ||| rj <<< 1)) ⋆ R) m := sep_ac hm
      rwa [BitVec.or_comm cbit (rj <<< 1)] at hm2
    refine hRecS cNext (rCur.set jNat rjNext) m hjLtNb ⟨by simp [hrLenS], hcNextLt,
      fun i hi1 hi2 hir hi2r => by
        rw [List.getElem_set_ne (by omega)]; exact hrRem i (by omega) hi2 _ _,
      ?_, hmS'⟩
    rw [limbsVal_take_set_succ rCur rjNext (by omega)]
    have hrTakeNext := limbsVal_take_succ (xs := rXs''.take nb.toNat)
      (i := jNat) (by rw [List.length_take_of_le (by omega)]; exact hjLtNb)
    rw [List.getElem_take] at hrTakeNext; rw [hrTakeNext]
    have hstep1 : rjNext.toNat + 2 ^ 64 * cNext.toNat = rj.toNat * 2 + cbit.toNat := by
      simpa [rjNext, cNext] using hstep.1
    have hpow : 2 ^ (64 * jNat) * 2 ^ 64 = 2 ^ (64 * (jNat + 1)) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have h1 : 2 ^ (64 * jNat) * (rjNext.toNat + 2 ^ 64 * cNext.toNat) =
        2 ^ (64 * jNat) * rjNext.toNat + 2 ^ (64 * (jNat + 1)) * cNext.toNat := by
      rw [Nat.mul_add, ← Nat.mul_assoc, hpow]
    have h2 : 2 ^ (64 * jNat) * (rj.toNat * 2 + cbit.toNat) =
        2 * (2 ^ (64 * jNat) * rj.toNat) + 2 ^ (64 * jNat) * cbit.toNat := by
      rw [Nat.mul_add, Nat.mul_comm rj.toNat 2, ← Nat.mul_assoc,
        Nat.mul_comm (2 ^ (64 * jNat)) 2, Nat.mul_assoc]
    have hz : 2 ^ (64 * jNat) * rjNext.toNat + 2 ^ (64 * (jNat + 1)) * cNext.toNat =
        2 * (2 ^ (64 * jNat) * rj.toNat) + 2 ^ (64 * jNat) * cbit.toNat := by
      rw [← h1, ← h2, hstep1]
    dsimp only [rj] at hz; rw [Nat.mul_add 2]; omega
  · have hjEqNb : jNat = nb.toNat := by c0_bv_omega
    subst hjEqNb
    rw [List.take_take, Nat.min_self] at hShInv
    rw [bv64_ofNat_toNat]
    exact hk cbit rCur mS hrLenS hcLt hShInv hmS

private theorem bn_divmod_ge_check_wp
    {Q : Post []} {X : XPost} {a b q r nb cbit : BitVec 64}
    {aXs bXs qXs' rCur : List (BitVec 64)} {R : Mem 64 → Prop} {mS : Mem 64}
    {bVal rShVal rValOld inBit : Nat}
    {geBody : Tup Val [Ty.bool] → Expr Val Cont []}
    (hrCur : nb.toNat ≤ rCur.length) (hnb : nb.toNat ≤ bXs.length)
    (hbVal : bVal = limbsVal (bXs.take nb.toNat))
    (hrShVal : rShVal = limbsVal (rCur.take nb.toNat))
    (hcLt : cbit.toNat < 2)
    (hbLtPow : bVal < 2 ^ (64 * nb.toNat))
    (hrShEq : rShVal + 2 ^ (64 * nb.toNat) * cbit.toNat = 2 * rValOld + inBit)
    (hmS : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rCur ⋆ R) mS)
    (hgeBody : ∀ ge, ge = decide (bVal ≤ 2 * rValOld + inBit) →
      wp rtR1Env Q X (geBody (ge, ())) mS) :
    wp rtR1Env Q X (divmodGeExpr b nb r cbit geBody) mS := by
  let rPrime := 2 * rValOld + inBit
  dsimp only [divmodGeExpr]
  refine LeanQbe.T.wp_join_group
    (fun (ge, ()) mG => ge = decide (bVal ≤ rPrime) ∧ mG = mS)
    (fun _ ⟨geB, ⟨⟩⟩ mG ⟨hgeEq, hmG⟩ => by
      simp only [Blocks.get]
      subst hgeEq hmG
      exact hgeBody (decide (bVal ≤ rPrime)) rfl)
    ?_
  intro Jge hJge
  c0_hsplit
  · have hcbit1 : cbit.toNat = 1 := by
      by_cases hz : cbit.toNat = 0
      · have hc0 : cbit = 0#64 := BitVec.eq_of_toNat_eq hz
        first
          | exact False.elim ((by assumption : cbit ≠ 0#64) hc0)
          | (have h : (cbit != 0#64) = true := by assumption
             rw [hc0] at h; exact absurd h Bool.false_ne_true)
      · omega
    have hgeTrue : bVal ≤ rPrime := by
      dsimp only [rPrime]; rw [← hrShEq, hcbit1, Nat.mul_one]; omega
    c0_hsteps; try rw [wp_jump]
    exact hJge (true, ()) mS ⟨(decide_eq_true hgeTrue).symm, rfl⟩
  · have hcbit0 : cbit.toNat = 0 := by c0_bv_omega
    rw [hcbit0, Nat.mul_zero, Nat.add_zero] at hrShEq
    have hrShEq' : rShVal = rPrime := hrShEq
    have hmCmp : (array64 r rCur ⋆ array64 b bXs ⋆
        (array64 a aXs ⋆ array64 q qXs' ⋆ R)) mS := sep_ac hmS
    refine bn_cmp_fixed_call_wp hrCur hnb hmCmp ?_
    c0_hsplit
    · have hc : (0#64).sle (cmpResult64 (limbsVal (rCur.take nb.toNat))
          (limbsVal (bXs.take nb.toNat))) = true := by assumption
      rw [← hbVal, ← hrShVal, (cmpResult64_sge0_iff _ _).1] at hc
      have hcmpTrue : bVal ≤ rPrime := by rwa [hrShEq'] at hc
      c0_hsteps; try rw [wp_jump]
      exact hJge (true, ()) mS ⟨(decide_eq_true hcmpTrue).symm, rfl⟩
    · have hcmpFalse : ¬ (bVal ≤ rPrime) := by
        rw [← hrShEq', ← (cmpResult64_sge0_iff rShVal bVal).1, hbVal, hrShVal]
        first
          | (intro ht; contradiction)
          | (intro ht
             have hf : (0#64).sle (cmpResult64 (limbsVal (rCur.take nb.toNat))
               (limbsVal (bXs.take nb.toNat))) = false := by assumption
             rw [ht] at hf; cases hf)
      c0_hsteps; try rw [wp_jump]
      exact hJge (false, ()) mS ⟨(decide_eq_false hcmpFalse).symm, rfl⟩

private theorem bn_divmod_sub_loop_wp
    {Q : Post []} {X : XPost} {a b q r nb : BitVec 64}
    {aXs bXs qXs' rCur rXs : List (BitVec 64)} {R : Mem 64 → Prop} {mG : Mem 64}
    {exitExpr : Tup Val [Ty.bool, i64] → Expr Val Cont []}
    (hnb : nb.toNat ≤ bXs.length) (hrLenS : rCur.length = rXs.length)
    (hnr : nb.toNat ≤ rXs.length)
    (hmG : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rCur ⋆ R) mG)
    (hk : ∀ br rSub mSub,
      rSub.length = rXs.length →
      limbsVal (rSub.take nb.toNat) + limbsVal (bXs.take nb.toNat) =
        limbsVal (rCur.take nb.toNat) + (if br then 2 ^ (64 * nb.toNat) else 0) →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rSub ⋆ R) mSub →
      wp rtR1Env Q X (exitExpr (br, nb, ())) mSub) :
    wp rtR1Env Q X (divmodSubExpr b nb r exitExpr) mG := by
  dsimp only [divmodSubExpr]
  refine wp_pair_up_loop 0 nb.toNat nb.isLt (t0 := Ty.bool) (α := List (BitVec 64))
    (fun jjNat br rSub mSub =>
      rSub.length = rXs.length ∧
      limbsVal (rSub.take jjNat) + limbsVal (bXs.take jjNat) =
        limbsVal (rCur.take jjNat) + (if br then 1 else 0) * 2 ^ (64 * jjNat) ∧
      (∀ i (_hi1 : jjNat ≤ i) (_hi2 : i < nb.toNat)
        (hir : i < rSub.length) (hic : i < rCur.length), rSub[i]'hir = rCur[i]'hic) ∧
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rSub ⋆ R) mSub)
    (fun Jsub hJsub => by
      c0_hsteps
      exact hJsub false rCur mG (Nat.zero_le _) ⟨hrLenS, by simp, fun _ _ _ _ _ => rfl, hmG⟩)
    ?_
  intro Jsub jjNat br rSub mSub hjjLe hjjLt64 hjjToNat ⟨hrLenSub, hSubInv, hrSubRem, hmSub⟩ hRecSub
  c0_hsplit
  · have hjjLtNb : jjNat < nb.toNat := by
      first
        | (have hc : (BitVec.ofNat 64 jjNat).toNat < nb.toNat := by assumption
           rwa [hjjToNat] at hc)
        | (have hc : jjNat % 2 ^ 64 < nb.toNat := by assumption
           rwa [Nat.mod_eq_of_lt hjjLt64] at hc)
    let rCurJ := rCur[jjNat]'(by omega)
    let bj := bXs[jjNat]'(by omega)
    have hrSubJ : rSub[jjNat]'(by omega) = rCurJ :=
      hrSubRem jjNat (le_refl _) hjjLtNb (by omega) (by omega)
    have hrl : (BitVec.ofNat 64 jjNat).toNat < rSub.length := by rw [hjjToNat]; omega
    have hbl : (BitVec.ofNat 64 jjNat).toNat < bXs.length := by rw [hjjToNat]; omega
    c0_hsteps
    simp only [hjjToNat, hrSubJ] at hm ⊢
    refine hRecSub _ (rSub.set jjNat (rCurJ - bj - BitVec.ofNat 64 br.toNat)) m hjjLtNb
      ⟨by simp [hrLenSub], ?_, fun i hi1 hi2 hir hic => by
        rw [List.getElem_set_ne (by omega)]; exact hrSubRem i (by omega) hi2 _ _, sep_ac hm⟩
    rw [limbsVal_take_set_succ rSub _ (by omega),
      limbsVal_take_succ (Nat.lt_of_lt_of_le hjjLtNb hnb), limbsVal_take_succ (by omega)]
    exact subb_limbs_step hSubInv (bv64_subb_step_eq rCurJ bj br _ decide_eq_true_iff)
  · have hjjEqNb : jjNat = nb.toNat := by
      have hnot : ¬ jjNat < nb.toNat := by
        first
          | (have hc : ¬ (BitVec.ofNat 64 jjNat).toNat < nb.toNat := by assumption
             rwa [hjjToNat] at hc)
          | (have hc : ¬ jjNat % 2 ^ 64 < nb.toNat := by assumption
             rwa [Nat.mod_eq_of_lt hjjLt64] at hc)
      omega
    subst hjjEqNb
    have hsubClean : limbsVal (rSub.take nb.toNat) + limbsVal (bXs.take nb.toNat) =
        limbsVal (rCur.take nb.toNat) + (if br then 2 ^ (64 * nb.toNat) else 0) := by
      rw [hSubInv]; cases br <;> simp
    rw [bv64_ofNat_toNat]
    exact hk br rSub mSub hrLenSub hsubClean hmSub

private theorem bn_divmod_word_loop_wp
    {Q : Post []} {X : XPost} {a na b nb q r : BitVec 64}
    {aXs bXs qXs rXs qInit rInit : List (BitVec 64)} {R : Mem 64 → Prop} {m0 : Mem 64}
    {aVal bVal : Nat}
    (haVal : aVal = limbsVal (aXs.take na.toNat))
    (hbVal : bVal = limbsVal (bXs.take nb.toNat))
    (hna : na.toNat ≤ aXs.length) (hnb : nb.toNat ≤ bXs.length)
    (hnq : na.toNat ≤ qXs.length) (hnr : nb.toNat ≤ rXs.length)
    (hbPos : 0 < bVal) (hbLtPow : bVal < 2 ^ (64 * nb.toNat)) (haLtPow : aVal < 2 ^ (64 * na.toNat))
    (hqInitLen : qInit.length = qXs.length) (hrInitLen : rInit.length = rXs.length)
    (hqInitZero : ∀ j (_hj : j < na.toNat) (hjq : j < qInit.length), qInit[j]'hjq = 0#64)
    (hqInitVal : limbsVal (qInit.take na.toNat) = 0)
    (hrInitZero : limbsVal (rInit.take nb.toNat) = 0)
    (hm0 : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qInit ⋆ array64 r rInit ⋆ R) m0)
    (hQ : ∀ qXs' rXs' m', qXs'.length = qXs.length → rXs'.length = rXs.length →
      limbsVal (qXs'.take na.toNat) =
        limbsVal (aXs.take na.toNat) / limbsVal (bXs.take nb.toNat) →
      limbsVal (rXs'.take nb.toNat) =
        limbsVal (aXs.take na.toNat) % limbsVal (bXs.take nb.toNat) →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXs' ⋆ R) m' → Q () m') :
    wp rtR1Env Q X (divmodWordLoopExpr a na b nb q r) m0 := by
  dsimp only [divmodWordLoopExpr]
  refine wp_cursor_down_loop na.toNat na.isLt (α := List (BitVec 64) × List (BitVec 64))
    (fun wNat ⟨qXs', rXs'⟩ mW =>
      qXs'.length = qXs.length ∧ rXs'.length = rXs.length ∧
      (∀ j (_hj : j < wNat) (hjq : j < qXs'.length), qXs'[j]'hjq = 0#64) ∧
      limbsVal (rXs'.take nb.toNat) < bVal ∧
      aVal >>> (64 * wNat) = (limbsVal (qXs'.take na.toNat) >>> (64 * wNat)) * bVal +
        limbsVal (rXs'.take nb.toNat) ∧
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXs' ⋆ R) mW)
    (fun Jw hJw => by
      c0_hsteps
      rw [← bv64_ofNat_toNat na]
      refine hJw (qInit, rInit) m0 ⟨hqInitLen, hrInitLen, hqInitZero,
        by rw [hrInitZero]; exact hbPos, ?_, hm0⟩
      rw [hqInitVal, hrInitZero, Nat.zero_shiftRight, Nat.zero_mul, Nat.zero_add,
        Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt haLtPow])
    ?_
  intro Jw wNat ⟨qXs', rXs'⟩ mW hwLe hwLt64 hwToNat
    ⟨hqLen, hrLen, hqZero, hrLt, hOuterInv, hmW⟩ hRecW
  c0_hsplit
  · have hwPos : 0 < wNat := by c0_bv_omega
    let w' := wNat - 1; let aw := aXs[w']'(by omega)
    have hw1ToNat : (BitVec.ofNat 64 wNat - (1 : BitVec 64)).toNat = w' := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwToNat]; change 1 ≤ wNat; omega),
        hwToNat]; rfl
    have hqZeroW' : qXs'[w']'(by omega) = 0#64 := hqZero w' (by omega) (by omega)
    have hqDvd : 2 ^ (64 * (w' + 1)) ∣ limbsVal (qXs'.take na.toNat) :=
      limbsVal_dvd_pow_of_low_zero qXs' (w' + 1) na.toNat (by omega) (by omega)
        fun j hj => hqZero j (by omega) (by omega)
    have haLenW' : (BitVec.ofNat 64 wNat - (1 : BitVec 64)).toNat < aXs.length := by
      rw [hw1ToNat]; omega
    c0_hsteps_nogrp
    refine wp_pair_down_loop 64 nat_lt_64_pow64 (t0 := i64) (α := List (BitVec 64))
      (fun kNat qw rXs'' mK =>
        rXs''.length = rXs.length ∧ 2 ^ kNat ∣ qw.toNat ∧
        limbsVal (rXs''.take nb.toNat) < bVal ∧
        aVal >>> (64 * w' + kNat) =
          ((limbsVal (qXs'.take na.toNat) + 2 ^ (64 * w') * qw.toNat) >>> (64 * w' + kNat)) *
            bVal + limbsVal (rXs''.take nb.toNat) ∧
        (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXs'' ⋆ R) mK)
      (fun Jk hJk => by
        c0_hsteps
        refine hJk 0#64 rXs' mW ⟨hrLen, Nat.dvd_zero _, hrLt, ?_, hmW⟩
        rw [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
          show 64 * w' + 64 = 64 * wNat by omega]
        exact hOuterInv)
      ?_
    intro Jk kNat qw0 rXs'' mK hkLe hkLt64 hkToNat
      ⟨hrLen', hqwDvd, hrLtK, hInnerInv, hmK⟩ hRecK
    c0_hsplit
    · have hkPos : 0 < kNat := by c0_bv_omega
      let k' := kNat - 1; let pos' := 64 * w' + k'; let inBitBv := (aw >>> k') &&& 1#64
      let inBit := if aVal.testBit pos' then 1 else 0
      have hk1ToNat : (BitVec.ofNat 64 kNat - (1 : BitVec 64)).toNat = k' := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hkToNat]; change 1 ≤ kNat; omega),
          hkToNat]; rfl
      have hkMod64 : (BitVec.ofNat 64 kNat - (1 : BitVec 64)).toNat % 64 = k' := by
        rw [hk1ToNat]; exact Nat.mod_eq_of_lt (by omega)
      have hinBitEq : inBitBv.toNat = inBit := by
        have hawTest : aVal.testBit pos' = aw.toNat.testBit k' := by
          rw [haVal]
          dsimp [pos', aw]
          have hdiv : (64 * w' + k') / 64 = w' := by omega
          have hmod : (64 * w' + k') % 64 = k' := by omega
          simp only [limbsVal_testBit, List.length_take_of_le hna, hdiv, hmod,
            show w' < na.toNat by omega, ↓reduceDIte, List.getElem_take]
        dsimp [inBitBv, inBit]
        rw [hawTest, Nat.and_one_is_mod, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.mod_two_eq_zero_or_one (aw.toNat / 2 ^ k') with hmod | hmod <;> simp [hmod]
      have hinBitLt2 : inBitBv.toNat < 2 := by
        rw [hinBitEq]; dsimp [inBit]; cases aVal.testBit pos' <;> simp
      c0_hsteps_nogrp
      dsimp only [lift2, Arg.val]
      simp only [hw1ToNat, hkMod64]
      refine bn_divmod_shift_loop_wp hnb hrLen' hnr hinBitLt2 hmK
        fun cbit rCur mS hrLenS hcLt hShInv hmS => ?_
      dsimp only
      let rShVal := limbsVal (rCur.take nb.toNat)
      let rValOld := limbsVal (rXs''.take nb.toNat); let rPrime := 2 * rValOld + inBit
      have hrShEq : rShVal + 2 ^ (64 * nb.toNat) * cbit.toNat = rPrime := by
        dsimp [rShVal, rValOld, rPrime]; rwa [← hinBitEq]
      have hrShLtPow : rShVal < 2 ^ (64 * nb.toNat) := by
        have h := limbsVal_lt_pow (rCur.take nb.toNat)
        rwa [List.length_take_of_le (by omega)] at h
      refine bn_divmod_ge_check_wp (by omega) hnb hbVal rfl hcLt hbLtPow hrShEq hmS
        fun geB hgeEq => ?_
      subst hgeEq
      let qVal := limbsVal (qXs'.take na.toNat) + 2 ^ (64 * w') * qw0.toNat
      have hinvPos : aVal >>> (pos' + 1) = (qVal >>> (pos' + 1)) * bVal + rValOld := by
        simpa [qVal, rValOld, show 64 * w' + kNat = pos' + 1 by dsimp [pos', k']; omega]
          using hInnerInv
      refine LeanQbe.T.wp_join_group
        (fun (ys : Tup Val [i64]) mN =>
          ∃ (qwN : BitVec 64) (rXsN : List (BitVec 64)), rXsN.length = rXs.length ∧
            ys.1 = qwN ∧ 2 ^ k' ∣ qwN.toNat ∧ limbsVal (rXsN.take nb.toNat) < bVal ∧
            aVal >>> pos' = ((limbsVal (qXs'.take na.toNat) + 2 ^ (64 * w') * qwN.toNat) >>>
              pos') * bVal + limbsVal (rXsN.take nb.toNat) ∧
            (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXsN ⋆ R) mN)
        (fun _ ⟨qwNBv, ⟨⟩⟩ mN ⟨qwN, rXsN, hrLenN, hqwN, hqwNDvd, hrNLt, hInvN, hmN⟩ => by
          dsimp only [Blocks.get] at hqwN ⊢; subst qwNBv
          c0_hsteps
          exact hRecK k' qwN rXsN mN (by omega) ⟨hrLenN, hqwNDvd, hrNLt, hInvN, hmN⟩)
        ?_
      intro JkN hJkN
      have hqProps := divmod_q_set_props hkPos hkLe hqDvd hqwDvd; dsimp only at hqProps
      rcases hqProps with ⟨hqwNextDvd, hqNextOr, hqNextShr, hqShr⟩
      have hdm := divmod_bit_step hrLtK hinvPos; dsimp only at hdm
      c0_hsplit
      · have hgeTrue : bVal ≤ rPrime := by
          first | exact of_decide_eq_true (by assumption) | assumption
        c0_hsteps_nogrp
        refine bn_divmod_sub_loop_wp hnb hrLenS hnr hmS
          fun br rSub mSub hrLenSub hSubEq hmSub => ?_
        have hrSubLtPow : limbsVal (rSub.take nb.toNat) < 2 ^ (64 * nb.toNat) := by
          have h := limbsVal_lt_pow (rSub.take nb.toNat)
          rwa [List.length_take_of_le (by omega)] at h
        have hsubClean : limbsVal (rSub.take nb.toNat) + bVal =
            rShVal + (if br then 2 ^ (64 * nb.toNat) else 0) := by
          dsimp [rShVal]; rw [hbVal]; exact hSubEq
        have hrSubEq : limbsVal (rSub.take nb.toNat) = rPrime - bVal :=
          divmod_post_sub_eq hrLtK hbLtPow (divmod_inBit_le_one _)
            hrShLtPow (by omega) hrShEq hgeTrue hrSubLtPow hsubClean
        have hrSubLtB : limbsVal (rSub.take nb.toNat) < bVal := by
          rw [hrSubEq]; dsimp [rPrime]
          have : inBit ≤ 1 := divmod_inBit_le_one _
          omega
        have hdecT : decide (bVal ≤ 2 * rValOld + inBit) = true := decide_eq_true hgeTrue
        dsimp only [rValOld, inBit] at hdecT
        simp only [hdecT, ↓reduceIte] at hdm
        have hqwNextEq : (qw0 ||| (1 : BitVec 64) <<<
            ((BitVec.ofNat 64 kNat - 1).toNat % 64)) = qw0 ||| (1#64 <<< k') := by
          rw [hkMod64]; rfl
        c0_hsteps; rw [hqwNextEq]
        refine hJkN (qw0 ||| (1#64 <<< k'), ()) mSub
          ⟨qw0 ||| (1#64 <<< k'), rSub, hrLenSub, rfl, hqwNextDvd, hrSubLtB, ?_, hmSub⟩
        rw [hqNextOr, hrSubEq]; exact (hdm hqNextShr).1
      · have hgeFalse : ¬ (bVal ≤ rPrime) := by
          first
            | exact of_decide_eq_false (by assumption)
            | (have hc : ¬ decide (bVal ≤ rPrime) = true := by assumption
               exact fun h => hc (decide_eq_true h))
            | assumption
        have hdecF : decide (bVal ≤ 2 * rValOld + inBit) = false := decide_eq_false hgeFalse
        dsimp only [rValOld, inBit] at hdecF
        simp only [hdecF, Bool.false_eq_true, ↓reduceIte] at hdm
        have hc0 : cbit.toNat = 0 := by
          by_cases hz : cbit.toNat = 0
          · exact hz
          · have h1 : cbit.toNat = 1 := by omega
            rw [h1, Nat.mul_one] at hrShEq; omega
        have hrShEq' : limbsVal (rCur.take nb.toNat) = rPrime := by
          dsimp [rShVal] at hrShEq
          rw [hc0, Nat.mul_zero, Nat.add_zero] at hrShEq; exact hrShEq
        c0_hsteps
        refine hJkN (qw0, ()) mS ⟨qw0, rCur, hrLenS, rfl,
          Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hqwDvd,
          by rw [hrShEq']; dsimp [rPrime]; omega, ?_, hmS⟩
        rw [hrShEq']; exact (hdm hqShr).1
    · have hk0 : kNat = 0 := by
        have hc : ¬ 0 < kNat % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hkLt64] at hc; omega
      subst hk0
      have hqLenW' : (BitVec.ofNat 64 wNat - (1 : BitVec 64)).toNat < qXs'.length := by
        rw [hw1ToNat]; omega
      c0_hsteps; try rw [wp_jump]
      simp only [hw1ToNat] at hm
      refine hRecW w' (qXs'.set w' qw0, rXs'') m (by omega)
        ⟨by simp [hqLen], hrLen', fun j hj _ => by
          rw [List.getElem_set_ne (by omega)]; exact hqZero j (by omega) (by omega),
          hrLtK, ?_, sep_ac hm⟩
      have hqTakeSet : limbsVal ((qXs'.set w' qw0).take na.toNat) =
          limbsVal (qXs'.take na.toNat) + 2 ^ (64 * w') * qw0.toNat := by
        have h := limbsVal_take_set_of_lt qXs' qw0 (p := w') (M := na.toNat)
          (by omega) (by omega)
        rw [hqZeroW'] at h; simpa [Nat.mul_zero, Nat.add_zero] using h
      rwa [← hqTakeSet, show 64 * w' + 0 = 64 * w' from Nat.add_zero _] at hInnerInv
  · have hw0 : wNat = 0 := by
      have hc : ¬ 0 < wNat % 2 ^ 64 := by assumption
      rw [Nat.mod_eq_of_lt hwLt64] at hc; omega
    subst hw0
    rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftRight_zero] at hOuterInv
    have hqDiv : limbsVal (qXs'.take na.toNat) = aVal / bVal := by
      rw [hOuterInv, Nat.add_comm (limbsVal (qXs'.take na.toNat) * bVal),
        Nat.add_mul_div_right _ _ hbPos, Nat.div_eq_of_lt hrLt, Nat.zero_add]
    have hrMod : limbsVal (rXs'.take nb.toNat) = aVal % bVal := by
      rw [hOuterInv, Nat.add_comm (limbsVal (qXs'.take na.toNat) * bVal),
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrLt]
    c0_hsteps; try rw [wp_ret]
    rw [haVal, hbVal] at hqDiv hrMod
    exact hQ qXs' rXs' mW hqLen hrLen hqDiv hrMod hmW

theorem bn_divmod_wp :
    ∀ xs m Q X, bnDivModSpec xs m Q X → Func.wp rtR1Env bn_divmod.body xs m Q X := by
  intro ⟨a, na, b, nb, q, r, ⟨⟩⟩ m Q X
    ⟨aXs, bXs, qXs, rXs, R, hnaPos, hnbPos, hna, hnb, hnq, hnr, hbLast, hm, hQ⟩
  let aVal := limbsVal (aXs.take na.toNat); let bVal := limbsVal (bXs.take nb.toNat)
  have hbTakeNe : bXs.take nb.toNat ≠ [] := fun h => by
    have hlen := congrArg List.length h; simp [List.length_take_of_le hnb] at hlen; omega
  have hbTakeLast : (bXs.take nb.toNat).getLast hbTakeNe ≠ 0#64 := by
    rw [List.getLast_eq_getElem]
    have hlen : (bXs.take nb.toNat).length = nb.toNat := List.length_take_of_le hnb
    simp only [hlen, List.getElem_take]
    have h0 : bXs[nb.toNat - 1]! = bXs[nb.toNat - 1]'(by omega) := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [← h0]; exact hbLast
  have hbPos : 0 < bVal := Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
    (limbsVal_ge_pow_of_nonzero_last hbTakeNe hbTakeLast)
  have hbLtPow : bVal < 2 ^ (64 * nb.toNat) := by
    simpa [List.length_take_of_le hnb] using limbsVal_lt_pow (bXs.take nb.toNat)
  have haLtPow : aVal < 2 ^ (64 * na.toNat) := by
    simpa [List.length_take_of_le hna] using limbsVal_lt_pow (aXs.take na.toNat)
  dsimp only [Func.wp, bn_divmod, bn_divmod_body]
  c0_hsplit
  · have : na.toNat = 0 := by c0_bv_omega
    omega
  c0_hsplit
  · have : nb.toNat = 0 := by c0_bv_omega
    omega
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_join_group
    (fun _ mJ => (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs ⋆ array64 r rXs ⋆ R) mJ) ?_ ?_
  · intro Js ⟨⟩ mJ hmJ
    c0_hsteps_nogrp
    refine bn_zero_call_wp hnq (sep_pick3_5 hmJ) fun q0 hmQ0 => ?_
    have hmQ0' := sep_unpick3_5 hmQ0
    let qInit := List.replicate na.toNat 0#64 ++ qXs.drop na.toNat
    have hqInitLen : qInit.length = qXs.length := by dsimp [qInit]; simp; omega
    have hqInitZero : ∀ j (_hj : j < na.toNat) (hjq : j < qInit.length),
        qInit[j]'hjq = 0#64 := fun j hj _ => by
      dsimp [qInit]; rw [List.getElem_append_left (by simp [hj]), List.getElem_replicate]
    c0_hsteps_nogrp
    refine bn_zero_call_wp hnr (sep_pick4_5 hmQ0') fun r0 hmR0 => ?_
    have hmR0' := sep_unpick4_5 hmR0
    let rInit := List.replicate nb.toNat 0#64 ++ rXs.drop nb.toNat
    have hrInitLen : rInit.length = rXs.length := by dsimp [rInit]; simp; omega
    have hrInitZero : limbsVal (rInit.take nb.toNat) = 0 := by
      dsimp [rInit]; rw [List.take_append_of_le_length (by simp), List.take_replicate,
        Nat.min_self, limbsVal_replicate_zero]
    have hqInitVal : limbsVal (qInit.take na.toNat) = 0 := by
      dsimp [qInit]; rw [List.take_append_of_le_length (by simp), List.take_replicate,
        Nat.min_self, limbsVal_replicate_zero]
    exact bn_divmod_word_loop_wp rfl rfl hna hnb hnq hnr hbPos hbLtPow haLtPow hqInitLen
      hrInitLen hqInitZero hqInitVal hrInitZero hmR0' hQ
  · intro Js hJs
    c0_hsplit
    · have hna1 : na.toNat = 1 := by
        first
          | (have hc : na = 1 := by assumption; rw [hc]; rfl)
          | (have hc : na = 1#64 := by assumption; rw [hc]; rfl)
          | c0_bv_omega
      c0_hsplit
      · have hnb1 : nb.toNat = 1 := by
          first
            | (have hc : nb = 1 := by assumption; rw [hc]; rfl)
            | (have hc : nb = 1#64 := by assumption; rw [hc]; rfl)
            | c0_bv_omega
        have hb0Ne : bXs[0]'(by omega) ≠ 0#64 := by
          have hb0 := hbLast
          rw [hnb1, Nat.sub_self, List.getElem!_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega)] at hb0
          exact hb0
        c0_hsteps
        try dsimp only [lift2, Arg.val] at hm ⊢
        try rw [wp_ret]
        all_goals first
          | exact absurd (by assumption : bXs[0]'(by omega) = 0#64) hb0Ne
          | exact hb0Ne
          | exact bn_divmod_fast1_post hna1 hnb1 (by omega) (by omega) (by omega) (by omega)
              (sep_ac hm) hQ
      · c0_hsteps; (try rw [wp_jump]); exact hJs () m hm
    · c0_hsteps; (try rw [wp_jump]); exact hJs () m hm

end LeanQbe.T.LeanLCNF
