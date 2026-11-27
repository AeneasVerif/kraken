module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof1
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof2
import all Kraken.Mem
import all Kraken.Separation
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Compound `Nat` Operations (`bn_nat_pow`, `bn_nat_gcd`) & Shared Helpers (`Milestone R1`, Part 3)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

theorem sep_cast_ac {P Q : Mem 64 → Prop} {m : Mem 64} (h : P m) (heq : P = Q) : Q m :=
  heq ▸ h

local macro "sep_ac" : tactic =>
  `(tactic| exact sep_cast_ac (by assumption) (by ac_rfl))

local macro "sep_use " t:term : tactic =>
  `(tactic| exact sep_cast_ac $t (by ac_rfl))

private theorem limbsVal_take_append_prefix {xs ys : List (BitVec 64)} {k n v : Nat}
    (hk : k = n) (hle : n ≤ xs.length) (hval : limbsVal (xs.take n) = v) :
    limbsVal ((xs.take k ++ ys).take n) = v := by
  subst hk
  rw [List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take, Nat.min_self]
  exact hval

/-! ## 1. Array Splitting / Joining, `BigNumRtWf`, and Bit-Arithmetic Helpers -/

theorem BigNumRtWf.with_state_len {rt : BitVec 64} {st st' : RtC0State} {scr : BitVec 64}
    {scrLimbs scrLimbs' : List (BitVec 64)}
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (hb' : st'.Bounded48) (hlen : scrLimbs'.length = scrLimbs.length) :
    BigNumRtWf rt st' scr scrLimbs' := by
  rcases hwf with ⟨_, hrt, hne, hmod, hlt, haddr⟩
  refine ⟨hb', hrt, hne, hmod, ?_, ?_⟩ <;> omega

theorem array64_join2 (a : BitVec 64) (s1 s2 : List (BitVec 64)) (k : Nat)
    (h1 : s1.length = k) :
    (array64 a s1 ⋆ array64 (a + BitVec.ofNat 64 (8 * k)) s2) = array64 a (s1 ++ s2) := by
  have hle : k ≤ (s1 ++ s2).length := by simp [h1]
  have hs := array64_split2 a (s1 ++ s2) k hle
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
      List.nil_append] at hs
  exact hs.symm

theorem array64_split4 (a : BitVec 64) (xs : List (BitVec 64)) (k1 k2 k3 : Nat)
    (h : k1 + k2 + k3 ≤ xs.length) :
    array64 a xs =
      (array64 a (xs.take k1) ⋆
       array64 (a + BitVec.ofNat 64 (8 * k1)) ((xs.drop k1).take k2) ⋆
       array64 (a + BitVec.ofNat 64 (8 * (k1 + k2))) ((xs.drop (k1 + k2)).take k3) ⋆
       array64 (a + BitVec.ofNat 64 (8 * (k1 + k2 + k3))) (xs.drop (k1 + k2 + k3))) := by
  have hs1 := array64_split3 a xs k1 k2 (by omega)
  have hs2 := array64_split2 (a + BitVec.ofNat 64 (8 * (k1 + k2))) (xs.drop (k1 + k2)) k3 (by
    rw [List.length_drop]; omega)
  have hadd : a + BitVec.ofNat 64 (8 * (k1 + k2)) + BitVec.ofNat 64 (8 * k3) =
      a + BitVec.ofNat 64 (8 * (k1 + k2 + k3)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hs1, hs2, hadd, List.drop_drop, ← sep_assoc]

theorem array64_join4 (a : BitVec 64) (s1 s2 s3 s4 : List (BitVec 64)) (k1 k2 k3 : Nat)
    (h1 : s1.length = k1) (h2 : s2.length = k2) (h3 : s3.length = k3) :
    (array64 a s1 ⋆
     array64 (a + BitVec.ofNat 64 (8 * k1)) s2 ⋆
     array64 (a + BitVec.ofNat 64 (8 * (k1 + k2))) s3 ⋆
     array64 (a + BitVec.ofNat 64 (8 * (k1 + k2 + k3))) s4) =
      array64 a (s1 ++ s2 ++ s3 ++ s4) := by
  have j12 := array64_join2 a s1 s2 k1 h1
  have j123 := array64_join2 a (s1 ++ s2) s3 (k1 + k2) (by simp [h1, h2])
  have j1234 := array64_join2 a (s1 ++ s2 ++ s3) s4 (k1 + k2 + k3) (by
    simp only [List.length_append, h1, h2, h3])
  rw [← j12] at j123
  rw [← j123] at j1234
  exact j1234

/-- Computable helper reading `k` consecutive 64-bit limbs from memory for loop measures. -/
@[expose] def readLimbsVal (m : Mem 64) (p : BitVec 64) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let v := (loadVal m i64 p).getD 0#64
    v.toNat + 2 ^ 64 * readLimbsVal m (p + 8) k

theorem readLimbsVal_eq_of_array64 :
    ∀ {k : Nat} {p : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64},
      (array64 p xs ⋆ R) m → k ≤ xs.length →
      readLimbsVal m p k = limbsVal (xs.take k)
  | 0, _, _, _, _, _, _ => by simp [readLimbsVal]
  | k + 1, p, xs, R, m, hm, hle => by
    cases xs with
    | nil => simp at hle
    | cons x xs' =>
      rw [array64_cons, sep_assoc] at hm
      have hld : loadVal m i64 p = some x := loadVal_cell64 hm
      have hm' : (array64 (p + 8) xs' ⋆ (cell64 p x ⋆ R)) m := by sep_use hm
      have hrec := readLimbsVal_eq_of_array64 (k := k) (p := p + 8) (xs := xs') hm' (by
        simp at hle; omega)
      simp only [readLimbsVal, List.take_succ_cons, limbsVal_cons, hld, Option.getD_some]
      rw [hrec]

private theorem bv64_eq_one_iff_natRep_zero {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hn : natRep w n objs) : w = 1#64 ↔ n = 0 := by
  constructor
  · intro hw
    subst hw
    unfold natRep at hn
    split at hn
    · have hto := congrArg BitVec.toNat hn
      simp only [BitVec.toNat_ofNat] at hto
      have hlt : 2 * n + 1 < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hlt] at hto
      omega
    · exfalso
      have h0 := hn.1
      have h1 : (1#64 &&& 1#64) = 1#64 := by decide
      rw [h1] at h0
      exact absurd h0 (by decide)
  · intro hn0
    subst hn0
    unfold natRep at hn
    simpa using hn

private theorem bv64_eq_three_iff_natRep_one {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hn : natRep w n objs) : w = 3#64 ↔ n = 1 := by
  constructor
  · intro hw
    subst hw
    unfold natRep at hn
    split at hn
    · have hto := congrArg BitVec.toNat hn
      simp only [BitVec.toNat_ofNat] at hto
      have hlt : 2 * n + 1 < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hlt] at hto
      omega
    · exfalso
      have h0 := hn.1
      have h1 : (3#64 &&& 1#64) = 1#64 := by decide
      rw [h1] at h0
      exact absurd h0 (by decide)
  · intro hn1
    subst hn1
    unfold natRep at hn
    simpa using hn

theorem preservesMeta_refl (st : RtC0State) : st.PreservesMeta st := by
  simp [RtC0State.PreservesMeta]

theorem preservesMeta_trans {st1 st2 st3 : RtC0State}
    (h1 : st1.PreservesMeta st2) (h2 : st2.PreservesMeta st3) :
    st1.PreservesMeta st3 := by
  rcases h1 with ⟨a1, b1, c1, d1, e1, f1, g1, h1', i1⟩
  rcases h2 with ⟨a2, b2, c2, d2, e2, f2, g2, h2', i2⟩
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1,
    f2.trans f1, g2.trans g1, h2'.trans h1', i2.trans i1⟩

theorem wp_call_ret0 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {f : Sym} {as : List Ty} (args : Tup (Arg Val) as)
    (k : Tup Val [] → Expr Val Cont rs) (Pred : Tup Val [] → Mem 64 → Prop) {m : Mem 64}
    (hcall : Γ f as [] (vals args) m (fun r m' => Pred r m') (fun _ _ _ _ => False))
    (hk : ∀ r m', Pred r m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  ⟨_, _, hcall, fun r m' hr => hk r m' hr, fun _ _ _ _ hx => hx.elim⟩

theorem limbLenNat_add_one_le (n : Nat) : limbLenNat (n + 1) ≤ limbLenNat n + 1 := by
  by_cases h : limbLenNat (n + 1) ≤ limbLenNat n + 1
  · exact h
  · have hlt : n < 2 ^ (64 * limbLenNat n) := limbLenNat_lt_pow
    have hpow1 : 2 ^ (64 * limbLenNat n) + 1 ≤ 2 ^ (64 * (limbLenNat n + 1)) := by
      have h1 : 1 ≤ 2 ^ (64 * limbLenNat n) := Nat.one_le_pow _ _ (by decide)
      have h2 : 2 ^ (64 * limbLenNat n) * 2 ≤ 2 ^ (64 * limbLenNat n) * 2 ^ 64 :=
        Nat.mul_le_mul_left _ (by decide)
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]; omega
    have hpow2 := pow_le_of_limbLenNat (n := n + 1) (Nat.succ_pos n)
    have hpow3 := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 64 * (limbLenNat n + 1) ≤ 64 * (limbLenNat (n + 1) - 1) by omega)
    omega

theorem limbLenNat_add_le (a b : Nat) :
    limbLenNat (a + b) ≤ max (limbLenNat a) (limbLenNat b) + 1 := by
  by_cases h : limbLenNat (a + b) ≤ max (limbLenNat a) (limbLenNat b) + 1
  · exact h
  · have ha : a < 2 ^ (64 * limbLenNat a) := limbLenNat_lt_pow
    have hb : b < 2 ^ (64 * limbLenNat b) := limbLenNat_lt_pow
    have hm := max (limbLenNat a) (limbLenNat b)
    have h1 : 2 ^ (64 * limbLenNat a) ≤ 2 ^ (64 * max (limbLenNat a) (limbLenNat b)) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ (64 * limbLenNat b) ≤ 2 ^ (64 * max (limbLenNat a) (limbLenNat b)) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : 2 * 2 ^ (64 * max (limbLenNat a) (limbLenNat b)) ≤
        2 ^ (64 * (max (limbLenNat a) (limbLenNat b) + 1)) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm 2]
      exact Nat.mul_le_mul_left _ (by decide)
    have hpos : 0 < a + b := by
      by_cases h0 : a + b = 0
      · exfalso; rw [h0] at h; simp [limbLenNat] at h
      · omega
    have hpow2 := pow_le_of_limbLenNat (n := a + b) hpos
    have hpow3 := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 64 * (max (limbLenNat a) (limbLenNat b) + 1) ≤ 64 * (limbLenNat (a + b) - 1) by omega)
    omega

theorem limbLenNat_mul_le (a b : Nat) : limbLenNat (a * b) ≤ limbLenNat a + limbLenNat b := by
  by_cases h : limbLenNat (a * b) ≤ limbLenNat a + limbLenNat b
  · exact h
  · have ha : a < 2 ^ (64 * limbLenNat a) := limbLenNat_lt_pow
    have hb : b < 2 ^ (64 * limbLenNat b) := limbLenNat_lt_pow
    have hmul : a * b < 2 ^ (64 * (limbLenNat a + limbLenNat b)) := by
      have h3 := Nat.mul_lt_mul'' ha hb
      rwa [← Nat.pow_add, ← Nat.mul_add] at h3
    have hpos : 0 < a * b := by
      by_cases h0 : a * b = 0
      · exfalso; rw [h0] at h; simp [limbLenNat] at h
      · omega
    have hpow2 := pow_le_of_limbLenNat (n := a * b) hpos
    have hpow3 := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 64 * (limbLenNat a + limbLenNat b) ≤ 64 * (limbLenNat (a * b) - 1) by omega)
    omega

private theorem natRep_small_bits {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hn : natRep w n objs) (hlt : n < 2 ^ 63) :
    (w &&& 1#64) = 1#64 ∧ w >>> 1 = BitVec.ofNat 64 n := by
  unfold natRep at hn
  simp only [hlt, ↓reduceIte] at hn
  subst hn
  have hlt64 : 2 * n + 1 < 2 ^ 64 := by omega
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.and_one_is_mod]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight]
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    omega

private theorem limbLenNat_add_le_of_mul_lt {x y tn : Nat}
    (hx : 0 < x) (hy : 0 < y) (hxy : x * y < 2 ^ (64 * tn)) :
    limbLenNat x + limbLenNat y ≤ tn + 1 := by
  have hxpow := pow_le_of_limbLenNat hx
  have hypow := pow_le_of_limbLenNat hy
  have hlx : 0 < limbLenNat x := limbLenNat_pos_iff.mpr hx
  have hly : 0 < limbLenNat y := limbLenNat_pos_iff.mpr hy
  have hmul : 2 ^ (64 * (limbLenNat x - 1) + 64 * (limbLenNat y - 1)) ≤ x * y := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul hxpow hypow
  have hlt_pow : 2 ^ (64 * (limbLenNat x - 1 + (limbLenNat y - 1))) < 2 ^ (64 * tn) := by
    rw [Nat.mul_add]
    exact Nat.lt_of_le_of_lt hmul hxy
  have hlt_exp : 64 * (limbLenNat x - 1 + (limbLenNat y - 1)) < 64 * tn :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt_pow
  omega

private theorem limb_last_nonzero_of_limbLenNat {xs : List (BitVec 64)} {n : Nat}
    (hle : n ≤ xs.length) (hpos : 0 < n) (hlen : limbLenNat (limbsVal (xs.take n)) = n) :
    xs[n - 1]! ≠ 0#64 := by
  have htl := limbLenNat_trimLenLoop (xs := xs) (n := n) hle
  rw [hlen] at htl
  have hnz := trimLenLoop_nonzero xs n (by omega)
  rwa [← htl] at hnz

private theorem limbsVal_take_one_set0 {xs : List (BitVec 64)} {v : BitVec 64}
    (hpos : 0 < xs.length) : limbsVal ((xs.set 0 v).take 1) = v.toNat := by
  cases xs with
  | nil => simp at hpos
  | cons x xs' => simp [List.set, limbsVal]

/-! ## 2. `*_call_wp` Wrappers for Helper Functions -/

private theorem bn_nat_len_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {val : Nat} {objs : List LcnfObj} {R : Mem 64 → Prop}
    (hrep : natRep a val objs)
    (hm : (lcnfHeap objs ⋆ R) m)
    (hk : wp rtR1Env Q X (k (BitVec.ofNat 64 (limbLenNat val), ())) m) :
    wp rtR1Env Q X (Expr.call (as := [i64]) (bs := [i64]) "bn_nat_len" (Arg.var a, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_nat_len
  exact ⟨val, objs, R, hrep, hm, hk⟩

private theorem bn_require_scratch_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt need scr cap : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {R : Mem 64 → Prop}
    (hscr0 : scr ≠ 0#64) (hneed : need.toNat ≤ cap.toNat)
    (hm : (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) cap ⋆ R) m)
    (hk : wp rtR1Env Q X (k (scr, ())) m) :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "bn_require_scratch" (Arg.var rt, Arg.var need,
        ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_require_scratch
  exact ⟨scr, cap, R, hscr0, hneed, hm, hk⟩

theorem bn_load_nat_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a dst : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {val : Nat} {objs : List LcnfObj} {dstXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hrep : natRep a val objs) (hlen : limbLenNat val ≤ dstXs.length)
    (hm : (lcnfHeap objs ⋆ array64 dst dstXs ⋆ R) m)
    (hk : ∀ dstXs' m',
      dstXs'.length = dstXs.length →
      limbsVal (dstXs'.take (limbLenNat val)) = val →
      dstXs'.drop (limbLenNat val) = dstXs.drop (limbLenNat val) →
      (lcnfHeap objs ⋆ array64 dst dstXs' ⋆ R) m' →
      wp rtR1Env Q X (k (BitVec.ofNat 64 (limbLenNat val), ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "bn_load_nat" (Arg.var a, Arg.var dst,
        ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_load_nat
  exact ⟨val, objs, dstXs, R, hrep, hlen, hm, hk⟩

theorem bn_nat_from_limbs_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt buf n : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {bufXs : List (BitVec 64)} {objs : List LcnfObj} {R : Mem 64 → Prop}
    (hlen : n.toNat ≤ bufXs.length) (hmax : n.toNat ≤ mpzMaxLimbs) (hb : st.Bounded48)
    (halloc : 2 ^ 63 ≤ limbsVal (bufXs.take n.toNat) →
      st.hasFree (16 + 8 * trimLenLoop bufXs n.toNat) ∨ 16 + 8 * trimLenLoop bufXs n.toNat ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ p st' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      natRep p (limbsVal (bufXs.take n.toNat)) objs' →
      (limbsVal (bufXs.take n.toNat) < 2 ^ 63 → objs' = objs) →
      (2 ^ 63 ≤ limbsVal (bufXs.take n.toNat) →
        ∃ newObj, newObj.addr = p ∧
          mpzNatCanon newObj (limbsVal (bufXs.take n.toNat)) ∧ objs' = newObj :: objs) →
      (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs' ⋆ R) m' →
      wp rtR1Env Q X (k (p, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_nat_from_limbs"
        (Arg.var rt, Arg.var buf, Arg.var n, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_nat_from_limbs
  exact ⟨st, bufXs, objs, R, hlen, hmax, hb, halloc, hm, hk⟩

private theorem bn_copy_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {dst src n : BitVec 64} {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    {dstXs srcXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hd : n.toNat ≤ dstXs.length) (hs : n.toNat ≤ srcXs.length)
    (hm : (array64 dst dstXs ⋆ array64 src srcXs ⋆ R) m)
    (hk : ∀ m',
      (array64 dst (srcXs.take n.toNat ++ dstXs.drop n.toNat) ⋆ array64 src srcXs ⋆ R) m' →
      wp rtR1Env Q X (k ()) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy" (Arg.var dst, Arg.var src, Arg.var n,
        ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [])
  apply rtR1Env_bn_copy
  exact ⟨dstXs, srcXs, R, hd, hs, hm, hk⟩

theorem bn_mul_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a na b nb out : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {aXs bXs outXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : na.toNat ≤ aXs.length) (hb : nb.toNat ≤ bXs.length)
    (hout : na.toNat + nb.toNat ≤ outXs.length) (hlt : na.toNat + nb.toNat < 2 ^ 64)
    (hm : (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs ⋆ R) m)
    (hk : ∀ outXs' m',
      outXs'.length = outXs.length →
      limbLenNat (limbsVal (aXs.take na.toNat) * limbsVal (bXs.take nb.toNat)) ≤ outXs.length →
      limbsVal (outXs'.take (limbLenNat (limbsVal (aXs.take na.toNat) * limbsVal
        (bXs.take nb.toNat)))) =
        limbsVal (aXs.take na.toNat) * limbsVal (bXs.take nb.toNat) →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs' ⋆ R) m' →
      wp rtR1Env Q X
        (k (BitVec.ofNat 64 (limbLenNat (limbsVal (aXs.take na.toNat) * limbsVal
          (bXs.take nb.toNat))), ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "bn_mul"
        (Arg.var a, Arg.var na, Arg.var b, Arg.var nb, Arg.var out, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_mul
  exact ⟨aXs, bXs, outXs, R, ha, hb, hout, hlt, hm, hk⟩

theorem bn_cmp_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a na b nb : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {aXs bXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : na.toNat ≤ aXs.length) (hb : nb.toNat ≤ bXs.length)
    (hm : (array64 a aXs ⋆ array64 b bXs ⋆ R) m)
    (hk : wp rtR1Env Q X
      (k (cmpResult64 (limbsVal (aXs.take na.toNat)) (limbsVal (bXs.take nb.toNat)), ())) m) :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
        (Arg.var a, Arg.var na, Arg.var b, Arg.var nb, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_cmp
  exact ⟨aXs, bXs, R, ha, hb, hm, hk⟩

theorem bn_divmod_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a na b nb q r : BitVec 64} {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    {aXs bXs qXs rXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hapos : 0 < na.toNat) (hbpos : 0 < nb.toNat)
    (ha : na.toNat ≤ aXs.length) (hb : nb.toNat ≤ bXs.length)
    (hq : na.toNat ≤ qXs.length) (hr : nb.toNat ≤ rXs.length)
    (hnz : bXs[nb.toNat - 1]! ≠ 0#64)
    (hm : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs ⋆ array64 r rXs ⋆ R) m)
    (hk : ∀ qXs' rXs' m',
      qXs'.length = qXs.length → rXs'.length = rXs.length →
      limbsVal (qXs'.take na.toNat) = limbsVal (aXs.take na.toNat) / limbsVal (bXs.take nb.toNat) →
      limbsVal (rXs'.take nb.toNat) = limbsVal (aXs.take na.toNat) % limbsVal (bXs.take nb.toNat) →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXs' ⋆ R) m' →
      wp rtR1Env Q X (k ()) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64, i64, i64]) (bs := []) "bn_divmod"
        (Arg.var a, Arg.var na, Arg.var b, Arg.var nb, Arg.var q, Arg.var r, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [])
  apply rtR1Env_bn_divmod
  exact ⟨aXs, bXs, qXs, rXs, R, hapos, hbpos, ha, hb, hq, hr, hnz, hm, hk⟩

theorem bn_trim_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {buf n : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hlen : n.toNat ≤ xs.length)
    (hm : (array64 buf xs ⋆ R) m)
    (hk : wp rtR1Env Q X (k (BitVec.ofNat 64 (trimLenLoop xs n.toNat), ())) m) :
    wp rtR1Env Q X (Expr.call (as := [i64, i64]) (bs := [i64]) "bn_trim" (Arg.var buf, Arg.var n,
      ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_trim
  exact ⟨xs, R, hlen, hm, hk⟩

private theorem lcnf_nat_alloc_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt nlimbs : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {R : Mem 64 → Prop}
    (hmax : nlimbs.toNat ≤ mpzMaxLimbs) (hb : st.Bounded48)
    (halloc : st.hasFree (16 + 8 * max 1 nlimbs.toNat) ∨ 16 + 8 * max 1 nlimbs.toNat ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ R) m)
    (hk : ∀ p st' m',
      let n' := max 1 nlimbs.toNat
      let bytes := 16 + 8 * n'
      let obj : LcnfObj :=
        { addr := p, rc := 1#32, csSz := if bytes < 65536 then bytes else 0,
          other := 0, tag := mpzTag, cap := n', arrSize := n', limbs := List.replicate n' 0#64 }
      obj.Wf → (p &&& 1#64) = 0#64 → st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      (rtC0Inv rt st' ⋆ lcnfObjMem obj ⋆ R) m' → wp rtR1Env Q X (k (p, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "lcnf_nat_alloc" (Arg.var rt, Arg.var nlimbs,
        ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_lcnf_nat_alloc
  exact ⟨st, R, hmax, hb, halloc, hm, hk⟩

theorem lcnf_nat_alloc_imm1_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {R : Mem 64 → Prop}
    (hb : st.Bounded48) (halloc : st.hasFree 24 ∨ 24 ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ R) m)
    (hk : ∀ p st' m',
      let obj : LcnfObj :=
        { addr := p, rc := 1#32, csSz := 24, other := 0,
          tag := mpzTag, cap := 1, arrSize := 1, limbs := [0#64] }
      obj.Wf → (p &&& 1#64) = 0#64 → st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      (rtC0Inv rt st' ⋆ lcnfObjMem obj ⋆ R) m' → wp rtR1Env Q X (k (p, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "lcnf_nat_alloc" (Arg.var rt, Arg.imm 1,
        ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_lcnf_nat_alloc
  have hmax : (1#64).toNat ≤ mpzMaxLimbs := by decide
  dsimp only [lcnfNatAllocSpec]
  refine ⟨st, R, hmax, hb, ?_, hm, ?_⟩
  · simpa using halloc
  · intro p st' m' hwf hp hmst hrem hb' hmem
    exact hk p st' m' (by simpa using hwf) hp hmst hrem hb' (by simpa using hmem)

private theorem bn_dec_nat_boxed_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt a : BitVec 64} {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {objs : List LcnfObj} {R : Mem 64 → Prop}
    (ha : (a &&& 1#64) = 0#64) (hwc : objs.length ≤ st.workCap)
    (hm : (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m)
    (hmem : ∃ obj ∈ objs, obj.addr = a) (hwf : ∀ obj ∈ objs, obj.Wf) (hcl : lcnfHeapClosed objs)
    (hrc : ∀ obj ∈ objs, obj.addr = a → obj.rc = 1#32 → RcSound a objs)
    (hk : ∀ st' objs' m',
      DecNatRel a st st' objs objs' →
      (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → wp rtR1Env Q X (k ()) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64]) (bs := []) "bn_dec_nat" (Arg.var rt, Arg.var a, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [])
  apply rtR1Env_bn_dec_nat
  dsimp only [bnDecNatSpec, vals, Arg.val]
  simp only [ha, ne_eq, not_true_eq_false, ↓reduceIte]
  exact ⟨st, objs, R, hwc, hm, hmem, hwf, hcl, hrc, hk⟩

private theorem bn_int_from_limbs_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt neg buf n : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {bufXs : List (BitVec 64)} {objs : List LcnfObj} {R : Mem 64 → Prop}
    (hlen : n.toNat ≤ bufXs.length) (hmax : n.toNat ≤ mpzMaxLimbs) (hb : st.Bounded48)
    (halloc :
      let mag := limbsVal (bufXs.take n.toNat)
      let tn := trimLenLoop bufXs n.toNat
      let val : Int := if tn = 0 then 0 else if neg = 0#64 then (mag : Int) else -(mag : Int)
      (val < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ val) →
        st.hasFree (16 + 8 * tn) ∨ 16 + 8 * tn ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ p st' objs' m',
      let mag := limbsVal (bufXs.take n.toNat)
      let tn := trimLenLoop bufXs n.toNat
      let val : Int := if tn = 0 then 0 else if neg = 0#64 then (mag : Int) else -(mag : Int)
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 → intRep p val objs' →
      ((-(2 ^ 62 : Int) ≤ val ∧ val < (2 ^ 62 : Int)) → objs' = objs) →
      ((val < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ val) →
        ∃ newObj : LcnfObj, newObj.addr = p ∧ mpzIntCanon newObj val ∧ objs' = newObj :: objs) →
      (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs' ⋆ R) m' →
      wp rtR1Env Q X (k (p, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_int_from_limbs"
        (Arg.var rt, Arg.var neg, Arg.var buf, Arg.var n, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_int_from_limbs
  exact ⟨st, bufXs, objs, R, hlen, hmax, hb, halloc, hm, hk⟩

private theorem bn_int_from_limbs_imm1_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt buf n : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {bufXs : List (BitVec 64)} {objs : List LcnfObj} {R : Mem 64 → Prop}
    (hlen : n.toNat ≤ bufXs.length) (hmax : n.toNat ≤ mpzMaxLimbs) (hb : st.Bounded48)
    (halloc :
      let mag := limbsVal (bufXs.take n.toNat)
      let tn := trimLenLoop bufXs n.toNat
      let val : Int := if tn = 0 then 0 else -(mag : Int)
      (val < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ val) →
        st.hasFree (16 + 8 * tn) ∨ 16 + 8 * tn ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ p st' objs' m',
      let mag := limbsVal (bufXs.take n.toNat)
      let tn := trimLenLoop bufXs n.toNat
      let val : Int := if tn = 0 then 0 else -(mag : Int)
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 → intRep p val objs' →
      ((-(2 ^ 62 : Int) ≤ val ∧ val < (2 ^ 62 : Int)) → objs' = objs) →
      ((val < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ val) →
        ∃ newObj : LcnfObj, newObj.addr = p ∧ mpzIntCanon newObj val ∧ objs' = newObj :: objs) →
      (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs' ⋆ R) m' →
      wp rtR1Env Q X (k (p, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_int_from_limbs"
        (Arg.var rt, Arg.imm 1, Arg.var buf, Arg.var n, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_int_from_limbs
  have h10 : (1#64 : BitVec 64) ≠ 0#64 := by decide
  dsimp only [bnIntFromLimbsSpec]
  refine ⟨st, bufXs, objs, R, hlen, hmax, hb, ?_, hm, ?_⟩
  · simpa [h10] using halloc
  · intro p st' objs' m' hmst hrem hb' hrep hsm hbg hmem
    exact hk p st' objs' m' hmst hrem hb' (by simpa [h10] using hrep)
      (by simpa [h10] using hsm) (by simpa [h10] using hbg) hmem

private theorem bn_int_from_limbs_imm0_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt buf n : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {st : RtC0State} {bufXs : List (BitVec 64)} {objs : List LcnfObj} {R : Mem 64 → Prop}
    (hlen : n.toNat ≤ bufXs.length) (hmax : n.toNat ≤ mpzMaxLimbs) (hb : st.Bounded48)
    (halloc :
      let mag := limbsVal (bufXs.take n.toNat)
      let tn := trimLenLoop bufXs n.toNat
      let val : Int := if tn = 0 then 0 else (mag : Int)
      (val < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ val) →
        st.hasFree (16 + 8 * tn) ∨ 16 + 8 * tn ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ p st' objs' m',
      let mag := limbsVal (bufXs.take n.toNat)
      let tn := trimLenLoop bufXs n.toNat
      let val : Int := if tn = 0 then 0 else (mag : Int)
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 → intRep p val objs' →
      ((-(2 ^ 62 : Int) ≤ val ∧ val < (2 ^ 62 : Int)) → objs' = objs) →
      ((val < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ val) →
        ∃ newObj : LcnfObj, newObj.addr = p ∧ mpzIntCanon newObj val ∧ objs' = newObj :: objs) →
      (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs' ⋆ R) m' →
      wp rtR1Env Q X (k (p, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_int_from_limbs"
        (Arg.var rt, Arg.imm 0, Arg.var buf, Arg.var n, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_int_from_limbs
  dsimp only [bnIntFromLimbsSpec]
  refine ⟨st, bufXs, objs, R, hlen, hmax, hb, ?_, hm, ?_⟩
  · simpa using halloc
  · intro p st' objs' m' hmst hrem hb' hrep hsm hbg hmem
    exact hk p st' objs' m' hmst hrem hb' (by simpa using hrep)
      (by simpa using hsm) (by simpa using hbg) hmem

private theorem bn_int_len_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {val : Int} {objs : List LcnfObj} {R : Mem 64 → Prop}
    (hrep : intRep a val objs) (hm : (lcnfHeap objs ⋆ R) m)
    (hk : wp rtR1Env Q X (k (BitVec.ofNat 64 (limbLenNat val.natAbs), ())) m) :
    wp rtR1Env Q X (Expr.call (as := [i64]) (bs := [i64]) "bn_int_len" (Arg.var a, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_int_len
  exact ⟨val, objs, R, hrep, hm, hk⟩

private theorem bn_load_int_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a dst : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {val : Int} {objs : List LcnfObj} {dstXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hrep : intRep a val objs) (hlen : limbLenNat val.natAbs ≤ dstXs.length)
    (hm : (lcnfHeap objs ⋆ array64 dst dstXs ⋆ R) m)
    (hk : ∀ dstXs' m',
      dstXs'.length = dstXs.length →
      limbsVal (dstXs'.take (limbLenNat val.natAbs)) = val.natAbs →
      dstXs'.drop (limbLenNat val.natAbs) = dstXs.drop (limbLenNat val.natAbs) →
      (lcnfHeap objs ⋆ array64 dst dstXs' ⋆ R) m' →
      wp rtR1Env Q X
        (k ((BitVec.ofNat 64 (limbLenNat val.natAbs) <<< 1) ||| (if val < 0 then 1#64 else 0#64),
          ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "bn_load_int" (Arg.var a, Arg.var dst,
        ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_load_int
  exact ⟨val, objs, dstXs, R, hrep, hlen, hm, hk⟩

theorem bn_add_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a na b nb out : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {aXs bXs outXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : na.toNat ≤ aXs.length) (hb : nb.toNat ≤ bXs.length)
    (hout : max na.toNat nb.toNat + 1 ≤ outXs.length) (hlt : max na.toNat nb.toNat + 1 < 2 ^ 64)
    (hm : (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs ⋆ R) m)
    (hk : ∀ outXs' m',
      let sum := limbsVal (aXs.take na.toNat) + limbsVal (bXs.take nb.toNat)
      let tn := limbLenNat sum
      outXs'.length = outXs.length → tn ≤ outXs.length → limbsVal (outXs'.take tn) = sum →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs' ⋆ R) m' →
      wp rtR1Env Q X (k (BitVec.ofNat 64 tn, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "bn_add"
        (Arg.var a, Arg.var na, Arg.var b, Arg.var nb, Arg.var out, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_add
  exact ⟨aXs, bXs, outXs, R, ha, hb, hout, hlt, hm, hk⟩

private theorem bn_add_one_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a na out : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {aXs outXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : na.toNat ≤ aXs.length) (hout : na.toNat + 1 ≤ outXs.length) (hlt : na.toNat + 1 < 2 ^ 64)
    (hm : (array64 a aXs ⋆ array64 out outXs ⋆ R) m)
    (hk : ∀ outXs' m',
      let sum := limbsVal (aXs.take na.toNat) + 1
      let tn := limbLenNat sum
      outXs'.length = outXs.length → tn ≤ outXs.length → limbsVal (outXs'.take tn) = sum →
      (array64 a aXs ⋆ array64 out outXs' ⋆ R) m' →
      wp rtR1Env Q X (k (BitVec.ofNat 64 tn, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_add_one"
        (Arg.var a, Arg.var na, Arg.var out, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_add_one
  exact ⟨aXs, outXs, R, ha, hout, hlt, hm, hk⟩

theorem bn_sub_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a na b nb out : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {aXs bXs outXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : na.toNat ≤ aXs.length) (hb : nb.toNat ≤ bXs.length) (hout : na.toNat ≤ outXs.length)
    (hle : limbsVal (bXs.take nb.toNat) ≤ limbsVal (aXs.take na.toNat))
    (hm : (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs ⋆ R) m)
    (hk : ∀ outXs' m',
      let diff := limbsVal (aXs.take na.toNat) - limbsVal (bXs.take nb.toNat)
      let tn := limbLenNat diff
      outXs'.length = outXs.length → tn ≤ outXs.length → limbsVal (outXs'.take tn) = diff →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs' ⋆ R) m' →
      wp rtR1Env Q X (k (BitVec.ofNat 64 tn, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "bn_sub"
        (Arg.var a, Arg.var na, Arg.var b, Arg.var nb, Arg.var out, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_sub
  exact ⟨aXs, bXs, outXs, R, ha, hb, hout, hle, hm, hk⟩

theorem bn_sub_one_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a na out : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {aXs outXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : na.toNat ≤ aXs.length) (hout : na.toNat ≤ outXs.length)
    (hpos : na.toNat = 0 ∨ 1 ≤ limbsVal (aXs.take na.toNat))
    (hm : (array64 a aXs ⋆ array64 out outXs ⋆ R) m)
    (hk : ∀ outXs' m',
      let diff := limbsVal (aXs.take na.toNat) - 1
      let tn := limbLenNat diff
      outXs'.length = outXs.length → tn ≤ outXs.length → limbsVal (outXs'.take tn) = diff →
      (array64 a aXs ⋆ array64 out outXs' ⋆ R) m' →
      wp rtR1Env Q X (k (BitVec.ofNat 64 tn, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_sub_one"
        (Arg.var a, Arg.var na, Arg.var out, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_sub_one
  exact ⟨aXs, outXs, R, ha, hout, hpos, hm, hk⟩

theorem bn_bitwise_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {op a na b nb out : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {aXs bXs outXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hop : op = 0#64 ∨ op = 1#64 ∨ op = 2#64)
    (ha : na.toNat ≤ aXs.length) (hb : nb.toNat ≤ bXs.length)
    (hout : (if op = 0#64 then min na.toNat nb.toNat else max na.toNat nb.toNat) ≤ outXs.length)
    (hm : (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs ⋆ R) m)
    (hk : ∀ outXs' m',
      let aVal := limbsVal (aXs.take na.toNat)
      let bVal := limbsVal (bXs.take nb.toNat)
      let res := if op = 0#64 then Nat.land aVal bVal else if op = 1#64 then Nat.lor aVal bVal
        else Nat.xor aVal bVal
      let tn := limbLenNat res
      outXs'.length = outXs.length → tn ≤ outXs.length → limbsVal (outXs'.take tn) = res →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs' ⋆ R) m' →
      wp rtR1Env Q X (k (BitVec.ofNat 64 tn, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64, i64, i64]) (bs := [i64]) "bn_bitwise"
        (Arg.var op, Arg.var a, Arg.var na, Arg.var b, Arg.var nb, Arg.var out, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_bitwise
  exact ⟨aXs, bXs, outXs, R, hop, ha, hb, hout, hm, hk⟩

theorem bn_shl_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a na ws bs out : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {aXs outXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : na.toNat ≤ aXs.length) (hbs : bs.toNat < 64)
    (hout : na.toNat = 0 ∨ ws.toNat + na.toNat + 1 ≤ outXs.length)
    (hlt : ws.toNat + na.toNat + 1 < 2 ^ 64)
    (hm : (array64 a aXs ⋆ array64 out outXs ⋆ R) m)
    (hk : ∀ outXs' m',
      let res := limbsVal (aXs.take na.toNat) <<< (64 * ws.toNat + bs.toNat)
      let tn := limbLenNat res
      outXs'.length = outXs.length → tn ≤ outXs.length → limbsVal (outXs'.take tn) = res →
      (array64 a aXs ⋆ array64 out outXs' ⋆ R) m' →
      wp rtR1Env Q X (k (BitVec.ofNat 64 tn, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "bn_shl"
        (Arg.var a, Arg.var na, Arg.var ws, Arg.var bs, Arg.var out, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_shl
  exact ⟨aXs, outXs, R, ha, hbs, hout, hlt, hm, hk⟩

theorem bn_shr_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {a na ws bs out : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    {aXs outXs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : na.toNat ≤ aXs.length) (hbs : bs.toNat < 64)
    (hout : na.toNat ≤ ws.toNat ∨ na.toNat - ws.toNat ≤ outXs.length)
    (hm : (array64 a aXs ⋆ array64 out outXs ⋆ R) m)
    (hk : ∀ outXs' m',
      let res := limbsVal (aXs.take na.toNat) >>> (64 * ws.toNat + bs.toNat)
      let tn := limbLenNat res
      outXs'.length = outXs.length → tn ≤ outXs.length → limbsVal (outXs'.take tn) = res →
      (array64 a aXs ⋆ array64 out outXs' ⋆ R) m' →
      wp rtR1Env Q X (k (BitVec.ofNat 64 tn, ())) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "bn_shr"
        (Arg.var a, Arg.var na, Arg.var ws, Arg.var bs, Arg.var out, ()) k) m := by
  apply wp_call_of (Γ := rtR1Env) (bs := [i64])
  apply rtR1Env_bn_shr
  exact ⟨aXs, outXs, R, ha, hbs, hout, hm, hk⟩

theorem array64_split_len {a : BitVec 64} {xs : List (BitVec 64)} {k : Nat}
    (hk : k ≤ xs.length) :
    array64 a xs = array64 a (xs.take k) ⋆ array64 (a + BitVec.ofNat 64 (8 * k)) (xs.drop k) := by
  conv => lhs; rw [← List.take_append_drop k xs]
  rw [array64_append, List.length_take_of_le hk]

theorem limbsVal_msb_nz {xs : List (BitVec 64)} {n : Nat}
    (hn0 : 0 < n) (hn : n ≤ xs.length) (hval : limbLenNat (limbsVal (xs.take n)) = n) :
    xs[n - 1]! ≠ 0#64 := by
  cases hn_eq : n with
  | zero => omega
  | succ k =>
    have hk_lt : k < xs.length := by omega
    have htake : xs.take (k + 1) = xs.take k ++ [xs[k]] := by
      apply List.ext_getElem
      · simp [List.length_take_of_le (by omega : k + 1 ≤ xs.length)]
      · intro j hj _
        by_cases hjk : j < k
        · rw [List.getElem_take,
            List.getElem_append_left
              (by simp [List.length_take_of_le (by omega : k ≤ xs.length)]; omega),
            List.getElem_take]
        · have hjeq : j = k := by
            simp [List.length_take_of_le (by omega : k + 1 ≤ xs.length)] at hj; omega
          rw [List.getElem_take,
            List.getElem_append_right
              (by simp [List.length_take_of_le (by omega : k ≤ xs.length)]; omega)]
          simp [List.length_take_of_le (by omega : k ≤ xs.length), hjeq]
    intro hz
    have hms : xs[k] = 0#64 := by
      have hzk : xs[k]! = 0#64 := by simpa [hn_eq] using hz
      simpa [getElem!_pos xs k hk_lt] using hzk
    have hval_eq : limbsVal (xs.take (k + 1)) = limbsVal (xs.take k) := by
      rw [htake, limbsVal_snoc, hms]
      simp
    have hlt : limbsVal (xs.take (k + 1)) < 2 ^ (64 * k) := by
      rw [hval_eq]
      simpa [List.length_take_of_le (by omega : k ≤ xs.length)] using limbsVal_lt_pow (xs.take k)
    have hpos : 0 < limbsVal (xs.take (k + 1)) := limbLenNat_pos_iff.mp
      (by rw [← hn_eq, hval]; omega)
    have hge := pow_le_of_limbLenNat hpos
    rw [← hn_eq, hval, hn_eq] at hge
    simp only [Nat.add_sub_cancel] at hge
    omega

theorem bn_nat_len_rt_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt a scr : BitVec 64} {st : RtC0State} {scrLimbs : List (BitVec 64)}
    {val : Nat} {objs : List LcnfObj} {R : Mem 64 → Prop}
    {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    (hrep : natRep a val objs)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : wp rtR1Env Q X (k (BitVec.ofNat 64 (limbLenNat val), ())) m) :
    wp rtR1Env Q X (Expr.call (as := [i64]) (bs := [i64]) "bn_nat_len" (Arg.var a, ()) k) m := by
  dsimp only [bigNumRtInv] at hm
  exact bn_nat_len_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrLimbs ⋆ R)
    hrep (by sep_use hm) hk

private theorem bn_int_len_rt_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt a scr : BitVec 64} {st : RtC0State} {scrLimbs : List (BitVec 64)}
    {val : Int} {objs : List LcnfObj} {R : Mem 64 → Prop}
    {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    (hrep : intRep a val objs)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : wp rtR1Env Q X (k (BitVec.ofNat 64 (limbLenNat val.natAbs), ())) m) :
    wp rtR1Env Q X (Expr.call (as := [i64]) (bs := [i64]) "bn_int_len" (Arg.var a, ()) k) m := by
  dsimp only [bigNumRtInv] at hm
  exact bn_int_len_call_wp (R := rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrLimbs ⋆ R)
    hrep (by sep_use hm) hk

theorem bn_require_scratch_rt_call_wp {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt need scr : BitVec 64} {st : RtC0State} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {R : Mem 64 → Prop} {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    (hwf : BigNumRtWf rt st scr scrLimbs) (hneed : need.toNat ≤ scrLimbs.length)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hk : wp rtR1Env Q X (k (scr, ())) m) :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "bn_require_scratch" (Arg.var rt, Arg.var need,
        ()) k) m := by
  dsimp only [bigNumRtInv] at hm
  have hcap : (BitVec.ofNat 64 scrLimbs.length).toNat = scrLimbs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwf.2.2.2.2.1]
  exact bn_require_scratch_call_wp (R := rtC0Inv rt st ⋆ array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R)
    hwf.2.2.1 (by rwa [hcap]) (by sep_use hm) hk

theorem wp_jnz_true {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : Bool} {e1 e2 : Expr Val Cont rs} {m : Mem 64}
    (hc : c = true) (h : wp rtR1Env Q X e1 m) :
    wp rtR1Env Q X (Expr.jnz (Arg.var c) e1 e2) m :=
  wp_jnz_of (fun _ => h) (fun hf =>
    by change c = false at hf; rw [hc] at hf; exact absurd hf (by decide))

theorem wp_jnz_false {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : Bool} {e1 e2 : Expr Val Cont rs} {m : Mem 64}
    (hc : c = false) (h : wp rtR1Env Q X e2 m) :
    wp rtR1Env Q X (Expr.jnz (Arg.var c) e1 e2) m :=
  wp_jnz_of (fun ht =>
    by change c = true at ht; rw [hc] at ht; exact absurd ht (by decide)) (fun _ => h)

/-! ## 3. Compound Nat Operations: `bn_nat_pow_wp` and `bn_nat_gcd_wp` -/

private theorem bv64_ult_ofNat_false {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : b ≤ a) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = false := by
  rw [BitVec.ult]; simp [h]

private theorem bv64_ult_ofNat_true {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a < b) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true := by
  rw [BitVec.ult]; simp [h]

private theorem bv64_beq0_ofNat_false {a : Nat} (ha : a < 2 ^ 64) (hpos : 0 < a) :
    (BitVec.ofNat 64 a == 0#64) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  have ht := congrArg BitVec.toNat (beq_iff_eq.mp h)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at ht
  exact Nat.ne_of_gt hpos ht

private theorem bv64_mul_off_eq (scr : BitVec 64) (k n m : Nat) (_hn : n < 2 ^ 64)
    (hk : k = 8 * m) :
    scr + BitVec.ofNat 64 k * BitVec.ofNat 64 n = scr + BitVec.ofNat 64 (8 * (m * n)) := by
  subst hk; congr 1; rw [← BitVec.ofNat_mul, Nat.mul_assoc]

private theorem objs_mem_of_from_limbs {val : Nat} {objs objs' : List LcnfObj}
    {P1 P2 : LcnfObj → Prop}
    (hsmall : val < 2 ^ 63 → objs' = objs)
    (hbig : 2 ^ 63 ≤ val → ∃ newObj, P1 newObj ∧ P2 newObj ∧ objs' = newObj :: objs) :
    ∀ o ∈ objs, o ∈ objs' := by
  intro o ho
  by_cases hlt : val < 2 ^ 63
  · rw [hsmall hlt]; exact ho
  · obtain ⟨newObj, _, _, rfl⟩ := hbig (by omega); exact List.mem_cons_of_mem newObj ho

private theorem bn_nat_pow_sq_step (Q : Post [i64]) (X : XPost) (J2 : Cont [i64])
    (rt bufBase bufTmp bufProd bnBV : BitVec 64)
    (sliceNat prodLen nextExp tn resVal1 baseVal aVal bVal : Nat)
    (sBaseL sTmpL sProd1 : List (BitVec 64)) (R_sq : Mem 64 → Prop) (m1 : Mem 64)
    (hres1_pos : 0 < resVal1) (hbase_pos : 0 < baseVal)
    (heq1 : resVal1 * baseVal ^ (2 * nextExp) = aVal ^ bVal)
    (htn_ge : limbLenNat (aVal ^ bVal) ≤ tn)
    (hpow_lt : aVal ^ bVal < 2 ^ (64 * tn))
    (hbn_eq : bnBV = BitVec.ofNat 64 (limbLenNat baseVal))
    (hbn_le : limbLenNat baseVal ≤ tn)
    (hslice_ge : tn + 1 ≤ sliceNat) (hslice_lt : sliceNat < 2 ^ 64)
    (hprod_ge : sliceNat ≤ prodLen) (hprod_lt : prodLen < 2 ^ 64)
    (hnext_lt_64 : nextExp < 2 ^ 64)
    (hsBaseL : sBaseL.length = sliceNat) (hsTmpL : sTmpL.length = sliceNat)
    (hsProd1 : sProd1.length = prodLen)
    (hbaseVal : limbsVal (sBaseL.take (limbLenNat baseVal)) = baseVal)
    (hm1 : (array64 bufBase sBaseL ⋆ array64 bufTmp sTmpL ⋆ array64 bufProd sProd1 ⋆ R_sq) m1)
    (hJ2 : ∀ (baseVal2 : Nat) (sBase2 sTmp2 sProd2 : List (BitVec 64)) (m2 : Mem 64),
      0 < baseVal2 → resVal1 * baseVal2 ^ nextExp = aVal ^ bVal →
      limbLenNat baseVal2 ≤ tn → sBase2.length = sliceNat → sTmp2.length = sliceNat →
      sProd2.length = prodLen → limbsVal (sBase2.take (limbLenNat baseVal2)) = baseVal2 →
      (array64 bufBase sBase2 ⋆ array64 bufTmp sTmp2 ⋆ array64 bufProd sProd2 ⋆ R_sq) m2 →
      J2 (BitVec.ofNat 64 (limbLenNat baseVal2), ()) m2) :
    wp rtR1Env Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide),
          args := (Arg.var (BitVec.ofNat 64 nextExp), Arg.imm 0, ()) }
        fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.let_
            { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var bnBV, Arg.var bnBV,
              ()) } fun p =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide),
                args := (Arg.var p.fst, Arg.var (BitVec.ofNat 64 sliceNat), ()) }
              fun p =>
              Expr.jnz (Arg.var p.fst)
                (Expr.exit (as := [i64, i64]) "lcnf_panic" (Arg.var rt, Arg.imm 4, ()))
                (Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
                    (Arg.var bufTmp, Arg.var bufBase, Arg.var bnBV, ()) fun _ =>
                  Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "bn_mul"
                    (Arg.var bufBase, Arg.var bnBV, Arg.var bufTmp, Arg.var bnBV, Arg.var bufProd,
                      ()) fun p =>
                    Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
                      (Arg.var bufBase, Arg.var bufProd, Arg.var p.fst, ()) fun _ =>
                      Expr.jump J2 (Arg.var p.fst, ())))
          (Expr.jump J2 (Arg.var bnBV, ()))) m1 := by
  by_cases hnext0 : nextExp = 0
  · c0_let_simp
    refine wp_jnz_false (by rw [hnext0]; decide) ?_
    rw [wp_jump, hbn_eq]
    exact hJ2 baseVal sBaseL sTmpL sProd1 m1 hbase_pos (by simpa [hnext0] using heq1)
      hbn_le hsBaseL hsTmpL hsProd1 hbaseVal hm1
  · have hnext_pos : 0 < nextExp := Nat.pos_of_ne_zero hnext0
    have hbb_le_pow : baseVal * baseVal ≤ aVal ^ bVal := by
      have h1 : baseVal * baseVal ≤ baseVal ^ (2 * nextExp) := by
        simpa [Nat.pow_two] using Nat.pow_le_pow_right hbase_pos (show 2 ≤ 2 * nextExp by omega)
      exact Nat.le_trans h1 (Nat.le_trans (Nat.le_mul_of_pos_left _ hres1_pos) (Nat.le_of_eq heq1))
    have hbb_lt : baseVal * baseVal < 2 ^ (64 * tn) := Nat.lt_of_le_of_lt hbb_le_pow hpow_lt
    have hbnbn_le : limbLenNat baseVal + limbLenNat baseVal ≤ sliceNat := by
      have := limbLenNat_add_le_of_mul_lt hbase_pos hbase_pos hbb_lt; omega
    have hbn_to : bnBV.toNat = limbLenNat baseVal := by
      rw [hbn_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : limbLenNat baseVal < 2 ^ 64)]
    c0_let_simp
    refine wp_jnz_true (bv64_ult_ofNat_true (by decide) hnext_lt_64 hnext_pos) ?_
    c0_let_simp
    have hbn_add : bnBV + bnBV = BitVec.ofNat 64 (limbLenNat baseVal + limbLenNat baseVal) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hbn_to, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : limbLenNat baseVal + limbLenNat baseVal < 2 ^ 64)]
    refine wp_jnz_false (by
      rw [hbn_add]; exact bv64_ult_ofNat_false hslice_lt (by omega) hbnbn_le) ?_
    have hm_cp1 : (array64 bufTmp sTmpL ⋆ array64 bufBase sBaseL ⋆
        (array64 bufProd sProd1 ⋆ R_sq)) m1 := by sep_use hm1
    apply bn_copy_call_wp (by omega) (by omega) hm_cp1
    intro m1a hm1a
    let sTmp2 := sBaseL.take bnBV.toNat ++ sTmpL.drop bnBV.toNat
    have hsTmp2_len : sTmp2.length = sliceNat := by dsimp [sTmp2]; simp [hsBaseL, hsTmpL]; omega
    have hsTmp2_val : limbsVal (sTmp2.take (limbLenNat baseVal)) = baseVal := by
      dsimp only [sTmp2]; exact limbsVal_take_append_prefix hbn_to (by omega) hbaseVal
    have hm_mul : (array64 bufBase sBaseL ⋆ array64 bufTmp sTmp2 ⋆
        array64 bufProd sProd1 ⋆ R_sq) m1a := by sep_use hm1a
    apply bn_mul_call_wp (by omega) (by omega) (by omega) (by omega) hm_mul
    intro sProd2 m1b hsProd2_len hprod2_le hprod2_val hm1b
    rw [hbn_to, hbaseVal, hsTmp2_val] at hprod2_le hprod2_val ⊢; dsimp only
    have hm_cp2 : (array64 bufBase sBaseL ⋆ array64 bufProd sProd2 ⋆
        (array64 bufTmp sTmp2 ⋆ R_sq)) m1b := by sep_use hm1b
    have hll_bb_le : limbLenNat (baseVal * baseVal) ≤ tn :=
      Nat.le_trans (limbLenNat_mono hbb_le_pow) htn_ge
    have hll_bb_to : (BitVec.ofNat 64 (limbLenNat (baseVal * baseVal))).toNat =
        limbLenNat (baseVal * baseVal) := by
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : limbLenNat (baseVal * baseVal) < 2 ^ 64)]
    apply bn_copy_call_wp (by omega) (by omega) hm_cp2
    intro m2 hm2
    let sBase2 := sProd2.take (BitVec.ofNat 64 (limbLenNat (baseVal * baseVal))).toNat ++
      sBaseL.drop (BitVec.ofNat 64 (limbLenNat (baseVal * baseVal))).toNat
    have hsBase2_len : sBase2.length = sliceNat := by
      dsimp [sBase2]; simp [hsProd2_len, hsProd1, hsBaseL]; omega
    have hsBase2_val : limbsVal (sBase2.take (limbLenNat (baseVal * baseVal))) =
        baseVal * baseVal := by
      dsimp only [sBase2]; exact limbsVal_take_append_prefix hll_bb_to (by omega) hprod2_val
    rw [wp_jump]
    refine hJ2 (baseVal * baseVal) sBase2 sTmp2 sProd2 m2 (Nat.mul_pos hbase_pos hbase_pos) ?_
      hll_bb_le hsBase2_len hsTmp2_len (by omega) hsBase2_val (by sep_use hm2)
    rw [← Nat.pow_two, ← Nat.pow_mul, ← heq1]

theorem bn_nat_pow_wp (xs : Tup Val [i64, i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (hspec : bnNatPowSpec xs m Q X) :
    Func.wp rtR1Env bn_nat_pow.body xs m Q X := by
  rcases xs with ⟨rt, a, b, ⟨⟩⟩
  rcases hspec with ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, hna, hnb, hpow, hm, hpost⟩
  rcases hwf with ⟨h48, hrtb, hscr0, hscrm, hlen64, hscr64⟩
  unfold Func.wp bn_nat_pow bn_nat_pow_body; dsimp only; c0_step
  by_cases hb0 : bVal = 0
  · refine wp_jnz_true (by simp [(bv64_eq_one_iff_natRep_zero hnb).mpr hb0]) ?_; rw [wp_ret]
    exact hpost 3#64 st scrLimbs objs m (preservesMeta_refl st) (Nat.le_refl _)
      ⟨h48, hrtb, hscr0, hscrm, hlen64, hscr64⟩ (by simp [hb0, Nat.pow_zero, natRep])
      (fun o ho _ => ho) (fun o ho _ => ho) hm
  · have hbne : b ≠ 1#64 := fun h => hb0 ((bv64_eq_one_iff_natRep_zero hnb).mp h)
    refine wp_jnz_false (by simp [hbne]) ?_; c0_step
    by_cases ha0 : aVal = 0
    · refine wp_jnz_true (by simp [(bv64_eq_one_iff_natRep_zero hna).mpr ha0]) ?_; rw [wp_ret]
      exact hpost 1#64 st scrLimbs objs m (preservesMeta_refl st) (Nat.le_refl _)
        ⟨h48, hrtb, hscr0, hscrm, hlen64, hscr64⟩
        (by simp [ha0, Nat.zero_pow (Nat.pos_of_ne_zero hb0), natRep])
        (fun o ho _ => ho) (fun o ho _ => ho) hm
    · have hane1 : a ≠ 1#64 := fun h => ha0 ((bv64_eq_one_iff_natRep_zero hna).mp h)
      refine wp_jnz_false (by simp [hane1]) ?_; c0_step
      by_cases ha1 : aVal = 1
      · refine wp_jnz_true (by simp [(bv64_eq_three_iff_natRep_one hna).mpr ha1]) ?_; rw [wp_ret]
        exact hpost 3#64 st scrLimbs objs m (preservesMeta_refl st) (Nat.le_refl _)
          ⟨h48, hrtb, hscr0, hscrm, hlen64, hscr64⟩ (by simp [ha1, Nat.one_pow, natRep])
          (fun o ho _ => ho) (fun o ho _ => ho) hm
      · have hane3 : a ≠ 3#64 := fun h => ha1 ((bv64_eq_three_iff_natRep_one hna).mp h)
        rcases hpow with rfl | rfl | rfl | ⟨hb63, htn_max, hscr_cap, halloc⟩
        · exact absurd rfl hb0
        · exact absurd rfl ha0
        · exact absurd rfl ha1
        · have ha_ge2 : 2 ≤ aVal := by omega
          have hb_pos : 0 < bVal := Nat.pos_of_ne_zero hb0
          let na := limbLenNat aVal; let tn := limbLenNat (aVal ^ bVal)
          have hpow_pos : 0 < aVal ^ bVal := Nat.pow_pos (by omega)
          have htn_pos : 1 ≤ tn := limbLenNat_pos_iff.mpr hpow_pos
          have hna_le_tn : na ≤ tn := limbLenNat_mono (Nat.le_self_pow (by omega) aVal)
          have hna_max : na ≤ mpzMaxLimbs := limbLenNat_le_max_of_natRep hna
          rcases natRep_small_bits hnb hb63 with ⟨hband, hbshift⟩
          refine wp_jnz_false (by simp [hane3]) ?_; c0_step; c0_step
          have hm_len : (lcnfHeap objs ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R)) m := by sep_use hm
          apply bn_nat_len_call_wp hna hm_len; rw [hbshift]; dsimp only; c0_step
          refine wp_jnz_false (bv64_ult_ofNat_false (by decide) (by omega) hna_max) ?_; c0_step
          unfold bigNumRtInv at hm
          have hm_cap : (cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
              (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆ array64 scr scrLimbs ⋆
                lcnfHeap objs ⋆ R)) m := by sep_use hm
          rw [wp_load]
          refine ⟨BitVec.ofNat 64 scrLimbs.length, c0_load_cell64_add33680 hm_cap, ?_⟩
          c0_step
          have hm_scr : (cell64 (rt + 33672#64) scr ⋆ (rtC0Inv rt st ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrLimbs ⋆
              lcnfHeap objs ⋆ R)) m := by sep_use hm
          rw [wp_load]; refine ⟨scr, c0_load_cell64_add33672 hm_scr, ?_⟩
          refine wp_join_group (fun _ _ => False) (by rintro J _ _ hF; exact hF.elim) ?_
          intro J _; c0_step
          refine wp_jnz_false (by simp [hscr0]) ?_; c0_step
          refine wp_jnz_false (bv64_ult_ofNat_false hlen64 (by decide)
            (Nat.le_trans (Nat.le_mul_of_pos_right 4 (Nat.succ_pos _)) hscr_cap)) ?_
          apply wp_udiv_of (by simp); dsimp only [Arg.val]
          rw [show (BitVec.ofNat 64 scrLimbs.length / 4) =
              BitVec.ofNat 64 (scrLimbs.length / 4) from by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              show (4 : BitVec 64).toNat = 4 by decide, Nat.mod_eq_of_lt hlen64,
              Nat.mod_eq_of_lt (by omega : scrLimbs.length / 4 < 2 ^ 64)]]
          c0_step
          let sliceNat := scrLimbs.length / 4
          have hslice_ge : tn + 1 ≤ sliceNat := by dsimp [sliceNat]; omega
          have hslice_lt : sliceNat < 2 ^ 64 := by dsimp [sliceNat]; omega
          refine wp_jnz_false (bv64_ult_ofNat_false hslice_lt (by omega)
            (by omega : na ≤ sliceNat)) ?_; c0_step
          let bufRes := scr; let bufBase := scr + 8#64 * BitVec.ofNat 64 sliceNat
          let bufTmp := scr + 16#64 * BitVec.ofNat 64 sliceNat
          let bufProd := scr + 24#64 * BitVec.ofNat 64 sliceNat
          have hbufBase : bufBase = scr + BitVec.ofNat 64 (8 * sliceNat) :=
            bv64_mul_off_eq scr 8 sliceNat 1 hslice_lt rfl |>.trans (by simp)
          have hbufTmp : bufTmp = scr + BitVec.ofNat 64 (8 * (sliceNat + sliceNat)) :=
            (bv64_mul_off_eq scr 16 sliceNat 2 hslice_lt rfl).trans
              (by simp [show 2 * sliceNat = sliceNat + sliceNat by omega])
          have hbufProd : bufProd = scr + BitVec.ofNat 64 (8 * (sliceNat + sliceNat + sliceNat)) :=
            (bv64_mul_off_eq scr 24 sliceNat 3 hslice_lt rfl).trans
              (by simp [show 3 * sliceNat = sliceNat + sliceNat + sliceNat by omega])
          have hsplit4 := array64_split4 scr scrLimbs sliceNat sliceNat sliceNat
            (by dsimp [sliceNat]; omega)
          let sRes0 := scrLimbs.take sliceNat
          let sBase0 := (scrLimbs.drop sliceNat).take sliceNat
          let sTmp0 := (scrLimbs.drop (sliceNat + sliceNat)).take sliceNat
          let sProd0 := scrLimbs.drop (sliceNat + sliceNat + sliceNat)
          have hsRes0_len : sRes0.length = sliceNat := by dsimp [sRes0, sliceNat]; simp; omega
          have hsBase0_len : sBase0.length = sliceNat := by
            dsimp [sBase0, sliceNat]; rw [List.length_take, List.length_drop]; omega
          have hsTmp0_len : sTmp0.length = sliceNat := by
            dsimp [sTmp0, sliceNat]; rw [List.length_take, List.length_drop]; omega
          have hsProd0_len : sProd0.length = scrLimbs.length - 3 * sliceNat := by
            dsimp [sProd0]; rw [List.length_drop]; omega
          let R_loop : Mem 64 → Prop :=
            rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ lcnfHeap objs ⋆ R
          have hm_split : (array64 bufRes sRes0 ⋆ array64 bufBase sBase0 ⋆
              array64 bufTmp sTmp0 ⋆ array64 bufProd sProd0 ⋆ R_loop) m := by
            rw [hsplit4] at hm; rw [hbufBase, hbufTmp, hbufProd]
            dsimp only [R_loop, bufRes, sRes0, sBase0, sTmp0, sProd0]
            simp only [Nat.add_assoc] at hm ⊢; sep_use hm
          have hm_st : (array64 bufRes sRes0 ⋆ (array64 bufBase sBase0 ⋆ array64 bufTmp sTmp0 ⋆
              array64 bufProd sProd0 ⋆ R_loop)) m := by sep_use hm_split
          refine wp_store_array64 (xs := sRes0) (i := 0) (v := Arg.imm 1#64) (base := bufRes)
            (by simp [bufRes]) (by dsimp [tn] at htn_pos; omega) hm_st ?_
          intro m1 hm1
          let sRes1 := sRes0.set 0 1#64
          have hsRes1_len : sRes1.length = sliceNat := by simp [sRes1, hsRes0_len]
          have hsRes1_val : limbsVal (sRes1.take 1) = 1 :=
            limbsVal_take_one_set0 (by dsimp [tn] at htn_pos; omega)
          have hm1_load : (lcnfHeap objs ⋆ array64 bufBase sBase0 ⋆ (array64 bufRes sRes1 ⋆
              array64 bufTmp sTmp0 ⋆ array64 bufProd sProd0 ⋆ (rtC0Inv rt st ⋆
              cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ R))) m1 := by
            dsimp only [R_loop] at hm1; dsimp only [sRes1]; sep_use hm1
          apply bn_load_nat_call_wp hna (by omega) hm1_load
          intro sBase1 m2 hsBase1_len hsBase1_val _ hm2
          let PowInv : Tup Val [i64, i64, i64] → Mem 64 → Prop := fun ys mL =>
            match ys with
            | (expBV, rnBV, bnBV, ()) => ∃ resVal baseVal sResL sBaseL sTmpL sProdL,
              0 < resVal ∧ 0 < baseVal ∧ resVal * baseVal ^ expBV.toNat = aVal ^ bVal ∧
              rnBV = BitVec.ofNat 64 (limbLenNat resVal) ∧
              bnBV = BitVec.ofNat 64 (limbLenNat baseVal) ∧
              limbLenNat resVal ≤ tn ∧ limbLenNat baseVal ≤ tn ∧ sResL.length = sliceNat ∧
              sBaseL.length = sliceNat ∧ sTmpL.length = sliceNat ∧
              sProdL.length = scrLimbs.length - 3 * sliceNat ∧
              limbsVal (sResL.take (limbLenNat resVal)) = resVal ∧
              limbsVal (sBaseL.take (limbLenNat baseVal)) = baseVal ∧
              (array64 bufRes sResL ⋆ array64 bufBase sBaseL ⋆ array64 bufTmp sTmpL ⋆
               array64 bufProd sProdL ⋆ R_loop) mL
          let μ : Tup Val [i64, i64, i64] → Mem 64 → Nat := fun ys _ => ys.1.toNat
          apply wp_loop_inv PowInv μ
          · intro J hJ; rw [wp_jump]; apply hJ
            refine ⟨1, aVal, sRes1, sBase1, sTmp0, sProd0, by decide, by omega, ?_, ?_, rfl, ?_,
              hna_le_tn, hsRes1_len, ?_, hsTmp0_len, hsProd0_len, ?_, ?_, ?_⟩
            · simp [BitVec.toNat_ofNat]
            · simp [limbLenNat_eq_one]
            · simp [limbLenNat_eq_one, htn_pos]
            · omega
            · simpa [limbLenNat_eq_one] using hsRes1_val
            · simpa [na] using hsBase1_val
            · dsimp [R_loop]; sep_use hm2
          · rintro J ⟨expBV, rnBV, bnBV, ⟨⟩⟩ mL ⟨resVal, baseVal, sResL, sBaseL, sTmpL, sProdL,
              hres_pos, hbase_pos, heq, hrn_eq, hbn_eq, hrn_le, hbn_le, hsResL, hsBaseL, hsTmpL,
              hsProdL, hresVal, hbaseVal, hmL⟩ hrec
            dsimp only; c0_step
            by_cases hexp0 : expBV.toNat = 0
            · refine wp_jnz_false (by rw [BitVec.ult]; simp [hexp0]) ?_
              have hres_final : resVal = aVal ^ bVal := by
                rw [hexp0, Nat.pow_zero, Nat.mul_one] at heq; exact heq
              have hrn_tn : limbLenNat resVal = tn := by dsimp [tn]; rw [hres_final]
              have hrn_toNat : rnBV.toNat = tn := by
                rw [hrn_eq, hrn_tn, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : tn < 2 ^ 64)]
              have hval_take : limbsVal (sResL.take rnBV.toNat) = aVal ^ bVal := by
                rw [hrn_toNat, ← hrn_tn, ← hres_final]; exact hresVal
              have hm_from : (rtC0Inv rt st ⋆ array64 bufRes sResL ⋆ lcnfHeap objs ⋆
                  (array64 bufBase sBaseL ⋆ array64 bufTmp sTmpL ⋆ array64 bufProd sProdL ⋆
                  cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ R)) mL := by
                dsimp [R_loop] at hmL; sep_use hmL
              apply bn_nat_from_limbs_call_wp (by omega) (by omega) h48 (fun hge => by
                have htl := limbLenNat_trimLenLoop (xs := sResL) (n := rnBV.toNat) (by omega)
                rw [hval_take] at htl hge; change _ ∨ _; rw [← htl]; exact halloc hge) hm_from
              intro res st' objs' m' hmeta hrem hb' hnat_res hsmall hbig hm'
              rw [wp_ret]; rw [hval_take] at hnat_res hsmall hbig
              let scrLimbs' := sResL ++ sBaseL ++ sTmpL ++ sProdL
              have hlen_scr' : scrLimbs'.length = scrLimbs.length := by
                dsimp [scrLimbs']; simp only [List.length_append, hsResL, hsBaseL, hsTmpL, hsProdL]
                omega
              have hjoin := array64_join4 scr sResL sBaseL sTmpL sProdL sliceNat sliceNat sliceNat
                hsResL hsBaseL hsTmpL
              have hm'_fin : (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' := by
                unfold bigNumRtInv; rw [← hjoin, ← hbufBase, ← hbufTmp, ← hbufProd, hlen_scr']
                sep_use hm'
              have hmem := objs_mem_of_from_limbs hsmall hbig
              exact hpost res st' scrLimbs' objs' m' hmeta hrem
                (BigNumRtWf.with_state_len ⟨h48, hrtb, hscr0, hscrm, hlen64, hscr64⟩ hb' hlen_scr')
                hnat_res (fun o ho _ => hmem o ho) (fun o ho _ => hmem o ho) hm'_fin
            · have hexp_pos : 0 < expBV.toNat := Nat.pos_of_ne_zero hexp0
              refine wp_jnz_true (by rw [BitVec.ult]; simp [hexp_pos]) ?_
              let PowMid1 : Tup Val [i64] → Mem 64 → Prop := fun ys1 m1 =>
                ∃ resVal1 sRes1 sProd1, 0 < resVal1 ∧
                  resVal1 * baseVal ^ (2 * (expBV.toNat / 2)) = aVal ^ bVal ∧
                  ys1.1 = BitVec.ofNat 64 (limbLenNat resVal1) ∧ limbLenNat resVal1 ≤ tn ∧
                  sRes1.length = sliceNat ∧ sProd1.length = scrLimbs.length - 3 * sliceNat ∧
                  limbsVal (sRes1.take (limbLenNat resVal1)) = resVal1 ∧
                  (array64 bufRes sRes1 ⋆ array64 bufBase sBaseL ⋆ array64 bufTmp sTmpL ⋆
                   array64 bufProd sProd1 ⋆ R_loop) m1
              apply wp_join_group PowMid1
              · rintro J1 ⟨rn1BV, ⟨⟩⟩ m1 ⟨resVal1, sRes1, sProd1, hres1_pos, heq1, hrn1_eq,
                  hrn1_le, hsRes1, hsProd1, hres1Val, hm1⟩
                c0_step
                have hnext_eq : expBV >>> 1 = BitVec.ofNat 64 (expBV.toNat / 2) := by
                  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ushiftRight]
                  simp [Nat.shiftRight_eq_div_pow]
                rw [hnext_eq]
                let nextExp := expBV.toNat / 2
                let PowMid2 : Tup Val [i64] → Mem 64 → Prop := fun ys2 m2 =>
                  ∃ baseVal2 sBase2 sTmp2 sProd2, 0 < baseVal2 ∧
                    resVal1 * baseVal2 ^ nextExp = aVal ^ bVal ∧
                    ys2.1 = BitVec.ofNat 64 (limbLenNat baseVal2) ∧ limbLenNat baseVal2 ≤ tn ∧
                    sBase2.length = sliceNat ∧ sTmp2.length = sliceNat ∧
                    sProd2.length = scrLimbs.length - 3 * sliceNat ∧
                    limbsVal (sBase2.take (limbLenNat baseVal2)) = baseVal2 ∧
                    (array64 bufRes sRes1 ⋆ array64 bufBase sBase2 ⋆ array64 bufTmp sTmp2 ⋆
                     array64 bufProd sProd2 ⋆ R_loop) m2
                apply wp_join_group PowMid2
                · rintro J2 ⟨bn2BV, ⟨⟩⟩ m2 ⟨baseVal2, sBase2, sTmp2, sProd2, hbase2_pos, heq2,
                    hbn2_eq, hbn2_le, hsBase2, hsTmp2, hsProd2, hbase2Val, hm2⟩
                  simp only [Blocks.get]; rw [wp_jump]; apply hrec
                  · dsimp only [μ, vals, Arg.val]
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [nextExp]; omega)]; omega
                  · refine ⟨resVal1, baseVal2, sRes1, sBase2, sTmp2, sProd2, hres1_pos, hbase2_pos,
                      ?_, hrn1_eq, hbn2_eq, hrn1_le, hbn2_le, hsRes1, hsBase2, hsTmp2, hsProd2,
                      hres1Val, hbase2Val, hm2⟩
                    dsimp only [Arg.val]
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [nextExp]; omega)]
                    exact heq2
                · intro J2 hJ2
                  exact bn_nat_pow_sq_step Q X J2 rt bufBase bufTmp bufProd bnBV sliceNat
                    (scrLimbs.length - 3 * sliceNat) nextExp tn resVal1 baseVal aVal bVal sBaseL
                    sTmpL sProd1 (array64 bufRes sRes1 ⋆ R_loop) m1 hres1_pos hbase_pos heq1
                    (Nat.le_refl _) limbLenNat_lt_pow hbn_eq hbn_le hslice_ge hslice_lt
                    (by dsimp [sliceNat]; omega) (by omega) (by dsimp [nextExp]; omega) hsBaseL
                    hsTmpL hsProd1 hbaseVal (by sep_use hm1)
                    (fun bv2 sb2 st2 sp2 m2 hp2 he2 hle2 hsb2 hst2 hsp2 hv2 hm2 =>
                      hJ2 (BitVec.ofNat 64 (limbLenNat bv2), ()) m2
                        ⟨bv2, sb2, st2, sp2, hp2, he2, rfl, hle2, hsb2, hst2, hsp2, hv2,
                          by sep_use hm2⟩)
              · intro J1 hJ1; c0_step
                by_cases hodd : expBV.toNat % 2 = 1
                · have hne0 : (expBV &&& 1#64 != 0#64) = true := by
                    simp only [bne_iff_ne, ne_eq]; intro h
                    have hto := congrArg BitVec.toNat h
                    simp [BitVec.toNat_and, Nat.and_one_is_mod] at hto; omega
                  refine wp_jnz_true hne0 ?_
                  have hrnbn_le : limbLenNat resVal + limbLenNat baseVal ≤ sliceNat := by
                    have hrb_le : resVal * baseVal ≤ aVal ^ bVal :=
                      Nat.le_trans (Nat.mul_le_mul_left resVal (by
                        simpa using Nat.pow_le_pow_right hbase_pos
                          (show 1 ≤ expBV.toNat by omega))) (Nat.le_of_eq heq)
                    have := limbLenNat_add_le_of_mul_lt hres_pos hbase_pos
                      (Nat.lt_of_le_of_lt hrb_le limbLenNat_lt_pow); omega
                  have hrn_to : rnBV.toNat = limbLenNat resVal := by
                    rw [hrn_eq, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : limbLenNat resVal < 2 ^ 64)]
                  have hbn_to : bnBV.toNat = limbLenNat baseVal := by
                    rw [hbn_eq, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : limbLenNat baseVal < 2 ^ 64)]
                  c0_let_simp
                  have hadd_rb : rnBV + bnBV = BitVec.ofNat 64 (limbLenNat resVal +
                      limbLenNat baseVal) := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_add, hrn_to, hbn_to, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
                      (by omega : limbLenNat resVal + limbLenNat baseVal < 2 ^ 64)]
                  have hult_rb : BitVec.ult (BitVec.ofNat 64 sliceNat) (rnBV + bnBV) = false := by
                    rw [hadd_rb]; exact bv64_ult_ofNat_false hslice_lt (by omega) hrnbn_le
                  refine wp_jnz_false hult_rb ?_
                  have hm_mul : (array64 bufRes sResL ⋆ array64 bufBase sBaseL ⋆
                      array64 bufProd sProdL ⋆ (array64 bufTmp sTmpL ⋆ R_loop)) mL := by sep_use hmL
                  apply bn_mul_call_wp (by rw [hrn_to]; omega) (by rw [hbn_to]; omega)
                    (by rw [hrn_to, hbn_to]; omega) (by rw [hrn_to, hbn_to]; omega) hm_mul
                  intro sProd1 mL1 hsProd1_len hprod1_le hprod1_val hmL1
                  rw [hrn_to, hbn_to, hresVal, hbaseVal] at hprod1_le hprod1_val ⊢; dsimp only
                  have hrb_le : resVal * baseVal ≤ aVal ^ bVal :=
                    Nat.le_trans (Nat.mul_le_mul_left resVal (by
                      simpa using Nat.pow_le_pow_right hbase_pos
                        (show 1 ≤ expBV.toNat by omega))) (Nat.le_of_eq heq)
                  have hll_rb_le : limbLenNat (resVal * baseVal) ≤ tn := limbLenNat_mono hrb_le
                  have hll_rb_to : (BitVec.ofNat 64 (limbLenNat (resVal * baseVal))).toNat =
                      limbLenNat (resVal * baseVal) := by
                    rw [BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : limbLenNat (resVal * baseVal) < 2 ^ 64)]
                  have hm_cp : (array64 bufRes sResL ⋆ array64 bufProd sProd1 ⋆
                      (array64 bufBase sBaseL ⋆ array64 bufTmp sTmpL ⋆ R_loop)) mL1 := by
                    sep_use hmL1
                  apply bn_copy_call_wp (by rw [hll_rb_to]; omega) (by rw [hll_rb_to]; omega) hm_cp
                  intro m1 hm1
                  let sRes1 := sProd1.take (BitVec.ofNat 64 (limbLenNat (resVal *
                    baseVal))).toNat ++ sResL.drop (BitVec.ofNat 64 (limbLenNat (resVal *
                    baseVal))).toNat
                  have hsRes1_len : sRes1.length = sliceNat := by
                    dsimp [sRes1]; simp [hsProd1_len, hsProdL, hsResL, hll_rb_to]; omega
                  have hsRes1_val : limbsVal (sRes1.take (limbLenNat (resVal * baseVal))) =
                      resVal * baseVal := by
                    dsimp only [sRes1]
                    exact limbsVal_take_append_prefix hll_rb_to (by omega) hprod1_val
                  rw [wp_jump]; apply hJ1
                  refine ⟨resVal * baseVal, sRes1, sProd1, Nat.mul_pos hres_pos hbase_pos, ?_, rfl,
                    hll_rb_le, hsRes1_len, (by omega), hsRes1_val, by sep_use hm1⟩
                  rw [show expBV.toNat = 2 * (expBV.toNat / 2) + 1 by omega, Nat.pow_succ] at heq
                  rw [← heq]; ac_rfl
                · have heq0 : (expBV &&& 1#64 != 0#64) = false := by
                    have he : (expBV &&& 1#64) = 0#64 := by
                      apply BitVec.eq_of_toNat_eq
                      simp [BitVec.toNat_and, Nat.and_one_is_mod]; omega
                    rw [he]; decide
                  refine wp_jnz_false heq0 ?_; rw [wp_jump]; apply hJ1
                  refine ⟨resVal, sResL, sProdL, hres_pos, ?_, hrn_eq, hrn_le, hsResL, hsProdL,
                    hresVal, hmL⟩
                  rw [show 2 * (expBV.toNat / 2) = expBV.toNat by omega]; exact heq

private theorem bn_nat_gcd_swap_step (Q : Post [i64]) (X : XPost) (J : Cont [i64, i64])
    (bufA bufB bufR curNaBV curNbBV : BitVec 64) (aCur bCur maxn rLen : Nat)
    (sA sB sR : List (BitVec 64)) (R_swap : Mem 64 → Prop) (mL : Mem 64)
    (hna_le : limbLenNat aCur ≤ maxn) (hnb_le : limbLenNat bCur ≤ maxn)
    (hcurNa_to : curNaBV.toNat = limbLenNat aCur)
    (hcurNb_to : curNbBV.toNat = limbLenNat bCur) (hrLen_ge : maxn ≤ rLen)
    (hsA : sA.length = maxn) (hsB : sB.length = maxn) (hsR : sR.length = rLen)
    (ha_val : limbsVal (sA.take (limbLenNat aCur)) = aCur)
    (hb_val : limbsVal (sB.take (limbLenNat bCur)) = bCur)
    (hmL : (array64 bufA sA ⋆ array64 bufB sB ⋆ array64 bufR sR ⋆ R_swap) mL)
    (hJ : ∀ (sA2 sB3 sR1 : List (BitVec 64)) (mL3 : Mem 64),
      sA2.length = maxn → sB3.length = maxn → sR1.length = rLen →
      limbsVal (sA2.take (limbLenNat bCur)) = bCur →
      limbsVal (sB3.take (limbLenNat aCur)) = aCur →
      (array64 bufA sA2 ⋆ array64 bufB sB3 ⋆ array64 bufR sR1 ⋆ R_swap) mL3 →
      J (curNbBV, curNaBV, ()) mL3) :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
        (Arg.var bufR, Arg.var bufA, Arg.var curNaBV, ()) fun _ =>
        Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
          (Arg.var bufA, Arg.var bufB, Arg.var curNbBV, ()) fun _ =>
          Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
            (Arg.var bufB, Arg.var bufR, Arg.var curNaBV, ()) fun _ =>
            Expr.jump J (Arg.var curNbBV, Arg.var curNaBV, ())) mL := by
  have hm_cp1 : (array64 bufR sR ⋆ array64 bufA sA ⋆ (array64 bufB sB ⋆ R_swap)) mL := by
    sep_use hmL
  apply bn_copy_call_wp (by rw [hcurNa_to]; omega) (by rw [hcurNa_to]; omega) hm_cp1
  intro mL1 hmL1
  let sR1 := sA.take curNaBV.toNat ++ sR.drop curNaBV.toNat
  have hsR1_len : sR1.length = rLen := by dsimp [sR1]; simp [hsA, hsR, hcurNa_to]; omega
  have hsR1_val : limbsVal (sR1.take (limbLenNat aCur)) = aCur :=
    limbsVal_take_append_prefix hcurNa_to (by omega) ha_val
  have hm_cp2 : (array64 bufA sA ⋆ array64 bufB sB ⋆ (array64 bufR sR1 ⋆ R_swap)) mL1 := by
    sep_use hmL1
  apply bn_copy_call_wp (by rw [hcurNb_to]; omega) (by rw [hcurNb_to]; omega) hm_cp2
  intro mL2 hmL2
  let sA2 := sB.take curNbBV.toNat ++ sA.drop curNbBV.toNat
  have hsA2_len : sA2.length = maxn := by dsimp [sA2]; simp [hsB, hsA, hcurNb_to]; omega
  have hsA2_val : limbsVal (sA2.take (limbLenNat bCur)) = bCur :=
    limbsVal_take_append_prefix hcurNb_to (by omega) hb_val
  have hm_cp3 : (array64 bufB sB ⋆ array64 bufR sR1 ⋆ (array64 bufA sA2 ⋆ R_swap)) mL2 := by
    sep_use hmL2
  apply bn_copy_call_wp (by rw [hcurNa_to]; omega) (by rw [hcurNa_to]; omega) hm_cp3
  intro mL3 hmL3
  let sB3 := sR1.take curNaBV.toNat ++ sB.drop curNaBV.toNat
  have hsB3_len : sB3.length = maxn := by dsimp [sB3]; simp [hsR1_len, hsB, hcurNa_to]; omega
  have hsB3_val : limbsVal (sB3.take (limbLenNat aCur)) = aCur :=
    limbsVal_take_append_prefix hcurNa_to (by omega) hsR1_val
  rw [wp_jump]
  exact hJ sA2 sB3 sR1 mL3 hsA2_len hsB3_len hsR1_len hsA2_val hsB3_val (by sep_use hmL3)

private theorem bn_nat_gcd_div_step (Q : Post [i64]) (X : XPost) (J : Cont [i64, i64])
    (bufA bufB bufQ bufR curNaBV curNbBV : BitVec 64) (aCur bCur maxn rLen : Nat)
    (sA sB sQ sR : List (BitVec 64)) (R_loop : Mem 64 → Prop) (mL : Mem 64)
    (hbCur_pos : 0 < bCur) (hna_le : limbLenNat aCur ≤ maxn) (hnb_le : limbLenNat bCur ≤ maxn)
    (hnb_pos' : 0 < limbLenNat bCur) (hna_pos' : 0 < limbLenNat aCur)
    (hcurNa_to : curNaBV.toNat = limbLenNat aCur)
    (hcurNb_to : curNbBV.toNat = limbLenNat bCur)
    (hmax64 : maxn < 2 ^ 64) (hrLen_ge : maxn ≤ rLen)
    (hsA : sA.length = maxn) (hsB : sB.length = maxn)
    (hsQ : sQ.length = maxn) (hsR : sR.length = rLen)
    (ha_val : limbsVal (sA.take (limbLenNat aCur)) = aCur)
    (hb_val : limbsVal (sB.take (limbLenNat bCur)) = bCur)
    (hmL : (array64 bufA sA ⋆ array64 bufB sB ⋆ array64 bufQ sQ ⋆ array64 bufR sR ⋆ R_loop) mL)
    (hJ : ∀ (sA2 sB3 sQ1 sR1 : List (BitVec 64)) (mL3 : Mem 64),
      limbLenNat (aCur % bCur) ≤ maxn → sA2.length = maxn → sB3.length = maxn →
      sQ1.length = maxn → sR1.length = rLen → limbsVal (sA2.take (limbLenNat bCur)) = bCur →
      limbsVal (sB3.take (limbLenNat (aCur % bCur))) = aCur % bCur →
      (array64 bufA sA2 ⋆ array64 bufB sB3 ⋆ array64 bufQ sQ1 ⋆ array64 bufR sR1 ⋆ R_loop) mL3 →
      J (curNbBV, BitVec.ofNat 64 (limbLenNat (aCur % bCur)), ()) mL3) :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64, i64, i64, i64, i64]) (bs := []) "bn_divmod"
        (Arg.var bufA, Arg.var curNaBV, Arg.var bufB, Arg.var curNbBV, Arg.var bufQ, Arg.var bufR,
          ())
        fun _ =>
        Expr.call (as := [i64, i64]) (bs := [i64]) "bn_trim" (Arg.var bufR, Arg.var curNbBV, ())
          fun p =>
          Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
            (Arg.var bufA, Arg.var bufB, Arg.var curNbBV, ()) fun _ =>
            Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
              (Arg.var bufB, Arg.var bufR, Arg.var p.fst, ()) fun _ =>
              Expr.jump J (Arg.var curNbBV, Arg.var p.fst, ())) mL := by
  have hb_last_nz : sB[curNbBV.toNat - 1]! ≠ 0#64 := by
    rw [hcurNb_to]; exact limb_last_nonzero_of_limbLenNat (by omega) hnb_pos' (by rw [hb_val])
  apply bn_divmod_call_wp (by rw [hcurNa_to]; exact hna_pos') (by rw [hcurNb_to]; exact hnb_pos')
    (by rw [hcurNa_to]; omega) (by rw [hcurNb_to]; omega) (by rw [hcurNa_to]; omega)
    (by rw [hcurNb_to]; omega) hb_last_nz hmL
  intro sQ1 sR1 mL1 hsQ1_len hsR1_len _ hrem_val hmL1
  rw [hcurNa_to, hcurNb_to, ha_val, hb_val] at hrem_val
  have hm_tr : (array64 bufR sR1 ⋆ (array64 bufA sA ⋆ array64 bufB sB ⋆ array64 bufQ sQ1 ⋆
      R_loop)) mL1 := by sep_use hmL1
  apply bn_trim_call_wp (by rw [hcurNb_to]; omega) hm_tr; dsimp only
  have htl_rem : trimLenLoop sR1 curNbBV.toNat = limbLenNat (aCur % bCur) := by
    rw [← hrem_val, ← hcurNb_to]
    exact (limbLenNat_trimLenLoop (xs := sR1) (n := curNbBV.toNat) (by omega)).symm
  rw [htl_rem]
  have hrem_ll_le : limbLenNat (aCur % bCur) ≤ maxn :=
    Nat.le_trans (limbLenNat_mono (Nat.le_of_lt (Nat.mod_lt aCur hbCur_pos))) hnb_le
  have hrem_ll_to : (BitVec.ofNat 64 (limbLenNat (aCur % bCur))).toNat =
      limbLenNat (aCur % bCur) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : limbLenNat (aCur % bCur) < 2 ^ 64)]
  have hrem_take : limbsVal (sR1.take (limbLenNat (aCur % bCur))) = aCur % bCur := by
    rw [← htl_rem, ← hrem_val, ← hcurNb_to]; exact limbsVal_trimLenLoop sR1 curNbBV.toNat (by omega)
  have hm_cp1 : (array64 bufA sA ⋆ array64 bufB sB ⋆ (array64 bufQ sQ1 ⋆ array64 bufR sR1 ⋆
      R_loop)) mL1 := by sep_use hmL1
  apply bn_copy_call_wp (by rw [hcurNb_to]; omega) (by rw [hcurNb_to]; omega) hm_cp1
  intro mL2 hmL2
  let sA2 := sB.take curNbBV.toNat ++ sA.drop curNbBV.toNat
  have hsA2_len : sA2.length = maxn := by dsimp [sA2]; simp [hsB, hsA, hcurNb_to]; omega
  have hsA2_val : limbsVal (sA2.take (limbLenNat bCur)) = bCur :=
    limbsVal_take_append_prefix hcurNb_to (by omega) hb_val
  have hm_cp2 : (array64 bufB sB ⋆ array64 bufR sR1 ⋆ (array64 bufA sA2 ⋆ array64 bufQ sQ1 ⋆
      R_loop)) mL2 := by sep_use hmL2
  apply bn_copy_call_wp (by rw [hrem_ll_to]; omega) (by rw [hrem_ll_to]; omega) hm_cp2
  intro mL3 hmL3
  let sB3 := sR1.take (BitVec.ofNat 64 (limbLenNat (aCur % bCur))).toNat ++
    sB.drop (BitVec.ofNat 64 (limbLenNat (aCur % bCur))).toNat
  have hsB3_len : sB3.length = maxn := by
    dsimp [sB3]; simp [hsR1_len, hsR, hsB, hrem_ll_to]; omega
  have hsB3_val : limbsVal (sB3.take (limbLenNat (aCur % bCur))) = aCur % bCur :=
    limbsVal_take_append_prefix hrem_ll_to (by omega) hrem_take
  rw [wp_jump]
  exact hJ sA2 sB3 sQ1 sR1 mL3 hrem_ll_le hsA2_len hsB3_len (by omega) (by omega)
    hsA2_val hsB3_val (by sep_use hmL3)

private theorem bn_nat_gcd_single_wp {rt x : BitVec 64} {aVal bVal xVal : Nat}
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hwf : BigNumRtWf rt st scr scrLimbs) (hx : natRep x xVal objs)
    (hx_scr : limbLenNat xVal ≤ scrLimbs.length)
    (hx_alloc : 2 ^ 63 ≤ xVal → canAllocBytes st (16 + 8 * limbLenNat xVal))
    (hx_gcd : Nat.gcd aVal bVal = xVal)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hpost : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natRep res (Nat.gcd aVal bVal) objs' → (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    wp rtR1Env Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "bn_require_scratch"
        (Arg.var rt, Arg.var (BitVec.ofNat 64 (limbLenNat xVal)), ()) fun p =>
        Expr.call (as := [i64, i64]) (bs := [i64]) "bn_load_nat"
          (Arg.var x, Arg.var p.fst, ()) fun p_8 =>
          Expr.call (as := [i64, i64, i64]) (bs := [i64]) "bn_nat_from_limbs"
            (Arg.var rt, Arg.var p.fst, Arg.var p_8.fst, ()) fun p => Expr.ret (Arg.var p.fst, ()))
      m := by
  let nx := limbLenNat xVal
  have hnx_max : nx ≤ mpzMaxLimbs := limbLenNat_le_max_of_natRep hx
  have hnx_lt : nx < 2 ^ 64 := by unfold mpzMaxLimbs at hnx_max; omega
  have hnx_mod : (BitVec.ofNat 64 nx).toNat = nx := Nat.mod_eq_of_lt hnx_lt
  rcases hwf with ⟨h48, hrtb, hscr0, hscrm, hlen64, hscr64⟩
  unfold bigNumRtInv at hm
  have hm_req : (cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      (rtC0Inv rt st ⋆ array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R)) m := by sep_use hm
  have hnx_req : (BitVec.ofNat 64 (limbLenNat xVal)).toNat ≤
      (BitVec.ofNat 64 scrLimbs.length).toNat := by
    rw [show limbLenNat xVal = nx from rfl, hnx_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64]
    exact hx_scr
  apply bn_require_scratch_call_wp hscr0 hnx_req hm_req
  dsimp only
  have hm_ld : (lcnfHeap objs ⋆ array64 scr scrLimbs ⋆
      (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
       cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ R)) m := by sep_use hm
  apply bn_load_nat_call_wp hx hx_scr hm_ld
  intro scrLimbs' m' hlen' hval' _ hm'; dsimp only
  have hm'_from : (rtC0Inv rt st ⋆ array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆
      (cell64 (rt + 33672#64) scr ⋆
       cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ R)) m' := by sep_use hm'
  apply bn_nat_from_limbs_call_wp (by rw [hnx_mod]; omega)
    (by rw [hnx_mod]; exact hnx_max) h48
    (fun hge => by
      have htl := limbLenNat_trimLenLoop (xs := scrLimbs') (n := nx) (by omega)
      rw [hnx_mod, hval'] at hge; rw [hval'] at htl; rw [hnx_mod]
      change _ ∨ _; rw [← htl]; exact hx_alloc hge)
    hm'_from
  intro res st' objs'' m'' hmeta hrem hb' hrep' hsmall hbig hm''
  rw [wp_ret]; rw [hnx_mod, hval'] at hrep' hsmall hbig
  have hwf' := BigNumRtWf.with_state_len ⟨h48, hrtb, hscr0, hscrm, hlen64, hscr64⟩ hb' hlen'
  have hm''_fin : (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs'' ⋆ R) m'' := by
    unfold bigNumRtInv; rw [hlen']; sep_use hm''
  exact hpost res st' scrLimbs' objs'' m'' hmeta hrem hwf'
    (by simpa [hx_gcd] using hrep') (objs_mem_of_from_limbs hsmall hbig) hm''_fin

theorem bn_nat_gcd_wp (xs : Tup Val [i64, i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (hspec : bnNatGcdSpec xs m Q X) :
    Func.wp rtR1Env bn_nat_gcd.body xs m Q X := by
  rcases xs with ⟨rt, a, b, ⟨⟩⟩
  rcases hspec with ⟨st, scr, scrLimbs, objs, aVal, bVal, R, hwf, hna, hnb, hgcd, hm, hpost⟩
  have h48 : st.Bounded48 := hwf.1
  have hscr0 : scr ≠ 0#64 := hwf.2.2.1
  have hlen64 : scrLimbs.length < 2 ^ 64 := hwf.2.2.2.2.1
  unfold Func.wp bn_nat_gcd bn_nat_gcd_body; dsimp only
  let na := limbLenNat aVal; let nb := limbLenNat bVal
  have hna_max : na ≤ 33554429 := show na ≤ mpzMaxLimbs from limbLenNat_le_max_of_natRep hna
  have hnb_max : nb ≤ 33554429 := show nb ≤ mpzMaxLimbs from limbLenNat_le_max_of_natRep hnb
  have hm_a : (lcnfHeap objs ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R)) m := by sep_use hm
  apply bn_nat_len_call_wp hna hm_a
  have hm_b : (lcnfHeap objs ⋆ (bigNumRtInv rt st scr scrLimbs ⋆ R)) m := by sep_use hm
  apply bn_nat_len_call_wp hnb hm_b
  apply wp_join_group (fun _ _ => False)
  · rintro J _ _ hF; exact hF.elim
  · intro _ _; c0_step
    refine wp_jnz_false (bv64_ult_ofNat_false (by decide) (by omega) hna_max) ?_; c0_step
    refine wp_jnz_false (bv64_ult_ofNat_false (by decide) (by omega) hnb_max) ?_
    let NonBothZero : Tup Val [] → Mem 64 → Prop := fun _ mG =>
      ¬ (aVal = 0 ∧ bVal = 0) ∧ (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) mG
    apply wp_join_group NonBothZero
    · rintro _ ⟨⟩ mG ⟨hnot00, hmG⟩; c0_step
      by_cases ha0 : aVal = 0
      · have hna0 : na = 0 := by dsimp [na]; rw [ha0, limbLenNat_zero]
        have hb0 : bVal ≠ 0 := fun hb => hnot00 ⟨ha0, hb⟩
        have hgcd_b : nb ≤ scrLimbs.length ∧ (2 ^ 63 ≤ bVal →
            canAllocBytes st (16 + 8 * nb)) := by
          rcases hgcd with ⟨_, hb_eq⟩ | ⟨_, _, h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact absurd hb_eq hb0
          · exact ⟨h1, h2⟩
          · exact absurd ha0 h1
          · exact absurd ha0 h1
        refine wp_jnz_true (by simp [na, hna0]) ?_
        exact bn_nat_gcd_single_wp hwf hnb hgcd_b.1 hgcd_b.2
          (by rw [ha0, Nat.gcd_zero_left]) hmG hpost
      · have hna_pos : 0 < na := limbLenNat_pos_iff.mpr (Nat.pos_of_ne_zero ha0)
        refine wp_jnz_false (bv64_beq0_ofNat_false (by omega) hna_pos) ?_; c0_step
        by_cases hb0 : bVal = 0
        · have hnb0 : nb = 0 := by dsimp [nb]; rw [hb0, limbLenNat_zero]
          have hgcd_a : na ≤ scrLimbs.length ∧ (2 ^ 63 ≤ aVal →
              canAllocBytes st (16 + 8 * na)) := by
            rcases hgcd with ⟨ha_eq, _⟩ | ⟨h1, _⟩ | ⟨_, _, h1, h2⟩ | ⟨_, h2, _⟩
            · exact absurd ha_eq ha0
            · exact absurd h1 ha0
            · exact ⟨h1, h2⟩
            · exact absurd hb0 h2
          refine wp_jnz_true (by simp [nb, hnb0]) ?_
          exact bn_nat_gcd_single_wp hwf hna hgcd_a.1 hgcd_a.2
            (by rw [hb0, Nat.gcd_zero_right]) hmG hpost
        · have hnb_pos : 0 < nb := limbLenNat_pos_iff.mpr (Nat.pos_of_ne_zero hb0)
          have hgcd_ab : 4 * max na nb ≤ scrLimbs.length ∧
              (2 ^ 63 ≤ aVal.gcd bVal →
                canAllocBytes st (16 + 8 * limbLenNat (aVal.gcd bVal))) := by
            rcases hgcd with ⟨ha_eq, _⟩ | ⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h1, h2⟩
            · exact absurd ha_eq ha0
            · exact absurd h1 ha0
            · exact absurd h2 hb0
            · exact ⟨h1, h2⟩
          have h4max := hgcd_ab.1; have hg_alloc := hgcd_ab.2
          refine wp_jnz_false (bv64_beq0_ofNat_false (by omega) hnb_pos) ?_
          let maxn := max na nb
          have hmaxn_pos : 0 < maxn := Nat.lt_of_lt_of_le hna_pos (Nat.le_max_left na nb)
          have hmaxn_max : maxn ≤ mpzMaxLimbs := Nat.max_le.mpr ⟨hna_max, hnb_max⟩
          have hmaxn_lt : maxn < 2 ^ 64 := by omega
          let MaxJoin : Tup Val [i64] → Mem 64 → Prop := fun y mJ =>
            y.1 = BitVec.ofNat 64 maxn ∧ mJ = mG
          apply wp_join_group MaxJoin
          · rintro _ ⟨maxnBV, ⟨⟩⟩ mJ ⟨hmaxBV, rfl⟩
            dsimp only at hmaxBV ⊢; rw [hmaxBV]; c0_step
            unfold bigNumRtInv at hmG
            have hm_req : (cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                (rtC0Inv rt st ⋆ array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R)) mJ := by
              sep_use hmG
            apply bn_require_scratch_call_wp hscr0
              (by rw [BitVec.toNat_mul, show (4 : BitVec 64).toNat = 4 by decide,
                BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64,
                Nat.mod_eq_of_lt hmaxn_lt,
                Nat.mod_eq_of_lt (show 4 * maxn < 2 ^ 64 by omega)]; exact h4max) hm_req
            c0_step
            let bufA := scr; let bufB := scr + 8#64 * BitVec.ofNat 64 maxn
            let bufQ := scr + 16#64 * BitVec.ofNat 64 maxn
            let bufR := scr + 24#64 * BitVec.ofNat 64 maxn
            have hbufB : bufB = scr + BitVec.ofNat 64 (8 * maxn) := by
              simpa [bufB, Nat.one_mul] using bv64_mul_off_eq scr 8 maxn 1 hmaxn_lt rfl
            have hbufQ : bufQ = scr + BitVec.ofNat 64 (8 * (maxn + maxn)) := by
              simpa [bufQ, show 2 * maxn = maxn + maxn by omega] using
                bv64_mul_off_eq scr 16 maxn 2 hmaxn_lt rfl
            have hbufR : bufR = scr + BitVec.ofNat 64 (8 * (maxn + maxn + maxn)) := by
              simpa [bufR, show 3 * maxn = maxn + maxn + maxn by omega] using
                bv64_mul_off_eq scr 24 maxn 3 hmaxn_lt rfl
            have hsplit4 := array64_split4 scr scrLimbs maxn maxn maxn (by omega)
            let sA0 := scrLimbs.take maxn; let sB0 := (scrLimbs.drop maxn).take maxn
            let sQ0 := (scrLimbs.drop (maxn + maxn)).take maxn
            let sR0 := scrLimbs.drop (maxn + maxn + maxn)
            have hsA0 : sA0.length = maxn := by dsimp [sA0]; rw [List.length_take]; omega
            have hsB0 : sB0.length = maxn := by
              dsimp [sB0]; rw [List.length_take, List.length_drop]; omega
            have hsQ0 : sQ0.length = maxn := by
              dsimp [sQ0]; rw [List.length_take, List.length_drop]; omega
            have hsR0 : sR0.length = scrLimbs.length - 3 * maxn := by
              dsimp [sR0]; rw [List.length_drop]; omega
            let R_loop : Mem 64 → Prop :=
              rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ lcnfHeap objs ⋆ R
            have hm_lda : (lcnfHeap objs ⋆ array64 bufA sA0 ⋆
                (array64 bufB sB0 ⋆ array64 bufQ sQ0 ⋆ array64 bufR sR0 ⋆
                 (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ R))) mJ := by
              rw [hsplit4, ← hbufB, ← hbufQ, ← hbufR] at hmG
              dsimp only [bufA, sA0, sB0, sQ0, sR0]; sep_use hmG
            apply bn_load_nat_call_wp hna (by omega) hm_lda
            intro sA1 mG1 hsA1_len hsA1_val _ hmG1
            have hm_ldb : (lcnfHeap objs ⋆ array64 bufB sB0 ⋆
                (array64 bufA sA1 ⋆ array64 bufQ sQ0 ⋆ array64 bufR sR0 ⋆
                 (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ R))) mG1 := by
              sep_use hmG1
            apply bn_load_nat_call_wp hnb (by omega) hm_ldb
            intro sB1 mG2 hsB1_len hsB1_val _ hmG2
            let GcdInv : Tup Val [i64, i64] → Mem 64 → Prop := fun ys mL =>
              match ys with
              | (curNaBV, curNbBV, ()) =>
                ∃ aCur bCur sA sB sQ sR,
                  0 < aCur ∧ aCur.gcd bCur = aVal.gcd bVal ∧
                  curNaBV = BitVec.ofNat 64 (limbLenNat aCur) ∧
                  curNbBV = BitVec.ofNat 64 (limbLenNat bCur) ∧
                  limbLenNat aCur ≤ maxn ∧ limbLenNat bCur ≤ maxn ∧
                  sA.length = maxn ∧ sB.length = maxn ∧
                  sQ.length = maxn ∧ sR.length = scrLimbs.length - 3 * maxn ∧
                  limbsVal (sA.take (limbLenNat aCur)) = aCur ∧
                  limbsVal (sB.take (limbLenNat bCur)) = bCur ∧
                  (array64 bufA sA ⋆ array64 bufB sB ⋆
                   array64 bufQ sQ ⋆ array64 bufR sR ⋆ R_loop) mL
            let μ : Tup Val [i64, i64] → Mem 64 → Nat := fun ys mL =>
              readLimbsVal mL bufB ys.2.1.toNat
            apply wp_loop_inv GcdInv μ
            · intro J hJ; rw [wp_jump]; apply hJ
              refine ⟨aVal, bVal, sA1, sB1, sQ0, sR0, Nat.pos_of_ne_zero ha0, rfl, rfl, rfl,
                Nat.le_max_left na nb, Nat.le_max_right na nb, (by omega), (by omega), hsQ0,
                hsR0, hsA1_val, hsB1_val, ?_⟩
              dsimp [R_loop]; sep_use hmG2
            · rintro J ⟨curNaBV, curNbBV, ⟨⟩⟩ mL hinv hrec; c0_step
              rcases hinv with ⟨aCur, bCur, sA, sB, sQ, sR, haCur_pos, hgcd_eq,
                hna_eq, hnb_eq, hna_le, hnb_le, hsA, hsB, hsQ, hsR, ha_val, hb_val, hmL⟩
              have hcurNa_to : curNaBV.toNat = limbLenNat aCur := by
                rw [hna_eq, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : limbLenNat aCur < 2 ^ 64)]
              have hcurNb_to : curNbBV.toNat = limbLenNat bCur := by
                rw [hnb_eq, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : limbLenNat bCur < 2 ^ 64)]
              have hμ_eq : μ (curNaBV, curNbBV, ()) mL = bCur := by
                dsimp [μ]; rw [hcurNb_to]
                have hmL_b : (array64 bufB sB ⋆
                    (array64 bufA sA ⋆ array64 bufQ sQ ⋆ array64 bufR sR ⋆ R_loop)) mL := by
                  sep_use hmL
                rw [readLimbsVal_eq_of_array64 hmL_b (by omega)]; exact hb_val
              by_cases hbCur0 : bCur = 0
              · have hnb0 : limbLenNat bCur = 0 := by rw [hbCur0, limbLenNat_zero]
                refine wp_jnz_false (by rw [hnb_eq, hnb0]; decide) ?_
                have ha_gcd : aCur = aVal.gcd bVal := by
                  rw [← hgcd_eq, hbCur0, Nat.gcd_zero_right]
                have hm_from : (rtC0Inv rt st ⋆ array64 bufA sA ⋆ lcnfHeap objs ⋆
                    (array64 bufB sB ⋆ array64 bufQ sQ ⋆ array64 bufR sR ⋆
                     cell64 (rt + 33672#64) scr ⋆
                     cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ R)) mL := by
                  dsimp [R_loop] at hmL; sep_use hmL
                have ha_take : limbsVal (sA.take curNaBV.toNat) = aVal.gcd bVal := by
                  rw [hcurNa_to, ha_val, ha_gcd]
                apply bn_nat_from_limbs_call_wp (by omega) (by omega) h48
                  (fun hge => by
                    have htl := limbLenNat_trimLenLoop (xs := sA) (n := curNaBV.toNat) (by omega)
                    rw [ha_take] at hge htl; change _ ∨ _; rw [← htl]; exact hg_alloc hge)
                  hm_from
                intro res st' objs' m' hmeta hrem hb' hrep_g hsmall hbig hm'
                rw [wp_ret]; rw [ha_take] at hrep_g hsmall hbig
                let scrLimbs' := sA ++ sB ++ sQ ++ sR
                have hlen_scr' : scrLimbs'.length = scrLimbs.length := by
                  dsimp [scrLimbs']; simp only [List.length_append, hsA, hsB, hsQ, hsR]; omega
                have hwf' := BigNumRtWf.with_state_len hwf hb' hlen_scr'
                have hjoin := array64_join4 scr sA sB sQ sR maxn maxn maxn hsA hsB hsQ
                have hm'_fin : (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' := by
                  unfold bigNumRtInv; rw [← hjoin, ← hbufB, ← hbufQ, ← hbufR, hlen_scr']
                  sep_use hm'
                exact hpost res st' scrLimbs' objs' m' hmeta hrem hwf' hrep_g
                  (objs_mem_of_from_limbs hsmall hbig) hm'_fin
              · have hbCur_pos : 0 < bCur := Nat.pos_of_ne_zero hbCur0
                have hnb_pos' : 0 < limbLenNat bCur := limbLenNat_pos_iff.mpr hbCur_pos
                have hna_pos' : 0 < limbLenNat aCur := limbLenNat_pos_iff.mpr haCur_pos
                refine wp_jnz_true (by
                  rw [hnb_eq]; exact bv64_ult_ofNat_true (by decide) (by omega) hnb_pos') ?_
                have hm_cmp : (array64 bufA sA ⋆ array64 bufB sB ⋆
                    (array64 bufQ sQ ⋆ array64 bufR sR ⋆ R_loop)) mL := by sep_use hmL
                apply bn_cmp_call_wp (by omega) (by omega) hm_cmp
                rw [hcurNa_to, hcurNb_to, ha_val, hb_val]; c0_step; c0_step
                · have hlt_ab : aCur < bCur := Nat.lt_of_not_ge (fun hge => by
                    have hcmp_f : (cmpResult64 aCur bCur).slt 0#64 = false := by
                      unfold cmpResult64; simp [show ¬ aCur < bCur by omega]; split <;> decide
                    rw [hcmp_f] at hc; exact absurd hc (by decide))
                  exact bn_nat_gcd_swap_step Q X J bufA bufB bufR curNaBV curNbBV aCur bCur maxn
                    (scrLimbs.length - 3 * maxn) sA sB sR (array64 bufQ sQ ⋆ R_loop) mL
                    hna_le hnb_le hcurNa_to hcurNb_to (by omega) hsA hsB hsR ha_val hb_val
                    (by sep_use hmL)
                    (fun sA2 sB3 sR1 mL3 hsA2_len hsB3_len hsR1_len hsA2_val hsB3_val hmL3 => by
                      apply hrec
                      · rw [hμ_eq]; dsimp [μ]; rw [hcurNa_to]
                        have hm3_b : (array64 bufB sB3 ⋆ (array64 bufA sA2 ⋆ array64 bufR sR1 ⋆
                            array64 bufQ sQ ⋆ R_loop)) mL3 := by sep_use hmL3
                        rw [readLimbsVal_eq_of_array64 hm3_b (by omega), hsB3_val]; exact hlt_ab
                      · refine ⟨bCur, aCur, sA2, sB3, sQ, sR1, hbCur_pos, ?_, hnb_eq, hna_eq,
                          hnb_le, hna_le, hsA2_len, hsB3_len, hsQ, hsR1_len, hsA2_val, hsB3_val,
                          ?_⟩
                        · rw [Nat.gcd_comm]; exact hgcd_eq
                        · sep_use hmL3)
                · exact bn_nat_gcd_div_step Q X J bufA bufB bufQ bufR curNaBV curNbBV aCur bCur
                    maxn (scrLimbs.length - 3 * maxn) sA sB sQ sR R_loop mL hbCur_pos hna_le
                    hnb_le hnb_pos' hna_pos' hcurNa_to hcurNb_to (by omega) (by omega) hsA hsB hsQ
                    hsR ha_val hb_val hmL
                    (fun sA2 sB3 sQ1 sR1 mL3 hrem_ll_le hsA2_len hsB3_len hsQ1_len hsR1_len
                      hsA2_val hsB3_val hmL3 => by
                      have hrem_ll_to : (BitVec.ofNat 64 (limbLenNat (aCur % bCur))).toNat =
                          limbLenNat (aCur % bCur) := by
                        rw [BitVec.toNat_ofNat,
                          Nat.mod_eq_of_lt (by omega : limbLenNat (aCur % bCur) < 2 ^ 64)]
                      apply hrec
                      · rw [hμ_eq]; dsimp [μ]; rw [hrem_ll_to]
                        have hm3_b : (array64 bufB sB3 ⋆ (array64 bufA sA2 ⋆ array64 bufQ sQ1 ⋆
                            array64 bufR sR1 ⋆ R_loop)) mL3 := by sep_use hmL3
                        rw [readLimbsVal_eq_of_array64 hm3_b (by omega), hsB3_val]
                        exact Nat.mod_lt aCur hbCur_pos
                      · refine ⟨bCur, aCur % bCur, sA2, sB3, sQ1, sR1, hbCur_pos, ?_, hnb_eq,
                          rfl, hnb_le, hrem_ll_le, hsA2_len, hsB3_len, hsQ1_len, hsR1_len,
                          hsA2_val, hsB3_val, hmL3⟩
                        rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact hgcd_eq)
          · intro Jmax hJmax; c0_step
            by_cases hgt : na > nb
            · refine wp_jnz_true (bv64_ult_ofNat_true (by omega) (by omega) hgt) ?_; rw [wp_jump]
              apply hJmax
              exact ⟨by dsimp only [vals, Arg.val, maxn, na, nb]
                        rw [Nat.max_eq_left (Nat.le_of_lt hgt)], rfl⟩
            · refine wp_jnz_false (bv64_ult_ofNat_false (by omega) (by omega)
                (Nat.le_of_not_lt hgt)) ?_; rw [wp_jump]; apply hJmax
              exact ⟨by dsimp only [vals, Arg.val, maxn, na, nb]
                        rw [Nat.max_eq_right (Nat.le_of_not_lt hgt)], rfl⟩
    · intro J hJ; dsimp only; c0_step
      by_cases ha0 : aVal = 0
      · have hna0 : na = 0 := by dsimp [na]; rw [ha0, limbLenNat_zero]
        refine wp_jnz_true (by simp [na, hna0]) ?_; c0_step
        by_cases hb0 : bVal = 0
        · have hnb0 : nb = 0 := by dsimp [nb]; rw [hb0, limbLenNat_zero]
          refine wp_jnz_true (by simp [nb, hnb0]) ?_; rw [wp_ret]
          exact hpost 1#64 st scrLimbs objs m (preservesMeta_refl st) (Nat.le_refl _) hwf
            (by simp [ha0, hb0, natRep]) (fun o ho => ho) hm
        · have hnb_pos : 0 < nb := limbLenNat_pos_iff.mpr (Nat.pos_of_ne_zero hb0)
          refine wp_jnz_false (bv64_beq0_ofNat_false (by omega) hnb_pos) ?_; rw [wp_jump]
          exact hJ () m ⟨fun ⟨_, hb⟩ => hb0 hb, hm⟩
      · have hna_pos : 0 < na := limbLenNat_pos_iff.mpr (Nat.pos_of_ne_zero ha0)
        refine wp_jnz_false (bv64_beq0_ofNat_false (by omega) hna_pos) ?_; rw [wp_jump]
        exact hJ () m ⟨fun ⟨ha, _⟩ => ha0 ha, hm⟩


theorem jnz_true {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Bool} {t e : Expr Val Cont rs} (hc : c = true) (ht : wp Γ Q X t m) :
    wp Γ Q X (Expr.jnz (Arg.var c) t e) m := by
  rw [wp_jnz]; exact ⟨fun _ => ht, (by intro h; rw [hc] at h; cases h)⟩

theorem jnz_false {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Bool} {t e : Expr Val Cont rs} (hc : c = false) (he : wp Γ Q X e m) :
    wp Γ Q X (Expr.jnz (Arg.var c) t e) m := by
  rw [wp_jnz]; exact ⟨(by intro h; rw [hc] at h; cases h), fun _ => he⟩

theorem allFns_of_mem {P : Fn → Prop} : (fs : List Fn) → (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | f :: _, h => ⟨h f List.mem_cons_self, allFns_of_mem _ (fun g hg =>
    h g (List.mem_cons_of_mem _ hg))⟩


theorem info_lshr1_and1 {len : Nat} {negBit : BitVec 64}
    (hlen : len < 2 ^ 63) (hneg : negBit = 0#64 ∨ negBit = 1#64) :
    let info := (BitVec.ofNat 64 len <<< 1#64) ||| negBit
    info >>> 1 = BitVec.ofNat 64 len ∧ info &&& (1 : BitVec 64) = negBit := by
  intro info
  have h1 : (1#64 : BitVec 64).toNat = 1 := by decide
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro i
    simp only [info, BitVec.shiftLeft_eq', h1,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    by_cases hi64 : i < 64
    · have hb0 : negBit.getLsbD (1 + i) = false := by
        rcases hneg with rfl | rfl <;> simp
      have hsub : 1 + i - 1 = i := by omega
      simp only [hb0, Bool.or_false, hsub]
      by_cases hi1 : 1 + i < 64
      · simp [hi1, hi64]
      · have hge63 : 63 ≤ i := by omega
        have hbf : (BitVec.ofNat 64 len).getLsbD i = false := by
          rw [BitVec.getLsbD_ofNat]; simp only [hi64, decide_true, Bool.true_and]
          exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlen
            (Nat.pow_le_pow_right (by decide : 0 < 2) hge63))
        simp [hi1, hbf]
    · simp [hi64]
  · rw [show (1 : BitVec 64) = 1#64 from rfl]
    apply BitVec.eq_of_getLsbD_eq; intro i
    simp only [info, BitVec.shiftLeft_eq', h1, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    cases i with
    | zero => rcases hneg with rfl | rfl <;> simp
    | succ k => rcases hneg with rfl | rfl <;> simp

theorem bv64_mul8_add {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 60) :
    x + (8 : BitVec 64) * BitVec.ofNat 64 n = x + BitVec.ofNat 64 (8 * n) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h8 : (8 : Nat) % 2 ^ 64 = 8 := by decide
  change (BitVec.toNat 8 * (n % 2 ^ 64)) % 2 ^ 64 = (8 * n) % 2 ^ 64
  rw [show BitVec.toNat (8 : BitVec 64) = 8 by decide, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem int_add_same_sign {aVal bEff : Int} {negA negB : BitVec 64}
    (_ha : aVal ≠ 0) (_hb : bEff ≠ 0)
    (hsa : negA = if aVal < 0 then 1#64 else 0#64)
    (hsb : negB = if bEff < 0 then 1#64 else 0#64) (heq : negA = negB) :
    (aVal + bEff).natAbs = aVal.natAbs + bEff.natAbs ∧ aVal + bEff ≠ 0 ∧
      ((aVal + bEff) < 0 ↔ negA = 1#64) := by
  have hs_iff : aVal < 0 ↔ bEff < 0 := by
    by_cases ha0 : aVal < 0 <;> by_cases hb0 : bEff < 0 <;> simp only [ha0, hb0,
      ↓reduceIte] at hsa hsb
    · exact ⟨fun _ => hb0, fun _ => ha0⟩
    · rw [hsa, hsb] at heq; cases heq
    · rw [hsa, hsb] at heq; cases heq
    · exact ⟨fun h => absurd h ha0, fun h => absurd h hb0⟩
  by_cases ha0 : aVal < 0
  · have hb0 := hs_iff.mp ha0
    have hlt : aVal + bEff < 0 := by omega
    refine ⟨by omega, by omega, ?_⟩
    simp only [hsa, ha0, ↓reduceIte, hlt]
  · have hnb0 : ¬(bEff < 0) := fun h => ha0 (hs_iff.mpr h)
    have hnlt : ¬(aVal + bEff < 0) := by omega
    have hne01 : (0#64 : BitVec 64) ≠ 1#64 := by decide
    refine ⟨by omega, by omega, ?_⟩
    simp only [hsa, ha0, ↓reduceIte, hnlt]
    exact ⟨fun h => False.elim h, fun h => absurd h hne01⟩

theorem int_add_opp_sign_gt {aVal bEff : Int} {negA negB : BitVec 64}
    (_ha : aVal ≠ 0) (_hb : bEff ≠ 0)
    (hsa : negA = if aVal < 0 then 1#64 else 0#64)
    (hsb : negB = if bEff < 0 then 1#64 else 0#64) (hne : negA ≠ negB)
    (hgt : bEff.natAbs < aVal.natAbs) :
    (aVal + bEff).natAbs = aVal.natAbs - bEff.natAbs ∧ aVal + bEff ≠ 0 ∧
      ((aVal + bEff) < 0 ↔ negA = 1#64) := by
  have hs_opp : ¬(aVal < 0 ↔ bEff < 0) := by
    intro hiff
    by_cases ha0 : aVal < 0
    · have hb0 := hiff.mp ha0
      simp only [ha0, hb0, ↓reduceIte] at hsa hsb; exact hne (hsa.trans hsb.symm)
    · have hnb0 : ¬(bEff < 0) := fun h => ha0 (hiff.mpr h)
      simp only [ha0, hnb0, ↓reduceIte] at hsa hsb; exact hne (hsa.trans hsb.symm)
  by_cases ha0 : aVal < 0
  · have hnb0 : ¬(bEff < 0) := fun h => hs_opp ⟨fun _ => h, fun _ => ha0⟩
    have hlt : aVal + bEff < 0 := by omega
    refine ⟨by omega, by omega, ?_⟩
    simp only [hsa, ha0, ↓reduceIte, hlt]
  · have hb0 : bEff < 0 := by
      by_cases hb0' : bEff < 0
      · exact hb0'
      · exact False.elim (hs_opp ⟨fun h => absurd h ha0, fun h => absurd h hb0'⟩)
    have hnlt : ¬(aVal + bEff < 0) := by omega
    have hne01 : (0#64 : BitVec 64) ≠ 1#64 := by decide
    refine ⟨by omega, by omega, ?_⟩
    simp only [hsa, ha0, ↓reduceIte, hnlt]
    exact ⟨fun h => False.elim h, fun h => absurd h hne01⟩

@[expose] def cmpResult64Int (a b : Int) : BitVec 64 :=
  if a < b then BitVec.ofInt 64 (-1) else if a = b then 0#64 else 1#64

theorem cmpResult64Int_of_same_sign {a b : Int} {negA negB : BitVec 64}
    (hsa : negA = if a < 0 then 1#64 else 0#64)
    (hsb : negB = if b < 0 then 1#64 else 0#64) (heq : negA = negB) :
    (if negA ≠ 0#64 then -(cmpResult64 a.natAbs b.natAbs) else cmpResult64 a.natAbs b.natAbs) =
      cmpResult64Int a b := by
  by_cases ha0 : a < 0
  · have hb0 : b < 0 := by
      by_cases hb0' : b < 0
      · exact hb0'
      · simp only [ha0, hb0', ↓reduceIte] at hsa hsb
        rw [hsa, hsb] at heq; cases heq
    have hna : negA ≠ 0#64 := by simp only [hsa, ha0, ↓reduceIte]; decide
    simp only [hna, ne_eq, not_false_eq_true, ↓reduceIte, cmpResult64, cmpResult64Int]
    by_cases hab : a < b
    · have h1 : ¬(a.natAbs < b.natAbs) := by omega
      have h2 : b.natAbs < a.natAbs := by omega
      simp [hab, h1, h2]
    · by_cases heq_ab : a = b
      · subst heq_ab; simp
      · have hnat : a.natAbs < b.natAbs := by omega
        simp [hab, heq_ab, hnat]
  · have hnb0 : ¬(b < 0) := by
      intro hb0
      simp only [ha0, hb0, ↓reduceIte] at hsa hsb
      rw [hsa, hsb] at heq; cases heq
    have hna : negA = 0#64 := by simp only [hsa, ha0, ↓reduceIte]
    simp only [hna, ne_eq, not_true_eq_false, ↓reduceIte, cmpResult64, cmpResult64Int]
    by_cases hab : a < b
    · have hnat : a.natAbs < b.natAbs := by omega
      simp [hab, hnat]
    · by_cases heq_ab : a = b
      · subst heq_ab; simp
      · have h1 : ¬(a.natAbs < b.natAbs) := by omega
        have h2 : b.natAbs < a.natAbs := by omega
        simp [hab, heq_ab, h1, h2]

/-! ## Shared `Int` call helpers for Proof7/Proof8 -/

theorem int_bn_int_len_call_wp {Q : Post [i64]} {X : XPost}
    {rt scr a : BitVec 64} {st : RtC0State} {scrLimbs : List (BitVec 64)}
    {val : Int} {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hrep : intRep a val objs)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : wp rtR1Env Q X (k (BitVec.ofNat 64 (limbLenNat val.natAbs), ())) m) :
    wp rtR1Env Q X (.call (as := [i64]) (bs := [i64]) "bn_int_len" (Arg.var a, ()) k) m := by
  refine wp_call_ret1 (as := [i64]) (Arg.var a, ()) k (fun w m' =>
    w = BitVec.ofNat 64 (limbLenNat val.natAbs) ∧ m' = m) ?_ ?_
  · refine rtR1Env_bn_int_len ?_
    dsimp only [bnIntLenSpec, vals, Arg.val]
    exact ⟨val, objs, bigNumRtInv rt st scr scrLimbs ⋆ R, hrep,
      sep_cast_ac hm (by ac_rfl), rfl, rfl⟩
  · rintro w m' ⟨rfl, hm'⟩; subst m'; exact hk

theorem int_bn_require_scratch_call_wp {Q : Post [i64]} {X : XPost}
    {rt need scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hwf : BigNumRtWf rt st scr scrLimbs) (hneed : need.toNat ≤ scrLimbs.length)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : wp rtR1Env Q X (k (scr, ())) m) :
    wp rtR1Env Q X
      (.call (as := [i64, i64]) (bs := [i64]) "bn_require_scratch"
        (Arg.var rt, Arg.var need, ()) k) m := by
  refine wp_call_ret1 (as := [i64, i64]) (Arg.var rt, Arg.var need, ()) k
    (fun scrP m' => scrP = scr ∧ m' = m) ?_ ?_
  · refine rtR1Env_bn_require_scratch ?_
    dsimp only [bnRequireScratchSpec, vals, Arg.val]
    refine ⟨scr, BitVec.ofNat 64 scrLimbs.length,
      rtC0Inv rt st ⋆ array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R,
      hwf.2.2.1, ?_, ?_, rfl, rfl⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwf.2.2.2.2.1]; exact hneed
    · dsimp only [bigNumRtInv] at hm; exact sep_cast_ac hm (by ac_rfl)
  · rintro scrP m' ⟨hscrP, hm'⟩; subst scrP; subst m'; exact hk

theorem int_bn_load_int_call_wp {Q : Post [i64]} {X : XPost}
    {a dst : BitVec 64}
    {val : Int} {objs : List LcnfObj} {xs : List (BitVec 64)}
    (F : Mem 64 → Prop) {m : Mem 64}
    (hrep : intRep a val objs) (hlen : xs.length = limbLenNat val.natAbs)
    (hm : (lcnfHeap objs ⋆ array64 dst xs ⋆ F) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : ∀ xs' m', xs'.length = limbLenNat val.natAbs → limbsVal xs' = val.natAbs →
      (lcnfHeap objs ⋆ array64 dst xs' ⋆ F) m' →
      wp rtR1Env Q X
        (k (((BitVec.ofNat 64 (limbLenNat val.natAbs) <<< 1#64) |||
          (if val < 0 then 1#64 else 0#64)), ())) m') :
    wp rtR1Env Q X
      (.call (as := [i64, i64]) (bs := [i64]) "bn_load_int" (Arg.var a, Arg.var dst, ()) k) m := by
  refine wp_call_ret1 (as := [i64, i64]) (Arg.var a, Arg.var dst, ()) k (fun info m' =>
    ∃ xs',
      info = ((BitVec.ofNat 64 (limbLenNat val.natAbs) <<< 1#64) |||
        (if val < 0 then 1#64 else 0#64)) ∧
      xs'.length = limbLenNat val.natAbs ∧ limbsVal xs' = val.natAbs ∧
      (lcnfHeap objs ⋆ array64 dst xs' ⋆ F) m') ?_ ?_
  · refine rtR1Env_bn_load_int ?_
    dsimp only [bnLoadIntSpec, vals, Arg.val]
    refine ⟨val, objs, xs, F, hrep, by rw [hlen]; exact Nat.le_refl _, hm,
      fun xs' m' hlen' hval' _ hm' => ?_⟩
    have htake : List.take (limbLenNat val.natAbs) xs' = xs' :=
      List.take_of_length_le (by rw [hlen', hlen]; exact Nat.le_refl _)
    rw [htake] at hval'
    exact ⟨xs', rfl, by rw [hlen', hlen], hval', hm'⟩
  · rintro info m' ⟨xs', rfl, hlen', hval', hm'⟩
    exact hk xs' m' hlen' hval' hm'

theorem int_bn_int_from_limbs_call_wp {Q : Post [i64]} {X : XPost}
    {rt negW buf : BitVec 64} {n : Nat}
    {st : RtC0State} {xs : List (BitVec 64)} {objs : List LcnfObj}
    (F : Mem 64 → Prop) {m : Mem 64} {z : Int}
    (hn_lt : n < 2 ^ 60) (hn_le : n ≤ xs.length) (hn_max : n ≤ mpzMaxLimbs)
    (hb : st.Bounded48) (htrim : trimLenLoop xs n = n)
    (hval : (if n = 0 then (0 : Int)
      else if negW = 0#64 then (limbsVal (xs.take n) : Int)
      else -(limbsVal (xs.take n) : Int)) = z)
    (halloc : (z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * n))
    (hm : (rtC0Inv rt st ⋆ array64 buf xs ⋆ lcnfHeap objs ⋆ F) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : ∀ res st' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m' →
      wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X (.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_int_from_limbs"
      (Arg.var rt, Arg.var negW, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k) m := by
  refine wp_call_ret1 (as := [i64, i64, i64, i64])
    (Arg.var rt, Arg.var negW, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k (fun res m' =>
    ∃ st' objs',
      st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧ st'.Bounded48 ∧
      intRep res z objs' ∧ (∀ o ∈ objs, o ∈ objs') ∧
      (rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m') ?_ ?_
  · refine rtR1Env_bn_int_from_limbs ?_
    dsimp only [bnIntFromLimbsSpec, vals, Arg.val]
    have hnbv : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hval' : (if trimLenLoop xs (BitVec.ofNat 64 n).toNat = 0 then (0 : Int)
        else if negW = 0#64 then (limbsVal (xs.take (BitVec.ofNat 64 n).toNat) : Int)
        else -(limbsVal (xs.take (BitVec.ofNat 64 n).toNat) : Int)) = z := by
      rw [hnbv, htrim]; exact hval
    refine ⟨st, xs, objs, F, by rw [hnbv]; exact hn_le, by rw [hnbv]; exact hn_max, hb,
      fun hrz => by rw [hnbv, htrim]; exact halloc (by rwa [hval'] at hrz),
      hm, fun res st' objs' m' hpm hrem hb' hrep' hsm hbg hm' => ?_⟩
    rw [hval'] at hrep' hsm hbg
    have hpres : ∀ o ∈ objs, o ∈ objs' := by
      by_cases hsm_c : -(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62
      · rw [hsm hsm_c]; exact fun _ h => h
      · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
        exact fun _ h => List.mem_cons_of_mem _ h
    exact ⟨st', objs', hpm, hrem, hb', hrep', hpres, hm'⟩
  · rintro res m' ⟨st', objs', hpm, hrem, hb', hrep', hpres, hm'⟩
    exact hk res st' objs' m' hpm hrem hb' hrep' hpres hm'

theorem bn_max_jnz {na nb : Nat} (hna : na < 2 ^ 60) (hnb : nb < 2 ^ 60)
    (m : Mem 64) (J : Cont [i64])
    (hJ : ∀ xs m', xs = (BitVec.ofNat 64 (max na nb), ()) ∧ m' = m → J xs m') :
    ∀ {Q : Post [i64]} {X : XPost},
      wp rtR1Env Q X
        (Expr.let_
          ({ sig := [i64, i64], code := OpCode.ugt i64,
             args := (Arg.var (BitVec.ofNat 64 na), Arg.var (BitVec.ofNat 64 nb), ()) } :
            Op Val [Ty.bool])
          fun t => Expr.jnz (Arg.var t.1)
            (Expr.jump J (Arg.var (BitVec.ofNat 64 na), ()))
            (Expr.jump J (Arg.var (BitVec.ofNat 64 nb), ()))) m := by
  intro Q X; c0_let_simp
  by_cases hgt : nb < na
  · have hugt : BitVec.ofNat 64 nb < BitVec.ofNat 64 na := by
      change (BitVec.ofNat 64 nb).toNat < (BitVec.ofNat 64 na).toNat
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hgt
    refine jnz_true (by simpa [BitVec.ult] using hugt) ?_; rw [wp_jump]
    exact hJ (BitVec.ofNat 64 na, ()) m ⟨by rw [Nat.max_eq_left (by omega)], rfl⟩
  · have hnugt : ¬(BitVec.ofNat 64 nb < BitVec.ofNat 64 na) := by
      change ¬((BitVec.ofNat 64 nb).toNat < (BitVec.ofNat 64 na).toNat)
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hgt
    refine jnz_false (by simpa [BitVec.ult] using hnugt) ?_; rw [wp_jump]
    exact hJ (BitVec.ofNat 64 nb, ()) m ⟨by rw [Nat.max_eq_right (by omega)], rfl⟩

end LeanQbe.T.LeanLCNF
