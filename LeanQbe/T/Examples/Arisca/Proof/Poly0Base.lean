/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Src.Poly
public import LeanQbe.T.Examples.Arisca.Proof.Arena
public import LeanQbe.T.Examples.Arisca.Proof.Arith
public import LeanQbe.T.Examples.Arisca.Proof.Sem
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Monomial Primitives Core WPs (`Arisca.Proof.Poly0Base`)

`XPost`-polymorphic `Mem 64` WP specifications (`arMcmpSpec`..`arCompactSpec`) and WP proofs
for `5` functions in `LeanQbe.T.Examples.Arisca.Src.Poly`:
- `ar_mcmp`, `ar_mhas_from`, `ar_sigbit`, `ar_msig`, `ar_mvanish`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly

@[expose] public section

/-! ## 1. Pure Helpers & Specifications (`Poly0`: `7` fns) -/

/-- Sum of stored monomial slice word lengths `(pool[tm[i]] + 1)` for `i < n`. -/
def monoTotalWords (pool tm : List (BitVec 32)) (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i => acc + ((pool.getD (tm.getD i 0#32).toNat 0#32).toNat + 1)) 0

/-- WP specification for `ar_mcmp(a, b)` on two slices inside a shared `u32` array. -/
def arMcmpSpec : Spec [i64, i64] [i32] :=
  fun ⟨aPtr, bPtr, ⟨⟩⟩ m Q _ =>
    ∃ (base : BitVec 64) (xs : List (BitVec 32)) (offA offB : Nat) (R : Mem 64 → Prop),
      aPtr = base + BitVec.ofNat 64 (4 * offA) ∧
      bPtr = base + BitVec.ofNat 64 (4 * offB) ∧
      MonoSliceOk xs offA xs.length ∧
      MonoSliceOk xs offB xs.length ∧
      (xs.getD offA 0#32).toNat + 1 < 2 ^ 32 ∧
      (array (t := i32) base xs ⋆ R) m ∧
      (∀ ret : BitVec 32,
        (ret = 0#32 → symListAt xs offA = symListAt xs offB) →
        Q (ret, ⟨⟩) m)

/-- WP specification for `ar_mhas_from(m, lo, s)`. -/
def arMhasFromSpec : Spec [i64, i32, i32] [.bool] :=
  fun ⟨mPtr, lo, s, ⟨⟩⟩ m Q _ =>
    ∃ (base : BitVec 64) (xs : List (BitVec 32)) (off : Nat) (R : Mem 64 → Prop),
      mPtr = base + BitVec.ofNat 64 (4 * off) ∧
      MonoSliceOk xs off xs.length ∧
      (xs.getD off 0#32).toNat + 1 < 2 ^ 32 ∧
      1 ≤ lo.toNat ∧ lo.toNat ≤ (xs.getD off 0#32).toNat + 1 ∧
      (array (t := i32) base xs ⋆ R) m ∧
      (∀ ok : Bool,
        (ok = true → ∃ idx, lo.toNat ≤ idx ∧ idx ≤ (xs.getD off 0#32).toNat ∧
          xs.getD (off + idx) 0#32 = s) →
        (MonoSorted xs off → ok = false → ∀ idx, lo.toNat ≤ idx →
          idx ≤ (xs.getD off 0#32).toNat → xs.getD (off + idx) 0#32 ≠ s) →
        Q (ok, ⟨⟩) m)

/-- WP specification for `ar_sigbit(sym)` (total `u64` Bloom hash bit). -/
def arSigbitSpec : Spec [i32] [i64] :=
  fun ⟨sym, ⟨⟩⟩ m Q _ => ∀ ret : BitVec 64, ret = sigBit sym → Q (ret, ⟨⟩) m

/-- WP specification for `ar_msig(m)` (64-bit Bloom signature of monomial slice). -/
def arMsigSpec : Spec [i64] [i64] :=
  fun ⟨mPtr, ⟨⟩⟩ m Q _ =>
    ∃ (base : BitVec 64) (xs : List (BitVec 32)) (off : Nat) (R : Mem 64 → Prop),
      mPtr = base + BitVec.ofNat 64 (4 * off) ∧
      MonoSliceOk xs off xs.length ∧
      (xs.getD off 0#32).toNat + 1 < 2 ^ 32 ∧
      (array (t := i32) base xs ⋆ R) m ∧
      (∀ sig : BitVec 64,
        (∀ x ∈ symListAt xs off, (sig &&& sigBit (BitVec.ofNat 32 x)) ≠ 0#64) →
        Q (sig, ⟨⟩) m)

/-- WP specification for `ar_mvanish(cx, m)` checking HA vanishing pairs. -/
def arMvanishSpec : Spec [i64, i64] [.bool] :=
  fun ⟨cx, mPtr, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (partnerArr : List (BitVec 32))
      (mBase : BitVec 64) (mArr : List (BitVec 32)) (mOff : Nat)
      (σ : Nat → Bool) (R : Mem 64 → Prop),
      mPtr = mBase + BitVec.ofNat 64 (4 * mOff) ∧
      MonoSliceOk mArr mOff mArr.length ∧
      (mArr.getD mOff 0#32).toNat + 1 < 2 ^ 32 ∧
      2 * s.n_nets.toNat ≤ 2 ^ 32 ∧
      PartnerRep σ s.n_nets.toNat partnerArr ∧
      (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) mBase mArr ⋆ R) m ∧
      (∀ ok : Bool,
        (ok = true → monoValL σ (symListAt mArr mOff) = false) →
        Q (ok, ⟨⟩) m)

/-- WP specification for `ar_munion(out, a, s, b)`. -/
def arMunionSpec : Spec [i64, i64, i32, i64] [i64] :=
  fun ⟨outPtr, aPtr, sym, bPtr, ⟨⟩⟩ m Q _ =>
    ∃ (out0 : List (BitVec 32)) (aBase : BitVec 64) (aArr : List (BitVec 32)) (aOff : Nat)
      (bBase : BitVec 64) (bArr : List (BitVec 32)) (bOff : Nat) (R : Mem 64 → Prop),
      let la := (aArr.getD aOff 0#32).toNat
      let lb := (bArr.getD bOff 0#32).toNat
      aPtr = aBase + BitVec.ofNat 64 (4 * aOff) ∧
      bPtr = bBase + BitVec.ofNat 64 (4 * bOff) ∧
      MonoSliceOk aArr aOff aArr.length ∧
      MonoSliceOk bArr bOff bArr.length ∧
      la + 1 < 2 ^ 32 ∧ lb + 1 < 2 ^ 32 ∧
      (∃ idx, 1 ≤ idx ∧ idx ≤ la ∧ aArr.getD (aOff + idx) 0#32 = sym) ∧
      la + lb ≤ out0.length ∧ la + lb < 2 ^ 32 ∧
      (array (t := i32) outPtr out0 ⋆ array (t := i32) aBase aArr ⋆
        array (t := i32) bBase bArr ⋆ R) m ∧
      (∀ (sig : BitVec 64) (out' : List (BitVec 32)) (m' : Mem 64),
        out'.length = out0.length →
        (out'.getD 0 0#32).toNat + 1 ≤ la + lb →
        (∀ z, z ∈ symListAt out' 0 ↔
          (z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff) →
        (MonoSorted aArr aOff → MonoSorted bArr bOff → MonoSorted out' 0) →
        (∀ x ∈ symListAt out' 0, (sig &&& sigBit (BitVec.ofNat 32 x)) ≠ 0#64) →
        (∀ idx, la + lb ≤ idx → out'.getD idx 0#32 = out0.getD idx 0#32) →
        (array (t := i32) outPtr out' ⋆ array (t := i32) aBase aArr ⋆
          array (t := i32) bBase bArr ⋆ R) m' →
        Q (sig, ⟨⟩) m')

/-- WP specification for `ar_compact(cx)` ping-ponging live `T` monomials. -/
def arCompactSpec : Spec [i64] [] :=
  fun ⟨cx, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (tm0 tm1 : List (BitVec 32))
      (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pool0 pool1 : List (BitVec 32))
      (σ : Nat → Bool) (R : Mem 64 → Prop),
      let srcPool := if s.pc.toNat = 0 then pool0 else pool1
      let srcTm := if s.tc.toNat = 0 then tm0 else tm1
      s.pc.toNat < 2 ∧ s.tc.toNat < 2 ∧
      s.tn.toNat ≤ s.tcap.toNat ∧
      s.tcap.toNat ≤ tm0.length ∧ s.tcap.toNat ≤ tm1.length ∧
      s.ptop.toNat ≤ s.pcap.toNat ∧
      s.pcap.toNat < 2 ^ 32 ∧
      s.pcap.toNat ≤ pool0.length ∧ s.pcap.toNat ≤ pool1.length ∧
      (∀ i < s.tn.toNat, MonoSliceOk srcPool (srcTm.getD i 0#32).toNat srcPool.length) ∧
      monoTotalWords srcPool srcTm s.tn.toNat ≤ s.pcap.toNat ∧
      (arCtxMem cx s ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ R) m ∧
      (∀ (s' : ArCtxState) (tm0' tm1' pool0' pool1' : List (BitVec 32)) (m' : Mem 64),
        let dstPool := if s.pc.toNat = 0 then pool1' else pool0'
        let dstTm := if s.tc.toNat = 0 then tm0' else tm1'
        let dstTl := if s.tc.toNat = 0 then tl0 else tl1
        let dstTh := if s.tc.toNat = 0 then th0 else th1
        s'.pc.toNat = 1 - s.pc.toNat →
        s' = { s with pc := s'.pc, ptop := s'.ptop } →
        s'.ptop.toNat = monoTotalWords srcPool srcTm s.tn.toNat →
        s'.ptop.toNat ≤ s.pcap.toNat →
        tm0'.length = tm0.length → tm1'.length = tm1.length →
        pool0'.length = pool0.length → pool1'.length = pool1.length →
        (if s.pc.toNat = 0 then pool0' = pool0 else pool1' = pool1) →
        (if s.tc.toNat = 0 then tm1' = tm1 else tm0' = tm0) →
        (∀ i < s.tn.toNat,
          symListAt dstPool (dstTm.getD i 0#32).toNat =
            symListAt srcPool (srcTm.getD i 0#32).toNat ∧
          MonoSliceOk dstPool (dstTm.getD i 0#32).toNat s'.ptop.toNat) →
        monoTotalWords dstPool dstTm s.tn.toNat = s'.ptop.toNat →
        polyEval s.modW σ dstPool dstTm dstTl dstTh s.tn.toNat =
          polyEval s.modW σ srcPool srcTm dstTl dstTh s.tn.toNat →
        (arCtxMem cx s' ⋆ tMem s' tm0' tm1' ts0 tl0 th0 ts1 tl1 th1 pool0' pool1' ⋆ R) m' →
        Q () m')

end

/-! ## 2. Basic Lemmas, Bloom Bits & Array Address Arithmetic -/

public section

theorem bv32_eq_of_ult_false {a b : BitVec 32} (h1 : ¬ a.toNat < b.toNat)
    (h2 : ¬ b.toNat < a.toNat) : a = b :=
  BitVec.eq_of_toNat_eq (by omega)

theorem arr32_elem_addr (base : BitVec 64) (off i : Nat) :
    base + BitVec.ofNat 64 (4 * off) + BitVec.ofNat 64 (4 * i) =
      base + BitVec.ofNat 64 (4 * (off + i)) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mul_add]

theorem arr32_idx_addr (base : BitVec 64) (off : Nat) (i : BitVec 32) :
    base + BitVec.ofNat 64 (4 * off) + BitVec.setWidth 64 i * 4 =
      base + BitVec.ofNat 64 (4 * (off + i.toNat)) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mul_add, Nat.mul_comm i.toNat 4]

theorem loadVal_arr32_at {base : BitVec 64} {xs : List (BitVec 32)} {off i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : off + i < xs.length)
    (h : (array (t := i32) base xs ⋆ R) m) :
    loadVal m i32 (base + BitVec.ofNat 64 (4 * off) + BitVec.ofNat 64 (4 * i)) =
      some (xs[off + i]) := by
  rw [arr32_elem_addr]
  exact loadVal_array (t := i32) (by decide) hi h

theorem wp_load_arr32 {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 32)} {off i : Nat} {R : Mem 64 → Prop}
    (ha : a.val = base + BitVec.ofNat 64 (4 * off) + BitVec.ofNat 64 (4 * i))
    (hi : off + i < xs.length) (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : wp Γ Q X (k (xs[off + i])) m) : wp Γ Q X (.load i32 a k) m :=
  head_wp_load ha (loadVal_arr32_at hi hm) hk

theorem wp_load_arr32_idx {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 32)} {off : Nat} {i : BitVec 32} {R : Mem 64 → Prop}
    (ha : a.val = base + BitVec.ofNat 64 (4 * off) + BitVec.setWidth 64 i * 4)
    (hi : off + i.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : wp Γ Q X (k (xs[off + i.toNat])) m) : wp Γ Q X (.load i32 a k) m := by
  rw [arr32_idx_addr] at ha
  exact head_wp_load ha (loadVal_array (t := i32) (by decide) hi hm) hk

theorem wp_load_arr32_abs {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 32)} {i : BitVec 64} {R : Mem 64 → Prop}
    (ha : a.val = base + i * 4) (hi : i.toNat < xs.length)
    (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : wp Γ Q X (k (xs[i.toNat])) m) : wp Γ Q X (.load i32 a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 (4 * i.toNat) := by
    rw [ha]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm i.toNat 4]
  exact head_wp_load ha' (loadVal_array (t := i32) (by decide) hi hm) hk

theorem wp_store_arr32_idx {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {v : Arg Val i32} {a : Arg Val i64} {val : BitVec 32} {k : Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 32)} {idx : BitVec 32} {R : Mem 64 → Prop}
    (hv : v.val = val) (ha : a.val = base + BitVec.setWidth 64 idx * 4)
    (hi : idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : ∀ m', (array (t := i32) base (xs.set idx.toNat val) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 (4 * idx.toNat) := by
    rw [ha]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_comm idx.toNat 4]
  exact head_wp_store hv ha' (store_array (t := i32) val (by decide) hi hm) hk

theorem wp_store_arr32_abs {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {v : Arg Val i32} {a : Arg Val i64} {val : BitVec 32} {k : Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 32)} {idx : BitVec 64} {R : Mem 64 → Prop}
    (hv : v.val = val) (ha : a.val = base + idx * 4)
    (hi : idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : ∀ m', (array (t := i32) base (xs.set idx.toNat val) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 (4 * idx.toNat) := by
    rw [ha]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm idx.toNat 4]
  exact head_wp_store hv ha' (store_array (t := i32) val (by decide) hi hm) hk

theorem wp_load_arr32_0 {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 32)} {off : Nat} {R : Mem 64 → Prop}
    (ha : a.val = base + BitVec.ofNat 64 (4 * off) + 0#64 * 4)
    (hi : off < xs.length) (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : wp Γ Q X (k (xs[off])) m) : wp Γ Q X (.load i32 a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 (4 * off) := by
    rw [ha]; simp [BitVec.add_zero]
  exact head_wp_load ha' (loadVal_array (t := i32) (by decide) hi hm) hk

theorem getD_eq_getElem {α : Type} (xs : List α) (d : α) {i : Nat} (hi : i < xs.length) :
    xs.getD i d = xs[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem getD_set_eq {α : Type} (xs : List α) (d v : α) {i j : Nat} (hi : i < xs.length) :
    (xs.set i v).getD j d = if j = i then v else xs.getD j d := by
  by_cases hji : j = i
  · subst hji; rw [getD_eq_getElem _ _ (by simp [hi])]; simp
  · have hij : i ≠ j := Ne.symm hji
    simp [List.getD_eq_getElem?_getD, hji, hij]

theorem monoTotalWords_zero (pool tm : List (BitVec 32)) :
    monoTotalWords pool tm 0 = 0 := rfl

theorem monoTotalWords_succ (pool tm : List (BitVec 32)) (n : Nat) :
    monoTotalWords pool tm (n + 1) =
      monoTotalWords pool tm n + ((pool.getD (tm.getD n 0#32).toNat 0#32).toNat + 1) := by
  simp only [monoTotalWords, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem symListAt_set_zero (xs : List (BitVec 32)) (k : BitVec 32) (hk : 0 < xs.length) :
    symListAt (xs.set 0 k) 0 =
      (List.range k.toNat).map (fun i => (xs.getD (1 + i) 0#32).toNat) := by
  simp only [symListAt, Nat.zero_add, getD_set_eq xs 0#32 k hk, ↓reduceIte]
  apply List.map_congr_left
  intro i _
  simp only [show 1 + i ≠ 0 by omega, ↓reduceIte]

theorem polyEval_congr_symListAt (n_out : Nat) (σ : Nat → Bool)
    (pool1 tm1 pool2 tm2 : List (BitVec 32)) (tl th : List (BitVec 64)) (n : Nat)
    (h : ∀ i < n, symListAt pool1 (tm1.getD i 0#32).toNat =
      symListAt pool2 (tm2.getD i 0#32).toNat) :
    polyEval n_out σ pool1 tm1 tl th n = polyEval n_out σ pool2 tm2 tl th n := by
  induction n with
  | zero => simp [polyEval_zero]
  | succ n ih =>
    rw [polyEval_succ, polyEval_succ, ih (fun i hi => h i (by omega))]
    congr 1
    simp only [termEval, h n (Nat.lt_succ_self n)]

private theorem sigBit_testBit (s : BitVec 32) :
    (sigBit s).toNat.testBit (((s * 0x9E3779B1#32) >>> 26).toNat) = true := by
  let k := ((s * 0x9E3779B1#32) >>> 26).toNat
  have hk : k < 64 := by
    dsimp only [k]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (s * 0x9E3779B1#32).isLt
    omega
  have hlt : 1 <<< k < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by decide) hk
  change (1#64 <<< k).toNat.testBit k = true
  rw [BitVec.toNat_shiftLeft, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt,
    Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  simp

theorem or_and_sigBit_ne_zero (g : BitVec 64) (s : BitVec 32) :
    ((g ||| sigBit s) &&& sigBit s) ≠ 0#64 := by
  intro h
  have hb := congrArg
    (fun x : BitVec 64 => x.toNat.testBit (((s * 0x9E3779B1#32) >>> 26).toNat)) h
  rw [BitVec.toNat_and, BitVec.toNat_or, Nat.testBit_and, Nat.testBit_or,
    sigBit_testBit, Bool.or_true, Bool.and_true, BitVec.toNat_zero, Nat.zero_testBit] at hb
  cases hb

theorem and_sigBit_or_left {g r t : BitVec 64} (h : (g &&& t) ≠ 0#64) :
    ((g ||| r) &&& t) ≠ 0#64 := by
  intro hz
  apply h
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro k
  have hzk := congrArg (fun x : BitVec 64 => x.toNat.testBit k) hz
  simp only [BitVec.toNat_and, BitVec.toNat_or, Nat.testBit_and, Nat.testBit_or,
    BitVec.toNat_zero, Nat.zero_testBit] at hzk ⊢
  cases hg : g.toNat.testBit k <;> cases ht : t.toNat.testBit k <;> simp_all

theorem mhas_not_found_of_lo1 {xs : List (BitVec 32)} {off : Nat} {s : BitVec 32}
    (h : ∀ idx, 1 ≤ idx → idx ≤ (xs.getD off 0#32).toNat → xs.getD (off + idx) 0#32 ≠ s) :
    s.toNat ∉ symListAt xs off := by
  intro hmem
  rw [mem_symListAt_iff] at hmem
  obtain ⟨idx, h1, hle, hval⟩ := hmem
  exact h idx h1 hle (BitVec.eq_of_toNat_eq hval)

/-! ## 3. `ar_mcmp_wp`, `ar_mhas_from_wp`, `ar_sigbit_wp`, `ar_msig_wp`, `ar_mvanish_wp` -/

theorem ar_mcmp_wp (Γ : T.Env) :
    ∀ xs m Q X, arMcmpSpec xs m Q X → Func.wp Γ ar_mcmp_body xs m Q X := by
  rintro ⟨aPtr, bPtr, ⟨⟩⟩ m Q X ⟨base, xs, offA, offB, R, haPtr, hbPtr, hA, hB, hlt32, hm, hQ⟩
  subst haPtr; subst hbPtr
  try c0_hsteps
  · exact wp_load_arr32 (base := base) (off := offA) (i := 0) (by simp) hA.1 hm (by
      try c0_hsteps
      · exact wp_load_arr32 (base := base) (off := offB) (i := 0) (by simp) hB.1 hm (by
          c0_hsteps
          · exact hQ (-1#32) (fun heq => absurd heq (by decide))
          · exact hQ 1#32 (fun heq => absurd heq (by decide))
          · have hlen_eq : xs.getD offA 0#32 = xs.getD offB 0#32 := by
              rw [getD_eq_getElem xs 0#32 hA.1, getD_eq_getElem xs 0#32 hB.1]
              exact ‹xs[offA]'hA.1 = xs[offB]'hB.1›
            have hlenNat : (xs.getD offA 0#32).toNat = (xs.getD offB 0#32).toNat :=
              congrArg BitVec.toNat hlen_eq
            refine wp_loop_group (fun rem ⟨i, ⟨⟩⟩ m' =>
                m' = m ∧ 1 ≤ i.toNat ∧ i.toNat ≤ (xs.getD offA 0#32).toNat + 1 ∧
                rem = (xs.getD offA 0#32).toNat + 1 - i.toNat ∧
                (∀ k, 1 ≤ k → k < i.toNat →
                  xs.getD (offA + k) 0#32 = xs.getD (offB + k) 0#32))
              ?_ ?_
            · intro J rem ⟨i, ⟨⟩⟩ m' hrec ⟨hm', hi1, hile, hrem, hpref⟩
              subst hm'
              c0_hsteps
              · have hilt : i.toNat ≤ (xs.getD offA 0#32).toNat := by
                  rw [getD_eq_getElem xs 0#32 hA.1]; exact hc
                have hlt_a : offA + i.toNat < xs.length := by
                  have := hA.2; omega
                have hlt_b : offB + i.toNat < xs.length := by
                  have := hB.2; omega
                try c0_hsteps
                · exact wp_load_arr32_idx (base := base) (off := offA) (i := i) rfl hlt_a hm (by
                    try c0_hsteps
                    · exact wp_load_arr32_idx (base := base) (off := offB) (i := i) rfl hlt_b hm (by
                        c0_hsteps
                        · try c0_hsteps
                          · exact wp_load_arr32_idx (base := base) (off := offA) (i := i) rfl hlt_a
                              hm (by
                              try c0_hsteps
                              · exact wp_load_arr32_idx (base := base) (off := offB) (i := i) rfl
                                  hlt_b hm (by
                                  c0_hsteps
                                  · exact hQ (-1#32) (fun heq => absurd heq (by decide))
                                  · exact hQ 1#32 (fun heq => absurd heq (by decide))))
                        · have hi_eq :
                              xs.getD (offA + i.toNat) 0#32 = xs.getD (offB + i.toNat) 0#32 := by
                            rw [getD_eq_getElem xs 0#32 hlt_a, getD_eq_getElem xs 0#32 hlt_b]
                            exact ‹xs[offA + i.toNat]'hlt_a = xs[offB + i.toNat]'hlt_b›
                          have hip1 : (i + 1).toNat = i.toNat + 1 := by
                            rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
                              Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
                          exact hrec ((xs.getD offA 0#32).toNat + 1 - (i + 1).toNat)
                            (i + 1, ⟨⟩) m' (by omega)
                            ⟨rfl, by omega, by omega, rfl, fun k hk1 hklt => by
                              by_cases hki : k = i.toNat
                              · subst hki; exact hi_eq
                              · exact hpref k hk1 (by omega)⟩))
              · refine hQ 0#32 (fun _ => ?_)
                have hi_eq : i.toNat = (xs.getD offA 0#32).toNat + 1 := by
                  have hlt' := BitVec.not_le.mp hc
                  have h0 : (xs[offA + 0]'(by have := hA.1; omega)).toNat =
                      (xs.getD offA 0#32).toNat := by
                    symm; exact congrArg BitVec.toNat (getD_eq_getElem xs 0#32 hA.1)
                  have hlt_nat : (xs[offA + 0]'(by have := hA.1; omega)).toNat < i.toNat := hlt'
                  omega
                simp only [symListAt, hlenNat]
                apply List.map_congr_left
                intro k hk
                rw [List.mem_range] at hk
                have heq := hpref (k + 1) (by omega) (by omega)
                rw [show offA + 1 + k = offA + (k + 1) by omega,
                  show offB + 1 + k = offB + (k + 1) by omega, heq]
            · intro J hJ
              c0_hsteps
              have h1_nat : (1#32 : BitVec 32).toNat = 1 := rfl
              exact hJ ((xs.getD offA 0#32).toNat + 1 - 1) (1#32, ⟨⟩) m
                ⟨rfl, by decide, by rw [h1_nat]; omega, rfl, fun k hk1 hklt => by omega⟩))

theorem ar_mhas_from_wp (Γ : T.Env) :
    ∀ xs m Q X, arMhasFromSpec xs m Q X → Func.wp Γ ar_mhas_from_body xs m Q X := by
  rintro ⟨mPtr, lo, s, ⟨⟩⟩ m Q X ⟨base, xs, off, R, hmPtr, hM, hlt32, hlo1, hlo_le, hm, hQ⟩
  subst hmPtr
  try c0_hsteps
  · exact wp_load_arr32 (base := base) (off := off) (i := 0) (by simp) hM.1 hm (by
      c0_hsteps
      refine wp_loop_group (fun rem ⟨lo', hi', ⟨⟩⟩ m' =>
          m' = m ∧ lo.toNat ≤ lo'.toNat ∧ lo'.toNat ≤ hi'.toNat ∧
          hi'.toNat ≤ (xs.getD off 0#32).toNat + 1 ∧
          rem = hi'.toNat - lo'.toNat ∧
          (MonoSorted xs off →
            (∀ k, lo.toNat ≤ k → k < lo'.toNat → (xs.getD (off + k) 0#32).toNat < s.toNat) ∧
            (∀ k, hi'.toNat ≤ k → k ≤ (xs.getD off 0#32).toNat →
              s.toNat ≤ (xs.getD (off + k) 0#32).toNat))) ?_ ?_
      · intro J rem ⟨lo', hi', ⟨⟩⟩ m' hrec ⟨hm', hlo_lo', hle, hhi_le, hrem, hsort⟩
        subst hm'
        c0_hsteps
        · have hlt : lo'.toNat < hi'.toNat := hc
          let mid := lo' + ((hi' - lo') >>> (1 : Nat))
          have hmid_bounds : lo'.toNat ≤ mid.toNat ∧ mid.toNat < hi'.toNat := by
            have hsub : (hi' - lo').toNat = hi'.toNat - lo'.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)
            have hsh : ((hi' - lo') >>> (1 : Nat)).toNat = (hi'.toNat - lo'.toNat) / 2 := by
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, hsub]
            have hsum : lo'.toNat + (hi'.toNat - lo'.toNat) / 2 < 2 ^ 32 := by omega
            have hm_eq : mid.toNat = lo'.toNat + (hi'.toNat - lo'.toNat) / 2 := by
              dsimp only [mid]; rw [BitVec.toNat_add, hsh, Nat.mod_eq_of_lt hsum]
            omega
          have hlt_mid : off + mid.toNat < xs.length := by
            have := hM.2; omega
          try c0_hsteps
          · exact wp_load_arr32_idx (base := base) (off := off) (i := mid) rfl hlt_mid hm (by
              c0_hsteps
              · have hmid1 : (mid + 1).toNat = mid.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega : mid.toNat + 1 < 2 ^ 32)]
                have hmid_val : (xs.getD (off + mid.toNat) 0#32).toNat < s.toNat := by
                  rw [getD_eq_getElem xs 0#32 hlt_mid]; exact hc
                refine hrec (hi'.toNat - (mid + 1).toNat) (mid + 1, hi', ⟨⟩) m' (by omega)
                  ⟨rfl, by omega, by omega, hhi_le, rfl, fun hms => ?_⟩
                refine ⟨fun k hk_lo hk_lt => ?_, (hsort hms).2⟩
                rw [hmid1] at hk_lt
                by_cases hkm : k = mid.toNat
                · subst hkm; exact hmid_val
                · have hms' := (monoSorted_iff xs off).mp hms
                  have hlt_k : (xs.getD (off + 1 + (k - 1)) 0#32).toNat <
                      (xs.getD (off + 1 + (mid.toNat - 1)) 0#32).toNat :=
                    hms' (k - 1) (mid.toNat - 1) (by omega) (by omega)
                  rw [show off + 1 + (k - 1) = off + k by omega,
                    show off + 1 + (mid.toNat - 1) = off + mid.toNat by omega] at hlt_k
                  omega
              · have hmid_val : s.toNat ≤ (xs.getD (off + mid.toNat) 0#32).toNat := by
                  rw [getD_eq_getElem xs 0#32 hlt_mid]; exact Nat.le_of_not_lt hc
                refine hrec (mid.toNat - lo'.toNat) (lo', mid, ⟨⟩) m' (by omega)
                  ⟨rfl, hlo_lo', hmid_bounds.1, by omega, rfl, fun hms => ?_⟩
                refine ⟨(hsort hms).1, fun k hk_lo hk_le => ?_⟩
                by_cases hkm : k = mid.toNat
                · subst hkm; exact hmid_val
                · have hms' := (monoSorted_iff xs off).mp hms
                  have hlt_k : (xs.getD (off + 1 + (mid.toNat - 1)) 0#32).toNat <
                      (xs.getD (off + 1 + (k - 1)) 0#32).toNat :=
                    hms' (mid.toNat - 1) (k - 1) (by omega) (by omega)
                  rw [show off + 1 + (k - 1) = off + k by omega,
                    show off + 1 + (mid.toNat - 1) = off + mid.toNat by omega] at hlt_k
                  omega)
        · have hnot : ¬ lo'.toNat < hi'.toNat := hc
          have hlo_hi : lo'.toNat = hi'.toNat := by omega
          try c0_hsteps
          · exact wp_load_arr32_0 (base := base) (off := off) rfl hM.1 hm (by
              c0_hsteps
              · have hilt : lo'.toNat ≤ (xs.getD off 0#32).toNat := by
                  rw [getD_eq_getElem xs 0#32 hM.1]; exact hc
                have hlt_m : off + lo'.toNat < xs.length := by
                  have := hM.2; omega
                try c0_hsteps
                · exact wp_load_arr32_idx (base := base) (off := off) (i := lo') rfl hlt_m hm (by
                    c0_hsteps
                    · refine hQ true (fun _ => ?_) (fun _ h => by cases h)
                      have heqs : xs[off + lo'.toNat]'hlt_m = s := by simpa using ‹_›
                      exact ⟨lo'.toNat, hlo_lo', hilt, by
                        rw [getD_eq_getElem xs 0#32 hlt_m]; exact heqs⟩
                    · refine hQ false (fun h => by cases h) (fun hms _ idx h1 h2 heq => ?_)
                      have hs_ne : xs.getD (off + lo'.toNat) 0#32 ≠ s := by
                        rw [getD_eq_getElem xs 0#32 hlt_m]; exact ‹xs[off + lo'.toNat]'hlt_m ≠ s›
                      rcases Nat.lt_trichotomy idx lo'.toNat with hlt | rfl | hgt
                      · have := (hsort hms).1 idx h1 hlt
                        rw [heq] at this; omega
                      · exact hs_ne heq
                      · have hlo_le_val := (hsort hms).2 lo'.toNat (by omega) hilt
                        have hms' := (monoSorted_iff xs off).mp hms
                        have hlt_k := hms' (lo'.toNat - 1) (idx - 1) (by omega) (by omega)
                        rw [show off + 1 + (lo'.toNat - 1) = off + lo'.toNat by omega,
                          show off + 1 + (idx - 1) = off + idx by omega, heq] at hlt_k
                        omega)
              · refine hQ false (fun h => by cases h) (fun hms _ idx h1 h2 heq => ?_)
                have hgt : (xs.getD off 0#32).toNat < lo'.toNat := by
                  have h0 := getD_eq_getElem xs 0#32 hM.1
                  rw [h0]; exact BitVec.not_le.mp hc
                have := (hsort hms).1 idx h1 (by omega)
                rw [heq] at this; omega)
      · intro J hJ
        c0_hsteps
        have h0 := getD_eq_getElem xs 0#32 hM.1
        have hhiNat : (xs[off]'hM.1 + 1).toNat = (xs.getD off 0#32).toNat + 1 := by
          rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl, ← h0,
            Nat.mod_eq_of_lt hlt32]
        exact hJ ((xs[off]'hM.1 + 1).toNat - lo.toNat) (lo, xs[off]'hM.1 + 1, ⟨⟩) m
          ⟨rfl, Nat.le_refl _, by omega, by omega, rfl, fun _ =>
            ⟨fun _ _ _ => by omega, fun k hk1 hk2 => by omega⟩⟩)

theorem ar_sigbit_wp (Γ : T.Env) :
    ∀ xs m Q X, arSigbitSpec xs m Q X → Func.wp Γ ar_sigbit_body xs m Q X := by
  rintro ⟨sym, ⟨⟩⟩ m Q X hQ
  c0_hsteps
  refine hQ _ ?_
  apply BitVec.eq_of_toNat_eq
  unfold sigBit
  have hlt : BitVec.toNat (sym * 0x9E3779B1#32) / 2 ^ 26 < 64 := by
    have := (sym * 0x9E3779B1#32).isLt; omega
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    show (1#64 : BitVec 64).toNat = 1 from rfl, show (1 : BitVec 64).toNat = 1 from rfl]
  congr 2
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (lt_trans (BitVec.isLt _) (by decide : 2 ^ 32 < 2 ^ 64)),
    BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  change (BitVec.toNat (sym * 0x9E3779B1#32) / 2 ^ 26) % 64 =
    BitVec.toNat (sym * 0x9E3779B1#32) / 2 ^ 26
  exact Nat.mod_eq_of_lt hlt

theorem ar_msig_wp (Γ : T.Env)
    (hSig : ∀ xs m Q X, arSigbitSpec xs m Q X → Γ "ar_sigbit" [i32] [i64] xs m Q X) :
    ∀ xs m Q X, arMsigSpec xs m Q X → Func.wp Γ ar_msig_body xs m Q X := by
  rintro ⟨mPtr, ⟨⟩⟩ m Q X ⟨base, xs, off, R, hmPtr, hM, hlt32, hm, hQ⟩
  subst hmPtr
  try c0_hsteps
  · exact wp_load_arr32 (base := base) (off := off) (i := 0) (by simp) hM.1 hm (by
      c0_hsteps
      refine wp_loop_group (fun rem ⟨g, i, ⟨⟩⟩ m' =>
          m' = m ∧ 1 ≤ i.toNat ∧ i.toNat ≤ (xs.getD off 0#32).toNat + 1 ∧
          rem = (xs.getD off 0#32).toNat + 1 - i.toNat ∧
          ∀ t, 1 ≤ t → t < i.toNat → (g &&& sigBit (xs.getD (off + t) 0#32)) ≠ 0#64) ?_ ?_
      · intro J rem ⟨g, i, ⟨⟩⟩ m' hrec ⟨hm', hi1, hile, hrem, hsig⟩
        subst hm'
        c0_hsteps
        · have hilt : i.toNat ≤ (xs.getD off 0#32).toNat := by
            rw [getD_eq_getElem xs 0#32 hM.1]; exact hc
          have hlt_m : off + i.toNat < xs.length := by
            have := hM.2; omega
          try c0_hsteps
          · exact wp_load_arr32_idx (base := base) (off := off) (i := i) rfl hlt_m hm (by
              c0_hsteps
              refine wp_call_of_spec _ _ (hSig _ _ _ _ (fun ret hret => ?_))
              c0_hsteps
              have hip1 : (i + 1).toNat = i.toNat + 1 := by
                rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
              refine hrec ((xs.getD off 0#32).toNat + 1 - (i + 1).toNat)
                (g ||| ret, i + 1, ⟨⟩) m' (by omega) ⟨rfl, by omega, by omega, rfl, ?_⟩
              intro t ht1 htlt
              rw [hip1] at htlt
              dsimp only [Arg.val] at hret
              rw [hret]
              by_cases hti : t = i.toNat
              · rw [hti, getD_eq_getElem xs 0#32 hlt_m]
                exact or_and_sigBit_ne_zero g (xs[off + i.toNat]'hlt_m)
              · exact and_sigBit_or_left (hsig t ht1 (by omega)))
        · refine hQ g (fun x hx => ?_)
          have hi_eq : i.toNat = (xs.getD off 0#32).toNat + 1 := by
            have hlt' := BitVec.not_le.mp hc
            have h0 : (xs[off + 0]'(by have := hM.1; omega)).toNat =
                (xs.getD off 0#32).toNat := by
              symm; exact congrArg BitVec.toNat (getD_eq_getElem xs 0#32 hM.1)
            omega
          rw [mem_symListAt_iff] at hx
          obtain ⟨t, ht1, htle, rfl⟩ := hx
          have hne := hsig t ht1 (by omega)
          rwa [BitVec.ofNat_toNat]
      · intro J hJ
        c0_hsteps
        have h1_nat : (1#32 : BitVec 32).toNat = 1 := rfl
        exact hJ ((xs.getD off 0#32).toNat + 1 - 1) (0#64, 1#32, ⟨⟩) m
          ⟨rfl, by decide, by rw [h1_nat]; omega, rfl, fun t ht1 htlt => by omega⟩)

theorem ar_mvanish_wp (Γ : T.Env)
    (hHas : ∀ xs m Q X, arMhasFromSpec xs m Q X →
      Γ "ar_mhas_from" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ xs m Q X, arMvanishSpec xs m Q X → Func.wp Γ ar_mvanish_body xs m Q X := by
  rintro ⟨cx, mPtr, ⟨⟩⟩ m Q X
    ⟨s, partnerArr, mBase, mArr, mOff, σ, R, hmPtr, hM, hlt32, hn32, hPart, hm, hQ⟩
  subst hmPtr
  let Rm := arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆ R
  let Rp := arCtxMem cx s ⋆ array (t := i32) mBase mArr ⋆ R
  try c0_hsteps
  · exact wp_load_arr32 (base := mBase) (off := mOff) (i := 0) (R := Rm) (by simp) hM.1
      (sep_cast hm (by dsimp only [Rm]; ac_rfl)) (by
      c0_hsteps
      refine wp_loop_group (fun rem ⟨i, ⟨⟩⟩ m' =>
          m' = m ∧ 1 ≤ i.toNat ∧ i.toNat ≤ (mArr.getD mOff 0#32).toNat + 1 ∧
          rem = (mArr.getD mOff 0#32).toNat + 1 - i.toNat) ?_ ?_
      · intro J rem ⟨i, ⟨⟩⟩ m' hrec ⟨hm', hi1, hile, hrem⟩
        subst hm'
        c0_hsteps
        · have hilt : i.toNat ≤ (mArr.getD mOff 0#32).toNat := by
            rw [getD_eq_getElem mArr 0#32 hM.1]; exact hc
          have hlt_m : mOff + i.toNat < mArr.length := by
            have := hM.2; omega
          have hip1 : (i + 1).toNat = i.toNat + 1 := by
            rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
          try c0_hsteps
          · exact wp_load_arr32_idx (base := mBase) (off := mOff) (i := i) (R := Rm)
              rfl hlt_m (sep_cast hm (by dsimp only [Rm]; ac_rfl)) (by
              let x := mArr[mOff + i.toNat]'hlt_m
              c0_hsteps
              · have hvlt : (x >>> (1 : Nat)).toNat < s.n_nets.toNat := hc
                try c0_hsteps
                · exact wp_load_arr32_idx (base := s.partner) (xs := partnerArr) (off := 0)
                    (i := x >>> (1 : Nat)) (R := Rp) (by dsimp only [x]; simp)
                    (by have := hPart.1; omega)
                    (sep_cast hm (by dsimp only [Rp]; ac_rfl)) (by
                    c0_hsteps
                    · refine wp_call_of_spec _ _ (hHas _ _ _ _
                        ⟨mBase, mArr, mOff, Rm, rfl, hM, hlt32,
                          by dsimp only [Arg.val]; rw [hip1]; omega,
                          by dsimp only [Arg.val]; rw [hip1]; exact Nat.succ_le_succ hilt,
                          sep_cast hm (by dsimp only [Rm]; ac_rfl), fun ok hok _ => ?_⟩)
                      c0_hsteps
                      · refine hQ true (fun _ => ?_)
                        obtain ⟨idx, hlo, hidx_le, hidx_eq⟩ := hok hc
                        have hx_even : x.toNat % 2 = 0 := by
                          have hev : (mArr[mOff + i.toNat]'hlt_m &&& 1#32) = 0#32 := ‹_›
                          have h1 := congrArg BitVec.toNat hev
                          rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
                            show (0#32 : BitVec 32).toNat = 0 from rfl,
                            Nat.and_one_is_mod] at h1
                          exact h1
                        have hx_eq : x.toNat = 2 * (x >>> (1 : Nat)).toNat := by
                          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                            Nat.pow_one]
                          omega
                        let v := (x >>> (1 : Nat)).toNat
                        let p := partnerArr.getD v 0#32
                        have hp_ne : p ≠ cNone32 := by
                          dsimp only [p]
                          rw [getD_eq_getElem partnerArr 0#32 (by have := hPart.1; omega)]
                          simpa [v, cNone32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                            Nat.pow_one] using ‹¬ partnerArr[0 + x.toNat / 2 ^ 1]'_ = 4294967295#32›
                        have hpr := hPart.2 v hvlt hp_ne
                        have hmem1 : 2 * v ∈ symListAt mArr mOff := by
                          rw [mem_symListAt_iff]
                          exact ⟨i.toNat, hi1, hilt, by
                            rw [getD_eq_getElem mArr 0#32 hlt_m, ← hx_eq]⟩
                        have hmem2 : 2 * p.toNat ∈ symListAt mArr mOff := by
                          rw [mem_symListAt_iff]
                          dsimp only [Arg.val] at hlo
                          rw [hip1] at hlo
                          refine ⟨idx, by omega, hidx_le, ?_⟩
                          dsimp only [Arg.val] at hidx_eq
                          simp only [Nat.zero_add] at hidx_eq
                          rw [hidx_eq]
                          dsimp only [p]
                          have hlt_nets : (partnerArr.getD v 0#32).toNat < s.n_nets.toNat := by
                            dsimp only [p] at hpr; exact hpr.1
                          rw [getD_eq_getElem partnerArr 0#32
                            (by have := hPart.1; omega)] at hlt_nets ⊢
                          dsimp only [v] at hlt_nets
                          rw [BitVec.toNat_mul, show (2 : BitVec 32).toNat = 2 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        by_cases hv_f : σ (2 * v) = false
                        · exact monoValL_false_of_mem hmem1 hv_f
                        · have hp_f : σ (2 * p.toNat) = false := by
                            have hσv : σ (2 * v) = true := by
                              cases h : σ (2 * v) with
                              | true => rfl
                              | false => exact absurd h hv_f
                            cases hσp : σ (2 * p.toNat) with
                            | false => rfl
                            | true => exact False.elim (hpr.2 ⟨hσv, hσp⟩)
                          exact monoValL_false_of_mem hmem2 hp_f
                      · exact hrec ((mArr.getD mOff 0#32).toNat + 1 - (i + 1).toNat)
                          (i + 1, ⟨⟩) m' (by omega) ⟨rfl, by omega, by omega, rfl⟩
                    · exact hrec ((mArr.getD mOff 0#32).toNat + 1 - (i + 1).toNat)
                        (i + 1, ⟨⟩) m' (by omega) ⟨rfl, by omega, by omega, rfl⟩
                    · exact hrec ((mArr.getD mOff 0#32).toNat + 1 - (i + 1).toNat)
                        (i + 1, ⟨⟩) m' (by omega) ⟨rfl, by omega, by omega, rfl⟩)
              · exact hrec ((mArr.getD mOff 0#32).toNat + 1 - (i + 1).toNat)
                  (i + 1, ⟨⟩) m' (by omega) ⟨rfl, by omega, by omega, rfl⟩
              · exact hrec ((mArr.getD mOff 0#32).toNat + 1 - (i + 1).toNat)
                  (i + 1, ⟨⟩) m' (by omega) ⟨rfl, by omega, by omega, rfl⟩)
        · exact hQ false (fun h => by cases h)
      · intro J hJ
        c0_hsteps
        have h1_nat : (1#32 : BitVec 32).toNat = 1 := rfl
        exact hJ ((mArr.getD mOff 0#32).toNat + 1 - 1) (1#32, ⟨⟩) m
          ⟨rfl, by decide, by rw [h1_nat]; omega, rfl⟩)

end

end LeanQbe.T.Examples.Arisca.Proof
