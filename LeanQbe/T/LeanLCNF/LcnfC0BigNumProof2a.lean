module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof1
import Kraken.Mem
import Kraken.Separation
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Soundness Proofs for `LcnfC0BigNum` Multi-Limb Operations (`Milestone R1`, Part 2a)

Shared separation-logic / `limbsVal` / loop-combinator helpers and Part A proofs:
`bn_add`, `bn_add_one`, `bn_sub`, `bn_sub_one`, `bn_bitwise`.
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

/-! ## 1. Separation-Logic, List/LimbsVal, and Control-Flow Helpers -/

theorem nat_lt_1_64 : (1#64 : BitVec 64).toNat < 64 := by decide

theorem nat_lt_64_pow64 : 64 < 2 ^ 64 := by decide

theorem bv64_1_ne_0 : (1#64 : BitVec 64) ≠ 0#64 := by decide

theorem bv64_2_ne_0 : (2#64 : BitVec 64) ≠ 0#64 := by decide

theorem bv64_2_ne_1 : (2#64 : BitVec 64) ≠ 1#64 := by decide

theorem bool_toNat_le_one (b : Bool) : b.toNat ≤ 1 := by
  cases b <;> simp

theorem bool_toNat_lt_pow64 (b : Bool) : b.toNat < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (bool_toNat_le_one b) (Nat.one_lt_two_pow (by omega))

theorem bv64_bool_toNat (b : Bool) : (BitVec.ofNat 64 b.toNat).toNat = b.toNat := by
  cases b <;> rfl

theorem sep_swap23 {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C)) m) : (B ⋆ (A ⋆ C)) m := sep_ac h

theorem sep_pick2_3_r4 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C ⋆ D)) m) : (B ⋆ (A ⋆ C ⋆ D)) m := sep_ac h

theorem sep_pick3_of3r {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C ⋆ D)) m) : (C ⋆ (A ⋆ B ⋆ D)) m := sep_ac h

theorem sep_pick3_4 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D) m) : (C ⋆ (A ⋆ B ⋆ D)) m := sep_ac h

theorem sep_unpick3_4 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ B ⋆ D)) m) : (A ⋆ B ⋆ C ⋆ D) m := sep_ac h

theorem sep_pick3_5 {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ E) m) : (C ⋆ (A ⋆ B ⋆ D ⋆ E)) m := sep_ac h

theorem sep_unpick3_5 {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ B ⋆ D ⋆ E)) m) : (A ⋆ B ⋆ C ⋆ D ⋆ E) m := sep_ac h

theorem sep_pick4_5 {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ E) m) : (D ⋆ (A ⋆ B ⋆ C ⋆ E)) m := sep_ac h

theorem sep_unpick4_5 {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (D ⋆ (A ⋆ B ⋆ C ⋆ E)) m) : (A ⋆ B ⋆ C ⋆ D ⋆ E) m := sep_ac h

theorem list_take_set_eq_of_le {α : Type _} (xs : List α) {i k : Nat} (v : α)
    (hki : k ≤ i) : (xs.set i v).take k = xs.take k := by
  induction xs generalizing i k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k' =>
      cases i with
      | zero => omega
      | succ i' =>
        simp only [List.set_cons_succ, List.take_succ_cons]
        congr 1
        exact ih (by omega)

theorem list_take_succ_set {α : Type _} (xs : List α) {i : Nat} (v : α)
    (hi : i < xs.length) : (xs.set i v).take (i + 1) = xs.take i ++ [v] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.length_cons] at hi
      simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
      congr 1
      exact ih (by omega)

theorem limbsVal_take_set_succ (xs : List (BitVec 64)) {i : Nat} (v : BitVec 64)
    (hi : i < xs.length) :
    limbsVal ((xs.set i v).take (i + 1)) = limbsVal (xs.take i) + 2 ^ (64 * i) * v.toNat := by
  rw [list_take_succ_set xs v hi, limbsVal_snoc, List.length_take_of_le (Nat.le_of_lt hi)]

theorem limbsVal_take_min_succ (xs : List (BitVec 64)) {n i : Nat} (hn : n ≤ xs.length) :
    limbsVal (xs.take (min (i + 1) n)) =
      limbsVal (xs.take (min i n)) +
        2 ^ (64 * i) * (if h : i < n then xs[i]'(Nat.lt_of_lt_of_le h hn) else 0#64).toNat := by
  by_cases hi : i < n
  · simp only [hi, ↓reduceDIte]
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (Nat.le_of_lt hi)]
    exact limbsVal_take_succ (Nat.lt_of_lt_of_le hi hn)
  · simp only [hi, ↓reduceDIte, show min (i + 1) n = n by omega, show min i n = n by omega]
    simp

theorem limbsVal_take_eq_of_lt_pow {xs : List (BitVec 64)} {n k : Nat}
    (hk : k ≤ n) (hn : n ≤ xs.length) (hlt : limbsVal (xs.take n) < 2 ^ (64 * k)) :
    limbsVal (xs.take k) = limbsVal (xs.take n) := by
  have hnk : k + (n - k) = n := by omega
  have hsplit : xs.take n = xs.take k ++ (xs.drop k).take (n - k) := by
    have h := List.take_add (l := xs) (i := k) (j := n - k)
    rwa [hnk] at h
  rw [hsplit, limbsVal_append, List.length_take_of_le (Nat.le_trans hk hn)] at hlt ⊢
  have hzero : limbsVal ((xs.drop k).take (n - k)) = 0 := by
    by_cases hz : limbsVal ((xs.drop k).take (n - k)) = 0
    · exact hz
    · have h1 : 1 ≤ limbsVal ((xs.drop k).take (n - k)) := Nat.pos_of_ne_zero hz
      have h2 : 2 ^ (64 * k) ≤ 2 ^ (64 * k) * limbsVal ((xs.drop k).take (n - k)) :=
        Nat.le_mul_of_pos_right _ h1
      omega
  rw [hzero, Nat.mul_zero, Nat.add_zero]

theorem addc_limbs_step {outP aP bP : Nat} {va vb s : BitVec 64} {carry co : Bool} {i : Nat}
    (hInv : outP + (if carry then 1 else 0) * 2 ^ (64 * i) = aP + bP)
    (haddc : co.toNat * 2 ^ 64 + s.toNat = va.toNat + vb.toNat + Bool.toNat carry) :
    (outP + 2 ^ (64 * i) * s.toNat) + (if co then 1 else 0) * 2 ^ (64 * (i + 1)) =
      (aP + 2 ^ (64 * i) * va.toNat) + (bP + 2 ^ (64 * i) * vb.toNat) := by
  have hcNat : Bool.toNat carry = if carry then 1 else 0 := by cases carry <;> rfl
  have hcoNat : co.toNat = if co then 1 else 0 := by cases co <;> rfl
  rw [hcNat, hcoNat] at haddc
  have hmul := congrArg (fun x => 2 ^ (64 * i) * x) haddc
  simp only [Nat.mul_add, ← Nat.mul_assoc] at hmul
  rw [show 2 ^ (64 * i) * (if co then 1 else 0) * 2 ^ 64 =
      (if co then 1 else 0) * 2 ^ (64 * (i + 1)) by
    rw [Nat.mul_add, Nat.pow_add]; ac_rfl] at hmul
  rw [show 2 ^ (64 * i) * (if carry then 1 else 0) =
      (if carry then 1 else 0) * 2 ^ (64 * i) from Nat.mul_comm _ _] at hmul
  omega

theorem subb_limbs_step {outP bP aP : Nat} {va vb d : BitVec 64} {borrow bo : Bool} {i : Nat}
    (hInv : outP + bP = aP + (if borrow then 1 else 0) * 2 ^ (64 * i))
    (hsubb : d.toNat + vb.toNat + Bool.toNat borrow = va.toNat + bo.toNat * 2 ^ 64) :
    (outP + 2 ^ (64 * i) * d.toNat) + (bP + 2 ^ (64 * i) * vb.toNat) =
      (aP + 2 ^ (64 * i) * va.toNat) + (if bo then 1 else 0) * 2 ^ (64 * (i + 1)) := by
  have hbrNat : Bool.toNat borrow = if borrow then 1 else 0 := by cases borrow <;> rfl
  have hboNat : bo.toNat = if bo then 1 else 0 := by cases bo <;> rfl
  rw [hbrNat, hboNat] at hsubb
  have hmul := congrArg (fun x => 2 ^ (64 * i) * x) hsubb
  simp only [Nat.mul_add, ← Nat.mul_assoc] at hmul
  rw [show 2 ^ (64 * i) * (if bo then 1 else 0) * 2 ^ 64 =
      (if bo then 1 else 0) * 2 ^ (64 * (i + 1)) by
    rw [Nat.mul_add, Nat.pow_add]; ac_rfl] at hmul
  rw [show 2 ^ (64 * i) * (if borrow then 1 else 0) =
      (if borrow then 1 else 0) * 2 ^ (64 * i) from Nat.mul_comm _ _] at hmul
  omega

theorem bv64_addc_eq (x y : BitVec 64) (cin : Bool) :
    (decide (2 ^ 64 ≤ x.toNat + y.toNat + Bool.toNat cin)).toNat * 2 ^ 64 +
        (x + y + BitVec.ofNat 64 (Bool.toNat cin)).toNat =
      x.toNat + y.toNat + Bool.toNat cin := by
  have heq : x + y + BitVec.ofNat 64 (Bool.toNat cin) =
      BitVec.ofNat 64 (x.toNat + y.toNat + if cin = true then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    have hc : (if cin = true then 1 else 0) = Bool.toNat cin := by cases cin <;> rfl
    rw [hc, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hx := x.isLt; have hy := y.isLt
    have hci : Bool.toNat cin < 2 ^ 64 := bool_toNat_lt_pow64 cin
    omega
  rw [heq]
  have hc : (if cin = true then 1 else 0) = Bool.toNat cin := by cases cin <;> rfl
  have hnat := addc64_nat x y cin
  dsimp only at hnat
  have hco : (decide (2 ^ 64 ≤ x.toNat + y.toNat + Bool.toNat cin)).toNat * 2 ^ 64 =
      if decide (2 ^ 64 ≤ x.toNat + y.toNat + if cin = true then 1 else 0) =
        true then 2 ^ 64 else 0 := by
    by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat + Bool.toNat cin <;> simp [hc, h]
  rw [hco, ← hc, Nat.add_comm]
  exact hnat

theorem bv64_subb_eq (x y : BitVec 64) (bin : Bool) :
    (x - y - BitVec.ofNat 64 (Bool.toNat bin)).toNat + y.toNat + Bool.toNat bin =
      x.toNat + (decide (x.toNat < y.toNat + Bool.toNat bin)).toNat * 2 ^ 64 := by
  have heq : x - y - BitVec.ofNat 64 (Bool.toNat bin) =
      BitVec.ofNat 64 (2 ^ 64 + x.toNat - y.toNat - if bin = true then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    have hx := x.isLt; have hy := y.isLt
    cases bin <;> simp [BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  rw [heq]
  have hb : (if bin = true then 1 else 0) = Bool.toNat bin := by cases bin <;> rfl
  have hnat := subb64_nat x y bin
  dsimp only at hnat
  have hbo : (decide (x.toNat < y.toNat + Bool.toNat bin)).toNat * 2 ^ 64 =
      if decide (x.toNat < y.toNat + if bin = true then 1 else 0) = true then 2 ^ 64 else 0 := by
    by_cases h : x.toNat < y.toNat + Bool.toNat bin <;> simp [hb, h]
  rw [hbo, ← hb]
  exact hnat

theorem limbsVal_take_testBit (xs : List (BitVec 64)) {n : Nat} (hn : n ≤ xs.length) (k : Nat) :
    (limbsVal (xs.take n)).testBit k =
      if h : k / 64 <
        n then (xs[k / 64]'(Nat.lt_of_lt_of_le h hn)).toNat.testBit (k % 64) else false := by
  rw [limbsVal_testBit]
  have hlen : (xs.take n).length = n := List.length_take_of_le hn
  by_cases hk : k / 64 < n
  · have hlt : k / 64 < (xs.take n).length := by omega
    simp only [hlt, ↓reduceDIte, hk, List.getElem_take]
  · have hge : ¬ k / 64 < (xs.take n).length := by omega
    simp only [hge, ↓reduceDIte, hk]

private def bwOp (op a b : BitVec 64) : BitVec 64 :=
  if op = 0#64 then a &&& b else if op = 1#64 then a ||| b else a ^^^ b

private theorem limbsVal_bitwise_aux (aXs bXs outXs : List (BitVec 64)) (na nb nres : Nat)
    (f : Bool → Bool → Bool)
    (hna : na ≤ aXs.length) (hnb : nb ≤ bXs.length) (hnout : nres ≤ outXs.length)
    (hnres : (nres = min na nb ∧ ∀ b, f false b = false ∧ f b false = false) ∨
      (na ≤ nres ∧ nb ≤ nres ∧ f false false = false))
    (res : Nat) (hres : ∀ k, res.testBit k =
      f ((limbsVal (aXs.take na)).testBit k) ((limbsVal (bXs.take nb)).testBit k))
    (hlim : ∀ j (hj : j < nres) r,
      (outXs[j]'(Nat.lt_of_lt_of_le hj hnout)).toNat.testBit r =
        f (if ha : j < na then (aXs[j]'(Nat.lt_of_lt_of_le ha hna)).toNat.testBit r else false)
          (if hb : j < nb then (bXs[j]'(Nat.lt_of_lt_of_le hb hnb)).toNat.testBit r
            else false)) :
    limbsVal (outXs.take nres) = res := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [hres k, limbsVal_take_testBit _ hnout, limbsVal_take_testBit _ hna,
    limbsVal_take_testBit _ hnb]
  by_cases hj : k / 64 < nres
  · simp only [hj, ↓reduceDIte]
    exact hlim (k / 64) hj (k % 64)
  · simp only [hj, ↓reduceDIte]
    rcases hnres with ⟨hmin, hfb⟩ | ⟨ha', hb', hf0⟩
    · by_cases ha : k / 64 < na
      · simp only [ha, ↓reduceDIte, show ¬ k / 64 < nb by omega, (hfb _).2]
      · simp only [ha, ↓reduceDIte, (hfb _).1]
    · simp only [show ¬ k / 64 < na by omega, show ¬ k / 64 < nb by omega, ↓reduceDIte, hf0]

private theorem limbsVal_bitwise_eq
    (op : BitVec 64) (hop : op = 0#64 ∨ op = 1#64 ∨ op = 2#64)
    (aXs bXs outXs : List (BitVec 64)) (na nb nres : Nat)
    (hna : na ≤ aXs.length) (hnb : nb ≤ bXs.length) (hnout : nres ≤ outXs.length)
    (hnres : nres = if op = 0#64 then min na nb else max na nb)
    (hlim : ∀ j (hj : j < nres),
      outXs[j]'(Nat.lt_of_lt_of_le hj hnout) =
        bwOp op (if ha : j < na then aXs[j]'(Nat.lt_of_lt_of_le ha hna) else 0#64)
                (if hb : j < nb then bXs[j]'(Nat.lt_of_lt_of_le hb hnb) else 0#64)) :
    limbsVal (outXs.take nres) =
      if op = 0#64 then (limbsVal (aXs.take na)).land (limbsVal (bXs.take nb))
      else if op = 1#64 then (limbsVal (aXs.take na)).lor (limbsVal (bXs.take nb))
      else (limbsVal (aXs.take na)).xor (limbsVal (bXs.take nb)) := by
  have h10 := bv64_1_ne_0
  have h20 := bv64_2_ne_0
  have h21 := bv64_2_ne_1
  have h0n : (0#64 : BitVec 64).toNat = 0 := rfl
  rcases hop with rfl | rfl | rfl
  · simp only [↓reduceIte] at hnres ⊢
    refine limbsVal_bitwise_aux aXs bXs outXs na nb nres (· && ·) hna hnb hnout
      (Or.inl ⟨hnres, fun b => ⟨by simp, by simp⟩⟩) _ (fun k => Nat.testBit_and ..)
      fun j hj r => ?_
    have ha : j < na := by omega
    have hb : j < nb := by omega
    rw [hlim j hj, bwOp]
    simp only [↓reduceIte, ha, hb, ↓reduceDIte, BitVec.toNat_and, Nat.testBit_and]
  · simp only [h10, ↓reduceIte] at hnres ⊢
    refine limbsVal_bitwise_aux aXs bXs outXs na nb nres (· || ·) hna hnb hnout
      (Or.inr ⟨by omega, by omega, rfl⟩) _ (fun k => Nat.testBit_or ..) fun j hj r => ?_
    rw [hlim j hj, bwOp]
    simp only [h10, ↓reduceIte, BitVec.toNat_or, Nat.testBit_or]
    by_cases ha : j < na <;> by_cases hb : j < nb <;>
      simp [ha, hb, h0n, Nat.zero_testBit]
  · simp only [h20, h21, ↓reduceIte] at hnres ⊢
    refine limbsVal_bitwise_aux aXs bXs outXs na nb nres Bool.xor hna hnb hnout
      (Or.inr ⟨by omega, by omega, rfl⟩) _ (fun k => Nat.testBit_xor ..) fun j hj r => ?_
    rw [hlim j hj, bwOp]
    simp only [h20, h21, ↓reduceIte, BitVec.toNat_xor, Nat.testBit_xor]
    by_cases ha : j < na <;> by_cases hb : j < nb <;>
      simp [ha, hb, h0n, Nat.zero_testBit]

theorem bn_trim_tail_wp {Q : Post [i64]} {X : XPost}
    {out : BitVec 64} {nMax : Nat} (hnMax64 : nMax < 2 ^ 64)
    {outXs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hnLe : nMax ≤ outXs.length) (hm : (array64 out outXs ⋆ R) m)
    {targetVal : Nat} (hVal : limbsVal (outXs.take nMax) = targetVal)
    (hQ : limbLenNat targetVal ≤ outXs.length →
      limbsVal (outXs.take (limbLenNat targetVal)) = targetVal →
      Q (BitVec.ofNat 64 (limbLenNat targetVal), ()) m) :
    wp rtR1Env Q X
      (Expr.call (V := Val) (L := Cont) (rs := [i64]) (as := [i64, i64]) (bs := [i64]) "bn_trim"
        (Arg.var out, Arg.var (BitVec.ofNat 64 nMax), ())
        fun p => Expr.ret (Arg.var p.fst, ()))
      m := by
  apply wp_call_of
  apply rtR1Env_bn_trim
  dsimp only [bnTrimSpec, vals, Tup.map, Arg.val]
  refine ⟨outXs, R, ?_, hm, ?_⟩
  · rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnMax64]
  · change wp rtR1Env Q X (Expr.ret (Arg.var (BitVec.ofNat 64 (trimLenLoop outXs
    (BitVec.ofNat 64 nMax).toNat)), ())) m
    rw [wp_ret]
    dsimp only [vals, Tup.map, Arg.val]
    have hnToNat : (BitVec.ofNat 64 nMax).toNat = nMax := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnMax64]
    have hTrimEq : trimLenLoop outXs (BitVec.ofNat 64 nMax).toNat = limbLenNat targetVal := by
      rw [hnToNat, ← hVal, limbLenNat_trimLenLoop hnLe]
    have hLenLe : limbLenNat targetVal ≤ outXs.length := by
      rw [← hTrimEq, hnToNat]
      exact Nat.le_trans (trimLenLoop_le outXs nMax) hnLe
    have hTakeEq : limbsVal (outXs.take (limbLenNat targetVal)) = targetVal := by
      rw [← hVal, limbLenNat_trimLenLoop hnLe, limbsVal_trimLenLoop outXs nMax hnLe]
    rw [hTrimEq]
    exact hQ hLenLe hTakeEq

theorem bv64_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem wp_join_tup {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (body : Tup Val ts → Expr Val Cont rs) (entry : Tup Cont [ts] → Expr Val Cont rs)
    (P : Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (xs : Tup Val ts) (m : Mem 64), P xs m → wp Γ Q X (body xs) m)
    (hentry : ∀ (Js : Tup Cont [ts]), (∀ (xs : Tup Val ts) (m : Mem 64), P xs m → Js.fst xs m) →
      wp Γ Q X (entry Js) m) :
    wp Γ Q X (Expr.group (fun _ => Blocks.cons body Blocks.nil) entry) m :=
  wp_join body (fun J => entry (J, ())) P hbody (fun J h => hentry (J, ()) h)

/-! ## 1b. `BigNumLoopKit`: Indexed Loop & `bn_trim` Tail Combinators -/

theorem wp_cursor_up_loop {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[i64]] → Blocks Val Cont rs [[i64]]}
    {entry : Tup Cont [[i64]] → Expr Val Cont rs}
    (lo hi : Nat) (hhi : hi < 2 ^ 64) {α : Type _} (Inv : Nat → α → Mem 64 → Prop)
    (hentry : ∀ J : Cont [i64],
      (∀ a m', lo ≤ hi → Inv lo a m' → J (BitVec.ofNat 64 lo, ()) m') →
      wp rtR1Env Q X (entry (J, ())) m)
    (hstep : ∀ (J : Cont [i64]) i a mL, i ≤ hi → i < 2 ^ 64 →
      (BitVec.ofNat 64 i).toNat = i → Inv i a mL →
      (∀ a' m', i + 1 ≤ hi → Inv (i + 1) a' m' → J (BitVec.ofNat 64 i + 1, ()) m') →
      wp rtR1Env Q X ((bodies (J, ())).get Member.here (BitVec.ofNat 64 i, ())) mL) :
    wp rtR1Env Q X (Expr.group (fun Js => bodies Js) entry) m := by
  refine wp_loop_inv
    (fun (xs : Tup Val [i64]) mL =>
      ∃ (i : Nat) (a : α), i ≤ hi ∧ xs.1 = BitVec.ofNat 64 i ∧ Inv i a mL)
    (fun (xs : Tup Val [i64]) _ => hi - xs.1.toNat)
    (fun J hJ => hentry J fun a m' hle hinv =>
      hJ (BitVec.ofNat 64 lo, ()) m' ⟨lo, a, hle, rfl, hinv⟩)
    ?_
  intro J ⟨iBv, ⟨⟩⟩ mL ⟨i, a, hiLe, hiEq, hinv⟩ hRec
  dsimp only at hiEq; subst hiEq
  have hiLt64 : i < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe hhi
  have hiToNat : (BitVec.ofNat 64 i).toNat = i := ArrayCursorInv.toNat_ofNat_lt hiLt64
  refine hstep J i a mL hiLe hiLt64 hiToNat hinv fun a' m' hi1 hinv' => ?_
  rw [ArrayCursorInv.ofNat_add_one]
  refine hRec (BitVec.ofNat 64 (i + 1), ()) m' ?_ ⟨i + 1, a', hi1, rfl, hinv'⟩
  show hi - (BitVec.ofNat 64 (i + 1)).toNat < hi - (BitVec.ofNat 64 i).toNat
  rw [hiToNat, ArrayCursorInv.toNat_ofNat_lt (by omega)]; omega

theorem wp_pair_up_loop {rs : List Ty} {t0 : Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[t0, i64]] → Blocks Val Cont rs [[t0, i64]]}
    {entry : Tup Cont [[t0, i64]] → Expr Val Cont rs}
    (lo hi : Nat) (hhi : hi < 2 ^ 64) {α : Type _} (Inv : Nat → Val t0 → α → Mem 64 → Prop)
    (hentry : ∀ J : Cont [t0, i64],
      (∀ v a m', lo ≤ hi → Inv lo v a m' → J (v, BitVec.ofNat 64 lo, ()) m') →
      wp rtR1Env Q X (entry (J, ())) m)
    (hstep : ∀ (J : Cont [t0, i64]) i v a mL, i ≤ hi → i < 2 ^ 64 →
      (BitVec.ofNat 64 i).toNat = i → Inv i v a mL →
      (∀ v' a' m', i + 1 ≤ hi → Inv (i + 1) v' a' m' →
        J (v', BitVec.ofNat 64 i + 1, ()) m') →
      wp rtR1Env Q X ((bodies (J, ())).get Member.here (v, BitVec.ofNat 64 i, ())) mL) :
    wp rtR1Env Q X (Expr.group (fun Js => bodies Js) entry) m := by
  refine wp_loop_inv
    (fun (xs : Tup Val [t0, i64]) mL =>
      ∃ (i : Nat) (v : Val t0) (a : α),
        i ≤ hi ∧ xs.1 = v ∧ xs.2.1 = BitVec.ofNat 64 i ∧ Inv i v a mL)
    (fun (xs : Tup Val [t0, i64]) _ => hi - xs.2.1.toNat)
    (fun J hJ => hentry J fun v a m' hle hinv =>
      hJ (v, BitVec.ofNat 64 lo, ()) m' ⟨lo, v, a, hle, rfl, rfl, hinv⟩)
    ?_
  intro J ⟨v, iBv, ⟨⟩⟩ mL ⟨i, v', a, hiLe, hvEq, hiEq, hinv⟩ hRec
  dsimp only at hvEq hiEq; subst hvEq; subst hiEq
  have hiLt64 : i < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe hhi
  have hiToNat : (BitVec.ofNat 64 i).toNat = i := ArrayCursorInv.toNat_ofNat_lt hiLt64
  refine hstep J i v a mL hiLe hiLt64 hiToNat hinv fun v' a' m' hi1 hinv' => ?_
  rw [ArrayCursorInv.ofNat_add_one]
  refine hRec (v', BitVec.ofNat 64 (i + 1), ()) m' ?_ ⟨i + 1, v', a', hi1, rfl, rfl, hinv'⟩
  show hi - (BitVec.ofNat 64 (i + 1)).toNat < hi - (BitVec.ofNat 64 i).toNat
  rw [hiToNat, ArrayCursorInv.toNat_ofNat_lt (by omega)]; omega

theorem wp_cursor_down_loop {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[i64]] → Blocks Val Cont rs [[i64]]}
    {entry : Tup Cont [[i64]] → Expr Val Cont rs}
    (hi : Nat) (hhi : hi < 2 ^ 64) {α : Type _} (Inv : Nat → α → Mem 64 → Prop)
    (hentry : ∀ J : Cont [i64],
      (∀ a m', Inv hi a m' → J (BitVec.ofNat 64 hi, ()) m') →
      wp rtR1Env Q X (entry (J, ())) m)
    (hstep : ∀ (J : Cont [i64]) i a mL, i ≤ hi → i < 2 ^ 64 →
      (BitVec.ofNat 64 i).toNat = i → Inv i a mL →
      (∀ i' a' m', i = i' + 1 → Inv i' a' m' → J (BitVec.ofNat 64 i - 1, ()) m') →
      wp rtR1Env Q X ((bodies (J, ())).get Member.here (BitVec.ofNat 64 i, ())) mL) :
    wp rtR1Env Q X (Expr.group (fun Js => bodies Js) entry) m := by
  refine wp_loop_inv
    (fun (xs : Tup Val [i64]) mL =>
      ∃ (i : Nat) (a : α), i ≤ hi ∧ xs.1 = BitVec.ofNat 64 i ∧ Inv i a mL)
    (fun (xs : Tup Val [i64]) _ => xs.1.toNat)
    (fun J hJ => hentry J fun a m' hinv =>
      hJ (BitVec.ofNat 64 hi, ()) m' ⟨hi, a, le_refl _, rfl, hinv⟩)
    ?_
  intro J ⟨iBv, ⟨⟩⟩ mL ⟨i, a, hiLe, hiEq, hinv⟩ hRec
  dsimp only at hiEq; subst hiEq
  have hiLt64 : i < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe hhi
  have hiToNat : (BitVec.ofNat 64 i).toNat = i := ArrayCursorInv.toNat_ofNat_lt hiLt64
  refine hstep J i a mL hiLe hiLt64 hiToNat hinv fun i' a' m' hpred hinv' => ?_
  subst hpred
  have hsub : BitVec.ofNat 64 (i' + 1) - (1 : BitVec 64) = BitVec.ofNat 64 i' := by
    apply BitVec.eq_of_toNat_eq; c0_bv_omega
  rw [hsub]
  refine hRec (BitVec.ofNat 64 i', ()) m' ?_ ⟨i', a', by omega, rfl, hinv'⟩
  show (BitVec.ofNat 64 i').toNat < (BitVec.ofNat 64 (i' + 1)).toNat
  rw [hiToNat, ArrayCursorInv.toNat_ofNat_lt (by omega)]; omega

theorem wp_pair_down_loop {rs : List Ty} {t0 : Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[t0, i64]] → Blocks Val Cont rs [[t0, i64]]}
    {entry : Tup Cont [[t0, i64]] → Expr Val Cont rs}
    (hi : Nat) (hhi : hi < 2 ^ 64) {α : Type _} (Inv : Nat → Val t0 → α → Mem 64 → Prop)
    (hentry : ∀ J : Cont [t0, i64],
      (∀ v a m', Inv hi v a m' → J (v, BitVec.ofNat 64 hi, ()) m') →
      wp rtR1Env Q X (entry (J, ())) m)
    (hstep : ∀ (J : Cont [t0, i64]) i v a mL, i ≤ hi → i < 2 ^ 64 →
      (BitVec.ofNat 64 i).toNat = i → Inv i v a mL →
      (∀ i' v' a' m', i = i' + 1 → Inv i' v' a' m' → J (v', BitVec.ofNat 64 i - 1, ()) m') →
      wp rtR1Env Q X ((bodies (J, ())).get Member.here (v, BitVec.ofNat 64 i, ())) mL) :
    wp rtR1Env Q X (Expr.group (fun Js => bodies Js) entry) m := by
  refine wp_loop_inv
    (fun (xs : Tup Val [t0, i64]) mL =>
      ∃ (i : Nat) (v : Val t0) (a : α),
        i ≤ hi ∧ xs.1 = v ∧ xs.2.1 = BitVec.ofNat 64 i ∧ Inv i v a mL)
    (fun (xs : Tup Val [t0, i64]) _ => xs.2.1.toNat)
    (fun J hJ => hentry J fun v a m' hinv =>
      hJ (v, BitVec.ofNat 64 hi, ()) m' ⟨hi, v, a, le_refl _, rfl, rfl, hinv⟩)
    ?_
  intro J ⟨v, iBv, ⟨⟩⟩ mL ⟨i, v', a, hiLe, hvEq, hiEq, hinv⟩ hRec
  dsimp only at hvEq hiEq; subst hvEq; subst hiEq
  have hiLt64 : i < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe hhi
  have hiToNat : (BitVec.ofNat 64 i).toNat = i := ArrayCursorInv.toNat_ofNat_lt hiLt64
  refine hstep J i v a mL hiLe hiLt64 hiToNat hinv fun i' v' a' m' hpred hinv' => ?_
  subst hpred
  have hsub : BitVec.ofNat 64 (i' + 1) - (1 : BitVec 64) = BitVec.ofNat 64 i' := by
    apply BitVec.eq_of_toNat_eq; c0_bv_omega
  rw [hsub]
  refine hRec (v', BitVec.ofNat 64 i', ()) m' ?_ ⟨i', v', a', by omega, rfl, rfl, hinv'⟩
  show (BitVec.ofNat 64 i').toNat < (BitVec.ofNat 64 (i' + 1)).toNat
  rw [hiToNat, ArrayCursorInv.toNat_ofNat_lt (by omega)]; omega

/-! ## 2. Proofs of Multi-Limb Operations (`Part A`: `bn_add` .. `bn_bitwise`) -/

theorem bn_add_wp :
    ∀ xs m Q X, bnAddSpec xs m Q X → Func.wp rtR1Env bn_add.body xs m Q X := by
  intro ⟨a, na, b, nb, out, ⟨⟩⟩ m Q X ⟨aXs, bXs, outXs, R, hna, hnb, hnout, hnmaxLt, hm, hQ⟩
  dsimp only [Func.wp, bn_add, bn_add_body]
  let nmax := max na.toNat nb.toNat
  have hnmaxOut : nmax + 1 ≤ outXs.length := hnout
  have hnmaxLt64 : nmax < 2 ^ 64 := by omega
  refine wp_join_tup _ _ (fun p1 m1 => p1.1 = BitVec.ofNat 64 nmax ∧ m1 = m) ?_ ?_
  · intro ⟨nmaxBv, ⟨⟩⟩ m1 ⟨hnmaxEq, hm1⟩
    dsimp only at hnmaxEq; subst hnmaxEq; rw [hm1] at *
    refine wp_pair_up_loop 0 nmax hnmaxLt64 (α := List (BitVec 64))
      (fun i carry outXs' mL => outXs'.length = outXs.length ∧
        limbsVal (outXs'.take i) + (if carry then 1 else 0) * 2 ^ (64 * i) =
          limbsVal (aXs.take (min i na.toNat)) + limbsVal (bXs.take (min i nb.toNat)) ∧
        (array64 out outXs' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mL)
      (fun J hJ => by
        c0_hsteps
        exact hJ false outXs m (Nat.zero_le _)
          ⟨rfl, by rw [limbsVal_take_zero]; rfl, sep_pick3_4 hm⟩)
      ?_
    intro J i carry outXs' mL hiLe hiLt64 hiToNat ⟨hlenOut', hSumInv, hmL⟩ hRec
    let vaRef := if ha : i < na.toNat then aXs[i]'(Nat.lt_of_lt_of_le ha hna) else 0#64
    let vbRef := if hb : i < nb.toNat then bXs[i]'(Nat.lt_of_lt_of_le hb hnb) else 0#64
    c0_hsplit
    · have hlt : i < nmax := by c0_bv_omega
      have hoLen : (BitVec.ofNat 64 i).toNat < outXs'.length := by omega
      refine wp_join_tup _ _ (fun p m1 => p.1 = vaRef ∧ m1 = mL) ?_ ?_
      · rintro ⟨va, ⟨⟩⟩ m1 ⟨hva, hm1⟩
        dsimp only at hva hm1; rw [hva, hm1] at *
        refine wp_join_tup _ _ (fun p m2 => p.1 = vbRef ∧ m2 = mL) ?_ ?_
        · rintro ⟨vb, ⟨⟩⟩ m2 ⟨hvb, hm2⟩
          dsimp only at hvb hm2; rw [hvb, hm2] at *
          c0_hsteps
          refine hRec _ (outXs'.set i (vaRef + vbRef + BitVec.ofNat 64 carry.toNat)) _ hlt
            ⟨by simp [hlenOut'], ?_, ?_⟩
          · rw [limbsVal_take_set_succ outXs' _ (by omega),
              limbsVal_take_min_succ aXs hna, limbsVal_take_min_succ bXs hnb]
            exact addc_limbs_step hSumInv (bv64_addc_eq vaRef vbRef carry)
          · rw [hiToNat] at hm; exact hm
        · intro Jb hJb
          c0_hsplit
          · have hltB : (BitVec.ofNat 64 i).toNat < bXs.length := by c0_bv_omega
            c0_hsteps
            exact hJb (bXs[(BitVec.ofNat 64 i).toNat]'hltB, ()) mL
              ⟨by simp [vbRef, show i < nb.toNat by c0_bv_omega, hiToNat], rfl⟩
          · c0_hsteps
            exact hJb (0#64, ()) mL
              ⟨by simp [vbRef, show ¬ i < nb.toNat by c0_bv_omega], rfl⟩
      · intro Ja hJa
        c0_hsplit
        · have hltA : (BitVec.ofNat 64 i).toNat < aXs.length := by c0_bv_omega
          c0_hsteps
          exact hJa (aXs[(BitVec.ofNat 64 i).toNat]'hltA, ()) mL
            ⟨by simp [vaRef, show i < na.toNat by c0_bv_omega, hiToNat], rfl⟩
        · c0_hsteps
          exact hJa (0#64, ()) mL ⟨by simp [vaRef, show ¬ i < na.toNat by c0_bv_omega], rfl⟩
    · have hiEq : i = nmax := by c0_bv_omega
      subst hiEq
      have houtLen : (BitVec.ofNat 64 nmax).toNat < outXs'.length := by omega
      c0_hsteps
      all_goals (
        have hSumFinal : limbsVal ((outXs'.set nmax (if carry then 1 else (0 : BitVec 64))).take
            (nmax + 1)) = limbsVal (aXs.take na.toNat) + limbsVal (bXs.take nb.toNat) := by
          rw [Nat.min_eq_right (Nat.le_max_left _ _),
            Nat.min_eq_right (Nat.le_max_right _ _)] at hSumInv
          rw [limbsVal_take_set_succ outXs' _ (by omega), ← hSumInv,
            show (if carry then (1 : BitVec 64) else 0).toNat =
              if carry then 1 else 0 by cases carry <;> rfl, Nat.mul_comm (2 ^ (64 * nmax))]
        dsimp only
        rw [ArrayCursorInv.ofNat_add_one]
        have hm' : (array64 out (outXs'.set nmax (if carry then (1 : BitVec 64) else 0)) ⋆
            (array64 a aXs ⋆ array64 b bXs ⋆ R)) m := by
          rw [hiToNat] at hm; simp [hc]; exact hm
        exact bn_trim_tail_wp hnmaxLt (by simp [hlenOut']; omega) hm'
          hSumFinal fun hLenLe hTakeEq =>
            hQ (outXs'.set nmax (if carry then 1 else 0)) _ (by simpa using hlenOut')
              (by rw [List.length_set, hlenOut'] at hLenLe; exact hLenLe)
              hTakeEq (sep_unpick3_4 (by simpa [sep_assoc] using hm')))
  · intro J hJ
    c0_hsplit
    · c0_hsteps
      exact hJ (na, ()) m ⟨by dsimp [nmax]; rw [Nat.max_eq_left (by c0_bv_omega), bv64_ofNat_toNat],
        rfl⟩
    · c0_hsteps
      exact hJ (nb, ()) m
        ⟨by dsimp [nmax]; rw [Nat.max_eq_right (by c0_bv_omega), bv64_ofNat_toNat], rfl⟩

theorem bn_add_one_wp :
    ∀ xs m Q X, bnAddOneSpec xs m Q X → Func.wp rtR1Env bn_add_one.body xs m Q X := by
  intro ⟨a, na, out, ⟨⟩⟩ m Q X ⟨aXs, outXs, R, hna, hnout, hna1Lt, hm, hQ⟩
  dsimp only [Func.wp, bn_add_one, bn_add_one_body]
  refine wp_pair_up_loop 0 na.toNat na.isLt (α := List (BitVec 64))
    (fun i carry outXs' mL => outXs'.length = outXs.length ∧
      limbsVal (outXs'.take i) + (if carry then 1 else 0) * 2 ^ (64 * i) =
        limbsVal (aXs.take i) + 1 ∧
      (array64 out outXs' ⋆ (array64 a aXs ⋆ R)) mL)
    (fun J hJ => by
      c0_hsteps
      exact hJ true outXs m (Nat.zero_le _)
        ⟨rfl, by rw [limbsVal_take_zero]; rfl, sep_pick2_3 hm⟩)
    ?_
  intro J i carry outXs' mL hiLe hiLt64 hiToNat ⟨hlenOut', hSumInv, hmL⟩ hRec
  c0_hsplit
  · have hlt : i < na.toNat := by c0_bv_omega
    have haLen : (BitVec.ofNat 64 i).toNat < aXs.length := by omega
    have hoLen : (BitVec.ofNat 64 i).toNat < outXs'.length := by omega
    c0_hsteps
    let va := aXs[i]'(Nat.lt_of_lt_of_le hlt hna)
    let s := va + 0 + BitVec.ofNat 64 (Bool.toNat carry)
    simp only [hiToNat] at hm ⊢
    rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
    refine hRec _ (outXs'.set i s) m hlt ⟨by simp [hlenOut'], ?_, hm⟩
    rw [limbsVal_take_set_succ outXs' s (by omega),
      limbsVal_take_succ (Nat.lt_of_lt_of_le hlt hna)]
    have hstep := addc_limbs_step hSumInv (bv64_addc_eq va 0#64 carry)
    rwa [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hstep
  · have hiEq : i = na.toNat := by c0_bv_omega
    subst hiEq
    have hoLen : (BitVec.ofNat 64 na.toNat).toNat < outXs'.length := by omega
    c0_hsteps
    all_goals (
      have hm' : (array64 out (outXs'.set na.toNat
          (if carry then (1 : BitVec 64) else 0)) ⋆ (array64 a aXs ⋆ R)) m := by
        simp only [*]; exact hm
      have hSumFinal : limbsVal ((outXs'.set na.toNat
          (if carry then 1 else (0 : BitVec 64))).take (na.toNat + 1)) =
          limbsVal (aXs.take na.toNat) + 1 := by
        rw [limbsVal_take_set_succ outXs' _ (by omega), ← hSumInv,
          show (if carry then (1 : BitVec 64) else 0).toNat =
            if carry then 1 else 0 by cases carry <;> rfl, Nat.mul_comm (2 ^ (64 * na.toNat))]
      dsimp only
      rw [show (na + 1 : BitVec 64) = BitVec.ofNat 64 (na.toNat + 1) from by
        apply BitVec.eq_of_toNat_eq; c0_bv_omega]
      exact bn_trim_tail_wp hna1Lt (by simp [hlenOut']; omega) hm' hSumFinal
        fun hLenLe hTakeEq =>
          hQ (outXs'.set na.toNat (if carry then 1 else 0)) _ (by simpa using hlenOut')
            (by rw [List.length_set, hlenOut'] at hLenLe; exact hLenLe)
            hTakeEq (sep_unpick2_3 hm'))

theorem bn_sub_wp :
    ∀ xs m Q X, bnSubSpec xs m Q X → Func.wp rtR1Env bn_sub.body xs m Q X := by
  intro ⟨a, na, b, nb, out, ⟨⟩⟩ m Q X ⟨aXs, bXs, outXs, R, hna, hnb, hnout, hba, hm, hQ⟩
  dsimp only [Func.wp, bn_sub, bn_sub_body]
  c0_hsteps
  · have hna0 : na.toNat = 0 := by c0_bv_omega
    have hdiff0 : limbsVal (aXs.take na.toNat) - limbsVal (bXs.take nb.toNat) = 0 := by
      rw [hna0, limbsVal_take_zero]; omega
    simpa [hdiff0, limbLenNat_zero, limbsVal_take_zero] using
      hQ outXs m rfl (by rw [hdiff0, limbLenNat_zero]; exact Nat.zero_le _)
        (by rw [hdiff0, limbLenNat_zero, limbsVal_take_zero]) hm
  · have hnaPos : 0 < na.toNat := by c0_bv_omega
    refine wp_pair_up_loop 0 na.toNat na.isLt (α := List (BitVec 64))
      (fun i borrow outXs' mL => outXs'.length = outXs.length ∧
        limbsVal (outXs'.take i) + limbsVal (bXs.take (min i nb.toNat)) =
          limbsVal (aXs.take i) + (if borrow then 1 else 0) * 2 ^ (64 * i) ∧
        (array64 out outXs' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mL)
      (fun J hJ => by
        c0_hsteps
        exact hJ false outXs m (Nat.zero_le _)
          ⟨rfl, by rw [limbsVal_take_zero]; rfl, sep_pick3_4 hm⟩)
      ?_
    intro J i borrow outXs' mL hiLe hiLt64 hiToNat ⟨hlenOut', hDiffInv, hmL⟩ hRec
    let vbRef := if hb : i < nb.toNat then bXs[i]'(Nat.lt_of_lt_of_le hb hnb) else 0#64
    c0_hsplit
    · have hlt : i < na.toNat := by c0_bv_omega
      have haLen : (BitVec.ofNat 64 i).toNat < aXs.length := by omega
      c0_hsteps_nogrp
      refine wp_join_tup _ _ (fun p m1 => p.1 = vbRef ∧ m1 = mL) ?_ ?_
      · rintro ⟨vb, ⟨⟩⟩ m1 ⟨hvb, hm1⟩
        dsimp only at hvb hm1; rw [hvb, hm1] at *
        have hoLen : (BitVec.ofNat 64 i).toNat < outXs'.length := by omega
        c0_hsteps
        let va0 := aXs[i]'(Nat.lt_of_lt_of_le hlt hna)
        simp only [hiToNat] at hm ⊢
        refine hRec _ (outXs'.set i (va0 - vbRef - BitVec.ofNat 64 borrow.toNat)) m hlt
          ⟨by simp [hlenOut'], ?_, hm⟩
        rw [limbsVal_take_set_succ outXs' _ (by omega),
          limbsVal_take_min_succ bXs hnb, limbsVal_take_succ (Nat.lt_of_lt_of_le hlt hna)]
        exact subb_limbs_step hDiffInv (bv64_subb_eq va0 vbRef borrow)
      · intro Jb hJb
        c0_hsplit
        · have hbLen : (BitVec.ofNat 64 i).toNat < bXs.length := by c0_bv_omega
          c0_hsteps
          exact hJb (bXs[(BitVec.ofNat 64 i).toNat]'hbLen, ()) mL
            ⟨by simp [vbRef, show i < nb.toNat by c0_bv_omega, hiToNat], rfl⟩
        · c0_hsteps
          exact hJb (0#64, ()) mL
            ⟨by simp [vbRef, show ¬ i < nb.toNat by c0_bv_omega], rfl⟩
    · have hiEq : i = na.toNat := by c0_bv_omega
      subst hiEq
      have hBMinEq : limbsVal (bXs.take (min na.toNat nb.toNat)) =
          limbsVal (bXs.take nb.toNat) := by
        by_cases hleNb : nb.toNat ≤ na.toNat
        · rw [Nat.min_eq_right hleNb]
        · rw [Nat.min_eq_left (by omega)]
          exact limbsVal_take_eq_of_lt_pow (by omega) hnb
            (Nat.lt_of_le_of_lt hba (limbsVal_take_lt_pow aXs na.toNat))
      rw [hBMinEq, show (if borrow = true then 1 else 0) * 2 ^ (64 * na.toNat) =
        if borrow = true then 2 ^ (64 * na.toNat) else 0 by cases borrow <;> simp] at hDiffInv
      have hDiffExact : limbsVal (outXs'.take na.toNat) =
          limbsVal (aXs.take na.toNat) - limbsVal (bXs.take nb.toNat) :=
        (sub_borrow_false_of_le (limbsVal_take_lt_pow outXs' na.toNat) hba hDiffInv).2
      rw [← bv64_ofNat_toNat na]
      exact bn_trim_tail_wp na.isLt (by omega) hmL hDiffExact fun hLenLe hTakeEq =>
        hQ outXs' mL hlenOut' (by rw [hlenOut'] at hLenLe; exact hLenLe)
          hTakeEq (sep_unpick3_4 (by simpa [sep_assoc] using hmL))

theorem bn_sub_one_wp :
    ∀ xs m Q X, bnSubOneSpec xs m Q X → Func.wp rtR1Env bn_sub_one.body xs m Q X := by
  intro ⟨a, na, out, ⟨⟩⟩ m Q X ⟨aXs, outXs, R, hna, hnout, hposOrZero, hm, hQ⟩
  dsimp only [Func.wp, bn_sub_one, bn_sub_one_body]
  c0_hsteps
  · have hna0 : na.toNat = 0 := by c0_bv_omega
    have hdiff0 : limbsVal (aXs.take na.toNat) - 1 = 0 := by rw [hna0, limbsVal_take_zero]
    simpa [hdiff0, limbLenNat_zero, limbsVal_take_zero] using
      hQ outXs m rfl (by rw [hdiff0, limbLenNat_zero]; exact Nat.zero_le _)
        (by rw [hdiff0, limbLenNat_zero, limbsVal_take_zero]) hm
  · have hnaPos : 0 < na.toNat := by c0_bv_omega
    have haGe1 : 1 ≤ limbsVal (aXs.take na.toNat) := by rcases hposOrZero with h0 | h1 <;> omega
    refine wp_pair_up_loop 0 na.toNat na.isLt (α := List (BitVec 64))
      (fun i borrow outXs' mL => outXs'.length = outXs.length ∧
        limbsVal (outXs'.take i) + 1 =
          limbsVal (aXs.take i) + (if borrow then 1 else 0) * 2 ^ (64 * i) ∧
        (array64 out outXs' ⋆ (array64 a aXs ⋆ R)) mL)
      (fun J hJ => by
        c0_hsteps
        exact hJ true outXs m (Nat.zero_le _)
          ⟨rfl, by rw [limbsVal_take_zero]; rfl, sep_pick2_3 hm⟩)
      ?_
    intro J i borrow outXs' mL hiLe hiLt64 hiToNat ⟨hlenOut', hDiffInv, hmL⟩ hRec
    c0_hsplit
    · have hlt : i < na.toNat := by c0_bv_omega
      have haLen : (BitVec.ofNat 64 i).toNat < aXs.length := by omega
      have hoLen : (BitVec.ofNat 64 i).toNat < outXs'.length := by omega
      c0_hsteps
      let va := aXs[i]'(Nat.lt_of_lt_of_le hlt hna)
      let d := va - 0 - BitVec.ofNat 64 (Bool.toNat borrow)
      simp only [hiToNat] at hm ⊢
      rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
      refine hRec _ (outXs'.set i d) m hlt ⟨by simp [hlenOut'], ?_, hm⟩
      rw [limbsVal_take_set_succ outXs' d (by omega),
        limbsVal_take_succ (Nat.lt_of_lt_of_le hlt hna)]
      have hstep := subb_limbs_step hDiffInv (bv64_subb_eq va 0#64 borrow)
      rwa [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hstep
    · have hiEq : i = na.toNat := by c0_bv_omega
      subst hiEq
      rw [show (if borrow = true then 1 else 0) * 2 ^ (64 * na.toNat) =
        if borrow = true then 2 ^ (64 * na.toNat) else 0 by cases borrow <;> simp] at hDiffInv
      have hDiffExact : limbsVal (outXs'.take na.toNat) = limbsVal (aXs.take na.toNat) - 1 :=
        (sub_one_borrow_false_of_pos (limbsVal_take_lt_pow outXs' na.toNat) haGe1 hDiffInv).2
      rw [← bv64_ofNat_toNat na]
      exact bn_trim_tail_wp na.isLt (by omega) hmL hDiffExact fun hLenLe hTakeEq =>
        hQ outXs' mL hlenOut' (by rw [hlenOut'] at hLenLe; exact hLenLe)
          hTakeEq (sep_unpick2_3 hmL)

theorem bn_bitwise_wp :
    ∀ xs m Q X, bnBitwiseSpec xs m Q X → Func.wp rtR1Env bn_bitwise.body xs m Q X := by
  intro ⟨op, a, na, b, nb, out, ⟨⟩⟩ m Q X ⟨aXs, bXs, outXs, R, hop, hna, hnb, hnout, hm, hQ⟩
  dsimp only [Func.wp, bn_bitwise, bn_bitwise_body]
  let nres := if op = 0#64 then min na.toNat nb.toNat else max na.toNat nb.toNat
  have hnresLeOut : nres ≤ outXs.length := hnout
  have hnresLt64 : nres < 2 ^ 64 := by dsimp [nres]; split <;> omega
  refine wp_join_tup _ _ (fun p1 m1 => p1.1 = BitVec.ofNat 64 nres ∧ m1 = m) ?_ ?_
  · intro ⟨nresBv, ⟨⟩⟩ m1 ⟨hnresEq, hm1⟩
    dsimp only at hnresEq; subst hnresEq; rw [hm1] at *
    refine wp_cursor_up_loop 0 nres hnresLt64 (α := List (BitVec 64))
      (fun i outXs' mL => outXs'.length = outXs.length ∧
        (∀ j, j < i → ∀ (hjOut : j < outXs'.length), outXs'[j]'hjOut =
          bwOp op (if ha : j < na.toNat then aXs[j]'(Nat.lt_of_lt_of_le ha hna) else 0#64)
                  (if hb : j < nb.toNat then bXs[j]'(Nat.lt_of_lt_of_le hb hnb) else 0#64)) ∧
        (array64 out outXs' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mL)
      (fun J hJ => by
        c0_hsteps
        exact hJ outXs m (Nat.zero_le _) ⟨rfl, fun _ hj _ => by omega, sep_pick3_4 hm⟩)
      ?_
    intro J i outXs' mL hiLe hiLt64 hiToNat ⟨hlenOut', hLimInv, hmL⟩ hRec
    let vaRef := if ha : i < na.toNat then aXs[i]'(Nat.lt_of_lt_of_le ha hna) else 0#64
    let vbRef := if hb : i < nb.toNat then bXs[i]'(Nat.lt_of_lt_of_le hb hnb) else 0#64
    c0_hsplit
    · have hlt : i < nres := by c0_bv_omega
      have hoLen : (BitVec.ofNat 64 i).toNat < outXs'.length := by omega
      refine wp_join_tup _ _ (fun p m1 => p.1 = vaRef ∧ m1 = mL) ?_ ?_
      · rintro ⟨va, ⟨⟩⟩ m1 ⟨hva, hm1⟩
        dsimp only at hva hm1; rw [hva, hm1] at *
        refine wp_join_tup _ _ (fun p m2 => p.1 = vbRef ∧ m2 = mL) ?_ ?_
        · rintro ⟨vb, ⟨⟩⟩ m2 ⟨hvb, hm2⟩
          dsimp only at hvb hm2; rw [hvb, hm2] at *
          c0_hsteps
          all_goals (
            rw [hiToNat] at hm
            refine hRec (outXs'.set i (bwOp op vaRef vbRef)) m hlt
              ⟨by simp [hlenOut'], fun j hj hjOut => ?_, ?_⟩
            · by_cases hjEq : j = i
              · subst hjEq; rw [List.getElem_set_self]
              · rw [List.getElem_set_ne (by omega)]
                exact hLimInv j (by omega) (by rw [List.length_set] at hjOut; exact hjOut)
            · dsimp only [bwOp]
              rw [show (0#64 : BitVec 64) = 0 from rfl, show (1#64 : BitVec 64) = 1 from rfl]
              simp only [*, ↓reduceIte]; try exact hm)
        · intro Jb hJb
          c0_hsplit
          · have hltB : (BitVec.ofNat 64 i).toNat < bXs.length := by c0_bv_omega
            c0_hsteps
            exact hJb (bXs[(BitVec.ofNat 64 i).toNat]'hltB, ()) mL
              ⟨by simp [vbRef, show i < nb.toNat by c0_bv_omega, hiToNat], rfl⟩
          · c0_hsteps
            exact hJb (0#64, ()) mL
              ⟨by simp [vbRef, show ¬ i < nb.toNat by c0_bv_omega], rfl⟩
      · intro Ja hJa
        c0_hsplit
        · have hltA : (BitVec.ofNat 64 i).toNat < aXs.length := by c0_bv_omega
          c0_hsteps
          exact hJa (aXs[(BitVec.ofNat 64 i).toNat]'hltA, ()) mL
            ⟨by simp [vaRef, show i < na.toNat by c0_bv_omega, hiToNat], rfl⟩
        · c0_hsteps
          exact hJa (0#64, ()) mL ⟨by simp [vaRef, show ¬ i < na.toNat by c0_bv_omega], rfl⟩
    · have hiEq : i = nres := by c0_bv_omega
      subst hiEq
      dsimp only
      have hOutEq : limbsVal (outXs'.take nres) =
          if op = 0#64 then (limbsVal (aXs.take na.toNat)).land (limbsVal (bXs.take nb.toNat))
          else if op = 1#64 then (limbsVal (aXs.take na.toNat)).lor (limbsVal (bXs.take nb.toNat))
          else (limbsVal (aXs.take na.toNat)).xor (limbsVal (bXs.take nb.toNat)) :=
        limbsVal_bitwise_eq op hop aXs bXs outXs' na.toNat nb.toNat nres hna hnb (by omega) rfl
          (fun j hj => hLimInv j hj (by omega))
      exact bn_trim_tail_wp hnresLt64 (by omega) hmL hOutEq fun hLenLe hTakeEq =>
        hQ outXs' mL hlenOut' (by rw [hlenOut'] at hLenLe; exact hLenLe)
          hTakeEq (sep_unpick3_4 (by simpa [sep_assoc] using hmL))
  · intro J hJ
    c0_hsplit
    · refine wp_join_tup _ _ (fun p2 m2 => p2.1 = BitVec.ofNat 64 nres ∧ m2 = m)
        (fun ⟨pv, ⟨⟩⟩ m2 ⟨hpv, hm2⟩ => by rw [wp_jump]; exact hJ (pv, ()) m2 ⟨hpv, hm2⟩) ?_
      intro Js1 hJs1; c0_hsplit
      · c0_hsteps
        exact hJs1 (na, ()) m ⟨by dsimp [nres]; simp [show op = 0#64 by assumption,
          Nat.min_eq_left (by c0_bv_omega : na.toNat ≤ nb.toNat)], rfl⟩
      · c0_hsteps
        exact hJs1 (nb, ()) m ⟨by dsimp [nres]; simp [show op = 0#64 by assumption,
          Nat.min_eq_right (by c0_bv_omega : nb.toNat ≤ na.toNat)], rfl⟩
    · refine wp_join_tup _ _ (fun p2 m2 => p2.1 = BitVec.ofNat 64 nres ∧ m2 = m)
        (fun ⟨pv, ⟨⟩⟩ m2 ⟨hpv, hm2⟩ => by rw [wp_jump]; exact hJ (pv, ()) m2 ⟨hpv, hm2⟩) ?_
      intro Js1 hJs1; c0_hsplit
      · c0_hsteps
        exact hJs1 (na, ()) m ⟨by dsimp [nres]; simp [show op ≠ 0#64 by assumption,
          Nat.max_eq_left (by c0_bv_omega : nb.toNat ≤ na.toNat)], rfl⟩
      · c0_hsteps
        exact hJs1 (nb, ()) m ⟨by dsimp [nres]; simp [show op ≠ 0#64 by assumption,
          Nat.max_eq_right (by c0_bv_omega : na.toNat ≤ nb.toNat)], rfl⟩

/-! ## 2b. Shared Part B Helpers (`array64_append`, bit-shift arithmetic) -/

theorem array64_append (a : BitVec 64) (xs ys : List (BitVec 64)) :
    array64 a (xs ++ ys) =
      (array64 a xs ⋆ array64 (a + BitVec.ofNat 64 (8 * xs.length)) ys) := by
  have h := array64_split2 a (xs ++ ys) xs.length (by simp)
  simpa using h

theorem bv64_mul8_eq (x : BitVec 64) :
    (8 : BitVec 64) * x = BitVec.ofNat 64 (8 * x.toNat) := by
  have h : BitVec.ofNat 64 8 * BitVec.ofNat 64 x.toNat = BitVec.ofNat 64 (8 * x.toNat) :=
    (BitVec.ofNat_mul 8 x.toNat).symm
  rw [bv64_ofNat_toNat x] at h
  exact h

theorem bv64_mul8_eq_r (x : BitVec 64) :
    x * (8#64 : BitVec 64) = BitVec.ofNat 64 (8 * x.toNat) := by
  rw [BitVec.mul_comm]
  exact bv64_mul8_eq x

theorem limbsVal_take_set_of_lt (xs : List (BitVec 64)) {p M : Nat} (v : BitVec 64)
    (hp : p < M) (hM : M ≤ xs.length) :
    limbsVal ((xs.set p v).take M) + 2 ^ (64 * p) * xs[p].toNat =
      limbsVal (xs.take M) + 2 ^ (64 * p) * v.toNat := by
  induction M generalizing p with
  | zero => omega
  | succ M ih =>
    by_cases hEq : p = M
    · subst hEq
      have hlen : p < xs.length := by omega
      rw [limbsVal_take_set_succ xs v hlen, limbsVal_take_succ hlen]
      ac_rfl
    · have hpM : p < M := by omega
      have hMle : M ≤ xs.length := by omega
      have hMlt : M < xs.length := by omega
      have hMltSet : M < (xs.set p v).length := by simpa using hMlt
      rw [limbsVal_take_succ hMltSet, limbsVal_take_succ hMlt,
          List.getElem_set_ne (by omega)]
      have hih := ih hpM hMle
      omega

theorem nat_testBit_mul_pow2_add (k : Nat) :
    ∀ (q v i : Nat), v < 2 ^ k →
      (2 ^ k * q + v).testBit i = if i < k then v.testBit i else q.testBit (i - k) := by
  induction k with
  | zero =>
    intro q v i hv
    have hv0 : v = 0 := by omega
    subst hv0
    simp
  | succ k ih =>
    intro q v i hv
    have hdiv : (2 ^ (k + 1) * q + v) / 2 = 2 ^ k * q + v / 2 := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
      omega
    have hmod : (2 ^ (k + 1) * q + v) % 2 = v % 2 := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
      omega
    cases i with
    | zero =>
      simp only [Nat.zero_lt_succ, ↓reduceIte, Nat.testBit_zero, hmod]
    | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, hdiv, ih q (v / 2) i (by omega)]
      by_cases hik : i < k
      · have h1 : i + 1 < k + 1 := by omega
        simp only [hik, h1, ↓reduceIte]
      · have h1 : ¬ i + 1 < k + 1 := by omega
        have hsub : i + 1 - (k + 1) = i - k := by omega
        simp only [hik, h1, ↓reduceIte, hsub]

theorem nat_testBit_false_of_lt {v i : Nat} (hv : v < 2 ^ i) : v.testBit i = false := by
  have h0 : v >>> i = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hv
  rw [← Nat.zero_add i, Nat.add_comm 0 i, ← Nat.testBit_shiftRight, h0, Nat.zero_testBit]

theorem nat_or_eq_add_of_pow_dvd {k q v : Nat} (hv : v < 2 ^ k) :
    (2 ^ k * q) ||| v = 2 ^ k * q + v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, nat_testBit_mul_pow2_add k q v i hv]
  have h1 := nat_testBit_mul_pow2_add k q 0 i (Nat.two_pow_pos k)
  rw [Nat.add_zero] at h1
  rw [h1]
  by_cases hi : i < k
  · simp [hi, Nat.zero_testBit]
  · simp only [hi, ↓reduceIte]
    have hvbit : v.testBit i = false :=
      nat_testBit_false_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hvbit]

theorem shl_step_nat (ld b carry : BitVec 64) (hbLt : b.toNat < 64)
    (hcarry : carry.toNat < 2 ^ b.toNat) :
    ((ld <<< b) ||| carry).toNat + 2 ^ 64 * (ld >>> (64#64 - b)).toNat =
        ld.toNat * 2 ^ b.toNat + carry.toNat ∧
      (ld >>> (64#64 - b)).toNat < 2 ^ b.toNat := by
  have hsubNat : (64#64 - b).toNat = 64 - b.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · change b.toNat ≤ 64; omega
  have hinvNat : (ld >>> (64#64 - b)).toNat = ld.toNat / 2 ^ (64 - b.toNat) := by
    rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, hsubNat, Nat.shiftRight_eq_div_pow]
  have hpow64 : 2 ^ 64 = 2 ^ b.toNat * 2 ^ (64 - b.toNat) := by
    rw [← Nat.pow_add, show b.toNat + (64 - b.toNat) = 64 by omega]
  have hcarryBound : (ld >>> (64#64 - b)).toNat < 2 ^ b.toNat := by
    rw [hinvNat]
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm, ← hpow64]
    exact ld.isLt
  have hshlNat : (ld <<< b).toNat = 2 ^ b.toNat * (ld.toNat % 2 ^ (64 - b.toNat)) := by
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        Nat.mul_comm ld.toNat (2 ^ b.toNat), hpow64, Nat.mul_mod_mul_left]
  have horNat : ((ld <<< b) ||| carry).toNat = (ld <<< b).toNat + carry.toNat := by
    rw [BitVec.toNat_or, hshlNat]
    exact nat_or_eq_add_of_pow_dvd hcarry
  refine ⟨?_, hcarryBound⟩
  rw [horNat, hshlNat, hinvNat]
  calc
    2 ^ b.toNat * (ld.toNat % 2 ^ (64 - b.toNat)) + carry.toNat +
        2 ^ 64 * (ld.toNat / 2 ^ (64 - b.toNat))
      = 2 ^ b.toNat * (ld.toNat % 2 ^ (64 - b.toNat) +
          2 ^ (64 - b.toNat) * (ld.toNat / 2 ^ (64 - b.toNat))) + carry.toNat := by
        rw [hpow64, Nat.mul_add]; ac_rfl
    _ = 2 ^ b.toNat * ld.toNat + carry.toNat := by
        rw [Nat.mod_add_div]
    _ = ld.toNat * 2 ^ b.toNat + carry.toNat := by
        rw [Nat.mul_comm]

end LeanQbe.T.LeanLCNF
