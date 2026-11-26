module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof1
import all Kraken.Mem
import all Kraken.Separation
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Soundness Proofs for `LcnfC0BigNum` Multi-Limb Operations (`Milestone R1`, Part 2)

Proves `Func.wp rtR1Env` contracts for the 9 multi-limb arithmetic, bitwise, shift,
and division/modulo routines of `rtR1Mod`:
- Part A: `bn_add`, `bn_add_one`, `bn_sub`, `bn_sub_one`, `bn_bitwise`
- Part B: `bn_mul`, `bn_shl`, `bn_shr`, `bn_divmod`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.LeanLCNF.BigNumRt

/-! ## 1. Separation-Logic, List/LimbsVal, and Control-Flow Helpers -/

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
    have hci : Bool.toNat cin < 2 ^ 64 := by cases cin <;> decide
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
  have h10 : (1#64 : BitVec 64) ≠ 0#64 := by decide
  have h20 : (2#64 : BitVec 64) ≠ 0#64 := by decide
  have h21 : (2#64 : BitVec 64) ≠ 1#64 := by decide
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

private theorem wp_cursor_up_loop {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
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

private theorem wp_pair_up_loop {rs : List Ty} {t0 : Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
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

private theorem wp_cursor_down_loop {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
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

private theorem wp_pair_down_loop {rs : List Ty} {t0 : Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
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

/-! ## 3. Part B Helpers & `bn_mul`, `bn_shl`, `bn_shr` -/

private theorem array64_append (a : BitVec 64) (xs ys : List (BitVec 64)) :
    array64 a (xs ++ ys) =
      (array64 a xs ⋆ array64 (a + BitVec.ofNat 64 (8 * xs.length)) ys) := by
  have h := array64_split2 a (xs ++ ys) xs.length (by simp)
  simpa using h

private theorem bv64_mul8_eq (x : BitVec 64) :
    (8 : BitVec 64) * x = BitVec.ofNat 64 (8 * x.toNat) := by
  have h : BitVec.ofNat 64 8 * BitVec.ofNat 64 x.toNat = BitVec.ofNat 64 (8 * x.toNat) :=
    (BitVec.ofNat_mul 8 x.toNat).symm
  rw [bv64_ofNat_toNat x] at h
  exact h

private theorem bv64_mul8_eq_r (x : BitVec 64) :
    x * (8#64 : BitVec 64) = BitVec.ofNat 64 (8 * x.toNat) := by
  rw [BitVec.mul_comm]
  exact bv64_mul8_eq x

private theorem limbsVal_take_set_of_lt (xs : List (BitVec 64)) {p M : Nat} (v : BitVec 64)
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

private theorem nat_testBit_mul_pow2_add (k : Nat) :
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

private theorem nat_testBit_false_of_lt {v i : Nat} (hv : v < 2 ^ i) : v.testBit i = false := by
  have h0 : v >>> i = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hv
  rw [← Nat.zero_add i, Nat.add_comm 0 i, ← Nat.testBit_shiftRight, h0, Nat.zero_testBit]

private theorem nat_or_eq_add_of_pow_dvd {k q v : Nat} (hv : v < 2 ^ k) :
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

private theorem shl_step_nat (ld b carry : BitVec 64) (hbLt : b.toNat < 64)
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
  have hbin1 : bin.toNat ≤ 1 := by cases bin <;> decide
  have hbin : (BitVec.ofNat 64 bin.toNat).toNat = bin.toNat := by cases bin <;> decide
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
      Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
    simp
  rcases Nat.lt_trichotomy i b with hib | rfl | hib
  · obtain ⟨k, hk⟩ : ∃ k, b = i + 1 + k := ⟨b - (i + 1), by omega⟩
    rw [hk, show i + 1 + k + 1 = (i + 1) + (k + 1) by omega, Nat.pow_add 2 (i + 1) (k + 1),
      Nat.pow_add 2 (i + 1) k, Nat.mul_assoc, ← Nat.mul_add, hbit0, hbit0, hbit0]; rfl
  · have ht : (2 ^ i).testBit i = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_self (Nat.pow_pos (by decide))]; decide
    rw [hbit0 i q, ht, Nat.testBit_eq_decide_div_mod_eq, Nat.pow_succ, Nat.mul_assoc,
      ← Nat.mul_add_one, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
    simp
  · rw [nat_testBit_false_of_lt (Nat.pow_lt_pow_right (by decide) hib), Bool.or_false,
      Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      show 2 ^ i = 2 ^ (b + 1) * 2 ^ (i - (b + 1)) by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)],
      ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      Nat.mul_add_div (Nat.pow_pos (by decide)),
      Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self b)),
      Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
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
        Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hkLt64)]
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
    have h2 : 2 ^ (64 * w' + k' + 1) = 2 ^ (64 * w') * 2 ^ (k' + 1) := by
      rw [← Nat.pow_add, Nat.add_assoc]
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
    rw [Nat.shiftRight_eq_div_pow, hqh, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
  have hdivPos : qVal >>> pos' = 2 * qh := by
    rw [Nat.shiftRight_eq_div_pow, hqh,
        show 2 ^ (pos' + 1) = 2 ^ pos' * 2 by rw [Nat.pow_succ],
        Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
  have hdivAdd : (qVal ||| (1 <<< pos')) >>> pos' = 2 * qh + 1 := by
    rw [hqValOr, Nat.shiftRight_eq_div_pow, hqh,
        show 2 ^ (pos' + 1) = 2 ^ pos' * 2 by rw [Nat.pow_succ],
        Nat.mul_assoc, ← Nat.mul_add_one,
        Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
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
    refine ⟨⟨fun h => absurd h (by decide), fun h => by omega⟩,
            ⟨fun h => absurd h (by decide), fun h => by omega⟩⟩
  · by_cases hgt : x > y
    · simp only [hlt, ↓reduceIte, hgt]
      refine ⟨⟨fun _ => by omega, fun _ => by decide⟩,
              ⟨fun _ => by omega, fun _ => by decide⟩⟩
    · simp only [hlt, ↓reduceIte, hgt]
      refine ⟨⟨fun _ => by omega, fun _ => by decide⟩,
              ⟨fun _ => by omega, fun _ => by decide⟩⟩

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
  have hbPos : 0 < bVal := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide))
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
        refine hJw (qInit, rInit) r0 ⟨hqInitLen, hrInitLen, hqInitZero,
          by rw [hrInitZero]; exact hbPos, ?_, hmR0'⟩
        have hqInitVal : limbsVal (qInit.take na.toNat) = 0 := by
          dsimp [qInit]; rw [List.take_append_of_le_length (by simp), List.take_replicate,
            Nat.min_self, limbsVal_replicate_zero]
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
      refine wp_pair_down_loop 64 (by decide) (t0 := i64) (α := List (BitVec 64))
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
            dsimp [aVal, pos', aw]
            have hdiv : (64 * w' + k') / 64 = w' := by omega
            have hmod : (64 * w' + k') % 64 = k' := by omega
            simp only [limbsVal_testBit, List.length_take_of_le hna, hdiv, hmod,
              show w' < na.toNat by omega, ↓reduceDIte, List.getElem_take]
          dsimp [inBitBv, inBit]
          rw [hawTest, Nat.and_one_is_mod, BitVec.toNat_ushiftRight,
            Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
          rcases Nat.mod_two_eq_zero_or_one (aw.toNat / 2 ^ k') with hmod | hmod <;> simp [hmod]
        have hinBitLt2 : inBitBv.toNat < 2 := by rw [hinBitEq]; dsimp [inBit]; split <;> decide
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
            dsimp only [lift2, Arg.val]
            simp only [hw1ToNat, hkMod64]
            exact hJs inBitBv rXs'' mK (Nat.zero_le _)
              ⟨hrLen', hinBitLt2, fun _ _ _ _ _ => rfl, by simp, hmK⟩)
          ?_
        intro Js jNat cbit rCur mS hjLe hjLt64 hjToNat ⟨hrLenS, hcLt, hrRem, hShInv, hmS⟩ hRecS
        c0_hsplit
        · have hjLtNb : jNat < nb.toNat := by c0_bv_omega
          let rj := rXs''[jNat]'(by omega)
          have hrjEq : rCur[jNat]'(by omega) = rj :=
            hrRem jNat (le_refl _) hjLtNb (by omega) (by omega)
          let rjNext := (rj <<< 1) ||| cbit; let cNext := rj >>> 63
          have hstep := shl_step_nat rj 1#64 cbit (by decide) (by simpa using hcLt)
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
          let rShVal := limbsVal (rCur.take nb.toNat)
          let rValOld := limbsVal (rXs''.take nb.toNat); let rPrime := 2 * rValOld + inBit
          have hrShEq : rShVal + 2 ^ (64 * nb.toNat) * cbit.toNat = rPrime := by
            dsimp [rShVal, rValOld, rPrime]; rwa [← hinBitEq]
          have hrShLtPow : rShVal < 2 ^ (64 * nb.toNat) := by
            have h := limbsVal_lt_pow (rCur.take nb.toNat)
            rwa [List.length_take_of_le (by omega)] at h
          refine LeanQbe.T.wp_join_group
            (fun (ge, ()) mG => ge = decide (bVal ≤ rPrime) ∧
              (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rCur ⋆ R) mG)
            ?_ ?_
          · intro Jge ⟨geB, ⟨⟩⟩ mG ⟨hgeEq, hmG⟩
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
              ?_ ?_
            · intro JkN ⟨qwNBv, ⟨⟩⟩ mN ⟨qwN, rXsN, hrLenN, hqwN, hqwNDvd, hrNLt, hInvN, hmN⟩
              dsimp only at hqwN; subst qwNBv
              c0_hsteps
              exact hRecK k' qwN rXsN mN (by omega) ⟨hrLenN, hqwNDvd, hrNLt, hInvN, hmN⟩
            · intro JkN hJkN
              have hqProps := divmod_q_set_props hkPos hkLe hqDvd hqwDvd; dsimp only at hqProps
              rcases hqProps with ⟨hqwNextDvd, hqNextOr, hqNextShr, hqShr⟩
              have hdm := divmod_bit_step hrLtK hinvPos; dsimp only at hdm
              c0_hsplit
              · have hgeTrue : bVal ≤ rPrime := by
                  first | exact of_decide_eq_true (by assumption) | assumption
                c0_hsteps_nogrp
                refine wp_pair_up_loop 0 nb.toNat nb.isLt (t0 := Ty.bool) (α := List (BitVec 64))
                  (fun jjNat br rSub mSub =>
                    rSub.length = rXs.length ∧
                    limbsVal (rSub.take jjNat) + limbsVal (bXs.take jjNat) =
                      limbsVal (rCur.take jjNat) + (if br then 1 else 0) * 2 ^ (64 * jjNat) ∧
                    (∀ i (_hi1 : jjNat ≤ i) (_hi2 : i < nb.toNat)
                      (hir : i < rSub.length) (hic : i < rCur.length),
                      rSub[i]'hir = rCur[i]'hic) ∧
                    (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rSub ⋆ R) mSub)
                  (fun Jsub hJsub => by
                    c0_hsteps
                    exact hJsub false rCur mG (Nat.zero_le _)
                      ⟨hrLenS, by simp, fun _ _ _ _ _ => rfl, hmG⟩)
                  ?_
                intro Jsub jjNat br rSub mSub hjjLe hjjLt64 hjjToNat
                  ⟨hrLenSub, hSubInv, hrSubRem, hmSub⟩ hRecSub
                c0_hsplit
                · have hjjLtNb : jjNat < nb.toNat := by
                    first
                      | (have hc : (BitVec.ofNat 64 jjNat).toNat < nb.toNat := by assumption
                         rwa [hjjToNat] at hc)
                      | (have hc : jjNat % 2 ^ 64 < nb.toNat := by assumption
                         rwa [Nat.mod_eq_of_lt hjjLt64] at hc)
                  let rCurJ := rCur[jjNat]'(by omega); let bj := bXs[jjNat]'(by omega)
                  have hrSubJ : rSub[jjNat]'(by omega) = rCurJ :=
                    hrSubRem jjNat (le_refl _) hjjLtNb (by omega) (by omega)
                  have hrl : (BitVec.ofNat 64 jjNat).toNat < rSub.length := by
                    rw [hjjToNat]; omega
                  have hbl : (BitVec.ofNat 64 jjNat).toNat < bXs.length := by
                    rw [hjjToNat]; omega
                  c0_hsteps
                  simp only [hjjToNat, hrSubJ] at hm ⊢
                  refine hRecSub _ (rSub.set jjNat (rCurJ - bj - BitVec.ofNat 64 br.toNat)) m
                    hjjLtNb ⟨by simp [hrLenSub], ?_, fun i hi1 hi2 hir hic => by
                      rw [List.getElem_set_ne (by omega)]; exact hrSubRem i (by omega) hi2 _ _,
                      sep_ac hm⟩
                  rw [limbsVal_take_set_succ rSub _ (by omega),
                    limbsVal_take_succ (Nat.lt_of_lt_of_le hjjLtNb hnb),
                    limbsVal_take_succ (by omega)]
                  exact subb_limbs_step hSubInv
                    (bv64_subb_step_eq rCurJ bj br _ decide_eq_true_iff)
                · have hjjEqNb : jjNat = nb.toNat := by
                    have hnot : ¬ jjNat < nb.toNat := by
                      first
                        | (have hc : ¬ (BitVec.ofNat 64 jjNat).toNat < nb.toNat := by assumption
                           rwa [hjjToNat] at hc)
                        | (have hc : ¬ jjNat % 2 ^ 64 < nb.toNat := by assumption
                           rwa [Nat.mod_eq_of_lt hjjLt64] at hc)
                    omega
                  subst hjjEqNb
                  have hrSubLtPow : limbsVal (rSub.take nb.toNat) < 2 ^ (64 * nb.toNat) := by
                    have h := limbsVal_lt_pow (rSub.take nb.toNat)
                    rwa [List.length_take_of_le (by omega)] at h
                  have hsubClean : limbsVal (rSub.take nb.toNat) + bVal =
                      rShVal + (if br then 2 ^ (64 * nb.toNat) else 0) := by
                    dsimp [bVal, rShVal]; rw [hSubInv]; cases br <;> simp
                  have hrSubEq : limbsVal (rSub.take nb.toNat) = rPrime - bVal :=
                    divmod_post_sub_eq hrLtK hbLtPow (by dsimp [inBit]; split <;> decide)
                      hrShLtPow (by omega) hrShEq hgeTrue hrSubLtPow hsubClean
                  have hrSubLtB : limbsVal (rSub.take nb.toNat) < bVal := by
                    rw [hrSubEq]; dsimp [rPrime]
                    have : inBit ≤ 1 := by dsimp [inBit]; split <;> decide
                    omega
                  have hdecT : decide (bVal ≤ 2 * rValOld + inBit) = true :=
                    decide_eq_true hgeTrue
                  dsimp only [rValOld, inBit] at hdecT
                  simp only [hdecT, ↓reduceIte] at hdm
                  have hqwNextEq : (qw0 ||| (1 : BitVec 64) <<<
                      ((BitVec.ofNat 64 kNat - 1).toNat % 64)) = qw0 ||| (1#64 <<< k') := by
                    rw [hkMod64]; rfl
                  c0_hsteps; dsimp only [lift2, Arg.val]; rw [hqwNextEq]
                  refine hJkN (qw0 ||| (1#64 <<< k'), ()) mSub
                    ⟨qw0 ||| (1#64 <<< k'), rSub, hrLenSub, rfl, hqwNextDvd, hrSubLtB, ?_, hmSub⟩
                  rw [hqNextOr, hrSubEq]; exact (hdm hqNextShr).1
              · have hgeFalse : ¬ (bVal ≤ rPrime) := by
                  first
                    | exact of_decide_eq_false (by assumption)
                    | (have hc : ¬ decide (bVal ≤ rPrime) = true := by assumption
                       exact fun h => hc (decide_eq_true h))
                    | assumption
                have hdecF : decide (bVal ≤ 2 * rValOld + inBit) = false :=
                  decide_eq_false hgeFalse
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
                refine hJkN (qw0, ()) mG ⟨qw0, rCur, hrLenS, rfl,
                  Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hqwDvd,
                  by rw [hrShEq']; dsimp [rPrime]; omega, ?_, hmG⟩
                rw [hrShEq']; exact (hdm hqShr).1
          · intro Jge hJge
            c0_hsplit
            · have hcbit1 : cbit.toNat = 1 := by
                by_cases hz : cbit.toNat = 0
                · have hc0 : cbit = 0#64 := BitVec.eq_of_toNat_eq hz
                  first
                    | exact False.elim ((by assumption : cbit ≠ 0#64) hc0)
                    | (have h : (cbit != 0#64) = true := by assumption
                       rw [hc0] at h; exact absurd h (by decide))
                · omega
              have hgeTrue : bVal ≤ rPrime := by rw [← hrShEq, hcbit1, Nat.mul_one]; omega
              c0_hsteps; try rw [wp_jump]
              exact hJge (true, ()) mS ⟨(decide_eq_true hgeTrue).symm, hmS⟩
            · have hcbit0 : cbit.toNat = 0 := by
                first
                  | (have hc : cbit = 0 := by assumption
                     simpa using congrArg BitVec.toNat hc)
                  | (have hc : cbit = 0#64 := by assumption
                     simpa using congrArg BitVec.toNat hc)
                  | (have h : ¬ cbit ≠ 0#64 := by assumption
                     simpa using congrArg BitVec.toNat (Classical.not_not.mp h))
                  | (have h : (cbit != 0#64) = false := by assumption
                     simpa using congrArg BitVec.toNat (bne_eq_false_iff_eq.mp h))
              rw [hcbit0, Nat.mul_zero, Nat.add_zero] at hrShEq
              have hrShEq' : rShVal = rPrime := hrShEq
              have hmCmp : (array64 r rCur ⋆ array64 b bXs ⋆
                  (array64 a aXs ⋆ array64 q qXs' ⋆ R)) mS := sep_ac hmS
              refine bn_cmp_fixed_call_wp (by omega) hnb hmCmp ?_
              c0_hsplit
              · have hc : (0#64).sle (cmpResult64 (limbsVal (rCur.take nb.toNat))
                    (limbsVal (bXs.take nb.toNat))) = true := by assumption
                rw [(cmpResult64_sge0_iff _ _).1] at hc
                have hcmpTrue : bVal ≤ rPrime := by change bVal ≤ rShVal at hc; rwa [hrShEq'] at hc
                c0_hsteps; try rw [wp_jump]
                exact hJge (true, ()) mS ⟨(decide_eq_true hcmpTrue).symm, hmS⟩
              · have hcmpFalse : ¬ (bVal ≤ rPrime) := by
                  rw [← hrShEq', ← (cmpResult64_sge0_iff rShVal bVal).1]
                  first
                    | (intro ht; contradiction)
                    | (intro ht
                       have hf : (0#64).sle (cmpResult64 (limbsVal (rCur.take nb.toNat))
                         (limbsVal (bXs.take nb.toNat))) = false := by assumption
                       rw [ht] at hf; exact absurd hf (by decide))
                c0_hsteps; try rw [wp_jump]
                exact hJge (false, ()) mS ⟨(decide_eq_false hcmpFalse).symm, hmS⟩
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
      exact hQ qXs' rXs' mW hqLen hrLen hqDiv hrMod hmW
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
