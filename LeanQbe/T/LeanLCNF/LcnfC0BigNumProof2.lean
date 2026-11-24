module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0BigNum` Multi-Limb Operations (`Milestone R1`, Part 2)

Proves `Func.wp rtR1Env` contracts for the 9 multi-limb arithmetic, bitwise, shift,
and division/modulo routines of `rtR1Mod`:
- Part A: `bn_add`, `bn_add_one`, `bn_sub`, `bn_sub_one`, `bn_bitwise`
- Part B: `bn_mul`, `bn_shl`, `bn_shr`, `bn_divmod`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
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
  have hzeroTest : ∀ r, (0#64 : BitVec 64).toNat.testBit r = false := fun r => Nat.zero_testBit r
  rcases hop with rfl | rfl | rfl
  · simp only [↓reduceIte] at hnres ⊢
    apply Nat.eq_of_testBit_eq
    intro k
    change (limbsVal (outXs.take nres)).testBit k =
      ((limbsVal (aXs.take na)) &&& (limbsVal (bXs.take nb))).testBit k
    rw [Nat.testBit_and, limbsVal_take_testBit _ hnout,
      limbsVal_take_testBit _ hna, limbsVal_take_testBit _ hnb]
    by_cases hj : k / 64 < nres
    · have hja : k / 64 < na := by omega
      have hjb : k / 64 < nb := by omega
      simp only [hj, hja, hjb, ↓reduceDIte, hlim (k / 64) hj, bwOp, ↓reduceIte,
        BitVec.toNat_and, Nat.testBit_and]
    · simp only [hj, ↓reduceDIte]
      by_cases hja : k / 64 < na
      · have hjb : ¬ k / 64 < nb := by omega
        simp only [hja, hjb, ↓reduceDIte, Bool.and_false]
      · simp only [hja, ↓reduceDIte, Bool.false_and]
  · have hne0 : (1#64 : BitVec 64) ≠ 0#64 := by decide
    simp only [hne0, ↓reduceIte] at hnres ⊢
    apply Nat.eq_of_testBit_eq
    intro k
    change (limbsVal (outXs.take nres)).testBit k =
      ((limbsVal (aXs.take na)) ||| (limbsVal (bXs.take nb))).testBit k
    rw [Nat.testBit_or, limbsVal_take_testBit _ hnout,
      limbsVal_take_testBit _ hna, limbsVal_take_testBit _ hnb]
    by_cases hj : k / 64 < nres
    · simp only [hj, ↓reduceDIte, hlim (k / 64) hj, bwOp, hne0, ↓reduceIte,
        BitVec.toNat_or, Nat.testBit_or]
      by_cases hja : k / 64 < na <;> by_cases hjb : k / 64 < nb
      · simp only [hja, hjb, ↓reduceDIte]
      · simp only [hja, hjb, ↓reduceDIte, hzeroTest, Bool.or_false]
      · simp only [hja, hjb, ↓reduceDIte, hzeroTest, Bool.false_or]
      · simp only [hja, hjb, ↓reduceDIte, hzeroTest, Bool.false_or]
    · simp only [hj, ↓reduceDIte]
      have hja : ¬ k / 64 < na := by omega
      have hjb : ¬ k / 64 < nb := by omega
      simp only [hja, hjb, ↓reduceDIte, Bool.false_or]
  · have hne0 : (2#64 : BitVec 64) ≠ 0#64 := by decide
    have hne1 : (2#64 : BitVec 64) ≠ 1#64 := by decide
    simp only [hne0, hne1, ↓reduceIte] at hnres ⊢
    apply Nat.eq_of_testBit_eq
    intro k
    change (limbsVal (outXs.take nres)).testBit k =
      ((limbsVal (aXs.take na)) ^^^ (limbsVal (bXs.take nb))).testBit k
    rw [Nat.testBit_xor, limbsVal_take_testBit _ hnout,
      limbsVal_take_testBit _ hna, limbsVal_take_testBit _ hnb]
    by_cases hj : k / 64 < nres
    · simp only [hj, ↓reduceDIte, hlim (k / 64) hj, bwOp, hne0, hne1, ↓reduceIte,
        BitVec.toNat_xor, Nat.testBit_xor]
      by_cases hja : k / 64 < na <;> by_cases hjb : k / 64 < nb
      · simp only [hja, hjb, ↓reduceDIte]
      · simp only [hja, hjb, ↓reduceDIte, hzeroTest, Bool.xor_false]
      · simp only [hja, hjb, ↓reduceDIte, hzeroTest, Bool.false_xor]
      · simp only [hja, hjb, ↓reduceDIte, hzeroTest, Bool.false_xor]
    · simp only [hj, ↓reduceDIte]
      have hja : ¬ k / 64 < na := by omega
      have hjb : ¬ k / 64 < nb := by omega
      simp only [hja, hjb, ↓reduceDIte, Bool.false_xor]

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

/-! ## 2. Proofs of Multi-Limb Operations (`Part A`: `bn_add` .. `bn_bitwise`) -/

theorem bn_add_wp :
    ∀ xs m Q X, bnAddSpec xs m Q X → Func.wp rtR1Env bn_add.body xs m Q X := by
  intro ⟨a, na, b, nb, out, ⟨⟩⟩ m Q X ⟨aXs, bXs, outXs, R, hna, hnb, hnout, hnmaxLt, hm, hQ⟩
  dsimp only [Func.wp, bn_add, bn_add_body]
  change LeanQbe.T.wp _ _ _ _ _
  let nmax := max na.toNat nb.toNat
  have hnmaxLt64 : nmax < 2 ^ 64 := by omega
  have hnb1Lt64 : nmax + 1 < 2 ^ 64 := hnmaxLt
  refine wp_join_tup _ _ (fun (p1 : Tup Val [i64]) m1 => p1.1 = BitVec.ofNat 64 nmax ∧ m1 = m) ?_ ?_
  · intro ⟨nmaxBv, ⟨⟩⟩ m1 ⟨hnmaxEq, hm1⟩
    dsimp only at hnmaxEq; subst hnmaxEq; rw [hm1] at *
    refine wp_loop_inv
      (fun (xs : Tup Val [Ty.bool, i64]) mL =>
        ∃ (carry : Bool) (iNat : Nat) (outXs' : List (BitVec 64)),
          iNat ≤ nmax ∧
          xs.1 = carry ∧
          xs.2.1 = BitVec.ofNat 64 iNat ∧
          outXs'.length = outXs.length ∧
          limbsVal (outXs'.take iNat) + (if carry then 1 else 0) * 2 ^ (64 * iNat) =
            limbsVal (aXs.take (min iNat na.toNat)) + limbsVal (bXs.take (min iNat nb.toNat)) ∧
          (array64 out outXs' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mL)
      (fun (xs : Tup Val [Ty.bool, i64]) _ => nmax - xs.2.1.toNat) ?_ ?_
    · intro Js hJs
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      exact hJs (false, 0#64, ()) m ⟨false, 0, outXs, Nat.zero_le _, rfl, rfl, rfl,
        by rw [limbsVal_take_zero]; rfl, sep_pick3_4 hm⟩
    · intro Js ⟨carryBv, iBv, ⟨⟩⟩ mL ⟨carry, iNat, outXs', hiLe, hcEq, hiEq, hlenOut', hSumInv,
      hmL⟩ hRec
      dsimp only at hcEq hiEq; subst hcEq; subst hiEq
      have hilt64 : iNat < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe hnmaxLt64
      have hiToNat : (BitVec.ofNat 64 iNat).toNat = iNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]
      let vaRef : BitVec 64 :=
        if ha : iNat < na.toNat then aXs[iNat]'(Nat.lt_of_lt_of_le ha hna) else 0#64
      let vbRef : BitVec 64 :=
        if hb : iNat < nb.toNat then bXs[iNat]'(Nat.lt_of_lt_of_le hb hnb) else 0#64
      have addStep {va vb : BitVec 64} {m' : Mem 64}
          (hm' : (array64 out (outXs'.set (BitVec.ofNat 64 iNat).toNat (va + vb +
            BitVec.ofNat 64 (Bool.toNat carryBv))) ⋆
              (array64 a aXs ⋆ array64 b bXs ⋆ R)) m')
          (hlt : iNat < nmax) (hva : va = vaRef) (hvb : vb = vbRef) :
          Js (decide (2 ^ 64 ≤ va.toNat + vb.toNat + Bool.toNat carryBv), BitVec.ofNat 64 iNat + 1,
            ()) m' := by
        subst hva; subst hvb
        let co := decide (2 ^ 64 ≤ vaRef.toNat + vbRef.toNat + Bool.toNat carryBv)
        let s := vaRef + vbRef + BitVec.ofNat 64 (Bool.toNat carryBv)
        rw [hiToNat] at hm'
        rw [show (BitVec.ofNat 64 iNat + 1 : BitVec 64) = BitVec.ofNat 64 (iNat + 1) from
          (BitVec.ofNat_add iNat 1).symm]
        apply hRec (co, BitVec.ofNat 64 (iNat + 1), ()) m'
        · show nmax - (BitVec.ofNat 64 (iNat + 1)).toNat < nmax - (BitVec.ofNat 64 iNat).toNat
          have h1lt : iNat + 1 < 2 ^ 64 := by omega
          rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
          omega
        · refine ⟨co, iNat + 1, outXs'.set iNat s, hlt, rfl, rfl, by simp [hlenOut'], ?_, hm'⟩
          rw [limbsVal_take_set_succ outXs' s (by omega),
              limbsVal_take_min_succ aXs hna, limbsVal_take_min_succ bXs hnb]
          have haddc := bv64_addc_eq vaRef vbRef carryBv
          dsimp only [vaRef, vbRef] at haddc
          exact addc_limbs_step hSumInv haddc
      have addExit {topLimb : BitVec 64} {m' : Mem 64}
          (hm' : (array64 out (outXs'.set (BitVec.ofNat 64 nmax).toNat topLimb) ⋆
              (array64 a aXs ⋆ array64 b bXs ⋆ R)) m')
          (hnlt : ¬ iNat < nmax) (htop : topLimb = if carryBv then 1#64 else 0#64) :
          wp rtR1Env Q X
            (Expr.call (V := Val) (L := Cont) (rs := [i64]) (as := [i64,
              i64]) (bs := [i64]) "bn_trim"
              (Arg.var out, Arg.var (BitVec.ofNat 64 nmax + 1), ())
              fun (p : Tup Val [i64]) => Expr.ret (Arg.var p.fst, ())) m' := by
        have hiEqNmax : iNat = nmax := by omega
        subst hiEqNmax; subst htop
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnmaxLt64] at hm'
        rw [show (BitVec.ofNat 64 nmax + 1 : BitVec 64) = BitVec.ofNat 64 (nmax + 1) from
          (BitVec.ofNat_add nmax 1).symm]
        have hminA : min nmax na.toNat = na.toNat := Nat.min_eq_right (Nat.le_max_left _ _)
        have hminB : min nmax nb.toNat = nb.toNat := Nat.min_eq_right (Nat.le_max_right _ _)
        have hSumFinal :
            limbsVal ((outXs'.set nmax (if carryBv then 1#64 else 0#64)).take (nmax + 1)) =
              limbsVal (aXs.take na.toNat) + limbsVal (bXs.take nb.toNat) := by
          rw [hminA, hminB] at hSumInv
          rw [limbsVal_take_set_succ outXs' _ (by omega), ← hSumInv]
          have htopNat : (if carryBv then (1#64 : BitVec 64) else 0#64).toNat =
            if carryBv then 1 else 0 := by
            cases carryBv <;> rfl
          rw [htopNat, Nat.mul_comm (2 ^ (64 * nmax))]
        exact bn_trim_tail_wp hnb1Lt64 (by simp [hlenOut']; omega) hm' hSumFinal
          (fun hLenLe hTakeEq =>
            hQ (outXs'.set nmax (if carryBv then 1#64 else 0#64)) m' (by simpa using hlenOut')
              (by rw [List.length_set, hlenOut'] at hLenLe; exact hLenLe)
              hTakeEq (sep_unpick3_4 (by simpa [sep_assoc] using hm')))
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      all_goals first
        | exact addExit hm (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnmaxLt64] at *; omega)
            (by simp [*])
        | exact addStep hm (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnmaxLt64] at *; omega)
            (by dsimp [vaRef]
                by_cases ha : iNat < na.toNat
                · first | exact absurd ha (by omega) | simp only [ha, ↓reduceDIte, hiToNat]
                · first
                  | exact absurd (by omega : iNat < na.toNat) ha
                  | simp only [ha, ↓reduceDIte])
            (by dsimp [vbRef]
                by_cases hb : iNat < nb.toNat
                · first | exact absurd hb (by omega) | simp only [hb, ↓reduceDIte, hiToNat]
                · first
                  | exact absurd (by omega : iNat < nb.toNat) hb
                  | simp only [hb, ↓reduceDIte])
  · intro Js hJs
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · have hgt : nb.toNat < na.toNat := by assumption
      exact hJs (na,
        ()) m ⟨by dsimp [nmax]; rw [Nat.max_eq_left (Nat.le_of_lt hgt), bv64_ofNat_toNat], rfl⟩
    · have hle : ¬ nb.toNat < na.toNat := by assumption
      exact hJs (nb, ()) m ⟨by dsimp [nmax]; rw [Nat.max_eq_right (by omega), bv64_ofNat_toNat],
        rfl⟩

theorem bn_add_one_wp :
    ∀ xs m Q X, bnAddOneSpec xs m Q X → Func.wp rtR1Env bn_add_one.body xs m Q X := by
  intro ⟨a, na, out, ⟨⟩⟩ m Q X ⟨aXs, outXs, R, hna, hnout, hna1Lt, hm, hQ⟩
  dsimp only [Func.wp, bn_add_one, bn_add_one_body]
  change LeanQbe.T.wp _ _ _ _ _
  refine wp_loop_inv
    (fun (xs : Tup Val [Ty.bool, i64]) mL =>
      ∃ (carry : Bool) (iNat : Nat) (outXs' : List (BitVec 64)),
        iNat ≤ na.toNat ∧
        xs.1 = carry ∧
        xs.2.1 = BitVec.ofNat 64 iNat ∧
        outXs'.length = outXs.length ∧
        limbsVal (outXs'.take iNat) + (if carry then 1 else 0) * 2 ^ (64 * iNat) =
          limbsVal (aXs.take iNat) + 1 ∧
        (array64 out outXs' ⋆ (array64 a aXs ⋆ R)) mL)
    (fun (xs : Tup Val [Ty.bool, i64]) _ => na.toNat - xs.2.1.toNat) ?_ ?_
  · intro Js hJs
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    exact hJs (true, 0#64, ()) m ⟨true, 0, outXs, Nat.zero_le _, rfl, rfl, rfl,
      by rw [limbsVal_take_zero]; rfl, sep_pick2_3 hm⟩
  · intro Js ⟨carryBv, iBv, ⟨⟩⟩ mL ⟨carry, iNat, outXs', hiLe, hcEq, hiEq, hlenOut', hSumInv,
    hmL⟩ hRec
    dsimp only at hcEq hiEq; subst hcEq; subst hiEq
    have hilt64 : iNat < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe na.isLt
    have hiToNat : (BitVec.ofNat 64 iNat).toNat = iNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]
    have addOneExit (hnlt : ¬ iNat < na.toNat) {topLimb : BitVec 64} {m' : Mem 64}
        (htop : topLimb = if carryBv then 1#64 else 0#64)
        (hm' : (array64 out (outXs'.set na.toNat topLimb) ⋆ (array64 a aXs ⋆ R)) m') :
        wp rtR1Env Q X
          (Expr.call (V := Val) (L := Cont) (rs := [i64]) (as := [i64, i64]) (bs := [i64]) "bn_trim"
            (Arg.var out, Arg.var (na + 1), ())
            fun (p : Tup Val [i64]) => Expr.ret (Arg.var p.fst, ())) m' := by
      have hiEqNa : iNat = na.toNat := by omega
      subst hiEqNa; subst htop
      rw [show (na + 1 : BitVec 64) = BitVec.ofNat 64 (na.toNat + 1) by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, Nat.mod_eq_of_lt hna1Lt]]
      have hSumFinal :
          limbsVal ((outXs'.set na.toNat (if carryBv then 1#64 else 0#64)).take (na.toNat + 1)) =
            limbsVal (aXs.take na.toNat) + 1 := by
        rw [limbsVal_take_set_succ outXs' _ (by omega), ← hSumInv]
        have htopNat : (if carryBv then (1#64 : BitVec 64) else 0#64).toNat =
          if carryBv then 1 else 0 := by
          cases carryBv <;> rfl
        rw [htopNat, Nat.mul_comm (2 ^ (64 * na.toNat))]
      exact bn_trim_tail_wp hna1Lt (by simp [hlenOut']; omega) hm' hSumFinal
        (fun hLenLe hTakeEq =>
          hQ (outXs'.set na.toNat (if carryBv then 1#64 else 0#64)) m'
            (by simpa using hlenOut') (by rw [List.length_set, hlenOut'] at hLenLe; exact hLenLe)
            hTakeEq (sep_unpick2_3 hm'))
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · have hlt : iNat < na.toNat := by
        have hc : iNat % 2 ^ 64 < na.toNat := by assumption
        omega
      let va := aXs[iNat]'(Nat.lt_of_lt_of_le hlt hna)
      let co := decide (2 ^ 64 ≤ va.toNat + 0 + Bool.toNat carryBv)
      let s := va + 0 + BitVec.ofNat 64 (Bool.toNat carryBv)
      have hm' : (array64 out (outXs'.set iNat s) ⋆ (array64 a aXs ⋆ R)) m := by
        simpa [hiToNat, s, va] using hm
      have hinc : BitVec.ofNat 64 iNat + 1 = BitVec.ofNat 64 (iNat + 1) :=
        (BitVec.ofNat_add iNat 1).symm
      rw [hinc]
      have hgoal : Js (co, BitVec.ofNat 64 (iNat + 1), ()) m := by
        apply hRec (co, BitVec.ofNat 64 (iNat + 1), ()) m
        · show na.toNat - (BitVec.ofNat 64 (iNat + 1)).toNat <
          na.toNat - (BitVec.ofNat 64 iNat).toNat
          have h1lt : iNat + 1 < 2 ^ 64 := by omega
          rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
          omega
        · refine ⟨co, iNat + 1, outXs'.set iNat s, hlt, rfl, rfl, by simp [hlenOut'], ?_, hm'⟩
          rw [limbsVal_take_set_succ outXs' s
            (by omega), limbsVal_take_succ (Nat.lt_of_lt_of_le hlt hna)]
          have haddc := bv64_addc_eq va 0#64 carryBv
          have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
          have hstep := addc_limbs_step hSumInv haddc
          rwa [h0, Nat.mul_zero, Nat.add_zero] at hstep
      simpa [hiToNat, va, co] using hgoal
    · exact addOneExit (by omega) (by simp [*]) hm
    · exact addOneExit (by omega) (by simp [*]) hm

theorem bn_sub_wp :
    ∀ xs m Q X, bnSubSpec xs m Q X → Func.wp rtR1Env bn_sub.body xs m Q X := by
  intro ⟨a, na, b, nb, out, ⟨⟩⟩ m Q X ⟨aXs, bXs, outXs, R, hna, hnb, hnout, hba, hm, hQ⟩
  dsimp only [Func.wp, bn_sub, bn_sub_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have hna0 : na.toNat = 0 := by
      have hc : na = 0#64 := by assumption
      subst hc; rfl
    have hdiff0 : limbsVal (aXs.take na.toNat) - limbsVal (bXs.take nb.toNat) = 0 := by
      rw [hna0, limbsVal_take_zero]; omega
    have hQ0 := hQ outXs m rfl (by rw [hdiff0, limbLenNat_zero]; exact Nat.zero_le _)
      (by rw [hdiff0, limbLenNat_zero, limbsVal_take_zero]) hm
    rwa [hdiff0, limbLenNat_zero] at hQ0
  · have hnaPos : 0 < na.toNat := by
      have hc : na ≠ 0#64 := by assumption
      by_cases hz : na.toNat = 0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using hz)) hc
      · omega
    refine wp_loop_inv
      (fun (xs : Tup Val [Ty.bool, i64]) mL =>
        ∃ (borrow : Bool) (iNat : Nat) (outXs' : List (BitVec 64)),
          iNat ≤ na.toNat ∧
          xs.1 = borrow ∧
          xs.2.1 = BitVec.ofNat 64 iNat ∧
          outXs'.length = outXs.length ∧
          limbsVal (outXs'.take iNat) + limbsVal (bXs.take (min iNat nb.toNat)) =
            limbsVal (aXs.take iNat) + (if borrow then 1 else 0) * 2 ^ (64 * iNat) ∧
          (array64 out outXs' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mL)
      (fun (xs : Tup Val [Ty.bool, i64]) _ => na.toNat - xs.2.1.toNat) ?_ ?_
    · intro Js hJs
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      exact hJs (false, 0#64, ()) m ⟨false, 0, outXs, Nat.zero_le _, rfl, rfl, rfl,
        by rw [limbsVal_take_zero]; rfl, sep_pick3_4 hm⟩
    · intro Js ⟨borrowBv, iBv, ⟨⟩⟩ mL ⟨borrow, iNat, outXs', hiLe, hbEq, hiEq, hlenOut', hDiffInv,
      hmL⟩ hRec
      dsimp only at hbEq hiEq; subst hbEq; subst hiEq
      have hilt64 : iNat < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe na.isLt
      have hiToNat : (BitVec.ofNat 64 iNat).toNat = iNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]
      let vbRef : BitVec 64 :=
        if hb : iNat < nb.toNat then bXs[iNat]'(Nat.lt_of_lt_of_le hb hnb) else 0#64
      have subStep {va vb : BitVec 64} {m' : Mem 64}
          (hm' : (array64 out (outXs'.set (BitVec.ofNat 64 iNat).toNat
              (va - vb - BitVec.ofNat 64 (Bool.toNat borrowBv))) ⋆
              (array64 a aXs ⋆ array64 b bXs ⋆ R)) m')
          (hlt : iNat < na.toNat)
          (hva : va = aXs[iNat]'(Nat.lt_of_lt_of_le hlt hna)) (hvb : vb = vbRef) :
          Js (decide (va.toNat < vb.toNat + Bool.toNat borrowBv), BitVec.ofNat 64 iNat + 1,
            ()) m' := by
        subst hva; subst hvb
        let va0 := aXs[iNat]'(Nat.lt_of_lt_of_le hlt hna)
        let bo := decide (va0.toNat < vbRef.toNat + Bool.toNat borrowBv)
        let d := va0 - vbRef - BitVec.ofNat 64 (Bool.toNat borrowBv)
        rw [hiToNat] at hm'
        rw [show (BitVec.ofNat 64 iNat + 1 : BitVec 64) = BitVec.ofNat 64 (iNat + 1) from
          (BitVec.ofNat_add iNat 1).symm]
        apply hRec (bo, BitVec.ofNat 64 (iNat + 1), ()) m'
        · show na.toNat - (BitVec.ofNat 64 (iNat + 1)).toNat <
          na.toNat - (BitVec.ofNat 64 iNat).toNat
          have h1lt : iNat + 1 < 2 ^ 64 := by omega
          rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
          omega
        · refine ⟨bo, iNat + 1, outXs'.set iNat d, hlt, rfl, rfl, by simp [hlenOut'], ?_, hm'⟩
          rw [limbsVal_take_set_succ outXs' d (by omega),
              limbsVal_take_min_succ bXs hnb,
              limbsVal_take_succ (Nat.lt_of_lt_of_le hlt hna)]
          have hsubb := bv64_subb_eq va0 vbRef borrowBv
          dsimp only [vbRef] at hsubb
          exact subb_limbs_step hDiffInv hsubb
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      · exact subStep hm (by omega) (by simp only [hiToNat])
          (by dsimp [vbRef]; have hltb : iNat < nb.toNat := by omega
              simp only [hltb, ↓reduceDIte, hiToNat])
      · exact subStep hm (by omega) (by simp only [hiToNat, Arg.val])
          (by dsimp [vbRef]; have hgeb : ¬ iNat < nb.toNat := by omega
              simp only [hgeb, ↓reduceDIte])
      · have hiEqNa : iNat = na.toNat := by omega
        subst hiEqNa
        have hBMinEq : limbsVal (bXs.take (min na.toNat nb.toNat)) = limbsVal (bXs.take nb.toNat) :=
          by
          by_cases hleNb : nb.toNat ≤ na.toNat
          · rw [Nat.min_eq_right hleNb]
          · rw [Nat.min_eq_left (by omega)]
            have hbLtPow : limbsVal (bXs.take nb.toNat) < 2 ^ (64 * na.toNat) :=
              Nat.lt_of_le_of_lt hba (limbsVal_take_lt_pow aXs na.toNat)
            exact limbsVal_take_eq_of_lt_pow (by omega) hnb hbLtPow
        rw [hBMinEq] at hDiffInv
        rw [show (if borrowBv = true then 1 else 0) * 2 ^ (64 * na.toNat) =
          if borrowBv = true then 2 ^ (64 * na.toNat) else 0 by cases borrowBv <;> simp] at hDiffInv
        have hDiffExact : limbsVal (outXs'.take na.toNat) =
            limbsVal (aXs.take na.toNat) - limbsVal (bXs.take nb.toNat) :=
          (sub_borrow_false_of_le (limbsVal_take_lt_pow outXs' na.toNat) hba hDiffInv).2
        rw [← bv64_ofNat_toNat na]
        exact bn_trim_tail_wp na.isLt (by omega) hmL hDiffExact
          (fun hLenLe hTakeEq =>
            hQ outXs' mL hlenOut' (by rw [hlenOut'] at hLenLe; exact hLenLe)
              hTakeEq (sep_unpick3_4 (by simpa [sep_assoc] using hmL)))

theorem bn_sub_one_wp :
    ∀ xs m Q X, bnSubOneSpec xs m Q X → Func.wp rtR1Env bn_sub_one.body xs m Q X := by
  intro ⟨a, na, out, ⟨⟩⟩ m Q X ⟨aXs, outXs, R, hna, hnout, hposOrZero, hm, hQ⟩
  dsimp only [Func.wp, bn_sub_one, bn_sub_one_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have hna0 : na.toNat = 0 := by
      have hc : na = 0#64 := by assumption
      subst hc; rfl
    have hdiff0 : limbsVal (aXs.take na.toNat) - 1 = 0 := by
      rw [hna0, limbsVal_take_zero]
    have hQ0 := hQ outXs m rfl (by rw [hdiff0, limbLenNat_zero]; exact Nat.zero_le _)
      (by rw [hdiff0, limbLenNat_zero, limbsVal_take_zero]) hm
    rwa [hdiff0, limbLenNat_zero] at hQ0
  · have hnaPos : 0 < na.toNat := by
      have hc : na ≠ 0#64 := by assumption
      by_cases hz : na.toNat = 0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using hz)) hc
      · omega
    have haGe1 : 1 ≤ limbsVal (aXs.take na.toNat) := by
      rcases hposOrZero with h0 | h1
      · omega
      · exact h1
    refine wp_loop_inv
      (fun (xs : Tup Val [Ty.bool, i64]) mL =>
        ∃ (borrow : Bool) (iNat : Nat) (outXs' : List (BitVec 64)),
          iNat ≤ na.toNat ∧
          xs.1 = borrow ∧
          xs.2.1 = BitVec.ofNat 64 iNat ∧
          outXs'.length = outXs.length ∧
          limbsVal (outXs'.take iNat) + 1 =
            limbsVal (aXs.take iNat) + (if borrow then 1 else 0) * 2 ^ (64 * iNat) ∧
          (array64 out outXs' ⋆ (array64 a aXs ⋆ R)) mL)
      (fun (xs : Tup Val [Ty.bool, i64]) _ => na.toNat - xs.2.1.toNat) ?_ ?_
    · intro Js hJs
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      exact hJs (true, 0#64, ()) m ⟨true, 0, outXs, Nat.zero_le _, rfl, rfl, rfl,
        by rw [limbsVal_take_zero]; rfl, sep_pick2_3 hm⟩
    · intro Js ⟨borrowBv, iBv, ⟨⟩⟩ mL ⟨borrow, iNat, outXs', hiLe, hbEq, hiEq, hlenOut', hDiffInv,
      hmL⟩ hRec
      dsimp only at hbEq hiEq; subst hbEq; subst hiEq
      have hilt64 : iNat < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe na.isLt
      have hiToNat : (BitVec.ofNat 64 iNat).toNat = iNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      · have hlt : iNat < na.toNat := by omega
        let va := aXs[iNat]'(Nat.lt_of_lt_of_le hlt hna)
        let bo := decide (va.toNat < 0 + Bool.toNat borrowBv)
        let d := va - 0 - BitVec.ofNat 64 (Bool.toNat borrowBv)
        have hm' : (array64 out (outXs'.set iNat d) ⋆ (array64 a aXs ⋆ R)) m := by
          simpa [hiToNat, va, d] using hm
        have hinc : BitVec.ofNat 64 iNat + 1 = BitVec.ofNat 64 (iNat + 1) :=
          (BitVec.ofNat_add iNat 1).symm
        rw [hinc]
        have hgoal : Js (bo, BitVec.ofNat 64 (iNat + 1), ()) m := by
          apply hRec (bo, BitVec.ofNat 64 (iNat + 1), ()) m
          · show na.toNat - (BitVec.ofNat 64 (iNat + 1)).toNat <
            na.toNat - (BitVec.ofNat 64 iNat).toNat
            have h1lt : iNat + 1 < 2 ^ 64 := by omega
            rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
            omega
          · refine ⟨bo, iNat + 1, outXs'.set iNat d, hlt, rfl, rfl, by simp [hlenOut'], ?_, hm'⟩
            rw [limbsVal_take_set_succ outXs' d
              (by omega), limbsVal_take_succ (Nat.lt_of_lt_of_le hlt hna)]
            have hsubb := bv64_subb_eq va 0#64 borrowBv
            have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
            have hstep := subb_limbs_step hDiffInv hsubb
            rwa [h0, Nat.mul_zero, Nat.add_zero] at hstep
        simpa [hiToNat, va, bo] using hgoal
      · have hiEqNa : iNat = na.toNat := by omega
        subst hiEqNa
        rw [show (if borrowBv = true then 1 else 0) * 2 ^ (64 * na.toNat) =
          if borrowBv = true then 2 ^ (64 * na.toNat) else 0 by cases borrowBv <;> simp] at hDiffInv
        have hDiffExact : limbsVal (outXs'.take na.toNat) = limbsVal (aXs.take na.toNat) - 1 :=
          (sub_one_borrow_false_of_pos (limbsVal_take_lt_pow outXs' na.toNat) haGe1 hDiffInv).2
        rw [← bv64_ofNat_toNat na]
        exact bn_trim_tail_wp na.isLt (by omega) hmL hDiffExact
          (fun hLenLe hTakeEq =>
            hQ outXs' mL hlenOut' (by rw [hlenOut'] at hLenLe; exact hLenLe)
              hTakeEq (sep_unpick2_3 hmL))

theorem bn_bitwise_wp :
    ∀ xs m Q X, bnBitwiseSpec xs m Q X → Func.wp rtR1Env bn_bitwise.body xs m Q X := by
  intro ⟨op, a, na, b, nb, out, ⟨⟩⟩ m Q X ⟨aXs, bXs, outXs, R, hop, hna, hnb, hnout, hm, hQ⟩
  dsimp only [Func.wp, bn_bitwise, bn_bitwise_body]
  change LeanQbe.T.wp _ _ _ _ _
  let nres := if op = 0#64 then min na.toNat nb.toNat else max na.toNat nb.toNat
  have hnresLeOut : nres ≤ outXs.length := hnout
  have hnresLt64 : nres < 2 ^ 64 := by
    dsimp [nres]; split <;> omega
  refine wp_join_tup _ _ (fun (p1 : Tup Val [i64]) m1 => p1.1 = BitVec.ofNat 64 nres ∧ m1 = m) ?_ ?_
  · intro ⟨nresBv, ⟨⟩⟩ m1 ⟨hnresEq, hm1⟩
    dsimp only at hnresEq; subst hnresEq; rw [hm1] at *
    refine wp_loop_inv
      (fun (xs : Tup Val [i64]) mL =>
        ∃ (iNat : Nat) (outXs' : List (BitVec 64)) (hiLe : iNat ≤ nres) (hlenOut' : outXs'.length =
          outXs.length),
          xs.1 = BitVec.ofNat 64 iNat ∧
          (∀ j (hj : j < iNat),
            outXs'[j]'(by omega) =
              bwOp op (if ha : j < na.toNat then aXs[j]'(Nat.lt_of_lt_of_le ha hna) else 0#64)
                      (if hb : j < nb.toNat then bXs[j]'(Nat.lt_of_lt_of_le hb hnb) else 0#64)) ∧
          (array64 out outXs' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mL)
      (fun (xs : Tup Val [i64]) _ => nres - xs.1.toNat) ?_ ?_
    · intro Js hJs
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      exact hJs (0#64, ()) m ⟨0, outXs, Nat.zero_le _, rfl, rfl, fun j hj =>
        by omega, sep_pick3_4 hm⟩
    · intro Js ⟨iBv, ⟨⟩⟩ mL ⟨iNat, outXs', hiLe, hlenOut', hiEq, hLimInv, hmL⟩ hRec
      dsimp only at hiEq; subst hiEq
      have hilt64 : iNat < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe hnresLt64
      have hiToNat : (BitVec.ofNat 64 iNat).toNat = iNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]
      let vaRef : BitVec 64 :=
        if ha : iNat < na.toNat then aXs[iNat]'(Nat.lt_of_lt_of_le ha hna) else 0#64
      let vbRef : BitVec 64 :=
        if hb : iNat < nb.toNat then bXs[iNat]'(Nat.lt_of_lt_of_le hb hnb) else 0#64
      have bwStep {vw : BitVec 64} {m' : Mem 64}
          (hm' : (array64 out (outXs'.set (BitVec.ofNat 64 iNat).toNat vw) ⋆
              (array64 a aXs ⋆ array64 b bXs ⋆ R)) m')
          (hlt : iNat < nres) (hvw : vw = bwOp op vaRef vbRef) :
          Js (BitVec.ofNat 64 iNat + 1, ()) m' := by
        subst hvw
        rw [hiToNat] at hm'
        rw [show (BitVec.ofNat 64 iNat + 1 : BitVec 64) = BitVec.ofNat 64 (iNat + 1) from
          (BitVec.ofNat_add iNat 1).symm]
        apply hRec (BitVec.ofNat 64 (iNat + 1), ()) m'
        · show nres - (BitVec.ofNat 64 (iNat + 1)).toNat < nres - (BitVec.ofNat 64 iNat).toNat
          have h1lt : iNat + 1 < 2 ^ 64 := by omega
          rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
          omega
        · refine ⟨iNat + 1, outXs'.set iNat (bwOp op vaRef vbRef), hlt, by simp [hlenOut'], rfl, ?_,
          hm'⟩
          intro j hj
          by_cases hjEq : j = iNat
          · subst hjEq; rw [List.getElem_set_self]
          · rw [List.getElem_set_ne (by omega)]; exact hLimInv j (by omega)
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      all_goals first
        | (have hiEqNres : iNat = nres := by
             have hcExit : ¬ (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 nres).toNat := by
               assumption
             rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnresLt64] at hcExit
             omega
           subst hiEqNres
           have hOutEq : limbsVal (outXs'.take nres) =
               if op = 0#64 then (limbsVal (aXs.take na.toNat)).land (limbsVal (bXs.take nb.toNat))
               else if op =
                 1#64 then (limbsVal (aXs.take na.toNat)).lor (limbsVal (bXs.take nb.toNat))
               else (limbsVal (aXs.take na.toNat)).xor (limbsVal (bXs.take nb.toNat)) :=
             limbsVal_bitwise_eq op hop aXs bXs outXs' na.toNat nb.toNat nres hna hnb (by omega) rfl
             hLimInv
           exact bn_trim_tail_wp hnresLt64 (by omega) hmL hOutEq
             (fun hLenLe hTakeEq =>
               hQ outXs' mL hlenOut' (by rw [hlenOut'] at hLenLe; exact hLenLe)
                 hTakeEq (sep_unpick3_4 (by simpa [sep_assoc] using hmL))))
        | exact bwStep hm
            (by have hcLt : (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 nres).toNat :=
                by assumption
                rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnresLt64] at hcLt
                exact hcLt)
            (by dsimp only [bwOp, vaRef, vbRef]
                first
                  | (have _ : iNat < na.toNat := by omega
                     simp only [hiToNat])
                  | (have _ : iNat < nb.toNat := by omega
                     simp only [hiToNat])
                  | skip
                first
                  | simp only [show op = 0#64 by assumption, ↓reduceIte]
                  | (simp only [show op ≠ 0#64 by assumption, ↓reduceIte]
                     simp only [show op = 1#64 by assumption, ↓reduceIte])
                  | (simp only [show op ≠ 0#64 by assumption, ↓reduceIte]
                     simp only [show op ≠ 1#64 by assumption, ↓reduceIte])
                first
                  | simp only [show iNat < na.toNat by omega, ↓reduceDIte]
                  | simp only [show ¬ iNat < na.toNat by omega, ↓reduceDIte]
                first
                  | simp only [show iNat < nb.toNat by omega, ↓reduceDIte]
                  | simp only [show ¬ iNat < nb.toNat by omega, ↓reduceDIte]
                try rfl)
  · intro Js hJs
    change LeanQbe.T.wp _ _ _ _ _
    apply wp_cmp
    intro c0 hc0
    rw [wp_jnz]
    constructor
    · intro hc0t
      dsimp only [Arg.val] at hc0 hc0t
      rw [hc0t] at hc0
      have hop0 : op = 0#64 := by simpa [CmpOp.evalBits] using hc0.symm
      refine wp_join_tup _ _ (fun (p2 : Tup Val [i64]) m2 => p2.1 = BitVec.ofNat 64 nres ∧
        m2 = m) ?_ ?_
      · intro ⟨pv, ⟨⟩⟩ m2 ⟨hpv, hm2⟩
        rw [wp_jump]
        exact hJs (pv, ()) m2 ⟨hpv, hm2⟩
      · intro Js1 hJs1
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        · exact hJs1 (na,
          ()) m ⟨by dsimp [nres];
                    simp only [hop0, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt
                      (by assumption)), bv64_ofNat_toNat], rfl⟩
        · exact hJs1 (nb,
          ()) m ⟨by dsimp [nres];
                    simp only [hop0, ↓reduceIte, Nat.min_eq_right
                      (by omega : nb.toNat ≤ na.toNat), bv64_ofNat_toNat], rfl⟩
    · intro hc0f
      dsimp only [Arg.val] at hc0 hc0f
      rw [hc0f] at hc0
      have hopNe0 : op ≠ 0#64 := by simpa [CmpOp.evalBits] using hc0.symm
      refine wp_join_tup _ _ (fun (p2 : Tup Val [i64]) m2 => p2.1 = BitVec.ofNat 64 nres ∧
        m2 = m) ?_ ?_
      · intro ⟨pv, ⟨⟩⟩ m2 ⟨hpv, hm2⟩
        rw [wp_jump]
        exact hJs (pv, ()) m2 ⟨hpv, hm2⟩
      · intro Js1 hJs1
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        · exact hJs1 (na,
          ()) m ⟨by dsimp [nres];
                    simp only [hopNe0, ↓reduceIte, Nat.max_eq_left (Nat.le_of_lt
                      (by assumption)), bv64_ofNat_toNat], rfl⟩
        · exact hJs1 (nb,
          ()) m ⟨by dsimp [nres];
                    simp only [hopNe0, ↓reduceIte, Nat.max_eq_right
                      (by omega : na.toNat ≤ nb.toNat), bv64_ofNat_toNat], rfl⟩

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

private theorem bv64_mac_step_eq (a b cur carry : BitVec 64) (c1 c2 : Bool)
    (hc1 : c1 = true ↔ 2 ^ 64 ≤ cur.toNat + a.toNat * b.toNat % 2 ^ 64 + false.toNat)
    (hc2 : c2 = true ↔
      2 ^ 64 ≤ (cur.toNat + a.toNat * b.toNat + false.toNat) % 2 ^ 64 + carry.toNat + false.toNat) :
    ((cur + a * b + BitVec.ofNat 64 false.toNat) + carry + BitVec.ofNat 64 false.toNat).toNat +
        2 ^ 64 * ((BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) + (if c1 then 1 else 0)) +
          (if c2 then 1 else 0)).toNat =
      cur.toNat + carry.toNat + a.toNat * b.toNat := by
  have hlo : a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
    have ha := bv64_ofNat_toNat a
    have hb := bv64_ofNat_toNat b
    calc
      a * b = BitVec.ofNat 64 a.toNat * BitVec.ofNat 64 b.toNat := by rw [ha, hb]
      _ = BitVec.ofNat 64 (a.toNat * b.toNat) := (BitVec.ofNat_mul a.toNat b.toNat).symm
  have hhi : BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) =
      BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64) := by
    rw [Nat.shiftRight_eq_div_pow]
  have hadd : ∀ (x y : BitVec 64), x + y = BitVec.ofNat 64 (x.toNat + y.toNat) := by
    intro x y
    calc
      x + y = BitVec.ofNat 64 x.toNat + BitVec.ofNat 64 y.toNat := by
        rw [bv64_ofNat_toNat, bv64_ofNat_toNat]
      _ = BitVec.ofNat 64 (x.toNat + y.toNat) := (BitVec.ofNat_add _ _).symm
  have hf : BitVec.ofNat 64 false.toNat = 0#64 := rfl
  have hf0 : false.toNat = 0 := rfl
  have hs1 : cur + a * b + BitVec.ofNat 64 false.toNat =
      BitVec.ofNat 64 (cur.toNat + (a * b).toNat) := by
    rw [hf, BitVec.add_zero, hadd]
  have hs2 : cur + a * b + BitVec.ofNat 64 false.toNat + carry + BitVec.ofNat 64 false.toNat =
      BitVec.ofNat 64 ((BitVec.ofNat 64 (cur.toNat + (a * b).toNat)).toNat + carry.toNat) := by
    rw [hs1, hf, BitVec.add_zero, hadd]
  have hc1eq : c1 = decide (2 ^ 64 ≤ cur.toNat + (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat) := by
    rw [BitVec.toNat_ofNat]
    cases c1 with
    | true =>
      exact (decide_eq_true (by have h := hc1.mp rfl; rw [hf0, Nat.add_zero] at h; exact h)).symm
    | false =>
      exact (decide_eq_false (fun h => by
        have h' := hc1.mpr (by rw [hf0, Nat.add_zero]; exact h)
        cases h')).symm
  have hc2eq : c2 = decide (2 ^ 64 ≤
      (BitVec.ofNat 64 (cur.toNat + (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat)).toNat +
        carry.toNat) := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.add_mod_mod]
    cases c2 with
    | true =>
      exact (decide_eq_true
        (by have h := hc2.mp rfl; rw [hf0, Nat.add_zero, Nat.add_zero] at h; exact h)).symm
    | false =>
      exact (decide_eq_false (fun h => by
        have h' := hc2.mpr (by rw [hf0, Nat.add_zero, Nat.add_zero]; exact h)
        cases h')).symm
  have h1bit : (if c1 = true then (1 : BitVec 64) else 0) = if c1 = true then 1#64 else 0#64 := by
    cases c1 <;> rfl
  have h2bit : (if c2 = true then (1 : BitVec 64) else 0) = if c2 = true then 1#64 else 0#64 := by
    cases c2 <;> rfl
  have hm0 := mac_step_nat a b cur carry
  dsimp only at hm0
  rw [← hlo] at hm0
  rw [hs2, hhi, h1bit, h2bit, hc1eq, hc2eq, ← hlo]
  exact hm0

theorem bn_mul_wp :
    ∀ xs m Q X, bnMulSpec xs m Q X → Func.wp rtR1Env bn_mul.body xs m Q X := by
  intro ⟨a, na, b, nb, out, ⟨⟩⟩ m Q X ⟨aXs, bXs, outXs, R, hna, hnb, hnout, hsum64, hm, hQ⟩
  dsimp only [Func.wp, bn_mul, bn_mul_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  have hsum : (na + nb).toNat = na.toNat + nb.toNat := by
    rw [BitVec.toNat_add]; omega
  refine bn_zero_call_wp (by omega) (sep_pick3_4 hm) ?_
  · intro m0 hm0
    let nsum := na.toNat + nb.toNat
    have hsumToNat : (na + nb).toNat = nsum := hsum
    rw [hsumToNat] at hm0
    let out0 := List.replicate nsum 0#64 ++ outXs.drop nsum
    have hout0Len : out0.length = outXs.length := by
      dsimp [out0]; simp [List.length_drop]; omega
    have hout0Zero : ∀ k (hk : k < nsum), out0[k]'(by omega) = 0#64 := by
      intro k hk
      dsimp [out0]
      rw [List.getElem_append_left (by simp [hk]), List.getElem_replicate]
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · have hna0 : na.toNat = 0 := by
        have hc : na = 0#64 := by assumption
        simp [hc]
      have hprod0 : limbsVal (aXs.take na.toNat) * limbsVal (bXs.take nb.toNat) = 0 := by
        simp [hna0]
      rw [hprod0] at hQ
      have htn0 : limbLenNat 0 = 0 := rfl
      exact hQ out0 m0 hout0Len (by omega) (by rw [htn0, List.take_zero, limbsVal_nil])
        (sep_unpick3_4 hm0)
    · have hnb0 : nb.toNat = 0 := by
        have hc : nb = 0#64 := by assumption
        simp [hc]
      have hprod0 : limbsVal (aXs.take na.toNat) * limbsVal (bXs.take nb.toNat) = 0 := by
        simp [hnb0]
      rw [hprod0] at hQ
      have htn0 : limbLenNat 0 = 0 := rfl
      exact hQ out0 m0 hout0Len (by omega) (by rw [htn0, List.take_zero, limbsVal_nil])
        (sep_unpick3_4 hm0)
    · have hnaPos : 0 < na.toNat := by
        have hc : ¬ na = 0#64 := by assumption
        exact bv64_toNat_pos_of_ne hc
      have hnbPos : 0 < nb.toNat := by
        have hc : ¬ nb = 0#64 := by assumption
        exact bv64_toNat_pos_of_ne hc
      refine wp_loop_inv
        (fun (xs : Tup Val [i64]) mL =>
          ∃ (iNat : Nat) (outXs' : List (BitVec 64))
              (hiLe : iNat ≤ na.toNat) (hlenOut' : outXs'.length = outXs.length),
            xs.1 = BitVec.ofNat 64 iNat ∧
            (∀ k (hk : k < nsum), iNat + nb.toNat ≤ k → outXs'[k]'(by omega) = 0#64) ∧
            limbsVal (outXs'.take (iNat + nb.toNat)) =
              limbsVal (aXs.take iNat) * limbsVal (bXs.take nb.toNat) ∧
            (array64 out outXs' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mL)
        (fun (xs : Tup Val [i64]) _ => na.toNat - xs.1.toNat) ?_ ?_
      · intro Js hJs
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        refine hJs (0#64, ()) m0 ⟨0, out0, Nat.zero_le _, hout0Len, rfl,
          fun k hk _ => hout0Zero k hk, ?_, hm0⟩
        have htake0 : out0.take nb.toNat = List.replicate nb.toNat 0#64 := by
          dsimp [out0]
          rw [List.take_append_of_le_length (by simp; dsimp [nsum]; omega),
              List.take_replicate, Nat.min_eq_left (by dsimp [nsum]; omega)]
        rw [Nat.zero_add, htake0, limbsVal_replicate_zero, List.take_zero, limbsVal_nil,
          Nat.zero_mul]
      · intro Js ⟨iBv, ⟨⟩⟩ mL ⟨iNat, outXs', hiLe, hlenOut', hiEq, hZeroTail, hProdInv, hmL⟩ hRec
        dsimp only at hiEq; subst hiEq
        have hilt64 : iNat < 2 ^ 64 := by omega
        have hiToNat : (BitVec.ofNat 64 iNat).toNat = iNat := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        · have hltNa : iNat < na.toNat := by
            have hc : (BitVec.ofNat 64 iNat).toNat < na.toNat := by assumption
            rwa [hiToNat] at hc
          let av := aXs[iNat]'(Nat.lt_of_lt_of_le hltNa hna)
          refine wp_loop_inv
            (fun (ys : Tup Val [i64, i64]) mIn =>
              ∃ (carry : BitVec 64) (jNat : Nat) (outXs'' : List (BitVec 64))
                  (hjLe : jNat ≤ nb.toNat) (hlenOut'' : outXs''.length = outXs.length),
                ys.1 = carry ∧ ys.2.1 = BitVec.ofNat 64 jNat ∧
                (∀ k (hk : k < nsum), iNat + nb.toNat ≤ k → outXs''[k]'(by omega) = 0#64) ∧
                limbsVal (outXs''.take (iNat + nb.toNat)) + 2 ^ (64 * (iNat + jNat)) * carry.toNat =
                  limbsVal (aXs.take iNat) * limbsVal (bXs.take nb.toNat) +
                    2 ^ (64 * iNat) * (av.toNat * limbsVal (bXs.take jNat)) ∧
                (array64 out outXs'' ⋆ (array64 a aXs ⋆ array64 b bXs ⋆ R)) mIn)
            (fun (ys : Tup Val [i64, i64]) _ => nb.toNat - ys.2.1.toNat) ?_ ?_
          · intro Js1 hJs1
            change LeanQbe.T.wp _ _ _ _ _
            c0_steps
            exact hJs1 (0#64, 0#64, ()) mL ⟨0#64, 0, outXs', Nat.zero_le _, hlenOut', rfl, rfl,
              hZeroTail, by simp [hProdInv], by simpa [av, hiToNat] using hmL⟩
          · intro Js1 ⟨carry, jBv, ⟨⟩⟩ mIn
              ⟨carry0, jNat, outXs'', hjLe, hlenOut'', hcEq, hjEq, hZeroIn, hMacInv, hmIn⟩ hRecIn
            dsimp only at hcEq hjEq; subst hcEq; subst hjEq
            have hjlt64 : jNat < 2 ^ 64 := by omega
            have hjToNat : (BitVec.ofNat 64 jNat).toNat = jNat := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hjlt64]
            have hijlt64 : iNat + jNat < 2 ^ 64 := by omega
            have hijToNat : (BitVec.ofNat 64 iNat + BitVec.ofNat 64 jNat).toNat = iNat + jNat := by
              rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hijlt64]
            have inbToNat : (BitVec.ofNat 64 iNat + nb).toNat = iNat + nb.toNat := by
              rw [BitVec.toNat_add, hiToNat, Nat.mod_eq_of_lt (by omega)]
            have macStep {carryNext : BitVec 64} {s2 : BitVec 64} {m' : Mem 64}
                (hm' : (array64 out (outXs''.set (iNat + jNat) s2) ⋆
                    (array64 a aXs ⋆ array64 b bXs ⋆ R)) m')
                (hltNb : jNat < nb.toNat)
                (hmac : s2.toNat + 2 ^ 64 * carryNext.toNat =
                  (outXs''[iNat + jNat]'(by omega)).toNat + carry.toNat +
                    av.toNat * (bXs[jNat]'(Nat.lt_of_lt_of_le hltNb hnb)).toNat) :
                Js1 (carryNext, BitVec.ofNat 64 jNat + 1, ()) m' := by
              rw [show (BitVec.ofNat 64 jNat + 1 : BitVec 64) = BitVec.ofNat 64 (jNat + 1) from
                (BitVec.ofNat_add jNat 1).symm]
              apply hRecIn (carryNext, BitVec.ofNat 64 (jNat + 1), ()) m'
              · show nb.toNat - (BitVec.ofNat 64 (jNat + 1)).toNat <
                nb.toNat - (BitVec.ofNat 64 jNat).toNat
                have h1lt : jNat + 1 < 2 ^ 64 := by omega
                rw [hjToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
                omega
              · refine ⟨carryNext, jNat + 1, outXs''.set (iNat + jNat) s2, hltNb,
                  by simp [hlenOut''], rfl, rfl, ?_, ?_, hm'⟩
                · intro k hk hik
                  rw [List.getElem_set_ne (by omega)]
                  exact hZeroIn k hk hik
                · have houtSwap := limbsVal_take_set_of_lt outXs'' s2 (p := iNat + jNat)
                    (M := iNat + nb.toNat) (by omega) (by omega)
                  have hbNext := limbsVal_take_succ (xs := bXs) (Nat.lt_of_lt_of_le hltNb hnb)
                  exact mul_inner_step_eq houtSwap hmac hMacInv hbNext
            have hmodI : iNat % 2 ^ 64 = iNat := Nat.mod_eq_of_lt hilt64
            have hmodJ : jNat % 2 ^ 64 = jNat := Nat.mod_eq_of_lt hjlt64
            have hmodIJ : (iNat + jNat) % 2 ^ 64 = iNat + jNat := Nat.mod_eq_of_lt hijlt64
            change LeanQbe.T.wp _ _ _ _ _
            c0_steps
            all_goals first
              | (have hjEqNb : jNat = nb.toNat := by
                   have hc : ¬ jNat % 2 ^ 64 < nb.toNat := by assumption
                   rw [hmodJ] at hc; omega
                 subst hjEqNb
                 have hm' := hm
                 simp only [inbToNat] at hm'
                 rw [show (BitVec.ofNat 64 iNat + 1 : BitVec 64) = BitVec.ofNat 64 (iNat + 1) from
                   (BitVec.ofNat_add iNat 1).symm]
                 apply hRec (BitVec.ofNat 64 (iNat + 1), ()) m
                 · show na.toNat - (BitVec.ofNat 64 (iNat + 1)).toNat <
                   na.toNat - (BitVec.ofNat 64 iNat).toNat
                   have h1lt : iNat + 1 < 2 ^ 64 := by omega
                   rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
                   omega
                 · refine ⟨iNat + 1, outXs''.set (iNat + nb.toNat) carry, hltNa,
                     by simp [hlenOut''], rfl, ?_, ?_, hm'⟩
                   · intro k hk hik
                     rw [List.getElem_set_ne (by omega)]
                     exact hZeroIn k hk (by omega)
                   · rw [show iNat + 1 + nb.toNat = (iNat + nb.toNat) + 1 by omega]
                     rw [limbsVal_take_set_succ outXs'' carry (by omega), hMacInv,
                         limbsVal_take_succ (Nat.lt_of_lt_of_le hltNa hna)]
                     dsimp [av]
                     rw [← Nat.mul_assoc, ← Nat.add_mul])
              | (have hltNb : jNat < nb.toNat := by
                   have hc : jNat % 2 ^ 64 < nb.toNat := by assumption
                   rwa [hmodJ] at hc
                 have hm' := hm
                 simp only [hijToNat, hiToNat, hjToNat] at hm'
                 apply macStep hm' hltNb
                 simp only [hiToNat, hjToNat]
                 dsimp only [av]
                 first
                   | apply bv64_mac_step_eq (c1 := true) (c2 := true)
                   | apply bv64_mac_step_eq (c1 := true) (c2 := false)
                   | apply bv64_mac_step_eq (c1 := false) (c2 := true)
                   | apply bv64_mac_step_eq (c1 := false) (c2 := false)
                 · constructor
                   · intro h
                     first
                       | (cases h; done)
                       | (have hc1 : 2 ^ 64 ≤
                              (outXs''[(iNat + jNat) % 2 ^ 64]'(by rw [hmodIJ]; omega)).toNat +
                                (aXs[iNat % 2 ^ 64]'(by rw [hmodI]; omega)).toNat *
                                  (bXs[jNat % 2 ^ 64]'(by rw [hmodJ]; omega)).toNat % 2 ^ 64 +
                                false.toNat := by assumption
                          simp only [hmodI, hmodJ, hmodIJ] at hc1
                          exact hc1)
                   · intro hc1
                     first
                       | rfl
                       | (have hnot : ¬ 2 ^ 64 ≤
                              (outXs''[(iNat + jNat) % 2 ^ 64]'(by rw [hmodIJ]; omega)).toNat +
                                (aXs[iNat % 2 ^ 64]'(by rw [hmodI]; omega)).toNat *
                                  (bXs[jNat % 2 ^ 64]'(by rw [hmodJ]; omega)).toNat % 2 ^ 64 +
                                false.toNat := by assumption
                          simp only [hmodI, hmodJ, hmodIJ] at hnot
                          exact absurd hc1 hnot)
                 · constructor
                   · intro h
                     first
                       | (cases h; done)
                       | (have hc2 : 2 ^ 64 ≤
                              ((outXs''[(iNat + jNat) % 2 ^ 64]'(by rw [hmodIJ]; omega)).toNat +
                                  (aXs[iNat % 2 ^ 64]'(by rw [hmodI]; omega)).toNat *
                                    (bXs[jNat % 2 ^ 64]'(by rw [hmodJ]; omega)).toNat +
                                  false.toNat) % 2 ^ 64 +
                                carry.toNat + false.toNat := by assumption
                          simp only [hmodI, hmodJ, hmodIJ] at hc2
                          exact hc2)
                   · intro hc2
                     first
                       | rfl
                       | (have hnot : ¬ 2 ^ 64 ≤
                              ((outXs''[(iNat + jNat) % 2 ^ 64]'(by rw [hmodIJ]; omega)).toNat +
                                  (aXs[iNat % 2 ^ 64]'(by rw [hmodI]; omega)).toNat *
                                    (bXs[jNat % 2 ^ 64]'(by rw [hmodJ]; omega)).toNat +
                                  false.toNat) % 2 ^ 64 +
                                carry.toNat + false.toNat := by assumption
                          simp only [hmodI, hmodJ, hmodIJ] at hnot
                          exact absurd hc2 hnot))
        · have hiEqNa : iNat = na.toNat := by
            have hc : ¬ (BitVec.ofNat 64 iNat).toNat < na.toNat := by assumption
            rw [hiToNat] at hc; omega
          subst hiEqNa
          rw [← bv64_ofNat_toNat (na + nb), hsumToNat]
          exact bn_trim_tail_wp hsum64 (by omega) hmL hProdInv
            (fun hLenLe hTakeEq =>
              hQ outXs' mL hlenOut' (by rw [hlenOut'] at hLenLe; exact hLenLe)
                hTakeEq (sep_unpick3_4 hmL))

theorem bn_shl_wp :
    ∀ xs m Q X, bnShlSpec xs m Q X → Func.wp rtR1Env bn_shl.body xs m Q X := by
  intro ⟨a, na, ws, bs, out, ⟨⟩⟩ m Q X ⟨aXs, outXs, R, hna, hbs, houtOr, hbound, hm, hQ⟩
  dsimp only [Func.wp, bn_shl, bn_shl_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have hna0 : na.toNat = 0 := by
      have hc : na = 0#64 := by assumption
      simp [hc]
    have hres0 : limbsVal (aXs.take na.toNat) <<< (64 * ws.toNat + bs.toNat) = 0 := by
      simp [hna0]
    rw [hres0] at hQ
    have htn0 : limbLenNat 0 = 0 := rfl
    exact hQ outXs m rfl (Nat.zero_le _) (by rw [htn0, List.take_zero, limbsVal_nil]) hm
  · have hnaPos : 0 < na.toNat := by
      have hc : ¬ na = 0#64 := by assumption
      exact bv64_toNat_pos_of_ne hc
    have houtLe : ws.toNat + na.toNat + 1 ≤ outXs.length := by
      rcases houtOr with h0 | hle
      · omega
      · exact hle
    refine bn_zero_call_wp (by omega) (sep_pick2_3 hm) ?_
    intro m0 hm0
    let out0 := List.replicate ws.toNat 0#64 ++ outXs.drop ws.toNat
    have hout0Len : out0.length = outXs.length := by
      dsimp [out0]; simp [List.length_drop]; omega
    have hwsnaLt64 : (ws + na).toNat = ws.toNat + na.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hwsna1Lt64 : (ws + na + 1).toNat = ws.toNat + na.toNat + 1 := by
      rw [BitVec.toNat_add, hwsnaLt64]
      change (ws.toNat + na.toNat + 1) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · have hbs0 : bs = 0#64 := by assumption
      have hbsNat : bs.toNat = 0 := by simp [hbs0]
      have hmSplit : (array64 (out + ((8 : BitVec 64) * ws)) (out0.drop ws.toNat) ⋆
          array64 a aXs ⋆ (array64 out (out0.take ws.toNat) ⋆ R)) m0 := by
        have hsp := array64_split2 out out0 ws.toNat (by omega)
        rw [← bv64_mul8_eq] at hsp
        rw [hsp] at hm0
        exact sep_ac hm0
      refine bn_copy_call_wp
        (by rw [List.length_drop, hout0Len]; omega) hna hmSplit ?_
      intro m1 hm1
      let dstTail := aXs.take na.toNat ++ (out0.drop ws.toNat).drop na.toNat
      let out1 := out0.take ws.toNat ++ dstTail
      have hout1Len : out1.length = outXs.length := by
        dsimp [out1, dstTail]
        simp [List.length_take, List.length_drop, hout0Len]
        omega
      have hmJoined : (array64 out out1 ⋆ (array64 a aXs ⋆ R)) m1 := by
        have hlenWs : (out0.take ws.toNat).length = ws.toNat := by simp [hout0Len]; omega
        have happ := array64_append out (out0.take ws.toNat) dstTail
        rw [hlenWs, ← bv64_mul8_eq] at happ
        have hm1' : ((array64 out (out0.take ws.toNat) ⋆
          array64 (out + (8 : BitVec 64) * ws) dstTail) ⋆
            (array64 a aXs ⋆ R)) m1 := sep_ac hm1
        rwa [← happ] at hm1'
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      have hwsnaEq : ((ws + na).toNat) = ws.toNat + na.toNat := hwsnaLt64
      have hm2 : (array64 out (out1.set (ws.toNat + na.toNat) 0#64) ⋆ (array64 a aXs ⋆ R)) m := by
        simpa [hwsnaEq] using hm
      let out2 := out1.set (ws.toNat + na.toNat) 0#64
      have hout2Len : out2.length = outXs.length := by simp [out2, hout1Len]
      have hout2Val : limbsVal (out2.take (ws.toNat + na.toNat + 1)) =
          limbsVal (aXs.take na.toNat) <<< (64 * ws.toNat + bs.toNat) := by
        dsimp [out2]
        rw [limbsVal_take_set_succ out1 0#64 (by rw [hout1Len]; omega)]
        have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
        rw [h0, Nat.mul_zero, Nat.add_zero]
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
            List.length_replicate, hbsNat, Nat.add_zero, Nat.shiftLeft_eq, Nat.mul_comm]
      rw [← bv64_ofNat_toNat (ws + na + 1), hwsna1Lt64]
      exact bn_trim_tail_wp (by omega) (by rw [hout2Len]; exact houtLe) hm2 hout2Val
        (fun hLenLe hTakeEq =>
          hQ out2 m hout2Len (by rw [hout2Len] at hLenLe; exact hLenLe)
            hTakeEq (sep_unpick2_3 hm2))
    · have hbsPos : 0 < bs.toNat := by
        have hc : ¬ bs = 0#64 := by assumption
        exact bv64_toNat_pos_of_ne hc
      have hbsMod : bs.toNat % 64 = bs.toNat := Nat.mod_eq_of_lt hbs
      have hsub64Nat : (64#64 - bs).toNat = 64 - bs.toNat := by
        rw [BitVec.toNat_sub_of_le (by change bs.toNat ≤ 64; omega)]; rfl
      have hsub64Mod : (64 - bs).toNat % 64 = 64 - bs.toNat := by
        rw [show (64 : BitVec 64) - bs = 64#64 - bs from rfl, hsub64Nat]
        exact Nat.mod_eq_of_lt (by omega)
      refine wp_loop_inv
        (fun (ys : Tup Val [i64, i64]) mL =>
          ∃ (carry : BitVec 64) (iNat : Nat) (outXs' : List (BitVec 64))
              (hiLe : iNat ≤ na.toNat) (hlenOut' : outXs'.length = outXs.length),
            ys.1 = carry ∧ ys.2.1 = BitVec.ofNat 64 iNat ∧
            carry.toNat < 2 ^ bs.toNat ∧
            limbsVal (outXs'.take (ws.toNat + iNat)) +
                2 ^ (64 * (ws.toNat + iNat)) * carry.toNat =
              limbsVal (aXs.take iNat) <<< (64 * ws.toNat + bs.toNat) ∧
            (array64 out outXs' ⋆ (array64 a aXs ⋆ R)) mL)
        (fun (ys : Tup Val [i64, i64]) _ => na.toNat - ys.2.1.toNat) ?_ ?_
      · intro Js hJs
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        refine hJs (0#64, 0#64, ()) m0 ⟨0#64, 0, out0, Nat.zero_le _, hout0Len, rfl, rfl,
          Nat.two_pow_pos _, ?_, hm0⟩
        have htake0 : out0.take ws.toNat = List.replicate ws.toNat 0#64 := by
          dsimp [out0]
          rw [List.take_append_of_le_length (by simp), List.take_replicate, Nat.min_self]
        rw [Nat.add_zero, htake0, limbsVal_replicate_zero, List.take_zero, limbsVal_nil]
        simp
      · intro Js ⟨carry, iBv, ⟨⟩⟩ mL
          ⟨carry0, iNat, outXs', hiLe, hlenOut', hcEq, hiEq, hcarryLt, hShlInv, hmL⟩ hRec
        dsimp only at hcEq hiEq; subst hcEq; subst hiEq
        have hilt64 : iNat < 2 ^ 64 := by omega
        have hiToNat : (BitVec.ofNat 64 iNat).toNat = iNat := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]
        have hwsiLt64 : ws.toNat + iNat < 2 ^ 64 := by omega
        have hwsiToNat : (ws + BitVec.ofNat 64 iNat).toNat = ws.toNat + iNat := by
          rw [BitVec.toNat_add, hiToNat, Nat.mod_eq_of_lt hwsiLt64]
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        · have hltNa : iNat < na.toNat := by
            have hc : (BitVec.ofNat 64 iNat).toNat < na.toNat := by assumption
            rwa [hiToNat] at hc
          let ld := aXs[iNat]'(Nat.lt_of_lt_of_le hltNa hna)
          let w := (ld <<< bs) ||| carry
          let carryNext := ld >>> (64#64 - bs)
          have hm' : (array64 out (outXs'.set (ws.toNat + iNat) w) ⋆ (array64 a aXs ⋆ R)) m := by
            have hm1 := hm
            simp only [hiToNat] at hm1
            rw [hwsiToNat, hbsMod, ← BitVec.shiftLeft_eq'] at hm1
            exact hm1
          rw [show (BitVec.ofNat 64 iNat + 1 : BitVec 64) = BitVec.ofNat 64 (iNat + 1) from
            (BitVec.ofNat_add iNat 1).symm]
          have hstep := shl_step_nat ld bs carry hbs hcarryLt
          have hgoal : Js (carryNext, BitVec.ofNat 64 (iNat + 1), ()) m := by
            apply hRec (carryNext, BitVec.ofNat 64 (iNat + 1), ()) m
            · show na.toNat - (BitVec.ofNat 64 (iNat + 1)).toNat <
              na.toNat - (BitVec.ofNat 64 iNat).toNat
              have h1lt : iNat + 1 < 2 ^ 64 := by omega
              rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
              omega
            · refine ⟨carryNext, iNat + 1, outXs'.set (ws.toNat + iNat) w, hltNa,
                by simp [hlenOut'], rfl, rfl, hstep.2, ?_, hm'⟩
              rw [show ws.toNat + (iNat + 1) = (ws.toNat + iNat) + 1 by omega]
              rw [limbsVal_take_set_succ outXs' w (by omega),
                  limbsVal_take_succ (Nat.lt_of_lt_of_le hltNa hna),
                  Nat.shiftLeft_eq, Nat.add_mul]
              have hpow1 : 2 ^ (64 * (ws.toNat + iNat + 1)) = 2 ^ (64 * (ws.toNat +
                iNat)) * 2 ^ 64 := by
                rw [show 64 * (ws.toNat + iNat + 1) = 64 * (ws.toNat + iNat) + 64 by omega,
                  Nat.pow_add]
              have hpow2 : 2 ^ (64 * (ws.toNat + iNat)) * 2 ^ bs.toNat =
                  2 ^ (64 * iNat) * 2 ^ (64 * ws.toNat + bs.toNat) := by
                rw [Nat.mul_add, Nat.pow_add, Nat.pow_add]; ac_rfl
              have hstep1 := hstep.1
              have hshlInv' : limbsVal (outXs'.take (ws.toNat + iNat)) +
                  2 ^ (64 * (ws.toNat + iNat)) * carry.toNat =
                  limbsVal (aXs.take iNat) * 2 ^ (64 * ws.toNat + bs.toNat) := by
                simpa [Nat.shiftLeft_eq] using hShlInv
              rw [hpow1]
              calc
                limbsVal (outXs'.take (ws.toNat + iNat)) +
                    2 ^ (64 * (ws.toNat + iNat)) * w.toNat +
                    2 ^ (64 * (ws.toNat + iNat)) * 2 ^ 64 * carryNext.toNat
                  = limbsVal (outXs'.take (ws.toNat + iNat)) +
                      2 ^ (64 * (ws.toNat + iNat)) * (w.toNat + 2 ^ 64 * carryNext.toNat) := by
                    rw [Nat.mul_assoc, Nat.add_assoc (limbsVal (outXs'.take (ws.toNat + iNat))),
                      ← Nat.mul_add]
                _ = limbsVal (outXs'.take (ws.toNat + iNat)) +
                      2 ^ (64 * (ws.toNat + iNat)) * (ld.toNat * 2 ^ bs.toNat + carry.toNat) := by
                    rw [hstep1]
                _ = limbsVal (outXs'.take (ws.toNat + iNat)) +
                      2 ^ (64 * (ws.toNat + iNat)) * carry.toNat +
                      (2 ^ (64 * (ws.toNat + iNat)) * 2 ^ bs.toNat) * ld.toNat := by
                    rw [Nat.mul_add]; ac_rfl
                _ = limbsVal (aXs.take iNat) * 2 ^ (64 * ws.toNat + bs.toNat) +
                      (2 ^ (64 * iNat) * ld.toNat) * 2 ^ (64 * ws.toNat + bs.toNat) := by
                    rw [hshlInv', hpow2]; ac_rfl
          simp only [hiToNat]
          rw [hsub64Mod, ← hsub64Nat, ← BitVec.ushiftRight_eq']
          exact hgoal
        · have hiEqNa : iNat = na.toNat := by
            have hc : ¬ (BitVec.ofNat 64 iNat).toNat < na.toNat := by assumption
            rw [hiToNat] at hc; omega
          subst hiEqNa
          have hm' : (array64 out (outXs'.set (ws.toNat + na.toNat) carry) ⋆ (array64 a aXs ⋆
            R)) m := by
            simpa [hwsnaLt64] using hm
          let out2 := outXs'.set (ws.toNat + na.toNat) carry
          have hout2Len : out2.length = outXs.length := by simp [out2, hlenOut']
          have hout2Val : limbsVal (out2.take (ws.toNat + na.toNat + 1)) =
              limbsVal (aXs.take na.toNat) <<< (64 * ws.toNat + bs.toNat) := by
            dsimp [out2]
            rw [limbsVal_take_set_succ outXs' carry (by omega), hShlInv]
          rw [← bv64_ofNat_toNat (ws + na + 1), hwsna1Lt64]
          exact bn_trim_tail_wp (by omega) (by rw [hout2Len]; exact houtLe) hm' hout2Val
            (fun hLenLe hTakeEq =>
              hQ out2 m hout2Len (by rw [hout2Len] at hLenLe; exact hLenLe)
                hTakeEq (sep_unpick2_3 hm'))

theorem bn_shr_wp :
    ∀ xs m Q X, bnShrSpec xs m Q X → Func.wp rtR1Env bn_shr.body xs m Q X := by
  intro ⟨a, na, ws, bs, out, ⟨⟩⟩ m Q X ⟨aXs, outXs, R, hna, hbs, houtOr, hm, hQ⟩
  dsimp only [Func.wp, bn_shr, bn_shr_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have hleWs : na.toNat ≤ ws.toNat := by assumption
    have hltPow : limbsVal (aXs.take na.toNat) < 2 ^ (64 * ws.toNat + bs.toNat) := by
      have h1 := limbsVal_take_lt_pow aXs na.toNat
      have hpow : 2 ^ (64 * na.toNat) ≤ 2 ^ (64 * ws.toNat + bs.toNat) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.lt_of_lt_of_le h1 hpow
    have hres0 : limbsVal (aXs.take na.toNat) >>> (64 * ws.toNat + bs.toNat) = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hltPow]
    rw [hres0] at hQ
    have htn0 : limbLenNat 0 = 0 := rfl
    exact hQ outXs m rfl (Nat.zero_le _) (by rw [htn0, List.take_zero, limbsVal_nil]) hm
  · have hnotLeWs : ¬ na.toNat ≤ ws.toNat := by assumption
    have hwsLtNa : ws.toNat < na.toNat := by omega
    let nres := na.toNat - ws.toNat
    have hnresPos : 0 < nres := by dsimp [nres]; omega
    have hnresLeOut : nres ≤ outXs.length := by
      rcases houtOr with hle | hle
      · omega
      · exact hle
    have hnresLt64 : nres < 2 ^ 64 := by dsimp [nres]; omega
    have hsubEq : (na - ws).toNat = nres := by
      dsimp [nres]
      exact BitVec.toNat_sub_of_le (Nat.le_of_lt hwsLtNa)
    have hbs0 : bs = 0#64 := by assumption
    have hbsNat : bs.toNat = 0 := by simp [hbs0]
    have hsp := array64_split2 a aXs ws.toNat (by omega)
    rw [← bv64_mul8_eq] at hsp
    have hmSplit : (array64 out outXs ⋆ array64 (a + (8 : BitVec 64) * ws) (aXs.drop ws.toNat) ⋆
        (array64 a (aXs.take ws.toNat) ⋆ R)) m := by
      rw [hsp] at hm
      exact sep_ac hm
    refine bn_copy_call_wp
      (by rw [hsubEq]; exact hnresLeOut)
      (by rw [hsubEq, List.length_drop]; dsimp [nres]; omega)
      hmSplit ?_
    intro m1 hm1
    rw [hsubEq] at hm1
    let out1 := (aXs.drop ws.toNat).take nres ++ outXs.drop nres
    have hout1Len : out1.length = outXs.length := by
      dsimp [out1]; simp [List.length_take, List.length_drop]; omega
    have hmRestored : (array64 out out1 ⋆ (array64 a aXs ⋆ R)) m1 := by
      have hm1' : (array64 (a + (8 : BitVec 64) * ws) (aXs.drop ws.toNat) ⋆
        array64 a (aXs.take ws.toNat) ⋆
          array64 out out1 ⋆ R) m1 := sep_ac hm1
      have hjoin : (array64 a (aXs.take ws.toNat) ⋆
          array64 (a + (8 : BitVec 64) * ws) (aXs.drop ws.toNat) ⋆ (array64 out out1 ⋆ R)) m1 := by
        exact sep_ac hm1'
      rw [← sep_assoc, ← hsp] at hjoin
      exact sep_ac hjoin
    have hout1Val : limbsVal (out1.take nres) =
        limbsVal (aXs.take na.toNat) >>> (64 * ws.toNat + bs.toNat) := by
      have hout1Take : out1.take nres = (aXs.drop ws.toNat).take nres := by
        dsimp [out1]
        rw [List.take_append_of_le_length
              (by rw [List.length_take_of_le (by rw [List.length_drop]; dsimp [nres]; omega)]
                  exact Nat.le_refl _),
            List.take_take, Nat.min_self]
      have haSplit : aXs.take na.toNat = aXs.take ws.toNat ++ (aXs.drop ws.toNat).take nres := by
        have hadd : na.toNat = ws.toNat + nres := by dsimp [nres]; omega
        rw [hadd, List.take_add]
      have haApp := congrArg limbsVal haSplit
      rw [limbsVal_append, List.length_take_of_le (by omega)] at haApp
      have hltWs := limbsVal_take_lt_pow aXs ws.toNat
      rw [hout1Take, hbsNat, Nat.add_zero, Nat.shiftRight_eq_div_pow, haApp,
          Nat.add_comm (limbsVal (aXs.take ws.toNat)),
          Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hltWs, Nat.add_zero]
    rw [← bv64_ofNat_toNat (na - ws), hsubEq]
    exact bn_trim_tail_wp hnresLt64 (by rw [hout1Len]; exact hnresLeOut) hmRestored hout1Val
      (fun hLenLe hTakeEq =>
        hQ out1 m1 hout1Len (by rw [hout1Len] at hLenLe; exact hLenLe)
          hTakeEq (sep_unpick2_3 hmRestored))
  · have hnotLeWs : ¬ na.toNat ≤ ws.toNat := by assumption
    have hwsLtNa : ws.toNat < na.toNat := by omega
    let nres := na.toNat - ws.toNat
    have hnresPos : 0 < nres := by dsimp [nres]; omega
    have hnresLeOut : nres ≤ outXs.length := by
      rcases houtOr with hle | hle
      · omega
      · exact hle
    have hnresLt64 : nres < 2 ^ 64 := by dsimp [nres]; omega
    have hsubEq : (na - ws).toNat = nres := by
      dsimp [nres]
      exact BitVec.toNat_sub_of_le (Nat.le_of_lt hwsLtNa)
    have hbsPos : 0 < bs.toNat := by
      have hc : ¬ bs = 0#64 := by assumption
      exact bv64_toNat_pos_of_ne hc
    have hbsMod : bs.toNat % 64 = bs.toNat := Nat.mod_eq_of_lt hbs
    have hsub64Nat : (64#64 - bs).toNat = 64 - bs.toNat := by
      rw [BitVec.toNat_sub_of_le (by change bs.toNat ≤ 64; omega)]; rfl
    have hsub64Mod : (64 - bs).toNat % 64 = 64 - bs.toNat := by
      rw [show (64 : BitVec 64) - bs = 64#64 - bs from rfl, hsub64Nat]
      exact Nat.mod_eq_of_lt (by omega)
    refine wp_loop_inv
      (fun (xs : Tup Val [i64]) mL =>
        ∃ (iNat : Nat) (outXs' : List (BitVec 64))
            (hiLe : iNat + 1 ≤ nres) (hlenOut' : outXs'.length = outXs.length),
          xs.1 = BitVec.ofNat 64 iNat ∧
          (∀ j (hj : j < iNat),
            outXs'[j]'(by omega) =
              ((aXs[ws.toNat + j]'(by omega)) >>> bs.toNat) |||
                ((aXs[ws.toNat + j + 1]'(by omega)) <<< (64 - bs.toNat))) ∧
          (array64 out outXs' ⋆ (array64 a aXs ⋆ R)) mL)
      (fun (xs : Tup Val [i64]) _ => nres - xs.1.toNat) ?_ ?_
    · intro Js hJs
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      exact hJs (0#64, ()) m ⟨0, outXs, hnresPos, rfl, rfl, fun j hj => by omega, sep_pick2_3 hm⟩
    · intro Js ⟨iBv, ⟨⟩⟩ mL ⟨iNat, outXs', hiLe, hlenOut', hiEq, hShrInv, hmL⟩ hRec
      dsimp only at hiEq; subst hiEq
      have hilt64 : iNat < 2 ^ 64 := by omega
      have hiToNat : (BitVec.ofNat 64 iNat).toNat = iNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]
      have hi1Lt64 : iNat + 1 < 2 ^ 64 := by omega
      have h1Nat : (1 : BitVec 64).toNat = 1 := rfl
      have hi1ToNat : (BitVec.ofNat 64 iNat + (1 : BitVec 64)).toNat = iNat + 1 := by
        rw [BitVec.toNat_add, hiToNat, h1Nat, Nat.mod_eq_of_lt hi1Lt64]
      have hwsiToNat : (ws + BitVec.ofNat 64 iNat).toNat = ws.toNat + iNat := by
        rw [BitVec.toNat_add, hiToNat, Nat.mod_eq_of_lt (by omega)]
      have hwsi1ToNat : (ws + BitVec.ofNat 64 iNat + (1 : BitVec 64)).toNat = ws.toNat + iNat + 1 :=
        by
        rw [BitVec.toNat_add, hwsiToNat, h1Nat, Nat.mod_eq_of_lt (by omega)]
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      · have hi1Lt : iNat + 1 < nres := by
          have hc : (iNat + (1 : BitVec 64).toNat) % 2 ^ 64 < (2 ^ 64 - ws.toNat +
            na.toNat) % 2 ^ 64 := by
            assumption
          rw [h1Nat] at hc
          dsimp [nres]
          omega
        let w := ((aXs[ws.toNat + iNat]'(by omega)) >>> bs.toNat) |||
          ((aXs[ws.toNat + iNat + 1]'(by omega)) <<< (64 - bs.toNat))
        have hm' : (array64 out (outXs'.set iNat w) ⋆ (array64 a aXs ⋆ R)) m := by
          have hm1 := hm
          simp only [hiToNat, hwsiToNat, hwsi1ToNat] at hm1
          rw [hbsMod, hsub64Mod] at hm1
          exact hm1
        rw [show (BitVec.ofNat 64 iNat + 1 : BitVec 64) = BitVec.ofNat 64 (iNat + 1) from
          (BitVec.ofNat_add iNat 1).symm]
        apply hRec (BitVec.ofNat 64 (iNat + 1), ()) m
        · show nres - (BitVec.ofNat 64 (iNat + 1)).toNat < nres - (BitVec.ofNat 64 iNat).toNat
          rw [hiToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi1Lt64]
          omega
        · refine ⟨iNat + 1, outXs'.set iNat w, hi1Lt, by simp [hlenOut'], rfl, ?_, hm'⟩
          intro j hj
          by_cases hjEq : j = iNat
          · subst hjEq
            rw [List.getElem_set_self]
          · rw [List.getElem_set_ne (by omega)]
            exact hShrInv j (by omega)
      · have hiEqLast : iNat + 1 = nres := by
          have hc : ¬ (iNat + (1 : BitVec 64).toNat) % 2 ^ 64 < (2 ^ 64 - ws.toNat +
            na.toNat) % 2 ^ 64 := by
            assumption
          rw [h1Nat] at hc
          dsimp [nres] at hc ⊢
          omega
        have hresSubToNat : (na - ws - (1 : BitVec 64)).toNat = nres - 1 := by
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hsubEq]; change 1 ≤ nres; omega),
              hsubEq]
          rfl
        have hwsResSubToNat : (ws + (na - ws) - (1 : BitVec 64)).toNat = ws.toNat + (nres - 1) := by
          have hwsRes : (ws + (na - ws)).toNat = ws.toNat + nres := by
            rw [BitVec.toNat_add, hsubEq, Nat.mod_eq_of_lt (by omega)]
          rw [BitVec.toNat_sub_of_le
            (by rw [BitVec.le_def, hwsRes]; change 1 ≤ ws.toNat + nres; omega),
              hwsRes]
          change ws.toNat + nres - 1 = ws.toNat + (nres - 1)
          omega
        let wLast := (aXs[ws.toNat + (nres - 1)]'(by omega)) >>> bs.toNat
        have hm' : (array64 out (outXs'.set (nres - 1) wLast) ⋆ (array64 a aXs ⋆ R)) m := by
          have hm1 := hm
          simp only [hwsResSubToNat] at hm1
          rw [hresSubToNat, hbsMod] at hm1
          exact hm1
        let out2 := outXs'.set (nres - 1) wLast
        have hout2Len : out2.length = outXs.length := by simp [out2, hlenOut']
        have hout2Val : limbsVal (out2.take nres) =
            limbsVal (aXs.take na.toNat) >>> (64 * ws.toNat + bs.toNat) := by
          apply shr_limbs_eq_of_lim aXs out2 na.toNat ws.toNat bs.toNat nres hbs hwsLtNa rfl hna
            (by rw [hout2Len]; exact hnresLeOut)
          · dsimp [out2, wLast]
            rw [List.getElem_set_self]
          · intro j hj
            dsimp [out2]
            rw [List.getElem_set_ne (by omega)]
            exact hShrInv j (by omega)
        rw [← bv64_ofNat_toNat (na - ws), hsubEq]
        exact bn_trim_tail_wp hnresLt64 (by rw [hout2Len]; exact hnresLeOut) hm' hout2Val
          (fun hLenLe hTakeEq =>
            hQ out2 m hout2Len (by rw [hout2Len] at hLenLe; exact hLenLe)
              hTakeEq (sep_unpick2_3 hm'))

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
  have hs := subb64_nat x y bin
  dsimp only at hs
  have hx := x.isLt
  have hy := y.isLt
  have hbinNat : Bool.toNat bin = if bin then 1 else 0 := by cases bin <;> rfl
  have hboutEq : bout = decide (x.toNat < y.toNat + (if bin then 1 else 0)) := by
    rw [← hbinNat]
    cases bout with
    | true => exact (decide_eq_true (hb.mp rfl)).symm
    | false => exact (decide_eq_false (fun h => by have h' := hb.mpr h; cases h')).symm
  have hboutNat : Bool.toNat bout * 2 ^ 64 =
      if decide (x.toNat < y.toNat + (if bin then 1 else 0)) then 2 ^ 64 else 0 := by
    rw [hboutEq]
    cases decide (x.toNat < y.toNat + (if bin then 1 else 0)) <;> rfl
  have hd : (x - y - BitVec.ofNat 64 bin.toNat).toNat =
      (BitVec.ofNat 64 (2 ^ 64 + x.toNat - y.toNat - if bin then 1 else 0)).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show bin.toNat < 2 ^ 64 by cases bin <;> decide)]
    rw [Nat.add_mod_mod]
    cases bin
    · change (2 ^ 64 - 0 + (2 ^ 64 - y.toNat + x.toNat)) % 2 ^ 64 = (2 ^ 64 +
      x.toNat - y.toNat) % 2 ^ 64
      rw [show 2 ^ 64 - 0 + (2 ^ 64 - y.toNat + x.toNat) = 2 ^ 64 + (2 ^ 64 +
        x.toNat - y.toNat) by omega,
          Nat.add_mod_left]
    · change (2 ^ 64 - 1 + (2 ^ 64 - y.toNat + x.toNat)) % 2 ^ 64 = (2 ^ 64 +
      x.toNat - y.toNat - 1) % 2 ^ 64
      rw [show 2 ^ 64 - 1 + (2 ^ 64 - y.toNat + x.toNat) = 2 ^ 64 + (2 ^ 64 +
        x.toNat - y.toNat - 1) by omega,
          Nat.add_mod_left]
  rw [hd, hboutNat, hbinNat]
  exact hs

private theorem limbsVal_dvd_pow_of_low_zero (xs : List (BitVec 64)) (k n : Nat)
    (hk : k ≤ n) (hn : n ≤ xs.length) (hz : ∀ j (hj : j < k), xs[j]'(by omega) = 0#64) :
    2 ^ (64 * k) ∣ limbsVal (xs.take n) := by
  have hsplit : xs.take n = xs.take k ++ (xs.drop k).take (n - k) := by
    have h := List.take_add (l := xs) (i := k) (j := n - k)
    rwa [show k + (n - k) = n by omega] at h
  have hzero : limbsVal (xs.take k) = 0 := by
    apply limbsVal_zero_iff.mpr
    intro x hx
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨j, hj, rfl⟩
    rw [List.length_take_of_le (by omega)] at hj
    rw [List.getElem_take]
    exact hz j hj
  rw [hsplit, limbsVal_append, List.length_take_of_le (by omega), hzero, Nat.zero_add]
  exact Nat.dvd_mul_right _ _

private theorem nat_or_pow2_eq_add_of_pow_succ_dvd {m b : Nat} (hdvd : 2 ^ (b + 1) ∣ m) :
    m ||| (1 <<< b) = m + 2 ^ b := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  obtain ⟨q, hq⟩ := hdvd
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  rcases Nat.lt_trichotomy i b with hib | rfl | hib
  · have hmBit : m.testBit i = false := by
      have hsub : 2 ^ (i + 1) ∣ m :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) ⟨q, hq⟩
      obtain ⟨t, ht⟩ := hsub
      rw [Nat.testBit_eq_decide_div_mod_eq, ht,
          show 2 ^ (i + 1) = 2 ^ i * 2 by rw [Nat.pow_succ],
          Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
      simp
    have hpBit : (2 ^ b).testBit i = false := by
      have hsub : 2 ^ (i + 1) ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨t, ht⟩ := hsub
      rw [Nat.testBit_eq_decide_div_mod_eq, ht,
          show 2 ^ (i + 1) = 2 ^ i * 2 by rw [Nat.pow_succ],
          Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
      simp
    have hsBit : (m + 2 ^ b).testBit i = false := by
      have hsub1 : 2 ^ (i + 1) ∣ m :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) ⟨q, hq⟩
      have hsub2 : 2 ^ (i + 1) ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨t1, ht1⟩ := hsub1
      obtain ⟨t2, ht2⟩ := hsub2
      rw [Nat.testBit_eq_decide_div_mod_eq, ht1, ht2, ← Nat.mul_add,
          show 2 ^ (i + 1) = 2 ^ i * 2 by rw [Nat.pow_succ],
          Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
      simp
    simp [hmBit, hpBit, hsBit]
  · have hmBit : m.testBit i = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hq,
          show 2 ^ (i + 1) = 2 ^ i * 2 by rw [Nat.pow_succ],
          Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
      simp
    have hpBit : (2 ^ i).testBit i = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_self (Nat.pow_pos (by decide))]
      decide
    have hsBit : (m + 2 ^ i).testBit i = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hq,
          show 2 ^ (i + 1) = 2 ^ i * 2 by rw [Nat.pow_succ],
          Nat.mul_assoc, ← Nat.mul_add_one,
          Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
      simp
    simp [hmBit, hpBit, hsBit]
  · have hpBit : (2 ^ b).testBit i = false :=
      nat_testBit_false_of_lt (Nat.pow_lt_pow_right (by decide) hib)
    have hmModDvd : 2 ^ (b + 1) ∣ m % 2 ^ i := by
      have h1 : 2 ^ (b + 1) ∣ 2 ^ i := Nat.pow_dvd_pow 2 (by omega)
      exact (Nat.dvd_mod_iff h1).mpr ⟨q, hq⟩
    obtain ⟨t, ht⟩ := hmModDvd
    have htLt : t < 2 ^ (i - (b + 1)) := by
      have hmModLt := Nat.mod_lt m (Nat.pow_pos (by decide : 0 < 2)) (y := 2 ^ i)
      rw [ht, show (2 ^ i : Nat) = 2 ^ (b + 1) * 2 ^ (i - (b + 1)) by
        rw [← Nat.pow_add, show b + 1 + (i - (b + 1)) = i by omega]] at hmModLt
      exact Nat.lt_of_mul_lt_mul_left hmModLt
    have hremLt : m % 2 ^ i + 2 ^ b < 2 ^ i := by
      have hbLt : 2 ^ b < 2 ^ (b + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
      have hmul : 2 ^ (b + 1) * (t + 1) ≤ 2 ^ i := by
        rw [show (2 ^ i : Nat) = 2 ^ (b + 1) * 2 ^ (i - (b + 1)) by
          rw [← Nat.pow_add, show b + 1 + (i - (b + 1)) = i by omega]]
        exact Nat.mul_le_mul_left _ (by omega)
      rw [ht]; rw [Nat.mul_add, Nat.mul_one] at hmul; omega
    have hdivEq : (m + 2 ^ b) / 2 ^ i = m / 2 ^ i := by
      have hmDecomp := (Nat.div_add_mod m (2 ^ i)).symm
      conv => lhs; rw [hmDecomp, Nat.add_assoc,
        Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)),
        Nat.div_eq_of_lt hremLt, Nat.add_zero]
    rw [hpBit, Bool.or_false, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      hdivEq]

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

theorem bn_divmod_wp :
    ∀ xs m Q X, bnDivModSpec xs m Q X → Func.wp rtR1Env bn_divmod.body xs m Q X := by
  intro ⟨a, na, b, nb, q, r, ⟨⟩⟩ m Q X
    ⟨aXs, bXs, qXs, rXs, R, hnaPos, hnbPos, hna, hnb, hnq, hnr, hbLast, hm, hQ⟩
  let aVal := limbsVal (aXs.take na.toNat)
  let bVal := limbsVal (bXs.take nb.toNat)
  have hbLastNe : bXs[nb.toNat - 1]! ≠ 0#64 := hbLast
  have hbTakeNe : bXs.take nb.toNat ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp [List.length_take_of_le hnb] at hlen
    omega
  have hbTakeLast : (bXs.take nb.toNat).getLast hbTakeNe ≠ 0#64 := by
    rw [List.getLast_eq_getElem]
    have hlen : (bXs.take nb.toNat).length = nb.toNat := List.length_take_of_le hnb
    simp only [hlen, List.getElem_take]
    have hb0 : bXs[nb.toNat - 1]! = bXs[nb.toNat - 1]'(by omega) := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [← hb0]
    exact hbLastNe
  have hbPos : 0 < bVal := by
    have hpow := limbsVal_ge_pow_of_nonzero_last hbTakeNe hbTakeLast
    have hp : 0 < 2 ^ (64 * ((bXs.take nb.toNat).length - 1)) := Nat.pow_pos (by decide)
    exact Nat.lt_of_lt_of_le hp hpow
  have hbLtPow : bVal < 2 ^ (64 * nb.toNat) := by
    simpa [List.length_take_of_le hnb] using limbsVal_lt_pow (bXs.take nb.toNat)
  have haLtPow : aVal < 2 ^ (64 * na.toNat) := by
    simpa [List.length_take_of_le hna] using limbsVal_lt_pow (aXs.take na.toNat)
  dsimp only [Func.wp, bn_divmod, bn_divmod_body]
  change LeanQbe.T.wp _ _ _ _ _
  apply LeanQbe.T.wp_let_cmp _ _ _ _ _ _ rfl
  rw [LeanQbe.T.wp_jnz]
  refine ⟨fun hc => ?_, fun _ => ?_⟩
  · have hna0 : na.toNat = 0 := by
      change decide (na = 0#64) = true at hc
      have h' : na = 0#64 := of_decide_eq_true hc
      simp [h']
    omega
  apply LeanQbe.T.wp_let_cmp _ _ _ _ _ _ rfl
  rw [LeanQbe.T.wp_jnz]
  refine ⟨fun hc => ?_, fun _ => ?_⟩
  · have hnb0 : nb.toNat = 0 := by
      change decide (nb = 0#64) = true at hc
      have h' : nb = 0#64 := of_decide_eq_true hc
      simp [h']
    omega
  · refine LeanQbe.T.wp_join_group
      (fun _ mJ => (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs ⋆ array64 r rXs ⋆ R) mJ) ?_ ?_
    · intro Js ⟨⟩ mJ hmJ
      c0_steps
      apply bn_zero_call_wp hnq (sep_pick3_5 hmJ)
      intro q0 hmQ0
      have hmQ0' := sep_unpick3_5 hmQ0
      let qInit := List.replicate na.toNat 0#64 ++ qXs.drop na.toNat
      have hqInitLen : qInit.length = qXs.length := by
        dsimp [qInit]; simp; omega
      have hqInitZero : ∀ j (_hj : j < na.toNat), qInit[j]'(by omega) = 0#64 := by
        intro j _hj
        dsimp [qInit]
        rw [List.getElem_append_left (by simp [_hj]), List.getElem_replicate]
      c0_steps
      apply bn_zero_call_wp hnr (sep_pick4_5 hmQ0')
      intro r0 hmR0
      have hmR0' := sep_unpick4_5 hmR0
      let rInit := List.replicate nb.toNat 0#64 ++ rXs.drop nb.toNat
      have hrInitLen : rInit.length = rXs.length := by
        dsimp [rInit]; simp; omega
      have hrInitZero : limbsVal (rInit.take nb.toNat) = 0 := by
        dsimp [rInit]
        rw [List.take_append_of_le_length (by simp), List.take_replicate, Nat.min_self,
            limbsVal_replicate_zero]
      refine wp_loop_inv
        (fun (ys : Tup Val [i64]) mW =>
          ∃ (wNat : Nat) (qXs' rXs' : List (BitVec 64))
              (hwLe : wNat ≤ na.toNat) (hqLen : qXs'.length = qXs.length) (hrLen : rXs'.length =
                rXs.length),
            ys.1 = BitVec.ofNat 64 wNat ∧
            (∀ j (_hj : j < wNat), qXs'[j]'(by omega) = 0#64) ∧
            limbsVal (rXs'.take nb.toNat) < bVal ∧
            aVal >>> (64 * wNat) = (limbsVal (qXs'.take na.toNat) >>> (64 * wNat)) * bVal +
              limbsVal (rXs'.take nb.toNat) ∧
            (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXs' ⋆ R) mW)
        (fun ys _ => ys.1.toNat) ?_ ?_
      · intro Jw hJw
        c0_steps
        refine hJw (na, ()) r0 ⟨na.toNat, qInit, rInit, Nat.le_refl _, hqInitLen, hrInitLen,
          (bv64_ofNat_toNat na).symm, hqInitZero, by rw [hrInitZero]; exact hbPos, ?_, hmR0'⟩
        have hqInitVal : limbsVal (qInit.take na.toNat) = 0 := by
          dsimp [qInit]
          rw [List.take_append_of_le_length (by simp), List.take_replicate, Nat.min_self,
              limbsVal_replicate_zero]
        have haShift0 : aVal >>> (64 * na.toNat) = 0 := by
          rw [Nat.shiftRight_eq_div_pow]
          exact Nat.div_eq_of_lt haLtPow
        rw [hqInitVal, hrInitZero, Nat.zero_shiftRight, Nat.zero_mul, Nat.zero_add, haShift0]
      · intro Jw ⟨wBv, ⟨⟩⟩ mW
          ⟨wNat, qXs', rXs', hwLe, hqLen, hrLen, hwEq, hqZero, hrLt, hOuterInv, hmW⟩ hRecW
        dsimp only at hwEq; subst hwEq
        have hwLt64 : wNat < 2 ^ 64 := Nat.lt_of_le_of_lt hwLe na.isLt
        have hwToNat : (BitVec.ofNat 64 wNat).toNat = wNat := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwLt64]
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        · have hwPos : 0 < wNat := by
            have hc : 0 < (BitVec.ofNat 64 wNat).toNat := by assumption
            rwa [hwToNat] at hc
          let w' := wNat - 1
          have hw1ToNat : (BitVec.ofNat 64 wNat - (1 : BitVec 64)).toNat = w' := by
            rw [BitVec.toNat_sub_of_le
              (by rw [BitVec.le_def, hwToNat]; change 1 ≤ wNat; omega), hwToNat]
            rfl
          have hw1Eq : BitVec.ofNat 64 wNat - (1 : BitVec 64) = BitVec.ofNat 64 w' :=
            BitVec.eq_of_toNat_eq
              (by rw [hw1ToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
          have hqZeroW' : qXs'[w']'(by omega) = 0#64 := hqZero w' (by omega)
          have hqDvd : 2 ^ (64 * (w' + 1)) ∣ limbsVal (qXs'.take na.toNat) :=
            limbsVal_dvd_pow_of_low_zero qXs' (w' + 1) na.toNat (by omega) (by omega)
              (fun j hj => hqZero j (by omega))
          let aw := aXs[w']'(by omega)
          refine wp_loop_inv
            (fun (ys : Tup Val [i64, i64]) mK =>
              ∃ (qw : BitVec 64) (kNat : Nat) (rXs'' : List (BitVec 64))
                  (hkLe : kNat ≤ 64) (hrLen' : rXs''.length = rXs.length),
                ys.1 = qw ∧ ys.2.1 = BitVec.ofNat 64 kNat ∧
                2 ^ kNat ∣ qw.toNat ∧
                limbsVal (rXs''.take nb.toNat) < bVal ∧
                (let qVal := limbsVal (qXs'.take na.toNat) + 2 ^ (64 * w') * qw.toNat
                 aVal >>> (64 * w' + kNat) = (qVal >>> (64 * w' + kNat)) * bVal +
                   limbsVal (rXs''.take nb.toNat)) ∧
                (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXs'' ⋆ R) mK)
            (fun ys _ => ys.2.1.toNat) ?_ ?_
          · intro Jk hJk
            c0_steps
            refine hJk (0#64, 64#64, ()) mW ⟨0#64, 64, rXs', Nat.le_refl _, hrLen, rfl, rfl,
              Nat.dvd_zero _, hrLt, ?_, hmW⟩
            dsimp only
            rw [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
                show 64 * w' + 64 = 64 * wNat by omega]
            exact hOuterInv
          · intro Jk ⟨qw0, kBv, ⟨⟩⟩ mK
              ⟨qw0', kNat, rXs'', hkLe, hrLen', hqwEq, hkEq, hqwDvd, hrLtK, hInnerInv, hmK⟩ hRecK
            dsimp only at hqwEq hkEq; subst hqwEq; subst hkEq
            have hkLt64 : kNat < 2 ^ 64 := by omega
            have hkToNat : (BitVec.ofNat 64 kNat).toNat = kNat := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkLt64]
            change LeanQbe.T.wp _ _ _ _ _
            c0_steps
            · have hkPos : 0 < kNat := by
                have hc : 0 < (BitVec.ofNat 64 kNat).toNat := by assumption
                rwa [hkToNat] at hc
              let k' := kNat - 1
              have hk1ToNat : (BitVec.ofNat 64 kNat - (1 : BitVec 64)).toNat = k' := by
                rw [BitVec.toNat_sub_of_le
                  (by rw [BitVec.le_def, hkToNat]; change 1 ≤ kNat; omega), hkToNat]
                rfl
              have hk1Eq : BitVec.ofNat 64 kNat - (1 : BitVec 64) = BitVec.ofNat 64 k' :=
                BitVec.eq_of_toNat_eq
                  (by rw [hk1ToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
              have hkMod64 : (BitVec.ofNat 64 kNat - (1 : BitVec 64)).toNat % 64 = k' := by
                rw [hk1ToNat]; exact Nat.mod_eq_of_lt (by omega)
              let pos' := 64 * w' + k'
              let inBitBv := (aw >>> k') &&& 1#64
              let inBit := if aVal.testBit pos' then 1 else 0
              have hinBitEq : inBitBv.toNat = inBit := by
                have hawTest : aVal.testBit pos' = aw.toNat.testBit k' := by
                  dsimp [aVal, pos', aw]
                  have hdiv : (64 * w' + k') / 64 = w' := by omega
                  have hmod : (64 * w' + k') % 64 = k' := by omega
                  have hlt : w' < na.toNat := by omega
                  simp only [limbsVal_testBit, List.length_take_of_le hna, hdiv, hmod, hlt,
                      ↓reduceDIte, List.getElem_take]
                dsimp [inBitBv, inBit]
                rw [hawTest, Nat.and_one_is_mod, BitVec.toNat_ushiftRight,
                    Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
                by_cases hdiv1 : aw.toNat / 2 ^ k' % 2 = 1
                · simp [hdiv1]
                · have hdiv0 : aw.toNat / 2 ^ k' % 2 = 0 := by omega
                  simp [hdiv0]
              have hinBitLt2 : inBitBv.toNat < 2 := by
                rw [hinBitEq]; dsimp [inBit]; split <;> decide
              refine wp_loop_inv
                (fun (ys : Tup Val [i64, i64]) mS =>
                  ∃ (cbit : BitVec 64) (jNat : Nat) (rCur : List (BitVec 64))
                      (hjLe : jNat ≤ nb.toNat) (hrLenS : rCur.length = rXs.length),
                    ys.1 = cbit ∧ ys.2.1 = BitVec.ofNat 64 jNat ∧
                    cbit.toNat < 2 ∧
                    (∀ i (_hi1 : jNat ≤ i) (_hi2 : i < nb.toNat),
                      rCur[i]'(by omega) = rXs''[i]'(by omega)) ∧
                    limbsVal (rCur.take jNat) + 2 ^ (64 * jNat) * cbit.toNat =
                      2 * limbsVal ((rXs''.take nb.toNat).take jNat) + inBitBv.toNat ∧
                    (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rCur ⋆ R) mS)
                (fun ys _ => nb.toNat - ys.2.1.toNat) ?_ ?_
              · intro Js hJs
                c0_steps
                simp only [hw1ToNat, hkMod64]
                exact hJs (inBitBv, 0#64, ()) mK ⟨inBitBv, 0, rXs'', Nat.zero_le _, hrLen',
                  rfl, rfl, hinBitLt2, fun i _ _ => rfl, by simp, hmK⟩
              · intro Js ⟨cbit, jBv, ⟨⟩⟩ mS
                  ⟨cbit', jNat, rCur, hjLe, hrLenS, hcEq, hjEq, hcLt, hrRem, hShInv, hmS⟩ hRecS
                dsimp only at hcEq hjEq; subst hcEq; subst hjEq
                have hjLt64 : jNat < 2 ^ 64 := Nat.lt_of_le_of_lt hjLe nb.isLt
                have hjToNat : (BitVec.ofNat 64 jNat).toNat = jNat := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hjLt64]
                have hmodJ : jNat % 2 ^ 64 = jNat := Nat.mod_eq_of_lt hjLt64
                change LeanQbe.T.wp _ _ _ _ _
                c0_step; c0_step
                · c0_steps
                  have hjLtNb : jNat < nb.toNat := by
                    have hc : jNat % 2 ^ 64 < nb.toNat := by assumption
                    rwa [hmodJ] at hc
                  let rj := rXs''[jNat]'(by omega)
                  have hrjEq : rCur[jNat]'(by omega) = rj := hrRem jNat (le_refl _) hjLtNb
                  let rjNext := (rj <<< 1) ||| cbit
                  let cNext := rj >>> 63
                  have hstep := shl_step_nat rj 1#64 cbit (by decide) (by simpa using hcLt)
                  rw [show (64#64 - 1#64 : BitVec 64) = 63#64 from rfl] at hstep
                  have h1eq : (rj <<< (1#64 : BitVec 64)) = rj <<< 1 := rfl
                  have h63eq : (rj >>> (63#64 : BitVec 64)) = rj >>> 63 := rfl
                  have hcNextLt : cNext.toNat < 2 := by
                    dsimp only [cNext]; rw [← h63eq]; simpa using hstep.2
                  have hmS' : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆
                      array64 r (rCur.set jNat rjNext) ⋆ R) m := by
                    have hm1 := hm
                    simp only [hjToNat] at hm1
                    rw [hrjEq] at hm1
                    have hm2 : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆
                        array64 r (rCur.set jNat (cbit ||| rj <<< 1)) ⋆ R) m := sep_ac hm1
                    rw [BitVec.or_comm cbit (rj <<< 1)] at hm2
                    exact hm2
                  simp only [hjToNat, hrjEq]
                  rw [show (BitVec.ofNat 64 jNat + 1 : BitVec 64) = BitVec.ofNat 64 (jNat + 1) from
                    (BitVec.ofNat_add jNat 1).symm]
                  apply hRecS (cNext, BitVec.ofNat 64 (jNat + 1), ()) m
                  · show nb.toNat - (BitVec.ofNat 64 (jNat + 1)).toNat <
                        nb.toNat - (BitVec.ofNat 64 jNat).toNat
                    have hj1Lt64 : jNat + 1 < 2 ^ 64 := by omega
                    rw [hjToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj1Lt64]
                    omega
                  · refine ⟨cNext, jNat + 1, rCur.set jNat rjNext, hjLtNb, by simp [hrLenS],
                      rfl, rfl, hcNextLt, ?_, ?_, ?_⟩
                    · intro i hi1 hi2
                      rw [List.getElem_set_ne (by omega)]
                      exact hrRem i (by omega) hi2
                    · rw [limbsVal_take_set_succ rCur rjNext (by omega)]
                      have hrTakeNext := limbsVal_take_succ (xs := rXs''.take nb.toNat)
                        (i := jNat) (by rw [List.length_take_of_le (by omega)]; exact hjLtNb)
                      rw [List.getElem_take] at hrTakeNext
                      rw [hrTakeNext]
                      have hstep1 : rjNext.toNat + 2 ^ 64 * cNext.toNat = rj.toNat * 2 +
                        cbit.toNat := by
                        dsimp only [rjNext, cNext]
                        rw [← h1eq, ← h63eq]
                        simpa using hstep.1
                      have hpow : 2 ^ (64 * jNat) * 2 ^ 64 = 2 ^ (64 * (jNat + 1)) := by
                        rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
                      have hMul : 2 ^ (64 * jNat) * rjNext.toNat + 2 ^ (64 * (jNat +
                        1)) * cNext.toNat =
                          2 * (2 ^ (64 * jNat) * rj.toNat) + 2 ^ (64 * jNat) * cbit.toNat := by
                        have hz := congrArg (fun z => 2 ^ (64 * jNat) * z) hstep1
                        rw [Nat.mul_add, ← Nat.mul_assoc, hpow] at hz
                        rw [hz, Nat.mul_add, Nat.mul_comm rj.toNat 2, ← Nat.mul_assoc,
                            Nat.mul_comm (2 ^ (64 * jNat)) 2, Nat.mul_assoc 2]
                      dsimp only [rj] at hMul
                      rw [Nat.mul_add 2]
                      omega
                    · exact hmS'
                · have hjEqNb : jNat = nb.toNat := by
                    have hc : ¬ jNat % 2 ^ 64 < nb.toNat := by assumption
                    rw [hmodJ] at hc; omega
                  subst hjEqNb
                  rw [List.take_take, Nat.min_self] at hShInv
                  let rShVal := limbsVal (rCur.take nb.toNat)
                  let rValOld := limbsVal (rXs''.take nb.toNat)
                  let rPrime := 2 * rValOld + inBit
                  have hrShEq : rShVal + 2 ^ (64 * nb.toNat) * cbit.toNat = rPrime := by
                    dsimp [rShVal, rValOld, rPrime]
                    rw [← hinBitEq]
                    exact hShInv
                  have hrShLtPow : rShVal < 2 ^ (64 * nb.toNat) := by
                    dsimp [rShVal]
                    have h := limbsVal_lt_pow (rCur.take nb.toNat)
                    rwa [List.length_take_of_le (by omega)] at h
                  refine LeanQbe.T.wp_join_group
                    (fun (ge, ()) mG =>
                      ge = decide (bVal ≤ rPrime) ∧
                      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rCur ⋆ R) mG)
                    ?_ ?_
                  · intro Jge ⟨geB, ⟨⟩⟩ mG ⟨hgeEq, hmG⟩
                    subst hgeEq
                    let qVal := limbsVal (qXs'.take na.toNat) + 2 ^ (64 * w') * qw0.toNat
                    have hposEq : 64 * w' + kNat = pos' + 1 := by dsimp [pos', k']; omega
                    have hinvPos : aVal >>> (pos' + 1) = (qVal >>> (pos' + 1)) * bVal + rValOld :=
                      by
                      dsimp [qVal, rValOld]
                      rwa [← hposEq]
                    refine LeanQbe.T.wp_join_group
                      (fun (ys : Tup Val [i64]) mN =>
                        ∃ (qwN : BitVec 64) (rXsN : List (BitVec 64)) (hrLenN : rXsN.length =
                          rXs.length),
                          ys.1 = qwN ∧
                          2 ^ k' ∣ qwN.toNat ∧
                          limbsVal (rXsN.take nb.toNat) < bVal ∧
                          (let qValN := limbsVal (qXs'.take na.toNat) + 2 ^ (64 * w') * qwN.toNat
                           aVal >>> pos' = (qValN >>> pos') * bVal + limbsVal (rXsN.take nb.toNat))
                           ∧
                          (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXsN ⋆ R) mN)
                      ?_ ?_
                    · intro JkN ⟨qwNBv, ⟨⟩⟩ mN ⟨qwN, rXsN, hrLenN, hqwN, hqwNDvd, hrNLt, hInvN, hmN⟩
                      dsimp only at hqwN; subst qwNBv
                      c0_steps
                      rw [hk1Eq]
                      apply hRecK (qwN, BitVec.ofNat 64 k', ()) mN
                      · show (BitVec.ofNat 64 k').toNat < (BitVec.ofNat 64 kNat).toNat
                        rw [hkToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        omega
                      · exact ⟨qwN, k', rXsN, by omega, hrLenN, rfl, rfl, hqwNDvd, hrNLt, hInvN,
                        hmN⟩
                    · intro JkN hJkN
                      c0_steps
                      · have hgeTrue : bVal ≤ rPrime := by assumption
                        refine wp_loop_inv
                          (fun (ys : Tup Val [Ty.bool, i64]) mSub =>
                            ∃ (br : Bool) (jjNat : Nat) (rSub : List (BitVec 64))
                                (hjjLe : jjNat ≤ nb.toNat) (hrLenSub : rSub.length = rXs.length),
                              ys.1 = br ∧ ys.2.1 = BitVec.ofNat 64 jjNat ∧
                              limbsVal (rSub.take jjNat) + limbsVal (bXs.take jjNat) =
                                limbsVal (rCur.take jjNat) + (if br then 1 else 0) * 2 ^ (64 *
                                jjNat) ∧
                              (∀ i (_hi1 : jjNat ≤ i) (_hi2 : i < nb.toNat),
                                rSub[i]'(by omega) = rCur[i]'(by omega)) ∧
                              (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rSub ⋆
                                R) mSub)
                          (fun ys _ => nb.toNat - ys.2.1.toNat) ?_ ?_
                        · intro Jsub hJsub
                          c0_steps
                          exact hJsub (false, 0#64, ()) mG ⟨false, 0, rCur, Nat.zero_le _, hrLenS,
                            rfl, rfl, by simp, fun i _ _ => rfl, hmG⟩
                        · intro Jsub ⟨brBv, jjBv, ⟨⟩⟩ mSub
                            ⟨br, jjNat, rSub, hjjLe, hrLenSub, hbrEq, hjjEq, hSubInv, hrSubRem,
                              hmSub⟩ hRecSub
                          dsimp only at hbrEq hjjEq; subst brBv; subst hjjEq
                          have hjjLt64 : jjNat < 2 ^ 64 := Nat.lt_of_le_of_lt hjjLe nb.isLt
                          have hjjToNat : (BitVec.ofNat 64 jjNat).toNat = jjNat := by
                            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hjjLt64]
                          have hmodJJ : jjNat % 2 ^ 64 = jjNat := Nat.mod_eq_of_lt hjjLt64
                          change LeanQbe.T.wp _ _ _ _ _
                          c0_steps
                          · have hjjLtNb : jjNat < nb.toNat := by
                              have hc : (BitVec.ofNat 64 jjNat).toNat < nb.toNat := by assumption
                              rwa [hjjToNat] at hc
                            let rCurJ := rCur[jjNat]'(by omega)
                            have hrSubJ : rSub[jjNat]'(by omega) = rCurJ :=
                              hrSubRem jjNat (le_refl _) hjjLtNb
                            let bj := bXs[jjNat]'(by omega)
                            have subStep : ∀ {brNext : Bool} {d : BitVec 64} {m' : Mem 64},
                                (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆
                                    array64 r (rSub.set jjNat d) ⋆ R) m' →
                                  (d.toNat + bj.toNat + br.toNat =
                                    rCurJ.toNat + brNext.toNat * 2 ^ 64) →
                                  Jsub (brNext, BitVec.ofNat 64 jjNat + 1, ()) m' := by
                              intro brNext d m' hm' hdEq
                              rw [show (BitVec.ofNat 64 jjNat + 1 : BitVec 64) =
                                BitVec.ofNat 64 (jjNat + 1) from
                                (BitVec.ofNat_add jjNat 1).symm]
                              apply hRecSub (brNext, BitVec.ofNat 64 (jjNat + 1), ()) m'
                              · show nb.toNat - (BitVec.ofNat 64 (jjNat + 1)).toNat <
                                    nb.toNat - (BitVec.ofNat 64 jjNat).toNat
                                have h1lt : jjNat + 1 < 2 ^ 64 := by omega
                                rw [hjjToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
                                omega
                              · refine ⟨brNext, jjNat + 1, rSub.set jjNat d, hjjLtNb,
                                by simp [hrLenSub],
                                  rfl, rfl, ?_, ?_, hm'⟩
                                · rw [limbsVal_take_set_succ rSub d (by omega),
                                      limbsVal_take_succ (Nat.lt_of_lt_of_le hjjLtNb hnb),
                                      limbsVal_take_succ (by omega)]
                                  exact subb_limbs_step hSubInv hdEq
                                · intro i hi1 hi2
                                  rw [List.getElem_set_ne (by omega)]
                                  exact hrSubRem i (by omega) hi2
                            have hm' := hm
                            simp only [hjjToNat] at hm'
                            rw [hrSubJ] at hm'
                            have hSubGoal : ∀ (bRes : Bool),
                                bRes = decide (rCurJ.toNat < bj.toNat + br.toNat) →
                                Jsub (bRes, BitVec.ofNat 64 jjNat + 1, ()) m := by
                              intro bRes hbEq
                              cases bRes
                              · have hbrN : ¬ rCurJ.toNat < bj.toNat + br.toNat := by
                                  simpa using Eq.symm hbEq
                                apply subStep (brNext := false) (sep_ac hm')
                                exact bv64_subb_step_eq rCurJ bj br false (by simp [hbrN])
                              · have hbrN : rCurJ.toNat < bj.toNat + br.toNat := by
                                  simpa using Eq.symm hbEq
                                apply subStep (brNext := true) (sep_ac hm')
                                exact bv64_subb_step_eq rCurJ bj br true (by simp [hbrN])
                            refine hSubGoal _ (Bool.eq_iff_iff.mpr ?_)
                            have h1 : (rSub[(BitVec.ofNat 64 jjNat).toNat]'(by rw [hjjToNat];
                                                                               omega)) =
                                rCurJ := by
                              simp only [hjjToNat, hrSubJ, rCurJ]
                            have h2 : (bXs[(BitVec.ofNat 64 jjNat).toNat]'(by rw [hjjToNat];
                                                                              omega)) =
                                bj := by
                              simp only [hjjToNat, bj]
                            exact ⟨fun h => decide_eq_true
                              (by have h' := of_decide_eq_true h; rwa [h1, h2] at h'),
                                   fun h => decide_eq_true
                                     (by have h' := of_decide_eq_true h; rwa [h1, h2])⟩
                          · have hjjEqNb : jjNat = nb.toNat := by
                              have hc : ¬ (BitVec.ofNat 64 jjNat).toNat < nb.toNat := by assumption
                              rw [hjjToNat] at hc; omega
                            subst hjjEqNb
                            have hrSubLtPow : limbsVal (rSub.take nb.toNat) < 2 ^ (64 * nb.toNat) :=
                              by
                              have h := limbsVal_lt_pow (rSub.take nb.toNat)
                              rwa [List.length_take_of_le (by omega)] at h
                            have hsubClean : limbsVal (rSub.take nb.toNat) + bVal =
                                rShVal + (if br then 2 ^ (64 * nb.toNat) else 0) := by
                              dsimp [bVal, rShVal]
                              rw [hSubInv]
                              cases br <;> simp
                            have hrSubEq : limbsVal (rSub.take nb.toNat) = rPrime - bVal :=
                              divmod_post_sub_eq hrLtK hbLtPow (by dsimp [inBit]; split <;> decide)
                                hrShLtPow (by omega) hrShEq hgeTrue hrSubLtPow hsubClean
                            have hrSubLtB : limbsVal (rSub.take nb.toNat) < bVal := by
                              rw [hrSubEq]; dsimp [rPrime]
                              have hinLe1 : inBit ≤ 1 := by dsimp [inBit]; split <;> decide
                              omega
                            have hqProps := divmod_q_set_props hkPos hkLe hqDvd hqwDvd
                            dsimp only at hqProps
                            rcases hqProps with ⟨hqwNextDvd, hqNextOr, hqNextShr, _⟩
                            have hdm := divmod_bit_step hrLtK hinvPos
                            dsimp only at hdm
                            have hdecT : decide (bVal ≤ 2 * rValOld + inBit) = true :=
                              decide_eq_true hgeTrue
                            dsimp only [rValOld, inBit] at hdecT
                            simp only [hdecT, ↓reduceIte] at hdm
                            have hdm' := hdm hqNextShr
                            have hqwNextEq : (qw0 |||
                              (1 : BitVec 64) <<< ((BitVec.ofNat 64 kNat - 1).toNat % 64)) =
                                qw0 ||| (1#64 <<< k') := by
                              rw [hkMod64]; rfl
                            c0_steps
                            rw [hqwNextEq]
                            apply hJkN (qw0 ||| (1#64 <<< k'), ()) mSub
                              ⟨qw0 ||| (1#64 <<< k'), rSub, hrLenSub, rfl, hqwNextDvd, hrSubLtB, ?_,
                                hmSub⟩
                            dsimp only
                            rw [hqNextOr, hrSubEq]
                            exact hdm'.1
                      · have hgeFalse : ¬ (bVal ≤ rPrime) := by assumption
                        have hqProps := divmod_q_set_props hkPos hkLe hqDvd hqwDvd
                        dsimp only at hqProps
                        rcases hqProps with ⟨_, _, _, hqShr⟩
                        have hdm := divmod_bit_step hrLtK hinvPos
                        dsimp only at hdm
                        have hdecF : decide (bVal ≤ 2 * rValOld + inBit) = false :=
                          decide_eq_false hgeFalse
                        dsimp only [rValOld, inBit] at hdecF
                        simp only [hdecF, Bool.false_eq_true, ↓reduceIte] at hdm
                        have hdm' := hdm hqShr
                        have hqwDvdNext : 2 ^ k' ∣ qw0.toNat :=
                          Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hqwDvd
                        have hrCurLtB : limbsVal (rCur.take nb.toNat) < bVal := by
                          have hc0 : cbit.toNat = 0 := by
                            by_cases hz : cbit.toNat = 0
                            · exact hz
                            · have hc1 : cbit.toNat = 1 := by omega
                              rw [hc1, Nat.mul_one] at hrShEq
                              omega
                          rw [hc0, Nat.mul_zero, Nat.add_zero] at hrShEq
                          dsimp [rShVal] at hrShEq
                          rw [hrShEq]
                          omega
                        c0_steps
                        refine hJkN (qw0, ()) mG
                          ⟨qw0, rCur, hrLenS, rfl, hqwDvdNext, hrCurLtB, ?_, hmG⟩
                        dsimp only
                        rw [show rShVal = limbsVal (rCur.take nb.toNat) from rfl] at hrShEq
                        have hcurValEq : limbsVal (rCur.take nb.toNat) = rPrime := by
                          have hc0 : cbit.toNat = 0 := by
                            by_cases hz : cbit.toNat = 0
                            · exact hz
                            · have hc1 : cbit.toNat = 1 := by omega
                              rw [hc1, Nat.mul_one] at hrShEq
                              omega
                          rw [hc0, Nat.mul_zero, Nat.add_zero] at hrShEq
                          exact hrShEq
                        rw [hcurValEq]
                        exact hdm'.1
                  · intro Jge hJge
                    c0_steps
                    · have hcbitNe0 : cbit ≠ 0#64 := by assumption
                      have hcbit1 : cbit.toNat = 1 := by
                        have hnz : cbit.toNat ≠ 0 := fun h => hcbitNe0 (BitVec.eq_of_toNat_eq h)
                        omega
                      have hgeTrue : bVal ≤ rPrime := by
                        rw [← hrShEq, hcbit1, Nat.mul_one]; omega
                      exact hJge (true, ()) mS ⟨(decide_eq_true hgeTrue).symm, hmS⟩
                    · have hcbit0 : cbit = 0#64 := by assumption
                      have hcbitNat0 : cbit.toNat = 0 := by simp [hcbit0]
                      rw [hcbitNat0, Nat.mul_zero, Nat.add_zero] at hrShEq
                      have hrShEq' : rShVal = rPrime := hrShEq
                      have hmCmp : (array64 r rCur ⋆ array64 b bXs ⋆
                          (array64 a aXs ⋆ array64 q qXs' ⋆ R)) mS := sep_ac hmS
                      have hrCurLen : nb.toNat ≤ rCur.length := by omega
                      apply bn_cmp_fixed_call_wp hrCurLen hnb hmCmp
                      c0_steps
                      · have hcmpTrue : bVal ≤ rPrime := by
                          have hc : (0#64).sle (cmpResult64 (limbsVal (rCur.take nb.toNat))
                              (limbsVal (bXs.take nb.toNat))) = true := by assumption
                          rw [(cmpResult64_sge0_iff _ _).1] at hc
                          change bVal ≤ rShVal at hc
                          rwa [hrShEq'] at hc
                        exact hJge (true, ()) mS ⟨(decide_eq_true hcmpTrue).symm, hmS⟩
                      · have hcmpFalse : ¬ (bVal ≤ rPrime) := by
                          have hc : ¬ (0#64).sle (cmpResult64 (limbsVal (rCur.take nb.toNat))
                              (limbsVal (bXs.take nb.toNat))) = true :=
                            Bool.eq_false_iff.mp (by assumption)
                          rw [(cmpResult64_sge0_iff _ _).1] at hc
                          change ¬ bVal ≤ rShVal at hc
                          rwa [hrShEq'] at hc
                        exact hJge (false, ()) mS ⟨(decide_eq_false hcmpFalse).symm, hmS⟩
            · have hk0 : kNat = 0 := by
                have hc : ¬ 0 < (BitVec.ofNat 64 kNat).toNat := by assumption
                rw [hkToNat] at hc; omega
              subst hk0
              c0_steps
              have hmW' : (array64 a aXs ⋆ array64 b bXs ⋆ array64 q (qXs'.set w' qw0) ⋆
                  array64 r rXs'' ⋆ R) m := by
                have hm1 := hm
                rw [hw1ToNat] at hm1
                exact sep_ac hm1
              rw [hw1Eq]
              apply hRecW (BitVec.ofNat 64 w', ()) m
              · show (BitVec.ofNat 64 w').toNat < (BitVec.ofNat 64 wNat).toNat
                rw [hwToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                omega
              · refine ⟨w', qXs'.set w' qw0, rXs'', by omega, by simp [hqLen], hrLen', rfl, ?_,
                hrLtK, ?_, hmW'⟩
                · intro j hj
                  rw [List.getElem_set_ne (by omega)]
                  exact hqZero j (by omega)
                · have hqTakeSet : limbsVal ((qXs'.set w' qw0).take na.toNat) =
                      limbsVal (qXs'.take na.toNat) + 2 ^ (64 * w') * qw0.toNat := by
                    have h := limbsVal_take_set_of_lt qXs' qw0 (p := w') (M := na.toNat)
                      (by omega) (by omega)
                    rw [hqZeroW'] at h
                    simpa [Nat.mul_zero, Nat.add_zero] using h
                  dsimp only at hInnerInv
                  rw [← hqTakeSet, show 64 * w' + 0 = 64 * w' from Nat.add_zero _] at hInnerInv
                  exact hInnerInv
        · have hw0 : wNat = 0 := by
            have hc : ¬ 0 < (BitVec.ofNat 64 wNat).toNat := by assumption
            rw [hwToNat] at hc; omega
          subst hw0
          rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftRight_zero] at hOuterInv
          have hqDiv : limbsVal (qXs'.take na.toNat) = aVal / bVal := by
            rw [hOuterInv, Nat.add_comm (limbsVal (qXs'.take na.toNat) * bVal),
                Nat.add_mul_div_right _ _ hbPos, Nat.div_eq_of_lt hrLt, Nat.zero_add]
          have hrMod : limbsVal (rXs'.take nb.toNat) = aVal % bVal := by
            rw [hOuterInv, Nat.add_comm (limbsVal (qXs'.take na.toNat) * bVal),
                Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrLt]
          exact hQ qXs' rXs' mW hqLen hrLen hqDiv hrMod hmW
    · intro Js hJs
      c0_steps
      all_goals first
        | exact hJs () m hm
        | (have hna1 : na.toNat = 1 := by
             have hc : na = 1#64 := by assumption
             simp [hc]
           have hnb1 : nb.toNat = 1 := by
             have hc : nb = 1#64 := by assumption
             simp [hc]
           have hb0Ne : bXs[0]'(by omega) ≠ 0#64 := by
             have hb0 := hbLast
             rw [hnb1, Nat.sub_self, List.getElem!_eq_getElem?_getD,
                 List.getElem?_eq_getElem (by omega)] at hb0
             exact hb0
           first
             | exact absurd (by assumption : bXs[0]'(by omega) = 0#64) hb0Ne
             | exact hb0Ne
             | (let q1 := qXs.set 0 ((aXs[0]'(by omega)) / (bXs[0]'(by omega)))
                let r1 := rXs.set 0 ((aXs[0]'(by omega)) % (bXs[0]'(by omega)))
                have hTake1 : ∀ {xs : List (BitVec 64)} (h : 0 < xs.length),
                    limbsVal (xs.take 1) = xs[0].toNat := fun {xs} h => by
                  simp [list_take_succ_append h]
                have haVal1 : aVal = (aXs[0]'(by omega)).toNat := by
                  dsimp [aVal]; rw [hna1, hTake1 (by omega)]
                have hbVal1 : bVal = (bXs[0]'(by omega)).toNat := by
                  dsimp [bVal]; rw [hnb1, hTake1 (by omega)]
                have hq1Val : limbsVal (q1.take na.toNat) = aVal / bVal := by
                  dsimp [q1]
                  rw [hna1, hTake1 (by simp; omega), List.getElem_set_self,
                      BitVec.toNat_udiv, haVal1, hbVal1]
                have hr1Val : limbsVal (r1.take nb.toNat) = aVal % bVal := by
                  dsimp [r1]
                  rw [hnb1, hTake1 (by simp; omega), List.getElem_set_self,
                      BitVec.toNat_umod, haVal1, hbVal1]
                exact hQ q1 r1 m (by simp [q1]) (by simp [r1]) hq1Val hr1Val (sep_ac hm)))

end LeanQbe.T.LeanLCNF
