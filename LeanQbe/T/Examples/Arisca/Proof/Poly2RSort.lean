/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2RPass2
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA `ar_build_R` Pass 1, Pass 3 Sort, & Pass 4 Combine WP (`Arisca.Proof.Poly2R`)

`XPost`-polymorphic `Mem 64` WP proofs completing `ar_build_R`:
- `buildR_combine_wp` (Pass 4 sorted deduplication & coefficient combining)
- `buildR_merge_phase` & `buildR_sort_wp` (Pass 3 index init + bottom-up `w = 1` merge sort)
- `buildR_pass1_f_wp` & `buildR_pass1_wp` (Pass 1 flip-count scan, fast path, and Pass 2..4 glue).
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

/-! ## 1. Pass 3 & Pass 4 AST Extractors & Pure Lemmas -/

public section

/-- Extract Pass 4 (`k2 = 0, i = 0; while (i < n) ...`) expression from `buildRPass2AfterExpr`. -/
@[expose] def buildRPass4Expr (cx aPtr bPtr : Val i64) (v off cnt : Val i32)
    (fv_b any : Val .bool) (bt bw : Val i64) (nFinal : Val i32) : Expr Val Cont [.bool] :=
  match buildRPass2AfterExpr cx 0#64 0#64 v off cnt fv_b any bt bw nFinal with
  | @Expr.group _ _ _ [[.bits 32]] bs1 _ =>
    match bs1 (fun _ _ => False, ()) with
    | .cons b1 _ => match b1 (0#32, ()) with
      | @Expr.let_ _ _ _ [.bool] _ c1 => match c1 (false, ()) with
        | .jnz _ _ eW => match eW with
          | @Expr.group _ _ _ [[.bits 64, .bits 64, .bits 64]] bsW _ =>
            match bsW (fun _ _ => False, ()) with
            | .cons bW _ => match bW (aPtr, bPtr, 0#64, ()) with
              | @Expr.let_ _ _ _ [.bits 64] _ _ =>
                match (bW (aPtr, bPtr, 0#64, ())) with
                | @Expr.let_ _ _ _ [.bits 64] _ w0 => match w0 (0#64, ()) with
                  | @Expr.let_ _ _ _ [.bool] _ cW => match cW (false, ()) with
                    | .jnz _ _ eP4 => eP4
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

private theorem bv64_zext32 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans x.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

private theorem wp_load_arr32_idx0 {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 32)} {i : BitVec 32} {R : Mem 64 → Prop}
    (ha : a.val = base + BitVec.setWidth 64 i * 4)
    (hi : i.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : wp Γ Q X (k (xs[i.toNat])) m) : wp Γ Q X (.load i32 a k) m :=
  wp_load_arr32_idx (off := 0) (by simpa using ha) (by simpa using hi) hm (by simpa using hk)

private theorem merge_w_bounds_r {n : BitVec 32} {w : BitVec 64}
    (hw_lo : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat) (hn32 : n.toNat + 16 < 2 ^ 32) :
    2 * w.toNat < 2 ^ 64 ∧ (w * 2#64).toNat = 2 * w.toNat ∧
      (w * 2#64).toNat ≤ 2 * max 1 n.toNat := by
  have hlt : 2 * w.toNat < 2 ^ 64 := by omega
  have h1 : (w * 2#64).toNat = 2 * w.toNat := by
    rw [BitVec.toNat_mul, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mul_comm, Nat.mod_eq_of_lt hlt]
  exact ⟨hlt, h1, by omega⟩

private theorem merge_lo2w_r {lo w : BitVec 64} (h64b : lo.toNat + 2 * w.toNat < 2 ^ 64) :
    (lo + 2#64 * w).toNat = lo.toNat + 2 * w.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, show (2#64 : BitVec 64).toNat = 2 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * w.toNat < 2 ^ 64), Nat.mod_eq_of_lt h64b]

private def MergeWInvR (s : ArCtxState) (ix ix2 : List (BitVec 32)) (n : Nat)
    (Rmerge : Mem 64 → Prop) (wrem : Nat) (xs : Tup Val [i64, i64, i64])
    (mW : Mem 64) : Prop :=
  let (aPtr, bPtr, w, _) := xs
  ∃ aArr bArr : List (BitVec 32),
    ((aPtr = s.ix ∧ bPtr = s.ix2 ∧ aArr.length = ix.length ∧ bArr.length = ix2.length) ∨
     (aPtr = s.ix2 ∧ bPtr = s.ix ∧ aArr.length = ix2.length ∧ bArr.length = ix.length)) ∧
    PermN aArr n ∧ 1 ≤ w.toNat ∧ w.toNat ≤ 2 * max 1 n ∧ wrem = 2 * max 1 n - w.toNat ∧
    (array (t := i32) aPtr aArr ⋆ array (t := i32) bPtr bArr ⋆ Rmerge) mW

private def MergeLoInvR (aPtr bPtr : BitVec 64) (aArr bArr : List (BitVec 32)) (n : Nat)
    (w : BitVec 64) (Rmerge : Mem 64 → Prop) (lorem : Nat) (xs : Tup Val [i64])
    (mL : Mem 64) : Prop :=
  let (lo, _) := xs
  ∃ bCur : List (BitVec 32),
    bCur.length = bArr.length ∧ lo.toNat ≤ n + 2 * w.toNat ∧
    lorem = (n + 2 * w.toNat) - lo.toNat ∧
    ((List.range (min lo.toNat n)).map (fun t => (bCur.getD t 0#32).toNat)).Perm
      ((List.range (min lo.toNat n)).map (fun t => (aArr.getD t 0#32).toNat)) ∧
    (array (t := i32) aPtr aArr ⋆ array (t := i32) bPtr bCur ⋆ Rmerge) mL

private def MergeChunkLoopInvR (aPtr bPtr : BitVec 64) (aArr bArr bCur : List (BitVec 32))
    (lo mid hi : Nat) (Rmerge : Mem 64 → Prop) (pqrem : Nat) (xs : Tup Val [i32, i32, i32])
    (mM : Mem 64) : Prop :=
  let (p, q, o, _) := xs
  pqrem = (hi - lo) - (o.toNat - lo) ∧
  MergeChunkInv aPtr bPtr aArr bArr bCur lo mid hi p.toNat q.toNat o.toNat Rmerge mM

private def MergePInvR (aPtr bPtr : BitVec 64) (aArr bArr bCur : List (BitVec 32))
    (lo mid hi q : Nat) (Rmerge : Mem 64 → Prop) (prem : Nat) (xs : Tup Val [i32, i32])
    (mP : Mem 64) : Prop :=
  let (p1, o1, _) := xs
  prem = mid - p1.toNat ∧
  MergeChunkInv aPtr bPtr aArr bArr bCur lo mid hi p1.toNat q o1.toNat Rmerge mP

private def MergeQInvR (aPtr bPtr : BitVec 64) (aArr bArr bCur : List (BitVec 32))
    (lo mid hi : Nat) (Rmerge : Mem 64 → Prop) (qrem : Nat) (xs : Tup Val [i32, i32])
    (mQ : Mem 64) : Prop :=
  let (q1, o2, _) := xs
  qrem = hi - q1.toNat ∧
  MergeChunkInv aPtr bPtr aArr bArr bCur lo mid hi mid q1.toNat o2.toNat Rmerge mQ

/-- Word sum of monomial slices `aArr[lo .. lo + len - 1]` inside `rpool` via `rm`. -/
def tailRWords (rpool rm aArr : List (BitVec 32)) (lo len : Nat) : Nat :=
  (List.range len).foldl (fun acc t =>
    acc + ((rpool.getD (rm.getD (aArr.getD (lo + t) 0#32).toNat 0#32).toNat 0#32).toNat + 1)) 0

private theorem tailRWords_zero (rpool rm aArr : List (BitVec 32)) (lo : Nat) :
    tailRWords rpool rm aArr lo 0 = 0 := rfl

private theorem tailRWords_succ (rpool rm aArr : List (BitVec 32)) (lo len : Nat) :
    tailRWords rpool rm aArr lo (len + 1) =
      tailRWords rpool rm aArr lo len +
        ((rpool.getD (rm.getD (aArr.getD (lo + len) 0#32).toNat 0#32).toNat 0#32).toNat + 1) := by
  simp [tailRWords, List.range_succ, List.foldl_append]

private theorem tailRWords_add (rpool rm aArr : List (BitVec 32)) (lo a b : Nat) :
    tailRWords rpool rm aArr lo (a + b) =
      tailRWords rpool rm aArr lo a + tailRWords rpool rm aArr (lo + a) b := by
  induction b with
  | zero => simp [tailRWords_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, tailRWords_succ, tailRWords_succ, ih, Nat.add_assoc,
      show lo + (a + b) = lo + a + b by omega]

private theorem tailRWords_split_one (rpool rm aArr : List (BitVec 32)) (lo len : Nat) :
    tailRWords rpool rm aArr lo (len + 1) =
      ((rpool.getD (rm.getD (aArr.getD lo 0#32).toNat 0#32).toNat 0#32).toNat + 1) +
        tailRWords rpool rm aArr (lo + 1) len := by
  have h := tailRWords_add rpool rm aArr lo 1 len
  rw [Nat.add_comm 1 len] at h
  rw [h, tailRWords_succ, tailRWords_zero, Nat.zero_add]
  simp only [Nat.add_zero]

private theorem foldl_add_nat_init {α : Type} (f : α → Nat) :
    ∀ (l : List α) (init : Nat),
      l.foldl (fun acc x => acc + f x) init = init + l.foldl (fun acc x => acc + f x) 0
  | [], init => by simp
  | x :: xs, init => by
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_nat_init f xs (init + f x), foldl_add_nat_init f xs (f x), Nat.add_assoc]

private theorem foldl_add_nat_perm {α : Type} (f : α → Nat) {l1 l2 : List α} (hp : l1.Perm l2) :
    l1.foldl (fun acc x => acc + f x) 0 = l2.foldl (fun acc x => acc + f x) 0 := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_nat_init, foldl_add_nat_init f _ (f x), ih]
  | swap x y l =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_nat_init, foldl_add_nat_init f l (f x + f y), Nat.add_comm (f x) (f y)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem tailRWords_init_perm {rpool rm aArr : List (BitVec 32)} {n : Nat}
    (hp : PermN aArr n) : tailRWords rpool rm aArr 0 n = monoTotalWords rpool rm n := by
  have h1 : tailRWords rpool rm aArr 0 n =
      ((List.range n).map (fun k => (aArr.getD k 0#32).toNat)).foldl (fun acc idx =>
        acc + ((rpool.getD (rm.getD idx 0#32).toNat 0#32).toNat + 1)) 0 := by
    simp [tailRWords, List.foldl_map]
  have h2 : monoTotalWords rpool rm n =
      (List.range n).foldl (fun acc idx =>
        acc + ((rpool.getD (rm.getD idx 0#32).toNat 0#32).toNat + 1)) 0 := rfl
  rw [h1, h2]
  exact foldl_add_nat_perm _ hp

private def CombineRAllInv (nOut : Nat) (Valid : (Nat → Bool) → Prop)
    (rpool rm : List (BitVec 32)) (rl rh : List (BitVec 64)) (aArr : List (BitVec 32))
    (n rcap : Nat) (rm2Ptr rl2Ptr rh2Ptr : BitVec 64)
    (rm20 : List (BitVec 32)) (rl20 rh20 : List (BitVec 64))
    (Rcmb : Mem 64 → Prop) (irem : Nat) (xs : Tup Val [i32, i32]) (mC : Mem 64) : Prop :=
  let (i, k2, _) := xs
  ∃ (rm2C : List (BitVec 32)) (rl2C rh2C : List (BitVec 64)),
    rm2C.length = rm20.length ∧ rl2C.length = rl20.length ∧ rh2C.length = rh20.length ∧
    rcap ≤ rm2C.length ∧ rcap ≤ rl2C.length ∧ rcap ≤ rh2C.length ∧
    k2.toNat ≤ i.toNat ∧ i.toNat ≤ n ∧ irem = n - i.toNat ∧
    (∀ p < k2.toNat, ∃ idx < n, rm2C.getD p 0#32 = rm.getD idx 0#32) ∧
    monoTotalWords rpool rm2C k2.toNat + tailRWords rpool rm aArr i.toNat (n - i.toNat) ≤
      monoTotalWords rpool rm n ∧
    (∀ σ, Valid σ →
      polyEval nOut σ rpool rm2C rl2C rh2C k2.toNat +
        polyEvalIdxOf nOut σ rpool rm rl rh aArr i.toNat (n - i.toNat) =
        polyEval nOut σ rpool rm rl rh n) ∧
    (array (t := i32) rm2Ptr rm2C ⋆ array64 rl2Ptr rl2C ⋆ array64 rh2Ptr rh2C ⋆ Rcmb) mC

private def CombineRJInv (nOut n i : Nat) (Valid : (Nat → Bool) → Prop)
    (rpool rm : List (BitVec 32)) (rl rh : List (BitVec 64)) (aArr : List (BitVec 32))
    (h0 : BitVec 32) (mC : Mem 64) (jrem : Nat) (xs : Tup Val [i64, i64, i32])
    (mJ : Mem 64) : Prop :=
  let (l, h, j, _) := xs
  mJ = mC ∧ i + 1 ≤ j.toNat ∧ j.toNat ≤ n ∧ jrem = n - j.toNat ∧
  ((rpool.getD (rm.getD h0.toNat 0#32).toNat 0#32).toNat + 1) +
    tailRWords rpool rm aArr j.toNat (n - j.toNat) ≤
    tailRWords rpool rm aArr i (n - i) ∧
  (∀ σ, Valid σ →
    (if monoValL σ (symListAt rpool (rm.getD h0.toNat 0#32).toNat)
      then coeff128 nOut l h else 0#nOut) +
      polyEvalIdxOf nOut σ rpool rm rl rh aArr j.toNat (n - j.toNat) =
      polyEvalIdxOf nOut σ rpool rm rl rh aArr i (n - i))

private theorem combineR_cadd_step {nOut n i : Nat} {Valid : (Nat → Bool) → Prop}
    {rpool rm : List (BitVec 32)} {rl rh : List (BitVec 64)} {aArr : List (BitVec 32)}
    {h0 j : BitVec 32} {l h nl nh : BitVec 64} {mC : Mem 64}
    (hj_lt : j.toNat < n) (hj_lo : i + 1 ≤ j.toNat) (hjp1 : (j + 1#32).toNat = j.toNat + 1)
    (hsym : symListAt rpool (rm.getD (aArr.getD j.toNat 0#32).toNat 0#32).toNat =
      symListAt rpool (rm.getD h0.toNat 0#32).toNat)
    (hcadd : coeff128 nOut nl nh = coeff128 nOut l h +
      coeff128 nOut (rl.getD (aArr.getD j.toNat 0#32).toNat 0#64)
        (rh.getD (aArr.getD j.toNat 0#32).toNat 0#64))
    (hwJ : ((rpool.getD (rm.getD h0.toNat 0#32).toNat 0#32).toNat + 1) +
      tailRWords rpool rm aArr j.toNat (n - j.toNat) ≤ tailRWords rpool rm aArr i (n - i))
    (hsumJ : ∀ σ, Valid σ →
      (if monoValL σ (symListAt rpool (rm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
        polyEvalIdxOf nOut σ rpool rm rl rh aArr j.toNat (n - j.toNat) =
        polyEvalIdxOf nOut σ rpool rm rl rh aArr i (n - i)) :
    CombineRJInv nOut n i Valid rpool rm rl rh aArr h0 mC (n - (j + 1#32).toNat)
      (nl, nh, j + 1#32, ⟨⟩) mC := by
  refine ⟨rfl, by omega, by omega, rfl, ?_, fun σ hσ => ?_⟩
  · rw [hjp1]
    have hsp : n - j.toNat = (n - (j.toNat + 1)) + 1 := by omega
    rw [hsp, tailRWords_split_one] at hwJ
    omega
  · rw [hjp1]
    have hsp : n - j.toNat = (n - (j.toNat + 1)) + 1 := by omega
    have hcur := hsumJ σ hσ
    rw [hsp, polyEvalIdxOf_split_one] at hcur
    rw [← hcur]; clear hcur
    simp only [termEval, hsym]
    cases monoValL σ (symListAt rpool (rm.getD h0.toNat 0#32).toNat)
    · simp [BitVec.zero_add]
    · simp only [↓reduceIte, hcadd]; rw [BitVec.add_assoc]

/-! ## 2. Pass 4 WP: `buildR_combine_wp` -/

private theorem array32_sep_ne {p q : BitVec 64} {xs ys : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64} (hx : 0 < xs.length) (hy : 0 < ys.length)
    (hm : (array (t := i32) p xs ⋆ array (t := i32) q ys ⋆ R) m) : p ≠ q := by
  intro hpq; subst hpq
  rcases xs with _ | ⟨x, xs'⟩; · simp at hx
  rcases ys with _ | ⟨y, ys'⟩; · simp at hy
  rw [array_cons, array_cons] at hm
  let Rrest := array (t := i32) (p + BitVec.ofNat 64 i32.bytes) xs' ⋆
    array (t := i32) (p + BitVec.ofNat 64 i32.bytes) ys' ⋆ R
  have hm' : (cell (t := i32) p x ⋆ (cell (t := i32) p y ⋆ Rrest)) m :=
    sep_cast hm (by dsimp [Rrest]; ac_rfl)
  obtain ⟨_, hst⟩ := store_cell (t := i32) (a := p) (v0 := x) (R := cell (t := i32) p y ⋆ Rrest)
    (y + 1#32) (by decide) hm'
  have h1 := loadVal_cell (t := i32) (a := p) (v := y + 1#32)
    (R := cell (t := i32) p y ⋆ Rrest) (by decide) hst
  have hst' : (cell (t := i32) p y ⋆ (cell (t := i32) p (y + 1#32) ⋆ Rrest))
      (storeMem m i32 p (y + 1#32)) := sep_cast hst (by ac_rfl)
  have h2 := loadVal_cell (t := i32) (a := p) (v := y)
    (R := cell (t := i32) p (y + 1#32) ⋆ Rrest) (by decide) hst'
  rw [h1] at h2; injection h2 with heq; bv_omega

theorem buildR_combine_wp (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx aPtr bPtr : BitVec 64} {v off cnt : BitVec 32} {fv_b any : Bool}
    {bt bw : BitVec 64} {n : BitVec 32}
    {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rm : List (BitVec 32)} {rl rh : List (BitVec 64)}
    {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {rpool aArr bArr ix ix2 : List (BitVec 32)}
    {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hn_rcap : n.toNat ≤ s.rcap.toNat) (hn_qcap : n.toNat ≤ s.qcap.toNat)
    (hqcap_lo : 1 ≤ s.qcap.toNat) (hqcap_hi : s.qcap.toNat + 16 < 2 ^ 32)
    (_hrpcap_32 : s.rpcap.toNat < 2 ^ 32)
    (hrm_len : s.rcap.toNat ≤ rm.length) (hrl_len : s.rcap.toNat ≤ rl.length)
    (hrh_len : s.rcap.toNat ≤ rh.length) (hrm2_len : s.rcap.toNat ≤ rm2.length)
    (hrl2_len : s.rcap.toNat ≤ rl2.length) (hrh2_len : s.rcap.toNat ≤ rh2.length)
    (_hrpool_len : s.rpcap.toNat ≤ rpool.length)
    (hix_eq : ix.length = ix2.length)
    (hptrs : (aPtr = s.ix ∧ bPtr = s.ix2 ∧ aArr.length = ix.length ∧ bArr.length = ix2.length) ∨
      (aPtr = s.ix2 ∧ bPtr = s.ix ∧ aArr.length = ix2.length ∧ bArr.length = ix.length))
    (hqcap_a : s.qcap.toNat ≤ aArr.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hPerm : PermN aArr n.toNat)
    (hSl : ∀ r < n.toNat, MonoSliceOk rpool (rm.getD r 0#32).toNat rpool.length ∧
      (rpool.getD (rm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : ∀ r < n.toNat, MonoSorted rpool (rm.getD r 0#32).toNat)
    (hWords : monoTotalWords rpool rm n.toNat ≤ s.rpcap.toNat)
    (hSyms : SymsBound rpool rm n.toNat s.n_nets.toNat)
    (hEval : ∀ σ, Valid σ →
      polyEval s.modW σ rpool rm rl rh n.toNat =
        bv s.modW
          (σ (if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)))
    (hm : (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
      array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
      array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆ array64 s.rh2 rh2 ⋆
      array (t := i32) s.rpool rpool ⋆ array (t := i32) aPtr aArr ⋆
      array (t := i32) bPtr bArr ⋆ u32PadTail s.rm rm.length ⋆
      u32PadTail s.rm2 rm2.length ⋆ u32PadTail s.rpool rpool.length ⋆ R) m)
    (hQ : ∀ (k2 : BitVec 32) (s' : ArCtxState)
        (rm2' : List (BitVec 32)) (rl2' rh2' : List (BitVec 64)) (m' : Mem 64),
      s' = { s with
        cur_rm := s.rm2, cur_rl := s.rl2, cur_rh := s.rh2,
        cur_rp := s.rpool, cur_nr := k2 } →
      k2.toNat ≤ s.rcap.toNat → rm2'.length = rm2.length → rl2'.length = rl2.length →
      rh2'.length = rh2.length →
      (∀ σ, Valid σ → CurRRep s.modW σ k2.toNat
        (if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)
        rm2' rl2' rh2' rpool) →
      (∀ r < k2.toNat, MonoSliceOk rpool (rm2'.getD r 0#32).toNat rpool.length ∧
        (rpool.getD (rm2'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ r < k2.toNat, MonoSorted rpool (rm2'.getD r 0#32).toNat) →
      monoTotalWords rpool rm2' k2.toNat ≤ s.rpcap.toNat →
      SymsBound rpool rm2' k2.toNat s.n_nets.toNat →
      (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
        array (t := i8) s'.flipped flippedArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
        rMem s' rm rl rh rm2' rl2' rh2' rpool ⋆ array (t := i32) s'.ix
          (if aPtr = s.ix then aArr else bArr) ⋆
        array (t := i32) s'.ix2 (if aPtr = s.ix then bArr else aArr) ⋆ R) m' →
      Q (true, ⟨⟩) m') :
    wp Γ Q X (buildRPass4Expr cx aPtr bPtr v off cnt fv_b any bt bw n) m := by
  let Rro : Mem 64 → Prop :=
    array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
    u32PadTail s.rm rm.length ⋆ u32PadTail s.rm2 rm2.length ⋆
    u32PadTail s.rpool rpool.length ⋆ R
  let Rcmb : Mem 64 → Prop :=
    arCtxMem cx s ⋆ array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
    array (t := i32) s.rpool rpool ⋆ array (t := i32) aPtr aArr ⋆
    array (t := i32) bPtr bArr ⋆ Rro
  have hRcmb : Rcmb = arCtxMem cx s ⋆ array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆
      array64 s.rh rh ⋆ array (t := i32) s.rpool rpool ⋆ array (t := i32) aPtr aArr ⋆
      array (t := i32) bPtr bArr ⋆ Rro := rfl
  have hm0 : (array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
      array64 s.rh2 rh2 ⋆ Rcmb) m := sep_cast hm (by dsimp only [Rcmb, Rro]; ac_rfl)
  clear hm
  dsimp only [buildRPass4Expr]
  refine wp_loop_group (CombineRAllInv s.modW Valid rpool rm rl rh aArr n.toNat
      s.rcap.toNat s.rm2 s.rl2 s.rh2 rm2 rl2 rh2 Rcmb) ?_ ?_
  · rintro JI irem ⟨i, k2, ⟨⟩⟩ mC hrecI
      ⟨rm2C, rl2C, rh2C, hrm2C_len, hrl2C_len, hrh2C_len, hrm2C_rc, hrl2C_rc, hrh2C_rc,
       hk2_le_i, hi_le_n, hirem, hpref, hwC, hevC, hmC⟩
    c0_hsteps_nogrp
    · have hi_lt : i.toNat < n.toNat := hc
      have hi_a : i.toNat < aArr.length := by omega
      have hip1 : (i + 1#32).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
      let h0 := aArr[i.toNat]'hi_a
      have hh0_eq : h0 = aArr.getD i.toNat 0#32 :=
        (getD_eq_getElem aArr 0#32 hi_a).symm
      have hh0_lt : h0.toNat < n.toNat := by rw [hh0_eq]; exact hPerm.mem_lt hi_lt
      have hh0_rl : h0.toNat < rl.length := by omega
      have hh0_rh : h0.toNat < rh.length := by omega
      have hmC0 : (arCtxMem cx s ⋆ array (t := i32) aPtr aArr ⋆ array64 s.rl rl ⋆
          array64 s.rh rh ⋆ array (t := i32) s.rm rm ⋆ array (t := i32) s.rpool rpool ⋆
          array (t := i32) s.rm2 rm2C ⋆ array64 s.rl2 rl2C ⋆ array64 s.rh2 rh2C ⋆
          array (t := i32) bPtr bArr ⋆ Rro) mC := by
        dsimp only [Rcmb] at hmC; exact sep_cast hmC (by ac_rfl)
      refine wp_load_arr32_idx (off := 0) (i := i) (base := aPtr) (xs := aArr)
        (R := arCtxMem cx s ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
          array (t := i32) s.rm rm ⋆ array (t := i32) s.rpool rpool ⋆
          array (t := i32) s.rm2 rm2C ⋆ array64 s.rl2 rl2C ⋆ array64 s.rh2 rh2C ⋆
          array (t := i32) bPtr bArr ⋆ Rro)
        (by simp) (by simpa using hi_a) (sep_cast hmC0 (by ac_rfl)) ?_
      c0_hsteps_nogrp
      have hh0_idx : (aArr[0 + i.toNat]'(by simpa using hi_a)) = h0 := by simp [h0]
      rw [hh0_idx]
      refine wp_load_arr64_idx (i := h0) (base := s.rl) (xs := rl)
        (R := arCtxMem cx s ⋆ array (t := i32) aPtr aArr ⋆ array64 s.rh rh ⋆
          array (t := i32) s.rm rm ⋆ array (t := i32) s.rpool rpool ⋆
          array (t := i32) s.rm2 rm2C ⋆ array64 s.rl2 rl2C ⋆ array64 s.rh2 rh2C ⋆
          array (t := i32) bPtr bArr ⋆ Rro)
        rfl hh0_rl (sep_cast hmC0 (by ac_rfl)) ?_
      c0_hsteps_nogrp
      let l0 := rl[h0.toNat]'hh0_rl
      let h_init := rh[h0.toNat]'hh0_rh
      refine wp_loop_group (CombineRJInv s.modW n.toNat i.toNat Valid
          rpool rm rl rh aArr h0 mC) ?_ ?_
      · rintro JJ jrem ⟨l, h, j, ⟨⟩⟩ mJ hrecJ ⟨hmJ, hj_lo, hj_le, hjrem, hwJ, hsumJ⟩
        subst mJ
        refine wp_join_group (fun (_ : Tup Val []) mE => mE = mC) ?_ ?_
        · rintro JE ⟨⟩ mE hmE
          subst mE
          c0_hsteps_nogrp
          refine wp_join_group (fun vK mK =>
              vK.1.toNat ≤ n.toNat ∧
              CombineRAllInv s.modW Valid rpool rm rl rh aArr n.toNat s.rcap.toNat
                s.rm2 s.rl2 s.rh2 rm2 rl2 rh2 Rcmb (n.toNat - j.toNat) (j, vK.1, ⟨⟩) mK) ?_ ?_
          · rintro JK ⟨k2', ⟨⟩⟩ mK ⟨_, hinvK⟩
            c0_hsteps_nogrp
            exact hrecI (n.toNat - j.toNat) (j, k2', ⟨⟩) mK (by omega) hinvK
          · intro JK hJK
            refine wp_join_group (fun (_ : Tup Val []) mD => mD = mC) ?_ ?_
            · rintro JD ⟨⟩ mD hmD
              subst mD
              have hk2_lt_rm : k2.toNat < rm2C.length := by omega
              have hk2_lt_rl : k2.toNat < rl2C.length := by omega
              have hk2_lt_rh : k2.toNat < rh2C.length := by omega
              have hh0_rm : h0.toNat < rm.length := by omega
              have hkp1 : (k2 + 1#32).toNat = k2.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : k2.toNat + 1 < 2 ^ 32)]
              c0_hsteps_nogrp
              have hh0_64 : (BitVec.setWidth 64 h0).toNat = h0.toNat := bv64_zext32 h0
              have hm_elem : rm[(BitVec.setWidth 64 h0).toNat]'(by rw [hh0_64]; exact hh0_rm) =
                  rm.getD h0.toNat 0#32 := by
                rw [← getD_eq_getElem rm 0#32 (by rw [hh0_64]; exact hh0_rm), hh0_64]
              have hk2_64 : (BitVec.setWidth 64 k2).toNat = k2.toNat := bv64_zext32 k2
              have hmK_new : (array (t := i32) s.rm2 (rm2C.set k2.toNat (rm.getD h0.toNat 0#32)) ⋆
                  array64 s.rl2 (rl2C.set k2.toNat l) ⋆ array64 s.rh2 (rh2C.set k2.toNat h) ⋆
                  Rcmb) m := by
                rw [hk2_64, hm_elem] at hm
                exact sep_cast hm (by dsimp only [Rcmb]; simp [ExtHashMap.sep_emp]; ac_rfl)
              let rm2' := rm2C.set k2.toNat (rm.getD h0.toNat 0#32)
              let rl2' := rl2C.set k2.toNat l
              let rh2' := rh2C.set k2.toNat h
              have hkeepE : ∀ σ t, t ≤ k2.toNat →
                  polyEval s.modW σ rpool rm2' rl2' rh2' t =
                    polyEval s.modW σ rpool rm2C rl2C rh2C t := by
                intro σ t ht
                induction t with
                | zero => rfl
                | succ t ih =>
                  have hne : t ≠ k2.toNat := by omega
                  rw [polyEval_succ, polyEval_succ, ih (by omega)]
                  congr 1
                  simp only [termEval, rm2', rl2', rh2', getD_set_eq _ 0#32 _ hk2_lt_rm,
                    getD_set_eq _ 0#64 _ hk2_lt_rl, getD_set_eq _ 0#64 _ hk2_lt_rh,
                    ite_eq_right hne]
              have htermE : ∀ σ, termEval s.modW σ rpool rm2' rl2' rh2' k2.toNat =
                  (if monoValL σ (symListAt rpool (rm.getD h0.toNat 0#32).toNat)
                    then coeff128 s.modW l h else 0#(s.modW)) := by
                intro σ
                simp only [termEval, rm2', rl2', rh2', getD_set_eq _ 0#32 _ hk2_lt_rm,
                  getD_set_eq _ 0#64 _ hk2_lt_rl, getD_set_eq _ 0#64 _ hk2_lt_rh, ↓reduceIte]
              refine hJK (k2 + 1#32, ⟨⟩) _ ⟨by rw [hkp1]; omega, rm2', rl2', rh2',
                by simp [rm2', hrm2C_len], by simp [rl2', hrl2C_len], by simp [rh2', hrh2C_len],
                by simp [rm2']; omega, by simp [rl2']; omega, by simp [rh2']; omega,
                by rw [hkp1]; omega, hj_le, rfl, fun p hp => ?_, ?_, fun σ hσ => ?_, hmK_new⟩
              · rw [hkp1] at hp
                by_cases hpk : p = k2.toNat
                · subst hpk; exact ⟨h0.toNat, hh0_lt, by
                    dsimp only [rm2']; rw [getD_set_eq _ 0#32 _ hk2_lt_rm, ite_eq_left rfl]⟩
                · obtain ⟨idx, hidx, heq⟩ := hpref p (by omega)
                  exact ⟨idx, hidx, by
                    dsimp only [rm2']; rw [getD_set_eq _ 0#32 _ hk2_lt_rm, ite_eq_right hpk, heq]⟩
              · rw [hkp1, monoTotalWords_succ]
                have hwm : monoTotalWords rpool rm2' k2.toNat =
                    monoTotalWords rpool rm2C k2.toNat := by
                  apply monoTotalWords_congr_prefix (bd := rpool.length) (fun r hr => by
                    obtain ⟨idx, hidx, heq⟩ := hpref r hr
                    rw [heq]
                    exact (hSl idx hidx).1) (fun _ _ => rfl)
                  intro p hp; dsimp only [rm2']
                  rw [getD_set_eq _ 0#32 _ hk2_lt_rm, ite_eq_right (by omega)]
                have hrmk : rm2'.getD k2.toNat 0#32 = rm.getD h0.toNat 0#32 := by
                  dsimp only [rm2']; rw [getD_set_eq _ 0#32 _ hk2_lt_rm, ite_eq_left rfl]
                rw [hwm, hrmk]; omega
              · rw [hkp1, polyEval_succ, hkeepE σ k2.toNat (le_refl _), htermE σ,
                  BitVec.add_assoc, hsumJ σ hσ, hevC σ hσ]
            · intro JD hJD
              c0_hsplit
              · exact hJD ⟨⟩ mC rfl
              · c0_hsplit
                · exact hJD ⟨⟩ mC rfl
                · have hl0 : l = 0#64 := by c0_bv_omega
                  have hh0_0 : h = 0#64 := by c0_bv_omega
                  c0_hfast_nogrp
                  have hk2_j : k2.toNat ≤ j.toNat :=
                    Nat.le_trans hk2_le_i (Nat.le_trans (Nat.le_succ _) hj_lo)
                  refine hJK (k2, ⟨⟩) mC ⟨Nat.le_trans hk2_j hj_le, rm2C, rl2C, rh2C, hrm2C_len,
                    hrl2C_len, hrh2C_len, hrm2C_rc, hrl2C_rc, hrh2C_rc, hk2_j, hj_le, rfl, hpref,
                    (Nat.le_trans (Nat.add_le_add_left
                      (Nat.le_trans (Nat.le_add_left _ _) hwJ) _) hwC),
                    (fun σ hσ => by
                      have h0c : (if monoValL σ (symListAt rpool (rm.getD h0.toNat 0#32).toNat)
                          then coeff128 s.modW l h else 0#(s.modW)) =
                          0#(s.modW) := by
                        subst hl0 hh0_0; simp [coeff128]
                      have hjS := hsumJ σ hσ
                      rw [h0c, BitVec.zero_add] at hjS
                      rw [hjS]; exact hevC σ hσ),
                    hmC⟩
        · intro JE hJE
          c0_hsteps_nogrp
          · have hj_lt : j.toNat < n.toNat := hc
            have hj_a : j.toNat < aArr.length := by omega
            have haj_eq : aArr[j.toNat]'hj_a = aArr.getD j.toNat 0#32 :=
              (getD_eq_getElem aArr 0#32 hj_a).symm
            have haj_lt : (aArr[j.toNat]'hj_a).toNat < n.toNat := by
              rw [haj_eq]; exact hPerm.mem_lt hj_lt
            have haj_rm : (aArr[j.toNat]'hj_a).toNat < rm.length := by omega
            have hh0_rm : h0.toNat < rm.length := by omega
            have hj_a64 : (BitVec.setWidth 64 j).toNat < aArr.length := by
              rw [bv64_zext32]; exact hj_a
            have haj_rm64 : (aArr[(BitVec.setWidth 64 j).toNat]'hj_a64).toNat < rm.length := by
              simpa only [bv64_zext32] using haj_rm
            refine wp_load_arr32_idx0 (i := aArr[(BitVec.setWidth 64 j).toNat]'hj_a64)
              (base := s.rm) (xs := rm)
              (R := arCtxMem cx s ⋆ array (t := i32) aPtr aArr ⋆ array64 s.rl rl ⋆
                array64 s.rh rh ⋆ array (t := i32) s.rpool rpool ⋆
                array (t := i32) s.rm2 rm2C ⋆ array64 s.rl2 rl2C ⋆ array64 s.rh2 rh2C ⋆
                array (t := i32) bPtr bArr ⋆ Rro)
              rfl haj_rm64 (sep_cast hmC0 (by ac_rfl)) ?_
            c0_hsteps_nogrp
            let aj := aArr[j.toNat]'hj_a
            have haj_eq' : aj = aArr.getD j.toNat 0#32 := haj_eq
            have haj_eq64 : aArr[(BitVec.setWidth 64 j).toNat]'hj_a64 = aj := by
              simp only [bv64_zext32, aj]
            have hh0_64 : (BitVec.setWidth 64 h0).toNat = h0.toNat := bv64_zext32 h0
            have hh0_rm64 : (BitVec.setWidth 64 h0).toNat < rm.length := by
              rw [hh0_64]; exact hh0_rm
            let rm_aj := rm[(aArr[(BitVec.setWidth 64 j).toNat]'hj_a64).toNat]'haj_rm64
            let rm_h0 := rm[(BitVec.setWidth 64 h0).toNat]'hh0_rm64
            have hrm_aj_eq : rm_aj = rm.getD (aArr.getD j.toNat 0#32).toNat 0#32 := by
              dsimp only [rm_aj]
              rw [← getD_eq_getElem rm 0#32 haj_rm64, haj_eq64, haj_eq']
            have hrm_h0_eq : rm_h0 = rm.getD h0.toNat 0#32 := by
              dsimp only [rm_h0]; rw [← getD_eq_getElem rm 0#32 hh0_rm64, hh0_64]
            let Rmc : Mem 64 → Prop :=
              arCtxMem cx s ⋆ array (t := i32) aPtr aArr ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
              array (t := i32) s.rm rm ⋆ array (t := i32) s.rm2 rm2C ⋆ array64 s.rl2 rl2C ⋆
              array64 s.rh2 rh2C ⋆ array (t := i32) bPtr bArr ⋆ Rro
            refine head_wp_call rfl (hMcmp _ _ _ _
              ⟨s.rpool, rpool, rm_aj.toNat, rm_h0.toNat, Rmc,
                (by apply BitVec.eq_of_toNat_eq
                    dsimp only [rm_aj]; simp [Nat.mul_comm]),
                (by apply BitVec.eq_of_toNat_eq
                    dsimp only [rm_h0]; simp [hh0_64, Nat.mul_comm]),
                (by rw [hrm_aj_eq, ← haj_eq]; exact (hSl _ haj_lt).1),
                (by rw [hrm_h0_eq]; exact (hSl _ hh0_lt).1),
                (by rw [hrm_aj_eq, ← haj_eq]; exact (hSl _ haj_lt).2),
                sep_cast hmC0 (by dsimp only [Rmc]; ac_rfl),
                fun cmp hcmp => ?_⟩)
            c0_hsteps_nogrp
            · have hcmp0 : cmp = 0#32 := by assumption
              have hsym : symListAt rpool (rm.getD (aArr.getD j.toNat 0#32).toNat 0#32).toNat =
                  symListAt rpool (rm.getD h0.toNat 0#32).toNat := by
                rw [← hrm_aj_eq, ← hrm_h0_eq]; exact hcmp hcmp0
              have haj_rl64 : (aArr[(BitVec.setWidth 64 j).toNat]'hj_a64).toNat < rl.length := by
                rw [haj_eq64]; dsimp only [aj] at *
                exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le haj_lt hn_rcap) hrl_len
              have haj_rh64 : (aArr[(BitVec.setWidth 64 j).toNat]'hj_a64).toNat < rh.length := by
                rw [haj_eq64]; dsimp only [aj] at *
                exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le haj_lt hn_rcap) hrh_len
              let rlj := rl[(aArr[(BitVec.setWidth 64 j).toNat]'hj_a64).toNat]'haj_rl64
              let rhj := rh[(aArr[(BitVec.setWidth 64 j).toNat]'hj_a64).toNat]'haj_rh64
              have hrlj_eq : rlj = rl.getD (aArr.getD j.toNat 0#32).toNat 0#64 := by
                dsimp only [rlj]
                rw [← getD_eq_getElem rl 0#64 haj_rl64, haj_eq64, haj_eq']
              have hrhj_eq : rhj = rh.getD (aArr.getD j.toNat 0#32).toNat 0#64 := by
                dsimp only [rhj]
                rw [← getD_eq_getElem rh 0#64 haj_rh64, haj_eq64, haj_eq']
              let Rcadd : Mem 64 → Prop :=
                array (t := i32) aPtr aArr ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
                array (t := i32) s.rm rm ⋆ array (t := i32) s.rpool rpool ⋆
                array (t := i32) s.rm2 rm2C ⋆ array64 s.rl2 rl2C ⋆ array64 s.rh2 rh2C ⋆
                array (t := i32) bPtr bArr ⋆ Rro
              refine head_wp_call rfl (hCadd _ _ _ _
                ⟨s, Rcadd, hMasks, sep_cast hmC0 (by dsimp only [Rcadd]; ac_rfl),
                  fun nl nh hcadd => ?_⟩)
              have hjp1 : (j + 1#32).toNat = j.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : j.toNat + 1 < 2 ^ 32)]
              c0_hsteps_nogrp
              exact hrecJ (n.toNat - (j + 1#32).toNat) (nl, nh, j + 1#32, ⟨⟩) mC
                (by omega) (combineR_cadd_step hj_lt hj_lo hjp1 hsym
                  (by rw [← hrlj_eq, ← hrhj_eq]; exact hcadd) hwJ hsumJ)
            · exact hJE ⟨⟩ mC rfl
          · exact hJE ⟨⟩ mC rfl
      · intro JJ hJJ
        c0_hsteps_nogrp
        have hsp : n.toNat - i.toNat = (n.toNat - (i.toNat + 1)) + 1 := by omega
        refine hJJ (n.toNat - (i + 1#32).toNat) (l0, h_init, i + 1#32, ⟨⟩) mC
          ⟨rfl, by omega, by omega, rfl, ?_, fun σ _ => ?_⟩
        · rw [hip1, hsp, tailRWords_split_one, hh0_eq]; exact le_refl _
        · rw [hip1, hsp, polyEvalIdxOf_split_one]
          dsimp only [l0, h_init]
          rw [← getD_eq_getElem rl 0#64 hh0_rl, ← getD_eq_getElem rh 0#64 hh0_rh, hh0_eq]
          rfl
    · have hi_eq : i.toNat = n.toNat := by have := BitVec.not_lt.mp hc; omega
      have hcur_eq : ∀ σ, Valid σ →
          polyEval s.modW σ rpool rm2C rl2C rh2C k2.toNat =
            polyEval s.modW σ rpool rm rl rh n.toNat := by
        intro σ hσ
        have he := hevC σ hσ
        simpa [hi_eq, Nat.sub_self, polyEvalIdxOf_nil] using he
      have hw_done : monoTotalWords rpool rm2C k2.toNat ≤ s.rpcap.toNat := by
        have ht0 : tailRWords rpool rm aArr i.toNat (n.toNat - i.toNat) = 0 := by
          simp [hi_eq, tailRWords_zero]
        omega
      dsimp only [Rcmb] at hmC
      c0_hsteps_nogrp
      let s' : ArCtxState := { s with
        cur_rm := s.rm2, cur_rl := s.rl2, cur_rh := s.rh2,
        cur_rp := s.rpool, cur_nr := k2 }
      have hm_ret : (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆
          array (t := i32) s'.rule_n ruleN ⋆ array (t := i8) s'.flipped flippedArr ⋆
          rsMem s' rsM rsL rsH rsPool ⋆ rMem s' rm rl rh rm2C rl2C rh2C rpool ⋆
          array (t := i32) s'.ix (if aPtr = s.ix then aArr else bArr) ⋆
          array (t := i32) s'.ix2 (if aPtr = s.ix then bArr else aArr) ⋆ R) m := by
        rw [rMem_unfold]
        rcases hptrs with ⟨ha, hb, hal, hbl⟩ | ⟨ha, hb, hal, hbl⟩
        · simp only [s', ha, ↓reduceIte]
          dsimp only [Rcmb, Rro] at hm
          exact sep_cast hm (by rw [ha, hb, hrm2C_len]; ac_rfl)
        · have hne : s.ix2 ≠ s.ix := by
            have ha_pos : 0 < aArr.length := by omega
            have hb_pos : 0 < bArr.length := by omega
            have hsep : (array (t := i32) s.ix2 aArr ⋆ array (t := i32) s.ix bArr ⋆
                (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆
                array (t := i32) s'.rule_n ruleN ⋆ array (t := i8) s'.flipped flippedArr ⋆
                rsMem s' rsM rsL rsH rsPool ⋆ array (t := i32) s.rm rm ⋆
                array64 s.rl rl ⋆ array64 s.rh rh ⋆ array (t := i32) s.rm2 rm2C ⋆
                array64 s.rl2 rl2C ⋆ array64 s.rh2 rh2C ⋆ array (t := i32) s.rpool rpool ⋆
                u32PadTail s.rm rm.length ⋆ u32PadTail s.rm2 rm2.length ⋆
                u32PadTail s.rpool rpool.length ⋆ R)) m := by
              dsimp only [Rcmb, Rro] at hm
              exact sep_cast hm (by rw [ha, hb]; ac_rfl)
            exact array32_sep_ne ha_pos hb_pos hsep
          simp only [s', ha, hne, ↓reduceIte]
          dsimp only [Rcmb, Rro] at hm
          exact sep_cast hm (by rw [ha, hb, hrm2C_len]; ac_rfl)
      refine hQ k2 s' rm2C rl2C rh2C m rfl (by omega) hrm2C_len hrl2C_len hrh2C_len
        (fun σ hσ => ?_) (fun r hr => ?_) (fun r hr => ?_) hw_done (fun r hr x hx => ?_) hm_ret
      · refine ⟨by omega, by omega, by omega, fun r hr => ?_, ?_⟩
        · obtain ⟨idx, hidx, heq⟩ := hpref r hr
          rw [heq]; exact (hSl idx hidx).1
        · rw [hcur_eq σ hσ]; exact (hEval σ hσ).symm
      · obtain ⟨idx, hidx, heq⟩ := hpref r hr
        rw [heq]; exact hSl idx hidx
      · obtain ⟨idx, hidx, heq⟩ := hpref r hr
        rw [heq]; exact hSorted idx hidx
      · obtain ⟨idx, hidx, heq⟩ := hpref r hr
        rw [heq] at hx; exact hSyms idx hidx x hx
  · intro JI hJI
    c0_hfast
    refine hJI n.toNat (0#32, 0#32, ⟨⟩) m ⟨rm2, rl2, rh2, rfl, rfl, rfl, hrm2_len, hrl2_len,
      hrh2_len, Nat.zero_le _, Nat.zero_le _, rfl, fun _ hp => by simp at hp, ?_, ?_, hm0⟩
    · simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, monoTotalWords_zero, Nat.zero_add]
      rw [tailRWords_init_perm hPerm]
      exact le_refl _
    · intro σ _
      have h1 : polyEvalIdxOf s.modW σ rpool rm rl rh aArr 0 n.toNat =
          ((List.range n.toNat).map (fun k => (aArr.getD k 0#32).toNat)).foldl
            (fun acc idx => acc + termEval s.modW σ rpool rm rl rh idx)
            0#(s.modW) := by
        simp [polyEvalIdxOf, List.foldl_map]
      have h2 : polyEval s.modW σ rpool rm rl rh n.toNat =
          (List.range n.toNat).foldl
            (fun acc idx => acc + termEval s.modW σ rpool rm rl rh idx)
            0#(s.modW) := by
        simp [polyEval, polyEvalRange]
      simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, polyEval_zero, BitVec.zero_add]
      rw [h1, h2]; exact foldl_add_perm _ hPerm

/-! ## 3. Pass 3 AST Matchers & WP (`buildR_merge_phase`, `buildR_sort_wp`) -/

/-- Extract the Pass 3 `while (w < (u64)n)` merge loop from `buildRPass2AfterExpr`. -/
@[expose] def buildRMergeExpr (cx ixPtr ix2Ptr : Val i64) (v off cnt : Val i32)
    (fv_b any : Val .bool) (bt bw : Val i64) (nFinal : Val i32) : Expr Val Cont [.bool] :=
  match buildRPass2AfterExpr cx ixPtr ix2Ptr v off cnt fv_b any bt bw nFinal with
  | @Expr.group _ _ _ [[.bits 32]] bs1 _ =>
    match bs1 (fun _ _ => False, ()) with
    | .cons b1 _ => match b1 (0#32, ()) with
      | @Expr.let_ _ _ _ [.bool] _ c1 => match c1 (false, ()) with
        | .jnz _ _ eW => eW
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

private theorem buildR_merge_phase (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx : BitVec 64} {v off cnt : BitVec 32} {fv_b any : Bool}
    {bt bw : BitVec 64} {n : BitVec 32}
    {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rm : List (BitVec 32)} {rl rh : List (BitVec 64)}
    {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)} {rpool a1 ix ix2 : List (BitVec 32)}
    {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hn_rcap : n.toNat ≤ s.rcap.toNat) (hn_qcap : n.toNat ≤ s.qcap.toNat)
    (hqcap_lo : 1 ≤ s.qcap.toNat) (hqcap_hi : s.qcap.toNat + 16 < 2 ^ 32)
    (hrpcap_32 : s.rpcap.toNat < 2 ^ 32)
    (hrm_len : s.rcap.toNat ≤ rm.length) (hrl_len : s.rcap.toNat ≤ rl.length)
    (hrh_len : s.rcap.toNat ≤ rh.length) (hrm2_len : s.rcap.toNat ≤ rm2.length)
    (hrl2_len : s.rcap.toNat ≤ rl2.length) (hrh2_len : s.rcap.toNat ≤ rh2.length)
    (hrpool_len : s.rpcap.toNat ≤ rpool.length) (hix_eq : ix.length = ix2.length)
    (hix_len : s.qcap.toNat ≤ ix.length) (ha1_len : a1.length = ix.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi) (hPerm : PermN a1 n.toNat)
    (hSl : ∀ r < n.toNat, MonoSliceOk rpool (rm.getD r 0#32).toNat rpool.length ∧
      (rpool.getD (rm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : ∀ r < n.toNat, MonoSorted rpool (rm.getD r 0#32).toNat)
    (hWords : monoTotalWords rpool rm n.toNat ≤ s.rpcap.toNat)
    (hSyms : SymsBound rpool rm n.toNat s.n_nets.toNat)
    (hEval : ∀ σ, Valid σ →
      polyEval s.modW σ rpool rm rl rh n.toNat =
        bv s.modW
          (σ (if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)))
    (hm : (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
      array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
      array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆ array64 s.rh2 rh2 ⋆
      array (t := i32) s.rpool rpool ⋆ array (t := i32) s.ix a1 ⋆ array (t := i32) s.ix2 ix2 ⋆
      u32PadTail s.rm rm.length ⋆ u32PadTail s.rm2 rm2.length ⋆
      u32PadTail s.rpool rpool.length ⋆ R) m)
    (hQ : ∀ (k2 : BitVec 32) (s' : ArCtxState)
        (rm2' : List (BitVec 32)) (rl2' rh2' : List (BitVec 64))
        (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      s' = { s with
        cur_rm := s.rm2, cur_rl := s.rl2, cur_rh := s.rh2,
        cur_rp := s.rpool, cur_nr := k2 } →
      k2.toNat ≤ s.rcap.toNat → rm2'.length = rm2.length → rl2'.length = rl2.length →
      rh2'.length = rh2.length → ix'.length = ix.length → ix2'.length = ix2.length →
      (∀ σ, Valid σ → CurRRep s.modW σ k2.toNat
        (if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)
        rm2' rl2' rh2' rpool) →
      (∀ r < k2.toNat, MonoSliceOk rpool (rm2'.getD r 0#32).toNat rpool.length ∧
        (rpool.getD (rm2'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ r < k2.toNat, MonoSorted rpool (rm2'.getD r 0#32).toNat) →
      monoTotalWords rpool rm2' k2.toNat ≤ s.rpcap.toNat →
      SymsBound rpool rm2' k2.toNat s.n_nets.toNat →
      (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
        array (t := i8) s'.flipped flippedArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
        rMem s' rm rl rh rm2' rl2' rh2' rpool ⋆ array (t := i32) s'.ix ix' ⋆
        array (t := i32) s'.ix2 ix2' ⋆ R) m' →
      Q (true, ⟨⟩) m') :
    wp Γ Q X (buildRMergeExpr cx s.ix s.ix2 v off cnt fv_b any bt bw n) m := by
  let Rmerge : Mem 64 → Prop :=
    arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
    array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
    array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆ array64 s.rh2 rh2 ⋆
    array (t := i32) s.rpool rpool ⋆ u32PadTail s.rm rm.length ⋆
    u32PadTail s.rm2 rm2.length ⋆ u32PadTail s.rpool rpool.length ⋆ R
  have hRmerge : Rmerge = arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆
      array (t := i32) s.rule_n ruleN ⋆ array (t := i8) s.flipped flippedArr ⋆
      rsMem s rsM rsL rsH rsPool ⋆ array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆
      array64 s.rh rh ⋆ array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
      array64 s.rh2 rh2 ⋆ array (t := i32) s.rpool rpool ⋆ u32PadTail s.rm rm.length ⋆
      u32PadTail s.rm2 rm2.length ⋆ u32PadTail s.rpool rpool.length ⋆ R := rfl
  dsimp only [buildRMergeExpr]
  refine wp_loop_group (MergeWInvR s ix ix2 n.toNat Rmerge) ?_ ?_
  · intro JW wrem ⟨aPtr, bPtr, w, ⟨⟩⟩ mW hrecW
      ⟨aArr, bArr, hptrs, hpermA, hw_lo, hw_bd, hwrem, hmW⟩
    have ha_qcap : s.qcap.toNat ≤ aArr.length ∧ s.qcap.toNat ≤ bArr.length := by
      rcases hptrs with ⟨_, _, ha, hb⟩ | ⟨_, _, ha, hb⟩ <;> omega
    c0_hsplit
    · have hw_lt : w.toNat < n.toNat := hc
      clear hc
      have ⟨hw2_64, hw_w2, hw2_bd⟩ := merge_w_bounds_r hw_lo hw_lt (by omega)
      c0_hfast_nogrp
      refine wp_loop_group (MergeLoInvR aPtr bPtr aArr bArr n.toNat w Rmerge) ?_ ?_
      · intro JL lorem ⟨lo, ⟨⟩⟩ mL hrecL ⟨bCur, hb_len, hlo_bd, hlorem, hprevL, hmL⟩
        clear hmW; c0_hsplit
        · have hlo_lt : lo.toNat < n.toNat := hc
          clear hc
          have hw_bd16 : w.toNat ≤ 2 * max 16 n.toNat := by
            simp only [Nat.max_def] at hw_bd ⊢; split at hw_bd <;> split <;> omega
          have ⟨h64a, h64b, hmid_eq, hhi_eq⟩ := merge_slice_bounds hlo_lt hw_bd16 (by omega)
          have hlo32 : (lo.setWidth 32).toNat = lo.toNat := by
            have := n.isLt; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          c0_hfast_nogrp
          refine wp_join_group (fun (v : Tup Val [i32]) mM1 =>
              mM1 = mL ∧ v.1.toNat = min (lo.toNat + w.toNat) n.toNat) ?_ ?_
          · rintro J1 ⟨mid, ⟨⟩⟩ mM1 ⟨hmM1, hmid_v⟩; subst mM1
            have hmid_v' : mid.toNat = min (lo.toNat + w.toNat) n.toNat := by simpa using hmid_v
            c0_hfast_nogrp
            refine wp_join_group (fun (v : Tup Val [i32]) mM2 =>
                mM2 = mL ∧ v.1.toNat = min (lo.toNat + 2 * w.toNat) n.toNat) ?_ ?_
            · rintro J2 ⟨hi, ⟨⟩⟩ mM2 ⟨hmM2, hhi_v⟩; subst mM2
              have hhi_v' : hi.toNat = min (lo.toNat + 2 * w.toNat) n.toNat := by
                simpa using hhi_v
              have hlo_mid : lo.toNat ≤ mid.toNat := by omega
              have hmid_hi : mid.toNat ≤ hi.toNat := by omega
              have hhi_n : hi.toNat ≤ n.toNat := by omega
              c0_hfast_nogrp
              refine wp_loop_group (MergeChunkLoopInvR aPtr bPtr aArr bArr bCur
                  lo.toNat mid.toNat hi.toNat Rmerge) ?_ ?_
              · intro JM pqrem ⟨p, q, o, ⟨⟩⟩ mM hrecM ⟨hpqrem, bM, hbM_len, hlo_p, hp_mid,
                    hmid_q, hq_hi, ho_eq, hkeepM, hpermM, hmM⟩
                clear hmL
                refine wp_join_group (fun (_ : Tup Val []) mJ => mJ = mM) ?_ ?_
                · rintro JJ ⟨⟩ mJ hmJ; subst mJ; c0_hstraight
                  refine wp_loop_group (MergePInvR aPtr bPtr aArr bArr bCur lo.toNat
                      mid.toNat hi.toNat q.toNat Rmerge) ?_ ?_
                  · intro JP prem ⟨p1, o1, ⟨⟩⟩ mP hrecP ⟨hprem, bP, hbP_len, hlo_p1,
                        hp1_mid, _, _, ho1_eq, hkeepP, hpermP, hmP⟩
                    clear hmM; c0_hsplit
                    · have hp1_lt : p1.toNat < mid.toNat := hc
                      clear hc
                      have ho1_p1 : (o1 + 1#32).toNat = o1.toNat + 1 :=
                        bv32_succ_toNat (by have := n.isLt; omega)
                      have hp1_p1 : (p1 + 1#32).toNat = p1.toNat + 1 :=
                        bv32_succ_toNat (by have := n.isLt; omega)
                      c0_hfast
                      refine hrecP (mid.toNat - (p1 + 1#32).toNat) (p1 + 1#32, o1 + 1#32, ⟨⟩)
                        _ (by rw [hp1_p1]; omega) ⟨rfl, ?_⟩
                      rw [ho1_p1, hp1_p1]
                      exact MergeChunkInv.step_p hbP_len hlo_p1 hp1_lt hmid_q hq_hi ho1_eq
                        (by omega) (by omega) hkeepP hpermP
                        (by simp only [bv64_zext32] at hm
                            exact sep_cast hm (by simp [ExtHashMap.sep_emp]; ac_rfl))
                    · have hp1_eq : p1.toNat = mid.toNat := by
                        have := BitVec.not_lt.mp hc; omega
                      clear hc; c0_hstraight
                      refine wp_loop_group (MergeQInvR aPtr bPtr aArr bArr bCur
                          lo.toNat mid.toNat hi.toNat Rmerge) ?_ ?_
                      · intro JQ qrem ⟨q1, o2, ⟨⟩⟩ mQ hrecQ ⟨hqrem, bQ, hbQ_len, _, _,
                            hmid_q1, hq1_hi, ho2_eq, hkeepQ, hpermQ, hmQ⟩
                        clear hmP; c0_hsplit
                        · have hq1_lt : q1.toNat < hi.toNat := hc
                          clear hc
                          have ho2_p1 : (o2 + 1#32).toNat = o2.toNat + 1 :=
                            bv32_succ_toNat (by have := n.isLt; omega)
                          have hq1_p1 : (q1 + 1#32).toNat = q1.toNat + 1 :=
                            bv32_succ_toNat (by have := n.isLt; omega)
                          c0_hfast
                          refine hrecQ (hi.toNat - (q1 + 1#32).toNat)
                            (q1 + 1#32, o2 + 1#32, ⟨⟩) _ (by rw [hq1_p1]; omega) ⟨rfl, ?_⟩
                          rw [ho2_p1, hq1_p1]
                          exact MergeChunkInv.step_q hbQ_len hlo_mid (le_refl _) hmid_q1 hq1_lt
                            ho2_eq (by omega) (by omega) hkeepQ hpermQ
                            (by simp only [bv64_zext32] at hm
                                exact sep_cast hm (by simp [ExtHashMap.sep_emp]; ac_rfl))
                        · have hq1_eq : q1.toNat = hi.toNat := by
                            have := BitVec.not_lt.mp hc; omega
                          clear hc
                          have hlo2w := merge_lo2w_r h64b; c0_hfast
                          refine hrecL ((n.toNat + 2 * w.toNat) - (lo + 2#64 * w).toNat)
                            (lo + 2#64 * w, ⟨⟩) mQ (by rw [hlo2w]; omega)
                            ⟨bQ, hbQ_len, by rw [hlo2w]; omega, rfl, ?_, hmQ⟩
                          rw [hlo2w]
                          exact merge_lo_next_perm (mid := mid.toNat) (le_trans hlo_mid hmid_hi)
                            (by omega) hhi_v hprevL hkeepQ (by
                              rw [show o2.toNat = hi.toNat by omega, hq1_eq] at hpermQ
                              simpa [Nat.sub_self] using hpermQ)
                      · intro JQ hJQ; c0_hfast; exact hJQ (hi.toNat - q.toNat)
                          (q, o1, ⟨⟩) mP ⟨rfl, bP, hbP_len, hlo_mid, le_refl _, hmid_q,
                            hq_hi, by omega, hkeepP, (by rw [hp1_eq] at hpermP; exact hpermP), hmP⟩
                  · intro JP hJP; c0_hfast; exact hJP (mid.toNat - p.toNat) (p, o, ⟨⟩) mM
                      ⟨rfl, bM, hbM_len, hlo_p, hp_mid, hmid_q, hq_hi, ho_eq, hkeepM, hpermM, hmM⟩
                · intro JJ hJJ; c0_hfast
                  · rename_i hc2
                    have hp_lt : p.toNat < mid.toNat := hc2
                    have hq_lt : q.toNat < hi.toNat := hc
                    try clear hc hc2
                    have ho_lt : o.toNat < bM.length := by omega
                    have hp_a : p.toNat < aArr.length := by omega
                    have hq_a : q.toNat < aArr.length := by omega
                    have ho_p1 : (o + 1#32).toNat = o.toNat + 1 :=
                      bv32_succ_toNat (by have := n.isLt; omega)
                    have hp_p1 : (p + 1#32).toNat = p.toNat + 1 :=
                      bv32_succ_toNat (by have := n.isLt; omega)
                    have hq_p1 : (q + 1#32).toNat = q.toNat + 1 :=
                      bv32_succ_toNat (by have := n.isLt; omega)
                    have ha_p_lt : (aArr[p.toNat]'hp_a).toNat < n.toNat := by
                      rw [← getD_eq_getElem aArr 0#32 hp_a]; exact hpermA.mem_lt (by omega)
                    have ha_q_lt : (aArr[q.toNat]'hq_a).toNat < n.toNat := by
                      rw [← getD_eq_getElem aArr 0#32 hq_a]; exact hpermA.mem_lt (by omega)
                    have hp_rm : (aArr[p.toNat]'hp_a).toNat < rm.length := by omega
                    have hq_rm : (aArr[q.toNat]'hq_a).toNat < rm.length := by omega
                    have hSl_p := hSl _ ha_p_lt
                    have hSl_q := hSl _ ha_q_lt
                    rw [← getD_eq_getElem aArr 0#32 hp_a] at hSl_p
                    rw [← getD_eq_getElem aArr 0#32 hq_a] at hSl_q
                    rw [hRmerge] at hmM; c0_hstraight
                    let Rmc := arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆
                      array (t := i32) s.rule_n ruleN ⋆ array (t := i8) s.flipped flippedArr ⋆
                      rsMem s rsM rsL rsH rsPool ⋆ array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆
                      array64 s.rh rh ⋆ array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
                      array64 s.rh2 rh2 ⋆ array (t := i32) aPtr aArr ⋆ array (t := i32) bPtr bM ⋆
                      u32PadTail s.rm rm.length ⋆ u32PadTail s.rm2 rm2.length ⋆
                      u32PadTail s.rpool rpool.length ⋆ R
                    have hp64 : (BitVec.setWidth 64 p).toNat = p.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans p.isLt (by decide))]
                    have hq64 : (BitVec.setWidth 64 q).toNat = q.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans q.isLt (by decide))]
                    have hap64 : (BitVec.setWidth 64 (aArr[p.toNat]'hp_a)).toNat =
                        (aArr[p.toNat]'hp_a).toNat := by
                      rw [BitVec.toNat_setWidth,
                        Nat.mod_eq_of_lt (lt_trans (aArr[p.toNat]'hp_a).isLt (by decide))]
                    have haq64 : (BitVec.setWidth 64 (aArr[q.toNat]'hq_a)).toNat =
                        (aArr[q.toNat]'hq_a).toNat := by
                      rw [BitVec.toNat_setWidth,
                        Nat.mod_eq_of_lt (lt_trans (aArr[q.toNat]'hq_a).isLt (by decide))]
                    refine head_wp_call rfl (hMcmp _ _ _ _
                      ⟨s.rpool, rpool,
                        (rm.getD (aArr.getD p.toNat 0#32).toNat 0#32).toNat,
                        (rm.getD (aArr.getD q.toNat 0#32).toNat 0#32).toNat, Rmc,
                        (by simp only [Arg.val, hp64, hap64]
                            rw [← getD_eq_getElem rm 0#32 hp_rm,
                              ← getD_eq_getElem aArr 0#32 hp_a]
                            apply congrArg (s.rpool + ·)
                            apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]),
                        (by simp only [Arg.val, hq64, haq64]
                            rw [← getD_eq_getElem rm 0#32 hq_rm,
                              ← getD_eq_getElem aArr 0#32 hq_a]
                            apply congrArg (s.rpool + ·)
                            apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]),
                        hSl_p.1, hSl_q.1, hSl_p.2,
                        sep_cast hmM (by dsimp only [Rmc]; ac_rfl), fun cmp _ => ?_⟩)
                    · dsimp only [Rmc]; rw [← hRmerge] at hmM
                      c0_hsplit
                      · clear hc; c0_hfast
                        refine hrecM ((hi.toNat - lo.toNat) - ((o + 1#32).toNat - lo.toNat))
                          (p + 1#32, q, o + 1#32, ⟨⟩) _ (by rw [ho_p1]; omega) ⟨rfl, ?_⟩
                        rw [ho_p1, hp_p1]
                        exact MergeChunkInv.step_p hbM_len hlo_p hp_lt hmid_q hq_hi ho_eq
                          ho_lt hp_a hkeepM hpermM
                          (by simp only [bv64_zext32] at hm
                              exact sep_cast hm (by simp [ExtHashMap.sep_emp]; ac_rfl))
                      · clear hc; c0_hfast
                        refine hrecM ((hi.toNat - lo.toNat) - ((o + 1#32).toNat - lo.toNat))
                          (p, q + 1#32, o + 1#32, ⟨⟩) _ (by rw [ho_p1]; omega) ⟨rfl, ?_⟩
                        rw [ho_p1, hq_p1]
                        exact MergeChunkInv.step_q hbM_len hlo_p hp_mid hmid_q hq_lt ho_eq
                          ho_lt hq_a hkeepM hpermM
                          (by simp only [bv64_zext32] at hm
                              exact sep_cast hm (by simp [ExtHashMap.sep_emp]; ac_rfl))
                  all_goals exact hJJ ⟨⟩ mM rfl
              · intro JM hJM; c0_hfast; exact hJM (hi.toNat - lo.toNat)
                  (lo.setWidth 32, mid, lo.setWidth 32, ⟨⟩) mL ⟨by rw [hlo32]; omega,
                    bCur, hb_len, by rw [hlo32]; exact le_refl _, by rw [hlo32]; exact hlo_mid,
                    le_refl _, hmid_hi, by rw [hlo32]; omega, fun t _ => rfl,
                    by simp only [hlo32, Nat.sub_self, List.range_zero,
                         List.map_nil, List.nil_append]
                       rw [show hi.toNat - lo.toNat =
                         (mid.toNat - lo.toNat) + (hi.toNat - mid.toNat) by omega,
                         List.range_add, List.map_append, List.map_map]
                       rw [show ((fun t => (aArr.getD (lo.toNat + t) 0#32).toNat) ∘
                           (fun x => mid.toNat - lo.toNat + x)) =
                           (fun x => (aArr.getD (mid.toNat + x) 0#32).toNat) by
                         funext x; dsimp; congr 2; omega],
                    hmL⟩
            · intro J2 hJ2; c0_hfast
              · have hlt : lo + 2#64 * w < BitVec.setWidth 64 n := by
                  simpa [BitVec.lt_def, bv64_zext32] using hc
                exact hJ2 ((lo + 2#64 * w).setWidth 32, ⟨⟩) mL
                  ⟨rfl, by rw [← hhi_eq]; simp only [hlt, ↓reduceIte]⟩
              · have hlt : ¬ (lo + 2#64 * w < BitVec.setWidth 64 n) := by
                  simpa [BitVec.lt_def, bv64_zext32] using hc
                exact hJ2 (n, ⟨⟩) mL ⟨rfl, by rw [← hhi_eq]; simp only [hlt, ↓reduceIte]⟩
          · intro J1 hJ1; c0_hfast
            · have hlt : lo + w < BitVec.setWidth 64 n := by
                simpa [BitVec.lt_def, bv64_zext32] using hc
              exact hJ1 ((lo + w).setWidth 32, ⟨⟩) mL
                ⟨rfl, by rw [← hmid_eq]; simp only [hlt, ↓reduceIte]⟩
            · have hlt : ¬ (lo + w < BitVec.setWidth 64 n) := by
                simpa [BitVec.lt_def, bv64_zext32] using hc
              exact hJ1 (n, ⟨⟩) mL ⟨rfl, by rw [← hmid_eq]; simp only [hlt, ↓reduceIte]⟩
        · have hlo_n : n.toNat ≤ lo.toNat := by
            have hnot : ¬ lo.toNat < (BitVec.setWidth 64 n).toNat := by simpa using hc
            rw [bv64_zext32] at hnot; omega
          clear hc; c0_hfast
          have hpermB : PermN bCur n.toNat := by
            rw [Nat.min_eq_right hlo_n] at hprevL; exact hprevL.trans hpermA
          refine hrecW (2 * max 1 n.toNat - (w * 2#64).toNat) (bPtr, aPtr, w * 2#64, ⟨⟩) mL
            (by rw [hw_w2]; omega) ⟨bCur, aArr, ?_, hpermB, by rw [hw_w2]; omega, hw2_bd, rfl,
              sep_cast hmL (by ac_rfl)⟩
          rcases hptrs with ⟨ha, hb, hal, hbl⟩ | ⟨ha, hb, hal, hbl⟩ <;>
            simp [ha, hb, hal, hbl, hb_len]
      · intro JL hJL; c0_hfast; exact hJL (n.toNat + 2 * w.toNat) (0#64, ⟨⟩) mW
          ⟨bArr, rfl, by simp, rfl, by simp [Nat.min_eq_left (Nat.zero_le _)], hmW⟩
    · clear hc; rw [hRmerge] at hmW
      change wp Γ Q X (buildRPass4Expr cx aPtr bPtr v off cnt fv_b any bt bw n) mW
      refine buildR_combine_wp Γ hMcmp hCadd (R := R) hn_rcap hn_qcap hqcap_lo hqcap_hi hrpcap_32
        hrm_len hrl_len hrh_len hrm2_len hrl2_len hrh2_len hrpool_len hix_eq hptrs
        ha_qcap.1 hMasks hpermA hSl hSorted hWords hSyms hEval (sep_cast hmW (by ac_rfl)) ?_
      intro k2 s' rm2' rl2' rh2' m' hs' hk2 hrm2' hrl2' hrh2' hCur hSl' hSorted' hW' hSb' hm'
      have hlen1 : (if aPtr = s.ix then aArr else bArr).length = ix.length := by
        rcases hptrs with ⟨_, _, hal, hbl⟩ | ⟨_, _, hal, hbl⟩ <;> split <;> omega
      have hlen2 : (if aPtr = s.ix then bArr else aArr).length = ix2.length := by
        rcases hptrs with ⟨_, _, hal, hbl⟩ | ⟨_, _, hal, hbl⟩ <;> split <;> omega
      exact hQ k2 s' rm2' rl2' rh2' _ _ m' hs' hk2 hrm2' hrl2' hrh2' hlen1 hlen2
        hCur hSl' hSorted' hW' hSb' hm'
  · intro JW hJW; c0_hfast; exact hJW (2 * max 1 n.toNat - 1) (s.ix, s.ix2, 1#64, ⟨⟩) m
      ⟨a1, ix2, Or.inl ⟨rfl, rfl, ha1_len, rfl⟩, hPerm, by decide,
        by simp [Nat.max_def]; split <;> omega, rfl,
        (by rw [hRmerge]; exact sep_cast hm (by ac_rfl))⟩

theorem buildR_sort_wp (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx : BitVec 64} {v off cnt : BitVec 32} {fv_b any : Bool}
    {bt bw : BitVec 64} {n : BitVec 32}
    {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rm : List (BitVec 32)} {rl rh : List (BitVec 64)}
    {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)} {rpool ix ix2 : List (BitVec 32)}
    {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hn_rcap : n.toNat ≤ s.rcap.toNat) (hn_qcap : n.toNat ≤ s.qcap.toNat)
    (hqcap_lo : 1 ≤ s.qcap.toNat) (hqcap_hi : s.qcap.toNat + 16 < 2 ^ 32)
    (hrpcap_32 : s.rpcap.toNat < 2 ^ 32)
    (hrm_len : s.rcap.toNat ≤ rm.length) (hrl_len : s.rcap.toNat ≤ rl.length)
    (hrh_len : s.rcap.toNat ≤ rh.length) (hrm2_len : s.rcap.toNat ≤ rm2.length)
    (hrl2_len : s.rcap.toNat ≤ rl2.length) (hrh2_len : s.rcap.toNat ≤ rh2.length)
    (hrpool_len : s.rpcap.toNat ≤ rpool.length) (hix_eq : ix.length = ix2.length)
    (hix_len : s.qcap.toNat ≤ ix.length) (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hSl : ∀ r < n.toNat, MonoSliceOk rpool (rm.getD r 0#32).toNat rpool.length ∧
      (rpool.getD (rm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : ∀ r < n.toNat, MonoSorted rpool (rm.getD r 0#32).toNat)
    (hWords : monoTotalWords rpool rm n.toNat ≤ s.rpcap.toNat)
    (hSyms : SymsBound rpool rm n.toNat s.n_nets.toNat)
    (hEval : ∀ σ, Valid σ →
      polyEval s.modW σ rpool rm rl rh n.toNat =
        bv s.modW
          (σ (if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)))
    (hm : (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
      rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ array (t := i32) s.ix ix ⋆
      array (t := i32) s.ix2 ix2 ⋆ R) m)
    (hQ : ∀ (k2 : BitVec 32) (s' : ArCtxState)
        (rm2' : List (BitVec 32)) (rl2' rh2' : List (BitVec 64))
        (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      s' = { s with
        cur_rm := s.rm2, cur_rl := s.rl2, cur_rh := s.rh2,
        cur_rp := s.rpool, cur_nr := k2 } →
      k2.toNat ≤ s.rcap.toNat → rm2'.length = rm2.length → rl2'.length = rl2.length →
      rh2'.length = rh2.length → ix'.length = ix.length → ix2'.length = ix2.length →
      (∀ σ, Valid σ → CurRRep s.modW σ k2.toNat
        (if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)
        rm2' rl2' rh2' rpool) →
      (∀ r < k2.toNat, MonoSliceOk rpool (rm2'.getD r 0#32).toNat rpool.length ∧
        (rpool.getD (rm2'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ r < k2.toNat, MonoSorted rpool (rm2'.getD r 0#32).toNat) →
      monoTotalWords rpool rm2' k2.toNat ≤ s.rpcap.toNat →
      SymsBound rpool rm2' k2.toNat s.n_nets.toNat →
      (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
        array (t := i8) s'.flipped flippedArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
        rMem s' rm rl rh rm2' rl2' rh2' rpool ⋆ array (t := i32) s'.ix ix' ⋆
        array (t := i32) s'.ix2 ix2' ⋆ R) m' →
      Q (true, ⟨⟩) m') :
    wp Γ Q X (buildRPass2AfterExpr cx s.ix s.ix2 v off cnt fv_b any bt bw n) m := by
  rw [rMem_unfold] at hm
  let Rsort : Mem 64 → Prop :=
    arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
    array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
    array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆ array64 s.rh2 rh2 ⋆
    array (t := i32) s.rpool rpool ⋆ array (t := i32) s.ix2 ix2 ⋆
    u32PadTail s.rm rm.length ⋆ u32PadTail s.rm2 rm2.length ⋆ u32PadTail s.rpool rpool.length ⋆ R
  have hRsort : Rsort = arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆
      array (t := i32) s.rule_n ruleN ⋆ array (t := i8) s.flipped flippedArr ⋆
      rsMem s rsM rsL rsH rsPool ⋆ array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆
      array64 s.rh rh ⋆ array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
      array64 s.rh2 rh2 ⋆ array (t := i32) s.rpool rpool ⋆ array (t := i32) s.ix2 ix2 ⋆
      u32PadTail s.rm rm.length ⋆ u32PadTail s.rm2 rm2.length ⋆
      u32PadTail s.rpool rpool.length ⋆ R := rfl
  dsimp only [buildRPass2AfterExpr]
  refine wp_loop_group (fun rem ⟨i, ⟨⟩⟩ m1 =>
      ∃ a1 : List (BitVec 32), a1.length = ix.length ∧ i.toNat ≤ n.toNat ∧
        rem = n.toNat - i.toNat ∧ (∀ t < i.toNat, (a1.getD t 0#32).toNat = t) ∧
        (array (t := i32) s.ix a1 ⋆ Rsort) m1) ?_ ?_
  · intro J1 rem ⟨i, ⟨⟩⟩ m1 hrec1 ⟨a1, ha1_len, hi_le, hrem1, ha1_id, hm1⟩
    clear hm; c0_hsplit
    · have hi_lt : i.toNat < n.toNat := hc
      clear hc
      have hip1 : (i + 1#32).toNat = i.toNat + 1 := bv32_succ_toNat (by have := n.isLt; omega)
      c0_hfast
      refine hrec1 (n.toNat - (i + 1#32).toNat) (i + 1#32, ⟨⟩) _ (by omega)
        ⟨a1.set i.toNat i, by simp [ha1_len], by omega, rfl, ?_, ‹_›⟩
      rw [hip1]; intro t ht
      rw [getD_set_eq a1 0#32 i (by omega)]
      by_cases hti : t = i.toNat
      · subst hti; simp
      · simp only [hti, ↓reduceIte]; exact ha1_id t (by omega)
    · have hi_eq : i.toNat = n.toNat := by have := BitVec.not_lt.mp hc; omega
      clear hc
      have hperm1 : PermN a1 n.toNat := permN_range_id (by simpa [hi_eq] using ha1_id)
      rw [hRsort] at hm1
      change wp Γ Q X (buildRMergeExpr cx s.ix s.ix2 v off cnt fv_b any bt bw n) m1
      exact buildR_merge_phase Γ hMcmp hCadd hn_rcap hn_qcap hqcap_lo hqcap_hi hrpcap_32
        hrm_len hrl_len hrh_len hrm2_len hrl2_len hrh2_len hrpool_len hix_eq hix_len ha1_len
        hMasks hperm1 hSl hSorted hWords hSyms hEval (sep_cast hm1 (by ac_rfl)) hQ
  · intro J1 hJ1; c0_hfast; exact hJ1 n.toNat (0#32, ⟨⟩) m
      ⟨ix, rfl, Nat.zero_le _, rfl, fun _ ht => by simp at ht,
        (by rw [hRsort]; exact sep_cast hm (by ac_rfl))⟩

/-! ## 4. Pass 1 WP (`buildR_pass1_wp`) & `ar_build_R_wp` Glue -/

theorem buildR_pass1_after (cx : BitVec 64) (v off cnt : BitVec 32)
    (fv_b any : Bool) (bt bw : BitVec 64) :
    (match ar_build_R_body Val Cont (cx, v, ()) with
      | @Expr.let_ _ _ _ [.bits 64] _ r0 => match r0 (0#64, ()) with
        | @Expr.load _ _ _ (.bits 64) _ r1 => match r1 0#64 with
          | @Expr.let_ _ _ _ [.bits 64] _ r2 => match r2 (0#64, ()) with
            | @Expr.let_ _ _ _ [.bits 64] _ r3 => match r3 (0#64, ()) with
              | @Expr.let_ _ _ _ [.bits 64] _ r4 => match r4 (0#64, ()) with
                | @Expr.load _ _ _ (.bits 32) _ r5 => match r5 off with
                  | @Expr.let_ _ _ _ [.bits 64] _ r6 => match r6 (0#64, ()) with
                    | @Expr.load _ _ _ (.bits 64) _ r7 => match r7 0#64 with
                      | @Expr.let_ _ _ _ [.bits 64] _ r8 => match r8 (0#64, ()) with
                        | @Expr.let_ _ _ _ [.bits 64] _ r9 => match r9 (0#64, ()) with
                          | @Expr.let_ _ _ _ [.bits 64] _ r10 => match r10 (0#64, ()) with
                            | @Expr.load _ _ _ (.bits 32) _ r11 => match r11 cnt with
                              | @Expr.let_ _ _ _ [.bits 64] _ r12 => match r12 (0#64, ()) with
                                | @Expr.load _ _ _ (.bits 64) _ r13 => match r13 0#64 with
                                  | @Expr.let_ _ _ _ [.bits 64] _ r14 => match r14 (0#64, ()) with
                                    | @Expr.let_ _ _ _ [.bits 64] _ r15 => match r15 (0#64, ()) with
                                      | @Expr.load _ _ _ (.bits 8) _ r16 => match r16 0#8 with
                                        | @Expr.let_ _ _ _ [.bits 8] _ r17 =>
                                          match r17 (0#8, ()) with
                                          | @Expr.let_ _ _ _ [.bits 32] _ r18 =>
                                            match r18 (0#32, ()) with
                                            | @Expr.let_ _ _ _ [.bits 32] _ r19 =>
                                              match r19 (0#32, ()) with
                                              | @Expr.let_ _ _ _ [.bool] _ r20 =>
                                                match r20 (fv_b, ()) with
                                                | @Expr.group _ _ _ [[.bits 64]] bs21 _ =>
                                                  match bs21 (fun _ _ => False, ()) with
                                                  | .cons b21 _ => match b21 (bw, ()) with
                                                    | @Expr.group _ _ _ [[.bits 64]] bs22 _ =>
                                                      match bs22 (fun _ _ => False, ()) with
                                                      | .cons b22 _ => match b22 (bt, ()) with
                                                        | @Expr.group _ _ _
                                                            [[.bool, .bits 64, .bits 64, .bits 32]]
                                                            bs23 _ =>
                                                          match bs23 (fun _ _ => False, ()) with
                                                          | .cons b23 _ =>
                                                            match b23 (any, bt, bw, cnt, ()) with
                                                            | @Expr.let_ _ _ _ [.bool] _ r24 =>
                                                              match r24 (false, ()) with
                                                              | .jnz _ _ eNF => match eNF with
                                                                | @Expr.group _ _ _ [[]] bsNF _ =>
                                                                  match bsNF
                                                                    (fun _ _ => False, ()) with
                                                                  | .cons bNF _ => bNF ()
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
                  | _ => .ret (Arg.imm false, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ()) : Expr Val Cont [.bool]) =
      buildRPass2EntryExpr cx v off cnt fv_b any bt bw := rfl

theorem bw_pass1_bound {rsPool rsM : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {off i cnt rsN rpcap : Nat} (hcnt : off + cnt ≤ rsN)
    (_hwords : monoTotalWords rsPool rsM rsN ≤ rpcap)
    (hmax : ∀ t < i, flipCount flippedArr (symListAt rsPool (rsM.getD (off + t) 0#32).toNat) ≤
      arRMaxF) (hi : i ≤ cnt) :
    ruleBw8 flippedArr rsPool rsM off i ≤ 2 ^ arRMaxF * monoTotalWords rsPool rsM rsN := by
  have hle : ruleBw8 flippedArr rsPool rsM off i ≤
      2 ^ arRMaxF * (List.range i).foldl (fun acc t =>
        acc + ((rsPool.getD (rsM.getD (off + t) 0#32).toNat 0#32).toNat + 1)) 0 := by
    induction i with
    | zero => simp [ruleBw8]
    | succ i ih =>
      rw [ruleBw8_succ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.mul_add]
      have h1 := ih (fun t ht => hmax t (Nat.lt_succ_of_lt ht)) (Nat.le_of_lt hi)
      have h2 : 2 ^ flipCount flippedArr (symListAt rsPool (rsM.getD (off + i) 0#32).toNat) ≤
          2 ^ arRMaxF := Nat.pow_le_pow_right (by decide) (hmax i (Nat.lt_succ_self i))
      have h3 := Nat.mul_le_mul_right
        ((rsPool.getD (rsM.getD (off + i) 0#32).toNat 0#32).toNat + 1) h2
      simp only [Nat.mul_add] at h1 h3 ⊢
      omega
  have hr : (List.range i).foldl (fun acc t =>
      acc + ((rsPool.getD (rsM.getD (off + t) 0#32).toNat 0#32).toNat + 1)) 0 ≤
      monoTotalWords rsPool rsM (off + cnt) := by
    clear hle
    have h1 : ∀ k, (List.range k).foldl (fun acc t =>
        acc + ((rsPool.getD (rsM.getD (off + t) 0#32).toNat 0#32).toNat + 1)) 0 =
        monoTotalWords rsPool rsM (off + k) - monoTotalWords rsPool rsM off := by
      intro k; induction k with
      | zero => simp
      | succ k ihk =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          show off + (k + 1) = (off + k) + 1 by omega, monoTotalWords_succ, ihk]
        have hmo : monoTotalWords rsPool rsM off ≤ monoTotalWords rsPool rsM (off + k) := by
          clear ihk
          induction k with
          | zero => exact le_refl _
          | succ k ihk2 =>
            rw [show off + (k + 1) = (off + k) + 1 by omega, monoTotalWords_succ]
            exact Nat.le_trans ihk2 (Nat.le_add_right _ _)
        omega
    have hm_le : monoTotalWords rsPool rsM (off + i) ≤ monoTotalWords rsPool rsM (off + cnt) := by
      have hinc : ∀ a b, a ≤ b → monoTotalWords rsPool rsM a ≤ monoTotalWords rsPool rsM b := by
        intro a b hab; induction hab with
        | refl => exact le_refl _
        | step _ ihs => rw [monoTotalWords_succ]; exact Nat.le_trans ihs (Nat.le_add_right _ _)
      exact hinc _ _ (by omega)
    rw [h1]; omega
  have hmn : monoTotalWords rsPool rsM (off + cnt) ≤ monoTotalWords rsPool rsM rsN := by
    have hinc : ∀ a b, a ≤ b → monoTotalWords rsPool rsM a ≤ monoTotalWords rsPool rsM b := by
      intro a b hab; induction hab with
      | refl => exact le_refl _
      | step _ ihs => rw [monoTotalWords_succ]; exact Nat.le_trans ihs (Nat.le_add_right _ _)
    exact hinc _ _ hcnt
  exact Nat.le_trans hle (Nat.mul_le_mul_left _ (Nat.le_trans hr hmn))

theorem bt_pass1_bound {rsPool rsM : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {off i : Nat}
    (hmax : ∀ t < i, flipCount flippedArr (symListAt rsPool (rsM.getD (off + t) 0#32).toNat) ≤
      arRMaxF) :
    ruleBt8 flippedArr rsPool rsM off i ≤ i * 2 ^ arRMaxF := by
  induction i with
  | zero => simp [ruleBt8]
  | succ i ih =>
    rw [ruleBt8_succ, Nat.succ_mul]
    have h1 := ih (fun t ht => hmax t (Nat.lt_succ_of_lt ht))
    have h2 : 2 ^ flipCount flippedArr (symListAt rsPool (rsM.getD (off + i) 0#32).toNat) ≤
        2 ^ arRMaxF := Nat.pow_le_pow_right (by decide) (hmax i (Nat.lt_succ_self i))
    omega

private theorem any_false_no_flips {flippedArr : List (BitVec 8)} {rsPool rsM : List (BitVec 32)}
    {off cnt : Nat}
    (hany : ∀ t < cnt,
      flipCount flippedArr (symListAt rsPool (rsM.getD (off + t) 0#32).toNat) = 0) :
    ruleBw8 flippedArr rsPool rsM off cnt =
      monoTotalWords rsPool rsM (off + cnt) - monoTotalWords rsPool rsM off := by
  induction cnt with
  | zero => simp [ruleBw8]
  | succ cnt ih =>
    have h0 := hany cnt (Nat.lt_succ_self cnt)
    rw [ruleBw8_succ, ih (fun t ht => hany t (Nat.lt_succ_of_lt ht)), h0, Nat.pow_zero, Nat.one_mul,
      show off + (cnt + 1) = (off + cnt) + 1 by omega, monoTotalWords_succ]
    have hmo : monoTotalWords rsPool rsM off ≤ monoTotalWords rsPool rsM (off + cnt) := by
      have hinc : ∀ a b, a ≤ b → monoTotalWords rsPool rsM a ≤ monoTotalWords rsPool rsM b := by
        intro a b hab; induction hab with
        | refl => exact le_refl _
        | step _ ihs => rw [monoTotalWords_succ]; exact Nat.le_trans ihs (Nat.le_add_right _ _)
      exact hinc _ _ (Nat.le_add_right _ _)
    omega

theorem pass1_bv64_bt_step {bt : BitVec 64} {f : BitVec 32}
    (hf : f.toNat ≤ arRMaxF) (hbt : bt.toNat + 2 ^ f.toNat < 2 ^ 64) :
    (bt + (1#64 <<< (BitVec.setWidth 64 f))).toNat = bt.toNat + 2 ^ f.toNat := by
  have hf64 : (BitVec.setWidth 64 f).toNat = f.toNat := bv64_zext32 f
  have hshl : (1#64 <<< (BitVec.setWidth 64 f)).toNat = 2 ^ f.toNat := by
    rw [bv_c0_toNat_shiftLeft_bv, hf64, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.one_mul,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hf) (by decide))]
  rw [BitVec.toNat_add, hshl, Nat.mod_eq_of_lt hbt]

theorem pass1_bv64_bw_step {bw : BitVec 64} {f mlen : BitVec 32}
    (hf : f.toNat ≤ arRMaxF) (hbw : bw.toNat + 2 ^ f.toNat * (mlen.toNat + 1) < 2 ^ 64) :
    (bw + (1#64 <<< (BitVec.setWidth 64 f)) * (BitVec.setWidth 64 mlen + 1#64)).toNat =
      bw.toNat + 2 ^ f.toNat * (mlen.toNat + 1) := by
  have hf64 : (BitVec.setWidth 64 f).toNat = f.toNat := bv64_zext32 f
  have hm64 : (BitVec.setWidth 64 mlen).toNat = mlen.toNat := bv64_zext32 mlen
  have hshl : (1#64 <<< (BitVec.setWidth 64 f)).toNat = 2 ^ f.toNat := by
    rw [bv_c0_toNat_shiftLeft_bv, hf64, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.one_mul,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hf) (by decide))]
  have hm1 : (BitVec.setWidth 64 mlen + 1#64).toNat = mlen.toNat + 1 := by
    rw [BitVec.toNat_add, hm64, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (lt_trans (Nat.add_lt_add_right mlen.isLt 1) (by decide))]
  have hmul : ((1#64 <<< (BitVec.setWidth 64 f)) * (BitVec.setWidth 64 mlen + 1#64)).toNat =
      2 ^ f.toNat * (mlen.toNat + 1) := by
    rw [BitVec.toNat_mul, hshl, hm1, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, hmul, Nat.mod_eq_of_lt hbw]

end

end LeanQbe.T.Examples.Arisca.Proof
