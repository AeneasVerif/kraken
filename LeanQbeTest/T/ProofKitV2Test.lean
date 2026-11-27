module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.ProofKit

/-!
# Verification Suite for `ProofKit` v2 + `C0HeadStep` Extensions

Exercises:
1. `U32Kit`, `c0_bv32_omega`, narrowing `setWidth`/`truncate`, nonneg/concrete `signExtend`,
   and goal-driven `c0_bv_omega` on 6-deep chained subtractions with heavy WP distractors.
2. `KissatHdrBitMaskKit`, `PWordKit`, and `pword_mask` pure-kernel bitmask orthogonality
   and 64-bit / 32-bit Kissat-style flag packing (`std3` axioms only; pure-kernel).
3. `c0_guard_exit`, `c0_hguard_exit`, and `c0_hstraight` (bare and `(exit := tac)`) on
   cascading early-return C0 functions and a 50-level nested early-return guard cascade.
4. `wp_while_record`, `wp_while_record_init`, `wp_jump_record`, and multi-arm join combinators
   (`wp_join_dag`, `wp_join3`, `wp_join_ite`, `wp_join_seq`, `C0JoinTree`, `wp_join_tree`).
5. `check_std_axioms!` verifying every test theorem uses only `std3`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.ProofKitV2Test

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofKit.U32Kit
open LeanQbe.T.ProofKit.KissatHdrBitMaskKit
open LeanQbe.T.ProofKit.PWordKit
open LeanQbe.T.Frontend.C0
open LeanQbe.T.C0HeadStep

/-! ## 1. `U32Kit`, `c0_bv32_omega`, `signExtend`, & Chained Subtraction `c0_bv_omega` -/

public section

theorem u32kit_roundtrips_and_bounds (x y : BitVec 32) (z : BitVec 64)
    (hxy : x.toNat + y.toNat < 2 ^ 32) (hyx : y.toNat ≤ x.toNat)
    (hz : z.toNat < 2 ^ 32) (hx31 : x.toNat < 2 ^ 31) :
    (x.setWidth 64).setWidth 32 = x ∧
    (x.setWidth 64).truncate 32 = x ∧
    (z.truncate 32).setWidth 64 = z ∧
    (x + y).setWidth 64 = x.setWidth 64 + y.setWidth 64 ∧
    (x - y).setWidth 64 = x.setWidth 64 - y.setWidth 64 ∧
    (z + (1#64)).truncate 32 = z.truncate 32 + 1#32 ∧
    (((x <<< 1) ||| 1#32) >>> 1).toNat = x.toNat := by
  refine ⟨bv32_setWidth64_setWidth32 x, bv32_setWidth64_truncate32 x,
    bv64_truncate32_setWidth64_of_lt hz, bv32_setWidth64_add_of_lt hxy,
    bv32_setWidth64_sub_of_le hyx, bv64_add_truncate32 z 1#64,
    bv32_shl1_or_one_ushiftRight1 hx31⟩

theorem bv32_omega_casts_shifts_signExtend (x y : BitVec 32) (z : BitVec 64)
    (a b c : UInt32) (hx : x.toNat + y.toNat < 2 ^ 32) (hz : z.toNat < 2 ^ 32)
    (hx31 : x.toNat < 2 ^ 31) (h1 : b ≤ a) (h2 : c ≤ a - b)
    (hmul : x.toNat * 4 < 2 ^ 32) :
    ((x.setWidth 64 + y.setWidth 64).truncate 32).toNat = x.toNat + y.toNat ∧
    (z.setWidth 32).toNat = z.toNat ∧
    (x.signExtend 64).toNat = x.toNat ∧
    ((BitVec.ofNat 32 0xFFFFFFFF).signExtend 64).toNat = 0xFFFFFFFFFFFFFFFF ∧
    (a - b - c).toNat = a.toNat - b.toNat - c.toNat ∧
    (x <<< 2).toNat = 4 * x.toNat ∧
    (a.toUInt64.toNat = a.toNat) := by
  have _ := hx31
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · c0_bv32_omega
  · c0_bv32_omega [hz]
  · c0_bv32_omega [hx31]
  · c0_bv32_omega
  · c0_bv32_omega [h1, h2]
  · c0_bv32_omega
  · c0_bv32_omega

theorem u32_xor_one_pair_bound (lit : BitVec 32) {nvars : Nat} (hlit : lit.toNat < 2 * nvars) :
    (lit ^^^ 1#32).toNat < 2 * nvars :=
  bv32_xor_one_lt hlit

theorem chained_sub_with_wp_distractors (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64)
    (ptr : BitVec 64) (hm : (cell64 ptr 7#64) m)
    (hwp : wp Γ Q X (.load i64 (.var ptr) fun v => .ret (.var v, ())) m)
    (a b c d e f : BitVec 64)
    (h1 : b.toNat ≤ a.toNat) (h2 : c.toNat ≤ a.toNat - b.toNat)
    (h3 : d.toNat ≤ a.toNat - b.toNat - c.toNat)
    (h4 : e.toNat ≤ a.toNat - b.toNat - c.toNat - d.toNat)
    (h5 : f.toNat ≤ a.toNat - b.toNat - c.toNat - d.toNat - e.toNat) :
    (((((a - b) - c) - d) - e) - f).toNat =
      a.toNat - b.toNat - c.toNat - d.toNat - e.toNat - f.toNat := by
  let _ := hm; let _ := hwp
  c0_bv_omega

theorem chained_sub_explicit_hyps (a b c d : BitVec 64)
    (h1 : b.toNat ≤ a.toNat) (h2 : c.toNat ≤ a.toNat - b.toNat)
    (h3 : d.toNat ≤ a.toNat - b.toNat - c.toNat) (unrelated : BitVec 64)
    (hunrel : unrelated.toNat = 999) :
    (((a - b) - c) - d).toNat ≤ a.toNat - b.toNat := by
  let _ := hunrel
  c0_bv_omega [h1, h2, h3]

end

/-! ## 2. `KissatHdrBitMaskKit`, `PWordKit`, & `pword_mask` (Pure Kernel `std3`) -/

public section

theorem kissat_general_mask_orthogonality {w : Nat} (x v m1 m2 : BitVec w)
    (hdisj : (m1 &&& m2) = 0#w) (hv : (v &&& m1) = v) (hv2 : (v &&& m2) = 0#w) :
    ((x &&& ~~~m1) &&& m2) = (x &&& m2) ∧
    ((x ||| v) &&& m2) = (x &&& m2) ∧
    (((x &&& ~~~m1) ||| v) &&& m2) = (x &&& m2) ∧
    (((x &&& ~~~m1) ||| v) &&& m1) = v :=
  ⟨bv_and_not_and_of_disjoint hdisj, bv_or_and_of_disjoint hv2,
   bv_clear_or_and_other hdisj hv2, bv_clear_or_and_self hv⟩

theorem kissat_single_bit_orthogonality {w : Nat} (x : BitVec w) {k j : Nat}
    (hk : k < w) (hj : j < w) (hne : k ≠ j) :
    ((x ||| (1#w <<< k)) &&& (1#w <<< j)) = (x &&& (1#w <<< j)) ∧
    ((x &&& ~~~(1#w <<< k)) &&& (1#w <<< j)) = (x &&& (1#w <<< j)) ∧
    ((x ^^^ (1#w <<< k)) &&& (1#w <<< j)) = (x &&& (1#w <<< j)) ∧
    ((x ||| (1#w <<< k)) &&& (1#w <<< k)) ≠ 0#w ∧
    ((x &&& ~~~(1#w <<< k)) &&& (1#w <<< k)) = 0#w :=
  ⟨bv_set_bit_test_ne x hk hj hne, bv_clear_bit_test_ne x hk hj hne,
   bv_toggle_bit_test_ne x hk hj hne, bv_set_bit_test_self x hk,
   bv_clear_bit_test_self x hk⟩

theorem kissat64_hdr_pack_clear_set (hdr tag : BitVec 64) (htag : tag.toNat < 2 ^ 8) :
    let h1 := ((hdr &&& ~~~0xFF#64) ||| tag)
    let h2 := ((h1 &&& ~~~(1#64 <<< 62)) ||| (1#64 <<< 63))
    (h2 &&& (1#64 <<< 63)) = (1#64 <<< 63) ∧
    (h2 &&& (1#64 <<< 62)) = 0#64 ∧
    (h2 &&& 0xFF00#64) = (hdr &&& 0xFF00#64) ∧
    (h2 &&& 0xFF#64) = tag ∧
    h2 ≠ 0#64 ∧
    h2 ≠ BitVec.allOnes 64 := by
  intro h1 h2
  have htagMask : (tag &&& 0xFF#64) = tag := bv_mask_low_bits_eq_self (by decide) htag
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [h2, h1]; pword_mask
  · dsimp only [h2, h1]; pword_mask
  · dsimp only [h2, h1]; pword_mask [htagMask]
  · dsimp only [h2, h1]; pword_mask [htagMask]
  · dsimp only [h2, h1]; pword_mask
  · dsimp only [h2, h1]
    apply bv_ne_of_and_ne (m := 1#64 <<< 62)
    pword_mask

theorem kissat32_pword_flags_pure (pw val : BitVec 32) (hval : val.toNat < 2 ^ 23) :
    let packed := ((pw &&& 0x80000000#32) ||| val)
    (packed &&& 0x80000000#32) = (pw &&& 0x80000000#32) ∧
    (packed &&& 0x007FFFFF#32) = val ∧
    (((packed ||| 0x40000000#32) &&& ~~~0x20000000#32) ≠ 0#32) ∧
    (((packed ||| 0x40000000#32) &&& ~~~0x20000000#32) ≠ 0xFFFFFFFF#32) := by
  intro packed
  have hv23 : (val &&& 0x007FFFFF#32) = val := bv_mask_low_bits_eq_self (by decide) hval
  have hv31 : val.toNat < 2 ^ 31 := Nat.lt_of_lt_of_le hval (by decide)
  refine ⟨bv32_pword_pack_flag hv31, ?_, ?_, ?_⟩
  · dsimp only [packed]; pword_mask [hv23]
  · dsimp only [packed]; pword_mask
  · dsimp only [packed]; pword_mask

theorem packed_field_extract_update_props (x v : BitVec 64) (hv : v.toNat < 2 ^ 8) :
    let mask := BitVec.ofNat 64 (2 ^ 8 - 1) <<< 16
    let updated := (x &&& ~~~mask) ||| (v <<< 16)
    updated.getLsbD 19 = v.getLsbD 3 ∧
    updated.getLsbD 5 = x.getLsbD 5 ∧
    ((updated &&& mask) >>> 16).toNat < 2 ^ 8 := by
  intro mask updated
  refine ⟨?_, ?_, ?_⟩
  · exact bv_packed_update_getLsbD_in (off := 16) (len := 8) x v
      (by decide) hv (by decide) (by decide)
  · exact bv_packed_update_getLsbD_out (off := 16) (len := 8) x v
      (by decide) hv (by decide) (Or.inl (by decide))
  · exact bv64_pword_extract_lt updated (by decide)

end

/-! ## 3. `c0_guard_exit`, `c0_hguard_exit`, `c0_hstraight`, & 50-Level Cascade -/

section GuardExitTests

c0_decl! "
u64 c0_guard_demo(u64 a, u64 b) {
  if (a == 0) return 10;
  if (b < 3) return 20;
  if (a < b) return 30;
  return a - b;
}
u64 c0_guard_mem_demo(u64 *out, u64 x, u64 y) {
  if (x < 10) return 1;
  if (y == 0) return 2;
  *out = x / y;
  return 0;
}
"

public section

theorem c0_guard_demo_bare (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64)
    (a b : BitVec 64)
    (h10 : a = 0#64 → Q (10#64, ()) m)
    (h20 : a ≠ 0#64 → b.toNat < 3 → Q (20#64, ()) m)
    (h30 : a ≠ 0#64 → ¬b.toNat < 3 → a.toNat < b.toNat → Q (30#64, ()) m)
    (hok : a ≠ 0#64 → ¬b.toNat < 3 → ¬a.toNat < b.toNat → Q (a - b, ()) m) :
    Func.wp Γ c0_guard_demo_body (a, b, ()) m Q X := by
  c0_guard_exit
  · exact h10 (by simpa using hc)
  · exact h20 (by intro ha; simp_all) hc
  · exact h30 (by intro ha; simp_all) (by simp_all) hc
  · exact hok (by intro ha; simp_all) (by simp_all) hc

theorem c0_guard_demo_auto_exit (Γ : Env) (X : XPost) (m : Mem 64) (a b : BitVec 64)
    (ha : a ≠ 0#64) (hb : 3 ≤ b.toNat) (hle : b.toNat ≤ a.toNat) :
    Func.wp Γ c0_guard_demo_body (a, b, ()) m
      (fun (r : Tup Val [i64]) m' => m' = m ∧ r.fst.toNat = a.toNat - b.toNat) X := by
  c0_hguard_exit (exit := by exfalso; first | exact ha (by simpa using hc) | c0_bv_omega)
  refine ⟨rfl, ?_⟩
  dsimp only
  c0_bv_omega

theorem c0_guard_mem_hstraight (Γ : Env) (X : XPost) (out v0 x y : BitVec 64)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (cell (t := i64) out v0 ⋆ R) m)
    (hx : 10 ≤ x.toNat) (hy : y ≠ 0#64) :
    Func.wp Γ c0_guard_mem_demo_body (out, x, y, ()) m
      (fun (r : Tup Val [i64]) m' =>
        r.fst = 0#64 ∧ (cell (t := i64) out (x / y) ⋆ R) m') X := by
  c0_hstraight (exit := by
    exfalso
    first
    | exact hy (by simpa using hc)
    | (c0_bv_omega [hx]))
  exact ⟨rfl, by assumption⟩

end

public section

/-- Build an `n`-level early-return guard cascade (`jnz` -> `.ret err`) followed by `.ret ok`. -/
def mkGuardCascade : Nat → Val i64 → Val i64 → Expr Val Cont [i64]
  | 0, x, y =>
      .let_ (op2 (.add i64) (.var x) (.var y)) fun (r, ()) => .ret (.var r, ())
  | k + 1, x, y =>
      let thresh := BitVec.ofNat 64 k
      .let_ (op2 (.ult i64) (.var x) (.imm thresh)) fun (c, ()) =>
      .jnz (.var c)
        (.ret (.imm thresh, ()))
        (mkGuardCascade k x y)

end

public section

theorem guard_cascade50_exit_close (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64)
    (x y : BitVec 64) (hx : 50 ≤ x.toNat)
    (hQ : Q (x + y, ()) m) :
    wp Γ Q X (mkGuardCascade 50 x y) m := by
  dsimp only [mkGuardCascade]
  c0_guard_exit (exit := by exfalso; c0_bv_omega [hx])
  exact hQ

theorem guard_cascade12_bare (Γ : Env) (X : XPost) (m : Mem 64) (x y : BitVec 64)
    (hx : 12 ≤ x.toNat) :
    wp Γ (fun (r : Tup Val [i64]) m' => m' = m ∧ r.fst = x + y) X
      (mkGuardCascade 12 x y) m := by
  dsimp only [mkGuardCascade]
  c0_hguard_exit
  all_goals
    first
    | (exfalso; c0_bv_omega [hx])
    | exact ⟨rfl, rfl⟩

end

end GuardExitTests

/-! ## 4. `wp_while_record` (Non-Slot-0 Cursor) & Multi-Arm `C0JoinTree` Combinators -/

section RecordLoopAndJoinTests

c0_decl! "
u64 sum_non_slot0(u64 *arr, u64 tag, u64 idx, u64 lim) {
  u64 acc = tag;
  while (idx < lim) {
    u64 v = arr[idx];
    acc = acc + v;
    idx = idx + 1;
  }
  return acc;
}
u64 seq_joins(u64 x, u64 a, u64 b) {
  u64 r = x;
  if (a != 0) { r = r + 1; } else { r = r + 2; }
  if (b != 0) { r = r + 10; } else { r = r + 20; }
  return r;
}
u64 multi_branch_join(u64 a, u64 b) {
  u64 r = 0;
  if (a == 0) {
    if (b == 0) { r = 100; } else { r = 101; }
  } else {
    if (b < 5) { r = 200; } else { r = 201; }
  }
  return r + 1;
}
"

public section

structure SumLoopSt where
  idx : Nat
  lim : Nat
  acc : BitVec 64
  xs : List (BitVec 64)

def sumFrom : Nat → Nat → List (BitVec 64) → BitVec 64 → BitVec 64
  | 0, _, _, acc => acc
  | n + 1, i, xs, acc => sumFrom n (i + 1) xs (acc + xs.getD i 0#64)

def multiDagExpr (x : BitVec 64) : Expr Val Cont [i64] :=
  .group (sig := [[i64], [i64], [i64]])
    (fun (_J0, J1, J2, ()) =>
      Blocks.cons (fun (a, ()) =>
        .let_ (op2 (.add i64) (.var a) (.imm 1#64)) fun (b, ()) => .jump J1 (.var b, ()))
      (Blocks.cons (fun (a, ()) =>
        .let_ (op2 (.add i64) (.var a) (.imm 2#64)) fun (b, ()) => .jump J2 (.var b, ()))
      (Blocks.cons (fun (a, ()) => .ret (.var a, ())) .nil)))
    fun (J0, _, _, ()) => .jump J0 (.var x, ())

def multiArm3Expr (b0 b1 : Bool) (x : BitVec 64) : Expr Val Cont [i64] :=
  .group (sig := [[i64], [i64], [i64]])
    (fun (_, _, _, ()) =>
      Blocks.cons (fun (a, ()) => .ret (.var (a + 1#64), ()))
      (Blocks.cons (fun (a, ()) => .ret (.var (a + 2#64), ()))
      (Blocks.cons (fun (a, ()) => .ret (.var (a + 3#64), ())) .nil)))
    fun (J0, J1, J2, ()) =>
      .jnz (.var b0) (.jump J0 (.var x, ()))
        (.jnz (.var b1) (.jump J1 (.var x, ())) (.jump J2 (.var x, ())))

def joinTreeBranchExpr (b0 b1 : Bool) (x : BitVec 64) : Expr Val Cont [i64] :=
  .group (sig := [[i64]])
    (fun _ => Blocks.cons (fun (a, ()) => .ret (.var a, ())) .nil)
    fun (J, ()) =>
      .jnz (.var b0)
        (.jump J (.var x, ()))
        (.jnz (.var b1) (.jump J (.var (x + 10#64), ())) (.ret (.imm 99#64, ())))

def joinIteExpr (b : Bool) (x y : BitVec 64) : Expr Val Cont [i64] :=
  .group (sig := [[i64]])
    (fun _ => Blocks.cons (fun (a, ()) => .ret (.var a, ())) .nil)
    fun (J, ()) => .jnz (.var b) (.jump J (.var x, ())) (.jump J (.var y, ()))

end

public section

private theorem sumFrom_step {n i : Nat} {xs : List (BitVec 64)} {acc : BitVec 64}
    (hlt : i < xs.length) :
    sumFrom (n + 1) i xs acc = sumFrom n (i + 1) xs (acc + xs[i]) := by
  simp only [sumFrom]
  rw [List.getD_eq_getElem?_getD, list_getElem?_getD_of_lt hlt]

theorem sum_non_slot0_wp (Γ : Env) (X : XPost) (arr tag : BitVec 64) (idx lim : Nat)
    (xs : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64)
    (hlen : lim ≤ xs.length) (hlim : lim < 2 ^ 64) (hle : idx ≤ lim)
    (hm : (array64 arr xs ⋆ R) m) :
    Func.wp Γ sum_non_slot0_body (arr, tag, BitVec.ofNat 64 idx, BitVec.ofNat 64 lim, ()) m
      (fun (res : Tup Val [i64]) m' =>
        res.fst = sumFrom (lim - idx) idx xs tag ∧ (array64 arr xs ⋆ R) m')
      X := by
  unfold Func.wp sum_non_slot0_body
  let st₀ : SumLoopSt := { idx := idx, lim := lim, acc := tag, xs := xs }
  let proj : SumLoopSt → Tup Val [i64, i64] := fun st =>
    (BitVec.ofNat 64 st.idx, st.acc, ())
  let Inv : SumLoopSt → Prop := fun st =>
    st.xs = xs ∧ st.lim = lim ∧ st.idx ≤ st.lim ∧
    sumFrom (st.lim - st.idx) st.idx st.xs st.acc = sumFrom (lim - idx) idx xs tag
  let MemPred : SumLoopSt → Mem 64 → Prop := fun st => array64 arr st.xs
  refine wp_while_record_init st₀ proj (fun st => st.lim - st.idx) Inv MemPred R
    ⟨rfl, rfl, hle, rfl⟩ hm ?_ ?_
  · intro J hi₀ hm₀ hJ
    c0_hsteps_nogrp
    exact hJ st₀ m hi₀ hm₀
  · intro J st ml ⟨hxs, hlim_eq, hidx_le, hsum⟩ hm_st ih
    dsimp only [proj]
    c0_hsplit
    · c0_hsteps_nogrp
      have hidx_lt : st.idx < st.lim := by c0_bv_omega
      have hi_lt : st.idx < st.xs.length := by rw [hxs, hlim_eq] at *; omega
      have haddr : arr + BitVec.ofNat 64 st.idx * 8#64 =
          arr + BitVec.ofNat 64 (8 * st.idx) := by
        apply congrArg (arr + ·)
        apply BitVec.eq_of_toNat_eq
        c0_bv_omega
      have hld : loadVal ml i64 (arr + BitVec.ofNat 64 st.idx * 8#64) =
          some st.xs[st.idx] :=
        haddr ▸ loadVal_array64 hi_lt hm_st
      refine head_wp_load rfl hld ?_
      c0_hsteps_nogrp
      let st' : SumLoopSt :=
        { idx := st.idx + 1, lim := st.lim, acc := st.acc + st.xs[st.idx], xs := st.xs }
      have hlt_meas : st'.lim - st'.idx < st.lim - st.idx := by dsimp only [st']; c0_bv_omega
      have hsum' : sumFrom (st'.lim - st'.idx) st'.idx st'.xs st'.acc =
          sumFrom (lim - idx) idx xs tag := by
        dsimp only [st']
        have hdiff : st.lim - st.idx = (st.lim - (st.idx + 1)) + 1 := by c0_bv_omega
        rw [← hsum, hdiff]
        exact (sumFrom_step hi_lt).symm
      have hi' : Inv st' := ⟨hxs, hlim_eq, by dsimp only [st']; c0_bv_omega, hsum'⟩
      have hjump : (BitVec.ofNat 64 st.idx + (BitVec.ofNat 32 1).signExtend 64,
          st.acc + st.xs[st.idx], ()) = proj st' := by
        dsimp only [proj, st']
        congr 1
        apply BitVec.eq_of_toNat_eq
        c0_bv_omega
      exact hjump ▸ ih st' ml hlt_meas hi' hm_st
    · c0_hsteps_nogrp
      have heq : st.idx = st.lim := by c0_bv_omega
      have hzero : st.lim - st.idx = 0 := by omega
      rw [hzero, sumFrom] at hsum
      exact ⟨hsum, hxs ▸ hm_st⟩

theorem jump_record_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {ml : Mem 64}
    {J : Cont [i64, i64]} (st : SumLoopSt) (Inv : SumLoopSt → Prop)
    (MemPred : SumLoopSt → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hi : Inv st) (hm : (MemPred st ⋆ R) ml)
    (hJ : ∀ st' ml', Inv st' → (MemPred st' ⋆ R) ml' →
      J (BitVec.ofNat 64 st'.idx, st'.acc, ()) ml') :
    wp Γ Q X (.jump J (.var (BitVec.ofNat 64 st.idx), .var st.acc, ())) ml :=
  wp_jump_record st rfl hi hm hJ

theorem seq_joins_wp (Γ : Env) (X : XPost) (m : Mem 64) (x a b : BitVec 64) :
    Func.wp Γ seq_joins_body (x, a, b, ()) m
      (fun (r : Tup Val [i64]) m' =>
        m' = m ∧
        r.fst = x + (if a != 0#64 then 1#64 else 2#64) + (if b != 0#64 then 10#64 else 20#64))
      X := by
  unfold Func.wp seq_joins_body
  let P₁ : Tup Val [i64] → Mem 64 → Prop := fun xs₁ m₁ =>
    m₁ = m ∧ xs₁.1 = x + (if a != 0#64 then 1#64 else 2#64)
  let P₂ : Tup Val [i64] → Tup Val [i64] → Mem 64 → Prop := fun _ xs₂ m₂ =>
    m₂ = m ∧ xs₂.1 = x + (if a != 0#64 then 1#64 else 2#64) + (if b != 0#64 then 10#64 else 20#64)
  refine wp_join_seq P₁ P₂ ?_ ?_ ?_
  · rintro J₁ ⟨r1, ⟨⟩⟩ J₂ ⟨r2, ⟨⟩⟩ m₂ ⟨hm₂, hr₂⟩
    c0_hsteps_nogrp
    exact ⟨hm₂, hr₂⟩
  · rintro J₁ J₂ ⟨r1, ⟨⟩⟩ m₁ hJ₂ ⟨hm₁, hr₁⟩
    c0_hsteps_nogrp
    c0_hsplit
    · c0_hsteps_nogrp; apply hJ₂; refine ⟨hm₁, ?_⟩
      have hne : (b != 0#64) = true := by simpa using hc
      dsimp only at hr₁ ⊢
      simp [hr₁, hne]
    · c0_hsteps_nogrp; apply hJ₂; refine ⟨hm₁, ?_⟩
      have heq : (b != 0#64) = false := by simpa using hc
      dsimp only at hr₁ ⊢
      simp [hr₁, heq]
  · intro J₁ hJ₁
    c0_hsteps_nogrp
    c0_hsplit
    · c0_hsteps_nogrp; apply hJ₁; refine ⟨rfl, ?_⟩
      have hne : (a != 0#64) = true := by simpa using hc
      simp [hne]
    · c0_hsteps_nogrp; apply hJ₁; refine ⟨rfl, ?_⟩
      have heq : (a != 0#64) = false := by simpa using hc
      simp [heq]

theorem multi_branch_tree_wp (Γ : Env) (X : XPost) (m : Mem 64) (a b : BitVec 64) :
    Func.wp Γ multi_branch_join_body (a, b, ()) m
      (fun (r : Tup Val [i64]) m' =>
        m' = m ∧
        r.fst = (if a == 0#64 then (if b == 0#64 then 100#64 else 101#64)
                 else (if b.ult 5#64 then 200#64 else 201#64)) + 1#64)
      X := by
  unfold Func.wp multi_branch_join_body
  c0_hsteps_nogrp
  let P : Tup Val [i64] → Mem 64 → Prop := fun xs m' =>
    m' = m ∧
    xs.1 = if a == 0#64 then (if b == 0#64 then 100#64 else 101#64)
           else (if b.ult 5#64 then 200#64 else 201#64)
  refine wp_join_tree P ?_ ?_
  · rintro J ⟨r, ⟨⟩⟩ m' ⟨hm', hr⟩
    c0_hsteps_nogrp
    exact ⟨hm', by dsimp only at hr ⊢; rw [hr]⟩
  · intro J
    apply C0JoinTree.leaf
    intro hJ
    c0_hstraight
    c0_hsplit
    · have ha : (a == 0#64) = true := by simpa using hc
      clear hc
      c0_hstraight
      apply C0JoinTree.wp hJ
      refine C0JoinTree.group P ?_ ?_
      · rintro J' ⟨r, ⟨⟩⟩ m' hP
        c0_hsteps_nogrp
        exact C0JoinTree.jump hP
      · intro J' hJ'
        apply C0JoinTree.leaf
        intro _
        c0_hstraight
        c0_hsplit
        · c0_hsteps_nogrp; apply hJ'; refine ⟨rfl, ?_⟩
          have hb : (b == 0#64) = true := by simpa using hc
          simp [ha, hb]
        · c0_hsteps_nogrp; apply hJ'; refine ⟨rfl, ?_⟩
          have hb : (b == 0#64) = false := by simpa using hc
          simp [ha, hb]
    · have ha : (a == 0#64) = false := by simpa using hc
      clear hc
      c0_hstraight
      apply C0JoinTree.wp hJ
      refine C0JoinTree.group P ?_ ?_
      · rintro J' ⟨r, ⟨⟩⟩ m' hP
        c0_hsteps_nogrp
        exact C0JoinTree.jump hP
      · intro J' hJ'
        apply C0JoinTree.leaf
        intro _
        c0_hstraight
        c0_hsplit
        · c0_hsteps_nogrp; apply hJ'; refine ⟨rfl, ?_⟩
          have hb : b.ult 5#64 = true := by simp [BitVec.ult, hc]
          simp [ha, hb]
        · c0_hsteps_nogrp; apply hJ'; refine ⟨rfl, ?_⟩
          have hb : b.ult 5#64 = false := by
            simp only [BitVec.ult, BitVec.reduceToNat, decide_eq_false_iff_not]
            omega
          simp [ha, hb]

theorem multi_dag_wp (Γ : Env) (X : XPost) (m : Mem 64) (x : BitVec 64) :
    wp Γ (fun (r : Tup Val [i64]) m' => m' = m ∧ r.fst = x + 3#64) X (multiDagExpr x) m := by
  dsimp only [multiDagExpr]
  let P0 : Cont [i64] := fun v m' => m' = m ∧ v.1 = x
  let P1 : Cont [i64] := fun v m' => m' = m ∧ v.1 = x + 1#64
  let P2 : Cont [i64] := fun v m' => m' = m ∧ v.1 = x + 3#64
  let rank : ∀ {ts}, Member ts [[i64], [i64], [i64]] → Nat := fun {ts} i =>
    match i with
    | .here => 2
    | .there .here => 1
    | .there (.there .here) => 0
    | .there (.there (.there j)) => nomatch j
  refine wp_join_dag (P0, P1, P2, ()) rank ?_ ?_
  · rintro ⟨J0, J1, J2, ⟨⟩⟩ ts i hrec xs ml hs
    cases i with
    | here =>
      let ⟨a, ⟨⟩⟩ := xs
      change P0 (a, ()) ml at hs
      dsimp only [P0] at hs
      c0_hsteps_nogrp
      exact hrec (.there .here) (by decide) (a + 1#64, ()) ml ⟨hs.1, by rw [hs.2]⟩
    | there i =>
      cases i with
      | here =>
        let ⟨a, ⟨⟩⟩ := xs
        change P1 (a, ()) ml at hs
        dsimp only [P1] at hs
        c0_hsteps_nogrp
        refine hrec (.there (.there .here)) (by decide) (a + 2#64, ()) ml ⟨hs.1, ?_⟩
        rw [hs.2, BitVec.add_assoc]; rfl
      | there i =>
        cases i with
        | here =>
          let ⟨a, ⟨⟩⟩ := xs
          c0_hsteps_nogrp
          exact hs
        | there i => cases i
  · rintro ⟨J0, _, _, ⟨⟩⟩ hJs
    c0_hsteps_nogrp
    exact hJs .here (x, ()) m ⟨rfl, rfl⟩

theorem multi_arm3_wp (Γ : Env) (X : XPost) (m : Mem 64) (b0 b1 : Bool) (x : BitVec 64) :
    wp Γ (fun (r : Tup Val [i64]) m' =>
      m' = m ∧ r.fst = if b0 then x + 1#64 else if b1 then x + 2#64 else x + 3#64) X
      (multiArm3Expr b0 b1 x) m := by
  dsimp only [multiArm3Expr]
  let P0 : Cont [i64] := fun v m' => m' = m ∧ v.1 = x ∧ b0 = true
  let P1 : Cont [i64] := fun v m' => m' = m ∧ v.1 = x ∧ b0 = false ∧ b1 = true
  let P2 : Cont [i64] := fun v m' => m' = m ∧ v.1 = x ∧ b0 = false ∧ b1 = false
  refine wp_join3 P0 P1 P2 ?_ ?_ ?_ ?_
  · intro _ _ _ ⟨a, ⟨⟩⟩ ml h
    c0_hsteps_nogrp; dsimp only [P0] at h; exact ⟨h.1, by simp [h.2]⟩
  · intro _ _ _ ⟨a, ⟨⟩⟩ ml h
    c0_hsteps_nogrp; dsimp only [P1] at h; exact ⟨h.1, by simp [h.2]⟩
  · intro _ _ _ ⟨a, ⟨⟩⟩ ml h
    c0_hsteps_nogrp; dsimp only [P2] at h; exact ⟨h.1, by simp [h.2]⟩
  · intro J0 J1 J2 h0 h1 h2
    c0_hstraight
    c0_hsplit
    · c0_hsteps_nogrp; apply h0; exact ⟨rfl, rfl, by simpa using hc⟩
    · have hb0 : b0 = false := by simpa using hc
      clear hc
      c0_hstraight
      c0_hsplit
      · c0_hsteps_nogrp
        apply h1
        exact ⟨rfl, rfl, hb0, by simpa using hc⟩
      · c0_hsteps_nogrp
        apply h2
        exact ⟨rfl, rfl, hb0, by simpa using hc⟩

theorem join_ite_and_tree_constructors_wp (Γ : Env) (X : XPost) (m : Mem 64)
    (b0 b1 : Bool) (x : BitVec 64) :
    wp Γ (fun (r : Tup Val [i64]) m' =>
      m' = m ∧ r.fst = if b0 then x else if b1 then x + 10#64 else 99#64) X
      (joinTreeBranchExpr b0 b1 x) m := by
  dsimp only [joinTreeBranchExpr]
  let P : Tup Val [i64] → Mem 64 → Prop := fun xs m' =>
    m' = m ∧ (b0 = true ∧ xs.1 = x ∨ b0 = false ∧ b1 = true ∧ xs.1 = x + 10#64)
  refine wp_join_tree P ?_ ?_
  · rintro J ⟨r, ⟨⟩⟩ m' ⟨hm', hdisj⟩
    c0_hsteps_nogrp
    dsimp only at hdisj ⊢
    rcases hdisj with ⟨hb0, hr⟩ | ⟨hb0, hb1, hr⟩
    · exact ⟨hm', by simp [hb0, hr]⟩
    · exact ⟨hm', by simp [hb0, hb1, hr]⟩
  · intro J
    apply C0JoinTree.branch
    · intro hb0
      exact C0JoinTree.jump ⟨rfl, Or.inl ⟨hb0, rfl⟩⟩
    · intro hb0
      apply C0JoinTree.branch
      · intro hb1
        exact C0JoinTree.jump ⟨rfl, Or.inr ⟨hb0, hb1, rfl⟩⟩
      · intro hb1
        exact C0JoinTree.ret ⟨rfl, by simp_all⟩

theorem join_ite_tactic_wp (Γ : Env) (X : XPost) (m : Mem 64) (b : Bool) (x y : BitVec 64) :
    wp Γ (fun (r : Tup Val [i64]) m' => m' = m ∧ r.fst = if b then x else y) X
      (joinIteExpr b x y) m := by
  dsimp only [joinIteExpr]
  c0_join_ite fun (xs : Tup Val [i64]) m' => m' = m ∧ xs.1 = (if b then x else y)
  · rintro J ⟨r, ⟨⟩⟩ m' ⟨hm', hr⟩; c0_hsteps_nogrp; exact ⟨hm', hr⟩
  · intro J hJ hb; c0_hsteps_nogrp; apply hJ; exact ⟨rfl, by simp_all⟩
  · intro J hJ hb; c0_hsteps_nogrp; apply hJ; exact ⟨rfl, by simp_all⟩

end

end RecordLoopAndJoinTests

/-! ## 5. Axiom Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

check_std_axioms!
  LeanQbeTest.T.ProofKitV2Test.u32kit_roundtrips_and_bounds
  LeanQbeTest.T.ProofKitV2Test.bv32_omega_casts_shifts_signExtend
  LeanQbeTest.T.ProofKitV2Test.u32_xor_one_pair_bound
  LeanQbeTest.T.ProofKitV2Test.chained_sub_with_wp_distractors
  LeanQbeTest.T.ProofKitV2Test.chained_sub_explicit_hyps
  LeanQbeTest.T.ProofKitV2Test.kissat_general_mask_orthogonality
  LeanQbeTest.T.ProofKitV2Test.kissat_single_bit_orthogonality
  LeanQbeTest.T.ProofKitV2Test.kissat64_hdr_pack_clear_set
  LeanQbeTest.T.ProofKitV2Test.kissat32_pword_flags_pure
  LeanQbeTest.T.ProofKitV2Test.packed_field_extract_update_props
  LeanQbeTest.T.ProofKitV2Test.c0_guard_demo_bare
  LeanQbeTest.T.ProofKitV2Test.c0_guard_demo_auto_exit
  LeanQbeTest.T.ProofKitV2Test.c0_guard_mem_hstraight
  LeanQbeTest.T.ProofKitV2Test.guard_cascade50_exit_close
  LeanQbeTest.T.ProofKitV2Test.guard_cascade12_bare
  LeanQbeTest.T.ProofKitV2Test.sum_non_slot0_wp
  LeanQbeTest.T.ProofKitV2Test.jump_record_wp
  LeanQbeTest.T.ProofKitV2Test.seq_joins_wp
  LeanQbeTest.T.ProofKitV2Test.multi_branch_tree_wp
  LeanQbeTest.T.ProofKitV2Test.multi_dag_wp
  LeanQbeTest.T.ProofKitV2Test.multi_arm3_wp
  LeanQbeTest.T.ProofKitV2Test.join_ite_and_tree_constructors_wp
  LeanQbeTest.T.ProofKitV2Test.join_ite_tactic_wp

end LeanQbeTest.T.ProofKitV2Test
