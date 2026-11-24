module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Logic.ProofKit

/-!
# ProofKitTest: Verification of `ProofKit` (`bv_c0`, `c0_bv_omega`, `state_frame`, `ArrayCursorInv`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.ProofKitTest

open LeanQbe.T
open LeanQbe.T.ProofKit
open Std.ExtHashMap

/-! ## 1. `bv_c0` and `c0_bv_omega` checks -/

/-- `bv_c0` does NOT rewrite BitVec `=` into `.toNat = .toNat`. -/
theorem bv_c0_preserves_eq (a b : BitVec 64) (h : a = b) : a = b := by
  c0_bv_simp
  exact h

theorem bv_c0_widths_and_ofNat (a : BitVec 1) (b : BitVec 8) (_c : BitVec 16) (d : BitVec 32) :
    (a.setWidth 32).toNat = a.toNat ∧
    (a.setWidth 64).toNat = a.toNat ∧
    (b.setWidth 16).toNat = b.toNat ∧
    (d.setWidth 64).toNat = d.toNat ∧
    (d.setWidth 32).toNat = d.toNat ∧
    (0#64).toNat = 0 ∧
    (1#64).toNat = 1 ∧
    (42#32).toNat = 42 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> c0_bv_omega

theorem bv_c0_shifts_and_packing (x y : BitVec 32)
    (hx : x.toNat < 1000) (hy : y.toNat ≤ x.toNat) :
    ((x.setWidth 64 <<< 1) ||| 1#64).toNat = 2 * x.toNat + 1 ∧
    ((x - y).toNat = x.toNat - y.toNat) ∧
    (((x.setWidth 64 + 1#64) - 1#64).toNat = x.toNat) ∧
    (((x ^^^ 1#32) >>> 1).toNat = x.toNat / 2) ∧
    ((x <<< 2).toNat = 4 * x.toNat) ∧
    ((x &&& 1#32).toNat = x.toNat % 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> c0_bv_omega

theorem bv_c0_trunc_and_shift_bv (x : BitVec 64) (k : BitVec 64)
    (hx : x.toNat < 50) (hk : k.toNat = 3) :
    ((x <<< k).toNat = x.toNat * 8) ∧
    (((x.setWidth 32).toNat) = x.toNat) ∧
    ((x >>> 1).toNat = x.toNat / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> c0_bv_omega

/-! ## 2. `state_frame` and `state_frame!` checks -/

@[expose] public section

structure MiniCfg where
  mv : Nat
  mc : Nat

structure MiniCore where
  vals : List (BitVec 8)
  trail : List (BitVec 32)
  sz : Nat

structure MiniScratch where
  watch : List (BitVec 64)
  marks : List (BitVec 8)
  pos : Nat

structure MiniState where
  core : MiniCore
  scratch : MiniScratch
  ticks : Nat

structure MiniCore.LengthsOk (c : MiniCfg) (k : MiniCore) : Prop where
  vals_len : k.vals.length = 2 * c.mv
  trail_len : k.trail.length = c.mv
  sz_le : k.sz ≤ c.mv

structure MiniScratch.LengthsOk (c : MiniCfg) (sc : MiniScratch) : Prop where
  watch_len : sc.watch.length = 2 * c.mv
  marks_len : sc.marks.length = c.mc
  pos_le : sc.pos ≤ c.mv

structure MiniState.LengthsOk (c : MiniCfg) (s : MiniState) : Prop where
  core_ok : s.core.LengthsOk c
  scratch_ok : s.scratch.LengthsOk c

def MiniScratchMask (s : MiniState) : MiniState :=
  { s with scratch := { watch := [], marks := [], pos := 0 }, ticks := 0 }

def MiniExtPres (s₀ s₁ : MiniState) : Prop :=
  s₁.core.vals = s₀.core.vals ∧ s₁.core.trail = s₀.core.trail

end

theorem state_frame_nested_preserves (c : MiniCfg) (s : MiniState)
    (hlen : s.LengthsOk c) (i : Nat) (w : BitVec 64) (p' : Nat) (hlt : p' < c.mv) :
    let s' : MiniState :=
      { s with
        scratch := { s.scratch with watch := s.scratch.watch.set i w, pos := p' }
        ticks := s.ticks + 1 }
    s'.LengthsOk c ∧
    AgreesExcept MiniScratchMask s s' ∧
    MiniExtPres s s' ∧
    s'.core = s.core := by
  intro s'
  state_frame
  exact Nat.le_of_lt hlt

theorem state_frame_bang_closes_bounds (c : MiniCfg) (s : MiniState)
    (hlen : s.LengthsOk c) (i : Nat) (v : BitVec 32) (hlt : s.scratch.pos < c.mv) :
    let s' : MiniState :=
      { s with
        core := { s.core with trail := s.core.trail.set i v }
        scratch := { s.scratch with pos := s.scratch.pos + 1 } }
    s'.LengthsOk c ∧
    PreservesCoreSlice MiniState.core s' { s' with ticks := 99 } := by
  intro s'
  state_frame!

/-! ## 3. Real C0 Loops via `wp_while_cursor64` & `wp_while_mut_cursor64` -/

c0_decl! kit "
u64 sum_arr64(u64 p, u64 n) {
  u64 i = 0ULL;
  u64 acc = 0ULL;
  while (i < n) {
    u64 v = ((u64 *)p)[i];
    acc = acc + v;
    i = i + 1ULL;
  }
  return acc;
}

void inc_arr32(u64 p, u64 n) {
  u64 i = 0ULL;
  while (i < n) {
    u32 v = ((u32 *)p)[i];
    ((u32 *)p)[i] = v + 1;
    i = i + 1ULL;
  }
  return;
}
"

private def prefixSum64 (xs : List (BitVec 64)) (k : Nat) : BitVec 64 :=
  (xs.take k).foldl (· + ·) 0#64

private theorem prefixSum64_succ (xs : List (BitVec 64)) {k : Nat} (hk : k < xs.length) :
    prefixSum64 xs (k + 1) = prefixSum64 xs k + xs[k] := by
  unfold prefixSum64
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem sum_arr64_spec (Γ : Env) (p : BitVec 64) (xs : List (BitVec 64))
    (n : BitVec 64) (hn : n.toNat ≤ xs.length) (R : Mem 64 → Prop) {m : Mem 64}
    (hm : (array64 p xs ⋆ R) m) (Q : Post [i64]) (X : XPost)
    (hQ : ∀ m', (array64 p xs ⋆ R) m' → Q (prefixSum64 xs n.toNat, ()) m') :
    Func.wp Γ sum_arr64.body (p, n, ()) m Q X := by
  dsimp only [Func.wp, sum_arr64, sum_arr64_body]
  c0_hsteps_nogrp
  refine wp_while_cursor64 (β := BitVec 64) (α := BitVec 64) 0 n.toNat xs
    (fun acc => (acc, ()))
    (fun idx acc => acc = prefixSum64 xs idx)
    (fun _ _ => array64 p xs) R ?hentry ?hbody
  · intro J hJ
    c0_hsteps
    refine hJ 0 0#64 m (ArrayCursorInv.init (Nat.zero_le _) hn rfl) hm
  · intro J idx acc ml hcur hmem hback
    have hlo := hcur.lo_le
    have hle := hcur.idx_le
    have hlen := hcur.hi_le
    have hacc := hcur.inv
    have hidx64 : idx < 2 ^ 64 := by have := n.isLt; omega
    c0_hsteps
    · have hback_step := hback (idx + 1) (acc + xs[idx]) ml (by omega)
        (hcur.step (by c0_bv_omega) (by rw [hacc, prefixSum64_succ xs (hcur.idx_lt_length (by c0_bv_omega))]))
        hmem
      simpa only [ArrayCursorInv.ofNat_add_one, ArrayCursorInv.toNat_ofNat_lt hidx64] using hback_step
    · obtain ⟨rfl, hacc_done⟩ := hcur.done (by c0_bv_omega)
      subst hacc_done
      exact hQ ml hmem

private theorem inc_arr32_spec (Γ : Env) (p : BitVec 64) (xs₀ : List (Val i32))
    (n : BitVec 64) (hn : n.toNat ≤ xs₀.length) (R : Mem 64 → Prop) {m : Mem 64}
    (hm : (array p xs₀ ⋆ R) m) (Q : Post []) (X : XPost)
    (hQ : ∀ xs : List (Val i32), ∀ m', xs.length = xs₀.length →
      (∀ i < n.toNat, xs[i]? = some (xs₀[i]?.getD 0#32 + 1#32)) →
      OutsideSliceAgrees 0 n.toNat xs₀ xs → (array p xs ⋆ R) m' → Q () m') :
    Func.wp Γ inc_arr32.body (p, n, ()) m Q X := by
  dsimp only [Func.wp, inc_arr32, inc_arr32_body]
  c0_hsteps_nogrp
  refine wp_while_mut_cursor64 (β := Val i32) (α := Unit) 0 n.toNat xs₀
    (fun _ => ())
    (fun idx xs _ => ∀ k < idx, xs[k]? = some (xs₀[k]?.getD 0#32 + 1#32))
    (fun _ xs _ => array p xs) R ?hentry ?hbody
  · intro J hJ
    c0_hsteps
    refine hJ 0 xs₀ () m (ArrayMutCursorInv.init (Nat.zero_le _) hn (fun _ hk => absurd hk (Nat.not_lt_zero _))) hm
  · intro J idx xs _ ml hcur hmem hback
    have hlo := hcur.lo_le
    have hle := hcur.idx_le
    have hlen := hcur.hi_le
    have hlen_eq := hcur.len_eq
    have hinv := hcur.inv
    have hidx64 : idx < 2 ^ 64 := by have := n.isLt; omega
    c0_hsteps
    · have hlt : idx < n.toNat := by c0_bv_omega
      have hidx_len : idx < xs.length := hcur.idx_lt_length hlt
      have hinv' : ∀ k < idx + 1, (xs.set idx (xs[idx] + 1#32))[k]? = some (xs₀[k]?.getD 0#32 + 1#32) := by
        intro k hk
        by_cases hkx : k = idx
        · subst hkx
          rw [List.getElem?_set_self hidx_len, Option.some.injEq]
          have hget : xs[k]? = xs₀[k]? := hcur.get_unwritten (Nat.le_refl k)
          have hk0 : k < xs₀.length := by omega
          rw [List.getElem?_eq_getElem hidx_len, List.getElem?_eq_getElem hk0] at hget
          injection hget with hget'
          rw [List.getElem?_eq_getElem hk0, Option.getD_some, hget']
        · rw [List.getElem?_set_ne (Ne.symm hkx)]
          exact hinv k (by omega)
      rw [ArrayCursorInv.ofNat_add_one]
      refine hback (idx + 1) (xs.set idx (xs[idx] + 1#32)) () _ (by omega)
        (hcur.step_set hlt (xs[idx] + 1#32) hinv') ?_
      simp only [ArrayCursorInv.toNat_ofNat_lt hidx64] at *
      assumption
    · obtain ⟨rfl, hlen_done, hout_done, hinv_done⟩ := hcur.done (by c0_bv_omega)
      exact hQ xs ml hlen_done hinv_done hout_done hmem

#print axioms bv_c0_preserves_eq
#print axioms bv_c0_widths_and_ofNat
#print axioms bv_c0_shifts_and_packing
#print axioms bv_c0_trunc_and_shift_bv
#print axioms state_frame_nested_preserves
#print axioms state_frame_bang_closes_bounds
check_std_axioms! bv_c0_preserves_eq bv_c0_widths_and_ofNat bv_c0_shifts_and_packing
  bv_c0_trunc_and_shift_bv state_frame_nested_preserves state_frame_bang_closes_bounds
  sum_arr64_spec inc_arr32_spec

end LeanQbeTest.T.ProofKitTest

end
