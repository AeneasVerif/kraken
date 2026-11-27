/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Gates.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation

/-!
# Shared Gate-Extraction WP Helpers (`Proof/Gates/WpHelpers`)

Pure BitVec / `List` / `FullDenseInvW` / `lit_mark` / scratch-array lemmas and
small shared C0 sub-expression WP helpers used across `Proof/Gates/Wp*`
(`0` legacy `Full*` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Gates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

@[expose] public section

/-- Tail-and-core portion of `FullMem c s` excluding `lit_mark` and `scratch_buf`. -/
def fullMemNoLmScr (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆ c.pad

/-- Shared M7 C0 sub-expression setting bit `idx` in scratch mask starting at `base`. -/
def m7SetMaskBitExpr (pScr : BitVec 64) (base idx : BitVec 32)
    (k : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.lshr i32, (Arg.var idx, Arg.imm 5, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i32, (Arg.var base, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p_1 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_1.fst, Arg.imm 4, ())⟩ fun p_2 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p_2.fst, ())⟩ fun p_3 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var idx, Arg.imm 31, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var ld, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (Arg.var p.fst) (Arg.var p_3.fst) k

end

public section

/-! ## 1. General BitVec, List, and `FullDenseInvW` Helpers -/

theorem getElem_congr {α : Type} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem bv32_xor1_lt {n : Nat} (l : BitVec 32) (hl : l.toNat < 2 * n) :
    (l ^^^ 1#32).toNat = l.toNat ^^^ 1 ∧ (l ^^^ 1#32).toNat < 2 * n := by
  have h1 : (l ^^^ 1#32).toNat = l.toNat ^^^ 1 := by
    rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have := fullInv_var_xor1 l.toNat
  exact ⟨h1, by omega⟩

theorem xor1_lt {n : Nat} (l : BitVec 32) (hl : l.toNat < 2 * n) :
    (l ^^^ 1#32).toNat < 2 * n :=
  (bv32_xor1_lt l hl).2

theorem pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have h1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h2 : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, h1, BitVec.toNat_ofNat]
    have h1m : 1 % 2 ^ 32 = 1 := rfl
    rw [h1m]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero, Nat.mul_mod_right]
      simp [show (2 * v.toNat + 1) % 2 = 1 by omega]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.mul_add_div (by omega : 0 < 2)]
  exact ⟨h1, h2⟩

theorem fullDenseInvW_lm_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} (hlm_len : lm'.length = 2 * c.max_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8)
    {scr' : List (BitVec 32)} (hscr_len : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with lit_mark := lm' }
        scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len },
    { h.1.scratch_ok with scratch_buf_len := hscr_len }⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlm_clr⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hscr_len : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  fullDenseInvW_lm_scr h h.1.core_ok.lit_mark_len h.2.2.1.2 hscr_len

theorem lengths_witness_lm_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} (hlm_len : lm'.length = 2 * c.max_vars)
    {scr' : List (BitVec 32)} (hscr_len : scr'.length = c.scratch_cap) :
    FullState.LengthsOk c
        { s with
          core := { s.core with lit_mark := lm' }
          scratch := { s.scratch with scratch_buf := scr' } } ∧
      FullWitnessInv c F0 F_cur { s.core with lit_mark := lm' } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len },
    { h.1.scratch_ok with scratch_buf_len := hscr_len }⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩

theorem bveEntry_congr_core {F_cur : List (List Nat)} {s s' : FullState}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hcv : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) :
    FullBveEntryOkW F_cur s' lit w := by
  unfold FullBveEntryOkW at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact ⟨by rw [hcv]; exact h.1, h.2⟩
  · rw [ite_eq_right hb] at h ⊢
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' w.toNat = fullArenaClauseGarb s w.toNat := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    rw [hrefs, hgb]; exact h

theorem lm_set_at {c : FullCfg} {lm : List (BitVec 8)} {l : Nat}
    (_hlm : lm.length = 2 * c.max_vars) (_hl : l < 2 * c.max_vars) {v : BitVec 8}
    {P : Nat → Prop} (hprev : ∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 → P y)
    (hnew : P l) :
    ∀ y < 2 * c.max_vars, (lm.set l v)[y]?.getD 0#8 ≠ 0#8 → P y := by
  intro y hy hnz
  by_cases hyl : y = l
  · subst hyl; exact hnew
  · rw [List.getElem?_set_ne (Ne.symm hyl)] at hnz; exact hprev y hy hnz

theorem lm_set2_at {c : FullCfg} {lm : List (BitVec 8)} {x0 x1 : Nat}
    {v0 v1 : BitVec 8} {P : Nat → Prop}
    (hprev : ∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 → P y)
    (hx0 : P x0) (hx1 : P x1) :
    ∀ y < 2 * c.max_vars, ((lm.set x0 v0).set x1 v1)[y]?.getD 0#8 ≠ 0#8 → P y := by
  intro y hy hnz
  by_cases hy1 : y = x1
  · subst hy1; exact hx1
  · rw [List.getElem?_set_ne (Ne.symm hy1)] at hnz
    by_cases hy0 : y = x0
    · subst hy0; exact hx0
    · rw [List.getElem?_set_ne (Ne.symm hy0)] at hnz; exact hprev y hy hnz

theorem lm_clear_step {lm : List (BitVec 8)} {l : Nat} {P : Nat → Prop}
    (hlm : l < lm.length)
    (hprev : ∀ x < lm.length, lm[x]?.getD 0#8 ≠ 0#8 → x = l ∨ P x) :
    ∀ x < lm.length, (lm.set l 0#8)[x]?.getD 0#8 ≠ 0#8 → P x := by
  intro x hx hnz
  by_cases hxl : x = l
  · subst hxl; simp [List.getElem?_set_self hlm] at hnz
  · rw [List.getElem?_set_ne (Ne.symm hxl)] at hnz
    exact (hprev x hx hnz).resolve_left hxl

theorem lm_clear_step_maxv {c : FullCfg} {lm : List (BitVec 8)} {x_idx : Nat}
    (hlm : lm.length = 2 * c.max_vars) (hx : x_idx < 2 * c.max_vars) {P : Nat → Prop}
    (hprev : ∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 → y = x_idx ∨ P y) :
    ∀ y < 2 * c.max_vars, (lm.set x_idx 0#8)[y]?.getD 0#8 ≠ 0#8 → P y := by
  have h := lm_clear_step (P := P) (hlm ▸ hx) (fun x hx' => hprev x (hlm ▸ hx'))
  exact fun y hy => h y (hlm ▸ hy)

theorem lm_clear2_step {c : FullCfg} {lm : List (BitVec 8)} {x0 x1 : Nat}
    (hlm : lm.length = 2 * c.max_vars) (hx0 : x0 < 2 * c.max_vars) (hx1 : x1 < 2 * c.max_vars)
    {P : Nat → Prop}
    (hprev : ∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 → y = x0 ∨ y = x1 ∨ P y) :
    ∀ y < 2 * c.max_vars,
      ((lm.set x0 0#8).set x1 0#8)[y]?.getD 0#8 ≠ 0#8 → P y := by
  intro y hy hnz
  by_cases hy1 : y = x1
  · subst y
    rw [List.getElem?_set_self (by simp [hlm, hx1]), Option.getD_some] at hnz
    exact absurd rfl hnz
  · rw [List.getElem?_set_ne (Ne.symm hy1)] at hnz
    by_cases hy0 : y = x0
    · subst y
      rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz; exact absurd rfl hnz
    · rw [List.getElem?_set_ne (Ne.symm hy0)] at hnz
      rcases hprev y hy hnz with h | h | h
      · exact absurd h hy0
      · exact absurd h hy1
      · exact h

theorem u32_and7fff_lt {n : Nat} (r : BitVec 32)
    (hr : r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < n) (hne : r ≠ 0xFFFFFFFF#32) :
    (r &&& 0x7FFFFFFF#32).toNat < n :=
  hr.resolve_left hne

theorem u32_and7fff_or8000 (j : BitVec 32) (hj : j.toNat < 2 ^ 31) :
    ((j ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = j := by
  apply BitVec.eq_of_toNat_eq
  have h1 : ((j ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = (j &&& 0x7FFFFFFF#32) := by
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
    have h0 : ((0x80000000#32 &&& 0x7FFFFFFF#32) : BitVec 32)[i] = false := by
      have : (0x80000000#32 &&& 0x7FFFFFFF#32) = 0#32 := by decide
      rw [this]; simp
    simp only [BitVec.getElem_and] at h0; rw [Bool.and_or_distrib_right, h0, Bool.or_false]
  rw [h1, BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hj]

theorem u32_and7fff_or8000_toNat (j : BitVec 32) (hj : j.toNat < 2 ^ 31) :
    ((j ||| 0x80000000#32) &&& 0x7FFFFFFF#32).toNat = j.toNat :=
  congrArg BitVec.toNat (u32_and7fff_or8000 j hj)

theorem u32_and7fff_self (j : BitVec 32) (hj : j.toNat < 2 ^ 31) :
    (j &&& 0x7FFFFFFF#32).toNat = j.toNat := by
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hj]

/-! ## 2. M7 Mask & XOR Helpers -/

theorem m7_mask_lt_16 (idx : BitVec 32) (hi : idx.toNat < 512) :
    (idx >>> (5 : Nat)).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

theorem m7_mask_idx_lo (base idx : BitVec 32)
    (hb : base.toNat = 1024 ∨ base.toNat = 1040) (hi : idx.toNat < 512) :
    1024 ≤ (base + (idx >>> (5 : Nat))).toNat ∧
    (base + (idx >>> (5 : Nat))).toNat < 1056 := by
  have hm := m7_mask_lt_16 idx hi
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega

theorem m7_bit_disjoint (p b : Nat) (hp : p < 16) (hb : b < 16) (hne : b ≠ p) :
    (1#32 <<< p) &&& (1#32 <<< b) = 0#32 := by
  have hall : ∀ p' < 16, ∀ b' < 16, b' ≠ p' → (1#32 <<< p') &&& (1#32 <<< b') = 0#32 := by
    decide
  exact hall p hp b hb hne

theorem m7_bit_test_imp (mask p : BitVec 32) (_hp : p.toNat < 16)
    (h : ((mask >>> p.toNat) &&& 1#32) ≠ 0#32) : (mask &&& (1#32 <<< p.toNat)) ≠ 0#32 := by
  intro hz
  have hz1 := congrArg (·.getLsbD p.toNat) hz
  simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft] at hz1
  have hfalse : mask.getLsbD p.toNat = false := by
    cases hm : mask.getLsbD p.toNat
    · rfl
    · exact absurd (by simpa [hm] using hz1) (by omega)
  apply h; ext i hi; simp
  by_cases hi0 : i = 0
  · subst hi0; simp [hfalse]
  · simp [hi0]

theorem m7_xor_idx_lt (m : BitVec 8) (k : BitVec 32)
    (hm : (m.setWidth 32).slt 2#32 = false)
    (hk : ¬ k.toNat ≤ (2 ^ 32 - 2 % 2 ^ 32 + m.toNat) % 2 ^ 32 / 2) :
    ((m.setWidth 32 - 2#32) >>> (1 : Nat)).toNat < k.toNat := by
  have hm_lt : m.toNat < 256 := m.isLt
  have hge2 : 2 ≤ m.toNat := by
    rcases Nat.lt_or_ge m.toNat 2 with hlt | hge
    · rcases (by omega : m.toNat = 0 ∨ m.toNat = 1) with h | h
      · have hm0 : m = 0#8 := BitVec.eq_of_toNat_eq (by simp [h])
        rw [hm0] at hm; cases hm
      · have hm1 : m = 1#8 := BitVec.eq_of_toNat_eq (by simp [h])
        rw [hm1] at hm; cases hm
    · exact hge
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.pow_one]
  omega

theorem m7_xor_bit_lt (x : BitVec 32) (hx : x.toNat < 4) :
    (1#32 <<< (x.toNat % 32)).toNat < 16 := by
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3) with
    h | h | h | h <;> simp [h]

theorem m7_setMaskBit_wp (Γ : Env) (c : FullCfg) (s0 : FullState)
    (scr : List (BitVec 32)) (R : Mem 64 → Prop) (base idx : BitVec 32)
    (m : Mem 64) (Q : Post [.bool]) (X : XPost) (k : Expr Val Cont [.bool])
    (hsc : scr.length = c.scratch_cap) (h1056 : 1056 ≤ c.scratch_cap)
    (hbase_lo : 1024 ≤ base.toNat) (hbase_hi : base.toNat + 16 ≤ 1056)
    (hidx_lt : idx.toNat < 512)
    (hm : (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr } } ⋆ R) m)
    (hk : ∀ (scr' : List (BitVec 32)),
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) → scr'[i]? = scr[i]?) →
      ∀ m', (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr' } } ⋆ R) m' →
        wp Γ Q X k m') :
    wp Γ Q X (m7SetMaskBitExpr c.pScratchBuf base idx k) m := by
  have hm_lt : (idx >>> (5 : Nat)).toNat < 16 := m7_mask_lt_16 idx hidx_lt
  have hoff_eq : ((base + (idx >>> (5 : Nat))).setWidth 64).toNat =
      base.toNat + idx.toNat / 32 := by
    rw [zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hoff_lt : ((base + (idx >>> (5 : Nat))).setWidth 64).toNat < scr.length := by
    rw [hsc]; omega
  unfold m7SetMaskBitExpr
  c0_hsteps_nogrp
  refine hk _ (by rw [List.length_set, hsc]) (fun i _ hor => ?_) m hm
  have hne_i : ((base + (idx >>> (5 : Nat))).setWidth 64).toNat ≠ i := by omega
  have hne_i2 : ((base + (idx >>> (5#32 : BitVec 32))).setWidth 64).toNat ≠ i := by
    have hsh2 : (idx >>> (5#32 : BitVec 32)).toNat = idx.toNat / 32 := by
      change (idx >>> (5#32 : BitVec 32).toNat).toNat = idx.toNat / 32
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by decide), Nat.shiftRight_eq_div_pow, show 2 ^ 5 = 32 from rfl]
    rw [zext32_toNat, BitVec.toNat_add, hsh2, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [List.getElem?_set_ne (by first | exact hne_i | exact hne_i2)]

/-! ## 3. M8 Scratch & Memory Framing Helpers -/

theorem m8_scr_imm_lt {c : FullCfg} {scr : List (BitVec 32)} {k : Nat}
    (hlen : scr.length = c.scratch_cap) (hsc : 16384 ≤ c.scratch_cap) (hk : k < 16384) :
    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat k)).toNat < scr.length := by
  change (BitVec.ofNat 64 k).toNat < scr.length
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]
  omega

theorem m8_mask_idx_lo (base idx : BitVec 32)
    (hb : base = 4002#32 ∨ base = 4066#32) (hi : idx.toNat < 2001) :
    (base + (idx >>> (5 : Nat))).toNat = base.toNat + idx.toNat / 32 ∧
    (base + (idx >>> (5 : Nat))).toNat < 4130 := by
  have hsh : (idx >>> (5 : Nat)).toNat = idx.toNat / 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt : base.toNat + idx.toNat / 32 < 4130 := by
    rcases hb with rfl | rfl <;> simp only [BitVec.toNat_ofNat] <;> omega
  rw [BitVec.toNat_add, hsh, Nat.mod_eq_of_lt (by omega)]
  exact ⟨rfl, hlt⟩

theorem fullMem_eq_lm_scr (c : FullCfg) (s : FullState)
    (lm : List (BitVec 8)) (scr : List (BitVec 32)) :
    FullMem c { s with
      core := { s.core with lit_mark := lm }
      scratch := { s.scratch with scratch_buf := scr } } =
      (array (t := i8) c.pLitMark lm ⋆ array (t := i32) c.pScratchBuf scr ⋆
        fullMemNoLmScr c s) := by
  unfold FullMem FullCoreArrays FullCoreByteArrs FullScratchArrays FullScrDynArrs fullMemNoLmScr
  ac_rfl

theorem fullMem_scr_iff (c : FullCfg) (s : FullState)
    (scr : List (BitVec 32)) (R : Mem 64 → Prop) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) =
      (array (t := i32) c.pScratchBuf scr ⋆
        (array (t := i8) c.pLitMark s.core.lit_mark ⋆ fullMemNoLmScr c s ⋆ R)) := by
  have h := fullMem_eq_lm_scr c s s.core.lit_mark scr
  have hs :
      { s with
        core := { s.core with lit_mark := s.core.lit_mark }
        scratch := { s.scratch with scratch_buf := scr } } =
        { s with scratch := { s.scratch with scratch_buf := scr } } := by
    cases s; rfl
  rw [← hs, h]
  ac_rfl

end

end LeanQbe.T.Examples.Kissat.Proof.Gates
