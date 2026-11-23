module

public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4E (`FullM7BveGates`) Proofs — Part 3b (`find_ite_side`, `find_ite`, `find_xor`)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
- `full_bve_find_ite_side_m7_wp`
- `full_bve_find_ite_m7_wp`
- `full_bve_find_xor_m7_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Shared Scratch, `lit_mark`, and Literal Helpers -/

private theorem m7_p3b_pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
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

private theorem m7_p3b_fullDenseInvW_lm_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
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

private theorem m7_p3b_bveEntry_congr_core {F_cur : List (List Nat)} {s s' : FullState}
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

private theorem m7_p3b_mask_lt_16 (idx : BitVec 32) (hi : idx.toNat < 512) :
    (idx >>> (5 : Nat)).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

private theorem m7_p3b_u32_and7fff_lt {n : Nat} (r : BitVec 32)
    (hr : r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < n) (hne : r ≠ 0xFFFFFFFF#32) :
    (r &&& 0x7FFFFFFF#32).toNat < n := hr.resolve_left hne

private theorem m7_p3b_lm_clear2_step {c : FullCfg} {lm : List (BitVec 8)} {x0 x1 : Nat}
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

private theorem m7_p3b_lm_set2_at {c : FullCfg} {lm : List (BitVec 8)} {x0 x1 : Nat}
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

private theorem m7_p3b_bit_disjoint (p b : Nat) (hp : p < 16) (hb : b < 16) (hne : b ≠ p) :
    (1#32 <<< p) &&& (1#32 <<< b) = 0#32 := by
  have hall : ∀ p' < 16, ∀ b' < 16, b' ≠ p' → (1#32 <<< p') &&& (1#32 <<< b') = 0#32 := by
    decide
  exact hall p hp b hb hne

private theorem m7_p3b_bit_or_bound {mask : BitVec 32} {pat idx : BitVec 32}
    {arr : List (BitVec 32)} {base n : Nat}
    (hprev : ∀ b < 16, (mask &&& (1#32 <<< b)) ≠ 0#32 →
      (arr[base + b]?.getD 0#32).toNat < n)
    (hpat : pat.toNat < 16) (hidx : idx.toNat < n) (hlen : base + 16 ≤ arr.length) :
    ∀ b < 16, ((mask ||| (1#32 <<< pat.toNat)) &&& (1#32 <<< b)) ≠ 0#32 →
      ((arr.set (base + pat.toNat) idx)[base + b]?.getD 0#32).toNat < n := by
  intro b hb hnz
  by_cases hbp : b = pat.toNat
  · subst hbp
    rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hidx
  · rw [List.getElem?_set_ne (by omega)]
    refine hprev b hb ?_
    intro hz; apply hnz
    rw [BitVec.and_or_distrib_right, hz, BitVec.zero_or]
    exact m7_p3b_bit_disjoint pat.toNat b hpat hb hbp

private def m7SetMaskBitExpr (pScr : BitVec 64) (base idx : BitVec 32)
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

private theorem m7_p3b_setMaskBit_wp (Γ : Env) (c : FullCfg) (s0 : FullState)
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
  have hm_lt : (idx >>> (5 : Nat)).toNat < 16 := m7_p3b_mask_lt_16 idx hidx_lt
  have hoff_eq : ((base + (idx >>> (5 : Nat))).setWidth 64).toNat =
      base.toNat + idx.toNat / 32 := by
    rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight,
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
    rw [m6_zext32_toNat, BitVec.toNat_add, hsh2, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [List.getElem?_set_ne (by first | exact hne_i | exact hne_i2)]

private def m7FinishIteExpr (pScr : BitVec 64) (r0 r1 : BitVec 32) :
    Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm (t := i32) 1056, ())⟩ fun p0 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p0.fst, Arg.imm 4, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p1.fst, ())⟩ fun p2 =>
  Expr.store (Arg.imm (t := i32) 1) (Arg.var p2.fst) (
  Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm (t := i32) 1057, ())⟩ fun q0 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var q0.fst, Arg.imm 4, ())⟩ fun q1 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var q1.fst, ())⟩ fun q2 =>
  Expr.group (sig := [[i32]])
    (fun _lbls =>
      Blocks.cons (fun arg =>
        Expr.store (Arg.var arg.fst) (Arg.var q2.fst)
          (Expr.ret (Arg.imm (t := .bool) true, ())))
        Blocks.nil)
    (fun lbls =>
      Expr.let_ ⟨OpCode.or i32, (Arg.var r0, Arg.var r1, ())⟩ fun t0 =>
      Expr.let_ ⟨OpCode.and i32, (Arg.var t0.fst, Arg.imm 0x80000000#32, ())⟩ fun t1 =>
      Expr.let_ ⟨OpCode.ne i32, (Arg.var t1.fst, Arg.imm 0, ())⟩ fun t2 =>
      Expr.jnz (Arg.var t2.fst) (Expr.jump lbls.1 (Arg.imm 1, ()))
        (Expr.jump lbls.1 (Arg.imm 0, ()))))

private def m7IteHitExpr (pScr : BitVec 64) (litMask oppMask i0 i1 r0 r1 : BitVec 32) :
    Expr Val Cont [.bool] :=
  m7SetMaskBitExpr pScr litMask i0
    (m7SetMaskBitExpr pScr litMask i1
      (m7SetMaskBitExpr pScr oppMask (r0 &&& 0x7FFFFFFF#32)
        (m7SetMaskBitExpr pScr oppMask (r1 &&& 0x7FFFFFFF#32)
          (m7FinishIteExpr pScr r0 r1))))

private theorem m7_p3b_ite_hit_wp (Γ : Env) (c : FullCfg) (s0 : FullState)
    (scr6 : List (BitVec 32)) (R : Mem 64 → Prop)
    (litMask oppMask i0 i1 r0 r1 : BitVec 32)
    (m6 : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hsc6 : scr6.length = c.scratch_cap)
    (hout6' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
      scr6[i]? = s0.scratch.scratch_buf[i]?)
    (hsc1066 : 1066 ≤ c.scratch_cap)
    (hlm_lo : 1024 ≤ litMask.toNat) (hlm_hi : litMask.toNat + 16 ≤ 1056)
    (hom_lo : 1024 ≤ oppMask.toNat) (hom_hi : oppMask.toNat + 16 ≤ 1056)
    (hi0_lt : i0.toNat < 512) (hi1_lt : i1.toNat < 512)
    (hr0_lt : (r0 &&& 0x7FFFFFFF#32).toNat < 512)
    (hr1_lt : (r1 &&& 0x7FFFFFFF#32).toNat < 512)
    (hm6' : (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr6 } } ⋆ R) m6)
    (hQ : ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
        scr'[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (ok, ()) m') :
    wp Γ Q X (m7IteHitExpr c.pScratchBuf litMask oppMask i0 i1 r0 r1) m6 := by
  unfold m7IteHitExpr
  refine m7_p3b_setMaskBit_wp Γ c s0 scr6 R litMask i0 m6 Q X _
    hsc6 (by omega) hlm_lo hlm_hi hi0_lt hm6' ?_
  intro scr7 hsc7 hout7 m7 hm7
  have hout7' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
      scr7[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout7 i hi (by rcases hor with h | h <;> omega)).trans (hout6' i hi hor)
  clear hout7 hout6' hm6'
  refine m7_p3b_setMaskBit_wp Γ c s0 scr7 R litMask i1 m7 Q X _
    hsc7 (by omega) hlm_lo hlm_hi hi1_lt hm7 ?_
  intro scr8 hsc8 hout8 m8 hm8
  have hout8' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
      scr8[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout8 i hi (by rcases hor with h | h <;> omega)).trans (hout7' i hi hor)
  clear hout8 hout7' hm7
  refine m7_p3b_setMaskBit_wp Γ c s0 scr8 R oppMask (r0 &&& 0x7FFFFFFF#32) m8 Q X _
    hsc8 (by omega) hom_lo hom_hi hr0_lt hm8 ?_
  intro scr9 hsc9 hout9 m9 hm9
  have hout9' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
      scr9[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout9 i hi (by rcases hor with h | h <;> omega)).trans (hout8' i hi hor)
  clear hout9 hout8' hm8
  refine m7_p3b_setMaskBit_wp Γ c s0 scr9 R oppMask (r1 &&& 0x7FFFFFFF#32) m9 Q X _
    hsc9 (by omega) hom_lo hom_hi hr1_lt hm9 ?_
  intro scr10 hsc10 hout10 m10 hm10
  have hout10' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
      scr10[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout10 i hi (by rcases hor with h | h <;> omega)).trans (hout9' i hi hor)
  clear hout10 hout9' hm9
  unfold m7FinishIteExpr
  have h1056' : 1056 < scr10.length := by rw [hsc10]; omega
  have h1057' : 1057 < scr10.length := by rw [hsc10]; omega
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
    (fun x => (x, ())) (fun _ => True) ?_
    (fun _ hJtag => by
      c0_hsplit <;> (c0_hsteps!; exact hJtag _ trivial))
  intro _ tag _
  c0_hsteps!
  refine hQ true ((scr10.set (1056#64).toNat 1#32).set (1057#64).toNat tag) m ?_ ?_ ?_
  · simp [hsc10]
  · intro idx hidx hor
    rw [List.getElem?_set_ne (by
        rw [show (1057#64).toNat = 1057 from rfl]; omega),
      List.getElem?_set_ne (by
        rw [show (1056#64).toNat = 1056 from rfl]; omega)]
    exact hout10' idx hidx hor
  · assumption

/-! ## 2. `full_bve_find_ite_side_m7` and `full_bve_find_ite_m7` -/

/-- Parametric `Func.wp` proof for `full_bve_find_ite_side_m7`. -/
theorem full_bve_find_ite_side_m7_wp (Γ : Env)
    (hGetTern : ∀ a m Q X, fullBveGetTernM7Spec a m Q X →
      Γ "full_bve_get_tern_m7" [i64, i32, i32, i32] [.bool] a m Q X)
    (hMatchTern : ∀ a m Q X, fullBveMatchTernM7Spec a m Q X →
      Γ "full_bve_match_tern_m7" [i64, i32, i32, i32, i32, i32] [i32] a m Q X) :
    ∀ a m Q X, fullBveFindIteSideM7Spec a m Q X →
      Func.wp Γ full_bve_find_ite_side_m7_body a m Q X := by
  rintro ⟨h, v, np, nn, neg, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1066, hv_lt, hnp512, hnn512,
    hp_ok, hn_ok, hm0, hQ⟩ := fullBveFindIteSideM7Spec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl := m7_p3b_pl_nl_eq v (by omega)
  unfold Func.wp full_bve_find_ite_side_m7_body
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun x => x = if neg then 1#32 else 0#32) ?_
    (fun _ hJ => by
      c0_hsplit <;> (c0_hsteps!; exact hJ _ (by split <;> simp_all)))
  rintro _ fl rfl
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun x => x = if neg then 512#32 else 0#32) ?_
    (fun _ hJ => by
      c0_hsplit <;> (c0_hsteps!; exact hJ _ (by split <;> simp_all)))
  rintro _ lit_off rfl
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun x => x = if neg then nn else np) ?_
    (fun _ hJ => by
      c0_hsplit <;> (c0_hsteps!; exact hJ _ (by split <;> simp_all)))
  rintro _ lit_n rfl
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun x => x = if neg then 0#32 else 512#32) ?_
    (fun _ hJ => by
      c0_hsplit <;> (c0_hsteps!; exact hJ _ (by split <;> simp_all)))
  rintro _ opp_off rfl
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun x => x = if neg then np else nn) ?_
    (fun _ hJ => by
      c0_hsplit <;> (c0_hsteps!; exact hJ _ (by split <;> simp_all)))
  rintro _ opp_n rfl
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun x => x = if neg then 1040#32 else 1024#32) ?_
    (fun _ hJ => by
      c0_hsplit <;> (c0_hsteps!; exact hJ _ (by split <;> simp_all)))
  rintro _ lit_mask rfl
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun x => x = if neg then 1024#32 else 1040#32) ?_
    (fun _ hJ => by
      c0_hsplit <;> (c0_hsteps!; exact hJ _ (by split <;> simp_all)))
  rintro _ opp_mask rfl
  let lit := (v <<< (1 : Nat)) ||| (if neg then 1#32 else 0#32)
  let opp := lit ^^^ 1#32
  have hlit_nat : lit.toNat = if neg then 2 * v.toNat + 1 else 2 * v.toNat := by
    cases neg
    · simp only [lit, Bool.false_eq_true, ↓reduceIte, BitVec.or_zero]; exact hplnl.1
    · exact hplnl.2
  have hxor_or : (v <<< (1 : Nat)) ^^^ 1#32 = (v <<< (1 : Nat)) ||| 1#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_or, hplnl.1, BitVec.toNat_ofNat]
    rw [show (1 : Nat) % 2 ^ 32 = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.mul_mod_right]
      simp
    | succ j =>
      rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ]
      simp
  have hopp_nat : opp.toNat = if neg then 2 * v.toNat else 2 * v.toNat + 1 := by
    cases neg
    · simp only [opp, lit, Bool.false_eq_true, ↓reduceIte, BitVec.or_zero, hxor_or]
      exact hplnl.2
    · simp only [opp, lit, ↓reduceIte, ← hxor_or, BitVec.xor_assoc, BitVec.xor_self,
        BitVec.xor_zero]
      exact hplnl.1
  have hlit_lt : lit.toNat < 2 * s0.core.cur_vars := by
    rw [hlit_nat]; cases neg <;> simp <;> omega
  have hln_le : (if neg then nn else np).toNat ≤ 512 := by cases neg <;> simp <;> omega
  have hon_le : (if neg then np else nn).toNat ≤ 512 := by cases neg <;> simp <;> omega
  have hlo_bd : (if neg then 512#32 else 0#32).toNat + (if neg then nn else np).toNat ≤ 1024 := by
    cases neg <;> simp <;> omega
  have hoo_bd : (if neg then 0#32 else 512#32).toNat + (if neg then np else nn).toNat ≤ 1024 := by
    cases neg <;> simp <;> omega
  have hlm_bd : 1024 ≤ (if neg then 1040#32 else 1024#32).toNat ∧
      (if neg then 1040#32 else 1024#32).toNat + 16 ≤ 1056 := by
    cases neg <;> simp
  have hom_bd : 1024 ≤ (if neg then 1024#32 else 1040#32).toNat ∧
      (if neg then 1024#32 else 1040#32).toNat + 16 ≤ 1056 := by
    cases neg <;> simp
  have hlit_ent : ∀ i < (if neg then nn else np).toNat, FullBveEntryOkW F_cur s0 lit.toNat
      (s0.scratch.scratch_buf[(if neg then 512#32 else 0#32).toNat + i]?.getD 0#32) := by
    intro i hi; rw [hlit_nat]; cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod,
        Nat.zero_add] at hi ⊢
      exact hp_ok i hi
    · simp only [↓reduceIte, BitVec.toNat_ofNat] at hi ⊢; exact hn_ok i hi
  have hopp_ent : ∀ j < (if neg then np else nn).toNat, FullBveEntryOkW F_cur s0 opp.toNat
      (s0.scratch.scratch_buf[(if neg then 0#32 else 512#32).toNat + j]?.getD 0#32) := by
    intro j hj; rw [hopp_nat]; cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat] at hj ⊢; exact hn_ok j hj
    · simp only [↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add] at hj ⊢
      exact hp_ok j hj
  c0_hsteps_nogrp
  · exact hQ false s0.scratch.scratch_buf m0 hdw0.1.scratch_ok.scratch_buf_len
      (fun _ _ _ => rfl) hm0
  · exact hQ false s0.scratch.scratch_buf m0 hdw0.1.scratch_ok.scratch_buf_len
      (fun _ _ _ => rfl) hm0
  ·
      refine wp_loop_group (ts := [i64, i32])
        (fun rem (lc, idx, ()) mi => mi = m0 ∧ idx.toNat ≤ (if neg then nn else np).toNat ∧
          rem = (if neg then nn else np).toNat - idx.toNat ∧ lc.toNat ≤ idx.toNat)
        ?_ ?_
      · rintro L rem ⟨lc, idx, ⟨⟩⟩ mi hL ⟨rfl, hi_le, rfl, hlc_le⟩
        c0_hsplit
        · have hi_lt : idx.toNat < (if neg then nn else np).toNat := hc
          have hsc_idx : (((if neg then 512#32 else 0#32) + idx).setWidth 64).toNat <
              s0.scratch.scratch_buf.length := by
            rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
          have hi1 : (idx + 1 : BitVec 32).toNat = idx.toNat + 1 := by c0_bound
          have hi1 : (idx + 1#32).toNat = idx.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
            (fun x => x.toNat ≤ idx.toNat + 1) ?_
            (fun _ hJlc => by
              c0_hsplit
              · c0_hsteps!; exact hJlc (lc + 1#64) (by c0_bound)
              · c0_hsteps!; exact hJlc lc (by omega))
          intro _ lc' hlc'; c0_hsteps!
          exact hL ((if neg then nn else np).toNat - (idx + 1#32).toNat)
            (lc', idx + 1#32, ()) mi (by rw [hi1]; omega)
            ⟨rfl, by rw [hi1]; omega, by rw [hi1], by rw [hi1]; exact hlc'⟩
        · c0_hsplit
          · c0_hsteps!; exact hQ false s0.scratch.scratch_buf mi hdw0.1.scratch_ok.scratch_buf_len
              (fun _ _ _ => rfl) hm0
          · c0_hsplit
            · c0_hsteps!; exact hQ false s0.scratch.scratch_buf mi
                hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm0
            · have h1058_0 : 1058 < s0.scratch.scratch_buf.length := by
                rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i32])
                (fun rem0 (i0, ()) m1 => ∃ scr1 : List (BitVec 32),
                  let s1 : FullState :=
                    { s0 with scratch := { s0.scratch with scratch_buf := scr1 } }
                  scr1.length = c.scratch_cap ∧ i0.toNat ≤ (if neg then nn else np).toNat ∧
                  rem0 = (if neg then nn else np).toNat - i0.toNat ∧
                  (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                    scr1[i]? = s0.scratch.scratch_buf[i]?) ∧
                  (FullMem c s1 ⋆ R) m1)
                ?_ ?_
              · rintro L0 rem0 ⟨i0, ⟨⟩⟩ m1 hL0 ⟨scr1, hsc1, hi0_le, rfl, hout1, hm1⟩
                have h1058 : 1058 < scr1.length := by rw [hsc1]; omega
                c0_hsplit
                · have hc_i0 : (i0 + 1#32).toNat < (if neg then nn else np).toNat := hc
                  c0_hsplit
                  · have hi0_lt : i0.toNat + 1 < (if neg then nn else np).toNat := by
                      have := hc_i0; c0_bound
                    have hi0_sc : (((if neg then 512#32 else 0#32) + i0).setWidth 64).toNat <
                        scr1.length := by
                      rw [hsc1, m6_zext32_toNat]; c0_bound
                    have hi0_eq : (((if neg then 512#32 else 0#32) + i0).setWidth 64).toNat =
                        (if neg then 512#32 else 0#32).toNat + i0.toNat := by
                      rw [m6_zext32_toNat]; c0_bound
                    let w0 :=
                      scr1[(((if neg then 512#32 else 0#32) + i0).setWidth 64).toNat]'hi0_sc
                    have hw0_orig : w0 = s0.scratch.scratch_buf[
                        (if neg then 512#32 else 0#32).toNat + i0.toNat]?.getD 0#32 := by
                      have hg := hout1 ((if neg then 512#32 else 0#32).toNat + i0.toNat) (by omega)
                        (Or.inl (by omega))
                      have hi0' : (if neg then 512#32 else 0#32).toNat + i0.toNat < scr1.length :=
                        by omega
                      rw [List.getElem?_eq_getElem hi0'] at hg; rw [← hg, Option.getD_some]
                      exact (m6_getElem_congr hi0_eq.symm hi0' hi0_sc).symm
                    have hi01 : (i0 + 1#32).toNat = i0.toNat + 1 := by c0_bound
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [])
                      (fun _ m2' => ∃ scr2 : List (BitVec 32),
                        let s2 : FullState :=
                          { s0 with scratch := { s0.scratch with scratch_buf := scr2 } }
                        scr2.length = c.scratch_cap ∧
                        (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                          scr2[i]? = s0.scratch.scratch_buf[i]?) ∧
                        (FullMem c s2 ⋆ R) m2')
                      (fun _ _ m2' ⟨scr2, hsc2, hout2, hm2⟩ => by
                        c0_hsteps!
                        exact hL0 ((if neg then nn else np).toNat - (i0 + 1#32).toNat)
                          (i0 + 1#32, ()) m2' (by rw [hi01]; omega)
                          ⟨scr2, hsc2, by rw [hi01]; omega, rfl, hout2, hm2⟩)
                      ?_
                    intro _ hJ0
                    c0_hsplit
                    · have hw0_c0 :
                          w0 = scr1[((if neg then 512#32 else 0#32).toNat + i0.toNat) % 2 ^ 32]'(by
                            rw [Nat.mod_eq_of_lt (by omega), hsc1]; omega) :=
                        m6_getElem_congr (by rw [hi0_eq, Nat.mod_eq_of_lt (by omega)]) _ _
                      have hw0_bin0 : (w0 &&& 0x80000000#32) = 0#32 := by
                        rw [hw0_c0]; exact hc
                      have hent0 := hlit_ent i0.toNat (by omega)
                      rw [← hw0_orig] at hent0; unfold FullBveEntryOkW at hent0
                      rw [ite_eq_right (fun h => h hw0_bin0)] at hent0
                      have hdw1 : FullDenseInvW c F0 F_cur
                          { s0 with scratch := { s0.scratch with scratch_buf := scr1 } } :=
                        m7_p3b_fullDenseInvW_lm_scr hdw0 hdw0.1.core_ok.lit_mark_len hdw0.2.2.1.2
                          hsc1
                      c0_hsteps_nogrp
                      m7_call hGetTern
                      refine fullBveGetTernM7Spec_intro rfl hdw1 hent0.1 hent0.2
                        (by simp; omega) hm1 ?_
                      intro ok0 scr2 m2 s2 hsc2 hout2 hm2
                      have hm2' : (FullMem c { s0 with
                          scratch := { s0.scratch with scratch_buf := scr2 } } ⋆ R) m2 := hm2
                      have hout2' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                          scr2[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                        (hout2 i hi (by rcases hor with h | h <;> simp <;> omega)).trans
                          (hout1 i hi hor)
                      clear s2 hm2 hout2
                      c0_hsplit
                      · have h1060 : 1060 < scr2.length := by omega
                        have h1061 : 1061 < scr2.length := by omega
                        c0_hsteps_nogrp
                        refine wp_loop_group (ts := [i32])
                          (fun rem1 (i1, ()) m3 => ∃ scr3 : List (BitVec 32),
                            let s3 : FullState :=
                              { s0 with scratch := { s0.scratch with scratch_buf := scr3 } }
                            scr3.length = c.scratch_cap ∧
                            i1.toNat ≤ (if neg then nn else np).toNat ∧
                            rem1 = (if neg then nn else np).toNat - i1.toNat ∧
                            (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                              scr3[i]? = s0.scratch.scratch_buf[i]?) ∧
                            (FullMem c s3 ⋆ R) m3)
                          ?_ ?_
                        · rintro L1 rem1 ⟨i1, ⟨⟩⟩ m3 hL1 ⟨scr3, hsc3, hi1_le, rfl, hout3, hm3⟩
                          have h1058' : 1058 < scr3.length := by rw [hsc3]; omega
                          c0_hsplit
                          · have hc_i1 : i1.toNat < (if neg then nn else np).toNat := hc
                            c0_hsplit
                            · have hi1_lt : i1.toNat < (if neg then nn else np).toNat := hc_i1
                              have hi1_sc : (((if neg then 512#32 else 0#32) +
                                  i1).setWidth 64).toNat < scr3.length := by
                                rw [hsc3, m6_zext32_toNat]; c0_bound
                              have hi1_eq : (((if neg then 512#32 else 0#32) +
                                  i1).setWidth 64).toNat =
                                  (if neg then 512#32 else 0#32).toNat + i1.toNat := by
                                rw [m6_zext32_toNat]; c0_bound
                              let w1 := scr3[
                                (((if neg then 512#32 else 0#32) + i1).setWidth 64).toNat]'hi1_sc
                              have hw1_orig : w1 = s0.scratch.scratch_buf[
                                  (if neg then 512#32 else 0#32).toNat + i1.toNat]?.getD 0#32 := by
                                have hg := hout3 ((if neg then 512#32 else 0#32).toNat + i1.toNat)
                                  (by omega) (Or.inl (by omega))
                                have hi1' : (if neg then 512#32 else 0#32).toNat + i1.toNat <
                                    scr3.length := by omega
                                rw [List.getElem?_eq_getElem hi1'] at hg
                                rw [← hg, Option.getD_some]
                                exact (m6_getElem_congr hi1_eq.symm hi1' hi1_sc).symm
                              have hi11 : (i1 + 1#32).toNat = i1.toNat + 1 := by c0_bound
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun _ m4' => ∃ scr4 : List (BitVec 32),
                                  let s4 : FullState :=
                                    { s0 with
                                      scratch := { s0.scratch with scratch_buf := scr4 } }
                                  scr4.length = c.scratch_cap ∧
                                  (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                    scr4[i]? = s0.scratch.scratch_buf[i]?) ∧
                                  (FullMem c s4 ⋆ R) m4')
                                (fun _ _ m4' ⟨scr4, hsc4, hout4, hm4⟩ => by
                                  c0_hsteps!
                                  exact hL1
                                    ((if neg then nn else np).toNat - (i1 + 1#32).toNat)
                                    (i1 + 1#32, ()) m4' (by rw [hi11]; omega)
                                    ⟨scr4, hsc4, by rw [hi11]; omega, rfl, hout4, hm4⟩)
                                ?_
                              intro _ hJ1
                              c0_hsplit
                              · have hw1_c0 : w1 = scr3[((if neg then 512#32 else 0#32).toNat +
                                    i1.toNat) % 2 ^ 32]'(by
                                      rw [Nat.mod_eq_of_lt (by omega), hsc3]; omega) :=
                                  m6_getElem_congr
                                    (by rw [hi1_eq, Nat.mod_eq_of_lt (by omega)]) _ _
                                have hw1_bin0 : (w1 &&& 0x80000000#32) = 0#32 := by
                                  rw [hw1_c0]; exact hc
                                have hent1 := hlit_ent i1.toNat (by omega)
                                rw [← hw1_orig] at hent1; unfold FullBveEntryOkW at hent1
                                rw [ite_eq_right (fun h => h hw1_bin0)] at hent1
                                have hdw3 : FullDenseInvW c F0 F_cur
                                    { s0 with
                                      scratch := { s0.scratch with scratch_buf := scr3 } } :=
                                  m7_p3b_fullDenseInvW_lm_scr hdw0 hdw0.1.core_ok.lit_mark_len
                                    hdw0.2.2.1.2 hsc3
                                c0_hsteps_nogrp
                                m7_call hGetTern
                                refine fullBveGetTernM7Spec_intro rfl hdw3 hent1.1 hent1.2
                                  (by simp; omega) hm3 ?_
                                intro ok1 scr4 m4 s4 hsc4 hout4 hm4
                                have hm4' : (FullMem c { s0 with
                                    scratch := { s0.scratch with scratch_buf := scr4 } } ⋆ R)
                                    m4 := hm4
                                have hout4' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                    scr4[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                                  (hout4 i hi (by rcases hor with h | h <;> simp <;> omega)).trans
                                    (hout3 i hi hor)
                                clear s4 hm4 hout4
                                c0_hsplit
                                · have h1060' : 1060 < scr4.length := by omega
                                  have h1061' : 1061 < scr4.length := by omega
                                  have h1062 : 1062 < scr4.length := by omega
                                  have h1063 : 1063 < scr4.length := by omega
                                  c0_hsteps_nogrp
                                  refine wp_join_state_pure (ts := [.bool, i32, i32, i32])
                                    (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
                                    (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2, ())) (fun _ => True) ?_
                                    (fun _ hJok => by
                                      c0_hsplit
                                      · c0_hsteps!; exact hJok (_, _, _, _) trivial
                                      · c0_hsteps_nogrp
                                        refine wp_join_state_pure (ts := [.bool, i32, i32, i32])
                                          (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
                                          (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2, ()))
                                          (fun _ => True)
                                          (fun _ p _ => by c0_hsteps!; exact hJok p trivial)
                                          (fun _ hJk2 => by
                                            c0_hsplit
                                            · c0_hsteps!; exact hJk2 (_, _, _, _) trivial
                                            · c0_hsteps_nogrp
                                              refine wp_join_state_pure
                                                (ts := [.bool, i32, i32, i32])
                                                (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
                                                (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2, ()))
                                                (fun _ => True)
                                                (fun _ p _ => by c0_hsteps!; exact hJk2 p trivial)
                                                (fun _ hJk3 => by
                                                  c0_hsplit
                                                  · c0_hsteps!; exact hJk3 (_, _, _, _) trivial
                                                  · c0_hsteps_nogrp
                                                    refine wp_join_state_pure
                                                      (ts := [.bool, i32, i32, i32])
                                                      (α := Bool × BitVec 32 ×
                                                        BitVec 32 × BitVec 32)
                                                      (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2, ()))
                                                      (fun _ => True)
                                                      (fun _ p _ => by
                                                        c0_hsteps!; exact hJk3 p trivial)
                                                      (fun _ hJk4 => by
                                                        c0_hsplit <;>
                                                          (c0_hsteps!
                                                           exact hJk4 (_, _, _, _) trivial)))))
                                  intro _ ⟨ok_c, cond, u, w⟩ _
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [])
                                    (fun _ mf => ∃ scr_e : List (BitVec 32),
                                      let s_e : FullState :=
                                        { s0 with
                                          scratch := { s0.scratch with scratch_buf := scr_e } }
                                      scr_e.length = c.scratch_cap ∧
                                      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                        scr_e[i]? = s0.scratch.scratch_buf[i]?) ∧
                                      (FullMem c s_e ⋆ R) mf)
                                    (fun _ _ mf ⟨scr_e, hse, houte, hme⟩ => by
                                      c0_hsteps!; exact hJ1 () mf ⟨scr_e, hse, houte, hme⟩)
                                    ?_
                                  intro _ hJno
                                  c0_hsplit
                                  · have hdw4 : FullDenseInvW c F0 F_cur
                                        { s0 with
                                          scratch := { s0.scratch with scratch_buf := scr4 } } :=
                                      m7_p3b_fullDenseInvW_lm_scr hdw0
                                        hdw0.1.core_ok.lit_mark_len hdw0.2.2.1.2 hsc4
                                    c0_hsteps_nogrp
                                    rotate_left 1
                                    · exact hJno () m4 ⟨scr4, hsc4, hout4', hm4'⟩
                                    m7_call hMatchTern
                                    refine fullBveMatchTernM7Spec_intro rfl hdw4 (by omega) hoo_bd
                                      hon_le (fun j hj => by
                                        dsimp only [Arg.val] at hj ⊢
                                        rw [hout4' ((if neg then 0#32 else 512#32).toNat + j)
                                          (by omega) (Or.inl (by omega))]
                                        exact hopp_ent j hj) hm4' ?_
                                    intro r0 scr5 m5 s5 hsc5 hout5 hr0_bd hm5
                                    have hm5' : (FullMem c { s0 with
                                        scratch := { s0.scratch with scratch_buf := scr5 } } ⋆ R)
                                        m5 := hm5
                                    have hout5' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                        scr5[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                                      (hout5 i hi (by rcases hor with h | h <;> omega)).trans
                                        (hout4' i hi hor)
                                    clear s5 hm5 hout5
                                    c0_hsteps_nogrp
                                    refine wp_join_group (ts := [])
                                      (fun _ m5' => ∃ scr_e : List (BitVec 32),
                                        let s_e : FullState :=
                                          { s0 with
                                            scratch := { s0.scratch with scratch_buf := scr_e } }
                                        scr_e.length = c.scratch_cap ∧
                                        (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                          scr_e[i]? = s0.scratch.scratch_buf[i]?) ∧
                                        (FullMem c s_e ⋆ R) m5')
                                      (fun _ _ m5' ⟨scr_e, hse, houte, hme⟩ => by
                                        c0_hsteps!; exact hJno () m5' ⟨scr_e, hse, houte, hme⟩)
                                      ?_
                                    intro _ hJm0
                                    c0_hsplit
                                    · dsimp only [Arg.val] at hr0_bd
                                      have hr0_lt : (r0 &&& 0x7FFFFFFF#32).toNat < 512 := by
                                        have := m7_p3b_u32_and7fff_lt r0 hr0_bd hc; omega
                                      have hdw5 : FullDenseInvW c F0 F_cur
                                          { s0 with
                                            scratch := { s0.scratch with scratch_buf := scr5 } } :=
                                        m7_p3b_fullDenseInvW_lm_scr hdw0
                                          hdw0.1.core_ok.lit_mark_len hdw0.2.2.1.2 hsc5
                                      c0_hsteps_nogrp
                                      m7_call hMatchTern
                                      refine fullBveMatchTernM7Spec_intro rfl hdw5 (by omega) hoo_bd
                                        hon_le (fun j hj => by
                                          dsimp only [Arg.val] at hj ⊢
                                          rw [hout5' ((if neg then 0#32 else 512#32).toNat + j)
                                            (by omega) (Or.inl (by omega))]
                                          exact hopp_ent j hj) hm5' ?_
                                      intro r1 scr6 m6 s6 hsc6 hout6 hr1_bd hm6
                                      have hm6' : (FullMem c { s0 with
                                          scratch := { s0.scratch with scratch_buf := scr6 } } ⋆ R)
                                          m6 := hm6
                                      have hout6' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                          scr6[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                                        (hout6 i hi (by rcases hor with h | h <;> omega)).trans
                                          (hout5' i hi hor)
                                      clear s6 hm6 hout6
                                      c0_hsteps_nogrp
                                      refine wp_join_group (ts := [])
                                        (fun _ mf' => ∃ scr_e : List (BitVec 32),
                                          let s_e : FullState :=
                                            { s0 with
                                              scratch := { s0.scratch with scratch_buf := scr_e } }
                                          scr_e.length = c.scratch_cap ∧
                                          (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                            scr_e[i]? = s0.scratch.scratch_buf[i]?) ∧
                                          (FullMem c s_e ⋆ R) mf')
                                        (fun _ _ mf' ⟨scr_e, hse, houte, hme⟩ => by
                                          c0_hsteps!; exact hJm0 () mf' ⟨scr_e, hse, houte, hme⟩)
                                        ?_
                                      intro _ hJm1
                                      c0_hsplit
                                      · dsimp only [Arg.val] at hr1_bd
                                        have hr1_lt : (r1 &&& 0x7FFFFFFF#32).toNat < 512 := by
                                          have := m7_p3b_u32_and7fff_lt r1 hr1_bd hc; omega
                                        clear hdw5 hdw4 hdw3 hdw1 hdw0 hlit_ent hopp_ent
                                          hp_ok hn_ok hm5' hm4' hm3 hm1 hJ1 hJ0
                                          hJno hJm0 hL1 hL0 hL
                                        c0_hstep; c0_hstep; c0_hstep; c0_hsplit
                                        rotate_left 1
                                        · c0_hsteps!
                                          exact hJm1 () m6 ⟨scr6, hsc6, hout6', hm6'⟩
                                        clear hJm1
                                        exact m7_p3b_ite_hit_wp Γ c s0 scr6 R _ _ i0 i1 r0 r1
                                          m6 Q X hsc6 hout6' hsc1066
                                          (by cases neg <;> simp) (by cases neg <;> simp)
                                          (by cases neg <;> simp) (by cases neg <;> simp)
                                          (by omega) (by omega) hr0_lt hr1_lt hm6' hQ
                                      · c0_hsteps!; exact hJm1 () m6 ⟨scr6, hsc6, hout6', hm6'⟩
                                    · c0_hsteps!; exact hJm0 () m5 ⟨scr5, hsc5, hout5', hm5'⟩
                                  · c0_hsteps!; exact hJno () m4 ⟨scr4, hsc4, hout4', hm4'⟩
                                · c0_hsteps!; exact hJ1 () m4 ⟨scr4, hsc4, hout4', hm4'⟩
                              · c0_hsteps!; exact hJ1 () m3 ⟨scr3, hsc3, hout3, hm3⟩
                            · c0_hsteps!; exact hJ0 () m3 ⟨scr3, hsc3, hout3, hm3⟩
                          · c0_hsteps!; exact hJ0 () m3 ⟨scr3, hsc3, hout3, hm3⟩
                        · intro L1 hL1; c0_hsteps!
                          exact hL1 ((if neg then nn else np).toNat -
                              (i0 + 1#32).toNat)
                            (i0 + 1#32, ()) m2
                            ⟨scr2, hsc2, by rw [hi01]; omega, rfl, hout2', hm2'⟩
                      · c0_hsteps!; exact hJ0 () m2 ⟨scr2, hsc2, hout2', hm2'⟩
                    · c0_hsteps!; exact hJ0 () m1 ⟨scr1, hsc1, hout1, hm1⟩
                  · c0_hsteps!; exact hQ false scr1 m1 hsc1 hout1 hm1
                · c0_hsteps!; exact hQ false scr1 m1 hsc1 hout1 hm1
              · intro L0 hL0; c0_hsteps!
                refine hL0 (if neg then nn else np).toNat (0#32, ()) _
                  ⟨s0.scratch.scratch_buf.set 1058 0#32, ?_, Nat.zero_le _, by simp,
                    fun i hi hor => by rw [List.getElem?_set_ne (by omega)], ?_⟩
                · rw [List.length_set, hdw0.1.scratch_ok.scratch_buf_len]
                · assumption
      · intro L hL; c0_hsteps!
        exact hL (if neg then nn else np).toNat (0#64, 0#32, ()) m0
          ⟨rfl, Nat.zero_le _, by simp, Nat.zero_le _⟩

/-- Parametric `Func.wp` proof for `full_bve_find_ite_m7`. -/
theorem full_bve_find_ite_m7_wp (Γ : Env)
    (hFindIteSide : ∀ a m Q X, fullBveFindIteSideM7Spec a m Q X →
      Γ "full_bve_find_ite_side_m7" [i64, i32, i32, i32, .bool] [.bool] a m Q X) :
    ∀ a m Q X, fullBveFindIteM7Spec a m Q X →
      Func.wp Γ full_bve_find_ite_m7_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1066, hv_lt, hnp512, hnn512,
    hp_ok, hn_ok, hm0, hQ⟩ := fullBveFindIteM7Spec_elim hSpec
  unfold Func.wp full_bve_find_ite_m7_body
  c0_hsteps_nogrp
  m7_call hFindIteSide
  change fullBveFindIteSideM7Spec (c.hdr, v, np, nn, false, ()) _ _ _
  refine fullBveFindIteSideM7Spec_intro rfl hdw0 hsc1066 hv_lt hnp512 hnn512 hp_ok hn_ok hm0 ?_
  intro ok1 scr1 m1 s1 hsc1 hout1 hm1
  c0_hsplit
  · c0_hsteps!; exact hQ true scr1 m1 hsc1 hout1 hm1
  · have hdw1 : FullDenseInvW c F0 F_cur s1 :=
      m7_p3b_fullDenseInvW_lm_scr hdw0 hdw0.1.core_ok.lit_mark_len hdw0.2.2.1.2 hsc1
    c0_hsteps_nogrp
    m7_call hFindIteSide
    change fullBveFindIteSideM7Spec (c.hdr, v, np, nn, true, ()) _ _ _
    refine fullBveFindIteSideM7Spec_intro rfl hdw1 hsc1066 hv_lt hnp512 hnn512
      (fun i hi => by
        dsimp only [s1]; rw [hout1 i (by have := c.hscr; unfold dimacsBound at this; omega)
          (Or.inl (by omega))]
        exact m7_p3b_bveEntry_congr_core (hp_ok i hi) rfl rfl rfl)
      (fun j hj => by
        dsimp only [s1]; rw [hout1 (512 + j) (by have := c.hscr; unfold dimacsBound at this; omega)
          (Or.inl (by omega))]
        exact m7_p3b_bveEntry_congr_core (hn_ok j hj) rfl rfl rfl)
      hm1 ?_
    intro ok2 scr2 m2 s2 hsc2 hout2 hm2
    c0_hsteps!
    exact hQ ok2 scr2 m2 hsc2 (fun i hi hor => (hout2 i hi hor).trans (hout1 i hi hor)) hm2

/-! ## 3. `full_bve_find_xor_m7` -/

private theorem m7_p3b_xor1_lt (l : BitVec 32) {n : Nat} (hl : l.toNat < 2 * n) :
    (l ^^^ 1#32).toNat < 2 * n := by
  have heq : (l ^^^ 1#32) >>> (1 : Nat) = l >>> (1 : Nat) := by
    ext i _; simp [BitVec.getLsbD_xor]
  have hdiv : (l ^^^ 1#32).toNat / 2 = l.toNat / 2 := by
    have := congrArg BitVec.toNat heq
    simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this
  omega

private theorem m7_p3b_bit_test_imp (mask p : BitVec 32) (hp : p.toNat < 16)
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

private theorem m7_p3b_lengths_witness_lm_scr {c : FullCfg} {F0 : CNF Nat}
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

private def m7XorLmClearExpr (pScr pLm : BitVec 64) (k : BitVec 32)
    (after : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32]])
    (fun lbls =>
      Blocks.cons (fun c_idx =>
        Expr.let_ ⟨OpCode.ult i32, (Arg.var c_idx.fst, Arg.var k, ())⟩ fun b =>
        Expr.jnz (Arg.var b.fst)
          (Expr.let_ ⟨OpCode.add i32, (Arg.imm 1092, Arg.var c_idx.fst, ())⟩ fun p0 =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p0.fst, ())⟩ fun p1 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun p2 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p2.fst, ())⟩ fun p3 =>
           Expr.load i32 (Arg.var p3.fst) fun l =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var l, ())⟩ fun q0 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pLm, Arg.var q0.fst, ())⟩ fun q1 =>
           Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm (t := i32) 0, ())⟩ fun z0 =>
           Expr.store (Arg.var z0.fst) (Arg.var q1.fst) (
           Expr.let_ ⟨OpCode.xor i32, (Arg.var l, Arg.imm 1, ())⟩ fun lx =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var lx.fst, ())⟩ fun r0 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pLm, Arg.var r0.fst, ())⟩ fun r1 =>
           Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm (t := i32) 0, ())⟩ fun z1 =>
           Expr.store (Arg.var z1.fst) (Arg.var r1.fst) (
           Expr.let_ ⟨OpCode.add i32, (Arg.var c_idx.fst, Arg.imm 1, ())⟩ fun nx =>
           Expr.jump lbls.1 (Arg.var nx.fst, ()))))
          after)
        Blocks.nil)
    (fun lbls => Expr.jump lbls.1 (Arg.imm (t := i32) 0, ()))

private theorem m7_p3b_xor_clean_lm_wp (Γ : Env) (c : FullCfg) (s0 : FullState)
    (lm : List (BitVec 8)) (scr : List (BitVec 32)) (R : Mem 64 → Prop)
    (k : BitVec 32) (m : Mem 64) (Q : Post [.bool]) (X : XPost)
    (after : Expr Val Cont [.bool])
    (hlm : lm.length = 2 * c.max_vars) (hsc : scr.length = c.scratch_cap)
    (h1096 : 1096 ≤ c.scratch_cap) (hk4 : k.toNat ≤ 4)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hrec : ∀ j < k.toNat, (scr[1092 + j]?.getD 0#32).toNat < 2 * s0.core.cur_vars)
    (hnz : ∀ y < 2 * c.max_vars, lm[y]?.getD 0#8 ≠ 0#8 →
      ∃ j < k.toNat, y = (scr[1092 + j]?.getD 0#32).toNat ∨
        y = ((scr[1092 + j]?.getD 0#32) ^^^ 1#32).toNat)
    (hm : (FullMem c { s0 with
        core := { s0.core with lit_mark := lm }
        scratch := { s0.scratch with scratch_buf := scr } } ⋆ R) m)
    (hafter : ∀ (lm' : List (BitVec 8)), lm'.length = 2 * c.max_vars →
      (∀ y < 2 * c.max_vars, lm'[y]?.getD 0#8 = 0#8) →
      ∀ m', (FullMem c { s0 with
          core := { s0.core with lit_mark := lm' }
          scratch := { s0.scratch with scratch_buf := scr } } ⋆ R) m' →
        wp Γ Q X after m') :
    wp Γ Q X (m7XorLmClearExpr c.pScratchBuf c.pLitMark k after) m := by
  unfold m7XorLmClearExpr
  refine wp_loop_group (ts := [i32])
    (fun rem (ci, ()) mc => ∃ lmc : List (BitVec 8),
      let sc : FullState :=
        { s0 with
          core := { s0.core with lit_mark := lmc }
          scratch := { s0.scratch with scratch_buf := scr } }
      lmc.length = 2 * c.max_vars ∧ ci.toNat ≤ k.toNat ∧ rem = k.toNat - ci.toNat ∧
      (∀ y < 2 * c.max_vars, lmc[y]?.getD 0#8 ≠ 0#8 →
        ∃ j, ci.toNat ≤ j ∧ j < k.toNat ∧
          (y = (scr[1092 + j]?.getD 0#32).toNat ∨
            y = ((scr[1092 + j]?.getD 0#32) ^^^ 1#32).toNat)) ∧
      (FullMem c sc ⋆ R) mc)
    ?_ ?_
  · rintro L rem ⟨ci, ⟨⟩⟩ mc hL ⟨lmc, hlmc, hci_le, rfl, hnz_c, hmc⟩
    c0_hsplit
    · have hc_ci : ci.toNat < k.toNat := hc
      have hsc_idx : ((1092#32 + ci).setWidth 64).toNat < scr.length := by
        rw [hsc, m6_zext32_toNat]; c0_bound
      have hsc_eq : ((1092#32 + ci).setWidth 64).toNat = 1092 + ci.toNat := by
        rw [m6_zext32_toNat]; c0_bound
      let l := scr[((1092#32 + ci).setWidth 64).toNat]'hsc_idx
      have hl_orig : l = scr[1092 + ci.toNat]?.getD 0#32 := by
        have hlt : 1092 + ci.toNat < scr.length := by omega
        rw [List.getElem?_eq_getElem hlt, Option.getD_some]
        exact m6_getElem_congr hsc_eq hsc_idx hlt
      have hl_lt : l.toNat < 2 * c.max_vars := by
        have := hrec ci.toNat hc_ci; rw [← hl_orig] at this; omega
      have hl1_lt : (l ^^^ 1#32).toNat < 2 * c.max_vars := by
        have := m7_p3b_xor1_lt l (by rw [hl_orig]; exact hrec ci.toNat hc_ci)
        omega
      have hl_sc : (l.setWidth 64).toNat < lmc.length := by
        rw [hlmc, m6_zext32_toNat]; exact hl_lt
      have hl1_sc : ((l ^^^ 1#32).setWidth 64).toNat < lmc.length := by
        rw [hlmc, m6_zext32_toNat]; exact hl1_lt
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      dsimp only at hm ⊢
      have hl1_set : (((l ^^^ 1#32).setWidth 64).toNat) <
          (lmc.set (l.setWidth 64).toNat 0#8).length := by
        rw [List.length_set]; exact hl1_sc
      c0_hsteps_nogrp
      refine hL (k.toNat - (ci + 1#32).toNat) (ci + 1#32, ()) _ (by rw [hci1]; omega)
        ⟨_, ?_, by rw [hci1]; omega, rfl, ?_, by assumption⟩
      · rw [List.length_set, List.length_set, hlmc]
      · dsimp only
        refine m7_p3b_lm_clear2_step hlmc (by rw [m6_zext32_toNat]; exact hl_lt)
          (by rw [m6_zext32_toNat]; exact hl1_lt) (fun y hy hy_nz => ?_)
        obtain ⟨j, hj_ge, hj_lt, hy_eq⟩ := hnz_c y hy hy_nz
        by_cases hjeq : j = ci.toNat
        · subst hjeq; rw [← hl_orig] at hy_eq
          rcases hy_eq with h0 | h1
          · exact Or.inl (h0.trans (m6_zext32_toNat _).symm)
          · exact Or.inr (Or.inl (h1.trans (m6_zext32_toNat _).symm))
        · exact Or.inr (Or.inr ⟨j, by omega, hj_lt, hy_eq⟩)
    · have hclr : ∀ y < 2 * c.max_vars, lmc[y]?.getD 0#8 = 0#8 := fun y hy =>
        Classical.byContradiction fun hy_nz => by
          obtain ⟨j, hj_ge, hj_lt, _⟩ := hnz_c y hy hy_nz
          omega
      exact hafter lmc hlmc hclr mc hmc
  · intro L hL; c0_hsteps!
    exact hL k.toNat (0#32, ()) m
      ⟨lm, hlm, Nat.zero_le _, by simp,
        fun y hy hy_nz => let ⟨j, hj, hy_eq⟩ := hnz y hy hy_nz; ⟨j, Nat.zero_le _, hj, hy_eq⟩,
        hm⟩

private def m7XorCommitExpr (pScr : BitVec 64) (k fullPmask fullNmask : BitVec 32) :
    Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var k, ())⟩ fun need =>
  Expr.group (sig := [[i32]])
    (fun lbl69 =>
      Blocks.cons (fun p =>
        Expr.let_ ⟨OpCode.ult i32, (Arg.var p.fst, Arg.var need.fst, ())⟩ fun cond =>
        Expr.jnz (Arg.var cond.fst)
          (Expr.group (sig := [[]])
            (fun _lbl72 =>
              Blocks.cons (fun _ =>
                Expr.group (sig := [[]])
                  (fun _lbl73 =>
                    Blocks.cons (fun _ =>
                      Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun np =>
                      Expr.jump lbl69.1 (Arg.var np.fst, ())) Blocks.nil)
                  (fun lbl73 =>
                    Expr.let_ ⟨OpCode.lshr i32, (Arg.var fullNmask, Arg.var p.fst, ())⟩ fun s =>
                    Expr.let_ ⟨OpCode.and i32, (Arg.var s.fst, Arg.imm 1, ())⟩ fun b =>
                    Expr.let_ ⟨OpCode.ne i32, (Arg.var b.fst, Arg.imm 0, ())⟩ fun c0 =>
                    Expr.jnz (Arg.var c0.fst)
                      (Expr.let_ ⟨OpCode.add i32, (Arg.imm 1076, Arg.var p.fst, ())⟩ fun a0 =>
                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var a0.fst, ())⟩ fun a1 =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var a1.fst, Arg.imm 4, ())⟩ fun a2 =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var a2.fst, ())⟩ fun a3 =>
                       Expr.load i32 (Arg.var a3.fst) fun idx =>
                       m7SetMaskBitExpr pScr 1040#32 idx (Expr.jump lbl73.1 ()))
                      (Expr.jump lbl73.1 ()))) Blocks.nil)
            (fun lbl72 =>
              Expr.let_ ⟨OpCode.lshr i32, (Arg.var fullPmask, Arg.var p.fst, ())⟩ fun s =>
              Expr.let_ ⟨OpCode.and i32, (Arg.var s.fst, Arg.imm 1, ())⟩ fun b =>
              Expr.let_ ⟨OpCode.ne i32, (Arg.var b.fst, Arg.imm 0, ())⟩ fun c0 =>
              Expr.jnz (Arg.var c0.fst)
                (Expr.let_ ⟨OpCode.add i32, (Arg.imm 1060, Arg.var p.fst, ())⟩ fun a0 =>
                 Expr.let_ ⟨OpCode.zext 32 64, (Arg.var a0.fst, ())⟩ fun a1 =>
                 Expr.let_ ⟨OpCode.mul i64, (Arg.var a1.fst, Arg.imm 4, ())⟩ fun a2 =>
                 Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var a2.fst, ())⟩ fun a3 =>
                 Expr.load i32 (Arg.var a3.fst) fun idx =>
                 m7SetMaskBitExpr pScr 1024#32 idx (Expr.jump lbl72.1 ()))
                (Expr.jump lbl72.1 ())))
          (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm (t := i32) 1056, ())⟩ fun w0 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var w0.fst, Arg.imm 4, ())⟩ fun w1 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var w1.fst, ())⟩ fun w2 =>
           Expr.store (Arg.imm (t := i32) 1) (Arg.var w2.fst) (
           Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm (t := i32) 1057, ())⟩ fun y0 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var y0.fst, Arg.imm 4, ())⟩ fun y1 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var y1.fst, ())⟩ fun y2 =>
           Expr.store (Arg.imm (t := i32) 0) (Arg.var y2.fst) (
           Expr.ret (Arg.imm (t := .bool) true, ())))))
        Blocks.nil)
    (fun lbl69 => Expr.jump lbl69.1 (Arg.imm (t := i32) 0, ()))

private theorem m7_p3b_xor_commit_wp (Γ : Env) (c : FullCfg) (s0 : FullState)
    (scr_in : List (BitVec 32)) (R : Mem 64 → Prop)
    (k fullPmask fullNmask : BitVec 32)
    (m_in : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hsc_in : scr_in.length = c.scratch_cap)
    (hout_in : ∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
      scr_in[i]? = s0.scratch.scratch_buf[i]?)
    (hsc1096 : 1096 ≤ c.scratch_cap) (hk1 : 1 ≤ k.toNat) (hk4 : k.toNat ≤ 4)
    (hpm_ok : ∀ b < 16, (fullPmask &&& (1#32 <<< b)) ≠ 0#32 →
      (scr_in[1060 + b]?.getD 0#32).toNat < 512)
    (hnm_ok : ∀ b < 16, (fullNmask &&& (1#32 <<< b)) ≠ 0#32 →
      (scr_in[1076 + b]?.getD 0#32).toNat < 512)
    (hm_in : (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr_in } } ⋆ R)
      m_in)
    (hQ : ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
        scr'[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (ok, ()) m') :
    wp Γ Q X (m7XorCommitExpr c.pScratchBuf k fullPmask fullNmask) m_in := by
  have hneed_le : (1#32 <<< k).toNat ≤ 16 := by
    change (1#32 <<< k.toNat).toNat ≤ 16
    have hpow : 2 ^ k.toNat ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) hk4
    rw [BitVec.toNat_shiftLeft, show (1#32).toNat = 1 from rfl, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt (by omega)]
    exact hpow
  unfold m7XorCommitExpr
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (p, ()) mc => ∃ scr_c : List (BitVec 32),
      let sc : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_c } }
      scr_c.length = c.scratch_cap ∧ p.toNat ≤ (1#32 <<< k).toNat ∧
      rem = (1#32 <<< k).toNat - p.toNat ∧
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) → scr_c[i]? = scr_in[i]?) ∧
      (FullMem c sc ⋆ R) mc)
    ?_ ?_
  · rintro L rem ⟨p, ⟨⟩⟩ mc hL ⟨scr_c, hsc_c, hp_le, rfl, hout_c, hm_c⟩
    c0_hsplit
    · have hp_lt : p.toNat < (1#32 <<< k).toNat := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      have hp16 : p.toNat < 16 := by omega
      have hp1 : (p + 1#32).toNat = p.toNat + 1 := by c0_bound
      refine wp_join_group (ts := [])
        (fun _ m72 => ∃ scr_d : List (BitVec 32),
          let sd : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_d } }
          scr_d.length = c.scratch_cap ∧
          (∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) → scr_d[i]? = scr_in[i]?) ∧
          (FullMem c sd ⋆ R) m72)
        (fun _ _ m72 ⟨scr_d, hsc_d, hout_d, hm_d⟩ => by
          refine wp_join_group (ts := [])
            (fun _ m73 => ∃ scr_e : List (BitVec 32),
              let se : FullState :=
                { s0 with scratch := { s0.scratch with scratch_buf := scr_e } }
              scr_e.length = c.scratch_cap ∧
              (∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) → scr_e[i]? = scr_in[i]?) ∧
              (FullMem c se ⋆ R) m73)
            (fun _ _ m73 ⟨scr_e, hsc_e, hout_e, hm_e⟩ => by
              c0_hsteps!
              exact hL ((1#32 <<< k).toNat - (p + 1#32).toNat) (p + 1#32, ()) m73
                (by rw [hp1]; omega) ⟨scr_e, hsc_e, by rw [hp1]; omega, rfl, hout_e, hm_e⟩)
            ?_
          intro _ hJ73
          c0_hsteps_nogrp
          c0_hsplit
          · have hnm_b : ((fullNmask >>> p.toNat) &&& 1#32) ≠ 0#32 := by
              rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
            have hnm_bit := m7_p3b_bit_test_imp fullNmask p hp16 hnm_b
            have h1076_lt : ((1076#32 + p).setWidth 64).toNat < scr_d.length := by
              rw [hsc_d, m6_zext32_toNat]; c0_bound
            have h1076_eq : ((1076#32 + p).setWidth 64).toNat = 1076 + p.toNat := by
              rw [m6_zext32_toNat]; c0_bound
            let idx := scr_d[((1076#32 + p).setWidth 64).toNat]'h1076_lt
            have hidx_orig : idx = scr_in[1076 + p.toNat]?.getD 0#32 := by
              have hlt : 1076 + p.toNat < scr_d.length := by omega
              have hg := hout_d (1076 + p.toNat) (by omega) (Or.inr (by omega))
              rw [List.getElem?_eq_getElem hlt] at hg
              rw [← hg, Option.getD_some]
              exact m6_getElem_congr h1076_eq h1076_lt hlt
            have hidx_lt : idx.toNat < 512 := by
              have := hnm_ok p.toNat hp16 hnm_bit; rw [← hidx_orig] at this; exact this
            c0_hsteps_nogrp
            refine m7_p3b_setMaskBit_wp Γ c s0 scr_d R 1040#32 idx m72 Q X _
              hsc_d (by omega) (by decide) (by decide) hidx_lt hm_d ?_
            intro scr_e hsc_e hout_e me hm_e
            have hout_e' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) →
                scr_e[i]? = scr_in[i]? :=
              fun i hi hor => (hout_e i hi hor).trans (hout_d i hi hor)
            c0_hsteps!
            exact hJ73 () me ⟨scr_e, hsc_e, hout_e', hm_e⟩
          · c0_hsteps!
            exact hJ73 () m72 ⟨scr_d, hsc_d, hout_d, hm_d⟩)
        ?_
      intro _ hJ72
      c0_hsteps_nogrp
      c0_hsplit
      · have hpm_b : ((fullPmask >>> p.toNat) &&& 1#32) ≠ 0#32 := by
          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
        have hpm_bit := m7_p3b_bit_test_imp fullPmask p hp16 hpm_b
        have h1060_lt : ((1060#32 + p).setWidth 64).toNat < scr_c.length := by
          rw [hsc_c, m6_zext32_toNat]; c0_bound
        have h1060_eq : ((1060#32 + p).setWidth 64).toNat = 1060 + p.toNat := by
          rw [m6_zext32_toNat]; c0_bound
        let idx := scr_c[((1060#32 + p).setWidth 64).toNat]'h1060_lt
        have hidx_orig : idx = scr_in[1060 + p.toNat]?.getD 0#32 := by
          have hlt : 1060 + p.toNat < scr_c.length := by omega
          have hg := hout_c (1060 + p.toNat) (by omega) (Or.inr (by omega))
          rw [List.getElem?_eq_getElem hlt] at hg
          rw [← hg, Option.getD_some]
          exact m6_getElem_congr h1060_eq h1060_lt hlt
        have hidx_lt : idx.toNat < 512 := by
          have := hpm_ok p.toNat hp16 hpm_bit; rw [← hidx_orig] at this; exact this
        c0_hsteps_nogrp
        refine m7_p3b_setMaskBit_wp Γ c s0 scr_c R 1024#32 idx mc Q X _
          hsc_c (by omega) (by decide) (by decide) hidx_lt hm_c ?_
        intro scr_d hsc_d hout_d md hm_d
        have hout_d' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1056 ≤ i) →
            scr_d[i]? = scr_in[i]? :=
          fun i hi hor => (hout_d i hi hor).trans (hout_c i hi hor)
        c0_hsteps!
        exact hJ72 () md ⟨scr_d, hsc_d, hout_d', hm_d⟩
      · c0_hsteps!
        exact hJ72 () mc ⟨scr_c, hsc_c, hout_c, hm_c⟩
    · have h1056' : 1056 < scr_c.length := by rw [hsc_c]; omega
      have h1057' : 1057 < scr_c.length := by rw [hsc_c]; omega
      c0_hsteps!
      refine hQ true ((scr_c.set (1056#64).toNat 1#32).set (1057#64).toNat 0#32) m ?_ ?_ hm
      · simp [hsc_c]
      · intro idx hidx hor
        rw [List.getElem?_set_ne (by
            rw [show (1057#64).toNat = 1057 from rfl]; omega),
          List.getElem?_set_ne (by
            rw [show (1056#64).toNat = 1056 from rfl]; omega)]
        exact (hout_c idx hidx (by rcases hor with h | h <;> omega)).trans
          (hout_in idx hidx hor)
  · intro L hL; c0_hsteps!
    exact hL (1#32 <<< k).toNat (0#32, ()) m_in
      ⟨scr_in, hsc_in, Nat.zero_le _, by simp, fun _ _ _ => rfl, hm_in⟩

private abbrev m7XorState (s : FullState) (lm : List (BitVec 8))
    (scr : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with lit_mark := lm }
    scratch := { s.scratch with scratch_buf := scr } }

private def XorMaskEntriesOk (scr : List (BitVec 32)) (base lim : Nat)
    (mask : BitVec 32) : Prop :=
  mask.toNat < 65536 ∧
  ∀ t < 16, (mask &&& (1#32 <<< t)) ≠ 0#32 → (scr[base + t]?.getD 0#32).toNat < lim

private theorem m7_p3b_shl16_toNat {p : BitVec 32} (hp : p.toNat < 16) :
    (1#32 <<< p).toNat = 2 ^ p.toNat := by
  change (1#32 <<< p.toNat).toNat = 2 ^ p.toNat
  rw [BitVec.toNat_shiftLeft, show (1#32).toNat = 1 from rfl, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.pow_lt_pow_right (by omega) hp) (by omega))

private theorem xorMaskEntriesOk_init {scr : List (BitVec 32)} {base lim : Nat}
    (hlen : base + 16 ≤ scr.length) {idx : BitVec 32} (hidx : idx.toNat < lim) :
    XorMaskEntriesOk (scr.set base idx) base lim 1#32 := by
  refine ⟨by decide, fun t ht hbit => ?_⟩
  have ht0 : t = 0 := by
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rfl
    · exfalso; apply hbit
      apply BitVec.eq_of_getLsbD_eq; intro k
      by_cases hk : k = 0 <;> simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft] <;> omega
  subst ht0
  rw [show base + 0 = base from Nat.add_zero _, List.getElem?_set_self (by omega),
    Option.getD_some]
  exact hidx

private theorem xorMaskEntriesOk_zero (scr : List (BitVec 32)) (base lim : Nat) :
    XorMaskEntriesOk scr base lim 0#32 :=
  ⟨by decide, fun t _ h => by simp at h⟩

private theorem xorMaskEntriesOk_set {scr : List (BitVec 32)} {base lim : Nat}
    {mask pat j : BitVec 32} (hm : XorMaskEntriesOk scr base lim mask)
    (hlen : base + 16 ≤ scr.length) (hpat : pat.toNat < 16) (hj : j.toNat < lim) :
    XorMaskEntriesOk (scr.set (base + pat.toNat) j) base lim (mask ||| (1#32 <<< pat)) := by
  have hshl := m7_p3b_shl16_toNat hpat
  have hshl_lt : (1#32 <<< pat).toNat < 2 ^ 16 := by
    rw [hshl]; exact Nat.pow_lt_pow_right (by omega) hpat
  refine ⟨?_, fun t ht hbit => ?_⟩
  · rw [BitVec.toNat_or]
    exact Nat.or_lt_two_pow hm.1 hshl_lt
  · by_cases htp : t = pat.toNat
    · subst htp
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      exact hj
    · rw [List.getElem?_set_ne (by omega)]
      refine hm.2 t ht fun h0 => hbit ?_
      have hmk : mask.getLsbD t = false := by
        have := congrArg (fun x => x.getLsbD t) h0
        simpa [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, show t < 32 by omega] using this
      have hpk : (1#32 <<< pat).getLsbD t = false := by
        change (1#32 <<< pat.toNat).getLsbD t = false
        simp [BitVec.getLsbD_shiftLeft]; intro _ _ _; omega
      apply BitVec.eq_of_getLsbD_eq; intro k
      by_cases hk : k = t
      · rw [hk]; simp [BitVec.getLsbD_and, BitVec.getLsbD_or, hmk]; intro _ _ _; omega
      · simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]; intro _ _; omega

private def XorCollectInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (sz k ci : BitVec 32) (mc : Mem 64) : Prop :=
  ∃ (lmc : List (BitVec 8)) (scrc : List (BitVec 32)),
    ci.toNat ≤ sz.toNat ∧ k.toNat ≤ 4 ∧
    lmc.length = 2 * c.max_vars ∧ scrc.length = c.scratch_cap ∧
    (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
      scrc[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ j < k.toNat, (scrc[1092 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
      ∃ j < k.toNat,
        y = (scrc[1092 + j]?.getD 0#32).toNat ∨
        y = ((scrc[1092 + j]?.getD 0#32) ^^^ 1#32).toNat) ∧
    (FullMem c (m7XorState s lmc scrc) ⋆ R) mc

private def m7XorNegScanExpr (h pScr : Val i64) (nn nl k otgt : Val i32)
    (onDone : Val i32 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32, i32]])
    (fun Js7 =>
      Blocks.cons
        (fun p41 =>
          Expr.let_ ⟨OpCode.ult i32, (Arg.var p41.snd.fst, Arg.var nn, ())⟩ fun p42 =>
          Expr.jnz (Arg.var p42.fst)
            (Expr.let_ ⟨OpCode.ne i32, (Arg.var p41.fst, Arg.var otgt, ())⟩ fun p43 =>
             Expr.jnz (Arg.var p43.fst)
               (Expr.let_ ⟨OpCode.add i32, (Arg.imm 512, Arg.var p41.snd.fst, ())⟩ fun p44 =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p44.fst, ())⟩ fun p45 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var p45.fst, Arg.imm 4, ())⟩ fun p46 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p46.fst, ())⟩ fun p47 =>
                Expr.load i32 (Arg.var p47.fst) fun ld =>
                Expr.group (sig := [[i32]])
                  (fun _JsNext =>
                    Blocks.cons
                      (fun pNext =>
                        Expr.let_ ⟨OpCode.add i32, (Arg.var p41.snd.fst, Arg.imm 1, ())⟩ fun p48 =>
                        Expr.jump Js7.fst (Arg.var pNext.fst, Arg.var p48.fst, ()))
                      Blocks.nil)
                  (fun Js =>
                    Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 2147483648, ())⟩ fun p48 =>
                    Expr.let_ ⟨OpCode.eq i32, (Arg.var p48.fst, Arg.imm 0, ())⟩ fun p49 =>
                    Expr.jnz (Arg.var p49.fst)
                      (Expr.call "full_bve_xor_pat_m7" (as := [i64, i32, i32, i32]) (bs := [i32])
                        (Arg.var h, Arg.var nl, Arg.var ld, Arg.var k, ())
                        fun pat =>
                        Expr.group (sig := [[i32]])
                          (fun _Js8 =>
                            Blocks.cons
                              (fun px => Expr.jump Js.fst (Arg.var px.fst, ()))
                              Blocks.nil)
                          (fun JsJoin =>
                            Expr.let_ ⟨OpCode.ult i32, (Arg.var pat.fst, Arg.imm 16, ())⟩
                              fun p50 =>
                            Expr.jnz (Arg.var p50.fst)
                              (Expr.let_ ⟨OpCode.lshr i32, (Arg.var otgt, Arg.var pat.fst, ())⟩
                                fun p51 =>
                               Expr.let_ ⟨OpCode.and i32, (Arg.var p51.fst, Arg.imm 1, ())⟩
                                 fun p52 =>
                               Expr.let_ ⟨OpCode.ne i32, (Arg.var p52.fst, Arg.imm 0, ())⟩
                                 fun p53 =>
                               Expr.jnz (Arg.var p53.fst)
                                 (Expr.let_ ⟨OpCode.lshr i32,
                                     (Arg.var p41.fst, Arg.var pat.fst, ())⟩ fun p54 =>
                                  Expr.let_ ⟨OpCode.and i32, (Arg.var p54.fst, Arg.imm 1, ())⟩
                                    fun p55 =>
                                  Expr.let_ ⟨OpCode.eq i32, (Arg.var p55.fst, Arg.imm 0, ())⟩
                                    fun p56 =>
                                  Expr.jnz (Arg.var p56.fst)
                                    (Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var pat.fst, ())⟩
                                      fun p57 =>
                                     Expr.let_ ⟨OpCode.or i32,
                                         (Arg.var p41.fst, Arg.var p57.fst, ())⟩ fun p58 =>
                                     Expr.let_ ⟨OpCode.add i32,
                                         (Arg.imm 1076, Arg.var pat.fst, ())⟩ fun q0 =>
                                     Expr.let_ ⟨OpCode.zext 32 64, (Arg.var q0.fst, ())⟩ fun q1 =>
                                     Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩
                                       fun q2 =>
                                     Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var q2.fst, ())⟩
                                       fun q3 =>
                                     Expr.store (Arg.var p41.snd.fst) (Arg.var q3.fst)
                                       (Expr.jump JsJoin.fst (Arg.var p58.fst, ())))
                                    (Expr.jump JsJoin.fst (Arg.var p41.fst, ())))
                                 (Expr.jump JsJoin.fst (Arg.var p41.fst, ())))
                              (Expr.jump JsJoin.fst (Arg.var p41.fst, ()))))
                      (Expr.jump Js.fst (Arg.var p41.fst, ()))))
               (onDone p41.fst))
            (onDone p41.fst))
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm (t := i32) 0, Arg.imm (t := i32) 0, ()))

private theorem m7_p3b_xor_neg_scan_wp (Γ : Env) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (lmc : List (BitVec 8))
    (scrp' : List (BitVec 32)) (R : Mem 64 → Prop)
    (nn nl k_b full_nm : BitVec 32) (mp' : Mem 64) (Q : Post [.bool]) (X : XPost)
    (onDone : Val i32 → Expr Val Cont [.bool])
    (hXorPat : ∀ a m Q X, fullBveXorPatM7Spec a m Q X →
      Γ "full_bve_xor_pat_m7" [i64, i32, i32, i32] [i32] a m Q X)
    (hdw0 : FullDenseInvW c F0 F_cur s)
    (hlmc_len : lmc.length = 2 * c.max_vars)
    (hscrp'_len : scrp'.length = c.scratch_cap)
    (hnn512 : nn.toNat ≤ 512) (hsc1096 : 1096 ≤ c.scratch_cap)
    (hk1 : 1 ≤ k_b.toNat) (hk4 : k_b.toNat ≤ 4)
    (hn_ok : ∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hscr_512 : ∀ j < nn.toNat, scrp'[512 + j]? = s.scratch.scratch_buf[512 + j]?)
    (hmp' : (FullMem c (m7XorState s lmc scrp') ⋆ R) mp')
    (honDone : ∀ (nmask : BitVec 32) (scrn : List (BitVec 32)) (mn : Mem 64),
      scrn.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) → scrn[idx]? = scrp'[idx]?) →
      XorMaskEntriesOk scrn 1076 nn.toNat nmask →
      (FullMem c (m7XorState s lmc scrn) ⋆ R) mn →
      wp Γ Q X (onDone nmask) mn) :
    wp Γ Q X (m7XorNegScanExpr c.hdr c.pScratchBuf nn nl k_b full_nm onDone) mp' := by
  have hlen0 := hdw0.1
  have hw0 := hdw0.2.1
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hscr_len0 := hlen0.scratch_ok.scratch_buf_len
  unfold m7XorNegScanExpr
  refine wp_loop_group (ts := [i32, i32])
    (fun remn (nmask, j2, ()) mn =>
      ∃ scrn : List (BitVec 32),
        j2.toNat ≤ nn.toNat ∧ remn = nn.toNat - j2.toNat ∧ scrn.length = c.scratch_cap ∧
        (∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) → scrn[idx]? = scrp'[idx]?) ∧
        XorMaskEntriesOk scrn 1076 nn.toNat nmask ∧
        (FullMem c (m7XorState s lmc scrn) ⋆ R) mn)
    ?_ ?_
  · rintro Ln remn ⟨nmask, j2, ⟨⟩⟩ mn hLn ⟨scrn, hj2_le, rfl, hscrn_len, hscrn_o, hnm_ok, hmn⟩
    c0_hsplit
    · have hj2_lt : j2.toNat < nn.toNat := hc
      c0_hsplit
      · have hj2_sc : (512#64 + j2.setWidth 64).toNat < scrn.length := by
          rw [hscrn_len]; c0_bound
        let c2j := scrn[(512#64 + j2.setWidth 64).toNat]'hj2_sc
        have hc2j_orig :
            c2j = s.scratch.scratch_buf[512 + j2.toNat]'(by rw [hscr_len0]; omega) := by
          have := (hscrn_o (512 + j2.toNat) (by omega) (Or.inl (by omega))).trans
            (hscr_512 j2.toNat hj2_lt)
          rw [List.getElem?_eq_getElem (by rw [hscrn_len]; omega),
            List.getElem?_eq_getElem (by rw [hscr_len0]; omega)] at this
          exact (m6_getElem_congr (by c0_bound)
            (by rw [hscrn_len]; c0_bound) (by rw [hscrn_len]; omega)).trans
            (Option.some.inj this)
        have hj21 : (j2 + 1#32).toNat = j2.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
          (fun nm' mn' =>
            ∃ scr_k : List (BitVec 32),
              scr_k.length = c.scratch_cap ∧
              (∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) →
                scr_k[idx]? = scrp'[idx]?) ∧
              XorMaskEntriesOk scr_k 1076 nn.toNat nm' ∧
              (FullMem c (m7XorState s lmc scr_k) ⋆ R) mn')
          (fun _ nm' mn' ⟨scr_k, h1, h2, h3, h4⟩ => by
            c0_hsteps!
            exact hLn (nn.toNat - (j2 + 1#32).toNat) (nm', j2 + 1#32, ()) mn' (by omega)
              ⟨scr_k, by omega, rfl, h1, h2, h3, h4⟩)
          (fun Jnm hJnm => by
            c0_hsplit
            · have hc2j_and : c2j &&& 0x80000000#32 = 0#32 := by
                have hidx_eq : (512#64 + j2.setWidth 64).toNat =
                    (BitVec.toNat 512#32 + j2.toNat) % 2 ^ 32 := by c0_bound
                dsimp only [c2j]
                rw [m6_getElem_congr hidx_eq
                  (by rw [hscrn_len]; c0_bound) (by rw [hscrn_len]; omega)]
                exact hc
              have hent_j2 := hn_ok j2.toNat hj2_lt
              rw [List.getElem?_eq_getElem (by rw [hscr_len0]; omega),
                Option.getD_some, ← hc2j_orig] at hent_j2
              unfold FullBveEntryOkW at hent_j2
              rw [ite_eq_right fun h => h hc2j_and] at hent_j2
              have ⟨hlen_n, hw_n⟩ := m7_p3b_lengths_witness_lm_scr hdw0 hlmc_len hscrn_len
              have hc2j_eq (hpf) :
                  scrn[(BitVec.setWidth 64 ((512 : BitVec 32) + j2)).toNat]'hpf = c2j :=
                m6_getElem_congr (by c0_bound) hpf hj2_sc
              c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hXorPat _ _ _ _ ?_)
              refine fullBveXorPatM7Spec_intro rfl hlen_n hw_n
                (by dsimp only [m7XorState, Arg.var]; rw [hc2j_eq _]; exact hent_j2.1)
                (by dsimp only [m7XorState, Arg.var]; rw [hc2j_eq _]; exact hent_j2.2)
                hk1 hk4 hmn ?_
              intro pat hpat
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
                (fun nm' mn' =>
                  ∃ scr_k : List (BitVec 32),
                    scr_k.length = c.scratch_cap ∧
                    (∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) →
                      scr_k[idx]? = scrp'[idx]?) ∧
                    XorMaskEntriesOk scr_k 1076 nn.toNat nm' ∧
                    (FullMem c (m7XorState s lmc scr_k) ⋆ R) mn')
                (fun _ nm' mn' ⟨scr_k, h1, h2, h3, h4⟩ => by
                  c0_hsteps!
                  exact hJnm nm' mn' ⟨scr_k, h1, h2, h3, h4⟩)
                (fun Jp2 hJp2 => by
                  c0_hsplit
                  · have hpat_lt : pat.toNat < 16 := hc
                    c0_hsplit
                    · c0_hsplit
                      · have hst : (1076#64 + pat.setWidth 64).toNat < scrn.length := by
                          rw [hscrn_len]; c0_bound
                        have hnm_s := xorMaskEntriesOk_set hnm_ok (by omega) hpat_lt hj2_lt
                        have hscr_o_s : ∀ idx < c.scratch_cap, (idx < 1076 ∨ 1092 ≤ idx) →
                            (scrn.set (1076 + pat.toNat) j2)[idx]? = scrp'[idx]? :=
                          fun idx hi hor => by
                            rw [List.getElem?_set_ne (by omega)]
                            exact hscrn_o idx hi hor
                        c0_hsteps!
                        dsimp only [m7XorState] at hm ⊢
                        rw [show scrn.set _ j2 = scrn.set (1076 + pat.toNat) j2 from
                          congrArg (fun k => scrn.set k j2) (by c0_bound)] at hm
                        have hsh : (1 : BitVec 32) <<< (pat.toNat % 32) = 1#32 <<< pat := by
                          change 1#32 <<< (pat.toNat % 32) = 1#32 <<< pat.toNat
                          rw [Nat.mod_eq_of_lt (by omega)]
                        rw [hsh]
                        exact hJp2 (nmask ||| (1#32 <<< pat)) _
                          ⟨scrn.set (1076 + pat.toNat) j2,
                            by rw [List.length_set, hscrn_len], hscr_o_s, hnm_s, hm⟩
                      · c0_hsteps!; exact hJp2 nmask mn ⟨scrn, hscrn_len, hscrn_o, hnm_ok, hmn⟩
                    · c0_hsteps!; exact hJp2 nmask mn ⟨scrn, hscrn_len, hscrn_o, hnm_ok, hmn⟩
                  · c0_hsteps!; exact hJp2 nmask mn ⟨scrn, hscrn_len, hscrn_o, hnm_ok, hmn⟩)
            · c0_hsteps!; exact hJnm nmask mn ⟨scrn, hscrn_len, hscrn_o, hnm_ok, hmn⟩)
      · c0_hsteps!; dsimp only; exact honDone nmask scrn mn hscrn_len hscrn_o hnm_ok hmn
    · c0_hsteps!; dsimp only; exact honDone nmask scrn mn hscrn_len hscrn_o hnm_ok hmn
  · intro Ln hLn; c0_hsteps!
    exact hLn nn.toNat (0#32, 0#32, ()) mp'
      ⟨scrp', Nat.zero_le _, by simp, hscrp'_len, fun _ _ _ => rfl,
        xorMaskEntriesOk_zero _ _ _, hmp'⟩

/-- WP proof for `full_bve_find_xor_m7`: faithful Kissat `find_xor_gate` (XOR parity gate
extraction over `lm` / `scr[1060..1096]`, calling `full_bve_xor_pat_m7`). -/
theorem full_bve_find_xor_m7_wp (Γ : Env)
    (hXorPat : ∀ a m Q X, fullBveXorPatM7Spec a m Q X →
      Γ "full_bve_xor_pat_m7" [i64, i32, i32, i32] [i32] a m Q X) :
    ∀ a m0 Q X, fullBveFindXorM7Spec a m0 Q X →
      Func.wp Γ full_bve_find_xor_m7_body a m0 Q X := by
  intro a m0 Q X hSpec
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩
  obtain ⟨c, F0, F_cur, s, R, rfl, hdw0, hsc1088, hv_lt, hnp512, hnn512,
    hp_ok, hn_ok, hm0, hQ⟩ := fullBveFindXorM7Spec_elim hSpec
  have hlen0 := hdw0.1
  have hw0 := hdw0.2.1
  have hlm0_clr := hdw0.2.2.1
  have hl0 := hdw0.2.2.2.2.2.1
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_lt := c.hscr; unfold dimacsBound at hscr_lt
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hscr_len0 := hlen0.scratch_ok.scratch_buf_len
  have har_len0 := hlen0.core_ok.arena_len_arr
  have hval_len0 := hlen0.core_ok.vals_len
  have hlm_len0 := hlen0.core_ok.lit_mark_len
  unfold Func.wp full_bve_find_xor_m7_body
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0 (fun _ _ _ => rfl) hm0
  · have hsc1096 : 1096 ≤ c.scratch_cap := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc
      change ¬c.scratch_cap < 1096 at hc; omega
    c0_hsteps_nogrp
    refine wp_loop_group (ts := [i32, i32])
      (fun rem (lp, i, ()) mi => mi = m0 ∧ i.toNat ≤ np.toNat ∧ rem = np.toNat - i.toNat)
      ?_ ?_
    · rintro L rem ⟨lp, i, ⟨⟩⟩ mi hL ⟨hm_eq, hi_le, rfl⟩
      subst mi
      c0_hsplit
      · have hi_lt : i.toNat < np.toNat := hc
        have hi_sc : (i.setWidth 64).toNat < s.scratch.scratch_buf.length := by
          rw [hscr_len0, m6_zext32_toNat]; omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun x => (x, ())) (fun _ => True)
          (fun _ lp' _ => by
            c0_hsteps!
            exact hL (np.toNat - (i + 1#32).toNat) (lp', i + 1#32, ()) m0 (by omega)
              ⟨rfl, by omega, rfl⟩)
          (fun J hJ => by
            c0_hsplit
            · c0_hsteps!; exact hJ (lp + 1#32) trivial
            · c0_hsteps!; exact hJ lp trivial)
      · c0_hsteps_nogrp
        refine wp_loop_group (ts := [i32, i32])
          (fun rem2 (ln, j, ()) mj => mj = m0 ∧ j.toNat ≤ nn.toNat ∧ rem2 = nn.toNat - j.toNat)
          ?_ ?_
        · rintro L2 rem2 ⟨ln, j, ⟨⟩⟩ mj hL2 ⟨hm_eq2, hj_le, rfl⟩
          subst mj
          c0_hsplit
          · have hj_lt : j.toNat < nn.toNat := hc
            have hj_sc : (512#64 + j.setWidth 64).toNat < s.scratch.scratch_buf.length := by
              rw [hscr_len0]; c0_bound
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
              (fun x => (x, ())) (fun _ => True)
              (fun _ ln' _ => by
                c0_hsteps!
                exact hL2 (nn.toNat - (j + 1#32).toNat) (ln', j + 1#32, ()) m0 (by omega)
                  ⟨rfl, by omega, rfl⟩)
              (fun J2 hJ2 => by
                c0_hsplit
                · c0_hsteps!; exact hJ2 (ln + 1#32) trivial
                · c0_hsteps!; exact hJ2 ln trivial)
          · c0_hsplit
            · c0_hsteps!
              exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0
                (fun _ _ _ => rfl) hm0
            · c0_hsplit
              · c0_hsteps!
                exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0
                  (fun _ _ _ => rfl) hm0
              · c0_hsplit
                · c0_hsteps!
                  exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0
                    (fun _ _ _ => rfl) hm0
                · have ⟨hpl_val, hnl_val⟩ := m7_p3b_pl_nl_eq (v := v) (by omega)
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i32])
                    (fun rem3 (i, ()) mi =>
                      ∃ (lmi : List (BitVec 8)) (scri : List (BitVec 32)),
                        lmi.length = 2 * c.max_vars ∧
                        (∀ y < lmi.length, lmi[y]?.getD 0#8 = 0#8) ∧
                        scri.length = c.scratch_cap ∧
                        (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                          scri[idx]? = s.scratch.scratch_buf[idx]?) ∧
                        i.toNat ≤ np.toNat ∧ rem3 = np.toNat - i.toNat ∧
                        (FullMem c (m7XorState s lmi scri) ⋆ R) mi)
                    ?_ ?_
                  · rintro L3 rem3 ⟨i, ⟨⟩⟩ mi hL3 ⟨lmi, scri, hlmi_len, hlmi_z, hscri_len,
                      hscri_out, hi_le, rfl, hmi⟩
                    have hdw_i := m7_p3b_fullDenseInvW_lm_scr hdw0 hlmi_len
                      (fun l hl => hlmi_z l (by rw [hlmi_len]; exact hl)) hscri_len
                    c0_hsplit
                    · have hi_lt : i.toNat < np.toNat := hc
                      have hi_sc : (i.setWidth 64).toNat < scri.length := by
                        rw [hscri_len, m6_zext32_toNat]; omega
                      let cr := scri[(i.setWidth 64).toNat]'hi_sc
                      have hcr_orig : cr = s.scratch.scratch_buf[i.toNat]'(by
                          rw [hscr_len0]; omega) := by
                        have := hscri_out i.toNat (by omega) (Or.inl (by omega))
                        rw [List.getElem?_eq_getElem (by rw [hscri_len]; omega),
                          List.getElem?_eq_getElem (by rw [hscr_len0]; omega)] at this
                        have hcr_eq := m6_getElem_congr (m6_zext32_toNat i)
                          (by rw [hscri_len, m6_zext32_toNat]; omega) (by rw [hscri_len]; omega)
                        exact hcr_eq.trans (Option.some.inj this)
                      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
                      c0_hsteps_nogrp
                      refine wp_join0
                        (P := fun mn =>
                          ∃ (lmn : List (BitVec 8)) (scrn : List (BitVec 32)),
                            lmn.length = 2 * c.max_vars ∧
                            (∀ y < lmn.length, lmn[y]?.getD 0#8 = 0#8) ∧
                            scrn.length = c.scratch_cap ∧
                            (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                              scrn[idx]? = s.scratch.scratch_buf[idx]?) ∧
                            (FullMem c (m7XorState s lmn scrn) ⋆ R) mn)
                        (fun _ mn ⟨lmn, scrn, hlmn_len, hlmn_z, hscrn_len, hscrn_out, hmn⟩ => by
                          c0_hsteps!
                          exact hL3 (np.toNat - (i + 1#32).toNat) (i + 1#32, ()) mn (by omega)
                            ⟨lmn, scrn, hlmn_len, hlmn_z, hscrn_len, hscrn_out,
                              by omega, rfl, hmn⟩)
                        (fun J34 hJ34 => by
                          c0_hsplit
                          · have hcr_and : cr &&& 0x80000000#32 = 0#32 := by
                              dsimp only [cr]
                              rw [m6_getElem_congr (m6_zext32_toNat i)
                                (by rw [hscri_len, m6_zext32_toNat]; omega)
                                (by rw [hscri_len]; omega)]
                              exact hc
                            have hent_i := hp_ok i.toNat hi_lt
                            rw [List.getElem?_eq_getElem (by rw [hscr_len0]; omega),
                              Option.getD_some, ← hcr_orig] at hent_i
                            unfold FullBveEntryOkW at hent_i
                            rw [ite_eq_right fun h => h hcr_and] at hent_i
                            obtain ⟨href_cr, hng_cr⟩ := hent_i
                            have harena_lt := c.harena; unfold dimacsBound at harena_lt
                            have hal_le := hlen0.core_ok.arena_len_le
                            have hwf_cr := hw0.arena.refs_wf cr.toNat href_cr
                            have hcr_bd := hwf_cr.1
                            have hsz_ge3 := hwf_cr.2.1
                            have hcr3_bd :
                                cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                                  s.core.arena_len := by
                              have h1 := hwf_cr.2.2.1; have h2 := hwf_cr.2.2.2.1; omega
                            have har_len_cr2 : (cr.setWidth 64 + 2#64).toNat <
                                s.core.arena.length := by
                              rw [har_len0]; c0_bound
                            let sz := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'har_len_cr2
                            have hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                              unfold sz fullArenaClauseSizeCore
                              rw [List.getElem?_eq_getElem (by rw [har_len0]; omega),
                                Option.getD_some]
                              exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                            c0_hsteps_nogrp
                            refine wp_while_break_state
                              (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
                              (β := Bool × BitVec 32 × BitVec 32)
                              (fun x => (x.1, x.2.1, x.2.2, ()))
                              (fun (ok_b, k_b, ci_b) mb =>
                                XorCollectInv c s R sz k_b ci_b mb)
                              (α := BitVec 32 × BitVec 32)
                              (fun p => (p.1, p.2, ()))
                              (fun p => sz.toNat - p.2.toNat)
                              (fun (k_c, ci_c) mc =>
                                XorCollectInv c s R sz k_c ci_c mc)
                              ?_ ?_ ?_
                            · rintro B42 ⟨ok_b, k_b, ci_b⟩ mb
                                ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len, hscrc_out,
                                  h1092_bd, hnz_c, hmb⟩
                              c0_hsteps_nogrp
                              refine wp_join0
                                (P := fun mf =>
                                  ∃ (lmf : List (BitVec 8)) (scrf : List (BitVec 32)),
                                    lmf.length = 2 * c.max_vars ∧
                                    (∀ y < lmf.length, lmf[y]?.getD 0#8 = 0#8) ∧
                                    scrf.length = c.scratch_cap ∧
                                    (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                                      scrf[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                    (FullMem c (m7XorState s lmf scrf) ⋆ R) mf)
                                (fun _ mf ⟨lmf, scrf, h1, h2, h3, h4, hm⟩ => by
                                  c0_hsteps!; exact hJ34 mf ⟨lmf, scrf, h1, h2, h3, h4, hm⟩)
                                (fun J46 hJ46 => by
                                  c0_hsteps_nogrp
                                  refine wp_join0
                                    (P := fun mc' =>
                                      ∃ (lmc' : List (BitVec 8)) (scrc' : List (BitVec 32)),
                                        lmc'.length = 2 * c.max_vars ∧
                                        k_b.toNat ≤ 4 ∧ scrc'.length = c.scratch_cap ∧
                                        (∀ idx < c.scratch_cap, (idx < 1024 ∨ 1096 ≤ idx) →
                                          scrc'[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                        (∀ j < k_b.toNat,
                                          (scrc'[1092 + j]?.getD 0#32).toNat <
                                            2 * s.core.cur_vars) ∧
                                        (∀ y < lmc'.length, lmc'[y]?.getD 0#8 ≠ 0#8 →
                                          ∃ j < k_b.toNat,
                                            y = (scrc'[1092 + j]?.getD 0#32).toNat ∨
                                            y = ((scrc'[1092 + j]?.getD 0#32) ^^^
                                              1#32).toNat) ∧
                                        (FullMem c (m7XorState s lmc' scrc') ⋆ R) mc')
                                    (fun _ mc' ⟨lmc', scrc', hlmc', hk', hscrc', hscrc_o',
                                        hbd', hnz', hmc'⟩ =>
                                      m7_p3b_xor_clean_lm_wp Γ c s lmc' scrc' R k_b mc' Q X _
                                        hlmc' hscrc' hsc1096 hk' hcv_le hbd'
                                        (fun y hy => hnz' y (by rw [hlmc']; exact hy)) hmc'
                                        (fun lm_cl hlm_cl_len hlm_cl_z m_cl hm_cl => by
                                          c0_hsteps!
                                          exact hJ46 m_cl ⟨lm_cl, scrc', hlm_cl_len,
                                            fun y hy => hlm_cl_z y (hlm_cl_len ▸ hy),
                                            hscrc', hscrc_o', hm_cl⟩))
                                    (fun J47 hJ47 => by
                                      c0_hsplit
                                      · c0_hsplit
                                        · have hk2 : 2 ≤ k_b.toNat := hc
                                          have hk4 : k_b.toNat ≤ 4 := hk_le
                                          c0_hsteps_nogrp
                                          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                                            (fun x => (x, ()))
                                            (fun full_pm => full_pm =
                                              if k_b = 2#32 then 9#32
                                              else if k_b = 3#32 then 105#32 else 38505#32)
                                            (fun _ full_pm hfp => ?_)
                                            (fun Jfp hJfp => by
                                              c0_hsplit
                                              · c0_hsteps!; exact hJfp 9#32 (by simp [hc])
                                              · have hk2_ne : k_b ≠ 2#32 := hc
                                                c0_hsteps_nogrp
                                                refine wp_join_state_pure (ts := [i32])
                                                  (α := BitVec 32) (fun x => (x, ()))
                                                  (fun x => x =
                                                    if k_b = 3#32 then 105#32 else 38505#32)
                                                  (fun _ x hx => by
                                                    c0_hsteps!
                                                    exact hJfp x (by simp [hk2_ne, hx]))
                                                  (fun Jfp2 hJfp2 => by
                                                    c0_hsplit
                                                    · c0_hsteps!; exact hJfp2 105#32 (by simp [hc])
                                                    · c0_hsteps!
                                                      exact hJfp2 38505#32
                                                        (by simp [show k_b ≠ 3#32 from hc])))
                                          c0_hsteps_nogrp
                                          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                                            (fun x => (x, ()))
                                            (fun full_nm => full_nm =
                                              if k_b = 2#32 then 6#32
                                              else if k_b = 3#32 then 150#32 else 27030#32)
                                            (fun _ full_nm hfn => ?_)
                                            (fun Jfn hJfn => by
                                              c0_hsplit
                                              · c0_hsteps!; exact hJfn 6#32 (by simp [hc])
                                              · have hk2_ne : k_b ≠ 2#32 := hc
                                                c0_hsteps_nogrp
                                                refine wp_join_state_pure (ts := [i32])
                                                  (α := BitVec 32) (fun x => (x, ()))
                                                  (fun x => x =
                                                    if k_b = 3#32 then 150#32 else 27030#32)
                                                  (fun _ x hx => by
                                                    c0_hsteps!
                                                    exact hJfn x (by simp [hk2_ne, hx]))
                                                  (fun Jfn2 hJfn2 => by
                                                    c0_hsplit
                                                    · c0_hsteps!; exact hJfn2 150#32 (by simp [hc])
                                                    · c0_hsteps!
                                                      exact hJfn2 27030#32
                                                        (by simp [show k_b ≠ 3#32 from hc])))
                                          have h1060 :
                                              (1060#64 : BitVec 64).toNat < scrc.length := by
                                            rw [hscrc_len]; c0_bound
                                          c0_hsteps_nogrp
                                          refine wp_loop_group (ts := [i32, i32])
                                            (fun remp (pmask, j, ()) mp =>
                                              ∃ scrp : List (BitVec 32),
                                                j.toNat ≤ np.toNat ∧ remp = np.toNat - j.toNat ∧
                                                scrp.length = c.scratch_cap ∧
                                                (∀ idx < c.scratch_cap,
                                                  (idx < 1060 ∨ 1076 ≤ idx) →
                                                    scrp[idx]? = scrc[idx]?) ∧
                                                XorMaskEntriesOk scrp 1060 np.toNat pmask ∧
                                                (FullMem c (m7XorState s lmc scrp) ⋆ R) mp)
                                            ?_ ?_
                                          · rintro Lp remp ⟨pmask, j, ⟨⟩⟩ mp hLp
                                              ⟨scrp, hj_le, rfl, hscrp_len, hscrp_o, hpm_ok, hmp⟩
                                            have h1092_p : ∀ j < k_b.toNat,
                                                (scrp[1092 + j]?.getD 0#32).toNat <
                                                  2 * s.core.cur_vars := fun j hj => by
                                              rw [hscrp_o (1092 + j) (by omega) (Or.inr (by omega))]
                                              exact h1092_bd j hj
                                            have hnz_p :
                                                ∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
                                                ∃ j < k_b.toNat,
                                                  y = (scrp[1092 + j]?.getD 0#32).toNat ∨
                                                  y = ((scrp[1092 + j]?.getD 0#32) ^^^
                                                    1#32).toNat :=
                                              fun y hy hyn => by
                                                obtain ⟨jj, hjj, hyeq⟩ := hnz_c y hy hyn
                                                refine ⟨jj, hjj, ?_⟩
                                                rwa [hscrp_o (1092 + jj) (by omega)
                                                  (Or.inr (by omega))]
                                            have hscrp_out : ∀ idx < c.scratch_cap,
                                                (idx < 1024 ∨ 1096 ≤ idx) →
                                                scrp[idx]? = s.scratch.scratch_buf[idx]? :=
                                              fun idx hi hor =>
                                                (hscrp_o idx hi (by
                                                  rcases hor with h | h
                                                  · exact Or.inl (by omega)
                                                  · exact Or.inr (by omega))).trans
                                                  (hscrc_out idx hi hor)
                                            c0_hsteps_nogrp
                                            refine wp_join0
                                              (P := fun mp' =>
                                                ∃ scrp' : List (BitVec 32),
                                                  scrp'.length = c.scratch_cap ∧
                                                  (∀ idx < c.scratch_cap,
                                                    (idx < 1060 ∨ 1076 ≤ idx) →
                                                      scrp'[idx]? = scrc[idx]?) ∧
                                                  XorMaskEntriesOk scrp' 1060 np.toNat pmask ∧
                                                  (FullMem c (m7XorState s lmc scrp') ⋆ R) mp')
                                              (fun _ mp' ⟨scrp', hscrp'_len, hscrp'_o, hpm_ok',
                                                  hmp'⟩ => by
                                                have h1092_p' : ∀ j < k_b.toNat,
                                                    (scrp'[1092 + j]?.getD 0#32).toNat <
                                                      2 * s.core.cur_vars := fun j hj => by
                                                  rw [hscrp'_o (1092 + j) (by omega)
                                                    (Or.inr (by omega))]
                                                  exact h1092_bd j hj
                                                have hnz_p' :
                                                    ∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
                                                    ∃ j < k_b.toNat,
                                                      y = (scrp'[1092 + j]?.getD 0#32).toNat ∨
                                                      y = ((scrp'[1092 + j]?.getD 0#32) ^^^
                                                        1#32).toNat :=
                                                  fun y hy hyn => by
                                                    obtain ⟨jj, hjj, hyeq⟩ := hnz_c y hy hyn
                                                    refine ⟨jj, hjj, ?_⟩
                                                    rwa [hscrp'_o (1092 + jj) (by omega)
                                                      (Or.inr (by omega))]
                                                have hscrp'_out : ∀ idx < c.scratch_cap,
                                                    (idx < 1024 ∨ 1096 ≤ idx) →
                                                    scrp'[idx]? = s.scratch.scratch_buf[idx]? :=
                                                  fun idx hi hor =>
                                                    (hscrp'_o idx hi (by
                                                      rcases hor with h | h
                                                      · exact Or.inl (by omega)
                                                      · exact Or.inr (by omega))).trans
                                                      (hscrc_out idx hi hor)
                                                c0_hsteps_nogrp
                                                refine wp_join_state (ts := [i32])
                                                  (α := BitVec 32) (fun x => (x, ()))
                                                  (fun nmask' mv =>
                                                    ∃ scr_v : List (BitVec 32),
                                                      scr_v.length = c.scratch_cap ∧
                                                      (∀ idx < c.scratch_cap,
                                                        (idx < 1024 ∨ 1096 ≤ idx) →
                                                        scr_v[idx]? =
                                                          s.scratch.scratch_buf[idx]?) ∧
                                                      (∀ j < k_b.toNat,
                                                        (scr_v[1092 + j]?.getD 0#32).toNat <
                                                          2 * s.core.cur_vars) ∧
                                                      (∀ y < lmc.length, lmc[y]?.getD 0#8 ≠ 0#8 →
                                                        ∃ j < k_b.toNat,
                                                          y = (scr_v[1092 + j]?.getD 0#32).toNat ∨
                                                          y = ((scr_v[1092 + j]?.getD 0#32) ^^^
                                                            1#32).toNat) ∧
                                                      (∀ t < 16,
                                                        (pmask &&& (1#32 <<< t)) ≠ 0#32 →
                                                        (scr_v[1060 + t]?.getD 0#32).toNat <
                                                          np.toNat) ∧
                                                      XorMaskEntriesOk scr_v 1076 nn.toNat nmask' ∧
                                                      (FullMem c (m7XorState s lmc scr_v) ⋆ R) mv)
                                                  (fun _ nmask' mv ⟨scr_v, hscrv_len, hscrv_out,
                                                      h1092_v, hnz_v, hpm_bd_v, hnm_ok_v, hmv⟩ =>
                                                    m7_p3b_xor_clean_lm_wp Γ c s lmc scr_v R k_b
                                                      mv Q X _ hlmc_len hscrv_len hsc1096 hk_le
                                                      hcv_le h1092_v
                                                      (fun y hy =>
                                                        hnz_v y (by rw [hlmc_len]; exact hy))
                                                      hmv
                                                      (fun lm_cl hlm_cl_len hlm_cl_z m_cl hm_cl =>
                                                        by
                                                        c0_hsplit
                                                        · have hpm_f : pmask = full_pm := hc
                                                          c0_hsplit
                                                          · have hnm_f : nmask' = full_nm := hc
                                                            let s_cl : FullState :=
                                                              { s with
                                                                core :=
                                                                  { s.core with
                                                                    lit_mark := lm_cl } }
                                                            dsimp only
                                                            refine m7_p3b_xor_commit_wp Γ c s_cl
                                                              scr_v R k_b full_pm full_nm m_cl Q X
                                                              hscrv_len hscrv_out hsc1096
                                                              (by omega) hk4
                                                              (fun b hb hbit => lt_of_lt_of_le
                                                                (hpm_bd_v b hb
                                                                  (by rw [hpm_f]; exact hbit))
                                                                hnp512)
                                                              (fun b hb hbit => lt_of_lt_of_le
                                                                (hnm_ok_v.2 b hb
                                                                  (by rw [hnm_f]; exact hbit))
                                                                hnn512)
                                                              hm_cl
                                                              (fun ok scr' m' hsc' hout' hm' =>
                                                                hQ ok lm_cl scr' m'
                                                                  (m7_p3b_fullDenseInvW_lm_scr
                                                                    hdw0 hlm_cl_len hlm_cl_z hsc')
                                                                  hsc' hout' hm')
                                                          · c0_hsteps!
                                                            exact hJ46 m_cl ⟨lm_cl, scr_v,
                                                              hlm_cl_len,
                                                              fun y hy =>
                                                                hlm_cl_z y (hlm_cl_len ▸ hy),
                                                              hscrv_len, hscrv_out, hm_cl⟩
                                                        · c0_hsteps!
                                                          exact hJ46 m_cl ⟨lm_cl, scr_v,
                                                            hlm_cl_len,
                                                            fun y hy =>
                                                              hlm_cl_z y (hlm_cl_len ▸ hy),
                                                            hscrv_len, hscrv_out, hm_cl⟩))
                                                  (fun J60 hJ60 => by
                                                    c0_hsplit
                                                    · c0_hsteps_nogrp
                                                      refine m7_p3b_xor_neg_scan_wp Γ c F0 F_cur s
                                                        lmc scrp' R nn ((v <<< 1#32) ||| 1#32) k_b
                                                        full_nm mp' Q X
                                                        (fun x => Expr.jump J60 (Arg.var x, ()))
                                                        hXorPat hdw0 hlmc_len hscrp'_len hnn512
                                                        hsc1096 (by omega) hk4
                                                        (fun j hj => by
                                                          change FullBveEntryOkW F_cur s
                                                            ((v <<< (1 : Nat)) ||| 1#32).toNat _
                                                          rw [hnl_val]; exact hn_ok j hj)
                                                        (fun j hj => hscrp'_out (512 + j)
                                                          (by omega) (Or.inl (by omega)))
                                                        hmp'
                                                        (fun nmask scrn mn hscrn_len hscrn_o
                                                            hnm_ok hmn => by
                                                          have h1092_n : ∀ j < k_b.toNat,
                                                              (scrn[1092 + j]?.getD 0#32).toNat <
                                                                2 * s.core.cur_vars :=
                                                            fun j hj => by
                                                            rw [hscrn_o (1092 + j) (by omega)
                                                              (Or.inr (by omega))]
                                                            exact h1092_p' j hj
                                                          have hnz_n : ∀ y < lmc.length,
                                                              lmc[y]?.getD 0#8 ≠ 0#8 →
                                                              ∃ j < k_b.toNat,
                                                                y = (scrn[1092 + j]?.getD
                                                                  0#32).toNat ∨
                                                                y = ((scrn[1092 + j]?.getD 0#32) ^^^
                                                                  1#32).toNat := fun y hy hyn => by
                                                            obtain ⟨jj, hjj, hyeq⟩ :=
                                                              hnz_p' y hy hyn
                                                            refine ⟨jj, hjj, ?_⟩
                                                            rwa [hscrn_o (1092 + jj) (by omega)
                                                              (Or.inr (by omega))]
                                                          have hscrn_out : ∀ idx < c.scratch_cap,
                                                              (idx < 1024 ∨ 1096 ≤ idx) →
                                                              scrn[idx]? =
                                                                s.scratch.scratch_buf[idx]? :=
                                                            fun idx hi hor =>
                                                              (hscrn_o idx hi (by
                                                                rcases hor with h | h
                                                                · exact Or.inl (by omega)
                                                                · exact Or.inr (by omega))).trans
                                                                (hscrp'_out idx hi hor)
                                                          have hpm_bd_n : ∀ t < 16,
                                                              (pmask &&& (1#32 <<< t)) ≠ 0#32 →
                                                              (scrn[1060 + t]?.getD 0#32).toNat <
                                                                np.toNat := fun t ht hb => by
                                                            rw [hscrn_o (1060 + t) (by omega)
                                                              (Or.inl (by omega))]
                                                            exact hpm_ok'.2 t ht hb
                                                          c0_hsteps!
                                                          exact hJ60 nmask mn ⟨scrn, hscrn_len,
                                                            hscrn_out, h1092_n, hnz_n, hpm_bd_n,
                                                            hnm_ok, hmn⟩)
                                                    · c0_hsteps!
                                                      exact hJ60 0#32 mp'
                                                        ⟨scrp', hscrp'_len, hscrp'_out, h1092_p',
                                                          hnz_p', hpm_ok'.2,
                                                          xorMaskEntriesOk_zero _ _ _, hmp'⟩))
                                              (fun Jex1 hJex1 => by
                                                c0_hsplit
                                                · have hj_lt : j.toNat < np.toNat := hc
                                                  c0_hsplit
                                                  · have hj_sc :
                                                        (j.setWidth 64).toNat < scrp.length := by
                                                      rw [hscrp_len, m6_zext32_toNat]; omega
                                                    let cj := scrp[(j.setWidth 64).toNat]'hj_sc
                                                    have hcj_orig :
                                                        cj = s.scratch.scratch_buf[j.toNat]'(by
                                                          rw [hscr_len0]; omega) := by
                                                      have := hscrp_out j.toNat (by omega)
                                                        (Or.inl (by omega))
                                                      rw [List.getElem?_eq_getElem
                                                          (by rw [hscrp_len]; omega),
                                                        List.getElem?_eq_getElem
                                                          (by rw [hscr_len0]; omega)] at this
                                                      exact (m6_getElem_congr (m6_zext32_toNat j)
                                                        (by rw [hscrp_len, m6_zext32_toNat]; omega)
                                                        (by rw [hscrp_len]; omega)).trans
                                                        (Option.some.inj this)
                                                    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
                                                      c0_bound
                                                    c0_hsteps_nogrp
                                                    refine wp_join_state (ts := [i32])
                                                      (α := BitVec 32) (fun x => (x, ()))
                                                      (fun pm' mp' =>
                                                        ∃ scr_k : List (BitVec 32),
                                                          scr_k.length = c.scratch_cap ∧
                                                          (∀ idx < c.scratch_cap,
                                                            (idx < 1060 ∨ 1076 ≤ idx) →
                                                              scr_k[idx]? = scrc[idx]?) ∧
                                                          XorMaskEntriesOk scr_k 1060 np.toNat pm' ∧
                                                          (FullMem c (m7XorState s lmc scr_k) ⋆ R)
                                                            mp')
                                                      (fun _ pm' mp' ⟨scr_k, h1, h2, h3, h4⟩ => by
                                                        c0_hsteps!
                                                        exact hLp (np.toNat - (j + 1#32).toNat)
                                                          (pm', j + 1#32, ()) mp' (by omega)
                                                          ⟨scr_k, by omega, rfl, h1, h2, h3, h4⟩)
                                                      (fun Jpm hJpm => by
                                                        c0_hsplit
                                                        rotate_left
                                                        · c0_hsteps!
                                                          exact hJpm pmask mp
                                                            ⟨scrp, hscrp_len, hscrp_o, hpm_ok,
                                                              hmp⟩
                                                        c0_hsplit
                                                        rotate_left
                                                        · c0_hsteps!
                                                          exact hJpm pmask mp
                                                            ⟨scrp, hscrp_len, hscrp_o, hpm_ok,
                                                              hmp⟩
                                                        have hcj_and :
                                                            cj &&& 0x80000000#32 = 0#32 := (by
                                                          dsimp only [cj]
                                                          rw [m6_getElem_congr
                                                            (m6_zext32_toNat j)
                                                            (by
                                                              rw [hscrp_len, m6_zext32_toNat]
                                                              omega)
                                                            (by rw [hscrp_len]; omega)]
                                                          exact hc)
                                                        have hent_j := hp_ok j.toNat hj_lt
                                                        rw [List.getElem?_eq_getElem
                                                          (by rw [hscr_len0]; omega),
                                                          Option.getD_some, ← hcj_orig] at hent_j
                                                        unfold FullBveEntryOkW at hent_j
                                                        rw [ite_eq_right fun h => h hcj_and]
                                                          at hent_j
                                                        have ⟨hlen_p, hw_p⟩ :=
                                                          m7_p3b_lengths_witness_lm_scr
                                                            hdw0 hlmc_len hscrp_len
                                                        have hk1 : 1 ≤ k_b.toNat := by omega
                                                        c0_hsteps_nogrp
                                                        refine wp_call_of_spec _ _
                                                          (hXorPat _ _ _ _ ?_)
                                                        refine fullBveXorPatM7Spec_intro
                                                          rfl hlen_p
                                                          hw_p hent_j.1 hent_j.2 hk1 hk4
                                                          hmp ?_
                                                        intro pat hpat
                                                        c0_hsteps_nogrp
                                                        refine wp_join_state (ts := [i32])
                                                          (α := BitVec 32) (fun x => (x, ()))
                                                          (fun pm' mp' =>
                                                            ∃ scr_k : List (BitVec 32),
                                                              scr_k.length = c.scratch_cap ∧
                                                              (∀ idx < c.scratch_cap,
                                                                (idx < 1060 ∨ 1076 ≤ idx) →
                                                                  scr_k[idx]? = scrc[idx]?) ∧
                                                              XorMaskEntriesOk scr_k 1060 np.toNat
                                                                pm' ∧
                                                              (FullMem c
                                                                (m7XorState s lmc scr_k) ⋆ R) mp')
                                                          (fun _ pm' mp' ⟨scr_k, h1, h2, h3,
                                                              h4⟩ => by
                                                            c0_hsteps!
                                                            exact hJpm pm' mp'
                                                              ⟨scr_k, h1, h2, h3, h4⟩)
                                                          (fun Jp1 hJp1 => by
                                                            c0_hsplit
                                                            · have hpat_lt : pat.toNat < 16 := hc
                                                              c0_hsplit
                                                              · c0_hsplit
                                                                · have hst :
                                                                      (1060#64 +
                                                                        pat.setWidth 64).toNat <
                                                                        scrp.length := by
                                                                    rw [hscrp_len]; c0_bound
                                                                  have hpm_s :=
                                                                    xorMaskEntriesOk_set hpm_ok
                                                                      (by rw [hscrp_len]; omega)
                                                                      hpat_lt hj_lt
                                                                  have hscr_o_s :
                                                                      ∀ idx < c.scratch_cap,
                                                                      (idx < 1060 ∨ 1076 ≤ idx) →
                                                                      (scrp.set
                                                                        (1060 + pat.toNat)
                                                                        j)[idx]? = scrc[idx]? :=
                                                                    fun idx hi hor => by
                                                                      rw [List.getElem?_set_ne
                                                                        (by omega)]
                                                                      exact hscrp_o idx hi hor
                                                                  c0_hsteps!
                                                                  dsimp only [m7XorState] at hm ⊢
                                                                  rw [show scrp.set _ j =
                                                                      scrp.set (1060 + pat.toNat)
                                                                        j from
                                                                      congrArg
                                                                        (fun k => scrp.set k j)
                                                                        (by c0_bound)] at hm
                                                                  have hsh :
                                                                      (1 : BitVec 32) <<<
                                                                        (pat.toNat % 32) =
                                                                      1#32 <<< pat := by
                                                                    change 1#32 <<<
                                                                        (pat.toNat % 32) =
                                                                      1#32 <<< pat.toNat
                                                                    rw [Nat.mod_eq_of_lt
                                                                      (by omega)]
                                                                  rw [hsh]
                                                                  exact hJp1
                                                                    (pmask ||| (1#32 <<< pat)) _
                                                                    ⟨scrp.set (1060 + pat.toNat)
                                                                      j,
                                                                      by rw [List.length_set,
                                                                        hscrp_len],
                                                                      hscr_o_s, hpm_s, hm⟩
                                                                · c0_hsteps!
                                                                  exact hJp1 pmask mp
                                                                    ⟨scrp, hscrp_len, hscrp_o,
                                                                      hpm_ok, hmp⟩
                                                              · c0_hsteps!
                                                                exact hJp1 pmask mp
                                                                  ⟨scrp, hscrp_len, hscrp_o,
                                                                    hpm_ok, hmp⟩
                                                            · c0_hsteps!
                                                              exact hJp1 pmask mp
                                                                ⟨scrp, hscrp_len, hscrp_o,
                                                                  hpm_ok, hmp⟩))
                                                  · c0_hsteps!
                                                    exact hJex1 mp ⟨scrp, hscrp_len, hscrp_o,
                                                      hpm_ok, hmp⟩
                                                · c0_hsteps!
                                                  exact hJex1 mp ⟨scrp, hscrp_len, hscrp_o,
                                                    hpm_ok, hmp⟩)
                                          · intro Lp hLp
                                            have hxmi := xorMaskEntriesOk_init
                                              (base := 1060) (lim := np.toNat)
                                              (by rw [hscrc_len]; omega) hi_lt
                                            have hscr_i_o : ∀ idx < c.scratch_cap,
                                                (idx < 1060 ∨ 1076 ≤ idx) →
                                                (scrc.set 1060 i)[idx]? = scrc[idx]? :=
                                              fun idx hi hor => by
                                                rw [List.getElem?_set_ne (by omega)]
                                            c0_hsteps!
                                            dsimp only [m7XorState] at hm ⊢
                                            rw [show scrc.set (1060#64).toNat i =
                                                scrc.set 1060 i from rfl] at hm
                                            exact hLp np.toNat (1#32, 0#32, ()) _
                                              ⟨scrc.set 1060 i, Nat.zero_le _, by simp,
                                                by rw [List.length_set, hscrc_len],
                                                hscr_i_o, hxmi, hm⟩
                                        · c0_hsteps!; exact hJ47 mb ⟨lmc, scrc, hlmc_len, hk_le,
                                            hscrc_len, hscrc_out, h1092_bd, hnz_c, hmb⟩
                                      · c0_hsteps!; exact hJ47 mb ⟨lmc, scrc, hlmc_len, hk_le,
                                          hscrc_len, hscrc_out, h1092_bd, hnz_c, hmb⟩))
                            · rintro B42 L43 ⟨k_c, ci_c⟩ mc hB42 hL43
                                ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len, hscrc_out,
                                  h1092_bd, hnz_c, hmc⟩
                              c0_hsplit
                              · have hci_lt : ci_c.toNat < sz.toNat := hc
                                have hcri : (cr.setWidth 64 + 3#64 + ci_c.setWidth 64).toNat <
                                    s.core.arena.length := by
                                  rw [har_len0]; c0_bound
                                let l := s.core.arena[(cr.setWidth 64 + 3#64 +
                                  ci_c.setWidth 64).toNat]'hcri
                                have hl_mem :
                                    l.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat := by
                                  rw [mem_fullArenaClauseLitsCore_iff (by rw [har_len0]; omega)]
                                  exact ⟨ci_c.toNat, by omega,
                                    congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
                                have hl_lt : l.toNat < 2 * s.core.cur_vars :=
                                  hw0.arena.lits_lt cr.toNat href_cr hng_cr _ hl_mem
                                have hl_v : (l.setWidth 64).toNat < s.core.vals.length := by
                                  rw [hval_len0, m6_zext32_toNat]; omega
                                have hl_lm : (l.setWidth 64).toNat < lmc.length := by
                                  rw [hlmc_len, m6_zext32_toNat]; omega
                                have hci1 : (ci_c + 1#32).toNat = ci_c.toNat + 1 := by c0_bound
                                c0_hsteps_nogrp
                                refine wp_join_state (ts := [.bool, i32])
                                  (α := Bool × BitVec 32) (fun x => (x.1, x.2, ()))
                                  (fun (ok_s, k') ms => XorCollectInv c s R sz k' ci_c ms)
                                  (fun _ ⟨ok_s, k'⟩ ms hk_s => by
                                    c0_hsteps!
                                    obtain ⟨l_s, s_s, _, hks, h1s, h2s, h3s, h4s, h5s, hms⟩ := hk_s
                                    exact hL43 (k', ci_c + 1#32) ms
                                      (by dsimp only; rw [hci1]; omega)
                                      ⟨l_s, s_s, by rw [hci1]; omega,
                                        hks, h1s, h2s, h3s, h4s, h5s, hms⟩)
                                  (fun J54 hJ54 => by
                                    c0_hsplit
                                    · c0_hsplit
                                      · c0_hsteps!; exact hB42 (false, k_c, ci_c) mc
                                          ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len,
                                            hscrc_out, h1092_bd, hnz_c, hmc⟩
                                      · c0_hsteps_nogrp
                                        refine wp_join_state (ts := [.bool, i32])
                                          (α := Bool × BitVec 32) (fun x => (x.1, x.2, ()))
                                          (fun (ok_s, k') ms => XorCollectInv c s R sz k' ci_c ms)
                                          (fun _ ⟨ok_s, k'⟩ ms hk_s => by
                                            c0_hsteps!
                                            exact hJ54 (ok_s, k') ms hk_s)
                                          (fun J55 hJ55 => by
                                            c0_hsplit
                                            rotate_left
                                            · c0_hsteps!; exact hJ55 (true, k_c) mc
                                                ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len,
                                                  hscrc_out, h1092_bd, hnz_c, hmc⟩
                                            · c0_hsplit
                                              · c0_hsteps!; exact hB42 (false, k_c, ci_c) mc
                                                  ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len,
                                                    hscrc_out, h1092_bd, hnz_c, hmc⟩
                                              · c0_hsplit
                                                · c0_hsteps!; exact hB42 (false, k_c, ci_c) mc
                                                    ⟨lmc, scrc, hci_le, hk_le, hlmc_len,
                                                      hscrc_len, hscrc_out, h1092_bd, hnz_c, hmc⟩
                                                · c0_hsplit
                                                  · c0_hsteps!; exact hB42 (false, k_c, ci_c) mc
                                                      ⟨lmc, scrc, hci_le, hk_le, hlmc_len,
                                                        hscrc_len, hscrc_out, h1092_bd, hnz_c, hmc⟩
                                                  · have hk_lt4 : k_c.toNat < 4 := by c0_bound
                                                    have hl1_lt :
                                                        (l ^^^ 1#32).toNat < 2 * s.core.cur_vars :=
                                                      m7_p3b_xor1_lt l hl_lt
                                                    have hl1_lm :
                                                        ((l ^^^ 1#32).setWidth 64).toNat <
                                                          lmc.length := by
                                                      rw [hlmc_len, m6_zext32_toNat]; omega
                                                    have hl_sc :
                                                        (l.setWidth 64).toNat < lmc.length :=
                                                      hl_lm
                                                    have h1092_k :
                                                        ((1092#32 + k_c).setWidth 64).toNat <
                                                          scrc.length := by
                                                      rw [hscrc_len]; c0_bound
                                                    have hk1 :
                                                        (k_c + 1#32).toNat = k_c.toNat + 1 := by
                                                      c0_bound
                                                    c0_hsteps_nogrp
                                                    have hl1_set :
                                                        ((l ^^^ 1#32).setWidth 64).toNat <
                                                          (lmc.set (l.setWidth 64).toNat
                                                            (BitVec.setWidth 8
                                                              (2#32 +
                                                                (k_c <<< 1#32)))).length := by
                                                      rw [List.length_set]; exact hl1_lm
                                                    c0_hsteps!
                                                    have hm_n :
                                                        (FullMem c (m7XorState s
                                                          ((lmc.set (l.setWidth 64).toNat
                                                              (BitVec.setWidth 8
                                                                (2#32 + (k_c <<< 1#32)))).set
                                                            ((l ^^^ 1#32).setWidth 64).toNat
                                                            (BitVec.setWidth 8
                                                              (3#32 + (k_c <<< 1#32))))
                                                          (scrc.set
                                                            ((1092#32 + k_c).setWidth 64).toNat
                                                            l)) ⋆ R) _ := hm
                                                    refine hJ55 (true, k_c + 1#32) _
                                                      ⟨_, _, hci_le, by omega,
                                                        by rw [List.length_set, List.length_set,
                                                             hlmc_len],
                                                        by rw [List.length_set, hscrc_len],
                                                        fun idx hi hor => by
                                                          rw [List.getElem?_set_ne (by c0_bound)]
                                                          exact hscrc_out idx hi hor,
                                                        fun j hj => by
                                                          by_cases hjk : j = k_c.toNat
                                                          · subst hjk
                                                            rw [show 1092 + k_c.toNat =
                                                                ((1092#32 + k_c).setWidth 64).toNat
                                                                  by c0_bound,
                                                              List.getElem?_set_self h1092_k,
                                                              Option.getD_some]
                                                            exact hl_lt
                                                          · rw [List.getElem?_set_ne (by c0_bound)]
                                                            exact h1092_bd j (by omega),
                                                        fun y hy hyn => ?_, hm_n⟩
                                                    by_cases hyl : y = l.toNat
                                                    · refine ⟨k_c.toNat, by omega, Or.inl ?_⟩
                                                      rw [show 1092 + k_c.toNat =
                                                          ((1092#32 + k_c).setWidth 64).toNat by
                                                            c0_bound,
                                                        List.getElem?_set_self h1092_k,
                                                        Option.getD_some]
                                                      exact hyl
                                                    · by_cases hyl1 : y = (l ^^^ 1#32).toNat
                                                      · refine ⟨k_c.toNat, by omega, Or.inr ?_⟩
                                                        rw [show 1092 + k_c.toNat =
                                                            ((1092#32 + k_c).setWidth 64).toNat by
                                                              c0_bound,
                                                          List.getElem?_set_self h1092_k,
                                                          Option.getD_some]
                                                        exact hyl1
                                                      · rw [List.getElem?_set_ne
                                                              (by rw [m6_zext32_toNat]
                                                                  exact Ne.symm hyl1),
                                                            List.getElem?_set_ne
                                                              (by rw [m6_zext32_toNat]
                                                                  exact Ne.symm hyl)]
                                                            at hyn
                                                        obtain ⟨jj, hjj, hyeq⟩ := hnz_c y
                                                          (by rw [List.length_set,
                                                                List.length_set] at hy
                                                              exact hy)
                                                          hyn
                                                        refine ⟨jj, by omega, ?_⟩
                                                        have h1092_ne :
                                                            ((1092#32 + k_c).setWidth 64).toNat ≠
                                                              1092 + jj := by
                                                          rw [show ((1092#32 + k_c).setWidth 64
                                                                ).toNat = 1092 + k_c.toNat by
                                                                c0_bound]
                                                          omega
                                                        rwa [List.getElem?_set_ne h1092_ne])
                                    · c0_hsteps!; exact hJ54 (true, k_c) mc
                                        ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len, hscrc_out,
                                          h1092_bd, hnz_c, hmc⟩)
                              · c0_hsteps!; exact hB42 (true, k_c, ci_c) mc
                                  ⟨lmc, scrc, hci_le, hk_le, hlmc_len, hscrc_len, hscrc_out,
                                    h1092_bd, hnz_c, hmc⟩
                            · intro B42 L43 hB42 hL43
                              c0_hsteps!
                              exact hL43 (0#32, 0#32) mi
                                ⟨lmi, scri, Nat.zero_le _, Nat.zero_le _, hlmi_len, hscri_len,
                                  hscri_out, fun _ hj => False.elim (Nat.not_lt_zero _ hj),
                                  fun y hy hyn => False.elim (hyn (by
                                    simpa [List.getElem?_eq_getElem hy] using hlmi_z y hy)),
                                  hmi⟩
                          · c0_hsteps!; exact hJ34 mi ⟨lmi, scri, hlmi_len, hlmi_z, hscri_len,
                              hscri_out, hmi⟩)
                    · c0_hsteps!
                      exact hQ false lmi scri mi hdw_i hscri_len hscri_out hmi
                  · intro L3 hL3; c0_hsteps!
                    exact hL3 np.toNat (0#32, ()) m0
                      ⟨s.core.lit_mark, s.scratch.scratch_buf, hlm_len0,
                        fun y hy => hlm0_clr.2 y (by rw [hlm_len0] at hy; exact hy),
                        hscr_len0, fun _ _ _ => rfl, Nat.zero_le _, by simp, hm0⟩
        · intro L2 hL2; c0_hsteps!
          exact hL2 nn.toNat (0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp⟩
    · intro L hL; c0_hsteps!
      exact hL np.toNat (0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp⟩

end LeanQbe.T.Examples.Kissat.FullM7BveGates
