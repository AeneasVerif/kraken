/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Gates.WpHelpers

/-!
# Kissat Gates WP Proofs — M7 ITE (`find_ite_side`, `find_ite`)

`CanonicalEnv`-clean `Func.wp` proofs for `full_bve_find_ite_side_m7` and
`full_bve_find_ite_m7` (`0` legacy `Full*` imports; every decl `<= 450` LOC).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Gates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Gates
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "gates_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "ite_neg_join" inv:term : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ())) ($inv) ?_
      (fun _ hJ => by c0_hsplit <;> (c0_hsteps!; exact hJ _ (by split <;> simp_all)))))

local macro "ite_pick_step" hPrev:ident : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [.bool, i32, i32, i32])
      (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
      (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2, ())) (fun _ => True)
      (fun _ p _ => by c0_hsteps!; exact $hPrev p trivial) ?_))

public section

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

private theorem m7_ite_hit_wp (Γ : Env) (c : FullCfg) (s0 : FullState)
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
  refine m7_setMaskBit_wp Γ c s0 scr6 R litMask i0 m6 Q X _
    hsc6 (by omega) hlm_lo hlm_hi hi0_lt hm6' ?_
  intro scr7 hsc7 hout7 m7 hm7
  have hout7' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
      scr7[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout7 i hi (by rcases hor with h | h <;> omega)).trans (hout6' i hi hor)
  clear hout7 hout6' hm6'
  refine m7_setMaskBit_wp Γ c s0 scr7 R litMask i1 m7 Q X _
    hsc7 (by omega) hlm_lo hlm_hi hi1_lt hm7 ?_
  intro scr8 hsc8 hout8 m8 hm8
  have hout8' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
      scr8[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout8 i hi (by rcases hor with h | h <;> omega)).trans (hout7' i hi hor)
  clear hout8 hout7' hm7
  refine m7_setMaskBit_wp Γ c s0 scr8 R oppMask (r0 &&& 0x7FFFFFFF#32) m8 Q X _
    hsc8 (by omega) hom_lo hom_hi hr0_lt hm8 ?_
  intro scr9 hsc9 hout9 m9 hm9
  have hout9' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
      scr9[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout9 i hi (by rcases hor with h | h <;> omega)).trans (hout8' i hi hor)
  clear hout9 hout8' hm8
  refine m7_setMaskBit_wp Γ c s0 scr9 R oppMask (r1 &&& 0x7FFFFFFF#32) m9 Q X _
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
    (fun _ hJtag => by c0_hsplit <;> (c0_hsteps!; exact hJtag _ trivial))
  intro _ tag _
  c0_hsteps!
  refine hQ true ((scr10.set (1056#64).toNat 1#32).set (1057#64).toNat tag) m ?_ ?_ ?_
  · simp [hsc10]
  · intro idx hidx hor
    rw [List.getElem?_set_ne (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
      List.getElem?_set_ne (by rw [show (1056#64).toNat = 1056 from rfl]; omega)]
    exact hout10' idx hidx hor
  · assumption

/-- Canonical `Func.wp` proof for `full_bve_find_ite_side_m7`. -/
theorem full_bve_find_ite_side_m7_wp (Γ : Env)
    (hGetTern : Γ.Has "full_bve_get_tern_m7" fullBveGetTernM7Spec)
    (hMatchTern : Γ.Has "full_bve_match_tern_m7" fullBveMatchTernM7Spec) :
    ∀ a m Q X, fullBveFindIteSideM7Spec a m Q X →
      Func.wp Γ full_bve_find_ite_side_m7_body a m Q X := by
  rintro ⟨h, v, np, nn, neg, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1066, hv_lt, hnp512, hnn512,
    hp_ok, hn_ok, hm0, hQ⟩ := fullBveFindIteSideM7Spec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl := pl_nl_eq v (by omega)
  unfold Func.wp full_bve_find_ite_side_m7_body
  ite_neg_join (fun x => x = if neg then 1#32 else 0#32); rintro _ fl rfl
  ite_neg_join (fun x => x = if neg then 512#32 else 0#32); rintro _ lit_off rfl
  ite_neg_join (fun x => x = if neg then nn else np); rintro _ lit_n rfl
  ite_neg_join (fun x => x = if neg then 0#32 else 512#32); rintro _ opp_off rfl
  ite_neg_join (fun x => x = if neg then np else nn); rintro _ opp_n rfl
  ite_neg_join (fun x => x = if neg then 1040#32 else 1024#32); rintro _ lit_mask rfl
  ite_neg_join (fun x => x = if neg then 1024#32 else 1040#32); rintro _ opp_mask rfl
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
    | succ j => rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ]; simp
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
      (if neg then 1040#32 else 1024#32).toNat + 16 ≤ 1056 := by cases neg <;> simp
  have hom_bd : 1024 ≤ (if neg then 1024#32 else 1040#32).toNat ∧
      (if neg then 1024#32 else 1040#32).toNat + 16 ≤ 1056 := by cases neg <;> simp
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
  · refine wp_loop_group (ts := [i64, i32])
      (fun rem (lc, idx, ()) mi => mi = m0 ∧ idx.toNat ≤ (if neg then nn else np).toNat ∧
        rem = (if neg then nn else np).toNat - idx.toNat ∧ lc.toNat ≤ idx.toNat)
      ?_ ?_
    · rintro L rem ⟨lc, idx, ⟨⟩⟩ mi hL ⟨rfl, hi_le, rfl, hlc_le⟩
      c0_hsplit
      · have hi_lt : idx.toNat < (if neg then nn else np).toNat := hc
        have hsc_idx : (((if neg then 512#32 else 0#32) + idx).setWidth 64).toNat <
            s0.scratch.scratch_buf.length := by
          rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; c0_bound
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
                let s1 : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr1 } }
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
                    rw [hsc1, zext32_toNat]; c0_bound
                  have hi0_eq : (((if neg then 512#32 else 0#32) + i0).setWidth 64).toNat =
                      (if neg then 512#32 else 0#32).toNat + i0.toNat := by
                    rw [zext32_toNat]; c0_bound
                  let w0 := scr1[(((if neg then 512#32 else 0#32) + i0).setWidth 64).toNat]'hi0_sc
                  have hw0_orig : w0 = s0.scratch.scratch_buf[
                      (if neg then 512#32 else 0#32).toNat + i0.toNat]?.getD 0#32 := by
                    have hg := hout1 ((if neg then 512#32 else 0#32).toNat + i0.toNat) (by omega)
                      (Or.inl (by omega))
                    have hi0' : (if neg then 512#32 else 0#32).toNat + i0.toNat < scr1.length :=
                      by omega
                    rw [List.getElem?_eq_getElem hi0'] at hg; rw [← hg, Option.getD_some]
                    exact (getElem_congr hi0_eq.symm hi0' hi0_sc).symm
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
                      getElem_congr (by rw [hi0_eq, Nat.mod_eq_of_lt (by omega)]) _ _
                    have hw0_bin0 : (w0 &&& 0x80000000#32) = 0#32 := by rw [hw0_c0]; exact hc
                    have hent0 := hlit_ent i0.toNat (by omega)
                    rw [← hw0_orig] at hent0; unfold FullBveEntryOkW at hent0
                    rw [ite_eq_right (fun h => h hw0_bin0)] at hent0
                    have hdw1 : FullDenseInvW c F0 F_cur
                        { s0 with scratch := { s0.scratch with scratch_buf := scr1 } } :=
                      fullDenseInvW_lm_scr hdw0 hdw0.1.core_ok.lit_mark_len hdw0.2.2.1.2 hsc1
                    c0_hsteps_nogrp
                    gates_call hGetTern
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
                              rw [hsc3, zext32_toNat]; c0_bound
                            have hi1_eq : (((if neg then 512#32 else 0#32) +
                                i1).setWidth 64).toNat =
                                (if neg then 512#32 else 0#32).toNat + i1.toNat := by
                              rw [zext32_toNat]; c0_bound
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
                              exact (getElem_congr hi1_eq.symm hi1' hi1_sc).symm
                            have hi11 : (i1 + 1#32).toNat = i1.toNat + 1 := by c0_bound
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [])
                              (fun _ m4' => ∃ scr4 : List (BitVec 32),
                                let s4 : FullState :=
                                  { s0 with scratch := { s0.scratch with scratch_buf := scr4 } }
                                scr4.length = c.scratch_cap ∧
                                (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                  scr4[i]? = s0.scratch.scratch_buf[i]?) ∧
                                (FullMem c s4 ⋆ R) m4')
                              (fun _ _ m4' ⟨scr4, hsc4, hout4, hm4⟩ => by
                                c0_hsteps!
                                exact hL1 ((if neg then nn else np).toNat - (i1 + 1#32).toNat)
                                  (i1 + 1#32, ()) m4' (by rw [hi11]; omega)
                                  ⟨scr4, hsc4, by rw [hi11]; omega, rfl, hout4, hm4⟩)
                              ?_
                            intro _ hJ1
                            c0_hsplit
                            · have hw1_c0 : w1 = scr3[((if neg then 512#32 else 0#32).toNat +
                                  i1.toNat) % 2 ^ 32]'(by
                                    rw [Nat.mod_eq_of_lt (by omega), hsc3]; omega) :=
                                getElem_congr (by rw [hi1_eq, Nat.mod_eq_of_lt (by omega)]) _ _
                              have hw1_bin0 : (w1 &&& 0x80000000#32) = 0#32 := by
                                rw [hw1_c0]; exact hc
                              have hent1 := hlit_ent i1.toNat (by omega)
                              rw [← hw1_orig] at hent1; unfold FullBveEntryOkW at hent1
                              rw [ite_eq_right (fun h => h hw1_bin0)] at hent1
                              have hdw3 : FullDenseInvW c F0 F_cur
                                  { s0 with scratch := { s0.scratch with scratch_buf := scr3 } } :=
                                fullDenseInvW_lm_scr hdw0 hdw0.1.core_ok.lit_mark_len
                                  hdw0.2.2.1.2 hsc3
                              c0_hsteps_nogrp
                              gates_call hGetTern
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
                                  (fun _ hJk => by
                                    c0_hsplit
                                    · c0_hsteps!; exact hJk (_, _, _, _) trivial
                                    · ite_pick_step hJk
                                      intro _ hJk2; c0_hsplit
                                      · c0_hsteps!; exact hJk2 (_, _, _, _) trivial
                                      · ite_pick_step hJk2
                                        intro _ hJk3; c0_hsplit
                                        · c0_hsteps!; exact hJk3 (_, _, _, _) trivial
                                        · ite_pick_step hJk3
                                          intro _ hJk4; c0_hsplit <;>
                                            (c0_hsteps!; exact hJk4 (_, _, _, _) trivial))
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
                                    fullDenseInvW_lm_scr hdw0
                                      hdw0.1.core_ok.lit_mark_len hdw0.2.2.1.2 hsc4
                                  c0_hsteps_nogrp
                                  rotate_left 1
                                  · exact hJno () m4 ⟨scr4, hsc4, hout4', hm4'⟩
                                  gates_call hMatchTern
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
                                      have := u32_and7fff_lt r0 hr0_bd hc; omega
                                    have hdw5 : FullDenseInvW c F0 F_cur
                                        { s0 with
                                          scratch := { s0.scratch with scratch_buf := scr5 } } :=
                                      fullDenseInvW_lm_scr hdw0
                                        hdw0.1.core_ok.lit_mark_len hdw0.2.2.1.2 hsc5
                                    c0_hsteps_nogrp
                                    gates_call hMatchTern
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
                                        have := u32_and7fff_lt r1 hr1_bd hc; omega
                                      clear hdw5 hdw4 hdw3 hdw1 hdw0 hlit_ent hopp_ent
                                        hp_ok hn_ok hm5' hm4' hm3 hm1 hJ1 hJ0
                                        hJno hJm0 hL1 hL0 hL
                                      c0_hstep; c0_hstep; c0_hstep; c0_hsplit
                                      rotate_left 1
                                      · c0_hsteps!
                                        exact hJm1 () m6 ⟨scr6, hsc6, hout6', hm6'⟩
                                      clear hJm1
                                      exact m7_ite_hit_wp Γ c s0 scr6 R _ _ i0 i1 r0 r1
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
                        exact hL1 ((if neg then nn else np).toNat - (i0 + 1#32).toNat)
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

/-- Canonical `Func.wp` proof for `full_bve_find_ite_m7`. -/
theorem full_bve_find_ite_m7_wp (Γ : Env)
    (hFindIteSide : Γ.Has "full_bve_find_ite_side_m7" fullBveFindIteSideM7Spec) :
    ∀ a m Q X, fullBveFindIteM7Spec a m Q X →
      Func.wp Γ full_bve_find_ite_m7_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1066, hv_lt, hnp512, hnn512,
    hp_ok, hn_ok, hm0, hQ⟩ := fullBveFindIteM7Spec_elim hSpec
  unfold Func.wp full_bve_find_ite_m7_body
  c0_hsteps_nogrp
  gates_call hFindIteSide
  change fullBveFindIteSideM7Spec (c.hdr, v, np, nn, false, ()) _ _ _
  refine fullBveFindIteSideM7Spec_intro rfl hdw0 hsc1066 hv_lt hnp512 hnn512 hp_ok hn_ok hm0 ?_
  intro ok1 scr1 m1 s1 hsc1 hout1 hm1
  c0_hsplit
  · c0_hsteps!; exact hQ true scr1 m1 hsc1 hout1 hm1
  · have hdw1 : FullDenseInvW c F0 F_cur s1 :=
      fullDenseInvW_lm_scr hdw0 hdw0.1.core_ok.lit_mark_len hdw0.2.2.1.2 hsc1
    c0_hsteps_nogrp
    gates_call hFindIteSide
    change fullBveFindIteSideM7Spec (c.hdr, v, np, nn, true, ()) _ _ _
    refine fullBveFindIteSideM7Spec_intro rfl hdw1 hsc1066 hv_lt hnp512 hnn512
      (fun i hi => by
        dsimp only [s1]; rw [hout1 i (by have := c.hscr; unfold dimacsBound at this; omega)
          (Or.inl (by omega))]
        exact bveEntry_congr_core (hp_ok i hi) rfl rfl rfl)
      (fun j hj => by
        dsimp only [s1]; rw [hout1 (512 + j) (by have := c.hscr; unfold dimacsBound at this; omega)
          (Or.inl (by omega))]
        exact bveEntry_congr_core (hn_ok j hj) rfl rfl rfl)
      hm1 ?_
    intro ok2 scr2 m2 s2 hsc2 hout2 hm2
    c0_hsteps!
    exact hQ ok2 scr2 m2 hsc2 (fun i hi hor => (hout2 i hi hor).trans (hout1 i hi hor)) hm2

end

end LeanQbe.T.Examples.Kissat.Proof.Gates
