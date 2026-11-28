/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpEls0

/-!
# Equivalent-Literal Substitution Literal & Driver WP Proofs (`Proof.Sweep.WpEls1`)

Clean flat-`CanonicalEnv` `Func.wp` proofs against `Src.Sweep` and `Proof.Sweep.Spec`:
1. `full_m6_els_lit_wp` (`fullM6ElsLitSpec`)
2. `full_m6_dense_els_wp` (`fullM6DenseElsSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Sweep
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
open LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
open FullArenaTactics M6ElsBvExt
open scoped FullArenaTactics M6SweepTactics M6ElsBv M6ElsBvExt

/-! ## 1. Watch-Pop / Watch-Compact `FullDenseInvW` & Pure `FullCongReprInv` Helpers -/

private theorem m6_denseInvW_watchPop {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {l popK : Nat} (hl : l < 2 * s.core.cur_vars)
    (hpop : popK ≤ fullWatchSize s l) (wu' : BitVec 64)
    (hsl' : DenseWatchSliceOk F_cur s.core l (fullWatchOff s l + popK) (fullWatchSize s l - popK)) :
    let off := fullWatchOff s l
    let sz := fullWatchSize s l
    let wvec' := (s.core.wvec.set (2 * l) (BitVec.ofNat 32 (off + popK))).set (2 * l + 1)
      (BitVec.ofNat 32 (sz - popK))
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wusable := wu' } } := by
  intro off sz wvec'
  let s' : FullState := { s with core := { s.core with wvec := wvec', wusable := wu' } }
  have hcl := hinv.1.core_ok; have hw := hinv.2.1
  have hwm := hw.watches; unfold ModeWatchesInv at hwm
  rw [ite_eq_right (fun h0 => hinv.2.2.2.2.2.2 h0)] at hwm
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hbd_l := hwm.layout.bounds l hl
  have hoff_eq : off = fullWatchOffCore s.core l := rfl
  have hsz_eq : sz = fullWatchSizeCore s.core l := rfl
  have hpop_c : popK ≤ fullWatchSizeCore s.core l := hpop
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hwlen_le := hcl.wlen_le
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with wvec_len := by simp [s', wvec', hwvl] }, hinv.1.scratch_ok⟩
  have hlt32_o : off + popK < 2 ^ 32 := by rw [hoff_eq]; omega
  have hlt32_s : sz - popK < 2 ^ 32 := by rw [hsz_eq]; omega
  have hoff_l' : fullWatchOffCore s'.core l = off + popK := by
    unfold fullWatchOffCore; dsimp only [s', wvec']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32_o]
  have hsz_l' : fullWatchSizeCore s'.core l = sz - popK := by
    unfold fullWatchSizeCore; dsimp only [s', wvec']
    rw [List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32_s]
  have hoth : ∀ l' ≠ l,
      fullWatchOffCore s'.core l' = fullWatchOffCore s.core l' ∧
      fullWatchSizeCore s'.core l' = fullWatchSizeCore s.core l' := fun l' hne => by
    unfold fullWatchOffCore fullWatchSizeCore; dsimp only [s', wvec']
    exact ⟨by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
           by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]⟩
  have hlay' : WatchStackLayout s'.core := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l' hl'
      by_cases hll : l' = l
      · rw [hll, hoff_l', hsz_l', hoff_eq, hsz_eq]
        change fullWatchOffCore s.core l + popK + (fullWatchSizeCore s.core l - popK) ≤ s.core.wlen
        omega
      · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho, hs]; exact hwm.layout.bounds l' hl'
    · intro l' hl' hpos
      by_cases hll : l' = l
      · rw [hll, hoff_l', hoff_eq]; rw [hll, hsz_l', hsz_eq] at hpos
        have := hwm.layout.pos_off l hl (by omega); omega
      · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho]; rw [hs] at hpos
        exact hwm.layout.pos_off l' hl' hpos
    · intro l1 l2 h1 h2 hne hp1 hp2
      have hb1 : fullWatchOffCore s.core l1 ≤ fullWatchOffCore s'.core l1 ∧
          fullWatchOffCore s'.core l1 + fullWatchSizeCore s'.core l1 =
            fullWatchOffCore s.core l1 + fullWatchSizeCore s.core l1 ∧
          0 < fullWatchSizeCore s.core l1 := by
        by_cases h1l : l1 = l
        · rw [h1l, hoff_l', hsz_l', hoff_eq, hsz_eq]; rw [h1l, hsz_l', hsz_eq] at hp1
          exact ⟨by omega, by omega, by omega⟩
        · obtain ⟨ho, hs⟩ := hoth l1 h1l; rw [ho, hs]; exact ⟨le_refl _, rfl, hs ▸ hp1⟩
      have hb2 : fullWatchOffCore s.core l2 ≤ fullWatchOffCore s'.core l2 ∧
          fullWatchOffCore s'.core l2 + fullWatchSizeCore s'.core l2 =
            fullWatchOffCore s.core l2 + fullWatchSizeCore s.core l2 ∧
          0 < fullWatchSizeCore s.core l2 := by
        by_cases h2l : l2 = l
        · rw [h2l, hoff_l', hsz_l', hoff_eq, hsz_eq]; rw [h2l, hsz_l', hsz_eq] at hp2
          exact ⟨by omega, by omega, by omega⟩
        · obtain ⟨ho, hs⟩ := hoth l2 h2l; rw [ho, hs]; exact ⟨le_refl _, rfl, hs ▸ hp2⟩
      have hd := hwm.layout.disjoint l1 l2 h1 h2 hne hb1.2.2 hb2.2.2
      omega
    · intro l' hl' idx hidx
      by_cases hll : l' = l
      · rw [hll, hoff_l', hoff_eq]; rw [hll, hsz_l', hsz_eq] at hidx
        simpa [s', show fullWatchOffCore s.core l + popK + idx =
          fullWatchOffCore s.core l + (popK + idx) by omega] using
          hwm.layout.no_sentinel l hl (popK + idx) (by omega)
      · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho]; rw [hs] at hidx
        exact hwm.layout.no_sentinel l' hl' idx hidx
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hwat' : ModeWatchesInv F_cur s'.core := by
    unfold ModeWatchesInv; rw [ite_eq_right (fun h0 => hinv.2.2.2.2.2.2 h0)]
    refine ⟨hlay', fun l' hl' => ?_⟩
    by_cases hll : l' = l
    · rw [hll, hoff_l', hsz_l']
      exact DenseWatchSliceOk.relocate (k := s.core) (k' := s'.core) hrefl (le_refl _)
        (fun _ r => r) (fun _ _ => rfl) hsl'
    · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho, hs]
      exact DenseWatchSliceOk.relocate (k := s.core) (k' := s'.core) hrefl (le_refl _)
        (fun _ r => r) (fun _ _ => rfl) (hwm.slices l' hl')
  exact ⟨hlen', { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' },
    hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
    hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_watchCompact {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {ot newSz : Nat} (hot : ot < 2 * s.core.cur_vars) (hle_sz : newSz ≤ fullWatchSize s ot)
    {wstk' : List (BitVec 32)} (hwl' : wstk'.length = c.wcap)
    (hout : ∀ i, i < fullWatchOff s ot ∨ fullWatchOff s ot + fullWatchSize s ot ≤ i →
      wstk'[i]? = s.core.wstk[i]?)
    (hsl' : DenseWatchSliceOk F_cur { s.core with wstk := wstk' } ot (fullWatchOff s ot) newSz)
    (wu' nb' : BitVec 64) :
    let wvec' := s.core.wvec.set (2 * ot + 1) (BitVec.ofNat 32 newSz)
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with
        wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } := by
  intro wvec'
  let s' : FullState :=
    { s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } }
  have hcl := hinv.1.core_ok; have hw := hinv.2.1
  have hwm := hw.watches; unfold ModeWatchesInv at hwm
  rw [ite_eq_right (fun h0 => hinv.2.2.2.2.2.2 h0)] at hwm
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hbd_ot := hwm.layout.bounds ot hot
  have hwlen_le := hcl.wlen_le
  let off := fullWatchOff s ot; let sz := fullWatchSize s ot
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with wvec_len := by simp [s', wvec', hwvl], wstk_len_arr := hwl' }, hinv.1.scratch_ok⟩
  have hlt32_s : newSz < 2 ^ 32 := by
    have : sz ≤ s.core.wlen := by change fullWatchSizeCore s.core ot ≤ s.core.wlen; omega
    omega
  have hoff_ot' : fullWatchOffCore s'.core ot = off := by
    unfold fullWatchOffCore; dsimp only [s', wvec']
    rw [List.getElem?_set_ne (by omega)]; rfl
  have hsz_ot' : fullWatchSizeCore s'.core ot = newSz := by
    unfold fullWatchSizeCore; dsimp only [s', wvec']
    rw [List.getElem?_set_self (by rw [hwvl]; omega), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32_s]
  have hoth : ∀ l' ≠ ot,
      fullWatchOffCore s'.core l' = fullWatchOffCore s.core l' ∧
      fullWatchSizeCore s'.core l' = fullWatchSizeCore s.core l' := fun l' hne => by
    unfold fullWatchOffCore fullWatchSizeCore; dsimp only [s', wvec']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact ⟨rfl, rfl⟩
  have hdisj_sub : ∀ l' < 2 * s.core.cur_vars, l' ≠ ot → 0 < fullWatchSizeCore s.core l' →
      ∀ idx < fullWatchSizeCore s.core l',
        wstk'[fullWatchOffCore s.core l' + idx]? = s.core.wstk[fullWatchOffCore s.core l' + idx]? :=
    fun l' hl' hne hpos idx hidx => by
      by_cases hsz0 : fullWatchSizeCore s.core ot = 0
      · exact hout _ (by change _ < fullWatchOffCore s.core ot ∨
          fullWatchOffCore s.core ot + fullWatchSizeCore s.core ot ≤ _; omega)
      · have hd := hwm.layout.disjoint l' ot hl' hot hne hpos (by omega)
        exact hout _ (by
          change _ < fullWatchOffCore s.core ot ∨
            fullWatchOffCore s.core ot + fullWatchSizeCore s.core ot ≤ _
          cases hd with | inl h => exact Or.inl (by omega) | inr h => exact Or.inr (by omega))
  have hlay' : WatchStackLayout s'.core := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l' hl'
      by_cases hll : l' = ot
      · rw [hll, hoff_ot', hsz_ot']; change fullWatchOffCore s.core ot + newSz ≤ s.core.wlen
        change newSz ≤ fullWatchSizeCore s.core ot at hle_sz; omega
      · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho, hs]; exact hwm.layout.bounds l' hl'
    · intro l' hl' hpos
      by_cases hll : l' = ot
      · rw [hll, hoff_ot']; rw [hll, hsz_ot'] at hpos
        exact hwm.layout.pos_off ot hot
          (by change newSz ≤ fullWatchSizeCore s.core ot at hle_sz; omega)
      · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho]; rw [hs] at hpos
        exact hwm.layout.pos_off l' hl' hpos
    · intro l1 l2 h1 h2 hne hp1 hp2
      have hb1 : fullWatchOffCore s.core l1 ≤ fullWatchOffCore s'.core l1 ∧
          fullWatchOffCore s'.core l1 + fullWatchSizeCore s'.core l1 ≤
            fullWatchOffCore s.core l1 + fullWatchSizeCore s.core l1 ∧
          0 < fullWatchSizeCore s.core l1 := by
        by_cases h1l : l1 = ot
        · rw [h1l, hoff_ot', hsz_ot']; rw [h1l, hsz_ot'] at hp1
          exact ⟨le_refl _, (by
            change fullWatchOffCore s.core ot + newSz ≤
              fullWatchOffCore s.core ot + fullWatchSizeCore s.core ot
            change newSz ≤ fullWatchSizeCore s.core ot at hle_sz; omega),
            (by change newSz ≤ fullWatchSizeCore s.core ot at hle_sz; omega)⟩
        · obtain ⟨ho, hs⟩ := hoth l1 h1l; rw [ho, hs]; exact ⟨le_refl _, le_refl _, hs ▸ hp1⟩
      have hb2 : fullWatchOffCore s.core l2 ≤ fullWatchOffCore s'.core l2 ∧
          fullWatchOffCore s'.core l2 + fullWatchSizeCore s'.core l2 ≤
            fullWatchOffCore s.core l2 + fullWatchSizeCore s.core l2 ∧
          0 < fullWatchSizeCore s.core l2 := by
        by_cases h2l : l2 = ot
        · rw [h2l, hoff_ot', hsz_ot']; rw [h2l, hsz_ot'] at hp2
          exact ⟨le_refl _, (by
            change fullWatchOffCore s.core ot + newSz ≤
              fullWatchOffCore s.core ot + fullWatchSizeCore s.core ot
            change newSz ≤ fullWatchSizeCore s.core ot at hle_sz; omega),
            (by change newSz ≤ fullWatchSizeCore s.core ot at hle_sz; omega)⟩
        · obtain ⟨ho, hs⟩ := hoth l2 h2l; rw [ho, hs]; exact ⟨le_refl _, le_refl _, hs ▸ hp2⟩
      have hd := hwm.layout.disjoint l1 l2 h1 h2 hne hb1.2.2 hb2.2.2
      omega
    · intro l' hl' idx hidx
      by_cases hll : l' = ot
      · rw [hll, hoff_ot']; rw [hll, hsz_ot'] at hidx; exact hsl'.ne_sentinel idx hidx
      · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho]; rw [hs] at hidx
        change wstk'[fullWatchOffCore s.core l' + idx]? ≠ some 0xFFFFFFFF#32
        rw [hdisj_sub l' hl' hll (by omega) idx hidx]
        exact hwm.layout.no_sentinel l' hl' idx hidx
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hwat' : ModeWatchesInv F_cur s'.core := by
    unfold ModeWatchesInv; rw [ite_eq_right (fun h0 => hinv.2.2.2.2.2.2 h0)]
    refine ⟨hlay', fun l' hl' => ?_⟩
    by_cases hll : l' = ot
    · rw [hll, hoff_ot', hsz_ot']
      exact DenseWatchSliceOk.relocate (k := { s.core with wstk := wstk' }) (k' := s'.core)
        hrefl (le_refl _) (fun _ r => r) (fun _ _ => rfl) hsl'
    · obtain ⟨ho, hs⟩ := hoth l' hll; rw [ho, hs]
      by_cases hpos : 0 < fullWatchSizeCore s.core l'
      · exact DenseWatchSliceOk.relocate (k := s.core) (k' := s'.core) hrefl (le_refl _)
          (fun _ r => r) (fun idx hidx => hdisj_sub l' hl' hll hpos idx hidx)
          (hwm.slices l' hl')
      · have hz : fullWatchSizeCore s.core l' = 0 := by omega
        rw [hz]; exact .empty
  exact ⟨hlen', { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' },
    hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
    hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_litEquiv_refl (f : CNF Nat) (a : Nat) : LitEquiv f a a := by
  constructor <;> (
    rw [CNF.entails_clause_def]; intro α _; rw [← clauseEvalVal_iff]
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg]
    cases evalLitVal α a <;> rfl)

private theorem m6_litEquiv_symm {f : CNF Nat} {a b : Nat} (h : LitEquiv f a b) :
    LitEquiv f b a := by
  have hcomm : ∀ x y, f.EntailsClause (cnfClause [x, y]) →
      f.EntailsClause (cnfClause [y, x]) := fun x y hc => by
    rw [CNF.entails_clause_def] at hc ⊢; intro α hα
    have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
    rw [← clauseEvalVal_iff]
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
    simpa [Bool.or_comm] using h1
  exact ⟨hcomm _ _ h.2, hcomm _ _ h.1⟩

private theorem m6_litEquiv_trans {f : CNF Nat} {a b c : Nat}
    (h1 : LitEquiv f a b) (h2 : LitEquiv f b c) : LitEquiv f a c := by
  constructor <;> (
    rw [CNF.entails_clause_def]; intro α hα
    have e1 := litEquiv_eval hα h1; have e2 := litEquiv_eval hα h2
    rw [← clauseEvalVal_iff]
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg]
    rw [e1, e2]; cases evalLitVal α c <;> rfl)

private theorem m6_litEquiv_self_neg_unsat {f : CNF Nat} {a : Nat}
    (h : LitEquiv f (a ^^^ 1) a) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have e := litEquiv_eval hα h
  rw [show a ^^^ 1 = litNeg a from rfl, evalLitVal_litNeg] at e
  cases hb : evalLitVal α a <;> simp [hb] at e

private theorem m6_litEquiv_entails_bin {f : CNF Nat} {a b : Nat} (h : LitEquiv f a b) :
    f.EntailsClause (cnfClause [a, b ^^^ 1]) ∧ f.EntailsClause (cnfClause [a ^^^ 1, b]) := by
  constructor <;> (
    rw [CNF.entails_clause_def]; intro α hα
    have e := litEquiv_eval hα h
    rw [← clauseEvalVal_iff]
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
      show a ^^^ 1 = litNeg a from rfl, show b ^^^ 1 = litNeg b from rfl, evalLitVal_litNeg]
    rw [e]; cases evalLitVal α b <;> rfl)

private theorem m6_div2_lt_of_lt_ne_xor1 {ra rb : BitVec 32}
    (hlt : ra.toNat < rb.toNat) (hne : ra ≠ rb ^^^ 1#32) : ra.toNat / 2 < rb.toNat / 2 := by
  cases Nat.lt_or_ge (ra.toNat / 2) (rb.toNat / 2) with
  | inl h => exact h
  | inr hge =>
    exfalso; apply hne; apply BitVec.eq_of_toNat_eq
    rw [m6_els_bv32_xor1_toNat, m6_nat_xor1_cases]; split <;> omega

private theorem m6_congReprInv_merge {F_cur : List (List Nat)} {nvars : Nat}
    {repr : List (BitVec 32)} (hinv : FullCongReprInv F_cur (2 * nvars) repr)
    {ra rb : BitVec 32} (hlt : ra.toNat < rb.toNat) (hrb : rb.toNat < 2 * nvars)
    (hne : ra ≠ rb ^^^ 1#32) (heqv : LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat) :
    FullCongReprInv F_cur (2 * nvars)
      ((repr.set rb.toNat ra).set (rb ^^^ 1#32).toNat (ra ^^^ 1#32)) := by
  have hdiv : ra.toNat / 2 < rb.toNat / 2 := m6_div2_lt_of_lt_ne_xor1 hlt hne
  have hrb1_to : (rb ^^^ 1#32).toNat = rb.toNat ^^^ 1 := by simp
  have hra1_to : (ra ^^^ 1#32).toNat = ra.toNat ^^^ 1 := by simp
  have hrb1_ne : (rb ^^^ 1#32).toNat ≠ rb.toNat := by
    rw [hrb1_to, m6_nat_xor1_cases]; split <;> omega
  have hrb1_lt : (rb ^^^ 1#32).toNat < repr.length := by
    have := hinv.1.1; rw [hrb1_to, m6_nat_xor1_cases]; split <;> omega
  have hrb_lt : rb.toNat < repr.length := by have := hinv.1.1; omega
  have hra1_le : (ra ^^^ 1#32).toNat ≤ (rb ^^^ 1#32).toNat := by
    rw [hra1_to, hrb1_to, m6_nat_xor1_cases, m6_nat_xor1_cases]; split <;> split <;> omega
  refine ⟨⟨by simp [hinv.1.1], fun l hl => ?_⟩, fun l hl => ?_⟩
  · by_cases h1 : l = (rb ^^^ 1#32).toNat
    · subst h1
      rw [List.getElem?_set_self (by rw [List.length_set]; exact hrb1_lt), Option.getD_some]
      exact hra1_le
    · rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = rb.toNat
      · subst h2; rw [List.getElem?_set_self hrb_lt, Option.getD_some]; omega
      · rw [List.getElem?_set_ne (Ne.symm h2)]; exact hinv.1.2 l hl
  · by_cases h1 : l = (rb ^^^ 1#32).toNat
    · subst h1
      rw [List.getElem?_set_self (by rw [List.length_set]; exact hrb1_lt), Option.getD_some,
        hrb1_to, hra1_to]
      exact m6_litEquiv_neg (m6_litEquiv_symm heqv)
    · rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = rb.toNat
      · subst h2; rw [List.getElem?_set_self hrb_lt, Option.getD_some]
        exact m6_litEquiv_symm heqv
      · rw [List.getElem?_set_ne (Ne.symm h2)]; exact hinv.2 l hl

private theorem m6_bv8_ne0_of_sext {v : BitVec 8} (h : ¬v.signExtend 32 = 0#32) : v ≠ 0#8 :=
  fun h0 => h ((m6_bv8_sext32_eq0_iff v).mpr h0)

private theorem m6_dense_els_vals_contra {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {a b : Nat} (ha : a < 2 * k.cur_vars) (hb : b < 2 * k.cur_vars)
    (heqv : LitEquiv (cnfOfClauses F_cur) a b)
    (hva_nz : k.vals[a]?.getD 0#8 ≠ 0#8) (hvb_nz : k.vals[b]?.getD 0#8 ≠ 0#8)
    (hne : k.vals[a]?.getD 0#8 ≠ k.vals[b]?.getD 0#8) : (cnfOfClauses F_cur).Unsat := by
  rcases hw.vals_domain a ha with ha0 | ha1 | haf
  · exact absurd ha0 hva_nz
  · rcases hw.vals_domain b hb with hb0 | hb1 | hbf
    · exact absurd hb0 hvb_nz
    · exact absurd (ha1.trans hb1.symm) hne
    · exact m6_litEquiv_unsat_contra heqv
        (m6_lvl0_true_entails hw hcl0 ha ha1) (m6_lvl0_false_entails hw hcl0 hb hbf)
  · rcases hw.vals_domain b hb with hb0 | hb1 | hbf
    · exact absurd hb0 hvb_nz
    · exact m6_litEquiv_unsat_contra (m6_litEquiv_symm heqv)
        (m6_lvl0_true_entails hw hcl0 hb hb1) (m6_lvl0_false_entails hw hcl0 ha haf)
    · exact absurd (haf.trans hbf.symm) hne

private theorem m6_dense_els_unit_of_val {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {a b : Nat} (ha : a < 2 * k.cur_vars) (heqv : LitEquiv (cnfOfClauses F_cur) a b)
    (hva_nz : k.vals[a]?.getD 0#8 ≠ 0#8) :
    ((0#8).slt (k.vals[a]?.getD 0#8) = true →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [b])) ∧
    ((0#8).slt (k.vals[a]?.getD 0#8) = false →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [b ^^^ 1])) := by
  have hunit_subst : ∀ {x y}, LitEquiv (cnfOfClauses F_cur) x y →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [x]) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [y]) := fun hx he =>
    m6_entails_unit_of_dup (m6_entails_bin_subst hx hx
      (CNF.entails_clause_def.mpr fun β hβ => by
        have h := (clauseEvalVal_iff β _).mpr (CNF.entails_clause_def.mp he β hβ)
        rw [← clauseEvalVal_iff]; simpa [clauseEvalVal] using h))
  rcases hw.vals_domain a ha with ha0 | ha1 | haf
  · exact absurd ha0 hva_nz
  · refine ⟨fun _ => hunit_subst heqv (m6_lvl0_true_entails hw hcl0 ha ha1), fun hf => ?_⟩
    rw [ha1] at hf; exfalso; revert hf; decide
  · refine ⟨fun ht => ?_, fun _ => hunit_subst (m6_litEquiv_neg heqv)
      (m6_lvl0_false_entails hw hcl0 ha haf)⟩
    rw [haf] at ht; exfalso; revert ht; decide

/-! ## 2. `full_m6_els_lit_wp` -/

private theorem m6_els_frame_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {R : Mem 64 → Prop} {mL : Mem 64} {Q : Post [.bool]}
    (h : M6ElsFrame c F0 F_cur s sL) (hmL : (FullMem c sL ⋆ R) mL)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (decide (sL.core.inconsistent = 0#64), ()) mL := by
  by_cases hinc : sL.core.inconsistent = 0#64
  · rw [decide_eq_true hinc]
    exact hQ true sL mL h.dinv h.cv h.fuel h.repr h.tmk h.trh h.scr h.ws1 h.ws2 h.gu
      (fun hn => Bool.noConfusion hn) hmL
  · rw [decide_eq_false hinc]
    exact hQ false sL mL h.dinv h.cv h.fuel h.repr h.tmk h.trh h.scr h.ws1 h.ws2 h.gu
      (fun _ => ⟨h.dinv.2.1.ext_sound.2 (h.dinv.2.1.inconsistent_sound hinc), hinc⟩) hmL

private theorem m6_els_compact_ot_watches {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s1 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {l ot : BitVec 32} {ooff_v oend_v : BitVec 64}
    {Jc2 : Cont []}
    (hinv1 : FullDenseInvW c F0 F_cur s1) (hot_lt : ot.toNat < 2 * s1.core.cur_vars)
    (hosz_pos : 0 < fullWatchSize s1 ot.toNat)
    (hooff_v : ooff_v = BitVec.ofNat 64 (fullWatchOff s1 ot.toNat))
    (hoend_v : oend_v = BitVec.ofNat 64 (fullWatchOff s1 ot.toNat + fullWatchSize s1 ot.toNat))
    (hm1 : (FullMem c s1 ⋆ R) m)
    (hCont : ∀ (wvec' wstk' : List (BitVec 32)) (wu' nb' : BitVec 64) (mf : Mem 64),
      FullDenseInvW c F0 F_cur { s1 with core := { s1.core with
        wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } →
      (FullMem c { s1 with core := { s1.core with
        wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } ⋆ R) mf →
      Jc2 () mf) :
    wp Γ Q X
      (Expr.group (sig := [[i64, i64, .bool]]) (fun Js => Blocks.cons (fun p =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64) (Arg.var p.fst, Arg.var oend_v, ()))
          fun p1 => Expr.jnz (Arg.var p1.fst)
          (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p2 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var p2.fst, ())) fun p3 =>
            Expr.load i32 (Arg.var p3.fst) fun ld =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p4 =>
            Expr.group (sig := [[i64, i64, .bool]]) (fun _ => Blocks.cons (fun q =>
              Expr.jump Js.fst (Arg.var q.fst, Arg.var q.snd.fst, Arg.var q.snd.snd.fst, ()))
              Blocks.nil) fun Js =>
            Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 2147483648, ())) fun p5 =>
            Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var p5.fst, Arg.imm 0, ())) fun p6 =>
            Expr.jnz (Arg.var p6.fst)
              (Expr.group (sig := [[i64, .bool]]) (fun _ => Blocks.cons (fun q =>
                Expr.jump Js.fst (Arg.var p4.fst, Arg.var q.fst, Arg.var q.snd.fst, ()))
                Blocks.nil) fun Js =>
                Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ())) fun q8 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var q8.fst, ()))
                    fun q9 => Expr.store (t := i32) (Arg.var ld) (Arg.var q9.fst)
                    (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.snd.fst, Arg.imm 1, ()))
                      fun q10 => Expr.jump Js.fst (Arg.var q10.fst, Arg.var p.snd.snd.fst, ())))
                  Blocks.nil) fun Js1 =>
                Expr.jnz (Arg.var p.snd.snd.fst) (Expr.jump Js1.fst ())
                  (Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 2147483647, ()))
                    fun q7 => Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32)
                      (Arg.var q7.fst, Arg.var l, ())) fun q8 =>
                    Expr.jnz (Arg.var q8.fst)
                      (Expr.jump Js.fst (Arg.var p.snd.fst, Arg.imm true, ()))
                      (Expr.jump Js1.fst ())))
              (Expr.group (sig := [[i64, i64]]) (fun _ => Blocks.cons (fun q7 =>
                Expr.jump Js.fst (Arg.var q7.fst, Arg.var q7.snd.fst, Arg.var p.snd.snd.fst, ()))
                Blocks.nil) fun Js =>
                Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64) (Arg.var p4.fst, Arg.var oend_v, ()))
                  fun q7 => Expr.jnz (Arg.var q7.fst)
                  (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ())) fun q8 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var q8.fst, ()))
                      fun q9 => Expr.store (t := i32) (Arg.var ld) (Arg.var q9.fst)
                      (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.snd.fst, Arg.imm 1, ()))
                        fun q10 => Expr.let_ (Op.mk (OpCode.mul i64)
                          (Arg.var q10.fst, Arg.imm 4, ())) fun q11 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var q11.fst, ()))
                          fun q12 => Expr.let_ (Op.mk (OpCode.mul i64)
                            (Arg.var p4.fst, Arg.imm 4, ())) fun q13 =>
                          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var q13.fst, ()))
                            fun q14 => Expr.load i32 (Arg.var q14.fst) fun ld2 =>
                            Expr.store (t := i32) (Arg.var ld2) (Arg.var q12.fst)
                              (Expr.let_ (Op.mk (OpCode.add i64)
                                (Arg.var p.snd.fst, Arg.imm 2, ())) fun r1 =>
                                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p4.fst, Arg.imm 1, ()))
                                  fun r2 => Expr.jump Js.fst (Arg.var r2.fst, Arg.var r1.fst, ()))))
                  (Expr.jump Js.fst (Arg.var p4.fst, Arg.var p.snd.fst, ()))))
          (Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun pk =>
            Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64) (Arg.var pk.fst, Arg.var oend_v, ()))
              fun pk1 => Expr.jnz (Arg.var pk1.fst)
              (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pk.fst, Arg.imm 4, ())) fun pk2 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var pk2.fst, ()))
                  fun pk3 => Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var pk3.fst)
                  (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk.fst, Arg.imm 1, ())) fun pk4 =>
                    Expr.jump Js.fst (Arg.var pk4.fst, ())))
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ot, ())) fun w4 =>
                Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun w5 =>
                Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var w4.fst, Arg.var w5.fst, ())) fun w6 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var w6.fst, Arg.imm 1, ())) fun w7 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var w7.fst, Arg.imm 4, ())) fun w8 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWvec, Arg.var w8.fst, ())) fun w9 =>
                Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var p.snd.fst, Arg.var ooff_v, ()))
                  fun w10 => Expr.let_ (Op.mk (OpCode.trunc 64 32) (Arg.var w10.fst, ()))
                  fun w11 => Expr.store (t := i32) (Arg.var w11.fst) (Arg.var w9.fst)
                  (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun u1 =>
                    Expr.load i64 (Arg.var u1.fst) fun ldu =>
                    Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var oend_v, Arg.var p.snd.fst, ()))
                      fun u2 => Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var ldu, Arg.var u2.fst, ())) fun u3 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun u4 =>
                      Expr.store (t := i64) (Arg.var u3.fst) (Arg.var u4.fst)
                        (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                          Expr.jump Jc2 ()) Blocks.nil) fun Js =>
                          Expr.jnz (Arg.var p.snd.snd.fst)
                            (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 504, ()))
                              fun n1 => Expr.load i64 (Arg.var n1.fst) fun ldn =>
                              Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64)
                                (Arg.var ldn, Arg.imm 0, ())) fun n2 =>
                              Expr.jnz (Arg.var n2.fst)
                                (Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var c.hdr, Arg.imm 504, ())) fun n3 =>
                                  Expr.load i64 (Arg.var n3.fst) fun ldn2 =>
                                  Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var ldn2, Arg.imm 1, ()))
                                    fun n4 => Expr.let_ (Op.mk (OpCode.add i64)
                                      (Arg.var c.hdr, Arg.imm 504, ())) fun n5 =>
                                    Expr.store (t := i64) (Arg.var n4.fst) (Arg.var n5.fst)
                                      (Expr.jump Js.fst ()))
                                (Expr.jump Js.fst ()))
                            (Expr.jump Js.fst ()))))) Blocks.nil)
            fun Js => Expr.jump Js.fst (Arg.var p.snd.fst, ()))) Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.var ooff_v, Arg.var ooff_v, Arg.imm false, ()))
      m := by
  have hcl1 := hinv1.1.core_ok; have hwm1 := hinv1.2.1.watches; unfold ModeWatchesInv at hwm1
  rw [ite_eq_right (fun h0 => hinv1.2.2.2.2.2.2 h0)] at hwm1
  have hwc := c.hwcap; unfold dimacsBound at hwc
  let ooff := fullWatchOff s1 ot.toNat; let osz := fullWatchSize s1 ot.toNat; let oend := ooff + osz
  have hbd_ot := hwm1.layout.bounds ot.toNat hot_lt
  have hwlen_le1 := hcl1.wlen_le; have hwstk_len1 := hcl1.wstk_len_arr
  have hoend_le : oend ≤ s1.core.wstk.length := by
    dsimp only [oend, ooff, osz]; rw [hwstk_len1]; exact Nat.le_trans hbd_ot hwlen_le1
  have hoend_cap : oend ≤ c.wcap := hwstk_len1 ▸ hoend_le
  have hoend_lt64 : oend < 2 ^ 64 := by omega
  have hosz_lt32 : osz < 2 ^ 32 := by
    unfold osz fullWatchSize fullWatchSizeCore; exact BitVec.isLt _
  have hooff_bv : ooff_v.toNat = ooff := by
    rw [hooff_v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hoend_bv : oend_v.toNat = oend := by
    rw [hoend_v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoend_lt64]
  have hslice_ot := hwm1.slices ot.toNat hot_lt
  refine wp_while_state (ts := [i64, i64, .bool])
    (proj := fun p : BitVec 64 × BitVec 64 × Bool => (p.1, p.2.1, p.2.2, ()))
    (μ := fun p => oend - p.1.toNat)
    (Inv := fun (op, oq, _orem) mop => ooff ≤ oq.toNat ∧ oq.toNat ≤ op.toNat ∧
      op.toNat ≤ oend ∧ ∃ wstkL : List (BitVec 32), wstkL.length = c.wcap ∧
        (∀ i, i < ooff ∨ op.toNat ≤ i → wstkL[i]? = s1.core.wstk[i]?) ∧
        DenseWatchSliceOk F_cur { s1.core with wstk := wstkL } ot.toNat ooff (oq.toNat - ooff) ∧
        DenseWatchSliceOk F_cur s1.core ot.toNat op.toNat (oend - op.toNat) ∧
        (FullMem c { s1 with core := { s1.core with wstk := wstkL } } ⋆ R) mop) ?_ ?_
  · intro J1 hJ1; c0_hsteps!
    refine hJ1 (ooff_v, ooff_v, false) _ ⟨by rw [hooff_bv]; exact le_refl _,
      by rw [hooff_bv]; exact le_refl _, by rw [hooff_bv]; omega,
      s1.core.wstk, hwstk_len1, fun _ _ => rfl, ?_, ?_, hm1⟩
    · rw [hooff_bv, Nat.sub_self]; exact .empty
    · rw [hooff_bv]; change DenseWatchSliceOk F_cur s1.core ot.toNat ooff ((ooff + osz) - ooff)
      rw [Nat.add_sub_cancel_left]; exact hslice_ot
  · rintro J1 ⟨op, oq, orem⟩ mop
      ⟨hooff_oq, hoq_op, hop_end, wstkL, hwlL, houtL, hsl_pre, hsl_suf, hmop⟩ ih1
    c0_hsplit
    · have hop_lt : op.toNat < oend := by rw [← hoend_bv]; exact hc
      have hop_bd : op.toNat < wstkL.length := by rw [hwlL]; omega
      have hop1 : (op + 1#64).toNat = op.toNat + 1 := by bv_omega
      let ow := wstkL[op.toNat]'hop_bd
      have how_s : s1.core.wstk[op.toNat]? = some ow := by
        have hq := houtL op.toNat (Or.inr (le_refl _)); rw [← hq, List.getElem?_eq_getElem hop_bd]
      c0_hsteps_nogrp
      refine wp_unroll_group fun Jbin hJbin => ?_
      c0_hsplit
      · have how_bin : (ow &&& 0x80000000#32) ≠ 0#32 := by
          rw [show (0x80000000#32 : BitVec 32) = (2147483648 : BitVec 32) from rfl]
          dsimp only [ow]; exact hc
        obtain ⟨how_ne, how_lt, hent_ow, hsl_suf1⟩ :=
          m6_denseSlice_step_bin hsl_suf (by omega) how_s how_bin
        have hoq_bd : oq.toNat < wstkL.length := by rw [hwlL]; omega
        have hoq1 : (oq + 1#64).toNat = oq.toNat + 1 := by bv_omega
        let wstkL' := wstkL.set oq.toNat ow
        have hsl_pre' : DenseWatchSliceOk F_cur { s1.core with wstk := wstkL' }
            ot.toNat ooff (oq.toNat + 1 - ooff) := by
          rw [show oq.toNat + 1 - ooff = (oq.toNat - ooff) + 1 by omega]
          refine DenseWatchSliceOk.append_bin (k := { s1.core with wstk := wstkL })
            (k' := { s1.core with wstk := wstkL' }) (le_refl _) (fun _ r => r)
            (fun idx hidx => by simp only [wstkL']; rw [List.getElem?_set_ne (by omega)])
            hsl_pre ?_ how_bin how_ne how_lt hent_ow
          simp only [wstkL']
          rw [show ooff + (oq.toNat - ooff) = oq.toNat by omega, List.getElem?_set_self hoq_bd]
        have hkeep : ∀ (orem' : Bool) (m' : Mem 64),
            (FullMem c { s1 with core := { s1.core with wstk := wstkL' } } ⋆ R) m' →
            J1 (op + 1#64, oq + 1#64, orem', ()) m' := fun orem' m' hm' =>
          ih1 (op + 1#64, oq + 1#64, orem') m' (by dsimp only; rw [hop1]; omega)
            ⟨by rw [hoq1]; omega, by rw [hoq1, hop1]; omega, by rw [hop1]; omega, wstkL',
             by rw [List.length_set, hwlL], fun i hi => by
               simp only [wstkL']; rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega)]
               exact houtL i (Or.imp (fun _ => by omega) (fun _ => by omega) hi),
             by rw [hoq1]; exact hsl_pre', by
               rw [hop1, show oend - (op.toNat + 1) = oend - op.toNat - 1 by omega]; exact hsl_suf1,
             hm'⟩
        refine wp_unroll_group fun Jrem hJrem => ?_
        c0_hsteps!
        all_goals first
          | exact hkeep _ _ (by assumption)
          | exact ih1 (op + 1#64, oq, true) _ (by dsimp only; rw [hop1]; omega)
              ⟨hooff_oq, by rw [hop1]; omega, by rw [hop1]; omega, wstkL, hwlL,
               (fun i hi => houtL i (Or.imp (fun _ => by omega) (fun _ => by omega) hi)),
               hsl_pre, by rw [hop1, show oend - (op.toNat + 1) = oend - op.toNat - 1 by omega]
                           exact hsl_suf1,
               by assumption⟩
      · have how_occ : (ow &&& 0x80000000#32) = 0#32 := by
          rw [show (0x80000000#32 : BitVec 32) = (2147483648 : BitVec 32) from rfl]
          dsimp only [ow]; exact hc
        obtain ⟨hrem2, hsz3, cr_w, hcr_s, hcr_lt, hcr_ref, hsl_suf2⟩ :=
          m6_denseSlice_step_occ hsl_suf (by omega) how_s how_occ
        have hop1_lt : (op + 1#64).toNat < oend := by rw [hop1]; omega
        have hop2 : (op + 1#64 + 1#64).toNat = op.toNat + 2 := by bv_omega
        have hop1_bd : (op + 1#64).toNat < wstkL.length := by rw [hwlL]; omega
        have hoq_bd : oq.toNat < wstkL.length := by rw [hwlL]; omega
        have hoq1 : (oq + 1#64).toNat = oq.toNat + 1 := by bv_omega
        have hoq2 : (oq + 2#64).toNat = oq.toNat + 2 := by bv_omega
        have hcr_L : wstkL[(op + 1#64).toNat]'hop1_bd = cr_w := by
          have h1 := houtL (op.toNat + 1) (Or.inr (by omega))
          rw [← hop1, List.getElem?_eq_getElem hop1_bd] at h1
          rw [← hop1] at hcr_s; exact Option.some.inj (h1.trans hcr_s)
        have hmem_occ : (wstkL.set oq.toNat ow)[(op + 1#64).toNat]'(by
            rw [List.length_set]; exact hop1_bd) = cr_w := by
          rw [List.getElem_set_ne (by rw [hop1]; omega)]; exact hcr_L
        let wstkL' := (wstkL.set oq.toNat ow).set (oq.toNat + 1) cr_w
        have hsl_pre' : DenseWatchSliceOk F_cur { s1.core with wstk := wstkL' }
            ot.toNat ooff (oq.toNat + 2 - ooff) := by
          rw [show oq.toNat + 2 - ooff = (oq.toNat - ooff) + 2 by omega]
          refine DenseWatchSliceOk.append_occ (k := { s1.core with wstk := wstkL })
            (k' := { s1.core with wstk := wstkL' }) (le_refl _) (fun _ r => r) (fun idx hidx => by
              simp only [wstkL']
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
            hsl_pre ?_ ?_ how_occ hsz3 hcr_lt hcr_ref
          · simp only [wstkL']; rw [show ooff + (oq.toNat - ooff) = oq.toNat by omega,
              List.getElem?_set_ne (by omega), List.getElem?_set_self hoq_bd]
          · simp only [wstkL']; rw [show ooff + (oq.toNat - ooff) + 1 = oq.toNat + 1 by omega,
              List.getElem?_set_self (by rw [List.length_set, hwlL]; omega)]
        have hwstk_eq : (wstkL.set oq.toNat (wstkL[op.toNat]'hop_bd)).set
            (oq + (1 : BitVec 64)).toNat ((wstkL.set oq.toNat
              (wstkL[op.toNat]'hop_bd))[(op + (1 : BitVec 64)).toNat]'(by
              rw [List.length_set]; exact hop1_bd)) = wstkL' := by
          have hoq1' : (oq + (1 : BitVec 64)).toNat = oq.toNat + 1 := hoq1
          have hmem' : (wstkL.set oq.toNat (wstkL[op.toNat]'hop_bd))[(op +
              (1 : BitVec 64)).toNat]'(by rw [List.length_set]; exact hop1_bd) = cr_w := hmem_occ
          simp only [wstkL', ow]; rw [hoq1', hmem']
        c0_hsteps!
        exact ih1 (op + 1#64 + 1#64, oq + 2#64, orem) _ (by dsimp only; rw [hop2]; omega)
          ⟨by rw [hoq2]; omega, by rw [hoq2, hop2]; omega, by rw [hop2]; omega,
           wstkL', by rw [List.length_set, List.length_set, hwlL], fun i hi => by
             simp only [wstkL']; rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega),
               List.getElem?_set_ne (by rcases hi with h | h <;> omega)]
             exact houtL i (Or.imp (fun _ => by omega) (fun _ => by omega) hi),
           by rw [hoq2]; exact hsl_pre', by
             rw [hop2, show oend - (op.toNat + 2) = oend - op.toNat - 2 by omega]; exact hsl_suf2,
           by dsimp only at hm ⊢; rwa [← hwstk_eq]⟩
    · have hop_eq : op.toNat = oend := by
        have hge : oend_v.toNat ≤ op.toNat := Nat.le_of_not_lt hc; rw [hoend_bv] at hge; omega
      rw [hop_eq] at houtL; clear hsl_suf hslice_ot hwm1 hbd_ot; c0_hsteps_nogrp
      refine wp_while_state (ts := [i64]) (proj := fun ok : BitVec 64 => (ok, ()))
        (μ := fun ok => oend - ok.toNat)
        (Inv := fun ok mok => oq.toNat ≤ ok.toNat ∧ ok.toNat ≤ oend ∧
          ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
            (∀ i, i < ooff ∨ oend ≤ i → wstkK[i]? = s1.core.wstk[i]?) ∧
            (∀ i, ooff ≤ i → i < oq.toNat → wstkK[i]? = wstkL[i]?) ∧
            (FullMem c { s1 with core := { s1.core with wstk := wstkK } } ⋆ R) mok) ?_ ?_
      · intro J2 hJ2; c0_hsteps!
        exact hJ2 oq _ ⟨le_refl _, by omega, wstkL, hwlL, houtL, fun _ _ _ => rfl, hmop⟩
      · rintro J2 ok mok ⟨hok_lo, hok_hi, wstkK, hwlK, houtK, hpreK, hmok⟩ ih2
        c0_hsplit
        · have hok_lt : ok.toNat < oend := by rw [← hoend_bv]; exact hc
          have hok_bd : ok.toNat < wstkK.length := by rw [hwlK]; omega
          have hok1 : (ok + 1#64).toNat = ok.toNat + 1 := by bv_omega
          let wstkK' := wstkK.set ok.toNat 0xFFFFFFFF#32; c0_hsteps!
          exact ih2 (ok + 1#64) _ (by rw [hok1]; omega)
            ⟨by rw [hok1]; omega, by rw [hok1]; omega, wstkK', by rw [List.length_set, hwlK],
             fun i hi => by
               simp only [wstkK']; rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega)]
               exact houtK i hi,
             fun i hi1 hi2 => by
               simp only [wstkK']; rw [List.getElem?_set_ne (by omega)]; exact hpreK i hi1 hi2,
             by assumption⟩
        · let newSz := oq.toNat - ooff
          have hle_oq : oq.toNat ≤ oend := Nat.le_trans hok_lo hok_hi
          have hle_sz : newSz ≤ osz := by omega
          have hnew_c0 : (oq - ooff_v).setWidth 32 = BitVec.ofNat 32 newSz := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_sub, hooff_bv, BitVec.toNat_ofNat]
            have hlt32 : newSz < 2 ^ 32 := Nat.lt_of_le_of_lt hle_sz hosz_lt32
            rw [show (2 ^ 64 - ooff + oq.toNat) % 2 ^ 64 = newSz by omega,
              Nat.mod_eq_of_lt hlt32]
          have hwu_c0 : oend_v - oq = BitVec.ofNat 64 (oend - oq.toNat) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sub, hoend_bv, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : oend - oq.toNat < 2 ^ 64)]; omega
          have h2ot1_c0 : (ot.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * ot.toNat + 1 := by
            rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
              show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have h2ot1_bd : (ot.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s1.core.wvec.length := by
            have := hcl1.cur_vars_le; rw [h2ot1_c0, hcl1.wvec_len]; omega
          have hslK : DenseWatchSliceOk F_cur { s1.core with wstk := wstkK } ot.toNat ooff
              newSz := DenseWatchSliceOk.relocate (k := { s1.core with wstk := wstkL })
              (k' := { s1.core with wstk := wstkK })
              (by rw [CNF.entails_def]; exact fun _ h => h) (le_refl _) (fun _ r => r)
              (fun idx hidx => hpreK (ooff + idx) (by omega) (by omega)) hsl_pre
          have hinv_k : ∀ (wu' nb' : BitVec 64), FullDenseInvW c F0 F_cur
                { s1 with core := { s1.core with
                    wvec := s1.core.wvec.set (2 * ot.toNat + 1) (BitVec.ofNat 32 newSz),
                    wstk := wstkK, wusable := wu', num_binary := nb' } } := fun wu' nb' =>
            m6_denseInvW_watchCompact hinv1 hot_lt hle_sz hwlK houtK hslK wu' nb'
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun () mf => ∃ nb' : BitVec 64,
              (FullMem c { s1 with core := { s1.core with
                  wvec := s1.core.wvec.set (2 * ot.toNat + 1) (BitVec.ofNat 32 newSz),
                  wstk := wstkK, wusable := s1.core.wusable + BitVec.ofNat 64 (oend - oq.toNat),
                  num_binary := nb' } } ⋆ R) mf) ?_ ?_
          · rintro _ ⟨⟩ mf ⟨nb', hmf⟩; c0_hsteps!
            exact hCont _ _ _ _ mf (hinv_k _ nb') hmf
          · intro Jnb hJnb; c0_hsplit
            · c0_hsplit
              · c0_hsteps!; refine hJnb () _ ⟨s1.core.num_binary - 1#64, ?_⟩
                rw [← h2ot1_c0, ← hnew_c0, ← hwu_c0]; assumption
              · c0_hsteps!; refine hJnb () _ ⟨s1.core.num_binary, ?_⟩
                rw [← h2ot1_c0, ← hnew_c0, ← hwu_c0]; assumption
            · c0_hsteps!; refine hJnb () _ ⟨s1.core.num_binary, ?_⟩
              rw [← h2ot1_c0, ← hnew_c0, ← hwu_c0]; assumption

private theorem m6_els_wvec_pop_eq {k : Nat} (sL : FullState) (l : BitVec 32) {offL szL : Nat}
    (hk_le : k ≤ szL) (hk_lt : k < 2 ^ 64) (hoff_lt : offL + k < 2 ^ 32) (hsz_lt : szL < 2 ^ 32)
    (h2l0_c0 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat = 2 * l.toNat)
    (h2l1_c0 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1)
    {h0 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat < sL.core.wvec.length}
    {h1 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat < sL.core.wvec.length}
    (hoffL_bv :
      (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'h0)).toNat =
        offL)
    (hszL_bv :
      (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) +
        (1 : BitVec 64)).toNat]'h1)).toNat = szL) :
    (sL.core.wvec.set (BitVec.setWidth 64 l <<< (1 : Nat)).toNat (BitVec.setWidth 32
        (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'h0) +
          BitVec.ofNat 64 k))).set
      (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat
      (BitVec.setWidth 32 (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) +
        (1 : BitVec 64)).toNat]'h1) - BitVec.ofNat 64 k)) =
    (sL.core.wvec.set (2 * l.toNat) (BitVec.ofNat 32 (offL + k))).set
      (2 * l.toNat + 1) (BitVec.ofNat 32 (szL - k)) := by
  have hoff64 : offL < 2 ^ 64 := by omega
  have hsz64 : szL < 2 ^ 64 := by omega
  refine m6_list_set2_eq sL.core.wvec h2l0_c0 h2l1_c0 ?_ ?_
  · apply BitVec.eq_of_toNat_eq
    have hv : BitVec.setWidth 64 (sL.core.wvec[_]'h0) = BitVec.ofNat 64 offL :=
      BitVec.eq_of_toNat_eq (by rw [hoffL_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64])
    rw [hv, BitVec.toNat_setWidth, show (BitVec.ofNat 64 offL + BitVec.ofNat 64 k).toNat =
      offL + k by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hk_lt, Nat.mod_eq_of_lt (by omega)],
      BitVec.toNat_ofNat]
  · apply BitVec.eq_of_toNat_eq
    have hv : BitVec.setWidth 64 (sL.core.wvec[_]'h1) = BitVec.ofNat 64 szL :=
      BitVec.eq_of_toNat_eq (by rw [hszL_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz64])
    rw [hv, BitVec.toNat_setWidth, show (BitVec.ofNat 64 szL - BitVec.ofNat 64 k).toNat =
      szL - k by rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hsz64, Nat.mod_eq_of_lt hk_lt]; omega,
      BitVec.toNat_ofNat]

private theorem m6_call_els_ar {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hElsAr : Γ.Has "full_m6_els_ar" fullM6ElsArSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s1 : FullState}
    {cr rl : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [.bool] → Expr Val Cont rs}
    (hfr : M6ElsFrame c F0 F_cur s s1) (hcr : cr.toNat ∈ fullArenaClauseRefs s1)
    (hrl : rl.toNat < 2 * s1.core.cur_vars) (hm : (FullMem c s1 ⋆ R) m)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      M6ElsFrame c F0 F_cur s s' →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_m6_els_ar"
        (Arg.var c.hdr, Arg.var cr, Arg.var rl, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hElsAr (c.hdr, cr, rl, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, F0, F_cur, s1, R, rfl, hfr.dinv, hcr, hrl, hfr.cv.symm ▸ hfr.repr, hm, ?_⟩
  intro ok s' m' hinv' hcv' hfl' hrepr' htmk' htrh' hscr' hws1' hws2' hgu' hfail' hm'
  exact hk ok s' m'
    ⟨hinv', hcv'.trans hfr.cv, hfl'.trans hfr.fuel, hfr.cv ▸ hrepr',
     htmk'.trans hfr.tmk, htrh'.trans hfr.trh, hscr'.trans hfr.scr,
     hws1'.trans hfr.ws1, hws2'.trans hfr.ws2, hgu'.trans hfr.gu⟩ hfail' hm'

theorem full_m6_els_lit_wp (Γ : Env)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec)
    (hElsAr : Γ.Has "full_m6_els_ar" fullM6ElsArSpec) :
    ∀ args m Q X, fullM6ElsLitSpec args m Q X →
      Func.wp Γ full_m6_els_lit_body args m Q X := by
  rintro ⟨h, l, rl, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hl_lt, hrl_lt, hlr_eq, hrepr_inv, hm, hQ⟩
  have hcl := hinv.1.core_ok; have hmx := c.hmaxv; have hwc := c.hwcap
  unfold dimacsBound at hmx hwc
  have hcv_le := hcl.cur_vars_le
  have h2l_bd : 2 * l.toNat + 1 < s.core.wvec.length := by rw [hcl.wvec_len]; omega
  have h2l_c0 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat =
      2 * l.toNat + 1 := by
    rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
      show ((1 : BitVec 64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have h2l_bd64 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat <
      s.core.wvec.length := h2l_c0 ▸ h2l_bd
  unfold Func.wp full_m6_els_lit_body
  c0_hsteps_nogrp
  refine wp_while_break_state (brkTs := [i64]) (lpTs := [i64]) (β := BitVec 64 × FullState)
    (fun p => (p.1, ())) (fun p mB => M6ElsFrame c F0 F_cur s p.2 ∧ (FullMem c p.2 ⋆ R) mB)
    (α := BitVec 64 × FullState) (fun p => (p.1, ())) (fun p => p.1.toNat)
    (fun p ml => M6ElsFrame c F0 F_cur s p.2 ∧ (FullMem c p.2 ⋆ R) ml) ?_ ?_ ?_
  · rintro B ⟨_, sB⟩ mB ⟨hB, hmB⟩; c0_hsteps!; exact m6_els_frame_exit hB hmB hQ
  · rintro B L ⟨gL, sL⟩ ml hB hL ⟨hLoop, hmL⟩
    dsimp only at *
    have hinvL := hLoop.dinv; have hclL := hinvL.1.core_ok; have hwL := hinvL.2.1
    have hcvL_le := hclL.cur_vars_le
    have hl_ltL : l.toNat < 2 * sL.core.cur_vars := hLoop.cv ▸ hl_lt
    have h2l_bdL : 2 * l.toNat + 1 < sL.core.wvec.length := by rw [hclL.wvec_len]; omega
    have h2l_bdL64 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat <
        sL.core.wvec.length := h2l_c0 ▸ h2l_bdL
    have h2l_mod : (2 * l.toNat + 1) % 2 ^ 64 = 2 * l.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    have hg_pos : 0 < gL.toNat := by bv_omega
    have h2l_c0_m : (l.toNat * 2 ^ OfNat.ofNat 1 + (1 : BitVec 64).toNat) % 2 ^ 64 =
        2 * l.toNat + 1 := by
      change (l.toNat * 2 ^ 1 + 1) % 2 ^ 64 = _; rw [Nat.pow_one, Nat.mul_comm]
      exact Nat.mod_eq_of_lt (by omega)
    have hsz_pos : 0 < fullWatchSize sL l.toNat := by
      unfold fullWatchSize fullWatchSizeCore
      rw [List.getElem?_eq_getElem h2l_bdL, Option.getD_some]
      have hpc : 0 % 2 ^ 32 < (sL.core.wvec[(l.toNat * 2 ^ OfNat.ofNat 1 +
          (1 : BitVec 64).toNat) % 2 ^ 64]'(by rw [h2l_c0_m]; exact h2l_bdL)).toNat := by assumption
      rw [m6_list_getElem_congr h2l_c0_m (by rw [h2l_c0_m]; exact h2l_bdL) h2l_bdL] at hpc
      exact hpc
    have hwmL := hwL.watches; unfold ModeWatchesInv at hwmL
    rw [ite_eq_right (fun h0 => hinvL.2.2.2.2.2.2 h0)] at hwmL
    have hbd_l := hwmL.layout.bounds l.toNat hl_ltL
    have hslice_l := hwmL.slices l.toNat hl_ltL
    let offL := fullWatchOff sL l.toNat; let szL := fullWatchSize sL l.toNat
    have hoff_def : offL = fullWatchOffCore sL.core l.toNat := rfl
    have hsz_def : szL = fullWatchSizeCore sL.core l.toNat := rfl
    have hoffL_lt : offL < sL.core.wstk.length := by
      have := hclL.wstk_len_arr; have := hclL.wlen_le; rw [hoff_def]; omega
    have h2l0_c0 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat = 2 * l.toNat := by
      rw [m6_els_bv64_shl1_nat, bv_c0_zext32_64, Nat.mod_eq_of_lt (by omega)]
    have h2l0_bdL64 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat < sL.core.wvec.length := by
      rw [h2l0_c0, hclL.wvec_len]; omega
    have h2l1_c0 := h2l_c0
    have hoffL_bv : (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'
        (by rw [h2l0_c0, hclL.wvec_len]; omega))).toNat = offL := by
      rw [bv_c0_zext32_64, m6_list_getElem_congr h2l0_c0
        (by rw [h2l0_c0, hclL.wvec_len]; omega) (by rw [hclL.wvec_len]; omega)]
      unfold offL fullWatchOff fullWatchOffCore
      rw [List.getElem?_eq_getElem (by rw [hclL.wvec_len]; omega), Option.getD_some]
    have hszL_bv : (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) +
        (1 : BitVec 64)).toNat]'(by rw [h2l1_c0, hclL.wvec_len]; omega))).toNat = szL := by
      rw [bv_c0_zext32_64, m6_list_getElem_congr h2l1_c0
        (by rw [h2l1_c0, hclL.wvec_len]; omega) h2l_bdL]
      unfold szL fullWatchSize fullWatchSizeCore
      rw [List.getElem?_eq_getElem h2l_bdL, Option.getD_some]
    have hws_off_lt : (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'
        (by rw [h2l0_c0, hclL.wvec_len]; omega))).toNat < sL.core.wstk.length := by
      rw [hoffL_bv]; exact hoffL_lt
    have hw0_c0_eq : ∀ (h1 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat < sL.core.wvec.length)
        (h2 : (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'
          h1)).toNat < sL.core.wstk.length),
        sL.core.wstk[(BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'
          h1)).toNat]'h2 = sL.core.wstk[offL]'hoffL_lt :=
      fun _ h2 => m6_list_getElem_congr hoffL_bv h2 hoffL_lt
    have hg1 : (gL - 1#64).toNat = gL.toNat - 1 := by bv_omega
    have h2l0_c0_m : (l.toNat * 2 ^ OfNat.ofNat 1) % 2 ^ 64 = 2 * l.toNat := by
      change (l.toNat * 2 ^ 1) % 2 ^ 64 = _; rw [Nat.pow_one, Nat.mul_comm]
      exact Nat.mod_eq_of_lt (by omega)
    have h2l0_bdL : 2 * l.toNat < sL.core.wvec.length := by rw [hclL.wvec_len]; omega
    have hwv0_m_eq : (sL.core.wvec[(l.toNat * 2 ^ OfNat.ofNat 1) % 2 ^ 64]'(by
        rw [h2l0_c0_m]; exact h2l0_bdL)).toNat = offL := by
      rw [m6_list_getElem_congr h2l0_c0_m (by rw [h2l0_c0_m]; exact h2l0_bdL) h2l0_bdL]
      unfold offL fullWatchOff fullWatchOffCore
      rw [List.getElem?_eq_getElem h2l0_bdL, Option.getD_some]
    have hw0_m_eq : sL.core.wstk[(sL.core.wvec[(l.toNat * 2 ^ OfNat.ofNat 1) % 2 ^ 64]'(by
        rw [h2l0_c0_m]; exact h2l0_bdL)).toNat]'(hwv0_m_eq.symm ▸ hoffL_lt) =
        sL.core.wstk[offL]'hoffL_lt :=
      m6_list_getElem_congr hwv0_m_eq (hwv0_m_eq.symm ▸ hoffL_lt) hoffL_lt
    have hwstk_len_L := hclL.wstk_len_arr; have hwlen_le_L := hclL.wlen_le
    c0_hsplit
    · -- Binary watch
      have hw0_some : sL.core.wstk[offL]? = some (sL.core.wstk[offL]'hoffL_lt) :=
        List.getElem?_eq_getElem hoffL_lt
      have hw0_bin : (sL.core.wstk[offL]'hoffL_lt &&& 0x80000000#32) ≠ 0#32 := by
        rw [← hw0_m_eq]; exact hc
      obtain ⟨_, hot_lt, hent_bin, hsl_nxt⟩ :=
        m6_denseSlice_step_bin hslice_l hsz_pos hw0_some hw0_bin
      let ot := sL.core.wstk[offL]'hoffL_lt &&& 0x7FFFFFFF#32
      have hot_lt_s : ot.toNat < 2 * sL.core.cur_vars := hot_lt
      have hent_rep : (cnfOfClauses F_cur).EntailsClause (cnfClause [rl.toNat, ot.toNat]) :=
        m6_entails_bin_subst hlr_eq (m6_litEquiv_refl _ _) hent_bin
      let wvec1 := (sL.core.wvec.set (2 * l.toNat) (BitVec.ofNat 32 (offL + 1))).set
        (2 * l.toNat + 1) (BitVec.ofNat 32 (szL - 1))
      obtain ⟨s1, hs1_def⟩ : ∃ s1 : FullState, s1 = { sL with core := { sL.core with
          wvec := wvec1, wusable := sL.core.wusable + 1#64 } } := ⟨_, rfl⟩
      have hinv1 : FullDenseInvW c F0 F_cur s1 :=
        hs1_def.symm ▸ m6_denseInvW_watchPop hinvL hl_ltL (by omega : 1 ≤ szL)
          (sL.core.wusable + 1#64) hsl_nxt
      have hfr1 : M6ElsFrame c F0 F_cur s s1 :=
        ⟨hinv1, hs1_def.symm ▸ hLoop.cv, hs1_def.symm ▸ hLoop.fuel, hs1_def.symm ▸ hLoop.repr,
         hs1_def.symm ▸ hLoop.tmk, hs1_def.symm ▸ hLoop.trh, hs1_def.symm ▸ hLoop.scr,
         hs1_def.symm ▸ hLoop.ws1, hs1_def.symm ▸ hLoop.ws2, hs1_def.symm ▸ hLoop.gu⟩
      have hsz_lt32 : szL < 2 ^ 32 := by
        unfold szL fullWatchSize fullWatchSizeCore; exact BitVec.isLt _
      have hwv_pop1 := m6_els_wvec_pop_eq (k := 1) sL l (by omega) (by decide) (by omega) hsz_lt32
        h2l0_c0 h2l1_c0 hoffL_bv hszL_bv
      have h2l_set1 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat <
          (sL.core.wvec.set (BitVec.setWidth 64 l <<< (1 : Nat)).toNat
            (BitVec.setWidth 32 (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
              (1 : Nat)).toNat]'h2l0_bdL64) + (1 : BitVec 64)))).length := by
        rw [List.length_set]; exact h2l_bdL64
      c0_hsteps_nogrp
      have hpop1_m : (FullMem c s1 ⋆ R) m := by
        rw [hs1_def]; dsimp only [wvec1]; rw [← hwv_pop1]; assumption
      let ot_c0 := sL.core.wstk[(BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
        (1 : Nat)).toNat]'(by rw [h2l0_c0, hclL.wvec_len]; omega))).toNat]'hws_off_lt &&&
        (2147483647 : BitVec 32)
      have hot_c0_eq : ot_c0 = ot := by dsimp only [ot_c0, ot]; rw [hw0_c0_eq]; rfl
      refine wp_join_group (ts := []) (fun () mC =>
          ∃ sC : FullState, M6ElsFrame c F0 F_cur s sC ∧ (FullMem c sC ⋆ R) mC) ?_ ?_
      · rintro _ ⟨⟩ mC ⟨sC, hfrC, hmC⟩
        c0_hsplit
        · c0_hsteps!; exact hL (gL - 1#64, sC) mC (by dsimp only; omega) ⟨hfrC, hmC⟩
        c0_hsplit
        · c0_hsteps!; exact hL (gL - 1#64, sC) mC (by dsimp only; omega) ⟨hfrC, hmC⟩
        c0_hsplit
        · have hrr : rl = ot := by dsimp only [ot]; rw [← hw0_m_eq]; exact hc
          have hent_u : (cnfOfClauses F_cur).EntailsClause (cnfClause [rl.toNat]) :=
            m6_entails_unit_of_dup (hrr ▸ hent_rep)
          c0_hsteps_nogrp
          refine m6_call_add_unit hAddUnit hfrC (hfrC.cv.symm ▸ hrl_lt) hent_u hmC
            fun okU sU mU hfrU _ hfail hmU => ?_
          c0_hsplit
          · c0_hsteps!; exact hL (gL - 1#64, sU) mU (by dsimp only; omega) ⟨hfrU, hmU⟩
          · have hokf : okU = false := by
              cases okU <;> first | rfl | contradiction | exact absurd rfl ‹_›
            c0_hsteps!
            exact hQ false sU mU hfrU.dinv hfrU.cv hfrU.fuel hfrU.repr hfrU.tmk hfrU.trh
              hfrU.scr hfrU.ws1 hfrU.ws2 hfrU.gu (fun _ => hfail hokf) hmU
        · c0_hsteps_nogrp
          refine m6_call_add_bin hAddBin hfrC (by
              dsimp only [Prod.fst]
              change (cnfOfClauses F_cur).EntailsClause (cnfClause [rl.toNat, ot_c0.toNat])
              rw [hot_c0_eq]; exact hent_rep) hmC
            fun rB sB mB hfrB hr20 hmB => ?_
          c0_hsplit
          · have hrB : rB = 20#64 := by bv_omega
            c0_hsteps!
            exact hQ false sB mB hfrB.dinv hfrB.cv hfrB.fuel hfrB.repr hfrB.tmk hfrB.trh
              hfrB.scr hfrB.ws1 hfrB.ws2 hfrB.gu (fun _ => hr20 hrB) hmB
          c0_hsplit
          · c0_hsteps!
            have hfrBo := hfrB.set_oom
            exact hQ true _ _ hfrBo.dinv hfrBo.cv hfrBo.fuel hfrBo.repr hfrBo.tmk hfrBo.trh
              hfrBo.scr hfrBo.ws1 hfrBo.ws2 hfrBo.gu (fun h => Bool.noConfusion h) (by assumption)
          · c0_hsteps!; exact hL (gL - 1#64, sB) mB (by dsimp only; omega) ⟨hfrB, hmB⟩
      · intro Jc hJc
        have hcl1 := hinv1.1.core_ok
        have hcv1_eq : s1.core.cur_vars = s.core.cur_vars := hfr1.cv
        have hwm1 := hinv1.2.1.watches; unfold ModeWatchesInv at hwm1
        rw [ite_eq_right (fun h0 => hinv1.2.2.2.2.2.2 h0)] at hwm1
        have hot_lt1 : ot.toNat < 2 * s1.core.cur_vars := by
          rw [hcv1_eq, ← hLoop.cv]; exact hot_lt_s
        have h2ot0_wvec : 2 * ot.toNat < s1.core.wvec.length := by rw [hcl1.wvec_len]; omega
        have h2ot1_wvec : 2 * ot.toNat + 1 < s1.core.wvec.length := by rw [hcl1.wvec_len]; omega
        have h2ot0_eq : (ot.setWidth 64 <<< (1 : Nat)).toNat = 2 * ot.toNat := by
          rw [m6_els_bv64_shl1_nat, bv_c0_zext32_64, Nat.mod_eq_of_lt (by omega)]
        have h2ot1_eq : (ot.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat =
            2 * ot.toNat + 1 := by
          rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
            show ((1 : BitVec 64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        have h2ot0_bd : (ot.setWidth 64 <<< (1 : Nat)).toNat < s1.core.wvec.length :=
          h2ot0_eq ▸ h2ot0_wvec
        have h2ot1_bd : (ot.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat <
            s1.core.wvec.length := h2ot1_eq ▸ h2ot1_wvec
        c0_hsplit; rotate_left
        · c0_hsteps!; exact hJc () _ ⟨s1, hfr1, hpop1_m⟩
        let ooff := fullWatchOff s1 ot.toNat; let osz := fullWatchSize s1 ot.toNat
        have hooff_bv : (BitVec.setWidth 64
            (s1.core.wvec[(ot.setWidth 64 <<< (1 : Nat)).toNat]'h2ot0_bd)).toNat = ooff := by
          rw [bv_c0_zext32_64, m6_list_getElem_congr h2ot0_eq h2ot0_bd h2ot0_wvec]
          unfold ooff fullWatchOff fullWatchOffCore
          rw [List.getElem?_eq_getElem h2ot0_wvec, Option.getD_some]
        have hosz_bv : (BitVec.setWidth 64 (s1.core.wvec[(ot.setWidth 64 <<< (1 : Nat) +
            (1 : BitVec 64)).toNat]'h2ot1_bd)).toNat = osz := by
          rw [bv_c0_zext32_64, m6_list_getElem_congr h2ot1_eq h2ot1_bd h2ot1_wvec]
          unfold osz fullWatchSize fullWatchSizeCore
          rw [List.getElem?_eq_getElem h2ot1_wvec, Option.getD_some]
        have hbd_ot := hwm1.layout.bounds ot.toNat hot_lt1
        have hwlen_le1 := hcl1.wlen_le
        have hoend_lt64 : ooff + osz < 2 ^ 64 := by
          change fullWatchOffCore s1.core ot.toNat + fullWatchSizeCore s1.core ot.toNat < 2 ^ 64
          omega
        have h2ot0_bd_c0 : (ot_c0.setWidth 64 <<< (1 : Nat)).toNat < s1.core.wvec.length :=
          hot_c0_eq ▸ h2ot0_bd
        have h2ot1_bd_c0 : (ot_c0.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat <
            s1.core.wvec.length := hot_c0_eq ▸ h2ot1_bd
        have hooff_c0_eq : s1.core.wvec[(ot_c0.setWidth 64 <<< (1 : Nat)).toNat]'h2ot0_bd_c0 =
            s1.core.wvec[(ot.setWidth 64 <<< (1 : Nat)).toNat]'h2ot0_bd :=
          m6_list_getElem_congr (by rw [hot_c0_eq]) h2ot0_bd_c0 h2ot0_bd
        have hosz_c0_eq : s1.core.wvec[(ot_c0.setWidth 64 <<< (1 : Nat) +
              (1 : BitVec 64)).toNat]'h2ot1_bd_c0 =
            s1.core.wvec[(ot.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat]'h2ot1_bd :=
          m6_list_getElem_congr (by rw [hot_c0_eq]) h2ot1_bd_c0 h2ot1_bd
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun () mc =>
            ∃ sC2 : FullState, M6ElsFrame c F0 F_cur s sC2 ∧ (FullMem c sC2 ⋆ R) mc)
          (fun _ () mc ⟨sC2, hLC2, hm2⟩ => by c0_hsteps!; exact hJc () mc ⟨sC2, hLC2, hm2⟩) ?_
        intro Jc2 hJc2; c0_hsplit; rotate_left
        · c0_hsteps!; exact hJc2 () _ ⟨s1, hfr1, hpop1_m⟩
        have hosz_pos : 0 < osz := by
          have h2ot1_m : (ot.toNat * 2 ^ OfNat.ofNat 1 + (1 : BitVec 64).toNat) % 2 ^ 64 =
              2 * ot.toNat + 1 := by
            change (ot.toNat * 2 ^ 1 + 1) % 2 ^ 64 = _; rw [Nat.pow_one, Nat.mul_comm]
            exact Nat.mod_eq_of_lt (by omega)
          repeat rw [m6_getElem_eq_getD s1.core.wvec (d := 0#32)] at hc
          repeat rw [m6_getElem_eq_getD sL.core.wstk (d := 0#32)] at hc
          rw [hwv0_m_eq, List.getElem?_eq_getElem hoffL_lt, Option.getD_some,
            show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] at hc
          change 0 < (s1.core.wvec[(ot.toNat * 2 ^ OfNat.ofNat 1 +
            (1 : BitVec 64).toNat) % 2 ^ 64]?.getD 0#32).toNat at hc
          rw [h2ot1_m] at hc; exact hc
        c0_hsteps_nogrp; dsimp only [Prod.fst]
        refine m6_els_compact_ot_watches (ot := ot_c0) hinv1 (hot_c0_eq.symm ▸ hot_lt1)
          (hot_c0_eq.symm ▸ hosz_pos) ?_ ?_ hpop1_m ?_
        · apply BitVec.eq_of_toNat_eq
          rw [hooff_c0_eq, hooff_bv, hot_c0_eq, BitVec.toNat_ofNat]
          exact (Nat.mod_eq_of_lt (by omega)).symm
        · apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, hooff_c0_eq, hosz_c0_eq, hooff_bv, hosz_bv, hot_c0_eq,
            BitVec.toNat_ofNat]
        · intro _ _ _ _ mf hinv2 hmf
          exact hJc2 () mf ⟨_, ⟨hinv2, hfr1.cv, hfr1.fuel, hfr1.repr, hfr1.tmk, hfr1.trh,
            hfr1.scr, hfr1.ws1, hfr1.ws2, hfr1.gu⟩, hmf⟩
    · -- Occurrence watch
      have hw0_some : sL.core.wstk[offL]? = some (sL.core.wstk[offL]'hoffL_lt) :=
        List.getElem?_eq_getElem hoffL_lt
      have hw0_occ : (sL.core.wstk[offL]'hoffL_lt &&& 0x80000000#32) = 0#32 := by
        rw [← hw0_m_eq]; exact hc
      obtain ⟨hsz2, _, cr, hw1_some, _, hcr_ref, hsl_nxt⟩ :=
        m6_denseSlice_step_occ hslice_l hsz_pos hw0_some hw0_occ
      c0_hsplit
      · exfalso
        have hlt2 : (sL.core.wvec[(l.toNat * 2 ^ OfNat.ofNat 1 + (1 : BitVec 64).toNat) %
            2 ^ 64]'(by rw [h2l_c0_m]; exact h2l_bdL)).toNat < 2 := hc
        rw [m6_list_getElem_congr h2l_c0_m (by rw [h2l_c0_m]; exact h2l_bdL) h2l_bdL] at hlt2
        have hszL_eq : (sL.core.wvec[2 * l.toNat + 1]'h2l_bdL).toNat = szL := by
          unfold szL fullWatchSize fullWatchSizeCore
          rw [List.getElem?_eq_getElem h2l_bdL, Option.getD_some]
        omega
      · have hsz2_l : 2 ≤ szL := by omega
        have hoff1_lt : offL + 1 < sL.core.wstk.length := by
          have := hclL.wstk_len_arr; have := hclL.wlen_le; rw [hoff_def]; omega
        have hcr_eq : sL.core.wstk[offL + 1]'hoff1_lt = cr :=
          Option.some.inj ((List.getElem?_eq_getElem hoff1_lt).symm.trans hw1_some)
        let wvec1 := (sL.core.wvec.set (2 * l.toNat) (BitVec.ofNat 32 (offL + 2))).set
          (2 * l.toNat + 1) (BitVec.ofNat 32 (szL - 2))
        let s1 : FullState := { sL with core := { sL.core with
          wvec := wvec1, wusable := sL.core.wusable + 2#64 } }
        have hinv1 := m6_denseInvW_watchPop hinvL hl_ltL hsz2 (sL.core.wusable + 2#64) hsl_nxt
        have hfr1 : M6ElsFrame c F0 F_cur s s1 :=
          ⟨hinv1, hLoop.cv, hLoop.fuel, hLoop.repr, hLoop.tmk, hLoop.trh, hLoop.scr,
           hLoop.ws1, hLoop.ws2, hLoop.gu⟩
        have hsz_lt32 : szL < 2 ^ 32 := by
          unfold szL fullWatchSize fullWatchSizeCore; exact BitVec.isLt _
        have hwv_pop2 := m6_els_wvec_pop_eq (k := 2) sL l hsz2_l (by decide) (by omega) hsz_lt32
          h2l0_c0 h2l1_c0 hoffL_bv hszL_bv
        have hoff1_c0 : (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
            (1 : Nat)).toNat]'(by rw [h2l0_c0, hclL.wvec_len]; omega)) +
            (1 : BitVec 64)).toNat = offL + 1 := by
          rw [BitVec.toNat_add, hoffL_bv, show ((1 : BitVec 64)).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hws_off1_lt : (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
            (1 : Nat)).toNat]'(by rw [h2l0_c0, hclL.wvec_len]; omega)) + (1 : BitVec 64)).toNat <
            sL.core.wstk.length := hoff1_c0 ▸ hoff1_lt
        have hcr_c0_eq : sL.core.wstk[(BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
            (1 : Nat)).toNat]'(by rw [h2l0_c0, hclL.wvec_len]; omega)) +
            (1 : BitVec 64)).toNat]'hws_off1_lt = cr := by
          rw [m6_list_getElem_congr hoff1_c0 hws_off1_lt hoff1_lt]; exact hcr_eq
        have h2l_set2 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat <
            (sL.core.wvec.set (BitVec.setWidth 64 l <<< (1 : Nat)).toNat
              (BitVec.setWidth 32 (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
                (1 : Nat)).toNat]'h2l0_bdL64) + (2 : BitVec 64)))).length := by
          rw [List.length_set]; exact h2l_bdL64
        dsimp only [Prod.fst]; c0_hsteps_nogrp
        refine m6_call_els_ar hElsAr hfr1 (hcr_c0_eq.symm ▸ hcr_ref)
          (hfr1.cv.symm ▸ hrl_lt) (by dsimp only [s1, wvec1]; rw [← hwv_pop2]; assumption)
          fun okA sA mA hfrA hokfA hmA => ?_
        c0_hsplit
        · c0_hsteps!; exact hL (gL - 1#64, sA) mA (by dsimp only; omega) ⟨hfrA, hmA⟩
        · have hokf : okA = false := by
            cases okA <;> first | rfl | contradiction | exact absurd rfl ‹_›
          c0_hsteps!
          exact hQ false sA mA hfrA.dinv hfrA.cv hfrA.fuel hfrA.repr hfrA.tmk hfrA.trh
            hfrA.scr hfrA.ws1 hfrA.ws2 hfrA.gu (fun _ => hokfA hokf) hmA
  · intro B L hB hL; c0_hsteps!
    exact hL (s.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat]'h2l_bd64
      |>.setWidth 64, s) m
      ⟨⟨hinv, rfl, rfl, hrepr_inv, rfl, rfl, rfl, rfl, rfl, rfl⟩, hm⟩

/-! ## 3. `full_m6_dense_els_wp` -/

private theorem m6_call_els_lit {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hElsLit : Γ.Has "full_m6_els_lit" fullM6ElsLitSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s1 : FullState}
    {l rl : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [.bool] → Expr Val Cont rs}
    (hfr : M6ElsFrame c F0 F_cur s s1)
    (hl : l.toNat < 2 * s1.core.cur_vars) (hrl : rl.toNat < 2 * s1.core.cur_vars)
    (heqv : LitEquiv (cnfOfClauses F_cur) l.toNat rl.toNat) (hm : (FullMem c s1 ⋆ R) m)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      M6ElsFrame c F0 F_cur s s' →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_m6_els_lit"
        (Arg.var c.hdr, Arg.var l, Arg.var rl, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hElsLit (c.hdr, l, rl, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, F0, F_cur, s1, R, rfl, hfr.dinv, hl, hrl, heqv, hfr.cv.symm ▸ hfr.repr, hm, ?_⟩
  intro ok s' m' hinv' hcv' hfl' hrepr' htmk' htrh' hscr' hws1' hws2' hgu' hfail' hm'
  exact hk ok s' m'
    ⟨hinv', hcv'.trans hfr.cv, hfl'.trans hfr.fuel, hfr.cv ▸ hrepr',
     htmk'.trans hfr.tmk, htrh'.trans hfr.trh, hscr'.trans hfr.scr,
     hws1'.trans hfr.ws1, hws2'.trans hfr.ws2, hgu'.trans hfr.gu⟩ hfail' hm'

private theorem m6_call_dense_prop {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hProp : Γ.Has "full_m6_dense_prop" fullDensePropSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sE : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [.bool] → Expr Val Cont rs}
    (hfr : M6ElsFrame c F0 F_cur s sE) (hm : (FullMem c sE ⋆ R) m)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      M6ElsFrame c F0 F_cur s s' →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64]) (bs := [.bool]) "full_m6_dense_prop"
        (Arg.var c.hdr, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hProp (c.hdr, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, F0, F_cur, sE, R, rfl, hfr.dinv, hm, ?_⟩
  intro ok s' m' hinv' hcv' hfl' hrp' _ _ htmk' htrh' hscr' hws1' hws2' hgu' _ hfail' hm'
  exact hk ok s' m'
    ⟨hinv', hcv'.trans hfr.cv, hfl'.trans hfr.fuel, hrp'.symm ▸ hfr.repr,
     htmk'.trans hfr.tmk, htrh'.trans hfr.trh, hscr'.trans hfr.scr,
     hws1'.trans hfr.ws1, hws2'.trans hfr.ws2, hgu'.trans hfr.gu⟩ hfail' hm'

private theorem m6_dense_els_ret {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sR : FullState} {R : Mem 64 → Prop} {mR : Mem 64} {Q : Post [.bool]} {ok : Bool}
    (hfr : M6ElsFrame c F0 F_cur s sR)
    (hf : ok = false → F0.Unsat ∧ sR.core.inconsistent ≠ 0#64)
    (hmR : (FullMem c sR ⋆ R) mR)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (ok, ()) mR :=
  hQ ok sR mR hfr.dinv hfr.cv hfr.fuel (hfr.cv.symm ▸ hfr.repr) hfr.tmk hfr.trh hfr.scr hfr.ws2
    hfr.gu hf hmR

theorem full_m6_dense_els_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" fullCongFindSpec)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hElsLit : Γ.Has "full_m6_els_lit" fullM6ElsLitSpec)
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec)
    (hDenseProp : Γ.Has "full_m6_dense_prop" fullDensePropSpec) :
    ∀ args m Q X, fullM6DenseElsSpec args m Q X →
      Func.wp Γ full_m6_dense_els_body args m Q X := by
  rintro ⟨h, neq, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, heqb, hrepr_inv, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hfr0 : M6ElsFrame c F0 F_cur s s :=
    ⟨hinv, rfl, rfl, hrepr_inv, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold Func.wp full_m6_dense_els_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () mE => (FullMem c s ⋆ R) mE) ?_ ?_
  · rintro _ ⟨⟩ mE hmE; c0_hsteps!
    by_cases hinc0 : s.core.inconsistent = 0#64
    · simpa [hinc0] using m6_dense_els_ret (ok := true) hfr0 (fun h => Bool.noConfusion h) hmE hQ
    · have huns := hinv.2.1.ext_sound.2 (hinv.2.1.inconsistent_sound hinc0)
      simpa [beq_false_of_ne hinc0] using m6_dense_els_ret (ok := false) hfr0
        (fun _ => ⟨huns, hinc0⟩) hmE hQ
  · intro Je hJe
    c0_hsplit; · c0_hsteps!; exact hJe () m hm
    c0_hsplit; · c0_hsteps!; exact hJe () m hm
    c0_hsteps_nogrp
    refine wp_while_state (ts := [i64]) (α := BitVec 64 × FullState)
      (proj := fun p => (p.1, ())) (μ := fun p => neq.toNat - p.1.toNat)
      (Inv := fun p ml => p.1.toNat ≤ neq.toNat ∧ M6ElsFrame c F0 F_cur s p.2 ∧
        (FullMem c p.2 ⋆ R) ml)
      (fun L hL => by c0_hsteps!; exact hL (0#64, s) m ⟨Nat.zero_le _, hfr0, hm⟩) ?_
    rintro L ⟨ei, sL⟩ ml ⟨hei_le, hfrL, hmL⟩ hL
    dsimp only at *
    refine wp_join_group (ts := []) (fun () mE => ∃ sE : FullState,
        M6ElsFrame c F0 F_cur s sE ∧ (FullMem c sE ⋆ R) mE) ?_ ?_
    · rintro _ ⟨⟩ mE ⟨sE, hfrE, hmE⟩
      c0_hsplit
      · have hinc : sE.core.inconsistent ≠ 0#64 := ‹_›
        have huns := hfrE.dinv.2.1.ext_sound.2 (hfrE.dinv.2.1.inconsistent_sound hinc)
        c0_hsteps!; exact m6_dense_els_ret (ok := false) hfrE (fun _ => ⟨huns, hinc⟩) hmE hQ
      · c0_hsteps_nogrp
        refine m6_call_dense_prop hDenseProp hfrE hmE fun okP sP mP hfrP hfailP hmP => ?_
        c0_hsteps!; exact m6_dense_els_ret hfrP hfailP hmP hQ
    · intro B hB
      have hinvL := hfrL.dinv; have hclL := hinvL.1.core_ok
      have hcvL_le := hclL.cur_vars_le; have hcv_eq := hfrL.cv
      have hneq_le : neq.toNat ≤ s.core.cur_vars := heqb.1
      c0_hsplit; rotate_left; · c0_hsteps!; exact hB () ml ⟨sL, hfrL, hmL⟩
      c0_hsplit; rotate_left; · c0_hsteps!; exact hB () ml ⟨sL, hfrL, hmL⟩
      c0_hsplit; rotate_left; · c0_hsteps!; exact hB () ml ⟨sL, hfrL, hmL⟩
      have hei_lt : ei.toNat < neq.toNat := by bv_omega
      have hei1 : (ei + 1#64).toNat = ei.toNat + 1 := by bv_omega
      have h2ei0_c0 : (ei <<< (1 : Nat)).toNat = 2 * ei.toNat := by
        rw [m6_els_bv64_shl1_nat, Nat.mod_eq_of_lt (by omega)]
      have h2ei1_c0 : (ei <<< (1 : Nat) + 1#64).toNat = 2 * ei.toNat + 1 := by
        rw [BitVec.toNat_add, h2ei0_c0, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have h2ei0_bd : (ei <<< (1 : Nat)).toNat < sL.scratch.work_stk2.length := by
        rw [h2ei0_c0, hinvL.1.scratch_ok.work_stk2_len]; omega
      have h2ei1_bd : (ei <<< (1 : Nat) + 1#64).toNat < sL.scratch.work_stk2.length := by
        rw [h2ei1_c0, hinvL.1.scratch_ok.work_stk2_len]; omega
      have ha_eq : sL.scratch.work_stk2[(ei <<< (1 : Nat)).toNat]'h2ei0_bd =
          s.scratch.work_stk2[2 * ei.toNat]?.getD 0#32 := by
        rw [m6_list_getElem_congr h2ei0_c0 h2ei0_bd (by
          rw [hinvL.1.scratch_ok.work_stk2_len]; omega), m6_getElem_eq_getD, hfrL.ws2]
      have hb_eq : sL.scratch.work_stk2[(ei <<< (1 : Nat) + 1#64).toNat]'h2ei1_bd =
          s.scratch.work_stk2[2 * ei.toNat + 1]?.getD 0#32 := by
        rw [m6_list_getElem_congr h2ei1_c0 h2ei1_bd (by
          rw [hinvL.1.scratch_ok.work_stk2_len]; omega), m6_getElem_eq_getD, hfrL.ws2]
      obtain ⟨ha_lt, hb_lt, hab_eqv⟩ := heqb.2 ei.toNat hei_lt
      c0_hsteps_nogrp
      c0_hsplit
      · c0_hsteps!
        exact hL (ei + 1#64, sL) ml (by dsimp only; rw [hei1]; omega)
          ⟨by dsimp only; rw [hei1]; omega, hfrL, hmL⟩
      c0_hsplit
      · c0_hsteps!
        exact hL (ei + 1#64, sL) ml (by dsimp only; rw [hei1]; omega)
          ⟨by dsimp only; rw [hei1]; omega, hfrL, hmL⟩
      c0_hsteps_nogrp
      refine m6_call_cong_find hFind (hcv_eq.symm ▸ hfrL.repr) (by rw [ha_eq, hcv_eq]; exact ha_lt)
        hmL fun ra0 repr1 m1 hrp1_l hrepr1 _ hra0_lt ha_ra0 hm1 => ?_
      let s1 : FullState := { sL with core := { sL.core with repr := repr1 } }
      have hinv1 := m6_fullDenseInvW_set_repr hinvL (hrp1_l.trans hclL.repr_len)
      have hfr1 : M6ElsFrame c F0 F_cur s s1 :=
        ⟨hinv1, hcv_eq, hfrL.fuel, hcv_eq ▸ hrepr1, hfrL.tmk, hfrL.trh, hfrL.scr,
         hfrL.ws1, hfrL.ws2, hfrL.gu⟩
      c0_hsteps_nogrp
      refine m6_call_cong_find hFind hrepr1 (by rw [hb_eq]; exact hcv_eq.symm ▸ hb_lt)
        hm1 fun rb0 repr2 m2 hrp2_l hrepr2 _ hrb0_lt hb_rb0 hm2 => ?_
      let s2 : FullState := { s1 with core := { s1.core with repr := repr2 } }
      have hinv2 := m6_fullDenseInvW_set_repr hinv1 (hrp2_l.trans (hrp1_l.trans hclL.repr_len))
      have hfr2 : M6ElsFrame c F0 F_cur s s2 :=
        ⟨hinv2, hcv_eq, hfrL.fuel, hcv_eq ▸ hrepr2, hfrL.tmk, hfrL.trh, hfrL.scr,
         hfrL.ws1, hfrL.ws2, hfrL.gu⟩
      have hrab0_eqv : LitEquiv (cnfOfClauses F_cur) ra0.toNat rb0.toNat :=
        m6_litEquiv_trans (m6_litEquiv_symm (ha_eq ▸ ha_ra0))
          (m6_litEquiv_trans hab_eqv (hb_eq ▸ hb_rb0))
      c0_hsplit
      · c0_hsteps!
        exact hL (ei + 1#64, s2) m2 (by dsimp only; rw [hei1]; omega)
          ⟨by dsimp only; rw [hei1]; omega, hfr2, hm2⟩
      c0_hsplit
      · have hcontra : ra0 = rb0 ^^^ 1#32 := ‹_›
        have huns : (cnfOfClauses F_cur).Unsat := m6_litEquiv_self_neg_unsat
          (by rw [← m6_els_bv32_xor1_toNat, ← hcontra]; exact hrab0_eqv)
        c0_hsteps!
        exact m6_dense_els_ret (ok := false)
          ⟨m6_fullDenseInvW_set_inconsistent hinv2 huns, hfr2.cv, hfr2.fuel, hfr2.repr,
           hfr2.tmk, hfr2.trh, hfr2.scr, hfr2.ws1, hfr2.ws2, hfr2.gu⟩
          (fun _ => ⟨hinv2.2.1.ext_sound.2 huns, by simp⟩) (by assumption) hQ
      have hne0 : ra0 ≠ rb0 := ‹_›
      have hne_xor0 : ra0 ≠ rb0 ^^^ 1#32 := ‹_›
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32, i32])
        (proj := fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
        (fun (ra, rb) mS => mS = m2 ∧ ra.toNat < rb.toNat ∧ rb.toNat < 2 * s2.core.cur_vars ∧
          ra ≠ rb ^^^ 1#32 ∧ LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat) ?_ ?_
      · rintro _ ⟨ra, rb⟩ mS ⟨hmS, hlt_ab, hrb_lt, hne_xor, hrab_eqv⟩
        subst mS
        have hra_lt : ra.toNat < 2 * s2.core.cur_vars := by omega
        have hcl2 := hinv2.1.core_ok
        have hcv2_le : s2.core.cur_vars ≤ c.max_vars := hcl2.cur_vars_le
        have hvl2_len : s2.core.vals.length = 2 * c.max_vars := hcl2.vals_len
        have hfl2_len : s2.core.flags.length = c.max_vars := hcl2.flags_len
        have hrp2_len : s2.core.repr.length = 2 * c.max_vars := hcl2.repr_len
        have hw2 := hinv2.2.1; have hcl0_2 := hinv2.2.2.2.2.2.1
        have hra_vl : ra.toNat < s2.core.vals.length := by rw [hvl2_len]; omega
        have hrb_vl : rb.toNat < s2.core.vals.length := by rw [hvl2_len]; omega
        have hrb1_lt : (rb ^^^ 1#32).toNat < 2 * s2.core.cur_vars := by
          rw [m6_els_bv32_xor1_toNat]; exact m6_nat_xor1_lt hrb_lt
        have hra1_lt : (ra ^^^ 1#32).toNat < 2 * s2.core.cur_vars := by
          rw [m6_els_bv32_xor1_toNat]; exact m6_nat_xor1_lt hra_lt
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun () mV1 => mV1 = m2 ∧
            ¬ (s2.core.vals[ra.toNat]'hra_vl ≠ 0#8 ∧ s2.core.vals[rb.toNat]'hrb_vl ≠ 0#8)) ?_ ?_
        · rintro _ ⟨⟩ mV1 ⟨hmV1, _⟩; subst mV1; c0_hsplit
          · have hva_nz : s2.core.vals[ra.toNat]?.getD 0#8 ≠ 0#8 := by
              rw [List.getElem?_eq_getElem hra_vl, Option.getD_some]; exact m6_bv8_ne0_of_sext hc
            obtain ⟨hu_pos, hu_neg⟩ := m6_dense_els_unit_of_val hw2 hcl0_2 hra_lt hrab_eqv hva_nz
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (proj := fun u : BitVec 32 => (u, ()))
              (fun u mU => mU = m2 ∧ u.toNat < 2 * s2.core.cur_vars ∧
                (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat])) ?_ ?_
            · rintro _ u mU ⟨hmU, hu_lt, hent_u⟩; subst mU; c0_hsteps_nogrp
              refine m6_call_add_unit hAddUnit hfr2 hu_lt hent_u hm2
                fun okU sU mU' hfrU _ hfailU hmU' => ?_
              c0_hsplit
              · c0_hsteps!; exact hL (ei + 1#64, sU) mU' (by dsimp only; rw [hei1]; omega)
                  ⟨by dsimp only; rw [hei1]; omega, hfrU, hmU'⟩
              · have hokf : okU = false := by
                  cases okU <;> first | rfl | contradiction | exact absurd rfl ‹_›
                c0_hsteps!; exact m6_dense_els_ret (ok := false) hfrU (fun _ => hfailU hokf) hmU' hQ
            · intro Ju hJu; c0_hsplit
              · c0_hsteps!; exact hJu rb m2 ⟨rfl, hrb_lt, hu_pos (by
                  rw [List.getElem?_eq_getElem hra_vl, Option.getD_some]; exact ‹_›)⟩
              · c0_hsteps!; exact hJu (rb ^^^ 1#32) m2 ⟨rfl, hrb1_lt, by
                  rw [m6_els_bv32_xor1_toNat]; exact hu_neg (by
                    rw [List.getElem?_eq_getElem hra_vl, Option.getD_some]; exact ‹_›)⟩
          c0_hsplit
          · have hvb_nz : s2.core.vals[rb.toNat]?.getD 0#8 ≠ 0#8 := by
              rw [List.getElem?_eq_getElem hrb_vl, Option.getD_some]; exact m6_bv8_ne0_of_sext hc
            obtain ⟨hu_pos, hu_neg⟩ :=
              m6_dense_els_unit_of_val hw2 hcl0_2 hrb_lt (m6_litEquiv_symm hrab_eqv) hvb_nz
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (proj := fun u : BitVec 32 => (u, ()))
              (fun u mU => mU = m2 ∧ u.toNat < 2 * s2.core.cur_vars ∧
                (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat])) ?_ ?_
            · rintro _ u mU ⟨hmU, hu_lt, hent_u⟩; subst mU; c0_hsteps_nogrp
              refine m6_call_add_unit hAddUnit hfr2 hu_lt hent_u hm2
                fun okU sU mU' hfrU _ hfailU hmU' => ?_
              c0_hsplit
              · c0_hsteps!; exact hL (ei + 1#64, sU) mU' (by dsimp only; rw [hei1]; omega)
                  ⟨by dsimp only; rw [hei1]; omega, hfrU, hmU'⟩
              · have hokf : okU = false := by
                  cases okU <;> first | rfl | contradiction | exact absurd rfl ‹_›
                c0_hsteps!; exact m6_dense_els_ret (ok := false) hfrU (fun _ => hfailU hokf) hmU' hQ
            · intro Ju hJu; c0_hsplit
              · c0_hsteps!; exact hJu ra m2 ⟨rfl, hra_lt, hu_pos (by
                  rw [List.getElem?_eq_getElem hrb_vl, Option.getD_some]; exact ‹_›)⟩
              · c0_hsteps!; exact hJu (ra ^^^ 1#32) m2 ⟨rfl, hra1_lt, by
                  rw [m6_els_bv32_xor1_toNat]; exact hu_neg (by
                    rw [List.getElem?_eq_getElem hrb_vl, Option.getD_some]; exact ‹_›)⟩
          have hra_fl : (ra >>> (1 : Nat)).toNat < s2.core.flags.length := by
            rw [hfl2_len, m6_els_bv32_shr1_nat]; omega
          have hrb_fl : (rb >>> (1 : Nat)).toNat < s2.core.flags.length := by
            rw [hfl2_len, m6_els_bv32_shr1_nat]; omega
          c0_hsplit
          · c0_hsteps!; exact hL (ei + 1#64, s2) m2 (by dsimp only; rw [hei1]; omega)
              ⟨by dsimp only; rw [hei1]; omega, hfr2, hm2⟩
          c0_hsplit
          · c0_hsteps!; exact hL (ei + 1#64, s2) m2 (by dsimp only; rw [hei1]; omega)
              ⟨by dsimp only; rw [hei1]; omega, hfr2, hm2⟩
          have hrb_rp : rb.toNat < s2.core.repr.length := by rw [hrp2_len]; omega
          have hrb1_rp : (rb ^^^ 1#32).toNat < (s2.core.repr.set rb.toNat ra).length := by
            rw [List.length_set, hrp2_len]; omega
          let repr3 := (s2.core.repr.set rb.toNat ra).set (rb ^^^ 1#32).toNat (ra ^^^ 1#32)
          let fl3 := s2.core.flags.set (rb >>> (1 : Nat)).toNat
            ((s2.core.flags[(rb >>> (1 : Nat)).toNat]'hrb_fl) &&&
              ~~~(1024#32 ||| 0x40000000#32 ||| 0x20000000#32))
          let s3 : FullState :=
            { s2 with
              core := { s2.core with repr := repr3, flags := fl3 }
              scratch := { s2.scratch with sweep_cnt := s2.scratch.sweep_cnt + 1#64 } }
          have hrepr3_len : repr3.length = 2 * c.max_vars := by simp [repr3, hrp2_len]
          have hfl3_len : fl3.length = c.max_vars := by simp [fl3, hfl2_len]
          have hinv3 : FullDenseInvW c F0 F_cur s3 :=
            m6_fullDenseInvW_set_sweep_cnt
              (m6_fullDenseInvW_with_flags (m6_fullDenseInvW_set_repr hinv2 hrepr3_len) hfl3_len) _
          have hrepr3 : FullCongReprInv F_cur (2 * s.core.cur_vars) repr3 :=
            m6_congReprInv_merge hfr2.repr hlt_ab (hcv_eq ▸ hrb_lt) hne_xor hrab_eqv
          have hfr3 : M6ElsFrame c F0 F_cur s s3 :=
            ⟨hinv3, hfr2.cv, hfr2.fuel, hrepr3, hfr2.tmk, hfr2.trh, hfr2.scr,
             hfr2.ws1, hfr2.ws2, hfr2.gu⟩
          c0_hsteps_nogrp
          refine m6_call_els_lit hElsLit hfr3 hrb_lt hra_lt (m6_litEquiv_symm hrab_eqv)
            (by dsimp only [s3, repr3, fl3]; assumption)
            fun ok1 s4 m4 hfr4 hfail4 hm4 => ?_
          c0_hsplit; rotate_left
          · have hokf : ok1 = false := by
              cases ok1 <;> first | rfl | contradiction | exact absurd rfl ‹_›
            c0_hsteps!; exact m6_dense_els_ret (ok := false) hfr4 (fun _ => hfail4 hokf) hm4 hQ
          c0_hsteps_nogrp
          refine m6_call_els_lit hElsLit hfr4 (by rw [hfr4.cv, ← hcv_eq]; exact hrb1_lt)
            (by rw [hfr4.cv, ← hcv_eq]; exact hra1_lt)
            (by dsimp only [Prod.fst]; rw [m6_els_bv32_xor1_ofnat, m6_els_bv32_xor1_ofnat]
                exact m6_litEquiv_neg (m6_litEquiv_symm hrab_eqv)) hm4
            fun ok2 s5 m5 hfr5 hfail5 hm5 => ?_
          c0_hsplit; rotate_left
          · have hokf : ok2 = false := by
              cases ok2 <;> first | rfl | contradiction | exact absurd rfl ‹_›
            c0_hsteps!; exact m6_dense_els_ret (ok := false) hfr5 (fun _ => hfail5 hokf) hm5 hQ
          obtain ⟨hent_b1, hent_b2⟩ := m6_litEquiv_entails_bin (m6_litEquiv_symm hrab_eqv)
          c0_hsteps_nogrp
          refine m6_call_add_bin hAddBin hfr5
            (by dsimp only [Prod.fst]
                rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.or_zero, m6_els_bv32_xor1_ofnat]
                exact hent_b1) hm5
            fun ab1 s6 m6 hfr6 hr20_1 hm6 => ?_
          c0_hsplit
          · have h20 : ab1 = 20#64 := by bv_omega
            c0_hsteps!; exact m6_dense_els_ret (ok := false) hfr6 (fun _ => hr20_1 h20) hm6 hQ
          c0_hsplit
          · c0_hsteps!
            exact m6_dense_els_ret (ok := true) hfr6.set_oom (fun h => Bool.noConfusion h)
              (by assumption) hQ
          c0_hsteps_nogrp
          refine m6_call_add_bin hAddBin hfr6
            (by dsimp only [Prod.fst]; rw [m6_els_bv32_xor1_ofnat]; exact hent_b2) hm6
            fun ab2 s7 m7 hfr7 hr20_2 hm7 => ?_
          c0_hsplit
          · have h20 : ab2 = 20#64 := by bv_omega
            c0_hsteps!; exact m6_dense_els_ret (ok := false) hfr7 (fun _ => hr20_2 h20) hm7 hQ
          c0_hsplit
          · c0_hsteps!
            exact m6_dense_els_ret (ok := true) hfr7.set_oom (fun h => Bool.noConfusion h)
              (by assumption) hQ
          · c0_hsteps!; exact hL (ei + 1#64, s7) m7 (by dsimp only; rw [hei1]; omega)
              ⟨by dsimp only; rw [hei1]; omega, hfr7, hm7⟩
        · intro Jv1 hJv1
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · have hva_nz : s2.core.vals[ra.toNat]?.getD 0#8 ≠ 0#8 := by
                  rw [List.getElem?_eq_getElem hra_vl, Option.getD_some]
                  exact m6_bv8_ne0_of_sext ‹¬BitVec.signExtend 32 (sL.core.vals[ra.toNat]'_) = 0#32›
                have hvb_nz : s2.core.vals[rb.toNat]?.getD 0#8 ≠ 0#8 := by
                  rw [List.getElem?_eq_getElem hrb_vl, Option.getD_some]
                  exact m6_bv8_ne0_of_sext ‹¬BitVec.signExtend 32 (sL.core.vals[rb.toNat]'_) = 0#32›
                have hne_v : s2.core.vals[ra.toNat]?.getD 0#8 ≠
                    s2.core.vals[rb.toNat]?.getD 0#8 := by
                  rw [List.getElem?_eq_getElem hra_vl, List.getElem?_eq_getElem hrb_vl,
                    Option.getD_some, Option.getD_some]
                  first | exact ‹_›
                        | (intro he; apply (‹_› : (s2.core.vals[ra.toNat]'hra_vl).signExtend 32 ≠
                            (s2.core.vals[rb.toNat]'hrb_vl).signExtend 32); rw [he])
                have huns := m6_dense_els_vals_contra hw2 hcl0_2 hra_lt hrb_lt hrab_eqv
                  hva_nz hvb_nz hne_v
                c0_hsteps!
                exact m6_dense_els_ret (ok := false)
                  ⟨m6_fullDenseInvW_set_inconsistent hinv2 huns, hfr2.cv, hfr2.fuel, hfr2.repr,
                   hfr2.tmk, hfr2.trh, hfr2.scr, hfr2.ws1, hfr2.ws2, hfr2.gu⟩
                  (fun _ => ⟨hw2.ext_sound.2 huns, by simp⟩) (by assumption) hQ
              · c0_hsteps!; exact hL (ei + 1#64, s2) m2 (by dsimp only; rw [hei1]; omega)
                  ⟨by dsimp only; rw [hei1]; omega, hfr2, hm2⟩
            · c0_hsteps!; exact hJv1 () m2 ⟨rfl, fun h => h.2 ((m6_bv8_sext32_eq0_iff _).mp hc)⟩
          · c0_hsteps!; exact hJv1 () m2 ⟨rfl, fun h => h.1 ((m6_bv8_sext32_eq0_iff _).mp hc)⟩
      · intro Js hJs
        c0_hsplit
        · have hrb_lt_ra : rb0.toNat < ra0.toNat := ‹_›
          have hne_sw : rb0 ≠ ra0 ^^^ 1#32 := fun he => hne_xor0 (by
            apply BitVec.eq_of_toNat_eq
            have h1 := congrArg BitVec.toNat he
            rw [m6_els_bv32_xor1_toNat] at h1 ⊢; rw [h1, m6_xor1_xor1])
          c0_hsteps!
          exact hJs (rb0, ra0) m2 ⟨rfl, hrb_lt_ra, hra0_lt, hne_sw, m6_litEquiv_symm hrab0_eqv⟩
        · have hra_lt_rb : ra0.toNat < rb0.toNat := by
            have hge : ra0.toNat ≤ rb0.toNat := Nat.le_of_not_lt ‹_›
            have hne_n : ra0.toNat ≠ rb0.toNat := fun he => hne0 (BitVec.eq_of_toNat_eq he)
            omega
          c0_hsteps!
          exact hJs (ra0, rb0) m2 ⟨rfl, hra_lt_rb, hrb0_lt, hne_xor0, hrab0_eqv⟩

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
