/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Helpers

/-!
# Pure Helpers & Loop Invariants for `full_subst_rewrite_ar`

Extracts pure `FullState` invariants and transition lemmas from `WpRewriteAr`
so every declaration stays compact (`<= 450` LOC) and free of `@[expose]`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped Proof.Spec.FullArenaTactics SubstArenaTactics

private theorem ra_bv32_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem ra_bv64_one : (1#64 : BitVec 64).toNat = 1 := rfl
private theorem ra_bv64_two : (2#64 : BitVec 64).toNat = 2 := rfl

private theorem ra_litVar_eq_iff (a b : Nat) : a / 2 = b / 2 ↔ a = b ∨ a = b ^^^ 1 := by
  constructor
  · intro h
    by_cases h0 : a % 2 = b % 2
    · left; omega
    · right
      apply Nat.eq_of_testBit_eq
      intro i
      cases i with
      | zero =>
        rw [Nat.testBit_xor]
        simp only [Nat.testBit_zero, show (1 : Nat) % 2 = 1 from rfl]
        cases ha : decide (a % 2 = 1) <;> cases hb : decide (b % 2 = 1) <;>
          simp_all <;> omega
      | succ k =>
        rw [Nat.testBit_xor]
        simp only [Nat.testBit_succ, show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit,
          Bool.bne_false, h]
  · rintro (rfl | rfl)
    · rfl
    · have : (b ^^^ 1) / 2 = b / 2 := by
        apply Nat.eq_of_testBit_eq; intro k
        have hk := Nat.testBit_succ (b ^^^ 1) k
        have hk2 := Nat.testBit_succ b k
        rw [← hk, ← hk2, Nat.testBit_xor]
        simp [Nat.testBit_succ, show (1 : Nat) / 2 = 0 from rfl]
      exact this

private theorem ra_litNeg_lt_two_mul {l n : Nat} (h : l < 2 * n) : l ^^^ 1 < 2 * n := by
  have heq : (l ^^^ 1) / 2 = l / 2 := (ra_litVar_eq_iff (l ^^^ 1) l).mpr (Or.inr rfl)
  omega

private theorem ra_fullState_eq_replace_arena_lm_ag {s s' : FullState}
    (hsc : s'.scratch = s.scratch)
    (hc :
      { s'.core with
        arena := s.core.arena, lit_mark := s.core.lit_mark,
        arena_garbage := s.core.arena_garbage } = s.core) :
    s' =
      { s with core := { s.core with
        arena := s'.core.arena, lit_mark := s'.core.lit_mark,
        arena_garbage := s'.core.arena_garbage } } := by
  rcases s with ⟨c0, sc0⟩; rcases s' with ⟨c1, sc1⟩
  cases hsc; cases c0; cases c1; cases hc; rfl

private theorem ra_core_eq_of_arena_lm {s s' : FullState}
    (hc : { s'.core with arena := s.core.arena, lit_mark := s.core.lit_mark } = s.core) :
    { s'.core with
      arena := s.core.arena, lit_mark := s.core.lit_mark,
      arena_garbage := s.core.arena_garbage } = s.core := by
  rcases s with ⟨c0, _⟩; rcases s' with ⟨c1, _⟩; cases c0; cases c1; cases hc; rfl

private theorem ra_replace_ag_eq {st st3 : FullState} {ar4 : List (BitVec 32)} {ag4 : BitVec 64}
    (hcore3 : { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core) :
    { ({ st3 with core := { st3.core with arena := ar4, arena_garbage := ag4 } } : FullState).core
      with arena := st.core.arena, lit_mark := st.core.lit_mark,
           arena_garbage := st.core.arena_garbage } = st.core := by
  rcases st with ⟨c0, _⟩; rcases st3 with ⟨c3, _⟩; cases c0; cases c3; cases hcore3; rfl

public section

theorem ra_arenaBlockReplace_l0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} {cref : Nat}
    (hsp : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0) (hsc : s'.scratch = s.scratch)
    (hc : { s'.core with
        arena := s.core.arena, lit_mark := s.core.lit_mark,
        arena_garbage := s.core.arena_garbage } = s.core)
    (href : cref ∈ fullArenaClauseRefs s) (har'_len : s'.core.arena.length = c.arena_cap)
    (hlm'_len : s'.core.lit_mark.length = 2 * c.max_vars)
    (hlm'_zero : ∀ x < 2 * c.max_vars, s'.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      s'.core.arena[i]? = s.core.arena[i]?)
    (hnxt_cref : fullArenaNextOff s'.core.arena s.core.arena_len cref =
      fullArenaNextOff s.core.arena s.core.arena_len cref)
    (hsz_cref : 3 ≤ (s'.core.arena[cref + 2]?.getD 0#32).toNat ∧
      (s'.core.arena[cref + 2]?.getD 0#32).toNat ≤ fullArenaClauseSize s cref)
    (hshrk_cref : (s'.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 →
      ∃ t, cref + 3 + (s'.core.arena[cref + 2]?.getD 0#32).toNat ≤ t ∧ t < s.core.arena_len ∧
        s'.core.arena[t]? = some 0xFFFFFFFF#32)
    (hlive_cref : (s'.core.arena[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32 →
      (∀ j < (s'.core.arena[cref + 2]?.getD 0#32).toNat,
        (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ i j, i < j → j < (s'.core.arena[cref + 2]?.getD 0#32).toNat →
        (s'.core.arena[cref + 3 + i]?.getD 0#32).toNat / 2 ≠
        (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat / 2) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((List.range (s'.core.arena[cref + 2]?.getD 0#32).toNat).map fun j =>
          (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat))) :
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
      s'.core.arena_len = s.core.arena_len := by
  have hout' : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i →
      s'.core.arena[i]? = s.core.arena[i]? := hout
  have hsz_le' : (s'.core.arena[cref + 2]?.getD 0#32).toNat ≤
      fullArenaClauseSizeCore s.core cref := hsz_cref.2
  rw [ra_fullState_eq_replace_arena_lm_ag hsc hc]
  let s1 : FullState :=
    { s with core := { s.core with
        arena := s'.core.arena, lit_mark := s'.core.lit_mark,
        arena_garbage := s'.core.arena_garbage } }
  have hcl := hsp.1.core_ok; have hw := hsp.2.1; have ha := hw.arena
  have hcref_wf := ha.refs_wf cref href
  have hblk_eq : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      ∀ i, r ≤ i → i < fullArenaNextOff s.core.arena s.core.arena_len r →
        s'.core.arena[i]? = s.core.arena[i]? := fun r hr hne i hi1 hi2 => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := fullArenaScanRefs_disjoint hr href hlt; exact hout' i (Or.inl (by omega))
    · have := fullArenaScanRefs_disjoint href hr hgt
      have := hcref_wf.2.2.1; exact hout' i (Or.inr (by omega))
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s1.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := fun r hr => by
    by_cases hrc : r = cref
    · subst r; exact hnxt_cref
    · have hrwf := ha.refs_wf r hr; have hbe := hblk_eq r hr hrc
      exact fullArenaNextOff_congr_block (hbe r (Nat.le_refl r) (by omega))
        (hbe (r + 2) (by omega) (by omega)) fun i hi1 hi2 => hbe i (by omega) hi2
  have hrefs : fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hother : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseSizeCore s1.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s1.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s1.core r = fullArenaClauseLitsCore s.core r := fun r hr hne => by
    have hrwf := ha.refs_wf r hr; have hbe := hblk_eq r hr hne
    have hszr : fullArenaClauseSizeCore s1.core r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore s1; rw [hbe (r + 2) (by omega) (by omega)]
    refine ⟨hszr,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore s1; rw [hbe r (Nat.le_refl r) (by omega)],
      fullArenaClauseLitsCore_eq_of_hold
        (by have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
        (by dsimp only [s1]; rw [har'_len]; have := hcl.arena_len_le; omega) hszr
        fun j hj => hbe (r + 3 + j) (by omega) (by omega)⟩
  have hclits : fullArenaClauseLitsCore s1.core cref =
      (List.range (s'.core.arena[cref + 2]?.getD 0#32).toNat).map fun j =>
        (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat := by
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
    exact list_drop_take_map_toNat_eq_range
      (by dsimp only [s1]; rw [har'_len]; have := hcl.arena_len_le; omega)
  have hc_ng_z : fullArenaClauseGarbCore s1.core cref = false →
      (s'.core.arena[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32 := fun hng => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore s1 at hng; simpa [bne_iff_ne] using hng
  have ha1 : FullArenaClausesInv c F_cur s1.core := by
    refine ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [s1] at hnxt ⊢; rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; unfold fullArenaClauseSizeCore; dsimp only [s1]
        exact ⟨hcref_wf.1, hsz_cref.1, by omega, hcref_wf.2.2.2.1, hcref_wf.2.2.2.2⟩
      · rw [(hother r hr hrc).1]; exact ha.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hshrk_cref hsh
      · have hrwf := ha.refs_wf r hr; have hbe := hblk_eq r hr hrc
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore s1 at hsh; rwa [hbe r (Nat.le_refl r) (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
        obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel hrwf.1 hsh0 ht1 ht2 hsent
        rw [(hother r hr hrc).1]
        exact ⟨t0, ht0_lo, by dsimp only [s1]; omega,
          by dsimp only [s1]; rw [hbe t0 (by omega) (by omega)]; exact ht0_sent⟩
    · intro r hr hng1; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; intro l hl; rw [hclits, List.mem_map] at hl; rcases hl with ⟨j, hj, rfl⟩
        exact (hlive_cref (hc_ng_z hng1)).1 j (List.mem_range.mp hj)
      · rw [(hother r hr hrc).2.1] at hng1; rw [(hother r hr hrc).2.2]; exact ha.lits_lt r hr hng1
    · intro r hr hng1; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; rw [hclits]; exact (hlive_cref (hc_ng_z hng1)).2.2
      · rw [(hother r hr hrc).2.1] at hng1; rw [(hother r hr hrc).2.2]; exact ha.entails r hr hng1
  have hnd1 : FullArenaVarsNodup s1 := fun r hr hng1 => by
    change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; change ((fullArenaClauseLitsCore s1.core cref).map (· / 2)).Nodup
      rw [hclits, List.map_map]; exact nodup_range_map_of_pairwise (hlive_cref (hc_ng_z hng1)).2.1
    · obtain ⟨_, hgb, hlt⟩ := hother r hr hrc
      change fullArenaClauseGarbCore s1.core r = false at hng1; rw [hgb] at hng1
      change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup; rw [hlt]
      exact hsp.2.2.2.1 r hr hng1
  have hw1 : FullWitnessInv c F0 F_cur s1.core :=
    { hw with
      arena := ha1
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl
        (fun r hr => by change r ∈ fullArenaClauseRefsCore s1.core; rw [hrefs]; exact hr)
      reason_inv := fun idx hidx hne => absurd
        (hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)) hne
      reason_lit_mem := fun idx hidx hne => absurd
        (hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)) hne }
  exact ⟨⟨⟨{ hcl with arena_len_arr := har'_len, lit_mark_len := hlm'_len }, hsp.1.scratch_ok⟩,
    hw1, ⟨hsp.2.2.1.1, hlm'_zero⟩, hnd1,
    hsp.2.2.2.2.1.of_pres ⟨rfl, rfl⟩
      (fun r hr => by change r ∈ fullArenaClauseRefsCore s1.core; rw [hrefs]; exact hr),
    hsp.2.2.2.2.2⟩, hrefs, rfl⟩

theorem ra_overwriteGarb_l0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} {cref : Nat}
    (hsp : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0) (hsc : s'.scratch = s.scratch)
    (hc : { s'.core with
        arena := s.core.arena, lit_mark := s.core.lit_mark,
        arena_garbage := s.core.arena_garbage } = s.core)
    (href : cref ∈ fullArenaClauseRefs s) (har'_len : s'.core.arena.length = c.arena_cap)
    (hlm'_len : s'.core.lit_mark.length = 2 * c.max_vars)
    (hlm'_zero : ∀ x < 2 * c.max_vars, s'.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hhdr' : s'.core.arena[cref]? = some (fullArenaHdr s cref ||| 0x00080000#32))
    (hsz' : s'.core.arena[cref + 2]? = s.core.arena[cref + 2]?)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      s'.core.arena[i]? = s.core.arena[i]?) :
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
      s'.core.arena_len = s.core.arena_len := by
  have hcl := hsp.1.core_ok; have ha := hsp.2.1.arena; have hwf := ha.refs_wf cref href
  have hget_c : s.core.arena[cref]? = some (fullArenaHdr s cref) := by
    have : cref < s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
  refine ra_arenaBlockReplace_l0 hsp hl0 hsc hc href
    har'_len hlm'_len hlm'_zero hout ?_ (by rw [hsz']; exact ⟨hwf.2.1, Nat.le_refl _⟩) ?_ ?_
  · have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
    have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
      unfold fullArenaClauseSizeCore at hwf; omega
    unfold fullArenaNextOff
    simp only [h1, ↓reduceIte, hsz', h2, hhdr', Option.getD_some, bit23_or_garb]
    rw [hget_c, Option.getD_some]; split
    · exact fullArenaSkipShrk_congr fun i hi _ => hout i (Or.inr hi)
    · rfl
  · intro hsh; rw [hhdr', Option.getD_some, bit23_or_garb] at hsh
    obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref href hsh
    refine ⟨t, by rw [hsz']; exact ht1, ht2, ?_⟩
    rw [hout t (Or.inr (by
      change cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat ≤ t; exact ht1))]
    exact hsent
  · intro hng; rw [hhdr', Option.getD_some] at hng; exact absurd hng (bit19_or_garb_ne0 _)

theorem ra_inPlaceShrink_l0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} {cref nsz : Nat}
    (hsp : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0) (hsc : s'.scratch = s.scratch)
    (hc : { s'.core with arena := s.core.arena, lit_mark := s.core.lit_mark } = s.core)
    (hcref : cref ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_le : nsz ≤ fullArenaClauseSize s cref)
    (har'_len : s'.core.arena.length = c.arena_cap)
    (hlm'_len : s'.core.lit_mark.length = 2 * c.max_vars)
    (hlm'_zero : ∀ x < 2 * c.max_vars, s'.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hhdr' : s'.core.arena[cref]? = some
      (if nsz < fullArenaClauseSize s cref ∧ (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 then
        fullArenaHdr s cref ||| 0x00800000#32 else fullArenaHdr s cref))
    (hsz' : s'.core.arena[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_old : ∀ j, nsz ≤ j → j < fullArenaClauseSize s cref - 1 →
      s'.core.arena[cref + 3 + j]? = s.core.arena[cref + 3 + j]?)
    (hlast_sent : nsz < fullArenaClauseSize s cref →
      (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 →
      s'.core.arena[cref + 3 + fullArenaClauseSize s cref - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : nsz < fullArenaClauseSize s cref →
      (fullArenaHdr s cref &&& 0x00800000#32) ≠ 0#32 →
      s'.core.arena[cref + 3 + fullArenaClauseSize s cref - 1]? =
        s.core.arena[cref + 3 + fullArenaClauseSize s cref - 1]?)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      s'.core.arena[i]? = s.core.arena[i]?)
    (hlits_lt' : ∀ j < nsz, (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hpw' : ∀ i j, i < j → j < nsz →
      (s'.core.arena[cref + 3 + i]?.getD 0#32).toNat / 2 ≠
      (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat / 2)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz).map fun j => (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat))) :
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
      s'.core.arena_len = s.core.arena_len := by
  have hcl := hsp.1.core_ok; have ha := hsp.2.1.arena; have hwf := ha.refs_wf cref hcref
  let old_sz := fullArenaClauseSizeCore s.core cref
  have hold_eq : fullArenaClauseSize s cref = old_sz := rfl
  have hwf' : cref + 3 ≤ s.core.arena_len ∧ 3 ≤ old_sz ∧
      cref + 3 + old_sz ≤ fullArenaNextOff s.core.arena s.core.arena_len cref ∧
      fullArenaNextOff s.core.arena s.core.arena_len cref ≤ s.core.arena_len ∧
      (fullArenaNextOff s.core.arena s.core.arena_len cref = s.core.arena_len ∨
        fullArenaNextOff s.core.arena s.core.arena_len cref + 3 ≤ s.core.arena_len) := hwf
  rw [hold_eq] at hnsz_le hhdr' hpad_old hlast_sent hlast_keep hout
  have hnsz_lt32 : nsz < 2 ^ 32 := by
    have := (s.core.arena[cref + 2]?.getD 0#32).isLt
    have hold_sz_eq : (s.core.arena[cref + 2]?.getD 0#32).toNat = old_sz := rfl; omega
  have hsz_n : (s'.core.arena[cref + 2]?.getD 0#32).toNat = nsz := by
    rw [hsz', Option.getD_some, ra_bv32_ofNat_toNat_lt hnsz_lt32]
  have hold_ne : ∀ j, j < old_sz →
      s.core.arena[cref + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hbd : cref + 3 + old_sz ≤ s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    have hlt_j : cref + 3 + j < s.core.arena.length := by omega
    rw [List.getElem?_eq_getElem hlt_j, Option.getD_some]
    have hlt_v :=
      ha.lits_lt cref hcref hng _ ((mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, hj, rfl⟩)
    have hmx := c.hmaxv; have hcv := hcl.cur_vars_le; unfold dimacsBound at hmx
    intro heq; rw [heq] at hlt_v; simp at hlt_v; omega
  refine ra_arenaBlockReplace_l0 hsp hl0 hsc (ra_core_eq_of_arena_lm hc)
    hcref har'_len hlm'_len hlm'_zero hout ?_ (by rw [hsz_n]; exact ⟨hnsz3, hnsz_le⟩) ?_ ?_
  · have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
    have h2 : ¬ (cref + 3 + old_sz > s.core.arena_len) := by omega
    have h2' : ¬ (cref + 3 + nsz > s.core.arena_len) := by omega
    have hold_sz_eq : (s.core.arena[cref + 2]?.getD 0#32).toNat = old_sz := rfl
    have hhdr_get : fullArenaHdr s cref = s.core.arena[cref]?.getD 0#32 := rfl
    rw [hhdr_get] at hhdr'
    by_cases hcond : nsz < old_sz ∧ (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
    · simp only [hcond.1, hcond.2, and_self, ite_true] at hhdr'
      have hsh0 : (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32 := hcond.2
      unfold fullArenaNextOff
      simp only [h1, h2, h2', hsz_n, hold_sz_eq, hhdr', Option.getD_some, hsh0,
        bit23_or_shrk, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]
      have hts := fullArenaSkipShrk_of_first_sentinel (ar := s'.core.arena)
        (alen := s.core.arena_len) (t := cref + 3 + old_sz - 1)
        (fuel := s.core.arena_len - (cref + 3 + nsz)) (p := cref + 3 + nsz) (by omega)
        (by omega) (hlast_sent hcond.1 hcond.2)
        (fun i hi1 hi2 => by
          have hj : i = cref + 3 + (i - (cref + 3)) := by omega
          rw [hj, hpad_old (i - (cref + 3)) (by omega) (by omega)]
          exact hold_ne (i - (cref + 3)) (by omega)) (by omega)
      have h3old : 3 ≤ old_sz := hwf'.2.1; omega
    · simp only [hcond, ite_false] at hhdr'
      by_cases hsh0 : (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
      · have hnsz_eq : nsz = old_sz := by
          have : ¬ nsz < old_sz := fun hlt => hcond ⟨hlt, hsh0⟩; omega
        unfold fullArenaNextOff
        simp only [h1, h2, hsz_n, hold_sz_eq, hhdr', Option.getD_some, hsh0, ↓reduceIte, hnsz_eq]
        rfl
      · obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref hcref hsh0
        obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent, ht0_first⟩ :=
          fullArenaSkipShrk_first_sentinel (ar := s.core.arena)
            (alen := s.core.arena_len) (t := t) (fuel := s.core.arena_len - (cref + 3 + old_sz))
            (p := cref + 3 + old_sz) ht1 ht2 hsent (by omega)
        unfold fullArenaNextOff
        simp only [h1, h2, h2', hsz_n, hold_sz_eq, hhdr', Option.getD_some, hsh0, ne_eq,
          not_false_eq_true, ↓reduceIte]
        rw [ht0_nxt]
        refine fullArenaSkipShrk_of_first_sentinel (ar := s'.core.arena)
          (alen := s.core.arena_len) (t := t0) (fuel := s.core.arena_len - (cref + 3 + nsz))
          (p := cref + 3 + nsz) (by omega) (by omega)
          (by rw [hout t0 (Or.inr ht0_lo)]; exact ht0_sent) (fun i hi1 hi2 => ?_) (by omega)
        by_cases hmid : i < cref + 3 + old_sz
        · by_cases hlast : i = cref + 3 + old_sz - 1
          · subst i; by_cases hlt_n : nsz < old_sz
            · rw [hlast_keep hlt_n hsh0,
                show cref + 3 + old_sz - 1 = cref + 3 + (old_sz - 1) by omega]
              exact hold_ne (old_sz - 1) (by omega)
            · omega
          · have hj : i = cref + 3 + (i - (cref + 3)) := by omega
            rw [hj, hpad_old (i - (cref + 3)) (by omega) (by omega)]
            exact hold_ne (i - (cref + 3)) (by omega)
        · rw [hout i (Or.inr (by omega))]; exact ht0_first i (by omega) hi2
  · intro hsh; rw [hsz_n]; rw [hhdr', Option.getD_some] at hsh
    split at hsh
    · rename_i hcond; exact ⟨cref + 3 + old_sz - 1, by omega, by omega, hlast_sent hcond.1 hcond.2⟩
    · obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref hcref hsh
      exact ⟨t, by omega, ht2, by rw [hout t (Or.inr ht1)]; exact hsent⟩
  · intro _; rw [hsz_n]; exact ⟨hlits_lt', hpw', hent'⟩

structure RaOuterCore (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (p : BitVec 64) (st : FullState) : Prop where
  sp : FullSparseInvW c F0 F_cur st
  cv_eq : st.core.cur_vars = s0.core.cur_vars
  hl0 : st.core.cur_level = 0
  fuel_eq : st.core.fuel = s0.core.fuel
  repr_eq : st.core.repr = s0.core.repr
  alen_eq : st.core.arena_len = s0.core.arena_len
  p_pos : p.toNat = st.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs st

structure RaLoop2Core (c : FullCfg) (st st2 : FullState)
    (p : BitVec 64) (sz : Nat) (nsz : BitVec 32) : Prop where
  len : st2.LengthsOk c
  sc_eq : st2.scratch = st.scratch
  core_eq : { st2.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core
  nsz_le : nsz.toNat ≤ sz
  pad : ∀ j, nsz.toNat ≤ j → j < sz →
    st2.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?
  out : ∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz ≤ i → st2.core.arena[i]? = st.core.arena[i]?
  lits_lt : ∀ j < sz, (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars
  pw : ∀ i j, i < j → j < nsz.toNat →
    (st2.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
    (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2
  lm : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔
    ∃ m < nsz.toNat, (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat = x
  mrk : ∀ v < c.max_vars, st2.core.mrk[v]?.getD 0#8 = 0#8

structure RaLoop2Inv (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (p : BitVec 64) (sz : Nat) (k nsz : BitVec 32) (st2 : FullState) : Prop where
  core : RaLoop2Core c st st2 p sz nsz
  k_le : k.toNat ≤ sz
  nsz_k : nsz.toNat ≤ k.toNat
  nsz_pos : 0 < k.toNat → 1 ≤ nsz.toNat
  ent : ∀ j < k.toNat, ∃ m < nsz.toNat,
    LitEquiv (cnfOfClauses F_cur)
      (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
      (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat

structure RaLoop2Brk (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (p : BitVec 64) (sz : Nat) (taut : Bool) (nsz : BitVec 32) (st2 : FullState) : Prop where
  core : RaLoop2Core c st st2 p sz nsz
  nsz_pos : taut = false → 1 ≤ nsz.toNat
  ent : taut = false → ∀ j < sz, ∃ m < nsz.toNat,
    LitEquiv (cnfOfClauses F_cur)
      (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
      (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat

structure RaDoneCore (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st st4 : FullState) : Prop where
  sp : FullSparseInvW c F0 F_cur st4
  cv_eq : st4.core.cur_vars = s0.core.cur_vars
  hl0 : st4.core.cur_level = 0
  fuel_eq : st4.core.fuel = s0.core.fuel
  repr_eq : st4.core.repr = s0.core.repr
  alen_eq : st4.core.arena_len = s0.core.arena_len
  refs_eq : fullArenaClauseRefs st4 = fullArenaClauseRefs st

theorem ra_push_step {c : FullCfg} {F_cur : List (List Nat)}
    {st st2 : FullState} {p : BitVec 64} {sz : Nat} {k nsz l2 rl2 : BitVec 32}
    (hk_lt : k.toNat < sz) (hk1 : (k + 1#32).toNat = k.toNat + 1)
    (hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1)
    (hc2 : RaLoop2Core c st st2 p sz nsz)
    (hnsz_le : nsz.toNat ≤ k.toNat)
    (hent2 : ∀ j < k.toNat, ∃ m < nsz.toNat,
      LitEquiv (cnfOfClauses F_cur)
        (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
        (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat)
    (hcv_le : st.core.cur_vars ≤ c.max_vars)
    (hp_bd : p.toNat + 3 + sz ≤ st2.core.arena.length)
    (hl2_orig_eq : st2.core.arena[p.toNat + 3 + k.toNat]? = some l2)
    (hrl2_lt_v : rl2.toNat < 2 * st.core.cur_vars)
    (hrl2_eqv : LitEquiv (cnfOfClauses F_cur) l2.toNat rl2.toNat)
    (hlm_neg0 : st2.core.lit_mark[rl2.toNat ^^^ 1]?.getD 0#8 = 0#8)
    (hlm_pos0 : st2.core.lit_mark[rl2.toNat]?.getD 0#8 = 0#8) :
    RaLoop2Inv c F_cur st p sz (k + 1#32) (nsz + 1#32)
      { st2 with core := { st2.core with
        lit_mark := st2.core.lit_mark.set rl2.toNat 1#8,
        arena := st2.core.arena.set (p.toNat + 3 + nsz.toNat) rl2 } } := by
  have hcl2 := hc2.len.core_ok; have harl2 := hcl2.arena_len_arr; have hlml2 := hcl2.lit_mark_len
  let lm2' := st2.core.lit_mark.set rl2.toNat 1#8
  let ar2' := st2.core.arena.set (p.toNat + 3 + nsz.toNat) rl2
  let st2' : FullState := { st2 with core := { st2.core with lit_mark := lm2', arena := ar2' } }
  have hcl2' : ({ st2 with core := { st2.core with lit_mark := lm2', arena := ar2' } } :
      FullState).core.LengthsOk c :=
    { hcl2 with arena_len_arr := by simp [ar2', harl2], lit_mark_len := by simp [lm2', hlml2] }
  refine ⟨⟨⟨hcl2', hc2.len.scratch_ok⟩,
      hc2.sc_eq, hc2.core_eq, by rw [hnsz1]; omega, ?_, ?_, ?_, ?_, ?_,
      by simpa [st2'] using hc2.mrk⟩,
    by rw [hk1]; omega, by rw [hk1, hnsz1]; omega, fun _ => by rw [hnsz1]; omega, ?_⟩
  · intro j hj1 hj2; dsimp only [st2', ar2']
    rw [List.getElem?_set_ne (by rw [hnsz1] at hj1; omega)]; exact hc2.pad j (by omega) hj2
  · intro i hi; dsimp only [st2', ar2']; rw [List.getElem?_set_ne (by omega)]; exact hc2.out i hi
  · intro j hj; dsimp only [st2', ar2']
    by_cases hjn : j = nsz.toNat
    · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hrl2_lt_v
    · rw [List.getElem?_set_ne (by omega)]; exact hc2.lits_lt j hj
  · intro i j hij hj; dsimp only [st2', ar2']; rw [hnsz1] at hj
    by_cases hj_last : j = nsz.toNat
    · subst hj_last
      rw [List.getElem?_set_self (by omega), List.getElem?_set_ne (by omega), Option.getD_some]
      intro hdv; rcases (ra_litVar_eq_iff _ rl2.toNat).mp hdv with heq | heq
      · exact (hc2.lm rl2.toNat (by omega)).mpr ⟨i, by omega, heq⟩ hlm_pos0
      · have hnx := ra_litNeg_lt_two_mul hrl2_lt_v
        exact (hc2.lm (rl2.toNat ^^^ 1) (by omega)).mpr ⟨i, by omega, heq⟩ hlm_neg0
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hc2.pw i j hij (by omega)
  · intro x hx; dsimp only [st2', lm2', ar2']; rw [hnsz1]; constructor
    · intro hnz
      by_cases hxr : x = rl2.toNat
      · subst hxr; refine ⟨nsz.toNat, by omega, ?_⟩
        rw [List.getElem?_set_self (by omega), Option.getD_some]
      · rw [List.getElem?_set_ne (Ne.symm hxr)] at hnz
        obtain ⟨m', hm', hm'_eq⟩ := (hc2.lm x hx).mp hnz
        refine ⟨m', by omega, ?_⟩; rw [List.getElem?_set_ne (by omega)]; exact hm'_eq
    · rintro ⟨m', hm', hm'_eq⟩
      by_cases hmn : m' = nsz.toNat
      · subst hmn; rw [List.getElem?_set_self (by omega), Option.getD_some] at hm'_eq
        subst hm'_eq; rw [List.getElem?_set_self (by rw [hlml2]; exact hx), Option.getD_some]
        decide
      · rw [List.getElem?_set_ne (by omega)] at hm'_eq
        have hnz := (hc2.lm x hx).mpr ⟨m', by omega, hm'_eq⟩
        by_cases hxr : x = rl2.toNat
        · subst hxr; rw [List.getElem?_set_self (by rw [hlml2]; exact hx), Option.getD_some]
          decide
        · rw [List.getElem?_set_ne (Ne.symm hxr)]; exact hnz
  · intro j hj; dsimp only [st2', ar2']; rw [hk1] at hj; rw [hnsz1]
    by_cases hjk : j = k.toNat
    · subst hjk; refine ⟨nsz.toNat, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      have hpad_k := hc2.pad k.toNat hnsz_le hk_lt
      have hl2_orig : (st.core.arena[p.toNat + 3 + k.toNat]?.getD 0#32).toNat = l2.toNat := by
        rw [← hpad_k, hl2_orig_eq, Option.getD_some]
      rwa [hl2_orig]
    · obtain ⟨m', hm', heqv⟩ := hent2 j (by omega)
      refine ⟨m', by omega, ?_⟩; rw [List.getElem?_set_ne (by omega)]; exact heqv

theorem ra_shrink_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st3 : FullState} {p : BitVec 64} {sz nsz : Nat} {ar4 : List (BitVec 32)}
    (ho : RaOuterCore c F0 F_cur s0 p st)
    (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st p.toNat = false) (hsz_eq : sz = fullArenaClauseSize st p.toNat)
    (hnsz3 : 3 ≤ nsz) (hnsz_le : nsz ≤ sz) (hsc3 : st3.scratch = st.scratch)
    (hcore3 : { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core)
    (har4_len : ar4.length = c.arena_cap)
    (hlm3_len : st3.core.lit_mark.length = 2 * c.max_vars)
    (hlm3_zero : ∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hhdr4 : ar4[p.toNat]? = some
      (if nsz < fullArenaClauseSize st p.toNat ∧
          (fullArenaHdr st p.toNat &&& 0x00800000#32) = 0#32 then
        fullArenaHdr st p.toNat ||| 0x00800000#32 else fullArenaHdr st p.toNat))
    (hsz4 : ar4[p.toNat + 2]? = some (BitVec.ofNat 32 nsz))
    (hlast_sent : nsz < fullArenaClauseSize st p.toNat →
      (fullArenaHdr st p.toNat &&& 0x00800000#32) = 0#32 →
      ar4[p.toNat + 3 + fullArenaClauseSize st p.toNat - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : nsz < fullArenaClauseSize st p.toNat →
      (fullArenaHdr st p.toNat &&& 0x00800000#32) ≠ 0#32 →
      ar4[p.toNat + 3 + fullArenaClauseSize st p.toNat - 1]? =
        st.core.arena[p.toNat + 3 + fullArenaClauseSize st p.toNat - 1]?)
    (har4_eq : ∀ i, i ≠ p.toNat → i ≠ p.toNat + 1 → i ≠ p.toNat + 2 →
      (nsz < sz → i ≠ p.toNat + 3 + sz - 1) → ar4[i]? = st3.core.arena[i]?)
    (har3_pad : ∀ j, nsz ≤ j → j < sz →
      st3.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?)
    (har3_out : ∀ i, i < p.toNat ∨ p.toNat + 3 + sz ≤ i → st3.core.arena[i]? = st.core.arena[i]?)
    (har3_lt : ∀ j < sz, (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (har3_pw : ∀ i j, i < j → j < nsz →
      (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
      (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2)
    (hent_n : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((List.range nsz).map fun j => (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat))) :
    RaDoneCore c F0 F_cur s0 st { st3 with core := { st3.core with arena := ar4 } } := by
  let st4 : FullState := { st3 with core := { st3.core with arena := ar4 } }
  have hwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref
  have hsz3 : 3 ≤ sz := by rw [hsz_eq]; exact hwf.2.1
  have hcore4' :
      { st4.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core := by
    rcases st with ⟨c0, _⟩; rcases st3 with ⟨c3, _⟩; cases c0; cases c3; cases hcore3; rfl
  have har4_s : st4.core.arena = ar4 := rfl
  have hmap_eq : ((List.range nsz).map fun j => (ar4[p.toNat + 3 + j]?.getD 0#32).toNat) =
      ((List.range nsz).map fun j => (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat) :=
    List.map_congr_left fun j hj => by
      have hj' := List.mem_range.mp hj
      rw [har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
  obtain ⟨hsp4, hrefs4, hal4⟩ := ra_inPlaceShrink_l0 (s' := st4)
    ho.sp ho.hl0 hsc3 hcore4'
    hp_ref hng hnsz3 (hsz_eq ▸ hnsz_le) (by rw [har4_s]; exact har4_len) hlm3_len hlm3_zero
    (by rw [har4_s]; exact hhdr4) (by rw [har4_s]; exact hsz4)
    (fun j hj1 hj2 => by
      rw [hsz_eq] at hnsz_le; rw [← hsz_eq] at hj2
      rw [har4_s, har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
      exact har3_pad j hj1 (by omega))
    (by rw [har4_s]; exact hlast_sent) (by rw [har4_s]; exact hlast_keep)
    (fun i hi => by
      rw [← hsz_eq] at hi
      rw [har4_s, har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
      exact har3_out i hi)
    (fun j hj => by
      rw [har4_s, har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
      exact har3_lt j (by omega))
    (fun i j hij hj => by
      rw [har4_s, har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega),
        har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
      exact har3_pw i j hij hj)
    (by rw [har4_s, hmap_eq]; exact hent_n)
  exact ⟨hsp4, (congrArg FullCoreState.cur_vars hcore4').trans ho.cv_eq,
    (congrArg FullCoreState.cur_level hcore4').trans ho.hl0,
    (congrArg FullCoreState.fuel hcore4').trans ho.fuel_eq,
    (congrArg FullCoreState.repr hcore4').trans ho.repr_eq, hal4.trans ho.alen_eq, hrefs4⟩

theorem ra_lm_zero {lm : List (BitVec 8)} {i j : Nat}
    {hi : i < lm.length} {hj : j < lm.length} (hij : i = j)
    (hc : BitVec.setWidth 32 (lm[j]'hj) = 0#32) : lm[i]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some,
    show lm[i]'hi = lm[j]'hj by subst hij; rfl]
  exact bv8_setWidth32_eq_zero hc

theorem ra_lm_ne {lm : List (BitVec 8)} {i j : Nat}
    {hi : i < lm.length} {hj : j < lm.length} (hij : i = j)
    (hc : ¬ BitVec.setWidth 32 (lm[j]'hj) = 0#32) : lm[i]?.getD 0#8 ≠ 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some,
    show lm[i]'hi = lm[j]'hj by subst hij; rfl]
  intro heq; exact hc (congrArg (BitVec.setWidth 32) heq)

structure RaClear3Core (c : FullCfg) (st st2 : FullState) (p : BitVec 64)
    (nsz : Nat) (k3 : BitVec 32) (st3 : FullState) : Prop where
  len : st3.LengthsOk c
  sc_eq : st3.scratch = st.scratch
  core_eq : { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core
  ar_eq : st3.core.arena = st2.core.arena
  k3_le : k3.toNat ≤ nsz
  lm : ∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
    ∃ i, k3.toNat ≤ i ∧ i < nsz ∧ (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat = x
  mrk : ∀ v < c.max_vars, st3.core.mrk[v]?.getD 0#8 = 0#8

theorem ra_clear3_init {c : FullCfg} {F_cur : List (List Nat)} {st st2 : FullState}
    {p : BitVec 64} {sz : Nat} {taut : Bool} {nsz : BitVec 32}
    (hb : RaLoop2Brk c F_cur st p sz taut nsz st2) :
    RaClear3Core c st st2 p nsz.toNat 0#32 st2 :=
  ⟨hb.core.len, hb.core.sc_eq, hb.core.core_eq, rfl, Nat.zero_le _,
   fun x hx hnz => by
     obtain ⟨m', hm1', hm2'⟩ := (hb.core.lm x hx).mp hnz
     exact ⟨m', Nat.zero_le _, hm1', hm2'⟩,
   hb.core.mrk⟩

theorem ra_clear3_step {c : FullCfg} {F_cur : List (List Nat)} {st st2 st3 : FullState}
    {p : BitVec 64} {sz : Nat} {taut : Bool} {nsz k3 : BitVec 32}
    (hb : RaLoop2Brk c F_cur st p sz taut nsz st2)
    (hc3 : RaClear3Core c st st2 p nsz.toNat k3 st3)
    (hk3_lt : k3.toNat < nsz.toNat) (hk3_1 : (k3 + 1#32).toNat = k3.toNat + 1)
    (hpk3_eq : (p + 3#64 + BitVec.setWidth 64 k3).toNat = p.toNat + 3 + k3.toNat)
    (hp_blk : p.toNat + 3 + sz ≤ c.arena_cap)
    (hcv_le : st.core.cur_vars ≤ c.max_vars) :
    ∃ (hpk3_lt : (p + 3#64 + BitVec.setWidth 64 k3).toNat < st3.core.arena.length),
    let l := st3.core.arena[(p + 3#64 + BitVec.setWidth 64 k3).toNat]'hpk3_lt
    (BitVec.setWidth 64 l).toNat < st3.core.lit_mark.length ∧
    RaClear3Core c st st2 p nsz.toNat (k3 + 1#32)
      { st3 with core := { st3.core with
        lit_mark := st3.core.lit_mark.set (BitVec.setWidth 64 l).toNat 0#8 } } := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl3 := hc3.len.core_ok; have harl3 := hcl3.arena_len_arr; have hlml3 := hcl3.lit_mark_len
  have hnsz_le := hb.core.nsz_le
  have hpk3_lt : (p + 3#64 + BitVec.setWidth 64 k3).toNat < st3.core.arena.length := by
    rw [hpk3_eq, harl3]; omega
  let l := st3.core.arena[(p + 3#64 + BitVec.setWidth 64 k3).toNat]'hpk3_lt
  have hrl3_lt_v : l.toNat < 2 * st.core.cur_vars := by
    have hg := hb.core.lits_lt k3.toNat (by omega)
    rw [← hc3.ar_eq, ← hpk3_eq, List.getElem?_eq_getElem hpk3_lt, Option.getD_some] at hg
    exact hg
  have hrl3_lt_lm : (BitVec.setWidth 64 l).toNat < st3.core.lit_mark.length := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlml3]; omega
  refine ⟨hpk3_lt, hrl3_lt_lm, ?_⟩
  let lm3' := st3.core.lit_mark.set (BitVec.setWidth 64 l).toNat 0#8
  let st3' : FullState := { st3 with core := { st3.core with lit_mark := lm3' } }
  have hset_idx : (BitVec.setWidth 64 l).toNat =
      (st3.core.arena[p.toNat + 3 + k3.toNat]'(by rw [harl3]; omega)).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    exact congrArg BitVec.toNat (bv32_getElem_congr hpk3_eq)
  have hlm3' : ∀ x < 2 * c.max_vars, st3'.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
      ∃ i, (k3 + 1#32).toNat ≤ i ∧ i < nsz.toNat ∧
        (st3'.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat = x := by
    intro x hx hnz; dsimp only [st3', lm3'] at hnz; rw [hset_idx] at hnz
    by_cases hxeq :
        x = (st3.core.arena[p.toNat + 3 + k3.toNat]'(by rw [harl3]; omega)).toNat
    · rw [hxeq, List.getElem?_set_self (by rw [hlml3, ← hxeq]; exact hx),
        Option.getD_some] at hnz
      exact absurd rfl hnz
    · rw [List.getElem?_set_ne (Ne.symm hxeq)] at hnz
      obtain ⟨i, hi1, hi2, hieq⟩ := hc3.lm x hx hnz
      have hine : i ≠ k3.toNat := by
        intro hieq'; subst hieq'
        rw [List.getElem?_eq_getElem (by rw [harl3]; omega), Option.getD_some] at hieq
        exact hxeq hieq.symm
      exact ⟨i, by rw [hk3_1]; omega, hi2, hieq⟩
  exact ⟨⟨{ hcl3 with lit_mark_len := by simp [hlml3] }, hc3.len.scratch_ok⟩,
    hc3.sc_eq, hc3.core_eq, hc3.ar_eq, by rw [hk3_1]; omega, hlm3',
    by simpa [st3'] using hc3.mrk⟩

theorem ra_clear3_done {c : FullCfg} {F_cur : List (List Nat)} {st st2 st3 : FullState}
    {p : BitVec 64} {sz : Nat} {taut : Bool} {nsz k3 : BitVec 32}
    (hb : RaLoop2Brk c F_cur st p sz taut nsz st2)
    (hc3 : RaClear3Core c st st2 p nsz.toNat k3 st3) (hnl : ¬ k3.toNat < nsz.toNat) :
    (∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 = 0#8) ∧
    (∀ j < sz, (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars) ∧
    (∀ i j, i < j → j < nsz.toNat →
      (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
      (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2) ∧
    (∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz ≤ i → st3.core.arena[i]? = st.core.arena[i]?) ∧
    (∀ j, nsz.toNat ≤ j → j < sz →
      st3.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?) ∧
    (taut = false →
      ∀ j < sz, ∃ m < nsz.toNat, LitEquiv (cnfOfClauses F_cur)
        (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
        (st3.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat) := by
  have hk3_eq : k3.toNat = nsz.toNat := by have := hc3.k3_le; omega
  have har3 := hc3.ar_eq
  refine ⟨fun x hx => Classical.byContradiction fun hnz => by
      obtain ⟨i, hi1, hi2, _⟩ := hc3.lm x hx hnz; omega,
    fun j hj => har3 ▸ hb.core.lits_lt j hj,
    fun i j hij hj => har3 ▸ hb.core.pw i j hij hj,
    fun i hi => har3 ▸ hb.core.out i hi,
    fun j hj1 hj2 => har3 ▸ hb.core.pad j hj1 hj2,
    fun ht j hj => har3 ▸ hb.ent ht j hj⟩

theorem ra_garb_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st3 : FullState} {p : BitVec 64} {sz : Nat} {hdr sz32 : BitVec 32}
    (ho : RaOuterCore c F0 F_cur s0 p st)
    (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hsz_eq : sz32.toNat = fullArenaClauseSize st p.toNat)
    (hhdr_eq : fullArenaHdr st p.toNat = hdr)
    (hsc3 : st3.scratch = st.scratch)
    (hcore3 : { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core)
    (harl3 : st3.core.arena.length = c.arena_cap)
    (hlml3 : st3.core.lit_mark.length = 2 * c.max_vars)
    (hlm3_zero : ∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 = 0#8)
    (har3_out : ∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz ≤ i →
      st3.core.arena[i]? = st.core.arena[i]?)
    (hsz_val : sz = sz32.toNat) :
    ∃ (_hp_lt3 : p.toNat < st3.core.arena.length),
    let st4 : FullState :=
      { st3 with core := { st3.core with
        arena := st3.core.arena.set p.toNat (hdr ||| 0x00080000#32)
        arena_garbage := st3.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz32 } }
    FullSparseInvW c F0 F_cur st4 ∧ st4.core.cur_vars = s0.core.cur_vars ∧
    st4.core.cur_level = 0 ∧ st4.core.fuel = s0.core.fuel ∧
    st4.core.repr = s0.core.repr ∧ st4.core.arena_len = s0.core.arena_len ∧
    fullArenaClauseRefs st4 = fullArenaClauseRefs st ∧
    RaDoneCore c F0 F_cur s0 st st4 := by
  have hcl := ho.sp.1.core_ok; have hwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref
  have hp_lt3 : p.toNat < st3.core.arena.length := by
    rw [harl3]; have := hcl.arena_len_le; omega
  have hsz3 : 3 ≤ sz := by rw [hsz_val, hsz_eq]; exact hwf.2.1
  let st4 : FullState :=
    { st3 with core := { st3.core with
      arena := st3.core.arena.set p.toNat (hdr ||| 0x00080000#32)
      arena_garbage := st3.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz32 } }
  obtain ⟨hsp4, hrefs4, _⟩ := ra_overwriteGarb_l0 (s' := st4) ho.sp ho.hl0 hsc3
    (ra_replace_ag_eq hcore3) hp_ref
    (by show st4.core.arena.length = c.arena_cap; simp [st4, harl3])
    hlml3 hlm3_zero
    (by show st4.core.arena[p.toNat]? = _; dsimp only [st4]
        rw [List.getElem?_set_self hp_lt3, hhdr_eq])
    (by show st4.core.arena[p.toNat + 2]? = _; dsimp only [st4]
        rw [List.getElem?_set_ne (by omega : p.toNat ≠ p.toNat + 2)]
        exact har3_out (p.toNat + 2) (Or.inl (by omega)))
    (fun i hi => by
      show st4.core.arena[i]? = _
      have hne : p.toNat ≠ i := by omega
      dsimp only [st4]; rw [List.getElem?_set_ne hne]
      exact har3_out i (hi.elim (fun h1 => Or.inl (by omega))
        (fun h2 => Or.inr (by rw [hsz_val, hsz_eq]; exact h2))))
  have hcv4 : st4.core.cur_vars = s0.core.cur_vars :=
    (congrArg FullCoreState.cur_vars hcore3).trans ho.cv_eq
  have hl04 : st4.core.cur_level = 0 := (congrArg FullCoreState.cur_level hcore3).trans ho.hl0
  have hfl4 : st4.core.fuel = s0.core.fuel := (congrArg FullCoreState.fuel hcore3).trans ho.fuel_eq
  have hrp4 : st4.core.repr = s0.core.repr :=
    (congrArg FullCoreState.repr hcore3).trans ho.repr_eq
  have hal4' : st4.core.arena_len = s0.core.arena_len :=
    (congrArg FullCoreState.arena_len hcore3).trans ho.alen_eq
  exact ⟨hp_lt3, hsp4, hcv4, hl04, hfl4, hrp4, hal4', hrefs4,
    ⟨hsp4, hcv4, hl04, hfl4, hrp4, hal4', hrefs4⟩⟩

theorem ra_addbin_prep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st3 st4 st5 : FullState} {p : BitVec 64} {sz : Nat} {sz32 : BitVec 32}
    (ho : RaOuterCore c F0 F_cur s0 p st) (hsp5 : FullSparseInvW c F0 F_cur st5)
    (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st p.toNat = false)
    (hsz_eq : sz32.toNat = fullArenaClauseSize st p.toNat) (hsz_val : sz = sz32.toNat)
    (harl3 : st3.core.arena.length = c.arena_cap)
    (har3_eq : st3.core.arena = st5.core.arena → False → False)
    (har5_eq : st5.core.arena = st4.core.arena)
    (hst4_ar : st4.core.arena =
      st3.core.arena.set p.toNat (fullArenaHdr st p.toNat ||| 0x00080000#32))
    (har3_out : ∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz ≤ i →
      st3.core.arena[i]? = st.core.arena[i]?)
    (hp3_eq : (p + 3#64).toNat = p.toNat + 3) (hp4_eq : (p + 4#64).toNat = p.toNat + 4)
    (hp_blk : p.toNat + 3 + sz ≤ c.arena_cap)
    (hent2 : ∀ j < sz, ∃ m < 2, LitEquiv (cnfOfClauses F_cur)
      (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
      (st3.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat) :
    ∃ (hp3_lt5 : (p + 3#64).toNat < st5.core.arena.length)
      (hp4_lt5 : (p + 4#64).toNat < st5.core.arena.length),
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      [(st5.core.arena[(p + 3#64).toNat]'hp3_lt5).toNat,
       (st5.core.arena[(p + 4#64).toNat]'hp4_lt5).toNat]) := by
  have _ := har3_eq; have _ := har3_out
  have hcl := ho.sp.1.core_ok; have harl := hcl.arena_len_arr
  have hwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref
  have hsz3 : 3 ≤ sz := by rw [hsz_val, hsz_eq]; exact hwf.2.1
  have harl5 := hsp5.1.core_ok.arena_len_arr
  have hp3_lt5 : (p + 3#64).toNat < st5.core.arena.length := by rw [hp3_eq, harl5]; omega
  have hp4_lt5 : (p + 4#64).toNat < st5.core.arena.length := by rw [hp4_eq, harl5]; omega
  have hget_p3 : st5.core.arena[(p + 3#64).toNat]'hp3_lt5 =
      st3.core.arena[p.toNat + 3]'(by rw [harl3]; omega) := by
    have hq : st5.core.arena[(p + 3#64).toNat]? = st3.core.arena[p.toNat + 3]? := by
      rw [hp3_eq, har5_eq, hst4_ar, List.getElem?_set_ne (by omega)]
    rw [List.getElem?_eq_getElem hp3_lt5, List.getElem?_eq_getElem (by rw [harl3]; omega)] at hq
    exact Option.some.inj hq
  have hget_p4 : st5.core.arena[(p + 4#64).toNat]'hp4_lt5 =
      st3.core.arena[p.toNat + 4]'(by rw [harl3]; omega) := by
    have hq : st5.core.arena[(p + 4#64).toNat]? = st3.core.arena[p.toNat + 4]? := by
      rw [hp4_eq, har5_eq, hst4_ar, List.getElem?_set_ne (by omega)]
    rw [List.getElem?_eq_getElem hp4_lt5, List.getElem?_eq_getElem (by rw [harl3]; omega)] at hq
    exact Option.some.inj hq
  refine ⟨hp3_lt5, hp4_lt5, entails_clause_subst (fun l hl => ?_)
    (ho.sp.2.1.arena.entails p.toNat hp_ref hng)⟩
  obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff (k := st.core)
    (by have := hcl.arena_len_le; rw [harl]; omega)).mp hl
  have hsz_core : fullArenaClauseSizeCore st.core p.toNat = sz := by rw [hsz_val, hsz_eq]
  rw [hsz_core] at hj
  obtain ⟨m', hm', heqv⟩ := hent2 j hj
  rcases (by omega : m' = 0 ∨ m' = 1) with rfl | rfl
  · refine ⟨_, List.mem_cons_self, ?_⟩
    rw [hget_p3]
    rw [Nat.add_zero, List.getElem?_eq_getElem (by rw [harl]; have := hcl.arena_len_le; omega),
      List.getElem?_eq_getElem (by rw [harl3]; omega), Option.getD_some,
      Option.getD_some] at heqv
    exact heqv
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    rw [hget_p4]
    rw [show p.toNat + 3 + 1 = p.toNat + 4 by omega,
      List.getElem?_eq_getElem (by rw [harl]; have := hcl.arena_len_le; omega),
      List.getElem?_eq_getElem (by rw [harl3]; omega), Option.getD_some,
      Option.getD_some] at heqv
    exact heqv

theorem ra_addunit_prep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st3 st4 : FullState} {p : BitVec 64} {sz : Nat} {sz32 : BitVec 32}
    (ho : RaOuterCore c F0 F_cur s0 p st) (hsp4 : FullSparseInvW c F0 F_cur st4)
    (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st p.toNat = false)
    (hsz_eq : sz32.toNat = fullArenaClauseSize st p.toNat) (hsz_val : sz = sz32.toNat)
    (hcv : st.core.cur_vars = s0.core.cur_vars) (hcv4 : st4.core.cur_vars = s0.core.cur_vars)
    (harl3 : st3.core.arena.length = c.arena_cap)
    (hst4_ar : st4.core.arena =
      st3.core.arena.set p.toNat (fullArenaHdr st p.toNat ||| 0x00080000#32))
    (har3_lt : ∀ j < sz, (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hp3_eq : (p + 3#64).toNat = p.toNat + 3)
    (hp_blk : p.toNat + 3 + sz ≤ c.arena_cap)
    (hent2 : ∀ j < sz, ∃ m < 1, LitEquiv (cnfOfClauses F_cur)
      (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
      (st3.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat) :
    ∃ (hp3_lt4 : (p + 3#64).toNat < st4.core.arena.length),
    (st4.core.arena[(p + 3#64).toNat]'hp3_lt4).toNat < 2 * st4.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(st4.core.arena[(p + 3#64).toNat]'hp3_lt4).toNat]) := by
  have hcl := ho.sp.1.core_ok; have harl := hcl.arena_len_arr
  have hwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref
  have hsz3 : 3 ≤ sz := by rw [hsz_val, hsz_eq]; exact hwf.2.1
  have harl4 := hsp4.1.core_ok.arena_len_arr
  have hp3_lt4 : (p + 3#64).toNat < st4.core.arena.length := by rw [hp3_eq, harl4]; omega
  have hlit_get : st4.core.arena[(p + 3#64).toNat]'hp3_lt4 =
      st3.core.arena[p.toNat + 3]'(by rw [harl3]; omega) := by
    have hq : st4.core.arena[(p + 3#64).toNat]? = st3.core.arena[p.toNat + 3]? := by
      rw [hp3_eq, hst4_ar, List.getElem?_set_ne (by omega)]
    rw [List.getElem?_eq_getElem hp3_lt4, List.getElem?_eq_getElem (by rw [harl3]; omega)] at hq
    exact Option.some.inj hq
  have hlit_lt_cv : (st4.core.arena[(p + 3#64).toNat]'hp3_lt4).toNat < 2 * st4.core.cur_vars := by
    rw [hlit_get, hcv4, ← hcv]
    have h0 := har3_lt 0 (by omega)
    rwa [Nat.add_zero, List.getElem?_eq_getElem (by rw [harl3]; omega), Option.getD_some] at h0
  refine ⟨hp3_lt4, hlit_lt_cv, entails_clause_subst (fun l hl => ?_)
    (ho.sp.2.1.arena.entails p.toNat hp_ref hng)⟩
  obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff (k := st.core)
    (by have := hcl.arena_len_le; rw [harl]; omega)).mp hl
  have hsz_core : fullArenaClauseSizeCore st.core p.toNat = sz := by rw [hsz_val, hsz_eq]
  rw [hsz_core] at hj
  obtain ⟨m', hm', heqv⟩ := hent2 j hj
  have hm0 : m' = 0 := by omega
  subst hm0; refine ⟨_, List.mem_singleton.mpr rfl, ?_⟩
  rw [hlit_get]
  rw [Nat.add_zero, List.getElem?_eq_getElem (by rw [harl]; have := hcl.arena_len_le; omega),
    List.getElem?_eq_getElem (by rw [harl3]; omega), Option.getD_some,
    Option.getD_some] at heqv
  exact heqv

theorem ra_shrink_lt_shrk0_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st3 : FullState} {p : BitVec 64} {sz32 nsz hdr : BitVec 32}
    (ho : RaOuterCore c F0 F_cur s0 p st) (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st p.toNat = false)
    (hsz_eq : sz32.toNat = fullArenaClauseSize st p.toNat)
    (hhdr_eq : fullArenaHdr st p.toNat = hdr)
    (hnsz3 : 3 ≤ nsz.toNat) (hnsz_lt : nsz.toNat < sz32.toNat)
    (hshrk_z : (hdr &&& 0x00800000#32) = 0#32)
    (hsc3 : st3.scratch = st.scratch)
    (hcore3 : { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core)
    (harl3 : st3.core.arena.length = c.arena_cap)
    (hlml3 : st3.core.lit_mark.length = 2 * c.max_vars)
    (hlm3_zero : ∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 = 0#8)
    (har3_pad : ∀ j, nsz.toNat ≤ j → j < sz32.toNat →
      st3.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?)
    (har3_in_out : ∀ i, i < p.toNat ∨ p.toNat + 3 + sz32.toNat ≤ i →
      st3.core.arena[i]? = st.core.arena[i]?)
    (har3_lt : ∀ j < sz32.toNat,
      (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (har3_pw : ∀ i j, i < j → j < nsz.toNat →
      (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
      (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2)
    (hent_n : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((List.range nsz.toNat).map fun j => (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat)))
    (hp1_eq : (p + 1#64).toNat = p.toNat + 1) (hp2_eq : (p + 2#64).toNat = p.toNat + 2)
    (hsent_idx : (p + 3#64 + BitVec.setWidth 64 sz32 - 1#64).toNat =
      p.toNat + 3 + sz32.toNat - 1) :
    let ar4a := (st3.core.arena.set (p + 2#64).toNat nsz).set (p + 1#64).toNat 2#32
    let ar4b := (ar4a.set p.toNat (hdr ||| 0x00800000#32)).set
      (p + 3#64 + BitVec.setWidth 64 sz32 - 1#64).toNat 0xFFFFFFFF#32
    (p + 2#64).toNat < st3.core.arena.length ∧
    (p + 1#64).toNat < (st3.core.arena.set (p + 2#64).toNat nsz).length ∧
    p.toNat < ar4a.length ∧
    (p + 3#64 + BitVec.setWidth 64 sz32 - 1#64).toNat <
      (ar4a.set p.toNat (hdr ||| 0x00800000#32)).length ∧
    RaDoneCore c F0 F_cur s0 st { st3 with core := { st3.core with arena := ar4b } } := by
  have hcl := ho.sp.1.core_ok; have harl := hcl.arena_len_arr
  have hwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref; have hale := hcl.arena_len_le
  have hblk : p.toNat + 3 + sz32.toNat ≤ c.arena_cap := by
    have hszc : fullArenaClauseSizeCore st.core p.toNat = sz32.toNat := hsz_eq.symm
    have := hwf.2.2.1; have := hwf.2.2.2.1; omega
  have hp2_lt3 : (p + 2#64).toNat < st3.core.arena.length := by rw [hp2_eq, harl3]; omega
  have hp1_lt3 : (p + 1#64).toNat < (st3.core.arena.set (p + 2#64).toNat nsz).length := by
    rw [List.length_set, hp1_eq, harl3]; omega
  have hp_lt3 : p.toNat <
      ((st3.core.arena.set (p + 2#64).toNat nsz).set (p + 1#64).toNat 2#32).length := by
    simp [harl3]; omega
  have hsent_lt3 : (p + 3#64 + BitVec.setWidth 64 sz32 - 1#64).toNat <
      (((st3.core.arena.set (p + 2#64).toNat nsz).set (p + 1#64).toNat 2#32).set p.toNat
        (hdr ||| 0x00800000#32)).length := by
    simp [hsent_idx, harl3]; omega
  refine ⟨hp2_lt3, hp1_lt3, hp_lt3, hsent_lt3, ?_⟩
  let ar4a := (st3.core.arena.set (p.toNat + 2) nsz).set (p.toNat + 1) 2#32
  let ar4b := (ar4a.set p.toNat (hdr ||| 0x00800000#32)).set
    (p.toNat + 3 + sz32.toNat - 1) 0xFFFFFFFF#32
  have har4b_eq :
      (((st3.core.arena.set (p + 2#64).toNat nsz).set (p + 1#64).toNat 2#32).set p.toNat
        (hdr ||| 0x00800000#32)).set
        (p + 3#64 + BitVec.setWidth 64 sz32 - 1#64).toNat 0xFFFFFFFF#32 = ar4b := by
    rw [hp2_eq, hp1_eq, hsent_idx]
  have hnsz_ofNat : BitVec.ofNat 32 nsz.toNat = nsz :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nsz.isLt])
  rw [har4b_eq]
  refine ra_shrink_done (ar4 := ar4b) ho hp_ref hng hsz_eq hnsz3 (by omega) hsc3 hcore3
    (by dsimp only [ar4b, ar4a]; simp [harl3]) hlml3 hlm3_zero ?_ ?_ ?_ ?_ ?_
    har3_pad (fun i hi => har3_in_out i (hi.elim (fun h1 => Or.inl (by omega)) Or.inr))
    har3_lt har3_pw hent_n
  · dsimp only [ar4b, ar4a]; rw [← hsz_eq, hhdr_eq]
    simp only [hnsz_lt, hshrk_z, and_self, ite_true]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [harl3]; omega)]
  · dsimp only [ar4b, ar4a]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [harl3]; omega), hnsz_ofNat]
  · intro _ _; dsimp only [ar4b, ar4a]; rw [← hsz_eq]
    exact List.getElem?_set_self (by simp [harl3]; omega)
  · intro _ hne; exact absurd (hhdr_eq.symm ▸ hshrk_z) hne
  · intro i h0 h1 h2 h3; dsimp only [ar4b, ar4a]
    rw [List.getElem?_set_ne (h3 hnsz_lt).symm, List.getElem?_set_ne h0.symm,
      List.getElem?_set_ne h1.symm, List.getElem?_set_ne h2.symm]

theorem ra_shrink_lt_shrk1_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st3 : FullState} {p : BitVec 64} {sz32 nsz hdr : BitVec 32}
    (ho : RaOuterCore c F0 F_cur s0 p st) (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st p.toNat = false)
    (hsz_eq : sz32.toNat = fullArenaClauseSize st p.toNat)
    (hhdr_eq : fullArenaHdr st p.toNat = hdr)
    (hnsz3 : 3 ≤ nsz.toNat) (hnsz_lt : nsz.toNat < sz32.toNat)
    (hshrk_ne : (hdr &&& 0x00800000#32) ≠ 0#32)
    (hsc3 : st3.scratch = st.scratch)
    (hcore3 : { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core)
    (harl3 : st3.core.arena.length = c.arena_cap)
    (hlml3 : st3.core.lit_mark.length = 2 * c.max_vars)
    (hlm3_zero : ∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 = 0#8)
    (har3_pad : ∀ j, nsz.toNat ≤ j → j < sz32.toNat →
      st3.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?)
    (har3_in_out : ∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz32.toNat ≤ i →
      st3.core.arena[i]? = st.core.arena[i]?)
    (har3_lt : ∀ j < sz32.toNat,
      (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (har3_pw : ∀ i j, i < j → j < nsz.toNat →
      (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
      (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2)
    (hent_n : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((List.range nsz.toNat).map fun j => (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat)))
    (hp1_eq : (p + 1#64).toNat = p.toNat + 1) (hp2_eq : (p + 2#64).toNat = p.toNat + 2) :
    let ar4a := (st3.core.arena.set (p + 2#64).toNat nsz).set (p + 1#64).toNat 2#32
    RaDoneCore c F0 F_cur s0 st { st3 with core := { st3.core with arena := ar4a } } := by
  have hcl := ho.sp.1.core_ok; have harl := hcl.arena_len_arr
  have hwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref; have hale := hcl.arena_len_le
  let ar4a := (st3.core.arena.set (p.toNat + 2) nsz).set (p.toNat + 1) 2#32
  have har4a_def :
      (st3.core.arena.set (p + 2#64).toNat nsz).set (p + 1#64).toNat 2#32 = ar4a := by
    rw [hp2_eq, hp1_eq]
  have hnsz_ofNat : BitVec.ofNat 32 nsz.toNat = nsz :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nsz.isLt])
  rw [har4a_def]
  refine ra_shrink_done (ar4 := ar4a) ho hp_ref hng hsz_eq hnsz3 (by omega) hsc3 hcore3
    (by dsimp only [ar4a]; simp [harl3]) hlml3 hlm3_zero ?_ ?_ ?_ ?_ ?_
    har3_pad (fun i hi => har3_in_out i (hi.elim (fun h1 => Or.inl (by omega)) Or.inr))
    har3_lt har3_pw hent_n
  · dsimp only [ar4a]; rw [hhdr_eq]; simp only [hshrk_ne, and_false, ite_false]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    refine (har3_in_out p.toNat (Or.inl (by omega))).trans ?_
    rw [← hhdr_eq]
    show _ = some (st.core.arena[p.toNat]?.getD 0#32)
    rw [List.getElem?_eq_getElem (by rw [harl]; omega), Option.getD_some]
  · dsimp only [ar4a]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [harl3]; omega), hnsz_ofNat]
  · intro _ hz; exact absurd (hhdr_eq ▸ hz) hshrk_ne
  · intro _ _; dsimp only [ar4a]; rw [← hsz_eq]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      show p.toNat + 3 + sz32.toNat - 1 = p.toNat + 3 + (sz32.toNat - 1) by omega]
    exact har3_pad (sz32.toNat - 1) (by omega) (by omega)
  · intro i _ h1 h2 _; dsimp only [ar4a]
    rw [List.getElem?_set_ne h1.symm, List.getElem?_set_ne h2.symm]

theorem ra_shrink_eq_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st3 : FullState} {p : BitVec 64} {sz32 nsz : BitVec 32}
    (ho : RaOuterCore c F0 F_cur s0 p st) (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st p.toNat = false)
    (hsz_eq : sz32.toNat = fullArenaClauseSize st p.toNat)
    (hp2_get : st.core.arena[p.toNat + 2]? = some sz32)
    (hnsz3 : 3 ≤ nsz.toNat) (hnsz_eq : nsz.toNat = sz32.toNat)
    (hsc3 : st3.scratch = st.scratch)
    (hcore3 : { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core)
    (harl3 : st3.core.arena.length = c.arena_cap)
    (hlml3 : st3.core.lit_mark.length = 2 * c.max_vars)
    (hlm3_zero : ∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 = 0#8)
    (har3_pad : ∀ j, nsz.toNat ≤ j → j < sz32.toNat →
      st3.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?)
    (har3_in_out : ∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz32.toNat ≤ i →
      st3.core.arena[i]? = st.core.arena[i]?)
    (har3_lt : ∀ j < sz32.toNat,
      (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (har3_pw : ∀ i j, i < j → j < nsz.toNat →
      (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
      (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2)
    (hent_n : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((List.range nsz.toNat).map fun j => (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat))) :
    RaDoneCore c F0 F_cur s0 st st3 := by
  have hcl := ho.sp.1.core_ok; have harl := hcl.arena_len_arr
  have hwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref; have hale := hcl.arena_len_le
  have hst3_eq : { st3 with core := { st3.core with arena := st3.core.arena } } = st3 := rfl
  rw [← hst3_eq]
  refine ra_shrink_done (ar4 := st3.core.arena) ho hp_ref hng hsz_eq hnsz3 (by omega)
    hsc3 hcore3 harl3 hlml3 hlm3_zero ?_ ?_ ?_ ?_ (fun _ _ _ _ _ => rfl)
    har3_pad (fun i hi => har3_in_out i (hi.elim (fun h1 => Or.inl (by omega)) Or.inr))
    har3_lt har3_pw hent_n
  · simp only [← hsz_eq, hnsz_eq, Nat.lt_irrefl, false_and, ite_false]
    refine (har3_in_out p.toNat (Or.inl (by omega))).trans ?_
    show _ = some (st.core.arena[p.toNat]?.getD 0#32)
    rw [List.getElem?_eq_getElem (by rw [harl]; omega), Option.getD_some]
  · rw [hnsz_eq, show BitVec.ofNat 32 sz32.toNat = sz32 from
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sz32.isLt])]
    rw [← hp2_get]; exact har3_in_out (p.toNat + 2) (Or.inl (by omega))
  · intro hlt; rw [← hsz_eq, hnsz_eq] at hlt; omega
  · intro hlt; rw [← hsz_eq, hnsz_eq] at hlt; omega

theorem ra_loop2_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {p : BitVec 64} {sz : Nat}
    (ho : RaOuterCore c F0 F_cur s0 p st) (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st p.toNat = false) (hsz_eq : sz = fullArenaClauseSize st p.toNat) :
    RaLoop2Inv c F_cur st p sz 0#32 0#32 st := by
  have harl := ho.sp.1.core_ok.arena_len_arr; have hale := ho.sp.1.core_ok.arena_len_le
  have hwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref
  have hsz_core : fullArenaClauseSizeCore st.core p.toNat = sz := hsz_eq.symm
  refine ⟨⟨ho.sp.1, rfl, rfl, Nat.zero_le _, fun _ _ _ => rfl, fun _ _ => rfl, ?_,
      fun _ _ _ h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega, ?_,
      ho.sp.2.2.1.1⟩,
    Nat.zero_le _, Nat.zero_le _,
    fun h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega,
    fun _ h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega⟩
  · intro j hj
    have hm_lt : (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat ∈
        fullArenaClauseLits st p.toNat := by
      unfold fullArenaClauseLits
      have hm_elt := (mem_fullArenaClauseLitsCore_iff (k := st.core)
        (cref := p.toNat) (by rw [harl, hsz_core]; omega)).mpr
        ⟨j, by rw [hsz_core]; exact hj, rfl⟩
      rw [List.getElem?_eq_getElem (by rw [harl]; omega), Option.getD_some]
      exact hm_elt
    exact ho.sp.2.1.arena.lits_lt p.toNat hp_ref hng _ hm_lt
  · intro x hx; constructor
    · intro hnz; exact absurd (ho.sp.2.2.1.2 x hx) hnz
    · rintro ⟨m', hm', _⟩; rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at hm'; omega

theorem ra_loop2_lit_prep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st2 : FullState} {p : BitVec 64} {sz : Nat} {k nsz : BitVec 32}
    (ho : RaOuterCore c F0 F_cur s0 p st) (hrepr_st : FullReprEquiv F_cur st)
    (hi : RaLoop2Inv c F_cur st p sz k nsz st2) (hk_lt : k.toNat < sz)
    (hpk_eq : (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat)
    (hp_blk : p.toNat + 3 + sz ≤ c.arena_cap) :
    ∃ (hpk_lt : (p + 3#64 + BitVec.setWidth 64 k).toNat < st2.core.arena.length)
      (hl2_lt_rp : (BitVec.setWidth 64
        (st2.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt)).toNat <
          st2.core.repr.length),
    let l2 := st2.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt
    let rl2 := st2.core.repr[(BitVec.setWidth 64 l2).toNat]'hl2_lt_rp
    st2.core.arena[p.toNat + 3 + k.toNat]? = some l2 ∧
    rl2.toNat < 2 * st.core.cur_vars ∧
    LitEquiv (cnfOfClauses F_cur) l2.toNat rl2.toNat ∧
    (BitVec.setWidth 64 (rl2 ^^^ 1#32)).toNat = rl2.toNat ^^^ 1 ∧
    (BitVec.setWidth 64 (rl2 ^^^ 1#32)).toNat < st2.core.lit_mark.length ∧
    (BitVec.setWidth 64 rl2).toNat = rl2.toNat ∧
    (BitVec.setWidth 64 rl2).toNat < st2.core.lit_mark.length := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := ho.sp.1.core_ok.cur_vars_le
  have hcl2 := hi.core.len.core_ok; have harl2 := hcl2.arena_len_arr
  have hrpl2 := hcl2.repr_len; have hlml2 := hcl2.lit_mark_len
  have hrp2 : st2.core.repr = st.core.repr := by
    have hc := hi.core.core_eq
    rcases st with ⟨c0, _⟩; rcases st2 with ⟨c2, _⟩; cases c0; cases c2; cases hc; rfl
  have hpk_lt : (p + 3#64 + BitVec.setWidth 64 k).toNat < st2.core.arena.length := by
    rw [hpk_eq, harl2]; omega
  let l2 := st2.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt
  have hl2_orig_eq : st2.core.arena[p.toNat + 3 + k.toNat]? = some l2 := by
    dsimp only [l2]; rw [← hpk_eq, List.getElem?_eq_getElem hpk_lt]
  have hl2_lt_v : l2.toNat < 2 * st.core.cur_vars := by
    have hg := hi.core.lits_lt k.toNat hk_lt
    rw [hl2_orig_eq, Option.getD_some] at hg; exact hg
  have hl2_lt_rp : (BitVec.setWidth 64 l2).toNat < st2.core.repr.length := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hrpl2]; omega
  let rl2 := st2.core.repr[(BitVec.setWidth 64 l2).toNat]'hl2_lt_rp
  have hrl2_eq_get : st.core.repr[l2.toNat]?.getD 0#32 = rl2 := by
    have hz : (BitVec.setWidth 64 l2).toNat = l2.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    dsimp only [rl2]; rw [← hrp2]
    rw [bv32_getElem_congr (xs := st2.core.repr) hz (hi := hl2_lt_rp)
        (hj := by rw [hrpl2]; omega),
      List.getElem?_eq_getElem (by rw [hrpl2]; omega), Option.getD_some]
  have hrl2_lt_v : rl2.toNat < 2 * st.core.cur_vars := by
    rw [← hrl2_eq_get]; exact FullReprEquiv.lt hrepr_st hl2_lt_v
  have hrl2_eqv : LitEquiv (cnfOfClauses F_cur) l2.toNat rl2.toNat := by
    rw [← hrl2_eq_get]; exact FullReprEquiv.litEquiv hrepr_st hl2_lt_v
  have hnx := ra_litNeg_lt_two_mul hrl2_lt_v
  have hrl2_1_z64 : (BitVec.setWidth 64 (rl2 ^^^ 1#32)).toNat = rl2.toNat ^^^ 1 := by
    rw [BitVec.toNat_setWidth, bv32_xor1_toNat, Nat.mod_eq_of_lt (by omega)]
  have hrl_z64 : (BitVec.setWidth 64 rl2).toNat = rl2.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  exact ⟨hpk_lt, hl2_lt_rp, hl2_orig_eq, hrl2_lt_v, hrl2_eqv, hrl2_1_z64,
    by rw [hrl2_1_z64, hlml2]; omega, hrl_z64, by rw [hrl_z64, hlml2]; omega⟩

theorem ra_loop2_dup_step {c : FullCfg} {F_cur : List (List Nat)} {st st2 : FullState}
    {p : BitVec 64} {sz : Nat} {k nsz l2 rl2 : BitVec 32}
    (hi : RaLoop2Inv c F_cur st p sz k nsz st2) (hk_lt : k.toNat < sz)
    (hk1 : (k + 1#32).toNat = k.toNat + 1) (hrl2_lt_v : rl2.toNat < 2 * st.core.cur_vars)
    (hcv_le : st.core.cur_vars ≤ c.max_vars)
    (hl2_orig_eq : st2.core.arena[p.toNat + 3 + k.toNat]? = some l2)
    (hrl2_eqv : LitEquiv (cnfOfClauses F_cur) l2.toNat rl2.toNat)
    (hlm_nz : st2.core.lit_mark[rl2.toNat]?.getD 0#8 ≠ 0#8) :
    RaLoop2Inv c F_cur st p sz (k + 1#32) nsz st2 := by
  obtain ⟨m_dup, hm_dup_lt, hm_dup_eq⟩ := (hi.core.lm rl2.toNat (by omega)).mp hlm_nz
  refine ⟨hi.core, by rw [hk1]; omega, by rw [hk1]; have := hi.nsz_k; omega,
    fun _ => by omega, fun j hj => ?_⟩
  rw [hk1] at hj
  by_cases hjk : j = k.toNat
  · subst hjk; refine ⟨m_dup, hm_dup_lt, ?_⟩
    have hpad_k := hi.core.pad k.toNat hi.nsz_k hk_lt
    have hl2_orig : (st.core.arena[p.toNat + 3 + k.toNat]?.getD 0#32).toNat = l2.toNat := by
      rw [← hpad_k, hl2_orig_eq, Option.getD_some]
    rw [hl2_orig, hm_dup_eq]; exact hrl2_eqv
  · exact hi.ent j (by omega)

theorem ra_loop1_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {p : BitVec 64} {sz : Nat} {k : BitVec 32}
    (ho : RaOuterCore c F0 F_cur s0 p st) (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st p.toNat = false)
    (hsz_eq : sz = fullArenaClauseSize st p.toNat) (hk_lt : k.toNat < sz)
    (hpk_eq : (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat)
    (hpk_lt : (p + 3#64 + BitVec.setWidth 64 k).toNat < st.core.arena.length) :
    let l := st.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt
    l.toNat < 2 * st.core.cur_vars ∧ (BitVec.setWidth 64 l).toNat < st.core.repr.length := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := ho.sp.1.core_ok; have harl := hcl.arena_len_arr
  have hrpl := hcl.repr_len; have hcv_le := hcl.cur_vars_le
  have hwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref
  have hsz_core : fullArenaClauseSizeCore st.core p.toNat = sz := hsz_eq.symm
  have hmem :
      (st.core.arena[p.toNat + 3 + k.toNat]'(by rw [harl]; omega)).toNat ∈
        fullArenaClauseLits st p.toNat := by
    unfold fullArenaClauseLits
    exact (mem_fullArenaClauseLitsCore_iff (k := st.core) (cref := p.toNat)
      (by rw [harl, hsz_core]; have := hcl.arena_len_le; omega)).mpr
        ⟨k.toNat, by rw [hsz_core]; exact hk_lt, rfl⟩
  have hl := ho.sp.2.1.arena.lits_lt p.toNat hp_ref hng _ hmem
  have hl' : (st.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt).toNat <
      2 * st.core.cur_vars := by
    rw [bv32_getElem_congr hpk_eq]; exact hl
  exact ⟨hl', by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hrpl]; omega⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute