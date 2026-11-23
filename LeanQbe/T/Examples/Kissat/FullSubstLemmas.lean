module

public import LeanQbe.T.Examples.Kissat.FullSubstLemmas2

/-!
# Kissat `D-Full` BIG SCC Substitution — Part 3 (`Stage 4`, UNSAT-Only)
Block-replacement helpers, `full_subst_rewrite_ar_wp` (fn 28), `full_substitute_wp` (fn 29). -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullSubstSpecs FullSubstTactics FullSubstHelpers
open scoped FullArenaTactics FullSubstTactics

section

/-! ## 1. Private Block-Replacement Invariants & Rewrite Step Helpers -/

private theorem arenaBlockReplace_level0_preserves_fullSparse {c : FullCfg} {F0 : CNF Nat}
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
  rw [fullState_eq_replace_arena_lm_ag hsc hc]
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

private theorem overwriteGarb_lits_level0_preserves_fullSparse {c : FullCfg} {F0 : CNF Nat}
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
  refine arenaBlockReplace_level0_preserves_fullSparse hsp hl0 hsc hc href
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

private theorem inPlaceShrink_level0_preserves_fullSparse {c : FullCfg} {F0 : CNF Nat}
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
    change (s.core.arena[cref + 2]?.getD 0#32).toNat = old_sz at hold_eq
    have hold_sz_eq : (s.core.arena[cref + 2]?.getD 0#32).toNat = old_sz := rfl
    omega
  have hsz_n : (s'.core.arena[cref + 2]?.getD 0#32).toNat = nsz := by
    rw [hsz', Option.getD_some, bv32_ofNat_toNat hnsz_lt32]
  have hold_ne : ∀ j, j < old_sz →
      s.core.arena[cref + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hbd : cref + 3 + old_sz ≤ s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    have hlt_j : cref + 3 + j < s.core.arena.length := by omega
    rw [List.getElem?_eq_getElem hlt_j, Option.getD_some]
    have hlt_v := ha.lits_lt cref hcref hng _
      ((mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, hj, rfl⟩)
    have hmx := c.hmaxv; have hcv := hcl.cur_vars_le; unfold dimacsBound at hmx
    intro heq; rw [heq] at hlt_v; simp at hlt_v; omega
  refine arenaBlockReplace_level0_preserves_fullSparse hsp hl0 hsc (core_eq_of_arena_lm hc)
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
          fullArenaSkipShrk_first_sentinel (ar := s.core.arena) (alen := s.core.arena_len)
            (t := t) (fuel := s.core.arena_len - (cref + 3 + old_sz))
            (p := cref + 3 + old_sz) ht1 ht2 hsent (by omega)
        unfold fullArenaNextOff
        simp only [h1, h2, h2', hsz_n, hold_sz_eq, hhdr', Option.getD_some, hsh0, ne_eq,
          not_false_eq_true, ↓reduceIte]
        rw [ht0_nxt]
        refine fullArenaSkipShrk_of_first_sentinel (ar := s'.core.arena) (alen := s.core.arena_len)
          (t := t0) (fuel := s.core.arena_len - (cref + 3 + nsz)) (p := cref + 3 + nsz)
          (by omega) (by omega) (by rw [hout t0 (Or.inr ht0_lo)]; exact ht0_sent)
          (fun i hi1 hi2 => ?_) (by omega)
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

private def RewriteArOuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (p : BitVec 64) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st : FullState,
    FullSparseInvW c F0 F_cur st ∧
    st.core.cur_vars = s0.core.cur_vars ∧ st.core.cur_level = 0 ∧
    st.core.fuel = s0.core.fuel ∧ st.core.repr = s0.core.repr ∧
    st.core.arena_len = s0.core.arena_len ∧
    (p.toNat = st.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs st) ∧
    (FullMem c st ⋆ R) m

private def RewriteArLoop2Core (c : FullCfg) (_F_cur : List (List Nat)) (st st2 : FullState)
    (p : BitVec 64) (sz : Nat) (nsz : BitVec 32) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  st2.LengthsOk c ∧ st2.scratch = st.scratch ∧
  { st2.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core ∧
  nsz.toNat ≤ sz ∧
  (∀ j, nsz.toNat ≤ j → j < sz →
    st2.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?) ∧
  (∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz ≤ i → st2.core.arena[i]? = st.core.arena[i]?) ∧
  (∀ j < sz, (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars) ∧
  (∀ i j, i < j → j < nsz.toNat →
    (st2.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
    (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2) ∧
  (∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔
    ∃ m < nsz.toNat, (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat = x) ∧
  (∀ v < c.max_vars, st2.core.mrk[v]?.getD 0#8 = 0#8) ∧ (FullMem c st2 ⋆ R) m

private def RewriteArLoop2Inv (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (p : BitVec 64) (sz : Nat) (k nsz : BitVec 32) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st2 : FullState,
    RewriteArLoop2Core c F_cur st st2 p sz nsz m R ∧
    k.toNat ≤ sz ∧ nsz.toNat ≤ k.toNat ∧ (0 < k.toNat → 1 ≤ nsz.toNat) ∧
    (∀ j < k.toNat, ∃ m < nsz.toNat,
      LitEquiv (cnfOfClauses F_cur)
        (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
        (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat)

private def RewriteArLoop2Brk (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (p : BitVec 64) (sz : Nat) (taut : Bool) (nsz : BitVec 32)
    (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st2 : FullState,
    RewriteArLoop2Core c F_cur st st2 p sz nsz m R ∧
    (taut = false → 1 ≤ nsz.toNat) ∧
    (taut = false → ∀ j < sz, ∃ m < nsz.toNat,
      LitEquiv (cnfOfClauses F_cur)
        (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
        (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat)

private def RewriteArLoop3Inv (c : FullCfg) (st st2 : FullState) (p : BitVec 64)
    (nsz k : BitVec 32) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st3 : FullState,
    st3.LengthsOk c ∧ st3.scratch = st.scratch ∧
    { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core ∧
    st3.core.arena = st2.core.arena ∧ k.toNat ≤ nsz.toNat ∧
    (∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
      ∃ i, k.toNat ≤ i ∧ i < nsz.toNat ∧
        (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat = x) ∧
    (∀ v < c.max_vars, st3.core.mrk[v]?.getD 0#8 = 0#8) ∧
    (FullMem c st3 ⋆ R) m

private def RewriteArClauseDoneInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st : FullState) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st4 : FullState,
    FullSparseInvW c F0 F_cur st4 ∧
    st4.core.cur_vars = s0.core.cur_vars ∧ st4.core.cur_level = 0 ∧
    st4.core.fuel = s0.core.fuel ∧ st4.core.repr = s0.core.repr ∧
    st4.core.arena_len = s0.core.arena_len ∧
    fullArenaClauseRefs st4 = fullArenaClauseRefs st ∧
    (FullMem c st4 ⋆ R) m

private def SubstituteAfterBtInv (c : FullCfg) (F0 : CNF Nat) (s0 : FullState)
    (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st : FullState,
    FullSparseInv c F0 st ∧ st.core.cur_level = 0 ∧
    st.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c st ⋆ R) m

private def SubstituteLoopInv (c : FullCfg) (F0 : CNF Nat) (s0 : FullState)
    (round : BitVec 64) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st : FullState,
    FullSparseInv c F0 st ∧ st.core.cur_level = 0 ∧
    st.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ round.toNat ≤ 4 ∧ (FullMem c st ⋆ R) m

private theorem rewriteAr_loop2_push_step {c : FullCfg} {F_cur : List (List Nat)}
    {st st2 : FullState} {p : BitVec 64} {sz : Nat} {k nsz : BitVec 32}
    {l2 rl2 : BitVec 32} {m2' : Mem 64} {R : Mem 64 → Prop}
    (hk_lt : k.toNat < sz) (_hsz3 : 3 ≤ sz) (hk1 : (k + 1#32).toNat = k.toNat + 1)
    (hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1)
    (hlen2 : st2.LengthsOk c) (hsc2 : st2.scratch = st.scratch)
    (hcore2 : { st2.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core)
    (hnsz_le : nsz.toNat ≤ k.toNat)
    (hpad2 : ∀ j, nsz.toNat ≤ j → j < sz →
      st2.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?)
    (hout2 : ∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz ≤ i →
      st2.core.arena[i]? = st.core.arena[i]?)
    (hlt2 : ∀ j < sz, (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hpw2 : ∀ i j, i < j → j < nsz.toNat →
      (st2.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
      (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2)
    (hent2 : ∀ j < k.toNat, ∃ m < nsz.toNat,
      LitEquiv (cnfOfClauses F_cur)
        (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
        (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat)
    (hlm2 : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔
      ∃ m < nsz.toNat, (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat = x)
    (hmrk2 : ∀ v < c.max_vars, st2.core.mrk[v]?.getD 0#8 = 0#8)
    (hcv_le : st.core.cur_vars ≤ c.max_vars)
    (hp_bd : p.toNat + 3 + sz ≤ st2.core.arena.length)
    (hl2_orig_eq : st2.core.arena[p.toNat + 3 + k.toNat]? = some l2)
    (hrl2_lt_v : rl2.toNat < 2 * st.core.cur_vars)
    (hrl2_eqv : LitEquiv (cnfOfClauses F_cur) l2.toNat rl2.toNat)
    (hlm_neg0 : st2.core.lit_mark[rl2.toNat ^^^ 1]?.getD 0#8 = 0#8)
    (hlm_pos0 : st2.core.lit_mark[rl2.toNat]?.getD 0#8 = 0#8)
    (hm2' : (FullMem c { st2 with
      core := { st2.core with
        lit_mark := st2.core.lit_mark.set rl2.toNat 1#8,
        arena := st2.core.arena.set (p.toNat + 3 + nsz.toNat) rl2 } } ⋆ R) m2') :
    RewriteArLoop2Inv c F_cur st p sz (k + 1#32) (nsz + 1#32) m2' R := by
  have hcl2 := hlen2.core_ok; have harl2 := hcl2.arena_len_arr; have hlml2 := hcl2.lit_mark_len
  let lm2' := st2.core.lit_mark.set rl2.toNat 1#8
  let ar2' := st2.core.arena.set (p.toNat + 3 + nsz.toNat) rl2
  let st2' : FullState := { st2 with core := { st2.core with lit_mark := lm2', arena := ar2' } }
  refine ⟨st2', ⟨⟨{ hcl2 with
        arena_len_arr := by simp [st2', ar2', harl2]
        lit_mark_len := by simp [st2', lm2', hlml2] }, hlen2.scratch_ok⟩,
      hsc2, hcore2, by omega, ?_, ?_, ?_, ?_, ?_, by simpa [st2'] using hmrk2, hm2'⟩,
    by omega, by omega, fun _ => by omega, ?_⟩
  · intro j hj1 hj2; dsimp only [st2', ar2']; rw [List.getElem?_set_ne (by omega)]
    exact hpad2 j (by omega) hj2
  · intro i hi; dsimp only [st2', ar2']; rw [List.getElem?_set_ne (by omega)]; exact hout2 i hi
  · intro j hj; dsimp only [st2', ar2']
    by_cases hjn : j = nsz.toNat
    · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hrl2_lt_v
    · rw [List.getElem?_set_ne (by omega)]; exact hlt2 j hj
  · intro i j hij hj; dsimp only [st2', ar2']
    by_cases hj_last : j = nsz.toNat
    · subst hj_last
      rw [List.getElem?_set_self (by omega), List.getElem?_set_ne (by omega), Option.getD_some]
      intro hdv; rcases (litVar_eq_iff _ rl2.toNat).mp hdv with heq | heq
      · exact (hlm2 rl2.toNat (by omega)).mpr ⟨i, by omega, heq⟩ hlm_pos0
      · have hnx := litNeg_lt_two_mul hrl2_lt_v
        exact (hlm2 (rl2.toNat ^^^ 1) (by omega)).mpr ⟨i, by omega, heq⟩ hlm_neg0
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hpw2 i j hij (by omega)
  · intro x hx; dsimp only [st2', lm2', ar2']; constructor
    · intro hnz
      by_cases hxr : x = rl2.toNat
      · subst hxr; refine ⟨nsz.toNat, by omega, ?_⟩
        rw [List.getElem?_set_self (by omega), Option.getD_some]
      · rw [List.getElem?_set_ne (Ne.symm hxr)] at hnz
        obtain ⟨m', hm', hm'_eq⟩ := (hlm2 x hx).mp hnz
        refine ⟨m', by omega, ?_⟩; rw [List.getElem?_set_ne (by omega)]; exact hm'_eq
    · rintro ⟨m', hm', hm'_eq⟩
      by_cases hmn : m' = nsz.toNat
      · subst hmn; rw [List.getElem?_set_self (by omega), Option.getD_some] at hm'_eq
        subst hm'_eq; rw [List.getElem?_set_self (by rw [hlml2]; exact hx), Option.getD_some]
        decide
      · rw [List.getElem?_set_ne (by omega)] at hm'_eq
        have hnz := (hlm2 x hx).mpr ⟨m', by omega, hm'_eq⟩
        by_cases hxr : x = rl2.toNat
        · subst hxr; rw [List.getElem?_set_self (by rw [hlml2]; exact hx), Option.getD_some]
          decide
        · rw [List.getElem?_set_ne (Ne.symm hxr)]; exact hnz
  · intro j hj; dsimp only [st2', ar2']
    by_cases hjk : j = k.toNat
    · subst hjk; refine ⟨nsz.toNat, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      have hpad_k := hpad2 k.toNat hnsz_le hk_lt
      have hl2_orig : (st.core.arena[p.toNat + 3 + k.toNat]?.getD 0#32).toNat = l2.toNat := by
        rw [← hpad_k, hl2_orig_eq, Option.getD_some]
      rwa [hl2_orig]
    · obtain ⟨m', hm', heqv⟩ := hent2 j (by omega)
      refine ⟨m', by omega, ?_⟩; rw [List.getElem?_set_ne (by omega)]; exact heqv

private theorem rewriteAr_shrink_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st3 : FullState} {p : BitVec 64} {sz nsz : Nat} {ar4 : List (BitVec 32)}
    {m4 : Mem 64} {R : Mem 64 → Prop}
    (hsp : FullSparseInvW c F0 F_cur st) (hl0 : st.core.cur_level = 0)
    (hcv : st.core.cur_vars = s0.core.cur_vars) (hfl : st.core.fuel = s0.core.fuel)
    (hrp : st.core.repr = s0.core.repr) (hal : st.core.arena_len = s0.core.arena_len)
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
      ((List.range nsz).map fun j => (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat)))
    (hm4 : (FullMem c { st3 with core := { st3.core with arena := ar4 } } ⋆ R) m4) :
    RewriteArClauseDoneInv c F0 F_cur s0 st m4 R := by
  let st4 : FullState := { st3 with core := { st3.core with arena := ar4 } }
  have hwf := hsp.2.1.arena.refs_wf p.toNat hp_ref
  have hsz3 : 3 ≤ sz := by rw [hsz_eq]; exact hwf.2.1
  have hcore4' :
      { st4.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core := by
    rcases st with ⟨c0, _⟩; rcases st3 with ⟨c3, _⟩; rcases c0; rcases c3; cases hcore3; rfl
  have har4_s : st4.core.arena = ar4 := rfl
  have hmap_eq : ((List.range nsz).map fun j => (ar4[p.toNat + 3 + j]?.getD 0#32).toNat) =
      ((List.range nsz).map fun j => (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat) :=
    List.map_congr_left fun j hj => by
      have hj' := List.mem_range.mp hj
      rw [har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
  obtain ⟨hsp4, hrefs4, hal4⟩ := inPlaceShrink_level0_preserves_fullSparse (s' := st4)
    hsp hl0 hsc3 hcore4'
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
  exact ⟨st4, hsp4, (congrArg FullCoreState.cur_vars hcore4').trans hcv,
    (congrArg FullCoreState.cur_level hcore4').trans hl0,
    (congrArg FullCoreState.fuel hcore4').trans hfl,
    (congrArg FullCoreState.repr hcore4').trans hrp, hal4.trans hal, hrefs4, hm4⟩

private theorem list_getElem_eq_of_getElem? {xs ys : List (BitVec 32)} {i j : Nat}
    {hi : i < xs.length} {hj : j < ys.length} (hij : i = j) (hq : xs[j]? = ys[j]?) :
    xs[i]'hi = ys[j]'hj := by
  subst hij; rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hq
  exact Option.some.inj hq

private theorem rewriteAr_lm_get_zero {lm : List (BitVec 8)} {i j : Nat}
    {hi : i < lm.length} {hj : j < lm.length} (hij : i = j)
    (hc : BitVec.setWidth 32 (lm[j]'hj) = 0#32) : lm[i]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some,
    show lm[i]'hi = lm[j]'hj by subst hij; rfl]
  exact bv8_setWidth32_eq_zero hc

private theorem rewriteAr_lm_get_ne {lm : List (BitVec 8)} {i j : Nat}
    {hi : i < lm.length} {hj : j < lm.length} (hij : i = j)
    (hc : ¬ BitVec.setWidth 32 (lm[j]'hj) = 0#32) : lm[i]?.getD 0#8 ≠ 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some,
    show lm[i]'hi = lm[j]'hj by subst hij; rfl]
  intro heq; exact hc (congrArg (BitVec.setWidth 32) heq)

end

/-! ## 2. `full_subst_rewrite_ar` `Func.wp` Proof (`Full3.lean` #28) -/

public section

theorem full_subst_rewrite_ar_wp (Γ : Env)
    (hArenaNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullSubstRewriteArSpec args m Q X →
      Func.wp Γ full_subst_rewrite_ar_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, hl0, hrepr0, hm, hQ⟩
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  s_to_group
  refine wp_loop_inv (fun (p, ()) ml => RewriteArOuterInv c F0 F_cur s0 p ml R)
    (fun (p, ()) _ => s0.core.arena_len - p.toNat) ?_ ?_
  · intro J hJ; s_steps
    exact hJ (0#64, ()) m
      ⟨s0, hsp0, rfl, hl0, rfl, rfl, rfl, fullArenaClauseRefs_zero_mem hsp0.2.1.arena, hm⟩
  · rintro J ⟨p, ⟨⟩⟩ ml ⟨st, hsp, hcv, hl0_st, hfl, hrp, hal, hp_pos, hml⟩ hJ
    have hcl := hsp.1.core_ok; have hsl := hsp.1.scratch_ok
    have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le
    have hcv_le := hcl.cur_vars_le; have hlml := hcl.lit_mark_len; have hrpl := hcl.repr_len
    have hrepr_st : FullReprEquiv F_cur st := fun l hl => by
      rw [hcv] at hl; have h0 := hrepr0 l hl; rw [hrp, hcv]; exact h0
    s_split
    · have hp_lt_alen : p.toNat < st.core.arena_len := by
        change p.toNat < (BitVec.ofNat 64 st.core.arena_len).toNat at hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      have hp_ref : p.toNat ∈ fullArenaClauseRefs st := hp_pos.elim (fun he => by omega) id
      have hpwf := hsp.2.1.arena.refs_wf p.toNat hp_ref
      have hp2_lt : (p + 2#64).toNat < st.core.arena.length := by
        rw [BitVec.toNat_add, show (2#64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
      have hp_trunc : (BitVec.setWidth 32 p).toNat = p.toNat := bv32_trunc_toNat (by omega)
      have hnp_lt_next := fullArenaClauseRefs_next_or_end hsp.2.1.arena hp_ref
      s_steps; s_call hArenaNext
      refine ⟨c, st, R, rfl, hsp.1, hml, ?_⟩; dsimp only
      let np := BitVec.setWidth 64 (BitVec.ofNat 32
        (fullArenaNextOff st.core.arena st.core.arena_len (BitVec.setWidth 32 p).toNat))
      have hnp_nat : np.toNat = fullArenaNextOff st.core.arena st.core.arena_len p.toNat := by
        dsimp only [np]; rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hp_trunc]
        have hnb := (fullArenaNextOff_bounds (ar := st.core.arena) (alen := st.core.arena_len)
          (cref := p.toNat) hpwf.1).2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hnp_meas : s0.core.arena_len - np.toNat < s0.core.arena_len - p.toNat := by
        rw [hnp_nat, ← hal]
        have := fullArenaNextOff_bounds (ar := st.core.arena) (alen := st.core.arena_len)
          (cref := p.toNat) hpwf.1; omega
      have hnp_pos : np.toNat = st.core.arena_len ∨ np.toNat ∈ fullArenaClauseRefs st :=
        hnp_nat ▸ hnp_lt_next
      let hdr := st.core.arena[p.toNat]'(by omega)
      let sz32 := st.core.arena[(p + 2#64).toNat]'hp2_lt
      have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by
        rw [BitVec.toNat_add, show (2#64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hp2_get : st.core.arena[p.toNat + 2]? = some sz32 := by
        dsimp only [sz32]; rw [← hp2_eq, List.getElem?_eq_getElem hp2_lt]
      have hsz_eq : sz32.toNat = fullArenaClauseSize st p.toNat := by
        unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [hp2_get, Option.getD_some]
      have hsz_core : fullArenaClauseSizeCore st.core p.toNat = sz32.toNat := hsz_eq.symm
      have hp_blk_le : p.toNat + 3 + sz32.toNat ≤ st.core.arena_len := by
        change fullArenaClauseSizeCore st.core p.toNat = sz32.toNat at hsz_core
        have := hpwf.2.2.1; have := hpwf.2.2.2.1; omega
      have hhdr_eq : fullArenaHdr st p.toNat = hdr := by
        dsimp only [hdr, fullArenaHdr, fullArenaHdrCore]
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      s_split
      · s_steps; exact hJ (np, ()) ml hnp_meas ⟨st, hsp, hcv, hl0_st, hfl, hrp, hal, hnp_pos, hml⟩
      · s_split
        · s_steps; exact hJ (np, ()) ml hnp_meas ⟨st, hsp, hcv, hl0_st, hfl, hrp, hal, hnp_pos, hml⟩
        · have hng : fullArenaClauseGarb st p.toNat = false := by
            unfold fullArenaClauseGarb fullArenaClauseGarbCore
            rw [show fullArenaHdrCore st.core p.toNat = hdr from hhdr_eq,
              (by assumption : (hdr &&& 0x00080000#32) = 0#32)]; decide
          have hsz3 : 3 ≤ sz32.toNat := by
            have hc0 : ¬ (st.core.arena[(p.toNat + 2) % 2 ^ 64]'(by
                rw [Nat.mod_eq_of_lt (by omega), harl]; omega)).toNat < (3#32).toNat := hc
            rw [bv32_getElem_congr (show (p.toNat + 2) % 2 ^ 64 = (p + 2#64).toNat by
                rw [BitVec.toNat_add, show (2#64).toNat = 2 from rfl])] at hc0
            change ¬ sz32.toNat < 3 at hc0; omega
          s_to_group; refine wp_loop_break_group
            (fun (chg, _k1, ()) m1 => (chg = true ∨ chg = false) ∧ (FullMem c st ⋆ R) m1)
            (fun n (k, ()) m1 =>
              n = sz32.toNat - k.toNat ∧ k.toNat ≤ sz32.toNat ∧ (FullMem c st ⋆ R) m1) ?_ ?_ ?_
          · rintro B ⟨chg, _k1, ⟨⟩⟩ m1 ⟨_, hm1⟩
            s_split
            · s_to_group; refine wp_loop_break_group
                (fun (_k2, taut, nsz, ()) m2 =>
                  RewriteArLoop2Brk c F_cur st p sz32.toNat taut nsz m2 R)
                (fun n (k, nsz, ()) m2 =>
                  n = sz32.toNat - k.toNat ∧
                  RewriteArLoop2Inv c F_cur st p sz32.toNat k nsz m2 R)
                ?_ ?_ ?_
              · rintro B2 ⟨_k2, taut, nsz, ⟨⟩⟩ m2
                  ⟨st2, ⟨hlen2, hsc2, hcore2, hnsz_le, hpad2, hout2, hlt2, hpw2, hlm2, hmrk2, hm2⟩,
                   hnsz_pos, hent2⟩
                s_to_group; refine wp_loop_inv
                  (fun (k3, ()) m3 => RewriteArLoop3Inv c st st2 p nsz k3 m3 R)
                  (fun (k3, ()) _ => nsz.toNat - k3.toNat) ?_ ?_
                · intro J3 hJ3; s_steps
                  refine hJ3 (0#32, ()) m2
                    ⟨st2, hlen2, hsc2, hcore2, rfl, Nat.zero_le _, ?_, hmrk2, hm2⟩
                  intro x hx hnz; obtain ⟨m', hm1', hm2'⟩ := (hlm2 x hx).mp hnz
                  exact ⟨m', Nat.zero_le _, hm1', hm2'⟩
                · rintro J3 ⟨k3, ⟨⟩⟩ m3
                    ⟨st3, hlen3, hsc3, hcore3, har3, hk3_le, hlm3, hmrk3, hm3⟩ hJ3
                  have hcl3 := hlen3.core_ok; have harl3 := hcl3.arena_len_arr
                  have hlml3 := hcl3.lit_mark_len
                  s_split
                  · have hk3_lt : k3.toNat < nsz.toNat := hc
                    have hk3_1 := fullSubst_add_u32_toNat (k := k3) (by omega)
                    have hpk3_eq := fullSubst_off3_toNat (p := p) (k := k3) (by omega)
                    have hpk3_lt : (p + 3#64 + BitVec.setWidth 64 k3).toNat <
                        st3.core.arena.length := by rw [hpk3_eq, harl3]; omega
                    have hrl3_lt_v : (st3.core.arena[(p + 3#64 +
                        BitVec.setWidth 64 k3).toNat]'hpk3_lt).toNat < 2 * st.core.cur_vars := by
                      have hg := hlt2 k3.toNat (by omega)
                      rw [← har3, List.getElem?_eq_getElem
                        (by rw [hpk3_eq] at hpk3_lt; exact hpk3_lt), Option.getD_some] at hg
                      simpa only [hpk3_eq] using hg
                    have hrl3_lt_lm : (BitVec.setWidth 64 (st3.core.arena[(p + 3#64 +
                        BitVec.setWidth 64 k3).toNat]'hpk3_lt)).toNat <
                        st3.core.lit_mark.length := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlml3]; omega
                    s_steps
                    let lm3' := st3.core.lit_mark.set (BitVec.setWidth 64 (st3.core.arena[(p +
                      3#64 + BitVec.setWidth 64 k3).toNat]'hpk3_lt)).toNat 0#8
                    let st3' : FullState := { st3 with core := { st3.core with lit_mark := lm3' } }
                    have hset_idx : (BitVec.setWidth 64 (st3.core.arena[(p + 3#64 +
                        BitVec.setWidth 64 k3).toNat]'hpk3_lt)).toNat =
                        (st3.core.arena[p.toNat + 3 + k3.toNat]'(by rw [harl3]; omega)).toNat := by
                      have hlt32 := (st3.core.arena[(p + 3#64 +
                        BitVec.setWidth 64 k3).toNat]'hpk3_lt).isLt
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      exact congrArg BitVec.toNat (bv32_getElem_congr hpk3_eq)
                    refine hJ3 (k3 + 1#32, ()) _ (by dsimp only; omega)
                      ⟨st3', ⟨{ hcl3 with lit_mark_len := by simp [st3', lm3', hlml3] },
                          hlen3.scratch_ok⟩,
                        hsc3, hcore3, har3, by omega, ?_, by simpa [st3'] using hmrk3,
                        by assumption⟩
                    intro x hx hnz; dsimp only [st3', lm3'] at hnz; rw [hset_idx] at hnz
                    by_cases hxeq :
                        x = (st3.core.arena[p.toNat + 3 + k3.toNat]'(by rw [harl3]; omega)).toNat
                    · rw [hxeq, List.getElem?_set_self (by rw [hlml3, ← hxeq]; exact hx)] at hnz
                      exact absurd rfl hnz
                    · rw [List.getElem?_set_ne (Ne.symm hxeq)] at hnz
                      obtain ⟨i, hi1, hi2, hieq⟩ := hlm3 x hx hnz
                      have hine : i ≠ k3.toNat := by
                        intro hieq'; subst hieq'
                        rw [List.getElem?_eq_getElem (by rw [harl3]; omega),
                          Option.getD_some] at hieq
                        exact hxeq hieq.symm
                      exact ⟨i, by omega, hi2, hieq⟩
                  · have hk3_eq : k3.toNat = nsz.toNat := by
                      have hnl : ¬ k3.toNat < nsz.toNat := hc; omega
                    have hlm3_zero : ∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 = 0#8 :=
                      fun x hx => Classical.byContradiction fun hnz => by
                        obtain ⟨i, hi1, hi2, _⟩ := hlm3 x hx hnz; omega
                    have har3_lt : ∀ j < sz32.toNat,
                        (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars :=
                      fun j hj => har3 ▸ hlt2 j hj
                    have har3_pw : ∀ i j, i < j → j < nsz.toNat →
                        (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
                        (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2 :=
                      fun i j hij hj => har3 ▸ hpw2 i j hij hj
                    have har3_out : ∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz32.toNat ≤ i →
                        st3.core.arena[i]? = st.core.arena[i]? := fun i hi => har3 ▸ hout2 i hi
                    have har3_pad : ∀ j, nsz.toNat ≤ j → j < sz32.toNat →
                        st3.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]? :=
                      fun j hj1 hj2 => har3 ▸ hpad2 j hj1 hj2
                    have har3_in_out : ∀ i, i < p.toNat ∨ p.toNat + 3 + sz32.toNat ≤ i →
                        st3.core.arena[i]? = st.core.arena[i]? := fun i hi => by
                      rcases hi with h1 | h2
                      · exact har3_out i (Or.inl (by omega))
                      · exact har3_out i (Or.inr h2)
                    s_to_group; refine wp_join_group (ts := [])
                      (fun () m4 => RewriteArClauseDoneInv c F0 F_cur s0 st m4 R) ?_ ?_
                    · rintro _ ⟨⟩ m4 ⟨st4, hsp4, hcv4, hl04, hfl4, hrp4, hal4, hrefs4, hm4⟩
                      s_steps
                      exact hJ (np, ()) m4 hnp_meas
                        ⟨st4, hsp4, hcv4, hl04, hfl4, hrp4, hal4,
                         by rw [hal4, ← hal, hrefs4]; exact hnp_pos, hm4⟩
                    · intro Jdone hDone; s_to_group
                      refine wp_join_group (ts := [])
                        (fun () mg =>
                          st3.LengthsOk c ∧ (FullMem c st3 ⋆ R) mg ∧ (taut = true ∨ nsz.toNat ≤ 2))
                        ?_ ?_
                      · rintro _ ⟨⟩ mg ⟨_, hmg, hcond⟩
                        have hp_lt3 : p.toNat < st3.core.arena.length := by rw [harl3]; omega
                        s_steps
                        let st4 : FullState :=
                          { st3 with core := { st3.core with
                              arena := st3.core.arena.set p.toNat (hdr ||| 0x00080000#32)
                              arena_garbage := st3.core.arena_garbage + 3#64 +
                                BitVec.setWidth 64 sz32 } }
                        obtain ⟨hsp4, hrefs4, hal4⟩ :=
                          overwriteGarb_lits_level0_preserves_fullSparse (s' := st4) hsp hl0_st hsc3
                            (replace_ag_eq hcore3) hp_ref
                            (by show st4.core.arena.length = c.arena_cap
                                dsimp only [st4]; rw [List.length_set, harl3])
                            hlml3 hlm3_zero
                            (by show st4.core.arena[p.toNat]? = _
                                dsimp only [st4]; rw [List.getElem?_set_self hp_lt3, hhdr_eq])
                            (by show st4.core.arena[p.toNat + 2]? = _
                                dsimp only [st4]
                                rw [List.getElem?_set_ne (by omega : p.toNat ≠ p.toNat + 2)]
                                exact har3_out (p.toNat + 2) (Or.inl (by omega)))
                            (fun i hi => by
                              show st4.core.arena[i]? = _
                              have hne : p.toNat ≠ i := by rw [← hsz_eq] at hi; omega
                              dsimp only [st4]; rw [List.getElem?_set_ne hne]
                              exact har3_in_out i (by rw [← hsz_eq] at hi; exact hi))
                        have ⟨hcv4, hl04, hfl4, hrp4⟩ : st4.core.cur_vars = s0.core.cur_vars ∧
                            st4.core.cur_level = 0 ∧ st4.core.fuel = s0.core.fuel ∧
                            st4.core.repr = s0.core.repr :=
                          ⟨(congrArg FullCoreState.cur_vars hcore3).trans hcv,
                           (congrArg FullCoreState.cur_level hcore3).trans hl0_st,
                           (congrArg FullCoreState.fuel hcore3).trans hfl,
                           (congrArg FullCoreState.repr hcore3).trans hrp⟩
                        have hal4' : st4.core.arena_len = s0.core.arena_len := hal4.trans hal
                        have hm4 : (FullMem c st4 ⋆ R) m := by assumption
                        have hp3_eq : (p + 3#64).toNat = p.toNat + 3 := by
                          rw [BitVec.toNat_add, show (3#64).toNat = 3 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        have hp4_eq : (p + 4#64).toNat = p.toNat + 4 := by
                          rw [BitVec.toNat_add, show (4#64).toNat = 4 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        s_to_group; refine wp_join_group (ts := [])
                          (fun () m4a => (taut = true ∨ 1 ≤ nsz.toNat) ∧ (FullMem c st4 ⋆ R) m4a)
                          ?_ ?_
                        · rintro _ ⟨⟩ m4a ⟨ht0_ok, hm4a⟩
                          s_to_group; refine wp_join_group (ts := [])
                            (fun () m5 => ∃ st5 : FullState,
                              st5.core.arena = st4.core.arena ∧ FullSparseInvW c F0 F_cur st5 ∧
                              st5.core.cur_vars = s0.core.cur_vars ∧ st5.core.cur_level = 0 ∧
                              st5.core.fuel = s0.core.fuel ∧ st5.core.repr = s0.core.repr ∧
                              st5.core.arena_len = s0.core.arena_len ∧
                              fullArenaClauseRefs st5 = fullArenaClauseRefs st ∧
                              (FullMem c st5 ⋆ R) m5)
                            ?_ ?_
                          · rintro _ ⟨⟩ m5 ⟨st5, har5_eq, hsp5, hcv5, hl05, hfl5, hrp5, hal5,
                                hrefs5, hm5⟩
                            s_split
                            · s_steps; exact hDone () m5
                                ⟨st5, hsp5, hcv5, hl05, hfl5, hrp5, hal5, hrefs5, hm5⟩
                            · have htaut_f2 : taut = false := by
                                cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                              s_split
                              · have hnsz2 : nsz.toNat = 2 := by
                                  have hbe : nsz = 2#32 := hc; rw [hbe]; rfl
                                have harl5 := hsp5.1.core_ok.arena_len_arr
                                have hp3_lt5 : (p + 3#64).toNat < st5.core.arena.length := by
                                  rw [hp3_eq, harl5]; omega
                                have hp4_lt5 : (p + 4#64).toNat < st5.core.arena.length := by
                                  rw [hp4_eq, harl5]; omega
                                have hget_p3 : st5.core.arena[(p + 3#64).toNat]'hp3_lt5 =
                                    st3.core.arena[p.toNat + 3]'(by rw [harl3]; omega) :=
                                  list_getElem_eq_of_getElem? hp3_eq (by
                                    rw [har5_eq]; dsimp only [st4]
                                    rw [List.getElem?_set_ne (by omega)])
                                have hget_p4 : st5.core.arena[(p + 4#64).toNat]'hp4_lt5 =
                                    st3.core.arena[p.toNat + 4]'(by rw [harl3]; omega) :=
                                  list_getElem_eq_of_getElem? hp4_eq (by
                                    rw [har5_eq]; dsimp only [st4]
                                    rw [List.getElem?_set_ne (by omega)])
                                have hent_b : (cnfOfClauses F_cur).EntailsClause
                                    (cnfClause
                                      [(st5.core.arena[(p + 3#64).toNat]'hp3_lt5).toNat,
                                       (st5.core.arena[(p + 4#64).toNat]'hp4_lt5).toNat]) := by
                                  refine entails_clause_subst (fun l hl => ?_)
                                    (hsp.2.1.arena.entails p.toNat hp_ref hng)
                                  obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff
                                    (by rw [harl]; omega)).mp hl
                                  rw [hsz_core] at hj
                                  obtain ⟨m', hm', heqv⟩ := hent2 htaut_f2 j (by omega)
                                  rcases (by omega : m' = 0 ∨ m' = 1) with rfl | rfl
                                  · refine ⟨_, List.mem_cons_self, ?_⟩
                                    rw [hget_p3]
                                    rw [← har3, Nat.add_zero,
                                      List.getElem?_eq_getElem (by rw [harl]; omega),
                                      List.getElem?_eq_getElem (by rw [harl3]; omega),
                                      Option.getD_some, Option.getD_some] at heqv
                                    exact heqv
                                  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                                    rw [hget_p4]
                                    rw [← har3, show p.toNat + 3 + 1 = p.toNat + 4 by omega,
                                      List.getElem?_eq_getElem (by rw [harl]; omega),
                                      List.getElem?_eq_getElem (by rw [harl3]; omega),
                                      Option.getD_some, Option.getD_some] at heqv
                                    exact heqv
                                s_steps; s_call hAddBin
                                refine ⟨c, F0, F_cur, st5, R, rfl, hsp5.1, hsp5.2.1, hl05,
                                  fun _ _ => hent_b, hm5, ?_⟩
                                intro r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 st6
                                  hlen6 hw6 _ hr20 _ hm6
                                have hsp6 := fullSparseInvW_afterAddBin hsp5 hlen6 hw6
                                s_steps
                                · exact hQ false st6 m6 hsp6 hl05 hcv5 hfl5
                                    (fun _ => (hr20 hc).1) hm6
                                · exact hDone () m6
                                    ⟨st6, hsp6, hcv5, hl05, hfl5, hrp5, hal5, hrefs5, hm6⟩
                              · s_steps; exact hDone () m5
                                  ⟨st5, hsp5, hcv5, hl05, hfl5, hrp5, hal5, hrefs5, hm5⟩
                          · intro J_1 hJ_1; s_split
                            · s_steps; exact hJ_1 () m4a
                                ⟨st4, rfl, hsp4, hcv4, hl04, hfl4, hrp4, hal4', hrefs4, hm4a⟩
                            · have htaut_f1 : taut = false := by
                                cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                              s_split
                              · have hnsz1 : nsz.toNat = 1 := by
                                  have hbe : nsz = 1#32 := hc; rw [hbe]; rfl
                                have hp3_lt4 : (p + 3#64).toNat < st4.core.arena.length := by
                                  rw [hp3_eq, show st4.core.arena.length =
                                    st3.core.arena.length by simp [st4], harl3]; omega
                                have hlit_get : st4.core.arena[(p + 3#64).toNat]'hp3_lt4 =
                                    st3.core.arena[p.toNat + 3]'(by rw [harl3]; omega) :=
                                  list_getElem_eq_of_getElem? hp3_eq (by
                                    dsimp only [st4]; rw [List.getElem?_set_ne (by omega)])
                                have hlit_lt_cv :
                                    (st4.core.arena[(p + 3#64).toNat]'hp3_lt4).toNat <
                                      2 * st4.core.cur_vars := by
                                  rw [hlit_get, hcv4, ← hcv]
                                  have h0 := har3_lt 0 (by omega)
                                  rwa [Nat.add_zero,
                                    List.getElem?_eq_getElem (by rw [harl3]; omega),
                                    Option.getD_some] at h0
                                have hlit_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause
                                    [(st4.core.arena[(p + 3#64).toNat]'hp3_lt4).toNat]) := by
                                  refine entails_clause_subst (fun l hl => ?_)
                                    (hsp.2.1.arena.entails p.toNat hp_ref hng)
                                  obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff
                                    (by rw [harl]; omega)).mp hl
                                  rw [hsz_core] at hj
                                  obtain ⟨m', hm', heqv⟩ := hent2 htaut_f1 j (by omega)
                                  have hm0 : m' = 0 := by omega
                                  subst hm0; refine ⟨_, List.mem_singleton.mpr rfl, ?_⟩
                                  rw [hlit_get]
                                  rw [← har3, Nat.add_zero,
                                    List.getElem?_eq_getElem (by rw [harl]; omega),
                                    List.getElem?_eq_getElem (by rw [harl3]; omega),
                                    Option.getD_some, Option.getD_some] at heqv
                                  exact heqv
                                s_steps; s_call hAddUnit
                                refine ⟨c, F0, F_cur, st4, R, rfl, hsp4.1, hsp4.2.1,
                                  fun _ => hlit_ent, hm4a, ?_⟩
                                intro ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 st5
                                  hlen5 hw5 hcl5 hfail5 _ hm5
                                have hsp5 := fullSparseInvW_afterAddUnit hsp4 hlen5 hw5
                                s_steps
                                · exact hJ_1 () m5
                                    ⟨st5, rfl, hsp5, hcv4, hcl5, hfl4, hrp4, hal4', hrefs4, hm5⟩
                                · exact hQ false st5 m5 hsp5 hcl5 hcv4 hfl4
                                    (fun _ => (hfail5 hlit_lt_cv (by
                                      cases ok <;> first | rfl | contradiction |
                                        exact absurd rfl hc)).1) hm5
                              · s_steps; exact hJ_1 () m4a
                                  ⟨st4, rfl, hsp4, hcv4, hl04, hfl4, hrp4, hal4', hrefs4, hm4a⟩
                        · intro J0 hJ0; s_split
                          · s_steps; exact hJ0 () _ ⟨Or.inl hc, by assumption⟩
                          · have htaut_f0 : taut = false := by
                              cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                            s_split
                            · exfalso; have hnsz0 : nsz.toNat = 0 := by
                                have hbe : nsz = 0#32 := hc; rw [hbe]; rfl
                              have := hnsz_pos htaut_f0; omega
                            · s_steps; exact hJ0 () _ ⟨Or.inr (hnsz_pos htaut_f0), by assumption⟩
                      · intro Jgarb hGarb; s_split
                        · s_steps; exact hGarb () m3 ⟨hlen3, hm3, Or.inl hc⟩
                        · s_split
                          · s_steps; exact hGarb () m3 ⟨hlen3, hm3, Or.inr hc⟩
                          · have htaut_f : taut = false := by
                              cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                            have hnsz3 : 3 ≤ nsz.toNat := by
                              have hnot : ¬ nsz.toNat ≤ 2 := hc; omega
                            s_to_group; refine wp_join_group (ts := [])
                              (fun () m4 => RewriteArClauseDoneInv c F0 F_cur s0 st m4 R) ?_ ?_
                            · rintro _ ⟨⟩ m4 ⟨st4, hsp4, hcv4, hl04, hfl4, hrp4, hal4, hrefs4, hm4⟩
                              s_steps; exact hDone () m4
                                ⟨st4, hsp4, hcv4, hl04, hfl4, hrp4, hal4, hrefs4, hm4⟩
                            · intro Jshr hShr
                              have hent_n : (cnfOfClauses F_cur).EntailsClause
                                  (cnfClause ((List.range nsz.toNat).map fun j =>
                                    (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat)) :=
                                entails_clause_subst (fun l hl => by
                                  obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff
                                    (by rw [harl]; omega)).mp hl
                                  rw [hsz_core] at hj
                                  obtain ⟨m', hm', heqv⟩ := hent2 htaut_f j (by omega)
                                  refine ⟨_, List.mem_map.mpr ⟨m', List.mem_range.mpr hm', rfl⟩, ?_⟩
                                  rw [← har3, List.getElem?_eq_getElem (by rw [harl]; omega),
                                    Option.getD_some] at heqv
                                  exact heqv)
                                  (hsp.2.1.arena.entails p.toNat hp_ref hng)
                              have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by
                                rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                              have hnsz_ofNat : BitVec.ofNat 32 nsz.toNat = nsz :=
                                BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat,
                                  Nat.mod_eq_of_lt nsz.isLt])
                              s_split
                              · have hnsz_lt : nsz.toNat < sz32.toNat := hc
                                have hp2_lt3 : (p + 2#64).toNat < st3.core.arena.length := by
                                  rw [hp2_eq, harl3]; omega
                                have hp1_lt3 : (p + 1#64).toNat < st3.core.arena.length := by
                                  rw [hp1_eq, harl3]; omega
                                s_steps
                                let ar4a := (st3.core.arena.set (p + 2#64).toNat nsz).set
                                  (p + 1#64).toNat 2#32
                                have har4a_def : ar4a = (st3.core.arena.set (p.toNat + 2) nsz).set
                                    (p.toNat + 1) 2#32 := by dsimp only [ar4a]; rw [hp2_eq, hp1_eq]
                                s_to_group; refine wp_join_group (ts := [])
                                  (fun () m4 => RewriteArClauseDoneInv c F0 F_cur s0 st m4 R) ?_ ?_
                                · rintro _ ⟨⟩ m4
                                    ⟨st4, hsp4, hcv4, hl04, hfl4, hrp4, hal4, hrefs4, hm4⟩
                                  s_steps; exact hShr () m4
                                    ⟨st4, hsp4, hcv4, hl04, hfl4, hrp4, hal4, hrefs4, hm4⟩
                                · intro Jshrk hShrk; s_split
                                  · have hshrk_z : (hdr &&& 0x00800000#32) = 0#32 := hc
                                    have hp_lt3 : p.toNat < st3.core.arena.length := by
                                      rw [harl3]; omega
                                    have hsent_idx :
                                        (p + 3#64 + BitVec.setWidth 64
                                          (st.core.arena[(p + 2#64).toNat]'hp2_lt) - 1#64).toNat =
                                          p.toNat + 3 + sz32.toNat - 1 := by
                                      change (p + 3#64 + BitVec.setWidth 64 sz32 - 1#64).toNat = _
                                      have hoff3 : (p + 3#64 + BitVec.setWidth 64 sz32).toNat =
                                          p.toNat + 3 + sz32.toNat :=
                                        fullSubst_off3_toNat (p := p) (k := sz32) (by omega)
                                      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                                          rw [hoff3, show (1#64).toNat = 1 from rfl]; omega)),
                                        hoff3, show (1#64).toNat = 1 from rfl]
                                    have hsent_lt3 :
                                        (p + 3#64 + BitVec.setWidth 64
                                          (st.core.arena[(p + 2#64).toNat]'hp2_lt) - 1#64).toNat <
                                          st3.core.arena.length := by rw [hsent_idx, harl3]; omega
                                    s_steps
                                    let ar4b := ((ar4a.set p.toNat (hdr ||| 0x00800000#32)).set
                                      (p + 3#64 + BitVec.setWidth 64
                                        (st.core.arena[(p + 2#64).toNat]'hp2_lt) - 1#64).toNat
                                      0xFFFFFFFF#32)
                                    have har4b_def : ar4b = ((ar4a.set p.toNat
                                        (hdr ||| 0x00800000#32)).set
                                        (p.toNat + 3 + sz32.toNat - 1) 0xFFFFFFFF#32) := by
                                      dsimp only [ar4b]; rw [hsent_idx]
                                    refine hShrk () _ (rewriteAr_shrink_done (ar4 := ar4b)
                                      hsp hl0_st hcv hfl hrp hal hp_ref hng hsz_eq hnsz3 (by omega)
                                      hsc3 hcore3 (by rw [har4b_def, har4a_def]; simp [harl3])
                                      hlml3 hlm3_zero ?_ ?_ ?_ ?_ ?_ har3_pad har3_in_out har3_lt
                                      har3_pw hent_n ?_)
                                    · rw [har4b_def, ← hsz_eq, hhdr_eq]
                                      simp only [hnsz_lt, hshrk_z, and_self, ite_true]
                                      rw [List.getElem?_set_ne
                                          (by omega : p.toNat + 3 + sz32.toNat - 1 ≠ p.toNat),
                                        List.getElem?_set_self (by
                                          dsimp only [ar4a]
                                          simp only [List.length_set, harl3]; omega)]
                                    · rw [har4b_def, har4a_def,
                                        List.getElem?_set_ne
                                          (by omega : p.toNat + 3 + sz32.toNat - 1 ≠ p.toNat + 2),
                                        List.getElem?_set_ne (by omega : p.toNat ≠ p.toNat + 2),
                                        List.getElem?_set_ne (by omega : p.toNat + 1 ≠ p.toNat + 2),
                                        List.getElem?_set_self (by rw [harl3]; omega), hnsz_ofNat]
                                    · intro _ _; rw [har4b_def, ← hsz_eq]
                                      exact List.getElem?_set_self (by
                                        dsimp only [ar4a]
                                        simp only [List.length_set, harl3]; omega)
                                    · intro _ hne; exact absurd (hhdr_eq.symm ▸ hshrk_z) hne
                                    · intro i h0 h1 h2 h3; rw [har4b_def, har4a_def,
                                        List.getElem?_set_ne (h3 hnsz_lt).symm,
                                        List.getElem?_set_ne h0.symm, List.getElem?_set_ne h1.symm,
                                        List.getElem?_set_ne h2.symm]
                                    · assumption
                                  · have hshrk_ne : (hdr &&& 0x00800000#32) ≠ 0#32 := hc
                                    s_steps
                                    refine hShrk () _ (rewriteAr_shrink_done (ar4 := ar4a)
                                      hsp hl0_st hcv hfl hrp hal hp_ref hng hsz_eq hnsz3 (by omega)
                                      hsc3 hcore3 (by rw [har4a_def]; simp [harl3]) hlml3 hlm3_zero
                                      ?_ ?_ ?_ ?_ ?_ har3_pad har3_in_out har3_lt har3_pw hent_n ?_)
                                    · rw [har4a_def, hhdr_eq]
                                      simp only [hshrk_ne, and_false, ite_false]
                                      rw [List.getElem?_set_ne (by omega : p.toNat + 1 ≠ p.toNat),
                                        List.getElem?_set_ne (by omega : p.toNat + 2 ≠ p.toNat)]
                                      exact (har3_out p.toNat (Or.inl (by omega))).trans
                                        (List.getElem?_eq_getElem (by rw [harl]; omega))
                                    · rw [har4a_def,
                                        List.getElem?_set_ne (by omega : p.toNat + 1 ≠ p.toNat + 2),
                                        List.getElem?_set_self (by rw [harl3]; omega), hnsz_ofNat]
                                    · intro _ hz; exact absurd (hhdr_eq ▸ hz) hshrk_ne
                                    · intro _ _; rw [har4a_def, ← hsz_eq,
                                        List.getElem?_set_ne (by omega),
                                        List.getElem?_set_ne (by omega),
                                        show p.toNat + 3 + sz32.toNat - 1 =
                                          p.toNat + 3 + (sz32.toNat - 1) by omega]
                                      exact har3_pad (sz32.toNat - 1) (by omega) (by omega)
                                    · intro i _ h1 h2 _; rw [har4a_def,
                                        List.getElem?_set_ne h1.symm, List.getElem?_set_ne h2.symm]
                                    · assumption
                              · have hnsz_eq : nsz.toNat = sz32.toNat := by
                                  have hnot : ¬ nsz.toNat < sz32.toNat := hc; omega
                                s_steps
                                refine hShr () m3 (rewriteAr_shrink_done (ar4 := st3.core.arena)
                                  hsp hl0_st hcv hfl hrp hal hp_ref hng hsz_eq hnsz3 (by omega)
                                  hsc3 hcore3 harl3 hlml3 hlm3_zero ?_ ?_ ?_ ?_
                                  (fun _ _ _ _ _ => rfl) har3_pad har3_in_out har3_lt har3_pw
                                  hent_n hm3)
                                · simp only [hhdr_eq, ← hsz_eq, hnsz_eq, Nat.lt_irrefl, false_and,
                                    ite_false]
                                  exact (har3_out p.toNat (Or.inl (by omega))).trans
                                    (List.getElem?_eq_getElem (by rw [harl]; omega))
                                · rw [hnsz_eq, show BitVec.ofNat 32 sz32.toNat = sz32 from
                                    BitVec.eq_of_toNat_eq (by
                                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sz32.isLt])]
                                  rw [← hp2_get]; exact har3_out (p.toNat + 2) (Or.inl (by omega))
                                · intro hlt; rw [← hsz_eq, hnsz_eq] at hlt; omega
                                · intro hlt; rw [← hsz_eq, hnsz_eq] at hlt; omega
              · rintro B2 L2 _ ⟨k, nsz, ⟨⟩⟩ m2 hB2 hL2
                  ⟨hk_n, ⟨st2, ⟨hlen2, hsc2, hcore2, hnsz_le, hpad2, hout2, hlt2, hpw2, hlm2,
                     hmrk2, hm2⟩, hk_le, hnsz_k, hnsz_pos, hent2⟩⟩
                subst hk_n
                have hcl2 := hlen2.core_ok; have harl2 := hcl2.arena_len_arr
                have hlml2 := hcl2.lit_mark_len; have hrpl2 := hcl2.repr_len
                have hrp2 : st2.core.repr = st.core.repr := by
                  rcases st with ⟨c0, _⟩; rcases st2 with ⟨c2, _⟩
                  rcases c0; rcases c2; cases hcore2; rfl
                s_split
                · have hk_lt : k.toNat < sz32.toNat := hc
                  have hk1 := fullSubst_add_u32_toNat (k := k) (by omega)
                  have hpk_eq := fullSubst_off3_toNat (p := p) (k := k) (by omega)
                  have hpk_lt :
                      (p + 3#64 + BitVec.setWidth 64 k).toNat < st2.core.arena.length := by
                    rw [hpk_eq, harl2]; omega
                  let l2 := st2.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt
                  have hl2_orig_eq : st2.core.arena[p.toNat + 3 + k.toNat]? = some l2 := by
                    dsimp only [l2]; rw [← hpk_eq, List.getElem?_eq_getElem hpk_lt]
                  have hl2_lt_v : l2.toNat < 2 * st.core.cur_vars := by
                    have hg := hlt2 k.toNat hk_lt
                    rw [hl2_orig_eq, Option.getD_some] at hg; exact hg
                  have hl2_lt_rp : (BitVec.setWidth 64 l2).toNat < st2.core.repr.length := by
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hrpl2]; omega
                  let rl2 := st2.core.repr[(BitVec.setWidth 64 l2).toNat]'hl2_lt_rp
                  have hrl2_eq_get : st.core.repr[l2.toNat]?.getD 0#32 = rl2 := by
                    have hz : (BitVec.setWidth 64 l2).toNat = l2.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    dsimp only [rl2]; rw [← hrp2]
                    rw [bv32_getElem_congr (xs := st2.core.repr) hz
                        (hi := hl2_lt_rp) (hj := by rw [hrpl2]; omega),
                      List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hrl2_lt_v : rl2.toNat < 2 * st.core.cur_vars := by
                    rw [← hrl2_eq_get]; exact FullReprEquiv.lt hrepr_st hl2_lt_v
                  have hrl2_eqv : LitEquiv (cnfOfClauses F_cur) l2.toNat rl2.toNat := by
                    rw [← hrl2_eq_get]; exact FullReprEquiv.litEquiv hrepr_st hl2_lt_v
                  have hidx_rl2 :
                      st2.core.repr[(st2.core.arena[(p.toNat + 3 + k.toNat) % 2 ^ 64]'(by
                        rw [Nat.mod_eq_of_lt (by omega), harl2]; omega)).toNat]'(by
                        have heq_l : st2.core.arena[(p.toNat + 3 + k.toNat) % 2 ^ 64]'(by
                            rw [Nat.mod_eq_of_lt (by omega), harl2]; omega) = l2 := by
                          dsimp only [l2]
                          exact bv32_getElem_congr (by rw [hpk_eq, Nat.mod_eq_of_lt (by omega)])
                        rw [heq_l, hrpl2]; omega) = rl2 := by
                    dsimp only [rl2]; refine bv32_getElem_congr ?_
                    have hsw : (BitVec.setWidth 64 l2).toNat = l2.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    exact (congrArg BitVec.toNat (bv32_getElem_congr (by
                      show (p.toNat + 3 + k.toNat) % 2 ^ 64 =
                        (p + 3#64 + BitVec.setWidth 64 k).toNat
                      rw [Nat.mod_eq_of_lt (by omega), hpk_eq]))).trans hsw.symm
                  have hrl2_1_lt_lm :
                      (BitVec.setWidth 64 (rl2 ^^^ 1#32)).toNat < st2.core.lit_mark.length := by
                    have hnx := litNeg_lt_two_mul hrl2_lt_v
                    rw [BitVec.toNat_setWidth, bv32_xor1_toNat, Nat.mod_eq_of_lt (by omega), hlml2]
                    omega
                  s_split
                  · s_steps; exact hB2 (k, true, nsz, ()) m2
                      ⟨st2, ⟨hlen2, hsc2, hcore2, by omega, hpad2, hout2, hlt2, hpw2, hlm2, hmrk2,
                         hm2⟩, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
                  · have hrl2_1_z64 :
                        (BitVec.setWidth 64 (rl2 ^^^ 1#32)).toNat = rl2.toNat ^^^ 1 := by
                      have hnx := litNeg_lt_two_mul hrl2_lt_v
                      rw [BitVec.toNat_setWidth, bv32_xor1_toNat, Nat.mod_eq_of_lt (by omega)]
                    have hlm_neg0 : st2.core.lit_mark[rl2.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
                      rewriteAr_lm_get_zero (hi := by rw [← hrl2_1_z64]; exact hrl2_1_lt_lm)
                        (hrl2_1_z64.trans (congrArg (·.toNat ^^^ 1) hidx_rl2.symm)) hc
                    have hrl2_lt_lm :
                        (BitVec.setWidth 64 rl2).toNat < st2.core.lit_mark.length := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlml2]; omega
                    have hrl_z64 : (BitVec.setWidth 64 rl2).toNat = rl2.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    s_to_group; refine wp_join_group (ts := [i32])
                      (fun (nsz', ()) m2' =>
                        RewriteArLoop2Inv c F_cur st p sz32.toNat (k + 1#32) nsz' m2' R)
                      ?_ ?_
                    · rintro _ ⟨nsz', ⟨⟩⟩ m2' h2'; s_steps
                      exact hL2 (sz32.toNat - (k + 1#32).toNat) (k + 1#32, nsz', ())
                        m2' (by omega) ⟨rfl, h2'⟩
                    · intro Jnsz hJnsz; s_split
                      · have hlm_pos0 : st2.core.lit_mark[rl2.toNat]?.getD 0#8 = 0#8 :=
                          rewriteAr_lm_get_zero (hi := by rw [← hrl_z64]; exact hrl2_lt_lm)
                            (hrl_z64.trans (congrArg BitVec.toNat hidx_rl2.symm)) hc
                        have hpnsz_eq := fullSubst_off3_toNat (p := p) (k := nsz) (by omega)
                        have hpnsz_lt : (p + 3#64 + BitVec.setWidth 64 nsz).toNat <
                            st2.core.arena.length := by rw [hpnsz_eq, harl2]; omega
                        have hnsz1 := fullSubst_add_u32_toNat (k := nsz) (by omega)
                        s_steps
                        refine hJnsz (nsz + 1#32, ()) _ (rewriteAr_loop2_push_step hk_lt hsz3 hk1
                          hnsz1 hlen2 hsc2 hcore2 hnsz_k hpad2 hout2 hlt2 hpw2 hent2 hlm2 hmrk2
                          hcv_le (by rw [harl2]; omega) hl2_orig_eq hrl2_lt_v hrl2_eqv hlm_neg0
                          hlm_pos0 ?_)
                        · rw [← hrl_z64, ← hpnsz_eq]; assumption
                      · have hlm_nz : st2.core.lit_mark[rl2.toNat]?.getD 0#8 ≠ 0#8 :=
                          rewriteAr_lm_get_ne (hi := by rw [← hrl_z64]; exact hrl2_lt_lm)
                            (hrl_z64.trans (congrArg BitVec.toNat hidx_rl2.symm)) hc
                        obtain ⟨m_dup, hm_dup_lt, hm_dup_eq⟩ :=
                          (hlm2 rl2.toNat (by omega)).mp hlm_nz
                        s_steps; refine hJnsz (nsz, ()) m2
                          ⟨st2, ⟨hlen2, hsc2, hcore2, by omega, hpad2, hout2, hlt2, hpw2, hlm2,
                             hmrk2, hm2⟩, by omega, by omega, fun _ => by omega, ?_⟩
                        intro j hj
                        by_cases hjk : j = k.toNat
                        · subst hjk; refine ⟨m_dup, hm_dup_lt, ?_⟩
                          have hpad_k := hpad2 k.toNat hnsz_k hk_lt
                          have hl2_orig : (st.core.arena[p.toNat + 3 + k.toNat]?.getD 0#32).toNat =
                              l2.toNat := by rw [← hpad_k, hl2_orig_eq, Option.getD_some]
                          rw [hl2_orig, hm_dup_eq]; exact hrl2_eqv
                        · exact hent2 j (by omega)
                · have hk_eq : k.toNat = sz32.toNat := by
                    have hnl : ¬ k.toNat < sz32.toNat := hc; omega
                  s_steps
                  exact hB2 (k, false, nsz, ()) m2
                    ⟨st2, ⟨hlen2, hsc2, hcore2, hnsz_le, hpad2, hout2, hlt2,
                       hpw2, hlm2, hmrk2, hm2⟩,
                     fun _ => hnsz_pos (by omega), fun _ j hj => hent2 j (by omega)⟩
              · intro B2 L2 _ hL2; s_steps
                refine hL2 sz32.toNat (0#32, 0#32, ()) m1
                  ⟨rfl, st, ⟨hsp.1, rfl, rfl, Nat.zero_le _, fun _ _ _ => rfl, fun _ _ => rfl, ?_,
                     fun _ _ _ h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega,
                     ?_, hsp.2.2.1.1, hm1⟩,
                   Nat.zero_le _, Nat.zero_le _,
                   fun h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega,
                   fun _ h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega⟩
                · intro j hj
                  have hm_lt : (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat ∈
                      fullArenaClauseLits st p.toNat := by
                    unfold fullArenaClauseLits
                    have hj_bd : j < fullArenaClauseSizeCore st.core p.toNat := by
                      rw [hsz_core]; exact hj
                    have hm_elt := (mem_fullArenaClauseLitsCore_iff
                      (by rw [harl]; omega)).mpr ⟨j, hj_bd, rfl⟩
                    rw [List.getElem?_eq_getElem (by rw [harl]; omega), Option.getD_some]
                    exact hm_elt
                  exact hsp.2.1.arena.lits_lt p.toNat hp_ref hng _ hm_lt
                · intro x hx; constructor
                  · intro hnz; exact absurd (hsp.2.2.1.2 x hx) hnz
                  · rintro ⟨m', hm', _⟩
                    rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at hm'; omega
            · s_steps
              exact hJ (np, ()) m1 hnp_meas ⟨st, hsp, hcv, hl0_st, hfl, hrp, hal, hnp_pos, hm1⟩
          · rintro B1 L1 _ ⟨k, ⟨⟩⟩ m1 hB1 hL1 ⟨hk_n, hk_le, hm1⟩; subst hk_n
            s_split
            · have hk_lt : k.toNat < sz32.toNat := hc
              have hk1 := fullSubst_add_u32_toNat (k := k) (by omega)
              have hpk_eq := fullSubst_off3_toNat (p := p) (k := k) (by omega)
              have hpk_lt : (p + 3#64 + BitVec.setWidth 64 k).toNat < st.core.arena.length := by
                rw [hpk_eq, harl]; omega
              s_to_group; refine wp_join_group (ts := []) (fun () mi => (FullMem c st ⋆ R) mi) ?_ ?_
              · rintro _ ⟨⟩ mi hmi; s_steps
                exact hL1 (sz32.toNat - (k + 1#32).toNat) (k + 1#32, ()) mi
                  (by omega) ⟨rfl, by omega, hmi⟩
              · intro Ji hJi; s_split
                · have hl_lt_v :
                      (st.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt).toNat <
                        2 * st.core.cur_vars := by
                    have hmem : (st.core.arena[p.toNat + 3 + k.toNat]'(by rw [harl]; omega)).toNat
                        ∈ fullArenaClauseLits st p.toNat := by
                      unfold fullArenaClauseLits
                      refine (mem_fullArenaClauseLitsCore_iff (by rw [harl]; omega)).mpr
                        ⟨k.toNat, by rw [hsz_core]; exact hk_lt, rfl⟩
                    have hl := hsp.2.1.arena.lits_lt p.toNat hp_ref hng _ hmem
                    rw [bv32_getElem_congr hpk_eq]; exact hl
                  have hl_lt_nl : (BitVec.setWidth 64
                      (st.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt)).toNat <
                      st.core.repr.length := by
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hrpl]; omega
                  s_split
                  · s_steps; exact hB1 (true, k, ()) m1 ⟨Or.inl rfl, hm1⟩
                  · s_steps; exact hJi () m1 hm1
                · s_steps; exact hJi () m1 hm1
            · s_steps; exact hB1 (false, k, ()) m1 ⟨Or.inr rfl, hm1⟩
          · intro B1 L1 _ hL1; s_steps
            exact hL1 sz32.toNat (0#32, ()) ml ⟨rfl, Nat.zero_le _, hml⟩
    · s_steps; exact hQ true st ml hsp hl0_st hcv (by rw [hfl]) (fun h => by cases h) hml

theorem full_substitute_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hTarjan : ∀ args m Q X, fullTarjanSccSpec args m Q X →
      Γ "full_tarjan_scc" [i64] [i64] args m Q X)
    (hElimVars : ∀ args m Q X, fullSubstElimVarsSpec args m Q X →
      Γ "full_subst_elim_vars" [i64, i64] [.bool] args m Q X)
    (hRewriteBins : ∀ args m Q X, fullSubstRewriteBinsSpec args m Q X →
      Γ "full_subst_rewrite_bins" [i64] [.bool] args m Q X)
    (hRewriteAr : ∀ args m Q X, fullSubstRewriteArSpec args m Q X →
      Γ "full_subst_rewrite_ar" [i64] [.bool] args m Q X)
    (hArenaSweep : ∀ args m Q X, fullArenaSweepSpec args m Q X →
      Γ "full_arena_sweep" [i64] [i64] args m Q X)
    (hProp : ∀ args m Q X, fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullSubstituteSpec args m Q X →
      Func.wp Γ full_substitute_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s0, R, rfl, hsp0, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  obtain ⟨F_cur0, hw0⟩ := hsp0.exists_witness
  have hcl0 := hsp0.1.lengths.core_ok
  have hclv_lt : s0.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  s_to_group; refine wp_join_group (ts := []) (fun () m1 => SubstituteAfterBtInv c F0 s0 m1 R) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨st1, hsp1, hl01, hfl1, hm1⟩
    s_to_group; refine wp_loop_break_group
      (fun (_r, ()) mb => SubstituteAfterBtInv c F0 s0 mb R)
      (fun n (round, ()) ml => n = 4 - round.toNat ∧ SubstituteLoopInv c F0 s0 round ml R)
      ?_ ?_ ?_
    · rintro B ⟨_r, ⟨⟩⟩ mb ⟨stb, hspb, hl0b, hflb, hmb⟩
      s_steps; exact hQ 1#64 stb mb hspb hl0b hflb (Or.inl rfl) (fun h => by cases h) hmb
    · rintro B L _ ⟨round, ⟨⟩⟩ ml hB hL ⟨hr_n, ⟨st, hsp, hl0_st, hfl_st, hr_le, hml⟩⟩
      subst hr_n; s_split
      · have hr_lt : round.toNat < 4 := hc
        have hr1 : (round + 1#64).toNat = round.toNat + 1 := by
          rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        s_split
        · s_split
          · obtain ⟨F_cur, hspw⟩ := hsp.exists_witness
            s_steps; s_call hTarjan
            refine ⟨c, F0, F_cur, st, R, rfl, hspw, hl0_st, hml, ?_⟩
            intro ucnt _ _ inc1 _ _ _ _ _ sstk1 _ m1 st1 hspw1 huc_le hus1 hrepr1 hm1
            have hl01' : st1.core.cur_level = 0 := hl0_st
            have hfl1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl_st
            s_split
            · s_steps; exact hQ 20#64 st1 m1 hspw1.toSparse hl01' hfl1' (Or.inr rfl)
                (fun _ => hspw1.2.1.ext_sound.2 (hspw1.2.1.inconsistent_sound hc)) hm1
            · s_steps; s_call hElimVars
              refine ⟨c, F0, F_cur, st1, R, rfl, hspw1, hl01', hrepr1 hc, huc_le, hus1, hm1, ?_⟩
              intro ok2 st2 m2 hspw2 hl02 _ hfl2 hrepr2 hfail2 hm2
              have hfl2' : st2.core.fuel.toNat ≤ s0.core.fuel.toNat := by omega
              s_split
              · s_split
                · s_steps; exact hB (round, ()) m2 ⟨st2, hspw2.toSparse, hl02, hfl2', hm2⟩
                · s_steps; s_call hRewriteBins
                  refine ⟨c, F0, F_cur, st2, R, rfl, hspw2, hl02, hrepr2, hm2, ?_⟩
                  intro ok3 st3 m3 hspw3 hl03 _ hfl3 hrepr3 hfail3 hm3
                  have hfl3' : st3.core.fuel.toNat ≤ s0.core.fuel.toNat := by rw [hfl3]; exact hfl2'
                  s_split
                  · s_steps; s_call hRewriteAr
                    refine ⟨c, F0, F_cur, st3, R, rfl, hspw3, hl03, hrepr3, hm3, ?_⟩
                    intro ok4 st4 m4 hspw4 hl04 _ hfl4 hfail4 hm4
                    have hfl4' : st4.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4 ▸ hfl3'
                    s_split
                    · s_steps; s_call hArenaSweep
                      refine ⟨c, F0, F_cur, st4, R, rfl, hspw4.1, hspw4.2.1, hspw4.2.2.2.1,
                        hspw4.2.2.2.2.2, fun hpos => by omega, hm4, ?_⟩
                      intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc5 m5 st5
                        hlen5 _ hext5 _ hll5 hw5 hnd5 _ _ _ hsr2 _ hm5
                      have hspw5 :=
                        fullSparseInvW_afterArenaSweep hspw4 hlen5 hext5 hll5 hw5 hnd5 rfl rfl rfl
                      have hl05 : st5.core.cur_level = 0 := hl04
                      s_split
                      · s_steps; exact hQ 20#64 st5 m5 hspw5.toSparse hl05 hfl4' (Or.inr rfl)
                          (fun _ => (hsr2 hc).2) hm5
                      · s_steps; s_call hProp
                        refine ⟨c, F0, F_cur, st5, R, rfl, hspw5.1, hspw5.2.1,
                          hspw5.2.2.2.2.2, hm5, ?_⟩
                        intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel6 _ _ _ _ _ _ _ _ m6 st6
                          hlen6 hw6 _ hperm6 hfl6 _ _ hpr1 _ _ hm6
                        have hspw6 := fullSparseInvW_afterPropagate hspw5 hlen6 hw6 hperm6
                        have hfl6' : st6.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                          have hfl5' : st5.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4'
                          dsimp only [st6]; omega
                        s_split
                        · s_steps; exact hQ 20#64 st6 m6 hspw6.toSparse hl05 hfl6' (Or.inr rfl)
                            (fun _ => level0_unsat_of_conflict_okW hw6 hl05 (hpr1 hc).2.2) hm6
                        · s_steps; exact hL (4 - (round + 1#64).toNat) (round + 1#64, ()) m6
                            (by omega) ⟨rfl, st6, hspw6.toSparse, hl05, hfl6', by omega, hm6⟩
                    · s_steps; exact hQ 20#64 st4 m4 hspw4.toSparse hl04 hfl4' (Or.inr rfl)
                        (fun _ => hfail4 (by
                          cases ok4 <;> first | rfl | contradiction | exact absurd rfl hc)) hm4
                  · s_steps; exact hQ 20#64 st3 m3 hspw3.toSparse hl03 hfl3' (Or.inr rfl)
                      (fun _ => hfail3 (by
                        cases ok3 <;> first | rfl | contradiction | exact absurd rfl hc)) hm3
              · s_steps; exact hQ 20#64 st2 m2 hspw2.toSparse hl02 hfl2' (Or.inr rfl)
                  (fun _ => hfail2 (by
                    cases ok2 <;> first | rfl | contradiction | exact absurd rfl hc)) hm2
          · s_steps; exact hB (round, ()) ml ⟨st, hsp, hl0_st, hfl_st, hml⟩
        · s_steps; exact hB (round, ()) ml ⟨st, hsp, hl0_st, hfl_st, hml⟩
      · s_steps; exact hB (round, ()) ml ⟨st, hsp, hl0_st, hfl_st, hml⟩
    · intro B L _ hL; s_steps
      exact hL 4 (0#64, ()) m1 ⟨rfl, st1, hsp1, hl01, hfl1, Nat.zero_le _, hm1⟩
  · intro Jbt hJbt; s_split
    · s_steps; s_call hBacktrack
      refine ⟨c, s0, R, rfl, hsp0.1.lengths, hclv_lt, fun _ => by
        have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega,
        hw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 st1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
      have hl01 : st1.core.cur_level = 0 := by dsimp only [st1]; rw [hcl1]; simp
      s_steps; exact hJbt () m1
        ⟨st1, fullSparseInv_afterBacktrack hsp0 hlen1 hprsc1 hw1 rfl rfl rfl rfl rfl,
         hl01, Nat.le_refl _, hm1⟩
    · have hl00 : s0.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      s_steps; exact hJbt () m ⟨s0, hsp0, hl00, Nat.le_refl _, hm⟩

end

end LeanQbe.T.Examples.Kissat.Full
