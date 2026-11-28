/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpSimplify0
public import LeanQbe.T.Examples.Kissat.Src.Vivify

/-!
# Vivify Simplify WP (`Proof.Vivify.WpSimplify`)

Canonical `Func.wp` proof (`0` legacy imports, `0` SAT model proofs) for `full_viv_simplify_m6`,
including level-0 clause filtering, glue lowering, `full_add_unit` / `full_add_bin_m6`,
in-place shrink (`PH_SHRK`), and OOM propagation.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Vivify
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
open LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. Pure Arena & Entailment Helpers -/

private abbrev VivSimpQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) (cref : Nat) : Prop :=
  ∀ r s' m',
    FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
    s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
    s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
    fullArenaClauseRefs s' = fullArenaClauseRefs s →
    s'.scratch.red_refs = s.scratch.red_refs →
    s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
    (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
    (r = 0#64 →
      cref ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref = false) →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem fullArena_updateLits_preserves_fullWitness_hnonact {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur k) {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    (hg : fullArenaClauseGarbCore k cref = false) (hnonact : NonActiveReason k cref)
    {ar' : List (BitVec 32)} {nsz : Nat}
    (har' : ar'.length = c.arena_cap) (hnsz : nsz < fullArenaClauseSizeCore k cref)
    (hout : ∀ p, (p < cref + 3 ∨ cref + 3 + nsz ≤ p) → ar'[p]? = k.arena[p]?)
    (hlits_lt : ∀ j < fullArenaClauseSizeCore k cref,
      (ar'[cref + 3 + j]?.getD 0#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { k with arena := ar' } cref))) :
    let k' : FullCoreState := { k with arena := ar' }
    k'.LengthsOk c ∧ FullWitnessInv c F0 F_cur k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
  intro k'
  have hwf := hw.arena.refs_wf cref href
  have hbd : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length := by
    have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
  have hold_ne_ff : ∀ p, cref + 3 ≤ p → p < cref + 3 + fullArenaClauseSizeCore k cref →
      ar'[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    intro p hp1 hp2
    let j := p - (cref + 3)
    have hj : j < fullArenaClauseSizeCore k cref := by omega
    have hlt := hlits_lt j hj
    have hcv := hlen.cur_vars_le; have hmx := c.hmaxv; unfold dimacsBound at hmx
    have hbdp : cref + 3 + j < ar'.length := by rw [har', ← hlen.arena_len_arr]; omega
    rw [List.getElem?_eq_getElem hbdp, Option.getD_some] at hlt
    rw [show p = cref + 3 + j by omega, List.getElem?_eq_getElem hbdp, Option.getD_some]
    intro heq; simp [heq] at hlt; omega
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r
      have h0eq : ar'[cref]? = k.arena[cref]? := hout cref (Or.inl (by omega))
      have h2eq : ar'[cref + 2]? = k.arena[cref + 2]? := hout (cref + 2) (Or.inl (by omega))
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      unfold fullArenaNextOff; dsimp only [k']
      simp only [h1, ↓reduceIte, h2eq, h2, h0eq]
      have hsz_lt : nsz < (k.arena[cref + 2]?.getD 0#32).toNat := hnsz
      split
      · refine fullArenaSkipShrk_congr fun p hp1 _ => hout p (Or.inr (by omega))
      · rfl
    · rcases (Nat.lt_or_gt_of_ne hrc) with hlt | hgt
      · have hdisj := fullArenaScanRefs_disjoint hr href hlt
        have hr_wf := hw.arena.refs_wf r hr
        exact fullArenaNextOff_congr_block (hout r (Or.inl (by omega)))
          (hout (r + 2) (Or.inl (by omega)))
          fun p _ hp2 => hout p (Or.inl (by omega))
      · have hdisj := fullArenaScanRefs_disjoint href hr hgt
        exact fullArenaNextOff_congr_block (hout r (Or.inr (by omega)))
          (hout (r + 2) (Or.inr (by omega)))
          fun p hp1 _ => hout p (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hoth_eq : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
    intro r hr hne
    have hr_wf := hw.arena.refs_wf r hr
    have hr_bd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
    have hout_r : ∀ p, r ≤ p → p < r + 3 + fullArenaClauseSizeCore k r →
        ar'[p]? = k.arena[p]? := fun p _ _ => by
      rcases (Nat.lt_or_gt_of_ne hne) with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr href hlt
        exact hout p (Or.inl (by omega))
      · have := fullArenaScanRefs_disjoint href hr hgt
        exact hout p (Or.inr (by omega))
    have hgb : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
      rw [hout_r r (by omega) (by omega)]
    have hsz : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
      unfold fullArenaClauseSizeCore; dsimp only [k']
      rw [hout_r (r + 2) (by omega) (by omega)]
    have hlits := fullArenaClauseLitsCore_eq_of_hold hr_bd
      (by rw [har', ← hlen.arena_len_arr]; exact hr_bd) hsz
      fun j hj => hout_r (r + 3 + j) (by omega) (by omega)
    exact ⟨hgb, hsz, hlits⟩
  have hgarb_c : fullArenaClauseGarbCore k' cref = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    rw [hout cref (Or.inl (by omega))]; exact hg
  have hsz_c : fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref := by
    unfold fullArenaClauseSizeCore; dsimp only [k']
    rw [hout (cref + 2) (Or.inl (by omega))]
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [k'] at hnxt ⊢; rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hsz_c]; exact hwf
      · rw [(hoth_eq r hr hrc).2.1]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        have hsh0 : (fullArenaHdrCore k cref &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [k'] at hsh
          rwa [hout cref (Or.inl (by omega))] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term cref hr hsh0
        refine ⟨t, by rw [hsz_c]; exact ht1, ht2, ?_⟩
        dsimp only [k']; rw [hout t (Or.inr (by omega))]; exact hsent
      · have hr_wf := hw.arena.refs_wf r hr
        have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [k'] at hsh
          rcases (Nat.lt_or_gt_of_ne hrc) with hlt | hgt
          · have := fullArenaScanRefs_disjoint hr href hlt
            rwa [hout r (Or.inl (by omega))] at hsh
          · have := fullArenaScanRefs_disjoint href hr hgt
            rwa [hout r (Or.inr (by omega))] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        have hr_len : r < k.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
          unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hr_len, Option.getD_some]
        have hsh_ar : (k.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
          rw [hget_r, Option.getD_some]; exact hsh0
        obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel hr_wf.1 hsh_ar ht1 ht2 hsent
        have hkal : k'.arena_len = k.arena_len := rfl
        refine ⟨t0, by rw [(hoth_eq r hr hrc).2.1]; exact ht0_lo, by omega, ?_⟩
        dsimp only [k']
        rcases (Nat.lt_or_gt_of_ne hrc) with hlt | hgt
        · have := fullArenaScanRefs_disjoint hr href hlt
          rw [hout t0 (Or.inl (by omega))]; exact ht0_sent
        · have := fullArenaScanRefs_disjoint href hr hgt
          rw [hout t0 (Or.inr (by omega))]; exact ht0_sent
    · intro r hr hngr l hl; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        have hbd' : cref + 3 + fullArenaClauseSizeCore k' cref ≤ k'.arena.length := by
          rw [hsz_c]; dsimp only [k']; rw [har', ← hlen.arena_len_arr]; exact hbd
        obtain ⟨j, hj, hjl⟩ := (mem_fullArenaClauseLitsCore_iff hbd').mp hl
        rw [hsz_c] at hj; have hlt := hlits_lt j hj
        have hjbd : cref + 3 + j < ar'.length := by rw [har', ← hlen.arena_len_arr]; omega
        rw [List.getElem?_eq_getElem hjbd, Option.getD_some] at hlt
        exact hjl ▸ hlt
      · obtain ⟨hgb, _, hlits⟩ := hoth_eq r hr hrc
        exact hw.arena.lits_lt r hr (hgb ▸ hngr) l (hlits ▸ hl)
    · intro r hr hngr; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hent
      · obtain ⟨hgb, _, hlits⟩ := hoth_eq r hr hrc
        rw [hlits]; exact hw.arena.entails r hr (hgb ▸ hngr)
  refine ⟨{ hlen with arena_len_arr := har' },
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        dsimp only [k'] at hrs ⊢
        by_cases hbin : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
            0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
        · rw [ite_eq_right hbin] at hrs ⊢
          let r := (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
          by_cases hrc : r = cref
          · exact False.elim (hnonact idx hidx hne (Classical.not_not.mp hbin) hrc)
          · obtain ⟨hg_r, _, hl_r⟩ := hoth_eq r hrs.1 hrc
            exact ⟨hrefs ▸ hrs.1, hg_r.trans hrs.2.1, fun q hq => hrs.2.2 q (hl_r ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrs := hw.reason_inv idx hidx hne
        have hbf : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
            0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
        rw [ite_eq_right hbf] at hrs
        let r := (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
        by_cases hrc : r = cref
        · exact False.elim (hnonact idx hidx hne hlg hrc)
        · dsimp only [k']; rw [(hoth_eq r hrs.1 hrc).2.2]
          exact hw.reason_lit_mem idx hidx hne hlg },
    hrefs, hnxt⟩

/-! ## 2. Shared State & Unwatch / Garbage Helpers -/

theorem fullSparseInvW_of_unwatch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen' : FullState.LengthsOk c
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } })
    (hmw' : ModeWatchesInv F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wu' }) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
  let hw := hsp.2.1
  ⟨hlen',
   { hw with
     arena := ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term,
       hw.arena.lits_lt, hw.arena.entails⟩
     watches := hmw' },
   hsp.2.2⟩

theorem fullSparseInvW_with_counts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (ni' nr' vc' : BitVec 64) :
    let s' := { s with
      core := { s.core with num_irred := ni', num_redundant := nr' }
      scratch := { s.scratch with viv_cnt := vc' } }
    FullSparseInvW c F0 F_cur s' ∧ VivArenaEq s s' := by
  intro s'
  let hw := hsp.2.1
  refine ⟨⟨⟨{ hsp.1.core_ok with }, { hsp.1.scratch_ok with }⟩,
    { hw with
      arena := ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term,
        hw.arena.lits_lt, hw.arena.entails⟩
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ h => h },
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩, rfl, fun _ _ => rfl⟩

private theorem viv_testBit_lt_pow {x k i : Nat} (hx : x < 2 ^ k) (hki : k ≤ i) :
    x.testBit i = false := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hki
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hx hpow)]
  rfl

private theorem viv_set_glue_mask {hdr ng mask : BitVec 32} (hng : ng.toNat < 2 ^ 19)
    (hm : (mask &&& 0x7FFFF#32) = 0#32) :
    (((hdr &&& ~~~0x7FFFF#32) ||| ng) &&& mask) = (hdr &&& mask) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  have hm_eq := congrArg (fun x : BitVec 32 => x[i]) hm
  simp only [BitVec.getElem_and, BitVec.getElem_zero] at hm_eq
  by_cases h19 : i < 19
  · have h_all : ∀ k : Fin 19, (0x7FFFF#32 : BitVec 32).toNat.testBit k.1 = true := by decide
    have hb : (0x7FFFF#32 : BitVec 32)[i] = true := by
      rw [BitVec.getElem_eq_testBit_toNat]; exact h_all ⟨i, h19⟩
    simp [hb] at hm_eq
    simp [hm_eq]
  · have hng_f : ng[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]; exact viv_testBit_lt_pow hng (by omega)
    have h07_f : (0x7FFFF#32 : BitVec 32)[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      exact viv_testBit_lt_pow (k := 19) (by decide) (by omega)
    simp [hng_f, h07_f]

private theorem viv_garb_or_bit_red {hdr : BitVec 32} :
    ((hdr ||| 0x80000#32) &&& 0x400000#32) = (hdr &&& 0x400000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have hbc : ((0x80000#32 : BitVec 32).toNat.testBit i &&
      (0x400000#32 : BitVec 32).toNat.testBit i) = false := by
    have h_all : ∀ k : Fin 32, ((0x80000#32 : BitVec 32).toNat.testBit k.1 &&
        (0x400000#32 : BitVec 32).toNat.testBit k.1) = false := by decide
    exact h_all ⟨i, hi⟩
  simp only [BitVec.getElem_eq_testBit_toNat]
  by_cases hc : (0x400000#32 : BitVec 32).toNat.testBit i <;> simp_all

private theorem simplify_compact_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s2 : FullState} (hlen2 : s2.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s2.core)
    (hcl0 : s2.core.cur_level = 0) {cref old_sz nsz : Nat}
    (href : cref ∈ fullArenaClauseRefs s2) (hg : fullArenaClauseGarb s2 cref = false)
    (hsz : fullArenaClauseSize s2 cref = old_sz) {idxs : List Nat} (hlen : idxs.length = nsz)
    (hq : ∀ q ∈ idxs, q < old_sz) {ar : List (BitVec 32)} (_har_len : ar.length = c.arena_cap)
    (hmap : ∀ t < nsz, ar[cref + 3 + t]? = s2.core.arena[cref + 3 + idxs[t]?.getD 0]?)
    (hdrop : ∀ j < old_sz, j ∈ idxs ∨
      ((s2.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
        s2.core.vals[(s2.core.arena[cref + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 255#8)) :
    (∀ t < nsz, (ar[cref + 3 + t]?.getD 0#32).toNat < 2 * s2.core.cur_vars) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz).map fun t => (ar[cref + 3 + t]?.getD 0#32).toNat)) ∧
    (nsz = 0 → (cnfOfClauses F_cur).Unsat ∧ F0.Unsat) := by
  have hwf := hw.arena.refs_wf cref href
  have hsz_c : fullArenaClauseSizeCore s2.core cref = old_sz := hsz
  have hbd : cref + 3 + old_sz ≤ s2.core.arena.length := by
    have := hlen2.core_ok.arena_len_arr; have := hlen2.core_ok.arena_len_le
    rw [hsz_c] at hwf; omega
  have hlits_lt : ∀ t < nsz, (ar[cref + 3 + t]?.getD 0#32).toNat < 2 * s2.core.cur_vars := by
    intro t ht
    have hqt : t < idxs.length := by omega
    have hq_mem : idxs[t]?.getD 0 ∈ idxs := by
      rw [List.getElem?_eq_getElem hqt, Option.getD_some]; exact List.getElem_mem hqt
    have hj_lt : idxs[t]?.getD 0 < old_sz := hq _ hq_mem
    have hmem_l : (s2.core.arena[cref + 3 + idxs[t]?.getD 0]?.getD 0#32).toNat ∈
        fullArenaClauseLitsCore s2.core cref := by
      refine (mem_fullArenaClauseLitsCore_iff (by rw [hsz_c]; exact hbd)).mpr
        ⟨idxs[t]?.getD 0, by rw [hsz_c]; exact hj_lt, ?_⟩
      have hjb : cref + 3 + idxs[t]?.getD 0 < s2.core.arena.length := by omega
      rw [List.getElem?_eq_getElem hjb, Option.getD_some]
    rw [hmap t ht]
    exact hw.arena.lits_lt cref href hg _ hmem_l
  have hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz).map fun t => (ar[cref + 3 + t]?.getD 0#32).toNat)) := by
    refine entails_filter_level0 hw hcl0 (hw.arena.entails cref href hg) fun l hl => ?_
    obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff (by rw [hsz_c]; exact hbd)).mp hl
    rw [hsz_c] at hj
    have hjb : cref + 3 + j < s2.core.arena.length := by omega
    rcases hdrop j hj with hmem_i | hd
    · left
      obtain ⟨t, ht, hti⟩ := List.mem_iff_getElem.mp hmem_i
      have ht' : t < nsz := by omega
      refine List.mem_map.mpr ⟨t, List.mem_range.mpr ht', ?_⟩
      have hmap_t := congrArg (fun x : Option (BitVec 32) => (x.getD 0#32).toNat) (hmap t ht')
      rw [List.getElem?_eq_getElem ht, Option.getD_some, hti,
        List.getElem?_eq_getElem hjb, Option.getD_some] at hmap_t
      exact hmap_t
    · right
      rw [List.getElem?_eq_getElem hjb, Option.getD_some] at hd
      exact hd
  refine ⟨hlits_lt, hent, fun h0 => ?_⟩
  subst h0
  simp only [List.range_zero, List.map_nil] at hent
  have hu : (cnfOfClauses F_cur).Unsat := unsat_of_entails_nil hent
  exact ⟨hu, hw.ext_sound.2 hu⟩

/-! ## 3. `full_viv_simplify_m6_wp` -/

private theorem bv8_sgt0_iff_eq1 {x : BitVec 8}
    (hx : x = 0#8 ∨ x = 1#8 ∨ x = 255#8) : BitVec.slt 0#8 x ↔ x = 1#8 := by
  rcases hx with rfl | rfl | rfl <;> decide

theorem simplify_garb_of_compacted {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s2 s_b : FullState} (hsp2 : FullSparseInvW c F0 F_cur s2)
    (hlen_b : s_b.LengthsOk c) (hw_b : FullWitnessInv c F0 F_cur s_b.core)
    (hcl_b0 : s_b.core.cur_level = 0)
    (hlm_b : FullLitMarksClear c s_b) (hxs_b : FullExtScratchOk c s_b)
    (hdm_b : s_b.core.dense_mode = 0#64) (hal_eq : s_b.core.arena_len = s2.core.arena_len)
    {cref old_sz nsz : Nat}
    (href2 : cref ∈ fullArenaClauseRefs s2) (href_b : cref ∈ fullArenaClauseRefs s_b)
    (hsz2 : fullArenaClauseSize s2 cref = old_sz)
    (hout_b : ∀ p, (p < cref + 3 ∨ cref + 3 + nsz ≤ p) →
      s_b.core.arena[p]? = s2.core.arena[p]?)
    (hnsz_le : nsz ≤ old_sz)
    (ag' ni' nr' vc' : BitVec 64) :
    let ar_g := s_b.core.arena.set cref (fullArenaHdr s_b cref ||| 0x80000#32)
    let s_g : FullState := {
      core := { s_b.core with
        arena := ar_g, arena_garbage := ag', num_irred := ni', num_redundant := nr' }
      scratch := { s_b.scratch with viv_cnt := vc' } }
    FullSparseInvW c F0 F_cur s_g ∧
    fullArenaClauseRefs s_g = fullArenaClauseRefs s_b := by
  intro ar_g s_g
  have hmg := FullArenaClausesInv.markGarb hw_b.arena hlen_b.core_ok href_b ag'
  have hrefs_g_b : fullArenaClauseRefs s_g = fullArenaClauseRefs s_b := hmg.1
  have hrefs_g_c : fullArenaClauseRefsCore s_g.core = fullArenaClauseRefsCore s_b.core := hmg.1
  have hnonact_b : NonActiveReason s_b.core cref := nonActiveReason_of_level0 hw_b hcl_b0 cref
  have hwf_b := hw_b.arena.refs_wf cref href_b
  have hwf2 := hsp2.2.1.arena.refs_wf cref href2
  have hbd_b : cref + 3 ≤ s_b.core.arena.length := by
    have := hlen_b.core_ok.arena_len_arr; have := hlen_b.core_ok.arena_len_le; omega
  have hcref_lt : cref < s_b.core.arena.length := by omega
  have ha_g_cref : ar_g[cref]? = some (fullArenaHdrCore s_b.core cref ||| 0x80000#32) :=
    List.getElem?_set_self hcref_lt
  have hgarb_g_true : fullArenaClauseGarb s_g cref = true := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    dsimp only [s_g]; rw [ha_g_cref, Option.getD_some]
    exact bne_iff_ne.mpr fun heq => by
      have h19 := congrArg (fun x : BitVec 32 => x[19]) heq
      revert h19; simp [BitVec.getElem_and, BitVec.getElem_or]
  have hsz2_c : fullArenaClauseSizeCore s2.core cref = old_sz := hsz2
  have hdisj_b : ∀ r ∈ fullArenaClauseRefsCore s_b.core, r ≠ cref →
      r + 3 + fullArenaClauseSizeCore s_b.core r ≤ cref ∨
        cref + 3 + fullArenaClauseSizeCore s_b.core cref ≤ r := by
    intro r hr hne
    have hwf_r := hw_b.arena.refs_wf r hr
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · left; have := fullArenaScanRefs_disjoint hr href_b hlt; omega
    · right; have := fullArenaScanRefs_disjoint href_b hr hgt; omega
  have hoth_g : ∀ r ∈ fullArenaClauseRefsCore s_b.core, r ≠ cref →
      fullArenaClauseGarbCore s_g.core r = fullArenaClauseGarbCore s_b.core r ∧
      fullArenaClauseLitsCore s_g.core r = fullArenaClauseLitsCore s_b.core r := by
    intro r hr hne
    have hlen_arr_b := hlen_b.core_ok.arena_len_arr
    have hlen_le_b := hlen_b.core_ok.arena_len_le
    have hr_bd : r + 3 + fullArenaClauseSizeCore s_b.core r ≤ s_b.core.arena.length := by
      have := (hw_b.arena.refs_wf r hr).2.2.1; have := (hw_b.arena.refs_wf r hr).2.2.2; omega
    have hout_r : r + 3 + fullArenaClauseSizeCore s_b.core r ≤ cref ∨ cref + 3 ≤ r := by
      rcases hdisj_b r hr hne with h1 | h2 <;> omega
    have h1 := fullArenaClauseLitsCore_set_outside (v := fullArenaHdr s_b cref ||| 0x80000#32)
      hr_bd hout_r
    have hgb : fullArenaClauseGarbCore s_g.core r = fullArenaClauseGarbCore s_b.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s_g]
      rw [List.getElem?_set_ne (Ne.symm hne)]
    exact ⟨hgb, h1.2⟩
  have hoth_2b : ∀ r ∈ fullArenaClauseRefsCore s2.core, r ≠ cref →
      fullArenaClauseGarbCore s_b.core r = fullArenaClauseGarbCore s2.core r ∧
      fullArenaClauseLitsCore s_b.core r = fullArenaClauseLitsCore s2.core r := by
    intro r hr hne
    have hwf_r := hsp2.2.1.arena.refs_wf r hr
    have hlen_arr2 := hsp2.1.core_ok.arena_len_arr
    have hlen_le2 := hsp2.1.core_ok.arena_len_le
    have hlen_arr_b := hlen_b.core_ok.arena_len_arr
    have hr_bd : r + 3 + fullArenaClauseSizeCore s2.core r ≤ s2.core.arena.length := by omega
    have hr2eq : s_b.core.arena[r + 2]? = s2.core.arena[r + 2]? := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr href2 hlt
        exact hout_b (r + 2) (Or.inl (by omega))
      · have := fullArenaScanRefs_disjoint href2 hr hgt
        exact hout_b (r + 2) (Or.inr (by rw [hsz2_c] at hwf2; omega))
    have hszr : fullArenaClauseSizeCore s_b.core r = fullArenaClauseSizeCore s2.core r := by
      unfold fullArenaClauseSizeCore; rw [hr2eq]
    have hr_bd_b : r + 3 + fullArenaClauseSizeCore s_b.core r ≤ s_b.core.arena.length := by omega
    have hout_r : ∀ p, r ≤ p → p < r + 3 + fullArenaClauseSizeCore s2.core r →
        s_b.core.arena[p]? = s2.core.arena[p]? := fun p _ _ => by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr href2 hlt
        exact hout_b p (Or.inl (by omega))
      · have := fullArenaScanRefs_disjoint href2 hr hgt
        exact hout_b p (Or.inr (by rw [hsz2_c] at hwf2; omega))
    have hgb : fullArenaClauseGarbCore s_b.core r = fullArenaClauseGarbCore s2.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore
      rw [hout_r r (by omega) (by omega)]
    have hlt_eq : fullArenaClauseLitsCore s_b.core r = fullArenaClauseLitsCore s2.core r :=
      fullArenaClauseLitsCore_eq_of_hold hr_bd (by rw [← hszr]; exact hr_bd_b)
        hszr fun j hj => hout_r (r + 3 + j) (by omega) (by omega)
    exact ⟨hgb, hlt_eq⟩
  have hrefs2_b : fullArenaClauseRefs s_b = fullArenaClauseRefs s2 := by
    refine fullArenaClauseRefsCore_congr hal_eq fun r hr => ?_
    have hwf_r := hsp2.2.1.arena.refs_wf r hr
    by_cases hrc : r = cref
    · subst r
      have h0eq := hout_b cref (Or.inl (by omega))
      have h2eq := hout_b (cref + 2) (Or.inl (by omega))
      have h1 : ¬ (cref + 3 > s2.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s2.core.arena[cref + 2]?.getD 0#32).toNat > s2.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf2; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, h0eq]
      split
      · refine fullArenaSkipShrk_congr fun p hp1 _ => hout_b p (Or.inr (by
          unfold fullArenaClauseSizeCore at hsz2_c; omega))
      · rfl
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr href2 hlt
        exact fullArenaNextOff_congr_block (hout_b r (Or.inl (by omega)))
          (hout_b (r + 2) (Or.inl (by omega))) fun p _ _ => hout_b p (Or.inl (by omega))
      · have := fullArenaScanRefs_disjoint href2 hr hgt
        exact fullArenaNextOff_congr_block (hout_b r (Or.inr (by rw [hsz2_c] at hwf2; omega)))
          (hout_b (r + 2) (Or.inr (by rw [hsz2_c] at hwf2; omega)))
          fun p _ _ => hout_b p (Or.inr (by rw [hsz2_c] at hwf2; omega))
  have hlen_g : s_g.LengthsOk c :=
    ⟨{ hlen_b.core_ok with arena_len_arr := by simp [s_g, ar_g, hlen_b.core_ok.arena_len_arr] },
     { hlen_b.scratch_ok with }⟩
  have har_g_c : FullArenaClausesInv c F_cur s_g.core :=
    ⟨hmg.2.len_ok, hmg.2.refs_wf, hmg.2.shrk_term, hmg.2.lits_lt, hmg.2.entails⟩
  have hw_g : FullWitnessInv c F0 F_cur s_g.core :=
    { hw_b with
      arena := har_g_c
      watches := hw_b.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hrefs_g_c ▸ hr
      reason_inv := fun idx hidx hne => by
        have hrs := hw_b.reason_inv idx hidx hne
        dsimp only [s_g] at hrs ⊢
        by_cases hbin : (s_b.core.rsns[(s_b.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
        · rw [ite_eq_right hbin] at hrs ⊢
          let r :=
            (s_b.core.rsns[(s_b.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
          by_cases hrc : r = cref
          · exact False.elim (hnonact_b idx hidx hne (Classical.not_not.mp hbin) hrc)
          · obtain ⟨hgb, hl⟩ := hoth_g r hrs.1 hrc
            exact ⟨hrefs_g_c ▸ hrs.1, hgb.trans hrs.2.1, fun q hq => hrs.2.2 q (hl ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrs := hw_b.reason_inv idx hidx hne
        have hbf : ¬ (s_b.core.rsns[(s_b.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
        rw [ite_eq_right hbf] at hrs
        let r := (s_b.core.rsns[(s_b.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
        by_cases hrc : r = cref
        · exact False.elim (hnonact_b idx hidx hne hlg hrc)
        · rw [(hoth_g r hrs.1 hrc).2]
          exact hw_b.reason_lit_mem idx hidx hne hlg }
  have hav_g : FullArenaVarsNodup s_g := fun r hr hngr => by
    rw [hrefs_g_b] at hr
    by_cases hrc : r = cref
    · subst r; simp [hgarb_g_true] at hngr
    · obtain ⟨hgb, hl⟩ := hoth_g r hr hrc
      have hr2 : r ∈ fullArenaClauseRefs s2 := hrefs2_b ▸ hr
      obtain ⟨hgb2, hl2⟩ := hoth_2b r hr2 hrc
      rw [show fullArenaClauseLits s_g r = fullArenaClauseLitsCore s_g.core r from rfl, hl, hl2]
      exact hsp2.2.2.2.1 r hr2 (hgb2.symm.trans (hgb.symm.trans hngr))
  have hxs_g : FullExtScratchOk c s_g := by
    refine ⟨fun i hi => ?_, hxs_b.2⟩
    have hll := hxs_b.1 i hi
    rcases hll with heq | hm
    · exact Or.inl heq
    · exact Or.inr (hrefs_g_b ▸ hm)
  exact ⟨⟨hlen_g, hw_g, hlm_b, hav_g, hxs_g, hdm_b⟩, hrefs_g_b⟩

theorem viv_unwatch_one_wp (Γ : Env)
    (hUnwatch : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {lit cref : BitVec 32}
    {rs : List Ty} {k : Tup Val [] → Expr Val Cont rs} {Q : Post rs} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ wvec' wstk' wu' m',
      let s' := { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
      FullSparseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
      (Arg.var c.hdr, Arg.var lit, Arg.var cref, ()) k) m := by
  refine wp_call_of_spec _ _ (hUnwatch _ _ _ _
    ⟨c, s, R, rfl, hsp.1, hsp.2.1.watches.layout, hm,
      fun wvec' wstk' wu' m' hlen' _ hmw' hm' => ?_⟩)
  exact hk wvec' wstk' wu' m' (fullSparseInvW_of_unwatch hsp hlen' (hmw' F_cur hsp.2.1.watches)) hm'

private theorem simplify_nsz1_prep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s2 : FullState} {cref sz : Nat}
    {ar_c : List (BitVec 32)} {idxs : List Nat}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hcl2 : s2.core.cur_level = 0)
    (href2 : cref ∈ fullArenaClauseRefs s2) (hg2 : fullArenaClauseGarb s2 cref = false)
    (hsz2 : fullArenaClauseSizeCore s2.core cref = sz) (hsz_ge3 : 3 ≤ sz)
    (hbd2 : cref + 3 + fullArenaClauseSizeCore s2.core cref ≤ s2.core.arena.length)
    (harc_len : ar_c.length = c.arena_cap) (hlen_i : idxs.length = 1)
    (hq_i : ∀ q ∈ idxs, q < sz)
    (hout_i : ∀ p, (p < cref + 3 ∨ cref + 3 + 1 ≤ p) → ar_c[p]? = s2.core.arena[p]?)
    (hmap_i : ∀ t < 1, ar_c[cref + 3 + t]? = s2.core.arena[cref + 3 + idxs[t]?.getD 0]?)
    (hdrop_i : ∀ j < sz, j ∈ idxs ∨
      ((s2.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
        s2.core.vals[(s2.core.arena[cref + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 255#8))
    (ag' ni' nr' : BitVec 64) :
    let ar_g := ar_c.set cref (fullArenaHdr s2 cref ||| 0x80000#32)
    let s_g : FullState := { s2 with core := { s2.core with
      arena := ar_g, arena_garbage := ag', num_irred := ni', num_redundant := nr' } }
    FullSparseInvW c F0 F_cur s_g ∧ fullArenaClauseRefs s_g = fullArenaClauseRefs s2 ∧
    (ar_g[cref + 3]?.getD 0#32).toNat < 2 * s_g.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(ar_g[cref + 3]?.getD 0#32).toNat]) := by
  intro ar_g s_g
  have hcl2_ok := hsp2.1.core_ok
  have hw2 := hsp2.2.1
  have hna := nonActiveReason_of_level0 hw2 hcl2 cref
  have hj0 : ∃ j0, idxs = [j0] := by
    cases idxs with
    | nil => simp at hlen_i
    | cons a t =>
      cases t with
      | nil => exact ⟨a, rfl⟩
      | cons _ _ => simp at hlen_i
  obtain ⟨j0, rfl⟩ := hj0
  have hj0_lt : j0 < sz := hq_i j0 (by simp)
  have hlit_0 := hmap_i 0 (by decide)
  have hbd_j0 : cref + 3 + j0 < s2.core.arena.length := by omega
  have hmem_0 : (s2.core.arena[cref + 3 + j0]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s2.core cref :=
    (mem_fullArenaClauseLitsCore_iff hbd2).mpr ⟨j0, hsz2.symm ▸ hj0_lt,
      by rw [List.getElem?_eq_getElem hbd_j0, Option.getD_some]⟩
  have hl0_lt : (s2.core.arena[cref + 3 + j0]?.getD 0#32).toNat < 2 * s2.core.cur_vars :=
    hw2.arena.lits_lt cref href2 hg2 _ hmem_0
  have hent_0 := simplify_lits_entails_of_idxs hw2 hcl2 href2 hg2 hsz2 hbd2 hdrop_i
  simp only [List.map_cons, List.map_nil] at hent_0
  have harc_c3_lt : cref + 3 < ar_c.length := by rw [harc_len, ← hcl2_ok.arena_len_arr]; omega
  have hl0_eq : ar_c[cref + 3]?.getD 0#32 = s2.core.arena[cref + 3 + j0]?.getD 0#32 := by
    simpa using congrArg (Option.getD · 0#32) hlit_0
  have harg_c3 : ar_g[cref + 3]?.getD 0#32 = s2.core.arena[cref + 3 + j0]?.getD 0#32 := by
    dsimp only [ar_g]; rw [List.getElem?_set_ne (by omega)]; exact hl0_eq
  have hres := fullArena_updateLits_preserves_fullWitness_hnonact (nsz := 1) hcl2_ok hw2
    href2 hg2 hna harc_len (by rw [hsz2]; omega)
    (fun p hp => hout_i p hp)
    (fun j hj => by
      by_cases hjz : j = 0
      · subst hjz; rw [hl0_eq]; exact hl0_lt
      · have hbd_j : cref + 3 + j < s2.core.arena.length := by omega
        rw [hout_i (cref + 3 + j) (Or.inr (by omega))]
        exact hw2.arena.lits_lt cref href2 hg2 _
          ((mem_fullArenaClauseLitsCore_iff hbd2).mpr ⟨j, hj,
            by rw [List.getElem?_eq_getElem hbd_j, Option.getD_some]⟩))
    (by
      have hbd_c : cref + 3 + fullArenaClauseSizeCore { s2.core with arena := ar_c } cref ≤
          ar_c.length := by
        unfold fullArenaClauseSizeCore
        rw [hout_i (cref + 2) (Or.inl (by omega)), harc_len, ← hcl2_ok.arena_len_arr]
        exact hbd2
      have hsz_c : fullArenaClauseSizeCore { s2.core with arena := ar_c } cref = sz := by
        unfold fullArenaClauseSizeCore; rw [hout_i (cref + 2) (Or.inl (by omega))]; exact hsz2
      have hmem_c0 : (ar_c[cref + 3]?.getD 0#32).toNat ∈
          fullArenaClauseLitsCore { s2.core with arena := ar_c } cref :=
        (mem_fullArenaClauseLitsCore_iff hbd_c).mpr ⟨0, by rw [hsz_c]; omega, by
          rw [List.getElem?_eq_getElem harc_c3_lt, Option.getD_some]⟩
      rw [CNF.entails_clause_def] at hent_0 ⊢
      intro α hα
      obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hent_0 α hα)
      simp only [List.mem_singleton] at hl; subst hl
      exact (clause_sat_cnfClause_iff α _).mpr ⟨_, by rw [← hl0_eq]; exact hmem_c0, hsat⟩)
  dsimp only at hres
  have hw_c : FullWitnessInv c F0 F_cur { s2.core with arena := ar_c } := hres.2.1
  let s_c : FullState := { s2 with core := { s2.core with arena := ar_c } }
  have hlen_c : s_c.LengthsOk c := ⟨hres.1, hsp2.1.scratch_ok⟩
  have href_c : cref ∈ fullArenaClauseRefs s_c := by
    change cref ∈ fullArenaClauseRefsCore s_c.core
    rw [show fullArenaClauseRefsCore s_c.core = fullArenaClauseRefsCore s2.core from hres.2.2.1]
    exact href2
  have hxs_c : FullExtScratchOk c s_c := FullExtScratchOk.of_pres hsp2.2.2.2.2.1 ⟨rfl, rfl⟩
    fun r hr => by
      change r ∈ fullArenaClauseRefsCore s_c.core
      rw [show fullArenaClauseRefsCore s_c.core = fullArenaClauseRefsCore s2.core from hres.2.2.1]
      exact hr
  have hsz2' : fullArenaClauseSize s2 cref = sz := hsz2
  have hsp_g := simplify_garb_of_compacted hsp2 hlen_c hw_c hcl2 hsp2.2.2.1 hxs_c
    hsp2.2.2.2.2.2 rfl href2 href_c hsz2'
    (fun p hp => hout_i p (by rcases hp with h | h; exact Or.inl h; exact Or.inr (by omega)))
    (by omega) ag' ni' nr' s2.scratch.viv_cnt
  have har_g_eq : s_c.core.arena.set cref (fullArenaHdr s_c cref ||| 0x80000#32) = ar_g := by
    simp [ar_g, s_c, fullArenaHdr, fullArenaHdrCore, hout_i cref (Or.inl (by omega))]
  have hscr_eq : ({ s_c.scratch with viv_cnt := s2.scratch.viv_cnt } : FullScratch) =
      s2.scratch := rfl
  have hrefs_cb : fullArenaClauseRefs s_c = fullArenaClauseRefs s2 := hres.2.2.1
  have hsp_g1 : FullSparseInvW c F0 F_cur s_g := by
    simpa [s_g, har_g_eq, hscr_eq] using hsp_g.1
  have hrefs_g1 : fullArenaClauseRefs s_g = fullArenaClauseRefs s2 := by
    simpa [s_g, har_g_eq, hscr_eq] using hsp_g.2.trans hrefs_cb
  refine ⟨hsp_g1, hrefs_g1, ?_, ?_⟩
  · change (ar_g[cref + 3]?.getD 0#32).toNat < 2 * s2.core.cur_vars
    rw [harg_c3]; exact hl0_lt
  · rw [harg_c3]; exact hent_0

private theorem simplify_nsz2_prep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s2 : FullState} {cref sz : Nat}
    {ar_c : List (BitVec 32)} {idxs : List Nat}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hcl2 : s2.core.cur_level = 0)
    (href2 : cref ∈ fullArenaClauseRefs s2) (hg2 : fullArenaClauseGarb s2 cref = false)
    (hsz2 : fullArenaClauseSizeCore s2.core cref = sz) (hsz_ge3 : 3 ≤ sz)
    (hbd2 : cref + 3 + fullArenaClauseSizeCore s2.core cref ≤ s2.core.arena.length)
    (harc_len : ar_c.length = c.arena_cap) (hlen_i : idxs.length = 2)
    (hq_i : ∀ q ∈ idxs, q < sz)
    (hout_i : ∀ p, (p < cref + 3 ∨ cref + 3 + 2 ≤ p) → ar_c[p]? = s2.core.arena[p]?)
    (hmap_i : ∀ t < 2, ar_c[cref + 3 + t]? = s2.core.arena[cref + 3 + idxs[t]?.getD 0]?)
    (hdrop_i : ∀ j < sz, j ∈ idxs ∨
      ((s2.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
        s2.core.vals[(s2.core.arena[cref + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 255#8)) :
    let s_c : FullState := { s2 with core := { s2.core with arena := ar_c } }
    FullWitnessInv c F0 F_cur s_c.core ∧ fullArenaClauseRefs s_c = fullArenaClauseRefs s2 ∧
    (ar_c[cref + 3]?.getD 0#32).toNat < 2 * s_c.core.cur_vars ∧
    (ar_c[cref + 4]?.getD 0#32).toNat < 2 * s_c.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(ar_c[cref + 3]?.getD 0#32).toNat, (ar_c[cref + 4]?.getD 0#32).toNat]) := by
  intro s_c
  have hcl2_ok := hsp2.1.core_ok
  have hw2 := hsp2.2.1
  have hna := nonActiveReason_of_level0 hw2 hcl2 cref
  have hj01 : ∃ j0 j1, idxs = [j0, j1] := by
    cases idxs with
    | nil => simp at hlen_i
    | cons a t =>
      cases t with
      | nil => simp at hlen_i
      | cons b t2 =>
        cases t2 with
        | nil => exact ⟨a, b, rfl⟩
        | cons _ _ => simp at hlen_i
  obtain ⟨j0, j1, rfl⟩ := hj01
  have hj0_lt : j0 < sz := hq_i j0 (by simp)
  have hj1_lt : j1 < sz := hq_i j1 (by simp)
  have hl0_eq : ar_c[cref + 3]?.getD 0#32 = s2.core.arena[cref + 3 + j0]?.getD 0#32 := by
    simpa using congrArg (Option.getD · 0#32) (hmap_i 0 (by decide))
  have hl1_eq : ar_c[cref + 4]?.getD 0#32 = s2.core.arena[cref + 3 + j1]?.getD 0#32 := by
    simpa [Nat.add_assoc] using congrArg (Option.getD · 0#32) (hmap_i 1 (by decide))
  have hl0_lt : (ar_c[cref + 3]?.getD 0#32).toNat < 2 * s2.core.cur_vars := by
    rw [hl0_eq]
    have hbd_j0 : cref + 3 + j0 < s2.core.arena.length := by omega
    exact hw2.arena.lits_lt cref href2 hg2 _
      ((mem_fullArenaClauseLitsCore_iff hbd2).mpr ⟨j0, hsz2.symm ▸ hj0_lt,
        by rw [List.getElem?_eq_getElem hbd_j0, Option.getD_some]⟩)
  have hl1_lt : (ar_c[cref + 4]?.getD 0#32).toNat < 2 * s2.core.cur_vars := by
    rw [hl1_eq]
    have hbd_j1 : cref + 3 + j1 < s2.core.arena.length := by omega
    exact hw2.arena.lits_lt cref href2 hg2 _
      ((mem_fullArenaClauseLitsCore_iff hbd2).mpr ⟨j1, hsz2.symm ▸ hj1_lt,
        by rw [List.getElem?_eq_getElem hbd_j1, Option.getD_some]⟩)
  have hent := simplify_lits_entails_of_idxs hw2 hcl2 href2 hg2 hsz2 hbd2 hdrop_i
  simp only [List.map_cons, List.map_nil] at hent
  rw [← hl0_eq, ← hl1_eq] at hent
  have harc_c3_lt : cref + 3 < ar_c.length := by rw [harc_len, ← hcl2_ok.arena_len_arr]; omega
  have harc_c4_lt : cref + 4 < ar_c.length := by rw [harc_len, ← hcl2_ok.arena_len_arr]; omega
  have hres := fullArena_updateLits_preserves_fullWitness_hnonact (nsz := 2) hcl2_ok hw2
    href2 hg2 hna harc_len (by rw [hsz2]; omega)
    (fun p hp => hout_i p hp)
    (fun j hj => by
      by_cases hj0 : j = 0
      · subst hj0; exact hl0_lt
      · by_cases hj1 : j = 1
        · subst hj1; exact hl1_lt
        · have hbd_j : cref + 3 + j < s2.core.arena.length := by omega
          rw [hout_i (cref + 3 + j) (Or.inr (by omega))]
          exact hw2.arena.lits_lt cref href2 hg2 _
            ((mem_fullArenaClauseLitsCore_iff hbd2).mpr ⟨j, hj,
              by rw [List.getElem?_eq_getElem hbd_j, Option.getD_some]⟩))
    (by
      have hbd_c : cref + 3 + fullArenaClauseSizeCore s_c.core cref ≤ ar_c.length := by
        unfold fullArenaClauseSizeCore s_c
        rw [hout_i (cref + 2) (Or.inl (by omega)), harc_len, ← hcl2_ok.arena_len_arr]
        exact hbd2
      have hsz_c : fullArenaClauseSizeCore s_c.core cref = sz := by
        unfold fullArenaClauseSizeCore s_c; rw [hout_i (cref + 2) (Or.inl (by omega))]; exact hsz2
      have hmem0 : (ar_c[cref + 3]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s_c.core cref :=
        (mem_fullArenaClauseLitsCore_iff hbd_c).mpr ⟨0, by rw [hsz_c]; omega, by
          rw [List.getElem?_eq_getElem harc_c3_lt, Option.getD_some]⟩
      have hmem1 : (ar_c[cref + 4]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s_c.core cref :=
        (mem_fullArenaClauseLitsCore_iff hbd_c).mpr ⟨1, by rw [hsz_c]; omega, by
          rw [List.getElem?_eq_getElem harc_c4_lt, Option.getD_some]⟩
      rw [CNF.entails_clause_def] at hent ⊢
      intro α hα
      obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hent α hα)
      simp only [List.mem_cons] at hl
      rcases hl with rfl | rfl | h_nil
      · exact (clause_sat_cnfClause_iff α _).mpr ⟨_, hmem0, hsat⟩
      · exact (clause_sat_cnfClause_iff α _).mpr ⟨_, hmem1, hsat⟩
      · cases h_nil)
  dsimp only [s_c] at hres ⊢
  exact ⟨hres.2.1, hres.2.2.1, hl0_lt, hl1_lt, hent⟩

abbrev simplifyNsz1Expr (c : FullCfg) (cref hdr_v old_sz : Val i32) :
    Expr Val Cont [i64] :=
  Expr.store (Arg.var (hdr_v ||| 524288))
    (Arg.var (c.pArena + BitVec.setWidth 64 cref * 4))
    (fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 472, ()) fun p =>
     Expr.load i64 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.add i64) (Arg.var ld, Arg.imm 3, ()) fun p =>
     fvOp (OpCode.zext 32 64) (Arg.var old_sz, ()) fun p2 =>
     fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var p2.fst, ()) fun p =>
     fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 472, ()) fun p3 =>
     Expr.store (Arg.var p.fst) (Arg.var p3.fst)
       (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
         Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
           Expr.ret (Arg.var p.fst, ())) Blocks.nil) fun Ju =>
         fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
         fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
         fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
         fvOp (OpCode.add i64) (Arg.var c.pArena, Arg.var p.fst, ()) fun p =>
         Expr.load i32 (Arg.var p.fst) fun ld =>
         Expr.call (as := [i64, i32]) (bs := [.bool]) "full_add_unit"
           (Arg.var c.hdr, Arg.var ld, ()) fun p =>
         Expr.jnz (Arg.var p.fst) (Expr.jump Ju.fst (Arg.imm 1, ()))
           (Expr.jump Ju.fst (Arg.imm 20, ()))) Blocks.nil) fun Js =>
        simplifyDecrExpr c.hdr hdr_v Js.fst))

private theorem simplify_nsz1_wp (Γ : Env)
    (hUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 s2 : FullState}
    {R : Mem 64 → Prop} {cref old_sz hdr_v : Val i32}
    {ar_c : List (BitVec 32)} {idxs : List Nat}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hcl2 : s2.core.cur_level = 0)
    (hs2_ar : s2.core.arena = s0.core.arena) (hs2_cv : s2.core.cur_vars = s0.core.cur_vars)
    (hs2_al : s2.core.arena_len = s0.core.arena_len) (hs2_pr : s2.core.probing = s0.core.probing)
    (hs2_fu : s2.core.fuel = s0.core.fuel)
    (hs2_rr : s2.scratch.red_refs = s0.scratch.red_refs)
    (hs2_tr : s2.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s0)
    (href0 : cref.toNat ∈ fullArenaClauseRefs s0) (hg0 : fullArenaClauseGarb s0 cref.toNat = false)
    (hhdr_v : hdr_v = fullArenaHdr s2 cref.toNat)
    (hsz0 : fullArenaClauseSize s0 cref.toNat = old_sz.toNat) (hsz_ge3 : 3 ≤ old_sz.toNat)
    (hbd2 : cref.toNat + 3 + fullArenaClauseSizeCore s2.core cref.toNat ≤ s2.core.arena.length)
    (harc_len : ar_c.length = c.arena_cap) (hlen_i : idxs.length = 1)
    (hq_i : ∀ q ∈ idxs, q < old_sz.toNat)
    (hout_i : ∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + 1 ≤ p) →
      ar_c[p]? = s2.core.arena[p]?)
    (hmap_i : ∀ t < 1,
      ar_c[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs[t]?.getD 0]?)
    (hdrop_i : ∀ j < old_sz.toNat, j ∈ idxs ∨
      ((s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
        s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 255#8))
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar_c } } ⋆ R) m)
    (hQ : VivSimpQ c F0 F_cur s0 R Q cref.toNat) :
    wp Γ Q X (simplifyNsz1Expr c cref hdr_v old_sz) m := by
  subst hhdr_v
  have hcl2_ok := hsp2.1.core_ok
  have hsz2 : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := by
    unfold fullArenaClauseSizeCore; rw [hs2_ar]; exact hsz0
  have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := hrefs2.symm ▸ href0
  have hg2 : fullArenaClauseGarb s2 cref.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hs2_ar]; exact hg0
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hc0_idx : (BitVec.setWidth 64 cref).toNat = cref.toNat := by bv_omega
  have hc3_idx : (BitVec.setWidth 64 cref + 3#64).toNat = cref.toNat + 3 := by bv_omega
  have hcref_lt : cref.toNat < ar_c.length := by rw [harc_len, ← hcl2_ok.arena_len_arr]; omega
  have harc_c0_lt : (BitVec.setWidth 64 cref).toNat < ar_c.length := hc0_idx ▸ hcref_lt
  have hcref3_lt : cref.toNat + 3 < ar_c.length := by rw [harc_len, ← hcl2_ok.arena_len_arr]; omega
  dsimp only [simplifyNsz1Expr, fvOp]
  viv_to_group
  let ag' := s2.core.arena_garbage + 3#64 + BitVec.setWidth 64 old_sz
  let ar_g := ar_c.set cref.toNat (fullArenaHdr s2 cref.toNat ||| 0x80000#32)
  have hm_g0 : (FullMem c { s2 with core := { s2.core with
      arena := ar_g, arena_garbage := ag' } } ⋆ R) m := by
    have heq : ar_c.set (BitVec.setWidth 64 cref).toNat
        (fullArenaHdr s2 cref.toNat ||| 524288#32) = ar_g := by rw [hc0_idx]
    rw [← heq]; assumption
  refine wp_join0 (fun md => ∃ ni' nr',
      (FullMem c { s2 with core := { s2.core with
        arena := ar_g, arena_garbage := ag',
        num_irred := ni', num_redundant := nr' } } ⋆ R) md) ?_ ?_
  · rintro _ md ⟨ni', nr', hmd⟩
    obtain ⟨hsp_g, hrefs_g, hl0_lt, hl0_ent⟩ := simplify_nsz1_prep hsp2 hcl2 href2 hg2
      hsz2 hsz_ge3 hbd2 harc_len hlen_i hq_i hout_i hmap_i hdrop_i ag' ni' nr'
    have hrefs_g0 : fullArenaClauseRefs { s2 with core := { s2.core with
        arena := ar_g, arena_garbage := ag', num_irred := ni', num_redundant := nr' } } =
        fullArenaClauseRefs s0 := hrefs_g.trans hrefs2
    viv_to_group
    refine wp_join_group (ts := [i64]) (fun (rv, ()) mu => ∃ su,
      FullSparseInvW c F0 F_cur su ∧ su.core.cur_level = 0 ∧
      su.core.cur_vars = s0.core.cur_vars ∧ su.core.arena_len = s0.core.arena_len ∧
      su.core.probing = s0.core.probing ∧ su.core.fuel = s0.core.fuel ∧
      fullArenaClauseRefs su = fullArenaClauseRefs s0 ∧
      su.scratch.red_refs = s2.scratch.red_refs ∧
      su.scratch.tarjan_reach = s2.scratch.tarjan_reach ∧
      (rv = 1#64 ∨ rv = 20#64) ∧ (rv = 20#64 → F0.Unsat) ∧
      (FullMem c su ⋆ R) mu) ?_ ?_
    · rintro _ ⟨rv, ⟨⟩⟩ mu ⟨su, hspu, hclu, hcvu, halu, hpru, hfuu, hrefsu, hrru,
        htru, hrv, huns, hmu⟩
      viv_steps
      exact hQ rv su mu hspu hclu hcvu halu hpru hfuu hrefsu
        (hrru.trans hs2_rr) (htru.trans hs2_tr)
        (by rcases hrv with rfl | rfl <;> simp) huns
        (fun h => by subst h; cases hrv <;> cases ‹_›) hmu
    · intro Ju hJu
      have hc3_bv : (BitVec.setWidth 64 cref + 3).toNat = cref.toNat + 3 := by bv_omega
      have harg_c3 : (BitVec.setWidth 64 cref + 3).toNat < ar_g.length := by
        simp only [ar_g, List.length_set, hc3_bv]; exact hcref3_lt
      have hget_g : ar_g[cref.toNat + 3]?.getD 0#32 =
          ar_g[(BitVec.setWidth 64 cref + 3).toNat]'harg_c3 := by
        rw [← hc3_bv, List.getElem?_eq_getElem harg_c3, Option.getD_some]
      viv_steps
      viv_call hUnit
      refine ⟨c, F0, F_cur, _, R, rfl, hsp_g.1, hsp_g.2.1, fun _ => ?_, hmd,
        fun ok _ _ _ _ _ _ _ _ cl' _ _ _ _ _ _ _ _ _ _ _ _ _ m_u
          hlen_u hw_u hcl0_u _ hok_f hm_u => ?_⟩
      · rw [← hget_g]; exact hl0_ent
      · have hsp_u : FullSparseInvW c F0 F_cur _ :=
          ⟨hlen_u, hw_u, hsp_g.2.2.1, hsp_g.2.2.2.1, hsp_g.2.2.2.2.1, hsp_g.2.2.2.2.2⟩
        viv_steps
        · exact hJu (1#64, ()) m_u ⟨_, hsp_u, hcl0_u, hs2_cv, hs2_al, hs2_pr, hs2_fu,
            hrefs_g0, rfl, rfl, Or.inl rfl, (fun h => by cases h), hm_u⟩
        · have hlt2v : (ar_g[(BitVec.setWidth 64 cref + 3).toNat]'harg_c3).toNat <
              2 * s2.core.cur_vars := by
            rw [← hget_g]; exact hl0_lt
          rcases hok_f (by simpa using hc) with hge | ⟨huns, _⟩
          · exact False.elim (Nat.not_le_of_gt hlt2v hge)
          · exact hJu (20#64, ()) m_u ⟨_, hsp_u, hcl0_u, hs2_cv, hs2_al, hs2_pr, hs2_fu,
              hrefs_g0, rfl, rfl, Or.inr rfl, (fun _ => huns), hm_u⟩
  · intro J2 hJ2
    exact simplify_decr_wp Γ hm_g0 fun ni' nr' md hmd => hJ2 md ⟨ni', nr', hmd⟩

abbrev simplifyNsz2Expr (c : FullCfg) (cref hdr_v old_sz : Val i32) :
    Expr Val Cont [i64] :=
  Expr.load i32 (Arg.var (c.pArena + (BitVec.setWidth 64 cref + 3) * 4)) fun ld0 =>
  fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var c.pArena, Arg.var p.fst, ()) fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld1 =>
  Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin_m6"
    (Arg.var c.hdr, Arg.var ld0, Arg.var ld1, ()) fun p =>
  fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p1 =>
  fvOp (OpCode.mul i64) (Arg.var p1.fst, Arg.imm 4, ()) fun p2 =>
  fvOp (OpCode.add i64) (Arg.var c.pArena, Arg.var p2.fst, ()) fun p3 =>
  fvOp (OpCode.or i32) (Arg.var hdr_v, Arg.imm 524288, ()) fun p4 =>
  Expr.store (Arg.var p4.fst) (Arg.var p3.fst)
    (fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 472, ()) fun p5 =>
     Expr.load i64 (Arg.var p5.fst) fun ld =>
     fvOp (OpCode.add i64) (Arg.var ld, Arg.imm 3, ()) fun p6 =>
     fvOp (OpCode.zext 32 64) (Arg.var old_sz, ()) fun p7 =>
     fvOp (OpCode.add i64) (Arg.var p6.fst, Arg.var p7.fst, ()) fun p8 =>
     fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 472, ()) fun p9 =>
     Expr.store (Arg.var p8.fst) (Arg.var p9.fst)
       (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
         fvOp (OpCode.cmp .eq i64 .bool (by decide)) (Arg.var p.fst, Arg.imm 20, ()) fun c1 =>
         Expr.jnz (Arg.var c1.fst) (Expr.ret (Arg.imm 20, ()))
           (fvOp (OpCode.cmp .eq i64 .bool (by decide)) (Arg.var p.fst, Arg.imm 2, ()) fun c2 =>
            Expr.jnz (Arg.var c2.fst) (Expr.ret (Arg.imm 2, ())) (Expr.ret (Arg.imm 1, ()))))
         Blocks.nil) fun Js =>
        simplifyDecrExpr c.hdr hdr_v Js.fst))

private theorem simplify_nsz2_wp (Γ : Env)
    (hBin : Γ.Has "full_add_bin_m6" fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 s2 : FullState}
    {R : Mem 64 → Prop} {cref old_sz hdr_v : Val i32}
    {ar_c : List (BitVec 32)} {idxs : List Nat}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hcl2 : s2.core.cur_level = 0)
    (hs2_ar : s2.core.arena = s0.core.arena) (hs2_cv : s2.core.cur_vars = s0.core.cur_vars)
    (hs2_al : s2.core.arena_len = s0.core.arena_len) (hs2_pr : s2.core.probing = s0.core.probing)
    (hs2_fu : s2.core.fuel = s0.core.fuel)
    (hs2_rr : s2.scratch.red_refs = s0.scratch.red_refs)
    (hs2_tr : s2.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s0)
    (href0 : cref.toNat ∈ fullArenaClauseRefs s0) (hg0 : fullArenaClauseGarb s0 cref.toNat = false)
    (hhdr_v : hdr_v = fullArenaHdr s2 cref.toNat)
    (hsz0 : fullArenaClauseSize s0 cref.toNat = old_sz.toNat) (hsz_ge3 : 3 ≤ old_sz.toNat)
    (hbd2 : cref.toNat + 3 + fullArenaClauseSizeCore s2.core cref.toNat ≤ s2.core.arena.length)
    (harc_len : ar_c.length = c.arena_cap) (hlen_i : idxs.length = 2)
    (hq_i : ∀ q ∈ idxs, q < old_sz.toNat)
    (hout_i : ∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + 2 ≤ p) →
      ar_c[p]? = s2.core.arena[p]?)
    (hmap_i : ∀ t < 2,
      ar_c[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs[t]?.getD 0]?)
    (hdrop_i : ∀ j < old_sz.toNat, j ∈ idxs ∨
      ((s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
        s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 255#8))
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar_c } } ⋆ R) m)
    (hQ : VivSimpQ c F0 F_cur s0 R Q cref.toNat) :
    wp Γ Q X (simplifyNsz2Expr c cref hdr_v old_sz) m := by
  subst hhdr_v
  have hcl2_ok := hsp2.1.core_ok
  have hsz2 : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := by
    unfold fullArenaClauseSizeCore; rw [hs2_ar]; exact hsz0
  have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := hrefs2.symm ▸ href0
  have hg2 : fullArenaClauseGarb s2 cref.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hs2_ar]; exact hg0
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hc0_idx : (BitVec.setWidth 64 cref).toNat = cref.toNat := by bv_omega
  have hc3_idx : (BitVec.setWidth 64 cref + 3).toNat = cref.toNat + 3 := by bv_omega
  have hc4_idx : (BitVec.setWidth 64 cref + 4).toNat = cref.toNat + 4 := by bv_omega
  have hcref0_lt : (BitVec.setWidth 64 cref).toNat < ar_c.length := by
    rw [hc0_idx, harc_len, ← hcl2_ok.arena_len_arr]; omega
  have hcref3_lt : (BitVec.setWidth 64 cref + 3).toNat < ar_c.length := by
    rw [hc3_idx, harc_len, ← hcl2_ok.arena_len_arr]; omega
  have hcref4_lt : (BitVec.setWidth 64 cref + 4).toNat < ar_c.length := by
    rw [hc4_idx, harc_len, ← hcl2_ok.arena_len_arr]; omega
  let s_c : FullState := { s2 with core := { s2.core with arena := ar_c } }
  have hlen_c : s_c.LengthsOk c :=
    ⟨{ hsp2.1.core_ok with arena_len_arr := harc_len }, hsp2.1.scratch_ok⟩
  obtain ⟨hw_c, hrefs_c, _, _, hent_bin⟩ := simplify_nsz2_prep hsp2 hcl2 href2 hg2 hsz2 hsz_ge3
    hbd2 harc_len hlen_i hq_i hout_i hmap_i hdrop_i
  dsimp only [simplifyNsz2Expr, fvOp]
  viv_steps
  viv_call hBin
  refine ⟨c, F0, F_cur, s_c, R, rfl, hlen_c, hw_c, hcl2, fun _ _ => ?_, hm,
    fun rb va' fl' lv' rs' tr' tp' te' un' uf' wv' ws' wl' wu' nb' oo' ic' ph' wso'
      mb hlen_b hw_b hrb h20 _ hmb => ?_⟩
  · have h3 : ar_c[cref.toNat + 3]?.getD 0#32 =
        ar_c[(BitVec.setWidth 64 cref + 3).toNat]'hcref3_lt := by
      rw [← hc3_idx, List.getElem?_eq_getElem hcref3_lt, Option.getD_some]
    have h4 : ar_c[cref.toNat + 4]?.getD 0#32 =
        ar_c[(BitVec.setWidth 64 cref + 4).toNat]'hcref4_lt := by
      rw [← hc4_idx, List.getElem?_eq_getElem hcref4_lt, Option.getD_some]
    rw [← h3, ← h4]; exact hent_bin
  · let sb_c : FullCoreState :=
      { s_c.core with
        vals := va', flags := fl', lvl := lv', rsns := rs', trl := tr', trail_pos := tp',
        trail_end := te', unassigned := un', unflushed := uf', wvec := wv', wstk := ws',
        wlen := wl', wusable := wu', num_binary := nb', oom := oo', inconsistent := ic' }
    let s_b : FullState :=
      { core := sb_c, scratch := { s_c.scratch with phases := ph', wsort := wso' } }
    viv_to_group
    let ag' := s_b.core.arena_garbage + 3#64 + BitVec.setWidth 64 old_sz
    let ar_g := ar_c.set cref.toNat (fullArenaHdr s2 cref.toNat ||| 0x80000#32)
    have hm_bg0 : (FullMem c { s_b with core := { s_b.core with
        arena := ar_g, arena_garbage := ag' } } ⋆ R) m := by
      have heq : ar_c.set (BitVec.setWidth 64 cref).toNat
          (fullArenaHdr s2 cref.toNat ||| 524288#32) = ar_g := by rw [hc0_idx]
      rw [← heq]; exact hm
    let sc_g (ni' nr' : BitVec 64) : FullCoreState :=
      { s_b.core with
        arena := ar_g, arena_garbage := ag'
        num_irred := ni', num_redundant := nr' }
    let sb_g (ni' nr' : BitVec 64) : FullState := { s_b with core := sc_g ni' nr' }
    refine wp_join0 (fun md => ∃ ni' nr', (FullMem c (sb_g ni' nr') ⋆ R) md) ?_ ?_
    · rintro _ md ⟨ni', nr', hmd⟩
      have hrefs_cb : fullArenaClauseRefs s_b = fullArenaClauseRefs s2 := hrefs_c
      have hxs_b : FullExtScratchOk c s_b := FullExtScratchOk.of_pres hsp2.2.2.2.2.1
        ⟨rfl, rfl⟩ fun r hr => by rw [hrefs_cb]; exact hr
      have hsp_g := simplify_garb_of_compacted hsp2 hlen_b hw_b hcl2 hsp2.2.2.1 hxs_b
        hsp2.2.2.2.2.2 rfl href2 (hrefs_cb.symm ▸ href2) hsz2 (fun p hp => hout_i p (by omega))
        (by omega) ag' ni' nr' s_b.scratch.viv_cnt
      have har_gb : s_b.core.arena.set cref.toNat (fullArenaHdr s_b cref.toNat ||| 0x80000#32) =
          ar_g := by
        simp [ar_g, fullArenaHdr, fullArenaHdrCore, s_b, sb_c, s_c,
          hout_i cref.toNat (Or.inl (by omega)), hs2_ar]
      let st_raw : FullState :=
        { core :=
            { s_b.core with
              arena := s_b.core.arena.set cref.toNat
                (fullArenaHdr s_b cref.toNat ||| 0x80000#32),
              arena_garbage := ag', num_irred := ni', num_redundant := nr' },
          scratch := { s_b.scratch with viv_cnt := s_b.scratch.viv_cnt } }
      have heq_st : st_raw = sb_g ni' nr' := by
        dsimp only [st_raw, sb_g, sc_g]; rw [har_gb]
      have hsp_g' : FullSparseInvW c F0 F_cur (sb_g ni' nr') := heq_st ▸ hsp_g.1
      have hrefs_g' : fullArenaClauseRefs (sb_g ni' nr') = fullArenaClauseRefs s0 := by
        rw [← heq_st, hsp_g.2, hrefs_cb, hrefs2]
      viv_steps
      · exact hQ 20#64 _ md hsp_g' hcl2 hs2_cv hs2_al hs2_pr hs2_fu hrefs_g' hs2_rr hs2_tr
          (Or.inr (Or.inr (Or.inr rfl))) (fun _ => (h20 hc).1) (fun h => by cases h) hmd
      · exact hQ 2#64 _ md hsp_g' hcl2 hs2_cv hs2_al hs2_pr hs2_fu hrefs_g' hs2_rr hs2_tr
          (Or.inr (Or.inr (Or.inl rfl))) (fun h => by cases h) (fun h => by cases h) hmd
      · exact hQ 1#64 _ md hsp_g' hcl2 hs2_cv hs2_al hs2_pr hs2_fu hrefs_g' hs2_rr hs2_tr
          (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun h => by cases h) hmd
    · intro J2 hJ2
      exact simplify_decr_wp Γ hm_bg0 fun ni' nr' md hmd => hJ2 md ⟨ni', nr', hmd⟩

theorem full_viv_simplify_m6_wp (Γ : Env)
    (hUnwatch : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    (hUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hBin : Γ.Has "full_add_bin_m6" fullAddBinSpec)
    (hWpush : Γ.Has "full_watch_push" fullWatchPushSpec) :
    ∀ args m Q X, fullVivSimplifyM6Spec args m Q X →
      Func.wp Γ full_viv_simplify_m6_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, hcl0, href0, hg0, hm0, hQ⟩
  have hcl_ok := hsp0.1.core_ok; have hw0 := hsp0.2.1
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hwf0 := hw0.arena.refs_wf cref.toNat href0
  have hlen_arr0 : s0.core.arena.length = c.arena_cap := hcl_ok.arena_len_arr
  have hlen_le0 : s0.core.arena_len ≤ c.arena_cap := hcl_ok.arena_len_le
  have hsz_c0 :
      fullArenaClauseSizeCore s0.core cref.toNat = fullArenaClauseSize s0 cref.toNat := rfl
  have hsz_ge3 : 3 ≤ fullArenaClauseSize s0 cref.toNat := hwf0.2.1
  have hbd0 : cref.toNat + 3 + fullArenaClauseSize s0 cref.toNat ≤ s0.core.arena.length := by
    have h1 := hwf0.2.2.1; have h2 := hwf0.2.2.2.1; rw [hsz_c0] at h1; omega
  have hcref_lt : cref.toNat < s0.core.arena.length := by omega
  have hcref2_lt : cref.toNat + 2 < s0.core.arena.length := by omega
  unfold Func.wp full_viv_simplify_m6_body
  viv_to_group
  let old_sz := s0.core.arena[cref.toNat + 2]?.getD 0#32
  have hold_sz_eq : s0.core.arena[cref.toNat + 2] = old_sz := by
    dsimp only [old_sz]; rw [List.getElem?_eq_getElem hcref2_lt, Option.getD_some]
  have hold_sz_nat : old_sz.toNat = fullArenaClauseSize s0 cref.toNat := rfl
  have hc_idx2 : (BitVec.toNat cref + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
    have h2 : BitVec.toNat (2 : BitVec 64) = 2 := by decide
    rw [h2]; omega
  have har_c2_eq :
      s0.core.arena[(BitVec.toNat cref + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64] = old_sz :=
    Option.some.inj (by
      rw [← List.getElem?_eq_getElem (by rw [hc_idx2]; exact hcref2_lt), hc_idx2,
        List.getElem?_eq_getElem hcref2_lt, hold_sz_eq])
  refine wp_loop_inv (ts := [i32, i32])
    (fun (k_v, i_v, ()) mi =>
      (FullMem c s0 ⋆ R) mi ∧ k_v.toNat ≤ i_v.toNat ∧ i_v.toNat ≤ old_sz.toNat ∧
      (k_v.toNat < i_v.toNat → ∃ j0 < i_v.toNat,
        (s0.core.vals[(s0.core.arena[cref.toNat + 3 + j0]?.getD 0#32).toNat]?.getD 0#8) ≠ 0#8) ∧
      ∀ j < i_v.toNat,
        (s0.core.vals[(s0.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8) ≠ 1#8)
    (fun (_, i_v, _) _ => old_sz.toNat - i_v.toNat) ?_ ?_
  · intro J hJ
    viv_steps
    exact hJ (0#32, 0#32, ()) m0 ⟨hm0, Nat.zero_le _, Nat.zero_le _,
      fun h => by omega, fun _ hj => by simp at hj⟩
  · rintro J ⟨k_v, i_v, ⟨⟩⟩ mi ⟨hmi, hk_le, hi_le, hmiss, hno_sat⟩ ih
    viv_step; viv_step
    · have hi_lt : i_v.toNat < old_sz.toNat := by
        rw [← har_c2_eq]; exact hc
      have hbd_i : cref.toNat + 3 + i_v.toNat < s0.core.arena.length := by omega
      have hlit_mem : (s0.core.arena[cref.toNat + 3 + i_v.toNat]?.getD 0#32).toNat ∈
          fullArenaClauseLitsCore s0.core cref.toNat := by
        refine (mem_fullArenaClauseLitsCore_iff (by rw [hsz_c0]; exact hbd0)).mpr
          ⟨i_v.toNat, by rw [hsz_c0]; exact hi_lt, ?_⟩
        rw [List.getElem?_eq_getElem hbd_i, Option.getD_some]
      have hlit_lt := hw0.arena.lits_lt cref.toNat href0 hg0 _ hlit_mem
      have hidx_eq : (BitVec.setWidth 64 cref + 3#64 + BitVec.setWidth 64 i_v).toNat =
          cref.toNat + 3 + i_v.toNat := by bv_omega
      obtain ⟨_, hlit_lt_vals, _⟩ := simplify_lit_idx_facts hidx_eq hbd_i hbd_i rfl
        hlit_lt hcl_ok.cur_vars_le hcl_ok.vals_len
      have hmod_eq : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_v.toNat) % 2 ^ 64 =
          cref.toNat + 3 + i_v.toNat := by bv_omega
      obtain ⟨_, _, hmod_val_eq⟩ := simplify_lit_idx_facts hmod_eq hbd_i hbd_i rfl
        hlit_lt hcl_ok.cur_vars_le hcl_ok.vals_len
      have hcref3_lt : cref.toNat + 3 < s0.core.arena.length := by omega
      have hcref4_lt : cref.toNat + 4 < s0.core.arena.length := by omega
      viv_to_group
      · viv_to_group
        refine viv_unwatch_one_wp Γ hUnwatch hsp0 hmi fun w1 ws1 u1 m1 hsp1 hm1 => ?_
        let s1 : FullState :=
          { s0 with core := { s0.core with wvec := w1, wstk := ws1, wusable := u1 } }
        viv_to_group
        refine viv_unwatch_one_wp Γ hUnwatch hsp1 hm1 fun w2 ws2 u2 m2 hsp2 hm2 => ?_
        let s2 : FullState :=
          { s1 with core := { s1.core with wvec := w2, wstk := ws2, wusable := u2 } }
        viv_to_group
        have hc_idx : (BitVec.setWidth 64 cref).toNat = cref.toNat := by bv_omega
        let ag' := s0.core.arena_garbage + 3#64 + BitVec.setWidth 64 old_sz
        have hhdr_eq : s0.core.arena[(BitVec.setWidth 64 cref).toNat] =
            fullArenaHdr s2 cref.toNat := by
          unfold fullArenaHdr fullArenaHdrCore
          rw [List.getElem?_eq_getElem hcref_lt, Option.getD_some]
          exact Option.some.inj (by
            rw [← List.getElem?_eq_getElem (by rw [hc_idx]; exact hcref_lt),
              ← List.getElem?_eq_getElem hcref_lt, hc_idx])
        have har_g_eq : s0.core.arena.set (BitVec.setWidth 64 cref).toNat
            (s0.core.arena[(BitVec.setWidth 64 cref).toNat] ||| (524288 : BitVec 32)) =
            s2.core.arena.set cref.toNat (fullArenaHdr s2 cref.toNat ||| 0x80000#32) := by
          rw [hhdr_eq, hc_idx]; rfl
        have har_c2_eq' : s0.core.arena[(BitVec.toNat cref + 2) % 2 ^ 64] = old_sz := by
          simpa using har_c2_eq
        have hm_g0 : (FullMem c { s2 with core := { s2.core with
            arena := s2.core.arena.set cref.toNat (fullArenaHdr s2 cref.toNat ||| 0x80000#32),
            arena_garbage := ag' } } ⋆ R) m := by
          rw [har_g_eq] at hm
          simpa [har_c2_eq'] using hm
        clear hm
        refine wp_join0 (fun md => ∃ sd, FullSparseInvW c F0 F_cur sd ∧
          sd.core.cur_level = 0 ∧ sd.core.cur_vars = s0.core.cur_vars ∧
          sd.core.arena_len = s0.core.arena_len ∧ sd.core.probing = s0.core.probing ∧
          sd.core.fuel = s0.core.fuel ∧ fullArenaClauseRefs sd = fullArenaClauseRefs s0 ∧
          sd.scratch.red_refs = s0.scratch.red_refs ∧
          sd.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧ (FullMem c sd ⋆ R) md) ?_ ?_
        · rintro _ md ⟨sd, hspd, hcld, hcvd, hald, hprd, hfud, hrefsd, hrrd, htrd, hmd⟩
          viv_steps
          exact hQ 1#64 sd md hspd hcld hcvd hald hprd hfud hrefsd hrrd htrd
            (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun h => by cases h) hmd
        · intro J2 hJ2
          exact simplify_decr_wp Γ hm_g0 fun ni' nr' md hmd => by
            have hm_g := markGarb_hnonact_preserves_fullSparseW hsp2 href0
              (nonActiveReason_of_level0 hsp2.2.1 hcl0 cref.toNat) ag' ni' nr' s0.scratch.viv_cnt
            exact hJ2 md ⟨_, hm_g.1, hcl0, rfl, rfl, rfl, rfl, hm_g.2, rfl, rfl, hmd⟩
      · have hhc_sat := hc
        refine wp_join_group (ts := [i32])
          (fun (k', ()) md => (FullMem c s0 ⋆ R) md ∧ k'.toNat ≤ i_v.toNat + 1 ∧
            (k'.toNat < i_v.toNat + 1 → ∃ j0 < i_v.toNat + 1,
              (s0.core.vals[(s0.core.arena[cref.toNat + 3 + j0]?.getD 0#32).toNat]?.getD 0#8) ≠
                0#8) ∧
            ∀ j < i_v.toNat + 1,
              (s0.core.vals[(s0.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8) ≠ 1#8)
          ?_ ?_
        · rintro _ ⟨k', ⟨⟩⟩ md ⟨hm', hk', hm_miss', hns'⟩
          viv_steps
          have hi1 : (i_v + 1#32).toNat = i_v.toNat + 1 := by bv_omega
          refine ih (k', i_v + 1#32, ()) md (by dsimp only; rw [hi1]; omega)
            ⟨hm', by rw [hi1]; exact hk', by rw [hi1]; omega,
              by simpa [hi1] using hm_miss', by simpa [hi1] using hns'⟩
        · intro J2 hJ2
          viv_to_group
          · viv_steps
            have hkv1 : (k_v + 1#32).toNat = k_v.toNat + 1 := by bv_omega
            refine hJ2 (k_v + 1#32, ()) mi ⟨hmi, by rw [hkv1]; omega, fun h => ?_, fun j hj => ?_⟩
            · rw [hkv1] at h
              obtain ⟨j0, hj0, hj0_p⟩ := hmiss (by omega)
              exact ⟨j0, by omega, hj0_p⟩
            · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
              · exact hno_sat j hlt
              · intro h1
                rw [hmod_val_eq] at h1
                rw [h1] at hc
                exact absurd hc (by decide)
          · viv_steps
            have hne0 :
                s0.core.vals[(s0.core.arena[cref.toNat + 3 + i_v.toNat]?.getD 0#32).toNat]?.getD
                  0#8 ≠ 0#8 := by
              intro h0
              rw [hmod_val_eq] at h0
              exact hc (by rw [h0]; decide)
            refine hJ2 (k_v, ()) mi ⟨hmi, by omega, fun _ => ⟨i_v.toNat, by omega, hne0⟩,
              fun j hj => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
            · exact hno_sat j hlt
            · intro h1
              rw [hmod_val_eq] at h1
              have htrue : (0#32).slt (BitVec.signExtend 32 1#8) = true := by decide
              rw [← h1, hhc_sat] at htrue
              cases htrue
    · have hi_eq : i_v.toNat = old_sz.toNat := by
        rw [har_c2_eq] at hc; omega
      viv_to_group
      · viv_steps
        exact hQ 0#64 s0 mi hsp0 hcl0 rfl rfl rfl rfl rfl rfl rfl
          (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨href0, hg0⟩) hmi
      · have hk_lt : k_v.toNat < old_sz.toNat := by
          have hne : k_v.toNat ≠ old_sz.toNat := fun heq => by
            apply hc
            rw [har_c2_eq]
            exact BitVec.eq_of_toNat_eq heq
          omega
        obtain ⟨j_miss, hj_miss_lt, hj_miss_val⟩ := hmiss (by omega)
        viv_to_group
        refine viv_unwatch_one_wp Γ hUnwatch hsp0 hmi fun w1 ws1 u1 m1 hsp1 hm1 => ?_
        let s1 : FullState :=
          { s0 with core := { s0.core with wvec := w1, wstk := ws1, wusable := u1 } }
        viv_to_group
        refine viv_unwatch_one_wp Γ hUnwatch hsp1 hm1 fun w2 ws2 u2 m2 hsp2 hm2 => ?_
        let s2 : FullState :=
          { s1 with core := { s1.core with wvec := w2, wstk := ws2, wusable := u2 } }
        viv_to_group
        have hsp2' := hsp2
        have hcl2 : s2.core.cur_level = 0 := hcl0
        have hw2 := hsp2.2.1
        have hcl_ok2 := hsp2.1.core_ok
        refine wp_loop_inv (ts := [i32, i32])
          (fun (i2_v, nsz_v, ()) mi2 => ∃ (ar_c : List (BitVec 32)) (idxs : List Nat),
            let s_c := { s2 with core := { s2.core with arena := ar_c } }
            i2_v.toNat ≤ old_sz.toNat ∧ nsz_v.toNat ≤ i2_v.toNat ∧
            ar_c.length = c.arena_cap ∧ idxs.length = nsz_v.toNat ∧
            List.Pairwise (· < ·) idxs ∧ (∀ q ∈ idxs, q < i2_v.toNat) ∧
            (∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + nsz_v.toNat ≤ p) →
              ar_c[p]? = s2.core.arena[p]?) ∧
            (∀ t < nsz_v.toNat,
              ar_c[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs[t]?.getD 0]?) ∧
            (∀ j < i2_v.toNat, j ∈ idxs ∨
              ((s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
                s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 =
                  255#8)) ∧
            (j_miss < i2_v.toNat → j_miss ∉ idxs) ∧
            (FullMem c s_c ⋆ R) mi2)
          (fun (i2_v, _, ()) _ => old_sz.toNat - i2_v.toNat) ?_ ?_
        · intro J2 hJ2
          viv_steps
          exact hJ2 (0#32, 0#32, ()) m2 ⟨s2.core.arena, [], Nat.zero_le _, Nat.zero_le _,
            hlen_arr0, rfl, List.Pairwise.nil, fun _ h => by simp at h,
            fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h,
            fun h => by simp at h, hm2⟩
        · rintro J2 ⟨i2_v, nsz_v, ⟨⟩⟩ mi2 ⟨ar_c, idxs, hi2_le, hnsz_le, harc_len, hlen_i,
            hpw_i, hq_i, hout_i, hmap_i, hdrop_i, hmiss_i, hmc⟩ ih2
          viv_step; viv_step
          · have hi2_lt : i2_v.toNat < old_sz.toNat := by
              rw [← har_c2_eq]; exact hc
            have hbd_i2 : cref.toNat + 3 + i2_v.toNat < ar_c.length := by
              rw [harc_len, ← hlen_arr0]; omega
            have hbd_i2_s2 : cref.toNat + 3 + i2_v.toNat < s2.core.arena.length := by
              change cref.toNat + 3 + i2_v.toNat < s0.core.arena.length; omega
            have harc_i2 : ar_c[cref.toNat + 3 + i2_v.toNat]? =
                s2.core.arena[cref.toNat + 3 + i2_v.toNat]? :=
              hout_i _ (Or.inr (by omega))
            have hsz_c2 : fullArenaClauseSizeCore s2.core cref.toNat =
                fullArenaClauseSize s0 cref.toNat := rfl
            have hbd2 : cref.toNat + 3 + fullArenaClauseSizeCore s2.core cref.toNat ≤
                s2.core.arena.length := by rw [hsz_c2]; exact hbd0
            have hlit2_mem : (s2.core.arena[cref.toNat + 3 + i2_v.toNat]?.getD 0#32).toNat ∈
                fullArenaClauseLitsCore s2.core cref.toNat := by
              refine (mem_fullArenaClauseLitsCore_iff hbd2).mpr
                ⟨i2_v.toNat, by rw [hsz_c2]; exact hi2_lt, ?_⟩
              rw [List.getElem?_eq_getElem hbd_i2_s2, Option.getD_some]
            have hlit2_lt := hw2.arena.lits_lt cref.toNat href0 hg0 _ hlit2_mem
            have hidx2_eq : (BitVec.setWidth 64 cref + 3#64 + BitVec.setWidth 64 i2_v).toNat =
                cref.toNat + 3 + i2_v.toNat := by bv_omega
            have hmod2_eq : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i2_v.toNat) % 2 ^ 64 =
                cref.toNat + 3 + i2_v.toNat := by bv_omega
            obtain ⟨hlit2_eq, _, _⟩ := simplify_lit_idx_facts hidx2_eq hbd_i2 hbd_i2_s2
              harc_i2 hlit2_lt hcl_ok2.cur_vars_le hcl_ok2.vals_len
            obtain ⟨_, _, hmod2_val_eq⟩ := simplify_lit_idx_facts hmod2_eq hbd_i2 hbd_i2_s2
              harc_i2 hlit2_lt hcl_ok2.cur_vars_le hcl_ok2.vals_len
            have hbd_n2 : cref.toNat + 3 + nsz_v.toNat < ar_c.length := by
              rw [harc_len, ← hlen_arr0]; omega
            viv_to_group
            refine wp_join_group (ts := [i32])
              (fun (nsz', ()) md => ∃ ar_c' idxs',
                let s_c' := { s2 with core := { s2.core with arena := ar_c' } }
                nsz'.toNat ≤ i2_v.toNat + 1 ∧ ar_c'.length = c.arena_cap ∧
                idxs'.length = nsz'.toNat ∧ List.Pairwise (· < ·) idxs' ∧
                (∀ q ∈ idxs', q < i2_v.toNat + 1) ∧
                (∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + nsz'.toNat ≤ p) →
                  ar_c'[p]? = s2.core.arena[p]?) ∧
                (∀ t < nsz'.toNat,
                  ar_c'[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs'[t]?.getD 0]?) ∧
                (∀ j < i2_v.toNat + 1, j ∈ idxs' ∨
                  ((s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
                    s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 =
                      255#8)) ∧
                (j_miss < i2_v.toNat + 1 → j_miss ∉ idxs') ∧
                (FullMem c s_c' ⋆ R) md) ?_ ?_
            · rintro _ ⟨nsz', ⟨⟩⟩ md ⟨ar_c', idxs', hnsz', harc', hli', hpi', hqi', hou', hmi',
                hdi', hmsi', hm'⟩
              viv_steps
              have hi21 : (i2_v + 1#32).toNat = i2_v.toNat + 1 := by bv_omega
              refine ih2 (i2_v + 1#32, nsz', ()) md (by dsimp only; rw [hi21]; omega)
                ⟨ar_c', idxs', by rw [hi21]; omega, by rw [hi21]; exact hnsz', harc', hli', hpi',
                  by simpa [hi21] using hqi', hou', hmi', by simpa [hi21] using hdi',
                  by simpa [hi21] using hmsi', hm'⟩
            · intro J3 hJ3
              viv_to_group
              · viv_steps
                have hnsz1 : (nsz_v + 1#32).toNat = nsz_v.toNat + 1 := by bv_omega
                have hidx_n : (BitVec.setWidth 64 cref + 3#64 + BitVec.setWidth 64 nsz_v).toNat =
                    cref.toNat + 3 + nsz_v.toNat := by bv_omega
                let lit2 := ar_c[(BitVec.setWidth 64 cref + 3#64 + BitVec.setWidth 64 i2_v).toNat]
                let ar_c' := ar_c.set (cref.toNat + 3 + nsz_v.toNat) lit2
                let idxs' := idxs ++ [i2_v.toNat]
                refine hJ3 (nsz_v + 1#32, ()) _ ⟨ar_c', idxs', by rw [hnsz1]; omega,
                  by simp [ar_c', harc_len], by simp [idxs', hlen_i, hnsz1],
                  ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · exact List.pairwise_append.mpr ⟨hpw_i, List.pairwise_singleton _ _,
                    fun a ha b hb => by
                      simp only [List.mem_singleton] at hb; subst hb; exact hq_i a ha⟩
                · intro q hq; simp only [idxs', List.mem_append, List.mem_singleton] at hq
                  rcases hq with hq | rfl
                  · exact Nat.lt_succ_of_lt (hq_i q hq)
                  · omega
                · intro p hp; rw [hnsz1] at hp
                  dsimp only [ar_c']
                  rw [List.getElem?_set_ne (by omega)]
                  exact hout_i p
                    (by rcases hp with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
                · intro t ht; rw [hnsz1] at ht
                  dsimp only [ar_c', idxs', lit2]; rw [hlit2_eq]
                  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
                  · rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]
                    exact hmap_i t hlt
                  · rw [List.getElem?_set_self hbd_n2, List.getElem?_append_right (by omega),
                      show nsz_v.toNat - idxs.length = 0 by omega]
                    simp [List.getElem?_eq_getElem hbd_i2_s2]
                · intro j hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                  · rcases hdrop_i j hlt with hmem | hfl
                    · exact Or.inl (by simp [idxs', hmem])
                    · exact Or.inr hfl
                  · exact Or.inl (by simp [idxs'])
                · intro hjlt; simp only [idxs', List.mem_append, List.mem_singleton]
                  rintro (hmem | heq)
                  · exact hmiss_i (hq_i _ hmem) hmem
                  · subst heq
                    rcases hw2.vals_domain _ hlit2_lt with h0 | h1 | hff
                    · exact hj_miss_val h0
                    · rw [hmod2_val_eq] at h1; rw [h1] at hc; exact absurd hc (by decide)
                    · rw [hmod2_val_eq] at hff; rw [hff] at hc; exact absurd hc (by decide)
                · dsimp only [ar_c']; simp only [← hidx_n]; assumption
              · viv_steps
                refine hJ3 (nsz_v, ()) mi2 ⟨ar_c, idxs, by omega, harc_len, hlen_i, hpw_i,
                  fun q hq => Nat.lt_succ_of_lt (hq_i q hq), hout_i, hmap_i, fun j hj => ?_,
                  fun hjlt => ?_, hmc⟩
                · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                  · exact hdrop_i j hlt
                  · right
                    have hdom2 := hw2.vals_domain _ hlit2_lt
                    have hns0 :
                        s2.core.vals[(s2.core.arena[cref.toNat + 3 + i2_v.toNat]?.getD
                          0#32).toNat]?.getD 0#8 ≠ 0#8 := by
                      intro h0
                      rw [hmod2_val_eq] at h0
                      exact hc (by rw [h0]; decide)
                    have hne1 := hno_sat i2_v.toNat (hi_eq ▸ hi2_lt)
                    rcases hdom2 with h0 | h1 | hff
                    · exact absurd h0 hns0
                    · exact absurd h1 hne1
                    · exact ⟨hlit2_lt, hff⟩
                · rcases Nat.lt_succ_iff_lt_or_eq.mp hjlt with hlt | rfl
                  · exact hmiss_i hlt
                  · exact fun hm => by have := hq_i _ hm; omega
          · have hi2_eq : i2_v.toNat = old_sz.toNat := by
              rw [har_c2_eq] at hc; omega
            have hnsz_lt : nsz_v.toNat < old_sz.toNat := by
              rw [← hlen_i]
              exact pairwise_lt_len_lt_of_missing hpw_i (fun q hq => hi2_eq ▸ hq_i q hq)
                (hi_eq ▸ hj_miss_lt) (hmiss_i (hi2_eq ▸ hi_eq ▸ hj_miss_lt))
            have hbd_s2 : cref.toNat + 3 + fullArenaClauseSizeCore s2.core cref.toNat ≤
                s2.core.arena.length := by
              dsimp only [s2, s1]
              unfold fullArenaClauseSizeCore
              change cref.toNat + 3 + (s0.core.arena[cref.toNat + 2]?.getD 0#32).toNat ≤
                s0.core.arena.length
              simpa [fullArenaClauseSizeCore, hsz_c0] using hbd0
            have harc_len' : cref.toNat + 3 + old_sz.toNat ≤ ar_c.length := by
              rw [harc_len, ← hlen_arr0]; omega
            have hc0_idx : (BitVec.setWidth 64 cref).toNat = cref.toNat := by bv_omega
            have hs2_ar : s2.core.arena = s0.core.arena := rfl
            have hs2_cv : s2.core.cur_vars = s0.core.cur_vars := rfl
            have hs2_al : s2.core.arena_len = s0.core.arena_len := rfl
            have hs2_pr : s2.core.probing = s0.core.probing := rfl
            have hs2_fu : s2.core.fuel = s0.core.fuel := rfl
            have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s0 := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore
              rw [hs2_ar, hs2_al]
            have hhdr_v : s0.core.arena[(BitVec.setWidth 64 cref).toNat] =
                fullArenaHdr s2 cref.toNat := by
              unfold fullArenaHdr fullArenaHdrCore
              exact Option.some.inj (by
                rw [← List.getElem?_eq_getElem (by rw [hc0_idx]; exact hcref_lt), hc0_idx, hs2_ar,
                  List.getElem?_eq_getElem hcref_lt, Option.getD_some])
            have hc2_idx'' : (BitVec.setWidth 64 cref + 2).toNat = cref.toNat + 2 := by bv_omega
            have hold_v : s0.core.arena[(BitVec.setWidth 64 cref + 2).toNat] = old_sz :=
              Option.some.inj (by
                rw [← List.getElem?_eq_getElem (by rw [hc2_idx'']; exact hcref2_lt), hc2_idx'',
                  List.getElem?_eq_getElem hcref2_lt, hold_sz_eq])
            have hsz0' : fullArenaClauseSize s0 cref.toNat =
                (s0.core.arena[(BitVec.setWidth 64 cref + 2).toNat]).toNat := by
              rw [hold_v, hold_sz_nat]
            have hi2_eq' : i2_v.toNat =
                (s0.core.arena[(BitVec.setWidth 64 cref + 2).toNat]).toNat := by
              rw [hold_v, hi2_eq]
            clear ih J hmi hmiss hno_sat hk_lt hsp1 hm1 ih2 J2 hi2_le hnsz_le
            viv_step
            · viv_step
              have hnsz0 : nsz_v.toNat = 0 := by
                have := congrArg BitVec.toNat hc; simpa using this
              obtain ⟨har_eq, huns, hsp_uns⟩ := simplify_nsz0_unsat hsp2 hcl2 href0 hg0 hsz_c0
                hbd_s2 harc_len (by rw [hlen_i, hnsz0]) (fun p hp => hout_i p (by omega))
                (fun j hj => hdrop_i j (hi2_eq ▸ hj))
              viv_steps
              have hm_i : (FullMem c { s2 with core := { s2.core with inconsistent := 1#64 } } ⋆ R)
                  m := by simpa [har_eq] using hm
              exact hQ 20#64 _ m hsp_uns hcl0 rfl rfl rfl rfl
                hrefs2 rfl rfl (Or.inr (Or.inr (Or.inr rfl))) (fun _ => huns)
                (fun h => by cases h) hm_i
            · have hne0 : nsz_v.toNat ≠ 0 := fun h => by
                have heq : nsz_v = 0#32 := BitVec.eq_of_toNat_eq (by simpa using h)
                simp [heq] at hc
              viv_step
              · have hnsz1 : nsz_v.toNat = 1 := by
                  have := congrArg BitVec.toNat hc; simpa using this
                exact simplify_nsz1_wp Γ hUnit hsp2 hcl2 hs2_ar hs2_cv hs2_al hs2_pr hs2_fu
                  rfl rfl hrefs2 href0 hg0 hhdr_v hsz0' (by rw [hold_v]; exact hsz_ge3) hbd_s2
                  harc_len (by rw [hlen_i, hnsz1]) (fun q hq => hi2_eq' ▸ hq_i q hq)
                  (fun p hp => hout_i p (by omega)) (fun t ht => hmap_i t (by omega))
                  (fun j hj => hdrop_i j (hi2_eq' ▸ hj)) hmc hQ
              · have hne1 : nsz_v.toNat ≠ 1 := fun h => by
                  have heq : nsz_v = 1#32 := BitVec.eq_of_toNat_eq (by simpa using h)
                  simp [heq] at hc
                viv_step
                · have hnsz2 : nsz_v.toNat = 2 := by
                    have := congrArg BitVec.toNat hc; simpa using this
                  exact simplify_nsz2_wp Γ hBin hsp2 hcl2 hs2_ar hs2_cv hs2_al hs2_pr hs2_fu
                    rfl rfl hrefs2 href0 hg0 hhdr_v hsz0' (by rw [hold_v]; exact hsz_ge3) hbd_s2
                    harc_len (by rw [hlen_i, hnsz2]) (fun q hq => hi2_eq' ▸ hq_i q hq)
                    (fun p hp => hout_i p (by omega)) (fun t ht => hmap_i t (by omega))
                    (fun j hj => hdrop_i j (hi2_eq' ▸ hj)) hmc hQ
                · have hne2 : nsz_v.toNat ≠ 2 := fun h => by
                    have heq : nsz_v = 2#32 := BitVec.eq_of_toNat_eq (by simpa using h)
                    simp [heq] at hc
                  have hnsz3 : 3 ≤ nsz_v.toNat := by omega
                  refine simplify_nsz_ge3_wp Γ hWpush hsp2 hcl2 hs2_ar hs2_cv hs2_al hs2_pr
                    hs2_fu hrefs2 href0 hg0 hhdr_v hsz0' hbd_s2 hnsz3
                    (by rw [hold_v]; exact hnsz_lt) harc_len hlen_i hpw_i
                    (fun q hq => hi2_eq' ▸ hq_i q hq) (fun p hp => hout_i p (by omega))
                    (fun t ht => hmap_i t (by omega)) (fun j hj => hdrop_i j (hi2_eq' ▸ hj))
                    hmc ?_ ?_
                  · intro so mo hspo hclo hcvo halo hpro hfuo hrefso hrro htro hrefo hgarbo hmo
                    viv_steps
                    exact hQ 0#64 so mo hspo hclo hcvo halo hpro hfuo hrefso hrro htro
                      (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hrefo, hgarbo⟩) hmo
                  · intro so mo hspo hclo hcvo halo hpro hfuo hrefso hrro htro hmo
                    viv_steps
                    exact hQ 2#64 so mo hspo hclo hcvo halo hpro hfuo hrefso hrro htro
                      (Or.inr (Or.inr (Or.inl rfl))) (fun h => by cases h)
                      (fun h => by cases h) hmo

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
