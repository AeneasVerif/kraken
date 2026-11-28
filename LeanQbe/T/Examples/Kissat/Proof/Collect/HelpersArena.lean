/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersWatch
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges

/-!
# Arena Mutation, Compaction & Reason-Map Helpers (`Proof.Collect.HelpersArena`)

Pure arena clause-reference, header/body mutation, permutation, level-0 assignment,
`SweepReasonMapInv`, and `CompactPrefixOk` preservation lemmas used across `Proof.Collect`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Arena Reference & Clause-Mutation Preservation -/

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  have _ : 3 ≤ k.arena_len := ha.len_ok.elim (fun hz => by omega) id
  unfold fullArenaClauseRefsCore
  cases hal : k.arena_len with
  | zero => omega
  | succ f => unfold fullArenaScanRefs; simp [show 0 + 3 ≤ f + 1 by omega]

theorem fullArenaScanRefs_mem_next {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel → fullArenaNextOff ar alen r + 3 ≤ alen →
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, hr, _ => by simp [fullArenaScanRefs] at hr
  | fuel + 1, pos, r, hfl, hr, hn3 => by
    unfold fullArenaScanRefs at hr ⊢; split at hr
    · rename_i hle
      simp only [hle, ↓reduceIte, List.mem_cons] at hr ⊢
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases hr with rfl | hrest
      · right; cases fuel with
        | zero => omega
        | succ _ => unfold fullArenaScanRefs; simp [hn3]
      · exact Or.inr (fullArenaScanRefs_mem_next (by omega) hrest hn3)
    · simp at hr

theorem fullArenaClauseRefs_next_or_end {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k)
    {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  (ha.refs_wf r hr).2.2.2.2.elim Or.inl
    fun h3 => Or.inr (fullArenaScanRefs_mem_next (by omega) hr h3)

theorem fullArenaVarsNodup_of_refs_eq {s s' : FullState} (h : FullArenaVarsNodup s)
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hcl : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) :
    FullArenaVarsNodup s' := by
  intro r hr hng; rw [hrefs] at hr; obtain ⟨hg, hl⟩ := hcl r hr
  rw [hl]; exact h r hr (hg.symm.trans hng)

theorem modifyClauseBody_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur k) {p : Nat} (hp : p ∈ fullArenaClauseRefsCore k)
    {ar' : List (BitVec 32)} (hlen_ar : ar'.length = c.arena_cap)
    (hout : OutsideSliceAgrees (p + 1) (p + 3 + fullArenaClauseSizeCore k p) k.arena ar')
    (h2 : ar'[p + 2]? = k.arena[p + 2]?)
    (hmem : ∀ l, l ∈ fullArenaClauseLitsCore { k with arena := ar' } p ↔
      l ∈ fullArenaClauseLitsCore k p) :
    let k' := { k with arena := ar' }
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaHdrCore k' r = fullArenaHdrCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r) ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ p →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) ∧
    FullWitnessInv c F0 F_cur k' := by
  intro k'
  have hpwf := hw.arena.refs_wf p hp
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ p →
      (r + 3 + fullArenaClauseSizeCore k r ≤ p ∧ fullArenaNextOff k.arena k.arena_len r ≤ p) ∨
      (p + 3 + fullArenaClauseSizeCore k p ≤ fullArenaNextOff k.arena k.arena_len p ∧
        fullArenaNextOff k.arena k.arena_len p ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr hp hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr hp hlt⟩
    · exact Or.inr ⟨hpwf.2.2.1, fullArenaScanRefs_disjoint hp hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff ar' k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = p
    · subst r
      exact fullArenaNextOff_congr_block (hout.getElem?_lt (by omega)) h2
        (fun i hi _ => hout.getElem?_ge hi)
    · refine fullArenaNextOff_congr_block ?_ ?_ ?_
      · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by omega)
      · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by omega)
      · intro idx _ hi2; rcases hne_out r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by have := (hw.arena.refs_wf r hr).2.2.1; omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hmeta : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaHdrCore k' r = fullArenaHdrCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    by_cases hrp : r = p
    · subst r; have h0 := hout.getElem?_lt (i := p) (by omega)
      exact ⟨by unfold fullArenaHdrCore k'; rw [h0],
        by unfold fullArenaClauseSizeCore k'; rw [h2],
        by unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [h0]⟩
    · rcases hne_out r hr hrp with ⟨h1, _⟩ | ⟨_, h2'⟩
      · have h0 := hout.getElem?_lt (i := r) (by omega)
        have hs := hout.getElem?_lt (i := r + 2) (by omega)
        exact ⟨by unfold fullArenaHdrCore k'; rw [h0],
          by unfold fullArenaClauseSizeCore k'; rw [hs],
          by unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [h0]⟩
      · have h0 := hout.getElem?_ge (i := r) (by omega)
        have hs := hout.getElem?_ge (i := r + 2) (by omega)
        exact ⟨by unfold fullArenaHdrCore k'; rw [h0],
          by unfold fullArenaClauseSizeCore k'; rw [hs],
          by unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [h0]⟩
  have hlits_other : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ p →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr hrp => by
    have hbd1 : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    have hbd2 : r + 3 + fullArenaClauseSizeCore k r ≤ ar'.length := by
      rw [hlen_ar, ← hlen.arena_len_arr]; exact hbd1
    exact fullArenaClauseLitsCore_eq_of_hold (k := k) (k' := k') hbd1 hbd2
      (hmeta r hr).2.1 fun j hj => by
        rcases hne_out r hr hrp with ⟨h1, _⟩ | ⟨_, h2'⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by omega)
  have hmem_all : ∀ r ∈ fullArenaClauseRefsCore k,
      ∀ l, l ∈ fullArenaClauseLitsCore k' r ↔ l ∈ fullArenaClauseLitsCore k r := fun r hr l => by
    by_cases hrp : r = p
    · subst r; exact hmem l
    · rw [hlits_other r hr hrp]
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have h := hw.arena.refs_wf r hr
      dsimp only [k'] at hnxt ⊢; rw [hnxt r hr, (hmeta r hr).2.1]; exact h
    · intro r hr hsh; rw [hrefs] at hr; rw [(hmeta r hr).1] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh
      have hr3 := (hw.arena.refs_wf r hr).1
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have : r < k.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ := fullArenaNextOff_hits_sentinel hr3
        (by rw [hget_r, Option.getD_some]; exact hsh) ht1 ht2 hsent
      have hnxt_le := (hw.arena.refs_wf r hr).2.2.2.1
      refine ⟨t0, by rw [(hmeta r hr).2.1]; exact ht0_lo, by dsimp only [k']; omega, ?_⟩
      dsimp only [k']; by_cases hrp : r = p
      · subst r; rw [hout.getElem?_ge ht0_lo]; exact ht0_sent
      · rcases hne_out r hr hrp with ⟨_, _⟩ | ⟨_, _⟩
        · rw [hout.getElem?_lt (by omega)]; exact ht0_sent
        · rw [hout.getElem?_ge (by have := (hw.arena.refs_wf r hr).2.2.1; omega)]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hmeta r hr).2.2] at hng; rw [hmem_all r hr l] at hl; exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr; rw [(hmeta r hr).2.2] at hng
      exact entails_of_mem_or_false (hw.arena.entails r hr hng) fun l hl =>
        Or.inl ((hmem_all r hr l).mpr hl)
  refine ⟨hrefs, hmeta, hlits_other, { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne; dsimp only [k'] at hrs ⊢
      by_cases hb : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        exact ⟨hrefs ▸ hrs.1, (hmeta _ hrs.1).2.2.trans hrs.2.1,
          fun q hq => hrs.2.2 q ((hmem_all _ hrs.1 q).mp hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hb : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      exact (hmem_all _ hrs.1 _).mpr (hw.reason_lit_mem idx hidx hne hlg) }⟩

theorem setHdrKeepGarbShrk_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur k) {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    {v : BitVec 32}
    (hgarb : (v &&& 0x00080000#32) = (fullArenaHdrCore k cref &&& 0x00080000#32))
    (hshrk : (v &&& 0x00800000#32) = (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let k' := { k with arena := k.arena.set cref v }
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) ∧
    FullWitnessInv c F0 F_cur k' := by
  intro k'
  have hwf := hw.arena.refs_wf cref href
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have ha_cref : k'.arena[cref]? = some v := List.getElem?_set_self har_len
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧ fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff k.arena k.arena_len cref ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : k'.arena[cref + 2]? = k.arena[cref + 2]? := List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some,
        hshrk, show fullArenaHdrCore k cref = k.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i _ _
        rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (hw.arena.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hcl_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr => by
    have hrwf := hw.arena.refs_wf r hr
    have hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst r
      have hsz : fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref := by
        unfold fullArenaClauseSizeCore k'; rw [List.getElem?_set_ne (by omega)]
      refine ⟨hsz, by
          unfold fullArenaClauseGarbCore fullArenaHdrCore
          rw [ha_cref, Option.getD_some, hgarb]; rfl,
        fullArenaClauseLitsCore_eq_of_hold hbd (by simp [k', hbd]) hsz fun j _ =>
          List.getElem?_set_ne (by omega)⟩
    · have hout : r + 3 + fullArenaClauseSizeCore k r ≤ cref ∨ cref + 3 ≤ r := by
        rcases hne_out r hr hrc with ⟨h1, _⟩ | ⟨h3, h2⟩ <;> omega
      have hls := fullArenaClauseLitsCore_set_outside (v := v) hbd hout
      exact ⟨hls.1,
        by unfold fullArenaClauseGarbCore fullArenaHdrCore k'
           rw [List.getElem?_set_ne (Ne.symm hrc)],
        hls.2⟩
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have h := hw.arena.refs_wf r hr
      dsimp only [k'] at hnxt ⊢; rw [hnxt r hr, (hcl_eq r hr).1]; exact h
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢; rwa [ha_cref, Option.getD_some, hshrk] at hsh
        · unfold fullArenaHdrCore at hsh ⊢; simpa [k', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have : r < k.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ := fullArenaNextOff_hits_sentinel
        (hw.arena.refs_wf r hr).1 (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; omega
        · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
          · omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      have hnxt_le := (hw.arena.refs_wf r hr).2.2.2.1
      exact ⟨t0, by rw [(hcl_eq r hr).1]; exact ht0_lo, by dsimp only [k']; omega,
        by dsimp only [k']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent⟩
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hcl_eq r hr).2.1] at hng; rw [(hcl_eq r hr).2.2] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hcl_eq r hr).2.1] at hng; rw [(hcl_eq r hr).2.2]; exact hw.arena.entails r hr hng
  refine ⟨hrefs, hcl_eq, { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne; dsimp only [k'] at hrs ⊢
      by_cases hb : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        have hc := hcl_eq _ hrs.1
        exact ⟨hrefs ▸ hrs.1, hc.2.1.trans hrs.2.1, fun q hq => hrs.2.2 q (hc.2.2 ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hb : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      exact (hcl_eq _ hrs.1).2.2 ▸ hw.reason_lit_mem idx hidx hne hlg }⟩

theorem markGarb_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k) (ag' : BitVec 64)
    (hnonact : ∀ idx < k.trail_end,
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let k' := { k with arena := k.arena.set cref (fullArenaHdrCore k cref ||| 0x00080000#32),
                       arena_garbage := ag' }
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧ FullWitnessInv c F0 F_cur k' := by
  intro k'
  have hmg := hw.arena.markGarb hlen href ag'; have hrefs := hmg.1
  have hdisj_lits : ∀ {r : Nat}, r ∈ fullArenaClauseRefsCore k → r ≠ cref →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun {r} hr hne => by
    have hdisj : r + 3 + fullArenaClauseSizeCore k r ≤ cref ∨ cref + 3 ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (hw.arena.disjoint hr href hlt)
      · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
    have hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    exact (fullArenaClauseLitsCore_set_outside hbd hdisj).2
  refine ⟨hrefs, { hw with
    arena := hmg.2
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne; dsimp only [k'] at hrs ⊢
      by_cases hb : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · have hlg' := Classical.byContradiction fun hn => hb hn
        rw [ite_eq_right hb] at hrs ⊢
        have hne_c := hnonact idx hidx hne hlg'
        have hgarb' : fullArenaClauseGarbCore k'
            (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = false := by
          unfold fullArenaClauseGarbCore fullArenaHdrCore k'
          rw [List.getElem?_set_ne hne_c.symm]; exact hrs.2.1
        exact ⟨hrefs ▸ hrs.1, hgarb', fun q hq => hrs.2.2 q (hdisj_lits hrs.1 hne_c ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hb : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs; exact hdisj_lits hrs.1 (hnonact idx hidx hne hlg) ▸
        hw.reason_lit_mem idx hidx hne hlg }⟩

/-! ## 2. Literal Swap & Level-0 Assignment Witness Preservation -/

private theorem list_set_swap_perm_lt {α : Type} (xs : List α) {a b : Nat}
    (hlt : a < b) (hb : b < xs.length) :
    List.Perm ((xs.set a (xs[b]'hb)).set b (xs[a]'(by omega))) xs := by
  have hsplit : ∀ (ys : List α) (x y : α),
      ys[a]? = some x → ys[b]? = some y → ys.length = xs.length →
      (∀ j, j < xs.length → j ≠ a → j ≠ b → ys[j]? = xs[j]?) →
      ys = xs.take a ++ (x :: ((xs.drop (a + 1)).take (b - a - 1) ++ [y])) ++
        xs.drop (b + 1) := by
    intro ys x y hxa hyb hlen hoth
    have hpre_len : (xs.take a).length = a := by simp; omega
    have hmid_len : ((xs.drop (a + 1)).take (b - a - 1)).length = b - a - 1 := by simp; omega
    have hsuf_len : (xs.drop (b + 1)).length = xs.length - (b + 1) := by simp
    have hlhs_len : (xs.take a ++ (x :: ((xs.drop (a + 1)).take (b - a - 1) ++ [y]))).length =
        b + 1 := by
      simp [hpre_len, hmid_len]; omega
    have htot_len : (xs.take a ++ (x :: ((xs.drop (a + 1)).take (b - a - 1) ++ [y])) ++
        xs.drop (b + 1)).length = xs.length := by
      rw [List.length_append, hlhs_len, hsuf_len]; omega
    have hcons : ∀ (z : α) (zs : List α) {k : Nat}, k ≠ 0 → (z :: zs)[k]? = zs[k - 1]? := by
      intro z zs k hk; cases k with | zero => exact absurd rfl hk | succ n => rfl
    have htake : ∀ (zs : List α) (n i : Nat), i < n → (zs.take n)[i]? = zs[i]? := by
      intro zs n i hi; simp [hi]
    refine List.ext_getElem? fun j => ?_
    by_cases hlt_len : xs.length ≤ j
    · rw [List.getElem?_eq_none (by rw [hlen]; exact hlt_len),
        List.getElem?_eq_none (by rw [htot_len]; exact hlt_len)]
    · have hjx : j < xs.length := Nat.lt_of_not_le hlt_len
      by_cases h1 : j < a
      · rw [List.getElem?_append_left (by rw [hlhs_len]; omega),
          List.getElem?_append_left (by rw [hpre_len]; exact h1),
          htake _ _ _ h1, ← hoth j hjx (by omega) (by omega)]
      · by_cases h2 : j = a
        · subst j; rw [List.getElem?_append_left (by rw [hlhs_len]; omega),
            List.getElem?_append_right (by rw [hpre_len]; exact Nat.le_refl _),
            hpre_len, Nat.sub_self, List.getElem?_cons_zero, hxa]
        · by_cases h3 : j < b
          · rw [List.getElem?_append_left (by rw [hlhs_len]; omega),
              List.getElem?_append_right (by rw [hpre_len]; omega),
              hpre_len, hcons _ _ (by omega),
              List.getElem?_append_left (by rw [hmid_len]; omega),
              htake _ _ _ (by omega), List.getElem?_drop,
              show a + 1 + (j - a - 1) = j by omega, ← hoth j hjx h2 (by omega)]
          · by_cases h4 : j = b
            · subst j
              rw [List.getElem?_append_left (by rw [hlhs_len]; omega),
                List.getElem?_append_right (by rw [hpre_len]; omega),
                hpre_len, hcons _ _ (by omega),
                List.getElem?_append_right (by rw [hmid_len]; exact Nat.le_refl _),
                hmid_len, Nat.sub_self, List.getElem?_cons_zero, hyb]
            · rw [List.getElem?_append_right (by rw [hlhs_len]; omega),
                hlhs_len, List.getElem?_drop, show b + 1 + (j - (b + 1)) = j by omega,
                ← hoth j hjx h2 h4]
  have hxs := hsplit xs (xs[a]'(by omega)) (xs[b]'hb)
    (by rw [List.getElem?_eq_getElem (by omega)])
    (by rw [List.getElem?_eq_getElem hb]) rfl (fun _ _ _ _ => rfl)
  have hsw := hsplit ((xs.set a (xs[b]'hb)).set b (xs[a]'(by omega))) (xs[b]'hb)
    (xs[a]'(by omega))
    (by rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)])
    (by rw [List.getElem?_set_self (by simp; omega)]) (by simp)
    (fun j _ hja hjb => by
      rw [List.getElem?_set_ne (Ne.symm hjb), List.getElem?_set_ne (Ne.symm hja)])
  let pre := xs.take a
  let mid := (xs.drop (a + 1)).take (b - a - 1)
  let suf := xs.drop (b + 1)
  have h1 : List.Perm (mid ++ [xs[a]'(by omega)]) (xs[a]'(by omega) :: mid) := by simp
  have h2 : List.Perm (xs[b]'hb :: mid) (mid ++ [xs[b]'hb]) := by
    simpa using (List.perm_middle (l₁ := mid) (l₂ := []) (a := xs[b]'hb)).symm
  have hp : List.Perm (pre ++ (xs[b]'hb :: (mid ++ [xs[a]'(by omega)])) ++ suf)
      (pre ++ (xs[a]'(by omega) :: (mid ++ [xs[b]'hb])) ++ suf) :=
    (((h1.cons _).trans ((List.Perm.swap _ _ mid).trans (h2.cons _))).append_left pre).append_right
      suf
  exact (List.Perm.of_eq hsw).trans (hp.trans (List.Perm.of_eq hxs.symm))

private theorem list_set_swap_perm {α : Type} (xs : List α) {a b : Nat}
    (ha : a < xs.length) (hb : b < xs.length) :
    List.Perm ((xs.set a (xs[b]'hb)).set b (xs[a]'ha)) xs := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact list_set_swap_perm_lt xs hlt hb
  · rw [show (xs.set a (xs[a]'ha)).set a (xs[a]'ha) = xs from List.ext_getElem (by simp)
      fun j _ _ => by
        by_cases hj : j = a
        · subst hj; simp
        · rw [List.getElem_set_ne (Ne.symm hj), List.getElem_set_ne (Ne.symm hj)]]
  · rw [show (xs.set a (xs[b]'hb)).set b (xs[a]'ha) =
        (xs.set b (xs[a]'ha)).set a (xs[b]'hb) from List.ext_getElem (by simp) fun j _ _ => by
      by_cases hjb : j = b
      · subst hjb; rw [List.getElem_set_self (by simp; omega), List.getElem_set_ne (by omega),
          List.getElem_set_self (by simp; omega)]
      · by_cases hja : j = a
        · subst hja
          rw [List.getElem_set_ne (Ne.symm hjb), List.getElem_set_self (by simp; omega),
            List.getElem_set_self (by simp; omega)]
        · rw [List.getElem_set_ne (Ne.symm hjb), List.getElem_set_ne (Ne.symm hja),
            List.getElem_set_ne (Ne.symm hja), List.getElem_set_ne (Ne.symm hjb)]]
    exact list_set_swap_perm_lt xs hgt ha

theorem swapClauseLits_perm {ar : List (BitVec 32)} {p sz a b : Nat}
    (ha : a < sz) (hb : b < sz) (hbd : p + 3 + sz ≤ ar.length) :
    let pa := p + 3 + a; let pb := p + 3 + b
    let ar' := (ar.set pa (ar[pb]'(by omega))).set pb (ar[pa]'(by omega))
    List.Perm (((ar'.drop (p + 3)).take sz).map BitVec.toNat)
      (((ar.drop (p + 3)).take sz).map BitVec.toNat) := by
  intro pa pb ar'
  have hlen1 : ((ar.drop (p + 3)).take sz).length = sz := by simp; omega
  have h1 : (ar'.drop (p + 3)).take sz =
      (((ar.drop (p + 3)).take sz).set a (((ar.drop (p + 3)).take sz)[b]'(by omega))).set b
        (((ar.drop (p + 3)).take sz)[a]'(by omega)) := by
    refine List.ext_getElem (by simp [ar']) fun j hj1 _ => ?_
    have hjsz : j < sz := by simp [ar'] at hj1; omega
    simp only [List.getElem_take, List.getElem_drop, ar', pa, pb]
    by_cases hjb : j = b
    · subst hjb; rw [List.getElem_set_self (by simp; omega), List.getElem_set_self (by simp; omega)]
    · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hjb)]
      by_cases hja : j = a
      · subst hja
        rw [List.getElem_set_self (by simp; omega), List.getElem_set_self (by simp; omega)]
      · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hja)]
        simp only [List.getElem_take, List.getElem_drop]
  rw [h1]
  exact (list_set_swap_perm ((ar.drop (p + 3)).take sz) (by omega) (by omega)).map BitVec.toNat

theorem level0Assign_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0) {lit : BitVec 32}
    (hlit : lit.toNat < 2 * k.cur_vars) (hun : k.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (flags' : List (BitVec 32)) (unass' unfl' : BitVec 64) :
    let v := lit.toNat / 2
    let k' : FullCoreState :=
      { k with
        vals := (k.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v 0#32, rsns := k.rsns.set v 0xFFFFFFFF#32
        trl := k.trl.set k.trail_end lit
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unass', unflushed := unfl' }
    FullWitnessInv c F0 F_cur k' := by
  intro v k'
  have hte_lt : k.trail_end < k.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * k.cur_vars := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hlen.cur_vars_le; omega
  have hte_max : k.trail_end < c.max_vars := by have := hlen.cur_vars_le; omega
  have hte_lt32 : k.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < k.trail_end + 1,
      (k'.trl[i]?.getD 0#32).toNat =
        if i = k.trail_end then lit.toNat else (k.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = k.trail_end
    · subst he; simp [k', List.getElem?_set_self (by rw [hlen.trl_len]; exact hte_max)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_zero : ∀ i < k.trail_end + 1,
      (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := fun i hi => by
    rw [htrl_get i hi]; by_cases hie : i = k.trail_end
    · subst hie; simp only [↓reduceIte]; dsimp only [k', v]
      rw [List.getElem?_set_self (by rw [hlen.lvl_len]; exact hv_lt)]; rfl
    · have hilt : i < k.trail_end := by omega
      simp only [hie, ↓reduceIte]; dsimp only [k']
      rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
      have := hw.lvl_le i hilt; omega
  have hrsn_all : ∀ i < k.trail_end + 1,
      k'.rsns[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun i hi => by
      rw [htrl_get i hi]; by_cases hie : i = k.trail_end
      · subst hie; simp only [↓reduceIte]; dsimp only [k', v]
        rw [List.getElem?_set_self (by rw [hlen.rsns_len]; exact hv_lt)]; rfl
      · have hilt : i < k.trail_end := by omega
        simp only [hie, ↓reduceIte]; dsimp only [k']
        rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
        exact hw.level0_rsn_none i hilt (by have := hw.lvl_le i hilt; omega)
  have hvals_get : ∀ l < 2 * k.cur_vars,
      k'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else k.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hlen.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [k']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hlen.vals_len]; omega)]; rfl
    · dsimp only [k']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hlen.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  refine {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := by dsimp [k']; omega
    trail_lits_lt := fun i hi => by
      rw [htrl_get i hi]; split
      · exact hlit
      · exact hw.trail_lits_lt i (by dsimp [k'] at hi; omega)
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp only [k'] at hi hj
      rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      rw [hvals_get l hl]; split; · exact Or.inr (Or.inr rfl)
      split; · exact Or.inr (Or.inl rfl)
      exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp only [k']; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨k.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ k.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = k.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp only [k']; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨k.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ k.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = k.trail_end
        · simp only [hie, ↓reduceIte] at heq
          have hl_eq : l = lit.toNat ^^^ 1 := by
            have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
            rw [h1] at h; exact h.symm
          simp [hl_eq]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by
            have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
    lvl_le := fun i hi => by rw [hlvl_zero i hi]; omega
    dec_earliest := fun _ j _ hj _ hdec => by rw [hlvl_zero j hj] at hdec; omega
    levels_inhabited := fun _ hL1 hLle => by dsimp [k'] at hLle; omega
    level0_sound := fun i hi _ => by
      dsimp only [k'] at hi; rw [htrl_get i hi]
      by_cases hie : i = k.trail_end
      · simp only [hie, ↓reduceIte]; exact hent
      · simp only [hie, ↓reduceIte]
        exact hw.level0_sound i (by omega) (by have := hw.lvl_le i (by omega); omega)
    trail_pos_inv := fun i hi => by
      dsimp only [k'] at hi; rw [htrl_get i hi]
      by_cases hie : i = k.trail_end
      · subst hie; simp only [↓reduceIte]; dsimp only [k', v]
        rw [List.getElem?_set_self (by rw [hlen.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat hte_lt32]
      · simp only [hie, ↓reduceIte]; dsimp only [k']
        rw [List.getElem?_set_ne (Ne.symm (hnot_var i (by omega)))]
        exact hw.trail_pos_inv i (by omega)
    level0_rsn_none := fun idx hidx _ => hrsn_all idx hidx
    frame_trail_lt := fun L hL => by
      have := hw.frame_trail_lt L hL; dsimp only [k']; omega
    frame_trail_mono := fun L1 L2 h1 h2 => hw.frame_trail_mono L1 L2 h1 h2
    frame_trail_before_lt := fun _ hL1 hLle => by dsimp [k'] at hLle; omega
    frame_dec_lt := fun _ hL1 hLle => by dsimp [k'] at hLle; omega
    reason_inv := fun idx hidx hne => absurd (hrsn_all idx hidx) hne
    reason_lit_mem := fun idx hidx hne => absurd (hrsn_all idx hidx) hne }

theorem level0_entails_of_filter {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {orig kept : List Nat}
    (horig : (cnfOfClauses F_cur).EntailsClause (cnfClause orig))
    (hdrop : ∀ l ∈ orig, l ∈ kept ∨
      (l < 2 * k.cur_vars ∧ (k.lvl[l / 2]?.getD 0#32).toNat = 0 ∧ k.vals[l]?.getD 0#8 = 0xFF#8)) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause kept) := by
  refine entails_of_mem_or_false horig fun l hl => ?_
  rcases hdrop l hl with hin | ⟨hlt, hl0, hff⟩
  · exact Or.inl hin
  · right; obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hlt).mp hff
    have hvar : (k.trl[i]?.getD 0#32).toNat / 2 = l / 2 := by rw [hieq]; exact fullInv_var_xor1 l
    have hs := hw.level0_sound i hi (by rw [hvar]; exact hl0); rwa [hieq] at hs

theorem level0_unsat_of_entails_nil {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hnil : (cnfOfClauses F_cur).EntailsClause (cnfClause [])) : F0.Unsat :=
  hw.ext_sound.2 (unsat_of_entails_nil hnil)

theorem level0_unsat_of_unit_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (_hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l]))
    (hff : k.vals[l]?.getD 0#8 = 0xFF#8) : F0.Unsat := by
  refine level0_unsat_of_entails_nil hw (level0_entails_of_filter hw hent fun q hq => Or.inr ?_)
  simp only [List.mem_singleton] at hq; subst hq
  obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff q hlt).mp hff
  have hvar : (k.trl[i]?.getD 0#32).toNat / 2 = q / 2 := by rw [hieq]; exact fullInv_var_xor1 q
  exact ⟨hlt, by have := hw.lvl_le i hi; rw [hvar] at this; omega, hff⟩

/-! ## 3. Arena Compaction, Reason Uniqueness & `SweepReasonMapInv` -/

theorem fullWitness_reason_unique {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {i1 i2 src : Nat}
    (hi1 : i1 < k.trail_end) (hi2 : i2 < k.trail_end) (hsrc_lt : src < 0x80000000)
    (hr1 : k.rsns[(k.trl[i1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src)
    (hr2 : k.rsns[(k.trl[i2]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src) :
    i1 = i2 := by
  have hne : BitVec.ofNat 32 src ≠ 0xFFFFFFFF#32 := fun h => by
    have := congrArg BitVec.toNat h; rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
  have hlg : (BitVec.ofNat 32 src &&& 0x80000000#32) = 0#32 :=
    (bv32_lt_highbit_iff _).mp (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt)
  have hgo : ∀ a b, a < k.trail_end → b < k.trail_end → a < b →
      k.rsns[(k.trl[a]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src →
      k.rsns[(k.trl[b]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src →
      False := fun a b ha hb hab hra hrb => by
    have hri := hw.reason_inv a ha (by rw [hra]; exact hne)
    rw [hra, ite_eq_right (fun h => h hlg)] at hri
    have hmem := hw.reason_lit_mem b hb (by rw [hrb]; exact hne) (by rw [hrb]; exact hlg)
    rw [hrb] at hmem
    rcases hri.2.2 _ hmem with heq | ⟨m, hm, hmeq, _⟩
    · have := hw.trail_vars_nodup b a hb ha (by rw [heq]); omega
    · have := hw.trail_vars_nodup m b (by omega) hb (by rw [hmeq, fullInv_var_xor1]); omega
  rcases lt_trichotomy i1 i2 with h | rfl | h
  · exact False.elim (hgo i1 i2 hi1 hi2 h hr1 hr2)
  · rfl
  · exact False.elim (hgo i2 i1 hi2 hi1 h hr2 hr1)

theorem compactArena_append_block {c : FullCfg} {F_cur : List (List Nat)} {k k' : FullCoreState}
    {dst new_sz : Nat}
    (ha : FullArenaClausesInv c F_cur { k with arena_len := dst })
    (hno_old : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      (fullArenaHdrCore k r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarbCore k r = false)
    (hcv : k'.cur_vars = k.cur_vars) (hge3 : 3 ≤ new_sz)
    (hlen_ar : k.arena.length = c.arena_cap) (hlen_ar' : k'.arena.length = c.arena_cap)
    (hdst_le : dst + 3 + new_sz ≤ c.arena_cap) (hhold : PrefixAgrees dst k.arena k'.arena)
    (hnoshrk : (k'.arena[dst]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnogarb : (k'.arena[dst]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsz : (k'.arena[dst + 2]?.getD 0#32).toNat = new_sz)
    (hlits_lt : ∀ j < new_sz, (k'.arena[dst + 3 + j]?.getD 0#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((k'.arena.drop (dst + 3)).take new_sz).map BitVec.toNat))) :
    let kn := { k' with arena_len := dst + 3 + new_sz }
    fullArenaClauseRefsCore kn = fullArenaClauseRefsCore { k with arena_len := dst } ++ [dst] ∧
    FullArenaClausesInv c F_cur kn ∧
    (∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      fullArenaClauseSizeCore kn r = fullArenaClauseSizeCore { k with arena_len := dst } r ∧
      fullArenaClauseGarbCore kn r = fullArenaClauseGarbCore { k with arena_len := dst } r ∧
      fullArenaClauseLitsCore kn r = fullArenaClauseLitsCore { k with arena_len := dst } r) ∧
    (∀ r ∈ fullArenaClauseRefsCore kn,
      (fullArenaHdrCore kn r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarbCore kn r = false) := by
  intro kn
  have hnxt_hold := ha.arenaNextOff_extend (arena' := k'.arena) (alen' := dst + 3 + new_sz)
    (by dsimp; omega) (fun i hi => hhold i hi)
  have hrefs : fullArenaClauseRefsCore kn =
      fullArenaClauseRefsCore { k with arena_len := dst } ++ [dst] :=
    fullArenaClauseRefsCore_append (k := { k with arena_len := dst }) (k' := kn) ha hge3 rfl
      (fun i hi => hhold i hi) hnoshrk hsz
  have hold_cl : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      fullArenaClauseSizeCore kn r = fullArenaClauseSizeCore { k with arena_len := dst } r ∧
      fullArenaClauseGarbCore kn r = fullArenaClauseGarbCore { k with arena_len := dst } r ∧
      fullArenaClauseLitsCore kn r = fullArenaClauseLitsCore { k with arena_len := dst } r :=
    fun r hr => by
      have hwf := ha.refs_wf r hr; dsimp at hwf
      have hszr : fullArenaClauseSizeCore kn r =
          fullArenaClauseSizeCore { k with arena_len := dst } r := by
        unfold fullArenaClauseSizeCore kn; simp [hhold (r + 2) (by omega)]
      refine ⟨hszr,
        by unfold fullArenaClauseGarbCore fullArenaHdrCore kn; simp [hhold r (by omega)],
        fullArenaClauseLitsCore_eq_of_hold (by dsimp; omega) (by dsimp [kn]; omega) hszr
          fun j hj => hhold (r + 3 + j) (by omega)⟩
  have hno_new : ∀ r ∈ fullArenaClauseRefsCore kn,
      (fullArenaHdrCore kn r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarbCore kn r = false := by
    intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · have hr3 := (ha.refs_wf r hr).1; dsimp at hr3
      have h0 := hhold r (by omega); have ho := hno_old r hr
      exact ⟨by unfold fullArenaHdrCore kn; rw [h0]; exact ho.1,
        by unfold fullArenaClauseGarbCore fullArenaHdrCore kn; rw [h0]; exact ho.2⟩
    · exact ⟨hnoshrk, by unfold fullArenaClauseGarbCore fullArenaHdrCore kn; simp [hnogarb]⟩
  have hnew_lits_lt : ∀ l ∈ fullArenaClauseLitsCore kn dst, l < 2 * kn.cur_vars := by
    intro l hl
    have hbd : dst + 3 + fullArenaClauseSizeCore kn dst ≤ kn.arena.length := by
      rw [show fullArenaClauseSizeCore kn dst = new_sz from hsz]; dsimp [kn]; omega
    obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl
    rw [show fullArenaClauseSizeCore kn dst = new_sz from hsz] at hj
    have hj_lt : dst + 3 + j < k'.arena.length := by omega
    have := hlits_lt j hj
    rw [List.getElem?_eq_getElem hj_lt, Option.getD_some] at this; dsimp [kn]; omega
  have ha' : FullArenaClausesInv c F_cur kn := by
    refine ⟨Or.inr (by dsimp [kn]; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr_dst
      · have hwf := ha.refs_wf r hr; dsimp at hwf
        rw [hnxt_hold r hr, (hold_cl r hr).1]
        exact ⟨by dsimp [kn]; omega, hwf.2.1, hwf.2.2.1, by dsimp [kn]; omega, Or.inr (by
          rcases hwf.2.2.2.2 with he | h3 <;> dsimp [kn] <;> omega)⟩
      · subst r
        have hnxt_d : fullArenaNextOff kn.arena kn.arena_len dst = dst + 3 + new_sz := by
          unfold fullArenaNextOff kn
          simp only [show ¬ (dst + 3 > dst + 3 + new_sz) by omega, ↓reduceIte, hsz,
            show ¬ (dst + 3 + new_sz > dst + 3 + new_sz) by omega, hnoshrk, ne_eq,
            not_true_eq_false]
        rw [hnxt_d, show fullArenaClauseSizeCore kn dst = new_sz from hsz]
        exact ⟨by dsimp [kn]; omega, hge3, by omega, by dsimp [kn]; omega, Or.inl (by dsimp [kn])⟩
    · intro r hr hsh; exact absurd (hno_new r hr).1 hsh
    · intro r hr hng l hl; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr_dst
      · rw [(hold_cl r hr).2.1] at hng; rw [(hold_cl r hr).2.2] at hl
        have := ha.lits_lt r hr hng l hl; dsimp [kn] at this ⊢; omega
      · subst r; exact hnew_lits_lt l hl
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr_dst
      · rw [(hold_cl r hr).2.1] at hng; rw [(hold_cl r hr).2.2]; exact ha.entails r hr hng
      · subst r; unfold fullArenaClauseLitsCore
        rw [show fullArenaClauseSizeCore kn dst = new_sz from hsz]; exact hent
  exact ⟨hrefs, ha', hold_cl, hno_new⟩

theorem fullArenaClausesInv_zero {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState} :
    FullArenaClausesInv c F_cur { k with arena_len := 0 } := by
  have hrefs : fullArenaClauseRefsCore { k with arena_len := 0 } = [] := by
    simp [fullArenaClauseRefsCore, fullArenaScanRefs]
  exact ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
    fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩

theorem fullWitnessInv_arena_len_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hbin : BinOnlyWatchesInv F_cur k)
    (_hcl0 : k.cur_level = 0) : FullWitnessInv c F0 F_cur { k with arena_len := 0 } :=
  { hw with
    arena := fullArenaClausesInv_zero
    watches := (hbin.with_core (k' := { k with arena_len := 0 }) rfl rfl rfl rfl).toModeWatchesInv
    reason_inv := fun i hi h =>
      absurd (hw.level0_rsn_none i hi (by have := hw.lvl_le i hi; omega)) h
    reason_lit_mem := fun i hi h =>
      absurd (hw.level0_rsn_none i hi (by have := hw.lvl_le i hi; omega)) h }

theorem fullWitnessInv_append_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {ar' : List (BitVec 32)} {dst new_sz : Nat}
    (hw : FullWitnessInv c F0 F_cur { k with arena_len := dst })
    (hbin : BinOnlyWatchesInv F_cur k) (_hcl0 : k.cur_level = 0)
    (ha' : FullArenaClausesInv c F_cur
      { { k with arena := ar' } with arena_len := dst + 3 + new_sz }) :
    FullWitnessInv c F0 F_cur { { k with arena := ar' } with arena_len := dst + 3 + new_sz } :=
  { hw with
    arena := ha'
    watches := (hbin.with_core
      (k' := { { k with arena := ar' } with arena_len := dst + 3 + new_sz })
      rfl rfl rfl rfl).toModeWatchesInv
    reason_inv := fun i hi h => absurd (hw.level0_rsn_none i hi (by
      have := hw.lvl_le i hi
      change (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level at this
      change (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0; omega)) h
    reason_lit_mem := fun i hi h => absurd (hw.level0_rsn_none i hi (by
      have := hw.lvl_le i hi
      change (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level at this
      change (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0; omega)) h }

/-- Non-root (`0 < cur_level`) reason-remapping invariant across arena compaction. -/
@[expose] def SweepReasonMapInv (k0 kL : FullCoreState) (src dst : Nat) : Prop :=
  ∀ idx < k0.trail_end,
    let v := (k0.trl[idx]?.getD 0#32).toNat / 2
    let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
    let rL := kL.rsns[v]?.getD 0xFFFFFFFF#32
    if r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 then rL = r0
    else if r0.toNat < src then
      rL.toNat < dst ∧ rL.toNat < 0x80000000 ∧ rL ≠ 0xFFFFFFFF#32 ∧
      (rL &&& 0x80000000#32) = 0#32 ∧
      rL.toNat ∈ fullArenaClauseRefsCore { kL with arena_len := dst } ∧
      fullArenaClauseGarbCore { kL with arena_len := dst } rL.toNat = false ∧
      fullArenaClauseLitsCore { kL with arena_len := dst } rL.toNat =
        fullArenaClauseLitsCore k0 r0.toNat
    else rL = r0

theorem SweepReasonMapInv.init {k0 : FullCoreState} : SweepReasonMapInv k0 k0 0 0 := by
  intro idx _; dsimp only; split; · rfl
  · split; · omega
    · rfl

theorem SweepReasonMapInv.skip {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k0 kL : FullCoreState} {src nsrc dst : Nat}
    (hw0 : FullWitnessInv c F0 F_cur k0) (hsrc_ref : src ∈ fullArenaClauseRefsCore k0)
    (hnsrc : nsrc = fullArenaNextOff k0.arena k0.arena_len src)
    (hskip : fullArenaClauseGarbCore k0 src = true ∨ fullArenaClauseSizeCore k0 src < 3 ∨
      k0.arena_len < src + 3 + fullArenaClauseSizeCore k0 src)
    (hrm : SweepReasonMapInv k0 kL src dst) : SweepReasonMapInv k0 kL nsrc dst := by
  intro idx hidx; have h := hrm idx hidx; dsimp only at h ⊢
  let v := (k0.trl[idx]?.getD 0#32).toNat / 2; let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
  change (if r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 then _ else _) at h ⊢
  split at h
  · rename_i hc1; simp only [hc1, ↓reduceIte]; exact h
  · rename_i hc1; simp only [hc1, ↓reduceIte]
    have hne : r0 ≠ 0xFFFFFFFF#32 := fun he => hc1 (Or.inl he)
    have hlg : (r0 &&& 0x80000000#32) = 0#32 :=
      Classical.byContradiction fun h0 => hc1 (Or.inr h0)
    have hri := hw0.reason_inv idx hidx hne; rw [ite_eq_right (fun h0 => h0 hlg)] at hri
    have hwf := hw0.arena.refs_wf r0.toNat hri.1
    split at h
    · have hb := fullArenaNextOff_bounds (ar := k0.arena) (hw0.arena.refs_wf src hsrc_ref).1
      split; · exact h
      · dsimp only [r0, v] at *; omega
    · rename_i hge
      have hne_src : r0.toNat ≠ src := fun heq => by
        rw [heq] at hri hwf; rcases hskip with hg | h3 | hgt
        · rw [hri.2.1] at hg; cases hg
        · have := hwf.2.1; omega
        · have := hwf.2.2.1; have := hwf.2.2.2.1; omega
      have hdisj := fullArenaScanRefs_disjoint hsrc_ref hri.1
        (by change ¬ r0.toNat < src at hge; dsimp only [r0, v] at *; omega)
      split; · dsimp only [r0, v] at *; omega
      · exact h

theorem SweepReasonMapInv.keep_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k0 kL : FullCoreState} {ar' rsns' : List (BitVec 32)} {src nsrc dst new_sz : Nat}
    (hw0 : FullWitnessInv c F0 F_cur k0) (hsrc_ref : src ∈ fullArenaClauseRefsCore k0)
    (hnsrc : nsrc = fullArenaNextOff k0.arena k0.arena_len src)
    (hdst_le_src : dst ≤ src) (hsrc_lt8 : src < 0x80000000)
    (hrm : SweepReasonMapInv k0 kL src dst)
    (happend :
      let kn : FullCoreState :=
        { kL with arena := ar', rsns := rsns', arena_len := dst + 3 + new_sz }
      fullArenaClauseRefsCore kn = fullArenaClauseRefsCore { kL with arena_len := dst } ++ [dst] ∧
      (∀ r ∈ fullArenaClauseRefsCore { kL with arena_len := dst },
        fullArenaClauseGarbCore kn r = fullArenaClauseGarbCore { kL with arena_len := dst } r ∧
        fullArenaClauseLitsCore kn r = fullArenaClauseLitsCore { kL with arena_len := dst } r) ∧
      fullArenaClauseGarbCore kn dst = false ∧
      fullArenaClauseLitsCore kn dst = fullArenaClauseLitsCore k0 src)
    (hrsns_other : ∀ idx < k0.trail_end,
      k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ BitVec.ofNat 32 src →
      rsns'[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        kL.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (hrsns_src : ∀ idx < k0.trail_end,
      k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src →
      rsns'[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 dst) :
    SweepReasonMapInv k0 { kL with arena := ar', rsns := rsns' } nsrc (dst + 3 + new_sz) := by
  intro idx hidx; have h := hrm idx hidx; dsimp only at h ⊢
  let v := (k0.trl[idx]?.getD 0#32).toNat / 2; let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
  have hr_oth : r0 ≠ BitVec.ofNat 32 src →
      rsns'[v]?.getD 0xFFFFFFFF#32 = kL.rsns[v]?.getD 0xFFFFFFFF#32 := hrsns_other idx hidx
  have hr_eq : r0 = BitVec.ofNat 32 src →
      rsns'[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 dst := hrsns_src idx hidx
  change (if r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 then _ else _) at h ⊢
  split at h
  · rename_i hc1; simp only [hc1, ↓reduceIte]
    have hne_s : r0 ≠ BitVec.ofNat 32 src := fun heq => by
      rcases hc1 with hff | hhi
      · rw [hff] at heq; have := congrArg BitVec.toNat heq
        rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
      · rw [heq] at hhi
        exact hhi ((bv32_lt_highbit_iff _).mp
          (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8))
    rw [hr_oth hne_s]; exact h
  · rename_i hc1; simp only [hc1, ↓reduceIte]
    have hne : r0 ≠ 0xFFFFFFFF#32 := fun he => hc1 (Or.inl he)
    have hlg : (r0 &&& 0x80000000#32) = 0#32 :=
      Classical.byContradiction fun h0 => hc1 (Or.inr h0)
    have hri := hw0.reason_inv idx hidx hne; rw [ite_eq_right (fun h0 => h0 hlg)] at hri
    have hb := fullArenaNextOff_bounds (ar := k0.arena) (hw0.arena.refs_wf src hsrc_ref).1
    split at h
    · split
      · have hne_s : r0 ≠ BitVec.ofNat 32 src := fun heq => by
          have := congrArg BitVec.toNat heq
          rw [bv32_ofNat_toNat (by omega)] at this
          dsimp only [r0, v] at *; omega
        rw [hr_oth hne_s]; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
        obtain ⟨hrefs', hhold', _, _⟩ := happend
        exact ⟨by dsimp only [v] at *; omega, h2, h3, h4,
          by rw [hrefs', List.mem_append]; exact Or.inl h5,
          (hhold' _ h5).1.trans h6, (hhold' _ h5).2.trans h7⟩
      · dsimp only [r0, v] at *; omega
    · rename_i hge
      by_cases hreq : r0.toNat = src
      · have hr_bv : r0 = BitVec.ofNat 32 src :=
          BitVec.eq_of_toNat_eq (by rw [hreq, bv32_ofNat_toNat (by omega)])
        split
        · rw [hr_eq hr_bv]
          have hdst_bv : (BitVec.ofNat 32 dst).toNat = dst := bv32_ofNat_toNat (by omega)
          have hdst_ne : BitVec.ofNat 32 dst ≠ 0xFFFFFFFF#32 := fun he => by
            have := congrArg BitVec.toNat he; rw [hdst_bv] at this; simp at this; omega
          obtain ⟨hrefs', _, hng_d, hlits_d⟩ := happend
          exact ⟨by omega, by omega, hdst_ne,
            (bv32_lt_highbit_iff _).mp (by rw [hdst_bv]; omega),
            by rw [hdst_bv, hrefs', List.mem_append, List.mem_singleton]; exact Or.inr rfl,
            by rw [hdst_bv]; exact hng_d, by rw [hdst_bv, hreq]; exact hlits_d⟩
        · dsimp only [r0, v] at *; omega
      · have hdisj := fullArenaScanRefs_disjoint hsrc_ref hri.1
          (by change ¬ r0.toNat < src at hge; dsimp only [r0, v] at *; omega)
        split; · dsimp only [r0, v] at *; omega
        · have hne_s : r0 ≠ BitVec.ofNat 32 src := fun heq => hreq (by
            have := congrArg BitVec.toNat heq; rwa [bv32_ofNat_toNat (by omega)] at this)
          rw [hr_oth hne_s]; exact h

theorem SweepReasonMapInv.congr_rsns_arena {k0 k1 k2 : FullCoreState} {nsrc ndst : Nat}
    (har : k2.arena = k1.arena) (hrs : k2.rsns = k1.rsns)
    (h : SweepReasonMapInv k0 k1 nsrc ndst) : SweepReasonMapInv k0 k2 nsrc ndst := by
  intro idx hidx; have h1 := h idx hidx; dsimp only at h1 ⊢
  unfold fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaHdrCore
    fullArenaClauseLitsCore fullArenaClauseSizeCore at h1 ⊢
  dsimp only at h1 ⊢; rw [har, hrs]; exact h1

/-- Compacted arena prefix invariant at length `dst`. -/
@[expose] def CompactPrefixOk (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (k : FullCoreState) (dst : Nat) : Prop :=
  let kCmp : FullCoreState := { k with arena_len := dst }
  FullArenaClausesInv c F_cur kCmp ∧
  (∀ r ∈ fullArenaClauseRefsCore kCmp,
    (fullArenaHdrCore kCmp r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarbCore kCmp r = false) ∧
  (FullArenaVarsNodup s →
    ∀ r ∈ fullArenaClauseRefsCore kCmp, ((fullArenaClauseLitsCore kCmp r).map (· / 2)).Nodup)

/-- Equality of clause refs, `PH_GARB`, and literal lists on `[0 ..< dst)`. -/
@[expose] def CompactPrefixCongr (k k' : FullCoreState) (dst : Nat) : Prop :=
  fullArenaClauseRefsCore { k' with arena_len := dst } =
    fullArenaClauseRefsCore { k with arena_len := dst } ∧
  (∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
    fullArenaClauseGarbCore { k' with arena_len := dst } r =
      fullArenaClauseGarbCore { k with arena_len := dst } r ∧
    fullArenaClauseLitsCore { k' with arena_len := dst } r =
      fullArenaClauseLitsCore { k with arena_len := dst } r)

theorem arenaPrefix_preserves_compact {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {k k' : FullCoreState} {dst : Nat}
    (hcmp : CompactPrefixOk c F_cur s k dst) (hcv : k'.cur_vars = k.cur_vars)
    (_hlen : k.arena.length = c.arena_cap) (_hlen' : k'.arena.length = c.arena_cap)
    (_hdst_le : dst ≤ c.arena_cap) (hpre : PrefixAgrees dst k.arena k'.arena) :
    CompactPrefixOk c F_cur s k' dst ∧ CompactPrefixCongr k k' dst := by
  obtain ⟨ha, hno, hnd⟩ := hcmp
  have hnxt := ha.arenaNextOff_extend (arena' := k'.arena) (alen' := dst) (Nat.le_refl _)
    (fun i hi => hpre i hi)
  have hrefs : fullArenaClauseRefsCore { k' with arena_len := dst } =
      fullArenaClauseRefsCore { k with arena_len := dst } :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hcl : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      fullArenaHdrCore { k' with arena_len := dst } r =
        fullArenaHdrCore { k with arena_len := dst } r ∧
      fullArenaClauseSizeCore { k' with arena_len := dst } r =
        fullArenaClauseSizeCore { k with arena_len := dst } r ∧
      fullArenaClauseGarbCore { k' with arena_len := dst } r =
        fullArenaClauseGarbCore { k with arena_len := dst } r ∧
      fullArenaClauseLitsCore { k' with arena_len := dst } r =
        fullArenaClauseLitsCore { k with arena_len := dst } r := fun r hr => by
    have hwf := ha.refs_wf r hr; dsimp at hwf
    have h0 := hpre r (by omega); have h2 := hpre (r + 2) (by omega)
    have hsz : fullArenaClauseSizeCore { k' with arena_len := dst } r =
        fullArenaClauseSizeCore { k with arena_len := dst } r := by
      unfold fullArenaClauseSizeCore; dsimp; rw [h2]
    refine ⟨by unfold fullArenaHdrCore; dsimp; rw [h0], hsz,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp; rw [h0],
      fullArenaClauseLitsCore_eq_of_hold (by dsimp; have := hwf.2.2.1; have := hwf.2.2.2.1; omega)
        (by dsimp; have := hwf.2.2.1; have := hwf.2.2.2.1; omega) hsz
        fun j hj => hpre (r + 3 + j) (by have := hwf.2.2.1; have := hwf.2.2.2.1; omega)⟩
  refine ⟨⟨⟨ha.len_ok, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩,
    hrefs, fun r hr => ⟨(hcl r hr).2.2.1, (hcl r hr).2.2.2⟩⟩
  · intro r hr; rw [hrefs] at hr; have h := ha.refs_wf r hr
    dsimp at hnxt h ⊢; rw [hnxt r hr, (hcl r hr).2.1]; exact h
  · intro r hr hsh; rw [hrefs] at hr; rw [(hcl r hr).1] at hsh; exact absurd (hno r hr).1 hsh
  · intro r hr hng l hl; rw [hrefs] at hr
    rw [(hcl r hr).2.2.1] at hng; rw [(hcl r hr).2.2.2] at hl
    have := ha.lits_lt r hr hng l hl; dsimp at this ⊢; omega
  · intro r hr hng; rw [hrefs] at hr
    rw [(hcl r hr).2.2.1] at hng; rw [(hcl r hr).2.2.2]; exact ha.entails r hr hng
  · intro r hr; rw [hrefs] at hr
    exact ⟨(hcl r hr).1.symm ▸ (hno r hr).1, (hcl r hr).2.2.1.trans (hno r hr).2⟩
  · intro hnd_s r hr; rw [hrefs] at hr; rw [(hcl r hr).2.2.2]; exact hnd hnd_s r hr

theorem CompactPrefixOk.with_rsns {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {k : FullCoreState} {arH rsnsR : List (BitVec 32)} {dst : Nat}
    (h : CompactPrefixOk c F_cur s { k with arena := arH } dst) :
    CompactPrefixOk c F_cur s { k with arena := arH, rsns := rsnsR } dst := by
  let k1 : FullCoreState := { k with arena := arH, arena_len := dst }
  let k2 : FullCoreState := { k with arena := arH, rsns := rsnsR, arena_len := dst }
  have hrefs : fullArenaClauseRefsCore k2 = fullArenaClauseRefsCore k1 :=
    fullArenaClauseRefsCore_congr rfl (fun _ _ => rfl)
  obtain ⟨ha, hno, hnd⟩ := h
  refine ⟨⟨ha.len_ok, ?_, ?_, ?_, ?_⟩, fun r hr => hno r (hrefs ▸ hr),
    fun hs r hr => hnd hs r (hrefs ▸ hr)⟩
  · intro r hr; rw [hrefs] at hr; exact ha.refs_wf r hr
  · intro r hr hsh; rw [hrefs] at hr; exact ha.shrk_term r hr hsh
  · intro r hr hng l hl; rw [hrefs] at hr; exact ha.lits_lt r hr hng l hl
  · intro r hr hng; rw [hrefs] at hr; exact ha.entails r hr hng

theorem SweepReasonMapInv.toFullWitnessInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k0 kL : FullCoreState} {dst : Nat} (hw0 : FullWitnessInv c F0 F_cur k0)
    (ha' : FullArenaClausesInv c F_cur { kL with arena_len := dst })
    (hbin : BinOnlyWatchesInv F_cur kL)
    (hvals : kL.vals = k0.vals) (hlvl : kL.lvl = k0.lvl) (htrl : kL.trl = k0.trl)
    (htp : kL.trail_pos = k0.trail_pos) (hte : kL.trail_end = k0.trail_end)
    (hcl : kL.cur_level = k0.cur_level) (hcv : kL.cur_vars = k0.cur_vars)
    (hft : kL.frame_trail = k0.frame_trail) (hfd : kL.frame_dec = k0.frame_dec)
    (hinc : kL.inconsistent = k0.inconsistent) (hrm : SweepReasonMapInv k0 kL k0.arena_len dst) :
    FullWitnessInv c F0 F_cur { kL with arena_len := dst } := by
  let kn : FullCoreState := { kL with arena_len := dst }
  have hrm_get : ∀ idx < k0.trail_end,
      let v := (k0.trl[idx]?.getD 0#32).toNat / 2
      let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32; let rL := kL.rsns[v]?.getD 0xFFFFFFFF#32
      (r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 → rL = r0) ∧
      (r0 ≠ 0xFFFFFFFF#32 → (r0 &&& 0x80000000#32) = 0#32 →
        rL.toNat < dst ∧ rL.toNat < 0x80000000 ∧ rL ≠ 0xFFFFFFFF#32 ∧
        (rL &&& 0x80000000#32) = 0#32 ∧ rL.toNat ∈ fullArenaClauseRefsCore kn ∧
        fullArenaClauseGarbCore kn rL.toNat = false ∧
        fullArenaClauseLitsCore kn rL.toNat = fullArenaClauseLitsCore k0 r0.toNat) := by
    intro idx hidx; have h := hrm idx hidx; dsimp only at h ⊢; constructor
    · intro hc1; split at h
      · exact h
      · exact absurd hc1 ‹_›
    · intro hne hlg
      have hc1 : ¬ (k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          0xFFFFFFFF#32 ∨ (k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
            0x80000000#32) ≠ 0#32) := fun hc => hc.elim hne (fun h0 => h0 hlg)
      split at h
      · exact absurd ‹_› hc1
      · have hri := hw0.reason_inv idx hidx hne; rw [ite_eq_right (fun h0 => h0 hlg)] at hri
        have hlt : (k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
            k0.arena_len := by have := (hw0.arena.refs_wf _ hri.1).1; omega
        split at h
        · exact h
        · exact absurd hlt ‹_›
  refine {
    ext_sound := by dsimp [kn]; rw [hcv]; exact hw0.ext_sound
    inconsistent_sound := by dsimp [kn]; rw [hinc]; exact hw0.inconsistent_sound
    arena := ha'
    watches := (hbin.with_core (k' := kn) rfl rfl rfl rfl).toModeWatchesInv
    cur_level_le := by dsimp [kn]; rw [hcl, hte]; exact hw0.cur_level_le
    trail_lits_lt := fun i hi => by
      dsimp [kn] at hi ⊢; rw [htrl, hcv]; exact hw0.trail_lits_lt i (hte ▸ hi)
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp [kn] at hi hj hveq; rw [htrl] at hveq
      exact hw0.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj) hveq
    vals_domain := fun l hl => by
      dsimp [kn] at hl ⊢; rw [hvals]; exact hw0.vals_domain l (hcv ▸ hl)
    vals_true_iff := fun l hl => by
      dsimp [kn] at hl ⊢; rw [hvals, hte, htrl]; exact hw0.vals_true_iff l (hcv ▸ hl)
    vals_false_iff := fun l hl => by
      dsimp [kn] at hl ⊢; rw [hvals, hte, htrl]; exact hw0.vals_false_iff l (hcv ▸ hl)
    lvl_le := fun i hi => by
      dsimp [kn] at hi ⊢; rw [hlvl, htrl, hcl]; exact hw0.lvl_le i (hte ▸ hi)
    dec_earliest := fun i j hi hj hlt hdec => by
      dsimp [kn] at hi hj hlt hdec ⊢; rw [hlvl, htrl] at hlt hdec
      have hr0_ff :
          k0.rsns[(k0.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
        obtain ⟨h1, h2⟩ := hrm_get j (hte ▸ hj)
        by_cases hc1 : k0.rsns[(k0.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
            0xFFFFFFFF#32 ∨
            (k0.rsns[(k0.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠
              0#32
        · exact (h1 hc1).symm.trans hdec.2
        · exact absurd hdec.2 (h2 (fun h => hc1 (Or.inl h))
            (Classical.byContradiction fun h0 => hc1 (Or.inr h0))).2.2.1
      exact hw0.dec_earliest i j (hte ▸ hi) (hte ▸ hj) hlt ⟨hdec.1, hr0_ff⟩
    levels_inhabited := fun L h1 h2 => by
      dsimp [kn] at h2 ⊢; rw [hte, hlvl, htrl]; exact hw0.levels_inhabited L h1 (hcl ▸ h2)
    level0_sound := fun i hi h0 => by
      dsimp [kn] at hi h0 ⊢; rw [hlvl, htrl] at h0; rw [htrl]
      exact hw0.level0_sound i (hte ▸ hi) h0
    trail_pos_inv := fun i hi => by
      dsimp [kn] at hi ⊢; rw [htp, htrl]; exact hw0.trail_pos_inv i (hte ▸ hi)
    level0_rsn_none := fun idx hidx h0 => by
      dsimp [kn] at hidx h0 ⊢; rw [hlvl, htrl] at h0; rw [htrl]
      have hr0 := hw0.level0_rsn_none idx (hte ▸ hidx) h0
      exact (hrm_get idx (hte ▸ hidx)).1 (Or.inl hr0) |>.trans hr0
    frame_trail_lt := fun L hL => by
      dsimp [kn] at hL ⊢; rw [hft, hte]; exact hw0.frame_trail_lt L (hcl ▸ hL)
    frame_trail_mono := fun L1 L2 h1 h2 => by
      dsimp [kn] at h2 ⊢; rw [hft]; exact hw0.frame_trail_mono L1 L2 h1 (hcl ▸ h2)
    frame_trail_before_lt := fun L h1 h2 i hi => by
      dsimp [kn] at h2 hi ⊢; rw [hft] at hi; rw [hlvl, htrl]
      exact hw0.frame_trail_before_lt L h1 (hcl ▸ h2) i hi
    frame_dec_lt := fun L h1 h2 => by
      dsimp [kn] at h2 ⊢; rw [hfd, hcv]; exact hw0.frame_dec_lt L h1 (hcl ▸ h2)
    reason_inv := fun idx hidx hne => by
      dsimp only [kn] at hidx hne ⊢; rw [htrl] at hne ⊢
      have hidx0 : idx < k0.trail_end := hte ▸ hidx; obtain ⟨h1, h2⟩ := hrm_get idx hidx0
      let v := (k0.trl[idx]?.getD 0#32).toNat / 2; let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
      by_cases hc1 : r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32
      · have hreq : kL.rsns[v]?.getD 0xFFFFFFFF#32 = r0 := h1 hc1
        change kL.rsns[v]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 at hne; rw [hreq] at hne
        have hri := hw0.reason_inv idx hidx0 hne
        rcases hc1 with hff | hhi
        · exact absurd hff hne
        · rw [ite_eq_left hhi] at hri
          change if (kL.rsns[v]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
          rw [hreq, ite_eq_left hhi, hcv, hlvl]; exact hri
      · have hne0 : r0 ≠ 0xFFFFFFFF#32 := fun h => hc1 (Or.inl h)
        have hlg0 : (r0 &&& 0x80000000#32) = 0#32 :=
          Classical.byContradiction fun h0 => hc1 (Or.inr h0)
        obtain ⟨_, _, _, hlgL, hrefL, hngL, hlitsL⟩ := h2 hne0 hlg0
        have hri := hw0.reason_inv idx hidx0 hne0
        rw [ite_eq_right (fun h0 => h0 hlg0)] at hri; rw [ite_eq_right (fun h0 => h0 hlgL)]
        refine ⟨hrefL, hngL, fun q hq => ?_⟩
        change q ∈ fullArenaClauseLitsCore kn _ at hq; rw [hlitsL] at hq
        rw [hlvl]; exact hri.2.2 q hq
    reason_lit_mem := fun idx hidx hne hlgL => by
      dsimp only [kn] at hidx hne hlgL ⊢; rw [htrl] at hne hlgL ⊢
      have hidx0 : idx < k0.trail_end := hte ▸ hidx; obtain ⟨h1, h2⟩ := hrm_get idx hidx0
      let v := (k0.trl[idx]?.getD 0#32).toNat / 2; let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
      by_cases hc1 : r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32
      · have hreq : kL.rsns[v]?.getD 0xFFFFFFFF#32 = r0 := h1 hc1
        change kL.rsns[v]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 at hne
        change (kL.rsns[v]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 at hlgL
        rw [hreq] at hne hlgL; rcases hc1 with hff | hhi
        · exact absurd hff hne
        · exact absurd hlgL hhi
      · have hne0 : r0 ≠ 0xFFFFFFFF#32 := fun h => hc1 (Or.inl h)
        have hlg0 : (r0 &&& 0x80000000#32) = 0#32 :=
          Classical.byContradiction fun h0 => hc1 (Or.inr h0)
        obtain ⟨_, _, _, _, _, _, hlitsL⟩ := h2 hne0 hlg0
        change (k0.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore kn _
        rw [hlitsL]; exact hw0.reason_lit_mem idx hidx0 hne0 hlg0 }

theorem fullLastLearnedWf_of_all_sentinel {s : FullState}
    (hall : ∀ i < 16, s.scratch.last_learned[i]? = some 0xFFFFFFFF#32) :
    FullLastLearnedWf s :=
  fun i hi => Or.inl (by rw [hall i (by omega), Option.getD_some])

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
