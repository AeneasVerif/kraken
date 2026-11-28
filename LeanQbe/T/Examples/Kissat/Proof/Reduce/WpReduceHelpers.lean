/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import Kraken.Mem
public import Kraken.Separation
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges

/-!
# Shared Reduce & Purge Invariant Helpers (`Proof.Reduce.WpReduceHelpers`)

Zero-legacy-import (`CanonicalEnv`) BitVec header-word, witness, sparse-invariant,
garbage-marking, BCP-13, and sweep-13 preservation lemmas for `WpPurge` and `WpReduce`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. BitVec Header & Arithmetic Helpers -/

theorem bv32_lt_highbit_iff (w : BitVec 32) :
    w.toNat < 0x80000000 ↔ (w &&& 0x80000000#32) = 0#32 := by
  have hw : w.toNat < 2 ^ 32 := w.isLt
  have hd := Nat.and_div_two_pow (a := w.toNat) (b := 0x80000000) (n := 31)
  have hr := Nat.and_mod_two_pow (a := w.toNat) (b := 0x80000000) (n := 31)
  have hdiv : 0x80000000 / 2 ^ 31 = 1 := by decide
  have hrem : 0x80000000 % 2 ^ 31 = 0 := by decide
  rw [hdiv] at hd; rw [hrem, Nat.and_zero] at hr
  have heq : w.toNat &&& 0x80000000 = 2 ^ 31 * ((w.toNat / 2 ^ 31) &&& 1) := by
    have hsplit := Nat.div_add_mod (w.toNat &&& 0x80000000) (2 ^ 31)
    rw [hd, hr, Nat.add_zero] at hsplit; exact hsplit.symm
  have hand_toNat : (w &&& 0x80000000#32).toNat = w.toNat &&& 0x80000000 := by
    rw [BitVec.toNat_and]; rfl
  constructor <;> intro h
  · apply BitVec.eq_of_toNat_eq
    have hq : w.toNat / 2 ^ 31 = 0 := by omega
    rw [hand_toNat, heq, hq]; rfl
  · have h0 : (w &&& 0x80000000#32).toNat = 0 := by rw [h]; rfl
    rw [hand_toNat, heq] at h0
    have hq0 : (w.toNat / 2 ^ 31) &&& 1 = 0 := by omega
    have hq_le : w.toNat / 2 ^ 31 ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq_le with hq | hq
    · omega
    · rw [hq] at hq0; contradiction

theorem bv32_size_mask_lt (w : BitVec 32) : (w &&& 0x0007FFFF#32).toNat < 2 ^ 19 := by
  rw [BitVec.toNat_and, show (0x0007FFFF#32).toNat = 2 ^ 19 - 1 from by decide]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem bv32_mask_pres_of_disj {w m bits upd : BitVec 32}
    (hm : m &&& bits = 0#32) (hu : upd &&& ~~~m = 0#32) :
    (((w &&& ~~~m) ||| upd) &&& bits) = (w &&& bits) := by
  apply BitVec.eq_of_getElem_eq; intro k hk
  have hmk := congrArg (·[k]) hm
  have huk := congrArg (·[k]) hu
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_zero]
    at hmk huk ⊢
  cases hwk : w[k] <;> cases hbk : bits[k] <;> cases hmk' : m[k] <;> cases huk' : upd[k] <;>
    simp_all

theorem bv32_or_pres_of_disj {w upd bits : BitVec 32} (hu : upd &&& bits = 0#32) :
    ((w ||| upd) &&& bits) = (w &&& bits) := by
  apply BitVec.eq_of_getElem_eq; intro k hk
  have huk := congrArg (·[k]) hu
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero] at huk ⊢
  cases hwk : w[k] <;> cases hbk : bits[k] <;> cases huk' : upd[k] <;> simp_all

theorem bv32_bit21_or_pres (w : BitVec 32) :
    ((w ||| 0x00200000#32) &&& 0x0007FFFF#32) = (w &&& 0x0007FFFF#32) ∧
    ((w ||| 0x00200000#32) &&& 0x00080000#32) = (w &&& 0x00080000#32) ∧
    ((w ||| 0x00200000#32) &&& 0x00100000#32) = (w &&& 0x00100000#32) ∧
    ((w ||| 0x00200000#32) &&& 0x00800000#32) = (w &&& 0x00800000#32) :=
  ⟨bv32_or_pres_of_disj (by decide), bv32_or_pres_of_disj (by decide),
   bv32_or_pres_of_disj (by decide), bv32_or_pres_of_disj (by decide)⟩

theorem bv32_bit19_or_pres (w : BitVec 32) :
    ((w ||| 0x00080000#32) &&& 0x0007FFFF#32) = (w &&& 0x0007FFFF#32) ∧
    ((w ||| 0x00080000#32) &&& 0x00100000#32) = (w &&& 0x00100000#32) ∧
    ((w ||| 0x00080000#32) &&& 0x00200000#32) = (w &&& 0x00200000#32) ∧
    ((w ||| 0x00080000#32) &&& 0x00800000#32) = (w &&& 0x00800000#32) ∧
    ((w ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  refine ⟨bv32_or_pres_of_disj (by decide), bv32_or_pres_of_disj (by decide),
    bv32_or_pres_of_disj (by decide), bv32_or_pres_of_disj (by decide), ?_⟩
  intro h
  have h19 := congrArg (·[19]) h
  revert h19; simp [BitVec.getElem_and, BitVec.getElem_or]

theorem bv32_usage_upd_pres (w u : BitVec 32) :
    let w' := (w &&& ~~~0x03000000#32) ||| ((u &&& 3#32) <<< 24)
    (w' &&& 0x0007FFFF#32) = (w &&& 0x0007FFFF#32) ∧
    (w' &&& 0x00080000#32) = (w &&& 0x00080000#32) ∧
    (w' &&& 0x00100000#32) = (w &&& 0x00100000#32) ∧
    (w' &&& 0x00200000#32) = (w &&& 0x00200000#32) ∧
    (w' &&& 0x00800000#32) = (w &&& 0x00800000#32) := by
  have hlt : (u &&& 3#32).toNat < 4 := by
    rw [BitVec.toNat_and, show (3#32).toNat = 3 from rfl]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hu3 : u &&& 3#32 = 0#32 ∨ u &&& 3#32 = 1#32 ∨ u &&& 3#32 = 2#32 ∨ u &&& 3#32 = 3#32 := by
    match hn : (u &&& 3#32).toNat with
    | 0 => left; exact BitVec.eq_of_toNat_eq hn
    | 1 => right; left; exact BitVec.eq_of_toNat_eq hn
    | 2 => right; right; left; exact BitVec.eq_of_toNat_eq hn
    | 3 => right; right; right; exact BitVec.eq_of_toNat_eq hn
    | _ + 4 => omega
  have hu : ((u &&& 3#32) <<< 24) &&& ~~~0x03000000#32 = 0#32 := by
    rcases hu3 with h | h | h | h <;> rw [h] <;> decide
  exact ⟨bv32_mask_pres_of_disj (by decide) hu, bv32_mask_pres_of_disj (by decide) hu,
    bv32_mask_pres_of_disj (by decide) hu, bv32_mask_pres_of_disj (by decide) hu,
    bv32_mask_pres_of_disj (by decide) hu⟩

/-! ## 2. `FullWitnessInv`, `FullReasonsMarked`, & `FullSparseInvW` Preservation -/

theorem markGarb_nonact_of_reasonsMarked {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hmrk : FullReasonsMarked s)
    {cref : Nat} (hnr : (fullArenaHdr s cref &&& 0x00200000#32) = 0#32) :
    ∀ idx < s.core.trail_end,
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref := by
  intro idx hidx rsn hne hlg heqc
  have hpos : 0 < (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
    Nat.zero_lt_of_ne_zero fun hl0 => hne (hw.level0_rsn_none idx hidx hl0)
  have hmk := hmrk idx hidx hpos hlg
  change (fullArenaHdr s rsn.toNat &&& 0x00200000#32) ≠ 0#32 at hmk
  rw [heqc] at hmk
  exact hmk hnr

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
  have hmg := hw.arena.markGarb hlen href ag'
  have hrefs := hmg.1
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
      rw [ite_eq_right hb] at hrs
      exact hdisj_lits hrs.1 (hnonact idx hidx hne hlg) ▸
        hw.reason_lit_mem idx hidx hne hlg }⟩

theorem markGarb_sparseInvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hmrk : FullReasonsMarked s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hnr : (fullArenaHdr s cref &&& 0x00200000#32) = 0#32) (ag' : BitVec 64) :
    let k' := { s.core with
      arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
      arena_garbage := ag' }
    let s' : FullState := { s with core := k' }
    FullSparseInvW c F0 F_cur s' ∧ FullReasonsMarked s' := by
  intro k' s'
  have hlen := hsp.1
  have hw := hsp.2.1
  have hna := markGarb_nonact_of_reasonsMarked hw hmrk hnr
  have hmg := markGarb_preserves_witness hlen.core_ok hw href ag' hna
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with arena_len_arr := by simp [s', k', hlen.core_ok.arena_len_arr] },
     hlen.scratch_ok⟩
  have hrefs_eq : fullArenaClauseRefs s' = fullArenaClauseRefs s := hmg.1
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng
    rw [hrefs_eq] at hr
    by_cases hrc : r = cref
    · subst hrc
      have hgb : fullArenaClauseGarb s' r = true := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
        dsimp only [s', k']
        have hlt : r < s.core.arena.length := by
          have := (hw.arena.refs_wf r hr).2.2.1
          have := (hw.arena.refs_wf r hr).2.2.2.1
          have := hlen.core_ok.arena_len_le
          have := hlen.core_ok.arena_len_arr
          omega
        rw [List.getElem?_set_self hlt, Option.getD_some]
        exact decide_eq_true (bv32_bit19_or_pres _).2.2.2.2
      rw [hgb] at hng; contradiction
    · have hng0 : fullArenaClauseGarb s r = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
        dsimp only [s', k'] at hng
        rwa [List.getElem?_set_ne (Ne.symm hrc)] at hng
      have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
        rcases Nat.lt_or_gt_of_ne hrc with h1 | h2
        · exact Or.inl (hw.arena.disjoint hr href h1)
        · exact Or.inr (by have := hw.arena.disjoint href hr h2; omega)
      have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
        have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
        have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
      have hlits_eq : fullArenaClauseLits s' r = fullArenaClauseLits s r :=
        (fullArenaClauseLitsCore_set_outside hbd hdisj).2
      rw [hlits_eq]; exact hsp.2.2.2.1 r hr hng0
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl (fun r hr => hrefs_eq.symm ▸ hr)
  have hext' : s'.scratch.extend_len ≤ c.extend_cap := hsp.2.2.2.2.1.2
  have hmrk' : FullReasonsMarked s' := by
    intro idx hidx v rsn hpos hlg
    have hmk := hmrk idx hidx hpos hlg
    change (fullArenaHdr s (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32).toNat &&& 0x00200000#32) ≠ 0#32 at hmk
    change (fullArenaHdr s' (s'.core.rsns[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32).toNat &&& 0x00200000#32) ≠ 0#32
    unfold fullArenaHdr fullArenaHdrCore at hmk ⊢
    dsimp only [s', k']
    by_cases hvc : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32).toNat = cref
    · rw [hvc] at hmk; exact absurd hnr hmk
    · rwa [List.getElem?_set_ne (Ne.symm hvc)]
  exact ⟨⟨hlen', hmg.2, hsp.2.2.1, hnd', ⟨hll', hext'⟩, hsp.2.2.2.2.2⟩, hmrk'⟩

theorem setHdrKeep_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k) (w' : BitVec 32)
    (hgarb : (w' &&& 0x00080000#32) = (fullArenaHdrCore k cref &&& 0x00080000#32))
    (hshrk : (w' &&& 0x00800000#32) = (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let k' := { k with arena := k.arena.set cref w' }
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) ∧
    FullWitnessInv c F0 F_cur k' := by
  intro k'
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hget_cref : k.arena[cref]? = some (fullArenaHdrCore k cref) := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have ha_cref : k'.arena[cref]? = some w' := List.getElem?_set_self har_len
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧
        fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff k.arena k.arena_len cref ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := hw.arena.disjoint hr href hlt
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
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [hshrk, show fullArenaHdrCore k cref = k.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_outside r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i _ _
        rcases hne_outside r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
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
        rcases hne_outside r hr hrc with ⟨h1, _⟩ | ⟨h3, h2⟩ <;> omega
      have hls := fullArenaClauseLitsCore_set_outside (v := w') hbd hout
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
        have : r < k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ := fullArenaNextOff_hits_sentinel
        (hw.arena.refs_wf r hr).1 (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; omega
        · rcases hne_outside r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
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

theorem setHdrKeep_sparseInvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (w' : BitVec 32)
    (hgarb : (w' &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32))
    (hshrk : (w' &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32)) :
    let s' : FullState :=
      { s with core := { s.core with arena := s.core.arena.set cref w' } }
    FullSparseInvW c F0 F_cur s' := by
  intro s'
  have hlen := hsp.1
  have hw := hsp.2.1
  obtain ⟨hrefs_eq, hcl_eq, hw'⟩ := setHdrKeep_preserves_witness hlen.core_ok hw
    href w' hgarb hshrk
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with arena_len_arr := by simp [s', hlen.core_ok.arena_len_arr] },
     hlen.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs at hr ⊢; exact hrefs_eq ▸ hr
    have hcl := hcl_eq r hr0
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb; rw [← hcl.2.1]; exact hng
    unfold fullArenaClauseLits; rw [hcl.2.2]
    exact hsp.2.2.2.1 r hr0 hng0
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl (fun r hr => by
      unfold fullArenaClauseRefs at hr ⊢; exact hrefs_eq.symm ▸ hr)
  exact ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩

theorem fullSparseInvW_of_bcp13 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core)
    (hmc : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext_len : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInvW c F0 F_cur s' := by
  have hmc' : FullLitMarksClear c s' := by
    have hmc0 := hsp.2.2.1
    unfold FullLitMarksClear FullMrkZero at hmc0 ⊢; rwa [hmc, hlm]
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hgb
    unfold fullArenaClauseRefs at hr; rw [hperm.2.1] at hr
    have hp := hperm.2.2 r hr
    unfold fullArenaClauseGarb at hgb; rw [hp.2.1] at hgb
    have hn := hsp.2.2.2.1 r hr hgb
    unfold fullArenaClauseLits at hn ⊢
    exact (List.Perm.map (fun x => x / 2) hp.2.2).nodup_iff.mpr hn
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset hll (fun r hr => by
      unfold fullArenaClauseRefs at hr ⊢; exact hperm.2.1 ▸ hr)
  have hext' : s'.scratch.extend_len ≤ c.extend_cap := by
    rw [hext_len]; exact hsp.2.2.2.2.1.2
  exact ⟨hlen', hw', hmc', hnd', ⟨hll', hext'⟩, hdm.trans hsp.2.2.2.2.2⟩

theorem fullSparseInvW_of_sweep13 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hnd' : FullArenaVarsNodup s') (hll' : FullLastLearnedWf s')
    (hmc : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hext_len : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInvW c F0 F_cur s' := by
  have hmc' : FullLitMarksClear c s' := by
    have hmc0 := hsp.2.2.1
    unfold FullLitMarksClear FullMrkZero at hmc0 ⊢; rwa [hmc, hlm]
  have hext' : s'.scratch.extend_len ≤ c.extend_cap := by
    rw [hext_len]; exact hsp.2.2.2.2.1.2
  exact ⟨hlen', hw', hmc', hnd', ⟨hll', hext'⟩, hdm.trans hsp.2.2.2.2.2⟩

end LeanQbe.T.Examples.Kissat.Proof.Reduce