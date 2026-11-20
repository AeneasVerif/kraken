/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Stage-4 (`D-Full`) GC / Sweep / Reduce `Func.wp` Proofs — Part 2 (`Full1.lean`, 7/13 fns)

Header-mutation preservation lemmas (`setHdrKeepGarbShrk_preserves_witness`,
`markGarb_preserves_witness`, `fullArenaVarsNodup_of_markGarb`) and `Func.wp` proofs for the first
7 owned functions in `Full1.lean`:
1. `full_mark_reasons`
2. `full_red_less`
3. `full_red_sift`
4. `full_sort_reds`
5. `full_lit_rank`
6. `full_unwatch_large`
7. `full_sweep_bins`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full.FullReduceSpecs
open LeanQbe.T.Examples.Kissat.Full.FullReduceHelpers
open scoped FullArenaTactics FullReduceTactics

/-! ## 1. Header, compaction prefix, & `SweepReasonMapInv.toFullWitnessInv` helpers -/

namespace FullReduceHelpers

/-- Updating non-structural header bits (`PH_RSN` or usage bits `27..31`, preserving `PH_GARB`
and `PH_SHRK`) at `cref ∈ fullArenaClauseRefsCore` preserves `FullWitnessInv` verbatim. -/
theorem setHdrKeepGarbShrk_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k) {v : BitVec 32}
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
        have : r < k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
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

/-- Witness-preserving version of `markGarb_preserves_fullCore` (same `F_cur`). -/
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

end FullReduceHelpers

/-! ## 2. `full_mark_reasons_wp` (`Full1.lean:1075-1094`) -/

theorem full_mark_reasons_wp (Γ : Env) :
    ∀ a m Q X, fullMarkReasonsSpec a m Q X → Func.wp Γ full_mark_reasons_body a m Q X := by
  rintro ⟨h, set_flag, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  have hte_le := hlen.core_ok.trail_end_le
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcap_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hal_le := hlen.core_ok.arena_len_le
  have htrl_len := hlen.core_ok.trl_len
  have hlvl_len := hlen.core_ok.lvl_len
  have hrsns_len := hlen.core_ok.rsns_len
  fr_steps
  refine wp_loop_inv
    (fun (i, ()) mL =>
      i.toNat ≤ s.core.trail_end ∧
      ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
        let sL : FullState := { s with core := { s.core with arena := arL } }
        FullWitnessInv c F0 F_cur sL.core ∧
        fullArenaClauseRefs sL = fullArenaClauseRefs s ∧
        (∀ r ∈ fullArenaClauseRefs s,
          fullArenaClauseSize sL r = fullArenaClauseSize s r ∧
          fullArenaClauseGarb sL r = fullArenaClauseGarb s r ∧
          fullArenaClauseLits sL r = fullArenaClauseLits s r) ∧
        (set_flag = true → ∀ idx < i.toNat,
          let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
          let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
          0 < (s.core.lvl[v]?.getD 0#32).toNat →
          (rsn &&& 0x80000000#32) = 0#32 →
          (fullArenaHdr sL rsn.toNat &&& 0x00200000#32) ≠ 0#32) ∧
        (FullMem c sL ⋆ R) mL)
    (fun (i, ()) _ => s.core.trail_end - i.toNat)
    (fun J hLoop => ?_) ?_
  · fr_steps
    exact hLoop (0#64, ()) m ⟨Nat.zero_le _, s.core.arena, hlen.core_ok.arena_len_arr, hw, rfl,
      fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ hi => by bv_omega, hm⟩
  · rintro J ⟨i, ⟨⟩⟩ mL ⟨hi_le, arL, harL, hwL, hrefsL, hclL, hmkL, hmL⟩ hLoop
    let sL : FullState := { s with core := { s.core with arena := arL } }
    have hlenL : sL.LengthsOk c := ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
    have hdone : i.toNat = s.core.trail_end → Q () mL := fun heq =>
      hQ arL mL hlenL hrefsL hclL (fun hsf => fun idx hidx => hmkL hsf idx (heq ▸ hidx)) hwL hmL
    fr_split
    · have hi_lt : i.toNat < s.core.trail_end := by c0_bound
      have hi_trl : i.toNat < sL.core.trl.length := by dsimp [sL]; rw [htrl_len]; omega
      have hlit_lt : (s.core.trl[i.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        have := hw.trail_lits_lt i.toNat hi_lt
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      have hv_lt : (s.core.trl[i.toNat]'(by omega)).toNat / 2 < s.core.cur_vars := by omega
      have hv_lvl : (s.core.trl[i.toNat]'(by omega)).toNat / 2 < s.core.lvl.length := by omega
      have hv_rsn : (s.core.trl[i.toNat]'(by omega)).toNat / 2 < s.core.rsns.length := by omega
      have hi_next : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
      let vNat : Nat := (s.core.trl[i.toNat]'(by omega)).toNat / 2
      let r32 : BitVec 32 := s.core.rsns[vNat]'hv_rsn
      have hr32_eq : s.core.rsns[(s.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
          = r32 := by
        simp [List.getElem?_eq_getElem (by omega : i.toNat < s.core.trl.length),
          List.getElem?_eq_getElem hv_rsn, r32, vNat]
      fr_to_group
      refine wp_join_group (fun () mJ =>
        ∃ ar' : List (BitVec 32), ar'.length = c.arena_cap ∧
          let s' : FullState := { s with core := { s.core with arena := ar' } }
          FullWitnessInv c F0 F_cur s'.core ∧
          fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
          (∀ r ∈ fullArenaClauseRefs s,
            fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
            fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
            fullArenaClauseLits s' r = fullArenaClauseLits s r) ∧
          (set_flag = true → ∀ idx < i.toNat + 1,
            let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
            let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
            0 < (s.core.lvl[v]?.getD 0#32).toNat →
            (rsn &&& 0x80000000#32) = 0#32 →
            (fullArenaHdr s' rsn.toNat &&& 0x00200000#32) ≠ 0#32) ∧
          (FullMem c s' ⋆ R) mJ) ?_ ?_
      · rintro _ ⟨⟩ mJ ⟨ar', har', hw', hrefs', hcl', hmk', hmJ⟩
        fr_steps
        exact hLoop (i + 1#64, ()) mJ (by dsimp only; rw [hi_next]; omega)
          ⟨by rw [hi_next]; omega, ar', har', hw', hrefs', hcl',
           by simpa [hi_next] using hmk', hmJ⟩
      · intro Jj hJj
        have hmem_of_lt : r32.toNat < 0x80000000 → r32.toNat ∈ fullArenaClauseRefsCore sL.core := by
          intro hr_lt
          have hr_ne : r32 ≠ 0xFFFFFFFF#32 := fun h => by
            have := congrArg BitVec.toNat h; simp at this; omega
          have hr_lg : (r32 &&& 0x80000000#32) = 0#32 := (bv32_lt_highbit_iff r32).mp hr_lt
          have hri := hwL.reason_inv i.toNat hi_lt (by simpa [sL, hr32_eq] using hr_ne)
          have h1 : sL.core.rsns[(sL.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
              = r32 := hr32_eq
          rw [h1, ite_eq_right (fun h => h hr_lg)] at hri; exact hri.1
        fr_steps
        · -- `set_flag = true`
          rename_i hv_lt_cv hlvl_pos hr_lt8 hr_le3
          have hr_lt : r32.toNat < 0x80000000 := by
            change (s.core.rsns[vNat]'hv_rsn).toNat < 0x80000000
            simpa [vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hr_lt8
          have hmem := hmem_of_lt hr_lt
          have hr_al : r32.toNat < arL.length := by
            have := (hwL.arena.refs_wf _ hmem).1; dsimp [sL] at this; omega
          have hbits := bv32_bit21_or_pres (arL[r32.toNat]'hr_al)
          have hhdr_eq : fullArenaHdrCore sL.core r32.toNat = arL[r32.toNat]'hr_al := by
            unfold fullArenaHdrCore; dsimp [sL]
            rw [List.getElem?_eq_getElem hr_al, Option.getD_some]
          obtain ⟨hrefs', hcl', hw'⟩ := setHdrKeepGarbShrk_preserves_witness hlenL.core_ok hwL hmem
            (v := (arL[r32.toNat]'hr_al) ||| 0x00200000#32)
            (by rw [hhdr_eq]; exact hbits.1) (by rw [hhdr_eq]; exact hbits.2.1)
          refine hJj () _ ⟨arL.set r32.toNat ((arL[r32.toNat]'hr_al) ||| 0x00200000#32),
            by simp [harL], hw', hrefs'.trans hrefsL, fun r hr => ?_, fun _ idx hidx => ?_, hm⟩
          · have hrL : r ∈ fullArenaClauseRefsCore sL.core := by
              change r ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hr
            have h1 := hcl' r hrL; have h2 := hclL r hr
            exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
          · dsimp only; intro hlpos hrlg
            by_cases hidx_eq : idx = i.toNat
            · subst hidx_eq; rw [hr32_eq]
              unfold fullArenaHdr fullArenaHdrCore; dsimp only
              rw [List.getElem?_set_self hr_al, Option.getD_some]; exact hbits.2.2
            · have hprev := hmkL hc idx (by omega) hlpos hrlg
              let rsn_i :=
                s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
              by_cases hre : rsn_i.toNat = r32.toNat
              · unfold fullArenaHdr fullArenaHdrCore; dsimp only
                rw [show (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                    0xFFFFFFFF#32).toNat = r32.toNat from hre,
                  List.getElem?_set_self hr_al, Option.getD_some]
                exact hbits.2.2
              · unfold fullArenaHdr fullArenaHdrCore at hprev ⊢; dsimp only at hprev ⊢
                rw [List.getElem?_set_ne (Ne.symm hre)]; exact hprev
        · -- `set_flag = false`
          rename_i hv_lt_cv hlvl_pos hr_lt8 hr_le3
          have hr_lt : r32.toNat < 0x80000000 := by
            change (s.core.rsns[vNat]'hv_rsn).toNat < 0x80000000
            simpa [vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hr_lt8
          have hmem := hmem_of_lt hr_lt
          have hr_al : r32.toNat < arL.length := by
            have := (hwL.arena.refs_wf _ hmem).1; dsimp [sL] at this; omega
          have hbits := bv32_bit21_clear_pres (arL[r32.toNat]'hr_al)
          have hhdr_eq : fullArenaHdrCore sL.core r32.toNat = arL[r32.toNat]'hr_al := by
            unfold fullArenaHdrCore; dsimp [sL]
            rw [List.getElem?_eq_getElem hr_al, Option.getD_some]
          obtain ⟨hrefs', hcl', hw'⟩ := setHdrKeepGarbShrk_preserves_witness hlenL.core_ok hwL hmem
            (v := (arL[r32.toNat]'hr_al) &&& ~~~0x00200000#32)
            (by rw [hhdr_eq]; exact hbits.1) (by rw [hhdr_eq]; exact hbits.2)
          refine hJj () _ ⟨arL.set r32.toNat ((arL[r32.toNat]'hr_al) &&& ~~~0x00200000#32),
            by simp [harL], hw', hrefs'.trans hrefsL, fun r hr => ?_,
            fun h => by simp [h] at hc, hm⟩
          have hrL : r ∈ fullArenaClauseRefsCore sL.core := by
            change r ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hr
          have h1 := hcl' r hrL; have h2 := hclL r hr
          exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
        · -- `r < 0x80000000` but `¬ (r + 3 ≤ alen)`: impossible
          rename_i hv_lt_cv hlvl_pos hr_lt8
          have hr_lt : r32.toNat < 0x80000000 := by
            change (s.core.rsns[vNat]'hv_rsn).toNat < 0x80000000
            simpa [vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hr_lt8
          have hmem := hmem_of_lt hr_lt
          have hwf3 := (hwL.arena.refs_wf _ hmem).1
          dsimp [sL] at hwf3
          have hnot3 : ¬ (r32.toNat + 3) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 := by
            simpa [r32, vNat, show (3 : BitVec 64).toNat = 3 from rfl] using hc
          omega
        · -- `r ≥ 0x80000000`
          rename_i hv_lt_cv hlvl_pos
          refine hJj () mL ⟨arL, harL, hwL, hrefsL, hclL, fun hsf idx hidx => ?_, hmL⟩
          by_cases hidx_eq : idx = i.toNat
          · subst hidx_eq; dsimp only; intro _ hrlg
            rw [hr32_eq] at hrlg
            have hlt := (bv32_lt_highbit_iff r32).mpr hrlg
            have hge : ¬ r32.toNat < 0x80000000 := by
              simpa [r32, vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hc
            exact False.elim (hge hlt)
          · exact hmkL hsf idx (by omega)
        · -- `lvl[v] == 0`
          rename_i hv_lt_cv
          refine hJj () mL ⟨arL, harL, hwL, hrefsL, hclL, fun hsf idx hidx => ?_, hmL⟩
          by_cases hidx_eq : idx = i.toNat
          · subst hidx_eq; dsimp only; intro hlpos _
            have h1 : (s.core.lvl[(s.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
                = (s.core.lvl[vNat]'hv_lvl).toNat := by
              simp [List.getElem?_eq_getElem (by omega : i.toNat < s.core.trl.length),
                List.getElem?_eq_getElem hv_lvl, vNat]
            have hnot : ¬ (0 < (s.core.lvl[vNat]'hv_lvl).toNat) := by
              simpa [vNat, show (0 : BitVec 32).toNat = 0 from rfl] using hc
            rw [h1] at hlpos; exact False.elim (hnot hlpos)
          · exact hmkL hsf idx (by omega)
    · fr_steps; exact hdone (by c0_bound)

/-! ## 3. `full_red_less_wp`, `full_red_sift_wp`, `full_sort_reds_wp` (`Full1.lean:1096-1127`) -/

theorem full_red_less_wp (Γ : Env) :
    ∀ a m Q X, fullRedLessSpec a m Q X → Func.wp Γ full_red_less_body a m Q X := by
  rintro ⟨ar_ptr, a, b, ⟨⟩⟩ m Q X ⟨ar, R, ha2, hb2, hm, hQ⟩
  have ha_lt : a.toNat < ar.length := by omega
  have hb_lt : b.toNat < ar.length := by omega
  have ha2_lt : (a + 2#32).toNat < ar.length := by
    have : (a + 2#32).toNat ≤ a.toNat + 2 := by rw [BitVec.toNat_add]; simp; omega
    omega
  have hb2_lt : (b + 2#32).toNat < ar.length := by
    have : (b + 2#32).toNat ≤ b.toNat + 2 := by rw [BitVec.toNat_add]; simp; omega
    omega
  fr_steps <;> exact hQ _

theorem full_red_sift_wp (Γ : Env)
    (hless : ∀ a m Q X, fullRedLessSpec a m Q X →
      Γ "full_red_less" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullRedSiftSpec a m Q X → Func.wp Γ full_red_sift_body a m Q X := by
  rintro ⟨ar_ptr, rr_ptr, start, n, ⟨⟩⟩ m Q X ⟨ar, rr, R, hsn, hn_rr, hn62, hrefs, hm, hQ⟩
  fr_steps
  refine wp_loop_inv
    (fun (root, ()) mL =>
      root.toNat ≤ n.toNat ∧
      ∃ rrL : List (BitVec 32), rrL.length = rr.length ∧
        (∀ k, n.toNat ≤ k → rrL[k]? = rr[k]?) ∧
        (∀ k < n.toNat, ∃ j < n.toNat, rrL[k]? = rr[j]?) ∧
        (array (t := i32) ar_ptr ar ⋆ array (t := i32) rr_ptr rrL ⋆ R) mL)
    (fun (root, ()) _ => n.toNat - root.toNat)
    (fun J hLoop => ?_) ?_
  · fr_steps
    exact hLoop (start, ()) m ⟨hsn, rr, rfl, fun _ _ => rfl, fun k hk => ⟨k, hk, rfl⟩, hm⟩
  · rintro J ⟨root, ⟨⟩⟩ mL ⟨hrt_le, rrL, hlenL, houtL, hmemL, hmL⟩ hLoop
    have hch_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 := by
      have hsh : (root <<< (1 : Nat)).toNat = 2 * root.toNat := by
        rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
      rw [BitVec.toNat_add, hsh]; simp; omega
    have hrefL : ∀ k < n.toNat, (rrL[k]?.getD 0#32).toNat + 2 < ar.length := fun k hk => by
      obtain ⟨j, hj, heq⟩ := hmemL k hk; rw [heq]; exact hrefs j hj
    fr_split
    · clear hc
      fr_split
      · -- `ch ≥ n`: break and return
        fr_steps; exact hQ rrL mL hlenL houtL hmemL hmL
      · have hch_lt : 2 * root.toNat + 1 < n.toNat := by
          have : ¬ (n.toNat ≤ ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat) := by c0_bound
          omega
        have hrt_lt : root.toNat < n.toNat := by omega
        fr_to_group
        refine wp_join_group
          (fun (ch, ()) mJ => mL = mJ ∧ ch.toNat < n.toNat ∧ root.toNat < ch.toNat) ?_ ?_
        · rintro _ ⟨ch, ⟨⟩⟩ mJ ⟨hm_eq, hch_n, hrt_ch⟩
          subst mJ
          have hrt_rr : root.toNat < rrL.length := by omega
          have hch_rr : ch.toNat < rrL.length := by omega
          fr_steps; c0_call hless
          refine ⟨ar, array (t := i32) rr_ptr rrL ⋆ R, ?_, ?_, by ecancel, fun res => ?_⟩
          · simpa [List.getElem?_eq_getElem hrt_rr] using hrefL root.toNat hrt_lt
          · simpa [List.getElem?_eq_getElem hch_rr] using hrefL ch.toNat hch_n
          · fr_steps
            · -- `res = true`: swap `rr[root]` and `rr[ch]`
              let rr1 := rrL.set root.toNat (rrL[ch.toNat]'hch_rr)
              let rr2 := rr1.set ch.toNat (rrL[root.toNat]'hrt_rr)
              have hlen2 : rr2.length = rr.length := by simp [rr2, rr1, hlenL]
              have hout2 : ∀ k, n.toNat ≤ k → rr2[k]? = rr[k]? := fun k hk => by
                dsimp only [rr2, rr1]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact houtL k hk
              have hmem2 : ∀ k < n.toNat, ∃ j < n.toNat, rr2[k]? = rr[j]? := fun k hk => by
                by_cases hkc : k = ch.toNat
                · subst hkc
                  obtain ⟨j, hj, heq⟩ := hmemL root.toNat hrt_lt
                  refine ⟨j, hj, ?_⟩
                  dsimp only [rr2, rr1]
                  rw [List.getElem?_set_self (by simp; omega), ← heq,
                    List.getElem?_eq_getElem hrt_rr]
                · by_cases hkr : k = root.toNat
                  · subst hkr
                    obtain ⟨j, hj, heq⟩ := hmemL ch.toNat hch_n
                    refine ⟨j, hj, ?_⟩
                    dsimp only [rr2, rr1]
                    rw [List.getElem?_set_ne (Ne.symm hkc), List.getElem?_set_self hrt_rr, ← heq,
                      List.getElem?_eq_getElem hch_rr]
                  · obtain ⟨j, hj, heq⟩ := hmemL k hk
                    refine ⟨j, hj, ?_⟩
                    dsimp only [rr2, rr1]
                    rw [List.getElem?_set_ne (Ne.symm hkc), List.getElem?_set_ne (Ne.symm hkr), heq]
              have hm' : (array (t := i32) rr_ptr rr2 ⋆ (array (t := i32) ar_ptr ar ⋆ R)) m := by
                dsimp only [rr2, rr1]; exact hm
              exact hLoop (ch, ()) m (by dsimp only; omega)
                ⟨by omega, rr2, hlen2, hout2, hmem2, by ecancel⟩
            · -- `!res`: break and return
              exact hQ rrL mL hlenL houtL hmemL hmL
        · intro Jj hJj
          fr_split
          · have hch1_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat =
                2 * root.toNat + 2 := by
              rw [BitVec.toNat_add, hch_eq]; simp; omega
            have hch1_lt : 2 * root.toNat + 2 < n.toNat := by
              have : ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat < n.toNat :=
                by c0_bound
              omega
            have h1_rr : ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat <
                rrL.length := by omega
            have h0_rr : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat < rrL.length := by omega
            fr_steps; c0_call hless
            refine ⟨ar, array (t := i32) rr_ptr rrL ⋆ R, ?_, ?_, by ecancel, fun res => ?_⟩
            · have h := hrefL ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat
                (by rw [hch1_eq]; omega)
              rwa [List.getElem?_eq_getElem h1_rr, Option.getD_some] at h
            · have h := hrefL ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat (by rw [hch_eq]; omega)
              rwa [List.getElem?_eq_getElem h0_rr, Option.getD_some] at h
            · fr_steps
              · exact hJj _ mL ⟨rfl, by rw [hch_eq]; omega, by rw [hch_eq]; omega⟩
              · exact hJj _ mL ⟨rfl, by rw [hch1_eq]; omega, by rw [hch1_eq]; omega⟩
          · fr_steps; exact hJj _ mL ⟨rfl, by rw [hch_eq]; omega, by rw [hch_eq]; omega⟩
    · fr_steps; exact hQ rrL mL hlenL houtL hmemL hmL

theorem full_sort_reds_wp (Γ : Env)
    (hsift : ∀ a m Q X, fullRedSiftSpec a m Q X →
      Γ "full_red_sift" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullSortRedsSpec a m Q X → Func.wp Γ full_sort_reds_body a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn_cap, hrefs, hm, hQ⟩
  have hrr_len := hlen.scratch_ok.red_refs_len
  have har_len := hlen.core_ok.arena_len_arr
  have hred_lt : c.red_cap < 2 * 2 ^ 28 := c.hred
  have hn62 : n.toNat < 2 ^ 62 := by omega
  fr_split
  · fr_steps; exact hQ s.scratch.red_refs m hrr_len (fun k hk => ⟨k, hk, rfl⟩) hm
  · have hn_gt1 : 1 < n.toNat := by c0_bound
    fr_steps
    refine wp_loop_inv
      (fun (st, ()) m1 =>
        st.toNat ≤ n.toNat ∧
        ∃ rr1 : List (BitVec 32), rr1.length = c.red_cap ∧
          (∀ k < n.toNat, ∃ j < n.toNat, rr1[k]? = s.scratch.red_refs[j]?) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rr1 } } ⋆ R) m1)
      (fun (st, ()) _ => st.toNat)
      (fun J1 hLoop1 => ?_) ?_
    · fr_steps
      have hst0 : (n >>> (1 : Nat)).toNat ≤ n.toNat := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
      exact hLoop1 (n >>> (1 : Nat), ()) m
        ⟨hst0, s.scratch.red_refs, hrr_len, fun k hk => ⟨k, hk, rfl⟩, hm⟩
    · rintro J1 ⟨st, ⟨⟩⟩ m1 ⟨hst_le, rr1, hlen1, hmem1, hm1⟩ hLoop1
      fr_split
      · have hst_pos : 0 < st.toNat := by c0_bound
        have hst1_eq : (st - (1 : BitVec 64)).toNat = st.toNat - 1 := by bv_omega
        fr_steps; c0_call hsift
        let s1 := { s with scratch := { s.scratch with red_refs := rr1 } }
        refine ⟨s.core.arena, rr1, FullArenaRedRest c s1 ⋆ R,
            by rw [hst1_eq]; omega, by omega, hn62, fun k hk => ?_, focus_full_arena_red_refs hm1,
            fun rr2 m2 hlen2 _ hmem2 hm2 => ?_⟩
        · obtain ⟨j, hj, heq⟩ := hmem1 k hk; rw [heq, har_len]; exact hrefs j hj
        · fr_steps
          refine hLoop1 (st - (1 : BitVec 64), ()) m2 (by dsimp only; rw [hst1_eq]; omega)
            ⟨by rw [hst1_eq]; omega, rr2, by omega, fun k hk => ?_, ?_⟩
          · obtain ⟨j, hj, heq⟩ := hmem2 k hk; obtain ⟨j0, hj0, heq0⟩ := hmem1 j hj
            exact ⟨j0, hj0, heq.trans heq0⟩
          · simpa [s1] using unfocus_full_arena_red_refs hm2
      · -- Loop 2: `end = n - 1; while (end > 0) { swap(rr[0], rr[end]); ... }`
        fr_steps
        refine wp_loop_inv
          (fun (ed, ()) m2 =>
            ed.toNat < n.toNat ∧
            ∃ rr2 : List (BitVec 32), rr2.length = c.red_cap ∧
              (∀ k < n.toNat, ∃ j < n.toNat, rr2[k]? = s.scratch.red_refs[j]?) ∧
              (FullMem c { s with scratch := { s.scratch with red_refs := rr2 } } ⋆ R) m2)
          (fun (ed, ()) _ => ed.toNat)
          (fun J2 hLoop2 => ?_) ?_
        · fr_steps
          exact hLoop2 (n - 1#64, ()) m1 ⟨by bv_omega, rr1, hlen1, hmem1, hm1⟩
        · rintro J2 ⟨ed, ⟨⟩⟩ m2 ⟨hed_lt, rr2, hlen2, hmem2, hm2⟩ hLoop2
          fr_split
          · have hed_pos : 0 < ed.toNat := by c0_bound
            have h0_rr : 0 < rr2.length := by omega
            have hed_rr : ed.toNat < rr2.length := by omega
            fr_steps; c0_call hsift
            let rr_sw := (rr2.set 0 (rr2[ed.toNat]'hed_rr)).set ed.toNat (rr2[0]'h0_rr)
            have hlen_sw : rr_sw.length = c.red_cap := by simp [rr_sw, hlen2]
            have hmem_sw : ∀ k < n.toNat, ∃ j < n.toNat, rr_sw[k]? = s.scratch.red_refs[j]? := by
              intro k hk
              by_cases hke : k = ed.toNat
              · subst hke
                obtain ⟨j, hj, heq⟩ := hmem2 0 (by omega)
                refine ⟨j, hj, ?_⟩
                dsimp only [rr_sw]; rw [List.getElem?_set_self (by simp; omega), ← heq,
                  List.getElem?_eq_getElem h0_rr]
              · by_cases hk0 : k = 0
                · subst hk0
                  obtain ⟨j, hj, heq⟩ := hmem2 ed.toNat hed_lt
                  refine ⟨j, hj, ?_⟩
                  dsimp only [rr_sw]
                  rw [List.getElem?_set_ne (Ne.symm hke), List.getElem?_set_self h0_rr, ← heq,
                    List.getElem?_eq_getElem hed_rr]
                · obtain ⟨j, hj, heq⟩ := hmem2 k hk
                  refine ⟨j, hj, ?_⟩
                  dsimp only [rr_sw]
                  rw [List.getElem?_set_ne (Ne.symm hke), List.getElem?_set_ne (Ne.symm hk0), heq]
            let s_sw := { s with scratch := { s.scratch with red_refs := rr_sw } }
            refine ⟨s.core.arena, rr_sw, FullArenaRedRest c s_sw ⋆ R,
                Nat.zero_le _, by omega, by omega, fun k hk => ?_,
                focus_full_arena_red_refs hm,
                fun rr3 m3 hlen3 hout3 hmem3 hm3 => ?_⟩
            · obtain ⟨j, hj, heq⟩ := hmem_sw k (by omega); rw [heq, har_len]; exact hrefs j hj
            · have hed1_eq : (ed - 1#64).toNat = ed.toNat - 1 := by bv_omega
              fr_steps
              refine hLoop2 (ed - 1#64, ()) m3 (by dsimp only; rw [hed1_eq]; omega)
                ⟨by rw [hed1_eq]; omega, rr3, by omega, fun k hk => ?_, ?_⟩
              · by_cases hke : k < ed.toNat
                · obtain ⟨j, hj, heq⟩ := hmem3 k hke
                  obtain ⟨j0, hj0, heq0⟩ := hmem_sw j (by omega)
                  exact ⟨j0, hj0, heq.trans heq0⟩
                · obtain ⟨j0, hj0, heq0⟩ := hmem_sw k hk
                  exact ⟨j0, hj0, (hout3 k (by omega)).trans heq0⟩
              · simpa [s_sw] using unfocus_full_arena_red_refs hm3
          · fr_steps; exact hQ rr2 m2 hlen2 hmem2 hm2

/-! ## 4. `full_lit_rank_wp`, `full_unwatch_large_wp`, `full_sweep_bins_wp` -/

theorem full_lit_rank_wp (Γ : Env) :
    ∀ a m Q X, fullLitRankSpec a m Q X → Func.wp Γ full_lit_rank_body a m Q X := by
  rintro ⟨vals_ptr, lvl_ptr, l, ⟨⟩⟩ m Q X ⟨vals, lvl, R, hl_v, hl_l, hm, hQ⟩
  have hsh : (l >>> 1#32).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hsh_l : (l >>> 1#32).toNat < lvl.length := by rw [hsh]; exact hl_l
  fr_steps <;> exact hQ _

theorem full_unwatch_large_wp (Γ : Env) :
    ∀ a m Q X, fullUnwatchLargeSpec a m Q X → Func.wp Γ full_unwatch_large_body a m Q X := by
  rintro ⟨h, lit, cref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr
  have hwl_le := hlen.core_ok.wlen_le
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hwcap_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  let dense : Bool := decide (s.core.dense_mode ≠ 0#64)
  fr_split
  · fr_steps; exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hw hm
  · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
      have hsh : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
        rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
      have : (lit.setWidth 64).toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by
        c0_bound
      rw [hsh, zext_toNat lit (by decide)] at this; exact this
    have h2l_eq : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
      rw [BitVec.toNat_shiftLeft, zext_toNat lit (by decide)]; simp [Nat.shiftLeft_eq]; omega
    have h2l1_eq : ((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
        2 * lit.toNat + 1 := by
      rw [BitVec.toNat_add, h2l_eq]; simp; omega
    have h2l_lt : 2 * lit.toNat < s.core.wvec.length := by omega
    have h2l1_lt : 2 * lit.toNat + 1 < s.core.wvec.length := by omega
    have hmod0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := by omega
    have hmod1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
      simp; omega
    let off0 : Nat := fullWatchOff s lit.toNat
    let sz0 : Nat := fullWatchSize s lit.toNat
    let offW : BitVec 32 := s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)
    let szW : BitVec 32 :=
      s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by omega)
    have hoff_idx : (s.core.wvec[2 * lit.toNat]'h2l_lt).toNat = off0 := by
      unfold off0 fullWatchOff fullWatchOffCore; simp [List.getElem?_eq_getElem h2l_lt]
    have hsz_idx : (s.core.wvec[2 * lit.toNat + 1]'h2l1_lt).toNat = sz0 := by
      unfold sz0 fullWatchSize fullWatchSizeCore; simp [List.getElem?_eq_getElem h2l1_lt]
    have hoff_eq : offW.toNat = off0 := by
      unfold offW; simp only [h2l_eq]; exact hoff_idx
    have hsz_eq : szW.toNat = sz0 := by
      unfold szW; simp only [h2l1_eq]; exact hsz_idx
    have hbd_end : off0 + sz0 ≤ s.core.wlen := hw.watches.bounds lit.toNat hlit_lt
    have hslice0 : ModeWatchSliceOk dense F_cur s.core lit.toNat off0 sz0 :=
      modeWatchesInv_slice_of_lt hw.watches hlit_lt
    fr_steps
    · -- `sz == 0`
      exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hw hm
    · -- Loop 1: compact `[off0, off0 + sz0)`
      have hsz_pos : 0 < sz0 := by
        have hnz : sz0 ≠ 0 := fun h0 => hc (by
          simp only [hmod1]
          apply BitVec.eq_of_toNat_eq
          rw [zext_toNat _ (by decide), hsz_idx, h0]; rfl)
        omega
      let end0 : Nat := off0 + sz0
      refine wp_loop_inv
        (fun (p, q, ()) m1 =>
          off0 ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end0 ∧
          ∃ wstk1 : List (BitVec 32), wstk1.length = c.wcap ∧
            (∀ i, i < off0 ∨ p.toNat ≤ i → wstk1[i]? = s.core.wstk[i]?) ∧
            ModeWatchSliceOk dense F_cur s.core lit.toNat p.toNat (end0 - p.toNat) ∧
            ModeWatchSliceOk dense F_cur { s.core with wstk := wstk1 } lit.toNat off0
              (q.toNat - off0) ∧
            (FullMem c { s with core := { s.core with wstk := wstk1 } } ⋆ R) m1)
        (fun (p, _, ()) _ => end0 - p.toNat)
        (fun J1 hLoop1 => ?_) ?_
      · fr_steps
        have hoff64 : (offW.setWidth 64).toNat = off0 := by
          rw [zext_toNat offW (by decide), hoff_eq]
        refine hLoop1 _ m ⟨by rw [hoff64]; exact Nat.le_refl _,
          by rw [hoff64]; exact Nat.le_refl _, by rw [hoff64]; omega,
          s.core.wstk, hws_len, fun _ _ => rfl, ?_, ?_, hm⟩
        · rw [hoff64, show end0 - off0 = sz0 by omega]; exact hslice0
        · rw [hoff64, Nat.sub_self]; exact ModeWatchSliceOk.empty
      · rintro J1 ⟨p, q, ⟨⟩⟩ m1 ⟨hoq, hqp, hpe, wstk1, hlen1, hout1, hrem1, hpre1, hm1⟩ hLoop1
        fr_split
        · have hp_lt : p.toNat < end0 := by
            have h1 := hc; simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1; omega
          have hp_w : p.toNat < wstk1.length := by omega
          have hq_w : q.toNat < wstk1.length := by omega
          let w0 := wstk1[p.toNat]'hp_w
          have hw0_orig : s.core.wstk[p.toNat]? = some w0 := by
            rw [← hout1 p.toNat (Or.inr (Nat.le_refl _)), List.getElem?_eq_getElem hp_w]
          have hstep := hrem1.step (by omega) hw0_orig
          fr_split
          · -- Binary watch: keep `w0` at `q`, advance `p + 1`, `q + 1`
            have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
              change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) ≠ 0#32; assumption
            obtain ⟨hne, hlt_o, hent_o, hrem'⟩ := hstep.1 hbin
            have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
            have hq1_eq : (q + 1#64).toNat = q.toNat + 1 := by bv_omega
            fr_steps
            refine hLoop1 (p + 1#64, q + 1#64, ()) m (by dsimp only; rw [hp1_eq]; omega)
              ⟨by rw [hq1_eq]; omega, by rw [hp1_eq, hq1_eq]; omega, by rw [hp1_eq]; omega,
               wstk1.set q.toNat w0, by simp [hlen1],
               fun i hi => by
                 rw [hp1_eq] at hi; rw [List.getElem?_set_ne (by omega)]; exact hout1 i (by omega),
               by simpa [hp1_eq, show end0 - (p.toNat + 1) = end0 - p.toNat - 1 by omega]
                 using hrem',
               ?_, hm⟩
            rw [hq1_eq, show q.toNat + 1 - off0 = (q.toNat - off0) + 1 by omega]
            exact ModeWatchSliceOk.append_bin (k := { s.core with wstk := wstk1 })
              (k' := { s.core with wstk := wstk1.set q.toNat w0 }) (p := off0) (p' := off0)
              (Nat.le_refl _) (fun _ r => r)
              (fun j hj => List.getElem?_set_ne (by omega)) hpre1
              (by rw [show off0 + (q.toNat - off0) = q.toNat by omega]
                  exact List.getElem?_set_self hq_w)
              hbin hne hlt_o hent_o
          · -- Large / occ watch: `(w0, cr)`
            have hlg : (w0 &&& 0x80000000#32) = 0#32 := by
              change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) = 0#32; assumption
            obtain ⟨h2rem, cr, hcr_orig, hsz3, hcr_lt, hcr_ref, hrem'⟩ := hstep.2 hlg
            have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
            have hp2_eq : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
              rw [BitVec.toNat_add, hp1_eq]; simp; omega
            have hp1_lt : (p + 1#64).toNat < end0 := by omega
            have hp1_w : (p + 1#64).toNat < wstk1.length := by omega
            have hcr_eq : wstk1[(p + 1#64).toNat]'hp1_w = cr := by
              have h1 := hout1 (p.toNat + 1) (Or.inr (by omega))
              rw [List.getElem?_eq_getElem (by omega : p.toNat + 1 < wstk1.length), hcr_orig] at h1
              have h2 := Option.some.inj h1
              simpa [hp1_eq] using h2
            fr_split
            · -- `p + 1 < end`
              fr_split
              · -- `cr ≠ cref`: write `(w0, cr)` at `(q, q + 1)`, advance `p + 2`, `q + 2`
                have hq1_eq : (q + 1#64).toNat = q.toNat + 1 := by bv_omega
                have hq2_eq : (q + 2#64).toNat = q.toNat + 2 := by bv_omega
                have hq1_w : (q + 1#64).toNat < wstk1.length := by omega
                fr_steps
                let wstk2 := (wstk1.set q.toNat w0).set (q.toNat + 1) cr
                have hm_eq : (wstk1.set q.toNat w0).set (q + 1#64).toNat
                    (wstk1[(p + 1#64).toNat]'hp1_w) = wstk2 := by
                  simp only [wstk2, hq1_eq, hcr_eq]
                refine hLoop1 (p + 1#64 + 1#64, q + 2#64, ()) m (by dsimp only; rw [hp2_eq]; omega)
                  ⟨by rw [hq2_eq]; omega, by rw [hp2_eq, hq2_eq]; omega, by rw [hp2_eq]; omega,
                   wstk2, by simp [wstk2, hlen1],
                   fun i hi => by
                     rw [hp2_eq] at hi; dsimp only [wstk2]
                     rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                     exact hout1 i (by omega),
                   by simpa [hp2_eq, show end0 - (p.toNat + 2) = end0 - p.toNat - 2 by omega]
                     using hrem',
                   ?_, by rw [← hm_eq]; exact hm⟩
                rw [hq2_eq, show q.toNat + 2 - off0 = (q.toNat - off0) + 2 by omega]
                refine ModeWatchSliceOk.append_pair (k := { s.core with wstk := wstk1 })
                  (k' := { s.core with wstk := wstk2 }) (p := off0) (p' := off0)
                  (Nat.le_refl _) (fun _ r => r)
                  (fun j hj => by
                    dsimp only [wstk2]
                    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]) hpre1
                  ?_ ?_ hlg hsz3 hcr_lt hcr_ref
                · dsimp only [wstk2]
                  rw [show off0 + (q.toNat - off0) = q.toNat by omega,
                    List.getElem?_set_ne (by omega), List.getElem?_set_self hq_w]
                · dsimp only [wstk2]
                  rw [show off0 + (q.toNat - off0) + 1 = q.toNat + 1 by omega,
                    List.getElem?_set_self (by simp; omega)]
              · -- `cr == cref`: drop entry, advance `p + 2`
                fr_steps
                refine hLoop1 (p + 1#64 + 1#64, q, ()) m1 (by dsimp only; rw [hp2_eq]; omega)
                  ⟨hoq, by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, wstk1, hlen1,
                   fun i hi => by rw [hp2_eq] at hi; exact hout1 i (by omega),
                   by simpa [hp2_eq, show end0 - (p.toNat + 2) = end0 - p.toNat - 2 by omega]
                     using hrem',
                   hpre1, hm1⟩
            · -- `¬ (p + 1 < end)`: impossible
              exfalso
              have h1 := hc
              simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1
              rw [show (1 : BitVec 64).toNat = 1 from rfl] at h1
              omega
        · -- Loop 1 exit (`p = end0`): Loop 2 writes `0xFFFFFFFFu` on `[q, end0)`
          have hp_end : p.toNat = end0 := by
            have h1 := hc; simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1; omega
          fr_steps
          refine wp_loop_inv
            (fun (k, ()) m2 =>
              q.toNat ≤ k.toNat ∧ k.toNat ≤ end0 ∧
              ∃ wstk2 : List (BitVec 32), wstk2.length = c.wcap ∧
                (∀ i, i < q.toNat ∨ end0 ≤ i → wstk2[i]? = wstk1[i]?) ∧
                (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) m2)
            (fun (k, ()) _ => end0 - k.toNat)
            (fun J2 hLoop2 => ?_) ?_
          · fr_steps; exact hLoop2 (q, ()) m1 ⟨Nat.le_refl _, by omega, wstk1, hlen1,
              fun _ _ => rfl, hm1⟩
          · rintro J2 ⟨k, ⟨⟩⟩ m2 ⟨hqk, hke, wstk2, hlen2, hout2, hm2⟩ hLoop2
            fr_split
            · have hk_lt : k.toNat < end0 := by
                have h1 := hc; simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1; omega
              have hk1_eq : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
              fr_steps
              exact hLoop2 (k + 1#64, ()) m (by dsimp only; rw [hk1_eq]; omega)
                ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega, wstk2.set k.toNat 0xFFFFFFFF#32,
                 by simp [hlen2],
                 fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hout2 i hi, hm⟩
            · -- Exit loop 2: update `wvec[2*lit + 1] = q - off`, `wusable += end - q`
              have hqoff_bv : (q - offW.setWidth 64).setWidth 32
                  = BitVec.ofNat 32 (q.toNat - off0) := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_setWidth, BitVec.toNat_sub, zext_toNat offW (by decide), hoff_eq]
                have hlt32 : q.toNat - off0 < 2 ^ 32 := by omega
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
                have : (2 ^ 64 - off0 + q.toNat) % 2 ^ 64 = q.toNat - off0 := by omega
                rw [this, Nat.mod_eq_of_lt hlt32]
              have hout_fin : ∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstk2[i]? = s.core.wstk[i]? := by
                intro i hi
                rw [hout2 i (by omega), hout1 i (by omega)]
              have hslice_fin : ModeWatchSliceOk dense F_cur { s.core with wstk := wstk2 }
                  lit.toNat off0 (q.toNat - off0) :=
                ModeWatchSliceOk.relocate (k := { s.core with wstk := wstk1 })
                  (k' := { s.core with wstk := wstk2 }) (p := off0) (p' := off0)
                  (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
                  (fun _ r => r) (fun j hj => hout2 (off0 + j) (Or.inl (by omega))) hpre1
              fr_steps
              let wvec' := s.core.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (q.toNat - off0))
              let wu' := s.core.wusable + ((offW.setWidth 64 + szW.setWidth 64) - q)
              have hw' : ModeWatchesInv F_cur
                  { s.core with wvec := wvec', wstk := wstk2, wusable := wu' } := by
                simpa [wvec', wu', off0, sz0, dense] using
                  modeWatchesInv_shrink_slice hw.watches hlen.core_ok hlit_lt
                    (new_sz := q.toNat - off0) (show q.toNat - off0 ≤ sz0 by omega)
                    hout_fin wu' s.core.num_binary hslice_fin
              have hwv_eq :
                  s.core.wvec.set ((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat
                    ((q - offW.setWidth 64).setWidth 32) = wvec' := by
                simp only [wvec', h2l1_eq, hqoff_bv]
              exact hQ wvec' wstk2 wu' m
                ⟨{ hlen.core_ok with wvec_len := by simp [wvec', hwv_len], wstk_len_arr := hlen2 },
                 hlen.scratch_ok⟩
                { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hw' }
                (by rw [← hwv_eq]; exact hm)

namespace FullReduceHelpers

theorem full_sweep_bins_finish_lit {c : FullCfg} {F_cur : List (List Nat)}
    {kL : FullCoreState} {sc : FullScratch} {wstk1 wstk2 : List (BitVec 32)}
    {wu' nb1 : BitVec 64} {l q_nat : Nat}
    (hlenL : kL.LengthsOk c) (hscrL : sc.LengthsOk c) (hwatL : ModeWatchesInv F_cur kL)
    (hbinL : ∀ j < l, BinOnlyWatchSliceOk F_cur kL j (fullWatchOffCore kL j)
      (fullWatchSizeCore kL j))
    (hl_lt : l < 2 * kL.cur_vars) (hlen2 : wstk2.length = c.wcap)
    (hoq : fullWatchOffCore kL l ≤ q_nat)
    (hqe : q_nat ≤ fullWatchOffCore kL l + fullWatchSizeCore kL l)
    (hout1 : ∀ i, i < fullWatchOffCore kL l ∨ fullWatchOffCore kL l + fullWatchSizeCore kL l ≤ i →
      wstk1[i]? = kL.wstk[i]?)
    (hout2 : ∀ i, i < q_nat ∨ fullWatchOffCore kL l + fullWatchSizeCore kL l ≤ i →
      wstk2[i]? = wstk1[i]?)
    (hpre1 : BinOnlyWatchSliceOk F_cur { kL with wstk := wstk1 } l (fullWatchOffCore kL l)
      (q_nat - fullWatchOffCore kL l))
    (kL' : FullCoreState)
    (hk' : kL' = { kL with wvec := kL.wvec.set (2 * l + 1)
                                     (BitVec.ofNat 32 (q_nat - fullWatchOffCore kL l)),
                           wstk := wstk2, wusable := wu', num_binary := nb1 }) :
    FullState.LengthsOk c ⟨kL', sc⟩ ∧ ModeWatchesInv F_cur kL' ∧
    ∀ j < l + 1, BinOnlyWatchSliceOk F_cur kL' j (fullWatchOffCore kL' j)
      (fullWatchSizeCore kL' j) := by
  subst hk'
  let off0 := fullWatchOffCore kL l; let sz0 := fullWatchSizeCore kL l
  let wvec' := kL.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q_nat - off0))
  have hout_fin : ∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstk2[i]? = kL.wstk[i]? :=
    fun i hi => by rw [hout2 i (by omega), hout1 i (by omega)]
  have hbin_l : BinOnlyWatchSliceOk F_cur { kL with wstk := wstk2 } l off0 (q_nat - off0) :=
    BinOnlyWatchSliceOk.relocate (k := { kL with wstk := wstk1 }) (k' := { kL with wstk := wstk2 })
      (p := off0) (p' := off0) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun j hj => hout2 (off0 + j) (Or.inl (by omega))) hpre1
  have hmode_l : ModeWatchSliceOk (decide (kL.dense_mode ≠ 0#64)) F_cur { kL with wstk := wstk2 }
      l off0 (q_nat - off0) := by
    by_cases hd : decide (kL.dense_mode ≠ 0#64) = true
    · simp only [ModeWatchSliceOk, hd, ↓reduceIte]; exact hbin_l.toDenseWatchSliceOk
    · simp only [ModeWatchSliceOk, hd, Bool.false_eq_true, ↓reduceIte]; exact hbin_l.toWatchSliceOk
  have hwat' := modeWatchesInv_shrink_slice hwatL hlenL hl_lt (new_sz := q_nat - off0) (by omega)
    hout_fin wu' nb1 hmode_l
  obtain ⟨_, hoff_self, hsz_self, hother⟩ :=
    watchStackLayout_shrink_slice hwatL.layout hlenL hl_lt
      (new_sz := q_nat - off0) (by omega) hout_fin hbin_l.ne_sentinel wu' nb1
  refine ⟨⟨{ hlenL with wvec_len := by simp [hlenL.wvec_len],
                        wstk_len_arr := hlen2 }, hscrL⟩, hwat', fun j hj => ?_⟩
  by_cases hjl : j = l
  · subst j; rw [hoff_self, hsz_self]
    exact BinOnlyWatchSliceOk.relocate (k := { kL with wstk := wstk2 })
      (k' := { kL with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 })
      (p := off0) (p' := off0) (by rw [CNF.entails_def]; exact fun _ p => p)
      (Nat.le_refl _) (fun _ _ => rfl) hbin_l
  · obtain ⟨ho, hs, hws⟩ := hother j (by omega) hjl; rw [ho, hs]
    exact BinOnlyWatchSliceOk.relocate (k := kL)
      (k' := { kL with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 })
      (p := fullWatchOffCore kL j) (p' := fullWatchOffCore kL j)
      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _) hws (hbinL j (by omega))

end FullReduceHelpers

theorem full_sweep_bins_wp (Γ : Env)
    (hdefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsSpec a m Q X → Func.wp Γ full_sweep_bins_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr
  have hwl_le := hlen.core_ok.wlen_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hwcap_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  let dense : Bool := decide (s.core.dense_mode ≠ 0#64)
  have hnlits_eq :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_shl1_toNat (by omega), h1]
  fr_steps
  refine wp_loop_inv
    (fun (l, ()) mL =>
      l.toNat ≤ 2 * s.core.cur_vars ∧
      ∃ wvecL wstkL wuL nbL,
        let sL : FullState :=
          { s with core := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL,
                                         num_binary := nbL } }
        sL.LengthsOk c ∧ ModeWatchesInv F_cur sL.core ∧
        (∀ j < l.toNat,
          BinOnlyWatchSliceOk F_cur sL.core j (fullWatchOff sL j) (fullWatchSize sL j)) ∧
        (FullMem c sL ⋆ R) mL)
    (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
    (fun JL hLoopL => ?_) ?_
  · fr_steps
    exact hLoopL (0#64, ()) m ⟨Nat.zero_le _, s.core.wvec, s.core.wstk, s.core.wusable,
      s.core.num_binary, hlen, hw.watches, fun _ hj => absurd hj (Nat.not_lt_zero _), hm⟩
  · rintro JL ⟨l, ⟨⟩⟩ mL ⟨hl_le, wvecL, wstkL, wuL, nbL, hlenL, hwatL, hbinL, hmL⟩ hLoopL
    let sL : FullState :=
      { s with core := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL,
                                     num_binary := nbL } }
    have hwvL_len : wvecL.length = 4 * c.max_vars := hlenL.core_ok.wvec_len
    fr_split
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        have : l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        omega
      have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := bv64_add1 (by omega)
      have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
      have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
        rw [bv64_add1 (by omega), h2l_eq]
      have h2l_lt : 2 * l.toNat < wvecL.length := by omega
      have h2l1_lt : 2 * l.toNat + 1 < wvecL.length := by omega
      have hmod0 : 2 * l.toNat % 2 ^ 64 = 2 * l.toNat := Nat.mod_eq_of_lt (by omega)
      have hmod1 : (2 * l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * l.toNat + 1 := by
        rw [show (1 : BitVec 64).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
      let off0 : Nat := fullWatchOff sL l.toNat
      let sz0 : Nat := fullWatchSize sL l.toNat
      let offW : BitVec 32 := wvecL[(l <<< (1 : Nat)).toNat]'(by omega)
      let szW : BitVec 32 := wvecL[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by omega)
      have hoff_idx : (wvecL[2 * l.toNat]'h2l_lt).toNat = off0 := by
        unfold off0 fullWatchOff fullWatchOffCore sL
        rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
      have hsz_idx : (wvecL[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
        unfold sz0 fullWatchSize fullWatchSizeCore sL
        rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
      have hoff_eq : offW.toNat = off0 := by unfold offW; simp only [h2l_eq]; exact hoff_idx
      have hsz_eq : szW.toNat = sz0 := by unfold szW; simp only [h2l1_eq]; exact hsz_idx
      have hbd_end : off0 + sz0 ≤ s.core.wlen := hwatL.bounds l.toNat hl_lt
      have hslice0 : ModeWatchSliceOk dense F_cur sL.core l.toNat off0 sz0 :=
        modeWatchesInv_slice_of_lt hwatL hl_lt
      clear hwv_len hws_len hw hlen hdefrag hQ
      fr_split
      · -- `sz == 0`: advance `l + 1`
        have hsz0 : sz0 = 0 := by
          have h1 := congrArg BitVec.toNat hc
          simp only [hmod1] at h1
          rw [zext_toNat (wvecL[2 * l.toNat + 1]'h2l1_lt) (by decide), hsz_idx] at h1
          exact h1
        fr_steps
        refine hLoopL (l + (1 : BitVec 64), ()) mL (by dsimp only; rw [hl1_eq]; omega)
          ⟨by rw [hl1_eq]; omega, wvecL, wstkL, wuL, nbL, hlenL, hwatL, fun j hj => ?_, hmL⟩
        rw [hl1_eq] at hj
        by_cases hjl : j = l.toNat
        · subst hjl; change BinOnlyWatchSliceOk F_cur sL.core l.toNat off0 sz0
          rw [hsz0]; exact .empty
        · exact hbinL j (by omega)
      · -- `sz > 0`: compute `lfix`, scan `[off0, off0 + sz0)` keeping only live binary watches
        have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv64_shr1_toNat l
        have hlv_lt : (l >>> (1 : Nat)).toNat < s.core.lvl.length := by rw [hlv_eq]; omega
        have hl_v : l.toNat < s.core.vals.length := by omega
        let end0 : Nat := off0 + sz0
        fr_to_group
        refine wp_join_group (fun (_lfix, ()) mF => mL = mF) ?_ ?_
        · rintro _ ⟨lfix, ⟨⟩⟩ _ rfl
          fr_steps
          refine wp_loop_inv
            (fun (p, q, ()) m1 =>
              off0 ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end0 ∧
              ∃ wstk1 nb1, wstk1.length = c.wcap ∧
                (∀ i, i < off0 ∨ p.toNat ≤ i → wstk1[i]? = wstkL[i]?) ∧
                ModeWatchSliceOk dense F_cur sL.core l.toNat p.toNat (end0 - p.toNat) ∧
                BinOnlyWatchSliceOk F_cur
                  { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL, num_binary := nbL }
                  l.toNat off0 (q.toNat - off0) ∧
                (FullMem c { s with core := { s.core with wvec := wvecL, wstk := wstk1,
                                                          wusable := wuL, num_binary := nb1 } } ⋆
                  R) m1)
            (fun (p, _, ()) _ => end0 - p.toNat)
            (fun J1 hLoop1 => ?_) ?_
          · fr_steps
            have hoff64 : (offW.setWidth 64).toNat = off0 := by
              rw [zext_toNat offW (by decide), hoff_eq]
            refine hLoop1 _ mL ⟨by rw [hoff64]; exact Nat.le_refl _,
              by rw [hoff64]; exact Nat.le_refl _, by rw [hoff64]; omega,
              wstkL, nbL, hlenL.core_ok.wstk_len_arr, fun _ _ => rfl, ?_, ?_, hmL⟩
            · rw [hoff64, show end0 - off0 = sz0 by omega]; exact hslice0
            · rw [hoff64, Nat.sub_self]; exact .empty
          · rintro J1 ⟨p, q, ⟨⟩⟩ m1 ⟨hoq, hqp, hpe, wstk1, nb1, hlen1, hout1, hrem1, hpre1, hm1⟩
              hLoop1
            fr_split
            · have hp_lt : p.toNat < end0 := by
                have h1 := hc; simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1; omega
              have hp_w : p.toNat < wstk1.length := by omega
              have hq_w : q.toNat < wstk1.length := by omega
              let w0 := wstk1[p.toNat]'hp_w
              have hw0_orig : sL.core.wstk[p.toNat]? = some w0 := by
                dsimp only [sL]
                rw [← hout1 p.toNat (Or.inr (Nat.le_refl _)), List.getElem?_eq_getElem hp_w]
              have hstep := hrem1.step (by omega) hw0_orig
              fr_split
              · -- Binary watch
                have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                  change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) ≠ 0#32; assumption
                obtain ⟨hne, hlt_o, hent_o, hrem'⟩ := hstep.1 hbin
                have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 :=
                  bv64_add1 (by omega)
                have hq1_eq : (q + (1 : BitVec 64)).toNat = q.toNat + 1 :=
                  bv64_add1 (by omega)
                have hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := hlt_o
                have hot_sh : ((w0 &&& 0x7FFFFFFF#32) >>> 1#32).toNat =
                    (w0 &&& 0x7FFFFFFF#32).toNat / 2 := bv32_shr1_toNat _
                have hot_lvl : ((w0 &&& 0x7FFFFFFF#32) >>> 1#32).toNat < s.core.lvl.length := by
                  rw [hot_sh]; omega
                have hot_v : (w0 &&& 0x7FFFFFFF#32).toNat < s.core.vals.length := by omega
                fr_to_group
                refine wp_join_group (fun (_ofix, ()) mO => m1 = mO) ?_ ?_
                · rintro _ ⟨ofix, ⟨⟩⟩ _ rfl
                  fr_to_group
                  refine wp_join_group (fun (q', ()) mQ =>
                    off0 ≤ q'.toNat ∧ q'.toNat ≤ p.toNat + 1 ∧
                    ∃ wstk' nb', wstk'.length = c.wcap ∧
                      (∀ i, i < off0 ∨ p.toNat + 1 ≤ i → wstk'[i]? = wstkL[i]?) ∧
                      BinOnlyWatchSliceOk F_cur
                        { s.core with wvec := wvecL, wstk := wstk', wusable := wuL,
                                      num_binary := nbL }
                        l.toNat off0 (q'.toNat - off0) ∧
                      (FullMem c { s with core := { s.core with wvec := wvecL, wstk := wstk',
                                                                wusable := wuL,
                                                                num_binary := nb' } } ⋆ R) mQ)
                    ?_ ?_
                  · rintro _ ⟨q', ⟨⟩⟩ mQ ⟨hoq', hqp', wstk', nb', hlen', hout', hpre', hmQ⟩
                    fr_steps
                    exact hLoop1 (p + (1 : BitVec 64), q', ()) mQ
                      (by dsimp only; rw [hp1_eq]; omega)
                      ⟨hoq', by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, wstk', nb', hlen',
                       by rw [hp1_eq]; exact hout',
                       by rw [hp1_eq, show end0 - (p.toNat + 1) = end0 - p.toNat - 1 by omega]
                          exact hrem',
                       hpre', hmQ⟩
                  · intro Jq hJq
                    fr_to_group
                    refine wp_join_group (fun () mD => m1 = mD) ?_ ?_
                    · rintro _ ⟨⟩ mD hmD
                      subst mD
                      fr_steps
                      · -- `l < ot ∧ num_binary > 0`
                        exact hJq (q, ()) m ⟨hoq, by omega, wstk1, nb1 - (1 : BitVec 64), hlen1,
                          fun i hi => hout1 i (by omega), hpre1, fullMem_cast hm rfl⟩
                      · -- `l < ot`, `num_binary = 0`
                        exact hJq (q, ()) m1 ⟨hoq, by omega, wstk1, nb1, hlen1,
                          fun i hi => hout1 i (by omega), hpre1, hm1⟩
                      · -- `¬(l < ot)`
                        exact hJq (q, ()) m1 ⟨hoq, by omega, wstk1, nb1, hlen1,
                          fun i hi => hout1 i (by omega), hpre1, hm1⟩
                    · intro Jd hJd
                      fr_steps
                      · exact hJd () m1 rfl
                      · exact hJd () m1 rfl
                      · -- `lfix = false`, `ofix = false`, `lfix = true` (skip)
                        exact hJq (q, ()) m1 ⟨hoq, by omega, wstk1, nb1, hlen1,
                          fun i hi => hout1 i (by omega), hpre1, hm1⟩
                      · -- `!lfix && !ofix`: `wstk[q] = w0; q = q + 1`
                        refine hJq (q + (1 : BitVec 64), ()) m
                          ⟨by rw [hq1_eq]; omega, by rw [hq1_eq]; omega,
                           wstk1.set q.toNat w0, nb1, List.length_set.trans hlen1,
                           fun i hi => by
                             rw [List.getElem?_set_ne (by omega)]; exact hout1 i (by omega),
                           ?_, fullMem_cast hm rfl⟩
                        rw [hq1_eq, show q.toNat + 1 - off0 = (q.toNat - off0) + 1 by omega]
                        exact BinOnlyWatchSliceOk.append_bin
                          (k := { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL,
                                              num_binary := nbL })
                          (k' := { s.core with wvec := wvecL, wstk := wstk1.set q.toNat w0,
                                               wusable := wuL, num_binary := nbL })
                          (p := off0) (p' := off0) (Nat.le_refl _)
                          (fun j hj => List.getElem?_set_ne (by omega)) hpre1
                          (by rw [show off0 + (q.toNat - off0) = q.toNat by omega]
                              exact List.getElem?_set_self hq_w)
                          hbin hne hlt_o hent_o
                · intro Jo hJo
                  clear hLoopL JL hLoop1 hJ J1 hbinL hwatL hlenL hslice0 hrem1 hpre1 hout1 hstep
                  fr_steps <;> exact hJo _ m1 rfl
              · -- Non-binary watch: drop (advance `p + 2`)
                have hlg : (w0 &&& 0x80000000#32) = 0#32 := by
                  change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) = 0#32; assumption
                obtain ⟨h2rem, _, _, _, _, _, hrem'⟩ := hstep.2 hlg
                have hp2_eq : (p + (2 : BitVec 64)).toNat = p.toNat + 2 :=
                  bv64_add2 (by omega)
                fr_steps
                apply hJ; fr_steps
                exact hLoop1 (p + (2 : BitVec 64), q, ()) m1 (by dsimp only; rw [hp2_eq]; omega)
                  ⟨hoq, by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, wstk1, nb1, hlen1,
                   fun i hi => by rw [hp2_eq] at hi; exact hout1 i (by omega),
                   by rw [hp2_eq, show end0 - (p.toNat + 2) = end0 - p.toNat - 2 by omega]
                      exact hrem',
                   hpre1, hm1⟩
            · -- Exit inner loop 1 (`p = end0`): zero `[q, end0)` with `0xFFFFFFFFu`
              have hp_end : p.toNat = end0 := by
                have h1 := hc; simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1; omega
              clear hrem1 hslice0 hLoop1 J1
              fr_steps
              refine wp_loop_inv
                (fun (k, ()) m2 =>
                  q.toNat ≤ k.toNat ∧ k.toNat ≤ end0 ∧
                  ∃ wstk2 : List (BitVec 32), wstk2.length = c.wcap ∧
                    (∀ i, i < q.toNat ∨ end0 ≤ i → wstk2[i]? = wstk1[i]?) ∧
                    (FullMem c { s with core := { s.core with wvec := wvecL, wstk := wstk2,
                                                              wusable := wuL,
                                                              num_binary := nb1 } } ⋆ R) m2)
                (fun (k, ()) _ => end0 - k.toNat)
                (fun J2 hLoop2 => ?_) ?_
              · fr_steps; exact hLoop2 (q, ()) m1 ⟨Nat.le_refl _, by omega, wstk1, hlen1,
                  fun _ _ => rfl, hm1⟩
              · rintro J2 ⟨k, ⟨⟩⟩ m2 ⟨hqk, hke, wstk2, hlen2, hout2, hm2⟩ hLoop2
                fr_split
                · have hk_lt : k.toNat < end0 := by
                    have h1 := hc; simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1; omega
                  have hk1_eq : (k + (1 : BitVec 64)).toNat = k.toNat + 1 :=
                    bv64_add1 (by omega)
                  fr_steps
                  exact hLoop2 (k + (1 : BitVec 64), ()) m (by dsimp only; rw [hk1_eq]; omega)
                    ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega,
                     wstk2.set k.toNat 0xFFFFFFFF#32, List.length_set.trans hlen2,
                     fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hout2 i hi,
                     fullMem_cast hm rfl⟩
                · -- Update `wvec[2*l + 1] = q - off`, `wusable += end - q`, advance `l + 1`
                  have hqoff_bv : (q - offW.setWidth 64).setWidth 32
                      = BitVec.ofNat 32 (q.toNat - off0) := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_setWidth, BitVec.toNat_sub, zext_toNat offW (by decide),
                      hoff_eq]
                    have hlt32 : q.toNat - off0 < 2 ^ 32 := by omega
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
                    have : (2 ^ 64 - off0 + q.toNat) % 2 ^ 64 = q.toNat - off0 := by omega
                    rw [this, Nat.mod_eq_of_lt hlt32]
                  fr_steps
                  let wvec' := wvecL.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat - off0))
                  let wu' := wuL + ((offW.setWidth 64 + szW.setWidth 64) - q)
                  obtain ⟨hlen', hwat', hbin'⟩ := full_sweep_bins_finish_lit
                    hlenL.core_ok hlenL.scratch_ok hwatL hbinL
                    hl_lt hlen2 hoq (show q.toNat ≤ end0 by omega)
                    (fun i hi => hout1 i (by change i < off0 ∨ end0 ≤ i at hi; omega))
                    hout2 hpre1
                    { s.core with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 }
                    rfl
                  have hwv_eq :
                      wvecL.set ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat
                        ((q - offW.setWidth 64).setWidth 32) = wvec' := by
                    dsimp only [wvec']; rw [h2l1_eq, hqoff_bv]
                  have hst_eq :
                      ({ s with core := { s.core with
                          wvec := wvecL.set ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat
                            ((q - offW.setWidth 64).setWidth 32),
                          wstk := wstk2, wusable := wu', num_binary := nb1 } } : FullState) =
                      { s with core := { s.core with wvec := wvec', wstk := wstk2,
                                                     wusable := wu', num_binary := nb1 } } :=
                    congrArg (fun wv =>
                      { s with core := { s.core with wvec := wv, wstk := wstk2,
                                                     wusable := wu', num_binary := nb1 } })
                      hwv_eq
                  exact hLoopL (l + (1 : BitVec 64), ()) m (by dsimp only; rw [hl1_eq]; omega)
                    ⟨by rw [hl1_eq]; omega, wvec', wstk2, wu', nb1, hlen', hwat',
                     by rw [hl1_eq]; exact hbin', fullMem_cast hm hst_eq⟩
        · intro Jf hJf
          clear hLoopL JL hbinL hwatL hlenL hslice0 hbd_end
          fr_steps <;> exact hJf _ mL rfl
    · -- Exit outer loop (`l = 2 * cur_vars`): call `full_wstack_defrag`
      have hl_end : l.toNat = 2 * s.core.cur_vars := by
        have : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat ≤ l.toNat := by c0_bound
        omega
      have hbin_all : BinOnlyWatchesInv F_cur sL.core :=
        ⟨hwatL.layout, fun j hj => hbinL j (hl_end ▸ hj)⟩
      fr_steps; c0_call hdefrag
      refine ⟨c, sL, R, rfl, hlenL, hwatL.layout, hmL,
        fun wvec' wstk' wlen' wsort' m' hlen' hlay' _ hpres hm' => ?_⟩
      let sF : FullState :=
        { core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
                                num_binary := nbL }
          scratch := { s.scratch with wsort := wsort' } }
      have hbinF : BinOnlyWatchesInv F_cur sF.core :=
        fullWstackDefrag_preserves_binOnly hbin_all hlay' rfl hpres
      fr_steps
      exact hQ wvec' wstk' wlen' nbL wsort' m' hlen' hbinF hbinF.toFull hbinF.toDenseWatchesInv
        { hw with arena := { hw.arena with len_ok := hw.arena.len_ok },
                  watches := hbinF.toModeWatchesInv } hm'

end LeanQbe.T.Examples.Kissat.Full
