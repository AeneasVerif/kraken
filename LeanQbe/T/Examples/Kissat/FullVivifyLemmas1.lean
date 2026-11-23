module

public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.Full3
import LeanQbe.T.Logic.C0Step

/-!
# Kissat `D-Full` Tiered Clause Vivification Proofs — Part 1 (`Stage 4`)

Builds on `FullArena`, `FullInv2`, and `Full3` to provide:
1. Shared Stage-4 UNSAT-only invariants (`FullLitMarksClear`, `FullSparseInv`) and strictly scoped
   tactic helpers (`FullVivifyTactics`).
2. Core arena/watch preservation lemmas for vivification:
   - `fullArena_setHdr_preserves_fullCore` (`PH_VIV` set/clear)
   - `fullArena_updateLits_preserves_fullCore` (level-0 in-place literal compaction)
   - `inPlaceShrink_preserves_fullCore` (`3 ≤ nsz < old_sz` with `PH_SHRK` + `0xFFFFFFFF#32`)
   - `fullWatchPush_large_preserves_sparseInv` (sparse 2WL large watch append)
   - `fullArenaClauseRefs_zero_mem`, `fullArenaClauseRefs_next_mem_or_end`, `entails_filter_level0`
3. Parametric callee `Spec` contracts for `full_arena_next`, `full_unwatch_large`,
   `full_watch_push`, `full_add_unit`, `full_add_bin`, `full_assign`, `full_backtrack`,
   `full_propagate_ignore`, and `full_propagate`.
4. Parametric `Func.wp` proof for `full_viv_sort_lits`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Shared invariants (`FullVivifySpecs`) & scoped tactics (`FullVivifyTactics`) -/

namespace FullVivifySpecs

/-- Both variable mark array (`< c.max_vars`) and literal mark array (`< 2 * c.max_vars`) are
completely cleared to `0#8`. -/
@[expose] def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Every non-garbage arena clause has pairwise distinct variable indices. -/
@[expose] def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- Every entry of `last_learned[0..7]` is either `0xFFFFFFFF#32` or a live arena block ref. -/
@[expose] def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Soundness-relevant scratch invariants (`last_learned` refs + `extend_len ≤ extend_cap`). -/
@[expose] def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Canonical sparse 2WL `D-Full` invariant with explicit current formula. -/
@[expose]
def FullSparseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) :
    Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Canonical sparse 2WL `D-Full` solver invariant. -/
@[expose] def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
    FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

end FullVivifySpecs

namespace FullVivifyTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "fv_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "fv_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "fv_step" : tactic => `(tactic| ((try fv_unmdata); (repeat fv_strip); c0_step))
scoped macro "fv_steps" : tactic =>
  `(tactic| (
      (try fv_unmdata)
      (repeat fv_strip)
      c0_steps
      repeat (any_goals (fv_strip; repeat fv_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
scoped elab "fv_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty ← Lean.instantiateMVars (← g.getType)
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

theorem bv8_sext32_eq0_iff : ∀ x : BitVec 8, x.signExtend 32 = 0#32 ↔ x = 0#8 := by
  decide

theorem bv8_dom_sgt0_iff {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#32).slt (x.signExtend 32) = true ↔ x = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bv8_dom_slt0_iff {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

private theorem mask19_bit : ∀ i : Fin 32, (0x00080000#32)[i.val] = decide (i.val = 19) := by decide
private theorem mask20_bit : ∀ i : Fin 32, (0x00100000#32)[i.val] = decide (i.val = 20) := by decide
private theorem mask22_bit : ∀ i : Fin 32, (0x00400000#32)[i.val] = decide (i.val = 22) := by decide
private theorem mask23_bit : ∀ i : Fin 32, (0x00800000#32)[i.val] = decide (i.val = 23) := by decide
private theorem maskN20_bit :
    ∀ i : Fin 32, (0xFFEFFFFF#32)[i.val] = decide (i.val ≠ 20) := by decide
private theorem maskN22_bit :
    ∀ i : Fin 32, (0xFFBFFFFF#32)[i.val] = decide (i.val ≠ 22) := by decide
private theorem mask31_bit : ∀ i : Fin 32, (0x80000000#32)[i.val] = decide (i.val = 31) := by decide
private theorem maskLo31_bit :
    ∀ i : Fin 32, (0x7FFFFFFF#32)[i.val] = decide (i.val < 31) := by decide

theorem bv32_or_viv_garb (h : BitVec 32) :
    ((h ||| 0x00100000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, mask19_bit ⟨i, hi⟩, mask20_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_or_viv_shrk (h : BitVec 32) :
    ((h ||| 0x00100000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, mask23_bit ⟨i, hi⟩, mask20_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_clr_viv_garb (h : BitVec 32) :
    ((h &&& ~~~0x00100000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  rw [show (~~~0x00100000#32 : BitVec 32) = 0xFFEFFFFF#32 from rfl]
  ext i hi
  simp only [BitVec.getElem_and, mask19_bit ⟨i, hi⟩, maskN20_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_clr_viv_shrk (h : BitVec 32) :
    ((h &&& ~~~0x00100000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  rw [show (~~~0x00100000#32 : BitVec 32) = 0xFFEFFFFF#32 from rfl]
  ext i hi
  simp only [BitVec.getElem_and, mask23_bit ⟨i, hi⟩, maskN20_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_clr_red_garb (h : BitVec 32) :
    ((h &&& ~~~0x00400000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  rw [show (~~~0x00400000#32 : BitVec 32) = 0xFFBFFFFF#32 from rfl]
  ext i hi
  simp only [BitVec.getElem_and, mask19_bit ⟨i, hi⟩, maskN22_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_clr_red_shrk (h : BitVec 32) :
    ((h &&& ~~~0x00400000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  rw [show (~~~0x00400000#32 : BitVec 32) = 0xFFBFFFFF#32 from rfl]
  ext i hi
  simp only [BitVec.getElem_and, mask23_bit ⟨i, hi⟩, maskN22_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_or_shrk_garb (h : BitVec 32) :
    ((h ||| 0x00800000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, mask19_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_or_garb_shrk (h : BitVec 32) :
    ((h ||| 0x00080000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, mask19_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_or_shrk_ne0 (h : BitVec 32) :
    ((h ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := by
  intro heq; have h23 := congrArg (·[23]) heq
  revert h23; simp [show (0x00800000#32)[23] = true from rfl]

theorem bv32_mask_lo31_props (x : BitVec 32) :
    ((x &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧ (x &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  constructor
  · ext i hi
    simp only [BitVec.getElem_and, mask31_bit ⟨i, hi⟩, maskLo31_bit ⟨i, hi⟩, BitVec.getElem_zero hi]
    by_cases h31 : i = 31 <;> simp [h31]
  · intro heq; have h31 := congrArg (·[31]) heq
    revert h31; simp [show (0x7FFFFFFF#32)[31] = false from rfl,
      show (0xFFFFFFFF#32)[31] = true from rfl]

theorem bv32_ne_sentinel_of_lt {x : BitVec 32} (hlt : x.toNat < 0x80000000) :
    x ≠ 0xFFFFFFFF#32 := by
  intro heq; subst heq; revert hlt; decide

end FullVivifyTactics

section

open FullVivifyTactics FullVivifySpecs
open scoped FullArenaTactics FullVivifyTactics

/-! ## 2. Core arena, watch, and level-0 preservation lemmas (`FullVivifyHelpers`) -/

namespace FullVivifyHelpers

theorem fv_with_scratch {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  ⟨h.1.with_scratch (h.1.lengths.with_scratch hok) rfl, h.2.1, h.2.2.1,
    ⟨fun i hi => by simpa [FullLastLearnedWf, hll] using h.2.2.2.1.1 i hi,
      by simpa [hext] using h.2.2.2.1.2⟩, h.2.2.2.2⟩

theorem fv_sparseW_to_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (h : FullSparseInvW c F0 F_cur s) : FullSparseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fv_with_oomW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (h : FullSparseInvW c F0 F_cur s) (v : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with oom := v } } :=
  ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    { h.2.1 with arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok },
                 watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fv_with_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (v : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with probing := v } } := by
  obtain ⟨⟨hlen, F_cur, hw⟩, hmc, hnd, hext, hdm⟩ := h
  refine ⟨⟨⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len }, hlen.scratch_ok⟩, F_cur,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok },
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }⟩,
    hmc, hnd, hext, hdm⟩

theorem fv_with_confl {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (ct cr : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with confl_type := ct, confl_ref := cr } } := by
  obtain ⟨⟨hlen, F_cur, hw⟩, hmc, hnd, hext, hdm⟩ := h
  refine ⟨⟨⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len }, hlen.scratch_ok⟩, F_cur,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok },
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }⟩,
    hmc, hnd, hext, hdm⟩

theorem fv_with_tmp {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tmp' : List (BitVec 32)} (ht : tmp'.length = c.max_vars) :
    FullSparseInv c F0 { s with core := { s.core with tmp := tmp' } } := by
  obtain ⟨⟨hlen, F_cur, hw⟩, hmc, hnd, hext, hdm⟩ := h
  refine ⟨⟨⟨{ hlen.core_ok with tmp_len_arr := ht }, hlen.scratch_ok⟩, F_cur,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok },
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }⟩,
    hmc, hnd, hext, hdm⟩

private theorem bit19_or_garb_ne0_viv (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have h19 := congrArg (·[19]) h
  revert h19; simp [show (0x00080000#32)[19] = true from rfl]

theorem fv_witness_markGarb_level0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (ag' : BitVec 64)
    (hnd_other : ∀ r ∈ fullArenaClauseRefs s, r ≠ cref → fullArenaClauseGarb s r = false →
      ((fullArenaClauseLits s r).map (· / 2)).Nodup) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧
      fullArenaClauseRefs s' = fullArenaClauseRefs s ∧ FullArenaVarsNodup s' ∧
      (∀ q ∈ fullArenaClauseRefs s,
        fullArenaNextOff s'.core.arena s.core.arena_len q =
          fullArenaNextOff s.core.arena s.core.arena_len q) := by
  intro s'
  have hcl := hlen.core_ok
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hlen.scratch_ok⟩
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  have har_len : cref < s.core.arena.length := by
    have := (hw.arena.refs_wf cref href).1
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have hnxt : ∀ q ∈ fullArenaClauseRefs s,
      fullArenaNextOff s'.core.arena s.core.arena_len q =
        fullArenaNextOff s.core.arena s.core.arena_len q := by
    intro q hq
    by_cases hqc : q = cref
    · subst q
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by
        have := (hw.arena.refs_wf cref href).1; omega
      unfold fullArenaNextOff
      simp only [s', h1, ↓reduceIte, List.getElem?_set_self har_len, Option.getD_some,
        List.getElem?_set_ne (show cref ≠ cref + 2 by omega)]
      split
      · rfl
      · change (if ((fullArenaHdr s cref ||| 0x00080000#32) &&& 0x00800000#32) ≠ 0#32 then
            _ else _) =
          if (fullArenaHdr s cref &&& 0x00800000#32) ≠ 0#32 then _ else _
        rw [bv32_or_garb_shrk]; split
        · exact fullArenaSkipShrk_congr fun k hk1 _ =>
            List.getElem?_set_ne (by omega)
        · rfl
    · rcases Nat.lt_or_gt_of_ne hqc with hlt | hgt
      · have hdisj := fullArenaScanRefs_disjoint hq href hlt
        have hq_wf := hw.arena.refs_wf q hq
        exact fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hqc))
          (List.getElem?_set_ne (by omega)) fun k _ hk2 => List.getElem?_set_ne (by omega)
      · exact fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hqc))
          (List.getElem?_set_ne (by omega)) fun k hk1 _ => List.getElem?_set_ne (by omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := hmg.2
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hlv : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hw.lvl_le idx hidx; omega
        exact absurd (hw.level0_rsn_none idx hidx hlv) hne
      reason_lit_mem := fun idx hidx hne _ => by
        have hlv : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hw.lvl_le idx hidx; omega
        exact absurd (hw.level0_rsn_none idx hidx hlv) hne }
  refine ⟨hlen', hw', hrefs, fun r hr hng => ?_, hnxt⟩
  dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits] at hr hng ⊢
  rw [hrefs] at hr
  have hne : r ≠ cref := by
    rintro rfl; unfold fullArenaClauseGarbCore fullArenaHdrCore at hng
    dsimp only [s'] at hng; rw [List.getElem?_set_self har_len, Option.getD_some] at hng
    simp [bit19_or_garb_ne0_viv] at hng
  have hng0 : fullArenaClauseGarb s r = false := by
    unfold fullArenaClauseGarb
    unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
    dsimp only [s'] at hng; rwa [List.getElem?_set_ne (Ne.symm hne)] at hng
  have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hw.arena.disjoint hr href hlt)
    · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have hlits_eq : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
    (fullArenaClauseLitsCore_set_outside hbd hdisj).2
  rw [hlits_eq]; exact hnd_other r hr hne hng0

theorem fv_markGarbW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (h : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
      (∀ q ∈ fullArenaClauseRefs s,
        fullArenaNextOff s'.core.arena s.core.arena_len q =
          fullArenaNextOff s.core.arena s.core.arena_len q) := by
  intro s'
  obtain ⟨hlen', hw', hrefs, hnd', hnxt⟩ :=
    fv_witness_markGarb_level0 h.1 h.2.1 hl0 href ag' (fun r hr _ hng => h.2.2.2.1 r hr hng)
  exact ⟨⟨hlen', hw', h.2.2.1, hnd',
    ⟨fun i hi => by
      simpa [FullLastLearnedWf, fullArenaClauseRefs, s', hrefs] using h.2.2.2.2.1.1 i hi,
      h.2.2.2.2.1.2⟩,
    h.2.2.2.2.2⟩, hrefs, hnxt⟩

/-- Updating header word `ar[cref]` while preserving `PH_GARB` (`bit 19`) and `PH_SHRK` (`bit 23`)
preserves `FullCoreInv`, `fullArenaClauseRefs`, `fullArenaClauseSize`, `fullArenaClauseGarb`,
`fullArenaClauseLits`, and `fullArenaNextOff`. -/
theorem fullArena_setHdr_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    {hdr' : BitVec 32}
    (hgarb : (hdr' &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32))
    (hshrk : (hdr' &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32)) :
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref hdr' } }
    FullCoreInv c F0 s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r ∧
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  dsimp only [fullArenaClauseRefs, fullArenaClauseSize, fullArenaClauseGarb,
    fullArenaClauseLits, fullArenaHdr] at *
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hcl := hinv.lengths.core_ok
  have hcref_wf := hw.arena.refs_wf cref href
  have hcref_lt : cref < s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have har_self : s'.core.arena[cref]? = some hdr' := List.getElem?_set_self hcref_lt
  have har_ne : ∀ k, k ≠ cref → s'.core.arena[k]? = s.core.arena[k]? := fun k hk =>
    List.getElem?_set_ne (Ne.symm hk)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, har_self, Option.getD_some, har_ne (cref + 2) (by omega)]
      split
      · rfl
      · change (if (hdr' &&& 0x00800000#32) ≠ 0#32 then _ else _) =
          if (fullArenaHdrCore s.core cref &&& 0x00800000#32) ≠ 0#32 then _ else _
        rw [hshrk]; split
        · exact fullArenaSkipShrk_congr fun k hk1 _ => har_ne k (by omega)
        · rfl
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj := fullArenaScanRefs_disjoint hr href hlt
        have hr_wf := hw.arena.refs_wf r hr
        exact fullArenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun k _ hk2 => har_ne k (by omega)
      · exact fullArenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun k hk1 _ => har_ne k (by omega)
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hprops : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
    intro r hr
    have hr_wf := hw.arena.refs_wf r hr
    have hnot_in : ∀ k, r + 2 ≤ k → k < r + 3 + fullArenaClauseSizeCore s.core r → k ≠ cref := by
      intro k hk1 hk2 heq; subst k
      by_cases hrc : r = cref
      · omega
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := hw.arena.disjoint hr href hlt; omega
        · omega
    have hsz : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore; exact congrArg (fun o => (o.getD 0#32).toNat)
        (har_ne (r + 2) (hnot_in (r + 2) (Nat.le_refl _) (by omega)))
    have hgb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore
      by_cases hrc : r = cref
      · subst r; rw [har_self, Option.getD_some]
        change (hdr' &&& 0x00080000#32 != 0#32) =
          (fullArenaHdrCore s.core cref &&& 0x00080000#32 != 0#32)
        rw [hgarb]
      · rw [har_ne r hrc]
    have hlits : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
      have hbd1 : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
        have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
      exact fullArenaClauseLitsCore_eq_of_hold hbd1 (by simpa [s'] using hbd1) hsz
        fun j hj => har_ne (r + 3 + j) (hnot_in (r + 3 + j) (by omega) (by omega))
    exact ⟨hsz, hgb, hlits⟩
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hinv.lengths.scratch_ok⟩
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      rw [show s'.core.arena_len = s.core.arena_len from rfl, hnxt r hr, (hprops r hr).1]
      exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh; rw [har_self, Option.getD_some] at hsh
          rwa [hshrk] at hsh
        · unfold fullArenaHdrCore at hsh ⊢; rwa [har_ne r hrc] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have hlt : r < s.core.arena.length := by
          have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hlt, Option.getD_some]
      have hsh_ar : (s.core.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (hw.arena.refs_wf cref hr).2.1; omega
        · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · have := fullArenaScanRefs_disjoint hr href hlt; omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      have ht0_lt : t0 < s.core.arena_len := by
        have := (hw.arena.refs_wf r hr).2.2.2.1; omega
      refine ⟨t0, by rw [(hprops r hr).1]; exact ht0_lo, ht0_lt, ?_⟩
      rw [har_ne t0 ht0_ne]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hprops r hr).2.1] at hng; rw [(hprops r hr).2.2] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hprops r hr).2.1] at hng; rw [(hprops r hr).2.2]
      exact hw.arena.entails r hr hng
  refine ⟨⟨hlen', F_cur, { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl,
        show s'.core.cur_vars = s.core.cur_vars from rfl, show s'.core.lvl = s.core.lvl from rfl]
      by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        obtain ⟨href_r, hng_r, hall_r⟩ := hrs
        exact ⟨hrefs ▸ href_r, (hprops _ href_r).2.1.trans hng_r,
          fun q hq => hall_r q ((hprops _ href_r).2.2 ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hbf : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hbf] at hrs
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl]
      exact (hprops _ hrs.1).2.2 ▸ hw.reason_lit_mem idx hidx hne hlg }⟩,
    hrefs, fun r hr => ⟨hnxt r hr, hprops r hr⟩⟩

/-- Updating only the literal payload `cref + 3 ..< cref + 3 + old_sz` of a non-garbage clause
at level 0 preserves `FullWitnessInv` (with the same `F_cur`), `fullArenaClauseRefs`, and
`fullArenaNextOff`. -/
theorem fullArena_updateLits_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    {arena' : List (BitVec 32)} (hal' : arena'.length = c.arena_cap)
    (hout : ∀ k, (k < cref + 3 ∨ cref + 3 + fullArenaClauseSize s cref ≤ k) →
      arena'[k]? = s.core.arena[k]?)
    (hlits_lt : ∀ j < fullArenaClauseSize s cref,
      (arena'[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := arena' } cref))) :
    let s' : FullState := { s with core := { s.core with arena := arena' } }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r) := by
  intro s'
  dsimp only [fullArenaClauseRefs, fullArenaClauseSize, fullArenaClauseGarb,
    fullArenaClauseLits, fullArenaHdr] at *
  have hcl := hlen.core_ok
  have hcref_wf := hw.arena.refs_wf cref href
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r
      exact fullArenaNextOff_congr_block (hout cref (Or.inl (by omega)))
        (hout (cref + 2) (Or.inl (by omega)))
        fun k hk1 _ => hout k (Or.inr hk1)
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj := fullArenaScanRefs_disjoint hr href hlt
        have hr_wf := hw.arena.refs_wf r hr
        exact fullArenaNextOff_congr_block (hout r (Or.inl (by omega)))
          (hout (r + 2) (Or.inl (by omega))) fun k _ hk2 => hout k (Or.inl (by omega))
      · have hdisj := fullArenaScanRefs_disjoint href hr hgt
        exact fullArenaNextOff_congr_block (hout r (Or.inr (by omega)))
          (hout (r + 2) (Or.inr (by omega))) fun k hk1 _ => hout k (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst r; rw [hout (cref + 2) (Or.inl (by omega))]
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := hw.arena.disjoint hr href hlt; rw [hout (r + 2) (Or.inl (by omega))]
      · have := hw.arena.disjoint href hr hgt; rw [hout (r + 2) (Or.inr (by omega))]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst r; rw [hout cref (Or.inl (by omega))]
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := hw.arena.disjoint hr href hlt; rw [hout r (Or.inl (by omega))]
      · have := hw.arena.disjoint href hr hgt; rw [hout r (Or.inr (by omega))]
  have hother_lits : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr hne => by
    have hr_wf := hw.arena.refs_wf r hr
    have hbd1 : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
    have hbd2 : r + 3 + fullArenaClauseSizeCore s.core r ≤ arena'.length := by
      rw [hal', ← hcl.arena_len_arr]; exact hbd1
    refine fullArenaClauseLitsCore_eq_of_hold hbd1 hbd2 (hsz_eq r hr) fun j hj => ?_
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := hw.arena.disjoint hr href hlt; exact hout (r + 3 + j) (Or.inl (by omega))
    · have := hw.arena.disjoint href hr hgt; exact hout (r + 3 + j) (Or.inr (by omega))
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := hal' }, hlen.scratch_ok⟩
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      rw [show s'.core.arena_len = s.core.arena_len from rfl, hnxt r hr, hsz_eq r hr]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hr_out : r < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ r := by
        by_cases hrc : r = cref
        · subst r; exact Or.inl (by omega)
        · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · exact Or.inl (by omega)
          · have := hw.arena.disjoint href hr hgt; exact Or.inr (by omega)
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh; rwa [hout r hr_out] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have hlt : r < s.core.arena.length := by
          have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hlt, Option.getD_some]
      have hsh_ar : (s.core.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
      have ht0_out : t0 < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ t0 := by
        by_cases hrc : r = cref
        · subst r; exact Or.inr ht0_lo
        · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · have := fullArenaScanRefs_disjoint hr href hlt; exact Or.inl (by omega)
          · have := hw.arena.disjoint href hr hgt; exact Or.inr (by omega)
      have ht0_lt : t0 < s.core.arena_len := by
        have := (hw.arena.refs_wf r hr).2.2.2.1; omega
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, ht0_lt, ?_⟩
      dsimp only [s']; rw [hout t0 ht0_out]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        have hbd : cref + 3 + fullArenaClauseSizeCore s'.core cref ≤ s'.core.arena.length := by
          rw [hsz_eq cref hr]; dsimp only [s']; have := hcl.arena_len_le; omega
        obtain ⟨j, hj, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl
        rw [hsz_eq cref hr] at hj
        have hlt := hlits_lt j hj
        have hbd' : cref + 3 + j < arena'.length := by
          dsimp only [s'] at hbd; rw [hsz_eq cref hr] at hbd; omega
        have hget' : (arena'[cref + 3 + j]?.getD 0#32).toNat = l := by
          rw [List.getElem?_eq_getElem hbd', Option.getD_some]; exact hget
        change l < 2 * s.core.cur_vars; omega
      · rw [hgarb_eq r hr] at hng; rw [hother_lits r hr hrc] at hl
        exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hent
      · rw [hgarb_eq r hr] at hng; rw [hother_lits r hr hrc]
        exact hw.arena.entails r hr hng
  refine ⟨hlen', { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hlv : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := hw.lvl_le idx hidx; omega
      exact absurd (hw.level0_rsn_none idx hidx hlv) hne
    reason_lit_mem := fun idx hidx hne _ => by
      have hlv : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := hw.lvl_le idx hidx; omega
      exact absurd (hw.level0_rsn_none idx hidx hlv) hne }, hrefs, hnxt⟩

private theorem fullArenaSkipShrk_step_range {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {p q : Nat}, p ≤ q → q ≤ alen →
      (∀ k, p ≤ k → k < q → ar[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      fullArenaSkipShrk ar alen p (alen - p) = fullArenaSkipShrk ar alen q (alen - q) := by
  suffices h : ∀ d p q, p + d = q → q ≤ alen →
      (∀ k, p ≤ k → k < q → ar[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      fullArenaSkipShrk ar alen p (alen - p) = fullArenaSkipShrk ar alen q (alen - q) from
    fun {p q} hle hqa hne => h (q - p) p q (by omega) hqa hne
  intro d
  induction d with
  | zero => intro p q hpq _ _; rw [show p = q by omega]
  | succ d ih =>
    intro p q hpq hqa hne
    have hpa : p < alen := by omega
    have hf : alen - p = (alen - (p + 1)) + 1 := by omega
    have hnep : ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := hne p (Nat.le_refl p) (by omega)
    have hstep1 : ∀ f, fullArenaSkipShrk ar alen p (f + 1) =
        fullArenaSkipShrk ar alen (p + 1) f := fun f => by
      simp [fullArenaSkipShrk, hpa, hnep]
    rw [hf, hstep1]
    exact ih (p + 1) q (by omega) hqa fun k hk1 hk2 => hne k (by omega) hk2

/-- In-place clause shrinking at level 0 (`3 ≤ nsz < old_sz`): writes `nhdr` (with `PH_SHRK` set
and `PH_GARB` clear), `nsz`, new literals `0 ..< nsz`, and `0xFFFFFFFF#32` terminator at
`cref + 3 + old_sz - 1` when `PH_SHRK` was previously clear. Preserves `fullArenaNextOff` on every
block, `fullArenaClauseRefs`, and `FullWitnessInv` (with the same `F_cur`). -/
theorem inPlaceShrink_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSize s cref)
    {arena' : List (BitVec 32)} {ni' nr' : BitVec 64} {sc' : FullScratch}
    (hal' : arena'.length = c.arena_cap) (hsc' : sc'.LengthsOk c)
    (hout : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ k) →
      arena'[k]? = s.core.arena[k]?)
    (hnhdr_garb : (arena'[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hnhdr_shrk : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32)
    (hnsz_eq : (arena'[cref + 2]?.getD 0#32).toNat = nsz)
    (hpad_old :
      if (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 then
        (∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + fullArenaClauseSize s cref - 1 →
          arena'[k]? = s.core.arena[k]?) ∧
        arena'[cref + 3 + fullArenaClauseSize s cref - 1]? = some 0xFFFFFFFF#32
      else
        ∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + fullArenaClauseSize s cref →
          arena'[k]? = s.core.arena[k]?)
    (hlits_lt : ∀ j < nsz, (arena'[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := arena' } cref))) :
    let s' : FullState :=
      { s with
        core := { s.core with arena := arena', num_irred := ni', num_redundant := nr' }
        scratch := sc' }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    fullArenaClauseGarb s' cref = false ∧ fullArenaClauseSize s' cref = nsz ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r) := by
  intro s'
  dsimp only [fullArenaClauseRefs, fullArenaClauseSize, fullArenaClauseGarb,
    fullArenaClauseLits, fullArenaHdr] at *
  have hcl := hlen.core_ok
  have hcref_wf := hw.arena.refs_wf cref href
  have hold_bd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hold_ne_ff : ∀ k, cref + 3 ≤ k → k < cref + 3 + fullArenaClauseSizeCore s.core cref →
      s.core.arena[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    intro k hk1 hk2
    let j := k - (cref + 3)
    have hj : j < fullArenaClauseSizeCore s.core cref := by omega
    have hk_eq : cref + 3 + j = k := by omega
    have hmem : (s.core.arena[cref + 3 + j]'(by omega)).toNat ∈
        fullArenaClauseLitsCore s.core cref :=
      (mem_fullArenaClauseLitsCore_iff hold_bd).mpr ⟨j, hj, rfl⟩
    have hlt := hw.arena.lits_lt cref href hng _ hmem
    have hcv := hcl.cur_vars_le; have hmax := c.hmaxv; unfold dimacsBound at hmax
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    intro heq
    have h1 : (s.core.arena[cref + 3 + j]'(by omega)).toNat = 0xFFFFFFFF := by
      have : s.core.arena[cref + 3 + j]'(by omega) = s.core.arena[k]'(by omega) := by
        congr 1
      rw [this, heq]; rfl
    omega
  have hnxt_cref : fullArenaNextOff arena' s.core.arena_len cref =
      fullArenaNextOff s.core.arena s.core.arena_len cref := by
    have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
    have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
      unfold fullArenaClauseSizeCore at hcref_wf; omega
    have h2n : ¬ (cref + 3 + nsz > s.core.arena_len) := by omega
    unfold fullArenaNextOff
    simp only [h1, h2, hnhdr_shrk, hnsz_eq, h2n, ↓reduceIte, ne_eq, not_false_eq_true]
    by_cases hsh0 : (fullArenaHdrCore s.core cref &&& 0x00800000#32) = 0#32
    · rw [ite_eq_left hsh0] at hpad_old
      obtain ⟨hkeep, hterm⟩ := hpad_old
      have hsh0' : ¬ ((s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32) := by
        simpa [fullArenaHdrCore] using hsh0
      rw [ite_eq_right hsh0']
      have hstep := fullArenaSkipShrk_step_range (ar := arena') (alen := s.core.arena_len)
        (p := cref + 3 + nsz) (q := cref + 3 + fullArenaClauseSizeCore s.core cref - 1)
        (by omega) (by omega) fun k hk1 hk2 => by
          rw [hkeep k hk1 hk2]; exact hold_ne_ff k (by omega) (by omega)
      rw [hstep]
      have hfl : s.core.arena_len - (cref + 3 + fullArenaClauseSizeCore s.core cref - 1) =
          (s.core.arena_len - (cref + 3 + fullArenaClauseSizeCore s.core cref)) + 1 := by omega
      have hlt_a : cref + 3 + fullArenaClauseSizeCore s.core cref - 1 < s.core.arena_len := by
        omega
      rw [hfl]; unfold fullArenaSkipShrk
      simp only [hlt_a, hterm, Option.getD_some, ↓reduceIte, ne_eq, not_true_eq_false]
      have hsz_def : fullArenaClauseSizeCore s.core cref =
          (s.core.arena[cref + 2]?.getD 0#32).toNat := rfl
      omega
    · rw [ite_eq_right hsh0] at hpad_old
      have hsh0' : (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := hsh0
      rw [ite_eq_left hsh0']
      have hstep := fullArenaSkipShrk_step_range (ar := arena') (alen := s.core.arena_len)
        (p := cref + 3 + nsz) (q := cref + 3 + fullArenaClauseSizeCore s.core cref)
        (by omega) (by omega) fun k hk1 hk2 => by
          rw [hpad_old k hk1 hk2]; exact hold_ne_ff k (by omega) hk2
      rw [hstep]
      exact fullArenaSkipShrk_congr fun k hk1 _ => hout k (Or.inr hk1)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r; exact hnxt_cref
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj := fullArenaScanRefs_disjoint hr href hlt
        have hr_wf := hw.arena.refs_wf r hr
        exact fullArenaNextOff_congr_block (hout r (Or.inl (by omega)))
          (hout (r + 2) (Or.inl (by omega))) fun k _ hk2 => hout k (Or.inl (by omega))
      · have hdisj := fullArenaScanRefs_disjoint href hr hgt
        exact fullArenaNextOff_congr_block (hout r (Or.inr (by omega)))
          (hout (r + 2) (Or.inr (by omega))) fun k hk1 _ => hout k (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hother_sz : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr hne => by
    unfold fullArenaClauseSizeCore; dsimp only [s']
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := hw.arena.disjoint hr href hlt; rw [hout (r + 2) (Or.inl (by omega))]
    · have := hw.arena.disjoint href hr hgt; rw [hout (r + 2) (Or.inr (by omega))]
  have hother_garb : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr hne => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := hw.arena.disjoint hr href hlt; rw [hout r (Or.inl (by omega))]
    · have := hw.arena.disjoint href hr hgt; rw [hout r (Or.inr (by omega))]
  have hother_lits : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr hne => by
    have hr_wf := hw.arena.refs_wf r hr
    have hbd1 : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
    have hbd2 : r + 3 + fullArenaClauseSizeCore s.core r ≤ arena'.length := by
      rw [hal', ← hcl.arena_len_arr]; exact hbd1
    refine fullArenaClauseLitsCore_eq_of_hold hbd1 hbd2 (hother_sz r hr hne) fun j hj => ?_
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := hw.arena.disjoint hr href hlt; exact hout (r + 3 + j) (Or.inl (by omega))
    · have := hw.arena.disjoint href hr hgt; exact hout (r + 3 + j) (Or.inr (by omega))
  have hcref_garb' : fullArenaClauseGarbCore s'.core cref = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']; simp [hnhdr_garb]
  have hcref_sz' : fullArenaClauseSizeCore s'.core cref = nsz := hnsz_eq
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := hal' }, hsc'⟩
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      rw [show s'.core.arena_len = s.core.arena_len from rfl, hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hcref_sz']; exact ⟨hwf.1, hnsz3, by omega, hwf.2.2.2.1, hwf.2.2.2.2⟩
      · rw [hother_sz r hr hrc]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; rw [hcref_sz']
        by_cases hsh0 : (fullArenaHdrCore s.core cref &&& 0x00800000#32) = 0#32
        · rw [ite_eq_left hsh0] at hpad_old
          exact ⟨cref + 3 + fullArenaClauseSizeCore s.core cref - 1, by omega,
            by change _ < s.core.arena_len; omega, hpad_old.2⟩
        · obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term cref hr hsh0
          exact ⟨t, by omega, ht2, by dsimp only [s']; rw [hout t (Or.inr ht1)]; exact hsent⟩
      · have hr_out : r < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ r := by
          rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · exact Or.inl hlt
          · have := hw.arena.disjoint href hr hgt; exact Or.inr (by omega)
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh; rwa [hout r hr_out] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
          have hr3 := (hw.arena.refs_wf r hr).1
          have hlt : r < s.core.arena.length := by
            have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
          unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hlt, Option.getD_some]
        have hsh_ar : (s.core.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
          rw [hget_r, Option.getD_some]; exact hsh0
        obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
        have ht0_out : t0 < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ t0 := by
          rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · have := fullArenaScanRefs_disjoint hr href hlt; exact Or.inl (by omega)
          · have := hw.arena.disjoint href hr hgt; exact Or.inr (by omega)
        have ht0_lt : t0 < s.core.arena_len := by
          have := (hw.arena.refs_wf r hr).2.2.2.1; omega
        refine ⟨t0, by rw [hother_sz r hr hrc]; exact ht0_lo, ht0_lt, ?_⟩
        dsimp only [s']; rw [hout t0 ht0_out]; exact ht0_sent
    · intro r hr hng' l hl; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        have hbd : cref + 3 + fullArenaClauseSizeCore s'.core cref ≤ s'.core.arena.length := by
          rw [hcref_sz']; dsimp only [s']; have := hcl.arena_len_le; omega
        obtain ⟨j, hj, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl
        rw [hcref_sz'] at hj
        have hlt := hlits_lt j hj
        have hbd' : cref + 3 + j < arena'.length := by
          dsimp only [s'] at hbd; rw [hcref_sz'] at hbd; omega
        have hget' : (arena'[cref + 3 + j]?.getD 0#32).toNat = l := by
          rw [List.getElem?_eq_getElem hbd', Option.getD_some]; exact hget
        change l < 2 * s.core.cur_vars; omega
      · rw [hother_garb r hr hrc] at hng'; rw [hother_lits r hr hrc] at hl
        exact hw.arena.lits_lt r hr hng' l hl
    · intro r hr hng'; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hent
      · rw [hother_garb r hr hrc] at hng'; rw [hother_lits r hr hrc]
        exact hw.arena.entails r hr hng'
  refine ⟨hlen', { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hlv : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := hw.lvl_le idx hidx; omega
      exact absurd (hw.level0_rsn_none idx hidx hlv) hne
    reason_lit_mem := fun idx hidx hne _ => by
      have hlv : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := hw.lvl_le idx hidx; omega
      exact absurd (hw.level0_rsn_none idx hidx hlv) hne },
    hrefs, hcref_garb', hcref_sz', hnxt⟩

theorem fv_watchSlice_relocate {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p' + i]? = k.wstk[p + i]?)
    (h : WatchSliceOk F_cur k lit p rem) : WatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega) hent
      (ih (p' := p' + 1) fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (i + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (i + 2) (by omega))

theorem fv_watchSlice_append_large {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p' + i]? = k.wstk[p + i]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .large (by simpa using hw0) (by simpa using hw1) hflag hlt href .empty
  | @bin p rem w hp hf hne hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun i hi => by simpa [show p' + 1 + i = p' + (i + 1) by omega,
        show p + 1 + i = p + (i + 1) by omega] using hwstk (i + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun i hi => by simpa [show p' + 2 + i = p' + (i + 2) by omega,
        show p + 2 + i = p + (i + 2) by omega] using hwstk (i + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

theorem fullWatchPush_large_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInvW c F0 F_cur s) {lit w0 cref : BitVec 32} {ok : Bool}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wusable' : BitVec 64}
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefs s) :
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } }
    s'.LengthsOk c → WatchStackLayout s'.core →
    (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize s' l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
    (ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + 2 ∧
      (∀ k < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
          s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some cref) →
    (ok = false → lit.toNat < 2 * s.core.cur_vars →
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
      ∀ k < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
          s.core.wstk[fullWatchOff s lit.toNat + k]?) →
    FullSparseInvW c F0 F_cur s' := by
  intro s' hlen' hlay hother hok_t hok_f
  obtain ⟨_, hw, hmc, hnd, hext, hdm⟩ := hsp
  have hwat0 : WatchesInv F_cur s.core := by
    have := hw.watches; unfold ModeWatchesInv at this; simpa [hdm] using this
  have hwat' : ModeWatchesInv F_cur s'.core := by
    unfold ModeWatchesInv; rw [show s'.core.dense_mode = 0#64 from hdm]; simp only [↓reduceIte]
    refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit.toNat
    · subst hle
      cases ok with
      | false =>
        obtain ⟨hsz, hpre⟩ := hok_f rfl hl
        rw [show fullWatchSizeCore s'.core lit.toNat = fullWatchSizeCore s.core lit.toNat from hsz]
        exact fv_watchSlice_relocate (k := s.core) (k' := s'.core)
          (Nat.le_refl _) (fun _ r => r) hpre (hwat0.slices _ hl)
      | true =>
        obtain ⟨_, hsz, hpre, hw0, hw1⟩ := hok_t rfl
        rw [show fullWatchSizeCore s'.core lit.toNat =
          fullWatchSizeCore s.core lit.toNat + 2 from hsz]
        exact fv_watchSlice_append_large (k := s.core) (k' := s'.core)
          (Nat.le_refl _) (fun _ r => r) hpre (hwat0.slices _ hl) hw0 hw1 hflag hlt href
    · obtain ⟨hsz, hpre⟩ := hother l hl hle
      rw [show fullWatchSizeCore s'.core l = fullWatchSizeCore s.core l from hsz]
      exact fv_watchSlice_relocate (k := s.core) (k' := s'.core)
        (Nat.le_refl _) (fun _ r => r) hpre (hwat0.slices l hl)
  have harena' : FullArenaClausesInv c F_cur s'.core :=
    ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt, hw.arena.entails⟩
  exact ⟨hlen', { hw with arena := harena', watches := hwat' }, hmc, hnd, hext, hdm⟩

theorem entails_filter_level0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {c1 c2 : List Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause c1))
    (hsub : ∀ l ∈ c1, l ∈ c2 ∨ (l < 2 * k.cur_vars ∧ k.vals[l]?.getD 0#8 = 0xFF#8)) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause c2) := by
  refine entails_of_mem_or_false hent fun l hl => ?_
  rcases hsub l hl with hin | ⟨hlt, hff⟩
  · exact Or.inl hin
  · right
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hlt).mp hff
    have hli : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le i hi; omega
    have hs := hw.level0_sound i hi hli
    rwa [hieq] at hs

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    have hf : ∃ f, k.arena_len = f + 1 := ⟨k.arena_len - 1, by omega⟩
    obtain ⟨f, hf⟩ := hf
    rw [hf]; unfold fullArenaScanRefs; simp [show 0 + 3 ≤ f + 1 by omega]

theorem fullArenaScanRefs_next_mem_or_end {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      (∀ q ∈ fullArenaScanRefs ar alen pos fuel,
        fullArenaNextOff ar alen q = alen ∨ fullArenaNextOff ar alen q + 3 ≤ alen) →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r = alen ∨
        fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, _, h => by simp [fullArenaScanRefs] at h
  | fuel + 1, pos, r, hfl, hwf, h => by
    unfold fullArenaScanRefs at h hwf ⊢; split at h
    · rename_i hle
      simp only [hle, ↓reduceIte] at hwf ⊢
      simp only [List.mem_cons] at h
      have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases h with rfl | hrest
      · rcases hwf r List.mem_cons_self with hend | h3
        · exact Or.inl hend
        · right; right
          cases fuel with
          | zero => omega
          | succ f' =>
            unfold fullArenaScanRefs; simp only [h3, ↓reduceIte]; exact List.mem_cons_self
      · rcases fullArenaScanRefs_next_mem_or_end (by omega)
            (fun q hq => hwf q (List.mem_cons_of_mem _ hq)) hrest with hend | hmem
        · exact Or.inl hend
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
    · simp at h

theorem fullArenaClauseRefs_next_mem_or_end {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k)
    {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next_mem_or_end (by omega) (fun q hq => (ha.refs_wf q hq).2.2.2.2) hr

end FullVivifyHelpers

open FullVivifyHelpers

/-! ## 3. Parametric callee `Spec` contracts (`FullVivifySpecs`) -/

namespace FullVivifySpecs

private def fullVivArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

@[expose] def fullVivUnwatchLargeSpec : Spec [i64, i32, i32] [] := fun (h, _lit, _cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wu' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
      FullSparseInv c F0 s' → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullVivWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : FullState :=
          { s with
            core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                  wusable := wusable' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        (ok = true →
          lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
          (∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
        (ok = false →
          (lit.toNat < 2 * s.core.cur_vars →
            fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
            ∀ k < fullWatchSize s lit.toNat,
              s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
                s.core.wstk[fullWatchOff s lit.toNat + k]?)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullVivAddUnitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ lit.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
      s'.core.oom = s.core.oom → s'.core.fuel = s.core.fuel →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullVivAddBinSpec : Spec [i64, i32, i32] [i64] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧ s.core.cur_level = 0 ∧
    a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      FullWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' → FullExtScratchOk c s' →
      s'.core.dense_mode = 0#64 → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = 0 → s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private def fullVivAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
        s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
      Q () m
    else
      let v := lit.toNat / 2
      let rsn' := if s.core.cur_level = 0 then 0xFFFFFFFF#32 else rsn
      let unfl' := if s.core.cur_level = 0 then s.core.unflushed + 1#64 else s.core.unflushed
      ∀ flags' unassigned' phases' m',
        flags'.length = c.max_vars → phases'.length = c.max_vars →
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                flags := flags'
                lvl := s.core.lvl.set v (BitVec.ofNat 32 s.core.cur_level)
                rsns := s.core.rsns.set v rsn'
                trl := s.core.trl.set s.core.trail_end lit
                trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                trail_end := s.core.trail_end + 1
                unassigned := unassigned', unflushed := unfl' }
            scratch := { s.scratch with phases := phases' } }
        s'.LengthsOk c → (FullMem c s' ⋆ R) m' → Q () m'

private def fullVivBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ FullWitnessInv c F0 F_cur s.core ∧
    target_lvl.toNat ≤ s.core.cur_level ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → FullWitnessInv c F0 F_cur s'.core →
      s'.core.cur_level = target_lvl.toNat →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
      s'.core.oom = s.core.oom → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 → s'.scratch.res_sz = s.scratch.res_sz →
      (FullMem c s' ⋆ R) m' → Q () m'

private def fullVivPropIgnoreSpec : Spec [i64, i64] [i64] := fun (h, _ignore_ref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) s' m',
      FullSparseInv c F0 s' → FullWitnessInv c F0 F_cur s'.core →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      s'.core.arena_len = s.core.arena_len → s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = s.core.cur_level → s'.core.probing = s.core.probing →
      s'.core.tmp = s.core.tmp → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ cref ∈ fullArenaClauseRefs s,
        s'.core.arena[cref]? = s.core.arena[cref]? ∧
        fullArenaNextOff s'.core.arena s.core.arena_len cref =
          fullArenaNextOff s.core.arena s.core.arena_len cref ∧
        fullArenaClauseSize s' cref = fullArenaClauseSize s cref ∧
        fullArenaClauseGarb s' cref = fullArenaClauseGarb s cref ∧
        (∀ l, l ∈ fullArenaClauseLits s' cref ↔ l ∈ fullArenaClauseLits s cref)) →
      s.core.trail_end ≤ s'.core.trail_end →
      (∀ i < s.core.trail_end, s'.core.trl[i]? = s.core.trl[i]?) →
      (r = 0#64 → s'.core.confl_type = s.core.confl_type) →
      (r = 1#64 →
        (s'.core.confl_type = 1#64 ∧
          s'.core.confl_lit0.toNat < 2 * s'.core.cur_vars ∧
          s'.core.confl_lit1.toNat < 2 * s'.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause [s'.core.confl_lit0.toNat, s'.core.confl_lit1.toNat]) ∧
          s'.core.vals[s'.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
          s'.core.vals[s'.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
        (s'.core.confl_type = 2#64 ∧
          s'.core.confl_ref.toNat ∈ fullArenaClauseRefs s' ∧
          fullArenaClauseGarb s' s'.core.confl_ref.toNat = false ∧
          ∀ l ∈ fullArenaClauseLits s' s'.core.confl_ref.toNat,
            s'.core.vals[l]?.getD 0#8 = 0xFF#8)) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private def fullVivPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) s' m',
      FullSparseInv c F0 s' → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      s'.core.arena_len = s.core.arena_len → s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = 0 → s'.core.probing = s.core.probing →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ cref ∈ fullArenaClauseRefs s,
        fullArenaNextOff s'.core.arena s.core.arena_len cref =
          fullArenaNextOff s.core.arena s.core.arena_len cref) →
      (r = 1#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullVivSortLitsSpec : Spec [i64, i64, i32] [] := fun (h, lits_ptr, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ lits_ptr = c.pTmp ∧ s.LengthsOk c ∧ sz.toNat ≤ c.max_vars ∧
    (∀ i < sz.toNat, (s.core.tmp[i]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' m', tmp'.length = c.max_vars →
      (tmp'.take sz.toNat).Perm (s.core.tmp.take sz.toNat) →
      (∀ i, sz.toNat ≤ i → i < c.max_vars → tmp'[i]? = s.core.tmp[i]?) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

end FullVivifySpecs

/-! ## 4. `full_viv_sort_lits` `Func.wp` proof -/

private theorem tmp_lt_of_perm {xs orig : List (BitVec 32)} {sz B : Nat}
    (hxs : sz ≤ xs.length) (hperm : (xs.take sz).Perm (orig.take sz))
    (hlt : ∀ idx < sz, (orig[idx]?.getD 0#32).toNat < B) :
    ∀ k < sz, (xs[k]?.getD 0#32).toNat < B := fun k hk => by
  have hm : xs[k]'(by omega) ∈ orig.take sz := hperm.mem_iff.mp (by
    rw [List.mem_iff_getElem]
    exact ⟨k, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩)
  obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hm
  have hle_o : (orig.take sz).length ≤ orig.length := by
    rw [List.length_take]; exact Nat.min_le_right _ _
  have hidx_sz : idx < sz := by rw [List.length_take] at hidx; omega
  have hget := hlt idx hidx_sz
  rw [List.getElem_take] at heq
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← heq]
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget

private theorem tmp_shift_hole {xs orig : List (BitVec 32)} {sz j : Nat} {x prev : BitVec 32}
    (hlen : xs.length = orig.length) (hsz : sz ≤ orig.length) (hj0 : 0 < j) (hjsz : j < sz)
    (hprev : xs[j - 1]? = some prev) (hperm : ((xs.set j x).take sz).Perm (orig.take sz)) :
    (((xs.set j prev).set (j - 1) x).take sz).Perm (orig.take sz) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj0)
  rw [Nat.succ_sub_one] at hprev ⊢
  let A := (xs.set (m + 1) x).take sz; let B := ((xs.set (m + 1) prev).set m x).take sz
  have hAl : A.length = sz := by simp [A, List.length_take, hlen]; omega
  let head := A.take m; let tail := A.drop (m + 2)
  have htk : head.length = m := by simp [head, List.length_take, hAl]; omega
  have hsp : ∀ (C : List (BitVec 32)) (a b : BitVec 32), C.length = sz →
      (∀ k < m, C[k]? = A[k]?) → C[m]? = some a → C[m + 1]? = some b →
      (∀ k, m + 2 ≤ k → C[k]? = A[k]?) → C = head ++ a :: b :: tail := by
    intro C a b hCl hk_lt hk_m hk_j hk_gt; refine List.ext_getElem? fun k => ?_
    by_cases hkm : k < m
    · rw [List.getElem?_append_left (by omega), List.getElem?_take]; simp [hkm, hk_lt k hkm]
    · rw [List.getElem?_append_right (by omega), htk]
      by_cases hk0 : k = m
      · subst hk0; simp [hk_m]
      · by_cases hk1 : k = m + 1
        · subst hk1; simp [hk_j]
        · rw [show k - m = (k - (m + 2)) + 2 by omega]
          simp only [List.getElem?_cons_succ, tail, List.getElem?_drop]
          rw [show m + 2 + (k - (m + 2)) = k by omega]; exact hk_gt k (by omega)
  have hA := hsp A prev x hAl (fun _ _ => rfl)
    (by simp only [A, List.getElem?_take, show m < sz by omega, ↓reduceIte,
          List.getElem?_set_ne (by omega : m + 1 ≠ m)]; exact hprev)
    (by simp only [A, List.getElem?_take, hjsz, ↓reduceIte]
        exact List.getElem?_set_self (by omega))
    fun _ _ => rfl
  have hB := hsp B x prev (by simp [B, List.length_take, hlen]; omega)
    (fun k hk => by
      simp only [A, B, List.getElem?_take, List.getElem?_set_ne (by omega : m ≠ k),
        List.getElem?_set_ne (by omega : m + 1 ≠ k)])
    (by simp only [B, List.getElem?_take, show m < sz by omega, ↓reduceIte]
        exact List.getElem?_set_self (by simp; omega))
    (by simp only [B, List.getElem?_take, hjsz, ↓reduceIte,
          List.getElem?_set_ne (by omega : m ≠ m + 1)]
        exact List.getElem?_set_self (by omega))
    fun k hk => by
      simp only [A, B, List.getElem?_take, List.getElem?_set_ne (by omega : m ≠ k),
        List.getElem?_set_ne (by omega : m + 1 ≠ k)]
  have hswap : B.Perm A := by
    rw [hB, hA]; exact List.Perm.append_left _ (List.Perm.swap prev x tail)
  exact hswap.trans hperm

private theorem bv32_zext64_shl1_add1 (x : BitVec 32) :
    (((x.setWidth 64) <<< 1#64) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  omega

theorem full_viv_sort_lits_wp (Γ : Env) :
    ∀ args m Q X, fullVivSortLitsSpec args m Q X →
      Func.wp Γ full_viv_sort_lits_body args m Q X := by
  rintro ⟨h, lits_ptr, sz, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, rfl, hlen, hsz_le, hlt_orig, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have htl0 := hlen.core_ok.tmp_len_arr; have hwl0 := hlen.core_ok.wvec_len
  fv_steps
  refine wp_loop_inv
    (fun (i, ()) m1 => ∃ tmp1 : List (BitVec 32),
      1 ≤ i.toNat ∧ (sz.toNat = 0 → i.toNat = 1) ∧ (0 < sz.toNat → i.toNat ≤ sz.toNat) ∧
      tmp1.length = c.max_vars ∧ (tmp1.take sz.toNat).Perm (s.core.tmp.take sz.toNat) ∧
      (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp1[k]? = s.core.tmp[k]?) ∧
      (FullMem c { s with core := { s.core with tmp := tmp1 } } ⋆ R) m1)
    (fun (i, ()) _ => sz.toNat - i.toNat)
    (fun J_out hJ => by
      fv_steps
      have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
      exact hJ (1#32, ()) m ⟨s.core.tmp, by omega, fun _ => rfl, fun h => by omega, htl0,
        .refl _, fun _ _ _ => rfl, hm⟩)
    (fun J_out (i, ()) m1 ⟨tmp1, hi1, hiz, hipos, htl1, hperm1, hout1, hm1⟩ ih => ?_)
  fv_steps
  · have hi_lt : i.toNat < sz.toNat := by c0_bound
    have htmp1_lt := tmp_lt_of_perm (by omega) hperm1 hlt_orig
    let x : BitVec 32 := tmp1[i.toNat]'(by omega)
    have hx_lt_v : x.toNat < 2 * c.max_vars := by
      have h := htmp1_lt i.toNat hi_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
    have hx_widx := bv32_zext64_shl1_add1 x
    have hx_wlt : (((x.setWidth 64) <<< 1#64) + 1#64).toNat < s.core.wvec.length := by omega
    have hperm_init : ((tmp1.set i.toNat x).take sz.toNat).Perm (s.core.tmp.take sz.toNat) := by
      rwa [show tmp1.set i.toNat x = tmp1 from List.ext_getElem (by simp) fun k hk _ => by
        by_cases hki : k = i.toNat
        · subst hki; rw [List.getElem_set_self]
        · rw [List.getElem_set_ne (Ne.symm hki)]]
    fv_steps
    refine wp_loop_inv
      (fun (j, ()) m2 => ∃ tmp2 : List (BitVec 32),
        j.toNat ≤ i.toNat ∧ tmp2.length = c.max_vars ∧
        ((tmp2.set j.toNat x).take sz.toNat).Perm (s.core.tmp.take sz.toNat) ∧
        (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp2[k]? = s.core.tmp[k]?) ∧
        (FullMem c { s with core := { s.core with tmp := tmp2 } } ⋆ R) m2)
      (fun (j, ()) _ => j.toNat)
      (fun J2 hJ2 => by
        fv_steps; exact hJ2 (i, ()) m1 ⟨tmp1, Nat.le_refl _, htl1, hperm_init, hout1, hm1⟩)
      (fun J2 (j, ()) m2 ⟨tmp2, hj_le, htl2, hperm2, hout2, hm2⟩ ih2 => ?_)
    have hplace : ∀ (j0 : BitVec 32) (tmp_f : List (BitVec 32)) (mf : Mem 64),
        j0.toNat ≤ i.toNat → tmp_f.length = c.max_vars →
        ((tmp_f.set j0.toNat x).take sz.toNat).Perm (s.core.tmp.take sz.toNat) →
        (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp_f[k]? = s.core.tmp[k]?) →
        (FullMem c { s with core := { s.core with tmp := tmp_f.set j0.toNat x } } ⋆ R) mf →
        J_out (i + 1#32, ()) mf := by
      intro j0 tmp_f mf hj0 htlf hpermf houtf hmf
      have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      exact ih (i + 1#32, ()) mf (by dsimp only; omega)
        ⟨tmp_f.set j0.toNat x, by omega, fun hz => by omega, fun _ => by omega, by simp [htlf],
         hpermf, fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega)]; exact houtf k hk1 hk2,
         hmf⟩
    fv_steps
    · have hj_pos : 0 < j.toNat := by c0_bound
      have hj1_nat : (j - 1#32).toNat = j.toNat - 1 := by bv_omega
      let prev : BitVec 32 := tmp2[(j - 1#32).toNat]'(by omega)
      have hprev_eq : tmp2[j.toNat - 1]? = some prev := by
        rw [List.getElem?_eq_getElem (by omega)]; congr 1; simp only [prev, hj1_nat]
      have hprev_lt : prev.toNat < 2 * c.max_vars := by
        have h := tmp_lt_of_perm (by simp [htl2]; omega) hperm2 hlt_orig (j.toNat - 1) (by omega)
        rwa [List.getElem?_set_ne (by omega), hprev_eq, Option.getD_some] at h
      have hp_widx := bv32_zext64_shl1_add1 prev
      have hp_wlt : (((prev.setWidth 64) <<< 1#64) + 1#64).toNat < s.core.wvec.length := by omega
      have hperm_sh := tmp_shift_hole (by omega : tmp2.length = s.core.tmp.length)
        (by omega : sz.toNat ≤ s.core.tmp.length) hj_pos (by omega) hprev_eq hperm2
      fv_steps
      · exact hplace j tmp2 _ hj_le htl2 hperm2 hout2 hm
      · exact hplace j tmp2 _ hj_le htl2 hperm2 hout2 hm
      · exact ih2 (j - 1#32, ()) _ (by dsimp only; omega) ⟨tmp2.set j.toNat prev, by omega,
          by simp [htl2], by simpa [hj1_nat] using hperm_sh,
          fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega)]; exact hout2 k hk1 hk2, hm⟩
      · exact ih2 (j - 1#32, ()) _ (by dsimp only; omega) ⟨tmp2.set j.toNat prev, by omega,
          by simp [htl2], by simpa [hj1_nat] using hperm_sh,
          fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega)]; exact hout2 k hk1 hk2, hm⟩
    · exact hplace j tmp2 _ hj_le htl2 hperm2 hout2 hm
  · exact hQ tmp1 m1 htl1 hperm1 hout1 hm1

end

end LeanQbe.T.Examples.Kissat.Full
