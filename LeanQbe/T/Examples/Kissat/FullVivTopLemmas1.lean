module

public import LeanQbe.T.Examples.Kissat.Full3
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step

/-!
# Kissat `D-Full` Vivification Driver Helpers & `Spec` Contracts (`Stage 4`, Part 1)

Provides:
1. Strictly file/section-local `FullVivTopTactics` (`open scoped FullArenaTactics`) and BV helpers.
2. `FullVivTopSpecs`: exact Stage-4 UNSAT-only `Spec` contracts aligned with `FullSpec{1,2,3}.lean`
   (including `#985` explicit `F_cur` threading / existential `F_cur` and `9e397b5` `taut` fix) for
   all `9` callees (`full_arena_next`, `full_assign`, `full_backtrack`, `full_propagate_ignore`,
   `full_propagate`, `full_viv_simplify`, `full_viv_sort_lits`, `full_viv_deduce`,
   `full_viv_commit`) and the `2` owned target functions (`full_viv_clause`, `full_vivify`).
3. Pure invariant, arena-header (`PH_VIV`), decision-assign, and trail-extension lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Scoped tactic helpers and bitvector arithmetic lemmas (`FullVivTopTactics`) -/

namespace FullVivTopTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "fvt_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "fvt_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "fvt_step" : tactic => `(tactic| ((try fvt_unmdata); (repeat fvt_strip); c0_step))
scoped macro "fvt_steps" : tactic =>
  `(tactic| (
      (try fvt_unmdata)
      (repeat fvt_strip)
      c0_steps
      repeat (any_goals (fvt_strip; repeat fvt_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
scoped elab "fvt_to_group" : tactic => do
  evalTactic (← `(tactic| ((try fvt_unmdata); (repeat fvt_strip))))
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1)
        out := out ++ (← getUnsolvedGoals)
      else
        out := out.push g
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
private theorem mask23_bit : ∀ i : Fin 32, (0x00800000#32)[i.val] = decide (i.val = 23) := by decide
private theorem maskN20_bit :
    ∀ i : Fin 32, (0xFFEFFFFF#32)[i.val] = decide (i.val ≠ 20) := by decide

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

private theorem mask19_20_bit :
    ∀ j : Fin 32, (0x00180000#32)[j.val] = decide (j.val = 19 ∨ j.val = 20) := by decide

theorem bv32_garb_zero_of_and_viv {h : BitVec 32} (hz : (h &&& 0x00180000#32) = 0#32) :
    (h &&& 0x00080000#32) = 0#32 := by
  ext i hi
  have h1 := congrArg (·[i]) hz
  simp only [BitVec.getElem_and, BitVec.getElem_zero] at h1 ⊢
  rw [mask19_bit ⟨i, hi⟩, mask19_20_bit ⟨i, hi⟩] at *
  by_cases h19 : i = 19 <;> simp [h19] at h1 ⊢; exact h1

theorem bv32_ne_sentinel_of_lt {x : BitVec 32} (hlt : x.toNat < 0x80000000) :
    x ≠ 0xFFFFFFFF#32 := by
  intro heq; subst heq; revert hlt; decide

theorem bv32_setWidth64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  bv_omega

theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem bv32_xor1_lt_even {l n : Nat} (hl : l < 2 * n) : l ^^^ 1 < 2 * n :=
  litNeg_lt_two_mul hl

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) :
    (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

end FullVivTopTactics

/-! ## 2. Canonical Stage-4 invariants and `FullVivTopSpecs` -/

namespace FullVivTopSpecs

/-- Variable marks (`mrk[0 ..< max_vars]`) are cleared to `0#8`. -/
@[expose] def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

/-- Both variable marks (`mrk`) and literal marks (`lit_mark`) are cleared to `0#8`. -/
@[expose] def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Every live arena clause has pairwise distinct variables (`NoDup` & non-tautology). -/
@[expose] def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- Every active slot in `last_learned[0 ..< 8]` is `0xFFFFFFFF#32` or a valid arena ref. -/
@[expose] def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Soundness-adjacent scratch bounds (`last_learned` validity + `extend_len ≤ extend_cap`). -/
@[expose] def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Canonical sparse-mode (2WL) UNSAT-only solver invariant (`dense_mode = 0#64`). -/
@[expose] def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Scratch-level equality predicate preserving `last_learned` and `extend_len`. -/
@[expose] def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

/-- Extended scratch-frame predicate preserved by `full_backtrack` and `full_propagate*`. -/
@[expose] def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

/-- Explicit-witness sparse-mode invariant (`FullSparseInv c F0 s ↔ ∃ F_cur, ...`). -/
@[expose]
def FullSparseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

theorem FullSparseInvW.toSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullSparseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInv.exists_witness {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : ∃ F_cur, FullSparseInvW c F0 F_cur s :=
  let ⟨F_cur, hw⟩ := h.1.witness
  ⟨F_cur, h.1.lengths, hw, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Explicit-witness conflict predicate (`FullConflictOkW F_cur s`). -/
@[expose] def FullConflictOkW (F_cur : List (List Nat)) (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat])) ∨
  (s.core.confl_type = 2#64 ∧
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)

theorem level0_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2 (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_))
    right
    have hlt := hw.arena.lits_lt _ href hng l hl
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
    rwa [heq] at hs

/-- Relaxed `FullWitnessInv` during OTFS retry (matching `FullSpec1.lean`). -/
structure FullOtfsWitnessInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (k : FullCoreState) : Prop where
  ext_sound : ExtUnsatSound F0 k.cur_vars F_cur
  inconsistent_sound : k.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat
  arena : FullArenaClausesInv c F_cur k
  watches : ModeWatchesInv F_cur k
  cur_level_le : k.cur_level ≤ k.trail_end
  trail_lits_lt : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars
  trail_vars_nodup : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j
  vals_domain : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0#8 ∨ k.vals[l]?.getD 0#8 = 1#8 ∨ k.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l
  vals_false_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level
  dec_earliest : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    0 < (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
    k.rsns[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 → j ≤ i
  levels_inhabited : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∃ i < k.trail_end, (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
  level0_sound : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(k.trl[i]?.getD 0#32).toNat])
  trail_pos_inv : ∀ i < k.trail_end,
    (k.trail_pos[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
  level0_rsn_none : ∀ idx < k.trail_end,
    (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  frame_trail_lt : ∀ L ≤ k.cur_level, (k.frame_trail[L]?.getD 0#32).toNat ≤ k.trail_end
  frame_trail_mono : ∀ L1 L2, L1 ≤ L2 → L2 ≤ k.cur_level →
    (k.frame_trail[L1]?.getD 0#32).toNat ≤ (k.frame_trail[L2]?.getD 0#32).toNat
  frame_trail_before_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∀ i < (k.frame_trail[L]?.getD 0#32).toNat,
      (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < L
  frame_dec_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    (k.frame_dec[L]?.getD 0#32).toNat < 2 * k.cur_vars
  reason_inv_below : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level →
    rsn ≠ 0xFFFFFFFF#32 →
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
      ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k.lvl[ot / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
    else
      rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
        q = p ∨ ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          (k.lvl[q / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
  reason_lit_mem_below : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level →
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
    p ∈ fullArenaClauseLitsCore k rsn.toNat

/-! ### 2.1 Callee `Spec` contracts (`9` callees) -/

@[expose] def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

@[expose] def fullAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
        s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
      Q () m
    else
      let v := lit.toNat / 2
      let rsn' := if s.core.cur_level = 0 then 0xFFFFFFFF#32 else rsn
      let unfl' := if s.core.cur_level = 0 then s.core.unflushed + 1#64 else s.core.unflushed
      ∀ flags' unass' phases' m',
        flags'.length = c.max_vars → phases'.length = c.max_vars →
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 s.core.cur_level)
                rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
                trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                trail_end := s.core.trail_end + 1
                unassigned := unass', unflushed := unfl' }
            scratch := { s.scratch with phases := phases' } }
        s'.LengthsOk c → (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧
    (target_lvl.toNat < s.core.cur_level → target_lvl.toNat < c.max_vars) ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → te' ≤ s.core.trail_end → prop' ≤ te' →
      cl' = min s.core.cur_level target_lvl.toNat → FullProbeScratchPres s s' →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullPropagateIgnoreSpec : Spec [i64, i64] [i64] := fun (h, _ignore_ref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
      FullProbeScratchPres s s' → s.core.trail_end ≤ te' → fuel'.toNat ≤ s.core.fuel.toNat →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ ref ∈ fullArenaClauseRefs s,
        fullArenaClauseSize s' ref = fullArenaClauseSize s ref ∧
        fullArenaClauseGarb s' ref = fullArenaClauseGarb s ref ∧
        (fullArenaClauseLits s' ref).Perm (fullArenaClauseLits s ref)) →
      (∀ i < s.core.trail_end, trl'[i]? = s.core.trl[i]?) →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        ctype' = s.core.confl_type ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
      FullProbeScratchPres s s' → s.core.trail_end ≤ te' → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
      (∀ i < s.core.trail_end, trl'[i]? = s.core.trl[i]?) →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullVivSimplifySpec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 → cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
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

@[expose] def fullVivDeduceSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, cref, implied, out_ptr, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ out_ptr = c.pWorkStk2 ∧ FullSparseInvW c F0 F_cur s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      (implied = 0xFFFFFFFF#32 →
        FullConflictOkW F_cur s ∨
        (s.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
      (implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ olen mrk' ws1' ws2' rsz' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk' }
            scratch := { s.scratch with work_stk1 := ws1', work_stk2 := ws2', res_sz := rsz' } }
        FullSparseInvW c F0 F_cur s' → olen.toNat ≤ c.max_vars →
        (olen.toNat < fullArenaClauseSize s cref.toNat →
          (∀ i < olen.toNat, (ws2'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
        (FullMem c s' ⋆ R) m' → Q (olen, ()) m'

@[expose] def fullVivCommitSpec : Spec [i64, i32, i64, i32, .bool] [i64] :=
  fun (h, cref, out_ptr, olen, _used_red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ out_ptr = c.pWorkStk2 ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      olen.toNat ≤ c.max_vars ∧
      (olen.toNat < fullArenaClauseSize s cref.toNat →
        (∀ i < olen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((s.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel →
        s'.core.arena_len = s.core.arena_len →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ### 2.2 Owned target `Spec` contracts (`full_viv_clause`, `full_vivify`) -/

@[expose] def fullVivClauseSpec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullVivifySpec : Spec [i64, i64] [i64] := fun (h, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullVivTopSpecs

open FullVivTopSpecs

namespace FullVivTop

/-! ## 3. Pure `FullSparseInvW`, arena-header, and trail/decision helpers -/

theorem FullWitnessInv.with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) (tmp' : List (BitVec 32)) :
    FullWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { h with
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem FullWitnessInv.with_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) (ct cr : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with confl_type := ct, confl_ref := cr } :=
  { h with
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem FullWitnessInv.with_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) (pr : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with probing := pr } :=
  { h with
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem FullSparseInvW.with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {tmp' : List (BitVec 32)}
    (ht : tmp'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := ht }, h.1.scratch_ok⟩,
   FullWitnessInv.with_tmp h.2.1 tmp', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInvW.with_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) (ct cr : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with confl_type := ct, confl_ref := cr } } :=
  ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
   FullWitnessInv.with_confl h.2.1 ct cr, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInvW.with_res_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) (rsz : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with scratch := { s.scratch with res_sz := rsz } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with work_stk1_len := h.1.scratch_ok.work_stk1_len }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInv.with_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (pr : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with probing := pr } } := by
  obtain ⟨F_cur, hsw⟩ := h.exists_witness
  exact ⟨⟨⟨{ hsw.1.core_ok with vals_len := hsw.1.core_ok.vals_len }, hsw.1.scratch_ok⟩,
    F_cur, FullWitnessInv.with_probing hsw.2.1 pr⟩,
    hsw.2.2.1, hsw.2.2.2.1, hsw.2.2.2.2.1, hsw.2.2.2.2.2⟩

theorem FullSparseInv.of_backtrack {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {target_lvl : Nat}
    {lvl' rsns' trl' tp' : List (BitVec 32)} {vals8' : List (BitVec 8)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (htle : target_lvl ≤ s.core.cur_level)
    (hlen' : ({ s with
      core := { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                            trail_pos := tp', trail_end := te', propagated := prop',
                            cur_level := cl', unassigned := unass' }
      scratch := sc' } : FullState).LengthsOk c)
    (hpres : FullProbeScratchPres s { s with scratch := sc' })
    (hw_bt : ∀ F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl ≤ s.core.cur_level →
      FullWitnessInv c F0 F_cur
        { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                      trail_pos := tp', trail_end := te', propagated := prop',
                      cur_level := cl', unassigned := unass' }) :
    FullSparseInv c F0
      { s with
        core := { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                              trail_pos := tp', trail_end := te', propagated := prop',
                              cur_level := cl', unassigned := unass' }
        scratch := sc' } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hw' := hw_bt F_cur hw htle
  refine ⟨⟨hlen', F_cur, hw'⟩, h.2.1, h.2.2.1,
    ⟨fun i hi => by dsimp only [FullLastLearnedWf]; rw [hpres.1.1]; exact h.2.2.2.1.1 i hi,
     by rw [hpres.1.2]; exact h.2.2.2.1.2⟩, h.2.2.2.2⟩

theorem FullSparseInvW.of_backtrack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {target_lvl : Nat}
    {vals8' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (_htle : target_lvl ≤ s.core.cur_level)
    (hlen' : ({ s with
      core := { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                            trail_pos := tp', trail_end := te', propagated := prop',
                            cur_level := cl', unassigned := unass' }
      scratch := sc' } : FullState).LengthsOk c)
    (hpres : FullProbeScratchPres s { s with scratch := sc' })
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    cur_level := cl', unassigned := unass' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                              trail_pos := tp', trail_end := te', propagated := prop',
                              cur_level := cl', unassigned := unass' }
        scratch := sc' } :=
  ⟨hlen', hw', h.2.2.1, h.2.2.2.1,
   ⟨fun i hi => by dsimp only [FullLastLearnedWf]; rw [hpres.1.1]; exact h.2.2.2.2.1.1 i hi,
    by rw [hpres.1.2]; exact h.2.2.2.2.1.2⟩, h.2.2.2.2.2⟩

/-- Updating header word `ar[cref]` while preserving `PH_GARB` (`bit 19`) and `PH_SHRK` (`bit 23`)
preserves `FullSparseInvW`, `fullArenaClauseRefs`, `fullArenaClauseSize`, `fullArenaClauseGarb`,
`fullArenaClauseLits`, and `fullArenaNextOff`. -/
theorem fullArena_setHdr_preserves_sparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {hdr' : BitVec 32}
    (hgarb : (hdr' &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32))
    (hshrk : (hdr' &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32)) :
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref hdr' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r ∧
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  have hw := hsp.2.1
  have hcl := hsp.1.core_ok
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
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hsp.1.scratch_ok⟩
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
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
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
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
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
        exact (hprops _ hrs.1).2.2 ▸ hw.reason_lit_mem idx hidx hne hlg }
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs] at hr
    change fullArenaClauseGarbCore s'.core r = false at hng
    rw [(hprops r hr).2.1] at hng
    change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
    rw [(hprops r hr).2.2]
    exact hsp.2.2.2.1 r hr hng
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => by
      change s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
        (s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefsCore s'.core
      rw [hrefs]; exact hsp.2.2.2.2.1.1 i hi,
     hsp.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩,
    hrefs, fun r hr => ⟨hnxt r hr, hprops r hr⟩⟩

/-- Decision step (`cur_level := cur_level + 1`, updating `frame_trail`/`frame_dec`, then
calling `full_assign(h, lit ^^^ 1#32, 0xFFFFFFFF#32)`) preserves `FullSparseInvW c F0 F_cur`. -/
theorem vivDecideAssign_preserves_sparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {lit : BitVec 32}
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    {flags' : List (BitVec 32)} {phases' : List (BitVec 8)}
    {unass' unfl' : BitVec 64} (hfll : flags'.length = c.max_vars)
    (hphl : phases'.length = c.max_vars) :
    let nlvl := s.core.cur_level + 1
    let dlit := lit ^^^ 1#32
    let v := dlit.toNat / 2
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl dlit
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set dlit.toNat 1#8).set (dlit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set v 0xFFFFFFFF#32, trl := s.core.trl.set s.core.trail_end dlit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1
            cur_level := nlvl, unassigned := unass', unflushed := unfl' }
        scratch := { s.scratch with phases := phases' } }
    nlvl ≤ c.max_vars ∧ FullSparseInvW c F0 F_cur s' ∧
    (∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0xFF#8 →
      s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    s'.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
  intro nlvl dlit v ftrl' fdec' s'
  have hw := hsp.2.1; have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hdlit_nat : dlit.toNat = lit.toNat ^^^ 1 := by simp [dlit, BitVec.toNat_xor]
  have hdlit_lt : dlit.toNat < 2 * s.core.cur_vars := hdlit_nat ▸ litNeg_lt_two_mul hlit
  have hv_eq : v = lit.toNat / 2 := by dsimp only [v]; rw [hdlit_nat, fullInv_var_xor1]
  have hte_lt : s.core.trail_end < s.core.cur_vars :=
    hw.trail_end_lt_of_unassigned hlit hun
  have hnlvl_le : nlvl ≤ c.max_vars := by
    have := hw.cur_level_le; have := hcl.cur_vars_le; omega
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
    rw [hv_eq]; exact (hw.vals_zero_iff hlit).mp hun
  have hne_lit : dlit.toNat ^^^ 1 ≠ dlit.toNat := litNeg_ne_self dlit.toNat
  have hdlit_neg : dlit.toNat ^^^ 1 = lit.toNat := by
    rw [hdlit_nat]; exact litNeg_litNeg lit.toNat
  have hv_lt : v < c.max_vars := by rw [hv_eq]; have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hnlvl_lt32 : nlvl < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then dlit.toNat else (s.core.trl[i]?.getD 0#32).toNat :=
    fun i _ => by
      by_cases he : i = s.core.trail_end
      · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
      · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars,
      (s'.core.lvl[w]?.getD 0#32).toNat =
        if w = v then nlvl else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt),
        bv32_ofNat_toNat hnlvl_lt32]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 =
        if l = dlit.toNat ^^^ 1 then 0xFF#8 else if l = dlit.toNat then 1#8
        else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = dlit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = dlit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars,
      s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
        if w = v then 0xFFFFFFFF#32 else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
      vals_len := by simp [s', hcl.vals_len], flags_len := hfll,
      lvl_len := by simp [s', hcl.lvl_len], rsns_len := by simp [s', hcl.rsns_len],
      trl_len := by simp [s', hcl.trl_len], trail_pos_len := by simp [s', hcl.trail_pos_len],
      frame_trail_len := by simp [s', ftrl', hcl.frame_trail_len],
      frame_dec_len := by simp [s', fdec', hcl.frame_dec_len],
      trail_end_le := by dsimp [s']; omega,
      propagated_le := by have := hcl.propagated_le; dsimp [s']; omega },
     { hscl with phases_len := hphl }⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
      cur_level_le := by have := hw.cur_level_le; dsimp [s', nlvl]; omega
      trail_lits_lt := fun i hi => by
        rw [htrl_get i hi]; split
        · exact hdlit_lt
        · exact hw.trail_lits_lt i (by dsimp [s'] at hi; omega)
      trail_vars_nodup := fun i j hi hj hveq => by
        rw [htrl_get i hi, htrl_get j hj] at hveq
        split at hveq <;> split at hveq
        · omega
        · exact absurd hveq.symm (hnot_var j (by dsimp [s'] at hj; omega))
        · exact absurd hveq (hnot_var i (by dsimp [s'] at hi; omega))
        · exact hw.trail_vars_nodup i j (by dsimp [s'] at hi; omega)
            (by dsimp [s'] at hj; omega) hveq
      vals_domain := fun l hl => by
        rw [hvals_get l hl]; split; · exact Or.inr (Or.inr rfl)
        split; · exact Or.inr (Or.inl rfl)
        exact hw.vals_domain l hl
      vals_true_iff := fun l hl => by
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = dlit.toNat ^^^ 1
          · simp [hneg] at h1
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = dlit.toNat
            · exact ⟨s.core.trail_end, by dsimp [s']; omega,
                by rw [htrl_get _ (by omega)]; simp [hpos]⟩
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
              exact ⟨i, by dsimp [s']; omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by dsimp [s'] at hi; omega)
            have h1 : l ≠ dlit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ dlit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr
              ⟨i, by dsimp [s'] at hi; omega, heq⟩
      vals_false_iff := fun l hl => by
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = dlit.toNat ^^^ 1
          · exact ⟨s.core.trail_end, by dsimp [s']; omega, by
              rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]
              exact (litNeg_litNeg _).symm⟩
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = dlit.toNat
            · simp [hpos] at h1
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
              exact ⟨i, by dsimp [s']; omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have hl_eq : l = dlit.toNat ^^^ 1 := by
              have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
              rw [h1] at h; exact h.symm
            simp [hl_eq]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by dsimp [s'] at hi; omega); rw [heq] at h
              rwa [fullInv_var_xor1] at h
            have h1 : l ≠ dlit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ dlit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr
              ⟨i, by dsimp [s'] at hi; omega, heq⟩
      lvl_le := fun i hi => by
        rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp [s', nlvl]
        · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
          simp only [hie, ↓reduceIte]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
          simp only [hnot_var i hilt, ↓reduceIte]
          have := hw.lvl_le i hilt; dsimp [s', nlvl]; omega
      dec_earliest := fun i j hi hj hleq hdec => by
        rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
        by_cases hje : j = s.core.trail_end
        · subst hje; simp only [↓reduceIte] at hleq hdec
          by_cases hie : i = s.core.trail_end
          · omega
          · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
            simp only [hie, ↓reduceIte] at hleq
            rw [hlvl_get v (by omega),
              hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hleq
            simp only [hnot_var i hilt, ↓reduceIte] at hleq
            have := hw.lvl_le i hilt; omega
        · by_cases hie : i = s.core.trail_end
          · dsimp [s'] at hj; omega
          · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
            have hjlt : j < s.core.trail_end := by dsimp [s'] at hj; omega
            simp only [hie, hje, ↓reduceIte] at hleq hdec
            rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega),
              hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hleq
            rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega),
              hrsn_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hdec
            simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
            exact hw.dec_earliest i j hilt hjlt hleq hdec
      levels_inhabited := fun L hL1 hLle => by
        by_cases hLn : L = nlvl
        · subst hLn; refine ⟨s.core.trail_end, by dsimp [s']; omega, ?_⟩
          rw [htrl_get _ (by omega)]; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp
        · have hLold : L ≤ s.core.cur_level := by dsimp [s', nlvl] at hLle; omega
          obtain ⟨i, hi, hli⟩ := hw.levels_inhabited L hL1 hLold
          refine ⟨i, by dsimp [s']; omega, ?_⟩
          rw [htrl_get i (by omega)]; simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hi; omega)]; simp [hnot_var i hi, hli]
      level0_sound := fun i hi hli => by
        rw [htrl_get i hi] at hli ⊢; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hli; rw [hlvl_get v (by omega)] at hli; simp [nlvl] at hli
        · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
          simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hli
          simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hw.level0_sound i hilt hli
      trail_pos_inv := fun i hi => by
        rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · subst hie; simp only [↓reduceIte]; dsimp only [s']
          rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
          simp only [hie, ↓reduceIte]; dsimp only [s']
          rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]; exact hw.trail_pos_inv i hilt
      level0_rsn_none := fun idx hidx hli => by
        rw [htrl_get idx hidx] at hli ⊢; by_cases hie : idx = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hli; rw [hlvl_get v (by omega)] at hli; simp [nlvl] at hli
        · have hilt : idx < s.core.trail_end := by dsimp [s'] at hidx; omega
          simp only [hie, ↓reduceIte] at hli ⊢; have hnv := hnot_var idx hilt
          rw [hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hli
          simp only [hnv, ↓reduceIte] at hli
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnv, ↓reduceIte]; exact hw.level0_rsn_none idx hilt hli
      frame_trail_lt := fun L hL => by
        dsimp only [s', ftrl'] at hL ⊢
        by_cases hLn : L = nlvl
        · subst hLn; rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]; omega
        · rw [List.getElem?_set_ne (Ne.symm hLn)]
          have := hw.frame_trail_lt L (by dsimp [nlvl] at hL; omega); omega
      frame_trail_mono := fun L1 L2 h12 h2 => by
        dsimp only [s', ftrl'] at h2 ⊢
        by_cases h2n : L2 = nlvl
        · subst h2n; rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
          by_cases h1n : L1 = nlvl
          · subst h1n; rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega),
              Option.getD_some, bv32_ofNat_toNat hte_lt32]
            exact Nat.le_refl _
          · rw [List.getElem?_set_ne (Ne.symm h1n)]
            exact hw.frame_trail_lt L1 (by dsimp [nlvl] at h12; omega)
        · have h1n : L1 ≠ nlvl := by dsimp [nlvl] at h2; omega
          rw [List.getElem?_set_ne (Ne.symm h1n), List.getElem?_set_ne (Ne.symm h2n)]
          exact hw.frame_trail_mono L1 L2 h12 (by dsimp [nlvl] at h2; omega)
      frame_trail_before_lt := fun L hL1 hLle i hi => by
        dsimp only [s', ftrl'] at hLle hi
        by_cases hLn : L = nlvl
        · subst hLn; rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega),
            Option.getD_some, bv32_ofNat_toNat hte_lt32] at hi
          rw [htrl_get i (by omega), ite_eq_right (by omega)]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hi; omega), ite_eq_right (hnot_var i hi)]
          have := hw.lvl_le i hi; dsimp [nlvl]; omega
        · rw [List.getElem?_set_ne (Ne.symm hLn)] at hi
          have hLle0 : L ≤ s.core.cur_level := by dsimp [s', nlvl] at hLle; omega
          have hi_lt : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle0)
          rw [htrl_get i (by omega), ite_eq_right (by omega)]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hi_lt; omega),
            ite_eq_right (hnot_var i hi_lt)]
          exact hw.frame_trail_before_lt L hL1 hLle0 i hi
      frame_dec_lt := fun L hL1 hLle => by
        dsimp only [s', fdec'] at hLle ⊢
        by_cases hLn : L = nlvl
        · subst hLn; rw [List.getElem?_set_self (by rw [hcl.frame_dec_len]; omega),
            Option.getD_some]; exact hdlit_lt
        · rw [List.getElem?_set_ne (Ne.symm hLn)]
          exact hw.frame_dec_lt L hL1 (by dsimp [s', nlvl] at hLle; omega)
      reason_inv := fun idx hidx hne => by
        rw [htrl_get idx hidx] at hne ⊢; by_cases hie : idx = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hne; rw [hrsn_get v (by omega)] at hne; simp at hne
        · have hilt : idx < s.core.trail_end := by dsimp [s'] at hidx; omega
          simp only [hie, ↓reduceIte] at hne ⊢; have hnv := hnot_var idx hilt
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne ⊢
          simp only [hnv, ↓reduceIte] at hne ⊢
          have hrs := hw.reason_inv idx hilt hne
          by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
          · rw [ite_eq_left hb] at hrs ⊢; obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
            refine ⟨hrs.1, hrs.2.1, m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
            · have hot_v : ((s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
                intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get _ (by omega), hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
              rw [ite_eq_right hot_v, ite_eq_right hnv]; exact hlvl_le
          · rw [ite_eq_right hb] at hrs ⊢
            refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
            have hq' : q ∈ fullArenaClauseLitsCore s.core
                (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32).toNat := by
              simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using hq
            refine (hrs.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ⟨m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
            · have hq_lt : q < 2 * s.core.cur_vars := hw.arena.lits_lt _ hrs.1 hrs.2.1 q hq'
              have hqv : q / 2 ≠ v := by
                intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get _ (by omega), hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
              simp [hnv, hqv, hlvl_le]
      reason_lit_mem := fun idx hidx hne hlg => by
        rw [htrl_get idx hidx] at hne hlg ⊢; by_cases hie : idx = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hne; rw [hrsn_get v (by omega)] at hne; simp at hne
        · have hilt : idx < s.core.trail_end := by dsimp [s'] at hidx; omega
          simp only [hie, ↓reduceIte] at hne hlg ⊢; have hnv := hnot_var idx hilt
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne hlg ⊢
          simp only [hnv, ↓reduceIte] at hne hlg ⊢
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
            hw.reason_lit_mem idx hilt hne hlg }
  refine ⟨hnlvl_le, ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩,
    fun l hl hff => ?_, ?_⟩
  · rw [hvals_get l hl]; split
    · rfl
    · split
      · rename_i hpos; exfalso
        have hlv : l / 2 ≠ v := by
          obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hff
          have := hnot_var i hi; rw [heq, fullInv_var_xor1] at this; exact this
        exact hlv (by rw [hpos])
      · exact hff
  · rw [hvals_get lit.toNat hlit, ite_eq_left hdlit_neg.symm]

theorem falsified_preserved_of_trailExt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hw' : FullWitnessInv c F0 F_cur k') (hcv : k'.cur_vars = k.cur_vars)
    (hte : k.trail_end ≤ k'.trail_end) (htrl : ∀ i < k.trail_end, k'.trl[i]? = k.trl[i]?)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hff : k.vals[l]?.getD 0#8 = 0xFF#8) :
    k'.vals[l]?.getD 0#8 = 0xFF#8 := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hff
  exact (hw'.vals_false_iff l (hcv ▸ hl)).mpr ⟨i, by omega, by rwa [htrl i hi]⟩

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

theorem vals_xor1_eq_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l : Nat}
    (hl : l < 2 * k.cur_vars) (hun : k.vals[l]?.getD 0#8 = 0#8) :
    k.vals[l ^^^ 1]?.getD 0#8 = 0#8 := by
  have hl1 : l ^^^ 1 < 2 * k.cur_vars := litNeg_lt_two_mul hl
  rcases hw.vals_domain (l ^^^ 1) hl1 with h0 | h1 | hff
  · exact h0
  · obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff (l ^^^ 1) hl1).mp h1
    have hff := (hw.vals_false_iff l hl).mpr ⟨i, hi, heq⟩
    rw [hun] at hff; cases hff
  · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff (l ^^^ 1) hl1).mp hff
    rw [show l ^^^ 1 ^^^ 1 = l from litNeg_litNeg l] at heq
    have ht := (hw.vals_true_iff l hl).mpr ⟨i, hi, heq⟩
    rw [hun] at ht; cases ht

theorem vivCopy_perm_lits {tmp tmp' ar : List (BitVec 32)} {cref sz : Nat}
    (htmp_len : tmp.length ≥ sz) (har_len : cref + 3 + sz ≤ ar.length)
    (hcp : ∀ k < sz, tmp[k]? = ar[cref + 3 + k]?)
    (hperm : (tmp'.take sz).Perm (tmp.take sz))
    (hsz' : tmp'.length ≥ sz) :
    ((tmp'.take sz).map BitVec.toNat).Perm (((ar.drop (cref + 3)).take sz).map BitVec.toNat) := by
  have heq : (tmp.take sz).map BitVec.toNat = ((ar.drop (cref + 3)).take sz).map BitVec.toNat := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop]
      rw [Nat.min_eq_left htmp_len, Nat.min_eq_left (by omega)]
    · intro j hj1 _
      have hj : j < sz := by
        simp only [List.length_map, List.length_take] at hj1; omega
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hget := hcp j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hget
      exact congrArg BitVec.toNat (Option.some.inj hget)
  have _ := hsz'
  exact heq ▸ hperm.map BitVec.toNat

theorem vivTmp_mem_of_perm {tmp' : List (BitVec 32)} {lits : List Nat} {sz : Nat}
    (hsz' : sz ≤ tmp'.length) (hperm : ((tmp'.take sz).map BitVec.toNat).Perm lits) :
    (∀ k < sz, (tmp'[k]?.getD 0#32).toNat ∈ lits) ∧
    (∀ l ∈ lits, ∃ k < sz, (tmp'[k]?.getD 0#32).toNat = l) := by
  constructor
  · intro k hk
    have hk_take : (tmp'[k]?.getD 0#32).toNat ∈ (tmp'.take sz).map BitVec.toNat := by
      rw [List.mem_map]
      refine ⟨tmp'[k]'(by omega), ?_, ?_⟩
      · have hlt : k < (tmp'.take sz).length := by simp [List.length_take]; omega
        simpa [List.getElem_take] using List.getElem_mem hlt
      · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hperm.mem_iff.mp hk_take
  · intro l hl
    have hmem := hperm.mem_iff.mpr hl
    rw [List.mem_map] at hmem
    obtain ⟨x, hx, rfl⟩ := hmem
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    have hk' : k < sz := by rw [List.length_take] at hk; omega
    refine ⟨k, hk', ?_⟩
    rw [List.getElem_take] at hget
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]

theorem fullSparseInvW_of_prop_state {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := sc' } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hnd' : FullArenaVarsNodup
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' })
    (hpres : FullProbeScratchPres s
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' })
    (hrefs : ∀ ref ∈ fullArenaClauseRefs s,
      ref ∈ fullArenaClauseRefs
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := sc' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' } :=
  ⟨hlen', hw', hsp.2.2.1, hnd',
   ⟨fun i hi => by
     dsimp only [FullLastLearnedWf]
     rw [hpres.1.1]
     rcases hsp.2.2.2.2.1.1 i hi with hff | hmem
     · exact Or.inl hff
     · exact Or.inr (hrefs _ hmem),
    by rw [hpres.1.2]; exact hsp.2.2.2.2.1.2⟩,
   hsp.2.2.2.2.2⟩

end FullVivTop

end LeanQbe.T.Examples.Kissat.Full
