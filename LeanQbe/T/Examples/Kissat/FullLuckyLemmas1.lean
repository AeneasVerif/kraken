module

public import LeanQbe.T.Examples.Kissat.Full3
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Lucky Probing Helpers, `Spec` Contracts & `full_lucky_polar` (`Stage 4`, Part 1)

Provides:
1. Strictly file/section-local `FullLuckyTactics` (`open scoped FullArenaTactics`) and BV helpers.
2. `FullLuckySpecs`: UNSAT-only Stage-4 `Spec` contracts aligned with `FullSpec{1,2,3}.lean`
   plus `#1058`/`#1063`/`#1064` callee alignment catches (`full_assign`, `full_backtrack`,
   `full_propagate`, `full_analyze`) and the `3` owned specs (`full_lucky_polar`,
   `full_lucky_scan`, `full_lucky`).
3. Pure invariant, backtrack/propagate/decide, OTFS level-0 collapse, and `trail_end` bound lemmas.
4. Parametric `(Γ : Env)` `Func.wp` proof for `full_lucky_polar` (`full_lucky_polar_wp`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Strictly scoped tactic helpers and bitvector arithmetic lemmas (`FullLuckyTactics`) -/

namespace FullLuckyTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "flk_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "flk_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "flk_steps" : tactic =>
  `(tactic| (
      (try flk_unmdata)
      (repeat flk_strip)
      c0_steps
      repeat (any_goals (flk_strip; repeat flk_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
scoped elab "flk_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      evalTactic (← `(tactic| all_goals (repeat flk_strip)))
      for g' in ← getUnsolvedGoals do
        if ← g'.isAssigned then continue
        setGoals [g']
        let ty := (← Lean.instantiateMVars (← g'.getType)).consumeMData
        if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
            ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.group then
          out := out.push g'
        else if ← LeanQbe.T.C0Step.stepOnce then
          evalTactic (← `(tactic| all_goals (repeat flk_strip)))
          go (fuel - 1)
          out := out ++ (← getUnsolvedGoals)
        else
          out := out.push g'
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

theorem bv8_eq0_of_not_slt_sgt {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8)
    (h1 : (0#32).slt (x.signExtend 32) = false) (h2 : (x.signExtend 32).slt 0#32 = false) :
    x = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> first | rfl | (exfalso; revert h1 h2; decide)

theorem bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv64_trunc32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), bv32_ofNat_toNat hn, Nat.mod_eq_of_lt hn]

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) :
    (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_add1_toNat {a : BitVec 64} (h : a.toNat + 1 < 2 ^ 64) :
    (a + 1#64).toNat = a.toNat + 1 := bv64_add_toNat h

theorem bv64_shl1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (x <<< 1#64).toNat = 2 * x.toNat := by
  have h1 : (x <<< 1#64).toNat = (x.toNat * 2) % 2 ^ 64 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [h1, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

theorem bv64_shl1_add1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    ((x <<< 1#64) + 1#64).toNat = 2 * x.toNat + 1 := by
  rw [bv64_add1_toNat (by rw [bv64_shl1_toNat hx]; omega), bv64_shl1_toNat hx]

theorem bv64_shl1_u32_toNat (x : BitVec 32) :
    (x.setWidth 64 <<< 1#64).toNat = 2 * x.toNat := by
  have hx := x.isLt
  have h1 : (x.setWidth 64 <<< 1#64).toNat = ((x.setWidth 64).toNat * 2) % 2 ^ 64 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [h1, bv_c0_zext32_64, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem bv32_shl1_trunc32_toNat {v : BitVec 64} (hv : 2 * v.toNat < 2 ^ 32) :
    ((v <<< 1#64).setWidth 32).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_setWidth, bv64_shl1_toNat (by omega), Nat.mod_eq_of_lt hv]

theorem bv32_shl1_or1_trunc32_toNat {v : BitVec 64} (hv : 2 * v.toNat + 1 < 2 ^ 32) :
    (((v <<< 1#64).setWidth 32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  rw [BitVec.toNat_or, bv32_shl1_trunc32_toNat (by omega)]
  change (2 * v.toNat) ||| 1 = 2 * v.toNat + 1
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_or]
    simp only [Nat.testBit_succ, show (1 : Nat) / 2 = 0 from rfl,
      show (2 * v.toNat) / 2 = v.toNat from by omega,
      show (2 * v.toNat + 1) / 2 = v.toNat from by omega,
      Nat.zero_testBit, Bool.or_false]

theorem bv32_mask_lo31_toNat (x : BitVec 32) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat % 2 ^ 31 := by
  simpa [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod x.toNat 31

end FullLuckyTactics

open FullLuckyTactics
open scoped FullArenaTactics FullLuckyTactics

/-! ## 2. Canonical Stage-4 invariants and `FullLuckySpecs` -/

namespace FullLuckySpecs

/-- Variable marks (`mrk[0 ..< max_vars]`) are cleared to `0#8`. -/
def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

/-- Both variable marks (`mrk`) and literal marks (`lit_mark`) are cleared to `0#8`. -/
def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Every live arena clause has pairwise distinct variables (`NoDup` & non-tautology). -/
def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- Every active slot in `last_learned[0 ..< 8]` is `0xFFFFFFFF#32` or a valid arena ref. -/
def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Soundness-adjacent scratch bounds (`last_learned` validity + `extend_len ≤ extend_cap`). -/
def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Canonical sparse-mode (2WL) UNSAT-only solver invariant (`dense_mode = 0#64`). -/
def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Scratch-level equality predicate preserving `last_learned` and `extend_len`. -/
def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

/-- Extended scratch-frame predicate preserved by `full_backtrack` and `full_propagate`. -/
def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

/-- Explicit-witness sparse-mode invariant (`FullSparseInv c F0 s ↔ ∃ F_cur, ...`). -/
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
def FullConflictOkW (F_cur : List (List Nat)) (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat])) ∨
  (s.core.confl_type ≠ 1#64 ∧
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

/-- At `cur_level = 0`, all trail literals have level `0` and `rsn = 0xFFFFFFFF#32`, so
`FullOtfsWitnessInv` collapses directly to `FullWitnessInv`. -/
theorem FullOtfsWitnessInv.toWitness_of_level0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) : FullWitnessInv c F0 F_cur k :=
  { ext_sound := h.ext_sound, inconsistent_sound := h.inconsistent_sound
    arena := h.arena, watches := h.watches, cur_level_le := h.cur_level_le
    trail_lits_lt := h.trail_lits_lt, trail_vars_nodup := h.trail_vars_nodup
    vals_domain := h.vals_domain, vals_true_iff := h.vals_true_iff
    vals_false_iff := h.vals_false_iff, lvl_le := h.lvl_le, dec_earliest := h.dec_earliest
    levels_inhabited := h.levels_inhabited, level0_sound := h.level0_sound
    trail_pos_inv := h.trail_pos_inv, level0_rsn_none := h.level0_rsn_none
    frame_trail_lt := h.frame_trail_lt, frame_trail_mono := h.frame_trail_mono
    frame_trail_before_lt := h.frame_trail_before_lt, frame_dec_lt := h.frame_dec_lt
    reason_inv := fun idx hidx hne => by
      have h0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := h.lvl_le idx hidx; omega
      exact absurd (h.level0_rsn_none idx hidx h0) hne
    reason_lit_mem := fun idx hidx hne _ => by
      have h0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := h.lvl_le idx hidx; omega
      exact absurd (h.level0_rsn_none idx hidx h0) hne }

/-- Sparse state bundled with `FullOtfsWitnessInv` (`full_analyze` `0#64` return). -/
def FullOtfsInvW (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
  s.core.dense_mode = 0#64 ∧ ∃ F_cur, FullOtfsWitnessInv c F0 F_cur s.core

theorem FullOtfsInvW.toSparse_of_level0 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullOtfsInvW c F0 s) (hl0 : s.core.cur_level = 0) : FullSparseInv c F0 s :=
  let ⟨hlen, hlm, hnd, hext, hdm, F_cur, hw⟩ := h
  ⟨⟨hlen, F_cur, hw.toWitness_of_level0 hl0⟩, hlm, hnd, hext, hdm⟩

/-- Trail prefix and level-assignment preservation across propagation. -/
def FullTrailExt (k k' : FullCoreState) : Prop :=
  k.trail_end ≤ k'.trail_end ∧
  (∀ i < k.trail_end, k'.trl[i]? = k.trl[i]?) ∧
  (∀ i < k.trail_end,
    k'.lvl[(k.trl[i]?.getD 0#32).toNat / 2]? = k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?)

/-! ### 2.1 Callee `Spec` contracts (`Full1`, `Full2` aligned + `#1058`/`#1063`/`#1064`) -/

def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

def fullAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
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
        (FullMem c s' ⋆ R) m' → Q () m'

def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
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
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core →
        ∀ l < 2 * s.core.cur_vars,
          vals'[l]?.getD 0#8 =
            if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
              s.core.vals[l]?.getD 0#8 else 0#8) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
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
      FullProbeScratchPres s s' → FullTrailExt s.core s'.core → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullAnalyzeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ FullConflictOkW F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullOtfsInvW c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ### 2.2 Owned target `Spec` contracts (`Full3`) -/

def fullLuckyPolarSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64, (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) → Q (r, ()) m

def fullLuckyScanSpec : Spec [i64, .bool, .bool] [i64] := fun (h, _pm, _fwd, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 →
        FullSparseInv c F0 s' ∧ (s.core.cur_level = 0 → s'.core.cur_level = 0)) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullLuckySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → s'.core.probing = 0#64 →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s') →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullLuckySpecs

open FullLuckySpecs

/-! ## 3. Pure state, invariant, and decision-assignment helpers -/

namespace FullLuckyHelpers

private theorem nodup_subset_length_le :
    ∀ {l1 l2 : List Nat}, l1.Nodup → l1 ⊆ l2 → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l2, hnd, hsub => by
    have ha_mem : a ∈ l2 := hsub (by simp)
    have hnd_t : t.Nodup := (List.nodup_cons.mp hnd).2
    have ha_not : a ∉ t := (List.nodup_cons.mp hnd).1
    have hsub_t : t ⊆ l2.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun heq => ha_not (by simpa [heq] using hx))).mpr (hsub (by simp [hx]))
    have hih := nodup_subset_length_le hnd_t hsub_t
    have herase : (l2.erase a).length = l2.length - 1 := List.length_erase_of_mem ha_mem
    have hpos : 0 < l2.length := List.length_pos_of_mem ha_mem
    simp only [List.length_cons]
    omega

theorem FullSparseInv.with_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (v : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with probing := v } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hw' : FullWitnessInv c F0 F_cur { s.core with probing := v } :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  refine ⟨⟨⟨{ h.1.lengths.core_ok with cur_vars_le := h.1.lengths.core_ok.cur_vars_le },
    h.1.lengths.scratch_ok⟩, F_cur, hw'⟩, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  exact h.2.2.2.1

theorem FullSparseInv.with_fuel {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (f : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with fuel := f } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hw' : FullWitnessInv c F0 F_cur { s.core with fuel := f } :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  refine ⟨⟨⟨{ h.1.lengths.core_ok with cur_vars_le := h.1.lengths.core_ok.cur_vars_le },
    h.1.lengths.scratch_ok⟩, F_cur, hw'⟩, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  exact h.2.2.2.1

theorem FullSparseInv.with_scratch_pres {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  refine ⟨⟨⟨h.1.lengths.core_ok, hok⟩, F_cur, hw⟩, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  refine ⟨fun i hi => ?_, by simpa [hext] using h.2.2.2.1.2⟩
  simpa [FullLastLearnedWf, fullArenaClauseRefs, hll] using h.2.2.2.1.1 i hi

theorem FullExtScratchOk.of_pres {c : FullCfg} {s s' : FullState} (h : FullExtScratchOk c s)
    (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullExtScratchOk c s' := by
  refine ⟨fun i hi => ?_, by simpa [hpres.2] using h.2⟩
  rcases h.1 i hi with hff | href
  · left; simpa [hpres.1] using hff
  · right; simpa [hpres.1] using hsub _ href

theorem FullSparseInv.of_propagate {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hnd' : FullArenaVarsNodup s')
    (hpres : FullProbeScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s')
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = 0#64) : FullSparseInv c F0 s' := by
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨fun v hv => by simpa [hmrk] using h.2.1.1 v hv,
    fun l hl => by simpa [hlm] using h.2.1.2 l hl⟩, hnd',
    FullExtScratchOk.of_pres h.2.2.2.1 hpres.1 hsub, hdm⟩

theorem FullSparseInv.of_backtrack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hpres : FullProbeScratchPres s s')
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = 0#64) : FullSparseInv c F0 s' := by
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    simp [fullArenaClauseRefs, fullArenaClauseRefsCore, har, hal]
  have hnd' : FullArenaVarsNodup s' := fun r hr hg => by
    have h1 : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := by
      simp [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, har]
    have h2 : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, har]
    rw [hrefs] at hr; rw [h1] at hg; rw [h2]; exact h.2.2.1 r hr hg
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨fun v hv => by simpa [hmrk] using h.2.1.1 v hv,
    fun l hl => by simpa [hlm] using h.2.1.2 l hl⟩, hnd',
    FullExtScratchOk.of_pres h.2.2.2.1 hpres.1 (fun r hr => hrefs ▸ hr), hdm⟩

theorem FullOtfsInvW.of_backtrack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullOtfsInvW c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hpres : FullProbeScratchPres s s')
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = 0#64) : FullSparseInv c F0 s' := by
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    simp [fullArenaClauseRefs, fullArenaClauseRefsCore, har, hal]
  have hnd' : FullArenaVarsNodup s' := fun r hr hg => by
    have h1 : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := by
      simp [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, har]
    have h2 : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, har]
    rw [hrefs] at hr; rw [h1] at hg; rw [h2]; exact h.2.2.1 r hr hg
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨fun v hv => by simpa [hmrk] using h.2.1.1 v hv,
    fun l hl => by simpa [hlm] using h.2.1.2 l hl⟩, hnd',
    FullExtScratchOk.of_pres h.2.2.2.1 hpres.1 (fun r hr => hrefs ▸ hr), hdm⟩

private theorem nodup_map_range (f : Nat → Nat) : ∀ n,
    (∀ i j, i < n → j < n → f i = f j → i = j) → ((List.range n).map f).Nodup
  | 0, _ => by simp
  | n + 1, hinj => by
    rw [List.range_succ, List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨nodup_map_range f n fun i j hi hj => hinj i j (by omega) (by omega),
      by simp, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map, List.mem_range] at hx
    simp only [List.mem_singleton] at hy
    obtain ⟨i, hi, rfl⟩ := hx
    subst hy
    have heq := hinj i n (by omega) (by omega) hxy
    omega

theorem trail_end_lt_of_unassigned_var {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {v : Nat}
    (hv : v < k.cur_vars) (hval0 : k.vals[2 * v]?.getD 0#8 = 0#8) :
    k.trail_end < k.cur_vars := by
  have hnone : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
    intro i hi heq
    have heq' : litVar (k.trl[i]?.getD 0#32).toNat = litVar (2 * v) := by
      simp only [litVar]; omega
    rcases (litVar_eq_iff _ (2 * v)).mp heq' with h1 | h2
    · have ht := (hw.vals_true_iff (2 * v) (by omega)).mpr ⟨i, hi, h1⟩
      rw [hval0] at ht; cases ht
    · have hf := (hw.vals_false_iff (2 * v) (by omega)).mpr ⟨i, hi, h2⟩
      rw [hval0] at hf; cases hf
  let vs := (List.range k.trail_end).map fun i => (k.trl[i]?.getD 0#32).toNat / 2
  have hnd : vs.Nodup :=
    nodup_map_range (fun i => (k.trl[i]?.getD 0#32).toNat / 2) k.trail_end
      fun i j hi hj heq => hw.trail_vars_nodup i j hi hj heq
  have hsub : vs ⊆ (List.range k.cur_vars).erase v := by
    intro w hw_mem
    simp only [vs, List.mem_map, List.mem_range] at hw_mem
    obtain ⟨i, hi, rfl⟩ := hw_mem
    refine (List.mem_erase_of_ne (hnone i hi)).mpr ?_
    exact List.mem_range.mpr (Nat.div_lt_of_lt_mul (hw.trail_lits_lt i hi))
  have hlen_le : vs.length ≤ ((List.range k.cur_vars).erase v).length :=
    nodup_subset_length_le hnd hsub
  have herase_len : ((List.range k.cur_vars).erase v).length = k.cur_vars - 1 := by
    rw [List.length_erase_of_mem (List.mem_range.mpr hv), List.length_range]
  have hvslen : vs.length = k.trail_end := by simp [vs]
  omega

theorem FullWitnessInv.vals_other_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {v l : Nat}
    (hl_lt : l < 2 * k.cur_vars) (hl_v : l / 2 = v) (hval0 : k.vals[2 * v]?.getD 0#8 = 0#8) :
    k.vals[l]?.getD 0#8 = 0#8 := by
  rcases hw.vals_domain l hl_lt with h0 | h1 | h2
  · exact h0
  · obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl_lt).mp h1
    have hv_eq : litVar (k.trl[i]?.getD 0#32).toNat = litVar (2 * v) := by
      simp only [litVar]; omega
    rcases (litVar_eq_iff _ (2 * v)).mp hv_eq with h1' | h2'
    · have ht := (hw.vals_true_iff (2 * v) (by omega)).mpr ⟨i, hi, h1'⟩
      rw [hval0] at ht; cases ht
    · have hf := (hw.vals_false_iff (2 * v) (by omega)).mpr ⟨i, hi, h2'⟩
      rw [hval0] at hf; cases hf
  · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl_lt).mp h2
    have hv_eq : litVar (k.trl[i]?.getD 0#32).toNat = litVar (2 * v) := by
      simp only [litVar]; rw [heq, fullInv_var_xor1]; omega
    rcases (litVar_eq_iff _ (2 * v)).mp hv_eq with h1' | h2'
    · have ht := (hw.vals_true_iff (2 * v) (by omega)).mpr ⟨i, hi, h1'⟩
      rw [hval0] at ht; cases ht
    · have hf := (hw.vals_false_iff (2 * v) (by omega)).mpr ⟨i, hi, h2'⟩
      rw [hval0] at hf; cases hf

theorem lucky_decide_preserves_fullSparseInv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {lit : BitVec 32} {v : Nat} (hinv : FullSparseInv c F0 s) (hv_lt : v < s.core.cur_vars)
    (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8) (hlit_v : lit.toNat / 2 = v)
    {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64} {phases' : List (BitVec 8)}
    (hfl_len : flags'.length = c.max_vars) (hph_len : phases'.length = c.max_vars) :
    let nlvl := s.core.cur_level + 1
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl lit
    let s' : FullState :=
      { core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set v 0xFFFFFFFF#32, trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec'
            trail_end := s.core.trail_end + 1, cur_level := nlvl
            unassigned := unas', unflushed := unfl' }
        scratch := { s.scratch with phases := phases' } }
    FullSparseInv c F0 s' ∧ s'.LengthsOk c ∧ s.core.trail_end < s.core.cur_vars ∧
    s.core.cur_level + 1 ≤ c.max_vars ∧ s.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
  intro nlvl ftrl' fdec' s'
  have hcl := hinv.1.lengths.core_ok
  have hsc := hinv.1.lengths.scratch_ok
  obtain ⟨F_cur, hw⟩ := hinv.1.witness
  have hcv_le := hcl.cur_vars_le
  have hte_lt : s.core.trail_end < s.core.cur_vars :=
    trail_end_lt_of_unassigned_var hw hv_lt hval0
  have hcl_lt : s.core.cur_level + 1 ≤ c.max_vars := by
    have := hw.cur_level_le; omega
  have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
  have hval_lit : s.core.vals[lit.toNat]?.getD 0#8 = 0#8 :=
    FullWitnessInv.vals_other_zero hw hlit_lt hlit_v hval0
  have hnot_v : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    hlit_v ▸ (hw.vals_zero_iff hlit_lt).mp hval_lit
  have hte32 : s.core.trail_end < 2 ^ 32 := by
    have := fullInv_max_vars_lt32 c; omega
  have hcore' : FullCoreInv c F0 s' := by
    have hc0 := chronoAssign_preserves_fullCore hinv.1
      (lit := lit) (rsn := 0xFFFFFFFF#32) (alvl := nlvl) (cur_level' := nlvl)
      (propagated' := s.core.propagated)
      (flags' := flags') (frame_trail' := ftrl') (frame_dec' := fdec')
      (unassigned' := unas') (unflushed' := unfl')
      (scratch' := { s.scratch with phases := phases' })
      (hsok' := { hsc with phases_len := hph_len })
      (hfll := hfl_len)
      (hftl := by simp [ftrl', hcl.frame_trail_len])
      (hfdl := by simp [fdec', hcl.frame_dec_len])
      (hlit := hlit_lt) (hun := hval_lit)
      (halvl_le := Nat.le_refl _)
      (hprop_le := by have := hcl.propagated_le; omega)
      (hcur_le := by have := hw.cur_level_le; dsimp [nlvl]; omega)
      (hft_lt := fun L hL => by
        by_cases hLn : L = nlvl
        · subst hLn; dsimp [ftrl']
          rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; exact Nat.lt_succ_of_le hcl_lt),
            Option.getD_some, bv32_ofNat_toNat hte32]
          omega
        · dsimp [ftrl']; rw [List.getElem?_set_ne (Ne.symm hLn)]
          have hL0 : L ≤ s.core.cur_level := by dsimp [nlvl] at hL; omega
          exact Nat.le_trans (hw.frame_trail_lt L hL0) (Nat.le_succ _))
      (hft_mono := fun L1 L2 h12 h2 => by
        by_cases h2n : L2 = nlvl
        · subst h2n; dsimp [ftrl']
          rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; exact Nat.lt_succ_of_le hcl_lt),
            Option.getD_some, bv32_ofNat_toNat hte32]
          by_cases h1n : L1 = nlvl
          · subst h1n
            rw [List.getElem?_set_self
              (by rw [hcl.frame_trail_len]; exact Nat.lt_succ_of_le hcl_lt),
              Option.getD_some, bv32_ofNat_toNat hte32]
            exact Nat.le_refl _
          · rw [List.getElem?_set_ne (Ne.symm h1n)]
            have h10 : L1 ≤ s.core.cur_level := by dsimp [nlvl] at h12; omega
            exact hw.frame_trail_lt L1 h10
        · dsimp [ftrl']
          have h20 : L2 ≤ s.core.cur_level := by dsimp [nlvl] at h2; omega
          have h1n : L1 ≠ nlvl := by dsimp [nlvl]; omega
          rw [List.getElem?_set_ne (Ne.symm h1n), List.getElem?_set_ne (Ne.symm h2n)]
          exact hw.frame_trail_mono L1 L2 h12 h20)
      (hft_bef := fun L hL1 hL i hi => by
        by_cases hLn : L = nlvl
        · subst hLn; dsimp [ftrl'] at hi
          rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; exact Nat.lt_succ_of_le hcl_lt),
            Option.getD_some, bv32_ofNat_toNat hte32] at hi
          have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
            hlit_v ▸ hnot_v i hi
          simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte, hnv]
          have := hw.lvl_le i hi; dsimp [nlvl]; omega
        · dsimp [ftrl'] at hi; rw [List.getElem?_set_ne (Ne.symm hLn)] at hi
          have hL0 : L ≤ s.core.cur_level := by dsimp [nlvl] at hL; omega
          have hi_te : i < s.core.trail_end :=
            Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hL0)
          have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
            hlit_v ▸ hnot_v i hi_te
          simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte, hnv]
          exact hw.frame_trail_before_lt L hL1 hL0 i hi)
      (hfd_lt := fun L hL1 hL => by
        by_cases hLn : L = nlvl
        · subst hLn; dsimp [fdec']
          rw [List.getElem?_set_self (by rw [hcl.frame_dec_len]; exact Nat.lt_succ_of_le hcl_lt),
            Option.getD_some]
          exact hlit_lt
        · dsimp [fdec']; rw [List.getElem?_set_ne (Ne.symm hLn)]
          exact hw.frame_dec_lt L hL1 (by dsimp [nlvl] at hL; omega))
      (hlvl_old_le := fun i hi => by
        have := hw.lvl_le i hi; dsimp [nlvl]; omega)
      (hinhab := fun L hL1 hL => by
        by_cases hLn : L = nlvl
        · exact Or.inl hLn
        · exact Or.inr (hw.levels_inhabited L hL1 (by dsimp [nlvl] at hL; omega)))
      (hdec_fresh := fun _ _ i hi => by
        have := hw.lvl_le i hi; dsimp [nlvl]; omega)
      (hl0 := fun h0 => by dsimp [nlvl] at h0; omega)
      (hrsn := fun _ hne => absurd rfl hne)
    simpa [s', hlit_v, ite_eq_right (by dsimp [nlvl]; omega : nlvl ≠ 0)] using hc0
  exact ⟨⟨hcore', hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2⟩,
    hcore'.lengths, hte_lt, hcl_lt, hval_lit⟩

/-! ## Pure Helpers and `full_lucky_polar_wp` -/

theorem bv64_shl1_eq (x : BitVec 64) : x <<< 1#64 = x * 2#64 := by
  change x <<< (1#64).toNat = x * 2#64
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq, Nat.mul_comm]

theorem bv64_shl1_or1_eq (x : BitVec 64) : x <<< 1#64 ||| 1#64 = x * 2#64 + 1#64 := by
  rw [bv64_shl1_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_add]
  obtain ⟨k, hk⟩ : ∃ k, (x * 2#64).toNat = 2 * k :=
    ⟨(x * 2#64).toNat / 2, by rw [BitVec.toNat_mul]; simp; omega⟩
  rw [hk]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have hlor : (2 * k) ||| 1 = 2 * k + 1 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_or]
    cases i with
    | zero => simp
    | succ i =>
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simp [Nat.testBit_succ, hdiv]
  rw [hlor]
  have hk_lt : 2 * k + 1 < 2 ^ 64 := by
    have : (x * 2#64).toNat < 2 ^ 64 := (x * 2#64).isLt; omega
  exact (Nat.mod_eq_of_lt hk_lt).symm

theorem arena_lit_mem_clauseLits (k : FullCoreState) (r j : Nat)
    (hj : j < fullArenaClauseSizeCore k r)
    (hrj : r + 3 + j < k.arena.length) :
    k.arena[r + 3 + j].toNat ∈ fullArenaClauseLitsCore k r := by
  unfold fullArenaClauseLitsCore
  rw [List.mem_map]
  refine ⟨k.arena[r + 3 + j], ?_, rfl⟩
  have h1 : k.arena[r + 3 + j] = (k.arena.drop (r + 3))[j]'(by simp; omega) := by
    simp [Nat.add_assoc]
  rw [h1]
  have h2 : j < ((k.arena.drop (r + 3)).take (fullArenaClauseSizeCore k r)).length := by
    simp; omega
  have hmem : (k.arena.drop (r + 3))[j]'(by simp; omega) =
      ((k.arena.drop (r + 3)).take (fullArenaClauseSizeCore k r))[j]'h2 := by
    simp
  rw [hmem]
  exact List.getElem_mem h2

private theorem fullArenaScanRefs_succ (ar : List (BitVec 32)) (alen pos f : Nat) :
    fullArenaScanRefs ar alen pos (f + 1) =
      if pos + 3 ≤ alen then pos :: fullArenaScanRefs ar alen (fullArenaNextOff ar alen pos) f
      else [] := by
  cases f <;> simp [fullArenaScanRefs]

theorem fullArenaScanRefs_next_mem (ar : List (BitVec 32)) (alen : Nat) :
    ∀ (fuel pos r : Nat), alen - pos ≤ fuel →
      (∀ p ∈ fullArenaScanRefs ar alen pos fuel,
        p + 3 ≤ fullArenaNextOff ar alen p ∧
        (fullArenaNextOff ar alen p = alen ∨ fullArenaNextOff ar alen p + 3 ≤ alen)) →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r = alen ∨
        fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, _, hr => by simp [fullArenaScanRefs] at hr
  | f + 1, pos, r, hfuel, hwf, hr => by
    rw [fullArenaScanRefs_succ] at hr ⊢
    by_cases hpos : pos + 3 ≤ alen
    · simp only [hpos, ↓reduceIte, List.mem_cons] at hr ⊢
      have hpos_wf := hwf pos (by rw [fullArenaScanRefs_succ]; simp [hpos])
      let nxt := fullArenaNextOff ar alen pos
      rcases hr with rfl | hr_tail
      · rcases hpos_wf.2 with heq | h3
        · exact Or.inl heq
        · right; right
          obtain ⟨f', hf'⟩ : ∃ f', f = f' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
          subst hf'
          rw [fullArenaScanRefs_succ]
          simp [h3]
      · have hwf_tail : ∀ p ∈ fullArenaScanRefs ar alen nxt f,
            p + 3 ≤ fullArenaNextOff ar alen p ∧
            (fullArenaNextOff ar alen p = alen ∨ fullArenaNextOff ar alen p + 3 ≤ alen) :=
          fun p hp => hwf p (by rw [fullArenaScanRefs_succ]; simp [hpos, nxt, hp])
        rcases fullArenaScanRefs_next_mem ar alen f nxt r (by omega) hwf_tail hr_tail with
          heq | hm
        · exact Or.inl heq
        · exact Or.inr (Or.inr hm)
    · simp [hpos] at hr

/-- Unified watch-slice invariant for `full_lucky_polar` across sparse and dense modes. -/
inductive PolarWatchOk (k : FullCoreState) : Nat → Nat → Prop where
  | empty (p : Nat) : PolarWatchOk k p 0
  | bin {p rem : Nat} {w0 : BitVec 32} :
      k.wstk[p]? = some w0 →
      w0 &&& 2147483648#32 ≠ 0#32 →
      w0 ≠ 4294967295#32 →
      (w0 &&& 2147483647#32).toNat < 2 * k.cur_vars →
      PolarWatchOk k (p + 1) rem →
      PolarWatchOk k p (rem + 1)
  | large {p rem : Nat} {w0 : BitVec 32} :
      k.wstk[p]? = some w0 →
      w0 &&& 2147483648#32 = 0#32 →
      PolarWatchOk k (p + 2) rem →
      PolarWatchOk k p (rem + 2)

theorem watchSliceOk_toPolar {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceOk F_cur k lit p rem) : PolarWatchOk k p rem := by
  induction h with
  | empty => exact PolarWatchOk.empty _
  | bin hw hb hn hlt _ _ ih => exact PolarWatchOk.bin hw hb hn hlt ih
  | large hw _ hb _ _ _ ih => exact PolarWatchOk.large hw hb ih

theorem denseWatchSliceOk_toPolar {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : DenseWatchSliceOk F_cur k lit p rem) : PolarWatchOk k p rem := by
  induction h with
  | empty => exact PolarWatchOk.empty _
  | bin hw hb hn hlt _ _ ih => exact PolarWatchOk.bin hw hb hn hlt ih
  | occ hw _ hb _ _ _ _ ih => exact PolarWatchOk.large hw hb ih

theorem modeWatchesInv_toPolar {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) :
    WatchStackLayout k ∧ ∀ l < 2 * k.cur_vars,
      PolarWatchOk k (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  unfold ModeWatchesInv at h
  by_cases hdm : k.dense_mode = 0#64
  · simp [hdm] at h; exact ⟨h.layout, fun l hl => watchSliceOk_toPolar (h.slices l hl)⟩
  · simp [hdm] at h; exact ⟨h.layout, fun l hl => denseWatchSliceOk_toPolar (h.slices l hl)⟩

theorem bv64_shl_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem bv64_shl_nat_or1 (x : BitVec 64) :
    (x <<< (1 : Nat) ||| 1#64).toNat = (2 * x.toNat) % 2 ^ 64 + 1 := by
  have h : (x <<< (1 : Nat) ||| 1#64) = (x <<< 1#64 ||| 1#64) := rfl
  rw [h, bv64_shl1_or1_eq, BitVec.toNat_add, BitVec.toNat_mul]
  simp; omega

end FullLuckyHelpers

open FullLuckyHelpers FullLuckyTactics FullLuckySpecs in
open scoped FullArenaTactics in
/-- Parametric WP proof for `full_lucky_polar_body`. -/
theorem full_lucky_polar_wp (Γ : Env)
    (hNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X) :
    ∀ args m Q X, fullLuckyPolarSpec args m Q X →
      Func.wp Γ full_lucky_polar_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold full_lucky_polar_body
  dsimp only [Func.wp]
  flk_to_group
  rcases hinv with ⟨hlen_all, F_cur, hwe⟩
  have hlen := hlen_all.core_ok
  have hdb : LratBytes.dimacsBound < 2 ^ 30 := by decide
  have hcv_lt : s.core.cur_vars < 2 ^ 31 := by
    have := hlen.cur_vars_le; have := c.hmaxv; omega
  have hal_lt : s.core.arena_len < 2 ^ 31 := by
    have := hlen.arena_len_le; have := c.harena; omega
  have hwl_lt : s.core.wlen < 2 ^ 31 := by
    have := hlen.wlen_le; have := c.hwcap; omega
  obtain ⟨hlay, hpw⟩ := modeWatchesInv_toPolar hwe.watches
  apply wp_loop_group (ts := [.bool, .bool, i64])
    (fun (r_rem : Nat) xs m' => ∃ (sp sn : Bool) (r : BitVec 64),
      xs = (sp, sn, r, ()) ∧ m' = m ∧ r_rem = s.core.arena_len - r.toNat ∧
      r.toNat ≤ s.core.arena_len ∧
      (r.toNat = s.core.arena_len ∨ r.toNat ∈ fullArenaClauseRefsCore s.core))
  · intro J n xs m' hrec ⟨sp, sn, r, hxs, hm', hn, hr_le, hr⟩
    subst hxs; subst m'
    simp only [Blocks.get]
    flk_to_group
    apply wp_join_group (ts := []) (fun _ m2 => m2 = m)
    · -- Loop 2: iterate over variables `0 .. cur_vars - 1`
      intro _Jexit ⟨⟩ m2 hm2
      subst m2
      flk_to_group
      apply wp_loop_group (ts := [.bool, .bool, i64])
        (fun (v_rem : Nat) xs2 m2 => ∃ (sp2 sn2 : Bool) (v : BitVec 64),
          xs2 = (sp2, sn2, v, ()) ∧ m2 = m ∧ v_rem = s.core.cur_vars - v.toNat ∧
          v.toNat ≤ s.core.cur_vars)
      · intro J2 n2 xs2 m2 hrec2 ⟨sp2, sn2, v, hxs2, hm2, hn2, hv_le⟩
        subst hxs2; subst m2
        simp only [Blocks.get]
        flk_to_group
        apply wp_join_group (ts := []) (fun _ m3 => m3 = m)
        · intro _Jret ⟨⟩ m3 hm3
          subst m3
          flk_to_group
          flk_steps <;> exact hQ _ (by decide)
        · intro Jret hJret
          flk_to_group
          apply wp_join_group (ts := []) (fun _ m3 => m3 = m ∧ v.toNat < s.core.cur_vars)
          · intro _J2b ⟨⟩ m3 ⟨hm3, hv_lt⟩
            subst m3
            flk_to_group
            apply wp_join_group (ts := [.bool, .bool]) (fun _ m4 => m4 = m)
            · intro _J2next ⟨sp', sn', ⟨⟩⟩ m4 hm4
              subst m4
              flk_to_group
              have hv1_lt : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
              exact hrec2 (s.core.cur_vars - (v + 1#64).toNat) (sp', sn', v + 1#64, ()) m
                (by omega) ⟨sp', sn', v + 1#64, rfl, rfl, rfl, by omega⟩
            · intro J2next hJ2next
              have h_vals : (v <<< 1#64).toNat < s.core.vals.length := by
                rw [bv64_shl1_eq]; have := hlen.vals_len; have := hlen.cur_vars_le; bv_omega
              have hw0 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64).toNat <
                  s.core.wvec.length := by
                rw [bv64_shl1_or1_eq, bv64_shl1_eq]
                have := hlen.wvec_len; have := hlen.cur_vars_le; bv_omega
              have hw1 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64 + 1#64).toNat <
                  s.core.wvec.length := by
                rw [bv64_shl1_or1_eq, bv64_shl1_eq]
                have := hlen.wvec_len; have := hlen.cur_vars_le; bv_omega
              have hw2 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64).toNat <
                  s.core.wvec.length := by
                rw [bv64_shl1_eq, bv64_shl1_eq]
                have := hlen.wvec_len; have := hlen.cur_vars_le; bv_omega
              have hw3 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64 + 1#64).toNat <
                  s.core.wvec.length := by
                rw [bv64_shl1_eq, bv64_shl1_eq]
                have := hlen.wvec_len; have := hlen.cur_vars_le; bv_omega
              flk_to_group
              · -- `vals[2*v] == 0#8`: Watch Loop 1 (`2*v + 1`), then Watch Loop 2 (`2*v`)
                let i_w1_0 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64).toNat
                let i_w1_1 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64 + 1#64).toNat
                let off1 := s.core.wvec[i_w1_0]
                let sz1 := s.core.wvec[i_w1_1]
                have hl1_idx : i_w1_0 = 2 * (2 * v.toNat + 1) := by
                  dsimp [i_w1_0]
                  rw [bv64_shl_nat, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                    bv64_shl_nat_or1]
                  bv_omega
                have hl1_idx1 : i_w1_1 = 2 * (2 * v.toNat + 1) + 1 := by
                  dsimp [i_w1_1]
                  rw [bv64_shl_nat, BitVec.toNat_setWidth,
                    BitVec.toNat_setWidth, bv64_shl_nat_or1]
                  bv_omega
                have hoff1_eq : off1.toNat = fullWatchOffCore s.core (2 * v.toNat + 1) := by
                  have hget : s.core.wvec[i_w1_0]? = some off1 := List.getElem?_eq_getElem hw0
                  dsimp [fullWatchOffCore]; rw [← hl1_idx, hget]; rfl
                have hsz1_eq : sz1.toNat = fullWatchSizeCore s.core (2 * v.toNat + 1) := by
                  have hget : s.core.wvec[i_w1_1]? = some sz1 := List.getElem?_eq_getElem hw1
                  dsimp [fullWatchSizeCore]; rw [← hl1_idx1, hget]; rfl
                have hbd1 := hlay.bounds (2 * v.toNat + 1) (by omega)
                have hpw1 := hpw (2 * v.toNat + 1) (by omega)
                apply wp_loop_group (ts := [.bool, i64])
                  (fun (wrem : Nat) xw mw => ∃ (flg : Bool) (jw : BitVec 64),
                    xw = (flg, jw, ()) ∧ mw = m ∧
                    jw.toNat + wrem = off1.toNat + sz1.toNat ∧
                    PolarWatchOk s.core jw.toNat wrem)
                · intro Jw1l nw xw mw hrecw ⟨flg, jw, hxw, hmw, hjw_sum, hpw_cur⟩
                  subst hxw; subst mw
                  simp only [Blocks.get]
                  flk_to_group
                  -- Inner join block: Watch Loop 2 (`l = 2 * v`) after Watch Loop 1 exits
                  apply wp_join_group (ts := []) (fun _ m4 => m4 = m)
                  · intro _Jw1_done ⟨⟩ m4 hm4
                    subst m4
                    flk_to_group
                    let i_w0_0 := (BitVec.setWidth 64
                      (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64).toNat
                    let i_w0_1 := (BitVec.setWidth 64
                      (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64 + 1#64).toNat
                    let off0 := s.core.wvec[i_w0_0]
                    let sz0 := s.core.wvec[i_w0_1]
                    have hl0_idx : i_w0_0 = 2 * (2 * v.toNat) := by
                      dsimp [i_w0_0]
                      rw [bv64_shl_nat, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                        bv64_shl_nat]
                      bv_omega
                    have hl0_idx1 : i_w0_1 = 2 * (2 * v.toNat) + 1 := by
                      dsimp [i_w0_1]
                      rw [bv64_shl_nat, BitVec.toNat_setWidth,
                        BitVec.toNat_setWidth, bv64_shl_nat]
                      bv_omega
                    have hoff0_eq : off0.toNat = fullWatchOffCore s.core (2 * v.toNat) := by
                      have hget : s.core.wvec[i_w0_0]? = some off0 := List.getElem?_eq_getElem hw2
                      dsimp [fullWatchOffCore]; rw [← hl0_idx, hget]; rfl
                    have hsz0_eq : sz0.toNat = fullWatchSizeCore s.core (2 * v.toNat) := by
                      have hget : s.core.wvec[i_w0_1]? = some sz0 := List.getElem?_eq_getElem hw3
                      dsimp [fullWatchSizeCore]; rw [← hl0_idx1, hget]; rfl
                    have hbd0 := hlay.bounds (2 * v.toNat) (by omega)
                    have hpw0 := hpw (2 * v.toNat) (by omega)
                    apply wp_loop_group (ts := [.bool, i64])
                      (fun (wrem2 : Nat) xw2 mw2 => ∃ (flg2 : Bool) (jw2 : BitVec 64),
                        xw2 = (flg2, jw2, ()) ∧ mw2 = m ∧
                        jw2.toNat + wrem2 = off0.toNat + sz0.toNat ∧
                        PolarWatchOk s.core jw2.toNat wrem2)
                    · intro Jw2 nw2 xw2 mw2 hrecw2 ⟨flg2, jw2, hxw2, hmw2, hjw2_sum, hpw2_cur⟩
                      subst hxw2; subst mw2
                      simp only [Blocks.get]
                      rw [wp_let]; simp only [Op.wp]
                      have hsum0_lt : off0.toNat + sz0.toNat < 2 ^ 64 := by omega
                      have hjw2_end : (BitVec.setWidth 64 off0 + BitVec.setWidth 64 sz0).toNat =
                          off0.toNat + sz0.toNat := by bv_omega
                      constructor
                      · intro hc
                        dsimp only [Arg.val] at hc
                        change (jw2.ult (BitVec.setWidth 64 off0 +
                            BitVec.setWidth 64 sz0) = true) at hc
                        rw [BitVec.ult] at hc
                        simp only [decide_eq_true_eq] at hc
                        have hjw2_lt : jw2.toNat < off0.toNat + sz0.toNat := by
                          rw [← hjw2_end]; exact hc
                        have hjw2_stk : jw2.toNat < s.core.wstk.length := by
                          have := hlen.wlen_le; rw [hlen.wstk_len_arr]; omega
                        cases flg2
                        · constructor
                          · intro hc2; dsimp only [Arg.val] at hc2; cases hc2
                          · intro _
                            flk_to_group
                            apply wp_join_group (ts := [.bool, i64]) Jw2
                            · intro _Js xs m' hJs; flk_to_group; exact hJs
                            · intro Js hJs
                              cases hpw2_cur with
                              | empty => omega
                              | bin hw_some hbit _ h_ot_lt hpw2_next =>
                                have hld_eq := Option.some.inj
                                  ((List.getElem?_eq_getElem hjw2_stk).symm.trans hw_some)
                                have hbit' := hld_eq.symm ▸ hbit
                                have h_ot_vals : (BitVec.setWidth 64
                                    (s.core.wstk[jw2.toNat] &&& 2147483647#32)).toNat <
                                    s.core.vals.length := by
                                  rw [hld_eq, BitVec.toNat_setWidth,
                                    Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
                                  have := hlen.vals_len; have := hlen.cur_vars_le; omega
                                simp only [wp_let, Op.wp, OpCode.wp, lift2, vals, Arg.val, liftCmp,
                                  CmpOp.evalBits, Ty.hasFloat]
                                rw [wp_jnz]
                                refine ⟨fun _ => ?_, fun hc => by simp [hbit'] at hc⟩
                                apply wp_join_group (ts := [.bool]) (fun _ m' => m' = m)
                                · intro _Js1 ⟨flg', ⟨⟩⟩ m' hm'; subst m'; flk_to_group
                                  have h1 : (jw2 + 1#64).toNat = jw2.toNat + 1 := by bv_omega
                                  exact hJs _ m (hrecw2
                                    (off0.toNat + sz0.toNat - (jw2 + 1#64).toNat) _ m
                                    (by omega) ⟨flg', jw2 + 1#64, rfl, rfl, by omega, by
                                      rw [h1]
                                      exact (congrArg (PolarWatchOk s.core _)
                                        (by omega)).mpr hpw2_next⟩)
                                · intro Js1 hJs1; flk_to_group <;> exact hJs1 _ m rfl
                              | large hw_some hbit hpw2_next =>
                                have hld_eq := Option.some.inj
                                  ((List.getElem?_eq_getElem hjw2_stk).symm.trans hw_some)
                                have hbit' := hld_eq.symm ▸ hbit
                                simp only [wp_let, Op.wp, OpCode.wp, lift2, vals, Arg.val, liftCmp,
                                  CmpOp.evalBits, Ty.hasFloat]
                                rw [wp_jnz]
                                refine ⟨fun hc => by simp [hbit'] at hc, fun _ => ?_⟩
                                flk_to_group
                                have h2 : (jw2 + 2#64).toNat = jw2.toNat + 2 := by bv_omega
                                exact hJs _ m (hrecw2
                                  (off0.toNat + sz0.toNat - (jw2 + 2#64).toNat)
                                  (false, jw2 + 2#64, ()) m (by omega)
                                  ⟨false, jw2 + 2#64, rfl, rfl, by omega, by
                                    rw [h2]
                                    exact (congrArg (PolarWatchOk s.core _)
                                      (by omega)).mpr hpw2_next⟩)
                        · constructor
                          · intro _; flk_to_group; exact hJ2next (flg, true, ()) m rfl
                          · intro hc2; dsimp only [Arg.val] at hc2; cases hc2
                      · intro _; flk_to_group; exact hJ2next (flg, flg2, ()) m rfl
                    · intro Jw2 hJw2
                      flk_to_group
                      have hoff0_64 : (BitVec.setWidth 64 off0).toNat = off0.toNat := by bv_omega
                      exact hJw2 sz0.toNat (sn2, BitVec.setWidth 64 off0, ()) m
                        ⟨sn2, BitVec.setWidth 64 off0, rfl, rfl, by rw [hoff0_64],
                          by simpa [hoff0_64, hoff0_eq, hsz0_eq] using hpw0⟩
                  · -- Watch Loop 1 condition + step
                    intro Jw1_done hJw1_done
                    (try flk_strip); c0_step
                    have hsum1_lt : off1.toNat + sz1.toNat < 2 ^ 64 := by omega
                    have hjw_end : (BitVec.setWidth 64 off1 + BitVec.setWidth 64 sz1).toNat =
                        off1.toNat + sz1.toNat := by bv_omega
                    constructor
                    · intro hc
                      dsimp only [Arg.val] at hc
                      change (jw.ult (BitVec.setWidth 64 off1 +
                          BitVec.setWidth 64 sz1) = true) at hc
                      rw [BitVec.ult, decide_eq_true_eq] at hc
                      have hjw_lt : jw.toNat < off1.toNat + sz1.toNat := hjw_end ▸ hc
                      have hjw_stk : jw.toNat < s.core.wstk.length := by
                        have := hlen.wlen_le; rw [hlen.wstk_len_arr]; omega
                      cases flg
                      · rw [wp_jnz]
                        refine ⟨fun hc => by simp [Arg.val] at hc, fun _ => ?_⟩
                        flk_to_group
                        apply wp_join_group (ts := [.bool, i64]) Jw1l
                        · intro _Js xs m' hJs; flk_to_group; exact hJs
                        · intro Js hJs
                          cases hpw_cur with
                          | empty => omega
                          | bin hw_some hbit _ h_ot_lt hpw_next =>
                            have hld_eq := Option.some.inj
                              ((List.getElem?_eq_getElem hjw_stk).symm.trans hw_some)
                            have hbit' := hld_eq.symm ▸ hbit
                            have h_ot_vals : (BitVec.setWidth 64
                                (s.core.wstk[jw.toNat] &&& 2147483647#32)).toNat <
                                s.core.vals.length := by
                              rw [hld_eq, BitVec.toNat_setWidth,
                                Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
                              have := hlen.vals_len; have := hlen.cur_vars_le; omega
                            simp only [wp_let, Op.wp, OpCode.wp, lift2, vals, Arg.val, liftCmp,
                              CmpOp.evalBits, Ty.hasFloat]
                            rw [wp_jnz]
                            refine ⟨fun _ => ?_, fun hc => by simp [hbit'] at hc⟩
                            apply wp_join_group (ts := [.bool]) (fun _ m' => m' = m)
                            · intro _Js1 ⟨flg', ⟨⟩⟩ m' hm'; subst m'; flk_to_group
                              have h1 : (jw + 1#64).toNat = jw.toNat + 1 := by bv_omega
                              exact hJs _ m (hrecw (off1.toNat + sz1.toNat - (jw + 1#64).toNat)
                                _ m (by omega) ⟨flg', jw + 1#64, rfl, rfl, by omega, by
                                  rw [h1]
                                  exact (congrArg (PolarWatchOk s.core _)
                                    (by omega)).mpr hpw_next⟩)
                            · intro Js1 hJs1
                              flk_to_group <;> exact hJs1 _ m rfl
                          | large hw_some hbit hpw_next =>
                            have hld_eq := Option.some.inj
                              ((List.getElem?_eq_getElem hjw_stk).symm.trans hw_some)
                            have hbit' := hld_eq.symm ▸ hbit
                            simp only [wp_let, Op.wp, OpCode.wp, lift2, vals, Arg.val, liftCmp,
                              CmpOp.evalBits, Ty.hasFloat]
                            rw [wp_jnz]
                            refine ⟨fun hc => by simp [hbit'] at hc, fun _ => ?_⟩
                            flk_to_group
                            have h2 : (jw + 2#64).toNat = jw.toNat + 2 := by bv_omega
                            exact hJs _ m (hrecw (off1.toNat + sz1.toNat - (jw + 2#64).toNat)
                              (false, jw + 2#64, ()) m (by omega) ⟨false, jw + 2#64, rfl, rfl,
                                by omega, by
                                  rw [h2]
                                  exact (congrArg (PolarWatchOk s.core _)
                                    (by omega)).mpr hpw_next⟩)
                      · rw [wp_jnz]; refine ⟨fun _ => ?_, fun hc => by simp [Arg.val] at hc⟩
                        flk_to_group; exact hJw1_done () m rfl
                    · intro _; flk_to_group; exact hJw1_done () m rfl
                · intro Jw1l hJw1l
                  flk_to_group
                  have hoff1_64 : (BitVec.setWidth 64 off1).toNat = off1.toNat := by bv_omega
                  exact hJw1l sz1.toNat (sp2, BitVec.setWidth 64 off1, ()) m
                    ⟨sp2, BitVec.setWidth 64 off1, rfl, rfl, by rw [hoff1_64],
                      by simpa [hoff1_64, hoff1_eq, hsz1_eq] using hpw1⟩
              · -- `vals[2*v] != 0#8`
                exact hJ2next (sp2, sn2, ()) m rfl
          · -- Loop 2 check
            intro J2b hJ2b
            flk_to_group <;>
              first | exact hJret () m rfl | exact hJ2b () m ⟨rfl, by omega⟩
          exact hJret () m rfl
      · -- Enter Loop 2
        intro J2 hJ2
        flk_to_group
        exact hJ2 s.core.cur_vars (sp, sn, 0#64, ()) m ⟨sp, sn, 0#64, rfl, rfl, rfl, Nat.zero_le _⟩
    · -- Loop 1 check: `r < arena_len` and `!(sp && sn)`
      intro Jexit hJexit
      flk_to_group
      rcases hr with hr_eq | hr_mem
      · have hlt : ¬ (r.toNat < s.core.arena_len % 2 ^ 64) := by
          rw [hr_eq, Nat.mod_eq_of_lt (by omega)]; omega
        cases sp <;> cases sn <;> simp_all <;> exact hJexit () m rfl
      · have hwf := hwe.arena.refs_wf r.toNat hr_mem
        have hr_lt_cap0 : r.toNat < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        have hr_lt_cap2 : (r + 2#64).toNat < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; bv_omega
        flk_to_group
        apply wp_join_group (ts := []) (fun _ m2 => m2 = m)
        · -- Loop 1 clause check
          intro _Jbody ⟨⟩ m2 hm2
          subst m2
          flk_to_group
          apply wp_join_group (ts := [.bool, .bool]) (fun _ m3 => m3 = m)
          · -- Next clause via `full_arena_next`
            intro _Jn ⟨sp', sn', ⟨⟩⟩ m3 hm3
            subst m3
            flk_to_group
            let nxt := fullArenaNextOff s.core.arena s.core.arena_len r.toNat
            have hr32 : (BitVec.setWidth 32 r).toNat = r.toNat := by bv_omega
            refine ⟨fun res m4 => res = (BitVec.ofNat 32 nxt, ()) ∧ m4 = m, X,
              hNext (c.hdr, BitVec.setWidth 32 r, ()) m _ X ⟨c, s, R, rfl, hlen_all, hm, ⟨?_, rfl⟩⟩,
              ?_, fun _ _ _ _ => id⟩
            · rw [hr32]
            · rintro ⟨r32, ⟨⟩⟩ m4 ⟨hr32_eq, hm4⟩
              subst m4
              injection hr32_eq with hr32_eq
              subst r32
              flk_to_group
              have hnxt_eq : (BitVec.setWidth 64 (BitVec.ofNat 32 nxt)).toNat = nxt := by
                have := hwf.2.2.2.1; bv_omega
              have hnxt_mem : nxt = s.core.arena_len ∨ nxt ∈ fullArenaClauseRefsCore s.core := by
                apply fullArenaScanRefs_next_mem s.core.arena s.core.arena_len s.core.arena_len 0
                  r.toNat (Nat.le_refl _)
                · intro p hp
                  have hpwf := hwe.arena.refs_wf p hp
                  exact ⟨Nat.le_trans (by omega) hpwf.2.2.1, hpwf.2.2.2.2⟩
                · exact hr_mem
              exact hrec (s.core.arena_len - nxt)
                (sp', sn', BitVec.setWidth 64 (BitVec.ofNat 32 nxt), ()) m
                (by have := hwf.2.2.1; have := hwf.1; omega)
                ⟨sp', sn', BitVec.setWidth 64 (BitVec.ofNat 32 nxt), rfl, rfl, by rw [hnxt_eq],
                  by rw [hnxt_eq]; exact hwf.2.2.2.1, by rw [hnxt_eq]; exact hnxt_mem⟩
          · -- Guard + clause literal scan
            intro Jn hJn
            flk_to_group
            · -- Inside `!garb`, `!red`, `3 ≤ sz`: literal loop
              have hsz_eq : (s.core.arena[(r + 2#64).toNat]).toNat =
                  fullArenaClauseSizeCore s.core r.toNat := by
                have hr2_eq : (r + 2#64).toNat = r.toNat + 2 := by bv_omega
                have ha : s.core.arena[r.toNat + 2]? =
                    some s.core.arena[(r + 2#64).toNat] := by
                  rw [← hr2_eq]; exact List.getElem?_eq_getElem hr_lt_cap2
                dsimp only [fullArenaClauseSizeCore]; rw [ha]; rfl
              have hgarb_false : fullArenaClauseGarbCore s.core r.toNat = false := by
                have ha : s.core.arena[r.toNat]? = some s.core.arena[r.toNat] :=
                  List.getElem?_eq_getElem hr_lt_cap0
                dsimp [fullArenaClauseGarbCore, fullArenaHdrCore]
                rw [ha]; simp; assumption
              apply wp_loop_group (ts := [.bool, .bool, i32])
                (fun (jrem : Nat) xj mj => ∃ (sat? any? : Bool) (j : BitVec 32),
                  xj = (sat?, any?, j, ()) ∧ mj = m ∧
                  jrem = fullArenaClauseSizeCore s.core r.toNat - j.toNat ∧
                  j.toNat ≤ fullArenaClauseSizeCore s.core r.toNat)
              · intro Jj nj xj mj hrecj ⟨sat?, any?, j, hxj, hmj, hnj, hj_le⟩
                subst hxj; subst mj
                simp only [Blocks.get]
                rw [wp_let]; simp only [Op.wp]
                constructor
                · intro hc
                  have hlt :
                      decide (j.toNat < s.core.arena[(r + 2#64).toNat].toNat) = true := hc
                  have hj : j.toNat < fullArenaClauseSizeCore s.core r.toNat := by
                    rw [← hsz_eq]; exact of_decide_eq_true hlt
                  have hj_ar : (r + 3#64 + BitVec.setWidth 64 j).toNat < s.core.arena.length := by
                    have := hlen.arena_len_le; have := hlen.arena_len_arr
                    have := hwf.2.2.1; bv_omega
                  flk_to_group
                  apply wp_join_group (ts := [.bool, .bool]) (fun _ m4 => m4 = m)
                  · intro _Jjnext ⟨sat', any', ⟨⟩⟩ m4 hm4
                    subst m4
                    flk_to_group
                    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                    exact hrecj (fullArenaClauseSizeCore s.core r.toNat - (j + 1#32).toNat)
                      (sat', any', j + 1#32, ()) m (by omega)
                      ⟨sat', any', j + 1#32, rfl, rfl, rfl, by omega⟩
                  · intro Jjnext hJjnext
                    have h_ar_idx : (r + 3#64 + BitVec.setWidth 64 j).toNat =
                        r.toNat + 3 + j.toNat := by bv_omega
                    have hlit_mem : s.core.arena[(r + 3#64 + BitVec.setWidth 64 j).toNat].toNat ∈
                        fullArenaClauseLitsCore s.core r.toNat := by
                      simp only [h_ar_idx]
                      exact arena_lit_mem_clauseLits s.core r.toNat j.toNat hj (h_ar_idx ▸ hj_ar)
                    have hlit_lt : (BitVec.setWidth 64
                        s.core.arena[(r + 3#64 + BitVec.setWidth 64 j).toNat]).toNat <
                        s.core.vals.length := by
                      have := hwe.arena.lits_lt r.toNat hr_mem hgarb_false _ hlit_mem
                      have := hlen.vals_len; have := hlen.cur_vars_le; bv_omega
                    flk_to_group
                    · apply wp_join_group (ts := [.bool, .bool]) (fun _ m' => m' = m)
                      · intro _Js ⟨sat', any', ⟨⟩⟩ m' hm'; subst m'
                        flk_to_group; exact hJjnext (sat', any', ()) m rfl
                      · intro Js hJs
                        flk_to_group <;> exact hJs _ m rfl
                    · exact hJjnext _ m rfl
                · intro _
                  apply wp_join_group (ts := [.bool]) (fun _ m5 => m5 = m)
                  · intro _Js ⟨sp', ⟨⟩⟩ m5 hm5; subst m5
                    apply wp_join_group (ts := [.bool]) (fun _ m6 => m6 = m)
                    · intro _Js2 ⟨sn', ⟨⟩⟩ m6 hm6; subst m6
                      flk_to_group; exact hJn (sp', sn', ()) m rfl
                    · intro Js2 hJs2; flk_to_group <;> exact hJs2 _ m rfl
                  · intro Js1 hJs1; flk_to_group <;> exact hJs1 _ m rfl
              · intro Jj hJj
                flk_to_group
                exact hJj (fullArenaClauseSizeCore s.core r.toNat) (false, false, 0#32, ()) m
                  ⟨false, false, 0#32, rfl, rfl, rfl, Nat.zero_le _⟩
            all_goals exact hJn (sp, sn, ()) m rfl
        · -- `if (sp && sn)` branch
          intro Jbody hJbody
          flk_to_group <;>
            first
            | exact hJbody () m rfl
            | exact hJexit () m rfl
            | (exfalso; have := hwf.1; omega)
      exact hJexit () m rfl
  · -- Enter Loop 1
    intro J hJ
    flk_to_group
    have h0 : 0 = s.core.arena_len ∨ 0 ∈ fullArenaClauseRefsCore s.core := by
      rcases hwe.arena.len_ok with h0 | h3
      · exact Or.inl h0.symm
      · right; unfold fullArenaClauseRefsCore
        cases al : s.core.arena_len with
        | zero => omega
        | succ _ => rw [fullArenaScanRefs_succ]; simp [← al, h3]
    exact hJ s.core.arena_len (false, false, 0#64, ()) m
      ⟨false, false, 0#64, rfl, rfl, rfl, Nat.zero_le _, h0⟩

end LeanQbe.T.Examples.Kissat.Full