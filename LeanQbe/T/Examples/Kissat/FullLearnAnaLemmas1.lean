module

public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.Full2
public import LeanQbe.T.Examples.Kissat.SolverIngestLemmas1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Learn/Analyze Top Helpers & Specs (`Stage 4`, Part 1)

Defines strictly scoped `FullLearnAnaTactics`, local `FullLearnAnaSpecs` matching
`FullSpec1.lean` / `FullSpec2.lean` 1:1 (including `#1017` `cur_vars`, `FullOtfsInvW`,
`FullOtfsWitnessInv.toWitness_of_level0`, `FullLastLearnedWf`, and the `FullLearnAna`
callee alignment clauses), and pure invariant / witness preservation lemmas for
`full_eager_subsume`, `full_learn_clause`, and `full_analyze`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

/-! ## 1. Strictly scoped `FullLearnAnaTactics` -/

namespace FullLearnAnaTactics

attribute [scoped bv_c0] List.length_set

@[scoped bv_c0] theorem bv32_setWidth64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

@[scoped bv_c0] theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl
@[scoped bv_c0] theorem bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl
@[scoped bv_c0] theorem bv64_seven_toNat : (7 : BitVec 64).toNat = 7 := rfl
@[scoped bv_c0] theorem bv64_eight_toNat : (8 : BitVec 64).toNat = 8 := rfl

section ArenaLoadStore
open scoped FullArenaTactics

@[scoped c0_load] theorem load_full_tmp0_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 0#64) = some s.core.tmp[0] := by
  simpa using FullArenaTactics.load_full_tmp (i := 0) hi hm

@[scoped c0_load] theorem load_full_tmp0_base {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using FullArenaTactics.load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem store_full_tmp0_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 0) v hi hm

@[scoped c0_store] theorem store_full_tmp0_base {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 0) v hi hm

@[scoped c0_load] theorem load_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 4#64) = some s.core.tmp[1] := by
  simpa using FullArenaTactics.load_full_tmp (i := 1) hi hm

@[scoped c0_store] theorem store_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 1) v hi hm

@[scoped c0_load] theorem load_full_ll0_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.last_learned.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pLastLearned + 0#64) = some s.scratch.last_learned[0] := by
  simpa using FullArenaTactics.load_full_last_learned (i := 0) hi hm

@[scoped c0_load] theorem load_full_ll0_base {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.last_learned.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pLastLearned = some s.scratch.last_learned[0] := by
  simpa using FullArenaTactics.load_full_last_learned (i := 0) hi hm

@[scoped c0_store] theorem store_full_ll0_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.last_learned.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pLastLearned + 0#64) ∧
      (FullMem c { s with scratch :=
        { s.scratch with last_learned := s.scratch.last_learned.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pLastLearned + 0#64) v) := by
  simpa using FullArenaTactics.store_full_last_learned (i := 0) v hi hm

@[scoped c0_store] theorem store_full_ll0_base {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.last_learned.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pLastLearned ∧
      (FullMem c { s with scratch :=
        { s.scratch with last_learned := s.scratch.last_learned.set 0 v } } ⋆ R)
        (storeMem m i32 c.pLastLearned v) := by
  simpa using FullArenaTactics.store_full_last_learned (i := 0) v hi hm

end ArenaLoadStore

open Lean Elab Tactic in
/-- Strip outer `Expr.mdata` wrappers from all unsolved goals so `c0_step` inspects heads. -/
scoped elab "c0_clean" : tactic => do
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    let ty ← Lean.instantiateMVars (← g.getType)
    if ty.isMData then
      out := out.push (← g.change ty.consumeMData (checkDefEq := false))
    else out := out.push g
  setGoals out.toList

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
scoped elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split it once. -/
scoped elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

theorem i8_sext32_eq0 (v : BitVec 8) : v.signExtend 32 = 0#32 ↔ v = 0#8 := by
  revert v; decide

theorem i8_sext32_slt0_eq1 {v : BitVec 8}
    (hv : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (h : BitVec.slt 0#32 (v.signExtend 32)) :
    v = 1#8 := by
  rcases hv with rfl | rfl | rfl <;> simp_all <;> revert h <;> decide

theorem i8_eq1_slt0_sext32 : BitVec.slt 0#32 ((1#8 : BitVec 8).signExtend 32) := by
  decide

private theorem mask31_bit : ∀ i : Fin 32, (0x80000000#32)[i.val] = decide (i.val = 31) := by
  decide
private theorem maskLo31_bit : ∀ i : Fin 32, (0x7FFFFFFF#32)[i.val] = decide (i.val < 31) := by
  decide

theorem bin_rsn_mask_props {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    let rsn : BitVec 32 := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) ≠ 0#32 ∧
      (rsn &&& 0x7FFFFFFF#32).toNat = l.toNat := by
  intro rsn
  have hbit31 : l[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (by omega : l.toNat < 2 ^ 31)]; rfl
  have hand_hi : (rsn &&& 0x80000000#32) = 0x80000000#32 := by
    ext i hi
    simp only [rsn, BitVec.getElem_and, BitVec.getElem_or, mask31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31 <;> simp [h31]
  have hand_lo : (rsn &&& 0x7FFFFFFF#32) = l := by
    ext i hi
    simp only [rsn, BitVec.getElem_and, BitVec.getElem_or,
      mask31_bit ⟨i, hi⟩, maskLo31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hbit31]
    · simp [h31, show i < 31 by omega]
  refine ⟨?_, ?_, congrArg BitVec.toNat hand_lo⟩
  · intro heq
    have := congrArg (fun x => x &&& 0x7FFFFFFF#32) heq
    rw [hand_lo] at this
    have hnat := congrArg BitVec.toNat this
    have hff : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := rfl
    rw [hff] at hnat; omega
  · rw [hand_hi]; decide

end FullLearnAnaTactics

/-! ## 2. Local `FullLearnAnaSpecs` matching canonical `FullSpec1.lean` & `FullSpec2.lean` 1:1 -/

namespace FullLearnAnaSpecs

def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

def FullSparseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) :
    Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

def FullConflictOkW (F_cur : List (List Nat)) (s : FullState) : Prop :=
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

def FullOtfsInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

theorem FullWitnessInv.toOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) : FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
   h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
   h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
   h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
   fun idx hi _ hne => h.reason_inv idx hi hne,
   fun idx hi _ hne hlg => h.reason_lit_mem idx hi hne hlg⟩

theorem FullSparseInvW.toOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, FullWitnessInv.toOtfs h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullOtfsWitnessInv.toWitness_of_level0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) : FullWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
   h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
   h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
   h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
   fun idx hi hne => absurd (h.level0_rsn_none idx hi (by have := h.lvl_le idx hi; omega)) hne,
   fun idx hi hne _ => absurd (h.level0_rsn_none idx hi (by have := h.lvl_le idx hi; omega)) hne⟩

structure FullWitnessCutInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut : Nat) (k : FullCoreState) : Prop extends FullOtfsWitnessInv c F0 F_cur k where
  cut_le : cut ≤ k.trail_end
  reason_inv_cut : ∀ idx < cut,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
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
  reason_lit_mem_cut : ∀ idx < cut,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
    p ∈ fullArenaClauseLitsCore k rsn.toNat

def FullCutInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

def FullConflictOkCut (F_cur : List (List Nat)) (cut : Nat) (s : FullState) : Prop :=
  FullConflictOkW F_cur s ∧
  (if s.core.confl_type = 1#64 then
    ((s.core.lvl[s.core.confl_lit0.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = s.core.confl_lit0.toNat ^^^ 1) ∧
    ((s.core.lvl[s.core.confl_lit1.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = s.core.confl_lit1.toNat ^^^ 1)
   else
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
      (s.core.lvl[l / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)

theorem FullWitnessInv.toCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) :
    FullWitnessCutInv c F0 F_cur k.trail_end k :=
  ⟨FullWitnessInv.toOtfs h, Nat.le_refl _, h.reason_inv, h.reason_lit_mem⟩

theorem FullSparseInvW.toCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) :
    FullCutInvW c F0 F_cur s.core.trail_end s :=
  ⟨h.1, FullWitnessInv.toCut h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullCutInvW.toOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s) : FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, h.2.1.toFullOtfsWitnessInv, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullConflictOkW.toCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hc : FullConflictOkW F_cur s) :
    FullConflictOkCut F_cur s.core.trail_end s := by
  refine ⟨hc, ?_⟩
  split
  · rename_i h1
    rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, _⟩ | ⟨hne, _⟩
    · exact ⟨fun _ => (hw.vals_false_iff _ h0lt).mp hf0,
        fun _ => (hw.vals_false_iff _ h1lt).mp hf1⟩
    · exact absurd (h1.symm.trans hne) (by decide)
  · rename_i hne
    rcases hc with ⟨h1, _⟩ | ⟨_, href, hng, hfals⟩
    · exact absurd h1 hne
    · exact fun l hl _ => (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)

theorem FullOtfsInvW.toSparse_of_level0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0) :
    FullSparseInvW c F0 F_cur s :=
  ⟨h.1, h.2.1.toWitness_of_level0 hl0, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

def fullWstackDefragSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → WatchStackLayout s'.core → (1 ≤ s.core.wlen → 1 ≤ wlen') →
      (∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullTickRelSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

def fullEmaUpdateSpec : Spec [i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _glue, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] :=
  fun (h, lit, rsn, alvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
          s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
        Q () m
      else
        let v := lit.toNat / 2
        let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
        let unfl' := if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed
        ∀ flags' unass' phases' m',
          flags'.length = c.max_vars → phases'.length = c.max_vars →
          let s' : FullState :=
            { s with
              core :=
                { s.core with
                  vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                  flags := flags', lvl := s.core.lvl.set v alvl, rsns := s.core.rsns.set v rsn'
                  trl := s.core.trl.set s.core.trail_end lit
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
      (∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss', sc' = { s.scratch with
        target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
        heap := hp', pos := ps', heap_len := hl',
        q_search_idx := qsi', q_search_stamp := qss' }) →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars, vals'[l]?.getD 0#8 =
          if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
            s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ i < s.core.trail_end, let v := (s.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]?.getD 0#32 = if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat then
            s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullAddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
      len.toNat ≤ c.max_vars ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      if len.toNat < 2 then
        Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                    wusable := wusable', num_binary := nb' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                    wstk := wstk', wlen := wlen', wusable := wusable',
                                    first_reducible := fred', num_irred := ni',
                                    num_redundant := nr' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
          (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
          (FullArenaVarsNodup s → FullArenaVarsNodup s') →
          (r = BitVec.ofNat 64 s.core.arena_len →
            alen' = s.core.arena_len + 3 + len.toNat ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullReduceSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → 0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullMinShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) ∧
    (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk',
                                min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }
          scratch := { s.scratch with conflicts := conf', learned_lits := llits',
                                      min_removed := mrem', shrink_stk := sstk' } }
      s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullDetNewLevelSpec : Spec [i64, i64] [i64] := fun (h, jump, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64,
      (s.core.cur_level = 0 → r = 0#64) →
      (0 < s.core.cur_level → jump.toNat < s.core.cur_level →
        jump.toNat ≤ r.toNat ∧ r.toNat < s.core.cur_level) →
      Q (r, ()) m

def fullOneLitConflSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCutInvW c F0 F_cur cut s ∧ FullConflictOkCut F_cur cut s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (r = 2#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 0#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ 0 < s'.core.cur_level ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullDeduce1uipSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧
    FullConflictOkCut F_cur cut s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullEagerSubsumeSpec : Spec [i64, i64] [] := fun (h, new_ref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
    (∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (new_ref.toNat < 0x80000000 → new_ref.toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ arena' ag' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag' }
          scratch := sc' }
      FullSparseInvW c F0 F_cur s' → sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullLearnClauseSpec : Spec [i64, i64] [i64] := fun (h, _glue, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullOtfsInvW c F0 F_cur s ∧ 0 < s.core.cur_level ∧
    1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level ∧
      lv ≤ (s.core.lvl[(s.core.tmp[s.core.tmp_len - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullAnalyzeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ FullConflictOkW F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullLearnAnaSpecs

/-! ## 3. Pure invariant & witness-preservation helpers -/

section PureHelpers

namespace FullLearnAnaHelpers

open FullLearnAnaSpecs

theorem FullLastLearnedWf.of_refs_subset {s s' : FullState}
    (h : FullLastLearnedWf s) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullLastLearnedWf s' := by
  intro i hi; dsimp only; rw [hll]
  exact (h i hi).elim Or.inl fun hr => Or.inr (hsub _ hr)

theorem FullExtScratchOk.of_pres {c : FullCfg} {s s' : FullState}
    (h : FullExtScratchOk c s) (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullExtScratchOk c s' := by
  refine ⟨FullLastLearnedWf.of_refs_subset h.1 hpres.1 hsub, ?_⟩
  rw [hpres.2]; exact h.2

private theorem markGarb_lits_ne {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hlen : s.LengthsOk c)
    {cref r : Nat} (href : cref ∈ fullArenaClauseRefs s) (hr : r ∈ fullArenaClauseRefs s)
    (hne : r ≠ cref) (ag' : BitVec 64) :
    fullArenaClauseLitsCore
      { s.core with
        arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
        arena_garbage := ag' } r = fullArenaClauseLitsCore s.core r := by
  have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hw.arena.disjoint hr href hlt)
    · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  exact (fullArenaClauseLitsCore_set_outside hbd hdisj).2

theorem FullArenaVarsNodup.of_markGarb_w {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hlen : s.LengthsOk c)
    (hnd : FullArenaVarsNodup s) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullArenaVarsNodup s' := by
  intro s' r hr hng
  have hmg := hw.arena.markGarb hlen.core_ok href ag'
  have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rwa [hmg.1] at hr
  have har_len : cref < s.core.arena.length := by
    have := (hw.arena.refs_wf cref href).1; have := hlen.core_ok.arena_len_le
    have := hlen.core_ok.arena_len_arr; omega
  have hne : r ≠ cref := by
    rintro rfl
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore s' at hng
    rw [List.getElem?_set_self har_len, Option.getD_some] at hng
    have hbit : ((fullArenaHdr s r ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
      intro h; have := congrArg (·[19]) h; simp at this
    exact hbit (by simpa using hng)
  have hng0 : fullArenaClauseGarb s r = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
    simpa [s', List.getElem?_set_ne hne.symm] using hng
  unfold fullArenaClauseLits; rw [markGarb_lits_ne hw hlen href hr0 hne ag']; exact hnd r hr0 hng0

theorem FullOtfsWitnessInv.with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k) (tmp' : List (BitVec 32)) :
    FullOtfsWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem FullOtfsInvW.of_safetySlice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullOtfsInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullOtfsInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.2.1
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs; rwa [heq]

theorem FullOtfsInvW.with_conflicts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) (k' : BitVec 64) :
    FullOtfsInvW c F0 F_cur { s with scratch := { s.scratch with conflicts := k' } } :=
  FullOtfsInvW.of_safetySlice h ⟨h.1.core_ok, { h.1.scratch_ok with }⟩ rfl ⟨rfl, rfl⟩

theorem FullConflictOkW.with_scratch {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflictOkW F_cur s) (sc' : FullScratch) :
    FullConflictOkW F_cur { s with scratch := sc' } := h

private theorem watchSliceOk_relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem fullWstackDefrag_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wsort' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hpres : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l =
        fullWatchSizeCore s.core l ∧
      ∀ k < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l + k]? =
          s.core.wstk[fullWatchOffCore s.core l + k]?) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } } := by
  let hw := h.2.1
  let k' : FullCoreState :=
    { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
  have hwat : ModeWatchesInv F_cur k' := by
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ p => p
    have hm := hw.watches
    unfold ModeWatchesInv at hm ⊢
    simp only [show s.core.dense_mode = 0#64 from h.2.2.2.2.2,
      show k'.dense_mode = 0#64 from h.2.2.2.2.2, ↓reduceIte] at hm ⊢
    refine ⟨hlay', fun l hl => ?_⟩
    obtain ⟨hsz, hslice⟩ := hpres l hl; rw [hsz]
    exact watchSliceOk_relocate (k := s.core) (k' := k') hrefl (Nat.le_refl _) (fun _ r => r)
      hslice (hm.slices l hl)
  exact ⟨hlen',
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullBacktrack_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hs : FullOtfsInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hdm' : s'.core.dense_mode = s.core.dense_mode) (hpres : FullExtScratchPres s s') :
    FullSparseInvW c F0 F_cur s' := by
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har', hal']
  refine ⟨hlen', hw', ?_, ?_, FullExtScratchOk.of_pres hs.2.2.2.2.1 hpres fun _ h => hrefs ▸ h,
    hdm' ▸ hs.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hmrk', hlm']; exact hs.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
      fullArenaClauseGarbCore fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
      fullArenaHdrCore
    rw [har', hal']; exact hs.2.2.2.1

theorem markGarb_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hlen : s.LengthsOk c)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64)
    (hnonact : ∀ idx < s.core.trail_end,
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hmg := hw.arena.markGarb hlen.core_ok href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  refine ⟨{ hw with
    arena := hmg.2
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl,
        show s'.core.cur_vars = s.core.cur_vars from rfl, show s'.core.lvl = s.core.lvl from rfl]
      by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
      · have hlg' := Classical.byContradiction fun hn => hbin hn
        rw [ite_eq_right hbin] at hrs ⊢
        have hne_cref := hnonact idx hidx hne hlg'
        have hgarb' : fullArenaClauseGarbCore s'.core (s.core.rsns[
            (s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = false := by
          unfold fullArenaClauseGarbCore fullArenaHdrCore
          rw [show s'.core.arena = s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
              from rfl, List.getElem?_set_ne hne_cref.symm]; exact hrs.2.1
        have hlits_eq := markGarb_lits_ne hw hlen href hrs.1 hne_cref ag'
        exact ⟨hrefs ▸ hrs.1, hgarb', fun q hq => hrs.2.2 q (hlits_eq ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      rw [ite_eq_right (fun h => absurd hlg h)] at hrs
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl]
      exact markGarb_lits_ne hw hlen href hrs.1 (hnonact idx hidx hne hlg) ag' ▸
        hw.reason_lit_mem idx hidx hne hlg }, hrefs⟩

theorem markGarb_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64)
    (hnonact : ∀ idx < s.core.trail_end,
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hlen' : s'.LengthsOk c :=
    ⟨{ h.1.core_ok with arena_len_arr := by simp [s', h.1.core_ok.arena_len_arr] }, h.1.scratch_ok⟩
  obtain ⟨hw', hrefs⟩ := markGarb_preserves_fullWitness h.2.1 h.1 href ag' hnonact
  have hnd' := FullArenaVarsNodup.of_markGarb_w h.2.1 h.1 h.2.2.2.1 href ag'
  refine ⟨⟨hlen', hw', h.2.2.1, hnd',
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr => hrefs ▸ hr, h.2.2.2.2.2⟩,
    hrefs⟩

/-- Set-membership invariant for `last_learned[0..8)` across `full_eager_subsume` updates. -/
def FullLastLearnedIn (refs : List Nat) (ll : List (BitVec 32)) : Prop :=
  ∀ i < 8, let cr := ll[i]?.getD 0xFFFFFFFF#32; cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ refs

theorem fullLastLearnedIn_set_sentinel {refs : List Nat} {ll : List (BitVec 32)}
    (h : FullLastLearnedIn refs ll) (idx : Nat) :
    FullLastLearnedIn refs (ll.set idx 0xFFFFFFFF#32) := by
  intro i hi; dsimp only; by_cases hie : i = idx
  · subst hie; by_cases hlt : i < ll.length
    · rw [List.getElem?_set_self hlt]; exact Or.inl rfl
    · rw [List.getElem?_eq_none (by simp [List.length_set]; omega)]; exact Or.inl rfl
  · rw [List.getElem?_set_ne (Ne.symm hie)]; exact h i hi

theorem fullLastLearnedIn_shift_step {refs : List Nat} {ll : List (BitVec 32)}
    (h : FullLastLearnedIn refs ll) {k : Nat} (hk1 : 1 ≤ k) (hk8 : k < 8)
    (hlen : 8 ≤ ll.length) : FullLastLearnedIn refs (ll.set k (ll[k - 1]'(by omega))) := by
  intro i hi; dsimp only; by_cases hik : i = k
  · subst hik; rw [List.getElem?_set_self (by omega), Option.getD_some]
    simpa [List.getElem?_eq_getElem (by omega : i - 1 < ll.length)] using h (i - 1) (by omega)
  · rw [List.getElem?_set_ne (Ne.symm hik)]; exact h i hi

theorem fullLastLearnedIn_set0 {refs : List Nat} {ll : List (BitVec 32)}
    (h : FullLastLearnedIn refs ll) (v : BitVec 32) (hv : v.toNat ∈ refs) (hlen : 8 ≤ ll.length) :
    FullLastLearnedIn refs (ll.set 0 v) := by
  intro i hi; dsimp only; cases i with
  | zero => rw [List.getElem?_set_self (by omega), Option.getD_some]; exact Or.inr hv
  | succ j => rw [List.getElem?_set_ne (by omega)]; exact h (j + 1) hi

private theorem count_set_add {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length) (v a : α),
      (xs.set i v).count a + (if xs[i] = a then 1 else 0) = xs.count a + (if v = a then 1 else 0)
  | _ :: _, 0, _, v, a => by simp [List.set, List.count_cons, beq_iff_eq]; omega
  | _ :: xs, i + 1, hi, v, a => by
    have ih := count_set_add xs i (by simp at hi; omega) v a
    simp only [List.set, List.count_cons, List.getElem_cons_succ, beq_iff_eq] at ih ⊢; omega

private theorem take_set_of_lt {α : Type} :
    ∀ (xs : List α) (i n : Nat) (v : α), i < n → (xs.set i v).take n = (xs.take n).set i v
  | [], _, _, _, _ => by simp
  | _ :: _, 0, _ + 1, _, _ => by simp [List.take_succ_cons]
  | _ :: xs, i + 1, n + 1, v, hi => by
    simp [List.set, List.take_succ_cons, take_set_of_lt xs i n v (by omega)]

theorem swap_tmp_perm {α : Type} (tmp : List α) {tl max_idx : Nat}
    (hm1 : 1 ≤ max_idx) (hmlt : max_idx < tl) (hle : tl ≤ tmp.length) :
    let w1 := tmp[1]'(by omega); let wm := tmp[max_idx]'(by omega)
    (((tmp.set 1 wm).set max_idx w1).take tl).Perm (tmp.take tl) := by
  classical
  intro w1 wm; let ys := tmp.take tl
  have hyl : ys.length = tl := by simp [ys, Nat.min_eq_left hle]
  have hys_sw : (((tmp.set 1 wm).set max_idx w1).take tl) = (ys.set 1 wm).set max_idx w1 := by
    dsimp only [ys]; rw [take_set_of_lt _ max_idx tl w1 hmlt, take_set_of_lt tmp 1 tl wm (by omega)]
  have hw1 : ys[1]'(by omega) = w1 := by simp [ys, w1]
  have hwm : ys[max_idx]'(by omega) = wm := by simp [ys, wm]
  rw [hys_sw, List.perm_iff_count]; intro a
  change List.count a ((ys.set 1 wm).set max_idx w1) = List.count a ys
  have h1 := count_set_add ys 1 (by omega) wm a
  have h2 := count_set_add (ys.set 1 wm) max_idx (by simp [hyl]; omega) w1 a
  by_cases hm_eq : max_idx = 1
  · subst hm_eq; have hself : (ys.set 1 wm)[1]'(by simp [hyl]; omega) = wm := by simp
    have heqw : wm = w1 := rfl
    rw [hself] at h2; rw [heqw] at h1 h2 ⊢; rw [hw1] at h1; omega
  · have hne : (ys.set 1 wm)[max_idx]'(by simp [hyl]; omega) = ys[max_idx]'(by omega) :=
      List.getElem_set_ne (by omega : 1 ≠ max_idx) (by simp [hyl]; omega)
    rw [hne, hwm] at h2; rw [hw1] at h1; omega

theorem swap_tmp_props_full {tmp : List (BitVec 32)} {tl max_idx : Nat} {uip : BitVec 32}
    (h2 : 2 ≤ tl) (hle : tl ≤ tmp.length) (hm1 : 1 ≤ max_idx) (hmlt : max_idx < tl)
    (h0 : tmp[0]? = some uip) (hnd : ((tmp.take tl).map fun x => x.toNat / 2).Nodup) :
    let w1 := tmp[1]'(by omega); let wm := tmp[max_idx]'(by omega)
    let tmp_sw := (tmp.set 1 wm).set max_idx w1
    (∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat) ∧
    (∀ l ∈ (tmp_sw.take tl).map BitVec.toNat,
      l = uip.toNat ∨ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l) ∧
    ((tmp_sw.take tl).map fun x => x.toNat / 2).Nodup ∧
    tmp_sw[0]? = some uip ∧ tmp_sw[1]? = some wm := by
  intro w1 wm tmp_sw
  have hperm := swap_tmp_perm tmp hm1 hmlt hle
  have hiff : ∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat := by
    intro l; simp only [List.mem_map]
    exact ⟨fun ⟨x, hx, he⟩ => ⟨x, hperm.mem_iff.mp hx, he⟩,
           fun ⟨x, hx, he⟩ => ⟨x, hperm.mem_iff.mpr hx, he⟩⟩
  have hnd_sw : ((tmp_sw.take tl).map fun x => x.toNat / 2).Nodup := (hperm.map _).nodup_iff.mpr hnd
  have hmem_take : ∀ l ∈ (tmp.take tl).map BitVec.toNat,
      l = uip.toNat ∨ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l := by
    intro l hl; rw [List.mem_map] at hl; rcases hl with ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
    have hjlt : j < tl := by rw [List.length_take] at hj; omega
    rw [List.getElem_take] at hget; cases j with
    | zero =>
      rw [← hget]; have h0e := List.getElem?_eq_getElem (by omega : 0 < tmp.length)
      rw [h0] at h0e; exact Or.inl (congrArg BitVec.toNat (Option.some.inj h0e.symm))
    | succ k =>
      refine Or.inr ⟨k + 1, by omega, hjlt, ?_⟩
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  refine ⟨hiff, fun l hl => hmem_take l ((hiff l).mp hl), hnd_sw, ?_, ?_⟩
  · dsimp only [tmp_sw]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), h0]
  · dsimp only [tmp_sw]; by_cases hm1' : max_idx = 1
    · subst hm1'; rw [List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]

theorem eagerSub_lm_step {tmp : List (BitVec 32)} {lm : List (BitVec 8)} {i nmax : Nat}
    (hinv : ∀ l < nmax, lm[l]?.getD 0#8 ≠ 0#8 → ∃ j < i, (tmp[j]?.getD 0#32).toNat = l) :
    ∀ l < nmax, (lm.set (tmp[i]?.getD 0#32).toNat 1#8)[l]?.getD 0#8 ≠ 0#8 →
      ∃ j < i + 1, (tmp[j]?.getD 0#32).toNat = l := by
  intro l hl hnz; by_cases hli : l = (tmp[i]?.getD 0#32).toNat
  · exact ⟨i, by omega, hli.symm⟩
  · rw [List.getElem?_set_ne (Ne.symm hli)] at hnz
    obtain ⟨j, hj, hje⟩ := hinv l hl hnz; exact ⟨j, by omega, hje⟩

theorem eagerSub_lm_clear_step {tmp : List (BitVec 32)} {lm : List (BitVec 8)}
    {tlen i nmax : Nat} (hlm_len : lm.length = nmax) (hlt : (tmp[i]?.getD 0#32).toNat < nmax)
    (hinv : ∀ l < nmax, lm[l]?.getD 0#8 ≠ 0#8 →
      (∃ j < tlen, (tmp[j]?.getD 0#32).toNat = l) ∧ (∀ j < i, (tmp[j]?.getD 0#32).toNat ≠ l)) :
    ∀ l < nmax, (lm.set (tmp[i]?.getD 0#32).toNat 0#8)[l]?.getD 0#8 ≠ 0#8 →
      (∃ j < tlen, (tmp[j]?.getD 0#32).toNat = l) ∧
      (∀ j < i + 1, (tmp[j]?.getD 0#32).toNat ≠ l) := by
  intro l hl hnz; by_cases hli : l = (tmp[i]?.getD 0#32).toNat
  · rw [hli, List.getElem?_set_self (by omega), Option.getD_some] at hnz; exact absurd rfl hnz
  · rw [List.getElem?_set_ne (Ne.symm hli)] at hnz
    obtain ⟨hex, hprev⟩ := hinv l hl hnz; refine ⟨hex, fun j hj => ?_⟩
    by_cases hji : j = i; · subst hji; exact Ne.symm hli
    · exact hprev j (by omega)

theorem chronoAssign_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hw : FullWitnessInv c F0 F_cur s.core) (hlen : s.LengthsOk c)
    {lit rsn : BitVec 32} {alvl : Nat}
    {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64}
    {scratch' : FullScratch}
    (hsok' : scratch'.LengthsOk c) (hfll : flags'.length = c.max_vars)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (halvl_le : alvl ≤ s.core.cur_level)
    (hpos_rsn : 0 < alvl → rsn ≠ 0xFFFFFFFF#32)
    (hl0 : alvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hrsn : 0 < alvl → rsn ≠ 0xFFFFFFFF#32 →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot]) ∧
        ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ alvl
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
          q = lit.toNat ∨ ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ alvl)
    (hrsn_mem : 0 < alvl → rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      lit.toNat ∈ fullArenaClauseLitsCore s.core rsn.toNat) :
    let v := lit.toNat / 2
    let rsn' := if alvl = 0 then 0xFFFFFFFF#32 else rsn
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 alvl)
            rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            trail_end := s.core.trail_end + 1
            unassigned := unassigned', unflushed := unflushed' }
        scratch := scratch' }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core := by
  intro v rsn' s'
  have hcl := hlen.core_ok
  have hte_lt := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var := (hw.vals_zero_iff hlit).mp hun
  have hnlit_lt := litNeg_lt_two_mul hlit
  have hne_lit := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have halvl_lt32 : alvl < 2 ^ 32 := by
    have := fullInv_max_vars_lt32 c; have := hw.cur_level_le
    have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1, (s'.core.trl[i]?.getD 0#32).toNat =
      if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = s.core.trail_end
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars, (s'.core.lvl[w]?.getD 0#32).toNat =
      if w = v then alvl else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt),
        bv32_ofNat_toNat halvl_lt32]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars, s'.core.vals[l]?.getD 0#8 =
      if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
      else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars, s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
      if w = v then rsn' else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
      vals_len := (by simp [s', hcl.vals_len]), flags_len := hfll,
      lvl_len := (by simp [s', hcl.lvl_len]), rsns_len := (by simp [s', hcl.rsns_len]),
      trl_len := (by simp [s', hcl.trl_len]),
      trail_pos_len := (by simp [s', hcl.trail_pos_len]),
      trail_end_le := (by dsimp [s']; omega),
      propagated_le := (by have := hcl.propagated_le; dsimp [s']; omega) }, hsok'⟩
  refine ⟨hlen', {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := by dsimp [s']; have := hw.cur_level_le; omega
    trail_lits_lt := fun i hi => by
      dsimp only [s'] at hi ⊢; rw [htrl_get i hi]; split
      · exact hlit
      · exact hw.trail_lits_lt i (by omega)
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp only [s'] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      rw [hvals_get l hl]; split; exact Or.inr (Or.inr rfl); split; exact Or.inr (Or.inl rfl)
      exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp only [s']; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq
          rw [ite_eq_right (show lit.toNat ≠ lit.toNat ^^^ 1 from hne_lit.symm)]; simp
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp only [s']; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨s.core.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
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
    lvl_le := fun i hi => by
      dsimp only [s'] at hi ⊢; rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simpa using halvl_le
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]; rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
        rw [ite_eq_right (hnot_var i hilt)]; exact hw.lvl_le i hilt
    dec_earliest := fun i j hi hj hleq hdec => by
      dsimp only [s'] at hi hj; rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
      by_cases hje : j = s.core.trail_end
      · subst hje; simp only [↓reduceIte] at hleq hdec
        rw [hlvl_get v (by omega), hrsn_get v (by omega)] at hdec; simp only [↓reduceIte] at hdec
        have hal0 : alvl ≠ 0 := by omega
        exact absurd (by simpa [rsn', hal0] using hdec.2) (hpos_rsn hdec.1)
      · by_cases hie : i = s.core.trail_end
        · omega
        · have hilt : i < s.core.trail_end := by omega
          have hjlt : j < s.core.trail_end := by omega
          simp only [hie, hje, ↓reduceIte] at hleq hdec
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega),
            hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hleq
          rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega),
            hrsn_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hdec
          rw [ite_eq_right (hnot_var i hilt)] at hleq
          rw [ite_eq_right (hnot_var j hjlt)] at hleq hdec
          rw [ite_eq_right (hnot_var j hjlt)] at hdec
          exact hw.dec_earliest i j hilt hjlt hleq hdec
    levels_inhabited := fun L hL1 hLle => by
      dsimp only [s'] at hLle ⊢; obtain ⟨i, hi, hli⟩ := hw.levels_inhabited L hL1 hLle
      refine ⟨i, by omega, ?_⟩; rw [htrl_get i (by omega)]
      simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte]
      rw [hlvl_get _ (by have := hw.trail_lits_lt i hi; omega),
        ite_eq_right (hnot_var i hi)]; exact hli
    level0_sound := fun i hi hli => by
      dsimp only [s'] at hi; rw [htrl_get i hi] at hli ⊢; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; exact hl0 hli
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hli
        rw [ite_eq_right (hnot_var i hilt)] at hli; exact hw.level0_sound i hilt hli
    trail_pos_inv := fun i hi => by
      dsimp only [s'] at hi; rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · subst hie; simp only [↓reduceIte]; dsimp only [s']
        rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat hte_lt32]
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]
        have hnv := hnot_var i hilt; dsimp only [s']
        rw [List.getElem?_set_ne (Ne.symm hnv)]; exact hw.trail_pos_inv i hilt
    level0_rsn_none := fun idx hidx hli => by
      dsimp only [s'] at hidx; rw [htrl_get idx hidx] at hli ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; rw [hrsn_get v (by omega)]; simp [rsn', hli]
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢; have hnv := hnot_var idx hilt
        rw [hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega), ite_eq_right hnv] at hli
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega), ite_eq_right hnv]
        exact hw.level0_rsn_none idx hilt hli
    frame_trail_lt := fun L hL => Nat.le_trans (hw.frame_trail_lt L hL) (by dsimp [s']; omega)
    frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := fun L hL1 hLle i hi => by
      have hi_le := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle)
      have hb := hw.frame_trail_before_lt L hL1 hLle i hi; change _ < L at ⊢
      rw [htrl_get i (by omega)]; simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte]
      rw [hlvl_get _ (by have := hw.trail_lits_lt i hi_le; omega), ite_eq_right (hnot_var i hi_le)]
      exact hb
    frame_dec_lt := hw.frame_dec_lt
    reason_inv := fun idx hidx hne => by
      dsimp only [s'] at hidx; rw [htrl_get idx hidx] at hne ⊢
      have hrsn_step : ∀ {p : Nat} {rsn_i : BitVec 32} {lim : Nat},
          lim ≤ idx → p < 2 * s.core.cur_vars → rsn_i ≠ 0xFFFFFFFF#32 →
          (if (rsn_i &&& 0x80000000#32) ≠ 0#32 then
            let ot := (rsn_i &&& 0x7FFFFFFF#32).toNat
            ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
            ∃ m < lim, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
              (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ (s'.core.lvl[p / 2]?.getD 0#32).toNat
          else
            rsn_i.toNat ∈ fullArenaClauseRefsCore s.core ∧
            fullArenaClauseGarbCore s.core rsn_i.toNat = false ∧
            ∀ q ∈ fullArenaClauseLitsCore s.core rsn_i.toNat,
              q = p ∨ ∃ m < lim, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ (s'.core.lvl[p / 2]?.getD 0#32).toNat) →
          if (rsn_i &&& 0x80000000#32) ≠ 0#32 then
            let ot := (rsn_i &&& 0x7FFFFFFF#32).toNat
            ot < 2 * s'.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
            ∃ m < idx, (s'.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
              (s'.core.lvl[ot / 2]?.getD 0#32).toNat ≤ (s'.core.lvl[p / 2]?.getD 0#32).toNat
          else
            rsn_i.toNat ∈ fullArenaClauseRefsCore s'.core ∧
            fullArenaClauseGarbCore s'.core rsn_i.toNat = false ∧
            ∀ q ∈ fullArenaClauseLitsCore s'.core rsn_i.toNat,
              q = p ∨ ∃ m < idx, (s'.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                (s'.core.lvl[q / 2]?.getD 0#32).toNat ≤ (s'.core.lvl[p / 2]?.getD 0#32).toNat := by
        intro p rsn_i lim hlim hp _ hsrc
        have hm_le : lim ≤ s.core.trail_end := by omega
        by_cases hbin : (rsn_i &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hsrc ⊢; obtain ⟨hot, hent, m, hm, hmeq, hle⟩ := hsrc
          have hot_v : (rsn_i &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
            intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
            exact hme (by simpa [fullInv_var_xor1] using heqv)
          refine ⟨hot, hent, m, by omega, ?_, ?_⟩
          · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
          · rw [hlvl_get _ (by omega)]; rw [ite_eq_right hot_v]; exact hle
        · rw [ite_eq_right hbin] at hsrc ⊢
          refine ⟨hsrc.1, hsrc.2.1, fun q hq => ?_⟩
          have hq' : q ∈ fullArenaClauseLitsCore s.core rsn_i.toNat := by
            simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using hq
          refine (hsrc.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hle⟩ => Or.inr ⟨m, by omega, ?_, ?_⟩
          · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
          · have hq_lt : q < 2 * s.core.cur_vars := hw.arena.lits_lt _ hsrc.1 hsrc.2.1 q hq'
            have hqv : q / 2 ≠ v := by
              intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
              exact hme (by simpa [fullInv_var_xor1] using heqv)
            rw [hlvl_get _ (by omega)]; rw [ite_eq_right hqv]; exact hle
      by_cases hie : idx = s.core.trail_end
      · subst hie; simp only [↓reduceIte] at hne ⊢
        rw [hrsn_get v (by omega)] at hne ⊢; simp only [↓reduceIte] at hne ⊢
        by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · have halpos : 0 < alvl := Nat.zero_lt_of_ne_zero hal0
          have hrs := hrsn halpos (by simpa [rsn', hal0] using hne)
          simp only [rsn', hal0, ↓reduceIte] at hne hrs ⊢
          refine hrsn_step (lim := s.core.trail_end) (Nat.le_refl _) hlit hne ?_
          rw [hlvl_get v (by omega), ite_eq_left rfl]; exact hrs
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne ⊢; have hnv := hnot_var idx hilt
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne ⊢
        rw [ite_eq_right hnv] at hne ⊢
        have hlt_p := hw.trail_lits_lt idx hilt
        refine hrsn_step (lim := idx) (Nat.le_refl _) hlt_p hne ?_
        rw [hlvl_get _ (by omega), ite_eq_right hnv]; exact hw.reason_inv idx hilt hne
    reason_lit_mem := fun idx hidx hne hlg => by
      dsimp only [s'] at hidx; rw [htrl_get idx hidx] at hne hlg ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne hlg ⊢
        rw [hrsn_get v (by omega)] at hne hlg ⊢; simp only [↓reduceIte] at hne hlg ⊢
        by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · simp only [rsn', hal0, ↓reduceIte] at hne hlg ⊢
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
            hrsn_mem (Nat.zero_lt_of_ne_zero hal0) hne hlg
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne hlg ⊢; have hnv := hnot_var idx hilt
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne hlg ⊢
        rw [ite_eq_right hnv] at hne hlg ⊢
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
          hw.reason_lit_mem idx hilt hne hlg }⟩

end FullLearnAnaHelpers

end PureHelpers

end LeanQbe.T.Examples.Kissat.Full
