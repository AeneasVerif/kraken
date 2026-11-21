module

public import LeanQbe.T.Examples.Kissat.Full1
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Stage-4 Arena / Watch-Stack Proofs & Shared Specs (Part 1)

Defines (`#1023` narrowed `4`-function UNSAT-only shard):
1. Scoped tactic & arithmetic helpers (`FullIngestTactics` and `fi_*`).
2. `FullIngestSpecs`: shared `FullLitMarksClear`, `FullArenaVarsNodup`, `FullLastLearnedWf`,
   `FullExtScratchOk`, `FullProbeScratchPres`, `FullSparseInv`, `FullDenseInv`,
   `FullOtfsWitnessInv`, `FullWsortMaxHeap`, callee contracts (`fullWsortSiftSpec`,
   `fullSaveTargetBestSpec`, `fullHeapPushSpec`), and owned contracts (`fullArenaNextSpec`,
   `fullAllocClSpec`, `fullWstackDefragSpec`, `fullBacktrackSpec`).
3. Parametric `(Γ : Env)` `Func.wp` proof for `full_wstack_defrag` (`full_arena_next` and
   `full_alloc_cl` are in `FullIngestLemmas.lean`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 0. Strictly scoped tactics & arithmetic helpers (`FullIngestTactics`) -/

namespace FullIngestTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "full_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "full_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "full_steps" : tactic =>
  `(tactic| (
    (try full_unmdata)
    (repeat full_strip)
    c0_steps
    repeat (any_goals (full_strip; repeat full_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining joins. -/
scoped elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let _ ← evalTactic (← `(tactic| try full_unmdata))
      let g ← getMainGoal
      let ty ← Lean.instantiateMVars (← g.getType)
      let ty := ty.consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
        let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
        let _ ← evalTactic (← `(tactic| try full_unmdata))
      let g ← getMainGoal
      let ty ← Lean.instantiateMVars (← g.getType)
      let ty := ty.consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step all goals like `c0_steps!`, stripping `mdata`, `Blocks.get`, and `strip_le` first. -/
scoped elab "full_c0_steps" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let _ ← evalTactic (← `(tactic| try full_unmdata))
      let g ← getMainGoal
      let ty ← Lean.instantiateMVars (← g.getType)
      let ty := ty.consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
        let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
        let _ ← evalTactic (← `(tactic| try full_unmdata))
      let _ ← evalTactic (← `(tactic| repeat full_strip))
      if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split once. -/
scoped elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let _ ← evalTactic (← `(tactic| try full_unmdata))
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
      let _ ← evalTactic (← `(tactic| try full_unmdata))
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

section BvC0Extras
@[scoped bv_c0] theorem bv32_0_toNat : (0 : BitVec 32).toNat = 0 := rfl
@[scoped bv_c0] theorem bv32_1_toNat : (1 : BitVec 32).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_0_toNat : (0 : BitVec 64).toNat = 0 := rfl
@[scoped bv_c0] theorem bv64_1_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_2_toNat : (2 : BitVec 64).toNat = 2 := rfl
@[scoped bv_c0] theorem bv64_3_toNat : (3 : BitVec 64).toNat = 3 := rfl
@[scoped bv_c0] theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x
@[scoped bv_c0] theorem bv32_toNat_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv64_toNat_mod64 (x : BitVec 64) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt x.isLt
attribute [scoped bv_c0 high] bv_c0_zext32_64 bv_c0_zext8_64 bv_c0_zext8_32
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set List.length_replicate
  BitVec.toNat_ushiftRight BitVec.toNat_shiftLeft BitVec.toNat_xor BitVec.toNat_and
  Nat.shiftLeft_eq Nat.shiftRight_eq_div_pow Bool.false_eq_true
end BvC0Extras

section AddZeroMem
@[scoped c0_store] theorem store_full_wstk_add0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.wstk.length)
    (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWstk + 0#64) ∧
      (FullMem c { s with core := { s.core with wstk := s.core.wstk.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pWstk + 0#64) v) := by
  rw [BitVec.add_zero]; exact FullArenaTactics.store_full_wstk0 v hi hm
@[scoped c0_load] theorem load_full_wsort_add0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.wsort.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 (c.pWsort + 0#64) = some s.scratch.wsort[0] := by
  rw [BitVec.add_zero]; exact FullArenaTactics.load_full_wsort0 hi hm
@[scoped c0_store] theorem store_full_wsort_add0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.wsort.length)
    (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWsort + 0#64) ∧
      (FullMem c { s with scratch := { s.scratch with wsort := s.scratch.wsort.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pWsort + 0#64) v) := by
  rw [BitVec.add_zero]; exact FullArenaTactics.store_full_wsort0 v hi hm
end AddZeroMem

end FullIngestTactics

open scoped FullArenaTactics FullIngestTactics

/-! ## 1. Reusable `List` index helper -/

private theorem fi_list_getElem_toNat_eq {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hij : i = j) : (xs[i]'hi).toNat = (xs[j]?.getD 0#32).toNat := by
  subst hij; rw [List.getElem?_eq_getElem hi, Option.getD_some]

/-! ## 2. Stage-4 invariants, watch-sort predicates, and local `Spec`s (`FullIngestSpecs`) -/

namespace FullIngestSpecs

/-- Variable marks (`< c.max_vars`) are zero (`#1003`). -/
def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

/-- Both variable marks (`< c.max_vars`) and literal marks (`< 2 * c.max_vars`) are zero. -/
def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8

/-- All non-garbage arena clauses have pairwise distinct variable indices (`· / 2`). -/
def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- All 8 cache slots in `last_learned[0..7]` are either `0xFFFFFFFF` or live arena refs. -/
def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8, let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Shared scratch-side well-formedness invariant (`last_learned` + `extend_len`). -/
def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Scratch-level equality predicate preserving `last_learned` and `extend_len`. -/
def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

/-- Extended scratch-frame predicate preserved across `full_save_target_best`, `full_heap_push`,
and `full_backtrack` (`FullSpec1:74-82`). -/
def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

theorem FullProbeScratchPres.trans {s s1 s2 : FullState}
    (h1 : FullProbeScratchPres s s1) (h2 : FullProbeScratchPres s1 s2) :
    FullProbeScratchPres s s2 :=
  ⟨⟨h2.1.1.trans h1.1.1, h2.1.2.trans h1.1.2⟩,
   h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2⟩

/-- Primary Stage-4 sparse 2WL UNSAT-soundness invariant (`dense_mode = 0`). -/
def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Dense occurrence-list UNSAT-soundness invariant (`dense_mode ≠ 0`, root level). -/
def FullDenseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

/-- Relaxed `FullWitnessInv` during OTFS retry (`FullSpec1:1208-1270`). -/
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

theorem FullWitnessInv.toOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) : FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
   h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le,
   h.dec_earliest, h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none,
   h.frame_trail_lt, h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
   fun idx hi _ hne => h.reason_inv idx hi hne,
   fun idx hi _ hne hlg => h.reason_lit_mem idx hi hne hlg⟩

/-- Max-heap property on `ws[lo ..< n)` keyed by `wvec[2 * l]` (`FullSpec2:35-39`). -/
def FullWsortMaxHeap (wvec ws : List (BitVec 32)) (lo n : Nat) : Prop :=
  ∀ i, lo ≤ i → i < n →
    let p := (wvec[2 * (ws[i]?.getD 0#32).toNat]?.getD 0#32).toNat
    (2 * i + 1 < n → (wvec[2 * (ws[2 * i + 1]?.getD 0#32).toNat]?.getD 0#32).toNat ≤ p) ∧
    (2 * i + 2 < n → (wvec[2 * (ws[2 * i + 2]?.getD 0#32).toNat]?.getD 0#32).toNat ≤ p)

/-- Callee `Spec`: `full_wsort_sift(wvec, ws, start, n)` (`FullSpec2:108-119` + `#1058`). -/
def fullWsortSiftSpec : Spec [i64, i64, i64, i64] [] :=
  fun (wvec_ptr, ws_ptr, start, n, ()) m Q _ =>
    ∃ (nlits : Nat) (wvec ws : List (BitVec 32)) (R : Mem 64 → Prop),
      2 * nlits ≤ wvec.length ∧ start.toNat < 2 ^ 62 ∧ n.toNat < 2 ^ 62 ∧
      start.toNat < n.toNat ∧ n.toNat ≤ ws.length ∧
      (∀ i < n.toNat, (ws[i]?.getD 0#32).toNat < nlits) ∧
      FullWsortMaxHeap wvec ws (start.toNat + 1) n.toNat ∧
      (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws ⋆ R) m ∧
      ∀ ws' m',
        ws'.length = ws.length → ws'.Perm ws →
        (∀ i, (i < start.toNat ∨ n.toNat ≤ i) → ws'[i]? = ws[i]?) →
        FullWsortMaxHeap wvec ws' start.toNat n.toNat →
        (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws' ⋆ R) m' → Q () m'

/-- Exact scratch-frame predicate preserved by `full_backtrack` (polarity-safe). -/
def BacktrackScrFrame (s s' : FullState) : Prop :=
  FullProbeScratchPres s s' ∧
  ∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss',
    s'.scratch = { s.scratch with
      target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
      heap := hp', pos := ps', heap_len := hl',
      q_search_idx := qsi', q_search_stamp := qss' }

/-- Callee `Spec`: `full_save_target_best(h)` matching `FullSpec2.fullSaveTargetBestSpec`. -/
def fullSaveTargetBestSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s' ∧
      ∃ ta' ba' pt' pb', s'.scratch = { s.scratch with
        target_assigned := ta', best_assigned := ba',
        phases_target := pt', phases_best := pb' })

/-- Callee `Spec`: `full_heap_push(h, v)` matching `FullSpec2.fullHeapPushSpec`. -/
def fullHeapPushSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s' ∧
      ∃ hp' ps' hl', s'.scratch = { s.scratch with heap := hp', pos := ps', heap_len := hl' })

/-- Specification of `full_arena_next(h, cref)` (`FullSpec2:84-87`). -/
def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

/-- Specification of `full_alloc_cl(h, sz, glue, red)` (`FullSpec2:89-106`). -/
def fullAllocClSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, sz, _glue, red, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      if c.arena_cap - s.core.arena_len < 3 + sz.toNat then
        Q (0xFFFFFFFF#64, ()) m
      else
        ∀ arena' m',
          let alen' := s.core.arena_len + 3 + sz.toNat
          let s' : FullState :=
            { s with core := { s.core with arena_len := alen', arena := arena' } }
          s'.LengthsOk c →
          (∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?) →
          (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 →
          (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 →
          ((arena'[s.core.arena_len]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ↔ red = true) →
          (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat →
          (FullMem c s' ⋆ R) m' →
          Q (BitVec.ofNat 64 s.core.arena_len, ()) m'

/-- Specification of `full_wstack_defrag(h)` (`FullSpec2:121-133`). -/
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

/-- Specification of `full_backtrack(h, target_lvl)` (polarity-safe exact scratch frame). -/
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
      cl' = min s.core.cur_level target_lvl.toNat → BacktrackScrFrame s s' →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (∀ l < 2 * s.core.cur_vars,
        (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
        vals'[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8) →
      (∀ v < s.core.cur_vars,
        (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat →
        lvl'[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32) →
      ((∃ F0 F_cur,
          FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
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

end FullIngestSpecs

open FullIngestSpecs

/-! ## 3. Pure heapsort / compaction helpers & `full_wstack_defrag` -/

private def wsVal (ws : List (BitVec 32)) (i : Nat) : Nat :=
  (ws[i]?.getD 0#32).toNat

private def WsCovers (ws : List (BitVec 32)) (n nlits : Nat) (sz : Nat → Nat) : Prop :=
  (∀ i < n, wsVal ws i < nlits ∧ 0 < sz (wsVal ws i)) ∧
  (∀ i < n, ∀ j < n, i ≠ j → wsVal ws i ≠ wsVal ws j) ∧
  (∀ l < nlits, 0 < sz l → ∃ i < n, wsVal ws i = l)

private def SortedRange (key : Nat → Nat) (ws : List (BitVec 32)) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → key (wsVal ws i) ≤ key (wsVal ws j)

private def SplitLe (key : Nat → Nat) (ws : List (BitVec 32)) (mid hi : Nat) : Prop :=
  ∀ i < mid, ∀ j, mid ≤ j → j < hi → key (wsVal ws i) ≤ key (wsVal ws j)

private def swapIdx (i j k : Nat) : Nat :=
  if k = i then j else if k = j then i else k

private theorem swapIdx_invol (i j k : Nat) : swapIdx i j (swapIdx i j k) = k := by
  unfold swapIdx; grind

private theorem wsVal_swap {ws : List (BitVec 32)} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (k : Nat) :
    wsVal ((ws.set i (ws[j]'hj)).set j (ws[i]'hi)) k = wsVal ws (swapIdx i j k) := by
  unfold wsVal swapIdx
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self (by simp; omega)]
    by_cases hki : k = i <;> simp [hki, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne (by omega)]
    by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self (by omega)]; simp [List.getElem?_eq_getElem hj]
    · rw [List.getElem?_set_ne (by omega)]; simp [hki, hkj]

private theorem wsCovers_swap {ws : List (BitVec 32)} {n nlits i j : Nat} {sz : Nat → Nat}
    (hc : WsCovers ws n nlits sz) (hi : i < n) (hj : j < n) (hn : n ≤ ws.length) :
    WsCovers ((ws.set i (ws[j]'(by omega))).set j (ws[i]'(by omega))) n nlits sz := by
  obtain ⟨hb, hnd, hcov⟩ := hc
  have hlt : ∀ k < n, swapIdx i j k < n := fun k hk => by unfold swapIdx; grind
  refine ⟨fun k hk => by rw [wsVal_swap (by omega) (by omega)]; exact hb _ (hlt k hk),
    fun a ha b hb' hab => by
      rw [wsVal_swap (by omega) (by omega), wsVal_swap (by omega) (by omega)]
      refine hnd _ (hlt a ha) _ (hlt b hb') fun heq => hab ?_
      simpa [swapIdx_invol] using congrArg (swapIdx i j) heq,
    fun l hl hsz => by
      obtain ⟨k, hk, hkl⟩ := hcov l hl hsz
      exact ⟨swapIdx i j k, hlt k hk, by
        rw [wsVal_swap (by omega) (by omega), swapIdx_invol]; exact hkl⟩⟩

private theorem list_perm_take_of_drop_eq {α : Type} {l1 l2 : List α} {n : Nat}
    (hlen : l1.length = l2.length) (hn : n ≤ l2.length)
    (hperm : l1.Perm l2) (hsuf : ∀ i, n ≤ i → l1[i]? = l2[i]?) :
    (l1.take n).Perm (l2.take n) := by
  have hdrop : l1.drop n = l2.drop n := by
    apply List.ext_getElem
    · simp [List.length_drop, hlen]
    · intro i hi _; simp only [List.length_drop] at hi
      rw [List.getElem_drop, List.getElem_drop]
      have heq := hsuf (n + i) (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
      exact Option.some.inj heq
  have hsplit : (l1.take n ++ l2.drop n).Perm (l2.take n ++ l2.drop n) := by
    rw [← hdrop, List.take_append_drop, hdrop, List.take_append_drop]; exact hperm
  exact (List.perm_append_right_iff (l2.drop n)).mp hsplit

private theorem wsCovers_of_perm_suffix {ws ws' : List (BitVec 32)} {n nlits : Nat}
    {sz : Nat → Nat} (hcov : WsCovers ws n nlits sz)
    (hlen : ws'.length = ws.length) (hn : n ≤ ws.length)
    (hperm : ws'.Perm ws) (hsuf : ∀ i, n ≤ i → ws'[i]? = ws[i]?) :
    WsCovers ws' n nlits sz := by
  have htp := list_perm_take_of_drop_eq hlen hn hperm hsuf
  have hlen_tk' : (ws'.take n).length = n := by rw [List.length_take]; omega
  have hlen_tk : (ws.take n).length = n := by rw [List.length_take]; omega
  have hmem_tk : ∀ (l : List (BitVec 32)), (l.take n).length = n → ∀ x,
      (∃ i < n, l[i]? = some x) ↔ x ∈ l.take n := fun l hlk x => by
    constructor
    · rintro ⟨i, hi, heq⟩; have hilt : i < l.length := by rw [List.length_take] at hlk; omega
      rw [List.getElem?_eq_getElem hilt, Option.some.injEq] at heq; subst heq
      have hgm := List.getElem_mem (l := l.take n) (n := i) (by omega)
      rwa [List.getElem_take] at hgm
    · intro hx; obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hilt : i < l.length := by rw [hlk] at hi; rw [List.length_take] at hlk; omega
      refine ⟨i, by omega, ?_⟩; rw [List.getElem?_eq_getElem hilt, List.getElem_take]
  have hmem_iff : ∀ x, (∃ i < n, ws'[i]? = some x) ↔ (∃ i < n, ws[i]? = some x) := fun x =>
    (hmem_tk ws' hlen_tk' x).trans (htp.mem_iff.trans (hmem_tk ws hlen_tk x).symm)
  have hnd : (ws.take n).Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
    rw [List.getElem_take, List.getElem_take]
    intro heq; apply hcov.2.1 i (by omega) j (by omega) (by omega)
    unfold wsVal; rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      Option.getD_some, Option.getD_some, heq]
  have hnd' : (ws'.take n).Nodup := htp.nodup_iff.mpr hnd
  refine ⟨fun i hi => ?_, fun a ha b hb hab => ?_, fun l hl hsz => ?_⟩
  · obtain ⟨j, hj, hjeq⟩ :=
      (hmem_iff (ws'[i]'(by omega))).mp ⟨i, hi, List.getElem?_eq_getElem (by omega)⟩
    have hveq : wsVal ws' i = wsVal ws j := by
      unfold wsVal; rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        hjeq, Option.getD_some]
    rw [hveq]; exact hcov.1 j hj
  · have hlt : a < b ∨ b < a := Nat.lt_or_gt_of_ne hab
    intro hveq
    have heqv : (ws'.take n)[a]'(by omega) = (ws'.take n)[b]'(by omega) := by
      rw [List.getElem_take, List.getElem_take]; apply BitVec.eq_of_toNat_eq
      unfold wsVal at hveq
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some, Option.getD_some] at hveq
      exact hveq
    rcases hlt with h1 | h2
    · exact List.pairwise_iff_getElem.mp hnd' a b (by omega) (by omega) h1 heqv
    · exact List.pairwise_iff_getElem.mp hnd' b a (by omega) (by omega) h2 heqv.symm
  · obtain ⟨j, hj, hjl⟩ := hcov.2.2 l hl hsz
    obtain ⟨i, hi, hieq⟩ :=
      (hmem_iff (ws[j]'(by omega))).mpr ⟨j, hj, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨i, hi, ?_⟩
    unfold wsVal at hjl ⊢; rw [hieq, Option.getD_some]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hjl; exact hjl

private theorem wsortMaxHeap_root_ge {wvec ws : List (BitVec 32)} {hi : Nat}
    (hmax : FullWsortMaxHeap wvec ws 0 hi) :
    ∀ i < hi,
      (wvec[2 * wsVal ws i]?.getD 0#32).toNat ≤ (wvec[2 * wsVal ws 0]?.getD 0#32).toNat := by
  intro i; induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hilt; rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact Nat.le_refl _
    · have hrec := ih _ (show (i - 1) / 2 < i by omega) (by omega)
      have hstep := hmax ((i - 1) / 2) (by omega) (by omega)
      by_cases hodd : i = 2 * ((i - 1) / 2) + 1
      · have := hstep.1 (by omega); rw [← hodd] at this; exact Nat.le_trans this hrec
      · have := hstep.2 (by omega)
        rw [← show i = 2 * ((i - 1) / 2) + 2 by omega] at this; exact Nat.le_trans this hrec

private theorem wsort_extract_swap_step {wvec ws : List (BitVec 32)} {e n : Nat}
    (hmax : FullWsortMaxHeap wvec ws 0 (e + 1))
    (hsp : SplitLe (fun l => (wvec[2 * l]?.getD 0#32).toNat) ws (e + 1) n)
    (hsrt : SortedRange (fun l => (wvec[2 * l]?.getD 0#32).toNat) ws (e + 1) n)
    (he : 0 < e) (hen : e < n) (hn : n ≤ ws.length) :
    let ws' := (ws.set 0 (ws[e]'(by omega))).set e (ws[0]'(by omega))
    let key := fun l => (wvec[2 * l]?.getD 0#32).toNat
    FullWsortMaxHeap wvec ws' 1 e ∧ SplitLe key ws' e n ∧ SortedRange key ws' e n := by
  intro ws' key; have hsw := wsVal_swap (ws := ws) (i := 0) (j := e) (by omega) (by omega)
  have hroot := wsortMaxHeap_root_ge hmax
  have hfix : ∀ k, 0 < k → k < e → swapIdx 0 e k = k := fun k _ _ => by unfold swapIdx; grind
  refine ⟨fun p hp hpe => ?_, fun i hi j hj1 hj2 => ?_, fun i j hi1 hij hj2 => ?_⟩
  · have hstep := hmax p (by omega) (by omega)
    constructor
    · intro h1; have hsw1 := hsw (2 * p + 1); have hswp := hsw p; unfold wsVal at hsw1 hswp
      dsimp only [ws']; rw [hsw1, hswp, hfix _ hp hpe, hfix _ (by omega) h1]
      exact hstep.1 (by omega)
    · intro h2; have hsw2 := hsw (2 * p + 2); have hswp := hsw p; unfold wsVal at hsw2 hswp
      dsimp only [ws']; rw [hsw2, hswp, hfix _ hp hpe, hfix _ (by omega) h2]
      exact hstep.2 (by omega)
  · dsimp only [key] at *; rw [hsw i, hsw j]
    have hisw : swapIdx 0 e i < e + 1 := by unfold swapIdx; grind
    by_cases hje : j = e
    · subst hje; rw [show swapIdx 0 j j = 0 by unfold swapIdx; grind]; exact hroot _ hisw
    · rw [show swapIdx 0 e j = j by unfold swapIdx; grind]; exact hsp _ hisw _ (by omega) hj2
  · dsimp only [key] at *; rw [hsw i, hsw j]
    by_cases hie : i = e
    · subst hie; rw [show swapIdx 0 i i = 0 by unfold swapIdx; grind]
      by_cases hje : j = i
      · subst hje; rw [show swapIdx 0 j j = 0 by unfold swapIdx; grind]; exact Nat.le_refl _
      · rw [show swapIdx 0 i j = j by unfold swapIdx; grind]
        exact hsp 0 (by omega) j (by omega) hj2
    · rw [show swapIdx 0 e i = i by unfold swapIdx; grind,
        show swapIdx 0 e j = j by unfold swapIdx; grind]
      exact hsrt i j (by omega) hij hj2

private theorem wsort_extract_perm_post {wvec ws ws' : List (BitVec 32)} {e n : Nat}
    (hlen : ws'.length = ws.length) (hen : e ≤ n) (hn : n ≤ ws.length)
    (hperm : ws'.Perm ws) (hsuf : ∀ i, e ≤ i → ws'[i]? = ws[i]?)
    (hsp : SplitLe (fun l => (wvec[2 * l]?.getD 0#32).toNat) ws e n)
    (hsrt : SortedRange (fun l => (wvec[2 * l]?.getD 0#32).toNat) ws e n) :
    let key := fun l => (wvec[2 * l]?.getD 0#32).toNat
    SplitLe key ws' e n ∧ SortedRange key ws' e n := by
  intro key; have htp := list_perm_take_of_drop_eq hlen (by omega) hperm hsuf
  have htk' : (ws'.take e).length = e := by rw [List.length_take]; omega
  have htk : (ws.take e).length = e := by rw [List.length_take]; omega
  refine ⟨fun i hi j hj1 hj2 => ?_, fun i j hi1 hij hj2 => ?_⟩
  · have hmem : ws'[i]'(by omega) ∈ ws'.take e := by
      have hgm := List.getElem_mem (l := ws'.take e) (n := i) (by rw [htk']; exact hi)
      rwa [List.getElem_take] at hgm
    obtain ⟨i0, hi0, hget0⟩ := List.mem_iff_getElem.mp (htp.mem_iff.mp hmem)
    rw [htk] at hi0; rw [List.getElem_take] at hget0
    have hvi : wsVal ws' i = wsVal ws i0 := by
      unfold wsVal; rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some, Option.getD_some, hget0]
    have hvj : wsVal ws' j = wsVal ws j := by unfold wsVal; rw [hsuf j hj1]
    dsimp only [key] at *; rw [hvi, hvj]; exact hsp i0 hi0 j hj1 hj2
  · have hvi : wsVal ws' i = wsVal ws i := by unfold wsVal; rw [hsuf i hi1]
    have hvj : wsVal ws' j = wsVal ws j := by unfold wsVal; rw [hsuf j (by omega)]
    dsimp only [key] at *; rw [hvi, hvj]; exact hsrt i j hi1 hij hj2

private theorem defrag_sorted_gap {s : FullState} {ws : List (BitVec 32)} {n : Nat}
    (hlay : WatchStackLayout s.core)
    (hcov : WsCovers ws n (2 * s.core.cur_vars) (fullWatchSize s))
    (hsrt : SortedRange (fullWatchOff s) ws 0 n) {i j : Nat} (hij : i < j) (hjn : j < n) :
    fullWatchOff s (wsVal ws i) + fullWatchSize s (wsVal ws i) ≤ fullWatchOff s (wsVal ws j) := by
  have hi := hcov.1 i (by omega); have hj := hcov.1 j hjn
  have hle := hsrt i j (by omega) (by omega) hjn
  rcases hlay.disjoint _ _ hi.1 hj.1 (hcov.2.1 i (by omega) j hjn (by omega)) hi.2 hj.2 with h | h
  · exact h
  · exfalso; unfold fullWatchOff fullWatchSize at *; omega

private theorem wvec_set_even_eq {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l < wvec.length) (j : Nat) :
    (wvec.set (2 * l) v)[2 * j + 1]? = wvec[2 * j + 1]? ∧
    (j ≠ l → (wvec.set (2 * l) v)[2 * j]? = wvec[2 * j]?) ∧
    (wvec.set (2 * l) v)[2 * l]? = some v :=
  ⟨List.getElem?_set_ne (by omega), fun _ => List.getElem?_set_ne (by omega),
   List.getElem?_set_self hl⟩

private theorem defrag_finalize {s : FullState}
    {wvecC wstkC wsort2 : List (BitVec 32)} {n p : Nat} (hlay : WatchStackLayout s.core)
    (hcov : WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s)) (_hp1 : 1 ≤ p)
    (hsz : ∀ l < 2 * s.core.cur_vars, (wvecC[2 * l + 1]?.getD 0#32).toNat = fullWatchSize s l)
    (hzero : ∀ l < 2 * s.core.cur_vars,
      fullWatchSize s l = 0 → (wvecC[2 * l]?.getD 0#32).toNat = 0)
    (hdone : ∀ j < n, let l := wsVal wsort2 j; let off := (wvecC[2 * l]?.getD 0#32).toNat;
      1 ≤ off ∧ off + fullWatchSize s l ≤ p ∧
      ∀ k < fullWatchSize s l, wstkC[off + k]? = s.core.wstk[fullWatchOff s l + k]?)
    (hdisj : ∀ a < n, ∀ b < n, a ≠ b →
      let la := wsVal wsort2 a; let lb := wsVal wsort2 b;
      (wvecC[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
        (wvecC[2 * lb]?.getD 0#32).toNat ∨
      (wvecC[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
        (wvecC[2 * la]?.getD 0#32).toNat) :
    let s' : FullState :=
      { s with core := { s.core with wvec := wvecC, wstk := wstkC, wlen := p, wusable := 0#64 }
               scratch := { s.scratch with wsort := wsort2 } }
    WatchStackLayout s'.core ∧
      ∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]? := by
  intro s'; have hsz' : ∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l := hsz
  refine ⟨⟨fun l hl => ?_, fun l hl hp => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
    fun l hl k hk => ?_⟩, fun l hl => ⟨hsz' l hl, fun k hk => ?_⟩⟩
  · change fullWatchOffCore s'.core l + fullWatchSizeCore s'.core l ≤ p
    rw [show fullWatchSizeCore s'.core l = fullWatchSize s' l from rfl, hsz' l hl]
    rcases Nat.eq_zero_or_pos (fullWatchSize s l) with hz | hp
    · change (wvecC[2 * l]?.getD 0#32).toNat + _ ≤ p; rw [hz, hzero l hl hz]; omega
    · obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl hp; exact (hdone j hj).2.1
  · rw [show fullWatchSizeCore s'.core l = fullWatchSize s' l from rfl, hsz' l hl] at hp
    obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl hp; exact (hdone j hj).1
  · rw [show fullWatchSizeCore s'.core l1 = fullWatchSize s' l1 from rfl, hsz' l1 h1] at hp1 ⊢
    rw [show fullWatchSizeCore s'.core l2 = fullWatchSize s' l2 from rfl, hsz' l2 h2] at hp2 ⊢
    obtain ⟨a, ha, rfl⟩ := hcov.2.2 l1 h1 hp1; obtain ⟨b, hb, rfl⟩ := hcov.2.2 l2 h2 hp2
    exact hdisj a ha b hb fun hab => hne (by rw [hab])
  · rw [show fullWatchSizeCore s'.core l = fullWatchSize s' l from rfl, hsz' l hl] at hk
    obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl (by omega)
    change wstkC[(wvecC[2 * wsVal wsort2 j]?.getD 0#32).toNat + k]? ≠ _
    rw [(hdone j hj).2.2 k hk]; exact hlay.no_sentinel _ hl k hk
  · obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl (by omega); exact (hdone j hj).2.2 k hk

/-! ## 5. `full_wstack_defrag` -/

private def fullWvecOff (wvec : List (BitVec 32)) (l : Nat) : Nat :=
  (wvec[2 * l]?.getD 0#32).toNat

private def FullCoreU32BNoWvec (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  array (t := i32) c.pFrameTrail k.frame_trail ⋆ array (t := i32) c.pFrameDec k.frame_dec ⋆
  array (t := i32) c.pRepr k.repr ⋆ array (t := i32) c.pMinStk k.min_stk

private def FullScrWksNoWsort (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array (t := i32) c.pWorkStk1 sc.work_stk1 ⋆ array (t := i32) c.pWorkStk2 sc.work_stk2 ⋆
  array (t := i32) c.pTarjanMark sc.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach sc.tarjan_reach

private def FullWvecWsortRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreU32BNoWvec c s.core ⋆
    FullCoreDynArrs c s.core) ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksNoWsort c s.scratch ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆ c.pad

private theorem fullMem_eq_wvec_wsort (c : FullCfg) (s : FullState) :
    FullMem c s = (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆ FullWvecWsortRest c s) := by
  unfold FullMem FullCoreArrays FullScratchArrays FullCoreU32B FullScrWksArrs
    FullWvecWsortRest FullCoreU32BNoWvec FullScrWksNoWsort
  ac_rfl

private theorem focus_wvec_wsort {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pWsort s.scratch.wsort ⋆
      (FullWvecWsortRest c s ⋆ R)) m := by
  rw [fullMem_eq_wvec_wsort, sep_assoc] at hm; exact hm

private theorem unfocus_wvec_wsort {c : FullCfg} {s : FullState} {ws' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hm' : (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pWsort ws' ⋆
      (FullWvecWsortRest c s ⋆ R)) m') :
    (FullMem c { s with scratch := { s.scratch with wsort := ws' } } ⋆ R) m' := by
  rw [fullMem_eq_wvec_wsort, sep_assoc]; exact hm'

theorem full_wstack_defrag_wp (Γ : Env)
    (hSift : ∀ a m Q X, fullWsortSiftSpec a m Q X →
      Γ "full_wsort_sift" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWstackDefragSpec a m Q X → Func.wp Γ full_wstack_defrag_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv; unfold dimacsBound at hmx
  have hwcap : c.wcap < 2 * dimacsBound := c.hwcap; unfold dimacsBound at hwcap
  have hcv_le := hcl.cur_vars_le
  have hwle := hcl.wlen_le; have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr
  have hwsrt_l := hsl.wsort_len
  full_steps
  · refine hQ s.core.wvec s.core.wstk s.core.wlen s.scratch.wsort _
      ⟨{ hcl with wlen_le := hwle }, hsl⟩
      (hlay.with_wstk rfl rfl rfl rfl) id (fun _ _ => ⟨rfl, fun _ _ => rfl⟩) hm
  · have hwlen_gt1 : 1 < s.core.wlen := by c0_bound
    have hwsl_pos : 0 < s.core.wstk.length := by omega
    have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
      rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega)]
      simp [Nat.shiftLeft_eq]; omega
    clear hc
    refine wp_loop_inv
      (fun (n, l, ()) m1 =>
        l.toNat ≤ 2 * s.core.cur_vars ∧ n.toNat ≤ l.toNat ∧
        ∃ (wvec1 wsort1 : List (BitVec 32)),
          wvec1.length = 4 * c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧
          (∀ j < 2 * s.core.cur_vars, wvec1[2 * j + 1]? = s.core.wvec[2 * j + 1]?) ∧
          (∀ j < 2 * s.core.cur_vars,
            0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?) ∧
          (∀ j < l.toNat, fullWatchSize s j = 0 → wvec1[2 * j]? = some 0#32) ∧
          WsCovers wsort1 n.toNat l.toNat (fullWatchSize s) ∧
          (FullMem c { s with core := { s.core with wvec := wvec1 },
                              scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1)
      (fun (_, l, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun J hLoop => ?_) ?_
    · c0_steps
      refine hLoop _ _ ⟨by simp, by simp, s.core.wvec, s.scratch.wsort, hwvl, hwsrt_l,
        fun _ _ => rfl, fun _ _ _ => rfl, fun _ hj => by simp at hj,
        ⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi, fun _ hl => by simp at hl⟩, hm⟩
    · rintro J ⟨n, l, ⟨⟩⟩ m1 ⟨hl_le, hn_le, wvec1, wsort1, hwv1, hws1,
        hsz1, hoff1, hzero1, hcov1, hm1⟩ hLoop
      clear hm
      c0_to_group
      · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
          have : l.toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
          omega
        have hl2 : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by
          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        have hl2p1 : ((l <<< (1 : Nat)) + 1).toNat = 2 * l.toNat + 1 := by
          rw [BitVec.toNat_add, hl2]; simp; omega
        have hl2_lt : (l <<< (1 : Nat)).toNat < wvec1.length := by omega
        have hl2p1_lt : ((l <<< (1 : Nat)) + 1).toNat < wvec1.length := by omega
        have hsz_eq : (wvec1[((l <<< (1 : Nat)) + 1).toNat]'hl2p1_lt).toNat =
            fullWatchSize s l.toNat := by
          unfold fullWatchSize fullWatchSizeCore
          have h1 := hsz1 l.toNat hl_lt; rw [← h1]
          have h2 : wvec1[((l <<< (1 : Nat)) + 1).toNat]'hl2p1_lt =
              wvec1[2 * l.toNat + 1]'(by omega) := by congr 1
          rw [h2, List.getElem?_eq_getElem (by omega), Option.getD_some]
        full_c0_steps
        · have hsz0 : fullWatchSize s l.toNat = 0 := by
            have hix : (l.toNat * 2 ^ 1 + 1) % 2 ^ 64 = 2 * l.toNat + 1 := by omega
            have h1 : (wvec1[(l.toNat * 2 ^ 1 + 1) % 2 ^ 64]'(by omega)).toNat =
                fullWatchSize s l.toNat := by
              rw [fi_list_getElem_toNat_eq (by omega) hix]
              unfold fullWatchSize fullWatchSizeCore; rw [hsz1 l.toNat hl_lt]
            rw [← h1, hc]; rfl
          have hset := wvec_set_even_eq (wvec := wvec1) (l := l.toNat) (v := 0#32) (by omega)
          have hlp1 : (l + 1).toNat = l.toNat + 1 := by bv_omega
          refine hLoop _ _ (by dsimp only; omega)
            ⟨by omega, by omega, _, wsort1, by rw [List.length_set, hwv1], hws1,
             fun j hj => by rw [hl2]; exact (hset j).1.trans (hsz1 j hj),
             fun j hj hp => by
               rw [hl2]; exact ((hset j).2.1 fun heq => by subst heq; omega).trans (hoff1 j hj hp),
             fun j hj hzj => by
               rw [hl2]; by_cases hjl : j = l.toNat
               · subst hjl; exact (hset l.toNat).2.2
               · exact ((hset j).2.1 hjl).trans (hzero1 j (by omega) hzj),
             ⟨fun i hi => ⟨by have := (hcov1.1 i hi).1; omega, (hcov1.1 i hi).2⟩, hcov1.2.1,
              fun j hj hzj => hcov1.2.2 j
                (if hjl : j = l.toNat then by subst hjl; omega else by omega) hzj⟩,
             hm⟩
        · have hszp : 0 < fullWatchSize s l.toNat := by
            have hix : (l.toNat * 2 ^ 1 + 1) % 2 ^ 64 = 2 * l.toNat + 1 := by omega
            have h1 : (wvec1[(l.toNat * 2 ^ 1 + 1) % 2 ^ 64]'(by omega)).toNat =
                fullWatchSize s l.toNat := by
              rw [fi_list_getElem_toNat_eq (by omega) hix]
              unfold fullWatchSize fullWatchSizeCore; rw [hsz1 l.toNat hl_lt]
            rw [← h1]; exact Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq h0)
          have hlp1 : (l + 1).toNat = l.toNat + 1 := by bv_omega
          have hnp1 : (n + 1).toNat = n.toNat + 1 := by bv_omega
          have htr : (l.setWidth 32).toNat = l.toNat := by
            rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
          have hws_at : ∀ k, wsVal (wsort1.set n.toNat (l.setWidth 32)) k =
              if k = n.toNat then l.toNat else wsVal wsort1 k := fun k => by
            unfold wsVal; by_cases hk : k = n.toNat
            · subst hk; rw [List.getElem?_set_self (by omega), Option.getD_some, htr]; simp
            · rw [List.getElem?_set_ne (by omega)]; simp [hk]
          refine hLoop _ _ (by dsimp only; omega)
            ⟨by omega, by omega, wvec1, _, hwv1, by rw [List.length_set, hws1], hsz1, hoff1,
             fun j hj hzj => hzero1 j
               (if hjl : j = l.toNat then by subst hjl; omega else by omega) hzj,
             ⟨fun i hi => by
                rw [hws_at]; split
                · exact ⟨by omega, hszp⟩
                · have := hcov1.1 i (by omega); exact ⟨by omega, this.2⟩,
              fun a ha b hb hab => by
                rw [hws_at, hws_at]; split <;> split
                · omega
                · have := (hcov1.1 b (by omega)).1; omega
                · have := (hcov1.1 a (by omega)).1; omega
                · exact hcov1.2.1 a (by omega) b (by omega) hab,
              fun j hj hzj => by
                by_cases hjl : j = l.toNat
                · subst hjl; exact ⟨n.toNat, by omega, by rw [hws_at]; simp⟩
                · obtain ⟨i, hi, hij⟩ := hcov1.2.2 j (by omega) hzj
                  exact ⟨i, by omega, by rw [hws_at]; simp [show i ≠ n.toNat by omega]; exact hij⟩⟩,
             hm⟩
      · have hl_eq : l.toNat = 2 * s.core.cur_vars := by
          have : ¬ (l.toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat) := by c0_bound
          omega
        rw [hl_eq] at hzero1 hcov1 hn_le; have hn0 : n.toNat = 0 := by rw [hc]; rfl
        have hfin := defrag_finalize (s := s) (wvecC := wvec1) (wstkC := s.core.wstk.set 0 0#32)
          (wsort2 := wsort1) (n := 0) (p := 1) hlay (by simpa [hn0] using hcov1) (by omega)
          (fun j hj => by have := hsz1 j hj; unfold fullWatchSize fullWatchSizeCore; rw [this])
          (fun j hj hz => by rw [hzero1 j hj hz]; rfl) (fun _ _ => by omega) (fun _ _ => by omega)
        refine hQ wvec1 (s.core.wstk.set 0 0#32) 1 wsort1 _
          ⟨{ hcl with wvec_len := hwv1, wstk_len_arr := by simp [hwsl],
                      wlen_le := by dsimp only; omega }, { hsl with wsort_len := hws1 }⟩
          hfin.1 (fun _ => by omega) hfin.2 hm
      · have hl_eq : l.toNat = 2 * s.core.cur_vars := by
          have : ¬ (l.toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat) := by c0_bound
          omega
        rw [hl_eq] at hzero1 hcov1 hn_le
        have hn_pos : 0 < n.toNat :=
          Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
        rename_i hc_ge; clear hc_ge hc hLoop J l hl_le hl_eq
        refine wp_join_group
          (fun _ m2 => ∃ wsort2 : List (BitVec 32), wsort2.length = 2 * c.max_vars ∧
            WsCovers wsort2 n.toNat (2 * s.core.cur_vars) (fullWatchSize s) ∧
            SortedRange (fullWatchOff s) wsort2 0 n.toNat ∧
            (FullMem c { s with core := { s.core with wvec := wvec1 },
                                scratch := { s.scratch with wsort := wsort2 } } ⋆ R) m2) ?_ ?_
        · rintro _ _ m2 ⟨wsort2, hws2, hcov2, hsrt2, hm2⟩
          clear hm1 wsort1 hws1 hcov1; c0_to_group
          refine wp_loop_inv
            (fun (p, i, ()) mC =>
              1 ≤ p.toNat ∧ p.toNat ≤ s.core.wlen ∧ i.toNat ≤ n.toNat ∧
              (i.toNat < n.toNat → p.toNat ≤ fullWatchOff s (wsVal wsort2 i.toNat)) ∧
              ∃ wvecC wstkC : List (BitVec 32), wvecC.length = 4 * c.max_vars ∧
                wstkC.length = c.wcap ∧
                (∀ j < 2 * s.core.cur_vars,
                  (wvecC[2 * j + 1]?.getD 0#32).toNat = fullWatchSize s j) ∧
                (∀ j < 2 * s.core.cur_vars,
                  fullWatchSize s j = 0 → (wvecC[2 * j]?.getD 0#32).toNat = 0) ∧
                (∀ j < i.toNat, let l := wsVal wsort2 j; let off := (wvecC[2 * l]?.getD 0#32).toNat
                  1 ≤ off ∧ off + fullWatchSize s l ≤ p.toNat ∧
                  ∀ k < fullWatchSize s l, wstkC[off + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                (∀ a < i.toNat, ∀ b < i.toNat, a ≠ b →
                  let la := wsVal wsort2 a; let lb := wsVal wsort2 b
                  (wvecC[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
                    (wvecC[2 * lb]?.getD 0#32).toNat ∨
                  (wvecC[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
                    (wvecC[2 * la]?.getD 0#32).toNat) ∧
                (∀ j, i.toNat ≤ j → j < n.toNat → let l := wsVal wsort2 j
                  (wvecC[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧ ∀ k < fullWatchSize s l,
                    wstkC[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                (FullMem c { s with core := { s.core with wvec := wvecC, wstk := wstkC },
                                    scratch := { s.scratch with wsort := wsort2 } } ⋆ R) mC)
            (fun (_, i, ()) _ => n.toNat - i.toNat) (fun J hLoop => ?_) ?_
          · c0_steps
            refine hLoop _ _ ⟨by simp, by simp; omega, by simp, fun h0 => ?_, wvec1, s.core.wstk,
              hwv1, hwsl, fun j hj => by unfold fullWatchSize fullWatchSizeCore; rw [hsz1 j hj],
              fun j hj hz => by rw [hzero1 j hj hz]; rfl,
              fun _ hj => by simp at hj, fun _ ha => by simp at ha,
              fun j _ hjn => ⟨by have := hcov2.1 j hjn
                                 unfold fullWatchOff fullWatchOffCore; rw [hoff1 _ this.1 this.2],
                fun _ _ => rfl⟩, hm2⟩
            have := hcov2.1 0 (by simpa using h0); simpa using hlay.pos_off _ this.1 this.2
          · rintro J ⟨p, i, ⟨⟩⟩ mC ⟨hp1, hple, hile, hp_off, wvecC, wstkC,
              hwvC, hwsC, hszC, hzeroC, hdoneC, hdisjC, hremC, hmC⟩ hLoop
            clear hm2; c0_split
            · have hi_lt : i.toNat < n.toNat := by c0_bound
              have hlit_info := hcov2.1 i.toNat hi_lt
              have hlit_eq : (wsort2[i.toNat]'(by omega)).toNat = wsVal wsort2 i.toNat := by
                unfold wsVal; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hlit_cv : (wsort2[i.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
                rw [hlit_eq]; exact hlit_info.1
              have hlit2 : ((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat =
                  2 * wsVal wsort2 i.toNat := by
                rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hlit_eq]
                simp [Nat.shiftLeft_eq]; omega
              have hlit2p1 :
                  (((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)) + 1).toNat =
                  2 * wsVal wsort2 i.toNat + 1 := by rw [BitVec.toNat_add, hlit2]; simp; omega
              have hlit2_lt : ((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat <
                  wvecC.length := by omega
              have hlit2p1_lt :
                  (((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)) + 1).toNat <
                  wvecC.length := by omega
              have hoff_i : (wvecC[((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat]'
                  hlit2_lt).toNat = fullWatchOff s (wsVal wsort2 i.toNat) := by
                rw [fi_list_getElem_toNat_eq hlit2_lt hlit2]
                exact (hremC i.toNat (by omega) hi_lt).1
              have hsz_i :
                  (wvecC[(((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)) + 1).toNat]'
                    hlit2p1_lt).toNat = fullWatchSize s (wsVal wsort2 i.toNat) := by
                rw [fi_list_getElem_toNat_eq hlit2p1_lt hlit2p1]
                exact hszC (wsVal wsort2 i.toNat) hlit_info.1
              have hp_le_off : p.toNat ≤ fullWatchOff s (wsVal wsort2 i.toNat) := hp_off hi_lt
              have hoff_sz_le : fullWatchOff s (wsVal wsort2 i.toNat) +
                  fullWatchSize s (wsVal wsort2 i.toNat) ≤ s.core.wlen := hlay.bounds _ hlit_info.1
              rename_i hci; clear hci; c0_to_group
              refine wp_join_group
                (fun _ mD => ∃ wvecD wstkD : List (BitVec 32),
                  wvecD.length = 4 * c.max_vars ∧ wstkD.length = c.wcap ∧
                  (∀ j < 2 * s.core.cur_vars,
                    (wvecD[2 * j + 1]?.getD 0#32).toNat = fullWatchSize s j) ∧
                  (∀ j < 2 * s.core.cur_vars,
                    fullWatchSize s j = 0 → (wvecD[2 * j]?.getD 0#32).toNat = 0) ∧
                  (∀ j < i.toNat + 1, let l := wsVal wsort2 j
                    let off := (wvecD[2 * l]?.getD 0#32).toNat
                    1 ≤ off ∧
                    off + fullWatchSize s l ≤ p.toNat + fullWatchSize s (wsVal wsort2 i.toNat) ∧
                    ∀ k < fullWatchSize s l, wstkD[off + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                  (∀ a < i.toNat + 1, ∀ b < i.toNat + 1, a ≠ b →
                    let la := wsVal wsort2 a; let lb := wsVal wsort2 b;
                    (wvecD[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
                      (wvecD[2 * lb]?.getD 0#32).toNat ∨
                    (wvecD[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
                      (wvecD[2 * la]?.getD 0#32).toNat) ∧
                  (∀ j, i.toNat + 1 ≤ j → j < n.toNat → let l := wsVal wsort2 j;
                    (wvecD[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧
                    ∀ k < fullWatchSize s l,
                      wstkD[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                  (FullMem c { s with core := { s.core with wvec := wvecD, wstk := wstkD },
                                      scratch := { s.scratch with wsort := wsort2 } } ⋆ R) mD)
                ?_ ?_
              · rintro _ _ mD ⟨wvecD, wstkD, hwvD, hwsD, hszD, hzeroD,
                  hdoneD, hdisjD, hremD, hmD⟩
                clear hmC hszC hzeroC hdoneC hdisjC hremC; c0_steps
                have hp_next : (p + BitVec.setWidth 64
                    (wvecC[(((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)) + 1).toNat]'
                      hlit2p1_lt)).toNat = p.toNat + fullWatchSize s (wsVal wsort2 i.toNat) := by
                  rw [BitVec.toNat_add, zext_toNat _ (by decide), hsz_i]; omega
                have hi_next : (i + 1).toNat = i.toNat + 1 := by bv_omega
                refine hLoop _ _ (by dsimp only; omega)
                  ⟨by omega, by omega, by omega, fun hlt => ?_, wvecD, wstkD, hwvD, hwsD, hszD,
                   hzeroD, by rw [hi_next, hp_next]; exact hdoneD, by rw [hi_next]; exact hdisjD,
                   by rw [hi_next]; exact hremD, hmD⟩
                rw [hp_next]
                have hgap := defrag_sorted_gap hlay hcov2 hsrt2 (i := i.toNat)
                  (j := (i + 1).toNat) (by omega) hlt
                omega
              · intro JD hJD
                clear hLoop hQ hlen hcl hsl hsz1 hoff1 hzero1 hwv1 hwsl hwvl hwsrt_l
                  hwlen_gt1 hwsl_pos hnlits
                c0_to_group
                · have hp_lt_off : p.toNat < fullWatchOff s (wsVal wsort2 i.toNat) := by
                    have hix : wsort2[i.toNat].toNat * 2 ^ 1 % 2 ^ 64 =
                        2 * wsVal wsort2 i.toNat := by simp [hlit_eq]; omega
                    have heq_w : (wvecC[wsort2[i.toNat].toNat * 2 ^ 1 % 2 ^ 64]'(by
                        rw [hix]; omega)).toNat = fullWatchOff s (wsVal wsort2 i.toNat) :=
                      (fi_list_getElem_toNat_eq (by rw [hix]; omega) hix).trans
                        (hremC i.toNat (by omega) hi_lt).1
                    have hne : p.toNat ≠ fullWatchOff s (wsVal wsort2 i.toNat) := fun he => by
                      apply hc; apply BitVec.eq_of_toNat_eq
                      rw [zext_toNat _ (by decide), heq_w, he]
                    omega
                  clear hc
                  refine wp_loop_inv
                    (fun (k, ()) mK =>
                      k.toNat ≤ fullWatchSize s (wsVal wsort2 i.toNat) ∧
                      ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
                        (∀ idx < p.toNat, wstkK[idx]? = wstkC[idx]?) ∧
                        (∀ idx, p.toNat + fullWatchSize s (wsVal wsort2 i.toNat) ≤ idx →
                          wstkK[idx]? = wstkC[idx]?) ∧
                        (∀ r < k.toNat, wstkK[p.toNat + r]? =
                          s.core.wstk[fullWatchOff s (wsVal wsort2 i.toNat) + r]?) ∧
                        (∀ r, k.toNat ≤ r → r < fullWatchSize s (wsVal wsort2 i.toNat) →
                          wstkK[fullWatchOff s (wsVal wsort2 i.toNat) + r]? =
                          s.core.wstk[fullWatchOff s (wsVal wsort2 i.toNat) + r]?) ∧
                        (FullMem c { s with core := { s.core with wvec := wvecC, wstk := wstkK },
                                            scratch := { s.scratch with wsort := wsort2 } } ⋆ R)
                          mK)
                    (fun (k, ()) _ => fullWatchSize s (wsVal wsort2 i.toNat) - k.toNat)
                    (fun JK hLoopK => ?_) ?_
                  · full_c0_steps; exact hLoopK _ _ ⟨by simp, wstkC, hwsC, fun _ _ => rfl,
                      fun _ _ => rfl, fun _ hr => by simp at hr,
                      fun r _ hr => (hremC i.toNat (by omega) hi_lt).2 r hr, hmC⟩
                  · rintro JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, wstkK, hwsK, hpreK, hpostK, hcopK, hsrcK, hmK⟩
                      hLoopK
                    clear hmC; full_c0_steps
                    · have hk_lt : k.toNat < fullWatchSize s (wsVal wsort2 i.toNat) := by
                        have hix : ((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega)) <<<
                            (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64 =
                            2 * wsVal wsort2 i.toNat + 1 := by
                          rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide),
                            Nat.shiftLeft_eq, hlit_eq]; simp; omega
                        have hsz_hc : (wvecC[((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega)) <<<
                            (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                            rw [hix]; omega)).toNat = fullWatchSize s (wsVal wsort2 i.toNat) :=
                          (fi_list_getElem_toNat_eq (by rw [hix]; omega) hix).trans
                            (hszC _ hlit_info.1)
                        have : k.toNat < (wvecC[((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega))
                            <<< (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                            rw [hix]; omega)).toNat := by c0_bound
                        omega
                      have hkp1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
                      have hpk : (p + k).toNat = p.toNat + k.toNat := by bv_omega
                      have hok_eq : (BitVec.setWidth 64
                          (wvecC[((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat]'
                            hlit2_lt) + k).toNat =
                          fullWatchOff s (wsVal wsort2 i.toNat) + k.toNat := by
                        rw [BitVec.toNat_add, zext_toNat _ (by decide), hoff_i]; omega
                      refine hLoopK _ _ (by dsimp only; omega)
                        ⟨by omega, _, by rw [List.length_set, hwsK],
                         fun idx hidx =>
                           by rw [List.getElem?_set_ne (by omega)]; exact hpreK idx hidx,
                         fun idx hidx =>
                           by rw [List.getElem?_set_ne (by omega)]; exact hpostK idx hidx,
                         fun r hr => ?_, fun r _ hr2 => by
                           rw [List.getElem?_set_ne (by omega)]; exact hsrcK r (by omega) hr2, hm⟩
                      by_cases hrk : r = k.toNat
                      · subst hrk; rw [hpk, List.getElem?_set_self (by omega),
                          ← List.getElem?_eq_getElem (by omega), hok_eq]
                        exact hsrcK k.toNat (by omega) hk_lt
                      · rw [List.getElem?_set_ne (by omega)]; exact hcopK r (by omega)
                    · have hk_eq : k.toNat = fullWatchSize s (wsVal wsort2 i.toNat) := by
                        have hix : ((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega)) <<<
                            (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64 =
                            2 * wsVal wsort2 i.toNat + 1 := by
                          rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide),
                            Nat.shiftLeft_eq, hlit_eq]; simp; omega
                        have hsz_hc : (wvecC[((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega)) <<<
                            (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                            rw [hix]; omega)).toNat = fullWatchSize s (wsVal wsort2 i.toNat) :=
                          (fi_list_getElem_toNat_eq (by rw [hix]; omega) hix).trans
                            (hszC _ hlit_info.1)
                        have : ¬ (k.toNat < (wvecC[((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega))
                            <<< (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                            rw [hix]; omega)).toNat) := by c0_bound
                        omega
                      have hp32 : (p.setWidth 32).toNat = p.toNat := by
                        rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
                      have hset := wvec_set_even_eq (wvec := wvecC) (l := wsVal wsort2 i.toNat)
                        (v := p.setWidth 32) (by omega)
                      refine hJD _ _ ⟨_, wstkK, by rw [List.length_set, hwvC], hwsK,
                        fun j hj => by rw [hlit2, (hset j).1]; exact hszC j hj,
                        fun j hj hzj => by
                          rw [hlit2]; have hne : j ≠ wsVal wsort2 i.toNat := fun heq => by
                            subst heq; have := hlit_info.2; omega
                          rw [(hset j).2.1 hne]; exact hzeroC j hj hzj,
                        ?_, ?_, ?_, hm⟩
                      · intro j hj; dsimp only
                        by_cases hji : j = i.toNat
                        · subst hji; rw [hlit2, (hset 0).2.2, Option.getD_some, hp32]
                          exact ⟨hp1, by omega, fun r hr => hcopK r (by omega)⟩
                        · have hne : wsVal wsort2 j ≠ wsVal wsort2 i.toNat :=
                            hcov2.2.1 j (by omega) i.toNat hi_lt hji
                          rw [hlit2, (hset _).2.1 hne]; have hd := hdoneC j (by omega)
                          exact ⟨hd.1, by omega, fun r hr => by
                            rw [hpreK _ (by omega)]; exact hd.2.2 r hr⟩
                      · intro a ha b hb hab; dsimp only
                        by_cases hai : a = i.toNat
                        · subst hai; have hne := hcov2.2.1 b (by omega) i.toNat hi_lt (by omega)
                          rw [hlit2, (hset 0).2.2, (hset _).2.1 hne, Option.getD_some, hp32]
                          exact Or.inr (hdoneC b (by omega)).2.1
                        · by_cases hbi : b = i.toNat
                          · subst hbi; have hne := hcov2.2.1 a (by omega) i.toNat hi_lt (by omega)
                            rw [hlit2, (hset 0).2.2, (hset _).2.1 hne, Option.getD_some, hp32]
                            exact Or.inl (hdoneC a (by omega)).2.1
                          · have hna := hcov2.2.1 a (by omega) i.toNat hi_lt hai
                            have hnb := hcov2.2.1 b (by omega) i.toNat hi_lt hbi
                            rw [hlit2, (hset _).2.1 hna, (hset _).2.1 hnb]
                            exact hdisjC a (by omega) b (by omega) hab
                      · intro j hj1 hj2; dsimp only
                        have hne := hcov2.2.1 j hj2 i.toNat hi_lt (by omega)
                        rw [hlit2, (hset _).2.1 hne]
                        have hgap := defrag_sorted_gap hlay hcov2 hsrt2 (i := i.toNat) (j := j)
                          (by omega) hj2
                        have hr := hremC j (by omega) hj2
                        exact ⟨hr.1, fun r hr' => by rw [hpostK _ (by omega)]; exact hr.2 r hr'⟩
                · have hoff_eq_p : fullWatchOff s (wsVal wsort2 i.toNat) = p.toNat := by
                    have h := congrArg BitVec.toNat hc; rw [zext_toNat _ (by decide)] at h
                    have hix : wsort2[i.toNat].toNat * 2 ^ 1 % 2 ^ 64 =
                        2 * wsVal wsort2 i.toNat := by simp [hlit_eq]; omega
                    have hget : (wvecC[wsort2[i.toNat].toNat * 2 ^ 1 % 2 ^ 64]'(by
                        rw [hix]; omega)).toNat = fullWatchOff s (wsVal wsort2 i.toNat) :=
                      (fi_list_getElem_toNat_eq (by rw [hix]; omega) hix).trans
                        (hremC i.toNat (by omega) hi_lt).1
                    exact hget.symm.trans h
                  refine hJD _ _ ⟨wvecC, wstkC, hwvC, hwsC, hszC, hzeroC, ?_, ?_,
                    fun j hj1 hj2 => hremC j (by omega) hj2, hmC⟩
                  · intro j hj; dsimp only
                    by_cases hji : j = i.toNat
                    · subst hji; have hr := hremC i.toNat (by omega) hi_lt; rw [hr.1, hoff_eq_p]
                      exact ⟨hp1, by omega, fun r hr' => by rw [← hoff_eq_p]; exact hr.2 r hr'⟩
                    · have hd := hdoneC j (by omega); exact ⟨hd.1, by omega, hd.2.2⟩
                  · intro a ha b hb hab; dsimp only
                    by_cases hai : a = i.toNat
                    · subst hai; rw [(hremC i.toNat (by omega) hi_lt).1, hoff_eq_p]
                      exact Or.inr (hdoneC b (by omega)).2.1
                    · by_cases hbi : b = i.toNat
                      · subst hbi; rw [(hremC i.toNat (by omega) hi_lt).1, hoff_eq_p]
                        exact Or.inl (hdoneC a (by omega)).2.1
                      · exact hdisjC a (by omega) b (by omega) hab
            · have hi_eq : i.toNat = n.toNat := by
                have hlt : ¬ (i.toNat < n.toNat) := by c0_bound
                omega
              full_c0_steps; rw [hi_eq] at hdoneC hdisjC
              have hfin := defrag_finalize hlay hcov2 hp1 hszC hzeroC hdoneC hdisjC
              refine hQ wvecC wstkC p.toNat wsort2 _
                ⟨{ hcl with wvec_len := hwvC, wstk_len_arr := hwsC,
                            wlen_le := by dsimp only; omega }, { hsl with wsort_len := hws2 }⟩
                hfin.1 (fun _ => hp1) hfin.2 hm
        · intro JS hJS
          clear hQ hlen hcl hsl hlay hsz1 hzero1 hwsl hwvl hwle hwsrt_l hwlen_gt1 hwsl_pos hnlits
          c0_to_group
          · have hn_gt1 : 1 < n.toNat := by c0_bound
            clear hc
            refine wp_loop_inv
              (fun (st, ()) mB => st.toNat ≤ n.toNat ∧ ∃ wsB : List (BitVec 32),
                wsB.length = 2 * c.max_vars ∧
                WsCovers wsB n.toNat (2 * s.core.cur_vars) (fullWatchSize s) ∧
                FullWsortMaxHeap wvec1 wsB st.toNat n.toNat ∧
                (FullMem c { s with core := { s.core with wvec := wvec1 },
                                    scratch := { s.scratch with wsort := wsB } } ⋆ R) mB)
              (fun (st, ()) _ => st.toNat) (fun JB hLoopB => ?_) ?_
            · c0_steps; have hshr : (n >>> (1 : Nat)).toNat = n.toNat / 2 := by
                rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]
              refine hLoopB _ _ ⟨by omega, wsort1, hws1, hcov1,
                fun _ _ _ => ⟨fun _ => by omega, fun _ => by omega⟩, hm1⟩
            · rintro JB ⟨st, ⟨⟩⟩ mB ⟨hst_le, wsB, hwsB, hcovB, hmaxB, hmB⟩ hLoopB
              clear hm1; c0_to_group
              · have hst_pos : 0 < st.toNat := by c0_bound
                have hstm1 : (st - 1).toNat = st.toNat - 1 := by bv_omega
                clear hc; c0_steps; c0_call hSift
                refine ⟨2 * s.core.cur_vars, wvec1, wsB, _, by rw [hwv1]; omega, by omega,
                  by omega, by omega, by omega, fun i hi => (hcovB.1 i hi).1,
                  by rw [hstm1, show st.toNat - 1 + 1 = st.toNat by omega]; exact hmaxB,
                  focus_wvec_wsort hmB, ?_⟩
                intro ws' m' hws' hperm' hsuf' hmax' hm'
                have hm'' := unfocus_wvec_wsort
                  (s := { s with core := { s.core with wvec := wvec1 },
                                 scratch := { s.scratch with wsort := wsB } }) hm'
                have hcov' := wsCovers_of_perm_suffix hcovB (by rw [hws']) (by omega) hperm'
                  fun i hi => hsuf' i (Or.inr hi)
                c0_steps; exact hLoopB _ _ (by dsimp only; omega)
                  ⟨by omega, ws', by rw [hws', hwsB], hcov', hmax', hm''⟩
              · have hst0 : st.toNat = 0 := by
                  have hlt : ¬ (0 < st.toNat) := by c0_bound
                  omega
                rw [hst0] at hmaxB; clear hc hLoopB JB st hst_le hst0 wsort1 hws1 hcov1
                refine wp_loop_inv
                  (fun (e, ()) mE => e.toNat < n.toNat ∧ ∃ wsE : List (BitVec 32),
                    wsE.length = 2 * c.max_vars ∧
                    WsCovers wsE n.toNat (2 * s.core.cur_vars) (fullWatchSize s) ∧
                    FullWsortMaxHeap wvec1 wsE 0 (e.toNat + 1) ∧
                    SplitLe (fullWvecOff wvec1) wsE (e.toNat + 1) n.toNat ∧
                    SortedRange (fullWvecOff wvec1) wsE (e.toNat + 1) n.toNat ∧
                    (FullMem c { s with core := { s.core with wvec := wvec1 },
                                        scratch := { s.scratch with wsort := wsE } } ⋆ R) mE)
                  (fun (e, ()) _ => e.toNat) (fun JE hLoopE => ?_) ?_
                · c0_steps; have hnm1 : (n - 1).toNat = n.toNat - 1 := by bv_omega
                  have hnm1p1 : (n - 1).toNat + 1 = n.toNat := by omega
                  refine hLoopE _ _ ⟨by omega, wsB, hwsB, hcovB, by rw [hnm1p1]; exact hmaxB,
                    fun _ _ _ _ _ => by omega, fun _ _ _ _ _ => by omega, hmB⟩
                · rintro JE ⟨e, ⟨⟩⟩ mE ⟨he_lt, wsE, hwsE, hcovE, hmaxE, hspE, hsrtE, hmE⟩ hLoopE
                  clear hmB wsB hwsB hcovB hmaxB; c0_to_group
                  · have he_pos : 0 < e.toNat := by c0_bound
                    have hem1 : (e - 1).toNat = e.toNat - 1 := by bv_omega
                    have h0_lt : 0 < wsE.length := by omega
                    have he_len : e.toNat < wsE.length := by omega
                    clear hc; c0_steps
                    have hsw_step :=
                      wsort_extract_swap_step hmaxE hspE hsrtE he_pos he_lt (by omega)
                    have hsw_cov := wsCovers_swap hcovE (i := 0) (j := e.toNat) (by omega)
                      he_lt (by omega)
                    let wsSwap := (wsE.set 0 (wsE[e.toNat]'he_len)).set e.toNat (wsE[0]'h0_lt)
                    c0_call hSift
                    refine ⟨2 * s.core.cur_vars, wvec1, wsSwap, _, by rw [hwv1]; omega,
                      by simp, by omega, by simp; exact he_pos, by simp [wsSwap, hwsE]; omega,
                      fun i hi => (hsw_cov.1 i (by omega)).1, by simp; exact hsw_step.1,
                      focus_wvec_wsort hm, ?_⟩
                    intro ws' m' hws' hperm' hsuf' hmax' hm'
                    have hm'' := unfocus_wvec_wsort
                      (s := { s with core := { s.core with wvec := wvec1 },
                                     scratch := { s.scratch with wsort := wsSwap } }) hm'
                    have hcov' := wsCovers_of_perm_suffix hsw_cov
                      (by rw [hws']) (by simp [hwsE]; omega)
                      hperm' fun i hi => hsuf' i (Or.inr (by omega))
                    have hperm_ps := wsort_extract_perm_post
                      (e := e.toNat) (n := n.toNat) (wvec := wvec1)
                      (by rw [hws']) (by omega) (by simp [wsSwap, hwsE]; omega) hperm'
                      (fun i hi => hsuf' i (Or.inr hi)) hsw_step.2.1 hsw_step.2.2
                    c0_steps; have hep : (e - 1).toNat + 1 = e.toNat := by omega
                    refine hLoopE _ _ (by dsimp only; omega)
                      ⟨by omega, ws', by simp [wsSwap, hwsE] at hws'; exact hws', hcov',
                       by rw [hep]; exact hmax',
                       by rw [hep]; exact hperm_ps.1, by rw [hep]; exact hperm_ps.2, hm''⟩
                  · have he0 : e.toNat = 0 := by
                      have hlt : ¬ (0 < e.toNat) := by c0_bound
                      omega
                    rw [he0] at hspE hsrtE
                    refine hJS _ _ ⟨wsE, hwsE, hcovE, fun i j hi hij hj => ?_, hmE⟩
                    have hkey_eq : ∀ k < n.toNat,
                        fullWvecOff wvec1 (wsVal wsE k) = fullWatchOff s (wsVal wsE k) :=
                      fun k hk => by
                        have := hcovE.1 k hk; unfold fullWvecOff fullWatchOff fullWatchOffCore
                        rw [hoff1 _ this.1 this.2]
                    rw [← hkey_eq i (by omega), ← hkey_eq j hj]
                    rcases Nat.eq_zero_or_pos i with rfl | hip
                    · rcases Nat.eq_zero_or_pos j with rfl | hjp
                      · exact Nat.le_refl _
                      · exact hspE 0 (by omega) j (by omega) hj
                    · exact hsrtE i j (by omega) hij hj
          · have hn1 : n.toNat ≤ 1 := by c0_bound
            refine hJS _ _ ⟨wsort1, hws1, hcov1, fun i j _ hij hj => ?_, hm1⟩
            have heq : i = j := by omega
            subst heq; exact Nat.le_refl _

end LeanQbe.T.Examples.Kissat.Full
