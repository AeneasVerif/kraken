module

public import LeanQbe.T.Examples.Kissat.FullDefSweep
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullCongLemmas2
public import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullSweepFwdLemmas1
public import LeanQbe.T.Examples.Kissat.FullSweepVarLemmas1
public import LeanQbe.T.Logic.C0HeadStep
public meta import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Gate Mining + Kitten Cone Sweeping Specs & Soundness (`Part 1`)

Defines:
1. Scoped `FullDefSweepTactics` (strictly scoped `c0_load`/`c0_store`/`bv_c0` and fast steppers).
2. Semantic BVE gate soundness (`FullDefGateUnsat`, `bve_gate_pg_ng_extUnsatSound`) proving
   that skipping `P_ng × N_ng` preserves `ExtUnsatSound` when `(⋀ P_g) ∧ (⋀ N_g)` is UNSAT
   relative to level-0 forced units.
3. Parameterized `Kitten` scratch model & specs (`kittenCoreClauses`, `KittenInvLaws`,
   `fullKitten{Init,AddClause,Solve,Core,Shrink,Flip}Spec`).
4. Target `Spec` contracts for all `9` functions in `FullDefSweep`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullDefSweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Scoped Tactics & BitVec/Memory Accessors (`FullDefSweepTactics`) -/

namespace FullDefSweepTactics

open FullArenaTactics FullCongTactics FullSweepVarTactics
open scoped FullArenaTactics FullCongTactics FullSweepVarTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem bv_c0_fullState_core (k : FullCoreState) (sc : FullScratch) :
    ({ core := k, scratch := sc } : FullState).core = k := rfl

@[scoped bv_c0] theorem bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped c0_load] theorem load_scr0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pScratchBuf = some s.scratch.scratch_buf[0] := by
  simpa using load_full_scratch_buf (i := 0) hi hm

@[scoped c0_store] theorem store_scr0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pScratchBuf ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set 0 v } } ⋆ R)
        (storeMem m i32 c.pScratchBuf v) := by
  simpa using store_full_scratch_buf (i := 0) v hi hm

@[scoped c0_load] theorem load_scr_imm {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {d : Nat} (hd : d % 4 = 0) (_hd64 : d < 2 ^ 64)
    (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 d) =
      some s.scratch.scratch_buf[d / 4] := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    congr 1; omega
  rw [heq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_scr_imm {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {d : Nat} (v : BitVec 32) (hd : d % 4 = 0) (_hd64 : d < 2 ^ 64)
    (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 d) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (d / 4) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 d) v) := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    congr 1; omega
  rw [heq]; exact store_full_scratch_buf v hi hm

@[scoped c0_load] theorem load_k_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {d : Nat} (hd : d % 4 = 0) (_hd64 : 1024 + d < 2 ^ 64)
    (hi : 256 + d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + 1024#64) + BitVec.ofNat 64 d) =
      some s.scratch.scratch_buf[256 + d / 4] := by
  have heq : (c.pScratchBuf + 1024#64) + BitVec.ofNat 64 d =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (256 + d / 4)) := by
    rw [BitVec.add_assoc]; congr 1
    rw [show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, ← BitVec.ofNat_add,
      show 1024 + d = 4 * (256 + d / 4) by omega]
  rw [heq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_k_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {d : Nat} (v : BitVec 32) (hd : d % 4 = 0) (_hd64 : 1024 + d < 2 ^ 64)
    (hi : 256 + d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + 1024#64) + BitVec.ofNat 64 d) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (256 + d / 4) v } } ⋆ R)
        (storeMem m i32 ((c.pScratchBuf + 1024#64) + BitVec.ofNat 64 d) v) := by
  have heq : (c.pScratchBuf + 1024#64) + BitVec.ofNat 64 d =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (256 + d / 4)) := by
    rw [BitVec.add_assoc]; congr 1
    rw [show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, ← BitVec.ofNat_add,
      show 1024 + d = 4 * (256 + d / 4) by omega]
  rw [heq]; exact store_full_scratch_buf v hi hm

@[scoped c0_load] theorem load_k_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 256 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + 1024#64) = some s.scratch.scratch_buf[256] := by
  simpa using load_k_off (d := 0) (by decide) (by decide) (by simpa using hi) hm

@[scoped c0_store] theorem store_k_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 256 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + 1024#64) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set 256 v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + 1024#64) v) := by
  simpa using store_k_off (d := 0) v (by decide) (by decide) (by simpa using hi) hm

@[scoped c0_load] theorem load_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem store_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using store_full_tmp (i := 0) v hi hm

@[scoped c0_load] theorem load_ws1_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using load_full_work_stk1 (i := 0) hi hm

@[scoped c0_store] theorem store_ws1_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk1 := s.scratch.work_stk1.set 0 v } } ⋆ R)
        (storeMem m i32 c.pWorkStk1 v) := by
  simpa using store_full_work_stk1 (i := 0) v hi hm

@[scoped c0_load] theorem load_k_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : 256 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + 1024#64) + i * 4) =
      some s.scratch.scratch_buf[256 + i.toNat] := by
  have heq : (c.pScratchBuf + 1024#64) + i * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (256 + i.toNat)) := by
    have hmul : i * 4 = BitVec.ofNat 64 (i.toNat * 4) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
    rw [BitVec.add_assoc]; congr 1
    rw [hmul, show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, ← BitVec.ofNat_add,
      show 1024 + i.toNat * 4 = 4 * (256 + i.toNat) by omega]
  rw [heq]; exact load_full_scratch_buf hi hm

@[scoped c0_load] theorem load_k_dyn_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {base : Nat} {i : BitVec 64}
    (hb : base % 4 = 0) (hi : 256 + base / 4 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (((c.pScratchBuf + 1024#64) + i * 4) + BitVec.ofNat 64 base) =
      some s.scratch.scratch_buf[256 + base / 4 + i.toNat] := by
  have heq : ((c.pScratchBuf + 1024#64) + i * 4) + BitVec.ofNat 64 base =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (256 + base / 4 + i.toNat)) := by
    have hmul : i * 4 = BitVec.ofNat 64 (i.toNat * 4) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1
    rw [hmul, show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      show 1024 + (i.toNat * 4 + base) = 4 * (256 + base / 4 + i.toNat) by omega]
  rw [heq]; exact load_full_scratch_buf hi hm

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "ds_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)

scoped macro "ds_steps" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      (repeat ds_strip)
      c0_hsteps!
      repeat (any_goals (ds_strip; repeat ds_strip); c0_hsteps!)))

scoped macro "ds_steps_soft" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      (repeat ds_strip)
      c0_hsteps
      repeat (any_goals (ds_strip; repeat ds_strip); c0_hsteps)))

scoped macro "ds_split" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      (repeat ds_strip)
      c0_hsplit))

scoped macro "ds_to_group" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      (repeat ds_strip)
      c0_hsteps_nogrp))

scoped macro "ds_csteps!" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_steps!))

end FullDefSweepTactics

/-! ## 2. Canonical Stage-4 Predicates, `TmkZero`, & Semantic Gate Soundness -/

section CanonicalAliases

abbrev EnvSpec (Γ : Env) (name : Sym) {as rs : List Ty} (S : Spec as rs) : Prop :=
  ∀ xs m Q X, S xs m Q X → Γ name as rs xs m Q X

abbrev FullLitMarksClear := FullSweepVarSpecs.FullLitMarksClear
abbrev FullArenaVarsNodup := FullSweepVarSpecs.FullArenaVarsNodup
abbrev FullExtScratchOk := FullSweepVarSpecs.FullExtScratchOk
abbrev FullSparseInv := FullSweepVarSpecs.FullSparseInv
abbrev FullDenseInv := FullSweepVarSpecs.FullDenseInv
abbrev FullDenseInvW := FullSweepVarSpecs.FullDenseInvW
abbrev FullBveEntryOkW := Full.FullBveEntryOkW

/-- Zero-initialized `tarjan_mark[0 ..< cur_vars)` used by `full_find_definition`,
`full_sweep_cone`, `full_sweep_var`, and `full_sweep_dense`. -/
@[expose] def TmkZero (s : FullState) : Prop :=
  ∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0#32

theorem TmkZero.congr {s s' : FullState} (h : TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (ht : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : TmkZero s' := by
  intro v hv; rw [ht]; exact h v (hcv ▸ hv)

end CanonicalAliases

/-! ### BVE gate-restricted resolution equisatisfiability (`P_ng × N_ng` skipping) -/

/-- Rest literals of an occurrence entry `w` after stripping `except`. -/
@[expose] def bveOccRestLits (s : FullState) (except : Nat) (w : BitVec 32) : List Nat :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    [(w &&& 0x7FFFFFFF#32).toNat]
  else
    (fullArenaClauseLits s w.toNat).filter (· != except)

/-- Unit clauses `[l ^^^ 1]` forced at level 0 in `s.core.vals`. -/
@[expose] def level0ForcedUnits (s : FullState) : List (List Nat) :=
  (List.range (2 * s.core.cur_vars)).filterMap fun l =>
    if s.core.vals[l]?.getD 0#8 = 0xFF#8 then some [l ^^^ 1] else none

/-- Subset of occurrence clauses selected by `mask` in `scr[off ..< off + cnt)`. -/
@[expose] def maskedOccRestCls (s : FullState) (except off cnt : Nat) (mask : BitVec 64) :
    List (List Nat) :=
  (List.range cnt).filterMap fun i =>
    if (mask >>> i) &&& 1#64 ≠ 0#64 then
      some (bveOccRestLits s except (s.scratch.scratch_buf[off + i]?.getD 0#32))
    else none

/-- Semantic definition/gate soundness certificate: the selected positive gate bodies
`P_g`, negative gate bodies `N_g`, and level-0 forced units in `s.core.vals` are jointly
unsatisfiable. -/
@[expose] def FullDefGateUnsat (s : FullState) (v : Nat) (pmask nmask : BitVec 64) (np nn : Nat) :
    Prop :=
  np ≤ 64 ∧ nn ≤ 64 ∧ (pmask ≠ 0#64 ∨ nmask ≠ 0#64) →
  (pmask >>> np) = 0#64 ∧ (nmask >>> nn) = 0#64 ∧
  (cnfOfClauses (level0ForcedUnits s ++
    maskedOccRestCls s (2 * v) 0 np pmask ++
    maskedOccRestCls s (2 * v + 1) 64 nn nmask)).Unsat

theorem level0ForcedUnits_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0) :
    ∀ cl ∈ level0ForcedUnits s, (cnfOfClauses F_cur).EntailsClause (cnfClause cl) := by
  intro cl hcl
  unfold level0ForcedUnits at hcl
  rw [List.mem_filterMap] at hcl
  obtain ⟨l, hl, hite⟩ := hcl
  rw [List.mem_range] at hl
  split at hite
  · rename_i hf
    cases Option.some.inj hite
    obtain ⟨idx, hidx, htrl⟩ := (hw.vals_false_iff l hl).mp hf
    have hl0 : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le idx hidx; omega
    have hs := hw.level0_sound idx hidx hl0
    rwa [htrl] at hs
  · cases hite

private theorem eval_clause_no_v {v : Nat} {cl : List Nat} (α : Nat → Bool) (b : Bool)
    (hnov : ∀ l ∈ cl, l / 2 ≠ v) :
    (cnfClause cl).Sat (fun x => if x = v then b else α x) ↔ (cnfClause cl).Sat α := by
  simp only [clause_sat_cnfClause_iff, litVar, litSign]
  constructor <;> rintro ⟨l, hl, hsat⟩ <;> refine ⟨l, hl, ?_⟩
  · have hne : l / 2 ≠ v := hnov l hl
    simpa [hne] using hsat
  · have hne : l / 2 ≠ v := hnov l hl
    simpa [hne]

/-- Pure SAT soundness for gate-restricted BVE (`(P_g × N) ∪ (P_ng × N_g)`, skipping
`P_ng × N_ng`): if `U` holds under `α` (`F_cur` units entailed by `Rest`) and `(U ++ P_g ++ N_g)`
is unsatisfiable, then every model of `Rest` plus resolved clauses extends to `Rest ++ P ++ N`. -/
theorem bve_gate_pg_ng_sat_extend (v : Nat) (Rest U P N : List (List Nat))
    (pg ng : Nat → Bool) (α : Nat → Bool)
    (hRestNoV : ∀ cl ∈ Rest, ∀ l ∈ cl, l / 2 ≠ v)
    (hPNoV : ∀ cl ∈ P, ∀ l ∈ cl, l / 2 ≠ v)
    (hNNoV : ∀ cl ∈ N, ∀ l ∈ cl, l / 2 ≠ v)
    (hU : ∀ cl ∈ U, (cnfClause cl).Sat α)
    (hRestSat : (cnfOfClauses Rest).Sat α)
    (hResSat : ∀ i j (hi : i < P.length) (hj : j < N.length),
      (pg i = true ∨ ng j = true) → (cnfClause (P[i]'hi ++ N[j]'hj)).Sat α)
    (hGateUnsat : (cnfOfClauses (U ++
      ((List.range P.length).filterMap fun i =>
        if pg i then some (P[i]?.getD []) else none) ++
      ((List.range N.length).filterMap fun j =>
        if ng j then some (N[j]?.getD []) else none))).Unsat) :
    ∃ b : Bool,
      (cnfOfClauses (Rest ++ P.map (fun C => (2 * v) :: C) ++
        N.map (fun D => (2 * v + 1) :: D))).Sat (fun x => if x = v then b else α x) := by
  let evalWith (b : Bool) : Nat → Bool := fun x => if x = v then b else α x
  have hPosSat : (cnfOfClauses (N.map fun D => (2 * v + 1) :: D)).Sat (evalWith false) := by
    rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
    rw [List.mem_map] at hcl; obtain ⟨D, _, rfl⟩ := hcl
    rw [clause_sat_cnfClause_iff]
    refine ⟨2 * v + 1, List.mem_cons_self .., ?_⟩
    simp only [litVar, litSign, evalWith]
    have hd : (2 * v + 1) / 2 = v := by omega
    have hm : (2 * v + 1) % 2 = 1 := by omega
    simp [hd, hm]
  have hNegSat : (cnfOfClauses (P.map fun C => (2 * v) :: C)).Sat (evalWith true) := by
    rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
    rw [List.mem_map] at hcl; obtain ⟨C, _, rfl⟩ := hcl
    rw [clause_sat_cnfClause_iff]
    refine ⟨2 * v, List.mem_cons_self .., ?_⟩
    simp only [litVar, litSign, evalWith]
    have hd : (2 * v) / 2 = v := by omega
    have hm : (2 * v) % 2 = 0 := by omega
    simp [hd, hm]
  have hRestPres : ∀ b, (cnfOfClauses Rest).Sat (evalWith b) := fun b => by
    rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
    exact (eval_clause_no_v α b (hRestNoV cl hcl)).mpr
      ((cnf_sat_cnfOfClauses_iff α Rest).mp hRestSat cl hcl)
  by_cases hP : ∀ i (hi : i < P.length), (cnfClause (P[i]'hi)).Sat α
  · refine ⟨false, ?_⟩
    rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
    simp only [List.mem_append, List.mem_map] at hcl
    rcases hcl with (hc | ⟨C, hC, rfl⟩) | ⟨D, hD, rfl⟩
    · exact (cnf_sat_cnfOfClauses_iff (evalWith false) Rest).mp (hRestPres false) cl hc
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hC
      have hs := (eval_clause_no_v α false (hPNoV _ hC)).mpr (hP i hi)
      rw [clause_sat_cnfClause_iff] at hs ⊢
      obtain ⟨l, hl, hsl⟩ := hs; exact ⟨l, List.mem_cons_of_mem _ hl, hsl⟩
    · exact (cnf_sat_cnfOfClauses_iff (evalWith false) _).mp hPosSat _ (List.mem_map_of_mem hD)
  · by_cases hN : ∀ j (hj : j < N.length), (cnfClause (N[j]'hj)).Sat α
    · refine ⟨true, ?_⟩
      rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
      simp only [List.mem_append, List.mem_map] at hcl
      rcases hcl with (hc | ⟨C, hC, rfl⟩) | ⟨D, hD, rfl⟩
      · exact (cnf_sat_cnfOfClauses_iff (evalWith true) Rest).mp (hRestPres true) cl hc
      · exact (cnf_sat_cnfOfClauses_iff (evalWith true) _).mp hNegSat _ (List.mem_map_of_mem hC)
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hD
        have hs := (eval_clause_no_v α true (hNNoV _ hD)).mpr (hN j hj)
        rw [clause_sat_cnfClause_iff] at hs ⊢
        obtain ⟨l, hl, hsl⟩ := hs; exact ⟨l, List.mem_cons_of_mem _ hl, hsl⟩
    · exfalso
      have hP' : ∃ i, ∃ hi : i < P.length, ¬ (cnfClause (P[i]'hi)).Sat α :=
        Classical.byContradiction fun hn => hP fun i hi =>
          Classical.byContradiction fun hni => hn ⟨i, hi, hni⟩
      have hN' : ∃ j, ∃ hj : j < N.length, ¬ (cnfClause (N[j]'hj)).Sat α :=
        Classical.byContradiction fun hn => hN fun j hj =>
          Classical.byContradiction fun hnj => hn ⟨j, hj, hnj⟩
      obtain ⟨i0, hi0, hni0⟩ := hP'
      obtain ⟨j0, hj0, hnj0⟩ := hN'
      have hpg0 : pg i0 = false := by
        cases hpg : pg i0
        · rfl
        · exfalso; apply hN; intro j hj
          have hs := hResSat i0 j hi0 hj (Or.inl hpg)
          rw [clause_sat_cnfClause_iff] at hs ⊢
          obtain ⟨l, hl, hsl⟩ := hs
          rw [List.mem_append] at hl
          exact hl.elim (fun h1 => absurd ((clause_sat_cnfClause_iff α _).mpr ⟨l, h1, hsl⟩) hni0)
            (fun h2 => ⟨l, h2, hsl⟩)
      have hng0 : ng j0 = false := by
        cases hng : ng j0
        · rfl
        · exfalso; apply hP; intro i hi
          have hs := hResSat i j0 hi hj0 (Or.inr hng)
          rw [clause_sat_cnfClause_iff] at hs ⊢
          obtain ⟨l, hl, hsl⟩ := hs
          rw [List.mem_append] at hl
          exact hl.elim (fun h1 => ⟨l, h1, hsl⟩)
            (fun h2 => absurd ((clause_sat_cnfClause_iff α _).mpr ⟨l, h2, hsl⟩) hnj0)
      rw [CNF.unsat_iff_not_sat] at hGateUnsat
      apply hGateUnsat α
      rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
      simp only [List.mem_append, List.mem_filterMap, List.mem_range] at hcl
      rcases hcl with (huc | ⟨i, ⟨hi, hite⟩⟩) | ⟨j, ⟨hj, hite⟩⟩
      · exact hU cl huc
      · split at hite
        · rename_i hpgi
          cases Option.some.inj hite
          have hs := hResSat i j0 hi hj0 (Or.inl hpgi)
          rw [List.getElem?_eq_getElem hi, Option.getD_some]
          rw [clause_sat_cnfClause_iff] at hs ⊢
          obtain ⟨l, hl, hsl⟩ := hs; rw [List.mem_append] at hl
          exact hl.elim (fun h1 => ⟨l, h1, hsl⟩)
            (fun h2 => absurd ((clause_sat_cnfClause_iff α _).mpr ⟨l, h2, hsl⟩) hnj0)
        · cases hite
      · split at hite
        · rename_i hngj
          cases Option.some.inj hite
          have hs := hResSat i0 j hi0 hj (Or.inr hngj)
          rw [List.getElem?_eq_getElem hj, Option.getD_some]
          rw [clause_sat_cnfClause_iff] at hs ⊢
          obtain ⟨l, hl, hsl⟩ := hs; rw [List.mem_append] at hl
          exact hl.elim (fun h1 => absurd ((clause_sat_cnfClause_iff α _).mpr ⟨l, h1, hsl⟩) hni0)
            (fun h2 => ⟨l, h2, hsl⟩)
        · cases hite

private theorem bve_pg_ng_forward_sat {v : Nat} {Rest P N : List (List Nat)} {pg ng : Nat → Bool}
    {α : Nat → Bool}
    (hSat : (cnfOfClauses (Rest ++ P.map (fun C => (2 * v) :: C) ++
      N.map (fun D => (2 * v + 1) :: D))).Sat α) :
    let Res := ((List.range P.length).flatMap fun i =>
      (List.range N.length).filterMap fun j =>
        if pg i || ng j then some (P[i]?.getD [] ++ N[j]?.getD []) else none)
    (cnfOfClauses (Rest ++ Res)).Sat α := by
  intro Res; rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
  simp only [List.mem_append] at hcl
  rcases hcl with hc | hr
  · exact (cnf_sat_cnfOfClauses_iff α _).mp hSat _
      (List.mem_append_left _ (List.mem_append_left _ hc))
  · simp only [Res, List.mem_flatMap, List.mem_range, List.mem_filterMap] at hr
    obtain ⟨i, hi, j, hj, hite⟩ := hr
    split at hite <;> cases hite
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some, Option.getD_some]
    have hPos := (cnf_sat_cnfOfClauses_iff α _).mp hSat _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem hi))))
    have hNeg := (cnf_sat_cnfOfClauses_iff α _).mp hSat _
      (List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem hj)))
    rw [clause_sat_cnfClause_iff] at hPos hNeg ⊢
    obtain ⟨lp, hlp, hsp⟩ := hPos
    obtain ⟨ln, hln, hsn⟩ := hNeg
    rcases List.mem_cons.mp hlp with rfl | hlp'
    · rcases List.mem_cons.mp hln with rfl | hln'
      · exfalso
        simp only [litVar, litSign] at hsp hsn
        have hdv0 : (2 * v) / 2 = v := by omega
        have hdv1 : (2 * v + 1) / 2 = v := by omega
        have hm0 : (2 * v) % 2 = 0 := by omega
        have hm1 : (2 * v + 1) % 2 = 1 := by omega
        rw [hdv0, hm0] at hsp; rw [hdv1, hm1] at hsn
        cases hb : α v <;> simp [hb] at hsp hsn
      · exact ⟨ln, List.mem_append_right _ hln', hsn⟩
    · exact ⟨lp, List.mem_append_left _ hlp', hsp⟩

/-- Full semantic equisatisfiability for gate-restricted BVE skipping `P_ng × N_ng`. -/
theorem bve_gate_pg_ng_unsat_iff {v : Nat} {Rest U P N : List (List Nat)} {pg ng : Nat → Bool}
    (hRestNoV : ∀ cl ∈ Rest, ∀ l ∈ cl, l / 2 ≠ v)
    (hPNoV : ∀ cl ∈ P, ∀ l ∈ cl, l / 2 ≠ v)
    (hNNoV : ∀ cl ∈ N, ∀ l ∈ cl, l / 2 ≠ v)
    (hUEnt : ∀ cl ∈ U, (cnfOfClauses Rest).EntailsClause (cnfClause cl))
    (hGateUnsat : (cnfOfClauses (U ++
      ((List.range P.length).filterMap fun i =>
        if pg i then some (P[i]?.getD []) else none) ++
      ((List.range N.length).filterMap fun j =>
        if ng j then some (N[j]?.getD []) else none))).Unsat) :
    let Res := ((List.range P.length).flatMap fun i =>
      (List.range N.length).filterMap fun j =>
        if pg i || ng j then some (P[i]?.getD [] ++ N[j]?.getD []) else none)
    (cnfOfClauses (Rest ++ P.map (fun C => (2 * v) :: C) ++
      N.map (fun D => (2 * v + 1) :: D))).Unsat ↔
      (cnfOfClauses (Rest ++ Res)).Unsat := by
  intro Res; constructor <;> intro hU
  · rw [CNF.unsat_iff_not_sat] at hU ⊢; intro α hSat
    have hRestSat : (cnfOfClauses Rest).Sat α := by
      rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
      exact (cnf_sat_cnfOfClauses_iff α _).mp hSat cl (List.mem_append_left _ hcl)
    have hUSat : ∀ cl ∈ U, (cnfClause cl).Sat α := fun cl hcl =>
      (CNF.entails_clause_def.mp (hUEnt cl hcl)) α hRestSat
    have hResSat : ∀ i j (hi : i < P.length) (hj : j < N.length),
        (pg i = true ∨ ng j = true) → (cnfClause (P[i]'hi ++ N[j]'hj)).Sat α := by
      intro i j hi hj hor
      have hmem : P[i]'hi ++ N[j]'hj ∈ Res := by
        simp only [Res, List.mem_flatMap, List.mem_range, List.mem_filterMap]
        refine ⟨i, hi, j, hj, ?_⟩
        have hbt : (pg i || ng j) = true := by rcases hor with h | h <;> simp [h]
        simp [hbt, hi, hj]
      exact (cnf_sat_cnfOfClauses_iff α _).mp hSat _ (List.mem_append_right _ hmem)
    obtain ⟨b, hb⟩ := bve_gate_pg_ng_sat_extend v Rest U P N pg ng α
      hRestNoV hPNoV hNNoV hUSat hRestSat hResSat hGateUnsat
    exact hU _ hb
  · rw [CNF.unsat_iff_not_sat] at hU ⊢; intro α hSat
    exact hU α (bve_pg_ng_forward_sat hSat)

/-- Full `ExtUnsatSound` preservation for gate-restricted BVE skipping `P_ng × N_ng`. -/
theorem bve_gate_pg_ng_extUnsatSound {F0 : CNF Nat} {cur_vars v : Nat}
    {Rest P N : List (List Nat)} {pg ng : Nat → Bool}
    (hExt : ExtUnsatSound F0 cur_vars (Rest ++ P.map (fun C => (2 * v) :: C) ++
      N.map (fun D => (2 * v + 1) :: D))) :
    let Res := ((List.range P.length).flatMap fun i =>
      (List.range N.length).filterMap fun j =>
        if pg i || ng j then some (P[i]?.getD [] ++ N[j]?.getD []) else none)
    ExtUnsatSound F0 cur_vars (Rest ++ Res) := by
  intro Res
  refine ⟨fun cl hcl l hl => ?_, fun hUnsat => hExt.2 ?_⟩
  · simp only [List.mem_append] at hcl
    rcases hcl with hc | hr
    · exact hExt.1 cl (List.mem_append_left _ (List.mem_append_left _ hc)) l hl
    · simp only [Res, List.mem_flatMap, List.mem_range, List.mem_filterMap] at hr
      obtain ⟨i, hi, j, hj, hite⟩ := hr
      split at hite <;> cases hite
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        Option.getD_some, Option.getD_some, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact hExt.1 ((2 * v) :: P[i]'hi)
          (List.mem_append_left _ (List.mem_append_right _
            (List.mem_map_of_mem (List.getElem_mem hi))))
          l (List.mem_cons_of_mem _ hl1)
      · exact hExt.1 ((2 * v + 1) :: N[j]'hj)
          (List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem hj)))
          l (List.mem_cons_of_mem _ hl2)
  · rw [CNF.unsat_iff_not_sat] at hUnsat ⊢; intro α hSat
    exact hUnsat α (bve_pg_ng_forward_sat hSat)

theorem fullDefGateUnsat_zero (s : FullState) (v np nn : Nat) :
    FullDefGateUnsat s v 0#64 0#64 np nn := by
  rintro ⟨_, _, h⟩; exact absurd h (by simp)

/-! ## 3. Parameterized `Kitten` Scratch Model & `EnvSpec`s -/

/-- Original clauses selected into the UNSAT core (`(KO_CL_META[ci] & KM_CORE) ≠ 0`). -/
@[expose] def kittenCoreClauses (cls : List (Nat × List Nat)) (scr : List (BitVec 32)) :
    List (Nat × List Nat) :=
  (List.range cls.length).filterMap fun ci =>
    if (scr[256 + 6816 + ci]?.getD 0#32 &&& 0x10000#32) ≠ 0#32 then cls[ci]? else none

theorem kittenCoreClauses_mem {cls : List (Nat × List Nat)} {scr : List (BitVec 32)}
    {x : Nat × List Nat} (hx : x ∈ kittenCoreClauses cls scr) : x ∈ cls := by
  unfold kittenCoreClauses at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨ci, _, hite⟩ := hx
  split at hite
  · exact List.mem_of_getElem? hite
  · cases hite

theorem kittenCoreClauses_length_le (cls : List (Nat × List Nat)) (scr : List (BitVec 32)) :
    (kittenCoreClauses cls scr).length ≤ cls.length := by
  unfold kittenCoreClauses
  exact Nat.le_trans (List.length_filterMap_le ..) (by rw [List.length_range]; exact Nat.le_refl _)

/-- Assumption unit clauses active in `k[KO_ASSUMP ..< KO_ASSUMP + k[KH_NASSUMP])`. -/
@[expose] def kittenAssumpClauses (scr : List (BitVec 32)) : List (List Nat) :=
  (List.range (scr[256 + 18]?.getD 0#32).toNat).map fun i =>
    [(scr[256 + 1184 + i]?.getD 0#32).toNat]

/-- Phase state of the `kitten` scratch workspace: `fresh` (after `init`, `add_clause`, or
`shrink`, ready to add clauses or `solve`), `solved` (post-`solve`/`flip` or assumptions
modified), or `unsatReady` (`solve = 20#64` with `ta = true`, `nassump = 0`, ready for `core`). -/
inductive KittenPhase where
  | fresh
  | solved
  | unsatReady
  deriving DecidableEq

/-- Minimal structural laws required of any `Kitten` scratch invariant `KInv`. -/
structure KittenInvLaws
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop) :
    Prop where
  cap_ok : ∀ {nv cls ta ph scr}, KInv nv cls ta ph scr →
    10240 ≤ scr.length ∧ 1 ≤ nv ∧ nv ≤ 128 ∧ cls.length ≤ 512
  orig_nc_eq : ∀ {nv cls ta ph scr}, KInv nv cls ta ph scr →
    (scr[256 + 2]?.getD 0#32).toNat = cls.length
  cl_aux_eq : ∀ {nv cls ta ph scr}, KInv nv cls ta ph scr →
    ∀ (i : Nat) (hi : i < cls.length), (scr[256 + 7712 + i]?.getD 0#32).toNat = (cls[i]'hi).1
  lits_lt : ∀ {nv cls ta ph scr}, KInv nv cls ta ph scr →
    ∀ c ∈ cls, ∀ l ∈ c.2, l < 2 * nv
  nassump_ok : ∀ {nv cls ta ph scr}, KInv nv cls ta ph scr →
    (scr[256 + 18]?.getD 0#32).toNat ≤ 2 ∧
    ∀ i < (scr[256 + 18]?.getD 0#32).toNat, (scr[256 + 1184 + i]?.getD 0#32).toNat < 2 * nv
  set_nv : ∀ {nv nv' cls ta scr}, KInv nv cls ta .fresh scr →
    1 ≤ nv' → nv' ≤ nv → (scr[256 + 18]?.getD 0#32).toNat = 0 →
    (∀ c ∈ cls, ∀ l ∈ c.2, l < 2 * nv') →
    KInv nv' cls ta .fresh
      ((scr.set 256 (BitVec.ofNat 32 nv')).set 262 (BitVec.ofNat 32 nv'))
  set_assumps : ∀ {nv cls ph scr scr'}, KInv nv cls false ph scr →
    scr'.length = scr.length →
    (∀ i, i ≠ 256 + 18 → i ≠ 256 + 1184 → i ≠ 256 + 1185 → scr'[i]? = scr[i]?) →
    (scr'[256 + 18]?.getD 0#32).toNat ≤ 2 →
    (∀ i < (scr'[256 + 18]?.getD 0#32).toNat, (scr'[256 + 1184 + i]?.getD 0#32).toNat < 2 * nv) →
    KInv nv cls false .solved scr'

@[expose] def fullKittenInitSpec
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop) :
    Spec [i64, i32, i32] [] := fun (h, nv, ta, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 10240 ≤ c.scratch_cap ∧
    1 ≤ nv.toNat ∧ nv.toNat ≤ 128 ∧ (FullMem c s ⋆ R) m ∧
    ∀ scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < 256, scr'[i]? = s.scratch.scratch_buf[i]?) →
      scr'[256 + 18]? = some 0#32 →
      KInv nv.toNat [] (ta ≠ 0#32) .fresh scr' →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullKittenAddClauseSpec
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop) :
    Spec [i64, i32, i64, i32] [.bool] := fun (h, eid, lits_ptr, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (nv : Nat) (cls : List (Nat × List Nat)) (ta : Bool)
    (xs : List (BitVec 32)) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 10240 ≤ c.scratch_cap ∧
    KInv nv cls ta .fresh s.scratch.scratch_buf ∧
    1 ≤ sz.toNat ∧ sz.toNat < 2 ^ 16 ∧ sz.toNat ≤ xs.length ∧
    (∀ k < sz.toNat, (xs[k]?.getD 0#32).toNat < 2 * nv) ∧
    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      array (t := i32) lits_ptr xs ⋆ R) m ∧
    ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < 256, scr'[i]? = s.scratch.scratch_buf[i]?) →
      scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? →
      (ok = true →
        KInv nv (cls ++ [(eid.toNat, (xs.take sz.toNat).map BitVec.toNat)]) ta .fresh scr') →
      (ok = false → KInv nv cls ta .fresh scr') →
      (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆
        array (t := i32) c.pScratchBuf scr' ⋆
        array (t := i32) lits_ptr xs ⋆ R) m' →
      Q (ok, ()) m'

@[expose] def fullKittenSolveSpec
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop) :
    Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (nv : Nat) (cls : List (Nat × List Nat))
    (ta : Bool) (ph : KittenPhase) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 10240 ≤ c.scratch_cap ∧
    KInv nv cls ta ph s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
    ∀ r fuel' scr' m',
      let s' : FullState :=
        { s with
          core := { s.core with fuel := fuel' }
          scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < 256, scr'[i]? = s.scratch.scratch_buf[i]?) →
      scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? →
      KInv nv cls ta (if decide (r = 20#64) && ta &&
        decide ((s.scratch.scratch_buf[256 + 18]?.getD 0#32).toNat = 0)
        then .unsatReady else .solved) scr' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 →
        (cnfOfClauses (cls.map Prod.snd ++ kittenAssumpClauses s.scratch.scratch_buf)).Unsat) →
      (r ≠ 20#64 → ∀ i < cls.length,
        (scr'[256 + 6816 + i]?.getD 0#32 &&& 0x10000#32) =
          (s.scratch.scratch_buf[256 + 6816 + i]?.getD 0#32 &&& 0x10000#32)) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullKittenCoreSpec
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop) :
    Spec [i64] [i32] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (nv : Nat) (cls : List (Nat × List Nat))
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 10240 ≤ c.scratch_cap ∧
    KInv nv cls true .unsatReady s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
    ∀ red scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < 256, scr'[i]? = s.scratch.scratch_buf[i]?) →
      scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? →
      KInv nv cls true .unsatReady scr' →
      (cnfOfClauses ((kittenCoreClauses cls scr').map Prod.snd)).Unsat →
      (FullMem c s' ⋆ R) m' → Q (red, ()) m'

@[expose] def fullKittenShrinkSpec
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop) :
    Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (nv : Nat) (cls : List (Nat × List Nat))
    (ta : Bool) (ph : KittenPhase) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 10240 ≤ c.scratch_cap ∧
    KInv nv cls ta ph s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
    ∀ scr' m',
      let cls' := kittenCoreClauses cls s.scratch.scratch_buf
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < 256, scr'[i]? = s.scratch.scratch_buf[i]?) →
      scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? →
      KInv nv cls' ta .fresh scr' →
      (∀ i < cls'.length, (scr'[256 + 6816 + i]?.getD 0#32 &&& 0x10000#32) = 0#32) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullKittenFlipSpec
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop) :
    Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (nv : Nat) (cls : List (Nat × List Nat))
    (ta : Bool) (ph : KittenPhase) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 10240 ≤ c.scratch_cap ∧
    KInv nv cls ta ph s.scratch.scratch_buf ∧ lit.toNat < 2 * nv ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < 256, scr'[i]? = s.scratch.scratch_buf[i]?) →
      scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? →
      KInv nv cls ta .solved scr' →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ## 4. Target `Spec` Contracts (`9` fns) & Canonical Bridges -/

@[expose] def fullBveMarkAndDefSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, v_lit, cr, n_off, nn, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      n_off.toNat + nn.toNat ≤ c.scratch_cap ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (v_lit.toNat ^^^ 1)
        (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with
            core := { s.core with lit_mark := lm' }
            scratch := { s.scratch with scratch_buf := scr' } }
        let nmask :=
          (scr'[130]?.getD 0#32).setWidth 64 ||| ((scr'[131]?.getD 0#32).setWidth 64 <<< 32)
        FullDenseInvW c F0 F_cur s' →
        (∀ i < c.scratch_cap, i ≠ 130 → i ≠ 131 → scr'[i]? = s.scratch.scratch_buf[i]?) →
        (ok = false →
          scr'[130]? = s.scratch.scratch_buf[130]? ∧ scr'[131]? = s.scratch.scratch_buf[131]?) →
        (ok = true → nn.toNat ≤ 64 →
          (nmask >>> nn.toNat) = 0#64 ∧
          (cnfOfClauses ([(fullArenaClauseLits s cr.toNat).filter (· != v_lit.toNat)] ++
            maskedOccRestCls s (v_lit.toNat ^^^ 1) n_off.toNat nn.toNat nmask)).Unsat) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveMarkAndDefSpec_to_base {args m Q X} (h : fullBveMarkAndSpec args m Q X) :
    fullBveMarkAndDefSpec args m Q X := by
  rcases args with ⟨h_ptr, v_lit, cr, n_off, nn, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, s, R, rfl, hdw, h132, hcr, hng, hnd, hok, hm, hQ⟩
  exact ⟨c, F0, F_cur, s, R, rfl, hdw, h132, hcr, hng, hnd, hok, hm,
    fun ok lm' scr' m' hdw' hpre _ _ hm' => hQ ok lm' scr' m' hdw' hpre hm'⟩

@[expose]
def fullFindDefinitionSpec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧ TmkZero s ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 64 ∧ nn.toNat ≤ 64 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[64 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      let scr' := s'.scratch.scratch_buf
      let pmask :=
        (scr'[128]?.getD 0#32).setWidth 64 ||| ((scr'[129]?.getD 0#32).setWidth 64 <<< 32)
      let nmask :=
        (scr'[130]?.getD 0#32).setWidth 64 ||| ((scr'[131]?.getD 0#32).setWidth 64 <<< 32)
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.vals = s.core.vals →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < c.scratch_cap, i < 128 ∨ (132 ≤ i ∧ (i < 256 ∨ c.scratch_cap < 10240)) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      ((∀ i ∈ [128, 129, 130, 131], scr'[i]? = s.scratch.scratch_buf[i]?) ∨
        FullDefGateUnsat s v.toNat pmask nmask np.toNat nn.toNat) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullBveGatesDefSpec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧ TmkZero s ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 64 ∧ nn.toNat ≤ 64 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[64 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      let scr' := s'.scratch.scratch_buf
      let pmask :=
        (scr'[128]?.getD 0#32).setWidth 64 ||| ((scr'[129]?.getD 0#32).setWidth 64 <<< 32)
      let nmask :=
        (scr'[130]?.getD 0#32).setWidth 64 ||| ((scr'[131]?.getD 0#32).setWidth 64 <<< 32)
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.vals = s.core.vals →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < c.scratch_cap, i < 128 ∨ (132 ≤ i ∧ (i < 256 ∨ c.scratch_cap < 10240)) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      FullDefGateUnsat s v.toNat pmask nmask np.toNat nn.toNat →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose]
def fullCongExtractTickSpec : Spec [i64, i64, i64] [i64] := fun (h, g_cap, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
    g_cap.toNat ≤ c.scratch_cap ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      ret.toNat ≤ g_cap.toNat →
      FullCongSpecs.GateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

@[expose] def fullCongruenceDenseSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' →
      s'.core.fuel = s.core.fuel →
      (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullSweepKittenConeOk (F_cur : List (List Nat)) (s : FullState)
    (cls : List (Nat × List Nat)) (nv nc : Nat) : Prop :=
  1 ≤ nv ∧ nv ≤ 128 ∧ nv ≤ s.core.cur_vars ∧ nc = cls.length ∧ cls.length ≤ 512 ∧
  (∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
  ∀ c ∈ cls,
    (∀ l ∈ c.2, l < 2 * nv) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause (c.2.map (fullSweepGlobalLit s)))

@[expose] def fullSweepConeKittenSpec
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop) :
    Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 10240 ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r tmp' ws1' tmk' scr' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp' }
          scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk',
                                      scratch_buf := scr' } }
      let nv := (r &&& 0xFFFF#64).toNat
      let nc := (r >>> 16).toNat
      ∀ cls' : List (Nat × List Nat),
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.vals = s.core.vals → s'.core.inconsistent = s.core.inconsistent →
        fullSweepKittenConeOk F_cur s' cls' nv nc →
        KInv nv cls' false .fresh scr' →
        (ws1'[0]?.getD 0#32).toNat = root_v.toNat →
        (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
          ∃ i < nv, (ws1'[i]?.getD 0#32).toNat = v) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose]
def fullSweepRefineKittenSpec : Spec [i64, i32, i32] [] := fun (h, nv, _bit_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 10240 ≤ c.scratch_cap ∧
    nv.toNat ≤ 128 ∧ nv.toNat ≤ 2 * c.max_vars ∧
    (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ sig' m', sig'.length = c.max_vars →
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' → Q () m'

@[expose]
def fullSweepVarKittenSpec : Spec [i64, i32, i64] [i64] := fun (h, root_v, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 10240 ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      TmkZero s' →
      (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose]
def fullSweepDenseSpec : Spec [i64, i64, i64] [i64] := fun (h, _budget, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem gateAt_to_full {F_cur : List (List Nat)} {cur_vars : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (hg : FullCongSpecs.GateAt F_cur cur_vars scr g_len g) :
    FullCongGateAt F_cur cur_vars scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hac, ha8, hrhs, hsem⟩ := hg
  exact ⟨lhs, mword, h0, h1, hlhs, hbd, hac, ha8, hrhs, hsem⟩

theorem gateSeqOk_to_full {F_cur : List (List Nat)} {cur_vars : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (hs : FullCongSpecs.GateSeqOk F_cur cur_vars scr g_len g) :
    FullCongGateSeqOk F_cur cur_vars scr g_len g := by
  induction hs with
  | done => exact .done
  | step hg _ ih => exact .step (gateAt_to_full hg) ih


/-! ## 5. Shared BitVec, Clause & Cone Helpers (Extracted from Parts 2 & 4) -/

section FullDefSweepSharedHelpers

open FullCongSpecs FullCongHelpers
open FullSweepFwdHelpers FullSweepVarHelpers

theorem nat_xor1_cancel (x : Nat) : (x ^^^ 1) ^^^ 1 = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]


theorem bv64_mask_split_32 (x : BitVec 64) :
    (x.setWidth 32).setWidth 64 ||| (((x >>> 32).setWidth 32).setWidth 64 <<< 32) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h32 : i < 32
  · simp [h32]
  · have hlt : i - 32 < 32 := by omega
    have hlt64 : i - 32 < 64 := by omega
    have hm : ¬ (i < 32) := h32
    simp [hm, hlt, hlt64, show 32 + (i - 32) = i by omega]


private theorem bv64_shl_testBit_self {k : Nat} (hk : k < 64) :
    (((1#64 : BitVec 64) <<< k) >>> k) &&& 1#64 ≠ 0#64 := by
  have hk0 : ((((1#64 : BitVec 64) <<< k) >>> k) &&& 1#64).getLsbD 0 = true := by
    simp [hk]
  intro h; rw [h] at hk0; simp at hk0

theorem bv64_or_shl_testBit_self (m : BitVec 64) {k : Nat} (hk : k < 64) :
    (((m ||| (1#64 <<< k)) >>> k) &&& 1#64) ≠ 0#64 := by
  have hk0 : ((((m ||| (1#64 <<< k)) >>> k) &&& 1#64)).getLsbD 0 = true := by
    simp [hk]
  intro h; rw [h] at hk0; simp at hk0

private theorem bv64_shl_testBit_ne {i k : Nat} (hne : k ≠ i) :
    (((1#64 : BitVec 64) <<< i) >>> k) &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro b _
  cases b with
  | zero =>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_one, BitVec.getLsbD_zero, Nat.add_zero]
    by_cases hk : k < 64
    · by_cases hlt : k < i
      · simp [hk, hlt]
      · simp [hk, show ¬ (k < i) by omega, show k - i ≠ 0 by omega]
    · simp [hk]
  | succ _ => simp [BitVec.getLsbD_and, BitVec.getLsbD_one]

theorem bv64_or_bit_pres_other {m : BitVec 64} {j k : Nat} (hk : k < 64)
    (hprev : (m >>> k) &&& 1#64 ≠ 0#64) :
    ((m ||| (1#64 <<< j)) >>> k) &&& 1#64 ≠ 0#64 := by
  intro h; apply hprev
  apply BitVec.eq_of_getLsbD_eq; intro b _
  have h2 := congrArg (·.getLsbD b) h
  cases b with
  | zero =>
    simp [hk] at h2 ⊢
    exact h2.1
  | succ _ => simp [BitVec.getLsbD_and, BitVec.getLsbD_one]


theorem maskedOccRestCls_mem {s : FullState} {except off cnt : Nat} {mask : BitVec 64}
    {k : Nat} (hk : k < cnt) (hbit : (mask >>> k) &&& 1#64 ≠ 0#64) :
    bveOccRestLits s except (s.scratch.scratch_buf[off + k]?.getD 0#32) ∈
      maskedOccRestCls s except off cnt mask := by
  unfold maskedOccRestCls
  rw [List.mem_filterMap]
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  simp [hbit]


theorem bv32_shr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_lit_shl_or (v l : BitVec 32) (hv : v.toNat < 2 ^ 30) :
    ((v <<< (1 : Nat)) ||| (l &&& 1#32)).toNat = 2 * v.toNat + l.toNat % 2 := by
  have h1 : (l &&& 1#32).toNat = l.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  exact (FullSweepFwdHelpers.bv32_shl1_or_pol v (l &&& 1#32) (by omega) (by omega)).trans
    (by rw [h1])

private theorem filterMap_single_bit {α : Type} {f : Nat → α} {i : Nat} (hi : i < 64) :
    ∀ m ≤ 64,
      (List.range m).filterMap (fun k =>
        if (((1#64 : BitVec 64) <<< i) >>> k) &&& 1#64 ≠ 0#64 then some (f k) else none) =
      if i < m then [f i] else []
  | 0, _ => by simp
  | m + 1, hm => by
    have ih := filterMap_single_bit (f := f) hi m (by omega)
    rw [List.range_succ, List.filterMap_append, ih]
    by_cases hmi : m = i
    · subst hmi
      have hs := bv64_shl_testBit_self hi
      simp [hs]
    · have hz := bv64_shl_testBit_ne hmi
      simp only [List.filterMap_cons, hz, ne_eq, not_true_eq_false, ↓reduceIte, List.filterMap_nil,
        List.append_nil]
      split <;> split <;> first | rfl | omega

theorem maskedOccRestCls_single_bit {s : FullState} {except off n i : Nat}
    (hi : i < n) (hn : n ≤ 64) :
    maskedOccRestCls s except off n (1#64 <<< i) =
      [bveOccRestLits s except (s.scratch.scratch_buf[off + i]?.getD 0#32)] := by
  unfold maskedOccRestCls
  have h := filterMap_single_bit
    (f := fun k => bveOccRestLits s except (s.scratch.scratch_buf[off + k]?.getD 0#32))
    (by omega : i < 64) n hn
  simpa [hi] using h

theorem fullDefGateUnsat_of_unsat {s : FullState} {v : Nat} {pmask nmask : BitVec 64}
    {np nn : Nat}
    (hpm : np ≤ 64 → pmask >>> np = 0#64)
    (hnm : nn ≤ 64 → nmask >>> nn = 0#64)
    (hu : (cnfOfClauses (level0ForcedUnits s ++
      maskedOccRestCls s (2 * v) 0 np pmask ++
      maskedOccRestCls s (2 * v + 1) 64 nn nmask)).Unsat) :
    FullDefGateUnsat s v pmask nmask np nn := by
  rintro ⟨hnp, hnn, _⟩
  exact ⟨hpm hnp, hnm hnn, hu⟩

theorem unsat_of_subclauses {cs1 cs2 : List (List Nat)}
    (hsub : ∀ cl ∈ cs1, cl ∈ cs2) (hu : (cnfOfClauses cs1).Unsat) :
    (cnfOfClauses cs2).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hSat; apply hu α
  rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
  exact (cnf_sat_cnfOfClauses_iff α _).mp hSat cl (hsub cl hcl)

theorem range_filterMap_congr {α : Type} {n : Nat} {f g : Nat → Option α}
    (h : ∀ i < n, f i = g i) : (List.range n).filterMap f = (List.range n).filterMap g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.filterMap_append, List.filterMap_append,
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    congr 1; simp only [List.filterMap_cons, List.filterMap_nil, h k (Nat.lt_succ_self k)]

theorem maskedOccRestCls_congr {s1 s2 : FullState} {except off cnt : Nat}
    {mask : BitVec 64} (har : s2.core.arena = s1.core.arena)
    (hbd : off + cnt ≤ 128)
    (hscr : ∀ i < 128, s2.scratch.scratch_buf[i]? = s1.scratch.scratch_buf[i]?) :
    maskedOccRestCls s2 except off cnt mask = maskedOccRestCls s1 except off cnt mask := by
  unfold maskedOccRestCls; apply range_filterMap_congr; intro i hi
  split
  · congr 1
    simp only [bveOccRestLits, fullArenaClauseLits, fullArenaClauseLitsCore,
      fullArenaClauseSizeCore, har, hscr (off + i) (by omega)]
  · rfl

theorem fullDefGateUnsat_congr {s1 s2 : FullState} {v : Nat} {pmask nmask : BitVec 64}
    {np nn : Nat} (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (hvals : s2.core.vals = s1.core.vals) (har : s2.core.arena = s1.core.arena)
    (hscr : ∀ i < 128, s2.scratch.scratch_buf[i]? = s1.scratch.scratch_buf[i]?)
    (h : FullDefGateUnsat s2 v pmask nmask np nn) :
    FullDefGateUnsat s1 v pmask nmask np nn := by
  intro hp
  have ⟨h1, h2, h3⟩ := h hp
  have huf : level0ForcedUnits s2 = level0ForcedUnits s1 := by
    unfold level0ForcedUnits; rw [hcv, hvals]
  have hm1 := maskedOccRestCls_congr (s1 := s1) (s2 := s2) (except := 2 * v)
    (off := 0) (cnt := np) (mask := pmask) har (by omega) hscr
  have hm2 := maskedOccRestCls_congr (s1 := s1) (s2 := s2) (except := 2 * v + 1)
    (off := 64) (cnt := nn) (mask := nmask) har (by omega) hscr
  rw [huf, hm1, hm2] at h3
  exact ⟨h1, h2, h3⟩

theorem fullBveEntryOkW_congr {F_cur : List (List Nat)} {s1 s2 : FullState} {l : Nat}
    {w : BitVec 32} (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (_hvals : s2.core.vals = s1.core.vals) (har : s2.core.arena = s1.core.arena)
    (hal : s2.core.arena_len = s1.core.arena_len) :
    FullBveEntryOkW F_cur s1 l w ↔ FullBveEntryOkW F_cur s2 l w := by
  unfold FullDefSweep.FullBveEntryOkW Full.FullBveEntryOkW
    fullArenaClauseRefs fullArenaClauseRefsCore
    fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
  rw [hcv, har, hal]

theorem unsat_of_unit_pair {l : Nat} : (cnfOfClauses [[l], [l ^^^ 1]]).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hSat
  have h1 := (cnf_sat_cnfOfClauses_iff α _).mp hSat [l] List.mem_cons_self
  have h2 := (cnf_sat_cnfOfClauses_iff α _).mp hSat [l ^^^ 1]
    (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [clause_sat_cnfClause_iff] at h1 h2
  obtain ⟨l1, hl1, hs1⟩ := h1
  obtain ⟨l2, hl2, hs2⟩ := h2
  rcases List.mem_singleton.mp hl1 with rfl
  rcases List.mem_singleton.mp hl2 with rfl
  have hxor_if : l1 ^^^ 1 = if l1 % 2 = 0 then l1 + 1 else l1 - 1 := by
    apply Nat.eq_of_testBit_eq; intro k
    cases k with
    | zero =>
      rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one l1 with h | h
      · simp [h, show (l1 + 1) % 2 = 1 by omega]
      · simp [h, show (l1 - 1) % 2 = 0 by omega]
    | succ k =>
      rw [Nat.testBit_xor, Nat.testBit_succ, show (1 : Nat).testBit (k + 1) = false by
        rw [Nat.testBit_succ]; simp]
      rcases Nat.mod_two_eq_zero_or_one l1 with h | h
      · simp [h, Nat.testBit_succ, show (l1 + 1) / 2 = l1 / 2 by omega]
      · simp [h, Nat.testBit_succ, show (l1 - 1) / 2 = l1 / 2 by omega]
  have hev := evalLitVal_litNeg α l1
  rw [litNeg_eq, ← hxor_if] at hev
  dsimp only [evalLitVal] at hev
  rw [hs1, hs2] at hev
  cases hbs1 : litSign l1 <;> cases hbs2 : litSign (l1 ^^^ 1) <;> simp_all

theorem list_set_eq_self_of_getElem? {α : Type} {xs : List α} {i : Nat} {v : α}
    (h : xs[i]? = some v) : xs.set i v = xs := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.mp h).1
  have hv : xs[i]'hi = v := (List.getElem?_eq_some_iff.mp h).2
  apply List.ext_getElem (by simp)
  intro j hj1 _
  by_cases hji : j = i
  · subst hji; rw [List.getElem_set_self (by simpa using hj1), ← hv]
  · rw [List.getElem_set_ne (Ne.symm hji)]



theorem dsSweep_ptr_k_256_eq (p i : BitVec 64) :
    (p + BitVec.ofNat 64 256 * 4) + i * 4 = p + BitVec.ofNat 64 (4 * (256 + i.toNat)) := by
  have hmul : i * 4 = BitVec.ofNat 64 (i.toNat * 4) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
  rw [BitVec.add_assoc]; congr 1
  rw [hmul, show (BitVec.ofNat 64 256 * 4 : BitVec 64) = BitVec.ofNat 64 1024 from rfl,
    ← BitVec.ofNat_add, show 1024 + i.toNat * 4 = 4 * (256 + i.toNat) by omega]

namespace FullDefSweepTactics

open FullArenaTactics FullSweepVarTactics

@[scoped c0_load] theorem load_k_256_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : 256 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 256 * 4 + i * 4) =
      some s.scratch.scratch_buf[256 + i.toNat] := by
  rw [dsSweep_ptr_k_256_eq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_k_256_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 256 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 256 * 4 + i * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (256 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 256 * 4 + i * 4) v) := by
  rw [dsSweep_ptr_k_256_eq]; exact store_full_scratch_buf v hi hm

@[scoped bv_c0] theorem bv32_shl1_mod32 (x : BitVec 32) :
    x <<< ((1#32 : BitVec 32).toNat % 32) = x <<< (1 : Nat) := rfl

end FullDefSweepTactics

theorem fullSweepGlobalLit_eq_coneLift' (s : FullState) :
    fullSweepGlobalLit s = FullSweepFwdSpecs.coneLift s.scratch.work_stk1 := by
  funext ll; unfold fullSweepGlobalLit FullSweepFwdSpecs.coneLift; omega

theorem dsSweep_bv32_add1_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega



end FullDefSweepSharedHelpers

end LeanQbe.T.Examples.Kissat.FullDefSweep
