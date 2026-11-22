module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
import LeanQbe.T.Logic.C0Step
public meta import LeanQbe.T.Logic.C0Step
import all Kraken.Separation

/-!
# Kissat `D-Full` Bounded Cone SAT Sweeping — Part 1 (`Stage 4`)

Defines local `FullSweepFwdSpecs` (canonical Stage-4 invariants, `fullRngNextSpec`, and `Spec`
contracts for the 4 owned `full_sweep_*` functions in `Full.lean` #11-14 aligned with `FullSpec`),
scoped `FullSweepFwdTactics`, pure sweeping cone & `padU32B` focus helpers, and parametric
`(Γ : Env)` `Func.wp` proofs for:
1. `full_sweep_add_cl` (`full_sweep_add_cl_wp`)
2. `full_sweep_refine` (`full_sweep_refine_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

/-! ## 1. Canonical shared Stage-4 invariants and shard `Spec` contracts -/

namespace FullSweepFwdSpecs

@[expose] def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

@[expose] def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

@[expose] def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

@[expose] def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

@[expose] def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

@[expose]
def FullDenseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

/-- All entries `tarjan_mark[0 ..< cur_vars)` hold the sweep sentinel `0xFFFFFFFF#32`. -/
@[expose] def TmkClear (s : FullState) : Prop :=
  ∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0xFFFFFFFF#32

/-- Lift a cone-local literal `l < 2 * nv` back to a global literal via `work_stk1`. -/
@[expose] def coneLift (cone_v : List (BitVec 32)) (l : Nat) : Nat :=
  (cone_v[l / 2]?.getD 0#32).toNat * 2 + l % 2

/-- Global literal corresponding to local cone literal `ll < 2 * nv` (matches `FullSpec3`). -/
@[expose] def fullSweepGlobalLit (s : FullState) (ll : Nat) : Nat :=
  2 * (s.scratch.work_stk1[ll / 2]?.getD 0#32).toNat + (ll % 2)

/-- Literals of cone clause `ci` stored in `scratch_buf[off ..< off + sz)`. -/
@[expose] def sweepClauseLits (s : FullState) (ci : Nat) : List Nat :=
  let off := (s.scratch.scratch_buf[ci]?.getD 0#32).toNat
  let sz := (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat
  ((s.scratch.scratch_buf.drop off).take sz).map BitVec.toNat

/-- Structural bounds on the cone clause table in `scratch_buf[0..1024)`. -/
@[expose] def SweepBufClausesOk (s : FullState) (nv nc : Nat) : Prop :=
  nv ≤ 24 ∧ nc ≤ 64 ∧ 128 ≤ s.scratch.res_sz.toNat ∧ s.scratch.res_sz.toNat ≤ 1024 ∧
  ∀ ci < nc,
    let off := (s.scratch.scratch_buf[ci]?.getD 0#32).toNat
    let sz := (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat
    128 ≤ off ∧ off + sz ≤ s.scratch.res_sz.toNat ∧
    ∀ l ∈ sweepClauseLits s ci, l < 2 * nv

/-- Bounded local kitten-sweep cone invariant (matches `FullSpec3` + `nv ≤ s.core.cur_vars`). -/
@[expose] def FullSweepConeOk (F_cur : List (List Nat)) (s : FullState) (nv nc : Nat) : Prop :=
  nv ≤ 24 ∧ nv ≤ s.core.cur_vars ∧ nc ≤ 64 ∧
  128 ≤ s.scratch.res_sz.toNat ∧ s.scratch.res_sz.toNat ≤ 1024 ∧
  (∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
  (∀ ci < nc,
    let off := (s.scratch.scratch_buf[ci]?.getD 0#32).toNat
    let sz := (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat
    128 ≤ off ∧ off + sz ≤ s.scratch.res_sz.toNat ∧
    (∀ k < sz, (s.scratch.scratch_buf[off + k]?.getD 0#32).toNat < 2 * nv) ∧
    let glits := (List.range sz).map fun k =>
      fullSweepGlobalLit s (s.scratch.scratch_buf[off + k]?.getD 0#32).toNat
    (cnfOfClauses F_cur).EntailsClause (cnfClause glits))

/-- Semantic UNSAT postcondition of `full_sweep_dpll(h, nv, nc, a0, a1) = 20#64` (`FullSpec3`). -/
@[expose]
def FullSweepDpllUnsat (F_cur : List (List Nat)) (s : FullState) (nv a0 a1 : Nat) : Prop :=
  let ass := (if a0 < 2 * nv then [fullSweepGlobalLit s a0 ^^^ 1] else []) ++
             (if a1 < 2 * nv then [fullSweepGlobalLit s a1 ^^^ 1] else [])
  (cnfOfClauses F_cur).EntailsClause (cnfClause ass)

/-- Cone-local assumption satisfaction for `full_sweep_dpll`. -/
@[expose] def DpllAssumpSat (nv a0 a1 : Nat) (α : Nat → Bool) : Prop :=
  (a0 < 2 * nv → (cnfClause [a0]).Sat α) ∧ (a1 < 2 * nv → (cnfClause [a1]).Sat α)

/-- Cone-local subproblem satisfaction (assumptions + all cone clauses). -/
@[expose] def DpllSubprobSat (s : FullState) (nv nc a0 a1 : Nat) (α : Nat → Bool) : Prop :=
  DpllAssumpSat nv a0 a1 α ∧ ∀ ci < nc, (cnfClause (sweepClauseLits s ci)).Sat α

/-- Internal cone-extraction invariant: bijection `work_stk1[0..nv)` ↔ `tarjan_mark`, plus `F_cur`
entailment of every lifted cone clause. -/
@[expose] def SweepConeOk (F_cur : List (List Nat)) (s : FullState) (root_v nv nc : Nat) : Prop :=
  1 ≤ nv ∧ nv ≤ 24 ∧ nv ≤ s.core.cur_vars ∧ nc ≤ 64 ∧ SweepBufClausesOk s nv nc ∧
  s.scratch.work_stk1[0]?.getD 0#32 = BitVec.ofNat 32 root_v ∧
  (∀ i < nv,
    (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars ∧
    s.scratch.tarjan_mark[(s.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32 =
      BitVec.ofNat 32 i) ∧
  (∀ v < s.core.cur_vars,
    s.scratch.tarjan_mark[v]?.getD 0#32 = 0xFFFFFFFF#32 ∨
    ∃ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat = v ∧
      s.scratch.tarjan_mark[v]?.getD 0#32 = BitVec.ofNat 32 i) ∧
  (∀ ci < nc,
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((sweepClauseLits s ci).map (coneLift s.scratch.work_stk1))))

/-! ### Callee specification (`full_rng_next`) -/

@[expose] def fullRngNextSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch = { s.scratch with rng_state := s'.scratch.rng_state })

/-! ### Owned function specifications (`Full.lean` #11-14, aligned with `FullSpec3`) -/

/-- `full_sweep_add_cl` operates on `(hdrTailWords, scratch_buf, lits)` directly so both
`c.pTmp` (`max_vars ≥ sz`) and `c.pTmp` + `padU32B` (`max_vars = 1, sz = 2`) frame cleanly. -/
@[expose] def fullSweepAddClSpec : Spec [i64, i64, i32, i32] [i64] :=
  fun (h, lits, sz, nc, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (xs : List (BitVec 32)) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 1152 ≤ c.scratch_cap ∧
      128 ≤ s.scratch.res_sz.toNat ∧ s.scratch.res_sz.toNat ≤ 1024 ∧
      sz.toNat ≤ xs.length ∧
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        array (t := i32) lits xs ⋆ R) m ∧
      if 64 ≤ nc.toNat ∨ 1024 < s.scratch.res_sz.toNat + sz.toNat then
        Q (nc.setWidth 64, ()) m
      else
        ∀ scr' m',
          let lp := s.scratch.res_sz.toNat
          let s' : FullState :=
            { s with scratch :=
              { s.scratch with
                scratch_buf := scr'
                res_sz := BitVec.ofNat 64 (lp + sz.toNat) } }
          scr'.length = c.scratch_cap →
          (∀ i < c.scratch_cap, i ≠ nc.toNat → i ≠ 64 + nc.toNat →
            ¬ (lp ≤ i ∧ i < lp + sz.toNat) → scr'[i]? = s.scratch.scratch_buf[i]?) →
          scr'[nc.toNat]? = some (BitVec.ofNat 32 lp) →
          scr'[64 + nc.toNat]? = some sz →
          (∀ k < sz.toNat, scr'[lp + k]? = xs[k]?) →
          (array64 (c.hdr + 32) (hdrTailWords c s') ⋆
            array (t := i32) c.pScratchBuf scr' ⋆
            array (t := i32) lits xs ⋆ R) m' →
          Q (BitVec.ofNat 64 (nc.toNat + 1), ()) m'

@[expose] def fullSweepConeSpec : Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1152 ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ TmkClear s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r tmp' ws1' tmk' scr' rsz' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp' }
          scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk',
                                      scratch_buf := scr', res_sz := rsz' } }
      let nv := (r &&& 0xFFFF#64).toNat
      let nc := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → 1 ≤ nv → FullSweepConeOk F_cur s' nv nc →
      (ws1'[0]?.getD 0#32).toNat = root_v.toNat →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
        ∃ i < nv, (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullSweepDpllSpec : Spec [i64, i32, i32, i32, i32] [i64] :=
  fun (h, nv, nc, a0, a1, ()) m Q _ =>
    ∃ (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 1152 ≤ c.scratch_cap ∧
      FullSweepConeOk F_cur s nv.toNat nc.toNat ∧ (FullMem c s ⋆ R) m ∧
      ∀ r fuel' scr' rng' m',
        let s' : FullState :=
          { s with
            core := { s.core with fuel := fuel' }
            scratch := { s.scratch with scratch_buf := scr', rng_state := rng' } }
        s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
        (∀ i < 1024, scr'[i]? = s.scratch.scratch_buf[i]?) →
        FullSweepConeOk F_cur s' nv.toNat nc.toNat →
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → FullSweepDpllUnsat F_cur s nv.toNat a0.toNat a1.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullSweepRefineSpec : Spec [i64, i32, i32] [] := fun (h, nv, _bit_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 1152 ≤ c.scratch_cap ∧ nv.toNat ≤ 24 ∧
    nv.toNat ≤ 2 * c.max_vars ∧
    (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ sig' m', sig'.length = c.max_vars →
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' → Q () m'

end FullSweepFwdSpecs

open FullSweepFwdSpecs

/-! ## 2. Scoped tactic helpers (`FullSweepFwdTactics`, zero global leaks) -/

namespace FullSweepFwdTactics

open Lean Elab Tactic in
scoped elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let g ← g.replaceTargetDefEq ty
      setGoals [g]
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
scoped elab "c0_unmdata" : tactic => do
  let mut out := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    out := out.push (← g.replaceTargetDefEq ty)
  setGoals out.toList

open Lean Elab Tactic in
scoped elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let g' ← g.replaceTargetDefEq ty
    setGoals (g' :: (← getUnsolvedGoals).tail!)
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

section Shortcuts
open FullArenaTactics
open scoped FullArenaTactics
variable {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_full_work_stk1_0 (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using load_full_work_stk1 (i := 0) hi hm
@[scoped c0_store] theorem store_full_work_stk1_0 (v : BitVec 32)
    (hi : 0 < s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
      (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
        ⋆ R) (storeMem m i32 c.pWorkStk1 v) := by
  simpa using store_full_work_stk1 (i := 0) v hi hm
@[scoped c0_load] theorem load_full_tmp0 (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using load_full_tmp (i := 0) hi hm
@[scoped c0_store] theorem store_full_tmp0 (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using store_full_tmp (i := 0) v hi hm
@[scoped c0_store] theorem store_full_tmp1 (v : BitVec 32) (hi : 1 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4) v) := by
  simpa using store_full_tmp (i := 1) v hi hm

private theorem load_full_scr_off {base : BitVec 64} {k : Nat} {i : BitVec 64}
    (hb : base = c.pScratchBuf + BitVec.ofNat 64 (4 * k))
    (hi : k + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (base + i * 4) = some s.scratch.scratch_buf[k + i.toNat] := by
  subst hb
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat, ptr_add_ofNat,
    show 4 * k + 4 * i.toNat = 4 * (k + i.toNat) by omega]
  exact load_full_scratch_buf hi hm

private theorem store_full_scr_off {base : BitVec 64} {k : Nat} {i : BitVec 64}
    (v : BitVec 32) (hb : base = c.pScratchBuf + BitVec.ofNat 64 (4 * k))
    (hi : k + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (base + i * 4) ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set (k + i.toNat) v } } ⋆ R)
        (storeMem m i32 (base + i * 4) v) := by
  subst hb
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat, ptr_add_ofNat,
    show 4 * k + 4 * i.toNat = 4 * (k + i.toNat) by omega]
  exact store_full_scratch_buf v hi hm

@[scoped c0_load] theorem load_full_scr_val {i : BitVec 64}
    (hi : 1024 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + 4096#64 + i * 4) = some s.scratch.scratch_buf[1024 + i.toNat] :=
  load_full_scr_off (k := 1024) rfl hi hm
@[scoped c0_store] theorem store_full_scr_val {i : BitVec 64} (v : BitVec 32)
    (hi : 1024 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + 4096#64 + i * 4) ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set (1024 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + 4096#64 + i * 4) v) :=
  store_full_scr_off (k := 1024) v rfl hi hm
@[scoped c0_load] theorem load_full_scr_dv {i : BitVec 64}
    (hi : 1048 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + 4192#64 + i * 4) = some s.scratch.scratch_buf[1048 + i.toNat] :=
  load_full_scr_off (k := 1048) rfl hi hm
@[scoped c0_store] theorem store_full_scr_dv {i : BitVec 64} (v : BitVec 32)
    (hi : 1048 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + 4192#64 + i * 4) ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set (1048 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + 4192#64 + i * 4) v) :=
  store_full_scr_off (k := 1048) v rfl hi hm
@[scoped c0_load] theorem load_full_scr_dph {i : BitVec 64}
    (hi : 1072 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + 4288#64 + i * 4) = some s.scratch.scratch_buf[1072 + i.toNat] :=
  load_full_scr_off (k := 1072) rfl hi hm
@[scoped c0_store] theorem store_full_scr_dph {i : BitVec 64} (v : BitVec 32)
    (hi : 1072 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + 4288#64 + i * 4) ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set (1072 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + 4288#64 + i * 4) v) :=
  store_full_scr_off (k := 1072) v rfl hi hm
@[scoped c0_load] theorem load_full_scr_trl {i : BitVec 64}
    (hi : 1096 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + 4384#64 + i * 4) = some s.scratch.scratch_buf[1096 + i.toNat] :=
  load_full_scr_off (k := 1096) rfl hi hm
@[scoped c0_store] theorem store_full_scr_trl {i : BitVec 64} (v : BitVec 32)
    (hi : 1096 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + 4384#64 + i * 4) ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set (1096 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + 4384#64 + i * 4) v) :=
  store_full_scr_off (k := 1096) v rfl hi hm
@[scoped c0_load] theorem load_full_scr_dt {i : BitVec 64}
    (hi : 1120 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + 4480#64 + i * 4) = some s.scratch.scratch_buf[1120 + i.toNat] :=
  load_full_scr_off (k := 1120) rfl hi hm
@[scoped c0_store] theorem store_full_scr_dt {i : BitVec 64} (v : BitVec 32)
    (hi : 1120 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + 4480#64 + i * 4) ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set (1120 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + 4480#64 + i * 4) v) :=
  store_full_scr_off (k := 1120) v rfl hi hm

end Shortcuts
end FullSweepFwdTactics

section
open scoped FullArenaTactics FullSweepFwdTactics

/-! ## 3. Pure state-update, `DenseWatchSliceOk`, and sweeping semantic lemmas -/

namespace FullSweepFwdHelpers

theorem fullWitnessInv_with_tmp_flags_fuel {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (tmp' flags' : List (BitVec 32)) (fuel' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with tmp := tmp', flags := flags', fuel := fuel' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem denseWatchSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem) (hpos : 0 < rem)
    (hp : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  cases hs with
  | empty => omega
  | bin hp' _ hne hlt hent hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact ⟨hne, hlt, hent, by simpa using hrest⟩
  | occ hp' _ hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hflag hbin

theorem denseWatchSlice_step_occ {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem) (hpos : 0 < rem)
    (hp : k.wstk[p]? = some w0) (hocc : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ 3 ≤ w0.toNat ∧
    ∃ cr, k.wstk[p + 1]? = some cr ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  cases hs with
  | empty => omega
  | bin hp' hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hocc hflag
  | occ hp' hp1 _ h3 hlt href hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'
    exact ⟨by omega, h3, _, hp1, hlt, href, by simpa using hrest⟩

theorem bv8_sgt0_iff_eq1 {x : BitVec 8} (hdom : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (BitVec.slt 0#8 x = true ↔ x = 1#8) ∧ (BitVec.slt x 0#8 = true ↔ x = 0xFF#8) := by
  rcases hdom with rfl | rfl | rfl <;> decide

theorem bv32_garb_false_of_and_garb_red {hdr mask : BitVec 32}
    (h : (hdr &&& (0x00080000#32 ||| mask)) = 0#32) :
    (hdr &&& 0x00080000#32) = 0#32 := by
  ext i hi
  have hi0 := congrArg (·[i]) h
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero hi] at hi0 ⊢
  cases h19 : (0x00080000#32)[i]
  · simp
  · rw [h19, Bool.true_or, Bool.and_true] at hi0; simp [hi0]

theorem bv32_shl1_or_pol (v pol : BitVec 32) (hv : v.toNat < 2 ^ 31) (hp : pol.toNat < 2) :
    ((v <<< (1 : Nat)) ||| pol).toNat = 2 * v.toNat + pol.toNat := by
  have h1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : v.toNat * 2 < 2 ^ 32)]
    omega
  have hlt : pol.toNat = 0 ∨ pol.toNat = 1 := by omega
  rcases hlt with h0 | h1p
  · have hp0 : pol = 0#32 := BitVec.eq_of_toNat_eq h0
    rw [hp0, BitVec.or_zero, h1, show (0#32).toNat = 0 from rfl]; omega
  · have hp1 : pol = 1#32 := BitVec.eq_of_toNat_eq h1p
    rw [hp1, BitVec.toNat_or, h1, show (1#32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i; cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        show (1 : Nat) / 2 = 0 from rfl, show (2 * v.toNat) / 2 = v.toNat by omega,
        show (2 * v.toNat + 1) / 2 = v.toNat by omega, Nat.zero_testBit, Bool.or_false]

theorem bv64_pack_nv_nc {nv nc : Nat} (hnv : nv ≤ 24) (_hnc : nc ≤ 64) :
    (BitVec.ofNat 64 (nv ||| (nc <<< 16)) &&& 0xFFFF#64).setWidth 32 = BitVec.ofNat 32 nv ∧
    (BitVec.ofNat 64 (nv ||| (nc <<< 16)) >>> (16 : Nat)).setWidth 32 = BitVec.ofNat 32 nc := by
  have hlt16 : ∀ {x : Nat}, x < 2 ^ 16 → ∀ j, 16 ≤ j → x.testBit j = false := fun hx j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
  have hmask : ∀ j, Nat.testBit 65535 j = decide (j < 16) := fun j => by
    rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
      Nat.testBit_or, Nat.testBit_shiftLeft, hmask, decide_eq_true hi,
      decide_eq_true (by omega : i < 64), Bool.true_and]
    by_cases h16 : i < 16
    · simp [h16, show ¬ (16 ≤ i) by omega]
    · simp [h16, hlt16 (by omega : nv < 2 ^ 16) i (by omega)]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat,
      Nat.testBit_or, Nat.testBit_shiftLeft, decide_eq_true hi,
      decide_eq_true (by omega : 16 + i < 64), Bool.true_and,
      show 16 ≤ 16 + i by omega, decide_true, show 16 + i - 16 = i by omega,
      hlt16 (by omega : nv < 2 ^ 16) (16 + i) (by omega), Bool.false_or]

theorem nodup_length_le_of_lt : ∀ {n : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, hlt => by have := hlt x (List.mem_cons_self ..); omega
  | n + 1, xs, hnd, hlt => by
    by_cases hmem : n ∈ xs
    · have hnd' : (xs.erase n).Nodup := hnd.erase n
      have hnot : n ∉ xs.erase n := List.Nodup.not_mem_erase hnd
      have hlt' : ∀ x ∈ xs.erase n, x < n := fun x hx => by
        have h1 := hlt x (List.mem_of_mem_erase hx)
        have hne : x ≠ n := fun h => hnot (h ▸ hx)
        omega
      have ih := nodup_length_le_of_lt hnd' hlt'
      rw [List.length_erase_of_mem hmem] at ih
      have hpos : 0 < xs.length := List.length_pos_of_mem hmem
      omega
    · have ih := nodup_length_le_of_lt (n := n) hnd fun x hx => by
        have h1 := hlt x hx
        have hne : x ≠ n := fun h => hmem (h ▸ hx)
        omega
      omega

theorem level0_false_not_sat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hfalse : k.vals[l]?.getD 0#8 = 0xFF#8)
    {α : Nat → Bool} (hα : (cnfOfClauses F_cur).Sat α) : ¬ (cnfClause [l]).Sat α := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_false_iff l hlt).mp hfalse
  have hlvl0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hent := hw.level0_sound idx hidx hlvl0
  rw [htrl, CNF.entails_clause_def] at hent
  have hneg : (cnfClause [litNeg l]).Sat α := hent α hα
  simp only [sat_cnfClause_singleton, litVar_litNeg, litSign_litNeg] at hneg ⊢
  intro hsat; rw [hsat] at hneg; cases hb : litSign l <;> simp [hb] at hneg

theorem coneLift_sat_iff {cone_v : List (BitVec 32)} {α : Nat → Bool} {l : Nat} :
    (cnfClause [l]).Sat (fun i => α (cone_v[i]?.getD 0#32).toNat) ↔
      (cnfClause [coneLift cone_v l]).Sat α := by
  simp only [sat_cnfClause_singleton, coneLift, litVar, litSign]
  have hd : ((cone_v[l / 2]?.getD 0#32).toNat * 2 + l % 2) / 2 =
      (cone_v[l / 2]?.getD 0#32).toNat := by omega
  have hm : ((cone_v[l / 2]?.getD 0#32).toNat * 2 + l % 2) % 2 = l % 2 := by omega
  rw [hd, hm]

theorem coneLift_clause_sat_iff {cone_v : List (BitVec 32)} {α : Nat → Bool} {cl : List Nat} :
    (cnfClause cl).Sat (fun i => α (cone_v[i]?.getD 0#32).toNat) ↔
      (cnfClause (cl.map (coneLift cone_v))).Sat α := by
  simp only [clause_sat_cnfClause_iff, List.mem_map]
  constructor
  · rintro ⟨l, hl, hs⟩
    refine ⟨coneLift cone_v l, ⟨l, hl, rfl⟩, ?_⟩
    exact (sat_cnfClause_singleton _ _).mp
      (coneLift_sat_iff.mp ((sat_cnfClause_singleton _ _).mpr hs))
  · rintro ⟨_, ⟨l, hl, rfl⟩, hs⟩
    refine ⟨l, hl, ?_⟩
    exact (sat_cnfClause_singleton _ _).mp
      (coneLift_sat_iff.mpr ((sat_cnfClause_singleton _ _).mpr hs))

theorem sweepClauseLits_congr {s1 s2 : FullState} {ci : Nat}
    (h0 : s2.scratch.scratch_buf[ci]? = s1.scratch.scratch_buf[ci]?)
    (h64 : s2.scratch.scratch_buf[64 + ci]? = s1.scratch.scratch_buf[64 + ci]?)
    (hbd1 : (s1.scratch.scratch_buf[ci]?.getD 0#32).toNat +
      (s1.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat ≤ s1.scratch.scratch_buf.length)
    (hbd2 : (s1.scratch.scratch_buf[ci]?.getD 0#32).toNat +
      (s1.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat ≤ s2.scratch.scratch_buf.length)
    (hlits : ∀ k < (s1.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat,
      s2.scratch.scratch_buf[(s1.scratch.scratch_buf[ci]?.getD 0#32).toNat + k]? =
        s1.scratch.scratch_buf[(s1.scratch.scratch_buf[ci]?.getD 0#32).toNat + k]?) :
    sweepClauseLits s2 ci = sweepClauseLits s1 ci := by
  unfold sweepClauseLits; dsimp only; rw [h0, h64]
  generalize (s1.scratch.scratch_buf[ci]?.getD 0#32).toNat = off at hbd1 hbd2 hlits ⊢
  generalize (s1.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat = sz at hbd1 hbd2 hlits ⊢
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
  · intro j hj1 _
    simp only [List.length_map, List.length_take, List.length_drop] at hj1
    have hj : j < sz := by omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    have he := hlits j hj
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at he
    exact congrArg BitVec.toNat (Option.some.inj he)

theorem mem_sweepClauseLits_iff {s : FullState} {ci l : Nat}
    (hbd : (s.scratch.scratch_buf[ci]?.getD 0#32).toNat +
      (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat ≤ s.scratch.scratch_buf.length) :
    l ∈ sweepClauseLits s ci ↔
      ∃ (k : Nat) (_hk : k < (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat),
        (s.scratch.scratch_buf[(s.scratch.scratch_buf[ci]?.getD 0#32).toNat + k]'(by omega)).toNat
          = l := by
  unfold sweepClauseLits; dsimp only
  let off := (s.scratch.scratch_buf[ci]?.getD 0#32).toNat
  let sz := (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat
  rw [List.mem_map]; constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    have hk' : k < sz := by rw [List.length_take, List.length_drop] at hk; omega
    refine ⟨k, hk', ?_⟩; rw [List.getElem_take, List.getElem_drop] at hget
    exact congrArg BitVec.toNat hget
  · rintro ⟨k, hk, hget⟩
    refine ⟨s.scratch.scratch_buf[off + k]'(by omega), ?_, hget⟩
    have hlt : k < ((s.scratch.scratch_buf.drop off).take sz).length := by
      rw [List.length_take, List.length_drop]; omega
    simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt

theorem sweepBufClausesOk_of_prefix {s s' : FullState} {nv nc : Nat}
    (hcap : 1152 ≤ s.scratch.scratch_buf.length)
    (hcap' : s'.scratch.scratch_buf.length = s.scratch.scratch_buf.length)
    (hres : s'.scratch.res_sz = s.scratch.res_sz)
    (hpre : ∀ i < 1024, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?)
    (hok : SweepBufClausesOk s nv nc) :
    SweepBufClausesOk s' nv nc ∧ ∀ ci < nc, sweepClauseLits s' ci = sweepClauseLits s ci := by
  obtain ⟨hnv, hnc, hlo, hhi, hcl⟩ := hok
  have heq : ∀ ci < nc, sweepClauseLits s' ci = sweepClauseLits s ci := fun ci hci => by
    have hc := hcl ci hci
    exact sweepClauseLits_congr (hpre ci (by omega)) (hpre (64 + ci) (by omega))
      (by omega) (by omega) fun k hk => hpre _ (by omega)
  refine ⟨⟨hnv, hnc, hres ▸ hlo, hres ▸ hhi, fun ci hci => ?_⟩, heq⟩
  have hc := hcl ci hci
  rw [hpre ci (by omega), hpre (64 + ci) (by omega), hres, heq ci hci]; exact hc

/-! ## 4. Cone-invariant transition helpers (`push_var` & `add_cl`) -/

theorem sweepConeOk_push_var {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {root_v nv nc : Nat} {ov : BitVec 32} (hlen : s.LengthsOk c)
    (hc : SweepConeOk F_cur s root_v nv nc) (hnv24 : nv < 24)
    (hov : ov.toNat < s.core.cur_vars)
    (hmiss : s.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0xFFFFFFFF#32) :
    nv < s.core.cur_vars ∧
    let s' : FullState :=
      { s with scratch :=
        { s.scratch with
          tarjan_mark := s.scratch.tarjan_mark.set ov.toNat (BitVec.ofNat 32 nv)
          work_stk1 := s.scratch.work_stk1.set nv ov } }
    SweepConeOk F_cur s' root_v (nv + 1) nc := by
  obtain ⟨hnv1, _, _, hnc64, hbuf, hroot, hfwd, hrev, hent⟩ := hc
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hne_ov : ∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ ov.toNat := fun i hi heq => by
    have hti := (hfwd i hi).2; rw [heq, hmiss] at hti
    have htn := congrArg BitVec.toNat hti
    simp only [BitVec.toNat_ofNat] at htn; omega
  have hnv_lt : nv < s.core.cur_vars :=
    inj_lt_of_missing (fun i => (s.scratch.work_stk1[i]?.getD 0#32).toNat)
      (fun i j hi hj heq => by
        have hti := (hfwd i hi).2; have htj := (hfwd j hj).2
        rw [heq] at hti
        have htn := congrArg BitVec.toNat (hti.symm.trans htj)
        simp only [BitVec.toNat_ofNat] at htn; omega)
      (fun i hi => (hfwd i hi).1) hov hne_ov
  refine ⟨hnv_lt, ?_⟩
  intro s'
  have hwk_len : s.scratch.work_stk1.length = 2 * c.max_vars := hlen.scratch_ok.work_stk1_len
  have htmk_len : s.scratch.tarjan_mark.length = 2 * c.max_vars := hlen.scratch_ok.tarjan_mark_len
  have hwk_lt : ∀ i < nv, s'.scratch.work_stk1[i]? = s.scratch.work_stk1[i]? := fun i hi =>
    List.getElem?_set_ne (by omega)
  have hwk_nv : s'.scratch.work_stk1[nv]? = some ov := List.getElem?_set_self (by omega)
  have hbuf' : SweepBufClausesOk s' (nv + 1) nc :=
    ⟨by omega, hbuf.2.1, hbuf.2.2.1, hbuf.2.2.2.1, fun ci hci => by
      have hci_ok := hbuf.2.2.2.2 ci hci
      exact ⟨hci_ok.1, hci_ok.2.1, fun l hl => by have := hci_ok.2.2 l hl; omega⟩⟩
  refine ⟨by omega, by omega, by dsimp only [s']; omega, hnc64, hbuf', ?_, ?_, ?_, ?_⟩
  · rw [hwk_lt 0 (by omega)]; exact hroot
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [hwk_lt i hi']
      have hne := hne_ov i hi'
      refine ⟨(hfwd i hi').1, ?_⟩
      dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hne)]; exact (hfwd i hi').2
    · rw [hwk_nv, Option.getD_some]
      refine ⟨hov, ?_⟩
      dsimp only [s']; rw [List.getElem?_set_self (by omega), Option.getD_some]
  · intro v hv
    by_cases hvo : v = ov.toNat
    · subst hvo; right; refine ⟨nv, by omega, ?_, ?_⟩
      · rw [hwk_nv, Option.getD_some]
      · dsimp only [s']; rw [List.getElem?_set_self (by omega), Option.getD_some]
    · dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hvo)]
      rcases hrev v hv with hff | ⟨i, hi, hwi, hti⟩
      · exact Or.inl hff
      · exact Or.inr ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hwi, hti⟩
  · intro ci hci
    have hcl_eq : (sweepClauseLits s' ci).map (coneLift s'.scratch.work_stk1) =
        (sweepClauseLits s ci).map (coneLift s.scratch.work_stk1) := by
      change (sweepClauseLits s ci).map (coneLift s'.scratch.work_stk1) = _
      apply List.map_congr_left; intro l hl
      have hlt : l < 2 * nv := (hbuf.2.2.2.2 ci hci).2.2 l hl
      unfold coneLift; rw [hwk_lt (l / 2) (by omega)]
    rw [hcl_eq]; exact hent ci hci

theorem sweepConeOk_add_cl {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {root_v nv nc sz : Nat} {xs scr' : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hcap : 1152 ≤ c.scratch_cap)
    (hc : SweepConeOk F_cur s root_v nv nc) (hnc_lt : nc < 64)
    (hsum : s.scratch.res_sz.toNat + sz ≤ 1024) (hsz_xs : sz ≤ xs.length)
    (hlits_lt : ∀ k, (hk : k < sz) → (xs[k]'(by omega)).toNat < 2 * nv)
    (hnew_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((xs.take sz).map (fun x => coneLift s.scratch.work_stk1 x.toNat))))
    (hscr_len : scr'.length = c.scratch_cap)
    (hhold : ∀ i < c.scratch_cap, i ≠ nc → i ≠ 64 + nc →
      ¬ (s.scratch.res_sz.toNat ≤ i ∧ i < s.scratch.res_sz.toNat + sz) →
      scr'[i]? = s.scratch.scratch_buf[i]?)
    (h0 : scr'[nc]? = some (BitVec.ofNat 32 s.scratch.res_sz.toNat))
    (h64 : scr'[64 + nc]? = some (BitVec.ofNat 32 sz))
    (hcp : ∀ k < sz, scr'[s.scratch.res_sz.toNat + k]? = xs[k]?) :
    let s' : FullState :=
      { s with scratch :=
        { s.scratch with
          scratch_buf := scr'
          res_sz := BitVec.ofNat 64 (s.scratch.res_sz.toNat + sz) } }
    SweepConeOk F_cur s' root_v nv (nc + 1) := by
  intro s'
  obtain ⟨hnv1, hnv24, hnv_cv, _, hbuf, hroot, hfwd, hrev, hent⟩ := hc
  let lp := s.scratch.res_sz.toNat
  have hlp_lo : 128 ≤ lp := hbuf.2.2.1
  have hres' : s'.scratch.res_sz.toNat = lp + sz := by
    dsimp only [s', lp]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hold_lits : ∀ ci < nc, sweepClauseLits s' ci = sweepClauseLits s ci := fun ci hci => by
    have hci_ok := hbuf.2.2.2.2 ci hci
    exact sweepClauseLits_congr (hhold ci (by omega) (by omega) (by omega) (by omega))
      (hhold (64 + ci) (by omega) (by omega) (by omega) (by omega))
      (by rw [hlen.scratch_ok.scratch_buf_len]; omega) (by dsimp [s']; omega)
      fun k hk => hhold _ (by omega) (by omega) (by omega) (by omega)
  have hnew_lits : sweepClauseLits s' nc = (xs.take sz).map BitVec.toNat := by
    unfold sweepClauseLits; dsimp only [s', lp]
    rw [h0, h64, Option.getD_some, Option.getD_some, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : lp < 2 ^ 32), Nat.mod_eq_of_lt (by omega : sz < 2 ^ 32)]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    · intro j hj1 _
      simp only [List.length_map, List.length_take, List.length_drop] at hj1
      have hj : j < sz := by omega
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hcj := hcp j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hcj
      exact congrArg BitVec.toNat (Option.some.inj hcj)
  have hbuf' : SweepBufClausesOk s' nv (nc + 1) := by
    refine ⟨hnv24, by omega, by omega, by omega, fun ci hci => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hci with hci' | rfl
    · have hci_ok := hbuf.2.2.2.2 ci hci'
      have h0e := hhold ci (by omega) (by omega) (by omega) (by omega)
      have h64e := hhold (64 + ci) (by omega) (by omega) (by omega) (by omega)
      rw [show s'.scratch.scratch_buf = scr' from rfl, h0e, h64e, hres', hold_lits ci hci']
      exact ⟨hci_ok.1, by omega, hci_ok.2.2⟩
    · rw [show s'.scratch.scratch_buf = scr' from rfl, h0, h64, Option.getD_some,
        Option.getD_some, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : lp < 2 ^ 32), Nat.mod_eq_of_lt (by omega : sz < 2 ^ 32),
        hres', hnew_lits]
      refine ⟨hlp_lo, Nat.le_refl _, fun l hl => ?_⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      have hkl : k < sz := by rw [List.length_take] at hk; omega
      simpa [List.getElem_take] using hlits_lt k hkl
  refine ⟨hnv1, hnv24, hnv_cv, by omega, hbuf', hroot, hfwd, hrev, fun ci hci => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hci with hci' | rfl
  · rw [hold_lits ci hci']; exact hent ci hci'
  · rw [hnew_lits, List.map_map]; exact hnew_ent

/-! ## 5. Memory-focus helpers for `full_sweep_add_cl` & `c.max_vars = 1` `padU32B` -/

@[expose] def fullSweepAddRestTmp (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  FullCoreByteArrs c s.core ⋆
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
   array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
   array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ c.pad

theorem fullMem_focus_addCl_tmp {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆ (fullSweepAddRestTmp c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrDynArrs at hm
  unfold fullSweepAddRestTmp; ecancel

theorem fullMem_unfocus_addCl_tmp {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {res' : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 (c.hdr + 32) (hdrTailWords c
        { s with scratch := { s.scratch with scratch_buf := scr', res_sz := res' } }) ⋆
      array (t := i32) c.pScratchBuf scr' ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆ (fullSweepAddRestTmp c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr', res_sz := res' } } ⋆ R)
      m := by
  let sc' : FullScratch := { s.scratch with scratch_buf := scr', res_sz := res' }
  change (array64 (c.hdr + 32) (hdrTailWords c { core := s.core, scratch := sc' }) ⋆
    array (t := i32) c.pScratchBuf scr' ⋆
    array (t := i32) c.pTmp s.core.tmp ⋆ (fullSweepAddRestTmp c s ⋆ R)) m at hm
  have hSB : FullScrByteArrs c sc' = FullScrByteArrs c s.scratch := rfl
  have hSA : FullScrU32A c sc' = FullScrU32A c s.scratch := rfl
  have hSW : FullScrWksArrs c sc' = FullScrWksArrs c s.scratch := rfl
  have hSM : FullScrMetaArrs c sc' = FullScrMetaArrs c s.scratch := rfl
  have hd : sc'.delayed = s.scratch.delayed := rfl
  have hr : sc'.red_refs = s.scratch.red_refs := rfl
  have he : sc'.extend_stk = s.scratch.extend_stk := rfl
  have hsb : sc'.scratch_buf = scr' := rfl
  change (FullMem c { s with scratch := sc' } ⋆ R) m
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrDynArrs
  dsimp only
  rw [hSB, hSA, hSW, hSM, hd, hr, he, hsb]
  unfold fullSweepAddRestTmp at hm; ecancel

def fullPadNoTmp (c : FullCfg) : Mem 64 → Prop :=
  c.padBytes ⋆ c.padU32A ⋆
  (region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
   region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
   region (c.pMinClr + BitVec.ofNat 64 (4 * c.max_vars))
     (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
   region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.max_vars))
     (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  c.padU32C ⋆ region c.pSlack c.slack

@[expose] def fullSweepAddRestTmp1 (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  FullCoreByteArrs c s.core ⋆
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
   array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
   array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ fullPadNoTmp c

theorem fullMem_focus_tmp2_of_mv1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {w0 : BitVec 32} (hm1 : c.max_vars = 1) (ht : s.core.tmp = [w0])
    (hm : (FullMem c s ⋆ R) m) :
    ∃ w1 : BitVec 32,
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        array (t := i32) c.pTmp [w0, w1] ⋆ (fullSweepAddRestTmp1 c s ⋆ R)) m := by
  have hu : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by rw [hm1]; decide
  have h4 : BitVec.ofNat 64 (4 * 1) = 4#64 := rfl
  have hm' : (region (c.pTmp + 4#64) 4 ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        array (t := i32) c.pTmp s.core.tmp ⋆ (fullSweepAddRestTmp1 c s ⋆ R))) m := by
    unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrDynArrs
      FullCfg.pad FullCfg.padU32B at hm
    unfold fullSweepAddRestTmp1 fullPadNoTmp
    rw [hu, hm1, h4] at hm ⊢; ecancel
  obtain ⟨m1, m2, hun, hdis, hreg, hrest⟩ := hm'
  obtain ⟨xs, hxl, hxa⟩ := region_to_array_i32 (a := c.pTmp + 4#64) 1 (by decide) hreg
  rcases xs with _ | ⟨w1, _ | _⟩ <;> simp at hxl
  refine ⟨w1, ?_⟩
  have hcomb : (array (t := i32) (c.pTmp + 4#64) [w1] ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        array (t := i32) c.pTmp [w0] ⋆ (fullSweepAddRestTmp1 c s ⋆ R))) m :=
    ⟨m1, m2, hun, hdis, hxa, ht ▸ hrest⟩
  have hpair : ((array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        (array (t := i32) c.pTmp [w0] ⋆ array (t := i32) (c.pTmp + 4#64) [w1])) ⋆
      (fullSweepAddRestTmp1 c s ⋆ R)) m := by
    clear hm hreg hrest hxa; ecancel
  have hmerge : ∀ f,
      (array (t := i32) c.pTmp [w0] ⋆ array (t := i32) (c.pTmp + 4#64) [w1]) f →
      array (t := i32) c.pTmp [w0, w1] f := fun f hf => by
    have ha := congrFun (array_append (t := i32) c.pTmp [w0] [w1]) f
    simpa [Ty.bytes, Ty.size, i32] using ha.mpr hf
  exact sep_mono (fun _ => sep_mono_r hmerge) hpair

theorem fullMem_unfocus_tmp2_of_mv1 {c : FullCfg} {s : FullState}
    {w0 w1 : BitVec 32} {scr' : List (BitVec 32)} {res' : BitVec 64} {R : Mem 64 → Prop}
    {m : Mem 64} (hm1 : c.max_vars = 1)
    (hm : (array64 (c.hdr + 32) (hdrTailWords c
        { s with
          core := { s.core with tmp := [w0] }
          scratch := { s.scratch with scratch_buf := scr', res_sz := res' } }) ⋆
      array (t := i32) c.pScratchBuf scr' ⋆
      array (t := i32) c.pTmp [w0, w1] ⋆ (fullSweepAddRestTmp1 c s ⋆ R)) m) :
    (FullMem c { s with
        core := { s.core with tmp := [w0] }
        scratch := { s.scratch with scratch_buf := scr', res_sz := res' } } ⋆ R) m := by
  let k' : FullCoreState := { s.core with tmp := [w0] }
  let sc' : FullScratch := { s.scratch with scratch_buf := scr', res_sz := res' }
  change (array64 (c.hdr + 32) (hdrTailWords c { core := k', scratch := sc' }) ⋆
    array (t := i32) c.pScratchBuf scr' ⋆
    array (t := i32) c.pTmp [w0, w1] ⋆ (fullSweepAddRestTmp1 c s ⋆ R)) m at hm
  have hCB : FullCoreByteArrs c k' = FullCoreByteArrs c s.core := rfl
  have hCU : FullCoreU32B c k' = FullCoreU32B c s.core := rfl
  have hCD : FullCoreDynArrs c k' = FullCoreDynArrs c s.core := rfl
  have hSB : FullScrByteArrs c sc' = FullScrByteArrs c s.scratch := rfl
  have hSA : FullScrU32A c sc' = FullScrU32A c s.scratch := rfl
  have hSW : FullScrWksArrs c sc' = FullScrWksArrs c s.scratch := rfl
  have hSM : FullScrMetaArrs c sc' = FullScrMetaArrs c s.scratch := rfl
  have hk1 : k'.d_cur = s.core.d_cur := rfl; have hk2 : k'.d_val = s.core.d_val := rfl
  have hk3 : k'.flags = s.core.flags := rfl; have hk4 : k'.lvl = s.core.lvl := rfl
  have hk5 : k'.rsns = s.core.rsns := rfl; have hk6 : k'.trl = s.core.trl := rfl
  have hk7 : k'.trail_pos = s.core.trail_pos := rfl; have hk8 : k'.tmp = [w0] := rfl
  have hk9 : k'.min_clr = s.core.min_clr := rfl
  have hs1 : sc'.delayed = s.scratch.delayed := rfl
  have hs2 : sc'.red_refs = s.scratch.red_refs := rfl
  have hs3 : sc'.extend_stk = s.scratch.extend_stk := rfl; have hs4 : sc'.scratch_buf = scr' := rfl
  have hu : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by rw [hm1]; decide
  have h4 : BitVec.ofNat 64 (4 * 1) = 4#64 := rfl
  have hsplit : ∀ f, array (t := i32) c.pTmp [w0, w1] f →
      (array (t := i32) c.pTmp [w0] ⋆ region (c.pTmp + 4#64) 4) f := fun f hf => by
    have ha := (congrFun (array_append (t := i32) c.pTmp [w0] [w1]) f).mp hf
    simp only [List.length_singleton, Ty.bytes, Ty.size, i32, Nat.mul_one] at ha
    exact sep_mono_r (fun _ h1 => by
      simpa [Ty.bytes, Ty.size, i32] using
        array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32]) h1) ha
  have hm1' : ((array (t := i32) c.pTmp [w0] ⋆ region (c.pTmp + 4#64) 4) ⋆
      (array64 (c.hdr + 32) (hdrTailWords c { core := k', scratch := sc' }) ⋆
      array (t := i32) c.pScratchBuf scr' ⋆ (fullSweepAddRestTmp1 c s ⋆ R))) m :=
    sep_mono hsplit (by ecancel)
  clear hm
  change (FullMem c { core := k', scratch := sc' } ⋆ R) m
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrDynArrs
    FullCfg.pad FullCfg.padU32B
  dsimp only
  rw [hCB, hCU, hCD, hSB, hSA, hSW, hSM, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9,
    hs1, hs2, hs3, hs4]
  unfold fullSweepAddRestTmp1 fullPadNoTmp at hm1'
  rw [hu, hm1, h4] at hm1' ⊢; ecancel

end FullSweepFwdHelpers

open FullSweepFwdHelpers

/-! ## 6. `full_sweep_add_cl_wp` (`Full.lean` #11) -/

private theorem fullHdrTailGet_arr {c : FullCfg} {s : FullState} {F : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 140) (hm : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ F) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((hdrTailWords c s)[i]'(by simpa using hi)) := by
  have hload := loadVal_array64 (i := i) (by simpa using hi) hm
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hload

private theorem fullHdrTailPut_res_sz {c : FullCfg} {s : FullState} {F : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 64) (hm : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ F) m) :
    storeOk m i64 (c.hdr + 1144) ∧
      (array64 (c.hdr + 32) (hdrTailWords c
        { s with scratch := { s.scratch with res_sz := v } }) ⋆ F)
        (storeMem m i64 (c.hdr + 1144) v) := by
  obtain ⟨hok, hst⟩ := store_array64 (i := 139) v (by simp) hm
  rw [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * 139) = c.hdr + 1144 from
    ptr_add_ofNat c.hdr 32 (8 * 139)] at hok hst
  refine ⟨hok, ?_⟩
  have heq : hdrTailWords c { s with scratch := { s.scratch with res_sz := v } } =
      (hdrTailWords c s).set 139 v := rfl
  rw [← heq] at hst; exact hst

private theorem sep4_first {A B C D : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B ⋆ C ⋆ D) m) :
    (A ⋆ (B ⋆ C ⋆ D)) m := by ecancel
private theorem sep4_unfirst {A B C D : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ (B ⋆ C ⋆ D)) m) :
    (A ⋆ B ⋆ C ⋆ D) m := by ecancel
private theorem sep4_mid {A B C D : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B ⋆ C ⋆ D) m) :
    (B ⋆ (A ⋆ C ⋆ D)) m := by ecancel
private theorem sep4_unmid {A B C D : Mem 64 → Prop} {m : Mem 64} (h : (B ⋆ (A ⋆ C ⋆ D)) m) :
    (A ⋆ B ⋆ C ⋆ D) m := by ecancel
private theorem sep4_third {A B C D : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B ⋆ C ⋆ D) m) :
    (C ⋆ (A ⋆ B ⋆ D)) m := by ecancel

theorem full_sweep_add_cl_wp (Γ : Env) :
    ∀ args m Q X, fullSweepAddClSpec args m Q X →
      Func.wp Γ full_sweep_add_cl_body args m Q X := by
  rintro ⟨h, lits, sz, nc, ⟨⟩⟩ m Q X
    ⟨c, s, xs, R, rfl, hlen, hcap, hres_lo, hres_hi, hsz_xs, hm, hQ⟩
  have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hld_res : loadVal m i64 (c.hdr + 1144) = some s.scratch.res_sz :=
    fullHdrTailGet_arr 139 (by decide) (sep4_first hm)
  unfold Func.wp full_sweep_add_cl_body; c0_let_simp
  refine wp_load_of hld_res ?_
  have hsz32 := sz.isLt
  have hsum_eq : (s.scratch.res_sz + sz.setWidth 64).toNat =
      s.scratch.res_sz.toNat + sz.toNat := by
    rw [BitVec.toNat_add, bv32_zext64_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : sz.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.scratch.res_sz.toNat + sz.toNat < 2 ^ 64)]
  refine wp_join_group (ts := [])
    (fun () ml => ml = m ∧ (64 ≤ nc.toNat ∨ 1024 < s.scratch.res_sz.toNat + sz.toNat))
    (fun _ () ml ⟨hml, hcond⟩ => by
      subst hml; c0_let_simp; rw [ite_eq_left hcond] at hQ; exact hQ)
    (fun J_ret hJ_ret => ?_)
  c0_let_simp
  refine wp_jnz_of (fun hc1 => ?_) (fun hc1 => ?_)
  · -- Early return 1: `nc >= 64`
    simp only [Arg.val_var, BitVec.ule_eq_decide, decide_eq_true_eq] at hc1
    have h64 : (64 : BitVec 32).toNat = 64 := rfl
    c0_let_simp; exact hJ_ret () m ⟨rfl, Or.inl (by omega)⟩
  simp only [Arg.val_var, BitVec.ule_eq_decide, decide_eq_false_iff_not] at hc1
  have hnc_lt : nc.toNat < 64 := by have : (64 : BitVec 32).toNat = 64 := rfl; omega
  c0_let_simp
  refine wp_jnz_of (fun hc2 => ?_) (fun hc2 => ?_)
  · -- Early return 2: `lp + sz > 1024`
    simp only [Arg.val_var, BitVec.ult_eq_decide, decide_eq_true_eq] at hc2
    have h1024 : (1024 : BitVec 64).toNat = 1024 := rfl
    c0_let_simp; exact hJ_ret () m ⟨rfl, Or.inr (by omega)⟩
  simp only [Arg.val_var, BitVec.ult_eq_decide, decide_eq_false_iff_not] at hc2
  have hsum_le : s.scratch.res_sz.toNat + sz.toNat ≤ 1024 := by
    have : (1024 : BitVec 64).toNat = 1024 := rfl; omega
  have hnot : ¬ (64 ≤ nc.toNat ∨ 1024 < s.scratch.res_sz.toNat + sz.toNat) := by omega
  rw [ite_eq_right hnot] at hQ
  let lp := s.scratch.res_sz.toNat
  have hld_scr : loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
    fullHdrTailGet_arr 111 (by decide) (sep4_first hm)
  c0_let_simp
  refine wp_load_of hld_scr ?_
  c0_let_simp
  have haddr1 : c.pScratchBuf + nc.setWidth 64 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * nc.toNat) := by rw [bv32_mul4_eq]
  have hst1' : storeOk m i32 (c.pScratchBuf + nc.setWidth 64 * 4) ∧
      (array (t := i32) c.pScratchBuf
        (s.scratch.scratch_buf.set nc.toNat (s.scratch.res_sz.setWidth 32)) ⋆
        (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ array (t := i32) lits xs ⋆ R))
        (storeMem m i32 (c.pScratchBuf + nc.setWidth 64 * 4) (s.scratch.res_sz.setWidth 32)) := by
    rw [haddr1]
    exact store_array (t := i32) (s.scratch.res_sz.setWidth 32) (by decide) (by omega) (sep4_mid hm)
  refine wp_store_sep hst1' fun m1 hm1 => ?_
  c0_let_simp
  let scr1 := s.scratch.scratch_buf.set nc.toNat (s.scratch.res_sz.setWidth 32)
  have haddr2 : c.pScratchBuf + (64#64 + nc.setWidth 64) * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (64 + nc.toNat)) := by
    simp only [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_add_mul_ofNat,
      bv32_zext64_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : nc.toNat < 2 ^ 64)]
  have hst2' : storeOk m1 i32 (c.pScratchBuf + (64#64 + nc.setWidth 64) * 4) ∧
      (array (t := i32) c.pScratchBuf (scr1.set (64 + nc.toNat) sz) ⋆
        (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ array (t := i32) lits xs ⋆ R))
        (storeMem m1 i32 (c.pScratchBuf + (64#64 + nc.setWidth 64) * 4) sz) := by
    rw [haddr2]
    exact store_array (t := i32) sz (by decide) (by simp [scr1]; omega) hm1
  refine wp_store_sep hst2' fun m2 hm2 => ?_
  let scr2 := scr1.set (64 + nc.toNat) sz
  have hres32 : s.scratch.res_sz.setWidth 32 = BitVec.ofNat 32 lp := by
    apply BitVec.eq_of_toNat_eq; simp [lp]
  refine wp_loop_inv (ts := [i32])
    (fun (k, ()) ml => k.toNat ≤ sz.toNat ∧ ∃ scr : List (BitVec 32),
      scr.length = c.scratch_cap ∧
      (∀ i < c.scratch_cap, i ≠ nc.toNat → i ≠ 64 + nc.toNat →
        ¬ (lp ≤ i ∧ i < lp + k.toNat) → scr[i]? = s.scratch.scratch_buf[i]?) ∧
      scr[nc.toNat]? = some (BitVec.ofNat 32 lp) ∧
      scr[64 + nc.toNat]? = some sz ∧
      (∀ j < k.toNat, scr[lp + j]? = xs[j]?) ∧
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) lits xs ⋆ R) ml)
    (fun (k, ()) _ => sz.toNat - k.toNat) (fun J hJ => ?_)
    (fun J (k, ()) ml ⟨hk_le, scr, hslen, hhold, h0, h64, hcp, hml⟩ hJ => ?_)
  · c0_let_simp
    refine hJ (0#32, ()) m2 ⟨Nat.zero_le _, scr2, by simp [scr2, scr1, hscr_len], ?_, ?_, ?_,
      fun _ hj => by have : (0#32 : BitVec 32).toNat = 0 := rfl; omega, sep4_unmid hm2⟩
    · intro i hi hne1 hne2 _
      simp [scr2, scr1, List.getElem?_set_ne (Ne.symm hne2), List.getElem?_set_ne (Ne.symm hne1)]
    · simp only [scr2, scr1]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), hres32]
    · simp only [scr2]; rw [List.getElem?_set_self (by simp [scr1]; omega)]
  · c0_let_simp
    refine wp_jnz_of (fun hck => ?_) (fun hck => ?_)
    · simp only [Arg.val_var, BitVec.ult_eq_decide, decide_eq_true_eq] at hck
      have hk_lt : k.toNat < sz.toNat := hck
      have hld_x : loadVal ml i32 (lits + k.setWidth 64 * 4) = some (xs[k.toNat]'(by omega)) := by
        rw [bv32_mul4_eq]
        exact loadVal_array (t := i32) (by decide) (by omega) (sep4_third hml)
      c0_let_simp
      refine wp_load_of hld_x ?_
      have haddr_k : c.pScratchBuf + (s.scratch.res_sz + k.setWidth 64) * 4 =
          c.pScratchBuf + BitVec.ofNat 64 (4 * (lp + k.toNat)) := by
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_add_mul_ofNat,
          bv32_zext64_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k.toNat < 2 ^ 64)]
      have hst_k : storeOk ml i32 (c.pScratchBuf + (s.scratch.res_sz + k.setWidth 64) * 4) ∧
          (array (t := i32) c.pScratchBuf (scr.set (lp + k.toNat) (xs[k.toNat]'(by omega))) ⋆
            (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ array (t := i32) lits xs ⋆ R))
            (storeMem ml i32 (c.pScratchBuf + (s.scratch.res_sz + k.setWidth 64) * 4)
              (xs[k.toNat]'(by omega))) := by
        rw [haddr_k]
        exact store_array (t := i32) (xs[k.toNat]'(by omega)) (by decide) (by omega) (sep4_mid hml)
      refine wp_store_sep hst_k fun ml' hml' => ?_
      c0_let_simp
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32).toNat = 1 by rfl, Nat.mod_eq_of_lt (by omega)]
      refine hJ (k + 1#32, ()) ml' (by dsimp only; omega)
        ⟨by omega, scr.set (lp + k.toNat) (xs[k.toNat]'(by omega)),
          by simp [hslen], ?_, ?_, ?_, ?_, sep4_unmid hml'⟩
      · intro i hi hne1 hne2 hout
        rw [List.getElem?_set_ne (by omega)]
        exact hhold i hi hne1 hne2 (by omega)
      · rw [List.getElem?_set_ne (by omega)]; exact h0
      · rw [List.getElem?_set_ne (by omega)]; exact h64
      · intro j hj
        by_cases hjk : j = k.toNat
        · subst hjk
          rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
        · rw [List.getElem?_set_ne (by omega)]; exact hcp j (by omega)
    · simp only [Arg.val_var, BitVec.ult_eq_decide, decide_eq_false_iff_not] at hck
      have hk_eq : k.toNat = sz.toNat := by omega
      c0_let_simp
      have hst_res := fullHdrTailPut_res_sz (s.scratch.res_sz + sz.setWidth 64) (sep4_first hml)
      refine wp_store_sep hst_res fun ml' hml' => ?_
      c0_let_simp
      have hres_eq : s.scratch.res_sz + sz.setWidth 64 = BitVec.ofNat 64 (lp + sz.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [hsum_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lp + sz.toNat < 2 ^ 64)]
      have hnc1 : (nc + 1).setWidth 64 = BitVec.ofNat 64 (nc.toNat + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [bv32_zext64_eq, BitVec.toNat_ofNat, BitVec.toNat_add,
          show (1 : BitVec 32).toNat = 1 by rfl,
          Nat.mod_eq_of_lt (by omega : nc.toNat + 1 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : nc.toNat + 1 < 2 ^ 64),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : nc.toNat + 1 < 2 ^ 64)]
      rw [hnc1]
      refine hQ scr ml' hslen (fun i hi h1 h2 hout => hhold i hi h1 h2 (by omega)) h0 h64
        (fun j hj => hcp j (by omega)) ?_
      rw [hres_eq] at hml'; exact sep4_unfirst hml'

/-! ## 7. `full_sweep_refine_wp` (`Full.lean` #14) -/

theorem full_sweep_refine_wp (Γ : Env) :
    ∀ args m Q X, fullSweepRefineSpec args m Q X →
      Func.wp Γ full_sweep_refine_body args m Q X := by
  rintro ⟨h, nv, bit_idx, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcap, hnv24, hnv_mx, hcone, hm, hQ⟩
  unfold Func.wp full_sweep_refine_body; c0_let_simp; c0_steps
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) ml => i.toNat ≤ nv.toNat ∧ ∃ sig : List (BitVec 64),
      sig.length = c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig } } ⋆ R) ml)
    (fun (i, ()) _ => nv.toNat - i.toNat) (fun J_lp hJ_lp => ?_)
    (fun J_lp (i, ()) ml ⟨hi_le, sig, hsig_len, hml⟩ hJ_lp => ?_)
  · c0_steps; exact hJ_lp _ _ ⟨Nat.zero_le _, s.scratch.sim_sig, hlen.scratch_ok.sim_sig_len, hm⟩
  · c0_split
    · have hi_lt : i.toNat < nv.toNat := by c0_bound
      generalize hst_eq :
        ({ s with scratch := { s.scratch with sim_sig := sig } } : FullState) = st at hml
      have hwk_len : st.scratch.work_stk1.length = 2 * c.max_vars := by
        rw [← hst_eq]; exact hlen.scratch_ok.work_stk1_len
      have hscr_len : st.scratch.scratch_buf.length = c.scratch_cap := by
        rw [← hst_eq]; exact hlen.scratch_ok.scratch_buf_len
      have hsig_st : st.scratch.sim_sig.length = c.max_vars := by rw [← hst_eq]; exact hsig_len
      have hgv_lt : (st.scratch.work_stk1[i.toNat]'(by omega)).toNat < c.max_vars := by
        have hwk_s := hlen.scratch_ok.work_stk1_len
        have hg := hcone i.toNat hi_lt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hg
        have heq : st.scratch.work_stk1 = s.scratch.work_stk1 := by rw [← hst_eq]
        simp only [heq]; exact Nat.lt_of_lt_of_le hg hlen.core_ok.cur_vars_le
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32).toNat = 1 by rfl, Nat.mod_eq_of_lt (by omega)]
      c0_unmdata; c0_steps!
      all_goals
        subst hst_eq
        refine hJ_lp (i + 1#32, ()) _ (by dsimp only; omega) ⟨by omega, _, ?_, by assumption⟩
        simp [hsig_len]
    · c0_unmdata; c0_steps; exact hQ sig ml hsig_len hml

/-! ## 8. Shared helpers for `full_sweep_cone_wp` (Part 2) -/

namespace FullSweepFwdHelpers

@[expose] def coneMask (t : FullState) : FullState :=
  { core := { t.core with tmp := [] }
    scratch :=
      { t.scratch with work_stk1 := [], tarjan_mark := [], scratch_buf := [], res_sz := 0#64 } }

theorem coneMask_core_eq {s st : FullState} (h : AgreesExcept coneMask s st) :
    st.core = { s.core with tmp := st.core.tmp } := by
  have hc : ({ st.core with tmp := [] } : FullCoreState) = { s.core with tmp := [] } :=
    congrArg FullState.core h
  cases h1 : st.core; cases h2 : s.core
  rw [h1, h2] at hc; cases hc; rfl

theorem coneMask_preserves_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hag : AgreesExcept coneMask s st)
    (hw : FullWitnessInv c F0 F_cur s.core)
    (hlm : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hcl0 : s.core.cur_level = 0) :
    FullWitnessInv c F0 F_cur st.core ∧ FullLitMarksClear c st ∧ FullArenaVarsNodup st ∧
    FullExtScratchOk c st ∧ st.core.cur_level = 0 ∧ st.core.dense_mode = s.core.dense_mode ∧
    st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
    st.core.inconsistent = s.core.inconsistent ∧ st.core.oom = s.core.oom ∧
    st.core.vals = s.core.vals ∧ st.core.flags = s.core.flags ∧
    st.core.arena = s.core.arena ∧ st.core.arena_len = s.core.arena_len := by
  have hc0 := coneMask_core_eq hag
  generalize st.core.tmp = tmp' at hc0
  have hll : st.scratch.last_learned = s.scratch.last_learned := hag.get (·.scratch.last_learned)
  have hex : st.scratch.extend_len = s.scratch.extend_len := hag.get (·.scratch.extend_len)
  have hw' : FullWitnessInv c F0 F_cur st.core := by
    rw [hc0]; exact fullWitnessInv_with_tmp_flags_fuel hw tmp' s.core.flags s.core.fuel
  refine ⟨hw', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hc0]; exact hlm
  · unfold FullArenaVarsNodup; simp only [fullArenaClauseRefs, fullArenaClauseGarb,
      fullArenaClauseLits, hc0]; exact hnd
  · refine ⟨fun i hi => ?_, by simpa [hex] using hext.2⟩
    have h1 := hext.1 i hi
    dsimp only at h1 ⊢; rw [hll, fullArenaClauseRefs, hc0]; exact h1
  · rw [hc0]; exact hcl0
  all_goals rw [hc0]

theorem full_sweep_cone_init_ok {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {root_v : BitVec 32} (hlen : s.LengthsOk c) (hroot : root_v.toNat < s.core.cur_vars)
    (htmk : TmkClear s) :
    let s1 : FullState :=
      { s with scratch :=
        { s.scratch with
          res_sz := 128#64
          work_stk1 := s.scratch.work_stk1.set 0 root_v
          tarjan_mark := s.scratch.tarjan_mark.set root_v.toNat 0#32 } }
    s1.LengthsOk c ∧ AgreesExcept coneMask s s1 ∧ SweepConeOk F_cur s1 root_v.toNat 1 0 := by
  intro s1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len
  have htm_len := hlen.scratch_ok.tarjan_mark_len
  have hlen1 : s1.LengthsOk c :=
    ⟨hlen.core_ok, { hlen.scratch_ok with
      work_stk1_len := by simp [s1, hwk_len]
      tarjan_mark_len := by simp [s1, htm_len] }⟩
  have h128 : (128#64 : BitVec 64).toNat = 128 := rfl
  have hbuf : SweepBufClausesOk s1 1 0 :=
    ⟨by omega, by omega, by dsimp only [s1]; omega, by dsimp only [s1]; omega, fun _ h => by omega⟩
  refine ⟨hlen1, rfl, Nat.le_refl _, by omega, by dsimp only [s1]; omega, by omega, hbuf, ?_, ?_,
    ?_, fun _ h => by omega⟩
  · dsimp only [s1]; rw [List.getElem?_set_self (by omega), Option.getD_some, bv_ofNat_toNat_eq]
  · intro i hi; have hi0 : i = 0 := by omega
    subst hi0; dsimp only [s1]
    rw [List.getElem?_set_self (by omega), Option.getD_some,
      List.getElem?_set_self (by omega), Option.getD_some]
    exact ⟨hroot, rfl⟩
  · intro v hv; dsimp only [s1]
    by_cases hvr : v = root_v.toNat
    · subst hvr; right
      refine ⟨0, by omega, by rw [List.getElem?_set_self (by omega), Option.getD_some],
        by rw [List.getElem?_set_self (by omega), Option.getD_some]⟩
    · left; rw [List.getElem?_set_ne (Ne.symm hvr)]; exact htmk v hv

theorem full_sweep_cone_call_addCl {Γ : Env} {c : FullCfg} {F_cur : List (List Nat)}
    {s0 st : FullState} {root_v : BitVec 32} {nv nc sz : BitVec 32} {aSz : Arg Val i32}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hAddCl : ∀ args m Q X, fullSweepAddClSpec args m Q X →
      Γ "full_sweep_add_cl" [i64, i64, i32, i32] [i64] args m Q X)
    (haSz : aSz.val = sz)
    (hlen : st.LengthsOk c) (hag : AgreesExcept coneMask s0 st) (hcap : 1152 ≤ c.scratch_cap)
    (hcone : SweepConeOk F_cur st root_v.toNat nv.toNat nc.toNat)
    (hnc_lt : nc.toNat < 64) (hsz_tmp : sz.toNat ≤ st.core.tmp.length)
    (hlits_lt : ∀ j, (hj : j < sz.toNat) → (st.core.tmp[j]'(by omega)).toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st.core.tmp.take sz.toNat).map (fun x => coneLift st.scratch.work_stk1 x.toNat))))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (nc' : BitVec 64) (st' : FullState) (m' : Mem 64),
      st'.LengthsOk c → AgreesExcept coneMask s0 st' →
      SweepConeOk F_cur st' root_v.toNat nv.toNat (nc'.setWidth 32).toNat →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k (nc', ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i32, i32]) (bs := [i64]) "full_sweep_add_cl"
      (Arg.var c.hdr, Arg.var c.pTmp, aSz, Arg.var nc, ()) k) m := by
  have hbuf := hcone.2.2.2.2.1
  have hres_lo : 128 ≤ st.scratch.res_sz.toNat := hbuf.2.2.1
  have hres_hi : st.scratch.res_sz.toNat ≤ 1024 := hbuf.2.2.2.1
  refine wp_call_of_spec _ k ?_
  simp only [vals, Arg.val_var, haSz]
  refine hAddCl (c.hdr, c.pTmp, sz, nc, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, st, st.core.tmp, fullSweepAddRestTmp c st ⋆ R, rfl, hlen, hcap, hres_lo, hres_hi, hsz_tmp,
      fullMem_focus_addCl_tmp hm, ?_⟩
  by_cases hfull : 64 ≤ nc.toNat ∨ 1024 < st.scratch.res_sz.toNat + sz.toNat
  · rw [ite_eq_left hfull]
    have hnc_id : (nc.setWidth 64).setWidth 32 = nc := by apply BitVec.eq_of_toNat_eq; simp
    exact hk (nc.setWidth 64) st m hlen hag (by rw [hnc_id]; exact hcone) rfl rfl hm
  · rw [ite_eq_right hfull]
    dsimp only
    intro scr' m' hslen hhold h0 h64 hcp hm'
    have hsum : st.scratch.res_sz.toNat + sz.toNat ≤ 1024 := by omega
    have hsz32 : BitVec.ofNat 32 sz.toNat = sz := bv_ofNat_toNat_eq sz
    let st' : FullState :=
      { st with scratch :=
        { st.scratch with
          scratch_buf := scr'
          res_sz := BitVec.ofNat 64 (st.scratch.res_sz.toNat + sz.toNat) } }
    have hlen' : st'.LengthsOk c :=
      ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hslen }⟩
    have hag' : AgreesExcept coneMask s0 st' := hag.update _ (fun _ => rfl)
    have hcone' : SweepConeOk F_cur st' root_v.toNat nv.toNat (nc.toNat + 1) :=
      sweepConeOk_add_cl hlen hcap hcone hnc_lt hsum hsz_tmp hlits_lt hent hslen hhold h0
        (by rw [hsz32]; exact h64) hcp
    have hnc1 : ((BitVec.ofNat 64 (nc.toNat + 1)).setWidth 32).toNat = nc.toNat + 1 := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : nc.toNat + 1 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : nc.toNat + 1 < 2 ^ 32)]
    exact hk (BitVec.ofNat 64 (nc.toNat + 1)) st' m' hlen' hag' (by rw [hnc1]; exact hcone')
      rfl rfl (fullMem_unfocus_addCl_tmp hm')

theorem coneLift_of_tmk_pair {wk : List (BitVec 32)} {idx v l : Nat}
    (hwk : (wk[idx]?.getD 0#32).toNat = v) (hl : l / 2 = v) :
    coneLift wk (2 * idx + l % 2) = l := by
  unfold coneLift
  have hd : (2 * idx + l % 2) / 2 = idx := by omega
  have hm : (2 * idx + l % 2) % 2 = l % 2 := by omega
  rw [hd, hm, hwk]; omega

theorem fullSweepGlobalLit_eq_coneLift (s : FullState) (ll : Nat) :
    fullSweepGlobalLit s ll = coneLift s.scratch.work_stk1 ll := by
  unfold fullSweepGlobalLit coneLift; omega

theorem sweepClauseLits_eq_range {s : FullState} {ci : Nat}
    (hbound : (s.scratch.scratch_buf[ci]?.getD 0#32).toNat +
      (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat ≤ s.scratch.scratch_buf.length) :
    sweepClauseLits s ci =
      (List.range (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat).map fun k =>
        let off := (s.scratch.scratch_buf[ci]?.getD 0#32).toNat
        (s.scratch.scratch_buf[off + k]?.getD 0#32).toNat := by
  unfold sweepClauseLits
  generalize (s.scratch.scratch_buf[ci]?.getD 0#32).toNat = off at hbound ⊢
  generalize (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat = sz at hbound ⊢
  apply List.ext_getElem
  · simp [Nat.min_eq_left (by omega : sz ≤ s.scratch.scratch_buf.length - off)]
  · intro i hi1 hi2
    have hi : i < sz := by simp at hi2; exact hi2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem sweepConeOk_to_fullSweepConeOk {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {root_v nv nc : Nat} (hlen : s.LengthsOk c) (hcap : 1152 ≤ c.scratch_cap)
    (h : SweepConeOk F_cur s root_v nv nc) : FullSweepConeOk F_cur s nv nc := by
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  rcases h with ⟨_, hnv24, hnv_cv, hnc64, hbuf, _, hfwd, _, hent⟩
  have hres_hi : s.scratch.res_sz.toNat ≤ 1024 := hbuf.2.2.2.1
  refine ⟨hnv24, hnv_cv, hnc64, hbuf.2.2.1, hres_hi,
    fun i hi => (hfwd i hi).1, fun ci hci => ?_⟩
  rcases hbuf.2.2.2.2 ci hci with ⟨hoff, hsum, hlts⟩
  have heq := sweepClauseLits_eq_range (s := s) (ci := ci) (by omega)
  refine ⟨hoff, hsum, fun k hk => ?_, ?_⟩
  · apply hlts; rw [heq]; exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · have hcl := hent ci hci
    rw [heq, List.map_map] at hcl
    simpa [Function.comp_def, fullSweepGlobalLit_eq_coneLift] using hcl

theorem fullSweepConeOk_to_buf {c : FullCfg} {F_cur : List (List Nat)} {s : FullState} {nv nc : Nat}
    (hlen : s.LengthsOk c) (hcap : 1152 ≤ c.scratch_cap) (h : FullSweepConeOk F_cur s nv nc) :
    SweepBufClausesOk s nv nc := by
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  rcases h with ⟨hnv24, _, hnc64, hlo, hhi, _, hcl⟩
  refine ⟨hnv24, hnc64, hlo, hhi, fun ci hci => ?_⟩
  rcases hcl ci hci with ⟨hoff, hsum, hlts, _⟩
  refine ⟨hoff, hsum, fun l hl => ?_⟩
  rw [sweepClauseLits_eq_range (by omega)] at hl
  rcases List.mem_map.mp hl with ⟨k, hk, rfl⟩
  exact hlts k (List.mem_range.mp hk)

theorem fullSweepConeOk_of_prefix {F_cur : List (List Nat)} {s1 s2 : FullState} {nv nc : Nat}
    (h1 : FullSweepConeOk F_cur s1 nv nc)
    (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (hwk : s2.scratch.work_stk1 = s1.scratch.work_stk1)
    (hres : s2.scratch.res_sz = s1.scratch.res_sz)
    (hscr : ∀ i < 1024, s2.scratch.scratch_buf[i]? = s1.scratch.scratch_buf[i]?) :
    FullSweepConeOk F_cur s2 nv nc := by
  rcases h1 with ⟨hnv24, hnv_cv, hnc64, hlo, hhi, hvars, hcl⟩
  refine ⟨hnv24, hcv ▸ hnv_cv, hnc64, hres ▸ hlo, hres ▸ hhi,
    fun i hi => by rw [hwk, hcv]; exact hvars i hi, fun ci hci => ?_⟩
  rcases hcl ci hci with ⟨hoff, hsum, hlts, hent⟩
  have h0 : s2.scratch.scratch_buf[ci]? = s1.scratch.scratch_buf[ci]? := hscr ci (by omega)
  have h64 : s2.scratch.scratch_buf[64 + ci]? = s1.scratch.scratch_buf[64 + ci]? :=
    hscr (64 + ci) (by omega)
  dsimp only at hoff hsum hlts hent ⊢
  rw [h0, h64, hres]
  refine ⟨hoff, hsum, fun k hk => ?_, ?_⟩
  · rw [hscr _ (by omega)]; exact hlts k hk
  · let off := (s1.scratch.scratch_buf[ci]?.getD 0#32).toNat
    let sz := (s1.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat
    have hmap : ((List.range sz).map fun k =>
        fullSweepGlobalLit s2 (s2.scratch.scratch_buf[off + k]?.getD 0#32).toNat) =
        ((List.range sz).map fun k =>
          fullSweepGlobalLit s1 (s1.scratch.scratch_buf[off + k]?.getD 0#32).toNat) := by
      apply List.map_congr_left; intro k hk
      have hk' := List.mem_range.mp hk
      rw [hscr _ (by omega)]; unfold fullSweepGlobalLit; rw [hwk]
    exact hmap ▸ hent

theorem fullSweepDpllUnsat_of_not_subprob {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {nv nc a0 a1 : Nat} (hlen : s.LengthsOk c) (hcap : 1152 ≤ c.scratch_cap)
    (hcone : FullSweepConeOk F_cur s nv nc)
    (hunsat : ∀ β : Nat → Bool, ¬ DpllSubprobSat s nv nc a0 a1 β) :
    FullSweepDpllUnsat F_cur s nv a0 a1 := by
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  unfold FullSweepDpllUnsat
  rw [CNF.entails_clause_def]
  intro α hα
  exact Classical.byContradiction fun hnot => by
    let β : Nat → Bool := fun v => α (s.scratch.work_stk1[v]?.getD 0#32).toNat
    have hnot_lit : ∀ a, a < 2 * nv → ¬ (cnfClause [fullSweepGlobalLit s a ^^^ 1]).Sat α →
        (cnfClause [a]).Sat β := by
      intro a ha hna
      have hsat : (cnfClause [fullSweepGlobalLit s a]).Sat α := by
        rw [sat_cnfClause_singleton] at hna ⊢
        have hd : litVar (fullSweepGlobalLit s a ^^^ 1) = litVar (fullSweepGlobalLit s a) :=
          litVar_litNeg _
        have hs : litSign (fullSweepGlobalLit s a ^^^ 1) = !litSign (fullSweepGlobalLit s a) :=
          litSign_litNeg _
        rw [hd, hs, Bool.not_not] at hna
        cases hb : α (litVar (fullSweepGlobalLit s a)) <;>
          cases hc : litSign (fullSweepGlobalLit s a) <;> simp [hb, hc] at hna ⊢
      rw [fullSweepGlobalLit_eq_coneLift] at hsat
      exact (coneLift_sat_iff (α := α) (cone_v := s.scratch.work_stk1) (l := a)).mpr hsat
    apply hunsat β
    refine ⟨⟨fun ha0 => hnot_lit a0 ha0 fun hsat => hnot ?_,
             fun ha1 => hnot_lit a1 ha1 fun hsat => hnot ?_⟩, fun ci hci => ?_⟩
    · rw [ite_eq_left ha0, clause_sat_cnfClause_iff]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton.mpr rfl),
        (sat_cnfClause_singleton _ _).mp hsat⟩
    · rw [ite_eq_left ha1, clause_sat_cnfClause_iff]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl),
        (sat_cnfClause_singleton _ _).mp hsat⟩
    · have hres_hi : s.scratch.res_sz.toNat ≤ 1024 := hcone.2.2.2.2.1
      rcases hcone.2.2.2.2.2.2 ci hci with ⟨hoff, hsum, _, hent⟩
      rw [CNF.entails_clause_def] at hent
      have hsat := hent α hα
      have heq := sweepClauseLits_eq_range (s := s) (ci := ci) (by omega)
      rw [heq]
      let off := (s.scratch.scratch_buf[ci]?.getD 0#32).toNat
      let sz := (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat
      have hlift : ((List.range sz).map fun k =>
          fullSweepGlobalLit s (s.scratch.scratch_buf[off + k]?.getD 0#32).toNat) =
          (((List.range sz).map fun k =>
            (s.scratch.scratch_buf[off + k]?.getD 0#32).toNat).map
            (coneLift s.scratch.work_stk1)) := by
        rw [List.map_map]; apply List.map_congr_left; intro k _
        exact fullSweepGlobalLit_eq_coneLift s _
      rw [hlift] at hsat
      exact (coneLift_clause_sat_iff (α := α) (cone_v := s.scratch.work_stk1)).mpr hsat

end FullSweepFwdHelpers
end

end LeanQbe.T.Examples.Kissat.Full
