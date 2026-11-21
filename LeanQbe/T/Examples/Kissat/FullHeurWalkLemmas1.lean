module

public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.Full1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Heuristic & Pure `Func.wp` Proofs — Part 1 (`Stage 4`)

Defines scoped `FullHeurWalkTactics` (`c0_clean`, `c0_to_group`, `c0_split`), `FullHeurWalkSpecs`
contracts for the 17 owned `Full1.lean` functions, and proves parametric `(Γ : Env)` `Func.wp`
theorems for the first 11:
1. `full_isqrt`, 2. `full_ilog10`, 3. `full_rng_next`,
4. `full_wsort_sift`, 5. `full_heap_up`, 6. `full_heap_down`, 7. `full_heap_push`,
8. `full_heap_pop`, 9. `full_rescale`, 10. `full_bump_var`, 11. `full_bump_decay`.
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

/-! ## 0. Scoped tactics, bitvector helpers, and shared predicates -/

namespace FullHeurWalkTactics

attribute [scoped bv_c0] List.length_set

@[scoped bv_c0] theorem bv32_setWidth64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

@[scoped bv_c0] theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl

open scoped FullArenaTactics in
@[scoped c0_load] theorem c0_load_full_heap0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.heap.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pHeap + 0#64) = some s.scratch.heap[0] := by
  simpa using FullArenaTactics.c0_load_full_heap (i := 0#64) hi hm

open scoped FullArenaTactics in
@[scoped c0_store] theorem c0_store_full_heap0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.heap.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pHeap + 0#64) ∧
      (FullMem c { s with scratch := { s.scratch with heap := s.scratch.heap.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pHeap + 0#64) v) := by
  simpa using FullArenaTactics.c0_store_full_heap (i := 0#64) v hi hm

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

end FullHeurWalkTactics

open scoped FullArenaTactics FullHeurWalkTactics

namespace FullHeurWalkSpecs

/-- Combined clear-marks invariant covering `mrk` (`< c.max_vars`) and `lit_mark`
(`< 2 * c.max_vars`). -/
def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

theorem fullCoreInv_with_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullCoreInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s') : FullCoreInv c F0 s' :=
  h.with_scratch hlen' hcore

theorem fullLitMarksClear_with_scratch {c : FullCfg} {s s' : FullState}
    (h : FullLitMarksClear c s)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s') : FullLitMarksClear c s' := by
  have heq := fullCoreState_agrees_with_scratch hcore
  unfold FullLitMarksClear; rwa [heq]

/-! ## 1. `FullHeurWalkSpecs`: contracts for the 17 `Full1.lean` heuristic/pure helpers -/

def fullIsqrtSpec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat * r.toNat ≤ x.toNat →
    (x.toNat ≤ 1 → r = x) →
    (2 ≤ x.toNat → 1 ≤ r.toNat ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1)) →
    Q (r, ()) m

def fullIlog10Spec : Spec [i64] [i64] := fun (_x, ()) m Q _ =>
  ∀ r : BitVec 64, 1 ≤ r.toNat → r.toNat ≤ 19 → Q (r, ()) m

def fullRngNextSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
      s'.scratch.walk_vals = s.scratch.walk_vals ∧
      s'.scratch.walk_best = s.scratch.walk_best ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullWsortKey (wvec : List (BitVec 32)) (l : Nat) : Nat :=
  (wvec[2 * l]?.getD 0#32).toNat

def fullWsortMaxHeap (key : Nat → Nat) (ws : List (BitVec 32)) (lo hi hole : Nat) : Prop :=
  ∀ p, lo ≤ p → p ≠ hole →
    (2 * p + 1 < hi → key (ws[2 * p + 1]?.getD 0#32).toNat ≤ key (ws[p]?.getD 0#32).toNat) ∧
    (2 * p + 2 < hi → key (ws[2 * p + 2]?.getD 0#32).toNat ≤ key (ws[p]?.getD 0#32).toNat)

def fullWsortHoleParent (key : Nat → Nat) (ws : List (BitVec 32))
    (lo hi root : Nat) : Prop :=
  0 < root → lo ≤ (root - 1) / 2 →
    (2 * root + 1 < hi →
      key (ws[2 * root + 1]?.getD 0#32).toNat ≤ key (ws[(root - 1) / 2]?.getD 0#32).toNat) ∧
    (2 * root + 2 < hi →
      key (ws[2 * root + 2]?.getD 0#32).toNat ≤ key (ws[(root - 1) / 2]?.getD 0#32).toNat)

def fullWsortSiftSpec : Spec [i64, i64, i64, i64] [] :=
  fun (wvecPtr, wsPtr, start, n, ()) m Q _ =>
    ∃ (wvec ws : List (BitVec 32)) (R : Mem 64 → Prop),
      start.toNat < 2 ^ 62 ∧ n.toNat ≤ ws.length ∧ n.toNat < 2 ^ 62 ∧
      (∀ k < n.toNat, 2 * (ws[k]?.getD 0#32).toNat < wvec.length) ∧
      (array (t := i32) wvecPtr wvec ⋆ array (t := i32) wsPtr ws ⋆ R) m ∧
      ∀ (ws' : List (BitVec 32)) (m' : Mem 64),
        ws'.length = ws.length →
        ws'.Perm ws →
        (∀ k, (k < start.toNat ∨ n.toNat ≤ k) → k < ws.length → ws'[k]? = ws[k]?) →
        (∀ (P : List (BitVec 32) → Prop), P ws →
          (∀ l i j, i < n.toNat → j < n.toNat →
            ∀ (hi : i < l.length) (hj : j < l.length),
            P l → P ((l.set i (l[j]'hj)).set j (l[i]'hi))) → P ws') →
        (∀ lo, lo ≤ start.toNat → start.toNat < n.toNat →
          fullWsortMaxHeap (fullWsortKey wvec) ws lo n.toNat start.toNat →
          fullWsortHoleParent (fullWsortKey wvec) ws lo n.toNat start.toNat →
          fullWsortMaxHeap (fullWsortKey wvec) ws' lo n.toNat n.toNat) →
        (array (t := i32) wvecPtr wvec ⋆ array (t := i32) wsPtr ws' ⋆ R) m' →
        Q () m'

def fullHeapUpSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      s'.scratch.heap_len = s.scratch.heap_len ∧ s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullHeapDownSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch.heap_len = s.scratch.heap_len ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullHeapPushSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullHeapPopSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      (r = 0xFFFFFFFF#64 ∨ r.toNat < s.core.cur_vars) ∧
      (0 < s.scratch.heap_len ∧ s.scratch.heap_len ≤ s.core.cur_vars →
        s'.scratch.heap_len = s.scratch.heap_len - 1) ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullRescaleSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullBumpVarSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullBumpDecaySpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullQueueRenumberSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullQueueMtfSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullTickRelSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullEmaUpdateSpec : Spec [i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _glue, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullSaveTargetBestSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

def fullRecomputeTiersSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len)

end FullHeurWalkSpecs

open FullHeurWalkSpecs

private theorem hlen_upd_scalar {c : FullCfg} {s s' : FullState}
    (h : FullState.LengthsOk c s) (hc : s'.core = s.core)
    (hs1 : s'.scratch.walk_vals = s.scratch.walk_vals)
    (hs2 : s'.scratch.phases = s.scratch.phases)
    (hs3 : s'.scratch.phases_target = s.scratch.phases_target)
    (hs4 : s'.scratch.phases_best = s.scratch.phases_best)
    (hs5 : s'.scratch.walk_best = s.scratch.walk_best)
    (hs6 : s'.scratch.heap = s.scratch.heap) (hs7 : s'.scratch.pos = s.scratch.pos)
    (hs8 : s'.scratch.shrink_stk = s.scratch.shrink_stk)
    (hs9 : s'.scratch.q_prev = s.scratch.q_prev) (hs10 : s'.scratch.q_next = s.scratch.q_next)
    (hs11 : s'.scratch.q_stamp = s.scratch.q_stamp) (hs12 : s'.scratch.wsort = s.scratch.wsort)
    (hs13 : s'.scratch.work_stk1 = s.scratch.work_stk1)
    (hs14 : s'.scratch.work_stk2 = s.scratch.work_stk2)
    (hs15 : s'.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (hs16 : s'.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hs17 : s'.scratch.score = s.scratch.score) (hs18 : s'.scratch.sim_sig = s.scratch.sim_sig)
    (hs19 : s'.scratch.glue_used = s.scratch.glue_used)
    (hs20 : s'.scratch.last_learned = s.scratch.last_learned)
    (hs21 : s'.scratch.delayed = s.scratch.delayed)
    (hs22 : s'.scratch.red_refs = s.scratch.red_refs)
    (hs23 : s'.scratch.extend_stk = s.scratch.extend_stk)
    (hs24 : s'.scratch.scratch_buf = s.scratch.scratch_buf) : FullState.LengthsOk c s' :=
  ⟨hc ▸ h.core_ok,
    { walk_vals_len := hs1 ▸ h.scratch_ok.walk_vals_len
      phases_len := hs2 ▸ h.scratch_ok.phases_len
      phases_target_len := hs3 ▸ h.scratch_ok.phases_target_len
      phases_best_len := hs4 ▸ h.scratch_ok.phases_best_len
      walk_best_len := hs5 ▸ h.scratch_ok.walk_best_len
      heap_len_arr := hs6 ▸ h.scratch_ok.heap_len_arr
      pos_len := hs7 ▸ h.scratch_ok.pos_len
      shrink_stk_len := hs8 ▸ h.scratch_ok.shrink_stk_len
      q_prev_len := hs9 ▸ h.scratch_ok.q_prev_len
      q_next_len := hs10 ▸ h.scratch_ok.q_next_len
      q_stamp_len := hs11 ▸ h.scratch_ok.q_stamp_len
      wsort_len := hs12 ▸ h.scratch_ok.wsort_len
      work_stk1_len := hs13 ▸ h.scratch_ok.work_stk1_len
      work_stk2_len := hs14 ▸ h.scratch_ok.work_stk2_len
      tarjan_mark_len := hs15 ▸ h.scratch_ok.tarjan_mark_len
      tarjan_reach_len := hs16 ▸ h.scratch_ok.tarjan_reach_len
      score_len := hs17 ▸ h.scratch_ok.score_len
      sim_sig_len := hs18 ▸ h.scratch_ok.sim_sig_len
      glue_used_len := hs19 ▸ h.scratch_ok.glue_used_len
      last_learned_len := hs20 ▸ h.scratch_ok.last_learned_len
      delayed_len_arr := hs21 ▸ h.scratch_ok.delayed_len_arr
      red_refs_len := hs22 ▸ h.scratch_ok.red_refs_len
      extend_stk_len := hs23 ▸ h.scratch_ok.extend_stk_len
      scratch_buf_len := hs24 ▸ h.scratch_ok.scratch_buf_len }⟩

private theorem hlen_upd_hp_ps {c : FullCfg} {s : FullState}
    (hlen : FullState.LengthsOk c s) (hl' : Nat) (hp' ps' : List (BitVec 32))
    (hh : hp'.length = c.max_vars) (hp : ps'.length = c.max_vars) :
    FullState.LengthsOk c { core := s.core, scratch := { s.scratch with
      heap_len := hl', heap := hp', pos := ps' } } :=
  hlen.with_scratch { hlen.scratch_ok with heap_len_arr := hh, pos_len := hp }

private theorem hlen_upd_score {c : FullCfg} {s : FullState}
    (hlen : FullState.LengthsOk c s) (sc' : List (BitVec 64)) (hs : sc'.length = c.max_vars) :
    FullState.LengthsOk c { core := s.core, scratch := { s.scratch with score := sc' } } :=
  hlen.with_scratch { hlen.scratch_ok with score_len := hs }

/-! ## 2. Pure arithmetic (`full_isqrt`, `full_ilog10`) & RNG (`full_rng_next`) -/

private theorem pow4_lt_2_64 {k : Nat} (hk : k ≤ 31) : 4 ^ k < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) (by decide)

private theorem pow4_shr2 {k : Nat} (hk : 1 ≤ k) (h4k : 4 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 (4 ^ k) >>> (2 : Nat) = BitVec.ofNat 64 (4 ^ (k - 1)) := by
  rw [bv_shr_ofNat h4k (by omega)]; congr 1
  rw [Nat.shiftRight_eq_div_pow, show 2 ^ 2 = 4 by decide]
  conv => lhs; rw [show k = (k - 1) + 1 by omega, Nat.pow_succ]
  exact Nat.mul_div_cancel _ (by omega)

private theorem isqrt_step_bound {q e x0 : Nat} (he : 1 ≤ e) (he32 : e ≤ 32)
    (hle : q * q * 4 ^ e ≤ x0) (hx : x0 < 2 ^ 64) : q * 4 ^ e + 4 ^ (e - 1) < 2 ^ 64 := by
  have h4 : 4 ^ e = 4 * 4 ^ (e - 1) := by
    conv => lhs; rw [show e = (e - 1) + 1 by omega, Nat.pow_succ]; rw [Nat.mul_comm]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have := pow4_lt_2_64 (k := e - 1) (by omega); omega
  · rcases Nat.eq_or_lt_of_le hq with rfl | hq2
    · have hlt : 4 ^ e < 2 ^ 64 := by simp only [Nat.one_mul] at hle; omega
      have he31 : e ≤ 31 := Classical.byContradiction fun h =>
        absurd (show 4 ^ 32 < 2 ^ 64 by rw [show 32 = e by omega]; exact hlt) (by decide)
      have h1 : 4 ^ (e - 1) ≤ 4 ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 5 * 4 ^ 30 < 2 ^ 64 := by decide
      simp only [Nat.one_mul]; omega
    · have hq4 : 2 * (q * 4 ^ e) ≤ q * q * 4 ^ e := by
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (4 ^ e) (Nat.mul_le_mul_right q hq2)
      have h4_le : 4 * 4 ^ (e - 1) ≤ q * q * 4 ^ e := by
        have h1 := Nat.mul_le_mul_right (4 ^ e) (Nat.mul_pos hq hq)
        simp only [Nat.one_mul] at h1; omega
      omega

private theorem isqrt_sq_odd (q a : Nat) :
    (2 * q + 1) * (2 * q + 1) * a = q * q * (4 * a) + (q * (4 * a) + a) := by grind

private theorem isqrt_sq_even (q a : Nat) : (2 * q) * (2 * q) * a = q * q * (4 * a) := by grind

private theorem isqrt_sq_succ_odd (q a : Nat) :
    (2 * q + 1 + 1) * (2 * q + 1 + 1) * a = (q + 1) * (q + 1) * (4 * a) := by grind

theorem full_isqrt_wp (Γ : Env) :
    ∀ a m Q X, fullIsqrtSpec a m Q X → Func.wp Γ full_isqrt_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  c0_steps
  · have hx1 : x.toNat ≤ 1 := by c0_bound
    exact hQ x (by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx1 with h | h <;> simp [h])
      (fun _ => rfl) (fun h => by omega)
  obtain hx2 : 2 ≤ x.toNat := by c0_bound
  obtain hxlt : x.toNat < 2 ^ 64 := x.isLt
  refine wp_loop_inv
    (fun (bit, ()) m1 => m1 = m ∧ ∃ k ≤ 31, bit = BitVec.ofNat 64 (4 ^ k) ∧ x.toNat < 4 ^ (k + 1))
    (fun (bit, ()) _ => bit.toNat) (fun J hJ => ?_)
    (fun J (bit, ()) m1 ⟨rfl, k, hk, hbit, hxk⟩ hJ => ?_)
  · c0_steps; refine hJ _ _ ⟨rfl, 31, by omega, by decide, ?_⟩
    have : 4 ^ 32 = 2 ^ 64 := by decide
    omega
  · subst hbit; c0_steps
    · have hkpos : 1 ≤ k := Classical.byContradiction fun h0 => by
        have hk0 : k = 0 := by omega
        subst hk0; simp at hc; omega
      have h4k := pow4_lt_2_64 hk; have h4k' := pow4_lt_2_64 (k := k - 1) (by omega)
      have hlt_bit : (BitVec.ofNat 64 (4 ^ (k - 1))).toNat < (BitVec.ofNat 64 (4 ^ k)).toNat := by
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4k', Nat.mod_eq_of_lt h4k]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      rw [pow4_shr2 hkpos h4k]
      exact hJ _ _ hlt_bit ⟨rfl, k - 1, by omega, rfl, by
        rw [show (k - 1) + 1 = k by omega]; rw [Nat.mod_eq_of_lt h4k] at hc; exact hc⟩
    · refine wp_loop_inv
        (fun (rem, r, bit, ()) m2 => m2 = m1 ∧ ∃ e q : Nat, e ≤ 32 ∧
          bit = (if e = 0 then 0#64 else BitVec.ofNat 64 (4 ^ (e - 1))) ∧
          r = BitVec.ofNat 64 (q * 4 ^ e) ∧ q * q * 4 ^ e + rem.toNat = x.toNat ∧
          x.toNat < (q + 1) * (q + 1) * 4 ^ e)
        (fun (_, _, bit, ()) _ => bit.toNat) (fun J2 hJ2 => ?_)
        (fun J2 (rem, r, bit, ()) m2 ⟨rfl, e, q, he32, hbit2, hr, hsum, hub⟩ hJ2 => ?_)
      · c0_steps
        exact hJ2 _ _ ⟨rfl, k + 1, 0, by omega, by simp, by simp, by simp, by simpa using hxk⟩
      · obtain hstep_prep : bit ≠ 0#64 →
            1 ≤ e ∧ bit = BitVec.ofNat 64 (4 ^ (e - 1)) ∧ 4 ^ e = 4 * 4 ^ (e - 1) ∧
            q * 4 ^ e + 4 ^ (e - 1) < 2 ^ 64 ∧
            r + bit = BitVec.ofNat 64 (q * 4 ^ e + 4 ^ (e - 1)) ∧
            r >>> (1 : Nat) = BitVec.ofNat 64 (2 * q * 4 ^ (e - 1)) ∧
            bit >>> (2 : Nat) = (if e - 1 = 0 then 0#64 else BitVec.ofNat 64 (4 ^ (e - 1 - 1))) ∧
            (bit >>> (2 : Nat)).toNat < bit.toNat := by
          intro hne0
          have hepos : 1 ≤ e := Classical.byContradiction fun h0 => by
            have he0 : e = 0 := by omega
            simp [he0] at hbit2; exact hne0 hbit2
          have hbit_eq : bit = BitVec.ofNat 64 (4 ^ (e - 1)) := by
            rw [hbit2]; simp [show e ≠ 0 by omega]
          have h4e1 := pow4_lt_2_64 (k := e - 1) (by omega)
          have h4e : 4 ^ e = 4 * 4 ^ (e - 1) := by
            conv => lhs; rw [show e = (e - 1) + 1 by omega, Nat.pow_succ]; rw [Nat.mul_comm]
          have hrb_lt := isqrt_step_bound (q := q) hepos he32 (by omega) hxlt
          have hr_shr : r >>> (1 : Nat) = BitVec.ofNat 64 (2 * q * 4 ^ (e - 1)) := by
            rw [hr, bv_shr_one (by omega)]; congr 1
            rw [show q * 4 ^ e = (2 * q * 4 ^ (e - 1)) * 2 by
              rw [h4e, show (4 : Nat) = 2 * 2 from rfl]; ac_rfl, Nat.mul_div_cancel _ (by omega)]
          have hbit_next : bit >>> (2 : Nat) =
              if e - 1 = 0 then 0#64 else BitVec.ofNat 64 (4 ^ (e - 1 - 1)) := by
            rw [hbit_eq]; by_cases he1 : e - 1 = 0
            · simp only [he1, ↓reduceIte, Nat.pow_zero]; decide
            · simp only [he1, ↓reduceIte]; exact pow4_shr2 (by omega) h4e1
          have hbit_dec : (bit >>> (2 : Nat)).toNat < bit.toNat := by
            rw [hbit_next, hbit_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4e1]; split
            · simpa using Nat.pow_pos (a := 4) (n := e - 1) (by omega)
            · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pow4_lt_2_64 (by omega))]
              exact Nat.pow_lt_pow_right (by omega) (by omega)
          exact ⟨hepos, hbit_eq, h4e, hrb_lt, by rw [hr, hbit_eq, bv_add_ofNat],
            hr_shr, hbit_next, hbit_dec⟩
        obtain hdone_prep : bit = 0#64 →
            r.toNat = q ∧ 1 ≤ q ∧ q * q ≤ x.toNat ∧ x.toNat < (q + 1) * (q + 1) := by
          intro hbz
          have he0 : e = 0 := Classical.byContradiction fun hne => by
            rw [hbz] at hbit2; simp only [hne, ↓reduceIte] at hbit2
            have h1 := congrArg BitVec.toNat hbit2
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (pow4_lt_2_64 (by omega))] at h1
            have := Nat.pow_pos (a := 4) (n := e - 1) (by omega); omega
          subst he0; simp only [Nat.pow_zero, Nat.mul_one] at hr hsum hub
          have hqpos : 1 ≤ q := Classical.byContradiction fun h0 => by
            have : q = 0 := by omega
            subst this; omega
          have hqlt : q < 2 ^ 64 := by have := Nat.le_mul_self q; omega
          exact ⟨by rw [hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt], hqpos, by omega, hub⟩
        c0_steps
        · obtain ⟨_, hbit_eq, h4e, hrb_lt, hrb_eq, hr_shr, hbit_next, hbit_dec⟩ :=
            hstep_prep (by assumption)
          have h1 : (r + bit).toNat = q * 4 ^ e + 4 ^ (e - 1) := by
            rw [hrb_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrb_lt]
          have hge : q * 4 ^ e + 4 ^ (e - 1) ≤ rem.toNat := by rw [BitVec.toNat_add] at h1; omega
          have hsub : (rem - (r + bit)).toNat = rem.toNat - (q * 4 ^ e + 4 ^ (e - 1)) := by
            rw [hrb_eq, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrb_lt]
            have := rem.isLt; omega
          exact hJ2 _ _ hbit_dec ⟨rfl, e - 1, 2 * q + 1, by omega, hbit_next,
            by rw [hr_shr, hbit_eq, bv_add_ofNat]; congr 1; rw [Nat.add_mul, Nat.one_mul],
            by rw [hsub, isqrt_sq_odd]; rw [h4e] at hsum hge ⊢; omega,
            by rw [isqrt_sq_succ_odd, ← h4e]; exact hub⟩
        · obtain ⟨_, _, h4e, hrb_lt, hrb_eq, hr_shr, hbit_next, hbit_dec⟩ :=
            hstep_prep (by assumption)
          have h1 : (r + bit).toNat = q * 4 ^ e + 4 ^ (e - 1) := by
            rw [hrb_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrb_lt]
          have hlt : rem.toNat < q * 4 ^ e + 4 ^ (e - 1) := by rw [BitVec.toNat_add] at h1; omega
          exact hJ2 _ _ hbit_dec ⟨rfl, e - 1, 2 * q, by omega, hbit_next, hr_shr,
            by rw [isqrt_sq_even, ← h4e]; exact hsum, by rw [isqrt_sq_odd, ← h4e]; omega⟩
        · obtain ⟨hr_toNat, hqpos, hsq, hub0⟩ := hdone_prep (by assumption)
          exact hQ r (by rw [hr_toNat]; exact hsq) (fun h => by omega)
            (fun _ => ⟨by rw [hr_toNat]; exact hqpos, by rw [hr_toNat]; exact hub0⟩)

theorem full_ilog10_wp (Γ : Env) :
    ∀ a m Q X, fullIlog10Spec a m Q X → Func.wp Γ full_ilog10_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  c0_steps
  refine wp_loop_inv
    (fun (r, _, ()) m1 => m1 = m ∧ 1 ≤ r.toNat ∧ r.toNat ≤ 19)
    (fun (r, _, ()) _ => 19 - r.toNat)
    (fun J hJ => ?_) (fun J (r, p, ()) m1 ⟨rfl, h1, h19⟩ hJ => ?_)
  · c0_steps; exact hJ _ _ ⟨rfl, by decide, by decide⟩
  · c0_steps
    · exact hJ _ _ (by c0_bound) ⟨rfl, by c0_bound, by c0_bound⟩
    · exact hQ r h1 h19
    · exact hQ r h1 h19

theorem full_rng_next_wp (Γ : Env) :
    ∀ a m Q X, fullRngNextSpec a m Q X → Func.wp Γ full_rng_next_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  c0_steps
  all_goals
    refine hQ _ _ _ ?_ ?_ ?_ hm
    · exact rfl
    · exact hlen_upd_scalar hlen rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. `full_wsort_sift` and binary max-heap (`heap_up`, `heap_down`, `heap_push`, `heap_pop`) -/

private def wsSwapIdx (i j k : Nat) : Nat :=
  if k = i then j else if k = j then i else k

private theorem wsSwap_getElem?_eq {ws : List (BitVec 32)} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (k : Nat) :
    ((ws.set i (ws[j]'hj)).set j (ws[i]'hi))[k]?.getD 0#32 =
      ws[wsSwapIdx i j k]?.getD 0#32 := by
  unfold wsSwapIdx
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self (by simp; omega)]
    by_cases hki : k = i <;> simp [hki, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne (by omega)]
    by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self (by omega)]; simp [List.getElem?_eq_getElem hj]
    · rw [List.getElem?_set_ne (by omega)]; simp [hki, hkj]

private theorem count_set_eq {α : Type} [DecidableEq α] (l : List α) (i : Nat) (v x : α)
    (hi : i < l.length) :
    (l.set i v).count x + (if l[i] = x then 1 else 0) =
      l.count x + (if v = x then 1 else 0) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => simp [List.count_cons]; omega
    | succ i' =>
      have hi' : i' < as.length := by simpa using hi
      have ih' := ih i' hi'
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ] at ih' ⊢
      omega

private theorem wsSwap_perm {ws : List (BitVec 32)} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) :
    ((ws.set i (ws[j]'hj)).set j (ws[i]'hi)).Perm ws := by
  by_cases hij : i = j
  · subst hij; rw [List.set_getElem_self hi, List.set_getElem_self hi]
  · rw [List.perm_iff_count]; intro x
    have h1 := count_set_eq ws i (ws[j]'hj) x hi
    have h2 := count_set_eq (ws.set i (ws[j]'hj)) j (ws[i]'hi) x (by rw [List.length_set]; exact hj)
    rw [List.getElem_set_ne hij] at h2; omega

private theorem fullWsort_sift_step {wvec ws : List (BitVec 32)}
    {lo hi root child : Nat} (hlo : lo ≤ root) (hchi : child < hi) (hhi : hi ≤ ws.length)
    (hch : child = 2 * root + 1 ∨ child = 2 * root + 2)
    (hmax : fullWsortMaxHeap (fullWsortKey wvec) ws lo hi root)
    (hpar : fullWsortHoleParent (fullWsortKey wvec) ws lo hi root)
    (hlt : fullWsortKey wvec (ws[root]?.getD 0#32).toNat <
      fullWsortKey wvec (ws[child]?.getD 0#32).toNat)
    (hsib : (2 * root + 1 < hi → fullWsortKey wvec (ws[2 * root + 1]?.getD 0#32).toNat ≤
        fullWsortKey wvec (ws[child]?.getD 0#32).toNat) ∧
      (2 * root + 2 < hi → fullWsortKey wvec (ws[2 * root + 2]?.getD 0#32).toNat ≤
        fullWsortKey wvec (ws[child]?.getD 0#32).toNat)) :
    let ws' := (ws.set root (ws[child]'(by omega))).set child (ws[root]'(by omega))
    fullWsortMaxHeap (fullWsortKey wvec) ws' lo hi child ∧
    fullWsortHoleParent (fullWsortKey wvec) ws' lo hi child := by
  intro ws'
  have hsw := wsSwap_getElem?_eq (ws := ws) (i := root) (j := child) (by omega) (by omega)
  let key := fullWsortKey wvec
  refine ⟨fun p hp hpc => ?_, fun _ _ => ?_⟩
  · have hstep : ∀ c, (c = 2 * p + 1 ∨ c = 2 * p + 2) → c < hi →
        key (ws'[c]?.getD 0#32).toNat ≤ key (ws'[p]?.getD 0#32).toNat := by
      intro c hc hci; dsimp only [ws']; rw [hsw c, hsw p]
      by_cases hpr : p = root
      · rcases hpr with rfl; rw [show wsSwapIdx p child p = child by unfold wsSwapIdx; simp]
        by_cases hcc : c = child
        · rcases hcc with rfl
          rw [show wsSwapIdx p c c = p by unfold wsSwapIdx; grind]
          dsimp only [key]; exact Nat.le_of_lt hlt
        · rw [show wsSwapIdx p child c = c by unfold wsSwapIdx; grind]
          rcases hc with rfl | rfl; exact hsib.1 hci; exact hsib.2 hci
      · rw [show wsSwapIdx root child p = p by unfold wsSwapIdx; grind]
        by_cases hcr : c = root
        · subst hcr
          have hproot : p = (c - 1) / 2 := by omega
          subst hproot
          rw [show wsSwapIdx c child c = child by unfold wsSwapIdx; simp]
          rcases hch with rfl | rfl; exact (hpar (by omega) hp).1 hchi
          exact (hpar (by omega) hp).2 hchi
        · rw [show wsSwapIdx root child c = c by unfold wsSwapIdx; grind]
          rcases hc with rfl | rfl; exact (hmax p hp hpr).1 hci; exact (hmax p hp hpr).2 hci
    exact ⟨hstep _ (Or.inl rfl), hstep _ (Or.inr rfl)⟩
  · rw [show (child - 1) / 2 = root by omega]; dsimp only [ws']; rw [hsw root]
    rw [show wsSwapIdx root child root = child by unfold wsSwapIdx; simp]
    exact ⟨fun h1 => by
        rw [hsw, show wsSwapIdx root child (2 * child + 1) = 2 * child + 1 by
          unfold wsSwapIdx; grind]
        exact (hmax child (by omega) (by omega)).1 h1,
      fun h2 => by
        rw [hsw, show wsSwapIdx root child (2 * child + 2) = 2 * child + 2 by
          unfold wsSwapIdx; grind]
        exact (hmax child (by omega) (by omega)).2 h2⟩

private theorem fullWsort_sift_done {key : Nat → Nat} {ws : List (BitVec 32)}
    {lo hi root : Nat} (hmax : fullWsortMaxHeap key ws lo hi root)
    (h1 : 2 * root + 1 < hi →
      key (ws[2 * root + 1]?.getD 0#32).toNat ≤ key (ws[root]?.getD 0#32).toNat)
    (h2 : 2 * root + 2 < hi →
      key (ws[2 * root + 2]?.getD 0#32).toNat ≤ key (ws[root]?.getD 0#32).toNat) :
    fullWsortMaxHeap key ws lo hi hi := fun p hp _ =>
  if hpr : p = root then hpr ▸ ⟨h1, h2⟩ else hmax p hp hpr

theorem full_wsort_sift_wp (Γ : Env) :
    ∀ a m Q X, fullWsortSiftSpec a m Q X → Func.wp Γ full_wsort_sift_body a m Q X := by
  rintro ⟨wvecPtr, wsPtr, start, n, ⟨⟩⟩ m Q X
    ⟨wvec, ws, R, hstart_bd, hn_le, hn_bd, hcov, hm, hQ⟩
  refine wp_join_group (fun _ m1 => Q () m1) (fun _ _ _ hq => by c0_steps; exact hq) ?_
  intro Jbrk hBrk
  c0_steps
  refine wp_loop_inv
    (fun (root, ()) mS =>
      start.toNat ≤ root.toNat ∧ root.toNat < 2 ^ 62 ∧ ∃ wsS : List (BitVec 32),
        wsS.length = ws.length ∧ wsS.Perm ws ∧
        (∀ k, (k < start.toNat ∨ n.toNat ≤ k) → k < ws.length → wsS[k]? = ws[k]?) ∧
        (∀ k < n.toNat, 2 * (wsS[k]?.getD 0#32).toNat < wvec.length) ∧
        (∀ (P : List (BitVec 32) → Prop), P ws →
          (∀ l i j, i < n.toNat → j < n.toNat →
            ∀ (hi : i < l.length) (hj : j < l.length),
            P l → P ((l.set i (l[j]'hj)).set j (l[i]'hi))) → P wsS) ∧
        (∀ lo, lo ≤ start.toNat → start.toNat < n.toNat →
          fullWsortMaxHeap (fullWsortKey wvec) ws lo n.toNat start.toNat →
          fullWsortHoleParent (fullWsortKey wvec) ws lo n.toNat start.toNat →
          lo ≤ root.toNat ∧ root.toNat < n.toNat ∧
          fullWsortMaxHeap (fullWsortKey wvec) wsS lo n.toNat root.toNat ∧
          fullWsortHoleParent (fullWsortKey wvec) wsS lo n.toNat root.toNat) ∧
        (array (t := i32) wvecPtr wvec ⋆ array (t := i32) wsPtr wsS ⋆ R) mS)
    (fun (root, ()) _ => n.toNat - root.toNat)
    (fun J hLoop => ?_) ?_
  · c0_steps
    exact hLoop (start, ()) m ⟨Nat.le_refl _, hstart_bd, ws, rfl, List.Perm.refl ws,
      fun _ _ _ => rfl, hcov, fun _ h _ => h,
      fun _ h1 h2 h3 h4 => ⟨h1, h2, h3, h4⟩, hm⟩
  · rintro J ⟨root, ⟨⟩⟩ mS
      ⟨hst_rt, hrt_bd, wsS, hwsS, hwsPerm, htailS, hcovS, hpermS, hheapS, hmS⟩ hLoop
    have hch_eq : ((root <<< (1 : Nat)) + 1).toNat = 2 * root.toNat + 1 := by
      have hsh : (root <<< (1 : Nat)).toNat = 2 * root.toNat := by c0_bound
      rw [BitVec.toNat_add, hsh]; simp; omega
    rw [Blocks.get_here]; dsimp only
    c0_split
    · c0_split
      · -- `ch >= n`: break
        have hge : n.toNat ≤ 2 * root.toNat + 1 := by c0_bound
        c0_steps
        exact hBrk (root, ()) mS (hQ wsS mS hwsS hwsPerm htailS hpermS
          (fun lo hlo hsn hmax hpar => by
            obtain ⟨_, _, hmx, _⟩ := hheapS lo hlo hsn hmax hpar
            exact fullWsort_sift_done hmx (fun h => by omega) (fun h => by omega)) hmS)
      · -- `ch < n`
        have hch_lt : 2 * root.toNat + 1 < n.toNat := by c0_bound
        have hch_ws : ((root <<< (1 : Nat)) + 1).toNat < wsS.length := by omega
        have hcl2 : ((wsS[((root <<< (1 : Nat)) + 1).toNat]'hch_ws).setWidth 64
            <<< (1 : Nat)).toNat < wvec.length := by
          have hget : (wsS[((root <<< (1 : Nat)) + 1).toNat]'hch_ws).toNat =
              (wsS[2 * root.toNat + 1]?.getD 0#32).toNat := by
            have hg := List.getElem?_eq_getElem (l := wsS) (i := 2 * root.toNat + 1) (by omega)
            rw [hg, Option.getD_some]; congr 2
          have hb := hcovS (2 * root.toNat + 1) hch_lt
          rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hget]
          simp [Nat.shiftLeft_eq]; omega
        c0_to_group
        refine wp_join_group
          (fun (ch, co, ()) mJ =>
            (ch.toNat = 2 * root.toNat + 1 ∨ ch.toNat = 2 * root.toNat + 2) ∧
            ch.toNat < n.toNat ∧
            co.toNat = fullWsortKey wvec (wsS[ch.toNat]?.getD 0#32).toNat ∧
            (2 * root.toNat + 1 < n.toNat →
              fullWsortKey wvec (wsS[2 * root.toNat + 1]?.getD 0#32).toNat ≤ co.toNat) ∧
            (2 * root.toNat + 2 < n.toNat →
              fullWsortKey wvec (wsS[2 * root.toNat + 2]?.getD 0#32).toNat ≤ co.toNat) ∧
            mS = mJ) ?_ ?_
        · rintro _ ⟨ch, co, ⟨⟩⟩ mJ ⟨hch_or, hch_n, hco_eq, hsib1, hsib2, hmJ⟩
          rcases hmJ with rfl
          have hrt_lt : root.toNat < n.toNat := by omega
          have hrl2 : ((wsS[root.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat <
              wvec.length := by
            have hget : (wsS[root.toNat]'(by omega)).toNat =
                (wsS[root.toNat]?.getD 0#32).toNat := by
              have hg := List.getElem?_eq_getElem (l := wsS) (i := root.toNat) (by omega)
              rw [hg, Option.getD_some]
            have hb := hcovS root.toNat hrt_lt
            rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hget]
            simp [Nat.shiftLeft_eq]; omega
          have hkey_r : wvec[2 * (wsS[root.toNat]'(by omega)).toNat % 2 ^ 64].toNat =
              fullWsortKey wvec (wsS[root.toNat]?.getD 0#32).toNat := by
            have hget : (wsS[root.toNat]'(by omega)).toNat =
                (wsS[root.toNat]?.getD 0#32).toNat := by
              have hg := List.getElem?_eq_getElem (l := wsS) (i := root.toNat) (by omega)
              rw [hg, Option.getD_some]
            have h2 : 2 * (wsS[root.toNat]'(by omega)).toNat % 2 ^ 64 =
                2 * (wsS[root.toNat]?.getD 0#32).toNat := by
              rw [hget, Nat.mod_eq_of_lt]; have := hcovS root.toNat hrt_lt; omega
            unfold fullWsortKey
            have hg := List.getElem?_eq_getElem (l := wvec)
              (i := 2 * (wsS[root.toNat]?.getD 0#32).toNat) (hcovS root.toNat hrt_lt)
            rw [hg, Option.getD_some]; congr 2
          rw [Blocks.get_here]; c0_clean; c0_steps
          · have hge : co.toNat ≤ fullWsortKey wvec (wsS[root.toNat]?.getD 0#32).toNat := by
              have h1 : co.toNat ≤
                  wvec[2 * (wsS[root.toNat]'(by omega)).toNat % 2 ^ 64].toNat := by c0_bound
              rw [hkey_r] at h1; exact h1
            exact hBrk (root, ()) mS (hQ wsS mS hwsS hwsPerm htailS hpermS
              (fun lo hlo hsn hmax hpar => by
                obtain ⟨_, _, hmx, _⟩ := hheapS lo hlo hsn hmax hpar
                exact fullWsort_sift_done hmx (fun h => Nat.le_trans (hsib1 h) hge)
                  (fun h => Nat.le_trans (hsib2 h) hge)) hmS)
          · have hlt : fullWsortKey wvec (wsS[root.toNat]?.getD 0#32).toNat <
                fullWsortKey wvec (wsS[ch.toNat]?.getD 0#32).toNat := by
              have h1 : ¬ (co.toNat ≤
                  wvec[2 * (wsS[root.toNat]'(by omega)).toNat % 2 ^ 64].toNat) := by c0_bound
              rw [hkey_r] at h1; omega
            let ws' := (wsS.set root.toNat (wsS[ch.toNat]'(by omega))).set
              ch.toNat (wsS[root.toNat]'(by omega))
            have hsw_cov : ∀ k < n.toNat, 2 * (ws'[k]?.getD 0#32).toNat < wvec.length := by
              intro k hk; dsimp only [ws']; rw [wsSwap_getElem?_eq (by omega) (by omega)]
              apply hcovS; unfold wsSwapIdx
              split
              · exact hch_n
              · split
                · exact hrt_lt
                · exact hk
            refine hLoop (ch, ()) m (by dsimp only; omega) ⟨by omega, by omega, ws',
              by simp [ws', hwsS],
              (wsSwap_perm (by omega) (by omega)).trans hwsPerm,
              fun k hk1 hk2 => by
                dsimp only [ws']
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact htailS k hk1 hk2,
              hsw_cov,
              fun P hP0 hPsw => hPsw wsS root.toNat ch.toNat hrt_lt hch_n
                (by omega) (by omega) (hpermS P hP0 hPsw),
              fun lo hlo hsn hmax hpar => by
                obtain ⟨hlor, _, hmx, hpr⟩ := hheapS lo hlo hsn hmax hpar
                have hst := fullWsort_sift_step hlor hch_n (by omega) hch_or hmx hpr hlt
                  ⟨fun h => by rw [← hco_eq]; exact hsib1 h,
                   fun h => by rw [← hco_eq]; exact hsib2 h⟩
                exact ⟨by omega, hch_n, hst.1, hst.2⟩,
              (by dsimp only [ws']
                  rw [sep_comm (array (t := i32) wvecPtr wvec)
                    (array (t := i32) wsPtr ws'), sep_assoc]
                  exact hm)⟩
        · intro Jc hJc
          have hco1 : (wvec[((wsS[((root <<< (1 : Nat)) + 1).toNat]'hch_ws).setWidth 64 <<<
              (1 : Nat)).toNat]'hcl2).toNat =
              fullWsortKey wvec (wsS[2 * root.toNat + 1]?.getD 0#32).toNat := by
            have hget : (wsS[((root <<< (1 : Nat)) + 1).toNat]'hch_ws).toNat =
                (wsS[2 * root.toNat + 1]?.getD 0#32).toNat := by
              have hg := List.getElem?_eq_getElem (l := wsS) (i := 2 * root.toNat + 1) (by omega)
              rw [hg, Option.getD_some]; congr 2
            have h2 : ((wsS[((root <<< (1 : Nat)) + 1).toNat]'hch_ws).setWidth 64 <<<
                (1 : Nat)).toNat = 2 * (wsS[2 * root.toNat + 1]?.getD 0#32).toNat := by
              rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hget]
              simp [Nat.shiftLeft_eq]; omega
            unfold fullWsortKey
            have hg := List.getElem?_eq_getElem (l := wvec)
              (i := 2 * (wsS[2 * root.toNat + 1]?.getD 0#32).toNat) (hcovS _ hch_lt)
            rw [hg, Option.getD_some]; congr 2
          c0_split
          · have hsp_eq : (((root <<< (1 : Nat)) + 1) + 1).toNat = 2 * root.toNat + 2 := by
              rw [BitVec.toNat_add, hch_eq]; simp; omega
            have hsp_lt : 2 * root.toNat + 2 < n.toNat := by c0_bound
            have hsp_ws : (((root <<< (1 : Nat)) + 1) + 1).toNat < wsS.length := by omega
            have hsl2 : ((wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'hsp_ws).setWidth 64 <<<
                (1 : Nat)).toNat < wvec.length := by
              have hget : (wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'hsp_ws).toNat =
                  (wsS[2 * root.toNat + 2]?.getD 0#32).toNat := by
                have hg := List.getElem?_eq_getElem (l := wsS) (i := 2 * root.toNat + 2) (by omega)
                rw [hg, Option.getD_some]; congr 2
              have hb := hcovS (2 * root.toNat + 2) hsp_lt
              rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hget]
              simp [Nat.shiftLeft_eq]; omega
            have hso : (wvec[((wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'hsp_ws).setWidth 64
                <<< (1 : Nat)).toNat]'hsl2).toNat =
                fullWsortKey wvec (wsS[2 * root.toNat + 2]?.getD 0#32).toNat := by
              have hget : (wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'hsp_ws).toNat =
                  (wsS[2 * root.toNat + 2]?.getD 0#32).toNat := by
                have hg := List.getElem?_eq_getElem (l := wsS) (i := 2 * root.toNat + 2) (by omega)
                rw [hg, Option.getD_some]; congr 2
              have h2 : ((wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'hsp_ws).setWidth 64 <<<
                  (1 : Nat)).toNat = 2 * (wsS[2 * root.toNat + 2]?.getD 0#32).toNat := by
                rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hget]
                simp [Nat.shiftLeft_eq]; omega
              unfold fullWsortKey
              have hg := List.getElem?_eq_getElem (l := wvec)
                (i := 2 * (wsS[2 * root.toNat + 2]?.getD 0#32).toNat) (hcovS _ hsp_lt)
              rw [hg, Option.getD_some]; congr 2
            c0_clean; c0_steps
            · exact hJc ((((root <<< (1 : Nat)) + 1) + 1), _, ()) _ ⟨Or.inr hsp_eq, by omega,
                by rw [hso, hsp_eq],
                fun _ => by
                  have hgt : (wvec[((wsS[((root <<< (1 : Nat)) + 1).toNat]'hch_ws).setWidth 64 <<<
                      (1 : Nat)).toNat]'hcl2).toNat <
                    (wvec[((wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'hsp_ws).setWidth 64 <<<
                      (1 : Nat)).toNat]'hsl2).toNat := by c0_bound
                  rw [hco1, hso] at hgt
                  rw [hso]; exact Nat.le_of_lt hgt,
                fun _ => by rw [hso]; exact Nat.le_refl _, rfl⟩
            · exact hJc ((root <<< (1 : Nat)) + 1, _, ()) _ ⟨Or.inl hch_eq, by omega,
                by rw [hco1, hch_eq],
                fun _ => by rw [hco1]; exact Nat.le_refl _,
                fun _ => by
                  have hle : ¬ ((wvec[((wsS[((root <<< (1 : Nat)) + 1).toNat]'hch_ws).setWidth 64
                      <<< (1 : Nat)).toNat]'hcl2).toNat <
                    (wvec[((wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'hsp_ws).setWidth 64 <<<
                      (1 : Nat)).toNat]'hsl2).toNat) := by c0_bound
                  rw [hco1, hso] at hle
                  rw [hco1]; omega,
                rfl⟩
          · have hsp_ge : n.toNat ≤ 2 * root.toNat + 2 := by
              have h1 : ¬ ((((root <<< (1 : Nat)) + 1) + 1).toNat < n.toNat) := by c0_bound
              have h2 : (((root <<< (1 : Nat)) + 1) + 1).toNat = 2 * root.toNat + 2 := by
                rw [BitVec.toNat_add, hch_eq]; simp; omega
              omega
            c0_clean; c0_steps
            exact hJc ((root <<< (1 : Nat)) + 1, _, ()) _ ⟨Or.inl hch_eq, by omega,
              by rw [hco1, hch_eq],
              fun _ => by rw [hco1]; exact Nat.le_refl _,
              fun h => by omega, rfl⟩
    · cases hc

theorem full_heap_up_wp (Γ : Env) :
    ∀ a m Q X, fullHeapUpSpec a m Q X → Func.wp Γ full_heap_up_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len; obtain hsl := hsok.score_len
  c0_steps
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl, rfl⟩ hm
  · obtain hv : v.toNat < s.core.cur_vars := by c0_bound
    obtain hp_lt : (s.scratch.pos[v.toNat]'(by omega)).toNat < s.core.cur_vars := by c0_bound
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
      (fun s1 (p, ()) => p.toNat < s.core.cur_vars ∧
        s1.scratch.heap_len = s.scratch.heap_len ∧
        s1.scratch.work_stk1 = s.scratch.work_stk1 ∧
        s1.scratch.last_learned = s.scratch.last_learned ∧
        s1.scratch.extend_len = s.scratch.extend_len)
      (fun (p, ()) => p.toNat)
      (fun J hLoop => ?_)
      (fun J s1 (p, ()) m1 hcore1 hlen1 ⟨hp1, hhl_eq, hw_eq, hll_eq, hel_eq⟩ hm1 hLoop1 => ?_)
    · c0_steps
      exact hLoop s (BitVec.setWidth 32 (s.scratch.pos[v.toNat]'(by omega)), ()) m hm rfl hlen
        ⟨by simpa [BitVec.toNat_setWidth] using hp_lt, rfl, rfl, rfl, rfl⟩
    · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok
      obtain hhl1 := hsok1.heap_len_arr; obtain hpl1 := hsok1.pos_len
      obtain hsl1 := hsok1.score_len
      c0_clean; c0_split
      · obtain hp0 : 0 < p.toNat := by c0_bound
        obtain hpp_lt : ((p - 1) >>> (1 : Nat)).toNat < p.toNat := by
          have hsub : (p - 1).toNat = p.toNat - 1 := by bv_omega
          rw [BitVec.toNat_ushiftRight, hsub]; simp [Nat.shiftRight_eq_div_pow]; omega
        obtain hpp_cv : ((p - 1) >>> (1 : Nat)).toNat < s.core.cur_vars := by omega
        obtain hpp64 : (BitVec.setWidth 64 ((p - 1) >>> (1 : Nat))).toNat =
            ((p - 1) >>> (1 : Nat)).toNat := zext_toNat _ (by decide)
        have hpp_arr : (BitVec.setWidth 64 ((p - 1) >>> (1 : Nat))).toNat <
            s1.scratch.heap.length := by rw [hhl1, hpp64]; omega
        c0_split
        · c0_steps
          refine hQ () _ m ?_ ?_ ?_ hm
          · exact hcore1.update _
          · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
          · exact ⟨hhl_eq, hw_eq, hll_eq, hel_eq⟩
        · obtain hpv_lt :
              (s1.scratch.heap[(BitVec.setWidth 64 ((p - 1) >>> (1 : Nat))).toNat]'hpp_arr).toNat <
              s1.scratch.pos.length := by
            have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hceq1]
            have : (s1.scratch.heap[(BitVec.setWidth 64 ((p - 1) >>>
                (1 : Nat))).toNat]'hpp_arr).toNat < s1.core.cur_vars := by
              rw [hceq1] at *; c0_bound
            omega
          c0_steps
          · refine hQ () _ m ?_ ?_ ?_ hm
            · exact hcore1.update _
            · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
            · exact ⟨hhl_eq, hw_eq, hll_eq, hel_eq⟩
          · refine hLoop1 _ ((p - 1) >>> (1 : Nat), ()) m hm (by dsimp only; omega) rfl ?_
              ⟨hpp_cv, hhl_eq, hw_eq, hll_eq, hel_eq⟩
            exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
      · c0_steps
        refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore1.update _
        · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
        · exact ⟨hhl_eq, hw_eq, hll_eq, hel_eq⟩

theorem full_heap_down_wp (Γ : Env) :
    ∀ a m Q X, fullHeapDownSpec a m Q X → Func.wp Γ full_heap_down_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len; obtain hsl := hsok.score_len
  c0_steps
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl⟩ hm
  · obtain hv : v.toNat < s.core.cur_vars := by c0_bound
    obtain hhle : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ s.core.cur_vars := by c0_bound
    obtain hp0_lt : (s.scratch.pos[(v.setWidth 64).toNat]'(by
        rw [zext_toNat _ (by decide)]; omega)).toNat <
        (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
      have : (s.scratch.pos[(v.setWidth 64).toNat]'(by
          rw [zext_toNat _ (by decide)]; omega)).toNat < s.scratch.heap_len % 2 ^ 64 := by
        c0_bound
      simpa [BitVec.toNat_ofNat] using this
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
      (fun s1 (p, ()) => p.toNat < (BitVec.ofNat 64 s.scratch.heap_len).toNat ∧
        s1.scratch.heap_len = s.scratch.heap_len ∧
        s1.scratch.last_learned = s.scratch.last_learned ∧
        s1.scratch.extend_len = s.scratch.extend_len)
      (fun (p, ()) => (BitVec.ofNat 64 s.scratch.heap_len).toNat - p.toNat)
      (fun J hLoop => ?_)
      (fun J s1 (p, ()) m1 hcore1 hlen1 ⟨hp, hhl_eq, hll_eq, hel_eq⟩ hm1 hLoop1 => ?_)
    · c0_steps
      exact hLoop s (_, ()) m hm rfl hlen ⟨hp0_lt, rfl, rfl, rfl⟩
    · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok
      obtain hhl1 := hsok1.heap_len_arr; obtain hpl1 := hsok1.pos_len
      obtain hsl1 := hsok1.score_len
      obtain hp_mv : p.toNat < c.max_vars := by omega
      obtain hsh_p : (p.setWidth 64 <<< (1 : Nat)).toNat = 2 * p.toNat := by
        rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]; simp [Nat.shiftLeft_eq]; omega
      obtain hcp_toNat : ((p.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * p.toNat + 1 := by
        rw [BitVec.toNat_add, hsh_p]; simp; omega
      c0_split
      c0_split
      · c0_steps
        refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore1.update _
        · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
        · exact ⟨hhl_eq, hll_eq, hel_eq⟩
      · have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hceq1]
        have hhlen64 : (BitVec.ofNat 64 s.scratch.heap_len).toNat ≤ c.max_vars := by omega
        have hcp_lt : 2 * p.toNat + 1 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
          have : (BitVec.setWidth 64 p <<< (1 : Nat) + 1).toNat <
              (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
          rw [hcp_toNat] at this; exact this
        have hcp_hlt : (BitVec.setWidth 64 p <<< (1 : Nat) + 1).toNat < s1.scratch.heap.length := by
          rw [hhl1, hcp_toNat]; omega
        c0_split
        · c0_steps
          refine hQ () _ m ?_ ?_ ?_ hm
          · exact hcore1.update _
          · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
          · exact ⟨hhl_eq, hll_eq, hel_eq⟩
        · have hcv_lt : (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) +
              1).toNat]'hcp_hlt).toNat < s.core.cur_vars := by
            have : (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) +
                1).toNat]'hcp_hlt).toNat < s1.core.cur_vars := by
              rw [hceq1] at *; c0_bound
            omega
          have hcv_sc : (BitVec.setWidth 64 (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) +
              1).toNat]'hcp_hlt)).toNat < s1.scratch.score.length := by
            rw [zext_toNat _ (by decide)]; omega
          c0_to_group
          · refine wp_join_group
              (fun (cp', cv', _csc', ()) m2 => p.toNat < cp'.toNat ∧
                cp'.toNat < (BitVec.ofNat 64 s.scratch.heap_len).toNat ∧
                cv'.toNat < s.core.cur_vars ∧ m1 = m2)
              (fun _ (cp', cv', csc', ()) m2 ⟨hgt, hlt, hcv_mv, hm2⟩ => ?_) ?_
            · rcases hm2 with rfl; c0_steps
              · refine hQ () _ m ?_ ?_ ?_ hm
                · exact hcore1.update _
                · exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
                · exact ⟨hhl_eq, hll_eq, hel_eq⟩
              · have hcp32 : (cp'.setWidth 32).toNat = cp'.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                refine hLoop1 _ (cp'.setWidth 32, ()) m hm (by dsimp only; omega) rfl ?_
                  ⟨by dsimp only; omega, hhl_eq, hll_eq, hel_eq⟩
                exact hlen_upd_hp_ps hlen1 _ _ _ (by simp [hhl1]) (by simp [hpl1])
            · intro Jm hJm; c0_steps
              · have hsp_eq : (BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat =
                    2 * p.toNat + 2 := by
                  rw [BitVec.toNat_add, hcp_toNat]; simp; omega
                have hsp_lt : 2 * p.toNat + 2 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by
                  have : (BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat <
                      (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
                  omega
                have hsv_mv : (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat]'(
                    by rw [hhl1, hsp_eq]; omega)).toNat < s.core.cur_vars := by
                  rw [hceq1] at *; c0_bound
                have hsv_lt : (BitVec.setWidth 64
                    (s1.scratch.heap[(BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat]'(by
                      rw [hhl1, hsp_eq]; omega))).toNat < s1.scratch.score.length := by
                  rw [zext_toNat _ (by decide)]; omega
                c0_clean; c0_steps
                exact hJm ((BitVec.setWidth 64 p <<< (1 : Nat)) + 1 + 1, _, _, ()) m1
                  ⟨by rw [hsp_eq]; omega, by rw [hsp_eq]; omega, hsv_mv, rfl⟩
              all_goals
                refine hJm _ _ ⟨by rw [hcp_toNat]; omega,
                  by rw [hcp_toNat]; omega,
                  hcv_lt, rfl⟩
      · cases hc

theorem full_heap_push_wp (Γ : Env)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullHeapPushSpec a m Q X → Func.wp Γ full_heap_push_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len
  c0_steps
  · exact hQ () s m rfl hlen ⟨rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl⟩ hm
  · refine wp_safety_slice_call hUp (fun _ => True) trivial rfl ?_ hm
      fun _ s' m' hcore' hlen' _ ⟨_, _, hll', hel'⟩ hm' => ?_
    · exact hlen_upd_hp_ps hlen _ _ _ (by simp [hhl]) (by simp [hpl])
    · dsimp only [fullSafetySlice] at hm' hlen'
      c0_steps
      refine hQ () s' m' ((PreservesCoreSlice.of_update _ s _ (fun _ => rfl)).trans hcore')
        hlen' ⟨hll', hel'⟩ hm'

theorem full_heap_pop_wp (Γ : Env)
    (hDown : ∀ a m Q X, fullHeapDownSpec a m Q X → Γ "full_heap_down" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullHeapPopSpec a m Q X → Func.wp Γ full_heap_pop_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  obtain hhl := hsok.heap_len_arr; obtain hpl := hsok.pos_len
  obtain hnlen_sub : 0 < s.scratch.heap_len ∧ s.scratch.heap_len ≤ s.core.cur_vars →
      (BitVec.ofNat 64 s.scratch.heap_len - 1).toNat = s.scratch.heap_len - 1 :=
    fun ⟨hpos, hle⟩ => by
      have h1 := bv64_ofNat_toNat (n := s.scratch.heap_len) (by omega)
      have : 0 < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by omega
      bv_omega
  c0_steps
  · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨Or.inl rfl, fun ⟨hpos, hle⟩ => by
      have h1 : (BitVec.ofNat 64 s.scratch.heap_len).toNat = 0 := by
        rw [bv64_ofNat_toNat (by omega)] at *; c0_bound
      rw [bv64_ofNat_toNat (by omega)] at h1; omega, rfl, rfl⟩ hm
  · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨Or.inl rfl, fun ⟨_, hle⟩ => by
      have h1 : s.core.cur_vars < (BitVec.ofNat 64 s.scratch.heap_len).toNat := by c0_bound
      rw [bv64_ofNat_toNat (by omega)] at h1; omega, rfl, rfl⟩ hm
  all_goals first
  | (refine wp_safety_slice_call hDown (fun _ => True) trivial rfl ?_ hm
       fun _ s' m' hcore' hlen' _ ⟨hhl', hll', hel'⟩ hm' => ?_
     · exact hlen_upd_hp_ps hlen _ _ _ (by simp [hhl]) (by simp [hpl])
     · dsimp only [fullSafetySlice] at hm' hlen'
       c0_steps
       · exact hQ (0xFFFFFFFF#64, ()) s' m' hcore' hlen' ⟨Or.inl rfl, fun h => by
           rw [hhl']; exact hnlen_sub h, hll', hel'⟩ hm'
       · exact hQ _ s' m' hcore' hlen' ⟨Or.inr (by
           rw [fullCoreState_agrees_with_scratch hcore'] at *; c0_bound),
           fun h => by rw [hhl']; exact hnlen_sub h, hll', hel'⟩ hm')
  | (refine hQ (0xFFFFFFFF#64, ()) _ _ ?_ ?_ ?_ hm
     · exact rfl
     · exact hlen_upd_hp_ps hlen _ _ _ (by simp [hhl]) (by simp [hpl])
     · exact ⟨Or.inl rfl, hnlen_sub, rfl, rfl⟩)
  | (refine hQ _ _ _ ?_ ?_ ?_ hm
     · exact rfl
     · exact hlen_upd_hp_ps hlen _ _ _ (by simp [hhl]) (by simp [hpl])
     · exact ⟨Or.inr (by c0_bound), hnlen_sub, rfl, rfl⟩)

/-! ## 4. EVSIDS rescaling & bumping (`full_rescale`, `full_bump_var`, `full_bump_decay`) -/

theorem full_rescale_wp (Γ : Env) :
    ∀ a m Q X, fullRescaleSpec a m Q X → Func.wp Γ full_rescale_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok
  obtain hcv_le := hok.cur_vars_le
  c0_steps
  refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
    (fun s1 (v, ()) => v.toNat ≤ s.core.cur_vars ∧ s1.scratch.work_stk1 = s.scratch.work_stk1 ∧
      s1.scratch.last_learned = s.scratch.last_learned ∧
      s1.scratch.extend_len = s.scratch.extend_len)
    (fun (v, ()) => s.core.cur_vars - v.toNat)
    (fun J hLoop => ?_)
    (fun J s1 (v, ()) m1 hcore1 hlen1 ⟨hv1, hw_eq, hll_eq, hel_eq⟩ hm1 hLoop1 => ?_)
  · c0_steps; exact hLoop s (0#64, ()) m hm rfl hlen ⟨by simp, rfl, rfl, rfl⟩
  · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
    have hceq1 : s1.core = s.core := hcore1
    obtain hsok1 := hlen1.scratch_ok; obtain hsl1 := hsok1.score_len
    c0_clean; c0_steps
    · have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
        bv64_ofNat_toNat (by omega)
      have hv_lt : v.toNat < s.core.cur_vars := by
        have h1 : v.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
          rw [hceq1] at *; c0_bound
        omega
      have hvp1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
      refine hLoop1 _ (v + 1, ()) m hm (by dsimp only; omega) rfl ?_
        ⟨by dsimp only; omega, hw_eq, hll_eq, hel_eq⟩
      exact hlen_upd_score hlen1 _ (by simp [hsl1])
    all_goals
      refine hQ () _ m ?_ ?_ ?_ hm
      · exact hcore1
      · exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact ⟨hw_eq, hll_eq, hel_eq⟩

theorem full_bump_var_wp (Γ : Env)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hRes : ∀ a m Q X, fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpVarSpec a m Q X → Func.wp Γ full_bump_var_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le; obtain hsl := hsok.score_len
  c0_steps
  · exact hQ () s m rfl hlen ⟨rfl, rfl, rfl⟩ hm
  all_goals
    refine wp_safety_slice_call hUp (fun _ => True) trivial rfl ?_ hm
      fun _ s1 m1 hcore1 hlen1 _ ⟨_, hw1, hll1, hel1⟩ hm1 => ?_
    · exact hlen_upd_score hlen _ (by simp [hsl])
    · dsimp only [fullSafetySlice] at hm1 hlen1
      c0_steps
      all_goals first
      | (refine wp_safety_slice_call hRes (fun _ => True) trivial rfl hlen1 hm1
           fun _ s2 m2 hcore2 hlen2 _ ⟨hw2, hll2, hel2⟩ hm2 => ?_
         dsimp only [fullSafetySlice] at hm2 hlen2
         c0_steps; exact hQ () s2 m2 (hcore1.trans hcore2) hlen2
           ⟨hw2.trans hw1, hll2.trans hll1, hel2.trans hel1⟩ hm2)
      | exact hQ () s1 m1 hcore1 hlen1 ⟨hw1, hll1, hel1⟩ hm1

theorem full_bump_decay_wp (Γ : Env)
    (hRes : ∀ a m Q X, fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpDecaySpec a m Q X → Func.wp Γ full_bump_decay_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  c0_to_group
  refine wp_join_group
    (fun (inc, ()) m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
      s1.LengthsOk c ∧ s1.scratch.work_stk1 = s.scratch.work_stk1 ∧
      s1.scratch.last_learned = s.scratch.last_learned ∧
      s1.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ (inc, ()) m1 ⟨s1, hcore1, hlen1, hw1, hll1, hel1, hm1⟩ => ?_) ?_
  · c0_to_group
    refine wp_join_group
      (fun (inc', ()) m2 => ∃ s2 : FullState, PreservesCoreSlice FullState.core s s2 ∧
        s2.LengthsOk c ∧ s2.scratch.work_stk1 = s.scratch.work_stk1 ∧
        s2.scratch.last_learned = s.scratch.last_learned ∧
        s2.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c s2 ⋆ R) m2)
      (fun _ (inc', ()) m2 ⟨s2, hcore2, hlen2, hw2, hll2, hel2, hm2⟩ => ?_) ?_
    · c0_steps
      · refine wp_safety_slice_call hRes (fun _ => True) trivial rfl ?_ hm
          fun _ s3 m3 hcore3 hlen3 _ ⟨hw3, hll3, hel3⟩ hm3 => ?_
        · exact hlen_upd_scalar hlen2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        · dsimp only [fullSafetySlice] at hm3 hlen3
          c0_steps
          exact hQ () s3 m3 (hcore2.trans hcore3) hlen3
            ⟨hw3.trans hw2, hll3.trans hll2, hel3.trans hel2⟩ hm3
      · refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore2
        · exact hlen_upd_scalar hlen2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        · exact ⟨hw2, hll2, hel2⟩
    · intro J2 hJ2; c0_steps
      all_goals first
      | (refine wp_safety_slice_call hRes (fun _ => True) trivial rfl hlen1 hm1
           fun _ s2 m2 hcore2 hlen2 _ ⟨hw2, hll2, hel2⟩ hm2 => ?_
         dsimp only [fullSafetySlice] at hm2 hlen2
         c0_steps
         exact hJ2 _ _ ⟨s2, hcore1.trans hcore2, hlen2, hw2.trans hw1, hll2.trans hll1,
           hel2.trans hel1, hm2⟩)
      | exact hJ2 _ _ ⟨s1, hcore1, hlen1, hw1, hll1, hel1, hm1⟩
  · intro J1 hJ1; c0_steps
    · exact hJ1 _ _ ⟨s, rfl, hlen, rfl, rfl, rfl, hm⟩
    · exact hJ1 _ _ ⟨s, rfl, hlen, rfl, rfl, rfl, hm⟩

end LeanQbe.T.Examples.Kissat.Full
