module

public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0Agrees
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Stage-3 M7 Search Parity `Func.wp` Proofs — Part 1 (`Group B` WPs & Drop-In Bridges)

Plain `public section` (`0` `@[expose]`) parametric `(Γ : Env)` `Func.wp` proofs for the remaining
`10` `FullM7Search` functions plus canonical `FullSpec*` drop-in bridges:
- Clause tumbling (`full_tumble_clause_m7_wp`, `full_tumble_clauses_m7_wp`, `full_tumble_m7_wp`)
- Lucky probing (`full_lucky_polar_m7_wp`, `full_lucky_late_m7_wp`, `full_lucky_late_m7_dropin_wp`)
- Random decision cadence (`full_randec_step_m7_wp`, `full_randec_var_m7_wp`,
  `full_randec_var_m7_dropin_wp`)
- Focused initial-phase alternation (`full_decide_m7_wp`, `full_decide_m7_dropin_wp`)
- Non-wiping mode-EMA swap (`full_ema_swap_m7_wp`, `full_switch_mode_m7_wp`,
  `full_switch_mode_m7_dropin_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Search

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. Local C0 Stepper Tactics & Arithmetic Helpers -/

private theorem m7_strip_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem m7_strip_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem m7_strip_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "m7_strip" : tactic =>
  `(tactic| first | apply m7_strip_32_64 | apply m7_strip_8_32 | apply m7_strip_8_64)
local macro "m7_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
local macro "m7_steps" : tactic =>
  `(tactic| (
      (try m7_unmdata)
      (repeat m7_strip)
      c0_steps
      repeat (any_goals (m7_strip; repeat m7_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops, stopping at `Expr.group` instead of inlining join points. -/
local elab "m7_to_group_step" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g'' ← g.change ty (checkDefEq := false)
        replaceMainGoal [g'']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push (← getMainGoal)
      else if ← LeanQbe.T.C0Step.stepOnce then
        evalTactic (← `(tactic| all_goals (try (repeat m7_strip))))
        go (fuel - 1)
        out := out ++ (← getUnsolvedGoals)
      else
        out := out.push (← getMainGoal)
    setGoals out.toList
  go 500

local macro "m7_to_group" : tactic =>
  `(tactic| ((try m7_unmdata); (repeat m7_strip); m7_to_group_step))

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops until `Expr.jnz`, then split it once. -/
local elab "m7_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step))
      return
    evalTactic (← `(tactic| all_goals (repeat m7_strip)))
    if ← Lean.Elab.Tactic.tryTactic (evalTactic (← `(tactic| c0_step))) then
      evalTactic (← `(tactic| all_goals (repeat m7_strip)))
      go (fuel - 1)
  go 120

local macro "m7_call" hSpec:term : tactic =>
  `(tactic| (
      m7_unmdata
      refine LeanQbe.T.wp_call_of_spec _ _ ($hSpec _ _ _ _ ?_)
      try c0_let_simp))

private theorem m7_ite_lt63 {α : Type} {n : Nat} {a b : α} (h : n < 63) :
    (if n < 63 then a else b) = a := by simp [h]

local macro "m7_step_init" hs:term "," hm:term "," hInit:ident ","
    hs':ident "," hi':ident "," hp':ident "," m':ident "," hm':ident : tactic =>
  `(tactic| (
    m7_to_group
    m7_call $hInit
    refine m7StateInitSpec_of $hs $hm ?_
    try dsimp only
    intro $hs':ident $hi':ident $hp':ident $m':ident $hm':ident))

local macro "m7_step_get64" hs:term "," hm:term "," hGet:ident "," _idx:ident : tactic =>
  `(tactic| (
    m7_to_group
    m7_call $hGet
    refine m7Get64Spec_of $hs $hm ?_
    try dsimp only
    focus (
      rw [m7_ite_lt63]
      any_goals try (first | decide | (dsimp only [Arg.val]; decide)))))

local macro "m7_step_set64" hs:term "," hm:term "," hSet:ident ","
    hs':ident "," m':ident "," hm':ident : tactic =>
  `(tactic| (
    m7_to_group
    m7_call $hSet
    refine m7Set64Spec_of $hs $hm ?_
    try dsimp only
    focus (
      rw [m7_ite_lt63]
      any_goals try (first | decide | (dsimp only [Arg.val]; decide)))
    try dsimp only
    intro $hs':ident $m':ident $hm':ident
    try dsimp only [Arg.val] at $hs':ident $hm':ident))

local macro "m7_step_lcg" hs:term "," hm:term "," hLcg:ident ","
    r:ident "," s':ident "," hcore':ident "," hs':ident "," hres':ident "," m':ident ","
    hm':ident : tactic =>
  `(tactic| (
    m7_to_group
    m7_call $hLcg
    refine m7LcgNextSpec_of $hs $hm ?_
    intro $r:ident $s':ident $m':ident $hcore':ident $hs':ident $hres':ident $hm':ident))

private theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem bv64_sub1_toNat {x : BitVec 64} (hx : x ≠ 0#64) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hpos : 0 < x.toNat :=
    Nat.pos_of_ne_zero fun h0 => hx (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

private theorem bv64_shl1_eq (x : BitVec 64) : x <<< 1#64 = x * 2#64 := by
  change x <<< (1#64).toNat = x * 2#64
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq, Nat.mul_comm]

private theorem bv64_shl1_toNat' {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< 1#64).toNat = 2 * x.toNat := by
  rw [bv64_shl1_eq, BitVec.toNat_mul]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt hx]

private theorem bv64_shl1_or1_eq (x : BitVec 64) : x <<< 1#64 ||| 1#64 = x * 2#64 + 1#64 := by
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

private theorem bv8_sext32_eq0_iff : ∀ x : BitVec 8, x.signExtend 32 = 0#32 ↔ x = 0#8 := by
  decide

private theorem bv8_dom_sgt0_iff {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#32).slt (x.signExtend 32) = true ↔ x = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

private theorem bv8_dom_slt0_iff {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

private theorem bv8_eq0_of_not_slt_sgt {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8)
    (h1 : (0#32).slt (x.signExtend 32) = false) (h2 : (x.signExtend 32).slt 0#32 = false) :
    x = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> first | rfl | (exfalso; revert h1 h2; decide)

/-! ## 2. Positional `FullScratch.LengthsOk`, `FullArenaScan`, & Invariant Helpers -/

/-- Construct `FullScratch.LengthsOk` without triggering struct-`with` depth blowups. -/
private theorem lengthsOk_scratch_scalars {c : FullCfg} {sc sc' : FullScratch}
    (h : FullScratch.LengthsOk c sc)
    (hwv : sc'.walk_vals = sc.walk_vals) (hph : sc'.phases = sc.phases)
    (hpt : sc'.phases_target = sc.phases_target) (hpb : sc'.phases_best = sc.phases_best)
    (hwb : sc'.walk_best = sc.walk_best) (hhp : sc'.heap = sc.heap)
    (hps : sc'.pos = sc.pos) (hsk : sc'.shrink_stk = sc.shrink_stk)
    (hqp : sc'.q_prev = sc.q_prev) (hqn : sc'.q_next = sc.q_next)
    (hqs : sc'.q_stamp = sc.q_stamp) (hws : sc'.wsort = sc.wsort)
    (hw1 : sc'.work_stk1 = sc.work_stk1) (hw2 : sc'.work_stk2 = sc.work_stk2)
    (htm : sc'.tarjan_mark = sc.tarjan_mark) (htr : sc'.tarjan_reach = sc.tarjan_reach)
    (hsc : sc'.score = sc.score) (hsg : sc'.sim_sig = sc.sim_sig)
    (hgu : sc'.glue_used = sc.glue_used) (hll : sc'.last_learned = sc.last_learned)
    (hdl : sc'.delayed = sc.delayed) (hrr : sc'.red_refs = sc.red_refs)
    (hes : sc'.extend_stk = sc.extend_stk) (hsb : sc'.scratch_buf = sc.scratch_buf) :
    FullScratch.LengthsOk c sc' :=
  FullScratch.LengthsOk.mk
    (hwv ▸ h.walk_vals_len) (hph ▸ h.phases_len) (hpt ▸ h.phases_target_len)
    (hpb ▸ h.phases_best_len) (hwb ▸ h.walk_best_len) (hhp ▸ h.heap_len_arr)
    (hps ▸ h.pos_len) (hsk ▸ h.shrink_stk_len) (hqp ▸ h.q_prev_len)
    (hqn ▸ h.q_next_len) (hqs ▸ h.q_stamp_len) (hws ▸ h.wsort_len)
    (hw1 ▸ h.work_stk1_len) (hw2 ▸ h.work_stk2_len) (htm ▸ h.tarjan_mark_len)
    (htr ▸ h.tarjan_reach_len) (hsc ▸ h.score_len) (hsg ▸ h.sim_sig_len)
    (hgu ▸ h.glue_used_len) (hll ▸ h.last_learned_len) (hdl ▸ h.delayed_len_arr)
    (hrr ▸ h.red_refs_len) (hes ▸ h.extend_stk_len) (hsb ▸ h.scratch_buf_len)

private theorem lengthsOk_scratch_heap {c : FullCfg} {sc : FullScratch}
    (h : FullScratch.LengthsOk c sc) {hp' ps' : List (BitVec 32)} {hl' : Nat}
    (hhp : hp'.length = c.max_vars) (hps : ps'.length = c.max_vars) :
    FullScratch.LengthsOk c { sc with heap := hp', pos := ps', heap_len := hl' } :=
  FullScratch.LengthsOk.mk
    h.walk_vals_len h.phases_len h.phases_target_len h.phases_best_len h.walk_best_len
    hhp hps h.shrink_stk_len h.q_prev_len h.q_next_len h.q_stamp_len h.wsort_len
    h.work_stk1_len h.work_stk2_len h.tarjan_mark_len h.tarjan_reach_len h.score_len
    h.sim_sig_len h.glue_used_len h.last_learned_len h.delayed_len_arr h.red_refs_len
    h.extend_stk_len h.scratch_buf_len

private theorem probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem probePres_trans {s1 s2 s3 : FullState}
    (h12 : FullProbeScratchPres s1 s2) (h23 : FullProbeScratchPres s2 s3) :
    FullProbeScratchPres s1 s3 :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩, h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1, h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1, h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

private theorem arena_lit_mem_clauseLits (k : FullCoreState) (r j : Nat)
    (hj : j < fullArenaClauseSizeCore k r) (hrj : r + 3 + j < k.arena.length) :
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
      ((k.arena.drop (r + 3)).take (fullArenaClauseSizeCore k r))[j]'h2 := by simp
  rw [hmem]
  exact List.getElem_mem h2

private theorem fullArenaScanRefs_succ (ar : List (BitVec 32)) (alen pos f : Nat) :
    fullArenaScanRefs ar alen pos (f + 1) =
      if pos + 3 ≤ alen then pos :: fullArenaScanRefs ar alen (fullArenaNextOff ar alen pos) f
      else [] := by
  cases f <;> simp [fullArenaScanRefs]

private theorem fullArenaScanRefs_next_mem (ar : List (BitVec 32)) (alen : Nat) :
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
          rw [fullArenaScanRefs_succ]; simp [h3]
      · have hwf_tail : ∀ p ∈ fullArenaScanRefs ar alen nxt f,
            p + 3 ≤ fullArenaNextOff ar alen p ∧
            (fullArenaNextOff ar alen p = alen ∨ fullArenaNextOff ar alen p + 3 ≤ alen) :=
          fun p hp => hwf p (by rw [fullArenaScanRefs_succ]; simp [hpos, nxt, hp])
        rcases fullArenaScanRefs_next_mem ar alen f nxt r (by omega) hwf_tail hr_tail with
          heq | hm
        · exact Or.inl heq
        · exact Or.inr (Or.inr hm)
    · simp [hpos] at hr

private theorem fullWitnessInv_unsat_of_level0_conflict {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl : s.core.cur_level = 0)
    (hcf : FullConflictOkW F_cur s) : F0.Unsat := by
  have hunit : ∀ l, l < 2 * s.core.cur_vars → s.core.vals[l]?.getD 0#8 = 0xFF#8 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := fun l hl hv => by
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hl).mp hv
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
    rwa [hieq] at hs
  rcases hcf with ⟨_, hl0, hl1, hv0, hv1, hent⟩ | ⟨_, href, hgarb, hlits⟩
  · refine hw.ext_sound.2 (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_))
    right; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> first | exact hunit _ hl0 hv0 | exact hunit _ hl1 hv1
  · exact hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hgarb) fun l hl =>
        Or.inr (hunit l (hw.arena.lits_lt _ href hgarb l hl) (hlits l hl))))

/-! ## 3. Clause Tumbling (`full_tumble_clause_m7`, `full_tumble_clauses_m7`, `full_tumble_m7`) -/

theorem full_tumble_clause_m7_wp (Γ : Env)
    (hLcg : EnvSpec Γ "full_lcg_next_m7" m7LcgNextSpec) :
    ∀ a m Q X, m7TumbleClauseSpec a m Q X →
      Func.wp Γ full_tumble_clause_m7_body a m Q X := by
  intro ⟨h, cref, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, F_cur, s, R, rfl, hsp, hcr, hm, hQ⟩ := m7TumbleClauseSpec_elim hspec
  have hwf := hsp.2.1.arena.refs_wf cref.toNat hcr
  have hcl := hsp.1.core_ok
  have har_len := hcl.arena_len_arr
  have har_le := hcl.arena_len_le
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hdb_ar := c.harena
  have hcr32 : cref.toNat < 2 ^ 32 := cref.isLt
  have hcr3 : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by bv_omega
  unfold Func.wp full_tumble_clause_m7_body
  m7_split
  · exfalso
    have hdb : LratBytes.dimacsBound < 2 ^ 30 := by decide
    have hgt : s.core.arena_len < cref.toNat + 3 := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
      exact hc
    omega
  · have hcr_lt0 : (cref.setWidth 64).toNat < s.core.arena.length := by bv_omega
    have hcr_lt2 : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
    have hcr_lt1 : (cref.setWidth 64 + 1#64).toNat < s.core.arena.length := by bv_omega
    have hidx0 : (cref.setWidth 64).toNat = cref.toNat := by bv_omega
    have hidx2 : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
    have hidx1 : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by bv_omega
    m7_split
    · m7_steps
      exact hQ false s.core.arena s.scratch.rng_state m hsp (fullArenaPermEq_refl _)
        (fun _ _ _ => rfl) (fun _ => ⟨rfl, rfl⟩) hm
    · m7_split
      · m7_steps
        exact hQ false s.core.arena s.scratch.rng_state m hsp (fullArenaPermEq_refl _)
          (fun _ _ _ => rfl) (fun _ => ⟨rfl, rfl⟩) hm
      · have hng_bit : (s.core.arena[cref.toNat] &&& 0x80000#32) = 0#32 := by
          simpa [hidx0] using ‹_›
        have hng : fullArenaClauseGarbCore s.core cref.toNat = false := by
          have ha : s.core.arena[cref.toNat]? = some s.core.arena[cref.toNat] :=
            List.getElem?_eq_getElem (by omega)
          dsimp only [fullArenaClauseGarbCore, fullArenaHdrCore]
          rw [ha]; simp [hng_bit]
        have hsz_eq : s.core.arena[cref.toNat + 2].toNat =
            fullArenaClauseSizeCore s.core cref.toNat := by
          have ha : s.core.arena[cref.toNat + 2]? = some s.core.arena[cref.toNat + 2] :=
            List.getElem?_eq_getElem (by omega)
          dsimp only [fullArenaClauseSizeCore]; rw [ha]; rfl
        have hsz_ge4 : 4 ≤ fullArenaClauseSizeCore s.core cref.toNat := by
          have h4 : ¬ s.core.arena[(cref.setWidth 64 + 2#64).toNat].toNat < 4 := ‹_›
          simp only [hidx2] at h4
          rw [hsz_eq] at h4; omega
        have hfit : cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤ s.core.arena_len :=
          Nat.le_trans hwf.2.2.1 hwf.2.2.2.1
        m7_split
        · exfalso
          have hdb : LratBytes.dimacsBound < 2 ^ 30 := by decide
          have h2_64 : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
            bv_omega
          have h3_64 : BitVec.toNat (3 : BitVec 64) = 3 := by decide
          have hc_nat : s.core.arena_len < cref.toNat + 3 + s.core.arena[cref.toNat + 2].toNat := by
            simp only [h2_64, h3_64] at hc
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
            exact hc
          rw [hsz_eq] at hc_nat; omega
        · have hdb : LratBytes.dimacsBound < 2 ^ 30 := by decide
          m7_steps
          obtain ⟨hsp0, hperm0⟩ := setSrch_preserves_sparseInvW hsp hcr (srch := 2#32)
          let ar0 := s.core.arena.set (cref.toNat + 1) 2#32
          have h1_64 : (cref.setWidth 64 + (1 : BitVec 64)).toNat = cref.toNat + 1 := hidx1
          have hm0' : (FullMem c { s with core := { s.core with arena := ar0 } } ⋆ R) m := by
            dsimp only [ar0]; rw [← h1_64]; assumption
          let szv := s.core.arena[cref.toNat + 2]
          have hszv_nat : szv.toNat = fullArenaClauseSizeCore s.core cref.toNat := hsz_eq
          have hsub1 : (szv - 1#32).toNat = szv.toNat - 1 := by bv_omega
          refine wp_loop_inv (ts := [i32])
            (fun (i, ()) m_cur => ∃ (ar' : List (BitVec 32)) (rng' : BitVec 64),
              let st' : FullState :=
                { core := { s.core with arena := ar' }
                  scratch := { s.scratch with rng_state := rng' } }
              FullSparseInvW c F0 F_cur st' ∧ FullArenaPermEq s.core st'.core ∧
              2 ≤ i.toNat ∧ i.toNat < szv.toNat ∧
              (∀ idx, idx < s.core.arena_len →
                idx ≠ cref.toNat + 1 ∧
                  ¬(cref.toNat + 5 ≤ idx ∧ idx < cref.toNat + 3 + szv.toNat) →
                ar'[idx]? = s.core.arena[idx]?) ∧
              (FullMem c st' ⋆ R) m_cur)
            (fun (i, ()) _ => i.toNat) ?_ ?_
          · intro L hL
            m7_steps
            have h2_64 : (cref.setWidth 64 + (2 : BitVec 64)).toNat = cref.toNat + 2 := hidx2
            simp only [h2_64]
            exact hL (szv - 1#32, ()) _ ⟨ar0, s.scratch.rng_state, hsp0, hperm0,
              by rw [hsub1, hszv_nat]; omega, by rw [hsub1]; omega,
              fun idx _ ⟨hne1, _⟩ => by dsimp only [ar0]; exact List.getElem?_set_ne hne1.symm,
              hm0'⟩
          · intro L (i, ()) m_cur ⟨ar', rng', hst_sp, hst_pm, hi2, hi_lt, hhold, hm_cur⟩ ih
            try simp only [Blocks.get]; try dsimp only
            m7_split
            · have hi_ge3 : 3 ≤ i.toNat := by
                have h2lt : 2 < i.toNat := ‹_›; omega
              let st_cur : FullState :=
                { core := { s.core with arena := ar' }
                  scratch := { s.scratch with rng_state := rng' } }
              have hm1_cur : (FullMem c st_cur ⋆ R) m_cur := hm_cur
              have hlen_cur := hst_sp.1
              m7_step_lcg hlen_cur, hm1_cur, hLcg, r_lcg, s1', hs1_core, hlen1, hres1, m1, hm1
              dsimp only at hres1
              obtain ⟨hr_eq, hsc_eq⟩ := hres1
              let rand := m7LcgNextVal rng'
              have hr_val : r_lcg = rand.2 := hr_eq
              let st1 : FullState :=
                { core := { s.core with arena := ar' },
                  scratch := { s.scratch with rng_state := rand.1 } }
              have hs1_eq : s1' = st1 := by
                cases s1' with
                | mk c1 sc1 =>
                  dsimp only at hs1_core hsc_eq; subst hs1_core; rw [hsc_eq]
              rw [hs1_eq] at hlen1 hm1
              have hsp1 : FullSparseInvW c F0 F_cur st1 :=
                fullSparseInvW_with_rng_gu hst_sp hlen1.scratch_ok rfl rfl
              have hpm1 : FullArenaPermEq s.core st1.core := hst_pm
              have hm1' : (FullMem c st1 ⋆ R) m1 := hm1
              have hm1_nat : (i - 1#32).toNat = i.toNat - 1 := by bv_omega
              have hi1_lt : (i - 1#32).toNat < 2 ^ 32 := (i - 1#32).isLt
              have hi1_64 : ((i - 1#32).setWidth 64).toNat = i.toNat - 1 := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hi1_lt (by decide)),
                  hm1_nat]
              have hdiv_pos : ((i - 1#32).setWidth 64) ≠ 0#64 := by
                intro hz
                have h0 : ((i - 1#32).setWidth 64).toNat = 0 := by simp [hz]
                rw [hi1_64] at h0; omega
              have hmod : (rand.2 % (i - 1#32).setWidth 64).toNat < i.toNat - 1 := by
                rw [BitVec.toNat_umod, hi1_64]
                exact Nat.mod_lt _ (by omega)
              let rem32 := (rand.2 % (i - 1#32).setWidth 64).setWidth 32
              have hrem : rem32.toNat < i.toNat - 1 := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hmod (by omega))]
                exact hmod
              let j := 2#32 + rem32
              have hj_nat : j.toNat = 2 + rem32.toNat := by
                dsimp only [j]
                rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                simp only [Nat.reducePow, Nat.reduceMod]
                omega
              have hj_le_i : j.toNat ≤ i.toNat := by omega
              have hj_ge2 : 2 ≤ j.toNat := by omega
              have hj_lt32 : j.toNat < 2 ^ 32 := j.isLt
              have hcref_lt32 : cref.toNat < 2 ^ 32 := cref.isLt
              have hi_lt32 : i.toNat < 2 ^ 32 := i.isLt
              have hcref1 : cref.toNat ∈ fullArenaClauseRefsCore st1.core := by
                rw [hpm1.2.1]; exact hcr
              have hsz1 : fullArenaClauseSizeCore st1.core cref.toNat = szv.toNat := by
                rw [(hpm1.2.2 cref.toNat hcr).1, hszv_nat]
              have har1_len : st1.core.arena.length = c.arena_cap := hlen1.core_ok.arena_len_arr
              have hi_idx : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
                  cref.toNat + 3 + i.toNat := by
                have hcb : (cref.setWidth 64).toNat = cref.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hcref_lt32 (by decide))]
                have hib : (i.setWidth 64).toNat = i.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hi_lt32 (by decide))]
                have h3 : (3#64).toNat = 3 := rfl
                have hs1 : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
                  rw [BitVec.toNat_add, hcb, h3, Nat.mod_eq_of_lt (by omega)]
                rw [BitVec.toNat_add, hs1, hib, Nat.mod_eq_of_lt (by omega)]
              have hj_idx : (cref.setWidth 64 + 3#64 + j.setWidth 64).toNat =
                  cref.toNat + 3 + j.toNat := by
                have hcb : (cref.setWidth 64).toNat = cref.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hcref_lt32 (by decide))]
                have hjb : (j.setWidth 64).toNat = j.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hj_lt32 (by decide))]
                have h3 : (3#64).toNat = 3 := rfl
                have hs1 : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
                  rw [BitVec.toNat_add, hcb, h3, Nat.mod_eq_of_lt (by omega)]
                rw [BitVec.toNat_add, hs1, hjb, Nat.mod_eq_of_lt (by omega)]
              have hi_bd : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat <
                  st1.core.arena.length := by rw [hi_idx]; omega
              have hj_bd : (cref.setWidth 64 + 3#64 + j.setWidth 64).toNat <
                  st1.core.arena.length := by rw [hj_idx]; omega
              have hj_bd2 :
                  (cref.setWidth 64 + 3#64 + (2#32 +
                    (rand.2 % (i - 1#32).setWidth 64).setWidth 32).setWidth 64).toNat <
                  (st1.core.arena.set (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat
                    st1.core.arena[(cref.setWidth 64 + 3#64 + (2#32 +
                      (rand.2 % (i - 1#32).setWidth 64).setWidth 32).setWidth 64).toNat]).length :=
                by rw [List.length_set]; exact hj_bd
              rw [hr_val]
              m7_steps
              have hsw := swapLits_preserves_sparseInvW hsp1 hcref1 (k1 := i.toNat) (k2 := j.toNat)
                (by rw [hsz1]; exact hi_lt) (by rw [hsz1]; omega)
              rcases hsw with ⟨hsp2, hpm2⟩
              let li := st1.core.arena[cref.toNat + 3 + i.toNat]'(by rw [← hi_idx]; exact hi_bd)
              let lj := st1.core.arena[cref.toNat + 3 + j.toNat]'(by rw [← hj_idx]; exact hj_bd)
              let ar2 := (ar'.set (cref.toNat + 3 + i.toNat) lj).set (cref.toNat + 3 + j.toNat) li
              have har2_eq :
                  (ar'.set (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat
                      (ar'[(cref.setWidth 64 + 3#64 + j.setWidth 64).toNat])).set
                    (cref.setWidth 64 + 3#64 + j.setWidth 64).toNat
                      (ar'[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]) = ar2 := by
                simp only [ar2, li, lj, st1, hi_idx, hj_idx]
              have hhold2 : ∀ idx, idx < s.core.arena_len →
                  idx ≠ cref.toNat + 1 ∧
                    ¬(cref.toNat + 5 ≤ idx ∧ idx < cref.toNat + 3 + szv.toNat) →
                  ar2[idx]? = s.core.arena[idx]? := by
                intro idx hidx1 hidx2
                dsimp only [ar2]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact hhold idx hidx1 hidx2
              let st2_sc : FullScratch := { s.scratch with rng_state := rand.1 }
              let ar2_raw := (ar'.set (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat
                (ar'[(cref.setWidth 64 + 3#64 + j.setWidth 64).toNat])).set
                (cref.setWidth 64 + 3#64 + j.setWidth 64).toNat
                (ar'[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat])
              let st2_raw : FullState :=
                { core := { s.core with arena := ar2_raw }, scratch := st2_sc }
              let st2_final : FullState :=
                { core := { s.core with arena := ar2 }, scratch := st2_sc }
              have har2_fin : st2_raw = st2_final :=
                congrArg (fun a =>
                  ({ core := { s.core with arena := a }, scratch := st2_sc } : FullState)) har2_eq
              refine ih (i - 1#32, ()) _ (by dsimp only; rw [hm1_nat]; omega)
                ⟨ar2, rand.1, hsp2, fullArenaPermEq_trans hpm1 hpm2,
                  by rw [hm1_nat]; omega, by rw [hm1_nat]; omega, hhold2, ?_⟩
              change (FullMem c st2_final ⋆ R) _
              rw [← har2_fin]
              assumption
            · m7_steps
              exact hQ true ar' rng' m_cur hst_sp hst_pm
                (fun idx h1 h2 =>
                  hhold idx h1 ⟨h2.1, fun h3 => h2.2 ⟨h3.1, by rw [← hszv_nat]; exact h3.2⟩⟩)
                (fun hf => by cases hf) hm_cur

theorem full_tumble_clauses_m7_wp (Γ : Env)
    (hNext : EnvSpec Γ "full_arena_next" fullArenaNextSpec)
    (hTc : EnvSpec Γ "full_tumble_clause_m7" m7TumbleClauseSpec) :
    ∀ a m Q X, m7TumbleClausesSpec a m Q X →
      Func.wp Γ full_tumble_clauses_m7_body a m Q X := by
  intro ⟨h, budget, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩ := m7TumbleClausesSpec_elim hspec
  have hcl := hsp.1.core_ok
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hdb : LratBytes.dimacsBound < 2 ^ 30 := by decide
  have hal_lt : s.core.arena_len < 2 ^ 31 := by
    have := hcl.arena_len_le; have := c.harena; omega
  unfold Func.wp full_tumble_clauses_m7_body
  m7_to_group
  refine wp_join_group (ts := [i64, i64]) (fun (_p_ret, done_ret, ()) m_ret =>
      ∃ ar'' rng'',
        let st'' : FullState :=
          { core := { s.core with arena := ar'' }
            scratch := { s.scratch with rng_state := rng'' } }
        FullSparseInvW c F0 F_cur st'' ∧ FullArenaPermEq s.core st''.core ∧
        (∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
          ar''[r + 3]? = s.core.arena[r + 3]? ∧ ar''[r + 4]? = s.core.arena[r + 4]?) ∧
        (FullMem c st'' ⋆ R) m_ret) ?_ ?_
  · rintro _ ⟨p_ret, done_ret, ⟨⟩⟩ m_ret ⟨ar'', rng'', hsp_r, hpm_r, hw_r, hm_r⟩
    simp only [Blocks.get]; try dsimp only
    m7_steps
    exact hQ done_ret ar'' rng'' m_ret hsp_r hpm_r hw_r hm_r
  · intro Jexit hJexit
    m7_to_group
    refine wp_loop_inv (ts := [i64, i64])
      (fun (p, done, ()) m_cur => ∃ (ar' : List (BitVec 32)) (rng' : BitVec 64),
        let st' : FullState :=
          { core := { s.core with arena := ar' }
            scratch := { s.scratch with rng_state := rng' } }
        FullSparseInvW c F0 F_cur st' ∧ FullArenaPermEq s.core st'.core ∧
        p.toNat ≤ s.core.arena_len ∧
        (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
        (∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
          ar'[r + 3]? = s.core.arena[r + 3]? ∧ ar'[r + 4]? = s.core.arena[r + 4]?) ∧
        (FullMem c st' ⋆ R) m_cur)
      (fun (p, _, ()) _ => s.core.arena_len - p.toNat) ?_ ?_
    · intro L hL
      m7_steps
      have h0_mem : (0#64).toNat = s.core.arena_len ∨ (0#64).toNat ∈ fullArenaClauseRefs s := by
        have h0_64 : (0#64).toNat = 0 := by decide
        rw [h0_64]
        rcases hsp.2.1.arena.len_ok with h0 | h3
        · exact Or.inl h0.symm
        · right; unfold fullArenaClauseRefs fullArenaClauseRefsCore
          cases hal : s.core.arena_len with
          | zero => omega
          | succ f => rw [fullArenaScanRefs_succ]; simp [← hal, h3]
      have hm_eq : (FullMem c
          { core := { s.core with arena := s.core.arena }
            scratch := { s.scratch with rng_state := s.scratch.rng_state } } ⋆ R) m := hm
      exact hL (0#64, 0#64, ()) m
        ⟨s.core.arena, s.scratch.rng_state, hsp, fullArenaPermEq_refl _, by simp, h0_mem,
          fun _ _ _ => ⟨rfl, rfl⟩, hm_eq⟩
    · intro L (p, done, ()) m_cur ⟨ar', rng', hst_sp, hst_pm, hp_le, hp_mem, hwatch, hm_cur⟩ ih
      let st_cur : FullState :=
        { core := { s.core with arena := ar' }
          scratch := { s.scratch with rng_state := rng' } }
      have hm1_cur : (FullMem c st_cur ⋆ R) m_cur := hm_cur
      have hlen_cur := hst_sp.1
      have hwe_cur := hst_sp.2.1
      simp only [Blocks.get]; try dsimp only
      m7_split
      · m7_split
        · have hp_lt : p.toNat < s.core.arena_len := by
            have hc_p : p.toNat < st_cur.core.arena_len % 2 ^ 64 := ‹_›
            change p.toNat < s.core.arena_len % 2 ^ 64 at hc_p
            rwa [Nat.mod_eq_of_lt (by omega)] at hc_p
          have hp_cref : p.toNat ∈ fullArenaClauseRefs st_cur := by
            rcases hp_mem with heq | hmem
            · omega
            · change p.toNat ∈ fullArenaClauseRefsCore st_cur.core
              rw [hst_pm.2.1]; exact hmem
          have hp32 : (p.setWidth 32).toNat = p.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          let nxt := fullArenaNextOff ar' s.core.arena_len p.toNat
          have hnxt_le : nxt ≤ s.core.arena_len := by
            have := (hwe_cur.arena.refs_wf p.toNat hp_cref).2.2.2.1
            dsimp only [st_cur] at this
            exact this
          have hlt32 : nxt < 2 ^ 32 := by
            have := c.harena
            have : LratBytes.dimacsBound < 2 ^ 30 := by decide
            have := hlen_cur.core_ok.arena_len_le
            omega
          m7_to_group
          m7_call hNext
          refine ⟨c, st_cur, R, rfl, hlen_cur, hm1_cur, ?_⟩
          rw [hp32]
          dsimp only [Arg.val]
          let nxt_v := BitVec.ofNat 32 nxt
          have hnxt_eq : (nxt_v.setWidth 64).toNat = nxt := by
            dsimp only [nxt_v]
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32,
              Nat.mod_eq_of_lt (Nat.lt_trans hlt32 (by decide))]
          have hnxt_mem : nxt = s.core.arena_len ∨ nxt ∈ fullArenaClauseRefs s := by
            have hnm := fullArenaScanRefs_next_mem ar' s.core.arena_len s.core.arena_len 0
              p.toNat (Nat.le_refl _)
              (fun q hq => by
                have hq_wf := hwe_cur.arena.refs_wf q hq
                exact ⟨Nat.le_trans (by omega) hq_wf.2.2.1, hq_wf.2.2.2.2⟩)
              hp_cref
            rcases hnm with heq | hmem
            · exact Or.inl heq
            · right; change _ ∈ fullArenaClauseRefsCore s.core
              rw [← hst_pm.2.1]; exact hmem
          have hnxt_le : nxt ≤ s.core.arena_len :=
            (hwe_cur.arena.refs_wf p.toNat hp_cref).2.2.2.1
          m7_to_group
          refine wp_join_group (ts := [i64]) (fun (done', ()) m_j =>
              ∃ ar1 rng1,
                let st1 : FullState :=
                  { core := { s.core with arena := ar1 }
                    scratch := { s.scratch with rng_state := rng1 } }
                FullSparseInvW c F0 F_cur st1 ∧ FullArenaPermEq s.core st1.core ∧
                (∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
                  ar1[r + 3]? = s.core.arena[r + 3]? ∧ ar1[r + 4]? = s.core.arena[r + 4]?) ∧
                (FullMem c st1 ⋆ R) m_j) ?_ ?_
          · rintro _ ⟨done', ⟨⟩⟩ m_j ⟨ar1, rng1, hsp1, hpm_all, hw1, hm1⟩
            simp only [Blocks.get]; try dsimp only
            m7_split
            · exact hJexit (p, done', ()) m_j ⟨ar1, rng1, hsp1, hpm_all, hw1, hm1⟩
            · have hgt : p.toNat < nxt := by
                have hc0 :
                    ¬ fullArenaNextOff st_cur.core.arena st_cur.core.arena_len p.toNat % 2 ^ 32 ≤
                      p.toNat := by assumption
                dsimp only [st_cur] at hc0
                change ¬ nxt % 2 ^ 32 ≤ p.toNat at hc0
                rw [Nat.mod_eq_of_lt hlt32] at hc0
                omega
              exact ih (nxt_v.setWidth 64, done', ()) m_j (by dsimp only; rw [hnxt_eq]; omega)
                ⟨ar1, rng1, hsp1, hpm_all, by rw [hnxt_eq]; exact hnxt_le,
                  by rw [hnxt_eq]; exact hnxt_mem, hw1, hm1⟩
          · intro Jnext hJnext
            m7_to_group
            m7_call hTc
            refine m7TumbleClauseSpec_of hst_sp (by rw [hp32]; exact hp_cref) hm1_cur ?_
            try dsimp only
            intro ok ar1 rng1 m1 hsp1 hpm1 hhold1 _ hm1
            change FullSparseInvW c F0 F_cur
              { core := { s.core with arena := ar1 }
                scratch := { s.scratch with rng_state := rng1 } } at hsp1
            change (FullMem c
              { core := { s.core with arena := ar1 }
                scratch := { s.scratch with rng_state := rng1 } } ⋆ R) m1 at hm1
            have hw1 : ∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
                ar1[r + 3]? = s.core.arena[r + 3]? ∧ ar1[r + 4]? = s.core.arena[r + 4]? := by
              intro r hr hsz
              obtain ⟨hw3, hw4⟩ := hwatch r hr hsz
              have hp_s : p.toNat ∈ fullArenaClauseRefs s := by
                change p.toNat ∈ fullArenaClauseRefsCore s.core
                rw [← hst_pm.2.1]; exact hp_cref
              have hwf_p := hsp.2.1.arena.refs_wf p.toNat hp_s
              have := hwf_p.2.2.1
              have hsz_eq : fullArenaClauseSizeCore st_cur.core p.toNat =
                  fullArenaClauseSizeCore s.core p.toNat := by
                have hpe := (hst_pm.2.2 p.toNat hp_s).1
                dsimp only [st_cur] at hpe
                exact hpe
              have hr_lt_al : r + 4 < s.core.arena_len := by
                have hwf_r := hsp.2.1.arena.refs_wf r hr
                have := hwf_r.2.2.1; have := hwf_r.2.2.2.1
                change 3 ≤ fullArenaClauseSizeCore s.core r at hsz; omega
              have h3_keep : ar1[r + 3]? = ar'[r + 3]? := by
                refine hhold1 (r + 3) (by omega) ?_
                rw [hp32, hsz_eq]; rcases Nat.lt_trichotomy r p.toNat with hlt | rfl | hgt
                · have hd := hsp.2.1.arena.disjoint hr hp_s hlt
                  change 3 ≤ fullArenaClauseSizeCore s.core r at hsz; omega
                · omega
                · have hd := hsp.2.1.arena.disjoint hp_s hr hgt; omega
              have h4_keep : ar1[r + 4]? = ar'[r + 4]? := by
                refine hhold1 (r + 4) (by omega) ?_
                rw [hp32, hsz_eq]; rcases Nat.lt_trichotomy r p.toNat with hlt | rfl | hgt
                · have hd := hsp.2.1.arena.disjoint hr hp_s hlt
                  change 3 ≤ fullArenaClauseSizeCore s.core r at hsz; omega
                · omega
                · have hd := hsp.2.1.arena.disjoint hp_s hr hgt; omega
              exact ⟨h3_keep.trans hw3, h4_keep.trans hw4⟩
            have hpm_all : FullArenaPermEq s.core
                { s.core with arena := ar1 } := fullArenaPermEq_trans hst_pm hpm1
            m7_split <;> m7_steps
            · exact hJnext (done + 1#64, ()) m1 ⟨ar1, rng1, hsp1, hpm_all, hw1, hm1⟩
            · exact hJnext (done, ()) m1 ⟨ar1, rng1, hsp1, hpm_all, hw1, hm1⟩
        · m7_steps; exact hJexit (p, done, ()) m_cur ⟨ar', rng', hst_sp, hst_pm, hwatch, hm_cur⟩
      · m7_steps; exact hJexit (p, done, ()) m_cur ⟨ar', rng', hst_sp, hst_pm, hwatch, hm_cur⟩

theorem full_tumble_m7_wp (Γ : Env)
    (hTc : EnvSpec Γ "full_tumble_clauses_m7" m7TumbleClausesSpec) :
    ∀ a m Q X, m7TumbleSpec a m Q X → Func.wp Γ full_tumble_m7_body a m Q X := by
  intro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩ := m7TumbleSpec_elim hspec
  unfold Func.wp full_tumble_m7_body
  m7_to_group
  m7_call hTc
  exact m7TumbleClausesSpec_of hsp hm hQ

/-! ## 4. Lucky Polar (`full_lucky_polar_m7`) & Decider Step (`full_randec_step_m7`) -/

private inductive PolarWatchOk (k : FullCoreState) : Nat → Nat → Prop where
  | empty (p : Nat) : PolarWatchOk k p 0
  | bin {p rem : Nat} {w0 : BitVec 32} :
      k.wstk[p]? = some w0 → w0 &&& 2147483648#32 ≠ 0#32 → w0 ≠ 4294967295#32 →
      (w0 &&& 2147483647#32).toNat < 2 * k.cur_vars → PolarWatchOk k (p + 1) rem →
      PolarWatchOk k p (rem + 1)
  | large {p rem : Nat} {w0 : BitVec 32} :
      k.wstk[p]? = some w0 → w0 &&& 2147483648#32 = 0#32 → PolarWatchOk k (p + 2) rem →
      PolarWatchOk k p (rem + 2)

private theorem modeWatchesInv_toPolar {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) :
    WatchStackLayout k ∧ ∀ l < 2 * k.cur_vars,
      PolarWatchOk k (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  have toPolW : ∀ {lit p rem}, WatchSliceOk F_cur k lit p rem → PolarWatchOk k p rem := by
    intro lit p rem hw
    induction hw with
    | empty => exact .empty _
    | bin h0 hb hn hl _ _ ih => exact .bin h0 hb hn hl ih
    | large h0 _ hb _ _ _ ih => exact .large h0 hb ih
  have toPolD : ∀ {lit p rem}, DenseWatchSliceOk F_cur k lit p rem → PolarWatchOk k p rem := by
    intro lit p rem hw
    induction hw with
    | empty => exact .empty _
    | bin h0 hb hn hl _ _ ih => exact .bin h0 hb hn hl ih
    | occ h0 _ hb _ _ _ _ ih => exact .large h0 hb ih
  unfold ModeWatchesInv at h
  by_cases hdm : k.dense_mode = 0#64
  · simp [hdm] at h; exact ⟨h.layout, fun l hl => toPolW (h.slices l hl)⟩
  · simp [hdm] at h; exact ⟨h.layout, fun l hl => toPolD (h.slices l hl)⟩

private theorem polar_widx_0 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64).toNat = 2 * (2 * v.toNat) := by
  rw [bv64_shl1_eq, bv64_shl1_eq]; bv_omega

private theorem polar_widx_01 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64 + 1#64).toNat =
      2 * (2 * v.toNat) + 1 := by
  rw [bv64_shl1_eq, bv64_shl1_eq]; bv_omega

private theorem polar_widx_10 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64).toNat =
      2 * (2 * v.toNat + 1) := by
  rw [bv64_shl1_or1_eq, bv64_shl1_eq]; bv_omega

private theorem polar_widx_11 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64 + 1#64).toNat =
      2 * (2 * v.toNat + 1) + 1 := by
  rw [bv64_shl1_or1_eq, bv64_shl1_eq]; bv_omega

theorem full_lucky_polar_m7_wp (Γ : Env)
    (hNext : EnvSpec Γ "full_arena_next" fullArenaNextSpec) :
    ∀ a m Q X, fullLuckyPolarSpec a m Q X →
      Func.wp Γ full_lucky_polar_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_lucky_polar_m7_body
  m7_to_group
  rcases hinv with ⟨hlen_all, F_cur, hwe⟩
  have hlen := hlen_all.core_ok
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hdb : LratBytes.dimacsBound < 2 ^ 30 := by decide
  have hcv_lt : s.core.cur_vars < 2 ^ 31 := by have := hlen.cur_vars_le; omega
  have hal_lt : s.core.arena_len < 2 ^ 31 := by
    have := hlen.arena_len_le; have := c.harena; omega
  have hwl_lt : s.core.wlen < 2 ^ 31 := by
    have := hlen.wlen_le; have := c.hwcap; omega
  obtain ⟨hlay, hpw⟩ := modeWatchesInv_toPolar hwe.watches
  apply wp_join_group (ts := [.bool, .bool, i64]) (fun _ m2 => m2 = m)
  · rintro _J0 ⟨sp, sn, _r, ⟨⟩⟩ m2 hm2
    rw [hm2]; clear hm2 m2
    simp only [Blocks.get]; try dsimp only
    m7_to_group
    apply wp_loop_group (ts := [.bool, .bool, i64])
      (fun (v_rem : Nat) xs2 m2 => ∃ (sp2 sn2 : Bool) (v : BitVec 64),
        xs2 = (sp2, sn2, v, ()) ∧ m2 = m ∧ v_rem = s.core.cur_vars - v.toNat ∧
        v.toNat ≤ s.core.cur_vars)
    · intro J2 n2 xs2 m2 hrec2 ⟨sp2, sn2, v, hxs2, hm2, hn2, hv_le⟩
      subst hxs2; rw [hm2]; clear hm2 m2; simp only [Blocks.get]; try dsimp only; m7_to_group
      apply wp_join_group (ts := []) (fun _ m3 => m3 = m)
      · intro _Jret ⟨⟩ m3 hm3; rw [hm3]; clear hm3 m3; m7_steps <;> exact hQ _ (by decide)
      · intro Jret hJret
        m7_to_group
        · have hv_lt : v.toNat < s.core.cur_vars := by
            have hc1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
            rwa [Nat.mod_eq_of_lt (by omega)] at hc1
          m7_to_group
          apply wp_join_group (ts := []) (fun _ m3 => m3 = m)
          · intro _J2b ⟨⟩ m3 hm3
            rw [hm3]; clear hm3 m3; m7_to_group
            apply wp_join_group (ts := [.bool, .bool]) (fun _ m4 => m4 = m)
            · intro _J2next ⟨sp', sn', ⟨⟩⟩ m4 hm4
              rw [hm4]; clear hm4 m4; simp only [Blocks.get]
              simp only [wp_let, Op.wp, OpCode.wp, lift2, wp_jump]
              have hv1_lt : (v + 1#64).toNat = v.toNat + 1 := bv64_add1_toNat (by omega)
              exact hrec2 (s.core.cur_vars - (v + 1#64).toNat) (sp', sn', v + 1#64, ()) m
                (by omega) ⟨sp', sn', v + 1#64, rfl, rfl, rfl, by omega⟩
            · intro J2next hJ2next
              have h_vals : (v <<< 1#64).toNat < s.core.vals.length := by
                rw [bv64_shl1_toNat' (by omega)]; have := hlen.vals_len
                have := hlen.cur_vars_le; omega
              have h_flags : v.toNat < s.core.flags.length := by
                have := hlen.flags_len; have := hlen.cur_vars_le; omega
              have := hlen.cur_vars_le
              have hv30 : v.toNat < 2 ^ 30 := by omega
              have hcv2 : 2 * (2 * v.toNat + 1) + 1 < 4 * s.core.cur_vars := by omega
              have hl1_0 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64).toNat =
                  2 * (2 * v.toNat + 1) := polar_widx_10 hv30
              have hl1_1 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64 + 1#64).toNat =
                  2 * (2 * v.toNat + 1) + 1 := polar_widx_11 hv30
              have hl0_0 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64).toNat =
                  2 * (2 * v.toNat) := polar_widx_0 hv30
              have hl0_1 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64 + 1#64).toNat =
                  2 * (2 * v.toNat) + 1 := polar_widx_01 hv30
              have hw0 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64).toNat <
                  s.core.wvec.length := by
                rw [hl1_0]; have := hlen.wvec_len; have := hlen.cur_vars_le; omega
              have hw1 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64 + 1#64).toNat <
                  s.core.wvec.length := by
                rw [hl1_1]; have := hlen.wvec_len; have := hlen.cur_vars_le; omega
              have hw2 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64).toNat < s.core.wvec.length := by
                rw [hl0_0]; have := hlen.wvec_len; have := hlen.cur_vars_le; omega
              have hw3 : (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64 + 1#64).toNat <
                  s.core.wvec.length := by
                rw [hl0_1]; have := hlen.wvec_len; have := hlen.cur_vars_le; omega
              let i1_0 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64).toNat
              let i1_1 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64 ||| 1#64)) <<< 1#64 + 1#64).toNat
              let off1 := s.core.wvec[i1_0]; let sz1 := s.core.wvec[i1_1]
              have hoff1 : off1.toNat = fullWatchOffCore s.core (2 * v.toNat + 1) := by
                dsimp [fullWatchOffCore]; rw [← hl1_0, List.getElem?_eq_getElem hw0]; rfl
              have hsz1 : sz1.toNat = fullWatchSizeCore s.core (2 * v.toNat + 1) := by
                dsimp [fullWatchSizeCore]; rw [← hl1_1, List.getElem?_eq_getElem hw1]; rfl
              have hbd1 := hlay.bounds (2 * v.toNat + 1) (by omega)
              have hpw1 := hpw (2 * v.toNat + 1) (by omega)
              let i0_0 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64).toNat
              let i0_1 := (BitVec.setWidth 64
                  (BitVec.setWidth 32 (v <<< 1#64)) <<< 1#64 + 1#64).toNat
              let off0 := s.core.wvec[i0_0]; let sz0 := s.core.wvec[i0_1]
              have hoff0 : off0.toNat = fullWatchOffCore s.core (2 * v.toNat) := by
                dsimp [fullWatchOffCore]; rw [← hl0_0, List.getElem?_eq_getElem hw2]; rfl
              have hsz0 : sz0.toNat = fullWatchSizeCore s.core (2 * v.toNat) := by
                dsimp [fullWatchSizeCore]; rw [← hl0_1, List.getElem?_eq_getElem hw3]; rfl
              have hbd0 := hlay.bounds (2 * v.toNat) (by omega)
              have hpw0 := hpw (2 * v.toNat) (by omega)
              m7_split
              · m7_split
                · m7_to_group
                  apply wp_join_group (ts := [.bool, i64]) (fun _ m4 => m4 = m)
                  · intro _Jw1_done ⟨sp', _w1j, ⟨⟩⟩ m4 hm4
                    rw [hm4]; clear hm4 m4; simp only [Blocks.get]; m7_to_group
                    apply wp_join_group (ts := [.bool, i64]) (fun _ m5 => m5 = m)
                    · intro _Jw2_done ⟨sn', _w0j, ⟨⟩⟩ m5 hm5
                      rw [hm5]; clear hm5 m5; simp only [Blocks.get, wp_jump]
                      exact hJ2next (sp', sn', ()) m rfl
                    · intro Jw2_done hJw2_done
                      m7_to_group
                      · apply wp_loop_group (ts := [.bool, i64])
                          (fun (wrem2 : Nat) xw2 mw2 => ∃ (flg2 : Bool) (jw2 : BitVec 64),
                            xw2 = (flg2, jw2, ()) ∧ mw2 = m ∧
                            jw2.toNat + wrem2 = off0.toNat + sz0.toNat ∧
                            PolarWatchOk s.core jw2.toNat wrem2)
                        · intro Jw2 nw2 xw2 mw2 hrecw2 ⟨flg2, jw2, hxw2, hmw2, hjw2_sum, hpw2_cur⟩
                          subst hxw2; subst mw2; simp only [Blocks.get]
                          rw [wp_let]; simp only [Op.wp]
                          have hsum0 : off0.toNat + sz0.toNat < 2 ^ 64 := by omega
                          have hjw2_end : (BitVec.setWidth 64 off0 + BitVec.setWidth 64 sz0).toNat =
                              off0.toNat + sz0.toNat := by
                            rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (Nat.lt_trans off0.isLt (by decide)),
                              Nat.mod_eq_of_lt (Nat.lt_trans sz0.isLt (by decide)),
                              Nat.mod_eq_of_lt (by omega)]
                          constructor
                          · intro hc; dsimp only [Arg.val] at hc
                            simp only [liftCmp, CmpOp.evalBits] at hc
                            have hlt : jw2.toNat < off0.toNat + sz0.toNat := by
                              change decide (jw2.toNat < (BitVec.setWidth 64 off0 +
                                BitVec.setWidth 64 sz0).toNat) = true at hc
                              rw [hjw2_end] at hc; exact of_decide_eq_true hc
                            rw [wp_jnz]; refine ⟨fun hflg => ?_, fun hflg => ?_⟩
                            · subst hflg; rw [wp_jump]; exact hJw2_done _ m rfl
                            · have hnw2 : 0 < nw2 := by omega
                              have hjw2_lt : jw2.toNat < s.core.wstk.length := by
                                have := hlen.wstk_len_arr; have := hlen.wlen_le
                                rw [← hoff0, ← hsz0] at hbd0; omega
                              m7_to_group
                              apply wp_join_group (ts := [.bool, i64]) (fun xs' mw' =>
                                ∃ (flg' : Bool) (jw' : BitVec 64), xs' = (flg', jw', ()) ∧
                                  mw' = m ∧ jw'.toNat ≤ off0.toNat + sz0.toNat ∧
                                  jw2.toNat < jw'.toNat ∧
                                  PolarWatchOk s.core jw'.toNat
                                    (off0.toNat + sz0.toNat - jw'.toNat))
                              · intro _Js ⟨flg', jw', ⟨⟩⟩ mw' hmw'
                                rcases hmw' with ⟨f', j', hxs', hmw_eq, hj_le, hj_gt, hp'⟩
                                subst mw'
                                injection hxs' with hf'; subst hf'
                                injection (by assumption : (jw', ()) = (j', ())) with hj'; subst hj'
                                simp only [Blocks.get]; rw [wp_jump]
                                exact hrecw2 (off0.toNat + sz0.toNat - jw'.toNat)
                                  (flg', jw', ()) m (by omega)
                                  ⟨flg', jw', rfl, rfl, by omega, hp'⟩
                              · intro Js hJs
                                cases hpw2_cur with
                                | empty => omega
                                | bin hw_some hbit hne hlit_lt hpw2_next =>
                                  have hld_eq := Option.some.inj
                                    ((List.getElem?_eq_getElem hjw2_lt).symm.trans hw_some)
                                  have hbit' := hld_eq.symm ▸ hbit
                                  have hval_lt : (BitVec.setWidth 64
                                      (s.core.wstk[jw2.toNat] &&& 2147483647#32)).toNat <
                                      s.core.vals.length := by
                                    rw [hld_eq, BitVec.toNat_setWidth,
                                      Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
                                    have := hlen.vals_len; have := hlen.cur_vars_le; omega
                                  have h1 : (jw2 + 1#64).toNat = jw2.toNat + 1 :=
                                    bv64_add1_toNat (by omega)
                                  have hp_next : PolarWatchOk s.core (jw2 + 1#64).toNat
                                      (off0.toNat + sz0.toNat - (jw2 + 1#64).toNat) := by
                                    rw [h1]; exact (congrArg (PolarWatchOk s.core _)
                                      (by omega)).mpr hpw2_next
                                  simp only [wp_let, Op.wp, OpCode.wp, lift2, vals, Arg.val,
                                    Ty.hasFloat]
                                  rw [wp_jnz]
                                  refine ⟨fun _ => ?_, fun hc' => by
                                    simp only [liftCmp, CmpOp.evalBits] at hc'
                                    exact False.elim (of_decide_eq_false hc' hbit')⟩
                                  apply wp_join_group (ts := [.bool]) (fun _ m' => m' = m)
                                  · intro _Js1 ⟨flg', ⟨⟩⟩ m' hm'; subst m'; simp only [Blocks.get]
                                    simp only [wp_let, Op.wp, OpCode.wp, lift2, wp_jump]
                                    exact hJs (flg', jw2 + 1#64, ()) m
                                      ⟨flg', jw2 + 1#64, rfl, rfl, by rw [h1]; omega,
                                        by rw [h1]; omega, hp_next⟩
                                  · intro Js1 hJs1; m7_to_group
                                    · apply wp_join_group (ts := [.bool]) (fun _ m' => m' = m)
                                      · intro _Js2 ⟨flg', ⟨⟩⟩ m' hm'
                                        subst m'; simp only [Blocks.get]
                                        rw [wp_jump]; exact hJs1 (flg', ()) m rfl
                                      · intro Js2 hJs2
                                        simp only [wp_let, Op.wp, OpCode.wp]
                                        repeat m7_strip
                                        rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                                        · rw [wp_jump]; exact hJs2 _ m rfl
                                        · simp only [wp_let, Op.wp, OpCode.wp]
                                          repeat m7_strip
                                          rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                                          · simp only [wp_let, Op.wp, OpCode.wp, lift2]
                                            rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
                                              (rw [wp_jump]; exact hJs2 _ m rfl)
                                          · rw [wp_jump]; exact hJs2 _ m rfl
                                    · exact hJs1 _ m rfl
                                | large hw_some hbit hpw2_next =>
                                  have hld_eq := Option.some.inj
                                    ((List.getElem?_eq_getElem hjw2_lt).symm.trans hw_some)
                                  have hbit' := hld_eq.symm ▸ hbit
                                  have h2 : (jw2 + 2#64).toNat = jw2.toNat + 2 := by
                                    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                                    simp only [Nat.reducePow, Nat.reduceMod]
                                    rw [Nat.mod_eq_of_lt (by omega)]
                                  have hp_next : PolarWatchOk s.core (jw2 + 2#64).toNat
                                      (off0.toNat + sz0.toNat - (jw2 + 2#64).toNat) := by
                                    rw [h2]; exact (congrArg (PolarWatchOk s.core _)
                                      (by omega)).mpr hpw2_next
                                  simp only [wp_let, Op.wp, OpCode.wp, lift2, vals, Arg.val,
                                    Ty.hasFloat]
                                  rw [wp_jnz]
                                  refine ⟨fun hc' => by
                                    simp only [liftCmp, CmpOp.evalBits] at hc'
                                    exact False.elim (of_decide_eq_true hc' hbit'), fun _ => ?_⟩
                                  simp only [wp_let, Op.wp, OpCode.wp, lift2, wp_jump]
                                  exact hJs (flg2, jw2 + 2#64, ()) m
                                    ⟨flg2, jw2 + 2#64, rfl, rfl, by rw [h2]; omega,
                                      by rw [h2]; omega, hp_next⟩
                          · intro _; rw [wp_jump]; exact hJw2_done _ m rfl
                        · intro Jw2l hJw2l; rw [wp_jump]
                          have hoff0_64 : (BitVec.setWidth 64 off0).toNat = off0.toNat := by
                            rw [BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (Nat.lt_trans off0.isLt (by decide))]
                          have hpw0' := hpw0
                          rw [← hoff0, ← hsz0] at hpw0'
                          exact hJw2l sz0.toNat (sn2, BitVec.setWidth 64 off0, ()) m
                            ⟨sn2, BitVec.setWidth 64 off0, rfl, rfl, by rw [hoff0_64],
                              by rw [hoff0_64]; exact hpw0'⟩
                      all_goals exact hJw2_done _ m rfl
                  · intro Jw1_done hJw1_done
                    m7_to_group
                    · apply wp_loop_group (ts := [.bool, i64])
                        (fun (wrem : Nat) xw mw => ∃ (flg : Bool) (jw : BitVec 64),
                          xw = (flg, jw, ()) ∧ mw = m ∧ jw.toNat + wrem = off1.toNat + sz1.toNat ∧
                          PolarWatchOk s.core jw.toNat wrem)
                      · intro Jw1l nw xw mw hrecw ⟨flg, jw, hxw, hmw, hjw_sum, hpw_cur⟩
                        subst hxw; subst mw; simp only [Blocks.get]
                        rw [wp_let]; simp only [Op.wp]
                        have hsum1 : off1.toNat + sz1.toNat < 2 ^ 64 := by omega
                        have hjw_end : (BitVec.setWidth 64 off1 + BitVec.setWidth 64 sz1).toNat =
                            off1.toNat + sz1.toNat := by
                          rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                            Nat.mod_eq_of_lt (Nat.lt_trans off1.isLt (by decide)),
                            Nat.mod_eq_of_lt (Nat.lt_trans sz1.isLt (by decide)),
                            Nat.mod_eq_of_lt (by omega)]
                        constructor
                        · intro hc; dsimp only [Arg.val] at hc
                          simp only [liftCmp, CmpOp.evalBits] at hc
                          have hlt : jw.toNat < off1.toNat + sz1.toNat := by
                            change decide (jw.toNat < (BitVec.setWidth 64 off1 +
                              BitVec.setWidth 64 sz1).toNat) = true at hc
                            rw [hjw_end] at hc; exact of_decide_eq_true hc
                          rw [wp_jnz]; refine ⟨fun hflg => ?_, fun hflg => ?_⟩
                          · subst hflg; rw [wp_jump]; exact hJw1_done _ m rfl
                          · have hnw : 0 < nw := by omega
                            have hjw_lt : jw.toNat < s.core.wstk.length := by
                              have := hlen.wstk_len_arr; have := hlen.wlen_le
                              rw [← hoff1, ← hsz1] at hbd1; omega
                            m7_to_group
                            apply wp_join_group (ts := [.bool, i64]) (fun xs' mw' =>
                              ∃ (flg' : Bool) (jw' : BitVec 64), xs' = (flg', jw', ()) ∧
                                mw' = m ∧ jw'.toNat ≤ off1.toNat + sz1.toNat ∧
                                jw.toNat < jw'.toNat ∧
                                PolarWatchOk s.core jw'.toNat
                                  (off1.toNat + sz1.toNat - jw'.toNat))
                            · intro _Js ⟨flg', jw', ⟨⟩⟩ mw' hmw'
                              rcases hmw' with ⟨f', j', hxs', hmw_eq, hj_le, hj_gt, hp'⟩
                              subst mw'
                              injection hxs' with hf'; subst hf'
                              injection (by assumption : (jw', ()) = (j', ())) with hj'; subst hj'
                              simp only [Blocks.get]; rw [wp_jump]
                              exact hrecw (off1.toNat + sz1.toNat - jw'.toNat)
                                (flg', jw', ()) m (by omega)
                                ⟨flg', jw', rfl, rfl, by omega, hp'⟩
                            · intro Js hJs
                              cases hpw_cur with
                              | empty => omega
                              | bin hw_some hbit hne hlit_lt hpw_next =>
                                have hld_eq := Option.some.inj
                                  ((List.getElem?_eq_getElem hjw_lt).symm.trans hw_some)
                                have hbit' := hld_eq.symm ▸ hbit
                                have hval_lt : (BitVec.setWidth 64
                                    (s.core.wstk[jw.toNat] &&& 2147483647#32)).toNat <
                                    s.core.vals.length := by
                                  rw [hld_eq, BitVec.toNat_setWidth,
                                    Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
                                  have := hlen.vals_len; have := hlen.cur_vars_le; omega
                                have h1 : (jw + 1#64).toNat = jw.toNat + 1 :=
                                  bv64_add1_toNat (by omega)
                                have hp_next : PolarWatchOk s.core (jw + 1#64).toNat
                                    (off1.toNat + sz1.toNat - (jw + 1#64).toNat) := by
                                  rw [h1]; exact (congrArg (PolarWatchOk s.core _)
                                    (by omega)).mpr hpw_next
                                simp only [wp_let, Op.wp, OpCode.wp, lift2, vals, Arg.val,
                                  Ty.hasFloat]
                                rw [wp_jnz]
                                refine ⟨fun _ => ?_, fun hc' => by
                                  simp only [liftCmp, CmpOp.evalBits] at hc'
                                  exact False.elim (of_decide_eq_false hc' hbit')⟩
                                apply wp_join_group (ts := [.bool]) (fun _ m' => m' = m)
                                · intro _Js1 ⟨flg', ⟨⟩⟩ m' hm'; subst m'; simp only [Blocks.get]
                                  simp only [wp_let, Op.wp, OpCode.wp, lift2, wp_jump]
                                  exact hJs (flg', jw + 1#64, ()) m
                                    ⟨flg', jw + 1#64, rfl, rfl, by rw [h1]; omega,
                                      by rw [h1]; omega, hp_next⟩
                                · intro Js1 hJs1; m7_to_group
                                  · apply wp_join_group (ts := [.bool]) (fun _ m' => m' = m)
                                    · intro _Js2 ⟨flg', ⟨⟩⟩ m' hm'
                                      subst m'; simp only [Blocks.get]
                                      rw [wp_jump]; exact hJs1 (flg', ()) m rfl
                                    · intro Js2 hJs2
                                      simp only [wp_let, Op.wp, OpCode.wp]
                                      repeat m7_strip
                                      rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                                      · rw [wp_jump]; exact hJs2 _ m rfl
                                      · simp only [wp_let, Op.wp, OpCode.wp]
                                        repeat m7_strip
                                        rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                                        · simp only [wp_let, Op.wp, OpCode.wp, lift2]
                                          rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
                                            (rw [wp_jump]; exact hJs2 _ m rfl)
                                        · rw [wp_jump]; exact hJs2 _ m rfl
                                  · exact hJs1 _ m rfl
                              | large hw_some hbit hpw_next =>
                                have hld_eq := Option.some.inj
                                  ((List.getElem?_eq_getElem hjw_lt).symm.trans hw_some)
                                have hbit' := hld_eq.symm ▸ hbit
                                have h2 : (jw + 2#64).toNat = jw.toNat + 2 := by
                                  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                                  simp only [Nat.reducePow, Nat.reduceMod]
                                  rw [Nat.mod_eq_of_lt (by omega)]
                                have hp_next : PolarWatchOk s.core (jw + 2#64).toNat
                                    (off1.toNat + sz1.toNat - (jw + 2#64).toNat) := by
                                  rw [h2]; exact (congrArg (PolarWatchOk s.core _)
                                    (by omega)).mpr hpw_next
                                simp only [wp_let, Op.wp, OpCode.wp, lift2, vals, Arg.val,
                                  Ty.hasFloat]
                                rw [wp_jnz]
                                refine ⟨fun hc' => by
                                  simp only [liftCmp, CmpOp.evalBits] at hc'
                                  exact False.elim (of_decide_eq_true hc' hbit'), fun _ => ?_⟩
                                simp only [wp_let, Op.wp, OpCode.wp, lift2, wp_jump]
                                exact hJs (flg, jw + 2#64, ()) m
                                  ⟨flg, jw + 2#64, rfl, rfl, by rw [h2]; omega,
                                    by rw [h2]; omega, hp_next⟩
                        · intro _; rw [wp_jump]; exact hJw1_done _ m rfl
                      · intro Jw1l hJw1l; rw [wp_jump]
                        have hoff1_64 : (BitVec.setWidth 64 off1).toNat = off1.toNat := by
                          rw [BitVec.toNat_setWidth,
                            Nat.mod_eq_of_lt (Nat.lt_trans off1.isLt (by decide))]
                        have hpw1' := hpw1
                        rw [← hoff1, ← hsz1] at hpw1'
                        exact hJw1l sz1.toNat (sp2, BitVec.setWidth 64 off1, ()) m
                          ⟨sp2, BitVec.setWidth 64 off1, rfl, rfl, by rw [hoff1_64],
                            by rw [hoff1_64]; exact hpw1'⟩
                    all_goals exact hJw1_done _ m rfl
                · exact hJ2next (sp2, sn2, ()) m rfl
              · exact hJ2next (sp2, sn2, ()) m rfl
          · intro J2b hJ2b
            m7_to_group <;> first | exact hJret () m rfl | exact hJ2b () m rfl
        · m7_to_group; exact hJret () m rfl
    · intro J2 hJ2; rw [wp_jump]
      exact hJ2 s.core.cur_vars (sp, sn, 0#64, ()) m ⟨sp, sn, 0#64, rfl, rfl, rfl, Nat.zero_le _⟩
  · intro J0 hJ0
    m7_to_group
    apply wp_loop_group (ts := [.bool, .bool, i64])
      (fun (r_rem : Nat) xs m' => ∃ (sp sn : Bool) (r : BitVec 64),
        xs = (sp, sn, r, ()) ∧ m' = m ∧ r_rem = s.core.arena_len - r.toNat ∧
        r.toNat ≤ s.core.arena_len ∧
        (r.toNat = s.core.arena_len ∨ r.toNat ∈ fullArenaClauseRefsCore s.core))
    · intro J n xs m' hrec ⟨sp, sn, r, hxs, hm', hn, hr_le, hr⟩
      subst hxs; subst m'; simp only [Blocks.get]; try dsimp only
      rcases hr with hr_eq | hr_mem
      · m7_to_group <;> first
          | exact hJ0 _ m rfl
          | (exfalso
             have : r.toNat < s.core.arena_len % 2 ^ 64 := by assumption
             rw [hr_eq, Nat.mod_eq_of_lt (by omega)] at this; omega)
      · have hwf := hwe.arena.refs_wf r.toNat hr_mem
        have hr_lt0 : r.toNat < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        have hr_lt2 : (r + 2#64).toNat < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          simp only [Nat.reducePow, Nat.reduceMod]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        m7_to_group
        · apply wp_join_group (ts := []) (fun _ m2 => m2 = m)
          · intro _Jbody ⟨⟩ m2 hm2; rw [hm2]; clear hm2 m2; simp only [Blocks.get]; try dsimp only
            m7_to_group
            let nxt := fullArenaNextOff s.core.arena s.core.arena_len r.toNat
            have hr32 : (BitVec.setWidth 32 r).toNat = r.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            refine ⟨fun res m4 => res = (BitVec.ofNat 32 nxt, ()) ∧ m4 = m, X,
              hNext (c.hdr, BitVec.setWidth 32 r, ()) m _ X
                ⟨c, s, R, rfl, hlen_all, hm, ⟨by rw [hr32], rfl⟩⟩, ?_, fun _ _ _ _ => id⟩
            rintro ⟨r32, ⟨⟩⟩ m4 ⟨hr32_eq, hm4⟩; rw [hm4]; clear hm4 m4
            injection hr32_eq with hr32_eq; subst r32
            simp only [wp_let, Op.wp, OpCode.wp]
            refine m7_strip_32_64 ?_
            have hnxt_eq : (BitVec.setWidth 64 (BitVec.ofNat 32 nxt)).toNat = nxt := by
              have := hwf.2.2.2.1
              rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            have hnxt_mem : nxt = s.core.arena_len ∨ nxt ∈ fullArenaClauseRefsCore s.core :=
              fullArenaScanRefs_next_mem s.core.arena s.core.arena_len s.core.arena_len 0
                r.toNat (Nat.le_refl _)
                (fun p hp => by
                  have hpwf := hwe.arena.refs_wf p hp
                  exact ⟨Nat.le_trans (by omega) hpwf.2.2.1, hpwf.2.2.2.2⟩)
                hr_mem
            apply wp_join_group (ts := [.bool, .bool]) (fun _ m5 => m5 = m)
            · intro _Jn ⟨sp', sn', ⟨⟩⟩ m5 hm5; rw [hm5]; clear hm5 m5; simp only [Blocks.get]
              simp only [wp_let, Op.wp, OpCode.wp]
              rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
              · rw [wp_jump]
                first
                | exact hJ0 (sp', sn', r, ()) m rfl
                | exact hrec (s.core.arena_len - nxt)
                    (sp', sn', BitVec.setWidth 64 (BitVec.ofNat 32 nxt), ()) m
                    (by have := hwf.2.2.1; have := hwf.1; omega)
                    ⟨sp', sn', BitVec.setWidth 64 (BitVec.ofNat 32 nxt), rfl, rfl,
                      by rw [hnxt_eq], by rw [hnxt_eq]; exact hwf.2.2.2.1,
                      by rw [hnxt_eq]; exact hnxt_mem⟩
            · intro Jn hJn; m7_to_group
              apply wp_join_group (ts := [.bool, .bool]) (fun _ m5 => m5 = m)
              · intro _Jn2 ⟨sp', sn', ⟨⟩⟩ m5 hm5; rw [hm5]; clear hm5 m5
                simp only [Blocks.get]; rw [wp_jump]; exact hJn (sp', sn', ()) m rfl
              · intro Jn2 hJn2; m7_to_group
                {
                have hsz_eq : (s.core.arena[(r + 2#64).toNat]).toNat =
                    fullArenaClauseSizeCore s.core r.toNat := by
                  have hr2_eq : (r + 2#64).toNat = r.toNat + 2 := by
                    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                    simp only [Nat.reducePow, Nat.reduceMod]
                    rw [Nat.mod_eq_of_lt (by omega)]
                  have ha : s.core.arena[r.toNat + 2]? =
                      some s.core.arena[(r + 2#64).toNat] := by
                    rw [← hr2_eq]; exact List.getElem?_eq_getElem hr_lt2
                  dsimp only [fullArenaClauseSizeCore]; rw [ha]; rfl
                have hgarb_false : fullArenaClauseGarbCore s.core r.toNat = false := by
                  have ha : s.core.arena[r.toNat]? = some s.core.arena[r.toNat] :=
                    List.getElem?_eq_getElem hr_lt0
                  dsimp [fullArenaClauseGarbCore, fullArenaHdrCore]
                  rw [ha]; simp; assumption
                apply wp_join_group (ts := [.bool, .bool, .bool, i32])
                  (fun _ m5 => m5 = m)
                · intro _Jpost ⟨sat', any', _skip', _j', ⟨⟩⟩ m5 hm5
                  rw [hm5]; clear hm5 m5; simp only [Blocks.get]; m7_to_group
                  apply wp_join_group (ts := [.bool, .bool]) (fun _ m6 => m6 = m)
                  · intro _Jn3 ⟨sp', sn', ⟨⟩⟩ m6 hm6; rw [hm6]; clear hm6 m6
                    simp only [Blocks.get, wp_jump]; exact hJn2 (sp', sn', ()) m rfl
                  · intro Jn3 hJn3
                    rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                    · rw [wp_jump]; exact hJn3 (sp, sn, ()) m rfl
                    · apply wp_join_group (ts := [.bool]) (fun _ m6 => m6 = m)
                      · intro _Jsp ⟨sp', ⟨⟩⟩ m6 hm6; rw [hm6]; clear hm6 m6
                        simp only [Blocks.get]
                        apply wp_join_group (ts := [.bool]) (fun _ m6 => m6 = m)
                        · intro _Jsn ⟨sn', ⟨⟩⟩ m6 hm6; rw [hm6]; clear hm6 m6
                          simp only [Blocks.get, wp_jump]; exact hJn3 (sp', sn', ()) m rfl
                        · intro Jsn hJsn
                          rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
                            (rw [wp_jump]; exact hJsn _ m rfl)
                      · intro Jsp hJsp
                        rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
                          (rw [wp_jump]; exact hJsp _ m rfl)
                · intro Jpost hJpost; m7_to_group
                  apply wp_loop_group (ts := [.bool, .bool, i32])
                    (fun (jrem : Nat) xj mj => ∃ (sat? any? : Bool) (j : BitVec 32),
                      xj = (sat?, any?, j, ()) ∧ mj = m ∧
                      jrem = fullArenaClauseSizeCore s.core r.toNat - j.toNat ∧
                      j.toNat ≤ fullArenaClauseSizeCore s.core r.toNat)
                  · intro Jj nj xj mj hrecj ⟨sat?, any?, j, hxj, hmj, hnj, hj_le⟩
                    subst hxj; subst mj; simp only [Blocks.get]
                    rw [wp_let]; simp only [Op.wp]
                    constructor
                    · intro hc
                      have hlt :
                          decide (j.toNat < s.core.arena[(r + 2#64).toNat].toNat) =
                            true := hc
                      have hj : j.toNat < fullArenaClauseSizeCore s.core r.toNat := by
                        rw [← hsz_eq]; exact of_decide_eq_true hlt
                      have hj_ar :
                          (r + 3#64 + BitVec.setWidth 64 j).toNat <
                            s.core.arena.length := by
                        have := hlen.arena_len_le; have := hlen.arena_len_arr
                        have := hwf.2.2.1
                        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
                          BitVec.toNat_ofNat,
                          Nat.mod_eq_of_lt (Nat.lt_trans j.isLt (by decide))]
                        simp only [Nat.reducePow, Nat.reduceMod]
                        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                        omega
                      m7_to_group
                      apply wp_join_group (ts := [.bool, .bool, .bool])
                        (fun _ m4 => m4 = m)
                      · intro _Jjnext ⟨_broke, ap', an', ⟨⟩⟩ m4 hm4
                        rw [hm4]; clear hm4 m4; simp only [Blocks.get]
                        simp only [wp_let, Op.wp, OpCode.wp, lift2, wp_jump]
                        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
                          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                          simp only [Nat.reducePow, Nat.reduceMod]
                          rw [Nat.mod_eq_of_lt (by omega)]
                        exact hrecj
                          (fullArenaClauseSizeCore s.core r.toNat - (j + 1#32).toNat)
                          (ap', an', j + 1#32, ()) m (by omega)
                          ⟨ap', an', j + 1#32, rfl, rfl, rfl, by omega⟩
                      · intro Jjnext hJjnext
                        have h_ar_idx : (r + 3#64 + BitVec.setWidth 64 j).toNat =
                            r.toNat + 3 + j.toNat := by
                          rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
                            BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (Nat.lt_trans j.isLt (by decide))]
                          simp only [Nat.reducePow, Nat.reduceMod]
                          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                        have hlit_mem :
                            s.core.arena[(r + 3#64 + BitVec.setWidth 64 j).toNat].toNat ∈
                              fullArenaClauseLitsCore s.core r.toNat := by
                          simp only [h_ar_idx]
                          exact arena_lit_mem_clauseLits s.core r.toNat j.toNat hj
                            (h_ar_idx ▸ hj_ar)
                        have hlit_lt : (BitVec.setWidth 64
                            s.core.arena[(r + 3#64 + BitVec.setWidth 64 j).toNat]).toNat <
                            s.core.vals.length := by
                          have := hwe.arena.lits_lt r.toNat hr_mem hgarb_false _ hlit_mem
                          have := hlen.vals_len; have := hlen.cur_vars_le
                          rw [BitVec.toNat_setWidth,
                            Nat.mod_eq_of_lt (Nat.lt_trans
                              (s.core.arena[(r + 3#64 +
                                BitVec.setWidth 64 j).toNat]).isLt (by decide))]
                          omega
                        m7_to_group
                        m7_split
                        · exact hJpost (true, sat?, any?, j, ()) m rfl
                        · apply wp_join_group (ts := [.bool, .bool])
                            (fun _ m' => m' = m)
                          · intro _Js ⟨ap', an', ⟨⟩⟩ m' hm'; subst m'
                            simp only [Blocks.get, wp_jump]
                            exact hJjnext (false, ap', an', ()) m rfl
                          · intro Js hJs
                            simp only [wp_let, Op.wp, OpCode.wp]
                            repeat m7_strip
                            rw [wp_jnz]; refine ⟨fun _ => ?_, fun _ => ?_⟩
                            · apply wp_join_group (ts := [.bool, .bool])
                                (fun _ m' => m' = m)
                              · intro _Js2 ⟨ap', an', ⟨⟩⟩ m' hm'; subst m'
                                simp only [Blocks.get, wp_jump]
                                exact hJs (ap', an', ()) m rfl
                              · intro Js2 hJs2
                                simp only [wp_let, Op.wp, OpCode.wp, lift2]
                                rw [wp_jnz]
                                refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
                                  (rw [wp_jump]; exact hJs2 _ m rfl)
                            · rw [wp_jump]; exact hJs _ m rfl
                        · exact hJjnext (false, sat?, any?, ()) m rfl
                    · intro _; rw [wp_jump]
                      exact hJpost (false, sat?, any?, j, ()) m rfl
                  · intro Jj hJj; rw [wp_jump]
                    exact hJj (fullArenaClauseSizeCore s.core r.toNat)
                      (false, false, 0#32, ()) m
                      ⟨false, false, 0#32, rfl, rfl, rfl, Nat.zero_le _⟩ }
                all_goals exact hJn2 (sp, sn, ()) m rfl
          · intro Jbody hJbody
            m7_to_group <;>
              (try rw [wp_jump]) <;>
              first | exact hJbody () m rfl | exact hJ0 _ m rfl
    · intro J hJ; rw [wp_jump]
      have h0 : 0 = s.core.arena_len ∨ 0 ∈ fullArenaClauseRefsCore s.core := by
        rcases hwe.arena.len_ok with h0 | h3
        · exact Or.inl h0.symm
        · right; unfold fullArenaClauseRefsCore
          cases al : s.core.arena_len with
          | zero => omega
          | succ _ => rw [fullArenaScanRefs_succ]; simp [← al, h3]
      exact hJ s.core.arena_len (false, false, 0#64, ()) m
        ⟨false, false, 0#64, rfl, rfl, rfl, Nat.zero_le _, h0⟩

theorem full_randec_step_m7_wp (Γ : Env)
    (hInit : EnvSpec Γ "full_m7_state_init" m7StateInitSpec)
    (hGet : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec) :
    ∀ a m Q X, m7RandecStepSpec a m Q X → Func.wp Γ full_randec_step_m7_body a m Q X := by
  intro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, s, R, rfl, hlen, hm, hQ⟩ := m7RandecStepSpec_elim hspec
  unfold Func.wp full_randec_step_m7_body
  m7_step_init hlen, hm, hInit, h0, hi0, hp0, m0, hm0
  let s0 : FullState :=
    { s with scratch := { s.scratch with glue_used := m7StateInitGu s.scratch } }
  m7_step_get64 h0, hm0, hGet, rem
  m7_split
  · m7_step_set64 h0, hm0, hSet, h1, m1, hm1
    m7_step_set64 h1, hm1, hSet, h2, m2, hm2
    m7_steps
    let s1 : FullState :=
      { s with
        scratch :=
          { s.scratch with
            glue_used := m7Set64List (m7StateInitGu s.scratch) m7GuRandecRemIdx
              (m7Get64Val (m7StateInitGu s.scratch) m7GuRandecRemIdx - 1#64) } }
    let s2 : FullState :=
      { s with
        scratch :=
          { s.scratch with
            glue_used := m7Set64List s1.scratch.glue_used m7GuRandecConflIdx s.scratch.conflicts } }
    have hp1 : M7GuPrefixPres s s1 :=
      M7GuPrefixPres.trans hp0
        (M7GuPrefixPres.of_set64 _ (by rw [m7GuRandecRemIdx_eq]; decide))
    have hp2 : M7GuPrefixPres s s2 :=
      M7GuPrefixPres.trans hp1
        (M7GuPrefixPres.of_set64 _ (by rw [m7GuRandecConflIdx_eq]; decide))
    have hi1 : M7StateInitOk s1.scratch.glue_used :=
      M7StateInitOk.of_set64 hi0 (by rw [m7GuRandecRemIdx_eq]; decide) _
    have hi2 : M7StateInitOk s2.scratch.glue_used :=
      M7StateInitOk.of_set64 hi1 (by rw [m7GuRandecConflIdx_eq]; decide) _
    exact hQ s2 m2 rfl h2 ⟨probePres_refl _, hp2, hi2, s2.scratch.glue_used, rfl⟩ hm2
  · m7_step_set64 h0, hm0, hSet, h1, m1, hm1
    m7_steps
    let s1 : FullState :=
      { s with
        scratch :=
          { s.scratch with
            glue_used := m7Set64List (m7StateInitGu s.scratch) m7GuRandecConflIdx
              s.scratch.conflicts } }
    have hp1 : M7GuPrefixPres s s1 :=
      M7GuPrefixPres.trans hp0
        (M7GuPrefixPres.of_set64 _ (by rw [m7GuRandecConflIdx_eq]; decide))
    have hi1 : M7StateInitOk s1.scratch.glue_used :=
      M7StateInitOk.of_set64 hi0 (by rw [m7GuRandecConflIdx_eq]; decide) _
    exact hQ s1 m1 rfl h1 ⟨probePres_refl _, hp1, hi1, s1.scratch.glue_used, rfl⟩ hm1


end LeanQbe.T.Examples.Kissat.FullM7Search
