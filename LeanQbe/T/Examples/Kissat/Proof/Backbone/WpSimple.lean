/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Backbone WP Proofs — Simple Helpers (`Proof.Backbone.WpSimple`)

Canonical `(Γ : Env)` `Func.wp` proofs (`0` `@[expose]` on theorems/lemmas) for:
1. `full_backbone_sched_m6_wp` (`fullBackboneSchedM6Spec`)
2. `full_backbone_keep_m6_wp` (`fullBackboneKeepM6Spec`)
3. `full_backbone_unwind_m6_wp` (`fullBackboneUnwindM6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backbone

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Backbone
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

/-! ## 1. File-Local Step Helpers & Scheduling Predicates -/

private theorem bb_strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem bb_strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem bb_strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "bb_strip" : tactic =>
  `(tactic| first
    | apply bb_strip_le_32_64 | apply bb_strip_le_8_32 | apply bb_strip_le_8_64)
local macro "bb_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
local macro "bb_step" : tactic => `(tactic| ((try bb_unmdata); (repeat bb_strip); c0_step))
local macro "bb_steps" : tactic =>
  `(tactic| (
      (try bb_unmdata)
      (repeat bb_strip)
      c0_steps
      repeat (any_goals (bb_strip; repeat bb_strip); c0_steps)))

open Lean Elab Tactic in
local elab "bb_to_group" : tactic => do
  evalTactic (← `(tactic| ((try bb_unmdata); (repeat bb_strip))))
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

private def bbPrio (fl : List (BitVec 32)) (vals : List (BitVec 8)) (u : Nat) : Nat :=
  if (fl[u]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧ vals[2 * u]?.getD 0#8 = 0#8 then
    (if (fl[u]?.getD 0#32 &&& 128#32) ≠ 0#32 then 1 else 0) +
    (if (fl[u]?.getD 0#32 &&& 256#32) ≠ 0#32 then 1 else 0)
  else 0

private def bbUnprio (fl : List (BitVec 32)) (vals : List (BitVec 8)) (u : Nat) : Nat :=
  if (fl[u]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧ vals[2 * u]?.getD 0#8 = 0#8 then
    (if (fl[u]?.getD 0#32 &&& 128#32) = 0#32 then 1 else 0) +
    (if (fl[u]?.getD 0#32 &&& 256#32) = 0#32 then 1 else 0)
  else 0

private def bbSumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => bbSumTo f k + f k

private theorem bbPrio_add_unprio_le (fl : List (BitVec 32)) (vals : List (BitVec 8)) (u : Nat) :
    bbPrio fl vals u + bbUnprio fl vals u ≤ 2 := by
  unfold bbPrio bbUnprio
  by_cases h1 : (fl[u]?.getD 0#32 &&& 1#32) = 0#32 <;>
  by_cases hv : vals[2 * u]?.getD 0#8 = 0#8 <;>
  by_cases h0 : (fl[u]?.getD 0#32 &&& 128#32) = 0#32 <;>
  by_cases h2 : (fl[u]?.getD 0#32 &&& 256#32) = 0#32 <;>
  simp [h1, hv, h0, h2]

private theorem bbSumTo_prio_unprio_le (fl : List (BitVec 32)) (vals : List (BitVec 8)) :
    ∀ n : Nat, bbSumTo (bbPrio fl vals) n + bbSumTo (bbUnprio fl vals) n ≤ 2 * n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    have ih := bbSumTo_prio_unprio_le fl vals n
    have h1 := bbPrio_add_unprio_le fl vals n
    simp only [bbSumTo]; omega

private theorem bbSumTo_mono (f : Nat → Nat) {a b : Nat} (hle : a ≤ b) :
    bbSumTo f a ≤ bbSumTo f b := by
  induction hle with
  | refl => exact Nat.le_refl _
  | @step m _ ih => simp only [bbSumTo]; omega

private theorem bb_sext32_eq0_imp : ∀ x : BitVec 8, x.signExtend 32 = 0#32 → x = 0#8 := by
  decide

private theorem bb_fullMem_symm {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m) (h : s1 = s2) : (FullMem c s2 ⋆ R) m := h ▸ hm

/-! ## 2. `full_backbone_sched_m6_wp` (`fullBackboneSchedM6Spec`) -/

theorem full_backbone_sched_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackboneSchedM6Spec a m Q X →
      Func.wp Γ full_backbone_sched_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hm0, hQ⟩
  have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hfl_len := hcl.flags_len
  have hvals_len := hcl.vals_len; have hws1_len := hscl.work_stk1_len
  let fl := s.core.flags
  let vals := s.core.vals
  have hfl_l : fl.length = c.max_vars := hfl_len
  have hvals_l : vals.length = 2 * c.max_vars := hvals_len
  unfold Func.wp full_backbone_sched_m6_body
  bb_to_group
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (cand_n, not_resched, v, ()) m1 =>
      ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
        v.toNat ≤ s.core.cur_vars ∧
        cand_n.toNat = bbSumTo (bbPrio fl vals) v.toNat ∧
        not_resched.toNat = bbSumTo (bbUnprio fl vals) v.toNat ∧
        (∀ i < cand_n.toNat, (ws1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
    (fun (_, _, v, ()) _ => s.core.cur_vars - v.toNat) ?_ ?_
  · intro J1 hJ1; bb_steps
    exact hJ1 (0#64, 0#64, 0#64, ()) m0 ⟨s.scratch.work_stk1, hws1_len, Nat.zero_le _,
      rfl, rfl, (fun _ h => by cases h), hm0⟩
  · rintro J1 ⟨cand_n, not_resched, v, ⟨⟩⟩ m1 ⟨ws1, hws1, hv_le, hcn_eq, hnr_eq, hlt1, hm1⟩ ih1
    have hsum_v := bbSumTo_prio_unprio_le fl vals v.toNat
    bb_step; bb_step
    · have hv_lt : v.toNat < s.core.cur_vars := by
        have h1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt (by omega)] at h1
      have hv_fl : v.toNat < fl.length := by omega
      have hv1_eq : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
      have hv2_eq : (v <<< (BitVec.signExtend 64 1#32)).toNat = 2 * v.toNat :=
        bb_bv64_shl1_sext v (by omega)
      have hv2_lt : (v <<< (BitVec.signExtend 64 1#32)).toNat < vals.length := by omega
      have hv2_lt' : 2 * v.toNat < vals.length := by omega
      have hfl_get : fl[v.toNat]?.getD 0#32 = fl[v.toNat]'hv_fl := by
        rw [List.getElem?_eq_getElem hv_fl, Option.getD_some]
      have hval_get : vals[2 * v.toNat]?.getD 0#8 = vals[2 * v.toNat]'hv2_lt' := by
        rw [List.getElem?_eq_getElem hv2_lt', Option.getD_some]
      bb_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (cn', nr', ()) m2 => ∃ ws1' : List (BitVec 32), ws1'.length = 2 * c.max_vars ∧
          cn'.toNat = bbSumTo (bbPrio fl vals) (v.toNat + 1) ∧
          nr'.toNat = bbSumTo (bbUnprio fl vals) (v.toNat + 1) ∧
          (∀ i < cn'.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m2)
        (fun _ ⟨cn', nr', ⟨⟩⟩ m2 ⟨ws1', hws1', hcn', hnr', hlt', hm2⟩ => by
          bb_steps
          exact ih1 (cn', nr', v + 1#64, ()) m2 (by dsimp only; omega)
            ⟨ws1', hws1', by omega, by rw [hv1_eq]; exact hcn', by rw [hv1_eq]; exact hnr',
             hlt', hm2⟩)
        (fun Jn hJn => by
          bb_to_group
          · have hact : (fl[v.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 := by
              rw [hfl_get]; exact by assumption
            have hval0 : vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
              have h0 : (vals[(v <<< BitVec.signExtend 64 1#32).toNat]'hv2_lt).signExtend 32 =
                  0#32 := by
                simpa using (by assumption :
                  (vals[(v <<< BitVec.signExtend 64 1#32).toNat]'hv2_lt).signExtend 32 =
                    ((0 : BitVec 32).setWidth 8).signExtend 32)
              have h1 := bb_sext32_eq0_imp _ h0
              rw [hval_get, ← m6_getElem_congr hv2_eq hv2_lt hv2_lt']; exact h1
            have hcond : (fl[v.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                vals[2 * v.toNat]?.getD 0#8 = 0#8 := ⟨hact, hval0⟩
            have hprio_eq : bbPrio fl vals v.toNat =
                (if (fl[v.toNat]?.getD 0#32 &&& 128#32) ≠ 0#32 then 1 else 0) +
                (if (fl[v.toNat]?.getD 0#32 &&& 256#32) ≠ 0#32 then 1 else 0) := by
              unfold bbPrio; rw [ite_eq_left hcond]
            have hunprio_eq : bbUnprio fl vals v.toNat =
                (if (fl[v.toNat]?.getD 0#32 &&& 128#32) = 0#32 then 1 else 0) +
                (if (fl[v.toNat]?.getD 0#32 &&& 256#32) = 0#32 then 1 else 0) := by
              unfold bbUnprio; rw [ite_eq_left hcond]
            refine wp_join_group (ts := [i64, i64])
              (fun (cn1, nr1, ()) m_a => ∃ ws1_a : List (BitVec 32),
                ws1_a.length = 2 * c.max_vars ∧
                cn1.toNat = cand_n.toNat +
                  (if (fl[v.toNat]?.getD 0#32 &&& 128#32) ≠ 0#32 then 1 else 0) ∧
                nr1.toNat = not_resched.toNat +
                  (if (fl[v.toNat]?.getD 0#32 &&& 128#32) = 0#32 then 1 else 0) ∧
                (∀ i < cn1.toNat, (ws1_a[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1_a } } ⋆ R) m_a)
              (fun _ ⟨cn1, nr1, ⟨⟩⟩ m_a ⟨ws1_a, hws1_a, hcn1, hnr1, hlta, hma⟩ => by
                refine wp_join_group (ts := [i64, i64])
                  (fun (cn2, nr2, ()) m_b => ∃ ws1_b : List (BitVec 32),
                    ws1_b.length = 2 * c.max_vars ∧
                    cn2.toNat = bbSumTo (bbPrio fl vals) (v.toNat + 1) ∧
                    nr2.toNat = bbSumTo (bbUnprio fl vals) (v.toNat + 1) ∧
                    (∀ i < cn2.toNat, (ws1_b[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1_b } } ⋆ R) m_b)
                  (fun _ ⟨cn2, nr2, ⟨⟩⟩ m_b h => hJn (cn2, nr2, ()) m_b h)
                  (fun Jb hJb => by
                    have hcn1_le : cn1.toNat ≤ 2 * v.toNat + 1 := by
                      split at hcn1 <;> omega
                    have hnr1_le : nr1.toNat ≤ 2 * v.toNat + 1 := by
                      split at hnr1 <;> omega
                    have hcn1_lt : cn1.toNat < ws1_a.length := by omega
                    have hcn1_1 : (cn1 + 1#64).toNat = cn1.toNat + 1 := by bv_omega
                    have hnr1_1 : (nr1 + 1#64).toNat = nr1.toNat + 1 := by bv_omega
                    have hl1_lt :
                        (((v <<< (BitVec.signExtend 64 1#32)) ||| 1#64).truncate 32).toNat <
                          2 * s.core.cur_vars := bb_bv64_shl1_sext_or1_tr v hv_lt (by omega)
                    bb_steps
                    · have hb1 : (fl[v.toNat]?.getD 0#32 &&& 256#32) ≠ 0#32 := by
                        rw [hfl_get]; exact by assumption
                      refine hJb (cn1 + 1#64, nr1, ()) _ ⟨_, by simp [hws1_a], ?_, ?_,
                        fun i hi => ?_, hm⟩
                      · rw [bbSumTo, hprio_eq, ite_eq_left hb1, hcn1_1, hcn1, hcn_eq]; omega
                      · rw [bbSumTo, hunprio_eq, ite_eq_right hb1, hnr1, hnr_eq]; omega
                      · rcases (by omega : i < cn1.toNat ∨ i = cn1.toNat) with hi' | rfl
                        · rw [List.getElem?_set_ne (by omega)]; exact hlta i hi'
                        · rw [List.getElem?_set_self hcn1_lt, Option.getD_some]; exact hl1_lt
                    · have hb1 : (fl[v.toNat]?.getD 0#32 &&& 256#32) = 0#32 := by
                        rw [hfl_get]; exact by assumption
                      refine hJb (cn1, nr1 + 1#64, ()) m_a ⟨ws1_a, hws1_a, ?_, ?_, hlta, hma⟩
                      · simp only [bbSumTo, hprio_eq, hb1, ne_eq, not_true_eq_false, ↓reduceIte,
                          hcn1, hcn_eq]; omega
                      · rw [bbSumTo, hunprio_eq, ite_eq_left hb1, hnr1_1, hnr1, hnr_eq]; omega))
              (fun Ja hJa => by
                have hcn_lt : cand_n.toNat < ws1.length := by omega
                have hcn_1 : (cand_n + 1#64).toNat = cand_n.toNat + 1 := by bv_omega
                have hnr_1 : (not_resched + 1#64).toNat = not_resched.toNat + 1 := by bv_omega
                have hl0_lt :
                    ((v <<< (BitVec.signExtend 64 1#32)).truncate 32).toNat <
                      2 * s.core.cur_vars := bb_bv64_shl1_sext_tr v hv_lt (by omega)
                bb_steps
                · have hb0 : (fl[v.toNat]?.getD 0#32 &&& 128#32) ≠ 0#32 := by
                    rw [hfl_get]; exact by assumption
                  refine hJa (cand_n + 1#64, not_resched, ()) _ ⟨_, by simp [hws1],
                    by simp [hb0, hcn_1], by simp [hb0], fun i hi => ?_, hm⟩
                  rcases (by omega : i < cand_n.toNat ∨ i = cand_n.toNat) with hi' | rfl
                  · rw [List.getElem?_set_ne (by omega)]; exact hlt1 i hi'
                  · rw [List.getElem?_set_self hcn_lt, Option.getD_some]; exact hl0_lt
                · have hb0 : (fl[v.toNat]?.getD 0#32 &&& 128#32) = 0#32 := by
                    rw [hfl_get]; exact by assumption
                  exact hJa (cand_n, not_resched + 1#64, ()) m1 ⟨ws1, hws1,
                    by simp [hb0], by simp [hb0, hnr_1], hlt1, hm1⟩)
          · have hval_ne : vals[2 * v.toNat]?.getD 0#8 ≠ 0#8 := by
              intro hz
              rw [hval_get, ← m6_getElem_congr hv2_eq hv2_lt hv2_lt'] at hz
              have hne : (vals[(v <<< BitVec.signExtend 64 1#32).toNat]'hv2_lt).signExtend 32 ≠
                  ((0 : BitVec 32).setWidth 8).signExtend 32 := by assumption
              rw [hz] at hne; exact hne rfl
            have hnc : ¬ ((fl[v.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                vals[2 * v.toNat]?.getD 0#8 = 0#8) := fun h => hval_ne h.2
            exact hJn (cand_n, not_resched, ()) m1 ⟨ws1, hws1,
              by simp only [bbSumTo, bbPrio, hnc, ↓reduceIte, Nat.add_zero]; exact hcn_eq,
              by simp only [bbSumTo, bbUnprio, hnc, ↓reduceIte, Nat.add_zero]; exact hnr_eq,
              hlt1, hm1⟩
          · have hnact : ¬ ((fl[v.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                vals[2 * v.toNat]?.getD 0#8 = 0#8) := fun h => by
              rw [hfl_get] at h; exact h.1 (by assumption)
            exact hJn (cand_n, not_resched, ()) m1 ⟨ws1, hws1,
              by simp only [bbSumTo, bbPrio, hnact, ↓reduceIte, Nat.add_zero]; exact hcn_eq,
              by simp only [bbSumTo, bbUnprio, hnact, ↓reduceIte, Nat.add_zero]; exact hnr_eq,
              hlt1, hm1⟩)
    · have hv_eq : v.toNat = s.core.cur_vars := by
        have h1 : ¬ v.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
        rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
      have htot_le : cand_n.toNat + bbSumTo (bbUnprio fl vals) s.core.cur_vars ≤
          2 * s.core.cur_vars := by
        rw [hcn_eq, hv_eq]; exact bbSumTo_prio_unprio_le fl vals s.core.cur_vars
      clear hc ih1 J1
      bb_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (cn_f, _, ()) mf => ∃ ws1' : List (BitVec 32),
          ws1'.length = 2 * c.max_vars ∧
          cn_f.toNat ≤ 2 * s.core.cur_vars ∧
          (∀ i < cn_f.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) mf)
        (fun _ ⟨cn_f, _, ⟨⟩⟩ mf ⟨ws1', hws1', hcn_f, hlt_f, hmf⟩ => by
          bb_steps
          exact hQ cn_f s.core.flags ws1' mf (bb_sparseW_with_ws1 hsp hws1') hcn_f hlt_f hmf)
        (fun Jf hJf => by
          bb_step; bb_step
          · refine wp_loop_inv (ts := [i64, i64])
              (fun (cn2, v2, ()) m2 => ∃ ws2 : List (BitVec 32),
                ws2.length = 2 * c.max_vars ∧
                v2.toNat ≤ s.core.cur_vars ∧
                cn2.toNat = cand_n.toNat + bbSumTo (bbUnprio fl vals) v2.toNat ∧
                (∀ i < cn2.toNat, (ws2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                (FullMem c { s with scratch := { s.scratch with work_stk1 := ws2 } } ⋆ R) m2)
              (fun (_, v2, ()) _ => s.core.cur_vars - v2.toNat) ?_ ?_
            · intro J2 hJ2; bb_steps
              exact hJ2 (cand_n, 0#64, ()) m1 ⟨ws1, hws1, Nat.zero_le _, by simp [bbSumTo],
                hlt1, hm1⟩
            · rintro J2 ⟨cn2, v2, ⟨⟩⟩ m2 ⟨ws2, hws2, hv2_le, hcn2_eq, hlt2, hm2⟩ ih2
              bb_step; bb_step
              · have hv2_lt : v2.toNat < s.core.cur_vars := by
                  have h1 : v2.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
                  rwa [Nat.mod_eq_of_lt (by omega)] at h1
                have hv2_fl : v2.toNat < fl.length := by omega
                have hv2_1 : (v2 + 1#64).toNat = v2.toNat + 1 := by bv_omega
                have hv2_shl : (v2 <<< (BitVec.signExtend 64 1#32)).toNat = 2 * v2.toNat :=
                  bb_bv64_shl1_sext v2 (by omega)
                have hv2_val : (v2 <<< (BitVec.signExtend 64 1#32)).toNat < vals.length := by
                  omega
                have hv2_val' : 2 * v2.toNat < vals.length := by omega
                have hfl2_get : fl[v2.toNat]?.getD 0#32 = fl[v2.toNat]'hv2_fl := by
                  rw [List.getElem?_eq_getElem hv2_fl, Option.getD_some]
                have hval2_get : vals[2 * v2.toNat]?.getD 0#8 = vals[2 * v2.toNat]'hv2_val' := by
                  rw [List.getElem?_eq_getElem hv2_val', Option.getD_some]
                have hsum_next : cand_n.toNat + bbSumTo (bbUnprio fl vals) (v2.toNat + 1) ≤
                    2 * s.core.cur_vars :=
                  Nat.le_trans (Nat.add_le_add_left
                    (bbSumTo_mono (bbUnprio fl vals) (by omega)) _) htot_le
                have hcn2_add_u : cn2.toNat + bbUnprio fl vals v2.toNat ≤
                    2 * s.core.cur_vars := by
                  rw [hcn2_eq]; simpa only [bbSumTo, Nat.add_assoc] using hsum_next
                bb_to_group
                refine wp_join_group (ts := [i64])
                  (fun (cn3, ()) m3 => ∃ ws3 : List (BitVec 32),
                    ws3.length = 2 * c.max_vars ∧
                    cn3.toNat = cand_n.toNat +
                      bbSumTo (bbUnprio fl vals) (v2.toNat + 1) ∧
                    (∀ i < cn3.toNat, (ws3[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws3 } } ⋆ R) m3)
                  (fun _ ⟨cn3, ⟨⟩⟩ m3 ⟨ws3, hws3, hcn3, hlt3, hm3⟩ => by
                    bb_steps
                    exact ih2 (cn3, v2 + 1#64, ()) m3 (by dsimp only; omega)
                      ⟨ws3, hws3, by omega, by rw [hv2_1]; exact hcn3, hlt3, hm3⟩)
                  (fun Jm hJm => by
                    bb_to_group
                    · have hact2 : (fl[v2.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 := by
                        rw [hfl2_get]; exact by assumption
                      have hval02 : vals[2 * v2.toNat]?.getD 0#8 = 0#8 := by
                        have h0 : (vals[(v2 <<< BitVec.signExtend 64 1#32).toNat]'hv2_val
                            ).signExtend 32 = 0#32 := by
                          simpa using (by assumption :
                            (vals[(v2 <<< BitVec.signExtend 64 1#32).toNat]'hv2_val
                              ).signExtend 32 = ((0 : BitVec 32).setWidth 8).signExtend 32)
                        have h1 := bb_sext32_eq0_imp _ h0
                        rw [hval2_get, ← m6_getElem_congr hv2_shl hv2_val hv2_val']; exact h1
                      have hcond2 : (fl[v2.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                          vals[2 * v2.toNat]?.getD 0#8 = 0#8 := ⟨hact2, hval02⟩
                      have hu_eq : bbUnprio fl vals v2.toNat =
                          (if (fl[v2.toNat]?.getD 0#32 &&& 128#32) = 0#32 then 1 else 0) +
                          (if (fl[v2.toNat]?.getD 0#32 &&& 256#32) = 0#32 then 1 else 0) := by
                        unfold bbUnprio; rw [ite_eq_left hcond2]
                      refine wp_join_group (ts := [i64])
                        (fun (cn2a, ()) m_a => ∃ ws2a : List (BitVec 32),
                          ws2a.length = 2 * c.max_vars ∧
                          cn2a.toNat = cn2.toNat +
                            (if (fl[v2.toNat]?.getD 0#32 &&& 128#32) = 0#32 then 1 else 0) ∧
                          (∀ i < cn2a.toNat, (ws2a[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                          (FullMem c { s with scratch :=
                            { s.scratch with work_stk1 := ws2a } } ⋆ R) m_a)
                        (fun _ ⟨cn2a, ⟨⟩⟩ m_a ⟨ws2a, hws2a, hcn2a, hlt2a, hma⟩ => by
                          refine wp_join_group (ts := [i64])
                            (fun (cn2b, ()) m_b => ∃ ws2b : List (BitVec 32),
                              ws2b.length = 2 * c.max_vars ∧
                              cn2b.toNat = cand_n.toNat +
                                bbSumTo (bbUnprio fl vals) (v2.toNat + 1) ∧
                              (∀ i < cn2b.toNat,
                                (ws2b[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                              (FullMem c { s with scratch :=
                                { s.scratch with work_stk1 := ws2b } } ⋆ R) m_b)
                            (fun _ ⟨cn2b, ⟨⟩⟩ m_b h => hJm (cn2b, ()) m_b h)
                            (fun Jb hJb => by
                              have hl1_lt :
                                  (((v2 <<< (BitVec.signExtend 64 1#32)) ||| 1#64).truncate
                                    32).toNat < 2 * s.core.cur_vars :=
                                bb_bv64_shl1_sext_or1_tr v2 hv2_lt (by omega)
                              c0_hsplit
                              · have hb1 : (fl[v2.toNat]?.getD 0#32 &&& 256#32) = 0#32 := by
                                  rw [hfl2_get]; exact hc
                                have hcn2a_lt : cn2a.toNat < ws2a.length := by
                                  rw [hu_eq, ite_eq_left hb1] at hcn2_add_u; omega
                                have hcn2a_1 : (cn2a + 1#64).toNat = cn2a.toNat + 1 := by bv_omega
                                c0_hsteps!
                                refine hJb (cn2a + 1#64, ()) _ ⟨_, by simp [hws2a], ?_,
                                  fun i hi => ?_, hm⟩
                                · rw [bbSumTo, hu_eq, ite_eq_left hb1, hcn2a_1, hcn2a, hcn2_eq]
                                  omega
                                · rcases (by omega : i < cn2a.toNat ∨ i = cn2a.toNat) with
                                    hi' | rfl
                                  · rw [List.getElem?_set_ne (by omega)]; exact hlt2a i hi'
                                  · rw [List.getElem?_set_self hcn2a_lt, Option.getD_some]
                                    exact hl1_lt
                              · have hb1 : (fl[v2.toNat]?.getD 0#32 &&& 256#32) ≠ 0#32 := by
                                  rw [hfl2_get]; exact hc
                                c0_hsteps!
                                refine hJb (cn2a, ()) m_a ⟨ws2a, hws2a, ?_, hlt2a, hma⟩
                                rw [bbSumTo, hu_eq, ite_eq_right hb1, hcn2a, hcn2_eq]; omega))
                        (fun Ja hJa => by
                          have hl0_lt :
                              ((v2 <<< (BitVec.signExtend 64 1#32)).truncate 32).toNat <
                                2 * s.core.cur_vars := bb_bv64_shl1_sext_tr v2 hv2_lt (by omega)
                          c0_hsplit
                          · have hb0 : (fl[v2.toNat]?.getD 0#32 &&& 128#32) = 0#32 := by
                              rw [hfl2_get]; exact hc
                            have hcn2_lt : cn2.toNat < ws2.length := by
                              rw [hu_eq, ite_eq_left hb0] at hcn2_add_u; omega
                            have hcn2_1 : (cn2 + 1#64).toNat = cn2.toNat + 1 := by bv_omega
                            c0_hsteps!
                            refine hJa (cn2 + 1#64, ()) _ ⟨_, by simp [hws2],
                              by rw [ite_eq_left hb0, hcn2_1], fun i hi => ?_, hm⟩
                            rcases (by omega : i < cn2.toNat ∨ i = cn2.toNat) with hi' | rfl
                            · rw [List.getElem?_set_ne (by omega)]; exact hlt2 i hi'
                            · rw [List.getElem?_set_self hcn2_lt, Option.getD_some]; exact hl0_lt
                          · have hb0 : (fl[v2.toNat]?.getD 0#32 &&& 128#32) ≠ 0#32 := by
                              rw [hfl2_get]; exact hc
                            c0_hsteps!
                            exact hJa (cn2, ()) m2 ⟨ws2, hws2, by rw [ite_eq_right hb0]; omega,
                              hlt2, hm2⟩)
                    · have hval_ne : vals[2 * v2.toNat]?.getD 0#8 ≠ 0#8 := by
                        intro hz
                        rw [hval2_get, ← m6_getElem_congr hv2_shl hv2_val hv2_val'] at hz
                        have hne : (vals[(v2 <<< BitVec.signExtend 64 1#32).toNat]'hv2_val
                            ).signExtend 32 ≠ ((0 : BitVec 32).setWidth 8).signExtend 32 := by
                          assumption
                        rw [hz] at hne; exact hne rfl
                      have hnc : ¬ ((fl[v2.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                          vals[2 * v2.toNat]?.getD 0#8 = 0#8) := fun h => hval_ne h.2
                      exact hJm (cn2, ()) m2 ⟨ws2, hws2,
                        by simp only [bbSumTo, bbUnprio, hnc, ↓reduceIte, Nat.add_zero]
                           exact hcn2_eq,
                        hlt2, hm2⟩
                    · have hnact : ¬ ((fl[v2.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                          vals[2 * v2.toNat]?.getD 0#8 = 0#8) := fun h => by
                        rw [hfl2_get] at h; exact h.1 (by assumption)
                      exact hJm (cn2, ()) m2 ⟨ws2, hws2,
                        by simp only [bbSumTo, bbUnprio, hnact, ↓reduceIte, Nat.add_zero]
                           exact hcn2_eq,
                        hlt2, hm2⟩)
              · bb_steps
                have hcn2_le : cn2.toNat ≤ 2 * s.core.cur_vars :=
                  Nat.le_trans (by
                    rw [hcn2_eq]
                    exact Nat.add_le_add_left (bbSumTo_mono (bbUnprio fl vals) hv2_le) _)
                    htot_le
                exact hJf (cn2, v2, ()) m2 ⟨ws2, hws2, hcn2_le, hlt2, hm2⟩
          · bb_steps
            exact hJf (cand_n, v, ()) m1 ⟨ws1, hws1, by omega, hlt1, hm1⟩)

/-! ## 3. `full_backbone_keep_m6_wp` (`fullBackboneKeepM6Spec`) -/

theorem full_backbone_keep_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Func.wp Γ full_backbone_keep_m6_body a m Q X := by
  rintro ⟨h, cand_n, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcn_le, hlt_c, hm0, hQ⟩
  have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hfl_len := hcl.flags_len
  have hws1_len := hscl.work_stk1_len
  unfold Func.wp full_backbone_keep_m6_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (prio, rem, i, ()) m1 => i.toNat ≤ cand_n.toNat ∧ m1 = m0)
    (fun (_, _, i, ()) _ => cand_n.toNat - i.toNat) ?_ ?_
  · intro J1 hJ1; c0_hsteps; exact hJ1 (0#64, 0#64, 0#64, ()) m0 ⟨Nat.zero_le _, rfl⟩
  · rintro J1 ⟨prio, rem, i, ⟨⟩⟩ m1 ⟨hi_le, hm1_eq⟩ ih1
    rw [hm1_eq]
    c0_hstraight
    c0_hsplit
    · have hi_lt : i.toNat < cand_n.toNat := by c0_bound
      have hi_ws1 : i.toNat < s.scratch.work_stk1.length := by omega
      have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
      let lit := s.scratch.work_stk1[i.toNat]'hi_ws1
      have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
        have := hlt_c i.toNat hi_lt; rwa [List.getElem?_eq_getElem hi_ws1, Option.getD_some] at this
      have hlv_fl : (lit >>> 1#32).toNat < s.core.flags.length := by
        rw [bb_bv32_lshr1, hfl_len]; omega
      c0_hstraight
      refine wp_join_group (ts := [i64, i64]) (fun _ m2 => m2 = m0)
        (fun _ ⟨prio', rem', ⟨⟩⟩ m2 hm2 => by
          rw [hm2]; c0_hsteps
          exact ih1 (prio', rem', i + 1#64, ()) m0 (by dsimp only; omega) ⟨by omega, rfl⟩)
        (fun Jn hJn => by
          c0_hsplit
          · c0_hsteps_nogrp
            refine wp_join_group (ts := [i32]) (fun _ mb => mb = m0)
              (fun _ ⟨_bit, ⟨⟩⟩ mb hmb => by
                rw [hmb]; c0_hsteps_nogrp
                refine wp_join_group (ts := [i64]) (fun _ mc => mc = m0)
                  (fun _ ⟨prio', ⟨⟩⟩ mc hmc => by
                    rw [hmc]; c0_hsteps
                    exact hJn (prio', rem + 1#64, ()) m0 rfl)
                  (fun Jp hJp => by
                    c0_hsplit
                    · c0_hsteps; exact hJp _ m0 rfl
                    · c0_hsteps; exact hJp _ m0 rfl))
              (fun Jb hJb => by
                c0_hsplit
                · c0_hsteps; exact hJb _ m0 rfl
                · c0_hsteps; exact hJb _ m0 rfl)
          · c0_hsteps; exact hJn (prio, rem, ()) m0 rfl)
    · clear hc ih1 J1
      c0_hsplit
      · c0_hsteps; exact hQ s.core.flags m0 hsp hm0
      c0_hsplit
      · c0_hsteps; exact hQ s.core.flags m0 hsp hm0
      c0_hsplit
      · c0_hsteps; exact hQ s.core.flags m0 hsp hm0
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64])
        (fun (i2, ()) m2 => ∃ fl2 : List (BitVec 32), fl2.length = c.max_vars ∧
          i2.toNat ≤ cand_n.toNat ∧
          (FullMem c { s with core := { s.core with flags := fl2 } } ⋆ R) m2)
        (fun (i2, ()) _ => cand_n.toNat - i2.toNat) ?_ ?_
      · intro J2 hJ2; c0_hsteps
        exact hJ2 (0#64, ()) m0 ⟨s.core.flags, hfl_len, Nat.zero_le _, hm0⟩
      · rintro J2 ⟨i2, ⟨⟩⟩ m2 ⟨fl2, hfl2, hi_le2, hm2⟩ ih2
        c0_hsteps_nogrp
        c0_hsplit
        · have hi_lt : i2.toNat < cand_n.toNat := by c0_bound
          have hi_ws1 : i2.toNat < s.scratch.work_stk1.length := by omega
          have hi1 : (i2 + 1#64).toNat = i2.toNat + 1 := by bv_omega
          let lit := s.scratch.work_stk1[i2.toNat]'hi_ws1
          have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
            have := hlt_c i2.toNat hi_lt
            rwa [List.getElem?_eq_getElem hi_ws1, Option.getD_some] at this
          have hlv_fl : (lit >>> 1#32).toNat < fl2.length := by rw [bb_bv32_lshr1]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun _ m3 => ∃ fl3 : List (BitVec 32), fl3.length = c.max_vars ∧
              (FullMem c { s with core := { s.core with flags := fl3 } } ⋆ R) m3)
            (fun _ _ m3 ⟨fl3, hfl3, hm3⟩ => by
              c0_hsteps
              exact ih2 (i2 + 1#64, ()) m3 (by dsimp only; omega) ⟨fl3, hfl3, by omega, hm3⟩)
            (fun Jn hJn => by
              c0_hsplit
              · c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun _ m3 => ∃ fl3 : List (BitVec 32), fl3.length = c.max_vars ∧
                    (FullMem c { s with core := { s.core with flags := fl3 } } ⋆ R) m3)
                  (fun _ _ m3 h => hJn () m3 h)
                  (fun Jb hJb => by
                    have hlv_fl64 : (BitVec.setWidth 64 (lit >>> 1#32)).toNat < fl2.length := by
                      have : (BitVec.setWidth 64 (lit >>> 1#32)).toNat = (lit >>> 1#32).toNat := by
                        bv_omega
                      omega
                    c0_hsplit
                    · c0_hsteps
                      refine hJb () _ ⟨fl2.set (BitVec.setWidth 64 (lit >>> 1#32)).toNat
                          (fl2[(BitVec.setWidth 64 (lit >>> 1#32)).toNat] ||| 128#32),
                        by simp [hfl2], ?_⟩
                      refine bb_fullMem_symm ‹(FullMem c _ ⋆ R) _› ?_
                      dsimp only [lit]; rfl
                    · c0_hsteps
                      refine hJb () _ ⟨fl2.set (BitVec.setWidth 64 (lit >>> 1#32)).toNat
                          (fl2[(BitVec.setWidth 64 (lit >>> 1#32)).toNat] ||| 256#32),
                        by simp [hfl2], ?_⟩
                      refine bb_fullMem_symm ‹(FullMem c _ ⋆ R) _› ?_
                      dsimp only [lit]; rfl)
              · c0_hsteps; exact hJn () m2 ⟨fl2, hfl2, hm2⟩)
        · c0_hsteps
          exact hQ fl2 m2 (bb_sparseW_with_flags hsp hfl2) hm2

/-! ## 4. `full_backbone_unwind_m6_wp` (`fullBackboneUnwindM6Spec`) -/

theorem full_backbone_unwind_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackboneUnwindM6Spec a m Q X →
      Func.wp Γ full_backbone_unwind_m6_body a m Q X := by
  rintro ⟨h, saved, target_lvl, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, st, saved0, max_lvl, R, rfl, hsp0, hbt, hs0_le, hs_le, htgt_le,
     hlvl_saved, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_backbone_unwind_m6_body
  bb_to_group
  refine wp_loop_inv (ts := [])
    (fun _ m1 => ∃ (vals1 : List (BitVec 8)) (te1 : Nat),
      let st1 : FullState := { st with core := { st.core with vals := vals1, trail_end := te1 } }
      BbTrailInv c F0 F_cur s0 st1 saved0 max_lvl ∧ saved.toNat ≤ te1 ∧
      (FullMem c st1 ⋆ R) m1)
    (fun _ m1 => (loadVal m1 i64 (c.hdr + 144)).elim 0 BitVec.toNat) ?_ ?_
  · intro J1 hJ1; bb_steps
    exact hJ1 () m0 ⟨st.core.vals, st.core.trail_end, hbt, hs_le, hm0⟩
  · rintro J1 ⟨⟩ m1 ⟨vals1, te1, hbt1, hs_le1, hm1⟩ ih1
    let st1 : FullState := { st with core := { st.core with vals := vals1, trail_end := te1 } }
    have hcv_st1 : st1.core.cur_vars = s0.core.cur_vars := by rw [hbt1.same_core]
    have hte1_le : te1 ≤ c.max_vars :=
      Nat.le_trans hbt1.len_ok.core_ok.trail_end_le
        (by rw [hcv_st1]; exact hsp0.1.core_ok.cur_vars_le)
    have hte1_64 : te1 < 2 ^ 64 := by omega
    have hld1 : loadVal m1 i64 (c.hdr + 144) = some (BitVec.ofNat 64 te1) :=
      FullArenaTactics.load_full_trail_end (s := st1) hm1
    bb_step; bb_step; bb_step
    · have hgt_s : saved.toNat < te1 := by
        have h1 : saved.toNat < te1 % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt hte1_64] at h1
      have hpop := BbTrailInv.pop hsp0 hbt1 (by change saved0 < te1; omega)
      have hte1_sub : (BitVec.ofNat 64 te1 - 1#64).toNat = te1 - 1 := by
        rw [BitVec.toNat_sub_of_le (by simp [Nat.mod_eq_of_lt hte1_64]; omega)]
        simp [Nat.mod_eq_of_lt hte1_64]
      have hte1_trl : (BitVec.ofNat 64 te1 - 1#64).toNat < st1.core.trl.length := by
        rw [hte1_sub, hbt1.len_ok.core_ok.trl_len]; omega
      let ul := st1.core.trl[(BitVec.ofNat 64 te1 - 1#64).toNat]'hte1_trl
      have hul_eq : ul = st1.core.trl[te1 - 1]?.getD 0#32 := by
        dsimp only [ul]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        simp only [hte1_sub]
      have hul_lt : ul.toNat < 2 * s0.core.cur_vars := hul_eq ▸ hpop.1
      have hcv_le : s0.core.cur_vars ≤ c.max_vars := hsp0.1.core_ok.cur_vars_le
      have hvals1_len : vals1.length = 2 * c.max_vars := hbt1.len_ok.core_ok.vals_len
      have hul_vlen : ul.toNat < vals1.length := by omega
      have hul_vlen64 : (ul.setWidth 64).toNat < vals1.length := by
        rw [m6_zext32_toNat]; exact hul_vlen
      have hnot_vlen64 :
          ((ul ^^^ 1#32).setWidth 64).toNat < (vals1.set (ul.setWidth 64).toNat 0#8).length := by
        rw [List.length_set, m6_zext32_toNat, bb_bv32_xor1]
        have := litNeg_lt_two_mul hul_lt; omega
      have hte1_trl_bv :
          (BitVec.ofNat 64 (BitVec.ofNat 64 te1 - 1).toNat).toNat < st.core.trl.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; exact hte1_trl
      have hul_bv_eq :
          st.core.trl[(BitVec.ofNat 64 (BitVec.ofNat 64 te1 - 1).toNat).toNat]'hte1_trl_bv =
            ul := by
        dsimp only [ul]; congr 1
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; rfl
      have hul_bv_vlen64 :
          ((st.core.trl[(BitVec.ofNat 64 (BitVec.ofNat 64 te1 - 1).toNat).toNat]'
            hte1_trl_bv).setWidth 64).toNat < vals1.length := by
        rw [hul_bv_eq]; exact hul_vlen64
      have hnot_bv_vlen64 :
          (((st.core.trl[(BitVec.ofNat 64 (BitVec.ofNat 64 te1 - 1).toNat).toNat]'
            hte1_trl_bv) ^^^ 1#32).setWidth 64).toNat <
          (vals1.set ((st.core.trl[(BitVec.ofNat 64 (BitVec.ofNat 64 te1 - 1).toNat).toNat]'
            hte1_trl_bv).setWidth 64).toNat 0#8).length := by
        rw [hul_bv_eq]; exact hnot_vlen64
      bb_steps
      let st2 : FullState :=
        { st with core := { st.core with
          vals := (vals1.set ul.toNat 0#8).set (ul.toNat ^^^ 1) 0#8
          trail_end := te1 - 1 } }
      refine ih1 () m ?_ ⟨(vals1.set ul.toNat 0#8).set (ul.toNat ^^^ 1) 0#8, te1 - 1,
        ?_, by omega, ?_⟩
      · have hm2 : (FullMem c st2 ⋆ R) m := by
          refine bb_fullMem_eq ?_ hm
          dsimp only [st1, st2]
          rw [hul_bv_eq, m6_zext32_toNat, m6_zext32_toNat,
            show (ul ^^^ 1).toNat = ul.toNat ^^^ 1 from bb_bv32_xor1 ul,
            show (BitVec.ofNat 64 te1 - 1).toNat = te1 - 1 from hte1_sub]
        have hld2 : loadVal m i64 (c.hdr + 144) = some (BitVec.ofNat 64 (te1 - 1)) :=
          FullArenaTactics.load_full_trail_end (s := st2) hm2
        rw [hld2, hld1]
        simp [Nat.mod_eq_of_lt hte1_64, Nat.mod_eq_of_lt (by omega : te1 - 1 < 2 ^ 64)]
        omega
      · have hbt2 := hpop.2
        rwa [← hul_eq] at hbt2
      · refine bb_fullMem_eq ?_ hm
        dsimp only [st1, st2]
        rw [hul_bv_eq, m6_zext32_toNat, m6_zext32_toNat,
          show (ul ^^^ 1).toNat = ul.toNat ^^^ 1 from bb_bv32_xor1 ul,
          show (BitVec.ofNat 64 te1 - 1).toNat = te1 - 1 from hte1_sub]
    · have hte_eq : te1 = saved.toNat := by
        have h1 : te1 % 2 ^ 64 ≤ saved.toNat := by c0_bound
        rw [Nat.mod_eq_of_lt hte1_64] at h1; omega
      bb_steps
      have hbt_f := BbTrailInv.with_cur_level hbt1 (new_max := target_lvl.toNat)
        (cl' := target_lvl.toNat) (Nat.le_refl _) (fun i hi => by
          change i < te1 at hi
          exact hlvl_saved i (by omega))
      exact hQ vals1 _ (by simpa [hte_eq] using hbt_f) (by
        have hst_eq : ({ st1 with core := { st1.core with cur_level := target_lvl.toNat } } :
            FullState) = { st with core := { st.core with
              vals := vals1, trail_end := saved.toNat, cur_level := target_lvl.toNat } } := by
          dsimp only [st1]; rw [hte_eq]
        rwa [← hst_eq])

end LeanQbe.T.Examples.Kissat.Proof.Backbone
