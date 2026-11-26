/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BBveFwd
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof4a
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullTransLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 12B — Backbone & Forward-Subsumption Proofs
(`FullFidelityStep12BProofBackFwd`)

UNSAT-only `Func.wp` proofs (`public section`, `0` `@[expose]`, `0` `import all`, `XPost := False`):
1. `full_backbone_sched_m6_s12b_wp`: certifies `FullM6VivBackbone.fullBackboneSchedM6Spec` for
   two-pass prioritized + remaining active-unassigned candidate scheduling (`P1-5a`).
2. `full_backbone_m6_s12b_wp`: certifies canonical `FullM3Backbone.fullBackboneSpec` with
   scaled round limit `min(1000, 100 * comp)` (`P1-5c`).
3. `full_dense_prop_unit_m7_s12b_wp`: certifies `FullM6BveFwd.fullDensePropUnitM6Spec` with
   `unass > 1u` early break in dense large-clause propagation (`P1-6c`).
4. `full_forward_sub_m7_s12b_wp`: certifies canonical `FullFastBveBudgets.fullForwardSubFastSpec`
   with `full_fwd_reconnect_irred_m7` + trail `propagated` rewind before
   `full_dense_flush_units_m7` (`P1-6b`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open Kraken.Bedrock2.Test
open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics

local macro "s12b_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Private Helpers for Two-Pass Backbone Scheduling & Sparse/Dense Transport -/

private def s12bBbPrio (fl : List (BitVec 32)) (vals : List (BitVec 8)) (u : Nat) : Nat :=
  if (fl[u]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧ vals[2 * u]?.getD 0#8 = 0#8 then
    (if (fl[u]?.getD 0#32 &&& 128#32) ≠ 0#32 then 1 else 0) +
    (if (fl[u]?.getD 0#32 &&& 256#32) ≠ 0#32 then 1 else 0)
  else 0

private def s12bBbUnprio (fl : List (BitVec 32)) (vals : List (BitVec 8)) (u : Nat) : Nat :=
  if (fl[u]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧ vals[2 * u]?.getD 0#8 = 0#8 then
    (if (fl[u]?.getD 0#32 &&& 128#32) = 0#32 then 1 else 0) +
    (if (fl[u]?.getD 0#32 &&& 256#32) = 0#32 then 1 else 0)
  else 0

private def s12bSumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => s12bSumTo f k + f k

private theorem s12bBbPrio_add_unprio_le (fl : List (BitVec 32)) (vals : List (BitVec 8))
    (u : Nat) : s12bBbPrio fl vals u + s12bBbUnprio fl vals u ≤ 2 := by
  unfold s12bBbPrio s12bBbUnprio
  by_cases h1 : (fl[u]?.getD 0#32 &&& 1#32) = 0#32 <;>
  by_cases hv : vals[2 * u]?.getD 0#8 = 0#8 <;>
  by_cases h0 : (fl[u]?.getD 0#32 &&& 128#32) = 0#32 <;>
  by_cases h2 : (fl[u]?.getD 0#32 &&& 256#32) = 0#32 <;>
  simp [h1, hv, h0, h2]

private theorem s12b_sext32_eq0_imp : ∀ x : BitVec 8, x.signExtend 32 = 0#32 → x = 0#8 := by
  decide

private theorem s12bSumTo_prio_unprio_le (fl : List (BitVec 32)) (vals : List (BitVec 8)) :
    ∀ n : Nat, s12bSumTo (s12bBbPrio fl vals) n + s12bSumTo (s12bBbUnprio fl vals) n ≤ 2 * n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    have ih := s12bSumTo_prio_unprio_le fl vals n
    have h1 := s12bBbPrio_add_unprio_le fl vals n
    simp only [s12bSumTo]; omega

private theorem s12bSumTo_mono (f : Nat → Nat) {a b : Nat} (hle : a ≤ b) :
    s12bSumTo f a ≤ s12bSumTo f b := by
  induction hle with
  | refl => exact Nat.le_refl _
  | @step m _ ih => simp only [s12bSumTo]; omega

private theorem s12b_bv64_shl1_sext (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x <<< BitVec.signExtend 64 1#32).toNat = 2 * x.toNat := by
  change (x <<< ((BitVec.signExtend 64 1#32).toNat % 64)).toNat = 2 * x.toNat
  rw [show (BitVec.signExtend 64 1#32).toNat % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem s12b_bv64_shl1_sext_tr (x : BitVec 64) {n : Nat} (hx : x.toNat < n)
    (hn : 2 * n < 2 ^ 32) :
    ((x <<< BitVec.signExtend 64 1#32).truncate 32).toNat < 2 * n := by
  have h1 := s12b_bv64_shl1_sext x (by omega)
  rw [BitVec.toNat_setWidth, h1, Nat.mod_eq_of_lt (by omega)]; omega

private theorem s12b_bv64_shl1_sext_or1_tr (x : BitVec 64) {n : Nat} (hx : x.toNat < n)
    (hn : 2 * n < 2 ^ 32) :
    (((x <<< BitVec.signExtend 64 1#32) ||| 1#64).truncate 32).toNat < 2 * n := by
  change (((x <<< (1 : Nat)) ||| 1#64).setWidth 32).toNat < 2 * n
  rw [FullTransHelpers.ft_bv64_shl1_or1_setWidth32 (by omega)]; omega

private theorem s12b_sparseW_with_ws1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {ws1' : List (BitVec 32)}
    (hws1 : ws1'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with work_stk1_len := hws1 }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s12b_sparseW_with_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (pr' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with probing := pr' } } :=
  ⟨⟨{ hsp.1.core_ok with }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s12b_sparseW_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (asz' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with ant_sz := asz' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s12b_sparseW_with_delayed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (dl' : Nat) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with delayed_len := dl' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s12b_sparseW_of_prop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hsp : FullSparseInvW c F0 F_cur s)
    (hs' : s' = { s with
      core := { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', unassigned := unass', unflushed := unfl',
        wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
        fuel := fuel', confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
        confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with
        search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm' : FullArenaPermEq s.core s'.core) : FullSparseInvW c F0 F_cur s' := by
  obtain ⟨_, _, hlm, hnd0, ⟨hll0, hel0⟩, hdm⟩ := hsp; subst hs'
  refine ⟨hlen', hw', hlm, fun r hr hng => ?_, ⟨fun i hi => ?_, hel0⟩, hdm⟩
  · have hr0 : r ∈ fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs at hr ⊢; rwa [hperm'.2.1] at hr
    obtain ⟨_, hgb, hpm⟩ := hperm'.2.2 r hr0
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb at hng ⊢; exact hgb ▸ hng
    unfold fullArenaClauseLits; exact (hpm.map (· / 2)).nodup_iff.mpr (hnd0 r hr0 hng0)
  · dsimp only; unfold FullLastLearnedWf at hll0; unfold fullArenaClauseRefs
    rw [hperm'.2.1]; exact hll0 i hi

private theorem s12b_zero_mem_arenaRefs {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    cases hal : k.arena_len with
    | zero => omega
    | succ n =>
      rw [fullArenaScanRefs]
      simp only [show 0 + 3 ≤ n + 1 by omega, ↓reduceIte]
      exact List.mem_cons_self

/-! ## 2. `full_backbone_sched_m6` (`P1-5a` Two-Pass Scheduling) -/

/-- `full_backbone_sched_m6` (Step-12B two-pass) satisfies `fullBackboneSchedM6Spec`. -/
theorem full_backbone_sched_m6_s12b_wp (Γ : Env) :
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
  fvt_to_group
  -- Pass 1 loop: `(cand_n, not_resched, v)`
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (cand_n, not_resched, v, ()) m1 =>
      ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
        v.toNat ≤ s.core.cur_vars ∧
        cand_n.toNat = s12bSumTo (s12bBbPrio fl vals) v.toNat ∧
        not_resched.toNat = s12bSumTo (s12bBbUnprio fl vals) v.toNat ∧
        (∀ i < cand_n.toNat, (ws1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
    (fun (_, _, v, ()) _ => s.core.cur_vars - v.toNat) ?_ ?_
  · intro J1 hJ1; fvt_steps
    exact hJ1 (0#64, 0#64, 0#64, ()) m0 ⟨s.scratch.work_stk1, hws1_len, Nat.zero_le _,
      rfl, rfl, (fun _ h => by cases h), hm0⟩
  · rintro J1 ⟨cand_n, not_resched, v, ⟨⟩⟩ m1 ⟨ws1, hws1, hv_le, hcn_eq, hnr_eq, hlt1, hm1⟩ ih1
    have hsum_v := s12bSumTo_prio_unprio_le fl vals v.toNat
    fvt_step; fvt_step
    · have hv_lt : v.toNat < s.core.cur_vars := by
        have h1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt (by omega)] at h1
      have hv_fl : v.toNat < fl.length := by omega
      have hv1_eq : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
      have hv2_eq : (v <<< (BitVec.signExtend 64 1#32)).toNat = 2 * v.toNat :=
        s12b_bv64_shl1_sext v (by omega)
      have hv2_lt : (v <<< (BitVec.signExtend 64 1#32)).toNat < vals.length := by omega
      have hv2_lt' : 2 * v.toNat < vals.length := by omega
      have hfl_get : fl[v.toNat]?.getD 0#32 = fl[v.toNat]'hv_fl := by
        rw [List.getElem?_eq_getElem hv_fl, Option.getD_some]
      have hval_get : vals[2 * v.toNat]?.getD 0#8 = vals[2 * v.toNat]'hv2_lt' := by
        rw [List.getElem?_eq_getElem hv2_lt', Option.getD_some]
      fvt_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (cn', nr', ()) m2 => ∃ ws1' : List (BitVec 32), ws1'.length = 2 * c.max_vars ∧
          cn'.toNat = s12bSumTo (s12bBbPrio fl vals) (v.toNat + 1) ∧
          nr'.toNat = s12bSumTo (s12bBbUnprio fl vals) (v.toNat + 1) ∧
          (∀ i < cn'.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m2)
        (fun _ ⟨cn', nr', ⟨⟩⟩ m2 ⟨ws1', hws1', hcn', hnr', hlt', hm2⟩ => by
          fvt_steps
          exact ih1 (cn', nr', v + 1#64, ()) m2 (by dsimp only; omega)
            ⟨ws1', hws1', by omega, by rw [hv1_eq]; exact hcn', by rw [hv1_eq]; exact hnr',
             hlt', hm2⟩)
        (fun Jn hJn => by
          fvt_to_group
          · -- `(fl[v] & FL_ACTIVE) != 0 && vals[2 * v] == 0`
            have hact : (fl[v.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 := by
              rw [hfl_get]; exact by assumption
            have hval0 : vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
              have h0 : (vals[(v <<< BitVec.signExtend 64 1#32).toNat]'hv2_lt).signExtend 32 =
                  0#32 := by
                simpa using (by assumption :
                  (vals[(v <<< BitVec.signExtend 64 1#32).toNat]'hv2_lt).signExtend 32 =
                    ((0 : BitVec 32).setWidth 8).signExtend 32)
              have h1 := s12b_sext32_eq0_imp _ h0
              rw [hval_get, ← m6_getElem_congr hv2_eq hv2_lt hv2_lt']; exact h1
            have hcond : (fl[v.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                vals[2 * v.toNat]?.getD 0#8 = 0#8 := ⟨hact, hval0⟩
            have hprio_eq : s12bBbPrio fl vals v.toNat =
                (if (fl[v.toNat]?.getD 0#32 &&& 128#32) ≠ 0#32 then 1 else 0) +
                (if (fl[v.toNat]?.getD 0#32 &&& 256#32) ≠ 0#32 then 1 else 0) := by
              unfold s12bBbPrio; rw [ite_eq_left hcond]
            have hunprio_eq : s12bBbUnprio fl vals v.toNat =
                (if (fl[v.toNat]?.getD 0#32 &&& 128#32) = 0#32 then 1 else 0) +
                (if (fl[v.toNat]?.getD 0#32 &&& 256#32) = 0#32 then 1 else 0) := by
              unfold s12bBbUnprio; rw [ite_eq_left hcond]
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
                    cn2.toNat = s12bSumTo (s12bBbPrio fl vals) (v.toNat + 1) ∧
                    nr2.toNat = s12bSumTo (s12bBbUnprio fl vals) (v.toNat + 1) ∧
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
                          2 * s.core.cur_vars := s12b_bv64_shl1_sext_or1_tr v hv_lt (by omega)
                    fvt_steps
                    · have hb1 : (fl[v.toNat]?.getD 0#32 &&& 256#32) ≠ 0#32 := by
                        rw [hfl_get]; exact by assumption
                      refine hJb (cn1 + 1#64, nr1, ()) _ ⟨_, by simp [hws1_a], ?_, ?_,
                        fun i hi => ?_, hm⟩
                      · rw [s12bSumTo, hprio_eq, ite_eq_left hb1, hcn1_1, hcn1, hcn_eq]; omega
                      · rw [s12bSumTo, hunprio_eq, ite_eq_right hb1, hnr1, hnr_eq]; omega
                      · rcases (by omega : i < cn1.toNat ∨ i = cn1.toNat) with hi' | rfl
                        · rw [List.getElem?_set_ne (by omega)]; exact hlta i hi'
                        · rw [List.getElem?_set_self hcn1_lt, Option.getD_some]; exact hl1_lt
                    · have hb1 : (fl[v.toNat]?.getD 0#32 &&& 256#32) = 0#32 := by
                        rw [hfl_get]; exact by assumption
                      refine hJb (cn1, nr1 + 1#64, ()) m_a ⟨ws1_a, hws1_a, ?_, ?_, hlta, hma⟩
                      · simp only [s12bSumTo, hprio_eq, hb1, ne_eq, not_true_eq_false, ↓reduceIte,
                          hcn1, hcn_eq]; omega
                      · rw [s12bSumTo, hunprio_eq, ite_eq_left hb1, hnr1_1, hnr1, hnr_eq]; omega))
              (fun Ja hJa => by
                have hcn_lt : cand_n.toNat < ws1.length := by omega
                have hcn_1 : (cand_n + 1#64).toNat = cand_n.toNat + 1 := by bv_omega
                have hnr_1 : (not_resched + 1#64).toNat = not_resched.toNat + 1 := by bv_omega
                have hl0_lt :
                    ((v <<< (BitVec.signExtend 64 1#32)).truncate 32).toNat <
                      2 * s.core.cur_vars := s12b_bv64_shl1_sext_tr v hv_lt (by omega)
                fvt_steps
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
          · -- `vals[2 * v] != 0`
            have hval_ne : vals[2 * v.toNat]?.getD 0#8 ≠ 0#8 := by
              intro hz
              rw [hval_get, ← m6_getElem_congr hv2_eq hv2_lt hv2_lt'] at hz
              have hne : (vals[(v <<< BitVec.signExtend 64 1#32).toNat]'hv2_lt).signExtend 32 ≠
                  ((0 : BitVec 32).setWidth 8).signExtend 32 := by assumption
              rw [hz] at hne; exact hne rfl
            have hnc : ¬ ((fl[v.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                vals[2 * v.toNat]?.getD 0#8 = 0#8) := fun h => hval_ne h.2
            exact hJn (cand_n, not_resched, ()) m1 ⟨ws1, hws1,
              by simp only [s12bSumTo, s12bBbPrio, hnc, ↓reduceIte, Nat.add_zero]; exact hcn_eq,
              by simp only [s12bSumTo, s12bBbUnprio, hnc, ↓reduceIte, Nat.add_zero]; exact hnr_eq,
              hlt1, hm1⟩
          · -- `(fl[v] & FL_ACTIVE) == 0`
            have hnact : ¬ ((fl[v.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                vals[2 * v.toNat]?.getD 0#8 = 0#8) := fun h => by
              rw [hfl_get] at h; exact h.1 (by assumption)
            exact hJn (cand_n, not_resched, ()) m1 ⟨ws1, hws1,
              by simp only [s12bSumTo, s12bBbPrio, hnact, ↓reduceIte, Nat.add_zero]; exact hcn_eq,
              by simp only [s12bSumTo, s12bBbUnprio, hnact, ↓reduceIte, Nat.add_zero]; exact hnr_eq,
              hlt1, hm1⟩)
    · -- Pass 1 exit: `v.toNat = s.core.cur_vars`
      have hv_eq : v.toNat = s.core.cur_vars := by
        have h1 : ¬ v.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
        rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
      have htot_le : cand_n.toNat + s12bSumTo (s12bBbUnprio fl vals) s.core.cur_vars ≤
          2 * s.core.cur_vars := by
        rw [hcn_eq, hv_eq]; exact s12bSumTo_prio_unprio_le fl vals s.core.cur_vars
      clear hc ih1 J1
      fvt_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (cn_f, _, ()) mf => ∃ ws1' : List (BitVec 32),
          ws1'.length = 2 * c.max_vars ∧
          cn_f.toNat ≤ 2 * s.core.cur_vars ∧
          (∀ i < cn_f.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) mf)
        (fun _ ⟨cn_f, _, ⟨⟩⟩ mf ⟨ws1', hws1', hcn_f, hlt_f, hmf⟩ => by
          fvt_steps
          exact hQ cn_f s.core.flags ws1' mf (s12b_sparseW_with_ws1 hsp hws1') hcn_f hlt_f hmf)
        (fun Jf hJf => by
          fvt_step; fvt_step
          · -- Pass 2 loop (`not_resched > 0`): append remaining non-prioritized active vars
            refine wp_loop_inv (ts := [i64, i64])
              (fun (cn2, v2, ()) m2 => ∃ ws2 : List (BitVec 32),
                ws2.length = 2 * c.max_vars ∧
                v2.toNat ≤ s.core.cur_vars ∧
                cn2.toNat = cand_n.toNat + s12bSumTo (s12bBbUnprio fl vals) v2.toNat ∧
                (∀ i < cn2.toNat, (ws2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                (FullMem c { s with scratch := { s.scratch with work_stk1 := ws2 } } ⋆ R) m2)
              (fun (_, v2, ()) _ => s.core.cur_vars - v2.toNat) ?_ ?_
            · intro J2 hJ2; fvt_steps
              exact hJ2 (cand_n, 0#64, ()) m1 ⟨ws1, hws1, Nat.zero_le _, by simp [s12bSumTo],
                hlt1, hm1⟩
            · rintro J2 ⟨cn2, v2, ⟨⟩⟩ m2 ⟨ws2, hws2, hv2_le, hcn2_eq, hlt2, hm2⟩ ih2
              fvt_step; fvt_step
              · have hv2_lt : v2.toNat < s.core.cur_vars := by
                  have h1 : v2.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
                  rwa [Nat.mod_eq_of_lt (by omega)] at h1
                have hv2_fl : v2.toNat < fl.length := by omega
                have hv2_1 : (v2 + 1#64).toNat = v2.toNat + 1 := by bv_omega
                have hv2_shl : (v2 <<< (BitVec.signExtend 64 1#32)).toNat = 2 * v2.toNat :=
                  s12b_bv64_shl1_sext v2 (by omega)
                have hv2_val : (v2 <<< (BitVec.signExtend 64 1#32)).toNat < vals.length := by
                  omega
                have hv2_val' : 2 * v2.toNat < vals.length := by omega
                have hfl2_get : fl[v2.toNat]?.getD 0#32 = fl[v2.toNat]'hv2_fl := by
                  rw [List.getElem?_eq_getElem hv2_fl, Option.getD_some]
                have hval2_get : vals[2 * v2.toNat]?.getD 0#8 = vals[2 * v2.toNat]'hv2_val' := by
                  rw [List.getElem?_eq_getElem hv2_val', Option.getD_some]
                have hsum_next : cand_n.toNat + s12bSumTo (s12bBbUnprio fl vals) (v2.toNat + 1) ≤
                    2 * s.core.cur_vars :=
                  Nat.le_trans (Nat.add_le_add_left
                    (s12bSumTo_mono (s12bBbUnprio fl vals) (by omega)) _) htot_le
                have hcn2_add_u : cn2.toNat + s12bBbUnprio fl vals v2.toNat ≤
                    2 * s.core.cur_vars := by
                  rw [hcn2_eq]; simpa only [s12bSumTo, Nat.add_assoc] using hsum_next
                fvt_to_group
                refine wp_join_group (ts := [i64])
                  (fun (cn3, ()) m3 => ∃ ws3 : List (BitVec 32),
                    ws3.length = 2 * c.max_vars ∧
                    cn3.toNat = cand_n.toNat +
                      s12bSumTo (s12bBbUnprio fl vals) (v2.toNat + 1) ∧
                    (∀ i < cn3.toNat, (ws3[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws3 } } ⋆ R) m3)
                  (fun _ ⟨cn3, ⟨⟩⟩ m3 ⟨ws3, hws3, hcn3, hlt3, hm3⟩ => by
                    fvt_steps
                    exact ih2 (cn3, v2 + 1#64, ()) m3 (by dsimp only; omega)
                      ⟨ws3, hws3, by omega, by rw [hv2_1]; exact hcn3, hlt3, hm3⟩)
                  (fun Jm hJm => by
                    fvt_to_group
                    · have hact2 : (fl[v2.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 := by
                        rw [hfl2_get]; exact by assumption
                      have hval02 : vals[2 * v2.toNat]?.getD 0#8 = 0#8 := by
                        have h0 : (vals[(v2 <<< BitVec.signExtend 64 1#32).toNat]'hv2_val
                            ).signExtend 32 = 0#32 := by
                          simpa using (by assumption :
                            (vals[(v2 <<< BitVec.signExtend 64 1#32).toNat]'hv2_val
                              ).signExtend 32 = ((0 : BitVec 32).setWidth 8).signExtend 32)
                        have h1 := s12b_sext32_eq0_imp _ h0
                        rw [hval2_get, ← m6_getElem_congr hv2_shl hv2_val hv2_val']; exact h1
                      have hcond2 : (fl[v2.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                          vals[2 * v2.toNat]?.getD 0#8 = 0#8 := ⟨hact2, hval02⟩
                      have hu_eq : s12bBbUnprio fl vals v2.toNat =
                          (if (fl[v2.toNat]?.getD 0#32 &&& 128#32) = 0#32 then 1 else 0) +
                          (if (fl[v2.toNat]?.getD 0#32 &&& 256#32) = 0#32 then 1 else 0) := by
                        unfold s12bBbUnprio; rw [ite_eq_left hcond2]
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
                                s12bSumTo (s12bBbUnprio fl vals) (v2.toNat + 1) ∧
                              (∀ i < cn2b.toNat,
                                (ws2b[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                              (FullMem c { s with scratch :=
                                { s.scratch with work_stk1 := ws2b } } ⋆ R) m_b)
                            (fun _ ⟨cn2b, ⟨⟩⟩ m_b h => hJm (cn2b, ()) m_b h)
                            (fun Jb hJb => by
                              have hl1_lt :
                                  (((v2 <<< (BitVec.signExtend 64 1#32)) ||| 1#64).truncate
                                    32).toNat < 2 * s.core.cur_vars :=
                                s12b_bv64_shl1_sext_or1_tr v2 hv2_lt (by omega)
                              c0_hsplit
                              · have hb1 : (fl[v2.toNat]?.getD 0#32 &&& 256#32) = 0#32 := by
                                  rw [hfl2_get]; exact hc
                                have hcn2a_lt : cn2a.toNat < ws2a.length := by
                                  rw [hu_eq, ite_eq_left hb1] at hcn2_add_u; omega
                                have hcn2a_1 : (cn2a + 1#64).toNat = cn2a.toNat + 1 := by bv_omega
                                c0_hsteps!
                                refine hJb (cn2a + 1#64, ()) _ ⟨_, by simp [hws2a], ?_,
                                  fun i hi => ?_, hm⟩
                                · rw [s12bSumTo, hu_eq, ite_eq_left hb1, hcn2a_1, hcn2a, hcn2_eq]
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
                                rw [s12bSumTo, hu_eq, ite_eq_right hb1, hcn2a, hcn2_eq]; omega))
                        (fun Ja hJa => by
                          have hl0_lt :
                              ((v2 <<< (BitVec.signExtend 64 1#32)).truncate 32).toNat <
                                2 * s.core.cur_vars := s12b_bv64_shl1_sext_tr v2 hv2_lt (by omega)
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
                        by simp only [s12bSumTo, s12bBbUnprio, hnc, ↓reduceIte, Nat.add_zero]
                           exact hcn2_eq,
                        hlt2, hm2⟩
                    · have hnact : ¬ ((fl[v2.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
                          vals[2 * v2.toNat]?.getD 0#8 = 0#8) := fun h => by
                        rw [hfl2_get] at h; exact h.1 (by assumption)
                      exact hJm (cn2, ()) m2 ⟨ws2, hws2,
                        by simp only [s12bSumTo, s12bBbUnprio, hnact, ↓reduceIte, Nat.add_zero]
                           exact hcn2_eq,
                        hlt2, hm2⟩)
              · fvt_steps
                have hcn2_le : cn2.toNat ≤ 2 * s.core.cur_vars :=
                  Nat.le_trans (by
                    rw [hcn2_eq]
                    exact Nat.add_le_add_left (s12bSumTo_mono (s12bBbUnprio fl vals) hv2_le) _)
                    htot_le
                exact hJf (cn2, v2, ()) m2 ⟨ws2, hws2, hcn2_le, hlt2, hm2⟩
          · fvt_steps
            exact hJf (cand_n, v, ()) m1 ⟨ws1, hws1, by omega, hlt1, hm1⟩)

/-! ## 3. `full_backbone_m6` (`P1-5c` Scaled Round Limit `min(1000, 100 * comp)`) -/

/-- `full_backbone_m6` (Step-12B) satisfies exact canonical `FullM3Backbone.fullBackboneSpec`. -/
theorem full_backbone_m6_s12b_del_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateDelSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hPrio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (hSched : ∀ a m Q X, fullBackboneSchedM6Spec a m Q X →
      Γ "full_backbone_sched_m6" [i64] [i64] a m Q X)
    (hRound : ∀ a m Q X, fullBackboneRoundM6Spec a m Q X →
      Γ "full_backbone_round_m6" [i64, i64, .bool] [i64] a m Q X)
    (hKeep : ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Γ "full_backbone_keep_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Func.wp Γ full_backbone_m6_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx; unfold Func.wp full_backbone_m6_body
  refine wp_join_group (ts := [])
    (fun _ m1 => ∃ (F_cur : List (List Nat)) (s1 : FullState),
      FullSparseInvW c F0 F_cur s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ _ m1 ⟨F_cur, s1, hsp1, hl0_1, hfu1, hm1⟩ => by
      have hcv1_le := hsp1.1.core_ok.cur_vars_le
      fvt_to_group
      refine wp_join_group (ts := []) (fun _ me => me = m1)
        (fun _ _ me heq => by
          subst heq; fvt_steps
          have hsp_e := s12b_sparseW_with_probing hsp1 0#64
          exact hQ 1#64 _ _ ⟨⟨hsp_e.1, ⟨F_cur, hsp_e.2.1⟩⟩, hsp_e.2.2.1, hsp_e.2.2.2.1,
            hsp_e.2.2.2.2.1, hsp_e.2.2.2.2.2⟩ hl0_1 rfl hfu1 (Or.inl rfl)
            (fun h => by cases h) hm)
        (fun Jez hJez => by
          fvt_steps
          · exact hJez () m1 rfl
          · exact hJez () m1 rfl
          · exact hJez () m1 rfl
          · let s1p : FullState := { s1 with core := { s1.core with probing := 1#64 } }
            have hsp1p : FullSparseInvW c F0 F_cur s1p := s12b_sparseW_with_probing hsp1 1#64
            c0_call hProp
            refine ⟨c, F0, F_cur, s1p, R, rfl, hsp1p.1, hsp1p.2.1, hsp1p.2.2.2.2.2, hm,
              fun pr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel2 _ _ _ _ _ _ _ _ _ m2 hlen2 hw2 _
                hperm2 hfu2 _ _ hpr0 _ _ hm2 => ?_⟩
            have hsp2 : FullSparseInvW c F0 F_cur _ :=
              s12b_sparseW_of_prop hsp1p rfl hlen2 hw2 hperm2
            have hfu2' : fuel2.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu2 hfu1
            fvt_steps
            · have hsp_u := s12b_sparseW_with_probing hsp2 0#64
              exact hQ 20#64 _ _ ⟨⟨hsp_u.1, ⟨F_cur, hsp_u.2.1⟩⟩, hsp_u.2.2.1, hsp_u.2.2.2.1,
                hsp_u.2.2.2.2.1, hsp_u.2.2.2.2.2⟩ hl0_1 rfl hfu2' (Or.inr rfl)
                (fun _ => level0_unsat_of_conflict_okW hw2 hl0_1 (hpr0 hc).2.2) hm
            · have hsp_o := s12b_sparseW_with_probing hsp2 0#64
              exact hQ 1#64 _ _ ⟨⟨hsp_o.1, ⟨F_cur, hsp_o.2.1⟩⟩, hsp_o.2.2.1, hsp_o.2.2.2.1,
                hsp_o.2.2.2.2.1, hsp_o.2.2.2.2.2⟩ hl0_1 rfl hfu2' (Or.inl rfl)
                (fun h => by cases h) hm
            · c0_call hPrio
              refine ⟨c, F0, F_cur, _, R, rfl, hsp2, hm2,
                fun stop_early wstk3 scr3 m3 hsp3 hm3 => ?_⟩
              c0_call hSched
              refine ⟨c, F0, F_cur, _, R, rfl, hsp3, hm3,
                fun cand_n0 fl4 ws1_4 m4 hsp4 hcn0_le hlt0 hm4 => ?_⟩
              c0_hsteps_nogrp
              -- Join 1: `comp = (h->probings > 0) ? h->probings : 1`
              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
                (fun _ => True) ?_ (fun Jc hJc => by
                  c0_hsplit
                  · c0_hsteps!; exact hJc _ trivial
                  · c0_hsteps!; exact hJc 1#64 trivial)
              intro _ comp _
              -- Join 2: `max_rounds = (comp >= 10) ? 1000 : 100 * comp`
              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
                (fun x => x.toNat ≤ 1000) ?_ (fun Jm hJm => by
                  c0_hsplit
                  · c0_hsteps!; exact hJm 1000#64 (by decide)
                  · c0_hsteps!
                    have hlt10 : comp.toNat < 10 := by c0_bound
                    exact hJm (100#64 * comp) (by
                      rw [BitVec.toNat_mul, show (100#64 : BitVec 64).toNat = 100 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                      omega))
              intro _ max_rounds hmr_le
              fvt_to_group
              -- Break join `Js` (`[i64, i64, i64]` = `(cand_n, res, round)`): `keep` + `probing=0`
              refine wp_join_group (ts := [i64, i64, i64])
                (fun (cn_f, res_f, _, ()) mf => ∃ sf : FullState, FullSparseInvW c F0 F_cur sf ∧
                  sf.core.cur_level = 0 ∧ sf.core.cur_vars = s1.core.cur_vars ∧
                  sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  cn_f.toNat ≤ 2 * sf.core.cur_vars ∧
                  (∀ i < cn_f.toNat, (sf.scratch.work_stk1[i]?.getD 0#32).toNat <
                    2 * sf.core.cur_vars) ∧
                  (res_f = 1#64 ∨ res_f = 20#64) ∧ (res_f = 20#64 → F0.Unsat) ∧
                  (FullMem c sf ⋆ R) mf)
                (fun _ ⟨cn_f, res_f, _, ⟨⟩⟩ mf
                    ⟨sf, hspf, hclf, _hcvf, hfuf, hcnf_le, hltf, hdom, huns, hmf⟩ => by
                  c0_call hKeep
                  refine ⟨c, F0, F_cur, sf, R, rfl, hspf, hcnf_le, hltf, hmf,
                    fun fl_k mk hspk hmk => ?_⟩
                  fvt_steps
                  have hsp_end := s12b_sparseW_with_probing hspk 0#64
                  exact hQ res_f _ _ ⟨⟨hsp_end.1, ⟨F_cur, hsp_end.2.1⟩⟩, hsp_end.2.2.1,
                    hsp_end.2.2.2.1, hsp_end.2.2.2.2.1, hsp_end.2.2.2.2.2⟩ hclf rfl hfuf hdom
                    huns hm)
                (fun Jbr hJbr => ?_)
              -- Round loop `[i64, i64, i64]` = `(cand_n, res, round)`
              refine wp_loop_inv (ts := [i64, i64, i64])
                (fun (cn_r, res_r, rnd, ()) mr => ∃ sr : FullState, FullSparseInvW c F0 F_cur sr ∧
                  sr.core.cur_level = 0 ∧ sr.core.cur_vars = s1.core.cur_vars ∧
                  sr.core.fuel.toNat ≤ s.core.fuel.toNat ∧ rnd.toNat ≤ max_rounds.toNat ∧
                  cn_r.toNat ≤ 2 * sr.core.cur_vars ∧
                  (∀ i < cn_r.toNat, (sr.scratch.work_stk1[i]?.getD 0#32).toNat <
                    2 * sr.core.cur_vars) ∧
                  (res_r = 1#64 ∨ res_r = 20#64) ∧ (res_r = 20#64 → F0.Unsat) ∧
                  (FullMem c sr ⋆ R) mr)
                (fun (_, _, rnd, ()) _ => max_rounds.toNat - rnd.toNat) ?_ ?_
              · intro Jr hJr; c0_hsteps!
                exact hJr (cand_n0, 1#64, 0#64, ()) _
                  ⟨_, s12b_sparseW_with_ant_sz hsp4 tick_lim, hl0_1, rfl, hfu2', Nat.zero_le _,
                   hcn0_le, hlt0, Or.inl rfl, (fun h => by cases h), hm⟩
              · rintro Jr ⟨cn_r, res_r, rnd, ⟨⟩⟩ mr
                  ⟨sr, hspr, hclr, hcvr, hfur, hrnd_le, hcnr_le, hltr, hdomr, hunsr, hmr⟩ ihr
                c0_hsplit
                · have hrnd_lt : rnd.toNat < max_rounds.toNat := by c0_bound
                  have hrnd1 : (rnd + 1#64).toNat = rnd.toNat + 1 := by bv_omega
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsplit
                      · c0_hsplit
                        · c0_hsteps_nogrp; c0_call hRound
                          refine ⟨c, F0, F_cur, sr, R, rfl, hspr, hclr, hcnr_le, hltr, hmr,
                            fun cn_n sn mn hspn hcln hcvn hfun hcnn_le hltn huc_le huc_ok
                              hmn => ?_⟩
                          have hcvn' : sn.core.cur_vars = s1.core.cur_vars := hcvn.trans hcvr
                          have hfun' : sn.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            rw [hfun]; exact hfur
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := [i64])
                            (fun (res_n, ()) m_n => ∃ s_n : FullState,
                              FullSparseInvW c F0 F_cur s_n ∧ s_n.core.cur_level = 0 ∧
                              s_n.core.cur_vars = s1.core.cur_vars ∧
                              s_n.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              cn_n.toNat ≤ 2 * s_n.core.cur_vars ∧
                              (∀ i < cn_n.toNat, (s_n.scratch.work_stk1[i]?.getD 0#32).toNat <
                                2 * s_n.core.cur_vars) ∧
                              (res_n = 1#64 ∨ res_n = 20#64) ∧ (res_n = 20#64 → F0.Unsat) ∧
                              (FullMem c s_n ⋆ R) m_n)
                            (fun _ ⟨res_n, ⟨⟩⟩ m_n
                                ⟨s_n, hsp_n, hcl_n, hcv_n, hfu_n, hcn_n', hlt_n', hdom_n, huns_n,
                                 hm_n⟩ => by
                              c0_hsteps
                              exact ihr (cn_n, res_n, rnd + 1#64, ()) m_n (by dsimp only; omega)
                                ⟨s_n, hsp_n, hcl_n, hcv_n, hfu_n, by omega, hcn_n', hlt_n',
                                 hdom_n, huns_n, hm_n⟩)
                            (fun Jn hJn => ?_)
                          c0_hsplit
                          · refine wp_join_group (ts := [i64, i64])
                              (fun (res_u, _, ()) mu => ∃ su : FullState,
                                FullSparseInvW c F0 F_cur su ∧ su.core.cur_level = 0 ∧
                                su.core.cur_vars = s1.core.cur_vars ∧
                                su.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                su.scratch.work_stk1 = sn.scratch.work_stk1 ∧
                                (res_u = 1#64 ∨ res_u = 20#64) ∧ (res_u = 20#64 → F0.Unsat) ∧
                                (FullMem c su ⋆ R) mu)
                              (fun _ ⟨res_u, _, ⟨⟩⟩ mu
                                  ⟨su, hspu, hclu, hcvu, hfuu, hws1u, hdomu, hunsu, hmu⟩ => by
                                c0_hsplit
                                · c0_hsteps
                                  exact hJbr (cn_n, res_u, rnd, ()) mu
                                    ⟨su, hspu, hclu, hcvu, hfuu,
                                     by rw [hcvu, ← hcvr]; exact hcnn_le,
                                     by rw [hws1u, hcvu, ← hcvr]; exact hltn, hdomu, hunsu, hmu⟩
                                · c0_hsteps_nogrp; c0_call hProp
                                  refine ⟨c, F0, F_cur, su, R, rfl, hspu.1, hspu.2.1,
                                    hspu.2.2.2.2.2, hmu,
                                    fun pr1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel_p _ _ _ _ _ _ _ _ _
                                      mp hlenp hwp _ hpermp hfup _ _ hpr1 _ _ hmp => ?_⟩
                                  have hspp : FullSparseInvW c F0 F_cur _ :=
                                    s12b_sparseW_of_prop hspu rfl hlenp hwp hpermp
                                  have hfup' : fuel_p.toNat ≤ s.core.fuel.toNat :=
                                    Nat.le_trans hfup hfuu
                                  c0_hsplit
                                  · c0_hsteps
                                    exact hJbr (cn_n, 20#64, rnd, ()) mp
                                      ⟨_, hspp, hclu, hcvu, hfup',
                                       by rw [hcvu, ← hcvr]; exact hcnn_le,
                                       by rw [hws1u, hcvu, ← hcvr]; exact hltn, Or.inr rfl,
                                       fun _ => level0_unsat_of_conflict_okW hwp hclu
                                         (hpr1 (by c0_bound)).2.2,
                                       hmp⟩
                                  · c0_hsplit
                                    · c0_hsteps
                                      exact hJbr (cn_n, res_u, rnd, ()) mp
                                        ⟨_, hspp, hclu, hcvu, hfup',
                                         by rw [hcvu, ← hcvr]; exact hcnn_le,
                                         by rw [hws1u, hcvu, ← hcvr]; exact hltn, hdomu, hunsu, hmp⟩
                                    · c0_hsteps
                                      exact hJn (res_u, ()) mp
                                        ⟨_, hspp, hclu, hcvu, hfup',
                                         by rw [hcvu, ← hcvr]; exact hcnn_le,
                                         by rw [hws1u, hcvu, ← hcvr]; exact hltn, hdomu, hunsu,
                                         hmp⟩)
                              (fun Ju hJu => ?_)
                            refine wp_loop_inv (ts := [i64])
                              (fun (ui, ()) mui => ∃ sui : FullState,
                                FullSparseInvW c F0 F_cur sui ∧ sui.core.cur_level = 0 ∧
                                sui.core.cur_vars = s1.core.cur_vars ∧
                                sui.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                ui.toNat ≤ sn.scratch.res_sz.toNat ∧
                                sui.scratch.work_stk1 = sn.scratch.work_stk1 ∧
                                sui.scratch.work_stk2 = sn.scratch.work_stk2 ∧
                                (FullMem c sui ⋆ R) mui)
                              (fun (ui, ()) _ => sn.scratch.res_sz.toNat - ui.toNat) ?_ ?_
                            · intro Jui hJui; c0_hsteps
                              exact hJui (0#64, ()) mn ⟨sn, hspn, hcln, hcvn', hfun', Nat.zero_le _,
                                rfl, rfl, hmn⟩
                            · rintro Jui ⟨ui, ⟨⟩⟩ mui
                                ⟨sui, hspui, hclui, hcvui, hfuui, hui_le, hws1ui, hws2ui, hmui⟩ ihui
                              c0_hsplit
                              · have hui_lt : ui.toNat < sn.scratch.res_sz.toNat := by c0_bound
                                have hui1 : (ui + 1#64).toNat = ui.toNat + 1 := by bv_omega
                                have hui_ws2 : ui.toNat < sui.scratch.work_stk2.length := by
                                  have := hspui.1.scratch_ok.work_stk2_len
                                  have := hspui.1.core_ok.cur_vars_le; omega
                                let ul := sui.scratch.work_stk2[ui.toNat]'hui_ws2
                                have hul_ok : ul.toNat < 2 * sui.core.cur_vars ∧
                                    (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]) := by
                                  have h1 := huc_ok ui.toNat hui_lt
                                  rw [← hws2ui, List.getElem?_eq_getElem hui_ws2,
                                    Option.getD_some] at h1
                                  rw [hcvui, ← hcvr]; exact h1
                                c0_hsteps_nogrp; c0_call hAddUnit
                                refine ⟨c, F0, F_cur, sui, R, rfl, hspui.1, hspui.2.1,
                                  fun _ => hul_ok.2, hmui,
                                  fun ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m_a
                                    hlen_a hw_a hcl_a hlt_a _ hm_a => ?_⟩
                                have hsp_a : FullSparseInvW c F0 F_cur _ :=
                                  ⟨hlen_a, hw_a, hspui.2.2.1, hspui.2.2.2.1, hspui.2.2.2.2.1,
                                   hspui.2.2.2.2.2⟩
                                c0_hsplit
                                · c0_hsteps
                                  exact ihui (ui + 1#64, ()) _ (by dsimp only; omega)
                                    ⟨_, s12b_sparseW_with_delayed hsp_a _, hcl_a, hcvui, hfuui,
                                     by omega, hws1ui, hws2ui, by assumption⟩
                                · c0_hsteps
                                  exact hJu (20#64, ui, ()) m_a ⟨_, hsp_a, hcl_a, hcvui, hfuui,
                                    hws1ui, Or.inr rfl,
                                    fun _ => (hlt_a hul_ok.1 (by c0_bound)).1, hm_a⟩
                              · c0_hsteps
                                exact hJu (res_r, ui, ()) mui ⟨sui, hspui, hclui, hcvui, hfuui,
                                  hws1ui, hdomr, hunsr, hmui⟩
                          · c0_hsteps
                            exact hJn (res_r, ()) mn ⟨sn, hspn, hcln, hcvn', hfun',
                              by rw [hcvn]; exact hcnn_le, by rw [hcvn]; exact hltn, hdomr, hunsr,
                              hmn⟩
                        · c0_hsteps
                          exact hJbr (cn_r, res_r, rnd, ()) mr
                            ⟨sr, hspr, hclr, hcvr, hfur, hcnr_le, hltr, hdomr, hunsr, hmr⟩
                      · c0_hsteps
                        exact hJbr (cn_r, res_r, rnd, ()) mr
                          ⟨sr, hspr, hclr, hcvr, hfur, hcnr_le, hltr, hdomr, hunsr, hmr⟩
                    · c0_hsteps
                      exact hJbr (cn_r, res_r, rnd, ()) mr
                        ⟨sr, hspr, hclr, hcvr, hfur, hcnr_le, hltr, hdomr, hunsr, hmr⟩
                  · c0_hsteps
                    exact hJbr (cn_r, res_r, rnd, ()) mr
                      ⟨sr, hspr, hclr, hcvr, hfur, hcnr_le, hltr, hdomr, hunsr, hmr⟩
                · c0_hsteps
                  exact hJbr (cn_r, res_r, rnd, ()) mr
                    ⟨sr, hspr, hclr, hcvr, hfur, hcnr_le, hltr, hdomr, hunsr, hmr⟩))
    (fun Jbt hJbt => by
      obtain ⟨F_cur, hw⟩ := hsp.1.witness
      have hlen := hsp.1.lengths
      have hcl_lt : s.core.cur_level < 2 ^ 64 := by
        have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
        have := hlen.core_ok.cur_vars_le; omega
      fvt_steps
      · c0_call hBacktrack
        refine ⟨c, s, R, rfl, hlen, hcl_lt, (fun hpos => by
            have := hlen.core_ok.cur_vars_le; have := hw.cur_level_le
            have := hlen.core_ok.trail_end_le
            have h0n : (0 : BitVec 64).toNat = 0 := rfl
            rw [h0n] at hpos ⊢; omega),
          hw.trail_lits_lt, hm0,
          fun _ _ _ _ _ _ _ _ _ _ _ hlen1 _ _ hcl1 hpr1 _ _ _ hw1 _ hm1 => ?_⟩
        have hsp1 := FullTransHelpers.fullBacktrack_sparse hsp rfl hlen1 hpr1 hw1
        obtain ⟨F_c1, hw1'⟩ := hsp1.1.witness
        exact hJbt () _ ⟨F_c1, _, ⟨hsp1.1.lengths, hw1', hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1,
          hsp1.2.2.2.2⟩, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
      · have hcl0' : s.core.cur_level = 0 := by
          have h1 : s.core.cur_level % 2 ^ 64 = 0 := by c0_bound
          rwa [Nat.mod_eq_of_lt hcl_lt] at h1
        exact hJbt () m0 ⟨F_cur, s, ⟨hlen, hw, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩,
          hcl0', Nat.le_refl _, hm0⟩)

theorem full_backbone_m6_s12b_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hPrio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (hSched : ∀ a m Q X, fullBackboneSchedM6Spec a m Q X →
      Γ "full_backbone_sched_m6" [i64] [i64] a m Q X)
    (hRound : ∀ a m Q X, fullBackboneRoundM6Spec a m Q X →
      Γ "full_backbone_round_m6" [i64, i64, .bool] [i64] a m Q X)
    (hKeep : ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Γ "full_backbone_keep_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Func.wp Γ full_backbone_m6_body a m Q X :=
  full_backbone_m6_s12b_del_wp Γ hBacktrack
    (fun a m Q X h => hProp a m Q X (fullPropagateSpec_of_del h))
    hAddUnit hPrio hSched hRound hKeep

/-! ## 4. `full_dense_prop_unit_m7` (`P1-6c` `unass > 1u` Early Break) -/

private def DpStatePres (s s' : FullState) : Prop :=
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.arena_len = s.core.arena_len ∧
  s'.core.fuel = s.core.fuel ∧
  s'.core.wvec = s.core.wvec ∧
  s'.core.wstk = s.core.wstk ∧
  s'.core.wlen = s.core.wlen ∧
  fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.red_refs = s.scratch.red_refs ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

private theorem dpStatePres_refl (s : FullState) : DpStatePres s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem dpStatePres_trans {s1 s2 s3 : FullState}
    (h12 : DpStatePres s1 s2) (h23 : DpStatePres s2 s3) : DpStatePres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1, h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- `full_dense_prop_unit_m7` (Step-12B) satisfies `FullM6BveFwd.fullDensePropUnitM6Spec`. -/
theorem full_dense_prop_unit_m7_s12b_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullDensePropUnitM6Spec a m Q X →
      Func.wp Γ full_dense_prop_unit_m7_body a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, hQ⟩ := fullDensePropUnitM6Spec_elim hs
  have hmx := c.hmaxv; have hwc := c.hwcap; have harc := c.harena
  unfold dimacsBound at hmx hwc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hret_t : ∀ s1 m1, FullDenseInvW c F0 F_cur s1 → DpStatePres s0 s1 →
      (FullMem c s1 ⋆ R) m1 → Q (true, ()) m1 :=
    fun s1 m1 hdw1 hp hm1 => hQ true s1 m1 hdw1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.2.2 (fun h => by cases h) hm1
  have hret_f : ∀ s1 m1, FullDenseInvW c F0 F_cur s1 → DpStatePres s0 s1 → F0.Unsat →
      (FullMem c s1 ⋆ R) m1 → Q (false, ()) m1 :=
    fun s1 m1 hdw1 hp hu hm1 => hQ false s1 m1 hdw1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.2.2 (fun _ => hu) hm1
  unfold Func.wp full_dense_prop_unit_m7_body
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!; exact hret_t s0 m0 hdw0 (dpStatePres_refl s0) hm0
  · have hlit_lt : lit.toNat < 2 * s0.core.cur_vars := by omega
    have hlit_val_idx : (lit.setWidth 64).toNat < s0.core.vals.length := by
      rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
    c0_hsteps_nogrp
    c0_hsplit
    · c0_hsteps!; exact hret_t s0 m0 hdw0 (dpStatePres_refl s0) hm0
    · have hv_lit1 : s0.core.vals[lit.toNat]?.getD 0#8 = 1#8 := by
        have hdom := hdw0.2.1.vals_domain lit.toNat hlit_lt
        have hlt_v : lit.toNat < s0.core.vals.length := by rw [hdw0.1.core_ok.vals_len]; omega
        rw [List.getElem?_eq_getElem hlt_v, Option.getD_some] at hdom ⊢
        exact m6_bv8_dom_pos_sle hdom hc
      have hent_lit : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) :=
        m6_vals_pos_entails hdw0.2.1 hdw0.2.2.2.2.2.1 hlit_lt hv_lit1
      have hnl_toNat : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := rfl
      have hnl_lt : (lit ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
        rw [hnl_toNat]; have := fullInv_var_xor1 lit.toNat; omega
      have hdw_s0 := m6_denseWatchesInv_of_w hdw0
      have hbd_nl := hdw_s0.layout.bounds _ hnl_lt
      have hwlen_le := hdw0.1.core_ok.wlen_le
      have hnl_wv0 : ((lit ^^^ 1#32).setWidth 64 <<< (1 : Nat)).toNat < s0.core.wvec.length := by
        rw [hdw0.1.core_ok.wvec_len]; c0_bound
      have hnl_wv1 : ((lit ^^^ 1#32).setWidth 64 <<< (1 : Nat) + 1#64).toNat <
          s0.core.wvec.length := by
        rw [hdw0.1.core_ok.wvec_len]; c0_bound
      c0_hsteps_nogrp
      let off_nl :=
        (s0.core.wvec[((lit ^^^ 1#32).setWidth 64 <<< (1 : Nat)).toNat]'hnl_wv0).setWidth 64
      let sz_nl :=
        (s0.core.wvec[((lit ^^^ 1#32).setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hnl_wv1).setWidth 64
      let end_nl := off_nl + sz_nl
      have hoff_nl_eq : off_nl.toNat = fullWatchOffCore s0.core (lit ^^^ 1#32).toNat := by
        unfold off_nl fullWatchOffCore
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some,
          m6_zext32_toNat]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      have hsz_nl_eq : sz_nl.toNat = fullWatchSizeCore s0.core (lit ^^^ 1#32).toNat := by
        unfold sz_nl fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some,
          m6_zext32_toNat]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      have hend_nl_eq : end_nl.toNat = off_nl.toNat + sz_nl.toNat := by
        dsimp only [end_nl]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
        (fun (_, ()) mb => ∃ s1 : FullState,
          FullDenseInvW c F0 F_cur s1 ∧ DpStatePres s0 s1 ∧ (FullMem c s1 ⋆ R) mb)
        (fun rem (p, ()) mp => ∃ sp : FullState,
          p.toNat ≤ end_nl.toNat ∧ rem = end_nl.toNat - p.toNat ∧
          FullDenseInvW c F0 F_cur sp ∧ DpStatePres s0 sp ∧
          DenseWatchSliceOk F_cur sp.core (lit ^^^ 1#32).toNat p.toNat rem ∧
          (FullMem c sp ⋆ R) mp)
        ?_ ?_ ?_
      · -- Loop 2: scan `lit` watches to mark root-satisfied large clauses `PH_GARB`
        rintro _ ⟨_, ⟨⟩⟩ m1 ⟨s1, hdw1, hp1, hm1⟩
        have hdw_s1 := m6_denseWatchesInv_of_w hdw1
        have hwlen1_le := hdw1.1.core_ok.wlen_le
        have hlit_lt1 : lit.toNat < 2 * s1.core.cur_vars := by rw [hp1.1]; exact hlit_lt
        have hbd_l := hdw_s1.layout.bounds _ hlit_lt1
        have hlit_wv0 : (lit.setWidth 64 <<< (1 : Nat)).toNat < s1.core.wvec.length := by
          rw [hdw1.1.core_ok.wvec_len]; c0_bound
        have hlit_wv1 : (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s1.core.wvec.length := by
          rw [hdw1.1.core_ok.wvec_len]; c0_bound
        c0_hsteps_nogrp
        let off_l := (s1.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlit_wv0).setWidth 64
        let sz_l :=
          (s1.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hlit_wv1).setWidth 64
        let end_l := off_l + sz_l
        have hoff_l_eq : off_l.toNat = fullWatchOffCore s1.core lit.toNat := by
          unfold off_l fullWatchOffCore
          rw [List.getElem?_eq_getElem (by rw [hdw1.1.core_ok.wvec_len]; omega), Option.getD_some,
            m6_zext32_toNat]
          exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
        have hsz_l_eq : sz_l.toNat = fullWatchSizeCore s1.core lit.toNat := by
          unfold sz_l fullWatchSizeCore
          rw [List.getElem?_eq_getElem (by rw [hdw1.1.core_ok.wvec_len]; omega), Option.getD_some,
            m6_zext32_toNat]
          exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
        have hend_l_eq : end_l.toNat = off_l.toNat + sz_l.toNat := by
          dsimp only [end_l]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
          (fun (_, ()) m2 => ∃ s2 : FullState,
            FullDenseInvW c F0 F_cur s2 ∧ DpStatePres s0 s2 ∧ (FullMem c s2 ⋆ R) m2)
          (fun rem (p, ()) mp => ∃ sp : FullState,
            p.toNat ≤ end_l.toNat ∧ rem = end_l.toNat - p.toNat ∧
            FullDenseInvW c F0 F_cur sp ∧ DpStatePres s0 sp ∧
            DenseWatchSliceOk F_cur sp.core lit.toNat p.toNat rem ∧
            (FullMem c sp ⋆ R) mp)
          ?_ ?_ ?_
        · rintro _ ⟨_, ⟨⟩⟩ m2 ⟨s2, hdw2, hp2, hm2⟩
          c0_hsteps!; exact hret_t s2 m2 hdw2 hp2 hm2
        · rintro B2 L2 rem ⟨p, ⟨⟩⟩ mp hB2 hL2 ⟨sp, hp_le, hrem, hdwp, hpp, hslice, hmp⟩
          have hlt1 : (s1.core.wvec[2 * lit.toNat % 2 ^ 64]'(by
              rw [hdw1.1.core_ok.wvec_len]; omega)).toNat = off_l.toNat := by
            rw [hoff_l_eq]; unfold fullWatchOffCore
            rw [List.getElem?_eq_getElem (by rw [hdw1.1.core_ok.wvec_len]; omega),
              Option.getD_some]
            exact congrArg BitVec.toNat (m6_getElem_congr (by omega) _ _)
          have hlt2 : (s1.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hdw1.1.core_ok.wvec_len]; simp; omega)).toNat = sz_l.toNat := by
            rw [hsz_l_eq]; unfold fullWatchSizeCore
            rw [List.getElem?_eq_getElem (by rw [hdw1.1.core_ok.wvec_len]; omega),
              Option.getD_some]
            exact congrArg BitVec.toNat (m6_getElem_congr (by simp; omega) _ _)
          have hsum_l : (off_l.toNat + sz_l.toNat) % 2 ^ 64 = end_l.toNat := by
            rw [Nat.mod_eq_of_lt (by omega), hend_l_eq]
          c0_hsplit
          · have hp_lt : p.toNat < end_l.toNat := by
              rw [hlt1, hlt2, hsum_l] at hc; exact hc
            have hpw : p.toNat < sp.core.wstk.length := by
              rw [hdwp.1.core_ok.wstk_len_arr]; omega
            have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
            cases hslice with
            | empty => omega
            | @bin _ rem1 w0 hwp hflag _ _ _ hrest =>
              have hw0_eq : sp.core.wstk[p.toNat]'hpw = w0 := by
                rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
              c0_hsplit
              · c0_hsteps!
                exact hL2 rem1 (p + 1#64, ()) mp (by omega)
                  ⟨sp, by omega, by omega, hdwp, hpp, by rw [hp1_nat]; exact hrest, hmp⟩
              · rw [hw0_eq] at hc; exact absurd hc hflag
            | @occ _ rem2 w0 cr hwp hwp1 hflag _ _ href hrest =>
              have hw0_eq : sp.core.wstk[p.toNat]'hpw = w0 := by
                rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
              have hrem2 : end_l.toNat - p.toNat = rem2 + 2 := by omega
              have hp1_lt : (p + 1#64).toNat < end_l.toNat := by omega
              have hp1_w : (p + 1#64).toNat < sp.core.wstk.length := by
                rw [hdwp.1.core_ok.wstk_len_arr]; omega
              have hp1_c0 : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
                simp; omega
              have hcr_eq :
                  sp.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hdwp.1.core_ok.wstk_len_arr]; omega) = cr := by
                rw [List.getElem?_eq_getElem (by omega)] at hwp1
                exact (m6_getElem_congr hp1_c0 _ _).trans (Option.some.inj hwp1)
              have hcr_eq' : sp.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_w = cr :=
                (m6_getElem_congr (by c0_bound) _ _).trans hcr_eq
              have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
              have hrest' : DenseWatchSliceOk F_cur sp.core lit.toNat (p + 1#64 + 1#64).toNat
                  rem2 := by
                rw [hp2_nat]; exact hrest
              have hwf_cr := hdwp.2.1.arena.refs_wf cr.toNat href
              have har_le := hdwp.1.core_ok.arena_len_le
              have hcr_ar : (cr.setWidth 64).toNat < sp.core.arena.length := by
                rw [hdwp.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
              c0_hsplit
              · rw [hw0_eq] at hc; exact absurd hflag hc
              · c0_hsplit
                · rw [hlt1, hlt2, hsum_l] at hc; simp at hc; omega
                · c0_hsplit
                  · c0_hsteps!
                    exact hL2 rem2 (p + 1#64 + 1#64, ()) mp
                      (by omega) ⟨sp, by omega, by omega, hdwp, hpp, hrest', hmp⟩
                  · simp only [hcr_eq, hcr_eq'] at hc ⊢
                    have har_len_cr : cr.toNat < sp.core.arena.length := by
                      rw [hdwp.1.core_ok.arena_len_arr]; omega
                    have hng : fullArenaClauseGarb sp cr.toNat = false := by
                      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                      rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                      change (sp.core.arena[cr.toNat]'har_len_cr &&& 0x00080000#32) = 0#32 at hc
                      rw [hc]; rfl
                    have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < sp.core.arena.length := by
                      rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                    let sz_c := sp.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
                    have hsz_eq : sz_c.toNat = fullArenaClauseSizeCore sp.core cr.toNat := by
                      unfold sz_c fullArenaClauseSizeCore
                      rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
                        Option.getD_some]
                      exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                    c0_hsteps_nogrp
                    refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                      (fun (_, _, ()) ms => ms = mp)
                      (fun rem_k (k, ()) mk => k.toNat ≤ sz_c.toNat ∧
                        rem_k = sz_c.toNat - k.toNat ∧ mk = mp)
                      ?_ ?_ ?_
                    · rintro _ ⟨sat_b, _, ⟨⟩⟩ ms rfl
                      refine wp_join0 (P := fun mj => ∃ sm : FullState,
                        FullDenseInvW c F0 F_cur sm ∧ DpStatePres s0 sm ∧
                        DenseWatchSliceOk F_cur sm.core lit.toNat (p + 1#64 + 1#64).toNat rem2 ∧
                        (FullMem c sm ⋆ R) mj)
                        (fun _ mj ⟨sm, hdwm, hpm, hrestm, hmm⟩ => by
                          c0_hsteps!
                          exact hL2 rem2 (p + 1#64 + 1#64, ()) mj (by omega)
                            ⟨sm, by omega, by omega, hdwm, hpm, hrestm, hmm⟩)
                        (fun Jm hJm => by
                          c0_hsplit
                          · have hhdr_eq : sp.core.arena[cr.toNat]'har_len_cr =
                                fullArenaHdr sp cr.toNat := by
                              unfold fullArenaHdr fullArenaHdrCore
                              rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                            c0_hsteps!
                            let ag' := sp.core.arena_garbage + 3#64 + sz_c.setWidth 64
                            let ar' := sp.core.arena.set (cr.setWidth 64).toNat
                              (sp.core.arena[(cr.setWidth 64).toNat]'hcr_ar ||| 0x00080000#32)
                            let smg : FullState :=
                              { sp with core :=
                                { sp.core with arena := ar', arena_garbage := ag' } }
                            have har'_eq : ar' = sp.core.arena.set cr.toNat
                                (fullArenaHdr sp cr.toNat ||| 0x00080000#32) := by
                              dsimp only [ar']; rw [← hhdr_eq]
                              have hval := m6_getElem_congr (m6_zext32_toNat cr) hcr_ar har_len_cr
                              rw [hval, m6_zext32_toNat]
                            have hmg := m6_fullDenseInvW_markGarb hdwp href (arena' := ar')
                              (ag' := ag')
                              (by simp [ar', hdwp.1.core_ok.arena_len_arr])
                              (Or.inl (by rw [har'_eq]; exact List.getElem?_set_self har_len_cr))
                              (fun i hne _ => by
                                rw [har'_eq]; exact List.getElem?_set_ne hne.symm)
                            have hpres_mg : DpStatePres sp smg :=
                              ⟨rfl, rfl, rfl, rfl, rfl, rfl, hmg.2, rfl, rfl, rfl, rfl, rfl, rfl⟩
                            have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                              rw [CNF.entails_def]; exact fun _ hx => hx
                            have hrest_mg := hrest'.mono (k := sp.core) (k' := smg.core) hent_r
                              (Nat.le_refl _) (fun r hr => by
                                change r ∈ fullArenaClauseRefs smg; rw [hmg.2]; exact hr)
                              (fun _ _ _ => rfl)
                            have hmg_mem : (FullMem c smg ⋆ R) m := hm
                            exact hJm m ⟨smg, hmg.1, dpStatePres_trans hpp hpres_mg, hrest_mg,
                              hmg_mem⟩
                          · c0_hsteps!
                            exact hJm ms ⟨sp, hdwp, hpp, hrest', hmp⟩)
                    · rintro Bk Lk rem_k ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hk_le, rfl, rfl⟩
                      have hsz_c0 : sp.core.arena[(cr.toNat + BitVec.toNat (2 : BitVec 64)) %
                          2 ^ 64]'(by rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) = sz_c :=
                        m6_getElem_congr (by c0_bound) _ _
                      c0_hsplit
                      · have hk_lt : k.toNat < sz_c.toNat := by rw [hsz_c0] at hc; exact hc
                        have hcri : (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                            sp.core.arena.length := by
                          rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                        have hcl_lt : (sp.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'
                            hcri).toNat < 2 * sp.core.cur_vars := by
                          have hmem : (sp.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'
                              hcri).toNat ∈ fullArenaClauseLitsCore sp.core cr.toNat := by
                            rw [mem_fullArenaClauseLitsCore_iff (by
                              rw [hdwp.1.core_ok.arena_len_arr]; omega)]
                            exact ⟨k.toNat, by omega, congrArg BitVec.toNat
                              (m6_getElem_congr (by c0_bound) _ _)⟩
                          exact hdwp.2.1.arena.lits_lt cr.toNat href hng _ hmem
                        have hcl_v : ((sp.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'
                            hcri).setWidth 64).toNat < sp.core.vals.length := by
                          rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; c0_bound
                        c0_hsplit
                        · c0_hsteps!; exact hBk (true, k, ()) mk rfl
                        · c0_hsteps!
                          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                          exact hLk (sz_c.toNat - (k + 1#32).toNat) (k + 1#32, ()) mk
                            (by omega) ⟨by omega, rfl, rfl⟩
                      · c0_hsteps!; exact hBk (false, k, ()) mk rfl
                    · intro _ Lk _ hLk; c0_hsteps!
                      exact hLk sz_c.toNat (0#32, ()) mp ⟨Nat.zero_le _, by simp, rfl⟩
          · c0_hsteps!; exact hB2 (p, ()) mp ⟨sp, hdwp, hpp, hmp⟩
        · intro _ L2 _ hL2; c0_hsteps!
          exact hL2 sz_l.toNat (off_l, ()) m1
            ⟨s1, by omega, by omega, hdw1, hp1, by
              rw [hoff_l_eq, hsz_l_eq]
              exact hdw_s1.slices lit.toNat hlit_lt1, hm1⟩
      · -- Loop 1 body: process watch entry at `p` on `nl = lit ^ 1` (with `unass > 1` early break)
        rintro B1 L1 rem ⟨p, ⟨⟩⟩ mp hB1 hL1 ⟨sp, hp_le, hrem, hdwp, hpp, hslice, hmp⟩
        have hlt1 : (s0.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'(by
            rw [hdw0.1.core_ok.wvec_len]; omega)).toNat = off_nl.toNat := by
          rw [hoff_nl_eq]; unfold fullWatchOffCore
          rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega),
            Option.getD_some]
          exact congrArg BitVec.toNat (m6_getElem_congr (by rw [hnl_toNat]; omega) _ _)
        have hlt2 : (s0.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by rw [hdw0.1.core_ok.wvec_len]; simp; omega)).toNat = sz_nl.toNat := by
          rw [hsz_nl_eq]; unfold fullWatchSizeCore
          rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega),
            Option.getD_some]
          exact congrArg BitVec.toNat (m6_getElem_congr (by simp [hnl_toNat]; omega) _ _)
        have hsum_nl : (off_nl.toNat + sz_nl.toNat) % 2 ^ 64 = end_nl.toNat := by
          rw [Nat.mod_eq_of_lt (by omega), hend_nl_eq]
        c0_hsplit
        · have hp_lt : p.toNat < end_nl.toNat := by
            rw [hlt1, hlt2, hsum_nl] at hc; exact hc
          have hpw : p.toNat < sp.core.wstk.length := by
            rw [hdwp.1.core_ok.wstk_len_arr]; omega
          have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
          cases hslice with
          | empty => omega
          | @bin _ rem1 w0 hwp hflag _ hot_lt hent_bin hrest =>
            have hw0_eq : sp.core.wstk[p.toNat]'hpw = w0 := by
              rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
            let ot := w0 &&& 0x7FFFFFFF#32
            have hot_lt' : ot.toNat < 2 * sp.core.cur_vars := hot_lt
            have hot_v : (ot.setWidth 64).toNat < sp.core.vals.length := by
              rw [hdwp.1.core_ok.vals_len, m6_zext32_toNat]; have := hdwp.1.core_ok.cur_vars_le
              omega
            have hent_ot : (cnfOfClauses F_cur).EntailsClause (cnfClause [ot.toNat]) :=
              m6_resolve_bin_unit (a := lit.toNat) hent_bin hent_lit
            c0_hsplit
            · rw [hw0_eq]
              c0_hsplit
              · have hv_ff : sp.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 := by
                  have hdom := hdwp.2.1.vals_domain ot.toNat hot_lt'
                  have hlt_ov : ot.toNat < sp.core.vals.length := by
                    rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; omega
                  rw [List.getElem?_eq_getElem hlt_ov, Option.getD_some] at hdom ⊢
                  exact m6_bv8_dom_neg_slt hdom hc
                have hneg_ot := m6_vals_neg_entails hdwp.2.1 hdwp.2.2.2.2.2.1 hot_lt' hv_ff
                have hunsat : (cnfOfClauses F_cur).Unsat :=
                  m6_unsat_of_lit_and_neg hent_ot hneg_ot
                c0_hsteps!
                let sinc := { sp with core := { sp.core with inconsistent := 1#64 } }
                exact hret_f sinc _ (m6_fullDenseInvW_set_inc hdwp hunsat)
                  (dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                    rfl, rfl, rfl⟩) (hdwp.2.1.ext_sound.2 hunsat) hm
              · c0_hsplit
                · c0_hsteps_nogrp
                  s12b_call hAddUnit
                  refine ⟨c, F0, F_cur, sp, R, rfl, hdwp.1, hdwp.2.1, fun _ => hent_ot, hmp, ?_⟩
                  intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
                    phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m_u su hlen_u hw_u hcl_u
                    hfu _ hm_u
                  have hdw_u : FullDenseInvW c F0 F_cur su :=
                    m6_fullDenseInvW_of_addUnit hdwp hlen_u hw_u hcl_u rfl rfl rfl rfl rfl rfl rfl
                  have hp_u : DpStatePres s0 su :=
                    dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                      rfl, rfl, rfl⟩
                  c0_hsplit
                  · c0_hsteps!
                    have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                      rw [CNF.entails_def]; exact fun _ hx => hx
                    have hrest_u := hrest.mono (k := sp.core) (k' := su.core) hent_r
                      (Nat.le_refl _) (fun _ hr => hr) (fun _ _ _ => rfl)
                    exact hL1 rem1 (p + 1#64, ()) m_u (by omega)
                      ⟨su, by omega, by omega, hdw_u, hp_u, by rw [hp1_nat]; exact hrest_u, hm_u⟩
                  · c0_hsteps!
                    exact hret_f su m_u hdw_u hp_u (hfu hot_lt' (by simpa using hc)).1 hm_u
                · c0_hsteps!
                  exact hL1 rem1 (p + 1#64, ()) mp (by omega)
                    ⟨sp, by omega, by omega, hdwp, hpp, by rw [hp1_nat]; exact hrest, hmp⟩
            · rw [hw0_eq] at hc; exact absurd hc hflag
          | @occ _ rem2 w0 cr hwp hwp1 hflag _ _ href hrest =>
            have hw0_eq : sp.core.wstk[p.toNat]'hpw = w0 := by
              rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
            have hrem2 : end_nl.toNat - p.toNat = rem2 + 2 := by omega
            have hp1_lt : (p + 1#64).toNat < end_nl.toNat := by omega
            have hp1_w : (p + 1#64).toNat < sp.core.wstk.length := by
              rw [hdwp.1.core_ok.wstk_len_arr]; omega
            have hp1_c0 : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              simp; omega
            have hcr_eq :
                sp.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hdwp.1.core_ok.wstk_len_arr]; omega) = cr := by
              rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.wstk_len_arr]; omega)] at hwp1
              exact (m6_getElem_congr hp1_c0 _ _).trans (Option.some.inj hwp1)
            have hcr_eq' : sp.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_w = cr :=
              (m6_getElem_congr (by c0_bound) _ _).trans hcr_eq
            have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
            have hrest' : DenseWatchSliceOk F_cur sp.core (lit ^^^ 1#32).toNat
                (p + 1#64 + 1#64).toNat rem2 := by
              rw [hp2_nat]; exact hrest
            have hwf_cr := hdwp.2.1.arena.refs_wf cr.toNat href
            have har_le := hdwp.1.core_ok.arena_len_le
            have har_len_cr : cr.toNat < sp.core.arena.length := by
              rw [hdwp.1.core_ok.arena_len_arr]; omega
            have hcr_ar : (cr.setWidth 64).toNat < sp.core.arena.length := by
              rw [hdwp.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
            c0_hsplit
            · rw [hw0_eq] at hc; exact absurd hflag hc
            · c0_hsplit
              · rw [hlt1, hlt2, hsum_nl] at hc; simp at hc; omega
              · c0_hsplit
                · c0_hsteps!
                  exact hL1 rem2 (p + 1#64 + 1#64, ()) mp
                    (by omega) ⟨sp, by omega, by omega, hdwp, hpp, hrest', hmp⟩
                · simp only [hcr_eq, hcr_eq'] at hc ⊢
                  have hng : fullArenaClauseGarb sp cr.toNat = false := by
                    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                    rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                    change (sp.core.arena[cr.toNat]'har_len_cr &&& 0x00080000#32) = 0#32 at hc
                    rw [hc]; rfl
                  have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < sp.core.arena.length := by
                    rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                  let sz_c := sp.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
                  have hsz_eq : sz_c.toNat = fullArenaClauseSizeCore sp.core cr.toNat := by
                    unfold sz_c fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
                      Option.getD_some]
                    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                  c0_hsteps_nogrp
                  refine wp_loop_break_group (brkTs := [.bool, i32, i32, i32])
                    (lpTs := [i32, i32, i32])
                    (fun (sat_b, unass_b, ulit_b, _k_b, ()) ms => ms = mp ∧
                      (sat_b = false →
                        (unass_b = 0#32 → ∀ j < sz_c.toNat,
                          sp.core.vals[(sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat]?.getD
                            0#8 = 0xFF#8) ∧
                        (unass_b = 1#32 →
                          ulit_b.toNat < 2 * sp.core.cur_vars ∧
                          ∀ j < sz_c.toNat,
                            let lj := (sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat
                            lj ≠ ulit_b.toNat → sp.core.vals[lj]?.getD 0#8 = 0xFF#8)))
                    (fun rem_k (unass_k, ulit_k, k, ()) mk =>
                      mk = mp ∧ k.toNat ≤ sz_c.toNat ∧
                      rem_k = sz_c.toNat - k.toNat ∧ unass_k.toNat ≤ k.toNat ∧
                      (unass_k = 0#32 → ∀ j < k.toNat,
                        sp.core.vals[(sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat]?.getD
                          0#8 = 0xFF#8) ∧
                      (unass_k = 1#32 →
                        ulit_k.toNat < 2 * sp.core.cur_vars ∧
                        ∀ j < k.toNat,
                          let lj := (sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat
                          lj ≠ ulit_k.toNat → sp.core.vals[lj]?.getD 0#8 = 0xFF#8))
                    ?_ ?_ ?_
                  · rintro _ ⟨sat_b, unass_b, ulit_b, _k_b, ⟨⟩⟩ ms ⟨rfl, hpost⟩
                    refine wp_join0 (P := fun mj => ∃ sm : FullState,
                      FullDenseInvW c F0 F_cur sm ∧ DpStatePres s0 sm ∧
                      DenseWatchSliceOk F_cur sm.core (lit ^^^ 1#32).toNat
                        (p + 1#64 + 1#64).toNat rem2 ∧ (FullMem c sm ⋆ R) mj)
                      (fun _ mj ⟨sm, hdwm, hpm, hrestm, hmm⟩ => by
                        c0_hsteps!
                        exact hL1 rem2 (p + 1#64 + 1#64, ()) mj (by omega)
                          ⟨sm, by omega, by omega, hdwm, hpm, hrestm, hmm⟩)
                      (fun Jm hJm => by
                        c0_hsplit
                        · have hhdr_eq' : sp.core.arena[cr.toNat]'har_len_cr =
                              fullArenaHdr sp cr.toNat := by
                            unfold fullArenaHdr fullArenaHdrCore
                            rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                          c0_hsteps!
                          let ag' := sp.core.arena_garbage + 3#64 + sz_c.setWidth 64
                          let ar' := sp.core.arena.set (cr.setWidth 64).toNat
                            (sp.core.arena[(cr.setWidth 64).toNat]'hcr_ar ||| 0x00080000#32)
                          let smg : FullState :=
                            { sp with core := { sp.core with arena := ar', arena_garbage := ag' } }
                          have har'_eq : ar' = sp.core.arena.set cr.toNat
                              (fullArenaHdr sp cr.toNat ||| 0x00080000#32) := by
                            dsimp only [ar']; rw [← hhdr_eq']
                            have hval := m6_getElem_congr (m6_zext32_toNat cr) hcr_ar har_len_cr
                            rw [hval, m6_zext32_toNat]
                          have hmg := m6_fullDenseInvW_markGarb hdwp href (arena' := ar')
                            (ag' := ag')
                            (by simp [ar', hdwp.1.core_ok.arena_len_arr])
                            (Or.inl (by rw [har'_eq]; exact List.getElem?_set_self har_len_cr))
                            (fun i hne _ => by rw [har'_eq]; exact List.getElem?_set_ne hne.symm)
                          have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                            rw [CNF.entails_def]; exact fun _ hx => hx
                          have hrest_mg := hrest'.mono (k := sp.core) (k' := smg.core) hent_r
                            (Nat.le_refl _) (fun r hr => by
                              change r ∈ fullArenaClauseRefs smg; rw [hmg.2]; exact hr)
                            (fun _ _ _ => rfl)
                          have hmg_mem : (FullMem c smg ⋆ R) m := hm
                          exact hJm m ⟨smg, hmg.1,
                            dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, hmg.2, rfl, rfl,
                              rfl, rfl, rfl, rfl⟩, hrest_mg, hmg_mem⟩
                        · obtain ⟨h0, h1⟩ := hpost hc
                          c0_hsplit
                          · have hall_f : ∀ l ∈ fullArenaClauseLitsCore sp.core cr.toNat,
                                sp.core.vals[l]?.getD 0#8 = 0xFF#8 := fun l hl => by
                              rw [mem_fullArenaClauseLitsCore_iff (by
                                rw [hdwp.1.core_ok.arena_len_arr]; omega)] at hl
                              obtain ⟨j, hj, rfl⟩ := hl
                              have hfj := h0 hc j (by omega)
                              have hlt_j : cr.toNat + 3 + j < sp.core.arena.length := by
                                rw [hdwp.1.core_ok.arena_len_arr]; omega
                              rwa [List.getElem?_eq_getElem hlt_j, Option.getD_some] at hfj
                            have hunsat : (cnfOfClauses F_cur).Unsat :=
                              m6_clause_all_false_unsat hdwp.2.1 hdwp.2.2.2.2.2.1
                                (hdwp.2.1.arena.entails cr.toNat href hng)
                                (hdwp.2.1.arena.lits_lt cr.toNat href hng) hall_f
                            c0_hsteps!
                            let sinc := { sp with core := { sp.core with inconsistent := 1#64 } }
                            exact hret_f sinc _ (m6_fullDenseInvW_set_inc hdwp hunsat)
                              (dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                                rfl, rfl, rfl, rfl⟩) (hdwp.2.1.ext_sound.2 hunsat) hm
                          · refine wp_join0 (P := fun mj => ∃ sm : FullState,
                              FullDenseInvW c F0 F_cur sm ∧ DpStatePres s0 sm ∧
                              DenseWatchSliceOk F_cur sm.core (lit ^^^ 1#32).toNat
                                (p + 1#64 + 1#64).toNat rem2 ∧ (FullMem c sm ⋆ R) mj)
                              (fun _ mj h => by c0_hsteps!; exact hJm mj h)
                              (fun _ hJ1 => by
                                c0_hsplit
                                · obtain ⟨hu_lt, hu_oth⟩ := h1 hc
                                  have hent_u : (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause [ulit_b.toNat]) :=
                                    m6_clause_one_unass_entails hdwp.2.1 hdwp.2.2.2.2.2.1
                                      (hdwp.2.1.arena.entails cr.toNat href hng)
                                      (hdwp.2.1.arena.lits_lt cr.toNat href hng) fun l hl hne => by
                                        rw [mem_fullArenaClauseLitsCore_iff (by
                                          rw [hdwp.1.core_ok.arena_len_arr]; omega)] at hl
                                        obtain ⟨j, hj, rfl⟩ := hl
                                        have hfj := hu_oth j (by omega)
                                        have hlt_j : cr.toNat + 3 + j < sp.core.arena.length := by
                                          rw [hdwp.1.core_ok.arena_len_arr]; omega
                                        rw [List.getElem?_eq_getElem hlt_j, Option.getD_some] at hfj
                                        exact hfj hne
                                  have hhdr_eq'' : sp.core.arena[cr.toNat]'har_len_cr =
                                      fullArenaHdr sp cr.toNat := by
                                    unfold fullArenaHdr fullArenaHdrCore
                                    rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                                  c0_hsteps_nogrp
                                  let ag' := sp.core.arena_garbage + 3#64 + sz_c.setWidth 64
                                  let ar' := sp.core.arena.set (cr.setWidth 64).toNat
                                    (sp.core.arena[(cr.setWidth 64).toNat]'hcr_ar ||| 0x00080000#32)
                                  let smg : FullState :=
                                    { sp with core :=
                                      { sp.core with arena := ar', arena_garbage := ag' } }
                                  have har'_eq : ar' = sp.core.arena.set cr.toNat
                                      (fullArenaHdr sp cr.toNat ||| 0x00080000#32) := by
                                    dsimp only [ar']; rw [← hhdr_eq'']
                                    have hval :=
                                      m6_getElem_congr (m6_zext32_toNat cr) hcr_ar har_len_cr
                                    rw [hval, m6_zext32_toNat]
                                  have hmg :=
                                    m6_fullDenseInvW_markGarb hdwp href (arena' := ar') (ag' := ag')
                                      (by simp [ar', hdwp.1.core_ok.arena_len_arr])
                                      (Or.inl (by
                                        rw [har'_eq]; exact List.getElem?_set_self har_len_cr))
                                      (fun i hne _ => by
                                        rw [har'_eq]; exact List.getElem?_set_ne hne.symm)
                                  have hmg_mem : (FullMem c smg ⋆ R) m := hm
                                  s12b_call hAddUnit
                                  refine ⟨c, F0, F_cur, smg, R, rfl, hmg.1.1, hmg.1.2.1,
                                    fun _ => hent_u, hmg_mem, ?_⟩
                                  intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass'
                                    unfl' inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m_u su
                                    hlen_u hw_u hcl_u hfu _ hm_u
                                  have hdw_u : FullDenseInvW c F0 F_cur su :=
                                    m6_fullDenseInvW_of_addUnit hmg.1 hlen_u hw_u hcl_u
                                      rfl rfl rfl rfl rfl rfl rfl
                                  have hp_u : DpStatePres s0 su :=
                                    dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, hmg.2, rfl,
                                      rfl, rfl, rfl, rfl, rfl⟩
                                  c0_hsplit
                                  · c0_hsteps!
                                    have hent_r :
                                        (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                                      rw [CNF.entails_def]; exact fun _ hx => hx
                                    have hrest_u := hrest'.mono (k := sp.core) (k' := su.core)
                                      hent_r (Nat.le_refl _) (fun r hr => by
                                        change r ∈ fullArenaClauseRefs smg; rw [hmg.2]; exact hr)
                                      (fun _ _ _ => rfl)
                                    exact hJ1 m_u ⟨su, hdw_u, hp_u, hrest_u, hm_u⟩
                                  · c0_hsteps!
                                    exact hret_f su m_u hdw_u hp_u (hfu hu_lt (by simpa using hc)).1
                                      hm_u
                                · c0_hsteps!
                                  exact hJ1 ms ⟨sp, hdwp, hpp, hrest', hmp⟩))
                  · rintro Bk Lk rem_k ⟨unass_k, ulit_k, k, ⟨⟩⟩ mk hBk hLk
                      ⟨rfl, hk_le, rfl, hun_le, h0k, h1k⟩
                    have hsz_c0 : sp.core.arena[(cr.toNat + BitVec.toNat (2 : BitVec 64)) %
                        2 ^ 64]'(by rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) = sz_c :=
                      m6_getElem_congr (by c0_bound) _ _
                    c0_hsplit
                    · have hk_lt : k.toNat < sz_c.toNat := by rw [hsz_c0] at hc; exact hc
                      have hcri : (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                          sp.core.arena.length := by
                        rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                      let cl_k := sp.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hcri
                      have hclk_eq :
                          (sp.core.arena[cr.toNat + 3 + k.toNat]?.getD 0#32) = cl_k := by
                        rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
                          Option.getD_some]
                        exact m6_getElem_congr (by c0_bound) _ _
                      have hcl_lt : cl_k.toNat < 2 * sp.core.cur_vars := by
                        have hmem : cl_k.toNat ∈ fullArenaClauseLitsCore sp.core cr.toNat := by
                          rw [mem_fullArenaClauseLitsCore_iff (by
                            rw [hdwp.1.core_ok.arena_len_arr]; omega)]
                          exact ⟨k.toNat, by omega, congrArg BitVec.toNat
                            (m6_getElem_congr (by c0_bound) _ _)⟩
                        exact hdwp.2.1.arena.lits_lt cr.toNat href hng _ hmem
                      have hcl_v : (cl_k.setWidth 64).toNat < sp.core.vals.length := by
                        rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; c0_bound
                      have hdom_k := hdwp.2.1.vals_domain cl_k.toNat hcl_lt
                      have hlt_cv : cl_k.toNat < sp.core.vals.length := by
                        rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; omega
                      have hclk_c0 :
                          sp.core.arena[(cr.toNat + BitVec.toNat (3 : BitVec 64) +
                            k.toNat) % 2 ^ 64]'(by
                              rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) = cl_k :=
                        m6_getElem_congr (by c0_bound) _ _
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                      c0_hsplit
                      · c0_hsteps!; exact hBk (true, unass_k, ulit_k, k, ()) mk ⟨rfl, by simp⟩
                      · have hnpos : (BitVec.ofNat 32 0).slt
                            ((sp.core.vals[cl_k.toNat]'hlt_cv).signExtend 32) = false := by
                          simpa only [hclk_c0] using hc
                        refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                          (fun p => (p.1, p.2, ()))
                          (fun p => p.1.toNat ≤ (k + 1#32).toNat ∧
                            (p.1 = 0#32 → ∀ j < (k + 1#32).toNat,
                              sp.core.vals[(sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat]?.getD
                                0#8 = 0xFF#8) ∧
                            (p.1 = 1#32 →
                              p.2.toNat < 2 * sp.core.cur_vars ∧
                              ∀ j < (k + 1#32).toNat,
                                let lj := (sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat
                                lj ≠ p.2.toNat → sp.core.vals[lj]?.getD 0#8 = 0xFF#8))
                          (fun _ ⟨un', ul'⟩ ⟨hun', h0', h1'⟩ => by
                            c0_hsteps!
                            exact hLk (sz_c.toNat - (k + 1#32).toNat) (un', ul', k + 1#32, ()) mk
                              (by omega) ⟨rfl, by omega, rfl, hun', h0', h1'⟩)
                          (fun Jv hJv => by
                            c0_hsplit
                            · have hun1 : (unass_k + 1#32).toNat = unass_k.toNat + 1 := by c0_bound
                              c0_hsplit
                              · -- `P1-6c` early break: `unass_k + 1 > 1` -> `unass_b ∉ {0, 1}`
                                have hgt1 : 1 < (unass_k + 1#32).toNat := by c0_bound
                                c0_hsteps!
                                exact hBk (false, unass_k + 1#32, ulit_k, k, ()) mk
                                  ⟨rfl, fun _ =>
                                    ⟨fun h0 => by
                                      have := congrArg BitVec.toNat h0; simp at this; omega,
                                     fun h1 => by
                                      have := congrArg BitVec.toNat h1; simp at this; omega⟩⟩
                              · c0_hsteps!
                                refine hJv (unass_k + 1#32, cl_k) ⟨by dsimp only; omega, ?_, ?_⟩
                                · intro hz; exfalso
                                  have := congrArg BitVec.toNat hz; rw [hun1] at this; simp at this
                                · intro ho
                                  have ho0 : unass_k = 0#32 := by
                                    apply BitVec.eq_of_toNat_eq
                                    have := congrArg BitVec.toNat ho; rw [hun1] at this
                                    simp at this ⊢; omega
                                  refine ⟨hcl_lt, fun j hj hne => ?_⟩
                                  have hj_lt : j < k.toNat := by
                                    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hk1 ▸ hj))
                                      with h | h
                                    · exact h
                                    · subst h; rw [hclk_eq] at hne; exact absurd rfl hne
                                  exact h0k ho0 j hj_lt
                            · have hvk_ff : sp.core.vals[cl_k.toNat]?.getD 0#8 = 0xFF#8 := by
                                rw [List.getElem?_eq_getElem hlt_cv, Option.getD_some] at hdom_k ⊢
                                have hc' : (sp.core.vals[cl_k.toNat]'hlt_cv).signExtend 32 ≠
                                    0#32 := by simpa only [hclk_c0] using hc
                                exact m6_bv8_dom_neg_of_not_pos_ne0 hdom_k hnpos hc'
                              c0_hsteps!
                              refine hJv (unass_k, ulit_k) ⟨by dsimp only; omega, ?_, ?_⟩
                              · intro hz j hj
                                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hk1 ▸ hj)) with h | h
                                · exact h0k hz j h
                                · subst h; rw [hclk_eq]; exact hvk_ff
                              · intro ho
                                obtain ⟨hul, hoth⟩ := h1k ho
                                refine ⟨hul, fun j hj hne => ?_⟩
                                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hk1 ▸ hj)) with h | h
                                · exact hoth j h hne
                                · subst h; rw [hclk_eq]; exact hvk_ff)
                    · have hk_eq : k = sz_c := by
                        rw [hsz_c0] at hc; apply BitVec.eq_of_toNat_eq; omega
                      c0_hsteps!
                      exact hBk (false, unass_k, ulit_k, k, ()) mk
                        ⟨rfl, fun _ =>
                          ⟨by subst hk_eq; exact h0k, by subst hk_eq; exact h1k⟩⟩
                  · intro _ Lk _ hLk; c0_hsteps!
                    exact hLk sz_c.toNat (0#32, 0#32, 0#32, ()) mp
                      ⟨rfl, Nat.zero_le _, by simp, Nat.zero_le _,
                       fun _ _ h => by simp at h, fun h => by cases h⟩
        · c0_hsteps!; exact hB1 (p, ()) mp ⟨sp, hdwp, hpp, hmp⟩
      · intro _ L1 _ hL1; c0_hsteps!
        exact hL1 sz_nl.toNat (off_nl, ()) m0
          ⟨s0, by omega, by omega, hdw0, dpStatePres_refl s0, by
            rw [hoff_nl_eq, hsz_nl_eq]
            exact hdw_s0.slices _ hnl_lt, hm0⟩

/-! ## 5. `full_forward_sub_m7` (`P1-6b` Reconnect Before Flush + `propagated` Rewind) -/

/-- `full_forward_sub_m7` (Step-12B) certifies `FullFastBveBudgets.fullForwardSubFastSpec`. -/
theorem full_forward_sub_m7_s12b_wp (Γ : Env)
    (hDedup : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hCollectSort : ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Γ "full_fwd_collect_sort_m7" [i64] [i64] a m Q X)
    (hFlushLarge : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hCheckCl : ∀ a m Q X, fullFwdCheckClM7Spec a m Q X →
      Γ "full_fwd_check_cl_m7" [i64, i32] [.bool] a m Q X)
    (hConnectSub : ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
      Γ "full_fwd_connect_subsumer_m7" [i64, i32] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hReconnect : ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Γ "full_fwd_reconnect_irred_m7" [i64] [] a m Q X) :
    ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Func.wp Γ full_forward_sub_m7_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hd0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hrc := c.hred
  unfold dimacsBound at hmx harc hrc
  obtain ⟨F_cur, hw0⟩ := hd0.exists_witness
  unfold Func.wp full_forward_sub_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s0 m0 hd0 rfl rfl (Or.inl rfl) (by simp) hm0
  · c0_hsteps_nogrp
    s12b_call hDedup
    refine ⟨c, F0, F_cur, s0, R, rfl, hw0, hm0, ?_⟩
    intro ok1 s1 m1 hdw1 hcv1 hfl1 hf1 hm1
    c0_hsplit
    · c0_hsteps_nogrp
      s12b_call hFlushUnits
      refine fullDenseFlushUnitsM6Spec_intro rfl hdw1 hm1 ?_
      intro ok2 s2 m2 hdw2 hcv2 _ hfl2 _ _ _ _ _ _ _ hf2 hm2
      have hsp_lt : s2.core.propagated < 2 ^ 64 := by
        have := hdw2.1.core_ok.propagated_le
        have := hdw2.1.core_ok.trail_end_le
        have := hdw2.1.core_ok.cur_vars_le; omega
      c0_hsplit
      · c0_hsteps_nogrp
        s12b_call hCollectSort
        refine fullFwdCollectSortM6Spec_intro rfl hdw2 hm2 ?_
        intro ncand s3 m3 hdw3 hcv3 hal3 hfl3 _ _ _ hnc_le hrr3 hm3
        c0_hsplit
        · c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ()))
            (fun r => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
            (fun _ r ⟨hr_disj, hr20⟩ => by
              c0_hsteps!
              exact hQ r s3 m3 hdw3.toDense (hcv3.trans (hcv2.trans hcv1))
                (hfl3.trans (hfl2.trans hfl1)) hr_disj hr20 hm3)
            (fun J7 hJ7 => by
              c0_hsplit
              · c0_hsteps!
                exact hJ7 20#64 ⟨Or.inr rfl, fun _ =>
                  hdw3.2.1.ext_sound.2 (hdw3.2.1.inconsistent_sound hc)⟩
              · c0_hsteps!; exact hJ7 1#64 ⟨Or.inl rfl, by simp⟩)
        · c0_hsteps_nogrp
          s12b_call hFlushLarge
          refine fullFwdFlushLargeM6Spec_intro rfl hdw3 hm3 ?_
          intro s4 m4 hdw4 hcv4 har4 hal4 hfl4 _ _ _ hrr4 _ _ _ _ hm4
          have hrr4_ok : ∀ k < ncand.toNat,
              (s4.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s4 := by
            intro k hk; rw [hrr4]
            have hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s3 := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, hal4]
            rw [hrefs4]; exact hrr3 k hk
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64, i64])
            (fun r_lp (i, rem, ()) ml => ∃ sl : FullState,
              i.toNat ≤ ncand.toNat ∧ r_lp = ncand.toNat - i.toNat ∧
              FullDenseInvW c F0 F_cur sl ∧
              sl.core.cur_vars = s0.core.cur_vars ∧ sl.core.fuel = s0.core.fuel ∧
              fullArenaClauseRefs sl = fullArenaClauseRefs s4 ∧
              sl.scratch.red_refs = s4.scratch.red_refs ∧
              (FullMem c sl ⋆ R) ml)
            ?_ ?_
          · rintro L r_lp ⟨i, rem, ⟨⟩⟩ ml hL
              ⟨sl, hi_le, rfl, hdwl, hcvl, hfll, hrefsl, hrrl, hml⟩
            refine wp_join0 (P := fun mb => mb = ml)
              (fun _ mb hmb => by
                rcases hmb.symm with rfl
                refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                  (fun sf mf =>
                    FullDenseInvW c F0 F_cur sf ∧
                    sf.core.cur_vars = s0.core.cur_vars ∧ sf.core.fuel = s0.core.fuel ∧
                    (FullMem c sf ⋆ R) mf)
                  (fun _ sf mf ⟨hdwf, hcvf, hflf, hmf⟩ => by
                    c0_hsteps_nogrp
                    c0_hsplit
                    · c0_hsteps!
                      exact hQ 20#64 sf mf hdwf.toDense hcvf hflf (Or.inr rfl)
                        (fun _ => hdwf.2.1.ext_sound.2 (hdwf.2.1.inconsistent_sound hc)) hmf
                    · -- `P1-6b`: reconnect irred BEFORE flushing newly derived units!
                      c0_hsteps_nogrp
                      s12b_call hReconnect
                      refine fullFwdReconnectIrredM6Spec_intro rfl hdwf hmf ?_
                      intro s5 m5 hdw5 hcv5 _ hfl5 _ _ hm5
                      -- Optional `propagated` rewind (`saved_prop < s5.propagated ≤ trail_end`)
                      refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                        (fun s5p m5p =>
                          FullDenseInvW c F0 F_cur s5p ∧
                          s5p.core.cur_vars = s0.core.cur_vars ∧
                          s5p.core.fuel = s0.core.fuel ∧
                          (FullMem c s5p ⋆ R) m5p)
                        (fun _ s5p m5p ⟨hdw5p, hcv5p, hfl5p, hm5p⟩ => by
                          c0_hsteps_nogrp
                          s12b_call hFlushUnits
                          refine fullDenseFlushUnitsM6Spec_intro rfl hdw5p hm5p ?_
                          intro ok6 s6 m6 hdw6 hcv6 _ hfl6 _ _ _ _ _ _ _ hf6 hm6
                          c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                              (fun r => (r, ()))
                              (fun r => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
                              (fun _ r ⟨hr_disj, hr20⟩ => by
                                c0_hsteps!
                                exact hQ r s6 m6 hdw6.toDense (hcv6.trans hcv5p)
                                  (hfl6.trans hfl5p) hr_disj hr20 hm6)
                              (fun J20 hJ20 => by
                                c0_hsplit
                                · c0_hsteps!
                                  exact hJ20 20#64 ⟨Or.inr rfl, fun _ =>
                                    hdw6.2.1.ext_sound.2 (hdw6.2.1.inconsistent_sound hc)⟩
                                · c0_hsteps!; exact hJ20 1#64 ⟨Or.inl rfl, by simp⟩)
                          · c0_hsteps!
                            exact hQ 20#64 s6 m6 hdw6.toDense (hcv6.trans hcv5p)
                              (hfl6.trans hfl5p) (Or.inr rfl)
                              (fun _ => hf6 (by simpa using hc)) hm6)
                        (fun Jrw hJrw => by
                          c0_hsplit
                          · c0_hsplit
                            · have hte5_lt : s5.core.trail_end < 2 ^ 64 := by
                                have := hdw5.1.core_ok.trail_end_le
                                have := hdw5.1.core_ok.cur_vars_le; omega
                              have hle_te : s2.core.propagated ≤ s5.core.trail_end := by
                                rw [Nat.mod_eq_of_lt hsp_lt, Nat.mod_eq_of_lt hte5_lt] at hc
                                exact hc
                              c0_hsteps!
                              let s5p : FullState :=
                                { s5 with core :=
                                  { s5.core with propagated := s2.core.propagated } }
                              exact hJrw s5p _ ⟨m6_fullDenseInvW_with_prop hdw5 hle_te,
                                hcv5.trans hcvf, hfl5.trans hflf, hm⟩
                            · c0_hsteps!
                              exact hJrw s5 m5 ⟨hdw5, hcv5.trans hcvf, hfl5.trans hflf, hm5⟩
                          · c0_hsteps!
                            exact hJrw s5 m5 ⟨hdw5, hcv5.trans hcvf, hfl5.trans hflf, hm5⟩))
                  (fun Jc hJc => by
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsplit
                        · have hcvl_le := hdwl.1.core_ok.cur_vars_le
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i64])
                            (fun rem_v (v, ()) mv => ∃ fl_v : List (BitVec 32),
                              let sv : FullState :=
                                { sl with core := { sl.core with flags := fl_v } }
                              fl_v.length = c.max_vars ∧ v.toNat ≤ sl.core.cur_vars ∧
                              rem_v = sl.core.cur_vars - v.toNat ∧ (FullMem c sv ⋆ R) mv)
                            ?_ ?_
                          · rintro Lv rem_v ⟨v, ⟨⟩⟩ mv hLv ⟨fl_v, hflv, hv_le, rfl, hmv⟩
                            c0_hsplit
                            · have hv_lt : v.toNat < sl.core.cur_vars := by
                                rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                              have hv_fl : v.toNat < fl_v.length := by omega
                              have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
                              c0_hsteps!
                              exact hLv (sl.core.cur_vars - (v + 1#64).toNat) (v + 1#64, ()) _
                                (by omega) ⟨_, by simp [hflv], by omega, rfl, hm⟩
                            · let sv0 : FullState :=
                                { sl with core := { sl.core with flags := fl_v } }
                              have hdw_v0 : FullDenseInvW c F0 F_cur sv0 :=
                                m6_fullDenseInvW_with_flags hdwl hflv
                              c0_hsteps_nogrp
                              refine wp_loop_group (ts := [i64])
                                (fun rem_p (p, ()) mp => ∃ sp : FullState,
                                  p.toNat ≤ sp.core.arena_len ∧
                                  rem_p = sp.core.arena_len - p.toNat ∧
                                  (p.toNat = sp.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
                                  FullDenseInvW c F0 F_cur sp ∧
                                  sp.core.cur_vars = s0.core.cur_vars ∧
                                  sp.core.arena_len = sl.core.arena_len ∧
                                  sp.core.fuel = s0.core.fuel ∧
                                  (FullMem c sp ⋆ R) mp)
                                ?_ ?_
                              · rintro Lp rem_p ⟨p, ⟨⟩⟩ mp hLp
                                  ⟨sp, hp_le, rfl, hp_mem, hdwp, hcvp, halp, hflp, hmp⟩
                                have hal_p := hdwp.1.core_ok.arena_len_le
                                c0_hsplit
                                · have hp_lt : p.toNat < sp.core.arena_len := by
                                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                  have hp_ref : p.toNat ∈ fullArenaClauseRefs sp :=
                                    hp_mem.resolve_left (by omega)
                                  have hwf_p := hdwp.2.1.arena.refs_wf p.toNat hp_ref
                                  have hp_ar : p.toNat < sp.core.arena.length := by
                                    rw [hdwp.1.core_ok.arena_len_arr]; omega
                                  have hp2_ar : (p + 2#64).toNat < sp.core.arena.length := by
                                    rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                                  have hp32 : (p.setWidth 32).toNat = p.toNat := by
                                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                                  let hdr_p := sp.core.arena[p.toNat]'hp_ar
                                  let sz_p := sp.core.arena[(p + 2#64).toNat]'hp2_ar
                                  have hsz_p :
                                      sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat := by
                                    unfold sz_p fullArenaClauseSizeCore
                                    rw [List.getElem?_eq_getElem (by
                                      rw [hdwp.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                                    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                                  c0_hsteps_nogrp
                                  s12b_call hArenaNext
                                  dsimp only [vals, Arg.val]
                                  refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
                                  have hnb := fullArenaNextOff_bounds (ar := sp.core.arena)
                                    (alen := sp.core.arena_len) (cref := p.toNat) hwf_p.1
                                  have hnp_mem :=
                                    FullDenseWatchHelpers.fullArenaClauseRefs_next_mem
                                      hdwp.2.1.arena hp_ref
                                  let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena
                                    sp.core.arena_len (p.setWidth 32).toNat)).setWidth 64
                                  have hnp_toNat : np.toNat =
                                      fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
                                    dsimp only [np]; rw [hp32, m6_zext32_toNat, BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt (by omega)]
                                  c0_hsteps_nogrp
                                  refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                      FullDenseInvW c F0 F_cur sj ∧
                                      sj.core.cur_vars = s0.core.cur_vars ∧
                                      sj.core.arena_len = sl.core.arena_len ∧
                                      sj.core.fuel = s0.core.fuel ∧
                                      fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                      (FullMem c sj ⋆ R) mj)
                                    (fun _ mj ⟨sj, hdwj, hcvj, halj, hflj, hrefsj, hmj⟩ => by
                                      c0_hsteps!
                                      exact hLp (sj.core.arena_len - np.toNat) (np, ()) mj
                                        (by omega) ⟨sj, by omega, rfl, by
                                          rw [hnp_toNat, halj, ← halp, hrefsj]; exact hnp_mem,
                                         hdwj, hcvj, halj, hflj, hmj⟩)
                                    (fun Jp hJp => by
                                      c0_hsplit
                                      · c0_hsteps_nogrp
                                        let v' := hdr_p &&& ~~~0x01000000#32
                                        let sc : FullState :=
                                          { sp with core := { sp.core with
                                            arena := sp.core.arena.set p.toNat v' } }
                                        have hhdr_eq : hdr_p = fullArenaHdr sp p.toNat := by
                                          unfold hdr_p fullArenaHdr fullArenaHdrCore
                                          rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                                        have hcb := m6_bit24_clear_pres hdr_p
                                        have hset := m6_fullDenseInvW_set_hdr_bit24 hdwp hp_ref
                                          (v' := v') (by rw [← hhdr_eq]; exact hcb.1)
                                          (by rw [← hhdr_eq]; exact hcb.2)
                                        refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                            FullDenseInvW c F0 F_cur sj ∧
                                            sj.core.cur_vars = s0.core.cur_vars ∧
                                            sj.core.arena_len = sl.core.arena_len ∧
                                            sj.core.fuel = s0.core.fuel ∧
                                            fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                            (FullMem c sj ⋆ R) mj)
                                          (fun _ mj hmj => hJp mj hmj)
                                          (fun J52 hJ52 => by
                                            c0_hsplit
                                            · c0_hsteps_nogrp
                                              refine wp_loop_group (ts := [i32])
                                                (fun rem_k (k, ()) mk =>
                                                  ∃ fl_k : List (BitVec 32),
                                                    let sk : FullState :=
                                                      { sc with core := { sc.core with
                                                        flags := fl_k } }
                                                    fl_k.length = c.max_vars ∧
                                                    k.toNat ≤ sz_p.toNat ∧
                                                    rem_k = sz_p.toNat - k.toNat ∧
                                                    (FullMem c sk ⋆ R) mk)
                                                ?_ ?_
                                              · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk
                                                  ⟨fl_k, hflk, hk_le, rfl, hmk⟩
                                                c0_hsplit
                                                · have hk_lt : k.toNat < sz_p.toNat := hc
                                                  have hpi_ar : (p + 3#64 + k.setWidth 64).toNat <
                                                      sc.core.arena.length := by
                                                    rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                                                    c0_bound
                                                  c0_hsteps_nogrp
                                                  refine wp_join0 (P := fun mj => ∃ fl' : List
                                                      (BitVec 32),
                                                      fl'.length = c.max_vars ∧
                                                      (FullMem c { sc with core := { sc.core with
                                                        flags := fl' } } ⋆ R) mj)
                                                    (fun _ mj ⟨fl', hfl', hmj⟩ => by
                                                      c0_hsteps!
                                                      exact hLk (sz_p.toNat - (k + 1#32).toNat)
                                                        (k + 1#32, ()) mj (by omega)
                                                        ⟨fl', hfl', by omega, rfl, hmj⟩)
                                                    (fun J65 hJ65 => by
                                                      c0_hsplit
                                                      · have hlv_lt : ((sc.core.arena[(p + 3#64 +
                                                            k.setWidth 64).toNat]'hpi_ar >>>
                                                            (1 : Nat)).setWidth 64).toNat <
                                                            fl_k.length := by
                                                          have hpi_mod : (p + 3#64 +
                                                              k.setWidth 64).toNat =
                                                              (p.toNat + BitVec.toNat (3#64) +
                                                                k.toNat) % 2 ^ 64 := by
                                                            rw [BitVec.toNat_add, BitVec.toNat_add,
                                                              m6_zext32_toNat]
                                                            simp only [BitVec.toNat_ofNat]
                                                            c0_bound
                                                          have har_eq : sc.core.arena[(p.toNat +
                                                              BitVec.toNat (3#64) +
                                                              k.toNat) % 2 ^ 64]'(by
                                                                rw [hset.1.1.core_ok.arena_len_arr]
                                                                c0_bound) =
                                                              sc.core.arena[(p + 3#64 +
                                                                k.setWidth 64).toNat]'hpi_ar :=
                                                            m6_getElem_congr hpi_mod.symm _ _
                                                          have hcv_mod : sl.core.cur_vars % 2 ^ 64 =
                                                              sl.core.cur_vars :=
                                                            Nat.mod_eq_of_lt (by
                                                              rw [hcvl]; have :=
                                                                hset.1.1.core_ok.cur_vars_le
                                                              omega)
                                                          rw [hcv_mod] at hc
                                                          have hdiv_lt : (sc.core.arena[(p + 3#64 +
                                                              k.setWidth 64).toNat]'hpi_ar).toNat /
                                                              2 < sl.core.cur_vars := by
                                                            simpa [har_eq] using hc
                                                          have hsh1 :
                                                              ((sc.core.arena[(p + 3#64 +
                                                                    k.setWidth 64).toNat]'hpi_ar
                                                                  >>> (1 : Nat)) :
                                                                BitVec 32).toNat =
                                                              (sc.core.arena[(p + 3#64 +
                                                                  k.setWidth 64).toNat]'
                                                                  hpi_ar).toNat / 2 := by
                                                            rw [BitVec.toNat_ushiftRight,
                                                              Nat.shiftRight_eq_div_pow]
                                                          rw [hflk, m6_zext32_toNat, hsh1]
                                                          have := hset.1.1.core_ok.cur_vars_le
                                                          omega
                                                        c0_hsteps!
                                                        exact hJ65 _ ⟨_, by simp [hflk], hm⟩
                                                      · c0_hsteps!; exact hJ65 mk ⟨fl_k, hflk, hmk⟩)
                                                · c0_hsteps!
                                                  exact hJ52 mk ⟨{ sc with core := { sc.core with
                                                    flags := fl_k } },
                                                    m6_fullDenseInvW_with_flags hset.1 hflk,
                                                    hcvp, halp, hflp, hset.2.1, hmk⟩
                                              · intro Lk hLk; c0_hsteps!
                                                exact hLk sz_p.toNat (0#32, ()) m
                                                  ⟨sc.core.flags, hset.1.1.core_ok.flags_len,
                                                   Nat.zero_le _, by simp, hm⟩
                                            · refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                                  FullDenseInvW c F0 F_cur sj ∧
                                                  sj.core.cur_vars = s0.core.cur_vars ∧
                                                  sj.core.arena_len = sl.core.arena_len ∧
                                                  sj.core.fuel = s0.core.fuel ∧
                                                  fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                                  (FullMem c sj ⋆ R) mj)
                                                (fun _ mj hmj => hJ52 mj hmj)
                                                (fun J55p hJ55p => by
                                                  c0_hsplit
                                                  · have hsz2 : 2 ≤ sz_p.toNat := hc
                                                    have hp3_ar : (p + 3#64).toNat <
                                                        sc.core.arena.length := by
                                                      rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                    have hp4_ar : (p + 4#64).toNat <
                                                        sc.core.arena.length := by
                                                      rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                    c0_hsteps_nogrp
                                                    refine wp_join_state (ts := [])
                                                      (α := List (BitVec 32)) (fun _ => ())
                                                      (fun fl1 m1 => fl1.length = c.max_vars ∧
                                                        (FullMem c { sc with core := { sc.core with
                                                          flags := fl1 } } ⋆ R) m1)
                                                      (fun _ fl1 m1 ⟨hfl1, hm1⟩ => by
                                                        c0_hsteps_nogrp
                                                        refine wp_join_state (ts := [])
                                                          (α := List (BitVec 32)) (fun _ => ())
                                                          (fun fl2 m2 => fl2.length = c.max_vars ∧
                                                            (FullMem c { sc with core :=
                                                              { sc.core with flags := fl2 } } ⋆ R)
                                                              m2)
                                                          (fun _ fl2 m2 ⟨hfl2, hm2⟩ => by
                                                            c0_hsteps!
                                                            let s_fl2 : FullState :=
                                                              { sc with core := { sc.core with
                                                                flags := fl2 } }
                                                            have hdw_fl2 :
                                                                FullDenseInvW c F0 F_cur s_fl2 :=
                                                              m6_fullDenseInvW_with_flags hset.1
                                                                hfl2
                                                            exact hJ55p m2 ⟨s_fl2, hdw_fl2,
                                                              hcvp, halp, hflp, hset.2.1, hm2⟩)
                                                          (fun J68 hJ68 => by
                                                            c0_hsplit
                                                            · have hv1_lt :
                                                                  ((sc.core.arena[(p +
                                                                    4#64).toNat]'hp4_ar >>>
                                                                    (1 : Nat)).setWidth 64).toNat <
                                                                    fl1.length := by
                                                                have hp4_mod : (p + 4#64).toNat =
                                                                    (p.toNat + BitVec.toNat 4#64) %
                                                                      2 ^ 64 := BitVec.toNat_add _ _
                                                                have hsp_len :
                                                                    sp.core.arena.length =
                                                                      c.arena_cap := by
                                                                  have h0 :=
                                                                    hset.1.1.core_ok.arena_len_arr
                                                                  simpa [sc] using h0
                                                                have hcv_mod : sl.core.cur_vars %
                                                                    2 ^ 64 = sl.core.cur_vars :=
                                                                  Nat.mod_eq_of_lt (by
                                                                    rw [hcvl]; have :=
                                                                      hset.1.1.core_ok.cur_vars_le
                                                                    omega)
                                                                rw [hcv_mod] at hc
                                                                have hne4 : p.toNat ≠
                                                                    (p.toNat + BitVec.toNat 4#64) %
                                                                      2 ^ 64 := by
                                                                  rw [← hp4_mod]; c0_bound
                                                                have hset_ne1 :
                                                                    (sp.core.arena.set p.toNat
                                                                      (sp.core.arena[p.toNat]'(by
                                                                        rw [hsp_len]; c0_bound) &&&
                                                                        ~~~(16777216 : BitVec 32)))[
                                                                        (p.toNat +
                                                                        BitVec.toNat 4#64) %
                                                                        2 ^ 64]'(by
                                                                          rw [List.length_set,
                                                                            hsp_len]
                                                                          c0_bound) =
                                                                      sp.core.arena[(p +
                                                                        4#64).toNat]'(by
                                                                          rw [hsp_len]; c0_bound) :=
                                                                  (List.getElem_set_ne hne4
                                                                    _).trans (m6_getElem_congr
                                                                      hp4_mod.symm _ _)
                                                                have hset_ne2 :
                                                                    sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar =
                                                                      sp.core.arena[(p +
                                                                        4#64).toNat]'(by
                                                                          rw [hsp_len]; c0_bound) :=
                                                                  by
                                                                  dsimp only [sc]
                                                                  exact List.getElem_set_ne
                                                                    (by c0_bound) _
                                                                have hdiv_lt : (sc.core.arena[(p +
                                                                    4#64).toNat]'hp4_ar).toNat / 2
                                                                    < sl.core.cur_vars := by
                                                                  have hc' :
                                                                      ((sp.core.arena.set p.toNat
                                                                        (sp.core.arena[p.toNat]'(by
                                                                          rw [hsp_len]; c0_bound)
                                                                          &&& ~~~(16777216 :
                                                                            BitVec 32)))[(p.toNat +
                                                                          BitVec.toNat 4#64) %
                                                                          2 ^ 64]'(by
                                                                            rw [List.length_set,
                                                                              hsp_len]
                                                                            c0_bound)).toNat / 2 <
                                                                        sl.core.cur_vars := hc
                                                                  rw [hset_ne1] at hc'
                                                                  rw [hset_ne2]; exact hc'
                                                                have hsh1 : ((sc.core.arena[(p +
                                                                    4#64).toNat]'hp4_ar >>>
                                                                    (1 : Nat)) : BitVec 32).toNat =
                                                                    (sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar).toNat /
                                                                      2 := by
                                                                  rw [BitVec.toNat_ushiftRight,
                                                                    Nat.shiftRight_eq_div_pow]
                                                                rw [hfl1, m6_zext32_toNat, hsh1]
                                                                have :=
                                                                  hset.1.1.core_ok.cur_vars_le
                                                                omega
                                                              c0_hsteps!
                                                              exact hJ68 _ _ ⟨by simp [hfl1], hm⟩
                                                            · c0_hsteps!
                                                              exact hJ68 fl1 m1 ⟨hfl1, hm1⟩))
                                                      (fun J67 hJ67 => by
                                                        c0_hsplit
                                                        · have hv0_lt :
                                                              ((sc.core.arena[(p + 3#64).toNat]'
                                                                hp3_ar >>> (1 : Nat)).setWidth
                                                                64).toNat < sc.core.flags.length :=
                                                            by
                                                              have hp3_mod : (p + 3#64).toNat =
                                                                  (p.toNat + BitVec.toNat 3#64) %
                                                                    2 ^ 64 := BitVec.toNat_add _ _
                                                              have hsp_len :
                                                                  sp.core.arena.length =
                                                                    c.arena_cap := by
                                                                have h0 :=
                                                                  hset.1.1.core_ok.arena_len_arr
                                                                simpa [sc] using h0
                                                              have hcv_mod : sl.core.cur_vars %
                                                                  2 ^ 64 = sl.core.cur_vars :=
                                                                Nat.mod_eq_of_lt (by
                                                                  rw [hcvl]; have :=
                                                                    hset.1.1.core_ok.cur_vars_le
                                                                  omega)
                                                              rw [hcv_mod] at hc
                                                              have hne3 : p.toNat ≠
                                                                  (p.toNat + BitVec.toNat 3#64) %
                                                                    2 ^ 64 := by
                                                                rw [← hp3_mod]; c0_bound
                                                              have hset_ne1 :
                                                                  (sp.core.arena.set p.toNat
                                                                    (sp.core.arena[p.toNat]'(by
                                                                      rw [hsp_len]; c0_bound) &&&
                                                                      ~~~(16777216 : BitVec 32)))[
                                                                      (p.toNat +
                                                                      BitVec.toNat 3#64) %
                                                                      2 ^ 64]'(by
                                                                        rw [List.length_set,
                                                                          hsp_len]
                                                                        c0_bound) =
                                                                    sp.core.arena[(p +
                                                                      3#64).toNat]'(by
                                                                        rw [hsp_len]; c0_bound) :=
                                                                (List.getElem_set_ne hne3 _).trans
                                                                  (m6_getElem_congr hp3_mod.symm _
                                                                    _)
                                                              have hset_ne2 :
                                                                  sc.core.arena[(p +
                                                                    3#64).toNat]'hp3_ar =
                                                                    sp.core.arena[(p +
                                                                      3#64).toNat]'(by
                                                                        rw [hsp_len]; c0_bound) :=
                                                                by
                                                                dsimp only [sc]
                                                                exact List.getElem_set_ne
                                                                  (by c0_bound) _
                                                              have hdiv_lt : (sc.core.arena[(p +
                                                                  3#64).toNat]'hp3_ar).toNat / 2 <
                                                                  sl.core.cur_vars := by
                                                                have hc' :
                                                                    ((sp.core.arena.set p.toNat
                                                                      (sp.core.arena[p.toNat]'(by
                                                                        rw [hsp_len]; c0_bound) &&&
                                                                        ~~~(16777216 : BitVec 32)))[
                                                                        (p.toNat +
                                                                        BitVec.toNat 3#64) %
                                                                        2 ^ 64]'(by
                                                                          rw [List.length_set,
                                                                            hsp_len]
                                                                          c0_bound)).toNat / 2 <
                                                                      sl.core.cur_vars := hc
                                                                rw [hset_ne1] at hc'
                                                                rw [hset_ne2]; exact hc'
                                                              have hsh1 : ((sc.core.arena[(p +
                                                                  3#64).toNat]'hp3_ar >>>
                                                                  (1 : Nat)) : BitVec 32).toNat =
                                                                  (sc.core.arena[(p +
                                                                    3#64).toNat]'hp3_ar).toNat /
                                                                    2 := by
                                                                rw [BitVec.toNat_ushiftRight,
                                                                  Nat.shiftRight_eq_div_pow]
                                                              rw [hset.1.1.core_ok.flags_len,
                                                                m6_zext32_toNat, hsh1]
                                                              have := hset.1.1.core_ok.cur_vars_le
                                                              omega
                                                          c0_hsteps!
                                                          exact hJ67 _ _
                                                            ⟨by simp [hset.1.1.core_ok.flags_len],
                                                             hm⟩
                                                        · c0_hsteps!
                                                          exact hJ67 sc.core.flags m
                                                            ⟨hset.1.1.core_ok.flags_len, hm⟩)
                                                  · c0_hsteps!
                                                    exact hJ55p m ⟨sc, hset.1, hcvp, halp, hflp,
                                                      hset.2.1, hm⟩))
                                      · c0_hsteps!
                                        exact hJp mp ⟨sp, hdwp, hcvp, halp, hflp, rfl, hmp⟩)
                                · c0_hsteps!; exact hJc sp mp ⟨hdwp, hcvp, hflp, hmp⟩
                              · intro Lp hLp; c0_hsteps!
                                exact hLp sv0.core.arena_len (0#64, ()) mv
                                  ⟨sv0, Nat.zero_le _, by simp, by
                                    by_cases hz : sv0.core.arena_len = 0
                                    · exact Or.inl hz.symm
                                    · exact Or.inr (s12b_zero_mem_arenaRefs hdw_v0.2.1.arena
                                        (Nat.pos_of_ne_zero hz)),
                                   hdw_v0, hcvl, rfl, hfll, hmv⟩
                          · intro Lv hLv; c0_hsteps!
                            exact hLv sl.core.cur_vars (0#64, ()) ml
                              ⟨sl.core.flags, hdwl.1.core_ok.flags_len, Nat.zero_le _, by simp, hml⟩
                        · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩
                      · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩
                    · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩))
              (fun B hB => by
                c0_hsplit
                · have hi_lt : i.toNat < ncand.toNat := hc
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsplit
                      · have hi_rr : i.toNat < sl.scratch.red_refs.length := by
                          rw [hdwl.1.scratch_ok.red_refs_len]; omega
                        have hcr_ref : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                            fullArenaClauseRefs sl := by
                          rw [hrefsl]
                          have h0 := hrr4_ok i.toNat hi_lt
                          rw [← hrrl, List.getElem?_eq_getElem hi_rr, Option.getD_some] at h0
                          exact h0
                        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        s12b_call hCheckCl
                        refine fullFwdCheckClM7Spec_intro rfl hdwl hcr_ref hml ?_
                        intro ok_c sc mc hdwc hcvc _ hflc hrefsc _ hrrc hfc hmc
                        c0_hsplit
                        · have hcr_ref_c : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                              fullArenaClauseRefs sc := hrefsc.symm ▸ hcr_ref
                          refine wp_join0 (P := fun mj => ∃ sj : FullState,
                              FullDenseInvW c F0 F_cur sj ∧
                              sj.core.cur_vars = s0.core.cur_vars ∧ sj.core.fuel = s0.core.fuel ∧
                              fullArenaClauseRefs sj = fullArenaClauseRefs s4 ∧
                              sj.scratch.red_refs = s4.scratch.red_refs ∧
                              (FullMem c sj ⋆ R) mj)
                            (fun _ mj ⟨sj, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩ => by
                              c0_hsteps!
                              exact hL (ncand.toNat - (i + 1#64).toNat)
                                (i + 1#64, rem - 1#64, ()) mj (by omega)
                                ⟨sj, by omega, rfl, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩)
                            (fun Jcon hJcon => by
                              c0_hsplit
                              · c0_hsplit
                                · have hcr_ar :
                                      ((sl.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
                                        sc.core.arena.length := by
                                    have hwf_c := hdwc.2.1.arena.refs_wf _ hcr_ref_c
                                    have := hdwc.1.core_ok.arena_len_le
                                    rw [hdwc.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
                                  c0_hsplit
                                  · c0_hsteps_nogrp
                                    s12b_call hConnectSub
                                    refine fullFwdConnectSubsumerM6Spec_intro rfl hdwc hcr_ref_c
                                      hmc ?_
                                    intro s_con m_con hdw_con hcv_con har_con hal_con hfl_con _ _
                                      hrr_con hm_con
                                    have hrefs_con : fullArenaClauseRefs s_con =
                                        fullArenaClauseRefs sc := by
                                      unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                      rw [har_con, hal_con]
                                    c0_hsteps!
                                    exact hJcon m_con ⟨s_con, hdw_con,
                                      hcv_con.trans (hcvc.trans hcvl),
                                      hfl_con.trans (hflc.trans hfll),
                                      hrefs_con.trans (hrefsc.trans hrefsl),
                                      hrr_con.trans (hrrc.trans hrrl), hm_con⟩
                                  · c0_hsteps!
                                    exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                      hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                                · c0_hsteps!
                                  exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                    hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                              · c0_hsteps!
                                exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                  hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩)
                        · c0_hsteps!
                          exact hQ 20#64 sc mc hdwc.toDense (hcvc.trans hcvl) (hflc.trans hfll)
                            (Or.inr rfl) (fun _ => hfc (by simpa using hc)) hmc
                      · c0_hsteps!; exact hB ml rfl
                    · c0_hsteps!; exact hB ml rfl
                  · c0_hsteps!; exact hB ml rfl
                · c0_hsteps!; exact hB ml rfl)
          · intro L hL; c0_hsteps!
            exact hL ncand.toNat (0#64, budget, ()) m4
              ⟨s4, Nat.zero_le _, by simp, hdw4,
               hcv4.trans (hcv3.trans (hcv2.trans hcv1)),
               hfl4.trans (hfl3.trans (hfl2.trans hfl1)), rfl, rfl, hm4⟩
      · c0_hsteps!
        exact hQ 20#64 s2 m2 hdw2.toDense (hcv2.trans hcv1) (hfl2.trans hfl1) (Or.inr rfl)
          (fun _ => hf2 (by simpa using hc)) hm2
    · c0_hsteps!
      exact hQ 20#64 s1 m1 hdw1.toDense hcv1 hfl1 (Or.inr rfl)
        (fun _ => hf1 (by simpa using hc)) hm1

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B
