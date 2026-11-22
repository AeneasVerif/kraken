module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof0
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullTransLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Wave-2 PR-W2C (`RC-21`) — Multi-Level Backbone Parity Proofs (`Proof4a`)
Certifies UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for all `7` `RC-21`
multi-level backbone functions in `FullM6VivBackbone.lean`:
1. `full_backbone_sched_m6_wp` (`fullBackboneSchedM6Spec`)
2. `full_backbone_keep_m6_wp` (`fullBackboneKeepM6Spec`)
3. `full_backbone_unwind_m6_wp` (`fullBackboneUnwindM6Spec`)
4. `full_backbone_prop_m6_wp` (`fullBackbonePropM6Spec`)
5. `full_backbone_analyze_m6_wp` (`fullBackboneAnalyzeM6Spec`, 2-literal 1UIP resolution)
6. `full_backbone_round_m6_wp` (`fullBackboneRoundM6Spec`)
7. `full_backbone_m6_wp` certifying exact canonical **`FullM3Backbone.fullBackboneSpec`**
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. Multi-Level Backbone Trail Invariant & Cross-File Specs -/

section Specs

/-- Multi-level backbone sweep invariant tracking an upper bound `max_lvl` on all trail levels
(allowing temporary `cur_level = 0` level-0 unit propagation while `max_lvl = old_lvl > 0`). -/
structure BbTrailInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st : FullState) (saved0 max_lvl : Nat) : Prop where
  len_ok : st.LengthsOk c
  s0_l0 : s0.core.cur_level = 0
  same_core : st.core =
    { s0.core with
      vals := st.core.vals, lvl := st.core.lvl, rsns := st.core.rsns,
      trl := st.core.trl, trail_end := st.core.trail_end, cur_level := st.core.cur_level,
      confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1 }
  same_scratch : st.scratch =
    { s0.scratch with
      ant_sz := st.scratch.ant_sz, res_sz := st.scratch.res_sz,
      work_stk1 := st.scratch.work_stk1, work_stk2 := st.scratch.work_stk2 }
  saved0_eq : saved0 = s0.core.trail_end
  saved0_le : saved0 ≤ st.core.trail_end
  cur_le_max : st.core.cur_level ≤ max_lvl
  trl_prefix : ∀ i < saved0, st.core.trl[i]? = s0.core.trl[i]?
  vals_prefix : ∀ l < 2 * s0.core.cur_vars,
    s0.core.vals[l]?.getD 0#8 ≠ 0#8 → st.core.vals[l]?.getD 0#8 = s0.core.vals[l]?.getD 0#8
  vals_hi : ∀ l, 2 * s0.core.cur_vars ≤ l → st.core.vals[l]? = s0.core.vals[l]?
  lvl_prefix : ∀ i < saved0,
    let v := (s0.core.trl[i]?.getD 0#32).toNat / 2
    st.core.lvl[v]? = s0.core.lvl[v]? ∧ st.core.rsns[v]? = s0.core.rsns[v]?
  trl_lits_lt : ∀ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars
  trl_vars_nodup : ∀ i j, i < st.core.trail_end → j < st.core.trail_end →
    (st.core.trl[i]?.getD 0#32).toNat / 2 = (st.core.trl[j]?.getD 0#32).toNat / 2 → i = j
  trl_vals_ok : ∀ i < st.core.trail_end,
    let l := (st.core.trl[i]?.getD 0#32).toNat
    st.core.vals[l]?.getD 0#8 = 1#8 ∧ st.core.vals[l ^^^ 1]?.getD 0#8 = 0xFF#8
  vals_dom : ∀ l < 2 * s0.core.cur_vars,
    st.core.vals[l]?.getD 0#8 = 0#8 ∨ st.core.vals[l]?.getD 0#8 = 1#8 ∨
    st.core.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_trl : ∀ l < 2 * s0.core.cur_vars,
    st.core.vals[l]?.getD 0#8 = 1#8 →
    ∃ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat = l
  vals_false_trl : ∀ l < 2 * s0.core.cur_vars,
    st.core.vals[l]?.getD 0#8 = 0xFF#8 →
    ∃ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le_max : ∀ i < st.core.trail_end,
    (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl
  l0_entails : ∀ i < st.core.trail_end,
    (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(st.core.trl[i]?.getD 0#32).toNat])

/-- `full_backbone_sched_m6(h)`: collects candidate literals into `work_stk1[0 ..< cand_n)` (with
full-sweep `FL_BONE0 | FL_BONE1` re-arming when empty). -/
@[expose] def fullBackboneSchedM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ cand_n fl' ws1' m',
      let s' : FullState :=
        { s with core := { s.core with flags := fl' }
                 scratch := { s.scratch with work_stk1 := ws1' } }
      FullSparseInvW c F0 F_cur s' → cand_n.toNat ≤ 2 * s.core.cur_vars →
      (∀ i < cand_n.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (cand_n, ()) m'

/-- `full_backbone_keep_m6(h, cand_n)`: updates persistent `FL_BONE0`/`FL_BONE1` flags from the
remaining candidate slice `work_stk1[0 ..< cand_n)`. -/
@[expose] def fullBackboneKeepM6Spec : Spec [i64, i64] [] := fun (h, cand_n, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cand_n.toNat ≤ 2 * s.core.cur_vars ∧
    (∀ i < cand_n.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ fl' m',
      let s' : FullState := { s with core := { s.core with flags := fl' } }
      FullSparseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_backbone_unwind_m6(h, saved, target_lvl)`: pops trail entries back to `saved`, clears
their `vals`, and sets `cur_level := target_lvl`, preserving `BbTrailInv`. -/
@[expose] def fullBackboneUnwindM6Spec : Spec [i64, i64, i64] [] :=
  fun (h, saved, target_lvl, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 st : FullState)
      (saved0 max_lvl : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ BbTrailInv c F0 F_cur s0 st saved0 max_lvl ∧
      saved0 ≤ saved.toNat ∧ saved.toNat ≤ st.core.trail_end ∧ target_lvl.toNat ≤ c.max_vars ∧
      (∀ i < saved.toNat,
        (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          target_lvl.toNat) ∧
      (FullMem c st ⋆ R) m ∧
      ∀ vals' m',
        let st' : FullState :=
          { st with core := { st.core with
            vals := vals', trail_end := saved.toNat, cur_level := target_lvl.toNat } }
        BbTrailInv c F0 F_cur s0 st' saved0 target_lvl.toNat → (FullMem c st' ⋆ R) m' → Q () m'

/-- `full_backbone_prop_m6(h, prop_start, stop_early)`: binary-only propagation under either
level-0 unit mode (`cur_level = 0`) or probe-level 1UIP mode (`BackboneProbeSeg`). -/
@[expose] def fullBackbonePropM6Spec : Spec [i64, i64, .bool] [.bool] :=
  fun (h, prop_start, _stop_early, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 st : FullState)
      (saved0 max_lvl : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ BbTrailInv c F0 F_cur s0 st saved0 max_lvl ∧
      saved0 ≤ prop_start.toNat ∧ prop_start.toNat ≤ st.core.trail_end ∧
      ((st.core.cur_level = 0 ∧
        ∀ i, prop_start.toNat ≤ i → i < st.core.trail_end →
          (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0) ∨
       (0 < st.core.cur_level ∧
        ∃ saved, saved0 ≤ saved ∧ saved ≤ prop_start.toNat ∧
          BackboneProbeSeg F_cur st saved st.core.cur_level)) ∧
      (FullMem c st ⋆ R) m ∧
      ∀ (ok : Bool) vals' lvl' rsns' trl' te' c0' c1' asz' m',
        let st' : FullState :=
          { st with
            core := { st.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_end := te',
              confl_lit0 := c0', confl_lit1 := c1' }
            scratch := { st.scratch with ant_sz := asz' } }
        BbTrailInv c F0 F_cur s0 st' saved0 max_lvl →
        st.core.trail_end ≤ te' →
        (∀ i < st.core.trail_end, trl'[i]? = st.core.trl[i]?) →
        (∀ i < st.core.trail_end,
          let v := (st.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]? = st.core.lvl[v]? ∧ rsns'[v]? = st.core.rsns[v]?) →
        (∀ saved, saved0 ≤ saved → saved ≤ prop_start.toNat → 0 < st.core.cur_level →
          BackboneProbeSeg F_cur st saved st.core.cur_level →
          BackboneProbeSeg F_cur st' saved st.core.cur_level) →
        (ok = false →
          c0'.toNat < 2 * s0.core.cur_vars ∧ c1'.toNat < 2 * s0.core.cur_vars ∧
          vals'[c0'.toNat]?.getD 0#8 = 0xFF#8 ∧ vals'[c1'.toNat]?.getD 0#8 = 0xFF#8 ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [c0'.toNat, c1'.toNat]) ∧
          ∃ idx0, prop_start.toNat ≤ idx0 ∧ idx0 < te' ∧
            (trl'[idx0]?.getD 0#32).toNat = c0'.toNat ^^^ 1) →
        (FullMem c st' ⋆ R) m' → Q (ok, ()) m'

/-- `full_backbone_analyze_m6(h, c0, c1, saved)`: 2-literal 1UIP binary-reason resolution certifying
`uip ≠ 0xFFFFFFFF#32 → uip < 2*cur_vars ∧ F_cur ⊨ [uip ^^^ 1]` and restoring `mrk = 0`. -/
@[expose] def fullBackboneAnalyzeM6Spec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, c0, c1, saved, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 st : FullState)
      (saved0 max_lvl : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ BbTrailInv c F0 F_cur s0 st saved0 max_lvl ∧
      0 < st.core.cur_level ∧ saved0 ≤ saved.toNat ∧
      (∀ i < saved.toNat,
        (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
          st.core.cur_level) ∧
      BackboneProbeSeg F_cur st saved.toNat st.core.cur_level ∧
      c0.toNat < 2 * s0.core.cur_vars ∧ c1.toNat < 2 * s0.core.cur_vars ∧
      st.core.vals[c0.toNat]?.getD 0#8 = 0xFF#8 ∧ st.core.vals[c1.toNat]?.getD 0#8 = 0xFF#8 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [c0.toNat, c1.toNat]) ∧
      (∃ idx0, saved.toNat ≤ idx0 ∧ idx0 < st.core.trail_end ∧
        (st.core.trl[idx0]?.getD 0#32).toNat = c0.toNat ^^^ 1) ∧
      (FullMem c st ⋆ R) m ∧
      ∀ uip mrk' m',
        let st' : FullState := { st with core := { st.core with mrk := mrk' } }
        mrk'.length = c.max_vars → FullMrkZero c st' →
        (uip ≠ 0xFFFFFFFF#32 →
          uip.toNat < 2 * s0.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat ^^^ 1])) →
        (FullMem c st' ⋆ R) m' → Q (uip, ()) m'

/-- `full_backbone_round_m6(h, cand_n, stop_early)`: one multi-level backbone sweep restoring
`FullSparseInvW` at level 0 and certifying every discovered unit in `work_stk2[0 ..< res_sz)`. -/
@[expose] def fullBackboneRoundM6Spec : Spec [i64, i64, .bool] [i64] :=
  fun (h, cand_n, _stop_early, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
      cand_n.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ i < cand_n.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ keep s' m',
        FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        keep.toNat ≤ 2 * s.core.cur_vars →
        (∀ i < keep.toNat, (s'.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
        s'.scratch.res_sz.toNat ≤ 2 * s.core.cur_vars →
        (∀ i < s'.scratch.res_sz.toNat,
          (s'.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(s'.scratch.work_stk2[i]?.getD 0#32).toNat])) →
        (FullMem c s' ⋆ R) m' → Q (keep, ()) m'

end Specs

/-! ## 2. Pure `BbTrailInv` & Resolution Helpers -/

section BbHelpers
private theorem bb_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> 1).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
private theorem bb_bv32_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]
private theorem bb_bv8_zext32_eq0 : ∀ x : BitVec 8, x.setWidth 32 = 0#32 ↔ x = 0#8 := by decide
private theorem bb_bv8_dom_slt0 {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide
private theorem bb_bv8_dom_sgt0 {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#32).slt (x.signExtend 32) = true ↔ x = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> decide
private theorem bb_bv8_sext32_eq0 : ∀ x : BitVec 8, x.signExtend 32 = 0#32 ↔ x = 0#8 := by decide
private theorem bb_getD_set2_ne {α : Type} {xs : List α} {a b i : Nat} {x y d : α}
    (ha : i ≠ a) (hb : i ≠ b) : ((xs.set a x).set b y)[i]?.getD d = xs[i]?.getD d := by
  rw [List.getElem?_set_ne hb.symm, List.getElem?_set_ne ha.symm]
private theorem bb_var_ne_xor {x y : Nat} (h : x / 2 ≠ y / 2) :
    x ≠ y ∧ x ≠ y ^^^ 1 ∧ x ^^^ 1 ≠ y ∧ x ^^^ 1 ≠ y ^^^ 1 :=
  ⟨fun e => h (by rw [e]), fun e => h (by rw [e, fullInv_var_xor1]),
   fun e => h (by rw [← e, fullInv_var_xor1]),
   fun e => h (by have := congrArg (· / 2) e; simpa only [fullInv_var_xor1] using this)⟩
private theorem bb_entails_comm2 {F : CNF Nat} {a b : Nat}
    (h : F.EntailsClause (cnfClause [a, b])) : F.EntailsClause (cnfClause [b, a]) := by
  rw [CNF.entails_clause_def] at h ⊢; intro α hα
  obtain ⟨l, hm, hs⟩ := (clause_sat_cnfClause_iff α _).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  exact (clause_sat_cnfClause_iff α _).mpr ⟨l, by simp [hm.symm], hs⟩
private theorem BbTrailInv.init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hsp : FullSparseInvW c F0 F_cur s0) (hl0 : s0.core.cur_level = 0) :
    BbTrailInv c F0 F_cur s0 s0 s0.core.trail_end 0 := by
  have hw := hsp.2.1
  exact
    { len_ok := hsp.1, s0_l0 := hl0, same_core := rfl, same_scratch := rfl,
      saved0_eq := rfl, saved0_le := Nat.le_refl _, cur_le_max := by omega,
      trl_prefix := fun _ _ => rfl, vals_prefix := fun _ _ _ => rfl,
      vals_hi := fun _ _ => rfl, lvl_prefix := fun _ _ => ⟨rfl, rfl⟩,
      trl_lits_lt := hw.trail_lits_lt, trl_vars_nodup := hw.trail_vars_nodup,
      trl_vals_ok := fun i hi => by
        have hlt := hw.trail_lits_lt i hi
        exact ⟨(hw.vals_true_iff _ hlt).mpr ⟨i, hi, rfl⟩,
          (hw.vals_false_iff _ (litNeg_lt_two_mul hlt)).mpr
            ⟨i, hi, (litNeg_litNeg _).symm⟩⟩,
      vals_dom := hw.vals_domain,
      vals_true_trl := fun l hl h1 => (hw.vals_true_iff l hl).mp h1,
      vals_false_trl := fun l hl hff => (hw.vals_false_iff l hl).mp hff,
      lvl_le_max := fun i hi => by have := hw.lvl_le i hi; omega,
      l0_entails := hw.level0_sound }
private theorem BbTrailInv.to_fullSparseInvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 : Nat} (hsp0 : FullSparseInvW c F0 F_cur s0)
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 0)
    (hte : st.core.trail_end = saved0) (hcl0 : st.core.cur_level = 0) :
    FullSparseInvW c F0 F_cur st := by
  have hbt0 : BackboneTrailInv c F0 F_cur s0 st saved0 :=
    ⟨hbt.len_ok, hbt.s0_l0, hbt.same_core, hbt.same_scratch, hbt.saved0_eq, hbt.saved0_le,
     hbt.trl_prefix, hbt.vals_prefix, hbt.vals_hi, hbt.lvl_prefix, hbt.trl_lits_lt,
     hbt.trl_vars_nodup, hbt.trl_vals_ok, hbt.vals_dom, hbt.vals_true_trl, hbt.vals_false_trl,
     fun i hi => by have := hbt.lvl_le_max i hi; omega, hbt.l0_entails⟩
  have hw' := hbt0.to_fullWitnessInv hsp0.2.1 hte hcl0
  have hmrk_eq : st.core.mrk = s0.core.mrk := by rw [hbt.same_core]
  have hlm_eq : st.core.lit_mark = s0.core.lit_mark := by rw [hbt.same_core]
  have har_eq : st.core.arena = s0.core.arena := by rw [hbt.same_core]
  have hal_eq : st.core.arena_len = s0.core.arena_len := by rw [hbt.same_core]
  have hdm_eq : st.core.dense_mode = s0.core.dense_mode := by rw [hbt.same_core]
  have hll_eq : st.scratch.last_learned = s0.scratch.last_learned := by rw [hbt.same_scratch]
  have hex_eq : st.scratch.extend_len = s0.scratch.extend_len := by rw [hbt.same_scratch]
  have href_eq : fullArenaClauseRefs st = fullArenaClauseRefs s0 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har_eq, hal_eq]
  refine ⟨hbt.len_ok, hw',
    ⟨fun v hv => by rw [hmrk_eq]; exact hsp0.2.2.1.1 v hv,
     fun l hl => by rw [hlm_eq]; exact hsp0.2.2.1.2 l hl⟩,
    fun r hr hng => by
      rw [href_eq] at hr
      have hg : fullArenaClauseGarb s0 r = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
        rwa [← har_eq]
      have hl : fullArenaClauseLits st r = fullArenaClauseLits s0 r := by
        unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har_eq]
      rw [hl]; exact hsp0.2.2.2.1 r hr hg,
    ⟨fun i hi => by
      change st.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨ _
      rw [hll_eq, href_eq]; exact hsp0.2.2.2.2.1.1 i hi,
     by change st.scratch.extend_len ≤ c.extend_cap; rw [hex_eq]; exact hsp0.2.2.2.2.1.2⟩,
    hdm_eq.trans hsp0.2.2.2.2.2⟩
private theorem bb_sext32_64_1 : BitVec.signExtend 64 1#32 = 1#64 := rfl
private theorem bb_bv64_shl1_sext (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x <<< BitVec.signExtend 64 1#32).toNat = 2 * x.toNat := by
  change (x <<< ((BitVec.signExtend 64 1#32).toNat % 64)).toNat = 2 * x.toNat
  rw [show (BitVec.signExtend 64 1#32).toNat % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega
private theorem bb_bv64_shl1_sext_tr (x : BitVec 64) {n : Nat} (hx : x.toNat < n)
    (hn : 2 * n < 2 ^ 32) :
    ((x <<< BitVec.signExtend 64 1#32).truncate 32).toNat < 2 * n := by
  have h1 := bb_bv64_shl1_sext x (by omega)
  rw [BitVec.toNat_setWidth, h1, Nat.mod_eq_of_lt (by omega)]; omega
private theorem bb_bv64_shl1_sext_or1_tr (x : BitVec 64) {n : Nat} (hx : x.toNat < n)
    (hn : 2 * n < 2 ^ 32) :
    (((x <<< BitVec.signExtend 64 1#32) ||| 1#64).truncate 32).toNat < 2 * n := by
  change (((x <<< (1 : Nat)) ||| 1#64).setWidth 32).toNat < 2 * n
  rw [FullTransHelpers.ft_bv64_shl1_or1_setWidth32 (by omega)]; omega
private theorem bb_bv64_shl1_nat (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat :=
  FullTransHelpers.ft_bv64_shl1 (by omega)
private theorem bb_xor1_xor1 (l : Nat) : (l ^^^ 1) ^^^ 1 = l := litNeg_litNeg l
private theorem bb_pigeonhole_le :
    ∀ (n m : Nat) (f : Nat → Nat),
      (∀ i < m, f i < n) → (∀ i j, i < m → j < m → f i = f j → i = j) → m ≤ n
  | 0, m, f, hlt, _ => by
    cases m with
    | zero => exact Nat.le_refl 0
    | succ m' => exact absurd (hlt 0 (Nat.zero_lt_succ m')) (Nat.not_lt_zero _)
  | n + 1, m, f, hlt, hinj => by
    by_cases hex : ∃ k < m, f k = n
    · obtain ⟨k, hk, hfk⟩ := hex
      let g (i : Nat) : Nat := if i < k then f i else f (i + 1)
      have hg : m - 1 ≤ n := bb_pigeonhole_le n (m - 1) g
        (fun i hi => by
          dsimp only [g]; split
          · have h1 := hlt i (by omega)
            have hne : f i ≠ n := fun h => by
              have := hinj i k (by omega) hk (h.trans hfk.symm); omega
            omega
          · have h1 := hlt (i + 1) (by omega)
            have hne : f (i + 1) ≠ n := fun h => by
              have := hinj (i + 1) k (by omega) hk (h.trans hfk.symm); omega
            omega)
        (fun i j hi hj heq => by
          dsimp only [g] at heq; split at heq <;> split at heq
          · exact hinj i j (by omega) (by omega) heq
          · have := hinj i (j + 1) (by omega) (by omega) heq; omega
          · have := hinj (i + 1) j (by omega) (by omega) heq; omega
          · have := hinj (i + 1) (j + 1) (by omega) (by omega) heq; omega)
      omega
    · have hlt' : ∀ i < m, f i < n := fun i hi => by
        have := hlt i hi; have hne : f i ≠ n := fun h => hex ⟨i, hi, h⟩; omega
      exact Nat.le_trans (bb_pigeonhole_le n m f hlt' hinj) (Nat.le_succ n)
private theorem BbTrailInv.var_unassigned {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl l : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (_hl : l < 2 * s0.core.cur_vars) (h0 : st.core.vals[l]?.getD 0#8 = 0#8) :
    ∀ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  intro i hi heq
  obtain ⟨hv1, hvff⟩ := hbt.trl_vals_ok i hi
  rcases (litVar_eq_iff _ _).mp heq with hl1 | hl2
  · rw [hl1, h0] at hv1; cases hv1
  · change (st.core.trl[i]?.getD 0#32).toNat = l ^^^ 1 at hl2
    rw [show (st.core.trl[i]?.getD 0#32).toNat ^^^ 1 = l by
      rw [hl2]; exact litNeg_litNeg l, h0] at hvff
    cases hvff
private theorem BbTrailInv.push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl new_max : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hmax : max_lvl ≤ new_max) {lit rsn : BitVec 32} {lv_bv : BitVec 32} {cl' : Nat}
    (hlit : lit.toNat < 2 * s0.core.cur_vars) (h0 : st.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hte_lt : st.core.trail_end < c.max_vars) (hlv_le : lv_bv.toNat ≤ new_max)
    (hcl_le : cl' ≤ new_max)
    (hl0_ent : lv_bv.toNat = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := st.core.lvl.set v lv_bv
        rsns := st.core.rsns.set v rsn
        trl := st.core.trl.set st.core.trail_end lit
        trail_end := st.core.trail_end + 1
        cur_level := cl' } }
    BbTrailInv c F0 F_cur s0 st' saved0 new_max := by
  intro v st'
  have hcl := hbt.len_ok.core_ok
  have hcv_eq : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_eq ▸ hcl.cur_vars_le
  have hmiss := hbt.var_unassigned hlit h0
  have hne_lit : lit.toNat ≠ lit.toNat ^^^ 1 := (litNeg_ne_self lit.toNat).symm
  have hnot_lt : lit.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hlit
  have h0_s0 : s0.core.vals[lit.toNat]?.getD 0#8 = 0#8 :=
    Classical.byContradiction fun hnz => by rw [hbt.vals_prefix _ hlit hnz] at h0; exact hnz h0
  have h0_not : st.core.vals[lit.toNat ^^^ 1]?.getD 0#8 = 0#8 := by
    rcases hbt.vals_dom _ hnot_lt with hz | h1 | hff
    · exact hz
    · obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl _ hnot_lt h1
      exact absurd (by rw [heq, fullInv_var_xor1]) (hmiss i hi)
    · obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl _ hnot_lt hff
      rw [show (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat from litNeg_litNeg _] at heq
      exact absurd (by rw [heq]) (hmiss i hi)
  have h0_not_s0 : s0.core.vals[lit.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
    Classical.byContradiction fun hnz => by
      rw [hbt.vals_prefix _ hnot_lt hnz] at h0_not; exact hnz h0_not
  have hv_len := hcl.vals_len; have hl_len := hcl.lvl_len
  have hr_len := hcl.rsns_len; have ht_len := hcl.trl_len
  have hv_lt : v < c.max_vars := by omega
  have hte_lt_cv : st.core.trail_end < s0.core.cur_vars := by
    let f (i : Nat) : Nat :=
      if i < st.core.trail_end then (st.core.trl[i]?.getD 0#32).toNat / 2 else v
    have hle := bb_pigeonhole_le s0.core.cur_vars (st.core.trail_end + 1) f
      (fun i hi => by
        dsimp only [f]; split
        · rename_i hlt; have := hbt.trl_lits_lt i hlt; omega
        · omega)
      (fun i j hi hj heq => by
        dsimp only [f] at heq; split at heq <;> split at heq
        · exact hbt.trl_vars_nodup i j ‹_› ‹_› heq
        · exact absurd heq (hmiss i ‹_›)
        · exact absurd heq.symm (hmiss j ‹_›)
        · omega)
    omega
  have hte_eq_len : st.core.trail_end < st.core.trl.length := by omega
  exact
    { len_ok := ⟨{ hcl with
        vals_len := by simp [st', hv_len], lvl_len := by simp [st', hl_len]
        rsns_len := by simp [st', hr_len], trl_len := by simp [st', ht_len]
        trail_end_le := by simp [st', hcv_eq]; omega
        propagated_le := by simp [st']; have := hcl.propagated_le; omega }, hbt.len_ok.scratch_ok⟩
      s0_l0 := hbt.s0_l0
      same_core := by dsimp only [st']; rw [hbt.same_core]
      same_scratch := hbt.same_scratch
      saved0_eq := hbt.saved0_eq
      saved0_le := by dsimp only [st']; have := hbt.saved0_le; omega
      cur_le_max := hcl_le
      trl_prefix := fun i hi => by
        dsimp only [st']; rw [List.getElem?_set_ne (by have := hbt.saved0_le; omega)]
        exact hbt.trl_prefix i hi
      vals_prefix := fun l hl hnz => by
        dsimp only [st']
        rw [bb_getD_set2_ne (fun e => hnz (by rw [e]; exact h0_s0))
          (fun e => hnz (by rw [e]; exact h0_not_s0))]
        exact hbt.vals_prefix l hl hnz
      vals_hi := fun l hl => by
        dsimp only [st']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hbt.vals_hi l hl
      lvl_prefix := fun i hi => by
        have hti := hbt.trl_prefix i hi
        have hne_v : (s0.core.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
          rw [← hti]; exact hmiss i (by have := hbt.saved0_le; omega)
        dsimp only [st']
        rw [List.getElem?_set_ne hne_v.symm, List.getElem?_set_ne hne_v.symm]
        exact hbt.lvl_prefix i hi
      trl_lits_lt := fun i hi => by
        dsimp only [st'] at hi ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some]; exact hlit
        · rw [List.getElem?_set_ne (Ne.symm he)]; exact hbt.trl_lits_lt i (by omega)
      trl_vars_nodup := fun i j hi hj heq => by
        dsimp only [st'] at hi hj heq
        by_cases hie : i = st.core.trail_end <;> by_cases hje : j = st.core.trail_end
        · omega
        · subst hie; rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
            List.getElem?_set_ne (Ne.symm hje)] at heq
          exact absurd heq.symm (hmiss j (by omega))
        · subst hje; rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
            List.getElem?_set_ne (Ne.symm hie)] at heq
          exact absurd heq (hmiss i (by omega))
        · rw [List.getElem?_set_ne (Ne.symm hie), List.getElem?_set_ne (Ne.symm hje)] at heq
          exact hbt.trl_vars_nodup i j (by omega) (by omega) heq
      trl_vals_ok := fun i hi => by
        dsimp only [st'] at hi ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some]
          refine ⟨by rw [List.getElem?_set_ne hne_lit.symm,
                       List.getElem?_set_self (by omega), Option.getD_some],
                  by rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some]⟩
        · rw [List.getElem?_set_ne (Ne.symm he)]
          obtain ⟨h1, h2, h3, h4⟩ := bb_var_ne_xor (hmiss i (by omega))
          rw [bb_getD_set2_ne h1 h2, bb_getD_set2_ne h3 h4]
          exact hbt.trl_vals_ok i (by omega)
      vals_dom := fun l hl => by
        dsimp only [st']
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; right; right
          rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm h1)]
          by_cases h2 : l = lit.toNat
          · subst h2; right; left
            rw [List.getElem?_set_self (by omega), Option.getD_some]
          · rw [List.getElem?_set_ne (Ne.symm h2)]; exact hbt.vals_dom l hl
      vals_true_trl := fun l hl hv1 => by
        dsimp only [st'] at hv1 ⊢
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some] at hv1
          cases hv1
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hv1
          by_cases h2 : l = lit.toNat
          · subst h2; exact ⟨st.core.trail_end, by omega, by
              rw [List.getElem?_set_self hte_eq_len, Option.getD_some]⟩
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hv1
            obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl l hl hv1
            exact ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact heq⟩
      vals_false_trl := fun l hl hvff => by
        dsimp only [st'] at hvff ⊢
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; exact ⟨st.core.trail_end, by omega, by
            rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
              show (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat from litNeg_litNeg _]⟩
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hvff
          by_cases h2 : l = lit.toNat
          · subst h2; rw [List.getElem?_set_self (by omega), Option.getD_some] at hvff; cases hvff
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hvff
            obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl l hl hvff
            exact ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact heq⟩
      lvl_le_max := fun i hi => by
        dsimp only [st'] at hi ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
            List.getElem?_set_self (by omega), Option.getD_some]; exact hlv_le
        · rw [List.getElem?_set_ne (Ne.symm he),
            List.getElem?_set_ne (Ne.symm (hmiss i (by omega)))]
          exact Nat.le_trans (hbt.lvl_le_max i (by omega)) hmax
      l0_entails := fun i hi hlv0 => by
        dsimp only [st'] at hi hlv0 ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some] at hlv0 ⊢
          rw [List.getElem?_set_self (by omega), Option.getD_some] at hlv0
          exact hl0_ent hlv0
        · rw [List.getElem?_set_ne (Ne.symm he)] at hlv0 ⊢
          rw [List.getElem?_set_ne (Ne.symm (hmiss i (by omega)))] at hlv0
          exact hbt.l0_entails i (by omega) hlv0 }
private theorem BbTrailInv.pop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hsp0 : FullSparseInvW c F0 F_cur s0)
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hgt : saved0 < st.core.trail_end) :
    let te' := st.core.trail_end - 1
    let ul := st.core.trl[te']?.getD 0#32
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set ul.toNat 0#8).set (ul.toNat ^^^ 1) 0#8
        trail_end := te' } }
    ul.toNat < 2 * s0.core.cur_vars ∧ BbTrailInv c F0 F_cur s0 st' saved0 max_lvl := by
  intro te' ul st'
  have hw0 := hsp0.2.1
  have hcl := hbt.len_ok.core_ok
  have hcv_eq : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_eq ▸ hcl.cur_vars_le
  have hult : ul.toNat < 2 * s0.core.cur_vars := hbt.trl_lits_lt te' (by omega)
  have hnot_lt : ul.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hult
  have hne_ul : ul.toNat ≠ ul.toNat ^^^ 1 := (litNeg_ne_self ul.toNat).symm
  have hv_len := hcl.vals_len
  have hmiss : ∀ i < te', (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ ul.toNat / 2 :=
    fun i hi heq => by have := hbt.trl_vars_nodup i te' (by omega) (by omega) heq; omega
  have h0_s0_of : ∀ q < 2 * s0.core.cur_vars, q / 2 = ul.toNat / 2 →
      s0.core.vals[q]?.getD 0#8 = 0#8 := fun q hq hqv =>
    (hw0.vals_zero_iff hq).mpr fun k hk heq => by
      have hk_s : k < saved0 := hbt.saved0_eq ▸ hk
      have hkt := hbt.trl_prefix k hk_s
      exact hmiss k (by omega) (by rw [hkt, heq, hqv])
  have h0_ul : s0.core.vals[ul.toNat]?.getD 0#8 = 0#8 := h0_s0_of ul.toNat hult rfl
  have h0_not : s0.core.vals[ul.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
    h0_s0_of (ul.toNat ^^^ 1) hnot_lt (fullInv_var_xor1 ul.toNat)
  have hprop_le : st.core.propagated ≤ te' := by
    have hp0 : st.core.propagated = s0.core.propagated := by rw [hbt.same_core]
    have hle0 := hsp0.1.core_ok.propagated_le
    have hs0 := hbt.saved0_eq; omega
  refine ⟨hult,
    { len_ok := ⟨{ hcl with
        vals_len := by simp [st', hv_len]
        trail_end_le := by simp [st']; have := hcl.trail_end_le; omega
        propagated_le := by simp [st']; exact hprop_le }, hbt.len_ok.scratch_ok⟩
      s0_l0 := hbt.s0_l0
      same_core := by dsimp only [st']; rw [hbt.same_core]
      same_scratch := hbt.same_scratch
      saved0_eq := hbt.saved0_eq
      saved0_le := by dsimp only [st']; omega
      cur_le_max := hbt.cur_le_max
      trl_prefix := hbt.trl_prefix
      vals_prefix := fun l hl hnz => by
        dsimp only [st']
        rw [bb_getD_set2_ne (fun e => hnz (by rw [e]; exact h0_ul))
          (fun e => hnz (by rw [e]; exact h0_not))]
        exact hbt.vals_prefix l hl hnz
      vals_hi := fun l hl => by
        dsimp only [st']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hbt.vals_hi l hl
      lvl_prefix := hbt.lvl_prefix
      trl_lits_lt := fun i hi => hbt.trl_lits_lt i (by dsimp only [st'] at hi; omega)
      trl_vars_nodup := fun i j hi hj heq =>
        hbt.trl_vars_nodup i j (by dsimp only [st'] at hi; omega)
          (by dsimp only [st'] at hj; omega) heq
      trl_vals_ok := fun i hi => by
        dsimp only [st'] at hi ⊢
        obtain ⟨h1, h2, h3, h4⟩ := bb_var_ne_xor (hmiss i hi)
        rw [bb_getD_set2_ne h1 h2, bb_getD_set2_ne h3 h4]
        exact hbt.trl_vals_ok i (by omega)
      vals_dom := fun l hl => by
        dsimp only [st']
        by_cases h1 : l = ul.toNat ^^^ 1
        · subst h1; left
          rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm h1)]
          by_cases h2 : l = ul.toNat
          · subst h2; left
            rw [List.getElem?_set_self (by omega), Option.getD_some]
          · rw [List.getElem?_set_ne (Ne.symm h2)]; exact hbt.vals_dom l hl
      vals_true_trl := fun l hl hv1 => by
        dsimp only [st'] at hv1 ⊢
        by_cases h1 : l = ul.toNat ^^^ 1
        · subst h1; rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some] at hv1
          cases hv1
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hv1
          by_cases h2 : l = ul.toNat
          · subst h2; rw [List.getElem?_set_self (by omega), Option.getD_some] at hv1; cases hv1
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hv1
            obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl l hl hv1
            have hne : i ≠ te' := fun he => by subst he; exact h2 heq.symm
            exact ⟨i, by omega, heq⟩
      vals_false_trl := fun l hl hvff => by
        dsimp only [st'] at hvff ⊢
        by_cases h1 : l = ul.toNat ^^^ 1
        · subst h1; rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some] at hvff
          cases hvff
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hvff
          by_cases h2 : l = ul.toNat
          · subst h2; rw [List.getElem?_set_self (by omega), Option.getD_some] at hvff; cases hvff
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hvff
            obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl l hl hvff
            have hne : i ≠ te' := fun he => by
              subst he
              have := congrArg (· ^^^ 1) heq
              rw [bb_xor1_xor1] at this
              exact h1 this.symm
            exact ⟨i, by omega, heq⟩
      lvl_le_max := fun i hi => hbt.lvl_le_max i (by dsimp only [st'] at hi; omega)
      l0_entails := fun i hi hlv0 => hbt.l0_entails i (by dsimp only [st'] at hi; omega) hlv0 }⟩
private theorem bb_sparseW_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  ⟨⟨{ hsp.1.core_ok with flags_len := hfl }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
private theorem bb_sparseW_with_ws1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {ws1' : List (BitVec 32)}
    (hws1 : ws1'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with work_stk1_len := hws1 }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
private theorem bb_sparseW_with_fl_ws1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {fl' ws1' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) (hws1 : ws1'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with flags := fl' }
               scratch := { s.scratch with work_stk1 := ws1' } } :=
  bb_sparseW_with_ws1 (bb_sparseW_with_flags hsp hfl) hws1
private theorem bb_sparseW_with_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (pr' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with probing := pr' } } :=
  ⟨⟨{ hsp.1.core_ok with }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
private theorem bb_sparseW_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (asz' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with ant_sz := asz' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
private theorem bb_sparseW_with_delayed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (dl' : Nat) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with delayed_len := dl' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
private theorem bb_sparseW_of_prop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)}
    (hsp : FullSparseInvW c F0 F_cur s)
    (hs' : s' = { s with
      core := { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', unassigned := unass', unflushed := unfl',
        wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
        fuel := fuel', confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
        confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } })
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
private theorem BbTrailInv.with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl) (asz' : BitVec 64) :
    BbTrailInv c F0 F_cur s0
      { st with scratch := { st.scratch with ant_sz := asz' } } saved0 max_lvl :=
  { hbt with
    len_ok := ⟨hbt.len_ok.core_ok, { hbt.len_ok.scratch_ok with }⟩
    same_scratch := by dsimp only; rw [hbt.same_scratch] }
private theorem BbTrailInv.with_ws1_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    {ws1' ws2' : List (BitVec 32)} {rsz' : BitVec 64}
    (h1 : ws1'.length = 2 * c.max_vars) (h2 : ws2'.length = 2 * c.max_vars) :
    BbTrailInv c F0 F_cur s0
      { st with scratch := { st.scratch with
        work_stk1 := ws1', work_stk2 := ws2', res_sz := rsz' } } saved0 max_lvl :=
  { hbt with
    len_ok := ⟨hbt.len_ok.core_ok,
      { hbt.len_ok.scratch_ok with work_stk1_len := h1, work_stk2_len := h2 }⟩
    same_scratch := by dsimp only; rw [hbt.same_scratch] }
private theorem BbTrailInv.with_confl_asz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (c0' c1' asz' : BitVec 64) :
    BbTrailInv c F0 F_cur s0
      { st with
        core := { st.core with confl_lit0 := c0', confl_lit1 := c1' }
        scratch := { st.scratch with ant_sz := asz' } } saved0 max_lvl :=
  { hbt with
    len_ok := ⟨{ hbt.len_ok.core_ok with }, { hbt.len_ok.scratch_ok with }⟩
    same_core := by dsimp only; rw [hbt.same_core]
    same_scratch := by dsimp only; rw [hbt.same_scratch] }
private theorem BbTrailInv.with_cur_level {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl new_max cl' : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hcl : cl' ≤ new_max)
    (hlvl : ∀ i < st.core.trail_end,
      (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ new_max) :
    BbTrailInv c F0 F_cur s0
      { st with core := { st.core with cur_level := cl' } } saved0 new_max :=
  { hbt with
    len_ok := ⟨{ hbt.len_ok.core_ok with }, hbt.len_ok.scratch_ok⟩
    same_core := by dsimp only; rw [hbt.same_core]
    cur_le_max := hcl
    lvl_le_max := hlvl }
private theorem BbTrailInv.with_mrk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (_hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hsp0 : FullSparseInvW c F0 F_cur s0) {mrk' : List (BitVec 8)}
    (hmrk_len : mrk'.length = c.max_vars)
    (hmrk0 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) :
    mrk' = s0.core.mrk := by
  have hlen0 := hsp0.1.core_ok.mrk_len
  refine List.ext_getElem (by omega) fun v hv1 _ => ?_
  have h1 := hmrk0 v (by omega)
  have h2 := hsp0.2.2.1.1 v (by omega)
  rw [List.getElem?_eq_getElem hv1, Option.getD_some] at h1
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h2
  exact h1.trans h2.symm
private theorem bb_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := h ▸ hm

end BbHelpers

/-! ## 3. Backbone Helper Proofs (`sched`, `keep`, `unwind`) -/

section BackboneSimpleProofs

/-- `full_backbone_sched_m6` satisfies `fullBackboneSchedM6Spec`. -/
theorem full_backbone_sched_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackboneSchedM6Spec a m Q X →
      Func.wp Γ full_backbone_sched_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hm0, hQ⟩
  have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hfl_len := hcl.flags_len
  have hvals_len := hcl.vals_len; have hws1_len := hscl.work_stk1_len
  unfold Func.wp full_backbone_sched_m6_body
  fvt_to_group
  refine wp_loop_inv (ts := [i64, i64])
    (fun (cand_n, v, ()) m1 =>
      ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
        v.toNat ≤ s.core.cur_vars ∧ cand_n.toNat ≤ 2 * v.toNat ∧
        (∀ i < cand_n.toNat, (ws1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
    (fun (_, v, ()) _ => s.core.cur_vars - v.toNat) ?_ ?_
  · intro J1 hJ1; fvt_steps
    exact hJ1 (0#64, 0#64, ()) m0 ⟨s.scratch.work_stk1, hws1_len, Nat.zero_le _,
      Nat.zero_le _, (fun _ h => by cases h), hm0⟩
  · rintro J1 ⟨cand_n, v, ⟨⟩⟩ m1 ⟨ws1, hws1, hv_le, hcn_le, hlt1, hm1⟩ ih1
    fvt_step; fvt_step
    · have hv_lt : v.toNat < s.core.cur_vars := by
        have h1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt (by omega)] at h1
      have hv_fl : v.toNat < s.core.flags.length := by omega
      have hv1_eq : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
      have hv2_eq : (v <<< (BitVec.signExtend 64 1#32)).toNat = 2 * v.toNat :=
        bb_bv64_shl1_sext v (by omega)
      have hv2_lt : (v <<< (BitVec.signExtend 64 1#32)).toNat < s.core.vals.length := by omega
      fvt_to_group
      refine wp_join_group (ts := [i64])
        (fun (cn', ()) m2 => ∃ ws1' : List (BitVec 32), ws1'.length = 2 * c.max_vars ∧
          cn'.toNat ≤ 2 * (v.toNat + 1) ∧
          (∀ i < cn'.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m2)
        (fun _ ⟨cn', ⟨⟩⟩ m2 ⟨ws1', hws1', hcn', hlt', hm2⟩ => by
          fvt_steps
          exact ih1 (cn', v + 1#64, ()) m2 (by dsimp only; omega)
            ⟨ws1', hws1', by omega, by omega, hlt', hm2⟩)
        (fun Jn hJn => by
          fvt_to_group
          · refine wp_join_group (ts := [i64])
              (fun (cn1, ()) m_a => ∃ ws1_a : List (BitVec 32), ws1_a.length = 2 * c.max_vars ∧
                cn1.toNat ≤ 2 * v.toNat + 1 ∧
                (∀ i < cn1.toNat, (ws1_a[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1_a } } ⋆ R) m_a)
              (fun _ ⟨cn1, ⟨⟩⟩ m_a ⟨ws1_a, hws1_a, hcn1, hlta, hma⟩ => by
                refine wp_join_group (ts := [i64])
                  (fun (cn2, ()) m_b => ∃ ws1_b : List (BitVec 32),
                    ws1_b.length = 2 * c.max_vars ∧ cn2.toNat ≤ 2 * (v.toNat + 1) ∧
                    (∀ i < cn2.toNat, (ws1_b[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1_b } } ⋆ R) m_b)
                  (fun _ ⟨cn2, ⟨⟩⟩ m_b h => hJn (cn2, ()) m_b h)
                  (fun Jb hJb => by
                    have hcn1_lt : cn1.toNat < ws1_a.length := by omega
                    have hcn1_1 : (cn1 + 1#64).toNat = cn1.toNat + 1 := by bv_omega
                    have hl1_lt :
                        (((v <<< (BitVec.signExtend 64 1#32)) ||| 1#64).truncate 32).toNat <
                          2 * s.core.cur_vars := bb_bv64_shl1_sext_or1_tr v hv_lt (by omega)
                    fvt_steps
                    · refine hJb (cn1 + 1#64, ()) _ ⟨_, by simp [hws1_a], by omega,
                        fun i hi => ?_, hm⟩
                      rcases (by omega : i < cn1.toNat ∨ i = cn1.toNat) with hi' | rfl
                      · rw [List.getElem?_set_ne (by omega)]; exact hlta i hi'
                      · rw [List.getElem?_set_self hcn1_lt, Option.getD_some]; exact hl1_lt
                    · exact hJb (cn1, ()) m_a ⟨ws1_a, hws1_a, by omega, hlta, hma⟩))
              (fun Ja hJa => by
                have hcn_lt : cand_n.toNat < ws1.length := by omega
                have hcn_1 : (cand_n + 1#64).toNat = cand_n.toNat + 1 := by bv_omega
                have hl0_lt :
                    ((v <<< (BitVec.signExtend 64 1#32)).truncate 32).toNat <
                      2 * s.core.cur_vars := bb_bv64_shl1_sext_tr v hv_lt (by omega)
                fvt_steps
                · refine hJa (cand_n + 1#64, ()) _ ⟨_, by simp [hws1], by omega,
                    fun i hi => ?_, hm⟩
                  rcases (by omega : i < cand_n.toNat ∨ i = cand_n.toNat) with hi' | rfl
                  · rw [List.getElem?_set_ne (by omega)]; exact hlt1 i hi'
                  · rw [List.getElem?_set_self hcn_lt, Option.getD_some]; exact hl0_lt
                · exact hJa (cand_n, ()) m1 ⟨ws1, hws1, by omega, hlt1, hm1⟩)
          · exact hJn (cand_n, ()) m1 ⟨ws1, hws1, by omega, hlt1, hm1⟩
          · exact hJn (cand_n, ()) m1 ⟨ws1, hws1, by omega, hlt1, hm1⟩)
    · clear hc ih1 J1
      fvt_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (cn_f, _, ()) mf => ∃ (fl' ws1' : List (BitVec 32)),
          fl'.length = c.max_vars ∧ ws1'.length = 2 * c.max_vars ∧
          cn_f.toNat ≤ 2 * s.core.cur_vars ∧
          (∀ i < cn_f.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          (FullMem c { s with core := { s.core with flags := fl' }
                              scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) mf)
        (fun _ ⟨cn_f, _, ⟨⟩⟩ mf ⟨fl', ws1', hfl', hws1', hcn_f, hlt_f, hmf⟩ => by
          fvt_steps
          exact hQ cn_f fl' ws1' mf (bb_sparseW_with_fl_ws1 hsp hfl' hws1') hcn_f hlt_f hmf)
        (fun Jf hJf => by
          fvt_step; fvt_step
          · refine wp_loop_inv (ts := [i64, i64])
              (fun (cn2, v2, ()) m2 => ∃ (fl2 ws2 : List (BitVec 32)),
                fl2.length = c.max_vars ∧ ws2.length = 2 * c.max_vars ∧
                v2.toNat ≤ s.core.cur_vars ∧ cn2.toNat ≤ 2 * v2.toNat ∧
                (∀ i < cn2.toNat, (ws2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                (FullMem c { s with core := { s.core with flags := fl2 }
                                    scratch := { s.scratch with work_stk1 := ws2 } } ⋆ R) m2)
              (fun (_, v2, ()) _ => s.core.cur_vars - v2.toNat) ?_ ?_
            · intro J2 hJ2; fvt_steps
              have hcn0 : cand_n = 0#64 := by c0_bound
              exact hJ2 (cand_n, 0#64, ()) m1 ⟨s.core.flags, ws1, hfl_len, hws1,
                Nat.zero_le _, by simp [hcn0], (fun i hi => by simp [hcn0] at hi), hm1⟩
            · rintro J2 ⟨cn2, v2, ⟨⟩⟩ m2 ⟨fl2, ws2, hfl2, hws2, hv2_le, hcn2_le, hlt2, hm2⟩ ih2
              fvt_step; fvt_step
              · have hv2_lt : v2.toNat < s.core.cur_vars := by
                  have h1 : v2.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
                  rwa [Nat.mod_eq_of_lt (by omega)] at h1
                have hv2_fl : v2.toNat < fl2.length := by omega
                have hv2_1 : (v2 + 1#64).toNat = v2.toNat + 1 := by bv_omega
                have hv2_shl : (v2 <<< (BitVec.signExtend 64 1#32)).toNat = 2 * v2.toNat :=
                  bb_bv64_shl1_sext v2 (by omega)
                have hv2_val : (v2 <<< (BitVec.signExtend 64 1#32)).toNat < s.core.vals.length := by
                  omega
                fvt_to_group
                refine wp_join_group (ts := [i64])
                  (fun (cn3, ()) m3 => ∃ (fl3 ws3 : List (BitVec 32)),
                    fl3.length = c.max_vars ∧ ws3.length = 2 * c.max_vars ∧
                    cn3.toNat ≤ 2 * (v2.toNat + 1) ∧
                    (∀ i < cn3.toNat, (ws3[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                    (FullMem c { s with core := { s.core with flags := fl3 }
                                        scratch := { s.scratch with work_stk1 := ws3 } } ⋆ R) m3)
                  (fun _ ⟨cn3, ⟨⟩⟩ m3 ⟨fl3, ws3, hfl3, hws3, hcn3, hlt3, hm3⟩ => by
                    fvt_steps
                    exact ih2 (cn3, v2 + 1#64, ()) m3 (by dsimp only; omega)
                      ⟨fl3, ws3, hfl3, hws3, by omega, by omega, hlt3, hm3⟩)
                  (fun Jm hJm => by
                    have hcn2_lt : cn2.toNat < ws2.length := by omega
                    have hcn2_1 : (cn2 + 1#64).toNat = cn2.toNat + 1 := by bv_omega
                    have hcn2_1_lt : (cn2 + 1#64).toNat < (ws2.set cn2.toNat
                        ((v2 <<< (BitVec.signExtend 64 1#32)).truncate 32)).length := by
                      simp [hws2]; omega
                    have hcn2_2 : (cn2 + 1#64 + 1#64).toNat = cn2.toNat + 2 := by bv_omega
                    have hl0_lt :
                        ((v2 <<< (BitVec.signExtend 64 1#32)).truncate 32).toNat <
                          2 * s.core.cur_vars := bb_bv64_shl1_sext_tr v2 hv2_lt (by omega)
                    have hl1_lt :
                        (((v2 <<< (BitVec.signExtend 64 1#32)) ||| 1#64).truncate 32).toNat <
                          2 * s.core.cur_vars := bb_bv64_shl1_sext_or1_tr v2 hv2_lt (by omega)
                    fvt_steps
                    · refine hJm (cn2 + 1#64 + 1#64, ()) _
                        ⟨_, _, by simp [hfl2], by simp [hws2], by omega, fun i hi => ?_, hm⟩
                      have h1_eq : (cn2 + 1).toNat = cn2.toNat + 1 := hcn2_1
                      by_cases h1 : i = cn2.toNat + 1
                      · subst h1
                        rw [← h1_eq, List.getElem?_set_self (by rw [List.length_set, h1_eq]; omega),
                          Option.getD_some]
                        exact hl1_lt
                      · rw [List.getElem?_set_ne (by rw [h1_eq]; omega)]
                        by_cases h0 : i = cn2.toNat
                        · subst h0; rw [List.getElem?_set_self hcn2_lt, Option.getD_some]
                          exact hl0_lt
                        · rw [List.getElem?_set_ne (Ne.symm h0)]; exact hlt2 i (by omega)
                    · exact hJm (cn2, ()) m2 ⟨fl2, ws2, hfl2, hws2, by omega, hlt2, hm2⟩
                    · exact hJm (cn2, ()) m2 ⟨fl2, ws2, hfl2, hws2, by omega, hlt2, hm2⟩)
              · fvt_steps
                exact hJf (cn2, v2, ()) m2 ⟨fl2, ws2, hfl2, hws2, by omega, hlt2, hm2⟩
          · fvt_steps
            exact hJf (cand_n, v, ()) m1 ⟨s.core.flags, ws1, hfl_len, hws1, by omega, hlt1, hm1⟩)

/-- `full_backbone_keep_m6` satisfies `fullBackboneKeepM6Spec`. -/
theorem full_backbone_keep_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Func.wp Γ full_backbone_keep_m6_body a m Q X := by
  rintro ⟨h, cand_n, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcn_le, hlt_c, hm0, hQ⟩
  have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hfl_len := hcl.flags_len
  have hvals_len := hcl.vals_len; have hws1_len := hscl.work_stk1_len
  unfold Func.wp full_backbone_keep_m6_body
  fvt_to_group
  refine wp_loop_inv (ts := [i64])
    (fun (v, ()) m1 => ∃ fl1 : List (BitVec 32), fl1.length = c.max_vars ∧
      v.toNat ≤ s.core.cur_vars ∧
      (FullMem c { s with core := { s.core with flags := fl1 } } ⋆ R) m1)
    (fun (v, ()) _ => s.core.cur_vars - v.toNat) ?_ ?_
  · intro J1 hJ1; fvt_steps
    exact hJ1 (0#64, ()) m0 ⟨s.core.flags, hfl_len, Nat.zero_le _, hm0⟩
  · rintro J1 ⟨v, ⟨⟩⟩ m1 ⟨fl1, hfl1, hv_le, hm1⟩ ih1
    fvt_step; fvt_step
    · have hv_lt : v.toNat < s.core.cur_vars := by
        have h1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt (by omega)] at h1
      have hv_fl : v.toNat < fl1.length := by omega
      have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
      fvt_steps
      exact ih1 (v + 1#64, ()) _ (by dsimp only; omega) ⟨_, by simp [hfl1], by omega, hm⟩
    · clear hc ih1 J1
      fvt_to_group
      refine wp_loop_inv (ts := [i64])
        (fun (i, ()) m2 => ∃ fl2 : List (BitVec 32), fl2.length = c.max_vars ∧
          i.toNat ≤ cand_n.toNat ∧
          (FullMem c { s with core := { s.core with flags := fl2 } } ⋆ R) m2)
        (fun (i, ()) _ => cand_n.toNat - i.toNat) ?_ ?_
      · intro J2 hJ2; fvt_steps
        exact hJ2 (0#64, ()) m1 ⟨fl1, hfl1, Nat.zero_le _, hm1⟩
      · rintro J2 ⟨i, ⟨⟩⟩ m2 ⟨fl2, hfl2, hi_le, hm2⟩ ih2
        fvt_step; fvt_step
        · have hi_lt : i.toNat < cand_n.toNat := by c0_bound
          have hi_ws1 : i.toNat < s.scratch.work_stk1.length := by omega
          have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
          let lit := s.scratch.work_stk1[i.toNat]'hi_ws1
          have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
            have := hlt_c i.toNat hi_lt
            rwa [List.getElem?_eq_getElem hi_ws1, Option.getD_some] at this
          have hlit_val : lit.toNat < s.core.vals.length := by omega
          have hlv_fl : (lit >>> 1#32).toNat < fl2.length := by
            rw [bb_bv32_lshr1]; omega
          fvt_to_group
          refine wp_join_group (ts := [])
            (fun _ m3 => ∃ fl3 : List (BitVec 32), fl3.length = c.max_vars ∧
              (FullMem c { s with core := { s.core with flags := fl3 } } ⋆ R) m3)
            (fun _ _ m3 ⟨fl3, hfl3, hm3⟩ => by
              fvt_steps
              exact ih2 (i + 1#64, ()) m3 (by dsimp only; omega) ⟨fl3, hfl3, by omega, hm3⟩)
            (fun Jn hJn => by
              fvt_to_group
              · refine wp_join_group (ts := [])
                  (fun _ m3 => ∃ fl3 : List (BitVec 32), fl3.length = c.max_vars ∧
                    (FullMem c { s with core := { s.core with flags := fl3 } } ⋆ R) m3)
                  (fun _ _ m3 h => hJn () m3 h)
                  (fun Jb hJb => by
                    fvt_steps
                    · exact hJb () _ ⟨_, by simp [hfl2], hm⟩
                    · exact hJb () _ ⟨_, by simp [hfl2], hm⟩)
              · exact hJn () m2 ⟨fl2, hfl2, hm2⟩)
        · fvt_steps
          exact hQ fl2 m2 (bb_sparseW_with_flags hsp hfl2) hm2

/-- `full_backbone_unwind_m6` satisfies `fullBackboneUnwindM6Spec`. -/
theorem full_backbone_unwind_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackboneUnwindM6Spec a m Q X →
      Func.wp Γ full_backbone_unwind_m6_body a m Q X := by
  rintro ⟨h, saved, target_lvl, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, st, saved0, max_lvl, R, rfl, hsp0, hbt, hs0_le, hs_le, htgt_le,
     hlvl_saved, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_backbone_unwind_m6_body
  fvt_to_group
  refine wp_loop_inv (ts := [])
    (fun _ m1 => ∃ (vals1 : List (BitVec 8)) (te1 : Nat),
      let st1 : FullState := { st with core := { st.core with vals := vals1, trail_end := te1 } }
      BbTrailInv c F0 F_cur s0 st1 saved0 max_lvl ∧ saved.toNat ≤ te1 ∧
      (FullMem c st1 ⋆ R) m1)
    (fun _ m1 => (loadVal m1 i64 (c.hdr + 144)).elim 0 BitVec.toNat) ?_ ?_
  · intro J1 hJ1; fvt_steps
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
    fvt_step; fvt_step; fvt_step
    · have hgt_s : saved.toNat < te1 := by
        have h1 : saved.toNat < te1 % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt hte1_64] at h1
      have hpop := BbTrailInv.pop hsp0 hbt1 (by change saved0 < te1; omega)
      have hte1_sub : (BitVec.ofNat 64 te1 - 1#64).toNat = te1 - 1 := by
        rw [BitVec.toNat_sub_of_le (by simp [Nat.mod_eq_of_lt hte1_64]; omega)]
        simp [Nat.mod_eq_of_lt hte1_64]
      have hte1_sub_bv : BitVec.ofNat 64 te1 - 1#64 = BitVec.ofNat 64 (te1 - 1) :=
        BitVec.eq_of_toNat_eq (by rw [hte1_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
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
        rw [FullTransHelpers.ft_bv32_setWidth64]; exact hul_vlen
      have hnot_vlen : (ul ^^^ 1#32).toNat < (vals1.set ul.toNat 0#8).length := by
        rw [List.length_set, bb_bv32_xor1]
        have := litNeg_lt_two_mul hul_lt; omega
      have hnot_vlen64 :
          ((ul ^^^ 1#32).setWidth 64).toNat < (vals1.set (ul.setWidth 64).toNat 0#8).length := by
        rw [List.length_set, FullTransHelpers.ft_bv32_setWidth64, bb_bv32_xor1]
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
      fvt_steps
      let st2 : FullState :=
        { st with core := { st.core with
          vals := (vals1.set ul.toNat 0#8).set (ul.toNat ^^^ 1) 0#8
          trail_end := te1 - 1 } }
      refine ih1 () m ?_ ⟨(vals1.set ul.toNat 0#8).set (ul.toNat ^^^ 1) 0#8, te1 - 1,
        ?_, by omega, ?_⟩
      · have hm2 : (FullMem c st2 ⋆ R) m := by
          refine bb_fullMem_eq ?_ hm
          dsimp only [st1, st2]
          rw [hul_bv_eq, FullTransHelpers.ft_bv32_setWidth64, FullTransHelpers.ft_bv32_setWidth64,
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
        rw [hul_bv_eq, FullTransHelpers.ft_bv32_setWidth64, FullTransHelpers.ft_bv32_setWidth64,
          show (ul ^^^ 1).toNat = ul.toNat ^^^ 1 from bb_bv32_xor1 ul,
          show (BitVec.ofNat 64 te1 - 1).toNat = te1 - 1 from hte1_sub]
    · have hte_eq : te1 = saved.toNat := by
        have h1 : te1 % 2 ^ 64 ≤ saved.toNat := by c0_bound
        rw [Nat.mod_eq_of_lt hte1_64] at h1; omega
      fvt_steps
      have hbt_f := BbTrailInv.with_cur_level hbt1 (new_max := target_lvl.toNat)
        (cl' := target_lvl.toNat) (Nat.le_refl _) (fun i hi => by
          change i < te1 at hi
          have htrl_i : st1.core.trl[i]? = st.core.trl[i]? := rfl
          have hlvl_i : st1.core.lvl = st.core.lvl := rfl
          exact hlvl_saved i (by omega))
      exact hQ vals1 _ (by simpa [hte_eq] using hbt_f) (by
        have hst_eq : ({ st1 with core := { st1.core with cur_level := target_lvl.toNat } } :
            FullState) = { st with core := { st.core with
              vals := vals1, trail_end := saved.toNat, cur_level := target_lvl.toNat } } := by
          dsimp only [st1]; rw [hte_eq]
        rwa [← hst_eq])

end BackboneSimpleProofs

/-! ## 4. Backbone Propagation & 1UIP Analysis Proofs (`prop`, `analyze`) -/

section BackbonePropAnalyzeProofs
private theorem bb_mask7f_or_bin (x : BitVec 32) :
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 ∧
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = (x &&& 0x7FFFFFFF#32) := by
  constructor
  · intro hz
    have hbit := congrArg (fun b : BitVec 32 => b[31]) hz
    simp at hbit
  · rw [BitVec.and_or_distrib_right,
      show (0x80000000#32 &&& 0x7FFFFFFF#32) = 0#32 from rfl, BitVec.or_zero, BitVec.and_assoc,
      show (0x7FFFFFFF#32 &&& 0x7FFFFFFF#32) = 0x7FFFFFFF#32 from rfl]
private theorem bb_mask7f_eq_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat := by
  have heq : x &&& 0x7FFFFFFF#32 = x := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and]
    by_cases h31 : i = 31
    · subst h31
      have hf : x[31] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
        have : x.toNat / 2 ^ 31 = 0 := Nat.div_eq_of_lt h
        simp [this]
      simp [hf]
    · have ht : (0x7FFFFFFF#32)[i] = true := by
        rw [BitVec.getElem_eq_testBit_toNat]
        have : i < 31 := by omega
        revert i this; decide
      simp [ht]
  rw [heq]
private theorem bb_probeSeg_push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl saved target_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hseg : BackboneProbeSeg F_cur st saved target_lvl)
    {ot not_lit : BitVec 32} {lv_bv : BitVec 32} {idx_p : Nat}
    (hot_lt : ot.toNat < 2 * s0.core.cur_vars)
    (h0 : st.core.vals[ot.toNat]?.getD 0#8 = 0#8)
    (hte_lt : st.core.trail_end < c.max_vars)
    (hlv_eq : lv_bv.toNat = target_lvl)
    (hnl_lt : not_lit.toNat < 2 * s0.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [ot.toNat, not_lit.toNat]))
    (hidx_ge : saved ≤ idx_p) (hidx_lt : idx_p < st.core.trail_end)
    (hidx_eq : (st.core.trl[idx_p]?.getD 0#32).toNat = not_lit.toNat ^^^ 1) :
    let v := ot.toNat / 2
    let rsn := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set ot.toNat 1#8).set (ot.toNat ^^^ 1) 0xFF#8
        lvl := st.core.lvl.set v lv_bv
        rsns := st.core.rsns.set v rsn
        trl := st.core.trl.set st.core.trail_end ot
        trail_end := st.core.trail_end + 1 } }
    BackboneProbeSeg F_cur st' saved target_lvl := by
  intro v rsn st'
  have hcl := hbt.len_ok.core_ok
  have hcv_eq : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_eq ▸ hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hmiss := hbt.var_unassigned hot_lt h0
  have hte_trl : st.core.trail_end < st.core.trl.length := by rw [hcl.trl_len]; omega
  have hv_lvl : v < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hv_rsn : v < st.core.rsns.length := by rw [hcl.rsns_len]; omega
  refine ⟨by dsimp only [st']; have := hseg.1; omega, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · have hi_te : i < st.core.trail_end := by have := hseg.1; omega
    dsimp only [st']
    have hti : (st.core.trl.set st.core.trail_end ot)[i]? = st.core.trl[i]? :=
      List.getElem?_set_ne (by omega)
    rw [hti, List.getElem?_set_ne (Ne.symm (hmiss i hi_te))]
    exact hseg.2.1 i hi
  · dsimp only [st'] at hi2 ⊢
    by_cases he : i = st.core.trail_end
    · subst he
      rw [List.getElem?_set_self hte_trl, Option.getD_some]
      refine ⟨by rw [List.getElem?_set_self hv_lvl, Option.getD_some]; exact hlv_eq, fun _ => ?_⟩
      rw [List.getElem?_set_self hv_rsn, Option.getD_some]
      obtain ⟨hbf, hm7⟩ := bb_mask7f_or_bin not_lit
      have hm7_nat : (rsn &&& 0x7FFFFFFF#32).toNat = not_lit.toNat := by
        dsimp only [rsn]; rw [hm7]; exact bb_mask7f_eq_of_lt (by omega)
      refine ⟨hbf, by rw [hm7_nat, hcv_eq]; exact hnl_lt, by rw [hm7_nat]; exact hent,
        idx_p, hidx_ge, hidx_lt, by rw [hm7_nat, List.getElem?_set_ne (by omega)]; exact hidx_eq⟩
    · have hi_te : i < st.core.trail_end := by omega
      rw [List.getElem?_set_ne (Ne.symm he), List.getElem?_set_ne (Ne.symm (hmiss i hi_te))]
      obtain ⟨hlv_i, hrsn_i⟩ := hseg.2.2 i hi1 hi_te
      refine ⟨hlv_i, fun hgt => ?_⟩
      rw [List.getElem?_set_ne (Ne.symm (hmiss i hi_te))]
      obtain ⟨hbf, hnq, hent_i, m, hm1, hm2, hmeq⟩ := hrsn_i hgt
      exact ⟨hbf, hnq, hent_i, m, hm1, hm2, by rw [List.getElem?_set_ne (by omega)]; exact hmeq⟩
private theorem bb_probeSeg_with_confl_asz {F_cur : List (List Nat)} {st : FullState}
    {saved target_lvl : Nat} (hseg : BackboneProbeSeg F_cur st saved target_lvl)
    (c0' c1' asz' : BitVec 64) :
    BackboneProbeSeg F_cur
      { st with core := { st.core with confl_lit0 := c0', confl_lit1 := c1' }
                scratch := { st.scratch with ant_sz := asz' } } saved target_lvl := hseg

/-- `full_backbone_prop_m6` satisfies `fullBackbonePropM6Spec`. -/
theorem full_backbone_prop_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackbonePropM6Spec a m Q X →
      Func.wp Γ full_backbone_prop_m6_body a m Q X := by
  rintro ⟨h, prop_start, stop_early, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, st, saved0, max_lvl, R, rfl, hsp0, hbt0, hs0_le, hps_le, hmode, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hsp0.1.core_ok.cur_vars_le
  have hcl0 := hbt0.len_ok.core_ok
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt0.same_core]
  have hmw : WatchesInv F_cur s0.core := by
    have h := hsp0.2.1.watches
    simp only [ModeWatchesInv, hsp0.2.2.2.2.2, ↓reduceIte] at h
    exact h
  have hwl_le : s0.core.wlen ≤ c.wcap := hsp0.1.core_ok.wlen_le
  have hcl_lt32 : st.core.cur_level < 2 ^ 32 := by
    rcases hmode with ⟨hc0, _⟩ | ⟨_, sv, _, _, hsg⟩
    · omega
    · have := (hsg.2.2 sv (Nat.le_refl _) hsg.1).1
      have hlt : (st.core.lvl[(st.core.trl[sv]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < 2 ^ 32 :=
        BitVec.isLt _
      omega
  have hcl_tr : ((BitVec.ofNat 64 st.core.cur_level).truncate 32).toNat = st.core.cur_level := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : st.core.cur_level < 2 ^ 64), Nat.mod_eq_of_lt hcl_lt32]
  have hnlits_eq :
      ((BitVec.ofNat 64 st.core.cur_vars) <<< (BitVec.signExtend 64 1#32)).toNat =
        2 * s0.core.cur_vars := by
    rw [hcv_st,
      bb_bv64_shl1_sext _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Func.wp full_backbone_prop_m6_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64])
    (fun (tk, prop, ()) m1 =>
      ∃ (vals1 : List (BitVec 8)) (lvl1 rsns1 trl1 : List (BitVec 32)) (te1 : Nat)
        (c01 c11 asz1 : BitVec 64),
        let st1 : FullState :=
          { st with
            core := { st.core with
              vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1, trail_end := te1,
              confl_lit0 := c01, confl_lit1 := c11 }
            scratch := { st.scratch with ant_sz := asz1 } }
        BbTrailInv c F0 F_cur s0 st1 saved0 max_lvl ∧
        prop_start.toNat ≤ prop.toNat ∧ prop.toNat ≤ te1 ∧ st.core.trail_end ≤ te1 ∧
        (∀ i < st.core.trail_end, trl1[i]? = st.core.trl[i]?) ∧
        (∀ i < st.core.trail_end,
          let v := (st.core.trl[i]?.getD 0#32).toNat / 2
          lvl1[v]? = st.core.lvl[v]? ∧ rsns1[v]? = st.core.rsns[v]?) ∧
        (st.core.cur_level = 0 → ∀ i, prop_start.toNat ≤ i → i < te1 →
          (lvl1[(trl1[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0) ∧
        (∀ saved, saved0 ≤ saved → saved ≤ prop_start.toNat → 0 < st.core.cur_level →
          BackboneProbeSeg F_cur st saved st.core.cur_level →
          BackboneProbeSeg F_cur st1 saved st.core.cur_level) ∧
        (FullMem c st1 ⋆ R) m1)
    (fun (_, prop, ()) _ => c.max_vars - prop.toNat) ?_ ?_
  · intro J1 hJ1; fvt_steps
    exact hJ1 (st.scratch.ant_sz, prop_start, ()) m0
      ⟨st.core.vals, st.core.lvl, st.core.rsns, st.core.trl, st.core.trail_end,
       st.core.confl_lit0, st.core.confl_lit1, st.scratch.ant_sz, hbt0, Nat.le_refl _, hps_le,
       Nat.le_refl _, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩,
       fun hc0 => hmode.elim (fun h => h.2) (fun h => by omega),
       fun _ _ _ _ hsg => hsg, hm0⟩
  · rintro J1 ⟨tk, prop, ⟨⟩⟩ m1
      ⟨vals1, lvl1, rsns1, trl1, te1, c01, c11, asz1, hbt1, hps1, hp_le, hte_ge, htrl_pre,
       hlvl_pre, hl0_1, hseg_1, hm1⟩ ih1
    let st1 : FullState :=
      { st with
        core := { st.core with
          vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1, trail_end := te1,
          confl_lit0 := c01, confl_lit1 := c11 }
        scratch := { st.scratch with ant_sz := asz1 } }
    have hcv_st1 : st1.core.cur_vars = s0.core.cur_vars := by rw [hbt1.same_core]
    have hte1_le : te1 ≤ c.max_vars :=
      Nat.le_trans hbt1.len_ok.core_ok.trail_end_le (by rw [hcv_st1]; omega)
    refine wp_join_group (ts := [])
      (fun _ m_ex => ∃ (vals2 : List (BitVec 8)) (lvl2 rsns2 trl2 : List (BitVec 32)) (te2 : Nat)
        (c02 c12 asz2 : BitVec 64),
        let st2 : FullState :=
          { st with
            core := { st.core with
              vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2, trail_end := te2,
              confl_lit0 := c02, confl_lit1 := c12 }
            scratch := { st.scratch with ant_sz := asz2 } }
        BbTrailInv c F0 F_cur s0 st2 saved0 max_lvl ∧ st.core.trail_end ≤ te2 ∧
        (∀ i < st.core.trail_end, trl2[i]? = st.core.trl[i]?) ∧
        (∀ i < st.core.trail_end,
          let v := (st.core.trl[i]?.getD 0#32).toNat / 2
          lvl2[v]? = st.core.lvl[v]? ∧ rsns2[v]? = st.core.rsns[v]?) ∧
        (∀ saved, saved0 ≤ saved → saved ≤ prop_start.toNat → 0 < st.core.cur_level →
          BackboneProbeSeg F_cur st saved st.core.cur_level →
          BackboneProbeSeg F_cur st2 saved st.core.cur_level) ∧
        (FullMem c st2 ⋆ R) m_ex)
      (fun _ _ m_ex ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hbt2, hte2, htp2, hlp2,
          hsg2, hm_ex⟩ => by
        c0_hsteps
        exact hQ true vals2 lvl2 rsns2 trl2 te2 c02 c12 tk _
          (BbTrailInv.with_ant_sz hbt2 tk) hte2 htp2 hlp2
          (fun sv hs1 hs2 hc hsg => bb_probeSeg_with_confl_asz (hsg2 sv hs1 hs2 hc hsg) c02 c12 tk)
          (fun h => by cases h) (by assumption))
      (fun Jex hJex => ?_)
    c0_hsplit
    · have hp_lt : prop.toNat < te1 := by
        have h1 : prop.toNat < te1 % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt (by omega)] at h1
      c0_hsplit
      · have hp1 : (prop + 1#64).toNat = prop.toNat + 1 := by bv_omega
        have hp_trl : prop.toNat < trl1.length := by
          have : trl1.length = c.max_vars := hbt1.len_ok.core_ok.trl_len; omega
        let lit := trl1[prop.toNat]'hp_trl
        let not_lit := lit ^^^ 1#32
        have hlit_get : (trl1[prop.toNat]?.getD 0#32) = lit := by
          rw [List.getElem?_eq_getElem hp_trl, Option.getD_some]
        have hlit_lt : lit.toNat < 2 * s0.core.cur_vars := by
          have := hbt1.trl_lits_lt prop.toNat hp_lt; rwa [hlit_get] at this
        have hnl_eq : not_lit.toNat = lit.toNat ^^^ 1 := bb_bv32_xor1 lit
        have hnl_lt : not_lit.toNat < 2 * s0.core.cur_vars := by
          rw [hnl_eq]; exact litNeg_lt_two_mul hlit_lt
        have hwv_eq : st1.core.wvec = s0.core.wvec := by rw [hbt1.same_core]
        have hws_eq : st1.core.wstk = s0.core.wstk := by rw [hbt1.same_core]
        have hwv_len : st1.core.wvec.length = 4 * c.max_vars := hbt1.len_ok.core_ok.wvec_len
        have hnl_64 : (not_lit.setWidth 64).toNat = not_lit.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have hnl_w0 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat := by
          rw [bb_bv64_shl1_nat _ (by rw [hnl_64]; omega), hnl_64]
        have hnl_w1 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
            2 * not_lit.toNat + 1 := by
          rw [BitVec.toNat_add, hnl_w0, show (1#64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hnl_w0_lt : (BitVec.setWidth 64 (trl1[prop.toNat]'hp_trl ^^^ 1) <<< 1).toNat <
            st1.core.wvec.length := by
          change (not_lit.setWidth 64 <<< (1 : Nat)).toNat < st1.core.wvec.length; omega
        have hnl_w1_lt : ((BitVec.setWidth 64 (trl1[prop.toNat]'hp_trl ^^^ 1) <<< 1) + 1#64).toNat <
            st1.core.wvec.length := by
          change ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < st1.core.wvec.length; omega
        have hbd_nl := hmw.layout.bounds not_lit.toNat hnl_lt
        have hslice0 := hmw.slices not_lit.toNat hnl_lt
        let off_n := fullWatchOffCore s0.core not_lit.toNat
        let sz_n := fullWatchSizeCore s0.core not_lit.toNat
        have hend_bd : off_n + sz_n ≤ c.wcap := Nat.le_trans hbd_nl hwl_le
        have hoff_eq :
            (st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).toNat =
              off_n := by
          unfold off_n fullWatchOffCore
          have hg : st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega) =
              s0.core.wvec[2 * not_lit.toNat]?.getD 0#32 := by
            rw [← hwv_eq, ← hnl_w0, List.getElem?_eq_getElem (by omega), Option.getD_some]
          rw [hg]
        have hsz_eq :
            (st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by omega)).toNat =
              sz_n := by
          unfold sz_n fullWatchSizeCore
          have hg : st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by omega) =
              s0.core.wvec[2 * not_lit.toNat + 1]?.getD 0#32 := by
            rw [← hwv_eq, ← hnl_w1, List.getElem?_eq_getElem (by omega), Option.getD_some]
          rw [hg]
        have hoff_64 :
            (st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 =
              BitVec.ofNat 64 off_n :=
          BitVec.eq_of_toNat_eq (by
            rw [BitVec.toNat_setWidth, hoff_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega)])
        have hsz_64 :
            (st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by
              omega)).setWidth 64 = BitVec.ofNat 64 sz_n :=
          BitVec.eq_of_toNat_eq (by
            rw [BitVec.toNat_setWidth, hsz_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega)])
        have hend_64 :
            ((st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 +
             (st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by
              omega)).setWidth 64).toNat = off_n + sz_n := by
          rw [hoff_64, hsz_64, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        c0_hsteps_nogrp
        -- Inner break join `Js` (`[i64, i64]`) -> next outer iteration `(tk_out, prop + 1)`
        refine wp_join_group (ts := [i64, i64])
          (fun (tk_o, _, ()) m_o =>
            ∃ (vals2 : List (BitVec 8)) (lvl2 rsns2 trl2 : List (BitVec 32)) (te2 : Nat)
              (c02 c12 asz2 : BitVec 64),
              let st2 : FullState :=
                { st with
                  core := { st.core with
                    vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2, trail_end := te2,
                    confl_lit0 := c02, confl_lit1 := c12 }
                  scratch := { st.scratch with ant_sz := asz2 } }
              BbTrailInv c F0 F_cur s0 st2 saved0 max_lvl ∧
              prop.toNat + 1 ≤ te2 ∧ st.core.trail_end ≤ te2 ∧
              (∀ i < st.core.trail_end, trl2[i]? = st.core.trl[i]?) ∧
              (∀ i < st.core.trail_end,
                let v := (st.core.trl[i]?.getD 0#32).toNat / 2
                lvl2[v]? = st.core.lvl[v]? ∧ rsns2[v]? = st.core.rsns[v]?) ∧
              (st.core.cur_level = 0 → ∀ i, prop_start.toNat ≤ i → i < te2 →
                (lvl2[(trl2[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0) ∧
              (∀ saved, saved0 ≤ saved → saved ≤ prop_start.toNat → 0 < st.core.cur_level →
                BackboneProbeSeg F_cur st saved st.core.cur_level →
                BackboneProbeSeg F_cur st2 saved st.core.cur_level) ∧
              (FullMem c st2 ⋆ R) m_o)
          (fun _ ⟨tk_o, _, ⟨⟩⟩ m_o
              ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hbt2, hp_le2, hte2, htp2, hlp2,
               hl0_2, hsg2, hm_o⟩ => by
            c0_hsteps
            exact ih1 (tk_o, prop + 1#64, ()) m_o (by dsimp only; omega)
              ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hbt2, by omega, by omega, hte2,
               htp2, hlp2, hl0_2, hsg2, hm_o⟩)
          (fun Jb hJb => ?_)
        refine wp_loop_inv (ts := [i64, i64])
          (fun (tk2, q, ()) m2 =>
            ∃ (vals2 : List (BitVec 8)) (lvl2 rsns2 trl2 : List (BitVec 32)) (te2 : Nat)
              (c02 c12 asz2 : BitVec 64),
              let st2 : FullState :=
                { st with
                  core := { st.core with
                    vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2, trail_end := te2,
                    confl_lit0 := c02, confl_lit1 := c12 }
                  scratch := { st.scratch with ant_sz := asz2 } }
              BbTrailInv c F0 F_cur s0 st2 saved0 max_lvl ∧
              off_n ≤ q.toNat ∧ q.toNat ≤ off_n + sz_n ∧
              WatchSliceOk F_cur s0.core not_lit.toNat q.toNat (off_n + sz_n - q.toNat) ∧
              te1 ≤ te2 ∧ (∀ i < te1, trl2[i]? = trl1[i]?) ∧
              st.core.trail_end ≤ te2 ∧
              (∀ i < st.core.trail_end, trl2[i]? = st.core.trl[i]?) ∧
              (∀ i < st.core.trail_end,
                let v := (st.core.trl[i]?.getD 0#32).toNat / 2
                lvl2[v]? = st.core.lvl[v]? ∧ rsns2[v]? = st.core.rsns[v]?) ∧
              (st.core.cur_level = 0 → ∀ i, prop_start.toNat ≤ i → i < te2 →
                (lvl2[(trl2[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0) ∧
              (∀ saved, saved0 ≤ saved → saved ≤ prop_start.toNat → 0 < st.core.cur_level →
                BackboneProbeSeg F_cur st saved st.core.cur_level →
                BackboneProbeSeg F_cur st2 saved st.core.cur_level) ∧
              (FullMem c st2 ⋆ R) m2)
          (fun (_, q, ()) _ => off_n + sz_n - q.toNat) ?_ ?_
        · intro J2 hJ2; c0_hsteps
          have hq0 : ((st.core.wvec[((trl1[prop.toNat]'hp_trl ^^^ 1).setWidth 64 <<<
              1).toNat]'(by omega)).setWidth 64).toNat = off_n := by
            have h1 : ((st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
                omega)).setWidth 64).toNat = off_n := by
              rw [hoff_64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            exact h1
          exact hJ2 (tk - 1#64, _, ()) m1
            ⟨vals1, lvl1, rsns1, trl1, te1, c01, c11, asz1, hbt1,
             by dsimp only; rw [hq0]; omega, by dsimp only; rw [hq0]; omega,
             by dsimp only; rw [hq0, Nat.add_sub_cancel_left]; exact hslice0,
             Nat.le_refl _, fun _ _ => rfl, hte_ge, htrl_pre, hlvl_pre, hl0_1, hseg_1, hm1⟩
        · rintro J2 ⟨tk2, q, ⟨⟩⟩ m2
            ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hbt2, hq_ge, hq_le, hslice_q,
             hte12, htrl12, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩ ih2
          let st2 : FullState :=
            { st with
              core := { st.core with
                vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2, trail_end := te2,
                confl_lit0 := c02, confl_lit1 := c12 }
              scratch := { st.scratch with ant_sz := asz2 } }
          have hcv_st2 : st2.core.cur_vars = s0.core.cur_vars := by rw [hbt2.same_core]
          have hte2_le : te2 ≤ c.max_vars :=
            Nat.le_trans hbt2.len_ok.core_ok.trail_end_le (by rw [hcv_st2]; omega)
          c0_hsplit
          · have hq_lt : q.toNat < off_n + sz_n := by
              have hend_raw :
                  ((st.core.wvec[((trl1[prop.toNat]'hp_trl ^^^ 1).setWidth 64 <<<
                      1).toNat]'(by omega)).setWidth 64 +
                   (st.core.wvec[(((trl1[prop.toNat]'hp_trl ^^^ 1).setWidth 64 <<<
                      1) + 1).toNat]'(by omega)).setWidth 64).toNat = off_n + sz_n := hend_64
              have h1 : q.toNat < ((st.core.wvec[((trl1[prop.toNat]'hp_trl ^^^ 1).setWidth 64 <<<
                  1).toNat]'(by omega)).setWidth 64 +
                (st.core.wvec[(((trl1[prop.toNat]'hp_trl ^^^ 1).setWidth 64 <<<
                  1) + 1).toNat]'(by omega)).setWidth 64).toNat := by c0_bound
              rwa [hend_raw] at h1
            have hq_ws : q.toNat < st2.core.wstk.length := by
              have : st2.core.wstk.length = c.wcap := hbt2.len_ok.core_ok.wstk_len_arr; omega
            let qw := st2.core.wstk[q.toNat]'hq_ws
            have hqw_s0 : s0.core.wstk[q.toNat]? = some qw := by
              have hws2 : st2.core.wstk = s0.core.wstk := by rw [hbt2.same_core]
              rw [← hws2, List.getElem?_eq_getElem hq_ws]
            c0_hsplit
            · -- Large watch `(qw & PW_BIN_FLAG) == 0`
              have hlg_f : (qw &&& 0x80000000#32) = 0#32 := by c0_bound
              obtain ⟨hrem2, _, _, _, _, hslice_2⟩ :=
                FullTransHelpers.watchSlice_inv_large hslice_q (by omega) hqw_s0 hlg_f
              c0_hsplit
              · -- `stop_early = true`: break out of inner loop
                c0_hsteps
                exact hJb (tk2, q, ()) m2
                  ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hbt2, by omega, hte2, htp2,
                   hlp2, hl0_2, hsg2, hm2⟩
              · -- `stop_early = false`: `q += 2`, optional ticks decr, continue
                have hq2 : (q + 2#64).toNat = q.toNat + 2 := by bv_omega
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64]) (fun _ mt => mt = m2)
                  (fun _ ⟨tk_n, ⟨⟩⟩ mt heq => by
                    subst heq; c0_hsteps
                    exact ih2 (tk_n, q + 2#64, ()) mt (by dsimp only; omega)
                      ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hbt2, by omega, by omega,
                       by simpa [hq2, show off_n + sz_n - (q.toNat + 2) =
                         off_n + sz_n - q.toNat - 2 by omega] using hslice_2,
                       hte12, htrl12, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩)
                  (fun Jtk hJtk => by c0_hsteps <;> exact hJtk _ _ rfl)
            · -- Binary watch `(qw & PW_BIN_FLAG) ≠ 0`
              have hbf : (qw &&& 0x80000000#32) ≠ 0#32 := by c0_bound
              obtain ⟨_, hot_lt, hent_bin, hslice_1⟩ :=
                FullTransHelpers.watchSlice_inv_bin hslice_q (by omega) hqw_s0 hbf
              have hq1 : (q + 1#64).toNat = q.toNat + 1 := by bv_omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ mt => mt = m2)
                (fun _ ⟨tk_n, ⟨⟩⟩ mt heq => by
                  subst heq
                  let ot := qw &&& 0x7FFFFFFF#32
                  have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
                  have hot_v : ot.toNat < vals2.length := by
                    have : vals2.length = 2 * c.max_vars := hbt2.len_ok.core_ok.vals_len; omega
                  have hot_not_lt : ot.toNat ^^^ 1 < 2 * s0.core.cur_vars :=
                    litNeg_lt_two_mul hot_lt'
                  have hot_not_v : (ot ^^^ 1#32).toNat < (vals2.set ot.toNat 1#8).length := by
                    rw [List.length_set, bb_bv32_xor1]
                    have : vals2.length = 2 * c.max_vars := hbt2.len_ok.core_ok.vals_len; omega
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [])
                    (fun _ m3 =>
                      ∃ (vals3 : List (BitVec 8)) (lvl3 rsns3 trl3 : List (BitVec 32)) (te3 : Nat)
                        (c03 c13 asz3 : BitVec 64),
                        let st3 : FullState :=
                          { st with
                            core := { st.core with
                              vals := vals3, lvl := lvl3, rsns := rsns3, trl := trl3,
                              trail_end := te3, confl_lit0 := c03, confl_lit1 := c13 }
                            scratch := { st.scratch with ant_sz := asz3 } }
                        BbTrailInv c F0 F_cur s0 st3 saved0 max_lvl ∧
                        te1 ≤ te3 ∧ (∀ i < te1, trl3[i]? = trl1[i]?) ∧
                        st.core.trail_end ≤ te3 ∧
                        (∀ i < st.core.trail_end, trl3[i]? = st.core.trl[i]?) ∧
                        (∀ i < st.core.trail_end,
                          let v := (st.core.trl[i]?.getD 0#32).toNat / 2
                          lvl3[v]? = st.core.lvl[v]? ∧ rsns3[v]? = st.core.rsns[v]?) ∧
                        (st.core.cur_level = 0 → ∀ i, prop_start.toNat ≤ i → i < te3 →
                          (lvl3[(trl3[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0) ∧
                        (∀ saved, saved0 ≤ saved → saved ≤ prop_start.toNat →
                          0 < st.core.cur_level →
                          BackboneProbeSeg F_cur st saved st.core.cur_level →
                          BackboneProbeSeg F_cur st3 saved st.core.cur_level) ∧
                        (FullMem c st3 ⋆ R) m3)
                    (fun _ _ m3
                        ⟨vals3, lvl3, rsns3, trl3, te3, c03, c13, asz3, hbt3, hte13, htrl13,
                         hte3, htp3, hlp3, hl0_3, hsg3, hm3⟩ => by
                      c0_hsteps
                      exact ih2 (tk_n, q + 1#64, ()) m3 (by dsimp only; omega)
                        ⟨vals3, lvl3, rsns3, trl3, te3, c03, c13, asz3, hbt3, by omega, by omega,
                         by simpa [hq1, show off_n + sz_n - (q.toNat + 1) =
                           off_n + sz_n - q.toNat - 1 by omega] using hslice_1,
                         hte13, htrl13, hte3, htp3, hlp3, hl0_3, hsg3, hm3⟩)
                    (fun Jc hJc => by
                      have hot_dom := hbt2.vals_dom ot.toNat hot_lt'
                      rw [List.getElem?_eq_getElem hot_v, Option.getD_some] at hot_dom
                      c0_hsplit
                      · c0_hsplit
                        · -- Conflict: `vals[ot] < 0` (`0xFF#8`)
                          have hot_ff : vals2[ot.toNat]?.getD 0#8 = 0xFF#8 := by
                            rw [List.getElem?_eq_getElem hot_v, Option.getD_some]
                            exact (bb_bv8_dom_slt0 hot_dom).mp hc
                          have hnl_ff : vals2[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
                            have hv := (hbt2.trl_vals_ok prop.toNat (by dsimp only [st2]; omega)).2
                            rw [htrl12 prop.toNat hp_lt, hlit_get] at hv
                            rwa [hnl_eq]
                          c0_hsteps
                          have hst_cf :=
                            BbTrailInv.with_confl_asz hbt2 (not_lit.setWidth 64)
                              (ot.setWidth 64) tk_n
                          refine hQ false vals2 lvl2 rsns2 trl2 te2
                            (not_lit.setWidth 64) (ot.setWidth 64) tk_n _ hst_cf hte2 htp2 hlp2
                            (fun sv hs1 hs2 hc hsg => bb_probeSeg_with_confl_asz
                              (hsg2 sv hs1 hs2 hc hsg) _ _ _)
                            (fun _ => ?_) (by assumption)
                          have hnl64 : (not_lit.setWidth 64).toNat = not_lit.toNat := by bv_omega
                          have hot64 : (ot.setWidth 64).toNat = ot.toNat := by bv_omega
                          refine ⟨by rw [hnl64]; exact hnl_lt, by rw [hot64]; exact hot_lt',
                            by rw [hnl64]; exact hnl_ff, by rw [hot64]; exact hot_ff,
                            by rw [hnl64, hot64]; exact hent_bin, prop.toNat, hps1, by omega, ?_⟩
                          rw [htrl12 prop.toNat hp_lt, hlit_get, hnl64, hnl_eq, bb_xor1_xor1]
                        · refine wp_unroll_group fun Jn hJn => ?_
                          c0_hsplit
                          · -- Unassigned `vals[ot] == 0`
                            have hot_z : vals2[ot.toNat]?.getD 0#8 = 0#8 := by
                              rw [List.getElem?_eq_getElem hot_v, Option.getD_some]
                              exact (bb_bv8_sext32_eq0 _).mp hc
                            c0_hsplit
                            · -- `te2 < max_vars`: push `ot` onto trail
                              have hte2_lt : te2 < c.max_vars := by
                                have h1 : te2 % 2 ^ 64 < c.max_vars % 2 ^ 64 := by c0_bound
                                rwa [Nat.mod_eq_of_lt (by omega),
                                  Nat.mod_eq_of_lt (by omega)] at h1
                              have hte2_trl : te2 < trl2.length := by
                                have : trl2.length = c.max_vars := hbt2.len_ok.core_ok.trl_len
                                omega
                              have hte2_bv : (BitVec.ofNat 64 te2).toNat = te2 := by
                                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                              have hot64 : (ot.setWidth 64).toNat = ot.toNat :=
                                FullTransHelpers.ft_bv32_setWidth64 ot
                              have hotn64 : ((ot ^^^ 1).setWidth 64).toNat = ot.toNat ^^^ 1 := by
                                rw [FullTransHelpers.ft_bv32_setWidth64]; exact bb_bv32_xor1 ot
                              have hotr64 : ((ot >>> 1).setWidth 64).toNat = ot.toNat / 2 := by
                                rw [FullTransHelpers.ft_bv32_setWidth64]
                                simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                              have hot_v2 : (ot >>> 1).toNat < lvl2.length := by
                                have : lvl2.length = c.max_vars := hbt2.len_ok.core_ok.lvl_len
                                simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
                              have hot_r2 : (ot >>> 1).toNat < rsns2.length := by
                                have : rsns2.length = c.max_vars := hbt2.len_ok.core_ok.rsns_len
                                simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
                              have hte2_add : (BitVec.ofNat 64 te2 + 1).toNat = te2 + 1 := by
                                rw [BitVec.toNat_add, hte2_bv, show (1 : BitVec 64).toNat = 1 from
                                  rfl, Nat.mod_eq_of_lt (by omega)]
                              have hmiss2 := hbt2.var_unassigned hot_lt' hot_z
                              let rsn_b := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
                              have hl0_ent :
                                  ((BitVec.ofNat 64 st.core.cur_level).truncate 32).toNat = 0 →
                                  (cnfOfClauses F_cur).EntailsClause (cnfClause [ot.toNat]) := by
                                intro hc0'
                                rw [hcl_tr] at hc0'
                                have hlv_p : (lvl2[(trl2[prop.toNat]?.getD 0#32).toNat / 2]?.getD
                                    0#32).toNat = 0 := hl0_2 hc0' prop.toNat hps1 (by omega)
                                have hlit_ent :=
                                  hbt2.l0_entails prop.toNat (by dsimp only [st2]; omega) hlv_p
                                rw [htrl12 prop.toNat hp_lt, hlit_get] at hlit_ent
                                exact backbone_resolve_l0 (bb_entails_comm2 hent_bin)
                                  (by rw [hnl_eq, bb_xor1_xor1]; exact hlit_ent)
                              have hbt3 := BbTrailInv.push hbt2 (Nat.le_refl _) (lit := ot)
                                (rsn := rsn_b)
                                (lv_bv := (BitVec.ofNat 64 st.core.cur_level).truncate 32)
                                (cl' := st.core.cur_level) hot_lt' hot_z hte2_lt
                                (by rw [hcl_tr]; exact hbt2.cur_le_max) hbt2.cur_le_max hl0_ent
                              c0_hsteps
                              refine hJc () _ ⟨_, _, _, _, te2 + 1, c02, c12, asz2, hbt3,
                                by omega, fun i hi => by
                                  rw [List.getElem?_set_ne (by dsimp only [st2]; omega)]
                                  exact htrl12 i hi,
                                by omega, fun i hi => by
                                  rw [List.getElem?_set_ne (by dsimp only [st2]; omega)]
                                  exact htp2 i hi,
                                fun i hi => by
                                  have hne_v : (st.core.trl[i]?.getD 0#32).toNat / 2 ≠
                                      ot.toNat / 2 := by
                                    rw [← htp2 i hi]; exact hmiss2 i (by dsimp only [st2]; omega)
                                  dsimp only
                                  rw [List.getElem?_set_ne hne_v.symm,
                                    List.getElem?_set_ne hne_v.symm]
                                  exact hlp2 i hi,
                                fun hc0' i hi1 hi2 => by
                                  by_cases he : i = te2
                                  · subst he
                                    rw [List.getElem?_set_self hte2_trl, Option.getD_some,
                                      List.getElem?_set_self (by
                                        rw [hbt2.len_ok.core_ok.lvl_len]; omega), Option.getD_some,
                                      hcl_tr, hc0']
                                  · rw [List.getElem?_set_ne (Ne.symm he),
                                      List.getElem?_set_ne (Ne.symm (hmiss2 i
                                        (by dsimp only [st2]; omega)))]
                                    exact hl0_2 hc0' i hi1 (by omega),
                                fun sv hs1 hs2 hc hsg =>
                                  bb_probeSeg_push hbt2 (hsg2 sv hs1 hs2 hc hsg) hot_lt' hot_z
                                    hte2_lt hcl_tr hnl_lt (bb_entails_comm2 hent_bin)
                                    (by omega : sv ≤ prop.toNat)
                                    (by dsimp only [st2]; omega : prop.toNat < st2.core.trail_end)
                                    (by dsimp only [st2]; rw [htrl12 prop.toNat hp_lt, hlit_get,
                                      hnl_eq, bb_xor1_xor1]), ?_⟩
                              refine bb_fullMem_eq ?_ (by assumption)
                              dsimp only [st2, ot, qw, rsn_b, not_lit]
                              rw [FullTransHelpers.ft_bv32_setWidth64,
                                FullTransHelpers.ft_bv32_setWidth64,
                                FullTransHelpers.ft_bv32_setWidth64, hte2_bv, hte2_add]
                              simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                              rw [show ((st.core.wstk[q.toNat]'hq_ws &&& 2147483647) ^^^ 1).toNat =
                                (st.core.wstk[q.toNat]'hq_ws &&& 2147483647).toNat ^^^ 1 from
                                bb_bv32_xor1 _]; rfl
                            · c0_hsteps
                              exact hJc () mt ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2,
                                hbt2, hte12, htrl12, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
                          · c0_hsteps
                            exact hJc () mt ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2,
                              hbt2, hte12, htrl12, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
                      · c0_hsteps
                        exact hJc () mt ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2,
                          hbt2, hte12, htrl12, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩))
                (fun Jtk hJtk => by c0_hsteps <;> exact hJtk _ _ rfl)
          · c0_hsteps
            exact hJb (tk2, q, ()) m2
              ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hbt2, by omega, hte2, htp2, hlp2,
               hl0_2, hsg2, hm2⟩
      · c0_hsteps
        exact hJex () m1 ⟨vals1, lvl1, rsns1, trl1, te1, c01, c11, asz1, hbt1, hte_ge, htrl_pre,
          hlvl_pre, hseg_1, hm1⟩
    · c0_hsteps
      exact hJex () m1 ⟨vals1, lvl1, rsns1, trl1, te1, c01, c11, asz1, hbt1, hte_ge, htrl_pre,
        hlvl_pre, hseg_1, hm1⟩

/-- `full_backbone_analyze_m6` satisfies `fullBackboneAnalyzeM6Spec`. -/
theorem full_backbone_analyze_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackboneAnalyzeM6Spec a m Q X →
      Func.wp Γ full_backbone_analyze_m6_body a m Q X := by
  rintro ⟨h, c0, c1, saved, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, st, saved0, max_lvl, R, rfl, hsp0, hbt, hcl_pos, hs0_le, hlvl_lt, hseg,
     hc0_lt, hc1_lt, hc0_ff, hc1_ff, hent_c, ⟨idx0, hidx0_ge, hidx0_lt, hidx0_eq⟩, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hbt.len_ok.core_ok
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_st ▸ hcl.cur_vars_le
  have hte_le : st.core.trail_end ≤ c.max_vars := Nat.le_trans hcl.trail_end_le (by omega)
  have hmrk0 : FullMrkZero c st := by
    have hm_eq : st.core.mrk = s0.core.mrk := by rw [hbt.same_core]
    exact fun v hv => by rw [hm_eq]; exact hsp0.2.2.1.1 v hv
  have hc0v : (c0 >>> 1#32).toNat < c.max_vars := by rw [bb_bv32_lshr1]; omega
  have hc1v : (c1 >>> 1#32).toNat < c.max_vars := by rw [bb_bv32_lshr1]; omega
  have hc1_lvl : (c1 >>> 1#32).toNat < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hc0_mrk : (c0 >>> 1#32).toNat < st.core.mrk.length := by rw [hcl.mrk_len]; omega
  have hc1_mrk : (c1 >>> 1#32).toNat < st.core.mrk.length := by rw [hcl.mrk_len]; omega
  obtain ⟨idx1, hidx1_lt, hidx1_eq⟩ := hbt.vals_false_trl c1.toNat hc1_lt hc1_ff
  unfold Func.wp full_backbone_analyze_m6_body
  fvt_step; fvt_step; fvt_step; fvt_step; fvt_step; fvt_step; fvt_step
  · -- `lv1 == 0`: return `c0 ^ 1` via `backbone_resolve_l0`
    have hlv1_0 : (st.core.lvl[c1.toNat / 2]?.getD 0#32).toNat = 0 := by
      rw [List.getElem?_eq_getElem (by rw [hcl.lvl_len]; omega), Option.getD_some]
      have h1 : st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl = 0#32 := by c0_bound
      have heq : st.core.lvl[c1.toNat / 2]'(by rw [hcl.lvl_len]; omega) =
          st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl := by
        congr 1
      rw [heq, h1]; rfl
    have hc1_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [c1.toNat ^^^ 1]) := by
      have h := hbt.l0_entails idx1 hidx1_lt (by rw [hidx1_eq, fullInv_var_xor1]; exact hlv1_0)
      rwa [hidx1_eq] at h
    fvt_steps
    exact hQ (c0 ^^^ 1#32) st.core.mrk m0 hcl.mrk_len hmrk0 (fun _ =>
      ⟨by rw [bb_bv32_xor1]; exact litNeg_lt_two_mul hc0_lt,
       by rw [bb_bv32_xor1, bb_xor1_xor1]; exact backbone_resolve_l0 hent_c hc1_ent⟩) hm0
  · fvt_step; fvt_step
    · -- `(u64)lv1 != cur_level`: return `0xFFFFFFFF`
      fvt_steps
      exact hQ 0xFFFFFFFF#32 st.core.mrk m0 hcl.mrk_len hmrk0
        (fun h => absurd rfl h) hm0
    · have hlv1_eq : (st.core.lvl[c1.toNat / 2]?.getD 0#32).toNat = st.core.cur_level := by
        have h1 : (st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl).toNat =
            st.core.cur_level % 2 ^ 64 := by
          have h2 : (st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl).setWidth 64 =
              BitVec.ofNat 64 st.core.cur_level := by c0_bound
          have h3 := congrArg BitVec.toNat h2
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
            have := BitVec.isLt (st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl); omega),
            BitVec.toNat_ofNat] at h3
          exact h3
        have hcl_64 : st.core.cur_level < 2 ^ 64 := by
          have := (hseg.2.2 saved.toNat (Nat.le_refl _) hseg.1).1
          have : (st.core.lvl[(st.core.trl[saved.toNat]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat < 2 ^ 32 := BitVec.isLt _
          omega
        rw [Nat.mod_eq_of_lt hcl_64] at h1
        rw [List.getElem?_eq_getElem (by rw [hcl.lvl_len]; omega), Option.getD_some]
        have heq : st.core.lvl[c1.toNat / 2]'(by rw [hcl.lvl_len]; omega) =
            st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl := by
          congr 1
        rw [heq]; exact h1
      have hidx1_ge : saved.toNat ≤ idx1 :=
        Classical.byContradiction fun hlt => by
          have h1 := hlvl_lt idx1 (by omega)
          rw [hidx1_eq, fullInv_var_xor1, hlv1_eq] at h1; omega
      fvt_step
      · -- `c0 == c1`: return `c0 ^ 1` via `backbone_collapse_eq`
        have hce : c0 = c1 := by c0_bound
        subst hce; fvt_steps
        exact hQ (c0 ^^^ 1#32) st.core.mrk m0 hcl.mrk_len hmrk0 (fun _ =>
          ⟨by rw [bb_bv32_xor1]; exact litNeg_lt_two_mul hc0_lt,
           by rw [bb_bv32_xor1, bb_xor1_xor1]; exact backbone_collapse_eq hent_c⟩) hm0
      · -- `c0 ≠ c1`: 2-literal 1UIP binary-reason resolution loop
        have hc_ne : c0 ≠ c1 := by c0_bound
        have hidx_ne : idx0 ≠ idx1 := fun he => by
          subst he
          have h1 := congrArg (· ^^^ 1) (hidx0_eq.symm.trans hidx1_eq)
          rw [bb_xor1_xor1, bb_xor1_xor1] at h1
          exact hc_ne (BitVec.eq_of_toNat_eq h1)
        have hv_ne : c0.toNat / 2 ≠ c1.toNat / 2 := fun he =>
          hidx_ne (hbt.trl_vars_nodup idx0 idx1 hidx0_lt hidx1_lt
            (by rw [hidx0_eq, hidx1_eq, fullInv_var_xor1, fullInv_var_xor1]; exact he))
        have hc0_mrk64 : (BitVec.setWidth 64 (c0 >>> 1)).toNat < st.core.mrk.length := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := BitVec.isLt (c0 >>> 1); omega)]
          exact hc0_mrk
        have hc1_mrk64 : (BitVec.setWidth 64 (c1 >>> 1)).toNat <
            (st.core.mrk.set (BitVec.setWidth 64 (c0 >>> 1)).toNat 1#8).length := by
          rw [List.length_set, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by have := BitVec.isLt (c1 >>> 1); omega)]
          exact hc1_mrk
        fvt_to_group
        -- Break join `Js` (`[i64]`): cleanup `mrk[trl[k] >> 1] = 0` for `k = saved ..< trail_end`
        refine wp_join_group (ts := [i64])
          (fun _ m_cl => ∃ mrk_c : List (BitVec 8), mrk_c.length = c.max_vars ∧
            (∀ v < c.max_vars, mrk_c[v]?.getD 0#8 ≠ 0#8 →
              ∃ i, saved.toNat ≤ i ∧ i < st.core.trail_end ∧
                (st.core.trl[i]?.getD 0#32).toNat / 2 = v) ∧
            (FullMem c { st with core := { st.core with mrk := mrk_c } } ⋆ R) m_cl)
          (fun _ _ m_cl ⟨mrk_c, hmc_len, hmc_dom, hm_cl⟩ => by
            fvt_to_group
            refine wp_loop_inv (ts := [i64])
              (fun (k, ()) mk => ∃ mrk_k : List (BitVec 8), mrk_k.length = c.max_vars ∧
                saved.toNat ≤ k.toNat ∧ k.toNat ≤ st.core.trail_end ∧
                (∀ v < c.max_vars, mrk_k[v]?.getD 0#8 ≠ 0#8 →
                  ∃ i, k.toNat ≤ i ∧ i < st.core.trail_end ∧
                    (st.core.trl[i]?.getD 0#32).toNat / 2 = v) ∧
                (FullMem c { st with core := { st.core with mrk := mrk_k } } ⋆ R) mk)
              (fun (k, ()) _ => st.core.trail_end - k.toNat) ?_ ?_
            · intro Jk hJk; fvt_steps
              exact hJk (saved, ()) m_cl ⟨mrk_c, hmc_len, Nat.le_refl _, by omega, hmc_dom, hm_cl⟩
            · rintro Jk ⟨k, ⟨⟩⟩ mk ⟨mrk_k, hmk_len, hk_ge, hk_le, hmk_dom, hmk⟩ ihk
              fvt_step; fvt_step; fvt_step
              · have hk_lt : k.toNat < st.core.trail_end := by
                  have h1 : k.toNat < st.core.trail_end % 2 ^ 64 := by c0_bound
                  rwa [Nat.mod_eq_of_lt (by omega)] at h1
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                have hk_trl : k.toNat < st.core.trl.length := by rw [hcl.trl_len]; omega
                let zk := st.core.trl[k.toNat]'hk_trl
                have hzk_lt : zk.toNat < 2 * s0.core.cur_vars := by
                  have := hbt.trl_lits_lt k.toNat hk_lt
                  rwa [List.getElem?_eq_getElem hk_trl, Option.getD_some] at this
                have hzk_mrk : (zk >>> 1#32).toNat < mrk_k.length := by
                  rw [bb_bv32_lshr1, hmk_len]; omega
                fvt_steps
                refine ihk (k + 1#64, ()) _ (by dsimp only; omega)
                  ⟨mrk_k.set (zk >>> 1#32).toNat 0#8, by simp [hmk_len], by omega, by omega,
                   fun v hv hnz => ?_, hm⟩
                have hv_ne_k : v ≠ (zk >>> 1#32).toNat := fun he => by
                  subst he; rw [List.getElem?_set_self hzk_mrk, Option.getD_some] at hnz
                  exact hnz rfl
                rw [List.getElem?_set_ne hv_ne_k.symm] at hnz
                obtain ⟨i, hi1, hi2, hieq⟩ := hmk_dom v hv hnz
                have hi_ne_k : i ≠ k.toNat := fun he => by
                  subst he; apply hv_ne_k
                  rw [bb_bv32_lshr1, ← hieq, List.getElem?_eq_getElem hk_trl, Option.getD_some]
                exact ⟨i, by omega, hi2, hieq⟩
              · have hk_eq : k.toNat = st.core.trail_end := by
                  have h1 : st.core.trail_end % 2 ^ 64 ≤ k.toNat := by c0_bound
                  rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
                fvt_steps
                refine hQ 0xFFFFFFFF#32 mrk_k mk hmk_len
                  (fun v hv => Classical.byContradiction fun hnz => by
                    obtain ⟨i, hi1, hi2, _⟩ := hmk_dom v hv hnz; omega)
                  (fun h => absurd rfl h) hmk)
          (fun Jbr hJbr => ?_)
        -- Main resolution loop `t = trail_end` down to `saved`
        refine wp_loop_inv (ts := [i64])
          (fun (t, ()) mt => ∃ mrk_t : List (BitVec 8), mrk_t.length = c.max_vars ∧
            saved.toNat ≤ t.toNat ∧ t.toNat ≤ st.core.trail_end ∧
            (∃ i1 i2, saved.toNat ≤ i1 ∧ i1 < i2 ∧ i2 < t.toNat ∧
              (∀ v < c.max_vars, mrk_t[v]?.getD 0#8 ≠ 0#8 ↔
                v = (st.core.trl[i1]?.getD 0#32).toNat / 2 ∨
                v = (st.core.trl[i2]?.getD 0#32).toNat / 2) ∧
              (cnfOfClauses F_cur).EntailsClause
                (cnfClause [(st.core.trl[i1]?.getD 0#32).toNat ^^^ 1,
                            (st.core.trl[i2]?.getD 0#32).toNat ^^^ 1])) ∧
            (FullMem c { st with core := { st.core with mrk := mrk_t } } ⋆ R) mt)
          (fun (t, ()) _ => t.toNat) ?_ ?_
        · intro Jt hJt; fvt_steps
          let mrk_init := (st.core.mrk.set (c0 >>> 1#32).toNat 1#8).set (c1 >>> 1#32).toNat 1#8
          have hmi_len : mrk_init.length = c.max_vars := by simp [mrk_init, hcl.mrk_len]
          have hmi_iff : ∀ v < c.max_vars,
              mrk_init[v]?.getD 0#8 ≠ 0#8 ↔ v = c0.toNat / 2 ∨ v = c1.toNat / 2 := fun v hv => by
            dsimp only [mrk_init]
            by_cases h1 : v = c1.toNat / 2
            · subst h1
              rw [show (c1 >>> 1#32).toNat = c1.toNat / 2 from bb_bv32_lshr1 c1,
                List.getElem?_set_self (by simp [hcl.mrk_len]; omega), Option.getD_some]
              exact ⟨fun _ => Or.inr rfl, fun _ => by decide⟩
            · rw [show (c1 >>> 1#32).toNat = c1.toNat / 2 from bb_bv32_lshr1 c1,
                List.getElem?_set_ne (Ne.symm h1)]
              by_cases h0 : v = c0.toNat / 2
              · subst h0
                rw [show (c0 >>> 1#32).toNat = c0.toNat / 2 from bb_bv32_lshr1 c0,
                  List.getElem?_set_self (by rw [hcl.mrk_len]; omega), Option.getD_some]
                exact ⟨fun _ => Or.inl rfl, fun _ => by decide⟩
              · rw [show (c0 >>> 1#32).toNat = c0.toNat / 2 from bb_bv32_lshr1 c0,
                  List.getElem?_set_ne (Ne.symm h0), hmrk0 v hv]
                exact ⟨fun h => absurd rfl h,
                  fun h => h.elim (fun he => absurd he h0) (fun he => absurd he h1)⟩
          have hst_mi : ({ st with core := { st.core with
              mrk := (st.core.mrk.set (BitVec.setWidth 64 (c0 >>> 1)).toNat 1#8).set
                (BitVec.setWidth 64 (c1 >>> 1)).toNat 1#8 } } : FullState) =
              { st with core := { st.core with mrk := mrk_init } } := by
            dsimp only [mrk_init]
            have h0_64 : (BitVec.setWidth 64 (c0 >>> 1)).toNat = (c0 >>> 1#32).toNat := by
              have hlt := BitVec.isLt (c0 >>> 1)
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl
            have h1_64 : (BitVec.setWidth 64 (c1 >>> 1)).toNat = (c1 >>> 1#32).toNat := by
              have hlt := BitVec.isLt (c1 >>> 1)
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl
            rw [h0_64, h1_64]
          refine hJt (BitVec.ofNat 64 st.core.trail_end, ()) _
            ⟨mrk_init, hmi_len, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega,
             by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _, ?_,
             bb_fullMem_eq hst_mi hm⟩
          rcases Nat.lt_or_gt_of_ne hidx_ne with h01 | h10
          · refine ⟨idx0, idx1, hidx0_ge, h01,
              by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hidx1_lt,
              fun v hv => by
                rw [hidx0_eq, hidx1_eq, fullInv_var_xor1, fullInv_var_xor1]; exact hmi_iff v hv,
              by rw [hidx0_eq, hidx1_eq, bb_xor1_xor1, bb_xor1_xor1]; exact hent_c⟩
          · refine ⟨idx1, idx0, hidx1_ge, h10,
              by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hidx0_lt,
              fun v hv => by
                rw [hidx0_eq, hidx1_eq, fullInv_var_xor1, fullInv_var_xor1, or_comm]
                exact hmi_iff v hv,
              by rw [hidx0_eq, hidx1_eq, bb_xor1_xor1, bb_xor1_xor1]
                 exact bb_entails_comm2 hent_c⟩
        · rintro Jt ⟨t, ⟨⟩⟩ mt
            ⟨mrk_t, hmt_len, ht_ge, ht_le, ⟨i1, i2, hi1_ge, hi12, hi2_lt, hdom, hent2⟩, hmt⟩ iht
          fvt_step; fvt_step
          · have ht_gt : saved.toNat < t.toNat := by c0_bound
            have ht_sub : (t - 1#64).toNat = t.toNat - 1 := by bv_omega
            have ht1_trl : (t - 1#64).toNat < st.core.trl.length := by rw [hcl.trl_len]; omega
            let z := st.core.trl[(t - 1#64).toNat]'ht1_trl
            have hz_get : st.core.trl[t.toNat - 1]?.getD 0#32 = z := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; dsimp only [z]
              simp only [ht_sub]
            have hz_lt : z.toNat < 2 * s0.core.cur_vars := by
              have := hbt.trl_lits_lt (t.toNat - 1) (by omega); rwa [hz_get] at this
            have hzv_lt : (z >>> 1#32).toNat < c.max_vars := by rw [bb_bv32_lshr1]; omega
            have hzv_mrk : (z >>> 1#32).toNat < mrk_t.length := by rw [hmt_len]; omega
            have hzv_rsn : (z >>> 1#32).toNat < st.core.rsns.length := by
              rw [hcl.rsns_len]; omega
            fvt_step; fvt_step; fvt_step
            · -- `mrk[zv] == 0`: skip `t - 1`
              have hm_z0 : mrk_t[(z >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                rw [List.getElem?_eq_getElem hzv_mrk, Option.getD_some]
                exact (bb_bv8_zext32_eq0 _).mp (by c0_bound)
              have hi2_ne : i2 ≠ t.toNat - 1 := fun he => by
                have hnz : mrk_t[(z >>> 1#32).toNat]?.getD 0#8 ≠ 0#8 :=
                  (hdom _ hzv_lt).mpr (Or.inr (by rw [bb_bv32_lshr1, he, hz_get]))
                exact hnz hm_z0
              fvt_steps
              exact iht (t - 1#64, ()) mt (by dsimp only; omega)
                ⟨mrk_t, hmt_len, by omega, by omega,
                 ⟨i1, i2, hi1_ge, hi12, by omega, hdom, hent2⟩, hmt⟩
            · -- `mrk[zv] ≠ 0`: `t - 1 = i2`, clear `mrk[zv]`, resolve via `rsns[zv]`
              have hm_znz : mrk_t[(z >>> 1#32).toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
                rw [List.getElem?_eq_getElem hzv_mrk, Option.getD_some] at h0
                exact (by c0_bound : (mrk_t[(z >>> 1#32).toNat]'hzv_mrk).setWidth 32 ≠ 0#32)
                  ((bb_bv8_zext32_eq0 _).mpr h0)
              have hi2_eq : t.toNat - 1 = i2 := by
                rcases (hdom _ hzv_lt).mp hm_znz with h_eq1 | h_eq2
                · have := hbt.trl_vars_nodup (t.toNat - 1) i1 (by omega) (by omega)
                    (by rw [hz_get, ← bb_bv32_lshr1]; exact h_eq1)
                  omega
                · exact hbt.trl_vars_nodup (t.toNat - 1) i2 (by omega) (by omega)
                    (by rw [hz_get, ← bb_bv32_lshr1]; exact h_eq2)
              let mrk1 := mrk_t.set (z >>> 1#32).toNat 0#8
              have hm1_len : mrk1.length = c.max_vars := by simp [mrk1, hmt_len]
              have hv1_ne_v2 : (st.core.trl[i1]?.getD 0#32).toNat / 2 ≠
                  (st.core.trl[i2]?.getD 0#32).toNat / 2 := fun he => by
                have := hbt.trl_vars_nodup i1 i2 (by omega) (by omega) he; omega
              have hm1_iff : ∀ v < c.max_vars,
                  mrk1[v]?.getD 0#8 ≠ 0#8 ↔ v = (st.core.trl[i1]?.getD 0#32).toNat / 2 := by
                intro v hv; dsimp only [mrk1]
                by_cases he : v = (z >>> 1#32).toNat
                · subst he
                  rw [List.getElem?_set_self hzv_mrk, Option.getD_some]
                  exact ⟨fun h => absurd rfl h, fun h => absurd h.symm (by
                    rw [bb_bv32_lshr1, ← hz_get, hi2_eq]; exact hv1_ne_v2)⟩
                · rw [List.getElem?_set_ne (Ne.symm he), hdom v hv]
                  exact ⟨fun ho => ho.elim id fun h2 => absurd
                    (by rw [h2, ← hi2_eq, hz_get, bb_bv32_lshr1]) he, Or.inl⟩
              fvt_step; fvt_step; fvt_step
              · -- `(rsn & PW_BIN_FLAG) == 0`: break to cleanup loop
                fvt_steps
                exact hJbr (t - 1#64, ()) _ ⟨mrk1, hm1_len, fun v hv hnz =>
                  ⟨i1, hi1_ge, by omega, ((hm1_iff v hv).mp hnz).symm⟩, hm⟩
              · -- `(rsn & PW_BIN_FLAG) ≠ 0`: resolve `z` with binary reason `rsn`
                have hi2_gt_s : saved.toNat < i2 := by omega
                obtain ⟨hbf_s, hnq_lt, hent_z, j, hj_ge, hj_lt, hj_eq⟩ :=
                  (hseg.2.2 i2 (by omega) (by omega)).2 hi2_gt_s
                have hrsn_get : st.core.rsns[(st.core.trl[i2]?.getD 0#32).toNat / 2]?.getD
                    0xFFFFFFFF#32 = st.core.rsns[(z >>> 1#32).toNat]'hzv_rsn := by
                  rw [← hi2_eq, hz_get, ← bb_bv32_lshr1,
                    List.getElem?_eq_getElem hzv_rsn, Option.getD_some]
                rw [hrsn_get] at hnq_lt hent_z hj_eq
                let p_l := (st.core.rsns[(z >>> 1#32).toNat]'hzv_rsn &&& 0x7FFFFFFF#32) ^^^ 1#32
                have hp_eq : p_l.toNat = (st.core.trl[j]?.getD 0#32).toNat := by
                  dsimp only [p_l]; rw [bb_bv32_xor1, hj_eq]
                have hp_lt : p_l.toNat < 2 * s0.core.cur_vars := by
                  rw [hp_eq]; exact hbt.trl_lits_lt j (by omega)
                have hpv_lt : (p_l >>> 1#32).toNat < c.max_vars := by rw [bb_bv32_lshr1]; omega
                have hpv_mrk : (p_l >>> 1#32).toNat < mrk1.length := by rw [hm1_len]; omega
                have hent_res : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [p_l.toNat ^^^ 1, (st.core.trl[i1]?.getD 0#32).toNat ^^^ 1]) := by
                  refine backbone_resolve2 (bb_entails_comm2 hent2) ?_
                  simpa [p_l, bb_bv32_xor1, bb_xor1_xor1] using hent_z
                fvt_step; fvt_step
                · -- `mrk1[pv] ≠ 0`: `pv` is already marked (`j = i1`) -> 1UIP found!
                  have hm1_pnz : mrk1[(p_l >>> 1#32).toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
                    rw [List.getElem?_eq_getElem hpv_mrk, Option.getD_some] at h0
                    exact (by c0_bound : (mrk1[(p_l >>> 1#32).toNat]'hpv_mrk).setWidth 32 ≠ 0#32)
                      ((bb_bv8_zext32_eq0 _).mpr h0)
                  have hj_eq_i1 : j = i1 := hbt.trl_vars_nodup j i1 (by omega) (by omega) (by
                    rw [← hp_eq, ← bb_bv32_lshr1]; exact (hm1_iff _ hpv_lt).mp hm1_pnz)
                  have hp_eq_i1 : (st.core.trl[i1]?.getD 0#32).toNat = p_l.toNat := by
                    rw [← hj_eq_i1, hp_eq]
                  have hent_uip :
                      (cnfOfClauses F_cur).EntailsClause (cnfClause [p_l.toNat ^^^ 1]) :=
                    backbone_collapse_eq (by rwa [hp_eq_i1] at hent_res)
                  fvt_steps
                  refine hQ p_l (mrk1.set (p_l >>> 1#32).toNat 0#8) _ (by simp [hm1_len])
                    (fun v hv => by
                      by_cases he : v = (p_l >>> 1#32).toNat
                      · subst he; rw [List.getElem?_set_self hpv_mrk, Option.getD_some]
                      · rw [List.getElem?_set_ne (Ne.symm he)]
                        exact Classical.byContradiction fun hnz =>
                          he (by rw [bb_bv32_lshr1, hp_eq, hj_eq_i1]; exact (hm1_iff v hv).mp hnz))
                    (fun _ => ⟨hp_lt, hent_uip⟩) hm
                · -- `mrk1[pv] == 0`: mark `pv` and continue resolution with `{j, i1}`
                  have hm1_pz : mrk1[(p_l >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem hpv_mrk, Option.getD_some]
                    exact (bb_bv8_zext32_eq0 _).mp (by c0_bound)
                  have hj_ne_i1 : j ≠ i1 := fun he => by
                    subst he
                    have hnz := (hm1_iff _ hpv_lt).mpr (by rw [bb_bv32_lshr1, hp_eq])
                    exact hnz hm1_pz
                  let mrk2 := mrk1.set (p_l >>> 1#32).toNat 1#8
                  have hm2_iff : ∀ v < c.max_vars, mrk2[v]?.getD 0#8 ≠ 0#8 ↔
                      v = (st.core.trl[j]?.getD 0#32).toNat / 2 ∨
                      v = (st.core.trl[i1]?.getD 0#32).toNat / 2 := fun v hv => by
                    dsimp only [mrk2]
                    by_cases he : v = (p_l >>> 1#32).toNat
                    · subst he; rw [List.getElem?_set_self hpv_mrk, Option.getD_some]
                      exact ⟨fun _ => Or.inl (by rw [bb_bv32_lshr1, hp_eq]), fun _ => by decide⟩
                    · rw [List.getElem?_set_ne (Ne.symm he), hm1_iff v hv]
                      exact ⟨Or.inr, fun ho => ho.elim
                        (fun h => absurd (by rw [bb_bv32_lshr1, hp_eq]; exact h) he) id⟩
                  fvt_steps
                  refine iht (t - 1#64, ()) _ (by dsimp only; omega)
                    ⟨mrk2, by simp [mrk2, hm1_len], by omega, by omega, ?_, hm⟩
                  rcases Nat.lt_or_gt_of_ne hj_ne_i1 with hji | hij
                  · exact ⟨j, i1, hj_ge, hji, by omega, hm2_iff, by rwa [hp_eq] at hent_res⟩
                  · exact ⟨i1, j, hi1_ge, hij, by omega,
                      fun v hv => by rw [or_comm]; exact hm2_iff v hv,
                      bb_entails_comm2 (by rwa [hp_eq] at hent_res)⟩

end BackbonePropAnalyzeProofs

/-! ## 5. Backbone Round & Top-Level Canonical Proofs (`round`, `full_backbone_m6`) -/

section BackboneTopProofs
private theorem bb_probeSeg_single {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    {probe : BitVec 32} {nlvl_bv : BitVec 32}
    (hpr_lt : probe.toNat < 2 * s0.core.cur_vars)
    (h0 : st.core.vals[probe.toNat]?.getD 0#8 = 0#8)
    (hte_lt : st.core.trail_end < c.max_vars)
    (hnlv : nlvl_bv.toNat = max_lvl + 1) :
    let v := probe.toNat / 2
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set probe.toNat 1#8).set (probe.toNat ^^^ 1) 0xFF#8
        lvl := st.core.lvl.set v nlvl_bv
        rsns := st.core.rsns.set v 0xFFFFFFFF#32
        trl := st.core.trl.set st.core.trail_end probe
        trail_end := st.core.trail_end + 1
        cur_level := max_lvl + 1 } }
    BackboneProbeSeg F_cur st' st.core.trail_end (max_lvl + 1) := by
  intro v st'
  have hcl := hbt.len_ok.core_ok
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_st ▸ hcl.cur_vars_le
  have hmiss := hbt.var_unassigned hpr_lt h0
  have hte_trl : st.core.trail_end < st.core.trl.length := by rw [hcl.trl_len]; omega
  have hv_lvl : v < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  refine ⟨by dsimp only [st']; omega, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · dsimp only [st']
    have hti : (st.core.trl.set st.core.trail_end probe)[i]? = st.core.trl[i]? :=
      List.getElem?_set_ne (by omega)
    rw [hti, List.getElem?_set_ne (Ne.symm (hmiss i hi))]
    have := hbt.lvl_le_max i hi; omega
  · dsimp only [st'] at hi2 ⊢
    have hi_eq : i = st.core.trail_end := by omega
    subst hi_eq
    rw [List.getElem?_set_self hte_trl, Option.getD_some,
      List.getElem?_set_self hv_lvl, Option.getD_some, hnlv]
    exact ⟨rfl, fun h => absurd h (Nat.lt_irrefl _)⟩
private theorem bb_ws1_keep_step {ws1 : List (BitVec 32)} {k ci lim bnd : Nat} {x : BitVec 32}
    (hlen : k < ws1.length) (hkle : k ≤ ci) (hx : x.toNat < bnd)
    (hprev : ∀ i < k, (ws1[i]?.getD 0#32).toNat < bnd)
    (hrem : ∀ i, ci ≤ i → i < lim → (ws1[i]?.getD 0#32).toNat < bnd) :
    (∀ i < k + 1, ((ws1.set k x)[i]?.getD 0#32).toNat < bnd) ∧
    (∀ i, ci + 1 ≤ i → i < lim → ((ws1.set k x)[i]?.getD 0#32).toNat < bnd) :=
  ⟨fun i hi => by
     rcases (by omega : i < k ∨ i = k) with hlt | rfl
     · rw [List.getElem?_set_ne (by omega)]; exact hprev i hlt
     · rw [List.getElem?_set_self hlen, Option.getD_some]; exact hx,
   fun i hi1 hi2 => by
     rw [List.getElem?_set_ne (by omega)]; exact hrem i (by omega) hi2⟩
private theorem bb_ws1_skip_step {ws1 : List (BitVec 32)} {ci lim bnd : Nat}
    (hrem : ∀ i, ci ≤ i → i < lim → (ws1[i]?.getD 0#32).toNat < bnd) :
    ∀ i, ci + 1 ≤ i → i < lim → (ws1[i]?.getD 0#32).toNat < bnd :=
  fun i hi1 hi2 => hrem i (by omega) hi2
private theorem bb_ws2_push_step {F_cur : List (List Nat)} {ws2 : List (BitVec 32)}
    {u bnd : Nat} {x : BitVec 32} (hlen : u < ws2.length)
    (hx : x.toNat < bnd ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat]))
    (hprev : ∀ i < u, (ws2[i]?.getD 0#32).toNat < bnd ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(ws2[i]?.getD 0#32).toNat])) :
    ∀ i < u + 1, ((ws2.set u x)[i]?.getD 0#32).toNat < bnd ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [((ws2.set u x)[i]?.getD 0#32).toNat]) :=
  fun i hi => by
    rcases (by omega : i < u ∨ i = u) with hlt | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hprev i hlt
    · rw [List.getElem?_set_self hlen, Option.getD_some]; exact hx

/-- `full_backbone_round_m6` satisfies `fullBackboneRoundM6Spec`. -/
theorem full_backbone_round_m6_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullBackbonePropM6Spec a m Q X →
      Γ "full_backbone_prop_m6" [i64, i64, .bool] [.bool] a m Q X)
    (hAnalyze : ∀ a m Q X, fullBackboneAnalyzeM6Spec a m Q X →
      Γ "full_backbone_analyze_m6" [i64, i32, i32, i64] [i32] a m Q X)
    (hUnwind : ∀ a m Q X, fullBackboneUnwindM6Spec a m Q X →
      Γ "full_backbone_unwind_m6" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullBackboneRoundM6Spec a m Q X →
      Func.wp Γ full_backbone_round_m6_body a m Q X := by
  rintro ⟨h, cand_n, stop_early, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hsp0, hl0, hcn_le, hlt_c, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok; have hscl0 := hsp0.1.scratch_ok
  have hcv_le := hcl0.cur_vars_le; have hte0_le := hcl0.trail_end_le
  have hnlits_eq :
      ((BitVec.ofNat 64 s0.core.cur_vars) <<< (BitVec.signExtend 64 1#32)).toNat =
        2 * s0.core.cur_vars := by
    rw [bb_bv64_shl1_sext _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs0_bv : (BitVec.ofNat 64 s0.core.trail_end).toNat = s0.core.trail_end := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Func.wp full_backbone_round_m6_body
  c0_hsteps_nogrp
  -- Break join `Js` (`[i64, i64, i64, .bool]` = `(ucnt, keep, ci, broken)`) -> tail copy + unwind
  refine wp_join_group (ts := [i64, i64, i64, .bool])
    (fun (ucnt, keep, ci, _broken, ()) mb =>
      ∃ st : FullState, BbTrailInv c F0 F_cur s0 st s0.core.trail_end st.core.cur_level ∧
        st.core.cur_level ≤ c.max_vars ∧
        keep.toNat ≤ ci.toNat ∧ ci.toNat ≤ cand_n.toNat ∧ ucnt.toNat ≤ 2 * s0.core.cur_vars ∧
        (∀ i < keep.toNat, (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
        (∀ i, ci.toNat ≤ i → i < cand_n.toNat →
          (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
        (∀ i < ucnt.toNat, (st.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(st.scratch.work_stk2[i]?.getD 0#32).toNat])) ∧
        (FullMem c st ⋆ R) mb)
    (fun _ ⟨ucnt, keep, ci, broken, ⟨⟩⟩ mb
        ⟨st, hbt, hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hmb⟩ => by
      fvt_to_group
      -- Tail loop `[i64, i64]` = `(keep_t, ci_t)` copying remaining `cands[ci ..< cand_n)`
      refine wp_loop_inv (ts := [i64, i64])
        (fun (kt, ct, ()) mt => ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
          kt.toNat ≤ ct.toNat ∧ ct.toNat ≤ cand_n.toNat ∧
          (∀ i < kt.toNat, (ws1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
          (∀ i, ct.toNat ≤ i → i < cand_n.toNat →
            (ws1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
          (FullMem c { st with scratch := { st.scratch with work_stk1 := ws1 } } ⋆ R) mt)
        (fun (_, ct, ()) _ => cand_n.toNat - ct.toNat) ?_ ?_
      · intro Jt hJt; fvt_steps
        exact hJt (keep, ci, ()) mb ⟨st.scratch.work_stk1, hbt.len_ok.scratch_ok.work_stk1_len,
          hkp_le, hci_le, hkp_lt, hrem_lt, hmb⟩
      · rintro Jt ⟨kt, ct, ⟨⟩⟩ mt ⟨ws1, hws1, hkt_le, hct_le, hkt_lt, hct_rem, hmt⟩ iht
        fvt_step; fvt_step
        · have hct_lt : ct.toNat < cand_n.toNat := by c0_bound
          have hct1 : (ct + 1#64).toNat = ct.toNat + 1 := by bv_omega
          have hkt1 : (kt + 1#64).toNat = kt.toNat + 1 := by bv_omega
          have hct_ws1 : ct.toNat < ws1.length := by omega
          have hkt_ws1 : kt.toNat < ws1.length := by omega
          let rem := ws1[ct.toNat]'hct_ws1
          have hrem_b : rem.toNat < 2 * s0.core.cur_vars := by
            have := hct_rem ct.toNat (Nat.le_refl _) hct_lt
            rwa [List.getElem?_eq_getElem hct_ws1, Option.getD_some] at this
          have hrem_val : rem.toNat < st.core.vals.length := by
            rw [hbt.len_ok.core_ok.vals_len]; omega
          fvt_to_group
          refine wp_join_group (ts := [i64])
            (fun (kt', ()) mn => ∃ ws1' : List (BitVec 32), ws1'.length = 2 * c.max_vars ∧
              kt'.toNat ≤ ct.toNat + 1 ∧
              (∀ i < kt'.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
              (∀ i, ct.toNat + 1 ≤ i → i < cand_n.toNat →
                (ws1'[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
              (FullMem c { st with scratch := { st.scratch with work_stk1 := ws1' } } ⋆ R) mn)
            (fun _ ⟨kt', ⟨⟩⟩ mn ⟨ws1', hws1', hkt', hkt_lt', hrem', hmn⟩ => by
              fvt_steps
              exact iht (kt', ct + 1#64, ()) mn (by dsimp only; omega)
                ⟨ws1', hws1', by omega, by omega, hkt_lt', by rwa [hct1], hmn⟩)
            (fun Jn hJn => by
              refine wp_join_group (ts := []) (fun _ mw => mw = mt)
                (fun _ _ mw heq => by
                  subst heq; fvt_steps
                  obtain ⟨h1, h2⟩ := bb_ws1_keep_step hkt_ws1 hkt_le hrem_b hkt_lt hct_rem
                  exact hJn (kt + 1#64, ()) _
                    ⟨ws1.set kt.toNat rem, by simp [hws1], by omega, by rwa [hkt1], h2, hm⟩)
                (fun Jw hJw => by
                  fvt_steps
                  · exact hJw () mt rfl
                  · exact hJw () mt rfl
                  · exact hJn (kt, ()) mt ⟨ws1, hws1, by omega, hkt_lt,
                      bb_ws1_skip_step hct_rem, hmt⟩))
        · -- Exit tail loop: `unwind(saved0, 0)`, store `res_sz = ucnt`, ret `kt`
          let st_w : FullState := { st with scratch := { st.scratch with work_stk1 := ws1 } }
          have hbt_w : BbTrailInv c F0 F_cur s0 st_w s0.core.trail_end st.core.cur_level :=
            BbTrailInv.with_ws1_ws2 hbt hws1 hbt.len_ok.scratch_ok.work_stk2_len
          have hlvl_s0 : ∀ i < s0.core.trail_end,
              (st_w.core.lvl[(st_w.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ 0 := by
            intro i hi
            have ht0 := hbt_w.trl_prefix i hi
            have hlp := (hbt_w.lvl_prefix i hi).1
            rw [ht0, hlp]
            have := hsp0.2.1.lvl_le i hi; omega
          fvt_steps; c0_call hUnwind
          refine ⟨c, F0, F_cur, s0, st_w, s0.core.trail_end, st.core.cur_level, R, rfl, hsp0,
            hbt_w, by omega, by rw [hs0_bv]; exact hbt_w.saved0_le, by simp,
            by simpa [hs0_bv] using hlvl_s0, hmt, fun vals_f mf hbt_f hmf => ?_⟩
          fvt_steps
          let sf : FullState :=
            { st_w with
              core := { st_w.core with
                vals := vals_f, trail_end := s0.core.trail_end, cur_level := 0 }
              scratch := { st_w.scratch with res_sz := ucnt } }
          have hbt_f' : BbTrailInv c F0 F_cur s0 sf s0.core.trail_end 0 :=
            BbTrailInv.with_ws1_ws2 (by simpa [hs0_bv] using hbt_f) hws1
              hbt.len_ok.scratch_ok.work_stk2_len
          have hsp_f : FullSparseInvW c F0 F_cur sf :=
            BbTrailInv.to_fullSparseInvW hsp0 hbt_f' rfl rfl
          have hcv_f : sf.core.cur_vars = s0.core.cur_vars := by rw [hbt_f'.same_core]
          have hfu_f : sf.core.fuel = s0.core.fuel := by rw [hbt_f'.same_core]
          exact hQ kt sf _ hsp_f rfl hcv_f hfu_f (by omega) hkt_lt huc_le huc_ok
            (by simpa [sf, hs0_bv] using hm))
    (fun Jbr hJbr => ?_)
  -- Main loop `[i64, i64, i64]` = `(ucnt, keep, ci)`
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (ucnt, keep, ci, ()) m1 =>
      ∃ st : FullState, BbTrailInv c F0 F_cur s0 st s0.core.trail_end st.core.cur_level ∧
        st.core.cur_level ≤ c.max_vars ∧
        keep.toNat ≤ ci.toNat ∧ ci.toNat ≤ cand_n.toNat ∧ ucnt.toNat ≤ 2 * s0.core.cur_vars ∧
        (∀ i < keep.toNat, (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
        (∀ i, ci.toNat ≤ i → i < cand_n.toNat →
          (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
        (∀ i < ucnt.toNat, (st.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(st.scratch.work_stk2[i]?.getD 0#32).toNat])) ∧
        (FullMem c st ⋆ R) m1)
    (fun (_, _, ci, ()) _ => cand_n.toNat - ci.toNat) ?_ ?_
  · intro J1 hJ1; c0_hsteps_nogrp
    exact hJ1 (0#64, 0#64, 0#64, ()) m0 ⟨s0, by rw [hl0]; exact BbTrailInv.init hsp0 hl0,
      by omega, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, (fun _ h => by cases h),
      fun i _ hi => hlt_c i hi, (fun _ h => by cases h), hm0⟩
  · rintro J1 ⟨ucnt, keep, ci, ⟨⟩⟩ m1
      ⟨st, hbt, hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hm1⟩ ih1
    have hcl := hbt.len_ok.core_ok; have hscl := hbt.len_ok.scratch_ok
    have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
    have hte_le : st.core.trail_end ≤ c.max_vars := Nat.le_trans hcl.trail_end_le (by omega)
    c0_hsplit
    · have hci_lt : ci.toNat < cand_n.toNat := by c0_bound
      c0_hsplit
      · c0_hsplit
        · have hte_lt : st.core.trail_end < c.max_vars := by
            have h1 : st.core.trail_end % 2 ^ 64 < c.max_vars % 2 ^ 64 := by c0_bound
            rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
          have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by bv_omega
          have hkp1 : (keep + 1#64).toNat = keep.toNat + 1 := by bv_omega
          have hci_ws1 : ci.toNat < st.scratch.work_stk1.length := by
            rw [hscl.work_stk1_len]; omega
          have hkp_ws1 : keep.toNat < st.scratch.work_stk1.length := by
            rw [hscl.work_stk1_len]; omega
          let probe := st.scratch.work_stk1[ci.toNat]'hci_ws1
          have hpr_lt : probe.toNat < 2 * s0.core.cur_vars := by
            have := hrem_lt ci.toNat (Nat.le_refl _) hci_lt
            rwa [List.getElem?_eq_getElem hci_ws1, Option.getD_some] at this
          have hpr_val : probe.toNat < st.core.vals.length := by rw [hcl.vals_len]; omega
          have hpr_dom := hbt.vals_dom probe.toNat hpr_lt
          rw [List.getElem?_eq_getElem hpr_val, Option.getD_some] at hpr_dom
          c0_hsplit
          · -- `pv > 0`: already implied true, drop candidate
            c0_hsteps
            exact ih1 (ucnt, keep, ci + 1#64, ()) m1 (by dsimp only; omega)
              ⟨st, hbt, hcl_le, by omega, by omega, huc_le, hkp_lt,
               by rw [hci1]; exact bb_ws1_skip_step hrem_lt, huc_ok, hm1⟩
          · rename_i h_ngt; c0_hsplit
            · -- `pv < 0`: already false, keep candidate
              c0_hsteps
              obtain ⟨h1, h2⟩ := bb_ws1_keep_step hkp_ws1 hkp_le hpr_lt hkp_lt hrem_lt
              exact ih1 (ucnt, keep + 1#64, ci + 1#64, ()) _ (by dsimp only; omega)
                ⟨{ st with scratch := { st.scratch with
                    work_stk1 := st.scratch.work_stk1.set keep.toNat probe } },
                 BbTrailInv.with_ws1_ws2 hbt (by simp [hscl.work_stk1_len])
                  hscl.work_stk2_len, hcl_le, by omega, by omega, huc_le,
                 by rwa [hkp1], by rwa [hci1], huc_ok, (by assumption)⟩
            · -- `pv == 0`: push `probe` at `nlvl = old_lvl + 1`, call `full_backbone_prop_m6`
              rename_i h_nlt
              have hpr_z : st.core.vals[probe.toNat]?.getD 0#8 = 0#8 := by
                rw [List.getElem?_eq_getElem hpr_val, Option.getD_some]
                rcases hpr_dom with hz | h1 | hff
                · exact hz
                · exfalso; dsimp only [probe] at h1; rw [h1] at h_nlt
                  exact absurd h_nlt (by decide)
                · exfalso; dsimp only [probe] at hff; rw [hff] at hc
                  exact absurd hc (by decide)
              have hte_bv : (BitVec.ofNat 64 st.core.trail_end).toNat = st.core.trail_end := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have hold_bv : (BitVec.ofNat 64 st.core.cur_level).toNat = st.core.cur_level := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have hnlvl_add : (BitVec.ofNat 64 st.core.cur_level + 1).toNat =
                  st.core.cur_level + 1 := by
                rw [BitVec.toNat_add, hold_bv, show (1 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              c0_hsplit
              · -- `nlvl > max_vars`: keep `probe`, `broken = true`, break
                c0_hsteps
                obtain ⟨h1, h2⟩ := bb_ws1_keep_step hkp_ws1 hkp_le hpr_lt hkp_lt hrem_lt
                exact hJbr (ucnt, keep + 1#64, ci + 1#64, true, ()) _
                  ⟨{ st with scratch := { st.scratch with
                      work_stk1 := st.scratch.work_stk1.set keep.toNat probe } },
                   BbTrailInv.with_ws1_ws2 hbt (by simp [hscl.work_stk1_len])
                    hscl.work_stk2_len, hcl_le, by omega, by omega, huc_le,
                   by rwa [hkp1], by rwa [hci1], huc_ok, (by assumption)⟩
              · -- `nlvl ≤ max_vars`: push decision `probe`, propagate
                have hnlvl_le : st.core.cur_level + 1 ≤ c.max_vars := by
                  have h1 : (BitVec.ofNat 64 st.core.cur_level + 1).toNat ≤
                      (BitVec.ofNat 64 c.max_vars).toNat := by c0_bound
                  rwa [hnlvl_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
                have hnlvl_tr :
                    ((BitVec.ofNat 64 st.core.cur_level + 1).truncate 32).toNat =
                      st.core.cur_level + 1 := by
                  rw [BitVec.toNat_setWidth, hnlvl_add, Nat.mod_eq_of_lt (by omega)]
                have hpr64 : (probe.setWidth 64).toNat = probe.toNat :=
                  FullTransHelpers.ft_bv32_setWidth64 probe
                have hprn64 : ((probe ^^^ 1).setWidth 64).toNat = probe.toNat ^^^ 1 := by
                  rw [FullTransHelpers.ft_bv32_setWidth64]; exact bb_bv32_xor1 probe
                have hprr64 : ((probe >>> 1).setWidth 64).toNat = probe.toNat / 2 := by
                  rw [FullTransHelpers.ft_bv32_setWidth64]
                  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                have hpr_not_v :
                    (probe ^^^ 1#32).toNat < (st.core.vals.set probe.toNat 1#8).length := by
                  rw [List.length_set, bb_bv32_xor1, hcl.vals_len]
                  have := litNeg_lt_two_mul hpr_lt; omega
                have hpr_lvl : (probe >>> 1#32).toNat < st.core.lvl.length := by
                  rw [bb_bv32_lshr1, hcl.lvl_len]; omega
                have hpr_rsn : (probe >>> 1#32).toNat < st.core.rsns.length := by
                  rw [bb_bv32_lshr1, hcl.rsns_len]; omega
                have hte_trl : (BitVec.ofNat 64 st.core.trail_end).toNat < st.core.trl.length := by
                  rw [hte_bv, hcl.trl_len]; omega
                have hte_add : (BitVec.ofNat 64 st.core.trail_end + 1).toNat =
                    st.core.trail_end + 1 := by
                  rw [BitVec.toNat_add, hte_bv, show (1 : BitVec 64).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                let st_d : FullState :=
                  { st with core := { st.core with
                    vals := (st.core.vals.set probe.toNat 1#8).set (probe.toNat ^^^ 1) 0xFF#8
                    lvl := st.core.lvl.set (probe.toNat / 2)
                      ((BitVec.ofNat 64 st.core.cur_level + 1).truncate 32)
                    rsns := st.core.rsns.set (probe.toNat / 2) 0xFFFFFFFF#32
                    trl := st.core.trl.set st.core.trail_end probe
                    trail_end := st.core.trail_end + 1
                    cur_level := st.core.cur_level + 1 } }
                have hbt_d : BbTrailInv c F0 F_cur s0 st_d s0.core.trail_end
                    (st.core.cur_level + 1) :=
                  BbTrailInv.push hbt (Nat.le_succ _) hpr_lt hpr_z hte_lt
                    (by rw [hnlvl_tr]; omega) (Nat.le_refl _) (by rw [hnlvl_tr]; omega)
                have hseg_d : BackboneProbeSeg F_cur st_d st.core.trail_end
                    (st.core.cur_level + 1) :=
                  bb_probeSeg_single hbt hpr_lt hpr_z hte_lt hnlvl_tr
                c0_hsteps_nogrp
                c0_call hProp
                refine ⟨c, F0, F_cur, s0, st_d, s0.core.trail_end, st.core.cur_level + 1, R, rfl,
                  hsp0, hbt_d, by rw [hte_bv]; exact hbt.saved0_le,
                  by dsimp only [st_d]; rw [hte_bv]; omega,
                  Or.inr ⟨by dsimp only [st_d]; omega, st.core.trail_end, hbt.saved0_le,
                    by rw [hte_bv]; exact Nat.le_refl _, hseg_d⟩, ?_,
                  fun pok vals_p lvl_p rsns_p trl_p te_p c0_p c1_p asz_p mp
                    hbt_p hte_p htp_p hlp_p hseg_p hcf_p hmp => ?_⟩
                · refine bb_fullMem_eq ?_ (by assumption)
                  dsimp only [st_d]
                  rw [hnlvl_add, hpr64, hprn64, hprr64, hte_bv, hte_add]; rfl
                let st_p : FullState :=
                  { st_d with
                    core := { st_d.core with
                      vals := vals_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p, trail_end := te_p,
                      confl_lit0 := c0_p, confl_lit1 := c1_p }
                    scratch := { st_d.scratch with ant_sz := asz_p } }
                have hseg_p' : BackboneProbeSeg F_cur st_p st.core.trail_end
                    (st.core.cur_level + 1) :=
                  hseg_p st.core.trail_end hbt.saved0_le (by rw [hte_bv]; exact Nat.le_refl _)
                    (by dsimp only [st_d]; omega) hseg_d
                have hlvl_saved : ∀ i < st.core.trail_end,
                    (lvl_p[(trl_p[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                      st.core.cur_level := fun i hi => by
                  have h1 := hseg_p'.2.1 i hi; dsimp only [st_p] at h1; omega
                c0_hsplit
                · -- `pok = true`: check `ant_sz == 0`
                  c0_hsplit
                  · -- `ant_sz == 0`: unwind to `(saved, old_lvl)`, keep `probe`, break
                    c0_call hUnwind
                    refine ⟨c, F0, F_cur, s0, st_p, s0.core.trail_end, st.core.cur_level + 1, R,
                      rfl, hsp0, hbt_p, by rw [hte_bv]; exact hbt.saved0_le,
                      by dsimp only [st_p, st_d] at hte_p ⊢; rw [hte_bv]; omega,
                      by rw [hold_bv]; exact hcl_le,
                      by simpa [hte_bv, hold_bv] using hlvl_saved, hmp,
                      fun vals_u mu hbt_u hmu => ?_⟩
                    let st_u : FullState :=
                      { st_p with core := { st_p.core with
                        vals := vals_u, trail_end := st.core.trail_end,
                        cur_level := st.core.cur_level } }
                    have hbt_u' : BbTrailInv c F0 F_cur s0 st_u s0.core.trail_end
                        st.core.cur_level := by simpa [st_u, hte_bv, hold_bv] using hbt_u
                    have hmu' : (FullMem c st_u ⋆ R) mu := by
                      simpa [st_u, hte_bv, hold_bv] using hmu
                    clear hmu
                    c0_hsteps
                    obtain ⟨h1, h2⟩ := bb_ws1_keep_step hkp_ws1 hkp_le hpr_lt hkp_lt hrem_lt
                    exact hJbr (ucnt, keep + 1#64, ci + 1#64, true, ()) _
                      ⟨{ st_u with scratch := { st_u.scratch with
                          work_stk1 := st.scratch.work_stk1.set keep.toNat probe } },
                       BbTrailInv.with_ws1_ws2 hbt_u' (by simp [hscl.work_stk1_len])
                        hscl.work_stk2_len, hcl_le, by omega, by omega, huc_le,
                       by rwa [hkp1], by rwa [hci1], huc_ok, (by assumption)⟩
                  · -- `ant_sz > 0`: stay at `nlvl` and continue to next candidate
                    c0_hsteps
                    exact ih1 (ucnt, keep, ci + 1#64, ()) mp (by dsimp only; omega)
                      ⟨st_p, hbt_p, hnlvl_le, by omega, by omega, huc_le, hkp_lt,
                       by rw [hci1]; exact bb_ws1_skip_step hrem_lt, huc_ok, hmp⟩
                · -- `pok = false`: conflict! Analyze 1UIP, unwind to `(saved, old_lvl)`
                  obtain ⟨hc0_lt, hc1_lt, hc0_ff, hc1_ff, hent_cf, idx0, hidx0_ge, hidx0_lt,
                    hidx0_eq⟩ := hcf_p (by c0_bound)
                  have hc0_tr : (c0_p.truncate 32).toNat = c0_p.toNat := by
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                  have hc1_tr : (c1_p.truncate 32).toNat = c1_p.toNat := by
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                  c0_hsteps_nogrp; c0_call hAnalyze
                  refine ⟨c, F0, F_cur, s0, st_p, s0.core.trail_end, st.core.cur_level + 1, R, rfl,
                    hsp0, hbt_p, by dsimp only [st_p, st_d]; omega,
                    by rw [hte_bv]; exact hbt.saved0_le,
                    by simpa [hte_bv] using hseg_p'.2.1,
                    by simpa [hte_bv] using hseg_p',
                    by rwa [hc0_tr], by rwa [hc1_tr], by rwa [hc0_tr], by rwa [hc1_tr],
                    by rwa [hc0_tr, hc1_tr],
                    ⟨idx0, by rw [hte_bv] at hidx0_ge ⊢; exact hidx0_ge, hidx0_lt,
                     by rwa [hc0_tr]⟩, hmp,
                    fun uip mrk_a ma hma_len hma_z huip_ok hma => ?_⟩
                  have hmrk_eq : mrk_a = s0.core.mrk :=
                    BbTrailInv.with_mrk hbt_p hsp0 hma_len hma_z
                  have hma' : (FullMem c st_p ⋆ R) ma := by
                    refine bb_fullMem_eq ?_ hma
                    have h1 : st.core.mrk = s0.core.mrk := by rw [hbt.same_core]
                    dsimp only [st_p, st_d]; rw [hmrk_eq, h1]
                  c0_call hUnwind
                  refine ⟨c, F0, F_cur, s0, st_p, s0.core.trail_end, st.core.cur_level + 1, R, rfl,
                    hsp0, hbt_p, by rw [hte_bv]; exact hbt.saved0_le,
                    by dsimp only [st_p, st_d] at hte_p ⊢; rw [hte_bv]; omega,
                    by rw [hold_bv]; exact hcl_le,
                    by simpa [hte_bv, hold_bv] using hlvl_saved, hma',
                    fun vals_u mu hbt_u hmu => ?_⟩
                  let st_u : FullState :=
                    { st_p with core := { st_p.core with
                      vals := vals_u, trail_end := st.core.trail_end,
                      cur_level := st.core.cur_level } }
                  have hbt_u' : BbTrailInv c F0 F_cur s0 st_u s0.core.trail_end
                      st.core.cur_level := by simpa [st_u, hte_bv, hold_bv] using hbt_u
                  have hmu' : (FullMem c st_u ⋆ R) mu := by simpa [st_u, hte_bv, hold_bv] using hmu
                  clear hmu
                  c0_hsplit
                  · -- `uip == 0xFFFFFFFF`: keep `probe`, continue
                    c0_hsteps
                    obtain ⟨h1, h2⟩ := bb_ws1_keep_step hkp_ws1 hkp_le hpr_lt hkp_lt hrem_lt
                    exact ih1 (ucnt, keep + 1#64, ci + 1#64, ()) _ (by dsimp only; omega)
                      ⟨{ st_u with scratch := { st_u.scratch with
                          work_stk1 := st.scratch.work_stk1.set keep.toNat probe } },
                       BbTrailInv.with_ws1_ws2 hbt_u' (by simp [hscl.work_stk1_len])
                        hscl.work_stk2_len, hcl_le, by omega, by omega, huc_le,
                       by rwa [hkp1], by rwa [hci1], huc_ok, (by assumption)⟩
                  · -- `uip ≠ 0xFFFFFFFF`: learned unit `not_uip = uip ^^^ 1`!
                    have huip_ne : uip ≠ 0xFFFFFFFF#32 := by c0_bound
                    obtain ⟨huip_lt, hent_nu⟩ := huip_ok huip_ne
                    let not_uip := uip ^^^ 1#32
                    have hnu_eq : not_uip.toNat = uip.toNat ^^^ 1 := bb_bv32_xor1 uip
                    have hnu_lt : not_uip.toNat < 2 * s0.core.cur_vars := by
                      rw [hnu_eq]; exact litNeg_lt_two_mul huip_lt
                    have hnu_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_uip.toNat]) :=
                      by rwa [hnu_eq]
                    c0_hsteps_nogrp
                    -- Join 1: `if (ucnt < nlits)` record `not_uip` in `work_stk2`
                    refine wp_join_group (ts := [i64])
                      (fun (ucnt', ()) m_u => ∃ ws2' : List (BitVec 32),
                        ws2'.length = 2 * c.max_vars ∧ ucnt'.toNat ≤ 2 * s0.core.cur_vars ∧
                        (∀ i < ucnt'.toNat, (ws2'[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
                          (cnfOfClauses F_cur).EntailsClause
                            (cnfClause [(ws2'[i]?.getD 0#32).toNat])) ∧
                        (FullMem c { st_u with scratch := { st_u.scratch with work_stk2 := ws2' } }
                          ⋆ R) m_u)
                      (fun _ ⟨ucnt', ⟨⟩⟩ m_u ⟨ws2', hws2', huc', huc_ok', hm_u⟩ => by
                        let st_u2 : FullState :=
                          { st_u with scratch := { st_u.scratch with work_stk2 := ws2' } }
                        have hbt_u2 : BbTrailInv c F0 F_cur s0 st_u2 s0.core.trail_end
                            st.core.cur_level :=
                          BbTrailInv.with_ws1_ws2 hbt_u' hscl.work_stk1_len hws2'
                        -- Join 2: `if (uip != probe)` keep `probe` in `work_stk1`
                        refine wp_join_group (ts := [i64])
                          (fun (keep', ()) m_k => ∃ ws1' : List (BitVec 32),
                            ws1'.length = 2 * c.max_vars ∧ keep'.toNat ≤ ci.toNat + 1 ∧
                            (∀ i < keep'.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
                            (∀ i, ci.toNat + 1 ≤ i → i < cand_n.toNat →
                              (ws1'[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
                            (FullMem c { st_u2 with scratch := { st_u2.scratch with
                              work_stk1 := ws1' } } ⋆ R) m_k)
                          (fun _ ⟨keep', ⟨⟩⟩ m_k ⟨ws1', hws1', hkp', hkp_lt', hrem', hm_k⟩ => by
                            let st_k : FullState :=
                              { st_u2 with scratch := { st_u2.scratch with work_stk1 := ws1' } }
                            have hbt_k : BbTrailInv c F0 F_cur s0 st_k s0.core.trail_end
                                st.core.cur_level :=
                              BbTrailInv.with_ws1_ws2 hbt_u2 hws1' hws2'
                            have hnu_val : not_uip.toNat < vals_u.length := by
                              rw [hbt_k.len_ok.core_ok.vals_len]; omega
                            have hnu_dom := hbt_k.vals_dom not_uip.toNat hnu_lt
                            rw [List.getElem?_eq_getElem hnu_val, Option.getD_some] at hnu_dom
                            c0_hsplit
                            · -- `nv < 0`: break (`broken = true`)
                              c0_hsteps
                              exact hJbr (ucnt', keep', ci + 1#64, true, ()) m_k
                                ⟨st_k, hbt_k, hcl_le, by rw [hci1]; exact hkp', by omega, huc',
                                 hkp_lt', by rwa [hci1], huc_ok', hm_k⟩
                            · refine wp_unroll_group fun Jn hJn => ?_
                              c0_hsplit
                              · -- `nv == 0`: check `trail_end < max_vars`, assign at level 0 & prop
                                have hnu_z : vals_u[not_uip.toNat]?.getD 0#8 = 0#8 := by
                                  rw [List.getElem?_eq_getElem hnu_val, Option.getD_some]
                                  exact (bb_bv8_sext32_eq0 _).mp hc
                                c0_hsplit
                                · -- Push `not_uip` at level 0 & call `full_backbone_prop_m6`
                                  have hnu64 : (not_uip.setWidth 64).toNat = not_uip.toNat :=
                                    FullTransHelpers.ft_bv32_setWidth64 not_uip
                                  have huip64 : (uip.setWidth 64).toNat = uip.toNat :=
                                    FullTransHelpers.ft_bv32_setWidth64 uip
                                  have hnur64 :
                                      ((not_uip >>> 1).setWidth 64).toNat = not_uip.toNat / 2 := by
                                    rw [FullTransHelpers.ft_bv32_setWidth64]
                                    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                                  have huip_val :
                                      uip.toNat < (vals_u.set not_uip.toNat 1#8).length := by
                                    rw [List.length_set, hbt_k.len_ok.core_ok.vals_len]; omega
                                  have hnu_lvl :
                                      (not_uip >>> 1#32).toNat < st_k.core.lvl.length := by
                                    rw [bb_bv32_lshr1, hbt_k.len_ok.core_ok.lvl_len]; omega
                                  have hnu_rsn :
                                      (not_uip >>> 1#32).toNat < st_k.core.rsns.length := by
                                    rw [bb_bv32_lshr1, hbt_k.len_ok.core_ok.rsns_len]; omega
                                  have hte_trl_k : (BitVec.ofNat 64 st.core.trail_end).toNat <
                                      st_k.core.trl.length := by
                                    rw [hte_bv, hbt_k.len_ok.core_ok.trl_len]; omega
                                  let st_l0 : FullState :=
                                    { st_k with core := { st_k.core with
                                      vals := (vals_u.set not_uip.toNat 1#8).set
                                        (not_uip.toNat ^^^ 1) 0xFF#8
                                      lvl := st_k.core.lvl.set (not_uip.toNat / 2) 0#32
                                      rsns := st_k.core.rsns.set (not_uip.toNat / 2) 0xFFFFFFFF#32
                                      trl := st_k.core.trl.set st.core.trail_end not_uip
                                      trail_end := st.core.trail_end + 1
                                      cur_level := 0 } }
                                  have hbt_l0 : BbTrailInv c F0 F_cur s0 st_l0 s0.core.trail_end
                                      st.core.cur_level :=
                                    BbTrailInv.push hbt_k (Nat.le_refl _) hnu_lt hnu_z hte_lt
                                      (Nat.zero_le _) (Nat.zero_le _) (fun _ => hnu_ent)
                                  c0_hsteps_nogrp
                                  c0_call hProp
                                  refine ⟨c, F0, F_cur, s0, st_l0, s0.core.trail_end,
                                    st.core.cur_level, R, rfl, hsp0, hbt_l0,
                                    by rw [hte_bv]; exact hbt.saved0_le,
                                    by dsimp only [st_l0]; rw [hte_bv]; omega,
                                    Or.inl ⟨rfl, fun i hi1 hi2 => by
                                      dsimp only [st_l0] at hi2 ⊢; rw [hte_bv] at hi1
                                      have hi_eq : i = st.core.trail_end := by omega
                                      subst hi_eq
                                      rw [List.getElem?_set_self (by
                                        rw [hbt_k.len_ok.core_ok.trl_len]; omega), Option.getD_some,
                                        List.getElem?_set_self (by
                                          rw [hbt_k.len_ok.core_ok.lvl_len]; omega),
                                        Option.getD_some]; rfl⟩, ?_,
                                    fun pok2 vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2 m2
                                      hbt2 _ _ _ _ _ hm2 => ?_⟩
                                  · refine bb_fullMem_eq ?_ (by assumption)
                                    dsimp only [st_l0, st_k, st_u2, st_u, st_p, st_d, not_uip]
                                    rw [FullTransHelpers.ft_bv32_setWidth64,
                                      FullTransHelpers.ft_bv32_setWidth64,
                                      FullTransHelpers.ft_bv32_setWidth64, hte_bv, hte_add, hnu_eq,
                                      bb_xor1_xor1]
                                    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                                    rfl
                                  let st_r : FullState :=
                                    { st_l0 with
                                      core := { st_l0.core with
                                        vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2,
                                        trail_end := te2, confl_lit0 := c02, confl_lit1 := c12,
                                        cur_level := st.core.cur_level }
                                      scratch := { st_l0.scratch with ant_sz := asz2 } }
                                  have hbt_r : BbTrailInv c F0 F_cur s0 st_r s0.core.trail_end
                                      st.core.cur_level :=
                                    BbTrailInv.with_cur_level hbt2 (Nat.le_refl _) hbt2.lvl_le_max
                                  c0_hsplit
                                  · c0_hsplit
                                    · c0_hsteps
                                      exact hJbr (ucnt', keep', ci + 1#64, true, ()) _
                                        ⟨st_r, hbt_r, hcl_le, by rw [hci1]; exact hkp', by omega,
                                         huc', hkp_lt', by rwa [hci1], huc_ok',
                                         by first
                                            | assumption
                                            | (refine bb_fullMem_eq ?_ (by assumption)
                                               dsimp only [st_r]; rw [hold_bv])⟩
                                    · c0_hsteps
                                      exact ih1 (ucnt', keep', ci + 1#64, ()) _
                                        (by dsimp only; omega)
                                        ⟨st_r, hbt_r, hcl_le, by rw [hci1]; exact hkp', by omega,
                                         huc', hkp_lt', by rwa [hci1], huc_ok',
                                         by first
                                            | assumption
                                            | (refine bb_fullMem_eq ?_ (by assumption)
                                               dsimp only [st_r]; rw [hold_bv])⟩
                                  · c0_hsteps
                                    exact hJbr (ucnt', keep', ci + 1#64, true, ()) _
                                      ⟨st_r, hbt_r, hcl_le, by rw [hci1]; exact hkp', by omega,
                                       huc', hkp_lt', by rwa [hci1], huc_ok',
                                       by first
                                          | assumption
                                          | (refine bb_fullMem_eq ?_ (by assumption)
                                             dsimp only [st_r]; rw [hold_bv])⟩
                                · c0_hsteps
                                  exact ih1 (ucnt', keep', ci + 1#64, ()) m_k (by dsimp only; omega)
                                    ⟨st_k, hbt_k, hcl_le, by rw [hci1]; exact hkp', by omega, huc',
                                     hkp_lt', by rwa [hci1], huc_ok', hm_k⟩
                              · c0_hsteps
                                exact ih1 (ucnt', keep', ci + 1#64, ()) m_k (by dsimp only; omega)
                                  ⟨st_k, hbt_k, hcl_le, by rw [hci1]; exact hkp', by omega, huc',
                                   hkp_lt', by rwa [hci1], huc_ok', hm_k⟩)
                          (fun Jk hJk => by
                            c0_hsplit
                            · c0_hsteps
                              obtain ⟨h1, h2⟩ :=
                                bb_ws1_keep_step hkp_ws1 hkp_le hpr_lt hkp_lt hrem_lt
                              exact hJk (keep + 1#64, ()) _
                                ⟨st.scratch.work_stk1.set keep.toNat probe,
                                 by simp [hscl.work_stk1_len],
                                 by omega, by rwa [hkp1], h2, (by assumption)⟩
                            · c0_hsteps
                              exact hJk (keep, ()) m_u ⟨st.scratch.work_stk1, hscl.work_stk1_len,
                                by omega, hkp_lt, bb_ws1_skip_step hrem_lt, hm_u⟩))
                      (fun Ju hJu => by
                        c0_hsplit
                        · have huc_lt : ucnt.toNat < 2 * s0.core.cur_vars := by
                            have h1 : ucnt.toNat < ((BitVec.ofNat 64 s0.core.cur_vars) <<<
                                (1 : Nat)).toNat := by c0_bound
                            rw [bb_bv64_shl1_nat _ (by rw [BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega)]; omega), BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega)] at h1; omega
                          have huc1 : (ucnt + 1#64).toNat = ucnt.toNat + 1 := by bv_omega
                          have huc_ws2 : ucnt.toNat < st.scratch.work_stk2.length := by
                            rw [hscl.work_stk2_len]; omega
                          c0_hsteps
                          exact hJu (ucnt + 1#64, ()) _
                            ⟨st.scratch.work_stk2.set ucnt.toNat not_uip,
                             by simp [hscl.work_stk2_len], by omega,
                             by rw [huc1]; exact bb_ws2_push_step huc_ws2 ⟨hnu_lt, hnu_ent⟩ huc_ok,
                             (by assumption)⟩
                        · c0_hsteps
                          exact hJu (ucnt, ()) mu ⟨st.scratch.work_stk2, hscl.work_stk2_len, huc_le,
                            huc_ok, hmu'⟩)
        · c0_hsteps
          exact hJbr (ucnt, keep, ci, false, ()) m1
            ⟨st, hbt, hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hm1⟩
      · c0_hsteps
        exact hJbr (ucnt, keep, ci, false, ()) m1
          ⟨st, hbt, hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hm1⟩
    · c0_hsteps
      exact hJbr (ucnt, keep, ci, false, ()) m1
        ⟨st, hbt, hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hm1⟩

/-- `full_backbone_m6` satisfies exact canonical **`FullM3Backbone.fullBackboneSpec`**. -/
theorem full_backbone_m6_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
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
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_backbone_m6_body
  -- Initial `if (h->cur_level != 0) full_backtrack(h, 0)`
  refine wp_join_group (ts := [])
    (fun _ m1 => ∃ (F_cur : List (List Nat)) (s1 : FullState),
      FullSparseInvW c F0 F_cur s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ _ m1 ⟨F_cur, s1, hsp1, hl0_1, hfu1, hm1⟩ => by
      have hcv1_le := hsp1.1.core_ok.cur_vars_le
      fvt_to_group
      -- Early exit join `Js` (`[]`): store `probing = 0`, return `1`
      refine wp_join_group (ts := []) (fun _ me => me = m1)
        (fun _ _ me heq => by
          subst heq; fvt_steps
          have hsp_e := bb_sparseW_with_probing hsp1 0#64
          exact hQ 1#64 _ _ ⟨⟨hsp_e.1, ⟨F_cur, hsp_e.2.1⟩⟩, hsp_e.2.2.1, hsp_e.2.2.2.1,
            hsp_e.2.2.2.2.1, hsp_e.2.2.2.2.2⟩ hl0_1 rfl hfu1 (Or.inl rfl)
            (fun h => by cases h) hm)
        (fun Jez hJez => by
          fvt_steps
          · exact hJez () m1 rfl
          · exact hJez () m1 rfl
          · exact hJez () m1 rfl
          · -- Active backbone: `probing := 1`, `full_propagate`, `prioritize`, `sched`
            let s1p : FullState := { s1 with core := { s1.core with probing := 1#64 } }
            have hsp1p : FullSparseInvW c F0 F_cur s1p := bb_sparseW_with_probing hsp1 1#64
            c0_call hProp
            refine ⟨c, F0, F_cur, s1p, R, rfl, hsp1p.1, hsp1p.2.1, hsp1p.2.2.2.2.2, hm,
              fun pr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel2 _ _ _ _ _ _ _ _ m2 hlen2 hw2 _
                hperm2 hfu2 _ _ hpr0 _ _ hm2 => ?_⟩
            have hsp2 : FullSparseInvW c F0 F_cur _ :=
              bb_sparseW_of_prop hsp1p rfl hlen2 hw2 hperm2
            have hfu2' : fuel2.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu2 hfu1
            fvt_steps
            · -- `pr0 == 1`: UNSAT at level 0
              have hsp_u := bb_sparseW_with_probing hsp2 0#64
              exact hQ 20#64 _ _ ⟨⟨hsp_u.1, ⟨F_cur, hsp_u.2.1⟩⟩, hsp_u.2.2.1, hsp_u.2.2.2.1,
                hsp_u.2.2.2.2.1, hsp_u.2.2.2.2.2⟩ hl0_1 rfl hfu2' (Or.inr rfl)
                (fun _ => level0_unsat_of_conflict_okW hw2 hl0_1 (hpr0 hc).2.2) hm
            · -- `pr0 == 2`: OOM / fuel exhausted
              have hsp_o := bb_sparseW_with_probing hsp2 0#64
              exact hQ 1#64 _ _ ⟨⟨hsp_o.1, ⟨F_cur, hsp_o.2.1⟩⟩, hsp_o.2.2.1, hsp_o.2.2.2.1,
                hsp_o.2.2.2.2.1, hsp_o.2.2.2.2.2⟩ hl0_1 rfl hfu2' (Or.inl rfl)
                (fun h => by cases h) hm
            · -- `pr0 == 0`: prioritize binaries + schedule candidates + multi-round loop
              c0_call hPrio
              refine ⟨c, F0, F_cur, _, R, rfl, hsp2, hm2,
                fun stop_early wstk3 scr3 m3 hsp3 hm3 => ?_⟩
              c0_call hSched
              refine ⟨c, F0, F_cur, _, R, rfl, hsp3, hm3,
                fun cand_n0 fl4 ws1_4 m4 hsp4 hcn0_le hlt0 hm4 => ?_⟩
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
                  have hsp_end := bb_sparseW_with_probing hspk 0#64
                  exact hQ res_f _ _ ⟨⟨hsp_end.1, ⟨F_cur, hsp_end.2.1⟩⟩, hsp_end.2.2.1,
                    hsp_end.2.2.2.1, hsp_end.2.2.2.2.1, hsp_end.2.2.2.2.2⟩ hclf rfl hfuf hdom
                    huns hm)
                (fun Jbr hJbr => ?_)
              -- Round loop `[i64, i64, i64]` = `(cand_n, res, round)`
              refine wp_loop_inv (ts := [i64, i64, i64])
                (fun (cn_r, res_r, rnd, ()) mr => ∃ sr : FullState, FullSparseInvW c F0 F_cur sr ∧
                  sr.core.cur_level = 0 ∧ sr.core.cur_vars = s1.core.cur_vars ∧
                  sr.core.fuel.toNat ≤ s.core.fuel.toNat ∧ rnd.toNat ≤ 100 ∧
                  cn_r.toNat ≤ 2 * sr.core.cur_vars ∧
                  (∀ i < cn_r.toNat, (sr.scratch.work_stk1[i]?.getD 0#32).toNat <
                    2 * sr.core.cur_vars) ∧
                  (res_r = 1#64 ∨ res_r = 20#64) ∧ (res_r = 20#64 → F0.Unsat) ∧
                  (FullMem c sr ⋆ R) mr)
                (fun (_, _, rnd, ()) _ => 100 - rnd.toNat) ?_ ?_
              · intro Jr hJr; fvt_steps
                exact hJr (cand_n0, 1#64, 0#64, ()) _
                  ⟨_, bb_sparseW_with_ant_sz hsp4 tick_lim, hl0_1, rfl, hfu2', Nat.zero_le _,
                   hcn0_le, hlt0, Or.inl rfl, (fun h => by cases h), hm⟩
              · rintro Jr ⟨cn_r, res_r, rnd, ⟨⟩⟩ mr
                  ⟨sr, hspr, hclr, hcvr, hfur, hrnd_le, hcnr_le, hltr, hdomr, hunsr, hmr⟩ ihr
                c0_hsplit
                · have hrnd_lt : rnd.toNat < 100 := by c0_bound
                  have hrnd1 : (rnd + 1#64).toNat = rnd.toNat + 1 := by bv_omega
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsplit
                      · c0_hsplit
                        · -- Body: call `full_backbone_round_m6`, install units, propagate
                          c0_hsteps_nogrp; c0_call hRound
                          refine ⟨c, F0, F_cur, sr, R, rfl, hspr, hclr, hcnr_le, hltr, hmr,
                            fun cn_n sn mn hspn hcln hcvn hfun hcnn_le hltn huc_le huc_ok
                              hmn => ?_⟩
                          have hcvn' : sn.core.cur_vars = s1.core.cur_vars := hcvn.trans hcvr
                          have hfun' : sn.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            rw [hfun]; exact hfur
                          c0_hsteps_nogrp
                          -- Join `Js_2` (`[i64]` = `res_n`) -> `round + 1`
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
                          · -- `ucnt > 0`: loop adding units + `full_propagate`
                            -- Break join `Js` (`[i64, i64]` = `(res_u, ui)`) after units loop
                            refine wp_join_group (ts := [i64, i64])
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
                                    fun pr1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel_p _ _ _ _ _ _ _ _ mp
                                      hlenp hwp _ hpermp hfup _ _ hpr1 _ _ hmp => ?_⟩
                                  have hspp : FullSparseInvW c F0 F_cur _ :=
                                    bb_sparseW_of_prop hspu rfl hlenp hwp hpermp
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
                                    ⟨_, bb_sparseW_with_delayed hsp_a _, hcl_a, hcvui, hfuui,
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

end BackboneTopProofs

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
