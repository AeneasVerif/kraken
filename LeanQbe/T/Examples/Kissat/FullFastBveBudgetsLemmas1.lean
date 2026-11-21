module

public import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
public import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
public import LeanQbe.T.Examples.Kissat.FullTransLemmas1
public import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M2 Tier-A BVE / Tarjan / Budgeted Inprocessing & Init-Hdr Proofs

Proves UNSAT-only `Func.wp` (`XPost := False`, `0` SAT model proofs), closed environment /
`SpecEntry.Impl` bridges, and concrete `Mem 64` UNSAT non-vacuity for all `7` upgraded functions
in `FullFastBveBudgets.lean`:
1. `full_init_hdr` (`probe_limit = 2000`, `elim_limit = 5000`, matching canonical `fullInitHdrSpec`)
2. `full_forward_sub(h, budget)` (`budget` param + early guard)
3. `full_transitive(h, tick_lim)` (`tick_lim` param + early guard)
4. `full_vivify(h, tier_mode, budget)` (`budget` param + early guard)
5. `full_probe_run(h, budget)` (early guard `budget == 0 || num_binary == 0`)
6. `full_tarjan_scc(h)` (zeroes `tmk`/`trc` at exit, establishing `TmkZero`)
7. `full_bve_var(h, v)` (`64u` occ cap + `P_ng × N_ng` gate-skip rule with `FullDefGateUnsat`
   and `TmkZero` compatibility, plus canonical `fullBveVarSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFastBveBudgets

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `TmkZero`, `FullDefGateUnsat`, & Upgraded `Spec` Contracts -/

section SpecsAndGateSoundness

/-- Zero-initialized `tarjan_mark[0 ..< cur_vars)` required on entry to `full_find_definition`
and `full_sweep_cone` (`FullDefSweep`-compatible). -/
def TmkZero (s : FullState) : Prop :=
  ∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0#32

theorem TmkZero.congr {s s' : FullState} (h : TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (ht : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : TmkZero s' := by
  intro v hv; rw [ht]; exact h v (hcv ▸ hv)

/-- Rest literals of an occurrence entry `w` after stripping `except`. -/
def bveOccRestLits (s : FullState) (except : Nat) (w : BitVec 32) : List Nat :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    [(w &&& 0x7FFFFFFF#32).toNat]
  else
    (fullArenaClauseLits s w.toNat).filter (· != except)

/-- Unit clauses `[l ^^^ 1]` forced at level 0 in `s.core.vals`. -/
def level0ForcedUnits (s : FullState) : List (List Nat) :=
  (List.range (2 * s.core.cur_vars)).filterMap fun l =>
    if s.core.vals[l]?.getD 0#8 = 0xFF#8 then some [l ^^^ 1] else none

/-- Subset of occurrence clauses selected by `mask` in `scr[off ..< off + cnt)`. -/
def maskedOccRestCls (s : FullState) (except off cnt : Nat) (mask : BitVec 64) :
    List (List Nat) :=
  (List.range cnt).filterMap fun i =>
    if (mask >>> i) &&& 1#64 ≠ 0#64 then
      some (bveOccRestLits s except (s.scratch.scratch_buf[off + i]?.getD 0#32))
    else none

/-- Semantic definition/gate soundness certificate (`FullDefSweep`-compatible): the selected
positive gate bodies `P_g`, negative gate bodies `N_g`, and level-0 forced units are jointly
unsatisfiable. -/
def FullDefGateUnsat (s : FullState) (v : Nat) (pmask nmask : BitVec 64) (np nn : Nat) :
    Prop :=
  np ≤ 64 ∧ nn ≤ 64 ∧ (pmask ≠ 0#64 ∨ nmask ≠ 0#64) →
  (pmask >>> np) = 0#64 ∧ (nmask >>> nn) = 0#64 ∧
  (cnfOfClauses (level0ForcedUnits s ++
    maskedOccRestCls s (2 * v) 0 np pmask ++
    maskedOccRestCls s (2 * v + 1) 64 nn nmask)).Unsat

theorem fullDefGateUnsat_zero (s : FullState) (v np nn : Nat) :
    FullDefGateUnsat s v 0#64 0#64 np nn := by
  rintro ⟨_, _, h⟩; exact absurd h (by simp)

private theorem eval_clause_no_v {v : Nat} {cl : List Nat} (α : Nat → Bool) (b : Bool)
    (hnov : ∀ l ∈ cl, l / 2 ≠ v) :
    (cnfClause cl).Sat (fun x => if x = v then b else α x) ↔ (cnfClause cl).Sat α := by
  simp only [clause_sat_cnfClause_iff, litVar, litSign]
  constructor <;> rintro ⟨l, hl, hsat⟩ <;> refine ⟨l, hl, ?_⟩ <;>
    (have hne : l / 2 ≠ v := hnov l hl; simpa [hne] using hsat)

/-- Pure SAT extension soundness for gate-restricted BVE skipping `P_ng × N_ng`
(`FullDefSweep`-compatible). -/
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
      rw [CNF.unsat_iff_not_sat] at hGateUnsat
      apply hGateUnsat α
      rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
      simp only [List.mem_append, List.mem_filterMap, List.mem_range] at hcl
      rcases hcl with (huc | ⟨i, ⟨hi, hite⟩⟩) | ⟨j, ⟨hj, hite⟩⟩
      · exact hU cl huc
      · split at hite
        · rename_i hpgi; cases Option.some.inj hite
          have hs := hResSat i j0 hi hj0 (Or.inl hpgi)
          rw [List.getElem?_eq_getElem hi, Option.getD_some]
          rw [clause_sat_cnfClause_iff] at hs ⊢
          obtain ⟨l, hl, hsl⟩ := hs; rw [List.mem_append] at hl
          exact hl.elim (fun h1 => ⟨l, h1, hsl⟩)
            (fun h2 => absurd ((clause_sat_cnfClause_iff α _).mpr ⟨l, h2, hsl⟩) hnj0)
        · cases hite
      · split at hite
        · rename_i hngj; cases Option.some.inj hite
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
    obtain ⟨lp, hlp, hsp⟩ := hPos; obtain ⟨ln, hln, hsn⟩ := hNeg
    rcases List.mem_cons.mp hlp with rfl | hlp'
    · rcases List.mem_cons.mp hln with rfl | hln'
      · exfalso; simp only [litVar, litSign] at hsp hsn
        have hdv0 : (2 * v) / 2 = v := by omega
        have hdv1 : (2 * v + 1) / 2 = v := by omega
        have hm0 : (2 * v) % 2 = 0 := by omega
        have hm1 : (2 * v + 1) % 2 = 1 := by omega
        rw [hdv0, hm0] at hsp; rw [hdv1, hm1] at hsn
        cases hb : α v <;> simp [hb] at hsp hsn
      · exact ⟨ln, List.mem_append_right _ hln', hsn⟩
    · exact ⟨lp, List.mem_append_left _ hlp', hsp⟩

/-- Full equisatisfiability for gate-restricted BVE skipping `P_ng × N_ng`. -/
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

/-- `ExtUnsatSound` preservation for gate-restricted BVE skipping `P_ng × N_ng`. -/
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

/-- Upgraded `full_init_hdr` spec certifying tuned `probe_limit = 2000` and `elim_limit = 5000`
(strictly refines canonical `Full.fullInitHdrSpec`). -/
def fullFastInitHdrSpec : Spec [i64, i64, i64, i64] [] := fun (h, mv, max_v, fuel, ()) m Q _ =>
  ∃ (c : FullCfg) (ws : List (BitVec 64)) (R : Mem 64 → Prop),
    h = c.hdr ∧ mv = BitVec.ofNat 64 c.mv ∧ max_v = BitVec.ofNat 64 c.max_vars ∧
    ws.length = 140 ∧
    (∀ (s0 : FullState),
      ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
              41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
              102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113],
        ws[i]? = (Full.hdrTailWords c s0)[i]?) ∧
    (array64 (c.hdr + 32) ws ⋆ R) m ∧
    ∀ (s : FullState) m',
      s.core.cur_vars = c.mv → s.core.arena_len = 0 → s.core.wlen = 1 →
      s.core.trail_end = 0 → s.core.propagated = 0 → s.core.cur_level = 0 →
      s.core.tmp_len = 0 → s.core.fuel = fuel → s.core.unflushed = 0#64 →
      s.core.probing = 0#64 → s.core.min_clr_len = 0 → s.core.min_clr_full = 0#64 →
      s.core.oom = 0#64 → s.core.dense_mode = 0#64 → s.core.inconsistent = 0#64 →
      s.scratch.extend_len = 0 →
      s.scratch.probe_limit = 2000#64 → s.scratch.elim_limit = 5000#64 →
      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ R) m' → Q () m'

theorem fullFastInitHdrSpec_of_canon {a m Q X} (h : Full.fullInitHdrSpec a m Q X) :
    fullFastInitHdrSpec a m Q X := by
  rcases a with ⟨h_ptr, mv, max_v, fuel, ⟨⟩⟩
  rcases h with ⟨c, ws, R, h1, h2, h3, h4, h5, hm, hQ⟩
  exact ⟨c, ws, R, h1, h2, h3, h4, h5, hm, fun s m' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    a14 a15 a16 _ _ hm' => hQ s m' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 hm'⟩

/-- Upgraded `full_probe_run(h, budget)` spec with early exit `budget == 0 || num_binary == 0`. -/
def fullProbeRunFastSpec : Spec [i64, i64] [i64] := fun (h, budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      (budget ≠ 0#64 → s.core.num_binary ≠ 0#64 →
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Upgraded `full_transitive(h, tick_lim)` spec (`2` args + early exit). -/
def fullTransitiveFastSpec : Spec [i64, i64] [i64] := fun (h, tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      (s.core.num_binary ≠ 0#64 → tick_lim ≠ 0#64 →
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Upgraded `full_vivify(h, tier_mode, budget)` spec (`3` args + early exit). -/
def fullVivifyFastSpec : Spec [i64, i64, i64] [i64] := fun (h, _tier_mode, budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      (budget ≠ 0#64 → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Upgraded `full_tarjan_scc(h)` spec certifying zeroed `tarjan_mark` / `tarjan_reach` (`TmkZero`)
on exit (strictly refines canonical `Full.fullTarjanSccSpec`). -/
def fullTarjanSccFastSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r repr' tc' inc' tmk' trc' ws1' ws2' wsort' sstk' rsz' m',
      let s' : FullState :=
        { s with
          core := { s.core with repr := repr', tmp_cnt := tc', inconsistent := inc' }
          scratch := { s.scratch with tarjan_mark := tmk', tarjan_reach := trc',
                                      work_stk1 := ws1', work_stk2 := ws2', wsort := wsort',
                                      shrink_stk := sstk', res_sz := rsz' } }
      FullSparseInvW c F0 F_cur s' → r.toNat ≤ c.max_vars →
      (∀ k < r.toNat,
        (sstk'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [(sstk'[k]?.getD 0#32).toNat])) →
      (inc' = 0#64 → FullReprEquiv F_cur s') →
      (∀ l < 2 * s.core.cur_vars,
        tmk'[l]?.getD 0#32 = 0#32 ∧ trc'[l]?.getD 0#32 = 0#32) →
      TmkZero s' →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullTarjanSccFastSpec_of_canon {a m Q X} (h : Full.fullTarjanSccSpec a m Q X) :
    fullTarjanSccFastSpec a m Q X := by
  rcases a with ⟨h_ptr, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, s, R, rfl, hsp, hcl0, hm, hQ⟩
  exact ⟨c, F0, F_cur, s, R, rfl, hsp, hcl0, hm,
    fun r repr' tc' inc' tmk' trc' ws1' ws2' wsort' sstk' rsz' m' h1 h2 h3 h4 _ _ hm' =>
      hQ r repr' tc' inc' tmk' trc' ws1' ws2' wsort' sstk' rsz' m' h1 h2 h3 h4 hm'⟩

/-- Upgraded `full_forward_sub(h, budget)` spec (`2` args + early exit). -/
def fullForwardSubFastSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `FullDefGateUnsat`-carrying `full_bve_gates` contract for M2 `FullDefSweep` wiring
(preserves `FullDenseInvW`, `TmkZero`, `cur_vars`, `arena`, `arena_len`, `fuel ≤`, and
`scr[0..127]`). -/
def fullBveGatesDefFastSpec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
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
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < 128, scr'[i]? = s.scratch.scratch_buf[i]?) →
      FullDefGateUnsat s v.toNat pmask nmask np.toNat nn.toNat →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `TmkZero`-preserving `full_bve_weaken` contract for M2 `FullDefSweep` wiring. -/
def fullBveWeakenTmkSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, blk_lit, off, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ blk_lit.toNat < 2 * s.core.cur_vars ∧
      off.toNat + cnt.toNat ≤ c.scratch_cap ∧
      (∀ i < cnt.toNat,
        FullBveWeakItemOk s.core (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel = s.core.fuel → s'.scratch.scratch_buf = s.scratch.scratch_buf →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `TmkZero`-preserving `full_bve_commit_res` contract for M2 `FullDefSweep` wiring. -/
def fullBveCommitResTmkSpec : Spec [i64, i64, i64] [i64] := fun (h, r_off, r_end, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ r_off.toNat ≤ r_end.toNat ∧
    r_end.toNat ≤ c.scratch_cap ∧ FullResBufOkW F_cur s r_end.toNat r_off.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `TmkZero`-preserving `full_extend_push2` contract for M2 `FullDefSweep` wiring. -/
def fullExtendPush2TmkSpec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _ot, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧ s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark)

/-- `TmkZero`-preserving `full_extend_push_cl` contract for M2 `FullDefSweep` wiring. -/
def fullExtendPushClTmkSpec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _cref, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧ s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark)

/-- `TmkZero`-preserving `full_bve_var` contract for M2 `FullDefSweep` wiring. -/
def fullBveVarDefSpec : Spec [i64, i32] [i64] := fun (h, v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ TmkZero s ∧ v.toNat < s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → TmkZero s' → s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end SpecsAndGateSoundness

/-! ## 2. `fast_init_hdr_wp` (`probe_limit = 2000`, `elim_limit = 5000`) -/

section InitHdrProof

open FullParseInitSpecs FullParseInitHelpers
open scoped FullArenaTactics FullParseInitTactics

private def hdrW3Fast (mv : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  let rng := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 mv + 1#64)
  ((((((((((((((((((((((((((w3.set 5 0#64).set 9 rng).set 10 100#64).set 11 0#64).set
    12 0#64).set 13 2000#64).set 14 0#64).set 15 5000#64).set 16 0#64).set 17 0#64).set
    18 0#64).set 19 0#64).set 20 0#64).set 21 0#64).set 22 0#64).set 23 0#64).set
    24 0#64).set 25 0#64).set 26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set
    30 0#64).set 31 0#64).set 32 0#64).set 33 0#64).set 34 0#64

private theorem hdrW3Fast_len {mv : Nat} {w : List (BitVec 64)} :
    (hdrW3Fast mv w).length = w.length := by simp [hdrW3Fast]

private theorem len_cons10 {α} (xs : List α) (n : Nat) (h : xs.length = n + 10) :
    ∃ a b c d e f g h1 i j ys, ys.length = n ∧
      xs = a :: b :: c :: d :: e :: f :: g :: h1 :: i :: j :: ys := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h1, _ | ⟨i, _ |
    ⟨j, ys⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, f, g, h1, i, j, ys, h, rfl⟩

private theorem decompose35 {α} (xs : List α) (h : xs.length = 35) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 d0 d1 d2 d3 d4 : α,
      xs = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
            c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, xs1, h1, rfl⟩ := len_cons10 xs 25 h
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, xs2, h2, rfl⟩ := len_cons10 xs1 15 h1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, xs3, h3, rfl⟩ := len_cons10 xs2 5 h2
  rcases xs3 with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | ⟨d4, _ | _⟩⟩⟩⟩⟩ <;> simp at h3
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩

private def initHdrFastWitness (c : FullCfg) (fuel : BitVec 64) : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := c.mv, unassigned := BitVec.ofNat 64 c.mv
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0xFFFFFFFF#64, num_irred := 0#64, num_redundant := 0#64
        num_binary := 0#64, unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
        cur_level := 0, fuel := fuel, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64
        confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0
        min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
        vals := [], lit_mark := [], mrk := [], flags := [], lvl := [], rsns := [], trl := []
        trail_pos := [], tmp := [], min_clr := [], frame_trail := [], frame_dec := [], wvec := []
        repr := [], min_stk := [], arena := [], wstk := [] }
    scratch :=
      { heap_len := c.mv, scinc := 1#64 <<< 28, rel_period := 1024#64
        rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64
        rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64
        delayed_len := 0, stable := 0#64, switched := 0#64, mode_count := 0#64
        mode_confl_lim := 1000#64, mode_tick_lim := 0#64, mode_saved_ticks := 0#64
        search_ticks := 0#64
        q_first := if c.mv = 0 then 0xFFFFFFFF#64 else 0#64
        q_last := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_idx := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_stamp := BitVec.ofNat 64 c.mv, q_cur_stamp := BitVec.ofNat 64 c.mv
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64
        ema_fast_exp := 1#64 <<< 24, ema_slow_biased := 0#64, ema_slow_exp := 1#64 <<< 24
        extend_len := 0, rng_state := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 c.mv + 1#64)
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 2000#64
        probings := 0#64, elim_limit := 5000#64, eliminations := 0#64, elim_bound := 0#64
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64, subst_cnt := 0#64
        cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64
        walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64
        res_sz := 0#64, walk_vals := [], phases := [], phases_target := [], phases_best := []
        walk_best := [], heap := [], pos := [], shrink_stk := [], q_prev := [], q_next := []
        q_stamp := [], wsort := [], work_stk1 := [], work_stk2 := [], tarjan_mark := []
        tarjan_reach := [], score := [], sim_sig := [], glue_used := [], last_learned := []
        delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] } }

local macro "fpi_jnz_t" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_true_eq] at $h:ident; fp_head_steps))
local macro "fpi_jnz_f" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_false_iff_not] at $h:ident; fp_head_steps))

private theorem fast_init_hdr4_wp (Γ : Env) {h mv max_v fuel : BitVec 64}
    {w0 w1 w2 w3 : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hle : mv.toNat ≤ max_v.toNat) (hmx : max_v.toNat < 2 * dimacsBound)
    (hm : (hdrTail4 h w0 w1 w2 w3 ⋆ R) m)
    (hQ : ∀ m', (hdrTail4 h (hdrW0 mv.toNat fuel w0) (hdrW1 w1)
      (hdrW2 mv.toNat max_v.toNat w2) (hdrW3Fast mv.toNat w3) ⋆ R) m' → Q () m') :
    Func.wp Γ full_init_hdr_body (h, mv, max_v, fuel, ()) m Q X := by
  have hmx' := hmx; unfold dimacsBound at hmx'
  let q0 := if mv.toNat = 0 then 0xFFFFFFFF#64 else 0#64
  let ql := if mv.toNat = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (mv.toNat - 1)
  have hmv0 : (mv == (0 : BitVec 64)) = decide (mv.toNat = 0) := by
    by_cases hz : mv.toNat = 0
    · have he : mv = 0#64 := BitVec.eq_of_toNat_eq hz; simp [he]
    · have hne : mv ≠ 0#64 := fun h => hz (by simp [h]); simp [hz, hne]
  have hsub_bva : max_v - mv = BitVec.ofNat 64 (max_v.toNat - mv.toNat) := by
    apply BitVec.eq_of_toNat_eq; have := max_v.isLt; have := mv.isLt
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsub_mv1 : mv.toNat ≠ 0 → mv - 1#64 = BitVec.ofNat 64 (mv.toNat - 1) := fun hnz => by
    apply BitVec.eq_of_toNat_eq; have := mv.isLt
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsh28 : (1 : BitVec 64) <<< (((28 : BitVec 32).signExtend 64).toNat % 64) =
      (1#64 <<< 28) := rfl
  have hsh24 : (1 : BitVec 64) <<< (((24 : BitVec 32).signExtend 64).toNat % 64) =
      (1#64 <<< 24) := rfl
  unfold Func.wp full_init_hdr_body
  fp_head_steps
  refine wp_join_group (fun (v : Tup Val [i64]) mqf => v.1 = q0 ∧ mqf = m) ?_ ?_
  · rintro _ ⟨qf, ⟨⟩⟩ mqf ⟨rfl, rfl⟩
    simp only [Blocks.get_here]; fp_head_steps
    refine wp_join_group (fun (v : Tup Val [i64]) mql => v.1 = ql ∧ mql = m) ?_ ?_
    · rintro _ ⟨qlv, ⟨⟩⟩ mql ⟨rfl, rfl⟩
      simp only [Blocks.get_here]; fp_head_steps
      refine wp_join_group (fun (v : Tup Val [i64]) mqsi => v.1 = ql ∧ mqsi = m) ?_ ?_
      · rintro _ ⟨qsi, ⟨⟩⟩ mqsi ⟨rfl, rfl⟩
        simp only [Blocks.get_here]; fp_head_steps
        rw [hsub_bva, hsh28, hsh24] at hm
        unfold hdrW0 hdrW1 hdrW2 hdrW3Fast at hQ
        rw [bv_ofNat_toNat_eq mv, bv_ofNat_toNat_eq max_v] at hQ
        exact hQ m hm
      · intro J3 hJ3; fp_head_steps; rw [hmv0]
        refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
        · fpi_jnz_t ht; exact hJ3 (_, ()) m ⟨by dsimp [ql]; simp only [ht, ↓reduceIte], rfl⟩
        · fpi_jnz_f hf; refine hJ3 (_, ()) m ⟨?_, rfl⟩
          dsimp [ql]; rw [ite_eq_right_iff.mpr (fun h => absurd h hf), hsub_mv1 hf]
    · intro J2 hJ2; fp_head_steps; rw [hmv0]
      refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
      · fpi_jnz_t ht; exact hJ2 (_, ()) m ⟨by dsimp [ql]; simp only [ht, ↓reduceIte], rfl⟩
      · fpi_jnz_f hf; refine hJ2 (_, ()) m ⟨?_, rfl⟩
        dsimp [ql]; rw [ite_eq_right_iff.mpr (fun h => absurd h hf), hsub_mv1 hf]
  · intro J1 hJ1; fp_head_steps; rw [hmv0]
    refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
    · fpi_jnz_t ht; exact hJ1 (_, ()) m ⟨by dsimp [q0]; simp only [ht, ↓reduceIte], rfl⟩
    · fpi_jnz_f hf; exact hJ1 (_, ()) m ⟨by
        dsimp [q0]; rw [ite_eq_right_iff.mpr (fun h => absurd h hf)], rfl⟩

private theorem hdrW0_fast_eq (c : FullCfg) (fuel : BitVec 64) (w0 : List (BitVec 64))
    (h0 : w0.length = 35)
    (hw : ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      w0[i]? = (hdrTailWords0 c (initHdrFastWitness c fuel))[i]?) :
    hdrW0 c.mv fuel w0 = hdrTailWords0 c (initHdrFastWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w0 h0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e4 := hw 4 (by simp)
  have e5 := hw 5 (by simp); have e6 := hw 6 (by simp); have e7 := hw 7 (by simp)
  have e8 := hw 8 (by simp); have e9 := hw 9 (by simp); have e10 := hw 10 (by simp)
  have e11 := hw 11 (by simp); have e12 := hw 12 (by simp); have e13 := hw 13 (by simp)
  have e21 := hw 21 (by simp); have e22 := hw 22 (by simp); have e23 := hw 23 (by simp)
  have e24 := hw 24 (by simp); have e25 := hw 25 (by simp); have e26 := hw 26 (by simp)
  have e29 := hw 29 (by simp)
  simp only [hdrTailWords0, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e21 e22 e23 e24 e25 e26 e29
  simp [hdrW0, hdrTailWords0, initHdrFastWitness, e0, e1, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e21, e22, e23, e24, e25, e26, e29]

private theorem hdrW1_fast_eq (c : FullCfg) (fuel : BitVec 64) (w1 : List (BitVec 64))
    (h1 : w1.length = 35)
    (hw : ∀ i ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      w1[i]? = (hdrTailWords1 c (initHdrFastWitness c fuel))[i]?) :
    hdrW1 w1 = hdrTailWords1 c (initHdrFastWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w1 h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e6 := hw 6 (by simp); have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  have e9 := hw 9 (by simp); have e10 := hw 10 (by simp); have e11 := hw 11 (by simp)
  have e12 := hw 12 (by simp); have e13 := hw 13 (by simp); have e14 := hw 14 (by simp)
  have e15 := hw 15 (by simp); have e16 := hw 16 (by simp); have e17 := hw 17 (by simp)
  simp only [hdrTailWords1, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
  simp [hdrW1, hdrTailWords1, initHdrFastWitness, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    e16, e17]

private theorem hdrW2_fast_eq (c : FullCfg) (fuel : BitVec 64) (w2 : List (BitVec 64))
    (h2 : w2.length = 35)
    (hw : ∀ i ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      w2[i]? = (hdrTailWords2 c (initHdrFastWitness c fuel))[i]?) :
    hdrW2 c.mv c.max_vars w2 = hdrTailWords2 c (initHdrFastWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w2 h2
  have hbva : c.max_vars - c.mv = c.bva_cap := by have := c.hbva; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e26 := hw 26 (by simp); have e27 := hw 27 (by simp); have e28 := hw 28 (by simp)
  have e29 := hw 29 (by simp); have e30 := hw 30 (by simp); have e31 := hw 31 (by simp)
  have e32 := hw 32 (by simp); have e33 := hw 33 (by simp); have e34 := hw 34 (by simp)
  simp only [hdrTailWords2, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e26 e27 e28 e29 e30 e31 e32 e33 e34
  simp [hdrW2, hdrTailWords2, initHdrFastWitness, hbva, e26, e27, e28, e29, e30, e31, e32, e33,
    e34]

private theorem hdrW3_fast_eq (c : FullCfg) (fuel : BitVec 64) (w3 : List (BitVec 64))
    (h3 : w3.length = 35)
    (hw : ∀ i ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      w3[i]? = (hdrTailWords3 c (initHdrFastWitness c fuel))[i]?) :
    hdrW3Fast c.mv w3 = hdrTailWords3 c (initHdrFastWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w3 h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e2 := hw 2 (by simp)
  have e3 := hw 3 (by simp); have e4 := hw 4 (by simp); have e6 := hw 6 (by simp)
  have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  simp only [hdrTailWords3, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e2 e3 e4 e6 e7 e8
  simp [hdrW3Fast, hdrTailWords3, initHdrFastWitness, e0, e1, e2, e3, e4, e6, e7, e8]

theorem fast_init_hdr_wp (Γ : Env) :
    ∀ a m Q X, fullFastInitHdrSpec a m Q X → Func.wp Γ full_init_hdr_body a m Q X := by
  rintro ⟨h, mv, max_v, fuel, ⟨⟩⟩ m Q X ⟨c, ws, R, rfl, rfl, rfl, hw, hws, hm, hQ⟩
  let s0 := initHdrFastWitness c fuel
  have hws0 := hws s0
  have hmv' := c.hmv; have hmx' := c.hmaxv; unfold dimacsBound at hmv' hmx'
  have hmv_to : (BitVec.ofNat 64 c.mv).toNat = c.mv := bv64_ofNat_toNat (by omega)
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have h0l : w0.length = 35 := by simp [w0, hw]
  have h1l : w1.length = 35 := by simp [w1, hw]
  have h2l : w2.length = 35 := by simp [w2, hw]
  have h3l : w3.length = 35 := by simp [w3, hw]
  have hw_len0 : (hdrTailWords0 c s0).length = 35 := by simp [hdrTailWords0]
  have hw_len1 : (hdrTailWords1 c s0).length = 35 := by simp [hdrTailWords1]
  have hw_len2 : (hdrTailWords2 c s0).length = 35 := by simp [hdrTailWords2]
  refine fast_init_hdr4_wp Γ (by rw [hmv_to, hmx_to]; have := c.hbva; omega)
    (by rw [hmx_to]; exact c.hmaxv) (array64_to_hdrTail4 hw hm) fun m' hm' => ?_
  rw [hmv_to, hmx_to] at hm'
  have hm_arr : (array64 (c.hdr + 32) (hdrW0 c.mv fuel w0 ++ hdrW1 w1 ++
      hdrW2 c.mv c.max_vars w2 ++ hdrW3Fast c.mv w3) ⋆ R) m' := by
    rwa [hdrTail4_eq_array64 (by rw [hdrW0_len]; exact h0l) (by rw [hdrW1_len]; exact h1l)
      (by rw [hdrW2_len]; exact h2l) (by rw [hdrW3Fast_len]; exact h3l)] at hm'
  have hi0 : ∀ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      j < 35 ∧ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi1 : ∀ j ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      j < 35 ∧ (35 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi2 : ∀ j ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      j < 35 ∧ (70 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi3 : ∀ j ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      j < 35 ∧ (105 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have heq0 : hdrW0 c.mv fuel w0 = hdrTailWords0 c s0 := hdrW0_fast_eq c fuel w0 h0l fun i hi => by
    have ⟨hi', hm'⟩ := hi0 i hi; have hgi := hws0 i hm'
    dsimp only [w0]; rw [List.getElem?_take_of_lt hi', hgi]
    unfold Full.hdrTailWords; exact append4_getElem?_0 hw_len0 hi'
  have heq1 : hdrW1 w1 = hdrTailWords1 c s0 := hdrW1_fast_eq c fuel w1 h1l fun i hi => by
    have ⟨hi35, hm'⟩ := hi1 i hi; have hgi := hws0 (35 + i) hm'
    dsimp only [w1]; rw [drop_take_getElem? ws 35 35 i hi35, hgi]
    unfold Full.hdrTailWords
    rw [append4_getElem?_1 hw_len0 hw_len1 (by omega) (by omega), show 35 + i - 35 = i by omega]
  have heq2 : hdrW2 c.mv c.max_vars w2 = hdrTailWords2 c s0 :=
    hdrW2_fast_eq c fuel w2 h2l fun i hi => by
      have ⟨hi35, hm'⟩ := hi2 i hi; have hgi := hws0 (70 + i) hm'
      dsimp only [w2]; rw [drop_take_getElem? ws 70 35 i hi35, hgi]
      unfold Full.hdrTailWords
      rw [append4_getElem?_2 hw_len0 hw_len1 hw_len2 (by omega) (by omega),
        show 70 + i - 70 = i by omega]
  have heq3 : hdrW3Fast c.mv w3 = hdrTailWords3 c s0 := hdrW3_fast_eq c fuel w3 h3l fun i hi => by
    have ⟨hi35, hm'⟩ := hi3 i hi; have hgi := hws0 (105 + i) hm'
    dsimp only [w3]; rw [drop_take_getElem? ws 105 35 i hi35, hgi]
    unfold Full.hdrTailWords
    rw [append4_getElem?_3 hw_len0 hw_len1 hw_len2 (by omega), show 105 + i - 105 = i by omega]
  rw [heq0, heq1, heq2, heq3] at hm_arr
  change (array64 (c.hdr + 32) (Full.hdrTailWords c s0) ⋆ R) m' at hm_arr
  exact hQ s0 m' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm_arr

theorem fast_init_hdr_canon_wp (Γ : Env) :
    ∀ a m Q X, Full.fullInitHdrSpec a m Q X → Func.wp Γ full_init_hdr_body a m Q X :=
  fun _ _ _ _ h => fast_init_hdr_wp Γ _ _ _ _ (fullFastInitHdrSpec_of_canon h)

end InitHdrProof

/-! ## 3. `fast_forward_sub_wp` (`u64 budget` parameter + early exit) -/

section ForwardSubProof

open FullBvaFwdHelpers
open scoped FullArenaTactics FullBvaFwdTactics

private theorem zero_mem_arenaRefs_of_pos {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    cases hal : k.arena_len with
    | zero => omega
    | succ n =>
      rw [fullArenaScanRefs]
      have hle : 0 + 3 ≤ n + 1 := by omega
      simp [hle]

theorem fast_forward_sub_wp (Γ : Env)
    (hDedup : ∀ args m Q X, fullFwdDedupBinsSpec args m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] args m Q X)
    (hArenaNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hCheckCl : ∀ args m Q X, fullFwdCheckClSpec args m Q X →
      Γ "full_fwd_check_cl" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullForwardSubFastSpec args m Q X →
      Func.wp Γ full_forward_sub_body args m Q X := by
  rintro ⟨h, budget0, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have har_cap := c.harena; unfold dimacsBound at har_cap
  bf_steps
  obtain ⟨F_cur, hw⟩ := hinv.1.witness
  c0_call hDedup
  refine ⟨c, F0, F_cur, s, R, rfl, ⟨hinv.1.lengths, hw, hinv.2⟩, hm,
    fun ok s1 m1 hinv1W hcv1 hfuel1 hfalse1 hm1 => ?_⟩
  have hinv1 := hinv1W.toDense
  bf_steps
  · -- `ok = true`, `budget0 == 0ULL` -> early return `1ULL`
    exact hQ 1#64 s1 m1 hinv1 hcv1 hfuel1 (Or.inl rfl) (by simp) hm1
  · -- `ok = true`, `budget0 ≠ 0ULL` -> main loop
    refine wp_loop_inv
      (fun (budget, p, ()) ml => ∃ st : FullState,
        FullDenseInv c F0 st ∧ st.core.cur_vars = s.core.cur_vars ∧
        st.core.fuel = s.core.fuel ∧ p.toNat ≤ st.core.arena_len ∧
        (p.toNat = st.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs st) ∧
        (FullMem c st ⋆ R) ml)
      (fun (_, p, _) _ => c.arena_cap - p.toNat)
      (fun J hJ => by
        bf_steps
        obtain ⟨F1, hw1⟩ := hinv1.1.witness
        refine hJ (budget0, 0#64, ()) m1 ⟨s1, hinv1, hcv1, hfuel1, Nat.zero_le _, ?_, hm1⟩
        by_cases hz : s1.core.arena_len = 0
        · exact Or.inl hz.symm
        · exact Or.inr (zero_mem_arenaRefs_of_pos hw1.arena (Nat.pos_of_ne_zero hz)))
      (fun J (budget, p, ()) ml ⟨st, hst, hcv_st, hfuel_st, hp_le, hp_mem, hml⟩ ih => ?_)
    have hlen_st := hst.1.lengths.core_ok
    have hal_le := hlen_st.arena_len_le
    have hal_arr := hlen_st.arena_len_arr
    obtain ⟨F_st, hw_st⟩ := hst.1.witness
    bf_steps
    · have hp_lt : p.toNat < st.core.arena_len := by c0_bound
      have hp_ref : p.toNat ∈ fullArenaClauseRefs st := hp_mem.resolve_left (by omega)
      have hwf_p := hw_st.arena.refs_wf p.toNat hp_ref
      have hp2_lt : p.toNat + 2 < st.core.arena.length := by omega
      have hp32 : (p.truncate 32).toNat = p.toNat := by
        rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
      bf_steps
      c0_call hArenaNext
      refine ⟨c, st, R, rfl, hst.1.lengths, hml, ?_⟩
      have hnb := fullArenaNextOff_bounds (ar := st.core.arena) (alen := st.core.arena_len)
        (cref := p.toNat) hwf_p.1
      have hnp_mem := fullArenaClauseRefs_next_mem hw_st.arena hp_ref
      have hnp_lt32 : fullArenaNextOff st.core.arena st.core.arena_len p.toNat < 2 ^ 32 := by omega
      have hnp_toNat : (BitVec.zeroExtend 64
          (BitVec.ofNat 32 (fullArenaNextOff st.core.arena st.core.arena_len
            (p.truncate 32).toNat))).toNat =
          fullArenaNextOff st.core.arena st.core.arena_len p.toNat := by
        rw [hp32, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hnp_lt32, Nat.mod_eq_of_lt (by omega)]
      bf_steps
      · c0_call hCheckCl
        refine ⟨c, F0, F_st, st, R, rfl, ⟨hst.1.lengths, hw_st, hst.2⟩, by rw [hp32]; exact hp_ref,
          hml, fun ok2 st2 m2 hst2W hcv2 hal2 hfuel2 hrefs2 hfalse2 hm2 => ?_⟩
        have hst2 := hst2W.toDense
        bf_steps
        · refine ih _ _ (by dsimp only; rw [hnp_toNat]; omega)
            ⟨st2, hst2, hcv2.trans hcv_st, hfuel2.trans hfuel_st, by rw [hnp_toNat, hal2]; omega,
             by rw [hnp_toNat, hal2, hrefs2]; exact hnp_mem, hm2⟩
        · exact hQ 20#64 st2 m2 hst2 (hcv2.trans hcv_st) (hfuel2.trans hfuel_st)
            (Or.inr rfl) (fun _ => hfalse2 hc) hm2
      · refine ih _ _ (by dsimp only; rw [hnp_toNat]; omega)
          ⟨st, hst, hcv_st, hfuel_st, by rw [hnp_toNat]; omega,
           by rw [hnp_toNat]; exact hnp_mem, hml⟩
      · refine ih _ _ (by dsimp only; rw [hnp_toNat]; omega)
          ⟨st, hst, hcv_st, hfuel_st, by rw [hnp_toNat]; omega,
           by rw [hnp_toNat]; exact hnp_mem, hml⟩
      · refine ih _ _ (by dsimp only; rw [hnp_toNat]; omega)
          ⟨st, hst, hcv_st, hfuel_st, by rw [hnp_toNat]; omega,
           by rw [hnp_toNat]; exact hnp_mem, hml⟩
    · exact hQ 20#64 st ml hst hcv_st hfuel_st (Or.inr rfl)
        (fun _ => hst.1.inconsistent_unsat hc) hml
    · exact hQ 20#64 st ml hst hcv_st hfuel_st (Or.inr rfl)
        (fun _ => hst.1.inconsistent_unsat hc) hml
    · exact hQ 1#64 st ml hst hcv_st hfuel_st (Or.inl rfl) (by simp) hml
    · exact hQ 20#64 st ml hst hcv_st hfuel_st (Or.inr rfl)
        (fun _ => hst.1.inconsistent_unsat hc) hml
    · exact hQ 1#64 st ml hst hcv_st hfuel_st (Or.inl rfl) (by simp) hml
  · exact hQ 20#64 s1 m1 hinv1 hcv1 hfuel1 (Or.inr rfl) (fun _ => hfalse1 hc) hm1

end ForwardSubProof

/-! ## 4. `fast_transitive_wp` (`u64 tick_lim` parameter + early exit) -/

section TransitiveProof

open FullTransHelpers
open scoped FullArenaTactics FullTransTactics

private theorem tr_bnds {c : FullCfg} {k : FullCoreState} (hl : k.LengthsOk c) :
    2 * k.cur_vars + 1 < 2 ^ 30 ∧ k.wlen ≤ c.wcap ∧ k.wlen < 2 ^ 64 ∧ k.trail_end < 2 ^ 64 := by
  have := hl.cur_vars_le; have := hl.wlen_le; have := hl.trail_end_le
  have := c.hmaxv; have := c.hwcap; unfold dimacsBound at *; omega

theorem fast_transitive_wp (Γ : Env)
    (h_backtrack : ∀ args m Q X,
      fullBacktrackSpec args m Q X → Γ "full_backtrack" [i64, i64] [] args m Q X)
    (h_trans_lit : ∀ args m Q X,
      fullTransLitSpec args m Q X → Γ "full_trans_lit" [i64, i32] [.bool] args m Q X)
    (h_propagate : ∀ args m Q X,
      fullPropagateSpec args m Q X → Γ "full_propagate" [i64] [i64] args m Q X)
    (h_defrag : ∀ args m Q X,
      fullWstackDefragSpec args m Q X → Γ "full_wstack_defrag" [i64] [] args m Q X) :
    ∀ args m Q X, fullTransitiveFastSpec args m Q X →
      Func.wp Γ full_transitive_body args m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  unfold full_transitive_body; ft_unmdata
  have hlen0 := hsp.1.lengths
  -- Early guard: `if (h->num_binary == 0ULL || tick_lim == 0ULL) { return 1ULL; }`
  ft_split
  · ft_steps
    exact hQ 1#64 s m hsp id id (fun hnb _ => absurd ‹_› hnb) (Nat.le_refl _) (Or.inl rfl)
      (fun h => absurd h (by decide)) hm
  rename_i hnb_ne
  ft_split
  · ft_steps
    exact hQ 1#64 s m hsp id id (fun _ htl => absurd ‹_› htl) (Nat.le_refl _) (Or.inl rfl)
      (fun h => absurd h (by decide)) hm
  rename_i htl_ne
  refine wp_join_group (P := fun _ m' => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m') ?_ ?_
  · rintro J ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfuel1, hm1⟩; have hlen1 := hsp1.1.lengths; ft_to_group
    refine wp_loop_break_group (brkTs := [i64, i64]) (lpTs := [i64])
      (BrkPost := fun xs m' => let res := xs.2.1; ∃ sb : FullState, FullSparseInv c F0 sb ∧
        sb.core.cur_level = 0 ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res = 1#64 ∨ res = 20#64) ∧ (res = 20#64 → F0.Unsat) ∧ (FullMem c sb ⋆ R) m')
      (Inv := fun n xs m' => let v := xs.1; ∃ sl : FullState, v.toNat ≤ s1.core.cur_vars ∧
        n = s1.core.cur_vars - v.toNat ∧ FullSparseInv c F0 sl ∧ sl.core.cur_level = 0 ∧
        sl.core.cur_vars = s1.core.cur_vars ∧ sl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullMem c sl ⋆ R) m') ?_ ?_ ?_
    · rintro B ⟨_v, res, ⟨⟩⟩ m2 ⟨sb, hspb, hclb, hfuelb, hresb, hunsatb, hm2⟩
      refine wp_join_group (P := fun _ m3 => ∃ sd : FullState, FullSparseInv c F0 sd ∧
          sd.core.cur_level = 0 ∧ sd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullMem c sd ⋆ R) m3) ?_ ?_
      · rintro Jd ⟨⟩ m3 ⟨sd, hspd, hcld, hfueld, hm3⟩; have hlend := hspd.1.lengths; ft_steps
        exact hQ res _ _ (fullSparseInv_with_probing hspd 0#64) (fun _ => hcld) (fun _ => rfl)
          (fun _ _ => ⟨hcld, rfl⟩) hfueld hresb hunsatb (by assumption)
      · intro Jd hJd; have hlenb := hspb.1.lengths; ft_split
        · ft_call h_defrag; obtain ⟨F_cb, hwb⟩ := hspb.1.witness
          have hm := hwb.watches; simp only [ModeWatchesInv, hspb.2.2.2.2, ↓reduceIte] at hm
          refine ⟨c, sb, R, rfl, hlenb, hm.layout, hm2, fun _ _ _ _ m3 hlen3 hlay3 _ hpres hm3 =>
            hJd () m3 ⟨_, fullWstackDefrag_sparse hspb rfl hlen3 hlay3 hpres, hclb, hfuelb, hm3⟩⟩
        · ft_steps; exact hJd () m2 ⟨sb, hspb, hclb, hfuelb, hm2⟩
    · rintro B L n ⟨v, ⟨⟩⟩ m2 hB hL ⟨sl, hvle, hneq, hspl, hcll, hcvl, hfuell, hm2⟩
      have hlenl := hspl.1.lengths
      have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := (tr_bnds hlen1.core_ok).1; omega
      have hB1 : B (v, 1#64, ()) m2 := hB (v, 1#64, ()) m2 ⟨sl, hspl, hcll, hfuell, Or.inl rfl,
        fun h => absurd (show (1#64 : BitVec 64) = 20#64 from h) (by decide), hm2⟩
      ft_split; rotate_left; · ft_steps; exact hB1
      have hv_lt : v.toNat < s1.core.cur_vars := by
        have hlt : v.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
          simpa [BitVec.ult] using ‹_›
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt] at hlt
      ft_split; rotate_left; · ft_steps; exact hB1
      ft_split; rotate_left; · ft_steps; exact hB1
      refine wp_join_group (P := fun xs m3 => xs.1 = 1#64 ∧ ∃ sn : FullState,
          FullSparseInv c F0 sn ∧ sn.core.cur_level = 0 ∧ sn.core.cur_vars = s1.core.cur_vars ∧
          sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sn ⋆ R) m3) ?_ ?_
      · rintro J2 ⟨_, ⟨⟩⟩ m3 ⟨rfl, sn, hspn, hcln, hcvn, hfueln, hm3⟩; ft_steps
        have hv1 : (v + 1#64).toNat = v.toNat + 1 := ft_bv64_add1 (by omega)
        dsimp only at hvle hneq; exact hL (s1.core.cur_vars - (v.toNat + 1)) (v + 1#64, ()) m3
          (by omega) ⟨sn, by dsimp only; rw [hv1]; omega, by dsimp only; rw [hv1], hspn, hcln,
            hcvn, hfueln, hm3⟩
      · intro J2 hJ2
        have hv_fl : v.toNat < sl.core.flags.length := by
          rw [hlenl.core_ok.flags_len]; have := hlenl.core_ok.cur_vars_le; omega
        ft_split; rotate_left
        · ft_steps; exact hJ2 (1#64, ()) m2 ⟨rfl, sl, hspl, hcll, hcvl, hfuell, hm2⟩
        ft_to_group; have hsp_cl : FullSparseInv c F0 { sl with core := { sl.core with
            flags := sl.core.flags.set v.toNat (sl.core.flags[v.toNat] &&& ~~~512#32) } } :=
          fullSparseInv_clear_fl_trans hspl
        have hv32 : 2 * v.toNat + 1 < 2 ^ 32 := by have := (tr_bnds hlenl.core_ok).1; omega
        have hlit0 : ((v <<< (1 : Nat)).setWidth 32).toNat < 2 * ({ sl.core with
            flags := sl.core.flags.set v.toNat (sl.core.flags[v.toNat] &&& ~~~512#32) } :
            FullCoreState).cur_vars := by rw [ft_bv64_shl1_setWidth32 (by omega)]; dsimp only; omega
        ft_call h_trans_lit; refine ⟨c, F0, _, R, rfl, hsp_cl, hcll, hlit0, (by assumption),
          fun ok s_t0 m3 hspt0 hclt0 hcvt0 hfuelt0 huns0 hm3 => ?_⟩
        have hcv_t0 : s_t0.core.cur_vars = s1.core.cur_vars := hcvt0.trans hcvl
        ft_split; rotate_left; · ft_steps; exact hB (v, 20#64, ()) m3 ⟨s_t0, hspt0, hclt0,
          by rw [hfuelt0]; exact hfuell, Or.inr rfl, fun _ => huns0 (by cases ok <;> simp_all), hm3⟩
        obtain ⟨F_ct0, hwt0⟩ := hspt0.1.witness; ft_call h_propagate
        refine ⟨c, F0, F_ct0, s_t0, R, rfl, hspt0.1.lengths, hwt0, hspt0.2.2.2.2, hm3,
          fun r_p0 vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
            wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m4 hlen4 hw4 _ hperm4
            hfu4 _ _ hr1 _ _ hm4 => ?_⟩
        have hsp_p0 := fullPropagate_sparse hspt0 rfl hlen4 hw4 hperm4; ft_split
        · ft_steps; exact hB (v, 20#64, ()) m4 ⟨_, hsp_p0, hclt0,
            Nat.le_trans (Nat.le_trans hfu4 (by rw [hfuelt0]; exact Nat.le_refl _)) hfuell,
            Or.inr rfl, fun _ => Full.level0_unsat_of_conflict_okW hw4 hclt0 (hr1 ‹_›).2.2,
            hm4⟩
        · let st_p0 : FullState := { s_t0 with
            scratch := { s_t0.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases' },
            core := { s_t0.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
              wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
              confl_lit0 := c0', confl_lit1 := c1', oom := oom' } }
          have hlit1 : (((v <<< (1 : Nat)) ||| 1#64).setWidth 32).toNat <
              2 * st_p0.core.cur_vars := by rw [ft_bv64_shl1_or1_setWidth32 hv32, hcv_t0]; omega
          ft_to_group; ft_call h_trans_lit; refine ⟨c, F0, st_p0, R, rfl, hsp_p0, hclt0, hlit1,
            hm4, fun ok2 s_t1 m5 hspt1 hclt1 hcvt1 hfuelt1 huns1 hm5 => ?_⟩
          have hcv_t1 : s_t1.core.cur_vars = s1.core.cur_vars := hcvt1.trans hcv_t0
          ft_split; rotate_left; · ft_steps; exact hB (v, 20#64, ()) m5 ⟨s_t1, hspt1, hclt1,
            by rw [hfuelt1]; exact Nat.le_trans hfu4 (by rw [hfuelt0]; exact hfuell),
            Or.inr rfl, fun _ => huns1 (by cases ok2 <;> simp_all), hm5⟩
          obtain ⟨F_ct1, hwt1⟩ := hspt1.1.witness; ft_call h_propagate
          refine ⟨c, F0, F_ct1, s_t1, R, rfl, hspt1.1.lengths, hwt1, hspt1.2.2.2.2, hm5,
            fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel2 _ _ _ _ _ _ _ _ m6 hlen6 hw6 _ hperm6
              hfu6 _ _ hr1_2 _ _ hm6 => ?_⟩
          have hsp_p1 := fullPropagate_sparse hspt1 rfl hlen6 hw6 hperm6
          have hfuel_p1 : fuel2.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu6
            (by rw [hfuelt1]; exact Nat.le_trans hfu4 (by rw [hfuelt0]; exact hfuell))
          ft_split
          · ft_steps; exact hB (v, 20#64, ()) m6 ⟨_, hsp_p1, hclt1, hfuel_p1, Or.inr rfl,
              fun _ => Full.level0_unsat_of_conflict_okW hw6 hclt1 (hr1_2 ‹_›).2.2, hm6⟩
          · ft_steps; exact hJ2 (1#64, ()) m6 ⟨rfl, _, hsp_p1, hclt1, hcv_t1, hfuel_p1, hm6⟩
    · intro B L hB hL; ft_steps; exact hL s1.core.cur_vars (0#64, ()) _ ⟨_, Nat.zero_le _, rfl,
        fullSparseInv_with_ant_sz (fullSparseInv_with_probing hsp1 1#64) tick_lim,
        hcl1, rfl, hfuel1, by assumption⟩
  · intro J hJ; have hlen := hsp.1.lengths; obtain ⟨F_cur, hw⟩ := hsp.1.witness
    have hcl_lt : s.core.cur_level < 2 ^ 64 := by
      have := hw.cur_level_le; have := (tr_bnds hlen.core_ok).2.2.2; omega
    ft_split
    · ft_call h_backtrack
      have htl0 : ((Arg.imm 0).val : Val i64).toNat = 0 := by decide
      refine ⟨c, s, R, rfl, hlen, hcl_lt, (fun hpos => by
          have := hlen.core_ok.cur_vars_le; have := hw.cur_level_le
          have := hlen.core_ok.trail_end_le; rw [htl0] at hpos ⊢; omega), hw.trail_lits_lt, hm,
        fun _ _ _ _ _ _ _ _ _ _ _ hlen1 _ _ hcl1 hpr1 _ _ _ hw1 _ hm1 => hJ () _ ⟨_,
          fullBacktrack_sparse hsp rfl hlen1 hpr1 hw1, by simp [hcl1], Nat.le_refl _, hm1⟩⟩
    · ft_steps
      have hcl0' : s.core.cur_level = 0 := by
        simpa [Nat.mod_eq_of_lt hcl_lt] using
          congrArg BitVec.toNat (‹BitVec.ofNat 64 s.core.cur_level = 0#64›)
      exact hJ () m ⟨s, hsp, hcl0', Nat.le_refl _, hm⟩

end TransitiveProof

/-! ## 5. `fast_vivify_wp` (`u64 budget` parameter + early exit) -/

section VivifyProof

open FullVivTopTactics FullVivTop
open scoped FullArenaTactics FullVivTopTactics

private theorem viv_otfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullVivTopSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem viv_backtrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullVivTopSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  exact hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' hte hprop hcl hps _ htrl' _ hw_w hw_o hm' =>
      hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' hlen' hte hprop hcl hps htrl' hw_w
        (fun F0 Fc ho => hw_o F0 Fc (viv_otfs_to_canon ho)) hm'⟩

private theorem viv_prop_adapter {Γ : Env}
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullVivTopSpecs.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
  refine hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr hperm hfu hr hr0 hr1 hr2 hnp hm'
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
  have hnd' : FullVivTopSpecs.FullArenaVarsNodup s' := by
    intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hnd ref href0 (hgb.symm.trans hng))
  have hps' : FullVivTopSpecs.FullProbeScratchPres s s' :=
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' s'.scratch m' hlen' hw' hnd' hps' htr.1 hfu
    (fun ref href => by change ref ∈ fullArenaClauseRefsCore _; rw [hperm.2.1]; exact href)
    htr.2.1 hr hr0 hr1 hr2 hnp hm'

theorem fast_vivify_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hNext : ∀ args m Q X, Full.fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hVivClause : ∀ args m Q X, Full.fullVivClauseSpec args m Q X →
      Γ "full_viv_clause" [i64, i32] [i64] args m Q X)
    (hProp : ∀ args m Q X, Full.fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullVivifyFastSpec args m Q X →
      Func.wp Γ full_vivify_body args m Q X := by
  let hBt := viv_backtrack_adapter hBacktrack
  let hPr := viv_prop_adapter hProp
  rintro ⟨h, tier_mode, budget0, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at har_cap hmx
  unfold Func.wp full_vivify_body; fvt_to_group
  -- Early guard: `if (budget == 0ULL) { return 1ULL; }`
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 id id (fun hnz => absurd (by c0_bound) hnz)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  have hbud_ne : budget0 ≠ 0#64 := by c0_bound
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfl1, hm1⟩
    fvt_to_group
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullSparseInv.with_probing hsp1 1#64
    refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
      (fun (_budget_b, _p_b, res_b, ()) mb => ∃ sb : FullState,
        FullSparseInv c F0 sb ∧ sb.core.cur_level = 0 ∧
        sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
        (FullMem c sb ⋆ R) mb)
      (fun rem (budget, p, ()) mp => ∃ sp : FullState,
        sp.core.arena_len ≤ c.arena_cap ∧ p.toNat ≤ sp.core.arena_len ∧
        rem = sp.core.arena_len - p.toNat ∧
        FullSparseInv c F0 sp ∧ sp.core.cur_level = 0 ∧
        sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (p.toNat = sp.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
        (FullMem c sp ⋆ R) mp) ?_ ?_ ?_
    · rintro _ ⟨_, _, res_b, ⟨⟩⟩ mb ⟨sb, hspb, hclb, hflb, hresb, h20b, hmb⟩
      fvt_steps
      · have hres1 : res_b = 1#64 := by c0_bound
        refine wp_loop_inv (ts := [i64])
          (fun (p2, ()) mp2 => ∃ sp2 : FullState,
            sp2.core.arena_len ≤ c.arena_cap ∧ p2.toNat ≤ sp2.core.arena_len ∧
            FullSparseInv c F0 sp2 ∧ sp2.core.cur_level = 0 ∧
            sp2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (p2.toNat = sp2.core.arena_len ∨ p2.toNat ∈ fullArenaClauseRefs sp2) ∧
            (FullMem c sp2 ⋆ R) mp2)
          (fun (p2, ()) _ => c.arena_cap - p2.toNat) ?_ ?_
        · intro J2 hJ2; fvt_steps
          obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
          have halb : sb.core.arena_len ≤ c.arena_cap := hspb.1.lengths.core_ok.arena_len_le
          have h0_mem : 0 = sb.core.arena_len ∨ 0 ∈ fullArenaClauseRefs sb := by
            rcases Nat.eq_zero_or_pos sb.core.arena_len with h0 | hpos
            · exact Or.inl h0.symm
            · exact Or.inr (fullArenaClauseRefs_zero_mem hswb.2.1.arena hpos)
          exact hJ2 (0#64, ()) mb ⟨sb, halb, Nat.zero_le _, hspb, hclb, hflb, h0_mem, hmb⟩
        · intro J2 (p2, ⟨⟩) mp2 ⟨sp2, hal2, hp2_le, hsp2, hcl2, hfl2, hp2_mem, hmp2⟩ ih2
          fvt_steps
          · have hp2_lt : p2.toNat < sp2.core.arena_len := by c0_bound
            have hp2_ref : p2.toNat ∈ fullArenaClauseRefs sp2 :=
              hp2_mem.resolve_left (by omega)
            obtain ⟨F_cur2, hsw2⟩ := hsp2.exists_witness
            have hcl_ok := hsp2.1.lengths.core_ok
            have hp2_lt_ar : p2.toNat < sp2.core.arena.length := by
              have := hcl_ok.arena_len_arr; omega
            let hdr2 := sp2.core.arena[p2.toNat]'hp2_lt_ar
            let hdr2' := hdr2 &&& ~~~0x00100000#32
            have hhdr2 : fullArenaHdr sp2 p2.toNat = hdr2 := by
              unfold fullArenaHdr fullArenaHdrCore
              rw [List.getElem?_eq_getElem hp2_lt_ar, Option.getD_some]
            obtain ⟨hsw_cl, hrefs_cl, _⟩ := fullArena_setHdr_preserves_sparseW hsw2 hp2_ref
              (hdr' := hdr2') (by rw [hhdr2]; exact bv32_clr_viv_garb hdr2)
              (by rw [hhdr2]; exact bv32_clr_viv_shrk hdr2)
            let s_cl : FullState :=
              { sp2 with core := { sp2.core with arena := sp2.core.arena.set p2.toNat hdr2' } }
            have hsp_cl : FullSparseInv c F0 s_cl := hsw_cl.toSparse
            have hp2_32 : (p2.setWidth 32).toNat = p2.toNat := by bv_omega
            fvt_steps
            c0_call hNext
            refine ⟨c, s_cl, R, rfl, hsp_cl.1.lengths, hm, ?_⟩
            have hp2_ref_cl : p2.toNat ∈ fullArenaClauseRefs s_cl := by rw [hrefs_cl]; exact hp2_ref
            have hwf_cl := hsw_cl.2.1.arena.refs_wf p2.toNat hp2_ref_cl
            let np2_nat := fullArenaNextOff s_cl.core.arena s_cl.core.arena_len p2.toNat
            have hal_cl : s_cl.core.arena_len = sp2.core.arena_len := rfl
            have hnb : p2.toNat < np2_nat ∧ np2_nat ≤ sp2.core.arena_len := by
              dsimp only [np2_nat]
              simpa [hal_cl] using fullArenaNextOff_bounds hwf_cl.1
            have hnp2_mem : np2_nat = s_cl.core.arena_len ∨ np2_nat ∈ fullArenaClauseRefs s_cl := by
              dsimp only [np2_nat]
              exact fullArenaClauseRefs_next_mem_or_end hsw_cl.2.1.arena hp2_ref_cl
            have hnp2_bv : ((BitVec.ofNat 32 np2_nat).setWidth 64).toNat = np2_nat := by
              rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)]
            have hrem2 : c.arena_cap - ((BitVec.ofNat 32 np2_nat).setWidth 64).toNat <
                c.arena_cap - p2.toNat := by rw [hnp2_bv]; omega
            simp only [hp2_32]
            refine ih2 ((BitVec.ofNat 32 np2_nat).setWidth 64, ()) _ hrem2
              ⟨s_cl, hal_cl ▸ hal2, by rw [hnp2_bv]; exact hnb.2, hsp_cl, hcl2, hfl2,
                by rw [hnp2_bv]; exact hnp2_mem, hm⟩
          · subst hres1
            let sf : FullState := { sp2 with core := { sp2.core with probing := 0#64 } }
            have hspf : FullSparseInv c F0 sf := FullSparseInv.with_probing hsp2 0#64
            exact hQ 1#64 sf _ hspf (fun _ => hcl2) (fun _ => rfl) (fun _ => ⟨hcl2, rfl⟩)
              hfl2 (Or.inl rfl) (fun h => by cases h) hm
      · have hres20 : res_b = 20#64 := by
          rcases hresb with rfl | rfl
          · exact absurd rfl (by c0_bound)
          · rfl
        subst hres20
        let sf : FullState := { sb with core := { sb.core with probing := 0#64 } }
        have hspf : FullSparseInv c F0 sf := FullSparseInv.with_probing hspb 0#64
        exact hQ 20#64 sf _ hspf (fun _ => hclb) (fun _ => rfl) (fun _ => ⟨hclb, rfl⟩)
          hflb (Or.inr rfl) (fun _ => h20b rfl) hm
    · intro B L rem (budget, p, ⟨⟩) mp hB hL
        ⟨sp, halp, hp_le, hrem, hspp, hclp, hflp, hp_mem, hmp⟩
      subst hrem; clear hm
      fvt_steps
      · have hp_lt : p.toNat < sp.core.arena_len := by c0_bound
        have hp_ref : p.toNat ∈ fullArenaClauseRefs sp := hp_mem.resolve_left (by omega)
        obtain ⟨F_curp, hswp⟩ := hspp.exists_witness
        have hwfp := hswp.2.1.arena.refs_wf p.toNat hp_ref
        have hcl_ok := hspp.1.lengths.core_ok
        have hp_lt_ar : p.toNat < sp.core.arena.length := by have := hcl_ok.arena_len_arr; omega
        have hp_32 : (p.setWidth 32).toNat = p.toNat := by bv_omega
        fvt_steps
        c0_call hNext
        refine ⟨c, sp, R, rfl, hspp.1.lengths, hmp, ?_⟩
        let np_nat := fullArenaNextOff sp.core.arena sp.core.arena_len (p.setWidth 32).toNat
        have hnb : p.toNat < np_nat ∧ np_nat ≤ sp.core.arena_len := by
          dsimp only [np_nat]; rw [hp_32]; exact fullArenaNextOff_bounds hwfp.1
        have hnp_mem : np_nat = sp.core.arena_len ∨ np_nat ∈ fullArenaClauseRefs sp := by
          dsimp only [np_nat]; rw [hp_32]
          exact fullArenaClauseRefs_next_mem_or_end hswp.2.1.arena hp_ref
        have hnp_bv : ((BitVec.ofNat 32 np_nat).setWidth 64).toNat = np_nat := by
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        dsimp only; fvt_to_group
        refine wp_join_group (ts := [i64, i64])
          (fun (budget', _res', ()) mn => ∃ sn : FullState,
            sn.core.arena_len = sp.core.arena_len ∧
            sn.core.arena_len ≤ c.arena_cap ∧ np_nat ≤ sn.core.arena_len ∧
            FullSparseInv c F0 sn ∧ sn.core.cur_level = 0 ∧
            sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (np_nat = sn.core.arena_len ∨ np_nat ∈ fullArenaClauseRefs sn) ∧
            (FullMem c sn ⋆ R) mn) ?_ ?_
        · rintro _ ⟨budget', _, ⟨⟩⟩ mn
            ⟨sn, haln_eq, haln, hnp_le, hspn, hcln, hfln, hnp_memn, hmn⟩
          fvt_steps
          have hrem1 : sn.core.arena_len - ((BitVec.ofNat 32 np_nat).setWidth 64).toNat <
              sp.core.arena_len - p.toNat := by rw [hnp_bv, haln_eq]; omega
          exact hL _ (budget', (BitVec.ofNat 32 np_nat).setWidth 64, ()) mn hrem1
            ⟨sn, haln, by rw [hnp_bv]; exact hnp_le, rfl, hspn, hcln, hfln,
              by rw [hnp_bv]; exact hnp_memn, hmn⟩
        · intro Jn hJn; fvt_to_group
          · have hgarb_z : (sp.core.arena[p.toNat]'hp_lt_ar &&& 0x00180000#32) = 0#32 := by c0_bound
            have hngp : fullArenaClauseGarb sp p.toNat = false := by
              unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
              rw [List.getElem?_eq_getElem hp_lt_ar, Option.getD_some,
                bv32_garb_zero_of_and_viv hgarb_z]; rfl
            refine wp_join_group (ts := [.bool])
              (fun (_take, ()) mn => (FullMem c sp ⋆ R) mn) ?_ ?_
            · rintro _ ⟨take, ⟨⟩⟩ mn hmn
              fvt_steps
              · c0_call hVivClause
                refine ⟨c, F0, F_curp, sp, R, rfl, hswp, hclp, by simpa [hp_32] using hp_ref,
                  by simpa [hp_32] using hngp, hmn,
                  fun vc s_vc m_vc hsw_vc hcl_vc hfl_vc hal_vc hrefs_vc hvc h20_vc hm_vc => ?_⟩
                fvt_steps
                · exact hB (budget - 1#64, p, 20#64, ()) m_vc
                    ⟨s_vc, hsw_vc.toSparse, hcl_vc, Nat.le_trans hfl_vc hflp,
                      Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
                · c0_call hPr
                  refine ⟨c, F0, F_curp, s_vc, R, rfl, hsw_vc.1, hsw_vc.2.1, hsw_vc.2.2.2.1,
                    hsw_vc.2.2.2.2.2, hm_vc,
                    fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                      wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p sc_p
                      m_p hlen_p hw_p hnd_p hpres_p _ hfl_p hrefs_p _ hpr_disj
                      _ hpr1 _ _ hm_p => ?_⟩
                  let s_p : FullState :=
                    { s_vc with
                      core := { s_vc.core with
                        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                        trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                        unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                        arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                        fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                      scratch := sc_p }
                  have hsw_p : FullSparseInvW c F0 F_curp s_p :=
                    fullSparseInvW_of_prop_state hsw_vc hlen_p hw_p hnd_p hpres_p hrefs_p
                  have hcl_p : s_p.core.cur_level = 0 := hcl_vc
                  have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat :=
                    Nat.le_trans hfl_p (Nat.le_trans hfl_vc hflp)
                  have hal_p : s_p.core.arena_len = sp.core.arena_len := hal_vc
                  fvt_steps
                  · have hpr_eq1 : pr = 1#64 := by c0_bound
                    have hunsat : F0.Unsat :=
                      level0_unsat_of_conflict_okW hw_p hcl_p (hpr1 hpr_eq1).2.2
                    exact hB (budget - 1#64, p, 20#64, ()) m_p
                      ⟨s_p, hsw_p.toSparse, hcl_p, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
                  · have hnp_mem_p : np_nat = s_p.core.arena_len ∨
                        np_nat ∈ fullArenaClauseRefs s_p := by
                      rw [hal_p]
                      rcases hnp_mem with h | h
                      · exact Or.inl h
                      · exact Or.inr (hrefs_p _ (hrefs_vc ▸ h))
                    exact hJn (budget - 1#64, 1#64, ()) m_p
                      ⟨s_p, hal_p, by rw [hal_p]; exact halp, by rw [hal_p]; exact hnb.2,
                        hsw_p.toSparse, hcl_p, hfl_p', hnp_mem_p, hm_p⟩
              · exact hJn (budget, 1#64, ()) _
                  ⟨sp, rfl, halp, hnb.2, hspp, hclp, hflp, hnp_mem, hmn⟩
            · intro Jtk hJtk; fvt_steps <;> exact hJtk _ mp hmp
          · exact hJn (budget, 1#64, ()) _ ⟨sp, rfl, halp, hnb.2, hspp, hclp, hflp, hnp_mem, hmp⟩
      · exact hB (budget, p, 1#64, ()) mp
          ⟨sp, hspp, hclp, hflp, Or.inl rfl, (fun h => by cases h), hmp⟩
      · exact hB (budget, p, 1#64, ()) mp
          ⟨sp, hspp, hclp, hflp, Or.inl rfl, (fun h => by cases h), hmp⟩
      · exact hB (budget, p, 1#64, ()) mp
          ⟨sp, hspp, hclp, hflp, Or.inl rfl, (fun h => by cases h), hmp⟩
      · exact hB (budget, p, 1#64, ()) mp
          ⟨sp, hspp, hclp, hflp, Or.inl rfl, (fun h => by cases h), hmp⟩
    · intro B L hB hL; fvt_steps
      obtain ⟨F_cur2, hsw2⟩ := hsp2.exists_witness
      have hal2 : s2.core.arena_len ≤ c.arena_cap := hsp2.1.lengths.core_ok.arena_len_le
      have h0_mem : 0 = s2.core.arena_len ∨ 0 ∈ fullArenaClauseRefs s2 := by
        rcases Nat.eq_zero_or_pos s2.core.arena_len with h0 | hpos
        · exact Or.inl h0.symm
        · exact Or.inr (fullArenaClauseRefs_zero_mem hsw2.2.1.arena hpos)
      exact hL s2.core.arena_len (budget0, 0#64, ()) _
        ⟨s2, hal2, Nat.zero_le _, by simp, hsp2, hcl1, hfl1, h0_mem, hm⟩
  · intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    fvt_steps
    · c0_call hBt
      refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl0_lt,
        fun h => by
          have h0n : (0 : BitVec 64).toNat = 0 := rfl; rw [h0n] at h
          have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
          have := hsp0.1.lengths.core_ok.cur_vars_le; omega,
        hsw0.2.1.trail_lits_lt, hm0,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1 hpres1 (by simpa using hw_bt F0)
      exact hJc () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
      exact hJc () m0 ⟨s, hsp0, hcl0, Nat.le_refl _, hm0⟩

end VivifyProof

/-! ## 6. `fast_probe_run_wp` (early guard `budget == 0 || num_binary == 0`) -/

section ProbeRunProof

open FullProbeTransHelpers
open scoped FullArenaTactics FullProbeTransTactics

private theorem pr_otfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullProbeTransSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem pr_canon_to_otfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullProbeTransSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem pr_backtrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullProbeTransSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' hte hpr hcl' hps hsc htrl' hvl hw_w hw_o hm' => ?_⟩
  have hshrk : sc'.shrink_stk = s.scratch.shrink_stk := by
    rcases hsc with ⟨_, _, _, _, _, _, _, _, _, rfl⟩; rfl
  exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hpr hcl' hps hshrk htrl'
    (fun ⟨F0, Fc, hwo⟩ => hvl ⟨F0, Fc, hwo.elim Or.inl (Or.inr ∘ pr_otfs_to_canon)⟩)
    hw_w (fun F0 Fc ho hlt => hw_o F0 Fc (pr_otfs_to_canon ho) hlt) hm'

private theorem pr_assumePair_adapter {Γ : Env}
    (hAp : ∀ a m Q X, Full.fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullProbeTransSpecs.fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm, hQ⟩
  refine hAp _ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm,
    fun r s' m' h12 h20 hcv hfu hr hm' => ?_⟩
  exact hQ r s' m' h12
    (fun h => let ⟨hu, Fc, ho⟩ := h20 h; ⟨hu, Fc, ⟨ho.1, pr_canon_to_otfs ho.2.1, ho.2.2⟩⟩)
    hcv hfu hr hm'

private theorem pr_set_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (p : BitVec 64) (hsp : FullSparseInv c F0 s) :
    FullSparseInv c F0 { s with core := { s.core with probing := p } } :=
  FullTransHelpers.fullSparseInv_with_probing hsp p

private abbrev prBtState (s : FullState) (vals' : List (BitVec 8))
    (lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' cl' : Nat) (unass' : BitVec 64)
    (sc' : FullScratch) : FullState :=
  { s with
    core := { s.core with
      vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
    scratch := sc' }

private theorem prBtState_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (hlen' : (prBtState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc').LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      (prBtState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc').core)
    (hlm : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hdm : s.core.dense_mode = 0#64) (hpres : FullExtScratchPres s { s with scratch := sc' }) :
    FullSparseInv c F0 (prBtState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc') :=
  ⟨⟨hlen', F_cur, hw'⟩, ⟨hlm.1, hlm.2⟩, hnd,
    ⟨fun i hi => by
      change (sc'.last_learned[i]?.getD 0xFFFFFFFF#32) = 0xFFFFFFFF#32 ∨ _
      rw [hpres.1]; exact hext.1 i hi,
     by change sc'.extend_len ≤ c.extend_cap; rw [hpres.2]; exact hext.2⟩, hdm⟩

private theorem pr_bv8_sext32_eq0 {x : BitVec 8} (h : x.signExtend 32 = 0#32) : x = 0#8 := by
  revert x h; decide

private theorem pr_vals_eq_0_of_sext {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (heq : (vals[i]'hi).signExtend 32 = 0#32) : vals[i]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some, pr_bv8_sext32_eq0 heq]

theorem fast_probe_run_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAssumePair : ∀ args m Q X, Full.fullProbeAssumePairSpec args m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] args m Q X) :
    ∀ args m Q X, fullProbeRunFastSpec args m Q X →
      Func.wp Γ full_probe_run_body args m Q X := by
  let hBt := pr_backtrack_adapter hBacktrack
  let hAp := pr_assumePair_adapter hAssumePair
  rintro ⟨h_arg, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  obtain ⟨⟨hlen0, F_cur0, hw0⟩, hlm0, hnd0, hext0, hdm0⟩ := hsp0
  have hcl0_ok := hlen0.core_ok; have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hcl0_ok.cur_vars_le
  have hcl_64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hcl0_ok.trail_end_le; omega
  have hpos_mv_if : 0 < s.core.cur_level → 0 < c.max_vars := fun _ => by
    have := hw0.cur_level_le; have := hcl0_ok.trail_end_le; omega
  have hsp0' : FullSparseInv c F0 s := ⟨⟨hlen0, F_cur0, hw0⟩, hlm0, hnd0, hext0, hdm0⟩
  unfold Func.wp full_probe_run_body
  pt_steps_nogrp
  -- Early guard: `if (budget == 0ULL || h->num_binary == 0ULL) { return 1ULL; }`
  · exact hQ 1#64 s m hsp0' id id (fun hb _ => absurd hc hb)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  · exact hQ 1#64 s m hsp0' id id (fun _ hnb => absurd hc hnb)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  let entryInv : Tup Val [] → Mem 64 → Prop := fun () mj =>
    ∃ st0 : FullState, FullSparseInv c F0 st0 ∧ st0.core.cur_level = 0 ∧
      st0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st0 ⋆ R) mj
  refine wp_join_group entryInv (fun _ () mj ⟨st0, hsp_e, hcl_e, hfu_e, hm_e⟩ => ?_)
    (fun Jentry hJentry => ?_)
  · pt_steps_nogrp
    let st1 : FullState := { st0 with core := { st0.core with probing := 1#64 } }
    have hcv_e64 : st0.core.cur_vars < 2 ^ 64 := by have := hsp_e.1.1.core_ok.cur_vars_le; omega
    have hsp1 := pr_set_probing 1#64 hsp_e
    have hm1 : (FullMem c st1 ⋆ R) m := by
      simpa only [st1, show (1 : BitVec 64) = 1#64 from rfl] using hm
    let exitInv : Tup Val [i64, i64, i64] → Mem 64 → Prop := fun (_d, _v, res_v, ()) mx =>
      ∃ st_x : FullState, st_x.LengthsOk c ∧
        (res_v = 1#64 → FullSparseInv c F0 st_x ∧ st_x.core.cur_level = 0) ∧
        (res_v = 20#64 → F0.Unsat ∧ ∃ F_x, FullProbeTransSpecs.FullOtfsInvW c F0 F_x st_x) ∧
        (res_v = 1#64 ∨ res_v = 20#64) ∧ st_x.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullMem c st_x ⋆ R) mx
    refine wp_join_group exitInv (fun _ (_d, _v, res_v, ()) mx ⟨st_x, hlen_x, h1, h20, hdom,
        hfu_x, hm_x⟩ => ?_) (fun Jexit hJexit => ?_)
    · let retInv : Tup Val [] → Mem 64 → Prop := fun () mr => ∃ st_r : FullState,
        FullSparseInv c F0 st_r ∧ st_r.core.cur_level = 0 ∧
        st_r.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (res_v = 20#64 → F0.Unsat) ∧
        (FullMem c st_r ⋆ R) mr
      refine wp_join_group retInv (fun _ () mr ⟨st_r, hsp_r, hcl_r, hfu_r, huns, hm_r⟩ => ?_)
        (fun Jret hJret => ?_)
      · pt_steps_nogrp
        exact hQ res_v { st_r with core := { st_r.core with probing := 0#64 } } m
          (pr_set_probing 0#64 hsp_r) (fun _ => hcl_r) (fun _ => rfl)
          (fun _ _ => ⟨hcl_r, rfl⟩) hfu_r hdom huns
          (by simpa only [show (0 : BitVec 64) = 0#64 from rfl] using hm)
      · have hcl_x64 : st_x.core.cur_level < 2 ^ 64 := by
          have := hlen_x.core_ok.trail_end_le; have := hlen_x.core_ok.cur_vars_le
          rcases hdom with rfl | rfl; · rw [(h1 rfl).2]; decide
          · obtain ⟨_, F_x, hot⟩ := h20 rfl; have := hot.2.1.cur_level_le; omega
        pt_steps_nogrp
        · have hpos_cl : 0 < st_x.core.cur_level := by
            pt_clear_big; have : (0 : Nat) < st_x.core.cur_level % 2 ^ 64 := hc; omega
          have hreq20 : res_v = 20#64 := by
            rcases hdom with rfl | rfl; exact absurd (h1 rfl).2 (by omega); rfl
          obtain ⟨huns, F_x, hot⟩ := h20 hreq20
          have hpos_mv_x : 0 < c.max_vars := by
            have := hot.2.1.cur_level_le; have := hlen_x.core_ok.trail_end_le
            have := hlen_x.core_ok.cur_vars_le; omega
          c0_call hBt
          refine ⟨c, st_x, R, rfl, hlen_x, hcl_x64, fun _ => hpos_mv_x, hot.2.1.trail_lits_lt,
            hm_x, ?_⟩; dsimp only
          intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt hlen_bt _ _ hcl_bt hpres
            _ _ _ _ hbt_o hm_bt
          let st_bt := prBtState st_x vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc'
          have hsp_bt := prBtState_sparse hlen_bt (hbt_o F0 F_x hot.2.1 hpos_cl)
            hot.2.2.1 hot.2.2.2.1 hot.2.2.2.2.1 hot.2.2.2.2.2 hpres.1
          exact hJret () m_bt ⟨st_bt, hsp_bt, by simp [st_bt, hcl_bt], hfu_x, fun _ => huns, hm_bt⟩
        · have hcl_z : st_x.core.cur_level = 0 := by
            pt_clear_big; rw [Nat.mod_eq_of_lt hcl_x64] at hc; omega
          rcases hdom with rfl | rfl
          · exact hJret () mx ⟨st_x, (h1 rfl).1, hcl_z, hfu_x, fun h => absurd h (by decide), hm_x⟩
          · obtain ⟨huns, F_x, hot⟩ := h20 rfl
            have hsw := hot.toSparse_of_level0 hcl_z
            exact hJret () mx ⟨st_x, ⟨⟨hsw.1, F_x, hsw.2.1⟩, hsw.2.2⟩,
              hcl_z, hfu_x, fun _ => huns, hm_x⟩
    · let loopInv : Tup Val [i64, i64] → Mem 64 → Prop := fun (_done_v, v_v, ()) ml =>
        v_v.toNat ≤ st1.core.cur_vars ∧ ∃ st : FullState, FullSparseInv c F0 st ∧
          st.core.cur_level = 0 ∧ st.core.cur_vars = st1.core.cur_vars ∧
          st.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st ⋆ R) ml
      let meas : Tup Val [i64, i64] → Mem 64 → Nat :=
        fun (_, v_v, ()) _ => st1.core.cur_vars - v_v.toNat
      refine wp_loop_inv loopInv meas (fun Jloop hJloop => ?_) (fun Jloop (done_v, v_v, ()) ml
          ⟨hv_le, st, hsp, hcl_st, hcv_st, hfu_st, hm_st⟩ hJloop => ?_)
      · pt_steps_nogrp
        exact hJloop (0#64, 0#64, ()) m ⟨Nat.zero_le _, st1, hsp1, hcl_e, rfl, hfu_e, hm1⟩
      · have hcl_sok := hsp.1.1.core_ok; have hcv_st_le := hcl_sok.cur_vars_le
        have hdone_exit : exitInv (done_v, v_v, 1#64, ()) ml := ⟨st, hsp.1.1,
          fun _ => ⟨hsp, hcl_st⟩, fun h => absurd h (by decide), Or.inl rfl, hfu_st, hm_st⟩
        pt_steps_nogrp
        · have hv_lt : v_v.toNat < st.core.cur_vars := by
            pt_clear_big; rw [Nat.mod_eq_of_lt hcv_e64] at *
            change v_v.toNat < st1.core.cur_vars at *; omega
          have hv_fl : v_v.toNat < st.core.flags.length := by rw [hcl_sok.flags_len]; omega
          have hv_shl : (v_v <<< (1#32 : BitVec 32).signExtend 64).toNat = 2 * v_v.toNat := by
            change (v_v <<< (1 : Nat)).toNat = 2 * v_v.toNat
            exact FullProbeTransHelpers.bv64_shl1_toNat (by omega)
          have hv_val : (v_v <<< (1#32 : BitVec 32).signExtend 64).toNat <
              st.core.vals.length := by rw [hv_shl, hcl_sok.vals_len]; omega
          have hv1_eq := FullProbeTransHelpers.bv64_add1_toNat (by omega : v_v.toNat + 1 < 2 ^ 64)
          let nextInv : Tup Val [i64, i64] → Mem 64 → Prop := fun (done_n, _, ()) mn =>
            ∃ st_n : FullState, FullSparseInv c F0 st_n ∧ st_n.core.cur_level = 0 ∧
              st_n.core.cur_vars = st1.core.cur_vars ∧ st_n.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st_n ⋆ R) mn
          refine wp_join_group nextInv (fun _ (done_n, _r, ()) mn
              ⟨st_n, hsp_n, hcl_n, hcv_n, hfu_n, hm_n⟩ => by
            pt_steps_nogrp
            exact hJloop (done_n, v_v + 1#64, ()) mn (by dsimp only [meas]; rw [hv1_eq]; omega)
              ⟨by rw [hv1_eq]; omega, st_n, hsp_n, hcl_n, hcv_n, hfu_n, hm_n⟩)
            (fun Jnext hJnext => ?_)
          pt_steps_nogrp
          · have hlit_to : ((v_v <<< (1#32 : BitVec 32).signExtend 64).setWidth 32).toNat =
                2 * v_v.toNat := by
              rw [BitVec.toNat_setWidth, hv_shl, Nat.mod_eq_of_lt (by omega)]
            have hlit_lt' : ((v_v <<< (1#32 : BitVec 32).signExtend 64).setWidth 32).toNat <
                2 * st.core.cur_vars := by rw [hlit_to]; omega
            have hun_lit : st.core.vals[((v_v <<<
                (1#32 : BitVec 32).signExtend 64).setWidth 32).toNat]?.getD 0#8 = 0#8 :=
              pr_vals_eq_0_of_sext (by rw [hlit_to, hcl_sok.vals_len]; omega) (by
                pt_clear_big
                simpa only [hlit_to, Nat.mod_eq_of_lt (by omega : 2 * v_v.toNat < 2 ^ 64)] using hc)
            c0_call hAp
            refine ⟨c, F0, st, R, rfl, hsp, hcl_st, hlit_lt', hun_lit, hm_st, ?_⟩; dsimp only
            intro ap st_ap m_ap hap12 hap20 hcv_ap hfu_ap hap_dom hm_ap
            have hcv_aps := hcv_ap.trans hcv_st; have hfu_aps := Nat.le_trans hfu_ap hfu_st
            pt_steps_nogrp
            · have hap_eq20 : ap = 20#64 := by pt_clear_big; exact hc
              obtain ⟨huns, F_ap, hot_ap'⟩ := hap20 hap_eq20
              exact hJexit (done_v + 1#64, v_v, 20#64, ()) m_ap ⟨st_ap, hot_ap'.1,
                fun h => absurd h (by decide), fun _ => ⟨huns, F_ap, hot_ap'⟩,
                Or.inr rfl, hfu_aps, hm_ap⟩
            · have hap_eq2 : ap = 2#64 := by pt_clear_big; exact hc
              obtain ⟨hsp_ap, hcl_ap⟩ := hap12 (Or.inr hap_eq2)
              exact hJexit (done_v + 1#64, v_v, 1#64, ()) m_ap ⟨st_ap, hsp_ap.1.1,
                fun _ => ⟨hsp_ap, hcl_ap⟩, fun h => absurd h (by decide),
                Or.inl rfl, hfu_aps, hm_ap⟩
            · have hap_eq1 : ap = 1#64 := by
                pt_clear_big; rcases hap_dom with h | h | h <;> simp_all
              obtain ⟨hsp_ap, hcl_ap⟩ := hap12 (Or.inl hap_eq1)
              exact hJnext (done_v + 1#64, 1#64, ()) m_ap
                ⟨st_ap, hsp_ap, hcl_ap, hcv_aps, hfu_aps, hm_ap⟩
          all_goals exact hJnext (done_v, 1#64, ()) ml ⟨st, hsp, hcl_st, hcv_st, hfu_st, hm_st⟩
        all_goals exact hJexit (done_v, v_v, 1#64, ()) ml hdone_exit
  · pt_steps_nogrp
    · c0_call hBt
      have hpos_cl : 0 < s.core.cur_level := by
        pt_clear_big; exact Nat.pos_of_ne_zero fun h0 => hc (by simp [h0])
      refine ⟨c, s, R, rfl, hlen0, hcl_64, fun _ => hpos_mv_if hpos_cl, hw0.trail_lits_lt, hm0, ?_⟩
      dsimp only; intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt hlen_bt _ _ hcl_bt
        hpres _ _ _ hbt_w _ hm_bt
      let st_bt := prBtState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc'
      have hw_bt := hbt_w F0 F_cur0 hw0 (Nat.zero_le _)
      have hsp_bt := prBtState_sparse hlen_bt hw_bt hlm0 hnd0 hext0 hdm0 hpres.1
      exact hJentry () m_bt ⟨st_bt, hsp_bt, by simp [st_bt, hcl_bt], Nat.le_refl _, hm_bt⟩
    · have hcl_0 : s.core.cur_level = 0 := by
        pt_clear_big; have h := congrArg BitVec.toNat hc
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_64] at h
      exact hJentry () m ⟨s, hsp0', hcl_0, Nat.le_refl _, hm0⟩

end ProbeRunProof

end LeanQbe.T.Examples.Kissat.FullFastBveBudgets
