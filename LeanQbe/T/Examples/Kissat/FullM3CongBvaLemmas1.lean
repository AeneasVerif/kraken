module

public import LeanQbe.T.Examples.Kissat.FullM3CongBva
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullCongLemmas
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1

/-!
# Kissat `D-Full` M3b Congruence & BVA/BVE Proofs — Part 1 (`Specs`, Lemmas, Helpers #1–#4)

Defines M2b callee specs (`fullCongExtractTickSpec`, `fullSweepDenseSpec`, `fullFactorHeapSpec`),
all `11` M3b `Spec` contracts (`m3CongMarkTrailSpec` .. `fullPreprocessSpec`), pure AND/XOR/ITE
folding & hash-matching soundness lemmas, `FullMem` framing helpers, and parametric `(Γ : Env)`
`Func.wp` proofs for helpers `#1–#4`:
1. `full_cong_mark_trail` (`m3_cong_mark_trail_wp`)
2. `full_cong_unit_fold` (`m3_cong_unit_fold_wp`)
3. `full_cong_equiv_fold` (`m3_cong_equiv_fold_wp`)
4. `full_cong_and_match` (`m3_cong_and_match_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM3CongBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open Kraken.Bedrock2.Test

/-! ## 1. M2b Callee Specs & All `11` M3b `Spec` Contracts -/

section Specs

/-- `full_cong_extract(h, g_cap, tick_lim)` (`FullDefSweep`, 3-arg M2b contract). -/
@[expose] def fullCongExtractTickSpec : Spec [i64, i64, i64] [i64] :=
  fun (h, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧ g_cap.toNat ≤ c.scratch_cap ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap → ret.toNat ≤ g_cap.toNat →
        FullCongSpecs.GateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- `full_sweep_dense(h, budget, tick_lim)` (`FullDefSweep`, 3-arg dense SAT sweeping). -/
@[expose] def fullSweepDenseSpec : Spec [i64, i64, i64] [i64] :=
  fun (h, _budget, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInv c F0 s' → s'.core.cur_level = 0 →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_factor(h, budget)` (`FullBvaHeap`, 2-arg max-degree heap BVA). -/
@[expose] def fullFactorHeapSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel = s.core.fuel → r = 1#64 → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **#1 (`full_cong_mark_trail`)**: marks newly pushed trail literals & representatives
in `tarjan_mark` with epoch `ep` while preserving `CongReprInv` and all non-`repr`/`tmk` fields. -/
@[expose] def m3CongMarkTrailSpec : Spec [i64, i64, i32] [] := fun (h, _prev_te, _ep, ()) m Q _ =>
  ∃ (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    (FullMem c s ⋆ R) m ∧
    ∀ repr' tmk' m',
      let s' : FullState :=
        { s with
          core := { s.core with repr := repr' }
          scratch := { s.scratch with tarjan_mark := tmk' } }
      s'.LengthsOk c →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- **#2 (`full_cong_unit_fold`)**: propagates an entailed literal under congruence, marks
trail epochs, and returns `0` (already satisfied), `1` (propagated), or `2` (`F0.Unsat`). -/
@[expose] def m3CongUnitFoldSpec : Spec [i64, i32, i32] [i64] := fun (h, lit, _next_ep, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    lit.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.tmp = s.core.tmp → s'.scratch.scratch_buf = s.scratch.scratch_buf →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 2#64 → s'.core.inconsistent ≠ 0#64 ∧ F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **#3 (`full_cong_equiv_fold`)**: propagates unit values when either side of `a ↔ b`
is assigned, merges `repr`, marks `tmk` & trail, and flags `2#64` (`F0.Unsat`) on conflict. -/
@[expose] def m3CongEquivFoldSpec : Spec [i64, i32, i32, i32] [i64] :=
  fun (h, a, b, _next_ep, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
      LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        s'.core.tmp = s.core.tmp → s'.scratch.scratch_buf = s.scratch.scratch_buf →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 2#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **#4 (`full_cong_and_match`)**: matches a candidate AND gate at `scr[ent]` (with unit-true
inputs dropped and remaining inputs matched bijectively against `tmp[0 ..< ua)`). -/
@[expose] def m3CongAndMatchSpec : Spec [i64, i32, i32] [.bool] := fun (h, ent, ua, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    g_len ≤ c.scratch_cap ∧
    (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
    FullCongSpecs.GateAt F_cur s.core.cur_vars scr0 g_len ent.toNat ∧
    (scr0[ent.toNat + 1]?.getD 0#32 >>> 28) = 0#32 ∧
    ua.toNat ≤ s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) repr' m',
      let s' : FullState := { s with core := { s.core with repr := repr' } }
      repr'.length = 2 * c.max_vars →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      (ok = true → 2 ≤ ua.toNat ∧ ua.toNat ≤ 8 ∧
        ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
          evalLitVal α (scr0[ent.toNat]?.getD 0#32).toNat =
            (List.range ua.toNat).all fun k =>
              evalLitVal α (s.core.tmp[k]?.getD 0#32).toNat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- **#5 (`full_cong_work_step`)**: worklist-filtered single congruence pass preserving
`FullDenseInv`, `FullCongReprInv`, persistent `CongHtInv`, `scr[0..g_len)`, `cur_vars`, `fuel`,
returning `st = r &&& 3` with `st = 2 → F0.Unsat`. -/
@[expose] def m3CongWorkStepSpec : Spec [i64, i64, i64, i64, i32] [i64] :=
  fun (h, g_len, ht_off, ht_sz, _cur_ep, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ g_len.toNat ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      FullCongSpecs.GateSeqOk F_cur s.core.cur_vars scr0 g_len.toNat 0 ∧
      (∀ idx < g_len.toNat, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      FullCongSpecs.CongHtInv F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
        g_len.toNat ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        FullCongSpecs.CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len.toNat ht_off.toNat ht_sz.toNat →
        ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) →
        ((r &&& 3#64) = 2#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **#6 (`full_congruence_dense`)**: dense-mode ticks-bounded congruence closure (up to `65536` HT,
epoch worklist, depth cap lifted), returning `1#64` or `20#64` (`F0.Unsat`). -/
@[expose] def m3CongruenceDenseSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- **#7 (`full_elim_collect_nbrs`)**: collects active unassigned variable neighbors of `v` into
`work_stk2[0 ..< nn)` while keeping `nn ≤ cur_vars`, all stored indices `< cur_vars`, and preserving
`FullDenseInv`, `TmkZero`, `cur_vars`, and `fuel`. -/
@[expose] def m3ElimCollectNbrsSpec : Spec [i64, i32] [i64] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ nn mclr' ws2' m',
      let s' : FullState :=
        { s with
          core := { s.core with min_clr := mclr' }
          scratch := { s.scratch with work_stk2 := ws2' } }
      s'.LengthsOk c →
      nn.toNat ≤ s.core.cur_vars →
      (∀ k < nn.toNat, (ws2'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (nn, ()) m'

/-- **#8 (`full_elim_bve`)**: M3b neighbor-rearming multi-pass BVE (`16` passes, `FL_ELIM_C`),
preserving `FullDenseInv`, `TmkZero`, `cur_vars ≤`, and `fuel ≤`. -/
@[expose] def m3ElimBveSpec : Spec [i64, i64] [i64] := fun (h, _bve_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → TmkZero s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

abbrev m3ProbeSpec : Spec [i64, .bool] [i64] := schedProbeSpec
abbrev m3EliminateSpec : Spec [i64, .bool] [i64] := schedEliminateSpec
abbrev m3PreprocessSpec : Spec [i64] [i64] := Full.fullPreprocessSpec

end Specs

/-! ## 2. Framing Helpers & Pure Congruence-Folding Lemmas -/

section Helpers

theorem fullWitnessInv_with_min_clr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (mclr' : List (BitVec 32)) :
    FullWitnessInv c F0 F_cur { k with min_clr := mclr' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullWitnessInv_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (fl' : List (BitVec 32)) :
    FullWitnessInv c F0 F_cur { k with flags := fl' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullDenseInvW_with_tarjan_mark {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {tmk' : List (BitVec 32)}
    (htl : tmk'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with tarjan_mark := tmk' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with tarjan_mark_len := htl }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInv_with_tarjan_mark {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {tmk' : List (BitVec 32)} (htl : tmk'.length = 2 * c.max_vars) :
    FullDenseInv c F0 { s with scratch := { s.scratch with tarjan_mark := tmk' } } := by
  obtain ⟨F_cur, hw⟩ := h.exists_witness
  exact (fullDenseInvW_with_tarjan_mark hw htl).toDense

theorem fullDenseInv_with_min_clr_work_stk2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {mclr' ws2' : List (BitVec 32)}
    (hml : mclr'.length = c.max_vars) (hwl : ws2'.length = 2 * c.max_vars) :
    FullDenseInv c F0
      { s with
        core := { s.core with min_clr := mclr' }
        scratch := { s.scratch with work_stk2 := ws2' } } := by
  obtain ⟨F_cur, hw⟩ := h.exists_witness
  exact FullDenseInvW.toDense
    ⟨⟨{ hw.1.core_ok with min_clr_len_arr := hml },
      { hw.1.scratch_ok with work_stk2_len := hwl }⟩,
     fullWitnessInv_with_min_clr hw.2.1 mclr', hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1,
     hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩

theorem fullDenseInv_with_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hw⟩ := h.exists_witness
  exact FullDenseInvW.toDense
    ⟨⟨{ hw.1.core_ok with flags_len := hfl }, hw.1.scratch_ok⟩,
     fullWitnessInv_with_flags hw.2.1 fl', hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1,
     hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩

theorem fullDenseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

theorem fullSparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

theorem fullAddUnitSpec_fullDenseInvW {c : FullCfg}
    {s s' : FullState} (hmk : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s)
    (hext : FullExtScratchOk c s) (hdm : s.core.dense_mode ≠ 0#64)
    (hcl' : s'.core.cur_level = 0)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hdm' : s'.core.dense_mode = s.core.dense_mode) :
    FullLitMarksClear c s' ∧ FullArenaVarsNodup s' ∧ FullExtScratchOk c s' ∧
    s'.core.cur_level = 0 ∧ s'.core.dense_mode ≠ 0#64 :=
  ⟨fullLitMarksClear_of_eq hmk hmrk' hlm', fullArenaVarsNodup_of_eq hnd har' hal',
   fullExtScratchOk_of_eq hext har' hal' hll' hext', hcl', hdm' ▸ hdm⟩

theorem unsat_of_inconsistent_w {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hinc : k.inconsistent ≠ 0#64) :
    F0.Unsat :=
  hw.ext_sound.2 (hw.inconsistent_sound hinc)

theorem bv8_ne0_of_signExtend32 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hne : v.signExtend 32 ≠ 0#32) : v ≠ 0#8 := by
  intro rfl; exact hne (by decide)

theorem bv8_eq0_of_signExtend32 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (heq : v.signExtend 32 = 0#32) : v = 0#8 := by
  rcases hdom with rfl | rfl | rfl
  · rfl
  · exact absurd heq (by decide)
  · exact absurd heq (by decide)

theorem bv8_eq1_of_signExtend32_sgt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hsgt : (0#32 : BitVec 32).slt (v.signExtend 32) = true) :
    v = 1#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd hsgt (by decide)
  · rfl
  · exact absurd hsgt (by decide)

theorem bv8_not_slt0_of_signExtend32_nslt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hnslt : (v.signExtend 32).slt 0#32 = false) :
    ¬ v.slt 0#8 = true := by
  rcases hdom with rfl | rfl | rfl
  · decide
  · decide
  · exact absurd hnslt (by decide)

theorem bv8_ne0_not_signExtend32_sgt0_eqff {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hne0 : v ≠ 0#8)
    (hnsgt : ¬ (0#32 : BitVec 32).slt (v.signExtend 32) = true) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd rfl hne0
  · exact absurd (by decide) hnsgt
  · rfl

theorem bv8_not_slt0_of_signExtend32_eq0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (heq : v.signExtend 32 = 0#32) :
    ¬ v.slt 0#8 = true := by
  rw [bv8_eq0_of_signExtend32 hdom heq]; decide

theorem bv8_eq1_of_signExtend32_ne0_nslt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hne : v.signExtend 32 ≠ 0#32)
    (hnslt : ¬ v.slt 0#8 = true) : v = 1#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd (by decide) hne
  · rfl
  · exact absurd (by decide) hnslt

theorem bv8_eq1_of_sgt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hsgt : (0#8 : BitVec 8).slt v = true) :
    v = 1#8 :=
  (bv8_sgt0_iff_eq1 hdom).mp hsgt

theorem bv8_eqff_of_slt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hslt : v.slt 0#8 = true) :
    v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · cases hslt
  · cases hslt
  · rfl

theorem bv8_ne0_not_sgt0_eqff {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hne0 : v ≠ 0#8)
    (hnsgt : ¬ (0#8 : BitVec 8).slt v = true) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd rfl hne0
  · exact absurd (by decide) hnsgt
  · rfl

theorem vals1_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {k : FullCoreState}
    (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0) {l : Nat}
    (hl : l < 2 * k.cur_vars) (hval : k.vals[l]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp hval
  have hlvl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hs := hw.level0_sound i hi hlvl0; rwa [heq] at hs

theorem valsff_entails_neg {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0) {l : Nat}
    (hl : l < 2 * k.cur_vars) (hval : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg l]) := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hval
  have hlvl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hs := hw.level0_sound i hi hlvl0; rwa [heq] at hs

theorem entails_eval_true {f : CNF Nat} {l : Nat} (h : f.EntailsClause (cnfClause [l]))
    {α : Nat → Bool} (hα : f.Sat α) : evalLitVal α l = true := by
  have hs := CNF.entails_clause_def.mp h α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at hs
  simpa using hs

theorem entails_neg_eval_false {f : CNF Nat} {l : Nat}
    (h : f.EntailsClause (cnfClause [litNeg l])) {α : Nat → Bool} (hα : f.Sat α) :
    evalLitVal α l = false := by
  have ht := entails_eval_true h hα
  rw [evalLitVal_litNeg] at ht
  cases hb : evalLitVal α l <;> simp [hb] at ht ⊢

theorem bv32_ushr1_lt_of_lt2 {l : BitVec 32} {n : Nat} (hl : (l >>> 1).toNat < n) :
    l.toNat < 2 * n := by
  have h1 : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (l >>> (1 : Nat)).toNat < n at hl; rw [h1] at hl; omega

theorem bv32_div2_lt_of_lt2 {l : BitVec 32} {n : Nat} (hl : l.toNat < 2 * n) :
    (l >>> 1).toNat < n := by
  change (l >>> (1 : Nat)).toNat < n
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

theorem bv64_shl2_or_low2_and3 {w s : BitVec 64} (hs : s.toNat < 4) :
    ((w <<< (2 : Nat)) ||| s) &&& 3#64 = s := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases hi2 : i < 2
  · have h3 : (3#64 : BitVec 64).getLsbD i = true := by
      rcases i with _ | _ | i' <;> first | decide | omega
    have hns : ¬ (2 ≤ i) := by omega
    simp [h3, hns]
  · have h2p : 4 ≤ 2 ^ i := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 2 ≤ i)
    have h3 : (3#64 : BitVec 64).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow (by omega)]; simp [hi]
    have hs0 : s.getLsbD i = false := by
      rw [← BitVec.testBit_toNat]; exact Nat.testBit_lt_two_pow (by omega)
    simp [h3, hs0]

private theorem full_mask_bit_aux :
    ∀ u : Fin 9, 2 ≤ u.val → ∀ k : Fin 8, k.val < u.val →
      ((1#32 <<< BitVec.ofNat 32 u.val) - 1#32).toNat.testBit k.val = true := by decide

theorem testBit_full_mask_iff {ua : BitVec 32} (hlo : 2 ≤ ua.toNat) (hhi : ua.toNat ≤ 8)
    {k : Nat} (hk : k < ua.toNat) :
    (((1#32 <<< ua) - 1#32).toNat.testBit k) = true := by
  have hua : BitVec.ofNat 32 ua.toNat = ua := BitVec.eq_of_toNat_eq (by simp)
  simpa [hua] using full_mask_bit_aux ⟨ua.toNat, by omega⟩ hlo ⟨k, by omega⟩ hk

private theorem shl_bit_aux :
    ∀ k : Fin 8, ∀ b : Fin 8,
      ((1#32 <<< BitVec.ofNat 32 k.val).toNat.testBit b.val) = decide (b.val = k.val) := by
  decide

private theorem shl_lt_256_aux :
    ∀ k : Fin 8, (1#32 <<< BitVec.ofNat 32 k.val).toNat < 256 := by decide

theorem testBit_or_shl_eq {mask : BitVec 32} {k : BitVec 32} (hk : k.toNat < 8)
    {b : Nat} (hb : b < 32) :
    ((mask ||| (1#32 <<< k)).toNat.testBit b) =
      (mask.toNat.testBit b || decide (b = k.toNat)) := by
  have hk_eq : BitVec.ofNat 32 k.toNat = k := BitVec.eq_of_toNat_eq (by simp)
  have hshl : (1#32 <<< BitVec.ofNat 32 k.toNat) = 1#32 <<< k := by rw [hk_eq]
  rw [← hshl, BitVec.toNat_or, Nat.testBit_or]
  by_cases hlt : b < 8
  · rw [shl_bit_aux ⟨k.toNat, hk⟩ ⟨b, hlt⟩]
  · have h1 : (1#32 <<< BitVec.ofNat 32 k.toNat).toNat < 2 ^ b := by
      have h256 := shl_lt_256_aux ⟨k.toNat, hk⟩
      have hpow : 2 ^ 8 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 8 ≤ b)
      have h256' : (2 ^ 8 : Nat) = 256 := by decide
      exact Nat.lt_of_lt_of_le h256 (h256' ▸ hpow)
    rw [Nat.testBit_lt_two_pow h1]; simp [show b ≠ k.toNat by omega]

theorem andMatch_sound_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs_ent : Nat} {rhs : List Nat} {tmp : List (BitVec 32)} {ua : Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs_ent rhs)
    (hfwd : ∀ p (hp : p < rhs.length), ∃ er < 2 * k.cur_vars,
      LitEquiv (cnfOfClauses F_cur) rhs[p] er ∧
      (k.vals[er]?.getD 0#8 = 1#8 ∨ ∃ j < ua, er = (tmp[j]?.getD 0#32).toNat))
    (hbwd : ∀ j < ua, ∃ p < rhs.length,
      LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) (tmp[j]?.getD 0#32).toNat) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs_ent =
        (List.range ua).all (fun j => evalLitVal α (tmp[j]?.getD 0#32).toNat) := by
  intro α hα
  rw [andGateDef_eval hα hand]
  by_cases hfall : (List.range ua).all (fun j => evalLitVal α (tmp[j]?.getD 0#32).toNat) = true
  · rw [hfall, List.all_eq_true]
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hl
    obtain ⟨er, her_lt, heqv, hv | ⟨j, hj, rfl⟩⟩ := hfwd p hp
    · have htr := entails_eval_true (vals1_entails hw hcl0 her_lt hv) hα
      rwa [litEquiv_eval hα heqv]
    · have ht := List.all_eq_true.mp hfall j (List.mem_range.mpr hj)
      rw [litEquiv_eval hα heqv]; exact ht
  · have hfalse : ((List.range ua).all fun j => evalLitVal α (tmp[j]?.getD 0#32).toNat) = false :=
      Bool.eq_false_iff.mpr hfall
    rw [hfalse, List.all_eq_false]
    rw [List.all_eq_false] at hfalse
    obtain ⟨j, hj_mem, hj_f⟩ := hfalse
    have hj : j < ua := List.mem_range.mp hj_mem
    obtain ⟨p, hp, heqv⟩ := hbwd j hj
    refine ⟨rhs[p], List.getElem_mem hp, ?_⟩
    rw [List.getElem?_eq_getElem hp, Option.getD_some] at heqv
    rw [litEquiv_eval hα heqv]
    exact hj_f

theorem andFold_has_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs0 lhs : Nat} {rhs : List Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs0 rhs)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0 lhs)
    (hex : ∃ x ∈ rhs, ∃ r < 2 * k.cur_vars,
      LitEquiv (cnfOfClauses F_cur) x r ∧ k.vals[r]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs]) := by
  refine entails_of_eval_mem fun α hα => ?_
  obtain ⟨x, hx, r, hr_lt, heqv, hval⟩ := hex
  have hrf : evalLitVal α r = false :=
    entails_neg_eval_false (valsff_entails_neg hw hcl0 hr_lt hval) hα
  have hxf : evalLitVal α x = false := (litEquiv_eval hα heqv).trans hrf
  have hall_f : rhs.all (evalLitVal α) = false :=
    List.all_eq_false.mpr ⟨x, hx, by simp [hxf]⟩
  have hl0 := andGateDef_eval hα hand
  rw [hall_f] at hl0
  refine ⟨litNeg lhs, List.mem_cons_self .., ?_⟩
  rw [evalLitVal_litNeg, ← litEquiv_eval hα hlhs, hl0]; rfl

theorem andFold_all_true_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs0 lhs : Nat} {rhs : List Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs0 rhs)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0 lhs)
    (hall : ∀ x ∈ rhs, ∃ r < 2 * k.cur_vars,
      LitEquiv (cnfOfClauses F_cur) x r ∧ k.vals[r]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lhs]) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hall_t : rhs.all (evalLitVal α) = true := List.all_eq_true.mpr fun x hx => by
    obtain ⟨r, hr_lt, heqv, hval⟩ := hall x hx
    rw [litEquiv_eval hα heqv]
    exact entails_eval_true (vals1_entails hw hcl0 hr_lt hval) hα
  have hl0 := andGateDef_eval hα hand
  rw [hall_t] at hl0
  exact ⟨lhs, List.mem_cons_self .., by rw [← litEquiv_eval hα hlhs, hl0]⟩

theorem andFold_clash_entails {F_cur : List (List Nat)} {lhs0 lhs : Nat}
    {rhs unass : List Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs0 rhs)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0 lhs)
    (hsub : ∀ l ∈ unass, ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x l)
    {z : Nat} (hz1 : z ∈ unass) (hz2 : litNeg z ∈ unass) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs]) := by
  refine entails_of_eval_mem fun α hα => ?_
  obtain ⟨x1, hx1, he1⟩ := hsub z hz1
  obtain ⟨x2, hx2, he2⟩ := hsub (litNeg z) hz2
  have hboth : (evalLitVal α x1 && evalLitVal α x2) = false := by
    rw [litEquiv_eval hα he1, litEquiv_eval hα he2, evalLitVal_litNeg]
    cases evalLitVal α z <;> rfl
  have hall_f : rhs.all (evalLitVal α) = false := by
    cases h1 : evalLitVal α x1 with
    | false => exact List.all_eq_false.mpr ⟨x1, hx1, by simp [h1]⟩
    | true =>
      have h2 : evalLitVal α x2 = false := by simpa [h1] using hboth
      exact List.all_eq_false.mpr ⟨x2, hx2, by simp [h2]⟩
  have hl0 := andGateDef_eval hα hand
  rw [hall_f] at hl0
  refine ⟨litNeg lhs, List.mem_cons_self .., ?_⟩
  rw [evalLitVal_litNeg, ← litEquiv_eval hα hlhs, hl0]; rfl

theorem andFold_eval_iff {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs0 lhs : Nat} {rhs unass : List Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs0 rhs)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0 lhs)
    (hfwd : ∀ x ∈ rhs, ∃ r < 2 * k.cur_vars,
      LitEquiv (cnfOfClauses F_cur) x r ∧ (k.vals[r]?.getD 0#8 = 1#8 ∨ r ∈ unass))
    (hbwd : ∀ l ∈ unass, ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x l) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs = unass.all (evalLitVal α) := by
  intro α hα
  rw [← litEquiv_eval hα hlhs, andGateDef_eval hα hand]
  by_cases hu : unass.all (evalLitVal α) = true
  · rw [hu, List.all_eq_true]; intro x hx
    obtain ⟨r, hr_lt, heqv, hval | hmem⟩ := hfwd x hx
    · rw [litEquiv_eval hα heqv]
      exact entails_eval_true (vals1_entails hw hcl0 hr_lt hval) hα
    · rw [litEquiv_eval hα heqv]
      exact List.all_eq_true.mp hu r hmem
  · have huf : unass.all (evalLitVal α) = false := Bool.eq_false_iff.mpr hu
    rw [huf, List.all_eq_false]
    rw [List.all_eq_false] at huf
    obtain ⟨l, hl, hlf⟩ := huf
    obtain ⟨x, hx, heqv⟩ := hbwd l hl
    refine ⟨x, hx, ?_⟩
    rw [litEquiv_eval hα heqv]; exact hlf

theorem andFold_ua1_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs0 lhs u0 : Nat} {rhs : List Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs0 rhs)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0 lhs)
    (hfwd : ∀ x ∈ rhs, ∃ r < 2 * k.cur_vars,
      LitEquiv (cnfOfClauses F_cur) x r ∧ (k.vals[r]?.getD 0#8 = 1#8 ∨ r = u0))
    (hbwd : ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x u0) :
    LitEquiv (cnfOfClauses F_cur) lhs u0 := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  have hev := andFold_eval_iff hw hcl0 hand hlhs (unass := [u0])
    (fun x hx => by
      obtain ⟨r, hr, he, h⟩ := hfwd x hx
      exact ⟨r, hr, he, h.elim Or.inl fun h => Or.inr (h ▸ List.mem_cons_self ..)⟩)
    (fun l hl => by simp at hl; rwa [hl]) α hα
  simpa using hev

theorem andFold_lhs_true_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs : Nat} (hlhs_lt : lhs < 2 * k.cur_vars) (hval : k.vals[lhs]?.getD 0#8 = 1#8)
    {us : List Nat}
    (hev : ∀ α : Nat → Bool,
      (cnfOfClauses F_cur).Sat α → evalLitVal α lhs = us.all (evalLitVal α)) :
    ∀ u ∈ us, (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := fun u hu => by
  refine entails_of_eval_mem fun α hα => ?_
  have h1 := entails_eval_true (vals1_entails hw hcl0 hlhs_lt hval) hα
  rw [hev α hα, List.all_eq_true] at h1
  exact ⟨u, List.mem_cons_self .., h1 u hu⟩

end Helpers

/-! ## 3. `Func.wp` Proofs for M3b Congruence Helpers #1–#4 -/

section HelperProofs

open scoped FullArenaTactics FullCongTactics

theorem m3_cong_mark_trail_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, m3CongMarkTrailSpec a m Q X → Func.wp Γ full_cong_mark_trail_body a m Q X := by
  rintro ⟨h, prev_te, ep, ⟨⟩⟩ m0 Q X ⟨c, F_cur, s, R, rfl, hlen, hrepr0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hte_le := hlen.core_ok.trail_end_le
  have hrl0 := hlen.core_ok.repr_len
  have htl0 := hlen.scratch_ok.tarjan_mark_len
  have htrll := hlen.core_ok.trl_len
  fc_steps
  refine wp_loop_inv
    (fun (i, ()) mi => ∃ (repri tmki : List (BitVec 32)),
      repri.length = 2 * c.max_vars ∧ tmki.length = 2 * c.max_vars ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) repri ∧
      (FullMem c { s with core := { s.core with repr := repri }
                          scratch := { s.scratch with tarjan_mark := tmki } } ⋆ R) mi)
    (fun (i, ()) _ => s.core.trail_end - i.toNat)
    (fun J hJ => by
      fc_let
      exact hJ (prev_te, ()) m0 ⟨s.core.repr, s.scratch.tarjan_mark, hrl0, htl0, hrepr0, hm0⟩)
    (fun J (i, ()) mi ⟨repri, tmki, hrli, htli, hrepri, hmi⟩ ihi => ?_)
  let sti : FullState :=
    { s with core := { s.core with repr := repri }
             scratch := { s.scratch with tarjan_mark := tmki } }
  have hleni : sti.LengthsOk c :=
    ⟨{ hlen.core_ok with repr_len := hrli }, { hlen.scratch_ok with tarjan_mark_len := htli }⟩
  fc_split_fast
  · have hi_lt : i.toNat < s.core.trail_end := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
    have hi_trl : i.toNat < sti.core.trl.length := by dsimp [sti]; omega
    have hi1_n : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    let lit := sti.core.trl[i.toNat]'hi_trl
    let lv := lit >>> 1
    fc_to_group; refine wp_join_group (ts := [])
      (fun () mj => ∃ reprj tmkj : List (BitVec 32),
        reprj.length = 2 * c.max_vars ∧ tmkj.length = 2 * c.max_vars ∧
        FullCongReprInv F_cur (2 * s.core.cur_vars) reprj ∧
        (FullMem c { s with core := { s.core with repr := reprj }
                            scratch := { s.scratch with tarjan_mark := tmkj } } ⋆ R) mj)
      ?_ ?_
    · rintro _ ⟨⟩ mj ⟨reprj, tmkj, hrlj, htlj, hreprj, hmj⟩
      fc_let; exact ihi (i + 1#64, ()) mj (by dsimp only; omega)
        ⟨reprj, tmkj, hrlj, htlj, hreprj, hmj⟩
    · intro Jj hJj; fc_split_fast
      · have hlv_lt : lv.toNat < s.core.cur_vars := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc
          change (lv.setWidth 64).toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat at hc
          rw [bv_zext32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc; exact hc
        have hlit_lt : lit.toNat < 2 * s.core.cur_vars := bv32_ushr1_lt_of_lt2 hlv_lt
        have hlv_arr : (lv.setWidth 64).toNat < sti.scratch.tarjan_mark.length := by
          rw [bv_zext32_toNat]; dsimp [sti]; omega
        fc_steps
        let tmka := tmki.set (lv.setWidth 64).toNat ep
        let stia : FullState := { sti with scratch := { sti.scratch with tarjan_mark := tmka } }
        have hm_set1 : (FullMem c stia ⋆ R) m := hm
        c0_call hFind
        refine ⟨F_cur, 2 * s.core.cur_vars, repri, FullReprRest c stia ⋆ R, hrepri, hlit_lt,
          focus_full_repr hm_set1, fun r repr1 m1 hrl1 hrepr1 _ hr_lt _ hm1 => ?_⟩
        let st1 : FullState := { stia with core := { stia.core with repr := repr1 } }
        have hm1' : (FullMem c st1 ⋆ R) m1 := unfocus_full_repr hm1; clear hm1
        let rv := r >>> 1
        fc_to_group; refine wp_join_group (ts := [])
          (fun () mk => ∃ tmk_k : List (BitVec 32), tmk_k.length = 2 * c.max_vars ∧
            (FullMem c { st1 with scratch := { st1.scratch with tarjan_mark := tmk_k } } ⋆ R) mk)
          ?_ ?_
        · rintro _ ⟨⟩ mk ⟨tmk_k, htl_k, hmk⟩
          fc_let; exact hJj () mk ⟨repr1, tmk_k, by omega, htl_k, hrepr1, hmk⟩
        · intro Jk hJk; fc_split_fast
          · have hrv_lt : rv.toNat < s.core.cur_vars := by
              simp only [BitVec.ult, decide_eq_true_eq] at hc
              change (rv.setWidth 64).toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat at hc
              rw [bv_zext32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc; exact hc
            have hrv_arr : (rv.setWidth 64).toNat < st1.scratch.tarjan_mark.length := by
              rw [bv_zext32_toNat]; dsimp [st1, stia, tmka]; rw [List.length_set]; omega
            fc_steps
            exact hJk () m ⟨_, by dsimp [st1, stia, tmka]; simp [htli], hm⟩
          · fc_let; exact hJk () m1 ⟨tmka, by simp [tmka, htli], hm1'⟩
      · fc_let; exact hJj () mi ⟨repri, tmki, hrli, htli, hrepri, hmi⟩
  · fc_let; exact hQ repri tmki mi hleni hrepri hmi

theorem m3_cong_unit_fold_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, Full.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hMark : ∀ a m Q X, m3CongMarkTrailSpec a m Q X →
      Γ "full_cong_mark_trail" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, m3CongUnitFoldSpec a m Q X → Func.wp Γ full_cong_unit_fold_body a m Q X := by
  rintro ⟨h, lit, next_ep, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hext, hcl0, hdm, hrepr, hlit, hent, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hlit_vals : (lit.setWidth 64).toNat < s.core.vals.length := by
    rw [bv_zext32_toNat, hlen.core_ok.vals_len]; omega
  fc_steps
  fc_split_fast
  · fc_steps
    exact hQ 0#64 s m0 hlen hw hmk hnd hext hcl0 hdm rfl rfl rfl rfl rfl rfl hrepr
      (Or.inl rfl) (fun h => by cases h) hm0
  · fc_steps; c0_call hAddUnit
    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, fun _ => hent, hm0, ?_⟩
    dsimp only
    intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      ph' ta' ba' pt' pb' hp' ps' hlen_hp qsi' qss' m1 hlen1 hw1 hcl1 hu_ok hu_fail hm1
    let s1 : FullState :=
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              cur_level := cl', unassigned := unass', unflushed := unfl',
                              inconsistent := inc' }
        scratch := { s.scratch with phases := ph', target_assigned := ta', best_assigned := ba',
                                    phases_target := pt', phases_best := pb', heap := hp',
                                    pos := ps', heap_len := hlen_hp, q_search_idx := qsi',
                                    q_search_stamp := qss' } }
    obtain ⟨hmk1, hnd1, hext1, _, hdm1⟩ := fullAddUnitSpec_fullDenseInvW (s' := s1)
      hmk hnd hext hdm hcl1 rfl rfl rfl rfl rfl rfl rfl
    fc_split_fast
    · have _hc_eq : ok = true := hc
      clear hc
      fc_steps
      let s1c : FullState :=
        { s1 with scratch := { s1.scratch with cong_cnt := s1.scratch.cong_cnt + 1#64 } }
      have hlen1c : s1c.LengthsOk c := ⟨hlen1.core_ok, { hlen1.scratch_ok with }⟩
      have hext1c : FullExtScratchOk c s1c := fullExtScratchOk_of_eq hext1 rfl rfl rfl rfl
      c0_call hMark
      refine ⟨c, F_cur, s1c, R, rfl, hlen1c, hrepr, hm, fun repr2 tmk2 m2 hlen2 hrepr2 hm2 => ?_⟩
      let s2 : FullState :=
        { s1c with
          core := { s1c.core with repr := repr2 }
          scratch := { s1c.scratch with tarjan_mark := tmk2 } }
      have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw1 repr2
      have hmk2 := fullLitMarksClear_of_eq hmk1 rfl rfl
      have hnd2 := fullArenaVarsNodup_of_eq hnd1 rfl rfl
      have hext2 := fullExtScratchOk_of_eq hext1c rfl rfl rfl rfl
      fc_split_fast
      · have hne0 : inc' ≠ 0#64 := bne_iff_ne.mp hc
        fc_steps
        exact hQ 2#64 s2 m2 hlen2 hw2 hmk2 hnd2 hext2 hcl1 hdm1 rfl rfl rfl rfl rfl rfl hrepr2
          (Or.inr (Or.inr rfl)) (fun _ => ⟨hne0, unsat_of_inconsistent_w hw2 hne0⟩) hm2
      · fc_steps
        exact hQ 1#64 s2 m2 hlen2 hw2 hmk2 hnd2 hext2 hcl1 hdm1 rfl rfl rfl rfl rfl rfl hrepr2
          (Or.inr (Or.inl rfl)) (fun h => by cases h) hm2
    · obtain ⟨huns, hinc_ne⟩ := hu_ok hlit hc
      fc_steps; c0_call hMark
      refine ⟨c, F_cur, s1, R, rfl, hlen1, hrepr, hm1, fun repr2 tmk2 m2 hlen2 hrepr2 hm2 => ?_⟩
      let s2 : FullState :=
        { s1 with
          core := { s1.core with repr := repr2 }
          scratch := { s1.scratch with tarjan_mark := tmk2 } }
      have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw1 repr2
      have hmk2 := fullLitMarksClear_of_eq hmk1 rfl rfl
      have hnd2 := fullArenaVarsNodup_of_eq hnd1 rfl rfl
      have hext2 := fullExtScratchOk_of_eq hext1 rfl rfl rfl rfl
      fc_steps
      exact hQ 2#64 s2 m2 hlen2 hw2 hmk2 hnd2 hext2 hcl1 hdm1 rfl rfl rfl rfl rfl rfl hrepr2
        (Or.inr (Or.inr rfl)) (fun _ => ⟨hinc_ne, huns⟩) hm2

theorem m3_cong_equiv_fold_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hAddUnit : ∀ a m Q X, Full.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hMark : ∀ a m Q X, m3CongMarkTrailSpec a m Q X →
      Γ "full_cong_mark_trail" [i64, i64, i32] [] a m Q X)
    (hMerge : ∀ a m Q X, fullCongMergeSpec a m Q X →
      Γ "full_cong_merge" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m3CongEquivFoldSpec a m Q X → Func.wp Γ full_cong_equiv_fold_body a m Q X := by
  rintro ⟨h, a, b, next_ep, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hext, hcl0, hdm, hrepr, ha, hb, heqv, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hrl0 := hlen.core_ok.repr_len
  fc_steps; c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, FullReprRest c s ⋆ R, hrepr, ha,
    focus_full_repr hm0, fun ra repr1 m1 hrl1 hrepr1 _ hra_lt ha_ra hm1 => ?_⟩
  let s1 : FullState := { s with core := { s.core with repr := repr1 } }
  have hlen1 : s1.LengthsOk c :=
    ⟨{ hlen.core_ok with repr_len := hrl1.trans hrl0 }, hlen.scratch_ok⟩
  have hw1 : FullWitnessInv c F0 F_cur s1.core := fullWitnessInv_with_repr hw repr1
  have hm1' : (FullMem c s1 ⋆ R) m1 := unfocus_full_repr hm1; clear hm1
  c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, repr1, FullReprRest c s1 ⋆ R, hrepr1, hb,
    focus_full_repr hm1', fun rb repr2 m2 hrl2 hrepr2 _ hrb_lt hb_rb hm2 => ?_⟩
  let s2 : FullState := { s1 with core := { s1.core with repr := repr2 } }
  have hlen2 : s2.LengthsOk c :=
    ⟨{ hlen1.core_ok with repr_len := hrl2.trans hlen1.core_ok.repr_len }, hlen1.scratch_ok⟩
  have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw1 repr2
  have hm2' : (FullMem c s2 ⋆ R) m2 := unfocus_full_repr hm2; clear hm0 hm1' hm2
  have hrab_eqv : LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat :=
    ha_ra.symm.trans (heqv.trans hb_rb)
  have hra_vals : (ra.setWidth 64).toNat < s2.core.vals.length := by
    rw [bv_zext32_toNat, hlen2.core_ok.vals_len]; omega
  have hrb_vals : (rb.setWidth 64).toNat < s2.core.vals.length := by
    rw [bv_zext32_toNat, hlen2.core_ok.vals_len]; omega
  fc_to_group
  refine wp_join_group (ts := [.bool])
    (fun (ch_j, ()) mj => ∃ sj : FullState,
      sj.LengthsOk c ∧ FullWitnessInv c F0 F_cur sj.core ∧
      FullLitMarksClear c sj ∧ FullArenaVarsNodup sj ∧ FullExtScratchOk c sj ∧
      sj.core.cur_level = 0 ∧ sj.core.dense_mode ≠ 0#64 ∧
      sj.core.cur_vars = s.core.cur_vars ∧ sj.core.fuel = s.core.fuel ∧
      sj.core.arena = s.core.arena ∧ sj.core.arena_len = s.core.arena_len ∧
      sj.core.tmp = s.core.tmp ∧ sj.scratch.scratch_buf = s.scratch.scratch_buf ∧
      FullCongReprInv F_cur (2 * sj.core.cur_vars) sj.core.repr ∧
      (FullMem c sj ⋆ R) mj)
    ?_ ?_
  · rintro _ ⟨ch_j, ⟨⟩⟩ mj ⟨sj, hlen_j, hw_j, hmk_j, hnd_j, hext_j, hcl_j, hdm_j,
      hcv_j, hfl_j, har_j, hal_j, htmp_j, hscr_j, hrepr_j, hmj⟩
    fc_to_group
    refine wp_join_group (ts := [.bool])
      (fun (ch_k, ()) mk => ∃ sk : FullState,
        sk.LengthsOk c ∧ FullWitnessInv c F0 F_cur sk.core ∧
        FullLitMarksClear c sk ∧ FullArenaVarsNodup sk ∧ FullExtScratchOk c sk ∧
        sk.core.cur_level = 0 ∧ sk.core.dense_mode ≠ 0#64 ∧
        sk.core.cur_vars = s.core.cur_vars ∧ sk.core.fuel = s.core.fuel ∧
        sk.core.arena = s.core.arena ∧ sk.core.arena_len = s.core.arena_len ∧
        sk.core.tmp = s.core.tmp ∧ sk.scratch.scratch_buf = s.scratch.scratch_buf ∧
        FullCongReprInv F_cur (2 * sk.core.cur_vars) sk.core.repr ∧
        (FullMem c sk ⋆ R) mk)
      ?_ ?_
    · rintro _ ⟨ch_k, ⟨⟩⟩ mk ⟨sk, hlen_k, hw_k, hmk_k, hnd_k, hext_k, hcl_k, hdm_k,
        hcv_k, hfl_k, har_k, hal_k, htmp_k, hscr_k, hrepr_k, hmk_mem⟩
      fc_to_group
      refine wp_join_group (ts := [])
        (fun () mf => ∃ sf : FullState,
          sf.LengthsOk c ∧ FullWitnessInv c F0 F_cur sf.core ∧
          FullLitMarksClear c sf ∧ FullArenaVarsNodup sf ∧ FullExtScratchOk c sf ∧
          sf.core.cur_level = 0 ∧ sf.core.dense_mode ≠ 0#64 ∧
          sf.core.cur_vars = s.core.cur_vars ∧ sf.core.fuel = s.core.fuel ∧
          sf.core.arena = s.core.arena ∧ sf.core.arena_len = s.core.arena_len ∧
          sf.core.tmp = s.core.tmp ∧ sf.scratch.scratch_buf = s.scratch.scratch_buf ∧
          FullCongReprInv F_cur (2 * sf.core.cur_vars) sf.core.repr ∧
          (FullMem c sf ⋆ R) mf)
        ?_ ?_
      · rintro _ ⟨⟩ mf ⟨sf, hlen_f, hw_f, hmk_f, hnd_f, hext_f, hcl_f, hdm_f,
          hcv_f, hfl_f, har_f, hal_f, htmp_f, hscr_f, hrepr_f, hmf⟩
        fc_split_fast
        · fc_steps
          exact hQ 2#64 sf mf hlen_f hw_f hmk_f hnd_f hext_f hcl_f hdm_f hcv_f hfl_f
            har_f hal_f htmp_f hscr_f hrepr_f (Or.inr (Or.inr rfl))
            (fun _ => unsat_of_inconsistent_w hw_f (bne_iff_ne.mp hc)) hmf
        · fc_split_fast
          · fc_steps
            exact hQ 1#64 sf mf hlen_f hw_f hmk_f hnd_f hext_f hcl_f hdm_f hcv_f hfl_f
              har_f hal_f htmp_f hscr_f hrepr_f (Or.inr (Or.inl rfl)) (fun h => by cases h) hmf
          · fc_steps
            exact hQ 0#64 sf mf hlen_f hw_f hmk_f hnd_f hext_f hcl_f hdm_f hcv_f hfl_f
              har_f hal_f htmp_f hscr_f hrepr_f (Or.inl rfl) (fun h => by cases h) hmf
      · intro Jf hJf; fc_split_fast
        · fc_steps; c0_call hMark
          refine ⟨c, F_cur, sk, R, rfl, hlen_k, hcv_k ▸ hrepr_k, hmk_mem,
            fun reprf tmkf mf hlen_f hrepr_f hmf => ?_⟩
          let sf : FullState :=
            { sk with core := { sk.core with repr := reprf }
                      scratch := { sk.scratch with tarjan_mark := tmkf } }
          exact hJf () mf ⟨sf, hlen_f, fullWitnessInv_with_repr hw_k reprf,
            fullLitMarksClear_of_eq hmk_k rfl rfl, fullArenaVarsNodup_of_eq hnd_k rfl rfl,
            fullExtScratchOk_of_eq hext_k rfl rfl rfl rfl, hcl_k, hdm_k, hcv_k, hfl_k,
            har_k, hal_k, htmp_k, hscr_k, hcv_k ▸ hrepr_f, hmf⟩
        · fc_let
          exact hJf () mk ⟨sk, hlen_k, hw_k, hmk_k, hnd_k, hext_k, hcl_k, hdm_k,
            hcv_k, hfl_k, har_k, hal_k, htmp_k, hscr_k, hrepr_k, hmk_mem⟩
    · intro Jk hJk; fc_steps; c0_call hMerge
      refine ⟨c, F0, F_cur, sj, R, rfl, hlen_j, hw_j, hmk_j, hnd_j, hext_j, hcl_j, hdm_j,
        hcv_j ▸ hrepr_j, hcv_j ▸ hra_lt, hcv_j ▸ hrb_lt, hrab_eqv, hmj,
        fun cm sm mm hlen_m hw_m hmk_m hnd_m hext_m hcl_m hdm_m hcv_m hfl_m har_m hal_m
          htmp_m hscr_m hrepr_m hmm => ?_⟩
      have hcv_ms : sm.core.cur_vars = s.core.cur_vars := hcv_m.trans hcv_j
      fc_split_fast
      · fc_to_group; refine wp_join_group (ts := [])
          (fun () ma => ∃ tmka : List (BitVec 32), tmka.length = 2 * c.max_vars ∧
            (FullMem c { sm with scratch := { sm.scratch with tarjan_mark := tmka } } ⋆ R) ma)
          ?_ ?_
        · rintro _ ⟨⟩ ma ⟨tmka, htl_a, hma⟩
          let sa : FullState := { sm with scratch := { sm.scratch with tarjan_mark := tmka } }
          have hlena : sa.LengthsOk c :=
            ⟨hlen_m.core_ok, { hlen_m.scratch_ok with tarjan_mark_len := htl_a }⟩
          fc_to_group; refine wp_join_group (ts := [])
            (fun () mb => ∃ tmkb : List (BitVec 32), tmkb.length = 2 * c.max_vars ∧
              (FullMem c { sm with scratch := { sm.scratch with tarjan_mark := tmkb } } ⋆ R) mb)
            ?_ ?_
          · rintro _ ⟨⟩ mb ⟨tmkb, htl_b, hmb⟩
            let sb : FullState := { sm with scratch := { sm.scratch with tarjan_mark := tmkb } }
            have hlenb : sb.LengthsOk c :=
              ⟨hlen_m.core_ok, { hlen_m.scratch_ok with tarjan_mark_len := htl_b }⟩
            fc_to_group; refine wp_join_group (ts := [])
              (fun () mc => ∃ tmkc : List (BitVec 32), tmkc.length = 2 * c.max_vars ∧
                (FullMem c { sm with scratch := { sm.scratch with tarjan_mark := tmkc } } ⋆ R) mc)
              ?_ ?_
            · rintro _ ⟨⟩ mc ⟨tmkc, htl_c, hmc⟩
              let sc : FullState := { sm with scratch := { sm.scratch with tarjan_mark := tmkc } }
              have hlenc : sc.LengthsOk c :=
                ⟨hlen_m.core_ok, { hlen_m.scratch_ok with tarjan_mark_len := htl_c }⟩
              fc_to_group; refine wp_join_group (ts := [])
                (fun () md => ∃ tmkd : List (BitVec 32), tmkd.length = 2 * c.max_vars ∧
                  (FullMem c { sm with scratch := { sm.scratch with tarjan_mark := tmkd } } ⋆ R)
                    md)
                ?_ ?_
              · rintro _ ⟨⟩ md ⟨tmkd, htl_d, hmd⟩
                let sd : FullState :=
                  { sm with scratch := { sm.scratch with tarjan_mark := tmkd } }
                have hlend : sd.LengthsOk c :=
                  ⟨hlen_m.core_ok, { hlen_m.scratch_ok with tarjan_mark_len := htl_d }⟩
                fc_let
                exact hJk (true, ()) md ⟨sd, hlend, hw_m, hmk_m, hnd_m, hext_m, hcl_m, hdm_m,
                  hcv_ms, hfl_m.trans hfl_j, har_m.trans har_j, hal_m.trans hal_j,
                  htmp_m.trans htmp_j, hscr_m.trans hscr_j, hcv_m ▸ hrepr_m, hmd⟩
              · intro Jd hJd; fc_split_fast
                · have hlt : (rb >>> 1).toNat < s.core.cur_vars := bv32_div2_lt_of_lt2 hrb_lt
                  have harr : ((rb >>> 1).setWidth 64).toNat < sc.scratch.tarjan_mark.length := by
                    rw [bv_zext32_toNat]; dsimp [sc]; omega
                  fc_steps; exact hJd () m ⟨tmkc.set ((rb >>> 1).setWidth 64).toNat next_ep,
                    by simp [htl_c], by simpa [sc] using hm⟩
                · fc_let; exact hJd () mc ⟨tmkc, htl_c, hmc⟩
            · intro Jc hJc; fc_split_fast
              · have hlt : (ra >>> 1).toNat < s.core.cur_vars := bv32_div2_lt_of_lt2 hra_lt
                have harr : ((ra >>> 1).setWidth 64).toNat < sb.scratch.tarjan_mark.length := by
                  rw [bv_zext32_toNat]; dsimp [sb]; omega
                fc_steps; exact hJc () m ⟨tmkb.set ((ra >>> 1).setWidth 64).toNat next_ep,
                  by simp [htl_b], by simpa [sb] using hm⟩
              · fc_let; exact hJc () mb ⟨tmkb, htl_b, hmb⟩
          · intro Jb hJb; fc_split_fast
            · have hlt : (b >>> 1).toNat < s.core.cur_vars := bv32_div2_lt_of_lt2 hb
              have harr : ((b >>> 1).setWidth 64).toNat < sa.scratch.tarjan_mark.length := by
                rw [bv_zext32_toNat]; dsimp [sa]; omega
              fc_steps; exact hJb () m ⟨tmka.set ((b >>> 1).setWidth 64).toNat next_ep,
                by simp [htl_a], by simpa [sa] using hm⟩
            · fc_let; exact hJb () ma ⟨tmka, htl_a, hma⟩
        · intro Ja hJa; fc_split_fast
          · have hlt : (a >>> 1).toNat < s.core.cur_vars := bv32_div2_lt_of_lt2 ha
            have harr : ((a >>> 1).setWidth 64).toNat < sm.scratch.tarjan_mark.length := by
              rw [bv_zext32_toNat, hlen_m.scratch_ok.tarjan_mark_len]; omega
            fc_steps
            exact hJa () m
              ⟨sm.scratch.tarjan_mark.set ((a >>> 1).setWidth 64).toNat next_ep,
               by simp [hlen_m.scratch_ok.tarjan_mark_len], hm⟩
          · fc_let; exact hJa () mm ⟨sm.scratch.tarjan_mark, hlen_m.scratch_ok.tarjan_mark_len, hmm⟩
      · fc_let
        exact hJk (ch_j, ()) mm ⟨sm, hlen_m, hw_m, hmk_m, hnd_m, hext_m, hcl_m, hdm_m,
          hcv_ms, hfl_m.trans hfl_j, har_m.trans har_j, hal_m.trans hal_j,
          htmp_m.trans htmp_j, hscr_m.trans hscr_j, hcv_m ▸ hrepr_m, hmm⟩
  · intro Jmid hJmid
    have hj_keep : Jmid (false, ()) m2 := hJmid (false, ()) m2
      ⟨s2, hlen2, hw2, hmk, hnd, hext, hcl0, hdm, rfl, rfl, rfl, rfl, rfl, rfl, hrepr2, hm2'⟩
    have hra_mod : ra.toNat % 18446744073709551616 = ra.toNat := Nat.mod_eq_of_lt (by omega)
    have hrb_mod : rb.toNat % 18446744073709551616 = rb.toNat := Nat.mod_eq_of_lt (by omega)
    fc_split_fast
    · have hva_dom := hw2.vals_domain ra.toNat hra_lt
      have hra_lt' : ra.toNat < s2.core.vals.length := by
        rw [bv_zext32_toNat] at hra_vals; exact hra_vals
      have hva_ne : s2.core.vals[ra.toNat]?.getD 0#8 ≠ 0#8 := by
        rw [List.getElem?_eq_getElem hra_lt', Option.getD_some] at hva_dom ⊢
        exact bv8_ne0_of_signExtend32 hva_dom (by
          rw [bv_zext32_toNat] at *; exact bne_iff_ne.mp hc)
      fc_to_group; refine wp_join_group (ts := [i32])
        (fun (tgt, ()) mt => mt = m2 ∧ tgt.toNat < 2 * s2.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [tgt.toNat]))
        ?_ ?_
      · rintro _ ⟨tgt, ⟨⟩⟩ mt ⟨hmt_eq, htgt_lt, htgt_ent⟩
        subst mt
        have htgt_vals : (tgt.setWidth 64).toNat < s2.core.vals.length := by
          rw [bv_zext32_toNat, hlen2.core_ok.vals_len]; dsimp [s2, s1] at htgt_lt; omega
        fc_split_fast
        · fc_steps; c0_call hAddUnit
          refine ⟨c, F0, F_cur, s2, R, rfl, hlen2, hw2, fun _ => htgt_ent, hm2', ?_⟩
          dsimp only
          intro ok3 vals3 flags3 lvl3 rsns3 trl3 tp3 te3 prop3 cl3 unass3 unfl3 inc3
            ph3 ta3 ba3 pt3 pb3 hp3 ps3 hl3 qsi3 qss3 m3 hlen3 hw3 hcl3 hu_ok _ hm3
          let s3 : FullState :=
            { s2 with
              core := { s2.core with vals := vals3, flags := flags3, lvl := lvl3, rsns := rsns3,
                                     trl := trl3, trail_pos := tp3, trail_end := te3,
                                     propagated := prop3, cur_level := cl3, unassigned := unass3,
                                     unflushed := unfl3, inconsistent := inc3 }
              scratch := { s2.scratch with phases := ph3, target_assigned := ta3,
                                           best_assigned := ba3, phases_target := pt3,
                                           phases_best := pb3, heap := hp3, pos := ps3,
                                           heap_len := hl3, q_search_idx := qsi3,
                                           q_search_stamp := qss3 } }
          obtain ⟨hmk3, hnd3, hext3, _, hdm3⟩ := fullAddUnitSpec_fullDenseInvW (s' := s3)
            hmk hnd hext hdm hcl3 rfl rfl rfl rfl rfl rfl rfl
          fc_split_fast
          · fc_steps
            let s3c : FullState :=
              { s3 with scratch := { s3.scratch with cong_cnt := s3.scratch.cong_cnt + 1#64 } }
            have hlen3c : s3c.LengthsOk c := ⟨hlen3.core_ok, { hlen3.scratch_ok with }⟩
            have hext3c : FullExtScratchOk c s3c := fullExtScratchOk_of_eq hext3 rfl rfl rfl rfl
            exact hJmid (true, ()) m ⟨s3c, hlen3c, hw3, hmk3, hnd3, hext3c, hcl3, hdm3,
              rfl, rfl, rfl, rfl, rfl, rfl, hrepr2, hm⟩
          · obtain ⟨huns3, _⟩ := hu_ok htgt_lt hc
            fc_steps; c0_call hMark
            refine ⟨c, F_cur, s3, R, rfl, hlen3, hrepr2, hm3,
              fun repr4 tmk4 m4 hlen4 hrepr4 hm4 => ?_⟩
            let s4 : FullState :=
              { s3 with core := { s3.core with repr := repr4 }
                        scratch := { s3.scratch with tarjan_mark := tmk4 } }
            fc_steps
            exact hQ 2#64 s4 m4 hlen4 (fullWitnessInv_with_repr hw3 repr4)
              (fullLitMarksClear_of_eq hmk3 rfl rfl) (fullArenaVarsNodup_of_eq hnd3 rfl rfl)
              (fullExtScratchOk_of_eq hext3 rfl rfl rfl rfl) hcl3 hdm3 rfl rfl rfl rfl rfl rfl
              hrepr4 (Or.inr (Or.inr rfl)) (fun _ => huns3) hm4
        · fc_steps; exact hj_keep
      · intro Jt hJt; fc_split_fast
        · have hva1 : s2.core.vals[ra.toNat]?.getD 0#8 = 1#8 := by
            rw [List.getElem?_eq_getElem hra_lt', Option.getD_some] at hva_dom ⊢
            have hc' := hc
            rw [list_getElem_congr (bv_zext32_toNat ra) hra_vals hra_lt'] at hc'
            exact bv8_eq1_of_signExtend32_sgt0 hva_dom hc'
          have hrb_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [rb.toNat]) := by
            have ha_ent := vals1_entails hw2 hcl0 hra_lt hva1
            exact entails_of_eval_mem fun α hα => ⟨rb.toNat, List.mem_cons_self ..,
              (litEquiv_eval hα hrab_eqv).symm.trans (entails_eval_true ha_ent hα)⟩
          fc_let; exact hJt (rb, ()) m2 ⟨rfl, hrb_lt, hrb_ent⟩
        · have hvaff : s2.core.vals[ra.toNat]?.getD 0#8 = 0xFF#8 := by
            rw [List.getElem?_eq_getElem hra_lt', Option.getD_some] at hva_dom hva_ne ⊢
            have hc' := hc
            rw [list_getElem_congr (bv_zext32_toNat ra) hra_vals hra_lt'] at hc'
            exact bv8_ne0_not_signExtend32_sgt0_eqff hva_dom hva_ne (Bool.eq_false_iff.mp hc')
          have hnrb_lt : (rb ^^^ 1#32).toNat < 2 * s2.core.cur_vars := by
            rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hrb_lt
          have hnrb_ent :
              (cnfOfClauses F_cur).EntailsClause (cnfClause [(rb ^^^ 1#32).toNat]) := by
            have ha_ent := valsff_entails_neg hw2 hcl0 hra_lt hvaff
            refine entails_of_eval_mem fun α hα => ⟨(rb ^^^ 1#32).toNat, List.mem_cons_self .., ?_⟩
            rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg, ← litEquiv_eval hα hrab_eqv]
            rw [entails_neg_eval_false ha_ent hα]; rfl
          fc_let; exact hJt (rb ^^^ 1#32, ()) m2 ⟨rfl, hnrb_lt, hnrb_ent⟩
    · fc_split_fast
      · have hvb_dom := hw2.vals_domain rb.toNat hrb_lt
        have hrb_lt' : rb.toNat < s2.core.vals.length := by
          rw [bv_zext32_toNat] at hrb_vals; exact hrb_vals
        have hvb_ne : s2.core.vals[rb.toNat]?.getD 0#8 ≠ 0#8 := by
          rw [List.getElem?_eq_getElem hrb_lt', Option.getD_some] at hvb_dom ⊢
          exact bv8_ne0_of_signExtend32 hvb_dom (by
            rw [bv_zext32_toNat] at *; exact bne_iff_ne.mp hc)
        fc_to_group; refine wp_join_group (ts := [i32])
          (fun (tgt, ()) mt => mt = m2 ∧ tgt.toNat < 2 * s2.core.cur_vars ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause [tgt.toNat]))
          ?_ ?_
        · rintro _ ⟨tgt, ⟨⟩⟩ mt ⟨hmt_eq, htgt_lt, htgt_ent⟩
          subst mt
          have htgt_vals : (tgt.setWidth 64).toNat < s2.core.vals.length := by
            rw [bv_zext32_toNat, hlen2.core_ok.vals_len]; dsimp [s2, s1] at htgt_lt; omega
          fc_split_fast
          · fc_steps; c0_call hAddUnit
            refine ⟨c, F0, F_cur, s2, R, rfl, hlen2, hw2, fun _ => htgt_ent, hm2', ?_⟩
            dsimp only
            intro ok3 vals3 flags3 lvl3 rsns3 trl3 tp3 te3 prop3 cl3 unass3 unfl3 inc3
              ph3 ta3 ba3 pt3 pb3 hp3 ps3 hl3 qsi3 qss3 m3 hlen3 hw3 hcl3 hu_ok _ hm3
            let s3 : FullState :=
              { s2 with
                core := { s2.core with vals := vals3, flags := flags3, lvl := lvl3, rsns := rsns3,
                                       trl := trl3, trail_pos := tp3, trail_end := te3,
                                       propagated := prop3, cur_level := cl3, unassigned := unass3,
                                       unflushed := unfl3, inconsistent := inc3 }
                scratch := { s2.scratch with phases := ph3, target_assigned := ta3,
                                             best_assigned := ba3, phases_target := pt3,
                                             phases_best := pb3, heap := hp3, pos := ps3,
                                             heap_len := hl3, q_search_idx := qsi3,
                                             q_search_stamp := qss3 } }
            obtain ⟨hmk3, hnd3, hext3, _, hdm3⟩ := fullAddUnitSpec_fullDenseInvW (s' := s3)
              hmk hnd hext hdm hcl3 rfl rfl rfl rfl rfl rfl rfl
            fc_split_fast
            · fc_steps
              let s3c : FullState :=
                { s3 with scratch := { s3.scratch with cong_cnt := s3.scratch.cong_cnt + 1#64 } }
              have hlen3c : s3c.LengthsOk c := ⟨hlen3.core_ok, { hlen3.scratch_ok with }⟩
              have hext3c : FullExtScratchOk c s3c := fullExtScratchOk_of_eq hext3 rfl rfl rfl rfl
              exact hJmid (true, ()) m ⟨s3c, hlen3c, hw3, hmk3, hnd3, hext3c, hcl3, hdm3,
                rfl, rfl, rfl, rfl, rfl, rfl, hrepr2, hm⟩
            · obtain ⟨huns3, _⟩ := hu_ok htgt_lt hc
              fc_steps; c0_call hMark
              refine ⟨c, F_cur, s3, R, rfl, hlen3, hrepr2, hm3,
                fun repr4 tmk4 m4 hlen4 hrepr4 hm4 => ?_⟩
              let s4 : FullState :=
                { s3 with core := { s3.core with repr := repr4 }
                          scratch := { s3.scratch with tarjan_mark := tmk4 } }
              fc_steps
              exact hQ 2#64 s4 m4 hlen4 (fullWitnessInv_with_repr hw3 repr4)
                (fullLitMarksClear_of_eq hmk3 rfl rfl) (fullArenaVarsNodup_of_eq hnd3 rfl rfl)
                (fullExtScratchOk_of_eq hext3 rfl rfl rfl rfl) hcl3 hdm3 rfl rfl rfl rfl rfl rfl
                hrepr4 (Or.inr (Or.inr rfl)) (fun _ => huns3) hm4
          · fc_steps; exact hj_keep
        · intro Jt hJt; fc_split_fast
          · have hvb1 : s2.core.vals[rb.toNat]?.getD 0#8 = 1#8 := by
              rw [List.getElem?_eq_getElem hrb_lt', Option.getD_some] at hvb_dom ⊢
              have hc' := hc
              rw [list_getElem_congr (bv_zext32_toNat rb) hrb_vals hrb_lt'] at hc'
              exact bv8_eq1_of_signExtend32_sgt0 hvb_dom hc'
            have hra_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [ra.toNat]) := by
              have hb_ent := vals1_entails hw2 hcl0 hrb_lt hvb1
              exact entails_of_eval_mem fun α hα => ⟨ra.toNat, List.mem_cons_self ..,
                (litEquiv_eval hα hrab_eqv).trans (entails_eval_true hb_ent hα)⟩
            fc_let; exact hJt (ra, ()) m2 ⟨rfl, hra_lt, hra_ent⟩
          · have hvbff : s2.core.vals[rb.toNat]?.getD 0#8 = 0xFF#8 := by
              rw [List.getElem?_eq_getElem hrb_lt', Option.getD_some] at hvb_dom hvb_ne ⊢
              have hc' := hc
              rw [list_getElem_congr (bv_zext32_toNat rb) hrb_vals hrb_lt'] at hc'
              exact bv8_ne0_not_signExtend32_sgt0_eqff hvb_dom hvb_ne (Bool.eq_false_iff.mp hc')
            have hnra_lt : (ra ^^^ 1#32).toNat < 2 * s2.core.cur_vars := by
              rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hra_lt
            have hnra_ent :
                (cnfOfClauses F_cur).EntailsClause (cnfClause [(ra ^^^ 1#32).toNat]) := by
              have hb_ent := valsff_entails_neg hw2 hcl0 hrb_lt hvbff
              refine entails_of_eval_mem fun α hα =>
                ⟨(ra ^^^ 1#32).toNat, List.mem_cons_self .., ?_⟩
              rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg, litEquiv_eval hα hrab_eqv]
              rw [entails_neg_eval_false hb_ent hα]; rfl
            fc_let; exact hJt (ra ^^^ 1#32, ()) m2 ⟨rfl, hnra_lt, hnra_ent⟩
      · fc_steps; exact hj_keep

theorem m3_cong_and_match_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, m3CongAndMatchSpec a m Q X → Func.wp Γ full_cong_and_match_body a m Q X := by
  rintro ⟨h, ent, ua, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, scr0, g_len, R, rfl, hlen, hw, hcl0, hrepr0, hg_cap, hpref,
     hgat, htag0, hua_cv, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hrl0 := hlen.core_ok.repr_len
  have htmpl0 := hlen.core_ok.tmp_len_arr
  have hscrl0 := hlen.scratch_ok.scratch_buf_len
  obtain ⟨lhs_ent, mword, he0, he1, _, hbd_e, _, _, hrhs_e, hsem_e⟩ := hgat
  have htag0' : (mword >>> 28).toNat = 0 := by
    rw [he1, Option.getD_some] at htag0; simpa using congrArg BitVec.toNat htag0
  obtain ⟨_, ha2_e, hand_e⟩ | ⟨ht_ne, _⟩ | ⟨ht_ne, _⟩ := hsem_e <;> (try omega)
  let ea := mword &&& 0xFF#32
  have hea_eq : ea.toNat = (mword &&& 0xFF#32).toNat := rfl
  let rhs := ((scr0.drop (ent.toNat + 2)).take ea.toNat).map BitVec.toNat
  have hrl_rhs : rhs.length = ea.toNat := by
    simp only [rhs, List.length_map, List.length_take, List.length_drop]
    rcases Nat.eq_zero_or_pos ea.toNat with hz | hpos
    · exact Nat.min_eq_left (by omega)
    · obtain ⟨_, hr, _⟩ := hrhs_e (ea.toNat - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp hr).1; omega
  have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
    rw [BitVec.toNat_add, bv_zext32_toNat]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1]; exact Nat.mod_eq_of_lt (by omega)
  have he1_arr : (ent.setWidth 64 + 1).toNat < s.scratch.scratch_buf.length := by omega
  have hst_e1 : s.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr = mword := by
    have h := (hpref (ent.toNat + 1) (by omega)).trans he1
    rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h; exact Option.some.inj h
  fc_split_fast
  · fc_steps; exact hQ false s.core.repr m0 hrl0 hrepr0 (fun h => by cases h) hm0
  · have h2_le_ua : 2 ≤ ua.toNat := by
      have h2_val : ((2 : BitVec 32).toNat) = 2 := rfl
      simp only [BitVec.ult, h2_val, decide_eq_false_iff_not] at hc; omega
    fc_split_fast
    · fc_steps; exact hQ false s.core.repr m0 hrl0 hrepr0 (fun h => by cases h) hm0
    · have hua_le_8 : ua.toNat ≤ 8 := by
        have h8_val : ((8 : BitVec 32).toNat) = 8 := rfl
        simp only [BitVec.ult, h8_val, decide_eq_false_iff_not] at hc; omega
      fc_steps
      refine wp_loop_inv
        (fun (mask, j, ()) mj => ∃ reprj : List (BitVec 32),
          reprj.length = 2 * c.max_vars ∧ j.toNat ≤ ea.toNat ∧
          FullCongReprInv F_cur (2 * s.core.cur_vars) reprj ∧
          (∀ p (hp : p < j.toNat), ∃ er < 2 * s.core.cur_vars,
            LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) er ∧
            (s.core.vals[er]?.getD 0#8 = 1#8 ∨
              ∃ k < ua.toNat, er = (s.core.tmp[k]?.getD 0#32).toNat)) ∧
          (∀ b < 32, mask.toNat.testBit b = true → b < ua.toNat ∧
            ∃ p < j.toNat, LitEquiv (cnfOfClauses F_cur)
              (rhs[p]?.getD 0) (s.core.tmp[b]?.getD 0#32).toNat) ∧
          (FullMem c { s with core := { s.core with repr := reprj } } ⋆ R) mj)
        (fun (_, j, ()) _ => ea.toNat - j.toNat)
        (fun J hJ => by
          fc_let
          exact hJ (0#32, 0#32, ()) m0 ⟨s.core.repr, hrl0, Nat.zero_le _, hrepr0,
            fun _ h => absurd h (by simp), fun _ _ h => by simp at h, hm0⟩)
        (fun J (mask, j, ()) mj ⟨reprj, hrlj, hj_le, hreprj, hfwdj, hbwdj, hmj⟩ ihj => ?_)
      let stj : FullState := { s with core := { s.core with repr := reprj } }
      have hlenj : stj.LengthsOk c := ⟨{ hlen.core_ok with repr_len := hrlj }, hlen.scratch_ok⟩
      have hwj : FullWitnessInv c F0 F_cur stj.core := fullWitnessInv_with_repr hw reprj
      fc_split_fast
      · have hj_lt : j.toNat < ea.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; rw [hst_e1] at hc; exact hc
        obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_e j.toNat hj_lt
        have hrhs_j : rhs[j.toNat]?.getD 0 = rv.toNat := by
          simp only [rhs, List.getElem?_map, List.getElem?_take,
            ite_eq_left (by omega : j.toNat < ea.toNat), List.getElem?_drop, hrv_get]
          rfl
        have he2j_n : (ent.setWidth 64 + 2 + j.setWidth 64).toNat = ent.toNat + 2 + j.toNat :=
          bv64_add_zext32 (k := 2) (by rw [bv_zext32_toNat]; omega)
        have he2j_arr : (ent.setWidth 64 + 2 + j.setWidth 64).toNat <
            stj.scratch.scratch_buf.length := by
          rw [he2j_n]; dsimp [stj]; omega
        have hst_e2j : stj.scratch.scratch_buf[(ent.setWidth 64 + 2 + j.setWidth 64).toNat]'
            he2j_arr = rv := by
          have h := (hpref (ent.toNat + 2 + j.toNat) (by omega)).trans hrv_get
          rw [← he2j_n, List.getElem?_eq_getElem he2j_arr] at h; exact Option.some.inj h
        have hj1_n : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
        fc_steps; c0_call hFind
        refine ⟨F_cur, 2 * s.core.cur_vars, reprj, FullReprRest c stj ⋆ R, hreprj,
          by rw [hst_e2j]; exact hrv_lt, focus_full_repr hmj,
          fun er repr_e me hrl_e hrepr_e _ her_lt her_eqv hme => ?_⟩
        let ste : FullState := { stj with core := { stj.core with repr := repr_e } }
        have hme' : (FullMem c ste ⋆ R) me := unfocus_full_repr hme; clear hme
        have hw_e : FullWitnessInv c F0 F_cur ste.core := fullWitnessInv_with_repr hwj repr_e
        have her_vals : (er.setWidth 64).toNat < ste.core.vals.length := by
          rw [bv_zext32_toNat]; dsimp [ste, stj]; rw [hlen.core_ok.vals_len]; omega
        have her_vals' : er.toNat < ste.core.vals.length := by
          rw [bv_zext32_toNat] at her_vals; exact her_vals
        have hrv_er_eqv : LitEquiv (cnfOfClauses F_cur) (rhs[j.toNat]?.getD 0) er.toNat := by
          rw [hrhs_j]; rwa [hst_e2j] at her_eqv
        have hev_dom : ste.core.vals[er.toNat]'her_vals' = 0#8 ∨
            ste.core.vals[er.toNat]'her_vals' = 1#8 ∨
            ste.core.vals[er.toNat]'her_vals' = 0xFF#8 := by
          have hd := hw_e.vals_domain er.toNat her_lt
          rwa [List.getElem?_eq_getElem her_vals', Option.getD_some] at hd
        fc_split_fast
        · -- ev < 0 -> return false
          fc_steps
          exact hQ false repr_e me (by omega) hrepr_e (fun h => by cases h) hme'
        · have hev_nslt : ¬ (ste.core.vals[er.toNat]'her_vals').slt 0#8 = true :=
            bv8_not_slt0_of_signExtend32_nslt0 hev_dom (by
              rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc; exact hc)
          fc_split_fast
          · -- ev == 0 -> scan tmp[0 ..< ua)
            have hev_eq0 : s.core.vals[er.toNat]?.getD 0#8 = 0#8 := by
              have hv0 : ste.core.vals[er.toNat]'her_vals' = 0#8 :=
                bv8_eq0_of_signExtend32 hev_dom (by
                  have hc' := beq_iff_eq.mp hc
                  rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc'; exact hc')
              rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.vals_len]; omega),
                Option.getD_some]
              exact hv0
            fc_to_group
            refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32])
              (fun (mask_b, found, _, ()) mb => mb = me ∧
                (found = true → ∃ k < ua.toNat, er = (s.core.tmp[k]?.getD 0#32) ∧
                  ∀ b < 32, mask_b.toNat.testBit b = true → b < ua.toNat ∧
                    (b = k ∨ ∃ p < j.toNat, LitEquiv (cnfOfClauses F_cur)
                      (rhs[p]?.getD 0) (s.core.tmp[b]?.getD 0#32).toNat)))
              (fun rem (k, ()) mk => mk = me ∧ k.toNat ≤ ua.toNat ∧ rem = ua.toNat - k.toNat)
              ?_ ?_ ?_
            · rintro _ ⟨mask_b, found, _, ⟨⟩⟩ mb ⟨hmb_eq, hfb⟩
              subst mb
              fc_split_fast
              · obtain ⟨k, hk_lt, htmp_k, hmask_b⟩ := hfb hc
                fc_steps
                refine ihj (mask_b, j + 1#32, ()) me (by dsimp only; omega)
                  ⟨repr_e, by omega, by omega, hrepr_e, ?_, ?_, hme'⟩
                · intro p hp
                  rw [hj1_n] at hp
                  by_cases hpj : p = j.toNat
                  · subst hpj
                    refine ⟨er.toNat, her_lt, hrv_er_eqv, Or.inr ⟨k, hk_lt, ?_⟩⟩
                    rw [htmp_k]
                  · exact hfwdj p (by omega)
                · intro b hb htb
                  obtain ⟨hb_ua, hbk | ⟨p, hp, heq⟩⟩ := hmask_b b hb htb
                  · refine ⟨hb_ua, j.toNat, by omega, ?_⟩
                    subst hbk; rwa [← htmp_k]
                  · exact ⟨hb_ua, p, by omega, heq⟩
              · fc_steps; exact hQ false repr_e me (by omega) hrepr_e (fun h => by cases h) hme'
            · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hmk_eq, hk_le, rfl⟩
              subst mk
              fc_split_fast
              · have hk_lt : k.toNat < ua.toNat := by
                  simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                have hk_tmp : (k.setWidth 64).toNat < ste.core.tmp.length := by
                  rw [bv_zext32_toNat]; dsimp [ste, stj]; omega
                have hk_tmp' : k.toNat < ste.core.tmp.length := by
                  rw [bv_zext32_toNat] at hk_tmp; exact hk_tmp
                have hk1_n : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                fc_split_fast
                · have htmp_eq : s.core.tmp[k.toNat]?.getD 0#32 = er := by
                    have h1 : ste.core.tmp[k.toNat]'hk_tmp' = er := by
                      have hc' := beq_iff_eq.mp hc
                      rw [list_getElem_congr (bv_zext32_toNat k) hk_tmp hk_tmp'] at hc'
                      exact hc'
                    change s.core.tmp[k.toNat]'_ = er at h1
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact h1
                  have hk_8 : k.toNat < 8 := by omega
                  fc_steps
                  have hkm : ((1 : BitVec 32) <<< (k.toNat % 32)) = 1#32 <<< k := by
                    rw [Nat.mod_eq_of_lt (by omega)]; rfl
                  rw [hkm]
                  refine hBk (mask ||| (1#32 <<< k), true, k, ()) me ⟨rfl, fun _ =>
                    ⟨k.toNat, hk_lt, htmp_eq.symm, fun b hb htb => ?_⟩⟩
                  rw [testBit_or_shl_eq hk_8 hb, Bool.or_eq_true, decide_eq_true_eq] at htb
                  rcases htb with htb | rfl
                  · obtain ⟨hb_ua, p, hp, heq⟩ := hbwdj b hb htb
                    exact ⟨hb_ua, Or.inr ⟨p, hp, heq⟩⟩
                  · exact ⟨hk_lt, Or.inl rfl⟩
                · fc_steps
                  exact hLk (ua.toNat - (k + 1#32).toNat) (k + 1#32, ()) me (by omega)
                    ⟨rfl, by omega, rfl⟩
              · fc_steps; exact hBk (mask, false, k, ()) me ⟨rfl, fun h => by cases h⟩
            · intro _ Lk _ hLk; fc_let; exact hLk ua.toNat (0#32, ()) me ⟨rfl, Nat.zero_le _, rfl⟩
          · -- ev > 0 -> guaranteed true, continue loop
            have hev_eq1 : s.core.vals[er.toNat]?.getD 0#8 = 1#8 := by
              have hne0 : (ste.core.vals[er.toNat]'her_vals').signExtend 32 ≠ 0#32 := by
                have hc' := beq_eq_false_iff_ne.mp hc
                rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc'; exact hc'
              have h1 := bv8_eq1_of_signExtend32_ne0_nslt0 hev_dom hne0 hev_nslt
              rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.vals_len]; omega),
                Option.getD_some]
              exact h1
            fc_steps
            refine ihj (mask, j + 1#32, ()) me (by dsimp only; omega)
              ⟨repr_e, by omega, by omega, hrepr_e, ?_, ?_, hme'⟩
            · intro p hp
              rw [hj1_n] at hp
              by_cases hpj : p = j.toNat
              · subst hpj; exact ⟨er.toNat, her_lt, hrv_er_eqv, Or.inl hev_eq1⟩
              · exact hfwdj p (by omega)
            · intro b hb htb
              obtain ⟨hb_ua, p, hp, heq⟩ := hbwdj b hb htb
              exact ⟨hb_ua, p, by omega, heq⟩
      · have hj_eq : j.toNat = ea.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not] at hc; rw [hst_e1] at hc
          change ¬ j.toNat < ea.toNat at hc; omega
        rw [hj_eq] at hfwdj hbwdj
        fc_steps
        have hm_mod : ((1 : BitVec 32) <<< (ua.toNat % 32)) = 1#32 <<< ua := by
          rw [Nat.mod_eq_of_lt (by omega)]; rfl
        rw [hm_mod]
        refine hQ (mask == (1#32 <<< ua) - 1#32) reprj mj hrlj hreprj ?_ hmj
        intro htrue
        have hm_eq : mask = (1#32 <<< ua) - 1#32 := beq_iff_eq.mp htrue
        refine ⟨h2_le_ua, hua_le_8, ?_⟩
        rw [he0, Option.getD_some]
        refine andMatch_sound_equiv hwj hcl0 hand_e ?_ ?_
        · intro p hp
          have hp' : p < ea.toNat := by rw [← hrl_rhs]; exact hp
          have h1 := hfwdj p hp'
          dsimp only [rhs] at h1
          rw [List.getElem?_eq_getElem hp, Option.getD_some] at h1
          exact h1
        · intro k hk
          have htb : mask.toNat.testBit k = true := by
            rw [hm_eq]; exact testBit_full_mask_iff h2_le_ua hua_le_8 hk
          have ⟨_, p, hp, heq⟩ := hbwdj k (by omega) htb
          rw [← hrl_rhs] at hp
          exact ⟨p, hp, heq⟩

end HelperProofs

end LeanQbe.T.Examples.Kissat.FullM3CongBva