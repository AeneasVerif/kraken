module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
import LeanQbe.T.Examples.Kissat.LayerAFull1
import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat `D-Full` SAT-Sweeping Top Shard — Part 1 (`Stage 4`)

Defines local `FullSweepVarSpecs` (matching `FullSpec1`/`FullSpec2`/`FullSpec3` 1:1, with the
`#1039` `nv ≤ s.core.cur_vars` / `nv.toNat ≤ 2 * c.max_vars` cone-bound fix), strictly scoped
`FullSweepVarTactics`, invariant/BitVec/semantic sweeping helpers, and the parametric `(Γ : Env)`
`Func.wp` proof for:
1. `full_sweep_seed_sim` (`full_sweep_seed_sim_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Stage-4 invariants and shard `Spec` contracts (`FullSweepVarSpecs`) -/

namespace FullSweepVarSpecs

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

@[expose] def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

@[expose] def FullDenseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

@[expose] def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

@[expose] def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

@[expose]
def FullSparseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

@[expose]
def FullDenseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

theorem FullSparseInvW.toSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullSparseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInv.exists_witness {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : ∃ F_cur, FullSparseInvW c F0 F_cur s :=
  let ⟨F_cur, hw⟩ := h.1.witness
  ⟨F_cur, h.1.lengths, hw, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem FullDenseInvW.toDense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : FullDenseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem FullDenseInv.exists_witness {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : ∃ F_cur, FullDenseInvW c F0 F_cur s :=
  let ⟨F_cur, hw⟩ := h.1.witness
  ⟨F_cur, h.1.lengths, hw, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInv.lengths {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : s.LengthsOk c := h.1.lengths

theorem FullDenseInv.lengths {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : s.LengthsOk c := h.1.lengths

theorem FullSparseInv.inconsistent_unsat {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat :=
  h.1.inconsistent_unsat hinc

theorem FullDenseInv.inconsistent_unsat {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat :=
  h.1.inconsistent_unsat hinc

theorem FullExtScratchOk.of_pres {c : FullCfg} {s s' : FullState}
    (h : FullExtScratchOk c s) (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') : FullExtScratchOk c s' := by
  refine ⟨fun i hi => ?_, hpres.2 ▸ h.2⟩
  dsimp only; rw [hpres.1]
  exact (h.1 i hi).elim Or.inl fun hr => Or.inr (hsub _ hr)

theorem FullCoreInv.with_fuel_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullCoreInv c F0 s) (hlen' : s'.LengthsOk c) {fuel' : BitVec 64}
    (hcore : s'.core = { s.core with fuel := fuel' }) : FullCoreInv c F0 s' := by
  obtain ⟨F_cur, hw⟩ := h.witness
  refine ⟨hlen', F_cur, ?_⟩
  rw [hcore]
  exact { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

@[expose] def FullConflictOkW (F_cur : List (List Nat)) (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat])) ∨
  (s.core.confl_type ≠ 1#64 ∧
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)

theorem level0_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (_hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2 (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_))
    right
    have hlt := hw.arena.lits_lt _ href hng l hl
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
    rwa [heq] at hs

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

@[expose] def fullRngNextSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

@[expose] def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

@[expose] def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
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
      cl' = min s.core.cur_level target_lvl.toNat → FullProbeScratchPres s s' →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
      FullProbeScratchPres s s' → s.core.trail_end ≤ te' → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
      (∀ i < s.core.trail_end, trl'[i]? = s.core.trl[i]?) →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullAddBinSpec : Spec [i64, i32, i32] [i64] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    (a.toNat < 2 * s.core.cur_vars → b.toNat < 2 * s.core.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                oom := oom', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', wsort := wsort' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat ∧ inc' ≠ 0#64) →
      (r = 2#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullAddUnitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    (lit.toNat < 2 * s.core.cur_vars → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', cur_level := cl', unassigned := unass',
                                unflushed := unfl', inconsistent := inc' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullProbeScratchPres s s' → cl' = 0 →
      (lit.toNat < 2 * s.core.cur_vars → ok = false → F0.Unsat ∧ inc' ≠ 0#64) →
      (ok = false → 2 * s.core.cur_vars ≤ lit.toNat ∨ (F0.Unsat ∧ inc' ≠ 0#64)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullEnterDenseSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel →
      (ok = true → FullDenseInv c F0 s') →
      (ok = false → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullRebuildWatchesSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullSweepGlobalLit (s : FullState) (ll : Nat) : Nat :=
  2 * (s.scratch.work_stk1[ll / 2]?.getD 0#32).toNat + (ll % 2)

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

@[expose]
def FullSweepDpllUnsat (F_cur : List (List Nat)) (s : FullState) (nv a0 a1 : Nat) : Prop :=
  let ass := (if a0 < 2 * nv then [fullSweepGlobalLit s a0 ^^^ 1] else []) ++
             (if a1 < 2 * nv then [fullSweepGlobalLit s a1 ^^^ 1] else [])
  (cnfOfClauses F_cur).EntailsClause (cnfClause ass)

@[expose] def fullSweepConeSpec : Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1152 ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧
    (∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0xFFFFFFFF#32) ∧
    (FullMem c s ⋆ R) m ∧
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

@[expose] def fullSweepSeedSimSpec : Spec [i64, i32, i32] [i32] := fun (h, nv, nc, ()) m Q _ =>
  ∃ (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 1152 ≤ c.scratch_cap ∧ 1 ≤ nv.toNat ∧
    FullSweepConeOk F_cur s nv.toNat nc.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ r fuel' scr' rng' sig' m',
      let s' : FullState :=
        { s with
          core := { s.core with fuel := fuel' }
          scratch := { s.scratch with scratch_buf := scr', rng_state := rng', sim_sig := sig' } }
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < 1024, scr'[i]? = s.scratch.scratch_buf[i]?) →
      FullSweepConeOk F_cur s' nv.toNat nc.toNat →
      (r = 0xFFFFFFFF#32 → (cnfOfClauses F_cur).Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullSweepVarSpec : Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1152 ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧
    (∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0xFFFFFFFF#32) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ v < s'.core.cur_vars, s'.scratch.tarjan_mark[v]?.getD 0#32 = 0xFFFFFFFF#32) →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullSweepSatSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

abbrev EnvSpec (Γ : Env) (name : Sym) {as rs : List Ty} (S : Spec as rs) : Prop :=
  ∀ xs m Q X, S xs m Q X → Γ name as rs xs m Q X

end FullSweepVarSpecs

open FullSweepVarSpecs

/-! ## 2. Strictly scoped tactics (`FullSweepVarTactics`) -/

namespace FullSweepVarTactics

open Lean Elab Tactic in
scoped elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty ← Lean.instantiateMVars (← g.getType)
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "fsv_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)

open Lean Elab Tactic in
scoped elab "fsv_unmdata" : tactic => do
  let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
  if ty.isMData then
    evalTactic (← `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _))

open Lean Elab Tactic in
scoped elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let ty0 ← Lean.instantiateMVars (← (← getMainGoal).getType)
    if ty0.isMData then
      try evalTactic (← `(tactic| focus fsv_unmdata)) catch _ => pure ()
    if ty0.consumeMData.isAppOf ``And then
      try evalTactic (← `(tactic| focus repeat fsv_strip)) catch _ => pure ()
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      evalTactic (← `(tactic| focus (
        refine LeanQbe.T.wp_jnz_of (fun hc => ?_) (fun hc => ?_)
        all_goals
          (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm] at hc)
          c0_cond hc
          try c0_let_simp)))
      return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100
open Lean Elab Tactic in
private meta def fsvStepOnce : TacticM Bool := do
  let g ← getMainGoal
  let ty0 ← Lean.instantiateMVars (← g.getType)
  if ty0.isMData then
    try evalTactic (← `(tactic| focus fsv_unmdata)) catch _ => pure ()
  let ty1 ← Lean.instantiateMVars (← (← getMainGoal).getType)
  if ty1.consumeMData.isAppOf ``And then
    try evalTactic (← `(tactic| focus repeat fsv_strip)) catch _ => pure ()
  let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
      ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
    let hc := mkIdent `hc
    evalTactic (← `(tactic| focus (
      refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)
      all_goals
        (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm] at $hc:ident)
        c0_cond $hc
        try (exfalso; first | decide | omega | bv_omega)
        try c0_let_simp)))
    return true
  try LeanQbe.T.C0Step.stepOnce catch _ => return false

open Lean Elab Tactic in
private meta partial def fsvStepsGo (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    if ← fsvStepOnce then
      fsvStepsGo (fuel - 1)
      out := out ++ (← getUnsolvedGoals)
    else
      out := out.push g
  setGoals out.toList

open Lean Elab Tactic in
scoped elab "fsv_steps" : tactic => fsvStepsGo 500
scoped macro "fsv_group" : tactic =>
  `(tactic| (
      (try fsv_unmdata)
      (repeat fsv_strip)
      c0_to_group
      repeat (any_goals (fsv_strip; repeat fsv_strip); c0_to_group)))

open Lean Elab Tactic Meta in
scoped elab "fsv_unwind_j" : tactic => do
  for _ in List.range 8 do
    let g ← getMainGoal
    let matchedDecl? ← g.withContext do
      let tgt ← Lean.instantiateMVars (← g.getType)
      let fn := tgt.consumeMData.getAppFn
      if !fn.isFVar then return none
      let lctx ← getLCtx
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let ty ← Lean.instantiateMVars decl.type
        let matched ← forallTelescopeReducing ty fun xs body => do
          if xs.size == 3 && body.consumeMData.getAppFn == fn then
            let dom ← Lean.instantiateMVars (← inferType xs[2]!)
            return dom.consumeMData.isAppOf ``LeanQbe.T.wp
          else
            return false
        if matched then return some decl.fvarId
      return none
    match matchedDecl? with
    | some fid =>
      let gs ← g.apply (mkFVar fid)
      setGoals gs
      evalTactic (← `(tactic| focus fsv_steps))
    | none => break

end FullSweepVarTactics

/-! ## 3. Shared preservation & BitVec helpers -/

namespace FullSweepVarHelpers

theorem fullSweepConeOk_with_scratch {F_cur : List (List Nat)} {s s' : FullState} {nv nc : Nat}
    (h : FullSweepConeOk F_cur s nv nc)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hws : s'.scratch.work_stk1 = s.scratch.work_stk1)
    (hrsz : s'.scratch.res_sz = s.scratch.res_sz)
    (hscr : ∀ i < 1024, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) :
    FullSweepConeOk F_cur s' nv nc := by
  obtain ⟨h24, hcv_le, h64, h128, h1024, hws1, hcl⟩ := h
  refine ⟨h24, hcv ▸ hcv_le, h64, hrsz ▸ h128, hrsz ▸ h1024, fun i hi => ?_, fun ci hci => ?_⟩
  · rw [hws, hcv]; exact hws1 i hi
  · obtain ⟨h128c, hbd, hlt, hent⟩ := hcl ci hci
    have hci64 : ci < 1024 := by omega
    have h64c : 64 + ci < 1024 := by omega
    have hoff : s'.scratch.scratch_buf[ci]? = s.scratch.scratch_buf[ci]? := hscr ci hci64
    have hsz : s'.scratch.scratch_buf[64 + ci]? = s.scratch.scratch_buf[64 + ci]? :=
      hscr (64 + ci) h64c
    dsimp only at h128c hbd hlt hent ⊢
    rw [hoff, hsz, hrsz]
    refine ⟨h128c, hbd, fun k hk => ?_, ?_⟩
    · rw [hscr ( _ + k) (by omega)]; exact hlt k hk
    · have hmap :
          ((List.range (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat).map fun k =>
            fullSweepGlobalLit s'
              (s'.scratch.scratch_buf[(s.scratch.scratch_buf[ci]?.getD 0#32).toNat + k]?.getD
                0#32).toNat) =
          ((List.range (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat).map fun k =>
            fullSweepGlobalLit s
              (s.scratch.scratch_buf[(s.scratch.scratch_buf[ci]?.getD 0#32).toNat + k]?.getD
                0#32).toNat) := by
        apply List.map_congr_left
        intro k hk
        have hkl : k < (s.scratch.scratch_buf[64 + ci]?.getD 0#32).toNat := List.mem_range.mp hk
        rw [hscr _ (by omega)]
        unfold fullSweepGlobalLit; rw [hws]
      rw [hmap]; exact hent

theorem fullDenseInvW_with_fuel_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {fuel' : BitVec 64} {sc' : FullScratch}
    (hsok : sc'.LengthsOk c) (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with fuel := fuel' }, scratch := sc' } := by
  let s' : FullState := { core := { s.core with fuel := fuel' }, scratch := sc' }
  refine ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, hsok⟩, ?_, h.2.2.1, h.2.2.2.1,
    ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · exact { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  · refine ⟨fun i hi => ?_, by dsimp only [s']; rw [hext]; exact h.2.2.2.2.1.2⟩
    dsimp only [s']; rw [hll]; exact h.2.2.2.2.1.1 i hi

theorem fullDenseInvW_with_inconsistent {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
   { h.2.1 with
     inconsistent_sound := fun _ => hu
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_tmk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {tmk' : List (BitVec 32)}
    (htl : tmk'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with tarjan_mark := tmk' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with tarjan_mark_len := htl }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_sweep_cnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (cnt' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with sweep_cnt := cnt' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with tarjan_mark_len := h.1.scratch_ok.tarjan_mark_len }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInv_with_tmk {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {tmk' : List (BitVec 32)} (htl : tmk'.length = 2 * c.max_vars) :
    FullDenseInv c F0 { s with scratch := { s.scratch with tarjan_mark := tmk' } } :=
  let ⟨_, hw⟩ := h.exists_witness
  (fullDenseInvW_with_tmk hw htl).toDense

theorem fullDenseInv_with_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hw⟩ := h.exists_witness
  refine FullDenseInvW.toDense ⟨⟨{ hw.1.core_ok with flags_len := hfl }, hw.1.scratch_ok⟩,
    { hw.2.1 with
      arena := { hw.2.1.arena with len_ok := hw.2.1.arena.len_ok }
      watches := hw.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩

theorem fullSweepDpllUnsat_nil {F_cur : List (List Nat)} {s : FullState} {nv : Nat}
    (hnv : nv ≤ 24) (hu : FullSweepDpllUnsat F_cur s nv 0xFFFFFFFF 0xFFFFFFFF) :
    (cnfOfClauses F_cur).Unsat := by
  unfold FullSweepDpllUnsat at hu
  have hnot : ¬ (0xFFFFFFFF < 2 * nv) := by omega
  simp only [hnot, ↓reduceIte, List.append_nil] at hu
  exact unsat_of_entails_nil hu

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

theorem bv64_to32_toNat (x : BitVec 64) (hx : x.toNat < 2 ^ 32) :
    (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

theorem bv32_xor1_toNat (x : BitVec 32) :
    (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  rw [BitVec.toNat_xor]; rfl

theorem bv32_1_sub_toNat (test : BitVec 32) (ht : test = 0#32 ∨ test = 1#32) :
    (1#32 - test).toNat = 1 - test.toNat := by
  rcases ht with rfl | rfl <;> decide

theorem bv32_shl1_toNat (v : BitVec 32) (hv : v.toNat < 2 ^ 31) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  have h := bv32_shl1_or_pol v 0#32 hv (by decide)
  simpa using h

theorem nat_2x_xor1 (x : Nat) : (2 * x) ^^^ 1 = 2 * x + 1 ∧ (2 * x + 1) ^^^ 1 = 2 * x := by
  constructor <;> apply Nat.eq_of_testBit_eq <;> intro i <;> cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit, Bool.xor_false,
      show (2 * x + 1) / 2 = x by omega, show (2 * x) / 2 = x by omega]

theorem tmk_clear_step {cv nv i : Nat} {tmk ws1 : List (BitVec 32)} {v : BitVec 32}
    (hi : i < nv) (hws : ws1[i]?.getD 0#32 = v) (hv_len : v.toNat < tmk.length)
    (ht : ∀ u < cv, tmk[u]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
      ∃ k, i ≤ k ∧ k < nv ∧ (ws1[k]?.getD 0#32).toNat = u) :
    ∀ u < cv, (tmk.set v.toNat 0xFFFFFFFF#32)[u]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
      ∃ k, i + 1 ≤ k ∧ k < nv ∧ (ws1[k]?.getD 0#32).toNat = u := by
  intro u hu hne
  by_cases huv : u = v.toNat
  · subst huv; rw [List.getElem?_set_self hv_len] at hne; exact absurd rfl hne
  · rw [List.getElem?_set_ne (Ne.symm huv)] at hne
    obtain ⟨k, hk1, hk2, hwk⟩ := ht u hu hne
    have hkne : k ≠ i := by rintro rfl; rw [hws] at hwk; exact huv hwk.symm
    exact ⟨k, by omega, hk2, hwk⟩

theorem tmk_clear_step64 {cv nv : Nat} {i : BitVec 32} {tmk ws1 ws_cur : List (BitVec 32)}
    (hi : i.toNat < nv) (hi1 : (i + 1#32).toNat = i.toNat + 1)
    (hws_eq : ws_cur = ws1) (hws_len : i.toNat < ws1.length)
    (hv_len : (ws1[i.toNat]'hws_len).toNat < tmk.length)
    (ht : ∀ u < cv, tmk[u]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
      ∃ k, i.toNat ≤ k ∧ k < nv ∧ (ws1[k]?.getD 0#32).toNat = u) :
    ∀ u < cv,
      (tmk.set (BitVec.setWidth 64 (ws_cur[(BitVec.setWidth 64 i).toNat]'(by
        have := BitVec.isLt i
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hws_eq]; exact hws_len))).toNat
        0xFFFFFFFF#32)[u]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
      ∃ k, (i + 1#32).toNat ≤ k ∧ k < nv ∧ (ws1[k]?.getD 0#32).toNat = u := by
  intro u hu hne
  have hi64 : (BitVec.setWidth 64 i).toNat = i.toNat := by
    have := BitVec.isLt i; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hcur_eq : ws_cur[(BitVec.setWidth 64 i).toNat]'(by
      rw [hi64, hws_eq]; exact hws_len) = ws1[i.toNat]'hws_len := by
    subst hws_eq; simp only [hi64]
  have hv64 : (BitVec.setWidth 64 (ws_cur[(BitVec.setWidth 64 i).toNat]'(by
      rw [hi64, hws_eq]; exact hws_len))).toNat = (ws1[i.toNat]'hws_len).toNat := by
    rw [hcur_eq, BitVec.toNat_setWidth]
    have := BitVec.isLt (ws1[i.toNat]'hws_len)
    exact Nat.mod_eq_of_lt (by omega)
  simp only [hv64] at hne
  obtain ⟨k, hk1, hk2, hwk⟩ :=
    tmk_clear_step hi (List.getElem?_eq_getElem hws_len ▸ rfl) hv_len ht u hu hne
  exact ⟨k, hi1 ▸ hk1, hk2, hwk⟩

theorem tmk_idx_lt {α : Type} {i : BitVec 32} {ws1 ws_cur : List (BitVec 32)} {tmk_c : List α}
    (hws_eq : ws_cur = ws1) (hws_len : i.toNat < ws1.length)
    (hv_lt : (ws1[i.toNat]'hws_len).toNat < tmk_c.length)
    (hi64 : (BitVec.setWidth 64 i).toNat < ws_cur.length) :
    (BitVec.setWidth 64 (ws_cur[(BitVec.setWidth 64 i).toNat]'hi64)).toNat < tmk_c.length := by
  have h64 : (BitVec.setWidth 64 i).toNat = i.toNat := by
    have := BitVec.isLt i; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hcur : ws_cur[(BitVec.setWidth 64 i).toNat]'hi64 = ws1[i.toNat]'hws_len := by
    subst hws_eq
    exact Option.some.inj (by rw [← List.getElem?_eq_getElem hi64, h64, List.getElem?_eq_getElem])
  rw [hcur, BitVec.toNat_setWidth]
  have := BitVec.isLt (ws1[i.toNat]'hws_len)
  rw [Nat.mod_eq_of_lt (by omega)]
  exact hv_lt

theorem tmk_clear_done {cv nv i : Nat} {tmk ws1 : List (BitVec 32)}
    (hge : ¬ i < nv)
    (ht : ∀ u < cv, tmk[u]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
      ∃ k, i ≤ k ∧ k < nv ∧ (ws1[k]?.getD 0#32).toNat = u) :
    ∀ u < cv, tmk[u]?.getD 0#32 = 0xFFFFFFFF#32 := by
  intro u hu
  exact Classical.byContradiction fun hne => by
    obtain ⟨k, hk1, hk2, _⟩ := ht u hu hne
    omega

theorem fullSweepDpllUnsat_unit {F_cur : List (List Nat)} {s : FullState}
    {nv : Nat} {root_v test : BitVec 32}
    (hnv2 : 2 ≤ nv) (hnv24 : nv ≤ 24)
    (hroot : (s.scratch.work_stk1[0]?.getD 0#32).toNat = root_v.toNat)
    (htest : test = 0#32 ∨ test = 1#32) (hroot_lt : root_v.toNat < 2 ^ 31)
    (hu : FullSweepDpllUnsat F_cur s nv test.toNat 0xFFFFFFFF) :
    let lit := (root_v <<< (1 : Nat)) ||| (1#32 - test)
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) := by
  intro lit
  have ht2 : test.toNat < 2 * nv := by rcases htest with rfl | rfl <;> simp <;> omega
  have hnot : ¬ (0xFFFFFFFF < 2 * nv) := by omega
  unfold FullSweepDpllUnsat at hu
  simp only [ht2, hnot, ↓reduceIte, List.append_nil] at hu
  have h1sub : (1#32 - test).toNat < 2 := by rcases htest with rfl | rfl <;> decide
  have hlit_eq : lit.toNat = fullSweepGlobalLit s test.toNat ^^^ 1 := by
    rw [bv32_shl1_or_pol root_v (1#32 - test) hroot_lt h1sub, bv32_1_sub_toNat test htest]
    unfold fullSweepGlobalLit
    rcases htest with rfl | rfl
    · simp [hroot]; rw [← (nat_2x_xor1 root_v.toNat).1]
    · simp [hroot]; rw [(nat_2x_xor1 root_v.toNat).2]
  rw [hlit_eq]; exact hu

theorem fullSweepDpllUnsat_bin1 {F_cur : List (List Nat)} {s : FullState}
    {nv : Nat} {root_v ov j pol : BitVec 32}
    (hnv24 : nv ≤ 24) (hj_lt : j.toNat < nv)
    (hroot : (s.scratch.work_stk1[0]?.getD 0#32).toNat = root_v.toNat)
    (hov : (s.scratch.work_stk1[j.toNat]?.getD 0#32).toNat = ov.toNat)
    (hpol : pol = 0#32 ∨ pol = 1#32)
    (hroot_lt : root_v.toNat < 2 ^ 31) (hov_lt : ov.toNat < 2 ^ 31)
    (hu : FullSweepDpllUnsat F_cur s nv 0 (((j <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat)) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [((root_v <<< (1 : Nat)) ^^^ 1#32).toNat,
        ((ov <<< (1 : Nat)) ||| pol).toNat]) := by
  have h0_lt : 0 < 2 * nv := by omega
  have hxp_lt : (1#32 ^^^ pol).toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have hp_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have ha1_eq : ((j <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat =
      2 * j.toNat + (1#32 ^^^ pol).toNat :=
    bv32_shl1_or_pol j (1#32 ^^^ pol) (by omega) hxp_lt
  have ha1_lt : ((j <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat < 2 * nv := by omega
  unfold FullSweepDpllUnsat at hu
  simp only [h0_lt, ha1_lt, ↓reduceIte, List.cons_append, List.nil_append] at hu
  have hl0 : ((root_v <<< (1 : Nat)) ^^^ 1#32).toNat = fullSweepGlobalLit s 0 ^^^ 1 := by
    rw [bv32_xor1_toNat, bv32_shl1_toNat root_v hroot_lt]
    unfold fullSweepGlobalLit; simp [hroot]
  have hl1 : ((ov <<< (1 : Nat)) ||| pol).toNat =
      fullSweepGlobalLit s ((j <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat ^^^ 1 := by
    rw [bv32_shl1_or_pol ov pol hov_lt hp_lt]
    unfold fullSweepGlobalLit; rw [ha1_eq]
    rcases hpol with rfl | rfl
    · have hxp : (1#32 ^^^ 0#32).toNat = 1 := rfl
      rw [hxp]
      simp [show (2 * j.toNat + 1) / 2 = j.toNat by omega,
        show (2 * j.toNat + 1) % 2 = 1 by omega, hov, (nat_2x_xor1 ov.toNat).2]
    · have hxp : (1#32 ^^^ 1#32).toNat = 0 := rfl
      rw [hxp]
      simp [hov, (nat_2x_xor1 ov.toNat).1]
  rw [hl0, hl1]; exact hu

theorem fullSweepDpllUnsat_bin2 {F_cur : List (List Nat)} {s : FullState}
    {nv : Nat} {root_v ov j pol : BitVec 32}
    (hnv24 : nv ≤ 24) (hj_lt : j.toNat < nv)
    (hroot : (s.scratch.work_stk1[0]?.getD 0#32).toNat = root_v.toNat)
    (hov : (s.scratch.work_stk1[j.toNat]?.getD 0#32).toNat = ov.toNat)
    (hpol : pol = 0#32 ∨ pol = 1#32)
    (hroot_lt : root_v.toNat < 2 ^ 31) (hov_lt : ov.toNat < 2 ^ 31)
    (hu : FullSweepDpllUnsat F_cur s nv 1 (((j <<< (1 : Nat)) ||| pol).toNat)) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(root_v <<< (1 : Nat)).toNat,
        (((ov <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat]) := by
  have h1_lt : 1 < 2 * nv := by omega
  have hp_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have ha1_eq : ((j <<< (1 : Nat)) ||| pol).toNat = 2 * j.toNat + pol.toNat :=
    bv32_shl1_or_pol j pol (by omega) hp_lt
  have ha1_lt : ((j <<< (1 : Nat)) ||| pol).toNat < 2 * nv := by omega
  unfold FullSweepDpllUnsat at hu
  simp only [h1_lt, ha1_lt, ↓reduceIte, List.cons_append, List.nil_append] at hu
  have hl0 : (root_v <<< (1 : Nat)).toNat = fullSweepGlobalLit s 1 ^^^ 1 := by
    rw [bv32_shl1_toNat root_v hroot_lt]
    unfold fullSweepGlobalLit; simp [hroot, (nat_2x_xor1 root_v.toNat).2]
  have hl1 : (((ov <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat =
      fullSweepGlobalLit s ((j <<< (1 : Nat)) ||| pol).toNat ^^^ 1 := by
    rw [bv32_xor1_toNat, bv32_shl1_or_pol ov pol hov_lt hp_lt]
    unfold fullSweepGlobalLit; rw [ha1_eq]
    rcases hpol with rfl | rfl
    · have hp0 : (0#32).toNat = 0 := rfl
      rw [hp0]; simp [hov]
    · have hp1 : (1#32).toNat = 1 := rfl
      rw [hp1]
      simp [show (2 * j.toNat + 1) / 2 = j.toNat by omega,
        show (2 * j.toNat + 1) % 2 = 1 by omega, hov]
  rw [hl0, hl1]; exact hu

theorem fullDenseInvW_after_refine {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {sig' : List (BitVec 64)} (hsig : sig'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with sim_sig := sig' } } :=
  fullDenseInvW_with_fuel_scratch h { h.1.scratch_ok with sim_sig_len := hsig } rfl rfl

theorem fullDenseInvW_after_addUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl32' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' unfl' inc' : BitVec 64} {sc' : FullScratch}
    (s' : FullState)
    (hs'_def : s' =
      { s with
        core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns',
            trl := trl32', trail_pos := tp', trail_end := te', propagated := prop',
            cur_level := cl', unassigned := unass', unflushed := unfl', inconsistent := inc' }
        scratch := sc' })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hpres : FullProbeScratchPres s s') (hcl0 : cl' = 0) :
    FullDenseInvW c F0 F_cur s' := by
  subst hs'_def
  refine ⟨hlen', hw', ?_, ?_, ?_, hcl0, h.2.2.2.2.2.2⟩
  · exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    exact h.2.2.2.1
  · exact h.2.2.2.2.1.of_pres hpres.1 fun r hr => hr

theorem fullDenseInvW_after_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' wsort' : List (BitVec 32)}
    {te' wlen' : Nat} {unass' unfl' wu' nb' oom' inc' : BitVec 64} {phases' : List (BitVec 8)}
    (s' : FullState)
    (hs'_def : s' =
      { s with
        core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
            unflushed := unfl',
            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
            oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core) :
    FullDenseInvW c F0 F_cur s' := by
  subst hs'_def
  refine ⟨hlen', hw', h.2.2.1, ?_, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    exact h.2.2.2.1
  · exact h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun r hr => hr

theorem fullSparseInv_after_backtrack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (s' : FullState)
    (hs'_def : s' =
      { s with
        core :=
          { s.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
            unassigned := unass' }
        scratch := sc' })
    (hlen' : s'.LengthsOk c) (hpres : FullProbeScratchPres s s')
    (hw' : FullWitnessInv c F0 F_cur s'.core) :
    FullSparseInv c F0 s' := by
  subst hs'_def
  refine ⟨⟨hlen', F_cur, hw'⟩, h.2.2.1, ?_, ?_, h.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    exact h.2.2.2.1
  · exact h.2.2.2.2.1.of_pres hpres.1 fun r hr => hr

theorem fullSparseInv_after_propagate {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' wvec' arena' wstk' : List (BitVec 32)}
    {te' prop' wlen' : Nat}
    {unass' unfl' wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (s' : FullState)
    (hs'_def : s' =
      { s with
        core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
            unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
            wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hnd' : FullArenaVarsNodup s') (hpres : FullProbeScratchPres s s')
    (hsub : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') :
    FullSparseInv c F0 s' := by
  subst hs'_def
  exact ⟨⟨hlen', F_cur, hw'⟩, h.2.2.1, hnd', h.2.2.2.2.1.of_pres hpres.1 hsub, h.2.2.2.2.2⟩

end FullSweepVarHelpers

/-! ## 4. `full_sweep_seed_sim_wp` (`Full.lean` #15) -/

section SeedSim
open FullSweepVarHelpers
open scoped FullArenaTactics FullSweepVarTactics

theorem full_sweep_seed_sim_wp (Γ : Env)
    (hdpll : EnvSpec Γ "full_sweep_dpll" fullSweepDpllSpec)
    (hrefine : EnvSpec Γ "full_sweep_refine" fullSweepRefineSpec) :
    ∀ args m Q X, fullSweepSeedSimSpec args m Q X →
      Func.wp Γ full_sweep_seed_sim_body args m Q X := by
  rintro ⟨h, nv, nc, ⟨⟩⟩ m Q X ⟨c, F_cur, s, R, rfl, hlen, hcap, hnv_pos, hcone, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hnv_24 : nv.toNat ≤ 24 := hcone.1
  have hnv_cv : nv.toNat ≤ s.core.cur_vars := hcone.2.1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  fsv_group
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) ml => i.toNat ≤ nv.toNat ∧ ∃ sig1 : List (BitVec 64),
      sig1.length = c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig1 } } ⋆ R) ml)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun J hLoop => by
      fsv_steps
      exact hLoop (0#32, ()) m ⟨Nat.zero_le _, s.scratch.sim_sig, hlen.scratch_ok.sim_sig_len, hm⟩)
    (fun J (i, ()) ml ⟨hi_le, sig1, hsig1_len, hml⟩ hLoop => ?_)
  · c0_split
    · have hi_lt : i.toNat < nv.toNat := by c0_bound
      have hws_len := hlen.scratch_ok.work_stk1_len
      have hgv_lt : (s.scratch.work_stk1[i.toNat]'(by omega)).toNat < c.max_vars := by
        have h1 := hcone.2.2.2.2.2.1 i.toNat hi_lt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
        omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      fsv_steps
      refine hLoop (i + 1#32, ()) _ (by dsimp only; omega) ?_
      refine ⟨by omega, ?_, ?_, by assumption⟩
      simp [hsig1_len]
    · fsv_group
      let s0 : FullState := { s with scratch := { s.scratch with sim_sig := sig1 } }
      have hlen0 : s0.LengthsOk c :=
        ⟨hlen.core_ok, { hlen.scratch_ok with sim_sig_len := hsig1_len }⟩
      have hcone0 : FullSweepConeOk F_cur s0 nv.toNat nc.toNat :=
        fullSweepConeOk_with_scratch hcone rfl rfl rfl (fun _ _ => rfl)
      refine wp_loop_inv (ts := [i32, i32])
        (fun (rbit, s_idx, ()) m1 =>
          s_idx.toNat ≤ 8 ∧ rbit.toNat ≤ 64 ∧
          ∃ fuel1 scr1 rng1 sig_cur,
            let s1 : FullState :=
              { s with
                core := { s.core with fuel := fuel1 }
                scratch := { s.scratch with
                  scratch_buf := scr1, rng_state := rng1, sim_sig := sig_cur } }
            s1.LengthsOk c ∧ fuel1.toNat ≤ s.core.fuel.toNat ∧
            (∀ k < 1024, scr1[k]? = s.scratch.scratch_buf[k]?) ∧
            FullSweepConeOk F_cur s1 nv.toNat nc.toNat ∧
            (FullMem c s1 ⋆ R) m1)
        (fun (_, s_idx, ()) _ => 8 - s_idx.toNat)
        (fun J2 hLoop2 => by
          fsv_steps
          exact hLoop2 (0#32, 0#32, ()) ml
            ⟨by simp, by simp, s.core.fuel, s.scratch.scratch_buf, s.scratch.rng_state,
              sig1, hlen0, Nat.le_refl _, fun _ _ => rfl, hcone0, hml⟩)
        (fun J2 (rbit, s_idx, ()) m1
            ⟨hs_le, hr_le, fuel1, scr1, rng1, sig_cur, hlen1, hfuel1, hscr1, hcone1, hm1⟩
            hLoop2 => ?_)
      have hexit : ¬ rbit = 0xFFFFFFFF#32 := by intro h; rw [h] at hr_le; revert hr_le; decide
      have hexitQ : Q (rbit, ()) m1 :=
        hQ rbit fuel1 scr1 rng1 sig_cur m1 hlen1 hfuel1 hscr1 hcone1 (fun h => absurd h hexit) hm1
      c0_split
      · c0_split
        · c0_split
          · fsv_group
            have hs_lt : s_idx.toNat < 8 := by c0_bound
            have hr_lt : rbit.toNat < 64 := by c0_bound
            have hnz_nv : nv ≠ 0#32 := by intro he; rw [he] at hnv_pos; simp at hnv_pos
            refine wp_join_group
              (fun (a0, ()) mJ => mJ = m1 ∧ (s_idx.toNat < 2 → a0 = 0xFFFFFFFF#32))
              (fun _ (a0, ()) mJ ⟨hmJ, ha0⟩ => by
                subst hmJ
                c0_call hdpll
                refine ⟨c, F_cur, _, R, rfl, hlen1, hcap, hcone1, hm1, ?_⟩
                intro d fuel2 scr2 rng2 m2 _ hlen2 hfuel2 hscr2 hcone2 hdom hunsat hm2
                let s2 : FullState :=
                  { s with
                    core := { s.core with fuel := fuel2 }
                    scratch := { s.scratch with
                      scratch_buf := scr2, rng_state := rng2, sim_sig := sig_cur } }
                have hfuel2_0 : fuel2.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuel2 hfuel1
                have hscr2_0 : ∀ k < 1024, scr2[k]? = s.scratch.scratch_buf[k]? :=
                  fun k hk => (hscr2 k hk).trans (hscr1 k hk)
                fsv_steps
                · have ha0_ff : a0 = 0xFFFFFFFF#32 := by c0_bound
                  have hd20 : d = 20#64 := by c0_bound
                  have hunsat' : (cnfOfClauses F_cur).Unsat := by
                    have hu := hunsat hd20
                    rw [ha0_ff] at hu
                    exact fullSweepDpllUnsat_nil hnv_24 hu
                  exact hQ 0xFFFFFFFF#32 fuel2 scr2 rng2 sig_cur m2 hlen2 hfuel2_0
                    hscr2_0 hcone2 (fun _ => hunsat') hm2
                · have hs1 : (s_idx + 1#32).toNat = s_idx.toNat + 1 := by bv_omega
                  exact hLoop2 (rbit, s_idx + 1#32, ()) m2 (by dsimp only; omega)
                    ⟨by omega, by omega, fuel2, scr2, rng2, sig_cur, hlen2, hfuel2_0,
                      hscr2_0, hcone2, hm2⟩
                · have hs1 : (s_idx + 1#32).toNat = s_idx.toNat + 1 := by bv_omega
                  c0_call hrefine
                  refine ⟨c, s2, R, rfl, hlen2, hcap, hnv_24, hnv_mx,
                    hcone2.2.2.2.2.2.1, hm2, ?_⟩
                  intro sig_next m3 hsig_len hm3
                  have hcone3 : FullSweepConeOk F_cur
                      { s2 with scratch := { s2.scratch with sim_sig := sig_next } }
                      nv.toNat nc.toNat :=
                    fullSweepConeOk_with_scratch hcone2 rfl rfl rfl (fun _ _ => rfl)
                  have hlen3 : ({ s2 with scratch :=
                      { s2.scratch with sim_sig := sig_next } } : FullState).LengthsOk c :=
                    ⟨hlen2.core_ok, { hlen2.scratch_ok with sim_sig_len := hsig_len }⟩
                  have hr1 : (rbit + 1#32).toNat = rbit.toNat + 1 := by bv_omega
                  fsv_steps
                  apply hJ
                  fsv_steps
                  exact hLoop2 (rbit + 1#32, s_idx + 1#32, ()) m3 (by dsimp only; omega)
                    ⟨by omega, by omega, fuel2, scr2, rng2, sig_next, hlen3, hfuel2_0,
                      hscr2_0, hcone3, hm3⟩
                · have hs1 : (s_idx + 1#32).toNat = s_idx.toNat + 1 := by bv_omega
                  exact hLoop2 (rbit, s_idx + 1#32, ()) m2 (by dsimp only; omega)
                    ⟨by omega, by omega, fuel2, scr2, rng2, sig_cur, hlen2, hfuel2_0,
                      hscr2_0, hcone2, hm2⟩)
              (fun Ja0 hJa0 => by
                fsv_steps
                · exact hJa0 (0xFFFFFFFF#32, ()) m1 ⟨rfl, fun _ => rfl⟩
                · have hs_ge2 : ¬ s_idx.toNat < 2 := by c0_bound
                  exact hJa0 _ m1 ⟨rfl, fun h2 => absurd h2 hs_ge2⟩)
          · fsv_steps; exact hexitQ
        · fsv_steps; exact hexitQ
      · fsv_steps; exact hexitQ

end SeedSim

end LeanQbe.T.Examples.Kissat.Full
