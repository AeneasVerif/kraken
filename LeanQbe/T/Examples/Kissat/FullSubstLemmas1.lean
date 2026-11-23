module

public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.Full3
import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Examples.Kissat.FullArena
public meta import LeanQbe.T.Logic.Rules
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat `D-Full` BIG SCC Substitution — Part 1 (`Stage 4`, UNSAT-Only)

Defines:
1. Canonical Stage-4 UNSAT-only invariants (`FullSubstSpecs`: matching `FullSpec1`–`FullSpec3`
   1:1), transition wrappers for callees, and owned `Spec` contracts (`fullSubstElimVarsSpec`,
   `fullSubstRewriteBinsSpec`, `fullSubstRewriteArSpec`, `fullSubstituteSpec`).
2. Strictly scoped tactic & bitvector helpers (`FullSubstTactics`).
3. Pure BIG substitution congruence lemmas and `full_subst_elim_vars_wp` (`Full3.lean` #26).
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

/-! ## 1. Canonical Stage-4 Invariants & Local `Spec` Contracts (`FullSubstSpecs`) -/

namespace FullSubstSpecs

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

@[expose] def FullReasonsMarked (s : FullState) : Prop :=
  ∀ idx < s.core.trail_end,
    let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
    let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
    0 < (s.core.lvl[v]?.getD 0#32).toNat →
    (rsn &&& 0x80000000#32) = 0#32 →
    (fullArenaHdr s rsn.toNat &&& 0x00200000#32) ≠ 0#32

@[expose] def FullReprEquiv (F_cur : List (List Nat)) (s : FullState) : Prop :=
  ∀ l < 2 * s.core.cur_vars,
    let r := (s.core.repr[l]?.getD 0#32).toNat
    r < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l, r ^^^ 1]) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1, r])

@[expose] def FullOtfsWitnessInv := FullWitnessInv

@[expose] def FullTrailExt (k k' : FullCoreState) : Prop :=
  k.trail_end ≤ k'.trail_end ∧
  (∀ i < k.trail_end, k'.trl[i]? = k.trl[i]?) ∧
  (∀ i < k.trail_end,
    k'.lvl[(k.trl[i]?.getD 0#32).toNat / 2]? = k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?)

@[expose] def FullArenaPermEq (k k' : FullCoreState) : Prop :=
  k'.arena_len = k.arena_len ∧
  fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
  ∀ r ∈ fullArenaClauseRefsCore k,
    fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
    fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
    (fullArenaClauseLitsCore k' r).Perm (fullArenaClauseLitsCore k r)

theorem FullSparseInvW.toSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullSparseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInv.exists_witness {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : ∃ F_cur, FullSparseInvW c F0 F_cur s :=
  let ⟨F_cur, hw⟩ := h.1.witness
  ⟨F_cur, h.1.lengths, hw, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem FullExtScratchOk.of_pres {c : FullCfg} {s s' : FullState}
    (h : FullExtScratchOk c s) (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') : FullExtScratchOk c s' := by
  refine ⟨fun i hi => ?_, hpres.2 ▸ h.2⟩
  dsimp only; rw [hpres.1]
  exact (h.1 i hi).elim Or.inl fun hr => Or.inr (hsub _ hr)

theorem FullArenaVarsNodup.of_arena_eq {s s' : FullState}
    (ha : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : FullArenaVarsNodup s) : FullArenaVarsNodup s' := by
  intro r hr hng
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [ha, hal]
  have hgarb : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [ha]
  have hlits : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [ha]
  rw [hrefs] at hr; rw [hgarb] at hng; rw [hlits]
  exact h r hr hng

theorem level0_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
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

/-! ### Callee specifications (exact `FullSpec2` / `FullSpec3` match) -/

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
      sc'.shrink_stk = s.scratch.shrink_stk →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars,
          vals'[l]?.getD 0#8 =
            if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
              s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ v < s.core.cur_vars,
          lvl'[v]?.getD 0#32 =
            if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat then
              s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullPropagateDelSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                      phases := phases', delayed := delayed' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullPropagateSpec_of_del {a : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullPropagateDelSpec a m Q X) : fullPropagateSpec a m Q X := by
  rcases a with ⟨hptr, ⟨⟩⟩
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩ := h
  exact ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm,
    fun r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph m'
        hlen' hw' htr hap hfl hd h0 h1 h2 heq hm' =>
      hQ r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph
        s.scratch.delayed m' hlen' hw' htr hap hfl hd h0 h1 h2 heq hm'⟩

@[expose] def fullArenaSweepSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ (0 < s.core.cur_level → FullReasonsMarked s) ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
      fred' ni' nr' nb' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
                                wusable := wu', arena_garbage := 0#64, first_reducible := fred',
                                num_irred := ni', num_redundant := nr', num_binary := nb',
                                oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
      sc'.extend_len = s.scratch.extend_len → sc'.work_stk2 = s.scratch.work_stk2 →
      FullLastLearnedWf s' → FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
      (r = 0#64 ∨ r = 1#64 → oom' = 0#64) →
      (0 < s.core.cur_level → r = 0#64 →
        vals' = s.core.vals ∧ lvl' = s.core.lvl ∧ trl' = s.core.trl ∧
        tp' = s.core.trail_pos ∧ te' = s.core.trail_end) →
      (r = 1#64 → s.core.cur_level = 0 ∧ s.core.trail_end < te') →
      (r = 2#64 → s.core.cur_level = 0 ∧ F0.Unsat) →
      (r = 3#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullExtendPush2Spec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _ot, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧ s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

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

@[expose] def fullSetInactiveSpec : Spec [i64, i32, i32] [] := fun (h, v, _flag, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ v.toNat then
      Q () m
    else
      ∀ flags' unass' m',
        flags'.length = c.max_vars →
        let s' : FullState :=
          { s with core := { s.core with flags := flags', unassigned := unass' } }
        (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullAddUnitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    (lit.toNat < 2 * s.core.cur_vars → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', cur_level := cl', unassigned := unass',
                                unflushed := unfl', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', target_assigned := ta',
                                      best_assigned := ba', phases_target := pt',
                                      phases_best := pb', heap := hp', pos := ps',
                                      heap_len := hl', q_search_idx := qsi',
                                      q_search_stamp := qss' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → cl' = 0 →
      (lit.toNat < 2 * s.core.cur_vars → ok = false → F0.Unsat ∧ inc' ≠ 0#64) →
      (ok = false → 2 * s.core.cur_vars ≤ lit.toNat ∨ (F0.Unsat ∧ inc' ≠ 0#64)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullTarjanSccSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
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
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ### Owned BIG substitution specifications (exact `FullSpec3` match) -/

@[expose] def fullSubstElimVarsSpec : Spec [i64, i64] [.bool] := fun (h, ucnt, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ FullReprEquiv F_cur s ∧
    ucnt.toNat ≤ c.max_vars ∧
    (∀ k < ucnt.toNat,
      (s.scratch.shrink_stk[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(s.scratch.shrink_stk[k]?.getD 0#32).toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → FullReprEquiv F_cur s' →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullSubstRewriteBinsSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ FullReprEquiv F_cur s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullReprEquiv F_cur s' → (ok = false → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullSubstRewriteArSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ FullReprEquiv F_cur s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullSubstituteSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullSubstSpecs

open FullSubstSpecs

/-! ## 2. Strictly Scoped Tactic & Bitvector Helpers (`FullSubstTactics`) -/

namespace FullSubstTactics

open FullArenaTactics
open scoped FullArenaTactics

@[scoped bv_c0] theorem bv64_sext1 : BitVec.signExtend 64 (1 : BitVec 32) = 1#64 := rfl

@[scoped bv_c0] theorem bv64_shl_1bv (x : BitVec 64) :
    (x <<< (1#64 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_ushr_1bv (x : BitVec 64) :
    (x >>> (1#64 : BitVec 64)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem bv32_ushr_1bv (x : BitVec 32) :
    (x >>> (1#32 : BitVec 32)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "subst_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)

scoped macro "subst_unmdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _ | skip)

scoped macro "subst_steps" : tactic =>
  `(tactic| (
      subst_unmdata
      (repeat subst_strip)
      c0_steps
      repeat (any_goals (subst_strip; repeat subst_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
scoped elab "subst_to_group" : tactic => do
  evalTactic (← `(tactic| subst_unmdata))
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split it once. -/
scoped elab "subst_split" : tactic => do
  evalTactic (← `(tactic| subst_unmdata))
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

@[scoped bv_c0] theorem bv64_one_toNat : ((1 : BitVec 64)).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_two_toNat : ((2 : BitVec 64)).toNat = 2 := rfl
@[scoped bv_c0] theorem bv64_shl_one (x : BitVec 64) :
    (x <<< (1 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := bv64_shl_1bv x

section FastLet
variable {Γ : Env} {rs : List Ty} {n : Nat} {Q : Post rs} {X : XPost} {m : Mem 64}
theorem wp_head_eq {e1 e2 : Expr Val Cont rs} (h : e1 = e2) (hk : wp Γ Q X e2 m) :
    wp Γ Q X e1 m := h ▸ hk
theorem wp_let_head {sig ts : List Ty} {c : OpCode sig ts} {args : Tup (Arg Val) sig}
    {k : Tup Val ts → Expr Val Cont rs} {r : Tup Val ts} (hr : ∀ P, P r → c.wp (vals args) P)
    (hk : wp Γ Q X (k r) m) : wp Γ Q X (.let_ (Op.mk c args) k) m := hr _ hk
theorem wp_blocks_here {ts : List Ty} {sig : List (List Ty)}
    {b : Tup Val ts → Expr Val Cont rs} {bs : Blocks Val Cont rs sig} {xs : Tup Val ts}
    (h : wp Γ Q X (b xs) m) : wp Γ Q X (Blocks.get (Blocks.cons b bs) .here xs) m := h
theorem wp_ret_head {xs : Tup (Arg Val) rs} (h : Q (vals xs) m) :
    wp Γ Q X (.ret xs) m := h
theorem wp_jump_head {ts : List Ty} {J : Cont ts} {xs : Tup (Arg Val) ts}
    (h : J (vals xs) m) : wp Γ Q X (.jump J xs) m := h
theorem wp_let_add_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va + vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem wp_let_sub_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va - vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem wp_let_mul_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va * vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem wp_let_and_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va &&& vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem wp_let_or_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va ||| vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem wp_let_xor_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va ^^^ vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem wp_let_eq_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va == vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n)) (a, b, ())) k) m := by
  cases ha; cases hb; simpa only [wp, Op.wp, OpCode.wp, vals, liftCmp, evalBits_eq_beq,
    Ty.hasFloat, Bool.false_eq_true, ite_false] using hk
theorem wp_let_ne_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va != vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne (.bits n)) (a, b, ())) k) m := by
  cases ha; cases hb; simpa only [wp, Op.wp, OpCode.wp, vals, liftCmp, evalBits_ne_bne,
    Ty.hasFloat, Bool.false_eq_true, ite_false] using hk
theorem wp_let_ult_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.ult vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n)) (a, b, ())) k) m := by
  cases ha; cases hb; exact hk
theorem wp_let_zext32_64 {a : Arg Val i32} {va : BitVec 32} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.setWidth 64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
theorem wp_let_trunc64_32 {a : Arg Val i64} {va : BitVec 64} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
theorem wp_let_shl64_1 {a b : Arg Val i64} {va : BitVec 64} {k} (ha : a.val = va)
    (hb : b.val = (1 : BitVec 64)) (hk : wp Γ Q X (k (va <<< (1 : BitVec 64), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl i64) (a, b, ())) k) m := by
  cases ha
  have h1 : a.val <<< ((1 : BitVec 64)).toNat = a.val <<< (1 : BitVec 64) := rfl
  have h1m : a.val <<< ((1 : BitVec 64).toNat % 64) = a.val <<< (1 : BitVec 64) := rfl
  simpa only [wp, Op.wp, OpCode.wp, vals, lift2, hb, h1, h1m, Ty.hasFloat, Bool.false_eq_true,
    ite_false] using hk
end FastLet

scoped macro "s_head_let" : tactic => `(tactic| (
  apply FullSubstTactics.wp_let_head
  · intro P hP; try dsimp (config := { zeta := false }) only
    simp only [LeanQbe.T.OpCode.wp, LeanQbe.T.OpCode.wp_cmp, LeanQbe.T.OpCode.wp_select,
      LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule,
      LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.uge, LeanQbe.T.OpCode.slt, LeanQbe.T.OpCode.sle,
      LeanQbe.T.OpCode.sgt, LeanQbe.T.OpCode.sge, LeanQbe.T.vals_nil, LeanQbe.T.vals_cons,
      LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, LeanQbe.T.Ty.hasFloat_vec,
      LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree, LeanQbe.T.evalBits_eq_beq,
      LeanQbe.T.evalBits_ne_bne, LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_ule_eq,
      LeanQbe.T.evalBits_ugt_eq, LeanQbe.T.evalBits_uge_eq, LeanQbe.T.evalBits_slt_eq,
      LeanQbe.T.evalBits_sle_eq, LeanQbe.T.evalBits_sgt_eq, LeanQbe.T.evalBits_sge_eq,
      LeanQbe.T.evalBool_eq_beq, LeanQbe.T.evalBool_ne_bne, LeanQbe.T.evalBool_ult_eq,
      LeanQbe.T.evalBool_ule_eq, LeanQbe.T.evalBool_ugt_eq, LeanQbe.T.evalBool_uge_eq,
      LeanQbe.T.evalBool_slt_eq, LeanQbe.T.evalBool_sle_eq, LeanQbe.T.evalBool_sgt_eq,
      LeanQbe.T.evalBool_sge_eq, LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.lift3,
      LeanQbe.T.liftCmp, cast_eq, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false,
      BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul,
      BitVec.reduceToNat, Nat.reduceMod, Nat.reduceDiv]
    try refine ⟨by decide, ?_⟩
    exact hP))

scoped macro "s_call" h:term : tactic => `(tactic| (
  refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_)
  try simp only [LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var,
    LeanQbe.T.Arg.val_imm]))

private meta def sFastRun (stopOnJnz : Bool) : Lean.Elab.Tactic.TacticM Unit := do
  let binOps : Array (Lean.Name × Lean.Name) := #[
    (``OpCode.add, ``wp_let_add_b), (``OpCode.sub, ``wp_let_sub_b), (``OpCode.mul, ``wp_let_mul_b),
    (``OpCode.and, ``wp_let_and_b), (``OpCode.or, ``wp_let_or_b), (``OpCode.xor, ``wp_let_xor_b),
    (``OpCode.eq, ``wp_let_eq_b), (``CmpOp.eq, ``wp_let_eq_b), (``OpCode.ne, ``wp_let_ne_b),
    (``CmpOp.ne, ``wp_let_ne_b), (``OpCode.ult, ``wp_let_ult_b), (``CmpOp.ult, ``wp_let_ult_b)]
  let unOps : Array (Lean.Name × Lean.Name) :=
    #[(``OpCode.zext, ``wp_let_zext32_64), (``OpCode.trunc, ``wp_let_trunc64_32)]
  let clearSet : Array Lean.Name := #[
    ``Exists, ``Std.ExtHashMap.sep, ``FullMem, ``FullSparseInvW, ``FullSparseInv,
    ``FullWitnessInv, ``FullReprEquiv, ``WatchesInv, ``AgreesExcept, ``FullArenaVarsNodup,
    ``FullExtScratchOk, ``FullLitMarksClear, ``LitEquiv, ``CNF.EntailsClause]
  let rec normProj : Nat → Lean.Expr → Lean.Expr
    | 0, x => x
    | n + 1, x =>
      let x := x.consumeMData
      if (x.isAppOf ``Prod.fst || x.isAppOf ``Prod.snd) && x.getAppNumArgs ≥ 3 then
        let p := normProj n (x.getArg! 2)
        if p.isAppOf ``Prod.mk && p.getAppNumArgs ≥ 4 then
          normProj n (p.getArg! (if x.isAppOf ``Prod.fst then 2 else 3))
        else x
      else x
  let argVal (x : Lean.Expr) : Option (Lean.Expr × Bool) :=
    let x := x.consumeMData
    if x.isAppOf ``LeanQbe.T.Arg.var then
      let v := normProj 6 x.appArg!
      some (v, v.isAppOf ``OfNat.ofNat || v.isAppOf ``BitVec.ofNat)
    else if x.isAppOf ``LeanQbe.T.Arg.imm then some (normProj 6 x.appArg!, true)
    else none
  let hdrLoadLems : Array Lean.Name := #[
    ``load_full_cur_vars, ``load_full_arena_len, ``load_full_arena_garbage,
    ``load_full_cur_level, ``load_full_inconsistent, ``load_full_oom, ``load_full_subst_cnt,
    ``load_full_wusable, ``load_full_num_binary, ``load_full_arena_ptr, ``load_full_repr_ptr,
    ``load_full_watch_vec_ptr, ``load_full_watch_stk_ptr, ``load_full_lit_mark_ptr,
    ``load_full_work_stk1_ptr, ``load_full_work_stk2_ptr]
  let hdrStoreLems : Array Lean.Name := #[
    ``store_full_wusable, ``store_full_num_binary, ``store_full_arena_garbage,
    ``store_full_inconsistent]
  let pickLems (isLoad : Bool) (ty : Lean.Expr) : Array Lean.Name :=
    if (ty.find? (·.isConstOf ``FullCfg.pWstk)).isSome then
      if isLoad then #[``c0_load_full_wstk, ``load_full_wstk]
      else #[``c0_store_full_wstk, ``store_full_wstk]
    else if (ty.find? (·.isConstOf ``FullCfg.pWvec)).isSome then
      if isLoad then #[``c0_load_full_wvec, ``load_full_wvec]
      else #[``c0_store_full_wvec, ``store_full_wvec]
    else if (ty.find? (·.isConstOf ``FullCfg.pRepr)).isSome then
      if isLoad then #[``c0_load_full_repr, ``load_full_repr] else #[]
    else if (ty.find? (·.isConstOf ``FullCfg.pArena)).isSome then
      if isLoad then #[``c0_load_full_arena, ``load_full_arena]
      else #[``c0_store_full_arena, ``store_full_arena]
    else if (ty.find? (·.isConstOf ``FullCfg.pLitMark)).isSome then
      if isLoad then #[``c0_load_full_lit_mark, ``load_full_lit_mark]
      else #[``c0_store_full_lit_mark, ``store_full_lit_mark]
    else if (ty.find? (·.isConstOf ``FullCfg.pWorkStk1)).isSome then
      if isLoad then #[``c0_load_full_work_stk1, ``load_full_work_stk1]
      else #[``c0_store_full_work_stk1, ``store_full_work_stk1]
    else if (ty.find? (·.isConstOf ``FullCfg.pWorkStk2)).isSome then
      if isLoad then #[``c0_load_full_work_stk2, ``load_full_work_stk2]
      else #[``c0_store_full_work_stk2, ``store_full_work_stk2]
    else if isLoad then hdrLoadLems else hdrStoreLems
  let solveMem (isLoad : Bool) (hmv : Lean.MVarId) : Lean.Elab.Tactic.TacticM Unit := do
    Lean.Elab.Tactic.setGoals [hmv]
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]);
        (try dsimp (config := { zeta := false }) only)))
    let hmv ← Lean.Elab.Tactic.getMainGoal
    let lems := pickLems isLoad (← Lean.instantiateMVars (← hmv.getType))
    let mut solved := false
    for nm in lems do
      let s ← Lean.saveState
      let ok ← try
        let sub ← Lean.Meta.withReducible <| hmv.apply (← Lean.Meta.mkConstWithFreshMVarLevels nm)
        let mut allOk := true
        for g' in sub do
          if !allOk then break
          if (← Lean.instantiateMVars (← g'.getType)).isAppOf ``Std.ExtHashMap.sep then
            Lean.Elab.Tactic.setGoals [g']
            Lean.Meta.withReducible <|
              Lean.Elab.Tactic.evalTactic (← `(tactic| first | assumption | c0_frame))
            if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then allOk := false
        for g' in sub do
          if !allOk || (← g'.isAssigned) then continue
          if ← Lean.Meta.isProp (← g'.getType) then
            Lean.Elab.Tactic.setGoals [g']
            Lean.Elab.Tactic.evalTactic (← `(tactic| first | rfl | assumption | decide | skip))
            if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then continue
            let g' ← Lean.Elab.Tactic.getMainGoal
            let toClear ← g'.withContext do
              let mut ids : Array Lean.FVarId := #[]
              for d in (← Lean.getLCtx).decls do
                let some d := d | continue
                if d.isAuxDecl || d.isLet then continue
                if ← Lean.Meta.isProp d.type then
                  let ty := d.type.consumeMData
                  let isBig := ty.isForall && !ty.bindingBody!.consumeMData.isConstOf ``False
                  if isBig || (ty.getAppFn.constName?.any (clearSet.contains ·)) then
                    ids := ids.push d.fvarId
              pure ids
            let g' ← g'.tryClearMany toClear
            Lean.Elab.Tactic.setGoals [g']
            Lean.Elab.Tactic.evalTactic (← `(tactic|
              ((try dsimp (config := { zeta := false }) only)
               (try simp only [List.length_set])
               first | assumption | rfl | decide | omega
                     | (simp only [bv_c0, FullSubstTactics.bv64_one_toNat,
                          FullSubstTactics.bv64_two_toNat, FullSubstTactics.bv64_shl_one,
                          BitVec.toNat_add, ← BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
                          BitVec.toNat_setWidth, Nat.reduceMod, Nat.reducePow, BitVec.reduceToNat];
                        omega))))
            if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then allOk := false
        for g' in sub do if !(← g'.isAssigned) then allOk := false
        pure allOk
      catch _ => pure false
      if ok then solved := true; break else s.restore
    if !solved then throwError "sFastRun: solveMem failed on {← hmv.getType}"
  let headBetaWp (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM Lean.MVarId :=
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
        let e' := (ty.getArg! 4).consumeMData.headBeta.consumeMData
        if e' == ty.getArg! 4 then return g
        let mvar ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
        g.assign (← Lean.Meta.mkAppM ``wp_head_eq #[← Lean.Meta.mkEqRefl e', mvar])
        return mvar.mvarId!
      return g
  let mut todo ← Lean.Elab.Tactic.getGoals
  let mut done : List Lean.MVarId := []
  while !todo.isEmpty do
    let g0 :: rest := todo | break
    todo := rest
    let ty0 := (← Lean.instantiateMVars (← g0.getType)).consumeMData.headBeta
    if ty0.isAppOf ``LeanQbe.T.Func.wp && ty0.getAppNumArgs ≥ 4 then
      if let some fn := (ty0.getArg! 3).getAppFn.constName? then
        Lean.Elab.Tactic.setGoals [g0]
        Lean.Elab.Tactic.evalTactic
          (← `(tactic| unfold LeanQbe.T.Func.wp $(Lean.mkIdent fn):ident))
        todo := (← Lean.Elab.Tactic.getGoals) ++ todo; continue
    let g ← headBetaWp g0
    let head? ← g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
        return some ((ty.getArg! 4).consumeMData.getAppFn.constName?, ty.getArg! 5)
      return none
    let some (fn?, m0) := head? | done := g :: done; continue
    if fn? == some ``LeanQbe.T.Blocks.get then
      Lean.Elab.Tactic.setGoals [g]
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply FullSubstTactics.wp_blocks_here))
      todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.let_ then
      let fastGoal? ← g.withContext do
        let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
        let e := (ty.getArg! 4).consumeMData
        if e.getAppNumArgs < 6 then return none
        let op := (e.getArg! 4).consumeMData
        if !(op.isAppOf ``LeanQbe.T.Op.mk && op.getAppNumArgs ≥ 5) then return none
        let gΓ := ty.getArg! 0; let grs := ty.getArg! 1; let gQ := ty.getArg! 2
        let gX := ty.getArg! 3; let gm := ty.getArg! 5; let gk := e.getArg! 5
        let code := (op.getArg! 3).consumeMData; let args := (op.getArg! 4).consumeMData
        let applyPf (nm : Lean.Name) (xs : Array (Option Lean.Expr)) :
            Lean.Meta.MetaM (Option Lean.MVarId) := do
          let s ← Lean.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkAppOptM nm xs) | s.restore; return none
            return some hk
          catch _ => s.restore; return none
        let c := code.getAppFn.constName?
        let key? :=
          if c == some ``OpCode.cmp && code.getAppNumArgs ≥ 1 then
            (code.getArg! 0).consumeMData.getAppFn.constName?
          else c
        if !(args.isAppOf ``Prod.mk && args.getAppNumArgs ≥ 4) then return none
        let a := args.getArg! 2; let r := (args.getArg! 3).consumeMData
        let some (va, ia) := argVal a | return none
        if let some (_, nm) := key?.bind fun k => binOps.find? (·.1 == k) then
          if !(r.isAppOf ``Prod.mk && r.getAppNumArgs ≥ 4) then return none
          let b := r.getArg! 2
          let some (vb, ib) := argVal b | return none
          if ia && ib then return none
          applyPf nm #[some gΓ, some grs, none, some gQ, some gX, some gm, some a, some b,
            some va, some vb, some gk, some (← Lean.Meta.mkEqRefl va),
            some (← Lean.Meta.mkEqRefl vb)]
        else if let some (_, nm) := c.bind fun k => unOps.find? (·.1 == k) then
          if ia then return none
          applyPf nm #[some gΓ, some grs, some gQ, some gX, some gm, some a, some va, some gk,
            some (← Lean.Meta.mkEqRefl va)]
        else if c == some ``OpCode.shl && !ia && r.isAppOf ``Prod.mk && r.getAppNumArgs ≥ 4 then
          let b := r.getArg! 2
          let some (vb, _) := argVal b | return none
          applyPf ``wp_let_shl64_1 #[some gΓ, some grs, some gQ, some gX, some gm, some a, some b,
            some va, some gk, some (← Lean.Meta.mkEqRefl va), some (← Lean.Meta.mkEqRefl vb)]
        else return none
      if let some hk := fastGoal? then todo := hk :: todo
      else
        Lean.Elab.Tactic.setGoals [g]
        Lean.Elab.Tactic.evalTactic (← `(tactic| s_head_let))
        todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.load then
      let gs ← g.withContext <|
        g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``LeanQbe.T.wp_load_of)
      let [hl, hk] := gs.take 2 | throwError "sFastRun: bad load"
      solveMem true hl
      todo := hk :: todo
    else if fn? == some ``LeanQbe.T.Expr.store then
      let gs ← g.withContext <|
        g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``LeanQbe.T.wp_store_sep)
      let [hs, hk] := gs.take 2 | throwError "sFastRun: bad store"
      solveMem false hs
      Lean.Elab.Tactic.setGoals [hk]
      let mId := Lean.mkIdent `m; let hmId := Lean.mkIdent `hm
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
      Lean.Elab.Tactic.evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var,
        LeanQbe.T.Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| try dsimp (config := { zeta := false }) only at $hmId:ident))
      if let .fvar mId0 := m0 then
        Lean.Elab.Tactic.withMainContext do
          for d in (← Lean.getLCtx).decls.toArray.reverse do
            let some d := d | continue
            let t ← Lean.instantiateMVars d.type
            if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
              try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId
              catch _ => pure ()
          try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId0 catch _ => pure ()
      todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.jnz then
      Lean.Elab.Tactic.setGoals [g]
      let hc := Lean.mkIdent `hc
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_) <;> (
          try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm] at $hc:ident
          c0_cond $hc
          try (first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                     | exact absurd trivial $hc))))
      if stopOnJnz then done := (← Lean.Elab.Tactic.getGoals).reverse ++ done
      else todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.ret then
      Lean.Elab.Tactic.setGoals [g]
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        (apply FullSubstTactics.wp_ret_head
         simp only [LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var,
           LeanQbe.T.Arg.val_imm])))
      done := (← Lean.Elab.Tactic.getGoals).reverse ++ done
    else if fn? == some ``LeanQbe.T.Expr.jump then
      Lean.Elab.Tactic.setGoals [g]
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        (apply FullSubstTactics.wp_jump_head
         simp only [LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var,
           LeanQbe.T.Arg.val_imm])))
      done := (← Lean.Elab.Tactic.getGoals).reverse ++ done
    else
      done := g :: done
  Lean.Elab.Tactic.setGoals done.reverse

scoped elab "s_steps" : tactic => sFastRun false
scoped elab "s_to_group" : tactic => sFastRun false
scoped elab "s_split" : tactic => sFastRun true

end FullSubstTactics

open FullSubstTactics
open scoped FullArenaTactics FullSubstTactics

/-! ## 3. Bitvector, BIG Substitution, & Callee-Preservation Helpers -/

namespace FullSubstHelpers

theorem bv32_trunc_toNat {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    (BitVec.setWidth 32 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem nat_two_mul_xor_one (n : Nat) : (2 * n) ^^^ 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    simp [Nat.testBit_succ, Nat.mul_add_div (by decide : 0 < 2)]

theorem bv32_and_litMask_lt (w0 : BitVec 32) : (w0 &&& 0x7FFFFFFF#32).toNat < 0x80000000 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem bv32_bit31_eq_zero_of_lt {x : BitVec 32} (h : x.toNat < 0x80000000) :
    (x &&& 0x80000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
    show (0#32).toNat = 0 from rfl]
  have hlt : x.toNat < 2 ^ 31 := h
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : i = 31
  · subst hi; rw [Nat.testBit_lt_two_pow hlt]; rfl
  · simp [Ne.symm hi]

theorem FullReprEquiv.litEquiv {F_cur : List (List Nat)} {s : FullState}
    (h : FullReprEquiv F_cur s) {l : Nat} (hl : l < 2 * s.core.cur_vars) :
    LitEquiv (cnfOfClauses F_cur) l (s.core.repr[l]?.getD 0#32).toNat :=
  ⟨(h l hl).2.2, (h l hl).2.1⟩

theorem FullReprEquiv.lt {F_cur : List (List Nat)} {s : FullState}
    (h : FullReprEquiv F_cur s) {l : Nat} (hl : l < 2 * s.core.cur_vars) :
    (s.core.repr[l]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
  (h l hl).1

theorem entails_bin_subst {f : CNF Nat} {a b a' b' : Nat}
    (ha : LitEquiv f a a') (hb : LitEquiv f b b')
    (hc : f.EntailsClause (cnfClause [a, b])) :
    f.EntailsClause (cnfClause [a', b']) := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  rw [← litEquiv_eval hα ha, ← litEquiv_eval hα hb]; exact h1

theorem entails_unit_of_dup {f : CNF Nat} {a : Nat}
    (hc : f.EntailsClause (cnfClause [a, a])) :
    f.EntailsClause (cnfClause [a]) := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  simpa using h1

theorem entails_clause_subst {f : CNF Nat} {cs cs' : List Nat}
    (hmap : ∀ l ∈ cs, ∃ l' ∈ cs', LitEquiv f l l')
    (hc : f.EntailsClause (cnfClause cs)) :
    f.EntailsClause (cnfClause cs') := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  rw [clauseEvalVal, List.any_eq_true] at h1 ⊢
  obtain ⟨l, hl, hsat⟩ := h1
  obtain ⟨l', hl', heq⟩ := hmap l hl
  exact ⟨l', hl', by rw [← litEquiv_eval hα heq]; exact hsat⟩

theorem fullSparseInvW_afterAddUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss'}
    (hsok : ({ s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', target_assigned := ta',
                                    best_assigned := ba', phases_target := pt',
                                    phases_best := pb', heap := hp', pos := ps',
                                    heap_len := hl', q_search_idx := qsi',
                                    q_search_stamp := qss' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', cur_level := cl', unassigned := unass',
                    unflushed := unfl', inconsistent := inc' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', target_assigned := ta',
                                    best_assigned := ba', phases_target := pt',
                                    phases_best := pb', heap := hp', pos := ps',
                                    heap_len := hl', q_search_idx := qsi',
                                    q_search_stamp := qss' } } :=
  ⟨hsok, hw', hsp.2.2.1, FullArenaVarsNodup.of_arena_eq rfl rfl hsp.2.2.2.1,
    ⟨fun i hi => hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩

theorem fullSparseInvW_afterAddBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort'}
    (hsok : ({ s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                              oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } } :
          FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    unassigned := unass', unflushed := unfl', wvec := wvec',
                    wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                    oom := oom', inconsistent := inc' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                              oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } } :=
  ⟨hsok, hw', hsp.2.2.1, FullArenaVarsNodup.of_arena_eq rfl rfl hsp.2.2.2.1,
    ⟨fun i hi => hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩

theorem fullSparseInvW_afterPropagate {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases'}
    (hsok : ({ s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' }
        scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                    phases := phases' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', unassigned := unass', unflushed := unfl',
                    wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                    wusable := wu', fuel := fuel', confl_type := ctype',
                    confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                    oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', unassigned := unass', unflushed := unfl',
                    wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                    wusable := wu', fuel := fuel', confl_type := ctype',
                    confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                    oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' }
        scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                    phases := phases' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', unassigned := unass', unflushed := unfl',
                            wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                            wusable := wu', fuel := fuel', confl_type := ctype',
                            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                            oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases' } }
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng
    have hreqs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hperm.2.1
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hreqs] at hr
    obtain ⟨_, hgb, hpm⟩ := hperm.2.2 r hr
    change fullArenaClauseGarbCore s'.core r = false at hng; rw [hgb] at hng
    exact (hsp.2.2.2.1 r hr hng).perm ((hpm.map (· / 2)).symm)
  have hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s' := fun r hr => by
    unfold fullArenaClauseRefs at hr ⊢; rw [hperm.2.1]; exact hr
  exact ⟨hsok, hw', hsp.2.2.1, hnd', hsp.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ hrefs, hsp.2.2.2.2.2⟩

theorem fullSparseInvW_afterPropagateDel {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed'}
    (hsok : ({ s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' }
        scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                    phases := phases', delayed := delayed' } } :
      FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', unassigned := unass', unflushed := unfl',
                    wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                    wusable := wu', fuel := fuel', confl_type := ctype',
                    confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                    oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', unassigned := unass', unflushed := unfl',
                    wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                    wusable := wu', fuel := fuel', confl_type := ctype',
                    confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                    oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' }
        scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                    phases := phases', delayed := delayed' } } := by
  let s0' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', unassigned := unass', unflushed := unfl',
                            wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                            wusable := wu', fuel := fuel', confl_type := ctype',
                            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                            oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
  have hsok0 : s0'.LengthsOk c :=
    ⟨hsok.core_ok,
      { hsok.scratch_ok with delayed_len_arr := hsp.1.scratch_ok.delayed_len_arr }⟩
  have h0 := fullSparseInvW_afterPropagate hsp hsok0 hw' hperm
  exact ⟨hsok, hw', h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2⟩

theorem fullSparseInvW_afterExtPush2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hsok : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len ≤ c.extend_cap) :
    FullSparseInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [heq]
  exact ⟨hsok, heq ▸ hsp.2.1,
    ⟨fun v hv => by rw [heq]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [heq]; exact hsp.2.2.1.2 l hl⟩,
    FullArenaVarsNodup.of_arena_eq (by rw [heq]) (by rw [heq]) hsp.2.2.2.1,
    ⟨fun i hi => by dsimp only; rw [hll, hrefs]; exact hsp.2.2.2.2.1.1 i hi, hext⟩,
    by rw [heq]; exact hsp.2.2.2.2.2⟩

theorem fullSparseInvW_afterSetInactive {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {flags' : List (BitVec 32)} {unass' : BitVec 64} (hfll : flags'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with flags := flags', unassigned := unass' } } :=
  ⟨⟨{ hsp.1.core_ok with flags_len := hfll }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   hsp.2.2.1, FullArenaVarsNodup.of_arena_eq rfl rfl hsp.2.2.2.1,
   hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem bit23_or_shrk (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := by
  intro h; have := congrArg (·[23]) h; simp at this

theorem bit19_or_shrk (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h19 : (0x00080000#32)[i] = true → (0x00800000#32)[i] = false := by revert i hi; decide
  cases h : (0x00080000#32)[i] <;> simp [h19, h]

theorem bit23_or_garb (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h23 : (0x00800000#32)[i] = true → (0x00080000#32)[i] = false := by revert i hi; decide
  cases h : (0x00800000#32)[i] <;> simp [h23, h]

theorem bit19_or_garb_ne0 (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have := congrArg (·[19]) h; simp at this

theorem list_drop_take_map_toNat_eq_range {ar : List (BitVec 32)} {off n : Nat}
    (hbd : off + n ≤ ar.length) :
    ((ar.drop off).take n).map BitVec.toNat =
      (List.range n).map fun j => (ar[off + j]?.getD 0#32).toNat := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro j hj1 _
    simp only [List.length_map, List.length_take, List.length_drop] at hj1
    have hj : j < n := by omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem nodup_range_map_of_pairwise {n : Nat} {f : Nat → Nat}
    (hpw : ∀ i j, i < j → j < n → f i ≠ f j) : ((List.range n).map f).Nodup := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨ih fun i j hij hj => hpw i j hij (by omega), (by simp), fun x hx y hy => ?_⟩
    simp only [List.mem_map, List.mem_range, List.mem_singleton] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx; subst hy; exact hpw i k hi (Nat.lt_succ_self k)

theorem fullSubst_off3_toNat {p : BitVec 64} {k : BitVec 32}
    (hbd : p.toNat + 3 + k.toNat < 2 ^ 64) :
    (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat := by
  have hk := k.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
    show (3#64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem fullSubst_add_u32_toNat {k : BitVec 32} (hlt : k.toNat + 1 < 2 ^ 32) :
    (k + 1#32).toNat = k.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt]

theorem bv8_setWidth32_eq_zero {x : BitVec 8}
    (h : BitVec.setWidth 32 x = 0#32) : x = 0#8 :=
  BitVec.eq_of_toNat_eq (by
    have h1 := congrArg BitVec.toNat h; have hx := x.isLt
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
      show (0#32).toNat = 0 from rfl] at h1
    exact h1)

theorem bv8_getElem_congr {xs : List (BitVec 8)} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (hij : i = j) :
    (xs[i]'hi) = (xs[j]'hj) := by subst hij; rfl

theorem bv32_getElem_congr {xs : List (BitVec 32)} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (hij : i = j) :
    (xs[i]'hi) = (xs[j]'hj) := by subst hij; rfl

end FullSubstHelpers

open FullSubstHelpers

/-! ## 4. `full_subst_elim_vars` `Func.wp` Proof (`Full3.lean` #26) -/

theorem full_subst_elim_vars_del_wp (Γ : Env)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hProp : ∀ args m Q X, fullPropagateDelSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hExtPush2 : ∀ args m Q X, fullExtendPush2Spec args m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] args m Q X)
    (hSetInact : ∀ args m Q X, fullSetInactiveSpec args m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullSubstElimVarsSpec args m Q X →
      Func.wp Γ full_subst_elim_vars_body args m Q X := by
  rintro ⟨h, ucnt, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s0, R, rfl, hsp0, hl0, hrepr0, huc_le, hus0, hm, hQ⟩
  have hmx := c.hmaxv; have hex := c.hext; unfold dimacsBound at hmx hex
  -- Loop 1: `while (k < ucnt) { if (!full_add_unit(h, units[k])) return false; k++; }`
  subst_to_group
  refine wp_loop_inv
    (fun (k, ()) ml =>
      ∃ st : FullState,
        FullSparseInvW c F0 F_cur st ∧
        st.core.cur_vars = s0.core.cur_vars ∧ st.core.cur_level = 0 ∧
        st.core.fuel = s0.core.fuel ∧ st.core.repr = s0.core.repr ∧
        st.scratch.shrink_stk = s0.scratch.shrink_stk ∧
        k.toNat ≤ ucnt.toNat ∧ (FullMem c st ⋆ R) ml)
    (fun (k, ()) _ => ucnt.toNat - k.toNat)
    ?_ ?_
  · intro J hJ; subst_steps
    exact hJ (0#64, ()) m ⟨s0, hsp0, rfl, hl0, rfl, rfl, rfl, Nat.zero_le _, hm⟩
  · rintro J ⟨k, ⟨⟩⟩ ml ⟨st, hsp, hcv, hst_l0, hfl, hrp, hsh, hk_le, hml⟩ hJ
    have hun_l := hsp.1.scratch_ok.shrink_stk_len
    subst_split
    · have hk_lt : k.toNat < ucnt.toNat := by c0_bound
      have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
      have hu_ok := hus0 k.toNat hk_lt
      have hu_get : st.scratch.shrink_stk[k.toNat]'(by omega) =
          s0.scratch.shrink_stk[k.toNat]?.getD 0#32 := by
        rw [← hsh, List.getElem?_eq_getElem (by omega), Option.getD_some]
      subst_steps
      c0_call hAddUnit
      refine ⟨c, F0, F_cur, st, R, rfl, hsp.1, hsp.2.1,
        fun _ => by rw [hu_get]; exact hu_ok.2, hml, ?_⟩
      intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
        phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' st' hlen' hw' hcl' hfail _ hm'
      have hsp' : FullSparseInvW c F0 F_cur st' := fullSparseInvW_afterAddUnit hsp hlen' hw'
      have hrepr' : FullReprEquiv F_cur st' := by
        intro l hl
        change l < 2 * st'.core.cur_vars at hl
        have hl0' : l < 2 * s0.core.cur_vars := by simpa [st', hcv] using hl
        simpa [st', hrp, hcv] using hrepr0 l hl0'
      subst_steps
      · exact hJ (k + 1#64, ()) m' (by dsimp only; omega)
          ⟨st', hsp', by simpa [st'] using hcv, hcl', by simpa [st'] using hfl,
           by simpa [st'] using hrp, hsh, by omega, hm'⟩
      · exact hQ false st' m' hsp' hcl' (by simpa [st'] using hcv)
          (by change st'.core.fuel.toNat ≤ s0.core.fuel.toNat; simp [st', hfl])
          hrepr' (fun _ => (hfail (by rw [hu_get, hcv]; exact hu_ok.1)
            (by cases ok <;> simp_all)).1) hm'
    · -- Exit Loop 1: call `full_propagate(h)` and check `r == 1 || inconsistent != 0`
      subst_steps
      c0_call hProp
      refine ⟨c, F0, F_cur, st, R, rfl, hsp.1, hsp.2.1, hsp.2.2.2.2.2, hml, ?_⟩
      intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
        fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m1 st1
        hlen1 hw1 _ hperm1 hfuel1 _ _ hr1 _ _ hm1
      have hsp1 : FullSparseInvW c F0 F_cur st1 :=
        fullSparseInvW_afterPropagateDel hsp hlen1 hw1 hperm1
      have hcv1 : st1.core.cur_vars = s0.core.cur_vars := hcv
      have hl01 : st1.core.cur_level = 0 := hst_l0
      have hfuel1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := by
        rw [← hfl]; exact hfuel1
      have hrepr1 : FullReprEquiv F_cur st1 := by
        intro l hl
        change l < 2 * st1.core.cur_vars at hl
        have hget : st1.core.repr[l]?.getD 0#32 = s0.core.repr[l]?.getD 0#32 := by
          change st.core.repr[l]?.getD 0#32 = _; rw [hrp]
        have h0 := hrepr0 l (hcv1 ▸ hl)
        refine ⟨by rw [hget, hcv1]; exact h0.1, ?_, ?_⟩
        · simpa [hget] using h0.2.1
        · simpa [hget] using h0.2.2
      subst_split
      · -- `r == 1`: UNSAT
        subst_steps
        have hr1_eq : r = 1#64 := by assumption
        exact hQ false st1 m1 hsp1 hl01 hcv1 hfuel1' hrepr1
          (fun _ => level0_unsat_of_conflict_okW hw1 hl01 (hr1 hr1_eq).2.2) hm1
      · subst_split
        · -- `inconsistent != 0`: UNSAT
          subst_steps
          have hinc_ne : st1.core.inconsistent ≠ 0#64 := by assumption
          exact hQ false st1 m1 hsp1 hl01 hcv1 hfuel1' hrepr1
            (fun _ => hw1.ext_sound.2 (hw1.inconsistent_sound hinc_ne)) hm1
        · -- Loop 2: `while (v < cv)` eliminate vars & push witness pairs
          subst_to_group
          refine wp_loop_inv
            (fun (v, ()) m2 =>
              ∃ st2 : FullState,
                FullSparseInvW c F0 F_cur st2 ∧
                st2.core.cur_vars = s0.core.cur_vars ∧ st2.core.cur_level = 0 ∧
                st2.core.fuel = st1.core.fuel ∧ FullReprEquiv F_cur st2 ∧
                v.toNat ≤ s0.core.cur_vars ∧ (FullMem c st2 ⋆ R) m2)
            (fun (v, ()) _ => s0.core.cur_vars - v.toNat)
            ?_ ?_
          · intro J2 hJ2; subst_steps
            exact hJ2 (0#64, ()) m1 ⟨st1, hsp1, hcv1, hl01, rfl, hrepr1, Nat.zero_le _, hm1⟩
          · rintro J2 ⟨v, ⟨⟩⟩ m2 ⟨st2, hsp2, hcv2, hl02, hfl2, hrepr2, hv_le, hm2⟩ hJ2
            have hcl2 := hsp2.1.core_ok; have hsl2 := hsp2.1.scratch_ok
            have hcv_le2 := hcl2.cur_vars_le
            have hfl_l := hcl2.flags_len; have hrp_l := hcl2.repr_len
            subst_split
            · have hv_lt : v.toNat < s0.core.cur_vars := by c0_bound
              have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
              have hlit_nat : (BitVec.setWidth 32 (v <<< 1#64)).toNat = 2 * v.toNat := by
                rw [BitVec.toNat_setWidth, bv64_shl_1bv]; omega
              have hlit1_nat :
                  ((BitVec.setWidth 32 (v <<< 1#64)) ^^^ 1#32).toNat = 2 * v.toNat + 1 := by
                rw [bv32_xor1_toNat, hlit_nat, nat_two_mul_xor_one]
              have hlit_lt : (BitVec.setWidth 32 (v <<< 1#64)).toNat < 2 * s0.core.cur_vars := by
                omega
              have hlit1_lt :
                  ((BitVec.setWidth 32 (v <<< 1#64)) ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
                omega
              -- Join point after `if (active && rep != lit)` -> `v = v + 1`
              subst_to_group
              refine wp_join_group (ts := [])
                (fun () m3 =>
                  ∃ st3 : FullState,
                    FullSparseInvW c F0 F_cur st3 ∧
                    st3.core.cur_vars = s0.core.cur_vars ∧ st3.core.cur_level = 0 ∧
                    st3.core.fuel = st1.core.fuel ∧ FullReprEquiv F_cur st3 ∧
                    (FullMem c st3 ⋆ R) m3)
                ?_ ?_
              · rintro _ ⟨⟩ m3 ⟨st3, hsp3, hcv3, hl03, hfl3, hrepr3, hm3⟩
                subst_steps
                exact hJ2 (v + 1#64, ()) m3 (by dsimp only; omega)
                  ⟨st3, hsp3, hcv3, hl03, hfl3, hrepr3, by omega, hm3⟩
              · intro Jnext hNext
                subst_split
                · -- `(fl[v] & FL_ACTIVE) != 0`
                  subst_split
                  · -- `rep != lit`
                    subst_split
                    · -- `extend_len + 4 <= extend_cap`: push2 + push2 + set_inactive + subst_cnt++
                      subst_steps
                      c0_call hExtPush2
                      refine ⟨c, st2, R, ⟨rfl, hsp2.2.2.2.2.1.2⟩, hsp2.1, hm2, ?_⟩
                      intro _ st3 m3 hcore3 hlen3 ⟨hll3, hex3, _⟩ hm3
                      have hsp3 : FullSparseInvW c F0 F_cur st3 :=
                        fullSparseInvW_afterExtPush2 hsp2 hlen3 hcore3 hll3 hex3
                      subst_steps
                      c0_call hExtPush2
                      refine ⟨c, st3, R, ⟨rfl, hsp3.2.2.2.2.1.2⟩, hsp3.1, hm3, ?_⟩
                      intro _ st4 m4 hcore4 hlen4 ⟨hll4, hex4, _⟩ hm4
                      have hsp4 : FullSparseInvW c F0 F_cur st4 :=
                        fullSparseInvW_afterExtPush2 hsp3 hlen4 hcore4 hll4 hex4
                      subst_steps
                      c0_call hSetInact
                      refine ⟨c, st4, R, rfl, hsp4.1, hm4, ?_⟩
                      rw [ite_eq_right (by
                        have heq42 : st4.core = st2.core := by
                          rw [fullCoreState_agrees_with_scratch hcore4,
                              fullCoreState_agrees_with_scratch hcore3]
                        rw [heq42, hcv2]
                        have hvn : (BitVec.setWidth 32 v).toNat = v.toNat := by
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                        omega)]
                      dsimp only
                      intro fl5 un5 m5 hfl5 hm5
                      let st5 : FullState :=
                        { st4 with core := { st4.core with flags := fl5, unassigned := un5 } }
                      change (FullMem c st5 ⋆ R) m5 at hm5
                      subst_steps
                      let st6 : FullState :=
                        { st5 with scratch := { st5.scratch with
                            subst_cnt := st5.scratch.subst_cnt + 1#64 } }
                      have hsp5 : FullSparseInvW c F0 F_cur st5 :=
                        fullSparseInvW_afterSetInactive hsp4 hfl5
                      have hsp6 : FullSparseInvW c F0 F_cur st6 :=
                        ⟨⟨hsp5.1.core_ok, { hsp5.1.scratch_ok with }⟩,
                         hsp5.2.1, hsp5.2.2.1, FullArenaVarsNodup.of_arena_eq rfl rfl hsp5.2.2.2.1,
                         ⟨fun i hi => hsp5.2.2.2.2.1.1 i hi, hsp5.2.2.2.2.1.2⟩,
                         hsp5.2.2.2.2.2⟩
                      have heq34 : st4.core = st2.core := by
                        rw [fullCoreState_agrees_with_scratch hcore4,
                            fullCoreState_agrees_with_scratch hcore3]
                      have hrepr6 : FullReprEquiv F_cur st6 := by
                        intro l hl; dsimp only [st6, st5] at hl ⊢
                        rw [heq34] at hl ⊢; exact hrepr2 l hl
                      exact hNext () _ ⟨st6, hsp6, by simp [st6, st5, heq34, hcv2],
                        by simp [st6, st5, heq34, hl02], by simp [st6, st5, heq34, hfl2],
                        hrepr6, by dsimp only [st6, st5]; assumption⟩
                    · -- `else`: revert `repr[lit] = lit; repr[lit ^ 1] = lit ^ 1`
                      have hlit1_64 :
                          (BitVec.setWidth 64
                            ((BitVec.setWidth 32 (v <<< 1#64)) ^^^ 1#32)).toNat <
                            2 * c.max_vars := by
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
                      subst_steps
                      have hset_lt :
                          (BitVec.setWidth 64
                            (BitVec.setWidth 32 (v <<< 1#64) ^^^ 1#32)).toNat <
                            ({ st2 with core := { st2.core with
                                repr := st2.core.repr.set
                                  (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64))).toNat
                                  (BitVec.setWidth 32 (v <<< 1#64)) } } :
                              FullState).core.repr.length := by
                        simp only [List.length_set, hrp_l]; exact hlit1_64
                      subst_steps
                      let lit32 := BitVec.setWidth 32 (v <<< 1#64)
                      let st3 : FullState :=
                        { st2 with core := { st2.core with
                            repr := (st2.core.repr.set
                              (BitVec.setWidth 64 lit32).toNat lit32).set
                              (BitVec.setWidth 64 (lit32 ^^^ 1#32)).toNat (lit32 ^^^ 1#32) } }
                      have hset1_eq : (BitVec.setWidth 64 lit32).toNat = lit32.toNat := by
                        dsimp only [lit32]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      have hset2_eq :
                          (BitVec.setWidth 64 (lit32 ^^^ 1#32)).toNat =
                            (lit32 ^^^ 1#32).toNat := by
                        dsimp only [lit32]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      have hsp3 : FullSparseInvW c F0 F_cur st3 :=
                        ⟨⟨{ hcl2 with repr_len := by simp [st3, hrp_l] }, hsl2⟩,
                         { hsp2.2.1 with
                           arena := { hsp2.2.1.arena with len_ok := hsp2.2.1.arena.len_ok }
                           watches := hsp2.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                             (fun _ hr => hr) },
                         hsp2.2.2.1, FullArenaVarsNodup.of_arena_eq rfl rfl hsp2.2.2.2.1,
                         hsp2.2.2.2.2.1, hsp2.2.2.2.2.2⟩
                      have hrepr3 : FullReprEquiv F_cur st3 := by
                        intro l hl; dsimp only [st3] at hl ⊢
                        rw [hset1_eq, hset2_eq]
                        by_cases hl1 : l = (lit32 ^^^ 1#32).toNat
                        · subst hl1
                          rw [List.getElem?_set_self (by simp only [List.length_set, hrp_l]; omega),
                            Option.getD_some]
                          have hrefl := LitEquiv.refl (cnfOfClauses F_cur) (lit32 ^^^ 1#32).toNat
                          exact ⟨by omega, hrefl.2, hrefl.1⟩
                        · rw [List.getElem?_set_ne (Ne.symm hl1)]
                          by_cases hl0' : l = lit32.toNat
                          · subst hl0'
                            rw [List.getElem?_set_self (by omega), Option.getD_some]
                            have hrefl := LitEquiv.refl (cnfOfClauses F_cur) lit32.toNat
                            exact ⟨by omega, hrefl.2, hrefl.1⟩
                          · rw [List.getElem?_set_ne (Ne.symm hl0')]; exact hrepr2 l hl
                      exact hNext () _ ⟨st3, hsp3, hcv2, hl02, hfl2, hrepr3,
                        by dsimp only [st3, lit32]; assumption⟩
                  · -- `rep == lit`: skip
                    subst_steps
                    exact hNext () m2 ⟨st2, hsp2, hcv2, hl02, hfl2, hrepr2, hm2⟩
                · -- inactive `v`: skip
                  subst_steps
                  exact hNext () m2 ⟨st2, hsp2, hcv2, hl02, hfl2, hrepr2, hm2⟩
            · -- Exit Loop 2: return `true`
              subst_steps
              exact hQ true st2 m2 hsp2 hl02 hcv2 (by rw [hfl2]; exact hfuel1') hrepr2
                (fun h => by cases h) hm2

theorem full_subst_elim_vars_wp (Γ : Env)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hProp : ∀ args m Q X, fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hExtPush2 : ∀ args m Q X, fullExtendPush2Spec args m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] args m Q X)
    (hSetInact : ∀ args m Q X, fullSetInactiveSpec args m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullSubstElimVarsSpec args m Q X →
      Func.wp Γ full_subst_elim_vars_body args m Q X :=
  full_subst_elim_vars_del_wp Γ hAddUnit
    (fun a m Q X h => hProp a m Q X (fullPropagateSpec_of_del h)) hExtPush2 hSetInact

end LeanQbe.T.Examples.Kissat.Full
