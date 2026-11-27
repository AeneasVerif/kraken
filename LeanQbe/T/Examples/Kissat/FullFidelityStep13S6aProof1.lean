module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullM7V2Robust
public import LeanQbe.T.Examples.Kissat.FullM6CongSubst
import LeanQbe.T.Examples.Kissat.FullSubstLemmas1
import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof0b
import LeanQbe.T.Examples.Kissat.FullFidelityStep12ProofPurgeDel
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Step 13 Unchanged-Caller Parametric Lifts (`Proof1`)

Proves callee-parametric `(Γ : Env)` Step-13 `Func.wp` lift theorems for:
1. `full_subst_elim_vars_step13_wp`
   (`Full.full_subst_elim_vars_body` -> `step13SubstElimVarsM6Spec`)
2. `full_substitute_step13_wp` (`Full.full_substitute_body` -> `step13SubstituteM6Spec`)
3. `full_reduce_purge_c0_step13_wp` (`FullM7V2Robust.full_reduce_purge_c0_body` ->
   `step13ReducePurgeC0M6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullSubstHelpers
open LeanQbe.T.Examples.Kissat.Full.FullReduceHelpers
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch

open scoped FullArenaTactics FullSubstTactics FullReduceTactics

local elab "s6a_to_jnz" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

/-! ## 1. Shared M6Hdr + Step13 Invariant Bridges -/

private theorem s6a_fullSparseInvW_of_bcp13 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64}
    {wvec' arena' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch} :
    let s' : FullState :=
      { core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
          confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
    FullArenaPermEq s.core s'.core →
    FullProbeScratchPres { core := s.core, scratch :=
      { s.scratch with
        search_ticks := sc'.search_ticks, phases := sc'.phases,
        wsort := sc'.wsort, delayed := sc'.delayed } } s' →
    FullSparseInvW c F0 F_cur s' := by
  intro s' hlen' hw' hperm hsc
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hperm.2.1
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    obtain ⟨_, hgb, hpm⟩ := hperm.2.2 r hr
    change fullArenaClauseGarbCore s'.core r = false at hng; rw [hgb] at hng
    exact (hsp.2.2.2.1 r hr hng).perm (hpm.map (· / 2)).symm
  have hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s' := fun r hr => by
    change r ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  have hext : FullExtScratchOk c s' := hsp.2.2.2.2.1.of_pres hsc.1 hrefs
  exact ⟨hlen', hw', hsp.2.2.1, hnd', hext, hsp.2.2.2.2.2⟩

private theorem s6a_watchSliceOk_congr_core {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hcv : k'.cur_vars = k.cur_vars) (hw : k'.wstk = k.wstk)
    (hal : k'.arena_len = k.arena_len) (ha : k'.arena = k.arena) :
    ∀ {lit p rem}, WatchSliceOk F_cur k lit p rem → WatchSliceOk F_cur k' lit p rem := by
  intro lit p rem h
  induction h with
  | empty => exact .empty
  | bin h0 h1 h2 h3 h4 _ ih => exact .bin (hw ▸ h0) h1 h2 (hcv ▸ h3) h4 ih
  | large h0 h1 h2 h3 h4 _ ih =>
    exact .large (hw ▸ h0) (hw ▸ h1) h2 h3
      (by unfold fullArenaClauseRefsCore; rw [hal, ha]; exact h4) ih

private theorem s6a_denseWatchSliceOk_congr_core {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hcv : k'.cur_vars = k.cur_vars) (hw : k'.wstk = k.wstk)
    (hal : k'.arena_len = k.arena_len) (ha : k'.arena = k.arena) :
    ∀ {lit p rem},
      DenseWatchSliceOk F_cur k lit p rem → DenseWatchSliceOk F_cur k' lit p rem := by
  intro lit p rem h
  induction h with
  | empty => exact .empty
  | bin h0 h1 h2 h3 h4 _ ih => exact .bin (hw ▸ h0) h1 h2 (hcv ▸ h3) h4 ih
  | occ h0 h1 h2 h3 h4 h5 _ ih =>
    exact .occ (hw ▸ h0) (hw ▸ h1) h2 h3 h4
      (by unfold fullArenaClauseRefsCore; rw [hal, ha]; exact h5) ih

private theorem s6a_fullWitnessInv_of_fields {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (fl' rp' : List (BitVec 32)) (unass' unfl' : BitVec 64) :
    FullWitnessInv c F0 F_cur
      { k with flags := fl', repr := rp', unassigned := unass', unflushed := unfl' } := by
  let k' : FullCoreState :=
    { k with flags := fl', repr := rp', unassigned := unass', unflushed := unfl' }
  have har : FullArenaClausesInv c F_cur k' :=
    ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt, hw.arena.entails⟩
  have hwt : ModeWatchesInv F_cur k' := by
    by_cases hdm : k.dense_mode = 0#64
    · have hdm' : k'.dense_mode = 0#64 := hdm
      have hw0 := hw.watches; unfold ModeWatchesInv at hw0 ⊢
      simp only [hdm, ↓reduceIte] at hw0; simp only [hdm', ↓reduceIte]
      exact ⟨⟨hw0.layout.bounds, hw0.layout.pos_off, hw0.layout.disjoint, hw0.layout.no_sentinel⟩,
        fun l hl => s6a_watchSliceOk_congr_core (k := k) (k' := k')
          rfl rfl rfl rfl (hw0.slices l hl)⟩
    · have hdm' : k'.dense_mode ≠ 0#64 := hdm
      have hw0 := hw.watches; unfold ModeWatchesInv at hw0 ⊢
      simp only [hdm, ↓reduceIte] at hw0; simp only [hdm', ↓reduceIte]
      exact ⟨⟨hw0.layout.bounds, hw0.layout.pos_off, hw0.layout.disjoint, hw0.layout.no_sentinel⟩,
        fun l hl => s6a_denseWatchSliceOk_congr_core (k := k) (k' := k')
          rfl rfl rfl rfl (hw0.slices l hl)⟩
  exact ⟨hw.ext_sound, hw.inconsistent_sound, har, hwt, hw.cur_level_le, hw.trail_lits_lt,
    hw.trail_vars_nodup, hw.vals_domain, hw.vals_true_iff, hw.vals_false_iff, hw.lvl_le,
    hw.dec_earliest, hw.levels_inhabited, hw.level0_sound, hw.trail_pos_inv,
    hw.level0_rsn_none, hw.frame_trail_lt, hw.frame_trail_mono, hw.frame_trail_before_lt,
    hw.frame_dec_lt, hw.reason_inv, hw.reason_lit_mem⟩

private theorem s6a_fullSparseInvW_setInact13 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {flags' qp' qn' qs' hp' ps' : List (BitVec 32)}
    {unass' qsi' qss' qf' ql' : BitVec 64} {hl' : Nat} :
    let s' : FullState :=
      { core := { s.core with flags := flags', unassigned := unass' }
        scratch := { s.scratch with
          heap_len := hl', q_first := qf', q_last := ql', q_search_idx := qsi',
          q_search_stamp := qss', heap := hp', pos := ps',
          q_prev := qp', q_next := qn', q_stamp := qs' } }
    s'.LengthsOk c → FullSparseInvW c F0 F_cur s' := by
  intro s' hlen'
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => hsp.2.2.2.1 r hr hng
  have hw' := s6a_fullWitnessInv_of_fields hsp.2.1 flags' s.core.repr unass' s.core.unflushed
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩
  exact ⟨hlen', hw', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩

private theorem s6a_fullSparseInvW_of_sweep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hnd' : FullArenaVarsNodup s') (hll' : FullLastLearnedWf s')
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) :
    FullSparseInvW c F0 F_cur s' :=
  ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩,
    hnd', ⟨hll', hext' ▸ hsp.2.2.2.2.1.2⟩, hdm.trans hsp.2.2.2.2.2⟩

private theorem s6a_fullSparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') :
    FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ hr
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 r hr0
    exact (hsp.2.2.2.1 r hr0 (hgb.symm.trans hng)).perm (hp.symm.map (· / 2))
  · exact hsp.2.2.2.2.1.of_pres hpres fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr

private theorem s6a_entails_taut {f : CNF Nat} {l : Nat} :
    f.EntailsClause (cnfClause [l, l ^^^ 1]) := by
  rw [CNF.entails_clause_def]
  intro τ _
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false]
  by_cases hp : l % 2 = 0
  · have hle : l = 2 * (l / 2) := by omega
    have hx : l ^^^ 1 = 2 * (l / 2) + 1 :=
      (congrArg (· ^^^ 1) hle).trans (nat_two_mul_xor_one (l / 2))
    rw [hx, hle]
    simp only [evalLitVal, litVar, litSign, Nat.mul_mod_right,
      Nat.mul_div_right _ (by decide : 0 < 2), Nat.mul_add_mod,
      Nat.mul_add_div (by decide : 0 < 2)]
    cases τ (l / 2) <;> decide
  · have hlo : l = 2 * (l / 2) + 1 := by omega
    have h0 := nat_two_mul_xor_one (l / 2)
    have hx : l ^^^ 1 = 2 * (l / 2) := by
      have h1 : (2 * (l / 2) + 1) ^^^ 1 = 2 * (l / 2) := by
        rw [← h0, Nat.xor_assoc]; simp
      exact (congrArg (· ^^^ 1) hlo).trans h1
    rw [hx, hlo]
    simp only [evalLitVal, litVar, litSign, Nat.mul_mod_right,
      Nat.mul_div_right _ (by decide : 0 < 2), Nat.mul_add_mod,
      Nat.mul_add_div (by decide : 0 < 2)]
    cases τ (l / 2) <;> decide

private theorem s6a_fullReprEquiv_reset_pair {F_cur : List (List Nat)} {s : FullState}
    (hr : FullReprEquiv F_cur s) (hrep_len : 2 * s.core.cur_vars ≤ s.core.repr.length)
    {v : Nat} (hv : v < s.core.cur_vars) (hlim : 2 * s.core.cur_vars < 2 ^ 32) :
    let r' := (s.core.repr.set (2 * v) (BitVec.ofNat 32 (2 * v))).set
      (2 * v + 1) (BitVec.ofNat 32 (2 * v + 1))
    FullReprEquiv F_cur { s with core := { s.core with repr := r' } } := by
  intro r' l hl
  have hlt1 : 2 * v < s.core.repr.length := by omega
  have hlt2 : 2 * v + 1 < (s.core.repr.set (2 * v) (BitVec.ofNat 32 (2 * v))).length := by
    rw [List.length_set]; omega
  have hxv0 : (2 * v) ^^^ 1 = 2 * v + 1 := nat_two_mul_xor_one v
  have hxv1 : (2 * v + 1) ^^^ 1 = 2 * v := by
    rw [← hxv0, Nat.xor_assoc]; simp
  dsimp only
  by_cases h1 : l = 2 * v + 1
  · subst h1
    have hget : r'[2 * v + 1]?.getD 0#32 = BitVec.ofNat 32 (2 * v + 1) := by
      dsimp only [r']; rw [List.getElem?_set_self hlt2, Option.getD_some]
    have hto : (BitVec.ofNat 32 (2 * v + 1)).toNat = 2 * v + 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
    rw [hget, hto]
    refine ⟨hl, ?_, ?_⟩
    · simpa [hxv0, hxv1] using (s6a_entails_taut (f := cnfOfClauses F_cur) (l := 2 * v + 1))
    · simpa [hxv0, hxv1] using (s6a_entails_taut (f := cnfOfClauses F_cur) (l := 2 * v))
  · by_cases h0 : l = 2 * v
    · subst h0
      have hget : r'[2 * v]?.getD 0#32 = BitVec.ofNat 32 (2 * v) := by
        dsimp only [r']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hlt1, Option.getD_some]
      have hto : (BitVec.ofNat 32 (2 * v)).toNat = 2 * v := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
      rw [hget, hto]
      refine ⟨hl, ?_, ?_⟩
      · simpa [hxv0, hxv1] using (s6a_entails_taut (f := cnfOfClauses F_cur) (l := 2 * v))
      · simpa [hxv0, hxv1] using (s6a_entails_taut (f := cnfOfClauses F_cur) (l := 2 * v + 1))
    · have hget : r'[l]? = s.core.repr[l]? := by
        dsimp only [r']
        rw [List.getElem?_set_ne (Ne.symm h1), List.getElem?_set_ne (Ne.symm h0)]
      rw [hget]; exact hr l hl

private theorem s6a_fullSparseInvW_repr_set2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hrep_len : 2 * c.max_vars = s.core.repr.length)
    {v : Nat} (_hv : v < s.core.cur_vars) :
    let r' := (s.core.repr.set (2 * v) (BitVec.ofNat 32 (2 * v))).set
      (2 * v + 1) (BitVec.ofNat 32 (2 * v + 1))
    FullSparseInvW c F0 F_cur { s with core := { s.core with repr := r' } } := by
  intro r'
  have hlen : ({ s with core := { s.core with repr := r' } } : FullState).LengthsOk c :=
    ⟨{ hsp.1.core_ok with repr_len := by dsimp only [r']; simp [← hrep_len] }, hsp.1.scratch_ok⟩
  have hw := s6a_fullWitnessInv_of_fields hsp.2.1 s.core.flags r' s.core.unassigned
    s.core.unflushed
  have hnd : FullArenaVarsNodup { s with core := { s.core with repr := r' } } :=
    fun r hr hng => hsp.2.2.2.1 r hr hng
  exact ⟨hlen, hw, hsp.2.2.1, hnd,
    ⟨fun i hi => hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩

private structure S6aPurgeStateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop where
  sparse : FullSparseInv c F0 s'
  witness : FullWitnessInv c F0 F_cur s'.core
  cl_le : s'.core.cur_level ≤ s.core.cur_level
  fuel_le : s'.core.fuel.toNat ≤ s.core.fuel.toNat
  cv_eq : s'.core.cur_vars = s.core.cur_vars
  tmp_eq : s'.core.tmp = s.core.tmp
  tl_eq : s'.core.tmp_len = s.core.tmp_len
  dm0 : s'.core.dense_mode = 0#64
  oom_pres : s.core.oom = 0#64 → s'.core.oom = 0#64
  mrk_zero : FullMrkZero c s'
  lm_clr : ∀ l < 2 * c.max_vars, s'.core.lit_mark[l]?.getD 0#8 = 0#8
  ll_wf : FullLastLearnedWf s'
  ext_eq : s'.scratch.extend_len = s.scratch.extend_len
  ws2_eq : s'.scratch.work_stk2 = s.scratch.work_stk2
  pos_pres : 0 < s'.core.cur_level →
    s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
    s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
    s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end

private theorem s6a_purgeStateOk_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) : S6aPurgeStateOk c F0 F_cur s s :=
  ⟨hsp.toSparse, hsp.2.1, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, hsp.2.2.2.2.2, id,
   hsp.2.2.1.1, hsp.2.2.1.2, hsp.2.2.2.2.1.1, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem s6a_purgeStateOk_trans {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st st' : FullState} (h1 : S6aPurgeStateOk c F0 F_cur s st)
    (h2 : S6aPurgeStateOk c F0 F_cur st st') : S6aPurgeStateOk c F0 F_cur s st' :=
  ⟨h2.sparse, h2.witness, Nat.le_trans h2.cl_le h1.cl_le, Nat.le_trans h2.fuel_le h1.fuel_le,
   h2.cv_eq.trans h1.cv_eq, h2.tmp_eq.trans h1.tmp_eq, h2.tl_eq.trans h1.tl_eq, h2.dm0,
   fun h => h2.oom_pres (h1.oom_pres h), h2.mrk_zero, h2.lm_clr, h2.ll_wf,
   h2.ext_eq.trans h1.ext_eq, h2.ws2_eq.trans h1.ws2_eq,
   fun hp => by
     obtain ⟨hc1, hv1, hl1, ht1, htp1, hte1⟩ := h2.pos_pres hp
     obtain ⟨hc0, hv0, hl0, ht0, htp0, hte0⟩ := h1.pos_pres (hc1 ▸ hp)
     exact ⟨hc1.trans hc0, hv1.trans hv0, hl1.trans hl0, ht1.trans ht0,
       htp1.trans htp0, hte1.trans hte0⟩⟩

private theorem s6a_purgeStateOk_mark_reasons {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s2 : FullState} {ar' : List (BitVec 32)}
    (h2 : S6aPurgeStateOk c F0 F_cur s s2)
    (hlen' : ({ s2 with core := { s2.core with arena := ar' } } : FullState).LengthsOk c)
    (hrefs : fullArenaClauseRefs { s2 with core := { s2.core with arena := ar' } } =
      fullArenaClauseRefs s2)
    (hper : ∀ r ∈ fullArenaClauseRefs s2,
      fullArenaClauseSize { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseSize s2 r ∧
      fullArenaClauseGarb { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseGarb s2 r ∧
      fullArenaClauseLits { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseLits s2 r)
    (hw' : FullWitnessInv c F0 F_cur { s2.core with arena := ar' }) :
    S6aPurgeStateOk c F0 F_cur s { s2 with core := { s2.core with arena := ar' } } := by
  let s3 : FullState := { s2 with core := { s2.core with arena := ar' } }
  have hrefs3 : fullArenaClauseRefs s3 = fullArenaClauseRefs s2 := hrefs
  have hnd : FullArenaVarsNodup s3 := fun r hr hng => by
    rw [hrefs3] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
    exact h2.sparse.2.2.1 r hr hng
  have hll : FullLastLearnedWf s3 := fun i hi => by
    change s2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (s2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s3
    rw [hrefs3]; exact h2.ll_wf i hi
  exact s6a_purgeStateOk_trans h2
    ⟨⟨⟨hlen', ⟨F_cur, hw'⟩⟩, h2.sparse.2.1, hnd, ⟨hll, h2.sparse.2.2.2.1.2⟩, h2.dm0⟩,
     hw', Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, h2.dm0, id, h2.mrk_zero, h2.lm_clr,
     hll, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem s6a_purgeStateOk_backtrack0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s0 : FullState} (h0 : S6aPurgeStateOk c F0 F_cur s s0)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch} :
    let sB : FullState := { s0 with
      core := { s0.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
      scratch := sc' }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    sc'.last_learned = s0.scratch.last_learned →
    sc'.extend_len = s0.scratch.extend_len →
    sc'.work_stk2 = s0.scratch.work_stk2 →
    S6aPurgeStateOk c F0 F_cur s sB := by
  intro sB hlen' hw' hll' hext' hws2'
  have hllB : FullLastLearnedWf sB := fun i hi => by
    change sc'.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s0
    rw [hll']; exact h0.ll_wf i hi
  exact s6a_purgeStateOk_trans h0
    ⟨⟨⟨hlen', ⟨F_cur, hw'⟩⟩, h0.sparse.2.1, h0.sparse.2.2.1,
      ⟨hllB, hext' ▸ h0.sparse.2.2.2.1.2⟩, h0.dm0⟩,
     hw', Nat.zero_le _, Nat.le_refl _, rfl, rfl, rfl, h0.dm0, id, h0.mrk_zero, h0.lm_clr,
     hllB, hext', hws2', fun hpos => by cases hpos⟩

private theorem s6a_purgeStateOk_bcp13 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st : FullState} (hst : S6aPurgeStateOk c F0 F_cur s st)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64}
    {wvec' arena' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch} :
    let s' : FullState :=
      { core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
          confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
    FullArenaPermEq st.core s'.core →
    FullProbeScratchPres { core := st.core, scratch :=
      { st.scratch with
        search_ticks := sc'.search_ticks, phases := sc'.phases,
        wsort := sc'.wsort, delayed := sc'.delayed } } s' →
    fuel'.toNat ≤ st.core.fuel.toNat → (st.core.oom = 0#64 → oom' = 0#64) →
    (0 < s'.core.cur_level →
      s'.core.cur_level = st.core.cur_level ∧ s'.core.vals = st.core.vals ∧
      s'.core.lvl = st.core.lvl ∧ s'.core.trl = st.core.trl ∧
      s'.core.trail_pos = st.core.trail_pos ∧ s'.core.trail_end = st.core.trail_end) →
    S6aPurgeStateOk c F0 F_cur s s' := by
  intro s' hlen' hw' hperm hsc hfl' hoom' hpos'
  have hsp_w : FullSparseInvW c F0 F_cur st :=
    ⟨hst.sparse.1.lengths, hst.witness, hst.sparse.2.1, hst.sparse.2.2.1,
     hst.sparse.2.2.2.1, hst.dm0⟩
  have hsp' := s6a_fullSparseInvW_of_bcp13 hsp_w hlen' hw' hperm hsc
  exact s6a_purgeStateOk_trans hst
    ⟨hsp'.toSparse, hw', Nat.le_refl _, hfl', rfl, rfl, rfl, hsp'.2.2.2.2.2, hoom',
     hsp'.2.2.1.1, hsp'.2.2.1.2, hsp'.2.2.2.2.1.1, hsc.1.2, hsc.2.2.1, hpos'⟩

private theorem s6a_purgeStateOk_sweep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st : FullState} (hst : S6aPurgeStateOk c F0 F_cur s st)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} :
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core →
    FullArenaVarsNodup sA → FullLastLearnedWf sA →
    sc'.extend_len = st.scratch.extend_len → sc'.work_stk2 = st.scratch.work_stk2 →
    (st.core.oom = 0#64 → oom' = 0#64) →
    (0 < st.core.cur_level →
      vals' = st.core.vals ∧ lvl' = st.core.lvl ∧ trl' = st.core.trl ∧
      tp' = st.core.trail_pos ∧ te' = st.core.trail_end) →
    S6aPurgeStateOk c F0 F_cur s sA := by
  intro sA hlenA hwA hndA hllA hextA hws2A hoomA hposA
  exact s6a_purgeStateOk_trans hst
    ⟨⟨⟨hlenA, ⟨F_cur, hwA⟩⟩, hst.sparse.2.1, hndA,
      ⟨hllA, hextA ▸ hst.sparse.2.2.2.1.2⟩, hst.dm0⟩,
     hwA, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, hst.dm0, hoomA, hst.mrk_zero, hst.lm_clr,
     hllA, hextA, hws2A, fun hp => by
      obtain ⟨hv, hl, ht, htp, hte⟩ := hposA hp
      exact ⟨rfl, hv, hl, ht, htp, hte⟩⟩

private theorem s6a_purgeStateOk_mark_garb {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sL : FullState} {cr : Nat} {agN : BitVec 64}
    (hokL : S6aPurgeStateOk c F0 F_cur s sL) (hrmL : FullReasonsMarked sL)
    (hcr_mem : cr ∈ fullArenaClauseRefs sL)
    (hcr_norsn : (fullArenaHdr sL cr &&& 0x00200000#32) = 0#32)
    (hcr_ar : cr < sL.core.arena.length) :
    let sM : FullState :=
      { sL with core := { sL.core with
        arena := sL.core.arena.set cr (sL.core.arena[cr]'hcr_ar ||| 0x00080000#32)
        arena_garbage := agN } }
    S6aPurgeStateOk c F0 F_cur s sM ∧ FullReasonsMarked sM := by
  intro sM
  have hhdr_eq : sL.core.arena[cr]'hcr_ar = fullArenaHdr sL cr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hnonact := FullDenseWatchHelpers.markGarb_nonact_of_reasonsMarked hokL.witness hrmL hcr_norsn
  have hmg := FullDenseWatchHelpers.markGarb_preserves_fullWitnessInv
    hokL.sparse.1.lengths hokL.witness hcr_mem agN hnonact
  rw [← hhdr_eq] at hmg
  obtain ⟨hlenM, hrefsM, hwM, hrsnM, hndM⟩ := hmg
  have hndM' : FullArenaVarsNodup sM := hndM fun r hr hng => hokL.sparse.2.2.1 r hr hng
  have hllM : FullLastLearnedWf sM := fun j hj => by
    change sL.scratch.last_learned[j]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sL.scratch.last_learned[j]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sM
    rw [hrefsM]; exact hokL.ll_wf j hj
  have hrmM : FullReasonsMarked sM := fun idx hidx hlp hlg => by
    have hne0 : sL.core.rsns[(sL.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      intro heq; rw [heq] at hlg; revert hlg; decide
    have hrs := hokL.witness.reason_inv idx hidx hne0
    have hbf : ¬ (sL.core.rsns[(sL.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
    rw [ite_eq_right hbf] at hrs
    rw [hrsnM _ hrs.1]; exact hrmL idx hidx hlp hlg
  exact ⟨s6a_purgeStateOk_trans hokL
    ⟨⟨⟨hlenM, ⟨F_cur, hwM⟩⟩, hokL.sparse.2.1, hndM',
      ⟨hllM, hokL.sparse.2.2.2.1.2⟩, hokL.dm0⟩,
     hwM, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, hokL.dm0, id, hokL.mrk_zero, hokL.lm_clr,
     hllM, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, hrmM⟩

private theorem s6a_bv32_norsn_of_mask {x : BitVec 32} (hx : (x &&& 0x00280000#32) = 0#32) :
    (x &&& 0x00200000#32) = 0#32 := by
  have h21 : (x &&& 0x00280000#32)[21] = false := by rw [hx]; decide
  have hb : (0x00280000#32 : BitVec 32)[21] = true := by decide
  simp only [BitVec.getElem_and, hb, Bool.and_true] at h21
  ext i hi; by_cases hi21 : i = 21
  · subst hi21; simp [h21]
  · simp [BitVec.getElem_and, show (0x00200000#32 : BitVec 32)[i] = false from by
      revert hi21; clear h21 hx; revert i; decide]

/-! ## 2. `full_subst_elim_vars` Step-13 Lift -/

/-- Step-13 callee-parametric WP lift for `Full.full_subst_elim_vars_body` to
`step13SubstElimVarsM6Spec` using `step13BcpM6Spec` and `step13SetInactiveSpec`. -/
theorem full_subst_elim_vars_step13_wp (Γ : Env)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hProp : ∀ args m Q X, step13BcpM6Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hExtPush2 : ∀ args m Q X, fullExtendPush2Spec args m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] args m Q X)
    (hSetInact : ∀ args m Q X, step13SetInactiveSpec args m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, step13SubstElimVarsM6Spec args m Q X →
      Func.wp Γ full_subst_elim_vars_body args m Q X := by
  rintro ⟨h, ucnt, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, ext0, s0, R, rfl, hinv0, hl0, hrepr0, huc_le, hus0, hm0, hQ⟩
  have _hx := c.hmaxv; unfold dimacsBound at _hx
  unfold Func.wp full_subst_elim_vars_body
  have hsp0 := hinv0.sparseW
  have hm0_f := fullM6HdrMem_focus_full hm0
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64])
    (fun (i, ()) ml => ∃ st : FullState,
      FullSparseInvW c F0 F_cur st ∧ st.core.cur_level = 0 ∧
      st.core.cur_vars = s0.core.cur_vars ∧ st.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      FullReprEquiv F_cur st ∧ i.toNat ≤ ucnt.toNat ∧
      st.scratch.shrink_stk = s0.scratch.shrink_stk ∧
      (FullMem c st ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) ml)
    (fun (i, ()) _ => ucnt.toNat - i.toNat)
    ?_ ?_
  · exact fun J1 hJ1 => hJ1 (0#64, ()) m
      ⟨s0, hsp0, hl0, rfl, Nat.le_refl _, hrepr0, Nat.zero_le _, rfl, hm0_f⟩
  rintro J1 ⟨i, ⟨⟩⟩ ml ⟨st, hsp, hl, hcv, hfl, hrepr, hi_le, hss, hml⟩ ih1
  have hi_lt' : i.toNat ≤ c.max_vars := Nat.le_trans hi_le huc_le
  have hstk_len_eq : st.scratch.shrink_stk.length = c.max_vars := hsp.1.scratch_ok.shrink_stk_len
  c0_hsteps_nogrp
  c0_hsplit
  · have hi_lt : i.toNat < ucnt.toNat := hc
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    have hstk_len : i.toNat < st.scratch.shrink_stk.length := by
      rw [hsp.1.scratch_ok.shrink_stk_len]; omega
    c0_hsteps_nogrp
    c0_call hAddUnit
    refine ⟨c, F0, F_cur, st, _, rfl, hsp.1, hsp.2.1, fun hlt => ?_, hml, ?_⟩
    · have hget : st.scratch.shrink_stk[i.toNat]?.getD 0#32 =
          st.scratch.shrink_stk[i.toNat]'hstk_len := by
        rw [List.getElem?_eq_getElem hstk_len, Option.getD_some]
      rw [← hget, hss]; exact (hus0 i.toNat hi_lt).2
    intro ok1 vals1 fl1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 unfl1 inc1
      ph1 ta1 ba1 pt1 pb1 hp1 ps1 hl1 qsi1 qss1 m1 _ hlen1 hw1 hcl1 _ hfail1 hm1_f
    let st1 : FullState :=
      { core := { st.core with
          vals := vals1, flags := fl1, lvl := lvl1, rsns := rsns1, trl := trl1,
          trail_pos := tp1, trail_end := te1, propagated := prop1, cur_level := cl1,
          unassigned := unass1, unflushed := unfl1, inconsistent := inc1 }
        scratch := { st.scratch with
          phases := ph1, target_assigned := ta1, best_assigned := ba1,
          phases_target := pt1, phases_best := pb1, heap := hp1, pos := ps1,
          heap_len := hl1, q_search_idx := qsi1, q_search_stamp := qss1 } }
    have hsp1 := fullSparseInvW_afterAddUnit hsp hlen1 hw1
    c0_hsteps_nogrp
    c0_hsplit
    · exact ih1 (i + 1#64, ()) m1 (by dsimp only; rw [hi1]; omega)
        ⟨st1, hsp1, hcl1, hcv, hfl, hrepr, by rw [hi1]; omega, hss, hm1_f⟩
    · exact hQ false ext0 st1 m1 (FullM6HdrInvW.mk_inv hinv0.cfgOk hinv0.extOk hsp1) hcl1 hcv hfl
        hrepr
        (fun _ => by
          have hlt_lit :
              (st.scratch.shrink_stk[i.toNat]'hstk_len).toNat < 2 * st.core.cur_vars := by
            have := (hus0 i.toNat hi_lt).1
            rw [← hcv, ← hss, List.getElem?_eq_getElem hstk_len, Option.getD_some] at this
            exact this
          exact (hfail1 (by cases ok1 <;> first | rfl | exact absurd hc (by decide))).elim
            (fun hle => absurd hlt_lit (by omega)) (·.1))
        (fullM6HdrMem_unfocus_full hm1_f)
  · c0_call hProp
    refine ⟨c, F0, F_cur, ext0, st, R, rfl, hinv0.cfgOk, hinv0.extOk, hsp.1, hsp.2.1,
      hsp.2.2.2.2.2, fullM6HdrMem_unfocus_full hml, ?_⟩
    intro pr ext1 vals1 fl1 lvl1 rsns1 trl1 tp1 te1 prop1 unass1 unfl1 wvec1 arena1 wstk1
      wlen1 wu1 fuel1 ctype1 cref1 c01 c11 oom1 sc1 m1 _ hext1 _ hlen1 hw1 _ hperm1 hsc1 _ _ _ _
      hfl1 _ _ hpr1 _ _ hm1
    let st1 : FullState :=
      { core := { st.core with
          vals := vals1, flags := fl1, lvl := lvl1, rsns := rsns1, trl := trl1,
          trail_pos := tp1, trail_end := te1, propagated := prop1, unassigned := unass1,
          unflushed := unfl1, wvec := wvec1, arena := arena1, wstk := wstk1,
          wlen := wlen1, wusable := wu1, fuel := fuel1, confl_type := ctype1,
          confl_ref := cref1, confl_lit0 := c01, confl_lit1 := c11, oom := oom1 }
        scratch := sc1 }
    have hsp1 := s6a_fullSparseInvW_of_bcp13 hsp hlen1 hw1 hperm1 hsc1
    have hfl1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hfl1 hfl
    have hrepr1 : FullReprEquiv F_cur st1 := hrepr
    have hm1_f := fullM6HdrMem_focus_full hm1
    c0_hsteps_nogrp
    · exact hQ false ext1 st1 m1 (FullM6HdrInvW.mk_inv hinv0.cfgOk hext1 hsp1) hl hcv hfl1' hrepr1
        (fun _ => level0_unsat_of_conflict_okW hw1 hl (hpr1 hc).2.2)
        (fullM6HdrMem_unfocus_full hm1_f)
    · exact hQ false ext1 st1 m1 (FullM6HdrInvW.mk_inv hinv0.cfgOk hext1 hsp1) hl hcv hfl1'
        hrepr1 (fun _ => hw1.ext_sound.2 (hw1.inconsistent_sound hc))
        (fullM6HdrMem_unfocus_full hm1_f)
    ·   c0_hsteps_nogrp
        refine wp_loop_inv (ts := [i64])
          (fun (v, ()) mv => ∃ stv : FullState,
            FullSparseInvW c F0 F_cur stv ∧ stv.core.cur_level = 0 ∧
            stv.core.cur_vars = s0.core.cur_vars ∧ stv.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
            FullReprEquiv F_cur stv ∧ v.toNat ≤ stv.core.cur_vars ∧
            stv.core.repr.length = 2 * c.max_vars ∧
            (FullMem c stv ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mv)
          (fun (v, ()) _ => st1.core.cur_vars - v.toNat)
          ?_ ?_
        · exact fun J2 hJ2 => hJ2 (0#64, ()) m1
            ⟨st1, hsp1, hl, hcv, hfl1', hrepr1, Nat.zero_le _, hsp1.1.core_ok.repr_len, hm1_f⟩
        rintro J2 ⟨v, ⟨⟩⟩ mv ⟨stv, hspv, hlv, hcvv, hflv, hreprv, hv_le, hrlenv, hmv⟩ ih2
        have hcv_max : stv.core.cur_vars ≤ c.max_vars := hspv.1.core_ok.cur_vars_le
        c0_hsteps_nogrp
        c0_hsplit
        · have hv_lt : v.toNat < stv.core.cur_vars := by
            rw [hcvv, ← hcv]
            exact Nat.lt_of_lt_of_le (by assumption) (Nat.mod_le _ _)
          have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
          have hcv_meas : stv.core.cur_vars = st1.core.cur_vars := hcvv.trans hcv.symm
          have h2v : (v <<< 1#64).toNat = 2 * v.toNat := by
            simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
          have hr_lt : 2 * v.toNat < stv.core.repr.length := by rw [hrlenv]; omega
          have hr1_lt : 2 * v.toNat + 1 < stv.core.repr.length := by rw [hrlenv]; omega
          have hf_lt : v.toNat < stv.core.flags.length := by
            rw [hspv.1.core_ok.flags_len]; omega
          c0_hsteps
          ·   c0_call hExtPush2
              refine ⟨c, stv, _, ⟨rfl, hspv.2.2.2.2.1.2⟩, hspv.1, hmv,
                fun _ st_p1 mp1 hpresp1 hlenp1 hp1 hm_p1 => ?_⟩
              have hsp_p1 := fullSparseInvW_afterExtPush2 hspv hlenp1 hpresp1 hp1.1 hp1.2.1
              c0_hsteps_nogrp
              c0_call hExtPush2
              refine ⟨c, st_p1, _, ⟨rfl, hsp_p1.2.2.2.2.1.2⟩, hsp_p1.1, hm_p1,
                fun _ st_p2 mp2 hpresp2 hlenp2 hp2 hm_p2 => ?_⟩
              have hsp_p2 := fullSparseInvW_afterExtPush2 hsp_p1 hlenp2 hpresp2 hp2.1 hp2.2.1
              have hcore_p2 : st_p2.core = stv.core :=
                (fullCoreState_agrees_with_scratch hpresp2).trans
                  (fullCoreState_agrees_with_scratch hpresp1)
              have hcv_p2 : st_p2.core.cur_vars = stv.core.cur_vars :=
                congrArg FullCoreState.cur_vars hcore_p2
              c0_hsteps_nogrp
              c0_call hSetInact
              have htrunc_v : (v.setWidth 32).toNat = v.toNat := by simp; omega
              refine ⟨c, st_p2, _, rfl, hsp_p2.1, hm_p2, ?_⟩
              simp only [show ¬st_p2.core.cur_vars ≤ (v.setWidth 32).toNat by
                rw [htrunc_v, hcv_p2]; omega, ↓reduceIte]
              intro fl_s unass_s qp_s qn_s qs_s qsi_s qss_s qf_s ql_s hp_s ps_s hl_s m_s
                hlen_s hm_s
              let st_s : FullState :=
                { core := { st_p2.core with flags := fl_s, unassigned := unass_s }
                  scratch := { st_p2.scratch with
                    heap_len := hl_s, q_first := qf_s, q_last := ql_s, q_search_idx := qsi_s,
                    q_search_stamp := qss_s, heap := hp_s, pos := ps_s,
                    q_prev := qp_s, q_next := qn_s, q_stamp := qs_s } }
              have hsp_s := s6a_fullSparseInvW_setInact13 hsp_p2 hlen_s
              have hrepr_p2 : FullReprEquiv F_cur st_p2 := by
                intro l hl
                have := hreprv l (by rw [← hcv_p2]; exact hl)
                change (st_p2.core.repr[l]?.getD 0#32).toNat < 2 * st_p2.core.cur_vars ∧ _
                rw [hcore_p2]; exact this
              have hrep_s : FullReprEquiv F_cur st_s := hrepr_p2
              c0_hsteps
              let st_f : FullState :=
                { st_s with scratch := { st_s.scratch with
                    subst_cnt := st_s.scratch.subst_cnt + 1#64 } }
              have hsp_f : FullSparseInvW c F0 F_cur st_f :=
                ⟨⟨hsp_s.1.core_ok, { hsp_s.1.scratch_ok with }⟩, hsp_s.2⟩
              exact ih2 (v + 1#64, ()) _ (by dsimp only; rw [hv1]; omega)
                ⟨st_f, hsp_f, by dsimp only [st_f, st_s]; rw [hcore_p2]; exact hlv,
                  by dsimp only [st_f, st_s]; rw [hcore_p2]; exact hcvv,
                  by dsimp only [st_f, st_s]; rw [hcore_p2]; exact hflv,
                  hrep_s, by dsimp only [st_f, st_s]; rw [hcore_p2, hv1]; omega,
                  hsp_f.1.core_ok.repr_len, by assumption⟩
          · have hrlen2 : 2 * stv.core.cur_vars ≤ stv.core.repr.length := by
              rw [hrlenv]; omega
            have hrepr_r := s6a_fullReprEquiv_reset_pair hreprv hrlen2 hv_lt (by omega)
            have hsp_r := s6a_fullSparseInvW_repr_set2 hspv hrlenv.symm hv_lt
            have hval0 : BitVec.setWidth 32 (v <<< 1#64) = BitVec.ofNat 32 (2 * v.toNat) := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, h2v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have hidx0 :
                (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64))).toNat = 2 * v.toNat := by
              rw [BitVec.toNat_setWidth, hval0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)]
            have hval1 : BitVec.setWidth 32 (v <<< 1#64) ^^^ 1#32 =
                BitVec.ofNat 32 (2 * v.toNat + 1) := by
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_xor, hval0, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : 2 * v.toNat < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : 2 * v.toNat + 1 < 2 ^ 32),
                nat_two_mul_xor_one]
            have h2v_xor :
                (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64) ^^^ 1#32)).toNat =
                  2 * v.toNat + 1 := by
              rw [BitVec.toNat_setWidth, hval1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)]
            have h2v_xor' :
                (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< OfNat.ofNat 1) ^^^ 1)).toNat =
                  2 * v.toNat + 1 := h2v_xor
            have hrep_set_len :
                (stv.core.repr.set
                  (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< OfNat.ofNat 1))).toNat
                  (BitVec.setWidth 32 (v <<< OfNat.ofNat 1))).length =
                  stv.core.repr.length := List.length_set
            c0_hsteps
            refine ih2 (v + 1#64, ()) _ (by dsimp only; rw [hv1]; omega)
              ⟨_, hsp_r, hlv, hcvv, hflv, hrepr_r, by dsimp only; rw [hv1]; omega,
                hsp_r.1.core_ok.repr_len, ?_⟩
            dsimp only at hm
            have hset32 : BitVec.setWidth 32 (v <<< (1 : Nat)) =
                BitVec.ofNat 32 (2 * BitVec.toNat v) := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
              simp [Nat.mod_eq_of_lt (by omega : BitVec.toNat v * 2 ^ 1 < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : BitVec.toNat v * 2 ^ 1 < 2 ^ 32)]
              omega
            rw [hset32, ← hval0, hidx0, show (1 : BitVec 32) = 1#32 from rfl, h2v_xor, hval1,
              hval0] at hm
            exact hm
          · c0_hsteps
            exact ih2 (v + 1#64, ()) mv (by dsimp only; rw [hv1]; omega)
              ⟨stv, hspv, hlv, hcvv, hflv, hreprv, by rw [hv1]; omega, hrlenv, hmv⟩
          · c0_hsteps
            exact ih2 (v + 1#64, ()) mv (by dsimp only; rw [hv1]; omega)
              ⟨stv, hspv, hlv, hcvv, hflv, hreprv, by rw [hv1]; omega, hrlenv, hmv⟩
        · c0_hsteps_nogrp
          exact hQ true ext1 stv mv (FullM6HdrInvW.mk_inv hinv0.cfgOk hext1 hspv) hlv hcvv hflv
            hreprv (fun h => by cases h) (fullM6HdrMem_unfocus_full hmv)

/-! ## 3. `full_substitute` Step-13 Lift -/

/-- Step-13 callee-parametric WP lift for `Full.full_substitute_body` to
`step13SubstituteM6Spec` using `step13SubstElimVarsM6Spec` and `step13BcpM6Spec`. -/
theorem full_substitute_step13_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hTarjan : ∀ args m Q X, fullTarjanSccSpec args m Q X →
      Γ "full_tarjan_scc" [i64] [i64] args m Q X)
    (hElimVars : ∀ args m Q X, step13SubstElimVarsM6Spec args m Q X →
      Γ "full_subst_elim_vars" [i64, i64] [.bool] args m Q X)
    (hRewriteBins : ∀ args m Q X, fullSubstRewriteBinsSpec args m Q X →
      Γ "full_subst_rewrite_bins" [i64] [.bool] args m Q X)
    (hRewriteAr : ∀ args m Q X, fullSubstRewriteArSpec args m Q X →
      Γ "full_subst_rewrite_ar" [i64] [.bool] args m Q X)
    (hArenaSweep : ∀ args m Q X, fullArenaSweepSpec args m Q X →
      Γ "full_arena_sweep" [i64] [i64] args m Q X)
    (hProp : ∀ args m Q X, step13BcpM6Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, step13SubstituteM6Spec args m Q X →
      Func.wp Γ full_substitute_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext0, s0, R, rfl, hinv0, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hsp0 := hinv0.sparse
  obtain ⟨F_cur0, hw0⟩ := hsp0.exists_witness
  have hcl0 := hsp0.1.lengths.core_ok
  have hclv_lt : s0.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  unfold Func.wp full_substitute_body
  have hm_f := fullM6HdrMem_focus_full hm
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState × List (BitVec 64))
    (fun p m1 => FullM6HdrInv c F0 p.2 p.1 ∧ p.1.core.cur_level = 0 ∧
      p.1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c p.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) p.2 ⋆ R)) m1) ?_ ?_
  · rintro _ ⟨st1, ext1⟩ m1 ⟨hinv1, hl01, hfl1, hm1_f⟩
    dsimp only at hinv1 hl01 hfl1 hm1_f
    c0_hsteps_nogrp
    refine wp_while_break_state (α := BitVec 64 × FullState × List (BitVec 64))
      (β := BitVec 64 × FullState × List (BitVec 64))
      (fun p => (p.1, ()))
      (fun p mb => FullM6HdrInv c F0 p.2.2 p.2.1 ∧ p.2.1.core.cur_level = 0 ∧
        p.2.1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
        (FullMem c p.2.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) p.2.2 ⋆ R)) mb)
      (fun p => (p.1, ()))
      (fun p => 4 - p.1.toNat)
      (fun p ml => FullM6HdrInv c F0 p.2.2 p.2.1 ∧ p.2.1.core.cur_level = 0 ∧
        p.2.1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ p.1.toNat ≤ 4 ∧
        (FullMem c p.2.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) p.2.2 ⋆ R)) ml)
      ?_ ?_ ?_
    · rintro _ ⟨_r, stb, extb⟩ mb ⟨hinvb, hl0b, hflb, hmb_f⟩
      c0_hsteps
      exact hQ 1#64 extb stb mb hinvb hl0b hflb (Or.inl rfl) (fun h => by cases h)
        (fullM6HdrMem_unfocus_full hmb_f)
    · rintro B L ⟨round, st, ext⟩ ml hB hL ⟨hinv, hl0_st, hfl_st, hr_le, hml⟩
      dsimp only at hinv hl0_st hfl_st hr_le hml
      c0_hsplit
      · have hr_lt : round.toNat < 4 := hc
        have hr1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
        c0_hsplit
        · c0_hsplit
          · obtain ⟨F_cur, hspw⟩ := hinv.sparse.exists_witness
            c0_hsteps; c0_call hTarjan
            refine ⟨c, F0, F_cur, st, _, rfl, hspw, hl0_st, hml, ?_⟩
            intro ucnt _ _ inc1 _ _ _ _ _ sstk1 _ m1 st1 hspw1 huc_le hus1 hrepr1 hm1_f
            have hinvw1 : FullM6HdrInvW c F0 F_cur ext st1 :=
              FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk hspw1
            have hl01' : st1.core.cur_level = 0 := hl0_st
            have hfl1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl_st
            c0_hsplit
            · c0_hsteps; exact hQ 20#64 ext st1 m1 hinvw1.toInv hl01' hfl1' (Or.inr rfl)
                (fun _ => hspw1.2.1.ext_sound.2 (hspw1.2.1.inconsistent_sound hc))
                (fullM6HdrMem_unfocus_full hm1_f)
            · c0_hsteps; c0_call hElimVars
              refine ⟨c, F0, F_cur, ext, st1, R, rfl, hinvw1, hl01', hrepr1 hc, huc_le, hus1,
                fullM6HdrMem_unfocus_full hm1_f, ?_⟩
              intro ok2 ext2 st2 m2 hinvw2 hl02 _ hfl2 hrepr2 hfail2 hm2
              have hfl2' : st2.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hfl2 hfl1'
              have hm2_f := fullM6HdrMem_focus_full hm2
              c0_hsplit
              · clear hm2
                c0_hsteps_nogrp
                c0_hsplit
                · exact hB (round, st2, ext2) m2 ⟨hinvw2.toInv, hl02, hfl2', hm2_f⟩
                · c0_hsteps_nogrp; c0_call hRewriteBins
                  refine ⟨c, F0, F_cur, st2, _, rfl, hinvw2.sparseW, hl02, hrepr2, hm2_f, ?_⟩
                  intro ok3 st3 m3 hspw3 hl03 _ hfl3 hrepr3 hfail3 hm3_f
                  have hinv3 := FullM6HdrInv.mk_inv hinvw2.cfgOk hinvw2.extOk hspw3.toSparse
                  have hfl3' : st3.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                    rw [hfl3]; exact hfl2'
                  c0_hsplit
                  · c0_hsteps; c0_call hRewriteAr
                    refine ⟨c, F0, F_cur, st3, _, rfl, hspw3, hl03, hrepr3, hm3_f, ?_⟩
                    intro ok4 st4 m4 hspw4 hl04 _ hfl4 hfail4 hm4_f
                    have hinv4 := FullM6HdrInv.mk_inv hinvw2.cfgOk hinvw2.extOk hspw4.toSparse
                    have hfl4' : st4.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4 ▸ hfl3'
                    c0_hsplit
                    · c0_hsteps; c0_call hArenaSweep
                      refine ⟨c, F0, F_cur, st4, _, rfl, hspw4.1, hspw4.2.1, hspw4.2.2.2.1,
                        hspw4.2.2.2.2.2, fun hpos => by omega, hm4_f, ?_⟩
                      intro sr vals5 fl5 lvl5 rsns5 trl5 tp5 te5 unass5 unfl5
                        wvec5 wstk5 arena5 alen5 wlen5 wu5 fred5 ni5 nr5 nb5 oom5 sc5
                        m5 _ hlen5 _ hext5 hws25 hll5 hw5 hnd5 _ _ _ hsr2 _ hm5_f
                      let st5 : FullState :=
                        { core := { st4.core with
                            vals := vals5, flags := fl5, lvl := lvl5, rsns := rsns5,
                            trl := trl5, trail_pos := tp5, trail_end := te5,
                            unassigned := unass5, unflushed := unfl5, wvec := wvec5,
                            wstk := wstk5, arena := arena5, arena_len := alen5,
                            wlen := wlen5, wusable := wu5, arena_garbage := 0#64,
                            first_reducible := fred5, num_irred := ni5,
                            num_redundant := nr5, num_binary := nb5, oom := oom5 }
                          scratch := sc5 }
                      have hspw5 := s6a_fullSparseInvW_of_sweep hspw4 hlen5 hw5 hnd5 hll5
                        hext5 rfl rfl rfl
                      have hinv5 :=
                        FullM6HdrInv.mk_inv hinvw2.cfgOk hinvw2.extOk hspw5.toSparse
                      have hl05 : st5.core.cur_level = 0 := hl04
                      c0_hsplit
                      · c0_hsteps
                        exact hQ 20#64 ext2 st5 m5 hinv5 hl05 hfl4' (Or.inr rfl)
                          (fun _ => (hsr2 hc).2) (fullM6HdrMem_unfocus_full hm5_f)
                      · c0_hsteps; c0_call hProp
                        refine ⟨c, F0, F_cur, ext2, st5, R, rfl, hinvw2.cfgOk,
                          hinvw2.extOk, hspw5.1, hspw5.2.1, hspw5.2.2.2.2.2,
                          fullM6HdrMem_unfocus_full hm5_f, ?_⟩
                        intro pr ext6 vals6 fl6 lvl6 rsns6 trl6 tp6 te6 prop6
                          unass6 unfl6 wvec6 arena6 wstk6 wlen6 wu6 fuel6 ctype6 cref6
                          c06 c16 oom6 sc6 m6 _ hext6 _ hlen6 hw6 _ hperm6 hsc6 _ _ _ _
                          hfl6 _ _ hpr1 _ _ hm6
                        let st6 : FullState :=
                          { core := { st5.core with
                              vals := vals6, flags := fl6, lvl := lvl6, rsns := rsns6,
                              trl := trl6, trail_pos := tp6, trail_end := te6,
                              propagated := prop6, unassigned := unass6,
                              unflushed := unfl6, wvec := wvec6, arena := arena6,
                              wstk := wstk6, wlen := wlen6, wusable := wu6,
                              fuel := fuel6, confl_type := ctype6, confl_ref := cref6,
                              confl_lit0 := c06, confl_lit1 := c16, oom := oom6 }
                            scratch := sc6 }
                        have hspw6 := s6a_fullSparseInvW_of_bcp13 hspw5 hlen6 hw6
                          hperm6 hsc6
                        have hinv6 := FullM6HdrInv.mk_inv hinvw2.cfgOk hext6
                          hspw6.toSparse
                        have hfl6' : st6.core.fuel.toNat ≤ s0.core.fuel.toNat :=
                          Nat.le_trans hfl6 hfl4'
                        c0_hsplit
                        · c0_hsteps
                          exact hQ 20#64 ext6 st6 m6 hinv6 hl05 hfl6' (Or.inr rfl)
                            (fun _ => level0_unsat_of_conflict_okW hw6 hl05
                              (hpr1 hc).2.2) hm6
                        · c0_hsteps
                          exact hL (round + 1#64, st6, ext6) m6 (by dsimp only; omega)
                            ⟨hinv6, hl05, hfl6', by dsimp only; omega,
                              fullM6HdrMem_focus_full hm6⟩
                    · c0_hsteps
                      exact hQ 20#64 ext2 st4 m4 hinv4 hl04 hfl4' (Or.inr rfl)
                        (fun _ => hfail4 (by
                          cases ok4 <;>
                            first | rfl | exact absurd hc (by decide)))
                        (fullM6HdrMem_unfocus_full hm4_f)
                  · c0_hsteps
                    exact hQ 20#64 ext2 st3 m3 hinv3 hl03 hfl3' (Or.inr rfl)
                      (fun _ => hfail3 (by
                        cases ok3 <;> first | rfl | exact absurd hc (by decide)))
                      (fullM6HdrMem_unfocus_full hm3_f)
              · c0_hsteps
                exact hQ 20#64 ext2 st2 m2 hinvw2.toInv hl02 hfl2' (Or.inr rfl)
                  (fun _ => hfail2 (by
                    cases ok2 <;> first | rfl | exact absurd hc (by decide))) hm2
          · c0_hsteps; exact hB (round, st, ext) ml ⟨hinv, hl0_st, hfl_st, hml⟩
        · c0_hsteps; exact hB (round, st, ext) ml ⟨hinv, hl0_st, hfl_st, hml⟩
      · c0_hsteps; exact hB (round, st, ext) ml ⟨hinv, hl0_st, hfl_st, hml⟩
    · intro B L _ hL; c0_hsteps
      exact hL (0#64, st1, ext1) m1 ⟨hinv1, hl01, hfl1, Nat.zero_le _, hm1_f⟩
  · intro Jbt hJbt; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s0, _, rfl, hsp0.1.lengths, hclv_lt, fun _ => by
        have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega,
        hw0.2.1.trail_lits_lt, hm_f, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 st1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1_f
      have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
      have hl01 : st1.core.cur_level = 0 := by dsimp only [st1]; rw [hcl1]; simp
      have hsp1 := s6a_fullSparseInvW_of_perm
        ⟨hsp0.1.lengths, hw0.2.1, hsp0.2.1, hsp0.2.2.1, hsp0.2.2.2.1, hsp0.2.2.2.2⟩
        hlen1 hw1 ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩
        rfl rfl rfl hprsc1.1
      c0_hsteps
      exact hJbt (st1, ext0) m1
        ⟨FullM6HdrInv.mk_inv hinv0.cfgOk hinv0.extOk hsp1.toSparse, hl01, Nat.le_refl _, hm1_f⟩
    · have hl00 : s0.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps; exact hJbt (s0, ext0) m ⟨hinv0, hl00, Nat.le_refl _, hm_f⟩

/-! ## 4. `full_reduce_purge_c0` Step-13 Lift -/

/-- Step-13 callee-parametric WP lift for `FullM7V2Robust.full_reduce_purge_c0_body` to
`step13ReducePurgeC0M6Spec` using `step13BcpM6Spec`. -/
theorem full_reduce_purge_c0_step13_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ h m Q X, step13ReducePurgeC0M6Spec (h, ()) m Q X →
      Func.wp Γ FullM7V2Robust.full_reduce_purge_c0_body (h, ()) m Q X := by
  rintro h m Q X hred
  rcases m6ReduceSpec_elim hred with ⟨c, F0, F_cur, ext0, s0, R, rfl, hinv0, hm, hQ⟩
  have _hx := c.hmaxv; unfold dimacsBound at _hx
  have hsp0 := hinv0.sparseW
  have hok0 := s6a_purgeStateOk_refl hsp0
  have hcl0_lt : s0.core.cur_level < 2 ^ 64 := by
    have := hsp0.2.1.cur_level_le; have := hsp0.1.core_ok.trail_end_le
    have := hsp0.1.core_ok.cur_vars_le; omega
  have hm_f := fullM6HdrMem_focus_full hm
  unfold Func.wp FullM7V2Robust.full_reduce_purge_c0_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState × List (BitVec 64))
    (fun p mp => S6aPurgeStateOk c F0 F_cur s0 p.1 ∧ M6HdrExtOk p.2 ∧
      (FullMem c p.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) p.2 ⋆ R)) mp) ?_ ?_
  · rintro _ ⟨sL, extL⟩ mL ⟨hokL, hextL, hmL_f⟩
    dsimp only at hokL hextL hmL_f
    c0_hsteps_nogrp; c0_call hMarkRsn
    refine ⟨c, F0, F_cur, sL, _, rfl, hokL.sparse.1.lengths, hokL.witness, hmL_f, ?_⟩
    intro ar1 m1_f _ hlen1 hrefs1 hper1 hrm1 hw1 hm1_f
    let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
    have hok1 := s6a_purgeStateOk_mark_reasons hokL hlen1 hrefs1 hper1 hw1
    have hrm1' : FullReasonsMarked s1 := hrm1 rfl
    have har1_len := hok1.sparse.lengths.core_ok.arena_len_le
    c0_hsteps_nogrp
    refine wp_join_state1 (t := i64) (α := FullState × BitVec 64) Prod.snd
      (fun p mp => S6aPurgeStateOk c F0 F_cur s0 p.1 ∧ FullReasonsMarked p.1 ∧
        (FullMem c p.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R)) mp) ?_ ?_
    · rintro _ ⟨sG, _⟩ mG ⟨hokG, hrmG, hmG⟩
      dsimp only at hokG hrmG hmG
      c0_hsteps_nogrp
      refine wp_join0 (fun mr => Q (1#64, ()) mr) (fun _ _ h => by c0_hsteps; exact h) ?_
      intro Jret hJret
      c0_hsteps_nogrp
      refine wp_while_state0 (α := FullState × List (BitVec 64))
        (fun p => c.max_vars + 1 - p.1.core.trail_end)
        (fun p mW => S6aPurgeStateOk c F0 F_cur s0 p.1 ∧ M6HdrExtOk p.2 ∧
          (0 < p.1.core.cur_level → FullReasonsMarked p.1) ∧
          (FullMem c p.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) p.2 ⋆ R)) mW) ?_ ?_
      · intro Jw hJw; exact hJw (sG, extL) mG ⟨hokG, hextL, fun _ => hrmG, hmG⟩
      rintro Jw ⟨sW, extW⟩ mW ⟨hokW, hextW, hrmW, hmW_f⟩ ihW
      c0_hsteps_nogrp <;> (try exact absurd (by assumption : true = false) (by decide))
      c0_call hSweep
      refine ⟨c, F0, F_cur, sW, _, rfl, hokW.sparse.1.lengths, hokW.witness,
        hokW.sparse.2.2.1, hokW.dm0, hrmW, hmW_f, ?_⟩
      intro sr valsA flA lvlA rsnsA trlA tpA teA unassA unflA wvecA wstkA arenaA alenA
        wlenA wuA fredA niA nrA nbA oomA scA mA _ hlenA hsr_disj hextA hws2A hllA hwA hndA
        hoomA hposA hsr1 hsr2 _hmA3 hmA_f
      let sA : FullState :=
        { core := { sW.core with
            vals := valsA, flags := flA, lvl := lvlA, rsns := rsnsA, trl := trlA,
            trail_pos := tpA, trail_end := teA, unassigned := unassA, unflushed := unflA,
            wvec := wvecA, wstk := wstkA, arena := arenaA, arena_len := alenA, wlen := wlenA,
            wusable := wuA, arena_garbage := 0#64, first_reducible := fredA, num_irred := niA,
            num_redundant := nrA, num_binary := nbA, oom := oomA }
          scratch := scA }
      have hmA := fullM6HdrMem_unfocus_full hmA_f
      have hspA : FullSparseInvW c F0 F_cur sA :=
        ⟨hlenA, hwA, ⟨hokW.mrk_zero, hokW.lm_clr⟩, hndA,
          ⟨hllA, hextA ▸ hokW.sparse.2.2.2.1.2⟩, hokW.dm0⟩
      have hclA_le : sA.core.cur_level ≤ s0.core.cur_level := hokW.cl_le
      have hflA_le : sA.core.fuel.toNat ≤ s0.core.fuel.toNat := hokW.fuel_le
      have hcvA : sA.core.cur_vars = s0.core.cur_vars := hokW.cv_eq
      have htmpA : sA.core.tmp = s0.core.tmp := hokW.tmp_eq
      have htlA : sA.core.tmp_len = s0.core.tmp_len := hokW.tl_eq
      have hws2A' : sA.scratch.work_stk2 = s0.scratch.work_stk2 :=
        hws2A.trans hokW.ws2_eq
      have hposA' : 0 < sA.core.cur_level →
          sA.core.cur_level = s0.core.cur_level ∧ sA.core.vals = s0.core.vals ∧
          sA.core.lvl = s0.core.lvl ∧ sA.core.trl = s0.core.trl ∧
          sA.core.trail_pos = s0.core.trail_pos ∧ sA.core.trail_end = s0.core.trail_end :=
        fun hp => by
          obtain ⟨_, _, hv1, hl1, ht1, htp1, hte1⟩ := hposA hp
          obtain ⟨hc0, hv0, hl0, ht0, htp0, hte0⟩ := hokW.pos_pres hp
          exact ⟨hc0, hv1.trans hv0, hl1.trans hl0, ht1.trans ht0,
            htp1.trans htp0, hte1.trans hte0⟩
      c0_hsteps_nogrp
      · exact hQ 20#64 extW sA mA (FullM6HdrInvW.mk_inv hinv0.cfgOk hextW hspA)
          (Or.inr (Or.inr rfl)) hclA_le hflA_le hcvA htmpA htlA hws2A'
          (fun _ => (hsr2 hc).2) (fun h => by cases h) (fun _ => hposA') hmA
      · exact hQ 0#64 extW sA mA (FullM6HdrInvW.mk_inv hinv0.cfgOk hextW hspA) (Or.inl rfl)
          hclA_le hflA_le hcvA htmpA htlA hws2A'
          (fun h => by cases h) (fun h => by cases h) (fun _ => hposA') hmA
      · exact hJret mA (hQ 1#64 extW sA mA (FullM6HdrInvW.mk_inv hinv0.cfgOk hextW hspA)
          (Or.inr (Or.inl rfl)) hclA_le hflA_le hcvA htmpA htlA hws2A' (fun h => by cases h)
          (fun _ _ => hoomA (Or.inl hc)) (fun _ => hposA') hmA)
      ·     have hsr_eq1 : sr = 1#64 := by
              rcases hsr_disj with rfl | rfl | rfl | rfl
              · exact absurd rfl (by assumption)
              · rfl
              · exact absurd rfl (by assumption)
              · exact absurd rfl (by assumption)
            obtain ⟨hlW0, hte_lt⟩ := hsr1 hsr_eq1
            have hokA := s6a_purgeStateOk_sweep hokW hlenA hwA hndA hllA hextA hws2A
              (fun _ => hoomA (Or.inr hsr_eq1)) (fun hp => (hposA hp).2.2)
            c0_call hProp
            refine ⟨c, F0, F_cur, extW, sA, R, rfl, hinv0.cfgOk, hextW,
              hlenA, hwA, hokW.dm0, hmA, ?_⟩
            intro pr extP valsP flP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP
              arenaP wstkP wlenP wuP fuelP ctypeP crefP c0P c1P oomP scP mP _ hextP _
              hlenP hwP htrP hpermP hscP _ _ _ _ hflP hpr_disj hpr0 hpr1 _ _ hmP
            let sP : FullState :=
              { core := { sA.core with
                  vals := valsP, flags := flP, lvl := lvlP, rsns := rsnsP, trl := trlP,
                  trail_pos := tpP, trail_end := teP, propagated := propP,
                  unassigned := unassP, unflushed := unflP, wvec := wvecP, arena := arenaP,
                  wstk := wstkP, wlen := wlenP, wusable := wuP, fuel := fuelP,
                  confl_type := ctypeP, confl_ref := crefP, confl_lit0 := c0P,
                  confl_lit1 := c1P, oom := oomP }
                scratch := scP }
            have hspP := s6a_fullSparseInvW_of_bcp13 hspA hlenP hwP hpermP hscP
            have hclP0 : sP.core.cur_level = 0 := hlW0
            have hclP_le : sP.core.cur_level ≤ s0.core.cur_level := by
              rw [hclP0]; exact Nat.zero_le _
            have hflP_le : sP.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hflP hflA_le
            have hcvP : sP.core.cur_vars = s0.core.cur_vars := hcvA
            have htmpP : sP.core.tmp = s0.core.tmp := htmpA
            have htlP : sP.core.tmp_len = s0.core.tmp_len := htlA
            have hws2P : sP.scratch.work_stk2 = s0.scratch.work_stk2 :=
              hscP.2.2.1.trans hws2A'
            have hposP : 0 < sP.core.cur_level →
                sP.core.cur_level = s0.core.cur_level ∧ sP.core.vals = s0.core.vals ∧
                sP.core.lvl = s0.core.lvl ∧ sP.core.trl = s0.core.trl ∧
                sP.core.trail_pos = s0.core.trail_pos ∧ sP.core.trail_end = s0.core.trail_end :=
              fun hp => by rw [hclP0] at hp; exact absurd hp (Nat.not_lt_zero _)
            c0_hsteps_nogrp
            · exact hQ 20#64 extP sP mP (FullM6HdrInvW.mk_inv hinv0.cfgOk hextP hspP)
                (Or.inr (Or.inr rfl)) hclP_le hflP_le hcvP htmpP htlP hws2P
                (fun _ => level0_unsat_of_conflict_okW hwP hclP0 (hpr1 hc).2.2)
                (fun h => by cases h) (fun _ => hposP) hmP
            · exact hQ 0#64 extP sP mP (FullM6HdrInvW.mk_inv hinv0.cfgOk hextP hspP) (Or.inl rfl)
                hclP_le hflP_le hcvP htmpP htlP hws2P
                (fun h => by cases h) (fun h => by cases h) (fun _ => hposP) hmP
            ·   have hpr0_eq : pr = 0#64 := hc
                have hmP_f := fullM6HdrMem_focus_full hmP
                clear hmP
                c0_hsteps_nogrp
                let sP0 : FullState := { sP with core := { sP.core with unflushed := 0#64 } }
                have hokP := s6a_purgeStateOk_bcp13 hokA hlenP hwP hpermP hscP hflP
                  (hpr0 hpr0_eq).2.1
                  (fun hp => by rw [hclP0] at hp; exact absurd hp (Nat.not_lt_zero _))
                have hwP0 := s6a_fullWitnessInv_of_fields hwP sP.core.flags sP.core.repr
                  sP.core.unassigned 0#64
                have hspP0 : FullSparseInvW c F0 F_cur sP0 :=
                  ⟨⟨{ hspP.1.core_ok with }, hspP.1.scratch_ok⟩, hwP0,
                    hspP.2.2.1, hspP.2.2.2.1, hspP.2.2.2.2.1, hspP.2.2.2.2.2⟩
                have hokP0 : S6aPurgeStateOk c F0 F_cur s0 sP0 :=
                  s6a_purgeStateOk_trans hokP
                    ⟨hspP0.toSparse, hwP0, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl,
                     hspP.2.2.2.2.2, id, hspP.2.2.1.1, hspP.2.2.1.2, hspP.2.2.2.2.1.1, rfl, rfl,
                     fun hp => by change 0 < sP.core.cur_level at hp; rw [hclP0] at hp; omega⟩
                have hte_eqP0 : sP0.core.trail_end = sP.core.trail_end := rfl
                have hte_ltP : sW.core.trail_end < sP0.core.trail_end := by
                  have := htrP.1; change sA.core.trail_end ≤ sP.core.trail_end at this
                  change sW.core.trail_end < sA.core.trail_end at hte_lt
                  omega
                have hteP_te : sP.core.trail_end = teP := rfl
                have hteP0_le : teP ≤ c.max_vars := by
                  have h1 := hspP.1.core_ok.trail_end_le
                  have h2 := hspP.1.core_ok.cur_vars_le
                  dsimp only [sP] at h1 h2; omega
                exact ihW (sP0, extP) _ (by
                  dsimp only; rw [hte_eqP0, hteP_te]
                  rw [hte_eqP0, hteP_te] at hte_ltP
                  omega)
                  ⟨hokP0, hextP, fun hp => by
                    change 0 < sP.core.cur_level at hp; rw [hclP0] at hp; omega, by assumption⟩
    · intro J hJ
      c0_hsteps_nogrp
      refine wp_while_state1 (t := i64) (α := FullState × BitVec 64) (fun p => p.2)
        (fun p => s1.core.arena_len - p.2.toNat)
        (fun (sC, cr) mC => S6aPurgeStateOk c F0 F_cur s0 sC ∧ FullReasonsMarked sC ∧
          sC.core.arena_len = s1.core.arena_len ∧ sC.core.arena.length = c.arena_cap ∧
          cr.toNat ≤ sC.core.arena_len ∧
          (cr.toNat < sC.core.arena_len → cr.toNat ∈ fullArenaClauseRefs sC) ∧
          (FullMem c sC ⋆ (m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R)) mC) ?_ ?_
      · intro Jc hJc; exact hJc (s1, 0#64) m1_f
          ⟨hok1, hrm1', rfl, hok1.sparse.lengths.core_ok.arena_len_arr, Nat.zero_le _,
           fun h0 => fullArenaClauseRefs_zero_mem hok1.witness.arena h0, hm1_f⟩
      rintro Jc ⟨sC, cr⟩ mC ⟨hokC, hrmC, halC, harC, hcr_le, hcr_ref, hmC⟩ ihC
      s6a_to_jnz
      rw [wp_jnz]; constructor <;> intro hc
      · have har_len_lt : sC.core.arena_len < 2 ^ 64 := by
          have := c.harena; unfold dimacsBound at this
          have := hokC.sparse.lengths.core_ok.arena_len_le; omega
        have hcr_lt : cr.toNat < sC.core.arena_len := by
          dsimp only [Arg.val] at hc
          simpa [BitVec.ult, Nat.mod_eq_of_lt har_len_lt] using hc
        have hcr_mem := hcr_ref hcr_lt
        have hcr_ar : cr.toNat < sC.core.arena.length := by
          rw [harC]; have := hokC.sparse.lengths.core_ok.arena_len_le; omega
        c0_hsteps_nogrp; c0_call hNext
        refine ⟨c, sC, _, rfl, hokC.sparse.lengths, hmC, ?_⟩
        dsimp only
        let nxt : BitVec 32 :=
          BitVec.ofNat 32 (fullArenaNextOff sC.core.arena sC.core.arena_len cr.toNat)
        have hnext_or := fullArenaClauseRefs_next_or_end hokC.witness.arena hcr_mem
        have hnxt_le : (fullArenaNextOff sC.core.arena sC.core.arena_len cr.toNat) ≤
            sC.core.arena_len := by
          rcases hnext_or with heq | href
          · omega
          · have := hokC.witness.arena.refs_wf _ href; omega
        have har_cap_lt : c.arena_cap < 2 ^ 32 := by
          have := c.harena; unfold dimacsBound at this; omega
        have har_len_le : sC.core.arena_len ≤ c.arena_cap :=
          hokC.sparse.lengths.core_ok.arena_len_le
        have hnxt_eq : nxt.toNat =
            fullArenaNextOff sC.core.arena sC.core.arena_len cr.toNat := by
          dsimp only [nxt]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
        refine wp_join_state0 (α := FullState)
          (fun sJ mJ => S6aPurgeStateOk c F0 F_cur s0 sJ ∧ FullReasonsMarked sJ ∧
            sJ.core.arena_len = s1.core.arena_len ∧ sJ.core.arena.length = c.arena_cap ∧
            (nxt.toNat < sJ.core.arena_len → nxt.toNat ∈ fullArenaClauseRefs sJ) ∧
            (FullMem c sJ ⋆ (m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R)) mJ) ?_ ?_
        · rintro _ sJ mJ ⟨hokJ, hrmJ, halJ, harJ, hnxtJ, hmJ⟩
          c0_hsteps_nogrp; c0_hsplit
          · exact hJ (sJ, cr) mJ ⟨hokJ, hrmJ, hmJ⟩
          · have hcr_32 : cr.toNat < 2 ^ 32 := by omega
            have hnxt_32 : nxt.toNat < 2 ^ 32 := nxt.isLt
            have hcr_nxt : cr.toNat < nxt.toNat := by
              rw [Nat.mod_eq_of_lt hcr_32, ← hnxt_eq, Nat.mod_eq_of_lt hnxt_32] at hc
              omega
            have hnxt64 : (BitVec.ofNat 64 nxt.toNat).toNat = nxt.toNat := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have hnxt_arg :
                BitVec.setWidth 64 (BitVec.ofNat 32 (fullArenaNextOff sC.core.arena
                  sC.core.arena_len (BitVec.setWidth 32 cr).toNat)) =
                  BitVec.ofNat 64 nxt.toNat := by
              have hcr_sw : (BitVec.setWidth 32 cr).toNat = cr.toNat := by
                simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcr_32]
              rw [hcr_sw]
              change BitVec.setWidth 64 nxt = BitVec.ofNat 64 nxt.toNat
              apply BitVec.eq_of_toNat_eq
              simp [BitVec.toNat_setWidth]
            rw [hnxt_arg]
            exact ihC (sJ, BitVec.ofNat 64 nxt.toNat) mJ
              (by dsimp only; rw [hnxt64]; omega)
              ⟨hokJ, hrmJ, halJ, harJ,
               by rw [hnxt64, halJ, ← halC, hnxt_eq]; exact hnxt_le,
               fun h => by rw [hnxt64] at h ⊢; exact hnxtJ h, hmJ⟩
        · intro Jk hJk
          s6a_to_jnz; rw [wp_jnz]; constructor <;> intro hc1
          · have har_bd : sC.core.arena_len ≤ c.arena_cap :=
              hokC.sparse.lengths.core_ok.arena_len_le
            have hcr3_le : cr.toNat + 3 ≤ sC.core.arena_len := by
              dsimp only [Arg.val] at hc1
              have hcr3_nat : (cr + 3#64).toNat = cr.toNat + 3 := by
                rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
              simpa [BitVec.ule, hcr3_nat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt har_len_lt] using hc1
            have hcr2_ar : (cr + 2#64).toNat < sC.core.arena.length := by
              rw [harC, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
            s6a_to_jnz; rw [wp_jnz]; constructor <;> intro _hc2
            · s6a_to_jnz; c0_hsplit
              · have hnorsn := s6a_bv32_norsn_of_mask hc
                have hnorsn' : (fullArenaHdr sC cr.toNat &&& 0x00200000#32) = 0#32 := by
                  simpa [fullArenaHdr, fullArenaHdrCore,
                    List.getElem?_eq_getElem hcr_ar, Option.getD_some] using hnorsn
                let agN := sC.core.arena_garbage + 3#64 +
                  (sC.core.arena[cr.toNat + 2]'(by omega)).setWidth 64
                obtain ⟨hokM, hrmM⟩ := s6a_purgeStateOk_mark_garb hokC hrmC hcr_mem hnorsn' hcr_ar
                  (agN := agN)
                let sM : FullState :=
                  { sC with core := { sC.core with
                    arena := sC.core.arena.set cr.toNat
                      (sC.core.arena[cr.toNat]'hcr_ar ||| 0x00080000#32)
                    arena_garbage := agN } }
                have hhdr_eq :
                    sC.core.arena[cr.toNat]'hcr_ar = fullArenaHdr sC cr.toNat := by
                  unfold fullArenaHdr fullArenaHdrCore
                  rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
                have hrefsM : fullArenaClauseRefs sM = fullArenaClauseRefs sC := by
                  dsimp only [sM]; rw [hhdr_eq]
                  exact (FullDenseWatchHelpers.markGarb_preserves_fullWitnessInv
                    hokC.sparse.lengths hokC.witness hcr_mem agN
                    (FullDenseWatchHelpers.markGarb_nonact_of_reasonsMarked hokC.witness hrmC
                      hnorsn')).2.1
                c0_hsteps_nogrp
                refine hJk sM _ ⟨hokM, hrmM, halC, by simp [sM, harC],
                  fun h => by
                    have halM : sM.core.arena_len = sC.core.arena_len := rfl
                    rw [halM] at h
                    rw [hrefsM, hnxt_eq]
                    exact hnext_or.elim (fun heq => by omega) id, ?_⟩
                dsimp only [sM, agN]
                have hcr2_nat : (cr + (2 : BitVec 64)).toNat = cr.toNat + 2 := by bv_omega
                have hne_cr : cr.toNat ≠ (cr + (2 : BitVec 64)).toNat := by omega
                have hget_eq : ∀ hpf,
                    sC.core.arena[(cr + (2 : BitVec 64)).toNat]'hpf =
                      sC.core.arena[cr.toNat + 2]'(by omega) := fun hpf =>
                  Option.some.inj (by simp only [← List.getElem?_eq_getElem, hcr2_nat])
                dsimp only at *
                simp only [List.getElem_set_ne hne_cr, hget_eq] at *
                try rw [show (0x00080000#32 : BitVec 32) = 524288 from rfl] at *
                exact (by assumption)
              · c0_hsteps_nogrp
                exact hJk sC mC ⟨hokC, hrmC, halC, harC,
                  fun h => by rw [hnxt_eq]; exact hnext_or.elim (fun heq => by omega) id, hmC⟩
            · c0_hsteps_nogrp
              exact hJk sC mC ⟨hokC, hrmC, halC, harC,
                fun h => by rw [hnxt_eq]; exact hnext_or.elim (fun heq => by omega) id, hmC⟩
          · c0_hsteps_nogrp
            exact hJk sC mC ⟨hokC, hrmC, halC, harC,
              fun h => by rw [hnxt_eq]; exact hnext_or.elim (fun heq => by omega) id, hmC⟩
      · c0_hsteps_nogrp; exact hJ (sC, cr) mC ⟨hokC, hrmC, hmC⟩
  · intro Jm hJm
    c0_hsteps_nogrp; c0_hsplit
    · c0_hsteps_nogrp
      refine wp_join_state0 (α := FullState)
        (fun p mp => S6aPurgeStateOk c F0 F_cur s0 p ∧ p.core.cur_level = 0 ∧
          (FullMem c p ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mp) ?_ ?_
      · rintro _ sB mB ⟨hokB, hlB, hmB_f⟩
        c0_hsteps_nogrp; c0_call hProp
        refine ⟨c, F0, F_cur, ext0, sB, R, rfl, hinv0.cfgOk, hinv0.extOk,
          hokB.sparse.1.lengths, hokB.witness, hokB.dm0, fullM6HdrMem_unfocus_full hmB_f, ?_⟩
        intro pr extP valsP flP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP
          wstkP wlenP wuP fuelP ctypeP crefP c0P c1P oomP scP mP _ hextP _ hlenP hwP _
          hpermP hscP _ _ _ _ hflP hpr_disj hpr0 hpr1 _ _ hmP
        let sP : FullState :=
          { core := { sB.core with
              vals := valsP, flags := flP, lvl := lvlP, rsns := rsnsP, trl := trlP,
              trail_pos := tpP, trail_end := teP, propagated := propP, unassigned := unassP,
              unflushed := unflP, wvec := wvecP, arena := arenaP, wstk := wstkP,
              wlen := wlenP, wusable := wuP, fuel := fuelP, confl_type := ctypeP,
              confl_ref := crefP, confl_lit0 := c0P, confl_lit1 := c1P, oom := oomP }
            scratch := scP }
        have hspP := s6a_fullSparseInvW_of_bcp13
          ⟨hokB.sparse.1.lengths, hokB.witness, hokB.sparse.2.1, hokB.sparse.2.2.1,
           hokB.sparse.2.2.2.1, hokB.dm0⟩ hlenP hwP hpermP hscP
        have hflP_le : sP.core.fuel.toNat ≤ s0.core.fuel.toNat :=
          Nat.le_trans hflP hokB.fuel_le
        have hclP_le : sP.core.cur_level ≤ s0.core.cur_level := by rw [hlB]; exact Nat.zero_le _
        have hws2P : sP.scratch.work_stk2 = s0.scratch.work_stk2 :=
          hscP.2.2.1.trans hokB.ws2_eq
        have hposP : 0 < sP.core.cur_level →
            sP.core.cur_level = s0.core.cur_level ∧ sP.core.vals = s0.core.vals ∧
            sP.core.lvl = s0.core.lvl ∧ sP.core.trl = s0.core.trl ∧
            sP.core.trail_pos = s0.core.trail_pos ∧ sP.core.trail_end = s0.core.trail_end :=
          fun hp => by rw [hlB] at hp; exact absurd hp (Nat.not_lt_zero _)
        c0_hsteps_nogrp
        · exact hQ 20#64 extP sP mP (FullM6HdrInvW.mk_inv hinv0.cfgOk hextP hspP)
            (Or.inr (Or.inr rfl)) hclP_le hflP_le hokB.cv_eq hokB.tmp_eq hokB.tl_eq hws2P
            (fun _ => level0_unsat_of_conflict_okW hwP hlB (hpr1 hc).2.2)
            (fun h => by cases h) (fun _ => hposP) hmP
        · exact hQ 0#64 extP sP mP (FullM6HdrInvW.mk_inv hinv0.cfgOk hextP hspP) (Or.inl rfl)
            hclP_le hflP_le hokB.cv_eq hokB.tmp_eq hokB.tl_eq hws2P
            (fun h => by cases h) (fun h => by cases h) (fun _ => hposP) hmP
        ·   have hpr0_eq : pr = 0#64 := hc
            have hmP_f := fullM6HdrMem_focus_full hmP
            clear hmP
            c0_hsteps_nogrp
            let sP0 : FullState := { sP with core := { sP.core with unflushed := 0#64 } }
            have hokP := s6a_purgeStateOk_bcp13 hokB hlenP hwP hpermP hscP hflP
              (hpr0 hpr0_eq).2.1 (fun hp => by rw [hlB] at hp; exact absurd hp (Nat.not_lt_zero _))
            have hwP0 := s6a_fullWitnessInv_of_fields hwP sP.core.flags sP.core.repr
              sP.core.unassigned 0#64
            have hspP0 : FullSparseInvW c F0 F_cur sP0 :=
              ⟨⟨{ hspP.1.core_ok with }, hspP.1.scratch_ok⟩, hwP0,
                hspP.2.2.1, hspP.2.2.2.1, hspP.2.2.2.2.1, hspP.2.2.2.2.2⟩
            have hokP0 : S6aPurgeStateOk c F0 F_cur s0 sP0 :=
              s6a_purgeStateOk_trans hokP
                ⟨hspP0.toSparse, hwP0, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl,
                 hspP.2.2.2.2.2, id, hspP.2.2.1.1, hspP.2.2.1.2, hspP.2.2.2.2.1.1, rfl, rfl,
                 fun hp => by change 0 < sP.core.cur_level at hp; rw [hlB] at hp; omega⟩
            exact hJm (sP0, extP) _ ⟨hokP0, hextP, by assumption⟩
      · intro Jb hJb; c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps_nogrp; c0_call hBacktrack
          refine ⟨c, s0, _, rfl, hsp0.1, hcl0_lt, fun _ => by
            have := hsp0.2.1.cur_level_le; have := hsp0.1.core_ok.trail_end_le
            have := hsp0.1.core_ok.cur_vars_le; omega,
            hsp0.2.1.trail_lits_lt, hm_f, ?_⟩
          intro _ _ _ _ _ _ _ clB _ scB mB sB hlenB _ _ hclB hprscB _ _ _ hw_le _ hmB_f
          have hwB := hw_le F0 F_cur hsp0.2.1 (Nat.zero_le _)
          have hclB0 : clB = 0 := by rw [hclB]; simp
          dsimp only [sB] at hlenB hwB
          rw [hclB0] at hlenB hwB
          have hokB := s6a_purgeStateOk_backtrack0 hok0 hlenB hwB
            hprscB.1.1 hprscB.1.2 hprscB.2.2.1
          have hokB' : S6aPurgeStateOk c F0 F_cur s0 sB := by
            dsimp only [sB]; rw [hclB0]; exact hokB
          have hlB : sB.core.cur_level = 0 := by dsimp only [sB]; rw [hclB0]
          exact hJb sB mB ⟨hokB', hlB, hmB_f⟩
        · have hl00 : s0.core.cur_level = 0 := by
            rw [Nat.mod_eq_of_lt hcl0_lt] at hc
            change ¬ 0 < s0.core.cur_level at hc
            omega
          exact hJb s0 m ⟨hok0, hl00, hm_f⟩
    · c0_hsteps_nogrp; exact hJm (s0, ext0) m ⟨hok0, hinv0.extOk, hm_f⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
