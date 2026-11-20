module

public import LeanQbe.T.Examples.Kissat.FullInv1

/-!
# Kissat `D-Full` UNSAT-Only Core Invariant Transitions (`Stage 4`, Part 2)

Builds on `FullInv1` to prove foundational core-invariant preservation lemmas across Stage-4 C0
operations:
- `FullCoreInv.with_scratch` / `FullInv.with_scratch` (`SafetySlice` 1-step transport)
- `FullCoreInv.with_d` / `FullInv.with_d`
- `fullWitnessInv_empty` & `fullInv_init`
- `markGarb_preserves_fullCore` & `FullWitnessInv.replace_extSound`
- `addEntailedClause_preserves_fullCore`
- `chronoAssign_preserves_fullCore` (decision, propagation, UIP, level-0 units)
- `chronoBacktrack_preserves_fullCore` (chronological trail filtering from `frame_trail`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-- `SafetySlice` 1-step transport: any transition preserving `(fullSafetySlice c).coreProj`
preserves `FullCoreInv` verbatim. -/
theorem FullCoreInv.with_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullCoreInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s') : FullCoreInv c F0 s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  obtain ⟨F_cur, hw⟩ := h.witness; exact ⟨hlen', F_cur, heq ▸ hw⟩

theorem FullInv.with_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s') : FullInv c F0 s' :=
  ⟨h.core.with_scratch hlen' hcore, by
    have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
    unfold FullMarksClear; rw [heq]; exact h.marks⟩

theorem FullCoreInv.with_d {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) (cur' val' : BitVec 64) :
    FullCoreInv c F0 { s with core := { s.core with d_cur := cur', d_val := val' } } := by
  obtain ⟨F_cur, hw⟩ := h.witness
  refine ⟨⟨{ h.lengths.core_ok with vals_len := h.lengths.core_ok.vals_len }, h.lengths.scratch_ok⟩,
    F_cur, { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
                     watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩

theorem FullInv.with_d {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullInv c F0 s) (cur' val' : BitVec 64) :
    FullInv c F0 { s with core := { s.core with d_cur := cur', d_val := val' } } :=
  ⟨h.core.with_d cur' val', h.marks⟩

/-- Generic empty-database witness constructor supporting any `ExtUnsatSound` formula `F_cur`. -/
theorem fullWitnessInv_empty {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hext : ExtUnsatSound F0 k.cur_vars F_cur)
    (hinc : k.inconsistent = 0#64) (hal : k.arena_len = 0)
    (hwvec : ∀ l < 2 * k.cur_vars, fullWatchOffCore k l = 0 ∧ fullWatchSizeCore k l = 0)
    (hte : k.trail_end = 0) (hcl : k.cur_level = 0)
    (hft0 : (k.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : ∀ l < 2 * k.cur_vars, k.vals[l]?.getD 0#8 = 0#8) :
    FullWitnessInv c F0 F_cur k := by
  have hrefs : fullArenaClauseRefsCore k = [] := by
    simp [fullArenaClauseRefsCore, hal, fullArenaScanRefs]
  have hwat : ModeWatchesInv F_cur k := by
    by_cases hc : k.dense_mode = 0#64 <;> simp only [ModeWatchesInv, hc, ↓reduceIte]
    · exact WatchesInv.of_slices
        (fun l hl => by obtain ⟨_, hs⟩ := hwvec l hl; omega)
        (fun l hl _ => by obtain ⟨_, hs⟩ := hwvec l hl; omega)
        (fun l1 _ h1 _ _ _ _ => by obtain ⟨_, hs⟩ := hwvec l1 h1; omega)
        (fun l hl => by obtain ⟨ho, hs⟩ := hwvec l hl; rw [ho, hs]; exact .empty)
    · exact DenseWatchesInv.of_slices
        (fun l hl => by obtain ⟨_, hs⟩ := hwvec l hl; omega)
        (fun l hl _ => by obtain ⟨_, hs⟩ := hwvec l hl; omega)
        (fun l1 _ h1 _ _ _ _ => by obtain ⟨_, hs⟩ := hwvec l1 h1; omega)
        (fun l hl => by obtain ⟨ho, hs⟩ := hwvec l hl; rw [ho, hs]; exact .empty)
  exact ⟨hext, fun hne => absurd hinc hne,
    ⟨Or.inl hal, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
     fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩,
    hwat, by rw [hte, hcl]; exact Nat.le_refl _,
    fun _ h => by omega, fun _ _ h => by omega, fun l hl => Or.inl (hvals l hl),
    fun l hl => ⟨(by intro h1; rw [hvals l hl] at h1; cases h1), (by rintro ⟨_, hi, _⟩; omega)⟩,
    fun l hl => ⟨(by intro h1; rw [hvals l hl] at h1; cases h1), (by rintro ⟨_, hi, _⟩; omega)⟩,
    fun _ h => by omega, fun _ _ _ h => by omega, fun _ _ h2 => by omega,
    fun _ h => by omega, fun _ h => by omega, fun _ h => by omega,
    (fun L hL => by
      have hLz : L = 0 := by omega
      subst hLz; rw [hft0]; omega),
    (fun L1 L2 _ hL2 => by
      have heq : L1 = L2 := by omega
      subst heq; exact Nat.le_refl _),
    fun _ h => by omega, fun _ h => by omega, fun _ h => by omega, fun _ h => by omega⟩

/-- Initial zeroed state from `full_init_state` satisfies `FullInv c F0 s` for any `F0`. -/
theorem fullInv_init {c : FullCfg} {F0 : CNF Nat} {s : FullState} (hlen : s.LengthsOk c)
    (hinc : s.core.inconsistent = 0#64) (hal : s.core.arena_len = 0)
    (hwvec : s.core.wvec = List.replicate (4 * c.max_vars) 0#32)
    (hte : s.core.trail_end = 0) (hcl : s.core.cur_level = 0)
    (hft0 : (s.core.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : s.core.vals = List.replicate (2 * c.max_vars) 0#8)
    (hmrk : s.core.mrk = List.replicate c.max_vars 0#8) : FullInv c F0 s := by
  have hext : ExtUnsatSound F0 s.core.cur_vars [] :=
    ⟨(fun _ hc => nomatch hc), fun hu => by
      rw [CNF.unsat_iff_not_sat] at hu
      exact False.elim (hu (fun _ => false)
        ((cnf_sat_cnfOfClauses_iff (fun _ => false) []).mpr fun _ hc => by cases hc))⟩
  have hcv := hlen.core_ok.cur_vars_le
  have hw0 : ∀ l < 2 * s.core.cur_vars,
      fullWatchOffCore s.core l = 0 ∧ fullWatchSizeCore s.core l = 0 := fun l hl => by
    unfold fullWatchOffCore fullWatchSizeCore; rw [hwvec]
    simp [show 2 * l < 4 * c.max_vars by omega, show 2 * l + 1 < 4 * c.max_vars by omega]
  have hv0 : ∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0#8 := fun l hl => by
    rw [hvals]; simp [show l < 2 * c.max_vars by omega]
  exact ⟨⟨hlen, ⟨[], fullWitnessInv_empty hext hinc hal hw0 hte hcl hft0 hv0⟩⟩, fun v hv => by
    rw [hmrk]; simp [show v < c.max_vars by omega]⟩

/-- Clause-garbage marking (`PH_GARB`): setting `PH_GARB` on non-active `cref` preserves
`FullCoreInv` for the same witness `F_cur`. -/
theorem markGarb_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (ag' : BitVec 64)
    (hnonact : ∀ idx < s.core.trail_end,
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullCoreInv c F0 s' := by
  intro s'
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hlen' : s'.LengthsOk c :=
    ⟨{ hinv.lengths.core_ok with
       arena_len_arr := by simp [s', hinv.lengths.core_ok.arena_len_arr] },
     hinv.lengths.scratch_ok⟩
  have hmg := hw.arena.markGarb hinv.lengths.core_ok href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  have hdisj_lits : ∀ {r : Nat}, r ∈ fullArenaClauseRefsCore s.core → r ≠ cref →
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun {r} hr hne => by
    have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (hw.arena.disjoint hr href hlt)
      · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hinv.lengths.core_ok.arena_len_le; have := hinv.lengths.core_ok.arena_len_arr; omega
    exact (fullArenaClauseLitsCore_set_outside hbd hdisj).2
  refine ⟨hlen', F_cur, { hw with
    arena := hmg.2
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hrs := hw.reason_inv idx hidx hne0
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl,
        show s'.core.cur_vars = s.core.cur_vars from rfl, show s'.core.lvl = s.core.lvl from rfl]
      by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
      · have hlg' : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
          Classical.byContradiction fun hn => hbin hn
        rw [ite_eq_right hbin] at hrs ⊢
        let r := (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
        have hne_cref := hnonact idx hidx hne0 hlg'
        have hgarb' : fullArenaClauseGarbCore s'.core r = false := by
          unfold fullArenaClauseGarbCore fullArenaHdrCore
          rw [show s'.core.arena = s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
              from rfl, List.getElem?_set_ne hne_cref.symm]
          exact hrs.2.1
        have hlits_eq := hdisj_lits hrs.1 hne_cref
        exact ⟨hrefs ▸ hrs.1, hgarb', fun q hq => hrs.2.2 q (hlits_eq ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hlg0 : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 := hlg
      have hrs := hw.reason_inv idx hidx hne0
      have hbin_f : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg0 h
      rw [ite_eq_right hbin_f] at hrs
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl]
      exact hdisj_lits hrs.1 (hnonact idx hidx hne0 hlg0) ▸ hw.reason_lit_mem idx hidx hne0 hlg0 }⟩

/-- Pure-formula subset deletion / inprocessing replacement in witness `F_cur` preserving
`FullWitnessInv` (one-line `ExtUnsatSound` deletion via `extUnsatSound_of_subset`). -/
theorem FullWitnessInv.replace_extSound {c : FullCfg} {F0 : CNF Nat}
    {F_cur F_next : List (List Nat)} {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k)
    (hext' : ExtUnsatSound F0 k.cur_vars F_next)
    (hent : (cnfOfClauses F_next).Entails (cnfOfClauses F_cur)) : FullWitnessInv c F0 F_next k :=
  { h with
    ext_sound := hext'
    inconsistent_sound := fun hi => by
      have hu := h.inconsistent_sound hi; rw [CNF.unsat_iff_not_sat] at hu ⊢
      rw [CNF.entails_def] at hent
      intro α hα; exact hu α (hent α hα)
    arena := h.arena.mono hent
    watches := h.watches.mono hent
    level0_sound := fun i hi hl0 => CNF.entails_clause_trans hent (h.level0_sound i hi hl0)
    reason_inv := fun idx hidx hne => by
      have hr := h.reason_inv idx hidx hne
      by_cases hb : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hr ⊢
        exact ⟨hr.1, CNF.entails_clause_trans hent hr.2.1, hr.2.2⟩
      · rw [ite_eq_right hb] at hr ⊢; exact hr }

/-- Appending one entailed non-garbage clause (`len ≥ 3`, `PH_SHRK` clear) to `arena` preserves
`FullCoreInv` across both sparse and dense mode watches. -/
theorem addEntailedClause_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {len : Nat}
    {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wusable' fred' ni' nr' : BitVec 64} {scratch' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                            first_reducible := fred', num_irred := ni', num_redundant := nr' }
      scratch := scratch' } : FullState).LengthsOk c)
    (hge3 : 3 ≤ len)
    (hlits_lt : ∀ l ∈ (s.core.tmp.take len).map BitVec.toNat, l < 2 * s.core.cur_vars)
    (hent : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((s.core.tmp.take len).map BitVec.toNat)))
    (hhold_arena : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]?)
    (hnew_noshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (_hnew_nogarb : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hnew_sz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hnew_lits : fullArenaClauseLitsCore
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len } s.core.arena_len =
      (s.core.tmp.take len).map BitVec.toNat)
    (hwat : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      ModeWatchesInv F_cur
        { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                      wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                      first_reducible := fred', num_irred := ni', num_redundant := nr' }) :
    FullCoreInv c F0
      { s with
        core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                              first_reducible := fred', num_irred := ni', num_redundant := nr' }
        scratch := scratch' } := by
  let s' : FullState :=
    { s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                            first_reducible := fred', num_irred := ni', num_redundant := nr' }
      scratch := scratch' }
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + len)
    (by omega) hhold_arena
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_arena hnew_noshrk hnew_sz
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1l := hinv.lengths.core_ok.arena_len_arr; have h1e := hinv.lengths.core_ok.arena_len_le
    have h2l : arena'.length = c.arena_cap := hlen'.core_ok.arena_len_arr
    have h2e : s.core.arena_len + 3 + len ≤ c.arena_cap := hlen'.core_ok.arena_len_le
    have hbd_ar : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [s']; omega)
      (hold_sz r hr) fun j hj => hhold_arena (r + 3 + j) (by omega)
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + len := by unfold fullArenaNextOff s'; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = len from hnew_sz]
        refine ⟨by dsimp [s']; omega, hge3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rwa [hhold_arena r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold_arena t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hnew_noshrk hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · exact hnew_lits ▸ hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · exact hnew_lits ▸ hent F_cur hw
  refine ⟨hlen', F_cur, { hw with
    arena := harena', watches := hwat F_cur hw
    reason_inv := fun idx hidx hne => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hrs := hw.reason_inv idx hidx hne0
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl,
        show s'.core.cur_vars = s.core.cur_vars from rfl, show s'.core.lvl = s.core.lvl from rfl]
      by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        have hrefs' := hrefs; have hgarb' := hold_garb _ hrs.1; have hlits' := hold_lits _ hrs.1
        exact ⟨hrefs' ▸ List.mem_append_left _ hrs.1, hgarb'.trans hrs.2.1,
          fun q hq => hrs.2.2 q (hlits' ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hlg0 : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 := hlg
      have hrs := hw.reason_inv idx hidx hne0
      have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg0 h
      rw [ite_eq_right hb] at hrs
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl]
      exact hold_lits _ hrs.1 ▸ hw.reason_lit_mem idx hidx hne0 hlg0 }⟩

/-- Chronological assignment (`full_decide` and `full_assign_lvl`) preserving `FullCoreInv`. -/
theorem chronoAssign_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {lit rsn : BitVec 32} {alvl cur_level' propagated' : Nat}
    {flags' frame_trail' frame_dec' : List (BitVec 32)}
    {unassigned' unflushed' : BitVec 64} {scratch' : FullScratch}
    (hsok' : scratch'.LengthsOk c) (hfll : flags'.length = c.max_vars)
    (hftl : frame_trail'.length = c.max_vars + 1) (hfdl : frame_dec'.length = c.max_vars + 1)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (halvl_le : alvl ≤ cur_level') (hprop_le : propagated' ≤ s.core.trail_end + 1)
    (hcur_le : cur_level' ≤ s.core.trail_end + 1)
    (hft_lt : ∀ L ≤ cur_level', (frame_trail'[L]?.getD 0#32).toNat ≤ s.core.trail_end + 1)
    (hft_mono : ∀ L1 L2, L1 ≤ L2 → L2 ≤ cur_level' →
      (frame_trail'[L1]?.getD 0#32).toNat ≤ (frame_trail'[L2]?.getD 0#32).toNat)
    (hft_bef : ∀ L, 1 ≤ L → L ≤ cur_level' →
      ∀ i < (frame_trail'[L]?.getD 0#32).toNat,
        (if i = s.core.trail_end then alvl
         else if (s.core.trl[i]?.getD 0#32).toNat / 2 = lit.toNat / 2 then alvl
         else (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) < L)
    (hfd_lt : ∀ L, 1 ≤ L → L ≤ cur_level' → (frame_dec'[L]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hlvl_old_le : ∀ i < s.core.trail_end,
      (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ cur_level')
    (hinhab : ∀ L, 1 ≤ L → L ≤ cur_level' →
      L = alvl ∨
        ∃ i < s.core.trail_end,
          (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L)
    (hdec_fresh : 0 < alvl → rsn = 0xFFFFFFFF#32 →
      ∀ i < s.core.trail_end,
        (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ alvl)
    (hl0 : alvl = 0 → ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hrsn : 0 < alvl → rsn ≠ 0xFFFFFFFF#32 → ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot]) ∧
        ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ alvl
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
          q = lit.toNat ∨ ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ alvl)
    (hrsn_mem : 0 < alvl → rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      lit.toNat ∈ fullArenaClauseLitsCore s.core rsn.toNat := by
      intro _ _ hlg; first | contradiction | (have := congrArg (·[31]) hlg; simp_all) | simp_all) :
    let v := lit.toNat / 2
    let rsn' := if alvl = 0 then 0xFFFFFFFF#32 else rsn
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 alvl)
            rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := frame_trail', frame_dec := frame_dec'
            trail_end := s.core.trail_end + 1, propagated := propagated'
            cur_level := cur_level', unassigned := unassigned', unflushed := unflushed' }
        scratch := scratch' }
    FullCoreInv c F0 s' := by
  intro v rsn' s'
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hcl := hinv.lengths.core_ok
  have hcv' : s'.core.cur_vars = s.core.cur_vars := rfl
  have hte' : s'.core.trail_end = s.core.trail_end + 1 := rfl
  have hclv' : s'.core.cur_level = cur_level' := rfl
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * s.core.cur_vars := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have halvl_lt32 : alvl < 2 ^ 32 := by
    have := fullInv_max_vars_lt32 c; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat :=
    fun i _ => by
      by_cases he : i = s.core.trail_end
      · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
      · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars,
      (s'.core.lvl[w]?.getD 0#32).toNat =
        if w = v then alvl else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt),
        bv32_ofNat_toNat halvl_lt32]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars,
      s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
        if w = v then rsn' else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
      vals_len := by simp [s', hcl.vals_len], flags_len := hfll,
      lvl_len := by simp [s', hcl.lvl_len], rsns_len := by simp [s', hcl.rsns_len],
      trl_len := by simp [s', hcl.trl_len], trail_pos_len := by simp [s', hcl.trail_pos_len],
      frame_trail_len := hftl, frame_dec_len := hfdl,
      trail_end_le := by dsimp [s']; omega, propagated_le := hprop_le }, hsok'⟩
  refine ⟨hlen', F_cur, {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := hcur_le
    trail_lits_lt := fun i hi => by
      rw [htrl_get i (hte' ▸ hi)]; split
      · exact hlit
      · exact hw.trail_lits_lt i (by rw [hte'] at hi; omega)
    trail_vars_nodup := fun i j hi hj hveq => by
      rw [hte'] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      rw [hcv'] at hl; rw [hvals_get l hl]
      split; · exact Or.inr (Or.inr rfl)
      split; · exact Or.inr (Or.inl rfl)
      exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      rw [hcv'] at hl; rw [hvals_get l hl, hte']
      constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      rw [hcv'] at hl; rw [hvals_get l hl, hte']
      constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨s.core.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq
          have hl_eq : l = lit.toNat ^^^ 1 := by
            have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
            rw [h1] at h; exact h.symm
          simp [hl_eq]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by
            have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
    lvl_le := fun i hi => by
      rw [hte'] at hi; rw [hclv', htrl_get i hi]
      by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simpa using halvl_le
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]
        rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
        simp only [hnot_var i hilt, ↓reduceIte]; exact hlvl_old_le i hilt
    dec_earliest := fun i j hi hj hleq hdec => by
      rw [hte'] at hi hj
      rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
      by_cases hje : j = s.core.trail_end
      · subst hje; simp only [↓reduceIte] at hleq hdec
        rw [hlvl_get v (by omega), hrsn_get v (by omega)] at hdec; simp only [↓reduceIte] at hdec
        have hal0 : alvl ≠ 0 := by omega
        have hrsn_dec : rsn = 0xFFFFFFFF#32 := by simpa [rsn', hal0] using hdec.2
        by_cases hie : i = s.core.trail_end
        · omega
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hleq
          rw [hlvl_get v (by omega),
            hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hleq
          simp only [hnot_var i hilt, ↓reduceIte] at hleq
          exact absurd hleq (hdec_fresh hdec.1 hrsn_dec i hilt)
      · by_cases hie : i = s.core.trail_end
        · omega
        · have hilt : i < s.core.trail_end := by omega
          have hjlt : j < s.core.trail_end := by omega
          simp only [hie, hje, ↓reduceIte] at hleq hdec
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega),
            hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hleq
          rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega),
            hrsn_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hdec
          simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
          exact hw.dec_earliest i j hilt hjlt hleq hdec
    levels_inhabited := fun L hL1 hLle => by
      rw [hclv'] at hLle; rw [hte']
      rcases hinhab L hL1 hLle with rfl | ⟨i, hi, hli⟩
      · refine ⟨s.core.trail_end, by omega, ?_⟩
        rw [htrl_get _ (by omega)]; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp
      · refine ⟨i, by omega, ?_⟩
        rw [htrl_get i (by omega)]; simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte]
        rw [hlvl_get _ (by have := hw.trail_lits_lt i hi; omega)]; simp [hnot_var i hi, hli]
    level0_sound := fun i hi hli => by
      rw [hte'] at hi; rw [htrl_get i hi] at hli ⊢
      by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli; exact hl0 hli F_cur hw
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hli
        simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hw.level0_sound i hilt hli
    trail_pos_inv := fun i hi => by
      rw [hte'] at hi; rw [htrl_get i hi]
      by_cases hie : i = s.core.trail_end
      · subst hie; simp only [↓reduceIte]; dsimp only [s']
        rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat hte_lt32]
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]
        have hnv := hnot_var i hilt
        dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hnv)]; exact hw.trail_pos_inv i hilt
    level0_rsn_none := fun idx hidx hli => by
      rw [hte'] at hidx; rw [htrl_get idx hidx] at hli ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli
        rw [hrsn_get v (by omega)]; simp [rsn', hli]
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢
        have hnv := hnot_var idx hilt
        rw [hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hli
        simp only [hnv, ↓reduceIte] at hli
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
        simp only [hnv, ↓reduceIte]; exact hw.level0_rsn_none idx hilt hli
    frame_trail_lt := hft_lt
    frame_trail_mono := hft_mono
    frame_trail_before_lt := fun L hL1 hLle i hi => by
      rw [hclv'] at hLle
      have hi_le : i < s.core.trail_end + 1 := Nat.lt_of_lt_of_le hi (hft_lt L hLle)
      have hb := hft_bef L hL1 hLle i hi
      change _ < L at ⊢
      rw [htrl_get i hi_le]
      by_cases hie : i = s.core.trail_end
      · subst hie; simp only [↓reduceIte] at hb ⊢; rw [hlvl_get v (by omega)]; simpa using hb
      · have hilt : i < s.core.trail_end := by omega
        have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v := hnot_var i hilt
        have hnv' : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := hnv
        simp only [hie, ↓reduceIte] at hb ⊢
        rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
        rw [ite_eq_right hnv'] at hb; rw [ite_eq_right hnv]; exact hb
    frame_dec_lt := hfd_lt
    reason_inv := fun idx hidx hne => by
      rw [hte'] at hidx
      rw [htrl_get idx hidx] at hne ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne ⊢
        rw [hrsn_get v (by omega)] at hne ⊢; simp only [↓reduceIte] at hne ⊢
        by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · have halpos : 0 < alvl := Nat.zero_lt_of_ne_zero hal0
          have hrs := hrsn halpos (by simpa [rsn', hal0] using hne) F_cur hw
          simp only [rsn', hal0, ↓reduceIte] at hne hrs ⊢
          by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
          · rw [ite_eq_left hbin] at hrs ⊢
            obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
            refine ⟨hrs.1, hrs.2.1, m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
            · have hot_v : (rsn &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
                intro heqv; have hme := hnot_var m hm; rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get v (by omega), hlvl_get _ (by omega)]
              rw [ite_eq_left rfl, ite_eq_right hot_v]; exact hlvl_le
          · rw [ite_eq_right hbin] at hrs ⊢
            refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
            have hq' : q ∈ fullArenaClauseLitsCore s.core rsn.toNat := by
              simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using hq
            refine (hrs.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ⟨m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
            · have hq_lt : q < 2 * s.core.cur_vars := hw.arena.lits_lt _ hrs.1 hrs.2.1 q hq'
              have hqv : q / 2 ≠ v := by
                intro heqv; have hme := hnot_var m hm; rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get v (by omega), hlvl_get _ (by omega)]; simpa [hqv] using hlvl_le
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne ⊢; have hnv := hnot_var idx hilt
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne ⊢
        simp only [hnv, ↓reduceIte] at hne ⊢
        have hrs := hw.reason_inv idx hilt hne
        by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢
          obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
          refine ⟨hrs.1, hrs.2.1, m, hm, ?_, ?_⟩
          · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
          · have hot_v : ((s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
              intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
              exact hme (by simpa [fullInv_var_xor1] using heqv)
            rw [hlvl_get _ (by omega), hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
            rw [ite_eq_right hot_v, ite_eq_right hnv]; exact hlvl_le
        · rw [ite_eq_right hbin] at hrs ⊢
          refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
          have hq' : q ∈ fullArenaClauseLitsCore s.core
              (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32).toNat := by
            simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using hq
          refine (hrs.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ⟨m, hm, ?_, ?_⟩
          · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
          · have hq_lt : q < 2 * s.core.cur_vars := hw.arena.lits_lt _ hrs.1 hrs.2.1 q hq'
            have hqv : q / 2 ≠ v := by
              intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
              exact hme (by simpa [fullInv_var_xor1] using heqv)
            rw [hlvl_get _ (by omega), hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
            simpa [hnv, hqv] using hlvl_le
    reason_lit_mem := fun idx hidx hne hlg => by
      rw [hte'] at hidx; rw [htrl_get idx hidx] at hne hlg ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne hlg ⊢
        rw [hrsn_get v (by omega)] at hne hlg ⊢; simp only [↓reduceIte] at hne hlg ⊢
        by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · simp only [rsn', hal0, ↓reduceIte] at hne hlg ⊢
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
            hrsn_mem (Nat.zero_lt_of_ne_zero hal0) hne hlg
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne hlg ⊢; have hnv := hnot_var idx hilt
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne hlg ⊢
        simp only [hnv, ↓reduceIte] at hne hlg ⊢
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
          hw.reason_lit_mem idx hilt hne hlg }⟩

private theorem filter_range_strictMono {n : Nat} {p : Nat → Bool}
    {i j : Nat} (hi : i < ((List.range n).filter p).length)
    (hj : j < ((List.range n).filter p).length) (hij : i < j) :
    ((List.range n).filter p)[i] < ((List.range n).filter p)[j] :=
  (List.pairwise_iff_getElem.mp (List.Pairwise.sublist List.filter_sublist
    List.pairwise_lt_range)) i j hi hj hij

/-- Chronological backtracking (`full_backtrack` to `target_lvl < cur_level`):
starting at `q_start = min frame_trail[target_lvl + 1] trail_end` and keeping trail entries with
`lvl ≤ target_lvl` while clearing popped variables preserves `FullCoreInv`. -/
theorem chronoBacktrack_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {target_lvl trail_end' propagated' : Nat}
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' trail_pos' : List (BitVec 32)}
    {unassigned' : BitVec 64} {scratch' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := trail_pos', trail_end := trail_end',
                            propagated := propagated', cur_level := target_lvl,
                            unassigned := unassigned' }
      scratch := scratch' } : FullState).LengthsOk c)
    (hlt : target_lvl < s.core.cur_level)
    (htrl_eq : ∀ i < trail_end',
      (trl'[i]?.getD 0#32).toNat =
        let q_start := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
        let keptTail := ((s.core.trl.take s.core.trail_end).drop q_start).filter fun lit =>
          decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)
        (((s.core.trl.take q_start ++ keptTail)[i]?).getD 0#32).toNat)
    (hte_len :
      let q_start := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
      let keptTail := ((s.core.trl.take s.core.trail_end).drop q_start).filter fun lit =>
        decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)
      trail_end' = (s.core.trl.take q_start ++ keptTail).length)
    (hvals_eq : ∀ l < 2 * s.core.cur_vars,
      vals'[l]?.getD 0#8 =
        if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl then s.core.vals[l]?.getD 0#8 else 0#8)
    (hlvl_eq : ∀ v < s.core.cur_vars,
      lvl'[v]?.getD 0#32 =
        if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then s.core.lvl[v]?.getD 0#32 else 0#32)
    (hrsn_eq : ∀ v < s.core.cur_vars,
      rsns'[v]?.getD 0xFFFFFFFF#32 =
        if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then
          s.core.rsns[v]?.getD 0xFFFFFFFF#32 else 0xFFFFFFFF#32)
    (htpos_eq : ∀ i < trail_end',
      (trail_pos'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i) :
    FullCoreInv c F0
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := trail_pos', trail_end := trail_end',
                              propagated := propagated', cur_level := target_lvl,
                              unassigned := unassigned' }
        scratch := scratch' } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := trail_pos', trail_end := trail_end',
                            propagated := propagated', cur_level := target_lvl,
                            unassigned := unassigned' }
      scratch := scratch' }
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hcl := hinv.lengths.core_ok
  have hte' : s'.core.trail_end = trail_end' := rfl
  have hcv' : s'.core.cur_vars = s.core.cur_vars := rfl
  have hclv' : s'.core.cur_level = target_lvl := rfl
  let q_start := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
  let keepPred : Nat → Bool := fun j =>
    decide ((s.core.lvl[(s.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl)
  let keptIdx := (List.range s.core.trail_end).filter keepPred
  have hq_le : q_start ≤ s.core.trail_end := Nat.min_le_right _ _
  have htrl_le : s.core.trail_end ≤ s.core.trl.length := by
    have := hcl.trail_end_le; have := hcl.cur_vars_le; have := hcl.trl_len; omega
  have hpref_keep : ∀ j < q_start, keepPred j = true := fun j hj => by
    have hbef := hw.frame_trail_before_lt (target_lvl + 1) (by omega) (by omega) j
      (by omega : j < (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat)
    simp only [keepPred, decide_eq_true_eq]; omega
  have htake_eq : s.core.trl.take s.core.trail_end =
      (List.range s.core.trail_end).map fun j => s.core.trl[j]?.getD 0#32 := by
    apply List.ext_getElem
    · simp [List.length_take, Nat.min_eq_left htrl_le]
    · intro j hj1 _; simp only [List.length_take, Nat.min_eq_left htrl_le] at hj1
      simp only [List.getElem_take, List.getElem_map, List.getElem_range]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsplit_range : List.range s.core.trail_end =
      List.range q_start ++ (List.range (s.core.trail_end - q_start)).map (· + q_start) := by
    have hsum : s.core.trail_end = q_start + (s.core.trail_end - q_start) := by omega
    conv => lhs; rw [hsum, List.range_add]
    congr 1; apply List.map_congr_left; intro x _; omega
  have hkeep_eq :
      s.core.trl.take q_start ++
        ((s.core.trl.take s.core.trail_end).drop q_start).filter
          (fun lit => decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)) =
      keptIdx.map (fun j => s.core.trl[j]?.getD 0#32) := by
    have ht1 : s.core.trl.take q_start =
        (List.range q_start).map fun j => s.core.trl[j]?.getD 0#32 := by
      apply List.ext_getElem
      · simp [List.length_take, Nat.min_eq_left (by omega : q_start ≤ s.core.trl.length)]
      · intro j hj1 _; simp only [List.length_take,
          Nat.min_eq_left (by omega : q_start ≤ s.core.trl.length)] at hj1
        simp only [List.getElem_take, List.getElem_map, List.getElem_range]
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have ht2 : (s.core.trl.take s.core.trail_end).drop q_start =
        ((List.range (s.core.trail_end - q_start)).map (· + q_start)).map
          fun j => s.core.trl[j]?.getD 0#32 := by
      apply List.ext_getElem
      · simp [List.length_drop, List.length_take, Nat.min_eq_left htrl_le]
      · intro j hj1 _
        simp only [List.length_drop, List.length_take, Nat.min_eq_left htrl_le] at hj1
        simp only [List.getElem_drop, List.getElem_take, List.getElem_map, List.getElem_range]
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        congr 1; omega
    have hf1 : (List.range q_start).filter keepPred = List.range q_start :=
      List.filter_eq_self.mpr fun j hj => hpref_keep j (List.mem_range.mp hj)
    have hf2 :
        (((List.range (s.core.trail_end - q_start)).map (· + q_start)).map
            fun j => s.core.trl[j]?.getD 0#32).filter
          (fun lit => decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)) =
        (((List.range (s.core.trail_end - q_start)).filter
            fun t => keepPred (t + q_start)).map (· + q_start)).map
          fun j => s.core.trl[j]?.getD 0#32 := by
      rw [List.filter_map, List.filter_map]; rfl
    rw [ht1, ht2, hf2, ← List.map_append]; congr 1
    dsimp only [keptIdx]; conv => rhs; rw [hsplit_range, List.filter_append, hf1, List.filter_map]
    rfl
  have hte_eq : trail_end' = keptIdx.length := by rw [hte_len, hkeep_eq, List.length_map]
  have htrl_idx : ∀ i (hi : i < trail_end'),
      (trl'[i]?.getD 0#32).toNat = (s.core.trl[keptIdx[i]'(hte_eq ▸ hi)]?.getD 0#32).toNat :=
    fun i hi => by
      have he := htrl_eq i hi; dsimp only at he; rw [he, hkeep_eq]
      simp [List.getElem?_map, List.getElem?_eq_getElem (hte_eq ▸ hi)]
  have hkept_pred : ∀ i (hi : i < trail_end'),
      (s.core.lvl[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl := fun i hi => by
    rw [htrl_idx i hi]
    have hm : keptIdx[i]'(hte_eq ▸ hi) ∈ (List.range s.core.trail_end).filter keepPred :=
      List.getElem_mem (l := keptIdx) (hte_eq ▸ hi)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hkept_lt : ∀ i (hi : i < trail_end'), keptIdx[i]'(hte_eq ▸ hi) < s.core.trail_end :=
    fun i hi => by
      have hm : keptIdx[i]'(hte_eq ▸ hi) ∈ (List.range s.core.trail_end).filter keepPred :=
        List.getElem_mem (l := keptIdx) (hte_eq ▸ hi)
      exact List.mem_range.mp (List.mem_filter.mp hm).1
  have hlvl_kept : ∀ i (hi : i < trail_end'),
      (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        (s.core.lvl[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := fun i hi => by
    have hlt_v : (trl'[i]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
      rw [htrl_idx i hi]; exact Nat.div_lt_of_lt_mul (hw.trail_lits_lt _ (hkept_lt i hi))
    rw [hlvl_eq _ hlt_v, ite_eq_left (hkept_pred i hi)]
  have hof_mem : ∀ m < s.core.trail_end,
      (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl →
      ∃ i, ∃ (hi : i < trail_end'), keptIdx[i]'(hte_eq ▸ hi) = m := fun m hm hml => by
    have hmem : m ∈ keptIdx :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hm, decide_eq_true hml⟩
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨i, hte_eq ▸ hi, heq⟩
  have hold_lits_lt : ∀ i < trail_end', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
    fun i hi => by rw [htrl_idx i hi]; exact hw.trail_lits_lt _ (hkept_lt i hi)
  have hsub_ex : ∀ {p : Nat},
      (∃ i < trail_end', (trl'[i]?.getD 0#32).toNat = p) ↔
      (∃ j < s.core.trail_end, (s.core.trl[j]?.getD 0#32).toNat = p ∧
        (s.core.lvl[p / 2]?.getD 0#32).toNat ≤ target_lvl) := by
    intro p; constructor
    · rintro ⟨i, hi, heq⟩
      have hkp := hkept_pred i hi; rw [heq] at hkp
      rw [htrl_idx i hi] at heq
      exact ⟨keptIdx[i]'(hte_eq ▸ hi), hkept_lt i hi, heq, hkp⟩
    · rintro ⟨j, hj, heq, hkp⟩
      obtain ⟨i, hi, hieq⟩ := hof_mem j hj (by rwa [heq])
      exact ⟨i, hi, by rw [htrl_idx i hi, hieq, heq]⟩
  have hft_le_old : ∀ L ≤ target_lvl, (s.core.frame_trail[L]?.getD 0#32).toNat ≤ q_start :=
    fun L hL => Nat.le_min.mpr
      ⟨hw.frame_trail_mono L (target_lvl + 1) (by omega) (by omega), hw.frame_trail_lt L (by omega)⟩
  have hkeep_pref_idx : ∀ j < q_start,
      ∃ i, ∃ (hi : i < trail_end'), keptIdx[i]'(hte_eq ▸ hi) = j ∧ i = j := fun j hj => by
    have hk_eq : (List.range q_start).filter keepPred = List.range q_start :=
      List.filter_eq_self.mpr fun x hx => hpref_keep x (List.mem_range.mp hx)
    have hsplit_k : keptIdx = List.range q_start ++
        ((List.range (s.core.trail_end - q_start)).map (· + q_start)).filter keepPred := by
      dsimp only [keptIdx]; rw [hsplit_range, List.filter_append, hk_eq]
    have hj_len : j < keptIdx.length := by
      rw [hsplit_k, List.length_append, List.length_range]; omega
    refine ⟨j, hte_eq ▸ hj_len, ?_, rfl⟩
    simp only [hsplit_k, List.getElem_append_left (by rw [List.length_range]; exact hj),
      List.getElem_range]
  have hinhab' : ∀ L, 1 ≤ L → L ≤ target_lvl →
      ∃ i < trail_end', (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L := by
    intro L hL1 hLle
    obtain ⟨j, hj, hlj⟩ := hw.levels_inhabited L hL1 (by omega)
    obtain ⟨i, hi, hieq⟩ := hof_mem j hj (by omega)
    exact ⟨i, hi, by rw [hlvl_kept i hi, htrl_idx i hi, hieq, hlj]⟩
  have hft_lt' : ∀ L ≤ target_lvl, (s.core.frame_trail[L]?.getD 0#32).toNat ≤ trail_end' := by
    intro L hL; have h1 := hft_le_old L hL
    have h2 : (s.core.trl.take q_start).length = q_start := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    dsimp only [q_start] at h1 h2; rw [hte_len]; rw [List.length_append, h2]; omega
  refine ⟨hlen', F_cur, {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := le_of_surj_range1
      (fun i => (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) hinhab'
    trail_lits_lt := hold_lits_lt
    trail_vars_nodup := fun i j hi hj hveq => by
      rw [hte'] at hi hj; rw [htrl_idx i hi, htrl_idx j hj] at hveq
      have hidx_eq := hw.trail_vars_nodup _ _ (hkept_lt i hi) (hkept_lt j hj) hveq
      by_cases hne : i = j
      · exact hne
      · rcases Nat.lt_or_gt_of_ne hne with h1 | h2
        · exact absurd hidx_eq
            (Nat.ne_of_lt (filter_range_strictMono (hte_eq ▸ hi) (hte_eq ▸ hj) h1))
        · exact absurd hidx_eq.symm
            (Nat.ne_of_lt (filter_range_strictMono (hte_eq ▸ hj) (hte_eq ▸ hi) h2))
    vals_domain := fun l hl => by
      rw [hvals_eq l (hcv' ▸ hl)]; split; exact hw.vals_domain l (hcv' ▸ hl); exact Or.inl rfl
    vals_true_iff := fun l hl => by
      rw [hcv'] at hl; rw [hvals_eq l hl, hte', hsub_ex]
      by_cases hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl
      · simp only [hlv, ↓reduceIte, and_true]; exact hw.vals_true_iff l hl
      · simp only [hlv, ↓reduceIte, and_false, exists_const, iff_false]; intro hf; cases hf
    vals_false_iff := fun l hl => by
      rw [hcv'] at hl; rw [hvals_eq l hl, hte', hsub_ex, fullInv_var_xor1]
      by_cases hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl
      · simp only [hlv, ↓reduceIte, and_true]; exact hw.vals_false_iff l hl
      · simp only [hlv, ↓reduceIte, and_false, exists_const, iff_false]; intro hf; cases hf
    lvl_le := fun i hi => by rw [hte'] at hi; rw [hclv', hlvl_kept i hi]; exact hkept_pred i hi
    dec_earliest := fun i j hi hj hleq hdec => by
      rw [hte'] at hi hj; dsimp only at hleq hdec ⊢
      rw [hlvl_kept i hi, hlvl_kept j hj] at hleq; rw [hlvl_kept j hj] at hdec
      have hjv : (trl'[j]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
        Nat.div_lt_of_lt_mul (hold_lits_lt j hj)
      rw [hrsn_eq _ hjv, ite_eq_left (hkept_pred j hj)] at hdec
      rw [htrl_idx i hi, htrl_idx j hj] at hleq
      rw [htrl_idx j hj] at hdec
      have hjk := hw.dec_earliest _ _ (hkept_lt i hi) (hkept_lt j hj) hleq hdec
      by_cases hij : j ≤ i
      · exact hij
      · have hstrict : keptIdx[i]'(hte_eq ▸ hi) < keptIdx[j]'(hte_eq ▸ hj) :=
          @filter_range_strictMono s.core.trail_end keepPred i j
            (hte_eq ▸ hi) (hte_eq ▸ hj) (Nat.lt_of_not_le hij)
        omega
    levels_inhabited := hinhab'
    level0_sound := fun i hi hl0 => by
      rw [hte'] at hi; rw [hlvl_kept i hi] at hl0; rw [htrl_idx i hi] at hl0 ⊢
      exact hw.level0_sound _ (hkept_lt i hi) hl0
    trail_pos_inv := htpos_eq
    level0_rsn_none := fun idx hidx hl0 => by
      rw [hte'] at hidx
      rw [show s'.core.trl = trl' from rfl, show s'.core.lvl = lvl' from rfl] at hl0
      rw [show s'.core.trl = trl' from rfl, show s'.core.rsns = rsns' from rfl]
      rw [hlvl_kept idx hidx] at hl0
      have hv : (trl'[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
        Nat.div_lt_of_lt_mul (hold_lits_lt idx hidx)
      rw [hrsn_eq _ hv, ite_eq_left (hkept_pred idx hidx)]
      rw [htrl_idx idx hidx] at hl0 ⊢
      exact hw.level0_rsn_none _ (hkept_lt idx hidx) hl0
    frame_trail_lt := hft_lt'
    frame_trail_mono := fun L1 L2 h1 h2 =>
      hw.frame_trail_mono L1 L2 h1 (by rw [hclv'] at h2; omega)
    frame_trail_before_lt := fun L hL1 hLle i hi => by
      rw [hclv'] at hLle
      have hfq := Nat.lt_of_lt_of_le hi (hft_le_old L hLle)
      obtain ⟨i', hi', hieq, hii'⟩ := hkeep_pref_idx i hfq
      rw [show s'.core.trl = trl' from rfl, show s'.core.lvl = lvl' from rfl]
      rw [← hii', hlvl_kept i' hi', htrl_idx i' hi', hieq]
      exact hw.frame_trail_before_lt L hL1 (by omega) i hi
    frame_dec_lt := fun L hL1 hLle => by
      rw [hclv'] at hLle; exact hw.frame_dec_lt L hL1 (by omega)
    reason_inv := fun idx hidx hne => by
      rw [hte'] at hidx
      rw [show s'.core.trl = trl' from rfl, show s'.core.rsns = rsns' from rfl] at hne
      rw [show s'.core.trl = trl' from rfl, show s'.core.rsns = rsns' from rfl,
        show s'.core.lvl = lvl' from rfl, show s'.core.cur_vars = s.core.cur_vars from rfl,
        show fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core from rfl,
        show fullArenaClauseGarbCore s'.core = fullArenaClauseGarbCore s.core from rfl,
        show fullArenaClauseLitsCore s'.core = fullArenaClauseLitsCore s.core from rfl]
      have hv : (trl'[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
        Nat.div_lt_of_lt_mul (hold_lits_lt idx hidx)
      have hkp := hkept_pred idx hidx
      rw [hrsn_eq _ hv, ite_eq_left hkp, htrl_idx idx hidx] at hne ⊢
      have hv_kept : (s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD 0#32).toNat / 2 <
          s.core.cur_vars := by rw [← htrl_idx idx hidx]; exact hv
      have hkp_kept : (s.core.lvl[(s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD
          0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl := by
        rw [← htrl_idx idx hidx]; exact hkp
      have hrs := hw.reason_inv _ (hkept_lt idx hidx) hne
      by_cases hbin : (s.core.rsns[(s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hbin] at hrs ⊢
        obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
        have hmt : (s.core.lvl[((s.core.rsns[(s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD
            0#32).toNat / 2]?.getD 0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2]?.getD
            0#32).toNat ≤ target_lvl := by
          have := hkp; rw [htrl_idx idx hidx] at this; omega
        have hm_p : (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            target_lvl := by rw [hmeq, fullInv_var_xor1]; exact hmt
        obtain ⟨m', hm', hm'_eq⟩ := hof_mem m (by have := hkept_lt idx hidx; omega) hm_p
        have hm'_lt : m' < idx := by
          by_cases hlt_mi : m' < idx
          · exact hlt_mi
          · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hlt_mi) with rfl | hgt
            · omega
            · have hs : keptIdx[idx]'(hte_eq ▸ hidx) < keptIdx[m']'(hte_eq ▸ hm') :=
                @filter_range_strictMono s.core.trail_end keepPred idx m'
                  (hte_eq ▸ hidx) (hte_eq ▸ hm') hgt
              omega
        have hot_v : ((s.core.rsns[(s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD
            0#32).toNat / 2]?.getD 0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2 <
            s.core.cur_vars := Nat.div_lt_of_lt_mul hrs.1
        refine ⟨hrs.1, hrs.2.1, m', hm'_lt, by rw [htrl_idx m' hm', hm'_eq, hmeq], ?_⟩
        rw [hlvl_eq _ hot_v, ite_eq_left hmt, hlvl_eq _ hv_kept, ite_eq_left hkp_kept]
        exact hlvl_le
      · rw [ite_eq_right hbin] at hrs ⊢
        refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
        refine (hrs.2.2 q hq).elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ?_
        have hmt : (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ target_lvl := by
          have := hkp; rw [htrl_idx idx hidx] at this; omega
        have hm_p : (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            target_lvl := by rw [hmeq, fullInv_var_xor1]; exact hmt
        obtain ⟨m', hm', hm'_eq⟩ := hof_mem m (by have := hkept_lt idx hidx; omega) hm_p
        have hm'_lt : m' < idx := by
          by_cases hlt_mi : m' < idx
          · exact hlt_mi
          · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hlt_mi) with rfl | hgt
            · omega
            · have hs : keptIdx[idx]'(hte_eq ▸ hidx) < keptIdx[m']'(hte_eq ▸ hm') :=
                @filter_range_strictMono s.core.trail_end keepPred idx m'
                  (hte_eq ▸ hidx) (hte_eq ▸ hm') hgt
              omega
        have hqv : q / 2 < s.core.cur_vars :=
          Nat.div_lt_of_lt_mul (hw.arena.lits_lt _ hrs.1 hrs.2.1 q hq)
        refine ⟨m', hm'_lt, by rw [htrl_idx m' hm', hm'_eq, hmeq], ?_⟩
        rw [hlvl_eq _ hqv, ite_eq_left hmt, hlvl_eq _ hv_kept, ite_eq_left hkp_kept]
        exact hlvl_le
    reason_lit_mem := fun idx hidx hne hlg => by
      rw [hte'] at hidx
      rw [show s'.core.trl = trl' from rfl, show s'.core.rsns = rsns' from rfl] at hne hlg
      rw [show s'.core.trl = trl' from rfl, show s'.core.rsns = rsns' from rfl,
        show fullArenaClauseLitsCore s'.core = fullArenaClauseLitsCore s.core from rfl]
      have hv : (trl'[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
        Nat.div_lt_of_lt_mul (hold_lits_lt idx hidx)
      rw [hrsn_eq _ hv, ite_eq_left (hkept_pred idx hidx), htrl_idx idx hidx] at hne hlg ⊢
      exact hw.reason_lit_mem _ (hkept_lt idx hidx) hne hlg }⟩

end LeanQbe.T.Examples.Kissat.Full
