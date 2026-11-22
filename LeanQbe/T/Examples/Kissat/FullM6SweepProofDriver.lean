module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofEls2
public import LeanQbe.T.Examples.Kissat.FullM4SweepProof
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import Kraken.Mem
public import Kraken.Separation

/-!
# `FullM6Sweep` Driver Proofs, `ModuleOk` Assembly, and Concrete Non-Vacuity

Proves the top-level driver functions of `LeanQbe.T.Examples.Kissat.FullM6Sweep`:
1. `full_m6_sweep_dense_wp` (`37/39`) + canonical `FullDefSweep.fullSweepDenseSpec` drop-in
   `full_m6_sweep_dense_canon_wp`, parameterized over `"full_m6_max_v"` and `"full_m6_sweep_vars"`.
2. `full_m6_sweep_sat_wp` (`38/39`), parameterized over its callees in `m6SweepSpecTable`.
3. `full_sweep_sat_m6_wp` (`39/39`), matching `Full.fullSweepSatSpec`.
4. `m6Sweep_tableImpl_of_parts` and `m6Sweep_moduleOk_of_parts`, assembling all 33 proved
   functions together with the 6 external `Var2a`/`Cands` hypotheses into `ModuleOk`.
5. Concrete `Mem 64` non-vacuity (`nv_m6_sweep_dense`, `nv_m6_sweep_sat`, `nv_full_sweep_sat_m6`)
   under `m6SweepEnv` with `XPost := fun _ _ _ _ => False`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM6Sweep.M6SweepTactics
open LeanQbe.T.Examples.Kissat.FullM4Sweep (m4SweepDenseSpec m4SweepSatSpec)
open LeanQbe.T.Examples.LratBytes (dimacsBound)

/-! ## 1. Small Structural & Invariant Helpers -/

private theorem m6_tmk_step {tmk : List (BitVec 32)} {i : Nat}
    (hlt : i < tmk.length)
    (hprev : ∀ v < i, tmk[v]?.getD 0#32 = 0#32) :
    (tmk.set i 0#32).length = tmk.length ∧
      ∀ v < i + 1, (tmk.set i 0#32)[v]?.getD 0#32 = 0#32 := by
  refine ⟨List.length_set, fun v hv => ?_⟩
  by_cases hvi : v = i
  · subst hvi
    rw [List.getElem?_set_self hlt, Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hvi)]
    exact hprev v (by omega)

private def m6WithTmk (s : FullState) (tmk' : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with tarjan_mark := tmk' } }

private theorem m6_denseInv_with_tmk {c : FullCfg} {F0 : Std.Sat.CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {tmk' : List (BitVec 32)}
    (hlen : tmk'.length = 2 * c.max_vars) :
    FullDenseInv c F0 (m6WithTmk s tmk') := by
  exact FullSweepVarHelpers.fullDenseInv_with_tmk hinv hlen

private theorem m6_fullSparseInv_after_backtrack {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInv c F0 s)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch} (s' : FullState)
    (hs' : s' = {
      core := { s.core with
        unassigned := unass', trail_end := te', propagated := prop', cur_level := cl',
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp' }
      scratch := sc' })
    (hlen' : FullState.LengthsOk c s')
    (hsc' : FullProbeScratchPres s s')
    (hw' : FullWitnessInv c F0 F_cur s'.core) :
    FullSparseInv c F0 s' := by
  rcases hsp with ⟨_, hlm, hnd, hsc0, hdm⟩
  have hll_eq : s'.scratch.last_learned = s.scratch.last_learned := hsc'.1.1
  have hel_eq : s'.scratch.extend_len = s.scratch.extend_len := hsc'.1.2
  have hcv : s'.core.cur_vars = s.core.cur_vars := by rw [hs']
  have hlm_eq : s'.core.lit_mark = s.core.lit_mark := by rw [hs']
  have hmrk_eq : s'.core.mrk = s.core.mrk := by rw [hs']
  have hal_eq : s'.core.arena_len = s.core.arena_len := by rw [hs']
  have har_eq : s'.core.arena = s.core.arena := by rw [hs']
  have hag_eq : s'.core.arena_garbage = s.core.arena_garbage := by rw [hs']
  have hdm' : s'.core.dense_mode = 0#64 := by rw [hs']; exact hdm
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨?_, ?_⟩, ?_, ?_, hdm'⟩
  · intro v hv
    simpa [FullSweepVarSpecs.FullMrkZero, hmrk_eq] using hlm.1 v hv
  · intro l hl
    simpa [hlm_eq] using hlm.2 l hl
  · intro r hr hgarb
    have hr0 : r ∈ fullArenaClauseRefs s := by
      rw [fullArenaClauseRefs, fullArenaClauseRefsCore, hal_eq, har_eq] at hr
      exact hr
    have hgarb0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hgarb ⊢
      rw [har_eq] at hgarb
      exact hgarb
    have hnd0 := hnd r hr0 hgarb0
    have hlits_eq : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
      rw [har_eq]
    simpa [hlits_eq] using hnd0
  · rcases hsc0 with ⟨hll0, hel0⟩
    refine ⟨?_, by omega⟩
    unfold FullLastLearnedWf at hll0 ⊢
    rw [hll_eq]
    simpa [fullArenaClauseRefs, fullArenaClauseRefsCore, hal_eq, har_eq] using hll0

private theorem m6_fullSparseInv_after_propagate {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInv c F0 s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64}
    {wvec' arena' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)}
    (s' : FullState)
    (hs' : s' = {
      core := { s.core with
        unassigned := unass', wlen := wlen', wusable := wu', unflushed := unfl',
        trail_end := te', propagated := prop', fuel := fuel', confl_ref := cref',
        confl_type := ctype', confl_lit0 := c0', confl_lit1 := c1', oom := oom',
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
        trail_pos := tp', wvec := wvec', arena := arena', wstk := wstk' }
      scratch := { s.scratch with
        search_ticks := ticks', phases := phases', wsort := wsort' } })
    (hlen' : FullState.LengthsOk c s')
    (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core) :
    FullSparseInv c F0 s' := by
  rcases hsp with ⟨_, hlm, hnd, hsc0, hdm⟩
  have hcv : s'.core.cur_vars = s.core.cur_vars := by rw [hs']
  have hlm_eq : s'.core.lit_mark = s.core.lit_mark := by rw [hs']
  have hmrk_eq : s'.core.mrk = s.core.mrk := by rw [hs']
  have hdm' : s'.core.dense_mode = 0#64 := by rw [hs']; exact hdm
  have hll_eq : s'.scratch.last_learned = s.scratch.last_learned := by rw [hs']
  have hel_eq : s'.scratch.extend_len = s.scratch.extend_len := by rw [hs']
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨?_, ?_⟩, ?_, ?_, hdm'⟩
  · intro v hv
    simpa [FullSweepVarSpecs.FullMrkZero, hmrk_eq] using hlm.1 v hv
  · intro l hl
    simpa [hlm_eq] using hlm.2 l hl
  · intro r hr hgarb
    have href : r ∈ fullArenaClauseRefs s := by
      simpa [fullArenaClauseRefs, hperm.2.1] using hr
    obtain ⟨_, hg_eq, hpl⟩ := hperm.2.2 r href
    have hgarb0 : fullArenaClauseGarb s r = false := by
      simpa [fullArenaClauseGarb, hg_eq] using hgarb
    have hnd0 := hnd r href hgarb0
    have hmap : (List.map (fun x => x / 2) (fullArenaClauseLits s' r)).Perm
        (List.map (fun x => x / 2) (fullArenaClauseLits s r)) := by
      simpa [fullArenaClauseLits] using hpl.map (fun x => x / 2)
    exact hmap.nodup_iff.mpr hnd0
  · rcases hsc0 with ⟨hll0, hel0⟩
    refine ⟨?_, by omega⟩
    unfold FullLastLearnedWf at hll0 ⊢
    rw [hll_eq]
    simpa [fullArenaClauseRefs, hperm.2.1] using hll0

private theorem m6_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : { name := nm, as := as, rs := bs, spec := sp, noExit := true } ∈ m6SweepSpecTable)
    (hnoEx : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    M6EnvSpec m6SweepEnv nm sp :=
  m6SweepEnv_row hmem hnoEx

private theorem m6_allFns_of_mem {P : Fn → Prop} {fs : List Fn}
    (h : ∀ f, f ∈ fs → P f) : AllFns P fs := by
  induction fs with
  | nil => trivial
  | cons f fs ih =>
    exact ⟨h f (List.Mem.head _), ih fun g hg => h g (List.Mem.tail _ hg)⟩

/-! ## 2. `full_m6_sweep_dense_wp` (`37/39`) -/

/-- `37/39`: Parametric `Func.wp` proof for `full_m6_sweep_dense` matching
    `FullM4Sweep.m4SweepDenseSpec`. Zero dependency on `Var2a` or `Cands`. -/
theorem full_m6_sweep_dense_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSweepVars : M6EnvSpec Γ "full_m6_sweep_vars" m6SweepVarsSpec) :
    ∀ args m Q X, m4SweepDenseSpec args m Q X →
      Func.wp Γ full_m6_sweep_dense_body args m Q X := by
  rintro ⟨h, budget, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hlen := hinv.lengths
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have htmk_len : s.scratch.tarjan_mark.length = 2 * c.max_vars :=
    hlen.scratch_ok.tarjan_mark_len
  have hmx := c.hmaxv
  unfold dimacsBound at hmx
  have hcv_lt64 : s.core.cur_vars < 2 ^ 63 := by omega
  have hm_ret1 : ∀ {m1 : Mem 64}, (FullMem c s ⋆ R) m1 → Q (1#64, ()) m1 :=
    fun hm1 => hQ 1#64 s _ hinv rfl (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm1
  c0_hsteps_nogrp
  refine m6_call_max_v hMaxV rfl ?_
  c0_hsplit
  · c0_hsteps!; exact hm_ret1 hm
  · c0_hsplit
    · c0_hsteps!; exact hm_ret1 hm
    · c0_hsplit
      · c0_hsteps!; exact hm_ret1 hm
      · c0_hsteps_nogrp
        refine wp_while_state1 (fun p : BitVec 64 × List (BitVec 32) => p.1)
          (fun p => s.core.cur_vars - p.1.toNat)
          (fun p ml =>
            p.1.toNat ≤ s.core.cur_vars ∧ p.2.length = 2 * c.max_vars ∧
              (∀ v < p.1.toNat, p.2[v]?.getD 0#32 = 0#32) ∧
              (FullMem c (m6WithTmk s p.2) ⋆ R) ml) ?_ ?_
        · intro L hL
          exact hL (0#64, s.scratch.tarjan_mark) m
            ⟨Nat.zero_le _, htmk_len, fun _ hv => by simp at hv, by simpa [m6WithTmk] using hm⟩
        · rintro L ⟨i, tmk⟩ ml ⟨hi_le, ht_len, ht_zero, hml⟩ ihL
          dsimp only at hi_le ht_len ht_zero hml ⊢
          c0_hsplit
          · have hi_lt : i.toNat < s.core.cur_vars := by bv_omega
            have hi_tlen : i.toNat < tmk.length := by omega
            have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
            have hstep := m6_tmk_step hi_tlen ht_zero
            c0_hsteps!
            exact ihL (i + 1#64, tmk.set i.toNat 0#32) _ (by dsimp only; rw [hi1]; omega)
              ⟨by dsimp only; rw [hi1]; omega, hstep.1.trans ht_len,
               by dsimp only; rw [hi1]; exact hstep.2, by simpa [m6WithTmk] using hm⟩
          · have hi_eq : i.toNat = s.core.cur_vars := by bv_omega
            let s0 := m6WithTmk s tmk
            have hinv0 : FullDenseInv c F0 s0 := m6_denseInv_with_tmk hinv ht_len
            have htmk0 : M6TmkZero s0 := fun v hv => ht_zero v (by rw [hi_eq]; exact hv)
            have hm0 : (FullMem c s0 ⋆ R) ml := hml
            c0_hsteps_nogrp
            refine wp_while_break_state
              (brkTs := [i64]) (lpTs := [i64]) (β := BitVec 64 × FullState)
              (fun b => (b.1, ()))
              (fun b mB => FullDenseInv c F0 b.2 ∧ b.2.core.cur_vars = s.core.cur_vars ∧
                b.2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c b.2 ⋆ R) mB)
              (α := BitVec 64 × FullState) (fun p => (p.1, ()))
              (fun p => 2 - p.1.toNat)
              (fun p mL => p.1.toNat ≤ 2 ∧ FullDenseInv c F0 p.2 ∧ M6TmkZero p.2 ∧
                p.2.core.cur_vars = s.core.cur_vars ∧
                p.2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c p.2 ⋆ R) mL)
              ?_ ?_ ?_
            · rintro B ⟨_, sB⟩ mB ⟨hinvB, hcvB, hfuelB, hmB⟩
              dsimp only at hinvB hcvB hfuelB hmB ⊢
              c0_hsteps_nogrp
              refine wp_join_state1 (t := i64) (α := BitVec 64) id
                (fun r mJ => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧
                  (FullMem c sB ⋆ R) mJ) ?_ ?_
              · rintro J r mJ ⟨hr, huns, hmJ⟩
                c0_hsteps!
                exact hQ r sB mJ hinvB hcvB hfuelB hr huns hmJ
              · intro J hJ
                c0_hsteps_nogrp
                c0_hsplit
                · have hinc : sB.core.inconsistent ≠ 0#64 := ‹_›
                  c0_hsteps!
                  exact hJ 20#64 mB ⟨Or.inr rfl, fun _ => hinvB.inconsistent_unsat hinc, hmB⟩
                · c0_hsteps!
                  exact hJ 1#64 mB ⟨Or.inl rfl, (fun h => by cases h), hmB⟩
            · rintro B L2 ⟨rd, sL⟩ mL ihB ihL2 ⟨hrd_le, hinvL, htmkL, hcvL, hfuelL, hmL⟩
              dsimp only at hrd_le hinvL htmkL hcvL hfuelL hmL ⊢
              c0_hsplit
              · have hrd_lt : rd.toNat < 2 := by bv_omega
                c0_hsplit
                · c0_hsplit
                  · c0_hsplit
                    · have hrd1 : (rd + 1#64).toNat = rd.toNat + 1 := by bv_omega
                      c0_hsteps_nogrp
                      c0_call hSweepVars
                      refine ⟨c, F0, sL, R, rfl, hinvL, htmkL, hmL,
                        fun rV sV mV hinvV hcvV hfuelV htmkV hrV hunsV hmV => ?_⟩
                      c0_hsplit
                      · have hr20 : rV = 20#64 := ‹_›
                        c0_hsteps!
                        exact hQ 20#64 sV mV hinvV (hcvV.trans hcvL) (Nat.le_trans hfuelV hfuelL)
                          (Or.inr rfl) (fun _ => hunsV hr20) hmV
                      · c0_hsteps_nogrp
                        c0_hsplit
                        · c0_hsteps!
                          exact ihB (rd, sV) mV
                            ⟨hinvV, hcvV.trans hcvL, Nat.le_trans hfuelV hfuelL, hmV⟩
                        · c0_hsteps!
                          exact ihL2 (rd + 1#64, sV) mV (by dsimp only; rw [hrd1]; omega)
                            ⟨by dsimp only; rw [hrd1]; omega, hinvV, htmkV, hcvV.trans hcvL,
                             Nat.le_trans hfuelV hfuelL, hmV⟩
                    · c0_hsteps!
                      exact ihB (rd, sL) mL ⟨hinvL, hcvL, hfuelL, hmL⟩
                  · c0_hsteps!
                    exact ihB (rd, sL) mL ⟨hinvL, hcvL, hfuelL, hmL⟩
                · c0_hsteps!
                  exact ihB (rd, sL) mL ⟨hinvL, hcvL, hfuelL, hmL⟩
              · c0_hsteps!
                exact ihB (rd, sL) mL ⟨hinvL, hcvL, hfuelL, hmL⟩
            · intro B L2 hB hL2
              exact wp_jump_state (proj := fun p : BitVec 64 × FullState => (p.1, ()))
                (0#64, s0) rfl
                (hL2 (0#64, s0) ml ⟨Nat.zero_le _, hinv0, htmk0, rfl, Nat.le_refl _, hm0⟩)

/-- Drop-in corollary proving `full_m6_sweep_dense` satisfies canonical
    `FullDefSweep.fullSweepDenseSpec` (definitionally equal to `FullM4Sweep.m4SweepDenseSpec`). -/
theorem full_m6_sweep_dense_canon_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSweepVars : M6EnvSpec Γ "full_m6_sweep_vars" m6SweepVarsSpec) :
    ∀ args m Q X, FullDefSweep.fullSweepDenseSpec args m Q X →
      Func.wp Γ full_m6_sweep_dense_body args m Q X :=
  full_m6_sweep_dense_wp Γ hMaxV hSweepVars

/-! ## 3. `full_m6_sweep_sat_wp` (`38/39`) and `full_sweep_sat_m6_wp` (`39/39`) -/

/-- `38/39`: Parametric `Func.wp` proof for `full_m6_sweep_sat` matching
    `FullM4Sweep.m4SweepSatSpec`. -/
theorem full_m6_sweep_sat_wp (Γ : Env)
    (hBt : M6EnvSpec Γ "full_backtrack" Full.fullBacktrackSpec)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hEnter : M6EnvSpec Γ "full_enter_dense" Full.fullEnterDenseSpec)
    (hDense : M6EnvSpec Γ "full_m6_sweep_dense" m4SweepDenseSpec)
    (hReb : M6EnvSpec Γ "full_rebuild_watches" Full.fullRebuildWatchesSpec)
    (hProp : M6EnvSpec Γ "full_propagate" Full.fullPropagateSpec)
    (hSubst : M6EnvSpec Γ "full_substitute" Full.fullSubstituteSpec) :
    ∀ args m Q X, m4SweepSatSpec args m Q X →
      Func.wp Γ full_m6_sweep_sat_body args m Q X := by
  rintro ⟨h, budget, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  c0_hsteps_nogrp
  refine wp_join0 (fun m0 => ∃ s0, FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0) ?_ ?_
  · rintro _ m0 ⟨s0, hsp0, hlvl0, hfuel0, hm0⟩
    c0_hsteps_nogrp
    refine m6_call_max_v hMaxV rfl ?_
    c0_hsplit
    · c0_hsteps!
      exact hQ 1#64 s0 m0 hsp0 hlvl0 hfuel0 (Or.inl rfl) (fun h => by cases h) hm0
    · c0_hsplit
      · c0_hsteps!
        exact hQ 1#64 s0 m0 hsp0 hlvl0 hfuel0 (Or.inl rfl) (fun h => by cases h) hm0
      · c0_hsteps_nogrp
        c0_call hEnter
        refine ⟨c, F0, s0, R, rfl, hsp0, hm0, fun ok s1 m1 hlvl1 hfuel1 hok_t hok_f hm1 => ?_⟩
        c0_hsplit
        · have hokt : ok = true := ‹_›
          have hinv1 : FullDenseInv c F0 s1 := hok_t hokt
          c0_hsteps_nogrp
          c0_call hDense
          refine ⟨c, F0, s1, R, rfl, hinv1, hm1,
            fun res s2 m2 hinv2 _ hfuel2 hres2 huns2 hm2 => ?_⟩
          c0_hsteps_nogrp
          c0_call hReb
          refine ⟨c, F0, s2, R, rfl, hinv2, hm2,
            fun rr s3 m3 hsp3 hlvl3 hfuel3 hrr3 huns3 hm3 => ?_⟩
          have hfuel3_le : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by
            rw [hfuel1] at hfuel2; exact Nat.le_trans hfuel3 (Nat.le_trans hfuel2 hfuel0)
          c0_hsteps_nogrp
          c0_hsplit
          · have hr20 : res = 20#64 := ‹_›
            c0_hsteps!
            exact hQ 20#64 s3 m3 hsp3 hlvl3 hfuel3_le (Or.inr rfl)
              (fun _ => huns2 hr20) hm3
          · have hrr20 : rr = 20#64 := ‹_›
            c0_hsteps!
            exact hQ 20#64 s3 m3 hsp3 hlvl3 hfuel3_le (Or.inr rfl)
              (fun _ => huns3 hrr20) hm3
          · have hc_ne : s3.core.inconsistent ≠ 0 := ‹_›
            have hinc3 : s3.core.inconsistent ≠ 0#64 := hc_ne
            c0_hsteps!
            exact hQ 20#64 s3 m3 hsp3 hlvl3 hfuel3_le (Or.inr rfl)
              (fun _ => hsp3.inconsistent_unsat hinc3) hm3
          · c0_hsteps_nogrp
            obtain ⟨F_cur3, hspW3⟩ := hsp3.exists_witness
            have hlen3 := hsp3.lengths
            have hw3 : FullWitnessInv c F0 F_cur3 s3.core := hspW3.2.1
            have hdm3 : s3.core.dense_mode = 0#64 := hsp3.2.2.2.2
            c0_call hProp
            refine ⟨c, F0, F_cur3, s3, R, rfl, hlen3, hw3, hdm3, hm3,
              fun rP vals4 flags4 lvl4 rsns4 trl4 tp4 te4 prop4 unass4 unfl4 wvec4 arena4
                wstk4 wlen4 wu4 fuel4 ctype4 cref4 c0_4 c1_4 oom4 ticks4 wsort4 phases4 m4
                hlen4 hw4 _ hperm4 hfuel4 hrP _ hrP1 _ _ hm4 => ?_⟩
            let s4 : FullState := {
              core := { s3.core with
                unassigned := unass4, wlen := wlen4, wusable := wu4, unflushed := unfl4,
                trail_end := te4, propagated := prop4, fuel := fuel4, confl_ref := cref4,
                confl_type := ctype4, confl_lit0 := c0_4, confl_lit1 := c1_4, oom := oom4,
                vals := vals4, flags := flags4, lvl := lvl4, rsns := rsns4, trl := trl4,
                trail_pos := tp4, wvec := wvec4, arena := arena4, wstk := wstk4 }
              scratch := { s3.scratch with
                search_ticks := ticks4, phases := phases4, wsort := wsort4 } }
            have hsp4 := m6_fullSparseInv_after_propagate hsp3 s4 rfl hlen4 hw4 hperm4
            have hfuel4_le : s4.core.fuel.toNat ≤ s.core.fuel.toNat :=
              Nat.le_trans hfuel4 hfuel3_le
            c0_hsplit
            · have hconf4 : FullConflictOkW F_cur3 s4 := (hrP1 ‹_›).2.2
              c0_hsteps!
              exact hQ 20#64 s4 m4 hsp4 hlvl3 hfuel4_le (Or.inr rfl)
                (fun _ => Full.level0_unsat_of_conflict_okW hw4 hlvl3 hconf4) hm4
            · c0_hsteps_nogrp
              c0_hsplit
              · c0_hsteps_nogrp
                c0_call hSubst
                refine ⟨c, F0, s4, R, rfl, hsp4, hm4,
                  fun rS s5 m5 hsp5 hlvl5 hfuel5 _ huns5 hm5 => ?_⟩
                have hfuel5_le : s5.core.fuel.toNat ≤ s.core.fuel.toNat :=
                  Nat.le_trans hfuel5 hfuel4_le
                c0_hsplit
                · c0_hsteps!
                  exact hQ 20#64 s5 m5 hsp5 hlvl5 hfuel5_le (Or.inr rfl)
                    (fun _ => huns5 ‹_›) hm5
                · c0_hsteps!
                  exact hQ 1#64 s5 m5 hsp5 hlvl5 hfuel5_le (Or.inl rfl)
                    (fun h => by cases h) hm5
              · c0_hsteps!
                exact hQ 1#64 s4 m4 hsp4 hlvl3 hfuel4_le (Or.inl rfl)
                  (fun h => by cases h) hm4
              · c0_hsteps!
                exact hQ 1#64 s4 m4 hsp4 hlvl3 hfuel4_le (Or.inl rfl)
                  (fun h => by cases h) hm4
        · have hokf : ok = false := by cases ok <;> simp_all
          have hsp1 : FullSparseInv c F0 s1 := hok_f hokf
          have hfuel1_le : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by
            rw [hfuel1]; exact hfuel0
          c0_hsteps_nogrp
          refine wp_join_state1 (t := i64) (α := BitVec 64) id
            (fun r mJ => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧
              (FullMem c s1 ⋆ R) mJ) ?_ ?_
          · rintro J1 r mJ ⟨hr, huns, hmJ⟩
            c0_hsteps!
            exact hQ r s1 mJ hsp1 hlvl1 hfuel1_le hr huns hmJ
          · intro J1 hJ1
            c0_hsteps_nogrp
            c0_hsplit
            · have hinc1 : s1.core.inconsistent ≠ 0#64 := ‹_›
              c0_hsteps!
              exact hJ1 20#64 m1 ⟨Or.inr rfl, fun _ => hsp1.inconsistent_unsat hinc1, hm1⟩
            · c0_hsteps!
              exact hJ1 1#64 m1 ⟨Or.inl rfl, (fun h => by cases h), hm1⟩
  · intro J hJ
    c0_hsplit
    · have hc_ne : BitVec.ofNat 64 s.core.cur_level ≠ 0 := ‹_›
      have hlvl_ne : s.core.cur_level ≠ 0 := fun h0 => hc_ne (by rw [h0]; rfl)
      have hlen := hsp.lengths
      obtain ⟨F_cur, hspW⟩ := hsp.exists_witness
      have hw : FullWitnessInv c F0 F_cur s.core := hspW.2.1
      have hmx := c.hmaxv
      unfold dimacsBound at hmx
      have hlvl_lt : s.core.cur_level < 2 ^ 64 := by
        have := hw.cur_level_le
        have := hlen.core_ok.trail_end_le
        have := hlen.core_ok.cur_vars_le
        omega
      have hmaxv_pos : 0 < c.max_vars := by
        have := hw.cur_level_le
        have := hlen.core_ok.trail_end_le
        have := hlen.core_ok.cur_vars_le
        omega
      c0_hsteps_nogrp
      c0_call hBt
      refine ⟨c, s, R, rfl, hlen, hlvl_lt, fun _ => hmaxv_pos, hw.trail_lits_lt, hm,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
          hlen' _ _ hcl' hps' _ _ _ hbw _ hm' => ?_⟩
      let s0 : FullState := {
        core := { s.core with
          unassigned := unass', trail_end := te', propagated := prop', cur_level := cl',
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp' }
        scratch := sc' }
      have hlvl0 : s0.core.cur_level = 0 := by
        dsimp [s0]
        rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.min_zero] at hcl'
        exact hcl'
      have hsp0 := m6_fullSparseInv_after_backtrack hsp s0 rfl hlen' hps'
        (hbw F0 F_cur hw (Nat.zero_le _))
      c0_hsteps!
      exact hJ m' ⟨s0, hsp0, hlvl0, Nat.le_refl _, hm'⟩
    · have hc_eq : BitVec.ofNat 64 s.core.cur_level = 0 := ‹_›
      have hlen := hsp.lengths
      have hmx := c.hmaxv
      unfold dimacsBound at hmx
      have hlvl_lt : s.core.cur_level < 2 ^ 64 := by
        obtain ⟨F_cur, hspW⟩ := hsp.exists_witness
        have := hspW.2.1.cur_level_le
        have := hlen.core_ok.trail_end_le
        have := hlen.core_ok.cur_vars_le
        omega
      have hlvl0 : s.core.cur_level = 0 := by bv_omega
      c0_hsteps!
      exact hJ m ⟨s, hsp, hlvl0, Nat.le_refl _, hm⟩

/-- `39/39`: Parametric `Func.wp` proof for `full_sweep_sat_m6` matching
    `Full.fullSweepSatSpec`. -/
theorem full_sweep_sat_m6_wp (Γ : Env)
    (hSat : M6EnvSpec Γ "full_m6_sweep_sat" m4SweepSatSpec) :
    ∀ args m Q X, Full.fullSweepSatSpec args m Q X →
      Func.wp Γ full_sweep_sat_m6_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  c0_hsteps_nogrp
  c0_call hSat
  exact ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩

/-! ## 4. Parametric `TableImpl` & `ModuleOk` Assembly (`m6Sweep_moduleOk_of_parts`) -/

/-- All 39 functions in `m6SweepModule.fns` are well-formed. -/
theorem m6Sweep_allFns_wf : AllFns Fn.Wf m6SweepModule.fns :=
  m6_allFns_of_mem m6Sweep_fns_wf

/-- Parametric `TableImpl` assembly for `m6SweepModule` under `m6SweepEnv`, taking only the 6
    unproved `Var2a`/`Cands` function specs as hypotheses and instantiating all 33 proved
    functions (`Kitten*`, `DenseProp`, `Cone`, `Var1a`, `Var1b`, `Els`, `Els2`, `Driver`). -/
theorem m6Sweep_tableImpl_of_parts
    (hUnits : ∀ args m Q X, m6SweepUnitsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_units_body args m Q X)
    (hClasses : ∀ args m Q X, m6SweepClassesSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_classes_body args m Q X)
    (hVar : ∀ args m Q X, m6SweepVarSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_var_body args m Q X)
    (hSift : ∀ args m Q X, m6CandSiftSpec args m Q X →
      Func.wp m6SweepEnv full_m6_cand_sift_body args m Q X)
    (hCollect : ∀ args m Q X, m6CollectCandsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_collect_cands_body args m Q X)
    (hVars : ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_vars_body args m Q X) :
    TableImpl m6SweepEnv m6SweepModule.fns m6SweepSpecTable := by
  have e_max_v : M6EnvSpec m6SweepEnv "full_m6_max_v" m6MaxVSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_add_ticks : M6EnvSpec m6SweepEnv "full_k6_add_ticks" k6AddTicksSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_init : M6EnvSpec m6SweepEnv "full_k6_init" k6InitSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_watch : M6EnvSpec m6SweepEnv "full_k6_watch" k6WatchSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_assign : M6EnvSpec m6SweepEnv "full_k6_assign" k6AssignSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_add_cl : M6EnvSpec m6SweepEnv "full_k6_add_clause" k6AddClauseSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_mtf : M6EnvSpec m6SweepEnv "full_k6_mtf" k6MtfSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_kbt : M6EnvSpec m6SweepEnv "full_k6_backtrack" k6BacktrackSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_kprop : M6EnvSpec m6SweepEnv "full_k6_propagate" k6PropagateSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_anacl : M6EnvSpec m6SweepEnv "full_k6_ana_clause" k6AnaClauseSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_ana : M6EnvSpec m6SweepEnv "full_k6_analyze" k6AnalyzeSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_ksolve : M6EnvSpec m6SweepEnv "full_k6_solve" k6SolveSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_flip : M6EnvSpec m6SweepEnv "full_k6_flip" k6FlipSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_dpl : M6EnvSpec m6SweepEnv "full_m6_dense_prop_lit" m6DensePropLitSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_dp : M6EnvSpec m6SweepEnv "full_m6_dense_prop" m6DensePropSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_refsig : M6EnvSpec m6SweepEnv "full_m6_sweep_refine_sig" m6SweepRefineSigSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_randp : M6EnvSpec m6SweepEnv "full_m6_sweep_rand_phases" m6SweepRandPhasesSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_ssolve : M6EnvSpec m6SweepEnv "full_m6_sweep_solve" m6SweepSolveSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_fliprd : M6EnvSpec m6SweepEnv "full_m6_sweep_flip_round" m6SweepFlipRoundSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_els_ar : M6EnvSpec m6SweepEnv "full_m6_els_ar" m6ElsArSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_els_lit : M6EnvSpec m6SweepEnv "full_m6_els_lit" m6ElsLitSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_els_fold : M6EnvSpec m6SweepEnv "full_m6_els_fold" m6ElsFoldSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_swvars : M6EnvSpec m6SweepEnv "full_m6_sweep_vars" m6SweepVarsSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_swdense : M6EnvSpec m6SweepEnv "full_m6_sweep_dense" m4SweepDenseSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_swsat : M6EnvSpec m6SweepEnv "full_m6_sweep_sat" m4SweepSatSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_rng : M6EnvSpec m6SweepEnv "full_rng_next" Full.fullRngNextSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_bt : M6EnvSpec m6SweepEnv "full_backtrack" Full.fullBacktrackSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_prop : M6EnvSpec m6SweepEnv "full_propagate" Full.fullPropagateSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_asglvl : M6EnvSpec m6SweepEnv "full_assign_lvl" Full.fullAssignLvlSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_wpush : M6EnvSpec m6SweepEnv "full_watch_push" Full.fullWatchPushSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_setinact : M6EnvSpec m6SweepEnv "full_set_inactive" Full.fullSetInactiveSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_extp2 : M6EnvSpec m6SweepEnv "full_extend_push2" m6ExtendPush2Spec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_addunit : M6EnvSpec m6SweepEnv "full_add_unit" Full.fullAddUnitSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_addbin : M6EnvSpec m6SweepEnv "full_add_bin" Full.fullAddBinSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_enterd : M6EnvSpec m6SweepEnv "full_enter_dense" Full.fullEnterDenseSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_rebw : M6EnvSpec m6SweepEnv "full_rebuild_watches" Full.fullRebuildWatchesSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_subst : M6EnvSpec m6SweepEnv "full_substitute" Full.fullSubstituteSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_max_v_wp m6SweepEnv⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_add_ticks_wp m6SweepEnv⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_init_wp m6SweepEnv e_max_v⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_watch_wp m6SweepEnv⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_assign_wp m6SweepEnv⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_add_clause_wp m6SweepEnv e_max_v e_assign e_watch⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_mtf_wp m6SweepEnv⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_backtrack_wp m6SweepEnv⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_propagate_wp m6SweepEnv e_add_ticks e_assign⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_ana_clause_wp m6SweepEnv⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_analyze_wp m6SweepEnv e_anacl e_kbt e_mtf e_watch e_assign⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_solve_wp m6SweepEnv e_max_v e_kbt e_assign e_kprop e_ana⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k6_flip_wp m6SweepEnv e_max_v e_add_ticks⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_k512_add_live_m6_wp m6SweepEnv e_max_v e_kbt e_assign
    e_watch e_kprop⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_dense_prop_lit_wp m6SweepEnv e_asglvl⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_dense_prop_wp m6SweepEnv e_dpl⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_cone_wp m6SweepEnv e_max_v e_init e_add_cl⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_refine_sig_wp m6SweepEnv e_max_v⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_rand_phases_wp m6SweepEnv e_max_v e_rng⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_solve_wp m6SweepEnv e_randp e_ksolve⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_flip_round_wp m6SweepEnv e_max_v e_rng e_flip⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_sim_wp m6SweepEnv e_max_v e_ssolve e_refsig e_fliprd⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_rearm_wp m6SweepEnv⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_build_pht_wp m6SweepEnv e_max_v⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_extract_pht_wp m6SweepEnv e_max_v⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_refine_partition_wp m6SweepEnv e_max_v⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, hUnits⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, hClasses⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_els_ar_wp m6SweepEnv e_wpush e_addunit e_addbin⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_els_lit_wp m6SweepEnv e_addunit e_addbin e_els_ar⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_els_fold_wp m6SweepEnv e_addunit e_extp2 e_setinact⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_dense_els_wp m6SweepEnv e_els_fold e_els_lit e_dp⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, hVar⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, hSift⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, hCollect⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, hVars⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_dense_wp m6SweepEnv e_max_v e_swvars⟩, ?_⟩
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_m6_sweep_sat_wp m6SweepEnv e_bt e_max_v e_enterd e_swdense
    e_rebw e_prop e_subst⟩, ?_⟩
  exact ⟨⟨⟨rfl, rfl, rfl⟩, full_sweep_sat_m6_wp m6SweepEnv e_swsat⟩, trivial⟩

/-- Top-level parametric `ModuleOk` assembly theorem for `m6SweepModule` under `m6SweepEnv`,
    additionally checking `m6SweepSpecTable_sigs` (by `t_kernel_rfl`), `m6SweepSpecTable_nodup`,
    and `m6SweepSpecTable_noExit`. -/
theorem m6Sweep_moduleOk_of_parts
    (hUnits : ∀ args m Q X, m6SweepUnitsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_units_body args m Q X)
    (hClasses : ∀ args m Q X, m6SweepClassesSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_classes_body args m Q X)
    (hVar : ∀ args m Q X, m6SweepVarSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_var_body args m Q X)
    (hSift : ∀ args m Q X, m6CandSiftSpec args m Q X →
      Func.wp m6SweepEnv full_m6_cand_sift_body args m Q X)
    (hCollect : ∀ args m Q X, m6CollectCandsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_collect_cands_body args m Q X)
    (hVars : ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_vars_body args m Q X) :
    ModuleOk m6SweepEnv m6SweepModule := by
  have _ := m6SweepSpecTable_sigs
  have _ := m6SweepSpecTable_nodup
  have _ := m6SweepSpecTable_noExit
  exact Env.ofTable_moduleOk m6Sweep_acyclic m6Sweep_allFns_wf
    (m6Sweep_tableImpl_of_parts hUnits hClasses hVar hSift hCollect hVars)

/-! ## 5. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`) -/

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_m6_sweep_dense` under `m6SweepEnv` with
    `XPost := fun _ _ _ _ => False`. -/
theorem nv_m6_sweep_dense :
    Func.wp m6SweepEnv full_m6_sweep_dense_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) FullM4Sweep.nvM4SweepMem
      (fun x m' =>
        match x with
        | (r, ()) =>
          ∃ s',
            FullDenseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
              (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧
                FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have e_max_v : M6EnvSpec m6SweepEnv "full_m6_max_v" m6MaxVSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_swvars : M6EnvSpec m6SweepEnv "full_m6_sweep_vars" m6SweepVarsSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  refine full_m6_sweep_dense_wp m6SweepEnv e_max_v e_swvars _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, FullM4Sweep.nvM4SweepState,
     Std.ExtHashMap.emp, rfl, FullM4Sweep.nvM4Sweep_invW.toDense,
     (by rw [Std.ExtHashMap.sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok),
     fun r s' m' hinv' _ _ hr _ hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨s', hinv', hr, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_m6_sweep_sat` under `m6SweepEnv` with
    `XPost := fun _ _ _ _ => False`. -/
theorem nv_m6_sweep_sat :
    Func.wp m6SweepEnv full_m6_sweep_sat_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) FullM4Sweep.nvM4SweepSparseMem
      (fun x m' =>
        match x with
        | (r, ()) =>
          ∃ s',
            FullSparseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
              s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧
                Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have e_bt : M6EnvSpec m6SweepEnv "full_backtrack" Full.fullBacktrackSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_max_v : M6EnvSpec m6SweepEnv "full_m6_max_v" m6MaxVSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_enterd : M6EnvSpec m6SweepEnv "full_enter_dense" Full.fullEnterDenseSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_swdense : M6EnvSpec m6SweepEnv "full_m6_sweep_dense" m4SweepDenseSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_rebw : M6EnvSpec m6SweepEnv "full_rebuild_watches" Full.fullRebuildWatchesSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_prop : M6EnvSpec m6SweepEnv "full_propagate" Full.fullPropagateSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_subst : M6EnvSpec m6SweepEnv "full_substitute" Full.fullSubstituteSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  refine full_m6_sweep_sat_wp m6SweepEnv e_bt e_max_v e_enterd e_swdense
    e_rebw e_prop e_subst _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, FullM4Sweep.nvM4SweepSparseState,
     Std.ExtHashMap.emp, rfl, FullM4Sweep.nvM4SweepSparse_inv,
     (by rw [Std.ExtHashMap.sep_emp]; exact FullM4Sweep.nvM4SweepSparseMem_ok),
     fun r s' m' hsp' hlvl' _ hr _ hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨s', hsp', hlvl', hr, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_sweep_sat_m6` under `m6SweepEnv` with
    `XPost := fun _ _ _ _ => False`. -/
theorem nv_full_sweep_sat_m6 :
    Func.wp m6SweepEnv full_sweep_sat_m6_body
      (FullM4Sweep.nvM4SweepCfg.hdr, ()) FullM4Sweep.nvM4SweepSparseMem
      (fun x m' =>
        match x with
        | (r, ()) =>
          ∃ s',
            FullSparseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
              s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧
                Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have e_swsat : M6EnvSpec m6SweepEnv "full_m6_sweep_sat" m4SweepSatSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  refine full_sweep_sat_m6_wp m6SweepEnv e_swsat _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, FullM4Sweep.nvM4SweepSparseState,
     Std.ExtHashMap.emp, rfl, FullM4Sweep.nvM4SweepSparse_inv,
     (by rw [Std.ExtHashMap.sep_emp]; exact FullM4Sweep.nvM4SweepSparseMem_ok),
     fun r s' m' hsp' hlvl' _ hr _ hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨s', hsp', hlvl', hr, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩

end LeanQbe.T.Examples.Kissat.FullM6Sweep
