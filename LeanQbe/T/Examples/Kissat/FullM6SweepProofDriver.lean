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
5. Concrete `Mem 64` non-vacuity with `inconsistent = 0#64` and embedded `K6State` (`max_v = 512`)
   for `full_k6_{init,solve}`, `full_m6_sweep_{cone,var,vars,dense,sat}`, and `full_sweep_sat_m6`
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

section ConcreteNonVacuity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test

/-- Concrete `K6Layout` matching `FullM4Sweep.nvM4SweepCfg` (`scratch_cap = 24576`,
    `maxV = 512`, `k6Base = 2304`, `acap = 2784`). -/
def nvM6K6Layout : K6Layout :=
  k6LayoutOfCap 24576 (by decide) (by decide)

private theorem nvM6K6Layout_maxV : nvM6K6Layout.maxV = 512 := k6MaxV_512

private theorem nvM6K6Layout_maxOrig : nvM6K6Layout.maxOrig = 1536 := by
  unfold K6Layout.maxOrig; rw [nvM6K6Layout_maxV]

private theorem nvM6K6Layout_maxCl : nvM6K6Layout.maxCl = 2048 := by
  unfold K6Layout.maxCl; rw [nvM6K6Layout_maxV]

private theorem nvM6K6Layout_acap : nvM6K6Layout.acap = 2784 := by
  unfold nvM6K6Layout k6LayoutOfCap; dsimp only; rw [k6MaxV_512]

private theorem nvM6K6Layout_k6Base : nvM6K6Layout.k6Base = 2304 := by
  unfold K6Layout.k6Base; rw [nvM6K6Layout_maxV]

private theorem nvM6K6Layout_scrLen : nvM6K6Layout.scrLen = 24576 :=
  k6LayoutOfCap_scrLen (by decide) (by decide)

/-- Concrete inconsistent `K6State` (`nv = 1`, `nc = 0`, `incons = 1`, `acap = 2784`,
    `max_v = 512`, `max_orig = 1536`, `max_cl = 2048`). -/
def nvM6K6State : K6State where
  nv := 1#32
  nc := 0#32
  lvl := 0#32
  prop := 0#32
  trl_end := 0#32
  unass := 1#32
  incons := 1#32
  qfirst := 0#32
  qlast := 0#32
  qsearch := 0#32
  qstamp := 1#32
  ticks := 0#32
  tick_lim := 0#32
  alen := 0#32
  acap := 2784#32
  nassump := 0#32
  nkl := 0#32
  nana := 0#32
  status := 0#32
  phase := 0#32
  openCnt := 0#32
  max_v := 512#32
  max_orig := 1536#32
  max_cl := 2048#32
  neq := 0#32
  hdrTail := List.replicate 7 0#32
  lvlArr := List.replicate 512 0#32
  rsn := List.replicate 512 0xFFFFFFFF#32
  qprev := List.replicate 512 0xFFFFFFFF#32
  qnext := List.replicate 512 0xFFFFFFFF#32
  qstampArr := List.replicate 512 0#32
  trl := List.replicate 512 0#32
  flags := List.replicate 512 0#32
  ana := List.replicate 512 0#32
  kl := List.replicate 512 0#32
  assump := List.replicate 512 0#32
  vals := List.replicate 1024 0#32
  whead := List.replicate 1024 0xFFFFFFFF#32
  wnext := List.replicate 4096 0xFFFFFFFF#32
  wblit := List.replicate 4096 0#32
  clOff := List.replicate 2048 0#32
  clSz := List.replicate 2048 0#32
  arena := List.replicate 2784 0#32

theorem nvM6K6State_shapes : nvM6K6State.ShapesOk nvM6K6Layout := by
  refine ⟨List.length_replicate, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    simp only [nvM6K6State, List.length_replicate, nvM6K6Layout_maxV, nvM6K6Layout_maxCl,
      nvM6K6Layout_acap] <;>
    decide

theorem nvM6K6State_inv : K6Inv nvM6K6Layout (fun _ => False) nvM6K6State := by
  have hsh : nvM6K6State.ShapesOk nvM6K6Layout := nvM6K6State_shapes
  have hcl : K6ClausesOk nvM6K6Layout (fun _ => False) nvM6K6State :=
    { acap_eq := by rw [nvM6K6Layout_acap]; rfl
      max_v_eq := by rw [nvM6K6Layout_maxV]; rfl
      max_orig_eq := by rw [nvM6K6Layout_maxOrig]; rfl
      max_cl_eq := by rw [nvM6K6Layout_maxCl]; rfl
      nv_le := by rw [nvM6K6Layout_maxV]; decide
      nc_le := by rw [nvM6K6Layout_maxCl]; decide
      alen_le := by rw [nvM6K6Layout_acap]; decide
      nassump_le := by rw [nvM6K6Layout_maxV]; decide
      nkl_le := by rw [nvM6K6Layout_maxV]; decide
      nana_le := by rw [nvM6K6Layout_maxV]; decide
      cl_wf := fun _ h => by simp [-List.reduceReplicate, nvM6K6State] at h
      cl_mono := fun _ _ _ h => by simp [-List.reduceReplicate, nvM6K6State] at h
      incons_ok := fun _ _ h => h
      assump_ok := fun _ h => by simp [-List.reduceReplicate, nvM6K6State] at h
      flags_clean := fun v hv => by
        have hv1 : v < 1 := hv
        simp [-List.reduceReplicate, nvM6K6State, show v < 512 by omega] }
  have hwat : K6WatchesOk nvM6K6State := by
    refine ⟨[[], []], rfl, by decide, fun l hl => ?_, fun l hl w hw => ?_⟩
    · have hl2 : l < 2 := hl
      rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
      · simp only [nvM6K6State, List.getElem?_replicate, show (0 : Nat) < 1024 by decide,
          ↓reduceIte, Option.getD_some, List.getElem?_cons_zero]
        exact FullM4Sweep.K5WChain.nil
      · simp only [nvM6K6State, List.getElem?_replicate, show (1 : Nat) < 1024 by decide,
          ↓reduceIte, Option.getD_some, List.getElem?_cons_succ, List.getElem?_cons_zero]
        exact FullM4Sweep.K5WChain.nil
    · have hl2 : l < 2 := hl
      rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;> simp at hw
  have hasg : K6BaseAssignOk (fun _ => False) nvM6K6State :=
    { trl_end_le := by decide
      prop_le := by decide
      unass_eq := by decide
      vals_dom := fun l hl => by
        have hl2 : l < 2 := hl
        simp [-List.reduceReplicate, nvM6K6State, show l < 1024 by omega]
      vals_neg_iff := fun l hl => by
        have hl2 : l < 2 := hl
        have hnl : l ^^^ 1 < 1024 := by
          rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;> decide
        simp [-List.reduceReplicate, nvM6K6State, show l < 1024 by omega, hnl]
      vals_nz_iff_trl := fun l hl => by
        have hl2 : l < 2 := hl
        simp [-List.reduceReplicate, nvM6K6State, show l < 1024 by omega]
      trl_nodup := by decide
      trl_lt := fun l hl => by simp [-List.reduceReplicate, k6TrailLits, nvM6K6State] at hl
      trl_lvl_le := fun v hv => by
        have hv1 : v < 1 := hv
        simp [-List.reduceReplicate, nvM6K6State, show v < 512 by omega]
      unass_lvl_zero := fun v hv _ => by
        have hv1 : v < 1 := hv
        simp [-List.reduceReplicate, nvM6K6State, show v < 512 by omega]
      trl_lvl_mono := fun _ _ _ h => by simp [-List.reduceReplicate, nvM6K6State] at h
      dec_earliest := fun _ _ _ h => by simp [-List.reduceReplicate, nvM6K6State] at h
      lvl0_ok := fun _ h => by simp [-List.reduceReplicate, nvM6K6State] at h }
  exact ⟨hsh, hcl, hwat, hasg, fun _ h => by simp [-List.reduceReplicate, nvM6K6State] at h⟩

/-- Concrete `24576`-word `scratch_buf` embedding `nvM6K6State` at `k6Base = 2304`. -/
def nvM6SweepScratchBuf : List (BitVec 32) :=
  List.replicate 2304 0#32 ++ nvM6K6State.toSlab

theorem nvM6SweepScratchBuf_length : nvM6SweepScratchBuf.length = 24576 := by
  unfold nvM6SweepScratchBuf
  rw [List.length_append, List.length_replicate, nvM6K6State.toSlab_length nvM6K6State_shapes]
  have hlen : nvM6K6Layout.k6Fixed + nvM6K6Layout.acap = 22272 := by
    unfold K6Layout.k6Fixed; rw [nvM6K6Layout_maxV, nvM6K6Layout_acap]
  rw [hlen]

theorem nvM6SweepScratchBuf_k6State :
    k6StateOfScratch nvM6K6Layout nvM6SweepScratchBuf = nvM6K6State := by
  unfold k6StateOfScratch nvM6SweepScratchBuf
  rw [nvM6K6Layout_k6Base,
    List.drop_append_of_le_length (by rw [List.length_replicate]; exact le_refl _),
    List.drop_replicate, Nat.sub_self, List.replicate_zero, List.nil_append]
  exact K6State.ofSlab_toSlab nvM6K6State_shapes

theorem nvM6SweepScratchBuf_k6Inv :
    K6ScratchInv (fun _ => False) nvM6SweepScratchBuf := by
  have hlen : nvM6SweepScratchBuf.length = nvM6K6Layout.scrLen := by
    rw [nvM6SweepScratchBuf_length, nvM6K6Layout_scrLen]
  have hmv : nvM6K6Layout.maxV = k6MaxV nvM6SweepScratchBuf.length := by
    rw [nvM6SweepScratchBuf_length, nvM6K6Layout_maxV]; exact k6MaxV_512.symm
  refine K6Inv.to_scratchInv hlen hmv (by rw [nvM6SweepScratchBuf_length]; decide)
    (by rw [nvM6SweepScratchBuf_length]; decide) ?_
  rw [nvM6SweepScratchBuf_k6State]
  exact nvM6K6State_inv

/-- Zero-initialized `FullScratch` carrying `nvM6SweepScratchBuf`. -/
def nvM6SweepScratch : FullScratch :=
  { FullM4Sweep.nvM4SweepScratch with scratch_buf := nvM6SweepScratchBuf }

/-- Concrete dense-mode UNSAT `FullState` (`FL_ACTIVE | FL_SWEEP`, `dense_mode = 1`,
    `inconsistent = 0`, `fuel = 1`, embedded `nvM6K6State`) so `full_m6_sweep_dense`
    enters the candidate loop rather than short-circuiting. -/
def nvM6SweepState : FullState :=
  { FullM4Sweep.nvM4SweepState with
    core := { FullM4Sweep.nvM4SweepState.core with inconsistent := 0#64 }
    scratch := nvM6SweepScratch }

/-- Concrete sparse-mode UNSAT `FullState` (`dense_mode = 0`, `inconsistent = 0`,
    `fuel = 1`, embedded `nvM6K6State`). -/
def nvM6SweepSparseState : FullState :=
  { nvM6SweepState with core := { nvM6SweepState.core with dense_mode := 0#64 } }

theorem nvM6SweepState_lengths : nvM6SweepState.LengthsOk FullM4Sweep.nvM4SweepCfg := by
  rcases FullM4Sweep.nvM4SweepState_lengths.1 with
    ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20,
     c21, c22, c23, c24, c25⟩
  rcases FullM4Sweep.nvM4SweepState_lengths.2 with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
     h21, h22, h23, _⟩
  exact ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
      c20, c21, c22, c23, c24, c25⟩,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21, h22, h23, nvM6SweepScratchBuf_length⟩⟩

theorem nvM6Sweep_invW :
    FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] nvM6SweepState := by
  have hcv : nvM6SweepState.core.cur_vars = 1 := rfl
  have hdm : nvM6SweepState.core.dense_mode ≠ 0#64 := by decide
  have hrefs : fullArenaClauseRefsCore nvM6SweepState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvM6SweepState.core := by
    unfold ModeWatchesInv; rw [ite_eq_right hdm]
    refine DenseWatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvM6SweepState, FullM4Sweep.nvM4SweepState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvM6SweepState, FullM4Sweep.nvM4SweepState] at hp
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact DenseWatchSliceOk.empty
  rcases FullM4Sweep.nvM4Sweep_invW with ⟨_, hw4, hlm4, hnd4, hll4, hext4, hdm4⟩
  refine ⟨nvM6SweepState_lengths,
    { ext_sound := hw4.ext_sound
      inconsistent_sound := fun _ => FullM4Sweep.nvM4SweepF0_unsat
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := hw4.cur_level_le
      trail_lits_lt := hw4.trail_lits_lt
      trail_vars_nodup := hw4.trail_vars_nodup
      vals_domain := hw4.vals_domain
      vals_true_iff := hw4.vals_true_iff
      vals_false_iff := hw4.vals_false_iff
      lvl_le := hw4.lvl_le
      dec_earliest := hw4.dec_earliest
      levels_inhabited := hw4.levels_inhabited
      level0_sound := hw4.level0_sound
      trail_pos_inv := hw4.trail_pos_inv
      level0_rsn_none := hw4.level0_rsn_none
      frame_trail_lt := hw4.frame_trail_lt
      frame_trail_mono := hw4.frame_trail_mono
      frame_trail_before_lt := hw4.frame_trail_before_lt
      frame_dec_lt := hw4.frame_dec_lt
      reason_inv := hw4.reason_inv
      reason_lit_mem := hw4.reason_lit_mem },
    hlm4, hnd4, hll4, hext4, hdm4⟩

theorem nvM6SweepSparse_inv :
    FullSparseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 nvM6SweepSparseState :=
  nvM6Sweep_invW.toSparse_clear_dense.toSparse

theorem nvM6Sweep_tmkZero : M6TmkZero nvM6SweepState := fun v hv =>
  FullM4Sweep.nvM4Sweep_tmkZero v hv

def nvM6BlockTail (s : FullState) : List UInt8 :=
  bytesOf (t := i32) s.core.min_stk ++
  bytesOf (t := i32) s.scratch.glue_used ++
  bytesOf (t := i32) s.scratch.last_learned ++
  bytesOf (t := i32) s.core.arena ++
  bytesOf (t := i32) s.core.wstk ++
  bytesOf (t := i32) s.scratch.delayed ++
  bytesOf (t := i32) s.scratch.red_refs ++
  bytesOf (t := i32) s.scratch.extend_stk ++
  bytesOf (t := i32) s.scratch.scratch_buf ++
  List.replicate 0 0

/-- Concrete `100060`-byte dense-mode image encoding `nvM4SweepCfg` and `nvM6SweepState`. -/
def nvM6SweepBytes : List UInt8 :=
  FullM4Sweep.nvM4BlockHdr nvM6SweepState ++ FullM4Sweep.nvM4BlockBytes ++
  FullM4Sweep.nvM4BlockU32A ++ FullM4Sweep.nvM4BlockU32B ++
  FullM4Sweep.nvM4BlockU32C ++ FullM4Sweep.nvM4BlockWvec ++
  nvM6BlockTail nvM6SweepState

/-- Concrete `100060`-byte sparse-mode image encoding `nvM4SweepCfg` and
    `nvM6SweepSparseState`. -/
def nvM6SweepSparseBytes : List UInt8 :=
  FullM4Sweep.nvM4BlockHdr nvM6SweepSparseState ++ FullM4Sweep.nvM4BlockBytes ++
  FullM4Sweep.nvM4BlockU32A ++ FullM4Sweep.nvM4BlockU32B ++
  FullM4Sweep.nvM4BlockU32C ++ FullM4Sweep.nvM4BlockWvec ++
  nvM6BlockTail nvM6SweepSparseState

/-- Concrete dense-mode `Mem 64` heap mapped at `FullM4Sweep.nvM4SweepCfg.hdr` (`0x1000#64`). -/
def nvM6SweepMem : Mem 64 := nvM6SweepBytes.At FullM4Sweep.nvM4SweepCfg.hdr

/-- Concrete sparse-mode `Mem 64` heap mapped at `FullM4Sweep.nvM4SweepCfg.hdr` (`0x1000#64`). -/
def nvM6SweepSparseMem : Mem 64 := nvM6SweepSparseBytes.At FullM4Sweep.nvM4SweepCfg.hdr

theorem nvM6SweepBytes_length : nvM6SweepBytes.length = 100060 := by
  simp only [nvM6SweepBytes, FullM4Sweep.nvM4BlockHdr, FullM4Sweep.nvM4BlockBytes,
    FullM4Sweep.nvM4BlockU32A, FullM4Sweep.nvM4BlockU32B, FullM4Sweep.nvM4BlockU32C,
    FullM4Sweep.nvM4BlockWvec, nvM6BlockTail, nvM6SweepState, nvM6SweepScratch,
    FullM4Sweep.nvM4SweepState, FullM4Sweep.nvM4SweepScratch, List.length_append,
    List.length_replicate, bytesOf_length, bytes64_length, Full.hdrTailWords_length,
    nvM6SweepScratchBuf_length, List.length_cons, List.length_nil]
  rfl

theorem nvM6SweepSparseBytes_length : nvM6SweepSparseBytes.length = 100060 := by
  simp only [nvM6SweepSparseBytes, FullM4Sweep.nvM4BlockHdr, FullM4Sweep.nvM4BlockBytes,
    FullM4Sweep.nvM4BlockU32A, FullM4Sweep.nvM4BlockU32B, FullM4Sweep.nvM4BlockU32C,
    FullM4Sweep.nvM4BlockWvec, nvM6BlockTail, nvM6SweepSparseState, nvM6SweepState,
    nvM6SweepScratch, FullM4Sweep.nvM4SweepState, FullM4Sweep.nvM4SweepScratch,
    List.length_append, List.length_replicate, bytesOf_length, bytes64_length,
    Full.hdrTailWords_length, nvM6SweepScratchBuf_length, List.length_cons, List.length_nil]
  rfl

private theorem nvM6SweepMem_ok_of_dense_mode (dm : BitVec 64) :
    let s : FullState :=
      { nvM6SweepState with core := { nvM6SweepState.core with dense_mode := dm } }
    FullMem FullM4Sweep.nvM4SweepCfg s
      ((FullM4Sweep.nvM4BlockHdr s ++ FullM4Sweep.nvM4BlockBytes ++
        FullM4Sweep.nvM4BlockU32A ++ FullM4Sweep.nvM4BlockU32B ++
        FullM4Sweep.nvM4BlockU32C ++ FullM4Sweep.nvM4BlockWvec ++ nvM6BlockTail s).At
        FullM4Sweep.nvM4SweepCfg.hdr) := by
  intro s
  let c := FullM4Sweep.nvM4SweepCfg
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : (FullM4Sweep.nvM4BlockHdr s).length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        ((FullM4Sweep.nvM4BlockHdr s).At c.hdr) :=
    Full.nv_join_pair
      (Full.nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (Full.nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : FullM4Sweep.nvM4BlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (FullM4Sweep.nvM4BlockBytes.At c.pVals) := by
    have h1 := Full.nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
      (by decide)
    have h6 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesTarget)
      (xs := s.scratch.phases_target) 1 7 rfl (by decide)
    have h7 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best)
      1 7 rfl (by decide)
    have h8 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best)
      1 7 rfl (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_sep_reorg (Full.nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => Full.nv_zip4 hm
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg hall fun _ hm => by
      have hfin := Full.nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : FullM4Sweep.nvM4BlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (FullM4Sweep.nvM4BlockU32A.At c.pFlags) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : FullM4Sweep.nvM4BlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (FullM4Sweep.nvM4BlockU32B.At c.pTmp) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl
      (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk)
      4 4 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : FullM4Sweep.nvM4BlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (FullM4Sweep.nvM4BlockU32C.At c.pQPrev) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail)
      8 0 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl
      (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : FullM4Sweep.nvM4BlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (FullM4Sweep.nvM4BlockWvec.At c.pWvec) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach)
      8 rfl (by decide)
    have h8 := Full.nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := Full.nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : (nvM6BlockTail s).length = 98644 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        ((nvM6BlockTail s).At c.pMinStk) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned)
      64 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl
      (by decide)
    have h8 := Full.nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := Full.nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 98304
      (by show 4 * nvM6SweepScratchBuf.length = 98304; rw [nvM6SweepScratchBuf_length])
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := Full.nv_join_pair h12345678 h9 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm =>
      by unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := Full.nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := Full.nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := Full.nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := Full.nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := Full.nv_join_pair h04 hWvec (by decide) (by decide)
  exact (Full.nv_sep_reorg (Q := FullMem c s) (Full.nv_join_pair h05 hTail (by decide) (by decide))
    fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad
      exact sep_ac hm).2

theorem nvM6SweepMem_ok : FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState nvM6SweepMem :=
  nvM6SweepMem_ok_of_dense_mode 1#64

theorem nvM6SweepSparseMem_ok :
    FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepSparseState nvM6SweepSparseMem :=
  nvM6SweepMem_ok_of_dense_mode 0#64

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `full_k6_init`. -/
theorem nv_m6_k6_init :
    Func.wp m6SweepEnv full_k6_init_body (FullM4Sweep.nvM4SweepCfg.hdr, 1#32, ()) nvM6SweepMem
      (fun () m' => ∃ scr',
        (∀ P, K6ScratchInv P scr') ∧ (k6StateOfScratch nvM6K6Layout scr').nv = 1#32 ∧
        FullMem FullM4Sweep.nvM4SweepCfg
          { nvM6SweepState with scratch := { nvM6SweepState.scratch with scratch_buf := scr' } }
          m')
      (fun _ _ _ _ => False) := by
  have e_max_v : M6EnvSpec m6SweepEnv "full_m6_max_v" m6MaxVSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState ⋆ emp) nvM6SweepMem := by
    rw [sep_emp]; exact nvM6SweepMem_ok
  refine full_k6_init_wp m6SweepEnv e_max_v _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvM6SweepState, emp, rfl, nvM6SweepState_lengths, hm, ?_⟩
  rw [ite_eq_right (by decide)]
  intro L scr' m' hLlen hLmv
  dsimp only
  intro hs'len _ hK _ hnv _ _ _ _ _ _ _ _ _ _ hm'
  have hscr_len : scr'.length = L.scrLen := hs'len.2.24.trans hLlen.symm
  have hLeq : L = nvM6K6Layout :=
    (k6LayoutOfCap_eq hLlen hLmv (by decide) (by decide)).symm
  have hScrInv : ∀ P, K6ScratchInv P scr' := fun P => by
    refine K6Inv.to_scratchInv hscr_len ?_ (by rw [hs'len.2.24]; decide)
      (by rw [hs'len.2.24]; decide) (hK P)
    rw [hLmv, hs'len.2.24]
  rw [sep_emp] at hm'
  exact ⟨scr', hScrInv, hLeq ▸ hnv, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_k6_solve` on the embedded
    inconsistent `K6State` slab (`max_v = 512`, `incons = 1`). -/
theorem nv_m6_k6_solve :
    Func.wp m6SweepEnv full_k6_solve_body (FullM4Sweep.nvM4SweepCfg.hdr, 100#64, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ fuel' scr',
        K6ScratchInv (fun _ => False) scr' ∧ (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧
        FullMem FullM4Sweep.nvM4SweepCfg
          { nvM6SweepState with
            core := { nvM6SweepState.core with fuel := fuel' }
            scratch := { nvM6SweepState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) := by
  have e_max_v : M6EnvSpec m6SweepEnv "full_m6_max_v" m6MaxVSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_kbt : M6EnvSpec m6SweepEnv "full_k6_backtrack" k6BacktrackSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_assign : M6EnvSpec m6SweepEnv "full_k6_assign" k6AssignSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_kprop : M6EnvSpec m6SweepEnv "full_k6_propagate" k6PropagateSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_ana : M6EnvSpec m6SweepEnv "full_k6_analyze" k6AnalyzeSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState ⋆ emp) nvM6SweepMem := by
    rw [sep_emp]; exact nvM6SweepMem_ok
  have hK0 : K6Inv nvM6K6Layout (fun _ => False)
      (k6StateOfScratch nvM6K6Layout nvM6SweepState.scratch.scratch_buf) := by
    change K6Inv nvM6K6Layout (fun _ => False) (k6StateOfScratch nvM6K6Layout nvM6SweepScratchBuf)
    rw [nvM6SweepScratchBuf_k6State]
    exact nvM6K6State_inv
  refine full_k6_solve_wp m6SweepEnv e_max_v e_kbt e_assign e_kprop e_ana _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvM6SweepState, (fun _ => False), nvM6K6Layout, emp, rfl,
     nvM6SweepState_lengths, nvM6K6Layout_scrLen,
     (by rw [nvM6K6Layout_maxV]; exact k6MaxV_512.symm), hK0, hm,
     fun r fuel' scr' m' hs'len _ _ hK _ _ _ _ _ hdom _ hm' => by
       have hscr_len : scr'.length = nvM6K6Layout.scrLen :=
         hs'len.2.24.trans nvM6K6Layout_scrLen.symm
       have hmv : nvM6K6Layout.maxV = k6MaxV scr'.length := by
         rw [hs'len.2.24, nvM6K6Layout_maxV]; exact k6MaxV_512.symm
       have hScrInv : K6ScratchInv (fun _ => False) scr' :=
         K6Inv.to_scratchInv hscr_len hmv (by rw [hs'len.2.24]; decide)
           (by rw [hs'len.2.24]; decide) hK
       rw [sep_emp] at hm'
       exact ⟨fuel', scr', hScrInv, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_m6_sweep_cone`. -/
theorem nv_m6_sweep_cone :
    Func.wp m6SweepEnv full_m6_sweep_cone_body (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M6SweepConeOk [[0], [1]] s' (r &&& 0xFFFF#64).toNat ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have e_max_v : M6EnvSpec m6SweepEnv "full_m6_max_v" m6MaxVSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_init : M6EnvSpec m6SweepEnv "full_k6_init" k6InitSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have e_add_cl : M6EnvSpec m6SweepEnv "full_k6_add_clause" k6AddClauseSpec :=
    m6_row (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) (fun _ _ _ _ h => h)
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState ⋆ emp) nvM6SweepMem := by
    rw [sep_emp]; exact nvM6SweepMem_ok
  exact full_m6_sweep_cone_wp m6SweepEnv e_max_v e_init e_add_cl _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, [[0], [1]], nvM6SweepState, emp, rfl,
     nvM6Sweep_invW, by decide, by decide, nvM6Sweep_tmkZero, hm,
     fun _ _ _ _ _ m' hd _ _ _ _ hcone _ _ _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨_, hd, hcone, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_m6_sweep_var`,
    parameterized by `full_m6_sweep_var_wp`. -/
theorem nv_m6_sweep_var_of
    (hVar : ∀ args m Q X, m6SweepVarSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_var_body args m Q X) :
    Func.wp m6SweepEnv full_m6_sweep_var_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, 8192#64, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M6TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState ⋆ emp) nvM6SweepMem := by
    rw [sep_emp]; exact nvM6SweepMem_ok
  exact hVar _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, [[0], [1]], nvM6SweepState, emp, rfl,
     nvM6Sweep_invW, by decide, by decide, nvM6Sweep_tmkZero, hm,
     fun r s' m' hd _ _ ht _ hdom _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨s', hd, ht, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_m6_sweep_vars`,
    parameterized by `full_m6_sweep_vars_wp`. -/
theorem nv_m6_sweep_vars_of
    (hVars : ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp m6SweepEnv full_m6_sweep_vars_body args m Q X) :
    Func.wp m6SweepEnv full_m6_sweep_vars_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
        M6TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState ⋆ emp) nvM6SweepMem := by
    rw [sep_emp]; exact nvM6SweepMem_ok
  exact hVars _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, nvM6SweepState, emp, rfl,
     nvM6Sweep_invW.toDense, nvM6Sweep_tmkZero, hm,
     fun r s' m' hd _ _ ht hdom _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨s', hd, ht, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_m6_sweep_dense` under `m6SweepEnv` with
    `inconsistent = 0#64` and `XPost := fun _ _ _ _ => False`. -/
theorem nv_m6_sweep_dense :
    Func.wp m6SweepEnv full_m6_sweep_dense_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM6SweepMem
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
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, nvM6SweepState,
     Std.ExtHashMap.emp, rfl, nvM6Sweep_invW.toDense,
     (by rw [Std.ExtHashMap.sep_emp]; exact nvM6SweepMem_ok),
     fun r s' m' hinv' _ _ hr _ hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨s', hinv', hr, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_m6_sweep_sat` under `m6SweepEnv` with
    `inconsistent = 0#64` and `XPost := fun _ _ _ _ => False`. -/
theorem nv_m6_sweep_sat :
    Func.wp m6SweepEnv full_m6_sweep_sat_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM6SweepSparseMem
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
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, nvM6SweepSparseState,
     Std.ExtHashMap.emp, rfl, nvM6SweepSparse_inv,
     (by rw [Std.ExtHashMap.sep_emp]; exact nvM6SweepSparseMem_ok),
     fun r s' m' hsp' hlvl' _ hr _ hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨s', hsp', hlvl', hr, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_sweep_sat_m6` under `m6SweepEnv` with
    `inconsistent = 0#64` and `XPost := fun _ _ _ _ => False`. -/
theorem nv_full_sweep_sat_m6 :
    Func.wp m6SweepEnv full_sweep_sat_m6_body
      (FullM4Sweep.nvM4SweepCfg.hdr, ()) nvM6SweepSparseMem
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
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, nvM6SweepSparseState,
     Std.ExtHashMap.emp, rfl, nvM6SweepSparse_inv,
     (by rw [Std.ExtHashMap.sep_emp]; exact nvM6SweepSparseMem_ok),
     fun r s' m' hsp' hlvl' _ hr _ hm' => ?_⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨s', hsp', hlvl', hr, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM6Sweep
