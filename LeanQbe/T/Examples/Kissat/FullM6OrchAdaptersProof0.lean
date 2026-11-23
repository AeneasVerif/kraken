module

public import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof0
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec3
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M6.0` Orchestrator Adapter Proofs — Part 0 (`FullM6OrchAdaptersProof0`)

Defines clean `M6Hdr`-aware contracts (`m6aBumpAnalyzedSpec`, `m6aRestoreBumpAnaSpec`,
`m6aAnaFailedLitSpec`, `m6aRephaseSpec`, `m6aVivifyTierSpec`, `m6aVivifySpec`) with full
`_of`/`_elim`/`_monoX` combinators (`0` `@[expose]`, plain `public section`), and proves
parametric `Func.wp` certifications for `13` of the `16` adapters in
`FullM6OrchAdapters.lean`:
1. All `8` direct canonical forwarders (`full_scale_delta`, `full_prop_lit_raw`,
   `full_propagate_ignore`, `full_propagate`, `full_add_bin`, `full_bve_var`, `full_forward_sub`,
   `full_init_fresh_var`), plus `_canon_dcap0` / `full_propagate_preserves_sparseInv` /
   `full_add_bin_canon_wp` bridges.
2. `full_probe_dticks_m6_hdr` (`FullM6Hdr.m6HdrW2aSpec [.bool] [i64]`).
3. `full_analyze_m6_hdr` (`FullM6Hdr.m6HdrAnalyzeSpec`).
4. `full_rephase_m6_hdr` (`m6aRephaseSpec`).
5. `full_vivify_tier_m6_hdr` (`m6aVivifyTierSpec`) and `full_vivify_m6_hdr` (`m6aVivifySpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6OrchAdapters

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open FullVivTopTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open scoped FullVivTopTactics
open Kraken.Bedrock2.Test

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "c0_hcall " h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

open Lean Elab Tactic in
local elab "m6_step_nojnz" : tactic => do
  let g ← getMainGoal
  let rawTy ← Lean.instantiateMVars (← g.getType)
  let ty := rawTy.consumeMData
  if rawTy.isMData then
    replaceMainGoal [← g.change ty (checkDefEq := false)]
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
      ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
    failure
  if !(← LeanQbe.T.C0Step.stepOnce) then
    failure

open Lean Elab Tactic in
local elab "m6_step_jnz" : tactic => do
  let g ← getMainGoal
  let rawTy ← Lean.instantiateMVars (← g.getType)
  let ty := rawTy.consumeMData
  if rawTy.isMData then
    replaceMainGoal [← g.change ty (checkDefEq := false)]
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
      ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
    let _ ← LeanQbe.T.C0Step.stepOnce

local macro "m6_to_group" : tactic => `(tactic| c0_hsteps_nogrp)

local macro "m6_split" : tactic => `(tactic| ((repeat m6_step_nojnz); m6_step_jnz))

private theorem bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fullSparseInvW_of_core_eq_ext {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hcore ▸ h.2.1, ?_, ?_, ?_, hcore ▸ h.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hcore]; exact h.2.2.2.1
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs; rwa [hcore]

private theorem fullSparseInv_of_core_eq_m6 {c : FullCfg} {F0 : CNF Nat}
    {s s' : FullState} (h : FullSparseInv c F0 s)
    (hlen' : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hpres : M6HdrScratchPres s s') : FullSparseInv c F0 s' := by
  obtain ⟨hcore_inv, hmc, hvn, hsc, hdm⟩ := h
  refine ⟨⟨hlen', ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨F_cur, hw⟩ := hcore_inv.2
    exact ⟨F_cur, by rw [hcore]; exact hw⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact hmc
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hcore]; exact hvn
  · exact FullExtScratchOk.of_pres hsc hpres.extPres fun r hr => by
      unfold fullArenaClauseRefs; rwa [hcore]
  · rw [hcore]; exact hdm

/-! ## 1. `M6Hdr`-Aware Adapter Specifications (`_of`, `_elim`, `_monoX`) -/

/-- `full_bump_analyzed_m6_hdr(h)`: lifted `Full.fullBumpAnalyzedSpec` over `FullM6HdrMem`,
preserving `tmp`, `tmp_len`, `cur_vars`, `work_stk2`, `FullExtScratchPres`, and `M6HdrExtOk`
(`ext' = ext` once `M6HdrExtInitOk ext`). -/
def m6aBumpAnalyzedSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullAnaMarksCov c s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ mrk' mcl' sc' ext' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → FullAnaMarksCov c s' → FullExtScratchPres s s' →
      sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem m6aBumpAnalyzedSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hcov : FullAnaMarksCov c s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' sc' ext' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → FullAnaMarksCov c s' → FullExtScratchPres s s' →
      sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    m6aBumpAnalyzedSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hcov, hm, hQ⟩

theorem m6aBumpAnalyzedSpec_elim {h : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} (hs : m6aBumpAnalyzedSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      s.LengthsOk c ∧ FullAnaMarksCov c s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' sc' ext' m',
        let s' : FullState :=
          { s with core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
        s'.LengthsOk c → FullAnaMarksCov c s' → FullExtScratchPres s s' →
        sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' := hs

theorem m6aBumpAnalyzedSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m6aBumpAnalyzedSpec xs m Q X) : m6aBumpAnalyzedSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-- `full_restore_bump_ana_m6_hdr(h)`: lifted `m6RestoreBumpAnaSpec` over `FullM6HdrMem`,
preserving `tmp`, `tmp_len`, `cur_vars`, `work_stk2`, `FullExtScratchPres`, and `M6HdrExtOk`. -/
def m6aRestoreBumpAnaSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ mrk' mcl' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem m6aRestoreBumpAnaSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    m6aRestoreBumpAnaSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩

theorem m6aRestoreBumpAnaSpec_elim {h : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} (hs : m6aRestoreBumpAnaSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      s.LengthsOk c ∧ (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
        s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (s.core.probing = 0#64 → mcl' = 0) →
        (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' := hs

theorem m6aRestoreBumpAnaSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m6aRestoreBumpAnaSpec xs m Q X) : m6aRestoreBumpAnaSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-- `full_ana_failed_lit_m6_hdr(h)`: level-1 failed-literal / multi-UIP resolution over
`FullM6HdrMem`. -/
def m6aAnaFailedLitSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    Full.FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧
    Full.FullConflictOkCut F_cur cut s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6aAnaFailedLitSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hcut : Full.FullCutInvW c F0 F_cur cut s) (hcl : 0 < s.core.cur_level)
    (hc : Full.FullConflictOkCut F_cur cut s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6aAnaFailedLitSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, hcl, hc, hm, hQ⟩

theorem m6aAnaFailedLitSpec_elim {h : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m6aAnaFailedLitSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
      (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      Full.FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧
      Full.FullConflictOkCut F_cur cut s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
        s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
        (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
        (r = 1#64 → Full.FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6aAnaFailedLitSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m6aAnaFailedLitSpec xs m Q X) : m6aAnaFailedLitSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-- `full_rephase_m6_hdr(h)`: lifted `FullM5Sched.m5RephaseSpec` over `FullM6HdrMem` in sparse mode
(`dense_mode = 0#64`), allowing `full_walk` (`fullWarmupSpec`) updates with `FullArenaPermEq`
and `M6_WM_REPHASE_TICKS` watermark update. -/
def m6aRephaseSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullCoreInv c F0 s ∧
    s.core.dense_mode = 0#64 ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' cl' unass' unfl'
      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
            propagated := prop', probing := prob', cur_level := cl', unassigned := unass',
            unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
            wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullCoreInv c F0 s' → FullArenaPermEq s.core s'.core →
      (s.scratch.stable ≠ 0#64 → cl' = 0) →
      cl' ≤ s.core.cur_level → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem m6aRephaseSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hinv : FullCoreInv c F0 s)
    (hdm0 : s.core.dense_mode = 0#64) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' cl' unass' unfl'
      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
            propagated := prop', probing := prob', cur_level := cl', unassigned := unass',
            unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
            wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullCoreInv c F0 s' → FullArenaPermEq s.core s'.core →
      (s.scratch.stable ≠ 0#64 → cl' = 0) →
      cl' ≤ s.core.cur_level → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    m6aRephaseSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hcfg, hext, hinv, hdm0, hm, hQ⟩

theorem m6aRephaseSpec_elim {h : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} (hs : m6aRephaseSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullCoreInv c F0 s ∧ s.core.dense_mode = 0#64 ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' cl' unass' unfl'
        wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
              propagated := prop', probing := prob', cur_level := cl', unassigned := unass',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
              wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
            scratch := sc' }
        M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullCoreInv c F0 s' → FullArenaPermEq s.core s'.core →
        (s.scratch.stable ≠ 0#64 → cl' = 0) →
        cl' ≤ s.core.cur_level → fuel'.toNat ≤ s.core.fuel.toNat →
        FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' := hs

theorem m6aRephaseSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m6aRephaseSpec xs m Q X) : m6aRephaseSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-- Lift `FullSparseInv c F0 s` across `full_rephase_m6_hdr` (`mrk`, `lit_mark`, and
`dense_mode` unchanged, `FullArenaPermEq` preserving `FullArenaVarsNodup` and `FullLastLearnedWf`).
-/
theorem fullSparseInv_of_rephase {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' ftrl' fdec' : List (BitVec 32)}
    {te' prop' cl' : Nat} {prob' unass' unfl' : BitVec 64}
    {wvec' arena' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' fuel' : BitVec 64}
    {ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (hc' : FullCoreInv c F0
      { core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
          propagated := prop', probing := prob', cur_level := cl', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
          confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' })
    (hperm : FullArenaPermEq s.core
      { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
        trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
        propagated := prop', probing := prob', cur_level := cl', unassigned := unass',
        unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
        wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
        confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' })
    (hpres : FullExtScratchPres s
      { core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
          propagated := prop', probing := prob', cur_level := cl', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
          confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' }) :
    FullSparseInv c F0
      { core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
          propagated := prop', probing := prob', cur_level := cl', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
          confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' } := by
  refine ⟨hc', hsp.2.1, ?_, ⟨?_, ?_⟩, hsp.2.2.2.2⟩
  · intro r hr hng
    have hr1 : r ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ hr
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 r hr1
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.1 r hr1 (hgb.symm.trans hng))
  · intro i hi
    dsimp only [fullArenaClauseRefs]
    rw [hpres.1, hperm.2.1]
    exact hsp.2.2.2.1.1 i hi
  · change sc'.extend_len ≤ c.extend_cap
    rw [hpres.2]
    exact hsp.2.2.2.1.2

/-- `full_vivify_tier_m6_hdr(h, tier_mode, budget, tick_lim)` contract over `FullMem`. -/
def m6aVivifyTierSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, _tier_mode, budget, _tick_lim, ()) m Q _ =>
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

theorem m6aVivifyTierSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {tm budget tl : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r s' m',
      FullSparseInv c F0 s' →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      (budget ≠ 0#64 → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m6aVivifyTierSpec (c.hdr, tm, budget, tl, ()) m Q X :=
  ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩

theorem m6aVivifyTierSpec_elim {h tm bud tl : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m6aVivifyTierSpec (h, tm, bud, tl, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m', FullSparseInv c F0 s' →
        (s.core.cur_level = 0 → s'.core.cur_level = 0) →
        (s.core.probing = 0#64 → s'.core.probing = 0#64) →
        (bud ≠ 0#64 → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6aVivifyTierSpec_monoX {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m6aVivifyTierSpec xs m Q X) :
    m6aVivifyTierSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

/-- `full_vivify_m6_hdr(h)` top-level multi-tier probing vivification hook on `M6HdrExt`. -/
def m6aVivifySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6aVivifySpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hsp : FullSparseInv c F0 s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6aVivifySpec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩

theorem m6aVivifySpec_elim {h : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m6aVivifySpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullSparseInv c F0 s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullSparseInv c F0 s' → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6aVivifySpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m6aVivifySpec xs m Q X) : m6aVivifySpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-! ## 2. Eight Direct Canonical Forwarders (`Func.wp` & `dcap0`/`sparseInv` Bridges) -/

theorem full_scale_delta_wp (Γ : Env)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Func.wp Γ full_scale_delta_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, R, rfl, hlen, hm, hQ⟩ := hs
  unfold Func.wp full_scale_delta_body
  c0_hsteps_nogrp
  c0_call hScale
  refine ⟨c, s, R, rfl, hlen, hm, fun r => ?_⟩
  c0_steps
  exact hQ r

theorem full_prop_lit_raw_wp (Γ : Env)
    (hRaw : ∀ a m Q X, FullM6BcpS15.fullPropLitS15Spec a m Q X →
      Γ "full_prop_lit_raw_s15" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, FullM6BcpS15.fullPropLitS15Spec a m Q X →
      Func.wp Γ full_prop_lit_raw_body a m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hinv, hden, hoom, hm, hQ⟩ := hs
  unfold Func.wp full_prop_lit_raw_body
  c0_hsteps_nogrp
  c0_call hRaw
  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hinv, hden, hoom, hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
      ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
      hlen' hinv' htr har hdel hok htrue hm' => ?_⟩
  c0_steps
  exact hQ ok vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
    ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
    hlen' hinv' htr har hdel hok htrue hm'

/-- Under `c.delayed_cap = 0`, `full_prop_lit_raw` satisfies unchanged `Full.fullPropLitSpec`. -/
theorem full_prop_lit_raw_wp_canon_dcap0 (Γ : Env)
    (hRaw : ∀ a m Q X, FullM6BcpS15.fullPropLitS15Spec a m Q X →
      Γ "full_prop_lit_raw_s15" [i64, i32, i64] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {lit : BitVec 32} {ignore_ref : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hdcap0 : c.delayed_cap = 0)
    (hlen0 : s.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hdense0 : s.core.dense_mode = 0#64) (hoom0 : s.core.oom = 0#64)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk'
      wlen' wu' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      (ok = false → oom' ≠ 0#64 ∨
        (FullConflictOkW F_cur s' ∧ (ctype' = 2#64 → cref' ≠ ignore_ref))) →
      (ok = true → oom' = 0#64 ∧ ctype' = s.core.confl_type) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Func.wp Γ full_prop_lit_raw_body (c.hdr, lit, ignore_ref, ()) m Q X := by
  apply full_prop_lit_raw_wp Γ hRaw
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hoom0, hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
      ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
      hlen' hw' htr' hperm' hd0 hcf hok hm' => ?_⟩
  have hdeq : delayed' = s.scratch.delayed := hd0 hdcap0
  subst hdeq
  exact hQ ok vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
    ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm' hcf hok hm'

theorem full_propagate_ignore_wp (Γ : Env)
    (hPropIgn : ∀ a m Q X, FullM6BcpS15.fullPropagateIgnoreS15Spec a m Q X →
      Γ "full_propagate_ignore_s15" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullM6BcpS15.fullPropagateIgnoreS15Spec a m Q X →
      Func.wp Γ full_propagate_ignore_body a m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hinv, hden, hm, hQ⟩ := hs
  unfold Func.wp full_propagate_ignore_body
  c0_hsteps_nogrp
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hinv, hden, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
      hlen' hinv' htr har hdel hfu hr h0 h1 h2 hprop hm' => ?_⟩
  c0_steps
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
    hlen' hinv' htr har hdel hfu hr h0 h1 h2 hprop hm'

/-- Under `c.delayed_cap = 0`, `full_propagate_ignore` satisfies unchanged
`Full.fullPropagateIgnoreSpec`. -/
theorem full_propagate_ignore_wp_canon_dcap0 (Γ : Env)
    (hPropIgn : ∀ a m Q X, FullM6BcpS15.fullPropagateIgnoreS15Spec a m Q X →
      Γ "full_propagate_ignore_s15" [i64, i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {ignore_ref : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hdcap0 : c.delayed_cap = 0)
    (hlen0 : s.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hdense0 : s.core.dense_mode = 0#64) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
      wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
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
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s' ∧
        (ctype' = 2#64 → cref' ≠ ignore_ref)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_propagate_ignore_body (c.hdr, ignore_ref, ()) m Q X := by
  apply full_propagate_ignore_wp Γ hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
      hlen' hw' htr' hperm' hd0 hfl' hr hr0 hr1 hr2 hnoop hm' => ?_⟩
  have hdeq : delayed' = s.scratch.delayed := hd0 hdcap0
  subst hdeq
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr' hperm' hfl' hr hr0 hr1 hr2 hnoop hm'

theorem full_propagate_wp (Γ : Env)
    (hBcp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_bcp_s15" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Func.wp Γ full_propagate_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hinv, hden, hm, hQ⟩ := hs
  unfold Func.wp full_propagate_body
  c0_hsteps_nogrp
  c0_call hBcp
  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hinv, hden, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
      hlen' hinv' htr har hdel hfu hr h0 h1 h2 hprop hm' => ?_⟩
  c0_steps
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
    hlen' hinv' htr har hdel hfu hr h0 h1 h2 hprop hm'

/-- Under `c.delayed_cap = 0`, `full_propagate` satisfies unchanged `Full.fullPropagateSpec`. -/
theorem full_propagate_wp_canon_dcap0 (Γ : Env)
    (hBcp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_bcp_s15" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hdcap0 : c.delayed_cap = 0)
    (hlen0 : s.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hdense0 : s.core.dense_mode = 0#64) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
      wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
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
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_propagate_body (c.hdr, ()) m Q X := by
  apply full_propagate_wp Γ hBcp
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
      hlen' hw' htr' hperm' hd0 hfl' hr hr0 hr1 hr2 hnoop hm' => ?_⟩
  have hdeq : delayed' = s.scratch.delayed := hd0 hdcap0
  subst hdeq
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr' hperm' hfl' hr hr0 hr1 hr2 hnoop hm'

theorem full_add_bin_wp (Γ : Env)
    (hAddBin : ∀ a m Q X, FullM6VivBackbone.fullAddBinM6Spec a m Q X →
      Γ "full_add_bin_m6" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, FullM6VivBackbone.fullAddBinM6Spec a m Q X →
      Func.wp Γ full_add_bin_body a m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hinv, hcl0, hent, hm, hQ⟩ := hs
  unfold Func.wp full_add_bin_body
  c0_hsteps_nogrp
  c0_call hAddBin
  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hinv, hcl0, hent, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom'
      inc' phases' wsort' m' hlen' hinv' hr h20 h2 hm' => ?_⟩
  c0_steps
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
    oom' inc' phases' wsort' m' hlen' hinv' hr h20 h2 hm'

/-- Canonical `Full.fullAddBinSpec` forwarder when `full_add_bin_m6` satisfies
`FullM6VivBackbone.fullAddBinM6Spec`. -/
theorem full_add_bin_canon_wp (Γ : Env)
    (hAddBin : ∀ a m Q X, FullM6VivBackbone.fullAddBinM6Spec a m Q X →
      Γ "full_add_bin_m6" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, Full.fullAddBinSpec a m Q X →
      Func.wp Γ full_add_bin_body a m Q X :=
  fun a m Q X h => full_add_bin_wp Γ hAddBin a m Q X h

theorem full_bve_var_wp (Γ : Env)
    (hBveVar : ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m6" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Func.wp Γ full_bve_var_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, s, R, rfl, hden, htmk, hv, hm, hQ⟩ := hs
  unfold Func.wp full_bve_var_body
  c0_hsteps_nogrp
  c0_call hBveVar
  refine ⟨c, F0, s, R, rfl, hden, htmk, hv, hm,
    fun r s' m' hden' htmk' hcv hfu hr h20 hm' => ?_⟩
  c0_steps
  exact hQ r s' m' hden' htmk' hcv hfu hr h20 hm'

theorem full_forward_sub_wp (Γ : Env)
    (hFwdSub : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m6" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Func.wp Γ full_forward_sub_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, s, R, rfl, hden, hm, hQ⟩ := hs
  unfold Func.wp full_forward_sub_body
  c0_hsteps_nogrp
  c0_call hFwdSub
  refine ⟨c, F0, s, R, rfl, hden, hm, fun r s' m' hden' hfu hr h20 hm' => ?_⟩
  c0_steps
  exact hQ r s' m' hden' hfu hr h20 hm'

theorem full_init_fresh_var_wp (Γ : Env)
    (hInitFv : ∀ a m Q X, Full.fullInitFreshVarSpec a m Q X →
      Γ "full_init_fresh_var_m6" [i64, i32] [] a m Q X) :
    ∀ a m Q X, Full.fullInitFreshVarSpec a m Q X →
      Func.wp Γ full_init_fresh_var_body a m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, R, rfl, hlen, hfv, hm, hQ⟩ := hs
  unfold Func.wp full_init_fresh_var_body
  c0_hsteps_nogrp
  c0_call hInitFv
  refine ⟨c, s, R, rfl, hlen, hfv, hm,
    fun vals' mrk' flags' lvl' rsns' wvec' unass' sc' m'
      hlen' hpres hbuf hv0 hv1 hvl hm0 hmv hl0 hlv hr0 hrv hw0 hwi hm' => ?_⟩
  c0_steps
  exact hQ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m'
    hlen' hpres hbuf hv0 hv1 hvl hm0 hmv hl0 hlv hr0 hrv hw0 hwi hm'

/-! ## 3. `full_probe_dticks_m6_hdr` & `full_analyze_m6_hdr` -/

theorem full_probe_dticks_m6_hdr_wp (Γ : Env)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp Γ full_probe_dticks_m6_hdr_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp full_probe_dticks_m6_hdr_body
  c0_hsteps_nogrp
  m6h_call hGetWm
  refine m6HdrW2aSpec_of rfl hcfg hext hlen ((fullM6HdrMem_iff ..).mpr hm)
    fun ⟨last_p, ⟨⟩⟩ ext1 s1 m1 hcore1 hlen1 hsc1 hext1 hpres1 hm1 => ?_
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps
  all_goals
    refine hQ (_, ()) ext1 s1 _ hcore1 hlen1 hsc1 hext1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1)

theorem full_analyze_m6_hdr_wp (Γ : Env)
    (hUpd : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_update_tier_limits" [i64] [] a m Q X)
    (hDrUpd : ∀ a m Q X, m6HdrDrMutSpec a m Q X →
      Γ "m6_hdr_dr_update" [i64] [] a m Q X)
    (hAnaCore : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_core_m6" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Func.wp Γ full_analyze_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hconf, hm, hQ⟩ := m6HdrAnalyzeSpec_elim hs
  have hcfg := hinv.cfgOk
  have hext := hinv.extOk
  have hsp := hinv.sparseW
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp full_analyze_m6_hdr_body
  c0_hsteps_nogrp
  · have hcl0 : s.core.cur_level = 0 := by
      have hle := hsp.2.1.cur_level_le
      have hte := hsp.1.core_ok.trail_end_le
      have hcv := hsp.1.core_ok.cur_vars_le
      have hmv := c.hmaxv; unfold dimacsBound at hmv
      have h0 : BitVec.ofNat 64 s.core.cur_level = 0#64 := hc
      have h1 := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      exact h1
    exact hQ 20#64 ext s m hext hsp.1 (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _)
      ⟨rfl, fun _ => ⟨hsp.toOtfs, Nat.le_refl _, rfl⟩⟩
      (fun _ => level0_unsat_of_conflict_okW hsp.2.1 hcl0 hconf)
      (fun h0 => by cases h0) (fun h1 => by cases h1) ((fullM6HdrMem_iff ..).mpr hm)
  · refine wp_join_group (ts := [])
      (fun () m2 => ∃ ext2 s2, s2.core = s.core ∧ s2.LengthsOk c ∧ M6HdrScratchPres s s2 ∧
        M6HdrExtOk ext2 ∧ (FullM6HdrMem c ext2 s2 ⋆ R) m2)
      (fun _ () m2 ⟨ext2, s2, heq2, hlen2, hsc2, hext2, hm2⟩ => ?_)
      (fun _ hJp => ?_)
    · have hsp2 : FullSparseInvW c F0 F_cur s2 :=
        fullSparseInvW_of_core_eq_ext hsp hlen2 heq2 hsc2.extPres
      have hinv2 : FullM6HdrInvW c F0 F_cur ext2 s2 :=
        FullM6HdrInvW.mk_inv hcfg hext2 hsp2
      have hconf2 : FullConflictOkW F_cur s2 := by
        unfold FullConflictOkW fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
          fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaHdrCore
          fullArenaClauseLitsCore fullArenaClauseSizeCore at hconf ⊢
        rwa [heq2]
      c0_hsteps_nogrp
      m6h_call hAnaCore
      refine m6HdrAnalyzeSpec_of hinv2 hconf2 hm2
        fun r ext3 s3 m3 hext3 hlen3 hdom hcv3 hfu3 ⟨hws3, h20s⟩ hu3 h0 h1 hm3 => ?_
      c0_hsteps
      exact hQ r ext3 s3 m3 hext3 hlen3 hdom (by rw [heq2] at hcv3; exact hcv3)
        (by rw [heq2] at hfu3; exact hfu3)
        ⟨hws3.trans hsc2.ws2, fun h20 => by
          have ⟨ho20, hcl20, hdm20⟩ := h20s h20
          rw [heq2] at hcl20 hdm20; exact ⟨ho20, hcl20, hdm20⟩⟩
        hu3 h0 (fun h1eq => by
          have ⟨hinv3, hcl3⟩ := h1 h1eq
          rw [heq2] at hcl3
          exact ⟨hinv3, hcl3⟩) hm3
    · c0_hsteps_nogrp
      · m6h_call hUpd
        refine m6HdrW2aSpec_of rfl hcfg hext hsp.1 ((fullM6HdrMem_iff ..).mpr hm)
          fun () ext1 s1 m1 hcore1 hlen1 hsc1 hext1 _ hm1 => ?_
        c0_hsteps_nogrp
        m6h_call hDrUpd
        refine m6HdrDrMutSpec_of hcfg hext1 hlen1 hm1 fun ext2 m2 hinit2 _ hm2 => ?_
        c0_hsteps
        exact hJp () m2 ⟨ext2, s1, hcore1, hlen1, hsc1, hinit2.toOk, hm2⟩
      · exact hJp () m ⟨ext, s, rfl, hsp.1, M6HdrScratchPres.refl s, hext,
          (fullM6HdrMem_iff ..).mpr hm⟩

/-! ## 4. `full_rephase_m6_hdr` (`m6aRephaseSpec`) -/

private theorem m6a_arenaPerm_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem m6a_arenaPerm_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullArenaPermEq k1 k2) (h2 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2.2 r (h1.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

private theorem m6a_arenaPerm_of_arena_eq {k1 k2 : FullCoreState}
    (ha : k2.arena = k1.arena) (hal : k2.arena_len = k1.arena_len) : FullArenaPermEq k1 k2 := by
  have hrefs : fullArenaClauseRefsCore k2 = fullArenaClauseRefsCore k1 := by
    unfold fullArenaClauseRefsCore; rw [ha, hal]
  refine ⟨hal, hrefs, fun r _ => ?_⟩
  have h1 : fullArenaClauseSizeCore k2 r = fullArenaClauseSizeCore k1 r := by
    unfold fullArenaClauseSizeCore; rw [ha]
  have h2 : fullArenaClauseGarbCore k2 r = fullArenaClauseGarbCore k1 r := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [ha]
  have h3 : fullArenaClauseLitsCore k2 r = fullArenaClauseLitsCore k1 r := by
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [ha]
  exact ⟨h1, h2, h3 ▸ List.Perm.refl _⟩

theorem full_rephase_m6_hdr_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      Γ "full_walk" [i64] [] a m Q X)
    (hLog : ∀ a m Q X, FullM5Sched.m5Log10Q16Spec a m Q X →
      Γ "full_log10_q16" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m6aRephaseSpec a m Q X →
      Func.wp Γ full_rephase_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hinv, hdm0, hm, hQ⟩ := m6aRephaseSpec_elim hs
  have hmaxv := c.hmaxv; unfold LratBytes.dimacsBound at hmaxv
  obtain ⟨F_cur, hw0⟩ := hinv.witness
  have hco0 := hinv.lengths.core_ok
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hmaxv_pos : (0 : BitVec 64).toNat < s.core.cur_level →
      (0 : BitVec 64).toNat < c.max_vars := by
    intro _; have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp full_rephase_m6_hdr_body
  m6_split
  · c0_hsteps
    let sc_early : FullScratch := { s.scratch with rephase_limit := s.scratch.mode_confl_lim }
    have hsc_early : sc_early.LengthsOk c :=
      { hinv.lengths.scratch_ok with walk_vals_len := hinv.lengths.scratch_ok.walk_vals_len }
    have hinv_e : FullCoreInv c F0
        { core := { s.core with fuel := s.core.fuel }, scratch := sc_early } :=
      hinv.with_fuel_scratch_spec ⟨hinv.lengths.core_ok, hsc_early⟩ rfl
    exact hQ s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.propagated s.core.probing
      s.core.cur_level s.core.unassigned s.core.unflushed s.core.wvec s.core.arena s.core.wstk
      s.core.wlen s.core.wusable s.core.fuel s.core.confl_type s.core.confl_ref
      s.core.confl_lit0 s.core.confl_lit1 s.core.oom sc_early ext m
      ⟨hext, fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩⟩
      hinv_e (m6a_arenaPerm_refl s.core) (fun hst => absurd hc hst) (Nat.le_refl _)
      (Nat.le_refl _) ⟨rfl, rfl⟩ ((fullM6HdrMem_iff ..).mpr hm)
  · refine wp_join_group (ts := [])
      (fun () m1 => ∃ (st1 : FullState),
        FullCoreInv c F0 st1 ∧ st1.core.vals.length = 2 * c.max_vars ∧
        st1.core.cur_vars = s.core.cur_vars ∧ st1.core.cur_level = 0 ∧
        st1.core.fuel = s.core.fuel ∧
        st1.core = { s.core with
          vals := st1.core.vals, lvl := st1.core.lvl, rsns := st1.core.rsns,
          trl := st1.core.trl, trail_pos := st1.core.trail_pos, trail_end := st1.core.trail_end,
          propagated := st1.core.propagated, cur_level := 0, unassigned := st1.core.unassigned } ∧
        FullExtScratchPres s st1 ∧ (FullMem c st1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
      (fun _ () m1 ⟨st1, hinv1, _, hcv1, hcl1, hfu1, hceq1, ⟨hll1, hext1⟩, hm1⟩ => ?_)
      (fun _ hJbt => ?_)
    · clear hm
      have hcv_le : st1.core.cur_vars ≤ c.max_vars := hinv1.lengths.core_ok.cur_vars_le
      have hdm1 : st1.core.dense_mode = 0#64 := by rw [hceq1]; exact hdm0
      have hperm1 : FullArenaPermEq s.core st1.core :=
        m6a_arenaPerm_of_arena_eq (by rw [hceq1]) (by rw [hceq1])
      c0_hsteps_nogrp
      let sc2 : FullScratch := { st1.scratch with rephased := st1.scratch.rephased + 1#64 }
      have hsc2_ok : sc2.LengthsOk c :=
        { hinv1.lengths.scratch_ok with walk_vals_len := hinv1.lengths.scratch_ok.walk_vals_len }
      let st2 : FullState := { st1 with scratch := sc2 }
      have hinv2 : FullCoreInv c F0 st2 :=
        hinv1.with_fuel_scratch_spec ⟨hinv1.lengths.core_ok, hsc2_ok⟩ rfl
      refine wp_join_group (ts := []) (fun () m2 => ∃ (core3 : FullCoreState) (sc3 : FullScratch),
        FullCoreInv c F0 { core := core3, scratch := sc3 } ∧
        FullArenaPermEq s.core core3 ∧
        core3.fuel.toNat ≤ st1.core.fuel.toNat ∧
        core3.cur_vars = st1.core.cur_vars ∧
        core3 = { s.core with
          vals := core3.vals, flags := core3.flags, lvl := core3.lvl, rsns := core3.rsns,
          trl := core3.trl, trail_pos := core3.trail_pos, frame_trail := core3.frame_trail,
          frame_dec := core3.frame_dec, trail_end := core3.trail_end,
          propagated := core3.propagated, probing := core3.probing, cur_level := 0,
          unassigned := core3.unassigned, unflushed := core3.unflushed, wvec := core3.wvec,
          arena := core3.arena, wstk := core3.wstk, wlen := core3.wlen,
          wusable := core3.wusable, fuel := core3.fuel, confl_type := core3.confl_type,
          confl_ref := core3.confl_ref, confl_lit0 := core3.confl_lit0,
          confl_lit1 := core3.confl_lit1, oom := core3.oom } ∧
        sc3.last_learned = s.scratch.last_learned ∧ sc3.extend_len = s.scratch.extend_len ∧
        (FullMem c { core := core3, scratch := sc3 } ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m2)
        ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨core3, sc3, hinv3, hperm3, hfl3, hcv3, hceq3, hll3, hext3, hm2⟩
        have hlen3 := hinv3.lengths
        have hco3 := hlen3.core_ok
        have hsc3 := hlen3.scratch_ok
        refine wp_loop_inv
          (fun (k, ()) m3 => ∃ ptgt' : List (BitVec 8),
            k.toNat ≤ st1.core.cur_vars ∧ ptgt'.length = c.max_vars ∧
            (FullMem c { core := core3, scratch := { sc3 with phases_target := ptgt' } } ⋆
              (array64 (c.hdr - 2304) ext ⋆ R)) m3)
          (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
          (fun L hL => by
            c0_steps
            exact hL (0#64, ()) m2 ⟨sc3.phases_target, Nat.zero_le _, hsc3.phases_target_len, hm2⟩)
          (fun L (k, ()) m3 ⟨ptgt', hk_le, hpt_len, hm3⟩ ih => ?_)
        have hph3 : sc3.phases.length = c.max_vars := hsc3.phases_len
        m6_to_group
        · c0_hsteps
          have hk_lt : k.toNat < st1.core.cur_vars := by
            have : k.toNat < core3.cur_vars := by c0_bound
            omega
          have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
          exact ih (k + 1#64, ()) _ (by dsimp only; omega)
            ⟨ptgt'.set k.toNat (sc3.phases[k.toNat]'(by omega)), by omega,
             by simp [hpt_len], by assumption⟩
        · let st3 : FullState :=
            { core := core3
              scratch := { sc3 with phases_target := ptgt', target_assigned := 0#64 } }
          refine wp_join_group (ts := [i64]) (fun _ m4 =>
            (FullMem c st3 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m4)
            (fun _ (nc, ()) m4 hm4 => ?_) ?_
          · m6_to_group
            c0_call hLog
            intro q _ _
            refine wp_join_group (ts := [i64]) (fun _ m5 =>
              (FullMem c st3 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m5)
              (fun _ (sc_val, ()) m5 hm5 => ?_) ?_
            · c0_hsteps_nogrp
              let sc4 : FullScratch := { sc3 with
                phases_target := ptgt', target_assigned := 0#64,
                rephase_limit := sc3.conflicts + sc_val }
              have hsc4 : sc4.LengthsOk c := { hsc3 with phases_target_len := hpt_len }
              let st4 : FullState := { core := core3, scratch := sc4 }
              have hinv4 : FullCoreInv c F0 st4 :=
                hinv3.with_fuel_scratch_spec ⟨hco3, hsc4⟩ rfl
              m6h_call hSetWm
              refine m6HdrW2aSpec_of rfl hcfg hext hinv4.lengths ((fullM6HdrMem_iff ..).mpr hm)
                fun () ext5 s5 m6 hcore5 hlen5 hsc5 hext5 hw5 hm6 => ?_
              have heq5 : s5.core = st4.core := hcore5
              have hinv_s5 : FullCoreInv c F0 s5 := by
                obtain ⟨F_c, hw_c⟩ := hinv4.witness
                exact ⟨hlen5, F_c, heq5 ▸ hw_c⟩
              have hc' : s5.core = { s.core with
                  vals := core3.vals, flags := core3.flags, lvl := core3.lvl,
                  rsns := core3.rsns, trl := core3.trl, trail_pos := core3.trail_pos,
                  frame_trail := core3.frame_trail, frame_dec := core3.frame_dec,
                  trail_end := core3.trail_end, propagated := core3.propagated,
                  probing := core3.probing, cur_level := 0, unassigned := core3.unassigned,
                  unflushed := core3.unflushed, wvec := core3.wvec, arena := core3.arena,
                  wstk := core3.wstk, wlen := core3.wlen, wusable := core3.wusable,
                  fuel := core3.fuel, confl_type := core3.confl_type,
                  confl_ref := core3.confl_ref, confl_lit0 := core3.confl_lit0,
                  confl_lit1 := core3.confl_lit1, oom := core3.oom } := by
                rw [heq5]; exact hceq3
              have hs5_eq : s5 =
                  { core := { s.core with
                      vals := core3.vals, flags := core3.flags, lvl := core3.lvl,
                      rsns := core3.rsns, trl := core3.trl, trail_pos := core3.trail_pos,
                      frame_trail := core3.frame_trail, frame_dec := core3.frame_dec,
                      trail_end := core3.trail_end, propagated := core3.propagated,
                      probing := core3.probing, cur_level := 0, unassigned := core3.unassigned,
                      unflushed := core3.unflushed, wvec := core3.wvec, arena := core3.arena,
                      wstk := core3.wstk, wlen := core3.wlen, wusable := core3.wusable,
                      fuel := core3.fuel, confl_type := core3.confl_type,
                      confl_ref := core3.confl_ref, confl_lit0 := core3.confl_lit0,
                      confl_lit1 := core3.confl_lit1, oom := core3.oom }
                    scratch := s5.scratch } := by
                cases s5; simp only [FullState.mk.injEq, and_true]; exact hc'
              c0_steps
              refine hQ core3.vals core3.flags core3.lvl core3.rsns core3.trl core3.trail_pos
                core3.frame_trail core3.frame_dec core3.trail_end core3.propagated
                core3.probing 0 core3.unassigned core3.unflushed core3.wvec core3.arena
                core3.wstk core3.wlen core3.wusable core3.fuel core3.confl_type
                core3.confl_ref core3.confl_lit0 core3.confl_lit1 core3.oom s5.scratch
                ext5 m6 ⟨hext5, hw5⟩ (hs5_eq ▸ hinv_s5) (by rw [← hc', heq5]; exact hperm3)
                (fun _ => rfl) (Nat.zero_le _) (hfu1 ▸ hfl3)
                ⟨hsc5.extPres.1.trans hll3, hsc5.extPres.2.trans hext3⟩ (hs5_eq ▸ hm6)
            · intro _ hJsc
              m6_split
              · c0_steps; exact hJsc (_, ()) m4 hm4
              · m6_to_group
                refine wp_join_group (ts := [i64]) (fun _ m5 => m4 = m5)
                  (fun _ (nlim, ()) _ hm5 => ?_) ?_
                · rcases hm5 with rfl; c0_steps; exact hJsc (_, ()) m4 hm4
                · intro _ hJn; c0_steps
                  · exact hJn (100000000#64, ()) m4 rfl
                  · exact hJn (_, ()) m4 rfl
          · intro _ hJnc; c0_steps
            · exact hJnc _ _ (by assumption)
            · exact hJnc _ _ (by assumption)
      · intro Jsel hJsel
        m6_split
        · refine wp_loop_inv
            (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
              k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
              (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆
                (array64 (c.hdr - 2304) ext ⋆ R)) m3)
            (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
            (fun L hL => by
              c0_hsteps; refine hL (0#64, ()) _
                ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, by assumption⟩)
            (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
          have hpb_l := hsc2_ok.phases_best_len
          c0_hsteps
          · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
            exact ih (k + 1#64, ()) _ (by dsimp only; omega)
              ⟨ph'.set k.toNat (sc2.phases_best[k.toNat]'(by omega)),
                by omega, by simp [hph_l], by assumption⟩
          · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
            exact ih (k + 1#64, ()) m3 (by dsimp only; omega) ⟨ph', by omega, hph_l, hm3⟩
          · let sc3 : FullScratch := { sc2 with phases := ph', best_assigned := 0#64 }
            have hinv3 : FullCoreInv c F0 { core := st1.core, scratch := sc3 } :=
              hinv1.with_fuel_scratch_spec
                ⟨hinv1.lengths.core_ok, { hsc2_ok with phases_len := hph_l }⟩ rfl
            refine hJsel () _
              ⟨st1.core, sc3, hinv3, hperm1, Nat.le_refl _, rfl,
               by rw [hceq1], hll1, hext1, by assumption⟩
        · m6_split
          · c0_call hWalk
            refine ⟨c, F0, st2, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv2, hdm1, by assumption,
              fun vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' unass' unfl'
                wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc3 m3
                hinv3 hperm3 hfl3 hpres3 _ hm3 => ?_⟩
            c0_hsteps
            exact hJsel () m3 ⟨_, sc3, hinv3, m6a_arenaPerm_trans hperm1 hperm3, hfl3,
              by simp [st2], by dsimp only [st2]; rw [hceq1],
              hpres3.1.trans hll1, hpres3.2.trans hext1, hm3⟩
          · m6_split
            · refine wp_loop_inv
                (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                  k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
                  (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆
                    (array64 (c.hdr - 2304) ext ⋆ R)) m3)
                (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
                (fun L hL => by
                  c0_hsteps; refine hL (0#64, ()) _
                    ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, by assumption⟩)
                (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
              c0_hsteps
              · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
                exact ih (k + 1#64, ()) _ (by dsimp only; omega)
                  ⟨ph'.set k.toNat (1#8), by omega, by simp [hph_l], by assumption⟩
              · c0_hsteps
                let sc3 : FullScratch := { sc2 with phases := ph' }
                have hinv3 : FullCoreInv c F0 { core := st1.core, scratch := sc3 } :=
                  hinv1.with_fuel_scratch_spec
                    ⟨hinv1.lengths.core_ok, { hsc2_ok with phases_len := hph_l }⟩ rfl
                refine hJsel () m3 ⟨st1.core, sc3, hinv3, hperm1, Nat.le_refl _, rfl,
                  by rw [hceq1], hll1, hext1, hm3⟩
            · refine wp_loop_inv
                (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                  k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
                  (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆
                    (array64 (c.hdr - 2304) ext ⋆ R)) m3)
                (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
                (fun L hL => by
                  c0_hsteps; refine hL (0#64, ()) _
                    ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, by assumption⟩)
                (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
              c0_hsteps
              · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
                exact ih (k + 1#64, ()) _ (by dsimp only; omega)
                  ⟨ph'.set k.toNat (0xFF#8), by omega, by simp [hph_l], by assumption⟩
              · c0_hsteps
                let sc3 : FullScratch := { sc2 with phases := ph' }
                have hinv3 : FullCoreInv c F0 { core := st1.core, scratch := sc3 } :=
                  hinv1.with_fuel_scratch_spec
                    ⟨hinv1.lengths.core_ok, { hsc2_ok with phases_len := hph_l }⟩ rfl
                refine hJsel () m3 ⟨st1.core, sc3, hinv3, hperm1, Nat.le_refl _, rfl,
                  by rw [hceq1], hll1, hext1, hm3⟩
    · c0_hsteps_nogrp
      · c0_call hBacktrack
        refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.lengths, hcl_lt64, hmaxv_pos,
          hw0.trail_lits_lt, hm,
          fun vals' lvl' rsns' trl' tp' te' prop' cl' unas' sc1 m1
            hlen1 _ _ hcl' hpres1 _ _ _ hwinv1 _ hm1 => ?_⟩
        have hcl'0 : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
        subst hcl'0
        let st1 : FullState :=
          { core := { s.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
              trail_end := te', propagated := prop', cur_level := 0, unassigned := unas' }
            scratch := sc1 }
        have hw1 : FullWitnessInv c F0 F_cur st1.core := hwinv1 F0 F_cur hw0 (Nat.zero_le _)
        exact hJbt () m1 ⟨st1, ⟨hlen1, F_cur, hw1⟩, hlen1.core_ok.vals_len, rfl, rfl, rfl,
          rfl, hpres1.1, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by c0_bound
        have heq0 : s.core = { s.core with cur_level := 0 } := by
          have hcl' : s.core.cur_level = 0 := hcl0
          cases hs : s.core; simp only [hs] at hcl'
          simp only [FullCoreState.mk.injEq, true_and, and_true]; exact hcl'
        exact hJbt () m ⟨s, hinv, hco0.vals_len, rfl, hcl0, rfl, heq0, ⟨rfl, rfl⟩, hm⟩

/-! ## 5. `full_vivify_tier_m6_hdr` & `full_vivify_m6_hdr` -/

private theorem m6b_sparse_with_tr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem m6b_sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem m6_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases',
                                  delayed := delayed' } } :
      FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases',
                                  delayed := delayed' } }
  have hnd' : FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsp hlen' hw' hnd'
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hrefs

theorem full_vivify_tier_m6_hdr_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, FullM6VivBackbone.fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, FullM6VivBackbone.fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hKeys : ∀ a m Q X, FullM6VivBackbone.fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, FullM6VivBackbone.fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, FullM6VivBackbone.fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, FullM6VivBackbone.fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6aVivifyTierSpec a m Q X →
      Func.wp Γ full_vivify_tier_m6_hdr_body a m Q X := by
  rintro ⟨h, tier_mode, budget0, tick_lim, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩ := m6aVivifyTierSpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  unfold Func.wp full_vivify_tier_m6_hdr_body; fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 (fun h => h) (fun h => h) (fun hb => absurd (by c0_bound) hb)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m ⟨s1, hsp1, hcl1, hfl1, hm⟩
    fvt_steps
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ R) m := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear_value s2
    clear hsp1 hcl1 hfl1
    c0_call hCollect
    refine ⟨c, F0, s2, R, rfl, hsp2, hm2, fun bn rr3 m3 h3bn hrr3 hok3 hm3 => ?_⟩
    let s3 : FullState := { s2 with scratch := { s2.scratch with red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 := m6b_sparse_with_rr hsp2 hrr3
    c0_call hCount
    refine ⟨c, F0, s3, R, rfl, hsp3, h3bn, hok3, hm3, fun tr3 m3c htr3 hm3c => ?_⟩
    let s3c : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := tr3 } }
    have hsp3c : FullSparseInv c F0 s3c := m6b_sparse_with_tr hsp3 htr3
    c0_call hKeys
    refine ⟨c, F0, s3c, R, rfl, hsp3c, h3bn, hok3, hm3c, fun rr4 m4 hrr4 hok4 hm4 => ?_⟩
    let s4 : FullState := { s3c with scratch := { s3c.scratch with red_refs := rr4 } }
    have hsp4 : FullSparseInv c F0 s4 := m6b_sparse_with_rr hsp3c hrr4
    c0_call hSortSched
    refine ⟨c, F0, s4, R, rfl, hsp4, h3bn, hok4, hm4,
      fun rr5 m5 hrr5_len hok5 hm5 => ?_⟩
    let s5 : FullState := { s4 with scratch := { s4.scratch with red_refs := rr5 } }
    have hsp5 : FullSparseInv c F0 s5 := m6b_sparse_with_rr hsp4 hrr5_len
    have hfl5 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := hfl2
    have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s2 := rfl
    have hrr5 : s5.scratch.red_refs = rr5 := rfl
    have hok5' : ∀ k < bn.toNat, (rr5[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2 := hok5
    have hm5' : (FullMem c s5 ⋆ R) m5 := hm5
    clear_value s5 s4 s3c s3
    clear s4 s3c s3 hsp4 hsp3c hsp3 tr3 rr3 rr4 htr3 hrr3 hrr4 hok3 hok4 hok5
      hm3 hm3c hm4 hm5 hsp2 hm2 hfl2 hCollect hCount hKeys hSortSched
    c0_hsteps_nogrp
    refine wp_loop_break_group (brkTs := [i64, i64, i64, i64]) (lpTs := [i64, i64, i64])
      (fun (_budget_b, res_b, bi_b, _spent_b, ()) mb => ∃ sb : FullState,
        FullSparseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
        (FullMem c sb ⋆ R) mb)
      (fun rem (budget, bi, spent, ()) mvi => ∃ svi : FullState,
        bi.toNat ≤ bn.toNat ∧ rem = bn.toNat - bi.toNat ∧
        FullSparseInv c F0 svi ∧ svi.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs svi = fullArenaClauseRefs s2 ∧
        svi.scratch.red_refs = rr5 ∧ (FullMem c svi ⋆ R) mvi)
      ?_ ?_ ?_
    · rintro _ ⟨_, res_b, bi_b, _, ⟨⟩⟩ mb ⟨sb, hspb, hflb, hresb, h20b, hmb⟩
      refine wp_join_group (ts := [])
        (fun () m_bt => ∃ sbt : FullState,
          FullSparseInv c F0 sbt ∧ sbt.core.cur_level = 0 ∧
          sbt.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sbt ⋆ R) m_bt) ?_ ?_
      · rintro _ ⟨⟩ m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
        refine wp_join_group (ts := [])
          (fun () m_w => ∃ sw : FullState,
            FullSparseInv c F0 sw ∧ sw.core.cur_level = 0 ∧
            sw.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sw ⋆ R) m_w) ?_ ?_
        · rintro _ ⟨⟩ m_w ⟨sw, hspw, hclw, hflw, hm_w⟩
          fvt_steps
          let sf : FullState := { sw with core := { sw.core with probing := 0#64 } }
          have hspf : FullSparseInv c F0 sf := FullVivTop.FullSparseInv.with_probing hspw 0#64
          exact hQ res_b sf _ hspf (fun _ => hclw) (fun _ => rfl)
            (fun _ => ⟨hclw, rfl⟩) hflw hresb h20b hm
        · intro Jw hJw
          fvt_steps
          · c0_call hClearTier
            refine ⟨c, F0, sbt, R, rfl, hspbt, hclbt, hm_bt,
              fun sw m_w hspw hclw hflw hm_w =>
                hJw () m_w ⟨sw, hspw, hclw, by rw [hflw]; exact hflbt, hm_w⟩⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
      · intro Jbt hJbt
        obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
        have hclb_lt : sb.core.cur_level < 2 ^ 64 := by
          have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
          have := hspb.1.lengths.core_ok.cur_vars_le; omega
        fvt_steps
        · c0_call hBacktrack
          refine ⟨c, sb, R, rfl, hspb.1.lengths, hclb_lt,
            (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro;
                have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
                have := hspb.1.lengths.core_ok.cur_vars_le; omega),
            hswb.2.1.trail_lits_lt, hmb,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ hcl_bt hpres_bt _ _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt : FullSparseInv c F0 _ :=
            FullVivTop.FullSparseInv.of_backtrack hspb (Nat.zero_le _) hlen_bt hpres_bt
              (by simpa using hw_bt F0)
          exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, hflb, hm_bt⟩
        · have hclb0 : sb.core.cur_level = 0 := by
            have h0 : (BitVec.ofNat 64 sb.core.cur_level).toNat = 0 := by rw [hc]; rfl
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclb_lt] at h0
          exact hJbt () mb ⟨sb, hspb, hclb0, hflb, hmb⟩
    · intro B L rem ⟨budget, bi, spent, ⟨⟩⟩ mvi hB hL
        ⟨svi, hbi_le, hrem, hspv, hflv, hrefsv, hrrv, hmvi⟩
      subst hrem
      fvt_steps
      · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
        have hbi3_nat : (bi * 3).toNat = 3 * bi.toNat := by bv_omega
        have hbi3_lt : (bi * 3).toNat < svi.scratch.red_refs.length := by
          rw [hrrv, hrr5_len]; omega
        let cr := svi.scratch.red_refs[(bi * 3).toNat]'hbi3_lt
        have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
          rw [hrefsv]
          have h := hok5' bi.toNat hbi_lt
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
          have heq : cr = rr5[3 * bi.toNat]'(by omega) := Option.some.inj (by
            rw [← List.getElem?_eq_getElem hbi3_lt, hrrv, hbi3_nat,
              List.getElem?_eq_getElem (by omega)])
          rwa [heq]
        have hcr_bnd : cr.toNat + 3 ≤ svi.core.arena_len :=
          (fullArenaScanRefs_mem_bounds hcr_ref).2
        have har_len : svi.core.arena.length = c.arena_cap :=
          hspv.1.lengths.core_ok.arena_len_arr
        have hal_le : svi.core.arena_len ≤ c.arena_cap := hspv.1.lengths.core_ok.arena_len_le
        have har_cr2 : (cr.setWidth 64 + 2#64).toNat < svi.core.arena.length := by bv_omega
        obtain ⟨F_curv, hswv⟩ := hspv.exists_witness
        have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
        fvt_steps
        c0_call hVivClause
        refine ⟨c, F0, F_curv, svi, R, rfl, hswv, hcr_ref, hmvi,
          fun vc s_vc m_vc hsw_vc hfl_vc _ hrefs_vc hrr_vc hvc h20_vc hm_vc => ?_⟩
        have hrefs_vc2 : fullArenaClauseRefs s_vc = fullArenaClauseRefs s2 :=
          hrefs_vc.trans hrefsv
        have hrr_vc5 : s_vc.scratch.red_refs = rr5 := hrr_vc.trans hrrv
        have hfl_vc' : s_vc.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_vc hflv
        fvt_steps
        · exact hB (budget - 1#64, 20#64, bi, _, ()) m_vc
            ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
        · exact hB (budget - 1#64, 1#64, bi, _, ()) m_vc
            ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inl rfl, (fun h => by cases h), hm_vc⟩
        · have hcl_vc_lt : s_vc.core.cur_level < 2 ^ 64 := by
            have := hsw_vc.2.1.cur_level_le; have := hsw_vc.1.core_ok.trail_end_le
            have := hsw_vc.1.core_ok.cur_vars_le; omega
          have hcl_vc0 : s_vc.core.cur_level = 0 := by
            have h0 : (BitVec.ofNat 64 s_vc.core.cur_level).toNat = 0 := by
              have hc0 : BitVec.ofNat 64 s_vc.core.cur_level = 0#64 := by c0_bound
              rw [hc0]; rfl
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_vc_lt] at h0
          c0_call hProp
          refine ⟨c, F0, F_curv, s_vc, R, rfl, hsw_vc.1, hsw_vc.2.1, hsw_vc.2.2.2.2.2, hm_vc,
            fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
              wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
              ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p _ hperm_p _ hfl_p _ _ hpr1 _ _
              hm_p => ?_⟩
          let s_p : FullState :=
            { s_vc with
              core := { s_vc.core with
                vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
              scratch := { s_vc.scratch with
                search_ticks := ticks_p, wsort := wsort_p, phases := phases_p,
                delayed := delayed_p } }
          have hsw_p : FullSparseInvW c F0 F_curv s_p :=
            m6_sparseInvW_of_prop_canon hsw_vc hlen_p hw_p hperm_p
          have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_vc := hperm_p.2.1
          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl_vc'
          fvt_steps
          · have hpr_eq1 : pr = 1#64 := by c0_bound
            have hunsat : F0.Unsat :=
              FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl_vc0 (hpr1 hpr_eq1).2.2
            exact hB (budget - 1#64, 20#64, bi, _, ()) m_p
              ⟨s_p, hsw_p.toSparse, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
          · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, _, ()) m_p
              (by rw [hbi1]; omega)
              ⟨s_p, by rw [hbi1]; omega, rfl, hsw_p.toSparse, hfl_p',
                hrefs_p.trans hrefs_vc2, hrr_vc5, hm_p⟩
        · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, _, ()) m_vc
            (by rw [hbi1]; omega)
            ⟨s_vc, by rw [hbi1]; omega, rfl, hsw_vc.toSparse, hfl_vc', hrefs_vc2, hrr_vc5, hm_vc⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
    · intro B L _ hL; fvt_steps
      exact hL bn.toNat (budget0, 0#64, 0#64, ()) m5
        ⟨s5, Nat.zero_le _, by simp, hsp5, hfl5, hrefs5, hrr5, hm5'⟩
  · intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl0_lt,
        (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro;
            have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
            have := hsp0.1.lengths.core_ok.cur_vars_le; omega),
        hsw0.2.1.trail_lits_lt, hm0,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJc () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
      exact hJc () m0 ⟨s, hsp0, hcl0, Nat.le_refl _, hm0⟩

theorem full_vivify_m6_hdr_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hVivTier : ∀ a m Q X, m6aVivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6aVivifySpec a m Q X →
      Func.wp Γ full_vivify_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩ := m6aVivifySpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  have hspw0 := hsp
  obtain ⟨F_cur, hw0⟩ := hspw0.1.witness
  have hco0 := hspw0.1.lengths.core_ok
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hmax_vars_pos : 0 < s.core.cur_level → 0 < c.max_vars := by
    intro _; have := hw0.cur_level_le; have := hco0.trail_end_le
    have := hco0.cur_vars_le; omega
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp full_vivify_m6_hdr_body; fvt_to_group
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
    (fun _ () m1 ⟨s1, hsp1, hcl01, hfu1, hm1⟩ => ?_) (fun _ hJ => ?_)
  · clear hm
    m6h_call hSync
    refine m6HdrW2aSpec_of rfl hcfg hext hsp1.1.lengths ((fullM6HdrMem_iff ..).mpr hm1)
      fun () ext2 s2 m2 hcore2 hlen2 hsc2 hext2 hw2 hm2 => ?_
    have hsp2 : FullSparseInv c F0 s2 := fullSparseInv_of_core_eq_m6 hsp1 hlen2 hcore2 hsc2
    have hcl02 : s2.core.cur_level = 0 := by rw [hcore2]; exact hcl01
    rw [fullM6HdrMem_iff] at hm2
    c0_hsteps_nogrp
    m6h_call hGetWm
    refine m6HdrW2aSpec_of rfl hcfg hext2 hsp2.1.lengths ((fullM6HdrMem_iff ..).mpr hm2)
      fun ⟨last_p, ⟨⟩⟩ ext3 s3 m3 hcore3 hlen3 hsc3 hext3 hw3 hm3 => ?_
    have hsp3 : FullSparseInv c F0 s3 := fullSparseInv_of_core_eq_m6 hsp2 hlen3 hcore3 hsc3
    have hcl03 : s3.core.cur_level = 0 := by rw [hcore3]; exact hcl02
    have hpres3 : M6HdrExtInitOk ext → M6HdrExtInitOk ext3 ∧ M6ExtW2bPres ext ext3 := fun hi =>
      ⟨(hw3 (hw2 hi).1).1, (hw2 hi).2.trans (hw3 (hw2 hi).1).2⟩
    rw [fullM6HdrMem_iff] at hm3
    have hbud : (0xFFFFFFFF#64 : BitVec 64) ≠ 0#64 := by decide
    fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ md => md = m3) ?_
      (fun Jd hJd => by fvt_steps <;> exact hJd _ m3 rfl)
    rintro _ ⟨delta, ⟨⟩⟩ md hmd; rw [hmd]; fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ me => me = m3) ?_
      (fun Je hJe => by fvt_steps <;> exact hJe _ m3 rfl)
    rintro _ ⟨eff_ref, ⟨⟩⟩ me hme; rw [hme]; fvt_steps
    · c0_call hVivTier
      refine m6aVivifyTierSpec_of hsp3 hm3
        fun r2 s4 m4 hsp4 _ _ hnz2 hfl4 hr2 hu2 hm4 => ?_
      obtain ⟨hcl4, hpr4⟩ := hnz2 hbud
      exact hQ r2 ext3 s4 m4 ⟨hext3, hpres3⟩ hsp4 ⟨hcl4, hpr4⟩
        (by rw [hcore3, hcore2] at hfl4; omega) hr2 hu2 ((fullM6HdrMem_iff ..).mpr hm4)
    · c0_call hVivTier
      refine m6aVivifyTierSpec_of hsp3 hm3
        fun r2 s4 m4 hsp4 _ _ hnz2 hfl4 hr2 hu2 hm4 => ?_
      obtain ⟨hcl4, hpr4⟩ := hnz2 hbud
      fvt_steps
      · exact hQ 20#64 ext3 s4 m4 ⟨hext3, hpres3⟩ hsp4 ⟨hcl4, hpr4⟩
          (by rw [hcore3, hcore2] at hfl4; omega) (Or.inr rfl) (fun _ => hu2 hc)
          ((fullM6HdrMem_iff ..).mpr hm4)
      · c0_call hVivTier
        refine m6aVivifyTierSpec_of hsp4 hm4
          fun r3 s5 m5 hsp5 _ _ hnz3 hfl5 hr3 hu3 hm5 => ?_
        obtain ⟨hcl5, hpr5⟩ := hnz3 hbud
        fvt_steps
        · exact hQ 20#64 ext3 s5 m5 ⟨hext3, hpres3⟩ hsp5 ⟨hcl5, hpr5⟩
            (by rw [hcore3, hcore2] at hfl4; have := Nat.le_trans hfl5 hfl4; omega)
            (Or.inr rfl) (fun _ => hu3 hc)
            ((fullM6HdrMem_iff ..).mpr hm5)
        · c0_call hVivTier
          refine m6aVivifyTierSpec_of hsp5 hm5
            fun r4 s6 m6 hsp6 _ _ hnz4 hfl6 hr4 hu4 hm6 => ?_
          obtain ⟨hcl6, hpr6⟩ := hnz4 hbud
          fvt_steps
          · exact hQ 20#64 ext3 s6 m6 ⟨hext3, hpres3⟩ hsp6 ⟨hcl6, hpr6⟩
              (by rw [hcore3, hcore2] at hfl4
                  have := Nat.le_trans hfl6 (Nat.le_trans hfl5 hfl4); omega)
              (Or.inr rfl) (fun _ => hu4 hc)
              ((fullM6HdrMem_iff ..).mpr hm6)
          · c0_call hVivTier
            refine m6aVivifyTierSpec_of hsp6 hm6
              fun r5 s7 m7 hsp7 _ _ hnz5 hfl7 hr5 hu5 hm7 => ?_
            obtain ⟨hcl7, hpr7⟩ := hnz5 hbud
            fvt_steps
            exact hQ r5 ext3 s7 m7 ⟨hext3, hpres3⟩ hsp7 ⟨hcl7, hpr7⟩
              (by rw [hcore3, hcore2] at hfl4
                  have := Nat.le_trans hfl7 (Nat.le_trans hfl6 (Nat.le_trans hfl5 hfl4)); omega)
              hr5 hu5 ((fullM6HdrMem_iff ..).mpr hm7)
  · fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1.lengths, hclv_lt, hmax_vars_pos,
        hw0.trail_lits_lt, hm, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJ () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at h0
      exact hJ () m ⟨s, hsp, hcl0, Nat.le_refl _, hm⟩

end LeanQbe.T.Examples.Kissat.FullM6OrchAdapters