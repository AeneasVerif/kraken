/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpRestore
public import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpReasons
public import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpFailedLit1
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Analyze
import LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.Rules
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Proof for `full_analyze_core_m6` (`Proof.Analyze.WpAnalyzeCore`)

Callee-parametric `Func.wp` proof for `Src.Analyze.full_analyze_core_m6_body` against
`Analyze.Spec.fullAnalyzeCoreM6Spec` (`= m6HdrAnalyzeSpec`), using only canonical sibling `Spec`
interfaces (`0` legacy imports, `0` `@[expose]` on theorems/sections, `<= 100` cols).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open scoped LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
open LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
open LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
open LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec

/-! ## 1. Local Framing, BitVec & Invariant Helpers -/

section AnalyzeCoreHelpers

private theorem ana_bv64_add_small_eq {x : BitVec 64} {k : Nat} (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h), Nat.mod_eq_of_lt h]

private theorem ana_bv64_add1_toNat {x lim : BitVec 64} (h : x.toNat < lim.toNat) :
    (x + 1#64).toNat = x.toNat + 1 :=
  ana_bv64_add_small_eq (by have := lim.isLt; omega)

private theorem ana_bv64_measure_sub_lt {iter lim : BitVec 64} (h : iter.toNat < lim.toNat) :
    lim.toNat - (iter + 1#64).toNat < lim.toNat - iter.toNat := by
  rw [ana_bv64_add1_toNat h]; omega

private theorem ana_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem ana_arenaVarsNodup_congr {s s' : FullState}
    (h : FullArenaVarsNodup s) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) : FullArenaVarsNodup s' := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
    fullArenaClauseGarbCore fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    fullArenaHdrCore
  rw [har, hal]; exact h

private theorem ana_otfsWitness_with_tmp_tl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k)
    (tmp' : List (BitVec 32)) (tl' : Nat) :
    FullOtfsWitnessInv c F0 F_cur { k with tmp := tmp', tmp_len := tl' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

private theorem ana_fullOtfsInvW_of_safetySlice {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : FullOtfsInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullOtfsInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.2.1
  · exact ana_arenaVarsNodup_congr h.2.2.2.1 (congrArg FullCoreState.arena heq)
      (congrArg FullCoreState.arena_len heq)
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs; rwa [heq]

private theorem ana_fullCutInvW_with_conflicts {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (h : FullCutInvW c F0 F_cur cut s) (k' : BitVec 64) :
    FullCutInvW c F0 F_cur cut { s with scratch := { s.scratch with conflicts := k' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with }⟩, h.2.1, h.2.2.1, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r), h.2.2.2.2.2⟩

private theorem ana_fullCutInvW_with_tmp_tl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (h : FullCutInvW c F0 F_cur cut s) (tmp' : List (BitVec 32)) (tl' : Nat)
    (htmp_len : tmp'.length = c.max_vars) (htl_le : tl' ≤ c.max_vars) :
    FullCutInvW c F0 F_cur cut
      { s with core := { s.core with tmp := tmp', tmp_len := tl' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htmp_len, tmp_len_le := htl_le }, h.1.scratch_ok⟩,
    ⟨ana_otfsWitness_with_tmp_tl h.2.1.toFullOtfsWitnessInv tmp' tl', h.2.1.cut_le,
      h.2.1.reason_inv_cut, h.2.1.reason_lit_mem_cut⟩,
    h.2.2.1, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r), h.2.2.2.2.2⟩

private theorem ana_fullCutInvW_of_restoreBump {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (h : FullCutInvW c F0 F_cur cut s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {repr' : List (BitVec 32)} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : FullMrkZero c
      { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }, scratch := sc' })
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }, scratch := sc' }) :
    FullCutInvW c F0 F_cur cut
      { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }, scratch := sc' } :=
  ⟨hlen',
    ⟨{ h.2.1.toFullOtfsWitnessInv with
        arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
        watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
      h.2.1.cut_le, h.2.1.reason_inv_cut, h.2.1.reason_lit_mem_cut⟩,
    ⟨hmrk0', h.2.2.1.2⟩,
    ana_arenaVarsNodup_congr h.2.2.2.1 rfl rfl,
    FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ r => r),
    h.2.2.2.2.2⟩

private theorem ana_fullOtfsInvW_of_reasons {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (h : FullOtfsInvW c F0 F_cur s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : FullMrkZero c
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' })
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    FullOtfsInvW c F0 F_cur
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' } :=
  ⟨hlen',
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    ⟨hmrk0', h.2.2.1.2⟩,
    ana_arenaVarsNodup_congr h.2.2.2.1 rfl rfl,
    FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ r => r),
    h.2.2.2.2.2⟩

private theorem ana_fullSparseInvW_of_bump_clear {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (h : FullSparseInvW c F0 F_cur s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {repr' : List (BitVec 32)} {sc' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' },
      scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hpres : FullExtScratchPres s
      { s with
        core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' },
        scratch := sc' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' },
        scratch := sc' } :=
  ⟨hlen',
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    ⟨hmrk0', h.2.2.1.2⟩,
    ana_arenaVarsNodup_congr h.2.2.2.1 rfl rfl,
    FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ r => r),
    h.2.2.2.2.2⟩

private def AnaCoreLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (iter_lim : BitVec 64)
    (st : BitVec 64 × FullState × List (BitVec 64)) (m' : Mem 64) : Prop :=
  ∃ cut', cut' ≤ st.2.1.core.trail_end ∧ FullCutInvW c F0 F_cur cut' st.2.1 ∧
    FullConflictOkCut F_cur cut' st.2.1 ∧ M6HdrExtOk st.2.2 ∧
    st.2.1.core.cur_vars = s.core.cur_vars ∧ st.2.1.core.fuel = s.core.fuel ∧
    st.2.1.core.cur_level ≤ s.core.cur_level ∧ st.2.1.scratch.work_stk2 = s.scratch.work_stk2 ∧
    st.1.toNat ≤ iter_lim.toNat ∧
    (FullMem c st.2.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) st.2.2 ⋆ R)) m'

private def AnaCoreShrinkPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (s' : FullState) : Prop :=
  FullOtfsInvW c F0 F_cur s' ∧ 0 < s'.core.cur_level ∧
  1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
  (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
  (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
  (∀ k, 1 ≤ k → k < s'.core.tmp_len →
    let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
    0 < lv ∧ lv < s'.core.cur_level) ∧
  (cnfOfClauses F_cur).EntailsClause
    (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp))) ∧
  s'.core.cur_vars = s.core.cur_vars ∧ s'.core.fuel = s.core.fuel ∧
  s'.core.cur_level ≤ s.core.cur_level ∧ s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  (s'.core.probing = 0#64 → s'.core.min_clr_len ≤ s'.core.cur_vars ∧
    ∀ k < s'.core.min_clr_len, (s'.scratch.work_stk1[k]?.getD 0#32).toNat < s'.core.cur_vars)

private def AnaCoreCutJoin (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut3 : Nat) (s : FullState) (s' : FullState) : Prop :=
  cut3 ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut3 s' ∧
  FullConflictOkCut F_cur cut3 s' ∧
  s'.core.cur_vars = s.core.cur_vars ∧ s'.core.fuel = s.core.fuel ∧
  s'.core.cur_level ≤ s.core.cur_level ∧ s'.scratch.work_stk2 = s.scratch.work_stk2

/-! ## 2. Small Pure Proof Helpers -/

private theorem ana_core_ema_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s5 s6 : FullState}
    (ho5 : FullOtfsInvW c F0 F_cur s5) (hpos5 : 0 < s5.core.cur_level)
    (htl5_ge : 1 ≤ s5.core.tmp_len) (htl5_le : s5.core.tmp_len ≤ s5.core.cur_vars)
    (hnd5 : (List.map (fun x => x.toNat / 2) (List.take s5.core.tmp_len s5.core.tmp)).Nodup)
    (hvals5 : ∀ k < s5.core.tmp_len, let l := (s5.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s5.core.cur_vars ∧ s5.core.vals[l]?.getD 0#8 = 255#8)
    (hlvl5 : ∀ k, 1 ≤ k → k < s5.core.tmp_len →
      let lv := (s5.core.lvl[(s5.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s5.core.cur_level)
    (hent5 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map BitVec.toNat (List.take s5.core.tmp_len s5.core.tmp))))
    (hcv5 : s5.core.cur_vars = s.core.cur_vars) (hfu5 : s5.core.fuel = s.core.fuel)
    (hcl5 : s5.core.cur_level ≤ s.core.cur_level)
    (hws5 : s5.scratch.work_stk2 = s.scratch.work_stk2)
    (hcov5 : s5.core.probing = 0#64 → s5.core.min_clr_len ≤ s5.core.cur_vars ∧
      ∀ k < s5.core.min_clr_len, (s5.scratch.work_stk1[k]?.getD 0#32).toNat < s5.core.cur_vars)
    (hcore6 : PreservesCoreSlice (fullSafetySlice c).coreProj s5 s6)
    (hlen6 : s6.LengthsOk c) (hpres6 : FullProbeScratchPres s5 s6) :
    AnaCoreShrinkPost c F0 F_cur s s6 := by
  have heq6 := fullCoreState_agrees_with_scratch hcore6
  refine ⟨ana_fullOtfsInvW_of_safetySlice ho5 hlen6 hcore6 hpres6.1,
    by change 0 < s6.core.cur_level; rw [heq6]; exact hpos5,
    by rw [heq6]; exact htl5_ge, by rw [heq6]; exact htl5_le,
    by rw [heq6]; exact hnd5, by rw [heq6]; exact hvals5,
    by rw [heq6]; exact hlvl5, by rw [heq6]; exact hent5,
    by rw [heq6]; exact hcv5, by rw [heq6]; exact hfu5,
    by change s6.core.cur_level ≤ _; rw [heq6]; exact hcl5,
    hpres6.2.2.1.trans hws5, fun hp => by
      have hcv_p := hcov5 (by rw [← heq6]; exact hp)
      rw [heq6, hpres6.2.1]; exact hcv_p⟩

private theorem ana_clear_lengthsOk {c : FullCfg} {s8 : FullState} {mrk9 : List (BitVec 8)}
    (hlen8 : s8.LengthsOk c) (hml9 : mrk9.length = c.max_vars) :
    ({ s8 with core := { s8.core with mrk := mrk9, min_clr_len := 0 } } :
      FullState).LengthsOk c :=
  ⟨{ hlen8.core_ok with mrk_len := hml9, min_clr_len_le := Nat.zero_le _ }, hlen8.scratch_ok⟩

private theorem ana_fullSparseInvW_with_conflicts {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (k : BitVec 64) :
    let s' : FullState := { s with scratch := { s.scratch with conflicts := k } }
    s'.LengthsOk c ∧ FullSparseInvW c F0 F_cur s' :=
  have hlen : ({ s with scratch := { s.scratch with conflicts := k } } : FullState).LengthsOk c :=
    ⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩
  ⟨hlen, hlen, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1,
    FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr), hsp.2.2.2.2.2⟩

private theorem ana_core_cut_tier_pres {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut3 : Nat} {s3 s3k s3t : FullState}
    (hcut3 : FullCutInvW c F0 F_cur cut3 s3k) (hcf3 : FullConflictOkCut F_cur cut3 s3)
    (hcore3k : s3k.core = s3.core) (hcore3t : s3t.core = s3k.core)
    (hlen3t : s3t.LengthsOk c) (hsc3t : M6HdrScratchPres s3k s3t) :
    FullCutInvW c F0 F_cur cut3 s3t ∧ FullConflictOkCut F_cur cut3 s3t := by
  have heq : s3t.core = s3.core := hcore3t.trans hcore3k
  refine ⟨⟨hlen3t, heq ▸ (hcore3k ▸ hcut3.2.1),
      by unfold FullLitMarksClear FullMrkZero; rw [heq, ← hcore3k]; exact hcut3.2.2.1,
      ana_arenaVarsNodup_congr hcut3.2.2.2.1 (congrArg FullCoreState.arena hcore3t)
        (congrArg FullCoreState.arena_len hcore3t),
      FullExtScratchOk.of_pres hcut3.2.2.2.2.1 hsc3t.extPres
        (fun r hr => by unfold fullArenaClauseRefs; rwa [hcore3t]),
      heq ▸ (hcore3k ▸ hcut3.2.2.2.2.2)⟩, ?_⟩
  unfold FullConflictOkCut FullConflictOkW fullArenaClauseRefs fullArenaClauseGarb
    fullArenaClauseLits fullArenaClauseRefsCore fullArenaClauseGarbCore
    fullArenaHdrCore fullArenaClauseLitsCore fullArenaClauseSizeCore at hcf3 ⊢
  rwa [heq]

private theorem ana_core_learn_ret {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s6 s7 s9 : FullState} {ext9 : List (BitVec 64)} {r : BitVec 64}
    {R : Mem 64 → Prop} {m9 : Mem 64} {Q : Post [i64]}
    (hinv : FullM6HdrCfgOk c) (hdm0 : s.core.dense_mode = 0#64)
    (hcv6 : s6.core.cur_vars = s.core.cur_vars) (hfu6 : s6.core.fuel = s.core.fuel)
    (hcl6 : s6.core.cur_level ≤ s.core.cur_level)
    (hws6 : s6.scratch.work_stk2 = s.scratch.work_stk2)
    (hr : r = 0#64 ∨ r = 1#64 ∨ r = 20#64)
    (hcv7 : s7.core.cur_vars = s6.core.cur_vars) (hfu7 : s7.core.fuel.toNat ≤ s6.core.fuel.toNat)
    (hws27 : s7.scratch.work_stk2 = s6.scratch.work_stk2)
    (h20_7 : r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s7 ∧
      s7.core.cur_level < s6.core.cur_level)
    (h1_7 : r = 1#64 → FullSparseInvW c F0 F_cur s7 ∧ s7.core.cur_level < s6.core.cur_level)
    (hext9 : M6HdrExtOk ext9) (hsp9 : FullSparseInvW c F0 F_cur s9)
    (hcv9 : s9.core.cur_vars = s7.core.cur_vars) (hfu9 : s9.core.fuel = s7.core.fuel)
    (hcl9 : s9.core.cur_level = s7.core.cur_level) (hdm9 : s9.core.dense_mode = s7.core.dense_mode)
    (hws29 : s9.scratch.work_stk2 = s7.scratch.work_stk2)
    (hm9 : (FullM6HdrMem c ext9 s9 ⋆ R) m9)
    (hQ : ∀ r ext' s' m', M6HdrExtOk ext' → s'.LengthsOk c →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s'.scratch.work_stk2 = s.scratch.work_stk2 ∧ (r = 20#64 → FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode)) →
      (r = 20#64 → F0.Unsat) → (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    Q (r, ()) m9 :=
  hQ r ext9 s9 m9 hext9 hsp9.1 hr (hcv9.trans (hcv7.trans hcv6))
    (Nat.le_trans (by rw [hfu9]; exact Nat.le_refl _)
      (Nat.le_trans hfu7 (by rw [hfu6]; exact Nat.le_refl _)))
    ⟨hws29.trans (hws27.trans hws6), fun h =>
      let ⟨_, hsp, hcl⟩ := h20_7 h
      ⟨hsp9.toOtfs, Nat.le_trans (by rw [hcl9]; exact Nat.le_of_lt hcl) hcl6,
        hdm9.trans (hsp.2.2.2.2.2.trans hdm0.symm)⟩⟩
    (fun h => (h20_7 h).1) (fun _ => hsp9.toOtfs)
    (fun h => ⟨FullM6HdrInvW.mk_inv hinv hext9 hsp9,
      Nat.lt_of_lt_of_le (by rw [hcl9]; exact (h1_7 h).2) hcl6⟩) hm9

private theorem ana_core_min_shrink_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s3 s4 : FullState}
    (ho3 : FullOtfsInvW c F0 F_cur s3)
    (htl_ge : 1 ≤ s3.core.tmp_len)
    (hvals3 : ∀ k < s3.core.tmp_len, let l := (s3.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s3.core.cur_vars ∧ s3.core.vals[l]?.getD 0#8 = 255#8)
    (hcv4 : s4.core.cur_vars = s3.core.cur_vars)
    (hval4 : s4.core.vals = s3.core.vals)
    (har4 : s4.core.arena = s3.core.arena)
    (hal4 : s4.core.arena_len = s3.core.arena_len)
    (hdm4 : s4.core.dense_mode = s3.core.dense_mode)
    (hpres4 : FullExtScratchPres s3 s4)
    (hlen4 : s4.LengthsOk c)
    (ho4 : FullOtfsWitnessInv c F0 F_cur s4.core)
    (hmc4 : FullLitMarksClear c s4)
    (htmp04 : s4.core.tmp[0]? = s3.core.tmp[0]?)
    (h4lits : ∀ j, 1 ≤ j → j < s4.core.tmp_len →
      let l := (s4.core.tmp[j]?.getD 0#32).toNat
      let lv := (s3.core.lvl[l / 2]?.getD 0#32).toNat
      l < 2 * s3.core.cur_vars ∧ s3.core.vals[l]?.getD 0#8 = 255#8 ∧
      0 < lv ∧ lv < s3.core.cur_level) :
    FullOtfsInvW c F0 F_cur s4 ∧
    ∀ k < s4.core.tmp_len, let l := (s4.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s4.core.cur_vars ∧ s4.core.vals[l]?.getD 0#8 = 255#8 := by
  refine ⟨⟨hlen4, ho4, hmc4, ana_arenaVarsNodup_congr ho3.2.2.2.1 har4 hal4,
    FullExtScratchOk.of_pres ho3.2.2.2.2.1 hpres4 (fun _ hr => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rwa [har4, hal4]),
    hdm4.trans ho3.2.2.2.2.2⟩, ?_⟩
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simpa [hcv4, hval4, htmp04] using hvals3 0 (Nat.lt_of_lt_of_le Nat.zero_lt_one htl_ge)
  · rw [hcv4, hval4]
    exact ⟨(h4lits k (Nat.pos_of_ne_zero hk0) hk).1,
      (h4lits k (Nat.pos_of_ne_zero hk0) hk).2.1⟩

private theorem ana_core_post_tick_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s3 s4 s5 s6 : FullState}
    {tl_le : s3.core.tmp_len ≤ s3.core.cur_vars} {tl4 : Nat}
    {htl4_ge : 1 ≤ tl4} {htl4_le : tl4 ≤ s3.core.tmp_len}
    {hpos3 : 0 < s3.core.cur_level} {hlle2 : s3.core.cur_level ≤ s.core.cur_level}
    {hcv3 : s3.core.cur_vars = s.core.cur_vars} {hfu3 : s3.core.fuel = s.core.fuel}
    {hws3 : s3.scratch.work_stk2 = s.scratch.work_stk2}
    {ho5 : FullOtfsInvW c F0 F_cur s5}
    {hcore6 : PreservesCoreSlice (fullSafetySlice c).coreProj s5 s6}
    {hlen6 : s6.LengthsOk c} {hpres6 : FullProbeScratchPres s5 s6}
    {htmp5 : s5.core.tmp = s4.core.tmp} {htl5 : s5.core.tmp_len = s4.core.tmp_len}
    {hcv5s : s5.core.cur_vars = s4.core.cur_vars} {hfu5s : s5.core.fuel = s4.core.fuel}
    {hcl5s : s5.core.cur_level = s4.core.cur_level} {hval5 : s5.core.vals = s4.core.vals}
    {hlvl5s : s5.core.lvl = s4.core.lvl}
    {hmcl5 : s5.core.min_clr_len ≤ s5.core.cur_vars ∧
      ∀ k < s5.core.min_clr_len, (s5.scratch.work_stk1[k]?.getD 0#32).toNat < s5.core.cur_vars}
    {hws5 : s5.scratch.work_stk2 = s4.scratch.work_stk2}
    {htl4s : s4.core.tmp_len = tl4}
    {hcv4s : s4.core.cur_vars = s3.core.cur_vars} {hfu4s : s4.core.fuel = s3.core.fuel}
    {hcl4s : s4.core.cur_level = s3.core.cur_level}
    {hlvl4s : s4.core.lvl = s3.core.lvl} {hws4s : s4.scratch.work_stk2 = s3.scratch.work_stk2}
    {htmp4s : s4.core.tmp = s4.core.tmp}
    (hnd4 : ((s4.core.tmp.take tl4).map fun x => x.toNat / 2).Nodup)
    (h4v : ∀ k < tl4, let l := (s4.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s4.core.cur_vars ∧ s4.core.vals[l]?.getD 0#8 = 255#8)
    (h4lits : ∀ j, 1 ≤ j → j < tl4 →
      let l := (s4.core.tmp[j]?.getD 0#32).toNat
      let lv := (s3.core.lvl[l / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s3.core.cur_level)
    (hent4 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s4.core.tmp.take tl4).map BitVec.toNat))) :
    AnaCoreShrinkPost c F0 F_cur s s6 := by
  have heq6 := fullCoreState_agrees_with_scratch hcore6
  have _ := htmp4s; have _ := tl_le
  refine ⟨ana_fullOtfsInvW_of_safetySlice ho5 hlen6 hcore6 hpres6.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < s6.core.cur_level; rw [heq6, hcl5s, hcl4s]; exact hpos3
  · rw [heq6, htl5, htl4s]; exact htl4_ge
  · rw [heq6, htl5, htl4s, hcv5s, hcv4s]; exact Nat.le_trans htl4_le tl_le
  · rw [heq6, htmp5, htl5, htl4s]; exact hnd4
  · intro k hk
    rw [heq6, htl5, htl4s] at hk; rw [heq6, htmp5, hcv5s, hval5]; exact h4v k hk
  · intro k hk1 hk2
    rw [heq6, htl5, htl4s] at hk2; rw [heq6, htmp5, hlvl5s, hcl5s, hlvl4s, hcl4s]
    exact h4lits k hk1 hk2
  · rw [heq6, htmp5, htl5, htl4s]; exact hent4
  · change s6.core.cur_vars = _; rw [heq6, hcv5s, hcv4s]; exact hcv3
  · change s6.core.fuel = _; rw [heq6, hfu5s, hfu4s]; exact hfu3
  · change s6.core.cur_level ≤ _; rw [heq6, hcl5s, hcl4s]; exact hlle2
  · exact hpres6.2.2.1.trans (hws5.trans (hws4s.trans hws3))
  · intro _; rw [heq6, hpres6.2.1]; exact hmcl5

/-! ## 3. Main WP Proof (`full_analyze_core_m6_wp`) -/

private theorem ana_minShrinkMask_fields {s3 s4 : FullState}
    (hframe : AgreesExcept Minimize.Spec.minShrinkMask s3 s4) :
    s4.core.cur_vars = s3.core.cur_vars ∧ s4.core.fuel = s3.core.fuel ∧
    s4.core.cur_level = s3.core.cur_level ∧ s4.core.vals = s3.core.vals ∧
    s4.core.lvl = s3.core.lvl ∧ s4.core.dense_mode = s3.core.dense_mode ∧
    s4.core.arena = s3.core.arena ∧ s4.core.arena_len = s3.core.arena_len ∧
    s4.scratch.work_stk2 = s3.scratch.work_stk2 ∧ FullExtScratchPres s3 s4 := by
  dsimp only [AgreesExcept, Minimize.Spec.minShrinkMask] at hframe
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · have h := congrArg (fun st => st.core.cur_vars) hframe; exact h
  · have h := congrArg (fun st => st.core.fuel) hframe; exact h
  · have h := congrArg (fun st => st.core.cur_level) hframe; exact h
  · have h := congrArg (fun st => st.core.vals) hframe; exact h
  · have h := congrArg (fun st => st.core.lvl) hframe; exact h
  · have h := congrArg (fun st => st.core.dense_mode) hframe; exact h
  · have h := congrArg (fun st => st.core.arena) hframe; exact h
  · have h := congrArg (fun st => st.core.arena_len) hframe; exact h
  · have h := congrArg (fun st => st.scratch.work_stk2) hframe; exact h
  · have h := congrArg (fun st => st.scratch.last_learned) hframe; exact h
  · have h := congrArg (fun st => st.scratch.extend_len) hframe; exact h

/-- Parametric `Func.wp` proof for `Src.Analyze.full_analyze_core_m6_body` against
`Analyze.Spec.analyzeSpec`. -/
theorem full_analyze_core_m6_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, Learn.Spec.oneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, anaFailedLitSpec a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, Deduce.Spec.fullDeduce1uipM6HdrSpec a m Q X →
      Γ "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X)
    (hUpdTier : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_update_tier_limits" [i64] [] a m Q X)
    (hRestore : ∀ a m Q X, restoreBumpAnaModeSpec a m Q X →
      Γ "full_restore_bump_ana_mode_fid" [i64, .bool] [] a m Q X)
    (hMinShrink : ∀ a m Q X, Minimize.Spec.minShrinkSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hReasons : ∀ a m Q X, analyzeReasonsSpec a m Q X →
      Γ "full_analyze_reasons_fid" [i64] [] a m Q X)
    (hTick : ∀ a m Q X, fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnM6 : ∀ a m Q X, Learn.Spec.learnClauseSpec a m Q X →
      Γ "full_learn_clause_m6" [i64, i64] [i64] a m Q X)
    (hBumpMode : ∀ a m Q X, fullBumpAnalyzedModeSpec a m Q X →
      Γ "full_bump_analyzed_mode_fid" [i64, .bool] [] a m Q X)
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X) :
    ∀ a m Q X, analyzeSpec a m Q X →
      Func.wp Γ Src.Analyze.full_analyze_core_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, ⟨F0, F_cur⟩, R, rfl, hcfg, hext, _, ⟨hsp, hcf⟩, hm, hQ0⟩ :=
    M6HdrContract.elim hs
  have hinv : FullM6HdrInvW c F0 F_cur ext s := FullM6HdrInvW.mk_inv hcfg hext hsp
  let hQ : ∀ (r : BitVec 64) ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
        (r = 20#64 → FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode)) →
      (r = 20#64 → F0.Unsat) → (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' :=
    fun r ext' s' m' hext' hlen' hr hcv' hfu' ⟨hws2', h20'⟩ h20u h0' h1' hm' =>
      hQ0 (r, ()) ext' s' m' hext' trivial hlen' ⟨hr, hcv', hfu', hws2',
        fun eq20 => let ⟨ho, hcl, hdm⟩ := h20' eq20; ⟨h20u eq20, ho, hcl, hdm⟩,
        h0', fun eq1 => let ⟨hinv', hcl'⟩ := h1' eq1; ⟨hinv'.sparseW, hcl'⟩⟩ hm'
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have hcv_le := hinv.sparseW.1.core_ok.cur_vars_le
  let iter_lim : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars + 64#64
  have hil_val : iter_lim.toNat = s.core.cur_vars + 64 := by
    dsimp only [iter_lim]
    rw [ana_bv64_add_small_eq (k := 64) (by simp; omega)]; simp; omega
  unfold Func.wp Src.Analyze.full_analyze_core_m6_body; dsimp only
  refine wp_m6Hdr_focus_frame hm fun hm' => ?_; c0_hsteps_nogrp
  refine wp_while_state1 (α := BitVec 64 × FullState × List (BitVec 64)) (fun st => st.1)
    (fun st => iter_lim.toNat - st.1.toNat) (AnaCoreLoopInv c F0 F_cur s R iter_lim) ?_ ?_
  · intro J hJ; refine hJ (0#64, s, ext) m ⟨s.core.trail_end, Nat.le_refl _, hinv.sparseW.toCut,
      hcf.toCut hinv.sparseW.2.1, hinv.extOk, rfl, rfl, Nat.le_refl _, rfl, by simp, hm'⟩
  · intro J ⟨iter, s1, ext1⟩ m1
      ⟨cut1, hcut1_le, hcut1, hcf1, hext1, hcv1, hfu1, hcl1, hws1, hil1, hm1⟩ ih
    dsimp only at hcut1_le hcut1 hcf1 hext1 hcv1 hfu1 hcl1 hws1 hil1 hm1 ⊢
    c0_hsteps_nogrp
    · have hlt : iter.toNat < iter_lim.toNat := by
        simpa [iter_lim, BitVec.toNat_add, BitVec.toNat_ofNat] using hc
      have hcv_fit : (BitVec.ofNat 64 s1.core.cur_vars + 64#64).toNat = s1.core.cur_vars + 64 := by
        rw [hcv1]; exact hil_val
      c0_hsteps_nogrp; c0_call hOneLit
      dsimp only [Learn.Spec.oneLitConflSpec]
      refine FullContract.intro (w := (F0, F_cur, cut1)) hcut1.1 ⟨hcut1, hcf1⟩ hm1 ?_
      rintro ⟨ol, ⟨⟩⟩ s2 m2 hlen2 ⟨hol, hcv2, hfu2, hws2, h20, h1, h2, h0⟩ hm2
      have hm2' := fullM6HdrMem_unfocus hm2
      rcases hol with rfl | rfl | rfl | rfl
      · rcases h0 rfl with ⟨cut2, hcut2_le, hcut2, hlvl2, hlle2, hcf2⟩
        c0_hsteps_nogrp
        · c0_call hFailed
          dsimp only [anaFailedLitSpec]
          refine M6HdrContract.intro (w := (F0, F_cur, cut2)) hinv.cfgOk hext1 hcut2.1
            ⟨hcut2, hlvl2, hcf2⟩ hm2' ?_
          rintro ⟨r, ⟨⟩⟩ ext3 s3 m3 hext3 _ hlen3 ⟨hr, hcv3, hfu3, hws3, hr20, hr0, hr1⟩ hm3
          exact hQ r ext3 s3 m3 hext3 hlen3 hr (hcv3.trans (hcv2.trans hcv1))
            (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _) ⟨hws3.trans (hws2.trans hws1),
              fun heq => by
                have ⟨_, ho, hcl, _⟩ := hr20 heq
                exact ⟨ho, Nat.le_trans hcl (Nat.le_trans hlle2 hcl1),
                  ho.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
            (fun heq => (hr20 heq).1) hr0
            (fun heq => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext3 (hr1 heq).1,
              Nat.lt_of_lt_of_le (hr1 heq).2 (Nat.le_trans hlle2 hcl1)⟩) hm3
        · c0_call hDeduce
          refine ⟨c, F0, F_cur, cut2, ext1, s2, R, rfl, hinv.cfgOk, hext1, hcut2, hlvl2, hcf2,
            hm2', ?_⟩
          intro dst ext3 s3 m3 hext3 hlen3 hdst hcv3 hfu3 hws3 hr20 hr0 hr1 hr2 hm3
          rcases hdst with rfl | rfl | rfl | rfl
          · c0_hsteps_nogrp
            exact hQ 0#64 ext3 s3 m3 hext3 hlen3 (Or.inl rfl) (hcv3.trans (hcv2.trans hcv1))
              (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _) ⟨hws3.trans (hws2.trans hws1),
                fun h => by cases h⟩
              (fun h => by cases h) hr0 (fun h => by cases h) hm3
          · rcases hr1 rfl with ⟨ho3, hcl3, htl_ge, htl_le, hnd3, hvals3, hlvl3, _hlvl0, hent3⟩
            refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_; c0_hsteps_nogrp; c0_call hMinShrink
            dsimp only [Minimize.Spec.minShrinkSpec]
            refine FullContract.intro (w := (F0, F_cur)) hlen3
              ⟨ho3.2.1, ho3.2.2.1, htl_ge, htl_le, hnd3, hent3, hvals3, hlvl3, _hlvl0⟩ hm3f ?_
            rintro ⟨⟩ s4 m4 hlen4
              ⟨hframe4, ho4, hmc4, htl4_ge, htl4_le, htmp04, hnd4, h4lits, hent4⟩ hm4
            obtain ⟨hcv4, hfu4, hcl4, hval4, hlvl4, hdm4, har4, hal4, hws24, hpres4⟩ :=
              ana_minShrinkMask_fields hframe4
            obtain ⟨hotfs4, h4v⟩ := ana_core_min_shrink_ok ho3 htl_ge hvals3 hcv4 hval4 har4 hal4
              hdm4 hpres4 hlen4 ho4 hmc4 htmp04 h4lits
            have hm4' := fullM6HdrMem_unfocus hm4
            c0_hsteps_nogrp
            refine wp_join_state0 (α := FullState × List (BitVec 64))
              (fun st m' => AnaCoreShrinkPost c F0 F_cur s st.1 ∧ M6HdrExtOk st.2 ∧
                (FullM6HdrMem c st.2 st.1 ⋆ R) m') ?_ ?_
            · rintro J4 ⟨s5, ext5⟩ m5 ⟨⟨ho5, hpos5, htl5_ge, htl5_le, hnd5, hvals5, hlvl5,
                hent5, hcv5, hfu5, hcl5, hws5, hcov5⟩, hext5, hm5⟩
              dsimp only at *
              refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
              have htl5_arr := ho5.1.core_ok.tmp_len_arr; have hcv5_le := ho5.1.core_ok.cur_vars_le
              have htl5_fit : s5.core.tmp_len < 2 ^ 64 := by omega
              c0_hsteps_nogrp
              refine wp_while_state_pure (α := BitVec 64 × BitVec 64 × BitVec 32)
                (fun st => (st.2.1, st.2.2, st.1, ()))
                (fun st => s5.core.tmp_len - st.1.toNat)
                (fun st => 1 ≤ st.1.toNat ∧ st.1.toNat ≤ s5.core.tmp_len) ?_ ?_
              · intro J5 hJ5; exact hJ5 (1#64, 0#64, 0#32) ⟨by decide, htl5_ge⟩
              · intro J5 ⟨gi, glue, llvl⟩ ⟨hgi_lo, hgi_hi⟩ ih5
                dsimp only at hgi_lo hgi_hi ⊢; c0_hsteps_nogrp
                · have hgi_lt : gi.toNat < s5.core.tmp_len := by
                    simpa [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl5_fit] using hc
                  have hlt_arr : gi.toNat < s5.core.tmp.length := by rw [htl5_arr]; omega
                  have hl_lt : (s5.core.tmp[gi.toNat]'hlt_arr).toNat < 2 * s5.core.cur_vars := by
                    simpa [List.getElem?_eq_getElem hlt_arr] using (hvals5 gi.toNat hgi_lt).1
                  have hv_lt : (BitVec.setWidth 64
                      ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32)).toNat <
                      s5.core.lvl.length := by
                    rw [ho5.1.core_ok.lvl_len, BitVec.toNat_setWidth, ana_bv32_lshr1,
                      Nat.mod_eq_of_lt
                        (by omega : (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 < 2 ^ 64)]
                    exact Nat.lt_of_lt_of_le (by omega) hcv5_le
                  have hgi_add1 : (gi + 1#64).toNat = gi.toNat + 1 :=
                    ana_bv64_add_small_eq (k := 1) (by omega)
                  c0_hsteps
                  · exact ih5 (gi + 1#64, glue + 1#64, s5.core.lvl[(BitVec.setWidth 64
                        ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32)).toNat]'hv_lt)
                      (by dsimp only; rw [hgi_add1]; omega)
                      ⟨by dsimp only; rw [hgi_add1]; omega, by dsimp only; rw [hgi_add1]; omega⟩
                  · exact ih5 (gi + 1#64, glue, llvl) (by dsimp only; rw [hgi_add1]; omega)
                      ⟨by dsimp only; rw [hgi_add1]; omega, by dsimp only; rw [hgi_add1]; omega⟩
                · refine wp_join_state0 (α := FullState)
                    (fun s6 m' => AnaCoreShrinkPost c F0 F_cur s s6 ∧
                      (FullMem c s6 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R)) m') ?_ ?_
                  · rintro J6 s6 m6 ⟨⟨ho6, hpos6, htl6_ge, htl6_le, hnd6, hvals6, hlvl6,
                      hent6, hcv6, hfu6, hcl6, hws6, hcov6⟩, hm6⟩
                    c0_hsteps_nogrp; c0_call hLearnM6
                    dsimp only [Learn.Spec.learnClauseSpec]
                    refine M6HdrContract.intro (w := (F0, F_cur)) hinv.cfgOk hext5 ho6.1
                      ⟨ho6, hpos6, ⟨htl6_ge, htl6_le⟩, hnd6, hvals6, hlvl6, hent6⟩
                      (fullM6HdrMem_unfocus hm6) ?_
                    rintro ⟨r, ⟨⟩⟩ ext7 s7 m7 hext7 _ hlen7
                      ⟨hr, hcv7, hfu7, hpr7, hmcl7, hws17, hws27, h20_7, h0_7, h1_7⟩ hm7
                    have hsp7 : FullSparseInvW c F0 F_cur s7 := by
                      rcases hr with rfl | rfl | rfl
                      · exact h0_7 rfl
                      · exact (h1_7 rfl).1
                      · exact (h20_7 rfl).2.1
                    refine wp_join_group (ts := []) (fun _ mf =>
                        ∃ (extf : List (BitVec 64)) (sf : FullState), M6HdrExtOk extf ∧
                          FullSparseInvW c F0 F_cur sf ∧
                          sf.core.cur_vars = s7.core.cur_vars ∧ sf.core.fuel = s7.core.fuel ∧
                          sf.core.cur_level = s7.core.cur_level ∧
                          sf.core.dense_mode = s7.core.dense_mode ∧
                          sf.scratch.work_stk2 = s7.scratch.work_stk2 ∧
                          (FullM6HdrMem c extf sf ⋆ R) mf)
                      (fun _ ⟨⟩ mf ⟨extf, sf, hextf, hspf, hcvf, hfuf, hclf, hdmf, hws2f, hmf⟩ =>
                        by rw [Blocks.get_here]; c0_hsteps
                           exact ana_core_learn_ret hinv.cfgOk hinv.sparseW.2.2.2.2.2
                             hcv6 hfu6 hcl6 hws6 hr hcv7 hfu7 hws27 h20_7 h1_7 hextf hspf
                             hcvf hfuf hclf hdmf hws2f hmf hQ) ?_
                    rintro Jend hJend
                    refine wp_m6Hdr_focus_frame hm7 fun hm7f => ?_; c0_hsteps_nogrp
                    · have hpr0 : s7.core.probing = 0#64 := by assumption
                      have hcov7 : s7.core.min_clr_len ≤ s7.core.cur_vars ∧
                          ∀ k < s7.core.min_clr_len,
                            (s7.scratch.work_stk1[k]?.getD 0#32).toNat < s7.core.cur_vars := by
                        obtain ⟨h1, h2⟩ := hcov6 (by rw [← hpr7]; exact hpr0)
                        rw [← hcv7] at h1; refine ⟨by omega, fun k hk => ?_⟩
                        rw [hcv7, hws17]; exact h2 k (by omega)
                      refine wp_join_group (ts := []) (fun _ m8 =>
                          ∃ (ext8 : List (BitVec 64)) (s8 : FullState), M6HdrExtOk ext8 ∧
                            FullSparseInvW c F0 F_cur s8 ∧ s8.core.cur_vars = s7.core.cur_vars ∧
                            s8.core.fuel = s7.core.fuel ∧ s8.core.cur_level = s7.core.cur_level ∧
                            s8.core.dense_mode = s7.core.dense_mode ∧
                            s8.scratch.work_stk2 = s7.scratch.work_stk2 ∧
                            (∀ v < c.max_vars, s8.core.mrk[v]?.getD 0#8 = 0#8) ∧
                            (FullM6HdrMem c ext8 s8 ⋆ R) m8)
                        (fun _ ⟨⟩ m8 ⟨ext8, s8, hext8, hsp8, hcv8, hfu8, hcl8, hdm8, hws28,
                            hmz8, hm8⟩ => by
                          rw [Blocks.get_here]
                          refine wp_m6Hdr_focus_frame hm8 fun hm8f => ?_; c0_hcall hClear
                          refine ⟨c, s8, m6ExtMem (m6ExtAddr c.hdr) ext8 ⋆ R, rfl, hsp8.1, hm8f,
                            fun mrk9 m9 hml9 hm09 _ _ hm9 => ?_⟩
                          let s9 : FullState :=
                            { s8 with core := { s8.core with mrk := mrk9, min_clr_len := 0 } }
                          have hlen9 := ana_clear_lengthsOk hsp8.1 hml9
                          have hmz9 : ∀ v < c.max_vars, mrk9[v]?.getD 0#8 = 0#8 :=
                            fun v hv => hm09 v hv (hmz8 v hv)
                          have hsp9 := ana_fullSparseInvW_of_bump_clear hsp8
                            (repr' := s8.core.repr) (sc' := s8.scratch) hlen9 hmz9 ⟨rfl, rfl⟩
                          c0_hsteps
                          exact hJend () m9 ⟨ext8, s9, hext8, hsp9, hcv8, hfu8, hcl8, hdm8,
                            hws28, fullM6HdrMem_unfocus hm9⟩) ?_
                      rintro Jclr hJclr; c0_hsteps_nogrp
                      · c0_call hBumpMode
                        refine fullBumpAnalyzedModeSpec_of hinv.cfgOk hext7 hlen7
                          (fullBumpPre_false_of hcov7.1 hcov7.2) hm7 ?_
                        intro mrk8 mcl8 repr8 sc8 ext8 m8
                        dsimp only
                        intro hlen8 _ hfa _ hpres8 hws28 hext8 _ hm8
                        obtain ⟨hmrk8, _, _⟩ := hfa rfl
                        let s8 : FullState :=
                          { s7 with
                            core := { s7.core with mrk := mrk8, min_clr_len := mcl8,
                                                   repr := repr8 },
                            scratch := sc8 }
                        have hmz8 : ∀ v < c.max_vars, mrk8[v]?.getD 0#8 = 0#8 := by
                          rw [hmrk8]; exact hsp7.2.2.1.1
                        have hsp8 := ana_fullSparseInvW_of_bump_clear hsp7 hlen8 hmz8 hpres8
                        c0_hsteps
                        exact hJclr () m8
                          ⟨ext8, s8, hext8, hsp8, rfl, rfl, rfl, rfl, hws28, hmz8, hm8⟩
                      · exact hJclr () m7 ⟨ext7, s7, hext7, hsp7, rfl, rfl, rfl, rfl, rfl,
                          hsp7.2.2.1.1, hm7⟩
                    · exact hJend () m7 ⟨ext7, s7, hext7, hsp7, rfl, rfl, rfl, rfl, rfl, hm7⟩
                    · exact hJend () m7 ⟨ext7, s7, hext7, hsp7, rfl, rfl, rfl, rfl, rfl, hm7⟩
                  · intro J6 hJ6; c0_hsteps_nogrp
                    · c0_call hEma
                      refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl, ho5.1, hm5f, ?_⟩
                      rintro ⟨⟩ s6 m6 hcore6 hlen6 hpres6 hm6
                      exact hJ6 s6 m6 ⟨ana_core_ema_post ho5 hpos5 htl5_ge htl5_le hnd5 hvals5
                        hlvl5 hent5 hcv5 hfu5 hcl5 hws5 hcov5 hcore6 hlen6 hpres6, hm6⟩
                    · exact hJ6 s5 m5 ⟨⟨ho5, hpos5, htl5_ge, htl5_le, hnd5, hvals5, hlvl5,
                        hent5, hcv5, hfu5, hcl5, hws5, hcov5⟩, hm5f⟩
            · intro J4 hJ4; c0_hsteps_nogrp
              · have hp0 : s4.core.probing = 0#64 := by assumption
                c0_call hReasons
                dsimp only [analyzeReasonsSpec]
                refine M6HdrContract.intro (w := ()) hinv.cfgOk hext3 hlen4 hmc4.1 hm4' ?_
                rintro ⟨⟩ ext5 s5 m5 hext5 _ hlen5 ⟨hcore5, hmz5, hcv5, _, hpres5, hws5⟩ hm5
                have hs5_eq : s5 = {
                    core := { s4.core with mrk := s5.core.mrk, min_clr_len := s5.core.min_clr_len }
                    scratch := s5.scratch } := by
                  obtain ⟨c5, sc5⟩ := s5; exact congrArg (fun k => FullState.mk k sc5) hcore5
                have ho5 : FullOtfsInvW c F0 F_cur s5 :=
                  hs5_eq.symm ▸ ana_fullOtfsInvW_of_reasons hotfs4
                    (hs5_eq ▸ hlen5) (hs5_eq ▸ hmz5) (hs5_eq ▸ hpres5)
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_; c0_hsteps_nogrp; c0_call hTick
                refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl, hlen5, hm5f, ?_⟩
                rintro ⟨⟩ s6 m6 hcore6 hlen6 hpres6 hm6
                have hcov5 := hcv5 hp0
                exact hJ4 (s6, ext5) m6
                  ⟨ana_core_post_tick_ok (s4 := s4) (s5 := s5) (tl_le := htl_le)
                    (htl4_ge := htl4_ge)
                    (htl4_le := htl4_le) (hpos3 := by change 0 < s3.core.cur_level; omega)
                    (hlle2 := by rw [hcl3]; exact Nat.le_trans hlle2 hcl1)
                    (hcv3 := hcv3.trans (hcv2.trans hcv1))
                    (hfu3 := by rw [hfu3, hfu2, hfu1])
                    (hws3 := hws3.trans (hws2.trans hws1))
                    (ho5 := ho5) (hcore6 := hcore6)
                    (hlen6 := hlen6) (hpres6 := hpres6) (htmp5 := by rw [hcore5])
                    (htl5 := by rw [hcore5]) (hcv5s := by rw [hcore5])
                    (hfu5s := by rw [hcore5]) (hcl5s := by rw [hcore5])
                    (hval5 := by rw [hcore5]) (hlvl5s := by rw [hcore5])
                    (hmcl5 := by rw [hcore5]; exact hcov5)
                    (hws5 := hws5) (htl4s := rfl) (hcv4s := hcv4)
                    (hfu4s := hfu4) (hcl4s := hcl4) (hlvl4s := hlvl4) (hws4s := hws24)
                    (htmp4s := rfl) hnd4 h4v (fun k hk1 hk2 => (h4lits k hk1 hk2).2.2) hent4,
                  hext5, fullM6HdrMem_unfocus hm6⟩
              · have hpne : s4.core.probing ≠ 0#64 := by assumption
                exact hJ4 (s4, ext3) m4 ⟨⟨hotfs4, by change 0 < s4.core.cur_level; rw [hcl4]; omega,
                  htl4_ge, by rw [hcv4]; exact Nat.le_trans htl4_le htl_le, hnd4, h4v,
                  fun k hk1 hk2 => by rw [hlvl4, hcl4]; exact (h4lits k hk1 hk2).2.2,
                  hent4, hcv4.trans (hcv3.trans (hcv2.trans hcv1)),
                  by rw [hfu4, hfu3, hfu2, hfu1], by rw [hcl4, hcl3]; exact Nat.le_trans hlle2 hcl1,
                  hws24.trans (hws3.trans (hws2.trans hws1)),
                  fun hp => absurd hp hpne⟩, hext3, hm4'⟩
          · rcases hr2 rfl with ⟨cut3, hcut3_le, hcut3, hcl3, hcf3⟩
            refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_; c0_hsteps_nogrp
            refine wp_join_state0 (α := FullState × List (BitVec 64))
              (fun st m' => AnaCoreCutJoin c F0 F_cur cut3 s st.1 ∧ M6HdrExtOk st.2 ∧
                (FullM6HdrMem c st.2 st.1 ⋆ R) m') ?_ ?_
            · rintro J4 ⟨s5, ext5⟩ m5 ⟨⟨hcut5_le, hcut5, hcf5, hcv5, hfu5, hcl5, hws5⟩, hext5, hm5⟩
              dsimp only at hcut5_le hcut5 hcf5 hcv5 hfu5 hcl5 hws5 hext5 hm5 ⊢
              refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_; c0_hsteps_nogrp
              exact ih (iter + 1#64, s5, ext5) m5 (ana_bv64_measure_sub_lt hlt)
                ⟨cut3, hcut5_le, hcut5, hcf5, hext5, hcv5, hfu5, hcl5, hws5,
                 by rw [ana_bv64_add1_toNat hlt]; exact hlt, hm5f⟩
            · intro J4 hJ4; c0_hsteps_nogrp
              · c0_hfast_nogrp
                have hcut3k := ana_fullCutInvW_with_conflicts hcut3 (s3.scratch.conflicts + 1#64)
                c0_call hUpdTier
                refine m6HdrW2aSpec_of rfl hinv.cfgOk hext3 hcut3k.1
                  (fullM6HdrMem_unfocus (by assumption)) ?_
                intro ⟨⟩ ext3t s3t m3t hcore3t hlen3t hsc3t hext3t _ hm3t
                obtain ⟨hcut3t, hcf3t⟩ := ana_core_cut_tier_pres hcut3k hcf3 rfl hcore3t
                  hlen3t hsc3t
                have hcv3t : s3t.core.cur_vars = s3.core.cur_vars := by rw [hcore3t]
                have hfu3t : s3t.core.fuel = s3.core.fuel := by rw [hcore3t]
                have hcl3t : s3t.core.cur_level = s3.core.cur_level := by rw [hcore3t]
                have hte3t : s3t.core.trail_end = s3.core.trail_end := by rw [hcore3t]
                have hws3t : s3t.scratch.work_stk2 = s3.scratch.work_stk2 := hsc3t.ws2
                refine wp_m6Hdr_focus_frame hm3t fun hm3tf => ?_
                refine wp_join_state0 (α := FullState)
                  (fun st m' => AnaCoreCutJoin c F0 F_cur cut3 s st ∧
                    (FullMem c st ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3t ⋆ R)) m') ?_ ?_
                · rintro J5 s4 m4 ⟨⟨hcut4_le, hcut4, hcf4, hcv4, hfu4, hcl4, hws4⟩, hm4⟩
                  c0_hsteps_nogrp; c0_call hRestore
                  dsimp only [restoreBumpAnaModeSpec]
                  refine M6HdrContract.intro (w := ()) hinv.cfgOk hext3t hcut4.1 hcut4.2.2.1.1
                    (fullM6HdrMem_unfocus hm4) ?_
                  rintro ⟨⟩ ext5 s5 m5 hext5 _ hlen5 ⟨hcore5, hmz5, _, _, hpres5, hws5⟩ hm5
                  have hs5_eq : s5 = {
                      core := { s4.core with
                        mrk := s5.core.mrk, min_clr_len := s5.core.min_clr_len,
                        repr := s5.core.repr }
                      scratch := s5.scratch } := by
                    obtain ⟨c5, sc5⟩ := s5; exact congrArg (fun k => FullState.mk k sc5) hcore5
                  have hcut5 : FullCutInvW c F0 F_cur cut3 s5 :=
                    hs5_eq.symm ▸ ana_fullCutInvW_of_restoreBump hcut4
                      (hs5_eq ▸ hlen5) (hs5_eq ▸ hmz5) (hs5_eq ▸ hpres5)
                  exact hJ4 (s5, ext5) m5
                    ⟨⟨by rw [hcore5]; exact hcut4_le, hcut5,
                      by unfold FullConflictOkCut FullConflictOkW fullArenaClauseRefs
                           fullArenaClauseGarb fullArenaClauseLits fullArenaClauseRefsCore
                           fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLitsCore
                           fullArenaClauseSizeCore at hcf4 ⊢
                         rw [hcore5]; exact hcf4,
                      by rw [hcore5]; exact hcv4, by rw [hcore5]; exact hfu4,
                      by change s5.core.cur_level ≤ _; rw [hcore5]; exact hcl4,
                      hws5.trans hws4⟩, hext5, hm5⟩
                · intro J5 hJ5
                  have hJ_s3t : ∀ m',
                      (FullMem c s3t ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3t ⋆ R)) m' →
                      J5 () m' := fun m' hm' =>
                    hJ5 s3t m' ⟨⟨by rw [hte3t]; exact hcut3_le, hcut3t, hcf3t,
                      hcv3t.trans (hcv3.trans (hcv2.trans hcv1)),
                      by rw [hfu3t, hfu3, hfu2, hfu1],
                      by rw [hcl3t, hcl3]; exact Nat.le_trans hlle2 hcl1,
                      hws3t.trans (hws3.trans (hws2.trans hws1))⟩, hm'⟩
                  c0_hsteps_nogrp
                  · have hpos3 : 0 < s3t.core.cur_vars := by
                      have : s3t.core.cur_vars < 2 ^ 64 := by
                        have := hcut3t.1.core_ok.cur_vars_le; omega
                      simpa [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this] using hc
                    have htl0 : (0#64 : BitVec 64).toNat < s3t.core.tmp.length := by
                      rw [hcut3t.1.core_ok.tmp_len_arr]
                      exact Nat.lt_of_lt_of_le hpos3 (by
                        rw [hcv3t, hcv3, hcv2, hcv1]; exact hcv_le)
                    have hJ_tmp : ∀ {tp' : List (BitVec 32)} {m'} (htp' : tp'.length = c.max_vars),
                        (FullMem c { s3t with core := { s3t.core with
                          tmp := tp', tmp_len := (1#64 : BitVec 64).toNat } } ⋆
                          (m6ExtMem (m6ExtAddr c.hdr) ext3t ⋆ R)) m' → J5 () m' := by
                      intro tp' m' htp' hm'
                      have htw := ana_fullCutInvW_with_tmp_tl hcut3t tp' (1#64 : BitVec 64).toNat
                        htp' (by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega)
                      exact hJ5 _ m' ⟨⟨by rw [hte3t]; exact hcut3_le, htw, hcf3t,
                        hcv3t.trans (hcv3.trans (hcv2.trans hcv1)), by rw [hfu3t, hfu3, hfu2, hfu1],
                        by rw [hcl3t, hcl3]; exact Nat.le_trans hlle2 hcl1,
                        hws3t.trans (hws3.trans (hws2.trans hws1))⟩, hm'⟩
                    refine wp_unroll_group fun Jlit hJlit => ?_; c0_hsteps_nogrp
                    · exact hJ_tmp
                        (by simpa [List.length_set] using hcut3t.1.core_ok.tmp_len_arr) hm
                    · refine wp_unroll_group fun Js hJs => ?_
                      have har_len := hcut3t.1.core_ok.arena_len_arr
                      have har_le := hcut3t.1.core_ok.arena_len_le
                      c0_hfast_nogrp
                      · rename_i hlt_ar
                        have href_lt : s3t.core.confl_ref.toNat < s3t.core.arena_len := by
                          simpa [BitVec.lt_def, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by omega : s3t.core.arena_len < 2 ^ 64)] using hlt_ar
                        have hsub_lt : 3 < s3t.core.arena_len - s3t.core.confl_ref.toNat := by
                          have hc' : 3 < (2 ^ 64 - s3t.core.confl_ref.toNat +
                              s3t.core.arena_len) % 2 ^ 64 := hc
                          omega
                        have har_lt : (s3t.core.confl_ref + 3#64).toNat <
                            s3t.core.arena.length := by
                          rw [ana_bv64_add_small_eq (k := 3) (by omega)]; omega
                        c0_hfast_nogrp
                        exact hJ_tmp
                            (by simpa [List.length_set] using hcut3t.1.core_ok.tmp_len_arr) hm
                      · exact hJ_s3t _ (by assumption)
                      · exact hJ_s3t _ (by assumption)
                      · exact hJ_s3t _ (by assumption)
                  · exact hJ_s3t _ (by assumption)
              · exact hJ4 (s3, ext3) _ ⟨⟨hcut3_le, hcut3, hcf3,
                  hcv3.trans (hcv2.trans hcv1), by rw [hfu3, hfu2, hfu1],
                  by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                  hws3.trans (hws2.trans hws1)⟩, hext3, fullM6HdrMem_unfocus (by assumption)⟩
          · rcases hr20 rfl with ⟨hu3, ho3, hcl3, _⟩
            c0_hsteps
            rw [show (20 : BitVec 64) = 20#64 from rfl]
            exact hQ 20#64 ext3 s3 m3 hext3 hlen3 (Or.inr (Or.inr rfl))
              (hcv3.trans (hcv2.trans hcv1)) (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _)
              ⟨hws3.trans (hws2.trans hws1),
                fun _ => ⟨ho3, Nat.le_trans hcl3 (Nat.le_trans hlle2 hcl1),
                  ho3.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
              (fun _ => hu3) (fun h => by cases h) (fun h => by cases h) hm3
      · c0_hsteps_nogrp; c0_hfast
        · c0_hfast
          have h1s := h1 rfl
          let s2k : FullState :=
            { s2 with scratch := { s2.scratch with conflicts := s2.scratch.conflicts + 1 } }
          have h2k := ana_fullSparseInvW_with_conflicts h1s.1 (s2.scratch.conflicts + 1)
          rw [show (1 : BitVec 64) = 1#64 from rfl]
          exact hQ 1#64 ext1 s2k _ hext1 h2k.1 (Or.inr (Or.inl rfl)) (hcv2.trans hcv1)
            (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
            (fun h => by cases h) (fun h => by cases h)
            (fun _ => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext1 h2k.2,
              Nat.lt_of_lt_of_le h1s.2 hcl1⟩) (fullM6HdrMem_unfocus (by assumption))
        · c0_hfast
          rw [show (1 : BitVec 64) = 1#64 from rfl]
          exact hQ 1#64 ext1 s2 m2 hext1 hlen2 (Or.inr (Or.inl rfl)) (hcv2.trans hcv1)
            (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
            (fun h => by cases h) (fun h => by cases h)
            (fun _ => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext1 (h1 rfl).1,
              Nat.lt_of_lt_of_le (h1 rfl).2 hcl1⟩) hm2'
      · c0_hsteps_nogrp
        exact hQ 0#64 ext1 s2 m2 hext1 hlen2 (Or.inl rfl) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
          (fun h => by cases h) (fun _ => h2 rfl) (fun h => by cases h) hm2'
      · c0_hsteps_nogrp
        rw [show (20 : BitVec 64) = 20#64 from rfl]
        have ⟨hu2, ho2, hcl2, _⟩ := h20 rfl
        exact hQ 20#64 ext1 s2 m2 hext1 hlen2 (Or.inr (Or.inr rfl)) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1,
            fun _ => ⟨ho2, Nat.le_trans hcl2 hcl1,
              ho2.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
          (fun _ => hu2) (fun h => by cases h) (fun h => by cases h) hm2'
    · c0_hsteps_nogrp
      rw [show (0 : BitVec 64) = 0#64 from rfl]
      exact hQ 0#64 ext1 s1 m1 hext1 hcut1.1 (Or.inl rfl) hcv1
        (by rw [hfu1]; exact Nat.le_refl _)
        ⟨hws1, fun h => by cases h⟩ (fun h => by cases h)
        (fun _ => hcut1.toOtfs) (fun h => by cases h) (fullM6HdrMem_unfocus hm1)

end AnalyzeCoreHelpers

end LeanQbe.T.Examples.Kissat.Proof.Analyze
