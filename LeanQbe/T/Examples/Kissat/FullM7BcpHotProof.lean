/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 Hot-Path Fused BCP — Top-Level Wrapper, Closed `ModuleOk`, & UNSAT Non-Vacuity

Plain `public section` with unexposed proof internals.
Certifies:
1. `full_bcp_hot_wp` and canonical drop-in `m7PropFn_wp` against unmodified
   `FullPropDecSpecs.fullPropagateSpec`.
2. Closed `7`-row `m7BcpHotSpecTable`, `m7BcpHotEnv`, `m7BcpHotEnv_noExit`,
   `m7BcpHotSpecTable_nodup`, `m7BcpHot_tableImpl`, and `m7BcpHot_moduleOk`.
3. Concrete `Mem 64` UNSAT soundness & non-vacuity (`nv_m7_bcp_hot`, `XPost := False`)
   against `FastCore.nvFastPropMem` and `Full.nvOneLitF0.Unsat`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BcpHot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

local macro "m7_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

/-! ## 1. Canonical Entry Wrappers (`full_bcp_hot_wp` & `m7PropFn_wp`) -/

private theorem m7_prop_post_weaken {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]}
    (hQ : ∀ (r : BitVec 64) vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl'
      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort'
      phases' m',
      let s' : FullState :=
        { core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
              wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullPropDecSpecs.FullTrailExt s.core s'.core →
      FullPropDecSpecs.FullArenaPermEq s.core s'.core →
      (FullPropDecSpecs.FullArenaVarsNodup s → FullPropDecSpecs.FullArenaVarsNodup s') →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        FullPropDecSpecs.FullConflOkW F_cur s'.core ∧ (s'.core.cur_level = 0 → F0.Unsat)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    ∀ (r : BitVec 64) vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl'
      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort'
      phases' m',
      let s' : FullState :=
        { core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
              wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullPropDecSpecs.FullTrailExt s.core s'.core →
      FullPropDecSpecs.FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
        (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        FullPropDecSpecs.FullConflOkW F_cur s'.core ∧
        (ctype' = 2#64 → cref' ≠ 0xFFFFFFFF#64) ∧ (s'.core.cur_level = 0 → F0.Unsat)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' _s'
    hlen' hw' htr' hperm' hfl' hr hr0 hr1 hr2 hnoop hm'
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr' hperm' (fun h => hperm'.preserves_varsNodup h) hfl' hr
    (fun h0 => let ⟨hp, _, ho, hf⟩ := hr0 h0; ⟨hp, ho, hf⟩)
    (fun h1 => let ⟨hf, ho, hca, _, hu⟩ := hr1 h1; ⟨hf, ho, hca, hu⟩)
    hr2 hnoop hm'

theorem full_bcp_hot_wp (Γ : Env)
    (hPropIgn : ∀ args m Q X, FullPropDecSpecs.fullPropagateIgnoreSpec args m Q X →
      Γ "full_propagate_ignore_hot" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, FullPropDecSpecs.fullPropagateSpec args m Q X →
      Func.wp Γ full_bcp_hot_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0, hQ⟩
  unfold Func.wp full_bcp_hot_body
  m7_hsteps
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk'
      wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
      hlen' hw' htr' hperm' hfl' hr hr0 hr1 hr2 hnoop hm' => ?_⟩
  m7_hsteps
  exact m7_prop_post_weaken hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr' hperm' hfl' hr hr0 hr1 hr2 hnoop hm'

theorem m7PropFn_wp (Γ : Env)
    (hPropIgn : ∀ args m Q X, FullPropDecSpecs.fullPropagateIgnoreSpec args m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, FullPropDecSpecs.fullPropagateSpec args m Q X →
      Func.wp Γ m7PropFn.body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0, hQ⟩
  unfold Func.wp m7PropFn full_propagate_body
  m7_hsteps
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk'
      wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
      hlen' hw' htr' hperm' hfl' hr hr0 hr1 hr2 hnoop hm' => ?_⟩
  m7_hsteps
  exact m7_prop_post_weaken hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr' hperm' hfl' hr hr0 hr1 hr2 hnoop hm'

/-! ## 2. Closed `7`-Row `m7BcpHotEnv`, `TableImpl`, & `ModuleOk` -/

/-- Closed `7`-row specification table for `m7BcpHotModule` (`4` functions + `3` externs). -/
def m7BcpHotSpecTable : List SpecEntry :=
  [ ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool], fullPropLitOvfHotSpec, true⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool], fullPropChronoHotSpec, true⟩
  , ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_bcp_hot", [i64], [i64], FullPropDecSpecs.fullPropagateSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  ]

/-- Closed specification environment induced by `m7BcpHotSpecTable`. -/
def m7BcpHotEnv : Env := Env.ofTable m7BcpHotSpecTable

theorem m7BcpHotSpecTable_length : m7BcpHotSpecTable.length = 7 := by
  simp only [m7BcpHotSpecTable, List.length_cons, List.length_nil]

theorem m7BcpHotSpecTable_noExit : ∀ e ∈ m7BcpHotSpecTable, e.noExit = true := by
  intro e he
  simp only [m7BcpHotSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem m7BcpHotEnv_noExit :
    ∀ f as bs xs m Q X X',
      m7BcpHotEnv f as bs xs m Q X → m7BcpHotEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7BcpHotSpecTable_noExit

theorem m7BcpHotSpecTable_nodup : (m7BcpHotSpecTable.map SpecEntry.name).Nodup := by
  show (["full_prop_lit_ovf_hot", "full_prop_chrono_hot",
    "full_propagate_ignore_hot", "full_bcp_hot", "full_wstack_defrag",
    "full_unwatch_large", "full_watch_push"] : List String).Nodup
  decide

private theorem m7BcpHotEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m7BcpHotSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m7BcpHotEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m7BcpHotSpecTable_nodup (hno xs m Q X h)

private theorem m7_allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, m7_allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

/-- Row-by-row `TableImpl` for all `4` functions in `m7BcpHot_fns`. -/
theorem m7BcpHot_tableImpl :
    TableImpl m7BcpHotEnv m7BcpHot_fns m7BcpHotSpecTable := by
  let hOvf := m7BcpHotEnv_row_at 0
    ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool], fullPropLitOvfHotSpec, true⟩
  let hChrono := m7BcpHotEnv_row_at 1
    ⟨"full_prop_chrono_hot", [i64, i64], [.bool], fullPropChronoHotSpec, true⟩
  let hPropIgn := m7BcpHotEnv_row_at 2
    ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩
  let hDefrag := m7BcpHotEnv_row_at 4
    ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  let hUnw := m7BcpHotEnv_row_at 5
    ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩
  let hPush := m7BcpHotEnv_row_at 6
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  exact ⟨.of (full_prop_lit_ovf_hot_wp m7BcpHotEnv hPush),
    ⟨.of (full_prop_chrono_hot_wp m7BcpHotEnv hDefrag hUnw hPush),
    ⟨.of (full_propagate_ignore_hot_wp m7BcpHotEnv hOvf hChrono),
    ⟨.of (full_bcp_hot_wp m7BcpHotEnv hPropIgn), trivial⟩⟩⟩⟩

/-- Closed `ModuleOk` for `m7BcpHotModule` under `m7BcpHotEnv`. -/
theorem m7BcpHot_moduleOk : ModuleOk m7BcpHotEnv m7BcpHotModule :=
  Env.ofTable_moduleOk m7BcpHot_acyclic (m7_allFns_of_forall m7BcpHot_fns_wf)
    m7BcpHot_tableImpl

/-! ## 3. Concrete `Mem 64` UNSAT Soundness & Non-Vacuity (`XPost := False`) -/

/-- Concrete `Mem 64` binary-watch UNSAT soundness for `full_bcp_hot_body` under closed
`m7BcpHotEnv` (`XPost := fun _ _ _ _ => False`): exercises `nvFastPropMem` and derives
`Full.nvOneLitF0.Unsat` on conflict return (`r = 1#64`). -/
theorem nv_m7_bcp_hot :
    Func.wp m7BcpHotEnv full_bcp_hot_body (FastCore.nvFastPropCfg.hdr, ())
      FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  let hPropIgn := m7BcpHotEnv_row_at 2
    ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩
  apply full_bcp_hot_wp m7BcpHotEnv hPropIgn
  refine ⟨FastCore.nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], FastCore.nvFastPropState, emp,
    rfl, FastCore.nvFastProp_lengths, FastCore.nvFastProp_witness, rfl,
    by rw [sep_emp]; exact FastCore.nvFastPropMem_ok, ?_⟩
  intro r _vals' _flags' _lvl' _rsns' _trl' _tp' _te' _prop' _unas' _unfl'
    _wvec' _arena' _wstk' _wlen' _wu' _fuel' _ctype' _cref' _c0' _c1' _oom'
    _ticks' _wsort' _phases' m' s' _hlen' _hwf' _htr' _hperm' _hnd' _hfl' hr _hr0 hr1
    _hr2 _hnoop hm'
  exact ⟨hr, fun h1 => (hr1 h1).2.2.2 rfl, s', hm'⟩

end LeanQbe.T.Examples.Kissat.FullM7BcpHot
