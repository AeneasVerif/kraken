/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Logic.BitVec
public import LeanQbe.T.Module
public import LeanQbe.T.Logic.C0Agrees
public import Kraken.Mem
public import Kraken.Separation
meta import Lean.Elab.Command

/-!
# Kissat `M6` / `M7` Proof Simplification & Combinator Library (`Proof.Spec.Tactics`)

1. Opaque `FullState` / `FullScratch` / `M6Hdr` record-update abstraction.
2. `M6Hdr <-> FullHdr` bridge combinators.
3. Bounded loop-measure / fuel / `BitVec` kernel lemmas & `M6ProofUtilTactics` `c0_hfast` glue.
4. `ModuleOk` / `Env.noExit` composition combinators.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open Kraken.Bedrock2.Test

/-! ## 1. Opaque `FullState` / `FullScratch` / `M6Hdr` Record-Update Abstraction -/

theorem fullExtScratchPres_refl (s : FullState) : FullExtScratchPres s s :=
  ⟨rfl, rfl⟩

theorem fullExtScratchPres_trans {s1 s2 s3 : FullState}
    (h12 : FullExtScratchPres s1 s2) (h23 : FullExtScratchPres s2 s3) :
    FullExtScratchPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

theorem fullProbeScratchPres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fullProbeScratchPres_trans {s1 s2 s3 : FullState}
    (h12 : FullProbeScratchPres s1 s2) (h23 : FullProbeScratchPres s2 s3) :
    FullProbeScratchPres s1 s3 :=
  ⟨fullExtScratchPres_trans h12.1 h23.1,
    h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
    h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
    h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1, h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
    h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

/-- Chain scratch-step packages (`LengthsOk`, `core =`, `FullProbeScratchPres`, `delayed =`)
without unfolding `FullScratch` or `FullCoreState`. -/
theorem probeStep_trans {c : FullCfg} {s0 s1 s2 : FullState}
    (h1 : s1.LengthsOk c ∧ s1.core = s0.core ∧ FullProbeScratchPres s0 s1 ∧
      s1.scratch.delayed_len = s0.scratch.delayed_len ∧
      s1.scratch.delayed = s0.scratch.delayed)
    (h2 : s2.LengthsOk c ∧ s2.core = s1.core ∧ FullProbeScratchPres s1 s2 ∧
      s2.scratch.delayed_len = s1.scratch.delayed_len ∧
      s2.scratch.delayed = s1.scratch.delayed) :
    s2.LengthsOk c ∧ s2.core = s0.core ∧ FullProbeScratchPres s0 s2 ∧
      s2.scratch.delayed_len = s0.scratch.delayed_len ∧
      s2.scratch.delayed = s0.scratch.delayed :=
  ⟨h2.1, h2.2.1.trans h1.2.1, fullProbeScratchPres_trans h1.2.2.1 h2.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.trans h1.2.2.2.2⟩

private theorem fullArenaClauseRefs_of_core_eq {s s' : FullState} (hc : s'.core = s.core) :
    fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  simp [fullArenaClauseRefs, hc]

private theorem fullLitMarksClear_of_core_eq {c : FullCfg} {s s' : FullState}
    (hc : s'.core = s.core) (h : FullLitMarksClear c s) : FullLitMarksClear c s' := by
  unfold FullLitMarksClear FullMrkZero
  rw [hc]
  exact h

private theorem fullArenaVarsNodup_of_core_eq {s s' : FullState}
    (hc : s'.core = s.core) (h : FullArenaVarsNodup s) : FullArenaVarsNodup s' := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits at h ⊢
  rw [hc]
  exact h

theorem fullExtScratchOk_of_core_eq {c : FullCfg} {s s' : FullState}
    (h : FullExtScratchOk c s) (hext : FullExtScratchPres s s') (hc : s'.core = s.core) :
    FullExtScratchOk c s' :=
  FullExtScratchOk.of_pres h hext (fun _ hr => (fullArenaClauseRefs_of_core_eq hc).symm ▸ hr)

theorem fullSparseInv_of_core_eq {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen : s'.LengthsOk c) (hc : s'.core = s.core)
    (hext : FullExtScratchPres s s') : FullSparseInv c F0 s' :=
  h.with_scratch hlen hc (fullExtScratchOk_of_core_eq h.2.2.2.1 hext hc)

theorem fullSparseInvW_of_core_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullSparseInvW c F0 F_cur s) (hlen : s'.LengthsOk c)
    (hc : s'.core = s.core) (hext : FullExtScratchPres s s') :
    FullSparseInvW c F0 F_cur s' :=
  ⟨hlen, hc ▸ h.2.1, fullLitMarksClear_of_core_eq hc h.2.2.1,
    fullArenaVarsNodup_of_core_eq hc h.2.2.2.1,
    fullExtScratchOk_of_core_eq h.2.2.2.2.1 hext hc, hc ▸ h.2.2.2.2.2⟩

theorem fullDenseInv_of_core_eq {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullDenseInv c F0 s) (hlen : s'.LengthsOk c) (hc : s'.core = s.core)
    (hext : FullExtScratchPres s s') : FullDenseInv c F0 s' :=
  h.with_scratch hlen hc (fullExtScratchOk_of_core_eq h.2.2.2.1 hext hc)

theorem fullM6HdrInv_of_core_eq {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s s' : FullState} (h : FullM6HdrInv c F0 ext s) (hlen : s'.LengthsOk c)
    (hc : s'.core = s.core) (hext : FullExtScratchPres s s') :
    FullM6HdrInv c F0 ext s' :=
  FullM6HdrInv.mk_inv h.cfgOk h.extOk (fullSparseInv_of_core_eq h.sparse hlen hc hext)

theorem fullM6HdrInv_of_probeStep {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s s' : FullState} (h : FullM6HdrInv c F0 ext s)
    (hstep : s'.LengthsOk c ∧ s'.core = s.core ∧ FullProbeScratchPres s s' ∧
      s'.scratch.delayed_len = s.scratch.delayed_len ∧
      s'.scratch.delayed = s.scratch.delayed) :
    FullM6HdrInv c F0 ext s' :=
  fullM6HdrInv_of_core_eq h hstep.1 hstep.2.1 hstep.2.2.1.1

theorem fullM6HdrInv_of_m6Pres {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s s' : FullState} (h : FullM6HdrInv c F0 ext s) (hlen : s'.LengthsOk c)
    (hc : s'.core = s.core) (hm6 : M6HdrScratchPres s s') : FullM6HdrInv c F0 ext s' :=
  fullM6HdrInv_of_core_eq h hlen hc hm6.extPres

/-- M6 extension array update lemmas (`ext.set`, `M6HdrExtOk`, `FullM6HdrInv*`). -/
theorem m6HdrExtOk_set {ext : List (BitVec 64)} (h : M6HdrExtOk ext) (idx : Nat)
    (v : BitVec 64) : M6HdrExtOk (ext.set idx v) :=
  M6HdrExtOk.of_len (by simp [List.length_set, h.len])

theorem fullM6HdrInv_with_ext {c : FullCfg} {F0 : CNF Nat}
    {ext ext' : List (BitVec 64)} {s : FullState}
    (h : FullM6HdrInv c F0 ext s) (hext' : M6HdrExtOk ext') :
    FullM6HdrInv c F0 ext' s :=
  FullM6HdrInv.mk_inv h.cfgOk hext' h.sparse

theorem fullM6HdrInv_set_ext {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (h : FullM6HdrInv c F0 ext s) (idx : Nat) (v : BitVec 64) :
    FullM6HdrInv c F0 (ext.set idx v) s :=
  fullM6HdrInv_with_ext h (m6HdrExtOk_set h.extOk idx v)

theorem m6ExtW2bPres_set_tier1 {ext : List (BitVec 64)} {k : Nat} (v : BitVec 64) :
    M6ExtW2bPres ext (ext.set (m6WTier1 + k) v) :=
  M6ExtW2bPres.set_ge8 v (by dsimp [m6WTier1]; omega)

theorem m6ExtW2bPres_set_tier2 {ext : List (BitVec 64)} {k : Nat} (v : BitVec 64) :
    M6ExtW2bPres ext (ext.set (m6WTier2 + k) v) :=
  M6ExtW2bPres.set_ge8 v (by dsimp [m6WTier2]; omega)

theorem m6ExtW2bPres_set_delayCnt {ext : List (BitVec 64)} {k : Nat} (v : BitVec 64) :
    M6ExtW2bPres ext (ext.set (m6WDelayCnt + k) v) :=
  M6ExtW2bPres.set_ge8 v (by dsimp [m6WDelayCnt]; omega)

/-- Scratch header fields whose mutation preserves `FullCoreState`, `LengthsOk`,
`FullProbeScratchPres`, and `delayed`/`delayed_len` (`59` fields). -/
@[expose] def HdrWordField.isScrPres : HdrWordField → Bool
  | .heap_len | .scinc | .rel_period | .rel_limit | .rel_wait | .rel_u | .rel_v | .rel_trigger
  | .conflicts | .learned_lits | .min_removed | .stable | .switched | .mode_count
  | .mode_confl_lim | .mode_tick_lim | .mode_saved_ticks | .search_ticks | .q_first | .q_last
  | .q_search_idx | .q_search_stamp | .q_cur_stamp | .target_assigned | .best_assigned
  | .rephase_limit | .rephased | .reduce_limit | .reductions | .tier1 | .tier2 | .restarts
  | .restart_limit | .ema_fast_biased | .ema_fast_exp | .ema_slow_biased | .ema_slow_exp
  | .rng_state | .chrono_levels | .otfs_cnt | .eager_sub_cnt | .probe_limit | .probings
  | .elim_limit | .eliminations | .elim_bound | .iterating | .hbr_cnt | .trans_cnt | .viv_cnt
  | .subst_cnt | .cong_cnt | .sweep_cnt | .bve_cnt | .bce_cnt | .bva_cnt | .walk_cnt_stat
  | .fwd_sub_cnt | .fwd_str_cnt => true
  | _ => false

/-- Generic frame step for any probe-preserving scratch `HdrWordField` (`59` fields). -/
theorem fullState_upd_scrHdr_step (f : HdrWordField) (hp : f.isScrPres = true)
    {c : FullCfg} {s : FullState} (hs : s.LengthsOk c) (v : BitVec 64) :
    let s' : FullState := f.set s v
    s'.LengthsOk c ∧ s'.core = s.core ∧ FullProbeScratchPres s s' ∧
      s'.scratch.delayed_len = s.scratch.delayed_len ∧
      s'.scratch.delayed = s.scratch.delayed := by
  cases f <;> first
    | (simp [HdrWordField.isScrPres] at hp; done)
    | exact ⟨⟨hs.1, { hs.2 with walk_vals_len := hs.2.walk_vals_len }⟩, rfl,
        ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Generic `FullM6HdrInv` preservation for any probe-preserving scratch `HdrWordField`. -/
theorem fullM6HdrInv_upd_scrHdr (f : HdrWordField) (hp : f.isScrPres = true)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    (h : FullM6HdrInv c F0 ext s) (v : BitVec 64) :
    FullM6HdrInv c F0 ext (f.set s v) :=
  fullM6HdrInv_of_probeStep h (fullState_upd_scrHdr_step f hp h.sparse.lengths v)

/- Generated single-field, grouped-scalar, and array `FullScratch` frame lemmas (zero 24-`rfl`
boilerplate). -/
section GenUpdLemmas
open Lean Elab Command

private meta def elabUpdCmd (tag src : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command src tag with
  | .ok stx => elabCommand stx
  | .error err => throwError "{tag}: failed to parse: {err}\n{src}"

local elab "gen_full_state_upd_lemmas!" : command => do
  -- 1. Grouped & single scalar `FullScratch` updates (`11` `*_step` + `5` `fullM6HdrInv_upd_*`)
  let scalarSpecs : Array (String × List (String × String) × Bool) := #[
    ("search_ticks", [("search_ticks", "v")], true),
    ("tier1", [("tier1", "v")], true),
    ("tier2", [("tier2", "v")], true),
    ("tiers", [("tier1", "t1"), ("tier2", "t2")], false),
    ("ema", [("ema_fast_biased", "fb"), ("ema_fast_exp", "fe"),
             ("ema_slow_biased", "sb"), ("ema_slow_exp", "se")], true),
    ("rng_state", [("rng_state", "v")], true),
    ("restarts", [("restarts", "r"), ("restart_limit", "rl")], false),
    ("mode", [("stable", "stb"), ("switched", "swt"), ("mode_count", "mc"),
              ("mode_confl_lim", "mcl"), ("mode_tick_lim", "mtl"),
              ("mode_saved_ticks", "mst")], false),
    ("probe", [("probe_limit", "pl"), ("probings", "pr")], false),
    ("elim", [("elim_limit", "el"), ("eliminations", "ec"), ("elim_bound", "eb")], false),
    ("rel", [("rel_period", "rp"), ("rel_limit", "rl"), ("rel_wait", "rw"),
             ("rel_u", "ru"), ("rel_v", "rv"), ("rel_trigger", "rt")], false)
  ]
  for (nm, flds, emitInv) in scalarSpecs do
    let vars := String.intercalate " " (flds.map (·.2))
    let assigns := String.intercalate ", " (flds.map fun (f, v) => s!"{f} := {v}")
    let sUpd := s!"\{ s with scratch := \{ s.scratch with {assigns} } }"
    elabUpdCmd nm <|
      s!"theorem fullState_upd_{nm}_step \{c : FullCfg} \{s : FullState} " ++
      s!"(hs : s.LengthsOk c) ({vars} : BitVec 64) :\n" ++
      s!"    let s' : FullState := {sUpd}\n" ++
      s!"    s'.LengthsOk c ∧ s'.core = s.core ∧ FullProbeScratchPres s s' ∧\n" ++
      s!"      s'.scratch.delayed_len = s.scratch.delayed_len ∧\n" ++
      s!"      s'.scratch.delayed = s.scratch.delayed :=\n" ++
      s!"  ⟨⟨hs.1, \{ hs.2 with walk_vals_len := hs.2.walk_vals_len }⟩, rfl,\n" ++
      s!"    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩"
    if emitInv then
      elabUpdCmd (nm ++ "_inv") <|
        s!"theorem fullM6HdrInv_upd_{nm} \{c : FullCfg} \{F0 : CNF Nat}\n" ++
        s!"    \{ext : List (BitVec 64)} \{s : FullState} " ++
        s!"(h : FullM6HdrInv c F0 ext s) ({vars} : BitVec 64) :\n" ++
        s!"    FullM6HdrInv c F0 ext {sUpd} :=\n" ++
        s!"  fullM6HdrInv_of_probeStep h (fullState_upd_{nm}_step h.sparse.lengths {vars})"
  -- 2. Array `FullScratch` updates (`6` `*_step` + `8` `fullM6HdrInv_upd_*[_set]`)
  let arrProbeSpecs : Array (String × String × String × String) := #[
    ("glue_used", "gu'", "hg", "glue_used_len"),
    ("wsort", "ws'", "hw", "wsort_len")
  ]
  for (nm, v, hv, lf) in arrProbeSpecs do
    let sUpd := s!"\{ s with scratch := \{ s.scratch with {nm} := {v} } }"
    elabUpdCmd nm <|
      s!"theorem fullState_upd_{nm}_step \{c : FullCfg} \{s : FullState}\n" ++
      s!"    (hs : s.LengthsOk c) \{{v} : List (BitVec 32)}\n" ++
      s!"    ({hv} : {v}.length = s.scratch.{nm}.length) :\n" ++
      s!"    let s' : FullState := {sUpd}\n" ++
      s!"    s'.LengthsOk c ∧ s'.core = s.core ∧ FullProbeScratchPres s s' ∧\n" ++
      s!"      s'.scratch.delayed_len = s.scratch.delayed_len ∧\n" ++
      s!"      s'.scratch.delayed = s.scratch.delayed :=\n" ++
      s!"  ⟨⟨hs.1, \{ hs.2 with {lf} := {hv}.trans hs.2.{lf} }⟩, rfl,\n" ++
      s!"    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩"
  let arrExtSpecs : Array (String × String × String × String × String × String) := #[
    ("scratch_buf", "buf'", "hb", "scratch_buf_len", "work_stk1", "work_stk2"),
    ("work_stk1", "ws1'", "hw1", "work_stk1_len", "work_stk2", "scratch_buf"),
    ("work_stk2", "ws2'", "hw2", "work_stk2_len", "work_stk1", "scratch_buf")
  ]
  for (nm, v, hv, lf, k1, k2) in arrExtSpecs do
    let sUpd := s!"\{ s with scratch := \{ s.scratch with {nm} := {v} } }"
    elabUpdCmd nm <|
      s!"theorem fullState_upd_{nm}_step \{c : FullCfg} \{s : FullState}\n" ++
      s!"    (hs : s.LengthsOk c) \{{v} : List (BitVec 32)}\n" ++
      s!"    ({hv} : {v}.length = s.scratch.{nm}.length) :\n" ++
      s!"    let s' : FullState := {sUpd}\n" ++
      s!"    s'.LengthsOk c ∧ s'.core = s.core ∧ FullExtScratchPres s s' ∧\n" ++
      s!"      s'.scratch.delayed = s.scratch.delayed ∧\n" ++
      s!"      s'.scratch.delayed_len = s.scratch.delayed_len ∧\n" ++
      s!"      s'.scratch.{k1} = s.scratch.{k1} ∧ s'.scratch.{k2} = s.scratch.{k2} :=\n" ++
      s!"  ⟨⟨hs.1, \{ hs.2 with {lf} := {hv}.trans hs.2.{lf} }⟩, rfl,\n" ++
      s!"    ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩"
    elabUpdCmd (nm ++ "_inv") <|
      s!"theorem fullM6HdrInv_upd_{nm} \{c : FullCfg} \{F0 : CNF Nat}\n" ++
      s!"    \{ext : List (BitVec 64)} \{s : FullState} (h : FullM6HdrInv c F0 ext s)\n" ++
      s!"    \{{v} : List (BitVec 32)} ({hv} : {v}.length = s.scratch.{nm}.length) :\n" ++
      s!"    FullM6HdrInv c F0 ext {sUpd} :=\n" ++
      s!"  let st := fullState_upd_{nm}_step h.sparse.lengths {hv}\n" ++
      s!"  fullM6HdrInv_of_core_eq h st.1 st.2.1 st.2.2.1"
    elabUpdCmd (nm ++ "_inv_set") <|
      s!"theorem fullM6HdrInv_upd_{nm}_set \{c : FullCfg} \{F0 : CNF Nat}\n" ++
      s!"    \{ext : List (BitVec 64)} \{s : FullState} (h : FullM6HdrInv c F0 ext s)\n" ++
      s!"    (idx : Nat) (v : BitVec 32) :\n" ++
      s!"    FullM6HdrInv c F0 ext " ++
      s!"\{ s with scratch := \{ s.scratch with {nm} := s.scratch.{nm}.set idx v } } :=\n" ++
      s!"  fullM6HdrInv_upd_{nm} h (List.length_set ..)"

gen_full_state_upd_lemmas!

end GenUpdLemmas

theorem fullState_upd_delayed_step {c : FullCfg} {s : FullState}
    (hs : s.LengthsOk c) {d' : List (BitVec 32)}
    (hd : d'.length = s.scratch.delayed.length) (dl : Nat) :
    let s' : FullState := { s with scratch := { s.scratch with delayed_len := dl, delayed := d' } }
    s'.LengthsOk c ∧ s'.core = s.core ∧ FullProbeScratchPres s s' :=
  ⟨⟨hs.1, { hs.2 with delayed_len_arr := hd.trans hs.2.delayed_len_arr }⟩, rfl,
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem fullM6HdrInv_upd_delayed {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInv c F0 ext s)
    {d' : List (BitVec 32)} (hd : d'.length = s.scratch.delayed.length) (dl : Nat) :
    FullM6HdrInv c F0 ext
      { s with scratch := { s.scratch with delayed_len := dl, delayed := d' } } :=
  let st := fullState_upd_delayed_step h.sparse.lengths hd dl
  fullM6HdrInv_of_core_eq h st.1 st.2.1 st.2.2.1

theorem fullM6HdrInv_upd_delayed_set {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInv c F0 ext s)
    (idx : Nat) (v : BitVec 32) :
    FullM6HdrInv c F0 ext
      { s with scratch := { s.scratch with delayed := s.scratch.delayed.set idx v } } :=
  fullM6HdrInv_upd_delayed h (List.length_set ..) s.scratch.delayed_len

/-! ## 2. `M6Hdr <-> FullHdr` Bridge Combinators -/

theorem fullM6HdrInv_to_coreInv {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInv c F0 ext s) :
    FullM6HdrCoreInv c F0 ext s :=
  FullM6HdrCoreInv.mk_inv h.cfgOk h.extOk h.sparse.1

theorem fullM6HdrInv_exists_witness {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInv c F0 ext s) :
    ∃ F_cur, FullM6HdrInvW c F0 F_cur ext s := by
  obtain ⟨F_cur, hw⟩ := h.sparse.exists_witness
  exact ⟨F_cur, FullM6HdrInvW.mk_inv h.cfgOk h.extOk hw⟩

theorem fullM6HdrInv_inconsistent_unsat {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInv c F0 ext s)
    (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat :=
  h.sparse.inconsistent_unsat hinc

/-- Lift any `SafetySlice.spec fullSafetySlice` contract over `FullMem c s` to
`FullM6HdrMem c ext s` while preserving `FullM6HdrCfgOk`, `M6HdrExtOk`, `LengthsOk`, and
`PreservesCoreSlice`. -/
theorem fullM6Hdr_frame_safetySlice {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {as rs : List Ty}
    {pre : FullCfg → Tup Val as → FullState → Prop}
    {post : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {Q : Post rs} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hpre : pre c xs s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', s'.LengthsOk c →
      PreservesCoreSlice (fullSafetySlice c).coreProj s s' → post c xs r s s' →
      FullM6HdrCfgOk c → M6HdrExtOk ext → (FullM6HdrMem c ext s' ⋆ R) m' → Q r m') :
    SafetySlice.spec fullSafetySlice pre post xs m Q X :=
  ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, hpre, hlen, fullM6HdrMem_focus_full hm,
    fun r s' m' hc hs' hp hm' =>
      hk r s' m' hs' hc hp hcfg hext (fullM6HdrMem_unfocus_full hm')⟩

/-- Lift `SafetySlice.spec fullSafetySlice` directly from `FullM6HdrInv`. -/
theorem fullM6Hdr_frame_safetySlice_inv {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {as rs : List Ty} {pre : FullCfg → Tup Val as → FullState → Prop}
    {post : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {Q : Post rs} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s)
    (hpre : pre c xs s) (hext_ok : ∀ r s', post c xs r s s' → FullExtScratchPres s s')
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInv c F0 ext s' → post c xs r s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q r m') :
    SafetySlice.spec fullSafetySlice pre post xs m Q X :=
  fullM6Hdr_frame_safetySlice hinv.cfgOk hinv.extOk hinv.sparse.lengths hpre hm
    (fun r s' m' hs' hc hp hcfg hext hm' =>
      let hext' := FullExtScratchOk.of_pres hinv.sparse.2.2.2.1 (hext_ok r s' hp)
        (fun _ ha => (fullArenaClauseRefs_of_core_eq hc).symm ▸ ha)
      hk r s' m' (FullM6HdrInv.mk_inv hcfg hext (hinv.sparse.with_scratch hs' hc hext')) hp hm')

/-! ### 2.1 One-Line `wp` Call Bridges (`Full1..5` & `M6Hdr` specs -> `FullM6HdrInv*`) -/

theorem m6Hdr_call_safetyVoid_inv {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', fullSafetyVoidSpec (c.hdr, ()) m Q' X' →
      Γ f [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m', FullM6HdrInv c F0 ext s' → FullProbeScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := []) args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (fullM6Hdr_frame_safetySlice_inv hinv (by exact rfl)
    (fun (_ : Tup Val []) _ hp => hp.1) hm (fun () s' m' hinv' hp hm' => hk s' m' hinv' hp hm'))

private theorem fullArenaPermEq_nodup {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hnd : FullArenaVarsNodup s) :
    FullArenaVarsNodup s' := by
  intro r hr
  unfold fullArenaClauseRefs at hr
  rw [hap.2.1] at hr
  have hmem : r ∈ fullArenaClauseRefs s := hr
  have hperm := hap.2.2 r hmem
  intro hgb
  unfold fullArenaClauseGarb at hgb
  rw [hperm.2.1] at hgb
  have hn := hnd r hmem hgb
  unfold fullArenaClauseLits at hn ⊢
  exact (List.Perm.map (fun x => x / 2) hperm.2.2).nodup_iff.mpr hn

theorem m6Hdr_call_fullPropagate_invW {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', fullPropagateSpec (c.hdr, ()) m Q' X' →
      Γ f [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInvW c F0 F_cur ext s' →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧
        (s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (r = 2#64 → s'.core.oom ≠ 0#64 ∨ s'.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := [i64]) args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X ⟨c, F0, F_cur, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R,
    rfl, hinv.sparseW.1, hinv.sparseW.2.1, hinv.sparseW.2.2.2.2.2,
    fullM6HdrMem_focus_full hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' s'
    hs' hw' hte hap hfl hdom h0 h1 h2 hs_eq hm'
  have hmc : FullLitMarksClear c s' := by
    have hmc0 := hinv.sparseW.2.2.1
    unfold FullLitMarksClear FullMrkZero at hmc0 ⊢; exact hmc0
  have hnd : FullArenaVarsNodup s' :=
    fullArenaPermEq_nodup hap hinv.sparseW.2.2.2.1
  have hll : FullLastLearnedWf s' :=
    hinv.sparseW.2.2.2.2.1.1.of_refs_subset rfl (fun _ hr => by
      unfold fullArenaClauseRefs at hr ⊢
      exact hap.2.1 ▸ hr)
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hs', hw', hmc, hnd, ⟨hll, hinv.sparseW.2.2.2.2.1.2⟩, hinv.sparseW.2.2.2.2.2⟩
  exact hk r s' m' hinv' hte hap hfl hdom h0 h1 h2 hs_eq (fullM6HdrMem_unfocus_full hm')

theorem m6Hdr_call_fullProbe_inv {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', fullProbeSpec (c.hdr, ()) m Q' X' → Γ f [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', s'.LengthsOk c → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := [i64]) args k) m := by
  refine wp_call_of_spec args k (hargs ▸ hΓ _ X ⟨c, F0, s,
    m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse, hl0, fullM6HdrMem_focus_full hm, ?_⟩)
  intro r s' m' hs' hfl hr hu h1 hm'
  exact hk r s' m' hs' hfl hr hu
    (fun eq1 => ⟨FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk (h1 eq1).1, (h1 eq1).2⟩)
    (fullM6HdrMem_unfocus_full hm')

theorem m6Hdr_call_fullSearch_inv {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', fullSearchSpec (c.hdr, ()) m Q' X' → Γ f [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', s'.LengthsOk c → (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := [i64]) args k) m := by
  refine wp_call_of_spec args k (hargs ▸ hΓ _ X ⟨c, F0, s,
    m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse, hl0, fullM6HdrMem_focus_full hm, ?_⟩)
  intro r s' m' hs' hr hu h10 hm'
  exact hk r s' m' hs' hr hu h10 (fullM6HdrMem_unfocus_full hm')

theorem m6Hdr_call_m6HdrW2a {Γ : Env} {f : Sym} {extraArgs rs ret : List Ty}
    {rest : Tup Val extraArgs} {args : Tup (Arg Val) (i64 :: extraArgs)}
    {k : Tup Val rs → Expr Val Cont ret}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, rest))
    (hΓ : ∀ Q' X', m6HdrW2aSpec extraArgs rs (c.hdr, rest) m Q' X' →
      Γ f (i64 :: extraArgs) rs (c.hdr, rest) m Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m', s'.core = s.core → s'.LengthsOk c → M6HdrScratchPres s s' →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f (as := i64 :: extraArgs) (bs := rs) args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (m6HdrW2aSpec_of rfl hcfg hext hlen hm hk)

/-! ## 3. Bounded Loop-Measure / `BitVec` Kernel Lemmas & `c0_hfast` Glue -/

/-! ### 3.1 Unsigned BitVec Arithmetic, Saturating Add, Masks, Literals, Arena Bounds -/

theorem bv32_add_small_eq {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_sub_small_eq {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem bv64_add1_toNat {i n : BitVec 64} (h : i.toNat < n.toNat) :
    (i + 1#64).toNat = i.toNat + 1 :=
  bv64_add_small_eq (by have := n.isLt; simp; omega)

theorem bv32_add1_toNat {i n : BitVec 32} (h : i.toNat < n.toNat) :
    (i + 1#32).toNat = i.toNat + 1 :=
  bv32_add_small_eq (by have := n.isLt; simp; omega)

theorem bv64_measure_sub_lt {i n : BitVec 64} (h : i.toNat < n.toNat) :
    n.toNat - (i + 1#64).toNat < n.toNat - i.toNat := by
  rw [bv64_add1_toNat h]; omega

theorem bv64_sat_add_eq {a d cap : BitVec 64} (_ha : a.toNat ≤ cap.toNat)
    (hd : d.toNat ≤ cap.toNat) :
    (if cap - d < a then cap else a + d).toNat = min (a.toNat + d.toNat) cap.toNat := by
  by_cases h : cap - d < a
  · have hlt : (cap - d).toNat < a.toNat := BitVec.lt_def.mp h
    rw [bv64_sub_small_eq hd] at hlt
    simp only [h, ↓reduceIte]
    omega
  · have hle : a.toNat ≤ (cap - d).toNat := by
      have h1 : ¬ ((cap - d).toNat < a.toNat) := by simpa [BitVec.lt_def] using h
      omega
    rw [bv64_sub_small_eq hd] at hle
    have hfit : a.toNat + d.toNat < 2 ^ 64 := by have := cap.isLt; omega
    simp only [h, ↓reduceIte, bv64_add_small_eq hfit]
    omega

theorem bv64_and_le_right (x m : BitVec 64) : (x &&& m).toNat ≤ m.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right

theorem bv32_and_le_right (x m : BitVec 32) : (x &&& m).toNat ≤ m.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right

theorem bv64_and_sub1_lt {x sz : BitVec 64} (hsz : 0 < sz.toNat) :
    (x &&& (sz - 1#64)).toNat < sz.toNat := by
  have h1 : (x &&& (sz - 1#64)).toNat ≤ (sz - 1#64).toNat := bv64_and_le_right x (sz - 1#64)
  have h2 : (sz - 1#64).toNat = sz.toNat - 1 := bv64_sub_small_eq (by simp; omega)
  omega

theorem bv32_shr1_toNat (lit : BitVec 32) : (lit >>> 1#32).toNat = lit.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_lit_var_lt {lit : BitVec 32} {mv : Nat} (hl : lit.toNat < 2 * mv) :
    (lit >>> 1#32).toNat < mv := by
  rw [bv32_shr1_toNat]; omega

private theorem nat_xor1_two_mul (q : Nat) : (2 * q) ^^^ 1 = 2 * q + 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.mul_comm]
  | succ k =>
    rw [Nat.testBit_xor]
    simp only [Nat.testBit_succ]
    simp [show (2 * q) / 2 = (2 * q + 1) / 2 by omega]

private theorem nat_xor1_two_mul_add_one (q : Nat) : (2 * q + 1) ^^^ 1 = 2 * q := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.mul_comm]
  | succ k =>
    rw [Nat.testBit_xor]
    simp only [Nat.testBit_succ]
    simp [show (2 * q + 1) / 2 = (2 * q) / 2 by omega]

theorem nat_xor1_eq (l : Nat) : l ^^^ 1 = if l % 2 = 0 then l + 1 else l - 1 := by
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm
  · simp only [hm, ↓reduceIte]
    have hq : l = 2 * (l / 2) := by omega
    rw [hq, nat_xor1_two_mul]
  · simp only [hm]
    have hq : l = 2 * (l / 2) + 1 := by omega
    have hx : l ^^^ 1 = 2 * (l / 2) := by
      calc l ^^^ 1 = (2 * (l / 2) + 1) ^^^ 1 := by rw [← hq]
        _ = 2 * (l / 2) := nat_xor1_two_mul_add_one (l / 2)
    rw [hx]; simp; omega

theorem nat_xor1_lt {l mv : Nat} (hl : l < 2 * mv) : (l ^^^ 1) < 2 * mv := by
  rw [nat_xor1_eq]; split <;> omega

theorem nat_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  rw [nat_xor1_eq]; split <;> omega

theorem nat_xor1_mod2 (l : Nat) : (l ^^^ 1) % 2 = 1 - l % 2 := by
  rw [nat_xor1_eq]; split <;> omega

theorem bv32_lit_neg_toNat (lit : BitVec 32) : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem bv32_lit_neg_lt {lit : BitVec 32} {mv : Nat} (hl : lit.toNat < 2 * mv) :
    (lit ^^^ 1#32).toNat < 2 * mv := by
  rw [bv32_lit_neg_toNat]; exact nat_xor1_lt hl

theorem bv32_xor1_shr1 (lit : BitVec 32) : (lit ^^^ 1#32) >>> 1#32 = lit >>> 1#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [bv32_shr1_toNat, bv32_lit_neg_toNat, nat_xor1_div2, ← bv32_shr1_toNat]

theorem bv64_arena_p3_add_k_toNat {p k : BitVec 64} {alen : Nat}
    (hp : p.toNat + 3 ≤ alen) (hc : k.toNat < alen - (p.toNat + 3)) (hfit : alen < 2 ^ 64) :
    (p + 3#64 + k).toNat = p.toNat + 3 + k.toNat ∧ (p + 3#64 + k).toNat < alen := by
  have h3 : (p + 3#64).toNat = p.toNat + 3 := bv64_add_small_eq (by simp; omega)
  have hpk : (p + 3#64 + k).toNat = p.toNat + 3 + k.toNat := by
    rw [bv64_add_small_eq (by rw [h3]; omega), h3]
  exact ⟨hpk, by omega⟩

theorem bv64_arena_clen_le {p clen : BitVec 64} {alen : Nat}
    (hp : p.toNat + 3 ≤ alen) (hfit : alen < 2 ^ 64)
    (hle : clen ≤ BitVec.ofNat 64 alen - (p + 3#64)) : clen.toNat ≤ alen - (p.toNat + 3) := by
  have ha : (BitVec.ofNat 64 alen).toNat = alen := by simp [Nat.mod_eq_of_lt hfit]
  have h3 : (p + 3#64).toNat = p.toNat + 3 := bv64_add_small_eq (by simp; omega)
  have hsub : (BitVec.ofNat 64 alen - (p + 3#64)).toNat = alen - (p.toNat + 3) := by
    rw [bv64_sub_small_eq (by rw [ha, h3]; exact hp), ha, h3]
  rw [← hsub]
  exact BitVec.le_def.mp hle

/-! ### 3.2 `c0_hfast` Frame-Lift Glue & Scoped `FullM6HdrMem` Tactics -/

theorem fullM6HdrMem_focus {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m :=
  fullM6HdrMem_focus_full hm

theorem fullM6HdrMem_unfocus {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m) :
    (FullM6HdrMem c ext s ⋆ R) m :=
  fullM6HdrMem_unfocus_full hm

theorem fullM6HdrMem_ext_focus {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    (array64 (c.hdr - 2304) ext ⋆ (FullMem c s ⋆ R)) m :=
  sep_swap_l ((fullM6HdrMem_iff c ext s R m).mp hm)

theorem fullM6HdrMem_ext_unfocus {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 (c.hdr - 2304) ext ⋆ (FullMem c s ⋆ R)) m) :
    (FullM6HdrMem c ext s ⋆ R) m :=
  (fullM6HdrMem_iff c ext s R m).mpr (sep_swap_l hm)

/-- Execute a `wp` step proven over `FullMem c s ⋆ (m6ExtMem ... ⋆ R)` inside a caller owning
`(FullM6HdrMem c ext s ⋆ R) m`. -/
theorem wp_m6Hdr_focus_frame {Γ : Env} {rs : List Ty} {e : Expr Val Cont rs}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hwp : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m →
      wp Γ Q X e m) :
    wp Γ Q X e m :=
  hwp (fullM6HdrMem_focus_full hm)

/-! Scoped `c0_load` / `c0_store` bridge rules acting directly on `(FullM6HdrMem c ext s ⋆ R) m`
and `(FullMem c s ⋆ (array64 a ext ⋆ R)) m`. -/

namespace M6ProofUtilTactics

private theorem m6Ext_off_eq (a : BitVec 64) {k : Nat} (hk : k < 2 ^ 61) :
    a + BitVec.ofNat 64 (8 * k) = a + BitVec.ofNat 64 k * 8#64 ∧
      (BitVec.ofNat 64 k).toNat = k := by
  have hklt : k < 2 ^ 64 := Nat.lt_trans hk (by decide)
  have hmod : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt]
  refine ⟨?_, hmod⟩
  rw [show (8#64 : BitVec 64) = (8 : BitVec 64) from rfl, m8, hmod]

section ExtRules
variable {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_fullM6Hdr_ext_mul8 {i : BitVec 64}
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hi : i.toNat < ext.length) :
    loadVal m i64 ((c.hdr - 2304#64) + i * 8#64) = some (ext[i.toNat]'hi) :=
  M6HdrTactics.load_m6Ext_mul8 ((fullM6HdrMem_iff c ext s R m).mp hm) hi

@[scoped c0_store] theorem store_fullM6Hdr_ext_mul8 {i v : BitVec 64}
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hi : i.toNat < ext.length) :
    storeOk m i64 ((c.hdr - 2304#64) + i * 8#64) ∧
      (FullM6HdrMem c (ext.set i.toNat v) s ⋆ R)
        (storeMem m i64 ((c.hdr - 2304#64) + i * 8#64) v) := by
  obtain ⟨hok, hst⟩ := M6HdrTactics.store_m6Ext_mul8 v ((fullM6HdrMem_iff c ext s R m).mp hm) hi
  exact ⟨hok, (fullM6HdrMem_iff c (ext.set i.toNat v) s R _).mpr hst⟩

@[scoped c0_load] theorem load_fullM6Hdr_ext_shl3 {i : BitVec 64}
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hi : i.toNat < ext.length) (hb : i.toNat < 2 ^ 61) :
    loadVal m i64 ((c.hdr - 2304#64) + (i <<< 3#64)) = some (ext[i.toNat]'hi) :=
  M6HdrTactics.load_m6Ext_shl3 ((fullM6HdrMem_iff c ext s R m).mp hm) hi hb

@[scoped c0_store] theorem store_fullM6Hdr_ext_shl3 {i v : BitVec 64}
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hi : i.toNat < ext.length) (hb : i.toNat < 2 ^ 61) :
    storeOk m i64 ((c.hdr - 2304#64) + (i <<< 3#64)) ∧
      (FullM6HdrMem c (ext.set i.toNat v) s ⋆ R)
        (storeMem m i64 ((c.hdr - 2304#64) + (i <<< 3#64)) v) := by
  obtain ⟨hok, hst⟩ := M6HdrTactics.store_m6Ext_shl3 v ((fullM6HdrMem_iff c ext s R m).mp hm) hi hb
  exact ⟨hok, (fullM6HdrMem_iff c (ext.set i.toNat v) s R _).mpr hst⟩

@[scoped c0_load] theorem load_fullM6Hdr_ext_zero
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hi : 0 < ext.length) :
    loadVal m i64 (c.hdr - 2304#64) = some (ext[0]'hi) :=
  M6HdrTactics.load_m6Ext_zero ((fullM6HdrMem_iff c ext s R m).mp hm) hi

@[scoped c0_store] theorem store_fullM6Hdr_ext_zero {v : BitVec 64}
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hi : 0 < ext.length) :
    storeOk m i64 (c.hdr - 2304#64) ∧
      (FullM6HdrMem c (ext.set 0 v) s ⋆ R) (storeMem m i64 (c.hdr - 2304#64) v) := by
  obtain ⟨hok, hst⟩ := M6HdrTactics.store_m6Ext_zero v ((fullM6HdrMem_iff c ext s R m).mp hm) hi
  exact ⟨hok, (fullM6HdrMem_iff c (ext.set 0 v) s R _).mpr hst⟩

@[scoped c0_load] theorem load_fullM6Hdr_ext_off {k : Nat}
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hi : k < ext.length) (hk : k < 2 ^ 61) :
    loadVal m i64 ((c.hdr - 2304#64) + BitVec.ofNat 64 (8 * k)) = some (ext[k]'hi) := by
  have ⟨heq, hmod⟩ := m6Ext_off_eq (c.hdr - 2304#64) hk
  rw [heq]
  have h := M6HdrTactics.load_m6Ext_mul8 (i := BitVec.ofNat 64 k)
    ((fullM6HdrMem_iff c ext s R m).mp hm) (by rwa [hmod])
  simp only [hmod] at h; exact h

@[scoped c0_store] theorem store_fullM6Hdr_ext_off {k : Nat} (v : BitVec 64)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hi : k < ext.length) (hk : k < 2 ^ 61) :
    storeOk m i64 ((c.hdr - 2304#64) + BitVec.ofNat 64 (8 * k)) ∧
      (FullM6HdrMem c (ext.set k v) s ⋆ R)
        (storeMem m i64 ((c.hdr - 2304#64) + BitVec.ofNat 64 (8 * k)) v) := by
  have ⟨heq, hmod⟩ := m6Ext_off_eq (c.hdr - 2304#64) hk
  rw [heq]
  obtain ⟨hok, hst⟩ :=
    M6HdrTactics.store_m6Ext_mul8 v ((fullM6HdrMem_iff c ext s R m).mp hm) (by rwa [hmod])
  rw [hmod] at hst; exact ⟨hok, (fullM6HdrMem_iff c (ext.set k v) s R _).mpr hst⟩

end ExtRules

end M6ProofUtilTactics

/-! ## 4. `ModuleOk` / `Env.noExit` Composition Combinators -/

theorem env_ofTable_noExit_all {tbl : List SpecEntry}
    (h : tbl.all SpecEntry.noExit = true) :
    ∀ f as bs xs m Q X X',
      Env.ofTable tbl f as bs xs m Q X → Env.ofTable tbl f as bs xs m Q X' :=
  Env.ofTable_noExit (fun e he => List.all_eq_true.mp h e he)

theorem tbl_all_noExit_append {t1 t2 : List SpecEntry}
    (h1 : t1.all SpecEntry.noExit = true) (h2 : t2.all SpecEntry.noExit = true) :
    (t1 ++ t2).all SpecEntry.noExit = true := by
  simp [List.all_append, h1, h2]

theorem module_namesNodup_of_checkAcyclic {M : Module}
    (hchk : M.checkAcyclic = true) : M.namesNodup := by
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact Module.namesNodup_of_checkNamesNodup hchk.1

theorem tbl_nodup_of_sigs {M : Module} {tbl : List SpecEntry}
    (hchk : M.checkAcyclic = true)
    (hsigs : tbl.map SpecEntry.name = M.fns.map Fn.name) :
    (tbl.map SpecEntry.name).Nodup := by
  have hnd := module_namesNodup_of_checkAcyclic hchk
  rw [hsigs]
  exact (List.nodup_append.mp hnd).1

/-- `O(n)` index lookup into `Env.ofTable` via `tbl[idx]? = some e` (avoids `simp [tbl]`). -/
theorem env_ofTable_row_at {tbl : List SpecEntry} {idx : Nat} {e : SpecEntry}
    (hget : tbl[idx]? = some e) (hnd : (tbl.map SpecEntry.name).Nodup)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : e.eff xs m Q X) : Env.ofTable tbl e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem (List.mem_of_getElem? hget) hnd h

/-- Eliminate `Env.ofTable tbl e.name e.as e.rs` directly back to `e.eff` when `e ∈ tbl`
and `(tbl.map SpecEntry.name).Nodup`. -/
theorem env_ofTable_elim_of_mem {tbl : List SpecEntry} {e : SpecEntry}
    (he : e ∈ tbl) (hnd : (tbl.map SpecEntry.name).Nodup)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : Env.ofTable tbl e.name e.as e.rs xs m Q X) : e.eff xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hes
    · exact (Env.ofTable_cons_self e es xs m Q X).mp h
    · have hne : e'.name ≠ e.name := fun hnm => hnd.1 (hnm ▸ List.mem_map_of_mem hes)
      rw [Env.ofTable_cons_ne hne] at h
      exact ih hes hnd.2 h

theorem allFns_nil (P : Fn → Prop) : AllFns P [] := trivial

theorem allFns_cons {P : Fn → Prop} {fn : Fn} {fs : List Fn}
    (h1 : P fn) (h2 : AllFns P fs) : AllFns P (fn :: fs) := ⟨h1, h2⟩

theorem allFns_append {P : Fn → Prop} :
    ∀ {fs1 fs2 : List Fn}, AllFns P fs1 → AllFns P fs2 → AllFns P (fs1 ++ fs2)
  | [], _, _, h2 => h2
  | _ :: _, _, h1, h2 => ⟨h1.1, allFns_append h1.2 h2⟩

theorem allFns_of_mem {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ fn ∈ fs, P fn) → AllFns P fs
  | [], _ => trivial
  | fn :: _, h => ⟨h fn List.mem_cons_self, allFns_of_mem (fun x hx => h x (.tail _ hx))⟩

theorem allFns_drop {P : Fn → Prop} {fs : List Fn} (h : AllFns P fs) (n : Nat) :
    AllFns P (fs.drop n) :=
  allFns_of_mem (fun x hx => AllFns.mem h x (List.mem_of_mem_drop hx))

theorem allFns_take {P : Fn → Prop} {fs : List Fn} (h : AllFns P fs) (n : Nat) :
    AllFns P (fs.take n) :=
  allFns_of_mem (fun x hx => AllFns.mem h x (List.mem_of_mem_take hx))

theorem tableImpl_nil (Γ : Env) (tbl : List SpecEntry) : TableImpl Γ [] tbl := trivial

theorem tableImpl_cons {Γ : Env} {fn : Fn} {fs : List Fn} {e : SpecEntry} {es : List SpecEntry}
    (h1 : SpecEntry.Impl Γ fn e) (h2 : TableImpl Γ fs es) :
    TableImpl Γ (fn :: fs) (e :: es) :=
  ⟨h1, h2⟩

theorem tableImpl_append {Γ : Env} :
    ∀ {fs1 fs2 : List Fn} {t1 t2 : List SpecEntry},
      fs1.length = t1.length → TableImpl Γ fs1 t1 → TableImpl Γ fs2 t2 →
      TableImpl Γ (fs1 ++ fs2) (t1 ++ t2)
  | [], _, [], _, _, _, h2 => h2
  | _ :: _, _, [], _, hlen, _, _ => by simp at hlen
  | [], _, _ :: _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _, _ :: _, _, hlen, h1, h2 => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    exact ⟨h1.1, tableImpl_append hlen h1.2 h2⟩

theorem tableImpl_of_forall_zip {Γ : Env} :
    ∀ {fs : List Fn} {tbl : List SpecEntry},
      fs.length = tbl.length →
      (∀ p ∈ List.zip fs tbl, SpecEntry.Impl Γ p.1 p.2) →
      TableImpl Γ fs tbl
  | [], _, _, _ => trivial
  | _ :: _, [], hlen, _ => by simp at hlen
  | fn :: fs, e :: tbl, hlen, h => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    exact ⟨h (fn, e) List.mem_cons_self,
      tableImpl_of_forall_zip hlen (fun p hp => h p (.tail _ hp))⟩

theorem tableImpl_drop_take {Γ : Env} {fs : List Fn} {tbl : List SpecEntry}
    (hlen : fs.length = tbl.length) (h : TableImpl Γ fs tbl) (off n : Nat) :
    TableImpl Γ ((fs.drop off).take n) ((tbl.drop off).take n) := by
  have aux : ∀ (k : Nat) (as : List Fn) (bs : List SpecEntry),
      as.length = bs.length → TableImpl Γ as bs →
      TableImpl Γ (as.drop k) (bs.drop k) := by
    intro k
    induction k with
    | zero => intro as bs _ h'; exact h'
    | succ k ih =>
      intro as bs hl h'
      cases as <;> cases bs
      · trivial
      · simp at hl
      · simp at hl
      · simp only [List.length_cons, Nat.succ.injEq] at hl
        exact ih _ _ hl h'.2
  have aux2 : ∀ (k : Nat) (as : List Fn) (bs : List SpecEntry),
      TableImpl Γ as bs → TableImpl Γ (as.take k) (bs.take k) := by
    intro k
    induction k with
    | zero => intro _ _ _; trivial
    | succ k ih =>
      intro as bs h'
      cases as <;> cases bs
      · trivial
      · trivial
      · exact False.elim h'
      · exact ⟨h'.1, ih _ _ h'.2⟩
  exact aux2 n _ _ (aux off fs tbl hlen h)

private theorem env_ofTable_of_entry_eq {t : List SpecEntry} {e : SpecEntry} {fn : Fn}
    (he : e ∈ t) (hnd : (t.map SpecEntry.name).Nodup)
    (hnm : e.name = fn.name) (has : e.as = fn.as) (hrs : e.rs = fn.rs)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hc : e.cast has hrs xs m Q X) :
    Env.ofTable t fn.name fn.as fn.rs xs m Q X := by
  cases e with
  | mk enm eas ers esp enx =>
    dsimp only at hnm has hrs
    cases hnm; cases has; cases hrs
    exact Env.ofTable_of_mem he hnd hc

private theorem mem_zip_exists_snd {α : Type _} {β : Type _} :
    ∀ {xs : List α} {ys : List β} {x : α}, xs.length = ys.length → x ∈ xs →
      ∃ y, (x, y) ∈ List.zip xs ys
  | [], _, _, _, hx => nomatch hx
  | _ :: _, [], _, hl, _ => by simp at hl
  | _ :: _, b :: _, _, _, .head _ => ⟨b, .head _⟩
  | _ :: _, _ :: _, _, hl, .tail _ hx =>
    let ⟨y, hy⟩ := mem_zip_exists_snd (Nat.succ.inj hl) hx; ⟨y, .tail _ hy⟩

private theorem mem_zip_take_iff {α : Type _} {β : Type _} :
    ∀ (k : Nat) (xs : List α) (ys : List β) (p : α × β),
      p ∈ List.zip (xs.take k) (ys.take k) →
      ∃ i < min k (min xs.length ys.length), xs[i]? = some p.1 ∧ ys[i]? = some p.2
  | 0, _, _, _, h => by simp at h
  | _ + 1, [], _, _, h => by simp at h
  | _ + 1, _, [], _, h => by simp at h
  | k + 1, a :: xs, b :: ys, p, h => by
    simp only [List.take_succ_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, rfl, rfl⟩
    · obtain ⟨i, hi, h1, h2⟩ := mem_zip_take_iff k xs ys p h
      exact ⟨i + 1, by simp at hi ⊢; omega, h1, h2⟩

private theorem nodup_getElem_eq_of_mem_map {α : Type _} {β : Type _} (f : α → β) :
    ∀ {xs : List α} {a1 a2 : α}, (xs.map f).Nodup → a1 ∈ xs → a2 ∈ xs → f a1 = f a2 → a1 = a2
  | [], _, _, _, h, _, _ => nomatch h
  | x :: xs, a1, a2, hnd, h1, h2, heq => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    cases List.mem_cons.mp h1 with
    | inl h1e =>
      cases List.mem_cons.mp h2 with
      | inl h2e => exact h1e.trans h2e.symm
      | inr h2t => exact absurd ⟨a2, h2t, h1e ▸ heq.symm⟩ hnd.1
    | inr h1t =>
      cases List.mem_cons.mp h2 with
      | inl h2e => exact absurd ⟨a1, h1t, h2e ▸ heq⟩ hnd.1
      | inr h2t => exact nodup_getElem_eq_of_mem_map f hnd.2 h1t h2t heq

private theorem nodup_getElem?_inj {α : Type _} :
    ∀ {xs : List α} {i j : Nat} {x : α}, xs.Nodup → xs[i]? = some x → xs[j]? = some x → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | x' :: xs, 0, j + 1, x, hnd, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    simp only [List.getElem?_cons_succ] at hj
    subst hi
    exact absurd (List.mem_of_getElem? hj) (List.nodup_cons.mp hnd).1
  | x' :: xs, i + 1, 0, x, hnd, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    simp only [List.getElem?_cons_succ] at hi
    subst hj
    exact absurd (List.mem_of_getElem? hi) (List.nodup_cons.mp hnd).1
  | _ :: _, i + 1, j + 1, _, hnd, hi, hj =>
    congrArg Nat.succ (nodup_getElem?_inj (List.nodup_cons.mp hnd).2 hi hj)

/-! `nodup_of_map` is inherited from `Proof.Spec.MemBridges`. -/

/-- Pointwise agreement between `Env.ofTable t1` and `Env.ofTable t2` on every signature
whose entry appears in both tables under `Nodup` names. -/
theorem env_ofTable_agree_of_mem_both {t1 t2 : List SpecEntry}
    (hnd1 : (t1.map SpecEntry.name).Nodup) (hnd2 : (t2.map SpecEntry.name).Nodup)
    (allowed : List SigEntry)
    (hall : ∀ s ∈ allowed, ∃ e ∈ t1, e ∈ t2 ∧ (e.name, e.as, e.rs) = s) :
    ∀ f as bs, (f, as, bs) ∈ allowed → ∀ xs m Q X,
      Env.ofTable t1 f as bs xs m Q X ↔ Env.ofTable t2 f as bs xs m Q X := by
  intro f as bs hs xs m Q X
  obtain ⟨e, he1, he2, hsig⟩ := hall (f, as, bs) hs
  rcases e with ⟨enm, eas, ers, esp, enx⟩
  rcases hsig with ⟨rfl, rfl, rfl⟩
  exact ⟨fun h1 => Env.ofTable_of_mem he2 hnd2 (env_ofTable_elim_of_mem he1 hnd1 h1),
    fun h2 => Env.ofTable_of_mem he1 hnd1 (env_ofTable_elim_of_mem he2 hnd2 h2)⟩

/-- Transport an already-proved segment `(fs, sub_tbl)` from `ModuleOk (Env.ofTable t1) M1` into
`TableImpl (Env.ofTable t2) fs sub_tbl` using `wp_env_agree_of_callsOk` and a checked
`allowed` call boundary. -/
theorem tableImpl_transport_of_callsOk {M1 : Module} {t1 t2 : List SpecEntry}
    {fs : List Fn} {sub_tbl : List SpecEntry} {allowed : List SigEntry}
    {exits : List Sym}
    (hM1 : ModuleOk (Env.ofTable t1) M1)
    (hnd1 : (t1.map SpecEntry.name).Nodup) (hnd2 : (t2.map SpecEntry.name).Nodup)
    (hlen : fs.length = sub_tbl.length)
    (hsub : ∀ p ∈ List.zip fs sub_tbl,
      p.1 ∈ M1.fns ∧ p.2 ∈ t1 ∧ p.2 ∈ t2 ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs)
    (hcalls : ∀ fn ∈ fs, fn.checkCallsOk allowed exits = true)
    (hall : ∀ s ∈ allowed, ∃ e ∈ t1, e ∈ t2 ∧ (e.name, e.as, e.rs) = s) :
    AllFns Fn.Wf fs ∧ TableImpl (Env.ofTable t2) fs sub_tbl := by
  have hsound1 : ∀ fn ∈ M1.fns, ∀ xs m Q X,
      Env.ofTable t1 fn.name fn.as fn.rs xs m Q X → Func.wp (Env.ofTable t1) fn.body xs m Q X := by
    intro fn hfn xs m Q X hs
    obtain ⟨pre, post, hsp⟩ := List.append_of_mem hfn
    exact (hM1.fnsOk pre fn post hsp).2.2 xs m Q X hs
  have hwf_fn : ∀ fn ∈ M1.fns, fn.Wf := by
    intro fn hfn
    obtain ⟨pre, post, hsp⟩ := List.append_of_mem hfn
    exact (hM1.fnsOk pre fn post hsp).1
  refine ⟨allFns_of_mem (fun fn hfn => ?_), tableImpl_of_forall_zip hlen ?_⟩
  · obtain ⟨e, he⟩ := mem_zip_exists_snd hlen hfn
    exact hwf_fn fn (hsub (fn, e) he).1
  · intro ⟨fn, e⟩ hmem
    obtain ⟨hfnM1, he1, _, hnm, has, hrs⟩ := hsub (fn, e) hmem
    have hfn_fs : fn ∈ fs := (List.of_mem_zip hmem).1
    have hagree := env_ofTable_agree_of_mem_both hnd1 hnd2 allowed hall
    have hc_ok : fn.callsOk allowed exits := Fn.callsOk_of_checkCallsOk (hcalls fn hfn_fs)
    have hwf := hwf_fn fn hfnM1
    refine ⟨⟨hnm, has, hrs⟩, fun xs m Q X hcast => ?_⟩
    have h1env := env_ofTable_of_entry_eq he1 hnd1 hnm has hrs hcast
    have hwp1 : Func.wp (Env.ofTable t1) fn.body xs m Q X := hsound1 fn hfnM1 xs m Q X h1env
    exact wp_env_agree_of_callsOk (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units _))
      hc_ok (fun f as bs hmem' xs' m' Q' X' hg => (hagree f as bs hmem' xs' m' Q' X').mp hg)
      m hwp1

/-- Convenience wrapper transporting a contiguous prefix `(M1.fns.take k, t1.take k)` from
an already-certified module `M1` with `M1.externs = []` into a larger table `t2` whenever
`t2.take k = t1.take k`. -/
theorem tableImpl_prefix_of_moduleOk {M1 : Module} {t1 t2 : List SpecEntry} (k : Nat)
    (hM1 : ModuleOk (Env.ofTable t1) M1)
    (hexts : M1.externs = [])
    (hsigs1 : t1.map SpecEntry.name = M1.fns.map Fn.name)
    (hsigs_full : ∀ e ∈ t1, ∃ fn ∈ M1.fns, e.name = fn.name ∧ e.as = fn.as ∧ e.rs = fn.rs)
    (hnd1 : (t1.map SpecEntry.name).Nodup) (hnd2 : (t2.map SpecEntry.name).Nodup)
    (hpre_t : t2.take k = t1.take k)
    (hlen1 : M1.fns.length = t1.length)
    (hall_t : ∀ i < min k M1.fns.length, t1[i]? = t2[i]?) :
    AllFns Fn.Wf (M1.fns.take k) ∧ TableImpl (Env.ofTable t2) (M1.fns.take k) (t2.take k) := by
  have hk_zip : ∀ p ∈ List.zip (M1.fns.take k) (t1.take k),
      p.1 ∈ M1.fns ∧ p.2 ∈ t1 ∧ p.2 ∈ t2 ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs := by
    intro ⟨fn, e⟩ hmem
    obtain ⟨i, hi, hfn_i, he_i⟩ := mem_zip_take_iff k M1.fns t1 (fn, e) hmem
    have hi' : i < min k M1.fns.length := by omega
    have ht2_i : t2[i]? = some e := (hall_t i hi').symm.trans he_i
    have hfn_m : fn ∈ M1.fns := List.mem_of_getElem? hfn_i
    have he_m1 : e ∈ t1 := List.mem_of_getElem? he_i
    have he_m2 : e ∈ t2 := List.mem_of_getElem? ht2_i
    obtain ⟨fn', hfn', hnm, has, hrs⟩ := hsigs_full e he_m1
    have h2_name : e.name = fn.name := by
      have hm1 : (t1.map SpecEntry.name)[i]? = some e.name := by simp [he_i]
      have h1_name : (M1.fns.map Fn.name)[i]? = some fn.name := by simp [hfn_i]
      rw [hsigs1] at hm1
      rw [hm1] at h1_name
      exact Option.some.inj h1_name
    have hnd_fns : (M1.fns.map Fn.name).Nodup := (List.nodup_append.mp hM1.nodup).1
    have heq_fn : fn' = fn :=
      nodup_getElem_eq_of_mem_map Fn.name hnd_fns hfn' hfn_m (hnm.symm.trans h2_name)
    subst heq_fn
    exact ⟨hfn_m, he_m1, he_m2, hnm, has, hrs⟩
  have hagree : ∀ (f : Sym) (as bs : List Ty), (f, as, bs) ∈ (M1.fns.take k).map Fn.sig →
      ∀ xs m Q X, Env.ofTable t1 f as bs xs m Q X ↔ Env.ofTable t2 f as bs xs m Q X := by
    intro f as bs hsig xs m Q X
    rw [List.mem_map] at hsig
    obtain ⟨fn, hfn_tk, hsig_eq⟩ := hsig
    simp only [Fn.sig, Prod.mk.injEq] at hsig_eq
    rcases hsig_eq with ⟨rfl, rfl, rfl⟩
    obtain ⟨e, he⟩ := @mem_zip_exists_snd Fn SpecEntry (M1.fns.take k) (t1.take k) fn
      (by simp [hlen1]) hfn_tk
    obtain ⟨_, he1, he2, hnm, has, hrs⟩ := hk_zip (fn, e) he
    cases e with
    | mk enm eas ers esp enx =>
      dsimp only at hnm has hrs
      cases hnm; cases has; cases hrs
      exact ⟨fun h1 => Env.ofTable_of_mem he2 hnd2 (env_ofTable_elim_of_mem he1 hnd1 h1),
        fun h2 => Env.ofTable_of_mem he1 hnd1 (env_ofTable_elim_of_mem he2 hnd2 h2)⟩
  have hwf_tk : AllFns Fn.Wf (M1.fns.take k) :=
    allFns_take (allFns_of_mem fun fn hfn => by
      obtain ⟨pre, post, hsp⟩ := List.append_of_mem hfn; exact (hM1.fnsOk pre fn post hsp).1) k
  refine ⟨hwf_tk, ?_⟩
  rw [hpre_t]
  refine tableImpl_of_forall_zip (by simp [hlen1]) (fun ⟨fn, e⟩ hmem => ?_)
  obtain ⟨hfnM1, he1, _, hnm, has, hrs⟩ := hk_zip (fn, e) hmem
  obtain ⟨pre, post, hsp⟩ := List.append_of_mem hfnM1
  have ⟨hwf, hcalls, hwp⟩ := hM1.fnsOk pre fn post hsp
  have hpre_sub : ∀ s ∈ pre.map Fn.sig ++ M1.externs.map Extern.sig,
      s ∈ (M1.fns.take k).map Fn.sig := by
    intro s hs
    rw [hexts, List.map_nil, List.append_nil, List.mem_map] at hs
    obtain ⟨f', hf', rfl⟩ := hs
    obtain ⟨i, hf'get_pre⟩ := List.mem_iff_getElem?.mp hf'
    have hi : i < pre.length := (List.getElem?_eq_some_iff.mp hf'get_pre).1
    have hf'get : M1.fns[i]? = some f' := by
      rw [hsp, List.getElem?_append_left hi]
      exact hf'get_pre
    have hfn_tk : fn ∈ M1.fns.take k := (List.of_mem_zip hmem).1
    obtain ⟨j', hfn_j'⟩ := List.mem_iff_getElem?.mp hfn_tk
    rw [List.getElem?_take] at hfn_j'
    split at hfn_j'
    · next hjk =>
      have hnd_fns : M1.fns.Nodup :=
        nodup_of_map Fn.name (List.nodup_append.mp hM1.nodup).1
      have hpre_fn : M1.fns[pre.length]? = some fn := by simp [hsp]
      have heq_j : j' = pre.length := nodup_getElem?_inj hnd_fns hfn_j' hpre_fn
      have hi_lt_k : i < k := by omega
      have hf'_tk : (M1.fns.take k)[i]? = some f' := by simp [hi_lt_k, hf'get]
      exact List.mem_map_of_mem (List.mem_of_getElem? hf'_tk)
    · cases hfn_j'
  refine ⟨⟨hnm, has, hrs⟩, fun xs m Q X hcast => ?_⟩
  have h1env := env_ofTable_of_entry_eq he1 hnd1 hnm has hrs hcast
  have hwp1 : Func.wp (Env.ofTable t1) fn.body xs m Q X := hwp xs m Q X h1env
  exact wp_env_agree_of_callsOk (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units _))
    hcalls (fun f as bs hmem' xs' m' Q' X' hg =>
      (hagree f as bs (hpre_sub _ hmem') xs' m' Q' X').mp hg)
    m hwp1

/-- Assemble `ModuleOk (Env.ofTable (t1 ++ t2)) M` from two contiguous segment proofs. -/
theorem moduleOk_of_two_segments {M : Module} {fs1 fs2 : List Fn}
    {t1 t2 : List SpecEntry}
    (hchk : M.checkAcyclic = true)
    (hfns : M.fns = fs1 ++ fs2) (hlen1 : fs1.length = t1.length)
    (hwf1 : AllFns Fn.Wf fs1) (hwf2 : AllFns Fn.Wf fs2)
    (hok1 : TableImpl (Env.ofTable (t1 ++ t2)) fs1 t1)
    (hok2 : TableImpl (Env.ofTable (t1 ++ t2)) fs2 t2) :
    ModuleOk (Env.ofTable (t1 ++ t2)) M :=
  Env.ofTable_moduleOk hchk (hfns ▸ allFns_append hwf1 hwf2)
    (hfns ▸ tableImpl_append hlen1 hok1 hok2)


end LeanQbe.T.Examples.Kissat.Proof.Spec
