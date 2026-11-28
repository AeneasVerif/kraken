/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.PropSearch
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical `Spec` Table for `Kissat/Src/PropSearch.lean` (`8` fns)

Canonical UNSAT-sound `Spec` definitions, `deps`, `Spec.XFree` proofs, `specs` table matching
`Src.PropSearch.fns` 1:1 (`noExit := true`), `specs_sigs`, `specs_nodup`, and `Env.Has`
projections (`0` legacy imports, `0` `@[expose]` on theorems/lemmas).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
open LeanQbe.T.Examples.Kissat.Src.PropSearch
open Kraken.Bedrock2.Test

@[expose] public section

/-! ## 1. Watch-Compaction, Delayed-Flush & Trail-Reason Invariants -/

/-- Valid pending delayed-watch entries `del[0 ..< 3 * dlen)`: each triple `(repl, w0, cref)`
targets a literal `repl ≠ skip_lit` within `2 * cur_vars` with valid large-watch words. -/
def DelayedWatchesOk (k : FullCoreState) (del : List (BitVec 32))
    (dlen skip_lit : Nat) : Prop :=
  ∀ j < dlen,
    let repl := (del[3 * j]?.getD 0#32).toNat
    let w0 := del[3 * j + 1]?.getD 0#32
    let cref := del[3 * j + 2]?.getD 0#32
    repl < 2 * k.cur_vars ∧ repl ≠ skip_lit ∧
    (w0 &&& 0x80000000#32) = 0#32 ∧ cref.toNat < 0x80000000 ∧
    cref.toNat ∈ fullArenaClauseRefsCore k

/-- Mid-compaction watch invariant for `full_propagate*`: `not_lit`'s slice `[off, end_v)` is
split into valid compacted prefix `[off, q)` and valid uninspected suffix `[p, end_v)`. -/
structure SplitWatchesInv (F_cur : List (List Nat)) (k : FullCoreState)
    (not_lit off q p end_v : Nat) : Prop where
  layout : WatchStackLayout k
  off_eq : fullWatchOffCore k not_lit = off
  sz_eq : fullWatchSizeCore k not_lit = end_v - off
  sz_pos : 0 < end_v - off
  q_ge : off ≤ q
  q_le_p : q ≤ p
  p_le_end : p ≤ end_v
  other_slices : ∀ l < 2 * k.cur_vars, l ≠ not_lit →
    WatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)
  kept_slice : WatchSliceOk F_cur k not_lit off (q - off)
  rem_slice : WatchSliceOk F_cur k not_lit p (end_v - p)

/-- Trail-prefix reason preservation across BCP (`full_propagate*`): variables already assigned on
`k.trl[0 ..< k.trail_end)` retain their exact `rsns` entries. -/
def FullTrailRsnsPres (k k' : FullCoreState) : Prop :=
  ∀ i < k.trail_end,
    k'.rsns[(k.trl[i]?.getD 0#32).toNat / 2]? = k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?

/-! ## 2. Upstream Extern Dependency Table (`deps`) -/

/-- Canonical upstream specification table covering the `4` `extern` functions declared in
`Src/PropSearch.lean`: `full_watch_push`, `m6_wm4_get`, `m6_hdr_add_ticks`, `full_backtrack`. -/
def deps : List SpecEntry :=
  [ ⟨"full_watch_push",  [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec,   true⟩
  , ⟨"m6_wm4_get",       [i64],                     [i64],   m6Wm4GetSpec,        true⟩
  , ⟨"m6_hdr_add_ticks", [i64, i64],                [],      m6HdrAddTicksSpec,   true⟩
  , ⟨"full_backtrack",   [i64, i64],                [],      fullBacktrackSpec,   true⟩
  ]

/-! ## 3. Canonical Per-Function Specifications (`8` Functions, `7` Distinct Specs) -/

/-- Canonical contract for cold overflow watch-push `full_prop_lit_ovf_hot(h, rw, w0, cref)`. -/
def fullPropLitOvfHotSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, cref, ()) m Q X => fullWatchPushSpec (h, lit, w0, cref, 2#32, ()) m Q X

/-- Canonical contract for cold delayed-watch flush `full_prop_flush_slow_fid(h, j, di)`. -/
def fidPropFlushSlowSpec : Spec [i64, i64, i64] [.bool] :=
  fun (h, j, di, ()) m Q _ =>
    ∃ (c : FullCfg) (F_cur : List (List Nat)) (st : FullState) (R : Mem 64 → Prop)
      (idx dlen skip_lit : Nat),
      h = c.hdr ∧ st.LengthsOk c ∧ WatchStackLayout st.core ∧
      j.toNat = 3 * idx ∧ di.toNat = 3 * dlen ∧ idx < dlen ∧ dlen ≤ c.delayed_cap ∧
      DelayedWatchesOk st.core st.scratch.delayed dlen skip_lit ∧
      (FullMem c st ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wu' wsort' m',
        let st' : FullState :=
          { st with
            core := { st.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
            scratch := { st.scratch with wsort := wsort' } }
        st'.LengthsOk c → WatchStackLayout st'.core →
        (WatchesInv F_cur st.core → WatchesInv F_cur st'.core) →
        (skip_lit < 2 * st.core.cur_vars →
          ∀ off q p end_v, SplitWatchesInv F_cur st.core skip_lit off q p end_v →
            let off' := fullWatchOffCore st'.core skip_lit
            SplitWatchesInv F_cur st'.core skip_lit off'
              (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) →
        (FullMem c st' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for hot delayed-watch flush `full_prop_flush_del_fid(h, di)`. -/
def fidPropFlushDelSpec : Spec [i64, i64] [.bool] :=
  fun (h, di, ()) m Q _ =>
    ∃ (c : FullCfg) (F_cur : List (List Nat)) (st : FullState) (R : Mem 64 → Prop)
      (dlen skip_lit : Nat),
      h = c.hdr ∧ st.LengthsOk c ∧ WatchStackLayout st.core ∧
      di.toNat = 3 * dlen ∧ dlen ≤ c.delayed_cap ∧
      DelayedWatchesOk st.core st.scratch.delayed dlen skip_lit ∧
      (FullMem c st ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wu' wsort' m',
        let st' : FullState :=
          { st with
            core := { st.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
            scratch := { st.scratch with wsort := wsort' } }
        st'.LengthsOk c → WatchStackLayout st'.core →
        (WatchesInv F_cur st.core → WatchesInv F_cur st'.core) →
        (skip_lit < 2 * st.core.cur_vars →
          ∀ off q p end_v, SplitWatchesInv F_cur st.core skip_lit off q p end_v →
            let off' := fullWatchOffCore st'.core skip_lit
            SplitWatchesInv F_cur st'.core skip_lit off'
              (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) →
        (FullMem c st' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical `FullM6HdrMem`-threaded contract for `full_propagate_ignore_hot` and
`full_propagate_ignore`. -/
def propIgnoreM6Spec : Spec [i64, i64] [i64] :=
  fun (h, ignore_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
        wu' fuel' ctype' cref' c0' c1' oom' (sc' : FullScratch) m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
                confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
            scratch := sc' }
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullTrailRsnsPres s.core s'.core →
        FullArenaPermEq s.core s'.core →
        FullProbeScratchPres { s with scratch := { s.scratch with
          search_ticks := sc'.search_ticks, wsort := sc'.wsort,
          phases := sc'.phases, delayed := sc'.delayed } } s' →
        sc'.red_refs = s.scratch.red_refs → sc'.delayed_len = s.scratch.delayed_len →
        (s.core.probing = 0#64 → sc' = { s.scratch with
          search_ticks := sc'.search_ticks, wsort := sc'.wsort,
          phases := sc'.phases, delayed := sc'.delayed }) →
        (c.delayed_cap = 0 → sc'.delayed = s.scratch.delayed) →
        fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
          (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s' ∧
          (ctype' = 2#64 → cref' ≠ ignore_ref)) →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ ext' = ext ∧ s' = s) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical `FullM6HdrMem`-threaded contract for `full_propagate`. -/
def propagateM6Spec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
        wu' fuel' ctype' cref' c0' c1' oom' (sc' : FullScratch) m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
                confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
            scratch := sc' }
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullTrailRsnsPres s.core s'.core →
        FullArenaPermEq s.core s'.core →
        FullProbeScratchPres { s with scratch := { s.scratch with
          search_ticks := sc'.search_ticks, wsort := sc'.wsort,
          phases := sc'.phases, delayed := sc'.delayed } } s' →
        sc'.red_refs = s.scratch.red_refs → sc'.delayed_len = s.scratch.delayed_len →
        (s.core.probing = 0#64 → sc' = { s.scratch with
          search_ticks := sc'.search_ticks, wsort := sc'.wsort,
          phases := sc'.phases, delayed := sc'.delayed }) →
        (c.delayed_cap = 0 → sc'.delayed = s.scratch.delayed) →
        fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ ext' = ext ∧ s' = s) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical `FullM6HdrMem`-threaded contract for `full_flush_trail`: backtracks to root
level, propagates pending units, sets `inconsistent = 1` on root conflict, and clears
`unflushed`/`confl_*` while preserving `FullM6HdrInv`, `FullArenaPermEq`, `FullProbeScratchPres`,
`red_refs`, and `delayed_len`. -/
def flushTrailM6Spec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
        FullProbeScratchPres s s' → s'.scratch.red_refs = s.scratch.red_refs →
        s'.scratch.delayed_len = s.scratch.delayed_len →
        (c.delayed_cap = 0 → s'.scratch.delayed = s.scratch.delayed) →
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (s.core.cur_level = 0 → s'.core.cur_level = 0) →
        (r = 20#64 → F0.Unsat) →
        (r = 1#64 → s'.core.cur_level = 0 ∧ s'.core.propagated = s'.core.trail_end ∧
          s'.core.oom = 0#64 ∧ s'.core.unflushed = 0#64 ∧ s'.core.inconsistent = 0#64 ∧
          (s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
            s'.core.fuel.toNat < s.core.fuel.toNat)) →
        (r ≠ 1#64 → s'.core.cur_level = 0 ∨ s'.core.inconsistent ≠ 0#64) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical `FullM6HdrMem`-threaded contract for `full_propagate_beyond_m7`: warmup BCP that
skips both binary and large conflicts without ever returning `1` or modifying conflict fields. -/
def propagateBeyondM6Spec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
        wu' fuel' oom' (sc' : FullScratch) m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', fuel := fuel', oom := oom' }
            scratch := sc' }
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullTrailRsnsPres s.core s'.core →
        FullArenaPermEq s.core s'.core →
        FullProbeScratchPres { s with scratch := { s.scratch with
          search_ticks := sc'.search_ticks, wsort := sc'.wsort,
          phases := sc'.phases, delayed := sc'.delayed } } s' →
        sc'.red_refs = s.scratch.red_refs → sc'.delayed_len = s.scratch.delayed_len →
        (s.core.probing = 0#64 → sc' = { s.scratch with
          search_ticks := sc'.search_ticks, wsort := sc'.wsort,
          phases := sc'.phases, delayed := sc'.delayed }) →
        (c.delayed_cap = 0 → sc'.delayed = s.scratch.delayed) →
        fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ ext' = ext ∧ s' = s) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical `8`-row specification table aligned 1:1 with `Src.PropSearch.fns`. -/
def specs : List SpecEntry :=
  [ ⟨"full_prop_lit_ovf_hot",     [i64, i32, i32, i32], [.bool], fullPropLitOvfHotSpec,  true⟩
  , ⟨"full_prop_flush_slow_fid",  [i64, i64, i64],      [.bool], fidPropFlushSlowSpec,   true⟩
  , ⟨"full_prop_flush_del_fid",   [i64, i64],           [.bool], fidPropFlushDelSpec,    true⟩
  , ⟨"full_propagate_ignore_hot", [i64, i64],           [i64],   propIgnoreM6Spec,       true⟩
  , ⟨"full_propagate_ignore",     [i64, i64],           [i64],   propIgnoreM6Spec,       true⟩
  , ⟨"full_propagate",            [i64],                [i64],   propagateM6Spec,        true⟩
  , ⟨"full_flush_trail",          [i64],                [i64],   flushTrailM6Spec,       true⟩
  , ⟨"full_propagate_beyond_m7",  [i64],                [i64],   propagateBeyondM6Spec,  true⟩
  ]

end

public section

/-! ## 4. Constructors, Eliminators, `Spec.XFree` & Table Invariants -/

theorem fullPropLitOvfHotSpec_xfree : Spec.XFree fullPropLitOvfHotSpec := by xfree

theorem fidPropFlushSlowSpec_xfree : Spec.XFree fidPropFlushSlowSpec := by xfree

theorem fidPropFlushDelSpec_xfree : Spec.XFree fidPropFlushDelSpec := by xfree

theorem propIgnoreM6Spec_xfree : Spec.XFree propIgnoreM6Spec := by xfree

theorem propagateM6Spec_xfree : Spec.XFree propagateM6Spec := by xfree

theorem flushTrailM6Spec_xfree : Spec.XFree flushTrailM6Spec := by xfree

theorem propagateBeyondM6Spec_xfree : Spec.XFree propagateBeyondM6Spec := by xfree

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullPropLitOvfHotSpec_xfree
  · exact fidPropFlushSlowSpec_xfree
  · exact fidPropFlushDelSpec_xfree
  · exact propIgnoreM6Spec_xfree
  · exact propIgnoreM6Spec_xfree
  · exact propagateM6Spec_xfree
  · exact flushTrailM6Spec_xfree
  · exact propagateBeyondM6Spec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.PropSearch.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

/-! ## 5. `Env.Sat` Projections (`deps` and `specs`) -/

private theorem mem_has_deps {Γ : Env} (h : Γ.Sat deps) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ deps)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem deps_has_full_watch_push {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_watch_push" fullWatchPushSpec :=
  mem_has_deps h (by simp [deps]) (by xfree)

theorem deps_has_m6_wm4_get {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "m6_wm4_get" m6Wm4GetSpec :=
  mem_has_deps h (by simp [deps]) m6Wm4GetSpec_xfree

theorem deps_has_m6_hdr_add_ticks {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "m6_hdr_add_ticks" m6HdrAddTicksSpec :=
  mem_has_deps h (by simp [deps]) m6HdrAddTicksSpec_xfree

theorem deps_has_full_backtrack {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_backtrack" fullBacktrackSpec :=
  mem_has_deps h (by simp [deps]) (by xfree)

private theorem mem_has_specs {Γ : Env} (h : Γ.Sat specs) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ specs)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem has_full_prop_lit_ovf_hot {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_prop_lit_ovf_hot" fullPropLitOvfHotSpec :=
  mem_has_specs h (by simp [specs]) fullPropLitOvfHotSpec_xfree

theorem has_full_prop_flush_slow_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_prop_flush_slow_fid" fidPropFlushSlowSpec :=
  mem_has_specs h (by simp [specs]) fidPropFlushSlowSpec_xfree

theorem has_full_prop_flush_del_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_prop_flush_del_fid" fidPropFlushDelSpec :=
  mem_has_specs h (by simp [specs]) fidPropFlushDelSpec_xfree

theorem has_full_propagate_ignore_hot {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_propagate_ignore_hot" propIgnoreM6Spec :=
  mem_has_specs h (by simp [specs]) propIgnoreM6Spec_xfree

theorem has_full_propagate_ignore {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_propagate_ignore" propIgnoreM6Spec :=
  mem_has_specs h (by simp [specs]) propIgnoreM6Spec_xfree

theorem has_full_propagate {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_propagate" propagateM6Spec :=
  mem_has_specs h (by simp [specs]) propagateM6Spec_xfree

theorem has_full_flush_trail {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_flush_trail" flushTrailM6Spec :=
  mem_has_specs h (by simp [specs]) flushTrailM6Spec_xfree

theorem has_full_propagate_beyond_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_propagate_beyond_m7" propagateBeyondM6Spec :=
  mem_has_specs h (by simp [specs]) propagateBeyondM6Spec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
