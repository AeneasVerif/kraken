/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Compact` (`13` Functions)

Defines compaction invariants (`CompactBijOk`, `CompactPreBinSliceOk`, `CompactUnmapBinSliceOk`,
`CompactUnmapBinsOk`, `CompactArenaOk`), the external dependency bundle `deps`, canonical
specifications for all `13` functions of `Src.Compact.fns` (with `FullM6HdrMem`-threaded
contracts for `full_compact_flush` and `full_compact` matching Step-13 Option-A), `Spec.XFree`
proofs (`0` SAT/model proofs, `noExit = true`), the 1:1 `specs` table, and `Γ.Has` projections.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact.Spec

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Compaction Invariants & Literal Unmapping -/

/-- Unmaps a compacted literal `l` using inverse variable table `inv` (`inv[v] = old_v`). -/
@[expose] def compactUnmapLit (inv : List (BitVec 32)) (l : Nat) : Nat :=
  2 * (inv[l / 2]?.getD 0#32).toNat + l % 2

/-- Bijection between surviving variables `[0 ..< ncv)` and unfixed variables in `[0 ..< old_cv)`
stored in `map` (`work_stk1`) and `inv` (`work_stk2`). -/
structure CompactBijOk (old_cv ncv : Nat) (vals : List (BitVec 8))
    (map inv : List (BitVec 32)) : Prop where
  ncv_le : ncv ≤ old_cv
  old_cv_lt : old_cv < 0x7FFFFFFF
  map_ok : ∀ ov < old_cv,
    map[ov]? = some 0xFFFFFFFF#32 ∨
    ∃ nv < ncv, nv ≤ ov ∧ vals[2 * ov]?.getD 0#8 = 0#8 ∧
      map[ov]? = some (BitVec.ofNat 32 nv) ∧ inv[nv]? = some (BitVec.ofNat 32 ov)
  inv_ok : ∀ nv < ncv,
    ∃ ov < old_cv, nv ≤ ov ∧ vals[2 * ov]?.getD 0#8 = 0#8 ∧
      inv[nv]? = some (BitVec.ofNat 32 ov) ∧ map[ov]? = some (BitVec.ofNat 32 nv)

/-- Pre-remap compacted binary watch slice for old literal `olit` (`< 2 * old_cv`), holding after
loop 1 of `full_compact_bins` before `wvec` entries are compacted and packed. -/
inductive CompactPreBinSliceOk (ncv : Nat) (inv : List (BitVec 32))
    (F_cur : List (List Nat)) (k : FullCoreState) (olit : Nat) : Nat → Nat → Prop where
  | empty {p} : CompactPreBinSliceOk ncv inv F_cur k olit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * ncv →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [olit, compactUnmapLit inv (w0 &&& 0x7FFFFFFF#32).toNat]) →
      CompactPreBinSliceOk ncv inv F_cur k olit (p + 1) rem →
      CompactPreBinSliceOk ncv inv F_cur k olit p (rem + 1)

/-- Post-remap binary-only watch slice for new literal `nlit` (`< 2 * ncv`), where every entry
`(w0 &&& 0x7FFFFFFF)` unmaps back to a binary clause entailed by `F_cur`. -/
inductive CompactUnmapBinSliceOk (ncv : Nat) (inv : List (BitVec 32))
    (F_cur : List (List Nat)) (k : FullCoreState) (nlit : Nat) : Nat → Nat → Prop where
  | empty {p} : CompactUnmapBinSliceOk ncv inv F_cur k nlit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * ncv →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [compactUnmapLit inv nlit,
          compactUnmapLit inv (w0 &&& 0x7FFFFFFF#32).toNat]) →
      CompactUnmapBinSliceOk ncv inv F_cur k nlit (p + 1) rem →
      CompactUnmapBinSliceOk ncv inv F_cur k nlit p (rem + 1)

/-- Complete compacted binary-only watch invariant over `[0 ..< 2 * ncv)`, with emptied `[2 * ncv
..< 2 * k.cur_vars)` slices and disjoint layout. -/
structure CompactUnmapBinsOk (ncv : Nat) (inv : List (BitVec 32))
    (F_cur : List (List Nat)) (k : FullCoreState) : Prop where
  layout : WatchStackLayout k
  empty_hi : ∀ l, 2 * ncv ≤ l → l < 2 * k.cur_vars →
    fullWatchSizeCore k l = 0
  slices : ∀ l < 2 * ncv,
    CompactUnmapBinSliceOk ncv inv F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)

/-- Compacted large-clause arena invariant (`no_shrk`, `no_garb`, `lits_lt` in `2 * ncv`,
`nodup` variables, and clause entailment under `compactUnmapLit inv`). -/
structure CompactArenaOk (_c : FullCfg) (ncv : Nat) (inv : List (BitVec 32))
    (F_cur : List (List Nat)) (k : FullCoreState) : Prop where
  len_ok : k.arena_len = 0 ∨ 3 ≤ k.arena_len
  refs_wf : ∀ r ∈ fullArenaClauseRefsCore k,
    r + 3 ≤ k.arena_len ∧ 3 ≤ fullArenaClauseSizeCore k r ∧
    r + 3 + fullArenaClauseSizeCore k r ≤ fullArenaNextOff k.arena k.arena_len r ∧
    fullArenaNextOff k.arena k.arena_len r ≤ k.arena_len ∧
    (fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r + 3 ≤ k.arena_len)
  no_shrk : ∀ r ∈ fullArenaClauseRefsCore k, (fullArenaHdrCore k r &&& 0x00800000#32) = 0#32
  no_garb : ∀ r ∈ fullArenaClauseRefsCore k, (fullArenaHdrCore k r &&& 0x00080000#32) = 0#32
  lits_lt : ∀ r ∈ fullArenaClauseRefsCore k, ∀ l ∈ fullArenaClauseLitsCore k r, l < 2 * ncv
  nodup : ∀ r ∈ fullArenaClauseRefsCore k, ((fullArenaClauseLitsCore k r).map (· / 2)).Nodup
  entails : ∀ r ∈ fullArenaClauseRefsCore k,
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLitsCore k r).map (compactUnmapLit inv)))

/-! ## 2. Specifications for All `13` Functions of `Kissat.Src.Compact` -/

/-- Canonical specification for `full_compact_needed`: read-only check returning `true` only at
root level in sparse mode with `10 * (cur_vars - unassigned) > cur_vars`. -/
@[expose] def fullCompactNeededSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ res : Bool,
      (res = true → s.core.cur_level = 0 ∧ s.core.dense_mode = 0#64 ∧
        0 < s.core.cur_vars ∧ s.core.unassigned.toNat < s.core.cur_vars ∧
        s.core.cur_vars < 10 * (s.core.cur_vars - s.core.unassigned.toNat)) →
      Q (res, ()) m

/-- Canonical `FullM6HdrMem`-threaded specification for `full_compact_flush` (`full_flush_trail`
alias matching Step-13 Option-A). -/
abbrev fullCompactFlushSpec : Spec [i64] [i64] :=
  Proof.PropSearch.Spec.flushTrailM6Spec

/-- Canonical specification for `full_compact_mark_live`: updates only `scratch.work_stk1`,
preserving `FullSparseInvW` and `LengthsOk`. -/
@[expose] def fullCompactMarkLiveSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ ws1' m',
      let s' : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
      FullSparseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q () m'

/-- Canonical specification for `full_compact_assign_map`: assigns dense variable indices `0 ..<
ncv` in `work_stk1` (`map`) and `work_stk2` (`inv`), returning `ncv` and establishing
`CompactBijOk`. -/
@[expose] def fullCompactAssignMapSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ncv : BitVec 64) (ws1 ws2 : List (BitVec 32)) m',
      let s' : FullState := { s with scratch := { s.scratch with work_stk1 := ws1,
                                                                 work_stk2 := ws2 } }
      s'.LengthsOk c → CompactBijOk s.core.cur_vars ncv.toNat s.core.vals ws1 ws2 →
      (FullMem c s' ⋆ R) m' → Q (ncv, ()) m'

/-- Canonical specification for `full_compact_record_ext`: records level-0 units and variable
remapping in `extend_stk`, updating only `extend_stk` and `extend_len` within capacity. -/
@[expose] def fullCompactRecordExtSpec : Spec [i64, i64, i64] [.bool] :=
  fun (h, old_cv, ncv, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_vars = old_cv.toNat ∧
      ncv.toNat ≤ old_cv.toNat ∧ s.scratch.extend_len ≤ c.extend_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) (ext' : List (BitVec 32)) (elen' : Nat) m',
        let s' : FullState :=
          { s with scratch := { s.scratch with extend_stk := ext', extend_len := elen' } }
        s'.LengthsOk c → elen' ≤ c.extend_cap →
        (ok = false → ext' = s.scratch.extend_stk ∧ elen' = s.scratch.extend_len) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical specification for `full_compact_bins`: compacts binary watch slices in `wvec`/`wstk`
and establishes `CompactUnmapBinsOk`. -/
@[expose] def fullCompactBinsSpec : Spec [i64, i64, i64] [] :=
  fun (h, old_cv, ncv, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_vars = old_cv.toNat ∧
      ncv.toNat ≤ old_cv.toNat ∧
      CompactBijOk old_cv.toNat ncv.toNat s.core.vals s.scratch.work_stk1 s.scratch.work_stk2 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ wvec' wstk' wu' nb' m',
        let s' : FullState :=
          { s with core := { s.core with wvec := wvec', wstk := wstk',
                                           wusable := wu', num_binary := nb' } }
        s'.LengthsOk c → CompactUnmapBinsOk ncv.toNat s.scratch.work_stk2 F_cur s'.core →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Canonical specification for `full_compact_arena`: compacts large clauses in the arena, pushing
strengthened binaries onto `wstk`, returning status `0` (ok), `2` (UNSAT), or `3` (OOM). -/
@[expose] def fullCompactArenaSpec : Spec [i64, i64] [i64] := fun (h, old_cv, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ncv : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ ExtUnsatSound F0 old_cv.toNat F_cur ∧
    FullArenaClausesInv c F_cur s.core ∧ FullArenaVarsNodup s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 0 ∧ s.core.cur_vars = old_cv.toNat ∧ ncv ≤ old_cv.toNat ∧
    CompactBijOk old_cv.toNat ncv s.core.vals s.scratch.work_stk1 s.scratch.work_stk2 ∧
    (∀ l < 2 * old_cv.toNat,
      s.core.vals[l]?.getD 0#8 = 0#8 ∨ s.core.vals[l]?.getD 0#8 = 1#8 ∨
        s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ l < 2 * old_cv.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1])) ∧
    CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur s.core ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ast ar' al' fred' ni' nr' wvec' wstk' wlen' wu' nb' oom' ll' ws' m',
      let s' : FullState :=
        { core := { s.core with arena := ar', arena_len := al', arena_garbage := 0#64,
                                first_reducible := fred', num_irred := ni', num_redundant := nr',
                                wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                                num_binary := nb', oom := oom' }
          scratch := { s.scratch with last_learned := ll', wsort := ws' } }
      s'.LengthsOk c → (ast = 0#64 ∨ ast = 2#64 ∨ ast = 3#64) → (ast = 2#64 → F0.Unsat) →
      (ast = 3#64 → oom' = 1#64) → CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur s'.core →
      CompactArenaOk c ncv s.scratch.work_stk2 F_cur s'.core → FullLastLearnedWf s' →
      (FullMem c s' ⋆ R) m' → Q (ast, ()) m'

/-- Canonical specification for `full_compact_vars`: compacts per-variable arrays from `old_cv` to
`ncv`, resets level-0 trail state, and shrinks `d.mv` / `bva_cap` via `FullCfgCompat`. -/
@[expose] def fullCompactVarsSpec : Spec [i64, i64, i64] [] :=
  fun (h, old_cv, ncv, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_vars = old_cv.toNat ∧
      ncv.toNat ≤ old_cv.toNat ∧
      (∀ nv < ncv.toNat, (s.scratch.work_stk2[nv]?.getD 0#32).toNat < old_cv.toNat) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ c' vals' fl' lvl' rsns' ft0 fd0 sc' m',
        let s' : FullState :=
          { core := { s.core with vals := vals', flags := fl', lvl := lvl', rsns := rsns',
                                  frame_trail := s.core.frame_trail.set 0 ft0,
                                  frame_dec := s.core.frame_dec.set 0 fd0,
                                  trail_end := 0, propagated := 0, cur_level := 0,
                                  unflushed := 0#64, confl_ref := 0xFFFFFFFF#64,
                                  confl_type := 0#64, cur_vars := ncv.toNat, unassigned := ncv }
            scratch := sc' }
        FullCfgCompat c c' → s'.LengthsOk c' → ft0.toNat = 0 →
        (∀ l < 2 * c'.max_vars, l < 2 * old_cv.toNat → vals'[l]?.getD 0#8 = 0#8) →
        FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
        sc'.work_stk2 = s.scratch.work_stk2 → (FullMem c' s' ⋆ R) m' → Q () m'

/-- Canonical specification for `full_compact_sift_q`: max-heap sift-down by `q_stamp`. -/
@[expose] def fullCompactSiftQSpec : Spec [i64, i64, i64, i64] [] :=
  fun (qs_ptr, ws_ptr, start, n, ()) m Q _ =>
    ∃ (qs ws : List (BitVec 32)) (R : Mem 64 → Prop),
      start.toNat < n.toNat ∧ n.toNat ≤ ws.length ∧ n.toNat < 2 ^ 62 ∧
      (∀ k < n.toNat, (ws[k]?.getD 0#32).toNat < qs.length) ∧
      (array (t := i32) qs_ptr qs ⋆ array (t := i32) ws_ptr ws ⋆ R) m ∧
      ∀ ws' m',
        ws'.length = ws.length → (∀ k, n.toNat ≤ k → ws'[k]? = ws[k]?) →
        (∀ k < n.toNat, ∃ j < n.toNat, ws'[k]? = ws[j]?) →
        (array (t := i32) qs_ptr qs ⋆ array (t := i32) ws_ptr ws' ⋆ R) m' → Q () m'

/-- Canonical specification for `full_compact_vmtf`: rebuilds VMTF doubly-linked queue over
compacted variables `[0 ..< ncv)` using `wsort` and `full_compact_sift_q`. -/
@[expose] def fullCompactVmtfSpec : Spec [i64, i64] [] := fun (h, ncv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ ncv.toNat ≤ s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ sc' m',
      let s' : FullState := { s with scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → (FullMem c s' ⋆ R) m' → Q () m'

/-- Canonical specification for `full_compact_sift_h`: max-heap sift-down by `score`, updating
`heap` and `pos`. -/
@[expose] def fullCompactSiftHSpec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (sc_ptr, hp_ptr, ps_ptr, start, n, ()) m Q _ =>
    ∃ (sc : List (BitVec 64)) (hp ps : List (BitVec 32)) (R : Mem 64 → Prop),
      start.toNat < n.toNat ∧ n.toNat ≤ hp.length ∧ n.toNat ≤ ps.length ∧ n.toNat < 2 ^ 62 ∧
      (∀ k < n.toNat,
        (hp[k]?.getD 0#32).toNat < sc.length ∧ (hp[k]?.getD 0#32).toNat < ps.length) ∧
      (array64 sc_ptr sc ⋆ array (t := i32) hp_ptr hp ⋆ array (t := i32) ps_ptr ps ⋆ R) m ∧
      ∀ hp' ps' m',
        hp'.length = hp.length → ps'.length = ps.length →
        (∀ k, n.toNat ≤ k → hp'[k]? = hp[k]?) →
        (∀ k < n.toNat, ∃ j < n.toNat, hp'[k]? = hp[j]?) →
        (array64 sc_ptr sc ⋆ array (t := i32) hp_ptr hp' ⋆
          array (t := i32) ps_ptr ps' ⋆ R) m' → Q () m'

/-- Canonical specification for `full_compact_heap`: rebuilds EVSIDS binary heap over compacted
variables `[0 ..< ncv)` using `full_compact_sift_h`. -/
@[expose] def fullCompactHeapSpec : Spec [i64, i64] [] := fun (h, ncv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ ncv.toNat ≤ s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ sc' m',
      let s' : FullState := { s with scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → (FullMem c s' ⋆ R) m' → Q () m'

/-- Canonical `FullM6HdrMem`-threaded specification for `full_compact` matching Step-13 Option-A
(`step13CompactM6Spec`). -/
@[expose] def fullCompactSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r c' ext' s' m',
      FullCfgCompat c c' → FullM6HdrInv c' F0 ext' s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars ≤ s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. `XFree` Proofs & Canonical Segment Bundle -/

theorem fullCompactNeededSpec_xfree : Spec.XFree fullCompactNeededSpec := by xfree
theorem fullCompactFlushSpec_xfree : Spec.XFree fullCompactFlushSpec := by xfree
theorem fullCompactMarkLiveSpec_xfree : Spec.XFree fullCompactMarkLiveSpec := by xfree
theorem fullCompactAssignMapSpec_xfree : Spec.XFree fullCompactAssignMapSpec := by xfree
theorem fullCompactRecordExtSpec_xfree : Spec.XFree fullCompactRecordExtSpec := by xfree
theorem fullCompactBinsSpec_xfree : Spec.XFree fullCompactBinsSpec := by xfree
theorem fullCompactArenaSpec_xfree : Spec.XFree fullCompactArenaSpec := by xfree
theorem fullCompactVarsSpec_xfree : Spec.XFree fullCompactVarsSpec := by xfree
theorem fullCompactSiftQSpec_xfree : Spec.XFree fullCompactSiftQSpec := by xfree
theorem fullCompactVmtfSpec_xfree : Spec.XFree fullCompactVmtfSpec := by xfree
theorem fullCompactSiftHSpec_xfree : Spec.XFree fullCompactSiftHSpec := by xfree
theorem fullCompactHeapSpec_xfree : Spec.XFree fullCompactHeapSpec := by xfree
theorem fullCompactSpec_xfree : Spec.XFree fullCompactSpec := by xfree

/-- External specifications required by `Kissat.Src.Compact`. -/
@[expose] def deps : List SpecEntry :=
  Proof.Arena.Spec.specs ++ Proof.Collect.Spec.specs ++
  Proof.PropSearch.Spec.specs ++ Proof.Watch.Spec.specs

/-- Canonical `SpecEntry` list matching `Src.Compact.fns` order 1:1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_compact_needed", [i64], [.bool], fullCompactNeededSpec, true⟩
  , ⟨"full_compact_flush", [i64], [i64], fullCompactFlushSpec, true⟩
  , ⟨"full_compact_mark_live", [i64], [], fullCompactMarkLiveSpec, true⟩
  , ⟨"full_compact_assign_map", [i64], [i64], fullCompactAssignMapSpec, true⟩
  , ⟨"full_compact_record_ext", [i64, i64, i64], [.bool], fullCompactRecordExtSpec, true⟩
  , ⟨"full_compact_bins", [i64, i64, i64], [], fullCompactBinsSpec, true⟩
  , ⟨"full_compact_arena", [i64, i64], [i64], fullCompactArenaSpec, true⟩
  , ⟨"full_compact_vars", [i64, i64, i64], [], fullCompactVarsSpec, true⟩
  , ⟨"full_compact_sift_q", [i64, i64, i64, i64], [], fullCompactSiftQSpec, true⟩
  , ⟨"full_compact_vmtf", [i64, i64], [], fullCompactVmtfSpec, true⟩
  , ⟨"full_compact_sift_h", [i64, i64, i64, i64, i64], [], fullCompactSiftHSpec, true⟩
  , ⟨"full_compact_heap", [i64, i64], [], fullCompactHeapSpec, true⟩
  , ⟨"full_compact", [i64], [i64], fullCompactSpec, true⟩ ]

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullCompactNeededSpec_xfree
  · exact fullCompactFlushSpec_xfree
  · exact fullCompactMarkLiveSpec_xfree
  · exact fullCompactAssignMapSpec_xfree
  · exact fullCompactRecordExtSpec_xfree
  · exact fullCompactBinsSpec_xfree
  · exact fullCompactArenaSpec_xfree
  · exact fullCompactVarsSpec_xfree
  · exact fullCompactSiftQSpec_xfree
  · exact fullCompactVmtfSpec_xfree
  · exact fullCompactSiftHSpec_xfree
  · exact fullCompactHeapSpec_xfree
  · exact fullCompactSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Compact.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem has_full_compact_needed {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_needed" fullCompactNeededSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide))
    fullCompactNeededSpec_xfree

theorem has_full_compact_flush {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_flush" fullCompactFlushSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide))
    fullCompactFlushSpec_xfree

theorem has_full_compact_mark_live {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_mark_live" fullCompactMarkLiveSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide))
    fullCompactMarkLiveSpec_xfree

theorem has_full_compact_assign_map {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_assign_map" fullCompactAssignMapSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide))
    fullCompactAssignMapSpec_xfree

theorem has_full_compact_record_ext {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_record_ext" fullCompactRecordExtSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide))
    fullCompactRecordExtSpec_xfree

theorem has_full_compact_bins {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_bins" fullCompactBinsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide))
    fullCompactBinsSpec_xfree

theorem has_full_compact_arena {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_arena" fullCompactArenaSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 6) (by decide))
    fullCompactArenaSpec_xfree

theorem has_full_compact_vars {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_vars" fullCompactVarsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 7) (by decide))
    fullCompactVarsSpec_xfree

theorem has_full_compact_sift_q {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_sift_q" fullCompactSiftQSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 8) (by decide))
    fullCompactSiftQSpec_xfree

theorem has_full_compact_vmtf {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_vmtf" fullCompactVmtfSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 9) (by decide))
    fullCompactVmtfSpec_xfree

theorem has_full_compact_sift_h {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_sift_h" fullCompactSiftHSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 10) (by decide))
    fullCompactSiftHSpec_xfree

theorem has_full_compact_heap {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact_heap" fullCompactHeapSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 11) (by decide))
    fullCompactHeapSpec_xfree

theorem has_full_compact {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_compact" fullCompactSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 12) (by decide))
    fullCompactSpec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
