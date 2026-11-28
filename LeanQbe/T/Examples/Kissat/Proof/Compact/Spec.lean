/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Compact
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Compact` (`13` C0 Functions)

Pure declarative specifications (`0` theorems, `0` tactics, `0` cross-subsystem `Spec` imports)
aligned 1:1 with `Src.Compact.fns`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Compact.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. Compaction Invariants & `AgreesExcept` Masks -/

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

/-- Pre-remap compacted binary watch slice for old literal `olit` (`< 2 * old_cv`). -/
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

/-- Post-remap binary-only watch slice for new literal `nlit` (`< 2 * ncv`). -/
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

/-- Complete compacted binary-only watch invariant over `[0 ..< 2 * ncv)`. -/
structure CompactUnmapBinsOk (ncv : Nat) (inv : List (BitVec 32))
    (F_cur : List (List Nat)) (k : FullCoreState) : Prop where
  layout : WatchStackLayout k
  empty_hi : ∀ l, 2 * ncv ≤ l → l < 2 * k.cur_vars → fullWatchSizeCore k l = 0
  slices : ∀ l < 2 * ncv,
    CompactUnmapBinSliceOk ncv inv F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)

/-- Compacted large-clause arena invariant under `compactUnmapLit inv`. -/
structure CompactArenaOk (ncv : Nat) (inv : List (BitVec 32))
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

/-- `AgreesExcept` mask for `full_compact_bins`. -/
@[expose] def compactBinsMask (s : FullState) : FullState :=
  { s with core := { s.core with wvec := [], wstk := [], wusable := 0#64, num_binary := 0#64 } }

/-- `AgreesExcept` mask for `full_compact_arena`. -/
@[expose] def compactArenaMask (s : FullState) : FullState :=
  { core := { s.core with
      arena := [], arena_len := 0, arena_garbage := 0#64, first_reducible := 0#64,
      num_irred := 0#64, num_redundant := 0#64, wvec := [], wstk := [], wlen := 0,
      wusable := 0#64, num_binary := 0#64, oom := 0#64 }
    scratch := { s.scratch with last_learned := [], wsort := [] } }

/-- `AgreesExcept` core mask for `full_compact_vars`. -/
@[expose] def compactVarsCoreMask (k : FullCoreState) : FullCoreState :=
  { k with
    vals := [], flags := [], lvl := [], rsns := [], frame_trail := [], frame_dec := [],
    trail_end := 0, propagated := 0, cur_level := 0, unflushed := 0#64,
    confl_ref := 0xFFFFFFFF#64, confl_type := 0#64, cur_vars := 0, unassigned := 0#64 }

/-! ## 2. Factored `Pre` / `Post` Packages -/

/-- Self-contained postcondition for `full_compact_flush` (`6` fields, `0` `PropSearch.Spec`
import). -/
structure CompactFlushPost (c : FullCfg) (F0 : CNF Nat) (ext' : List (BitVec 64))
    (s s' : FullState) (r : BitVec 64) : Prop where
  inv : FullM6HdrInv c F0 ext' s'
  ret_cases : r = 0#64 ∨ r = 1#64 ∨ r = 20#64
  cur_vars_eq : s'.core.cur_vars = s.core.cur_vars
  fuel_le : s'.core.fuel.toNat ≤ s.core.fuel.toNat
  unsat_of_20 : r = 20#64 → F0.Unsat
  ok_post : r = 1#64 → s'.core.cur_level = 0 ∧ s'.core.inconsistent = 0#64

/-- Precondition package for `full_compact_arena` (`11` fields). -/
structure CompactArenaPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ncv : Nat) (s : FullState) (old_cv : BitVec 64) : Prop where
  ext_sound : ExtUnsatSound F0 old_cv.toNat F_cur
  arena_inv : FullArenaClausesInv c F_cur s.core
  nodup : FullArenaVarsNodup s
  dense_zero : s.core.dense_mode = 0#64
  root_level : s.core.cur_level = 0
  cur_vars_eq : s.core.cur_vars = old_cv.toNat
  ncv_le : ncv ≤ old_cv.toNat
  bij : CompactBijOk old_cv.toNat ncv s.core.vals s.scratch.work_stk1 s.scratch.work_stk2
  vals_tri : ∀ l < 2 * old_cv.toNat,
    s.core.vals[l]?.getD 0#8 = 0#8 ∨ s.core.vals[l]?.getD 0#8 = 1#8 ∨
      s.core.vals[l]?.getD 0#8 = 0xFF#8
  false_entails : ∀ l < 2 * old_cv.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1])
  bins_ok : CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur s.core

/-- Postcondition package for `full_compact_arena` (`8` fields). -/
structure CompactArenaPost (F0 : CNF Nat) (F_cur : List (List Nat)) (ncv : Nat)
    (s s' : FullState) (ast : BitVec 64) : Prop where
  frame : AgreesExcept compactArenaMask s s'
  arena_garbage_zero : s'.core.arena_garbage = 0#64
  ret_cases : ast = 0#64 ∨ ast = 2#64 ∨ ast = 3#64
  unsat_of_2 : ast = 2#64 → F0.Unsat
  oom_of_3 : ast = 3#64 → s'.core.oom = 1#64
  bins_ok : CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur s'.core
  arena_ok : CompactArenaOk ncv s.scratch.work_stk2 F_cur s'.core
  last_learned_wf : FullLastLearnedWf s'

/-- Postcondition package for `full_compact_vars` (`10` fields). -/
structure CompactVarsPost (c' : FullCfg) (s s' : FullState) (old_cv ncv : BitVec 64) : Prop where
  core_frame : AgreesExcept compactVarsCoreMask s.core s'.core
  frame_trail_zero : s'.core.frame_trail = s.core.frame_trail.set 0 0#32
  frame_dec_upd : ∃ fd0, s'.core.frame_dec = s.core.frame_dec.set 0 fd0
  trail_reset : s'.core.trail_end = 0 ∧ s'.core.propagated = 0 ∧
    s'.core.cur_level = 0 ∧ s'.core.unflushed = 0#64
  confl_reset : s'.core.confl_ref = 0xFFFFFFFF#64 ∧ s'.core.confl_type = 0#64
  vars_eq : s'.core.cur_vars = ncv.toNat ∧ s'.core.unassigned = ncv
  vals_zero : ∀ l < 2 * c'.max_vars, l < 2 * old_cv.toNat → s'.core.vals[l]?.getD 0#8 = 0#8
  ext_pres : FullExtScratchPres s s'
  work_stk1_eq : s'.scratch.work_stk1 = s.scratch.work_stk1
  work_stk2_eq : s'.scratch.work_stk2 = s.scratch.work_stk2

/-! ## 3. Canonical Per-Function Specifications (`12` Distinct Specs for `13` C0 Functions) -/

/-- `full_compact_needed(h)`: read-only check returning `true` only at root level in sparse mode
with `> 10%` fixed variables. -/
@[expose] def compactNeededSpec : Spec [i64] [.bool] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ s () () => s.core.cur_level < 2 ^ 64
      post := fun _ s () () (res, ()) s' =>
        s' = s ∧
        (res = true → s.core.cur_level = 0 ∧ s.core.dense_mode = 0#64 ∧
          0 < s.core.cur_vars ∧ s.core.unassigned.toNat < s.core.cur_vars ∧
          s.core.cur_vars < 10 * (s.core.cur_vars - s.core.unassigned.toNat)) }

/-- `full_compact_flush(h)`: flushes root-level trail before variable compaction. -/
@[expose] def compactFlushSpec : Spec [i64] [i64] :=
  M6HdrContract.toSpec (W := CNF Nat)
    { extFrame := .w2aOnly
      pre := fun c ext s () F0 => FullM6HdrInv c F0 ext s
      post := fun c _ s () F0 (r, ()) ext' s' => CompactFlushPost c F0 ext' s s' r }

/-- `full_compact_mark_live(h)`: marks live variables in `scratch.work_stk1`. -/
@[expose] def compactMarkLiveSpec : Spec [i64] [] :=
  FullContract.toSpec (W := CNF Nat × List (List Nat))
    { pre := fun c s () (F0, F_cur) => FullSparseInvW c F0 F_cur s
      post := fun c s () (F0, F_cur) () s' =>
        CorePres s s' ∧ ScratchModifies [.work_stk1] s s' ∧ FullSparseInvW c F0 F_cur s' }

/-- `full_compact_assign_map(h)`: builds dense `map`/`inv` bijection in `work_stk1`/`work_stk2`. -/
@[expose] def compactAssignMapSpec : Spec [i64] [i64] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ _ () () => True
      post := fun _ s () () (ncv, ()) s' =>
        CorePres s s' ∧ ScratchModifies [.work_stk1, .work_stk2] s s' ∧
        CompactBijOk s.core.cur_vars ncv.toNat s.core.vals
          s'.scratch.work_stk1 s'.scratch.work_stk2 }

/-- `full_compact_record_ext(h, old_cv, ncv)`: appends level-0 units and variable remap to
`extend_stk`. -/
@[expose] def compactRecordExtSpec : Spec [i64, i64, i64] [.bool] :=
  FullContract.toSpec (W := Unit)
    { pre := fun c s (old_cv, ncv, ()) () =>
        s.core.cur_vars = old_cv.toNat ∧ ncv.toNat ≤ old_cv.toNat ∧
        s.scratch.extend_len ≤ c.extend_cap
      post := fun c s _ () (ok, ()) s' =>
        CorePres s s' ∧ ScratchModifies [.extend_stk, .extend_len] s s' ∧
        s'.scratch.extend_len ≤ c.extend_cap ∧ (ok = false → s' = s) }

/-- `full_compact_bins(h, old_cv, ncv)`: remaps binary watches and establishes
`CompactUnmapBinsOk`. -/
@[expose] def compactBinsSpec : Spec [i64, i64, i64] [] :=
  FullContract.toSpec (W := CNF Nat × List (List Nat))
    { pre := fun c s (old_cv, ncv, ()) (F0, F_cur) =>
        FullSparseInvW c F0 F_cur s ∧ s.core.cur_vars = old_cv.toNat ∧
        ncv.toNat ≤ old_cv.toNat ∧
        CompactBijOk old_cv.toNat ncv.toNat s.core.vals s.scratch.work_stk1 s.scratch.work_stk2
      post := fun _ s (_, ncv, ()) (_, F_cur) () s' =>
        AgreesExcept compactBinsMask s s' ∧
        CompactUnmapBinsOk ncv.toNat s.scratch.work_stk2 F_cur s'.core }

/-- `full_compact_arena(h, old_cv)`: remaps large arena clauses, promoting binaries, returning
`0` (ok), `2` (UNSAT), or `3` (OOM). -/
@[expose] def compactArenaSpec : Spec [i64, i64] [i64] :=
  FullContract.toSpec (W := CNF Nat × List (List Nat) × Nat)
    { pre := fun c s (old_cv, ()) (F0, F_cur, ncv) =>
        CompactArenaPre c F0 F_cur ncv s old_cv
      post := fun _ s _ (F0, F_cur, ncv) (ast, ()) s' =>
        CompactArenaPost F0 F_cur ncv s s' ast }

/-- `full_compact_vars(h, old_cv, ncv)`: compacts per-variable arrays, resets level-0 trail,
and updates `FullCfg` via `FullCfgCompat`. -/
@[expose] def compactVarsSpec : Spec [i64, i64, i64] [] :=
  FullCfgContract.toSpec (W := Unit)
    { pre := fun _ s (old_cv, ncv, ()) () =>
        s.core.cur_vars = old_cv.toNat ∧ ncv.toNat ≤ old_cv.toNat ∧
        (∀ nv < ncv.toNat, (s.scratch.work_stk2[nv]?.getD 0#32).toNat < old_cv.toNat)
      post := fun _ s (old_cv, ncv, ()) () () c' s' =>
        CompactVarsPost c' s s' old_cv ncv }

/-- `full_compact_sift_q(qs, ws, start, n)`: max-heap sift-down by `q_stamp`. -/
@[expose] def compactSiftQSpec : Spec [i64, i64, i64, i64] [] :=
  FnContract.toSpec (W := List (BitVec 32) × List (BitVec 32)) (W' := List (BitVec 32))
    { pre := fun (_, _, start, n, ()) (qs, ws) =>
        start.toNat < n.toNat ∧ n.toNat ≤ ws.length ∧ n.toNat < 2 ^ 62 ∧
        (∀ k < n.toNat, (ws[k]?.getD 0#32).toNat < qs.length)
      mem := fun (qsp, wsp, _, _, ()) (qs, ws) =>
        array (t := i32) qsp qs ⋆ array (t := i32) wsp ws
      post := fun (_, _, _, n, ()) (_, ws) () ws' =>
        ws'.length = ws.length ∧ (∀ k, n.toNat ≤ k → ws'[k]? = ws[k]?) ∧
        (∀ k < n.toNat, ∃ j < n.toNat, ws'[k]? = ws[j]?)
      postMem := fun (qsp, wsp, _, _, ()) (qs, _) () ws' =>
        array (t := i32) qsp qs ⋆ array (t := i32) wsp ws' }

/-- Shared contract for `full_compact_vmtf(h, ncv)` and `full_compact_heap(h, ncv)`: rebuilds
search heuristic structures over `[0 ..< ncv)` while preserving `core`, `ext`, and `work_stk1/2`. -/
@[expose] def compactHeurSpec : Spec [i64, i64] [] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ s (ncv, ()) () => ncv.toNat ≤ s.core.cur_vars
      post := fun _ s _ () () s' =>
        CorePres s s' ∧ FullExtScratchPres s s' ∧
        s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
        s'.scratch.work_stk2 = s.scratch.work_stk2 }

/-- `full_compact_sift_h(sc, hp, ps, start, n)`: max-heap sift-down by EVSIDS `score`. -/
@[expose] def compactSiftHSpec : Spec [i64, i64, i64, i64, i64] [] :=
  FnContract.toSpec (W := List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
      (W' := List (BitVec 32) × List (BitVec 32))
    { pre := fun (_, _, _, start, n, ()) (sc, hp, ps) =>
        start.toNat < n.toNat ∧ n.toNat ≤ hp.length ∧ n.toNat ≤ ps.length ∧ n.toNat < 2 ^ 62 ∧
        (∀ k < n.toNat,
          (hp[k]?.getD 0#32).toNat < sc.length ∧ (hp[k]?.getD 0#32).toNat < ps.length)
      mem := fun (scp, hpp, psp, _, _, ()) (sc, hp, ps) =>
        array64 scp sc ⋆ array (t := i32) hpp hp ⋆ array (t := i32) psp ps
      post := fun (_, _, _, _, n, ()) (_, hp, ps) () (hp', ps') =>
        hp'.length = hp.length ∧ ps'.length = ps.length ∧
        (∀ k, n.toNat ≤ k → hp'[k]? = hp[k]?) ∧
        (∀ k < n.toNat, ∃ j < n.toNat, hp'[k]? = hp[j]?)
      postMem := fun (scp, hpp, psp, _, _, ()) (sc, _, _) () (hp', ps') =>
        array64 scp sc ⋆ array (t := i32) hpp hp' ⋆ array (t := i32) psp ps' }

/-- `full_compact(h)`: top-level variable compaction preserving `FullM6HdrInv` and UNSAT
soundness under `FullCfgCompat`. -/
@[expose] def compactSpec : Spec [i64] [i64] :=
  M6HdrCfgContract.toSpec (W := CNF Nat)
    { extFrame := .any
      pre := fun c ext s () F0 => FullM6HdrInv c F0 ext s
      post := fun _ _ s () F0 (r, ()) c' ext' s' =>
        FullM6HdrInv c' F0 ext' s' ∧ (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        s'.core.cur_vars ≤ s.core.cur_vars ∧ s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (r = 20#64 → F0.Unsat) ∧ (r = 1#64 → s'.core.cur_level = 0) }

/-- Canonical `13`-row specification table aligned 1:1 with `Src.Compact.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_compact_needed",     [i64],                     [.bool], compactNeededSpec,    true⟩
  , ⟨"full_compact_flush",      [i64],                     [i64],   compactFlushSpec,     true⟩
  , ⟨"full_compact_mark_live",  [i64],                     [],      compactMarkLiveSpec,  true⟩
  , ⟨"full_compact_assign_map", [i64],                     [i64],   compactAssignMapSpec, true⟩
  , ⟨"full_compact_record_ext", [i64, i64, i64],           [.bool], compactRecordExtSpec, true⟩
  , ⟨"full_compact_bins",       [i64, i64, i64],           [],      compactBinsSpec,      true⟩
  , ⟨"full_compact_arena",      [i64, i64],                [i64],   compactArenaSpec,     true⟩
  , ⟨"full_compact_vars",       [i64, i64, i64],           [],      compactVarsSpec,      true⟩
  , ⟨"full_compact_sift_q",     [i64, i64, i64, i64],      [],      compactSiftQSpec,     true⟩
  , ⟨"full_compact_vmtf",       [i64, i64],                [],      compactHeurSpec,      true⟩
  , ⟨"full_compact_sift_h",     [i64, i64, i64, i64, i64], [],      compactSiftHSpec,     true⟩
  , ⟨"full_compact_heap",       [i64, i64],                [],      compactHeurSpec,      true⟩
  , ⟨"full_compact",            [i64],                     [i64],   compactSpec,          true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
