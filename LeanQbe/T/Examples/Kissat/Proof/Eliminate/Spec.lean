/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Extend.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Eliminate
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical `Spec` Table for `Kissat/Src/Eliminate.lean` (`16` Functions)

Canonical UNSAT-sound `XFree` specifications (`0` legacy `Full*` imports, `0` `@[expose]` on
theorems/lemmas/sections, `XPost`-polymorphic) for all `16` functions in `Src.Eliminate.fns`,
with upstream `deps`, `specs` alignment (`specs_sigs`, `specs_nodup`, `specs_noExit`,
`specs_xfree`), `_intro`/`_elim` wrappers, and `Env.Has` projections (`deps_has_*`, `has_*`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open LeanQbe.T.Examples.Kissat.Src.Eliminate
open Kraken.Bedrock2.Test

public section

/-! ## 1. Upstream Dependency Table (`deps`) -/

/-- Canonical upstream specifications supplying the `23` `extern` callees in `Src.Eliminate`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Clause.Spec.specs ++
  Definition.Spec.specs ++ Dense.Spec.specs ++ Extend.Spec.specs ++
  Float64.Spec.specs ++ Forward.Spec.specs ++ Internal.Spec.specs ++
  Limits.Spec.specs ++ Watch.Spec.specs

/-! ## 2. Canonical Per-Function Specifications (`16` Functions) -/

/-- Canonical contract for `full_bve_collect_m7`: reuses `Proof.Spec.fullBveCollectSpec`. -/
abbrev fullBveCollectM7Spec : Spec [i64, i32, i64, i32] [i32] :=
  Proof.Spec.fullBveCollectSpec

/-- Canonical contract for `full_bve_resolve_pair`: reuses `Proof.Spec.fullBveResolvePairSpec`. -/
abbrev fullBveResolvePairSpec : Spec [i64, i32, i32, i32] [.bool] :=
  Proof.Spec.fullBveResolvePairSpec

/-- Canonical `TmkZero`-preserving contract for `full_bve_weaken` and
`full_bve_weaken_unit_fid`. -/
@[expose] def fullBveWeakenTmkSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, blk_lit, off, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧
      blk_lit.toNat < 2 * s.core.cur_vars ∧ off.toNat + cnt.toNat ≤ c.scratch_cap ∧
      (∀ i < cnt.toNat,
        FullBveWeakItemOk s.core (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.scratch_buf = s.scratch.scratch_buf →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical `TmkZero`-preserving contract for `full_bve_commit_res`. -/
@[expose] def fullBveCommitResTmkSpec : Spec [i64, i64, i64] [i64] :=
  fun (h, r_off, r_end, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧
      r_off.toNat ≤ r_end.toNat ∧ r_end.toNat ≤ c.scratch_cap ∧
      FullResBufOkW F_cur s r_end.toNat r_off.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical contract for `full_bve_ext_need`: reuses `Proof.Spec.fullBveExtNeedSpec`. -/
abbrev fullBveExtNeedSpec : Spec [i64, i32, i32] [i64] :=
  Proof.Spec.fullBveExtNeedSpec

/-- Canonical contract for `full_bve_var_m7`: dense-mode BVE on variable `v`. -/
@[expose] def fullBveVarM7Spec : Spec [i64, i32] [i64] := fun (h, v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ TmkZero s ∧ v.toNat < s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) s' m',
      FullDenseInv c F0 s' → TmkZero s' →
      s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical read-only contract for `full_bve_var_key_m7`. -/
@[expose] def fullBveVarKeyM7Spec : Spec [i64, i32] [i64] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64, Q (r, ()) m

/-- Canonical contract for `full_bve_heap_up_m7`: updates `work_stk1` preserving length. -/
@[expose] def fullBveHeapUpM7Spec : Spec [i64, i64, i32] [] := fun (h, _hlen, _pos, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q () m'

/-- Canonical contract for `full_bve_heap_down_m7`: updates `work_stk1` preserving length. -/
@[expose] def fullBveHeapDownM7Spec : Spec [i64, i64, i32] [] :=
  fun (h, _hlen, _pos, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ ws1' m',
        ws1'.length = 2 * c.max_vars →
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
        Q () m'

/-- Canonical contract for `full_bve_heap_push_m7`: updates `work_stk1` and `sim_sig`. -/
@[expose] def fullBveHeapPushM7Spec : Spec [i64, i64, i32] [i64] :=
  fun (h, hlen, _v, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
      ∀ hlen' ws1' ss' m',
        ws1'.length = 2 * c.max_vars → ss'.length = c.max_vars →
        (hlen.toNat ≤ s.core.cur_vars → hlen'.toNat ≤ s.core.cur_vars) →
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } ⋆
          R) m' →
        Q (hlen', ()) m'

/-- Canonical contract for `full_bve_heap_pop_m7`: pops max candidate updating `work_stk1`. -/
@[expose] def fullBveHeapPopM7Spec : Spec [i64, i64] [i32] := fun (h, _hlen, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 32) ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q (r, ()) m'

/-- Canonical contract for `full_bve_collect_nbrs_m7`: collects neighbor variables into
`work_stk2[0 ..< nn)` using `min_clr` deduplication. -/
@[expose] def fullBveCollectNbrsM7Spec : Spec [i64, i32] [i64] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (nn : BitVec 64) mclr' ws2' m',
      let s' : FullState :=
        { s with
          core := { s.core with min_clr := mclr' }
          scratch := { s.scratch with work_stk2 := ws2' } }
      s'.LengthsOk c → nn.toNat ≤ s.core.cur_vars →
      (∀ i < nn.toNat, (ws2'[i]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (nn, ()) m'

/-- Canonical contract for `full_elim_bve_m7`: dense-mode BVE round driver returning
`1#64` or `20#64` (`F0.Unsat`). -/
@[expose] def fullElimBveM7Spec : Spec [i64, i64] [i64] := fun (h, _lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) s' m',
      FullDenseInv c F0 s' → TmkZero s' →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical read-only contract for `full_has_elim_cands_fid`. -/
@[expose] def fullHasElimCandsFidSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ ok : Bool, Q (ok, ()) m

/-- Canonical `FullM6HdrMem`-threaded Step-13 contract for `full_eliminate_m6`. -/
@[expose] def fullEliminateM6Spec : Spec [i64, .bool] [i64] := fun (h, _initial, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' →
      s'.core.cur_level = 0 → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. Canonical `SpecEntry` Table (`16` Rows, Aligned 1:1 with `Src.Eliminate.fns`) -/

/-- Canonical `16`-row specification table aligned 1:1 with `Src.Eliminate.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_bve_collect_m7",      [i64, i32, i64, i32], [i32],   fullBveCollectM7Spec,    true⟩
  , ⟨"full_bve_resolve_pair",    [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec,  true⟩
  , ⟨"full_bve_weaken",          [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec,    true⟩
  , ⟨"full_bve_commit_res",      [i64, i64, i64],      [i64],   fullBveCommitResTmkSpec, true⟩
  , ⟨"full_bve_ext_need",        [i64, i32, i32],      [i64],   fullBveExtNeedSpec,      true⟩
  , ⟨"full_bve_weaken_unit_fid", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec,    true⟩
  , ⟨"full_bve_var_m7",          [i64, i32],           [i64],   fullBveVarM7Spec,        true⟩
  , ⟨"full_bve_var_key_m7",      [i64, i32],           [i64],   fullBveVarKeyM7Spec,     true⟩
  , ⟨"full_bve_heap_up_m7",      [i64, i64, i32],      [],      fullBveHeapUpM7Spec,     true⟩
  , ⟨"full_bve_heap_down_m7",    [i64, i64, i32],      [],      fullBveHeapDownM7Spec,   true⟩
  , ⟨"full_bve_heap_push_m7",    [i64, i64, i32],      [i64],   fullBveHeapPushM7Spec,   true⟩
  , ⟨"full_bve_heap_pop_m7",     [i64, i64],           [i32],   fullBveHeapPopM7Spec,    true⟩
  , ⟨"full_bve_collect_nbrs_m7", [i64, i32],           [i64],   fullBveCollectNbrsM7Spec, true⟩
  , ⟨"full_elim_bve_m7",         [i64, i64],           [i64],   fullElimBveM7Spec,       true⟩
  , ⟨"full_has_elim_cands_fid",  [i64],                [.bool], fullHasElimCandsFidSpec, true⟩
  , ⟨"full_eliminate_m6",        [i64, .bool],         [i64],   fullEliminateM6Spec,     true⟩
  ]

/-! ## 4. `Spec.XFree`, Constructors, Eliminators & Table Invariants -/

theorem fullBveCollectM7Spec_xfree : Spec.XFree fullBveCollectM7Spec := by xfree
theorem fullBveResolvePairSpec_xfree : Spec.XFree fullBveResolvePairSpec := by xfree
theorem fullBveWeakenTmkSpec_xfree : Spec.XFree fullBveWeakenTmkSpec := by xfree
theorem fullBveCommitResTmkSpec_xfree : Spec.XFree fullBveCommitResTmkSpec := by xfree
theorem fullBveExtNeedSpec_xfree : Spec.XFree fullBveExtNeedSpec := by xfree
theorem fullBveVarM7Spec_xfree : Spec.XFree fullBveVarM7Spec := by xfree
theorem fullBveVarKeyM7Spec_xfree : Spec.XFree fullBveVarKeyM7Spec := by xfree
theorem fullBveHeapUpM7Spec_xfree : Spec.XFree fullBveHeapUpM7Spec := by xfree
theorem fullBveHeapDownM7Spec_xfree : Spec.XFree fullBveHeapDownM7Spec := by xfree
theorem fullBveHeapPushM7Spec_xfree : Spec.XFree fullBveHeapPushM7Spec := by xfree
theorem fullBveHeapPopM7Spec_xfree : Spec.XFree fullBveHeapPopM7Spec := by xfree
theorem fullBveCollectNbrsM7Spec_xfree : Spec.XFree fullBveCollectNbrsM7Spec := by xfree
theorem fullElimBveM7Spec_xfree : Spec.XFree fullElimBveM7Spec := by xfree
theorem fullHasElimCandsFidSpec_xfree : Spec.XFree fullHasElimCandsFidSpec := by xfree
theorem fullEliminateM6Spec_xfree : Spec.XFree fullEliminateM6Spec := by xfree

theorem fullBveWeakenTmkSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {blk_lit off cnt : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hblk : blk_lit.toNat < 2 * s.core.cur_vars) (hcap : off.toNat + cnt.toNat ≤ c.scratch_cap)
    (hitems : ∀ i < cnt.toNat,
      FullBveWeakItemOk s.core (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveWeakenTmkSpec (h, blk_lit, off, cnt, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hblk, hcap, hitems, hm, hQ⟩

theorem fullBveWeakenTmkSpec_elim {h : BitVec 64} {blk_lit off cnt : BitVec 32} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost} (hs : fullBveWeakenTmkSpec (h, blk_lit, off, cnt, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧
      blk_lit.toNat < 2 * s.core.cur_vars ∧ off.toNat + cnt.toNat ≤ c.scratch_cap ∧
      (∀ i < cnt.toNat,
        FullBveWeakItemOk s.core (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.scratch_buf = s.scratch.scratch_buf →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' :=
  hs

theorem fullBveCommitResTmkSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h r_off r_end : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hle : r_off.toNat ≤ r_end.toNat) (hend : r_end.toNat ≤ c.scratch_cap)
    (hbuf : FullResBufOkW F_cur s r_end.toNat r_off.toNat) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fullBveCommitResTmkSpec (h, r_off, r_end, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hle, hend, hbuf, hm, hQ⟩

theorem fullBveCommitResTmkSpec_elim {h r_off r_end : BitVec 64} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hs : fullBveCommitResTmkSpec (h, r_off, r_end, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧
      r_off.toNat ≤ r_end.toNat ∧ r_end.toNat ≤ c.scratch_cap ∧
      FullResBufOkW F_cur s r_end.toNat r_off.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullBveVarM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hden : FullDenseInv c F0 s) (htmk : TmkZero s)
    (hv : v.toNat < s.core.cur_vars) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) s' m',
      FullDenseInv c F0 s' → TmkZero s' →
      s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fullBveVarM7Spec (h, v, ()) m Q X :=
  ⟨c, F0, s, R, hh, hden, htmk, hv, hm, hQ⟩

theorem fullBveVarM7Spec_elim {h : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hs : fullBveVarM7Spec (h, v, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInv c F0 s ∧ TmkZero s ∧ v.toNat < s.core.cur_vars ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInv c F0 s' → TmkZero s' →
        s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullBveVarKeyM7Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core)
    (hm : (FullMem c s ⋆ R) m) (hQ : ∀ r : BitVec 64, Q (r, ()) m) :
    fullBveVarKeyM7Spec (h, v, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hlay, hm, hQ⟩

theorem fullBveVarKeyM7Spec_elim {h : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hs : fullBveVarKeyM7Spec (h, v, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
      ∀ r : BitVec 64, Q (r, ()) m :=
  hs

theorem fullBveHeapUpM7Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h hlen : BitVec 64} {pos : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlenOk : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q () m') :
    fullBveHeapUpM7Spec (h, hlen, pos, ()) m Q X :=
  ⟨c, s, R, hh, hlenOk, hm, hQ⟩

theorem fullBveHeapUpM7Spec_elim {h hlen : BitVec 64} {pos : BitVec 32} {m : Mem 64}
    {Q : Post []} {X : XPost} (hs : fullBveHeapUpM7Spec (h, hlen, pos, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ ws1' m',
        ws1'.length = 2 * c.max_vars →
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
        Q () m' :=
  hs

theorem fullBveHeapDownM7Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h hlen : BitVec 64} {pos : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlenOk : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q () m') :
    fullBveHeapDownM7Spec (h, hlen, pos, ()) m Q X :=
  ⟨c, s, R, hh, hlenOk, hm, hQ⟩

theorem fullBveHeapDownM7Spec_elim {h hlen : BitVec 64} {pos : BitVec 32} {m : Mem 64}
    {Q : Post []} {X : XPost} (hs : fullBveHeapDownM7Spec (h, hlen, pos, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ ws1' m',
        ws1'.length = 2 * c.max_vars →
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
        Q () m' :=
  hs

theorem fullBveHeapPushM7Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h hlen : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hlenOk : s.LengthsOk c) (hlay : WatchStackLayout s.core)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ hlen' ws1' ss' m',
      ws1'.length = 2 * c.max_vars → ss'.length = c.max_vars →
      (hlen.toNat ≤ s.core.cur_vars → hlen'.toNat ≤ s.core.cur_vars) →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } ⋆
        R) m' →
      Q (hlen', ()) m') :
    fullBveHeapPushM7Spec (h, hlen, v, ()) m Q X :=
  ⟨c, s, R, hh, hlenOk, hlay, hm, hQ⟩

theorem fullBveHeapPushM7Spec_elim {h hlen : BitVec 64} {v : BitVec 32} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : fullBveHeapPushM7Spec (h, hlen, v, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
      ∀ hlen' ws1' ss' m',
        ws1'.length = 2 * c.max_vars → ss'.length = c.max_vars →
        (hlen.toNat ≤ s.core.cur_vars → hlen'.toNat ≤ s.core.cur_vars) →
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } ⋆
          R) m' →
        Q (hlen', ()) m' :=
  hs

theorem fullBveHeapPopM7Spec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h hlen : BitVec 64} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hlenOk : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 32) ws1' m',
      ws1'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q (r, ()) m') :
    fullBveHeapPopM7Spec (h, hlen, ()) m Q X :=
  ⟨c, s, R, hh, hlenOk, hm, hQ⟩

theorem fullBveHeapPopM7Spec_elim {h hlen : BitVec 64} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hs : fullBveHeapPopM7Spec (h, hlen, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) ws1' m',
        ws1'.length = 2 * c.max_vars →
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
        Q (r, ()) m' :=
  hs

theorem fullBveCollectNbrsM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {h : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]}
    {X : XPost}
    (hh : h = c.hdr) (hden : FullDenseInv c F0 s) (htmk : TmkZero s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (nn : BitVec 64) mclr' ws2' m',
      let s' : FullState :=
        { s with
          core := { s.core with min_clr := mclr' }
          scratch := { s.scratch with work_stk2 := ws2' } }
      s'.LengthsOk c → nn.toNat ≤ s.core.cur_vars →
      (∀ i < nn.toNat, (ws2'[i]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (nn, ()) m') :
    fullBveCollectNbrsM7Spec (h, v, ()) m Q X :=
  ⟨c, F0, s, R, hh, hden, htmk, hm, hQ⟩

theorem fullBveCollectNbrsM7Spec_elim {h : BitVec 64} {v : BitVec 32} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : fullBveCollectNbrsM7Spec (h, v, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInv c F0 s ∧ TmkZero s ∧ (FullMem c s ⋆ R) m ∧
      ∀ (nn : BitVec 64) mclr' ws2' m',
        let s' : FullState :=
          { s with
            core := { s.core with min_clr := mclr' }
            scratch := { s.scratch with work_stk2 := ws2' } }
        s'.LengthsOk c → nn.toNat ≤ s.core.cur_vars →
        (∀ i < nn.toNat, (ws2'[i]?.getD 0#32).toNat < s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q (nn, ()) m' :=
  hs

theorem fullElimBveM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    {h lim : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hden : FullDenseInv c F0 s) (htmk : TmkZero s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) s' m',
      FullDenseInv c F0 s' → TmkZero s' →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fullElimBveM7Spec (h, lim, ()) m Q X :=
  ⟨c, F0, s, R, hh, hden, htmk, hm, hQ⟩

theorem fullElimBveM7Spec_elim {h lim : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullElimBveM7Spec (h, lim, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInv c F0 s ∧ TmkZero s ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInv c F0 s' → TmkZero s' →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullHasElimCandsFidSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ok : Bool, Q (ok, ()) m) :
    fullHasElimCandsFidSpec (h, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hm, hQ⟩

theorem fullHasElimCandsFidSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hs : fullHasElimCandsFidSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ ok : Bool, Q (ok, ()) m :=
  hs

theorem fullEliminateM6Spec_intro {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {initial : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hinv : FullM6HdrInv c F0 ext s) (hcl : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' →
      s'.core.cur_level = 0 → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullEliminateM6Spec (h, initial, ()) m Q X :=
  ⟨c, F0, ext, s, R, hh, hinv, hcl, hm, hQ⟩

theorem fullEliminateM6Spec_elim {h : BitVec 64} {initial : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : fullEliminateM6Spec (h, initial, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        FullM6HdrInv c F0 ext' s' →
        s'.core.cur_level = 0 → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact fullBveCollectM7Spec_xfree
  · exact fullBveResolvePairSpec_xfree
  · exact fullBveWeakenTmkSpec_xfree
  · exact fullBveCommitResTmkSpec_xfree
  · exact fullBveExtNeedSpec_xfree
  · exact fullBveWeakenTmkSpec_xfree
  · exact fullBveVarM7Spec_xfree
  · exact fullBveVarKeyM7Spec_xfree
  · exact fullBveHeapUpM7Spec_xfree
  · exact fullBveHeapDownM7Spec_xfree
  · exact fullBveHeapPushM7Spec_xfree
  · exact fullBveHeapPopM7Spec_xfree
  · exact fullBveCollectNbrsM7Spec_xfree
  · exact fullElimBveM7Spec_xfree
  · exact fullHasElimCandsFidSpec_xfree
  · exact fullEliminateM6Spec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Eliminate.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

/-! ## 5. `Env.Sat` Projections (`specs` and `deps`) -/

private theorem mem_has_specs {Γ : Env} (h : Γ.Sat specs) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ specs)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem has_full_bve_collect_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_collect_m7" fullBveCollectM7Spec :=
  mem_has_specs h (by simp [specs]) fullBveCollectM7Spec_xfree

theorem has_full_bve_resolve_pair {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_resolve_pair" fullBveResolvePairSpec :=
  mem_has_specs h (by simp [specs]) fullBveResolvePairSpec_xfree

theorem has_full_bve_weaken {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_weaken" fullBveWeakenTmkSpec :=
  mem_has_specs h (by simp [specs]) fullBveWeakenTmkSpec_xfree

theorem has_full_bve_commit_res {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_commit_res" fullBveCommitResTmkSpec :=
  mem_has_specs h (by simp [specs]) fullBveCommitResTmkSpec_xfree

theorem has_full_bve_ext_need {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_ext_need" fullBveExtNeedSpec :=
  mem_has_specs h (by simp [specs]) fullBveExtNeedSpec_xfree

theorem has_full_bve_weaken_unit_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_weaken_unit_fid" fullBveWeakenTmkSpec :=
  mem_has_specs h (by simp [specs]) fullBveWeakenTmkSpec_xfree

theorem has_full_bve_var_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_var_m7" fullBveVarM7Spec :=
  mem_has_specs h (by simp [specs]) fullBveVarM7Spec_xfree

theorem has_full_bve_var_key_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_var_key_m7" fullBveVarKeyM7Spec :=
  mem_has_specs h (by simp [specs]) fullBveVarKeyM7Spec_xfree

theorem has_full_bve_heap_up_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_heap_up_m7" fullBveHeapUpM7Spec :=
  mem_has_specs h (by simp [specs]) fullBveHeapUpM7Spec_xfree

theorem has_full_bve_heap_down_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_heap_down_m7" fullBveHeapDownM7Spec :=
  mem_has_specs h (by simp [specs]) fullBveHeapDownM7Spec_xfree

theorem has_full_bve_heap_push_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_heap_push_m7" fullBveHeapPushM7Spec :=
  mem_has_specs h (by simp [specs]) fullBveHeapPushM7Spec_xfree

theorem has_full_bve_heap_pop_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_heap_pop_m7" fullBveHeapPopM7Spec :=
  mem_has_specs h (by simp [specs]) fullBveHeapPopM7Spec_xfree

theorem has_full_bve_collect_nbrs_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_collect_nbrs_m7" fullBveCollectNbrsM7Spec :=
  mem_has_specs h (by simp [specs]) fullBveCollectNbrsM7Spec_xfree

theorem has_full_elim_bve_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_elim_bve_m7" fullElimBveM7Spec :=
  mem_has_specs h (by simp [specs]) fullElimBveM7Spec_xfree

theorem has_full_has_elim_cands_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_has_elim_cands_fid" fullHasElimCandsFidSpec :=
  mem_has_specs h (by simp [specs]) fullHasElimCandsFidSpec_xfree

theorem has_full_eliminate_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_eliminate_m6" fullEliminateM6Spec :=
  mem_has_specs h (by simp [specs]) fullEliminateM6Spec_xfree

private theorem deps_sat_split {Γ : Env} (h : Γ.Sat deps) :
    Γ.Sat Arena.Spec.specs ∧ Γ.Sat Backtrack.Spec.specs ∧ Γ.Sat Clause.Spec.specs ∧
    Γ.Sat Definition.Spec.specs ∧ Γ.Sat Dense.Spec.specs ∧ Γ.Sat Extend.Spec.specs ∧
    Γ.Sat Float64.Spec.specs ∧ Γ.Sat Forward.Spec.specs ∧ Γ.Sat Internal.Spec.specs ∧
    Γ.Sat Limits.Spec.specs ∧ Γ.Sat Watch.Spec.specs := by
  simpa only [deps, Env.Sat.append_iff, and_assoc] using h

theorem deps_has_full_alloc_cl {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_alloc_cl" fullAllocClSpec :=
  Arena.Spec.has_full_alloc_cl (deps_sat_split h).1

theorem deps_has_full_assign_lvl {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_assign_lvl" fullAssignLvlSpec :=
  Backtrack.Spec.has_full_assign_lvl (deps_sat_split h).2.1

theorem deps_has_full_add_bin {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_add_bin" fullAddBinSpec :=
  Clause.Spec.has_full_add_bin (deps_sat_split h).2.2.1

theorem deps_has_full_add_unit {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_add_unit" fullAddUnitSpec :=
  Clause.Spec.has_full_add_unit (deps_sat_split h).2.2.1

theorem deps_has_full_bve_gates_m7 {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_bve_gates_m7" Definition.Spec.fullBveGatesM7Spec :=
  Definition.Spec.has_full_bve_gates_m7 (deps_sat_split h).2.2.2.1

theorem deps_has_full_bve_gates_fid {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_bve_gates_fid" Definition.Spec.m8BveGatesSpec :=
  Definition.Spec.has_full_bve_gates_fid (deps_sat_split h).2.2.2.1

theorem deps_has_full_dense_occ_cnt_fid {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_dense_occ_cnt_fid" Dense.Spec.fullDenseOccCntSpec :=
  Dense.Spec.has_full_dense_occ_cnt_fid (deps_sat_split h).2.2.2.2.1

theorem deps_has_full_enter_dense_ex_fid {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_enter_dense_ex_fid" Dense.Spec.fullEnterDenseExM6Spec :=
  Dense.Spec.has_full_enter_dense_ex_fid (deps_sat_split h).2.2.2.2.1

theorem deps_has_full_rebuild_watches {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_rebuild_watches" Dense.Spec.fullRebuildWatchesM6Spec :=
  Dense.Spec.has_full_rebuild_watches (deps_sat_split h).2.2.2.2.1

theorem deps_has_full_dense_flush_units_m7 {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_dense_flush_units_m7" Dense.Spec.fullDenseFlushUnitsSpec :=
  Dense.Spec.has_full_dense_flush_units_m7 (deps_sat_split h).2.2.2.2.1

theorem deps_has_full_extend_push2 {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_extend_push2" Extend.Spec.fullExtendPush2Spec :=
  Env.Sat.has (deps_sat_split h).2.2.2.2.2.1
    (List.getElem_mem (l := Extend.Spec.specs) (n := 0) (by decide)) (by xfree)

theorem deps_has_full_extend_push_cl {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_extend_push_cl" Extend.Spec.fullExtendPushClSpec :=
  Env.Sat.has (deps_sat_split h).2.2.2.2.2.1
    (List.getElem_mem (l := Extend.Spec.specs) (n := 1) (by decide)) (by xfree)

theorem deps_has_f64u_mul {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec :=
  Env.Sat.has (deps_sat_split h).2.2.2.2.2.2.1
    (List.getElem_mem (l := Float64.Spec.specs) (n := 4) (by decide))
    Float64.Spec.f64uPure2Spec_xfree

theorem deps_has_f64u_to_u64 {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "f64u_to_u64" Float64.Spec.f64uPure1Spec :=
  Env.Sat.has (deps_sat_split h).2.2.2.2.2.2.1
    (List.getElem_mem (l := Float64.Spec.specs) (n := 8) (by decide))
    Float64.Spec.f64uPure1Spec_xfree

theorem deps_has_f64u_nlogpown {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "f64u_nlogpown" Float64.Spec.f64uPure2Spec :=
  Env.Sat.has (deps_sat_split h).2.2.2.2.2.2.1
    (List.getElem_mem (l := Float64.Spec.specs) (n := 11) (by decide))
    Float64.Spec.f64uPure2Spec_xfree

theorem deps_has_full_forward_sub_m7 {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_forward_sub_m7" Forward.Spec.fullForwardSubM7Spec :=
  Forward.Spec.has_full_forward_sub_m7 (deps_sat_split h).2.2.2.2.2.2.2.1

theorem deps_has_full_set_inactive {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_set_inactive" Internal.Spec.fullSetInactiveSpec :=
  Internal.Spec.has_full_set_inactive (deps_sat_split h).2.2.2.2.2.2.2.2.1

theorem deps_has_full_update_classify_fid {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_update_classify_fid" Internal.Spec.fullUpdateClassifyFidSpec :=
  Internal.Spec.has_full_update_classify_fid (deps_sat_split h).2.2.2.2.2.2.2.2.1

theorem deps_has_full_scale_delta {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_scale_delta" Limits.Spec.schedScaleDeltaSpec :=
  Env.Sat.has (deps_sat_split h).2.2.2.2.2.2.2.2.2.1
    (List.getElem_mem (l := Limits.Spec.specs) (n := 5) (by decide)) (by xfree)

theorem deps_has_full_elim_dticks {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_elim_dticks" Limits.Spec.schedElimDticksSpec :=
  Env.Sat.has (deps_sat_split h).2.2.2.2.2.2.2.2.2.1
    (List.getElem_mem (l := Limits.Spec.specs) (n := 9) (by decide)) (by xfree)

theorem deps_has_full_wstack_defrag {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_wstack_defrag" fullWstackDefragSpec :=
  Watch.Spec.has_full_wstack_defrag (deps_sat_split h).2.2.2.2.2.2.2.2.2.2

theorem deps_has_full_watch_push {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_watch_push" fullWatchPushSpec :=
  Watch.Spec.has_full_watch_push (deps_sat_split h).2.2.2.2.2.2.2.2.2.2

theorem deps_has_full_delete_binary {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_delete_binary" Watch.Spec.fullDeleteBinarySpec :=
  Watch.Spec.has_full_delete_binary (deps_sat_split h).2.2.2.2.2.2.2.2.2.2

end

end LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
