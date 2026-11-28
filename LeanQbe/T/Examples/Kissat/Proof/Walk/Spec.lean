/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Walk
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Walk` (`Kissat.Proof.Walk.Spec`)

Canonical UNSAT-sound `CanonicalEnv` specifications (`Spec.XFree`) for all `13` functions in
`LeanQbe.T.Examples.Kissat.Src.Walk.fns` (`WalkSAT`, `warmup`, and `rephase`), with zero legacy
imports:
- `10` inner WalkSAT functions (`full_walk_cb_inv_m7` .. `full_walk_m7`): `FullMem`-threaded
- `3` outer `FullHdr`+M6 functions (`full_warmup_m7`, `full_walk`, `full_rephase`):
  `FullM6HdrMem`-threaded

Imported upstream specs (`deps`):
`Arena`, `Backtrack`, `Decide`, `Dense`, `Float64`, `Forward`, and `PropSearch`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Walk.Spec

open Std.Sat
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Walk Table Invariant & Scratch Prefix Preservation -/

/-- Table-length invariant established by `full_walk_cb_inv_m7` (`tbl[1080] ≤ 1080`) and
required by `full_walk_pick_m7` so `tbl[b]` stays strictly inside `scratch_buf[0..2160)`. -/
@[expose] def WalkTblExpsOk (s : FullState) : Prop :=
  (((s.scratch.scratch_buf[2160]?.getD 0#32).setWidth 64) |||
    (((s.scratch.scratch_buf[2161]?.getD 0#32).setWidth 64) <<< 32)).toNat ≤ 1080

/-- Preservation of the `u64` exponential-table prefix `scratch_buf[0 ..< 2200)`. -/
@[expose] def WalkScrPrefixPres (s s' : FullState) : Prop :=
  ∀ j < 2200, s'.scratch.scratch_buf[j]? = s.scratch.scratch_buf[j]?

/-! ## 2. Upstream Callee Dependency Table (`deps`) -/

/-- Canonical upstream specs imported by `Src.Walk` (`14` externs). -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Decide.Spec.specs ++
    Dense.Spec.specs ++ Float64.Spec.specs ++ Forward.Spec.specs ++
    PropSearch.Spec.specs

/-! ## 3. Canonical Per-Function Specifications (`13` functions, matching `Src.Walk.fns`) -/

/-- `full_walk_cb_inv_m7`: populates `tbl[0..1082]` in `scratch_buf` and establishes
`WalkTblExpsOk` whenever `r ≠ 0`. -/
@[expose] def fullWalkCbInvM7Spec : Spec [i64, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _ncl, _tot, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' => FullExtScratchPres s s' ∧ (r ≠ 0#64 → WalkTblExpsOk s'))

/-- `full_walk_effort_m7`: read-only tick-effort calculation. -/
@[expose] def fullWalkEffortM7Spec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _mf, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s' = s)

/-- `full_walk_init_vals_m7`: initializes `walk_vals` and `walk_best` in `scratch`. -/
@[expose] def fullWalkInitValsM7Spec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

/-- `full_walk_collect_m7`: collects unsatisfied/active clauses into `scratch_buf[2200..]`. -/
@[expose] def fullWalkCollectM7Spec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

/-- `full_walk_build_occ_m7`: preserves `scratch_buf[0..2200)` and returns `ulen ≤ ncl`. -/
@[expose] def fullWalkBuildOccM7Spec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _ncl, ()) _ => h = c.hdr)
    (fun _ (_, ncl, ()) (r, ()) s s' =>
      FullExtScratchPres s s' ∧ WalkScrPrefixPres s s' ∧ r.toNat ≤ ncl.toNat)

/-- `full_walk_break_m7`: read-only break-count computation. -/
@[expose] def fullWalkBreakM7Spec : Spec [i64, i32, i64] [i32] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _nl, _ncl, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s' = s)

/-- `full_walk_pick_m7`: requires & preserves `WalkTblExpsOk` while selecting a literal. -/
@[expose] def fullWalkPickM7Spec : Spec [i64, i32, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _cl, _ncl, ()) s => h = c.hdr ∧ WalkTblExpsOk s)
    (fun _ _ _ s s' => FullExtScratchPres s s' ∧ WalkTblExpsOk s')

/-- `full_walk_flip_m7`: preserves `scratch_buf[0..2200)` and bounds `(r &&& 0xFFFFFFFF) ≤ ncl`. -/
@[expose] def fullWalkFlipM7Spec : Spec [i64, i32, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _fl, _ncl, _ul, ()) _ => h = c.hdr)
    (fun _ (_, _, ncl, _, ()) (r, ()) s s' =>
      FullExtScratchPres s s' ∧ WalkScrPrefixPres s s' ∧ (r &&& 0xFFFFFFFF#64).toNat ≤ ncl.toNat)

/-- `full_walk_save_min_m7`: updates best/target phases and `best_assigned` in `scratch`. -/
@[expose] def fullWalkSaveMinM7Spec : Spec [i64, i64, .bool] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _bp, _ok, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

/-- `full_walk_m7`: `FullSparseInv`-preserving WalkSAT run (via binary watch roundtrip and
large-clause watch reconnection). -/
@[expose] def fullWalkM7Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = s.core.probing →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_warmup_m7`: `FullM6HdrMem`-threaded warmup calling `full_next_dec_var`, `full_assign`,
`full_propagate_beyond_m7`, and `full_backtrack`. -/
@[expose] def fullWarmupM7Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-- `full_walk`: `FullM6HdrMem`-threaded top-level walk (`full_warmup_m7` then `full_walk_m7`). -/
@[expose] def fullWalkM6Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-- `full_rephase`: `FullM6HdrMem`-threaded rephase scheduling phase resets, `full_walk`,
`full_backtrack`, `f64u_nlogpown`, and `f64u_to_u64`. -/
@[expose] def fullRephaseM6Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      (s.scratch.stable ≠ 0#64 → s'.core.cur_level = 0) →
      s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-! ## 4. Canonical Spec Table & Structural Lemmas -/

/-- Canonical spec table for `Src.Walk.fns` (`13` functions, 1:1 order). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_walk_cb_inv_m7",   [i64, i64, i64],     [i64], fullWalkCbInvM7Spec,   true⟩
  , ⟨"full_walk_effort_m7",   [i64, i64],          [i64], fullWalkEffortM7Spec,  true⟩
  , ⟨"full_walk_init_vals_m7",[i64],               [],    fullWalkInitValsM7Spec,true⟩
  , ⟨"full_walk_collect_m7",  [i64],               [i64], fullWalkCollectM7Spec, true⟩
  , ⟨"full_walk_build_occ_m7",[i64, i64],          [i64], fullWalkBuildOccM7Spec,true⟩
  , ⟨"full_walk_break_m7",    [i64, i32, i64],     [i32], fullWalkBreakM7Spec,   true⟩
  , ⟨"full_walk_pick_m7",     [i64, i32, i64],     [i64], fullWalkPickM7Spec,    true⟩
  , ⟨"full_walk_flip_m7",     [i64, i32, i64, i64],[i64], fullWalkFlipM7Spec,    true⟩
  , ⟨"full_walk_save_min_m7", [i64, i64, .bool],   [],    fullWalkSaveMinM7Spec, true⟩
  , ⟨"full_walk_m7",          [i64],               [],    fullWalkM7Spec,        true⟩
  , ⟨"full_warmup_m7",        [i64],               [],    fullWarmupM7Spec,      true⟩
  , ⟨"full_walk",             [i64],               [],    fullWalkM6Spec,        true⟩
  , ⟨"full_rephase",          [i64],               [],    fullRephaseM6Spec,     true⟩
  ]

theorem fullWalkCbInvM7Spec_xfree : Spec.XFree fullWalkCbInvM7Spec := by xfree
theorem fullWalkEffortM7Spec_xfree : Spec.XFree fullWalkEffortM7Spec := by xfree
theorem fullWalkInitValsM7Spec_xfree : Spec.XFree fullWalkInitValsM7Spec := by xfree
theorem fullWalkCollectM7Spec_xfree : Spec.XFree fullWalkCollectM7Spec := by xfree
theorem fullWalkBuildOccM7Spec_xfree : Spec.XFree fullWalkBuildOccM7Spec := by xfree
theorem fullWalkBreakM7Spec_xfree : Spec.XFree fullWalkBreakM7Spec := by xfree
theorem fullWalkPickM7Spec_xfree : Spec.XFree fullWalkPickM7Spec := by xfree
theorem fullWalkFlipM7Spec_xfree : Spec.XFree fullWalkFlipM7Spec := by xfree
theorem fullWalkSaveMinM7Spec_xfree : Spec.XFree fullWalkSaveMinM7Spec := by xfree
theorem fullWalkM7Spec_xfree : Spec.XFree fullWalkM7Spec := by xfree
theorem fullWarmupM7Spec_xfree : Spec.XFree fullWarmupM7Spec := by xfree
theorem fullWalkM6Spec_xfree : Spec.XFree fullWalkM6Spec := by xfree
theorem fullRephaseM6Spec_xfree : Spec.XFree fullRephaseM6Spec := by xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Walk.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : ∀ e ∈ specs, e.noExit = true := by decide

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullWalkCbInvM7Spec_xfree
  · exact fullWalkEffortM7Spec_xfree
  · exact fullWalkInitValsM7Spec_xfree
  · exact fullWalkCollectM7Spec_xfree
  · exact fullWalkBuildOccM7Spec_xfree
  · exact fullWalkBreakM7Spec_xfree
  · exact fullWalkPickM7Spec_xfree
  · exact fullWalkFlipM7Spec_xfree
  · exact fullWalkSaveMinM7Spec_xfree
  · exact fullWalkM7Spec_xfree
  · exact fullWarmupM7Spec_xfree
  · exact fullWalkM6Spec_xfree
  · exact fullRephaseM6Spec_xfree

/-! ## 5. `Env.Sat specs` Projections -/

theorem has_full_walk_cb_inv_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_cb_inv_m7" fullWalkCbInvM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide)) fullWalkCbInvM7Spec_xfree

theorem has_full_walk_effort_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_effort_m7" fullWalkEffortM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide)) fullWalkEffortM7Spec_xfree

theorem has_full_walk_init_vals_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_init_vals_m7" fullWalkInitValsM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide)) fullWalkInitValsM7Spec_xfree

theorem has_full_walk_collect_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_collect_m7" fullWalkCollectM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide)) fullWalkCollectM7Spec_xfree

theorem has_full_walk_build_occ_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_build_occ_m7" fullWalkBuildOccM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide)) fullWalkBuildOccM7Spec_xfree

theorem has_full_walk_break_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_break_m7" fullWalkBreakM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide)) fullWalkBreakM7Spec_xfree

theorem has_full_walk_pick_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_pick_m7" fullWalkPickM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 6) (by decide)) fullWalkPickM7Spec_xfree

theorem has_full_walk_flip_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_flip_m7" fullWalkFlipM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 7) (by decide)) fullWalkFlipM7Spec_xfree

theorem has_full_walk_save_min_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_save_min_m7" fullWalkSaveMinM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 8) (by decide)) fullWalkSaveMinM7Spec_xfree

theorem has_full_walk_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk_m7" fullWalkM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 9) (by decide)) fullWalkM7Spec_xfree

theorem has_full_warmup_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_warmup_m7" fullWarmupM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 10) (by decide)) fullWarmupM7Spec_xfree

theorem has_full_walk {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_walk" fullWalkM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 11) (by decide)) fullWalkM6Spec_xfree

theorem has_full_rephase {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_rephase" fullRephaseM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 12) (by decide)) fullRephaseM6Spec_xfree

/-! ## 6. `_intro` / `_elim` Wrappers for Downstream M6 Consumers -/

theorem fullWalkM7Spec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hinv : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = s.core.probing →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m') :
    fullWalkM7Spec (c.hdr, ()) m Q X :=
  ⟨c, F0, s, R, rfl, hinv, hm, hk⟩

theorem fullWarmupM7Spec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    fullWarmupM7Spec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hm, hk⟩

theorem fullWalkM6Spec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    fullWalkM6Spec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hm, hk⟩

theorem fullRephaseM6Spec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      (s.scratch.stable ≠ 0#64 → s'.core.cur_level = 0) →
      s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    fullRephaseM6Spec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hm, hk⟩

end LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
