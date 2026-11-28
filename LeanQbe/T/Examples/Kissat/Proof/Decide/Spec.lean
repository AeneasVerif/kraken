/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core

/-!
# Canonical Pure Specifications for `Kissat.Src.Decide` (`5` functions)

Pure contract definitions and `specs : List SpecEntry` matching `Src.Decide.fns` 1:1.
Zero theorems, zero tactics, zero `deps`, zero cross-subsystem `Spec` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Decide.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- Preservation of the first `36` `glue_used` words (`M7GuPrefixPres`). -/
@[expose] def GuPrefixPres (s s' : FullState) : Prop :=
  ∀ j < 36, s'.scratch.glue_used[j]? = s.scratch.glue_used[j]?

/-- Valid random-decision candidate: sentinel `-1` or an active unassigned variable. -/
@[expose] def RandecVarOk (s : FullState) (r : BitVec 64) : Prop :=
  r = 0xFFFFFFFFFFFFFFFF#64 ∨
  (r.toNat < s.core.cur_vars ∧
    (s.core.flags[r.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
    s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)

/-- Core-state modification footprint of `full_decide_m7` and `m6_hdr_decide_fid`. -/
@[expose] def DecideCoreMod (s s' : FullState) : Prop :=
  s'.core = { s.core with
    vals := s'.core.vals, flags := s'.core.flags, lvl := s'.core.lvl,
    rsns := s'.core.rsns, trl := s'.core.trl, trail_pos := s'.core.trail_pos,
    frame_trail := s'.core.frame_trail, frame_dec := s'.core.frame_dec,
    trail_end := s'.core.trail_end, cur_level := s'.core.cur_level,
    unassigned := s'.core.unassigned, unflushed := s'.core.unflushed }

/-- Shared postcondition for `full_decide_m7` and `m6_hdr_decide_fid`. -/
@[expose] def DecidePost (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (r : BitVec 64) (s' : FullState) : Prop :=
  DecideCoreMod s s' ∧
  FullCoreInv c F0 s' ∧
  ScratchModifies.extPres s s' ∧
  (r = 0#64 ∨ r = 1#64) ∧
  (r = 0#64 → s'.core.cur_level = s.core.cur_level ∧ s'.core.trail_end = s.core.trail_end) ∧
  (r = 1#64 → s'.core.cur_level = s.core.cur_level + 1 ∧ s'.core.trail_end = s.core.trail_end + 1)

/-- `full_next_dec_var(h)`: picks next unassigned decision variable (VMTF or VSIDS) or `-1`. -/
@[expose] def nextDecVarSpec : Spec [i64] [i64] :=
  FullContract.toSpec (extraArgs := []) (rs := [i64]) (W := Unit) {
    pre := fun _ _ () () => True
    post := fun _ s () () (r, ()) s' =>
      CorePres s s' ∧
      ScratchModifies.extPres s s' ∧
      (r = 0xFFFFFFFFFFFFFFFF#64 ∨
        (r.toNat < s.core.cur_vars ∧ s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8))
  }

/-- `full_randec_var_lvl_fid(h, max_lvl)`: bounded-level random decision variable selection. -/
@[expose] def randecVarLvlSpec : Spec [i64, i64] [i64] :=
  FullContract.toSpec (extraArgs := [i64]) (rs := [i64]) (W := Unit) {
    pre := fun _ _ _ () => True
    post := fun _ s _ () (r, ()) s' =>
      CorePres s s' ∧
      ScratchModifies.extPres s s' ∧
      GuPrefixPres s s' ∧
      RandecVarOk s r
  }

/-- `full_randec_var_m7(h)`: random decision variable selection. -/
@[expose] def randecVarSpec : Spec [i64] [i64] :=
  FullContract.toSpec (extraArgs := []) (rs := [i64]) (W := Unit) {
    pre := fun _ _ () () => True
    post := fun _ s () () (r, ()) s' =>
      CorePres s s' ∧
      ScratchModifies.extPres s s' ∧
      GuPrefixPres s s' ∧
      RandecVarOk s r
  }

/-- `full_decide_m7(h)`: makes one branching decision (`0`: none left, `1`: decided). -/
@[expose] def decideCoreSpec : Spec [i64] [i64] :=
  FullContract.toSpec (extraArgs := []) (rs := [i64]) (W := CNF Nat) {
    pre := fun c s () F0 => FullCoreInv c F0 s
    post := fun c s () F0 (r, ()) s' => DecidePost c F0 s r s'
  }

/-- `m6_hdr_decide_fid(h)`: M6-header-threaded decision wrapper initializing `dr_*`
on `r = 1#64` while preserving W2a tier/watermark words. -/
@[expose] def decideSpec : Spec [i64] [i64] :=
  M6HdrContract.toSpec (extraArgs := []) (rs := [i64]) (W := CNF Nat) {
    extFrame := .any
    pre := fun c _ s () F0 => FullCoreInv c F0 s
    post := fun c ext s () F0 (r, ()) ext' s' =>
      DecidePost c F0 s r s' ∧
      (r = 1#64 → M6HdrExtInitOk ext' ∧ (M6HdrExtInitOk ext → M6ExtW2aPres ext ext'))
  }

/-- Canonical specification table aligned 1:1 with `Src.Decide.fns` (`5` entries). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_next_dec_var",       [i64],      [i64], nextDecVarSpec,   true⟩
  , ⟨"full_randec_var_lvl_fid", [i64, i64], [i64], randecVarLvlSpec, true⟩
  , ⟨"full_randec_var_m7",      [i64],      [i64], randecVarSpec,    true⟩
  , ⟨"full_decide_m7",          [i64],      [i64], decideCoreSpec,   true⟩
  , ⟨"m6_hdr_decide_fid",       [i64],      [i64], decideSpec,       true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
