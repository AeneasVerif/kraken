/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Parse.Tumble
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Parse
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Parse` (`Proof.Parse.Spec`)

Canonical `SegCert` specifications for all `5` functions in `Src.Parse.fns`:
- `full_activate_lit_fid` (`fullActivateLitFidSpec`, `FullMem`)
- `full_ingest_cl` (`fullIngestClTumSpec`, `FullMem`)
- `full_tumble_finish_fid` (`fullTumbleFinishFidSpec`, `FullMem`)
- `full_parse_body_m6` (`fullParseBodyM6Spec`, Step-13 Option-A `FullM6HdrMem`-threaded)
- `full_parse_body` (`fullParseBodyM6Spec`, Step-13 Option-A `FullM6HdrMem`-threaded)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Parse.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Parse
open LeanQbe.T.Examples.Kissat.Src.Parse
open Kraken.Bedrock2.Test

/-- S11-3 lazy activation helper `full_activate_lit_fid(h, v)`: mutates `core.flags`,
`core.unassigned`, and non-extend scratch fields while preserving `FullExtScratchPres`. -/
@[expose] def fullActivateLitFidSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' unass' sc' m',
      let s' : FullState :=
        { core := { s.core with flags := flags', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c →
      FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Tumble + lazy-activation clause ingestion `full_ingest_cl(h, cnf_end)`. -/
@[expose] def fullIngestClTumSpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (accCnf : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    let tum := decide (c.mv < c.extend_cap)
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    s.core.cur_vars = c.mv ∧ s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.core.cur_level = 0 ∧
    TumbleInv tum c.mv s.scratch.extend_len s.core.frame_dec ∧
    TumbleCovers tum s.core.frame_dec (shiftDownCnf accCnf) ∧
    CnfVarsLt c.mv (shiftDownCnf accCnf) ∧
    FullSparseInvW c (CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf accCnf))
      F_cur s ∧
    (CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf accCnf)).Entails
      (cnfOfClauses F_cur) ∧
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m ∧
    match parseClause c.mv (cnfBytes.drop i0) with
    | none =>
      ∀ s' m', s'.LengthsOk c → s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
        s'.core.probing = s.core.probing →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (0#64, ()) m'
    | some (cl, rest) =>
      ∀ r s' j m',
        (∀ lit ∈ cl.literals, 1 ≤ lit.1) →
        i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        s'.LengthsOk c → s'.core.cur_vars = c.mv →
        s'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
        s'.core.probing = s.core.probing →
        TumbleInv tum c.mv s'.scratch.extend_len s'.core.frame_dec →
        TumbleCovers tum s'.core.frame_dec (shiftDownCnf (accCnf.add cl)) →
        CnfVarsLt c.mv (shiftDownCnf (accCnf.add cl)) →
        (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
        (r = 1#64 → ∃ F_cur',
          FullSparseInvW c
            (CNF.relabel (tumblePi tum s'.core.frame_dec) (shiftDownCnf (accCnf.add cl)))
            F_cur' s' ∧
          (CNF.relabel (tumblePi tum s'.core.frame_dec) (shiftDownCnf (accCnf.add cl))).Entails
            (cnfOfClauses F_cur')) →
        (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
        (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
          TumbleValsRel tum c.mv s.core.frame_dec vext s.core.vals →
          TumbleUnusedZero tum c.mv s.scratch.extend_len s.core.vals →
          cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          vext[l]?.getD 0#8 = 0#8 →
          r = 1#64 ∧
          TumbleValsRel tum c.mv s'.core.frame_dec
            ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8) s'.core.vals ∧
          TumbleUnusedZero tum c.mv s'.scratch.extend_len s'.core.vals ∧
          s'.core.trail_end = s.core.trail_end + 1 ∧
          s'.core.propagated = s.core.propagated) →
        (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
          TumbleValsRel tum c.mv s.core.frame_dec vext s.core.vals →
          cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          vext[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Parse-exit tumble finisher `full_tumble_finish_fid(h)`. -/
@[expose] def fullTumbleFinishFidSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level = 0 ∧
    (FullMem c s ⋆ R) m ∧
    ∀ fdec' ext' elen' m',
      let s' : FullState :=
        { core := { s.core with frame_dec := fdec' }
          scratch := { s.scratch with extend_stk := ext', extend_len := elen' } }
      s'.LengthsOk c →
      (c.mv < c.extend_cap → elen' = c.mv + 1) →
      (¬ c.mv < c.extend_cap → s' = s) →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 Option-A `FullM6HdrMem`-threaded contract for `full_parse_body_m6` and
`full_parse_body`. -/
@[expose] def fullParseBodyM6Spec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    parseHeader cnfBytes = some (c.mv, c.nc, cnfBytes.drop i0) ∧
    s.core.cur_vars = c.mv ∧ s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.core.cur_level = 0 ∧ s.core.trail_end = 0 ∧ s.core.propagated = 0 ∧
    s.core.arena_len = 0 ∧ s.core.oom = 0#64 ∧ s.core.probing = 0#64 ∧
    s.core.inconsistent = 0#64 ∧
    s.core.vals = List.replicate (2 * c.max_vars) 0#8 ∧
    s.core.wvec = List.replicate (4 * c.max_vars) 0#32 ∧
    FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
    (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel = s.core.fuel → s'.core.oom = 0#64 → s'.core.probing = 0#64 →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        FullM6HdrInv c (shiftDownCnf cnf) ext' s' ∧ s'.core.cur_level = 0) →
      (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
        r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Direct dependency spec table for `Src.Parse`. -/
@[expose] def deps : List SpecEntry :=
  Backtrack.Spec.specs ++ Clause.Spec.specs ++ Dimacs.Spec.specs ++
  Float64.Spec.specs ++ Heap.Spec.specs ++ PropSearch.Spec.specs ++ Watch.Spec.specs

/-- Canonical exported specification rows matching `Src.Parse.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_activate_lit_fid", [i64, i32], [], fullActivateLitFidSpec, true⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClTumSpec, true⟩
  , ⟨"full_tumble_finish_fid", [i64], [], fullTumbleFinishFidSpec, true⟩
  , ⟨"full_parse_body_m6", [i64, i64], [i64], fullParseBodyM6Spec, true⟩
  , ⟨"full_parse_body", [i64, i64], [i64], fullParseBodyM6Spec, true⟩
  ]

theorem specs_sigs : specs.map SpecEntry.sig = fns.map Fn.sig := by decide

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : ∀ e ∈ specs, e.noExit = true := by decide

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> xfree

theorem has_full_activate_lit_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_activate_lit_fid" fullActivateLitFidSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide)) (by xfree)

theorem has_full_ingest_cl {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_ingest_cl" fullIngestClTumSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide)) (by xfree)

theorem has_full_tumble_finish_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_tumble_finish_fid" fullTumbleFinishFidSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide)) (by xfree)

theorem has_full_parse_body_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_parse_body_m6" fullParseBodyM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide)) (by xfree)

theorem has_full_parse_body {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_parse_body" fullParseBodyM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide)) (by xfree)

end LeanQbe.T.Examples.Kissat.Proof.Parse.Spec
