/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Gates.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Src.Definition
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Definition` (`Proof.Definition.Spec`)

Flat `CanonicalEnv` specification table (`specs`) matching `Src.Definition.fns` (`26` functions:
`11` M7-fallback K6/BVE functions + `15` fidelity K6/BVE functions) 1:1, with `deps` tying
upstream `Backtrack`, `Gates`, and `Kitten` segments, `specs_noExit`, `Spec.XFree` proofs, and
`Env.Has` capability extractors. Zero legacy `Full*` imports; zero `@[expose]` on theorems/sections.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Shared Predicates (`TmkZero`, `K6BufOk`, `fidK6MaxV`, `FidK6BufOk`) -/

/-- Zero-initialized `tarjan_mark[0 ..< cur_vars)` invariant required on BVE gate entry/exit. -/
@[expose] def TmkZero (s : FullState) : Prop :=
  ∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0#32

/-- Structural and arena safety invariant on the M7 K6 micro-solver `u32 *k` slab. -/
@[expose] def K6BufOk (kbuf : List (BitVec 32)) : Prop :=
  let nc := kbuf[1]?.getD 0#32
  let alen := kbuf[14]?.getD 0#32
  let acap := kbuf[15]?.getD 0#32
  2912 + acap.toNat ≤ kbuf.length ∧ kbuf.length < 2 ^ 28 ∧
  nc.toNat ≤ 256 ∧ alen.toNat ≤ acap.toNat ∧
  ∀ cid < nc.toNat,
    let off := (kbuf[1888 + cid]?.getD 0#32).toNat
    let cm := kbuf[2144 + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (kbuf[2400 + cid]?.getD 0#32).toNat
    off + sz ≤ acap.toNat ∧ ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ acap.toNat)

/-- Dynamic K6 variable capacity inside `scratch_buf[4192..)` (`[256, 8192]`, mult of `64`). -/
@[expose] def fidK6MaxV (cap : Nat) : Nat :=
  if cap < 16384 then 0
  else if 524288 ≤ cap then 8192
  else
    let raw := ((cap - 4224) / 64) / 64 * 64
    max 256 (min 8192 raw)

/-- Dynamic structural and arena bounds invariant for fidelity K6 inside `scr[4192..)`. -/
@[expose] def FidK6BufOk (scr : List (BitVec 32)) : Prop :=
  let mv := (scr[4214]?.getD 0#32).toNat
  let nc := (scr[4193]?.getD 0#32).toNat
  let alen := (scr[4206]?.getD 0#32).toNat
  let acap := (scr[4207]?.getD 0#32).toNat
  256 ≤ mv ∧ mv ≤ 8192 ∧
  4224 + 45 * mv + acap ≤ scr.length ∧ scr.length < 2 ^ 30 ∧
  nc ≤ 4 * mv ∧ alen ≤ acap ∧
  ∀ cid < nc,
    let off := (scr[4224 + 29 * mv + cid]?.getD 0#32).toNat
    let cm := scr[4224 + 33 * mv + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (scr[4224 + 37 * mv + cid]?.getD 0#32).toNat
    off + sz ≤ acap ∧ ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ acap)

/-! ## 2. M7 K6 Micro-Solver & Gate Definition Specs (`11` functions, `10` distinct specs) -/

/-- Contract for `full_k6_watch_m7`. -/
@[expose] def fullK6WatchM7Spec : Spec [i64, i32, i32, i32, i32] [] :=
  fun (pk, _cid, _l0, _l1, _sz, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, (idx < 736 ∨ 1888 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

/-- Contract for `full_k6_assign_m7`. -/
@[expose] def fullK6AssignM7Spec : Spec [i64, i32, i32] [] :=
  fun (pk, _lit, _rsn_cid, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
          (idx < 608 ∨ 736 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

/-- Contract for `full_k6_mtf_m7`. -/
@[expose] def fullK6MtfM7Spec : Spec [i64, i32] [] :=
  fun (pk, _v, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 8 → idx ≠ 9 → idx ≠ 10 → idx ≠ 11 →
          (idx < 160 ∨ 352 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

/-- Contract for `full_k6_backtrack_m7`. -/
@[expose] def fullK6BacktrackM7Spec : Spec [i64, i32] [] :=
  fun (pk, _target_lvl, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      2912 ≤ kbuf.length ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
          (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

/-- Contract for `full_k6_prop_m7`. -/
@[expose] def fullK6PropM7Spec : Spec [i64] [i32] :=
  fun (pk, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ r kbuf' m',
        K6BufOk kbuf' → kbuf'.length = kbuf.length →
        kbuf'[0]? = kbuf[0]? → kbuf'[1]? = kbuf[1]? →
        kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
        (∀ cid < 256, kbuf'[1888 + cid]? = kbuf[1888 + cid]? ∧
          kbuf'[2144 + cid]? = kbuf[2144 + cid]? ∧
          kbuf'[2400 + cid]? = kbuf[2400 + cid]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q (r, ()) m'

/-- Contract for `full_k6_ana_cl_m7`. -/
@[expose] def fullK6AnaClM7Spec : Spec [i64, i32, i32] [] :=
  fun (pk, _cid, _skip_v, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length, idx ≠ 16 → idx ≠ 17 → idx ≠ 18 → idx ≠ 20 →
          (idx < 416 ∨ 608 ≤ idx) → (idx < 2784 ∨ 2912 ≤ idx) →
          kbuf'[idx]? = kbuf[idx]?) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

/-- Contract for `full_k6_analyze_m7`. -/
@[expose] def fullK6AnalyzeM7Spec : Spec [i64, i32] [.bool] :=
  fun (pk, _confl_cid, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ (ok : Bool) kbuf' m',
        K6BufOk kbuf' → kbuf'.length = kbuf.length →
        kbuf'[0]? = kbuf[0]? → kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
        (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q (ok, ()) m'

/-- Contract for `full_k6_solve_m7`. -/
@[expose] def fullK6SolveM7Spec : Spec [i64, i64, i32] [i64] :=
  fun (h, pk, _tick_lim, ()) m Q _ =>
    ∃ (hdr : List (BitVec 64)) (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      hdr.length = 140 ∧ K6BufOk kbuf ∧
      (array64 (h + 32) hdr ⋆ array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ r fuel' kbuf' m',
        fuel'.toNat ≤ (hdr[17]?.getD 0#64).toNat →
        K6BufOk kbuf' → kbuf'.length = kbuf.length →
        kbuf'[0]? = kbuf[0]? →
        (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
        kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
        (array64 (h + 32) (hdr.set 17 fuel') ⋆ array (t := i32) pk kbuf' ⋆ R) m' →
        Q (r, ()) m'

/-- Contract for `full_k6_core_m7`. -/
@[expose] def fullK6CoreM7Spec : Spec [i64] [] :=
  fun (pk, ()) m Q _ =>
    ∃ (kbuf : List (BitVec 32)) (R : Mem 64 → Prop),
      K6BufOk kbuf ∧ (array (t := i32) pk kbuf ⋆ R) m ∧
      ∀ kbuf' m', kbuf'.length = kbuf.length →
        (∀ idx < kbuf.length,
          (idx < 416 ∨ (480 ≤ idx ∧ idx < 2144) ∨ 2400 ≤ idx) →
          kbuf'[idx]? = kbuf[idx]?) →
        (∀ cid < (kbuf[1]?.getD 0#32).toNat,
          let m0 := kbuf[2144 + cid]?.getD 0#32
          let m1 := kbuf'[2144 + cid]?.getD 0#32
          (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
            (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32)) →
        (array (t := i32) pk kbuf' ⋆ R) m' → Q () m'

/-- Contract for `full_bve_def_k6_m7` and `full_bve_gates_m7`. -/
@[expose] def fullBveGatesM7Spec : Spec [i64, i32, i32, i32] [] :=
  fun (h, v, np, nn, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 1088 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s.scratch.scratch_buf[512 + j]?) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-! ## 3. Fidelity K6 & BVE Definition Specs (`15` functions, `14` distinct specs) -/

/-- Exact pure specification for `full_bve_k6_mv_fid`. -/
@[expose] def fidBveK6MvSpec : Spec [i64] [i64] := fun (cap, ()) m Q _ =>
  Q (BitVec.ofNat 64 (fidK6MaxV cap.toNat), ()) m

/-- Contract for `full_fid_k6_add_ticks`. -/
@[expose] def fidK6AddTicksSpec : Spec [i64, i64] [] := fun (h, _delta, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 15744 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
    ∀ tk' m',
      let scr' := s.scratch.scratch_buf.set 4204 tk'
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

/-- Contract for `full_k6_watch_fid`. -/
@[expose] def fidK6WatchSpec : Spec [i64, i32, i32, i32, i32] [] :=
  fun (h, _cid, _l0, _l1, _sz, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, (idx < 4224 + 11 * mv ∨ 4224 + 29 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

/-- Contract for `full_k6_assign_fid`. -/
@[expose] def fidK6AssignSpec : Spec [i64, i32, i32] [] :=
  fun (h, _lit, _rsn_cid, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
          (idx < 4224 ∨ 4224 + 2 * mv ≤ idx) →
          (idx < 4224 + 5 * mv ∨ 4224 + 7 * mv ≤ idx) →
          (idx < 4224 + 9 * mv ∨ 4224 + 11 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

/-- Contract for `full_k6_mtf_fid`. -/
@[expose] def fidK6MtfSpec : Spec [i64, i32] [] :=
  fun (h, _v, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4224 + 2 * mv) ∨ 4224 + 5 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

/-- Contract for `full_k6_backtrack_fid`. -/
@[expose] def fidK6BacktrackSpec : Spec [i64, i32] [] :=
  fun (h, _target_lvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨
            (4224 + 2 * mv ≤ idx ∧ idx < 4224 + 9 * mv) ∨ 4224 + 11 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

/-- Contract for `full_k6_prop_fid`. -/
@[expose] def fidK6PropSpec : Spec [i64] [i32] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        FidK6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4195, scr'[i]? = scr[i]?) →
        (∀ i, 4199 ≤ i → i < 4204 → scr'[i]? = scr[i]?) →
        (∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?) →
        (∀ i, 4224 + 2 * mv ≤ i → i < 4224 + 5 * mv → scr'[i]? = scr[i]?) →
        (∀ i, 4224 + 7 * mv ≤ i → i < 4224 + 9 * mv → scr'[i]? = scr[i]?) →
        (∀ i, 4224 + 29 * mv ≤ i → i < 4224 + 45 * mv → scr'[i]? = scr[i]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (r, ()) m'

/-- Contract for `full_k6_ana_cl_fid`. -/
@[expose] def fidK6AnaClSpec : Spec [i64, i32, i32] [] :=
  fun (h, _cid, _skip_v, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
          (idx < 4224 + 6 * mv ∨ 4224 + 9 * mv ≤ idx) →
          (idx < 4224 + 43 * mv ∨ 4224 + 45 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

/-- Contract for `full_k6_analyze_fid`. -/
@[expose] def fidK6AnalyzeSpec : Spec [i64, i32] [.bool] :=
  fun (h, _confl_cid, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        FidK6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4193, scr'[i]? = scr[i]?) →
        scr'[4194]? = scr[4194]? →
        (scr[4193]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
        (∀ cid < (scr[4193]?.getD 0#32).toNat,
          scr'[4224 + 37 * mv + cid]? = scr[4224 + 37 * mv + cid]?) →
        scr'[4199]? = scr[4199]? → scr'[4205]? = scr[4205]? →
        scr'[4207]? = scr[4207]? → scr'[4211]? = scr[4211]? →
        scr'[4213]? = scr[4213]? → scr'[4214]? = scr[4214]? →
        scr'[4215]? = scr[4215]? → scr'[4216]? = scr[4216]? →
        (∀ i, 4224 + 41 * mv ≤ i → i < 4224 + 43 * mv → scr'[i]? = scr[i]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (ok, ()) m'

/-- Contract for `full_k6_solve_fid`. -/
@[expose] def fidK6SolveSpec : Spec [i64, i32] [i64] :=
  fun (h, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧
      (scr[4194]?.getD 0#32).toNat ≤ (scr[4193]?.getD 0#32).toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) scr' fuel' m',
        let s' : FullState :=
          { s with
            core := { s.core with fuel := fuel' }
            scratch := { s.scratch with scratch_buf := scr' } }
        FidK6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4192, scr'[i]? = scr[i]?) →
        scr'[4194]? = scr[4194]? → scr'[4214]? = scr[4214]? →
        (scr[4194]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
        (∀ cid < (scr[4194]?.getD 0#32).toNat,
          scr'[4224 + 37 * mv + cid]? = scr[4224 + 37 * mv + cid]?) →
        fuel'.toNat ≤ s.core.fuel.toNat →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Contract for `full_k6_core_fid`. -/
@[expose] def fidK6CoreSpec : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      let scr := s.scratch.scratch_buf
      let mv := (scr[4214]?.getD 0#32).toNat
      h = c.hdr ∧ s.LengthsOk c ∧ FidK6BufOk scr ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4224 + 6 * mv ∨ (4224 + 7 * mv ≤ idx ∧ idx < 4224 + 33 * mv) ∨
            4224 + 37 * mv ≤ idx) →
          scr'[idx]? = scr[idx]?) →
        FidK6BufOk scr' →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

/-- Contract for `full_k6_extract_and_solve_fid`. -/
@[expose] def fidK6ExtractSolveSpec : Spec [i64, i32, i32, i32, .bool, i32] [.bool] :=
  fun (h, v, np, nn, _second_pass, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < 4002, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Contract for `full_bve_certify_unit_fid`. -/
@[expose] def fidBveCertifyUnitSpec : Spec [i64, i32, i32, i32, i32, i32] [.bool] :=
  fun (h, _v, unit, side_off, side_cnt, side_mask, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
      unit.toNat < 2 * s.core.cur_vars ∧
      side_cnt.toNat ≤ 2001 ∧ side_off.toNat + side_cnt.toNat ≤ 4002 ∧
      (side_mask = 4002#32 ∨ side_mask = 4066#32) ∧
      (∀ i < side_cnt.toNat, FullBveEntryOkW F_cur s unit.toNat
        (s.scratch.scratch_buf[side_off.toNat + i]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < 4192, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Contract for `full_bve_def_k6_fid` and `full_bve_gates_fid`. -/
@[expose] def m8BveGatesSpec : Spec [i64, i32, i32, i32] [] :=
  fun (h, v, np, nn, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ j < nn.toNat, s'.scratch.scratch_buf[2001 + j]? = s.scratch.scratch_buf[2001 + j]?) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-! ## 4. Canonical `deps` & `specs` Tables Matching `Src.Definition.fns` (`26` fns) -/

/-- Upstream dependency specification tables for `Src.Definition`
(`Backtrack`, `Gates`, `Kitten`). -/
@[expose] def deps : List SpecEntry :=
  Proof.Backtrack.Spec.specs ++ Proof.Gates.specs ++ Proof.Kitten.Spec.specs

/-- Canonical `SpecEntry` table matching `Src.Definition.fns` order 1:1 (`26` functions). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_k6_watch_m7", [i64, i32, i32, i32, i32], [], fullK6WatchM7Spec, true⟩
  , ⟨"full_k6_assign_m7", [i64, i32, i32], [], fullK6AssignM7Spec, true⟩
  , ⟨"full_k6_mtf_m7", [i64, i32], [], fullK6MtfM7Spec, true⟩
  , ⟨"full_k6_backtrack_m7", [i64, i32], [], fullK6BacktrackM7Spec, true⟩
  , ⟨"full_k6_prop_m7", [i64], [i32], fullK6PropM7Spec, true⟩
  , ⟨"full_k6_ana_cl_m7", [i64, i32, i32], [], fullK6AnaClM7Spec, true⟩
  , ⟨"full_k6_analyze_m7", [i64, i32], [.bool], fullK6AnalyzeM7Spec, true⟩
  , ⟨"full_k6_solve_m7", [i64, i64, i32], [i64], fullK6SolveM7Spec, true⟩
  , ⟨"full_k6_core_m7", [i64], [], fullK6CoreM7Spec, true⟩
  , ⟨"full_bve_def_k6_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩
  , ⟨"full_bve_gates_m7", [i64, i32, i32, i32], [], fullBveGatesM7Spec, true⟩
  , ⟨"full_bve_k6_mv_fid", [i64], [i64], fidBveK6MvSpec, true⟩
  , ⟨"full_fid_k6_add_ticks", [i64, i64], [], fidK6AddTicksSpec, true⟩
  , ⟨"full_k6_watch_fid", [i64, i32, i32, i32, i32], [], fidK6WatchSpec, true⟩
  , ⟨"full_k6_assign_fid", [i64, i32, i32], [], fidK6AssignSpec, true⟩
  , ⟨"full_k6_mtf_fid", [i64, i32], [], fidK6MtfSpec, true⟩
  , ⟨"full_k6_backtrack_fid", [i64, i32], [], fidK6BacktrackSpec, true⟩
  , ⟨"full_k6_prop_fid", [i64], [i32], fidK6PropSpec, true⟩
  , ⟨"full_k6_ana_cl_fid", [i64, i32, i32], [], fidK6AnaClSpec, true⟩
  , ⟨"full_k6_analyze_fid", [i64, i32], [.bool], fidK6AnalyzeSpec, true⟩
  , ⟨"full_k6_solve_fid", [i64, i32], [i64], fidK6SolveSpec, true⟩
  , ⟨"full_k6_core_fid", [i64], [], fidK6CoreSpec, true⟩
  , ⟨"full_k6_extract_and_solve_fid", [i64, i32, i32, i32, .bool, i32], [.bool],
      fidK6ExtractSolveSpec, true⟩
  , ⟨"full_bve_certify_unit_fid", [i64, i32, i32, i32, i32, i32], [.bool],
      fidBveCertifyUnitSpec, true⟩
  , ⟨"full_bve_def_k6_fid", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩
  , ⟨"full_bve_gates_fid", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩ ]

/-! ## 5. Structural Checks, `Spec.XFree`, & `Env.Has` Extractors -/

theorem specs_sigs : specs.map SpecEntry.sig = Src.Definition.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem fullK6WatchM7Spec_xfree : fullK6WatchM7Spec.XFree := by xfree
theorem fullK6AssignM7Spec_xfree : fullK6AssignM7Spec.XFree := by xfree
theorem fullK6MtfM7Spec_xfree : fullK6MtfM7Spec.XFree := by xfree
theorem fullK6BacktrackM7Spec_xfree : fullK6BacktrackM7Spec.XFree := by xfree
theorem fullK6PropM7Spec_xfree : fullK6PropM7Spec.XFree := by xfree
theorem fullK6AnaClM7Spec_xfree : fullK6AnaClM7Spec.XFree := by xfree
theorem fullK6AnalyzeM7Spec_xfree : fullK6AnalyzeM7Spec.XFree := by xfree
theorem fullK6SolveM7Spec_xfree : fullK6SolveM7Spec.XFree := by xfree
theorem fullK6CoreM7Spec_xfree : fullK6CoreM7Spec.XFree := by xfree
theorem fullBveGatesM7Spec_xfree : fullBveGatesM7Spec.XFree := by xfree
theorem fidBveK6MvSpec_xfree : fidBveK6MvSpec.XFree := by xfree
theorem fidK6AddTicksSpec_xfree : fidK6AddTicksSpec.XFree := by xfree
theorem fidK6WatchSpec_xfree : fidK6WatchSpec.XFree := by xfree
theorem fidK6AssignSpec_xfree : fidK6AssignSpec.XFree := by xfree
theorem fidK6MtfSpec_xfree : fidK6MtfSpec.XFree := by xfree
theorem fidK6BacktrackSpec_xfree : fidK6BacktrackSpec.XFree := by xfree
theorem fidK6PropSpec_xfree : fidK6PropSpec.XFree := by xfree
theorem fidK6AnaClSpec_xfree : fidK6AnaClSpec.XFree := by xfree
theorem fidK6AnalyzeSpec_xfree : fidK6AnalyzeSpec.XFree := by xfree
theorem fidK6SolveSpec_xfree : fidK6SolveSpec.XFree := by xfree
theorem fidK6CoreSpec_xfree : fidK6CoreSpec.XFree := by xfree
theorem fidK6ExtractSolveSpec_xfree : fidK6ExtractSolveSpec.XFree := by xfree
theorem fidBveCertifyUnitSpec_xfree : fidBveCertifyUnitSpec.XFree := by xfree
theorem m8BveGatesSpec_xfree : m8BveGatesSpec.XFree := by xfree

private theorem mem_has {Γ : Env} (h : Γ.Sat specs) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ specs)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem has_full_k6_watch_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_watch_m7" fullK6WatchM7Spec :=
  mem_has h (by simp [specs]) fullK6WatchM7Spec_xfree

theorem has_full_k6_assign_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_assign_m7" fullK6AssignM7Spec :=
  mem_has h (by simp [specs]) fullK6AssignM7Spec_xfree

theorem has_full_k6_mtf_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_mtf_m7" fullK6MtfM7Spec :=
  mem_has h (by simp [specs]) fullK6MtfM7Spec_xfree

theorem has_full_k6_backtrack_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_backtrack_m7" fullK6BacktrackM7Spec :=
  mem_has h (by simp [specs]) fullK6BacktrackM7Spec_xfree

theorem has_full_k6_prop_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_prop_m7" fullK6PropM7Spec :=
  mem_has h (by simp [specs]) fullK6PropM7Spec_xfree

theorem has_full_k6_ana_cl_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_ana_cl_m7" fullK6AnaClM7Spec :=
  mem_has h (by simp [specs]) fullK6AnaClM7Spec_xfree

theorem has_full_k6_analyze_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_analyze_m7" fullK6AnalyzeM7Spec :=
  mem_has h (by simp [specs]) fullK6AnalyzeM7Spec_xfree

theorem has_full_k6_solve_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_solve_m7" fullK6SolveM7Spec :=
  mem_has h (by simp [specs]) fullK6SolveM7Spec_xfree

theorem has_full_k6_core_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_core_m7" fullK6CoreM7Spec :=
  mem_has h (by simp [specs]) fullK6CoreM7Spec_xfree

theorem has_full_bve_def_k6_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_def_k6_m7" fullBveGatesM7Spec :=
  mem_has h (by simp [specs]) fullBveGatesM7Spec_xfree

theorem has_full_bve_gates_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_gates_m7" fullBveGatesM7Spec :=
  mem_has h (by simp [specs]) fullBveGatesM7Spec_xfree

theorem has_full_bve_k6_mv_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_k6_mv_fid" fidBveK6MvSpec :=
  mem_has h (by simp [specs]) fidBveK6MvSpec_xfree

theorem has_full_fid_k6_add_ticks {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fid_k6_add_ticks" fidK6AddTicksSpec :=
  mem_has h (by simp [specs]) fidK6AddTicksSpec_xfree

theorem has_full_k6_watch_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_watch_fid" fidK6WatchSpec :=
  mem_has h (by simp [specs]) fidK6WatchSpec_xfree

theorem has_full_k6_assign_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_assign_fid" fidK6AssignSpec :=
  mem_has h (by simp [specs]) fidK6AssignSpec_xfree

theorem has_full_k6_mtf_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_mtf_fid" fidK6MtfSpec :=
  mem_has h (by simp [specs]) fidK6MtfSpec_xfree

theorem has_full_k6_backtrack_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_backtrack_fid" fidK6BacktrackSpec :=
  mem_has h (by simp [specs]) fidK6BacktrackSpec_xfree

theorem has_full_k6_prop_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_prop_fid" fidK6PropSpec :=
  mem_has h (by simp [specs]) fidK6PropSpec_xfree

theorem has_full_k6_ana_cl_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_ana_cl_fid" fidK6AnaClSpec :=
  mem_has h (by simp [specs]) fidK6AnaClSpec_xfree

theorem has_full_k6_analyze_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_analyze_fid" fidK6AnalyzeSpec :=
  mem_has h (by simp [specs]) fidK6AnalyzeSpec_xfree

theorem has_full_k6_solve_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_solve_fid" fidK6SolveSpec :=
  mem_has h (by simp [specs]) fidK6SolveSpec_xfree

theorem has_full_k6_core_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_core_fid" fidK6CoreSpec :=
  mem_has h (by simp [specs]) fidK6CoreSpec_xfree

theorem has_full_k6_extract_and_solve_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_extract_and_solve_fid" fidK6ExtractSolveSpec :=
  mem_has h (by simp [specs]) fidK6ExtractSolveSpec_xfree

theorem has_full_bve_certify_unit_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_certify_unit_fid" fidBveCertifyUnitSpec :=
  mem_has h (by simp [specs]) fidBveCertifyUnitSpec_xfree

theorem has_full_bve_def_k6_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_def_k6_fid" m8BveGatesSpec :=
  mem_has h (by simp [specs]) m8BveGatesSpec_xfree

theorem has_full_bve_gates_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_gates_fid" m8BveGatesSpec :=
  mem_has h (by simp [specs]) m8BveGatesSpec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
