/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Src.Gates
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat/Src/Gates.lean` (`Proof/Gates/Spec`)

Single source of truth for all `13` gate-extraction functions of `Src.Gates.fns`
(`8` M7 gate extractors + `5` M8 gate extractors; `0` externs):
- One canonical `Spec` per function (`@[expose]` definitions only).
- `specs : List SpecEntry` matching `Src.Gates.fns` order 1:1 (`noExit := true`).
- `Spec.XFree` proofs (`by xfree`), `specs_sigs`, `Env.Has` projections, and
  `intro`/`elim` wrappers in `public section` (`0` `@[expose]` on theorems).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Gates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

@[expose] public section

/-! ## 1. M7 Gate-Extraction Canonical Specs (`8` functions) -/

/-- Canonical contract for `full_bve_find_equiv_m7`. -/
def fullBveFindEquivM7Spec : Spec [i64, i32, i32] [.bool] := fun (h, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
    np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
    (∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
    (∀ j < nn.toNat, let w := s.scratch.scratch_buf[512 + j]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for `full_bve_find_and_m7`. -/
def fullBveFindAndM7Spec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, lit, lit_n, opp_n, ()) m Q _ =>
    let lit_off := (lit &&& 1#32) <<< 9
    let opp_off := 512#32 - lit_off
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
      lit.toNat < 2 * s.core.cur_vars ∧ lit_n.toNat ≤ 512 ∧ opp_n.toNat ≤ 512 ∧
      (∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
        (s.scratch.scratch_buf[lit_off.toNat + i]?.getD 0#32)) ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s (lit.toNat ^^^ 1)
        (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for `full_bve_get_tern_m7`: extracts 2 unassigned literals of `cr`. -/
def fullBveGetTernM7Spec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, _v_lit, cr, out_off, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      out_off.toNat + 2 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < out_off.toNat ∨ out_off.toNat + 2 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for `full_bve_match_tern_m7`. -/
def fullBveMatchTernM7Spec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, nl, _x, _y, n_off, nn, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      n_off.toNat + nn.toNat ≤ 1024 ∧ nn.toNat ≤ 512 ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
        (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < nn.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical contract for `full_bve_find_ite_side_m7`. -/
def fullBveFindIteSideM7Spec : Spec [i64, i32, i32, i32, .bool] [.bool] :=
  fun (h, v, np, nn, _neg, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for `full_bve_find_ite_m7`. -/
def fullBveFindIteM7Spec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for `full_bve_xor_pat_m7` (read-only; permits temporary `lit_mark`). -/
def fullBveXorPatM7Spec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, _v_lit, cr, k, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      1 ≤ k.toNat ∧ k.toNat ≤ 4 ∧ (FullMem c s ⋆ R) m ∧
      ∀ pat : BitVec 32, (pat = 0xFFFFFFFF#32 ∨ pat.toNat < 16) → Q (pat, ()) m

/-- Canonical contract for `full_bve_find_xor_m7`. -/
def fullBveFindXorM7Spec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ## 2. M8 Gate-Extraction Canonical Specs (`5` functions) -/

/-- Canonical contract for `full_bve_find_equiv_m8`. -/
def m8BveFindEquivSpec : Spec [i64, i32, i32] [.bool] := fun (h, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
    np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
    (∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
    (∀ j < nn.toNat, let w := s.scratch.scratch_buf[2001 + j]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for `full_bve_find_and_m8`. -/
def m8BveFindAndSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, lit, lit_n, opp_n, ()) m Q _ =>
    let lit_off : Nat := if (lit &&& 1#32) ≠ 0#32 then 2001 else 0
    let opp_off : Nat := if (lit &&& 1#32) ≠ 0#32 then 0 else 2001
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      lit_n.toNat ≤ 2001 ∧ opp_n.toNat ≤ 2001 ∧
      (∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
        (s.scratch.scratch_buf[lit_off + i]?.getD 0#32)) ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s ((lit ^^^ 1#32).toNat)
        (s.scratch.scratch_buf[opp_off + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for `full_bve_match_tern_m8`. -/
def m8BveMatchTernSpec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, opp_lit, _x, _y, opp_off, opp_n, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      opp_off.toNat + opp_n.toNat ≤ 4002 ∧ opp_n.toNat ≤ 2001 ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s opp_lit.toNat
        (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4132 ∨ 4133 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < opp_n.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical contract for `full_bve_find_ite_side_m8`. -/
def m8BveFindIteSideSpec : Spec [i64, i32, i32, i32, .bool] [.bool] :=
  fun (h, v, np, nn, _neg, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for `full_bve_find_ite_m8`. -/
def m8BveFindIteSpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ## 3. Canonical `SpecEntry` Table (`specs`) matching `Src.Gates.fns` 1:1 -/

/-- Canonical `SpecEntry` rows matching `Src.Gates.fns` order (`13` functions). -/
def specs : List SpecEntry :=
  [ { name := "full_bve_find_equiv_m7", as := [i64, i32, i32], rs := [.bool],
      spec := fullBveFindEquivM7Spec, noExit := true }
  , { name := "full_bve_find_and_m7", as := [i64, i32, i32, i32], rs := [.bool],
      spec := fullBveFindAndM7Spec, noExit := true }
  , { name := "full_bve_get_tern_m7", as := [i64, i32, i32, i32], rs := [.bool],
      spec := fullBveGetTernM7Spec, noExit := true }
  , { name := "full_bve_match_tern_m7", as := [i64, i32, i32, i32, i32, i32], rs := [i32],
      spec := fullBveMatchTernM7Spec, noExit := true }
  , { name := "full_bve_find_ite_side_m7", as := [i64, i32, i32, i32, .bool], rs := [.bool],
      spec := fullBveFindIteSideM7Spec, noExit := true }
  , { name := "full_bve_find_ite_m7", as := [i64, i32, i32, i32], rs := [.bool],
      spec := fullBveFindIteM7Spec, noExit := true }
  , { name := "full_bve_xor_pat_m7", as := [i64, i32, i32, i32], rs := [i32],
      spec := fullBveXorPatM7Spec, noExit := true }
  , { name := "full_bve_find_xor_m7", as := [i64, i32, i32, i32], rs := [.bool],
      spec := fullBveFindXorM7Spec, noExit := true }
  , { name := "full_bve_find_equiv_m8", as := [i64, i32, i32], rs := [.bool],
      spec := m8BveFindEquivSpec, noExit := true }
  , { name := "full_bve_find_and_m8", as := [i64, i32, i32, i32], rs := [.bool],
      spec := m8BveFindAndSpec, noExit := true }
  , { name := "full_bve_match_tern_m8", as := [i64, i32, i32, i32, i32, i32], rs := [i32],
      spec := m8BveMatchTernSpec, noExit := true }
  , { name := "full_bve_find_ite_side_m8", as := [i64, i32, i32, i32, .bool], rs := [.bool],
      spec := m8BveFindIteSideSpec, noExit := true }
  , { name := "full_bve_find_ite_m8", as := [i64, i32, i32, i32], rs := [.bool],
      spec := m8BveFindIteSpec, noExit := true } ]

end

/-! ## 4. `Spec.XFree`, `specs_sigs`, `Env.Sat.has`, and `intro` / `elim` Helpers -/

public section

theorem specs_sigs : specs.map SpecEntry.sig = Src.Gates.fns.map Fn.sig := rfl

theorem fullBveFindEquivM7Spec_xfree : fullBveFindEquivM7Spec.XFree := by xfree
theorem fullBveFindAndM7Spec_xfree : fullBveFindAndM7Spec.XFree := by xfree
theorem fullBveGetTernM7Spec_xfree : fullBveGetTernM7Spec.XFree := by xfree
theorem fullBveMatchTernM7Spec_xfree : fullBveMatchTernM7Spec.XFree := by xfree
theorem fullBveFindIteSideM7Spec_xfree : fullBveFindIteSideM7Spec.XFree := by xfree
theorem fullBveFindIteM7Spec_xfree : fullBveFindIteM7Spec.XFree := by xfree
theorem fullBveXorPatM7Spec_xfree : fullBveXorPatM7Spec.XFree := by xfree
theorem fullBveFindXorM7Spec_xfree : fullBveFindXorM7Spec.XFree := by xfree
theorem m8BveFindEquivSpec_xfree : m8BveFindEquivSpec.XFree := by xfree
theorem m8BveFindAndSpec_xfree : m8BveFindAndSpec.XFree := by xfree
theorem m8BveMatchTernSpec_xfree : m8BveMatchTernSpec.XFree := by xfree
theorem m8BveFindIteSideSpec_xfree : m8BveFindIteSideSpec.XFree := by xfree
theorem m8BveFindIteSpec_xfree : m8BveFindIteSpec.XFree := by xfree

private theorem mem_has {Γ : Env} (h : Γ.Sat specs) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ specs)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem has_full_bve_get_tern_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_get_tern_m7" fullBveGetTernM7Spec :=
  mem_has h (by simp [specs]) fullBveGetTernM7Spec_xfree

theorem has_full_bve_match_tern_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_match_tern_m7" fullBveMatchTernM7Spec :=
  mem_has h (by simp [specs]) fullBveMatchTernM7Spec_xfree

theorem has_full_bve_find_ite_side_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_find_ite_side_m7" fullBveFindIteSideM7Spec :=
  mem_has h (by simp [specs]) fullBveFindIteSideM7Spec_xfree

theorem has_full_bve_xor_pat_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_xor_pat_m7" fullBveXorPatM7Spec :=
  mem_has h (by simp [specs]) fullBveXorPatM7Spec_xfree

theorem has_full_bve_match_tern_m8 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_match_tern_m8" m8BveMatchTernSpec :=
  mem_has h (by simp [specs]) m8BveMatchTernSpec_xfree

theorem has_full_bve_find_ite_side_m8 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bve_find_ite_side_m8" m8BveFindIteSideSpec :=
  mem_has h (by simp [specs]) m8BveFindIteSideSpec_xfree

theorem fullBveFindEquivM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1088 ≤ c.scratch_cap)
    (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hn : ∀ j < nn.toNat, let w := s.scratch.scratch_buf[512 + j]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindEquivM7Spec (h, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveFindEquivM7Spec_elim {a m Q X} (h : fullBveFindEquivM7Spec a m Q X) :
    let (hp, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
      np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
        (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ j < nn.toNat, let w := s.scratch.scratch_buf[512 + j]?.getD 0#32;
        (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, np, nn, ⟨⟩⟩; exact h

theorem fullBveFindAndM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {lit lit_n opp_n : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1088 ≤ c.scratch_cap)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hln : lit_n.toNat ≤ 512) (hon : opp_n.toNat ≤ 512)
    (hpl : ∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
      (s.scratch.scratch_buf[((lit &&& 1#32) <<< 9).toNat + i]?.getD 0#32))
    (hnl : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s (lit.toNat ^^^ 1)
      (s.scratch.scratch_buf[(512#32 - ((lit &&& 1#32) <<< 9)).toNat + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindAndM7Spec (h, lit, lit_n, opp_n, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hlit, hln, hon, hpl, hnl, hm, hQ⟩

theorem fullBveFindAndM7Spec_elim {a m Q X} (h : fullBveFindAndM7Spec a m Q X) :
    let (hp, lit, ln, on_, _) := a
    let lo := (lit &&& 1#32) <<< 9
    let oo := 512#32 - lo
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
      lit.toNat < 2 * s.core.cur_vars ∧ ln.toNat ≤ 512 ∧ on_.toNat ≤ 512 ∧
      (∀ i < ln.toNat, FullBveEntryOkW F_cur s lit.toNat
        (s.scratch.scratch_buf[lo.toNat + i]?.getD 0#32)) ∧
      (∀ j < on_.toNat, FullBveEntryOkW F_cur s (lit.toNat ^^^ 1)
        (s.scratch.scratch_buf[oo.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, lit, ln, on_, ⟨⟩⟩; exact h

theorem fullBveGetTernM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v_lit cr out_off : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (href : cr.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr.toNat = false)
    (hout : out_off.toNat + 2 ≤ c.scratch_cap) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < out_off.toNat ∨ out_off.toNat + 2 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveGetTernM7Spec (h, v_lit, cr, out_off, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, href, hng, hout, hm, hQ⟩

theorem fullBveMatchTernM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {nl x y n_off nn : BitVec 32}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1066 ≤ c.scratch_cap)
    (hnoff : n_off.toNat + nn.toNat ≤ 1024) (hnn : nn.toNat ≤ 512)
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
      (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 32) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < nn.toNat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fullBveMatchTernM7Spec (h, nl, x, y, n_off, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hnoff, hnn, hn, hm, hQ⟩

theorem fullBveMatchTernM7Spec_elim {a m Q X} (h : fullBveMatchTernM7Spec a m Q X) :
    let (hp, nl, _x, _y, n_off, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      n_off.toNat + nn.toNat ≤ 1024 ∧ nn.toNat ≤ 512 ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
        (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < nn.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨hp, nl, _x, _y, n_off, nn, ⟨⟩⟩; exact h

theorem fullBveFindIteSideM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32} {neg : Bool}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1066 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindIteSideM7Spec (h, v, np, nn, neg, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveFindIteSideM7Spec_elim {a m Q X} (h : fullBveFindIteSideM7Spec a m Q X) :
    let (hp, v, np, nn, _neg, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, _neg, ⟨⟩⟩; exact h

theorem fullBveFindIteM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1066 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindIteM7Spec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveFindIteM7Spec_elim {a m Q X} (h : fullBveFindIteM7Spec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

theorem fullBveXorPatM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v_lit cr k : BitVec 32}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (href : cr.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr.toNat = false)
    (hk1 : 1 ≤ k.toNat) (hk4 : k.toNat ≤ 4) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ pat : BitVec 32, (pat = 0xFFFFFFFF#32 ∨ pat.toNat < 16) → Q (pat, ()) m) :
    fullBveXorPatM7Spec (h, v_lit, cr, k, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hlen, hw, href, hng, hk1, hk4, hm, hQ⟩

theorem fullBveXorPatM7Spec_elim {a m Q X} (h : fullBveXorPatM7Spec a m Q X) :
    let (hp, _vl, cr, k, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      1 ≤ k.toNat ∧ k.toNat ≤ 4 ∧ (FullMem c s ⋆ R) m ∧
      ∀ pat : BitVec 32, (pat = 0xFFFFFFFF#32 ∨ pat.toNat < 16) → Q (pat, ()) m := by
  rcases a with ⟨hp, _vl, cr, k, ⟨⟩⟩; exact h

theorem fullBveFindXorM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1088 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindXorM7Spec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveFindXorM7Spec_elim {a m Q X} (h : fullBveFindXorM7Spec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

theorem m8BveFindEquivSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hn : ∀ j < nn.toNat, let w := s.scratch.scratch_buf[2001 + j]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8BveFindEquivSpec (h, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8BveFindEquivSpec_elim {a m Q X} (h : m8BveFindEquivSpec a m Q X) :
    let (hp, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
        (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ j < nn.toNat, let w := s.scratch.scratch_buf[2001 + j]?.getD 0#32;
        (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, np, nn, ⟨⟩⟩; exact h

theorem m8BveFindAndSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {lit lit_n opp_n : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hln : lit_n.toNat ≤ 2001) (hon : opp_n.toNat ≤ 2001)
    (hl : ∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
      (s.scratch.scratch_buf[(if (lit &&& 1#32) ≠ 0#32 then 2001 else 0) + i]?.getD 0#32))
    (ho : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s ((lit ^^^ 1#32).toNat)
      (s.scratch.scratch_buf[(if (lit &&& 1#32) ≠ 0#32 then 0 else 2001) + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8BveFindAndSpec (h, lit, lit_n, opp_n, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hln, hon, hl, ho, hm, hQ⟩

theorem m8BveFindAndSpec_elim {a m Q X} (h : m8BveFindAndSpec a m Q X) :
    let (hp, lit, lit_n, opp_n, _) := a
    let lit_off : Nat := if (lit &&& 1#32) ≠ 0#32 then 2001 else 0
    let opp_off : Nat := if (lit &&& 1#32) ≠ 0#32 then 0 else 2001
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      lit_n.toNat ≤ 2001 ∧ opp_n.toNat ≤ 2001 ∧
      (∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
        (s.scratch.scratch_buf[lit_off + i]?.getD 0#32)) ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s ((lit ^^^ 1#32).toNat)
        (s.scratch.scratch_buf[opp_off + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, lit, lit_n, opp_n, ⟨⟩⟩; exact h

theorem m8BveMatchTernSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64}
    {opp_lit x y opp_off opp_n : BitVec 32}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hoff : opp_off.toNat + opp_n.toNat ≤ 4002) (hon : opp_n.toNat ≤ 2001)
    (hn : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s opp_lit.toNat
      (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 32) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4132 ∨ 4133 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < opp_n.toNat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m8BveMatchTernSpec (h, opp_lit, x, y, opp_off, opp_n, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hoff, hon, hn, hm, hQ⟩

theorem m8BveMatchTernSpec_elim {a m Q X} (h : m8BveMatchTernSpec a m Q X) :
    let (hp, opp_lit, _x, _y, opp_off, opp_n, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      opp_off.toNat + opp_n.toNat ≤ 4002 ∧ opp_n.toNat ≤ 2001 ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s opp_lit.toNat
        (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4132 ∨ 4133 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < opp_n.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨hp, opp_lit, _x, _y, opp_off, opp_n, ⟨⟩⟩; exact h

theorem m8BveFindIteSideSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32} {neg : Bool}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8BveFindIteSideSpec (h, v, np, nn, neg, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8BveFindIteSideSpec_elim {a m Q X} (h : m8BveFindIteSideSpec a m Q X) :
    let (hp, v, np, nn, _neg, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, _neg, ⟨⟩⟩; exact h

theorem m8BveFindIteSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8BveFindIteSpec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8BveFindIteSpec_elim {a m Q X} (h : m8BveFindIteSpec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

end

end LeanQbe.T.Examples.Kissat.Proof.Gates
