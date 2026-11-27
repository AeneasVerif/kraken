/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv
public import LeanQbe.T.Examples.Kissat.Src.Dimacs
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specification Table for `Kissat.Src.Dimacs` (`Proof.Dimacs.Spec`)

Defines the `7` canonical DIMACS scanner/header/literal `Spec` contracts using
`Kissat.Ref.*` and `Kissat.Proof.Spec.*` (`dimacsState`, `isWsWord`, `isDigitWord`,
`nextLitPure`), and reuses `Proof.Spec.kissatCheckModelExactSpec` and `Proof.Spec.fullSkipClSpec`
directly (`0` spec duplication, `0` legacy imports, `0` `@[expose]` on theorems/lemmas).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec

open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src
open Kraken.Bedrock2.Test

/-- Specification of `kissat_is_ws(b)`. -/
@[expose] def kissatIsWsSpec : Spec [i64] [.bool] := fun (b, ()) m Q _ =>
  Q (isWsWord b, ()) m

/-- Specification of `kissat_is_digit(b)`. -/
@[expose] def kissatIsDigitSpec : Spec [i64] [.bool] := fun (b, ()) m Q _ =>
  Q (isDigitWord b, ()) m

/-- Specification of `kissat_skip_ws_comments(p, end)`. -/
@[expose] def kissatSkipWsCommentsSpec : Spec [i64, i64] [i64] := fun (p, cend, ()) m Q _ =>
  ∃ (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    p = cnf_ptr + BitVec.ofNat 64 i0 ∧
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆ R) m ∧
    ∀ j, i0 ≤ j → j ≤ cnfBytes.length →
      cnfBytes.drop j = skipWsComments (cnfBytes.drop i0) →
      Q (cnf_ptr + BitVec.ofNat 64 j, ()) m

/-- Specification of `kissat_skip_ws1(end, d)`. -/
@[expose] def kissatSkipWs1Spec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
  ∃ (cnf_ptr mv nc val : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 i0) val ⋆ R) m ∧
    match skipWs1 (cnfBytes.drop i0) with
    | none => Q (false, ()) m
    | some rest =>
      ∀ j m', i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 j) val ⋆ R) m' →
        Q (true, ()) m'

/-- Specification of `kissat_read_nat(end, d)`. -/
@[expose] def kissatReadNatSpec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
  ∃ (cnf_ptr mv nc val : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 i0) val ⋆ R) m ∧
    match parseNat (cnfBytes.drop i0) with
    | none => Q (false, ()) m
    | some (v, rest) =>
      ∀ j m', v < dimacsBound → i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 v) ⋆ R) m' →
        Q (true, ()) m'

/-- Specification of `kissat_parse_header(cnf_ptr, cnf_end, d)`. -/
@[expose] def kissatParseHeaderSpec : Spec [i64, i64, i64] [.bool] :=
  fun (cnf_ptr, cend, d, ()) m Q _ =>
  ∃ (mv0 nc0 cur0 val0 : BitVec 64) (cnfBytes : List UInt8) (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv0 nc0 cur0 val0 ⋆ R) m ∧
    match parseHeader cnfBytes with
    | none =>
      ∀ mv' nc' cur' val' m',
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv' nc' cur' val' ⋆ R) m' →
        Q (false, ()) m'
    | some (mv, nc, rest) =>
      ∀ j m', mv < dimacsBound → nc < dimacsBound →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
            (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R) m' →
        Q (true, ()) m'

/-- Specification of `kissat_next_lit(cnf_end, d)` returning status `0` (err), `1` (end of
clause), or `2` (0-based encoded literal in `d->val`). -/
@[expose] def kissatNextLitSpec : Spec [i64, i64] [i64] := fun (cend, d, ()) m Q _ =>
  ∃ (cnf_ptr nc val0 : BitVec 64) (mv : Nat) (cnfBytes : List UInt8) (i0 : Nat)
    (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    mv < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 i0) val0 ⋆ R) m ∧
    match nextLitPure mv (cnfBytes.drop i0) with
    | .err =>
      ∀ cur' val' m',
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc cur' val' ⋆ R) m' →
        Q (0#64, ()) m'
    | .endClause rest =>
      ∀ j m', i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 j) 0#64 ⋆ R) m' →
        Q (1#64, ()) m'
    | .lit l rest =>
      ∀ j m', l < 2 * mv → l < 2 * dimacsBound →
        i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc
            (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) ⋆ R) m' →
        Q (2#64, ()) m'

theorem kissatIsWsSpec_xfree : Spec.XFree kissatIsWsSpec := by xfree

theorem kissatIsDigitSpec_xfree : Spec.XFree kissatIsDigitSpec := by xfree

theorem kissatSkipWsCommentsSpec_xfree : Spec.XFree kissatSkipWsCommentsSpec := by xfree

theorem kissatSkipWs1Spec_xfree : Spec.XFree kissatSkipWs1Spec := by xfree

theorem kissatReadNatSpec_xfree : Spec.XFree kissatReadNatSpec := by xfree

theorem kissatParseHeaderSpec_xfree : Spec.XFree kissatParseHeaderSpec := by xfree

theorem kissatNextLitSpec_xfree : Spec.XFree kissatNextLitSpec := by xfree

theorem kissatCheckModelExactSpec_xfree : Spec.XFree kissatCheckModelExactSpec := by xfree

theorem fullSkipClSpec_xfree : Spec.XFree fullSkipClSpec := by xfree

/-- Canonical `SpecEntry` table matching `Src.Dimacs.fns` 1-to-1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  , ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  , ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  , ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  , ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  , ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  , ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Dimacs.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem has_kissat_is_ws {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_is_ws" kissatIsWsSpec :=
  Env.Sat.has h List.mem_cons_self kissatIsWsSpec_xfree

theorem has_kissat_is_digit {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_is_digit" kissatIsDigitSpec :=
  Env.Sat.has h (.tail _ List.mem_cons_self) kissatIsDigitSpec_xfree

theorem has_kissat_skip_ws_comments {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_skip_ws_comments" kissatSkipWsCommentsSpec :=
  Env.Sat.has h (.tail _ (.tail _ List.mem_cons_self)) kissatSkipWsCommentsSpec_xfree

theorem has_kissat_skip_ws1 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_skip_ws1" kissatSkipWs1Spec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ List.mem_cons_self))) kissatSkipWs1Spec_xfree

theorem has_kissat_read_nat {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_read_nat" kissatReadNatSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self)))) kissatReadNatSpec_xfree

theorem has_kissat_parse_header {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_parse_header" kissatParseHeaderSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self)))))
    kissatParseHeaderSpec_xfree

theorem has_kissat_next_lit {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_next_lit" kissatNextLitSpec :=
  Env.Sat.has h
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self))))))
    kissatNextLitSpec_xfree

theorem has_kissat_check_model {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_check_model" kissatCheckModelExactSpec :=
  Env.Sat.has h
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self)))))))
    kissatCheckModelExactSpec_xfree

theorem has_full_skip_cl {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_skip_cl" fullSkipClSpec :=
  Env.Sat.has h
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      List.mem_cons_self))))))))
    fullSkipClSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
