/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module

/-!
# Gate G1 Toy Source Segment 1 (`Src1`)

Contains one exported leaf (`toy_inc`, inlined into `S2` and `S3`) and one non-exported
out-of-line helper (`toy_helper1`) for rebuild-radius isolation testing.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Src1

open LeanQbe.T

/-- Exported tiny leaf: `x + 1`. -/
@[expose] def fnToyInc : Fn :=
  { name := "toy_inc", as := [i64], rs := [i64]
    body := fun _ _ (x, ()) =>
      .let_ (ts := [i64]) ⟨.add i64, (.var x, .imm 1#64, ())⟩ fun (r, ()) =>
      .ret (.var r, ()) }

/-- Non-exported out-of-line helper: `(x + 7) ^^^ 3`. -/
@[expose] def fnToyHelper1 : Fn :=
  { name := "toy_helper1", as := [i64], rs := [i64]
    body := fun _ _ (x, ()) =>
      .let_ (ts := [i64]) ⟨.add i64, (.var x, .imm 7#64, ())⟩ fun (a, ()) =>
      .let_ (ts := [i64]) ⟨.xor i64, (.var a, .imm 3#64, ())⟩ fun (r, ()) =>
      .ret (.var r, ()) }

/-- Source functions in segment 1. -/
@[expose] def fns : List Fn := [fnToyInc, fnToyHelper1]

end LeanQbeTest.T.SegCertToy.Src1
