/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Inline
public import LeanQbeTest.T.SegCertToy.Src1
public import LeanQbeTest.T.SegCertToy.Src2
public import LeanQbeTest.T.SegCertToy.Src3

/-!
# Gate G1 Toy Whole Source Module & Inline Policy (`SrcFull`)
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.SrcFull

open LeanQbe.T
open LeanQbeTest.T.SegCertToy

/-- Concatenated 3-segment toy function list. -/
@[expose] def toyFns : List Fn :=
  Src1.fns ++ Src2.fns ++ Src3.fns

/-- Whole 3-segment toy source module. -/
@[expose] def toyModule : Module :=
  { fns := toyFns }

/-- Reference inline policy: inline `toy_inc` and `toy_add_inc`, keep `toy_helper1`,
`toy_mix2`, and `toy_step3` out-of-line. -/
@[expose] def toyPolicy : InlinePolicy :=
  { budget := fun _ => 20
    keepOutOfLine := ["toy_helper1", "toy_mix2", "toy_step3"] }

end LeanQbeTest.T.SegCertToy.SrcFull
