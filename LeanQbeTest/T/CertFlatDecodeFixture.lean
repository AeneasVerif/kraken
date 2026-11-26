/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk

/-!
# Test Fixture for `(compile := false)` `TFlatFn` Materialization (`CertFlatDecodeFixture`)

Materializes a 6-function module using default `(compile := false)` on `inline_mod!`,
`inline_mod_chunk!`, and `inline_mod_join!` to verify zero-`meta import` `.olean` decoding in
`LeanQbeTest.T.CertFlatDecodeTest`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.CertFlatDecodeFixture

open LeanQbe.T

/-- Leaf helper (`size = 3`), eligible for inlining. -/
def fnLeaf : Fn where
  name := "leaf"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, ()) =>
    .let_ ⟨OpCode.add i64, (.var x, .imm 1#64, ())⟩ fun (r, ()) => .ret (.var r, ())

/-- Candidate 1 calling `leaf`. -/
def fnStep1 : Fn where
  name := "step1"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, ()) =>
    .call (as := [i64]) (bs := [i64]) "leaf" (.var x, ()) fun (r, ()) => .ret (.var r, ())

/-- Candidate 2 calling `step1` (tests intra-chunk wavefront ordering). -/
def fnStep2 : Fn where
  name := "step2"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, ()) =>
    .call (as := [i64]) (bs := [i64]) "step1" (.var x, ()) fun (r, ()) => .ret (.var r, ())

/-- Candidate 3 calling `leaf` (shares wave 0 with `fnStep1` via `MetaM.par'`). -/
def fnStep3 : Fn where
  name := "step3"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, ()) =>
    .call (as := [i64]) (bs := [i64]) "leaf" (.var x, ()) fun (r, ()) => .ret (.var r, ())

private def bigChain (V : Ty → Type) (L : List Ty → Type) (x : V i64) : Nat → Expr V L [i64]
  | 0 => .ret (.var x, ())
  | n + 1 =>
    .let_ ⟨OpCode.add i64, (.var x, .imm 1#64, ())⟩ fun (y, ()) => bigChain V L y n

/-- Non-candidate 1 (`size > budget`), exercising zero-candidate chunk fast skip. -/
def fnBig : Fn where
  name := "big"
  as := [i64]
  rs := [i64]
  body := fun V L (x, ()) => bigChain V L x 12

/-- Entry function calling `step2`, `step3`, and `big`. -/
def fnEntry : Fn where
  name := "entry"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, ()) =>
    .call (as := [i64]) (bs := [i64]) "step2" (.var x, ()) fun (a, ()) =>
      .call (as := [i64]) (bs := [i64]) "step3" (.var x, ()) fun (b, ()) =>
        .call (as := [i64]) (bs := [i64]) "big" (.var x, ()) fun (c, ()) =>
          .let_ ⟨OpCode.add i64, (.var a, .var b, ())⟩ fun (s, ()) =>
            .let_ ⟨OpCode.add i64, (.var s, .var c, ())⟩ fun (d, ()) => .ret (.var d, ())

/-- Source module (`6` functions). -/
def fixSrcMod : Module :=
  { fns := [fnLeaf, fnStep1, fnStep2, fnStep3, fnBig, fnEntry], externs := [], exits := [] }

/-- Policy accepting `leaf`, `step1`, `step2`, `step3` and rejecting `big`/`entry`. -/
def fixPol : InlinePolicy :=
  { budget := fun _ => 8, maxCallerSize := 200, maxCallerCalls := 8 }

inline_chunk_base! fixBase fixSrcMod fixPol
inline_mod_chunk! fixC0 fixBase fixSrcMod fixPol 0 4
inline_mod_chunk! fixC1 fixBase fixSrcMod fixPol 4 1 (prev := fixC0)
inline_mod_chunk! fixC2 fixBase fixSrcMod fixPol 5 1 (prev := fixC1) (isLast := true)
inline_mod_join! fixMod fixFns fixSrcMod fixPol fixBase [fixC0, fixC1, fixC2]

inline_mod! fixSingleMod fixSrcMod fixPol

end LeanQbeTest.T.CertFlatDecodeFixture
