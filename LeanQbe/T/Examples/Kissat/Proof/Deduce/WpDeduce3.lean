/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpDeduce3a
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpDeduceTop

/-!
# Kissat 1-UIP Deduce Top-Level WP (`Proof.Deduce.WpDeduce3`)

Composes `WpDeduceTop.full_deduce_1uip_m6_hdr_loop_wp` with
`WpDeduce3a.deduce_loop_rsn_wp` to prove `full_deduce_1uip_m6_hdr_wp`
against `Proof.Deduce.Spec.fullDeduce1uipM6HdrSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Deduce
open LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec

/-- Canonical `Func.wp` proof for `full_deduce_1uip_m6_hdr` (`Spec.fullDeduce1uipM6HdrSpec`). -/
theorem full_deduce_1uip_m6_hdr_wp (Γ : Env)
    (hLit : Γ.Has "full_analyze_lit" fullAnalyzeLitSpec)
    (hRsn : Γ.Has "full_analyze_rsn_m6_hdr" s13AnalyzeRsnHdrSpec)
    (hClr : Γ.Has "full_clear_ana" fullClearAnaSpec)
    (hLarge : Γ.Has "full_otfs_large" step13OtfsLargeSpec)
    (hBin : Γ.Has "full_otfs_bin" fullOtfsBinSpec)
    (hSub : Γ.Has "full_otfs_subsume" fullOtfsSubsumeSpec) :
    ∀ a m Q X, fullDeduce1uipM6HdrSpec a m Q X →
      Func.wp Γ full_deduce_1uip_m6_hdr_body a m Q X :=
  full_deduce_1uip_m6_hdr_loop_wp Γ hLit hRsn hClr
    (@deduce_loop_rsn_wp Γ hRsn hClr hBin hLarge hSub)

end LeanQbe.T.Examples.Kissat.Proof.Deduce
