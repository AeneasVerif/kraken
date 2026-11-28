/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpAnalyzeCore
import LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.Rules
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Proof for `full_analyze_m6_hdr` (`Proof.Analyze.WpAnalyze`)

Callee-parametric `Func.wp` proof for `Src.Analyze.full_analyze_m6_hdr_body` against
`Analyze.Spec.fullAnalyzeM6HdrSpec` (`= m6HdrAnalyzeSpec`), using only canonical sibling `Spec`
interfaces (`0` legacy imports, `0` `@[expose]` on theorems/sections, `<= 100` cols).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open scoped LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
open LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec

/-- Parametric `Func.wp` proof for `Src.Analyze.full_analyze_m6_hdr_body` against
`Analyze.Spec.fullAnalyzeM6HdrSpec`. -/
theorem full_analyze_m6_hdr_wp (Γ : Env)
    (hDrUpd : ∀ a m Q X, m6HdrDrMutSpec a m Q X →
      Γ "m6_hdr_dr_update" [i64] [] a m Q X)
    (hAnaCore : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_core_m6" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Func.wp Γ Src.Analyze.full_analyze_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hconf, hm, hQ⟩ := m6HdrAnalyzeSpec_elim hs
  have hcfg := hinv.cfgOk; have hext := hinv.extOk; have hsp := hinv.sparseW
  unfold Func.wp Src.Analyze.full_analyze_m6_hdr_body; dsimp only
  refine wp_m6Hdr_focus_frame hm fun hm' => ?_
  c0_hsteps_nogrp
  · have hcl0 : s.core.cur_level = 0 := by
      have hle := hsp.2.1.cur_level_le
      have hte := hsp.1.core_ok.trail_end_le
      have hcv := hsp.1.core_ok.cur_vars_le
      have hmv := c.hmaxv; unfold dimacsBound at hmv
      have h0 : BitVec.ofNat 64 s.core.cur_level = 0#64 := by assumption
      have h1 := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      exact h1
    exact hQ 20#64 ext s m hext hsp.1 (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _)
      ⟨rfl, fun _ => ⟨hsp.toOtfs, Nat.le_refl _, rfl⟩⟩
      (fun _ => level0_unsat_of_conflict_okW hsp.2.1 hcl0 hconf)
      (fun h0 => by cases h0) (fun h1 => by cases h1) (fullM6HdrMem_unfocus hm')
  · refine wp_join_group (ts := [])
      (fun () m2 => ∃ ext2, M6HdrExtOk ext2 ∧ (FullM6HdrMem c ext2 s ⋆ R) m2)
      (fun _ () m2 ⟨ext2, hext2, hm2⟩ => ?_)
      (fun _ hJp => ?_)
    · have hinv2 : FullM6HdrInvW c F0 F_cur ext2 s := FullM6HdrInvW.mk_inv hcfg hext2 hsp
      c0_hsteps_nogrp; c0_call hAnaCore
      exact m6HdrAnalyzeSpec_of hinv2 hconf hm2 hQ
    · c0_hsteps_nogrp
      · c0_call hDrUpd
        refine m6HdrDrMutSpec_of hcfg hext hsp.1 (fullM6HdrMem_unfocus hm')
          fun ext2 m2 hinit2 _ hm2 => ?_
        c0_hsteps; exact hJp () m2 ⟨ext2, hinit2.toOk, hm2⟩
      · exact hJp () m ⟨ext, hext, fullM6HdrMem_unfocus hm'⟩

end LeanQbe.T.Examples.Kissat.Proof.Analyze
