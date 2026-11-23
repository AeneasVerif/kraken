module

public import LeanQbe.T.Examples.Kissat.FullM7Bump
public import LeanQbe.T.Examples.Kissat.FullM7BumpProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7Bump
meta import LeanQbe.T.Examples.Kissat.FullM7BumpProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Behavioral Checks, Backend Guards, and Axiom Audit (`FullM7Bump`)

1. Executable `#guard` checks on `m7BumpModule` (`7` fns, `3` externs, `10` spec rows, `0` exits),
   `checkAcyclic = true`, drop-in handles (`m7RngNextFn`, `m7ScaleDeltaFn`, `m7ScaleDeltaM6Fn`,
   `m7BumpAnalyzedFn`), behavioral RNG/stamp checks, `PrintCpp`, `PrintQbe`, and `Fn.legal` across
   `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Restated headline theorems for `m7BumpFns_wf`, `m7Bump_acyclic`, `m7BumpEnv_noExit`, all `7`
   parametric WP specs (`full_rng_next_m7`, `full_log10_q16_m7`, `full_scale_delta_m7`,
   `full_bump_sift_m7`, `full_bump_sort_stamps_m7`, `full_bump_reasons_m7`,
   `full_bump_analyzed_m7`), drop-in handles, `m7Bump_moduleOk`, and concrete `Mem 64` UNSAT
   non-vacuity (`XPost := False`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7BumpTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7Bump
open Kraken.Bedrock2.Test

/-! ## 1. Module Structure, Behavioral Checks, and 4-ISA Legalization Guards -/

#guard m7BumpModule.checkAcyclic == true
#guard m7BumpModule.exits.isEmpty == true
#guard m7BumpFns.length == 7
#guard m7BumpExterns.length == 3
#guard m7BumpSpecTable.length == 10
#guard m7BumpSpecTable.all (·.noExit) == true
#guard m7RngNextFn.name == "full_rng_next"
#guard m7ScaleDeltaFn.name == "full_scale_delta"
#guard m7ScaleDeltaM6Fn.name == "full_scale_delta_m6"
#guard m7BumpAnalyzedFn.name == "full_bump_analyzed"
#guard (m7BumpExterns.map Extern.name) ==
  ["full_bump_var", "full_bump_decay", "full_queue_mtf"]
#guard (ppTModule m7BumpModule).isOk
#guard (PrintQbe.module m7BumpModule).isOk
#guard (ppModule (m7BumpFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7BumpFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7BumpFns.map (Fn.legal .x64AVX2))).isOk
#guard m7BumpFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

private def refKnuthStep (s : BitVec 64) : BitVec 64 :=
  s * 6364136223846793005#64 + 1442695040888963407#64

private def refKnuthSeq (n : Nat) (s0 : BitVec 64) : List (BitVec 64) :=
  match n with
  | 0 => []
  | k + 1 =>
    let s1 := refKnuthStep s0
    (s1 >>> 32) :: refKnuthSeq k s1

#guard (6364136223846793005#64 &&& 7#64) == 5#64
#guard (1442695040888963407#64 &&& 1#64) == 1#64
#guard m7KnuthNext 0#64 == refKnuthStep 0#64
#guard m7KnuthNext 0#64 == 1442695040888963407#64
#guard (m7KnuthNext (m7KnuthNext 0#64)) == refKnuthStep (refKnuthStep 0#64)
#guard ((m7KnuthNext 0#64) >>> 32) == (refKnuthSeq 1 0#64).head!
#guard m7KnuthNext 0x123456789abcdef0#64 != 0x123456789abcdef0#64
#guard (refKnuthSeq 4 0#64).all (fun x => x.toNat < 2 ^ 32)
#guard bumpStampKey 4 [30#32, 10#32, 40#32, 20#32] 1#32 == (10, 1)
#guard bumpStampKey 4 [30#32, 10#32, 40#32, 20#32] 3#32 == (20, 3)
#guard (bumpStampKey 3 [10#32, 10#32, 5#32] 2#32).1 <
  (bumpStampKey 3 [10#32, 10#32, 5#32] 0#32).1
#guard (bumpStampKey 3 [10#32, 10#32, 5#32] 0#32).2 <
  (bumpStampKey 3 [10#32, 10#32, 5#32] 1#32).2

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem m7b_wf : ∀ f ∈ m7BumpFns, f.Wf := m7BumpFns_wf
theorem m7b_acyc : m7BumpModule.checkAcyclic = true := m7Bump_acyclic
theorem m7b_nd : (m7BumpSpecTable.map SpecEntry.name).Nodup := m7BumpSpecTable_nodup

theorem m7b_no_exit :
    ∀ f as bs xs m Q X X', m7BumpEnv f as bs xs m Q X → m7BumpEnv f as bs xs m Q X' :=
  m7BumpEnv_noExit

theorem m7b_rng_wp (Γ : Env) :
    ∀ a m Q X, fullRngNextSpec a m Q X → Func.wp Γ m7RngNextFn.body a m Q X :=
  m7RngNextFn_wp Γ

theorem m7b_rng_ex_wp (Γ : Env) :
    ∀ a m Q X, m7RngNextExactSpec a m Q X → Func.wp Γ m7RngNextFn.body a m Q X :=
  m7RngNextFn_wp_exact Γ

theorem m7b_log_wp (Γ : Env) :
    ∀ a m Q X, m7Log10Q16Spec a m Q X → Func.wp Γ full_log10_q16_m7_body a m Q X :=
  full_log10_q16_m7_wp Γ

theorem m7b_scale_wp (Γ : Env)
    (hLog : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7ScaleDeltaSpec a m Q X → Func.wp Γ m7ScaleDeltaFn.body a m Q X :=
  m7ScaleDeltaFn_wp Γ hLog

theorem m7b_scale_m6_wp (Γ : Env)
    (hLog : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7ScaleDeltaCompatSpec a m Q X → Func.wp Γ m7ScaleDeltaM6Fn.body a m Q X :=
  m7ScaleDeltaM6Fn_wp Γ hLog

theorem m7b_sift_wp (Γ : Env) :
    ∀ a m Q X, m7BumpSiftSpec a m Q X → Func.wp Γ full_bump_sift_m7_body a m Q X :=
  full_bump_sift_m7_wp Γ

theorem m7b_sort_wp (Γ : Env)
    (hSift : ∀ a m Q X, m7BumpSiftSpec a m Q X →
      Γ "full_bump_sift_m7" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m7BumpSortStampsSpec a m Q X →
      Func.wp Γ full_bump_sort_stamps_m7_body a m Q X :=
  full_bump_sort_stamps_m7_wp Γ hSift

theorem m7b_reasons_wp (Γ : Env) :
    ∀ a m Q X, m7BumpReasonsSpec a m Q X → Func.wp Γ full_bump_reasons_m7_body a m Q X :=
  full_bump_reasons_m7_wp Γ

theorem m7b_bump_wp (Γ : Env)
    (hReasons : ∀ a m Q X, m7BumpReasonsSpec a m Q X →
      Γ "full_bump_reasons_m7" [i64] [] a m Q X)
    (hSort : ∀ a m Q X, m7BumpSortStampsSpec a m Q X →
      Γ "full_bump_sort_stamps_m7" [i64, i64] [] a m Q X)
    (hBumpVar : ∀ a m Q X, fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hDecay : ∀ a m Q X, fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X)
    (hQmtf : ∀ a m Q X, fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBumpAnalyzedSpec a m Q X →
      Func.wp Γ m7BumpAnalyzedFn.body a m Q X :=
  m7BumpAnalyzedFn_wp Γ hReasons hSort hBumpVar hDecay hQmtf

theorem m7b_mod_ok : ModuleOk m7BumpEnv m7BumpModule := m7Bump_moduleOk

theorem m7b_nv_rng :
    Func.wp m7BumpEnv full_rng_next_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' =>
        nvOneLitF0.Unsat ∧
        r = (6364136223846793005#64 * nvOneLitState.scratch.rng_state +
          1442695040888963407#64) >>> (32 : Nat) ∧
        ∃ s' : FullState,
          s'.core = nvOneLitState.core ∧
          s'.scratch.rng_state =
            6364136223846793005#64 * nvOneLitState.scratch.rng_state + 1442695040888963407#64 ∧
          FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_rng_next

theorem m7b_nv_scale :
    Func.wp m7BumpEnv full_scale_delta_m7_body (nvOneLitCfg.hdr, 100#64, ()) nvOneLitMem
      (fun (r, ()) m' => nvOneLitF0.Unsat ∧ 100 ≤ r.toNat ∧ FullMem nvOneLitCfg nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_m7_scale_delta

theorem m7b_nv_bump :
    Func.wp m7BumpEnv full_bump_analyzed_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun _ m' =>
        nvOneLitF0.Unsat ∧
        ∃ s' : FullState,
          s'.LengthsOk nvOneLitCfg ∧ FullAnaMarksCov nvOneLitCfg s' ∧
          FullExtScratchPres nvOneLitState s' ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_bump_analyzed

end AuditSpec

end LeanQbeTest.T.KissatM7BumpTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7b_a_wf := @LeanQbeTest.T.KissatM7BumpTest.m7b_wf
abbrev m7b_a_acyc := @LeanQbeTest.T.KissatM7BumpTest.m7b_acyc
abbrev m7b_a_nd := @LeanQbeTest.T.KissatM7BumpTest.m7b_nd
abbrev m7b_a_nx := @LeanQbeTest.T.KissatM7BumpTest.m7b_no_exit
abbrev m7b_a_rng := @LeanQbeTest.T.KissatM7BumpTest.m7b_rng_wp
abbrev m7b_a_rngx := @LeanQbeTest.T.KissatM7BumpTest.m7b_rng_ex_wp
abbrev m7b_a_log := @LeanQbeTest.T.KissatM7BumpTest.m7b_log_wp
abbrev m7b_a_scl := @LeanQbeTest.T.KissatM7BumpTest.m7b_scale_wp
abbrev m7b_a_scl6 := @LeanQbeTest.T.KissatM7BumpTest.m7b_scale_m6_wp
abbrev m7b_a_sift := @LeanQbeTest.T.KissatM7BumpTest.m7b_sift_wp
abbrev m7b_a_sort := @LeanQbeTest.T.KissatM7BumpTest.m7b_sort_wp
abbrev m7b_a_rsns := @LeanQbeTest.T.KissatM7BumpTest.m7b_reasons_wp
abbrev m7b_a_bump := @LeanQbeTest.T.KissatM7BumpTest.m7b_bump_wp
abbrev m7b_a_mod := @LeanQbeTest.T.KissatM7BumpTest.m7b_mod_ok
abbrev m7b_a_nv_r := @LeanQbeTest.T.KissatM7BumpTest.m7b_nv_rng
abbrev m7b_a_nv_s := @LeanQbeTest.T.KissatM7BumpTest.m7b_nv_scale
abbrev m7b_a_nv_b := @LeanQbeTest.T.KissatM7BumpTest.m7b_nv_bump

#print axioms m7b_a_wf
#print axioms m7b_a_acyc
#print axioms m7b_a_nd
#print axioms m7b_a_nx
#print axioms m7b_a_rng
#print axioms m7b_a_rngx
#print axioms m7b_a_log
#print axioms m7b_a_scl
#print axioms m7b_a_scl6
#print axioms m7b_a_sift
#print axioms m7b_a_sort
#print axioms m7b_a_rsns
#print axioms m7b_a_bump
#print axioms m7b_a_mod
#print axioms m7b_a_nv_r
#print axioms m7b_a_nv_s
#print axioms m7b_a_nv_b
