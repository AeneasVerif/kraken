module

public import LeanQbe.T.Examples.Kissat.FullM7FidelitySched
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas

import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 High-Fidelity Schedule & Preprocessing Proofs (`FullM7FidelitySchedProof`)

M1-clean, UNSAT-only proof module (`public section`, `0` `@[expose]`, `XPost := False`, `0` SAT
model-finding proofs, standard `[propext, Classical.choice, Quot.sound]` axioms):
1. `full_ilog10_fid_exact_wp` (`fidIlog10ExactSpec`) & `full_ilog10_fid_wp` (`Full.fullIlog10Spec`).
2. `full_nlogpown_fid_wp` (`fidNlogpownSpec`, upstream `NLOGN`/`NLOG2N`/`NLOG3N`).
3. `full_calc_max_v_fid_wp` (`Full.fullCalcMaxVSpec`, uncapped dynamic `bva_cap ≤ 4096`).
4. `full_reduce_fid_wp` (`FullM6Orch.m6ReduceSpec` on `FullM6HdrInvW` / `FullM6HdrMem`).
5. `full_probe_fid_wp` (`fidProbeSpec` on `FullM6HdrInv` / `FullM6HdrMem`).
6. `full_eliminate_fid_wp` (`FullFastSched.schedEliminateSpec` on `FullSparseInv` / `FullMem`).
7. `full_preprocess_fid_wp` (`FullM6.fullM6PreprocessSpec` on `FullM6HdrInv` / `FullM6HdrMem`).
8. Closed `38`-row `fidSchedSpecTable`, `fidSchedEnv`, `fidSchedEnv_noExit`, `fidSched_tableImpl`,
   `fidSched_moduleOk`, and concrete `Mem 64` UNSAT non-vacuity (`nv_fid_*`, `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelitySched

open Std Std.Sat Std.ExtHashMap LeanQbe.T.Examples.LratBytes
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics
open Kraken.Bedrock2.Test

/-! ## 1. High-Fidelity Specifications -/

/-- Exact mathematical contract for `full_ilog10_fid`: `r = max 1 (floor (log10 x))`, capped at
`19` (`1` for `0 ≤ x < 100`, `k` for `10^k ≤ x < 10^(k+1)`, `19` for `x ≥ 10^19`). -/
def fidIlog10ExactSpec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64,
    1 ≤ r.toNat → r.toNat ≤ 19 → (r.toNat = 1 ∨ 10 ^ r.toNat ≤ x.toNat) →
    (r.toNat < 19 → x.toNat < 10 ^ (r.toNat + 1)) → Q (r, ()) m

/-- Exact overflow-safe `NLOGN`/`NLOG2N`/`NLOG3N` specification matching upstream `kimits.c`. -/
def fidNlogpownSpec : Spec [i64, i64, i64] [i64] := fun (base, count, exp, ()) m Q _ =>
  ∀ r : BitVec 64,
    (∃ lg : Nat, 1 ≤ lg ∧ lg ≤ 19 ∧
      (lg = 1 ∨ 10 ^ lg ≤ min (count.toNat + 9) (2 ^ 64 - 1)) ∧
      (lg < 19 → min (count.toNat + 9) (2 ^ 64 - 1) < 10 ^ (lg + 1)) ∧
      r.toNat = min base.toNat 10000 * min count.toNat 100000000 * lg ^ min exp.toNat 3) →
    Q (r, ()) m

/-- `M6Hdr`-aware probe-tail specification matching `FullM6Orch.m6ProbeTailSpec`. -/
def fidProbeTailSpec : Spec [i64, i64] [i64] := fun (h, _dticks, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem fidProbeTailSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {dticks : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    fidProbeTailSpec (c.hdr, dticks, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

/-- `M6Hdr`-aware probing specification matching `FullM6Orch.m6ProbeSpec`. -/
def fidProbeSpec : Spec [i64, .bool] [i64] := fun (h, _initial, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem fidProbeSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {initial : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    fidProbeSpec (c.hdr, initial, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

theorem fidProbeSpec_elim {h : BitVec 64} {initial : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : fidProbeSpec (h, initial, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

/-! ## 2. `full_ilog10_fid_wp` & `full_nlogpown_fid_wp` -/

private theorem fid_pow10_le19 {k : Nat} (hk : k ≤ 19) : 10 ^ k < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) (by decide)

theorem full_ilog10_fid_exact_wp (Γ : Env) :
    ∀ a m Q X, fidIlog10ExactSpec a m Q X → Func.wp Γ full_ilog10_fid_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_ilog10_fid_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (r, p, ()) m1 => m1 = m ∧ 1 ≤ r.toNat ∧ r.toNat ≤ 19 ∧ p.toNat = 10 ^ r.toNat ∧
      (r.toNat = 1 ∨ 10 ^ r.toNat ≤ x.toNat))
    (fun (r, _, ()) _ => 19 - r.toNat)
    (fun J hJ => by
      c0_hsteps_nogrp
      exact hJ (1#64, 10#64, ()) m ⟨rfl, by decide, by decide, by decide, Or.inl rfl⟩)
    (fun J (r, p, ()) m1 ⟨hm1, hr1, hr19, hp, hpow⟩ hJ => ?_)
  subst m1
  c0_hsteps_nogrp
  · have hr_lt19 : r.toNat < 19 := by
      have h19 : (19#64 : BitVec 64).toNat = 19 := rfl; c0_bound
    have hp_le : p.toNat ≤ x.toNat / 10 := by
      have hdiv : (x / 10#64).toNat = x.toNat / 10 := by rw [BitVec.toNat_udiv]; rfl
      rw [← hdiv]; c0_bound
    have hr1_eq : (r + 1#64).toNat = r.toNat + 1 := by c0_bound
    have hp10_lt : p.toNat * 10 < 2 ^ 64 := by
      rw [hp, ← Nat.pow_succ]; exact fid_pow10_le19 (by omega)
    have hp10_eq : (p * 10#64).toNat = 10 ^ (r.toNat + 1) := by
      rw [BitVec.toNat_mul, show (10#64 : BitVec 64).toNat = 10 from rfl,
        Nat.mod_eq_of_lt hp10_lt, hp, Nat.pow_succ]
    have hpow' : 10 ^ (r.toNat + 1) ≤ x.toNat := by rw [Nat.pow_succ, ← hp]; omega
    refine hJ (r + 1#64, p * 10#64, ()) m (by dsimp only; rw [hr1_eq]; omega)
      ⟨rfl, by rw [hr1_eq]; omega, by rw [hr1_eq]; omega, hr1_eq ▸ hp10_eq,
        Or.inr (hr1_eq ▸ hpow')⟩
  · have hlt_imp : r.toNat < 19 → x.toNat < 10 ^ (r.toNat + 1) := fun hr19' => by
      have hdiv : (x / 10#64).toNat = x.toNat / 10 := by rw [BitVec.toNat_udiv]; rfl
      have hnot : ¬ (x.toNat / 10 ≥ p.toNat) := fun hge => by
        have hlt : p ≤ x / 10#64 := BitVec.le_def.mpr (by rw [hdiv]; exact hge); contradiction
      rw [hp] at hnot; rw [Nat.pow_succ]; omega
    exact hQ r hr1 hr19 hpow hlt_imp
  · have hlt_imp : r.toNat < 19 → x.toNat < 10 ^ (r.toNat + 1) := fun hr19' => by
      have hdiv : (x / (10 : BitVec 64)).toNat = x.toNat / 10 := by
        rw [BitVec.toNat_udiv]; rfl
      have hnot : ¬ (x.toNat / 10 ≥ p.toNat) := fun hge =>
        absurd (BitVec.le_def.mpr (by rw [hdiv]; exact hge)) hc
      rw [hp] at hnot; rw [Nat.pow_succ]; omega
    exact hQ r hr1 hr19 hpow hlt_imp

theorem full_ilog10_fid_wp (Γ : Env) :
    ∀ a m Q X, fullIlog10Spec a m Q X → Func.wp Γ full_ilog10_fid_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  exact full_ilog10_fid_exact_wp Γ (x, ()) m Q X (fun r h1 h19 _ _ => hQ r h1 h19)

theorem full_nlogpown_fid_wp (Γ : Env)
    (hIlog : ∀ a m Q X, fidIlog10ExactSpec a m Q X →
      Γ "full_ilog10_fid" [i64] [i64] a m Q X) :
    ∀ a m Q X, fidNlogpownSpec a m Q X → Func.wp Γ full_nlogpown_fid_body a m Q X := by
  rintro ⟨base, count, exp, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_nlogpown_fid_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (arg, ()) ma => ma = m ∧ arg.toNat = min (count.toNat + 9) (2 ^ 64 - 1))
    ?_ (fun Jarg hJarg => by
      c0_hsteps_nogrp
      · have hgt : (2 ^ 64 - 10 : Nat) < count.toNat := by
          have : ((0xFFFFFFFFFFFFFFFF#64 : BitVec 64) - 9#64) < count := ‹_›
          have hm := BitVec.lt_def.mp this
          simpa using hm
        refine hJarg (0xFFFFFFFFFFFFFFFF#64, ()) m ⟨rfl, ?_⟩
        rw [show (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 from rfl]; omega
      · have hle : count.toNat ≤ 2 ^ 64 - 10 := by
          have hnot : ¬ (((0xFFFFFFFFFFFFFFFF#64 : BitVec 64) - 9#64) < count) := ‹_›
          have hm : count.toNat ≤ ((0xFFFFFFFFFFFFFFFF#64 : BitVec 64) - 9#64).toNat :=
            Nat.le_of_not_lt (fun h => hnot (BitVec.lt_def.mpr h))
          simpa using hm
        have hadd : (count + 9#64).toNat = count.toNat + 9 := by
          rw [BitVec.toNat_add, show (9#64 : BitVec 64).toNat = 9 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        refine hJarg (count + 9#64, ()) m ⟨rfl, ?_⟩; omega)
  rintro _ ⟨arg, ⟨⟩⟩ ma ⟨hma, harg⟩; subst ma
  c0_hsteps_nogrp
  c0_call hIlog
  intro lg hlg1 hlg19 hlg_pow hlg_lt
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (cc, ()) mc => mc = m ∧ cc.toNat = min count.toNat 100000000)
    (fun _ (cc, ()) mc ⟨hmc, hcc⟩ => by
      subst mc; c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun (bc, ()) mb => mb = m ∧ bc.toNat = min base.toNat 10000)
        (fun _ (bc, ()) mb ⟨hmb, hbc⟩ => by
          subst mb; c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (e, ()) me => me = m ∧ e.toNat = min exp.toNat 3)
            (fun _ (e, ()) me ⟨hme, he⟩ => by
              subst me; c0_hsteps_nogrp
              refine wp_loop_inv
                (fun (p, i, ()) m1 => m1 = m ∧ i.toNat ≤ e.toNat ∧
                  p.toNat = lg.toNat ^ i.toNat)
                (fun (_, i, ()) _ => e.toNat - i.toNat)
                (fun JL hJL => by
                  c0_hsteps_nogrp
                  exact hJL (1#64, 0#64, ()) m ⟨rfl, Nat.zero_le _, rfl⟩)
                (fun JL (p, i, ()) m1 ⟨hm1, hi_le, hp⟩ hJL => ?_)
              subst m1
              c0_hsteps_nogrp
              · have hilt : i.toNat < e.toNat := by c0_bound
                have hp_lt : p.toNat * lg.toNat < 2 ^ 64 := by
                  rw [hp]
                  have h1 : lg.toNat ^ i.toNat ≤ 19 ^ 2 :=
                    Nat.le_trans (Nat.pow_le_pow_left hlg19 _)
                      (Nat.pow_le_pow_right (by omega) (by omega))
                  have h2 : lg.toNat ≤ 19 := hlg19
                  calc lg.toNat ^ i.toNat * lg.toNat ≤ 19 ^ 2 * 19 := Nat.mul_le_mul h1 h2
                    _ < 2 ^ 64 := by decide
                have hp_eq : (p * lg).toNat = lg.toNat ^ (i.toNat + 1) := by
                  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hp_lt, hp, Nat.pow_succ]
                have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                exact hJL (p * lg, i + 1#64, ()) m (by dsimp only; omega)
                  ⟨rfl, by omega, by rw [hi1]; exact hp_eq⟩
              · have hi_eq : i.toNat = e.toNat := by c0_bound
                have hp_eq : p.toNat = lg.toNat ^ min exp.toNat 3 := by
                  rw [hp, hi_eq, he]
                have hpow_le : p.toNat ≤ 19 ^ 3 := by
                  rw [hp_eq]
                  exact Nat.le_trans (Nat.pow_le_pow_left hlg19 _)
                    (Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _))
                have hbc_cc_lt : bc.toNat * cc.toNat < 2 ^ 64 := by
                  have h1 : bc.toNat ≤ 10000 := by omega
                  have h2 : cc.toNat ≤ 100000000 := by omega
                  calc bc.toNat * cc.toNat ≤ 10000 * 100000000 := Nat.mul_le_mul h1 h2
                    _ < 2 ^ 64 := by decide
                have hmul1 : (bc * cc).toNat = bc.toNat * cc.toNat := by
                  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hbc_cc_lt]
                have hprod_lt : (bc * cc).toNat * p.toNat < 2 ^ 64 := by
                  rw [hmul1]
                  have h1 : bc.toNat * cc.toNat ≤ 10000 * 100000000 :=
                    Nat.mul_le_mul (by omega) (by omega)
                  calc bc.toNat * cc.toNat * p.toNat
                      ≤ (10000 * 100000000) * 19 ^ 3 := Nat.mul_le_mul h1 hpow_le
                    _ < 2 ^ 64 := by decide
                have hmul2 : (bc * cc * p).toNat =
                    min base.toNat 10000 * min count.toNat 100000000 * lg.toNat ^ min exp.toNat 3 :=
                  by rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hprod_lt, hmul1, hbc, hcc, hp_eq]
                exact hQ (bc * cc * p) ⟨lg.toNat, hlg1, hlg19, harg ▸ hlg_pow,
                  fun h => harg ▸ hlg_lt h, hmul2⟩)
            (fun Je hJe => by
              c0_hsteps_nogrp
              · have : 3 < exp.toNat := by c0_bound
                exact hJe (3#64, ()) m
                  ⟨rfl, by simp [show (3#64 : BitVec 64).toNat = 3 from rfl]; omega⟩
              · have : exp.toNat ≤ 3 := by c0_bound
                exact hJe (exp, ()) m ⟨rfl, by omega⟩))
        (fun Jb hJb => by
          c0_hsteps_nogrp
          · have : 10000 < base.toNat := by c0_bound
            exact hJb (10000#64, ()) m
              ⟨rfl, by simp [show (10000#64 : BitVec 64).toNat = 10000 from rfl]; omega⟩
          · have : base.toNat ≤ 10000 := by c0_bound
            exact hJb (base, ()) m ⟨rfl, by omega⟩))
    (fun Jc hJc => by
      c0_hsteps_nogrp
      · have : 100000000 < count.toNat := by c0_bound
        exact hJc (100000000#64, ()) m
          ⟨rfl, by simp [show (100000000#64 : BitVec 64).toNat = 100000000 from rfl]; omega⟩
      · have : count.toNat ≤ 100000000 := by c0_bound
        exact hJc (count, ()) m ⟨rfl, by omega⟩)

/-! ## 3. `full_calc_max_v_fid_wp` (Uncapped Dynamic BVA Cap `≤ 4096`) -/

section CalcMaxVProof

private abbrev fidBvaCap (avail mv nc f0 : Nat) : Nat :=
  if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
    min 4096 (((avail - f0) - nc * 48 - 4096) / 2688)
  else 0

private def fidCalcMaxV (avail mv nc f0 : Nat) : Nat :=
  let max_v := mv + fidBvaCap avail mv nc f0
  let fixed := fullFixedBytes max_v
  if avail < fixed ∨ avail - fixed < nc * 40 + 136 then mv else max_v

private theorem fidBvaCap_le (avail mv nc f0 : Nat) : fidBvaCap avail mv nc f0 ≤ 4096 := by
  unfold fidBvaCap; split <;> omega

private theorem fidCalcMaxV_fits {avail mv nc : Nat}
    (hfit : fullFixedBytes mv + nc * 40 + 136 ≤ avail) :
    fullFixedBytes (fidCalcMaxV avail mv nc (fullFixedBytes mv)) + nc * 40 + 136 ≤ avail := by
  unfold fidCalcMaxV; dsimp only; split <;> omega

private theorem fid_bv64_ofNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
private theorem fid_bv64_mul (x : BitVec 64) (k : Nat) :
    x * BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat * k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]
private theorem fid_bv64_ult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, fid_bv64_ofNat ha, fid_bv64_ofNat hb]
private theorem fid_bv64_sub {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by have := a.isLt; rw [BitVec.toNat_sub]; omega

private theorem fidCalcMaxV_eq1 {avail mv nc f0 : Nat}
    (hlt : avail < fullFixedBytes (mv + fidBvaCap avail mv nc f0)) :
    fidCalcMaxV avail mv nc f0 = mv := by
  unfold fidCalcMaxV; dsimp only; exact ite_eq_left_iff.mpr fun h => absurd (Or.inl hlt) h
private theorem fidCalcMaxV_eq2 {avail mv nc f0 : Nat}
    (hlt : avail - fullFixedBytes (mv + fidBvaCap avail mv nc f0) < nc * 40 + 136) :
    fidCalcMaxV avail mv nc f0 = mv := by
  unfold fidCalcMaxV; dsimp only; exact ite_eq_left_iff.mpr fun h => absurd (Or.inr hlt) h
private theorem fidCalcMaxV_eq3 {avail mv nc f0 : Nat}
    (h1 : ¬ avail < fullFixedBytes (mv + fidBvaCap avail mv nc f0))
    (h2 : ¬ avail - fullFixedBytes (mv + fidBvaCap avail mv nc f0) < nc * 40 + 136) :
    fidCalcMaxV avail mv nc f0 = mv + fidBvaCap avail mv nc f0 := by
  unfold fidCalcMaxV; dsimp only; exact ite_eq_right_iff.mpr fun h => absurd h (by omega)

private theorem full_calc_max_v_fid_post_wp (Γ : Env)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hQ : Q (BitVec.ofNat 64 (fidCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var mv,
        Arg.var (BitVec.ofNat 64 (fidBvaCap avail.toNat mv.toNat nc.toNat f0.toNat)), ()))
        fun p =>
      Expr.call "full_fixed_bytes" (as := [i64]) (bs := [i64]) (Arg.var p.fst, ()) fun p_1 =>
      Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var avail, Arg.var p_1.fst, ()))
        fun p_2 =>
      Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.var mv, ()))
        (Expr.let_ (Op.mk (.sub i64) (Arg.var avail, Arg.var p_1.fst, ())) fun p_2 =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 40, ())) fun p_3 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_3.fst, Arg.imm 136, ())) fun p_4 =>
          Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
            (Arg.var p_2.fst, Arg.var p_4.fst, ())) fun p_2 =>
          Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.var mv, ()))
            (Expr.ret (Arg.var p.fst, ())))) m := by
  let bva := fidBvaCap avail.toNat mv.toNat nc.toNat f0.toNat
  have hbva_le : bva ≤ 4096 := fidBvaCap_le _ _ _ _
  have hmv_b := hmv; have hnc_b := hnc; unfold dimacsBound at hmv_b hnc_b
  let max_v := mv.toNat + bva
  have hmax_bd : max_v < 2 * dimacsBound := by unfold dimacsBound; omega
  have hfx_lt : fullFixedBytes max_v < 2 ^ 64 := by have := fullFixedBytes_lt hmax_bd; omega
  have hmv_add : mv + BitVec.ofNat 64 bva = BitVec.ofNat 64 max_v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, fid_bv64_ofNat (by omega), fid_bv64_ofNat (by omega),
      Nat.mod_eq_of_lt (by omega)]
  c0_hsteps_nogrp; rw [hmv_add]
  refine wp_call_of_spec _ _ (hFixed _ _ _ _ ⟨?_, ?_⟩)
  · dsimp only [Arg.val_var]; rw [fid_bv64_ofNat (by omega)]; exact hmax_bd
  · dsimp only [Arg.val_var]; rw [fid_bv64_ofNat (by omega)]
    have hav_lt := avail.isLt
    c0_hsteps_nogrp
    · have hlt1 : avail.toNat < fullFixedBytes max_v := by
        rwa [Nat.mod_eq_of_lt hfx_lt] at hc
      rw [fidCalcMaxV_eq1 hlt1, BitVec.ofNat_toNat] at hQ; exact hQ
    · rename_i hge1; rw [Nat.mod_eq_of_lt hfx_lt] at hge1
      have hm1 : (2 ^ 64 - fullFixedBytes max_v + avail.toNat) % 2 ^ 64 =
          avail.toNat - fullFixedBytes max_v := by omega
      have hm2 : (nc.toNat * 40 + 136) % 2 ^ 64 = nc.toNat * 40 + 136 := Nat.mod_eq_of_lt (by omega)
      have hlt2 : avail.toNat - fullFixedBytes max_v < nc.toNat * 40 + 136 := by
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt, hm1, hm2] using hc
      rw [fidCalcMaxV_eq2 hlt2, BitVec.ofNat_toNat] at hQ; exact hQ
    · rename_i hge1; rw [Nat.mod_eq_of_lt hfx_lt] at hge1
      have hm1 : (2 ^ 64 - fullFixedBytes max_v + avail.toNat) % 2 ^ 64 =
          avail.toNat - fullFixedBytes max_v := by omega
      have hm2 : (nc.toNat * 40 + 136) % 2 ^ 64 = nc.toNat * 40 + 136 := Nat.mod_eq_of_lt (by omega)
      have hge2 : ¬ avail.toNat - fullFixedBytes max_v < nc.toNat * 40 + 136 := by
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt, hm1, hm2] using hc
      rw [fidCalcMaxV_eq3 hge1 hge2] at hQ; exact hQ

open FullParseInitTactics in
private theorem fid_bva_ult_eq (avail f0 nc : Val i64) (hfle : f0.toNat ≤ avail.toNat)
    (hnc : nc.toNat < dimacsBound) :
    ((nc * (48 : BitVec 64) + 8192).ult (avail - f0)) =
      decide (nc.toNat * 48 + 8192 < avail.toNat - f0.toNat) := by
  have hnc_b := hnc; unfold dimacsBound at hnc_b; have hav_lt := avail.isLt
  have hrem_eq : avail - f0 = BitVec.ofNat 64 (avail.toNat - f0.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [fid_bv64_sub hfle, fid_bv64_ofNat (by omega)]
  have hnc48 : nc * (48 : BitVec 64) + (8192 : BitVec 64) =
      BitVec.ofNat 64 (nc.toNat * 48 + 8192) := by
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, fid_bv64_mul]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, fid_bv64_ofNat (by omega),
      show (8192 : BitVec 64).toNat = 8192 from rfl, fid_bv64_ofNat (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hrem_eq, hnc48, fid_bv64_ult (by omega) (by omega)]

private abbrev fidBvaMinExpr (nc remv : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_4 =>
    Expr.let_ (Op.mk (.sub i64) (Arg.var remv, Arg.var p_4.fst, ())) fun p_5 =>
    Expr.let_ (Op.mk (.sub i64) (Arg.var p_5.fst, Arg.imm 4096, ())) fun p_6 =>
    Expr.let_ (Op.mk (.udiv 64) (Arg.var p_6.fst, Arg.imm 2688, ())) fun p_7 =>
    Expr.group (sig := [[i64]])
      (fun _ => Blocks.cons (fun p_8 => Expr.jump J (Arg.var p_8.fst, ())) Blocks.nil)
      fun Js =>
        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.imm 4096, Arg.var p_7.fst, ())) fun p =>
        Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 4096, ()))
          (Expr.jump Js.fst (Arg.var p_7.fst, ()))

open FullParseInitTactics in
private theorem full_calc_bva_min_fid_wp (Γ : Env)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J : Cont [i64]}
    (hmv_ge : 2 ≤ mv.toNat) (hnc : nc.toNat < dimacsBound) (hfle : f0.toNat ≤ avail.toNat)
    (hgt : nc.toNat * 48 + 8192 < avail.toNat - f0.toNat)
    (hJ : ∀ xs m_1, xs.1 = BitVec.ofNat 64 (fidBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧
      m_1 = m → J xs m_1) :
    wp Γ Q X (fidBvaMinExpr nc (BitVec.ofNat 64 (avail.toNat - f0.toNat)) J) m := by
  have hnc_b := hnc; unfold dimacsBound at hnc_b; have hav_lt := avail.isLt
  let rem0 := avail.toNat - f0.toNat
  let max_bva := (rem0 - nc.toNat * 48 - 4096) / 2688
  dsimp only [fidBvaMinExpr]; fp_head_steps
  have h48 : (nc * (48 : BitVec 64)).toNat = nc.toNat * 48 := by
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, fid_bv64_mul,
      fid_bv64_ofNat (by omega)]
  have hsub1 : (BitVec.ofNat 64 rem0 - nc * (48 : BitVec 64)).toNat = rem0 - nc.toNat * 48 := by
    rw [fid_bv64_sub (by rw [fid_bv64_ofNat (by dsimp [rem0]; omega), h48]; dsimp [rem0]; omega),
      fid_bv64_ofNat (by dsimp [rem0]; omega), h48]
  have hsub3 : BitVec.ofNat 64 rem0 - nc * (48 : BitVec 64) - (4096 : BitVec 64) =
      BitVec.ofNat 64 (rem0 - nc.toNat * 48 - 4096) := by
    apply BitVec.eq_of_toNat_eq; have h4096 : (4096 : BitVec 64).toNat = 4096 := rfl
    rw [fid_bv64_sub (by rw [hsub1, h4096]; dsimp [rem0]; omega), hsub1, h4096,
      fid_bv64_ofNat (by dsimp [rem0]; omega)]
  rw [hsub3]; apply wp_udiv_of
  · dsimp only [Arg.val_imm]; intro h; have := congrArg BitVec.toNat h; simp at this
  · dsimp only [Arg.val_var, Arg.val_imm]
    have hmb64 : max_bva < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by dsimp [rem0]; omega)
    have hdiv_eq : BitVec.ofNat 64 (rem0 - nc.toNat * 48 - 4096) / (2688 : BitVec 64) =
        BitVec.ofNat 64 max_bva := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_udiv, fid_bv64_ofNat (by dsimp [rem0]; omega),
        show (2688 : BitVec 64).toNat = 2688 from rfl, fid_bv64_ofNat hmb64]
    rw [hdiv_eq]
    refine wp_join_group (ts := [i64]) (fun v mx =>
      v.1 = BitVec.ofNat 64 (fidBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧ mx = m) ?_ ?_
    · rintro _ ⟨bx_v, ⟨⟩⟩ mx ⟨rfl, rfl⟩
      simp only [Blocks.get_here]; fp_head_steps; exact hJ (_, ()) _ ⟨rfl, rfl⟩
    · intro Jm hJm; fp_head_steps
      rw [show (4096 : BitVec 64) = BitVec.ofNat 64 4096 from rfl, fid_bv64_ult (by omega) hmb64]
      refine wp_jnz_of (fun hclt => ?_) (fun hcge => ?_)
      · dsimp only [Arg.val_var] at hclt; rw [decide_eq_true_eq] at hclt; fp_head_steps
        refine hJm (_, ()) m ⟨?_, rfl⟩; unfold fidBvaCap
        rw [ite_eq_left_iff.mpr fun h => absurd (And.intro hmv_ge hgt) h]
        exact congrArg (BitVec.ofNat 64) (Nat.min_eq_left (Nat.le_of_lt hclt)).symm
      · dsimp only [Arg.val_var] at hcge; rw [decide_eq_false_iff_not] at hcge; fp_head_steps
        refine hJm (_, ()) m ⟨?_, rfl⟩; unfold fidBvaCap
        rw [ite_eq_left_iff.mpr fun h => absurd (And.intro hmv_ge hgt) h]
        exact congrArg (BitVec.ofNat 64) (Nat.min_eq_right (Nat.le_of_not_gt hcge)).symm

open FullParseInitTactics in
private theorem full_calc_max_v_fid_bva_wp (Γ : Env)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J : Cont [i64]}
    (_hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound) (hfle : f0.toNat ≤ avail.toNat)
    (hJ : ∀ xs m_1, xs.1 = BitVec.ofNat 64 (fidBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧
      m_1 = m → J xs m_1) :
    wp Γ Q X (Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl) (Arg.var mv, Arg.imm 2, ())) fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_1 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_1.fst, Arg.imm 8192, ())) fun p_2 =>
          Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var (avail - f0), Arg.var p_2.fst, ()))
            fun p_3 =>
            Expr.jnz (Arg.var p_3.fst) (fidBvaMinExpr nc (avail - f0) J)
              (Expr.jump J (Arg.imm 0, ())))
        (Expr.jump J (Arg.imm 0, ()))) m := by
  have hav_lt := avail.isLt
  have hrem_eq : avail - f0 = BitVec.ofNat 64 (avail.toNat - f0.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [fid_bv64_sub hfle, fid_bv64_ofNat (by omega)]
  fp_head_steps
  have hule2 : ((2 : BitVec 64).ule mv) = decide (2 ≤ mv.toNat) := by simp [BitVec.ule]
  rw [hule2]
  refine wp_jnz_of (fun hmv_ge => ?_) (fun hmv_lt => ?_)
  · dsimp only [Arg.val_var] at hmv_ge; rw [decide_eq_true_eq] at hmv_ge; fp_head_steps
    rw [fid_bva_ult_eq avail f0 nc hfle hnc]
    refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
    · dsimp only [Arg.val_var] at hgt; rw [decide_eq_true_eq] at hgt; fp_head_steps
      rw [hrem_eq]; exact full_calc_bva_min_fid_wp Γ hmv_ge hnc hfle hgt hJ
    · dsimp only [Arg.val_var] at hle; rw [decide_eq_false_iff_not] at hle; fp_head_steps
      refine hJ (0#64, ()) m ⟨?_, rfl⟩; unfold fidBvaCap
      rw [ite_eq_right_iff.mpr fun h => absurd h.2 hle]
  · dsimp only [Arg.val_var] at hmv_lt; rw [decide_eq_false_iff_not] at hmv_lt; fp_head_steps
    refine hJ (0#64, ()) m ⟨?_, rfl⟩; unfold fidBvaCap
    rw [ite_eq_right_iff.mpr fun h => absurd h.1 hmv_lt]

private theorem full_calc_max_v_fid_exact_wp (Γ : Env)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hf0 : f0.toNat = fullFixedBytes mv.toNat)
    (hle : f0.toNat + nc.toNat * 40 + 136 ≤ avail.toNat)
    (hQ : Q (BitVec.ofNat 64 (fidCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    Func.wp Γ full_calc_max_v_fid_body (avail, mv, nc, f0, ()) m Q X := by
  unfold Func.wp full_calc_max_v_fid_body; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun v mb =>
    v.1 = BitVec.ofNat 64 (fidBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧ mb = m) ?_ ?_
  · rintro _ ⟨bv_v, ⟨⟩⟩ mb ⟨rfl, rfl⟩
    simp only [Blocks.get_here]; exact full_calc_max_v_fid_post_wp Γ hFixed hmv hnc hQ
  · intro J hJ; exact full_calc_max_v_fid_bva_wp Γ hmv hnc (by omega) hJ

theorem full_calc_max_v_fid_wp (Γ : Env)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_fid_body a m Q X := by
  rintro ⟨avail, mv, nc, f0, ⟨⟩⟩ m Q X ⟨hmv, hnc, hf0, hle, hQ⟩
  have hbva_le := fidBvaCap_le avail.toNat mv.toNat nc.toNat f0.toNat
  have hmv_b : mv.toNat < 2 ^ 28 := hmv; have hnc_b : nc.toNat < 2 ^ 28 := hnc
  have hret_lt : fidCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat < 2 * dimacsBound := by
    unfold fidCalcMaxV dimacsBound at *; dsimp only; split <;> omega
  have hret_toNat := fid_bv64_ofNat (n := fidCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat)
    (by unfold dimacsBound at hret_lt; omega)
  refine full_calc_max_v_fid_exact_wp Γ hFixed hmv hnc hf0 hle ?_
  refine hQ _ (by rw [hret_toNat]; unfold fidCalcMaxV; dsimp only; split <;> omega)
    (by rw [hret_toNat]; exact hret_lt) (by rw [hret_toNat, hf0]; exact fidCalcMaxV_fits (by omega))

end CalcMaxVProof

/-! ## 4. `full_reduce_fid_wp` (`FullM6Orch.m6ReduceSpec`) -/

section ReduceFid

private theorem fid_arenaVarsNodup_perm {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hnd : FullArenaVarsNodup s) :
    FullArenaVarsNodup s' := by
  intro r hr hgb; change r ∈ fullArenaClauseRefs s' at hr
  have hmem : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rw [hap.2.1] at hr; exact hr
  have hperm := hap.2.2 r hmem; unfold fullArenaClauseGarb at hgb; rw [hperm.2.1] at hgb
  exact (List.Perm.map (fun x => x / 2) hperm.2.2).nodup_iff.mpr (hnd r hmem hgb)

private structure FidRedSt (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (ext : List (BitVec 64))
    (st : FullState) (ml : Mem 64) : Prop where
  inv : FullM6HdrInvW c F0 F_cur ext st
  cl : st.core.cur_level ≤ s.core.cur_level
  fu : st.core.fuel.toNat ≤ s.core.fuel.toNat
  cv : st.core.cur_vars = s.core.cur_vars
  tmp : st.core.tmp = s.core.tmp
  tl : st.core.tmp_len = s.core.tmp_len
  ws2 : st.scratch.work_stk2 = s.scratch.work_stk2
  pos : 0 < st.core.cur_level →
    st.core.cur_level = s.core.cur_level ∧ st.core.vals = s.core.vals ∧
    st.core.lvl = s.core.lvl ∧ st.core.trl = s.core.trl ∧
    st.core.trail_pos = s.core.trail_pos ∧ st.core.trail_end = s.core.trail_end
  mem : (FullM6HdrMem c ext st ⋆ R) ml

private theorem fidRedSt_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    FidRedSt c F0 F_cur s R ext s m :=
  ⟨hinv, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hm⟩

private theorem fidRedSt_with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : FidRedSt c F0 F_cur s R ext st ml) {sc' : FullScratch}
    (hsc : sc'.LengthsOk c) (hll : sc'.last_learned = st.scratch.last_learned)
    (hext : sc'.extend_len = st.scratch.extend_len) (hws2 : sc'.work_stk2 = st.scratch.work_stk2)
    {ml' : Mem 64} (hm' : (FullM6HdrMem c ext { st with scratch := sc' } ⋆ R) ml') :
    FidRedSt c F0 F_cur s R ext { st with scratch := sc' } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk ⟨⟨hsp.1.core_ok, hsc⟩, hsp.2.1, hsp.2.2.1,
      hsp.2.2.2.1, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll, hext⟩ (fun _ hr => hr),
      hsp.2.2.2.2.2⟩, hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hws2.trans hst.ws2, hst.pos, hm'⟩

private theorem fidRedSt_w2a {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st s' : FullState} {R : Mem 64 → Prop} {ext ext' : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : FidRedSt c F0 F_cur s R ext st ml) (hc : s'.core = st.core) (hl : s'.LengthsOk c)
    (hms : M6HdrScratchPres st s') (hext : M6HdrExtOk ext')
    (hm' : (FullM6HdrMem c ext' s' ⋆ R) ml') : FidRedSt c F0 F_cur s R ext' s' ml' := by
  have hsp := hst.inv.sparseW
  have hlm' : FullLitMarksClear c s' :=
    ⟨fun v hv => by rw [hc]; exact hsp.2.2.1.1 v hv, by simpa only [hc] using hsp.2.2.1.2⟩
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨hl, hc ▸ hsp.2.1, hlm',
      fun r hr hng => by
        change r ∈ fullArenaClauseRefs s' at hr; unfold fullArenaClauseRefs at hr
        unfold fullArenaClauseGarb at hng; unfold fullArenaClauseLits
        rw [hc] at hr hng ⊢; exact hsp.2.2.2.1 r hr hng,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 hms.extPres
        fun _ hr => by unfold fullArenaClauseRefs at hr ⊢; rwa [hc],
      hc ▸ hsp.2.2.2.2.2⟩
  exact ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hext hsp', hc ▸ hst.cl, hc ▸ hst.fu, hc ▸ hst.cv,
    hc ▸ hst.tmp, hc ▸ hst.tl, hms.ws2.trans hst.ws2,
    fun hpos => by rw [hc] at hpos ⊢; exact hst.pos hpos, hm'⟩

private theorem fidRedSt_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : FidRedSt c F0 F_cur s R ext st ml) (u' : BitVec 64)
    (hm' : (FullM6HdrMem c ext { st with core := { st.core with unflushed := u' } } ⋆ R) ml') :
    FidRedSt c F0 F_cur s R ext { st with core := { st.core with unflushed := u' } } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
    ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
      Full.FullDenseWatchHelpers.fullWitnessInv_with_unflushed hsp.2.1 u', hsp.2.2.1,
      hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩

private theorem fidRedSt_mark_reasons {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {ar' : List (BitVec 32)} (hst : FidRedSt c F0 F_cur s R ext st ml)
    (hlen' : ({ st with core := { st.core with arena := ar' } } : FullState).LengthsOk c)
    (hrefs : fullArenaClauseRefs { st with core := { st.core with arena := ar' } } =
      fullArenaClauseRefs st)
    (hper : ∀ r ∈ fullArenaClauseRefs st,
      fullArenaClauseSize { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseSize st r ∧
      fullArenaClauseGarb { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseGarb st r ∧
      fullArenaClauseLits { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseLits st r)
    (hw' : FullWitnessInv c F0 F_cur { st.core with arena := ar' })
    (hm' : (FullM6HdrMem c ext { st with core := { st.core with arena := ar' } } ⋆ R) ml') :
    FidRedSt c F0 F_cur s R ext { st with core := { st.core with arena := ar' } } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk ⟨hlen', hw', hsp.2.2.1, fun r hr hng => by
      rw [hrefs] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
      exact hsp.2.2.2.1 r hr hng,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => by rwa [hrefs]),
      hsp.2.2.2.2.2⟩, hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩

private theorem fidRedSt_backtrack0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : FidRedSt c F0 F_cur s R ext st ml)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch} {m' : Mem 64} :
    let sB : FullState :=
      { core := { st.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
        scratch := sc' }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    sc'.last_learned = st.scratch.last_learned → sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (FullM6HdrMem c ext sB ⋆ R) m' → FidRedSt c F0 F_cur s R ext sB m' :=
  fun hlen' hw' hll' hext' hws2' hm' => have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll', hext'⟩ (fun _ hr => hr), hsp.2.2.2.2.2⟩,
    Nat.zero_le _, hst.fu, hst.cv, hst.tmp, hst.tl, hws2'.trans hst.ws2,
    (fun h => by cases h), hm'⟩

private theorem fid_call_fullBcpS15_red {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s st : FullState} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' → Γ f [i64] [i64] a m' Q' X')
    (hst : FidRedSt c F0 F_cur s R ext st ml) (hcl0 : st.core.cur_level = 0)
    (hk : ∀ r s' m', FidRedSt c F0 F_cur s R ext s' m' → s'.core.cur_level = 0 →
      st.core.trail_end ≤ s'.core.trail_end → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → st.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → F0.Unsat) → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := [i64]) args k) ml := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hst.inv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
    hsp.1, hsp.2.1, hsp.2.2.2.2.2, fullM6HdrMem_focus_full hst.mem, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hs' hw' hte hap _hdel hfu hr h0 h1 _h2 _hno hm'
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨hs', hw', hsp.2.2.1, fid_arenaVarsNodup_perm hap hsp.2.2.2.1,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr =>
        by unfold fullArenaClauseRefs at hr ⊢; rwa [hap.2.1],
      hsp.2.2.2.2.2⟩
  have hst' : FidRedSt c F0 F_cur s R ext s' m' :=
    ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hsp', hst.cl,
      Nat.le_trans hfu hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2,
      fun hpos => by change 0 < st.core.cur_level at hpos; omega, fullM6HdrMem_unfocus_full hm'⟩
  exact hk r s' m' hst' hcl0 hte.1 hr (fun h0eq hso => (h0 h0eq).2.1 hso)
    (fun h1eq => level0_unsat_of_conflict_okW hw' hcl0 (h1 h1eq).2.2)

private theorem fidRedSt_arena_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : FidRedSt c F0 F_cur s R ext st ml)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} {m' : Mem 64} :
    let sA : FullState :=
      { core :=
          { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core → FullArenaVarsNodup sA →
    FullLastLearnedWf sA → sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (0 < st.core.cur_level → vals' = st.core.vals ∧ lvl' = st.core.lvl ∧ trl' = st.core.trl ∧
      tp' = st.core.trail_pos ∧ te' = st.core.trail_end) →
    (FullM6HdrMem c ext sA ⋆ R) m' → FidRedSt c F0 F_cur s R ext sA m' := by
  intro sA hlenA hwA hndA hllA hextA hws2A hposA hm'
  have hsp := hst.inv.sparseW
  refine ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨hlenA, hwA, hsp.2.2.1, hndA, ⟨hllA, hextA ▸ hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hws2A.trans hst.ws2, fun hpos => ?_, hm'⟩
  obtain ⟨hv, hl, ht, htp, hte⟩ := hposA hpos
  obtain ⟨hcl, hv0, hl0, ht0, htp0, hte0⟩ := hst.pos hpos
  exact ⟨hcl, hv.trans hv0, hl.trans hl0, ht.trans ht0, htp.trans htp0, hte.trans hte0⟩

private def FidRedRefsOk (s : FullState) (rc : Nat) : Prop :=
  ∀ j < rc,
    let r := (s.scratch.red_refs[j]?.getD 0#32).toNat
    r ∈ fullArenaClauseRefs s ∧ (fullArenaHdr s r &&& 0x00200000#32) = 0#32

private theorem fidRedRefsOk_push {c : FullCfg} {s : FullState} {rc p : Nat}
    (hrr_len : s.scratch.red_refs.length = c.red_cap) (hrc_lt : rc < c.red_cap)
    (hp_lt32 : p < 2 ^ 32) (hp_mem : p ∈ fullArenaClauseRefs s)
    (hp_norsn : (fullArenaHdr s p &&& 0x00200000#32) = 0#32)
    (hprev : FidRedRefsOk s rc) :
    FidRedRefsOk { s with scratch :=
      { s.scratch with red_refs := s.scratch.red_refs.set rc (BitVec.ofNat 32 p) } } (rc + 1) := by
  intro j hj
  by_cases hje : j = rc
  · subst j
    have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[rc]? = some (BitVec.ofNat 32 p) :=
      List.getElem?_set_self (by omega)
    simpa [hget, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt32] using And.intro hp_mem hp_norsn
  · have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[j]? = s.scratch.red_refs[j]? :=
      List.getElem?_set_ne (Ne.symm hje)
    simpa [hget] using hprev j (by omega)

private theorem fidRedSt_update_used {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {p rc : Nat} {u : BitVec 32}
    (hst : FidRedSt c F0 F_cur s R ext st ml) (hrmL : FullReasonsMarked st)
    (hrrL : FidRedRefsOk st rc) (hp_in : p ∈ fullArenaClauseRefs st)
    (hp_ar : p < st.core.arena.length)
    (hm' : (FullM6HdrMem c ext
      { core := { st.core with
          arena := st.core.arena.set p
            ((st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))) }
        scratch := st.scratch } ⋆ R) ml') :
    let v' := (st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    let sU : FullState := { st with core := { st.core with arena := st.core.arena.set p v' } }
    FidRedSt c F0 F_cur s R ext sU ml' ∧ FullReasonsMarked sU ∧
    fullArenaClauseRefs sU = fullArenaClauseRefs st ∧ FidRedRefsOk sU rc ∧
    (fullArenaHdr sU p &&& 0x00200000#32) = (st.core.arena[p]'hp_ar &&& 0x00200000#32) := by
  intro v' sU
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[p]'hp_ar = fullArenaHdr st p := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
  have hup := Full.FullDenseWatchHelpers.updateUsed_preserves_fullWitnessInv hsp.1 hsp.2.1 hp_in u
  rw [← hhdr_eq] at hup
  obtain ⟨hlenU, hrefsU, hperU, hwU⟩ := hup
  have hndU : FullArenaVarsNodup sU := fun r hr hng => by
    rw [hrefsU] at hr; rw [(hperU r hr).2.1] at hng; rw [(hperU r hr).2.2.1]
    exact hsp.2.2.2.1 r hr hng
  have hspU : FullSparseInvW c F0 F_cur sU :=
    ⟨hlenU, hwU, hsp.2.2.1, hndU, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by rwa [hrefsU]), hsp.2.2.2.2.2⟩
  have hrmU : FullReasonsMarked sU := fun idx hidx hlp hlg => by
    have hne0 : st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun heq => by rw [heq] at hlg; revert hlg; decide
    have hrs := hsp.2.1.reason_inv idx hidx hne0
    rw [ite_eq_right (fun h => absurd hlg h)] at hrs
    rw [(hperU _ hrs.1).2.2.2]; exact hrmL idx hidx hlp hlg
  have hrrU : FidRedRefsOk sU rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrL j hj; exact ⟨hrefsU ▸ hjm, (hperU _ hjm).2.2.2.trans hjr⟩
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspU, hst.cl, hst.fu,
    hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩, hrmU, hrefsU, hrrU,
    by rw [(hperU p hp_in).2.2.2, ← hhdr_eq]⟩

private theorem fidRedSt_mark_garb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {cr rc : Nat} {agN : BitVec 64}
    (hst : FidRedSt c F0 F_cur s R ext st ml) (hrmI : FullReasonsMarked st)
    (hrrI : FidRedRefsOk st rc) (hcr_mem : cr ∈ fullArenaClauseRefs st)
    (hcr_norsn : (fullArenaHdr st cr &&& 0x00200000#32) = 0#32)
    (hcr_ar : cr < st.core.arena.length)
    (hm' : (FullM6HdrMem c ext
      { core := { st.core with
          arena := st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32)
          arena_garbage := agN }
        scratch := st.scratch } ⋆ R) ml') :
    let sN : FullState :=
      { core := { st.core with
          arena := st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32)
          arena_garbage := agN }
        scratch := st.scratch }
    FidRedSt c F0 F_cur s R ext sN ml' ∧ FullReasonsMarked sN ∧
    fullArenaClauseRefs sN = fullArenaClauseRefs st ∧ FidRedRefsOk sN rc := by
  intro sN
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[cr]'hcr_ar = fullArenaHdr st cr := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hnonact := Full.FullDenseWatchHelpers.markGarb_nonact_of_reasonsMarked hsp.2.1 hrmI hcr_norsn
  have hmg := Full.FullDenseWatchHelpers.markGarb_preserves_fullWitnessInv
    hsp.1 hsp.2.1 hcr_mem agN hnonact
  rw [← hhdr_eq] at hmg
  obtain ⟨hlenN, hrefsN, hwN, hrsnN, hndN⟩ := hmg
  have hspN : FullSparseInvW c F0 F_cur sN :=
    ⟨hlenN, hwN, hsp.2.2.1, hndN hsp.2.2.2.1, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by rwa [hrefsN]), hsp.2.2.2.2.2⟩
  have hrmN : FullReasonsMarked sN := fun idx hidx hlp hlg => by
    have hne0 : st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun heq => by rw [heq] at hlg; revert hlg; decide
    have hrs := hsp.2.1.reason_inv idx hidx hne0
    rw [ite_eq_right (fun h => absurd hlg h)] at hrs
    rw [hrsnN _ hrs.1]; exact hrmI idx hidx hlp hlg
  have hrrN : FidRedRefsOk sN rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrI j hj; exact ⟨hrefsN ▸ hjm, (hrsnN _ hjm).trans hjr⟩
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspN, hst.cl, hst.fu,
    hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩, hrmN, hrefsN, hrrN⟩

private theorem fid_reduce_jt_loop {Γ : Env} {ret : Val i64} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext2 : List (BitVec 64)} {s sT : FullState}
    {R : Mem 64 → Prop} {mT : Mem 64} {Q : Post [i64]} {X : XPost} {Jt : Cont [i64]}
    {e_else : Expr Val Cont [i64]} (hret : ret = 1#64)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hJt : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (rret, ()) => ∃ st : FullState,
        FidRedSt c F0 F_cur s R ext2 st m ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64)) →
      Jt xs m)
    (hstT : FidRedSt c F0 F_cur s R ext2 sT mT)
    (hoomT : s.core.oom = 0#64 → sT.core.oom = 0#64) (hrmT : FullReasonsMarked sT) :
    wp Γ Q X (Expr.group (sig := [[]]) (fun L => Blocks.cons (fun _ =>
      Expr.jnz (Arg.imm true)
        (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ()) fun p =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 2, ())) fun p_1 =>
            Expr.jnz (Arg.var p_1.fst) (Expr.jump Jt (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 3, ()))
                  fun p_2 =>
                Expr.jnz (Arg.var p_2.fst) (Expr.jump Jt (Arg.imm 0, ()))
                  (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 0, ()))
                      fun p_3 =>
                    Expr.jnz (Arg.var p_3.fst) (Expr.jump Jt (Arg.var ret, ()))
                      (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                          (Arg.var c.hdr, ()) fun p_4 =>
                        Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                            (Arg.var p_4.fst, Arg.imm 1, ())) fun p_5 =>
                          Expr.jnz (Arg.var p_5.fst) (Expr.jump Jt (Arg.imm 20, ()))
                            (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl)
                                (Arg.var p_4.fst, Arg.imm 0, ())) fun p_6 =>
                              Expr.jnz (Arg.var p_6.fst) (Expr.jump Jt (Arg.imm 0, ()))
                                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ()))
                                    fun p_7 =>
                                  Expr.store (t := i64) (Arg.imm 0) (Arg.var p_7.fst)
                                    (Expr.jump L.fst ()))))))) e_else) .nil)
      (fun L => Expr.jump L.fst ())) mT := by
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ st : FullState,
      rem = c.max_vars - st.core.trail_end ∧
      FidRedSt c F0 F_cur s R ext2 st ml ∧
      (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (0 < st.core.cur_level → FullReasonsMarked st))
    ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hst_st, hoom_st, hrm_st⟩
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    refine wp_m6Hdr_focus_frame hst_st.mem fun hmf => ?_
    c0_call hSweep
    refine ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R,
      rfl, hst_st.inv.sparseW.1, hst_st.inv.sparseW.2.1,
      hst_st.inv.sparseW.2.2.2.1, hst_st.inv.sparseW.2.2.2.2.2,
      hrm_st, hmf,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec'
        wstk' arena' alen' wlen' wu' fred' ni' nr' nb' oom' sc' mA
        hlenA hsr_dom hextA hws2A hllA hwA hndA hoomA hposA hsr1 hsr2 _hsr3 hmA => ?_⟩
    have hstA := fidRedSt_arena_sweep hst_st hlenA hwA hndA hllA hextA
      hws2A (fun hpos => by
        obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposA hpos
        exact ⟨hv, hl, ht, htp, hte⟩) (fullM6HdrMem_unfocus_full hmA)
    c0_hsteps_nogrp
    · exact hJt (20#64, ()) mA ⟨_, hstA, Or.inr (Or.inr rfl),
        fun _ => (hsr2 hc).2, fun h => by cases h⟩
    · exact hJt (0#64, ()) mA ⟨_, hstA, Or.inl rfl,
        (fun h => by cases h), fun h => by cases h⟩
    · simpa only [← hret] using hJt (1#64, ()) mA ⟨_, hstA, Or.inr (Or.inl rfl),
        (fun h => by cases h), fun _ _ => hoomA (Or.inl hc)⟩
    · have hsr_eq1 : sr = 1#64 := by
        rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
      obtain ⟨hcl0, hteA⟩ := hsr1 hsr_eq1
      have hoomA0 : oom' = 0#64 := hoomA (Or.inr hsr_eq1)
      refine fid_call_fullBcpS15_red rfl
        (fun _ _ _ _ h => hProp _ _ _ _ h) hstA hcl0
        fun pr sB mB hstB hclB hteB hrB h0B h1B => ?_
      c0_hsteps_nogrp
      · exact hJt (20#64, ()) mB ⟨sB, hstB, Or.inr (Or.inr rfl),
          fun _ => h1B hc, fun h => by cases h⟩
      · exact hJt (0#64, ()) mB ⟨sB, hstB, Or.inl rfl,
          (fun h => by cases h), fun h => by cases h⟩
      · refine wp_m6Hdr_focus_frame hstB.mem fun hmBf => ?_
        c0_hsteps_nogrp
        have hte_bd : sB.core.trail_end ≤ c.max_vars :=
          Nat.le_trans hstB.inv.sparseW.1.core_ok.trail_end_le
            hstB.inv.sparseW.1.core_ok.cur_vars_le
        dsimp only at hteB
        exact ih (c.max_vars - sB.core.trail_end) () _ (by omega)
          ⟨{ sB with core := { sB.core with unflushed := 0#64 } }, rfl,
            fidRedSt_with_unflushed hstB 0#64 (fullM6HdrMem_unfocus (by assumption)),
            fun _ => h0B hc hoomA0,
            fun hpos => by change 0 < sB.core.cur_level at hpos; omega⟩
  · intro L hL
    c0_hsteps_nogrp
    exact hL (c.max_vars - sT.core.trail_end) () mT ⟨sT, rfl, hstT, hoomT, fun _ => hrmT⟩

private theorem fid_reduce_j4_post {Γ : Env} {ret : Val i64} {force : Val .bool}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)}
    {s s4 : FullState} {R : Mem 64 → Prop} {m4 : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jret : Cont [i64]} (hret : ret = 1#64)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hJret : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (rret, ()) => ∃ extR sR,
        FidRedSt c F0 F_cur s R extR sR m ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → sR.core.oom = 0#64)) →
      Jret xs m)
    (hst4 : FidRedSt c F0 F_cur s R ext2 s4 m4)
    (hoom4 : s.core.oom = 0#64 → s4.core.oom = 0#64) (hrm4 : FullReasonsMarked s4) :
    wp Γ Q X (Expr.group (sig := [[i64]])
      (fun _Js => Blocks.cons (fun p => Expr.jump Jret (Arg.var p.fst, ())) Blocks.nil)
      fun Js => Expr.group (sig := [[]])
        (fun _Js_1 => Blocks.cons (fun _ =>
          Expr.group (sig := [[i64]])
            (fun _Js_2 => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
            fun Js => Expr.group (sig := [[]])
              (fun Js_2 => Blocks.cons (fun _ =>
                Expr.jnz (Arg.imm true)
                  (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep"
                    (Arg.var c.hdr, ()) fun p =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                        (Arg.var p.fst, Arg.imm 2, ())) fun p_1 =>
                      Expr.jnz (Arg.var p_1.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                        (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                            (Arg.var p.fst, Arg.imm 3, ())) fun p_2 =>
                          Expr.jnz (Arg.var p_2.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                            (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                                (Arg.var p.fst, Arg.imm 0, ())) fun p =>
                              Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.var ret, ()))
                                (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                                    (Arg.var c.hdr, ()) fun p =>
                                  Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                                      (Arg.var p.fst, Arg.imm 1, ())) fun p_3 =>
                                    Expr.jnz (Arg.var p_3.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                                      (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl)
                                          (Arg.var p.fst, Arg.imm 0, ())) fun p =>
                                        Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                                          (Expr.let_ (Op.mk (.add i64)
                                              (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                                            Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
                                              (Expr.jump Js_2.fst ())))))))
                  (Expr.jump Js.fst (Arg.var ret, ()))) Blocks.nil)
              fun Js => Expr.jump Js.fst ()) Blocks.nil)
        fun Js_1 => Expr.jnz (Arg.var force) (Expr.jump Js_1.fst ())
          (Expr.group (sig := [[]])
            (fun _Js_2 => Blocks.cons (fun _ =>
              Expr.call (as := [i64, .bool]) (bs := []) "full_mark_reasons"
                (Arg.var c.hdr, Arg.imm false, ()) fun _ =>
                Expr.jump Js.fst (Arg.var ret, ())) Blocks.nil)
            fun Js => Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
              Expr.load i64 (Arg.var p.fst) fun ld =>
                Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p =>
                  Expr.jnz (Arg.var p.fst)
                    (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p =>
                      Expr.load i64 (Arg.var p.fst) fun ld =>
                        Expr.let_ (Op.mk (.mul i64) (Arg.var ld, Arg.imm 4, ())) fun p =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 48, ())) fun p_1 =>
                            Expr.load i64 (Arg.var p_1.fst) fun ld =>
                              Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl)
                                  (Arg.var p.fst, Arg.var ld, ())) fun p =>
                                Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ())
                                  (Expr.let_ (Op.mk (.add i64)
                                      (Arg.var c.hdr, Arg.imm 48, ())) fun p =>
                                    Expr.load i64 (Arg.var p.fst) fun ld =>
                                      Expr.let_ (Op.mk (.mul i64) (Arg.var ld, Arg.imm 5, ()))
                                          fun p =>
                                        Expr.let_ (Op.mk (.add i64)
                                            (Arg.var c.hdr, Arg.imm 32, ())) fun p_2 =>
                                          Expr.load i64 (Arg.var p_2.fst) fun ld =>
                                            Expr.let_ (Op.mk (.mul i64)
                                                (Arg.var ld, Arg.imm 4, ())) fun p_3 =>
                                              Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl)
                                                  (Arg.var p.fst, Arg.var p_3.fst, ())) fun p =>
                                                Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ())
                                                  (Expr.jump Js.fst ())))
                    (Expr.jump Js.fst ()))) m4 := by
  refine wp_join_group (fun ((rret : Val i64), ()) m5 => ∃ s5 : FullState,
      FidRedSt c F0 F_cur s R ext2 s5 m5 ∧
      (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
      (rret = 20#64 → F0.Unsat) ∧
      (rret = 1#64 → s.core.oom = 0#64 → s5.core.oom = 0#64))
    (fun _ (rret, ()) m5 ⟨s5, hst5, hr5, hu5, ho5⟩ => by
      c0_hsteps_nogrp
      exact hJret (rret, ()) m5 ⟨ext2, s5, hst5, hr5, hu5, ho5⟩)
    (fun J5 hJ5 => by
      refine wp_join_group (fun _ mT => ∃ sT : FullState,
          FidRedSt c F0 F_cur s R ext2 sT mT ∧
          (s.core.oom = 0#64 → sT.core.oom = 0#64) ∧ FullReasonsMarked sT)
        (fun _ _ mT ⟨sT, hstT, hoomT, hrmT⟩ => by
          refine wp_join_group (fun ((rret : Val i64), ()) mt => ∃ st : FullState,
              FidRedSt c F0 F_cur s R ext2 st mt ∧
              (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
              (rret = 20#64 → F0.Unsat) ∧
              (rret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64))
            (fun _ (rret, ()) mt h => hJ5 (rret, ()) mt h)
            (fun Jt hJt => @fid_reduce_jt_loop Γ ret c F0 F_cur ext2 s sT R mT Q X Jt
              (Expr.jump Jt (Arg.var ret, ())) hret hProp hSweep hJt hstT hoomT hrmT))
        (fun JT hJT => by
          refine wp_m6Hdr_focus_frame hst4.mem fun hm4f => ?_
          c0_hsteps_nogrp
          · exact hJT () m4 ⟨s4, hst4, hoom4, hrm4⟩
          · refine wp_join_group (fun _ mE => ∃ sE : FullState,
                FidRedSt c F0 F_cur s R ext2 sE mE ∧
                (s.core.oom = 0#64 → sE.core.oom = 0#64))
              (fun _ _ mE ⟨sE, hstE, hoomE⟩ => by
                refine wp_m6Hdr_focus_frame hstE.mem fun hmEf => ?_
                c0_call hMarkRsn
                refine ⟨c, F0, F_cur, sE, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R,
                  rfl, hstE.inv.sparseW.1, hstE.inv.sparseW.2.1, hmEf,
                  fun ar5 m5 hl5 hrefs5 hper5 _ hw5 hm5 => ?_⟩
                c0_hsteps_nogrp
                simpa only [← hret] using hJ5 (1#64, ()) _
                  ⟨_, fidRedSt_mark_reasons hstE hl5 hrefs5 hper5 hw5
                    (fullM6HdrMem_unfocus_full hm5), Or.inr (Or.inl rfl),
                    (fun h => absurd h (by decide)), fun _ => hoomE⟩)
              (fun JE hJE => by
                c0_hsteps_nogrp <;> first
                | exact hJT () m4 ⟨s4, hst4, hoom4, hrm4⟩
                | exact hJE () m4 ⟨s4, hst4, hoom4⟩)))

private abbrev fidMarkGarbExpr (c : FullCfg) (rc target : Val i64) (J4 : Cont []) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]])
      (fun Js_2 => Blocks.cons (fun p_30 =>
        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_30.fst, Arg.var target, ()))
            fun p_31 =>
          Expr.jnz (Arg.var p_31.fst)
            (Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_30.fst, Arg.var rc, ()))
                fun p_32 =>
              Expr.jnz (Arg.var p_32.fst)
                (Expr.let_ (Op.mk (.mul i64) (Arg.var p_30.fst, Arg.imm 4, ())) fun p_33 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_33.fst, ()))
                      fun p_34 =>
                    Expr.load i32 (Arg.var p_34.fst) fun ld_7 =>
                      Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_7, ())) fun p_35 =>
                        Expr.let_ (Op.mk (.mul i64) (Arg.var p_35.fst, Arg.imm 4, ())) fun p_36 =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_36.fst, ()))
                              fun p_37 =>
                            Expr.load i32 (Arg.var p_37.fst) fun ld_8 =>
                              Expr.group (sig := [[]])
                                (fun _Js => Blocks.cons (fun _p =>
                                  Expr.let_ (Op.mk (.add i64) (Arg.var p_30.fst, Arg.imm 1, ()))
                                      fun p =>
                                    Expr.jump Js_2.fst (Arg.var p.fst, ())) Blocks.nil)
                                fun Js =>
                                Expr.let_ (Op.mk (.and i32) (Arg.var ld_8, Arg.imm 524288, ()))
                                    fun p_38 =>
                                  Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl)
                                      (Arg.var p_38.fst, Arg.imm 0, ())) fun p_39 =>
            Expr.jnz (Arg.var p_39.fst)
              (Expr.let_ (Op.mk (.mul i64) (Arg.var p_35.fst, Arg.imm 4, ())) fun p_40 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_40.fst, ())) fun p_41 =>
                  Expr.let_ (Op.mk (.or i32) (Arg.var ld_8, Arg.imm 524288, ())) fun p_42 =>
                    Expr.store (t := i32) (Arg.var p_42.fst) (Arg.var p_41.fst)
                      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p_43 =>
                        Expr.load i64 (Arg.var p_43.fst) fun ld_9 =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var ld_9, Arg.imm 3, ())) fun p_44 =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var p_35.fst, Arg.imm 2, ()))
                                fun p_45 =>
                              Expr.let_ (Op.mk (.mul i64) (Arg.var p_45.fst, Arg.imm 4, ()))
                                  fun p_46 =>
                                Expr.let_ (Op.mk (.add i64)
                                    (Arg.var c.pArena, Arg.var p_46.fst, ())) fun p_47 =>
                                  Expr.load i32 (Arg.var p_47.fst) fun ld =>
                                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_48 =>
                                      Expr.let_ (Op.mk (.add i64)
                                          (Arg.var p_44.fst, Arg.var p_48.fst, ())) fun p_49 =>
                                        Expr.let_ (Op.mk (.add i64)
                                            (Arg.var c.hdr, Arg.imm 472, ())) fun p =>
                                          Expr.store (t := i64) (Arg.var p_49.fst) (Arg.var p.fst)
                                            (Expr.jump Js.fst ())))
              (Expr.jump Js.fst ()))
                (Expr.jump J4 ()))
            (Expr.jump J4 ())) Blocks.nil)
      (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))

private theorem fid_reduce_mark_garb_loop {Γ : Env} {rc target : Val i64} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)} {s sS : FullState}
    {R : Mem 64 → Prop} {mS : Mem 64} {Q : Post [i64]} {X : XPost} {J4 : Cont []}
    (hJ4 : ∀ (xs : Tup Val []) (m : Mem 64), (∃ s4 : FullState,
      FidRedSt c F0 F_cur s R ext2 s4 m ∧ (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧
      FullReasonsMarked s4) → J4 xs m)
    (hstS : FidRedSt c F0 F_cur s R ext2 sS mS)
    (hoomS : s.core.oom = 0#64 → sS.core.oom = 0#64) (hrmS : FullReasonsMarked sS)
    (hrc_le : rc.toNat ≤ c.red_cap) (hrrS : FidRedRefsOk sS rc.toNat) :
    wp Γ Q X (fidMarkGarbExpr c rc target J4) mS := by
  refine wp_loop_inv
    (fun (i, ()) mI => i.toNat ≤ rc.toNat ∧ ∃ sI : FullState,
      FidRedSt c F0 F_cur s R ext2 sI mI ∧ (s.core.oom = 0#64 → sI.core.oom = 0#64) ∧
      FullReasonsMarked sI ∧ FidRedRefsOk sI rc.toNat)
    (fun (i, ()) _ => rc.toNat - i.toNat)
    (fun JI hLoopI => by
      c0_hsteps_nogrp
      exact hLoopI (0#64, ()) _ ⟨Nat.zero_le _, sS, hstS, hoomS, hrmS, hrrS⟩)
    (fun JI (i, ()) mI ⟨hi_le, sI, hstI, hoomI, hrmI, hrrI⟩ hLoopI => ?_)
  have hlenI := hstI.inv.sparseW.1
  have hrrlI := hlenI.scratch_ok.red_refs_len
  have halI := hlenI.core_ok.arena_len_le
  have haarI := hlenI.core_ok.arena_len_arr
  refine wp_m6Hdr_focus_frame hstI.mem fun hmIf => ?_
  c0_hsteps_nogrp
  · have hi_lt : i.toNat < rc.toNat := by c0_bound
    have hi_rr : i.toNat < sI.scratch.red_refs.length := by omega
    have hcr_ok := hrrI i.toNat hi_lt
    have hcr_get : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat =
        (sI.scratch.red_refs[i.toNat]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem hi_rr, Option.getD_some]
    have hcr_mem : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat ∈ fullArenaClauseRefs sI := by
      rw [hcr_get]; exact hcr_ok.1
    have hcr_norsn : (fullArenaHdr sI
        (sI.scratch.red_refs[i.toNat]'hi_rr).toNat &&& 0x00200000#32) = 0#32 := by
      rw [hcr_get]; exact hcr_ok.2
    have hcr_wf := hstI.inv.sparseW.2.1.arena.refs_wf _ hcr_mem
    have hcr_lt : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat < sI.core.arena.length := by
      have := hcr_wf.1; omega
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
    have hcr_idx : ((sI.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat =
        (sI.scratch.red_refs[i.toNat]'hi_rr).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
        (Nat.lt_trans (sI.scratch.red_refs[i.toNat]'hi_rr).isLt (by decide))]
    have hcr_z_lt : ((sI.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
        sI.core.arena.length := by rw [hcr_idx]; exact hcr_lt
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun _ mN => ∃ sN : FullState,
        FidRedSt c F0 F_cur s R ext2 sN mN ∧ (s.core.oom = 0#64 → sN.core.oom = 0#64) ∧
        FullReasonsMarked sN ∧ FidRedRefsOk sN rc.toNat) ?_ ?_
    · rintro _ _ mN ⟨sN, hstN, hoomN, hrmN, hrrN⟩
      c0_hsteps_nogrp
      exact hLoopI (i + 1#64, ()) mN (by dsimp only; omega) ⟨by omega, sN, hstN, hoomN, hrmN, hrrN⟩
    · intro _Js hJs
      c0_hsteps_nogrp
      · simp only [hcr_idx] at hc hm
        obtain ⟨hstN, hrmN, _, hrrN⟩ := fidRedSt_mark_garb (agN := _)
          hstI hrmI hrrI hcr_mem hcr_norsn (by omega) (fullM6HdrMem_unfocus hm)
        exact hJs () _ ⟨_, hstN, hoomI, hrmN, hrrN⟩
      · exact hJs () mI ⟨sI, hstI, hoomI, hrmI, hrrI⟩
  · exact hJ4 () mI ⟨sI, hstI, hoomI, hrmI⟩
  · exact hJ4 () mI ⟨sI, hstI, hoomI, hrmI⟩

private theorem fid_reduce_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J1 : Cont [i64]}
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hJ1 : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (ret, ()) => ∃ ext1 s1,
        FidRedSt c F0 F_cur s R ext1 s1 m ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
        (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → s1.core.oom = 0#64)) →
      J1 xs m)
    (hst0 : FidRedSt c F0 F_cur s R ext s0 m) (hlen0 : s0.LengthsOk c)
    (hs0_core : s0.core = s.core) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_10 =>
      Expr.load i64 (Arg.var p_10.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_11 =>
          Expr.jnz (Arg.var p_11.fst)
            (Expr.group (sig := [[]])
              (fun _Js_1 => Blocks.cons (fun _p_12 =>
                Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                    fun p_13 =>
                  Expr.group (sig := [[i64]])
                    (fun _Js_2 => Blocks.cons (fun p => Expr.jump J1 (Arg.var p.fst, ()))
                      Blocks.nil)
                    fun Js =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 1, ()))
                        fun p_14 =>
                      Expr.jnz (Arg.var p_14.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                        (Expr.group (sig := [[i64]])
                          (fun _Js_2 => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
                            Blocks.nil)
                          fun Js =>
                          Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl)
                              (Arg.var p_13.fst, Arg.imm 0, ())) fun p_15 =>
                            Expr.jnz (Arg.var p_15.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                              (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ()))
                                  fun p =>
                                Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
                                  (Expr.jump Js.fst (Arg.imm 1, ()))))) Blocks.nil)
              fun Js =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 160, ())) fun p_12 =>
                Expr.load i64 (Arg.var p_12.fst) fun ld =>
                  Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ()))
                      fun p_13 =>
                    Expr.jnz (Arg.var p_13.fst)
                      (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
                          (Arg.var c.hdr, Arg.imm 0, ()) fun _p =>
                        Expr.jump Js.fst ())
                      (Expr.jump Js.fst ()))
            (Expr.jump J1 (Arg.imm 1, ()))) m := by
  refine wp_m6Hdr_focus_frame hst0.mem fun hm0f => ?_
  c0_hsteps_nogrp
  · refine wp_join_group (fun _ mB => ∃ sB : FullState,
        FidRedSt c F0 F_cur s R ext sB mB ∧ sB.core.cur_level = 0 ∧
        (s.core.oom = 0#64 → sB.core.oom = 0#64))
      (fun _ _ mB ⟨sB, hstB, hclB, hoomB⟩ => by
        c0_hsteps_nogrp
        refine fid_call_fullBcpS15_red rfl (fun _ _ _ _ h => hProp _ _ _ _ h) hstB hclB
          fun pr sP mP hstP hclP _hteP hrP h0P h1P => ?_
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun ((ret : Val i64), ()) mJ => ∃ sJ : FullState,
            FidRedSt c F0 F_cur s R ext sJ mJ ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
            (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → sJ.core.oom = 0#64))
          ?_ ?_
        · rintro _ ⟨ret, ⟨⟩⟩ mJ ⟨sJ, hstJ, hrJ, huJ, hoJ⟩
          c0_hsteps_nogrp; exact hJ1 (ret, ()) mJ ⟨ext, sJ, hstJ, hrJ, huJ, hoJ⟩
        · intro Jp1 hJp1
          c0_hsteps_nogrp
          · exact hJp1 (20#64, ()) mP ⟨sP, hstP, Or.inr (Or.inr rfl),
              fun _ => h1P (by assumption), fun h => by cases h⟩
          · refine wp_join_group (ts := [i64]) (fun ((ret : Val i64), ()) mJ => ∃ sJ : FullState,
                FidRedSt c F0 F_cur s R ext sJ mJ ∧
                (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
                (ret = 20#64 → F0.Unsat) ∧
                (ret = 1#64 → s.core.oom = 0#64 → sJ.core.oom = 0#64)) ?_ ?_
            · rintro _ ⟨ret, ⟨⟩⟩ mJ hJ
              c0_hsteps_nogrp; exact hJp1 (ret, ()) mJ hJ
            · intro Jp2 hJp2
              c0_hsteps_nogrp
              · exact hJp2 (0#64, ()) mP ⟨sP, hstP, Or.inl rfl,
                  fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
              · refine wp_m6Hdr_focus_frame hstP.mem fun hmPf => ?_
                c0_hsteps_nogrp
                exact hJp2 (1#64, ()) _ ⟨_, fidRedSt_with_unflushed hstP 0#64
                    (fullM6HdrMem_unfocus (by assumption)),
                  Or.inr (Or.inl rfl), fun h => absurd h (by decide),
                  fun _ hso => h0P (by assumption) (hoomB hso)⟩)
      (fun JB hJB => by
        c0_hsteps_nogrp
        · c0_call hBacktrack
          refine ⟨c, s0, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen0,
            by have hmax := c.hmaxv; unfold dimacsBound at hmax
               have := hst0.inv.sparseW.2.1.cur_level_le
               have := hlen0.core_ok.trail_end_le
               have := hlen0.core_ok.cur_vars_le; omega,
            fun _ => by
              have hmax := c.hmaxv; unfold dimacsBound at hmax
              have := hst0.inv.sparseW.2.1.cur_level_le
              have := hlen0.core_ok.trail_end_le
              have := hlen0.core_ok.cur_vars_le; omega,
            hst0.inv.sparseW.2.1.trail_lits_lt, hm0f,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
              hlen' _ _ hcl' _ hsc' _ _ hw' _ hm' => ?_⟩
          have hcl'0 : cl' = 0 := by simpa using hcl'
          subst hcl'0
          obtain ⟨ta', ba', pt', pb', hp', ps', hl', qsi', qss', hsc_eq⟩ := hsc'
          c0_hsteps_nogrp
          exact hJB () _
            ⟨_, fidRedSt_backtrack0 hst0 hlen'
              (hw' F0 F_cur hst0.inv.sparseW.2.1 (Nat.zero_le _))
              (by rw [hsc_eq]) (by rw [hsc_eq]) (by rw [hsc_eq])
              (fullM6HdrMem_unfocus_full hm'),
              rfl, fun h => by dsimp only; rwa [hs0_core]⟩
        · have hcl0 : s0.core.cur_level = 0 := by
            have hmax := c.hmaxv; unfold dimacsBound at hmax
            have hle := hlen0.core_ok.trail_end_le
            have hcv := hlen0.core_ok.cur_vars_le
            have hcl := hst0.inv.sparseW.2.1.cur_level_le
            c0_bound
          exact hJB () m ⟨s0, hst0, hcl0, fun h => hs0_core ▸ h⟩)
  · exact hJ1 (1#64, ()) m
      ⟨ext, s0, hst0, Or.inr (Or.inl rfl), fun h => absurd h (by decide),
        fun _ hso => by rwa [hs0_core]⟩

private def FidRedLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s3 : FullState) (R : Mem 64 → Prop) (ext2 : List (BitVec 64))
    (rc : Val i64) (sL : FullState) (mL : Mem 64) : Prop :=
  rc.toNat ≤ c.red_cap ∧ sL.core.arena_len = s3.core.arena_len ∧
  FidRedSt c F0 F_cur s R ext2 sL mL ∧ (s.core.oom = 0#64 → sL.core.oom = 0#64) ∧
  FullReasonsMarked sL ∧ fullArenaClauseRefs sL = fullArenaClauseRefs s3 ∧
  FidRedRefsOk sL rc.toNat ∧ (FullMem c sL ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mL

private abbrev fidPushRcExpr (c : FullCfg) (rc p : Val i64) (keep : Val .bool)
    (Jrc2 : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.jnz (Arg.var keep) (Expr.jump Jrc2 (Arg.var rc, ()))
    (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 440, ())) fun p_1 =>
      Expr.load i64 (Arg.var p_1.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var rc, Arg.var ld, ())) fun p_2 =>
          Expr.jnz (Arg.var p_2.fst)
            (Expr.let_ (Op.mk (.mul i64) (Arg.var rc, Arg.imm 4, ())) fun p_3 =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_3.fst, ())) fun p_4 =>
                Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p, ())) fun p_37 =>
                  Expr.store (t := i32) (Arg.var p_37.fst) (Arg.var p_4.fst)
                    (Expr.let_ (Op.mk (.add i64) (Arg.var rc, Arg.imm 1, ())) fun p_5 =>
                      Expr.jump Jrc2 (Arg.var p_5.fst, ())))
            (Expr.jump Jrc2 (Arg.var rc, ())))

private abbrev fidKeepBoolExpr (glue t1 t2 : Val i64) (old_u : Val i32)
    (JK : Cont [.bool]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[]])
    (fun _Js_3 => Blocks.cons (fun _ =>
      Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl) (Arg.var glue, Arg.var t2, ())) fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.let_ (Op.mk (.cmp .uge i32 Ty.bool rfl) (Arg.var old_u, Arg.imm 30, ())) fun p_2 =>
            Expr.jnz (Arg.var p_2.fst) (Expr.jump JK (Arg.imm true, ()))
              (Expr.jump JK (Arg.imm false, ())))
          (Expr.jump JK (Arg.imm false, ()))) Blocks.nil)
    fun Js_3 =>
      Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl) (Arg.var glue, Arg.var t1, ())) fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.let_ (Op.mk (.cmp .ugt i32 Ty.bool rfl) (Arg.var old_u, Arg.imm 0, ())) fun p_2 =>
            Expr.jnz (Arg.var p_2.fst) (Expr.jump JK (Arg.imm true, ()))
              (Expr.jump Js_3.fst ()))
          (Expr.jump Js_3.fst ())

private theorem fid_reduce_push_rc {Γ : Env} {rc p : Val i64} {keep : Val .bool}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)}
    {s s3 sU : FullState} {R : Mem 64 → Prop} {mU : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jrc2 : Cont [i64]}
    (hJrc2 : ∀ (xs : Tup Val [i64]) mR,
      (∃ sR, FidRedLoopInv c F0 F_cur s s3 R ext2 xs.1 sR mR) → Jrc2 xs mR)
    (hrc_le : rc.toNat ≤ c.red_cap) (hred_cap : c.red_cap < 2 * 2 ^ 28)
    (hp_lt32 : p.toNat < 2 ^ 32) (hp_trunc : (p.setWidth 32).toNat = p.toNat)
    (hp_inU : p.toNat ∈ fullArenaClauseRefs sU)
    (hno_rsn : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = 0#32)
    (hlenU : sU.LengthsOk c) (halenU : sU.core.arena_len = s3.core.arena_len)
    (hstU : FidRedSt c F0 F_cur s R ext2 sU mU) (hoomU : s.core.oom = 0#64 → sU.core.oom = 0#64)
    (hrmU : FullReasonsMarked sU) (hrefsU : fullArenaClauseRefs sU = fullArenaClauseRefs s3)
    (hrrU : FidRedRefsOk sU rc.toNat)
    (hmU : (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU) :
    wp Γ Q X (fidPushRcExpr c rc p keep Jrc2) mU := by
  have hrrlU := hlenU.scratch_ok.red_refs_len; dsimp only [fidPushRcExpr]; c0_hsteps_nogrp
  · exact hJrc2 (rc, ()) mU ⟨sU, hrc_le, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hmU⟩
  · have hrc_lt : rc.toNat < c.red_cap := by
      have := BitVec.lt_def.mp (by assumption : rc < BitVec.ofNat 64 c.red_cap)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this
    have hrc1 : (rc + 1#64).toNat = rc.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    c0_hsteps_nogrp
    let scU' : FullScratch :=
      { sU.scratch with red_refs := sU.scratch.red_refs.set rc.toNat (p.setWidth 32) }
    let sU' : FullState := { sU with scratch := scU' }
    have hmU' : (FullMem c sU' ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m := hm
    have hstU' := fidRedSt_with_scratch hstU (sc' := scU')
      { hlenU.scratch_ok with red_refs_len := by simp [scU', hrrlU] }
      rfl rfl rfl (fullM6HdrMem_unfocus hmU')
    have hp_sw : p.setWidth 32 = BitVec.ofNat 32 p.toNat := BitVec.eq_of_toNat_eq
      (by rw [hp_trunc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt32])
    have hrrU' : FidRedRefsOk sU' (rc + 1#64).toNat := by
      dsimp only [sU', scU']; rw [hrc1, hp_sw]
      exact fidRedRefsOk_push hrrlU hrc_lt hp_lt32 hp_inU hno_rsn hrrU
    exact hJrc2 (rc + 1#64, ()) _
      ⟨sU', by dsimp only; omega, halenU, hstU', hoomU, hrmU, hrefsU, hrrU', hmU'⟩
  · exact hJrc2 (rc, ()) mU ⟨sU, hrc_le, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hmU⟩

private theorem fid_reduce_keep_bool {Γ : Env} {glue t1 t2 : Val i64} {old_u : Val i32}
    {mU : Mem 64} {Q : Post [i64]} {X : XPost} {JK : Cont [.bool]}
    (hJK : ∀ b, JK (b, ()) mU) : wp Γ Q X (fidKeepBoolExpr glue t1 t2 old_u JK) mU := by
  dsimp only [fidKeepBoolExpr]; c0_hsteps_nogrp
  refine wp_join_group (fun (_ : Tup Val []) mS => mS = mU)
    (fun _ _ _ hmS => by cases hmS; c0_hsteps_nogrp <;> exact hJK _)
    (fun _ hJs => by c0_hsteps_nogrp <;> first | exact hJK true | exact hJs () mU rfl)

private theorem fid_reduce_collect_jr {Γ : Env} {hdr : Val i32} {rc p t1 t2 : Val i64}
    {old_u : Val i32} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext2 : List (BitVec 64)} {s s3 sU _sL : FullState} {R : Mem 64 → Prop} {mU : Mem 64}
    {Q : Post [i64]} {X : XPost} {JR : Cont [i64]}
    (hJR : ∀ (xs : Tup Val [i64]) mR,
      (∃ sR, FidRedLoopInv c F0 F_cur s s3 R ext2 xs.1 sR mR) → JR xs mR)
    (hrc_le : rc.toNat ≤ c.red_cap) (hred_cap : c.red_cap < 2 * 2 ^ 28)
    (hp_lt : p.toNat < s3.core.arena_len) (hp_lt32 : p.toNat < 2 ^ 32)
    (hp_trunc : (p.setWidth 32).toNat = p.toNat)
    (hp_mem : p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3)
    (hhdrU : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = (hdr &&& 0x00200000#32))
    (halenU : sU.core.arena_len = s3.core.arena_len)
    (hstU : FidRedSt c F0 F_cur s R ext2 sU mU) (hoomU : s.core.oom = 0#64 → sU.core.oom = 0#64)
    (hrmU : FullReasonsMarked sU) (hrefsU : fullArenaClauseRefs sU = fullArenaClauseRefs s3)
    (hrrU : FidRedRefsOk sU rc.toNat)
    (hmU : (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU) :
    wp Γ Q X (Expr.let_ (Op.mk (.and i32) (Arg.var hdr, Arg.imm 2097152, ())) fun p_32 =>
      Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var p_32.fst, Arg.imm 0, ())) fun p_33 =>
        Expr.jnz (Arg.var p_33.fst)
          (Expr.let_ (Op.mk (.and i32) (Arg.var hdr, Arg.imm 524287, ())) fun p_34 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_34.fst, ())) fun p_35 =>
              Expr.group (sig := [[.bool]]) (fun _Js_3 => Blocks.cons (fun p_36 =>
                Expr.group (sig := [[i64]]) (fun _Js_4 => Blocks.cons (fun q =>
                  Expr.jump JR (Arg.var q.fst, ())) Blocks.nil)
                  (fun Js => fidPushRcExpr c rc p p_36.fst Js.fst)) Blocks.nil)
                (fun Js => fidKeepBoolExpr p_35.fst t1 t2 old_u Js.fst))
          (Expr.jump JR (Arg.var rc, ()))) mU := by
  have hlenU := hstU.inv.sparseW.1
  c0_hsteps_nogrp
  · have hno_rsn : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = 0#32 := hhdrU ▸ hc
    have hp_inU : p.toNat ∈ fullArenaClauseRefs sU :=
      hrefsU ▸ hp_mem.resolve_left (by omega)
    refine wp_join_group (fun (_ : Tup Val [.bool]) mK => mK = mU) (by
      rintro _ ⟨keep, ⟨⟩⟩ mK rfl
      refine wp_join_group
        (fun (rc', ()) mR => ∃ sR, FidRedLoopInv c F0 F_cur s s3 R ext2 rc' sR mR)
        (fun _ (rc', ()) mR hR => by c0_hsteps_nogrp; exact hJR (rc', ()) mR hR)
        (fun _ hJrc2 => fid_reduce_push_rc hJrc2 hrc_le hred_cap hp_lt32 hp_trunc hp_inU
          hno_rsn hlenU halenU hstU hoomU hrmU hrefsU hrrU hmU))
      (fun _ hJK => by c0_hsteps_nogrp; exact fid_reduce_keep_bool fun b => hJK (b, ()) mU rfl)
  · exact hJR (rc, ()) mU ⟨sU, hrc_le, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hmU⟩

private theorem fid_reduce_ret_wm {Γ : Env} {rret : Val i64} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {extR : List (BitVec 64)} {s sR : FullState} {R : Mem 64 → Prop}
    {mr : Mem 64} {Q : Post [i64]} {X : XPost}
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hQ : ∀ r ext' s' m', FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → 0 < s'.core.cur_level → s'.core.cur_level = s.core.cur_level ∧
        s'.core.vals = s.core.vals ∧ s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m')
    (hstR : FidRedSt c F0 F_cur s R extR sR mr)
    (hrR : rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) (huR : rret = 20#64 → F0.Unsat)
    (hoR : rret = 1#64 → s.core.oom = 0#64 → sR.core.oom = 0#64) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p_12 =>
      Expr.load i64 (Arg.var p_12.fst) fun ld =>
        Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
            (Arg.var c.hdr, Arg.imm 2, Arg.var ld, ()) fun _ =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 600, ())) fun p_14 =>
            Expr.load i64 (Arg.var p_14.fst) fun ld =>
              Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
                  (Arg.var c.hdr, Arg.imm 3, Arg.var ld, ()) fun _ =>
                Expr.ret (Arg.var rret, ())) mr := by
  refine wp_m6Hdr_focus_frame hstR.mem fun hmRf => ?_
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hstR.inv.cfgOk
    hstR.inv.extOk hstR.inv.sparseW.1 (fullM6HdrMem_unfocus hmRf)
    fun _ extR1 sR1 mR1 hcR1 hlR1 hmsR1 hextR1 _ hmR1 => ?_
  have hstR1 := fidRedSt_w2a hstR hcR1 hlR1 hmsR1 hextR1 hmR1
  refine wp_m6Hdr_focus_frame hstR1.mem fun hmR1f => ?_
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hstR1.inv.cfgOk
    hstR1.inv.extOk hstR1.inv.sparseW.1 (fullM6HdrMem_unfocus hmR1f)
    fun _ extR2 sR2 mR2 hcR2 hlR2 hmsR2 hextR2 _ hmR2 => ?_
  have hstR2 := fidRedSt_w2a hstR1 hcR2 hlR2 hmsR2 hextR2 hmR2
  c0_hsteps_nogrp
  exact hQ rret extR2 sR2 mR2 hstR2.inv hrR hstR2.cl hstR2.fu hstR2.cv hstR2.tmp hstR2.tl
    hstR2.ws2 huR (fun h1 hso => by rw [hcR2, hcR1]; exact hoR h1 hso) (fun _ => hstR2.pos)
    hstR2.mem

theorem full_reduce_fid_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, fullIlog10Spec a m Q X →
      Γ "full_ilog10_fid" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ReduceSpec a m Q X → Func.wp Γ full_reduce_fid_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X hs
  rcases m6ReduceSpec_elim hs with ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hm0, hQ⟩
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hred_cap : c.red_cap < 2 * 2 ^ 28 := c.hred
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  unfold Func.wp full_reduce_fid_body
  have hst_init := fidRedSt_refl hinv hm0
  refine wp_m6Hdr_focus_frame hm0 fun hmf => ?_
  c0_hsteps_nogrp; c0_call hIsqrt; intro r_isq _ _ _; dsimp only; c0_hsteps_nogrp
  let s0 : FullState := { s with scratch :=
    { s.scratch with
      reductions := s.scratch.reductions + 1#64
      reduce_limit := s.scratch.conflicts + 1000#64 * r_isq } }
  have hlen0 : s0.LengthsOk c :=
    ⟨hinv.sparseW.1.core_ok, { hinv.sparseW.1.scratch_ok with
      walk_vals_len := hinv.sparseW.1.scratch_ok.walk_vals_len }⟩
  have hmf0 : (FullMem c s0 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m := by
    simpa only [s0, BitVec.ofNat_eq_ofNat] using hm
  have hst0 : FidRedSt c F0 F_cur s R ext s0 m :=
    fidRedSt_with_scratch hst_init hlen0.scratch_ok rfl rfl rfl (fullM6HdrMem_unfocus hmf0)
  refine wp_join_group (fun ((ret : Val i64), ()) m1 => ∃ ext1 s1,
      FidRedSt c F0 F_cur s R ext1 s1 m1 ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
      (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → s1.core.oom = 0#64)) ?_ ?_
  · rintro J1 ⟨ret, ⟨⟩⟩ m1 ⟨ext1, s1, hst1, hr1, hu1, ho1⟩
    refine wp_join_group (ts := [i64]) (fun (rret, ()) mr => ∃ extR sR,
        FidRedSt c F0 F_cur s R extR sR mr ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → sR.core.oom = 0#64)) ?_ ?_
    · rintro _ ⟨rret, ⟨⟩⟩ mr ⟨extR, sR, hstR, hrR, huR, hoR⟩
      exact fid_reduce_ret_wm hSetWm hQ hstR hrR huR hoR
    · intro Jret hJret
      c0_hsteps_nogrp
      · have hc_ret : ret = 1#64 := hc
        have hoom1 : s.core.oom = 0#64 → s1.core.oom = 0#64 := ho1 hc_ret
        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRecomp _ _ _ _ h) hst1.inv.cfgOk
          hst1.inv.extOk hst1.inv.sparseW.1 hst1.mem
          fun _ ext2 s2 m2 hc2 hl2 hms2 hext2 _ hm2 => ?_
        have hst2 := fidRedSt_w2a hst1 hc2 hl2 hms2 hext2 hm2
        have hoom2 : s.core.oom = 0#64 → s2.core.oom = 0#64 := fun h => hc2 ▸ hoom1 h
        c0_hsteps_nogrp; c0_call hMarkRsn
        refine ⟨c, F0, F_cur, s2, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl,
          hst2.inv.sparseW.1, hst2.inv.sparseW.2.1, fullM6HdrMem_focus_full hst2.mem,
          fun ar3 m3 hl3 hrefs3 hper3 hrm3 hw3 hm3 => ?_⟩
        have hst3 := fidRedSt_mark_reasons hst2 hl3 hrefs3 hper3 hw3 (fullM6HdrMem_unfocus_full hm3)
        let s3 : FullState := { s2 with core := { s2.core with arena := ar3 } }
        have hrm3' : FullReasonsMarked s3 := hrm3 rfl
        have hoom3 : s.core.oom = 0#64 → s3.core.oom = 0#64 := hoom2
        refine wp_m6Hdr_focus_frame hst3.mem fun hm3f => ?_
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (rc, p, ()) mL => p.toNat ≤ s3.core.arena_len ∧
            (p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3) ∧
            ∃ sL : FullState, FidRedLoopInv c F0 F_cur s s3 R ext2 rc sL mL)
          (fun (_, p, ()) _ => s3.core.arena_len - p.toNat)
          (fun JL hLoopL => by
            c0_hsteps_nogrp
            refine hLoopL (0#64, 0#64, ()) m3 ⟨Nat.zero_le _, ?_, s3,
              Nat.zero_le _, rfl, hst3, hoom3, hrm3', rfl, fun _ h => by simp at h, hm3f⟩
            by_cases hz : s3.core.arena_len = 0
            · exact Or.inl hz.symm
            · exact Or.inr (Full.FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem
                hst3.inv.sparseW.2.1.arena (Nat.pos_of_ne_zero hz)))
          (fun JL (rc, p, ()) mL ⟨hp_le, hp_mem, sL, hL⟩ hLoopL => ?_)
        · have ⟨hrc_le, halenL, hstL, hoomL, hrmL, hrefsL, hrrL, hmL⟩ := hL
          have hlenL := hstL.inv.sparseW.1; have halL := hlenL.core_ok.arena_len_le
          have haarL := hlenL.core_ok.arena_len_arr; have hrrlL := hlenL.scratch_ok.red_refs_len
          c0_hsteps_nogrp
          · have hp_lt : p.toNat < sL.core.arena_len := by c0_bound
            have hp_in : p.toNat ∈ fullArenaClauseRefs sL := by
              rw [hrefsL]; exact hp_mem.resolve_left (by omega)
            have hp_wf := hstL.inv.sparseW.2.1.arena.refs_wf p.toNat hp_in
            have hp_lt32 : p.toNat < 2 ^ 32 := by omega
            have hp_trunc : (p.setWidth 32).toNat = p.toNat := by
              rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hp_lt32
            c0_call hArenaNext
            refine ⟨c, sL, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hlenL, hmL, ?_⟩
            have hnb := fullArenaNextOff_bounds (ar := sL.core.arena) (alen := sL.core.arena_len)
              (cref := p.toNat) hp_wf.1
            have hnxt_mem :=
              FullDenseWatchHelpers.fullArenaClauseRefs_next_mem hstL.inv.sparseW.2.1.arena hp_in
            have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len
                (p.setWidth 32).toNat)).setWidth 64).toNat =
                fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat := by
              rw [hp_trunc, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            refine wp_join_group
              (fun (rc', ()) mN => ∃ sN : FullState, FidRedLoopInv c F0 F_cur s s3 R ext2 rc' sN mN)
              (fun _ (rc', ()) mN ⟨sN, hN⟩ => by
                c0_hsteps_nogrp
                refine hLoopL (rc', _, ()) mN (by dsimp only; rw [hn_eq]; omega)
                  ⟨by rw [hn_eq]; omega, ?_, sN, hN⟩
                rw [hn_eq]; rcases hnxt_mem with hend | hmem
                · exact Or.inl (hend.trans halenL)
                · exact Or.inr (hrefsL ▸ hmem))
              (fun JN hJN => ?_)
            c0_hsteps_nogrp
            · refine wp_join_group
                (fun _ mU => ∃ sU : FullState, sU.core.arena_len = s3.core.arena_len ∧
                  FidRedSt c F0 F_cur s R ext2 sU mU ∧ (s.core.oom = 0#64 → sU.core.oom = 0#64) ∧
                  FullReasonsMarked sU ∧ fullArenaClauseRefs sU = fullArenaClauseRefs s3 ∧
                  FidRedRefsOk sU rc.toNat ∧ (fullArenaHdr sU p.toNat &&& 0x00200000#32) =
                    (sL.core.arena[p.toNat]'(by omega) &&& 0x00200000#32) ∧
                  (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU)
                (fun _ _ mU ⟨sU, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hhdrU, hmU⟩ => by
                  c0_hsteps_nogrp
                  refine wp_join_group
                    (fun (rc', ()) mR => ∃ sR, FidRedLoopInv c F0 F_cur s s3 R ext2 rc' sR mR)
                    (fun _ (rc', ()) mR hR => by c0_hsteps_nogrp; exact hJN (rc', ()) mR hR)
                    (fun _ hJR => fid_reduce_collect_jr (_sL := sL) hJR hrc_le hred_cap
                      (by omega) hp_lt32 hp_trunc hp_mem (by rw [hhdrU]) halenU hstU
                      hoomU hrmU hrefsU hrrU hmU))
                (fun JU hJU => by
                  c0_hsteps_nogrp
                  · let sU : FullState :=
                      { core := { sL.core with
                          arena := sL.core.arena.set p.toNat
                            ((sL.core.arena[p.toNat]'(by omega) &&& 0x07FFFFFF#32) |||
                              ((((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat)) &&&
                                31#32) - 1#32) <<< (27 : Nat))) }
                        scratch := sL.scratch }
                    have hmUf : (FullMem c sU ⋆
                        (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m := hm
                    obtain ⟨hstU, hrmU, hrefsU, hrrU, hhdrU⟩ := fidRedSt_update_used
                      (u := (((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat))
                      &&& 31#32) - 1#32)) hstL hrmL hrrL hp_in (by omega)
                      (fullM6HdrMem_unfocus hmUf)
                    exact hJU () m ⟨sU, halenL, hstU, hoomL, hrmU, hrefsU.trans hrefsL, hrrU,
                      hhdrU, hmUf⟩
                  · have hhdr_eq :
                        fullArenaHdr sL p.toNat = sL.core.arena[p.toNat]'(by omega) := by
                      unfold fullArenaHdr fullArenaHdrCore
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                    exact hJU () mL ⟨sL, halenL, hstL, hoomL, hrmL, hrefsL, hrrL,
                      by rw [hhdr_eq], hmL⟩)
            all_goals exact hJN (rc, ()) mL ⟨sL, hL⟩
          · refine wp_join_group
              (fun _ m4 => ∃ s4 : FullState, FidRedSt c F0 F_cur s R ext2 s4 m4 ∧
                (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧ FullReasonsMarked s4)
              (fun _ _ m4 ⟨s4, hst4, hoom4, hrm4⟩ =>
                fid_reduce_j4_post hc_ret hMarkRsn hProp hSweep hJret hst4 hoom4 hrm4)
              fun J4 hJ4 => by
                c0_hsteps_nogrp
                · have hrr_bd : ∀ k < rc.toNat,
                      (sL.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap := fun k hk => by
                    have hwf := (hstL.inv.sparseW.2.1.arena.refs_wf _ (hrrL k hk).1).1
                    omega
                  c0_call hSortReds
                  refine ⟨c, sL, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hlenL, hrc_le, hrr_bd,
                    hmL, fun rr' mS hrr_len hpermS hmS => ?_⟩
                  let scS : FullScratch := { sL.scratch with red_refs := rr' }
                  have hstS := fidRedSt_with_scratch hstL (sc' := scS)
                    { hlenL.scratch_ok with red_refs_len := hrr_len }
                    rfl rfl rfl (fullM6HdrMem_unfocus_full hmS)
                  have hrrS : FidRedRefsOk { sL with scratch := scS } rc.toNat := fun k hk => by
                    obtain ⟨j, hj, heq⟩ := hpermS k hk
                    change (scS.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sL ∧
                      (fullArenaHdr sL (scS.red_refs[k]?.getD 0#32).toNat &&& 0x00200000#32) = 0#32
                    rw [heq]; exact hrrL j hj
                  let sS : FullState := { sL with scratch := scS }
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) ma => ma = mS)
                    (fun _ ⟨arg, ⟨⟩⟩ ma hma => by
                      subst hma; c0_hsteps_nogrp; c0_call hIlog10; intro logv hlog1 _
                      have hlog_ne : logv ≠ 0#64 := fun hz => by rw [hz] at hlog1; cases hlog1
                      c0_hsteps_nogrp
                      exact fid_reduce_mark_garb_loop (sS := sS) hJ4 hstS hoomL hrmL hrc_le hrrS)
                    (fun Jarg hJarg => by c0_hsteps_nogrp <;> exact hJarg (_, ()) mS rfl)
                · exact hJ4 () mL ⟨sL, hstL, hoomL, hrmL⟩
      · exact hJret (ret, ()) m1 ⟨ext1, s1, hst1, hr1, hu1, ho1⟩
  · intro J1 hJ1; exact fid_reduce_unflushed hBacktrack hProp hJ1 hst0 hlen0 rfl

end ReduceFid

/-! ## 5. `full_probe_fid_wp` (`fidProbeSpec`) -/

private theorem fid_probe_ret_wm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s0 s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    {args : Tup (Arg Val) [i64, i64, i64]}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hk_ret : k () = .ret (Arg.imm r, ()))
    (hargs : vals args = (c.hdr, 0#64, BitVec.ofNat 64 s.scratch.search_ticks.toNat, ()) ∨
      vals args = (c.hdr, 0#64, s.scratch.search_ticks, ()))
    (hSetWm : ∀ a m' Q' X', m6HdrW2aSpec [i64, i64] [] a m' Q' X' →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m' Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hfu : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hr : r = 1#64 ∨ r = 20#64) (hu : r = 20#64 → F0.Unsat)
    (h1 : r = 1#64 → FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (.call "m6_hdr_set_watermark" (as := [i64, i64, i64]) (bs := []) args k) m := by
  obtain ⟨v, hv⟩ : ∃ v, vals args = (c.hdr, 0#64, v, ()) :=
    hargs.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  refine m6Hdr_call_m6HdrW2a hv (fun _ _ h => hSetWm _ _ _ _ h) hcfg hext hlen hm
    fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
  rw [hk_ret]; c0_hsteps_nogrp
  exact hQ ext' s' m' hlen' hext' (by rw [hc']; exact hfu) hr hu
    (fun h => let ⟨hi, hcl⟩ := h1 h
      ⟨fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hi hlen' hc' hms') hext',
        by rw [hc']; exact hcl⟩) hm'

private theorem fid_dense_inconsistent_unsat {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} (hd : FullDenseInv c F0 s) (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat := by
  obtain ⟨F_cur, hw⟩ := hd.1.witness
  exact hw.ext_sound.2 (hw.inconsistent_sound hinc)

theorem full_probe_fid_wp (Γ : Env)
    (hDticks : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hNlog : ∀ a m Q X, fidNlogpownSpec a m Q X →
      Γ "full_nlogpown_fid" [i64, i64, i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullDefSweep.fullCongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRebuild : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweep : ∀ a m Q X, FullM3CongBva.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hTail : ∀ a m Q X, fidProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fidProbeSpec a m Q X → Func.wp Γ full_probe_fid_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases fidProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_fid_body
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDticks _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths hm
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := hc0 ▸ hcl0
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ mW => ∃ extW sW, FullM6HdrInv c F0 extW sW ∧
        sW.core.cur_level = 0 ∧ sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c extW sW ⋆ R) mW) ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ mW ⟨extW, sW, hinvW, hclW, hfuW, hmW⟩
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun _ mT => ∃ extT sT, FullM6HdrInv c F0 extT sT ∧
          sT.core.cur_level = 0 ∧ sT.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullM6HdrMem c extT sT ⋆ R) mT) ?_ ?_
      · rintro _ _ mT ⟨extT, sT, hinvT, hclT, hfuT, hmT⟩
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mRet => ∃ extRet sRet,
            FullM6HdrInv c F0 extRet sRet ∧ sRet.core.cur_level = 0 ∧
            sRet.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extRet sRet ⋆ R) mRet)
          (?_ ) (?_ )
        · rintro _ _ mRet ⟨extRet, sRet, hinvRet, hclRet, hfuRet, hmRet⟩
          refine wp_m6Hdr_focus_frame hmRet fun hmRetf => ?_
          c0_hsteps_nogrp
          exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvRet.cfgOk hinvRet.extOk
            hinvRet.sparse.lengths hfuRet (Or.inl rfl) (fun h => by cases h)
            (fun _ => ⟨hinvRet, hclRet⟩) (fullM6HdrMem_unfocus hmRetf) (hQ 1#64)
        · intro Jret hJret
          refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
          c0_hsteps_nogrp
          · c0_call hEnter
            refine ⟨c, F0, sT, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hinvT.sparse,
              hmTf, fun ok sF mF hclF hfuF hdenF hspF hmF => ?_⟩
            have hmF' := fullM6HdrMem_unfocus hmF
            c0_hsteps_nogrp
            · have hdenF' := hdenF ‹_›
              refine wp_join_group (ts := [i64]) (fun _ mB => mB = mF)
                (fun _ ⟨fbud0, ⟨⟩⟩ mB hmB => by
                  subst hmB
                  c0_hsteps_nogrp; c0_call hMin; intro fbud _; c0_hsteps_nogrp
                  c0_call hFactor
                  refine ⟨c, F0, sF, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hdenF',
                    hmF, fun _ sFc mFc hdenFc _ hfuFc _ hmFc => ?_⟩
                  c0_hsteps_nogrp; c0_call hRebuild
                  refine ⟨c, F0, sFc, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hdenFc,
                    hmFc, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                  have hinvR := FullM6HdrInv.mk_inv hinvT.cfgOk hinvT.extOk hspR
                  have hmR' := fullM6HdrMem_unfocus hmR
                  have hfuR' : sR.core.fuel.toNat ≤ s.core.fuel.toNat := by
                    rw [hfuFc] at hfuR; exact Nat.le_trans hfuR (Nat.le_trans hfuF hfuT)
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                      hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · exact hJret () mR ⟨extT, sR, hinvR, hclR, hfuR', hmR'⟩)
                (fun _ hJ0 => by c0_hsteps_nogrp <;> exact hJ0 (_, ()) mF rfl)
            · have hinvF := FullM6HdrInv.mk_inv hinvT.cfgOk hinvT.extOk (hspF ‹_›)
              refine wp_m6Hdr_focus_frame hmF' fun hmFf => ?_
              c0_hsteps_nogrp
              exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvF.cfgOk hinvF.extOk
                hinvF.sparse.lengths (Nat.le_trans hfuF hfuT) (Or.inr rfl)
                (fun _ => fullM6HdrInv_inconsistent_unsat hinvF ‹_›)
                (fun h => by cases h) (fullM6HdrMem_unfocus hmFf) (hQ 20#64)
            · have hinvF := FullM6HdrInv.mk_inv hinvT.cfgOk hinvT.extOk (hspF ‹_›)
              exact hJret () mF ⟨extT, sF, hinvF, hclF, Nat.le_trans hfuF hfuT, hmF'⟩
      · intro JT hJT; c0_hsteps_nogrp
        · refine wp_m6Hdr_focus_frame hmW fun hmWf => ?_
          c0_hsteps_nogrp
          · c0_call hBackbone
            refine ⟨c, F0, sW, m6ExtMem (m6ExtAddr c.hdr) extW ⋆ R, rfl, hinvW.sparse, hmWf,
              fun rB sB mB hspB hclB _ hfuB hdB huB hmB => ?_⟩
            have hinvB := FullM6HdrInv.mk_inv hinvW.cfgOk hinvW.extOk hspB
            have hmB' := fullM6HdrMem_unfocus hmB
            c0_hsteps_nogrp
            · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
              c0_hsteps_nogrp
              exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                hinvB.sparse.lengths (Nat.le_trans hfuB hfuW) (Or.inr rfl)
                (fun _ => huB ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
            · exact hJT () mB ⟨extW, sB, hinvB, hclB, Nat.le_trans hfuB hfuW, hmB'⟩
          · exact hJT () mW ⟨extW, sW, hinvW, hclW, hfuW, fullM6HdrMem_unfocus hmWf⟩
        · c0_call hTail
          refine fidProbeTailSpec_of hinvW hclW hmW
            fun rT extT sT mT hlT heT hfuT hdT huT h1T hmT => ?_
          c0_hsteps_nogrp
          · refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
            c0_hsteps_nogrp
            exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvW.cfgOk heT hlT
              (Nat.le_trans hfuT hfuW) (Or.inr rfl) (fun _ => huT ‹_›)
              (fun h => by cases h) (fullM6HdrMem_unfocus hmTf) (hQ 20#64)
          · exact hJT () mT ⟨extT, sT, (h1T (hdT.resolve_right ‹_›)).1,
              (h1T (hdT.resolve_right ‹_›)).2, Nat.le_trans hfuT hfuW, hmT⟩
    · intro JW hJW; c0_hsteps_nogrp
      refine wp_loop_inv (fun (round, ()) mL => round.toNat ≤ 2 ∧
          ∃ extL sL, FullM6HdrInv c F0 extL sL ∧ sL.core.cur_level = 0 ∧
            sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extL sL ⋆ R) mL)
        (fun (round, ()) _ => 2 - round.toNat)
        (fun JL hJL => by
          c0_hsteps_nogrp
          exact hJL (0#64, ()) m1 ⟨Nat.zero_le _, ext1, s1, hinv1, hcl1,
            by rw [hfu1]; exact Nat.le_refl _, hm1⟩)
        (fun JL (round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ hJL => ?_)
      · refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
        c0_hsteps_nogrp
        · have hnd_lt : round.toNat < 2 := BitVec.lt_def.mp ‹_›
          have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by c0_bound
          refine wp_join_group (ts := []) (fun _ mD => ∃ extD sD, FullM6HdrInv c F0 extD sD ∧
              sD.core.cur_level = 0 ∧ sD.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c extD sD ⋆ R) mD) ?_ ?_
          · rintro _ _ mD ⟨extD, sD, hinvD, hclD, hfuD, hmD⟩
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mS => ∃ extS sS, FullM6HdrInv c F0 extS sS ∧
                sS.core.cur_level = 0 ∧ sS.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c extS sS ⋆ R) mS) ?_ ?_
            · rintro _ _ mS ⟨extS, sS, hinvS, hclS, hfuS, hmS⟩
              refine wp_m6Hdr_focus_frame hmS fun hmSf => ?_
              c0_hsteps_nogrp
              · exact hJW (round, ()) mS ⟨extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
              · exact hJL (round + 1#64, ()) mS (by dsimp only; omega)
                  ⟨by omega, extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
            · intro JS hJS; refine wp_m6Hdr_focus_frame hmD fun hmDf => ?_
              c0_hsteps_nogrp
              · c0_call hSubst
                refine ⟨c, F0, sD, m6ExtMem (m6ExtAddr c.hdr) extD ⋆ R, rfl, hinvD.sparse, hmDf,
                  fun rS sS mS hspS hclS hfuS hdS huS hmS => ?_⟩
                have hinvS := FullM6HdrInv.mk_inv hinvD.cfgOk hinvD.extOk hspS
                have hmS' := fullM6HdrMem_unfocus hmS
                c0_hsteps_nogrp
                · refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                  c0_hsteps_nogrp
                  exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvS.cfgOk hinvS.extOk
                    hinvS.sparse.lengths (Nat.le_trans hfuS hfuD) (Or.inr rfl)
                    (fun _ => huS ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmSf) (hQ 20#64)
                · exact hJS () mS ⟨extD, sS, hinvS, hclS, Nat.le_trans hfuS hfuD, hmS'⟩
              · exact hJS () mD ⟨extD, sD, hinvD, hclD, hfuD, fullM6HdrMem_unfocus hmDf⟩
          · intro JD hJD
            c0_hsteps_nogrp; c0_call hEnter
            refine ⟨c, F0, sL, m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R, rfl, hinvL.sparse, hmLf,
              fun ok sE mE hclE hfuE hdenE hspE hmE => ?_⟩
            have hmE' := fullM6HdrMem_unfocus hmE
            c0_hsteps_nogrp
            · have hdenE' := hdenE ‹_›
              refine wp_join_group (ts := []) (fun _ mC => ∃ extC sC,
                  FullM6HdrCfgOk c ∧ M6HdrExtOk extC ∧ FullDenseInv c F0 sC ∧
                  sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullM6HdrMem c extC sC ⋆ R) mC) ?_ ?_
              · rintro _ _ mC ⟨extC, sC, _, hextC, hdenC, hfuC, hmC⟩
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun _ mW2 => ∃ extW2 sW2,
                    FullM6HdrCfgOk c ∧ M6HdrExtOk extW2 ∧ FullDenseInv c F0 sW2 ∧
                    sW2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c extW2 sW2 ⋆ R) mW2) ?_ ?_
                · rintro _ _ mW2 ⟨extW2, sW2, _, hextW2, hdenW2, hfuW2, hmW2⟩
                  refine wp_m6Hdr_focus_frame hmW2 fun hmW2f => ?_
                  c0_hsteps_nogrp; c0_call hRebuild
                  refine ⟨c, F0, sW2, m6ExtMem (m6ExtAddr c.hdr) extW2 ⋆ R, rfl, hdenW2, hmW2f,
                    fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                  have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextW2 hspR
                  have hmR' := fullM6HdrMem_unfocus hmR
                  have hfuR' := Nat.le_trans hfuR hfuW2
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                      hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · exact hJD () mR ⟨extW2, sR, hinvR, hclR, hfuR', hmR'⟩
                · intro JW2 hJW2
                  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                    hinvL.cfgOk hextC hdenC.lengths hmC
                    fun ⟨del2, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                  have hdenCd := fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres
                  have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcCd]; exact hfuC
                  c0_hsteps_nogrp
                  · exact hJW2 () mCd ⟨extCd, sCd, hinvL.cfgOk, hextCd, hdenCd, hfuCd, hmCd⟩
                  · refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                    c0_hsteps_nogrp; c0_call hSweep
                    refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenCd,
                      hmCdf, fun rS sS mS hdenS _ hfuS _ huS hmS => ?_⟩
                    have hfuS' := Nat.le_trans hfuS hfuCd
                    c0_hsteps_nogrp
                    · c0_call hRebuild
                      refine ⟨c, F0, sS, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenS, hmS,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuS') (Or.inr rfl)
                        (fun _ => huS ‹_›) (fun h => by cases h)
                        (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                    · have hmS' := fullM6HdrMem_unfocus hmS
                      refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                          M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                          sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                        (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ =>
                          hJW2 () mSd ⟨extSd, sSd, hinvL.cfgOk, hextSd, hdenSd, hfuSd, hmSd⟩) ?_
                      intro JSd hJSd; c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                          M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                          sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                        (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ => by
                          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                            hinvL.cfgOk hextSd hdenSd.lengths hmSd
                            fun _ extSd' sSd' mSd' hcSd hlSd hmsSd hextSd' _ hmSd' => ?_
                          exact hJSd () mSd' ⟨extSd', sSd', hextSd',
                            fullDenseInv_of_core_eq hdenSd hlSd hcSd hmsSd.extPres,
                            by rw [hcSd]; exact hfuSd, hmSd'⟩) ?_
                      intro JSdb hJSdb
                      refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                      c0_hsteps_nogrp
                      · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                          hinvL.cfgOk hextCd hdenS.lengths (fullM6HdrMem_unfocus hmSf)
                          fun _ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
                        exact hJSd () mSd ⟨extSd, sSd, hextSd,
                          fullDenseInv_of_core_eq hdenS hlSd hcSd hmsSd.extPres,
                          by rw [hcSd]; exact hfuS', hmSd⟩
                      · exact hJSdb () mS
                          ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
                      · exact hJSdb () mS
                          ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
              · intro JC hJC
                refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                  hinvL.cfgOk hinvL.extOk hdenE'.lengths hmE'
                  fun ⟨del1, ⟨⟩⟩ extEd sEd mEd hcEd hlEd hmsEd hextEd _ hmEd => ?_
                have hdenEd := fullDenseInv_of_core_eq hdenE' hlEd hcEd hmsEd.extPres
                have hfuEd : sEd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hcEd]; exact Nat.le_trans hfuE hfuL
                c0_hsteps_nogrp
                · exact hJC () mEd ⟨extEd, sEd, hinvL.cfgOk, hextEd, hdenEd, hfuEd, hmEd⟩
                · refine wp_m6Hdr_focus_frame hmEd fun hmEdf => ?_
                  c0_hsteps_nogrp; c0_call hCong
                  refine ⟨c, F0, sEd, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenEd, hmEdf,
                    fun rC sC mC hdenC hfuC hdomC huC hmC => ?_⟩
                  have hfuC' : sC.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfuC]; exact hfuEd
                  c0_hsteps_nogrp
                  · c0_call hRebuild
                    refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenC, hmC,
                      fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                    have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextEd hspR
                    have hmR' := fullM6HdrMem_unfocus hmR
                    refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                      hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                      (fun _ => huC ‹_›) (fun h => by cases h)
                      (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · have hmC' := fullM6HdrMem_unfocus hmC
                    refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                        M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                        sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                      (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ =>
                        hJC () mCd ⟨extCd, sCd, hinvL.cfgOk, hextCd, hdenCd, hfuCd, hmCd⟩) ?_
                    intro JCd hJCd; c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                        M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                        sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                      (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ => by
                        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                          hinvL.cfgOk hextCd hdenCd.lengths hmCd
                          fun _ extCd' sCd' mCd' hcCd hlCd hmsCd hextCd' _ hmCd' => ?_
                        exact hJCd () mCd' ⟨extCd', sCd', hextCd',
                          fullDenseInv_of_core_eq hdenCd hlCd hcCd hmsCd.extPres,
                          by rw [hcCd]; exact hfuCd, hmCd'⟩) ?_
                    intro JCdb hJCdb
                    refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                    c0_hsteps_nogrp
                    · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                        hinvL.cfgOk hextEd hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                        fun _ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                      exact hJCd () mCd ⟨extCd, sCd, hextCd,
                        fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres,
                        by rw [hcCd]; exact hfuC', hmCd⟩
                    · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                    · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
            · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hinvL.extOk (hspE ‹_›)
              refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
              c0_hsteps_nogrp
              exact fid_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hinvE.extOk
                hinvE.sparse.lengths (Nat.le_trans hfuE hfuL) (Or.inr rfl)
                (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
            · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hinvL.extOk (hspE ‹_›)
              exact hJD () mE ⟨extL, sE, hinvE, hclE, Nat.le_trans hfuE hfuL, hmE'⟩
        · exact hJW (round, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, fullM6HdrMem_unfocus hmLf⟩
  · intro J1 hJ1; c0_hsteps_nogrp
    · exact hJ1 () m0 ⟨ext0, s0, hinv0, hcl0', hc0 ▸ rfl, hm0⟩
    · refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
      c0_hsteps_nogrp; c0_call hNlog; intro nlogp _
      c0_hsteps_nogrp; c0_call hScale
      refine ⟨c, _, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl,
        (fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
          (s0.scratch.probings + 1#64)).1, by assumption, fun sd => ?_⟩
      c0_hsteps_nogrp
      have hst1 := fullState_upd_probe_step hinv0.sparse.lengths
        (s0.scratch.conflicts + sd) (s0.scratch.probings + 1#64)
      have hinv1 := fullM6HdrInv_of_probeStep hinv0 hst1
      exact hJ1 () _ ⟨ext0, _, hinv1, hst1.2.1 ▸ hcl0',
        by rw [hst1.2.1, hc0], fullM6HdrMem_unfocus (by assumption)⟩

/-! ## 6. `full_eliminate_fid_wp` (`FullFastSched.schedEliminateSpec`) -/

theorem full_eliminate_fid_wp (Γ : Env)
    (hDticks : ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hNlog : ∀ a m Q X, fidNlogpownSpec a m Q X →
      Γ "full_nlogpown_fid" [i64, i64, i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m7" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ full_eliminate_fid_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hinv0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_eliminate_fid_body
  c0_hsteps_nogrp
  c0_call hDticks
  refine ⟨c, s0, R, rfl, hinv0.lengths, hm0, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, _, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      c0_call hEnter
      refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
      intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
      c0_hsplit
      · have hden2 : FullDenseInv c F0 s2 := hok_d hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun b => (b, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            c0_call hMin; intro fbud _
            c0_hsteps_nogrp
            c0_call hFwd
            refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
            intro fs s3 m3 hden3 hcv3 hfu3 _ huf3 hm3
            have hcv2_le := hden2.lengths.core_ok.cur_vars_le
            let s3r : FullState :=
              { s3 with scratch := { s3.scratch with fwd_sub_cnt := s2.scratch.fwd_sub_cnt } }
            have hden3r : FullDenseInv c F0 s3r :=
              FullM3CongBva.fullDenseInv_with_scratch_keep hden3
                { hden3.lengths.scratch_ok with
                  walk_vals_len := hden3.lengths.scratch_ok.walk_vals_len } rfl rfl
            have hfu3r : s3r.core.fuel.toNat ≤ s0.core.fuel.toNat := by
              change s3.core.fuel.toNat ≤ s0.core.fuel.toNat; rw [hfu3]; omega
            c0_hsplit
            · c0_hsteps_nogrp
              c0_call hReb
              refine ⟨c, F0, s3r, R, rfl, hden3r, hm, ?_⟩
              intro _ s4 m4 hsp4 hcl4 hfu4 _ _ hm4
              c0_hsteps!
              exact hQ 20#64 s4 m4 hsp4 hcl4 (by omega) (Or.inr rfl) (fun _ => huf3 hc) hm4
            · let cv3 := s3r.core.cur_vars
              have hcv3_le : cv3 ≤ c.max_vars := hden3r.lengths.core_ok.cur_vars_le
              have htl3 := hden3r.lengths.scratch_ok.tarjan_mark_len
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i64])
                (fun rem_t (ti, ()) mt => ∃ tmki : List (BitVec 32),
                  tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv3 ∧ rem_t = cv3 - ti.toNat ∧
                  (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                  (FullMem c { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } } ⋆
                    R) mt)
                ?_ ?_
              · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨tmki, htli, hti_le, rfl, hinit, hmt⟩
                c0_hsplit
                · have hti_lt : ti.toNat < cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                  have hti_b : ti.toNat < tmki.length := by omega
                  have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by c0_bound
                  c0_hsteps!
                  exact hLt (cv3 - (ti + 1#64).toNat) (ti + 1#64, ()) _ (by omega)
                    ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega, rfl, fun k hk => by
                       rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hti1 ▸ hk)) with h | h
                       · rw [List.getElem?_set_ne (by omega)]; exact hinit k h
                       · subst h; rw [List.getElem?_set_self hti_b, Option.getD_some], hm⟩
                · have hti_eq : ti.toNat = cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc
                    change ¬ti.toNat < cv3 at hc; omega
                  rw [hti_eq] at hinit
                  let s3t : FullState :=
                    { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } }
                  have hden3t : FullDenseInv c F0 s3t :=
                    FullM3CongBva.fullDenseInv_with_scratch_keep hden3r
                      { hden3r.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
                  have htmk3t : FullDefSweep.TmkZero s3t := fun v hv => hinit v hv
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                    (fun b => (b, ())) (fun _ => True)
                    (fun _ bve_lim _ => by
                      c0_hsteps_nogrp
                      c0_call hBve
                      refine ⟨c, F0, s3t, R, rfl, hden3t, htmk3t, hmt, ?_⟩
                      intro res s4 m4 hden4 _ hfu4 _ hres_u hm4
                      have hfu4' : s4.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        dsimp only [s3t, s3r] at hfu4
                        have hfu3' : s3.core.fuel.toNat ≤ s0.core.fuel.toNat := hfu3r
                        omega
                      c0_hsteps_nogrp
                      refine wp_join_state0 (α := FullState)
                        (fun sf mf => FullDenseInv c F0 sf ∧
                          sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf)
                        (fun _ sf mf ⟨hdenf, hfuf, hmf⟩ => by
                          c0_hsteps_nogrp
                          c0_call hReb
                          refine ⟨c, F0, sf, R, rfl, hdenf, hmf, ?_⟩
                          intro rr se me hspe hcle hfue _ hue hme
                          let se' : FullState :=
                            { se with scratch :=
                              { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                          have hspe' : FullSparseInv c F0 se' :=
                            FullM3CongBva.fullSparseInv_with_scratch_keep hspe
                              { hspe.lengths.scratch_ok with
                                walk_vals_len := hspe.lengths.scratch_ok.walk_vals_len } rfl rfl
                          have hfue' : se'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                            change se.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
                          c0_hsteps!
                          · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                              (fun _ => hres_u hc) hm
                          · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                              (fun _ => hue hc) hm
                          · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                              (fun _ => hspe'.inconsistent_unsat hc) hm
                          · exact hQ 1#64 se' _ hspe' hcle hfue' (Or.inl rfl)
                              (fun h => by cases h) hm)
                        (fun Jf hJf => by
                          c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_join_state0 (α := FullState)
                              (fun sg mg => FullDenseInv c F0 sg ∧
                                sg.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sg ⋆ R) mg)
                              (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                                c0_hsteps_nogrp
                                refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                                  (fun b => (b, ())) (fun _ => True)
                                  (fun _ _ _ => by
                                    c0_hsteps_nogrp
                                    c0_call hMin; intro fact_bud _
                                    c0_hsteps_nogrp
                                    c0_call hFact
                                    refine ⟨c, F0, sg, R, rfl, hdeng, hmg, ?_⟩
                                    intro _ sf0 mf0 hdenf0 _ hfuf0 _ hmf0
                                    c0_hsteps!
                                    let sf1 : FullState :=
                                      { sf0 with scratch :=
                                        { sf0.scratch with elim_bound := sg.scratch.elim_bound } }
                                    have hdenf1 : FullDenseInv c F0 sf1 :=
                                      FullM3CongBva.fullDenseInv_with_scratch_keep hdenf0
                                        { hdenf0.lengths.scratch_ok with
                                          walk_vals_len :=
                                            hdenf0.lengths.scratch_ok.walk_vals_len } rfl rfl
                                    exact hJf sf1 _ ⟨hdenf1, by
                                      change sf0.core.fuel.toNat ≤ s0.core.fuel.toNat
                                      rw [hfuf0]; exact hfug, hm⟩)
                                  (fun Jfb hJfb => by
                                    c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial)))
                              (fun Jdo hJdo => by
                                c0_hsteps!
                                · exact hJdo s4 m4 ⟨hden4, hfu4', hm4⟩
                                · exact hJdo s4 m4 ⟨hden4, hfu4', hm4⟩
                                · exact hJf s4 m4 ⟨hden4, hfu4', hm4⟩)
                          · c0_hsteps!; exact hJf s4 m4 ⟨hden4, hfu4', hm4⟩))
                    (fun Jb hJb => by
                      c0_hsplit
                      · c0_hsteps!; exact hJb _ trivial
                      · c0_hsteps_nogrp; c0_call hMin; intro b _; c0_hsteps!; exact hJb b trivial)
              · intro Lt hLt; c0_hsteps!
                exact hLt cv3 (0#64, ()) _
                  ⟨s3r.scratch.tarjan_mark, htl3, Nat.zero_le _, by simp,
                   fun _ h => by simp at h, hm⟩)
          (fun Jfb hJfb => by c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial))
      · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
        let s2' : FullState :=
          { s2 with scratch := { s2.scratch with fwd_str_cnt := s2.scratch.search_ticks } }
        have hsp2' : FullSparseInv c F0 s2' := FullM3CongBva.fullSparseInv_with_scratch_keep hsp2
          { hsp2.lengths.scratch_ok with walk_vals_len := hsp2.lengths.scratch_ok.walk_vals_len }
          rfl rfl
        have hfu2' : s2'.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hfu2 hfu1
        c0_hsteps!
        · exact hQ 20#64 s2' _ hsp2' hcl2 hfu2' (Or.inr rfl)
            (fun _ => hsp2'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s2' _ hsp2' hcl2 hfu2' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps!; exact hJ1 s0 m0 ⟨hinv0, hcl0, Nat.le_refl _, hm0⟩
      · c0_hsteps_nogrp
        let s0a : FullState :=
          { s0 with scratch := { s0.scratch with eliminations := s0.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c := ⟨hinv0.lengths.core_ok,
          { hinv0.lengths.scratch_ok with walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }⟩
        c0_call hNlog; intro nloge _; c0_hsteps_nogrp
        c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, fun delta => ?_⟩; c0_hsteps!
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b := FullM3CongBva.fullSparseInv_with_scratch_keep hinv0
          { hinv0.lengths.scratch_ok with walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }
          rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

/-! ## 7. `full_preprocess_fid_wp` (`FullM6.fullM6PreprocessSpec`) -/

private theorem fid_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', FullM6BcpS15.fullBcpS15Spec (c.hdr, ()) m Q' X' →
      Γ "full_propagate" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → s'.core.cur_level = s.core.cur_level →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom _ hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' rfl htr' hperm' hfu' hdom hr1
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid_conflict_level0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private abbrev FidPrePost (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) c' ext' s' m',
    FullM4Compact.FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' →
    M6HdrExtOk ext' → (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
    s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
    (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
    (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
    (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem fidPre_ret10 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : FidPrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (10#64, ()) m' :=
  hQ 10#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk
    (Or.inr (Or.inr (Or.inl rfl))) hfu (fun h => by cases h) (fun h => by cases h)
    (fun _ => hinv.sparse.2.2.2.1.2) hm

private theorem fidPre_ret20 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : FidPrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hlen : s'.LengthsOk c') (hcfg : FullM6HdrCfgOk c') (hext : M6HdrExtOk ext')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hu : F0.Unsat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (20#64, ()) m' :=
  hQ 20#64 c' ext' s' m' hcmp hlen hcfg hext (Or.inr (Or.inr (Or.inr rfl))) hfu
    (fun _ => hu) (fun h => by cases h) (fun h => by cases h) hm

private theorem fidPre_ret20_inc {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : FidPrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hinc : s'.core.inconsistent ≠ 0#64) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (20#64, ()) m' :=
  fidPre_ret20 hQ hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk hfu
    (fullM6HdrInv_inconsistent_unsat hinv hinc) hm

private theorem fidPre_ret0_inv {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : FidPrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (0#64, ()) m' :=
  hQ 0#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk (Or.inl rfl) hfu
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm

private theorem fid_pre_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    {Q : Post [i64]} {X : XPost} {J2 : Cont []}
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hinv1 : FullM6HdrInv c F0 ext s1) (hcl1' : s1.core.cur_level = 0)
    (hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm1 : (FullM6HdrMem c ext s1 ⋆ R) m1)
    (hJ2 : ∀ xs m2, (∃ s2, FullM6HdrInv c F0 ext s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s2 ⋆ R) m2) → J2 xs m2)
    (hQ : FidPrePost c F0 s R Q) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_7 =>
      Expr.load i64 (Arg.var p_7.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_8 =>
          Expr.jnz (Arg.var p_8.fst)
            (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ())
                fun p_9 =>
              Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_9.fst, Arg.imm 2, ()))
                  fun p_10 =>
                Expr.jnz (Arg.var p_10.fst) (Expr.ret (Arg.imm 20, ()))
                  (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                      fun p_11 =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                        (Arg.var p_11.fst, Arg.imm 1, ())) fun p_12 =>
                      Expr.jnz (Arg.var p_12.fst) (Expr.ret (Arg.imm 20, ()))
                        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                          Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst) (Expr.jump J2 ()))))
            (Expr.jump J2 ())) m1 := by
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
    c0_call hSweep
    refine ⟨c, F0, F_cur1, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
      hinv1.sparse.lengths, hw1, hinv1.sparse.2.2.1, hinv1.sparse.2.2.2.2,
      fun hpos => by omega, hm1f,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen'
        wu' fred' ni' nr' nb' oom' sc' mS hlenS hsr hexlenS hws2S hllS hwS hndS
        _ _ _ h20S _ hmS => ?_⟩
    have hmS' := fullM6HdrMem_unfocus hmS; let sSc : FullCoreState := { s1.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      arena := arena', arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := 0#64,
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      oom := oom' }
    let sS : FullState := { core := sSc, scratch := sc' }
    have hinvWS : FullM6HdrInvW c F0 F_cur1 ext sS :=
      FullM6HdrInvW.mk_inv hinv1.cfgOk hinv1.extOk
        ⟨hlenS, hwS, hinv1.sparse.2.1, hndS,
          ⟨hllS, (by change sc'.extend_len ≤ c.extend_cap; rw [hexlenS]
                     exact hinv1.sparse.2.2.2.1.2)⟩,
          hinv1.sparse.2.2.2.2⟩
    c0_hsteps_nogrp
    · exact fidPre_ret20 hQ (.refl c) hlenS hinvWS.cfgOk hinvWS.extOk hfu1 (h20S ‹_›).2 hmS'
    · refine fid_call_bcp rfl (fun _ _ h => hProp _ _ _ _ h) hinvWS hmS'
        fun pr sP mP hinvWP hclP _ _ hfuP _ hrP1 hmP => ?_
      have hinvP := hinvWP.toInv; have hfuP' := Nat.le_trans hfuP hfu1
      c0_hsteps_nogrp
      · exact fidPre_ret20 hQ (.refl c) hinvP.sparse.lengths hinvP.cfgOk hinvP.extOk hfuP'
          (fid_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hcl1') (hrP1 ‹_›).2.2) hmP
      · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
        c0_hsteps_nogrp
        have hinvP' : FullM6HdrInv c F0 ext
            { sP with core := { sP.core with unflushed := 0#64 } } :=
          FullM6HdrInv.mk_inv hinvP.cfgOk hinvP.extOk ⟨⟨⟨{ hinvP.sparse.lengths.core_ok with
              vals_len := hinvP.sparse.lengths.core_ok.vals_len }, hinvP.sparse.lengths.scratch_ok⟩,
            ⟨F_cur1, { hinvWP.sparseW.2.1 with
              arena := { hinvWP.sparseW.2.1.arena with len_ok := hinvWP.sparseW.2.1.arena.len_ok }
              watches := hinvWP.sparseW.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
              }⟩⟩, hinvP.sparse.2.1, hinvP.sparse.2.2.1, hinvP.sparse.2.2.2.1, hinvP.sparse.2.2.2.2⟩
        exact hJ2 () _ ⟨_, hinvP', hclP ▸ hcl1', hfuP', fullM6HdrMem_unfocus (by assumption)⟩
  · exact hJ2 () m1 ⟨s1, hinv1, hcl1', hfu1, fullM6HdrMem_unfocus hm1f⟩

private theorem fid_pre_compact_step {Γ : Env} {c c0 : FullCfg} {hdr : BitVec 64}
    {F0 : CNF Nat} {ext : List (BitVec 64)} {s s0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post [i64]} {X : XPost} {JC : Cont []}
    (hCompNeed : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hhdr : c0.hdr = hdr)
    (hcmp0 : FullM4Compact.FullCfgCompat c c0) (hinv0 : FullM6HdrInv c0 F0 ext s0)
    (hcl0 : s0.core.cur_level = 0) (hfu0 : s0.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm0f : (FullMem c0 s0 ⋆ (m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R)) m0)
    (hJC : ∀ xs mC, (∃ cC sC, FullM4Compact.FullCfgCompat c cC ∧
      FullM6HdrInv cC F0 ext sC ∧ sC.core.cur_level = 0 ∧
      sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem cC ext sC ⋆ R) mC) → JC xs mC)
    (hQ : FidPrePost c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [.bool]) "full_compact_needed" (Arg.var hdr, ())
        fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var hdr, ()) fun p_13 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 20, ()))
              fun p_14 =>
            Expr.jnz (Arg.var p_14.fst) (Expr.ret (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 1, ()))
                  fun p_15 =>
                Expr.jnz (Arg.var p_15.fst) (Expr.ret (Arg.imm 0, ())) (Expr.jump JC ())))
        (Expr.jump JC ())) m0 := by
  subst hhdr
  have hlen0 := hinv0.sparse.lengths
  c0_hsteps_nogrp; c0_call hCompNeed
  refine ⟨c0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hlen0,
    by have := hlen0.core_ok.trail_end_le; have := hlen0.core_ok.cur_vars_le
       have := c0.hmaxv; unfold dimacsBound at *; omega,
    hm0f, fun need _ => ?_⟩
  c0_hsteps_nogrp
  · c0_call hCompact
    refine ⟨c0, F0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hinv0.sparse, hm0f,
      fun rC cC sC mC hcmpC hspC hrC _ hfuC huC h1C hmC => ?_⟩
    have hcfgC := M6HdrCfgOk_of_le (by rw [hcmpC.hdr]; exact M6HdrCfgOk_le hinv0.cfgOk)
    have hinvC := FullM6HdrInv.mk_inv hcfgC hinv0.extOk hspC; have hfuC' := Nat.le_trans hfuC hfu0
    have hmC' := fullM6HdrMem_unfocus (hcmpC.hdr ▸ hmC); have hcmpC' := hcmp0.trans hcmpC
    c0_hsteps_nogrp
    · exact fidPre_ret20 hQ hcmpC' hspC.lengths hcfgC hinvC.extOk hfuC' (huC ‹_›) hmC'
    · exact fidPre_ret0_inv hQ hcmpC' hinvC hfuC' hmC'
    · exact hJC () mC ⟨cC, sC, hcmpC', hinvC, h1C ‹_›, hfuC', hmC'⟩
  · exact hJC () m0 ⟨c0, s0, hcmp0, hinv0, hcl0, hfu0, fullM6HdrMem_unfocus hm0f⟩

theorem full_preprocess_fid_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X →
      Γ "full_lucky" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, fidProbeSpec a m Q X →
      Γ "full_probe_fid" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Γ "full_eliminate_fid" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ full_preprocess_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6PreprocessSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_preprocess_fid_body
  obtain ⟨F_cur, hw0⟩ := hinv.sparse.1.witness
  have hinvW0 : FullM6HdrInvW c F0 F_cur ext s := FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
    ⟨hinv.sparse.lengths, hw0, hinv.sparse.2.1, hinv.sparse.2.2.1, hinv.sparse.2.2.2.1,
      hinv.sparse.2.2.2.2⟩
  c0_hsteps_nogrp
  refine fid_call_bcp rfl (fun _ _ h => hProp _ _ _ _ h) hinvW0 hm
    fun r1 s1 m1 hinvW1 hcl1 _ _ hfu1 _ hr1_1 hm1 => ?_
  have hinv1 := hinvW1.toInv; have hcl1' : s1.core.cur_level = 0 := hcl1 ▸ hcl0
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · exact fidPre_ret20 hQ (.refl c) hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk hfu1
      (fid_conflict_level0_unsat hinvW1.sparseW.2.1 hcl1' (hr1_1 ‹_›).2.2)
      (fullM6HdrMem_unfocus hm1f)
  · exact fidPre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · exact fidPre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
      refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
      c0_hsteps_nogrp
      · exact fidPre_ret10 hQ (.refl c) hinv2 hfu2 (fullM6HdrMem_unfocus hm2f)
      · c0_call hLucky
        refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hcl2, hm2f,
          fun lk s3 m3 hlen3 hlk hfu3 _ hu3 hsp3 h10_3 hm3 => ?_⟩
        have hm3' := fullM6HdrMem_unfocus hm3; have hfu3' := Nat.le_trans hfu3 hfu2
        let mkInv3 : lk ≠ 20#64 → lk ≠ 10#64 →
            FullM6HdrInv c F0 ext s3 ∧ s3.core.cur_level = 0 := fun h20 h10 =>
          let h02 : lk = 0#64 ∨ lk = 2#64 := by
            rcases hlk with rfl | rfl | rfl | rfl <;>
              (first | exact Or.inl rfl | exact Or.inr rfl | contradiction)
          let ⟨hs3, hc3⟩ := hsp3 h02
          ⟨FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hs3, hc3⟩
        c0_hsteps_nogrp
        · rw [‹lk = 20#64›]
          exact fidPre_ret20 hQ (.refl c) hlen3 hinv2.cfgOk hinv2.extOk hfu3' (hu3 ‹_›) hm3'
        · rw [‹lk = 10#64›]
          exact hQ 10#64 c ext s3 m3 (.refl c) hlen3 hinv2.cfgOk hinv2.extOk
            (Or.inr (Or.inr (Or.inl rfl))) hfu3' (fun _ => by cases ‹_›)
            (fun h => by cases h) (fun _ => h10_3 ‹_›) hm3'
        · exact fidPre_ret20_inc hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' ‹_› hm3'
        · exact fidPre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · exact fidPre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · obtain ⟨hinv3, hcl3⟩ := mkInv3 ‹_› ‹_›
          refine wp_join_group (fun (_ : Tup Val []) m4 => ∃ c4 s4,
              FullM4Compact.FullCfgCompat c c4 ∧ FullM6HdrInv c4 F0 ext s4 ∧
              s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c4 ext s4 ⋆ R) m4) ?_ ?_
          · rintro _ _ m4 ⟨c4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩; rw [← hcmp4.hdr]
            refine wp_m6Hdr_focus_frame hm4 fun hm4f => ?_
            c0_hsteps_nogrp
            · exact fidPre_ret20_inc hQ hcmp4 hinv4 hfu4 ‹_› (fullM6HdrMem_unfocus hm4f)
            · exact fidPre_ret0_inv hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
            · exact fidPre_ret10 hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
            · c0_call hScale
              refine ⟨c4, s4, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl, hinv4.sparse.lengths,
                hm4f, fun sd1 => ?_⟩
              c0_hsteps_nogrp; c0_call hScale
              refine ⟨c4, _, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl,
                (fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings).1,
                by assumption, fun sd2 => ?_⟩
              c0_hsteps_nogrp
              have hst4 := fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings
              have hst4' := fullState_upd_elim_step hst4.1 sd2 s4.scratch.eliminations
                s4.scratch.elim_bound
              have hinv4' := fullM6HdrInv_of_probeStep hinv4 (probeStep_trans hst4 hst4')
              have hm4' := fullM6HdrMem_unfocus (by assumption)
              c0_call hProbe
              refine fidProbeSpec_of hinv4' (by rw [hst4'.2.1, hst4.2.1]; exact hcl4) hm4'
                fun r5 ext5 s5 m5 hlen5 hext5 hfu5 hr5 hu5 h15 hm5 => ?_
              have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hst4'.2.1, hst4.2.1] at hfu5; exact Nat.le_trans hfu5 hfu4
              c0_hsteps_nogrp
              · exact fidPre_ret20 hQ hcmp4 hlen5 hinv4'.cfgOk hext5 hfu5' (hu5 ‹_›) hm5
              · obtain ⟨hinv5, hcl5⟩ := h15 (hr5.resolve_right ‹_›)
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
                c0_hsteps_nogrp
                · exact fidPre_ret20_inc hQ hcmp4 hinv5 hfu5' ‹_› (fullM6HdrMem_unfocus hm5f)
                · exact fidPre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                · exact fidPre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                · c0_call hElim
                  refine ⟨c4, F0, s5, m6ExtMem (m6ExtAddr c4.hdr) ext5 ⋆ R, rfl, hinv5.sparse,
                    hcl5, hm5f, fun rE s5e m5e hsp5e hcl5e hfu5e hr5e hu5e hm5e => ?_⟩
                  have hinv5e := FullM6HdrInv.mk_inv hinv5.cfgOk hext5 hsp5e
                  have hm5e' := fullM6HdrMem_unfocus hm5e; have hfu5e' := Nat.le_trans hfu5e hfu5'
                  c0_hsteps_nogrp
                  · exact fidPre_ret20 hQ hcmp4 hsp5e.lengths hinv5e.cfgOk hext5 hfu5e'
                      (hu5e ‹_›) hm5e'
                  · exact fidPre_ret20_inc hQ hcmp4 hinv5e hfu5e' ‹_› hm5e'
                  · exact fidPre_ret0_inv hQ hcmp4 hinv5e hfu5e' hm5e'
                  · exact fidPre_ret0_inv hQ hcmp4 hinv5e hfu5e' hm5e'
                  · refine wp_join_group (fun (_ : Tup Val []) m6 => ∃ c6 s6,
                        FullM4Compact.FullCfgCompat c c6 ∧ FullM6HdrInv c6 F0 ext5 s6 ∧
                        s6.core.cur_level = 0 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c6 ext5 s6 ⋆ R) m6) ?_ ?_
                    · rintro _ _ m6 ⟨c6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
                      rw [hcmp4.hdr, ← hcmp6.hdr]
                      refine wp_m6Hdr_focus_frame hm6 fun hm6f => ?_
                      c0_hsteps_nogrp
                      · exact fidPre_ret20_inc hQ hcmp6 hinv6 hfu6 ‹_› (fullM6HdrMem_unfocus hm6f)
                      · exact fidPre_ret0_inv hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                      · exact fidPre_ret10 hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                      · c0_call hScale
                        refine ⟨c6, s6, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                          hinv6.sparse.lengths, hm6f, fun sd3 => ?_⟩
                        c0_hsteps_nogrp; c0_call hScale
                        refine ⟨c6, _, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                          (fullState_upd_probe_step hinv6.sparse.lengths sd3
                            s6.scratch.probings).1,
                          by assumption, fun sd4 => ?_⟩
                        c0_hsteps_nogrp
                        have hst6 := fullState_upd_probe_step hinv6.sparse.lengths sd3
                          s6.scratch.probings
                        have hst6' := fullState_upd_elim_step hst6.1 sd4 s6.scratch.eliminations
                          s6.scratch.elim_bound
                        have hinv6' := fullM6HdrInv_of_probeStep hinv6
                          (probeStep_trans hst6 hst6')
                        exact hQ 1#64 c6 ext5 _ _ hcmp6 hinv6'.sparse.lengths hinv6'.cfgOk
                          hinv6'.extOk (Or.inr (Or.inl rfl))
                          (by rw [hst6'.2.1, hst6.2.1]; exact hfu6) (fun h => by cases h)
                          (fun _ => ⟨hinv6', by rw [hst6'.2.1, hst6.2.1]; exact hcl6⟩)
                          (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
                    · exact fun _ hJC2 => fid_pre_compact_step hCompNeed hCompact rfl hcmp4 hinv5e
                        hcl5e hfu5e' hm5e hJC2 hQ
          · exact fun _ hJC1 => fid_pre_compact_step hCompNeed hCompact rfl (.refl c)
              hinv3 hcl3 hfu3' hm3 hJC1 hQ
    · exact fun _ hJ2 =>
        fid_pre_unflushed hProp hSweep hinv1 hcl1' hfu1 (fullM6HdrMem_unfocus hm1f) hJ2 hQ

/-! ## 8. Closed `38`-Row `fidSchedSpecTable`, `fidSchedEnv`, and `ModuleOk` -/

section ModuleOkSection

private def fidSchedDefRows : List SpecEntry :=
  [ ⟨"full_ilog10_fid", [i64], [i64], fidIlog10ExactSpec, true⟩
  , ⟨"full_nlogpown_fid", [i64, i64, i64], [i64], fidNlogpownSpec, true⟩
  , ⟨"full_calc_max_v_fid", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩
  , ⟨"full_reduce_fid", [i64, .bool], [i64], m6ReduceSpec, true⟩
  , ⟨"full_probe_fid", [i64, .bool], [i64], fidProbeSpec, true⟩
  , ⟨"full_eliminate_fid", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  , ⟨"full_preprocess_fid", [i64], [i64], fullM6PreprocessSpec, true⟩ ]

private def fidSchedExtRows : List SpecEntry :=
  [ ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩
  , ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], FullM6BcpS15.fullBcpS15Spec, true⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullDefSweep.fullCongruenceDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullM3CongBva.fullSweepDenseSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], fidProbeTailSpec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullM3CongBva.fullFactorHeapSpec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  , ⟨"full_forward_sub_m7", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
  , ⟨"full_compact_needed", [i64], [.bool], FullM6CompactFlush.fullCompactNeededM6Spec, true⟩
  , ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩ ]

/-- Closed `38`-row specification table for `fidSchedModule` (`7` defined functions + `31`
external callees, all `noExit = true`). -/
def fidSchedSpecTable : List SpecEntry := fidSchedDefRows ++ fidSchedExtRows

theorem fidSchedSpecTable_length : fidSchedSpecTable.length = 38 := by rfl

theorem fidSchedSpecTable_sigs :
    fidSchedSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      fidSchedModule.fns.map Fn.sig ++ fidSchedModule.externs.map Extern.sig := by rfl

theorem fidSchedSpecTable_nodup : (fidSchedSpecTable.map SpecEntry.name).Nodup := by
  have heq : fidSchedSpecTable.map SpecEntry.name =
      fidSchedModule.fns.map Fn.name ++ fidSchedModule.externs.map Extern.name := by rfl
  rw [heq]; decide

theorem fidSchedSpecTable_noExit : ∀ e ∈ fidSchedSpecTable, e.noExit = true :=
  fun e he => List.all_eq_true.mp (by rfl : fidSchedSpecTable.all (·.noExit) = true) e he

/-- Closed environment induced by `fidSchedSpecTable`. -/
def fidSchedEnv : Env := Env.ofTable fidSchedSpecTable

theorem fidSchedEnv_noExit : ∀ f as bs xs m Q X X',
    fidSchedEnv f as bs xs m Q X → fidSchedEnv f as bs xs m Q X' :=
  fun _ _ _ _ _ _ _ h => env_ofTable_noExit_all (by rfl) _ _ _ _ _ _ _ h

private theorem fidSchedEnv_row (idx : Nat) (e : SpecEntry)
    (hidx : fidSchedSpecTable[idx]? = some e) (xs : Tup Val e.as) (m : Mem 64) (Q : Post e.rs)
    (X : XPost) (hs : e.eff xs m Q X) : fidSchedEnv e.name e.as e.rs xs m Q X :=
  env_ofTable_row_at hidx fidSchedSpecTable_nodup hs

private theorem fidSched_row0_ilog_lo :
    ∀ a m Q X, fullIlog10Spec a m Q X → fidSchedEnv "full_ilog10_fid" [i64] [i64] a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hs
  exact fidSchedEnv_row 0 ⟨"full_ilog10_fid", [i64], [i64], fidIlog10ExactSpec, true⟩ rfl
    (x, ()) m Q X (fun r h1 h19 _ _ => hs r h1 h19)

theorem fidSched_tableImpl : TableImpl fidSchedEnv fidSchedFns fidSchedSpecTable := by
  let er := fun i n as rs sp (h : fidSchedSpecTable[i]? = some ⟨n, as, rs, sp, true⟩) =>
    fun a m Q X hs => fidSchedEnv_row i ⟨n, as, rs, sp, true⟩ h a m Q X hs
  let erW := fun i n ea rs
      (h : fidSchedSpecTable[i]? = some ⟨n, i64 :: ea, rs, m6HdrW2aSpec ea rs, true⟩) =>
    fun a m Q X hs => fidSchedEnv_noExit _ _ _ _ _ _ _ X
      (fidSchedEnv_row i ⟨n, i64 :: ea, rs, m6HdrW2aSpec ea rs, true⟩ h a m Q
        (fun _ _ _ _ => False) (m6HdrW2aSpec_monoX (X := X) hs))
  refine tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs =>
      full_ilog10_fid_exact_wp fidSchedEnv xs m Q X hs⟩
    (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs =>
        full_nlogpown_fid_wp fidSchedEnv
          (er 0 "full_ilog10_fid" [i64] [i64] _ rfl) xs m Q X hs⟩
      (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs =>
          full_calc_max_v_fid_wp fidSchedEnv
            (er 7 "full_fixed_bytes" [i64] [i64] _ rfl) xs m Q X hs⟩
        (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs => by
            dsimp only [SpecEntry.cast, SpecEntry.eff] at hs
            exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
              (full_reduce_fid_wp fidSchedEnv (er 8 _ _ _ _ rfl) fidSched_row0_ilog_lo
                (er 13 _ _ _ _ rfl) (erW 11 _ _ _ rfl) (erW 16 _ _ _ rfl) (er 12 _ _ _ _ rfl)
                (er 14 _ _ _ _ rfl) (er 9 _ _ _ _ rfl) (er 10 _ _ _ _ rfl) (er 15 _ _ _ _ rfl)
                xs m Q _ hs)⟩
          (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs =>
              full_probe_fid_wp fidSchedEnv (erW 17 _ _ _ rfl) (er 1 _ _ _ _ rfl)
                (er 18 _ _ _ _ rfl) (er 19 _ _ _ _ rfl) (erW 20 _ _ _ rfl) (er 21 _ _ _ _ rfl)
                (er 22 _ _ _ _ rfl) (erW 23 _ _ _ rfl) (erW 24 _ _ _ rfl) (er 25 _ _ _ _ rfl)
                (er 26 _ _ _ _ rfl) (erW 16 _ _ _ rfl) (er 27 _ _ _ _ rfl) (er 28 _ _ _ _ rfl)
                (er 29 _ _ _ _ rfl) (er 30 _ _ _ _ rfl) xs m Q X hs⟩
            (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs =>
                full_eliminate_fid_wp fidSchedEnv (er 31 _ _ _ _ rfl) (er 1 _ _ _ _ rfl)
                  (er 32 _ _ _ _ rfl) (er 19 _ _ _ _ rfl) (er 29 _ _ _ _ rfl) (er 33 _ _ _ _ rfl)
                  (er 34 _ _ _ _ rfl) (er 30 _ _ _ _ rfl) (er 22 _ _ _ _ rfl) xs m Q X hs⟩
              (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs => by
                  dsimp only [SpecEntry.cast, SpecEntry.eff] at hs
                  exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
                    (full_preprocess_fid_wp fidSchedEnv (er 10 _ _ _ _ rfl) (er 15 _ _ _ _ rfl)
                      (er 35 _ _ _ _ rfl) (er 36 _ _ _ _ rfl) (er 37 _ _ _ _ rfl)
                      (er 18 _ _ _ _ rfl) (er 4 _ _ _ _ rfl) (er 5 _ _ _ _ rfl) xs m Q _ hs)⟩
                (tableImpl_nil fidSchedEnv fidSchedExtRows)))))))

/-- Closed `ModuleOk` for `fidSchedModule` (`7` defined functions + `31` externs). -/
theorem fidSched_moduleOk : ModuleOk fidSchedEnv fidSchedModule :=
  Env.ofTable_moduleOk fidSched_acyclic (allFns_of_mem fidSched_fns_wf) fidSched_tableImpl

end ModuleOkSection

/-! ## 9. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvFid_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h0 : (cnfClause [0]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1; simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvFid_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl; have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore nvOneLitState.core → False := fun _ hr => by
    rw [show fullArenaClauseRefsCore nvOneLitState.core = [] from rfl] at hr; cases hr
  have hi0 : ∀ i, i < nvOneLitState.core.trail_end → i = 0 := fun _ hi => by rw [hte] at hi; omega
  have hL0 : ∀ L, L ≤ nvOneLitState.core.cur_level → L = 0 := fun _ hL => by rw [hcl] at hL; omega
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact .empty)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) :=
    CNF.entails_clause_def.mpr fun _ hα =>
      (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim,
        fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hi0 i hi]; decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hi0 i hi, hi0 j hj]
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hi0 i hi]; exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hp => by rw [hi0 j hj] at hp; exact absurd hp.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hi0 i hi]; exact hent0
      trail_pos_inv := fun i hi => by rw [hi0 i hi]; rfl
      level0_rsn_none := fun i hi _ => by rw [hi0 i hi]; rfl
      frame_trail_lt := fun L hL => by rw [hL0 L hL]; decide
      frame_trail_mono := fun L1 L2 h12 hL2 => by
        rw [hL0 L1 (by omega), hL0 L2 hL2]; exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => absurd rfl (hi0 i hi ▸ hne)
      reason_lit_mem := fun i hi hne => absurd rfl (hi0 i hi ▸ hne) }
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => (hr0 r hr).elim,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by simp only [nvOneLitState, nvOneLitScratch,
      List.getElem?_replicate, show i < 16 by omega, ↓reduceIte, Option.getD_some],
      Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem fid_nv_wp {f : Sym} {as rs : List Ty} {sp : Spec as rs} (idx : Nat)
    (hidx : fidSchedSpecTable[idx]? = some ⟨f, as, rs, sp, true⟩) (pre post : List Fn) (fn : Fn)
    (hsplit : fidSchedFns = pre ++ fn :: post) (hname : fn.name = f) (has : fn.as = as)
    (hrs : fn.rs = rs) (body : Func as rs) (hbody : has ▸ hrs ▸ fn.body = body) :
    ∀ (a : Tup Val as) m Q, sp a m Q (fun _ _ _ _ => False) →
      Func.wp fidSchedEnv body a m Q (fun _ _ _ _ => False) := by
  subst has hrs hname hbody; let ⟨_, _, hwp⟩ := fidSched_moduleOk.fnsOk pre fn post hsplit
  exact fun a m Q hs => hwp a m Q _
    (fidSchedEnv_row idx ⟨fn.name, fn.as, fn.rs, sp, true⟩ hidx a m Q (fun _ _ _ _ => False) hs)

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_ilog10_fid(10) = 1`. -/
theorem nv_fid_ilog10 : Func.wp fidSchedEnv full_ilog10_fid_body (10#64, ()) nvOneLitMem
    (fun (r, ()) m' => r = 1#64 ∧ FullMem nvOneLitCfg nvOneLitState m')
    (fun _ _ _ _ => False) := by
  refine fid_nv_wp 0 rfl [] (fidSchedFns.drop 1) fidSchedFns[0] rfl rfl rfl rfl
    full_ilog10_fid_body rfl (10#64, ()) nvOneLitMem _ fun r _ _ hpow _ => ?_
  have h1 : r.toNat = 1 := hpow.elim id fun h => by
    by_cases heq : r.toNat = 1; · exact heq
    have : 100 ≤ 10 ^ r.toNat :=
      Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ r.toNat))
    exact absurd (Nat.le_trans this (by simpa using h)) (by decide)
  exact ⟨BitVec.eq_of_toNat_eq h1, nvOneLitMem_ok⟩

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_nlogpown_fid(500, 1, 2) = 500`. -/
theorem nv_fid_nlogpown : Func.wp fidSchedEnv full_nlogpown_fid_body (500#64, 1#64, 2#64, ())
    nvOneLitMem (fun (r, ()) m' => r = 500#64 ∧ FullMem nvOneLitCfg nvOneLitState m')
    (fun _ _ _ _ => False) := by
  refine fid_nv_wp 1 rfl (fidSchedFns.take 1) (fidSchedFns.drop 2) fidSchedFns[1]
    rfl rfl rfl rfl full_nlogpown_fid_body rfl (500#64, 1#64, 2#64, ()) nvOneLitMem _ ?_
  rintro r ⟨lg, _, _, hpow, _, hr⟩
  have hlg : lg = 1 := hpow.elim id fun h => by
    by_cases heq : lg = 1; · exact heq
    have hm : min ((1#64 : BitVec 64).toNat + 9) (2 ^ 64 - 1) = 10 := by decide
    have h100 : 100 ≤ 10 ^ lg :=
      Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ lg))
    rw [hm] at h; exact absurd (Nat.le_trans h100 h) (by decide)
  rw [hlg] at hr; exact ⟨BitVec.eq_of_toNat_eq (by simpa using hr), nvOneLitMem_ok⟩

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_calc_max_v_fid`. -/
theorem nv_fid_calc_max_v : Func.wp fidSchedEnv full_calc_max_v_fid_body
    (65536#64, 1#64, 2#64, BitVec.ofNat 64 (fullFixedBytes 1), ()) nvOneLitMem
    (fun (r, ()) m' => 1 ≤ r.toNat ∧ r.toNat < 2 * dimacsBound ∧
      fullFixedBytes r.toNat + 2 * 40 + 136 ≤ 65536 ∧ FullMem nvOneLitCfg nvOneLitState m')
    (fun _ _ _ _ => False) :=
  fid_nv_wp 2 rfl (fidSchedFns.take 2) (fidSchedFns.drop 3) fidSchedFns[2] rfl rfl rfl rfl
    full_calc_max_v_fid_body rfl _ nvOneLitMem _
    ⟨by decide, by decide, by decide, by decide, fun _ h1 h2 h3 => ⟨h1, h2, h3, nvOneLitMem_ok⟩⟩

private theorem nvFid_hdrMem_emp :
    (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
  rw [sep_emp]; exact nvM6HdrMem_ok

theorem nv_fid_reduce : Func.wp fidSchedEnv full_reduce_fid_body (nvOneLitCfg.hdr, false, ())
    nvM6HdrMem (fun (r, ()) m' => ∃ ext' s',
      FullM6HdrInvW nvOneLitCfg nvOneLitF0 [[0], [1]] ext' s' ∧ (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
      (r = 20#64 → nvOneLitF0.Unsat) ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
    (fun _ _ _ _ => False) :=
  fid_nv_wp 3 rfl (fidSchedFns.take 3) (fidSchedFns.drop 4) fidSchedFns[3] rfl rfl rfl rfl
    full_reduce_fid_body rfl _ nvM6HdrMem _ (m6ReduceSpec_of (FullM6HdrInvW.mk_inv nvM6HdrCfg_ok
      nvM6ExtWords_ok nvFid_sparseW) nvFid_hdrMem_emp
      fun r ext' s' m' hi' hr' _ _ _ _ _ _ hu' _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hi', hr', fun h => hu' h, hm'⟩)

theorem nv_fid_probe : Func.wp fidSchedEnv full_probe_fid_body (nvOneLitCfg.hdr, true, ())
    nvM6HdrMem (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
      (r = 20#64 → nvOneLitF0.Unsat) ∧
      (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
      FullM6HdrMem nvOneLitCfg ext' s' m') (fun _ _ _ _ => False) :=
  fid_nv_wp 4 rfl (fidSchedFns.take 4) (fidSchedFns.drop 5) fidSchedFns[4] rfl rfl rfl rfl
    full_probe_fid_body rfl _ nvM6HdrMem _ (fidProbeSpec_of (FullM6HdrInvW.mk_inv nvM6HdrCfg_ok
      nvM6ExtWords_ok nvFid_sparseW).toInv rfl nvFid_hdrMem_emp
      fun r ext' s' m' _ _ _ hr' hu' h1' hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hr', hu', h1', hm'⟩)

theorem nv_fid_eliminate : Func.wp fidSchedEnv full_eliminate_fid_body (nvOneLitCfg.hdr, true, ())
    nvOneLitMem (fun (r, ()) m' => ∃ s', FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
      s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
    (fun _ _ _ _ => False) :=
  fid_nv_wp 5 rfl (fidSchedFns.take 5) (fidSchedFns.drop 6) fidSchedFns[5] rfl rfl rfl rfl
    full_eliminate_fid_body rfl (nvOneLitCfg.hdr, true, ()) nvOneLitMem _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvFid_sparseW.toSparse, rfl,
      by rw [sep_emp]; exact nvOneLitMem_ok, fun r s' m' hsp' hcl' _ hr' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp', hcl', hr', nvFid_unsat, hm'⟩⟩

theorem nv_fid_preprocess : Func.wp fidSchedEnv full_preprocess_fid_body (nvOneLitCfg.hdr, ())
    nvM6HdrMem (fun (r, ()) m' => ∃ c' ext' s', FullM4Compact.FullCfgCompat nvOneLitCfg c' ∧
      s'.LengthsOk c' ∧ FullM6HdrCfgOk c' ∧ M6HdrExtOk ext' ∧
      (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
      (r = 1#64 → FullM6HdrInv c' nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
      FullM6HdrMem c' ext' s' m') (fun _ _ _ _ => False) :=
  fid_nv_wp 6 rfl (fidSchedFns.take 6) (fidSchedFns.drop 7) fidSchedFns[6] rfl rfl rfl rfl
    full_preprocess_fid_body rfl _ nvM6HdrMem _ (fullM6PreprocessSpec_of (FullM6HdrInvW.mk_inv
      nvM6HdrCfg_ok nvM6ExtWords_ok nvFid_sparseW).toInv rfl nvFid_hdrMem_emp
      fun r c' ext' s' m' hcmp' hlen' hcfg' hext' hr' _ hu' h1' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨c', ext', s', hcmp', hlen', hcfg', hext', hr', hu', h1', hm'⟩)

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM7FidelitySched
