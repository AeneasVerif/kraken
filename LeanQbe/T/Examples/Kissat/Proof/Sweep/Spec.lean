/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Sweep.State
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Sweep
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Sweep` (`20` Functions)

Single source of truth for all `20` functions in `Src.Sweep.fns` on flat `CanonicalEnv`:
- `deps` (`Kitten.Spec ++ Clause.Spec ++ Congruence.Spec ++ Watch.Spec ++ Dense.Spec`)
- UNSAT-sound `Spec` definitions (`0` SAT/model proofs, `XFree`, `noExit := true`)
- `specs` table matching `Src.Sweep.fns` `1:1` (`20` rows), `specs_sigs`, `specs_nodup`,
  `specs_noExit`, `specs_xfree`, and `has_*` projections.

Zero legacy `Full*` imports; zero `@[expose]` on theorems, lemmas, or sections.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec

open Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open LeanQbe.T.Examples.Kissat.Proof.Sweep
open LeanQbe.T.Examples.Kissat.Src.Sweep

/-! ## 1. Dependencies & All `20` Canonical `Spec` Contracts -/

/-- Exact upstream segment capability dependencies for `Src.Sweep`. -/
@[expose] def deps : List SpecEntry :=
  Kitten.Spec.specs ++ Clause.Spec.specs ++ Congruence.Spec.specs ++
  Watch.Spec.specs ++ Dense.Spec.specs

/-- `1/20`: `full_m6_sweep_cone` extracts a bounded `K6` cone with `K6HwmClean` + HWM bound. -/
@[expose] def fullM6SweepConeSpec : Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ k6MinScr ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ M6TmkZero s ∧
    (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
        (k6StateOfScratch L s.scratch.scratch_buf)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r tmp' ws1' tmk' scr' gu' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp' }
          scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk',
                                      scratch_buf := scr', glue_used := gu' } }
      let nv := (r &&& 0xFFFF#64).toNat
      let nc := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.vals = s.core.vals →
      s'.core.inconsistent = s.core.inconsistent → M6SweepConeOk F_cur s' nv →
      nc ≤ 3 * k6MaxV c.scratch_cap → r.toNat = nv + nc * 2 ^ 16 →
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr') ∧
        (2 ≤ nv →
          gu'[33]? = some 0xFFFFFFFF#32 ∨ nv ≤ (gu'[33]?.getD 0#32).toNat)) →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nv, (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `2/20`: `full_m6_sweep_refine_sig` updates `sim_sig` bit `bit_idx & 63` from `K6` values. -/
@[expose] def fullM6SweepRefineSigSpec : Spec [i64, i32, i32] [] :=
  fun (h, nv, _bit_idx, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ k6MinScr ≤ c.scratch_cap ∧ nv.toNat ≤ k6MaxV c.scratch_cap ∧
      nv.toNat ≤ 2 * c.max_vars ∧
      (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ sig' m', sig'.length = c.max_vars →
        (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' → Q () m'

/-- `3/20`: `full_m6_sweep_rand_phases` randomizes `K6` phases via isolated `k[25]` PRNG. -/
@[expose] def fullM6SweepRandPhasesSpec : Spec [i64, i32] [] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧
    (k6StateOfScratch L s.scratch.scratch_buf).nv = nv ∧ (FullMem c s ⋆ R) m ∧
    ∀ scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `4/20`: `full_m6_sweep_solve` randomizes phases and invokes `full_k6_solve`. -/
@[expose] def fullM6SweepSolveSpec : Spec [i64, i32, i64] [i64] :=
  fun (h, nv, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧
      (k6StateOfScratch L s.scratch.scratch_buf).nv = nv ∧ (FullMem c s ⋆ R) m ∧
      ∀ r fuel' scr' m',
        let s' : FullState :=
          { s with core := { s.core with fuel := fuel' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
        s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
        (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
        K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = nv → K6TailEq L ks ks' →
        ks'.nassump = ks.nassump →
        k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k6AssumpLitsS L scr')).Sat β) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `5/20`: `full_m6_sweep_flip_round` tries flipping half the cone variables via `k[25]`. -/
@[expose] def fullM6SweepFlipRoundSpec : Spec [i64, i32] [i32] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧
    (k6StateOfScratch L s.scratch.scratch_buf).nv = nv ∧ (FullMem c s ⋆ R) m ∧
    ∀ ret scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- `6/20`: `full_m6_sweep_sim` runs initial solve + flip-based signature simulation rounds. -/
@[expose] def fullM6SweepSimSpec : Spec [i64, i32, i64] [i32] :=
  fun (h, nv, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6SweepConeOk F_cur s nv.toNat ∧
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        let ks := k6StateOfScratch L s.scratch.scratch_buf
        K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32) ks ∧
        (s.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
          ks.nv.toNat ≤ (s.scratch.glue_used[33]?.getD 0#32).toNat)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r fuel' sig' scr' m',
        let s' : FullState :=
          { s with core := { s.core with fuel := fuel' }
                   scratch := { s.scratch with sim_sig := sig', scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → fuel'.toNat ≤ s.core.fuel.toNat →
        M6SweepConeOk F_cur s' nv.toNat →
        (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          let ks' := k6StateOfScratch L scr'
          K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32) ks' ∧
          (s.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
            ks'.nv.toNat ≤ (s.scratch.glue_used[33]?.getD 0#32).toNat)) →
        (r = 0xFFFFFFFF#32 → (cnfOfClauses F_cur).Unsat) →
        (r ≠ 0xFFFFFFFF#32 → r.toNat ≤ 64) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `7/20`: `full_m6_sweep_rearm` marks neighbors of `v` with `FL_SWEEP` preserving `FullDenseInvW`.
-/
@[expose] def fullM6SweepRearmSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' m',
      let s' : FullState := { s with core := { s.core with flags := flags' } }
      flags'.length = c.max_vars → FullDenseInvW c F0 F_cur s' →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `8/20`: `full_m6_sweep_build_pht` hashes cone signatures into `scratch_buf` PHT buckets. -/
@[expose] def fullM6SweepBuildPhtSpec : Spec [i64, i32, i64] [] :=
  fun (h, nv, _smask, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (L : K6Layout) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      nv.toNat ≤ L.maxV ∧ nv.toNat ≤ 2 * c.max_vars ∧
      (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, i < k6PhtHead ∨ L.phtMerged ≤ i →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        M6PhtOk nv.toNat scr' → (FullMem c s' ⋆ R) m' → Q () m'

/-- `9/20`: `full_m6_extract_pht` extracts candidate classes of size `>= 2` from PHT buckets. -/
@[expose] def fullM6ExtractPhtSpec : Spec [i64, i32, i64] [i32] :=
  fun (h, nv, _smask, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (L : K6Layout) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      nv.toNat ≤ L.maxV ∧ nv.toNat ≤ c.max_vars ∧
      (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
      M6PhtOk nv.toNat s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
      ∀ ncls scr' sstk' mclr' m',
        let s' : FullState :=
          { s with core := { s.core with min_clr := mclr' }
                   scratch := { s.scratch with scratch_buf := scr', shrink_stk := sstk' } }
        scr'.length = c.scratch_cap → sstk'.length = c.max_vars → mclr'.length = c.max_vars →
        (∀ i < c.scratch_cap, i < k6PhtHead ∨ L.phtMerged ≤ i →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        ncls.toNat ≤ c.max_vars → M6PartitionOk nv.toNat ncls.toNat scr' sstk' →
        (FullMem c s' ⋆ R) m' → Q (ncls, ()) m'

/-- `10/20`: `full_m6_refine_partition` splits candidate equivalence classes using `K6` values. -/
@[expose] def fullM6RefinePartitionSpec : Spec [i64, i32, i32] [i32] :=
  fun (h, nv, ncls, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (L : K6Layout) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      nv.toNat ≤ L.maxV ∧ nv.toNat ≤ c.max_vars ∧ ncls.toNat ≤ c.max_vars ∧
      (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
      M6PartitionOk nv.toNat ncls.toNat s.scratch.scratch_buf s.scratch.shrink_stk ∧
      (FullMem c s ⋆ R) m ∧
      ∀ new_n scr' sstk' wsort' m',
        let sc' : FullScratch :=
          { s.scratch with scratch_buf := scr', shrink_stk := sstk', wsort := wsort' }
        let s' : FullState := { s with scratch := sc' }
        scr'.length = c.scratch_cap → sstk'.length = c.max_vars →
        wsort'.length = 2 * c.max_vars →
        (∀ i < c.scratch_cap, i < k6PhtNext ∨ L.phtMerged ≤ i →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        new_n.toNat ≤ c.max_vars → M6PartitionOk nv.toNat new_n.toNat scr' sstk' →
        (FullMem c s' ⋆ R) m' → Q (new_n, ()) m'

/-- `11/20`: `full_m6_sweep_units` tests constant-signature cone variables for forced units. -/
@[expose] def fullM6SweepUnitsSpec : Spec [i64, i32, i32, i64] [i64] :=
  fun (h, nv, rbit_in, _tlim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6SweepConeOk F_cur s nv.toNat ∧
      rbit_in.toNat ≤ 64 ∧
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        let ks := k6StateOfScratch L s.scratch.scratch_buf
        K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32) ks ∧
        (s.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
          ks.nv.toNat ≤ (s.scratch.glue_used[33]?.getD 0#32).toNat)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.repr = s.core.repr →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        s'.scratch.glue_used = s.scratch.glue_used →
        M6SweepConeOk F_cur s' nv.toNat →
        (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          let ks' := k6StateOfScratch L s'.scratch.scratch_buf
          K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32) ks' ∧
          (s'.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
            ks'.nv.toNat ≤ (s'.scratch.glue_used[33]?.getD 0#32).toNat)) →
        (r = 0xFFFFFFFFFFFFFFFF#64 → F0.Unsat) →
        (r ≠ 0xFFFFFFFFFFFFFFFF#64 → r.toNat ≤ 64) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `12/20`: `full_m6_sweep_classes` refines signature classes to proven literal equivalences. -/
@[expose] def fullM6SweepClassesSpec : Spec [i64, i32, i32, i64] [i64] :=
  fun (h, nv, rbit_in, _tlim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6SweepConeOk F_cur s nv.toNat ∧
      rbit_in.toNat ≤ 64 ∧
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        let ks := k6StateOfScratch L s.scratch.scratch_buf
        K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32) ks ∧
        (s.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
          ks.nv.toNat ≤ (s.scratch.glue_used[33]?.getD 0#32).toNat)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.repr = s.core.repr →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        s'.scratch.glue_used = s.scratch.glue_used →
        (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
            (k6StateOfScratch L s'.scratch.scratch_buf)) →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 1#64 → ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          M6EqBufOk F_cur s' (k6StateOfScratch L s'.scratch.scratch_buf).neq.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `13/20`: `full_m6_els_ar` rewrites large arena clause `cr` under `FullCongReprInv`. -/
@[expose] def fullM6ElsArSpec : Spec [i64, i32, i32] [.bool] := fun (h, cr, rl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cr.toNat ∈ fullArenaClauseRefs s ∧
    rl.toNat < 2 * s.core.cur_vars ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `14/20`: `full_m6_els_lit` substitutes merged literal `l -> rl` across watch list `l`. -/
@[expose] def fullM6ElsLitSpec : Spec [i64, i32, i32] [.bool] := fun (h, l, rl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ l.toNat < 2 * s.core.cur_vars ∧
    rl.toNat < 2 * s.core.cur_vars ∧ LitEquiv (cnfOfClauses F_cur) l.toNat rl.toNat ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `15/20`: `full_m6_dense_els` incrementally folds `eqb` into `repr` + performs ELS. -/
@[expose] def fullM6DenseElsSpec : Spec [i64, i32] [.bool] := fun (h, neq, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6EqBufOk F_cur s neq.toNat ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `16/20`: `full_m6_sweep_var` sweeps a single root variable preserving `FullCongReprInv`. -/
@[expose] def fullM6SweepVarSpec : Spec [i64, i32, i64] [i64] :=
  fun (h, root_v, _tlim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ k6MinScr ≤ c.scratch_cap ∧
      root_v.toNat < s.core.cur_vars ∧ M6TmkZero s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
          (k6StateOfScratch L s.scratch.scratch_buf)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        (∀ i < 64, i ≠ 33 → s'.scratch.glue_used[i]? = s.scratch.glue_used[i]?) →
        (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
            (k6StateOfScratch L s'.scratch.scratch_buf)) →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `17/20`: `full_m6_cand_sift` max-heap sift-down over candidate indices keyed by `deg`. -/
@[expose] def fullM6CandSiftSpec : Spec [i64, i64, i32, i32] [] :=
  fun (cands_ptr, deg_ptr, start, n, ()) m Q _ =>
    ∃ (cands deg : List (BitVec 32)) (bound : Nat) (R : Mem 64 → Prop),
      start.toNat < n.toNat ∧ n.toNat ≤ cands.length ∧ n.toNat < 2 ^ 31 ∧
      bound ≤ deg.length ∧ (∀ i < n.toNat, (cands[i]?.getD 0#32).toNat < bound) ∧
      (array (t := i32) cands_ptr cands ⋆ array (t := i32) deg_ptr deg ⋆ R) m ∧
      ∀ cands' m',
        cands'.length = cands.length →
        (∀ i < n.toNat, (cands'[i]?.getD 0#32).toNat < bound) →
        (array (t := i32) cands_ptr cands' ⋆ array (t := i32) deg_ptr deg ⋆ R) m' → Q () m'

/-- `18/20`: `full_m6_collect_cands` collects and sorts sweep candidates in `tarjan_reach`. -/
@[expose] def fullM6CollectCandsSpec : Spec [i64] [i32] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ nc trc' ws2' m',
      let s' : FullState :=
        { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } }
      s'.LengthsOk c → nc.toNat ≤ s.core.cur_vars →
      (∀ i < nc.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (nc, ()) m'

/-- `19/20`: `full_m6_sweep_vars` runs budgeted dense variable sweeping with `M6TmkZero`. -/
@[expose] def fullM6SweepVarsSpec : Spec [i64, i64, i64] [i64] :=
  fun (h, _budget, _tlim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInv c F0 s ∧ M6TmkZero s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `20/20`: `full_sweep_dense_m6` top-level dense SAT-sweeping entry point. -/
@[expose] def fullSweepDenseM6Spec : Spec [i64, i64, i64] [i64] :=
  fun (h, _budget, _tlim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 2. `Spec.XFree` Proofs & Canonical `SpecEntry` Table (`20` Rows) -/

theorem fullM6SweepConeSpec_xfree : Spec.XFree fullM6SweepConeSpec := by xfree
theorem fullM6SweepRefineSigSpec_xfree : Spec.XFree fullM6SweepRefineSigSpec := by xfree
theorem fullM6SweepRandPhasesSpec_xfree : Spec.XFree fullM6SweepRandPhasesSpec := by xfree
theorem fullM6SweepSolveSpec_xfree : Spec.XFree fullM6SweepSolveSpec := by xfree
theorem fullM6SweepFlipRoundSpec_xfree : Spec.XFree fullM6SweepFlipRoundSpec := by xfree
theorem fullM6SweepSimSpec_xfree : Spec.XFree fullM6SweepSimSpec := by xfree
theorem fullM6SweepRearmSpec_xfree : Spec.XFree fullM6SweepRearmSpec := by xfree
theorem fullM6SweepBuildPhtSpec_xfree : Spec.XFree fullM6SweepBuildPhtSpec := by xfree
theorem fullM6ExtractPhtSpec_xfree : Spec.XFree fullM6ExtractPhtSpec := by xfree
theorem fullM6RefinePartitionSpec_xfree : Spec.XFree fullM6RefinePartitionSpec := by xfree
theorem fullM6SweepUnitsSpec_xfree : Spec.XFree fullM6SweepUnitsSpec := by xfree
theorem fullM6SweepClassesSpec_xfree : Spec.XFree fullM6SweepClassesSpec := by xfree
theorem fullM6ElsArSpec_xfree : Spec.XFree fullM6ElsArSpec := by xfree
theorem fullM6ElsLitSpec_xfree : Spec.XFree fullM6ElsLitSpec := by xfree
theorem fullM6DenseElsSpec_xfree : Spec.XFree fullM6DenseElsSpec := by xfree
theorem fullM6SweepVarSpec_xfree : Spec.XFree fullM6SweepVarSpec := by xfree
theorem fullM6CandSiftSpec_xfree : Spec.XFree fullM6CandSiftSpec := by xfree
theorem fullM6CollectCandsSpec_xfree : Spec.XFree fullM6CollectCandsSpec := by xfree
theorem fullM6SweepVarsSpec_xfree : Spec.XFree fullM6SweepVarsSpec := by xfree
theorem fullSweepDenseM6Spec_xfree : Spec.XFree fullSweepDenseM6Spec := by xfree

/-- Canonical `SpecEntry` table matching `Src.Sweep.fns` `1:1` (`20` rows). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_m6_sweep_cone", [i64, i32], [i64], fullM6SweepConeSpec, true⟩
  , ⟨"full_m6_sweep_refine_sig", [i64, i32, i32], [], fullM6SweepRefineSigSpec, true⟩
  , ⟨"full_m6_sweep_rand_phases", [i64, i32], [], fullM6SweepRandPhasesSpec, true⟩
  , ⟨"full_m6_sweep_solve", [i64, i32, i64], [i64], fullM6SweepSolveSpec, true⟩
  , ⟨"full_m6_sweep_flip_round", [i64, i32], [i32], fullM6SweepFlipRoundSpec, true⟩
  , ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], fullM6SweepSimSpec, true⟩
  , ⟨"full_m6_sweep_rearm", [i64, i32], [], fullM6SweepRearmSpec, true⟩
  , ⟨"full_m6_sweep_build_pht", [i64, i32, i64], [], fullM6SweepBuildPhtSpec, true⟩
  , ⟨"full_m6_extract_pht", [i64, i32, i64], [i32], fullM6ExtractPhtSpec, true⟩
  , ⟨"full_m6_refine_partition", [i64, i32, i32], [i32], fullM6RefinePartitionSpec, true⟩
  , ⟨"full_m6_sweep_units", [i64, i32, i32, i64], [i64], fullM6SweepUnitsSpec, true⟩
  , ⟨"full_m6_sweep_classes", [i64, i32, i32, i64], [i64], fullM6SweepClassesSpec, true⟩
  , ⟨"full_m6_els_ar", [i64, i32, i32], [.bool], fullM6ElsArSpec, true⟩
  , ⟨"full_m6_els_lit", [i64, i32, i32], [.bool], fullM6ElsLitSpec, true⟩
  , ⟨"full_m6_dense_els", [i64, i32], [.bool], fullM6DenseElsSpec, true⟩
  , ⟨"full_m6_sweep_var", [i64, i32, i64], [i64], fullM6SweepVarSpec, true⟩
  , ⟨"full_m6_cand_sift", [i64, i64, i32, i32], [], fullM6CandSiftSpec, true⟩
  , ⟨"full_m6_collect_cands", [i64], [i32], fullM6CollectCandsSpec, true⟩
  , ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], fullM6SweepVarsSpec, true⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], fullSweepDenseM6Spec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Src.Sweep.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullM6SweepConeSpec_xfree
  · exact fullM6SweepRefineSigSpec_xfree
  · exact fullM6SweepRandPhasesSpec_xfree
  · exact fullM6SweepSolveSpec_xfree
  · exact fullM6SweepFlipRoundSpec_xfree
  · exact fullM6SweepSimSpec_xfree
  · exact fullM6SweepRearmSpec_xfree
  · exact fullM6SweepBuildPhtSpec_xfree
  · exact fullM6ExtractPhtSpec_xfree
  · exact fullM6RefinePartitionSpec_xfree
  · exact fullM6SweepUnitsSpec_xfree
  · exact fullM6SweepClassesSpec_xfree
  · exact fullM6ElsArSpec_xfree
  · exact fullM6ElsLitSpec_xfree
  · exact fullM6DenseElsSpec_xfree
  · exact fullM6SweepVarSpec_xfree
  · exact fullM6CandSiftSpec_xfree
  · exact fullM6CollectCandsSpec_xfree
  · exact fullM6SweepVarsSpec_xfree
  · exact fullSweepDenseM6Spec_xfree

/-! ## 3. `Env.Sat.has` Projections (`20` fns) -/

theorem has_full_m6_sweep_cone {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_cone" fullM6SweepConeSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide))
    fullM6SweepConeSpec_xfree

theorem has_full_m6_sweep_refine_sig {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_refine_sig" fullM6SweepRefineSigSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide))
    fullM6SweepRefineSigSpec_xfree

theorem has_full_m6_sweep_rand_phases {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_rand_phases" fullM6SweepRandPhasesSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide))
    fullM6SweepRandPhasesSpec_xfree

theorem has_full_m6_sweep_solve {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_solve" fullM6SweepSolveSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide))
    fullM6SweepSolveSpec_xfree

theorem has_full_m6_sweep_flip_round {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_flip_round" fullM6SweepFlipRoundSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide))
    fullM6SweepFlipRoundSpec_xfree

theorem has_full_m6_sweep_sim {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_sim" fullM6SweepSimSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide))
    fullM6SweepSimSpec_xfree

theorem has_full_m6_sweep_rearm {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_rearm" fullM6SweepRearmSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 6) (by decide))
    fullM6SweepRearmSpec_xfree

theorem has_full_m6_sweep_build_pht {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_build_pht" fullM6SweepBuildPhtSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 7) (by decide))
    fullM6SweepBuildPhtSpec_xfree

theorem has_full_m6_extract_pht {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_extract_pht" fullM6ExtractPhtSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 8) (by decide))
    fullM6ExtractPhtSpec_xfree

theorem has_full_m6_refine_partition {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_refine_partition" fullM6RefinePartitionSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 9) (by decide))
    fullM6RefinePartitionSpec_xfree

theorem has_full_m6_sweep_units {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_units" fullM6SweepUnitsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 10) (by decide))
    fullM6SweepUnitsSpec_xfree

theorem has_full_m6_sweep_classes {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_classes" fullM6SweepClassesSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 11) (by decide))
    fullM6SweepClassesSpec_xfree

theorem has_full_m6_els_ar {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_els_ar" fullM6ElsArSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 12) (by decide))
    fullM6ElsArSpec_xfree

theorem has_full_m6_els_lit {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_els_lit" fullM6ElsLitSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 13) (by decide))
    fullM6ElsLitSpec_xfree

theorem has_full_m6_dense_els {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_dense_els" fullM6DenseElsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 14) (by decide))
    fullM6DenseElsSpec_xfree

theorem has_full_m6_sweep_var {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_var" fullM6SweepVarSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 15) (by decide))
    fullM6SweepVarSpec_xfree

theorem has_full_m6_cand_sift {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_cand_sift" fullM6CandSiftSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 16) (by decide))
    fullM6CandSiftSpec_xfree

theorem has_full_m6_collect_cands {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_collect_cands" fullM6CollectCandsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 17) (by decide))
    fullM6CollectCandsSpec_xfree

theorem has_full_m6_sweep_vars {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_sweep_vars" fullM6SweepVarsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 18) (by decide))
    fullM6SweepVarsSpec_xfree

theorem has_full_sweep_dense_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_sweep_dense_m6" fullSweepDenseM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 19) (by decide))
    fullSweepDenseM6Spec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
