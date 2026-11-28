/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.State
public import LeanQbe.T.Examples.Kissat.Src.Kitten
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Step-13 `Spec` Table for `Kissat/Src/Kitten.lean` (`14` fns)

Single canonical `Spec` per function of `Src.Kitten.fns` (`14` C0 functions, `0` externs):
`m6MaxVSpec`, `k6AddTicksSpec`, `step13K6InitSpec`, `k6WatchSpec`, `k6AssignSpec`,
`step13K6AddClauseSpec`, `k6MtfSpec`, `step13K6BacktrackSpec`, `step13K6PropagateSpec`,
`step13K6AnaClauseSpec`, `step13K6AnalyzeSpec`, `step13K6SolveSpec`, `step13K6FlipSpec`, and
`step13K6AddLiveSpec`.

Includes `Spec.XFree` proofs, `specs` table matching `Src.Kitten.fns` 1:1 (`noExit := true`),
`specs_sigs`, `specs_nodup`, and `Env.Has` projections.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open LeanQbe.T.Examples.Kissat.Src.Kitten

/-! ## 1. All `14` Canonical Step-13 `Spec` Contracts -/

@[expose] def m6MaxVSpec : Spec [i64] [i64] := fun (cap, ()) m Q _ =>
  Q (BitVec.ofNat 64 (k6MaxV cap.toNat), ()) m

@[expose] def k6AddTicksSpec : Spec [i64, i64] [] := fun (kPtr, _delta, ()) m Q _ =>
  ∃ (L : K6Layout) (ks : K6State) (R : Mem 64 → Prop),
    ks.ShapesOk L ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ tk' m', (K6Mem L kPtr (ks.putHdr .ticks tk') ⋆ R) m' → Q () m'

/-- Step-13 `full_k6_init` contract (`glue_used[33]` HWM tracking + `K6HwmClean`). -/
@[expose] def step13K6InitSpec : Spec [i64, i32] [] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    (c.scratch_cap < k6MinScr ∨ k6MaxV c.scratch_cap < nv.toNat → Q () m) ∧
    (k6MinScr ≤ c.scratch_cap → nv.toNat ≤ k6MaxV c.scratch_cap →
      ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
          (k6StateOfScratch L s.scratch.scratch_buf) ∧
        ∀ (scr' gu' : List (BitVec 32)) (m' : Mem 64),
          let ks' := k6StateOfScratch L scr'
          let s' : FullState :=
            { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }
          s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
          (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
          (nv.toNat = L.maxV → gu'[33]? = some 0#32) →
          (nv.toNat < L.maxV →
            gu'[33]? = some 0xFFFFFFFF#32 ∨ nv.toNat ≤ (gu'[33]?.getD 0#32).toNat) →
          K6HwmClean L (gu'[33]?.getD 0#32) ks' →
          (∀ P, K6Inv L P ks') → K6TrailSynced ks' →
          ks'.nv = nv → ks'.nc = 0#32 → ks'.lvl = 0#32 → ks'.prop = 0#32 →
          ks'.trl_end = 0#32 → ks'.unass = nv → ks'.incons = 0#32 → ks'.nassump = 0#32 →
          ks'.status = 0#32 → ks'.openCnt = 0#32 → ks'.neq = 0#32 →
          (FullMem c s' ⋆ R) m' → Q () m')

@[expose] def k6WatchSpec : Spec [i64, i32, i32, i32] [] := fun (kPtr, cid, l0, l1, ()) m Q _ =>
  ∃ (L : K6Layout) (ks : K6State) (R : Mem 64 → Prop),
    ks.ShapesOk L ∧ ks.max_v = L.mv32 ∧ cid.toNat < L.maxCl ∧
    l0.toNat < 2 * L.maxV ∧ l1.toNat < 2 * L.maxV ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ m', (K6Mem L kPtr (k6WatchStep ks cid l0 l1) ⋆ R) m' → Q () m'

@[expose] def k6AssignSpec : Spec [i64, i32, i32] [] := fun (kPtr, lit, rsn, ()) m Q _ =>
  ∃ (L : K6Layout) (ks : K6State) (R : Mem 64 → Prop),
    ks.ShapesOk L ∧ ks.max_v = L.mv32 ∧ lit.toNat < 2 * L.maxV ∧
    ks.trl_end.toNat < L.maxV ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ m', (K6Mem L kPtr (k6AssignStep ks lit rsn) ⋆ R) m' → Q () m'

/-- Step-13 `full_k6_add_clause` contract (`glue_used[33]` HWM update + `K6HwmClean`). -/
@[expose] def step13K6AddClauseSpec : Spec [i64, i64, i32] [.bool] :=
  fun (h, lits_ptr, sz, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
      (scr gu xs : List (BitVec 32)) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ s.scratch.scratch_buf = scr ∧ s.scratch.glue_used = gu ∧
      L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      K6Inv L P (k6StateOfScratch L scr) ∧ K6TrailSynced (k6StateOfScratch L scr) ∧
      (k6StateOfScratch L scr).lvl = 0#32 ∧ sz.toNat ≤ xs.length ∧ sz.toNat < 2 ^ 28 ∧
      (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * (k6StateOfScratch L scr).nv.toNat) ∧
      SemEntails P ((xs.take sz.toNat).map BitVec.toNat) ∧
      K6HwmClean L (gu[33]?.getD 0#32) (k6StateOfScratch L scr) ∧
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ array (t := i32) c.pScratchBuf scr ⋆
        array (t := i32) c.pGlueUsed gu ⋆ array (t := i32) lits_ptr xs ⋆ R) m ∧
      ∀ (ok : Bool) (scr' gu' : List (BitVec 32)) (m' : Mem 64),
        let ks := k6StateOfScratch L scr; let ks' := k6StateOfScratch L scr'
        let s' : FullState :=
          { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }
        s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = scr[i]?) →
        (∀ i < 64, i ≠ 33 → gu'[i]? = gu[i]?) →
        K6HwmClean L (gu'[33]?.getD 0#32) ks' →
        K6Inv L P ks' → K6TrailSynced ks' → ks'.lvl = 0#32 → ks'.nv = ks.nv →
        ks'.nassump = ks.nassump → k6AssumpLitsS L scr' = k6AssumpLitsS L scr →
        (ok = false → ks' = ks) →
        (2 ≤ sz.toNat → ks'.trl_end = ks.trl_end ∧ ks'.prop = ks.prop ∧
          ks'.unass = ks.unass ∧ ks'.incons = ks.incons) →
        (∀ M, (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * M) →
          K6LitsBounded M ks → (∀ l ∈ k6TrailLits ks, l < 2 * M) →
          K6LitsBounded M ks' ∧ (∀ l ∈ k6TrailLits ks', l < 2 * M)) →
        (array64 (c.hdr + 32) (hdrTailWords c s') ⋆ array (t := i32) c.pScratchBuf scr' ⋆
          array (t := i32) c.pGlueUsed gu' ⋆ array (t := i32) lits_ptr xs ⋆ R) m' →
        Q (ok, ()) m'

@[expose] def k6MtfSpec : Spec [i64, i32] [] := fun (kPtr, _v, ()) m Q _ =>
  ∃ (L : K6Layout) (ks : K6State) (R : Mem 64 → Prop),
    ks.ShapesOk L ∧ ks.max_v = L.mv32 ∧ ks.nv.toNat ≤ L.maxV ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ qf' ql' qs' qst' qp' qn' qsa' m',
      let ks' : K6State := { ks with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                                     qprev := qp', qnext := qn', qstampArr := qsa' }
      ks'.ShapesOk L → (K6Mem L kPtr ks' ⋆ R) m' → Q () m'

/-- `K6TailEq`-preserving `full_k6_backtrack` contract. -/
@[expose] def step13K6BacktrackSpec : Spec [i64, i32] [] := fun (kPtr, target_lvl, ()) m Q _ =>
  ∃ (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (R : Mem 64 → Prop),
    K6Inv L P ks ∧ (target_lvl = 0#32 ∨ K6TrailSynced ks) ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → ks'.lvl = target_lvl →
      ks'.trl_end.toNat ≤ ks.trl_end.toNat → K6BtPreserved ks ks' → K6TailEq L ks ks' →
      (∀ i < ks'.trl_end.toNat,
        ks'.trl[i]? = ks.trl[i]? ∧ ks'.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]? =
          ks.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]? ∧
        (ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) →
      (∀ i < ks.trl_end.toNat,
        (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
        i < ks'.trl_end.toNat) →
      (K6Mem L kPtr ks' ⋆ R) m' → Q () m'

/-- `K6TailEq`-preserving `full_k6_propagate` contract. -/
@[expose] def step13K6PropagateSpec : Spec [i64] [i32] := fun (kPtr, ()) m Q _ =>
  ∃ (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (R : Mem 64 → Prop),
    K6Inv L P ks ∧ K6TrailSynced ks ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ (confl : BitVec 32) (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → K6PropPreserved ks ks' → K6TailEq L ks ks' →
      ks.trl_end.toNat ≤ ks'.trl_end.toNat →
      (∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? ∧
        ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
          ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? ∧
        ks'.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]? =
          ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?) →
      (∀ i, ks.trl_end.toNat ≤ i → i < ks'.trl_end.toNat →
        ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧
        ks'.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32) →
      (confl = 0xFFFFFFFF#32 → ks'.prop = ks'.trl_end) →
      (confl ≠ 0xFFFFFFFF#32 →
        confl.toNat < ks'.nc.toNat ∧ ∀ l ∈ k6ClauseLits ks' confl.toNat, ks'.vals[l]? = some 2#32) →
      (K6Mem L kPtr ks' ⋆ R) m' → Q (confl, ()) m'

/-- `K6TailEq`-preserving `full_k6_ana_clause` contract. -/
@[expose] def step13K6AnaClauseSpec : Spec [i64, i32, i32] [] :=
  fun (kPtr, cid, skip_v, ()) m Q _ =>
    ∃ (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (idx : Nat) (R : Mem 64 → Prop),
      K6AnaInv L P ks idx ∧ cid.toNat < ks.nc.toNat ∧
      (∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl) ∧
      (∀ l ∈ k6ClauseLits ks cid.toNat, l / 2 ≠ skip_v.toNat →
        ks.vals[l]? = some 2#32 ∧
        (ks.lvlArr[l / 2]?.getD 0#32 = ks.lvl →
          ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1)) ∧
      (skip_v ≠ 0xFFFFFFFF#32 →
        ∃ l ∈ k6ClauseLits ks cid.toNat, l / 2 = skip_v.toNat ∧
          (∀ l' ∈ k6ClauseLits ks cid.toNat, l' / 2 = skip_v.toNat → l' = l) ∧
          (ks.flags[skip_v.toNat]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
          ks.lvlArr[skip_v.toNat]?.getD 0#32 = ks.lvl ∧
          SemEntails P ((l ^^^ 1) :: k6ResolventLits ks idx)) ∧
      (K6Mem L kPtr ks ⋆ R) m ∧
      ∀ (ks' : K6State) (m' : Mem 64),
        K6AnaInv L P ks' idx → K6AnaPreserved ks ks' → K6TailEq L ks ks' →
        SemEntails P (k6ResolventLits ks' idx) →
        (∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
          (ks'.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) →
        (K6Mem L kPtr ks' ⋆ R) m' → Q () m'

/-- `K6TailEq`-preserving `full_k6_analyze` contract. -/
@[expose] def step13K6AnalyzeSpec : Spec [i64, i32] [.bool] := fun (kPtr, confl_cid, ()) m Q _ =>
  ∃ (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (R : Mem 64 → Prop),
    K6Inv L P ks ∧ K6TrailSynced ks ∧ 0 < ks.lvl.toNat ∧
    (∃ i < ks.trl_end.toNat,
      ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl) ∧
    confl_cid.toNat < ks.nc.toNat ∧
    (∀ l ∈ k6ClauseLits ks confl_cid.toNat, ks.vals[l]? = some 2#32) ∧
    (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ (ok : Bool) (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → K6TailEq L ks ks' →
      ks'.nassump = ks.nassump → ks'.assump = ks.assump → ks'.incons = ks.incons →
      ks'.status = ks.status → ks'.neq = ks.neq →
      (ok = true →
        ks'.lvl.toNat < ks.lvl.toNat ∧
        (0 < ks'.lvl.toNat → ∃ i < ks'.trl_end.toNat,
          ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks'.lvl) ∧
        (∀ d ∈ k6TrailDecisions ks', ∃ i < ks.trl_end.toNat,
          (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k6TrailDecisions ks ∧
          (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat) ∧
        (∀ i < ks.trl_end.toNat,
          (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat →
          i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
          ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
            ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?)) →
      (K6Mem L kPtr ks' ⋆ R) m' → Q (ok, ()) m'

/-- `K6TailEq`-preserving `full_k6_solve` contract. -/
@[expose] def step13K6SolveSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with core := { s.core with fuel := fuel' }
                                     scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → K6TailEq L ks ks' →
      ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k6AssumpLitsS L scr')).Sat β) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `K6TailEq`-preserving `full_k6_flip` contract. -/
@[expose] def step13K6FlipSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧
    lit.toNat < 2 * (k6StateOfScratch L s.scratch.scratch_buf).nv.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = ks.nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `K6TailEq`-preserving `full_k512_add_live_m6` contract. -/
@[expose] def step13K6AddLiveSpec : Spec [i64, i32, i32] [] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    let ks0 := k6StateOfScratch L s.scratch.scratch_buf
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P ks0 ∧ a.toNat < 2 * ks0.nv.toNat ∧
    (b = 0xFFFFFFFF#32 → SemEntails P [a.toNat]) ∧
    (b ≠ 0xFFFFFFFF#32 → b.toNat < 2 * ks0.nv.toNat ∧ SemEntails P [a.toNat, b.toNat]) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks0.nv → K6TailEq L ks0 ks' →
      ks'.nassump = ks0.nassump → k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf →
      ks'.neq = ks0.neq → (FullMem c s' ⋆ R) m' → Q () m'

/-! ## 2. Canonical `SpecEntry` Table, `Spec.XFree`, Signatures, & `Env.Has` Projections -/

/-- Canonical `14`-row specification table aligned 1:1 with `Src.Kitten.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_m6_max_v",        [i64],                [i64],   m6MaxVSpec,             true⟩
  , ⟨"full_k6_add_ticks",    [i64, i64],           [],      k6AddTicksSpec,         true⟩
  , ⟨"full_k6_init",         [i64, i32],           [],      step13K6InitSpec,       true⟩
  , ⟨"full_k6_watch",        [i64, i32, i32, i32], [],      k6WatchSpec,            true⟩
  , ⟨"full_k6_assign",       [i64, i32, i32],      [],      k6AssignSpec,           true⟩
  , ⟨"full_k6_add_clause",   [i64, i64, i32],      [.bool], step13K6AddClauseSpec,  true⟩
  , ⟨"full_k6_mtf",          [i64, i32],           [],      k6MtfSpec,              true⟩
  , ⟨"full_k6_backtrack",    [i64, i32],           [],      step13K6BacktrackSpec,  true⟩
  , ⟨"full_k6_propagate",    [i64],                [i32],   step13K6PropagateSpec,  true⟩
  , ⟨"full_k6_ana_clause",   [i64, i32, i32],      [],      step13K6AnaClauseSpec,  true⟩
  , ⟨"full_k6_analyze",      [i64, i32],           [.bool], step13K6AnalyzeSpec,    true⟩
  , ⟨"full_k6_solve",        [i64, i64],           [i64],   step13K6SolveSpec,      true⟩
  , ⟨"full_k6_flip",         [i64, i32],           [.bool], step13K6FlipSpec,       true⟩
  , ⟨"full_k512_add_live_m6", [i64, i32, i32],     [],      step13K6AddLiveSpec,    true⟩
  ]

theorem m6MaxVSpec_xfree : Spec.XFree m6MaxVSpec := by xfree
theorem k6AddTicksSpec_xfree : Spec.XFree k6AddTicksSpec := by xfree
theorem step13K6InitSpec_xfree : Spec.XFree step13K6InitSpec := by xfree
theorem k6WatchSpec_xfree : Spec.XFree k6WatchSpec := by xfree
theorem k6AssignSpec_xfree : Spec.XFree k6AssignSpec := by xfree
theorem step13K6AddClauseSpec_xfree : Spec.XFree step13K6AddClauseSpec := by xfree
theorem k6MtfSpec_xfree : Spec.XFree k6MtfSpec := by xfree
theorem step13K6BacktrackSpec_xfree : Spec.XFree step13K6BacktrackSpec := by xfree
theorem step13K6PropagateSpec_xfree : Spec.XFree step13K6PropagateSpec := by xfree
theorem step13K6AnaClauseSpec_xfree : Spec.XFree step13K6AnaClauseSpec := by xfree
theorem step13K6AnalyzeSpec_xfree : Spec.XFree step13K6AnalyzeSpec := by xfree
theorem step13K6SolveSpec_xfree : Spec.XFree step13K6SolveSpec := by xfree
theorem step13K6FlipSpec_xfree : Spec.XFree step13K6FlipSpec := by xfree
theorem step13K6AddLiveSpec_xfree : Spec.XFree step13K6AddLiveSpec := by xfree

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6MaxVSpec_xfree
  · exact k6AddTicksSpec_xfree
  · exact step13K6InitSpec_xfree
  · exact k6WatchSpec_xfree
  · exact k6AssignSpec_xfree
  · exact step13K6AddClauseSpec_xfree
  · exact k6MtfSpec_xfree
  · exact step13K6BacktrackSpec_xfree
  · exact step13K6PropagateSpec_xfree
  · exact step13K6AnaClauseSpec_xfree
  · exact step13K6AnalyzeSpec_xfree
  · exact step13K6SolveSpec_xfree
  · exact step13K6FlipSpec_xfree
  · exact step13K6AddLiveSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Kitten.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

def deps : List SpecEntry := []

/-! ## 3. `Env.Sat specs` Projections -/

private theorem mem_has {Γ : Env} (h : Γ.Sat specs) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ specs)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem has_full_m6_max_v {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_max_v" m6MaxVSpec :=
  mem_has h (by simp [specs]) m6MaxVSpec_xfree

theorem has_full_k6_add_ticks {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_add_ticks" k6AddTicksSpec :=
  mem_has h (by simp [specs]) k6AddTicksSpec_xfree

theorem has_full_k6_init {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_init" step13K6InitSpec :=
  mem_has h (by simp [specs]) step13K6InitSpec_xfree

theorem has_full_k6_watch {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_watch" k6WatchSpec :=
  mem_has h (by simp [specs]) k6WatchSpec_xfree

theorem has_full_k6_assign {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_assign" k6AssignSpec :=
  mem_has h (by simp [specs]) k6AssignSpec_xfree

theorem has_full_k6_add_clause {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_add_clause" step13K6AddClauseSpec :=
  mem_has h (by simp [specs]) step13K6AddClauseSpec_xfree

theorem has_full_k6_mtf {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_mtf" k6MtfSpec :=
  mem_has h (by simp [specs]) k6MtfSpec_xfree

theorem has_full_k6_backtrack {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_backtrack" step13K6BacktrackSpec :=
  mem_has h (by simp [specs]) step13K6BacktrackSpec_xfree

theorem has_full_k6_propagate {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_propagate" step13K6PropagateSpec :=
  mem_has h (by simp [specs]) step13K6PropagateSpec_xfree

theorem has_full_k6_ana_clause {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_ana_clause" step13K6AnaClauseSpec :=
  mem_has h (by simp [specs]) step13K6AnaClauseSpec_xfree

theorem has_full_k6_analyze {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_analyze" step13K6AnalyzeSpec :=
  mem_has h (by simp [specs]) step13K6AnalyzeSpec_xfree

theorem has_full_k6_solve {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_solve" step13K6SolveSpec :=
  mem_has h (by simp [specs]) step13K6SolveSpec_xfree

theorem has_full_k6_flip {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k6_flip" step13K6FlipSpec :=
  mem_has h (by simp [specs]) step13K6FlipSpec_xfree

theorem has_full_k512_add_live_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_k512_add_live_m6" step13K6AddLiveSpec :=
  mem_has h (by simp [specs]) step13K6AddLiveSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec

end
