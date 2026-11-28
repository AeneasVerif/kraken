/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Vivify
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical `Spec` Table for `Kissat/Src/Vivify.lean` (`28` fns)

Canonical UNSAT-sound `Spec` contracts (`0` SAT model proofs, `0` legacy `Full*` imports,
`0` `@[expose]` on theorems/lemmas/sections, `XPost`-polymorphic) for all `28` functions
in `Src.Vivify.fns`, upstream `deps`, `Spec.XFree` certificates, `specs_sigs`,
`specs_nodup`, `specs_noExit`, and `Env.Has` projections.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
open LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
open LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
open LeanQbe.T.Examples.Kissat.Src.Vivify
open Kraken.Bedrock2.Test

public section

/-! ## 1. Auxiliary Predicates -/

/-- No active trail literal currently uses large arena clause `cref` as its reason. -/
@[expose] def NonActiveReason (k : FullCoreState) (cref : Nat) : Prop :=
  ∀ idx < k.trail_end,
    let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref

/-- Valid conflict witness on entry to `full_viv_deduce_m6` when `implied = 0xFFFFFFFF#32`
and `confl_type ≠ 0#64` (`1`: binary conflict; `2`: live arena clause `confl_ref`). -/
@[expose] def FullVivConflictOk (F_cur : List (List Nat)) (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]) ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
  (s.core.confl_type = 2#64 ∧
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
      s.core.vals[l]?.getD 0#8 = 0xFF#8)

/-- Subsumption witness stored in `h->ant_sz` by `full_viv_deduce_m6`: none (`-1`), binary
(`-2`), or an arena clause ref in `fullArenaClauseRefs s`. -/
@[expose] def M6SubRefOk (s : FullState) (sub_ref : BitVec 64) : Prop :=
  sub_ref = 0xFFFFFFFFFFFFFFFF#64 ∨ sub_ref = 0xFFFFFFFFFFFFFFFE#64 ∨
  sub_ref.toNat ∈ fullArenaClauseRefs s

/-- Sparse-mode invariant omitting `FullLitMarksClear`, used by `full_viv_recompute_promote_fid`
while `lit_mark` is populated inside `full_viv_deduce_m6`. -/
@[expose] def S13SparseInvNoMark (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Semantic subsuming-clause witness returned by `full_viv_deduce_m6` when `ant_sz ≠ -1`: an
entailed clause whose literals all lie in `tmp[0 ..< sz)` (not non-reason true) or are
falsified at level `0`, enabling `full_viv_inst_m6` to resolve out `tmp[sz - 1]`. -/
@[expose] def VivDeduceSubWitness (F_cur : List (List Nat)) (s : FullState) (sz : Nat) : Prop :=
  ∃ sub : List Nat, (cnfOfClauses F_cur).EntailsClause (cnfClause sub) ∧
    ∀ l ∈ sub, l < 2 * s.core.cur_vars ∧
      (((∃ k < sz, (s.core.tmp[k]?.getD 0#32).toNat = l) ∧
        (s.core.vals[l]?.getD 0#8 ≠ 1#8 ∨
          s.core.rsns[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)) ∨
       (s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0))

/-! ## 2. Canonical Specifications (`28` Functions, 1:1 with `Src.Vivify.fns`) -/

/-- `full_viv_unreason_m6(h, cref)`: backtracks to level `0` if `cref` is an active trail
reason, guaranteeing `NonActiveReason s'.core cref.toNat`. -/
@[expose] def fullVivUnreasonM6Spec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInvW c F0 F_cur s' → NonActiveReason s'.core cref.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.probing = s.core.probing →
      s'.core.fuel = s.core.fuel → s'.core.tmp = s.core.tmp →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.core.cur_level ≤ s.core.cur_level → (s.core.cur_level = 0 → s' = s) →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_watch_rank_m6(h, lit)`: read-only 2WL watch-selection priority key. -/
@[expose] def fullVivWatchRankM6Spec : Spec [i64, i32] [i64] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ lit.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64, Q (r, ()) m

/-- `full_viv_best_watch_m6(h, olen)`: permutes `work_stk2[0 ..< olen)` to move the two
highest-rank watch literals into slots `0, 1`. -/
@[expose] def fullVivBestWatchM6Spec : Spec [i64, i32] [] := fun (h, olen, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ olen.toNat ≤ c.max_vars ∧
    (∀ i < olen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ws2' m',
      ws2'.length = 2 * c.max_vars →
      (ws2'.take olen.toNat).Perm (s.scratch.work_stk2.take olen.toNat) →
      (FullMem c { s with scratch := { s.scratch with work_stk2 := ws2' } } ⋆ R) m' →
      Q () m'

/-- `full_viv_simplify_m6(h, cref)`: level-0 simplification (satisfied drop, unit, binary,
or in-place arena shrink with glue lowering). Returns `0`, `1`, `2` (OOM), or `20` (UNSAT). -/
@[expose] def fullVivSimplifyM6Spec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 →
        cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_commit_m6(h, cref, olen, implied)`: prefix-preserving commit of
`work_stk2[0 ..< olen)` entailed by `F_cur` at any `cur_level` (with `FL_*` flags on irred),
preserving `fullArenaClauseRefs`, `red_refs`, and `tarjan_reach`. -/
@[expose] def fullVivCommitM6Spec : Spec [i64, i32, i32, i32] [i64] :=
  fun (h, cref, olen, _implied, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      olen.toNat ≤ c.max_vars ∧
      (olen.toNat < fullArenaClauseSize s cref.toNat →
        (∀ i < olen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((s.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullSparseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
        s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.red_refs = s.scratch.red_refs →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_mark_garb_m6(h, cref)`: unreasons, unwatches, marks `PH_GARB`, and marks `FL_*`
flags on irred literals while preserving `FullSparseInvW`, `fullArenaClauseRefs`, `red_refs`,
and `tarjan_reach`. -/
@[expose] def fullVivMarkGarbM6Spec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.probing = s.core.probing →
      s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.core.cur_level ≤ s.core.cur_level →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_subsumes_bin_m6(h, a, b)`: read-only binary subsumption check against
`lit_mark` and level-0 falsified literals. -/
@[expose] def fullVivSubsumesBinM6Spec : Spec [i64, i32, i32] [.bool] :=
  fun (h, a, b, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
      ∀ ok : Bool,
        (ok = true →
          (s.core.lit_mark[a.toNat]?.getD 0#8 ≠ 0#8 ∨
            (s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∧
              (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat = 0)) ∧
          (s.core.lit_mark[b.toNat]?.getD 0#8 ≠ 0#8 ∨
            (s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 ∧
              (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat = 0))) →
        Q (ok, ()) m

/-- `full_viv_subsumes_cl_m6(h, rcr, sz)`: read-only arena clause subsumption test against
`lit_mark` and level-0 falsified literals. -/
@[expose] def fullVivSubsumesClM6Spec : Spec [i64, i32, i32] [.bool] :=
  fun (h, rcr, _sz, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      rcr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s rcr.toNat = false ∧
      (FullMem c s ⋆ R) m ∧
      ∀ ok : Bool,
        (ok = true → ∀ l ∈ fullArenaClauseLits s rcr.toNat,
          l < 2 * s.core.cur_vars ∧
          (s.core.lit_mark[l]?.getD 0#8 ≠ 0#8 ∨
            (s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
              (s.core.lvl[l / 2]?.getD 0#32).toNat = 0))) →
        Q (ok, ()) m

/-- `full_viv_recompute_promote_fid(h, cref)`: recomputes glue for a non-garbage arena clause
and lowers it in place if `0 < ng < glue`, restoring `frame_trail` and preserving
`S13SparseInvNoMark`, `fullArenaClauseRefs`, and all clause garb/size/literal lists. -/
@[expose] def vivRecomputePromoteSpec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ S13SparseInvNoMark c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ (FullMem c s ⋆ R) m ∧
    ∀ ar' mclr' m',
      let s' : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
      S13SparseInvNoMark c F0 F_cur s' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s,
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_deduce_m6(h, cref, sz, implied)`: backward unit/reason BFS with binary/large
subsumption (`M6SubRefOk` in `ant_sz`), glue promotion, `mrk`/`lit_mark` restoration, and
entailed `work_stk2[0 ..< olen)` (`ant_sz = -1`) or subsuming witness (`ant_sz ≠ -1`). -/
@[expose] def vivDeduceM6Spec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, cref, sz, implied, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s cref.toNat = false ∧ sz.toNat ≤ c.max_vars ∧
      (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (implied = 0xFFFFFFFF#32 →
        FullVivConflictOk F_cur s ∨
        s.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ olen ar' mclr' mrk' lm' ws1' ws2' asz' rsz' m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with arena := ar', min_clr := mclr', mrk := mrk', lit_mark := lm' }
            scratch :=
              { s.scratch with
                work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } }
        FullSparseInvW c F0 F_cur s' → M6SubRefOk s' asz' →
        (asz' ≠ 0xFFFFFFFFFFFFFFFF#64 → asz' ≠ 0xFFFFFFFFFFFFFFFE#64 →
          asz'.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' asz'.toNat = false) →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s,
          fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
          fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
          fullArenaClauseLits s' r = fullArenaClauseLits s r) →
        (asz' = 0xFFFFFFFFFFFFFFFF#64 → olen ≠ 0xFFFFFFFF#32 →
          olen.toNat ≤ s.core.cur_vars ∧
          (∀ k < olen.toNat, (ws2'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
        (asz' ≠ 0xFFFFFFFFFFFFFFFF#64 → olen ≠ 0xFFFFFFFF#32 →
          olen.toNat ≤ s.core.cur_vars ∧
          (∀ k < olen.toNat, (ws2'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          VivDeduceSubWitness F_cur s sz.toNat) →
        (FullMem c s' ⋆ R) m' → Q (olen, ()) m'

/-- `full_viv_best_implied_m6(h, sz)`: read-only scan selecting the earliest-assigned
(`min trail_pos`) satisfied literal in `tmp[0 ..< sz)`, or `0xFFFFFFFF#32`. -/
@[expose] def fullVivBestImpliedM6Spec : Spec [i64, i32] [i32] := fun (h, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ sz.toNat ≤ c.max_vars ∧
    (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 32,
      (r ≠ 0xFFFFFFFF#32 → r.toNat < 2 * s.core.cur_vars ∧ s.core.vals[r.toNat]?.getD 0#8 = 1#8) →
      Q (r, ()) m

/-- `full_viv_reestablish_m6(h, cref)`: 2WL watch-invariant backtrack repair preserving
`FullSparseInvW`, arena, `red_refs`, and `tarjan_reach`. -/
@[expose] def fullVivReestablishM6Spec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_inst_check_m6(h, sz, iolen, not_lit)`: verifies every literal in
`work_stk2[0 ..< iolen)` is `not_lit` or in `tmp[0 ..< sz - 1)` with cleared `lit_mark`. -/
@[expose] def fullVivInstCheckM6Spec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, sz, iolen, not_lit, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ 1 ≤ sz.toNat ∧ sz.toNat ≤ c.max_vars ∧
      iolen.toNat ≤ c.max_vars ∧
      (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ i < iolen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' m',
        let s' : FullState := { s with core := { s.core with lit_mark := lm' } }
        FullSparseInvW c F0 F_cur s' →
        (ok = true → ∀ i < iolen.toNat,
          s.scratch.work_stk2[i]?.getD 0#32 = not_lit ∨
          ∃ k, k + 1 < sz.toNat ∧
            s.scratch.work_stk2[i]?.getD 0#32 = s.core.tmp[k]?.getD 0#32) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_viv_inst_m6(h, cref, sz)`: instantiation strengthening over `FullM6HdrMem`
calling `full_propagate_ignore`, dropping `tmp[sz - 1]` and committing `tmp[0 ..< sz - 1)`. -/
@[expose] def vivInstM6Spec : Spec [i64, i32, i32] [i64] := fun (h, cref, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInvW c F0 F_cur s ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    fullArenaClauseSize s cref.toNat = sz.toNat ∧ sz.toNat ≤ c.max_vars ∧
    ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm (fullArenaClauseLits s cref.toNat) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_finish_m6(h, cref, sz, confl, implied, all_done)`: post-loop deduction,
subsumption promotion/glue-lowering, commit, deletion, instantiation (`FullM6HdrMem`), and
2WL re-establishment. -/
@[expose] def vivFinishM6Spec : Spec [i64, i32, i32, .bool, i32, .bool] [i64] :=
  fun (h, cref, sz, confl, implied, all_done, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInvW c F0 F_cur s ∧
      sz.toNat ≤ c.max_vars ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      fullArenaClauseSize s cref.toNat = sz.toNat ∧
      ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm (fullArenaClauseLits s cref.toNat) ∧
      (confl = true → FullConflictOkW F_cur s) ∧
      (confl = false → implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (confl = false → implied = 0xFFFFFFFF#32 → all_done = true →
        s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullSparseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.arena_len = s.core.arena_len →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.red_refs = s.scratch.red_refs →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_sift_counts_m6(h, start, n)`: sifts element `start` within `tmp_lits[0 ..< n)`
in place, preserving `tmp_lits.take sz` as a permutation (`n ≤ sz ≤ max_vars`). -/
@[expose] def fullVivSiftCountsM6Spec : Spec [i64, i64, i64] [] :=
  fun (h, start, n, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (sz : Nat),
      h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ sz ∧ sz ≤ c.max_vars ∧
      start.toNat < n.toNat ∧
      (∀ k < sz, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ tmp' m', tmp'.length = c.max_vars →
        (tmp'.take sz).Perm (s.core.tmp.take sz) →
        (∀ k, sz ≤ k → k < c.max_vars → tmp'[k]? = s.core.tmp[k]?) →
        (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

/-- `full_viv_sort_counts_m6(h, sz)`: heapsorts `tmp_lits[0 ..< sz)` in place by literal
counts stored in `tarjan_reach`. -/
@[expose] def fullVivSortCountsM6Spec : Spec [i64, i32] [] := fun (h, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ sz.toNat ≤ c.max_vars ∧
    (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' m', tmp'.length = c.max_vars →
      (tmp'.take sz.toNat).Perm (s.core.tmp.take sz.toNat) →
      (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp'[k]? = s.core.tmp[k]?) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

/-- `full_viv_has_l0_m6(h, cref, sz)`: read-only level-0 assignment scan over `cref`. -/
@[expose] def fullVivHasL0M6Spec : Spec [i64, i32, i32] [.bool] :=
  fun (h, cref, sz, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s cref.toNat = false ∧ sz.toNat = fullArenaClauseSize s cref.toNat ∧
      (FullMem c s ⋆ R) m ∧ ∀ r : Bool, Q (r, ()) m

/-- `full_viv_l0_simp_m6(h, cref, sz)`: if `cref` has a level-0 assigned literal, backtracks
to level `0` and runs `full_viv_simplify_m6`; returns `0`, `1`, `2`, or `20`. -/
@[expose] def fullVivL0SimpM6Spec : Spec [i64, i32, i32] [i64] :=
  fun (h, cref, sz, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s cref.toNat = false ∧ sz.toNat = fullArenaClauseSize s cref.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullSparseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
        s'.core.arena_len = s.core.arena_len →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.red_refs = s.scratch.red_refs →
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 0#64 →
          cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_reuse_prefix_m6(h, cref, sz)`: prefix-trail reuse keeping the longest shared
decision prefix and backtracking only to `keep_lvl`. -/
@[expose] def fullVivReusePrefixM6Spec : Spec [i64, i32, i32] [] :=
  fun (h, _cref, sz, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ sz.toNat ≤ c.max_vars ∧
      (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullSparseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
        s'.core.tmp = s.core.tmp → s'.scratch.red_refs = s.scratch.red_refs →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_clause_m6(h, cref)`: full M6 single-clause vivification threading
`FullM6HdrMem` across `full_propagate_ignore` and `full_viv_finish_m6`, clearing `PH_VIV`. -/
@[expose] def vivClauseM6Spec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInvW c F0 F_cur s ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_tier_match_m6(h, hdr, tier_mode)`: read-only tier filter predicate. -/
@[expose] def fullVivTierMatchM6Spec : Spec [i64, i32, i64] [.bool] :=
  fun (h, _hdr, _tier_mode, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ (FullMem c s ⋆ R) m ∧ ∀ r, Q (r, ()) m

/-- `full_viv_clear_tier_m6(h, tier_mode)`: clears `PH_VIV` on matching non-garbage tier
clauses, preserving `FullSparseInv`, `cur_level = 0`, and `fuel`. -/
@[expose] def fullVivClearTierM6Spec : Spec [i64, i64] [] :=
  fun (h, _tier_mode, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_collect_fid(h, tier_mode)`: 2-pass candidate collection into `red_refs[0 ..< bn)`
setting `PH_VIV` when no prioritized clauses exist, preserving `FullSparseInv` and
`fullArenaClauseRefs`. -/
@[expose] def vivCollectFidSpec : Spec [i64, i64] [i64] :=
  fun (h, _tier_mode, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ bn arena' rr' m',
        let s' : FullState :=
          { s with
            core := { s.core with arena := arena' }
            scratch := { s.scratch with red_refs := rr' } }
        bn.toNat ≤ c.red_cap → rr'.length = c.red_cap →
        FullSparseInv c F0 s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
        (FullMem c s' ⋆ R) m' → Q (bn, ()) m'

/-- `full_viv_sort2_fid(h, bn, mode)`: 2-key Shell sort of `red_refs[0 ..< bn)` using scratch
keys in `red_refs + bn` (`mode = 1`, `3 * bn ≤ red_cap`) or `scratch_buf` (`mode = 2`,
`2 * bn ≤ scratch_cap`). -/
@[expose] def fullVivSort2FidSpec : Spec [i64, i64, i64] [] :=
  fun (h, bn, mode, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ bn.toNat ≤ c.red_cap ∧
      ((mode = 1#64 ∧ 3 * bn.toNat ≤ c.red_cap) ∨
       (mode = 2#64 ∧ 2 * bn.toNat ≤ c.scratch_cap)) ∧
      (∀ k < bn.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ rr' scr' m',
        rr'.length = c.red_cap → scr'.length = c.scratch_cap →
        (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
        (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } }
          ⋆ R) m' → Q () m'

/-- `full_viv_sort_fid(h, bn)`: dispatches 2-key sort, 1-key sort, or 2-way `PH_VIV` partition
over `red_refs[0 ..< bn)`. -/
@[expose] def fullVivSortFidSpec : Spec [i64, i64] [] := fun (h, bn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ bn.toNat ≤ c.red_cap ∧
    (∀ k < bn.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' scr' m',
      rr'.length = c.red_cap → scr'.length = c.scratch_cap →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } }
        ⋆ R) m' → Q () m'

/-- `full_vivify_tier_m6_hdr(h, tier_mode, budget, tick_lim)`: collects, counts, sorts,
and vivifies one tier with watermark tick cap while preserving `h->probing`. -/
@[expose] def vivifyTierM6HdrSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, _tier_mode, budget, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullSparseInv c F0 s' →
        (s.core.cur_level = 0 → s'.core.cur_level = 0) →
        s'.core.probing = s.core.probing →
        (budget ≠ 0#64 → s'.core.cur_level = 0) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- `full_vivify_m6_hdr(h)`: multi-tier vivification driver preserving `h->probing` and
`FullM6HdrMem` extension invariants (`1`: done; `20`: `F0.Unsat`). -/
@[expose] def vivifyM6HdrSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. Canonical Dependency & Specification Tables (`specs_sigs`, `specs_nodup`, `specs_xfree`)
-/

/-- Upstream canonical specifications imported by `Src.Vivify`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Clause.Spec.specs ++
  PropSearch.Spec.specs ++ Tiers.Spec.specs ++ Watch.Spec.specs

/-- Canonical `28`-row specification table aligned 1:1 with `Src.Vivify.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_viv_unreason_m6", [i64, i32], [], fullVivUnreasonM6Spec, true⟩
  , ⟨"full_viv_watch_rank_m6", [i64, i32], [i64], fullVivWatchRankM6Spec, true⟩
  , ⟨"full_viv_best_watch_m6", [i64, i32], [], fullVivBestWatchM6Spec, true⟩
  , ⟨"full_viv_simplify_m6", [i64, i32], [i64], fullVivSimplifyM6Spec, true⟩
  , ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64], fullVivCommitM6Spec, true⟩
  , ⟨"full_viv_mark_garb_m6", [i64, i32], [], fullVivMarkGarbM6Spec, true⟩
  , ⟨"full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool], fullVivSubsumesBinM6Spec, true⟩
  , ⟨"full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool], fullVivSubsumesClM6Spec, true⟩
  , ⟨"full_viv_recompute_promote_fid", [i64, i32], [], vivRecomputePromoteSpec, true⟩
  , ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32], vivDeduceM6Spec, true⟩
  , ⟨"full_viv_best_implied_m6", [i64, i32], [i32], fullVivBestImpliedM6Spec, true⟩
  , ⟨"full_viv_reestablish_m6", [i64, i32], [], fullVivReestablishM6Spec, true⟩
  , ⟨"full_viv_inst_check_m6", [i64, i32, i32, i32], [.bool], fullVivInstCheckM6Spec, true⟩
  , ⟨"full_viv_inst_m6", [i64, i32, i32], [i64], vivInstM6Spec, true⟩
  , ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64], vivFinishM6Spec, true⟩
  , ⟨"full_viv_sift_counts_m6", [i64, i64, i64], [], fullVivSiftCountsM6Spec, true⟩
  , ⟨"full_viv_sort_counts_m6", [i64, i32], [], fullVivSortCountsM6Spec, true⟩
  , ⟨"full_viv_has_l0_m6", [i64, i32, i32], [.bool], fullVivHasL0M6Spec, true⟩
  , ⟨"full_viv_l0_simp_m6", [i64, i32, i32], [i64], fullVivL0SimpM6Spec, true⟩
  , ⟨"full_viv_reuse_prefix_m6", [i64, i32, i32], [], fullVivReusePrefixM6Spec, true⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64], vivClauseM6Spec, true⟩
  , ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool], fullVivTierMatchM6Spec, true⟩
  , ⟨"full_viv_clear_tier_m6", [i64, i64], [], fullVivClearTierM6Spec, true⟩
  , ⟨"full_viv_collect_fid", [i64, i64], [i64], vivCollectFidSpec, true⟩
  , ⟨"full_viv_sort2_fid", [i64, i64, i64], [], fullVivSort2FidSpec, true⟩
  , ⟨"full_viv_sort_fid", [i64, i64], [], fullVivSortFidSpec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], vivifyTierM6HdrSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], vivifyM6HdrSpec, true⟩
  ]

theorem fullVivUnreasonM6Spec_xfree : Spec.XFree fullVivUnreasonM6Spec := by xfree
theorem fullVivWatchRankM6Spec_xfree : Spec.XFree fullVivWatchRankM6Spec := by xfree
theorem fullVivBestWatchM6Spec_xfree : Spec.XFree fullVivBestWatchM6Spec := by xfree
theorem fullVivSimplifyM6Spec_xfree : Spec.XFree fullVivSimplifyM6Spec := by xfree
theorem fullVivCommitM6Spec_xfree : Spec.XFree fullVivCommitM6Spec := by xfree
theorem fullVivMarkGarbM6Spec_xfree : Spec.XFree fullVivMarkGarbM6Spec := by xfree
theorem fullVivSubsumesBinM6Spec_xfree : Spec.XFree fullVivSubsumesBinM6Spec := by xfree
theorem fullVivSubsumesClM6Spec_xfree : Spec.XFree fullVivSubsumesClM6Spec := by xfree
theorem vivRecomputePromoteSpec_xfree : Spec.XFree vivRecomputePromoteSpec := by xfree
theorem vivDeduceM6Spec_xfree : Spec.XFree vivDeduceM6Spec := by xfree
theorem fullVivBestImpliedM6Spec_xfree : Spec.XFree fullVivBestImpliedM6Spec := by xfree
theorem fullVivReestablishM6Spec_xfree : Spec.XFree fullVivReestablishM6Spec := by xfree
theorem fullVivInstCheckM6Spec_xfree : Spec.XFree fullVivInstCheckM6Spec := by xfree
theorem vivInstM6Spec_xfree : Spec.XFree vivInstM6Spec := by xfree
theorem vivFinishM6Spec_xfree : Spec.XFree vivFinishM6Spec := by xfree
theorem fullVivSiftCountsM6Spec_xfree : Spec.XFree fullVivSiftCountsM6Spec := by xfree
theorem fullVivSortCountsM6Spec_xfree : Spec.XFree fullVivSortCountsM6Spec := by xfree
theorem fullVivHasL0M6Spec_xfree : Spec.XFree fullVivHasL0M6Spec := by xfree
theorem fullVivL0SimpM6Spec_xfree : Spec.XFree fullVivL0SimpM6Spec := by xfree
theorem fullVivReusePrefixM6Spec_xfree : Spec.XFree fullVivReusePrefixM6Spec := by xfree
theorem vivClauseM6Spec_xfree : Spec.XFree vivClauseM6Spec := by xfree
theorem fullVivTierMatchM6Spec_xfree : Spec.XFree fullVivTierMatchM6Spec := by xfree
theorem fullVivClearTierM6Spec_xfree : Spec.XFree fullVivClearTierM6Spec := by xfree
theorem vivCollectFidSpec_xfree : Spec.XFree vivCollectFidSpec := by xfree
theorem fullVivSort2FidSpec_xfree : Spec.XFree fullVivSort2FidSpec := by xfree
theorem fullVivSortFidSpec_xfree : Spec.XFree fullVivSortFidSpec := by xfree
theorem vivifyTierM6HdrSpec_xfree : Spec.XFree vivifyTierM6HdrSpec := by xfree
theorem vivifyM6HdrSpec_xfree : Spec.XFree vivifyM6HdrSpec := by xfree

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullVivUnreasonM6Spec_xfree
  · exact fullVivWatchRankM6Spec_xfree
  · exact fullVivBestWatchM6Spec_xfree
  · exact fullVivSimplifyM6Spec_xfree
  · exact fullVivCommitM6Spec_xfree
  · exact fullVivMarkGarbM6Spec_xfree
  · exact fullVivSubsumesBinM6Spec_xfree
  · exact fullVivSubsumesClM6Spec_xfree
  · exact vivRecomputePromoteSpec_xfree
  · exact vivDeduceM6Spec_xfree
  · exact fullVivBestImpliedM6Spec_xfree
  · exact fullVivReestablishM6Spec_xfree
  · exact fullVivInstCheckM6Spec_xfree
  · exact vivInstM6Spec_xfree
  · exact vivFinishM6Spec_xfree
  · exact fullVivSiftCountsM6Spec_xfree
  · exact fullVivSortCountsM6Spec_xfree
  · exact fullVivHasL0M6Spec_xfree
  · exact fullVivL0SimpM6Spec_xfree
  · exact fullVivReusePrefixM6Spec_xfree
  · exact vivClauseM6Spec_xfree
  · exact fullVivTierMatchM6Spec_xfree
  · exact fullVivClearTierM6Spec_xfree
  · exact vivCollectFidSpec_xfree
  · exact fullVivSort2FidSpec_xfree
  · exact fullVivSortFidSpec_xfree
  · exact vivifyTierM6HdrSpec_xfree
  · exact vivifyM6HdrSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Vivify.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

/-! ## 4. `Env.Has` Projections -/

private theorem mem_has {Γ : Env} (h : Γ.Sat specs) {n : Nat} (hn : n < specs.length)
    (hx : (specs[n]'hn).spec.XFree) :
    Γ.Has (specs[n]'hn).name (specs[n]'hn).spec :=
  Env.Sat.has h (List.getElem_mem hn) hx

theorem has_full_viv_unreason_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_unreason_m6" fullVivUnreasonM6Spec :=
  mem_has h (n := 0) (by decide) fullVivUnreasonM6Spec_xfree

theorem has_full_viv_watch_rank_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_watch_rank_m6" fullVivWatchRankM6Spec :=
  mem_has h (n := 1) (by decide) fullVivWatchRankM6Spec_xfree

theorem has_full_viv_best_watch_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_best_watch_m6" fullVivBestWatchM6Spec :=
  mem_has h (n := 2) (by decide) fullVivBestWatchM6Spec_xfree

theorem has_full_viv_simplify_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_simplify_m6" fullVivSimplifyM6Spec :=
  mem_has h (n := 3) (by decide) fullVivSimplifyM6Spec_xfree

theorem has_full_viv_commit_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_commit_m6" fullVivCommitM6Spec :=
  mem_has h (n := 4) (by decide) fullVivCommitM6Spec_xfree

theorem has_full_viv_mark_garb_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_mark_garb_m6" fullVivMarkGarbM6Spec :=
  mem_has h (n := 5) (by decide) fullVivMarkGarbM6Spec_xfree

theorem has_full_viv_subsumes_bin_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_subsumes_bin_m6" fullVivSubsumesBinM6Spec :=
  mem_has h (n := 6) (by decide) fullVivSubsumesBinM6Spec_xfree

theorem has_full_viv_subsumes_cl_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_subsumes_cl_m6" fullVivSubsumesClM6Spec :=
  mem_has h (n := 7) (by decide) fullVivSubsumesClM6Spec_xfree

theorem has_full_viv_recompute_promote_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_recompute_promote_fid" vivRecomputePromoteSpec :=
  mem_has h (n := 8) (by decide) vivRecomputePromoteSpec_xfree

theorem has_full_viv_deduce_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_deduce_m6" vivDeduceM6Spec :=
  mem_has h (n := 9) (by decide) vivDeduceM6Spec_xfree

theorem has_full_viv_best_implied_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_best_implied_m6" fullVivBestImpliedM6Spec :=
  mem_has h (n := 10) (by decide) fullVivBestImpliedM6Spec_xfree

theorem has_full_viv_reestablish_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_reestablish_m6" fullVivReestablishM6Spec :=
  mem_has h (n := 11) (by decide) fullVivReestablishM6Spec_xfree

theorem has_full_viv_inst_check_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_inst_check_m6" fullVivInstCheckM6Spec :=
  mem_has h (n := 12) (by decide) fullVivInstCheckM6Spec_xfree

theorem has_full_viv_inst_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_inst_m6" vivInstM6Spec :=
  mem_has h (n := 13) (by decide) vivInstM6Spec_xfree

theorem has_full_viv_finish_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_finish_m6" vivFinishM6Spec :=
  mem_has h (n := 14) (by decide) vivFinishM6Spec_xfree

theorem has_full_viv_sift_counts_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_sift_counts_m6" fullVivSiftCountsM6Spec :=
  mem_has h (n := 15) (by decide) fullVivSiftCountsM6Spec_xfree

theorem has_full_viv_sort_counts_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_sort_counts_m6" fullVivSortCountsM6Spec :=
  mem_has h (n := 16) (by decide) fullVivSortCountsM6Spec_xfree

theorem has_full_viv_has_l0_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_has_l0_m6" fullVivHasL0M6Spec :=
  mem_has h (n := 17) (by decide) fullVivHasL0M6Spec_xfree

theorem has_full_viv_l0_simp_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_l0_simp_m6" fullVivL0SimpM6Spec :=
  mem_has h (n := 18) (by decide) fullVivL0SimpM6Spec_xfree

theorem has_full_viv_reuse_prefix_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_reuse_prefix_m6" fullVivReusePrefixM6Spec :=
  mem_has h (n := 19) (by decide) fullVivReusePrefixM6Spec_xfree

theorem has_full_viv_clause_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_clause_m6" vivClauseM6Spec :=
  mem_has h (n := 20) (by decide) vivClauseM6Spec_xfree

theorem has_full_viv_tier_match_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_tier_match_m6" fullVivTierMatchM6Spec :=
  mem_has h (n := 21) (by decide) fullVivTierMatchM6Spec_xfree

theorem has_full_viv_clear_tier_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_clear_tier_m6" fullVivClearTierM6Spec :=
  mem_has h (n := 22) (by decide) fullVivClearTierM6Spec_xfree

theorem has_full_viv_collect_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_collect_fid" vivCollectFidSpec :=
  mem_has h (n := 23) (by decide) vivCollectFidSpec_xfree

theorem has_full_viv_sort2_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_sort2_fid" fullVivSort2FidSpec :=
  mem_has h (n := 24) (by decide) fullVivSort2FidSpec_xfree

theorem has_full_viv_sort_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_viv_sort_fid" fullVivSortFidSpec :=
  mem_has h (n := 25) (by decide) fullVivSortFidSpec_xfree

theorem has_full_vivify_tier_m6_hdr {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_vivify_tier_m6_hdr" vivifyTierM6HdrSpec :=
  mem_has h (n := 26) (by decide) vivifyTierM6HdrSpec_xfree

theorem has_full_vivify_m6_hdr {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_vivify_m6_hdr" vivifyM6HdrSpec :=
  mem_has h (n := 27) (by decide) vivifyM6HdrSpec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
