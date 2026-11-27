/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import Kraken.Mem
public import Kraken.Separation

/-!
# Kissat `D-Full` Per-Function UNSAT-Only `Spec` Contracts (`Proof.Spec.Contracts2`)

1. `Full2` 1UIP/OTFS analysis, minimization, block shrinking, decision, walk, extend contracts.
2. Top-level `fullSolveBytesCoreSpec` and `fullSolveBytesSpec`.
3. `FullCfgCompat` and `fullCfgShrinkMv` compatibility / header shrink helpers.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 5. `Full2` 1UIP/OTFS analysis, minimization, block shrinking, decision, walk, extend -/

@[expose]
def fullAnalyzeLitSpec : Spec [i64, i32, i32] [.bool] := fun (h, lit, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    s.core.tmp_cnt + 1 < 2 ^ 64 ∧ FullAnaMarksCov c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' ws1' ant' res' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl' }
          scratch := { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }
      s'.LengthsOk c → FullAnaMarksCov c s' → s.core.tmp_len ≤ tl' → tl' ≤ s.core.tmp_len + 1 →
      tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      ant' = s.scratch.ant_sz +
        (if lit.toNat / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level
         then 1#64 else 0#64) →
      res' = s.scratch.res_sz +
        (if lit.toNat / 2 < s.core.cur_vars ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
            mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 then 1#64 else 0#64) →
      tc' = s.core.tmp_cnt +
        (if lit.toNat / 2 < s.core.cur_vars ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
            mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level
         then 1 else 0) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        lit.toNat / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
        0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
        (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' →
        (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧ lit.toNat / 2 < s.core.cur_vars ∧
        lit.toNat / 2 ≠ skip_var.toNat ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
        0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
        mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) →
      (ok = true → lit.toNat / 2 < s.core.cur_vars ∧
        (lit.toNat / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
              (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
              tc' = s.core.tmp_cnt + 1) ∧
            (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
              (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level →
              tl' = s.core.tmp_len + 1 ∧ tmp'[s.core.tmp_len]? = some lit)))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose]
def fullAnalyzeRsnSpec : Spec [i64, i32, i32] [.bool] := fun (h, rsn, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
    s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
    (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' arena' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧
        0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧
        mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
      (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧
          (l / 2 ≠ skip_var.toNat →
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                  (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullClearAnaSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ mrk' m', mrk'.length = c.max_vars →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8) →
      (∀ i < s.core.min_clr_len, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars →
        mrk'[(s.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#8 = 0#8) →
      (FullAnaMarksCov c s → ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (FullMem c { s with core := { s.core with mrk := mrk', min_clr_len := 0 } } ⋆ R) m' → Q () m'

@[expose] def fullBumpAnalyzedSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullAnaMarksCov c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ mrk' mcl' sc' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → FullAnaMarksCov c s' → FullExtScratchPres s s' →
      sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullOtfsLargeSpec : Spec [i64, i32, i32] [.bool] := fun (h, cref, uip, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut idx_u : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ uip.toNat < 2 * s.core.cur_vars ∧
    idx_u < cut ∧ (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat ∧
    s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref ∧
    (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits s cref.toNat).filter fun l =>
        decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                                wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' cref.toNat = false ∧
        ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
            ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullOtfsBinSpec : Spec [i64, i32, i32] [.bool] := fun (h, cref, uip, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut idx_u : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ uip.toNat < 2 * s.core.cur_vars ∧
    idx_u < cut ∧ (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat ∧
    s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref ∧
    (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (∀ f0 f1 : BitVec 32,
      f0.toNat ∈ fullArenaClauseLits s cref.toNat → f1.toNat ∈ fullArenaClauseLits s cref.toNat →
      f0 ≠ uip → f1 ≠ uip → f0 ≠ f1 →
      0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat →
      0 < (s.core.lvl[f1.toNat / 2]?.getD 0#32).toNat →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) arena' ag' wvec' wstk' wlen' wu' nb' ctype' cr' c0' c1' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                confl_type := ctype', confl_ref := cr', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ctype' = 1#64 ∧ FullConflictOkCut F_cur idx_u s') →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullOtfsSubsumeSpec : Spec [i64, i32, i64, i64, .bool] [] :=
  fun (h, new_confl, old_ctype, old_cref, to_bin, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
      (old_ctype = 2#64 → old_cref ≠ 0xFFFFFFFF#64 →
        old_cref.toNat ∈ fullArenaClauseRefs s ∧
        (to_bin = false → new_confl.toNat ∈ fullArenaClauseRefs s) ∧
        ∀ idx < s.core.trail_end,
          let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
          let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
          (idx < cut ∨ (s.core.lvl[v]?.getD 0#32).toNat < s.core.cur_level) →
          rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ old_cref.toNat) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ arena' ag' ni' nr' m',
        let s' : FullState :=
          { s with core := { s.core with arena := arena', arena_garbage := ag',
                                         num_irred := ni', num_redundant := nr' } }
        s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullArenaVarsNodup s' →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseLits s' r = fullArenaClauseLits s r ∧
          ((old_ctype = 2#64 → r ≠ old_cref.toNat) →
            fullArenaClauseGarb s' r = fullArenaClauseGarb s r)) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Purely structural minimization mark invariant (`FullMinSpecs.FullMinMarkInv`). -/
structure FullMinMarkInv (k : FullCoreState) (keep : List Nat) : Prop where
  mrk_dom : ∀ v < k.cur_vars, (k.mrk[v]?.getD 0#8 &&& 0xF1#8) = 0#8
  clr_cov : k.min_clr_full = 0#64 → ∀ v < k.cur_vars,
    (k.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 →
    ∃ j < k.min_clr_len, (k.min_clr[j]?.getD 0#32).toNat = v
  rem_sound : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    (k.mrk[p / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 →
    (p ^^^ 1) ∈ keep ∨
      (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level ∧
      let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * k.cur_vars ∧
        ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((k.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (k.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else
        rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
          q = p ∨ ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((k.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (k.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)

@[expose] def fullMinMarkCore (k : FullCoreState) (v : Nat) (tag : BitVec 8) : FullCoreState :=
  let cur := k.mrk[v]?.getD 0#8
  let mclr' := if cur = 0#8 ∧ k.min_clr_len < k.cur_vars then
                 k.min_clr.set k.min_clr_len (BitVec.ofNat 32 v)
               else k.min_clr
  let mcl' := if cur = 0#8 ∧ k.min_clr_len < k.cur_vars then k.min_clr_len + 1 else k.min_clr_len
  let mcf' := if cur = 0#8 ∧ ¬ k.min_clr_len < k.cur_vars then 1#64 else k.min_clr_full
  { k with mrk := k.mrk.set v (cur ||| tag),
           min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }

/-- State update of `full_min_mark(h, v, tag)`. -/
@[expose] def fullMinMarkState (s : FullState) (v : Nat) (tag : BitVec 8) : FullState :=
  { s with core := fullMinMarkCore s.core v tag }

@[expose] def fullMinMarkSpec : Spec [i64, i32, i8] [] := fun (h, v, tag, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    let cur := s.core.mrk[v.toNat]?.getD 0#8
    if s.core.cur_vars ≤ v.toNat ∨ (cur &&& tag) ≠ 0#8 then
      Q () m
    else
      ∀ m', (FullMem c (fullMinMarkState s v.toNat tag) ⋆ R) m' → Q () m'

@[expose] def fullMinLitSpec : Spec [i64, i32] [.bool] := fun (h, root_lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ FullMinMarkInv s.core keepSet ∧
    root_lit.toNat < 2 * s.core.cur_vars ∧ s.core.vals[root_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
    (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
    (∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' mstk' mclr' mcl' mcf' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_stk := mstk', min_clr := mclr',
                                       min_clr_len := mcl', min_clr_full := mcf' } }
      s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv s'.core keepSet →
      (ok = true →
        (∀ keep' : List Nat,
          (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') → FullMinMarkInv s'.core keep') ∧
        FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullTmpLessSpec : Spec [i64, i64, i32, i32] [.bool] :=
  fun (lvl_ptr, tpos_ptr, a, b, ()) m Q _ =>
    ∃ (lvl tpos : List (BitVec 32)) (R : Mem 64 → Prop),
      a.toNat / 2 < lvl.length ∧ b.toNat / 2 < lvl.length ∧
      a.toNat / 2 < tpos.length ∧ b.toNat / 2 < tpos.length ∧
      (array (t := i32) lvl_ptr lvl ⋆ array (t := i32) tpos_ptr tpos ⋆ R) m ∧
      Q (fullTmpKeyLt lvl tpos a b, ()) m

@[expose] def fullSortTmpSiftSpec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (tmp_ptr, lvl_ptr, tpos_ptr, start, n, ()) m Q _ =>
    ∃ (tmp lvl tpos : List (BitVec 32)) (R : Mem 64 → Prop),
      start.toNat < n.toNat ∧ 1 + n.toNat ≤ tmp.length ∧ n.toNat < 2 ^ 60 ∧
      (∀ k, 1 ≤ k → k < 1 + n.toNat → (tmp[k]?.getD 0#32).toNat / 2 < lvl.length ∧
        (tmp[k]?.getD 0#32).toNat / 2 < tpos.length) ∧
      FullTmpMaxHeap lvl tpos tmp (start.toNat + 1) n.toNat ∧
      (array (t := i32) tmp_ptr tmp ⋆ array (t := i32) lvl_ptr lvl ⋆
        array (t := i32) tpos_ptr tpos ⋆ R) m ∧
      ∀ tmp' m', tmp'.length = tmp.length → tmp'.Perm tmp →
        (∀ k, (k = 0 ∨ 1 + n.toNat ≤ k) → tmp'[k]? = tmp[k]?) →
        FullSortSliceEq tmp' tmp (1 + n.toNat) →
        FullTmpMaxHeap lvl tpos tmp' start.toNat n.toNat →
        (array (t := i32) tmp_ptr tmp' ⋆ array (t := i32) lvl_ptr lvl ⋆
          array (t := i32) tpos_ptr tpos ⋆ R) m' → Q () m'

@[expose] def fullSortTmpSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.tmp_len ≤ c.max_vars ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' m', tmp'.length = c.max_vars →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

@[expose] def fullShrinkLowerSpec : Spec [i64, i32, i32] [.bool] := fun (h, ot, ov, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ FullMinMarkInv s.core keepSet ∧
    ov.toNat = ot.toNat / 2 ∧ ot.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 ∧
    (s.core.lvl[ov.toNat]?.getD 0#32).toNat < s.core.cur_level ∧
    (∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[ov.toNat]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' mstk' mclr' mcl' mcf' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_stk := mstk', min_clr := mclr',
                                       min_clr_len := mcl', min_clr_full := mcf' } }
      s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv s'.core keepSet →
      (ok = true → (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullShrinkBlkSpec : Spec [i64, i64, i64, i32, i64] [] :=
  fun (h, beg, end_b, blvl, max_tr, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧
      FullMinMarkInv s.core
        (((s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
      (∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      1 ≤ beg.toNat ∧ beg.toNat < end_b.toNat ∧ end_b.toNat ≤ s.core.tmp_len ∧
      s.core.tmp_len ≤ s.core.cur_vars ∧ 0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level ∧
      (∀ k, beg.toNat ≤ k → k < end_b.toNat →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
        (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat) ∧
      (∀ k < s.core.tmp_len, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ tmp' mrk' mstk' mclr' mcl' mcf' sstk' m',
        let s' : FullState :=
          { core := { s.core with tmp := tmp', mrk := mrk', min_stk := mstk', min_clr := mclr',
                                  min_clr_len := mcl', min_clr_full := mcf' }
            scratch := { s.scratch with shrink_stk := sstk' } }
        FullOtfsCoreInv c F0 s' →
        FullMinMarkInv s'.core
          (((tmp'.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
        (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
        (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (∀ k < s.core.tmp_len, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.core.tmp[k]?) →
        (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
        ((((s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map
            fun x => x.toNat / 2).Nodup →
          (∀ k < s.core.tmp_len, (k < beg.toNat ∨ end_b.toNat ≤ k) →
            s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
            (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) →
          (((tmp'.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map
            fun x => x.toNat / 2).Nodup) →
        (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
          (cnfOfClauses F_cur).EntailsClause (cnfClause
            (((s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
          FullOtfsWitnessInv c F0 F_cur s'.core ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause
            (((tmp'.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) →
        (∀ k < s.core.tmp_len, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          let l := (tmp'[k]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullMinShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) ∧
    (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk',
                                min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }
          scratch := { s.scratch with conflicts := conf', learned_lits := llits',
                                      min_removed := mrem', shrink_stk := sstk' } }
      s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullDetNewLevelSpec : Spec [i64, i64] [i64] := fun (h, jump, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64, (s.core.cur_level = 0 → r = 0#64) →
      (0 < s.core.cur_level → jump.toNat < s.core.cur_level →
        jump.toNat ≤ r.toNat ∧ r.toNat < s.core.cur_level) → Q (r, ()) m

@[expose] def fullOneLitConflSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCutInvW c F0 F_cur cut s ∧ FullConflictOkCut F_cur cut s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (r = 2#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 0#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ 0 < s'.core.cur_level ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullDeduce1uipSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧
    FullConflictOkCut F_cur cut s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullEagerSubsumeSpec : Spec [i64, i64] [] := fun (h, new_ref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
    (∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (new_ref.toNat < 0x80000000 → new_ref.toNat ∈ fullArenaClauseRefs s) ∧ (FullMem c s ⋆ R) m ∧
    ∀ arena' ag' sc' m',
      let s' : FullState :=
        { s with core := { s.core with arena := arena', arena_garbage := ag' }, scratch := sc' }
      FullSparseInvW c F0 F_cur s' → sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullLearnClauseSpec : Spec [i64, i64] [i64] := fun (h, _glue, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullOtfsInvW c F0 F_cur s ∧ 0 < s.core.cur_level ∧
    1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level ∧
      lv ≤ (s.core.lvl[(s.core.tmp[s.core.tmp_len - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullAnalyzeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ FullConflictOkW F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s'.scratch.work_stk2 = s.scratch.work_stk2 ∧ (r = 20#64 → FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode)) →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 6. Top-level `fullSolveBytesCoreSpec` & `fullSolveBytesSpec` -/

/-- Core UNSAT-only `kissat_solve_bytes` contract carrying general UNSAT soundness (`0 | 10 | 20`)
and deterministic level-0 unit-contradiction non-vacuity (`UnitUnsatTrace → r = 20#64`). -/
@[expose] def fullSolveBytesCoreSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Headline UNSAT-only soundness specification of `kissat_solve_bytes` (`D-Full`). -/
@[expose] def fullSolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

theorem fullSolveBytesCoreSpec_of_spec
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullSolveBytesSpec args m Q X) : fullSolveBytesCoreSpec args m Q X := by
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' hdom hu _ hm' => hQ r m' hdom hu hm'⟩

/-! ## 2. `FullCfgCompat`, `FullCfg.shrinkMv`, & header shrink stores -/

/-- Configuration compatibility after dead-variable compaction shrinks `d.mv`:
preserves `hdr`, `avail`, `max_vars`, and all buffer capacities, keeping pointers and `pad` equal
while allowing `mv` to decrease (`bva_cap := max_vars - mv`). -/
structure FullCfgCompat (c c' : FullCfg) : Prop where
  hdr : c'.hdr = c.hdr
  avail : c'.avail = c.avail
  mv_le : c'.mv ≤ c.mv
  max_vars : c'.max_vars = c.max_vars
  nc : c'.nc = c.nc
  arena_cap : c'.arena_cap = c.arena_cap
  wcap : c'.wcap = c.wcap
  delayed_cap : c'.delayed_cap = c.delayed_cap
  red_cap : c'.red_cap = c.red_cap
  extend_cap : c'.extend_cap = c.extend_cap
  scratch_cap : c'.scratch_cap = c.scratch_cap

theorem FullCfgCompat.refl (c : FullCfg) : FullCfgCompat c c :=
  ⟨rfl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FullCfgCompat.trans {c1 c2 c3 : FullCfg}
    (h12 : FullCfgCompat c1 c2) (h23 : FullCfgCompat c2 c3) : FullCfgCompat c1 c3 :=
  ⟨h23.hdr.trans h12.hdr, h23.avail.trans h12.avail, Nat.le_trans h23.mv_le h12.mv_le,
   h23.max_vars.trans h12.max_vars, h23.nc.trans h12.nc, h23.arena_cap.trans h12.arena_cap,
   h23.wcap.trans h12.wcap, h23.delayed_cap.trans h12.delayed_cap,
   h23.red_cap.trans h12.red_cap, h23.extend_cap.trans h12.extend_cap,
   h23.scratch_cap.trans h12.scratch_cap⟩

/-- Shrink `mv` to `mv' ≤ c.mv` and grow `bva_cap` to `c.max_vars - mv'`. -/
@[expose] def fullCfgShrinkMv (c : FullCfg) (mv' : Nat) (hle : mv' ≤ c.mv) : FullCfg where
  hdr := c.hdr
  avail := c.avail
  mv := mv'
  max_vars := c.max_vars
  bva_cap := c.max_vars - mv'
  nc := c.nc
  arena_cap := c.arena_cap
  wcap := c.wcap
  delayed_cap := c.delayed_cap
  red_cap := c.red_cap
  extend_cap := c.extend_cap
  scratch_cap := c.scratch_cap
  hbva := by have := c.hbva; omega
  hmv := Nat.lt_of_le_of_lt hle c.hmv
  hmaxv := c.hmaxv
  hnc := c.hnc
  harena := c.harena
  hwcap := c.hwcap
  hdel := c.hdel
  hred := c.hred
  hext := c.hext
  hscr := c.hscr
  havail_fit := c.havail_fit
  hsize := c.hsize

theorem FullCfgCompat.shrinkMv (c : FullCfg) (mv' : Nat) (hle : mv' ≤ c.mv) :
    FullCfgCompat c (fullCfgShrinkMv c mv' hle) :=
  ⟨rfl, rfl, hle, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FullLitMarksClear.of_compat {c c' : FullCfg} {s : FullState}
    (hc : FullCfgCompat c c') (h : FullLitMarksClear c s) : FullLitMarksClear c' s :=
  ⟨fun v hv => h.1 v (hc.max_vars ▸ hv), fun l hl => h.2 l (hc.max_vars ▸ hl)⟩

theorem FullExtScratchOk.of_compat {c c' : FullCfg} {s s' : FullState}
    (hc : FullCfgCompat c c') (h : FullExtScratchOk c s) (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullExtScratchOk c' s' := by
  refine ⟨FullLastLearnedWf.of_refs_subset h.1 hpres.1 hsub, ?_⟩
  rw [hc.extend_cap, hpres.2]; exact h.2

/-- Intermediate heap predicate between `h->d.mv = ncv` and `h->bva_cap = h->max_vars - ncv`. -/
@[expose] def FullMemShrinkMid (c : FullCfg) (mv' : BitVec 64) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr mv' (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

private theorem hdrTailWords_set94 (c : FullCfg) (s : FullState) (mv' : Nat) (hle : mv' ≤ c.mv) :
    (hdrTailWords c s).set 94 (BitVec.ofNat 64 (c.max_vars - mv')) =
      hdrTailWords (fullCfgShrinkMv c mv' hle) s := by
  simp only [hdrTailWords, HdrWordField.tailChunk0, HdrWordField.tailChunk1,
    HdrWordField.tailChunk2, HdrWordField.tailChunk3, List.cons_append, List.nil_append,
    List.set_cons_succ, List.set_cons_zero]
  rfl

private theorem fullRest_shrinkMv (c : FullCfg) (s : FullState) (mv' : Nat) (hle : mv' ≤ c.mv) :
    FullCoreArrays (fullCfgShrinkMv c mv' hle) s.core = FullCoreArrays c s.core ∧
    FullScratchArrays (fullCfgShrinkMv c mv' hle) s.scratch = FullScratchArrays c s.scratch ∧
    (fullCfgShrinkMv c mv' hle).pad = c.pad :=
  ⟨rfl, rfl, rfl⟩

theorem full_store_mv_mid {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (mv' : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 c.hdr ∧
      (FullMemShrinkMid c mv' s ⋆ R) (storeMem m i64 c.hdr mv') := by
  have h1 : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      s.core.d_cur s.core.d_val ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMem at hm; ecancel
  obtain ⟨hok, hst⟩ := store_dimacs_mv mv' h1
  refine ⟨hok, ?_⟩
  unfold FullMemShrinkMid; ecancel

theorem full_load_max_vars_mid {c : FullCfg} {mv' : BitVec 64} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemShrinkMid c mv' s ⋆ R) m) :
    loadVal m i64 (c.hdr + 768) = some (BitVec.ofNat 64 c.max_vars) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr mv' (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemShrinkMid at hm; ecancel
  have hget := loadVal_array64 (i := 92) (by rw [hdrTailWords_length]; decide) h1
  rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 92) = 768 by decide] at hget
  have helem : (hdrTailWords c s)[92]'(by rw [hdrTailWords_length]; decide) =
      BitVec.ofNat 64 c.max_vars := rfl
  simpa only [helem] using hget

theorem full_store_bva_mid {c : FullCfg} {mv' : Nat} (hle : mv' ≤ c.mv) {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMemShrinkMid c (BitVec.ofNat 64 mv') s ⋆ R) m) :
    storeOk m i64 (c.hdr + 784) ∧
      (FullMem (fullCfgShrinkMv c mv' hle) s ⋆ R)
        (storeMem m i64 (c.hdr + 784) (BitVec.ofNat 64 (c.max_vars - mv'))) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 mv') (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemShrinkMid at hm; ecancel
  obtain ⟨hok, hst⟩ := store_array64 (i := 94) (BitVec.ofNat 64 (c.max_vars - mv'))
    (by rw [hdrTailWords_length]; decide) h1
  have hptr : c.hdr + 32 + BitVec.ofNat 64 (8 * 94) = c.hdr + 784 := by
    rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 94) = 784 by decide]
  rw [hptr] at hok hst
  rw [hdrTailWords_set94 c s mv' hle] at hst
  have ⟨hc1, hc2, hc3⟩ := fullRest_shrinkMv c s mv' hle
  refine ⟨hok, ?_⟩
  unfold FullMem
  rw [hc1, hc2, hc3]
  change (dimacsState (fullCfgShrinkMv c mv' hle).hdr
      (BitVec.ofNat 64 (fullCfgShrinkMv c mv' hle).mv)
      (BitVec.ofNat 64 (fullCfgShrinkMv c mv' hle).nc) s.core.d_cur s.core.d_val ⋆
    array64 ((fullCfgShrinkMv c mv' hle).hdr + 32)
      (hdrTailWords (fullCfgShrinkMv c mv' hle) s) ⋆
    FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R) _
  ecancel

end LeanQbe.T.Examples.Kissat.Proof.Spec
