/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBva
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof2
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVA Proofs — Part 0 (`Specs, Dynamic Matrix Invariant & 7 Helper/Picker Proofs`)

M1-clean UNSAT-only specifications and parametric `Func.wp` proofs (`public section`,
`0` axioms, `0` placeholders, `XPost`-polymorphic) for
`FullFidelityBva`:
1. Dynamic scratch-scaled packed matrix invariant `FidBvaMatrixInv` (`fidStepsCap`) and
   canonical/internal specifications for all `13` functions of `FullFidelityBva`.
2. Parametric `(Γ : Env)` WP proofs for the `6` additive helpers plus zero-hop `pick_cand`:
   - `full_bva_steps_cap_fid_wp` (`fidBvaStepsCapSpec`)
   - `full_bva_clines_fid_wp` (`fidBvaClinesSpec`)
   - `full_fheap_up_fid_wp` (`fidFheapUpSpec`)
   - `full_fheap_down_fid_wp` (`fidFheapDownSpec`)
   - `full_bva_count_lit_deg_fid_wp` (`fidBvaCountLitDegSpec`)
   - `full_bva_connect_clauses_fid_wp` (`fidBvaConnectClausesSpec`, `GAP-BVA-02` peeling)
   - `full_bva_pick_cand_fid_wp` (canonical `FullBvaHeap.fullBvaPickCandSpec`).
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Dynamic Scratch-Scaled Matrix Invariant & Specifications -/

/-- Dynamic factoring step capacity chosen from `h->scratch_cap` (`GAP-BVA-01`). -/
@[expose] def fidStepsCap (cap : Nat) : Nat :=
  if 8192 ≤ cap then 256
  else if 1024 ≤ cap then 64
  else if 256 ≤ cap then 32
  else if 64 ≤ cap then 8
  else 0

theorem fidStepsCap_mul4_le (cap : Nat) : 4 * fidStepsCap cap ≤ cap := by
  unfold fidStepsCap; repeat (first | omega | split)

theorem fidStepsCap_le_256 (cap : Nat) : fidStepsCap cap ≤ 256 := by
  unfold fidStepsCap; repeat (first | omega | split)

theorem fidStepsCap_pos_iff (cap : Nat) : 0 < fidStepsCap cap ↔ 64 ≤ cap := by
  unfold fidStepsCap; repeat (first | omega | split)

/-- Soundness invariant for one entry `w` in a Fidelity BVA row with factor literal `fr`:
either a binary watch `PW_BIN_FLAG | q` with residue `[q]`, or a live irredundant size `3..5`
arena clause ref containing `fr` with residue `(lits w).filter (· != fr)`. -/
@[expose] def FidBvaRowEntryOk (F_cur : List (List Nat)) (s : FullState) (fr : Nat) (w : BitVec 32)
    (res : List Nat) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    let q := (w &&& 0x7FFFFFFF#32).toNat
    q < 2 * s.core.cur_vars ∧ res = [q] ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [fr, q])
  else
    w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false ∧
    3 ≤ fullArenaClauseSize s w.toNat ∧ fullArenaClauseSize s w.toNat ≤ 5 ∧
    fr ∈ fullArenaClauseLits s w.toNat ∧
    res.Perm ((fullArenaClauseLits s w.toNat).filter (· != fr)) ∧
    (fullArenaClauseLits s w.toNat).Perm (fr :: res)

/-- Complete inductive invariant for the dynamic packed Fidelity BVA matrix over steps `0 ..< step`
inside `scratch_buf[0 .. bump)` (`4 * sc ≤ bump ≤ c.scratch_cap`, `sc = fidStepsCap c.scratch_cap`):
header stores `factors[0..sc)`, `row_off[sc..2*sc)`, `row_len[2*sc..3*sc)`, `par_off[3*sc..4*sc)`,
and packed rows/parents live disjointly in `[4*sc .. bump)`. -/
@[expose] def FidBvaMatrixInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (step bump : Nat) : Prop :=
  let sc := fidStepsCap c.scratch_cap
  let sb := s.scratch.scratch_buf
  0 < sc ∧ 1 ≤ step ∧ step ≤ sc ∧ 4 * sc ≤ bump ∧ bump ≤ c.scratch_cap ∧
  (∀ r < step,
    let fr := (sb[r]?.getD 0#32).toNat
    let ro := (sb[sc + r]?.getD 0#32).toNat
    let qn := (sb[2 * sc + r]?.getD 0#32).toNat
    let po := (sb[3 * sc + r]?.getD 0#32).toNat
    fr < 2 * s.core.cur_vars ∧ 4 * sc ≤ ro ∧ 2 ≤ qn ∧ ro + qn ≤ bump ∧
    (0 < r → 4 * sc ≤ po ∧ po + qn ≤ bump) ∧
    ∀ m < qn, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s fr (sb[ro + m]?.getD 0#32) res ∧
      (∀ t ≤ r,
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((sb[t]?.getD 0#32).toNat :: res))) ∧
      (0 < r →
        let pi := (sb[po + m]?.getD 0#32).toNat
        pi < (sb[2 * sc + (r - 1)]?.getD 0#32).toNat ∧
        FidBvaRowEntryOk F_cur s (sb[r - 1]?.getD 0#32).toNat
          (sb[(sb[sc + (r - 1)]?.getD 0#32).toNat + pi]?.getD 0#32) res))

/-- Spec for `full_bva_steps_cap_fid`: pure computation of `fidStepsCap cap.toNat`. -/
@[expose] def fidBvaStepsCapSpec : Spec [i64] [i32] := fun (cap, ()) m Q _ =>
  Q (BitVec.ofNat 32 (fidStepsCap cap.toNat), ()) m

/-- Spec for `full_bva_clines_fid`: pure cache-line count (memory unchanged). -/
@[expose] def fidBvaClinesSpec : Spec [i64] [i64] := fun (_n, ()) m Q _ =>
  ∀ r : BitVec 64, Q (r, ()) m

/-- Spec for `full_fheap_up_fid`: exact clause-count `deg` array max-heap sift-up. -/
@[expose] def fidFheapUpSpec : Spec [i64, i64, i64, i32] [] :=
  fun (hp_ptr, ps_ptr, deg_ptr, p, ()) m Q _ =>
    ∃ (nlits : Nat) (hp ps deg : List (BitVec 32)) (R : Mem 64 → Prop),
      nlits ≤ hp.length ∧ nlits ≤ ps.length ∧ nlits ≤ deg.length ∧ nlits < 2 ^ 30 ∧
      p.toNat < nlits ∧
      (∀ i ≤ p.toNat, (hp[i]?.getD 0#32).toNat < nlits) ∧
      (array (t := i32) hp_ptr hp ⋆ array (t := i32) ps_ptr ps ⋆
        array (t := i32) deg_ptr deg ⋆ R) m ∧
      ∀ hp' ps' m',
        hp'.length = hp.length → ps'.length = ps.length →
        (∀ i ≤ p.toNat, ∃ j ≤ p.toNat, hp'[i]? = hp[j]?) →
        (∀ i, p.toNat < i → hp'[i]? = hp[i]?) →
        (array (t := i32) hp_ptr hp' ⋆ array (t := i32) ps_ptr ps' ⋆
          array (t := i32) deg_ptr deg ⋆ R) m' → Q () m'

/-- Spec for `full_fheap_down_fid`: exact clause-count `deg` array max-heap sift-down. -/
@[expose] def fidFheapDownSpec : Spec [i64, i64, i64, i32, i32] [] :=
  fun (hp_ptr, ps_ptr, deg_ptr, p, n, ()) m Q _ =>
    ∃ (nlits : Nat) (hp ps deg : List (BitVec 32)) (R : Mem 64 → Prop),
      nlits ≤ hp.length ∧ nlits ≤ ps.length ∧ nlits ≤ deg.length ∧ nlits < 2 ^ 30 ∧
      p.toNat < n.toNat ∧ n.toNat ≤ nlits ∧
      (∀ i < n.toNat, (hp[i]?.getD 0#32).toNat < nlits) ∧
      (array (t := i32) hp_ptr hp ⋆ array (t := i32) ps_ptr ps ⋆
        array (t := i32) deg_ptr deg ⋆ R) m ∧
      ∀ hp' ps' m',
        hp'.length = hp.length → ps'.length = ps.length →
        (∀ i < n.toNat, ∃ j < n.toNat, hp'[i]? = hp[j]?) →
        (∀ i, n.toNat ≤ i → hp'[i]? = hp[i]?) →
        (array (t := i32) hp_ptr hp' ⋆ array (t := i32) ps_ptr ps' ⋆
          array (t := i32) deg_ptr deg ⋆ R) m' → Q () m'

/-- Spec for `full_bva_count_lit_deg_fid`: pure read-only count of dense watches on `lit`. -/
@[expose] def fidBvaCountLitDegSpec : Spec [i64, i32] [i32] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ lit.toNat < 2 * s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 32, Q (r, ()) m

/-- Spec for `full_bva_connect_clauses_fid` (`GAP-BVA-02` candidate peeling + exact `deg`):
preserves `FullDenseInvW`, `cur_vars`, `fuel`, `arena`, `arena_len`, `scratch_buf`. -/
@[expose] def fidBvaConnectClausesSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Spec for `full_bva_match_large_bva_fid`: read-only bit-25 (`PH_BVA_Q`) clause match. -/
@[expose] def fidBvaMatchLargeBvaSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, cur_cr, next_lit, d_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R_mem : Mem 64 → Prop) (R_set : List Nat),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      cur_cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cur_cr.toNat = false ∧
      d_ref.toNat ∈ fullArenaClauseRefs s ∧ R_set.Nodup ∧ (∀ x ∈ R_set, x < 2 * s.core.cur_vars) ∧
      fullArenaClauseSize s cur_cr.toNat = R_set.length + 1 ∧
      (∀ l < 2 * s.core.cur_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ R_set) ∧
      (FullMem c s ⋆ R_mem) m ∧ ∀ ok : Bool, (ok = true →
          fullArenaClauseGarb s d_ref.toNat = false ∧
          (fullArenaHdr s d_ref.toNat &&& 0x02000000#32) = 0#32 ∧
          fullArenaClauseSize s d_ref.toNat = fullArenaClauseSize s cur_cr.toNat ∧
          next_lit.toNat ∈ fullArenaClauseLits s d_ref.toNat ∧
          (fullArenaClauseLits s d_ref.toNat).Perm (next_lit.toNat :: R_set) ∧
          ((fullArenaClauseLits s d_ref.toNat).filter (· != next_lit.toNat)).Perm R_set ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (next_lit.toNat :: R_set))) →
        Q (ok, ()) m

/-- Spec for `full_bva_scan_cands` (`GAP-BVA-01/03`: dynamic row length + `ant_sz` tick budget). -/
@[expose] def fidBvaScanCandsSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, row_off, cur_qn, init_lits, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      init_lits.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      row_off.toNat + cur_qn.toNat ≤ c.scratch_cap ∧
      (∀ qi < cur_qn.toNat,
        let w := s.scratch.scratch_buf[row_off.toNat + qi]?.getD 0#32
        if (w &&& 0x80000000#32) ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars
        else w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ncntd : BitVec 32) wsort' ws1' ws2' ant' m',
        let s' : FullState :=
          { s with scratch :=
            { s.scratch with wsort := wsort', work_stk1 := ws1', work_stk2 := ws2',
                             ant_sz := ant' } }
        s'.LengthsOk c →
        ncntd.toNat ≤ init_lits.toNat →
        (∀ i < ncntd.toNat, (ws1'[i]?.getD 0#32).toNat < init_lits.toNat) →
        (FullMem c s' ⋆ R) m' → Q (ncntd, ()) m'

/-- Spec for `full_bva_filter_row` (`GAP-BVA-01/03`: packed dynamic matrix + `ant_sz` ticks). -/
@[expose] def fidBvaFilterRowSpec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, row_off, nrow_off, par_off, cur_qn, best_lit, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop) (step bump : Nat),
      let sc := fidStepsCap c.scratch_cap
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      0 < sc ∧ 1 ≤ step ∧ step < sc ∧
      row_off.toNat = (s.scratch.scratch_buf[sc + (step - 1)]?.getD 0#32).toNat ∧
      cur_qn.toNat = (s.scratch.scratch_buf[2 * sc + (step - 1)]?.getD 0#32).toNat ∧
      nrow_off.toNat = bump ∧ nrow_off.toNat ≤ par_off.toNat ∧
      par_off.toNat + (par_off.toNat - nrow_off.toNat) ≤ c.scratch_cap ∧
      best_lit.toNat < 2 * s.core.cur_vars ∧
      FidBvaMatrixInv c F_cur s step bump ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      (∀ r < step, (s.core.lit_mark[(s.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&&
        1#8) ≠ 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (new_qn : BitVec 32) sb' ant' m',
        let s' : FullState :=
          { s with scratch := { s.scratch with scratch_buf := sb', ant_sz := ant' } }
        let max_new := par_off.toNat - nrow_off.toNat
        s'.LengthsOk c → new_qn.toNat ≤ max_new →
        (∀ idx < c.scratch_cap,
          ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
          ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
          sb'[idx]? = s.scratch.scratch_buf[idx]?) →
        (∀ nm < new_qn.toNat,
          let pi := (sb'[par_off.toNat + nm]?.getD 0#32).toNat
          pi < cur_qn.toNat ∧
          ∃ res : List Nat,
            (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
            FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
              (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res ∧
            FidBvaRowEntryOk F_cur s best_lit.toNat (sb'[nrow_off.toNat + nm]?.getD 0#32) res ∧
            (∀ t < step, (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))) →
        (FullMem c s' ⋆ R) m' → Q (new_qn, ()) m'

/-- Spec for `full_bva_commit`: commits dynamic packed `FidBvaMatrixInv`, strictly incrementing
`cur_vars` on `ok = true`. -/
@[expose] def fidBvaCommitSpec : Spec [i64, i32] [.bool] := fun (h, best_k, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (bump : Nat),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
    1 ≤ best_k.toNat ∧ best_k.toNat < fidStepsCap c.scratch_cap ∧
    FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Spec for `full_bva_try_lit`: strengthens `fullBvaTryLitHeapSpec` with strict `cur_vars` growth
on `ok = true` so `full_factor` terminates unconditionally under arbitrary tick budgets. -/
@[expose] def fidBvaTryLitSpec : Spec [i64, i32, i64] [.bool] := fun (h, f0, _init_cv, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ f0.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fidBvaTryLitSpec_weaken :
    ∀ a m Q X, fullBvaTryLitHeapSpec a m Q X → fidBvaTryLitSpec a m Q X := by
  rintro ⟨h, f0, init_cv, ⟨⟩⟩ m Q X ⟨c, F0, s, R, hh, hinv, hf0, hm, hQ⟩
  exact ⟨c, F0, s, R, hh, hinv, hf0, hm, fun ok s' m' hi hcv _ hfu htm htr hm' =>
    hQ ok s' m' hi hcv hfu htm htr hm'⟩

/-! ## 2. Shared Congruence & Dynamic-Matrix Preservation Helpers -/

theorem fidBvaRowEntryOk_congr {F_cur : List (List Nat)} {s s' : FullState}
    {fr : Nat} {w : BitVec 32} {res : List Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : FidBvaRowEntryOk F_cur s fr w res) : FidBvaRowEntryOk F_cur s' fr w res := by
  unfold FidBvaRowEntryOk at h ⊢
  by_cases hbin : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hbin] at h ⊢; rwa [hcv]
  · rw [ite_eq_right hbin] at h ⊢
    simp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseSize,
      fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
      fullArenaClauseSizeCore, fullArenaClauseLitsCore, fullArenaHdrCore, har, hal] at h ⊢
    exact h

theorem fidBvaMatrixInv_congr {c : FullCfg} {F_cur : List (List Nat)} {s s' : FullState}
    {step bump : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (h : FidBvaMatrixInv c F_cur s step bump) : FidBvaMatrixInv c F_cur s' step bump := by
  rcases h with ⟨hsc, hs1, hss, hb1, hb2, hrows⟩
  refine ⟨hsc, hs1, hss, hb1, hb2, fun r hr => ?_⟩
  rcases hrows r hr with ⟨hfr, hro1, hq2, hro2, hpo, hm⟩
  refine ⟨by rw [hsb, hcv]; exact hfr, by rw [hsb]; exact hro1, by rw [hsb]; exact hq2,
    by rw [hsb]; exact hro2, by intro hr0; rw [hsb]; exact hpo hr0, fun m hm_lt => ?_⟩
  rw [hsb] at hm_lt
  rcases hm m hm_lt with ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩
  refine ⟨res, fun x hx => by rw [hcv]; exact hres_lt x hx, hres_nd, ?_, ?_, ?_⟩
  · rw [hsb]; exact fidBvaRowEntryOk_congr hcv har hal hok
  · intro t ht; rw [hsb]; exact hent t ht
  · intro hr0; rw [hsb]; obtain ⟨hpi, hpok⟩ := hpar hr0
    exact ⟨hpi, fidBvaRowEntryOk_congr hcv har hal hpok⟩

theorem fid_bv32_bin_flag_zero_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x80000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
    show (0#32).toNat = 0 from rfl]
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
  by_cases hk : k = 31
  · subst hk; simp [Nat.testBit_lt_two_pow h]
  · simp [Ne.symm hk]

theorem fid_bv32_garb_zero_of_and_480000 {x : BitVec 32}
    (h : (x &&& 0x00480000#32) = 0#32) : (x &&& 0x00080000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00080000#32) h
  rw [BitVec.and_assoc, show (0x00480000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

theorem fid_bv64_32 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_trans (BitVec.isLt x) (by decide))

private theorem fid_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fid_bv64_add2 {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + 2#64).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt h]

private theorem fid_bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fid_bv64_trunc32 {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

private theorem fid_bv64_add3_u32 {p : BitVec 64} {k : BitVec 32}
    (h : p.toNat + 3 + k.toNat < 2 ^ 64) :
    (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, fid_bv64_32,
    show (3#64 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : p.toNat + 3 < 2 ^ 64), Nat.mod_eq_of_lt h]

private theorem fid_bv32_ne_sent {x : BitVec 32} (h : x.toNat < 2 ^ 31) : x ≠ 0xFFFFFFFF#32 :=
  fun he => by have := congrArg BitVec.toNat he; simp at this; omega

/-! ## 3. Pure Leaf Proofs: `full_bva_steps_cap_fid`, `full_bva_clines_fid` -/

theorem full_bva_steps_cap_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBvaStepsCapSpec a m Q X → Func.wp Γ full_bva_steps_cap_fid_body a m Q X := by
  rintro ⟨cap, ⟨⟩⟩ m Q X hQ
  unfold fidBvaStepsCapSpec at hQ
  unfold Func.wp full_bva_steps_cap_fid_body
  c0_hsteps
  · have h1 : 8192 ≤ cap.toNat := by c0_bound
    simpa [fidStepsCap, h1] using hQ
  · have h1 : ¬ (8192 ≤ cap.toNat) := by c0_bound
    have h2 : 1024 ≤ cap.toNat := by c0_bound
    simpa [fidStepsCap, h1, h2] using hQ
  · have h1 : ¬ (8192 ≤ cap.toNat) := by c0_bound
    have h2 : ¬ (1024 ≤ cap.toNat) := by c0_bound
    have h3 : 256 ≤ cap.toNat := by c0_bound
    simpa [fidStepsCap, h1, h2, h3] using hQ
  · have h1 : ¬ (8192 ≤ cap.toNat) := by c0_bound
    have h2 : ¬ (1024 ≤ cap.toNat) := by c0_bound
    have h3 : ¬ (256 ≤ cap.toNat) := by c0_bound
    have h4 : 64 ≤ cap.toNat := by c0_bound
    simpa [fidStepsCap, h1, h2, h3, h4] using hQ
  · have h1 : ¬ (8192 ≤ cap.toNat) := by c0_bound
    have h2 : ¬ (1024 ≤ cap.toNat) := by c0_bound
    have h3 : ¬ (256 ≤ cap.toNat) := by c0_bound
    have h4 : ¬ (64 ≤ cap.toNat) := by c0_bound
    simpa [fidStepsCap, h1, h2, h3, h4] using hQ

theorem full_bva_clines_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBvaClinesSpec a m Q X → Func.wp Γ full_bva_clines_fid_body a m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_bva_clines_fid_body
  c0_hsteps <;> exact hQ _

/-! ## 4. Exact-Degree Heap Sift Proofs: `full_fheap_up_fid`, `full_fheap_down_fid` -/

private theorem bv32_sub1_ushr1 {p : BitVec 32} (h : 0 < p.toNat) :
    ((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat = (p.toNat - 1) / 2 := by
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]; omega

private theorem bv32_shl1_add1 {p : BitVec 32} (h : p.toNat < 2 ^ 30) :
    ((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat = 2 * p.toNat + 1 := by
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem bv32_shl1_add2 {p : BitVec 32} (h : p.toNat < 2 ^ 30) :
    (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat = 2 * p.toNat + 2 := by
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem full_fheap_up_fid_wp (Γ : Env) :
    ∀ a m Q X, fidFheapUpSpec a m Q X → Func.wp Γ full_fheap_up_fid_body a m Q X := by
  rintro ⟨hp_ptr, ps_ptr, deg_ptr, p0, ⟨⟩⟩ m Q X
    ⟨nlits, hp0, ps0, deg, R, hhp_len, hps_len, hdeg_len, hnl_lt, hp0_lt, hhp0_ok, hm, hQ⟩
  have hi32 : i32.bytes = 4 := rfl
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := fid_bv64_32
  have hl0_lt : (hp0[p0.toNat]'(by omega)).toNat < nlits := by
    have := hhp0_ok p0.toNat (Nat.le_refl _)
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  unfold Func.wp full_fheap_up_fid_body
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun st => st.1)
    (fun ⟨pf, hpf, psf⟩ mf =>
      pf.toNat ≤ p0.toNat ∧ hpf.length = hp0.length ∧ psf.length = ps0.length ∧
      (∀ i ≤ p0.toNat, ∃ j ≤ p0.toNat, hpf[i]? = hp0[j]?) ∧
      (∀ i, p0.toNat < i → hpf[i]? = hp0[i]?) ∧
      (array (t := i32) hp_ptr hpf ⋆ array (t := i32) ps_ptr psf ⋆
        array (t := i32) deg_ptr deg ⋆ R) mf)
    (fun _ ⟨pf, hpf, psf⟩ mf ⟨hpf_le, hhpf_len, hpsf_len, hsubf, houtf, hmf⟩ => ?_)
    (fun Jend hJend => ?_)
  · clear m hm; c0_hsteps
    let hpf' := hpf.set pf.toNat (hp0[p0.toNat]'(by omega))
    let psf' := psf.set (hp0[p0.toNat]'(by omega)).toNat pf
    have hmem : (array (t := i32) hp_ptr hpf' ⋆ array (t := i32) ps_ptr psf' ⋆
        array (t := i32) deg_ptr deg ⋆ R) m := by
      dsimp only [hpf', psf']; simp only [hset] at hm; exact sep_ac hm
    refine hQ hpf' psf' _ (by simp [hpf', hhpf_len]) (by simp [psf', hpsf_len])
      (fun i hi => ?_) (fun i hi => ?_) hmem
    · dsimp only [hpf']; by_cases hie : i = pf.toNat
      · subst hie; refine ⟨p0.toNat, Nat.le_refl _, ?_⟩
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsubf i hi
    · dsimp only [hpf']; rw [List.getElem?_set_ne (by omega)]; exact houtf i hi
  · refine wp_loop_inv
      (fun (p, ()) ml => ∃ hpl psl,
        p.toNat ≤ p0.toNat ∧ hpl.length = hp0.length ∧ psl.length = ps0.length ∧
        (∀ i ≤ p0.toNat, ∃ j ≤ p0.toNat, hpl[i]? = hp0[j]?) ∧
        (∀ i, p0.toNat < i → hpl[i]? = hp0[i]?) ∧
        (array (t := i32) hp_ptr hpl ⋆ array (t := i32) ps_ptr psl ⋆
          array (t := i32) deg_ptr deg ⋆ R) ml)
      (fun (p, ()) _ => p.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (p0, ()) m ⟨hp0, ps0, Nat.le_refl _, rfl, rfl,
          fun i hi => ⟨i, hi, rfl⟩, fun _ _ => rfl, hm⟩)
      (fun J (p, ()) ml ⟨hpl, psl, hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩ ih => ?_)
    clear m hm
    c0_hsteps
    · have hp_pos : 0 < p.toNat := by c0_bound
      have hpp_nat : ((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat = (p.toNat - 1) / 2 :=
        bv32_sub1_ushr1 hp_pos
      have hpp_lt : ((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat < p.toNat := by omega
      have hpl_ok :
          (hpl[((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat]'(by omega)).toNat < nlits := by
        obtain ⟨j, hj, heq⟩ := hsub ((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat (by omega)
        have h1 := hhp0_ok j hj
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
      have hpl_ok_sw :
          (hpl[(BitVec.setWidth 64 ((p - (1 : BitVec 32)) >>> (1 : BitVec 32))).toNat]'(by
            simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hpl_ok
      c0_hsteps
      · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩
      · let par := (p - (1 : BitVec 32)) >>> (1 : BitVec 32)
        have hpar_nat : par.toNat = (p.toNat - 1) / 2 := hpp_nat
        let hpl' := hpl.set p.toNat (hpl[par.toNat]'(by omega))
        let psl' := psl.set (hpl[par.toNat]'(by omega)).toNat p
        have hmem : (array (t := i32) hp_ptr hpl' ⋆ array (t := i32) ps_ptr psl' ⋆
            array (t := i32) deg_ptr deg ⋆ R) m := by
          dsimp only [hpl', psl', par]; simp only [hset] at hm; exact sep_ac hm
        refine ih (par, ()) _ (by dsimp only; omega)
          ⟨hpl', psl', by omega, by simp [hpl', hhpl_len], by simp [psl', hpsl_len],
           fun i hi => ?_,
           fun i hi => by
             dsimp only [hpl']; rw [List.getElem?_set_ne (by omega)]; exact hout i hi,
           hmem⟩
        dsimp only [hpl']
        by_cases hie : i = p.toNat
        · subst hie
          obtain ⟨j, hj, heq⟩ := hsub par.toNat (by omega)
          refine ⟨j, hj, ?_⟩
          rw [List.getElem?_set_self (by omega), ← heq, List.getElem?_eq_getElem (by omega)]
        · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsub i hi
    · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩

theorem full_fheap_down_fid_wp (Γ : Env) :
    ∀ a m Q X, fidFheapDownSpec a m Q X → Func.wp Γ full_fheap_down_fid_body a m Q X := by
  rintro ⟨hp_ptr, ps_ptr, deg_ptr, p0, n, ⟨⟩⟩ m Q X
    ⟨nlits, hp0, ps0, deg, R, hhp_len, hps_len, hdeg_len, hnl_lt, hp0_lt, hn_le, hhp0_ok, hm, hQ⟩
  have hi32 : i32.bytes = 4 := rfl
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := fid_bv64_32
  have hl0_lt : (hp0[p0.toNat]'(by omega)).toNat < nlits := by
    have := hhp0_ok p0.toNat hp0_lt
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  unfold Func.wp full_fheap_down_fid_body
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun st => st.1)
    (fun ⟨pf, hpf, psf⟩ mf =>
      pf.toNat < n.toNat ∧ hpf.length = hp0.length ∧ psf.length = ps0.length ∧
      (∀ i < n.toNat, ∃ j < n.toNat, hpf[i]? = hp0[j]?) ∧
      (∀ i, n.toNat ≤ i → hpf[i]? = hp0[i]?) ∧
      (array (t := i32) hp_ptr hpf ⋆ array (t := i32) ps_ptr psf ⋆
        array (t := i32) deg_ptr deg ⋆ R) mf)
    (fun _ ⟨pf, hpf, psf⟩ mf ⟨hpf_lt, hhpf_len, hpsf_len, hsubf, houtf, hmf⟩ => ?_)
    (fun Jend hJend => ?_)
  · clear m hm; c0_hsteps
    let hpf' := hpf.set pf.toNat (hp0[p0.toNat]'(by omega))
    let psf' := psf.set (hp0[p0.toNat]'(by omega)).toNat pf
    have hmem : (array (t := i32) hp_ptr hpf' ⋆ array (t := i32) ps_ptr psf' ⋆
        array (t := i32) deg_ptr deg ⋆ R) m := by
      dsimp only [hpf', psf']; simp only [hset] at hm; exact sep_ac hm
    refine hQ hpf' psf' _ (by simp [hpf', hhpf_len]) (by simp [psf', hpsf_len])
      (fun i hi => ?_) (fun i hi => ?_) hmem
    · dsimp only [hpf']; by_cases hie : i = pf.toNat
      · subst hie; refine ⟨p0.toNat, hp0_lt, ?_⟩
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsubf i hi
    · dsimp only [hpf']; rw [List.getElem?_set_ne (by omega)]; exact houtf i hi
  · refine wp_loop_inv
      (fun (p, ()) ml => ∃ hpl psl,
        p.toNat < n.toNat ∧ hpl.length = hp0.length ∧ psl.length = ps0.length ∧
        (∀ i < n.toNat, ∃ j < n.toNat, hpl[i]? = hp0[j]?) ∧
        (∀ i, n.toNat ≤ i → hpl[i]? = hp0[i]?) ∧
        (array (t := i32) hp_ptr hpl ⋆ array (t := i32) ps_ptr psl ⋆
          array (t := i32) deg_ptr deg ⋆ R) ml)
      (fun (p, ()) _ => n.toNat - p.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (p0, ()) m ⟨hp0, ps0, hp0_lt, rfl, rfl,
          fun i hi => ⟨i, hi, rfl⟩, fun _ _ => rfl, hm⟩)
      (fun J (p, ()) ml ⟨hpl, psl, hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩ ih => ?_)
    clear m hm
    have hlc_nat : ((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat = 2 * p.toNat + 1 :=
      bv32_shl1_add1 (by omega)
    c0_hsteps_nogrp
    · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩
    · have hlc_lt : ((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat < n.toNat := by c0_bound
      have hcl_ok :
          (hpl[((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat]'(by omega)).toNat < nlits := by
        obtain ⟨j, hj, heq⟩ := hsub ((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat hlc_lt
        have h1 := hhp0_ok j hj
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
      have hcl_ok_sw :
          (hpl[(BitVec.setWidth 64 ((p <<< (1 : BitVec 32)) + (1 : BitVec 32))).toNat]'(by
            simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hcl_ok
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
        (fun ⟨best, bd⟩ => (best, bd, ()))
        (fun ⟨best, _⟩ mf =>
          p.toNat < best.toNat ∧ best.toNat < n.toNat ∧ ml = mf)
        (fun _ ⟨best, bd⟩ mf ⟨hgt_p, hbest_lt, hmf⟩ => ?_)
        (fun Jc hJc => ?_)
      · rcases hmf with rfl
        have hbl_ok : (hpl[best.toNat]'(by omega)).toNat < nlits := by
          obtain ⟨j, hj, heq⟩ := hsub best.toNat hbest_lt
          have h1 := hhp0_ok j hj
          rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
        c0_hsteps
        · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩
        · let hpl' := hpl.set p.toNat (hpl[best.toNat]'(by omega))
          let psl' := psl.set (hpl[best.toNat]'(by omega)).toNat p
          have hmem : (array (t := i32) hp_ptr hpl' ⋆ array (t := i32) ps_ptr psl' ⋆
              array (t := i32) deg_ptr deg ⋆ R) m := by
            dsimp only [hpl', psl']; simp only [hset] at hm; exact sep_ac hm
          refine ih (best, ()) _ (by dsimp only; omega)
            ⟨hpl', psl', hbest_lt, by simp [hpl', hhpl_len], by simp [psl', hpsl_len],
             fun i hi => ?_,
             fun i hi => by
               dsimp only [hpl']; rw [List.getElem?_set_ne (by omega)]; exact hout i hi,
             hmem⟩
          dsimp only [hpl']
          by_cases hie : i = p.toNat
          · subst hie
            obtain ⟨j, hj, heq⟩ := hsub best.toNat hbest_lt
            refine ⟨j, hj, ?_⟩
            rw [List.getElem?_set_self (by omega), ← heq, List.getElem?_eq_getElem (by omega)]
          · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsub i hi
      · c0_hsteps_nogrp
        · have hrc_nat :
              (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat =
                2 * p.toNat + 2 :=
            bv32_shl1_add2 (by omega)
          have hrc_lt :
              (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat < n.toNat := by
            c0_bound
          have hrl_ok :
              (hpl[(((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat]'(by
                omega)).toNat < nlits := by
            obtain ⟨j, hj, heq⟩ :=
              hsub (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat hrc_lt
            have h1 := hhp0_ok j hj
            rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
          have hrl_ok_sw :
              (hpl[(BitVec.setWidth 64 (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) +
                (1 : BitVec 32))).toNat]'(by simp only [hset]; omega)).toNat < nlits := by
            simp only [hset]; exact hrl_ok
          c0_hsteps
          · exact hJc ((((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)), _) ml
              ⟨by omega, hrc_lt, rfl⟩
          · exact hJc (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)), _) ml ⟨by omega, hlc_lt, rfl⟩
        · c0_hsteps
          exact hJc (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)), _) ml ⟨by omega, hlc_lt, rfl⟩
    · exact False.elim (Bool.noConfusion (by assumption))

/-! ## 5. Exact Clause-Count Degree Reader (`full_bva_count_lit_deg_fid`) -/

theorem full_bva_count_lit_deg_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Func.wp Γ full_bva_count_lit_deg_fid_body a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, hlit_lt, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hcl := hdw.1.core_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have hwl_le := hcl.wlen_le
  have hlay := (m6_denseWatchesInv_of_w hdw).layout
  have hwb := hlay.bounds lit.toNat hlit_lt
  have hlit2 : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat = 2 * lit.toNat := by c0_bound
  have hlit21 : ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat = 2 * lit.toNat + 1 := by
    c0_bound
  have hoff_eq :
      (s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(by omega)).toNat =
        fullWatchOffCore s.core lit.toNat := by
    unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (by simp only [hlit2])
  have hsz_eq :
      (s.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat]'(by omega)).toNat =
        fullWatchSizeCore s.core lit.toNat := by
    unfold fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (by simp only [hlit21])
  unfold Func.wp full_bva_count_lit_deg_fid_body
  c0_hsteps_nogrp
  let off_bv := BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(by
    omega))
  let sz_bv := BitVec.setWidth 64 (s.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
    1#64).toNat]'(by omega))
  let end_bv := off_bv + sz_bv
  have hend_nat : end_bv.toNat =
      fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat := by
    dsimp only [end_bv, off_bv, sz_bv]
    rw [BitVec.toNat_add, fid_bv64_32, fid_bv64_32, hoff_eq, hsz_eq]
    exact Nat.mod_eq_of_lt (by omega)
  refine wp_loop_inv
    (fun (p, _cnt, ()) ml => ml = m ∧ p.toNat ≤ end_bv.toNat)
    (fun (p, _, _) _ => end_bv.toNat - p.toNat)
    (fun J hJ => by
      c0_hsteps
      exact hJ (off_bv, 0#32, ()) m ⟨rfl, by
        dsimp only [off_bv]; rw [fid_bv64_32, hoff_eq, hend_nat]; omega⟩)
    (fun J (p, cnt, ()) ml ⟨hml, hp_le⟩ ih => ?_)
  rcases hml with rfl
  c0_hsteps_nogrp
  · have hp_lt : p.toNat < end_bv.toNat := by c0_bound
    have hp1 : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
    c0_hsteps
    · exact ih (p + 1#64, cnt + 1#32, ()) ml (by dsimp only; omega) ⟨rfl, by omega⟩
    · have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
      have hp1_lt : p.toNat + 1 < end_bv.toNat := by
        have h1' : (BitVec.toNat p + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have h2m : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
        have h21m : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
            2 * lit.toNat + 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have hoff' : s.core.wvec[2 * lit.toNat % 2 ^ 64].toNat =
            fullWatchOffCore s.core lit.toNat := by simpa only [hlit2, h2m] using hoff_eq
        have hsz' : s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat =
            fullWatchSizeCore s.core lit.toNat := by simpa only [hlit21, h21m] using hsz_eq
        rw [h1', hoff', hsz', Nat.mod_eq_of_lt (by omega)] at hc
        omega
      exact ih (p + 1#64 + 1#64, cnt + 1#32, ()) ml (by dsimp only; omega) ⟨rfl, by omega⟩
    · exact ih (p + 1#64, cnt, ()) ml (by dsimp only; omega) ⟨rfl, by omega⟩
  · c0_hsteps; exact hQ cnt

/-! ## 6. `GAP-BVA-02` Candidate Peeling & Reconnect (`full_bva_connect_clauses_fid`) -/

section ConnectClauses

private def ConnStateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 s : FullState) : Prop :=
  FullDenseInvW c F0 F_cur s ∧ s.core.cur_vars = s0.core.cur_vars ∧
  s.core.fuel = s0.core.fuel ∧ s.core.arena = s0.core.arena ∧
  s.core.arena_len = s0.core.arena_len ∧ s.scratch.scratch_buf = s0.scratch.scratch_buf

private theorem fullDenseInvW_set_scr_arrs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tm ws1 ws2 : List (BitVec 32)}
    (htm : tm.length = 2 * c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hws2 : ws2.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with tarjan_mark := tm, work_stk1 := ws1,
                                           work_stk2 := ws2 } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with
      tarjan_mark_len := htm, work_stk1_len := hws1, work_stk2_len := hws2 }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem fullDenseInvW_set_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {rp : List (BitVec 32)} (hrp : rp.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with repr := rp } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    h hrp h.1.core_ok.min_clr_len_arr h.1.core_ok.tmp_len_arr h.1.core_ok.flags_len
    h.1.core_ok.tmp_len_le h.1.scratch_ok rfl rfl

private theorem fullDenseInvW_set_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (oom' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := oom' } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m6_denseSlice_bin_other_lt {F_cur : List (List Nat)} {k : FullCoreState}
    {l off n p : Nat} (hdw : DenseWatchSliceOk F_cur k l off n)
    (hp : off ≤ p) (hplt : p < off + n)
    {w0 : BitVec 32} (hw : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars := by
  induction hdw with
  | empty => omega
  | @bin q rem w hq hflag _ hlt _ _ ih =>
    by_cases heq : p = q
    · subst heq; rw [hq] at hw; cases hw; exact hlt
    · exact ih (by omega) (by omega)
  | @occ q rem w cr hq hq1 hflag _ _ _ _ ih =>
    by_cases heq0 : p = q
    · subst heq0; rw [hq] at hw; cases hw; exact absurd hflag hbin
    · by_cases heq1 : p = q + 1
      · exfalso
        subst heq1
        rw [hq1] at hw; cases hw
        exact hbin (fid_bv32_bin_flag_zero_of_lt (by omega))
      · exact ih (by omega) (by omega)

private theorem fid_zero_mem_arenaRefs {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    cases hal : k.arena_len with
    | zero => omega
    | succ n =>
      rw [fullArenaScanRefs]
      have hle : 0 + 3 ≤ n + 1 := by omega
      simp [hle]

private theorem fid_conn_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sp sk : FullState} {p : BitVec 64} {k : BitVec 32}
    (hokp : ConnStateOk c F0 F_cur s0 sp) (hokk : ConnStateOk c F0 F_cur s0 sk)
    (hp_ref : p.toNat ∈ fullArenaClauseRefs sp) (hng : fullArenaClauseGarb sp p.toNat = false)
    (hk_lt : k.toNat < fullArenaClauseSizeCore sp.core p.toNat)
    (hidx : (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat)
    (hlt_ar : (p + 3#64 + BitVec.setWidth 64 k).toNat < sk.core.arena.length) :
    (sk.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hlt_ar).toNat < 2 * sk.core.cur_vars ∧
    (sk.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hlt_ar).toNat < 2 * c.max_vars ∧
    (BitVec.setWidth 64 (sk.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hlt_ar)).toNat <
      2 * c.max_vars := by
  have hwf := hokp.1.2.1.arena.refs_wf p.toNat hp_ref
  have har_l := hokp.1.1.core_ok.arena_len_arr
  have hal_l := hokp.1.1.core_ok.arena_len_le
  have hmem : (sp.core.arena[p.toNat + 3 + k.toNat]'(by omega)).toNat ∈
      fullArenaClauseLits sp p.toNat :=
    List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem hk_lt (by omega))
  have h1 := hokp.1.2.1.arena.lits_lt p.toNat hp_ref hng _ hmem
  have h2 : sk.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hlt_ar =
      sp.core.arena[p.toNat + 3 + k.toNat]'(by omega) := by
    simp only [hokk.2.2.2.1, hokp.2.2.2.1, hidx]
  have hcv_eq : sk.core.cur_vars = sp.core.cur_vars := hokk.2.1.trans hokp.2.1.symm
  have hcv_le := hokp.1.1.core_ok.cur_vars_le
  have hlt1 : (sk.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hlt_ar).toNat <
      2 * sk.core.cur_vars := by rw [h2, hcv_eq]; exact h1
  have hlt2 : (sk.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hlt_ar).toNat <
      2 * c.max_vars := by rw [h2]; omega
  exact ⟨hlt1, hlt2, by rw [fid_bv64_32]; exact hlt2⟩

private theorem connStateOk_set_scr_arrs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (h : ConnStateOk c F0 F_cur s0 s)
    {tm ws1 ws2 : List (BitVec 32)}
    (htm : tm.length = 2 * c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hws2 : ws2.length = 2 * c.max_vars) :
    ConnStateOk c F0 F_cur s0
      { s with scratch := { s.scratch with tarjan_mark := tm, work_stk1 := ws1,
                                           work_stk2 := ws2 } } :=
  ⟨fullDenseInvW_set_scr_arrs h.1 htm hws1 hws2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
   h.2.2.2.2.2⟩

private theorem fid_bv32_and_7fff_lt (x : BitVec 32) :
    (x &&& (2147483647 : BitVec 32)).toNat < 2 ^ 31 := by
  rw [BitVec.toNat_and, show ((2147483647 : BitVec 32)).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

end ConnectClauses

/-- Parametric `Func.wp` proof for `full_bva_connect_clauses_fid` (`GAP-BVA-02`):
flushes dense large watches via `full_fwd_flush_large_m7`, counts binary/large literal degrees,
runs `2` candidate peeling rounds, selectively reconnects surviving `3..5`-lit irredundant clauses,
and populates exact watch counts in `h->repr`. -/
theorem full_bva_connect_clauses_fid_wp (Γ : Env)
    (hFlush : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hCountDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fidBvaConnectClausesSpec a m Q X →
      Func.wp Γ full_bva_connect_clauses_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hwcap := c.hwcap
  unfold dimacsBound at hmx harc hwcap
  unfold Func.wp full_bva_connect_clauses_fid_body
  c0_hfast_nogrp
  fid_call hFlush
  refine fullFwdFlushLargeM6Spec_intro rfl hdw0 hm0 ?_
  intro s1 m1 hdw1 hcv1 har1 hal1 hfl1 _ _ _ _ hsb1 _ _ _ hm1
  have hok1 : ConnStateOk c F0 F_cur s0 s1 := ⟨hdw1, hcv1, hfl1, har1, hal1, hsb1⟩
  have hcv1_le := hdw1.1.core_ok.cur_vars_le
  have hnl1_nat :
      (BitVec.ofNat 64 s1.core.cur_vars <<< (1 : Nat)).toNat = 2 * s1.core.cur_vars := by
    c0_bound
  c0_hfast_nogrp
  -- Loop 1: zero `bc[0..nlits)` (`tarjan_mark`) and `lc[0..nlits)` (`work_stk1`)
  refine wp_loop_inv
    (fun (i, ()) ml => ∃ si,
      i.toNat ≤ 2 * s0.core.cur_vars ∧ ConnStateOk c F0 F_cur s0 si ∧
      (FullMem c si ⋆ R) ml)
    (fun (i, ()) _ => 2 * s0.core.cur_vars - i.toNat)
    (fun L1 hL1 => by c0_hfast; exact hL1 (0#64, ()) m1 ⟨s1, Nat.zero_le _, hok1, hm1⟩)
    (fun L1 (i, ()) ml ⟨si, hi_le, hoki, hmi⟩ ih1 => ?_)
  c0_hfast_nogrp
  · have hi_lt : i.toNat < 2 * s0.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := fid_bv64_add1 (by omega)
    have hcvi := hoki.1.1.core_ok.cur_vars_le; have hcve := hoki.2.1
    have htm_l := hoki.1.1.scratch_ok.tarjan_mark_len
    have hws1_l := hoki.1.1.scratch_ok.work_stk1_len
    c0_hfast
    have hdw_z := fullDenseInvW_set_scr_arrs hoki.1
      (tm := si.scratch.tarjan_mark.set i.toNat 0#32)
      (ws1 := si.scratch.work_stk1.set i.toNat 0#32)
      (by simp [htm_l]) (by simp [hws1_l]) hoki.1.1.scratch_ok.work_stk2_len
    exact ih1 (i + 1#64, ()) _ (by dsimp only; omega)
      ⟨_, by omega, ⟨hdw_z, hcve, hoki.2.2.1, hoki.2.2.2.1, hoki.2.2.2.2.1,
        hoki.2.2.2.2.2⟩, by assumption⟩
  -- Loop 2: count binary watches per active unassigned literal into `bc` (`tarjan_mark`)
  clear hc ih1 hok1 hm1 hi_le hcv1_le hnl1_nat
  c0_hfast_nogrp
  refine wp_loop_inv
    (fun (j, ()) m2 => ∃ s2,
      j.toNat ≤ 2 * s0.core.cur_vars ∧ ConnStateOk c F0 F_cur s0 s2 ∧ (FullMem c s2 ⋆ R) m2)
    (fun (j, ()) _ => 2 * s0.core.cur_vars - j.toNat)
    (fun L2 hL2 => by c0_hfast; exact hL2 (0#64, ()) ml ⟨si, Nat.zero_le _, hoki, hmi⟩)
    (fun L2 (j, ()) m2 ⟨s2, hj_le, hok2, hm2⟩ ih2 => ?_)
  have hdw_2 := hok2.1; have hcv2 := hok2.2.1; have hcv2_le := hdw_2.1.core_ok.cur_vars_le
  have hfl2_l := hdw_2.1.core_ok.flags_len; have hvl2_l := hdw_2.1.core_ok.vals_len
  have htm2_l := hdw_2.1.scratch_ok.tarjan_mark_len
  c0_hfast_nogrp
  · have hj_lt : j.toNat < 2 * s0.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
    have hj1 : (j + 1#64).toNat = j.toNat + 1 := fid_bv64_add1 (by omega)
    have hjshr : (j >>> (1 : Nat)).toNat = j.toNat / 2 := by c0_bound
    refine wp_join_group (ts := [])
      (fun _ mj => ∃ sj, ConnStateOk c F0 F_cur s0 sj ∧ (FullMem c sj ⋆ R) mj)
      (fun _ _ mj ⟨sj, hokj, hmj⟩ => by
        c0_hfast; exact ih2 (j + 1#64, ()) mj (by dsimp only; omega) ⟨sj, by omega, hokj, hmj⟩)
      (fun Jw hJw => ?_)
    c0_hfast_nogrp
    · have hlay := (m6_denseWatchesInv_of_w hdw_2).layout
      have hwb := hlay.bounds j.toNat (by omega)
      have hslice := (m6_denseWatchesInv_of_w hdw_2).slices j.toNat (by omega)
      have hj2 : (j <<< (1 : Nat)).toNat = 2 * j.toNat := by c0_bound
      have hj21 : ((j <<< (1 : Nat)) + 1#64).toNat = 2 * j.toNat + 1 := by c0_bound
      have hwv_len := hdw_2.1.core_ok.wvec_len
      have hws_len := hdw_2.1.core_ok.wstk_len_arr
      have hwl_le := hdw_2.1.core_ok.wlen_le
      have hoff_eq : (s2.core.wvec[(j <<< (1 : Nat)).toNat]'(by omega)).toNat =
          fullWatchOffCore s2.core j.toNat := by
        unfold fullWatchOffCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact congrArg BitVec.toNat (by simp only [hj2])
      have hsz_eq : (s2.core.wvec[((j <<< (1 : Nat)) + 1#64).toNat]'(by omega)).toNat =
          fullWatchSizeCore s2.core j.toNat := by
        unfold fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact congrArg BitVec.toNat (by simp only [hj21])
      let off_bv := BitVec.setWidth 64 (s2.core.wvec[(j <<< (1 : Nat)).toNat]'(by omega))
      let sz_bv := BitVec.setWidth 64 (s2.core.wvec[((j <<< (1 : Nat)) + 1#64).toNat]'(by omega))
      let end_bv := off_bv + sz_bv
      have hend_nat : end_bv.toNat =
          fullWatchOffCore s2.core j.toNat + fullWatchSizeCore s2.core j.toNat := by
        dsimp only [end_bv, off_bv, sz_bv]
        rw [BitVec.toNat_add, fid_bv64_32, fid_bv64_32, hoff_eq, hsz_eq]
        exact Nat.mod_eq_of_lt (by omega)
      c0_hfast_nogrp
      refine wp_loop_inv
        (fun (p, _bcnt, ()) mp =>
          mp = m2 ∧ fullWatchOffCore s2.core j.toNat ≤ p.toNat ∧ p.toNat ≤ end_bv.toNat)
        (fun (p, _, _) _ => end_bv.toNat - p.toNat)
        (fun Lp hLp => by
          c0_hfast
          exact hLp (off_bv, 0#32, ()) m2 ⟨rfl, by
            dsimp only [off_bv]; rw [fid_bv64_32, hoff_eq]; exact Nat.le_refl _,
            by dsimp only [off_bv]; rw [fid_bv64_32, hoff_eq, hend_nat]; omega⟩)
        (fun Lp (p, bcnt, ()) mp ⟨hmp, hp_lo, hp_hi⟩ ihp => ?_)
      rcases hmp with rfl
      c0_hfast_nogrp
      · have hp_lt : p.toNat < end_bv.toNat := by c0_bound
        have hp1 : (p + 1#64).toNat = p.toNat + 1 := fid_bv64_add1 (by omega)
        c0_hfast
        · have hoth_lt :
              ((s2.core.wstk[p.toNat]'(by omega)) &&& 0x7FFFFFFF#32).toNat <
                2 * s2.core.cur_vars :=
            m6_denseSlice_bin_other_lt hslice hp_lo (by omega)
              (List.getElem?_eq_getElem (by omega)) (by exact hc)
          have hoth_v :
              (((s2.core.wstk[p.toNat]'(by omega)) &&& 0x7FFFFFFF#32) >>>
                (1 : BitVec 32)).toNat < c.max_vars := by
            have hshr : ∀ x : BitVec 32, (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 := fun x => by
              simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
            rw [hshr]; omega
          have hoth_fl :
              (BitVec.setWidth 64 (((s2.core.wstk[p.toNat]'(by omega)) &&&
                (2147483647 : BitVec 32)) >>> (1 : BitVec 32))).toNat <
                  s2.core.flags.length := by
            rw [fid_bv64_32, hfl2_l]; exact hoth_v
          c0_hfast
          all_goals
            exact ihp (p + 1#64, _, ()) mp (by dsimp only; omega) ⟨rfl, by omega, by omega⟩
        · have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by rw [fid_bv64_add1 (by omega), hp1]
          have hp1_lt : p.toNat + 1 < end_bv.toNat := by
            have h1' : (BitVec.toNat p + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            have h2m : 2 * j.toNat % 2 ^ 64 = 2 * j.toNat := Nat.mod_eq_of_lt (by omega)
            have h21m : (2 * j.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                2 * j.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            have hoff' : s2.core.wvec[2 * j.toNat % 2 ^ 64].toNat =
                fullWatchOffCore s2.core j.toNat := by simpa only [hj2, h2m] using hoff_eq
            have hsz' :
                s2.core.wvec[(2 * j.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat =
                  fullWatchSizeCore s2.core j.toNat := by simpa only [hj21, h21m] using hsz_eq
            rw [h1', hoff', hsz', Nat.mod_eq_of_lt (by omega)] at hc
            omega
          exact ihp (p + 1#64 + 1#64, bcnt, ()) mp (by dsimp only; omega) ⟨rfl, by omega, by omega⟩
        · exact ihp (p + 1#64, bcnt, ()) mp (by dsimp only; omega) ⟨rfl, by omega, by omega⟩
      · c0_hfast
        have hdw_b := fullDenseInvW_set_scr_arrs hdw_2
          (tm := s2.scratch.tarjan_mark.set j.toNat bcnt)
          (by simp [htm2_l]) hdw_2.1.scratch_ok.work_stk1_len hdw_2.1.scratch_ok.work_stk2_len
        exact hJw () _ ⟨_, ⟨hdw_b, hok2.2.1, hok2.2.2.1, hok2.2.2.2.1, hok2.2.2.2.2.1,
          hok2.2.2.2.2.2⟩, by assumption⟩
    all_goals exact hJw () m2 ⟨s2, hok2, hm2⟩
  -- Loop 3: initial arena scan counting `3..5`-lit irredundant clauses into `lc` (`work_stk1`)
  clear hc ih2 hoki hmi hj_le hdw_2 hcv2 hcv2_le hfl2_l hvl2_l htm2_l
  c0_hfast_nogrp
  refine wp_loop_inv
    (fun (cands, p, ()) m3 => ∃ s3,
      p.toNat ≤ s3.core.arena_len ∧
      (p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3) ∧
      ConnStateOk c F0 F_cur s0 s3 ∧ (FullMem c s3 ⋆ R) m3)
    (fun (_, p, _) _ => s0.core.arena_len - p.toNat)
    (fun Lp hLp => by
      c0_hfast
      refine hLp (0#64, 0#64, ()) m2 ⟨s2, Nat.zero_le _, ?_, hok2, hm2⟩
      by_cases h0 : s2.core.arena_len = 0
      · exact Or.inl h0.symm
      · exact Or.inr (fid_zero_mem_arenaRefs hok2.1.2.1.arena (by omega)))
    (fun Lp (cands, p, ()) m3 ⟨s3, hp_le, hp_mem, hok3, hm3⟩ ih3 => ?_)
  have hdw_3 := hok3.1; have hal_3 := hok3.2.2.2.2.1
  have hal3_le := hdw_3.1.core_ok.arena_len_le; have har3_len := hdw_3.1.core_ok.arena_len_arr
  c0_hfast_nogrp
  · have hp_lt : p.toNat < s3.core.arena_len := by rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hp_ref : p.toNat ∈ fullArenaClauseRefs s3 := hp_mem.resolve_left (by omega)
    have hwf_p := hdw_3.2.1.arena.refs_wf p.toNat hp_ref
    have hp32 : (p.setWidth 32).toNat = p.toNat := fid_bv64_trunc32 (by omega)
    have hp2_nat : (p + 2#64).toNat = p.toNat + 2 := fid_bv64_add2 (by omega)
    let sz_p := s3.core.arena[(p + 2#64).toNat]'(by omega)
    have hsz_eq : sz_p.toNat = fullArenaClauseSizeCore s3.core p.toNat := by
      unfold sz_p fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (by simp only [hp2_nat])
    c0_hfast_nogrp
    fid_call hArenaNext
    refine ⟨c, s3, R, rfl, hdw_3.1, hm3, ?_⟩
    have hnb := fullArenaNextOff_bounds (ar := s3.core.arena) (alen := s3.core.arena_len)
      (cref := p.toNat) hwf_p.1
    have hnp_mem := fullArenaClauseRefs_next_mem hdw_3.2.1.arena hp_ref
    let np := (BitVec.ofNat 32 (fullArenaNextOff s3.core.arena s3.core.arena_len
      (p.setWidth 32).toNat)).setWidth 64
    have hnp_nat : np.toNat = fullArenaNextOff s3.core.arena s3.core.arena_len p.toNat := by
      dsimp only [np]; rw [hp32, fid_bv64_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    c0_hfast_nogrp
    refine wp_join_group (ts := [i64])
      (fun _ mj => ∃ sj, ConnStateOk c F0 F_cur s0 sj ∧ (FullMem c sj ⋆ R) mj)
      (fun _ ⟨nc', ⟨⟩⟩ mj ⟨sj, hokj, hmj⟩ => by
        c0_hfast
        have hrefs_eq : fullArenaClauseRefs sj = fullArenaClauseRefs s3 := by
          simp only [fullArenaClauseRefs, fullArenaClauseRefsCore, hokj.2.2.2.1,
            hokj.2.2.2.2.1, hok3.2.2.2.1, hok3.2.2.2.2.1]
        exact ih3 (nc', np, ()) mj (by dsimp only; omega)
          ⟨sj, by have := hokj.2.2.2.2.1; omega,
           by rw [hnp_nat, hokj.2.2.2.2.1, ← hal_3, hrefs_eq]; exact hnp_mem,
           hokj, hmj⟩)
      (fun Jc hJc => ?_)
    c0_hfast_nogrp
    · have hng : fullArenaClauseGarb s3 p.toNat = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [fid_bv32_garb_zero_of_and_480000 (by assumption)]; rfl
      refine wp_join_group (ts := [.bool, i32]) (fun _ mk => mk = m3)
        (fun _ ⟨sat, _kk, ⟨⟩⟩ mk hmk => ?_)
        (fun Jk hJk => ?_)
      · subst mk
        refine wp_join_group (ts := [i64, i32])
          (fun _ ms => ∃ ss, ConnStateOk c F0 F_cur s0 ss ∧ (FullMem c ss ⋆ R) ms)
          (fun _ ⟨nc, _, ⟨⟩⟩ ms h => by c0_hfast; exact hJc (nc, ()) ms h)
          (fun Js hJs => ?_)
        c0_hfast_nogrp
        · exact hJs (cands, _kk, ()) m3 ⟨s3, hok3, hm3⟩
        · refine wp_loop_inv
            (fun (k, ()) mk => ∃ sk,
              k.toNat ≤ sz_p.toNat ∧ ConnStateOk c F0 F_cur s0 sk ∧ (FullMem c sk ⋆ R) mk)
            (fun (k, ()) _ => sz_p.toNat - k.toNat)
            (fun Lk hLk => by c0_hfast; exact hLk (0#32, ()) m3 ⟨s3, Nat.zero_le _, hok3, hm3⟩)
            (fun Lk (k, ()) mk ⟨sk, hk_le, hokk, hmk⟩ ihk => ?_)
          c0_hfast_nogrp
          · have hk_lt : k.toNat < sz_p.toNat := by exact hc
            have hk1 : (k + 1#32).toNat = k.toNat + 1 := fid_bv32_add1 (by omega)
            have hl_idx : (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat :=
              fid_bv64_add3_u32 (by omega)
            have har_k := hokk.1.1.core_ok.arena_len_arr
            have hws1_k := hokk.1.1.scratch_ok.work_stk1_len
            have ⟨_, hl_lt, hl_sw⟩ := fid_conn_lit_lt hok3 hokk hp_ref hng (by omega) hl_idx
              (by omega)
            c0_hfast
            · refine ihk (k + 1#32, ()) _ (by dsimp only; omega) ⟨_, by omega, ?_, hm⟩
              exact connStateOk_set_scr_arrs hokk hokk.1.1.scratch_ok.tarjan_mark_len
                (by simp [hws1_k]) hokk.1.1.scratch_ok.work_stk2_len
            · exact ihk (k + 1#32, ()) mk (by dsimp only; omega) ⟨sk, by omega, hokk, hmk⟩
          · c0_hfast; exact hJs (cands + 1#64, k, ()) mk ⟨sk, hokk, hmk⟩
      · refine wp_loop_inv
          (fun (k, ()) mk => mk = m3 ∧ k.toNat ≤ sz_p.toNat)
          (fun (k, ()) _ => sz_p.toNat - k.toNat)
          (fun Lk hLk => by c0_hfast; exact hLk (0#32, ()) m3 ⟨rfl, Nat.zero_le _⟩)
          (fun Lk (k, ()) mk ⟨hmk, hk_le⟩ ihk => ?_)
        subst mk
        c0_hfast_nogrp
        · have hk_lt : k.toNat < sz_p.toNat := by exact hc
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := fid_bv32_add1 (by omega)
          have hl_idx : (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat :=
            fid_bv64_add3_u32 (by omega)
          have hvl_3 := hdw_3.1.core_ok.vals_len
          have ⟨_, hl_lt, hl_sw⟩ := fid_conn_lit_lt hok3 hok3 hp_ref hng (by omega) hl_idx
            (by omega)
          c0_hfast
          · exact hJk (true, k, ()) m3 rfl
          · exact ihk (k + 1#32, ()) m3 (by dsimp only; omega) ⟨rfl, by omega⟩
        · c0_hfast; exact hJk (false, k, ()) m3 rfl
    all_goals exact hJc (cands, ()) m3 ⟨s3, hok3, hm3⟩
  -- Loop 4: up to `2` peeling rounds (`while (rnd < 2u && cands > 0ULL)`, with `break`)
  clear hc ih3 hok2 hm2 hp_le hp_mem hdw_3 hal_3 hal3_le har3_len
  c0_hfast_nogrp
  refine wp_join_group (ts := [i64, i64, i64, i32])
    (fun _ m5 => ∃ s5, ConnStateOk c F0 F_cur s0 s5 ∧ (FullMem c s5 ⋆ R) m5)
    ?_ ?_
  · -- Continuation after Loop 4: Loop 5 (reconnect) -> Loop 6 (populate `deg`)
    rintro _ _ m5 ⟨s5, hok5, hm5⟩
    clear hok3 hm3
    c0_hfast_nogrp
    refine wp_loop_inv
      (fun (p5, ()) m5l => ∃ sp,
        p5.toNat ≤ sp.core.arena_len ∧
        (p5.toNat = sp.core.arena_len ∨ p5.toNat ∈ fullArenaClauseRefs sp) ∧
        ConnStateOk c F0 F_cur s0 sp ∧ (FullMem c sp ⋆ R) m5l)
      (fun (p5, ()) _ => s0.core.arena_len - p5.toNat)
      (fun Lp5 hLp5 => by
        c0_hfast
        refine hLp5 (0#64, ()) m5 ⟨s5, Nat.zero_le _, ?_, hok5, hm5⟩
        by_cases h0 : s5.core.arena_len = 0
        · exact Or.inl h0.symm
        · exact Or.inr (fid_zero_mem_arenaRefs hok5.1.2.1.arena (by omega)))
      (fun Lp5 (p5, ()) m5l ⟨sp, hp_le5, hp_mem5, hokp, hmp⟩ ih5 => ?_)
    have hdw_p := hokp.1; have hal_p := hokp.2.2.2.2.1
    have hal_le := hdw_p.1.core_ok.arena_len_le; have har_len := hdw_p.1.core_ok.arena_len_arr
    c0_hfast_nogrp
    -- Join `Js_1` (`ts := []`) for Loop 5's `!(p5 < arena_len && oom == 0)` exit -> Loop 6
    refine wp_join_group (ts := [])
      (fun _ m6 => ∃ s6, ConnStateOk c F0 F_cur s0 s6 ∧ (FullMem c s6 ⋆ R) m6)
      (fun _ _ m6 ⟨s6, hok6, hm6⟩ => ?_)
      (fun J5x hJ5x => ?_)
    · -- Loop 6: populate exact watch degrees `deg[0..nlits)` in `h->repr`
      clear ih5 hokp hmp hp_le5 hp_mem5 hdw_p hal_p hal_le har_len hok5 hm5
      c0_hfast_nogrp
      refine wp_loop_inv
        (fun (dl, ()) m6l => ∃ sl,
          dl.toNat ≤ 2 * s0.core.cur_vars ∧ ConnStateOk c F0 F_cur s0 sl ∧
          (FullMem c sl ⋆ R) m6l)
        (fun (dl, ()) _ => 2 * s0.core.cur_vars - dl.toNat)
        (fun J6 hJ6 => by c0_hfast; exact hJ6 (0#64, ()) m6 ⟨s6, Nat.zero_le _, hok6, hm6⟩)
        (fun J6 (dl, ()) m6l ⟨sl, hdl_le, hokl, hml⟩ ih6 => ?_)
      have hcvl := hokl.2.1; have hcvl_le := hokl.1.1.core_ok.cur_vars_le
      have hrepr_l := hokl.1.1.core_ok.repr_len
      c0_hfast_nogrp
      · have hdl_lt : dl.toNat < 2 * s0.core.cur_vars := by
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
        have hdl32 : (dl.setWidth 32).toNat = dl.toNat := fid_bv64_trunc32 (by omega)
        have hdl1 : (dl + 1#64).toNat = dl.toNat + 1 := fid_bv64_add1 (by omega)
        fid_call hCountDeg
        refine ⟨c, F0, F_cur, sl, R, rfl, hokl.1,
          by dsimp only [Arg.val]; rw [hdl32]; omega, hml, fun degv => ?_⟩
        c0_hfast
        have hdw_r := fullDenseInvW_set_repr hokl.1
          (rp := sl.core.repr.set dl.toNat degv) (by simp [hrepr_l])
        exact ih6 (dl + 1#64, ()) _ (by dsimp only; omega)
          ⟨_, by omega, ⟨hdw_r, hcvl, hokl.2.2.1, hokl.2.2.2.1, hokl.2.2.2.2.1,
            hokl.2.2.2.2.2⟩, by assumption⟩
      · c0_hfast
        exact hQ sl m6l hokl.1 hokl.2.1 hokl.2.2.1 hokl.2.2.2.1 hokl.2.2.2.2.1 hokl.2.2.2.2.2 hml
    · -- Loop 5 body (`p5 < arena_len && h->oom == 0`)
      c0_hfast_nogrp
      · have hp_lt : p5.toNat < sp.core.arena_len := by
          have h1 : p5.toNat < sp.core.arena_len % 2 ^ 64 := by assumption
          rwa [Nat.mod_eq_of_lt (by omega)] at h1
        have hp_ref : p5.toNat ∈ fullArenaClauseRefs sp := hp_mem5.resolve_left (by omega)
        have hwf_p := hdw_p.2.1.arena.refs_wf p5.toNat hp_ref
        have hp32 : (p5.setWidth 32).toNat = p5.toNat := fid_bv64_trunc32 (by omega)
        have hp2_nat : (p5 + 2#64).toNat = p5.toNat + 2 := fid_bv64_add2 (by omega)
        let sz_p := sp.core.arena[(p5 + 2#64).toNat]'(by omega)
        have hsz_eq : sz_p.toNat = fullArenaClauseSizeCore sp.core p5.toNat := by
          unfold sz_p fullArenaClauseSizeCore
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact congrArg BitVec.toNat (by simp only [hp2_nat])
        c0_hfast_nogrp
        fid_call hArenaNext
        refine ⟨c, sp, R, rfl, hdw_p.1, hmp, ?_⟩
        have hnb := fullArenaNextOff_bounds (ar := sp.core.arena) (alen := sp.core.arena_len)
          (cref := p5.toNat) hwf_p.1
        have hnp_mem := fullArenaClauseRefs_next_mem hdw_p.2.1.arena hp_ref
        let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena sp.core.arena_len
          (p5.setWidth 32).toNat)).setWidth 64
        have hnp_nat : np.toNat = fullArenaNextOff sp.core.arena sp.core.arena_len p5.toNat := by
          dsimp only [np]; rw [hp32, fid_bv64_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        c0_hfast_nogrp
        refine wp_join_group (ts := [])
          (fun _ mj => ∃ sj, ConnStateOk c F0 F_cur s0 sj ∧ (FullMem c sj ⋆ R) mj)
          (fun _ _ mj ⟨sj, hokj, hmj⟩ => by
            c0_hfast
            have hrefs_eq : fullArenaClauseRefs sj = fullArenaClauseRefs sp := by
              simp only [fullArenaClauseRefs, fullArenaClauseRefsCore, hokj.2.2.2.1,
                hokj.2.2.2.2.1, hokp.2.2.2.1, hokp.2.2.2.2.1]
            exact ih5 (np, ()) mj (by dsimp only; omega)
              ⟨sj, by have := hokj.2.2.2.2.1; omega,
               by rw [hnp_nat, hokj.2.2.2.2.1, ← hal_p, hrefs_eq]; exact hnp_mem,
               hokj, hmj⟩)
          (fun Jc hJc => ?_)
        c0_hfast_nogrp
        · have hng : fullArenaClauseGarb sp p5.toNat = false := by
            unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            rw [fid_bv32_garb_zero_of_and_480000 (by assumption)]; rfl
          have hsz3 : 3 ≤ sz_p.toNat := by assumption
          have hsz5 : sz_p.toNat ≤ 5 := by assumption
          refine wp_join_group (ts := [.bool, i32]) (fun _ mk => mk = m5l)
            (fun _ ⟨keep, _kk, ⟨⟩⟩ mk hmk => ?_)
            (fun Jk hJk => ?_)
          · subst mk
            refine wp_join_group (ts := [i32])
              (fun _ ms => ∃ ss, ConnStateOk c F0 F_cur s0 ss ∧ (FullMem c ss ⋆ R) ms)
              (fun _ _ ms h => by c0_hfast; exact hJc () ms h)
              (fun Js hJs => ?_)
            c0_hfast_nogrp
            · refine wp_join_group (ts := [i32])
                (fun _ mw => ∃ sw, ConnStateOk c F0 F_cur s0 sw ∧ (FullMem c sw ⋆ R) mw)
                (fun _ ⟨kw, ⟨⟩⟩ mw h => by c0_hfast; exact hJs (kw, ()) mw h)
                (fun Jw hJw => ?_)
              c0_hfast_nogrp
              refine wp_loop_inv
                (fun (k, ()) mw => ∃ sw,
                  k.toNat ≤ sz_p.toNat ∧ ConnStateOk c F0 F_cur s0 sw ∧ (FullMem c sw ⋆ R) mw)
                (fun (k, ()) _ => sz_p.toNat - k.toNat)
                (fun Lk hLk => by
                  c0_hfast; exact hLk (0#32, ()) m5l ⟨sp, Nat.zero_le _, hokp, hmp⟩)
                (fun Lk (k, ()) mw ⟨sw, hk_le, hokw, hmw⟩ ihk => ?_)
              c0_hfast_nogrp
              · have hk_lt : k.toNat < sz_p.toNat := by exact hc
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := fid_bv32_add1 (by omega)
                have hl_idx : (p5 + 3#64 + BitVec.setWidth 64 k).toNat =
                    p5.toNat + 3 + k.toNat := fid_bv64_add3_u32 (by omega)
                have har_w := hokw.1.1.core_ok.arena_len_arr
                have ⟨hl_lt, _, _⟩ := fid_conn_lit_lt hokp hokw hp_ref hng (by omega) hl_idx
                  (by omega)
                have hsz_mask : (sz_p &&& 0x7FFFFFFF#32).toNat = sz_p.toNat := by
                  have h31 : sz_p.toNat < 2 ^ 31 := by omega
                  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
                    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h31]
                have hflag0 : (sz_p &&& 0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 := by
                  rw [BitVec.and_assoc,
                    show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 from rfl, BitVec.and_zero]
                c0_hfast_nogrp
                fid_call hWatchPush
                refine ⟨c, sw, R, rfl, hokw.1.1, (m6_denseWatchesInv_of_w hokw.1).layout,
                  fun h => by simp at h,
                  fun _ => by
                    dsimp only [Arg.val]
                    exact ⟨fid_bv32_ne_sent (fid_bv32_and_7fff_lt _),
                      fid_bv32_ne_sent (by rw [hp32]; omega)⟩,
                  hmw, ?_⟩
                intro ok wvec' wstk' wlen' wu' wsort' m' sw' hlen' hlay' hoth hok_t hok_f hm'
                have hp_ref_sw : (p5.setWidth 32).toNat ∈ fullArenaClauseRefs sw := by
                  rw [hp32]; simp only [fullArenaClauseRefs, fullArenaClauseRefsCore,
                    hokw.2.2.2.1, hokw.2.2.2.2.1]
                  simpa only [fullArenaClauseRefs, fullArenaClauseRefsCore,
                    hokp.2.2.2.1, hokp.2.2.2.2.1] using hp_ref
                have hdw_wp : FullDenseInvW c F0 F_cur sw' :=
                  m6_fullDenseInvW_of_watchPush_occ hokw.1 hlen' hlay'
                    hflag0 (by omega) (by rw [hp32]; omega) hp_ref_sw hoth
                    (fun ht => by
                      obtain ⟨h1, _, h3, h4, h5, h6⟩ := hok_t ht
                      exact ⟨h1, h3, h4, h5, h6 rfl⟩)
                    (fun hf => (hok_f hf).1)
                have hokw' : ConnStateOk c F0 F_cur s0 sw' :=
                  ⟨hdw_wp, hokw.2.1, hokw.2.2.1, hokw.2.2.2.1, hokw.2.2.2.2.1, hokw.2.2.2.2.2⟩
                c0_hfast
                · exact ihk (k + 1#32, ()) m' (by dsimp only; omega) ⟨sw', by omega, hokw', hm'⟩
                · have hdw_oom := fullDenseInvW_set_oom hdw_wp 1#64
                  exact hJw (k, ()) _ ⟨_, ⟨hdw_oom, hokw.2.1, hokw.2.2.1, hokw.2.2.2.1,
                    hokw.2.2.2.2.1, hokw.2.2.2.2.2⟩, by assumption⟩
              · c0_hfast; exact hJw (k, ()) mw ⟨sw, hokw, hmw⟩
            · exact hJs (_kk, ()) m5l ⟨sp, hokp, hmp⟩
          · refine wp_loop_inv
              (fun (k, ()) mk => mk = m5l ∧ k.toNat ≤ sz_p.toNat)
              (fun (k, ()) _ => sz_p.toNat - k.toNat)
              (fun Lk hLk => by c0_hfast; exact hLk (0#32, ()) m5l ⟨rfl, Nat.zero_le _⟩)
              (fun Lk (k, ()) mk ⟨hmk, hk_le⟩ ihk => ?_)
            subst mk
            c0_hfast_nogrp
            · have hk_lt : k.toNat < sz_p.toNat := by exact hc
              have hk1 : (k + 1#32).toNat = k.toNat + 1 := fid_bv32_add1 (by omega)
              have hl_idx : (p5 + 3#64 + BitVec.setWidth 64 k).toNat = p5.toNat + 3 + k.toNat :=
                fid_bv64_add3_u32 (by omega)
              have hvl_p := hdw_p.1.core_ok.vals_len
              have htm_p := hdw_p.1.scratch_ok.tarjan_mark_len
              have hws1_p := hdw_p.1.scratch_ok.work_stk1_len
              have ⟨_, hl_lt, hl_sw⟩ := fid_conn_lit_lt hokp hokp hp_ref hng (by omega) hl_idx
                (by omega)
              c0_hfast
              · exact hJk (false, k, ()) m5l rfl
              · exact hJk (false, k, ()) m5l rfl
              · exact ihk (k + 1#32, ()) m5l (by dsimp only; omega) ⟨rfl, by omega⟩
            · c0_hfast; exact hJk (true, k, ()) m5l rfl
        all_goals exact hJc () m5l ⟨sp, hokp, hmp⟩
      all_goals exact hJ5x () m5l ⟨sp, hokp, hmp⟩
  · -- Body of Loop 4 (`while (rnd < 2u && cands > 0ULL)`, tuple `(i, cands, p, rnd)`)
    intro J4 hJ4
    c0_hfast_nogrp
    refine wp_loop_inv
      (fun (_i4, _cands, _p4, rnd, ()) m4 => ∃ sr,
        rnd.toNat ≤ 2 ∧ ConnStateOk c F0 F_cur s0 sr ∧ (FullMem c sr ⋆ R) m4)
      (fun (_, _, _, rnd, _) _ => 2 - rnd.toNat)
      (fun Lr hLr => by
        c0_hfast; exact hLr (j, cands, p, 0#32, ()) m3 ⟨s3, Nat.zero_le _, hok3, hm3⟩)
      (fun Lr (i4, cands4, p4, rnd, ()) m4 ⟨sr, hrnd_le, hokr, hmr⟩ ihr => ?_)
    clear hok3 hm3
    have hcvr := hokr.2.1; have hcvr_le := hokr.1.1.core_ok.cur_vars_le
    c0_hfast_nogrp
    · have hrnd_lt : rnd.toNat < 2 := by assumption
      have hrnd1 : (rnd + 1#32).toNat = rnd.toNat + 1 := fid_bv32_add1 (by omega)
      -- Sub-loop 4a: zero `nlc[0..nlits)` (`work_stk2`)
      refine wp_loop_inv
        (fun (ia, ()) ma => ∃ sa,
          ia.toNat ≤ 2 * s0.core.cur_vars ∧ ConnStateOk c F0 F_cur s0 sa ∧ (FullMem c sa ⋆ R) ma)
        (fun (ia, ()) _ => 2 * s0.core.cur_vars - ia.toNat)
        (fun La hLa => by c0_hfast; exact hLa (0#64, ()) m4 ⟨sr, Nat.zero_le _, hokr, hmr⟩)
        (fun La (ia, ()) ma ⟨sa, hia_le, hoka, hma⟩ iha => ?_)
      c0_hfast_nogrp
      · have hia_lt : ia.toNat < 2 * s0.core.cur_vars := by
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
        have hia1 : (ia + 1#64).toNat = ia.toNat + 1 := fid_bv64_add1 (by omega)
        have hcva := hoka.1.1.core_ok.cur_vars_le; have hcvea := hoka.2.1
        have hws2_a := hoka.1.1.scratch_ok.work_stk2_len
        c0_hfast
        have hdw_a := fullDenseInvW_set_scr_arrs hoka.1
          (ws2 := sa.scratch.work_stk2.set ia.toNat 0#32)
          hoka.1.1.scratch_ok.tarjan_mark_len hoka.1.1.scratch_ok.work_stk1_len
          (by simp [hws2_a])
        exact iha (ia + 1#64, ()) _ (by dsimp only; omega)
          ⟨_, by omega, ⟨hdw_a, hcvea, hoka.2.2.1, hoka.2.2.2.1, hoka.2.2.2.2.1,
            hoka.2.2.2.2.2⟩, by assumption⟩
      -- Sub-loop 4b: arena peeling pass updating `nlc` (`work_stk2`), tuple `(pb, ncands)`
      clear hc iha hokr hmr hia_le hcvr hcvr_le
      c0_hfast_nogrp
      refine wp_loop_inv
        (fun (pb, _ncands, ()) mb => ∃ sb,
          pb.toNat ≤ sb.core.arena_len ∧
          (pb.toNat = sb.core.arena_len ∨ pb.toNat ∈ fullArenaClauseRefs sb) ∧
          ConnStateOk c F0 F_cur s0 sb ∧ (FullMem c sb ⋆ R) mb)
        (fun (pb, _, _) _ => s0.core.arena_len - pb.toNat)
        (fun Lp hLp => by
          c0_hfast
          refine hLp (0#64, 0#64, ()) ma ⟨sa, Nat.zero_le _, ?_, hoka, hma⟩
          by_cases h0 : sa.core.arena_len = 0
          · exact Or.inl h0.symm
          · exact Or.inr (fid_zero_mem_arenaRefs hoka.1.2.1.arena (by omega)))
        (fun Lp (pb, ncands, ()) mb ⟨sb, hpb_le, hpb_mem, hokb, hmb⟩ ihb => ?_)
      have hdw_b := hokb.1; have hal_b := hokb.2.2.2.2.1
      have hal_le := hdw_b.1.core_ok.arena_len_le; have har_len := hdw_b.1.core_ok.arena_len_arr
      c0_hfast_nogrp
      · have hpb_lt : pb.toNat < sb.core.arena_len := by
          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
        have hpb_ref : pb.toNat ∈ fullArenaClauseRefs sb := hpb_mem.resolve_left (by omega)
        have hwf_p := hdw_b.2.1.arena.refs_wf pb.toNat hpb_ref
        have hpb32 : (pb.setWidth 32).toNat = pb.toNat := fid_bv64_trunc32 (by omega)
        have hpb2_nat : (pb + 2#64).toNat = pb.toNat + 2 := fid_bv64_add2 (by omega)
        let sz_p := sb.core.arena[(pb + 2#64).toNat]'(by omega)
        have hsz_eq : sz_p.toNat = fullArenaClauseSizeCore sb.core pb.toNat := by
          unfold sz_p fullArenaClauseSizeCore
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact congrArg BitVec.toNat (by simp only [hpb2_nat])
        c0_hfast_nogrp
        fid_call hArenaNext
        refine ⟨c, sb, R, rfl, hdw_b.1, hmb, ?_⟩
        have hnb := fullArenaNextOff_bounds (ar := sb.core.arena) (alen := sb.core.arena_len)
          (cref := pb.toNat) hwf_p.1
        have hnp_mem := fullArenaClauseRefs_next_mem hdw_b.2.1.arena hpb_ref
        let np := (BitVec.ofNat 32 (fullArenaNextOff sb.core.arena sb.core.arena_len
          (pb.setWidth 32).toNat)).setWidth 64
        have hnp_nat : np.toNat = fullArenaNextOff sb.core.arena sb.core.arena_len pb.toNat := by
          dsimp only [np]; rw [hpb32, fid_bv64_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        c0_hfast_nogrp
        refine wp_join_group (ts := [i64])
          (fun _ mj => ∃ sj, ConnStateOk c F0 F_cur s0 sj ∧ (FullMem c sj ⋆ R) mj)
          (fun _ ⟨nc', ⟨⟩⟩ mj ⟨sj, hokj, hmj⟩ => by
            c0_hfast
            have hrefs_eq : fullArenaClauseRefs sj = fullArenaClauseRefs sb := by
              simp only [fullArenaClauseRefs, fullArenaClauseRefsCore, hokj.2.2.2.1,
                hokj.2.2.2.2.1, hokb.2.2.2.1, hokb.2.2.2.2.1]
            exact ihb (np, nc', ()) mj (by dsimp only; omega)
              ⟨sj, by have := hokj.2.2.2.2.1; omega,
               by rw [hnp_nat, hokj.2.2.2.2.1, ← hal_b, hrefs_eq]; exact hnp_mem,
               hokj, hmj⟩)
          (fun Jc hJc => ?_)
        c0_hfast_nogrp
        · have hng : fullArenaClauseGarb sb pb.toNat = false := by
            unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            rw [fid_bv32_garb_zero_of_and_480000 (by assumption)]; rfl
          refine wp_join_group (ts := [.bool, i32]) (fun _ mk => mk = mb)
            (fun _ ⟨keep, _kk, ⟨⟩⟩ mk hmk => ?_)
            (fun Jk hJk => ?_)
          · subst mk
            refine wp_join_group (ts := [i64, i32])
              (fun _ ms => ∃ ss, ConnStateOk c F0 F_cur s0 ss ∧ (FullMem c ss ⋆ R) ms)
              (fun _ ⟨nc, _, ⟨⟩⟩ ms h => by c0_hfast; exact hJc (nc, ()) ms h)
              (fun Js hJs => ?_)
            c0_hfast_nogrp
            · refine wp_loop_inv
                (fun (k, ()) mk => ∃ sk,
                  k.toNat ≤ sz_p.toNat ∧ ConnStateOk c F0 F_cur s0 sk ∧ (FullMem c sk ⋆ R) mk)
                (fun (k, ()) _ => sz_p.toNat - k.toNat)
                (fun Lk hLk => by c0_hfast; exact hLk (0#32, ()) mb ⟨sb, Nat.zero_le _, hokb, hmb⟩)
                (fun Lk (k, ()) mk ⟨sk, hk_le, hokk, hmk⟩ ihk => ?_)
              c0_hfast_nogrp
              · have hk_lt : k.toNat < sz_p.toNat := by exact hc
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := fid_bv32_add1 (by omega)
                have hl_idx : (pb + 3#64 + BitVec.setWidth 64 k).toNat =
                    pb.toNat + 3 + k.toNat := fid_bv64_add3_u32 (by omega)
                have har_k := hokk.1.1.core_ok.arena_len_arr
                have hws2_k := hokk.1.1.scratch_ok.work_stk2_len
                have ⟨_, hl_lt, hl_sw⟩ := fid_conn_lit_lt hokb hokk hpb_ref hng (by omega) hl_idx
                  (by omega)
                c0_hfast
                · refine ihk (k + 1#32, ()) _ (by dsimp only; omega) ⟨_, by omega, ?_, hm⟩
                  exact connStateOk_set_scr_arrs hokk hokk.1.1.scratch_ok.tarjan_mark_len
                    hokk.1.1.scratch_ok.work_stk1_len (by simp [hws2_k])
                · exact ihk (k + 1#32, ()) mk (by dsimp only; omega) ⟨sk, by omega, hokk, hmk⟩
              · c0_hfast; exact hJs (ncands + 1#64, k, ()) mk ⟨sk, hokk, hmk⟩
            · exact hJs (ncands, _kk, ()) mb ⟨sb, hokb, hmb⟩
          · refine wp_loop_inv
              (fun (k, ()) mk => mk = mb ∧ k.toNat ≤ sz_p.toNat)
              (fun (k, ()) _ => sz_p.toNat - k.toNat)
              (fun Lk hLk => by c0_hfast; exact hLk (0#32, ()) mb ⟨rfl, Nat.zero_le _⟩)
              (fun Lk (k, ()) mk ⟨hmk, hk_le⟩ ihk => ?_)
            subst mk
            c0_hfast_nogrp
            · have hk_lt : k.toNat < sz_p.toNat := by exact hc
              have hk1 : (k + 1#32).toNat = k.toNat + 1 := fid_bv32_add1 (by omega)
              have hl_idx : (pb + 3#64 + BitVec.setWidth 64 k).toNat =
                  pb.toNat + 3 + k.toNat := fid_bv64_add3_u32 (by omega)
              have hvl_b := hdw_b.1.core_ok.vals_len
              have htm_b := hdw_b.1.scratch_ok.tarjan_mark_len
              have hws1_b := hdw_b.1.scratch_ok.work_stk1_len
              have ⟨_, hl_lt, hl_sw⟩ := fid_conn_lit_lt hokb hokb hpb_ref hng (by omega) hl_idx
                (by omega)
              c0_hfast
              · exact hJk (false, k, ()) mb rfl
              · exact hJk (false, k, ()) mb rfl
              · exact ihk (k + 1#32, ()) mb (by dsimp only; omega) ⟨rfl, by omega⟩
            · c0_hfast; exact hJk (true, k, ()) mb rfl
        all_goals exact hJc (ncands, ()) mb ⟨sb, hokb, hmb⟩
      -- Sub-loop 4c: copy `lc[0..nlits) = nlc[0..nlits)` then check `ncands == cands`
      clear hc ihb hoka hma hpb_le hpb_mem hdw_b hal_b hal_le har_len
      c0_hfast_nogrp
      refine wp_loop_inv
        (fun (jc, ()) mc => ∃ sc,
          jc.toNat ≤ 2 * s0.core.cur_vars ∧ ConnStateOk c F0 F_cur s0 sc ∧ (FullMem c sc ⋆ R) mc)
        (fun (jc, ()) _ => 2 * s0.core.cur_vars - jc.toNat)
        (fun Lc hLc => by c0_hfast; exact hLc (0#64, ()) mb ⟨sb, Nat.zero_le _, hokb, hmb⟩)
        (fun Lc (jc, ()) mc ⟨sc, hjc_le, hokc, hmc⟩ ihc => ?_)
      c0_hfast_nogrp
      · have hcvc := hokc.1.1.core_ok.cur_vars_le; have hcvec := hokc.2.1
        have hjc_lt : jc.toNat < 2 * s0.core.cur_vars := by
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
        have hjc1 : (jc + 1#64).toNat = jc.toNat + 1 := fid_bv64_add1 (by omega)
        have hws1_l := hokc.1.1.scratch_ok.work_stk1_len
        have hws2_l := hokc.1.1.scratch_ok.work_stk2_len
        c0_hfast
        refine ihc (jc + 1#64, ()) _ (by dsimp only; omega) ⟨_, by omega, ?_, by assumption⟩
        exact connStateOk_set_scr_arrs hokc hokc.1.1.scratch_ok.tarjan_mark_len
          (by simp [hws1_l]) hws2_l
      · c0_hfast; exact hJ4 (jc, cands4, pb, rnd, ()) mc ⟨sc, hokc, hmc⟩
      · c0_hfast
        exact ihr (jc, ncands, pb, rnd + 1#32, ()) mc (by dsimp only; omega)
          ⟨sc, by omega, hokc, hmc⟩
    all_goals exact hJ4 (i4, cands4, p4, rnd, ()) m4 ⟨sr, hokr, hmr⟩
/-! ## 7. Zero-Hop Upstream `watches_score` Candidate Picker (`full_bva_pick_cand`) -/

/-- Parametric `Func.wp` proof for `full_bva_pick_cand` against canonical
`FullBvaHeap.fullBvaPickCandSpec` (`0` callees, strict upstream `deg[clit]` tie-breaking). -/
theorem full_bva_pick_cand_fid_wp (Γ : Env) :
    ∀ a m Q X, fullBvaPickCandSpec a m Q X → Func.wp Γ full_bva_pick_cand_body a m Q X := by
  rintro ⟨h, ncntd, f0, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hf0_lt, hnc_le, hcntd_ok, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hrepr_len := hcl.repr_len
  have hws_len := hsc.wsort_len; have hws1_len := hsc.work_stk1_len
  unfold Func.wp full_bva_pick_cand_body
  c0_hsteps
  refine wp_loop_inv
    (fun (best_c, best_deg, best_lit, ci, ()) ml =>
      ml = m ∧ ci.toNat ≤ ncntd.toNat ∧
      (2 ≤ best_c.toNat → best_lit.toNat < 2 * s.core.cur_vars))
    (fun (_, _, _, ci, _) _ => ncntd.toNat - ci.toNat)
    (fun J1 hJ1 => by
      c0_hsteps
      exact hJ1 (0#32, 0#32, 0xFFFFFFFF#32, 0#32, ()) m
        ⟨rfl, Nat.zero_le _, fun h => by simp only [bv_c0] at h; omega⟩)
    (fun J1 (best_c, best_deg, best_lit, ci, ()) ml ⟨hml, hci_le, hbl_ok⟩ ih1 => ?_)
  rcases hml with rfl
  c0_hsteps_nogrp
  · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
    have hci64 : (BitVec.setWidth 64 ci).toNat = ci.toNat := by c0_bound
    have hclit_lt :
        (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
      have := hcntd_ok ci.toNat hci_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
    c0_hsteps
    all_goals first
      | exact ih1 (_, _, _, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, fun _ => by simpa only [hci64] using hclit_lt⟩
      | exact ih1 (_, _, best_lit, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, hbl_ok⟩
  · let mkSt (ws : List (BitVec 32)) : FullState :=
      { core := { s.core with repr := s.core.repr, min_clr := s.core.min_clr,
                              tmp_cnt := s.core.tmp_cnt, tmp_len := s.core.tmp_len }
        scratch := { s.scratch with wsort := ws, ant_sz := s.scratch.ant_sz,
                                    sim_sig := s.scratch.sim_sig,
                                    shrink_stk := s.scratch.shrink_stk } }
    c0_hsteps
    refine wp_loop_inv
      (fun (ci, ()) m2 => ∃ ws2,
        ci.toNat ≤ ncntd.toNat ∧ ws2.length = 2 * c.max_vars ∧
        (FullMem c (mkSt ws2) ⋆ R) m2)
      (fun (ci, ()) _ => ncntd.toNat - ci.toNat)
      (fun J2 hJ2 => by
        c0_hsteps
        exact hJ2 (0#32, ()) ml ⟨s.scratch.wsort, Nat.zero_le _, hws_len, hm⟩)
      (fun J2 (ci, ()) m2 ⟨ws2, hci_le, hws2_len, hm2⟩ ih2 => ?_)
    dsimp only [mkSt] at hm2
    c0_hsteps_nogrp
    · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
      have hclit_lt :
          (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        have := hcntd_ok ci.toNat hci_lt
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
      c0_hsteps
      exact ih2 (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
        ⟨_, by rw [hci1]; omega, by simp [hws2_len], hm⟩
    · have hinv_fin : FullDenseInvNoLm c F0 F_cur (mkSt ws2) :=
        fullDenseInvNoLm_with_core_aux hinv hcl.repr_len hcl.min_clr_len_arr hcl.tmp_len_arr
          hcl.flags_len hcl.tmp_len_le { hsc with wsort_len := hws2_len } rfl rfl
      c0_hsteps
      · exact hQ 0xFFFFFFFF#32 s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin (Or.inl rfl) hm2
      · exact hQ best_lit s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin
          (Or.inr (hbl_ok (by c0_bound))) hm2

/-! ## 8. Bit-25 (`PH_BVA_Q`) Large-Clause Matcher (`full_bva_match_large_bva_fid`) -/

private theorem fid_bv32_garb_zero_of_and_02480000 {x : BitVec 32}
    (h : (x &&& 0x02480000#32) = 0#32) : (x &&& 0x00080000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00080000#32) h
  rw [BitVec.and_assoc, show (0x02480000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

private theorem fid_bv32_bvaq_zero_of_and_02480000 {x : BitVec 32}
    (h : (x &&& 0x02480000#32) = 0#32) : (x &&& 0x02000000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x02000000#32) h
  rw [BitVec.and_assoc, show (0x02480000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

/-- Parametric `Func.wp` proof for `full_bva_match_large_bva_fid` (`PH_BVA_Q` bit 25). -/
theorem full_bva_match_large_bva_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBvaMatchLargeBvaSpec a m Q X →
      Func.wp Γ full_bva_match_large_bva_fid_body a m Q X := by
  rintro ⟨h, cur_cr, next_lit, d_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R_mem, R_set, rfl, hslen, hw, hnodup, hl0, hdm, hcur_ref, hcur_ng, hd_ref,
     hR_nd, hR_lt, hcur_sz, hlm2_sub, hm, hQ⟩
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcl := hslen.core_ok; have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le
  have hlm_len := hcl.lit_mark_len; have hcv_le := hcl.cur_vars_le
  have hcur_wf := hw.arena.refs_wf cur_cr.toNat hcur_ref
  have hd_wf := hw.arena.refs_wf d_ref.toNat hd_ref
  have hcur_sz_eq : (s.core.arena[cur_cr.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSize s cur_cr.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hd_sz_eq : (s.core.arena[d_ref.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSize s d_ref.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hcur2_idx : (BitVec.setWidth 64 cur_cr + 2).toNat = cur_cr.toNat + 2 := by
    change (BitVec.setWidth 64 cur_cr + 2#64).toNat = _; c0_bound
  have hd2_idx : (BitVec.setWidth 64 d_ref + 2).toNat = d_ref.toNat + 2 := by
    change (BitVec.setWidth 64 d_ref + 2#64).toNat = _; c0_bound
  have hd0_idx : (BitVec.setWidth 64 d_ref).toNat = d_ref.toNat := by c0_bound
  unfold Func.wp full_bva_match_large_bva_fid_body
  c0_hsteps
  · exact hQ false (fun h => by cases h)
  · exact hQ false (fun h => by cases h)
  · have hsz_eq : fullArenaClauseSize s d_ref.toNat = fullArenaClauseSize s cur_cr.toNat := by
      have h1 : s.core.arena[(BitVec.setWidth 64 d_ref + 2).toNat]'(by rw [hd2_idx]; omega) =
          s.core.arena[(BitVec.setWidth 64 cur_cr + 2).toNat]'(by rw [hcur2_idx]; omega) := by
        assumption
      have h2 := congrArg BitVec.toNat h1; simp only [hd2_idx, hcur2_idx] at h2; omega
    have h0248 : (s.core.arena[d_ref.toNat]'(by omega) &&& 0x02480000#32) = 0#32 := by
      have h1 : (s.core.arena[(BitVec.setWidth 64 d_ref).toNat]'(by rw [hd0_idx]; omega) &&&
          0x02480000#32) = 0#32 := by assumption
      simpa only [hd0_idx] using h1
    have hd_ng : fullArenaClauseGarb s d_ref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp [fid_bv32_garb_zero_of_and_02480000 h0248]
    have hd_nbvaq : (fullArenaHdr s d_ref.toNat &&& 0x02000000#32) = 0#32 := by
      unfold fullArenaHdr fullArenaHdrCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact fid_bv32_bvaq_zero_of_and_02480000 h0248
    let sz_bv := s.core.arena[(BitVec.setWidth 64 cur_cr + 2).toNat]'(by rw [hcur2_idx]; omega)
    have hsz_bv_nat : sz_bv.toNat = fullArenaClauseSize s cur_cr.toNat := by
      dsimp only [sz_bv]; simp only [hcur2_idx]; exact hcur_sz_eq
    have hd_lits_len : (fullArenaClauseLits s d_ref.toNat).length = sz_bv.toNat := by
      unfold fullArenaClauseLits
      rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by
        have := hd_wf.2.2.1; have := hd_wf.2.2.2.1; omega)]
      unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega
    have hcur2_mod : (cur_cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
        cur_cr.toNat + 2 := by
      rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
    have hsz_mod : sz_bv = s.core.arena[(cur_cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
        rw [hcur2_mod]; omega) := by
      dsimp only [sz_bv]; simp only [hcur2_idx, hcur2_mod]
    refine wp_loop_inv
      (fun (j, seen_next, ()) ml =>
        ml = m ∧ j.toNat ≤ sz_bv.toNat ∧
        (seen_next = true → next_lit.toNat ∈ fullArenaClauseLits s d_ref.toNat) ∧
        (∀ k < j.toNat, let dl := (s.core.arena[d_ref.toNat + 3 + k]?.getD 0#32).toNat
          dl ≠ next_lit.toNat → dl ∈ R_set))
      (fun (j, _, _) _ => sz_bv.toNat - j.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (0#32, false, ()) m ⟨rfl, Nat.zero_le _, (fun h => by cases h),
          fun _ h => by simp only [bv_c0] at h; omega⟩)
      (fun J (j, seen_next, ()) ml ⟨hml, hj_le, hseen, hall⟩ ih => ?_)
    rcases hml with rfl
    c0_hsteps
    · have hj_lt : j.toNat < sz_bv.toNat := by rw [hsz_mod]; c0_bound
      have hj_lt_d : j.toNat < fullArenaClauseSizeCore s.core d_ref.toNat := by
        unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega
      have hdl_idx : (BitVec.setWidth 64 d_ref + 3 + BitVec.setWidth 64 j).toNat =
          d_ref.toNat + 3 + j.toNat := by
        change (BitVec.setWidth 64 d_ref + 3#64 + BitVec.setWidth 64 j).toNat = _; c0_bound
      have hdl_mod : (d_ref.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
          d_ref.toNat + 3 + j.toNat := by
        rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
      have hdl_mem : (s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega)).toNat ∈
          fullArenaClauseLits s d_ref.toNat :=
        List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem hj_lt_d (by omega))
      have hdl_lt := hw.arena.lits_lt d_ref.toNat hd_ref hd_ng _ hdl_mem
      have hdl_lt_lm : (s.core.arena[(BitVec.setWidth 64 d_ref + 3 +
          BitVec.setWidth 64 j).toNat]'(by rw [hdl_idx]; omega)).toNat <
            s.core.lit_mark.length := by
        have h1 : s.core.arena[(BitVec.setWidth 64 d_ref + 3 +
            BitVec.setWidth 64 j).toNat]'(by rw [hdl_idx]; omega) =
            s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega) := by simp only [hdl_idx]
        rw [h1]; omega
      c0_hsteps
      · exact hQ false (fun h => by cases h)
      · have hdl_eq : (s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega)) = next_lit := by
          have h1 : s.core.arena[(d_ref.toNat + BitVec.toNat (3 : BitVec 64) +
              j.toNat) % 2 ^ 64]'(by rw [hdl_mod]; omega) = next_lit := by assumption
          simpa only [hdl_mod] using h1
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
        refine ih (j + 1#32, true, ()) ml (by dsimp only; rw [hj1]; omega)
          ⟨rfl, by rw [hj1]; omega, fun _ => by rw [← hdl_eq]; exact hdl_mem, fun k hk hne => ?_⟩
        rw [hj1] at hk
        by_cases hkj : k = j.toNat
        · subst hkj
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hdl_eq] at hne
          exact absurd rfl hne
        · exact hall k (by omega) hne
      · exact hQ false (fun h => by cases h)
      · have hdl_in : (s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega)).toNat ∈ R_set := by
          apply hlm2_sub _ hdl_lt
          have h1 : ¬ (BitVec.setWidth 32 (s.core.lit_mark[(s.core.arena[(d_ref.toNat +
              BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64]'(by
              rw [hdl_mod]; omega)).toNat]'(by simp only [hdl_mod]; omega)) &&&
              BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 2)) =
              BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) := by assumption
          simp only [hdl_mod] at h1; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          intro h0; apply h1; apply BitVec.eq_of_toNat_eq
          have h0' := congrArg BitVec.toNat h0
          simp only [BitVec.toNat_and, BitVec.toNat_setWidth,
            show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 2)).toNat = 2 from rfl,
            show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)).toNat = 0 from rfl,
            show (2#8 : BitVec 8).toNat = 2 from rfl,
            show (0#8 : BitVec 8).toNat = 0 from rfl] at h0' ⊢
          have hlt8 := (s.core.lit_mark[(s.core.arena[d_ref.toNat + 3 + j.toNat]'(by
            omega)).toNat]'(by omega)).isLt
          rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt8 (by decide))]; exact h0'
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
        refine ih (j + 1#32, seen_next, ()) ml (by dsimp only; rw [hj1]; omega)
          ⟨rfl, by rw [hj1]; omega, hseen, fun k hk hne => ?_⟩
        rw [hj1] at hk
        by_cases hkj : k = j.toNat
        · subst hkj; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdl_in
        · exact hall k (by omega) hne
    · have hj_eq : j.toNat = sz_bv.toNat := by rw [hsz_mod]; c0_bound
      refine hQ seen_next fun htrue => ?_
      have hnext_in := hseen htrue
      have hD_nd : (fullArenaClauseLits s d_ref.toNat).Nodup :=
        nodup_of_map_div2 (hnodup d_ref.toNat hd_ref hd_ng)
      have hsub : ∀ x ∈ fullArenaClauseLits s d_ref.toNat, x ≠ next_lit.toNat → x ∈ R_set := by
        intro x hx hne
        obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hx
        have hk_sz : k < sz_bv.toNat := by rw [← hd_lits_len]; exact hk_lt
        have hk_get := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := s.core)
          (r := d_ref.toNat) (j := k) (by unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega)
          (by have := hd_wf.2.2.1; have := hd_wf.2.2.2.1
              unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega)
        have hx_eq : x = (s.core.arena[d_ref.toNat + 3 + k]?.getD 0#32).toNat := by
          have h1 : (fullArenaClauseLits s d_ref.toNat)[k]? = some x := by
            rw [List.getElem?_eq_getElem hk_lt, hk_eq]
          unfold fullArenaClauseLits at h1; rw [hk_get] at h1
          rw [← Option.some.inj h1, List.getElem?_eq_getElem (by
            have := hd_wf.2.2.1; have := hd_wf.2.2.2.1; have := hcl.arena_len_le
            unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega), Option.getD_some]
        rw [hx_eq] at hne ⊢; exact hall k (by omega) hne
      have ⟨hperm, hfilt⟩ := bva_match_large_perm hR_nd hD_nd hnext_in
        (by rw [hd_lits_len, hsz_bv_nat, hcur_sz]) hsub
      exact ⟨hd_ng, hd_nbvaq, hsz_eq, hnext_in, hperm, hfilt,
        clause_entails_of_perm hperm (hw.arena.entails d_ref.toNat hd_ref hd_ng)⟩

end LeanQbe.T.Examples.Kissat.FullFidelityBva

end
