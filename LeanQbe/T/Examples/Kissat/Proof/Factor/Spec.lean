/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Factor` (`15` Functions)

Defines `deps`, dynamic packed BVA matrix invariants (`fidStepsCap`, `FidBvaRowEntryOk`,
`FidBvaMatrixInv`, `Step7BvaLayout`, `Step7BvaMatrixInv`, `Step7RowRefOk`,
`Step7BvaCommittedOk`), UNSAT-sound `Spec.XFree` contracts for all `15` functions in
`Src.Factor.fns`, `SpecEntry` list `specs` matching `Src.Factor.fns` order 1:1, and
`Env.Sat` capability projections (`deps_has_*` and `has_*`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Factor.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Factor

public section

/-! ## 1. External Dependencies & Shared BVA Matrix Invariants -/

/-- Canonical upstream callee environment required by `Src.Factor`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Clause.Spec.specs ++ Forward.Spec.specs ++
  Internal.Spec.specs ++ Limits.Spec.specs ++ Watch.Spec.specs

/-- Maximum dynamic BVA matrix depth (`sc`) permitted inside `scratch_buf[0 .. cap)`
so that `4 * sc ≤ cap` when `64 ≤ cap`. -/
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
@[expose] def FidBvaRowEntryOk (F_cur : List (List Nat)) (s : FullState) (fr : Nat)
    (w : BitVec 32) (res : List Nat) : Prop :=
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

/-- Monotone bump-allocator layout of the dynamic BVA matrix required by `full_bva_commit`:
every row `r` precedes its parent table and every earlier row's `(row, parent)` slices
precede later rows (`row_off[r'] ≥ par_off[r] + qn[r]`). -/
@[expose] def Step7BvaLayout (c : FullCfg) (s : FullState) (step : Nat) : Prop :=
  let sc := fidStepsCap c.scratch_cap
  let sb := s.scratch.scratch_buf
  (∀ r < step, 0 < r →
    (sb[sc + r]?.getD 0#32).toNat + (sb[2 * sc + r]?.getD 0#32).toNat ≤
      (sb[3 * sc + r]?.getD 0#32).toNat) ∧
  (∀ r r', r < r' → r' < step →
    (sb[2 * sc + r']?.getD 0#32).toNat ≤ (sb[2 * sc + r]?.getD 0#32).toNat ∧
    (sb[sc + r]?.getD 0#32).toNat + (sb[2 * sc + r]?.getD 0#32).toNat ≤
      (sb[sc + r']?.getD 0#32).toNat ∧
    (0 < r → (sb[3 * sc + r]?.getD 0#32).toNat + (sb[2 * sc + r]?.getD 0#32).toNat ≤
      (sb[sc + r']?.getD 0#32).toNat))

/-- Step-7 packed matrix invariant: `FidBvaMatrixInv` plus the monotone bump layout. -/
@[expose] def Step7BvaMatrixInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (step bump : Nat) : Prop :=
  FidBvaMatrixInv c F_cur s step bump ∧ Step7BvaLayout c s step

theorem Step7BvaMatrixInv.toFid {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {step bump : Nat} (h : Step7BvaMatrixInv c F_cur s step bump) :
    FidBvaMatrixInv c F_cur s step bump :=
  h.1

theorem Step7BvaLayout.mono {c : FullCfg} {s : FullState} {step step' : Nat}
    (hle : step' ≤ step) (h : Step7BvaLayout c s step) : Step7BvaLayout c s step' :=
  ⟨fun r hr hr0 => h.1 r (by omega) hr0, fun r r' hrr hr' => h.2 r r' hrr (by omega)⟩

theorem Step7BvaLayout.congr {c : FullCfg} {s s' : FullState} {step : Nat}
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf) (h : Step7BvaLayout c s step) :
    Step7BvaLayout c s' step := by
  unfold Step7BvaLayout at h ⊢; rw [hsb]; exact h

/-- Validity of one compacted matrix entry `w` read by `full_factor`: a binary watch
`PW_BIN_FLAG | q` with `q < 2 * cur_vars`, or an in-bounds arena clause ref (possibly already
garbage-marked by `full_bva_commit`) whose literals are all `< 2 * cur_vars`. -/
@[expose] def Step7RowRefOk (s : FullState) (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars
  else
    w.toNat ∈ fullArenaClauseRefs s ∧
    w.toNat + 3 + fullArenaClauseSize s w.toNat ≤ s.core.arena_len ∧
    ∀ l ∈ fullArenaClauseLits s w.toNat, l < 2 * s.core.cur_vars

/-- Post-commit state read by `full_factor` after `full_bva_try_lit` returns `true`:
`h->res_sz = bk < sc`, and every row `q ≤ bk` has factor literal `< 2 * cur_vars`, an in-bounds
block `[ro, ro + qn) ⊆ [0, scratch_cap)`, and valid entries (`Step7RowRefOk`). -/
@[expose] def Step7BvaCommittedOk (c : FullCfg) (s : FullState) (bk : Nat) : Prop :=
  let sc := fidStepsCap c.scratch_cap
  let sb := s.scratch.scratch_buf
  bk < sc ∧ s.scratch.res_sz = BitVec.ofNat 64 bk ∧
  ∀ q ≤ bk,
    let ro := (sb[sc + q]?.getD 0#32).toNat
    let qn := (sb[2 * sc + q]?.getD 0#32).toNat
    (sb[q]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧ ro + qn ≤ c.scratch_cap ∧
    ∀ qi < qn, Step7RowRefOk s (sb[ro + qi]?.getD 0#32)

theorem Step7RowRefOk.congr {s s' : FullState} {w : BitVec 32}
    (hcv : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (h : Step7RowRefOk s w) :
    Step7RowRefOk s' w := by
  unfold Step7RowRefOk at h ⊢
  simp only [fullArenaClauseRefs, fullArenaClauseSize, fullArenaClauseLits,
    fullArenaClauseRefsCore, fullArenaClauseSizeCore, fullArenaClauseLitsCore, har, hal,
    hcv] at h ⊢
  exact h

theorem Step7BvaCommittedOk.congr {c : FullCfg} {s s' : FullState} {bk : Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len)
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hres : s'.scratch.res_sz = s.scratch.res_sz) (h : Step7BvaCommittedOk c s bk) :
    Step7BvaCommittedOk c s' bk := by
  dsimp only [Step7BvaCommittedOk] at h ⊢
  obtain ⟨hbk, hrs, hrows⟩ := h
  refine ⟨hbk, hres.trans hrs, fun q hq => ?_⟩
  obtain ⟨hfr, hro, hent⟩ := hrows q hq
  rw [hsb, hcv]
  exact ⟨hfr, hro, fun qi hqi => (hent qi hqi).congr hcv har hal⟩

/-! ## 2. Canonical Per-Function `Spec` Contracts (`15` Functions) -/

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

/-- Spec for `full_bva_connect_clauses_fid`: preserves `FullDenseInvW`, `cur_vars`, `fuel`,
`arena`, `arena_len`, `scratch_buf`. -/
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
      d_ref.toNat ∈ fullArenaClauseRefs s ∧ R_set.Nodup ∧
      (∀ x ∈ R_set, x < 2 * s.core.cur_vars) ∧
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

/-- Canonical spec for `full_bva_scan_cands`
(`ncntd ≤ 2 * c.max_vars` and `ws1'[i] ≤ init_lits`). -/
@[expose] def step13BvaScanCandsSpec : Spec [i64, i32, i32, i64] [i32] :=
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
        s'.LengthsOk c → ncntd.toNat ≤ 2 * c.max_vars →
        (∀ i < ncntd.toNat,
          (ws1'[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
          (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q (ncntd, ()) m'

/-- Canonical spec for `full_bva_pick_cand`: accepts `ncntd ≤ 2 * c.max_vars`. -/
@[expose] def step13BvaPickCandSpec : Spec [i64, i32, i32] [i32] :=
  fun (h, ncntd, f0, ()) m Q _ =>
    ∃ c F0 F_cur s R,
      h = c.hdr ∧ FullBvaHeapHelpers.FullDenseInvNoLm c F0 F_cur s ∧
      f0.toNat < 2 * s.core.cur_vars ∧ ncntd.toNat ≤ 2 * c.max_vars ∧
      (∀ i < ncntd.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) (repr' mclr' : List (BitVec 32)) (tc' tl' : Nat)
        (wsort' : List (BitVec 32)) (ant' : BitVec 64) (sig' : List (BitVec 64))
        (shrk' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState :=
          { core := { s.core with tmp_cnt := tc', tmp_len := tl', min_clr := mclr', repr := repr' }
            scratch := { s.scratch with ant_sz := ant', shrink_stk := shrk',
                                          wsort := wsort', sim_sig := sig' } }
        FullBvaHeapHelpers.FullDenseInvNoLm c F0 F_cur s' →
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2 * s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Spec for `full_bva_filter_row`: packed dynamic matrix + `ant_sz` ticks. -/
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

/-- Canonical spec for `full_bva_commit`: consumes `Step7BvaMatrixInv` over rows `0 ..= best_k`
with `h->res_sz = best_k`, and on `ok = true` strictly increments `cur_vars` and exports the
compacted matrix (`Step7BvaCommittedOk`). -/
@[expose] def step7BvaCommitSpec : Spec [i64, i32] [.bool] := fun (h, best_k, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (bump : Nat),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
    1 ≤ best_k.toNat ∧ best_k.toNat < fidStepsCap c.scratch_cap ∧
    Step7BvaMatrixInv c F_cur s (best_k.toNat + 1) bump ∧
    s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical spec for `full_bva_try_lit`: preserves `FullDenseInv`, strictly advances `cur_vars`
and exports `Step7BvaCommittedOk` on `ok = true`. -/
@[expose] def step7BvaTryLitSpec : Spec [i64, i32, i64] [.bool] :=
  fun (h, f0, _init_cv, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInv c F0 s ∧ f0.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
        (ok = true → s.core.cur_vars < s'.core.cur_vars) →
        (ok = true → ∃ bk, Step7BvaCommittedOk c s' bk) →
        s'.core.fuel = s.core.fuel →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical spec for `full_bva_upd_lit_fid`: packed `u64` `(hsz << 32) ||| tl` in arg 5. -/
@[expose] def step9BvaUpdLitSpec : Spec [i64, i64, i64, i64, i64, i64] [i32] :=
  fun (h, fheap, fpos, deg, cur_nl, hsz_tl, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop) (hsz tl : BitVec 32),
      h = c.hdr ∧ fheap = c.pTarjanMark ∧ fpos = c.pTarjanReach ∧ deg = c.pRepr ∧
      hsz_tl = (BitVec.setWidth 64 hsz <<< (32 : Nat)) ||| BitVec.setWidth 64 tl ∧
      FullDenseInv c F0 s ∧ cur_nl.toNat = 2 * s.core.cur_vars ∧
      tl.toNat < 2 * s.core.cur_vars ∧ hsz.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ i < hsz.toNat, (s.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (hsz' : BitVec 32) (rp hp ps : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState :=
          { s with core := { s.core with repr := rp }
                   scratch := { s.scratch with tarjan_mark := hp, tarjan_reach := ps } }
        FullDenseInv c F0 s' → hsz'.toNat ≤ 2 * s.core.cur_vars →
        (∀ i < hsz'.toNat, (hp[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q (hsz', ()) m'

/-- Canonical contract for `full_factor` (re-exported from `Proof.Spec.Contracts4`). -/
abbrev fullFactorHeapSpec : Spec [i64, i64] [i64] :=
  Proof.Spec.fullFactorHeapSpec

/-- Canonical read-only contract for `full_has_factor_cands_fid`. -/
@[expose] def step13HasFactorCandsSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : Bool, Q (r, ()) m

/-! ## 3. Canonical `SpecEntry` Table & Structural Theorems -/

/-- Canonical `SpecEntry` table matching `Src.Factor.fns` 1:1. -/
@[expose] def specs : List SpecEntry :=
  [ { name := "full_bva_steps_cap_fid", as := [i64], rs := [i32],
      spec := fidBvaStepsCapSpec, noExit := true }
  , { name := "full_bva_clines_fid", as := [i64], rs := [i64],
      spec := fidBvaClinesSpec, noExit := true }
  , { name := "full_fheap_up_fid", as := [i64, i64, i64, i32], rs := [],
      spec := fidFheapUpSpec, noExit := true }
  , { name := "full_fheap_down_fid", as := [i64, i64, i64, i32, i32], rs := [],
      spec := fidFheapDownSpec, noExit := true }
  , { name := "full_bva_count_lit_deg_fid", as := [i64, i32], rs := [i32],
      spec := fidBvaCountLitDegSpec, noExit := true }
  , { name := "full_bva_connect_clauses_fid", as := [i64], rs := [],
      spec := fidBvaConnectClausesSpec, noExit := true }
  , { name := "full_bva_match_large_bva_fid", as := [i64, i32, i32, i32], rs := [.bool],
      spec := fidBvaMatchLargeBvaSpec, noExit := true }
  , { name := "full_bva_scan_cands", as := [i64, i32, i32, i64], rs := [i32],
      spec := step13BvaScanCandsSpec, noExit := true }
  , { name := "full_bva_pick_cand", as := [i64, i32, i32], rs := [i32],
      spec := step13BvaPickCandSpec, noExit := true }
  , { name := "full_bva_filter_row", as := [i64, i32, i32, i32, i32, i32], rs := [i32],
      spec := fidBvaFilterRowSpec, noExit := true }
  , { name := "full_bva_commit", as := [i64, i32], rs := [.bool],
      spec := step7BvaCommitSpec, noExit := true }
  , { name := "full_bva_try_lit", as := [i64, i32, i64], rs := [.bool],
      spec := step7BvaTryLitSpec, noExit := true }
  , { name := "full_bva_upd_lit_fid", as := [i64, i64, i64, i64, i64, i64], rs := [i32],
      spec := step9BvaUpdLitSpec, noExit := true }
  , { name := "full_factor", as := [i64, i64], rs := [i64],
      spec := fullFactorHeapSpec, noExit := true }
  , { name := "full_has_factor_cands_fid", as := [i64], rs := [.bool],
      spec := step13HasFactorCandsSpec, noExit := true } ]

theorem fidBvaStepsCapSpec_xfree : Spec.XFree fidBvaStepsCapSpec := by xfree
theorem fidBvaClinesSpec_xfree : Spec.XFree fidBvaClinesSpec := by xfree
theorem fidFheapUpSpec_xfree : Spec.XFree fidFheapUpSpec := by xfree
theorem fidFheapDownSpec_xfree : Spec.XFree fidFheapDownSpec := by xfree
theorem fidBvaCountLitDegSpec_xfree : Spec.XFree fidBvaCountLitDegSpec := by xfree
theorem fidBvaConnectClausesSpec_xfree : Spec.XFree fidBvaConnectClausesSpec := by xfree
theorem fidBvaMatchLargeBvaSpec_xfree : Spec.XFree fidBvaMatchLargeBvaSpec := by xfree
theorem step13BvaScanCandsSpec_xfree : Spec.XFree step13BvaScanCandsSpec := by xfree
theorem step13BvaPickCandSpec_xfree : Spec.XFree step13BvaPickCandSpec := by xfree
theorem fidBvaFilterRowSpec_xfree : Spec.XFree fidBvaFilterRowSpec := by xfree
theorem step7BvaCommitSpec_xfree : Spec.XFree step7BvaCommitSpec := by xfree
theorem step7BvaTryLitSpec_xfree : Spec.XFree step7BvaTryLitSpec := by xfree
theorem step9BvaUpdLitSpec_xfree : Spec.XFree step9BvaUpdLitSpec := by xfree
theorem fullFactorHeapSpec_xfree : Spec.XFree fullFactorHeapSpec := by xfree
theorem step13HasFactorCandsSpec_xfree : Spec.XFree step13HasFactorCandsSpec := by xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Factor.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact fidBvaStepsCapSpec_xfree
  · exact fidBvaClinesSpec_xfree
  · exact fidFheapUpSpec_xfree
  · exact fidFheapDownSpec_xfree
  · exact fidBvaCountLitDegSpec_xfree
  · exact fidBvaConnectClausesSpec_xfree
  · exact fidBvaMatchLargeBvaSpec_xfree
  · exact step13BvaScanCandsSpec_xfree
  · exact step13BvaPickCandSpec_xfree
  · exact fidBvaFilterRowSpec_xfree
  · exact step7BvaCommitSpec_xfree
  · exact step7BvaTryLitSpec_xfree
  · exact step9BvaUpdLitSpec_xfree
  · exact fullFactorHeapSpec_xfree
  · exact step13HasFactorCandsSpec_xfree

/-! ## 4. `Env.Sat` Projections (`deps` and `specs`) -/

theorem deps_has_full_arena_next {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_arena_next" fullArenaNextSpec :=
  Arena.Spec.has_full_arena_next h.left.left.left.left.left

theorem deps_has_full_alloc_cl {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_alloc_cl" fullAllocClSpec :=
  Arena.Spec.has_full_alloc_cl h.left.left.left.left.left

theorem deps_has_full_add_bin {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_add_bin" fullAddBinSpec :=
  Clause.Spec.has_full_add_bin h.left.left.left.left.right

theorem deps_has_full_fwd_flush_large_m7 {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_fwd_flush_large_m7" Forward.Spec.fullFwdFlushLargeM7Spec :=
  Forward.Spec.has_full_fwd_flush_large_m7 h.left.left.left.right

theorem deps_has_full_init_fresh_var {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_init_fresh_var" Internal.Spec.fullInitFreshVarSpec :=
  Internal.Spec.has_full_init_fresh_var h.left.left.right

theorem deps_has_full_fill_u64_m7 {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_fill_u64_m7" Limits.Spec.m7FillU64Spec :=
  Env.Sat.has h.left.right
    (List.getElem_mem (l := Limits.Spec.specs) (n := 6) (by decide))
    Limits.Spec.m7FillU64Spec_xfree

theorem deps_has_full_wstack_defrag {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_wstack_defrag" fullWstackDefragSpec :=
  Watch.Spec.has_full_wstack_defrag h.right

theorem deps_has_full_watch_push {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_watch_push" fullWatchPushSpec :=
  Watch.Spec.has_full_watch_push h.right

theorem deps_has_full_unwatch_large {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_unwatch_large" fullUnwatchLargeSpec :=
  Watch.Spec.has_full_unwatch_large h.right

theorem deps_has_full_delete_binary {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_delete_binary" Watch.Spec.fullDeleteBinarySpec :=
  Watch.Spec.has_full_delete_binary h.right

theorem has_full_bva_steps_cap_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_steps_cap_fid" fidBvaStepsCapSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide)) fidBvaStepsCapSpec_xfree

theorem has_full_bva_clines_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_clines_fid" fidBvaClinesSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide)) fidBvaClinesSpec_xfree

theorem has_full_fheap_up_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fheap_up_fid" fidFheapUpSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide)) fidFheapUpSpec_xfree

theorem has_full_fheap_down_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fheap_down_fid" fidFheapDownSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide)) fidFheapDownSpec_xfree

theorem has_full_bva_count_lit_deg_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_count_lit_deg_fid" fidBvaCountLitDegSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide)) fidBvaCountLitDegSpec_xfree

theorem has_full_bva_connect_clauses_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_connect_clauses_fid" fidBvaConnectClausesSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide))
    fidBvaConnectClausesSpec_xfree

theorem has_full_bva_match_large_bva_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_match_large_bva_fid" fidBvaMatchLargeBvaSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 6) (by decide))
    fidBvaMatchLargeBvaSpec_xfree

theorem has_full_bva_scan_cands {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_scan_cands" step13BvaScanCandsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 7) (by decide))
    step13BvaScanCandsSpec_xfree

theorem has_full_bva_pick_cand {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_pick_cand" step13BvaPickCandSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 8) (by decide))
    step13BvaPickCandSpec_xfree

theorem has_full_bva_filter_row {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_filter_row" fidBvaFilterRowSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 9) (by decide)) fidBvaFilterRowSpec_xfree

theorem has_full_bva_commit {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_commit" step7BvaCommitSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 10) (by decide)) step7BvaCommitSpec_xfree

theorem has_full_bva_try_lit {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_try_lit" step7BvaTryLitSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 11) (by decide)) step7BvaTryLitSpec_xfree

theorem has_full_bva_upd_lit_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bva_upd_lit_fid" step9BvaUpdLitSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 12) (by decide)) step9BvaUpdLitSpec_xfree

theorem has_full_factor {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_factor" fullFactorHeapSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 13) (by decide)) fullFactorHeapSpec_xfree

theorem has_full_has_factor_cands_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_has_factor_cands_fid" step13HasFactorCandsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 14) (by decide))
    step13HasFactorCandsSpec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
