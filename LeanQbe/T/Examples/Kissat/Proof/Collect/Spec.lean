/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Kissat Canonical `Spec` Table for `Src.Collect` (`Proof.Collect.Spec`)

Canonical `Env` contracts and `CanonicalEnv` `SpecEntry` list (`specs`) for all `15` functions in
`Src.Collect.fns`, depending strictly on
`Arena.Spec.specs ++ Backtrack.Spec.specs ++ Watch.Spec.specs` with `0` legacy imports and
`0` SAT model proofs.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect.Spec

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Auxiliary Predicates & Local `Collect` Specifications -/

/-- Watch slice containing binary watches and only large-clause refs strictly below `keep`. -/
inductive WatchSliceLtOk (keep : Nat) (F_cur : List (List Nat))
    (k : FullCoreState) (lit : Nat) : Nat → Nat → Prop where
  | empty {p} : WatchSliceLtOk keep F_cur k lit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      WatchSliceLtOk keep F_cur k lit (p + 1) rem →
      WatchSliceLtOk keep F_cur k lit p (rem + 1)
  | large {p rem w0 cref} :
      k.wstk[p]? = some w0 → k.wstk[p + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 → cref.toNat < 0x80000000 → cref.toNat < keep →
      cref.toNat ∈ fullArenaClauseRefsCore k →
      WatchSliceLtOk keep F_cur k lit (p + 2) rem →
      WatchSliceLtOk keep F_cur k lit p (rem + 2)

theorem WatchSliceLtOk.toWatchSliceOk {keep : Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceLtOk keep F_cur k lit p rem) : WatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih
  | large hp1 hp2 hflag hlt _ hcref _ ih => exact .large hp1 hp2 hflag hlt hcref ih

theorem WatchSliceLtOk.ne_sentinel {keep : Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceLtOk keep F_cur k lit p rem) :
    ∀ idx < rem, k.wstk[p + idx]? ≠ some 0xFFFFFFFF#32 :=
  h.toWatchSliceOk.ne_sentinel

theorem WatchSliceLtOk.relocate {keep : Nat} {F F' : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat}
    (hF : (cnfOfClauses F').Entails (cnfOfClauses F)) (hvars : k.cur_vars ≤ k'.cur_vars)
    (hkeep : ∀ r ∈ fullArenaClauseRefsCore k, r < keep → r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : WatchSliceLtOk keep F k lit p rem) : WatchSliceLtOk keep F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (by omega)
      (CNF.entails_clause_trans hF hent) (ih (p' := p' + 1) fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
  | @large p rem w0 cref hp1 hp2 hfl hlt hkp hcr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp1)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hwstk 1 (by omega)).trans hp2)
      hfl hlt hkp (hkeep cref.toNat hcr hkp)
      (ih (p' := p' + 2) fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))

theorem WatchSliceLtOk.append_bin {keep : Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hkeep : ∀ r ∈ fullArenaClauseRefsCore k, r < keep → r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : WatchSliceLtOk keep F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceLtOk keep F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))
  | @large p rem w cref hp1 hp2 hfl hltc hkp hcr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp1)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hwstk 1 (by omega)).trans hp2)
      hfl hltc hkp (hkeep cref.toNat hcr hkp)
      (ih (p' := p' + 2)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))

theorem WatchSliceLtOk.append_large {keep : Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat} {w0 cref : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hkeep : ∀ r ∈ fullArenaClauseRefsCore k, r < keep → r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : WatchSliceLtOk keep F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hcr : k'.wstk[p' + rem + 1]? = some cref)
    (hfl : (w0 &&& 0x80000000#32) = 0#32) (hltc : cref.toNat < 0x80000000)
    (hkp : cref.toNat < keep) (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceLtOk keep F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty =>
    exact .large (by simpa using hw0) (by simpa [Nat.add_assoc] using hcr) hfl hltc hkp href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcr))
  | @large p rem w cr hp1 hp2 hfl2 hltc2 hkp2 hcr2 _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp1)
      (by simpa [Nat.add_assoc, Nat.add_comm] using (hwstk 1 (by omega)).trans hp2)
      hfl2 hltc2 hkp2 (hkeep cr.toNat hcr2 hkp2)
      (ih (p' := p' + 2) (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcr))

/-- Partial watch-stack sweep contract used by `full_sweep_bins_range_m6` and
`full_arena_sweep_m6`: removes garbage and large watches with `cref ≥ keep_before`. -/
@[expose] def fullSweepBinsRangeSpec : Spec [i64, i64] [] := fun (h, keep_before, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (0 < keep_before.toNat → s.core.dense_mode = 0#64) ∧
    FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' nb' ws' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                wusable := 0#64, num_binary := nb' }
          scratch := { s.scratch with wsort := ws' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ l < 2 * s.core.cur_vars,
        WatchSliceLtOk keep_before.toNat F_cur s'.core l
          (fullWatchOff s' l) (fullWatchSize s' l)) →
      FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q () m'

/-- Canonical postcondition shared by `full_rewatch_range_m6` and `full_rewatch_arena_m6`. -/
@[expose] def fullRewatchArenaPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (Q : Post [.bool]) : Prop :=
  ∀ (ok : Bool) arena' wvec' wstk' wlen' wu' oom' wsort' m',
    let s' : FullState :=
      { s with
        core := { s.core with arena := arena', wvec := wvec', wstk := wstk',
                              wlen := wlen', wusable := wu', oom := oom' }
        scratch := { s.scratch with wsort := wsort' } }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
    (FullArenaVarsNodup s → FullArenaVarsNodup s') →
    fullArenaClauseRefs s' = fullArenaClauseRefs s →
    (ok = false → oom' = 1#64) → (ok = true → oom' = s.core.oom) →
    (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Partial arena rewatching contract starting from `start ∈ fullArenaClauseRefs s`. -/
@[expose] def fullRewatchRangeSpec : Spec [i64, i64, i64] [.bool] :=
  fun (h, start, dst, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ start.toNat ≤ s.core.arena_len ∧
    (start.toNat < s.core.arena_len → start.toNat ∈ fullArenaClauseRefs s) ∧
    dst.toNat = s.core.arena_len ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr s r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb s r = false) ∧
    (FullMem c s ⋆ R) m ∧ fullRewatchArenaPost c F0 F_cur s R Q

/-- Inductive specification of a contiguous valid non-garb/non-shrk clause range `[lo, hi)`
inside `arena`, together with the total word length `redWords` of redundant clauses. -/
inductive MoveRangeChain (ar : List (BitVec 32)) : Nat → Nat → Nat → Prop where
  | empty {p} : MoveRangeChain ar p p 0
  | step {p hi rw} :
      p + 3 ≤ hi → (ar[p]?.getD 0#32 &&& 0x00880000#32) = 0#32 →
      3 ≤ (ar[p + 2]?.getD 0#32).toNat →
      p + 3 + (ar[p + 2]?.getD 0#32).toNat ≤ hi →
      MoveRangeChain ar (p + 3 + (ar[p + 2]?.getD 0#32).toNat) hi rw →
      MoveRangeChain ar p hi
        ((if (ar[p]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
          3 + (ar[p + 2]?.getD 0#32).toNat else 0) + rw)

/-- Clause starts visited along a `MoveRangeChain`. -/
inductive RefInChain (ar : List (BitVec 32)) : Nat → Nat → Nat → Prop where
  | head {p hi} :
      p + 3 ≤ hi → (ar[p]?.getD 0#32 &&& 0x00880000#32) = 0#32 →
      3 ≤ (ar[p + 2]?.getD 0#32).toNat →
      p + 3 + (ar[p + 2]?.getD 0#32).toNat ≤ hi →
      RefInChain ar p hi p
  | tail {p hi r} :
      p + 3 ≤ hi → (ar[p]?.getD 0#32 &&& 0x00880000#32) = 0#32 →
      3 ≤ (ar[p + 2]?.getD 0#32).toNat →
      p + 3 + (ar[p + 2]?.getD 0#32).toNat ≤ hi →
      RefInChain ar (p + 3 + (ar[p + 2]?.getD 0#32).toNat) hi r →
      RefInChain ar p hi r

theorem MoveRangeChain.le {ar : List (BitVec 32)} {lo hi rw : Nat}
    (h : MoveRangeChain ar lo hi rw) : lo ≤ hi ∧ rw ≤ hi - lo := by
  induction h with
  | empty => exact ⟨Nat.le_refl _, Nat.zero_le _⟩
  | @step p hi rw _ _ _ _ _ ih => split <;> omega

theorem MoveRangeChain.congr {ar1 ar2 : List (BitVec 32)} {lo hi rw : Nat}
    (h : MoveRangeChain ar1 lo hi rw) (heq : ∀ i, lo ≤ i → i < hi → ar2[i]? = ar1[i]?) :
    MoveRangeChain ar2 lo hi rw := by
  induction h with
  | empty => exact .empty
  | @step p hi rw h3 hfl hsz hfit _ ih =>
    have h0 : ar2[p]? = ar1[p]? := heq p (Nat.le_refl _) (by omega)
    have h2 : ar2[p + 2]? = ar1[p + 2]? := heq (p + 2) (by omega) (by omega)
    have hstp := MoveRangeChain.step h3 (by rw [h0]; exact hfl) (by rw [h2]; exact hsz)
      (by rw [h2]; exact hfit) (by rw [h2]; exact ih fun i hi1 hi2 => heq i (by omega) hi2)
    simpa [h0, h2] using hstp

theorem RefInChain.bounds {ar : List (BitVec 32)} {lo hi r : Nat}
    (h : RefInChain ar lo hi r) : lo ≤ r ∧ r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ hi := by
  induction h with
  | head _ _ _ hfit => exact ⟨Nat.le_refl _, hfit⟩
  | tail _ _ _ _ _ ih => exact ⟨by omega, ih.2⟩

theorem RefInChain.congr {ar1 ar2 : List (BitVec 32)} {lo hi r : Nat}
    (h : RefInChain ar1 lo hi r) (heq : ∀ i, lo ≤ i → i < hi → ar2[i]? = ar1[i]?) :
    RefInChain ar2 lo hi r := by
  induction h with
  | @head p hi h3 hfl hsz hfit =>
    have h0 : ar2[p]? = ar1[p]? := heq p (Nat.le_refl _) (by omega)
    have h2 : ar2[p + 2]? = ar1[p + 2]? := heq (p + 2) (by omega) (by omega)
    exact .head h3 (by rw [h0]; exact hfl) (by rw [h2]; exact hsz) (by rw [h2]; exact hfit)
  | @tail p hi r h3 hfl hsz hfit _ ih =>
    have h0 : ar2[p]? = ar1[p]? := heq p (Nat.le_refl _) (by omega)
    have h2 : ar2[p + 2]? = ar1[p + 2]? := heq (p + 2) (by omega) (by omega)
    refine .tail h3 (by rw [h0]; exact hfl) (by rw [h2]; exact hsz) (by rw [h2]; exact hfit) ?_
    have ih' := ih fun i hi1 hi2 => heq i (by omega) hi2
    simpa [h2] using ih'

/-- Uniqueness of variables assigned with a reason inside `ar[lo ..< hi)`. -/
@[expose] def MoveRedRsnUnique (_ar : List (BitVec 32)) (vals : List (BitVec 8))
    (rsns : List (BitVec 32)) (cv lo hi : Nat) : Prop :=
  ∀ r, lo ≤ r → r < hi → ∀ v1 v2 : Nat, v1 < cv → v2 < cv →
    (vals[2 * v1]?.getD 0#8 = 1#8 ∨ vals[2 * v1 + 1]?.getD 0#8 = 1#8) →
    (vals[2 * v2]?.getD 0#8 = 1#8 ∨ vals[2 * v2 + 1]?.getD 0#8 = 1#8) →
    (rsns[v1]?.getD 0xFFFFFFFF#32).toNat = r →
    (rsns[v2]?.getD 0xFFFFFFFF#32).toNat = r → v1 = v2

theorem MoveRedRsnUnique.intro {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {rsns : List (BitVec 32)} {cv lo hi : Nat}
    (h : ∀ r, lo ≤ r → r < hi → ∀ v1 v2 : Nat, v1 < cv → v2 < cv →
      (vals[2 * v1]?.getD 0#8 = 1#8 ∨ vals[2 * v1 + 1]?.getD 0#8 = 1#8) →
      (vals[2 * v2]?.getD 0#8 = 1#8 ∨ vals[2 * v2 + 1]?.getD 0#8 = 1#8) →
      (rsns[v1]?.getD 0xFFFFFFFF#32).toNat = r →
      (rsns[v2]?.getD 0xFFFFFFFF#32).toNat = r → v1 = v2) :
    MoveRedRsnUnique ar vals rsns cv lo hi := h

theorem MoveRedRsnUnique.cast_ar {ar1 ar2 : List (BitVec 32)} {vals : List (BitVec 8)}
    {rsns : List (BitVec 32)} {cv lo hi : Nat}
    (h : MoveRedRsnUnique ar1 vals rsns cv lo hi) :
    MoveRedRsnUnique ar2 vals rsns cv lo hi := h

/-- `FullMem` without `c.pArena` and `c.pScratchBuf`, allowing either `scratch_buf` or
`arena.drop` to serve as the temporary buffer `buf` in `full_move_red_end_buf_m6`. -/
@[expose] def FullMemArenaOut (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆
  FullCoreU32B c s.core ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆ c.pad

/-- Predicate characterizing an active arena reason `r0` for `v` inside `ar[fr ..< dst)`. -/
@[expose] def MoveLiveRsn (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (rsns : List (BitVec 32)) (fr dst v : Nat) : Prop :=
  let r0 := rsns[v]?.getD 0xFFFFFFFF#32
  fr ≤ r0.toNat ∧ r0.toNat < dst ∧ RefInChain ar fr dst r0.toNat ∧
  (ar[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
  ∃ j < (ar[r0.toNat + 2]?.getD 0#32).toNat,
    let lit := (ar[r0.toNat + 3 + j]?.getD 0#32).toNat
    lit / 2 = v ∧ vals[lit]?.getD 0#8 = 1#8

open Classical in
/-- Loop invariant for pass 2 of moving redundant clauses (`full_move_red_pass2_m6`). -/
@[expose] def MovePass2Inv (c : FullCfg) (s : FullState) (arOrig ar1 buf rsns1 : List (BitVec 32))
    (first_red dst bufPtr : BitVec 64) (mid rlen : Nat) (R : Mem 64 → Prop) :
    Tup Val [i64] → Mem 64 → Prop
  | (rpos, ()), m2 =>
    rpos.toNat ≤ rlen ∧ mid + rlen = dst.toNat ∧
    ∃ (ar rsns : List (BitVec 32)),
      ar.length = dst.toNat ∧ rsns.length = c.max_vars ∧
      (∀ i < mid, ar[i]? = ar1[i]?) ∧
      MoveRangeChain ar mid (mid + rpos.toNat) rpos.toNat ∧
      (rpos.toNat < rlen → RefInChain buf 0 rlen rpos.toNat) ∧
      (∀ r, RefInChain ar mid (mid + rpos.toNat) r →
        let sz := (ar[r + 2]?.getD 0#32).toNat
        (ar[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧ ar[r + 1]? = some 2#32 ∧
        ∃ rp, RefInChain buf 0 rlen rp ∧ r = mid + rp ∧
          (buf[rp + 2]?.getD 0#32).toNat = sz ∧
          ∀ j < sz, ar[r + 3 + j]? = buf[rp + 3 + j]?) ∧
      (∀ v < s.core.cur_vars,
        let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
        if MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
            (arOrig[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
          ∃ rp, RefInChain buf 0 rlen rp ∧
            (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
            buf[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
            (∀ rp2, RefInChain buf 0 rlen rp2 →
              (buf[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
              buf[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp) ∧
            if rp < rpos.toNat then
              let r' := (rsns[v]?.getD 0xFFFFFFFF#32).toNat
              r' = mid + rp ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
              RefInChain ar mid (mid + rpos.toNat) r' ∧
              (ar[r' + 2]?.getD 0#32).toNat = (buf[rp + 2]?.getD 0#32).toNat ∧
              ∀ j < (buf[rp + 2]?.getD 0#32).toNat, ar[r' + 3 + j]? = buf[rp + 3 + j]?
            else rsns[v]?.getD 0xFFFFFFFF#32 = r0
        else rsns[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32) ∧
      (array (t := i32) c.pArena ar ⋆ array (t := i32) bufPtr buf ⋆
        FullMemArenaOut c { s with core := { s.core with rsns := rsns } } ⋆ R) m2

open Classical in
/-- Spec of `full_move_red_pass2_m6`: copies redundant clauses from `buf[0 ..< rlen)` back into
`ar[mid ..< dst)`, updates `rsns` and `h->first_reducible`. -/
@[expose] def fullMoveRedPass2Spec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (h, mid, rlen, dst, bufPtr, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (arOrig ar1 buf rsns1 : List (BitVec 32))
      (first_red : BitVec 64) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      first_red.toNat ≤ mid.toNat ∧ dst.toNat ≤ c.arena_cap ∧
      rlen.toNat ≤ buf.length ∧ buf.length < 2 * dimacsBound ∧
      MoveRangeChain buf 0 rlen.toNat rlen.toNat ∧
      (∀ rp, RefInChain buf 0 rlen.toNat rp →
        let sz := (buf[rp + 2]?.getD 0#32).toNat
        (buf[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        ∃ src_c, RefInChain arOrig first_red.toNat dst.toNat src_c ∧
          (arOrig[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
          (arOrig[src_c + 2]?.getD 0#32).toNat = sz ∧
          (∀ j < sz, buf[rp + 3 + j]? = arOrig[src_c + 3 + j]?) ∧
          ((buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            (buf[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
            s.core.rsns[(buf[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
              BitVec.ofNat 32 src_c ∧
            MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat
              (buf[rp + 1]?.getD 0#32).toNat)) ∧
      MovePass2Inv c s arOrig ar1 buf rsns1 first_red dst bufPtr mid.toNat rlen.toNat R
        (0#64, ()) m ∧
      ∀ (arOut rsnsOut : List (BitVec 32)) (fred' : BitVec 64) m',
        arOut.length = dst.toNat → rsnsOut.length = c.max_vars →
        (∀ i < mid.toNat, arOut[i]? = ar1[i]?) →
        MoveRangeChain arOut mid.toNat (mid.toNat + rlen.toNat) rlen.toNat →
        (∀ r, RefInChain arOut mid.toNat (mid.toNat + rlen.toNat) r →
          let sz := (arOut[r + 2]?.getD 0#32).toNat
          (arOut[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧ arOut[r + 1]? = some 2#32 ∧
          ∃ rp, RefInChain buf 0 rlen.toNat rp ∧ r = mid.toNat + rp ∧
            (buf[rp + 2]?.getD 0#32).toNat = sz ∧
            ∀ j < sz, arOut[r + 3 + j]? = buf[rp + 3 + j]?) →
        (∀ v < s.core.cur_vars,
          let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
          if MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
              (arOrig[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
            ∃ rp, RefInChain buf 0 rlen.toNat rp ∧
              (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
              buf[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
              (∀ rp2, RefInChain buf 0 rlen.toNat rp2 →
                (buf[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
                buf[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp) ∧
              let r' := (rsnsOut[v]?.getD 0xFFFFFFFF#32).toNat
              r' = mid.toNat + rp ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
              RefInChain arOut mid.toNat (mid.toNat + rlen.toNat) r' ∧
              (arOut[r' + 2]?.getD 0#32).toNat = (buf[rp + 2]?.getD 0#32).toNat ∧
              ∀ j < (buf[rp + 2]?.getD 0#32).toNat, arOut[r' + 3 + j]? = buf[rp + 3 + j]?
          else rsnsOut[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32) →
        fred' = (if mid.toNat < dst.toNat then mid else 0xFFFFFFFF#64) →
        (array (t := i32) c.pArena arOut ⋆ array (t := i32) bufPtr buf ⋆
          FullMemArenaOut c { s with core := { s.core with rsns := rsnsOut,
                                                           first_reducible := fred' } } ⋆ R) m' →
        Q () m'

open Classical in
/-- Spec of `full_move_red_end_buf_m6`: partitions `arOrig[first_red ..< dst)` into irredundant
clauses at `[first_red, mid)` and redundant clauses at `[mid, dst)`, clears `PH_RSN`, remaps
`rsns` without collision, and updates `h->first_reducible`. -/
@[expose] def fullMoveRedEndBufSpec : Spec [i64, i64, i64, i64] [] :=
  fun (h, first_red, dst, bufPtr, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (arPre buf : List (BitVec 32)) (redWords : Nat)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      first_red.toNat ≤ dst.toNat ∧ dst.toNat ≤ c.arena_cap ∧
      arPre.length = dst.toNat ∧ redWords ≤ buf.length ∧ buf.length < 2 * dimacsBound ∧
      MoveRangeChain arPre first_red.toNat dst.toNat redWords ∧
      (∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0#8 ∨
        s.core.vals[l]?.getD 0#8 = 1#8 ∨ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      MoveRedRsnUnique arPre s.core.vals s.core.rsns s.core.cur_vars first_red.toNat dst.toNat ∧
      (array (t := i32) c.pArena arPre ⋆ array (t := i32) bufPtr buf ⋆
        FullMemArenaOut c s ⋆ R) m ∧
      ∀ (arOut bufOut rsns' : List (BitVec 32)) (fred' : BitVec 64) (mid : Nat) (m' : Mem 64),
        let s' : FullState := { s with core := { s.core with rsns := rsns',
                                                             first_reducible := fred' } }
        arOut.length = dst.toNat → bufOut.length = buf.length → rsns'.length = c.max_vars →
        first_red.toNat ≤ mid → mid ≤ dst.toNat →
        (∀ i < first_red.toNat, arOut[i]? = arPre[i]?) →
        MoveRangeChain arOut first_red.toNat mid 0 →
        MoveRangeChain arOut mid dst.toNat (dst.toNat - mid) →
        (∀ r, RefInChain arOut first_red.toNat mid r ∨ RefInChain arOut mid dst.toNat r →
          let sz := (arOut[r + 2]?.getD 0#32).toNat
          (arOut[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
          (mid ≤ r → arOut[r + 1]? = some 2#32) ∧
          ∃ src, RefInChain arPre first_red.toNat dst.toNat src ∧
            (arPre[src + 2]?.getD 0#32).toNat = sz ∧
            (∀ j < sz, arOut[r + 3 + j]? = arPre[src + 3 + j]?)) →
        (∀ v < s.core.cur_vars,
          let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
          if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
              RefInChain arPre first_red.toNat dst.toNat r0.toNat ∧
              (arPre[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
              ∃ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
                let lit := (arPre[r0.toNat + 3 + j]?.getD 0#32).toNat
                lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
          then
            let r' := (rsns'[v]?.getD 0xFFFFFFFF#32).toNat
            first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
            (RefInChain arOut first_red.toNat mid r' ∨ RefInChain arOut mid dst.toNat r') ∧
            (arOut[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
            ∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
              arOut[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?
          else rsns'[v]?.getD 0xFFFFFFFF#32 = r0) →
        fred' = (if mid < dst.toNat then BitVec.ofNat 64 mid else 0xFFFFFFFF#64) →
        (array (t := i32) c.pArena arOut ⋆ array (t := i32) bufPtr bufOut ⋆
          FullMemArenaOut c s' ⋆ R) m' →
        Q () m'

open Classical in
/-- Spec of `full_move_red_end_m6`: chooses scratch or in-place buffer (or clears `PH_RSN`
in fallback) and preserves reason soundness across `[first_red, dst)`. -/
@[expose] def fullMoveRedEndSpec : Spec [i64, i64, i64] [] :=
  fun (h, first_red, dst, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (rw0 : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      first_red.toNat < dst.toNat ∧ dst.toNat ≤ c.arena_cap ∧
      0 < rw0 ∧ MoveRangeChain s.core.arena first_red.toNat dst.toNat rw0 ∧
      (∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0#8 ∨
        s.core.vals[l]?.getD 0#8 = 1#8 ∨ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      MoveRedRsnUnique s.core.arena s.core.vals s.core.rsns s.core.cur_vars
        first_red.toNat dst.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ar' rsns' : List (BitVec 32)) (fred' : BitVec 64) (sc' : FullScratch)
          (rwOut : Nat) (m' : Mem 64),
        let s' : FullState :=
          { s with
            core := { s.core with arena := ar', rsns := rsns', first_reducible := fred' }
            scratch := sc' }
        ar'.length = c.arena_cap → rsns'.length = c.max_vars → sc'.LengthsOk c →
        sc'.extend_len = s.scratch.extend_len →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
        (∀ i < first_red.toNat, ar'[i]? = s.core.arena[i]?) →
        MoveRangeChain ar' first_red.toNat dst.toNat rwOut →
        (∀ r, RefInChain ar' first_red.toNat dst.toNat r →
          (ar'[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
          ∃ src, RefInChain s.core.arena first_red.toNat dst.toNat src ∧
            (ar'[r + 2]?.getD 0#32).toNat = (s.core.arena[src + 2]?.getD 0#32).toNat ∧
            ∀ j < (s.core.arena[src + 2]?.getD 0#32).toNat,
              ar'[r + 3 + j]? = s.core.arena[src + 3 + j]?) →
        (∀ v < s.core.cur_vars,
          let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
          if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
              RefInChain s.core.arena first_red.toNat dst.toNat r0.toNat ∧
              (s.core.arena[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
              ∃ j < (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
                let lit := (s.core.arena[r0.toNat + 3 + j]?.getD 0#32).toNat
                lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
          then
            let r' := (rsns'[v]?.getD 0xFFFFFFFF#32).toNat
            first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
            RefInChain ar' first_red.toNat dst.toNat r' ∧
            (ar'[r' + 2]?.getD 0#32).toNat = (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat ∧
            ∀ j < (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
              ar'[r' + 3 + j]? = s.core.arena[r0.toNat + 3 + j]?
          else rsns'[v]?.getD 0xFFFFFFFF#32 = r0) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 `full_arena_sweep` contract (`Proof.Spec.fullArenaSweepSpec` plus
`sc'.work_stk1 = s.scratch.work_stk1` preservation for downstream `Reduce`/`Analyze`). -/
@[expose] def step13ArenaSweepSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ (0 < s.core.cur_level → FullReasonsMarked s) ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
      fred' ni' nr' nb' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
                                wusable := wu', arena_garbage := 0#64, first_reducible := fred',
                                num_irred := ni', num_redundant := nr', num_binary := nb',
                                oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
      sc'.extend_len = s.scratch.extend_len → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → FullLastLearnedWf s' →
      FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
      (r = 0#64 ∨ r = 1#64 → oom' = 0#64) →
      (0 < s.core.cur_level → r ≠ 1#64 ∧ r ≠ 2#64 ∧
        vals' = s.core.vals ∧ lvl' = s.core.lvl ∧ trl' = s.core.trl ∧
        tp' = s.core.trail_pos ∧ te' = s.core.trail_end) →
      (r = 1#64 → s.core.cur_level = 0 ∧ s.core.trail_end < te') →
      (r = 2#64 → s.core.cur_level = 0 ∧ F0.Unsat) →
      (r = 3#64 → oom' ≠ 0#64) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 2. `Spec.XFree` Proofs & Canonical `SpecEntry` Table -/

theorem fullLitRankSpec_xfree : Spec.XFree Proof.Spec.fullLitRankSpec := by xfree
theorem fullSweepBinsRangeSpec_xfree : Spec.XFree fullSweepBinsRangeSpec := by xfree
theorem fullRewatchRangeSpec_xfree : Spec.XFree fullRewatchRangeSpec := by xfree
theorem fullRewatchArenaSpec_xfree : Spec.XFree Proof.Spec.fullRewatchArenaSpec := by xfree
theorem fullSweepBinsSpec_xfree : Spec.XFree Proof.Spec.fullSweepBinsSpec := by xfree
theorem fullSweepCopySpec_xfree : Spec.XFree Proof.Spec.fullSweepCopySpec := by xfree
theorem fullMoveRedPass2Spec_xfree : Spec.XFree fullMoveRedPass2Spec := by xfree
theorem fullMoveRedEndBufSpec_xfree : Spec.XFree fullMoveRedEndBufSpec := by xfree
theorem fullMoveRedEndSpec_xfree : Spec.XFree fullMoveRedEndSpec := by xfree
theorem step13ArenaSweepSpec_xfree : Spec.XFree step13ArenaSweepSpec := by xfree
theorem fullArenaSweepSpec_xfree : Spec.XFree Proof.Spec.fullArenaSweepSpec := by xfree
theorem fullMarkReasonsSpec_xfree : Spec.XFree Proof.Spec.fullMarkReasonsSpec := by xfree

theorem fullArenaSweepSpec_le_step13 :
    Proof.Spec.fullArenaSweepSpec.Le step13ArenaSweepSpec := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hrmk, hm, hQ⟩
  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hrmk, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
      fred' ni' nr' nb' oom' sc' m' hlen' hr hext _ hws2 hll hw' hnd' hoom hpos hr1 hr2 hr3
      hm' =>
    hQ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
      fred' ni' nr' nb' oom' sc' m' hlen' hr hext hws2 hll hw' hnd' hoom hpos hr1 hr2 hr3 hm'⟩

/-- Upstream capability dependencies for `Kissat.Src.Collect`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Watch.Spec.specs

/-- Canonical `SpecEntry` table matching `Src.Collect.fns` 1-to-1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Proof.Spec.fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins_range_m6", [i64, i64], [], fullSweepBinsRangeSpec, true⟩
  , ⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool], fullRewatchRangeSpec, true⟩
  , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool], Proof.Spec.fullRewatchArenaSpec, true⟩
  , ⟨"full_sweep_bins_m6cf", [i64], [], Proof.Spec.fullSweepBinsSpec, true⟩
  , ⟨"full_sweep_bins", [i64], [], Proof.Spec.fullSweepBinsSpec, true⟩
  , ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], Proof.Spec.fullSweepCopySpec, true⟩
  , ⟨"full_rewatch_arena", [i64, i64], [.bool], Proof.Spec.fullRewatchArenaSpec, true⟩
  , ⟨"full_move_red_pass2_m6", [i64, i64, i64, i64, i64], [], fullMoveRedPass2Spec, true⟩
  , ⟨"full_move_red_end_buf_m6", [i64, i64, i64, i64], [], fullMoveRedEndBufSpec, true⟩
  , ⟨"full_move_red_end_m6", [i64, i64, i64], [], fullMoveRedEndSpec, true⟩
  , ⟨"full_arena_sweep_m6", [i64], [i64], step13ArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons_m6", [i64, .bool], [], Proof.Spec.fullMarkReasonsSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], step13ArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons", [i64, .bool], [], Proof.Spec.fullMarkReasonsSpec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Src.Collect.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullLitRankSpec_xfree
  · exact fullSweepBinsRangeSpec_xfree
  · exact fullRewatchRangeSpec_xfree
  · exact fullRewatchArenaSpec_xfree
  · exact fullSweepBinsSpec_xfree
  · exact fullSweepBinsSpec_xfree
  · exact fullSweepCopySpec_xfree
  · exact fullRewatchArenaSpec_xfree
  · exact fullMoveRedPass2Spec_xfree
  · exact fullMoveRedEndBufSpec_xfree
  · exact fullMoveRedEndSpec_xfree
  · exact step13ArenaSweepSpec_xfree
  · exact fullMarkReasonsSpec_xfree
  · exact step13ArenaSweepSpec_xfree
  · exact fullMarkReasonsSpec_xfree

theorem has_full_lit_rank_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_lit_rank_m6" Proof.Spec.fullLitRankSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide)) fullLitRankSpec_xfree

theorem has_full_sweep_bins_range_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_sweep_bins_range_m6" fullSweepBinsRangeSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide)) fullSweepBinsRangeSpec_xfree

theorem has_full_rewatch_range_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_rewatch_range_m6" fullRewatchRangeSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide)) fullRewatchRangeSpec_xfree

theorem has_full_rewatch_arena_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_rewatch_arena_m6" Proof.Spec.fullRewatchArenaSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide)) fullRewatchArenaSpec_xfree

theorem has_full_sweep_bins_m6cf {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_sweep_bins_m6cf" Proof.Spec.fullSweepBinsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide)) fullSweepBinsSpec_xfree

theorem has_full_sweep_bins {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_sweep_bins" Proof.Spec.fullSweepBinsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide)) fullSweepBinsSpec_xfree

theorem has_full_sweep_copy {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_sweep_copy" Proof.Spec.fullSweepCopySpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 6) (by decide)) fullSweepCopySpec_xfree

theorem has_full_rewatch_arena {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_rewatch_arena" Proof.Spec.fullRewatchArenaSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 7) (by decide)) fullRewatchArenaSpec_xfree

theorem has_full_move_red_pass2_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_move_red_pass2_m6" fullMoveRedPass2Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 8) (by decide)) fullMoveRedPass2Spec_xfree

theorem has_full_move_red_end_buf_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_move_red_end_buf_m6" fullMoveRedEndBufSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 9) (by decide)) fullMoveRedEndBufSpec_xfree

theorem has_full_move_red_end_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_move_red_end_m6" fullMoveRedEndSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 10) (by decide)) fullMoveRedEndSpec_xfree

theorem has_full_arena_sweep_m6_s13 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_arena_sweep_m6" step13ArenaSweepSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 11) (by decide)) step13ArenaSweepSpec_xfree

theorem has_full_arena_sweep_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_arena_sweep_m6" Proof.Spec.fullArenaSweepSpec :=
  (has_full_arena_sweep_m6_s13 h).of_le fullArenaSweepSpec_le_step13

theorem has_full_mark_reasons_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_mark_reasons_m6" Proof.Spec.fullMarkReasonsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 12) (by decide)) fullMarkReasonsSpec_xfree

theorem has_full_arena_sweep_s13 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_arena_sweep" step13ArenaSweepSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 13) (by decide)) step13ArenaSweepSpec_xfree

theorem has_full_arena_sweep {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_arena_sweep" Proof.Spec.fullArenaSweepSpec :=
  (has_full_arena_sweep_s13 h).of_le fullArenaSweepSpec_le_step13

theorem has_full_mark_reasons {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_mark_reasons" Proof.Spec.fullMarkReasonsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 14) (by decide)) fullMarkReasonsSpec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
