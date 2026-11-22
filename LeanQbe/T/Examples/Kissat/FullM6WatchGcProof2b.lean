module

public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProofWatch
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof1
public import LeanQbe.T.Examples.Kissat.FullReduceLemmas4
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2a

/-!
# Kissat M6 `PR-W2E-lite` Proofs Part 2b: `full_move_red_end_buf_m6_wp`

Proves `full_move_red_end_buf_m6_wp` (`fullMoveRedEndBufSpec`): 2-pass irredundant-first
partitioning over `[first_red, dst)` with `buf[rlen + 1] = v` O(1) non-colliding reason
remapping and live `first_reducible` update.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6WatchGc

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat.Full
open FullReduceSpecs FullReduceHelpers
open Kraken.Bedrock2.Test
section Proof2bHelpers
open scoped FullArenaTactics FullReduceTactics M6Tactics1 M6Tactics2a

/-! ## 1. Specs & chain invariants for `full_move_red_end_buf_m6` -/

/-- Inductive witness relating every clause in `ar[lo ..< hi)` to its literals and `rsns`
mapping in `full_move_red_end_buf_m6`. -/
def MoveRedRsnUnique (_ar : List (BitVec 32)) (vals : List (BitVec 8)) (rsns : List (BitVec 32))
    (cv lo hi : Nat) : Prop :=
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

theorem RefInChain.bounds {ar : List (BitVec 32)} {lo hi r : Nat}
    (h : RefInChain ar lo hi r) : lo ≤ r ∧ r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ hi := by
  induction h with
  | head _ _ _ hfit => exact ⟨Nat.le_refl _, hfit⟩
  | tail h3 hfl hsz hfit _ ih => exact ⟨by omega, ih.2⟩

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

open Classical in
/-- Spec of `full_move_red_end_buf_m6`: partitions `arOrig[first_red ..< dst)` into irredundant
clauses at `[first_red, mid)` and redundant clauses at `[mid, dst)`, clears `PH_RSN`, remaps
`rsns` cleanly without collision, and updates `h->first_reducible`. -/
def fullMoveRedEndBufSpec : Spec [i64, i64, i64, i64] [] :=
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
theorem fullMoveRedEndBufSpec.intro {h first_red dst bufPtr : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} (c : FullCfg) (s : FullState) (arPre buf : List (BitVec 32))
    (redWords : Nat) (R : Mem 64 → Prop) (hh : h = c.hdr) (hlen : s.LengthsOk c)
    (hfr : first_red.toNat ≤ dst.toNat) (hdst : dst.toNat ≤ c.arena_cap)
    (harP : arPre.length = dst.toNat) (hrw : redWords ≤ buf.length)
    (hbuf : buf.length < 2 * dimacsBound)
    (hmv : MoveRangeChain arPre first_red.toNat dst.toNat redWords)
    (hdom : ∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0#8 ∨
      s.core.vals[l]?.getD 0#8 = 1#8 ∨ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (huniq : MoveRedRsnUnique arPre s.core.vals s.core.rsns s.core.cur_vars
      first_red.toNat dst.toNat)
    (hm : (array (t := i32) c.pArena arPre ⋆ array (t := i32) bufPtr buf ⋆
      FullMemArenaOut c s ⋆ R) m)
    (hQ : ∀ (arOut bufOut rsns' : List (BitVec 32)) (fred' : BitVec 64) (mid : Nat)
        (m' : Mem 64),
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
      Q () m') :
    fullMoveRedEndBufSpec (h, first_red, dst, bufPtr, ()) m Q X :=
  ⟨c, s, arPre, buf, redWords, R, hh, hlen, hfr, hdst, harP, hrw, hbuf, hmv, hdom, huniq, hm, hQ⟩

private theorem bv32_clear_rsn_props (h : BitVec 32) :
    ((h &&& ~~~0x00200000#32) &&& 0x00200000#32) = 0#32 ∧
    ((h &&& ~~~0x00200000#32) &&& 0x00880000#32) = (h &&& 0x00880000#32) ∧
    ((h &&& ~~~0x00200000#32) &&& 0x00400000#32) = (h &&& 0x00400000#32) := by
  refine ⟨by rw [BitVec.and_assoc,
      show (~~~0x00200000#32 &&& 0x00200000#32) = 0#32 by decide, BitVec.and_zero],
    by rw [BitVec.and_assoc,
      show (~~~0x00200000#32 &&& 0x00880000#32) = 0x00880000#32 by decide],
    by rw [BitVec.and_assoc,
      show (~~~0x00200000#32 &&& 0x00400000#32) = 0x00400000#32 by decide]⟩

private theorem moveRangeChain_head_inv {ar : List (BitVec 32)} {p hi rw : Nat}
    (h : MoveRangeChain ar p hi rw) (hlt : p < hi) :
    p + 3 ≤ hi ∧ (ar[p]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
    3 ≤ (ar[p + 2]?.getD 0#32).toNat ∧
    p + 3 + (ar[p + 2]?.getD 0#32).toNat ≤ hi ∧
    let rw_step := if (ar[p]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
      3 + (ar[p + 2]?.getD 0#32).toNat else 0
    rw_step ≤ rw ∧
    MoveRangeChain ar (p + 3 + (ar[p + 2]?.getD 0#32).toNat) hi (rw - rw_step) := by
  cases h with
  | empty => omega
  | @step _ _ rw1 h3 hfl hsz hfit htl =>
    exact ⟨h3, hfl, hsz, hfit, Nat.le_add_right _ _, by simpa using htl⟩

private theorem refInChain_head_inv {ar : List (BitVec 32)} {lo hi r : Nat}
    (hr : RefInChain ar lo hi r) :
    r + 3 ≤ hi ∧ (ar[r]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
    3 ≤ (ar[r + 2]?.getD 0#32).toNat ∧ r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ hi := by
  induction hr with
  | head h3 hfl hsz hfit => exact ⟨h3, hfl, hsz, hfit⟩
  | tail _ _ _ _ _ ih => exact ih

private theorem refInChain_iff_head {ar : List (BitVec 32)} {p hi r : Nat}
    (h3 : p + 3 ≤ hi) (hfl : (ar[p]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hsz : 3 ≤ (ar[p + 2]?.getD 0#32).toNat) (hfit : p + 3 + (ar[p + 2]?.getD 0#32).toNat ≤ hi) :
    RefInChain ar p hi r ↔
      (r = p ∨ RefInChain ar (p + 3 + (ar[p + 2]?.getD 0#32).toNat) hi r) := by
  constructor
  · intro hr; cases hr with
    | head => exact Or.inl rfl
    | tail _ _ _ _ htl => exact Or.inr htl
  · rintro (rfl | htl)
    · exact RefInChain.head h3 hfl hsz hfit
    · exact RefInChain.tail h3 hfl hsz hfit htl

private theorem moveRangeChain_append_one {ar : List (BitVec 32)} {lo p0 sz rw : Nat}
    (h : MoveRangeChain ar lo p0 rw)
    (hfl : (ar[p0]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hsz_eq : (ar[p0 + 2]?.getD 0#32).toNat = sz) (hsz3 : 3 ≤ sz) :
    let rw_step := if (ar[p0]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then 3 + sz else 0
    MoveRangeChain ar lo (p0 + 3 + sz) (rw + rw_step) ∧
    ∀ r, RefInChain ar lo (p0 + 3 + sz) r ↔ (RefInChain ar lo p0 r ∨ r = p0) := by
  revert hfl hsz_eq
  induction h with
  | empty =>
    intro hfl hsz_eq; refine ⟨?_, fun r => ?_⟩
    · have h0 := MoveRangeChain.step (ar := ar) (rw := 0)
        (by omega) hfl (by omega) (by omega) .empty
      simpa [hsz_eq, Nat.add_zero, Nat.zero_add] using h0
    · constructor
      · intro hr; cases hr with
        | head => exact Or.inr rfl
        | tail _ _ _ _ htl => exfalso; have := htl.bounds; rw [hsz_eq] at this; omega
      · rintro (hr | rfl)
        · exfalso; have := hr.bounds; omega
        · exact RefInChain.head (by omega) hfl (by omega) (by omega)
  | @step q hi1 rw0 h3q hflq hszq hfitq htl ih =>
    intro hfl hsz_eq; obtain ⟨hmv, href⟩ := ih hfl hsz_eq; refine ⟨?_, fun r => ?_⟩
    · have hst := MoveRangeChain.step (by omega) hflq hszq (by omega) hmv
      rwa [← Nat.add_assoc _ rw0 _] at hst
    · constructor
      · intro hr; cases hr with
        | head => exact Or.inl (.head h3q hflq hszq hfitq)
        | tail _ _ _ _ htlr =>
          rcases (href r).mp htlr with hl | rfl
          · exact Or.inl (.tail h3q hflq hszq hfitq hl)
          · exact Or.inr rfl
      · rintro (hr | rfl)
        · cases hr with
          | head => exact .head (by omega) hflq hszq (by omega)
          | tail _ _ _ _ htlr =>
            exact .tail (by omega) hflq hszq (by omega) ((href r).mpr (Or.inl htlr))
        · have hne : r ≠ q := by have := htl.le; omega
          exact .tail (by omega) hflq hszq (by omega) ((href _).mpr (Or.inr rfl))

private def MoveLiveRsn (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (rsns : List (BitVec 32)) (fr dst v : Nat) : Prop :=
  let r0 := rsns[v]?.getD 0xFFFFFFFF#32
  fr ≤ r0.toNat ∧ r0.toNat < dst ∧ RefInChain ar fr dst r0.toNat ∧
  (ar[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
  ∃ j < (ar[r0.toNat + 2]?.getD 0#32).toNat,
    let lit := (ar[r0.toNat + 3 + j]?.getD 0#32).toNat
    lit / 2 = v ∧ vals[lit]?.getD 0#8 = 1#8

open Classical in
private def MovePass1Inv (c : FullCfg) (s : FullState) (arPre buf0 : List (BitVec 32))
    (redWords : Nat) (first_red dst bufPtr : BitVec 64) (R : Mem 64 → Prop) :
    Tup Val [i64, i64, i64] → Mem 64 → Prop
  | (src, idst, rlen, ()), m1 =>
    first_red.toNat ≤ idst.toNat ∧ idst.toNat + rlen.toNat = src.toNat ∧ src.toNat ≤ dst.toNat ∧
    ∃ (ar buf rsns : List (BitVec 32)) (rw_rem : Nat),
      ar.length = dst.toNat ∧ buf.length = buf0.length ∧ rsns.length = c.max_vars ∧
      rlen.toNat + rw_rem = redWords ∧
      (∀ i < first_red.toNat, ar[i]? = arPre[i]?) ∧
      (∀ i, src.toNat ≤ i → i < dst.toNat → ar[i]? = arPre[i]?) ∧
      MoveRangeChain ar first_red.toNat idst.toNat 0 ∧
      MoveRangeChain ar src.toNat dst.toNat rw_rem ∧
      MoveRangeChain buf 0 rlen.toNat rlen.toNat ∧
      (src.toNat < dst.toNat → RefInChain arPre first_red.toNat dst.toNat src.toNat) ∧
      (∀ r, RefInChain ar first_red.toNat idst.toNat r →
        let sz := (ar[r + 2]?.getD 0#32).toNat
        (ar[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
        ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
          (arPre[src_c + 2]?.getD 0#32).toNat = sz ∧
          ∀ j < sz, ar[r + 3 + j]? = arPre[src_c + 3 + j]?) ∧
      (∀ rp, RefInChain buf 0 rlen.toNat rp →
        let sz := (buf[rp + 2]?.getD 0#32).toNat
        (buf[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
          (arPre[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
          (arPre[src_c + 2]?.getD 0#32).toNat = sz ∧
          (∀ j < sz, buf[rp + 3 + j]? = arPre[src_c + 3 + j]?) ∧
          ((buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            (buf[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
            s.core.rsns[(buf[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
              BitVec.ofNat 32 src_c ∧
            MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat
              (buf[rp + 1]?.getD 0#32).toNat)) ∧
      (∀ v < s.core.cur_vars,
        let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
        if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
            r0.toNat < src.toNat then
          if (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 then
            let r' := (rsns[v]?.getD 0xFFFFFFFF#32).toNat
            first_red.toNat ≤ r' ∧ r' < idst.toNat ∧ r' < 0x80000000 ∧
            RefInChain ar first_red.toNat idst.toNat r' ∧
            (ar[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
            (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
              ar[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
            (∀ rp, RefInChain buf 0 rlen.toNat rp →
              (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
              buf[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v)
          else
            rsns[v]?.getD 0xFFFFFFFF#32 = r0 ∧
            ∃ rp, RefInChain buf 0 rlen.toNat rp ∧
              (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
              buf[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
              (buf[rp + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
              (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
                buf[rp + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
              (∀ rp2, RefInChain buf 0 rlen.toNat rp2 →
                (buf[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
                buf[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp)
        else
          rsns[v]?.getD 0xFFFFFFFF#32 = r0 ∧
          ∀ rp, RefInChain buf 0 rlen.toNat rp →
            (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            buf[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v) ∧
      (array (t := i32) c.pArena ar ⋆ array (t := i32) bufPtr buf ⋆
        FullMemArenaOut c { s with core := { s.core with rsns := rsns } } ⋆ R) m1

open Classical in
def MovePass2Inv (c : FullCfg) (s : FullState) (arOrig ar1 buf rsns1 : List (BitVec 32))
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
def fullMoveRedPass2Spec : Spec [i64, i64, i64, i64, i64] [] :=
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

private theorem refInChain_gap {ar : List (BitVec 32)} {lo hi p q : Nat}
    (hp : RefInChain ar lo hi p) (hq : RefInChain ar lo hi q) (hpq : p < q) :
    p + 3 + (ar[p + 2]?.getD 0#32).toNat ≤ q := by
  induction hp with
  | @head r hi h3 hfl hsz hfit =>
    rcases (refInChain_iff_head h3 hfl hsz hfit).mp hq with rfl | htl
    · omega
    · exact htl.bounds.1
  | @tail r hi p h3 hfl hsz hfit hp_tl ih =>
    rcases (refInChain_iff_head h3 hfl hsz hfit).mp hq with rfl | htl
    · have := hp_tl.bounds.1; omega
    · exact ih htl hpq

private theorem bv32_ofNat_inj_of_lt {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (heq : BitVec.ofNat 32 a = BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat heq
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

private theorem move_liveRsn_vals_true {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {rsns : List (BitVec 32)} {fr dst v : Nat} (h : MoveLiveRsn ar vals rsns fr dst v) :
    vals[2 * v]?.getD 0#8 = 1#8 ∨ vals[2 * v + 1]?.getD 0#8 = 1#8 := by
  rcases h with ⟨_, _, _, _, j, _, hdiv, hval⟩
  let lit := (ar[(rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD 0#32).toNat
  rcases Nat.mod_two_eq_zero_or_one lit with hm | hm
  · exact Or.inl (by rw [show 2 * v = lit by omega]; exact hval)
  · exact Or.inr (by rw [show 2 * v + 1 = lit by omega]; exact hval)

private theorem refInChain_trans_tail {ar : List (BitVec 32)} {lo mid hi r : Nat}
    (h1 : RefInChain ar lo hi mid) (h2 : RefInChain ar mid hi r) :
    RefInChain ar lo hi r := by
  induction h1 with
  | head h3 hfl hsz hfit => exact h2
  | tail h3 hfl hsz hfit _ ih => exact .tail h3 hfl hsz hfit (ih h2)

private theorem refInChain_next {ar arOrig : List (BitVec 32)} {lo hi p rw : Nat}
    (hp : RefInChain arOrig lo hi p) (hmv : MoveRangeChain ar p hi rw)
    (htail_ag : ∀ i, p ≤ i → i < hi → ar[i]? = arOrig[i]?)
    (hlt : p + 3 + (ar[p + 2]?.getD 0#32).toNat < hi) :
    RefInChain arOrig lo hi (p + 3 + (ar[p + 2]?.getD 0#32).toNat) := by
  have h2eq : arOrig[p + 2]? = ar[p + 2]? := (htail_ag (p + 2) (by omega) (by omega)).symm
  obtain ⟨_, _, _, hfit, _, htl⟩ := moveRangeChain_head_inv hmv (by omega)
  obtain ⟨h3', hfl', hsz', hfit', _, _⟩ := moveRangeChain_head_inv htl hlt
  have h0' : arOrig[p + 3 + (ar[p + 2]?.getD 0#32).toNat]? =
      ar[p + 3 + (ar[p + 2]?.getD 0#32).toNat]? := (htail_ag _ (by omega) (by omega)).symm
  have h2' : arOrig[p + 3 + (ar[p + 2]?.getD 0#32).toNat + 2]? =
      ar[p + 3 + (ar[p + 2]?.getD 0#32).toNat + 2]? := (htail_ag _ (by omega) (by omega)).symm
  have hhd : RefInChain arOrig (p + 3 + (arOrig[p + 2]?.getD 0#32).toNat) hi
      (p + 3 + (arOrig[p + 2]?.getD 0#32).toNat) := by
    rw [h2eq]
    exact .head h3' (by rw [h0']; exact hfl') (by rw [h2']; exact hsz') (by rw [h2']; exact hfit')
  rw [← h2eq]
  obtain ⟨h3p, hflp, hszp, hfitp⟩ : p + 3 ≤ hi ∧ (arOrig[p]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
      3 ≤ (arOrig[p + 2]?.getD 0#32).toNat ∧ p + 3 + (arOrig[p + 2]?.getD 0#32).toNat ≤ hi := by
    rw [h2eq, ← htail_ag p (Nat.le_refl _) (by omega)]
    exact ⟨by omega, (moveRangeChain_head_inv hmv (by omega)).2.1,
      (moveRangeChain_head_inv hmv (by omega)).2.2.1, hfit⟩
  exact refInChain_trans_tail hp (.tail h3p hflp hszp hfitp hhd)

open Classical in
private theorem move_pass1_red_step {c : FullCfg} {s : FullState}
    {arPre buf0 ar buf buf' rsns : List (BitVec 32)} {redWords : Nat}
    {first_red dst bufPtr src idst rlen : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hdst_cap : dst.toNat ≤ c.arena_cap)
    (hbuf_b : buf0.length < 2 * dimacsBound)
    (hid_lo : first_red.toNat ≤ idst.toNat) (hsum : idst.toNat + rlen.toNat = src.toNat)
    (hs_lt : src.toNat < dst.toNat) (har_l : ar.length = dst.toNat)
    (hbuf0_l : buf.length = buf0.length) (hbuf'_l : buf'.length = buf0.length)
    (hrsns_l : rsns.length = c.max_vars) (hrw_sum : rlen.toNat + (redWords - rlen.toNat) = redWords)
    (hpre_ag : ∀ i < first_red.toNat, ar[i]? = arPre[i]?)
    (htail_ag : ∀ i, src.toNat ≤ i → i < dst.toNat → ar[i]? = arPre[i]?)
    (hmv_ir : MoveRangeChain ar first_red.toNat idst.toNat 0)
    (hmv_rm : MoveRangeChain ar src.toNat dst.toNat (redWords - rlen.toNat))
    (hmv_bf : MoveRangeChain buf 0 rlen.toNat rlen.toNat)
    (hir_info : ∀ r, RefInChain ar first_red.toNat idst.toNat r →
      let sz := (ar[r + 2]?.getD 0#32).toNat
      (ar[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = sz ∧
        ∀ j < sz, ar[r + 3 + j]? = arPre[src_c + 3 + j]?)
    (hbf_info : ∀ rp, RefInChain buf 0 rlen.toNat rp →
      let sz := (buf[rp + 2]?.getD 0#32).toNat
      (buf[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = sz ∧
        (∀ j < sz, buf[rp + 3 + j]? = arPre[src_c + 3 + j]?) ∧
        ((buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          (buf[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
          s.core.rsns[(buf[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            BitVec.ofNat 32 src_c ∧
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat
            (buf[rp + 1]?.getD 0#32).toNat))
    (hrsn_inv : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat < src.toNat then
        if (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 then
          let r' := (rsns[v]?.getD 0xFFFFFFFF#32).toNat
          first_red.toNat ≤ r' ∧ r' < idst.toNat ∧ r' < 0x80000000 ∧
          RefInChain ar first_red.toNat idst.toNat r' ∧
          (ar[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
          (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
            ar[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
          (∀ rp, RefInChain buf 0 rlen.toNat rp →
            (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            buf[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v)
        else
          rsns[v]?.getD 0xFFFFFFFF#32 = r0 ∧
          ∃ rp, RefInChain buf 0 rlen.toNat rp ∧
            (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
            buf[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
            (buf[rp + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
            (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
              buf[rp + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
            (∀ rp2, RefInChain buf 0 rlen.toNat rp2 →
              (buf[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
              buf[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp)
      else
        rsns[v]?.getD 0xFFFFFFFF#32 = r0 ∧
        ∀ rp, RefInChain buf 0 rlen.toNat rp →
          (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          buf[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v)
    (huniq : MoveRedRsnUnique arPre s.core.vals s.core.rsns s.core.cur_vars
      first_red.toNat dst.toNat)
    (hsrc_ref : RefInChain arPre first_red.toNat dst.toNat src.toNat)
    (hred : (ar[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32)
    (hbuf_pre : ∀ i < rlen.toNat, buf'[i]? = buf[i]?)
    (hsz_eq : (ar[src.toNat + 2]?.getD 0#32).toNat = (arPre[src.toNat + 2]?.getD 0#32).toNat)
    (hbuf_copy : ∀ k < 3 + (ar[src.toNat + 2]?.getD 0#32).toNat,
      k ≠ 0 → k ≠ 1 → buf'[rlen.toNat + k]? = ar[src.toNat + k]?)
    (hbuf_2 : buf'[rlen.toNat + 2]? = ar[src.toNat + 2]?)
    (hbuf_0fl : (buf'[rlen.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
      (buf'[rlen.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32)
    (hbuf_rsn : ((buf'[rlen.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
      ∃ v < s.core.cur_vars, buf'[rlen.toNat + 1]? = some (BitVec.ofNat 32 v) ∧
        s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat ∧
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v) ∧
      ((buf'[rlen.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 →
        ∀ v < s.core.cur_vars,
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
          (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ src.toNat))
    (hs_next : src + 3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64 =
      BitVec.ofNat 64 (src.toNat + 3 + (ar[src.toNat + 2]?.getD 0#32).toNat))
    (hr_next : rlen + (3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64) =
      BitVec.ofNat 64 (rlen.toNat + 3 + (ar[src.toNat + 2]?.getD 0#32).toNat))
    (hrnext_bd : rlen.toNat + 3 + (ar[src.toNat + 2]?.getD 0#32).toNat ≤ buf0.length)
    (hm : (array (t := i32) c.pArena ar ⋆ array (t := i32) bufPtr buf' ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsns } } ⋆ R) m) :
    MovePass1Inv c s arPre buf0 redWords first_red dst bufPtr R
      (src + 3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64, idst,
       rlen + (3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64), ()) m := by
  let sz := (ar[src.toNat + 2]?.getD 0#32).toNat
  have hmaxv := c.hmaxv; have harc := c.harena; have hcvl := hlen.core_ok.cur_vars_le
  unfold dimacsBound at hmaxv harc hbuf_b
  obtain ⟨h3, hfl, hsz3, hfit, hrw_le, htl⟩ := moveRangeChain_head_inv hmv_rm hs_lt
  have hs_n : (src + 3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64).toNat =
      src.toNat + 3 + sz := by
    rw [hs_next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr_n : (rlen + (3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64)).toNat =
      rlen.toNat + 3 + sz := by
    rw [hr_next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmv_bf_pre : MoveRangeChain buf' 0 rlen.toNat rlen.toNat :=
    hmv_bf.congr fun i _ hi => hbuf_pre i hi
  have hsz_bf : (buf'[rlen.toNat + 2]?.getD 0#32).toNat = sz :=
    congrArg (fun x => (x.getD 0#32).toNat) hbuf_2
  obtain ⟨hmv_bf', href_bf'⟩ := moveRangeChain_append_one hmv_bf_pre hbuf_0fl.1 hsz_bf hsz3
  have hmv_bf'_fin : MoveRangeChain buf' 0 (rlen.toNat + 3 + sz) (rlen.toNat + 3 + sz) := by
    rw [rw_ite_pos hbuf_0fl.2] at hmv_bf'
    rwa [← Nat.add_assoc] at hmv_bf'
  have hred_src : (ar[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := hred
  have h_rw : 3 + sz ≤ redWords - rlen.toNat := by rw [rw_ite_pos hred_src] at hrw_le; exact hrw_le
  refine ⟨hid_lo, by rw [hs_n, hr_n]; omega, by rw [hs_n]; exact hfit, ar, buf', rsns,
    redWords - (rlen.toNat + 3 + sz), har_l, hbuf'_l, hrsns_l,
    by rw [hr_n]; dsimp only [sz] at *; omega,
    hpre_ag, fun i hi1 hi2 => htail_ag i (by rw [hs_n] at hi1; omega) hi2,
    hmv_ir, by
      rw [hs_n]; dsimp only [sz]; rw [rw_ite_pos hred_src] at htl
      rwa [show redWords - rlen.toNat - (3 + (ar[src.toNat + 2]?.getD 0#32).toNat) =
        redWords - (rlen.toNat + 3 + (ar[src.toNat + 2]?.getD 0#32).toNat) by omega] at htl,
    by rw [hr_n]; exact hmv_bf'_fin,
    fun hlt => by rw [hs_n] at *; exact refInChain_next hsrc_ref hmv_rm htail_ag hlt,
    hir_info, fun rp hrp => ?_, fun v hv => ?_, hm⟩
  · rw [hr_n] at hrp; rcases (href_bf' rp).mp hrp with hrp_old | rfl
    · have hrp_old' := hrp_old.congr fun i _ hi => (hbuf_pre i hi).symm
      have hrp_bd := hrp_old'.bounds
      have hcon : buf'[rp + 2]?.getD 0#32 = buf[rp + 2]?.getD 0#32 :=
        congrArg (·.getD 0#32) (hbuf_pre (rp + 2) (by omega))
      have h0eq : buf'[rp]? = buf[rp]? := hbuf_pre rp (by omega)
      have h1eq : buf'[rp + 1]? = buf[rp + 1]? := hbuf_pre (rp + 1) (by omega)
      obtain ⟨hred_p, src_c, hsc, hred_sc, hsz_c, hlits_p, hlive_p⟩ := hbf_info rp hrp_old'
      refine ⟨by rw [h0eq]; exact hred_p, src_c, hsc, hred_sc, by rw [hcon]; exact hsz_c,
        fun j hj => by rw [hcon] at hj; rw [hbuf_pre (rp + 3 + j) (by omega)]; exact hlits_p j hj,
        fun hrsn => by rw [h0eq] at hrsn; rw [h1eq]; exact hlive_p hrsn⟩
    · refine ⟨hbuf_0fl.2, src.toNat, hsrc_ref,
        by rw [← htail_ag src.toNat (Nat.le_refl _) hs_lt]; exact hred_src,
        by rw [hsz_bf]; exact hsz_eq.symm,
        fun j hj => by
          rw [hsz_bf] at hj
          have h1 := hbuf_copy (3 + j) (by omega) (by omega) (by omega)
          rw [← Nat.add_assoc, ← Nat.add_assoc] at h1
          rw [h1, htail_ag (src.toNat + 3 + j) (by omega) (by omega)],
        fun hrsn => ?_⟩
      obtain ⟨v, hv, hbp1, hrsn_v, hlive_v⟩ := hbuf_rsn.1 hrsn
      have hv_lt32 : v < 2 ^ 32 := by omega
      have hbp_nat : (buf'[rlen.toNat + 1]?.getD 0#32).toNat = v := by
        rw [hbp1, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv_lt32]
      simpa [hbp_nat] using ⟨hv, hrsn_v, hlive_v⟩
  · dsimp only; rw [hr_n, hs_n]
    let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
    have hr0_def : r0.toNat = (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat := rfl
    have hpre_v := hrsn_inv v hv; dsimp only at hpre_v
    have hnot_new : ∀ (hlt_n : ¬ (MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat
        dst.toNat v ∧ r0.toNat < src.toNat)),
        r0.toNat ≠ src.toNat → ∀ rp, RefInChain buf' 0 (rlen.toNat + 3 + sz) rp →
          (buf'[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          buf'[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v := fun hlt_n hne rp hrp hrsn => by
      rw [rw_ite_neg hlt_n] at hpre_v
      rcases (href_bf' rp).mp hrp with hrp_old | rfl
      · have hrp_old' := hrp_old.congr fun i _ hi => (hbuf_pre i hi).symm
        have hrp_bd := hrp_old'.bounds
        rw [hbuf_pre rp (by omega)] at hrsn; rw [hbuf_pre (rp + 1) (by omega)]
        exact hpre_v.2 rp hrp_old' hrsn
      · obtain ⟨v1, hv1, hbp1, hrsn1, _⟩ := hbuf_rsn.1 hrsn
        rw [hbp1, Option.getD_some]; intro heq
        have hv1_eq := bv32_ofNat_inj_of_lt (by omega) (by omega) heq
        apply hne; dsimp only [r0]
        rw [← hv1_eq, hrsn1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hlive_v : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v
    · have hgap := fun hlt => refInChain_gap hsrc_ref hlive_v.2.2.1 hlt
      by_cases hlt_old : r0.toNat < src.toNat
      · have hlt_new : r0.toNat < src.toNat + 3 + sz := by omega
        rw [rw_ite_pos ⟨hlive_v, hlt_old⟩] at hpre_v
        rw [rw_ite_pos ⟨hlive_v, hlt_new⟩]
        by_cases hir : (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32
        · rw [rw_ite_pos hir] at hpre_v ⊢
          refine ⟨hpre_v.1, hpre_v.2.1, hpre_v.2.2.1, hpre_v.2.2.2.1, hpre_v.2.2.2.2.1,
            hpre_v.2.2.2.2.2.1, fun rp hrp hrsn => ?_⟩
          rcases (href_bf' rp).mp hrp with hrp_old | rfl
          · have hrp_old' := hrp_old.congr fun i _ hi => (hbuf_pre i hi).symm
            have hrp_bd := hrp_old'.bounds
            rw [hbuf_pre rp (by omega)] at hrsn; rw [hbuf_pre (rp + 1) (by omega)]
            exact hpre_v.2.2.2.2.2.2 rp hrp_old' hrsn
          · obtain ⟨v1, hv1, hbp1, hrsn1, _⟩ := hbuf_rsn.1 hrsn
            rw [hbp1, Option.getD_some]; intro heq
            have hv1_eq := bv32_ofNat_inj_of_lt (by omega) (by omega) heq
            have heqs : r0.toNat = src.toNat := by
              dsimp only [r0]
              rw [← hv1_eq, hrsn1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            omega
        · rw [rw_ite_neg hir] at hpre_v ⊢
          obtain ⟨hr_eq, rp0, hrp0, hrsn0, hbp0, hsz0, hlits0, huniq0⟩ := hpre_v
          have hrp0_bd := hrp0.bounds
          refine ⟨hr_eq, rp0,
            (href_bf' rp0).mpr (Or.inl (hrp0.congr fun i _ hi => hbuf_pre i hi)),
            by rw [hbuf_pre rp0 (by omega)]; exact hrsn0,
            by rw [hbuf_pre (rp0 + 1) (by omega)]; exact hbp0,
            by rw [hbuf_pre (rp0 + 2) (by omega)]; exact hsz0,
            fun j hj => by rw [hbuf_pre (rp0 + 3 + j) (by omega)]; exact hlits0 j hj,
            fun rp2 hrp2 hrsn2 hbp2 => ?_⟩
          rcases (href_bf' rp2).mp hrp2 with hrp2_old | rfl
          · have hrp2_old' := hrp2_old.congr fun i _ hi => (hbuf_pre i hi).symm
            have hrp2_bd := hrp2_old'.bounds
            rw [hbuf_pre rp2 (by omega)] at hrsn2; rw [hbuf_pre (rp2 + 1) (by omega)] at hbp2
            exact huniq0 rp2 hrp2_old' hrsn2 hbp2
          · obtain ⟨v1, hv1, hbp1, hrsn1, _⟩ := hbuf_rsn.1 hrsn2
            rw [hbp1, Option.getD_some] at hbp2
            have hv1_eq := bv32_ofNat_inj_of_lt (by omega) (by omega) hbp2
            have heqs : r0.toNat = src.toNat := by
              dsimp only [r0]
              rw [← hv1_eq, hrsn1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            omega
      · by_cases heq_src : r0.toNat = src.toNat
        · have hlt_new : r0.toNat < src.toNat + 3 + sz := by omega
          have hred_r0 : (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := by
            rw [heq_src, ← htail_ag src.toNat (Nat.le_refl _) hs_lt]; exact hred_src
          rw [rw_ite_neg (fun ⟨_, h⟩ => hlt_old h)] at hpre_v
          rw [rw_ite_pos ⟨hlive_v, hlt_new⟩, rw_ite_neg hred_r0]
          have hfl_rsn : (buf'[rlen.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 := fun h0 =>
            hbuf_rsn.2 h0 v hv hlive_v heq_src
          obtain ⟨v1, hv1, hbp1, hrsn1, hlive1⟩ := hbuf_rsn.1 hfl_rsn
          have hv1_eq : v1 = v := huniq src.toNat (by omega : first_red.toNat ≤ src.toNat)
            hs_lt v1 v hv1 hv (move_liveRsn_vals_true hlive1) (move_liveRsn_vals_true hlive_v)
            (by rw [hrsn1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) heq_src
          rw [hv1_eq] at hbp1
          refine ⟨hpre_v.1, rlen.toNat, (href_bf' rlen.toNat).mpr (Or.inr rfl), hfl_rsn,
            by rw [hbp1]; rfl,
            by rw [hsz_bf]; dsimp only [sz]; rw [hsz_eq, heq_src],
            fun j hj => by
              rw [heq_src, ← hsz_eq] at hj
              have h1 := hbuf_copy (3 + j) (by omega) (by omega) (by omega)
              rw [← Nat.add_assoc, ← Nat.add_assoc] at h1
              rw [h1, htail_ag (src.toNat + 3 + j) (by omega) (by omega), heq_src],
            fun rp2 hrp2 hrsn2 hbp2 => ?_⟩
          rcases (href_bf' rp2).mp hrp2 with hrp2_old | rfl
          · have hrp2_old' := hrp2_old.congr fun i _ hi => (hbuf_pre i hi).symm
            have hrp2_bd := hrp2_old'.bounds
            rw [hbuf_pre rp2 (by omega)] at hrsn2; rw [hbuf_pre (rp2 + 1) (by omega)] at hbp2
            exact absurd hbp2 (hpre_v.2 rp2 hrp2_old' hrsn2)
          · rfl
        · have hnot_n : ¬ (MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat
              dst.toNat v ∧ r0.toNat < src.toNat + 3 + sz) := fun ⟨_, hlt⟩ => by
            have := hgap (by dsimp only [MoveLiveRsn] at hlive_v; omega)
            rw [← hsz_eq] at this; omega
          rw [rw_ite_neg hnot_n]; rw [rw_ite_neg (fun ⟨_, h⟩ => hlt_old h)] at hpre_v
          exact ⟨hpre_v.1, hnot_new (fun ⟨_, h⟩ => hlt_old h) heq_src⟩
    · rw [rw_ite_neg (fun ⟨hlv, _⟩ => hlive_v hlv)] at hpre_v ⊢
      refine ⟨hpre_v.1, fun rp hrp hrsn => ?_⟩
      rcases (href_bf' rp).mp hrp with hrp_old | rfl
      · have hrp_old' := hrp_old.congr fun i _ hi => (hbuf_pre i hi).symm
        have hrp_bd := hrp_old'.bounds
        rw [hbuf_pre rp (by omega)] at hrsn; rw [hbuf_pre (rp + 1) (by omega)]
        exact hpre_v.2 rp hrp_old' hrsn
      · obtain ⟨v1, hv1, hbp1, _, hlive1⟩ := hbuf_rsn.1 hrsn
        rw [hbp1, Option.getD_some]; intro heq
        have hv1_eq := bv32_ofNat_inj_of_lt (by omega) (by omega) heq
        rw [hv1_eq] at hlive1; exact hlive_v hlive1

open Classical in
private theorem move_pass1_irred_step {c : FullCfg} {s : FullState}
    {arPre buf0 ar ar' buf rsns rsns' : List (BitVec 32)} {redWords : Nat}
    {first_red dst bufPtr src idst rlen : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hdst_cap : dst.toNat ≤ c.arena_cap)
    (hid_lo : first_red.toNat ≤ idst.toNat) (hsum : idst.toNat + rlen.toNat = src.toNat)
    (hs_lt : src.toNat < dst.toNat) (har_l : ar.length = dst.toNat)
    (har'_l : ar'.length = dst.toNat) (hbuf0_l : buf.length = buf0.length)
    (_hrsns_l : rsns.length = c.max_vars) (hrsns'_l : rsns'.length = c.max_vars)
    (hrw_sum : rlen.toNat + (redWords - rlen.toNat) = redWords)
    (hpre_ag : ∀ i < first_red.toNat, ar[i]? = arPre[i]?)
    (htail_ag : ∀ i, src.toNat ≤ i → i < dst.toNat → ar[i]? = arPre[i]?)
    (hmv_ir : MoveRangeChain ar first_red.toNat idst.toNat 0)
    (hmv_rm : MoveRangeChain ar src.toNat dst.toNat (redWords - rlen.toNat))
    (hmv_bf : MoveRangeChain buf 0 rlen.toNat rlen.toNat)
    (hir_info : ∀ r, RefInChain ar first_red.toNat idst.toNat r →
      let sz := (ar[r + 2]?.getD 0#32).toNat
      (ar[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = sz ∧
        ∀ j < sz, ar[r + 3 + j]? = arPre[src_c + 3 + j]?)
    (hbf_info : ∀ rp, RefInChain buf 0 rlen.toNat rp →
      let sz := (buf[rp + 2]?.getD 0#32).toNat
      (buf[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = sz ∧
        (∀ j < sz, buf[rp + 3 + j]? = arPre[src_c + 3 + j]?) ∧
        ((buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          (buf[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
          s.core.rsns[(buf[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            BitVec.ofNat 32 src_c ∧
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat
            (buf[rp + 1]?.getD 0#32).toNat))
    (hrsn_inv : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat < src.toNat then
        if (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 then
          let r' := (rsns[v]?.getD 0xFFFFFFFF#32).toNat
          first_red.toNat ≤ r' ∧ r' < idst.toNat ∧ r' < 0x80000000 ∧
          RefInChain ar first_red.toNat idst.toNat r' ∧
          (ar[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
          (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
            ar[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
          (∀ rp, RefInChain buf 0 rlen.toNat rp →
            (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            buf[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v)
        else
          rsns[v]?.getD 0xFFFFFFFF#32 = r0 ∧
          ∃ rp, RefInChain buf 0 rlen.toNat rp ∧
            (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
            buf[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
            (buf[rp + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
            (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
              buf[rp + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
            (∀ rp2, RefInChain buf 0 rlen.toNat rp2 →
              (buf[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
              buf[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp)
      else
        rsns[v]?.getD 0xFFFFFFFF#32 = r0 ∧
        ∀ rp, RefInChain buf 0 rlen.toNat rp →
          (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          buf[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v)
    (hsrc_ref : RefInChain arPre first_red.toNat dst.toNat src.toNat)
    (hnred : (ar[src.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32)
    (har_pre : ∀ i < idst.toNat, ar'[i]? = ar[i]?)
    (har_tail : ∀ i, src.toNat + 3 + (ar[src.toNat + 2]?.getD 0#32).toNat ≤ i →
      i < dst.toNat → ar'[i]? = ar[i]?)
    (hsz_eq : (ar[src.toNat + 2]?.getD 0#32).toNat = (arPre[src.toNat + 2]?.getD 0#32).toNat)
    (har_lits : ∀ j < (ar[src.toNat + 2]?.getD 0#32).toNat,
      ar'[idst.toNat + 3 + j]? = arPre[src.toNat + 3 + j]?)
    (har_2 : ar'[idst.toNat + 2]? = ar[src.toNat + 2]?)
    (har_0fl : (ar'[idst.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      (ar'[idst.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
      (ar'[idst.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32)
    (hrsns_upd : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat = src.toNat then
        rsns'[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 idst.toNat
      else rsns'[v]?.getD 0xFFFFFFFF#32 = rsns[v]?.getD 0xFFFFFFFF#32)
    (hs_next : src + 3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64 =
      BitVec.ofNat 64 (src.toNat + 3 + (ar[src.toNat + 2]?.getD 0#32).toNat))
    (hid_next : idst + (3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64) =
      BitVec.ofNat 64 (idst.toNat + 3 + (ar[src.toNat + 2]?.getD 0#32).toNat))
    (hm : (array (t := i32) c.pArena ar' ⋆ array (t := i32) bufPtr buf ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) m) :
    MovePass1Inv c s arPre buf0 redWords first_red dst bufPtr R
      (src + 3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64,
       idst + (3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64), rlen, ()) m := by
  let sz := (ar[src.toNat + 2]?.getD 0#32).toNat
  have hmaxv := c.hmaxv; have harc := c.harena; have hcvl := hlen.core_ok.cur_vars_le
  unfold dimacsBound at hmaxv harc
  obtain ⟨h3, hfl, hsz3, hfit, hrw_le, htl⟩ := moveRangeChain_head_inv hmv_rm hs_lt
  have hs_n : (src + 3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64).toNat =
      src.toNat + 3 + sz := by
    rw [hs_next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hid_n : (idst + (3#64 + (ar[src.toNat + 2]?.getD 0#32).setWidth 64)).toNat =
      idst.toNat + 3 + sz := by
    rw [hid_next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmv_ir_pre : MoveRangeChain ar' first_red.toNat idst.toNat 0 :=
    hmv_ir.congr fun i _ hi => har_pre i hi
  have hsz_id : (ar'[idst.toNat + 2]?.getD 0#32).toNat = sz :=
    congrArg (fun x => (x.getD 0#32).toNat) har_2
  obtain ⟨hmv_ir', href_ir'⟩ := moveRangeChain_append_one hmv_ir_pre har_0fl.2.1 hsz_id hsz3
  have hmv_ir'_fin : MoveRangeChain ar' first_red.toNat (idst.toNat + 3 + sz) 0 := by
    dsimp only [sz] at hmv_ir' ⊢
    rw [rw_ite_neg (not_not.mpr har_0fl.2.2)] at hmv_ir'
    simpa [← Nat.add_assoc] using hmv_ir'
  have hmv_rm' : MoveRangeChain ar' (src.toNat + 3 + sz) dst.toNat (redWords - rlen.toNat) := by
    rw [rw_ite_neg (not_not.mpr hnred)] at htl
    exact htl.congr fun i hi1 hi2 => har_tail i hi1 hi2
  refine ⟨by rw [hid_n]; omega, by rw [hs_n, hid_n]; omega, by rw [hs_n]; exact hfit,
    ar', buf, rsns', redWords - rlen.toNat, har'_l, hbuf0_l, hrsns'_l, hrw_sum,
    fun i hi => (har_pre i (by omega)).trans (hpre_ag i hi),
    fun i hi1 hi2 => (har_tail i (by rw [hs_n] at hi1; exact hi1) hi2).trans
      (htail_ag i (by rw [hs_n] at hi1; omega) hi2),
    by rw [hid_n]; exact hmv_ir'_fin, by rw [hs_n]; exact hmv_rm', hmv_bf,
    fun hlt => by rw [hs_n] at *; exact refInChain_next hsrc_ref hmv_rm htail_ag hlt,
    fun r hr => ?_, hbf_info, fun v hv => ?_, hm⟩
  · rw [hid_n] at hr; rcases (href_ir' r).mp hr with hr_old | rfl
    · have hr_old' := hr_old.congr fun i _ hi => (har_pre i hi).symm
      have hr_bd := hr_old'.bounds
      have hcon : ar'[r + 2]?.getD 0#32 = ar[r + 2]?.getD 0#32 :=
        congrArg (·.getD 0#32) (har_pre (r + 2) (by omega))
      have h0eq : ar'[r]? = ar[r]? := har_pre r (by omega)
      obtain ⟨hrsn0, src_c, hsc, hsz_c, hlits⟩ := hir_info r hr_old'
      refine ⟨by rw [h0eq]; exact hrsn0, src_c, hsc, by rw [hcon]; exact hsz_c,
        fun j hj => by rw [hcon] at hj; rw [har_pre (r + 3 + j) (by omega)]; exact hlits j hj⟩
    · refine ⟨har_0fl.1, src.toNat, hsrc_ref, by rw [hsz_id]; exact hsz_eq.symm,
        fun j hj => by rw [hsz_id] at hj; exact har_lits j hj⟩
  · dsimp only; rw [hs_n, hid_n]
    let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
    have hr0_def : r0.toNat = (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat := rfl
    have hpre_v := hrsn_inv v hv; have hup_v := hrsns_upd v hv
    dsimp only at hpre_v hup_v
    by_cases hlive_v : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v
    · have hgap := fun hlt => refInChain_gap hsrc_ref hlive_v.2.2.1 hlt
      by_cases hlt_old : r0.toNat < src.toNat
      · have hlt_new : r0.toNat < src.toNat + 3 + sz := by omega
        rw [rw_ite_pos ⟨hlive_v, hlt_old⟩] at hpre_v
        rw [rw_ite_neg (fun ⟨_, heq⟩ => by dsimp only [r0] at hlt_old; omega)] at hup_v
        rw [rw_ite_pos ⟨hlive_v, hlt_new⟩]
        by_cases hir : (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32
        · rw [rw_ite_pos hir] at hpre_v ⊢
          obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpre_v
          have h4_bd : (rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
              (ar[(rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD 0#32).toNat ≤ idst.toNat :=
            h4.bounds.2
          have hr'_eq := congrArg BitVec.toNat hup_v
          rw [hr'_eq]
          refine ⟨h1, by omega, h3,
            (href_ir' _).mpr (Or.inl (h4.congr fun i _ hi => har_pre i hi)), ?_, fun j hj => ?_, h7⟩
          · rw [har_pre _ (by omega)]; exact h5
          · rw [har_pre _ (by rw [h5] at h4_bd; omega)]; exact h6 j hj
        · rw [rw_ite_neg hir] at hpre_v ⊢
          rw [hup_v]; exact hpre_v
      · by_cases heq_src : r0.toNat = src.toNat
        · have hlt_new : r0.toNat < src.toNat + 3 + sz := by omega
          have hirred_r0 : (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 := by
            rw [heq_src, ← htail_ag src.toNat (Nat.le_refl _) hs_lt]; exact hnred
          rw [rw_ite_neg (fun ⟨_, h⟩ => hlt_old h)] at hpre_v
          rw [rw_ite_pos ⟨hlive_v, heq_src⟩] at hup_v
          rw [rw_ite_pos ⟨hlive_v, hlt_new⟩, rw_ite_pos hirred_r0]
          have hid_nat : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat = idst.toNat := by
            rw [hup_v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          dsimp only [r0] at heq_src ⊢
          refine ⟨by rw [hid_nat]; exact hid_lo, by rw [hid_nat]; omega,
            by rw [hid_nat]; omega, by rw [hid_nat]; exact (href_ir' idst.toNat).mpr (Or.inr rfl),
            by rw [hid_nat, heq_src, hsz_id]; exact hsz_eq,
            fun j hj => by rw [hid_nat, heq_src]; rw [heq_src, ← hsz_eq] at hj; exact har_lits j hj,
            hpre_v.2⟩
        · have hnot_n : ¬ (MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat
              dst.toNat v ∧ r0.toNat < src.toNat + 3 + sz) := fun ⟨_, hlt⟩ => by
            have := hgap (by dsimp only [MoveLiveRsn] at hlive_v; omega)
            rw [← hsz_eq] at this; omega
          rw [rw_ite_neg (fun ⟨_, h⟩ => hlt_old h)] at hpre_v
          rw [rw_ite_neg (fun ⟨_, heq⟩ => heq_src heq)] at hup_v
          rw [rw_ite_neg hnot_n, hup_v]; exact hpre_v
    · rw [rw_ite_neg (fun ⟨hlv, _⟩ => hlive_v hlv)] at hpre_v ⊢
      rw [rw_ite_neg (fun ⟨hlv, _⟩ => hlive_v hlv)] at hup_v
      rw [hup_v]; exact hpre_v

private theorem refInChain_next_of_prefix {ar : List (BitVec 32)} {lo hi p rw : Nat}
    (hmv : MoveRangeChain ar lo hi rw) (hp : RefInChain ar lo hi p)
    (hlt : p + 3 + (ar[p + 2]?.getD 0#32).toNat < hi) :
    RefInChain ar lo hi (p + 3 + (ar[p + 2]?.getD 0#32).toNat) := by
  revert rw hmv hlt
  induction hp with
  | @head q hi h3 hfl hsz hfit =>
    intro _rw hmv hlt; cases hmv with
    | empty => omega
    | @step _ _ _ _ _ _ _ htl =>
      obtain ⟨h3', hfl', hsz', hfit', _, _⟩ := moveRangeChain_head_inv htl hlt
      exact .tail h3 hfl hsz hfit (.head h3' hfl' hsz' hfit')
  | @tail q hi r h3 hfl hsz hfit _ ih =>
    intro _rw hmv hlt; cases hmv with
    | empty => omega
    | @step _ _ _ _ _ _ _ htl => exact .tail h3 hfl hsz hfit (ih htl hlt)

open Classical in
private theorem move_pass2_step {c : FullCfg} {s : FullState}
    {arOrig ar1 ar ar' buf rsns1 rsns rsns' : List (BitVec 32)}
    {first_red dst bufPtr rpos : BitVec 64} {mid rlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hdst_cap : dst.toNat ≤ c.arena_cap)
    (hm_sum : mid + rlen = dst.toNat) (_hrp_lt : rpos.toNat < rlen)
    (har_l : ar.length = dst.toNat) (har'_l : ar'.length = dst.toNat)
    (hrsns_l : rsns.length = c.max_vars) (hrsns'_l : rsns'.length = c.max_vars)
    (hpre_ag : ∀ i < mid, ar[i]? = ar1[i]?)
    (har_pre : ∀ i < mid + rpos.toNat, ar'[i]? = ar[i]?)
    (hmv_2 : MoveRangeChain ar mid (mid + rpos.toNat) rpos.toNat)
    (hmv_bf : MoveRangeChain buf 0 rlen rlen)
    (h2_info : ∀ r, RefInChain ar mid (mid + rpos.toNat) r →
      let sz := (ar[r + 2]?.getD 0#32).toNat
      (ar[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧ ar[r + 1]? = some 2#32 ∧
      ∃ rp, RefInChain buf 0 rlen rp ∧ r = mid + rp ∧
        (buf[rp + 2]?.getD 0#32).toNat = sz ∧
        ∀ j < sz, ar[r + 3 + j]? = buf[rp + 3 + j]?)
    (hbf_info : ∀ rp, RefInChain buf 0 rlen rp →
      (buf[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ((buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
        let v := (buf[rp + 1]?.getD 0#32).toNat
        v < s.core.cur_vars ∧
        MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        (arOrig[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
          0x00400000#32) ≠ 0#32))
    (hrsn_inv : ∀ v < s.core.cur_vars,
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
      else rsns[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32)
    (hrp_ref : RefInChain buf 0 rlen rpos.toNat)
    (har_0fl : (ar'[mid + rpos.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      (ar'[mid + rpos.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
      (ar'[mid + rpos.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32)
    (har_1 : ar'[mid + rpos.toNat + 1]? = some 2#32)
    (har_2 : ar'[mid + rpos.toNat + 2]? = buf[rpos.toNat + 2]?)
    (har_lits : ∀ j < (buf[rpos.toNat + 2]?.getD 0#32).toNat,
      ar'[mid + rpos.toNat + 3 + j]? = buf[rpos.toNat + 3 + j]?)
    (hrsns_upd : ((buf[rpos.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
      let v := (buf[rpos.toNat + 1]?.getD 0#32).toNat
      v < s.core.cur_vars ∧
      rsns'[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 (mid + rpos.toNat) ∧
      ∀ v' < s.core.cur_vars, v' ≠ v →
        rsns'[v']?.getD 0xFFFFFFFF#32 = rsns[v']?.getD 0xFFFFFFFF#32) ∧
      ((buf[rpos.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 → rsns' = rsns))
    (hr_next : rpos + (3#64 + (buf[rpos.toNat + 2]?.getD 0#32).setWidth 64) =
      BitVec.ofNat 64 (rpos.toNat + 3 + (buf[rpos.toNat + 2]?.getD 0#32).toNat))
    (hfit_2 : rpos.toNat + 3 + (buf[rpos.toNat + 2]?.getD 0#32).toNat ≤ rlen)
    (hm : (array (t := i32) c.pArena ar' ⋆ array (t := i32) bufPtr buf ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) m) :
    MovePass2Inv c s arOrig ar1 buf rsns1 first_red dst bufPtr mid rlen R
      (rpos + (3#64 + (buf[rpos.toNat + 2]?.getD 0#32).setWidth 64), ()) m := by
  let sz := (buf[rpos.toNat + 2]?.getD 0#32).toNat
  have harc := c.harena; have hmaxv := c.hmaxv; have hcvl := hlen.core_ok.cur_vars_le
  unfold dimacsBound at harc hmaxv
  obtain ⟨_, _, hsz3_b, _⟩ := refInChain_head_inv hrp_ref
  have hr_n : (rpos + (3#64 + (buf[rpos.toNat + 2]?.getD 0#32).setWidth 64)).toNat =
      rpos.toNat + 3 + sz := by
    rw [hr_next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmv_2_pre : MoveRangeChain ar' mid (mid + rpos.toNat) rpos.toNat :=
    hmv_2.congr fun i _ hi => har_pre i hi
  have hsz_ar : (ar'[mid + rpos.toNat + 2]?.getD 0#32).toNat = sz :=
    congrArg (fun x => (x.getD 0#32).toNat) har_2
  obtain ⟨hmv_2', href_2'⟩ := moveRangeChain_append_one hmv_2_pre har_0fl.2.1 hsz_ar hsz3_b
  have hmv_2'_fin :
      MoveRangeChain ar' mid (mid + (rpos.toNat + 3 + sz)) (rpos.toNat + 3 + sz) := by
    rw [rw_ite_pos har_0fl.2.2] at hmv_2'
    rw [show mid + (rpos.toNat + 3 + sz) = mid + rpos.toNat + 3 + sz by omega,
      show rpos.toNat + 3 + sz = rpos.toNat + (3 + sz) by omega]
    exact hmv_2'
  refine ⟨by rw [hr_n]; exact hfit_2, hm_sum, ar', rsns', har'_l, hrsns'_l,
    fun i hi => (har_pre i (by omega)).trans (hpre_ag i hi),
    by rw [hr_n]; exact hmv_2'_fin,
    fun hlt => by
      have hlt' : rpos.toNat + 3 + (buf[rpos.toNat + 2]?.getD 0#32).toNat < rlen := by
        rw [← hr_n]; exact hlt
      have hnex := refInChain_next_of_prefix hmv_bf hrp_ref hlt'
      rwa [← hr_n] at hnex,
    fun r hr => ?_, fun v hv => ?_, hm⟩
  · rw [hr_n, ← show mid + rpos.toNat + 3 + sz = mid + (rpos.toNat + 3 + sz) by omega] at hr
    rcases (href_2' r).mp hr with hr_old | rfl
    · have hr_old' := hr_old.congr fun i _ hi => (har_pre i hi).symm
      have hr_bd := hr_old'.bounds
      have hcon : ar'[r + 2]?.getD 0#32 = ar[r + 2]?.getD 0#32 :=
        congrArg (·.getD 0#32) (har_pre (r + 2) (by omega))
      have h0eq : ar'[r]? = ar[r]? := har_pre r (by omega)
      have h1eq : ar'[r + 1]? = ar[r + 1]? := har_pre (r + 1) (by omega)
      obtain ⟨h0, h1, rp, hrp, rfl, hszp, hlits⟩ := h2_info r hr_old'
      refine ⟨by rw [h0eq]; exact h0, by rw [h1eq]; exact h1, rp, hrp, rfl,
        by rw [hcon]; exact hszp,
        fun j hj => by
          rw [hcon] at hj; rw [har_pre (mid + rp + 3 + j) (by omega)]; exact hlits j hj⟩
    · refine ⟨har_0fl.1, har_1, rpos.toNat, hrp_ref, rfl, by rw [hsz_ar],
        fun j hj => by rw [hsz_ar] at hj; exact har_lits j hj⟩
  · dsimp only; rw [hr_n]
    have hpre_v := hrsn_inv v hv; dsimp only at hpre_v
    by_cases hcond : MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        (arOrig[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
    · rw [rw_ite_pos hcond] at hpre_v ⊢
      obtain ⟨rp, hrp, hflp, hbp1, huniqp, hbranch⟩ := hpre_v
      refine ⟨rp, hrp, hflp, hbp1, huniqp, ?_⟩
      by_cases hrp_lt_old : rp < rpos.toNat
      · have hrp_lt_new : rp < rpos.toNat + 3 + sz := by omega
        rw [rw_ite_pos hrp_lt_old] at hbranch; rw [rw_ite_pos hrp_lt_new]
        obtain ⟨hr_eq, hlt_d, hlt8, href_r, hsz_r, hlits_r⟩ := hbranch
        have hcon_rs : rsns'[v]?.getD 0xFFFFFFFF#32 = rsns[v]?.getD 0xFFFFFFFF#32 := by
          by_cases hrsn_b : (buf[rpos.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32
          · obtain ⟨hv0, _, hoth⟩ := hrsns_upd.1 hrsn_b
            have hv_ne : v ≠ (buf[rpos.toNat + 1]?.getD 0#32).toNat := fun heq => by
              rw [← heq] at hv0
              have hbp1' : buf[rpos.toNat + 1]?.getD 0#32 = BitVec.ofNat 32 v := by
                rw [heq]; apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (buf[rpos.toNat + 1]?.getD 0#32).isLt]
              have heq_rp := huniqp rpos.toNat hrp_ref hrsn_b hbp1'
              omega
            exact hoth v hv hv_ne
          · rw [hrsns_upd.2 (not_not.mp hrsn_b)]
        have hr_bd := href_r.bounds
        have hr'_nat : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat = mid + rp := by
          rw [hcon_rs]; exact hr_eq
        refine ⟨hr'_nat, by omega, by omega, ?_, ?_, ?_⟩
        · have href_pre := href_r.congr fun i _ hi => har_pre i hi
          rw [hcon_rs, ← show mid + rpos.toNat + 3 + sz = mid + (rpos.toNat + 3 + sz) by omega]
          exact (href_2' _).mpr (Or.inl href_pre)
        · rw [hcon_rs, har_pre _ (by omega)]; exact hsz_r
        · intro j hj
          rw [hcon_rs, har_pre _ (by omega)]; exact hlits_r j hj
      · by_cases hrp_eq : rp = rpos.toNat
        · have hrp_lt_new : rp < rpos.toNat + 3 + sz := by omega
          rw [rw_ite_neg hrp_lt_old] at hbranch; rw [rw_ite_pos hrp_lt_new]
          obtain ⟨_, hrs_v, _⟩ := hrsns_upd.1 (by rw [← hrp_eq]; exact hflp)
          have hv_eq : (buf[rpos.toNat + 1]?.getD 0#32).toNat = v := by
            have hv_lt32 : (buf[rpos.toNat + 1]?.getD 0#32).toNat < 2 ^ 32 :=
              (buf[rpos.toNat + 1]?.getD 0#32).isLt
            have h1 := congrArg BitVec.toNat hbp1
            rw [hrp_eq] at h1; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
          rw [hv_eq] at hrs_v
          have hr'_nat : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat = mid + rpos.toNat := by
            rw [hrs_v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          refine ⟨by rw [hr'_nat, hrp_eq], by omega, by omega, ?_, ?_, ?_⟩
          · rw [hr'_nat, ← show mid + rpos.toNat + 3 + sz = mid + (rpos.toNat + 3 + sz) by omega]
            exact (href_2' (mid + rpos.toNat)).mpr (Or.inr rfl)
          · rw [hr'_nat, hrp_eq, hsz_ar]
          · intro j hj; rw [hr'_nat, hrp_eq]; rw [hrp_eq] at hj; exact har_lits j hj
        · have hgap := refInChain_gap hrp_ref hrp (by omega)
          have hrp_not_new : ¬ rp < rpos.toNat + 3 + sz := by omega
          rw [rw_ite_neg hrp_lt_old] at hbranch; rw [rw_ite_neg hrp_not_new]
          by_cases hrsn_b : (buf[rpos.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32
          · obtain ⟨hv0, _, hoth⟩ := hrsns_upd.1 hrsn_b
            have hv_ne : v ≠ (buf[rpos.toNat + 1]?.getD 0#32).toNat := fun heq => by
              have hbp1' : buf[rpos.toNat + 1]?.getD 0#32 = BitVec.ofNat 32 v := by
                rw [heq]; apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (buf[rpos.toNat + 1]?.getD 0#32).isLt]
              have heq_rp := huniqp rpos.toNat hrp_ref hrsn_b hbp1'
              exact hrp_eq heq_rp.symm
            rw [hoth v hv hv_ne, hbranch]
          · rw [hrsns_upd.2 (not_not.mp hrsn_b), hbranch]
    · rw [rw_ite_neg hcond] at hpre_v ⊢
      by_cases hrsn_b : (buf[rpos.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32
      · obtain ⟨hv0, _, hoth⟩ := hrsns_upd.1 hrsn_b
        have hv_ne : v ≠ (buf[rpos.toNat + 1]?.getD 0#32).toNat := fun heq => by
          have h1 := (hbf_info rpos.toNat hrp_ref).2 hrsn_b
          dsimp only at h1; rw [← heq] at h1; exact hcond h1.2
        rw [hoth v hv hv_ne, hpre_v]
      · rw [hrsns_upd.2 (not_not.mp hrsn_b), hpre_v]

private theorem bv_i8_slt0_eq_1 {b : BitVec 8} (hb : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    ((0#32).slt (b.signExtend 32) = true ↔ b = 1#8) ∧
    ((0#32).slt (b.signExtend 32) = false ↔ b ≠ 1#8) := by
  rcases hb with rfl | rfl | rfl <;> decide

open Classical in
private theorem move_pass1_to_pass2 {c : FullCfg} {s : FullState}
    {arPre buf ar rsns : List (BitVec 32)} {redWords : Nat}
    {first_red dst bufPtr idst rlen : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (_hlen : s.LengthsOk c) (_hdst_cap : dst.toNat ≤ c.arena_cap)
    (_hid_lo : first_red.toNat ≤ idst.toNat) (hsum : idst.toNat + rlen.toNat = dst.toNat)
    (har_l : ar.length = dst.toNat) (hrsns_l : rsns.length = c.max_vars)
    (_hrw_sum : rlen.toNat + (redWords - rlen.toNat) = redWords)
    (_hpre_ag : ∀ i < first_red.toNat, ar[i]? = arPre[i]?)
    (_hmv_ir : MoveRangeChain ar first_red.toNat idst.toNat 0)
    (_hmv_rm : MoveRangeChain ar dst.toNat dst.toNat (redWords - rlen.toNat))
    (hmv_bf : MoveRangeChain buf 0 rlen.toNat rlen.toNat)
    (_hbf_info : ∀ rp, RefInChain buf 0 rlen.toNat rp →
      let sz := (buf[rp + 2]?.getD 0#32).toNat
      (buf[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = sz ∧
        (∀ j < sz, buf[rp + 3 + j]? = arPre[src_c + 3 + j]?) ∧
        ((buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          (buf[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
          s.core.rsns[(buf[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            BitVec.ofNat 32 src_c ∧
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat
            (buf[rp + 1]?.getD 0#32).toNat))
    (hrsn_inv : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat < dst.toNat then
        if (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 then
          let r' := (rsns[v]?.getD 0xFFFFFFFF#32).toNat
          first_red.toNat ≤ r' ∧ r' < idst.toNat ∧ r' < 0x80000000 ∧
          RefInChain ar first_red.toNat idst.toNat r' ∧
          (ar[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
          (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
            ar[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
          (∀ rp, RefInChain buf 0 rlen.toNat rp →
            (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            buf[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v)
        else
          rsns[v]?.getD 0xFFFFFFFF#32 = r0 ∧
          ∃ rp, RefInChain buf 0 rlen.toNat rp ∧
            (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
            buf[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
            (buf[rp + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
            (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
              buf[rp + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
            (∀ rp2, RefInChain buf 0 rlen.toNat rp2 →
              (buf[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
              buf[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp)
      else
        rsns[v]?.getD 0xFFFFFFFF#32 = r0 ∧
        ∀ rp, RefInChain buf 0 rlen.toNat rp →
          (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          buf[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v)
    (hm : (array (t := i32) c.pArena ar ⋆ array (t := i32) bufPtr buf ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsns } } ⋆ R) m) :
    MovePass2Inv c s arPre ar buf rsns first_red dst bufPtr idst.toNat rlen.toNat R
      (0#64, ()) m := by
  refine ⟨Nat.zero_le _, hsum, ar, rsns, har_l, hrsns_l, fun _ _ => rfl, .empty,
    fun hlt => let ⟨h3, hfl, hsz, hfit, _, _⟩ := moveRangeChain_head_inv hmv_bf hlt
               .head h3 hfl hsz hfit,
    fun r hr => by exfalso; have := hr.bounds; simp only [BitVec.toNat_ofNat] at this; omega,
    fun v hv => ?_, hm⟩
  dsimp only
  have hpre_v := hrsn_inv v hv; dsimp only at hpre_v
  by_cases hcond : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
      (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
  · have hlt : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat := hcond.1.2.1
    rw [rw_ite_pos ⟨hcond.1, hlt⟩, rw_ite_neg hcond.2] at hpre_v
    rw [rw_ite_pos hcond]
    obtain ⟨hr_eq, rp, hrp, hrsn_p, hbp, _, _, huniq_p⟩ := hpre_v
    exact ⟨rp, hrp, hrsn_p, hbp, huniq_p, by rw [rw_ite_neg (by simp)]; exact hr_eq⟩
  · rw [rw_ite_neg hcond]

private def Pass1RedPost (c : FullCfg) (s : FullState) (arPre ar1 buf1 rsns1 : List (BitVec 32))
    (first_red dst bufPtr src rlen : BitVec 64) (buf0Len sz : Nat) (R : Mem 64 → Prop) :
    Tup Val [] → Mem 64 → Prop
  | (), m' =>
    ∃ buf' : List (BitVec 32), buf'.length = buf0Len ∧
      (∀ i < rlen.toNat, buf'[i]? = buf1[i]?) ∧
      (∀ k < 3 + sz, k ≠ 0 → k ≠ 1 → buf'[rlen.toNat + k]? = ar1[src.toNat + k]?) ∧
      buf'[rlen.toNat + 2]? = ar1[src.toNat + 2]? ∧
      (buf'[rlen.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
      (buf'[rlen.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      (((buf'[rlen.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
        ∃ v < s.core.cur_vars, buf'[rlen.toNat + 1]? = some (BitVec.ofNat 32 v) ∧
          s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat ∧
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v) ∧
       ((buf'[rlen.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 →
        ∀ v < s.core.cur_vars,
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
          (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ src.toNat)) ∧
      (array (t := i32) c.pArena ar1 ⋆ array (t := i32) bufPtr buf' ⋆
        FullMemArenaOut c { s with core := { s.core with rsns := rsns1 } } ⋆ R) m'

open Classical in
private def Pass1IrredPost (c : FullCfg) (s : FullState) (arPre ar1 buf1 rsns1 : List (BitVec 32))
    (first_red dst bufPtr src idst : BitVec 64) (sz : Nat) (R : Mem 64 → Prop) :
    Tup Val [] → Mem 64 → Prop
  | (), m' =>
    ∃ ar' rsns' : List (BitVec 32), ar'.length = dst.toNat ∧ rsns'.length = c.max_vars ∧
      (∀ i < idst.toNat, ar'[i]? = ar1[i]?) ∧
      (∀ i, src.toNat + 3 + sz ≤ i → i < dst.toNat → ar'[i]? = ar1[i]?) ∧
      (∀ j < sz, ar'[idst.toNat + 3 + j]? = arPre[src.toNat + 3 + j]?) ∧
      ar'[idst.toNat + 2]? = ar1[src.toNat + 2]? ∧
      (∀ v < s.core.cur_vars,
        let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
        if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
            r0.toNat = src.toNat then
          rsns'[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 idst.toNat
        else rsns'[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32) ∧
      (array (t := i32) c.pArena ar' ⋆ array (t := i32) bufPtr buf1 ⋆
        FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) m'

/-! ## 2. `full_move_red_end_buf_m6_wp` -/

private theorem bv64_add_lt {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem bv64_add2_gen_lt {a b c : BitVec 64}
    (h : a.toNat + b.toNat + c.toNat < 2 ^ 64) :
    (a + b + c).toNat = a.toNat + b.toNat + c.toNat := by
  rw [bv64_add_lt (by rw [bv64_add_lt (by omega)]; omega), bv64_add_lt (by omega)]

end Proof2bHelpers

open scoped M6Tactics1 M6Tactics2a

local macro "m6_tiny_simp" : tactic =>
  `(tactic| simp only [
      LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk,
      LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_and_eq,
      LeanQbe.T.wp_let_cmp_eq, LeanQbe.T.wp_let_zext_eq, LeanQbe.T.wp_let_sext_eq,
      LeanQbe.T.wp_let_trunc_eq,
      LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.sgt,
      LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
      LeanQbe.T.Ty.hasFloat_vec, LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree,
      LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne,
      LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_sgt_eq,
      LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.liftCmp,
      cast_eq, Bool.false_eq_true, ite_false, ite_true,
      BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul])

local macro "m6_tiny_lets" : tactic =>
  `(tactic| (
    try m6_unmdata
    try repeat (first | (m6_strip; try m6_tiny_simp) | m6_tiny_simp)))

local macro "m6_fast" : tactic => `(tactic| (m6_tiny_lets; m6_steps))

open Classical in
private theorem pass1_irred_miss_rsn
    {arPre ar1 rsns1 : List (BitVec 32)} {s : FullState}
    {first_red dst src : BitVec 64} {sz : Nat}
    (hsz_eq : (ar1[src.toNat + 2]?.getD 0#32).toNat =
      (arPre[src.toNat + 2]?.getD 0#32).toNat)
    (hsz_def : sz = (ar1[src.toNat + 2]?.getD 0#32).toNat)
    (htail_ag : ∀ i, src.toNat ≤ i → i < dst.toNat → ar1[i]? = arPre[i]?)
    (hsrc_lt : src.toNat + 3 + sz ≤ dst.toNat)
    (hdom : ∀ l < 2 * s.core.cur_vars,
      s.core.vals[l]?.getD 0#8 = 0#8 ∨ s.core.vals[l]?.getD 0#8 = 1#8 ∨
      s.core.vals[l]?.getD 0#8 = 255#8)
    (hrsns_eq_src : ∀ v < s.core.cur_vars,
      (rsns1[v]?.getD 0xFFFFFFFF#32).toNat = src.toNat ↔
      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat = src.toNat)
    (hmiss : ∀ j < sz,
      let lit := (ar1[src.toNat + 3 + j]?.getD 0#32).toNat
      ¬ (lit / 2 < s.core.cur_vars ∧
        (0#32).slt ((s.core.vals[lit]?.getD 0#8).signExtend 32) = true ∧
        (rsns1[lit / 2]?.getD 0xFFFFFFFF#32).toNat = src.toNat))
    {v : Nat} (hv : v < s.core.cur_vars)
    (hlv : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v)
    (heq_s : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat = src.toNat) : False := by
  obtain ⟨_, _, _, _, j, hj_sz, hdiv, hval1⟩ := hlv
  rw [heq_s, ← hsz_eq, ← hsz_def] at hj_sz
  have hae := htail_ag (src.toNat + 3 + j) (by omega) (by omega)
  have hlit_eq : (ar1[src.toNat + 3 + j]?.getD 0#32).toNat =
      (arPre[src.toNat + 3 + j]?.getD 0#32).toNat :=
    congrArg (fun x : Option (BitVec 32) => (x.getD 0#32).toNat) hae
  rw [heq_s] at hdiv hval1
  apply hmiss j hj_sz
  refine ⟨by rw [hlit_eq, hdiv]; exact hv, ?_, ?_⟩
  · have hlt_2cv : (arPre[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars := by omega
    rw [hlit_eq, (bv_i8_slt0_eq_1 (hdom _ hlt_2cv)).1]; exact hval1
  · rw [hlit_eq, hdiv]; exact (hrsns_eq_src v hv).mpr heq_s

private theorem pass2_bf_info_lift
    {s : FullState} {arPre buf1 : List (BitVec 32)} {first_red dst : BitVec 64}
    {rlen : Nat} (hdst_lt32 : dst.toNat < 2 ^ 32)
    (hbf_info : ∀ rp, RefInChain buf1 0 rlen rp →
      (buf1[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = (buf1[rp + 2]?.getD 0#32).toNat ∧
        (∀ j < (buf1[rp + 2]?.getD 0#32).toNat,
          buf1[rp + 3 + j]? = arPre[src_c + 3 + j]?) ∧
        ((buf1[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          (buf1[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
          s.core.rsns[(buf1[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            BitVec.ofNat 32 src_c ∧
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat
            (buf1[rp + 1]?.getD 0#32).toNat)) :
    ∀ rp, RefInChain buf1 0 rlen rp →
      (buf1[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ((buf1[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
        let v := (buf1[rp + 1]?.getD 0#32).toNat
        v < s.core.cur_vars ∧
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
          0x00400000#32) ≠ 0#32) := fun rp hrp => by
  obtain ⟨hred_p, src_c, hsc, hred_sc, _, _, hlive_p⟩ := hbf_info rp hrp
  have hsc_bd := hsc.bounds
  have hsc_lt32 : src_c < 2 ^ 32 := by omega
  refine ⟨hred_p, fun hrsn => ?_⟩
  obtain ⟨hv, hrs_eq, hlv⟩ := hlive_p hrsn
  refine ⟨hv, hlv, ?_⟩
  have hrs_nat : (s.core.rsns[(buf1[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat =
      src_c := by
    rw [hrs_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsc_lt32]
  rwa [hrs_nat]

private theorem pass2_fin_clauses_helper
    {arPre ar1 ar2 buf1 : List (BitVec 32)} {first_red idst dst : BitVec 64} {rlen : Nat}
    (hmid_eq : idst.toNat + rlen = dst.toNat)
    (h2_pre : ∀ i < idst.toNat, ar2[i]? = ar1[i]?)
    (hir_info : ∀ r, RefInChain ar1 first_red.toNat idst.toNat r →
      (ar1[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = (ar1[r + 2]?.getD 0#32).toNat ∧
        (∀ j < (ar1[r + 2]?.getD 0#32).toNat, ar1[r + 3 + j]? = arPre[src_c + 3 + j]?))
    (h2_info : ∀ r, RefInChain ar2 idst.toNat (idst.toNat + rlen) r →
      (ar2[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧ ar2[r + 1]? = some 2#32 ∧
      ∃ rp, RefInChain buf1 0 rlen rp ∧ r = idst.toNat + rp ∧
        (buf1[rp + 2]?.getD 0#32).toNat = (ar2[r + 2]?.getD 0#32).toNat ∧
        (∀ j < (ar2[r + 2]?.getD 0#32).toNat, ar2[r + 3 + j]? = buf1[rp + 3 + j]?))
    (hbf_info : ∀ rp, RefInChain buf1 0 rlen rp →
      (buf1[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = (buf1[rp + 2]?.getD 0#32).toNat ∧
        (∀ j < (buf1[rp + 2]?.getD 0#32).toNat, buf1[rp + 3 + j]? = arPre[src_c + 3 + j]?) ∧
        True) :
    ∀ r, RefInChain ar2 first_red.toNat idst.toNat r ∨ RefInChain ar2 idst.toNat dst.toNat r →
      let sz := (ar2[r + 2]?.getD 0#32).toNat
      (ar2[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      (idst.toNat ≤ r → ar2[r + 1]? = some 2#32) ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = sz ∧
        (∀ j < sz, ar2[r + 3 + j]? = arPre[src_c + 3 + j]?) := by
  rintro r (hl | hr)
  · have hl' := hl.congr fun i _ hi => (h2_pre i hi).symm
    have hr_bd := hl'.bounds
    obtain ⟨hfl0, src_c, hsc, hszc, hlitsc⟩ := hir_info r hl'
    have h2eq : ar2[r + 2]? = ar1[r + 2]? := h2_pre (r + 2) (by omega)
    refine ⟨by rw [h2_pre r (by omega)]; exact hfl0, fun hge => by omega, src_c, hsc,
      by rw [h2eq]; exact hszc, fun j hj => by
        rw [h2eq] at hj; rw [h2_pre _ (by omega)]; exact hlitsc j hj⟩
  · rw [← hmid_eq] at hr
    obtain ⟨hfl0, h1eq, rp, hrp, rfl, hszp, hlitsp⟩ := h2_info r hr
    obtain ⟨_, src_c, hsc, _, hszc, hlits_bf, _⟩ := hbf_info rp hrp
    refine ⟨hfl0, fun _ => h1eq, src_c, hsc, by rw [hszc, hszp], fun j hj => by
      have hj' : j < (buf1[rp + 2]?.getD 0#32).toNat := by rwa [hszp]
      rw [hlitsp j hj, hlits_bf j hj']⟩

open Classical in
private theorem pass2_fin_rsns_helper
    {s : FullState} {arPre ar1 ar2 buf1 rsns1 rsns2 : List (BitVec 32)}
    {first_red idst dst : BitVec 64} {rlen : Nat}
    (hid_lo : first_red.toNat ≤ idst.toNat)
    (hmid_eq : idst.toNat + rlen = dst.toNat)
    (h2_pre : ∀ i < idst.toNat, ar2[i]? = ar1[i]?)
    (hrsn_inv : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat < dst.toNat then
        if (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 then
          let r' := (rsns1[v]?.getD 0xFFFFFFFF#32).toNat
          first_red.toNat ≤ r' ∧ r' < idst.toNat ∧ r' < 0x80000000 ∧
          RefInChain ar1 first_red.toNat idst.toNat r' ∧
          (ar1[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
          (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
            ar1[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
          (∀ rp, RefInChain buf1 0 rlen rp →
            (buf1[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            buf1[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v)
        else
          rsns1[v]?.getD 0xFFFFFFFF#32 = r0 ∧
          ∃ rp, RefInChain buf1 0 rlen rp ∧
            (buf1[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
            buf1[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
            (buf1[rp + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
            (∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
              buf1[rp + 3 + j]? = arPre[r0.toNat + 3 + j]?) ∧
            ∀ rp', RefInChain buf1 0 rlen rp' →
              (buf1[rp']?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
              buf1[rp' + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp' = rp
      else
        rsns1[v]?.getD 0xFFFFFFFF#32 = r0 ∧
        ∀ rp, RefInChain buf1 0 rlen rp →
          (buf1[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          buf1[rp + 1]?.getD 0#32 ≠ BitVec.ofNat 32 v)
    (hrsn_inv2 : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
        ∃ rp, RefInChain buf1 0 rlen rp ∧
          (buf1[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          buf1[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
          (∀ rp', RefInChain buf1 0 rlen rp' →
            (buf1[rp']?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            buf1[rp' + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp' = rp) ∧
          let r' := (rsns2[v]?.getD 0xFFFFFFFF#32).toNat
          r' = idst.toNat + rp ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
          RefInChain ar2 idst.toNat (idst.toNat + rlen) r' ∧
          (ar2[r' + 2]?.getD 0#32).toNat = (buf1[rp + 2]?.getD 0#32).toNat ∧
          ∀ j < (buf1[rp + 2]?.getD 0#32).toNat, ar2[r' + 3 + j]? = buf1[rp + 3 + j]?
      else rsns2[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32) :
    ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
          RefInChain arPre first_red.toNat dst.toNat r0.toNat ∧
          (arPre[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          ∃ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
            let lit := (arPre[r0.toNat + 3 + j]?.getD 0#32).toNat
            lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
      then
        let r' := (rsns2[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
        (RefInChain ar2 first_red.toNat idst.toNat r' ∨
          RefInChain ar2 idst.toNat dst.toNat r') ∧
        (ar2[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
          ar2[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?
      else rsns2[v]?.getD 0xFFFFFFFF#32 = r0 := fun v hv => by
  dsimp only
  let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
  have hinv2 := hrsn_inv2 v hv; have hinv1 := hrsn_inv v hv
  dsimp only at hinv2 hinv1
  by_cases hlive : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v
  · have hlive' : first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
        RefInChain arPre first_red.toNat dst.toNat r0.toNat ∧
        (arPre[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
        ∃ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
          let lit := (arPre[r0.toNat + 3 + j]?.getD 0#32).toNat
          lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8 := hlive
    rw [rw_ite_pos hlive']
    by_cases hred_r0 : (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
    · rw [rw_ite_pos ⟨hlive, hred_r0⟩] at hinv2
      rw [rw_ite_pos ⟨hlive, hlive.2.1⟩, rw_ite_neg hred_r0] at hinv1
      obtain ⟨rp, hrp, hrsn_p, hbp, huniq_p, hbr⟩ := hinv2
      obtain ⟨_, rp1, hrp1, hrsn_p1, hbp1, hsz_p1, hlits_p1, _⟩ := hinv1
      have heq_rp : rp = rp1 := (huniq_p rp1 hrp1 hrsn_p1 hbp1).symm
      subst heq_rp
      obtain ⟨hr_eq, hlt_d, hlt8, href_r, hsz_r, hlits_r⟩ := hbr
      refine ⟨by omega, hlt_d, hlt8, Or.inr (by rwa [← hmid_eq]),
        by rw [hsz_r, hsz_p1], fun j hj => by rw [hlits_r j (by omega), hlits_p1 j hj]⟩
    · rw [rw_ite_neg (fun h => hred_r0 h.2)] at hinv2
      rw [rw_ite_pos ⟨hlive, hlive.2.1⟩, rw_ite_pos (not_not.mp hred_r0)] at hinv1
      obtain ⟨hlo, hlt_id, hlt8, href_r, hsz_r, hlits_r, _⟩ := hinv1
      have hr_bd := href_r.bounds
      have hcon2 : rsns2[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32 := hinv2
      refine ⟨by rw [hcon2]; exact hlo, by rw [hcon2]; omega, by rw [hcon2]; exact hlt8,
        Or.inl (by rw [hcon2]; exact href_r.congr fun i _ hi => h2_pre i hi),
        by rw [hcon2, h2_pre _ (by omega)]; exact hsz_r,
        fun j hj => by rw [hcon2, h2_pre _ (by omega)]; exact hlits_r j hj⟩
  · have hnot_live : ¬ (first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
        RefInChain arPre first_red.toNat dst.toNat r0.toNat ∧
        (arPre[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
        ∃ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
          let lit := (arPre[r0.toNat + 3 + j]?.getD 0#32).toNat
          lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8) := hlive
    rw [rw_ite_neg hnot_live]
    rw [rw_ite_neg (fun h => hlive h.1)] at hinv2 hinv1
    exact hinv2.trans hinv1.1

private theorem pass1_red_hit_helper
    {arPre ar1 buf_k buf1 : List (BitVec 32)} {s : FullState}
    {first_red dst src rlen : BitVec 64} {buf0Len sz : Nat} {hdr lit32 v32 : BitVec 32}
    {i : BitVec 32}
    (har1_l : ar1.length = dst.toNat) (hsrc_sz : src.toNat + 3 + sz ≤ dst.toNat)
    (hs_lt : src.toNat < dst.toNat)
    (hsrc_ref : RefInChain arPre first_red.toNat dst.toNat src.toNat)
    (hfl : (ar1[src.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hred : (ar1[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32)
    (hrsn_ne : (ar1[src.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32)
    (hsz_def : sz = (ar1[src.toNat + 2]?.getD 0#32).toNat)
    (hsz_eq : (ar1[src.toNat + 2]?.getD 0#32).toNat =
      (arPre[src.toNat + 2]?.getD 0#32).toNat)
    (htail_ag : ∀ k, src.toNat ≤ k → k < dst.toNat → ar1[k]? = arPre[k]?)
    (hi_lt : i.toNat < sz)
    (hlit32_get : lit32 = ar1[src.toNat + 3 + i.toNat]'(by omega))
    (hv_def : v32.toNat = lit32.toNat / 2)
    (hv_lt : v32.toNat < s.core.cur_vars)
    (hval_eq1 : s.core.vals[lit32.toNat]?.getD 0#8 = 1#8)
    (hrs0_src : (s.core.rsns[v32.toNat]?.getD 0xFFFFFFFF#32).toNat = src.toNat)
    (hbk_l : buf_k.length = buf0Len)
    (hbk_pre : ∀ j < rlen.toNat, buf_k[j]? = buf1[j]?)
    (hbk_cp : ∀ k < 3 + sz, buf_k[rlen.toNat + k]? = ar1[src.toNat + k]?)
    (hsrc_lt232 : src.toNat < 2 ^ 32) (hr1_lt : rlen.toNat + 1 < buf_k.length)
    (_hrsz_le : rlen.toNat + 3 + sz ≤ buf_k.length)
    (_hsz_ge3 : 3 ≤ 3 + sz)
    (_hhdr_def : hdr = ar1[src.toNat]?.getD 0#32) :
    let buf' := buf_k.set (rlen.toNat + 1) v32
    buf'.length = buf0Len ∧
    (∀ j < rlen.toNat, buf'[j]? = buf1[j]?) ∧
    (∀ k < 3 + sz, k ≠ 0 → k ≠ 1 → buf'[rlen.toNat + k]? = ar1[src.toNat + k]?) ∧
    buf'[rlen.toNat + 2]? = ar1[src.toNat + 2]? ∧
    (buf'[rlen.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
    (buf'[rlen.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
    (((buf'[rlen.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
      ∃ v < s.core.cur_vars, buf'[rlen.toNat + 1]? = some (BitVec.ofNat 32 v) ∧
        s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat ∧
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v) ∧
     ((buf'[rlen.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 →
      ∀ v < s.core.cur_vars,
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ src.toNat)) := by
  dsimp only
  have hbp0 : (buf_k.set (rlen.toNat + 1) v32)[rlen.toNat]? = ar1[src.toNat]? := by
    rw [List.getElem?_set_ne (by omega)]; exact hbk_cp 0 (by omega)
  have hrs_bv0 : s.core.rsns[v32.toNat]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat := by
    apply BitVec.eq_of_toNat_eq
    have := (s.core.rsns[v32.toNat]?.getD 0xFFFFFFFF#32).isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc_lt232, hrs0_src]
  have hlive_v : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v32.toNat := by
    dsimp only [MoveLiveRsn]; rw [hrs0_src]
    refine ⟨hsrc_ref.bounds.1, hs_lt, hsrc_ref, ?_, i.toNat, ?_, ?_⟩
    · rw [← htail_ag src.toNat (Nat.le_refl _) hs_lt]; exact hrsn_ne
    · rw [← hsz_eq, ← hsz_def]; exact hi_lt
    · have hae := htail_ag (src.toNat + 3 + i.toNat) (by omega) (by omega)
      have hlt_eq : (arPre[src.toNat + 3 + i.toNat]?.getD 0#32).toNat = lit32.toNat := by
        rw [← hae, hlit32_get, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [hlt_eq]; exact ⟨hv_def.symm, hval_eq1⟩
  refine ⟨by simp [hbk_l],
    fun j hj => by rw [List.getElem?_set_ne (by omega)]; exact hbk_pre j hj,
    fun k hk hk0 hk1 => by rw [List.getElem?_set_ne (by omega)]; exact hbk_cp k hk,
    by rw [List.getElem?_set_ne (by omega)]; exact hbk_cp 2 (by omega),
    by rw [hbp0]; exact hfl, by rw [hbp0]; exact hred,
    ⟨fun _ => ⟨v32.toNat, hv_lt, by
       rw [List.getElem?_set_self hr1_lt]
       congr 1; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v32.isLt],
       hrs_bv0, hlive_v⟩,
     fun h0 => False.elim (hrsn_ne (by rwa [← hbp0]))⟩⟩

open Classical in
private theorem pass1_irred_hit_helper
    {arPre ar1 rsns1 : List (BitVec 32)} {s : FullState}
    {first_red dst src idst : BitVec 64} {sz : Nat} {lit32 v32 : BitVec 32} {i : BitVec 32}
    (har1_l : ar1.length = dst.toNat) (hsrc_sz : src.toNat + 3 + sz ≤ dst.toNat)
    (hs_lt : src.toNat < dst.toNat)
    (hsrc_ref : RefInChain arPre first_red.toNat dst.toNat src.toNat)
    (hrsn_ne : (ar1[src.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32)
    (hsz_def : sz = (ar1[src.toNat + 2]?.getD 0#32).toNat)
    (hsz_eq : (ar1[src.toNat + 2]?.getD 0#32).toNat =
      (arPre[src.toNat + 2]?.getD 0#32).toNat)
    (htail_ag : ∀ k, src.toNat ≤ k → k < dst.toNat → ar1[k]? = arPre[k]?)
    (hi_lt : i.toNat < sz)
    (hlit32_get : lit32 = ar1[src.toNat + 3 + i.toNat]'(by omega))
    (hv_def : v32.toNat = lit32.toNat / 2)
    (hv_lt : v32.toNat < s.core.cur_vars)
    (hval_eq1 : s.core.vals[lit32.toNat]?.getD 0#8 = 1#8)
    (hrs0_src : (s.core.rsns[v32.toNat]?.getD 0xFFFFFFFF#32).toNat = src.toNat)
    (_hid_lo : first_red.toNat ≤ idst.toNat)
    (huniq : MoveRedRsnUnique arPre s.core.vals s.core.rsns s.core.cur_vars
      first_red.toNat dst.toNat)
    (hid_32 : idst.setWidth 32 = BitVec.ofNat 32 idst.toNat)
    (hv_lt_r : v32.toNat < rsns1.length) :
    let rsns' := rsns1.set v32.toNat (idst.setWidth 32)
    ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat = src.toNat then
        rsns'[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 idst.toNat
      else rsns'[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32 := by
  intro rsns' v hv; dsimp only
  have hlive_v0 :
      MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v32.toNat := by
    dsimp only [MoveLiveRsn]; rw [hrs0_src]
    refine ⟨hsrc_ref.bounds.1, hs_lt, hsrc_ref, ?_, i.toNat, ?_, ?_⟩
    · rw [← htail_ag src.toNat (Nat.le_refl _) hs_lt]; exact hrsn_ne
    · rw [← hsz_eq, ← hsz_def]; exact hi_lt
    · have hae := htail_ag (src.toNat + 3 + i.toNat) (by omega) (by omega)
      have hlt_eq : (arPre[src.toNat + 3 + i.toNat]?.getD 0#32).toNat = lit32.toNat := by
        rw [← hae, hlit32_get, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [hlt_eq]; exact ⟨hv_def.symm, hval_eq1⟩
  by_cases hvv0 : v = v32.toNat
  · subst hvv0
    rw [rw_ite_pos ⟨hlive_v0, hrs0_src⟩, List.getElem?_set_self hv_lt_r, Option.getD_some, hid_32]
  · have hnot : ¬ (MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat = src.toNat) :=
      fun ⟨hlv_v, hr_v⟩ => hvv0 <| by
        exact huniq src.toNat hsrc_ref.bounds.1 hs_lt v v32.toNat hv hv_lt
          (move_liveRsn_vals_true hlv_v) (move_liveRsn_vals_true hlive_v0) hr_v hrs0_src
    rw [rw_ite_neg hnot, List.getElem?_set_ne (Ne.symm hvv0)]

open Lean Elab Tactic in
local elab "m6_to_jnz_tiny" : tactic => do
  for _ in [:100] do
    let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let _ ← evalTactic (← `(tactic| try m6_tiny_lets))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
      let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

open Classical in
theorem full_move_red_pass2_m6_wp (Γ : Env) :
    ∀ a m Q X, fullMoveRedPass2Spec a m Q X →
      Func.wp Γ full_move_red_pass2_m6_body a m Q X := by
  rintro ⟨h, mid, rlen, dst, bufPtr, ⟨⟩⟩ m Q X
    ⟨c, s, arPre, ar1, buf1, rsns1, first_red, R, rfl, hlen, hid_lo, hdst_cap, hrlen_buf,
     hbuf_b, hmv_bf, hbf_info, hinit, hQ⟩
  have harc := c.harena; have hmaxv := c.hmaxv; have hcvl := hlen.core_ok.cur_vars_le
  have hrl := hlen.core_ok.rsns_len
  unfold dimacsBound at harc hmaxv hbuf_b
  have hmem_d : ∃ ar_d rsns_d : List (BitVec 32),
      (FullMemArenaOut c { s with core := { s.core with rsns := rsns_d } } ⋆
        array (t := i32) c.pArena ar_d ⋆ array (t := i32) bufPtr buf1 ⋆ R) m :=
    let ⟨_, _, ar_d, rsns_d, _, _, _, _, _, _, _, hm_d⟩ := hinit
    ⟨ar_d, rsns_d, sep_ac hm_d⟩
  rcases hmem_d with ⟨ar_d, rsns_d, hm_d⟩
  m6_tiny_lets; m6_c0_steps
  clear ar_d rsns_d hm_d
  m6_nojoin
  refine wp_loop_inv
    (MovePass2Inv c s arPre ar1 buf1 rsns1 first_red dst bufPtr mid.toNat rlen.toNat R)
    (fun (rpos, ()) _ => rlen.toNat - rpos.toNat)
    (fun J2 hLoop2 => by m6_tiny_lets; m6_nojoin; exact hLoop2 (0#64, ()) m hinit) ?_
  rintro J2 ⟨rpos, ⟨⟩⟩ m2
    ⟨hrp_le, hm_sum, ar2, rsns2, har2_l, hrsns2_l, h2_pre, hmv_2, hrp_fn, h2_info, hrsn_inv2,
     hm2⟩ hLoop2
  have hbf_info2 : ∀ rp, RefInChain buf1 0 rlen.toNat rp →
      (buf1[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ((buf1[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
        let v := (buf1[rp + 1]?.getD 0#32).toNat
        v < s.core.cur_vars ∧
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
          0x00400000#32) ≠ 0#32) :=
    pass2_bf_info_lift (by omega) hbf_info
  m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
  · have hrp_lt : rpos.toNat < rlen.toNat := by c0_cond hc; exact hc
    have hrp_ref := hrp_fn hrp_lt
    obtain ⟨h3_b, hfl_b, hsz3_b, hfit_b⟩ := refInChain_head_inv hrp_ref
    have hr2_eq : (rpos + 2#64).toNat = rpos.toNat + 2 := bv64_add2_lt (by omega)
    have hb0_lt : rpos.toNat < buf1.length := by omega
    have hb2_lt : (rpos + 2#64).toNat < buf1.length := by rw [hr2_eq]; omega
    let hdr_b := buf1[rpos.toNat]'(by omega)
    let sz32_b := buf1[(rpos + 2#64).toNat]'hb2_lt
    let sz_b := sz32_b.toNat
    have hszb_get : sz32_b = buf1[rpos.toNat + 2]'(by omega) := by
      dsimp only [sz32_b]; simp only [hr2_eq]
    have hsz_b_def : sz_b = (buf1[rpos.toNat + 2]?.getD 0#32).toNat := by
      simp [sz_b, hszb_get,
        List.getElem?_eq_getElem (by omega : rpos.toNat + 2 < buf1.length)]
    have hhdr_b_def : hdr_b = buf1[rpos.toNat]?.getD 0#32 := by
      simp [hdr_b, List.getElem?_eq_getElem (by omega : rpos.toNat < buf1.length)]
    have hcl_b : (3#64 + sz32_b.setWidth 64).toNat = 3 + sz_b := by
      rw [BitVec.toNat_add, BitVec.toNat_setWidth, show (3#64).toNat = 3 from rfl,
        Nat.mod_eq_of_lt (by have := sz32_b.isLt; omega),
        Nat.mod_eq_of_lt (by omega)]
    have hr_next : rpos + (3#64 + sz32_b.setWidth 64) =
        BitVec.ofNat 64 (rpos.toNat + 3 + sz_b) := by
      have hlt_rb : rpos.toNat + 3 + sz_b < 2 ^ 64 := by omega
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hcl_b, BitVec.toNat_ofNat,
        show rpos.toNat + (3 + sz_b) = rpos.toNat + 3 + sz_b by omega,
        Nat.mod_eq_of_lt hlt_rb]
    have hod_eq : (mid + rpos).toNat = mid.toNat + rpos.toNat := bv64_add_lt (by omega)
    m6_tiny_lets; m6_nojoin
    refine wp_loop_inv
      (fun (x : Tup Val [i64]) mk =>
        let (k, ()) := x
        k.toNat ≤ 3 + sz_b ∧ ∃ ar_k : List (BitVec 32),
        ar_k.length = dst.toNat ∧
        (∀ i < mid.toNat + rpos.toNat, ar_k[i]? = ar2[i]?) ∧
        (∀ j < k.toNat, ar_k[mid.toNat + rpos.toNat + j]? = buf1[rpos.toNat + j]?) ∧
        (array (t := i32) c.pArena ar_k ⋆ array (t := i32) bufPtr buf1 ⋆
          FullMemArenaOut c { s with core := { s.core with rsns := rsns2 } } ⋆ R) mk)
      (fun (k, ()) _ => 3 + sz_b - k.toNat)
      (fun Jk hLoopK => by
        m6_tiny_lets; m6_nojoin
        exact hLoopK (0#64, ()) m2 ⟨Nat.zero_le _, ar2, har2_l,
          fun _ _ => rfl, fun _ hj => by simp at hj, hm2⟩)
      (fun Jk (k, ()) mk ⟨hk_le, ar_k, hak_l, hak_pre, hak_cp, hmk⟩ hLoopK => ?_)
    · m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
      · have hk_lt : k.toNat < 3 + sz_b := by
          c0_cond hc
          first
          | (have hlt1 : k.toNat < (3#64 + sz32_b.setWidth 64).toNat := hc
             exact hcl_b ▸ hlt1)
          | (have h3sz_b : (BitVec.toNat (3 : BitVec 64) +
                BitVec.toNat (buf1[(rpos + 2#64).toNat]'hb2_lt)) % 2 ^ 64 = 3 + sz_b := by
               change (3 + sz32_b.toNat) % 2 ^ 64 = 3 + sz_b
               exact Nat.mod_eq_of_lt (by omega)
             rw [h3sz_b] at hc; exact hc)
        have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_lt (by omega)
        have hodk : (mid + rpos + k).toNat = mid.toNat + rpos.toNat + k.toNat :=
          bv64_add2_gen_lt (by omega)
        have hrk : (rpos + k).toNat = rpos.toNat + k.toNat := bv64_add_lt (by omega)
        have hrk_lt : (rpos + k).toNat < buf1.length := by rw [hrk]; omega
        have hodk_lt : (mid + rpos + k).toNat < ar_k.length := by rw [hodk]; omega
        m6_tiny_lets
        first
        | (apply wp_load_of (M6Tactics2a.out_load_arr32 hrk_lt (sep_ac hmk))
           m6_tiny_lets
           apply wp_store_sep (M6Tactics2a.out_store_arr32 hodk_lt (sep_ac hmk))
           intro m hm; m6_tiny_lets; rw [wp_jump])
        | m6_nojoin
        let ar_k' := ar_k.set (mid.toNat + rpos.toNat + k.toNat)
          (buf1[rpos.toNat + k.toNat]'(by omega))
        refine hLoopK (k + 1#64, ()) _ (by dsimp only; rw [hk1]; omega)
          ⟨by rw [hk1]; omega, ar_k', by simp [ar_k', hak_l],
           fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hak_pre i hi,
           fun j hj => by
             rw [hk1] at hj
             by_cases hjk : j = k.toNat
             · subst hjk; rw [List.getElem?_set_self (by omega),
                 List.getElem?_eq_getElem (by omega : rpos.toNat + k.toNat < buf1.length)]
             · rw [List.getElem?_set_ne (by omega)]; exact hak_cp j (by omega),
           by dsimp only [ar_k']; simp only [← hodk, ← hrk]; exact sep_ac ‹_›⟩
      · have hk_eq : k.toNat = 3 + sz_b := by
          have : ¬ (k.toNat < 3 + sz_b) := by
            c0_cond hc
            first
            | (have hlt1 : ¬ k.toNat < (3#64 + sz32_b.setWidth 64).toNat := hc
               exact hcl_b ▸ hlt1)
            | (have h3sz_b : (BitVec.toNat (3 : BitVec 64) +
                  BitVec.toNat (buf1[(rpos + 2#64).toNat]'hb2_lt)) % 2 ^ 64 = 3 + sz_b := by
                 change (3 + sz32_b.toNat) % 2 ^ 64 = 3 + sz_b
                 exact Nat.mod_eq_of_lt (by omega)
               rw [h3sz_b] at hc; exact hc)
          omega
        rw [hk_eq] at hak_cp; clear hm2 hLoopK Jk
        m6_to_group_strip
        refine wp_join_group
          (fun () mR => ∃ rsns' : List (BitVec 32), rsns'.length = c.max_vars ∧
            (((buf1[rpos.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
              let v := (buf1[rpos.toNat + 1]?.getD 0#32).toNat
              v < s.core.cur_vars ∧
              rsns'[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 (mid.toNat + rpos.toNat) ∧
              ∀ v' < s.core.cur_vars, v' ≠ v →
                rsns'[v']?.getD 0xFFFFFFFF#32 = rsns2[v']?.getD 0xFFFFFFFF#32) ∧
             ((buf1[rpos.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 → rsns' = rsns2)) ∧
            (array (t := i32) c.pArena ar_k ⋆ array (t := i32) bufPtr buf1 ⋆
              FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) mR)
          ?_ ?_
        · rintro _ ⟨⟩ mR ⟨rsns', hrsns'_l, hrsns_upd, hmR⟩
          have hclr := bv32_clear_rsn_props hdr_b
          have hod_32 : (mid.toNat + rpos.toNat) < dst.toNat := by omega
          have hod_lt : (mid + rpos).toNat < ar_k.length := by rw [hod_eq]; omega
          have hod1_lt : (mid + rpos + 1#64).toNat < ar_k.length := by
            rw [bv64_add_lt (by rw [hod_eq, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega),
              hod_eq, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega
          m6_usteps
          apply wp_store_sep (M6Tactics2a.out_store_arr32
            (R := array (t := i32) bufPtr buf1 ⋆
              FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R)
            hod_lt (sep_ac hmR))
          intro m1 hm1; simp only [Arg.val_var] at hm1; m6_usteps
          have har1_k : buf1[rpos.toNat]'(by omega) = hdr_b := rfl
          rw [har1_k, hod_eq] at hm1
          have hod1_lt' : (mid + rpos + 1#64).toNat <
              (ar_k.set (mid.toNat + rpos.toNat) (hdr_b &&& ~~~0x00200000#32)).length := by
            simpa [List.length_set] using hod1_lt
          apply wp_store_sep (M6Tactics2a.out_store_arr32 hod1_lt' hm1)
          intro m2' hm2'; m6_tiny_lets; m6_nojoin
          let ar' := (ar_k.set (mid.toNat + rpos.toNat) (hdr_b &&& ~~~0x00200000#32)).set
            (mid.toNat + rpos.toNat + 1) 2#32
          have har'_0 :
              ar'[mid.toNat + rpos.toNat]? = some (hdr_b &&& ~~~0x00200000#32) := by
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
          have har'_fl : (ar'[mid.toNat + rpos.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
              (ar'[mid.toNat + rpos.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
              (ar'[mid.toNat + rpos.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := by
            rw [har'_0, Option.getD_some, hclr.1, hclr.2.1, hclr.2.2, hhdr_b_def]
            exact ⟨rfl, hfl_b, (hbf_info2 rpos.toNat hrp_ref).1⟩
          have hod1_eq : (mid + rpos + 1#64).toNat = mid.toNat + rpos.toNat + 1 := by
            rw [bv64_add1_lt (by rw [hod_eq]; omega), hod_eq]
          have hmR' : (array (t := i32) c.pArena ar' ⋆ array (t := i32) bufPtr buf1 ⋆
              FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) m2' := by
            rw [hod1_eq] at hm2'; exact sep_ac hm2'
          have hszb_opt : sz32_b = buf1[rpos.toNat + 2]?.getD 0#32 := by
            rw [hszb_get, List.getElem?_eq_getElem (by omega : rpos.toNat + 2 < buf1.length),
              Option.getD_some]
          have hstep2 := move_pass2_step hlen hdst_cap hm_sum hrp_lt har2_l
            (by simp [ar', hak_l]) hrsns2_l hrsns'_l h2_pre
            (fun i hi => by
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              exact hak_pre i hi)
            hmv_2 hmv_bf h2_info hbf_info2 hrsn_inv2 hrp_ref har'_fl
            (List.getElem?_set_self (by simp [hak_l]; omega))
            (by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact hak_cp 2 (by omega))
            (fun j hj => by
              rw [← hsz_b_def] at hj
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                Nat.add_assoc, hak_cp (3 + j) (by omega), ← Nat.add_assoc])
            hrsns_upd (by rw [← hsz_b_def, ← hszb_opt]; exact hr_next)
            hfit_b hmR'
          rw [← hszb_opt] at hstep2
          refine hLoop2 (rpos + (3#64 + sz32_b.setWidth 64), ()) _
            (by dsimp only; rw [hr_next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                omega)
            hstep2
        · intro J2_rsn hJ2_rsn
          m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
          · have hrsn_ne : (buf1[rpos.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 := by
              c0_cond hc; rwa [← hhdr_b_def]
            have hv_lt : (buf1[rpos.toNat + 1]?.getD 0#32).toNat < s.core.cur_vars :=
              ((hbf_info2 rpos.toNat hrp_ref).2 hrsn_ne).1
            let v32 := buf1[rpos.toNat + 1]'(by omega)
            have hv32_def : v32.toNat = (buf1[rpos.toNat + 1]?.getD 0#32).toNat := by
              simp [v32, List.getElem?_eq_getElem (by omega : rpos.toNat + 1 < buf1.length)]
            have hr1_eq : (rpos + 1#64).toNat = rpos.toNat + 1 := bv64_add1_lt (by omega)
            m6_nojoin
            · apply hJ; m6_nojoin
              have hod32 : (mid + rpos).setWidth 32 =
                  BitVec.ofNat 32 (mid.toNat + rpos.toNat) := by
                apply BitVec.eq_of_toNat_eq
                simp only [BitVec.toNat_setWidth, hod_eq, BitVec.toNat_ofNat]
              have hv64_idx : (v32.setWidth 64).toNat = v32.toNat := bv32_zext64_toNat v32
              let rsns' := rsns2.set v32.toNat ((mid + rpos).setWidth 32)
              refine hJ2_rsn () _ ⟨rsns', by simp [rsns', hrsns2_l], ⟨fun _ => ⟨hv_lt, by
                   have h_s : rsns'[v32.toNat]? = some ((mid + rpos).setWidth 32) :=
                     List.getElem?_set_self (by omega)
                   rw [← hv32_def, h_s, Option.getD_some, hod32],
                   fun v' _ hne => by
                     dsimp only [rsns']
                     rw [List.getElem?_set_ne (by rw [hv32_def]; exact fun h => hne h.symm)]⟩,
                 fun h0 => absurd h0 hrsn_ne⟩, by
                   dsimp only [rsns']; rw [← hv64_idx]; simp only [v32, ← hr1_eq]; exact sep_ac hm⟩
            · exfalso; apply hc
              simp only [show (1 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : rpos.toNat + 1 < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)]
              rw [Nat.mod_eq_of_lt (by have := v32.isLt; exact Nat.lt_trans this (by decide))]
              exact hv32_def ▸ hv_lt
          · have hrsn_0 : (buf1[rpos.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 := by
              rw [List.getElem?_eq_getElem (by omega : rpos.toNat < buf1.length),
                Option.getD_some]
              c0_cond hc; exact hc
            m6_tiny_lets; m6_nojoin
            exact hJ2_rsn () _
              ⟨rsns2, hrsns2_l, ⟨fun h => absurd hrsn_0 h, fun _ => rfl⟩, hmk⟩
  · have hrp_eq : rpos.toNat = rlen.toNat := by
      have : ¬ (rpos.toNat < rlen.toNat) := by c0_cond hc; exact hc
      omega
    rw [hrp_eq] at hmv_2 h2_info hrsn_inv2
    have hinv_fin : ∀ v < s.core.cur_vars,
        let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
        if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
            (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
          ∃ rp, RefInChain buf1 0 rlen.toNat rp ∧
            (buf1[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
            buf1[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
            (∀ rp2, RefInChain buf1 0 rlen.toNat rp2 →
              (buf1[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
              buf1[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp) ∧
            let r' := (rsns2[v]?.getD 0xFFFFFFFF#32).toNat
            r' = mid.toNat + rp ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
            RefInChain ar2 mid.toNat (mid.toNat + rlen.toNat) r' ∧
            (ar2[r' + 2]?.getD 0#32).toNat = (buf1[rp + 2]?.getD 0#32).toNat ∧
            ∀ j < (buf1[rp + 2]?.getD 0#32).toNat, ar2[r' + 3 + j]? = buf1[rp + 3 + j]?
        else rsns2[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32 := fun v hv => by
      have hv2 := hrsn_inv2 v hv; dsimp only at hv2 ⊢
      by_cases hcond : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
      · rw [rw_ite_pos hcond] at hv2 ⊢
        obtain ⟨rp, hrp, hrsn_p, hbp, huniq_p, hbr⟩ := hv2
        have hrp_bd := hrp.bounds
        rw [rw_ite_pos (by omega)] at hbr
        exact ⟨rp, hrp, hrsn_p, hbp, huniq_p, hbr⟩
      · rw [rw_ite_neg hcond] at hv2 ⊢; exact hv2
    have hm2_re : (FullMemArenaOut c { s with core := { s.core with rsns := rsns2 } } ⋆
        (array (t := i32) c.pArena ar2 ⋆ array (t := i32) bufPtr buf1 ⋆ R)) m2 := sep_ac hm2
    m6_to_group_strip
    refine wp_unroll_group fun Jfr hJfr => ?_
    m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
    · m6_tiny_lets; rw [wp_jump]; apply hJfr; m6_usteps; m6_tiny_lets
      have hst := M6Tactics2a.out_store_first_red mid hm2_re
      refine ⟨hst.1, ?_⟩
      m6_tiny_lets; rw [wp_ret]
      exact hQ ar2 rsns2 mid _ har2_l hrsns2_l h2_pre hmv_2 h2_info hinv_fin
        (by rw [rw_ite_pos (by simpa [BitVec.ult] using hc)]) (sep_ac hst.2)
    · m6_tiny_lets; rw [wp_jump]; apply hJfr; m6_usteps; m6_tiny_lets
      have hst := M6Tactics2a.out_store_first_red 0xFFFFFFFF#64 hm2_re
      refine ⟨hst.1, ?_⟩
      m6_tiny_lets; rw [wp_ret]
      exact hQ ar2 rsns2 0xFFFFFFFF#64 _ har2_l hrsns2_l h2_pre hmv_2 h2_info hinv_fin
        (by rw [rw_ite_neg (by simpa [BitVec.ult] using hc)]) (sep_ac hst.2)

open Classical in
theorem full_move_red_end_buf_m6_wp (Γ : Env)
    (hPass2 : ∀ a m Q X, fullMoveRedPass2Spec a m Q X →
      Γ "full_move_red_pass2_m6" [i64, i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullMoveRedEndBufSpec a m Q X →
      Func.wp Γ full_move_red_end_buf_m6_body a m Q X := by
  rintro ⟨h, first_red, dst, bufPtr, ⟨⟩⟩ m Q X
    ⟨c, s, arPre, buf0, redWords, R, rfl, hlen, hfr_le, hdst_cap, har_l, hred_buf, hbuf_b,
     hmv_orig, hdom, huniq, hm, hQ⟩
  have harc := c.harena; have hmaxv := c.hmaxv; have hcvl := hlen.core_ok.cur_vars_le
  have hvl := hlen.core_ok.vals_len; have hrl := hlen.core_ok.rsns_len
  unfold dimacsBound at harc hmaxv hbuf_b
  m6_tiny_lets; m6_nojoin
  refine wp_loop_inv (MovePass1Inv c s arPre buf0 redWords first_red dst bufPtr R)
    (fun (src, _, _, ()) _ => dst.toNat - src.toNat) (fun J1 hLoop1 => ?_) ?_
  · m6_tiny_lets; m6_nojoin
    refine hLoop1 (first_red, first_red, 0#64, ()) m
      ⟨Nat.le_refl _, by simp, hfr_le, arPre, buf0, s.core.rsns, redWords,
       har_l, rfl, hrl, by simp, fun _ _ => rfl, fun _ _ _ => rfl, .empty, hmv_orig, .empty,
       fun hlt => let ⟨h3, hfl, hsz, hfit, _, _⟩ := moveRangeChain_head_inv hmv_orig hlt
                  .head h3 hfl hsz hfit,
       fun r hr => by exfalso; have := hr.bounds; omega,
       fun rp hrp => by
         exfalso; have := hrp.bounds; simp only [BitVec.toNat_ofNat] at this; omega,
       fun v hv => ?_, hm⟩
    dsimp only
    rw [rw_ite_neg (fun ⟨hlv, hlt⟩ => by have := hlv.1; omega)]
    exact ⟨rfl, fun rp hrp => by
      exfalso; have := hrp.bounds; simp only [BitVec.toNat_ofNat] at this; omega⟩
  · rintro J1 ⟨src, idst, rlen, ⟨⟩⟩ m1
      ⟨hid_lo, hsum, hs_le, ar1, buf1, rsns1, rw_rem, har1_l, hbuf1_l, hrsns1_l, hrw_sum,
       hpre_ag, htail_ag, hmv_ir, hmv_rm, hmv_bf, hsrc_ref_fn, hir_info, hbf_info, hrsn_inv, hm1⟩
      hLoop1
    clear hm
    have hrsns_eq_src : ∀ v < s.core.cur_vars,
        (rsns1[v]?.getD 0xFFFFFFFF#32).toNat = src.toNat ↔
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat = src.toNat := fun v hv => by
      have hpre_v := hrsn_inv v hv; dsimp only at hpre_v
      by_cases hcond : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < src.toNat
      · rw [rw_ite_pos hcond] at hpre_v
        split at hpre_v
        · have h1 := hpre_v.2.1; constructor <;> intro heq <;> omega
        · rw [hpre_v.1]
      · rw [rw_ite_neg hcond] at hpre_v; rw [hpre_v.1]
    m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
    · have hs_lt : src.toNat < dst.toNat := by c0_cond hc; exact hc
      have hsrc_ref := hsrc_ref_fn hs_lt
      obtain ⟨h3, hfl, hsz3, hfit, hrw_le, htl⟩ := moveRangeChain_head_inv hmv_rm hs_lt
      have hsrc2_eq : (src + 2#64).toNat = src.toNat + 2 := bv64_add2_lt (by omega)
      have hsrc2_lt : (src + 2#64).toNat < ar1.length := by rw [hsrc2_eq]; omega
      let sz32 := ar1[(src + 2#64).toNat]'hsrc2_lt
      let sz := sz32.toNat
      let hdr := ar1[src.toNat]'(by omega)
      have hsz32_get : sz32 = ar1[src.toNat + 2]'(by omega) := by
        dsimp only [sz32]; simp only [hsrc2_eq]
      have hsz_def : sz = (ar1[src.toNat + 2]?.getD 0#32).toNat := by
        simp [sz, hsz32_get, List.getElem?_eq_getElem (by omega : src.toNat + 2 < ar1.length)]
      have hhdr_def : hdr = ar1[src.toNat]?.getD 0#32 := by
        simp [hdr, List.getElem?_eq_getElem (by omega : src.toNat < ar1.length)]
      have hsz_eq : (ar1[src.toNat + 2]?.getD 0#32).toNat =
          (arPre[src.toNat + 2]?.getD 0#32).toNat := by
        rw [htail_ag (src.toNat + 2) (by omega) (by omega)]
      have hsz32_eq : sz32 = ar1[src.toNat + 2]?.getD 0#32 := by
        simp [hsz32_get, List.getElem?_eq_getElem (by omega : src.toNat + 2 < ar1.length)]
      have hrw_rem : rw_rem = redWords - rlen.toNat := by omega
      have hcl_eq : (3#64 + sz32.setWidth 64).toNat = 3 + sz := by
        have hlt_s : sz32.toNat < 2 ^ 64 := by have := sz32.isLt; omega
        rw [BitVec.toNat_add, BitVec.toNat_setWidth, show (3#64).toNat = 3 from rfl,
          Nat.mod_eq_of_lt hlt_s, Nat.mod_eq_of_lt (by omega)]
      have hs_next : src + 3#64 + sz32.setWidth 64 =
          BitVec.ofNat 64 (src.toNat + 3 + sz) := by
        have hlt_n : src.toNat + 3 + sz32.toNat < 2 ^ 64 := by omega
        apply BitVec.eq_of_toNat_eq
        have hlt_s : sz32.toNat < 2 ^ 64 := by have := sz32.isLt; omega
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
          show (3#64).toNat = 3 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_s,
          Nat.mod_eq_of_lt (by omega : src.toNat + 3 < 2 ^ 64), Nat.mod_eq_of_lt hlt_n]
      have hs_next2 : src + (3#64 + sz32.setWidth 64) =
          BitVec.ofNat 64 (src.toNat + 3 + sz) := by
        rw [← BitVec.add_assoc]; exact hs_next
      m6_to_group_strip
      refine wp_join_group
        (fun (x : Tup Val [i64, i64]) m' =>
          let (idst', rlen', ()) := x
          src.toNat + 3 + sz ≤ dst.toNat ∧
          MovePass1Inv c s arPre buf0 redWords first_red dst bufPtr R
            (src + 3#64 + sz32.setWidth 64, idst', rlen', ()) m') ?_ ?_
      · rintro _ ⟨idst', rlen', ⟨⟩⟩ m' ⟨hfit', hinv'⟩
        m6_tiny_lets; m6_nojoin
        have hfit2 : src.toNat + 3 + sz32.toNat ≤ dst.toNat := by
          dsimp only [sz] at hfit'; exact hfit'
        exact hLoop1 (src + (3#64 + sz32.setWidth 64), idst', rlen', ()) m'
          (by dsimp only; rw [hs_next2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
          (by simpa only [← BitVec.add_assoc] using hinv')
      intro J1_join hJ1_join
      m6_split
      · have hred : (ar1[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := by
          have h1 : (ar1[src.toNat]'(by omega) &&& 0x00400000#32) ≠ 0#32 := by c0_cond hc; exact hc
          rwa [← hhdr_def]
        have hr_next_bd : rlen.toNat + 3 + sz ≤ buf0.length := by
          rw [rw_ite_pos hred] at hrw_le; dsimp only [sz] at hrw_le ⊢; omega
        have hr_next : rlen + (3#64 + sz32.setWidth 64) =
            BitVec.ofNat 64 (rlen.toNat + 3 + sz) := by
          have hlt_n : rlen.toNat + 3 + sz < 2 ^ 64 := by omega
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, hcl_eq, BitVec.toNat_ofNat,
            show rlen.toNat + (3 + sz) = rlen.toNat + 3 + sz by omega,
            Nat.mod_eq_of_lt hlt_n]
        m6_tiny_lets; m6_c0_steps
        refine wp_loop_inv
          (fun (x : Tup Val [i64]) mk =>
            let (k, ()) := x
            k.toNat ≤ 3 + sz ∧ ∃ buf_k : List (BitVec 32),
            buf_k.length = buf0.length ∧ (∀ i < rlen.toNat, buf_k[i]? = buf1[i]?) ∧
            (∀ i < k.toNat, buf_k[rlen.toNat + i]? = ar1[src.toNat + i]?) ∧
            (array (t := i32) c.pArena ar1 ⋆ array (t := i32) bufPtr buf_k ⋆
              FullMemArenaOut c { s with core := { s.core with rsns := rsns1 } } ⋆ R) mk)
          (fun (k, ()) _ => 3 + sz - k.toNat)
          (fun Jk hLoopK => by
            m6_tiny_lets; m6_nojoin
            exact hLoopK (0#64, ()) m1 ⟨Nat.zero_le _, buf1, hbuf1_l,
              fun _ _ => rfl, fun _ hi => by simp at hi, hm1⟩)
          (fun Jk (k, ()) mk ⟨hk_le, buf_k, hbk_l, hbk_pre, hbk_cp, hmk⟩ hLoopK => ?_)
        · m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
          · have hk_lt : k.toNat < 3 + sz := by
              c0_cond hc
              first
              | (have hlt1 : k.toNat < (3#64 + sz32.setWidth 64).toNat := hc
                 exact hcl_eq ▸ hlt1)
              | (have h3sz : (BitVec.toNat (3 : BitVec 64) +
                    BitVec.toNat (ar1[(src + 2#64).toNat]'hsrc2_lt)) % 2 ^ 64 = 3 + sz := by
                   change (3 + sz32.toNat) % 2 ^ 64 = 3 + sz
                   exact Nat.mod_eq_of_lt (by omega)
                 try simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                   Nat.mod_eq_of_lt (by omega : src.toNat + 2 < 2 ^ 64)] at hc
                 first
                 | (rw [h3sz] at hc; exact hc)
                 | (rw [← hsz32_get, show (BitVec.toNat (3 : BitVec 64) + sz32.toNat) % 2 ^ 64 =
                      3 + sz from Nat.mod_eq_of_lt (by omega)] at hc; exact hc))
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_lt (by omega)
            have hrk : (rlen + k).toNat = rlen.toNat + k.toNat := bv64_add_lt (by omega)
            have hsk : (src + k).toNat = src.toNat + k.toNat := bv64_add_lt (by omega)
            have hrk_lt : (rlen + k).toNat < buf_k.length := by rw [hrk]; omega
            have hsk_lt : (src + k).toNat < ar1.length := by rw [hsk]; omega
            m6_tiny_lets
            first
            | (apply wp_load_of (M6Tactics2a.out_load_arr32 hsk_lt (sep_ac hmk))
               m6_tiny_lets
               apply wp_store_sep (M6Tactics2a.out_store_arr32 hrk_lt (sep_ac hmk))
               intro m hm; m6_tiny_lets; rw [wp_jump])
            | m6_nojoin
            refine hLoopK (k + 1#64, ()) _ (by dsimp only; rw [hk1]; omega)
              ⟨by rw [hk1]; omega,
               buf_k.set (rlen.toNat + k.toNat) (ar1[src.toNat + k.toNat]'(by omega)),
               by simp [hbk_l],
               fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hbk_pre i hi,
               fun i hi => by
                 rw [hk1] at hi
                 by_cases hik : i = k.toNat
                 · subst hik; rw [List.getElem?_set_self (by omega),
                     List.getElem?_eq_getElem (by omega : src.toNat + k.toNat < ar1.length)]
                 · rw [List.getElem?_set_ne (by omega)]; exact hbk_cp i (by omega),
               by simp only [← hrk, ← hsk]; exact sep_ac ‹_›⟩
          · have hk_eq : k.toNat = 3 + sz := by
              have hnot : ¬ (k.toNat < 3 + sz) := by
                c0_cond hc
                first
                | (have hlt1 : ¬ k.toNat < (3#64 + sz32.setWidth 64).toNat := hc
                   exact hcl_eq ▸ hlt1)
                | (have h3sz : (BitVec.toNat (3 : BitVec 64) +
                      BitVec.toNat (ar1[(src + 2#64).toNat]'hsrc2_lt)) % 2 ^ 64 = 3 + sz := by
                     change (3 + sz32.toNat) % 2 ^ 64 = 3 + sz
                     exact Nat.mod_eq_of_lt (by omega)
                   try simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                     Nat.mod_eq_of_lt (by omega : src.toNat + 2 < 2 ^ 64)] at hc
                   first
                   | (rw [h3sz] at hc; exact hc)
                   | (rw [← hsz32_get, show (BitVec.toNat (3 : BitVec 64) + sz32.toNat) % 2 ^ 64 =
                        3 + sz from Nat.mod_eq_of_lt (by omega)] at hc; exact hc))
              omega
            rw [hk_eq] at hbk_cp; clear hm1 hLoopK Jk
            m6_to_group
            refine wp_join_group
              (Pass1RedPost c s arPre ar1 buf1 rsns1 first_red dst bufPtr src rlen buf0.length sz R)
              ?_ ?_
            · rintro _ ⟨⟩ mR ⟨buf', hbp_l, hbp_pre, hbp_copy, hbp_2, hbp_0fl, hbp_4fl, hbp_rsn, hmR⟩
              m6_tiny_lets; m6_nojoin
              have hstep := move_pass1_red_step hlen hdst_cap hbuf_b hid_lo hsum hs_lt har1_l
                hbuf1_l hbp_l hrsns1_l (hrw_rem ▸ hrw_sum) hpre_ag htail_ag hmv_ir
                (hrw_rem ▸ hmv_rm) hmv_bf hir_info hbf_info hrsn_inv huniq hsrc_ref hred hbp_pre
                hsz_eq
                (fun k hk hk0 hk1 => by rw [← hsz_def] at hk; exact hbp_copy k hk hk0 hk1)
                hbp_2 ⟨hbp_0fl, hbp_4fl⟩ hbp_rsn (by rw [← hsz32_eq]; exact hs_next)
                (by rw [← hsz32_eq]; exact hr_next) (by rw [← hsz_def]; exact hr_next_bd) hmR
              exact hJ1_join (idst, rlen + (3#64 + sz32.setWidth 64), ()) mR
                ⟨by rw [← hsz_def] at hfit; exact hfit, by simpa only [← hsz32_eq] using hstep⟩
            · intro J_red hJ_red
              clear hQ hLoop1 J1 hJ1_join J1_join hmv_orig hrw_sum hpre_ag hmv_ir hmv_rm
                hmv_bf hsrc_ref_fn hir_info hbf_info hrsn_inv huniq
              m6_split
              · have hrsn_ne : (ar1[src.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 := by
                  have h1 : (ar1[src.toNat]'(by omega) &&& 0x00200000#32) ≠ 0#32 := by
                    c0_cond hc; exact hc
                  rwa [← hhdr_def]
                m6_to_group_strip
                refine wp_unroll_group fun J_rsn hJ_rsn => ?_
                m6_to_group_strip
                refine wp_loop_inv
                  (fun (x : Tup Val [i32]) mi =>
                    let (i, ()) := x
                    i.toNat ≤ sz ∧ mk = mi ∧
                    ∀ j < i.toNat,
                      let lit := (ar1[src.toNat + 3 + j]?.getD 0#32).toNat
                      let v := lit / 2
                      ¬ (v < s.core.cur_vars ∧
                        (0#32).slt ((s.core.vals[lit]?.getD 0#8).signExtend 32) = true ∧
                        (rsns1[v]?.getD 0xFFFFFFFF#32).toNat = src.toNat))
                  (fun (i, ()) _ => sz - i.toNat)
                  (fun Ji hLoopI => by
                    m6_tiny_lets; m6_nojoin
                    exact hLoopI (0#32, ()) mk
                      ⟨Nat.zero_le _, rfl, fun _ hj => by simp at hj⟩)
                  (fun Ji (i, ()) _ ⟨hi_le, rfl, hmiss⟩ hLoopI => ?_)
                · m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
                  · have hi_lt : i.toNat < sz := by
                      c0_cond hc
                      simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, ← hsrc2_eq,
                        Nat.mod_eq_of_lt (src + 2#64).isLt] at hc
                      exact hc
                    have hi1 : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_lt (by omega)
                    have hs3i : (src + 3#64 + i.setWidth 64).toNat = src.toNat + 3 + i.toNat :=
                      bv64_add3_zext_lt (by omega)
                    have hs3i_lt : (src + 3#64 + i.setWidth 64).toNat < ar1.length := by
                      rw [hs3i]; omega
                    let lit32 := ar1[(src + 3#64 + i.setWidth 64).toNat]'hs3i_lt
                    let v32 := lit32 >>> 1#32
                    have hlit32_get : lit32 = ar1[src.toNat + 3 + i.toNat]'(by omega) := by
                      dsimp only [lit32]; simp only [hs3i]
                    have hs3i_raw : ar1[(src.toNat + BitVec.toNat (3 : BitVec 64) +
                        i.toNat) % 2 ^ 64]'(by
                        rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                          Nat.mod_eq_of_lt (by omega)]; omega) = lit32 := by
                      rw [hlit32_get]; congr 1
                      rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    have hv_def : v32.toNat = lit32.toNat / 2 := by
                      simp [v32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                    m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
                    · have hv_lt : v32.toNat < s.core.cur_vars := by
                        c0_cond hc
                        rw [hs3i_raw] at hc
                        try rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                          Nat.pow_one] at hc
                        rw [← hv_def, Nat.mod_eq_of_lt (by omega : v32.toNat < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                        exact hc
                      have hlit_div : lit32.toNat / 2 < s.core.cur_vars := hv_def ▸ hv_lt
                      have hlit_lt_vals : lit32.toNat < s.core.vals.length := by omega
                      have hlit_lt_2cv : lit32.toNat < 2 * s.core.cur_vars := by omega
                      m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
                      · have hval_pos : (0#32).slt
                            ((s.core.vals[lit32.toNat]?.getD 0#8).signExtend 32) = true := by
                          c0_cond hc; simp only [hs3i_raw, Nat.mod_eq_of_lt
                            (by have := lit32.isLt; omega : lit32.toNat < 2 ^ 64)] at hc
                          rwa [List.getElem?_eq_getElem hlit_lt_vals, Option.getD_some]
                        have hval_eq1 : s.core.vals[lit32.toNat]?.getD 0#8 = 1#8 :=
                          (bv_i8_slt0_eq_1 (hdom lit32.toNat hlit_lt_2cv)).1.mp hval_pos
                        m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
                        · have hrs_src : (rsns1[v32.toNat]?.getD 0xFFFFFFFF#32).toNat =
                              src.toNat := by
                            have h1 : rsns1[v32.toNat]?.getD 0xFFFFFFFF#32 =
                                BitVec.ofNat 32 src.toNat := by
                              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                              apply BitVec.eq_of_toNat_eq
                              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                              have h2 : (rsns1[v32.toNat]'(by omega)).setWidth 64 = src := by
                                c0_cond hc; simp only [hs3i_raw] at hc
                                have hv_mod : (lit32 >>> 1).toNat % 2 ^ 64 = v32.toNat :=
                                  Nat.mod_eq_of_lt (by have := v32.isLt; omega)
                                have hlt_mod : (lit32 >>> 1).toNat % 2 ^ 64 < rsns1.length := by
                                  rw [hv_mod]; omega
                                have hget_eq : rsns1[(lit32 >>> 1).toNat % 2 ^ 64]'hlt_mod =
                                    rsns1[v32.toNat]'(by omega) := by congr 1
                                rwa [hget_eq] at hc
                              have h3 := congrArg BitVec.toNat h2
                              have hlt_r := (rsns1[v32.toNat]'(by omega)).isLt
                              rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at h3
                            rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                          have hrs0_src := (hrsns_eq_src v32.toNat hv_lt).mp hrs_src
                          have hr1_eq : (rlen + 1#64).toNat = rlen.toNat + 1 :=
                            bv64_add1_lt (by omega)
                          m6_c0_steps <;> try contradiction
                          have hp_step := pass1_red_hit_helper (buf0Len := buf0.length)
                            (buf1 := buf1) har1_l (by rw [hsz_def]; exact hfit) hs_lt hsrc_ref
                            hfl hred hrsn_ne hsz_def hsz_eq htail_ag hi_lt hlit32_get hv_def hv_lt
                            hval_eq1 hrs0_src hbk_l hbk_pre hbk_cp (by omega)
                            (by rw [hbk_l]; omega) (by rw [hbk_l]; omega) (by omega) hhdr_def
                          exact hJ_red () _ ⟨buf_k.set (rlen.toNat + 1) v32,
                            hp_step.1, hp_step.2.1, hp_step.2.2.1, hp_step.2.2.2.1,
                            hp_step.2.2.2.2.1, hp_step.2.2.2.2.2.1, hp_step.2.2.2.2.2.2,
                            by dsimp only [v32, lit32]
                               simp only [show (3#64 : BitVec 64) = 3 from rfl,
                                 show (1#32 : BitVec 32) = 1 from rfl, ← hr1_eq]
                               exact sep_ac hm⟩
                        · have hrs_ne : (rsns1[v32.toNat]?.getD 0xFFFFFFFF#32).toNat ≠
                              src.toNat := by
                            c0_cond hc; simp only [hs3i_raw] at hc
                            have hv_mod : (lit32 >>> 1).toNat % 2 ^ 64 = v32.toNat :=
                              Nat.mod_eq_of_lt (by have := v32.isLt; omega)
                            have hlt_mod : (lit32 >>> 1).toNat % 2 ^ 64 < rsns1.length := by
                              rw [hv_mod]; omega
                            have hget_eq : rsns1[(lit32 >>> 1).toNat % 2 ^ 64]'hlt_mod =
                                rsns1[v32.toNat]'(by omega) := by congr 1
                            intro heq; apply hc
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
                            apply BitVec.eq_of_toNat_eq
                            have hlt_r := (rsns1[(lit32 >>> 1).toNat % 2 ^ 64]'hlt_mod).isLt
                            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hget_eq, heq]
                          m6_tiny_lets; m6_c0_steps
                          refine hLoopI (i + 1#32, ()) mk (by dsimp only; rw [hi1]; omega)
                            ⟨by rw [hi1]; omega, rfl, fun j hj => ?_⟩
                          rw [hi1] at hj; by_cases hji : j = i.toNat
                          · subst hji; have hle1 : src.toNat + 3 + i.toNat < ar1.length := by omega
                            dsimp only
                            rw [List.getElem?_eq_getElem hle1, Option.getD_some, ← hlit32_get]
                            rintro ⟨_, _, heq⟩
                            rw [← hv_def] at heq; exact hrs_ne heq
                          · exact hmiss j (by omega)
                      · have hval_npos : ¬ ((0#32).slt
                            ((s.core.vals[lit32.toNat]?.getD 0#8).signExtend 32) = true) := by
                          c0_cond hc; simp only [hs3i_raw] at hc
                          simp only [Nat.mod_eq_of_lt
                            (by have := lit32.isLt; omega : lit32.toNat < 2 ^ 64)] at hc
                          rw [List.getElem?_eq_getElem hlit_lt_vals, Option.getD_some, hc]
                          decide
                        m6_tiny_lets; m6_c0_steps
                        refine hLoopI (i + 1#32, ()) mk (by dsimp only; rw [hi1]; omega)
                          ⟨by rw [hi1]; omega, rfl, fun j hj => ?_⟩
                        rw [hi1] at hj; by_cases hji : j = i.toNat
                        · subst hji
                          rw [List.getElem?_eq_getElem
                            (by omega : src.toNat + 3 + i.toNat < ar1.length),
                            Option.getD_some, ← hlit32_get]
                          exact fun h => hval_npos h.2.1
                        · exact hmiss j (by omega)
                    · have hv_ge : ¬ (v32.toNat < s.core.cur_vars) := by
                        c0_cond hc
                        rw [hs3i_raw] at hc
                        try rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                          Nat.pow_one] at hc
                        rw [← hv_def, Nat.mod_eq_of_lt (by omega : v32.toNat < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                        exact hc
                      m6_tiny_lets; m6_c0_steps
                      refine hLoopI (i + 1#32, ()) mk (by dsimp only; rw [hi1]; omega)
                        ⟨by rw [hi1]; omega, rfl, fun j hj => ?_⟩
                      rw [hi1] at hj; by_cases hji : j = i.toNat
                      · subst hji
                        rw [List.getElem?_eq_getElem
                          (by omega : src.toNat + 3 + i.toNat < ar1.length),
                          Option.getD_some, ← hlit32_get]
                        exact fun ⟨hlt, _⟩ => hv_ge (hv_def ▸ hlt)
                      · exact hmiss j (by omega)
                  · have hi_eq : i.toNat = sz := by
                      have : ¬ (i.toNat < sz) := by
                        c0_cond hc
                        simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, ← hsrc2_eq,
                          Nat.mod_eq_of_lt (src + 2#64).isLt] at hc
                        exact hc
                      omega
                    rw [hi_eq] at hmiss
                    m6_tiny_lets; rw [wp_jump]; apply hJ_rsn; m6_tiny_lets
                    refine wp_unroll_group fun Js hJs => ?_
                    m6_to_jnz
                    refine wp_jnz_of (fun hf => by
                      exfalso; simp only [Arg.val_var] at hf; revert hf; decide) ?_
                    intro _; m6_usteps; m6_tiny_lets
                    refine wp_store_sep
                      (M6Tactics2a.out_store_arr32
                        (R := array (t := i32) c.pArena ar1 ⋆
                          FullMemArenaOut c { s with core := { s.core with rsns := rsns1 } } ⋆ R)
                        (by omega : rlen.toNat < buf_k.length) (sep_ac hmk))
                      fun m_rsn hm_rsn => ?_
                    simp only [Arg.val_var] at hm_rsn
                    m6_tiny_lets; rw [wp_jump]; apply hJs; m6_nojoin
                    let buf' := buf_k.set rlen.toNat (hdr &&& ~~~0x00200000#32)
                    have hbp0 : buf'[rlen.toNat]? = some (hdr &&& ~~~0x00200000#32) :=
                      List.getElem?_set_self (by omega)
                    have hpr := bv32_clear_rsn_props hdr
                    have hbp0_fl : (buf'[rlen.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
                        (buf'[rlen.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := by
                      rw [hbp0, Option.getD_some, hpr.2.1, hpr.2.2, hhdr_def]; exact ⟨hfl, hred⟩
                    have hbp0_n : (buf'[rlen.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 := by
                      rw [hbp0, Option.getD_some]; exact hpr.1
                    refine hJ_red () _ ⟨buf', by simp [buf', hbk_l],
                      fun j hj => by rw [List.getElem?_set_ne (by omega)]; exact hbk_pre j hj,
                      fun k hk hk0 _ => by
                        rw [List.getElem?_set_ne (by omega)]; exact hbk_cp k hk,
                      by rw [List.getElem?_set_ne (by omega)]; exact hbk_cp 2 (by omega),
                      hbp0_fl.1, hbp0_fl.2,
                      ⟨fun hne => absurd hbp0_n hne, fun _ v hv hlv heq_s => by
                        obtain ⟨_, _, _, _, j, hj_sz, hdiv, hval1⟩ := hlv
                        rw [heq_s] at hj_sz hdiv hval1
                        rw [← hsz_eq, ← hsz_def] at hj_sz
                        have hj_miss := hmiss j hj_sz
                        have hae := htail_ag (src.toNat + 3 + j) (by omega) (by omega)
                        have hlit_eq : (ar1[src.toNat + 3 + j]?.getD 0#32).toNat =
                            (arPre[src.toNat + 3 + j]?.getD 0#32).toNat :=
                          congrArg (fun x : Option (BitVec 32) => (x.getD 0#32).toNat) hae
                        apply hj_miss
                        refine ⟨by rw [hlit_eq, hdiv]; exact hv, ?_, ?_⟩
                        · rw [hlit_eq, (bv_i8_slt0_eq_1 (hdom _ (by omega))).1]; exact hval1
                        · rw [hlit_eq, hdiv]; exact (hrsns_eq_src v hv).mpr heq_s⟩,
                      by dsimp only [buf', hdr]
                         rw [BitVec.and_comm (ar1[src.toNat]'(by omega)),
                           show (~~~0x00200000#32 : BitVec 32) = 4292870143#32 from rfl]
                         exact sep_ac hm_rsn⟩
              · have hrsn_0 : (ar1[src.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 := by
                  rw [List.getElem?_eq_getElem (by omega : src.toNat < ar1.length),
                    Option.getD_some]
                  c0_cond hc; exact hc
                m6_tiny_lets; m6_nojoin
                have hc0 := hbk_cp 0 (by omega); simp only [Nat.add_zero] at hc0
                refine hJ_red () _ ⟨buf_k, hbk_l, hbk_pre, fun k hk _ _ => hbk_cp k hk,
                  hbk_cp 2 (by omega), by rw [hc0]; exact hfl, by rw [hc0]; exact hred,
                  ⟨fun hne => by rw [hc0] at hne; exact absurd hrsn_0 hne,
                   fun _ v _ hlv heq_s => by
                     have h0 := hlv.2.2.2.1
                     rw [heq_s, ← htail_ag src.toNat (Nat.le_refl _) hs_lt] at h0
                     exact absurd hrsn_0 h0⟩,
                  hmk⟩
      · have hnred : (ar1[src.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 := by
          c0_cond hc; rwa [← hhdr_def]
        have hid_next : idst + (3#64 + sz32.setWidth 64) =
            BitVec.ofNat 64 (idst.toNat + 3 + sz) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, hcl_eq, BitVec.toNat_ofNat,
            show idst.toNat + (3 + sz) = idst.toNat + 3 + sz by omega,
            Nat.mod_eq_of_lt (by rw [hsz_def]; omega)]
        m6_to_group_strip
        refine wp_join_group
          (Pass1IrredPost c s arPre ar1 buf1 rsns1 first_red dst bufPtr src idst sz R) ?_ ?_
        · rintro _ ⟨⟩ mR ⟨ar', rsns', har'_l, hrsns'_l, har_pre, har_tail, har_lits, har_2,
            hrsns_upd, hmR⟩
          have hid_lt : idst.toNat < ar'.length := by omega
          have hcl_pr := bv32_clear_rsn_props hdr
          m6_nojoin
          let ar'' := ar'.set idst.toNat (hdr &&& ~~~0x00200000#32)
          have har''_0 : ar''[idst.toNat]? = some (hdr &&& ~~~0x00200000#32) :=
            List.getElem?_set_self (by omega)
          have har''_fl : (ar''[idst.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
              (ar''[idst.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
              (ar''[idst.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 := by
            rw [har''_0, Option.getD_some, hcl_pr.1, hcl_pr.2.1, hcl_pr.2.2, hhdr_def]
            exact ⟨rfl, hfl, hnred⟩
          refine hJ1_join (idst + (3#64 + sz32.setWidth 64), rlen, ()) _
            ⟨by rw [← hsz_def] at hfit; exact hfit, ?_⟩
          have hstep := move_pass1_irred_step (R := R) (bufPtr := bufPtr) hlen hdst_cap hid_lo
            hsum hs_lt har1_l (by simp [ar'', har'_l]) hbuf1_l hrsns1_l hrsns'_l
            (hrw_rem ▸ hrw_sum) hpre_ag htail_ag hmv_ir (hrw_rem ▸ hmv_rm) hmv_bf hir_info
            hbf_info hrsn_inv hsrc_ref hnred
            (fun i hi => by
              dsimp only [ar'']; rw [List.getElem?_set_ne (by omega)]; exact har_pre i hi)
            (fun i hi1 hi2 => by
              dsimp only [ar'']
              rw [List.getElem?_set_ne (by omega)]
              exact har_tail i (by rw [← hsz_def] at hi1; exact hi1) hi2)
            hsz_eq
            (fun j hj => by
              dsimp only [ar'']
              rw [List.getElem?_set_ne (by omega)]
              exact har_lits j (by rw [← hsz_def] at hj; exact hj))
            (by dsimp only [ar'']; rw [List.getElem?_set_ne (by omega)]; exact har_2)
            har''_fl hrsns_upd (by rw [← hsz32_eq]; exact hs_next)
            (by rw [← hsz32_eq]; exact hid_next) (by
              dsimp only [ar'', hdr]
              rw [BitVec.and_comm (ar1[src.toNat]'(by omega)),
                show (~~~0x00200000#32 : BitVec 32) = 4292870143#32 from rfl]
              exact sep_ac hm)
          simpa only [← hsz32_eq] using hstep
        · intro J_ir hJ_ir
          clear hQ hmv_orig hJ1_join J1_join hLoop1 J1 hrw_sum hpre_ag hmv_ir hmv_rm hmv_bf
            hsrc_ref_fn hir_info hbf_info
          m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
          · have hid_lt_src : idst.toNat < src.toNat := by
              have hne : idst ≠ src := by c0_cond hc; exact hc
              have hne_nat : idst.toNat ≠ src.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
              omega
            m6_tiny_lets; m6_nojoin
            refine wp_loop_inv
              (fun (x : Tup Val [i64]) mk =>
                let (k, ()) := x
                k.toNat ≤ 3 + sz ∧ ∃ ar_k : List (BitVec 32),
                ar_k.length = dst.toNat ∧ (∀ i < idst.toNat, ar_k[i]? = ar1[i]?) ∧
                (∀ j < k.toNat, ar_k[idst.toNat + j]? = ar1[src.toNat + j]?) ∧
                (∀ i, src.toNat + k.toNat ≤ i → i < dst.toNat → ar_k[i]? = ar1[i]?) ∧
                (array (t := i32) c.pArena ar_k ⋆ array (t := i32) bufPtr buf1 ⋆
                  FullMemArenaOut c { s with core := { s.core with rsns := rsns1 } } ⋆ R) mk)
              (fun (k, ()) _ => 3 + sz - k.toNat)
              (fun Jk hLoopK => by
                m6_tiny_lets; m6_nojoin
                exact hLoopK (0#64, ()) m1 ⟨Nat.zero_le _, ar1, har1_l,
                  fun _ _ => rfl, fun _ hj => by simp at hj, fun _ _ _ => rfl, hm1⟩)
              (fun Jk (k, ()) mk ⟨hk_le, ar_k, hak_l, hak_pre, hak_cp, hak_tl, hmk⟩ hLoopK => ?_)
            · m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
              · have hk_lt : k.toNat < 3 + sz := by
                  c0_cond hc
                  have hlt1 : k.toNat < (3#64 + sz32.setWidth 64).toNat := hc
                  rwa [hcl_eq] at hlt1
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_lt (by omega)
                have hsk : (src + k).toNat = src.toNat + k.toNat := bv64_add_lt (by omega)
                have hik : (idst + k).toNat = idst.toNat + k.toNat := bv64_add_lt (by omega)
                have hsk_lt : (src + k).toNat < ar_k.length := by rw [hsk]; omega
                have hik_lt : (idst + k).toNat < ar_k.length := by rw [hik]; omega
                have hsk_val : ar_k[src.toNat + k.toNat]'(by omega) =
                    ar1[src.toNat + k.toNat]'(by omega) := by
                  have h1 := hak_tl (src.toNat + k.toNat) (Nat.le_refl _) (by omega)
                  rw [List.getElem?_eq_getElem (by omega : src.toNat + k.toNat < ar_k.length),
                    List.getElem?_eq_getElem (by omega : src.toNat + k.toNat < ar1.length)] at h1
                  exact Option.some.inj h1
                m6_tiny_lets
                first
                | (apply wp_load_of (M6Tactics2a.out_load_arr32 hsk_lt (sep_ac hmk))
                   m6_tiny_lets
                   apply wp_store_sep (M6Tactics2a.out_store_arr32 hik_lt (sep_ac hmk))
                   intro m hm; m6_tiny_lets; rw [wp_jump])
                | m6_nojoin
                refine hLoopK (k + 1#64, ()) _ (by dsimp only; rw [hk1]; omega)
                  ⟨by rw [hk1]; omega, ar_k.set (idst.toNat + k.toNat)
                     (ar_k[(src + k).toNat]'hsk_lt), by simp [hak_l],
                   fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hak_pre i hi,
                   fun j hj => by
                     rw [hk1] at hj
                     by_cases hjk : j = k.toNat
                     · subst hjk
                       rw [List.getElem?_set_self (by omega)]
                       simp only [hsk, hsk_val,
                         List.getElem?_eq_getElem (by omega : src.toNat + k.toNat < ar1.length)]
                     · rw [List.getElem?_set_ne (by omega)]; exact hak_cp j (by omega),
                   fun i hi1 hi2 => by
                     rw [hk1] at hi1
                     rw [List.getElem?_set_ne (by omega)]; exact hak_tl i (by omega) hi2,
                   by simp only [← hik]; exact sep_ac ‹(array c.pArena _ ⋆ _) _›⟩
              · have hk_eq : k.toNat = 3 + sz := by
                  have hnot : ¬ (k.toNat < 3 + sz) := by
                    c0_cond hc
                    have hlt1 : ¬ k.toNat < (3#64 + sz32.setWidth 64).toNat := hc
                    rwa [hcl_eq] at hlt1
                  omega
                rw [hk_eq] at hak_cp hak_tl; clear hm1 hLoopK Jk
                have hal_cp : ∀ j < sz, ar_k[idst.toNat + 3 + j]? = arPre[src.toNat + 3 + j]? :=
                  fun j hj => by
                    rw [Nat.add_assoc, hak_cp (3 + j) (by omega), ← Nat.add_assoc]
                    exact htail_ag (src.toNat + 3 + j) (by omega) (by omega)
                have ha2_cp : ar_k[idst.toNat + 2]? = ar1[src.toNat + 2]? := hak_cp 2 (by omega)
                m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
                · have hrsn_ne : (ar1[src.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 := by
                    c0_cond hc; rwa [← hhdr_def]
                  m6_tiny_lets; m6_nojoin
                  refine wp_loop_inv
                    (fun (x : Tup Val [i32]) mi =>
                      let (i, ()) := x
                      i.toNat ≤ sz ∧ mk = mi ∧
                      ∀ j < i.toNat,
                        let lit := (ar1[src.toNat + 3 + j]?.getD 0#32).toNat
                        let v := lit / 2
                        ¬ (v < s.core.cur_vars ∧
                          (0#32).slt ((s.core.vals[lit]?.getD 0#8).signExtend 32) = true ∧
                          (rsns1[v]?.getD 0xFFFFFFFF#32).toNat = src.toNat))
                    (fun (i, ()) _ => sz - i.toNat)
                    (fun Ji hLoopI => by
                      m6_tiny_lets; m6_nojoin
                      exact hLoopI (0#32, ()) mk
                        ⟨Nat.zero_le _, rfl, fun _ hj => by simp at hj⟩)
                    (fun Ji (i, ()) _ ⟨hi_le, rfl, hmiss⟩ hLoopI => ?_)
                  · m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
                    · have hi_lt : i.toNat < sz := by
                        c0_cond hc
                        simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, ← hsrc2_eq,
                          Nat.mod_eq_of_lt (src + 2#64).isLt] at hc
                        exact hc
                      have hi1 : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_lt (by omega)
                      have hid3i : (idst + 3#64 + i.setWidth 64).toNat =
                          idst.toNat + 3 + i.toNat := bv64_add3_zext_lt (by omega)
                      have hid3i_lt : (idst + 3#64 + i.setWidth 64).toNat < ar_k.length := by
                        rw [hid3i]; omega
                      let lit32 := ar_k[(idst + 3#64 + i.setWidth 64).toNat]'hid3i_lt
                      let v32 := lit32 >>> 1#32
                      have hlit32_get : lit32 = ar1[src.toNat + 3 + i.toNat]'(by omega) := by
                        have h1 := hak_cp (3 + i.toNat) (by omega)
                        have hle_k : (idst + 3#64 + i.setWidth 64).toNat < ar_k.length := hid3i_lt
                        have hle_1 : src.toNat + 3 + i.toNat < ar1.length := by omega
                        dsimp only [lit32]
                        rw [← Nat.add_assoc idst.toNat 3 i.toNat,
                          ← Nat.add_assoc src.toNat 3 i.toNat, ← hid3i,
                          List.getElem?_eq_getElem hle_k,
                          List.getElem?_eq_getElem hle_1] at h1
                        exact Option.some.inj h1
                      have hid3i_raw : ar_k[(idst.toNat + BitVec.toNat (3 : BitVec 64) +
                          i.toNat) % 2 ^ 64]'(by
                          rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                            Nat.mod_eq_of_lt (by omega)]; omega) = lit32 := by
                        dsimp only [lit32]; congr 1
                        rw [hid3i, show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                          Nat.mod_eq_of_lt (by omega)]
                      have hv_def : v32.toNat = lit32.toNat / 2 := by
                        simp [v32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                      m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
                      · have hv_lt : v32.toNat < s.core.cur_vars := by
                          c0_cond hc
                          rw [hid3i_raw] at hc
                          try rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                          Nat.pow_one] at hc
                          rw [← hv_def, Nat.mod_eq_of_lt (by omega : v32.toNat < 2 ^ 64),
                            Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                          exact hc
                        have hlit_div : lit32.toNat / 2 < s.core.cur_vars := hv_def ▸ hv_lt
                        have hlit_lt_vals : lit32.toNat < s.core.vals.length := by omega
                        have hlit_lt_2cv : lit32.toNat < 2 * s.core.cur_vars := by omega
                        m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
                        · have hval_pos : (0#32).slt
                              ((s.core.vals[lit32.toNat]?.getD 0#8).signExtend 32) = true := by
                            c0_cond hc
                            simp only [hid3i_raw, Nat.mod_eq_of_lt
                              (by have := lit32.isLt; omega : lit32.toNat < 2 ^ 64)] at hc
                            rwa [List.getElem?_eq_getElem hlit_lt_vals, Option.getD_some]
                          have hval_eq1 : s.core.vals[lit32.toNat]?.getD 0#8 = 1#8 :=
                            (bv_i8_slt0_eq_1 (hdom lit32.toNat hlit_lt_2cv)).1.mp hval_pos
                          m6_to_jnz; apply wp_jnz_of <;>
                            (intro hc; try simp only [Arg.val_var] at hc)
                          · have hrs_src : (rsns1[v32.toNat]?.getD 0xFFFFFFFF#32).toNat =
                                src.toNat := by
                              have h1 : rsns1[v32.toNat]?.getD 0xFFFFFFFF#32 =
                                  BitVec.ofNat 32 src.toNat := by
                                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                apply BitVec.eq_of_toNat_eq
                                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                                have h2 : (rsns1[v32.toNat]'(by omega)).setWidth 64 = src := by
                                  c0_cond hc; simp only [hid3i_raw] at hc
                                  have hv_mod : (lit32 >>> 1).toNat % 2 ^ 64 = v32.toNat :=
                                    Nat.mod_eq_of_lt (by have := v32.isLt; omega)
                                  have hlt_mod : (lit32 >>> 1).toNat % 2 ^ 64 < rsns1.length := by
                                    rw [hv_mod]; omega
                                  have hget_eq : rsns1[(lit32 >>> 1).toNat % 2 ^ 64]'hlt_mod =
                                      rsns1[v32.toNat]'(by omega) := by congr 1
                                  rwa [hget_eq] at hc
                                have h3 := congrArg BitVec.toNat h2
                                have hlt_r := (rsns1[v32.toNat]'(by omega)).isLt
                                rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at h3
                              rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                            have hrs0_src := (hrsns_eq_src v32.toNat hv_lt).mp hrs_src
                            have hid_32 : idst.setWidth 32 = BitVec.ofNat 32 idst.toNat := by
                              apply BitVec.eq_of_toNat_eq
                              rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
                            have hv64_idx : (v32.setWidth 64).toNat = v32.toNat :=
                              bv32_zext64_toNat v32
                            m6_tiny_lets; m6_c0_steps
                            refine ⟨by decide, by decide, ?_⟩
                            apply wp_store_sep
                            · simp only [Arg.val_var]
                              refine M6Tactics2a.out_store_rsns
                                (R := array (t := i32) c.pArena ar_k ⋆
                                  array (t := i32) bufPtr buf1 ⋆ R) ?_ (sep_ac hmk)
                              rw [bv32_zext64_toNat]
                              simp only [show (3 : BitVec 64) = 3#64 from rfl]
                              change v32.toNat < rsns1.length; omega
                            intro m hm
                            m6_tiny_lets; m6_c0_steps
                            let rsns' := rsns1.set v32.toNat (idst.setWidth 32)
                            refine hJ_ir () _ ⟨ar_k, rsns', hak_l,
                              by simp only [rsns', List.length_set, hrsns1_l],
                              hak_pre, fun i hi1 hi2 => hak_tl i (by omega) hi2,
                              hal_cp, ha2_cp, pass1_irred_hit_helper har1_l
                                (by rw [hsz_def]; exact hfit) hs_lt hsrc_ref hrsn_ne hsz_def
                                hsz_eq htail_ag hi_lt hlit32_get hv_def hv_lt hval_eq1 hrs0_src
                                hid_lo huniq hid_32 (by omega), ?_⟩
                            · dsimp only [rsns', v32, lit32]
                              simp only [show (3#64 : BitVec 64) = 3 from rfl,
                                show (1#32 : BitVec 32) = 1 from rfl]
                              exact sep_ac hm
                          · have hrs_ne : (rsns1[v32.toNat]?.getD 0xFFFFFFFF#32).toNat ≠
                                src.toNat := by
                              c0_cond hc; simp only [hid3i_raw] at hc
                              have hv_mod : (lit32 >>> 1).toNat % 2 ^ 64 = v32.toNat :=
                                Nat.mod_eq_of_lt (by have := v32.isLt; omega)
                              have hlt_mod : (lit32 >>> 1).toNat % 2 ^ 64 < rsns1.length := by
                                rw [hv_mod]; omega
                              have hget_eq : rsns1[(lit32 >>> 1).toNat % 2 ^ 64]'hlt_mod =
                                  rsns1[v32.toNat]'(by omega) := by congr 1
                              intro heq; apply hc
                              rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
                              apply BitVec.eq_of_toNat_eq
                              have hlt_r :=
                                (rsns1[(lit32 >>> 1).toNat % 2 ^ 64]'hlt_mod).isLt
                              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hget_eq, heq]
                            m6_tiny_lets; m6_c0_steps
                            refine hLoopI (i + 1#32, ()) mk (by dsimp only; rw [hi1]; omega)
                              ⟨by rw [hi1]; omega, rfl, fun j hj => ?_⟩
                            rw [hi1] at hj
                            by_cases hji : j = i.toNat
                            · subst hji
                              have hle1 : src.toNat + 3 + i.toNat < ar1.length := by omega
                              dsimp only
                              rw [List.getElem?_eq_getElem hle1, Option.getD_some, ← hlit32_get]
                              rintro ⟨_, _, heq⟩
                              rw [← hv_def] at heq; exact hrs_ne heq
                            · exact hmiss j (by omega)
                        · have hval_npos : ¬ ((0#32).slt
                              ((s.core.vals[lit32.toNat]?.getD 0#8).signExtend 32) = true) := by
                            c0_cond hc
                            simp only [hid3i_raw, Nat.mod_eq_of_lt
                              (by have := lit32.isLt; omega : lit32.toNat < 2 ^ 64)] at hc
                            rw [List.getElem?_eq_getElem hlit_lt_vals, Option.getD_some, hc]
                            decide
                          m6_tiny_lets; m6_c0_steps
                          refine hLoopI (i + 1#32, ()) mk (by dsimp only; rw [hi1]; omega)
                            ⟨by rw [hi1]; omega, rfl, fun j hj => ?_⟩
                          rw [hi1] at hj; by_cases hji : j = i.toNat
                          · subst hji
                            rw [List.getElem?_eq_getElem
                              (by omega : src.toNat + 3 + i.toNat < ar1.length),
                              Option.getD_some, ← hlit32_get]
                            exact fun h => hval_npos h.2.1
                          · exact hmiss j (by omega)
                      · have hv_ge : ¬ (v32.toNat < s.core.cur_vars) := by
                          c0_cond hc
                          rw [hid3i_raw] at hc
                          try rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                          Nat.pow_one] at hc
                          rw [← hv_def, Nat.mod_eq_of_lt (by omega : v32.toNat < 2 ^ 64),
                            Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                          exact hc
                        m6_tiny_lets; m6_c0_steps
                        refine hLoopI (i + 1#32, ()) mk (by dsimp only; rw [hi1]; omega)
                          ⟨by rw [hi1]; omega, rfl, fun j hj => ?_⟩
                        rw [hi1] at hj; by_cases hji : j = i.toNat
                        · subst hji
                          rw [List.getElem?_eq_getElem
                            (by omega : src.toNat + 3 + i.toNat < ar1.length),
                            Option.getD_some, ← hlit32_get]
                          exact fun ⟨hlt, _⟩ => hv_ge (hv_def ▸ hlt)
                        · exact hmiss j (by omega)
                    · have hi_eq : i.toNat = sz := by
                        have : ¬ (i.toNat < sz) := by
                          c0_cond hc
                          simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, ← hsrc2_eq,
                            Nat.mod_eq_of_lt (src + 2#64).isLt] at hc
                          exact hc
                        omega
                      rw [hi_eq] at hmiss
                      m6_tiny_lets; m6_c0_steps
                      refine hJ_ir () _ ⟨ar_k, rsns1, hak_l, hrsns1_l, hak_pre,
                        fun i hi1 hi2 => hak_tl i (by omega) hi2, hal_cp,
                        ha2_cp, fun v hv => ?_, hmk⟩
                      rw [rw_ite_neg (fun ⟨hlv, heq_s⟩ => pass1_irred_miss_rsn hsz_eq hsz_def
                        htail_ag (by omega) hdom hrsns_eq_src hmiss hv hlv heq_s)]
                · have hrsn_0 : (ar1[src.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 := by
                    rw [List.getElem?_eq_getElem (by omega : src.toNat < ar1.length),
                      Option.getD_some]
                    c0_cond hc; exact hc
                  m6_tiny_lets; m6_c0_steps
                  refine hJ_ir () _ ⟨ar_k, rsns1, hak_l, hrsns1_l, hak_pre,
                    fun i hi1 hi2 => hak_tl i (by omega) hi2, hal_cp, ha2_cp,
                    fun v hv => ?_, hmk⟩
                  rw [rw_ite_neg (fun ⟨hlv, heq_s⟩ => by
                    have h0 := hlv.2.2.2.1
                    rw [heq_s, ← htail_ag src.toNat (Nat.le_refl _) hs_lt] at h0
                    exact absurd hrsn_0 h0)]
          · have hid_eq_src : idst.toNat = src.toNat :=
              congrArg BitVec.toNat (by c0_cond hc; exact hc : idst = src)
            m6_tiny_lets; m6_nojoin
            refine hJ_ir () _ ⟨ar1, rsns1, har1_l, hrsns1_l, fun _ _ => rfl, fun _ _ _ => rfl,
              fun j hj => by rw [hid_eq_src]; exact htail_ag _ (by omega) (by omega),
              by rw [hid_eq_src], fun v hv => ?_, hm1⟩
            dsimp only; split
            · next hcond =>
              have hpre_v := hrsn_inv v hv; dsimp only at hpre_v
              rw [rw_ite_neg (by omega)] at hpre_v
              rw [hpre_v.1]; apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hcond.2, hid_eq_src]
            · rfl
    · have hs_eq : src.toNat = dst.toNat := by
        have hnot : ¬ (src.toNat < dst.toNat) := by c0_cond hc; exact hc
        omega
      clear hdom huniq hmv_orig hsrc_ref_fn
      rw [hs_eq] at hsum hmv_rm htail_ag hrsn_inv
      have hrw_0 : redWords - rlen.toNat = 0 := by have := hmv_rm.le; omega
      have hid_le_dst : idst.toNat ≤ dst.toNat := by omega
      m6_tiny_lets; m6_nojoin; c0_call hPass2
      refine ⟨c, s, arPre, ar1, buf1, rsns1, first_red, R, rfl, hlen, hid_lo, hdst_cap,
        (by omega), (by rw [hbuf1_l]; exact hbuf_b), hmv_bf, hbf_info,
        move_pass1_to_pass2 hlen hdst_cap hid_lo hsum har1_l hrsns1_l
          (by rw [show redWords - rlen.toNat = rw_rem by omega]; exact hrw_sum)
          hpre_ag hmv_ir (by rwa [show redWords - rlen.toNat = rw_rem by omega])
          hmv_bf hbf_info hrsn_inv hm1, ?_⟩
      intro ar2 rsns2 fred' m2 har2_l hrsns2_l h2_pre hmv_2 h2_info hrsn_inv2 hfred' hm2
      have hmid_eq : idst.toNat + rlen.toNat = dst.toNat := hsum
      have hmv_ir_fin : MoveRangeChain ar2 first_red.toNat idst.toNat 0 :=
        hmv_ir.congr fun i _ hi => h2_pre i hi
      have hmv_2_fin : MoveRangeChain ar2 idst.toNat dst.toNat (dst.toNat - idst.toNat) := by
        rw [← hmid_eq, show idst.toNat + rlen.toNat - idst.toNat = rlen.toNat by omega]
        exact hmv_2
      have hfin_clauses := pass2_fin_clauses_helper hmid_eq h2_pre hir_info h2_info
        (fun rp hrp => let ⟨h0, s0, h1, h2, h3, h4, _⟩ := hbf_info rp hrp
          ⟨h0, s0, h1, h2, h3, h4, trivial⟩)
      have hfin_rsns := pass2_fin_rsns_helper hid_lo hmid_eq h2_pre hrsn_inv hrsn_inv2
      have hfred'' : fred' =
          if idst.toNat < dst.toNat then BitVec.ofNat 64 idst.toNat else 0xFFFFFFFF#64 := by
        rw [hfred']; split
        · apply BitVec.eq_of_toNat_eq; rw [bv64_ofNat_toNat_id (by omega)]
        · rfl
      m6_tiny_lets; m6_nojoin
      exact hQ ar2 buf1 rsns2 fred' idst.toNat m2 har2_l hbuf1_l hrsns2_l hid_lo hid_le_dst
        (fun i hi => (h2_pre i (by omega)).trans (hpre_ag i hi)) hmv_ir_fin hmv_2_fin
        hfin_clauses hfin_rsns hfred'' hm2

theorem fullMoveRedPass2Spec_xirrel {a m Q X X'}
    (h : fullMoveRedPass2Spec a m Q X) : fullMoveRedPass2Spec a m Q X' := h

theorem fullMoveRedEndBufSpec_xirrel {a m Q X X'}
    (h : fullMoveRedEndBufSpec a m Q X) : fullMoveRedEndBufSpec a m Q X' := h

end LeanQbe.T.Examples.Kissat.FullM6WatchGc
