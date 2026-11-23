module

public import LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds
public import LeanQbe.T.Examples.Kissat.FullFastCoreBcpLemmas1
public import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1

/-!
# Kissat M7 Inner-Bounds-Check-Free Watch Invariant & Helpers (`FullM7BcpNoBoundsProof0`)

M1-clean (`public section`, zero `@[expose]`, zero `import all`) structural watch-bounds invariant
and core WP building blocks for `FullM7BcpNoBounds`:
1. `WatchSliceBoundsOk` & `FullWatchBoundsInv (st : FullState)`:
   - Every active 2WL slice `wvec[l]` satisfies `off + sz ≤ st.core.wlen` (≤ `c.wcap` under
     `LengthsOk`).
   - Binary watches satisfy `(w0 &&& 0x7FFFFFFF#32).toNat < 2 * cur_vars` and `w0 ≠ 0xFFFFFFFF#32`.
   - Large watches satisfy `(w0 &&& 0x7FFFFFFF#32).toNat < 2 * cur_vars`, `cref < 0x80000000`,
     `2 ≤ clen`, `cref + 3 + clen ≤ arena_len`, and all live clause literals `< 2 * cur_vars`.
2. Preservation lemmas for `full_watch_push`, `full_wstack_defrag`, and `full_add_clause`
   (both abstract state transitions and `Func.wp` preservation over `Full1.full_add_clause_body`).
3. `fullPropLitNoBoundsSpec`, `fullPropagateIgnoreNoBoundsSpec`, `fullPropagateNoBoundsSpec`,
   `SplitWatchBoundsInv`, `PropLitNoBoundsInv`, and inner-bounds-check-free `wp` helpers
   (`noBoundsReplSearch_wp`, `noBoundsAssign_wp`, `noBoundsAlvlAssign_wp`, `m7NoBoundsFinish_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_prop_lit_body full_prop_lit_wf full_prop_lit_wp
  full_propagate_ignore_body full_propagate_ignore_wf full_propagate_ignore_wp
  full_propagate_body full_propagate_wf full_propagate_wp
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec fullWatchPushSpec
  FullTrailExt FullArenaPermEq
open LeanQbe.T.Examples.Kissat.Full.FullAssignAddTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
  LeanQbe.T.Examples.Kissat.Full.FullAssignAddTactics

attribute [local irreducible] fastPropMem

local elab "nb_head_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun false

local elab "nb_head_split" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun true

/-! ## 1. `WatchSliceBoundsOk` & `FullWatchBoundsInv` -/

/-- When a clause at `r` is non-garbage (`PH_GARB == 0`), every literal `< 2 * cur_vars`. -/
@[expose] def fullArenaLiveLitsLt (k : FullCoreState) (r : Nat) : Prop :=
  (fullArenaHdrCore k r &&& 0x00080000#32) = 0#32 →
    ∀ i < fullArenaClauseSizeCore k r,
      (k.arena[r + 3 + i]?.getD 0#32).toNat < 2 * k.cur_vars

theorem fullArenaLiveLitsLt_of_arenaInv {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k)
    (har_len : k.arena_len ≤ k.arena.length) {r : Nat}
    (href : r ∈ fullArenaClauseRefsCore k) :
    fullArenaLiveLitsLt k r := by
  intro hhdr i hi
  have hwf := ha.refs_wf r href
  have hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length :=
    Nat.le_trans (Nat.le_trans hwf.2.2.1 hwf.2.2.2.1) har_len
  have hng : fullArenaClauseGarbCore k r = false := by
    unfold fullArenaClauseGarbCore; simp [hhdr]
  have hlt := ha.lits_lt r href hng
  have hmem : (k.arena[r + 3 + i]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore k r := by
    rw [mem_fullArenaClauseLitsCore_iff hbd]
    refine ⟨i, hi, ?_⟩
    have hi_bd : r + 3 + i < k.arena.length := by omega
    rw [List.getElem?_eq_getElem hi_bd, Option.getD_some]
  exact hlt _ hmem

theorem fullArenaLiveLitsLt_of_nw_arenaInv {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur (withEmptyWatchesCore c k))
    (har_len : k.arena_len ≤ k.arena.length) {r : Nat}
    (href : r ∈ fullArenaClauseRefsCore k) :
    fullArenaLiveLitsLt k r :=
  fullArenaLiveLitsLt_of_arenaInv ha har_len href

/-- Structural inner-bounds invariant on a single 2WL watch-stack slice `k.wstk[p ..< p + rem)`.
Carries blocker literal bounds `(w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars` on both binary
and large entries plus arena extent and literal bounds on large entries, enabling
inner-bounds-check-free watch traversal in `full_prop_lit_nobounds_m7`. -/
inductive WatchSliceBoundsOk (k : FullCoreState) : Nat → Nat → Prop where
  | empty {p} : WatchSliceBoundsOk k p 0
  | bin {p rem} {w0 : BitVec 32} :
      k.wstk[p]? = some w0 →
      (w0 &&& 0x80000000#32) ≠ 0#32 →
      w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      WatchSliceBoundsOk k (p + 1) rem →
      WatchSliceBoundsOk k p (rem + 1)
  | large {p rem} {w0 cref : BitVec 32} :
      k.wstk[p]? = some w0 →
      k.wstk[p + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      cref.toNat < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore k cref.toNat →
      cref.toNat + 3 + fullArenaClauseSizeCore k cref.toNat ≤ k.arena_len →
      fullArenaLiveLitsLt k cref.toNat →
      WatchSliceBoundsOk k (p + 2) rem →
      WatchSliceBoundsOk k p (rem + 2)

theorem WatchSliceBoundsOk.relocate {k k' : FullCoreState} {p p' rem : Nat}
    (hcv : k.cur_vars ≤ k'.cur_vars)
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (_hal : k.arena_len ≤ k'.arena_len)
    (har : ∀ cref : Nat, cref < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore k cref →
      cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len →
      fullArenaLiveLitsLt k cref →
      2 ≤ fullArenaClauseSizeCore k' cref ∧
      cref + 3 + fullArenaClauseSizeCore k' cref ≤ k'.arena_len ∧
      fullArenaLiveLitsLt k' cref)
    (h : WatchSliceBoundsOk k p rem) :
    WatchSliceBoundsOk k' p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt _ ih =>
    refine .bin ((hwstk 0 (by omega)).trans hp) hflag hne (by omega) ?_
    exact ih (p' := p' + 1) fun idx hi => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega)
  | @large p rem w0 cref hp hp1 hflag hblk hlt hsz hfit hlive _ ih =>
    obtain ⟨hsz', hfit', hlive'⟩ := har cref.toNat hlt hsz hfit hlive
    refine .large ((hwstk 0 (by omega)).trans hp)
      ((hwstk 1 (by omega)).trans hp1) hflag (by omega) hlt hsz' hfit' hlive' ?_
    exact ih (p' := p' + 2) fun idx hi => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega)

theorem WatchSliceBoundsOk.mono_wstk {k k' : FullCoreState} {p rem : Nat}
    (hcv : k.cur_vars ≤ k'.cur_vars)
    (hwstk : ∀ idx, p ≤ idx → idx < p + rem → k'.wstk[idx]? = k.wstk[idx]?)
    (hal : k.arena_len ≤ k'.arena_len)
    (har : ∀ cref : Nat, cref < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore k cref →
      cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len →
      fullArenaLiveLitsLt k cref →
      2 ≤ fullArenaClauseSizeCore k' cref ∧
      cref + 3 + fullArenaClauseSizeCore k' cref ≤ k'.arena_len ∧
      fullArenaLiveLitsLt k' cref)
    (h : WatchSliceBoundsOk k p rem) :
    WatchSliceBoundsOk k' p rem :=
  h.relocate hcv (fun idx hi => hwstk (p + idx) (by omega) (by omega)) hal har

theorem WatchSliceBoundsOk.append {k : FullCoreState} {p n m : Nat}
    (h1 : WatchSliceBoundsOk k p n) (h2 : WatchSliceBoundsOk k (p + n) m) :
    WatchSliceBoundsOk k p (n + m) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w0 hp hflag hne hlt _ ih =>
    rw [show rem + 1 + m = (rem + m) + 1 by omega]
    exact .bin hp hflag hne hlt (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      h2))
  | @large p rem w0 cref hp hp1 hflag hblk hlt hsz hfit hlive _ ih =>
    rw [show rem + 2 + m = (rem + m) + 2 by omega]
    exact .large hp hp1 hflag hblk hlt hsz hfit hlive
      (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2))

theorem WatchSliceBoundsOk.append_bin {k : FullCoreState} {p rem : Nat} {w0 : BitVec 32}
    (h : WatchSliceBoundsOk k p rem) (hw0 : k.wstk[p + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hblk : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars) :
    WatchSliceBoundsOk k p (rem + 1) :=
  h.append (.bin hw0 hflag hne hblk .empty)

theorem WatchSliceBoundsOk.append_large {k : FullCoreState} {p rem : Nat} {w0 cref : BitVec 32}
    (h : WatchSliceBoundsOk k p rem) (hw0 : k.wstk[p + rem]? = some w0)
    (hw1 : k.wstk[p + rem + 1]? = some cref) (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hblk : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars) (hlt : cref.toNat < 0x80000000)
    (hsz : 2 ≤ fullArenaClauseSizeCore k cref.toNat)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore k cref.toNat ≤ k.arena_len)
    (hlive : fullArenaLiveLitsLt k cref.toNat) :
    WatchSliceBoundsOk k p (rem + 2) :=
  h.append (.large hw0 hw1 hflag hblk hlt hsz hfit hlive .empty)

theorem WatchSliceBoundsOk.inv_bin {k : FullCoreState} {p rem : Nat} {w0 : BitVec 32}
    (h : WatchSliceBoundsOk k p rem) (hpos : 0 < rem)
    (hw0 : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    WatchSliceBoundsOk k (p + 1) (rem - 1) := by
  cases h with
  | empty => omega
  | bin hw hfl hne hblk hrest =>
    rcases Option.some.inj (hw0.symm.trans hw) with rfl
    exact ⟨hne, hblk, by simpa using hrest⟩
  | large hw _ hfl =>
    rcases Option.some.inj (hw0.symm.trans hw) with rfl
    exact absurd hfl hflag

theorem WatchSliceBoundsOk.inv_large {k : FullCoreState} {p rem : Nat} {w0 : BitVec 32}
    (h : WatchSliceBoundsOk k p rem) (hpos : 0 < rem)
    (hw0 : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ ∃ cref : BitVec 32,
      k.wstk[p + 1]? = some cref ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      cref.toNat < 0x80000000 ∧
      2 ≤ fullArenaClauseSizeCore k cref.toNat ∧
      cref.toNat + 3 + fullArenaClauseSizeCore k cref.toNat ≤ k.arena_len ∧
      fullArenaLiveLitsLt k cref.toNat ∧
      WatchSliceBoundsOk k (p + 2) (rem - 2) := by
  cases h with
  | empty => omega
  | bin hw hfl =>
    rcases Option.some.inj (hw0.symm.trans hw) with rfl
    exact absurd hflag hfl
  | large hw hw1 _ hblk hlt hsz hfit hlive hrest =>
    rcases Option.some.inj (hw0.symm.trans hw) with rfl
    exact ⟨by omega, _, hw1, hblk, hlt, hsz, hfit, hlive, by simpa using hrest⟩

theorem WatchSliceBoundsOk.head_blk_lt {k : FullCoreState} {p rem : Nat} {w0 : BitVec 32}
    (h : WatchSliceBoundsOk k p rem) (hpos : 0 < rem) (hw0 : k.wstk[p]? = some w0) :
    (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars := by
  by_cases hf : (w0 &&& 0x80000000#32) = 0#32
  · obtain ⟨_, _, _, hblk, _⟩ := h.inv_large hpos hw0 hf; exact hblk
  · exact (h.inv_bin hpos hw0 hf).2.1

theorem WatchSliceBoundsOk.of_watchSliceOk {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p rem : Nat}
    (ha : FullArenaClausesInv c F_cur k) (har_len : k.arena_len ≤ k.arena.length)
    (hs : WatchSliceOk F_cur k lit p rem)
    (hblk : ∀ q w0 cref, p ≤ q → q + 1 < p + rem →
      k.wstk[q]? = some w0 → k.wstk[q + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 → (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars) :
    WatchSliceBoundsOk k p rem := by
  induction hs with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt _ _ ih =>
    exact .bin hp hflag hne hlt (ih fun q w cr hq1 hq2 => hblk q w cr (by omega) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    have hwf := ha.refs_wf cref.toNat href
    have hfit : cref.toNat + 3 + fullArenaClauseSizeCore k cref.toNat ≤ k.arena_len :=
      Nat.le_trans hwf.2.2.1 hwf.2.2.2.1
    exact .large hp hp1 hflag (hblk p w0 cref (Nat.le_refl _) (by omega) hp hp1 hflag) hlt
      (Nat.le_trans (by decide : 2 ≤ 3) hwf.2.1) hfit
      (fullArenaLiveLitsLt_of_arenaInv ha har_len href)
      (ih fun q w cr hq1 hq2 => hblk q w cr (by omega) (by omega))

/-- Clean, composable watch-validity invariant `FullWatchBoundsInv (st : FullState)`:
- `layout`: every `wvec[l]` satisfies `off + sz ≤ st.core.wlen` (`≤ c.wcap` under `LengthsOk`),
  positive-size slices start at `off ≥ 1`, distinct active slices are disjoint, and active
  slices contain no `0xFFFFFFFFu` sentinel words.
- `slices`: in 2WL mode (`dense_mode = 0#64`), every literal `l < 2 * st.core.cur_vars` has a
  `WatchSliceBoundsOk` slice covering `[off, off + sz)`. -/
structure FullWatchBoundsInv (st : FullState) : Prop where
  layout : WatchStackLayout st.core
  slices : st.core.dense_mode = 0#64 →
    ∀ l < 2 * st.core.cur_vars,
      WatchSliceBoundsOk st.core (fullWatchOffCore st.core l) (fullWatchSizeCore st.core l)

theorem FullWatchBoundsInv.slice_le_wcap {c : FullCfg} {st : FullState}
    (hw : FullWatchBoundsInv st) (hl : st.LengthsOk c) {l : Nat} (hlv : l < 2 * st.core.cur_vars) :
    fullWatchOffCore st.core l + fullWatchSizeCore st.core l ≤ c.wcap :=
  Nat.le_trans (hw.layout.bounds l hlv) hl.core_ok.wlen_le

theorem FullWatchBoundsInv.with_scratch {st : FullState} (hw : FullWatchBoundsInv st)
    (sc' : FullScratch) : FullWatchBoundsInv { st with scratch := sc' } :=
  ⟨hw.layout, hw.slices⟩

theorem FullWatchBoundsInv.with_nonwatch {st st' : FullState} (hw : FullWatchBoundsInv st)
    (hcv : st'.core.cur_vars = st.core.cur_vars)
    (hdm : st'.core.dense_mode = st.core.dense_mode)
    (hwv : st'.core.wvec = st.core.wvec) (hws : st'.core.wstk = st.core.wstk)
    (hwl : st'.core.wlen = st.core.wlen)
    (hal : st.core.arena_len ≤ st'.core.arena_len)
    (har : ∀ cref : Nat, cref < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore st.core cref →
      cref + 3 + fullArenaClauseSizeCore st.core cref ≤ st.core.arena_len →
      fullArenaLiveLitsLt st.core cref →
      2 ≤ fullArenaClauseSizeCore st'.core cref ∧
      cref + 3 + fullArenaClauseSizeCore st'.core cref ≤ st'.core.arena_len ∧
      fullArenaLiveLitsLt st'.core cref) :
    FullWatchBoundsInv st' := by
  refine ⟨hw.layout.with_wstk hcv hwv hws hwl, fun hdm0 l hl => ?_⟩
  have hwo : fullWatchOffCore st'.core l = fullWatchOffCore st.core l := by
    unfold fullWatchOffCore; rw [hwv]
  have hwsz : fullWatchSizeCore st'.core l = fullWatchSizeCore st.core l := by
    unfold fullWatchSizeCore; rw [hwv]
  rw [hwo, hwsz]
  exact (hw.slices (hdm.symm.trans hdm0) l (hcv ▸ hl)).mono_wstk (by omega)
    (fun idx _ _ => by rw [hws]) hal har

theorem FullWatchBoundsInv.with_safetySlice {c : FullCfg} {st st' : FullState}
    (hw : FullWatchBoundsInv st)
    (hpres : PreservesCoreSlice (fullSafetySlice c).coreProj st st') :
    FullWatchBoundsInv st' := by
  have hcore : st'.core = st.core := fullCoreState_agrees_with_scratch hpres
  exact ⟨hcore ▸ hw.layout, fun h0 l hl => hcore ▸ hw.slices (hcore ▸ h0) l (hcore ▸ hl)⟩

theorem FullWatchBoundsInv.of_witnessInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} (hw : FullWitnessInv c F0 F_cur st.core)
    (har_len : st.core.arena_len ≤ st.core.arena.length) (hdm : st.core.dense_mode = 0#64)
    (hblk : ∀ l < 2 * st.core.cur_vars, ∀ q w0 cref,
      fullWatchOffCore st.core l ≤ q →
      q + 1 < fullWatchOffCore st.core l + fullWatchSizeCore st.core l →
      st.core.wstk[q]? = some w0 → st.core.wstk[q + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 → (w0 &&& 0x7FFFFFFF#32).toNat < 2 * st.core.cur_vars) :
    FullWatchBoundsInv st := by
  have hwat : WatchesInv F_cur st.core := by
    have h := hw.watches; unfold ModeWatchesInv at h; simpa [hdm] using h
  refine ⟨hwat.layout, fun _ l hl =>
    WatchSliceBoundsOk.of_watchSliceOk hw.arena har_len (hwat.slices l hl) (hblk l hl)⟩

/-! ## 2. Arena Helpers & `wstack_defrag` / `watch_push` / `add_clause` Preservation -/

private theorem fullArenaHdrCore_congr {k k' : FullCoreState} {r : Nat}
    (h : k'.arena[r]? = k.arena[r]?) : fullArenaHdrCore k' r = fullArenaHdrCore k r := by
  unfold fullArenaHdrCore; rw [h]

private theorem fullArenaClauseSizeCore_congr {k k' : FullCoreState} {r : Nat}
    (h : k'.arena[r + 2]? = k.arena[r + 2]?) :
    fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
  unfold fullArenaClauseSizeCore; rw [h]

theorem fullArenaLiveLitsLt_of_hold {k k' : FullCoreState} {r : Nat}
    (hcv : k.cur_vars ≤ k'.cur_vars)
    (h0 : k'.arena[r]? = k.arena[r]?) (h2 : k'.arena[r + 2]? = k.arena[r + 2]?)
    (hlits : ∀ i < fullArenaClauseSizeCore k r, k'.arena[r + 3 + i]? = k.arena[r + 3 + i]?)
    (hlive : fullArenaLiveLitsLt k r) :
    fullArenaLiveLitsLt k' r := by
  intro hhdr i hi
  rw [fullArenaHdrCore_congr h0] at hhdr
  rw [fullArenaClauseSizeCore_congr h2] at hi
  rw [hlits i hi]
  exact Nat.lt_of_lt_of_le (hlive hhdr i hi) (Nat.mul_le_mul_left 2 hcv)

/-- Arena extension `[0 ..< alen)` preserved (`full_alloc_cl` / `full_add_clause`). -/
theorem WatchSliceBoundsOk.with_arena_extend {k k' : FullCoreState} {p rem : Nat}
    (hcv : k.cur_vars ≤ k'.cur_vars) (hws : k'.wstk = k.wstk) (hal : k.arena_len ≤ k'.arena_len)
    (hhold : ∀ i < k.arena_len, k'.arena[i]? = k.arena[i]?)
    (h : WatchSliceBoundsOk k p rem) :
    WatchSliceBoundsOk k' p rem :=
  h.mono_wstk hcv (fun _ _ _ => by rw [hws]) hal fun cref _ hsz hfit hlive => by
    have h0 : k'.arena[cref]? = k.arena[cref]? := hhold cref (by omega)
    have h2 : k'.arena[cref + 2]? = k.arena[cref + 2]? := hhold (cref + 2) (by omega)
    have hsz_eq : fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref :=
      fullArenaClauseSizeCore_congr h2
    exact ⟨hsz_eq ▸ hsz, by rw [hsz_eq]; omega,
      fullArenaLiveLitsLt_of_hold hcv h0 h2 (fun i hi => hhold (cref + 3 + i) (by omega)) hlive⟩

/-- Reconstruct `WatchSliceBoundsOk k' p rem` across any arena transformation once
`FullArenaClausesInv c F_cur k'` and `WatchSliceOk F_cur k' lit p rem` hold. -/
theorem WatchSliceBoundsOk.reconstruct_of_arenaInv {c : FullCfg} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p rem : Nat}
    (hcv : k.cur_vars ≤ k'.cur_vars)
    (hws : ∀ idx, p ≤ idx → idx < p + rem → k'.wstk[idx]? = k.wstk[idx]?)
    (ha' : FullArenaClausesInv c F_cur k') (har_len' : k'.arena_len ≤ k'.arena.length)
    (hs' : WatchSliceOk F_cur k' lit p rem)
    (hb : WatchSliceBoundsOk k p rem) :
    WatchSliceBoundsOk k' p rem := by
  induction hs' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt _ _ ih =>
    have ⟨_, _, hbrest⟩ := hb.inv_bin (by omega)
      ((hws p (Nat.le_refl _) (by omega)).symm.trans hp) hflag
    exact .bin hp hflag hne hlt (ih (fun idx h1 h2 => hws idx (by omega) (by omega)) hbrest)
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    have ⟨_, _, _, hblk, _, _, _, _, hbrest⟩ := hb.inv_large (by omega)
      ((hws p (Nat.le_refl _) (by omega)).symm.trans hp) hflag
    have hwf := ha'.refs_wf cref.toNat href
    exact .large hp hp1 hflag (by omega) hlt
      (Nat.le_trans (by decide : 2 ≤ 3) hwf.2.1)
      (Nat.le_trans hwf.2.2.1 hwf.2.2.2.1)
      (fullArenaLiveLitsLt_of_arenaInv ha' har_len' href)
      (ih (fun idx h1 h2 => hws idx (by omega) (by omega)) hbrest)

theorem WatchSliceBoundsOk.reconstruct_of_nw_arenaInv {c : FullCfg} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p rem : Nat}
    (hcv : k.cur_vars ≤ k'.cur_vars)
    (hws : ∀ idx, p ≤ idx → idx < p + rem → k'.wstk[idx]? = k.wstk[idx]?)
    (ha' : FullArenaClausesInv c F_cur (withEmptyWatchesCore c k'))
    (har_len' : k'.arena_len ≤ k'.arena.length)
    (hs' : WatchSliceOk F_cur k' lit p rem)
    (hb : WatchSliceBoundsOk k p rem) :
    WatchSliceBoundsOk k' p rem := by
  induction hs' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt _ _ ih =>
    have ⟨_, _, hbrest⟩ := hb.inv_bin (by omega)
      ((hws p (Nat.le_refl _) (by omega)).symm.trans hp) hflag
    exact .bin hp hflag hne hlt (ih (fun idx h1 h2 => hws idx (by omega) (by omega)) hbrest)
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    have ⟨_, _, _, hblk, _, _, _, _, hbrest⟩ := hb.inv_large (by omega)
      ((hws p (Nat.le_refl _) (by omega)).symm.trans hp) hflag
    have hwf := ha'.refs_wf cref.toNat href
    exact .large hp hp1 hflag (by omega) hlt
      (Nat.le_trans (by decide : 2 ≤ 3) hwf.2.1)
      (Nat.le_trans hwf.2.2.1 hwf.2.2.2.1)
      (fullArenaLiveLitsLt_of_nw_arenaInv ha' har_len' href)
      (ih (fun idx h1 h2 => hws idx (by omega) (by omega)) hbrest)

/-- Reconstruct `FullWatchBoundsInv` across any `cur_vars`/`wstk`-preserving arena step once
`FullWitnessInv c F0 F_cur st'.core` holds (`full_add_clause` garbage rollback, etc.). -/
theorem FullWatchBoundsInv.reconstruct_of_witnessInv {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {st st' : FullState}
    (hwb : FullWatchBoundsInv st) (hw' : FullWitnessInv c F0 F_cur st'.core)
    (har_len' : st'.core.arena_len ≤ st'.core.arena.length)
    (hdm0 : st.core.dense_mode = 0#64) (hdm' : st'.core.dense_mode = 0#64)
    (hcv : st.core.cur_vars = st'.core.cur_vars)
    (hwv : st'.core.wvec = st.core.wvec) (hws : st'.core.wstk = st.core.wstk) :
    FullWatchBoundsInv st' := by
  have hwat' : WatchesInv F_cur st'.core := by
    have h := hw'.watches; unfold ModeWatchesInv at h; simpa [hdm'] using h
  refine ⟨hwat'.layout, fun _ l hl => ?_⟩
  have hwo : fullWatchOffCore st'.core l = fullWatchOffCore st.core l := by
    unfold fullWatchOffCore; rw [hwv]
  have hwsz : fullWatchSizeCore st'.core l = fullWatchSizeCore st.core l := by
    unfold fullWatchSizeCore; rw [hwv]
  have hsl := hwat'.slices l hl
  rw [hwo, hwsz] at hsl ⊢
  exact (hwb.slices hdm0 l (hcv ▸ hl)).reconstruct_of_arenaInv (by omega)
    (fun _ _ _ => by rw [hws]) hw'.arena har_len' hsl

/-- `fullWstackDefragSpec` preserves `FullWatchBoundsInv`. -/
theorem fullWstackDefrag_preserves_watchBoundsInv {s : FullState}
    (hw : FullWatchBoundsInv s)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hpres : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        l = fullWatchSizeCore s.core l ∧
      ∀ k < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l + k]? =
          s.core.wstk[fullWatchOffCore s.core l + k]?) :
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } }
    FullWatchBoundsInv s' := by
  intro s'
  refine ⟨hlay', fun hdm0 l hl => ?_⟩
  obtain ⟨hsz, hslice⟩ := hpres l hl
  change WatchSliceBoundsOk s'.core (fullWatchOffCore s'.core l) (fullWatchSizeCore s'.core l)
  rw [show fullWatchSizeCore s'.core l = fullWatchSizeCore s.core l from hsz]
  exact (hw.slices hdm0 l hl).relocate (k' := s'.core) (p' := fullWatchOffCore s'.core l)
    (Nat.le_refl s.core.cur_vars) (fun idx hi => hslice idx hi) (Nat.le_refl s.core.arena_len)
    (fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩)

/-- Composable `wp` preservation lemma for `full_wstack_defrag` under `FullWatchBoundsInv`. -/
theorem full_wstack_defrag_preserves_watchBoundsInv_wp {Γ : Env}
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hwb : FullWatchBoundsInv s) (hm : (FullMem c s ⋆ R) m)
    (Q : Post []) (X : XPost)
    (hpost : ∀ s' m',
      s'.LengthsOk c → FullWatchBoundsInv s' → (1 ≤ s.core.wlen → 1 ≤ s'.core.wlen) →
      (∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
      (∃ wvec' wstk' wlen' wsort', s' =
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
          scratch := { s.scratch with wsort := wsort' } }) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (.call "full_wstack_defrag" (as := [i64]) (bs := []) (.imm c.hdr, ()) fun _ =>
      .ret ()) m := by
  c0_call hDefrag
  refine ⟨c, s, R, rfl, hlen, hwb.layout, hm,
    fun wvec' wstk' wlen' wsort' m' hlen' hlay' hwlen' hpres hm' => ?_⟩
  let s' : FullState :=
    { s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s.scratch with wsort := wsort' } }
  have hwb' := fullWstackDefrag_preserves_watchBoundsInv (wsort' := wsort') hwb hlay' hpres
  nb_head_steps
  exact hpost s' m' hlen' hwb' hwlen' hpres ⟨wvec', wstk', wlen', wsort', rfl⟩ hm'

/-- `fullWatchPushSpec` preserves `FullWatchBoundsInv` whenever the pushed watch word(s) satisfy
the inner-bounds preconditions (`blk < 2 * cur_vars` and for `cnt = 2`, valid clause extent and
live clause literals `< 2 * cur_vars`). -/
theorem fullWatchPush_preserves_watchBoundsInv {s : FullState}
    {lit w0 w1 cnt : BitVec 32} {ok : Bool}
    (hw : FullWatchBoundsInv s)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wusable' : BitVec 64}
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' })
    (hbin : s.core.dense_mode = 0#64 → cnt.toNat = 1 →
      (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hlarge : s.core.dense_mode = 0#64 → cnt.toNat = 2 →
      (w0 &&& 0x80000000#32) = 0#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars ∧
      w1.toNat < 0x80000000 ∧
      2 ≤ fullArenaClauseSizeCore s.core w1.toNat ∧
      w1.toNat + 3 + fullArenaClauseSizeCore s.core w1.toNat ≤ s.core.arena_len ∧
      fullArenaLiveLitsLt s.core w1.toNat)
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' } l =
        fullWatchSizeCore s.core l ∧
      ∀ idx < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' } l +
          idx]? = s.core.wstk[fullWatchOffCore s.core l + idx]?)
    (hok_true : ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        lit.toNat = fullWatchSizeCore s.core lit.toNat + cnt.toNat ∧
      (∀ idx < fullWatchSizeCore s.core lit.toNat,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
          lit.toNat + idx]? = s.core.wstk[fullWatchOffCore s.core lit.toNat + idx]?) ∧
      wstk'[fullWatchOffCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        lit.toNat + fullWatchSizeCore s.core lit.toNat]? = some w0 ∧
      (cnt.toNat = 2 →
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
          lit.toNat + fullWatchSizeCore s.core lit.toNat + 1]? = some w1))
    (hok_false : ok = false → lit.toNat < 2 * s.core.cur_vars →
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        lit.toNat = fullWatchSizeCore s.core lit.toNat ∧
      ∀ idx < fullWatchSizeCore s.core lit.toNat,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
          lit.toNat + idx]? = s.core.wstk[fullWatchOffCore s.core lit.toNat + idx]?) :
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } }
    FullWatchBoundsInv s' := by
  intro s'
  refine ⟨hlay', fun hdm0 l hl => ?_⟩
  have har_id : ∀ cref : Nat, cref < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore s.core cref →
      cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena_len →
      fullArenaLiveLitsLt s.core cref →
      2 ≤ fullArenaClauseSizeCore s'.core cref ∧
      cref + 3 + fullArenaClauseSizeCore s'.core cref ≤ s'.core.arena_len ∧
      fullArenaLiveLitsLt s'.core cref := fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩
  by_cases hle : l = lit.toNat
  · subst hle; cases ok with
    | false =>
      obtain ⟨hsz, hpre⟩ := hok_false rfl hl
      change WatchSliceBoundsOk s'.core
        (fullWatchOffCore s'.core lit.toNat) (fullWatchSizeCore s'.core lit.toNat)
      rw [hsz]
      exact (hw.slices hdm0 lit.toNat hl).relocate (k' := s'.core)
        (p' := fullWatchOffCore s'.core lit.toNat) (Nat.le_refl s.core.cur_vars) hpre
        (Nat.le_refl s.core.arena_len) har_id
    | true =>
      obtain ⟨_, hcnt, hsz, hpre, hw0', hw1'⟩ := hok_true rfl
      have hbase := (hw.slices hdm0 lit.toNat hl).relocate (k' := s'.core)
        (p' := fullWatchOffCore s'.core lit.toNat) (Nat.le_refl s.core.cur_vars) hpre
        (Nat.le_refl s.core.arena_len) har_id
      change WatchSliceBoundsOk s'.core
        (fullWatchOffCore s'.core lit.toNat) (fullWatchSizeCore s'.core lit.toNat)
      rw [hsz]
      rcases hcnt with hc1 | hc2
      · rw [hc1]; obtain ⟨hf, hn, hblk⟩ := hbin hdm0 hc1
        exact hbase.append_bin hw0' hf hn hblk
      · rw [hc2]; obtain ⟨hf, hblk, hlt, hcsz, hfit, hlive⟩ := hlarge hdm0 hc2
        exact hbase.append_large hw0' (hw1' hc2) hf hblk hlt hcsz hfit hlive
  · obtain ⟨hsz, hpre⟩ := hother l hl hle
    change WatchSliceBoundsOk s'.core (fullWatchOffCore s'.core l) (fullWatchSizeCore s'.core l)
    rw [hsz]
    exact (hw.slices hdm0 l hl).relocate (k' := s'.core) (p' := fullWatchOffCore s'.core l)
      (Nat.le_refl s.core.cur_vars) hpre (Nat.le_refl s.core.arena_len) har_id

/-- Composable `wp` preservation lemma for `full_watch_push` under `FullWatchBoundsInv`. -/
theorem full_watch_push_preserves_watchBoundsInv_wp {Γ : Env}
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {s : FullState} {lit w0 w1 cnt : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hwb : FullWatchBoundsInv s)
    (hc1 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hc2 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hbin : s.core.dense_mode = 0#64 → cnt.toNat = 1 →
      (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hlarge : s.core.dense_mode = 0#64 → cnt.toNat = 2 →
      (w0 &&& 0x80000000#32) = 0#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars ∧
      w1.toNat < 0x80000000 ∧
      2 ≤ fullArenaClauseSizeCore s.core w1.toNat ∧
      w1.toNat + 3 + fullArenaClauseSizeCore s.core w1.toNat ≤ s.core.arena_len ∧
      fullArenaLiveLitsLt s.core w1.toNat)
    (hm : (FullMem c s ⋆ R) m) (Q : Post [.bool]) (X : XPost)
    (hpost : ∀ (ok : Bool) s' m',
      s'.LengthsOk c → FullWatchBoundsInv s' →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
      (.imm c.hdr, (.imm lit, (.imm w0, (.imm w1, (.imm cnt, ()))))) fun r =>
      .ret (.var r.1, ())) m := by
  c0_call hPush
  refine ⟨c, s, R, rfl, hlen, hwb.layout, hc1, hc2, hm, ?_⟩
  intro ok wvec' wstk' wlen' wu' wsort' m' s' hlen' hlay' hoth hokt hokf hm'
  nb_head_steps
  have hwb' := fullWatchPush_preserves_watchBoundsInv (wsort' := wsort') hwb hlay' hbin hlarge
    hoth (fun ht => let ⟨h1, h2, h3, h4, h5, h6⟩ := hokt ht; ⟨h1, h2, h3, h4, h5, h6⟩)
    (fun hf => (hokf hf).1)
  exact hpost ok s' m' hlen' hwb' hm'

private theorem bv32_and_7f_toNat_le (x : BitVec 32) :
    (x &&& 0x7FFFFFFF#32).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_left

private theorem full_add_clause_bin_step {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {lit other : BitVec 32}
    (hw : FullWitnessInv c F0 F_cur s.core) (hwb : FullWatchBoundsInv s)
    (_hdm : s.core.dense_mode = 0#64) (hcv : s.core.cur_vars < 2 ^ 29)
    (_hlit : lit.toNat < 2 * s.core.cur_vars) (hoth : other.toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, other.toNat]))
    {ok : Bool} {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hoth_w : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        l = fullWatchSizeCore s.core l ∧
      ∀ idx < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } l +
          idx]? = s.core.wstk[fullWatchOffCore s.core l + idx]?)
    (hokt : ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧ (1 = 1 ∨ 1 = 2) ∧
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        lit.toNat = fullWatchSizeCore s.core lit.toNat + 1 ∧
      (∀ idx < fullWatchSizeCore s.core lit.toNat,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } lit.toNat +
          idx]? = s.core.wstk[fullWatchOffCore s.core lit.toNat + idx]?) ∧
      wstk'[fullWatchOffCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } lit.toNat +
        fullWatchSizeCore s.core lit.toNat]? =
        some ((other &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ∧
      (1 = 2 →
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } lit.toNat +
          fullWatchSizeCore s.core lit.toNat + 1]? = some 0#32))
    (hokf : ok = false → lit.toNat < 2 * s.core.cur_vars →
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        lit.toNat = fullWatchSizeCore s.core lit.toNat ∧
      ∀ idx < fullWatchSizeCore s.core lit.toNat,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } lit.toNat +
          idx]? = s.core.wstk[fullWatchOffCore s.core lit.toNat + idx]?) :
    let s1 : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { s.scratch with wsort := wsort' } }
    FullWitnessInv c F0 F_cur s1.core ∧ FullWatchBoundsInv s1 := by
  let b := (other &&& 0x7FFFFFFF#32) ||| 0x80000000#32
  have hb_ne : b ≠ 0xFFFFFFFF#32 := bv32_tag_bin_ne_sent (by omega)
  have hwat : ModeWatchesInv F_cur
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } :=
    Full.FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv (lit := lit) (w0 := b)
      (w1 := 0#32) (cnt := 1#32) hw.watches
      hlay' rfl rfl (fun _ hr => hr)
      (fun _ => ⟨bv32_tag_bin_flag other, hb_ne,
        by rw [bv32_tag_bin_mask (by omega)]; exact hoth,
        by rw [bv32_tag_bin_mask (by omega)]; exact hent⟩)
      (fun hc => absurd hc (by decide)) hoth_w hokt hokf
  have hw1 := Full.FullAssignAddSpecs.watchUpdate_preserves_witness hw hwat
  have hwb1 := fullWatchPush_preserves_watchBoundsInv (lit := lit) (w0 := b) (w1 := 0#32)
    (cnt := 1#32) (wsort' := wsort') hwb hlay'
    (fun _ _ => ⟨bv32_tag_bin_flag other, hb_ne,
      by rw [bv32_tag_bin_mask (by omega)]; exact hoth⟩)
    (fun _ hc => absurd hc (by decide)) hoth_w hokt hokf
  exact ⟨hw1, hwb1⟩

/-- Direct `Func.wp` proof that `Full1.full_add_clause_body` preserves
`FullWitnessInv ∧ FullWatchBoundsInv` (reusing `Full.fullAllocClSpec` and
`Full.fullWatchPushSpec`, zero changes to frozen `Full1..6*`). -/
theorem full_add_clause_preserves_watchBoundsInv_wp (Γ : Env)
    (hAlloc : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
      {len glue : BitVec 32} {red : Bool} {R : Mem 64 → Prop} {m : Mem 64}
      {Q : Post [i64]} {X : XPost},
      s.LengthsOk c → FullWitnessInv c F0 F_cur s.core → FullWatchBoundsInv s →
      s.core.dense_mode = 0#64 → len.toNat ≤ c.max_vars →
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat))) →
      (FullMem c s ⋆ R) m →
      (∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullWatchBoundsInv s' →
        (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m') →
      Func.wp Γ Full.full_add_clause_body (c.hdr, len, glue, red, ()) m Q X := by
  intro c F0 F_cur s len glue red R m Q X hlen hw hwb hdm _hlen_bd hcl_bd hm hQ
  have hmv := c.hmaxv; have har := c.harena; have hwcap := c.hwcap
  unfold dimacsBound at hmv har hwcap; have hco := hlen.core_ok
  have hcv_lt : s.core.cur_vars < 2 ^ 29 := by have := hco.cur_vars_le; omega
  faa_head_steps
  refine wp_head_jnz_iff (b := decide (len.toNat = 2))
    (by simpa [Arg.val_var] using bv32_beq_nat_eq (x := len) (n := 2) (by decide)) ?_
  rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun h2 => ?_, fun hne2 => ?_⟩
  · obtain ⟨hlits_lt, _hnd2, hent2⟩ := hcl_bd (by omega)
    have htm_gt0 : 0 < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
    have htm_gt1 : 1 < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
    let l0 := s.core.tmp[0]'htm_gt0; let l1 := s.core.tmp[1]'htm_gt1
    have htmp_take2 : (s.core.tmp.take 2).map BitVec.toNat = [l0.toNat, l1.toNat] := by
      refine List.ext_getElem (by simp [hco.tmp_len_arr]; omega) fun k hk _ => ?_
      match k, hk with | 0, _ => simp [l0] | 1, _ => simp [l1]
    rw [h2, htmp_take2] at hlits_lt hent2
    have hl0_lt : l0.toNat < 2 * s.core.cur_vars := hlits_lt _ (by simp)
    have hl1_lt : l1.toNat < 2 * s.core.cur_vars := hlits_lt _ (by simp)
    have hent2_swap := entails_swap2 hent2
    let b0 := (l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let b1 := (l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    have hb0_ne : b0 ≠ 0xFFFFFFFF#32 := bv32_tag_bin_ne_sent (by omega)
    have hb1_ne : b1 ≠ 0xFFFFFFFF#32 := bv32_tag_bin_ne_sent (by omega)
    faa_steps; c0_call hPush
    refine ⟨c, s, R, rfl, hlen, hwb.layout, (fun _ => hb0_ne),
      (fun hc => absurd hc (by decide)), hm, ?_⟩
    intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1 hlay1 hoth1 hok1t hok1f hm1
    obtain ⟨hw1, hwb1⟩ := full_add_clause_bin_step hw hwb hdm hcv_lt hl0_lt hl1_lt hent2
      hlay1 hoth1 hok1t (fun h => (hok1f h).1)
    faa_steps
    · subst hc; c0_call hPush
      refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun _ => hb1_ne),
        (fun hc => absurd hc (by decide)), hm1, ?_⟩
      intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
      obtain ⟨hw2, hwb2⟩ := full_add_clause_bin_step hw1 hwb1 hdm hcv_lt hl1_lt hl0_lt hent2_swap
        hlay2 hoth2 hok2t (fun h => (hok2f h).1)
      faa_steps
      · let s_fin : FullState :=
          { s2 with core := { s2.core with num_binary := s.core.num_binary + 1#64 } }
        have hwat2 : ModeWatchesInv F_cur s2.core := hw2.watches
        have hwat_fin : ModeWatchesInv F_cur s_fin.core :=
          hwat2.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
        have hw_fin : FullWitnessInv c F0 F_cur s_fin.core :=
          Full.FullAssignAddSpecs.watchUpdate_preserves_witness hw (oom' := s.core.oom) hwat_fin
        have hwb_fin : FullWatchBoundsInv s_fin :=
          hwb2.with_nonwatch rfl rfl rfl rfl rfl (Nat.le_refl _)
            (fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩)
        exact hQ 0xFFFFFFFE#64 s_fin _
          { core_ok := { hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }
            scratch_ok := hlen2.scratch_ok }
          hw_fin hwb_fin (Or.inr (Or.inl rfl)) ‹_›
      · exact hQ 0xFFFFFFFF#64 s2 m2 hlen2 hw2 hwb2 (Or.inl rfl) hm2
    · exact hQ 0xFFFFFFFF#64 s1 m1 hlen1 hw1 hwb1 (Or.inl rfl) hm1
  · faa_head_steps
    refine wp_head_jnz_iff (b := decide (len.toNat < 3))
      (by simp only [Arg.val_var]; simpa [bv_ofNat_toNat_eq len] using
        bv32_ult_eq len.isLt (b := 3) (by decide)) ?_
    rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hlt3 => ?_, fun hge3 => ?_⟩
    · faa_steps; exact hQ 0xFFFFFFFF#64 s m hlen hw hwb (Or.inl rfl) hm
    · have hge3' : 3 ≤ len.toNat := by omega
      have hs_alen_lt32 : s.core.arena_len < 0xFFFFFFFF := by have := hco.arena_len_le; omega
      obtain ⟨hlits_lt, _hnd_tmp, hent_cl⟩ := hcl_bd (by omega)
      faa_steps; c0_call hAlloc; refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
      split
      · faa_steps
        · exact hQ 0xFFFFFFFF#64 s m hlen hw hwb (Or.inl rfl) hm
        · exact absurd rfl (by assumption)
      · intro arena1 m1 alen1 s1_st hlen1 hhold1 hnoshrk1 hnogarb1 _hred1 hsz1 hm1
        faa_steps
        refine wp_loop_group (ts := [i32]) (fun r (iv, ()) mc => ∃ i arena',
          i ≤ len.toNat ∧ r = len.toNat - i ∧ iv = BitVec.ofNat 32 i ∧
          arena'.length = c.arena_cap ∧
          (∀ k < s.core.arena_len + 3, arena'[k]? = arena1[k]?) ∧
          (∀ k < i, arena'[s.core.arena_len + 3 + k]? = s.core.tmp[k]?) ∧
          (FullMem c { s1_st with core := { s1_st.core with arena := arena' } } ⋆ R) mc) ?_ ?_
        · rintro L r ⟨iv, ⟨⟩⟩ mc ih ⟨i, arena', hile, rfl, rfl, harl, hpre, hcp, hmc⟩
          faa_head_steps
          refine wp_head_jnz_iff (b := decide (i < len.toNat)) (by
            simp only [Arg.val_var]
            simpa [bv_ofNat_toNat_eq len] using bv32_ult_eq (a := i) (by omega) len.isLt) ?_
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hilt => ?_, fun hige => ?_⟩
          · have htm_bd_i : i <
                ({ s1_st with core := { s1_st.core with arena := arena' } }).core.tmp.length := by
              simp [s1_st, hco.tmp_len_arr]; omega
            have har_bd : s.core.arena_len + 3 + i < arena'.length := by
              have := hlen1.core_ok.arena_len_le; simp [s1_st, alen1] at this; omega
            have hidx_eq : ((BitVec.ofNat 32 i).setWidth 64) * 4 = BitVec.ofNat 64 (4 * i) := by
              rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]; bv_omega
            have hidx2 : c.pArena + ((BitVec.ofNat 64 s.core.arena_len + (3 : BitVec 64) +
                BitVec.ofNat 64 i) * 4) =
                c.pArena + BitVec.ofNat 64 (4 * (s.core.arena_len + 3 + i)) := by bv_omega
            faa_lets; try rw [hidx_eq]
            refine wp_load_of (FullArenaTactics.load_full_tmp (i := i) htm_bd_i hmc) ?_
            faa_lets; rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), hidx2]
            let lit_i := s.core.tmp[i]'(by rw [hco.tmp_len_arr]; omega)
            obtain ⟨ok_ar, hm_ar⟩ :=
              FullArenaTactics.store_full_arena (i := s.core.arena_len + 3 + i) lit_i
                (by simpa [s1_st] using har_bd) hmc
            refine ⟨ok_ar, ?_⟩; faa_lets
            rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1) by bv_omega]
            exact ih (len.toNat - (i + 1)) (BitVec.ofNat 32 (i + 1), ()) _ (by omega)
              ⟨i + 1, arena'.set (s.core.arena_len + 3 + i) lit_i, by omega, rfl, rfl,
                by simp [harl],
                (fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hpre k hk),
                (fun k hk => by
                  by_cases hki : k = i
                  · subst hki; rw [List.getElem?_set_self har_bd,
                      List.getElem?_eq_getElem (by rw [hco.tmp_len_arr]; omega)]
                  · rw [List.getElem?_set_ne (by omega)]; exact hcp k (by omega)), hm_ar⟩
          · have hieq : i = len.toNat := by omega
            subst hieq
            let s_cp : FullState := { s1_st with core := { s1_st.core with arena := arena' } }
            have hhold_cp : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]? := fun k hk =>
              (hpre k (by omega)).trans (hhold1 k hk)
            have hnoshrk_cp : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
              rw [hpre s.core.arena_len (by omega)]; exact hnoshrk1
            have hnogarb_cp : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
              rw [hpre s.core.arena_len (by omega)]; exact hnogarb1
            have hsz_cp : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len.toNat := by
              rw [hpre (s.core.arena_len + 2) (by omega)]; exact hsz1
            have hrefs_cp :
                fullArenaClauseRefsCore s_cp.core =
                  fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
              fullArenaClauseRefsCore_append hw.arena hge3' rfl hhold_cp hnoshrk_cp hsz_cp
            have hwat_cp : ModeWatchesInv F_cur s_cp.core :=
              hw.watches.with_wstk rfl rfl rfl rfl rfl
                (fun r hr => hrefs_cp ▸ List.mem_append_left _ hr)
            have hlen_cp : s_cp.LengthsOk c :=
              { core_ok := { hlen1.core_ok with arena_len_arr := by simp [s_cp, harl] }
                scratch_ok := hlen1.scratch_ok }
            have hwb_cp : FullWatchBoundsInv s_cp :=
              ⟨hwb.layout.with_wstk rfl rfl rfl rfl, fun h0 l hl =>
                (hwb.slices h0 l hl).with_arena_extend (k := s.core) (k' := s_cp.core)
                  (Nat.le_refl _) rfl (by dsimp [s_cp, s1_st, alen1]; omega) hhold_cp⟩
            have hlits_cp : fullArenaClauseLits s_cp s.core.arena_len =
                (s.core.tmp.take len.toNat).map BitVec.toNat := by
              have hle_len : s.core.arena_len + 3 + len.toNat ≤ arena'.length := by
                have := hlen1.core_ok.arena_len_le; simp [s1_st, alen1] at this; omega
              apply List.ext_getElem
              · simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                  hsz_cp, harl, hco.tmp_len_arr]
                omega
              · intro k hk1 _
                have hk_lt : k < len.toNat := by
                  simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                    hsz_cp] at hk1
                  omega
                have hcpk := hcp k hk_lt
                rw [List.getElem?_eq_getElem (by omega),
                  List.getElem?_eq_getElem (by rw [hco.tmp_len_arr]; omega)] at hcpk
                simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                  hsz_cp, Option.some.inj hcpk]
            have hnew_sz_cp : fullArenaClauseSizeCore s_cp.core s.core.arena_len = len.toNat := by
              unfold fullArenaClauseSizeCore; exact hsz_cp
            have hnew_live_cp : fullArenaLiveLitsLt s_cp.core s.core.arena_len := by
              intro _ j hj; rw [hnew_sz_cp] at hj
              have hcpj := hcp j hj
              change arena'[s.core.arena_len + 3 + j]? = s.core.tmp[j]? at hcpj
              have hj_tmp : j < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
              change (arena'[s.core.arena_len + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars
              rw [hcpj, List.getElem?_eq_getElem hj_tmp, Option.getD_some]
              refine hlits_lt _ (List.mem_map.mpr ⟨s.core.tmp[j]'hj_tmp, ?_, rfl⟩)
              rw [List.mem_iff_getElem]
              exact ⟨j, by simp; omega, by simp [List.getElem_take]⟩
            have hcref32 : (BitVec.ofNat 32 s.core.arena_len).toNat = s.core.arena_len :=
              bv32_ofNat_toNat (by omega)
            have hcref32_ne : BitVec.ofNat 32 s.core.arena_len ≠ 0xFFFFFFFF#32 := fun he => by
              have ht := congrArg BitVec.toNat he
              rw [hcref32] at ht; change s.core.arena_len = 0xFFFFFFFF at ht; omega
            have hcref32_lt : (BitVec.ofNat 32 s.core.arena_len).toNat < 0x80000000 := by
              rw [hcref32]; omega
            have htm_gt0 : 0 < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
            have htm_gt1 : 1 < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
            let t0 := s.core.tmp[0]'htm_gt0
            let t1 := s.core.tmp[1]'htm_gt1
            have ht0_lt : t0.toNat < 2 * s.core.cur_vars := by
              refine hlits_lt t0.toNat (List.mem_map.mpr ⟨t0, ?_, rfl⟩)
              rw [List.mem_iff_getElem]
              exact ⟨0, by simp; omega, by simp [t0, List.getElem_take]⟩
            have ht1_lt : t1.toNat < 2 * s.core.cur_vars := by
              refine hlits_lt t1.toNat (List.mem_map.mpr ⟨t1, ?_, rfl⟩)
              rw [List.mem_iff_getElem]
              exact ⟨1, by simp; omega, by simp [t1, List.getElem_take]⟩
            refine wp_join_group (ts := []) (fun () mf => ∃ wvec' wstk' wlen' wusable' wsort',
              let sf : FullState :=
                { s_cp with
                  core := { s_cp.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                           wusable := wusable' }
                  scratch := { s_cp.scratch with wsort := wsort' } }
              sf.LengthsOk c ∧ ModeWatchesInv F_cur sf.core ∧ FullWatchBoundsInv sf ∧
              (FullMem c sf ⋆ R) mf) ?_ ?_
            · rintro _ ⟨⟩ mf ⟨wvec', wstk', wlen', wusable', wsort', hlen_w, hwat_w, hwb_w, hmf⟩
              let s_w : FullState :=
                { s_cp with
                  core := { s_cp.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                           wusable := wusable' }
                  scratch := { s_cp.scratch with wsort := wsort' } }
              have har_bd0 : s.core.arena_len < s_w.core.arena.length := by
                have := hlen_w.core_ok.arena_len_le; have h2 := hlen_w.core_ok.arena_len_arr
                change s_w.core.arena.length = c.arena_cap at h2; omega
              faa_lets
              have haddr_ar : c.pArena + BitVec.ofNat 64 s.core.arena_len * 4 =
                  c.pArena + BitVec.ofNat 64 (4 * s.core.arena_len) := by
                rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat,
                  bv64_ofNat_toNat (by omega)]
              rw [haddr_ar]
              refine wp_load_of
                (FullArenaTactics.load_full_arena (i := s.core.arena_len) har_bd0 hmf) ?_
              faa_lets
              let hdr_g := arena'[s.core.arena_len]'(by omega) ||| 0x00080000#32
              let arena_g := arena'.set s.core.arena_len hdr_g
              let s_g : FullState := { s_w with core := { s_w.core with arena := arena_g } }
              obtain ⟨ok_g, hm_g⟩ := FullArenaTactics.store_full_arena (i := s.core.arena_len)
                hdr_g (by simpa [s_w] using har_bd0) hmf
              refine ⟨ok_g, ?_⟩; faa_lets
              have hhold_g : ∀ k < s.core.arena_len, arena_g[k]? = s.core.arena[k]? :=
                fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hhold_cp k hk
              have hnoshrk_g :
                  (arena_g[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
                rw [List.getElem?_set_self (by omega), Option.getD_some]
                exact bv32_or_garb_noshrk (by
                  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hnoshrk_cp)
              have hnogarb_g :
                  (arena_g[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32 := by
                rw [List.getElem?_set_self (by omega), Option.getD_some]; exact bv32_or_garb_nz _
              have hsz_g : (arena_g[s.core.arena_len + 2]?.getD 0#32).toNat = len.toNat := by
                rw [List.getElem?_set_ne (by omega)]; exact hsz_cp
              have hlen_g : s_g.LengthsOk c :=
                { core_ok := { hlen_w.core_ok with arena_len_arr := by simp [s_g, arena_g, harl] }
                  scratch_ok := hlen_w.scratch_ok }
              have hrefs_g :
                  fullArenaClauseRefsCore s_g.core =
                    fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                fullArenaClauseRefsCore_append hw.arena hge3' rfl hhold_g hnoshrk_g hsz_g
              have hwat_g : ModeWatchesInv F_cur s_g.core := hwat_w.with_wstk rfl rfl rfl rfl rfl
                (fun r hr => by
                  have h1 : fullArenaClauseRefsCore s_w.core =
                      fullArenaClauseRefsCore s.core ++ [s.core.arena_len] := hrefs_cp
                  rwa [hrefs_g, ← h1])
              obtain ⟨hw_g, _, _⟩ :=
                Full.FullAssignAddSpecs.addGarbageClause_preserves_witness
                  (ag' := s.core.arena_garbage) (oom' := s.core.oom) hlen hw hlen_g hge3'
                  hhold_g hnoshrk_g hnogarb_g hsz_g hwat_g
              have hwb_g : FullWatchBoundsInv s_g :=
                hwb_w.reconstruct_of_witnessInv hw_g
                  (Nat.le_trans hlen_g.core_ok.arena_len_le
                    (Nat.le_of_eq hlen_g.core_ok.arena_len_arr.symm))
                  hdm hdm rfl rfl rfl
              exact hQ 0xFFFFFFFF#64 s_g _ hlen_g hw_g hwb_g (Or.inl rfl) hm_g
            · intro Jw hJw
              faa_steps; rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
              have hnew_fit : s.core.arena_len + 3 + fullArenaClauseSizeCore s_cp.core
                  s.core.arena_len ≤ s_cp.core.arena_len := by
                rw [hnew_sz_cp]; dsimp [s_cp, s1_st, alen1]; omega
              have hnew_ref : s.core.arena_len ∈ fullArenaClauseRefsCore s_cp.core :=
                hrefs_cp ▸ List.mem_append_right _ (by simp)
              refine ⟨c, s_cp, R, rfl, hlen_cp, hwat_cp.layout, (fun hc => absurd hc (by decide)),
                (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hmc, ?_⟩
              intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1 hlay1 hoth1 hok1t hok1f hm1
              have hrefs1 :
                  fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s_cp.core := rfl
              have hwat1 : ModeWatchesInv F_cur s1.core :=
                Full.FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv
                  hwat_cp hlay1 rfl rfl (fun r hr => hrefs1 ▸ hr)
                  (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _,
                    fun hdm' => absurd hdm hdm', hcref32_lt,
                    hrefs1 ▸ by rw [hcref32]; exact hnew_ref⟩)
                  hoth1 hok1t (fun h => (hok1f h).1)
              have hwb1 : FullWatchBoundsInv s1 := fullWatchPush_preserves_watchBoundsInv
                (lit := t0) (w0 := t1 &&& 0x7FFFFFFF#32)
                (w1 := BitVec.ofNat 32 s.core.arena_len) (cnt := 2#32) (wsort' := wsort1)
                hwb_cp hlay1 (fun _ hc => absurd hc (by decide))
                (fun _ _ => ⟨bv32_mask_flag0 _,
                  Nat.lt_of_le_of_lt
                    (Nat.le_trans (bv32_and_7f_toNat_le _) (bv32_and_7f_toNat_le _)) ht1_lt,
                  hcref32_lt,
                  (by rw [hcref32, hnew_sz_cp]; omega), (by rw [hcref32]; exact hnew_fit),
                  (by rw [hcref32]; exact hnew_live_cp)⟩)
                hoth1 (fun ht => let ⟨x1, x2, x3, x4, x5, x6⟩ := hok1t ht
                  ⟨x1, x2, x3, x4, x5, x6⟩) (fun hf => (hok1f hf).1)
              faa_steps
              · rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
                refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun hc => absurd hc (by decide)),
                  (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hm1, ?_⟩
                intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
                have hrefs2 : fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s1.core :=
                  rfl
                have hwat2 : ModeWatchesInv F_cur s2.core :=
                  Full.FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv
                    hwat1 hlay2 rfl rfl (fun r hr => hrefs2 ▸ hr)
                    (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _,
                      fun hdm' => absurd hdm hdm', hcref32_lt,
                      hrefs2 ▸ hrefs1 ▸ by rw [hcref32]; exact hnew_ref⟩)
                    hoth2 hok2t (fun h => (hok2f h).1)
                have hwb2 : FullWatchBoundsInv s2 := fullWatchPush_preserves_watchBoundsInv
                  (lit := t1) (w0 := t0 &&& 0x7FFFFFFF#32)
                  (w1 := BitVec.ofNat 32 s.core.arena_len) (cnt := 2#32) (wsort' := wsort2)
                  hwb1 hlay2 (fun _ hc => absurd hc (by decide))
                  (fun _ _ => ⟨bv32_mask_flag0 _,
                    Nat.lt_of_le_of_lt
                      (Nat.le_trans (bv32_and_7f_toNat_le _) (bv32_and_7f_toNat_le _)) ht0_lt,
                    hcref32_lt,
                    (by
                      rw [hcref32]
                      change 2 ≤ fullArenaClauseSizeCore s_cp.core s.core.arena_len
                      rw [hnew_sz_cp]; omega),
                    (by rw [hcref32]; exact hnew_fit), (by rw [hcref32]; exact hnew_live_cp)⟩)
                  hoth2 (fun ht => by
                    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hok2t ht
                    exact ⟨x1, x2, x3, x4, x5, x6⟩) (fun hf => (hok2f hf).1)
                let addClState (fred' ni' nr' : BitVec 64) : FullState :=
                  { s with
                    core := { s.core with
                      arena := arena', arena_len := s.core.arena_len + 3 + len.toNat,
                      wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := wu2,
                      first_reducible := fred', num_irred := ni', num_redundant := nr' }
                    scratch := { s.scratch with wsort := wsort2 } }
                have hfin : ∀ fred' ni' nr' mf,
                    (FullMem c (addClState fred' ni' nr') ⋆ R) mf →
                    Q (BitVec.ofNat 64 s.core.arena_len, ()) mf :=
                  fun fred' ni' nr' mf hm_f => by
                    let s_fin := addClState fred' ni' nr'
                    have hlen_f : s_fin.LengthsOk c :=
                      { core_ok := { hlen2.core_ok with
                          arena_len_arr := by simp [s_fin, addClState]; exact harl }
                        scratch_ok := hlen2.scratch_ok }
                    have hrefs_f0 :
                        fullArenaClauseRefsCore s_fin.core =
                          fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                      fullArenaClauseRefsCore_append hw.arena hge3' rfl hhold_cp hnoshrk_cp hsz_cp
                    have hwat_f : ModeWatchesInv F_cur s_fin.core :=
                      hwat2.with_wstk rfl rfl rfl rfl rfl
                        (fun r hr => by
                          have h1 : fullArenaClauseRefsCore s2.core =
                              fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                            hrefs2.trans (hrefs1.trans hrefs_cp)
                          rwa [hrefs_f0, ← h1])
                    obtain ⟨hw_f, _, _⟩ :=
                      Full.FullAssignAddSpecs.addEntailedClause_preserves_witness
                        hlen hw hlen_f hge3' hlits_lt hent_cl hhold_cp hnoshrk_cp hsz_cp hlits_cp
                        hwat_f
                    have hwb_f : FullWatchBoundsInv s_fin :=
                      hwb2.with_nonwatch rfl rfl rfl rfl rfl
                        (by dsimp [s_fin, addClState, s2, s1, s_cp, s1_st, alen1]; omega)
                        (fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩)
                    exact hQ (BitVec.ofNat 64 s.core.arena_len) s_fin mf hlen_f hw_f hwb_f
                      (Or.inr (Or.inr rfl)) hm_f
                faa_steps
                · exact hfin (BitVec.ofNat 64 s.core.arena_len) s.core.num_irred
                    (s.core.num_redundant + 1#64) _ (by assumption)
                · exact hfin s.core.first_reducible s.core.num_irred
                    (s.core.num_redundant + 1#64) _ (by assumption)
                · exact hfin s.core.first_reducible (s.core.num_irred + 1#64)
                    s.core.num_redundant _ (by assumption)
                · exact hJw () m2 ⟨wvec2, wstk2, wlen2, wu2, wsort2, hlen2, hwat2, hwb2, hm2⟩
              · exact hJw () m1 ⟨wvec1, wstk1, wlen1, wu1, wsort1, hlen1, hwat1, hwb1, hm1⟩
        · intro L hL; faa_steps; exact hL len.toNat _ m1 ⟨0, arena1, Nat.zero_le _, by simp, rfl,
            hlen1.core_ok.arena_len_arr, fun _ _ => rfl, fun _ h => by omega, hm1⟩

/-! ## 3. No-Bounds BCP Specs, `SplitWatchBoundsInv` & Inner `wp` Building Blocks -/

/-- Spec for `full_prop_lit_nobounds_m7`: extends `Full.fullPropLitSpec` with
`FullWatchBoundsInv s` pre/post so per-watch inner bounds checks are soundly omitted
while preserving `FullSafetySlice` (`LengthsOk` + `FullMem`), `FullWitnessInv`, and
`FullWatchBoundsInv`. -/
@[expose] def fullPropLitNoBoundsSpec : Spec [i64, i32, i64] [.bool] :=
  fun (h, _lit, ignore_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullWatchBoundsInv s ∧
      s.core.dense_mode = 0#64 ∧ s.core.oom = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
        ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
        let s' : FullState :=
          { s with
            core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', trail_end := te',
                                  unassigned := unass', unflushed := unfl', wvec := wvec',
                                  arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                                  confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                  confl_lit1 := c1', oom := oom' }
            scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                        phases := phases' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullWatchBoundsInv s' →
        Full.FullPropDecSpecs.FullTrailExt s.core s'.core →
        Full.FullPropDecSpecs.FullArenaPermEq s.core s'.core →
        (ok = false → oom' ≠ 0#64 ∨
          (Full.FullConflictOkW F_cur s' ∧ (ctype' = 2#64 → cref' ≠ ignore_ref))) →
        (ok = true → oom' = 0#64 ∧ ctype' = s.core.confl_type) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Spec for `full_propagate_ignore_nobounds_m7`. -/
@[expose] def fullPropagateIgnoreNoBoundsSpec : Spec [i64, i64] [i64] :=
  fun (h, ignore_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullWatchBoundsInv s ∧
      s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
        fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
        let s' : FullState :=
          { s with
            core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', trail_end := te',
                                  propagated := prop', unassigned := unass', unflushed := unfl',
                                  wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                  wusable := wu', fuel := fuel', confl_type := ctype',
                                  confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                  oom := oom' }
            scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                        phases := phases' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullWatchBoundsInv s' →
        Full.FullPropDecSpecs.FullTrailExt s.core s'.core →
        Full.FullPropDecSpecs.FullArenaPermEq s.core s'.core →
        fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ Full.FullConflictOkW F_cur s' ∧
          (ctype' = 2#64 → cref' ≠ ignore_ref)) →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Spec for `full_bcp_nobounds_m7`. -/
@[expose] def fullPropagateNoBoundsSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullWatchBoundsInv s ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullWatchBoundsInv s' →
      Full.FullPropDecSpecs.FullTrailExt s.core s'.core →
      Full.FullPropDecSpecs.FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ Full.FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Mid-compaction watch-bounds invariant complementing `Full.SplitWatchesInv`. -/
structure SplitWatchBoundsInv (k : FullCoreState) (not_lit off q p end_v : Nat) : Prop where
  other_slices : ∀ l < 2 * k.cur_vars, l ≠ not_lit →
    WatchSliceBoundsOk k (fullWatchOffCore k l) (fullWatchSizeCore k l)
  kept_slice : WatchSliceBoundsOk k off (q - off)
  rem_slice : WatchSliceBoundsOk k p (end_v - p)

theorem SplitWatchBoundsInv.init {st : FullState} {not_lit : Nat}
    (hwb : FullWatchBoundsInv st) (hdm0 : st.core.dense_mode = 0#64)
    (hnot_lt : not_lit < 2 * st.core.cur_vars) :
    SplitWatchBoundsInv st.core not_lit (fullWatchOffCore st.core not_lit)
      (fullWatchOffCore st.core not_lit) (fullWatchOffCore st.core not_lit)
      (fullWatchOffCore st.core not_lit + fullWatchSizeCore st.core not_lit) :=
  { other_slices := fun l hl _ => hwb.slices hdm0 l hl
    kept_slice := by simp only [Nat.sub_self]; exact .empty
    rem_slice := by
      simpa only [Nat.add_sub_cancel_left] using hwb.slices hdm0 not_lit hnot_lt }

theorem SplitWatchBoundsInv.with_nonwatch {k k' : FullCoreState} {not_lit off q p end_v : Nat}
    (h : SplitWatchBoundsInv k not_lit off q p end_v)
    (hcv : k'.cur_vars = k.cur_vars) (hwv : k'.wvec = k.wvec) (hws : k'.wstk = k.wstk)
    (hal : k'.arena_len = k.arena_len) (har : k'.arena = k.arena) :
    SplitWatchBoundsInv k' not_lit off q p end_v := by
  have har_id : ∀ cref : Nat, cref < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore k cref →
      cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len →
      fullArenaLiveLitsLt k cref →
      2 ≤ fullArenaClauseSizeCore k' cref ∧
      cref + 3 + fullArenaClauseSizeCore k' cref ≤ k'.arena_len ∧
      fullArenaLiveLitsLt k' cref := by
    intro cref _ h1 h2 h3
    simp only [fullArenaClauseSizeCore, fullArenaLiveLitsLt, fullArenaHdrCore,
      har, hal, hcv] at h1 h2 h3 ⊢
    exact ⟨h1, h2, h3⟩
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore; rw [hwv]
  have hwsz : ∀ l, fullWatchSizeCore k' l = fullWatchSizeCore k l := fun l => by
    unfold fullWatchSizeCore; rw [hwv]
  exact
    { other_slices := fun l hl hne => by
        rw [hwo, hwsz]
        exact (h.other_slices l (hcv ▸ hl) hne).mono_wstk (by omega)
          (fun _ _ _ => by rw [hws]) (by omega) har_id
      kept_slice := h.kept_slice.mono_wstk (by omega) (fun _ _ _ => by rw [hws]) (by omega) har_id
      rem_slice := h.rem_slice.mono_wstk (by omega) (fun _ _ _ => by rw [hws]) (by omega) har_id }

theorem SplitWatchBoundsInv.reconstruct_of_arenaInv {c : FullCfg} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {not_lit off q p end_v : Nat}
    (hb : SplitWatchBoundsInv k not_lit off q p end_v)
    (hsw' : Full.SplitWatchesInv F_cur k' not_lit off q p end_v)
    (ha' : FullArenaClausesInv c F_cur k') (har_len' : k'.arena_len ≤ k'.arena.length)
    (hcv : k'.cur_vars = k.cur_vars)
    (hwv : k'.wvec = k.wvec) (hws : k'.wstk = k.wstk) :
    SplitWatchBoundsInv k' not_lit off q p end_v := by
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore; rw [hwv]
  have hwsz : ∀ l, fullWatchSizeCore k' l = fullWatchSizeCore k l := fun l => by
    unfold fullWatchSizeCore; rw [hwv]
  refine
    { other_slices := fun l hl hne => by
        have hsl := hsw'.other_slices l hl hne
        have hbl := hb.other_slices l (hcv ▸ hl) hne
        rw [hwo, hwsz] at hsl ⊢
        exact hbl.reconstruct_of_arenaInv (by omega) (fun _ _ _ => by rw [hws]) ha' har_len' hsl
      kept_slice := hb.kept_slice.reconstruct_of_arenaInv (by omega) (fun _ _ _ => by rw [hws])
        ha' har_len' hsw'.kept_slice
      rem_slice := hb.rem_slice.reconstruct_of_arenaInv (by omega) (fun _ _ _ => by rw [hws])
        ha' har_len' hsw'.rem_slice }

theorem SplitWatchBoundsInv.reconstruct_of_nw_arenaInv {c : FullCfg} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {not_lit off q p end_v : Nat}
    (hb : SplitWatchBoundsInv k not_lit off q p end_v)
    (hsw' : Full.SplitWatchesInv F_cur k' not_lit off q p end_v)
    (ha' : FullArenaClausesInv c F_cur (withEmptyWatchesCore c k'))
    (har_len' : k'.arena_len ≤ k'.arena.length) (hcv : k'.cur_vars = k.cur_vars)
    (hwv : k'.wvec = k.wvec) (hws : k'.wstk = k.wstk) :
    SplitWatchBoundsInv k' not_lit off q p end_v := by
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore; rw [hwv]
  have hwsz : ∀ l, fullWatchSizeCore k' l = fullWatchSizeCore k l := fun l => by
    unfold fullWatchSizeCore; rw [hwv]
  refine
    { other_slices := fun l hl hne => by
        have hsl := hsw'.other_slices l hl hne
        have hbl := hb.other_slices l (hcv ▸ hl) hne
        rw [hwo, hwsz] at hsl ⊢
        exact hbl.reconstruct_of_nw_arenaInv (by omega) (fun _ _ _ => by rw [hws])
          ha' har_len' hsl
      kept_slice := hb.kept_slice.reconstruct_of_nw_arenaInv (by omega)
        (fun _ _ _ => by rw [hws]) ha' har_len' hsw'.kept_slice
      rem_slice := hb.rem_slice.reconstruct_of_nw_arenaInv (by omega)
        (fun _ _ _ => by rw [hws]) ha' har_len' hsw'.rem_slice }

theorem SplitWatchBoundsInv.advance_rem {k : FullCoreState} {not_lit off q p p' end_v : Nat}
    (h : SplitWatchBoundsInv k not_lit off q p end_v)
    (hrem' : WatchSliceBoundsOk k p' (end_v - p')) :
    SplitWatchBoundsInv k not_lit off q p' end_v :=
  { h with rem_slice := hrem' }

theorem SplitWatchBoundsInv.write_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p end_v : Nat} {w0 : BitVec 32}
    (hb : SplitWatchBoundsInv k not_lit off q (p + 1) end_v)
    (hsw : Full.SplitWatchesInv F_cur k not_lit off q (p + 1) end_v)
    (hnot_lt : not_lit < 2 * k.cur_vars) (_hqp : q ≤ p) (hq_lt : q < k.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hblk : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars) :
    SplitWatchBoundsInv { k with wstk := k.wstk.set q w0 } not_lit off (q + 1) (p + 1) end_v := by
  let k' : FullCoreState := { k with wstk := k.wstk.set q w0 }
  have hq_ge : off ≤ q := hsw.q_ge
  have hp_end : p + 1 ≤ end_v := hsw.p_le_end
  have hq_lt_end : q < end_v := by omega
  have hq_le := hsw.q_le_p
  have har_id : ∀ cref : Nat, cref < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore k cref →
      cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len →
      fullArenaLiveLitsLt k cref →
      2 ≤ fullArenaClauseSizeCore k' cref ∧
      cref + 3 + fullArenaClauseSizeCore k' cref ≤ k'.arena_len ∧
      fullArenaLiveLitsLt k' cref := fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩
  refine
    { other_slices := fun l hl hne_l => by
        by_cases hsz0 : fullWatchSizeCore k l = 0
        · change WatchSliceBoundsOk k' (fullWatchOffCore k l) (fullWatchSizeCore k l)
          rw [hsz0]; exact .empty
        · have hdisj := hsw.layout.disjoint l not_lit hl hnot_lt hne_l (by omega)
            (by rw [hsw.sz_eq]; exact hsw.sz_pos)
          rw [hsw.off_eq, hsw.sz_eq] at hdisj
          change WatchSliceBoundsOk k' (fullWatchOffCore k l) (fullWatchSizeCore k l)
          exact (hb.other_slices l hl hne_l).mono_wstk (k' := k') (Nat.le_refl k.cur_vars)
            (fun j hj1 hj2 => by
              dsimp only [k']
              exact List.getElem?_set_ne (by rcases hdisj with hd | hd <;> omega))
            (Nat.le_refl k.arena_len) har_id
      kept_slice := by
        rw [show q + 1 - off = (q - off) + 1 by omega]
        refine ((hb.kept_slice.mono_wstk (k' := k') (Nat.le_refl k.cur_vars)
          (fun j hj1 hj2 => by dsimp only [k']; exact List.getElem?_set_ne (by omega))
          (Nat.le_refl k.arena_len) har_id).append_bin ?_ hflag hne hblk)
        dsimp only [k']; rw [show off + (q - off) = q by omega, List.getElem?_set_self hq_lt]
      rem_slice := hb.rem_slice.mono_wstk (k' := k') (Nat.le_refl k.cur_vars)
        (fun j hj1 _ => by dsimp only [k']; exact List.getElem?_set_ne (by omega))
        (Nat.le_refl k.arena_len) har_id }

theorem SplitWatchBoundsInv.write_large {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p end_v : Nat} {w0 cref : BitVec 32}
    (hb : SplitWatchBoundsInv k not_lit off q (p + 2) end_v)
    (hsw : Full.SplitWatchesInv F_cur k not_lit off q (p + 2) end_v)
    (hnot_lt : not_lit < 2 * k.cur_vars) (_hqp : q ≤ p)
    (hq_lt : q < k.wstk.length) (hq1_lt : q + 1 < k.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hblk : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hlt : cref.toNat < 0x80000000)
    (hsz : 2 ≤ fullArenaClauseSizeCore k cref.toNat)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore k cref.toNat ≤ k.arena_len)
    (hlive : fullArenaLiveLitsLt k cref.toNat) :
    SplitWatchBoundsInv { k with wstk := (k.wstk.set q w0).set (q + 1) cref }
      not_lit off (q + 2) (p + 2) end_v := by
  let k' : FullCoreState := { k with wstk := (k.wstk.set q w0).set (q + 1) cref }
  have hq_ge : off ≤ q := hsw.q_ge
  have hp_end : p + 2 ≤ end_v := hsw.p_le_end
  have hq_lt_end : q < end_v := by omega
  have hq1_lt_end : q + 1 < end_v := by omega
  have hq_le := hsw.q_le_p
  have har_id : ∀ cr : Nat, cr < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore k cr →
      cr + 3 + fullArenaClauseSizeCore k cr ≤ k.arena_len →
      fullArenaLiveLitsLt k cr →
      2 ≤ fullArenaClauseSizeCore k' cr ∧
      cr + 3 + fullArenaClauseSizeCore k' cr ≤ k'.arena_len ∧
      fullArenaLiveLitsLt k' cr := fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩
  refine
    { other_slices := fun l hl hne_l => by
        by_cases hsz0 : fullWatchSizeCore k l = 0
        · change WatchSliceBoundsOk k' (fullWatchOffCore k l) (fullWatchSizeCore k l)
          rw [hsz0]; exact .empty
        · have hdisj := hsw.layout.disjoint l not_lit hl hnot_lt hne_l (by omega)
            (by rw [hsw.sz_eq]; exact hsw.sz_pos)
          rw [hsw.off_eq, hsw.sz_eq] at hdisj
          change WatchSliceBoundsOk k' (fullWatchOffCore k l) (fullWatchSizeCore k l)
          exact (hb.other_slices l hl hne_l).mono_wstk (k' := k') (Nat.le_refl k.cur_vars)
            (fun j hj1 hj2 => by
              dsimp only [k']
              rcases hdisj with hd | hd <;>
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
            (Nat.le_refl k.arena_len) har_id
      kept_slice := by
        rw [show q + 2 - off = (q - off) + 2 by omega]
        refine ((hb.kept_slice.mono_wstk (k' := k') (Nat.le_refl k.cur_vars) (fun j hj1 hj2 => by
          dsimp only [k']
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
          (Nat.le_refl k.arena_len) har_id).append_large ?_ ?_ hflag hblk hlt hsz hfit hlive)
        · dsimp only [k']; rw [show off + (q - off) = q by omega,
            List.getElem?_set_ne (by omega), List.getElem?_set_self hq_lt]
        · dsimp only [k']; rw [show off + (q - off) + 1 = q + 1 by omega,
            List.getElem?_set_self (by simp; exact hq1_lt)]
      rem_slice := hb.rem_slice.mono_wstk (k' := k') (Nat.le_refl k.cur_vars) (fun j hj1 _ => by
        dsimp only [k']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
        (Nat.le_refl k.arena_len) har_id }

theorem SplitWatchBoundsInv.after_push {k k' : FullCoreState}
    {not_lit repl off q p end_v : Nat} {w0 cref : BitVec 32} {pok : Bool}
    (hb : SplitWatchBoundsInv k not_lit off q p end_v)
    (hoff_eq : off = fullWatchOffCore k not_lit)
    (hend_eq : end_v = off + fullWatchSizeCore k not_lit)
    (hq_ge : off ≤ q) (hq_le : q ≤ p) (hp_le : p ≤ end_v)
    (hvars : k'.cur_vars = k.cur_vars) (hal : k'.arena_len = k.arena_len) (har : k'.arena = k.arena)
    (hnot_lt : not_lit < 2 * k.cur_vars) (hrepl_lt : repl < 2 * k.cur_vars) (hne : repl ≠ not_lit)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hblk : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hlt : cref.toNat < 0x80000000)
    (hsz_c : 2 ≤ fullArenaClauseSizeCore k cref.toNat)
    (hfit_c : cref.toNat + 3 + fullArenaClauseSizeCore k cref.toNat ≤ k.arena_len)
    (hlive_c : fullArenaLiveLitsLt k cref.toNat)
    (hpres_other : ∀ l < 2 * k.cur_vars, l ≠ repl →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?)
    (hpok_t : pok = true →
      fullWatchSizeCore k' repl = fullWatchSizeCore k repl + 2 ∧
      (∀ j < fullWatchSizeCore k repl,
        k'.wstk[fullWatchOffCore k' repl + j]? = k.wstk[fullWatchOffCore k repl + j]?) ∧
      k'.wstk[fullWatchOffCore k' repl + fullWatchSizeCore k repl]? = some w0 ∧
      k'.wstk[fullWatchOffCore k' repl + fullWatchSizeCore k repl + 1]? = some cref)
    (hpok_f : pok = false →
      fullWatchSizeCore k' repl = fullWatchSizeCore k repl ∧
      ∀ j < fullWatchSizeCore k repl,
        k'.wstk[fullWatchOffCore k' repl + j]? = k.wstk[fullWatchOffCore k repl + j]?) :
    let off' := fullWatchOffCore k' not_lit
    SplitWatchBoundsInv k' not_lit off' (off' + (q - off)) (off' + (p - off))
      (off' + (end_v - off)) := by
  intro off'
  have har_id : ∀ cr : Nat, cr < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore k cr →
      cr + 3 + fullArenaClauseSizeCore k cr ≤ k.arena_len →
      fullArenaLiveLitsLt k cr →
      2 ≤ fullArenaClauseSizeCore k' cr ∧
      cr + 3 + fullArenaClauseSizeCore k' cr ≤ k'.arena_len ∧
      fullArenaLiveLitsLt k' cr := by
    intro cr _ h1 h2 h3
    simp only [fullArenaClauseSizeCore, fullArenaLiveLitsLt, fullArenaHdrCore,
      har, hal, hvars] at h1 h2 h3 ⊢
    exact ⟨h1, h2, h3⟩
  have hsz_not_eq := (hpres_other not_lit hnot_lt hne.symm).1
  have hget_not := (hpres_other not_lit hnot_lt hne.symm).2
  rw [← hoff_eq] at hget_not
  refine
    { other_slices := fun l hl hln => by
        have hl0 : l < 2 * k.cur_vars := hvars ▸ hl
        by_cases hlr : l = repl
        · subst hlr; cases pok with
          | false =>
            obtain ⟨hsz_r, hget_r⟩ := hpok_f rfl; rw [hsz_r]
            exact (hb.other_slices l hl0 hln).relocate (k' := k') (by omega) hget_r (by omega)
              har_id
          | true =>
            obtain ⟨hsz_r, hget_r, hw0, hcr⟩ := hpok_t rfl; rw [hsz_r]
            have hbase := (hb.other_slices l hl0 hln).relocate (k' := k') (by omega) hget_r
              (by omega) har_id
            obtain ⟨hsz', hfit', hlive'⟩ := har_id cref.toNat hlt hsz_c hfit_c hlive_c
            exact hbase.append_large hw0 hcr hflag (by omega) hlt hsz' hfit' hlive'
        · obtain ⟨hsz_l, hget_l⟩ := hpres_other l hl0 hlr; rw [hsz_l]
          exact (hb.other_slices l hl0 hln).relocate (k' := k') (by omega) hget_l (by omega)
            har_id
      kept_slice := by
        rw [show off' + (q - off) - off' = q - off by omega]
        exact hb.kept_slice.relocate (k' := k') (p' := off') (by omega)
          (fun j hj => hget_not j (by omega)) (by omega) har_id
      rem_slice := by
        rw [show off' + (end_v - off) - (off' + (p - off)) = end_v - p by omega]
        refine hb.rem_slice.relocate (k' := k') (p' := off' + (p - off)) (by omega)
          (fun j hj => ?_) (by omega) har_id
        have hj' := hget_not ((p - off) + j) (by omega)
        have h1 : off' + ((p - off) + j) = off' + (p - off) + j := by omega
        have h2 : off + ((p - off) + j) = p + j := by omega
        rw [h1, h2] at hj'
        exact hj' }

theorem SplitWatchBoundsInv.finish {c : FullCfg} {F_cur : List (List Nat)} {k0 : FullCoreState}
    {not_lit off q0 p0 end_v : Nat} {wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (sc' : FullScratch)
    (hb : SplitWatchBoundsInv k0 not_lit off q0 p0 end_v)
    (hsw : Full.SplitWatchesInv F_cur k0 not_lit off q0 p0 end_v)
    (hnot_lt : not_lit < 2 * k0.cur_vars) (hcv : k0.cur_vars ≤ c.max_vars)
    (hwv_len : k0.wvec.length = 4 * c.max_vars) (hwlen_le : k0.wlen ≤ c.wcap)
    (hkeep_pre : ∀ j, off ≤ j → j < q0 → wstk'[j]? = k0.wstk[j]?)
    (hkeep_suf : ∀ j < end_v - p0, wstk'[q0 + j]? = k0.wstk[p0 + j]?)
    (hkeep_out : ∀ j, (j < off ∨ end_v ≤ j) → wstk'[j]? = k0.wstk[j]?) :
    let q_fin := q0 + (end_v - p0)
    let st' : FullState :=
      { core := { k0 with
          wstk := wstk'
          wvec := k0.wvec.set (2 * not_lit + 1) (BitVec.ofNat 32 (q_fin - off))
          wusable := wu' }
        scratch := sc' }
    FullWatchBoundsInv st' := by
  intro q_fin st'
  have hwat_fin := hsw.finish (wu' := wu') hnot_lt hcv hwv_len hwlen_le hkeep_pre hkeep_suf
    hkeep_out
  let k' := st'.core
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k0 l := fun l => by
    unfold fullWatchOffCore; dsimp only [k', st']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_ne : ∀ l, l ≠ not_lit → fullWatchSizeCore k' l = fullWatchSizeCore k0 l :=
    fun l hne => by
    unfold fullWatchSizeCore; dsimp only [k', st']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_not : fullWatchSizeCore k' not_lit = q_fin - off := by
    have hwcap := c.hwcap; unfold dimacsBound at hwcap
    have hnot_bd := hsw.layout.bounds not_lit hnot_lt
    rw [hsw.off_eq, hsw.sz_eq] at hnot_bd
    have hq_le := hsw.q_le_p; have hp_le := hsw.p_le_end
    have hsz_lt32 : q_fin - off < 2 ^ 32 := by omega
    unfold fullWatchSizeCore; dsimp only [k', st']
    rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hsz_lt32]
  have har_id : ∀ cr : Nat, cr < 0x80000000 →
      2 ≤ fullArenaClauseSizeCore k0 cr →
      cr + 3 + fullArenaClauseSizeCore k0 cr ≤ k0.arena_len →
      fullArenaLiveLitsLt k0 cr →
      2 ≤ fullArenaClauseSizeCore k' cr ∧
      cr + 3 + fullArenaClauseSizeCore k' cr ≤ k'.arena_len ∧
      fullArenaLiveLitsLt k' cr := fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩
  refine ⟨hwat_fin.layout, fun _ l hl => ?_⟩
  by_cases hln : l = not_lit
  · subst hln; rw [hwo, hsw.off_eq, hwsz_not]
    have hpre : WatchSliceBoundsOk k' off (q0 - off) :=
      hb.kept_slice.mono_wstk (k' := k') (Nat.le_refl k0.cur_vars)
        (fun j hj1 hj2 => hkeep_pre j hj1 (by have := hsw.q_ge; omega))
        (Nat.le_refl k0.arena_len) har_id
    have hsuf : WatchSliceBoundsOk k' q0 (end_v - p0) :=
      hb.rem_slice.relocate (k' := k') (p' := q0) (Nat.le_refl k0.cur_vars)
        hkeep_suf (Nat.le_refl k0.arena_len) har_id
    rw [show q_fin - off = (q0 - off) + (end_v - p0) by
      dsimp only [q_fin]; have := hsw.q_ge; omega]
    exact hpre.append ((show off + (q0 - off) = q0 by have := hsw.q_ge; omega).symm ▸ hsuf)
  · rw [hwo, hwsz_ne l hln]
    by_cases hsz0 : fullWatchSizeCore k0 l = 0
    · rw [hsz0]; exact .empty
    · have hdisj := hsw.layout.disjoint l not_lit hl hnot_lt hln (by omega)
        (by rw [hsw.sz_eq]; exact hsw.sz_pos)
      rw [hsw.off_eq, hsw.sz_eq] at hdisj
      exact (hb.other_slices l hl hln).mono_wstk (k' := k') (Nat.le_refl k0.cur_vars)
        (fun j hj1 hj2 => hkeep_out j (by omega)) (Nat.le_refl k0.arena_len) har_id

/-- Bundled loop-body invariant combining `PropLitInv` and `SplitWatchBoundsInv`. -/
structure PropLitNoBoundsInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s st : FullState) (not_lit off q p end_v : Nat) : Prop where
  prop : Full.PropLitInv c F0 F_cur s st not_lit off q p end_v
  sb : SplitWatchBoundsInv st.core not_lit off q p end_v

/-- `full_prop_lit_nobounds_m7` unit assignment (`noBoundsAssignExpr`, without `tend < max_v`
inner check). -/
@[expose] def noBoundsAssignExpr (other alvl rsn : Val i32) (rec_ph : Val .bool)
    (tend_v unass_v unfl_v vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p : Val i64)
    (k_next : Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .let_ (Op.mk (.lshr i32) (.var other, (.imm (1 : BitVec 32), ()))) fun ov_v =>
  .let_ (Op.mk (.zext 32 64) (.var other, ())) fun o64 =>
  .let_ (Op.mk (.add i64) (.var vals_p, (.var o64.1, ()))) fun p_v0 =>
  .let_ (Op.mk (.trunc 32 8) (.imm (1 : BitVec 32), ())) fun b1 =>
  .store (.var b1.1) (.var p_v0.1) (
    .let_ (Op.mk (.xor i32) (.var other, (.imm (1 : BitVec 32), ()))) fun no32 =>
    .let_ (Op.mk (.zext 32 64) (.var no32.1, ())) fun no64 =>
    .let_ (Op.mk (.add i64) (.var vals_p, (.var no64.1, ()))) fun p_v1 =>
    .let_ (Op.mk (.neg i32) (.imm (1 : BitVec 32), ())) fun m1 =>
    .let_ (Op.mk (.trunc 32 8) (.var m1.1, ())) fun bm1 =>
    .store (.var bm1.1) (.var p_v1.1) (
      .group (sig := [[i64]])
        (fun L3 => .cons (fun un_n =>
          .group (sig := [[]])
            (fun L4 => .cons (fun _ =>
              .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun v0 =>
              .let_ (Op.mk (.mul i64) (.var v0.1, (.imm (4 : BitVec 64), ()))) fun v1 =>
              .let_ (Op.mk (.add i64) (.var lvl_p, (.var v1.1, ()))) fun p_lv =>
              .store (.var alvl) (.var p_lv.1) (
                .group (sig := [[i64]])
                  (fun L5 => .cons (fun uf_n =>
                    .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
                    .let_ (Op.mk (.mul i64) (.var z0.1, (.imm (4 : BitVec 64), ()))) fun z1 =>
                    .let_ (Op.mk (.add i64) (.var tpos_p, (.var z1.1, ()))) fun ptp =>
                    .let_ (Op.mk (.trunc 64 32) (.var tend_v, ())) fun te32 =>
                    .store (.var te32.1) (.var ptp.1) (
                      .let_ (Op.mk (.mul i64) (.var tend_v, (.imm (4 : BitVec 64), ()))) fun t0 =>
                      .let_ (Op.mk (.add i64) (.var trl_p, (.var t0.1, ()))) fun ptrl =>
                      .store (.var other) (.var ptrl.1) (
                        .let_ (Op.mk (.add i64) (.var tend_v, (.imm (1 : BitVec 64), ())))
                          fun te1 =>
                        k_next te1.1 un_n.1 uf_n.1
                      )
                    )
                  ) .nil)
                  (fun L5 =>
                    .let_ (Op.mk (.cmp .eq i32) (.var alvl, (.imm (0 : BitVec 32), ()))) fun c1 =>
                    .jnz (.var c1.1) (
                      .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
                      .let_ (Op.mk (.mul i64) (.var z0.1, (.imm (4 : BitVec 64), ()))) fun z1 =>
                      .let_ (Op.mk (.add i64) (.var rsns_p, (.var z1.1, ()))) fun prs =>
                      .store (t := i32) (.imm (4294967295 : BitVec 32)) (.var prs.1) (
                        .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun y0 =>
                        .let_ (Op.mk (.mul i64) (.var y0.1, (.imm (4 : BitVec 64), ()))) fun y1 =>
                        .let_ (Op.mk (.add i64) (.var fl_p, (.var y1.1, ()))) fun pf0 =>
                        .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun y2 =>
                        .let_ (Op.mk (.mul i64) (.var y2.1, (.imm (4 : BitVec 64), ()))) fun y3 =>
                        .let_ (Op.mk (.add i64) (.var fl_p, (.var y3.1, ()))) fun pf1 =>
                        .load i32 (.var pf1.1) fun fl_v =>
                        .let_ (Op.mk (.not i32) (.imm (1 : BitVec 32), ())) fun nf =>
                        .let_ (Op.mk (.and i32) (.var fl_v, (.var nf.1, ()))) fun fl2 =>
                        .store (.var fl2.1) (.var pf0.1) (
                          .let_ (Op.mk (.add i64) (.var unfl_v, (.imm (1 : BitVec 64), ())))
                            fun uf1 =>
                          .jump L5.1 (.var uf1.1, ())
                        )
                      )
                    ) (
                      .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
                      .let_ (Op.mk (.mul i64) (.var z0.1, (.imm (4 : BitVec 64), ()))) fun z1 =>
                      .let_ (Op.mk (.add i64) (.var rsns_p, (.var z1.1, ()))) fun prs =>
                      .store (.var rsn) (.var prs.1) (.jump L5.1 (.var unfl_v, ()))
                    )
                  )
              )
            ) .nil)
            (fun L4 =>
              .jnz (.var rec_ph) (
                .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
                .let_ (Op.mk (.add i64) (.var ph_p, (.var z0.1, ()))) fun pph =>
                .group (sig := [[i32]])
                  (fun L6 => .cons (fun pv32 =>
                    .let_ (Op.mk (.trunc 32 8) (.var pv32.1, ())) fun pv8 =>
                    .store (.var pv8.1) (.var pph.1) (.jump L4.1 ())
                  ) .nil)
                  (fun L6 =>
                    .let_ (Op.mk (.and i32) (.var other, (.imm (1 : BitVec 32), ()))) fun lsb =>
                    .let_ (Op.mk (.cmp .ne i32) (.var lsb.1, (.imm (0 : BitVec 32), ()))) fun c2 =>
                    .jnz (.var c2.1) (
                      .let_ (Op.mk (.neg i32) (.imm (1 : BitVec 32), ())) fun n1 =>
                      .let_ (Op.mk (.trunc 32 8) (.var n1.1, ())) fun n8 =>
                      .let_ (Op.mk (.sext 8 32) (.var n8.1, ())) fun n32 =>
                      .jump L6.1 (.var n32.1, ())
                    ) (
                      .let_ (Op.mk (.trunc 32 8) (.imm (1 : BitVec 32), ())) fun p8 =>
                      .let_ (Op.mk (.sext 8 32) (.var p8.1, ())) fun p32 =>
                      .jump L6.1 (.var p32.1, ())
                    )
                  )
              ) (.jump L4.1 ())
            )
        ) .nil)
        (fun L3 =>
          .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
          .let_ (Op.mk (.mul i64) (.var z0.1, (.imm (4 : BitVec 64), ()))) fun z1 =>
          .let_ (Op.mk (.add i64) (.var fl_p, (.var z1.1, ()))) fun pfl =>
          .load i32 (.var pfl.1) fun flv =>
          .let_ (Op.mk (.and i32) (.var flv, (.imm (1 : BitVec 32), ()))) fun fa =>
          .let_ (Op.mk (.cmp .ne i32) (.var fa.1, (.imm (0 : BitVec 32), ()))) fun ca =>
          .jnz (.var ca.1) (
            .let_ (Op.mk (.cmp .ugt i64) (.var unass_v, (.imm (0 : BitVec 64), ()))) fun cu =>
            .jnz (.var cu.1) (
              .let_ (Op.mk (.sub i64) (.var unass_v, (.imm (1 : BitVec 64), ()))) fun un1 =>
              .jump L3.1 (.var un1.1, ())
            ) (.jump L3.1 (.var unass_v, ()))
          ) (.jump L3.1 (.var unass_v, ()))
        )
    )
  )

theorem noBoundsAssign_wp {Γ : Env} {c : FullCfg} {s st1 : FullState}
    {other alvl rsn : BitVec 32} {rec_ph : Bool}
    {tend_v unass_v unfl_v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    {k_next : Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hlen1_mem : (fastPropMem s st1).LengthsOk c)
    (hcv1 : st1.core.cur_vars = s.core.cur_vars)
    (hother_lt : other.toNat < 2 * st1.core.cur_vars)
    (hte_lt : st1.core.trail_end < st1.core.cur_vars)
    (htend_eq : tend_v.toNat = st1.core.trail_end)
    (hm : (FullMem c (fastPropMem s st1) ⋆ R) m)
    (hcont : ∀ (flags' : List (BitVec 32)) (ph' : List (BitVec 8))
        (unass_n unfl_n : BitVec 64) (m' : Mem 64),
      flags'.length = c.max_vars → ph'.length = c.max_vars →
      (FullMem c { fastPropMem s st1 with
        core := { (fastPropMem s st1).core with
          vals := (st1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
          flags := flags', lvl := st1.core.lvl.set (other.toNat / 2) alvl
          rsns := st1.core.rsns.set (other.toNat / 2)
            (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn)
          trl := st1.core.trl.set st1.core.trail_end other
          trail_pos := st1.core.trail_pos.set (other.toNat / 2)
            (BitVec.ofNat 32 st1.core.trail_end) }
        scratch := { (fastPropMem s st1).scratch with phases := ph' } } ⋆ R) m' →
      wp Γ Q X (k_next (tend_v + 1#64) unass_n unfl_n) m') :
    wp Γ Q X (noBoundsAssignExpr other alvl rsn rec_ph tend_v unass_v unfl_v
      c.pVals c.pFlags c.pLevel c.pReason c.pTrailPos c.pTrail c.pPhases k_next) m := by
  have hm_vals := hlen1_mem.core_ok.vals_len
  have hm_fl := hlen1_mem.core_ok.flags_len
  have hm_ph := hlen1_mem.scratch_ok.phases_len
  have hm_lvl := hlen1_mem.core_ok.lvl_len
  have hm_rsn := hlen1_mem.core_ok.rsns_len
  have hm_tp := hlen1_mem.core_ok.trail_pos_len
  have hm_trl := hlen1_mem.core_ok.trl_len
  unfold dimacsBound at hmaxv
  have hte_mv : st1.core.trail_end < c.max_vars := Nat.lt_of_lt_of_le hte_lt (hcv1 ▸ hcv0)
  have hother1_lt : other.toNat ^^^ 1 < 2 * c.max_vars := by
    have h2cv : 2 * st1.core.cur_vars ≤ 2 * c.max_vars :=
      Nat.mul_le_mul_left 2 (hcv1 ▸ hcv0)
    rw [fc_nat_xor_one]
    by_cases hev : other.toNat % 2 = 0 <;> simp [hev] <;> omega
  unfold noBoundsAssignExpr
  nb_head_steps
  refine wp_join_group (fun (_unass_n, ()) mu => mu = m) ?_ ?_
  · rintro _ ⟨unass_n, ⟨⟩⟩ mu hmu
    subst mu
    nb_head_steps
    refine wp_join_group (fun () mph => ∃ ph' : List (BitVec 8),
      ph'.length = c.max_vars ∧
      (FullMem c { fastPropMem s st1 with
          core := { (fastPropMem s st1).core with
            vals := (st1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8 }
          scratch := { (fastPropMem s st1).scratch with phases := ph' } } ⋆ R) mph) ?_ ?_
    · rintro _ ⟨⟩ mph ⟨ph', hph', hmph⟩
      nb_head_steps
      let rsn_v := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
      refine wp_join_group (fun (unfl_n, ()) m_as =>
        ∃ flags' : List (BitVec 32), flags'.length = c.max_vars ∧
        (FullMem c { fastPropMem s st1 with
            core := { (fastPropMem s st1).core with
              vals := (st1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
              flags := flags', lvl := st1.core.lvl.set (other.toNat / 2) alvl
              rsns := st1.core.rsns.set (other.toNat / 2) rsn_v }
            scratch := { (fastPropMem s st1).scratch with phases := ph' } } ⋆ R) m_as) ?_ ?_
      · rintro _ ⟨unfl_n, ⟨⟩⟩ m_as ⟨flags', hfl', hm_as⟩
        nb_head_steps
        have htpos_eq : tend_v.setWidth 32 = BitVec.ofNat 32 st1.core.trail_end :=
          BitVec.eq_of_toNat_eq (by
            have hte32 : st1.core.trail_end < 2 ^ 32 :=
              Nat.lt_trans hte_mv (Nat.lt_trans hmaxv (by decide))
            rw [BitVec.toNat_setWidth, htend_eq, Nat.mod_eq_of_lt hte32,
              bv32_ofNat_toNat hte32])
        refine hcont flags' ph' unass_n unfl_n m hfl' hph' ?_
        simpa only [fastPropMem_trail_pos, fastPropMem_trl, htend_eq, htpos_eq,
          bv_c0_zext32_64, bv32_lshr_1] using hm
      · intro Junfl hJunfl; nb_head_steps
        · refine hJunfl (unfl_v + 1#64, ()) m
            ⟨(fastPropMem s st1).core.flags.set (other.toNat / 2)
              ((fastPropMem s st1).core.flags[(other.toNat / 2)]'(by
                rw [hm_fl]; exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hother_lt
                  (Nat.mul_le_mul_left 2 (hcv1 ▸ hcv0)))) &&& ~~~1#32),
              ?_, ?_⟩
          · rw [List.length_set, hm_fl]
          · have hc0 : alvl = 0#32 := hc
            simpa only [rsn_v, hc0, ↓reduceIte, bv_c0_zext32_64, bv32_lshr_1,
              ← BitVec.ofNat_eq_ofNat, fastPropMem_vals, fastPropMem_flags, fastPropMem_lvl,
              fastPropMem_rsns] using hm
        · have hne0 : alvl ≠ 0#32 := hc
          refine hJunfl (unfl_v, ()) m ⟨(fastPropMem s st1).core.flags, hm_fl, ?_⟩
          simpa only [rsn_v, hne0, ↓reduceIte, bv_c0_zext32_64, bv32_lshr_1,
            fastPropMem_vals, fastPropMem_flags, fastPropMem_lvl, fastPropMem_rsns] using hm
    · intro Jph hJph
      have hm1_8 : BitVec.setWidth 8 (-1 : BitVec 32) = 0xFF#8 := by decide
      nb_head_split
      · nb_head_steps
        refine wp_join_group (fun (_pv32, ()) mpv => mpv = m) ?_ ?_
        · rintro _ ⟨pv32, ⟨⟩⟩ mpv hmpv
          subst mpv
          nb_head_steps
          exact hJph () m
            ⟨(fastPropMem s st1).scratch.phases.set (other.toNat / 2)
                (BitVec.setWidth 8 pv32),
              by rw [List.length_set, hm_ph],
              by simpa only [fastPropMem_phases, fastPropMem_vals, bv_c0_zext32_64,
                bv32_lshr_1, bv32_xor_1, hm1_8] using hm⟩
        · intro J6 hJ6; nb_head_steps
          · exact hJ6 _ m rfl
          · exact hJ6 _ m rfl
      · nb_head_steps
        exact hJph () m ⟨(fastPropMem s st1).scratch.phases, hm_ph, by
          simpa only [fastPropMem_vals, bv_c0_zext32_64, bv32_xor_1, hm1_8] using hm⟩
  · intro Jun hJun; nb_head_steps
    · simpa only [fastPropMem_flags] using hJun _ _ rfl
    · simpa only [fastPropMem_flags] using hJun _ _ rfl
    · simpa only [fastPropMem_flags] using hJun _ _ rfl

/-- `full_prop_lit_nobounds_m7` assignment-level loop + `noBoundsAssignExpr` (no `tend < max_v`
check). -/
@[expose] def noBoundsAlvlAssignExpr (nl_lvl cur_lvl csz other cref : Val i32)
    (rec_ph : Val .bool) (cbase ar_p tend_v unass_v unfl_v vals_p fl_p lvl_p rsns_p
      tpos_p trl_p ph_p : Val i64)
    (k_next : Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i32]])
    (fun L17 => .cons (fun alvl_v =>
      noBoundsAssignExpr other alvl_v.1 cref rec_ph tend_v unass_v unfl_v vals_p fl_p lvl_p
        rsns_p tpos_p trl_p ph_p k_next) .nil)
    (fun L17 =>
      .let_ (Op.mk (.cmp .ult i32) (.var nl_lvl, (.var cur_lvl, ()))) fun clt =>
      .jnz (.var clt.1) (
        .group (sig := [[i32, i32]])
          (fun L23 => .cons (fun p =>
            .let_ (Op.mk (.cmp .ult i32) (.var p.2.1, (.var csz, ()))) fun cli =>
            .jnz (.var cli.1) (
              .let_ (Op.mk (.zext 32 64) (.var p.2.1, ())) fun li64 =>
              .let_ (Op.mk (.add i64) (.var cbase, (.var li64.1, ()))) fun idx0 =>
              .let_ (Op.mk (.mul i64) (.var idx0.1, (.imm (4 : BitVec 64), ()))) fun off4 =>
              .let_ (Op.mk (.add i64) (.var ar_p, (.var off4.1, ()))) fun par =>
              .load i32 (.var par.1) fun clit =>
              .group (sig := [[i32]])
                (fun L24 => .cons (fun mx_n =>
                  .let_ (Op.mk (.add i32) (.var p.2.1, (.imm (1 : BitVec 32), ()))) fun li1 =>
                  .jump L23.1 (.var mx_n.1, (.var li1.1, ()))
                ) .nil)
                (fun L24 =>
                  .let_ (Op.mk (.cmp .ne i32) (.var clit, (.var other, ()))) fun cne =>
                  .jnz (.var cne.1) (
                    .let_ (Op.mk (.lshr i32) (.var clit, (.imm (1 : BitVec 32), ()))) fun cv =>
                    .let_ (Op.mk (.zext 32 64) (.var cv.1, ())) fun cv64 =>
                    .let_ (Op.mk (.mul i64) (.var cv64.1, (.imm (4 : BitVec 64), ()))) fun cv4 =>
                    .let_ (Op.mk (.add i64) (.var lvl_p, (.var cv4.1, ()))) fun plv =>
                    .load i32 (.var plv.1) fun clv =>
                    .group (sig := [[i32]])
                      (fun L25 => .cons (fun mx2 => .jump L24.1 (.var mx2.1, ())) .nil)
                      (fun L25 =>
                        .let_ (Op.mk (.cmp .ugt i32) (.var clv, (.var p.1, ()))) fun cgt =>
                        .jnz (.var cgt.1) (.jump L25.1 (.var clv, ())) (.jump L25.1 (.var p.1, ()))
                      )
                  ) (.jump L24.1 (.var p.1, ()))
                )
            ) (.jump L17.1 (.var p.1, ()))
          ) .nil)
          (fun L23 => .jump L23.1 (.imm (0 : BitVec 32), (.imm (0 : BitVec 32), ())))
      ) (.jump L17.1 (.var nl_lvl, ()))
    )

theorem noBoundsAlvlAssign_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem2 : FullState}
    {not_lit other cref nl_lvl0 cur_lvl csz32 : BitVec 32} {rec_ph : Bool}
    {off_v p_v q_v end_v tend_v unass_v unfl_v : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_next : Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    (_hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hpi2 : Full.PropLitInv c F0 F_cur s sem2 not_lit.toNat off_v.toNat (q_v + 2#64).toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen2_mem : (fastPropMem s sem2).LengthsOk c)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem2.core)
    (hng : fullArenaClauseGarbCore sem2.core cref.toNat = false)
    (hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤ sem2.core.arena_len)
    (hother_lt : other.toNat < 2 * sem2.core.cur_vars)
    (hov_un : sem2.core.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_st : not_lit.toNat < 2 * sem2.core.cur_vars)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem2.core cref.toNat)
    (hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem2.core cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore sem2.core cref.toNat,
      l = other.toNat ∨ sem2.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hnl_eq : sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hcur_eq : cur_lvl = BitVec.ofNat 32 sem2.core.cur_level)
    (hcl32 : sem2.core.cur_level < 2 ^ 32)
    (hcsz32 : csz32.toNat = fullArenaClauseSizeCore sem2.core cref.toNat)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (htend_eq : tend_v.toNat = sem2.core.trail_end)
    (hoom_eq : sem2.core.oom = 0#64) (hct_eq : sem2.core.confl_type = s.core.confl_type)
    (hm : (FullMem c (fastPropMem s sem2) ⋆ R) m)
    (hpost : ∀ (sem3 : FullState) (tend_n unass_n unfl_n : BitVec 64) (m' : Mem 64),
      Full.PropLitInv c F0 F_cur s sem3 not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      sem3.core.cur_vars = sem2.core.cur_vars → sem3.core.wvec = sem2.core.wvec →
      sem3.core.wstk = sem2.core.wstk → sem3.core.arena_len = sem2.core.arena_len →
      sem3.core.arena = sem2.core.arena →
      tend_n.toNat = sem3.core.trail_end → unass_n = sem3.core.unassigned →
      unfl_n = sem3.core.unflushed →
      sem3.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      sem3.core.oom = 0#64 → sem3.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s sem3) ⋆ R) m' →
      wp Γ Q X (k_next tend_n unass_n unfl_n) m') :
    wp Γ Q X (noBoundsAlvlAssignExpr nl_lvl0 cur_lvl csz32 other cref rec_ph
      (cref.setWidth 64 + 3#64) c.pArena tend_v unass_v unfl_v
      c.pVals c.pFlags c.pLevel c.pReason c.pTrailPos c.pTrail c.pPhases k_next) m := by
  subst hcur_eq
  unfold dimacsBound at _hmaxv har
  have haren2 := hpi2.len.core_ok.arena_len_arr
  have halen2_le := hpi2.len.core_ok.arena_len_le
  have hm2_aren := hlen2_mem.core_ok.arena_len_arr
  have hm2_lvl := hlen2_mem.core_ok.lvl_len
  have hwstk2 := hpi2.len.core_ok.wstk_len_arr
  have hte_lt : sem2.core.trail_end < sem2.core.cur_vars :=
    hpi2.nw.trail_end_lt_of_unassigned hother_lt hov_un
  have hmv64 : c.max_vars + 1 < 2 ^ 64 :=
    Nat.lt_trans (Nat.add_lt_add_right _hmaxv 1) (by decide)
  have hte_mv : sem2.core.trail_end < c.max_vars :=
    Nat.lt_of_lt_of_le hte_lt (hpi2.cur_vars_eq ▸ hcv0)
  have htend1 : (tend_v + 1#64).toNat = sem2.core.trail_end + 1 := by
    rw [BitVec.toNat_add, htend_eq]
    change (sem2.core.trail_end + 1) % 2 ^ 64 = sem2.core.trail_end + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hbd2 : cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤
      sem2.core.arena.length := haren2 ▸ Nat.le_trans hcr_fit halen2_le
  have hkr_lt : ∀ {k}, k < fullArenaClauseSizeCore sem2.core cref.toNat →
      cref.toNat + 3 + k < sem2.core.arena.length := fun hk =>
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk (cref.toNat + 3)) hbd2
  have hl_var : ∀ k (hk : k < fullArenaClauseSizeCore sem2.core cref.toNat),
      (sem2.core.arena[cref.toNat + 3 + k]'(hkr_lt hk)).toNat / 2 < c.max_vars := fun k hk =>
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le
      (hpi2.nw.arena.lits_lt _ hcr_ref hng _ ((mem_fullArenaClauseLitsCore_iff hbd2).mpr
        ⟨k, hk, rfl⟩)) (Nat.mul_le_mul_left 2 (hpi2.cur_vars_eq ▸ hcv0)))
  unfold noBoundsAlvlAssignExpr
  refine wp_join_group (fun (alvl_v, ()) ma => ma = m ∧
      (∀ l ∈ fullArenaClauseLitsCore sem2.core cref.toNat, l ≠ other.toNat →
        (sem2.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvl_v.toNat) ∧
      (alvl_v = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore sem2.core cref.toNat,
        l ≠ other.toNat ∧ alvl_v = sem2.core.lvl[l / 2]?.getD 0#32)) ?_ ?_
  · rintro _ ⟨alvl_v, ⟨⟩⟩ _ ⟨rfl, hmax_ge, hmax_att⟩
    refine noBoundsAssign_wp _hmaxv hcv0 hlen2_mem hpi2.cur_vars_eq hother_lt hte_lt htend_eq hm ?_
    intro flags' ph' unass_n unfl_n m' hfl' hph' hm'
    dsimp only at hm'
    rw [fastPropMem_assign_eq (te' := sem2.core.trail_end + 1)
      (un' := unass_n) (uf' := unfl_n)] at hm'
    have hassign := Full.full_large_assign_nw_step hpi2.len.core_ok hpi2.nw hcr_lt hcr_ref hng
      hother_lt hov_un hnot_st hpi2.not_f hother_mem hunit hmax_ge hmax_att (flags' := flags')
      (unas' := unass_n) (unfl' := unfl_n)
    have ⟨hlen3, hnw3, hsw3, hag3, htr3, hperm3, hsc3, hnot_f3, hnl3⟩ :=
      fastPropMem_eq_of_eq hpi2 hpi2.sw hwstk2 hfl' hph' hnot_st hother_lt hov_un hnl_eq hassign
    exact hpost _ (tend_v + 1#64) unass_n unfl_n m'
      ⟨hlen3, hnw3, hsw3, hag3, htr3, hperm3, hsc3, hnot_f3⟩
      rfl rfl rfl rfl rfl htend1 rfl rfl hnl3 hoom_eq hct_eq (by
        have hws_id : { sem2.core with wstk := sem2.core.wstk } = sem2.core := by
          cases sem2.core; rfl
        simpa only [hws_id] using hm')
  · intro Jalvl hJalvl; nb_head_split
    · nb_head_steps
      refine wp_loop_inv (ts := [i32, i32])
        (fun (mx_c, li_c, ()) m_li =>
          li_c.toNat ≤ fullArenaClauseSizeCore sem2.core cref.toNat ∧ m_li = m ∧
          (∀ k < li_c.toNat,
            (sem2.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat ≠ other.toNat →
            (sem2.core.lvl[(sem2.core.arena[cref.toNat + 3 + k]?.getD
              0#32).toNat / 2]?.getD 0#32).toNat ≤ mx_c.toNat) ∧
          (mx_c = 0#32 ∨ ∃ k < li_c.toNat,
            (sem2.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat ≠ other.toNat ∧
            mx_c = sem2.core.lvl[(sem2.core.arena[cref.toNat + 3 + k]?.getD
              0#32).toNat / 2]?.getD 0#32))
        (fun (_, li_c, ()) _ => fullArenaClauseSizeCore sem2.core cref.toNat - li_c.toNat)
        (fun L hL => by
          nb_head_steps
          exact hL _ m ⟨Nat.zero_le _, rfl, fun _ hk => by simp at hk, Or.inl rfl⟩)
        (fun L (mx_c, li_c, ()) m_li ⟨hli_le, hm_eq, hge, hatt⟩ ihi => by
          subst m_li
          nb_head_split
          · have hi_lt : li_c.toNat < fullArenaClauseSizeCore sem2.core cref.toNat :=
              hcsz32 ▸ hc
            have hidx_li : (cref.setWidth 64 + 3#64 + li_c.setWidth 64).toNat =
                cref.toNat + 3 + li_c.toNat := by
              rw [bv64_add_toNat (by
                rw [h3_idx, bv_c0_zext32_64]
                exact Nat.lt_of_lt_of_le (hkr_lt hi_lt)
                  (Nat.le_trans (Nat.le_of_eq haren2) (Nat.le_of_lt (Nat.lt_trans har
                    (by decide))))),
                h3_idx, bv_c0_zext32_64]
            have hli1 : (li_c + (1 : BitVec 32)).toNat = li_c.toNat + 1 := by
              rw [BitVec.toNat_add]
              exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hi_lt)
                (hcsz32 ▸ csz32.isLt))
            have hvar_lt := hl_var li_c.toNat hi_lt
            have hkr_idx : (cref.setWidth 64 + 3#64 + li_c.setWidth 64).toNat <
                sem2.core.arena.length := by
              rw [hidx_li]; exact hkr_lt hi_lt
            let clit_v := sem2.core.arena[cref.toNat + 3 + li_c.toNat]'(hkr_lt hi_lt)
            let clv_v := sem2.core.lvl[clit_v.toNat / 2]'(by rw [hpi2.len.core_ok.lvl_len]; omega)
            have hcl_get : sem2.core.lvl[(sem2.core.arena[cref.toNat + 3 +
                li_c.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = clv_v := by
              rw [List.getElem?_eq_getElem (hkr_lt hi_lt), Option.getD_some,
                List.getElem?_eq_getElem (by rw [hpi2.len.core_ok.lvl_len]; omega),
                Option.getD_some]
            have hdec : fullArenaClauseSizeCore sem2.core cref.toNat -
                (li_c + (1 : BitVec 32)).toNat <
                fullArenaClauseSizeCore sem2.core cref.toNat - li_c.toNat := by
              rw [hli1]; exact Nat.sub_lt (Nat.sub_pos_of_lt hi_lt) Nat.zero_lt_one
            nb_head_steps
            refine wp_join_group (fun (mx_n, ()) m24 => m24 = m ∧
              (clit_v.toNat ≠ other.toNat → clv_v.toNat ≤ mx_n.toNat) ∧
              mx_c.toNat ≤ mx_n.toNat ∧
              (mx_n = mx_c ∨ (clit_v.toNat ≠ other.toNat ∧ mx_n = clv_v))) ?_ ?_
            · rintro _ ⟨mx_n, ⟨⟩⟩ m24 ⟨hm24, hcl_le, hmx_le, hmx_src⟩
              subst m24
              nb_head_steps
              refine ihi _ m hdec ⟨by rw [hli1]; exact Nat.succ_le_of_lt hi_lt, rfl,
                fun k hk hne => ?_, ?_⟩
              · rw [hli1] at hk
                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | hki
                · exact Nat.le_trans (hge k hk' hne) hmx_le
                · subst hki; rw [hcl_get]
                  apply hcl_le
                  rw [List.getElem?_eq_getElem (hkr_lt hi_lt), Option.getD_some] at hne
                  exact hne
              · rcases hmx_src with rfl | ⟨hne, rfl⟩
                · exact hatt.imp id fun ⟨k, hk, hne, he⟩ =>
                    ⟨k, by rw [hli1]; exact Nat.lt_succ_of_lt hk, hne, he⟩
                · exact Or.inr ⟨li_c.toNat, by rw [hli1]; exact Nat.lt_succ_self _, fun heq => by
                    rw [List.getElem?_eq_getElem (hkr_lt hi_lt), Option.getD_some] at heq
                    exact hne heq, hcl_get.symm⟩
            · intro J24 hJ24; nb_head_split
              · have hne_o : clit_v.toNat ≠ other.toNat := fun heq => by
                  apply hc; apply BitVec.eq_of_toNat_eq
                  simpa only [fastPropMem_arena,
                    Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + li_c.toNat < 2 ^ 64)] using heq
                nb_head_steps
                refine wp_join_group (fun (mx2, ()) m25 => m25 = m ∧
                  clv_v.toNat ≤ mx2.toNat ∧ mx_c.toNat ≤ mx2.toNat ∧
                  (mx2 = mx_c ∨ mx2 = clv_v)) ?_ ?_
                · rintro _ ⟨mx2, ⟨⟩⟩ m25 ⟨hm25, h1, h2, hsrc⟩
                  subst m25
                  nb_head_steps
                  exact hJ24 (mx2, ()) m ⟨rfl, fun _ => h1, h2, hsrc.imp id fun he => ⟨hne_o, he⟩⟩
                · intro J25 hJ25; nb_head_steps
                  · have hkr_idx_m : (cref.setWidth 64 + 3#64 + li_c.setWidth 64).toNat <
                        (fastPropMem s sem2).core.arena.length := by
                      rw [fastPropMem_arena]; exact hkr_idx
                    have hclv_mem : ∀ hp, ((fastPropMem s sem2).core.lvl[(BitVec.setWidth 64
                        ((fastPropMem s sem2).core.arena[(cref.setWidth 64 + 3#64 +
                          li_c.setWidth 64).toNat]'hkr_idx_m >>> 1)).toNat]'hp) = clv_v :=
                      fun hp => by
                        dsimp only [clv_v]
                        have h1 : (BitVec.setWidth 64 ((fastPropMem s sem2).core.arena[(
                            cref.setWidth 64 + 3#64 + li_c.setWidth 64).toNat]'hkr_idx_m >>>
                              1)).toNat = clit_v.toNat / 2 := by
                          rw [bv_c0_zext32_64, bv32_lshr_1]
                          exact congrArg (·.toNat / 2)
                            ((fc_getElem_arena s sem2).trans
                              (fc_getElem_eq_of_idx hidx_li _ (hkr_lt hi_lt)))
                        exact (fc_getElem_lvl s sem2).trans (fc_getElem_eq_of_idx h1 _ _)
                    have hgt : mx_c.toNat < clv_v.toNat := by
                      have hc' := hc
                      simp only [fastPropMem_lvl, fastPropMem_arena,
                        Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + li_c.toNat < 2 ^ 64)]
                        at hc'
                      exact hc'
                    refine hJ25 (_, ()) m ⟨rfl, ?_, ?_, Or.inr (hclv_mem _)⟩
                    · simp only [hclv_mem]; exact Nat.le_refl _
                    · simp only [hclv_mem]; exact Nat.le_of_lt hgt
                  · have hle : clv_v.toNat ≤ mx_c.toNat := by
                      have hnot_gt : ¬ mx_c.toNat < clv_v.toNat := by
                        have hc' := hc
                        simp only [fastPropMem_lvl, fastPropMem_arena,
                          Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + li_c.toNat < 2 ^ 64)]
                          at hc'
                        exact hc'
                      exact Nat.le_of_not_lt hnot_gt
                    exact hJ25 (mx_c, ()) m ⟨rfl, hle, Nat.le_refl _, Or.inl rfl⟩
              · have hcl_eq : clit_v.toNat = other.toNat := by
                  have hh := congrArg BitVec.toNat hc
                  simpa only [fastPropMem_arena,
                    Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + li_c.toNat < 2 ^ 64)] using hh
                nb_head_steps
                exact hJ24 (mx_c, ()) m
                  ⟨rfl, fun hne => absurd hcl_eq hne, Nat.le_refl _, Or.inl rfl⟩
          · have hi_eq : li_c.toNat = fullArenaClauseSizeCore sem2.core cref.toNat := by
              change ¬ li_c.toNat < csz32.toNat at hc
              exact Nat.le_antisymm hli_le (hcsz32 ▸ Nat.le_of_not_lt hc)
            nb_head_steps
            refine hJalvl _ m ⟨rfl, fun l hl hne => ?_, ?_⟩
            · obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd2).mp hl
              have hk' := hge k (hi_eq ▸ hk)
              rw [List.getElem?_eq_getElem (hkr_lt hk), Option.getD_some, hget] at hk'
              exact hk' hne
            · refine hatt.elim Or.inl fun ⟨k, hk, hne, hres⟩ => ?_
              have hk' : k < fullArenaClauseSizeCore sem2.core cref.toNat := hi_eq ▸ hk
              rw [List.getElem?_eq_getElem (hkr_lt hk'), Option.getD_some] at hne hres
              exact Or.inr ⟨(sem2.core.arena[cref.toNat + 3 + k]'(hkr_lt hk')).toNat,
                (mem_fullArenaClauseLitsCore_iff hbd2).mpr ⟨k, hk', rfl⟩, hne, hres⟩)
    · have hnot_ult : nl_lvl0.ult (BitVec.ofNat 32 sem2.core.cur_level) = false := by
        have hnot_lt_cl : ¬ nl_lvl0.toNat < sem2.core.cur_level := by
          simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl32] using hc
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl32]; exact hnot_lt_cl)
      have ⟨hge, hatt⟩ := fastProp_nonchrono_alvl hpi2.nw hcr_ref hng hpi2.not_f
        hov_un hnot_mem hunit hnl_eq hnot_ult hcl32
      nb_head_steps
      exact hJalvl _ m ⟨rfl, hge, hatt⟩

/-- Inner-bounds-check-free two-pass replacement literal search (`noBoundsReplSearchExpr`,
without `cand < nlits` check). -/
@[expose] def noBoundsReplSearchExpr (srch_v csz : Val i32) (cbase ar_p vals_p : Val i64)
    (j6_body : Tup Val [i32, i32, i32] → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i32, i32, i32]])
    (fun L10 => .cons (fun p1 =>
      .group (sig := [[i32, i32, i32]])
        (fun L11 => .cons (fun pf => j6_body pf) .nil)
        (fun L11 =>
          .let_ (Op.mk (.cmp .eq i32) (.var p1.1, (.imm (4294967295 : BitVec 32), ())))
            fun ceq =>
          .jnz (.var ceq.1) (
            .group (sig := [[i32, i32, i32]])
              (fun L21 => .cons (fun p2 =>
                .jump L11.1 (.var p2.1, (.var p2.2.1, (.var p2.2.2.1, ())))
              ) .nil)
              (fun L21 =>
                .group (sig := [[i32]])
                  (fun L22 => .cons (fun r2 =>
                    .let_ (Op.mk (.cmp .ult i32) (.var r2.1, (.var srch_v, ()))) fun clt =>
                    .jnz (.var clt.1) (
                      .let_ (Op.mk (.zext 32 64) (.var r2.1, ())) fun r64 =>
                      .let_ (Op.mk (.add i64) (.var cbase, (.var r64.1, ()))) fun idx0 =>
                      .let_ (Op.mk (.mul i64) (.var idx0.1, (.imm (4 : BitVec 64), ())))
                        fun off4 =>
                      .let_ (Op.mk (.add i64) (.var ar_p, (.var off4.1, ()))) fun par =>
                      .load i32 (.var par.1) fun cand =>
                      .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64' =>
                      .let_ (Op.mk (.add i64) (.var vals_p, (.var c64'.1, ()))) fun pv =>
                      .load i8 (.var pv.1) fun cv =>
                      .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun z8 =>
                      .let_ (Op.mk (.sext 8 32) (.var cv, ())) fun cv32 =>
                      .let_ (Op.mk (.sext 8 32) (.var z8.1, ())) fun z32 =>
                      .let_ (Op.mk (.cmp .sge i32) (.var cv32.1, (.var z32.1, ()))) fun csge =>
                      .jnz (.var csge.1)
                        (.jump L21.1 (.var r2.1, (.var cand, (.var r2.1, ()))))
                        (.let_ (Op.mk (.add i32) (.var r2.1, (.imm (1 : BitVec 32), ()))) fun r2' =>
                         .jump L22.1 (.var r2'.1, ()))
                    ) (.jump L21.1 (.var p1.1, (.var p1.2.1, (.var r2.1, ()))))
                  ) .nil)
                  (fun L22 => .jump L22.1 (.imm (2 : BitVec 32), ()))
              )
          ) (.jump L11.1 (.var p1.1, (.var p1.2.1, (.var p1.2.2.1, ()))))
        )
    ) .nil)
    (fun L10 =>
      .group (sig := [[i32]])
        (fun L24 => .cons (fun r1 =>
          .let_ (Op.mk (.cmp .ult i32) (.var r1.1, (.var csz, ()))) fun clt =>
          .jnz (.var clt.1) (
            .let_ (Op.mk (.zext 32 64) (.var r1.1, ())) fun r64 =>
            .let_ (Op.mk (.add i64) (.var cbase, (.var r64.1, ()))) fun idx0 =>
            .let_ (Op.mk (.mul i64) (.var idx0.1, (.imm (4 : BitVec 64), ()))) fun off4 =>
            .let_ (Op.mk (.add i64) (.var ar_p, (.var off4.1, ()))) fun par =>
            .load i32 (.var par.1) fun cand =>
            .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64' =>
            .let_ (Op.mk (.add i64) (.var vals_p, (.var c64'.1, ()))) fun pv =>
            .load i8 (.var pv.1) fun cv =>
            .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun z8 =>
            .let_ (Op.mk (.sext 8 32) (.var cv, ())) fun cv32 =>
            .let_ (Op.mk (.sext 8 32) (.var z8.1, ())) fun z32 =>
            .let_ (Op.mk (.cmp .sge i32) (.var cv32.1, (.var z32.1, ()))) fun csge =>
            .jnz (.var csge.1)
              (.jump L10.1 (.var r1.1, (.var cand, (.var r1.1, ()))))
              (.let_ (Op.mk (.add i32) (.var r1.1, (.imm (1 : BitVec 32), ()))) fun r1' =>
               .jump L24.1 (.var r1'.1, ()))
          ) (.jump L10.1 (.imm (4294967295 : BitVec 32), (.imm (0 : BitVec 32), (.var r1.1, ()))))
        ) .nil)
        (fun L24 => .jump L24.1 (.var srch_v, ()))
    )

theorem noBoundsReplSearch_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem1 : FullState} {not_lit cref srch_v csz32 : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64} {R : Mem 64 → Prop} {mj : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    {j6_body : Tup Val [i32, i32, i32] → Expr Val Cont [.bool]}
    (_hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hpi1 : Full.PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hng : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hcsz32_nat : csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (hsrch2 : 2 ≤ srch_v.toNat)
    (hsrch_lt : srch_v.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (hm : (FullMem c (fastPropMem s sem1) ⋆ R) mj)
    (hj6 : ∀ ri_f repl_f _rf : BitVec 32,
      ((ri_f = 0xFFFFFFFF#32 ∧ ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem1.core cref.toNat →
          Full.FullPropDecSpecs.fullFindReplBad sem1 cref.toNat k) ∨
       (ri_f ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri_f.toNat ∧
          ∃ hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
          repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(by
            rw [hpi1.len.core_ok.arena_len_arr]
            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr_lt _)
              (Nat.le_trans hfit1 hpi1.len.core_ok.arena_len_le)) ∧
          repl_f.toNat < 2 * sem1.core.cur_vars ∧
          ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)) →
      wp Γ Q X (j6_body (ri_f, repl_f, _rf, ())) mj) :
    wp Γ Q X (noBoundsReplSearchExpr srch_v csz32
      (cref.setWidth 64 + 3#64) c.pArena c.pVals j6_body) mj := by
  unfold dimacsBound at _hmaxv har
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1_le := hpi1.len.core_ok.arena_len_le
  have hvals1 := hpi1.len.core_ok.vals_len
  have hm1_aren := hlen1_mem.core_ok.arena_len_arr
  have hm1_vals := hlen1_mem.core_ok.vals_len
  have hcv1_eq := hpi1.cur_vars_eq
  have hfit1_ar : ∀ {r}, r < fullArenaClauseSizeCore sem1.core cref.toNat →
      cref.toNat + 3 + r < sem1.core.arena.length := fun hr => by
    rw [haren1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr _) (Nat.le_trans hfit1 halen1_le)
  have hcsz_lt32 : fullArenaClauseSizeCore sem1.core cref.toNat < 2 ^ 32 :=
    hcsz32_nat ▸ csz32.isLt
  have hcsz_lt_ff : fullArenaClauseSizeCore sem1.core cref.toNat < 0xFFFFFFFF :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hfit1)
      (Nat.lt_of_le_of_lt halen1_le (Nat.lt_trans har (by decide)))
  have hcand_live : ∀ (r : Nat) (hr : r < fullArenaClauseSizeCore sem1.core cref.toNat),
      (sem1.core.arena[cref.toNat + 3 + r]'(hfit1_ar hr)).toNat < 2 * sem1.core.cur_vars :=
    fun r hr => by
      have hmem : (sem1.core.arena[cref.toNat + 3 + r]'(hfit1_ar hr)).toNat ∈
          fullArenaClauseLitsCore sem1.core cref.toNat :=
        (mem_fullArenaClauseLitsCore_iff (haren1 ▸ Nat.le_trans hfit1 halen1_le)).mpr ⟨_, hr, rfl⟩
      exact hpi1.nw.arena.lits_lt cref.toNat hcr_ref hng _ hmem
  unfold noBoundsReplSearchExpr
  refine wp_loop_break_group
    (brkTs := [i32, i32, i32]) (lpTs := [i32])
    (fun (ri1, repl1, r1, ()) mb1 => mb1 = mj ∧
      ((ri1 = 0xFFFFFFFF#32 ∧ ∀ k, srch_v.toNat ≤ k →
          k < fullArenaClauseSizeCore sem1.core cref.toNat →
          Full.FullPropDecSpecs.fullFindReplBad sem1 cref.toNat k) ∨
       (ri1 ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri1.toNat ∧
          ∃ hr_lt : ri1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
          repl1 = sem1.core.arena[cref.toNat + 3 + ri1.toNat]'(hfit1_ar hr_lt) ∧
          repl1.toNat < 2 * sem1.core.cur_vars ∧
          ((sem1.core.vals[repl1.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)))
    (fun rem1 (r1, ()) ml1 => rem1 = csz32.toNat - r1.toNat ∧
      srch_v.toNat ≤ r1.toNat ∧ r1.toNat ≤ csz32.toNat ∧ ml1 = mj ∧
      ∀ k, srch_v.toNat ≤ k → k < r1.toNat →
        Full.FullPropDecSpecs.fullFindReplBad sem1 cref.toNat k) ?_ ?_ ?_
  · rintro _ ⟨ri1, repl1, r1, ⟨⟩⟩ mb1 ⟨hmb1, hres1⟩
    subst mb1
    refine wp_join_group (fun (ri_f, repl_f, rf, ()) mf => mf = mj ∧
        ((ri_f = 0xFFFFFFFF#32 ∧ ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem1.core cref.toNat →
            Full.FullPropDecSpecs.fullFindReplBad sem1 cref.toNat k) ∨
         (ri_f ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri_f.toNat ∧
            ∃ hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
            repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(hfit1_ar hr_lt) ∧
            repl_f.toNat < 2 * sem1.core.cur_vars ∧
            ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false))) ?_ ?_
    · rintro _ ⟨ri_f, repl_f, rf, ⟨⟩⟩ mf ⟨hmf, hfin⟩
      subst mf
      exact hj6 ri_f repl_f rf hfin
    · intro Jri hJri; nb_head_steps
      · have hri1 : ri1 = 0xFFFFFFFF#32 := hc
        have hnone1 : ∀ k, srch_v.toNat ≤ k →
            k < fullArenaClauseSizeCore sem1.core cref.toNat →
            Full.FullPropDecSpecs.fullFindReplBad sem1 cref.toNat k :=
          hres1.elim And.right fun h => absurd hri1 h.1
        refine wp_loop_break_group
          (brkTs := [i32, i32, i32]) (lpTs := [i32])
          (fun (ri2, repl2, r2, ()) mb2 => mb2 = mj ∧
            ((ri2 = 0xFFFFFFFF#32 ∧ ∀ k, 2 ≤ k →
                k < fullArenaClauseSizeCore sem1.core cref.toNat →
                Full.FullPropDecSpecs.fullFindReplBad sem1 cref.toNat k) ∨
             (ri2 ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri2.toNat ∧
                ∃ hr_lt : ri2.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
                repl2 = sem1.core.arena[cref.toNat + 3 + ri2.toNat]'(hfit1_ar hr_lt) ∧
                repl2.toNat < 2 * sem1.core.cur_vars ∧
                ((sem1.core.vals[repl2.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)))
          (fun rem2 (r2, ()) ml2 => rem2 = srch_v.toNat - r2.toNat ∧
            2 ≤ r2.toNat ∧ r2.toNat ≤ srch_v.toNat ∧ ml2 = mj ∧
            ∀ k, 2 ≤ k → k < r2.toNat →
              Full.FullPropDecSpecs.fullFindReplBad sem1 cref.toNat k) ?_ ?_ ?_
        · rintro _ ⟨ri2, repl2, r2, ⟨⟩⟩ mb2 ⟨hmb2, hres2⟩
          subst mb2
          nb_head_steps; exact hJri (ri2, repl2, r2, ()) mj ⟨rfl, hres2⟩
        · rintro B2 L2 _ ⟨r2, ⟨⟩⟩ ml2 hB2 ih2 ⟨rfl, hr2_ge, hr2_le, hml2, hseen2⟩
          subst ml2
          nb_head_split
          · have hr2_lt : r2.toNat < srch_v.toNat := by assumption
            have hr2_csz : r2.toNat < fullArenaClauseSizeCore sem1.core cref.toNat :=
              Nat.lt_trans hr2_lt hsrch_lt
            have hidx_r2 : (cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat =
                cref.toNat + 3 + r2.toNat := by
              rw [bv64_add_toNat (by
                rw [h3_idx, bv_c0_zext32_64]
                exact Nat.lt_of_lt_of_le (hfit1_ar hr2_csz) (Nat.le_trans
                  (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har (by decide))))),
                h3_idx, bv_c0_zext32_64]
            have hidx_r2_lt : (cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat < c.arena_cap := by
              rw [hidx_r2]; omega
            have hcand_cv_raw := hcand_live r2.toNat hr2_csz
            have hcand_max_raw : (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                hfit1_ar hr2_csz)).toNat < 2 * c.max_vars :=
              Nat.lt_of_lt_of_le hcand_cv_raw (Nat.mul_le_mul_left 2 (hcv1_eq ▸ hcv0))
            have hidx_r2_ar : (cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat <
                sem1.core.arena.length := by
              rw [hidx_r2]; exact hfit1_ar hr2_csz
            have hidx_r2_mod : (cref.toNat + 3 + r2.toNat) % 2 ^ 64 =
                cref.toNat + 3 + r2.toNat :=
              Nat.mod_eq_of_lt (by omega)
            have hr2_1 : (r2 + (1 : BitVec 32)).toNat = r2.toNat + 1 := by
              rw [BitVec.toNat_add]
              exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hr2_csz) hcsz_lt32)
            let cand2_m := (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 3#64 +
              r2.setWidth 64).toNat]'(by rw [fastPropMem_arena]; exact hidx_r2_ar)
            have hcand2_eq : cand2_m = sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                hfit1_ar hr2_csz) :=
              (fc_getElem_arena s sem1).trans
                (fc_getElem_eq_of_idx hidx_r2 _ (hfit1_ar hr2_csz))
            nb_head_steps
            · have hok := fastProp_findRepl_ok (st := sem1) (cref := cref.toNat) (r := r2.toNat)
                (hi_lt := hfit1_ar hr2_csz) (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le
                  hcand_cv_raw (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
                hcand_cv_raw
                (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r2_mod] using hc)
              have hr2_ne : r2 ≠ 0xFFFFFFFF#32 := fun heq => by
                have heq' : r2.toNat = 0xFFFFFFFF := by rw [heq]; decide
                exact absurd (heq' ▸ hr2_csz) (Nat.not_lt.mpr (Nat.le_of_lt hcsz_lt_ff))
              exact hB2 (r2, cand2_m, r2, ()) mj ⟨rfl, Or.inr ⟨hr2_ne, hr2_ge, hr2_csz,
                hcand2_eq, by simpa only [hcand2_eq,
                  List.getElem?_eq_getElem (hfit1_ar hr2_csz), Option.getD_some] using hok⟩⟩
            · have hbad := fastProp_findRepl_bad_slt (st := sem1) (cref := cref.toNat)
                (r := r2.toNat) (hi_lt := hfit1_ar hr2_csz)
                (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le hcand_cv_raw
                  (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
                (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r2_mod] using hc)
              exact ih2 _ _ mj (by
                  rw [hr2_1]; exact Nat.sub_lt (Nat.sub_pos_of_lt hr2_lt) Nat.zero_lt_one)
                ⟨rfl, by rw [hr2_1]; exact Nat.le_trans hr2_ge (Nat.le_succ _),
                 by rw [hr2_1]; exact Nat.succ_le_of_lt hr2_lt, rfl,
                 fun k hk1 hk2 => by
                   rw [hr2_1] at hk2
                   rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk2) with hk' | hkr
                   · exact hseen2 k hk1 hk'
                   · subst hkr; exact hbad⟩
          · have hr2_eq : r2.toNat = srch_v.toNat := Nat.le_antisymm hr2_le (Nat.le_of_not_lt hc)
            nb_head_steps
            exact hB2 (ri1, repl1, r2, ()) mj ⟨rfl, Or.inl ⟨hri1,
              fun k hk2 hksz => if hks : k < srch_v.toNat then hseen2 k hk2 (hr2_eq ▸ hks)
                else hnone1 k (Nat.le_of_not_lt hks) hksz⟩⟩
        · intro B2 L2 _ hL2; nb_head_steps
          exact hL2 _ (2#32, ()) mj ⟨rfl, by decide, hsrch2, rfl,
            fun _ hk1 hk2 => absurd (Nat.lt_of_le_of_lt hk1 hk2) (by decide)⟩
      · exact hJri (ri1, repl1, r1, ()) mj ⟨rfl, Or.inr (hres1.resolve_left (fun h => hc h.1))⟩
  · rintro B1 L1 _ ⟨r1, ⟨⟩⟩ ml1 hB1 ih1 ⟨rfl, hr1_ge, hr1_le, hml1, hseen1⟩
    subst ml1
    nb_head_split
    · have hr1_lt : r1.toNat < csz32.toNat := by assumption
      have hr1_csz : r1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat := hcsz32_nat ▸ hr1_lt
      have hidx_r1 : (cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat =
          cref.toNat + 3 + r1.toNat := by
        rw [bv64_add_toNat (by
          rw [h3_idx, bv_c0_zext32_64]
          exact Nat.lt_of_lt_of_le (hfit1_ar hr1_csz) (Nat.le_trans
            (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har (by decide))))),
          h3_idx, bv_c0_zext32_64]
      have hidx_r1_lt : (cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat < c.arena_cap := by
        rw [hidx_r1]; omega
      have hcand_cv_raw := hcand_live r1.toNat hr1_csz
      have hcand_max_raw : (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
          hfit1_ar hr1_csz)).toNat < 2 * c.max_vars :=
        Nat.lt_of_lt_of_le hcand_cv_raw (Nat.mul_le_mul_left 2 (hcv1_eq ▸ hcv0))
      have hidx_r1_ar : (cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat <
          sem1.core.arena.length := by
        rw [hidx_r1]; exact hfit1_ar hr1_csz
      have hidx_r1_mod : (cref.toNat + 3 + r1.toNat) % 2 ^ 64 = cref.toNat + 3 + r1.toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hr1_1 : (r1 + (1 : BitVec 32)).toNat = r1.toNat + 1 := by
        rw [BitVec.toNat_add]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hr1_csz) hcsz_lt32)
      let cand1_m := (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 3#64 +
        r1.setWidth 64).toNat]'(by rw [fastPropMem_arena]; exact hidx_r1_ar)
      have hcand1_eq : cand1_m = sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
          hfit1_ar hr1_csz) :=
        (fc_getElem_arena s sem1).trans (fc_getElem_eq_of_idx hidx_r1 _ (hfit1_ar hr1_csz))
      nb_head_steps
      · have hok := fastProp_findRepl_ok (st := sem1) (cref := cref.toNat) (r := r1.toNat)
          (hi_lt := hfit1_ar hr1_csz) (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le
            hcand_cv_raw (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
          hcand_cv_raw
          (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r1_mod] using hc)
        have hr1_ne : r1 ≠ 0xFFFFFFFF#32 := fun heq => by
          have heq' : r1.toNat = 0xFFFFFFFF := by rw [heq]; decide
          exact absurd (heq' ▸ hr1_csz) (Nat.not_lt.mpr (Nat.le_of_lt hcsz_lt_ff))
        exact hB1 (r1, cand1_m, r1, ()) mj ⟨rfl, Or.inr ⟨hr1_ne, Nat.le_trans hsrch2 hr1_ge,
          hr1_csz, hcand1_eq, by simpa only [hcand1_eq,
            List.getElem?_eq_getElem (hfit1_ar hr1_csz), Option.getD_some] using hok⟩⟩
      · have hbad := fastProp_findRepl_bad_slt (st := sem1) (cref := cref.toNat)
          (r := r1.toNat) (hi_lt := hfit1_ar hr1_csz)
          (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le hcand_cv_raw
            (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
          (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r1_mod] using hc)
        exact ih1 _ _ mj (by
            rw [hr1_1]; exact Nat.sub_lt (Nat.sub_pos_of_lt hr1_lt) Nat.zero_lt_one)
          ⟨rfl, by rw [hr1_1]; exact Nat.le_trans hr1_ge (Nat.le_succ _),
           by rw [hr1_1]; exact Nat.succ_le_of_lt hr1_lt, rfl,
           fun k hk1 hk2 => by
             rw [hr1_1] at hk2
             rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk2) with hk' | hkr
             · exact hseen1 k hk1 hk'
             · subst hkr; exact hbad⟩
    · have hr1_eq : r1.toNat = csz32.toNat := Nat.le_antisymm hr1_le (Nat.le_of_not_lt hc)
      nb_head_steps
      exact hB1 (0xFFFFFFFF#32, 0#32, r1, ()) mj ⟨rfl, Or.inl ⟨rfl, fun k hk1 hk2 => by
        rw [← hcsz32_nat, ← hr1_eq] at hk2; exact hseen1 k hk1 hk2⟩⟩
  · intro B1 L1 _ hL1; nb_head_steps
    exact hL1 _ (srch_v, ()) mj ⟨rfl, Nat.le_refl _, hcsz32_nat ▸ Nat.le_of_lt hsrch_lt, rfl,
      fun _ hk1 hk2 => absurd hk1 (Nat.not_le.mpr hk2)⟩

/-- Exit helper (`Loop 2` copy + `Loop 3` dead-tail `0xFFFFFFFFu` fill + probing-gated ticks)
matching `full_prop_lit_nobounds_m7` tail verbatim and preserving `FullWatchBoundsInv`. -/
@[expose] def m7NoBoundsFinishExpr (h_p pWvec pWstk : Val i64) (not_lit : Val i32)
    (off_v tend_v unass_v unfl_v ticks_v p_v q_v end_v : Val i64) (confl_v : Val .bool) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i64, i64]])
    (fun L1 => .cons (fun q =>
      .let_ (Op.mk (.cmp .ult i64) (.var q.1, (.var end_v, ()))) fun v88 =>
      .jnz (.var v88.1) (
        .let_ (Op.mk (.mul i64) (.var q.2.1, (.imm (4 : BitVec 64), ()))) fun v89 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v89.1, ()))) fun v90 =>
        .let_ (Op.mk (.mul i64) (.var q.1, (.imm (4 : BitVec 64), ()))) fun v91 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v91.1, ()))) fun v92 =>
        .load i32 (.var v92.1) fun v93 =>
        .store (.var v93) (.var v90.1) (
          .let_ (Op.mk (.add i64) (.var q.2.1, (.imm (1 : BitVec 64), ()))) fun v94 =>
          .let_ (Op.mk (.add i64) (.var q.1, (.imm (1 : BitVec 64), ()))) fun v95 =>
          .jump L1.1 (.var v95.1, (.var v94.1, ()))
        )
      ) (
        .group (sig := [[i64]])
          (fun L3 => .cons (fun k =>
            .let_ (Op.mk (.cmp .ult i64) (.var k.1, (.var end_v, ()))) fun c3 =>
            .jnz (.var c3.1) (
              .let_ (Op.mk (.mul i64) (.var k.1, (.imm (4 : BitVec 64), ()))) fun o4 =>
              .let_ (Op.mk (.add i64) (.var pWstk, (.var o4.1, ()))) fun pk =>
              .store (t := i32) (.imm 0xFFFFFFFF#32) (.var pk.1) (
                .let_ (Op.mk (.add i64) (.var k.1, (.imm (1 : BitVec 64), ()))) fun k1 =>
                .jump L3.1 (.var k1.1, ())
              )
            ) (
              .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun v89 =>
              .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun v90 =>
              .let_ (Op.mk (.shl i64) (.var v89.1, (.var v90.1, ()))) fun v91 =>
              .let_ (Op.mk (.add i64) (.var v91.1, (.imm (1 : BitVec 64), ()))) fun v92 =>
              .let_ (Op.mk (.mul i64) (.var v92.1, (.imm (4 : BitVec 64), ()))) fun v93 =>
              .let_ (Op.mk (.add i64) (.var pWvec, (.var v93.1, ()))) fun v94 =>
              .let_ (Op.mk (.sub i64) (.var q.2.1, (.var off_v, ()))) fun v95 =>
              .let_ (Op.mk (.trunc 64 32) (.var v95.1, ())) fun v96 =>
              .store (.var v96.1) (.var v94.1) (
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v97 =>
                .load i64 (.var v97.1) fun v98 =>
                .let_ (Op.mk (.sub i64) (.var end_v, (.var q.2.1, ()))) fun v99 =>
                .let_ (Op.mk (.add i64) (.var v98, (.var v99.1, ()))) fun v100 =>
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v101 =>
                .store (.var v100.1) (.var v101.1) (
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (144 : BitVec 64), ()))) fun v102 =>
                  .store (.var tend_v) (.var v102.1) (
                    .let_ (Op.mk (.add i64) (.var h_p, (.imm (792 : BitVec 64), ()))) fun v103 =>
                    .store (.var unass_v) (.var v103.1) (
                      .let_ (Op.mk (.add i64) (.var h_p, (.imm (512 : BitVec 64), ()))) fun v104 =>
                      .store (.var unfl_v) (.var v104.1) (
                        .group (sig := [[]])
                          (fun L4 => .cons (fun _ =>
                            .let_ (Op.mk (.not .bool) (.var confl_v, ())) fun v109 =>
                            .ret (.var v109.1, ())
                          ) .nil)
                          (fun L4 =>
                            .let_ (Op.mk (.add i64) (.var h_p, (.imm (520 : BitVec 64), ())))
                              fun vp0 =>
                            .load i64 (.var vp0.1) fun vp1 =>
                            .let_ (Op.mk (.cmp .eq i64) (.var vp1, (.imm (0 : BitVec 64), ())))
                              fun vp2 =>
                            .jnz (.var vp2.1) (
                              .let_ (Op.mk (.add i64) (.var h_p, (.imm (600 : BitVec 64), ())))
                                fun v105 =>
                              .load i64 (.var v105.1) fun v106 =>
                              .let_ (Op.mk (.add i64) (.var v106, (.var ticks_v, ()))) fun v107 =>
                              .let_ (Op.mk (.add i64) (.var h_p, (.imm (600 : BitVec 64), ())))
                                fun v108 =>
                              .store (.var v107.1) (.var v108.1) (
                                .jump L4.1 ()
                              )
                            ) (.jump L4.1 ())
                          )
                      )
                    )
                  )
                )
              )
            )
          ) .nil)
          (fun L3 => .jump L3.1 (.var q.2.1, ()))
      )
    ) .nil)
    (fun L1 => .jump L1.1 (.var p_v, (.var q_v, ())))

theorem m7NoBoundsFinish_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem : FullState} {not_lit : BitVec 32}
    {off_v tend_v unass_v unfl_v ticks_v p_v q_v end_v ignore_ref : BitVec 64}
    {confl_v : Bool} {R : Mem 64 → Prop} {mb : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hwc : c.wcap < 2 * dimacsBound) (_hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hdense0 : s.core.dense_mode = 0#64) (hnot_lt : not_lit.toNat < 2 * s.core.cur_vars)
    (hnb : PropLitNoBoundsInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
      end_v.toNat)
    (htend_eq : tend_v.toNat = sem.core.trail_end) (hunass_eq : unass_v = sem.core.unassigned)
    (hunfl_eq : unfl_v = sem.core.unflushed)
    (hcf_f : confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type)
    (hcf_t : confl_v = true → Full.PropLitConfl F_cur ignore_ref sem.core)
    (hmb : (FullMem c (fastPropMem s sem) ⋆ R) mb)
    (hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core → FullWatchBoundsInv st →
      AgreesExcept Full.propLitCoreMask s.core st.core →
      Full.FullPropDecSpecs.FullTrailExt s.core st.core →
      Full.FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = false → Full.PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml) :
    wp Γ Q X (m7NoBoundsFinishExpr c.hdr c.pWvec c.pWstk not_lit off_v tend_v unass_v unfl_v
      ticks_v p_v q_v end_v confl_v) mb := by
  have hpi := hnb.prop
  have hnot_st : not_lit.toNat < 2 * sem.core.cur_vars := hpi.cur_vars_eq.symm ▸ hnot_lt
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
  have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  unfold dimacsBound at hwc
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hwstk_len := hpi.len.core_ok.wstk_len_arr; have hwvec_len := hpi.len.core_ok.wvec_len
  have hwvec_mem : (fastPropMem s sem).core.wvec.length = 4 * c.max_vars := by
    rw [fastPropMem_wvec]; exact hwvec_len
  have hidx1_nat :
      ((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 :=
    fc_bv64_shl1_add1_nat not_lit
  let q_fin : Nat := q_v.toNat + (end_v.toNat - p_v.toNat)
  unfold m7NoBoundsFinishExpr
  refine wp_loop_inv
    (fun (p_c, q_c, ()) m2 => ∃ wstk_c : List (BitVec 32),
      wstk_c.length = c.wcap ∧ p_v.toNat ≤ p_c.toNat ∧ p_c.toNat ≤ end_v.toNat ∧
      q_c.toNat = q_v.toNat + (p_c.toNat - p_v.toNat) ∧
      (∀ k, off_v.toNat ≤ k → k < q_v.toNat → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (∀ k < p_c.toNat - p_v.toNat, wstk_c[q_v.toNat + k]? = sem.core.wstk[p_v.toNat + k]?) ∧
      (∀ k, p_c.toNat ≤ k → k < end_v.toNat → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (∀ k, (k < off_v.toNat ∨ end_v.toNat ≤ k) → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (FullMem c (fastPropMem s { sem with core := { sem.core with wstk := wstk_c } }) ⋆ R) m2)
    (fun (p_c, _, ()) _ => end_v.toNat - p_c.toNat)
    (fun L2 hL2 => by
      nb_head_steps
      exact hL2 (p_v, q_v, ()) mb ⟨sem.core.wstk, hwstk_len, Nat.le_refl _, hp_le, by omega,
        fun _ _ _ => rfl, fun _ hk => by omega, fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩)
    (fun L2 (p_c, q_c, ()) m2 ⟨wstk_c, hwl2, hp_ge, hp_le2, hqc_eq,
        hpre, hsuf, hrem, hout, hm2⟩ ih2 => ?_)
  nb_head_steps
  · have hp_lt : p_c.toNat < end_v.toNat := hc
    have hstep := Full.propLit_loop2_step hq_ge hq_le hp_ge hp_lt (by omega) (by omega)
      hpre hsuf hrem hout
    have hpc_add : (p_c + (1 : BitVec 64)).toNat = p_c.toNat + 1 := bv64_add1_no_ovf (by omega)
    have hqc_add : (q_c + (1 : BitVec 64)).toNat =
        q_v.toNat + ((p_c + (1 : BitVec 64)).toNat - p_v.toNat) := by
      rw [bv64_add1_no_ovf (by omega), hpc_add]; omega
    refine ih2 (p_c + (1 : BitVec 64), q_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
      ⟨wstk_c.set q_c.toNat (wstk_c[p_c.toNat]'(by omega)), by simp [hwl2],
        by omega, by omega, hqc_add, ?_, ?_, ?_, ?_, by
          simpa only [fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
    · simpa only [← hqc_eq] using hstep.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.2.1
    · simpa only [← hqc_eq] using hstep.2.2.2
  · have hpc_eq : p_c.toNat = end_v.toNat := by c0_bound
    have hqfin_eq : q_c.toNat = q_fin := by dsimp [q_fin]; omega
    refine wp_loop_inv
      (fun (k_c, ()) m3 => ∃ wstk_k : List (BitVec 32),
        wstk_k.length = c.wcap ∧ q_fin ≤ k_c.toNat ∧ k_c.toNat ≤ end_v.toNat ∧
        (∀ i, (i < q_fin ∨ end_v.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
        (FullMem c (fastPropMem s { sem with core := { sem.core with wstk := wstk_k } }) ⋆ R) m3)
      (fun (k_c, ()) _ => end_v.toNat - k_c.toNat)
      (fun L3 hL3 => by
        nb_head_steps
        exact hL3 (q_c, ()) m2 ⟨wstk_c, hwl2, by omega, by omega, fun _ _ => rfl, hm2⟩)
      (fun L3 (k_c, ()) m3 ⟨wstk_k, hwl3, hk_ge, hk_le, hkeep, hm3⟩ ih3 => ?_)
    nb_head_steps
    · have hk_lt : k_c.toNat < end_v.toNat := hc
      have hk_add : (k_c + (1 : BitVec 64)).toNat = k_c.toNat + 1 :=
        bv64_add1_no_ovf (by omega)
      refine ih3 (k_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
        ⟨wstk_k.set k_c.toNat 0xFFFFFFFF#32, by simp [hwl3], by omega, by omega,
          Full.propLit_loop3_step hk_ge hk_lt hkeep, by
            simpa only [fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
    · have hk_eq : k_c.toNat = end_v.toNat := by c0_bound
      refine wp_join_group (ts := [])
        (fun () m4 => ∃ ticks_fin : BitVec 64,
          let sem' : FullState :=
            { sem with scratch := { sem.scratch with search_ticks := ticks_fin } }
          Full.PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
            end_v.toNat ∧
          (FullMem c { sem' with core := { sem'.core with
              wstk := wstk_k
              wvec := sem'.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_v).setWidth 32)
              wusable := sem'.core.wusable + (end_v - q_c) } } ⋆ R) m4)
        ?_ ?_
      · rintro _ ⟨⟩ m4 ⟨ticks_fin, hpi', hm_rew⟩
        nb_head_steps
        have ⟨hl_f, hw_f, hag_f, htr_f, hperm_f, hsc_f, hcf_f', hoom_f, hm_f⟩ :=
          Full.propLit_finish (ctype0 := s.core.confl_type) hpi' hdense0 hnot_st hwl3 hqfin_eq rfl
            hpre (fun k hk => hsuf k (by omega)) hout hkeep hcf_f hcf_t hm_rew
        have hkeep_pre : ∀ j, off_v.toNat ≤ j → j < q_v.toNat →
            wstk_k[j]? = sem.core.wstk[j]? := fun j hj1 hj2 =>
          (hkeep j (Or.inl (by dsimp [q_fin]; omega))).trans (hpre j hj1 hj2)
        have hkeep_suf : ∀ j < end_v.toNat - p_v.toNat,
            wstk_k[q_v.toNat + j]? = sem.core.wstk[p_v.toNat + j]? := fun j hj =>
          (hkeep (q_v.toNat + j) (Or.inl (by dsimp [q_fin]; omega))).trans (hsuf j (by omega))
        have hkeep_out : ∀ j, (j < off_v.toNat ∨ end_v.toNat ≤ j) →
            wstk_k[j]? = sem.core.wstk[j]? := fun j hj =>
          (hkeep j (by
            cases hj with
            | inl h1 => exact Or.inl (by dsimp [q_fin]; have := hpi.sw.q_ge; omega)
            | inr h2 => exact Or.inr h2)).trans (hout j hj)
        have hwb_fin0 := hnb.sb.finish { sem with scratch := { sem.scratch with
            search_ticks := ticks_fin } }.scratch hpi.sw hnot_st hpi.len.core_ok.cur_vars_le
          hwvec_len hwlen_le (wu' := sem.core.wusable + (end_v - q_c)) hkeep_pre hkeep_suf
          hkeep_out
        exact hret_st (!confl_v) _ m4 hl_f hw_f hwb_fin0 hag_f htr_f hperm_f hsc_f hcf_f' hoom_f
          hm_f
      · intro L4 hL4
        nb_head_steps
        · let sem' : FullState :=
            { sem with scratch :=
                { sem.scratch with search_ticks := s.scratch.search_ticks + ticks_v } }
          have hpi' : Full.PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat q_v.toNat
              p_v.toNat end_v.toNat :=
            { len := ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks _⟩
              nw := hpi.nw, sw := hpi.sw, ag := hpi.ag, tr := hpi.tr, perm := hpi.perm
              sc_eq := by dsimp only [sem']; rw [hpi.sc_eq]
              not_f := hpi.not_f }
          have hm_rew :
              (FullMem c { sem' with core := { sem'.core with
                  wstk := wstk_k
                  wvec := sem'.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_v).setWidth 32)
                  wusable := sem'.core.wusable + (end_v - q_c) } } ⋆ R) m := by
            simp only [hidx1_nat, fastPropMem_wvec, fastPropMem_wusable,
              fastPropMem_search_ticks] at hm
            rw [htend_eq, hunass_eq, hunfl_eq] at hm
            rw [fastPropMem_finish_eq] at hm
            exact hm
          exact hL4 () m ⟨s.scratch.search_ticks + ticks_v, hpi', hm_rew⟩
        · let sem' : FullState :=
            { sem with scratch := { sem.scratch with search_ticks := s.scratch.search_ticks } }
          have hpi' : Full.PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat q_v.toNat
              p_v.toNat end_v.toNat :=
            { len := ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks _⟩
              nw := hpi.nw, sw := hpi.sw, ag := hpi.ag, tr := hpi.tr, perm := hpi.perm
              sc_eq := by dsimp only [sem']; rw [hpi.sc_eq]
              not_f := hpi.not_f }
          have hm_rew :
              (FullMem c { sem' with core := { sem'.core with
                  wstk := wstk_k
                  wvec := sem'.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_v).setWidth 32)
                  wusable := sem'.core.wusable + (end_v - q_c) } } ⋆ R) m := by
            simp only [hidx1_nat, fastPropMem_wvec, fastPropMem_wusable] at hm
            rw [htend_eq, hunass_eq, hunfl_eq, fastPropMem_def] at hm
            exact hm
          exact hL4 () m ⟨s.scratch.search_ticks, hpi', hm_rew⟩

end LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds
