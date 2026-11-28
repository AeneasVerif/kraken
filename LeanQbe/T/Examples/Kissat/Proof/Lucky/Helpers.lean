/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Shared Pure Invariant & M6-Call Helpers for `Kissat.Proof.Lucky`

Self-contained zero-legacy pure BV, `PolarWatchOk`, `FullSparseInv`, `decide`,
`backtrack`, `propagate`, and `analyze` helpers for `Wp0` and `Wp1`.
-/

set_option autoImplicit false

local elab "lk_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "lk_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Lucky

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6ProofUtilTactics

/-! ## 1. Pure BitVec & Arena Helpers -/

theorem lk_bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem lk_bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem lk_bv64_trunc32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, lk_bv64_ofNat_toNat (by omega), lk_bv32_ofNat_toNat hn,
    Nat.mod_eq_of_lt hn]

theorem lk_bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) :
    (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem lk_bv64_shl1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (x <<< 1#64).toNat = 2 * x.toNat := by
  have h1 : (x <<< 1#64).toNat = (x.toNat * 2) % 2 ^ 64 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [h1, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

theorem lk_bv64_shl1_eq (x : BitVec 64) : x <<< 1#64 = x * 2#64 := by
  change x <<< (1#64).toNat = x * 2#64
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq, Nat.mul_comm]

theorem lk_bv64_shl1_or1_eq (x : BitVec 64) : x <<< 1#64 ||| 1#64 = x * 2#64 + 1#64 := by
  rw [lk_bv64_shl1_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_add]
  obtain ⟨k, hk⟩ : ∃ k, (x * 2#64).toNat = 2 * k :=
    ⟨(x * 2#64).toNat / 2, by rw [BitVec.toNat_mul]; simp; omega⟩
  rw [hk]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have hlor : (2 * k) ||| 1 = 2 * k + 1 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_or]
    cases i with
    | zero => simp
    | succ i =>
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simp [Nat.testBit_succ, hdiv]
  rw [hlor]
  have hk_lt : 2 * k + 1 < 2 ^ 64 := by
    have : (x * 2#64).toNat < 2 ^ 64 := (x * 2#64).isLt; omega
  exact (Nat.mod_eq_of_lt hk_lt).symm

theorem lk_bv32_shl1_trunc32_toNat {v : BitVec 64} (hv : 2 * v.toNat < 2 ^ 32) :
    ((v <<< 1#64).setWidth 32).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_setWidth, lk_bv64_shl1_toNat (by omega), Nat.mod_eq_of_lt hv]

theorem lk_bv32_shl1_or1_trunc32_toNat {v : BitVec 64} (hv : 2 * v.toNat + 1 < 2 ^ 32) :
    (((v <<< 1#64).setWidth 32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  rw [BitVec.toNat_or, lk_bv32_shl1_trunc32_toNat (by omega)]
  change (2 * v.toNat) ||| 1 = 2 * v.toNat + 1
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_or]
    simp only [Nat.testBit_succ, show (1 : Nat) / 2 = 0 from rfl,
      show (2 * v.toNat) / 2 = v.toNat from by omega,
      show (2 * v.toNat + 1) / 2 = v.toNat from by omega,
      Nat.zero_testBit, Bool.or_false]

theorem lk_bv32_lit_even {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    ((v <<< 1#64).setWidth 32).toNat = 2 * v.toNat :=
  lk_bv32_shl1_trunc32_toNat (by omega)

theorem lk_bv32_lit_odd {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (((v <<< 1#64).setWidth 32) ||| 1#32).toNat = 2 * v.toNat + 1 :=
  lk_bv32_shl1_or1_trunc32_toNat (by omega)

theorem lk_bv32_xor1_div2 (l : BitVec 32) : (l ^^^ 1#32).toNat / 2 = l.toNat / 2 := by
  rw [bv32_lit_neg_toNat, nat_xor1_div2]

theorem lk_bv8_sext32_eq0_iff : ∀ x : BitVec 8, x.signExtend 32 = 0#32 ↔ x = 0#8 := by
  decide

theorem lk_bv8_dom_sgt0_iff {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#32).slt (x.signExtend 32) = true ↔ x = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem lk_bv8_dom_slt0_iff {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem lk_bv8_eq0_of_not_slt_sgt {x : BitVec 8} (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8)
    (h1 : (0#32).slt (x.signExtend 32) = false) (h2 : (x.signExtend 32).slt 0#32 = false) :
    x = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> first | rfl | (exfalso; revert h1 h2; decide)

theorem arena_lit_mem_clauseLits (k : FullCoreState) (r j : Nat)
    (hj : j < fullArenaClauseSizeCore k r) (hrj : r + 3 + j < k.arena.length) :
    k.arena[r + 3 + j].toNat ∈ fullArenaClauseLitsCore k r := by
  unfold fullArenaClauseLitsCore
  rw [List.mem_map]
  refine ⟨k.arena[r + 3 + j], ?_, rfl⟩
  have h1 : k.arena[r + 3 + j] = (k.arena.drop (r + 3))[j]'(by simp; omega) := by
    simp [Nat.add_assoc]
  rw [h1]
  have h2 : j < ((k.arena.drop (r + 3)).take (fullArenaClauseSizeCore k r)).length := by
    simp; omega
  have hmem : (k.arena.drop (r + 3))[j]'(by simp; omega) =
      ((k.arena.drop (r + 3)).take (fullArenaClauseSizeCore k r))[j]'h2 := by simp
  rw [hmem]
  exact List.getElem_mem h2

private theorem fullArenaScanRefs_succ (ar : List (BitVec 32)) (alen pos f : Nat) :
    fullArenaScanRefs ar alen pos (f + 1) =
      if pos + 3 ≤ alen then pos :: fullArenaScanRefs ar alen (fullArenaNextOff ar alen pos) f
      else [] := by
  cases f <;> simp [fullArenaScanRefs]

theorem fullArenaScanRefs_next_mem (ar : List (BitVec 32)) (alen : Nat) :
    ∀ (fuel pos r : Nat), alen - pos ≤ fuel →
      (∀ p ∈ fullArenaScanRefs ar alen pos fuel,
        p + 3 ≤ fullArenaNextOff ar alen p ∧
        (fullArenaNextOff ar alen p = alen ∨ fullArenaNextOff ar alen p + 3 ≤ alen)) →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r = alen ∨
        fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, _, hr => by simp [fullArenaScanRefs] at hr
  | f + 1, pos, r, hfuel, hwf, hr => by
    rw [fullArenaScanRefs_succ] at hr ⊢
    by_cases hpos : pos + 3 ≤ alen
    · simp only [hpos, ↓reduceIte, List.mem_cons] at hr ⊢
      have hpos_wf := hwf pos (by rw [fullArenaScanRefs_succ]; simp [hpos])
      let nxt := fullArenaNextOff ar alen pos
      rcases hr with rfl | hr_tail
      · rcases hpos_wf.2 with heq | h3
        · exact Or.inl heq
        · right; right
          obtain ⟨f', hf'⟩ : ∃ f', f = f' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
          subst hf'
          rw [fullArenaScanRefs_succ]; simp [h3]
      · have hwf_tail : ∀ p ∈ fullArenaScanRefs ar alen nxt f,
            p + 3 ≤ fullArenaNextOff ar alen p ∧
            (fullArenaNextOff ar alen p = alen ∨ fullArenaNextOff ar alen p + 3 ≤ alen) :=
          fun p hp => hwf p (by rw [fullArenaScanRefs_succ]; simp [hpos, nxt, hp])
        rcases fullArenaScanRefs_next_mem ar alen f nxt r (by omega) hwf_tail hr_tail with
          heq | hm
        · exact Or.inl heq
        · exact Or.inr (Or.inr hm)
    · simp [hpos] at hr

/-! ## 2. Unified Watch-Slice Invariant for `full_lucky_polar_m7` -/

inductive PolarWatchOk (k : FullCoreState) : Nat → Nat → Prop where
  | empty (p : Nat) : PolarWatchOk k p 0
  | bin {p rem : Nat} {w0 : BitVec 32} :
      k.wstk[p]? = some w0 → w0 &&& 2147483648#32 ≠ 0#32 → w0 ≠ 4294967295#32 →
      (w0 &&& 2147483647#32).toNat < 2 * k.cur_vars → PolarWatchOk k (p + 1) rem →
      PolarWatchOk k p (rem + 1)
  | large {p rem : Nat} {w0 : BitVec 32} :
      k.wstk[p]? = some w0 → w0 &&& 2147483648#32 = 0#32 → PolarWatchOk k (p + 2) rem →
      PolarWatchOk k p (rem + 2)

theorem modeWatchesInv_toPolar {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) :
    WatchStackLayout k ∧ ∀ l < 2 * k.cur_vars,
      PolarWatchOk k (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  have toPolW : ∀ {lit p rem}, WatchSliceOk F_cur k lit p rem → PolarWatchOk k p rem := by
    intro lit p rem hw
    induction hw with
    | empty => exact .empty _
    | bin h0 hb hn hl _ _ ih => exact .bin h0 hb hn hl ih
    | large h0 _ hb _ _ _ ih => exact .large h0 hb ih
  have toPolD : ∀ {lit p rem}, DenseWatchSliceOk F_cur k lit p rem → PolarWatchOk k p rem := by
    intro lit p rem hw
    induction hw with
    | empty => exact .empty _
    | bin h0 hb hn hl _ _ ih => exact .bin h0 hb hn hl ih
    | occ h0 _ hb _ _ _ _ ih => exact .large h0 hb ih
  unfold ModeWatchesInv at h
  by_cases hdm : k.dense_mode = 0#64
  · simp [hdm] at h; exact ⟨h.layout, fun l hl => toPolW (h.slices l hl)⟩
  · simp [hdm] at h; exact ⟨h.layout, fun l hl => toPolD (h.slices l hl)⟩

/-! ## 3. `FullSparseInv`, `decide`, `backtrack`, `propagate` & `analyze` Lemmas -/

theorem fullSparseInv_with_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (v : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with probing := v } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hw' : FullWitnessInv c F0 F_cur { s.core with probing := v } :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨⟨⟨{ h.1.lengths.core_ok with cur_vars_le := h.1.lengths.core_ok.cur_vars_le },
    h.1.lengths.scratch_ok⟩, F_cur, hw'⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem fullSparseInv_with_fuel {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (f : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with fuel := f } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hw' : FullWitnessInv c F0 F_cur { s.core with fuel := f } :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨⟨⟨{ h.1.lengths.core_ok with cur_vars_le := h.1.lengths.core_ok.cur_vars_le },
    h.1.lengths.scratch_ok⟩, F_cur, hw'⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem fullSparseInv_of_fullPropagate {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlmrk : s'.core.lit_mark = s.core.lit_mark)
    (hdense : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 s' := by
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro v hv; rw [hmrk]; exact hsp.2.1.1 v hv
  · intro l hl; rw [hlmrk]; exact hsp.2.1.2 l hl
  · intro r hr hg
    have hr0 : r ∈ fullArenaClauseRefs s := by
      change r ∈ fullArenaClauseRefsCore s.core; rw [← hperm.2.1]; exact hr
    have hg0 : fullArenaClauseGarb s r = false := by
      change fullArenaClauseGarbCore s.core r = false
      rw [← (hperm.2.2 r hr0).2.1]; exact hg
    exact (((hperm.2.2 r hr0).2.2).map (· / 2)).nodup_iff.mpr (hsp.2.2.1 r hr0 hg0)
  · intro i hi
    change (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32) = 0xFFFFFFFF#32 ∨
      (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefsCore s'.core
    rw [hll, hperm.2.1]; exact hsp.2.2.2.1.1 i hi
  · rw [hext]; exact hsp.2.2.2.1.2
  · rw [hdense]; exact hsp.2.2.2.2

theorem fullSparseInv_of_fullBacktrack {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlmrk : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (harl : s'.core.arena_len = s.core.arena_len)
    (hdense : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 s' := by
  have hperm : FullArenaPermEq s.core s'.core := by
    refine ⟨harl, ?_, fun r _ => ⟨?_, ?_, ?_⟩⟩ <;>
      simp [fullArenaClauseRefsCore, fullArenaHdrCore, fullArenaClauseSizeCore,
        fullArenaClauseGarbCore, fullArenaClauseLitsCore, har, harl]
  exact fullSparseInv_of_fullPropagate hsp hlen' hw' hperm hmrk hlmrk hdense hll hext

theorem fullSparseInv_of_otfs_backtrack {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState}
    (hotfs : FullOtfsInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hwt : ∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → 0 ≤ s.core.cur_level →
      FullWitnessInv c F0 F_cur s'.core)
    (hot : ∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → 0 < s.core.cur_level →
      FullWitnessInv c F0 F_cur s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlmrk : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (harl : s'.core.arena_len = s.core.arena_len)
    (hdense : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 s' := by
  have hw' : FullWitnessInv c F0 F_cur s'.core := by
    by_cases hl0 : s.core.cur_level = 0
    · exact hwt F0 F_cur (hotfs.2.1.toWitness_of_level0 hl0) (Nat.zero_le _)
    · exact hot F0 F_cur hotfs.2.1 (Nat.pos_of_ne_zero hl0)
  have hperm : FullArenaPermEq s.core s'.core := by
    refine ⟨harl, ?_, fun r _ => ⟨?_, ?_, ?_⟩⟩ <;>
      simp [fullArenaClauseRefsCore, fullArenaHdrCore, fullArenaClauseSizeCore,
        fullArenaClauseGarbCore, fullArenaClauseLitsCore, har, harl]
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro v hv; rw [hmrk]; exact hotfs.2.2.1.1 v hv
  · intro l hl; rw [hlmrk]; exact hotfs.2.2.1.2 l hl
  · intro r hr hg
    have hr0 : r ∈ fullArenaClauseRefs s := by
      change r ∈ fullArenaClauseRefsCore s.core; rw [← hperm.2.1]; exact hr
    have hg0 : fullArenaClauseGarb s r = false := by
      change fullArenaClauseGarbCore s.core r = false; rw [← (hperm.2.2 r hr0).2.1]; exact hg
    exact (((hperm.2.2 r hr0).2.2).map (· / 2)).nodup_iff.mpr (hotfs.2.2.2.1 r hr0 hg0)
  · intro i hi
    change (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32) = 0xFFFFFFFF#32 ∨
      (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefsCore s'.core
    rw [hll, hperm.2.1]; exact hotfs.2.2.2.2.1.1 i hi
  · rw [hext]; exact hotfs.2.2.2.2.1.2
  · rw [hdense]; exact hotfs.2.2.2.2.2

theorem vals_other_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l v : Nat}
    (hl : l < 2 * k.cur_vars) (hlv : l / 2 = v) (hval0 : k.vals[2 * v]?.getD 0#8 = 0#8) :
    k.vals[l]?.getD 0#8 = 0#8 :=
  (hw.vals_zero_iff hl).mpr (by
    have h2v : 2 * v < 2 * k.cur_vars := by omega
    simpa [hlv, show (2 * v) / 2 = v by omega] using (hw.vals_zero_iff h2v).mp hval0)

theorem trail_end_lt_of_unassigned_var {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {v : Nat}
    (hv : v < k.cur_vars) (hval0 : k.vals[2 * v]?.getD 0#8 = 0#8) :
    k.trail_end < k.cur_vars :=
  hw.trail_end_lt_of_unassigned (by omega) hval0

theorem lucky_decide_preserves_fullSparseInv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {lit : BitVec 32} {v : Nat} (hinv : FullSparseInv c F0 s) (hv_lt : v < s.core.cur_vars)
    (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8) (hlit_v : lit.toNat / 2 = v)
    {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64} {phases' : List (BitVec 8)}
    (hfl_len : flags'.length = c.max_vars) (hph_len : phases'.length = c.max_vars) :
    let nlvl := s.core.cur_level + 1
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl lit
    let s' : FullState :=
      { core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set v 0xFFFFFFFF#32, trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec'
            trail_end := s.core.trail_end + 1, cur_level := nlvl
            unassigned := unas', unflushed := unfl' }
        scratch := { s.scratch with phases := phases' } }
    FullSparseInv c F0 s' ∧ s'.LengthsOk c ∧ s.core.trail_end < s.core.cur_vars ∧
    s.core.cur_level + 1 ≤ c.max_vars ∧ s.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
  intro nlvl ftrl' fdec' s'
  have hcl := hinv.1.lengths.core_ok
  have hsc := hinv.1.lengths.scratch_ok
  obtain ⟨F_cur, hw⟩ := hinv.1.witness
  have hcv_le := hcl.cur_vars_le
  have hte_lt : s.core.trail_end < s.core.cur_vars :=
    trail_end_lt_of_unassigned_var hw hv_lt hval0
  have hcl_lt : s.core.cur_level + 1 ≤ c.max_vars := by have := hw.cur_level_le; omega
  have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
  have hval_lit : s.core.vals[lit.toNat]?.getD 0#8 = 0#8 :=
    vals_other_zero hw hlit_lt hlit_v hval0
  have hnot_v : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    hlit_v ▸ (hw.vals_zero_iff hlit_lt).mp hval_lit
  have hte32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have hcore' : FullCoreInv c F0 s' := by
    have hc0 := chronoAssign_preserves_fullCore hinv.1
      (lit := lit) (rsn := 0xFFFFFFFF#32) (alvl := nlvl) (cur_level' := nlvl)
      (propagated' := s.core.propagated) (flags' := flags') (frame_trail' := ftrl')
      (frame_dec' := fdec') (unassigned' := unas') (unflushed' := unfl')
      (scratch' := { s.scratch with phases := phases' })
      (hsok' := { hsc with phases_len := hph_len }) (hfll := hfl_len)
      (hftl := by simp [ftrl', hcl.frame_trail_len])
      (hfdl := by simp [fdec', hcl.frame_dec_len])
      (hlit := hlit_lt) (hun := hval_lit) (halvl_le := Nat.le_refl _)
      (hprop_le := by have := hcl.propagated_le; omega)
      (hcur_le := by have := hw.cur_level_le; dsimp [nlvl]; omega)
      (hft_lt := fun L hL => by
        by_cases hLn : L = nlvl
        · subst hLn; dsimp [ftrl']
          rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; exact Nat.lt_succ_of_le hcl_lt),
            Option.getD_some, lk_bv32_ofNat_toNat hte32]
          omega
        · dsimp [ftrl']; rw [List.getElem?_set_ne (Ne.symm hLn)]
          exact Nat.le_trans (hw.frame_trail_lt L (by dsimp [nlvl] at hL; omega)) (Nat.le_succ _))
      (hft_mono := fun L1 L2 h12 h2 => by
        by_cases h2n : L2 = nlvl
        · subst h2n; dsimp [ftrl']
          rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; exact Nat.lt_succ_of_le hcl_lt),
            Option.getD_some, lk_bv32_ofNat_toNat hte32]
          by_cases h1n : L1 = nlvl
          · subst h1n
            rw [List.getElem?_set_self
              (by rw [hcl.frame_trail_len]; exact Nat.lt_succ_of_le hcl_lt),
              Option.getD_some, lk_bv32_ofNat_toNat hte32]
            exact Nat.le_refl _
          · rw [List.getElem?_set_ne (Ne.symm h1n)]
            exact hw.frame_trail_lt L1 (by dsimp [nlvl] at h12; omega)
        · dsimp [ftrl']
          have h1n : L1 ≠ nlvl := by dsimp [nlvl]; omega
          rw [List.getElem?_set_ne (Ne.symm h1n), List.getElem?_set_ne (Ne.symm h2n)]
          exact hw.frame_trail_mono L1 L2 h12 (by dsimp [nlvl] at h2; omega))
      (hft_bef := fun L hL1 hL i hi => by
        by_cases hLn : L = nlvl
        · subst hLn; dsimp [ftrl'] at hi
          rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; exact Nat.lt_succ_of_le hcl_lt),
            Option.getD_some, lk_bv32_ofNat_toNat hte32] at hi
          have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
            hlit_v ▸ hnot_v i hi
          simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte, hnv]
          have := hw.lvl_le i hi; dsimp [nlvl]; omega
        · dsimp [ftrl'] at hi; rw [List.getElem?_set_ne (Ne.symm hLn)] at hi
          have hi_te : i < s.core.trail_end :=
            Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L (by dsimp [nlvl] at hL; omega))
          have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
            hlit_v ▸ hnot_v i hi_te
          simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte, hnv]
          exact hw.frame_trail_before_lt L hL1 (by dsimp [nlvl] at hL; omega) i hi)
      (hfd_lt := fun L hL1 hL => by
        by_cases hLn : L = nlvl
        · subst hLn; dsimp [fdec']
          rw [List.getElem?_set_self (by rw [hcl.frame_dec_len]; exact Nat.lt_succ_of_le hcl_lt),
            Option.getD_some]
          exact hlit_lt
        · dsimp [fdec']; rw [List.getElem?_set_ne (Ne.symm hLn)]
          exact hw.frame_dec_lt L hL1 (by dsimp [nlvl] at hL; omega))
      (hlvl_old_le := fun i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
      (hinhab := fun L hL1 hL => by
        by_cases hLn : L = nlvl
        · exact Or.inl hLn
        · exact Or.inr (hw.levels_inhabited L hL1 (by dsimp [nlvl] at hL; omega)))
      (hdec_fresh := fun _ _ i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
      (hl0 := fun h0 => by dsimp [nlvl] at h0; omega)
      (hrsn := fun _ hne => absurd rfl hne)
    simpa [s', hlit_v, ite_eq_right (by dsimp [nlvl]; omega : nlvl ≠ 0)] using hc0
  exact ⟨⟨hcore', hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2⟩,
    hcore'.lengths, hte_lt, hcl_lt, hval_lit⟩

theorem scan_backtrack_unassigned {v cl0 te0 : Nat} {lit : BitVec 32}
    {s_asn s_prop : FullState} {vals_bt : List (BitVec 8)}
    (hlit_v : lit.toNat / 2 = v) (hte_lt : te0 < s_asn.core.trail_end)
    (htrl : s_asn.core.trl[te0]? = some lit)
    (hlvl_v : s_asn.core.lvl[v]?.getD 0#32 = BitVec.ofNat 32 (cl0 + 1))
    (hcl_lt : cl0 + 1 < 2 ^ 32) (htr : FullTrailExt s_asn.core s_prop.core)
    (h2v_lt : 2 * v < 2 * s_prop.core.cur_vars)
    (hbt_vals : ∀ l < 2 * s_prop.core.cur_vars, vals_bt[l]?.getD 0#8 =
      if (s_prop.core.lvl[l / 2]?.getD 0#32).toNat ≤ cl0 then
        s_prop.core.vals[l]?.getD 0#8 else 0#8) :
    vals_bt[2 * v]?.getD 0#8 = 0#8 := by
  have hvb := hbt_vals (2 * v) h2v_lt
  have hdiv : (2 * v) / 2 = v := by omega
  have hlvl_prop : s_prop.core.lvl[v]?.getD 0#32 = BitVec.ofNat 32 (cl0 + 1) := by
    have htr_l := htr.2.2 te0 hte_lt
    simp only [htrl, Option.getD_some, hlit_v] at htr_l
    rw [htr_l, hlvl_v]
  rw [hvb, hdiv, hlvl_prop, lk_bv32_ofNat_toNat hcl_lt]
  simp [show ¬ (cl0 + 1 ≤ cl0) by omega]

theorem decide_nlvl_ok {c : FullCfg} {F0 : CNF Nat} {s : FullState} {v : Nat}
    (hsp : FullSparseInv c F0 s) (hv_lt : v < s.core.cur_vars)
    (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8) :
    s.core.trail_end < s.core.cur_vars ∧
    s.core.cur_level + 1 < 2 ^ 64 ∧ s.core.cur_level + 1 ≤ c.max_vars ∧
    (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat = s.core.cur_level + 1 ∧
    (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat < s.core.frame_trail.length ∧
    (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat < s.core.frame_dec.length ∧
    ¬ ((BitVec.ofNat 64 c.max_vars).toNat <
      (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat) := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hsp.1.lengths.core_ok.cur_vars_le
  obtain ⟨_, hw0⟩ := hsp.1.witness
  have hcl0 := hw0.cur_level_le
  have hte_lt := trail_end_lt_of_unassigned_var hw0 hv_lt hval0
  have hnlvl_lt64 : s.core.cur_level + 1 < 2 ^ 64 := by omega
  have hnlvl_bv : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat = s.core.cur_level + 1 := by
    bv_omega
  have hnlvl_le : s.core.cur_level + 1 ≤ c.max_vars := by omega
  have hft_len : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat < s.core.frame_trail.length := by
    rw [hnlvl_bv, hsp.1.lengths.core_ok.frame_trail_len]; omega
  have hfd_len : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat < s.core.frame_dec.length := by
    rw [hnlvl_bv, hsp.1.lengths.core_ok.frame_dec_len]; omega
  have hnlvl_ne : ¬ ((BitVec.ofNat 64 c.max_vars).toNat <
      (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat) := by
    rw [hnlvl_bv, lk_bv64_ofNat_toNat (by omega)]; omega
  exact ⟨hte_lt, hnlvl_lt64, hnlvl_le, hnlvl_bv, hft_len, hfd_len, hnlvl_ne⟩

/-! ## 4. Shared `M6HdrMem` Call Combinators (`backtrack`, `decide+propagate`, `analyze`) -/

theorem call_backtrack0_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s_init s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (_hext : M6HdrExtOk ext) (hsp : FullSparseInv c F0 s)
    (hfl : s.core.fuel.toNat ≤ s_init.core.fuel.toNat)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m', s'.LengthsOk c → s'.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
      (Arg.var c.hdr, Arg.imm 0, ()) k) m := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hsp.1.lengths.core_ok.cur_vars_le
  have hte_le := hsp.1.lengths.core_ok.trail_end_le
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by have := hw.cur_level_le; omega
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  lk_call hBt
  refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hsp.1.lengths, hcl_lt,
    fun hpos => by
      simp only [Arg.val] at hpos ⊢
      have := hw.cur_level_le; omega,
    hw.trail_lits_lt, hmf,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' hlen' _ _ hcl_eq hps _ _ _
      hwt _ hm' => ?_⟩
  let s' : FullState :=
    { core := { s.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
      scratch := sc' }
  have hcl0' : s'.core.cur_level = 0 := by change cl' = 0; rw [hcl_eq]; simp
  have hw' : FullWitnessInv c F0 F_cur s'.core := hwt F0 F_cur hw (by simp)
  have hsp' : FullSparseInv c F0 s' :=
    fullSparseInv_of_fullBacktrack hsp hlen' hw' rfl rfl rfl rfl rfl hps.1.1 hps.1.2
  exact hk s' m' hlen' hfl hsp' hcl0' (fullM6HdrMem_unfocus hm')

theorem call_backtrack0_otfs_ret2_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s_init s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (_hext : M6HdrExtOk ext) (hotfs : FullOtfsInvW c F0 F_cur s)
    (hfl : s.core.fuel.toNat ≤ s_init.core.fuel.toNat)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ s' m', s'.LengthsOk c → s'.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q (2#64, ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
      (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.ret (Arg.imm 2, ())) m := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hotfs.1.core_ok.cur_vars_le
  have hte_le := hotfs.1.core_ok.trail_end_le
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by have := hotfs.2.1.cur_level_le; omega
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  lk_call hBt
  refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hotfs.1, hcl_lt,
    fun _ => by have := hotfs.2.1.cur_level_le; omega, hotfs.2.1.trail_lits_lt, hmf,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' hlen' _ _ hcl_eq hps _ _ _
      hwt hot hm' => ?_⟩
  let s' : FullState :=
    { core := { s.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
      scratch := sc' }
  have hcl0' : s'.core.cur_level = 0 := by change cl' = 0; rw [hcl_eq]; simp
  have hsp' : FullSparseInv c F0 s' :=
    fullSparseInv_of_otfs_backtrack hotfs hlen'
      (fun F0 Fc hwa _ => hwt F0 Fc hwa (by simp))
      (fun F0 Fc hoa hlt => hot F0 Fc hoa (by simpa [Arg.val] using hlt))
      rfl rfl rfl rfl rfl hps.1.1 hps.1.2
  lk_hfast_nogrp
  exact hQ s' m' hlen' hfl hsp' hcl0' (fullM6HdrMem_unfocus hm')

theorem call_assign_prop_decide_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s_init : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {lit : BitVec 32} {v : Nat} {k_prop : Tup Val [i64] → Expr Val Cont [i64]}
    (hAssign : Γ.Has "full_assign" fullAssignSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hsp : FullSparseInv c F0 s)
    (hfl : s.core.fuel.toNat ≤ s_init.core.fuel.toNat)
    (hv_lt : v < s.core.cur_vars) (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8)
    (hlit_v : lit.toNat / 2 = v)
    (hm : (FullM6HdrMem c ext { s with core := { s.core with
      cur_level := s.core.cur_level + 1
      frame_trail := s.core.frame_trail.set (s.core.cur_level + 1)
        (BitVec.ofNat 32 s.core.trail_end)
      frame_dec := s.core.frame_dec.set (s.core.cur_level + 1) lit } } ⋆ R) m)
    (hK : ∀ (r : BitVec 64) (F_cur : List (List Nat)) (ext' : List (BitVec 64))
      (s_asn s_p : FullState) (mp : Mem 64),
      M6HdrExtOk ext' → s_p.LengthsOk c → FullSparseInv c F0 s_p →
      FullWitnessInv c F0 F_cur s_p.core → s_p.core.cur_level = s.core.cur_level + 1 →
      s_p.core.cur_vars = s.core.cur_vars → s_p.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) → (r = 1#64 → FullConflictOkW F_cur s_p) →
      FullTrailExt s_asn.core s_p.core → s.core.trail_end < s_asn.core.trail_end →
      s_asn.core.trl[s.core.trail_end]? = some lit →
      s_asn.core.lvl[v]?.getD 0#32 = BitVec.ofNat 32 (s.core.cur_level + 1) →
      (FullM6HdrMem c ext' s_p ⋆ R) mp → wp Γ Q X (k_prop (r, ())) mp) :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := []) "full_assign"
      (Arg.var c.hdr, Arg.var lit, Arg.imm 4294967295, ()) fun _ =>
      Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
        (Arg.var c.hdr, ()) k_prop) m := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hsp.1.lengths.core_ok.cur_vars_le
  have hte_le := hsp.1.lengths.core_ok.trail_end_le
  obtain ⟨_, hw0⟩ := hsp.1.witness
  have hcl0 := hw0.cur_level_le
  have hpr0 := lucky_decide_preserves_fullSparseInv hsp hv_lt hval0 hlit_v
    (unas' := 0#64) (unfl' := 0#64)
    (List.length_replicate (n := c.max_vars) (a := (0 : BitVec 32)))
    (List.length_replicate (n := c.max_vars) (a := (0 : BitVec 8)))
  have hte_lt := hpr0.2.2.1
  have hnlvl_le := hpr0.2.2.2.1
  have hval_lit := hpr0.2.2.2.2
  let ftrl' := s.core.frame_trail.set (s.core.cur_level + 1) (BitVec.ofNat 32 s.core.trail_end)
  let fdec' := s.core.frame_dec.set (s.core.cur_level + 1) lit
  let s_dec : FullState :=
    { s with core := { s.core with
      cur_level := s.core.cur_level + 1, frame_trail := ftrl', frame_dec := fdec' } }
  have hdec_len : s_dec.LengthsOk c :=
    { hsp.1.lengths with core_ok := { hsp.1.lengths.core_ok with
      frame_trail_len := by change ftrl'.length = c.max_vars + 1; simp [ftrl',
        hsp.1.lengths.core_ok.frame_trail_len]
      frame_dec_len := by change fdec'.length = c.max_vars + 1; simp [fdec',
        hsp.1.lengths.core_ok.frame_dec_len] } }
  have hcl_lt32 : s_dec.core.cur_level < 2 ^ 32 := by change s.core.cur_level + 1 < 2 ^ 32; omega
  have hnot_pre : ¬ (s_dec.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s_dec.core.trail_end ∨
      s_dec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
    change ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
      s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
    rw [hlit_v, hval_lit]; simp; omega
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  lk_call hAssign
  refine ⟨c, s_dec, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hdec_len, hcl_lt32, hmf, ?_⟩
  have hcl_ne0 : s_dec.core.cur_level ≠ 0 := by change s.core.cur_level + 1 ≠ 0; omega
  dsimp only [vals, Arg.val]
  simp only [hnot_pre, ↓reduceIte, hcl_ne0]
  intro flags' unass' phases' ma hfl_len hph_len hma
  have hpr := lucky_decide_preserves_fullSparseInv hsp hv_lt hval0 hlit_v
    (unas' := unass') (unfl' := s_dec.core.unflushed) hfl_len hph_len
  let s_asn : FullState :=
    { core := { s_dec.core with
        unassigned := unass', unflushed := s_dec.core.unflushed,
        trail_end := s_dec.core.trail_end + 1,
        vals := (s_dec.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 255#8,
        flags := flags',
        lvl := s_dec.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 s_dec.core.cur_level),
        rsns := s_dec.core.rsns.set (lit.toNat / 2) 4294967295#32,
        trl := s_dec.core.trl.set s_dec.core.trail_end lit,
        trail_pos := s_dec.core.trail_pos.set (lit.toNat / 2)
          (BitVec.ofNat 32 s_dec.core.trail_end) }
      scratch := { s_dec.scratch with phases := phases' } }
  have hsp_asn : FullSparseInv c F0 s_asn := by
    simpa only [s_asn, s_dec, ftrl', fdec', hlit_v] using hpr.1
  obtain ⟨F_cur_a, hw_a⟩ := hsp_asn.1.witness
  have hma' := fullM6HdrMem_unfocus hma
  lk_call hProp
  refine ⟨c, F0, F_cur_a, ext, s_asn, R, rfl, hcfg, hext, hsp_asn.1.lengths, hw_a,
    hsp_asn.2.2.2.2, hma', ?_⟩
  dsimp only
  intro r ext' vals' flags'' lvl' rsns' trl' tp' te' prop' unass'' unfl'' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' mp
    hext' _ hlen_p hw_p htr_p _ hperm_p hps_p _ _ _ _ hfl_p hr_or _ h1 _ _ hmp
  let s_p : FullState :=
    { core := { s_asn.core with
        vals := vals', flags := flags'', lvl := lvl', rsns := rsns', trl := trl',
        trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass'',
        unflushed := unfl'', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
        wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
        confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := sc' }
  have hsp_p : FullSparseInv c F0 s_p :=
    fullSparseInv_of_fullPropagate hsp_asn hlen_p hw_p hperm_p rfl rfl rfl hps_p.1.1 hps_p.1.2
  have hte_asn : s.core.trail_end < s_asn.core.trail_end := by
    change s.core.trail_end < s.core.trail_end + 1; omega
  have htrl_asn : s_asn.core.trl[s.core.trail_end]? = some lit := by
    change (s.core.trl.set s.core.trail_end lit)[s.core.trail_end]? = some lit
    rw [List.getElem?_set_self]; have := hsp.1.lengths.core_ok.trl_len; omega
  have hlvl_asn : s_asn.core.lvl[v]?.getD 0#32 = BitVec.ofNat 32 (s.core.cur_level + 1) := by
    change (s.core.lvl.set (lit.toNat / 2)
      (BitVec.ofNat 32 (s.core.cur_level + 1)))[v]?.getD 0#32 = _
    rw [hlit_v, List.getElem?_set_self]; simp
    have := hsp.1.lengths.core_ok.lvl_len; omega
  exact hK r F_cur_a ext' s_asn s_p mp hext' hlen_p hsp_p hw_p rfl rfl
    (Nat.le_trans hfl_p hfl) hr_or (fun hr1 => (h1 hr1).2.2) htr_p hte_asn htrl_asn
    hlvl_asn hmp

theorem scan_ana_branch_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur1 : List (List Nat)} {ext1 : List (BitVec 64)} {s_init s_p1 : FullState}
    {R : Mem 64 → Prop} {mp1 : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jbt : Cont [i64]} {karg : Val i64}
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hAna : Γ.Has "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hsp1 : FullSparseInv c F0 s_p1) (hw1 : FullWitnessInv c F0 F_cur1 s_p1.core)
    (hcl_eq1 : s_p1.core.cur_level = 1) (hcf1 : FullConflictOkW F_cur1 s_p1)
    (hfl_p1 : s_p1.core.fuel.toNat ≤ s_init.core.fuel.toNat)
    (hmp1 : (FullM6HdrMem c ext1 s_p1 ⋆ R) mp1)
    (hret2 : ∀ ext_b (s_b : FullState) mb,
      M6HdrExtOk ext_b → FullSparseInv c F0 s_b → s_b.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (FullM6HdrMem c ext_b s_b ⋆ R) mb →
      wp Γ Q X (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
        (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.ret (Arg.imm 2, ())) mb)
    (hret2_otfs : ∀ ext_b (s_b : FullState) mb,
      M6HdrExtOk ext_b → FullOtfsInvW c F0 F_cur1 s_b →
      s_b.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (FullM6HdrMem c ext_b s_b ⋆ R) mb →
      wp Γ Q X (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
        (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.ret (Arg.imm 2, ())) mb)
    (hunsat : ∀ ext_u (s_u : FullState) mu,
      M6HdrExtOk ext_u → s_u.LengthsOk c → s_u.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      F0.Unsat → (FullM6HdrMem c ext_u s_u ⋆ R) mu → Q (20#64, ()) mu)
    (hJbt : ∀ ext_o (s_o : FullState) mo,
      M6HdrExtOk ext_o → s_o.core.cur_vars = s_p1.core.cur_vars →
      FullSparseInv c F0 s_o → s_o.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (FullM6HdrMem c ext_o s_o ⋆ R) mo → Jbt (karg, ()) mo) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_analyze_m6_hdr"
      (Arg.var c.hdr, ()) fun p_43 =>
      Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_43.fst, Arg.imm 20, ())) fun p_44 =>
        Expr.jnz (Arg.var p_44.fst) (Expr.ret (Arg.imm 20, ()))
          (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_43.fst, Arg.imm 1, ()))
            fun p_45 =>
              Expr.jnz (Arg.var p_45.fst)
                (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
                  (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.ret (Arg.imm 2, ()))
                (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                  (Arg.var c.hdr, ()) fun p_46 =>
                  Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                      (Arg.var p_46.fst, Arg.imm 1, ())) fun p_47 =>
                    Expr.jnz (Arg.var p_47.fst) (Expr.ret (Arg.imm 20, ()))
                      (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                          (Arg.var p_46.fst, Arg.imm 2, ())) fun p_48 =>
                        Expr.jnz (Arg.var p_48.fst)
                          (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
                            (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.ret (Arg.imm 2, ()))
                          (Expr.jump Jbt (Arg.var karg, ())))))) mp1 := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hlen1 := hsp1.1.lengths
  have hcv_le := hlen1.core_ok.cur_vars_le
  have hte_le := hlen1.core_ok.trail_end_le
  have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by have := hw1.cur_level_le; omega
  have hsw1 : FullSparseInvW c F0 F_cur1 s_p1 := ⟨hlen1, hw1, hsp1.2⟩
  have hinv1 : FullM6HdrInvW c F0 F_cur1 ext1 s_p1 := FullM6HdrInvW.mk_inv hcfg hext1 hsw1
  lk_call hAna
  refine m6HdrAnalyzeSpec_of hinv1 hcf1 hmp1
    fun ra ext_a s_a ma hext_a hlen_a hra hcv_a hfl_a _ huns_a hotfs_a h1_a hm_a => ?_
  lk_hfast_nogrp
  · exact hunsat ext_a s_a ma hext_a hlen_a (Nat.le_trans hfl_a hfl_p1) (huns_a ‹_›) hm_a
  · have hra0 : ra = 0#64 := by
      rcases hra with rfl | rfl | rfl <;> first | rfl | contradiction
    exact hret2_otfs ext_a s_a ma hext_a (hotfs_a hra0) (Nat.le_trans hfl_a hfl_p1) hm_a
  · have hra1 : ra = 1#64 := by
      rcases hra with rfl | rfl | rfl <;> first | rfl | contradiction
    obtain ⟨hinv_a, hcl_lt_a⟩ := h1_a hra1
    have hsw_a := hinv_a.sparseW
    have hcl0_a : s_a.core.cur_level = 0 := by omega
    lk_call hProp
    refine ⟨c, F0, F_cur1, ext_a, s_a, R, rfl, hcfg, hext_a, hsw_a.1, hsw_a.2.1,
      hsw_a.2.2.2.2.2, hm_a, ?_⟩
    dsimp only
    intro r3 ext3 vals3 flags3 lvl3 rsns3 trl3 tp3 te3 prop3 unass3 unfl3
      wvec3 arena3 wstk3 wlen3 wu3 fuel3 ctype3 cref3 c03 c13 oom3 sc3 mp3
      hext3 _ hlen3 hw3 _ _ hperm3 hps3 _ _ _ _ hfl3 hr3 _ h1_3 _ _ hmp3
    let s_p3 : FullState :=
      { core := { s_a.core with
          vals := vals3, flags := flags3, lvl := lvl3, rsns := rsns3, trl := trl3,
          trail_pos := tp3, trail_end := te3, propagated := prop3, unassigned := unass3,
          unflushed := unfl3, wvec := wvec3, arena := arena3, wstk := wstk3, wlen := wlen3,
          wusable := wu3, fuel := fuel3, confl_type := ctype3, confl_ref := cref3,
          confl_lit0 := c03, confl_lit1 := c13, oom := oom3 }
        scratch := sc3 }
    have hsp3 : FullSparseInv c F0 s_p3 :=
      fullSparseInv_of_fullPropagate ⟨⟨hsw_a.1, F_cur1, hsw_a.2.1⟩, hsw_a.2.2⟩
        hlen3 hw3 hperm3 rfl rfl rfl hps3.1.1 hps3.1.2
    have hfl_3 : s_p3.core.fuel.toNat ≤ s_init.core.fuel.toNat :=
      Nat.le_trans hfl3 (Nat.le_trans hfl_a hfl_p1)
    lk_hfast_nogrp
    · have hcl0_p3 : s_p3.core.cur_level = 0 := hcl0_a
      have hr3_1 : r3 = 1#64 := by exact Eq.trans ‹r3 = (1 : BitVec 64)› rfl
      exact hunsat ext3 s_p3 mp3 hext3 hlen3 hfl_3
        (level0_unsat_of_conflict_okW (hw := hw3) hcl0_p3 (h1_3 hr3_1).2.2) hmp3
    · exact hret2 ext3 s_p3 mp3 hext3 hsp3 hfl_3 hmp3
    · exact hJbt ext3 s_p3 mp3 hext3 hcv_a hsp3 hfl_3 hmp3

end LeanQbe.T.Examples.Kissat.Proof.Lucky
