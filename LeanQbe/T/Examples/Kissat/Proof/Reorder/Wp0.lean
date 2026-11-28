/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Reorder
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.WpMem
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# WP Proofs for `Src.Reorder` Part 0 (`Proof.Reorder.Wp0`)

Shared pure state, boundedness, and bit-vector index helpers (`RPostOk`, `RRelinkOk`,
`RWsortEq`), together with canonical `Func.wp` proofs for `full_reorder_sift_fid`
(`fullReorderSiftFidSpec`) and `full_reorder_m6` (`fullReorderM6Spec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reorder

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Reorder
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Reorder.ReorderTactics
open Kraken.Bedrock2.Test

/-! ## 1. Pure Reorder State, Boundedness & Arithmetic Helpers -/

@[expose] def RPostOk (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (m' : Mem 64) : Prop :=
  ∃ s' : FullState,
    s'.core = s.core ∧ s'.LengthsOk c ∧ FullExtScratchPres s s' ∧ (FullMem c s' ⋆ R) m'

@[expose] def RRelinkOk (c : FullCfg) (s0 s1 : FullState) (n : Nat) : Prop :=
  s1.core = s0.core ∧ s1.LengthsOk c ∧ FullExtScratchPres s0 s1 ∧
  WsortBounded s1.scratch.wsort n s1.core.cur_vars

@[expose] def RWsortEq (s s1 : FullState) : Prop :=
  s1 = { s with scratch := { s.scratch with wsort := s1.scratch.wsort } }

theorem rw_refl (s : FullState) : RWsortEq s s := by rcases s with ⟨_, ⟨_⟩⟩; rfl

theorem rw_curVars {s s1 : FullState} (h : RWsortEq s s1) :
    s1.core.cur_vars = s.core.cur_vars := by unfold RWsortEq at h; rw [h]

theorem rw_flags {s s1 : FullState} (h : RWsortEq s s1) :
    s1.core.flags.length = s.core.flags.length := by unfold RWsortEq at h; rw [h]

theorem rw_qstamp {s s1 : FullState} (h : RWsortEq s s1) :
    s1.scratch.q_stamp = s.scratch.q_stamp := by unfold RWsortEq at h; rw [h]

theorem rw_set {s s1 : FullState} (h : RWsortEq s s1) (ws : List (BitVec 32)) :
    RWsortEq s { s1 with scratch := { s1.scratch with wsort := ws } } := by
  unfold RWsortEq at h ⊢; rw [h]

theorem rw_lengthsOk {c : FullCfg} {s s1 : FullState} (hlen : s.LengthsOk c)
    (hs1 : RWsortEq s s1) (hwl : s1.scratch.wsort.length = s.scratch.wsort.length) :
    s1.LengthsOk c := by
  unfold RWsortEq at hs1; rw [hs1]
  exact ⟨hlen.core_ok, { hlen.scratch_ok with wsort_len := hwl.trans hlen.scratch_ok.wsort_len }⟩

theorem wb_set {ws : List (BitVec 32)} {n cv idx : Nat}
    (v : BitVec 32) (h : WsortBounded ws n cv) (hv : v.toNat < cv) :
    WsortBounded (ws.set idx v) n cv := by
  intro i hi; by_cases he : i = idx
  · subst he; by_cases hl : i < ws.length
    · rw [List.getElem?_set_self hl, Option.getD_some]; exact hv
    · rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]; exact Nat.zero_lt_of_lt hv
  · rw [List.getElem?_set_ne (Ne.symm he)]; exact h i hi

theorem wb_push {ws : List (BitVec 32)} {n cv : Nat} {v : BitVec 32}
    (h : WsortBounded ws n cv) (hn : n < ws.length) (hv : v.toNat < cv) :
    WsortBounded (ws.set n v) (n + 1) cv := by
  intro i hi; by_cases he : i = n
  · subst he; rw [List.getElem?_set_self hn, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm he)]; exact h i (by omega)

theorem wb_get {ws : List (BitVec 32)} {n cv i : Nat}
    (h : WsortBounded ws n cv) (hi : i < n) (hl : i < ws.length) : (ws[i]'hl).toNat < cv := by
  have h1 := h i hi; rw [List.getElem?_eq_getElem hl, Option.getD_some] at h1; exact h1

theorem wb_swap {ws : List (BitVec 32)} {n cv i j : Nat}
    {vi vj : BitVec 32} (hwb : WsortBounded ws n cv)
    (hvi : vi.toNat < cv) (hvj : vj.toNat < cv) :
    WsortBounded ((ws.set i vi).set j vj) n cv :=
  wb_set _ (wb_set _ hwb hvi) hvj

theorem wb_lift {ws ws' : List (BitVec 32)} {k n cv : Nat}
    (hwb : WsortBounded ws n cv) (hwb' : WsortBounded ws' k cv)
    (hpres : ∀ j, k ≤ j → ws'[j]? = ws[j]?) : WsortBounded ws' n cv := by
  intro j hj; by_cases hjk : j < k
  · exact hwb' j hjk
  · rw [hpres j (Nat.le_of_not_lt hjk)]; exact hwb j hj

theorem wb_shrink {ws : List (BitVec 32)} {k n cv : Nat}
    (hwb : WsortBounded ws n cv) (hk : k ≤ n) : WsortBounded ws k cv :=
  fun j hj => hwb j (Nat.lt_of_lt_of_le hj hk)

theorem rel_of_reorder {c : FullCfg} {s0 s1 : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {n : Nat}
    (hlen0 : s0.LengthsOk c) (hs1 : RWsortEq s0 s1)
    (hwl : s1.scratch.wsort.length = s0.scratch.wsort.length)
    (hwb : WsortBounded s1.scratch.wsort n s0.core.cur_vars)
    (hm : (ReorderMem c s1 wl wr ⋆ R) m) :
    ∃ s2 : FullState, RRelinkOk c s0 s2 n ∧ (FullMem c s2 ⋆ R) m := by
  obtain ⟨tmk, trc, htmk, htrc, hmF⟩ := fullMem_of_reorderMem hm
  have hs1' : s1 = { s0 with scratch := { s0.scratch with wsort := s1.scratch.wsort } } := hs1
  refine ⟨{ s1 with scratch := { s1.scratch with tarjan_mark := tmk, tarjan_reach := trc } },
    ⟨by rw [hs1'], ⟨by rw [hs1']; exact hlen0.core_ok,
      { hlen0.scratch_ok with
        walk_vals_len := by rw [hs1']; exact hlen0.scratch_ok.walk_vals_len
        phases_len := by rw [hs1']; exact hlen0.scratch_ok.phases_len
        phases_target_len := by rw [hs1']; exact hlen0.scratch_ok.phases_target_len
        phases_best_len := by rw [hs1']; exact hlen0.scratch_ok.phases_best_len
        walk_best_len := by rw [hs1']; exact hlen0.scratch_ok.walk_best_len
        heap_len_arr := by rw [hs1']; exact hlen0.scratch_ok.heap_len_arr
        pos_len := by rw [hs1']; exact hlen0.scratch_ok.pos_len
        shrink_stk_len := by rw [hs1']; exact hlen0.scratch_ok.shrink_stk_len
        q_prev_len := by rw [hs1']; exact hlen0.scratch_ok.q_prev_len
        q_next_len := by rw [hs1']; exact hlen0.scratch_ok.q_next_len
        q_stamp_len := by rw [hs1']; exact hlen0.scratch_ok.q_stamp_len
        wsort_len := by simpa using hwl.trans hlen0.scratch_ok.wsort_len
        work_stk1_len := by rw [hs1']; exact hlen0.scratch_ok.work_stk1_len
        work_stk2_len := by rw [hs1']; exact hlen0.scratch_ok.work_stk2_len
        tarjan_mark_len := htmk, tarjan_reach_len := htrc
        score_len := by rw [hs1']; exact hlen0.scratch_ok.score_len
        sim_sig_len := by rw [hs1']; exact hlen0.scratch_ok.sim_sig_len
        glue_used_len := by rw [hs1']; exact hlen0.scratch_ok.glue_used_len
        last_learned_len := by rw [hs1']; exact hlen0.scratch_ok.last_learned_len
        delayed_len_arr := by rw [hs1']; exact hlen0.scratch_ok.delayed_len_arr
        red_refs_len := by rw [hs1']; exact hlen0.scratch_ok.red_refs_len
        extend_stk_len := by rw [hs1']; exact hlen0.scratch_ok.extend_stk_len
        scratch_buf_len := by rw [hs1']; exact hlen0.scratch_ok.scratch_buf_len }⟩,
     ⟨by rw [hs1'], by rw [hs1']⟩, by rw [hs1']; exact hwb⟩, hmF⟩

theorem rel_lengths {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : RRelinkOk c s0 s1 n) :
    s1.core.cur_vars = s0.core.cur_vars ∧ s1.core.vals.length = 2 * c.max_vars ∧
    s1.scratch.wsort.length = 2 * c.max_vars ∧ s1.scratch.q_prev.length = c.max_vars ∧
    s1.scratch.q_next.length = c.max_vars ∧ s1.scratch.q_stamp.length = c.max_vars :=
  ⟨h.1 ▸ rfl, h.2.1.core_ok.vals_len, h.2.1.scratch_ok.wsort_len,
   h.2.1.scratch_ok.q_prev_len, h.2.1.scratch_ok.q_next_len, h.2.1.scratch_ok.q_stamp_len⟩

theorem rel_wsort_get {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : RRelinkOk c s0 s1 n) {i : Nat} (hin : i < n) (hil : i < s1.scratch.wsort.length) :
    (s1.scratch.wsort[i]'hil).toNat < s0.core.cur_vars := by
  have := h.2.2.2 i hin
  rw [List.getElem?_eq_getElem hil, Option.getD_some, h.1] at this; exact this

theorem rel_to_post {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (h : RRelinkOk c s0 s1 n) (hm : (FullMem c s1 ⋆ R) m) :
    RPostOk c s0 R m := ⟨s1, h.1, h.2.1, h.2.2.1, hm⟩

theorem rel_set_qprev {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : RRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    RRelinkOk c s0 { s1 with scratch := { s1.scratch with q_prev := s1.scratch.q_prev.set i v } }
      n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_prev_len := by simp [h.2.1.scratch_ok.q_prev_len] }⟩, h.2.2.1, h.2.2.2⟩

theorem rel_set_qnext {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : RRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    RRelinkOk c s0 { s1 with scratch := { s1.scratch with q_next := s1.scratch.q_next.set i v } }
      n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_next_len := by simp [h.2.1.scratch_ok.q_next_len] }⟩, h.2.2.1, h.2.2.2⟩

theorem rel_set_qstamp {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : RRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    RRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_stamp := s1.scratch.q_stamp.set i v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_stamp_len := by simp [h.2.1.scratch_ok.q_stamp_len] }⟩, h.2.2.1, h.2.2.2⟩

theorem rel_hdr5 {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : RRelinkOk c s0 s1 n) (a b d e f : BitVec 64) :
    RRelinkOk c s0
      { s1 with scratch := { s1.scratch with
          q_first := a, q_last := b, q_search_idx := d, q_search_stamp := e, q_cur_stamp := f } }
      n := ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

theorem rel_hdr3 {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : RRelinkOk c s0 s1 n) (a b d : BitVec 64) :
    RRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_first := a, q_last := b, q_cur_stamp := d } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

theorem rel_hdr2 {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : RRelinkOk c s0 s1 n) (a b : BitVec 64) :
    RRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_search_idx := a, q_search_stamp := b } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

theorem r_zext64_32_lt {x : BitVec 32} {n : Nat} (h : x.toNat < n) :
    (BitVec.setWidth 64 x).toNat < n := by
  have hz : (BitVec.setWidth 64 x).toNat = x.toNat := by bv_omega
  omega

theorem r_child_nat {root n : BitVec 64} (hroot : root.toNat < 2 ^ 29)
    (h : ¬n.toNat ≤ (2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64) :
    ((root <<< 1) + 1#64).toNat < n.toNat := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  have h2 : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
  rw [h1, Nat.mod_eq_of_lt (by omega)] at h; omega

theorem r_ushr1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) :
    (x >>> (1 : Nat)).toNat < n := by
  have : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem r_ushr1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) :
    (x >>> (1 : BitVec 64)).toNat < n := r_ushr1_nat_lt h

theorem r_zext32_ushr1_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    ((BitVec.setWidth 64 x) >>> (1 : BitVec 64)).toNat < n := r_ushr1_bv_lt h

theorem r_zext32_ushr1_nat_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    ((BitVec.setWidth 64 x) >>> (1 : Nat)).toNat < n := r_ushr1_nat_lt h

theorem r_shl1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    (x <<< (1 : Nat)).toNat < 4 * n := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 64)]; omega
  omega

theorem r_shl1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    (x <<< (1 : BitVec 64)).toNat < 4 * n := r_shl1_nat_lt h hn

theorem r_shl1_add1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n)
    (hn : n < 2 ^ 29) : ((x <<< (1 : Nat)) + 1#64).toNat < 4 * n := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 64)]; omega
  have h2 : ((x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
    rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  omega

theorem r_shl1_add1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n)
    (hn : n < 2 ^ 29) : ((x <<< (1 : BitVec 64)) + 1#64).toNat < 4 * n :=
  r_shl1_add1_nat_lt h hn

theorem r_shl1_mul2_nat_lt {x : BitVec 64} {m : Nat}
    (h : x.toNat < m) (hm : m < 2 * 2 ^ 28) : (x <<< (1 : Nat)).toNat < 2 * m := by
  have h64 : x.toNat * 2 < 2 ^ 64 := lt_trans (by omega : x.toNat * 2 < 2 ^ 30) (by decide)
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt h64]; omega
  omega

theorem r_shl1_mul2_bv_lt {x : BitVec 64} {m : Nat}
    (h : x.toNat < m) (hm : m < 2 * 2 ^ 28) : (x <<< (1 : BitVec 64)).toNat < 2 * m :=
  r_shl1_mul2_nat_lt h hm

theorem r_zext32_bv32_ushr1_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    (BitVec.setWidth 64 (x >>> (1 : Nat))).toNat < n := by
  have hz1 : (BitVec.setWidth 64 x).toNat = x.toNat := by bv_omega
  have hz2 : (BitVec.setWidth 64 (x >>> (1 : Nat))).toNat = (x >>> (1 : Nat)).toNat := by
    bv_omega
  have hdiv : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem r_zext32_bv32_ushr1_bv_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    (BitVec.setWidth 64 (x >>> (1 : BitVec 32))).toNat < n := r_zext32_bv32_ushr1_lt h

theorem r_bv64_lt_mod {v : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (h : v.toNat < m % 2 ^ 64) : v.toNat < m := by
  rw [Nat.mod_eq_of_lt (lt_trans hm (by decide))] at h; exact h

theorem r_bv64_lt_two_mul_mod {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 29)
    (h : x.toNat < 2 * (m % 2 ^ 64) % 2 ^ 64) : x.toNat < 2 * m := by
  have hm64 : m < 2 ^ 64 := lt_trans hm (by decide)
  have h2m64 : 2 * m < 2 ^ 64 := lt_trans (Nat.mul_lt_mul_of_pos_left hm (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt h2m64] at h; exact h

theorem r_off3_add {off j : BitVec 64} (ho : off.toNat < 2 ^ 29)
    (hj : j.toNat < 2 ^ 29) :
    ((off + 3#64) + j).toNat = off.toNat + 3 + j.toNat ∧
    (off.toNat + 3 % 2 ^ 64 + j.toNat) % 2 ^ 64 = off.toNat + 3 + j.toNat ∧
    ((off.toNat + 3 % 2 ^ 64) % 2 ^ 64 + j.toNat) % 2 ^ 64 = off.toNat + 3 + j.toNat := by
  have ho64 : off.toNat + 3 < 2 ^ 64 := lt_trans (by omega : off.toNat + 3 < 2 ^ 30) (by decide)
  have hoj64 : off.toNat + 3 + j.toNat < 2 ^ 64 :=
    lt_trans (by omega : off.toNat + 3 + j.toNat < 2 ^ 31) (by decide)
  have h1 : ((off + 3#64) + j).toNat = off.toNat + 3 + j.toNat := by bv_omega
  have hm3 : (3 : Nat) % 2 ^ 64 = 3 := by decide
  rw [hm3, Nat.mod_eq_of_lt ho64, Nat.mod_eq_of_lt hoj64]; exact ⟨h1, rfl, rfl⟩

theorem r_arena_lit_2cv {arena : List (BitVec 32)} {i j cv : Nat}
    (hij : i = j) (hcv : cv < 2 ^ 29) (hi : i < arena.length) (hj : j < arena.length)
    (hc : (arena[j]'hj).toNat < 2 * (cv % 2 ^ 64) % 2 ^ 64) :
    (BitVec.setWidth 64 (arena[i]'hi)).toNat < 2 * cv := by
  subst hij
  have h32 : (arena[i]'hi).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  have hz : (BitVec.setWidth 64 (arena[i]'hi)).toNat = (arena[i]'hi).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32]
  exact hz ▸ r_bv64_lt_two_mul_mod hcv (x := BitVec.setWidth 64 (arena[i]'hi)) (hz ▸ hc)

theorem r_off_bounds {arena_len arena_arr_len : Nat} {off n3 : BitVec 64}
    (har29 : arena_len < 2 ^ 29) (har_le : arena_len ≤ arena_arr_len)
    (h1 : off.toNat < arena_len % 2 ^ 64)
    (h2 : ¬arena_len % 2 ^ 64 < (off.toNat + n3.toNat) % 2 ^ 64) (hn3 : n3.toNat = 3) :
    off.toNat + 3 ≤ arena_len ∧ off.toNat < 2 ^ 29 ∧ (off + 2#64).toNat = off.toNat + 2 ∧
    off.toNat < arena_arr_len ∧ (off + 2#64).toNat < arena_arr_len := by
  have har64 : arena_len < 2 ^ 64 := lt_trans har29 (by decide)
  rw [Nat.mod_eq_of_lt har64] at h1 h2; rw [hn3] at h2
  have ho29 : off.toNat < 2 ^ 29 := Nat.lt_trans h1 har29
  rw [Nat.mod_eq_of_lt (lt_trans (by omega : off.toNat + 3 < 2 ^ 30) (by decide))] at h2
  have hoff3 : off.toNat + 3 ≤ arena_len := Nat.le_of_not_lt h2
  have ho2 : (off + 2#64).toNat = off.toNat + 2 := by
    rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (lt_trans (by omega : off.toNat + 2 < 2 ^ 30) (by decide))]
  exact ⟨hoff3, ho29, ho2, Nat.lt_of_lt_of_le h1 har_le,
    ho2 ▸ Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hoff3 har_le)⟩

theorem r_sz_off3_le {arena : List (BitVec 32)} {arena_len : Nat} {off n2 n3 : BitVec 64}
    (hoff3 : off.toNat + 3 ≤ arena_len) (har29 : arena_len < 2 ^ 29)
    {hi1 : (off.toNat + n2.toNat) % 2 ^ 64 < arena.length}
    (hi2 : (off + 2#64).toNat < arena.length) (ho2 : (off + 2#64).toNat = off.toNat + 2)
    (hle : (arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1).toNat ≤
      (2 ^ 64 - (off.toNat + n3.toNat) % 2 ^ 64 + arena_len) % 2 ^ 64)
    (hn2 : n2.toNat = 2) (hn3 : n3.toNat = 3) :
    off.toNat + 3 + (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat ≤ arena_len ∧
    (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat < 2 ^ 29 := by
  have ho2_64 : off.toNat + 2 < 2 ^ 64 := lt_trans (by omega : off.toNat + 2 < 2 ^ 30) (by decide)
  have ho3_64 : off.toNat + 3 < 2 ^ 64 := lt_trans (by omega : off.toNat + 3 < 2 ^ 30) (by decide)
  have hi_eq : (off.toNat + n2.toNat) % 2 ^ 64 = (off + 2#64).toNat := by
    rw [hn2, ho2, Nat.mod_eq_of_lt ho2_64]
  have helem : arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1 = arena[(off + 2#64).toNat]'hi2 := by
    clear hle; revert hi1; rw [hi_eq]; intro _; rfl
  have hrem29 : arena_len - (off.toNat + 3) < 2 ^ 29 := by omega
  have hrem : arena_len - (off.toNat + 3) < 2 ^ 64 := lt_trans hrem29 (by decide)
  have hrhs : (2 ^ 64 - (off.toNat + n3.toNat) % 2 ^ 64 + arena_len) % 2 ^ 64 =
      arena_len - (off.toNat + 3) := by
    rw [hn3, Nat.mod_eq_of_lt ho3_64,
      show 2 ^ 64 - (off.toNat + 3) + arena_len = (arena_len - (off.toNat + 3)) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hrem]
  rw [helem, hrhs] at hle
  have h32 : (arena[(off + 2#64).toNat]'hi2).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  have hz : (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat =
      (arena[(off + 2#64).toNat]'hi2).toNat := by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32]
  rw [hz]; exact ⟨by omega, by omega⟩

theorem r_arena_k_lt {arena : List (BitVec 32)} {off k n2 : BitVec 64}
    (ho2 : (off + 2#64).toNat = off.toNat + 2) (hoff : off.toNat < 2 ^ 29)
    {hi1 : (off.toNat + n2.toNat) % 2 ^ 64 < arena.length}
    (hi2 : (off + 2#64).toNat < arena.length)
    (hc : k.toNat < (arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1).toNat) (hn2 : n2.toNat = 2) :
    k.toNat < (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat := by
  have ho2_64 : off.toNat + 2 < 2 ^ 64 := lt_trans (by omega : off.toNat + 2 < 2 ^ 30) (by decide)
  have heq : (off.toNat + n2.toNat) % 2 ^ 64 = (off + 2#64).toNat := by
    rw [hn2, ho2, Nat.mod_eq_of_lt ho2_64]
  have helem : arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1 = arena[(off + 2#64).toNat]'hi2 := by
    clear hc; revert hi1; rw [heq]; intro _; rfl
  have h32 : (arena[(off + 2#64).toNat]'hi2).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32, ← helem]; exact hc

theorem r_lt_shl1_ofNat {v : BitVec 64} {m : Nat} (hm : m < 2 ^ 29)
    (h : v.toNat < (BitVec.ofNat 64 m <<< (1 : Nat)).toNat) : v.toNat < 2 * m := by
  have hm64 : m < 2 ^ 64 := lt_trans hm (by decide)
  have h1 : (BitVec.ofNat 64 m <<< (1 : Nat)).toNat = 2 * m := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one]
    rw [Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt (by omega)]; omega
  omega

theorem r_add1 {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30) (hx : x.toNat < m) :
    (x + 1#64).toNat = x.toNat + 1 ∧ (x + 1#64).toNat ≤ m ∧ m - (x + 1#64).toNat < m - x.toNat := by
  have : x.toNat < 2 ^ 64 - 1 := lt_trans hx (lt_trans hm (by decide)); bv_omega

theorem r_add2_sub_lt {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30) (hx : x.toNat < m) :
    m - (x + 2#64).toNat < m - x.toNat := by
  have : x.toNat < 2 ^ 64 - 2 := lt_trans hx (lt_trans hm (by decide)); bv_omega

theorem r_sub1 {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (hx_le : x.toNat ≤ m) (hx_pos : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 ∧ (x - 1#64).toNat < x.toNat ∧
    (x - 1#64).toNat ≤ m ∧ (x - 1#64).toNat < m := by
  have : x.toNat < 2 ^ 64 := lt_of_le_of_lt hx_le (lt_trans hm (by decide)); bv_omega

theorem r_ushr1_le {x : BitVec 64} {m : Nat} (hx : x.toNat ≤ m) :
    (x >>> 1#64).toNat ≤ m := by
  have h1 : (x >>> 1#64).toNat = x.toNat / 2 := by
    change (x >>> (1 : Nat)).toNat = x.toNat / 2
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem r_pos_ne0 {x : BitVec 64} (h : x ≠ 0#64) : 0 < x.toNat := by bv_omega

theorem r_we_le_wlen {ws wc : BitVec 32} {wlen : Nat}
    (hwl : wlen < 2 ^ 29) (hws : ws.toNat < wlen % 2 ^ 64)
    (hwc : wc.toNat ≤ (2 ^ 64 - ws.toNat + wlen) % 2 ^ 64) :
    ws.toNat ≤ wlen ∧ ((BitVec.setWidth 64 ws) + (BitVec.setWidth 64 wc)).toNat ≤ wlen := by
  have hws' : ws.toNat < wlen := by
    rw [Nat.mod_eq_of_lt (lt_trans hwl (by decide))] at hws; exact hws
  have hsub : (2 ^ 64 - ws.toNat + wlen) % 2 ^ 64 = wlen - ws.toNat := by
    rw [show 2 ^ 64 - ws.toNat + wlen = (wlen - ws.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hwc' : wc.toNat ≤ wlen - ws.toNat := hsub ▸ hwc
  have hz1 : (BitVec.setWidth 64 ws).toNat = ws.toNat := by bv_omega
  have hz2 : (BitVec.setWidth 64 wc).toNat = wc.toNat := by bv_omega
  have hadd : (BitVec.setWidth 64 ws + BitVec.setWidth 64 wc).toNat = ws.toNat + wc.toNat := by
    rw [BitVec.toNat_add, hz1, hz2, Nat.mod_eq_of_lt (by omega)]
  omega

theorem r_call_spec {Γ : Env} {rs as bs : List Ty} {Q : Post rs} {X : XPost}
    {f : Sym} {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {spec : Spec as bs} (hEnv : Γ.Has f spec)
    (hSpec : spec (vals args) m (fun r m' => wp Γ Q X (k r) m') X) :
    wp Γ Q X (.call f args k) m :=
  ⟨fun r m' => wp Γ Q X (k r) m', X, hEnv _ _ _ _ hSpec, fun _ _ h => h, fun _ _ _ _ h => h⟩

/-! ## 2. `full_reorder_sift_fid_wp` (`fullReorderSiftFidSpec`) -/

/-- Canonical `Func.wp` proof for `full_reorder_sift_fid` against `fullReorderSiftFidSpec`. -/
theorem full_reorder_sift_fid_wp (Γ : Env) :
    ∀ a m Q X, siftSpec a m Q X → Func.wp Γ full_reorder_sift_fid_body a m Q X := by
  rintro ⟨h, start, n, ⟨⟩⟩ m Q X hs
  unfold siftSpec at hs
  obtain ⟨⟨c, s, wl, wr⟩, R, ⟨rfl, hlen, hwb⟩, hm, hQ⟩ := FnContract.elim hs
  dsimp only at hlen hwb hm hQ
  have hQ' : ∀ (s1 : FullState) (m1 : Mem 64),
      RWsortEq s s1 → s1.scratch.wsort.length = s.scratch.wsort.length →
      WsortBounded s1.scratch.wsort n.toNat s.core.cur_vars →
      (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) →
      (ReorderMem c s1 wl wr ⋆ R) m1 → Q () m1 :=
    fun s1 m1 hs1_eq hlen1 hwb1 hpres1 hm1 =>
      hQ () s1.scratch.wsort m1 ⟨hlen1, hwb1, hpres1⟩ (hs1_eq ▸ hm1)
  clear hQ
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le; have hcv_29 : s.core.cur_vars < 2 ^ 29 := by omega
  have hws_len := hlen.scratch_ok.wsort_len; have hqs_len := hlen.scratch_ok.q_stamp_len
  unfold Func.wp full_reorder_sift_fid_body
  c0_hsplit
  · c0_hsteps; exact hQ' s m (rw_refl s) rfl hwb (fun _ _ => rfl) hm
  · c0_hsplit
    · c0_hsteps; exact hQ' s m (rw_refl s) rfl hwb (fun _ _ => rfl) hm
    · c0_hsplit
      · c0_hsteps; exact hQ' s m (rw_refl s) rfl hwb (fun _ _ => rfl) hm
      · have hn_pos : 1 ≤ n.toNat := by bv_omega
        have hst_lt : start.toNat < n.toNat := by bv_omega
        have hn_le : n.toNat ≤ s.core.cur_vars := by omega
        c0_hsteps_nogrp
        refine wp_while_break_state (fun root : BitVec 64 => (root, ()))
          (fun _ m1 => ∃ s1 : FullState,
            RWsortEq s s1 ∧ s1.scratch.wsort.length = s.scratch.wsort.length ∧
            WsortBounded s1.scratch.wsort n.toNat s.core.cur_vars ∧
            (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) ∧
            (ReorderMem c s1 wl wr ⋆ R) m1)
          (fun root : BitVec 64 => (root, ())) (fun root => n.toNat - root.toNat)
          (fun root m1 => root.toNat < n.toNat ∧ ∃ s1 : FullState,
            RWsortEq s s1 ∧ s1.scratch.wsort.length = s.scratch.wsort.length ∧
            WsortBounded s1.scratch.wsort n.toNat s.core.cur_vars ∧
            (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) ∧
            (ReorderMem c s1 wl wr ⋆ R) m1)
          (fun B _ m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩ => by
            c0_hsteps; exact hQ' s1 m1 hs1_eq hws1_len hwb1 hpres1 hm1)
          (fun B L root m1 hB hL ⟨hroot, s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩ => ?_)
          (fun B L _ hL => by
            c0_hsteps
            exact hL start m ⟨hst_lt, s, rw_refl s, rfl, hwb, fun _ _ => rfl, hm⟩)
        have hqs1_len : s1.scratch.q_stamp.length = c.max_vars := by
          rw [rw_qstamp hs1_eq]; exact hqs_len
        have hchild_eq : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
        have hroot_lt_ws : root.toNat < s1.scratch.wsort.length := by omega
        have hbv0_lt : (s1.scratch.wsort[root.toNat]'hroot_lt_ws).toNat < s.core.cur_vars :=
          wb_get hwb1 hroot hroot_lt_ws
        have hbv0_mv :
            (BitVec.setWidth 64 (s1.scratch.wsort[root.toNat]'hroot_lt_ws)).toNat < c.max_vars :=
          r_zext64_32_lt (Nat.lt_of_lt_of_le hbv0_lt hcv_le)
        have hbv0_qs : (BitVec.setWidth 64 (s1.scratch.wsort[root.toNat]'hroot_lt_ws)).toNat <
            s1.scratch.q_stamp.length := hqs1_len ▸ hbv0_mv
        c0_hsplit
        · c0_hsplit
          · c0_hsteps; exact hB root m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩
          · have hch_nat : ((root <<< 1) + 1#64).toNat < n.toNat :=
              r_child_nat (by omega) ‹_›
            have hch_lt_ws : ((root <<< 1) + 1#64).toNat < s1.scratch.wsort.length := by omega
            have hcv0_lt : (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws).toNat <
                s.core.cur_vars := wb_get hwb1 hch_nat hch_lt_ws
            have hcv0_mv : (BitVec.setWidth 64
                (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws)).toNat < c.max_vars :=
              r_zext64_32_lt (Nat.lt_of_lt_of_le hcv0_lt hcv_le)
            have hcv0_qs : (BitVec.setWidth 64
                (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws)).toNat <
                s1.scratch.q_stamp.length := hqs1_len ▸ hcv0_mv
            have hrch_eq : ((root <<< 1) + 1#64 + 1#64).toNat = 2 * root.toNat + 2 := by bv_omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i32, i64, i32])
              (fun xs m' => m' = m1 ∧ (xs.1 = root ∨ xs.1 = (root <<< 1) + 1#64) ∧
                xs.1.toNat < n.toNat ∧ xs.2.1.toNat < s.core.cur_vars) ?_ ?_
            · rintro J xs m' ⟨hm_eq, hx_eq, hx_lt, hxv_lt⟩
              subst m'; dsimp only [Blocks.get]; c0_hsteps_nogrp
              refine wp_join_group (ts := [i64, i32])
                (fun ys m'' => m'' = m1 ∧
                  (ys.1 = root ∨ ys.1 = (root <<< 1) + 1#64 ∨ ys.1 = (root <<< 1) + 1#64 + 1#64) ∧
                  ys.1.toNat < n.toNat ∧ ys.2.1.toNat < s.core.cur_vars) ?_ ?_
              · rintro J2 ys m'' ⟨hm_eq', hy_eq, hy_lt, hyv_lt⟩
                subst m''; c0_hsplit
                · c0_hsteps; exact hB _ m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩
                · have hgt : root.toNat < ys.1.toNat := by
                    rcases hy_eq with h1 | h1 | h1
                    · exact absurd h1 (by assumption)
                    · rw [h1, hchild_eq]; omega
                    · rw [h1, hrch_eq]; omega
                  have hys_ws : ys.1.toNat < s1.scratch.wsort.length := by omega
                  have hys_ws' : ys.1.toNat < (s1.scratch.wsort.set root.toNat ys.2.1).length := by
                    simpa using hys_ws
                  c0_hsteps
                  let ws2 := (s1.scratch.wsort.set root.toNat ys.2.1).set ys.1.toNat
                    (s1.scratch.wsort[root.toNat]'hroot_lt_ws)
                  exact hL ys.1 _ (by omega)
                    ⟨hy_lt, { s1 with scratch := { s1.scratch with wsort := ws2 } },
                     rw_set hs1_eq _, by simp [ws2, hws1_len],
                     wb_set _ (wb_set _ hwb1 hyv_lt) hbv0_lt,
                     fun j hj => by
                       dsimp only [ws2]; rw [List.getElem?_set_ne (by omega),
                         List.getElem?_set_ne (by omega)]; exact hpres1 j hj,
                     by assumption⟩
              · intro J2 hJ2; c0_hsplit
                · have hrch_nat : ((root <<< 1) + 1#64 + 1#64).toNat < n.toNat := by
                    clear hB hL hQ' hwb1 hpres1 hm1 hbv0_lt hbv0_mv hbv0_qs
                    clear hcv0_lt hcv0_mv hcv0_qs hx_eq hx_lt hxv_lt
                    have hone : (1 : BitVec 64).toNat = 1 := rfl
                    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                      hone, Nat.shiftLeft_eq, Nat.pow_one, Nat.reducePow, Nat.reduceMod] at *
                    omega
                  have hrch_ws : ((root <<< 1) + 1#64 + 1#64).toNat < s1.scratch.wsort.length := by
                    omega
                  have hrv_lt : (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws).toNat
                      < s.core.cur_vars := wb_get hwb1 hrch_nat hrch_ws
                  have hrv_mv : (BitVec.setWidth 64
                      (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                      c.max_vars := r_zext64_32_lt (Nat.lt_of_lt_of_le hrv_lt hcv_le)
                  have hrv_qs : (BitVec.setWidth 64
                      (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                      s1.scratch.q_stamp.length := hqs1_len ▸ hrv_mv
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64, i32])
                    (fun zs m'' => m'' = m1 ∧
                      (zs.1 = root ∨ zs.1 = (root <<< 1) + 1#64 ∨
                        zs.1 = (root <<< 1) + 1#64 + 1#64) ∧
                      zs.1.toNat < n.toNat ∧ zs.2.1.toNat < s.core.cur_vars)
                    (fun _ _ m'' ⟨hm_z, hz⟩ => by
                      subst m''; dsimp only [Blocks.get]; c0_hsteps; exact hJ2 _ m1 ⟨rfl, hz⟩)
                    (fun J3 hJ3 => by
                      c0_hsteps_nogrp; all_goals
                        refine hJ3 _ m1 ⟨rfl, ?_, ?_, ?_⟩
                        · first | exact Or.inr (Or.inr rfl) | exact hx_eq.imp_right Or.inl
                        · first | exact hrch_nat | exact hx_lt
                        · first | exact hrv_lt | exact hxv_lt)
                · c0_hsteps; exact hJ2 _ m1 ⟨rfl, hx_eq.imp_right Or.inl, hx_lt, hxv_lt⟩
            · intro J1 hJ1; c0_hsteps_nogrp; all_goals
                refine hJ1 _ m1 ⟨rfl, ?_, ?_, ?_⟩
                · first | exact Or.inl rfl | exact Or.inr rfl
                · first | exact hroot | exact hch_nat
                · first | exact hbv0_lt | exact hcv0_lt
        · exact absurd ‹true = false› (by decide)

/-! ## 3. `full_reorder_m6_wp` (`fullReorderM6Spec`) -/

private theorem fid_arenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

/-- Canonical `Func.wp` proof for `full_reorder_m6` against `fullReorderM6Spec`. -/
theorem full_reorder_m6_wp (Γ : Env)
    (hQueue : Γ.Has "full_reorder_queue_m7" queueSpec) :
    ∀ a m Q X, reorderSpec a m Q X → Func.wp Γ full_reorder_m6_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X hs
  unfold reorderSpec at hs
  obtain ⟨c, s, F0, R, rfl, hlen, hsp, hm, hQ⟩ := FullContract.elim hs
  unfold Func.wp full_reorder_m6_body
  c0_hsteps
  · exact hQ (0#64, ()) s m hsp.lengths ⟨hsp, fid_arenaPermEq_refl s.core, rfl, rfl⟩ hm
  · c0_call hQueue
    dsimp only [queueSpec]
    refine FullContract.intro (w := PUnit.unit) hsp.lengths trivial hm ?_
    rintro ⟨r, ⟨⟩⟩ s1 m1 hlen1 ⟨hc1, hpres1⟩ hm1
    have hce1 : s1.core = s.core := hc1
    c0_hsteps
    exact hQ (r, ()) s1 m1 hlen1
      ⟨fullSparseInv_of_core_eq hsp hlen1 hce1 hpres1,
       hce1 ▸ fid_arenaPermEq_refl s.core, by rw [hce1], by rw [hce1]⟩ hm1

end LeanQbe.T.Examples.Kissat.Proof.Reorder
