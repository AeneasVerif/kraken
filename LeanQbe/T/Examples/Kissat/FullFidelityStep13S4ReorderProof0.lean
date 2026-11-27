/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorder
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorderProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4ReorderMemProof
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-A Proofs — `full_reorder_queue_m7` (`fullReorderQueueSpec`)

UNSAT-only, callee-parametric `Func.wp` proof (`public section`, `0` `@[expose]` on theorems,
`0` `import all`, `XPost`-polymorphic) for Step-13 `full_reorder_queue_m7`, directly certifying
canonical `FullM4Ternary.fullReorderQueueSpec`.

Split into modular `<= 250`-line sub-proofs (P1–P4 + main):
- P1 (`s13_reorder_stable_wp`): `h->stable != 0` branch (`full_rescale`, collect active vars into
  `wsort`, inline heapsort on `wsort`, `f64u_add` + `full_heap_up`).
- P2 (`s13_reorder_phase2_wp`): `h->stable == 0` VMTF queue relinking.
- P3 (`s13_reorder_focus_wp`): `h->stable == 0` collect + heapsort (`full_reorder_sift_fid`).
- P4 (`s13_reorder_loop34_wp`): binary watches weight loop (`f64u_add`), `wl`/`wr` fold loop
  (`f64u_mul`/`f64u_add`), and `h->stable` dispatch.
- Main (`full_reorder_queue_m7_step13_wp`): zero `wl`/`wr` + arena clause weight loop (`f64u_add`,
  `full_arena_next`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Ternary
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullFidelityStep13S4.S13ReorderTactics
open Kraken.Bedrock2.Test

/-! ## 1. `S13ReorderMem` <-> `FullMem` Bridge & Pure Helpers -/

@[expose] def S13RPostOk (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (m' : Mem 64) : Prop :=
  ∃ s' : FullState,
    s'.core = s.core ∧ s'.LengthsOk c ∧ FullExtScratchPres s s' ∧ (FullMem c s' ⋆ R) m'

@[expose] def S13RRelinkOk (c : FullCfg) (s0 s1 : FullState) (n : Nat) : Prop :=
  s1.core = s0.core ∧ s1.LengthsOk c ∧ FullExtScratchPres s0 s1 ∧
  S13WsortBounded s1.scratch.wsort n s1.core.cur_vars

@[expose] def S13RWsortEq (s s1 : FullState) : Prop :=
  s1 = { s with scratch := { s.scratch with wsort := s1.scratch.wsort } }

theorem s13rw_refl (s : FullState) : S13RWsortEq s s := by rcases s with ⟨_, ⟨_⟩⟩; rfl
theorem s13rw_curVars {s s1 : FullState} (h : S13RWsortEq s s1) :
    s1.core.cur_vars = s.core.cur_vars := by unfold S13RWsortEq at h; rw [h]
theorem s13rw_flags {s s1 : FullState} (h : S13RWsortEq s s1) :
    s1.core.flags.length = s.core.flags.length := by unfold S13RWsortEq at h; rw [h]
theorem s13rw_set {s s1 : FullState} (h : S13RWsortEq s s1) (ws : List (BitVec 32)) :
    S13RWsortEq s { s1 with scratch := { s1.scratch with wsort := ws } } := by
  unfold S13RWsortEq at h ⊢; rw [h]
theorem s13rw_lengthsOk {c : FullCfg} {s s1 : FullState} (hlen : s.LengthsOk c)
    (hs1 : S13RWsortEq s s1) (hwl : s1.scratch.wsort.length = s.scratch.wsort.length) :
    s1.LengthsOk c := by
  unfold S13RWsortEq at hs1; rw [hs1]
  exact ⟨hlen.core_ok, { hlen.scratch_ok with wsort_len := hwl.trans hlen.scratch_ok.wsort_len }⟩

theorem s13wb_set {ws : List (BitVec 32)} {n cv idx : Nat}
    (v : BitVec 32) (h : S13WsortBounded ws n cv) (hv : v.toNat < cv) :
    S13WsortBounded (ws.set idx v) n cv := by
  intro i hi; by_cases he : i = idx
  · subst he; by_cases hl : i < ws.length
    · rw [List.getElem?_set_self hl, Option.getD_some]; exact hv
    · rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]; exact Nat.zero_lt_of_lt hv
  · rw [List.getElem?_set_ne (Ne.symm he)]; exact h i hi

theorem s13wb_push {ws : List (BitVec 32)} {n cv : Nat} {v : BitVec 32}
    (h : S13WsortBounded ws n cv) (hn : n < ws.length) (hv : v.toNat < cv) :
    S13WsortBounded (ws.set n v) (n + 1) cv := by
  intro i hi; by_cases he : i = n
  · subst he; rw [List.getElem?_set_self hn, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm he)]; exact h i (by omega)

theorem s13wb_get {ws : List (BitVec 32)} {n cv i : Nat}
    (h : S13WsortBounded ws n cv) (hi : i < n) (hl : i < ws.length) : (ws[i]'hl).toNat < cv := by
  have h1 := h i hi; rw [List.getElem?_eq_getElem hl, Option.getD_some] at h1; exact h1

theorem s13wb_swap {ws : List (BitVec 32)} {n cv i j : Nat}
    {vi vj : BitVec 32} (hwb : S13WsortBounded ws n cv)
    (hvi : vi.toNat < cv) (hvj : vj.toNat < cv) :
    S13WsortBounded ((ws.set i vi).set j vj) n cv :=
  s13wb_set _ (s13wb_set _ hwb hvi) hvj

theorem s13wb_lift {ws ws' : List (BitVec 32)} {k n cv : Nat}
    (hwb : S13WsortBounded ws n cv) (hwb' : S13WsortBounded ws' k cv)
    (hpres : ∀ j, k ≤ j → ws'[j]? = ws[j]?) : S13WsortBounded ws' n cv := by
  intro j hj; by_cases hjk : j < k
  · exact hwb' j hjk
  · rw [hpres j (Nat.le_of_not_lt hjk)]; exact hwb j hj

theorem s13wb_shrink {ws : List (BitVec 32)} {k n cv : Nat}
    (hwb : S13WsortBounded ws n cv) (hk : k ≤ n) : S13WsortBounded ws k cv :=
  fun j hj => hwb j (Nat.lt_of_lt_of_le hj hk)

theorem s13rel_of_reorder {c : FullCfg} {s0 s1 : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {n : Nat}
    (hlen0 : s0.LengthsOk c) (hs1 : S13RWsortEq s0 s1)
    (hwl : s1.scratch.wsort.length = s0.scratch.wsort.length)
    (hwb : S13WsortBounded s1.scratch.wsort n s0.core.cur_vars)
    (hm : (S13ReorderMem c s1 wl wr ⋆ R) m) :
    ∃ s2 : FullState, S13RRelinkOk c s0 s2 n ∧ (FullMem c s2 ⋆ R) m := by
  obtain ⟨tmk, trc, htmk, htrc, hmF⟩ := s13r_fullMem_of_reorderMem hm
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

theorem s13rel_lengths {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : S13RRelinkOk c s0 s1 n) :
    s1.core.cur_vars = s0.core.cur_vars ∧ s1.core.vals.length = 2 * c.max_vars ∧
    s1.scratch.wsort.length = 2 * c.max_vars ∧ s1.scratch.q_prev.length = c.max_vars ∧
    s1.scratch.q_next.length = c.max_vars ∧ s1.scratch.q_stamp.length = c.max_vars :=
  ⟨h.1 ▸ rfl, h.2.1.core_ok.vals_len, h.2.1.scratch_ok.wsort_len,
   h.2.1.scratch_ok.q_prev_len, h.2.1.scratch_ok.q_next_len, h.2.1.scratch_ok.q_stamp_len⟩

theorem s13rel_wsort_get {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : S13RRelinkOk c s0 s1 n) {i : Nat} (hin : i < n) (hil : i < s1.scratch.wsort.length) :
    (s1.scratch.wsort[i]'hil).toNat < s0.core.cur_vars := by
  have := h.2.2.2 i hin
  rw [List.getElem?_eq_getElem hil, Option.getD_some, h.1] at this; exact this

theorem s13rel_to_post {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (h : S13RRelinkOk c s0 s1 n) (hm : (FullMem c s1 ⋆ R) m) :
    S13RPostOk c s0 R m := ⟨s1, h.1, h.2.1, h.2.2.1, hm⟩

theorem s13rel_set_qprev {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : S13RRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    S13RRelinkOk c s0 { s1 with scratch := { s1.scratch with q_prev := s1.scratch.q_prev.set i v } }
      n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_prev_len := by simp [h.2.1.scratch_ok.q_prev_len] }⟩, h.2.2.1, h.2.2.2⟩
theorem s13rel_set_qnext {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : S13RRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    S13RRelinkOk c s0 { s1 with scratch := { s1.scratch with q_next := s1.scratch.q_next.set i v } }
      n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_next_len := by simp [h.2.1.scratch_ok.q_next_len] }⟩, h.2.2.1, h.2.2.2⟩
theorem s13rel_set_qstamp {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : S13RRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    S13RRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_stamp := s1.scratch.q_stamp.set i v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_stamp_len := by simp [h.2.1.scratch_ok.q_stamp_len] }⟩, h.2.2.1, h.2.2.2⟩
theorem s13rel_hdr5 {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : S13RRelinkOk c s0 s1 n) (a b d e f : BitVec 64) :
    S13RRelinkOk c s0
      { s1 with scratch := { s1.scratch with
          q_first := a, q_last := b, q_search_idx := d, q_search_stamp := e, q_cur_stamp := f } }
      n := ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩
theorem s13rel_hdr3 {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : S13RRelinkOk c s0 s1 n) (a b d : BitVec 64) :
    S13RRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_first := a, q_last := b, q_cur_stamp := d } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩
theorem s13rel_hdr2 {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : S13RRelinkOk c s0 s1 n) (a b : BitVec 64) :
    S13RRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_search_idx := a, q_search_stamp := b } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

theorem s13r_zext64_32_lt {x : BitVec 32} {n : Nat} (h : x.toNat < n) :
    (BitVec.setWidth 64 x).toNat < n := by
  have hz : (BitVec.setWidth 64 x).toNat = x.toNat := by bv_omega
  omega
theorem s13r_child_nat {root n : BitVec 64} (hroot : root.toNat < 2 ^ 29)
    (h : ¬n.toNat ≤ (2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64) :
    ((root <<< 1) + 1#64).toNat < n.toNat := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  have h2 : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
  rw [h1, Nat.mod_eq_of_lt (by omega)] at h; omega
theorem s13r_ushr1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) :
    (x >>> (1 : Nat)).toNat < n := by
  have : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega
theorem s13r_ushr1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) :
    (x >>> (1 : BitVec 64)).toNat < n := s13r_ushr1_nat_lt h
theorem s13r_zext32_ushr1_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    ((BitVec.setWidth 64 x) >>> (1 : BitVec 64)).toNat < n := s13r_ushr1_bv_lt h
theorem s13r_zext32_ushr1_nat_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    ((BitVec.setWidth 64 x) >>> (1 : Nat)).toNat < n := s13r_ushr1_nat_lt h
theorem s13r_shl1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    (x <<< (1 : Nat)).toNat < 4 * n := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 64)]; omega
  omega
theorem s13r_shl1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    (x <<< (1 : BitVec 64)).toNat < 4 * n := s13r_shl1_nat_lt h hn
theorem s13r_shl1_add1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n)
    (hn : n < 2 ^ 29) : ((x <<< (1 : Nat)) + 1#64).toNat < 4 * n := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 64)]; omega
  have h2 : ((x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
    rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  omega
theorem s13r_shl1_add1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n)
    (hn : n < 2 ^ 29) : ((x <<< (1 : BitVec 64)) + 1#64).toNat < 4 * n :=
  s13r_shl1_add1_nat_lt h hn
theorem s13r_shl1_mul2_nat_lt {x : BitVec 64} {m : Nat}
    (h : x.toNat < m) (hm : m < 2 * 2 ^ 28) : (x <<< (1 : Nat)).toNat < 2 * m := by
  have h64 : x.toNat * 2 < 2 ^ 64 := lt_trans (by omega : x.toNat * 2 < 2 ^ 30) (by decide)
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt h64]; omega
  omega
theorem s13r_shl1_mul2_bv_lt {x : BitVec 64} {m : Nat}
    (h : x.toNat < m) (hm : m < 2 * 2 ^ 28) : (x <<< (1 : BitVec 64)).toNat < 2 * m :=
  s13r_shl1_mul2_nat_lt h hm
theorem s13r_zext32_bv32_ushr1_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    (BitVec.setWidth 64 (x >>> (1 : Nat))).toNat < n := by
  have hz1 : (BitVec.setWidth 64 x).toNat = x.toNat := by bv_omega
  have hz2 : (BitVec.setWidth 64 (x >>> (1 : Nat))).toNat = (x >>> (1 : Nat)).toNat := by bv_omega
  have hdiv : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega
theorem s13r_zext32_bv32_ushr1_bv_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    (BitVec.setWidth 64 (x >>> (1 : BitVec 32))).toNat < n := s13r_zext32_bv32_ushr1_lt h

theorem s13r_bv64_lt_mod {v : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (h : v.toNat < m % 2 ^ 64) : v.toNat < m := by
  rw [Nat.mod_eq_of_lt (lt_trans hm (by decide))] at h; exact h
theorem s13r_bv64_lt_two_mul_mod {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 29)
    (h : x.toNat < 2 * (m % 2 ^ 64) % 2 ^ 64) : x.toNat < 2 * m := by
  have hm64 : m < 2 ^ 64 := lt_trans hm (by decide)
  have h2m64 : 2 * m < 2 ^ 64 := lt_trans (Nat.mul_lt_mul_of_pos_left hm (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt h2m64] at h; exact h
theorem s13r_off3_add {off j : BitVec 64} (ho : off.toNat < 2 ^ 29)
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
theorem s13r_arena_lit_2cv {arena : List (BitVec 32)} {i j cv : Nat}
    (hij : i = j) (hcv : cv < 2 ^ 29) (hi : i < arena.length) (hj : j < arena.length)
    (hc : (arena[j]'hj).toNat < 2 * (cv % 2 ^ 64) % 2 ^ 64) :
    (BitVec.setWidth 64 (arena[i]'hi)).toNat < 2 * cv := by
  subst hij
  have h32 : (arena[i]'hi).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  have hz : (BitVec.setWidth 64 (arena[i]'hi)).toNat = (arena[i]'hi).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32]
  exact hz ▸ s13r_bv64_lt_two_mul_mod hcv (x := BitVec.setWidth 64 (arena[i]'hi)) (hz ▸ hc)

theorem s13r_off_bounds {arena_len arena_arr_len : Nat} {off n3 : BitVec 64}
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

theorem s13r_sz_off3_le {arena : List (BitVec 32)} {arena_len : Nat} {off n2 n3 : BitVec 64}
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

theorem s13r_arena_k_lt {arena : List (BitVec 32)} {off k n2 : BitVec 64}
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

theorem s13r_lt_shl1_ofNat {v : BitVec 64} {m : Nat} (hm : m < 2 ^ 29)
    (h : v.toNat < (BitVec.ofNat 64 m <<< (1 : Nat)).toNat) : v.toNat < 2 * m := by
  have hm64 : m < 2 ^ 64 := lt_trans hm (by decide)
  have h1 : (BitVec.ofNat 64 m <<< (1 : Nat)).toNat = 2 * m := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one]
    rw [Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt (by omega)]; omega
  omega
theorem s13r_add1 {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30) (hx : x.toNat < m) :
    (x + 1#64).toNat = x.toNat + 1 ∧ (x + 1#64).toNat ≤ m ∧ m - (x + 1#64).toNat < m - x.toNat := by
  have : x.toNat < 2 ^ 64 - 1 := lt_trans hx (lt_trans hm (by decide)); bv_omega
theorem s13r_add2_sub_lt {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30) (hx : x.toNat < m) :
    m - (x + 2#64).toNat < m - x.toNat := by
  have : x.toNat < 2 ^ 64 - 2 := lt_trans hx (lt_trans hm (by decide)); bv_omega
theorem s13r_sub1 {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (hx_le : x.toNat ≤ m) (hx_pos : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 ∧ (x - 1#64).toNat < x.toNat ∧
    (x - 1#64).toNat ≤ m ∧ (x - 1#64).toNat < m := by
  have : x.toNat < 2 ^ 64 := lt_of_le_of_lt hx_le (lt_trans hm (by decide)); bv_omega
theorem s13r_ushr1_le {x : BitVec 64} {m : Nat} (hx : x.toNat ≤ m) :
    (x >>> 1#64).toNat ≤ m := by
  have h1 : (x >>> 1#64).toNat = x.toNat / 2 := by
    change (x >>> (1 : Nat)).toNat = x.toNat / 2
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega
theorem s13r_pos_ne0 {x : BitVec 64} (h : x ≠ 0#64) : 0 < x.toNat := by bv_omega
theorem s13r_we_le_wlen {ws wc : BitVec 32} {wlen : Nat}
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

theorem s13r_call_spec {Γ : Env} {rs as bs : List Ty} {Q : Post rs} {X : XPost}
    {f : Sym} {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {spec : Spec as bs} (hEnv : EnvSpec Γ f spec)
    (hSpec : spec (vals args) m (fun r m' => wp Γ Q X (k r) m') X) :
    wp Γ Q X (.call f args k) m :=
  ⟨fun r m' => wp Γ Q X (k r) m', X, hEnv _ _ _ _ hSpec, fun _ _ h => h, fun _ _ _ _ h => h⟩

/-! ## 2. Sub-Expression Projections of `full_reorder_queue_m7_body` -/

@[expose] def s13rDummyVal : (t : Ty) → Val t
  | .bool => false
  | .bits n => BitVec.zero n
  | .float f => BitVec.zero f.width
  | .pair a b => (s13rDummyVal a, s13rDummyVal b)

@[expose] def s13rDummyTup : (ts : List Ty) → Tup Val ts
  | [] => ()
  | t :: ts => (s13rDummyVal t, s13rDummyTup ts)

@[expose] def s13rSkipLets {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | fuel + 1, .let_ (ts := ts) _ k => s13rSkipLets fuel (k (s13rDummyTup ts))
  | _, e => e

@[expose] def s13rSkip {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | fuel + 1, .let_ (ts := ts) _ k => s13rSkip fuel (k (s13rDummyTup ts))
  | fuel + 1, .load t _ k => s13rSkip fuel (k (s13rDummyVal t))
  | _, e => e

@[expose] def s13rLoad64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v
  | _ => .hlt

@[expose] def s13rLet64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 64]) _ k => k (v, ())
  | _ => .hlt

@[expose] def s13rGrp0Exit {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bodies _ =>
    match bodies (fun _ _ => False, ()) with
    | .cons f .nil => f ()
  | _ => .hlt

@[expose] def s13rGrp1Exit {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64]]) bodies _ =>
    match bodies (fun _ _ => False, ()) with
    | .cons f .nil => f (0#64, ())
  | _ => .hlt

@[expose] def s13rGrp2Exit {rs : List Ty} (n : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64]]) bodies _ =>
    match bodies (fun _ _ => False, ()) with
    | .cons f .nil => f (n, 0#64, ())
  | _ => .hlt

@[expose] def s13rThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t
  | _ => .hlt

@[expose] def s13rElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e
  | _ => .hlt

@[expose] def s13rNextLoad64 {rs : List Ty} (v : Val i64) (e : Expr Val Cont rs) :
    Expr Val Cont rs :=
  s13rLoad64 v (s13rSkipLets 10 e)

@[expose] def s13rNextLoad64Let64 {rs : List Ty} (v lv : Val i64) (e : Expr Val Cont rs) :
    Expr Val Cont rs :=
  s13rLet64 lv (s13rSkipLets 1 (s13rNextLoad64 v e))

@[expose] def s13rSkipWhile1 {rs : List Ty} (e : Expr Val Cont rs) : Expr Val Cont rs :=
  s13rElse (s13rSkip 16 (s13rGrp1Exit (s13rSkip 16 e)))

@[expose] def s13rLoop34Expr (h cv nlits wlen vl fl wvec wstk ws qp qn qs wl wr : Val i64) :
    Expr Val Cont [i64] :=
  full_reorder_queue_m7_body Val Cont (h, ())
    |> s13rNextLoad64Let64 cv nlits
    |> s13rNextLoad64 0#64 |> s13rNextLoad64 wlen |> s13rNextLoad64 vl
    |> s13rNextLoad64 fl
    |> s13rNextLoad64 0#64 |> s13rNextLoad64 wvec |> s13rNextLoad64 wstk
    |> s13rNextLoad64 ws |> s13rNextLoad64 qp |> s13rNextLoad64 qn |> s13rNextLoad64 qs
    |> s13rNextLoad64 wl |> s13rNextLoad64 wr
    |> s13rSkipWhile1
    |> (fun e => s13rGrp1Exit (s13rSkip 16 e))

@[expose] def s13rPost4Expr (h cv vl fl ws qp qn qs wl wr : Val i64) : Expr Val Cont [i64] :=
  s13rLoop34Expr h cv 0#64 0#64 vl fl 0#64 0#64 ws qp qn qs wl wr
    |> s13rSkipWhile1
    |> s13rSkipWhile1

@[expose] def s13rSiftInnerExpr {V : Ty → Type} {C : List Ty → Type}
    (pWs pWl pSc bound : V i64) (B L : C [i64]) (root : V i64) : Expr V C [i64] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .jnz (.imm true)
    (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun s1 =>
     .let_ (op64 (.shl i64) (.var root) (.var s1.fst)) fun s2 =>
     .let_ (op64 (.add i64) (.var s2.fst) (.imm 1)) fun ch =>
     .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var ch.fst, .var bound, ())) fun c0 =>
     .jnz (.var c0.fst) (.jump B (.var root, ()))
       (.let_ (op64 (.mul i64) (.var root) (.imm 4)) fun a1 =>
        .let_ (op64 (.add i64) (.var pWs) (.var a1.fst)) fun a2 =>
        .load i32 (.var a2.fst) fun bv =>
        .let_ (Op.mk (.zext 32 64) (.var bv, ())) fun a3 =>
        .let_ (op64 (.mul i64) (.var a3.fst) (.imm 8)) fun a4 =>
        .let_ (op64 (.add i64) (.var pWl) (.var a4.fst)) fun a5 =>
        .load i64 (.var a5.fst) fun bw =>
        .let_ (Op.mk (.zext 32 64) (.var bv, ())) fun a6 =>
        .let_ (op64 (.mul i64) (.var a6.fst) (.imm 8)) fun a7 =>
        .let_ (op64 (.add i64) (.var pSc) (.var a7.fst)) fun a8 =>
        .load i64 (.var a8.fst) fun bs =>
        .let_ (op64 (.mul i64) (.var ch.fst) (.imm 4)) fun b1 =>
        .let_ (op64 (.add i64) (.var pWs) (.var b1.fst)) fun b2 =>
        .load i32 (.var b2.fst) fun cv1 =>
        .let_ (Op.mk (.zext 32 64) (.var cv1, ())) fun b3 =>
        .let_ (op64 (.mul i64) (.var b3.fst) (.imm 8)) fun b4 =>
        .let_ (op64 (.add i64) (.var pWl) (.var b4.fst)) fun b5 =>
        .load i64 (.var b5.fst) fun cw =>
        .let_ (Op.mk (.zext 32 64) (.var cv1, ())) fun b6 =>
        .let_ (op64 (.mul i64) (.var b6.fst) (.imm 8)) fun b7 =>
        .let_ (op64 (.add i64) (.var pSc) (.var b7.fst)) fun b8 =>
        .load i64 (.var b8.fst) fun cs =>
        .group (sig := [[i64, i32, i64, i64]]) (fun _ =>
          .cons (fun (xs : Tup V [i64, i32, i64, i64]) =>
            let best1 := xs.fst; let bv1 := xs.snd.fst
            let bw1 := xs.snd.snd.fst; let bs1 := xs.snd.snd.snd.fst
            .let_ (op64 (.add i64) (.var ch.fst) (.imm 1)) fun rch =>
            .group (sig := [[i64, i32]]) (fun _ =>
              .cons (fun (ys : Tup V [i64, i32]) =>
                let best2 := ys.fst; let bv2 := ys.snd.fst
                .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var best2, .var root, ())) fun eqr =>
                .jnz (.var eqr.fst) (.jump B (.var root, ()))
                  (.let_ (op64 (.mul i64) (.var root) (.imm 4)) fun t1 =>
                   .let_ (op64 (.add i64) (.var pWs) (.var t1.fst)) fun t2 =>
                   .load i32 (.var t2.fst) fun tv =>
                   .let_ (op64 (.mul i64) (.var root) (.imm 4)) fun t3 =>
                   .let_ (op64 (.add i64) (.var pWs) (.var t3.fst)) fun t4 =>
                   .store (.var bv2) (.var t4.fst)
                     (.let_ (op64 (.mul i64) (.var best2) (.imm 4)) fun t5 =>
                      .let_ (op64 (.add i64) (.var pWs) (.var t5.fst)) fun t6 =>
                      .store (.var tv) (.var t6.fst) (.jump L (.var best2, ()))))) .nil)
              fun J2 =>
                .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var rch.fst, .var bound, ())) fun cr =>
                .jnz (.var cr.fst)
                  (.let_ (op64 (.mul i64) (.var rch.fst) (.imm 4)) fun d1 =>
                   .let_ (op64 (.add i64) (.var pWs) (.var d1.fst)) fun d2 =>
                   .load i32 (.var d2.fst) fun rv1 =>
                   .let_ (Op.mk (.zext 32 64) (.var rv1, ())) fun d3 =>
                   .let_ (op64 (.mul i64) (.var d3.fst) (.imm 8)) fun d4 =>
                   .let_ (op64 (.add i64) (.var pWl) (.var d4.fst)) fun d5 =>
                   .load i64 (.var d5.fst) fun rw =>
                   .let_ (Op.mk (.zext 32 64) (.var rv1, ())) fun d6 =>
                   .let_ (op64 (.mul i64) (.var d6.fst) (.imm 8)) fun d7 =>
                   .let_ (op64 (.add i64) (.var pSc) (.var d7.fst)) fun d8 =>
                   .load i64 (.var d8.fst) fun rs =>
                   .group (sig := [[i64, i32]]) (fun _ =>
                     .cons (fun (zs : Tup V [i64, i32]) =>
                       .jump J2.fst (.var zs.fst, .var zs.snd.fst, ())) .nil)
                     fun J3 =>
                       .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var rw, .var bw1, ())) fun g1 =>
                       .jnz (.var g1.fst) (.jump J3.fst (.var rch.fst, .var rv1, ()))
                         (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var rw, .var bw1, ())) fun g2 =>
                          .jnz (.var g2.fst)
                            (.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var rs, .var bs1, ()))
                               fun g3 =>
                             .jnz (.var g3.fst) (.jump J3.fst (.var rch.fst, .var rv1, ()))
                               (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var rs, .var bs1, ()))
                                 fun g4 =>
                                .jnz (.var g4.fst)
                                  (.let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var rv1, .var bv1, ()))
                                    fun g5 =>
                                   .jnz (.var g5.fst) (.jump J3.fst (.var rch.fst, .var rv1, ()))
                                     (.jump J3.fst (.var best1, .var bv1, ())))
                                  (.jump J3.fst (.var best1, .var bv1, ()))))
                            (.jump J3.fst (.var best1, .var bv1, ()))))
                  (.jump J2.fst (.var best1, .var bv1, ()))) .nil)
          fun J1 =>
            .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var cw, .var bw, ())) fun f1 =>
            .jnz (.var f1.fst) (.jump J1.fst (.var ch.fst, .var cv1, .var cw, .var cs, ()))
              (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var cw, .var bw, ())) fun f2 =>
               .jnz (.var f2.fst)
                 (.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var cs, .var bs, ())) fun f3 =>
                  .jnz (.var f3.fst) (.jump J1.fst (.var ch.fst, .var cv1, .var cw, .var cs, ()))
                    (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var cs, .var bs, ())) fun f4 =>
                     .jnz (.var f4.fst)
                       (.let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var cv1, .var bv, ())) fun f5 =>
                        .jnz (.var f5.fst)
                          (.jump J1.fst (.var ch.fst, .var cv1, .var cw, .var cs, ()))
                          (.jump J1.fst (.var root, .var bv, .var bw, .var bs, ())))
                       (.jump J1.fst (.var root, .var bv, .var bw, .var bs, ()))))
                 (.jump J1.fst (.var root, .var bv, .var bw, .var bs, ())))))
    (.jump B (.var root, ()))

@[expose] def s13rStableExpr (h cv _vl fl ws _qp _qn _qs wl _wr : Val i64) : Expr Val Cont [i64] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
  .call "full_rescale" (as := [i64]) (bs := []) (.var h, ()) fun _ =>
  .let_ (op64 (.add i64) (.var h) (.imm 216)) fun psc =>
  .load i64 (.var psc.fst) fun sc =>
  .group (sig := [[i64, i64]]) (fun Js => .cons (fun (p : Tup Val [i64, i64]) =>
    let n_s := p.fst; let sv := p.snd.fst
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var sv, .var cv, ())) fun c1 =>
    .jnz (.var c1.fst)
      (.group (sig := [[i64]]) (fun _ => .cons (fun (q : Tup Val [i64]) =>
        .let_ (op64 (.add i64) (.var sv) (.imm 1)) fun sv1 =>
        .jump Js.fst (.var q.fst, .var sv1.fst, ())) .nil)
        fun Jn =>
          .let_ (op64 (.mul i64) (.var sv) (.imm 4)) fun pf0 =>
          .let_ (op64 (.add i64) (.var fl) (.var pf0.fst)) fun pf =>
          .load i32 (.var pf.fst) fun flv =>
          .let_ (Op.mk (.and i32) (.var flv, .imm 1, ())) fun fa =>
          .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var fa.fst, .imm 0, ())) fun fc =>
          .jnz (.var fc.fst)
            (.let_ (op64 (.mul i64) (.var n_s) (.imm 4)) fun w1 =>
             .let_ (op64 (.add i64) (.var ws) (.var w1.fst)) fun w2 =>
             .let_ (Op.mk (.trunc 64 32) (.var sv, ())) fun sv32 =>
             .store (.var sv32.fst) (.var w2.fst)
               (.let_ (op64 (.add i64) (.var n_s) (.imm 1)) fun ns1 =>
                .jump Jn.fst (.var ns1.fst, ())))
            (.jump Jn.fst (.var n_s, ())))
      (.group (sig := [[]]) (fun _ => .cons (fun _ =>
        .group (sig := [[i64]]) (fun Jr => .cons (fun (r : Tup Val [i64]) =>
          let rem := r.fst
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var rem, .imm 0, ())) fun cr =>
          .jnz (.var cr.fst)
            (.let_ (op64 (.sub i64) (.var rem) (.imm 1)) fun rem1 =>
             .let_ (op64 (.mul i64) (.var rem1.fst) (.imm 4)) fun r1 =>
             .let_ (op64 (.add i64) (.var ws) (.var r1.fst)) fun r2 =>
             .load i32 (.var r2.fst) fun idx =>
             .let_ (Op.mk (.zext 32 64) (.var idx, ())) fun r3 =>
             .let_ (op64 (.mul i64) (.var r3.fst) (.imm 8)) fun r4 =>
             .let_ (op64 (.add i64) (.var sc) (.var r4.fst)) fun r5 =>
             .let_ (Op.mk (.zext 32 64) (.var idx, ())) fun r6 =>
             .let_ (op64 (.mul i64) (.var r6.fst) (.imm 8)) fun r7 =>
             .let_ (op64 (.add i64) (.var sc) (.var r7.fst)) fun r8 =>
             .load i64 (.var r8.fst) fun sci =>
             .let_ (Op.mk (.zext 32 64) (.var idx, ())) fun r9 =>
             .let_ (op64 (.mul i64) (.var r9.fst) (.imm 8)) fun r10 =>
             .let_ (op64 (.add i64) (.var wl) (.var r10.fst)) fun r11 =>
             .load i64 (.var r11.fst) fun wli =>
             .call "f64u_add" (as := [i64, i64]) (bs := [i64]) (.var sci, .var wli, ()) fun sum =>
             .store (.var sum.fst) (.var r5.fst)
               (.call "full_heap_up" (as := [i64, i32]) (bs := []) (.var h, .var idx, ()) fun _ =>
                .jump Jr.fst (.var rem1.fst, ())))
            (.ret (.var n_s, ()))) .nil)
          fun Jr => .jump Jr.fst (.var n_s, ())) .nil)
        fun J6 =>
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var n_s, .imm 1, ())) fun cn =>
          .jnz (.var cn.fst)
            (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun sh =>
             .let_ (op64 (.lshr i64) (.var n_s) (.var sh.fst)) fun s0 =>
             .group (sig := [[i64]]) (fun Jb => .cons (fun (sb : Tup Val [i64]) =>
               .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var sb.fst, .imm 0, ())) fun cb =>
               .jnz (.var cb.fst)
                 (.let_ (op64 (.sub i64) (.var sb.fst) (.imm 1)) fun sb1 =>
                  .group (sig := [[i64]]) (fun _ => .cons (fun _ =>
                    .jump Jb.fst (.var sb1.fst, ())) .nil)
                    fun JB =>
                      .group (sig := [[i64]]) (fun JL => .cons (fun (rt : Tup Val [i64]) =>
                        s13rSiftInnerExpr ws wl sc n_s JB.fst JL.fst rt.fst) .nil)
                        fun JL => .jump JL.fst (.var sb1.fst, ()))
                 (.group (sig := [[i64]]) (fun Jp => .cons (fun (ep : Tup Val [i64]) =>
                   .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var ep.fst, .imm 1, ())) fun cp =>
                   .jnz (.var cp.fst)
                     (.let_ (op64 (.sub i64) (.var ep.fst) (.imm 1)) fun e1 =>
                      .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun z0 =>
                      .let_ (op64 (.mul i64) (.var z0.fst) (.imm 4)) fun z1 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z1.fst)) fun z2 =>
                      .load i32 (.var z2.fst) fun sw =>
                      .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun z3 =>
                      .let_ (op64 (.mul i64) (.var z3.fst) (.imm 4)) fun z4 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z4.fst)) fun z5 =>
                      .let_ (op64 (.mul i64) (.var e1.fst) (.imm 4)) fun z6 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z6.fst)) fun z7 =>
                      .load i32 (.var z7.fst) fun wse =>
                      .store (.var wse) (.var z5.fst)
                        (.let_ (op64 (.mul i64) (.var e1.fst) (.imm 4)) fun z8 =>
                         .let_ (op64 (.add i64) (.var ws) (.var z8.fst)) fun z9 =>
                         .store (.var sw) (.var z9.fst)
                           (.group (sig := [[i64]]) (fun _ => .cons (fun _ =>
                             .jump Jp.fst (.var e1.fst, ())) .nil)
                             fun JBp =>
                               .group (sig := [[i64]])
                                 (fun JLp => .cons (fun (rt : Tup Val [i64]) =>
                                   s13rSiftInnerExpr ws wl sc e1.fst JBp.fst JLp.fst rt.fst) .nil)
                                 fun JLp => .jump JLp.fst (.imm 0, ()))))
                     (.jump J6.fst ())) .nil)
                   fun Jp => .jump Jp.fst (.var n_s, ()))) .nil)
               fun Jb => .jump Jb.fst (.var s0.fst, ()))
            (.jump J6.fst ()))) .nil)
    fun Js => .jump Js.fst (.imm 0, .imm 0, ())

@[expose] def s13rPhase2Expr (h n cv vl _fl ws qp qn qs _wl _wr : Val i64) : Expr Val Cont [i64] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Jrv => .cons (fun (p : Tup Val [i64]) =>
    let rv := p.fst
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var rv, .var cv, ())) fun c1 =>
    .jnz (.var c1.fst)
      (.let_ (op64 (.mul i64) (.var rv) (.imm 4)) fun a1 =>
       .let_ (op64 (.add i64) (.var qp) (.var a1.fst)) fun a2 =>
       .store (t := i32) (.imm 4294967295) (.var a2.fst)
         (.let_ (op64 (.mul i64) (.var rv) (.imm 4)) fun a3 =>
          .let_ (op64 (.add i64) (.var qn) (.var a3.fst)) fun a4 =>
          .store (t := i32) (.imm 4294967295) (.var a4.fst)
            (.let_ (op64 (.mul i64) (.var rv) (.imm 4)) fun a5 =>
             .let_ (op64 (.add i64) (.var qs) (.var a5.fst)) fun a6 =>
             .store (t := i32) (.imm 0) (.var a6.fst)
               (.let_ (op64 (.add i64) (.var rv) (.imm 1)) fun rv1 =>
                .jump Jrv.fst (.var rv1.fst, ())))))
      (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var n, .imm 0, ())) fun cz =>
       .jnz (.var cz.fst)
         (.let_ (op64 (.add i64) (.var h) (.imm 608)) fun f1 =>
          .store (t := i64) (.imm 4294967295) (.var f1.fst)
            (.let_ (op64 (.add i64) (.var h) (.imm 616)) fun f2 =>
             .store (t := i64) (.imm 4294967295) (.var f2.fst)
               (.let_ (op64 (.add i64) (.var h) (.imm 624)) fun f3 =>
                .store (t := i64) (.imm 4294967295) (.var f3.fst)
                  (.let_ (op64 (.add i64) (.var h) (.imm 640)) fun f4 =>
                   .store (t := i64) (.imm 0) (.var f4.fst)
                     (.let_ (op64 (.add i64) (.var h) (.imm 632)) fun f5 =>
                      .store (t := i64) (.imm 0) (.var f5.fst) (.ret (.imm 0, ())))))))
         (.group (sig := [[i64, i64, i64]]) (fun Jq => .cons (fun (q : Tup Val [i64, i64, i64]) =>
           let sidx := q.fst; let sstamp := q.snd.fst; let qi := q.snd.snd.fst
           .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var qi, .var n, ())) fun cq =>
           .jnz (.var cq.fst)
             (.let_ (op64 (.mul i64) (.var qi) (.imm 4)) fun b1 =>
              .let_ (op64 (.add i64) (.var ws) (.var b1.fst)) fun b2 =>
              .load i32 (.var b2.fst) fun cur =>
              .let_ (Op.mk (.zext 32 64) (.var cur, ())) fun b3 =>
              .let_ (op64 (.mul i64) (.var b3.fst) (.imm 4)) fun b4 =>
              .let_ (op64 (.add i64) (.var qp) (.var b4.fst)) fun b5 =>
              .group (sig := [[i32]]) (fun _ => .cons (fun (pv : Tup Val [i32]) =>
                .store (.var pv.fst) (.var b5.fst)
                  (.let_ (Op.mk (.zext 32 64) (.var cur, ())) fun c2 =>
                   .let_ (op64 (.mul i64) (.var c2.fst) (.imm 4)) fun c3 =>
                   .let_ (op64 (.add i64) (.var qn) (.var c3.fst)) fun c4 =>
                   .group (sig := [[i32]]) (fun _ => .cons (fun (nv : Tup Val [i32]) =>
                     .store (.var nv.fst) (.var c4.fst)
                       (.let_ (Op.mk (.zext 32 64) (.var cur, ())) fun d1 =>
                        .let_ (op64 (.mul i64) (.var d1.fst) (.imm 4)) fun d2 =>
                        .let_ (op64 (.add i64) (.var qs) (.var d2.fst)) fun d3 =>
                        .let_ (op64 (.add i64) (.var qi) (.imm 1)) fun qi1 =>
                        .let_ (Op.mk (.trunc 64 32) (.var qi1.fst, ())) fun qs32 =>
                        .store (.var qs32.fst) (.var d3.fst)
                          (.group (sig := [[i64, i64]]) (fun _ =>
                            .cons (fun (ss : Tup Val [i64, i64]) =>
                              .let_ (op64 (.add i64) (.var qi) (.imm 1)) fun qn1 =>
                              .jump Jq.fst (.var ss.fst, .var ss.snd.fst, .var qn1.fst, ())) .nil)
                            fun Js =>
                              .let_ (Op.mk (.zext 32 64) (.var cur, ())) fun e1 =>
                              .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun e2 =>
                              .let_ (op64 (.shl i64) (.var e1.fst) (.var e2.fst)) fun e3 =>
                              .let_ (op64 (.add i64) (.var vl) (.var e3.fst)) fun e4 =>
                              .load i8 (.var e4.fst) fun v0 =>
                              .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun e5 =>
                              .let_ (Op.mk (.sext 8 32) (.var v0, ())) fun e6 =>
                              .let_ (Op.mk (.sext 8 32) (.var e5.fst, ())) fun e7 =>
                              .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var e6.fst, .var e7.fst, ()))
                                fun e8 =>
                              .jnz (.var e8.fst)
                                (.let_ (Op.mk (.zext 32 64) (.var cur, ())) fun e9 =>
                                 .let_ (op64 (.add i64) (.var qi) (.imm 1)) fun e10 =>
                                 .jump Js.fst (.var e9.fst, .var e10.fst, ()))
                                (.jump Js.fst (.var sidx, .var sstamp, ()))))) .nil)
                     fun Jn =>
                       .let_ (op64 (.add i64) (.var qi) (.imm 1)) fun n1 =>
                       .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var n1.fst, .var n, ())) fun n2 =>
                       .jnz (.var n2.fst)
                         (.let_ (op64 (.add i64) (.var qi) (.imm 1)) fun n3 =>
                          .let_ (op64 (.mul i64) (.var n3.fst) (.imm 4)) fun n4 =>
                          .let_ (op64 (.add i64) (.var ws) (.var n4.fst)) fun n5 =>
                          .load i32 (.var n5.fst) fun wn =>
                          .jump Jn.fst (.var wn, ()))
                         (.jump Jn.fst (.imm 4294967295, ())))) .nil)
                fun Jp =>
                  .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var qi, .imm 0, ())) fun p1 =>
                  .jnz (.var p1.fst)
                    (.let_ (op64 (.sub i64) (.var qi) (.imm 1)) fun p2 =>
                     .let_ (op64 (.mul i64) (.var p2.fst) (.imm 4)) fun p3 =>
                     .let_ (op64 (.add i64) (.var ws) (.var p3.fst)) fun p4 =>
                     .load i32 (.var p4.fst) fun wp =>
                     .jump Jp.fst (.var wp, ()))
                    (.jump Jp.fst (.imm 4294967295, ())))
             (.let_ (op64 (.add i64) (.var h) (.imm 608)) fun g1 =>
              .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun g2 =>
              .let_ (op64 (.mul i64) (.var g2.fst) (.imm 4)) fun g3 =>
              .let_ (op64 (.add i64) (.var ws) (.var g3.fst)) fun g4 =>
              .load i32 (.var g4.fst) fun w0 =>
              .let_ (Op.mk (.zext 32 64) (.var w0, ())) fun g5 =>
              .store (.var g5.fst) (.var g1.fst)
                (.let_ (op64 (.add i64) (.var h) (.imm 616)) fun g6 =>
                 .let_ (op64 (.sub i64) (.var n) (.imm 1)) fun g7 =>
                 .let_ (op64 (.mul i64) (.var g7.fst) (.imm 4)) fun g8 =>
                 .let_ (op64 (.add i64) (.var ws) (.var g8.fst)) fun g9 =>
                 .load i32 (.var g9.fst) fun wl1 =>
                 .let_ (Op.mk (.zext 32 64) (.var wl1, ())) fun g10 =>
                 .store (.var g10.fst) (.var g6.fst)
                   (.let_ (op64 (.add i64) (.var h) (.imm 640)) fun g11 =>
                    .store (.var n) (.var g11.fst)
                      (.group (sig := [[i64, i64]]) (fun _ =>
                        .cons (fun (sf : Tup Val [i64, i64]) =>
                          .let_ (op64 (.add i64) (.var h) (.imm 624)) fun h1 =>
                          .store (.var sf.fst) (.var h1.fst)
                            (.let_ (op64 (.add i64) (.var h) (.imm 632)) fun h2 =>
                             .store (.var sf.snd.fst) (.var h2.fst) (.ret (.var n, ())))) .nil)
                        fun Jf =>
                          .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var sidx, .var cv, ())) fun h3 =>
                          .jnz (.var h3.fst)
                            (.let_ (op64 (.sub i64) (.var n) (.imm 1)) fun h4 =>
                             .let_ (op64 (.mul i64) (.var h4.fst) (.imm 4)) fun h5 =>
                             .let_ (op64 (.add i64) (.var ws) (.var h5.fst)) fun h6 =>
                             .load i32 (.var h6.fst) fun wl2 =>
                             .let_ (Op.mk (.zext 32 64) (.var wl2, ())) fun h7 =>
                             .jump Jf.fst (.var h7.fst, .var n, ()))
                            (.jump Jf.fst (.var sidx, .var sstamp, ()))))))) .nil)
           fun Jq => .jump Jq.fst (.imm 4294967295, .imm 0, .imm 0, ())))) .nil)
    fun Jrv => .jump Jrv.fst (.imm 0, ())

@[expose] def s13rFocusExpr (h cv vl fl ws qp qn qs wl wr : Val i64) : Expr Val Cont [i64] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64]]) (fun Jf => .cons (fun (p : Tup Val [i64, i64]) =>
    let n := p.fst; let av := p.snd.fst
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var av, .var cv, ())) fun c1 =>
    .jnz (.var c1.fst)
      (.group (sig := [[i64]]) (fun _ => .cons (fun (q : Tup Val [i64]) =>
        .let_ (op64 (.add i64) (.var av) (.imm 1)) fun av1 =>
        .jump Jf.fst (.var q.fst, .var av1.fst, ())) .nil)
        fun Jn =>
          .let_ (op64 (.mul i64) (.var av) (.imm 4)) fun pf0 =>
          .let_ (op64 (.add i64) (.var fl) (.var pf0.fst)) fun pf =>
          .load i32 (.var pf.fst) fun flv =>
          .let_ (Op.mk (.and i32) (.var flv, .imm 1, ())) fun fa =>
          .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var fa.fst, .imm 0, ())) fun fc =>
          .jnz (.var fc.fst)
            (.let_ (op64 (.mul i64) (.var n) (.imm 4)) fun w1 =>
             .let_ (op64 (.add i64) (.var ws) (.var w1.fst)) fun w2 =>
             .let_ (Op.mk (.trunc 64 32) (.var av, ())) fun av32 =>
             .store (.var av32.fst) (.var w2.fst)
               (.let_ (op64 (.add i64) (.var n) (.imm 1)) fun n1 =>
                .jump Jn.fst (.var n1.fst, ())))
            (.jump Jn.fst (.var n, ())))
      (.group (sig := [[]]) (fun _ => .cons (fun _ =>
        s13rPhase2Expr h n cv vl fl ws qp qn qs wl wr) .nil)
        fun J6 =>
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var n, .imm 1, ())) fun cn =>
          .jnz (.var cn.fst)
            (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun sh =>
             .let_ (op64 (.lshr i64) (.var n) (.var sh.fst)) fun s0 =>
             .group (sig := [[i64]]) (fun Jb => .cons (fun (sb : Tup Val [i64]) =>
               .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var sb.fst, .imm 0, ())) fun cb =>
               .jnz (.var cb.fst)
                 (.let_ (op64 (.sub i64) (.var sb.fst) (.imm 1)) fun sb1 =>
                  .call "full_reorder_sift_fid" (as := [i64, i64, i64]) (bs := [])
                    (.var h, .var sb1.fst, .var n, ()) fun _ =>
                  .jump Jb.fst (.var sb1.fst, ()))
                 (.group (sig := [[i64]]) (fun Jp => .cons (fun (ep : Tup Val [i64]) =>
                   .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var ep.fst, .imm 1, ())) fun cp =>
                   .jnz (.var cp.fst)
                     (.let_ (op64 (.sub i64) (.var ep.fst) (.imm 1)) fun e1 =>
                      .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun z0 =>
                      .let_ (op64 (.mul i64) (.var z0.fst) (.imm 4)) fun z1 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z1.fst)) fun z2 =>
                      .load i32 (.var z2.fst) fun sw =>
                      .let_ (Op.mk (.sext 32 64) (.imm 0, ())) fun z3 =>
                      .let_ (op64 (.mul i64) (.var z3.fst) (.imm 4)) fun z4 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z4.fst)) fun z5 =>
                      .let_ (op64 (.mul i64) (.var e1.fst) (.imm 4)) fun z6 =>
                      .let_ (op64 (.add i64) (.var ws) (.var z6.fst)) fun z7 =>
                      .load i32 (.var z7.fst) fun wse =>
                      .store (.var wse) (.var z5.fst)
                        (.let_ (op64 (.mul i64) (.var e1.fst) (.imm 4)) fun z8 =>
                         .let_ (op64 (.add i64) (.var ws) (.var z8.fst)) fun z9 =>
                         .store (.var sw) (.var z9.fst)
                           (.call "full_reorder_sift_fid" (as := [i64, i64, i64]) (bs := [])
                             (.var h, .imm 0, .var e1.fst, ()) fun _ =>
                            .jump Jp.fst (.var e1.fst, ()))))
                     (.jump J6.fst ())) .nil)
                   fun Jp => .jump Jp.fst (.var n, ()))) .nil)
               fun Jb => .jump Jb.fst (.var s0.fst, ()))
            (.jump J6.fst ()))) .nil)
    fun Jf => .jump Jf.fst (.imm 0, .imm 0, ())

/-! ## 3. P1: Stable-Mode Reorder Branch (`s13_reorder_sift_inner_wp` & `s13_reorder_stable_wp`) -/

private theorem s13_reorder_sift_inner_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s sF1 sb : FullState} {R : Mem 64 → Prop} {wl1 wr1 : S13Arr64 c.max_vars}
    {n_s bound root : BitVec 64} {B L : Cont [i64]} {mb : Mem 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcv_29 : s.core.cur_vars < 2 ^ 29)
    (hcv_ws : s.core.cur_vars ≤ 2 * c.max_vars)
    (hsc1_len : sF1.scratch.score.length = c.max_vars)
    (hn_cv : n_s.toNat ≤ s.core.cur_vars) (hbd_le : bound.toNat ≤ n_s.toNat)
    (hroot : root.toNat < bound.toNat)
    (hsb_eq : S13RWsortEq sF1 sb) (hwsb : sb.scratch.wsort.length = 2 * c.max_vars)
    (hwb_b : S13WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars)
    (hmb : (S13ReorderMem c sb wl1 wr1 ⋆ R) mb)
    (hB : ∀ r m', (∃ sb' : FullState, S13RWsortEq sF1 sb' ∧
      sb'.scratch.wsort.length = 2 * c.max_vars ∧
      S13WsortBounded sb'.scratch.wsort n_s.toNat s.core.cur_vars ∧
      (S13ReorderMem c sb' wl1 wr1 ⋆ R) m') → B (r, ()) m')
    (hL : ∀ r' m', bound.toNat - r'.toNat < bound.toNat - root.toNat →
      (r'.toNat < bound.toNat ∧ ∃ sb' : FullState, S13RWsortEq sF1 sb' ∧
        sb'.scratch.wsort.length = 2 * c.max_vars ∧
        S13WsortBounded sb'.scratch.wsort n_s.toNat s.core.cur_vars ∧
        (S13ReorderMem c sb' wl1 wr1 ⋆ R) m') → L (r', ()) m') :
    wp Γ Q X (s13rSiftInnerExpr c.pWsort c.pTarjanMark c.pScore bound B L root) mb := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscb_len : sb.scratch.score.length = c.max_vars := by
    unfold S13RWsortEq at hsb_eq; rw [hsb_eq]; exact hsc1_len
  have hch_eq : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
  have hrt_ws : root.toNat < sb.scratch.wsort.length := by omega
  have hbv_lt : (sb.scratch.wsort[root.toNat]'hrt_ws).toNat < s.core.cur_vars :=
    s13wb_get hwb_b (by omega) hrt_ws
  have hbv_mv : (BitVec.setWidth 64 (sb.scratch.wsort[root.toNat]'hrt_ws)).toNat <
      c.max_vars := s13r_zext64_32_lt (Nat.lt_of_lt_of_le hbv_lt hcv_le)
  have hbv_sc : (BitVec.setWidth 64 (sb.scratch.wsort[root.toNat]'hrt_ws)).toNat <
      sb.scratch.score.length := hscb_len ▸ hbv_mv
  dsimp only [s13rSiftInnerExpr]
  c0_hsplit
  · c0_hsplit
    · c0_hsteps; exact hB root mb ⟨sb, hsb_eq, hwsb, hwb_b, hmb⟩
    · have hch_nat : ((root <<< 1) + 1#64).toNat < bound.toNat := s13r_child_nat (by omega) ‹_›
      have hch_ws : ((root <<< 1) + 1#64).toNat < sb.scratch.wsort.length := by omega
      have hcv_lt : (sb.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_ws).toNat <
          s.core.cur_vars := s13wb_get hwb_b (by omega) hch_ws
      have hcv_mv : (BitVec.setWidth 64
          (sb.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_ws)).toNat < c.max_vars :=
        s13r_zext64_32_lt (Nat.lt_of_lt_of_le hcv_lt hcv_le)
      have hcv_sc : (BitVec.setWidth 64
          (sb.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_ws)).toNat <
          sb.scratch.score.length := hscb_len ▸ hcv_mv
      have hrch_eq : ((root <<< 1) + 1#64 + 1#64).toNat = 2 * root.toNat + 2 := by bv_omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i32, i64, i64])
        (fun xs m' => m' = mb ∧ (xs.1 = root ∨ xs.1 = (root <<< 1) + 1#64) ∧
          xs.1.toNat < bound.toNat ∧ xs.2.1.toNat < s.core.cur_vars) ?_ ?_
      · rintro _ xs m' ⟨hm_eq, hx_eq, hx_lt, hxv_lt⟩
        subst m'; dsimp only [Blocks.get]; c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i32])
          (fun ys m'' => m'' = mb ∧
            (ys.1 = root ∨ ys.1 = (root <<< 1) + 1#64 ∨ ys.1 = (root <<< 1) + 1#64 + 1#64) ∧
            ys.1.toNat < bound.toNat ∧ ys.2.1.toNat < s.core.cur_vars) ?_ ?_
        · rintro _ ys m'' ⟨hm_eq', hy_eq, hy_lt, hyv_lt⟩
          subst m''; c0_hsplit
          · c0_hsteps; exact hB _ mb ⟨sb, hsb_eq, hwsb, hwb_b, hmb⟩
          · have hgt : root.toNat < ys.1.toNat := by
              rcases hy_eq with h1 | h1 | h1
              · exact absurd h1 ‹_›
              · rw [h1, hch_eq]; omega
              · rw [h1, hrch_eq]; omega
            have hys_ws : ys.1.toNat < sb.scratch.wsort.length := by omega
            have hys_ws' : ys.1.toNat < (sb.scratch.wsort.set root.toNat ys.2.1).length := by
              simpa using hys_ws
            c0_hsteps
            let ws2 := (sb.scratch.wsort.set root.toNat ys.2.1).set ys.1.toNat
              (sb.scratch.wsort[root.toNat]'hrt_ws)
            exact hL ys.1 _ (by omega)
              ⟨hy_lt, { sb with scratch := { sb.scratch with wsort := ws2 } },
               s13rw_set hsb_eq _, by simp [ws2, hwsb],
               s13wb_swap hwb_b hyv_lt hbv_lt, by assumption⟩
        · intro J2 hJ2; c0_hsplit
          · have hrch_nat : ((root <<< 1) + 1#64 + 1#64).toNat < bound.toNat := by
              clear hB hL hwb_b hmb hbv_lt hbv_mv hbv_sc hcv_lt hcv_mv hcv_sc hx_eq hx_lt hxv_lt
              have hone : (1 : BitVec 64).toNat = 1 := rfl
              simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                hone, Nat.shiftLeft_eq, Nat.pow_one, Nat.reducePow, Nat.reduceMod] at *
              omega
            have hrch_ws : ((root <<< 1) + 1#64 + 1#64).toNat < sb.scratch.wsort.length := by omega
            have hrv_lt : (sb.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws).toNat <
                s.core.cur_vars := s13wb_get hwb_b (by omega) hrch_ws
            have hrv_mv : (BitVec.setWidth 64
                (sb.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                c.max_vars := s13r_zext64_32_lt (Nat.lt_of_lt_of_le hrv_lt hcv_le)
            have hrv_sc : (BitVec.setWidth 64
                (sb.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                sb.scratch.score.length := hscb_len ▸ hrv_mv
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i32])
              (fun zs m'' => m'' = mb ∧
                (zs.1 = root ∨ zs.1 = (root <<< 1) + 1#64 ∨ zs.1 = (root <<< 1) + 1#64 + 1#64) ∧
                zs.1.toNat < bound.toNat ∧ zs.2.1.toNat < s.core.cur_vars)
              (fun _ _ m'' ⟨hm_z, hz⟩ => by
                subst m''; dsimp only [Blocks.get]; c0_hsteps; exact hJ2 _ mb ⟨rfl, hz⟩)
              (fun J3 hJ3 => by
                c0_hsteps_nogrp; all_goals
                  refine hJ3 _ mb ⟨rfl, ?_, ?_, ?_⟩
                  · first | exact Or.inr (Or.inr rfl) | exact hx_eq.imp_right Or.inl
                  · first | exact hrch_nat | exact hx_lt
                  · first | exact hrv_lt | exact hxv_lt)
          · c0_hsteps; exact hJ2 _ mb ⟨rfl, hx_eq.imp_right Or.inl, hx_lt, hxv_lt⟩
      · intro J1 hJ1; c0_hsteps_nogrp; all_goals
          refine hJ1 _ mb ⟨rfl, ?_, ?_, ?_⟩
          · first | exact Or.inl rfl | exact Or.inr rfl
          · first | exact hroot | exact hch_nat
          · first | exact hbv_lt | exact hcv_lt
  · exact absurd ‹true = false› (by decide)

theorem s13_reorder_stable_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {wl4 wr4 : S13Arr64 c.max_vars}
    {m4 : Mem 64}
    (hFadd : EnvSpec Γ "f64u_add" f64uPure2Spec)
    (hRescale : EnvSpec Γ "full_rescale" fullRescaleSpec)
    (hHeapUp : EnvSpec Γ "full_heap_up" fullHeapUpSpec)
    (hlen : s.LengthsOk c) (hQ' : ∀ r m', S13RPostOk c s R m' → Q r m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcv_29 : s.core.cur_vars < 2 ^ 29)
    (hcv_30 : s.core.cur_vars < 2 ^ 30) (hm4 : (S13ReorderMem c s wl4 wr4 ⋆ R) m4) :
    wp Γ Q X (s13rStableExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pVals c.pFlags
      c.pWsort c.pQPrev c.pQNext c.pQStamp c.pTarjanMark c.pTarjanReach) m4 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_ws : s.core.cur_vars ≤ 2 * c.max_vars :=
    Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide))
  dsimp only [s13rStableExpr]
  obtain ⟨tmk0, trc0, htmk0, htrc0, hmF0⟩ := s13r_fullMem_of_reorderMem hm4
  let sF0 : FullState :=
    { s with scratch := { s.scratch with tarjan_mark := tmk0, tarjan_reach := trc0 } }
  have hlenF0 : sF0.LengthsOk c :=
    ⟨hlen.core_ok, { hlen.scratch_ok with tarjan_mark_len := htmk0, tarjan_reach_len := htrc0 }⟩
  c0_call hRescale
  refine ⟨c, sF0, R, rfl, hlenF0, hmF0, fun _ sF1 mF1 hsF1_core hsF1_len hsF1_p hmF1 => ?_⟩
  obtain ⟨wl1, wr1, hm1r⟩ := s13r_reorderMem_of_fullMem hsF1_len hmF1
  have hce1 : sF1.core = s.core := hsF1_core
  have hext1 : FullExtScratchPres s sF1 := hsF1_p.1
  have hfl1_len : sF1.core.flags.length = c.max_vars := hsF1_len.core_ok.flags_len
  have hws1_len : sF1.scratch.wsort.length = 2 * c.max_vars := hsF1_len.scratch_ok.wsort_len
  have hsc1_len : sF1.scratch.score.length = c.max_vars := hsF1_len.scratch_ok.score_len
  c0_hsteps_nogrp
  -- Collect active vars into `ws[0 ..< n_s)`
  refine wp_while_state (fun p : BitVec 64 × BitVec 64 × PUnit => p)
    (fun p => s.core.cur_vars - p.2.1.toNat)
    (fun p m5 => p.2.1.toNat ≤ s.core.cur_vars ∧ p.1.toNat ≤ p.2.1.toNat ∧
      ∃ s5 : FullState, S13RWsortEq sF1 s5 ∧ s5.scratch.wsort.length = 2 * c.max_vars ∧
        S13WsortBounded s5.scratch.wsort p.1.toNat s.core.cur_vars ∧
        (S13ReorderMem c s5 wl1 wr1 ⋆ R) m5)
    (fun J5 hJ5 => by
      c0_hsteps; exact hJ5 (0#64, 0#64, ()) mF1 ⟨Nat.zero_le _, Nat.zero_le _, sF1,
        s13rw_refl sF1, hws1_len, fun _ h => absurd h (Nat.not_lt_zero _), hm1r⟩)
    (fun J5 ⟨n_s, sv, ⟨⟩⟩ m5 ⟨hsv, hn_le, s5, hs5_eq, hws5_len, hwb5, hm5⟩ hJ5 => ?_)
  c0_hsplit
  · have hsv_lt : sv.toNat < s.core.cur_vars := s13r_bv64_lt_mod hcv_30 ‹_›
    have hsv_fl : sv.toNat < s5.core.flags.length :=
      (s13rw_flags hs5_eq).symm ▸ hfl1_len.symm ▸ Nat.lt_of_lt_of_le hsv_lt hcv_le
    have hsvp1 := s13r_add1 hcv_30 hsv_lt
    have hn_lt : n_s.toNat < s.core.cur_vars := Nat.lt_of_le_of_lt hn_le hsv_lt
    have hnp1 := s13r_add1 hcv_30 hn_lt
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun n' m5' => n'.1.toNat ≤ sv.toNat + 1 ∧ ∃ s5' : FullState,
        S13RWsortEq sF1 s5' ∧ s5'.scratch.wsort.length = 2 * c.max_vars ∧
        S13WsortBounded s5'.scratch.wsort n'.1.toNat s.core.cur_vars ∧
        (S13ReorderMem c s5' wl1 wr1 ⋆ R) m5')
      (fun _ ⟨n', ⟨⟩⟩ m5' ⟨hn', s5', hs5', hlen5', hwb5', hm5'⟩ => by
        dsimp only [Blocks.get]; c0_hsteps
        exact hJ5 (n', sv + 1#64, ()) m5' hsvp1.2.2
          ⟨hsvp1.2.1, hsvp1.1 ▸ hn', s5', hs5', hlen5', hwb5', hm5'⟩)
      (fun Jc hJc => ?_)
    c0_hsplit
    · have hn_ws : n_s.toNat < s5.scratch.wsort.length :=
        hws5_len.symm ▸ Nat.lt_of_lt_of_le hn_lt hcv_ws
      have hsv_cv : (BitVec.setWidth 32 sv).toNat < s.core.cur_vars := by
        have : sv.toNat < 2 ^ 32 := lt_trans hsv_lt (lt_trans hcv_29 (by decide))
        have hz : (BitVec.setWidth 32 sv).toNat = sv.toNat := by bv_omega
        omega
      c0_hsteps
      exact hJc (n_s + 1#64, ()) _
        ⟨Nat.le_trans (Nat.le_of_eq hnp1.1) (Nat.succ_le_succ hn_le),
         { s5 with scratch := { s5.scratch with
             wsort := s5.scratch.wsort.set n_s.toNat (BitVec.setWidth 32 sv) } },
         s13rw_set hs5_eq _, by simp [hws5_len],
         hnp1.1 ▸ s13wb_push hwb5 hn_ws hsv_cv, by assumption⟩
    · c0_hsteps; exact hJc (n_s, ()) m5
        ⟨Nat.le_trans hn_le (Nat.le_succ _), s5, hs5_eq, hws5_len, hwb5, hm5⟩
  · have hn_cv : n_s.toNat ≤ s.core.cur_vars := Nat.le_trans hn_le hsv
    have hn_29 : n_s.toNat < 2 ^ 30 := Nat.lt_of_le_of_lt hn_cv (lt_trans hcv_29 (by decide))
    refine wp_join_group (ts := [])
      (fun _ m6 => ∃ s6 : FullState, S13RWsortEq sF1 s6 ∧
        s6.scratch.wsort.length = 2 * c.max_vars ∧
        S13WsortBounded s6.scratch.wsort n_s.toNat s.core.cur_vars ∧
        (S13ReorderMem c s6 wl1 wr1 ⋆ R) m6) ?_ ?_
    · -- Post-heapsort: reverse sweep `rem_s = n_s ..> 0`: update scores & `full_heap_up`
      rintro _ _ m6 ⟨s6, hs6_eq, hws6_len, hwb6, hm6⟩
      dsimp only [Blocks.get]; c0_hsteps_nogrp
      have hlen6 : s6.LengthsOk c :=
        s13rw_lengthsOk hsF1_len hs6_eq (hws6_len.trans hws1_len.symm)
      have hce6 : s6.core = s.core := by unfold S13RWsortEq at hs6_eq; rw [hs6_eq]; exact hce1
      have hext6 : FullExtScratchPres s s6 := by
        unfold S13RWsortEq at hs6_eq; rw [hs6_eq]; exact hext1
      refine wp_while_state1 (fun rem : BitVec 64 => rem) (fun rem => rem.toNat)
        (fun rem m7 => rem.toNat ≤ n_s.toNat ∧ ∃ (sb : FullState) (wlb wrb : S13Arr64 c.max_vars),
          sb.core = s.core ∧ sb.LengthsOk c ∧ FullExtScratchPres s sb ∧
          S13WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
          (S13ReorderMem c sb wlb wrb ⋆ R) m7)
        (fun J7 hJ7 => by
          c0_hsteps; exact hJ7 n_s m6 ⟨le_refl _, s6, wl1, wr1, hce6, hlen6, hext6, hwb6, hm6⟩)
        (fun J7 rem m7 ⟨hrem, sb, wlb, wrb, hsb_core, hsb_len, hsb_ext, hwb_b, hmb⟩ hJ7 => ?_)
      c0_hsplit
      · have hrp := s13r_sub1 hn_29 hrem ‹_›
        have hr_ws : (rem - 1#64).toNat < sb.scratch.wsort.length :=
          hsb_len.scratch_ok.wsort_len.symm ▸
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hrp.2.2.2 hn_cv) hcv_ws
        have hidx_cv : (sb.scratch.wsort[(rem - 1#64).toNat]'hr_ws).toNat < s.core.cur_vars :=
          s13wb_get hwb_b hrp.2.2.2 hr_ws
        have hidx_mv : (BitVec.setWidth 64 (sb.scratch.wsort[(rem - 1#64).toNat]'hr_ws)).toNat <
            c.max_vars := s13r_zext64_32_lt (Nat.lt_of_lt_of_le hidx_cv hcv_le)
        have hidx_sc : (BitVec.setWidth 64 (sb.scratch.wsort[(rem - 1#64).toNat]'hr_ws)).toNat <
            sb.scratch.score.length := hsb_len.scratch_ok.score_len.symm ▸ hidx_mv
        c0_hsteps_nogrp
        c0_call hFadd
        refine f64uPure2Spec_of fun nsc => ?_
        c0_hsteps_nogrp
        let sb1 : FullState :=
          { sb with scratch := { sb.scratch with
              score := sb.scratch.score.set
                (BitVec.setWidth 64 (sb.scratch.wsort[(rem - 1#64).toNat]'hr_ws)).toNat nsc } }
        have hlen1 : sb1.LengthsOk c := ⟨hsb_len.core_ok, { hsb_len.scratch_ok with
          score_len := by simp [sb1, hsb_len.scratch_ok.score_len] }⟩
        obtain ⟨tmk1, trc1, htmk1, htrc1, hmF1'⟩ :=
          s13r_fullMem_of_reorderMem (s := sb1) (wl := wlb) (wr := wrb) (by assumption)
        let sb1F : FullState :=
          { sb1 with scratch := { sb1.scratch with tarjan_mark := tmk1, tarjan_reach := trc1 } }
        have hlen1F : sb1F.LengthsOk c := ⟨hlen1.core_ok, { hlen1.scratch_ok with
          tarjan_mark_len := htmk1, tarjan_reach_len := htrc1 }⟩
        c0_call hHeapUp
        refine ⟨c, sb1F, R, rfl, hlen1F, hmF1',
          fun _ sb2F m_b' hsb2_core hsb2_len hsb2_p hmF2' => ?_⟩
        obtain ⟨wlb2, wrb2, hm_b2⟩ := s13r_reorderMem_of_fullMem hsb2_len hmF2'
        have hsb2_ce : sb2F.core = sb.core := hsb2_core
        have hwb2 : S13WsortBounded sb2F.scratch.wsort n_s.toNat s.core.cur_vars := by
          obtain ⟨_, hp', ps', hscr'⟩ := hsb2_p
          have hws_eq : sb2F.scratch.wsort = sb.scratch.wsort := by rw [hscr']
          rw [hws_eq]; exact hwb_b
        c0_hsteps
        exact hJ7 (rem - 1#64) m_b' hrp.2.1
          ⟨hrp.2.2.1, sb2F, wlb2, wrb2, hsb2_ce.trans hsb_core, hsb2_len,
           ⟨hsb2_p.1.1.1.trans hsb_ext.1, hsb2_p.1.1.2.trans hsb_ext.2⟩, hwb2, hm_b2⟩
      · obtain ⟨tmkF, trcF, htmkF, htrcF, hmFF⟩ := s13r_fullMem_of_reorderMem hmb
        let sbF : FullState :=
          { sb with scratch := { sb.scratch with tarjan_mark := tmkF, tarjan_reach := trcF } }
        have hlenF : sbF.LengthsOk c := ⟨hsb_len.core_ok, { hsb_len.scratch_ok with
          tarjan_mark_len := htmkF, tarjan_reach_len := htrcF }⟩
        c0_hsteps; exact hQ' (n_s, ()) _ ⟨sbF, hsb_core, hlenF, hsb_ext, hmFF⟩
    · -- Inline heapsort on `ws[0 ..< n_s)` (`if (n_s > 1)`)
      intro J6 hJ6; c0_hsplit
      · have hn_pos : 0 < n_s.toNat := Nat.lt_trans Nat.zero_lt_one ‹_›
        c0_hsteps_nogrp
        -- Build heap loop
        refine wp_while_state1 (fun si : BitVec 64 => si) (fun si => si.toNat)
          (fun si m6 => si.toNat ≤ n_s.toNat ∧ ∃ s6 : FullState, S13RWsortEq sF1 s6 ∧
            s6.scratch.wsort.length = 2 * c.max_vars ∧
            S13WsortBounded s6.scratch.wsort n_s.toNat s.core.cur_vars ∧
            (S13ReorderMem c s6 wl1 wr1 ⋆ R) m6)
          (fun Jb hJb => by
            c0_hsteps; exact hJb (n_s >>> 1#64) m5 ⟨s13r_ushr1_le (le_refl _),
              s5, hs5_eq, hws5_len, hwb5, hm5⟩)
          (fun Jb si m6 ⟨hsi, s6, hs6_eq, hws6_len, hwb6, hm6⟩ hJb => ?_)
        c0_hsplit
        · have hsip := s13r_sub1 hn_29 hsi ‹_›
          c0_hsteps_nogrp
          refine wp_while_break_state (fun root : BitVec 64 => (root, ()))
            (fun _ mb => ∃ sb : FullState, S13RWsortEq sF1 sb ∧
              sb.scratch.wsort.length = 2 * c.max_vars ∧
              S13WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
              (S13ReorderMem c sb wl1 wr1 ⋆ R) mb)
            (fun root : BitVec 64 => (root, ())) (fun root => n_s.toNat - root.toNat)
            (fun root mb => root.toNat < n_s.toNat ∧ ∃ sb : FullState, S13RWsortEq sF1 sb ∧
              sb.scratch.wsort.length = 2 * c.max_vars ∧
              S13WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
              (S13ReorderMem c sb wl1 wr1 ⋆ R) mb)
            (fun _ _ mb ⟨sb, hsb_eq, hwsb, hwb_b, hmb⟩ => by
              c0_hsteps
              exact hJb (si - 1#64) mb hsip.2.1 ⟨hsip.2.2.1, sb, hsb_eq, hwsb, hwb_b, hmb⟩)
            (fun B L root mb hB hL ⟨hroot, sb, hsb_eq, hwsb, hwb_b, hmb⟩ => ?_)
            (fun _ _ _ hL => by
              c0_hsteps; exact hL (si - 1#64) m6 ⟨hsip.2.2.2, s6, hs6_eq, hws6_len, hwb6, hm6⟩)
          exact s13_reorder_sift_inner_wp hcv_le hcv_29 hcv_ws hsc1_len hn_cv (le_refl _) hroot
            hsb_eq hwsb hwb_b hmb hB hL
        · -- Pop heap loop (reuses `s13_reorder_sift_inner_wp`)
          refine wp_while_state1 (fun e : BitVec 64 => e) (fun e => e.toNat)
            (fun e m7 => e.toNat ≤ n_s.toNat ∧ ∃ s7 : FullState, S13RWsortEq sF1 s7 ∧
              s7.scratch.wsort.length = 2 * c.max_vars ∧
              S13WsortBounded s7.scratch.wsort n_s.toNat s.core.cur_vars ∧
              (S13ReorderMem c s7 wl1 wr1 ⋆ R) m7)
            (fun Jp hJp => by
              c0_hsteps; exact hJp n_s m6 ⟨le_refl _, s6, hs6_eq, hws6_len, hwb6, hm6⟩)
            (fun Jp e m7 ⟨he, s7, hs7_eq, hws7_len, hwb7, hm7⟩ hJp => ?_)
          c0_hsplit
          · have he_gt1 : 1 < e.toNat := ‹_›
            have he_pos : 0 < e.toNat := Nat.lt_trans Nat.zero_lt_one he_gt1
            have hep := s13r_sub1 hn_29 he he_pos
            have he1_n : (e - 1#64).toNat < n_s.toNat := Nat.lt_of_lt_of_le hep.2.1 he
            have h0_lt_e1 : (0#64 : BitVec 64).toNat < (e - 1#64).toNat := by
              have h1 := hep.1; simp only [BitVec.toNat_ofNat]; omega
            have h0_ws : 0 < s7.scratch.wsort.length := by omega
            have he_ws : (e - 1#64).toNat < s7.scratch.wsort.length := by omega
            have hv0_lt : (s7.scratch.wsort[0]'h0_ws).toNat < s.core.cur_vars :=
              s13wb_get hwb7 hn_pos h0_ws
            have hve_lt : (s7.scratch.wsort[(e - 1#64).toNat]'he_ws).toNat < s.core.cur_vars :=
              s13wb_get hwb7 he1_n he_ws
            have he_ws' : (e - 1#64).toNat <
                (s7.scratch.wsort.set 0 (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).length := by
              simpa using he_ws
            c0_hsteps_nogrp
            let ws_sw := (s7.scratch.wsort.set 0 (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).set
              (e - 1#64).toNat (s7.scratch.wsort[0]'h0_ws)
            let s7_sw : FullState := { s7 with scratch := { s7.scratch with wsort := ws_sw } }
            have hwb_sw : S13WsortBounded ws_sw n_s.toNat s.core.cur_vars :=
              s13wb_swap hwb7 hve_lt hv0_lt
            refine wp_while_break_state (fun root : BitVec 64 => (root, ()))
              (fun _ mb => ∃ sb : FullState, S13RWsortEq sF1 sb ∧
                sb.scratch.wsort.length = 2 * c.max_vars ∧
                S13WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
                (S13ReorderMem c sb wl1 wr1 ⋆ R) mb)
              (fun root : BitVec 64 => (root, ())) (fun root => (e - 1#64).toNat - root.toNat)
              (fun root mb => root.toNat < (e - 1#64).toNat ∧ ∃ sb : FullState, S13RWsortEq sF1 sb ∧
                sb.scratch.wsort.length = 2 * c.max_vars ∧
                S13WsortBounded sb.scratch.wsort n_s.toNat s.core.cur_vars ∧
                (S13ReorderMem c sb wl1 wr1 ⋆ R) mb)
              (fun _ _ mb ⟨sb, hsb_eq, hwsb, hwb_b, hmb⟩ => by
                c0_hsteps
                exact hJp (e - 1#64) mb hep.2.1 ⟨Nat.le_of_lt he1_n, sb, hsb_eq, hwsb, hwb_b, hmb⟩)
              (fun B L root mb hB hL ⟨hroot, sb, hsb_eq, hwsb, hwb_b, hmb⟩ =>
                s13_reorder_sift_inner_wp hcv_le hcv_29 hcv_ws hsc1_len hn_cv (le_of_lt he1_n)
                  hroot hsb_eq hwsb hwb_b hmb hB hL)
              (fun _ _ _ hL => by
                c0_hsteps
                exact hL 0#64 _ ⟨h0_lt_e1, s7_sw, s13rw_set hs7_eq ws_sw,
                  by dsimp only [s7_sw, ws_sw]; rw [List.length_set, List.length_set, hws7_len],
                  hwb_sw, by assumption⟩)
          · c0_hsteps; exact hJ6 () m7 ⟨s7, hs7_eq, hws7_len, hwb7, hm7⟩
      · c0_hsteps; exact hJ6 () m5 ⟨s5, hs5_eq, hws5_len, hwb5, hm5⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
