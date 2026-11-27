/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorderProof0
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-A — `S13ReorderMem`, `S13ReorderTactics` & `full_reorder_sift_fid`

Transparent (`@[expose]` on defs, `0` `@[expose]` on theorems) Step-13 reorder memory view
(`S13ReorderMem`, `S13WsortBounded`, `s13ReorderSiftSpec`) and parametric `Func.wp` proof
`full_reorder_sift_fid_step13_wp` on unchanged `FullM7FidelityCore.full_reorder_sift_fid_body`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7FidelityCore
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. `S13ReorderMem`, `S13WsortBounded` & `s13ReorderSiftSpec` -/

/-- Fixed-length `u64` array view (`n` elements). -/
abbrev S13Arr64 (n : Nat) := { xs : List (BitVec 64) // xs.length = n }

/-- Variant of `FullMem` viewing `tarjan_mark` and `tarjan_reach` as `max_vars`-length `u64`
arrays (`wl`, `wr`). -/
@[expose] def S13ReorderMem (c : FullCfg) (s : FullState) (wl wr : S13Arr64 c.max_vars) :
    Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
  c.pad

/-- Boundedness of `wsort[0 ..< n)` indices below `cur_vars`. -/
@[expose] def S13WsortBounded (wsort : List (BitVec 32)) (n cv : Nat) : Prop :=
  ∀ i < n, (wsort[i]?.getD 0#32).toNat < cv

/-- Canonical sift helper specification for `full_reorder_sift_fid` over `S13ReorderMem`. -/
@[expose] def s13ReorderSiftSpec : Spec [i64, i64, i64] [] :=
  fun (h, _start, n, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (wl wr : S13Arr64 c.max_vars) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      S13WsortBounded s.scratch.wsort n.toNat s.core.cur_vars ∧
      (S13ReorderMem c s wl wr ⋆ R) m ∧
      ∀ (ws' : List (BitVec 32)) (m' : Mem 64),
        ws'.length = s.scratch.wsort.length →
        S13WsortBounded ws' n.toNat s.core.cur_vars →
        (∀ j, n.toNat ≤ j → ws'[j]? = s.scratch.wsort[j]?) →
        let s' := { s with scratch := { s.scratch with wsort := ws' } }
        (S13ReorderMem c s' wl wr ⋆ R) m' → Q () m'

theorem s13ReorderSiftSpec_monoX {a m Q X X'} (h : s13ReorderSiftSpec a m Q X) :
    s13ReorderSiftSpec a m Q X' := h

theorem s13r_reorderMem_of_fullMem {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m) :
    ∃ wl wr : S13Arr64 c.max_vars, (S13ReorderMem c s wl wr ⋆ R) m := by
  have htm := hlen.scratch_ok.tarjan_mark_len; have htr := hlen.scratch_ok.tarjan_reach_len
  let wl : S13Arr64 c.max_vars := ⟨s13PackPairs64 s.scratch.tarjan_mark, by
    rw [s13PackPairs64_length, htm]; omega⟩
  let wr : S13Arr64 c.max_vars := ⟨s13PackPairs64 s.scratch.tarjan_reach, by
    rw [s13PackPairs64_length, htr]; omega⟩
  refine ⟨wl, wr, ?_⟩
  unfold FullMem FullScratchArrays FullScrWksArrs at hm
  rw [s13_array_i32_eq_array64_pack c.pTarjanMark s.scratch.tarjan_mark (by omega),
    s13_array_i32_eq_array64_pack c.pTarjanReach s.scratch.tarjan_reach (by omega)] at hm
  unfold S13ReorderMem; exact hm

theorem s13r_fullMem_of_reorderMem {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    ∃ tmk trc : List (BitVec 32),
      tmk.length = 2 * c.max_vars ∧ trc.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } } ⋆
        R) m := by
  let tmk := s13UnpackPairs32 wl.1; let trc := s13UnpackPairs32 wr.1
  refine ⟨tmk, trc, by simp [tmk, s13UnpackPairs32_length, wl.2],
    by simp [trc, s13UnpackPairs32_length, wr.2], ?_⟩
  unfold S13ReorderMem at hm
  rw [s13_array64_eq_array_i32_unpack c.pTarjanMark wl.1,
    s13_array64_eq_array_i32_unpack c.pTarjanReach wr.1] at hm
  unfold FullMem FullScratchArrays FullScrWksArrs; exact hm

private theorem s13rm_bv64_mul4 (i : BitVec 64) :
    (i * 4 : BitVec 64) = BitVec.ofNat 64 (4 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]

private theorem s13rm_bv64_mul8 (i : BitVec 64) :
    (i * 8 : BitVec 64) = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]

/-! ## 2. `S13ReorderTactics` (`c0_load` / `c0_store` Lemmas) -/

namespace S13ReorderTactics

open FullArenaTactics
open scoped FullArenaTactics

@[scoped c0_load] theorem load_s13re_arena_len {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 48) = some (BitVec.ofNat 64 s.core.arena_len) := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_arena_len hmF

@[scoped c0_load] theorem load_s13re_wlen {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 56) = some (BitVec.ofNat 64 s.core.wlen) := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_wlen hmF

@[scoped c0_load] theorem load_s13re_values_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 64) = some c.pVals := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_values_ptr hmF

@[scoped c0_load] theorem load_s13re_watch_vec_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 104) = some c.pWvec := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  simpa using load_full_watch_vec_ptr hmF

@[scoped c0_load] theorem load_s13re_arena_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 112) = some c.pArena := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_arena_ptr hmF

@[scoped c0_load] theorem load_s13re_watch_stk_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 120) = some c.pWstk := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  simpa using load_full_watch_stk_ptr hmF

@[scoped c0_load] theorem load_s13re_score_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 216) = some c.pScore := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_score_ptr hmF

@[scoped c0_load] theorem load_s13re_scinc {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 256) = some s.scratch.scinc := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_scinc hmF

@[scoped c0_load] theorem load_s13re_q_prev_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 368) = some c.pQPrev := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_q_prev_ptr hmF

@[scoped c0_load] theorem load_s13re_q_next_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 376) = some c.pQNext := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_q_next_ptr hmF

@[scoped c0_load] theorem load_s13re_q_stamp_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 384) = some c.pQStamp := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_q_stamp_ptr hmF

@[scoped c0_load] theorem load_s13re_wsort_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 408) = some c.pWsort := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_wsort_ptr hmF

@[scoped c0_load] theorem load_s13re_stable {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 552) = some s.scratch.stable := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_stable hmF

@[scoped c0_load] theorem load_s13re_cur_vars {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 776) = some (BitVec.ofNat 64 s.core.cur_vars) := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_cur_vars hmF

@[scoped c0_load] theorem load_s13re_flags_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 800) = some c.pFlags := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm; simpa using load_full_flags_ptr hmF

@[scoped c0_load] theorem load_s13re_tarjan_mark_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 864) = some c.pTarjanMark := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  simpa using load_full_tarjan_mark_ptr hmF

@[scoped c0_load] theorem load_s13re_tarjan_reach_ptr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 872) = some c.pTarjanReach := by
  obtain ⟨_, _, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  simpa using load_full_tarjan_reach_ptr hmF

@[scoped c0_load] theorem c0_load_s13re_vals {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.vals.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i8 (c.pVals + i) = some s.core.vals[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_vals (s := s') hi hmF

@[scoped c0_load] theorem c0_load_s13re_flags {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.flags.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pFlags + i * 4) = some s.core.flags[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_flags (s := s') hi hmF

@[scoped c0_load] theorem c0_load_s13re_arena {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.arena.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_arena (s := s') hi hmF

@[scoped c0_load] theorem c0_load_s13re_wvec {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.wvec.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pWvec + i * 4) = some s.core.wvec[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_wvec (s := s') hi hmF

@[scoped c0_load] theorem c0_load_s13re_wstk {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.wstk.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pWstk + i * 4) = some s.core.wstk[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_wstk (s := s') hi hmF

@[scoped c0_load] theorem c0_load_s13re_q_stamp {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.q_stamp.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pQStamp + i * 4) = some s.scratch.q_stamp[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_q_stamp (s := s') hi hmF

@[scoped c0_load] theorem c0_load_s13re_wsort {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.wsort.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some s.scratch.wsort[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_wsort (s := s') hi hmF

@[scoped c0_load] theorem load_s13re_wsort0 {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < s.scratch.wsort.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 c.pWsort = some s.scratch.wsort[0] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using load_full_wsort0 (s := s') hi hmF

@[scoped c0_load] theorem c0_load_s13re_score {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.score.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pScore + i * 8) = some s.scratch.score[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := s13r_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_score (s := s') hi hmF

@[scoped c0_store] theorem store_s13re_score {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i < s.scratch.score.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) ∧
      (S13ReorderMem c { s with scratch := { s.scratch with score := s.scratch.score.set i v } }
        wl wr ⋆ R) (storeMem m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) v) := by
  unfold S13ReorderMem FullScrMetaArrs at hm ⊢
  change _ ∧ (dimacsState c.hdr _ _ _ _ ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
    FullCoreArrays c s.core ⋆ (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆ array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
    array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
    array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1) ⋆
    (array64 c.pScore (s.scratch.score.set i v) ⋆ array64 c.pSimSig s.scratch.sim_sig ⋆
    array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
    array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
    FullScrDynArrs c s.scratch) ⋆ c.pad ⋆ R) _
  have hm' : (array64 c.pScore s.scratch.score ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1 ⋆
      array64 c.pSimSig s.scratch.sim_sig ⋆
      array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
      array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
      FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R)) m := by ecancel
  obtain ⟨h1, h2⟩ := store_array64 v hi hm'
  exact ⟨h1, by clear hm hm'; ecancel⟩

@[scoped c0_store] theorem c0_store_s13re_score {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < s.scratch.score.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pScore + i * 8) ∧
      (S13ReorderMem c
        { s with scratch := { s.scratch with score := s.scratch.score.set i.toNat v } }
        wl wr ⋆ R) (storeMem m i64 (c.pScore + i * 8) v) := by
  rw [s13rm_bv64_mul8]; exact store_s13re_score v hi hm

@[scoped c0_store] theorem store_s13re_wsort {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 32)
    (hi : i < s.scratch.wsort.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) ∧
      (S13ReorderMem c { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } }
        wl wr ⋆ R) (storeMem m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) v) := by
  unfold S13ReorderMem at hm ⊢
  change _ ∧ (dimacsState c.hdr _ _ _ _ ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
    FullCoreArrays c s.core ⋆ (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort (s.scratch.wsort.set i v) ⋆
    array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
    array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
    array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆ c.pad ⋆ R) _
  have hm' : (array (t := i32) c.pWsort s.scratch.wsort ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1 ⋆
      FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R)) m := by ecancel
  obtain ⟨h1, h2⟩ := store_array (t := i32) v (by decide) hi hm'
  have h2' : (array (t := i32) c.pWsort (s.scratch.wsort.set i v) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1 ⋆
      FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R))
      (storeMem m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) v) := by
    simpa only [Ty.bytes, Ty.size, Nat.mul_comm] using h2
  exact ⟨h1, by clear hm hm'; ecancel⟩

@[scoped c0_store] theorem c0_store_s13re_wsort {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.scratch.wsort.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 (c.pWsort + i * 4) ∧
      (S13ReorderMem c
        { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i.toNat v } }
        wl wr ⋆ R) (storeMem m i32 (c.pWsort + i * 4) v) := by
  rw [s13rm_bv64_mul4]; exact store_s13re_wsort v hi hm

@[scoped c0_store] theorem store_s13re_wsort0 {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hi : 0 < s.scratch.wsort.length) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 c.pWsort ∧
      (S13ReorderMem c { s with scratch := { s.scratch with wsort := s.scratch.wsort.set 0 v } }
        wl wr ⋆ R) (storeMem m i32 c.pWsort v) := by
  simpa using store_s13re_wsort v hi hm

@[scoped c0_load] theorem load_s13re_wl {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanMark + BitVec.ofNat 64 (8 * i)) =
      some (wl.1[i]'(by rw [wl.2]; exact hi)) := by
  unfold S13ReorderMem at hm
  exact loadVal_array64 (R := _) (by rw [wl.2]; exact hi) (by ecancel)

@[scoped c0_load] theorem c0_load_s13re_wl {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanMark + i * 8) =
      some (wl.1[i.toNat]'(by rw [wl.2]; exact hi)) := by
  rw [s13rm_bv64_mul8]; exact load_s13re_wl hi hm

@[scoped c0_load] theorem load_s13re_wl0 {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 c.pTarjanMark = some (wl.1[0]'(by rw [wl.2]; exact hi)) := by
  simpa using load_s13re_wl hi hm

@[scoped c0_store] theorem store_s13re_wl {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanMark + BitVec.ofNat 64 (8 * i)) ∧
      (S13ReorderMem c s ⟨wl.1.set i v, by simp [wl.2]⟩ wr ⋆ R)
        (storeMem m i64 (c.pTarjanMark + BitVec.ofNat 64 (8 * i)) v) := by
  unfold S13ReorderMem at hm ⊢
  have hi' : i < wl.1.length := by rw [wl.2]; exact hi
  have hm' : (array64 c.pTarjanMark wl.1 ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanReach wr.1 ⋆ FullScrMetaArrs c s.scratch ⋆
      FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R)) m := by ecancel
  obtain ⟨h1, h2⟩ := store_array64 v hi' hm'
  exact ⟨h1, by ecancel⟩

@[scoped c0_store] theorem c0_store_s13re_wl {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanMark + i * 8) ∧
      (S13ReorderMem c s ⟨wl.1.set i.toNat v, by simp [wl.2]⟩ wr ⋆ R)
        (storeMem m i64 (c.pTarjanMark + i * 8) v) := by
  rw [s13rm_bv64_mul8]; exact store_s13re_wl v hi hm

@[scoped c0_store] theorem store_s13re_wl0 {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hi : 0 < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 c.pTarjanMark ∧
      (S13ReorderMem c s ⟨wl.1.set 0 v, by simp [wl.2]⟩ wr ⋆ R)
        (storeMem m i64 c.pTarjanMark v) := by
  simpa using store_s13re_wl v hi hm

@[scoped c0_load] theorem load_s13re_wr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanReach + BitVec.ofNat 64 (8 * i)) =
      some (wr.1[i]'(by rw [wr.2]; exact hi)) := by
  unfold S13ReorderMem at hm
  exact loadVal_array64 (R := _) (by rw [wr.2]; exact hi) (by ecancel)

@[scoped c0_load] theorem c0_load_s13re_wr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanReach + i * 8) =
      some (wr.1[i.toNat]'(by rw [wr.2]; exact hi)) := by
  rw [s13rm_bv64_mul8]; exact load_s13re_wr hi hm

@[scoped c0_load] theorem load_s13re_wr0 {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 c.pTarjanReach = some (wr.1[0]'(by rw [wr.2]; exact hi)) := by
  simpa using load_s13re_wr hi hm

@[scoped c0_store] theorem store_s13re_wr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanReach + BitVec.ofNat 64 (8 * i)) ∧
      (S13ReorderMem c s wl ⟨wr.1.set i v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 (c.pTarjanReach + BitVec.ofNat 64 (8 * i)) v) := by
  unfold S13ReorderMem at hm ⊢
  have hi' : i < wr.1.length := by rw [wr.2]; exact hi
  have hm' : (array64 c.pTarjanReach wr.1 ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ FullScrMetaArrs c s.scratch ⋆
      FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R)) m := by ecancel
  obtain ⟨h1, h2⟩ := store_array64 v hi' hm'
  exact ⟨h1, by ecancel⟩

@[scoped c0_store] theorem c0_store_s13re_wr {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanReach + i * 8) ∧
      (S13ReorderMem c s wl ⟨wr.1.set i.toNat v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 (c.pTarjanReach + i * 8) v) := by
  rw [s13rm_bv64_mul8]; exact store_s13re_wr v hi hm

@[scoped c0_store] theorem store_s13re_wr0 {c : FullCfg} {s : FullState}
    {wl wr : S13Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hi : 0 < c.max_vars) (hm : (S13ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 c.pTarjanReach ∧
      (S13ReorderMem c s wl ⟨wr.1.set 0 v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 c.pTarjanReach v) := by
  simpa using store_s13re_wr v hi hm

end S13ReorderTactics

/-! ## 3. `full_reorder_sift_fid_step13_wp` (`s13ReorderSiftSpec`) -/

section S13ReorderSiftProof

open scoped S13ReorderTactics

private def S13SiftWsortEq (s s1 : FullState) : Prop :=
  s1 = { s with scratch := { s.scratch with wsort := s1.scratch.wsort } }

private theorem s13sift_refl (s : FullState) : S13SiftWsortEq s s := by
  rcases s with ⟨_, ⟨_⟩⟩; rfl

private theorem s13sift_qstamp {s s1 : FullState} (h : S13SiftWsortEq s s1) :
    s1.scratch.q_stamp = s.scratch.q_stamp := by
  unfold S13SiftWsortEq at h; rw [h]

private theorem s13sift_set {s s1 : FullState} (h : S13SiftWsortEq s s1) (ws : List (BitVec 32)) :
    S13SiftWsortEq s { s1 with scratch := { s1.scratch with wsort := ws } } := by
  unfold S13SiftWsortEq at h ⊢; rw [h]

private theorem s13sift_wb_set {ws : List (BitVec 32)} {n cv idx : Nat}
    (v : BitVec 32) (h : S13WsortBounded ws n cv) (hv : v.toNat < cv) :
    S13WsortBounded (ws.set idx v) n cv := by
  intro i hi; by_cases he : i = idx
  · subst he; by_cases hl : i < ws.length
    · rw [List.getElem?_set_self hl, Option.getD_some]; exact hv
    · rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]; exact Nat.zero_lt_of_lt hv
  · rw [List.getElem?_set_ne (Ne.symm he)]; exact h i hi

private theorem s13sift_wb_get {ws : List (BitVec 32)} {n cv i : Nat}
    (h : S13WsortBounded ws n cv) (hi : i < n) (hl : i < ws.length) :
    (ws[i]'hl).toNat < cv := by
  have := h i hi; rwa [List.getElem?_eq_getElem hl, Option.getD_some] at this

private theorem s13sift_zext64_32_lt {x : BitVec 32} {n : Nat} (h : x.toNat < n) :
    (BitVec.setWidth 64 x).toNat < n := by
  have hlt : x.toNat < 2 ^ 64 := lt_trans x.isLt (by decide)
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]; exact h

private theorem s13sift_child_nat {root n : BitVec 64} (hroot : root.toNat < 2 ^ 29)
    (h : ¬n.toNat ≤ (2 * root.toNat + (1 : BitVec 64).toNat) % 2 ^ 64) :
    ((root <<< 1) + 1#64).toNat < n.toNat := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  have h2 : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
  rw [h1, Nat.mod_eq_of_lt (by omega)] at h; omega

/-- Parametric `Func.wp` proof for unchanged `FullM7FidelityCore.full_reorder_sift_fid_body`
against transparent `s13ReorderSiftSpec`. -/
theorem full_reorder_sift_fid_step13_wp (Γ : Env) :
    ∀ a m Q X, s13ReorderSiftSpec a m Q X → Func.wp Γ full_reorder_sift_fid_body a m Q X := by
  rintro ⟨h, start, n, ⟨⟩⟩ m Q X ⟨c, s, wl, wr, R, rfl, hlen, hwb, hm, hQ⟩
  have hQ' : ∀ (s1 : FullState) (m1 : Mem 64),
      S13SiftWsortEq s s1 → s1.scratch.wsort.length = s.scratch.wsort.length →
      S13WsortBounded s1.scratch.wsort n.toNat s.core.cur_vars →
      (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) →
      (S13ReorderMem c s1 wl wr ⋆ R) m1 → Q () m1 :=
    fun s1 m1 hs1_eq hlen1 hwb1 hpres1 hm1 =>
      hQ s1.scratch.wsort m1 hlen1 hwb1 hpres1 (hs1_eq ▸ hm1)
  clear hQ
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le; have hcv_29 : s.core.cur_vars < 2 ^ 29 := by omega
  have hws_len := hlen.scratch_ok.wsort_len; have hqs_len := hlen.scratch_ok.q_stamp_len
  unfold Func.wp full_reorder_sift_fid_body
  c0_hsplit
  · c0_hsteps; exact hQ' s m (s13sift_refl s) rfl hwb (fun _ _ => rfl) hm
  · c0_hsplit
    · c0_hsteps; exact hQ' s m (s13sift_refl s) rfl hwb (fun _ _ => rfl) hm
    · c0_hsplit
      · c0_hsteps; exact hQ' s m (s13sift_refl s) rfl hwb (fun _ _ => rfl) hm
      · have hn_pos : 1 ≤ n.toNat := by bv_omega
        have hst_lt : start.toNat < n.toNat := by bv_omega
        have hn_le : n.toNat ≤ s.core.cur_vars := by omega
        c0_hsteps_nogrp
        refine wp_while_break_state (fun root : BitVec 64 => (root, ()))
          (fun _ m1 => ∃ s1 : FullState,
            S13SiftWsortEq s s1 ∧ s1.scratch.wsort.length = s.scratch.wsort.length ∧
            S13WsortBounded s1.scratch.wsort n.toNat s.core.cur_vars ∧
            (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) ∧
            (S13ReorderMem c s1 wl wr ⋆ R) m1)
          (fun root : BitVec 64 => (root, ())) (fun root => n.toNat - root.toNat)
          (fun root m1 => root.toNat < n.toNat ∧ ∃ s1 : FullState,
            S13SiftWsortEq s s1 ∧ s1.scratch.wsort.length = s.scratch.wsort.length ∧
            S13WsortBounded s1.scratch.wsort n.toNat s.core.cur_vars ∧
            (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) ∧
            (S13ReorderMem c s1 wl wr ⋆ R) m1)
          (fun B _ m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩ => by
            c0_hsteps; exact hQ' s1 m1 hs1_eq hws1_len hwb1 hpres1 hm1)
          (fun B L root m1 hB hL ⟨hroot, s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩ => ?_)
          (fun B L _ hL => by
            c0_hsteps
            exact hL start m ⟨hst_lt, s, s13sift_refl s, rfl, hwb, fun _ _ => rfl, hm⟩)
        have hqs1_len : s1.scratch.q_stamp.length = c.max_vars := by
          rw [s13sift_qstamp hs1_eq]; exact hqs_len
        have hchild_eq : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
        have hroot_lt_ws : root.toNat < s1.scratch.wsort.length := by omega
        have hbv0_lt : (s1.scratch.wsort[root.toNat]'hroot_lt_ws).toNat < s.core.cur_vars :=
          s13sift_wb_get hwb1 hroot hroot_lt_ws
        have hbv0_mv :
            (BitVec.setWidth 64 (s1.scratch.wsort[root.toNat]'hroot_lt_ws)).toNat < c.max_vars :=
          s13sift_zext64_32_lt (Nat.lt_of_lt_of_le hbv0_lt hcv_le)
        have hbv0_qs : (BitVec.setWidth 64 (s1.scratch.wsort[root.toNat]'hroot_lt_ws)).toNat <
            s1.scratch.q_stamp.length := hqs1_len ▸ hbv0_mv
        c0_hsplit
        · c0_hsplit
          · c0_hsteps; exact hB root m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩
          · have hch_nat : ((root <<< 1) + 1#64).toNat < n.toNat :=
              s13sift_child_nat (by omega) ‹_›
            have hch_lt_ws : ((root <<< 1) + 1#64).toNat < s1.scratch.wsort.length := by omega
            have hcv0_lt : (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws).toNat <
                s.core.cur_vars := s13sift_wb_get hwb1 hch_nat hch_lt_ws
            have hcv0_mv : (BitVec.setWidth 64
                (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws)).toNat < c.max_vars :=
              s13sift_zext64_32_lt (Nat.lt_of_lt_of_le hcv0_lt hcv_le)
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
                     s13sift_set hs1_eq _, by simp [ws2, hws1_len],
                     s13sift_wb_set _ (s13sift_wb_set _ hwb1 hyv_lt) hbv0_lt,
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
                      < s.core.cur_vars := s13sift_wb_get hwb1 hrch_nat hrch_ws
                  have hrv_mv : (BitVec.setWidth 64
                      (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                      c.max_vars := s13sift_zext64_32_lt (Nat.lt_of_lt_of_le hrv_lt hcv_le)
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

end S13ReorderSiftProof

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
